#!/usr/bin/env python3
"""Decide a dependency-relation claim between two modules of this repository, or over a set.

A clause asserting a *dependency relation between two named files* — *that file is downstream of
this one*, *this file does not import that one*, *no file in this repository imports both*, *N
modules below* — has to be **measured**, and a graph walk is the instrument.  Until this script
that walk was written from scratch in the session that needed it and thrown away afterwards.
`scripts/import_cost.py` is the same shape of computation against **Mathlib**; this one is the
repository's own graph, and closure figures against Mathlib are a different graph.

Usage:

    python3 scripts/module_graph.py Oka/A.lean Oka/B.lean       # the pair verdict
    python3 scripts/module_graph.py --downstream Oka/A.lean     # what imports it, transitively
    python3 scripts/module_graph.py --upstream Oka/A.lean       # what it imports, transitively
    python3 scripts/module_graph.py --importers Oka/A.lean      # one reverse edge, no closure
    python3 scripts/module_graph.py --downstream Oka/A.lean --grep Token --grep Other
    python3 scripts/module_graph.py --downstream Oka/A.lean --word --grep IsProper
    python3 scripts/module_graph.py --self-test

A path may be written either way round — `Oka/A.lean` or `Oka.A` — since the prose this exists to
check uses both spellings and a reader retyping one of them should not have to convert it.

It reads text and nothing else: no build, no oleans, no `lake`.  Exit 0 unless the arguments are
wrong or the self-test fails; **a verdict is output and not an exit code**, because the claims
this decides live in English prose and no script can tell which sentence meant which pair.

## The parser is the whole of it, and the obvious one is wrong twice over

`^import\\s+([\\w.]+)` over the raw file text follows an `import` line written inside a comment,
and it matches neither the keyword nor the module of a `public import`, which 13 files of this
tree use on a repository-internal module — 30 of the 902 internal edges at `0b2759b`.  So the
parser here is `scripts/import_cost.py`'s own `IMPORT` over its own nesting-aware
`strip_comments`, imported rather than reimplemented: that script's published figures are
computed with it, and two instruments that disagree about the graph are worse than one.

**Checking the delta is not a check on the parser.**  On the
`Oka/Analytification/StandardEtaleFiniteness.lean` and
`Oka/Analytification/StandardEtaleLocalIso.lean` pair the naive regex understates both closures by
exactly 14 and returns the two *marginal* costs unchanged.

## The aggregator is deleted from the tally and not from the graph

`Oka.lean` is the module `mk_all` generates; at `0b2759b` it carried an `import` line for each of
the **253** modules under `Oka/`, with none missing.  The root is therefore downstream of
everything it covers and is a hit for every question of this shape.  Nothing in the population
imports it, so it conducts nothing.

The walk therefore runs over the whole graph, the root included, and the root alone is subtracted
from what is reported.  `--include-aggregators` puts it back, which adds 1 to each `--downstream`
figure and changes nothing else.  **`self_test` plants the root** so that the subtraction is one
the fixture has rather than one it assumes.

## Population

Every tracked `.lean` file under `Oka/`, together with `Oka.lean`.  `scripts/DumpOkaDecls.lean`
and `scripts/DumpEnvNames.lean` import `Oka` and are **not** in it; counting them adds 2 edges and
no node any prose claim is about.  `git ls-files` is the set, not the directory listing, so that
an ignored or untracked file on disk is not counted.

## What this cannot decide

**A claim about declarations rather than modules.**  *"Proved without using `X`, or anything
downstream of `X`"* is about the environment, and the instrument for it is a transitive
`Expr.getUsedConstants`
walk.  `--grep` is the weaker text test: it says
which modules mention a token **in code** — comments stripped with the same stripper — and a
module that mentions nothing is evidence, while a module that mentions something is only a
pointer to read it, so a run of `--grep` is not to be read as a verdict.

**`--grep` is a substring test and `--word` is not the same figure**, which is worth a live
example rather than a warning.  At `0b2759b` `IsProper` occurred as a whole word in the code of
**no** module under `Oka/`, and the substring occurred in **three**:
`Oka/AnalyticSpace/Finite.lean`, `Oka/Topology/Algebra/Polynomial.lean` and
`Oka/Topology/Maps/Proper/Basic.lean`, every one of them `IsProperMap`, which is a different
class.  A verdict taken from the wrong one of the two reads
*the class this file declines to declare is consumed downstream* off the class it declines in
favour of.  Whichever a figure is, say which.

**And `--grep` is never a figure about the repository, because it only ever qualifies a set**: it
is an option on `--downstream`, `--upstream` or `--importers` and `module_graph.py --grep IsProper`
on its own exits 1 with the usage text.  *"`--grep IsProper` returns 3"* is a different claim for
every set it can qualify, and cannot be checked until the set is named.  **Name the set beside the
count**, which is the same instruction one level up from *say which of the two tests it is*.
"""

from __future__ import annotations

import os
import re
import subprocess
import sys
import tempfile
from collections import deque
from pathlib import Path

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from import_cost import IMPORT, strip_comments  # noqa: E402

ROOTS = ("Oka",)
AGGREGATORS = frozenset(ROOTS)
#: How many modules to name under a set answer.  A downstream set here runs to about 130 and a
#: reader deciding a prose claim wants the count and a sample, not the list; `--all` prints it.
LIST_UPTO = 30


def module_of(path: str) -> str:
    """`Oka/A/B.lean` as the module name `Oka.A.B`."""
    return path[:-5].replace("/", ".") if path.endswith(".lean") else path


class Graph:
    """The repository's own import graph, and closures within it."""

    def __init__(self, root: Path, files: list[str] | None = None) -> None:
        self.root = root
        if files is None:
            files = self.population(root)
        self.files = files
        self.modules = {module_of(f): f for f in files}
        self.imports: dict[str, list[str]] = {}
        self._code: dict[str, str] = {}
        for f in files:
            code = strip_comments((root / f).read_text(encoding="utf-8"))
            self._code[module_of(f)] = code
            self.imports[module_of(f)] = [m for m in IMPORT.findall(code) if m in self.modules]
        self.importers: dict[str, list[str]] = {m: [] for m in self.modules}
        for m, ims in self.imports.items():
            for i in ims:
                self.importers[i].append(m)
        for v in self.importers.values():
            v.sort()

    @staticmethod
    def population(root: Path) -> list[str]:
        out = subprocess.run(
            ["git", "-C", str(root), "ls-files", "*.lean"],
            capture_output=True,
            text=True,
            check=True,
        ).stdout.split()
        return sorted(
            f
            for f in out
            if f.startswith(tuple(r + "/" for r in ROOTS)) or f in tuple(r + ".lean" for r in ROOTS)
        )

    def resolve(self, arg: str) -> str:
        """`arg` as a module name, accepting either spelling, or `SystemExit` naming the failure."""
        m = module_of(arg)
        if m not in self.modules:
            raise SystemExit(f"not a module of this repository: {arg}")
        return m

    def _closure(self, start: str, edges: dict[str, list[str]]) -> set[str]:
        seen, stack = set(), [start]
        while stack:
            for y in edges.get(stack.pop(), []):
                if y not in seen:
                    seen.add(y)
                    stack.append(y)
        return seen

    def upstream(self, m: str) -> set[str]:
        """Every module `m` imports, transitively.  `m` itself is not in it."""
        return self._closure(m, self.imports)

    def downstream(self, m: str) -> set[str]:
        """Every module that imports `m`, transitively.  `m` itself is not in it."""
        return self._closure(m, self.importers)

    def distance(self, a: str, b: str) -> int | None:
        """BFS edge distance from `a` to `b` along `import`, or `None` if `b` is not upstream."""
        if b not in self.upstream(a):
            return None
        q, seen = deque([(a, 0)]), {a}
        while q:
            x, d = q.popleft()
            for y in self.imports.get(x, []):
                if y == b:
                    return d + 1
                if y not in seen:
                    seen.add(y)
                    q.append((y, d + 1))
        return None  # unreachable: `b` is in the closure

    def mentions(self, m: str, token: str, word: bool = False) -> bool:
        """Whether `m`'s **code** contains `token`.  Comments are stripped; see the docstring.

        `word` makes it a whole-token test, the boundary being the Lean identifier alphabet with
        `.` on it, so that `IsProperMap` is not a hit for `IsProper` while
        `ComplexAnalytic.toAmbient` still is for `toAmbient`.
        """
        if not word:
            return token in self._code[m]
        return re.search(r"(?<![A-Za-z0-9_])" + re.escape(token) + r"(?![A-Za-z0-9_])",
                         self._code[m]) is not None


def strip_aggregators(s: set[str], keep: bool) -> set[str]:
    return s if keep else s - AGGREGATORS


def report_set(label: str, subject: str, s: set[str], graph: Graph, tokens: list[str],
               show_all: bool, word: bool = False) -> None:
    names = sorted(s)
    print(f"{subject}: {len(names)} modules {label}")
    if tokens:
        for t in tokens:
            hits = [n for n in names if graph.mentions(n, t, word)]
            print(f"  `{t}` in the code of {len(hits)} of them"
                  + (f": {', '.join(hits[:LIST_UPTO])}" if hits else ""))
            if hits and len(hits) > LIST_UPTO and show_all:
                print("    " + ", ".join(hits[LIST_UPTO:]))
    shown = names if show_all else names[:LIST_UPTO]
    for n in shown:
        print(f"  {n}")
    if len(names) > len(shown):
        print(f"  … and {len(names) - len(shown)} more (--all)")


def pair(graph: Graph, a: str, b: str) -> str:
    """The verdict on the ordered pair, in the vocabulary the prose uses."""
    da, db = graph.distance(a, b), graph.distance(b, a)
    if da is not None:
        return f"{b} is upstream of {a} (that is, {a} is downstream of {b}), at distance {da}"
    if db is not None:
        return f"{b} is downstream of {a} (that is, {a} is upstream of {b}), at distance {db}"
    return f"{a} and {b} are incomparable: neither is in the other's import closure"


def self_test() -> int:
    """Plant a fixture tree whose every answer is known, and a control for each hazard.

    The cases are the ones that have cost this repository a push: an `import` line inside a
    comment, a `public import`, a pair whose names look ordered and is not, and the aggregator
    that is a hit for everything.  A walk that only ever ran on the real tree would pass all four
    silently.
    """
    failures = 0

    def check(name: str, got: object, want: object) -> None:
        nonlocal failures
        ok = got == want
        print(f"  [{'ok' if ok else 'FAIL'}] {name}: {got!r}" + ("" if ok else f" != {want!r}"))
        failures += not ok

    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        (root / "Oka").mkdir()
        write = lambda p, s: (root / p).write_text(s, encoding="utf-8")  # noqa: E731
        write("Oka/Leaf.lean", "/-! A leaf. `Token` is named here and only here. -/\n")
        # An `import` line inside a comment, which the naive regex follows.
        write(
            "Oka/Mid.lean",
            "/-!\nUpstreaming this would need\n\nimport Oka.Unrelated\n-/\nimport Oka.Leaf\n",
        )
        # A `public import`, whose keyword and module the naive regex both miss.
        write("Oka/Top.lean", "module\npublic import Oka.Mid\n/-! Top. -/\ndef Token := 1\n")
        write("Oka/Unrelated.lean", "/-! Nothing imports this. -/\n")
        write("Oka.lean", "import Oka.Leaf\nimport Oka.Mid\nimport Oka.Top\nimport Oka.Unrelated\n")
        files = ["Oka.lean", "Oka/Leaf.lean", "Oka/Mid.lean", "Oka/Top.lean", "Oka/Unrelated.lean"]
        g = Graph(root, files)

        check("a commented-out import is not an edge", g.imports["Oka.Mid"], ["Oka.Leaf"])
        check("a `public import` is an edge", g.imports["Oka.Top"], ["Oka.Mid"])
        check("closure follows both", sorted(g.upstream("Oka.Top")), ["Oka.Leaf", "Oka.Mid"])
        check("distance is the BFS one", g.distance("Oka.Top", "Oka.Leaf"), 2)
        check(
            "incomparable is not `None` twice by accident",
            (g.distance("Oka.Top", "Oka.Unrelated"), g.distance("Oka.Unrelated", "Oka.Top")),
            (None, None),
        )
        check(
            "the pair verdict names incomparable",
            "incomparable" in pair(g, "Oka.Top", "Oka.Unrelated"),
            True,
        )
        # The root is downstream of everything and is subtracted from the tally, not the graph.
        check(
            "the root is subtracted from the tally",
            strip_aggregators(g.downstream("Oka.Leaf"), keep=False),
            {"Oka.Mid", "Oka.Top"},
        )
        check(
            "…and only from the tally, not from the graph",
            len(strip_aggregators(g.downstream("Oka.Leaf"), keep=True))
            - len(strip_aggregators(g.downstream("Oka.Leaf"), keep=False)),
            1,
        )
        # `--grep` reads code and not comments: `Token` is in `Oka/Top.lean`'s code and in
        # `Oka/Leaf.lean`'s docstring only.
        check("--grep sees code", g.mentions("Oka.Top", "Token"), True)
        check("--grep does not see a docstring", g.mentions("Oka.Leaf", "Token"), False)
        # The `IsProper` / `IsProperMap` pair, which is live in this tree, and the dotted name,
        # which is the other half of `mentions`'s boundary class: `.` is a boundary and a letter
        # is not, so a longer token is not a hit and a qualified one is.
        write("Oka/Wider.lean", "/-! W. -/\ndef TokenWider := 2\n")
        write("Oka/Dotted.lean", "/-! D. -/\ndef d := Name.Space.Token\n")
        gw = Graph(root, files + ["Oka/Dotted.lean", "Oka/Wider.lean"])
        check("--grep is a substring test", gw.mentions("Oka.Wider", "Token"), True)
        check("--word is not", gw.mentions("Oka.Wider", "Token", word=True), False)
        check("--word matches under a dropped namespace",
              gw.mentions("Oka.Dotted", "Token", word=True), True)
        check("--word matches the qualified name too",
              gw.mentions("Oka.Dotted", "Name.Space.Token", word=True), True)
        check("--word does not match a proper prefix of a component",
              gw.mentions("Oka.Dotted", "Toke", word=True), False)
        check("a name may be given either way round", g.resolve("Oka/Mid.lean"), "Oka.Mid")

    print("self-test failed" if failures else "self-test passed")
    return 1 if failures else 0


def main(argv: list[str]) -> int:
    if "--self-test" in argv:
        return self_test()
    keep = "--include-aggregators" in argv
    show_all = "--all" in argv
    word = "--word" in argv
    tokens: list[str] = []
    rest: list[str] = []
    it = iter([a for a in argv if a not in ("--include-aggregators", "--all", "--word")])
    mode = None
    for a in it:
        if a == "--grep":
            tokens.append(next(it, ""))
        elif a in ("--downstream", "--upstream", "--importers"):
            mode = a
            rest.append(next(it, ""))
        else:
            rest.append(a)
    root = Path(
        subprocess.run(
            ["git", "rev-parse", "--show-toplevel"], capture_output=True, text=True, check=True
        ).stdout.strip()
    )
    graph = Graph(root)
    if mode is None:
        if len(rest) != 2:
            print(__doc__.split("Usage:")[1].split("It reads text")[0].strip())
            return 1
        a, b = graph.resolve(rest[0]), graph.resolve(rest[1])
        print(pair(graph, a, b))
        return 0
    if len(rest) != 1:
        raise SystemExit(f"{mode} takes exactly one module")
    m = graph.resolve(rest[0])
    if mode == "--importers":
        direct = strip_aggregators(set(graph.importers[m]), keep)
        report_set("importing it directly", m, direct, graph, tokens, show_all, word)
    elif mode == "--downstream":
        report_set("downstream", m, strip_aggregators(graph.downstream(m), keep), graph, tokens,
                   show_all, word)
    else:
        report_set("upstream", m, strip_aggregators(graph.upstream(m), keep), graph, tokens,
                   show_all, word)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
