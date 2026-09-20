#!/usr/bin/env python3
"""Find the sentences of this repository's prose that assert Mathlib lacks something.

`OkaTest/Axioms.lean`'s `### A negative universal about Mathlib` is the rule; this is the scan
that narrows the tree to what the rule asks a reader to look at.  **It reports pattern hits and
not defects.**  Deciding whether a hit is in the class, and then whether it is true, is a human
step and no run of this prints a verdict.

Usage:

    python3 scripts/mathlib_absence.py                 # per-file counts and the totals
    python3 scripts/mathlib_absence.py --list          # each matched sentence, with its file
    python3 scripts/mathlib_absence.py --file PATH     # one file, listed
    python3 scripts/mathlib_absence.py --mentions      # the denominator: sentences naming Mathlib
    python3 scripts/mathlib_absence.py --self-test

Exit 0 unless the arguments are wrong or the self-test fails.  Like `scripts/import_cost.py` and
unlike `scripts/check_docstring_names.py`, it is a tool and not a gate: nothing here can be a
gate, because the population it would have to quantify over is not in this repository.

## Why this class needs a scan of its own

Every other census instrument on this board walks **this tree**: `scripts/guard_coverage.py`
reads `## Main results` sections, `scripts/check_docstring_names.py` resolves a backticked name
against the environment of `Oka` + `OkaTest`, `scripts/module_graph.py` walks the import edges of
these modules.  A sentence of the form *Mathlib does not have X* has the same grammar and the same
failure mode as *nothing in this repository has X*, and **not one of those instruments can reach
it**, because what it quantifies over is not in the population they walk.

It also fails differently, and worse, in one respect.  A claim about this tree is falsified by a
commit on this board and can in principle be re-checked by one; **a claim about Mathlib is
falsified by a version bump nobody here makes**, and `.orchestra/validation.sh` will not say a
word.  `scripts/check_docstring_names.py` checks that a backticked name *resolves*, which is the
opposite polarity: it cannot see a claim that something is absent, and a name that stops resolving
after a bump fails it for the wrong reason.

`scripts/import_cost.py` already writes the principle down, once, about its own figure:

    It is a fact about Mathlib at a version and it will drift; the masking is what does not.

**So every run of this prints the pinned Mathlib version and rev**, read out of
`lake-manifest.json`, because a hit list is a statement about the Mathlib on disk and is worth
nothing without one.

## The population, and the two readings of a file

Tracked files under `Oka/`, `OkaTest/` and `scripts/` with one of the suffixes `.lean`, `.md`,
`.py`, `.sh`, `.yml`, `.toml`, together with `Oka.lean`, `OkaTest.lean` and `README.md`.

For a `.lean` file **only the comment content is read** — the inverse of
`scripts/import_cost.py`'s `strip_comments`, nesting-aware, with `/-!`, `/--` and `--` all opening
a comment like any other `/-`.  For every other suffix the whole file is read, a `.py` or `.sh`
file being prose and code in the same breath.  Text is **whitespace-normalised before matching**,
so a clause wrapped across two source lines is visible: that is the failure mode taxis #1712
records of `git log -S` and taxis #2097 of a line-anchored `grep`, and it is not hypothetical
here, where a `.lean` docstring is hard-wrapped at column 100 and most sentences of this class are
longer than that.

A sentence is the match extended to the nearest `. ` on each side.  A `(file, sentence)` pair is
reported once however many times the pattern matches inside it.

## What the pattern cannot see, and the denominator that bounds it

The pattern is six shapes and they are spellings, not meanings.  *`Mathlib/Topology/Covering/` has
only conjugation by a homeomorphism* is the same claim as *Mathlib has no cancellation lemma* and
matches nothing here; so does a negative carried by a noun (*the one thing Mathlib is missing
is …*) or by a name that never says `Mathlib` at all.  **This is why `--mentions` exists**: it
reports every sentence in the population that names Mathlib, which is the population a reader
would have to sweep by hand to find what the six shapes drop, and it makes the ratio between the
two a figure rather than a guess.

## Why classification is a human step, with the three worked cases

At the commit that adds this script, three of the sentences it returns are **out of class**, and
each is out for a different reason a pattern cannot see:

* two in `Oka/AnalyticSpace/FundamentalGroup.lean` — *"none proves anything Mathlib does not"*,
  *"nothing is proved below that Mathlib does not prove for a general Galois category"* — are
  claims about **this file's own contents**, with Mathlib as the yardstick rather than the
  subject.  The self-limiting spelling `OkaTest/Axioms.lean` prescribes covers them already;
* one in `scripts/check_docstring_names.py` is a universal about Mathlib namespaces that the
  paragraph carrying it **retracts in the next clause** — *"that is false"* — and then counts four
  counterexamples.  The class handled correctly, in prose, inside the script that cannot check it.

A checker that called any of those a defect would be the thing `scripts/import_cost.py`'s
docstring warns about: an instrument whose exactness is read as evidence for a claim it cannot
decide.  This one reports, and says so on every line of its output.
"""

from __future__ import annotations

import json
import re
import subprocess
import sys
from pathlib import Path

SUFFIXES = (".lean", ".md", ".py", ".sh", ".yml", ".toml")
ROOTS = ("Oka/", "OkaTest/", "scripts/")
FILES = ("Oka.lean", "OkaTest.lean", "README.md")

# Six shapes.  Each is a way this tree has actually spelled "Mathlib lacks something"; none of
# them is a meaning, and the module docstring says what that costs.
ABSENCE = re.compile(
    r"(?:nothing (?:in|under) Mathlib"
    r"|\bno\b[^.]{0,80}?\b(?:in|under|from) Mathlib"
    r"|Mathlib (?:does not|doesn't|has no|lacks|offers no|provides no|contains no|knows no"
    r"|has nothing)"
    r"|(?:is|are) not (?:in|under) Mathlib"
    r"|(?:absent|missing) from Mathlib)",
    re.I,
)

MENTION = re.compile(r"Mathlib")


def comment_content(text: str) -> str:
    """`text` with the **code** removed and the comment contents kept, newlines preserved.

    The inverse of `scripts/import_cost.py`'s `strip_comments`, and deliberately written as its
    mirror image so that the two can be read against each other: block comments nest, `/-!` and
    `/--` open one like any other `/-`, and a line comment runs to the end of its line.
    """
    out: list[str] = []
    i = 0
    depth = 0
    n = len(text)
    while i < n:
        if depth == 0 and text.startswith("--", i):
            j = text.find("\n", i)
            end = n if j < 0 else j
            out.append(text[i + 2 : end])
            i = end
            continue
        if text.startswith("/-", i):
            depth += 1
            i += 2
            continue
        if text.startswith("-/", i) and depth > 0:
            depth -= 1
            i += 2
            continue
        if depth > 0:
            out.append(text[i])
        elif text[i] == "\n":
            out.append("\n")
        i += 1
    return "".join(out)


def prose_of(path: Path, name: str) -> str:
    """The prose of one file, whitespace-normalised: comments only for `.lean`, all of it else."""
    text = path.read_text(encoding="utf-8")
    if name.endswith(".lean"):
        text = comment_content(text)
    return re.sub(r"\s+", " ", text).strip()


def sentences(prose: str, pattern: re.Pattern[str]) -> list[str]:
    """Each distinct sentence of `prose` in which `pattern` matches, in order of first match."""
    found: list[str] = []
    seen: set[str] = set()
    for m in pattern.finditer(prose):
        left = prose.rfind(". ", 0, m.start())
        start = 0 if left < 0 else left + 2
        right = prose.find(". ", m.end())
        end = len(prose) if right < 0 else right + 1
        sentence = prose[start:end]
        if sentence not in seen:
            seen.add(sentence)
            found.append(sentence)
    return found


def population(root: Path) -> list[str]:
    """The tracked files this scans, as repository-relative names, sorted."""
    listed = subprocess.run(
        ["git", "-C", str(root), "ls-files", "-z"],
        capture_output=True,
        text=True,
        check=True,
    ).stdout.split("\0")
    keep = [
        name
        for name in listed
        if name
        and name.endswith(SUFFIXES)
        and (name.startswith(ROOTS) or name in FILES)
    ]
    return sorted(keep)


def mathlib_pin(root: Path) -> str:
    """The `inputRev` and `rev` `lake-manifest.json` pins Mathlib at, as one phrase."""
    manifest = root / "lake-manifest.json"
    if not manifest.exists():
        return "no lake-manifest.json here"
    data = json.loads(manifest.read_text(encoding="utf-8"))
    for package in data.get("packages", []):
        if package.get("name") == "mathlib":
            return f"{package.get('inputRev')} ({package.get('rev')})"
    return "lake-manifest.json pins no package named mathlib"


def scan(root: Path, pattern: re.Pattern[str], only: str | None) -> list[tuple[str, str]]:
    rows: list[tuple[str, str]] = []
    for name in population(root):
        if only is not None and name != only:
            continue
        for sentence in sentences(prose_of(root / name, name), pattern):
            rows.append((name, sentence))
    return rows


def report(root: Path, rows: list[tuple[str, str]], listing: bool, what: str) -> None:
    files = len({name for name, _ in rows})
    print(f"Mathlib is pinned at {mathlib_pin(root)}; every sentence below is a claim about it.")
    print(f"{len(rows)} {what} in {files} file{'' if files == 1 else 's'}. These are pattern")
    print("hits and not defects; which are in class, and which are true, is a human step.")
    if listing:
        for name, sentence in rows:
            print()
            print(f"{name}:")
            print(f"  {sentence}")
    else:
        counts: dict[str, int] = {}
        for name, _ in rows:
            counts[name] = counts.get(name, 0) + 1
        for name in sorted(counts, key=lambda k: (-counts[k], k)):
            print(f"  {counts[name]:3d}  {name}")


def self_test() -> int:
    """Positive controls, near misses, and the two readings of a `.lean` file."""
    failures = 0

    def check(label: str, ok: bool) -> None:
        nonlocal failures
        print(f"  [{'ok' if ok else 'FAIL'}] {label}")
        failures += not ok

    hits = [
        "Mathlib does not have this; it sits beside the other one.",
        "Mathlib has no cancellation lemma for this at all.",
        "There is nothing in Mathlib of that shape.",
        "no declaration under Mathlib/CategoryTheory/Galois/ binds two of them.",
        "That statement is not in Mathlib.",
        "The lemma is absent from Mathlib.",
        "mathlib lacks the relative form.",
    ]
    for text in hits:
        check(f"matches: {text[:52]}", bool(ABSENCE.search(text)))

    misses = [
        "Mathlib proves this for IsCoveringMapOn.",
        "This is a candidate for upstreaming to Mathlib.",
        "Mathlib/Topology/Covering/ has only conjugation by a homeomorphism.",
        "There is no lemma below that does it.",
    ]
    for text in misses:
        check(f"no match: {text[:52]}", not ABSENCE.search(text))

    # The whole point of normalising first, and the wrap has to fall *inside* a match for this
    # to be a test of anything: a hard wrap at column 100 puts one there often enough.
    wrapped = "The direction Mathlib\ndoes not have in any form.\n"
    check(
        "a clause wrapped inside the match is found after normalisation",
        bool(ABSENCE.search(re.sub(r"\s+", " ", wrapped))),
    )
    check(
        "and the same pattern on the raw text cannot see it",
        not ABSENCE.search(wrapped),
    )

    lean = (
        "/-!\n# T\n\nMathlib does not have this.\n-/\n\n"
        "-- Mathlib has no such lemma either.\n"
        'theorem t : True := by trivial -- "Mathlib lacks it" is a comment, not code\n'
        'def notes : String := "Mathlib contains no such thing"\n'
    )
    got = sentences(re.sub(r"\s+", " ", comment_content(lean)).strip(), ABSENCE)
    check(
        "a .lean file is read as its comments alone: the module docstring and the two line "
        f"comments are found and the string literal is not (got {len(got)})",
        len(got) == 3 and all("String" not in s for s in got),
    )
    check(
        "and a `-- …` at the end of a line of code is comment content",
        any("not code" in s for s in got),
    )

    nested = "/- outer /- inner\nMathlib has no X.\n-/ still outer -/ code"
    check(
        "block comments nest: the inner one is comment content",
        bool(ABSENCE.search(re.sub(r"\s+", " ", comment_content(nested)))),
    )

    duplicated = "Mathlib has no X. Filler. Mathlib has no X."
    check(
        "the same sentence in one file is reported once",
        len(sentences(duplicated, ABSENCE)) == 1,
    )
    two = "Mathlib has no X and nothing in Mathlib has Y. Filler."
    check(
        "two matches inside one sentence are one row",
        len(sentences(two, ABSENCE)) == 1,
    )

    root = Path(
        subprocess.run(
            ["git", "rev-parse", "--show-toplevel"],
            capture_output=True,
            text=True,
            check=True,
        ).stdout.strip()
    )
    pin = mathlib_pin(root)
    check(f"the Mathlib pin is read out of lake-manifest.json (got {pin})", "(" in pin)

    print("self-test failed" if failures else "self-test passed")
    return 1 if failures else 0


def main() -> int:
    # `--mentions | head` is the normal way to read a 212-file report, and without this the
    # interpreter reports the closed pipe as a traceback on a run that did what was asked.
    try:
        import signal

        signal.signal(signal.SIGPIPE, signal.SIG_DFL)
    except (AttributeError, ValueError):
        pass
    argv = sys.argv[1:]
    if "--self-test" in argv:
        return self_test()
    only = None
    listing = "--list" in argv
    if "--file" in argv:
        index = argv.index("--file")
        if index + 1 >= len(argv):
            print("--file wants a repository-relative path", file=sys.stderr)
            return 2
        only = argv[index + 1]
        listing = True
    unknown = [
        a
        for a in argv
        if a not in ("--list", "--mentions", "--file", "--self-test") and a != only
    ]
    if unknown:
        print(f"unknown argument(s): {' '.join(unknown)}", file=sys.stderr)
        print(__doc__.split("Usage:")[1].split("Exit 0")[0].strip(), file=sys.stderr)
        return 2
    root = Path(
        subprocess.run(
            ["git", "rev-parse", "--show-toplevel"],
            capture_output=True,
            text=True,
            check=True,
        ).stdout.strip()
    )
    mentions = "--mentions" in argv
    pattern = MENTION if mentions else ABSENCE
    what = "sentences name Mathlib" if mentions else "sentences match one of the six shapes"
    report(root, scan(root, pattern, only), listing, what)
    return 0


if __name__ == "__main__":
    sys.exit(main())
