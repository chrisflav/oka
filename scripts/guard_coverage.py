#!/usr/bin/env python3
"""Report which declarations a module docstring advertises as main results and nothing guards.

`OkaTest/Axioms/` is this repository's regression test that the library rests only on `propext`,
`Classical.choice` and `Quot.sound`.  `OkaTest/Axioms.lean` states a **placement** rule — which
file, which heading — and says nothing about which declarations ought to be guarded, so a reader
is entitled to think the guards are complete.  They are not, nothing measured how incomplete, and
this is the measurement.

Usage:

    python3 scripts/guard_coverage.py                 # the report
    python3 scripts/guard_coverage.py --by-file       # ...with every gap listed by file
    python3 scripts/guard_coverage.py --self-test
    python3 scripts/guard_coverage.py --dump FILE     # reuse a declaration dump
    python3 scripts/guard_coverage.py --env-dump FILE # ...and reconcile against `DumpEnvNames`

It runs `lake env lean scripts/DumpOkaDecls.lean` unless `--dump` is given, so the build must
have run first: it reads the oleans, it does not produce them.

**This is a reporter and not a gate, and it must not be wired into `.orchestra/validation.sh`.**
The correct number of unguarded results is not zero, nobody has decided what it should be, and a
check that fails on the current tree is a check somebody will disable.  `scripts/import_cost.py`
is the model, and its docstring gives the reason in a sentence: *"the cost itself is output, not a
verdict, because the figures live in English prose and nothing can check them mechanically."*
Exit is 0 whatever the coverage is, and non-zero only when an argument is wrong, the dump cannot
be built, or the self-test fails.

## Comparing two reports takes both flags and one dump pair held fixed

Two runs are comparable only if they were handed the **same two dumps**, and the `--env-dump` half
of that is the one that gets missed.  Without it the skipped-token row prints counts and no
per-token site, so no line number appears anywhere in the report and a difference confined to
prose outside a `## Main results` section cannot show up at all: the two reports come out
byte-identical and the flat result reads like evidence rather than like a missing flag.  With it,
but with a dump rebuilt per tree, the opposite failure follows: the skipped-token reconciliation
moves with the dump as well as with the prose, so a difference that does show up is not
attributable to the prose.  Neither announces itself, so **a replay reporting what moved between
two trees owes the pair it was given**, and holding one pair fixed across all of them is what
makes the answer mean anything.

## The defect this exists to stop

`ComplexAnalytic.AnalyticSpace.sigmaι_sigmaDesc` was added to `Oka/AnalyticSpace/Sigma.lean`'s
`## Main results` by lana-agents/oka#191 — which was itself taking a reviewer's note that the list
was missing it — **without the matching guard**, and the two lists then disagreed by exactly one
entry.  It was caught by a reviewer reading both lists by eye, routed to taxis #1051 and fixed in
lana-agents/oka#194.  Nothing mechanical would have caught it.  The argument that settled it was a
precedent inside the same guard file: `ComplexAnalytic.AnalyticSpace.ι_glueMorphisms` was already
guarded and stands to `glueMorphisms` exactly as `sigmaι_sigmaDesc` stands to `sigmaDesc`.  That
is a good argument about one declaration and it does not scale.

## What is counted, and it is not what a prefix test would count

*Guarded* is a `#print axioms <name>` command under `OkaTest/Axioms/`, with comments masked.
*Advertised* is a backticked token inside a `## Main results` section of a **module** docstring
under `Oka/`, kept when it names a declaration this repository owns.

Ownership is read from `scripts/DumpOkaDecls.lean`, which asks Lean which module declared each
constant.  A prefix test on the name would be wrong in both directions: this repository declares
into `AlgebraicGeometry`, `CategoryTheory` and `Polynomial` from its mirror tree — those names
have nothing beginning with `Oka` about them — and a `## Main results` section may cite a Mathlib
declaration in a namespace this repository also declares into.  So `AlgebraicGeometry.…` alone
decides nothing, and the dump is what separates the two.

## Four things it cannot see, in decreasing order of how much they matter

* **A main result named in prose and not backticked is invisible**, so the *advertised* figure is
  a lower bound on what the docstrings claim.  `Oka/Weierstrass.lean`'s `localweierstrass_division`
  is backticked and guarded and so lands in the overlap; a result described in words is not
  counted at all.
* **It has no opinion about whether a name ought to be guarded.**
  `Oka/Analytic/ParametricCircleIntegral.lean` is general complex analysis with a Mathlib
  destination and guarding all 17 of its advertised results may well be the wrong call.  The
  number is a measurement and the judgement is a human one; see `OkaTest/Axioms.lean`.
* **The reverse direction is not a defect.**  A guard on a lemma no docstring advertises is fine
  and there are many; the count is printed because it is the other half of the divergence, not
  because anything should be done about it.
* **A `## Main results` list can advertise a declaration that lives in another file.**  That is
  legitimate — a file may be the natural place to announce a result it re-exports — and the
  report says how many such entries there are rather than treating them as errors.

## Why the instrument gets its own self-test

`scripts/import_cost.py` records that the obvious instrument for *its* question "was written
wrong twice, by two different agents, and both wrong figures passed the project's standard
validation."  This is the same species: a count over docstrings, produced once, quoted afterwards
in prose that nothing checks.  The failure that actually happened here is on this issue's own
thread — the first version of taxis #1057 gave five figures that were all correct about the tree
they were taken on, which was the filer's branch and not `master`.  **A number can be right and
its description wrong**, and no self-test can catch that one; what `--self-test` does catch is the
extraction, which is the part with a wrong answer that looks like a right one.

Both halves are pinned with a control, so neither check can go vacuous: the masking fixture
asserts that the unmasked regex *does* find the thing masking removes, and the module-docstring
fixture asserts that the same text in a `/--` declaration docstring is *not* read as a list of
main results.
"""

from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys
import tempfile

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DUMP_SCRIPT = os.path.join("scripts", "DumpOkaDecls.lean")
LIBRARY_DIR = "Oka"
GUARD_DIR = os.path.join("OkaTest", "Axioms")

PRINT_AXIOMS = re.compile(r"^[ \t]*#print axioms(?:[ \t]+|[ \t]*\n[ \t]+)(\S+)[ \t]*$", re.M)
PRINT_AXIOMS_CMD = re.compile(r"^[ \t]*#print axioms\b", re.M)
BACKTICKED = re.compile(r"`([^`\s]+)`")
MAIN_RESULTS = re.compile(r"^#{1,6}\s+Main results\s*$")
HEADING = re.compile(r"^#{1,6}\s")


def strip_comments(text: str) -> str:
    """`text` with comment *contents* removed and newlines kept.

    Block comments nest, and `/-!` and `/--` open one like any other `/-`; line comments run to
    the end of the line.  Without this a `#print axioms` shown inside a docstring — which is how
    one would document the convention — would be counted as a guard.
    """
    out: list[str] = []
    i, depth, n = 0, 0, len(text)
    while i < n:
        if depth == 0 and text.startswith("--", i):
            j = text.find("\n", i)
            i = n if j < 0 else j
            continue
        if text.startswith("/-", i):
            depth += 1
            i += 2
            continue
        if text.startswith("-/", i) and depth > 0:
            depth -= 1
            i += 2
            continue
        if depth == 0:
            out.append(text[i])
        elif text[i] == "\n":
            out.append("\n")
        i += 1
    return "".join(out)


def module_docstrings(text: str) -> list[tuple[int, str]]:
    """`(offset, contents)` for every `/-! … -/` region, nesting as Lean's comments do.

    Declaration docstrings (`/-- … -/`) and plain comments are deliberately not returned: a
    `## Main results` heading is a module-docstring convention, and a `/--` on a declaration that
    happened to contain one would otherwise be read as a second list.
    """
    out: list[tuple[int, str]] = []
    i, n = 0, len(text)
    while i < n:
        if text.startswith("--", i):
            j = text.find("\n", i)
            i = n if j < 0 else j + 1
            continue
        if text.startswith("/-", i):
            module = text.startswith("/-!", i)
            depth, j = 1, i + 2
            start = j
            while j < n and depth > 0:
                if text.startswith("/-", j):
                    depth += 1
                    j += 2
                elif text.startswith("-/", j):
                    depth -= 1
                    j += 2
                else:
                    j += 1
            end = j - 2 if depth == 0 else n
            if module:
                out.append((start, text[start:end]))
            i = j
            continue
        if text[i] == '"':
            j = i + 1
            while j < n:
                if text[j] == "\\":
                    j += 2
                elif text[j] == '"':
                    j += 1
                    break
                else:
                    j += 1
            i = j
            continue
        i += 1
    return out


def main_results_tokens(text: str) -> list[tuple[str, int]]:
    """Every backticked token inside a `## Main results` section of a module docstring.

    A section runs from its heading to the next heading of any level or to the end of the
    docstring, so a `## What is not here` list — which on this project cites the names of things
    that are *absent* — cannot leak into the count.
    """
    out: list[tuple[str, int]] = []
    for offset, body in module_docstrings(text):
        pos = 0
        inside = False
        for line in body.splitlines(keepends=True):
            if MAIN_RESULTS.match(line):
                inside = True
            elif HEADING.match(line):
                inside = False
            elif inside:
                for m in BACKTICKED.finditer(line):
                    at = offset + pos + m.start()
                    out.append((m.group(1), text.count("\n", 0, at) + 1))
            pos += len(line)
    return out


def guarded_names(text: str) -> list[tuple[str, int]]:
    """Every `#print axioms <name>` in `text`, comments masked.

    The name may be on the line after the command: one guard in this repository is
    `#print axioms` followed by an indented 100-character name, because that is what fits.  **The
    obvious line regex misses it**, and both instruments that have counted these guards missed it
    — at `0b19eb1` the count was reported as 471, in the issue that asked for this script and
    again in this script's first draft, and it was 472.  `guard_count` is the tripwire that
    would have said so.
    """
    masked = strip_comments(text)
    return [(m.group(1), masked.count("\n", 0, m.start()) + 1)
            for m in PRINT_AXIOMS.finditer(masked)]


def guard_count(text: str) -> int:
    """How many `#print axioms` commands `text` has, however their argument is laid out.

    Compared against `len(guarded_names(text))` by the caller, so that a layout this file does not
    parse is reported rather than silently dropped.  A count and an extraction that disagree is
    the only way an instrument like this one can say *"there is something here I did not read"*.
    """
    return len(PRINT_AXIOMS_CMD.findall(strip_comments(text)))


def lean_files(*roots: str) -> list[str]:
    """Every `.lean` file under `roots`, repository-relative and sorted."""
    paths: list[str] = []
    for root in roots:
        for dirpath, _, filenames in os.walk(os.path.join(REPO, root)):
            paths += [os.path.relpath(os.path.join(dirpath, f), REPO)
                      for f in filenames if f.endswith(".lean")]
    return sorted(paths)


def read_decls(dump: str) -> dict[str, str]:
    """`name -> declaring module`, from `scripts/DumpOkaDecls.lean`'s output."""
    decls: dict[str, str] = {}
    with open(dump, encoding="utf-8") as f:
        for line in f:
            module, _, name = line.rstrip("\n").partition("\t")
            if name:
                decls[name] = module
    return decls


def read_env(dump: str) -> set[str]:
    """Every name in `scripts/DumpEnvNames.lean`'s output — the whole environment, Mathlib too.

    Each line there is `<kind>` TAB `<name>` with `kind` either `module` or `decl`, and a name
    never contains a tab; **an untagged line is the whole name**, which is what a dump written
    before the tag existed looks like.  Nothing here cares which kind a name is — this set is
    only ever asked *whether it contains* a name — so the tag is stripped and discarded.  It is
    stripped rather than ignored because a line read whole would put `decl\tFoo.bar` in the set
    and `Foo.bar` out of it, and the only symptom would be a name reported as unknown.
    """
    out = set()
    with open(dump, encoding="utf-8") as f:
        for line in f:
            line = line.rstrip("\n")
            if not line.strip():
                continue
            kind, tab, rest = line.partition("\t")
            out.add(rest if tab and kind in ("module", "decl") else line)
    return out


def build_dump() -> str:
    """Run `scripts/DumpOkaDecls.lean` and return the path it wrote."""
    fd, path = tempfile.mkstemp(prefix="oka-decls-", suffix=".txt")
    os.close(fd)
    proc = subprocess.run(
        ["lake", "env", "lean", DUMP_SCRIPT], cwd=REPO,
        env=dict(os.environ, OKA_DECL_DUMP=path), capture_output=True, text=True,
    )
    if proc.returncode != 0 or not os.path.getsize(path):
        sys.stderr.write(proc.stdout + proc.stderr)
        sys.stderr.write(
            "\nFailed to dump the declarations of `Oka` + `OkaTest`. `lake build` must have run\n"
            "first: this reads the oleans, it does not produce them.\n"
        )
        os.unlink(path)
        sys.exit(2)
    return path


def module_of(path: str) -> str:
    """`Oka/Foo/Bar.lean` -> `Oka.Foo.Bar`."""
    return path[:-len(".lean")].replace(os.sep, ".")


def report(decls: dict[str, str], env: set[str] | None, by_file: bool) -> None:
    guarded: dict[str, str] = {}
    unread: list[tuple[str, int, int]] = []
    for path in lean_files(GUARD_DIR):
        with open(os.path.join(REPO, path), encoding="utf-8") as f:
            text = f.read()
        found = guarded_names(text)
        for name, _ in found:
            guarded[name] = path
        if len(found) != guard_count(text):
            unread.append((path, guard_count(text), len(found)))

    advertised: dict[str, set[str]] = {}
    foreign: dict[str, int] = {"module": 0, "Mathlib": 0, "other": 0}
    unresolved: list[tuple[str, str, int]] = []
    unresolved_all: list[tuple[str, str, int]] = []
    modules = {module_of(p) for p in lean_files(LIBRARY_DIR, "OkaTest")} | {"Oka", "OkaTest"}
    for path in lean_files(LIBRARY_DIR) + ["Oka.lean"]:
        with open(os.path.join(REPO, path), encoding="utf-8") as f:
            text = f.read()
        for token, line in main_results_tokens(text):
            if token in decls:
                advertised.setdefault(path, set()).add(token)
                continue
            unresolved_all.append((token, path, line))
            if token in modules:
                foreign["module"] += 1
            elif token.startswith("Mathlib.") or (env is not None and token in env):
                foreign["Mathlib"] += 1
            else:
                foreign["other"] += 1
                unresolved.append((token, path, line))

    names = {n for ns in advertised.values() for n in ns}
    unguarded = names - set(guarded)
    gaps = {path: sorted(ns - set(guarded)) for path, ns in advertised.items()}
    gaps = {path: ns for path, ns in gaps.items() if ns}
    elsewhere = sum(1 for path, ns in advertised.items() for n in ns
                    if decls[n] != module_of(path))

    print(f"guards under {GUARD_DIR}/            {len(guarded)} distinct names, "
          f"{len(lean_files(GUARD_DIR))} files")
    print(f"advertised in a `## Main results`   {len(names)} distinct declarations of this "
          f"repository, in {len(advertised)} files")
    print(f"  of those, unguarded               {len(unguarded)}"
          f" ({100 * len(unguarded) // max(len(names), 1)}%), in {len(gaps)} files")
    print(f"  in both lists                     {len(names) - len(unguarded)}")
    print(f"guarded and advertised nowhere      {len(set(guarded) - names)}"
          "  (not a defect — see this script's docstring)")
    print(f"advertised from another file        {elsewhere}")
    suffixes: dict[str, set[str]] = {}
    for name in decls:
        parts = name.split(".")
        for i in range(1, len(parts)):
            suffixes.setdefault(".".join(parts[i:]), set()).add(name)
    abbreviated = sorted({t for t, _, _ in unresolved_all if t in suffixes})
    dotted = [t for t in abbreviated if "." in t]
    print(f"abbreviated citations, not counted  {len(abbreviated)}"
          f" ({len(dotted)} of them dotted) — so the figure above is a lower bound")
    if by_file:
        for token in abbreviated:
            owners = sorted(suffixes[token])
            print(f"      `{token}` -> {owners[0]}"
                  f"{f'  (ambiguous, {len(owners)} declarations)' if len(owners) > 1 else ''}")
    print(f"backticked tokens skipped           {foreign['module']} repository module name(s), "
          f"{foreign['Mathlib']} name(s) this repository does not declare, "
          f"{foreign['other']} that resolve to nothing")
    if env is None and foreign["other"]:
        print("  (without --env-dump the last two cannot be told apart for a name outside the\n"
              "   `Mathlib.` namespace; the count above is an upper bound on real typos)")
    for token, path, line in unresolved if env is not None else []:
        print(f"      {path}:{line}: `{token}`")
    for path, commands, read in unread:
        print(f"  !! {path}: {commands} `#print axioms` command(s), {read} name(s) read — "
              "a layout this script does not parse")
    guards_outside = sorted(set(guarded) - set(decls))
    if guards_outside:
        print(f"guards on declarations this repository does not own: {len(guards_outside)}")
        for name in guards_outside:
            print(f"      {name}  ({guarded[name]})")

    print()
    print("largest gaps (unguarded / advertised):")
    order = sorted(gaps, key=lambda p: (-len(gaps[p]), p))
    for path in order if by_file else order[:12]:
        print(f"  {len(gaps[path]):3d} / {len(advertised[path]):-3d}  {path}")
        if by_file:
            for name in gaps[path]:
                print(f"           {name}")
    if not by_file and len(order) > 12:
        print(f"  ({len(order) - 12} more files with a gap; --by-file lists every one)")


def self_test() -> int:
    failures = 0

    def check(name: str, got: object, want: object) -> None:
        nonlocal failures
        ok = got == want
        print(f"  [{'ok' if ok else 'FAIL'}] {name}: got {got!r}, want {want!r}")
        failures += not ok

    # The fixture taxis #1057 asks for: a guarded name, an unguarded name, a repository module
    # name and a `Mathlib.` name, in one `## Main results` block.
    fixture = (
        "/-!\n# A file\n\n## Main results\n\n"
        "- `Oka.Guarded.thm` and `Oka.Unguarded.thm`, proved from `Mathlib.Order.Basic`'s\n"
        "  machinery; see `Oka.Weierstrass`.\n\n"
        "## What is not here\n\n- `Oka.Absent.thm`, which nothing proves.\n-/\n"
        "/-- `Oka.NotAMainResult.thm` is only a declaration docstring.\n\n"
        "## Main results\n\n- `Oka.AlsoNotOne.thm`\n-/\ntheorem foo : True := trivial\n"
    )
    check("every backticked token of the `## Main results` block, and only those",
          [t for t, _ in main_results_tokens(fixture)],
          ["Oka.Guarded.thm", "Oka.Unguarded.thm", "Mathlib.Order.Basic", "Oka.Weierstrass"])
    decls = {"Oka.Guarded.thm": "Oka.A", "Oka.Unguarded.thm": "Oka.B", "Oka.Absent.thm": "Oka.C"}
    check("...of which two are declarations of this repository",
          sorted({t for t, _ in main_results_tokens(fixture) if t in decls}),
          ["Oka.Guarded.thm", "Oka.Unguarded.thm"])
    check("a `## What is not here` name is not advertised, though it is a declaration",
          "Oka.Absent.thm" in [t for t, _ in main_results_tokens(fixture)], False)
    check("a `## Main results` inside a `/--` docstring is not a list of main results",
          [t for t in ["Oka.NotAMainResult.thm", "Oka.AlsoNotOne.thm"]
           if t in [x for x, _ in main_results_tokens(fixture)]], [])
    check("...and the same text opened with `/-!` is, so the control is not vacuous",
          [t for t, _ in main_results_tokens(
              "/-!\n## Main results\n\n- `Oka.AlsoNotOne.thm`\n-/\n")],
          ["Oka.AlsoNotOne.thm"])

    # A heading of a different level closes the section too; `Oka/` uses `##` throughout today,
    # and a file that used `###` for its subsections would otherwise leak them into the count.
    check("a deeper heading closes the section",
          [t for t, _ in main_results_tokens(
              "/-!\n## Main results\n\n- `Oka.In.thm`\n\n### A digression\n\n- `Oka.Out.thm`\n-/")],
          ["Oka.In.thm"])

    # Masking, with its control.  A `#print axioms` shown inside a docstring is how one documents
    # the convention, and `OkaTest/Axioms.lean` does exactly that in prose.
    guards = ("/-- info: 'A.b' depends on axioms: [propext] -/\n#guard_msgs in\n"
              "#print axioms A.b\n/-!\nRun `#print axioms C.d` yourself.\n"
              "\n    #print axioms E.f\n-/\n")
    check("a guard inside a docstring is not counted",
          [n for n, _ in guarded_names(guards)], ["A.b"])
    check("...and the unmasked regex does count it, so the fixture is not vacuous",
          PRINT_AXIOMS.findall(guards), ["A.b", "E.f"])
    check("a nested block comment closes correctly",
          [n for n, _ in guarded_names("/- a /- b -/ c -/\n#print axioms I.j\n")], ["I.j"])
    # A line comment is *not* an argument for the masking: `PRINT_AXIOMS` anchors at the start of
    # a line, so `-- #print axioms` never matched.  Indentation is allowed, though, and the two
    # differ by two characters — so both directions are pinned rather than one asserted.
    check("a line comment cannot fake a guard, masked or not",
          ([n for n, _ in guarded_names("-- #print axioms G.h\n")],
           PRINT_AXIOMS.findall("-- #print axioms G.h\n")), ([], []))
    check("...while an indented guard outside a comment is one",
          [n for n, _ in guarded_names("  #print axioms K.l\n")], ["K.l"])

    # The instance in this tree, and the reason the count was 471 twice: one name is 100
    # characters and does not fit after the command.
    wrapped = ("#guard_msgs (whitespace := lax) in\n#print axioms\n"
               "  A.very.long.name_of_isCoherent\n")
    check("a guard whose name is on the next line is read",
          [n for n, _ in guarded_names(wrapped)], ["A.very.long.name_of_isCoherent"])
    check("...and the same text read as one line per guard misses it, which is the defect",
          re.findall(r"^[ \t]*#print axioms[ \t]+(\S+)[ \t]*$", wrapped, re.M), [])
    # The tripwire, fired on a layout deliberately outside what `PRINT_AXIOMS` accepts.  A check
    # that has only ever been seen to pass is not evidence.
    check("a layout the extraction cannot read is counted and reported, not dropped",
          (guard_count("#print axioms\n\nM.n\n"),
           len(guarded_names("#print axioms\n\nM.n\n"))), (1, 0))
    check("...and the two agree on a layout it can read",
          (guard_count(wrapped), len(guarded_names(wrapped))), (1, 1))

    print("self-test FAILED" if failures else "self-test passed")
    return 1 if failures else 0


def main() -> int:
    ap = argparse.ArgumentParser(
        description="Report the declarations advertised as main results that nothing guards.")
    ap.add_argument("--dump", metavar="FILE",
                    help="reuse a `scripts/DumpOkaDecls.lean` dump instead of building one")
    ap.add_argument("--env-dump", metavar="FILE",
                    help="a `scripts/DumpEnvNames.lean` dump, to tell a Mathlib name from a typo")
    ap.add_argument("--by-file", action="store_true",
                    help="list every file with a gap, and every unguarded name in it")
    ap.add_argument("--self-test", action="store_true", help="check the extraction on fixtures")
    args = ap.parse_args()
    if args.self_test:
        return self_test()
    dump = args.dump or build_dump()
    try:
        report(read_decls(dump), read_env(args.env_dump) if args.env_dump else None, args.by_file)
    finally:
        if not args.dump:
            os.unlink(dump)
    return 0


if __name__ == "__main__":
    sys.exit(main())
