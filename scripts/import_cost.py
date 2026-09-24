#!/usr/bin/env python3
"""Compute what upstreaming a mirror file would add to its Mathlib target's transitive imports.

`README.md`'s mirror-tree section does **not** ask a module docstring to state that number.  It
says the mirror path *"has to survive the imports they need"*, quotes one 96-file precedent, and
works one example through; stating the figure is a practice grown from those, and **26 of the 123
files under `Oka/` follow it** — counting a module docstring that says what upstreaming would cost
its target, whether as a number or as an explicit *nothing*.  A minority, measured at `bd03bee`,
expected to drift, and not a figure anything here depends on.  Counting the *vocabulary* instead
gives 44: forty-four module docstrings say `import`, `closure` or `upstream` somewhere, and **18
of those say it only** in sentences like *"this file is a candidate for upstreaming to Mathlib"*
that state no cost at all.
A number obtained by grepping for a word and reported as a count of measurements is exactly the
species of error this script exists to stop, so it is worth not making it in this paragraph.

Before this script every such figure was produced by a breadth-first search written from scratch
in the session that needed it and thrown away afterwards, and **on 2026-08-23 that instrument was
written wrong twice, by two different agents, and both wrong figures passed the project's standard
validation.**  This is the same computation with a test attached.

Usage:

    python3 scripts/import_cost.py Oka/Algebra/Category/ModuleCat/Sheaf/Generators.lean
    python3 scripts/import_cost.py --target Mathlib.Analysis.Complex.CoveringMap \
        Mathlib.FieldTheory.IsAlgClosed.Basic
    python3 scripts/import_cost.py --self-test

It reads text and nothing else: no build, no oleans, no `lake`.  Exit 0 unless something is wrong
with the arguments or the self-test fails; the cost itself is output, not a verdict, because the
figures live in English prose and nothing can check them mechanically.  See
`.orchestra/validation.sh` for what *is* a gate.

## The defect this exists to stop, which is not hypothetical

The obvious instrument is `re.compile(r"^(?:public\\s+)?import\\s+([\\w.]+)", re.M)` over the raw
file text.  **That matches `import` lines inside comments.**  Under `Mathlib/` there are

* **14 files** carrying such a line, **29 lines** in all — 18 of the lines inside a `/-!` module
  docstring and 7 inside a `/--` declaration docstring, so **12 of the 14 files**; the other 4
  lines, in the two files under `RingTheory/AdicCompletion/`, sit inside a plain `/-` block
  holding commented-out `variable`s and `example`s, with the `import` at the top where a real one
  would go.  **Those two are the better example of the defect**, because nobody would call them
  documentation and the regex matches them anyway;
* **2 of them a bare `import Mathlib`** — `Mathlib/Tactic/Rify.lean` and
  `Mathlib/Analysis/Normed/Algebra/Exponential.lean`, both inside fenced example blocks — at which
  point the computed closure becomes the entire library;
* and one that reaches almost every closure: **`Mathlib/Tactic/FunProp.lean`**, whose documentation
  shows `import Mathlib.Analysis.Complex.Trigonometric` as an example.  Following it pulls that
  module's whole closure — 1238 Mathlib modules — into almost every closure.

**What that edge costs is a fact about the baseline and not about the edge**, so it is quoted here
against named targets rather than as a number on its own.  Against
`Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous` it takes the closure from **1473
to 1744**, so the edge adds **271** — of which only **8** are under `Mathlib/Analysis/`, the rest
being the algebra, topology and order substrate that one analysis module sits on.  Against
`Mathlib.FieldTheory.IsAlgClosed.Basic` it adds **223**; against a closure that already reaches
complex analysis it adds nothing.  **271 is that edge's share and 274 is the whole inflation of
that closure**: the other three are `Mathlib.Algebra.Polynomial.Basic`,
`Mathlib.Data.Sym.Sym2.Init` and `Mathlib.Algebra.Group.AddChar`, reached from phantom edges in
`Mathlib/Tactic/ExtractGoal.lean` and `Mathlib/Tactic/MinImports.lean`.  An earlier draft of this
paragraph read *"that single phantom edge pulls in 274 analysis modules"*, which attaches a total
to a part, calls substrate modules analysis, and gives a baseline-relative figure with no
baseline.  Getting that sentence wrong inside the file whose subject is exactly this is the reason
it is spelled out at length.

The full list, for a reader who wants to check rather than believe: `AlgebraicGeometry/Scheme`,
`Tactic/Rify`, `Tactic/MinImports`, `Tactic/FunProp`, `Tactic/Common`, `Tactic/ExtractGoal`,
`Tactic/Linter/UpstreamableDecl`, `Tactic/Linter/Header`, `LinearAlgebra/Basis/VectorSpace`,
`RingTheory/AdicCompletion/AsTensorProduct`, `RingTheory/AdicCompletion/Functoriality`,
`Algebra/Group/UniqueProds/Basic`, `Data/Int/Log`, `Analysis/Normed/Algebra/Exponential`.  It is a
fact about Mathlib at a version and it will drift; the masking is what does not.

**The direction of the error is not predictable.**  The baseline always inflates, but the marginal
cost can move either way, because the phantom modules land on *both* sides of the subtraction.  In
the real instance, the true cost 103 was reported as 75.  "The total may be off but the delta is
probably fine" is a reading this project has used and it is not safe.

## Why the usual validation does not catch it

The convention here is to check a fresh instrument against the two figures the tree already
carries — `Mathlib.RingTheory.Localization.Finiteness` costs
`Mathlib/AlgebraicGeometry/Modules/Tilde.lean` **2**, and
`Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators` costs
`Mathlib/AlgebraicGeometry/Modules/Sheaf.lean` **3**.  Both are in `self_test` below as regression
cases, and **both reproduce on the broken instrument**: neither target's closure reaches a
comment-embedded import in a way that moves the delta, because they sit in categories and algebra
and the phantom edges lead into analysis.  Two agreeing deltas in one corner of the library are
not a test of a closure computation.  The case that is a test is
`self_test`'s `import Mathlib` fixture, and the tripwire in `closure` is the cheap version of it.

## What is counted

**Mathlib modules only** — modules with a file under `Mathlib/`.  A closure also contains
`Aesop.*`, `Batteries.*`, `Init.*` and `Lean.*`, roughly a hundred of them, and two reviewers have
independently hit that discrepancy and each spent a paragraph attributing it.  The output says so
on every line that carries a number.

## What is priced, and what is not

The headline cost counts only the file's **`Mathlib.` imports**.  An `Oka.` import cannot go into
that sum: a mirror file's cost is against *its own* Mathlib target, not against this one's, so the
two numbers are not comparable and adding them means nothing.

**There is a third number, and it is the one a module docstring actually needs**: what *this*
target pays if that dependency lands at its own mirror path and has to come along.  It is well
defined, it is a `cost` call against a target the script has already resolved in order to print
the `mirrors …` line, and **it is now printed, one figure per dropped import**.

`Oka/Geometry/RingedSpace/LocallyRingedSpace/HasColimits.lean` is why that matters.  It has one
`Mathlib.` import, already in the target's closure, so the headline cost is **0** — and its module
docstring said upstreaming would cost that file *nothing*, which was false: the cover it defines
is stated in terms of `AlgebraicGeometry.LocallyRingedSpace.OpenCover`, whose mirror target costs
that same target **3**.  Repairing it took taxis #1021 and two pull requests.  The author had run
this script; **the script had declined to price the import and the docstring read the silence as
a zero.**  The three modules are now named in the output, which is what that repair had to
compute by hand.

`Oka/Geometry/RingedSpace/PresheafedSpace/Gluing.lean` is the same shape at a scale nobody would
guess: headline cost **0**, while one of its three `Oka.` imports,
`Oka.AlgebraicGeometry.GammaSpecAdjunction`, costs that same target **359** on a baseline of 1697.
Both numbers are true of different questions, and the author is now given both without leaving
the tool.

**It is the number authors were already computing by hand**, which is the argument that it belongs
here rather than in a reader's head.  `Oka/RingTheory/Filtration.lean` — the placement `README.md`
works through — states the whole comparison in its own docstring: closures of **1291** and
**1228**, *"adding `ResidueField.Basic` to `Filtration` costs 33 files; adding `Filtration` to
`ResidueField.Basic` costs 96"*.  All four reproduce exactly, and the 33 is what this script now
prints for that file's one dropped import without being asked.  `self_test` pins both directions,
because 33 on its own decides nothing: the decision was the comparison.

**The dropped figures do not add — not to each other, and not to the headline cost.**  Each is
computed against the same baseline, so shared ancestors are counted twice by anyone who sums
them, and the output says so on the line that introduces them.  This is not a caution about
arithmetic in general: `Oka/AlgebraicGeometry/Modules/Sheaf.lean` is a worked counterexample in
this tree.  Its headline cost is **3** and its `Oka.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`
prices at **5**; taking both is **5**, not 8, because the mirror target's closure already contains
everything the two `Mathlib.` imports add.  `self_test` pins that, and
`Oka/AlgebraicGeometry/Modules/Tilde.lean` records the same trap for the `Mathlib.` imports alone.

**And the figure is conditional, so it is an upper bound on a decision rather than a property of
a file.**  It is what the target pays if the declarations needing that import go upstream with it.
In `HasColimits.lean` the import is needed by the cover, and by what is stated in terms of the
cover, and by nothing else in the file — which is why the repair there was to split the
destination rather than to pay the 3.  Nothing textual can see which declarations need what, and
this script does not pretend to.

**Not every dropped import has a Mathlib file at its own mirror path**, and the output says which
do: measured at `538e13d`, **11 of the 43** files under `Oka/` with a Mathlib target import
another `Oka` module, **18** such import lines between them naming 16 distinct modules.  **3** of
the 18 are mirror files for a Mathlib file that does not exist
(`Oka/AlgebraicGeometry/Modules/Tilde.lean`, `Oka/RingTheory/MvPolynomial/Ideal.lean` and
`Oka/RingTheory/RingHom/FaithfullyFlat.lean` each have one).  Those cannot be priced at all, by
this script or by hand, and the output says so in different words from the ones it uses for a path
that is not a mirror path at all.

Of the 15 that can be priced, **10 cost 0 and 5 cost something**.  That ratio is why the old
behaviour survived as long as it did: ten of those fifteen silences were a correct zero, so
reading one as a zero worked until it did not.

Until this figure was printed the omission had to be argued for, and the argument turned on how
many dropped imports state their own cost somewhere in their own docstrings.  It no longer has
to; what stays is the reason the numbers cannot be **added**, which is above and is unchanged.

## Two limitations a reader should not have to discover

`strip_comments` does not know about string literals, so a `/-` inside one opens a comment as far
as it is concerned.  That cannot bite on this input — imports precede any string literal in a Lean
file, so a spurious open can only blank text *after* the import block — but it is a real
limitation and not an oversight.  And the size check in `closure` is a `raise` rather than an
`assert` deliberately: `python3 -O` strips assertions, and a tripwire that a flag can remove is
not one.
"""

from __future__ import annotations

import re
import subprocess
import sys
from collections import deque
from pathlib import Path

MATHLIB = "/.lake/packages/mathlib"

IMPORT = re.compile(r"^(?:public\s+)?import\s+([\w.]+)", re.M)

# How many modules to name under a *dropped* import's own figure.  The main report lists up to 30,
# which is the number a reader is deciding on; a dropped import's figure is secondary and one file
# can have several of them, so the cap is lower.  10 keeps a whole run readable while still naming
# every module in the case this exists for — three, in
# `Oka/Geometry/RingedSpace/LocallyRingedSpace/HasColimits.lean`.  The two caps are deliberately
# different and neither is load-bearing.
LIST_SKIPPED_UPTO = 10


def strip_comments(text: str) -> str:
    """`text` with comment *contents* removed and newlines kept.

    Block comments nest, and `/-!` and `/--` open one like any other `/-`.  Line comments run to
    the end of the line.  Without this, an `import` line inside a docstring is followed as if it
    were an import; see the module docstring for how much that costs.
    """
    out: list[str] = []
    i = 0
    depth = 0
    n = len(text)
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


class Mathlib:
    """The Mathlib checkout, and import closures within it."""

    def __init__(self, root: Path, mask: bool = True) -> None:
        self.root = root
        self.mask = mask
        self._imports: dict[str, list[str] | None] = {}
        self.total = sum(1 for _ in (root / "Mathlib").rglob("*.lean"))

    def path_of(self, module: str) -> Path:
        return self.root / (module.replace(".", "/") + ".lean")

    def exists(self, module: str) -> bool:
        return self.path_of(module).exists()

    def imports_of(self, module: str) -> list[str] | None:
        """The modules `module` imports, or `None` if it has no file (Aesop, Batteries, …)."""
        if module in self._imports:
            return self._imports[module]
        path = self.path_of(module)
        if not path.exists():
            self._imports[module] = None
            return None
        text = path.read_text(encoding="utf-8")
        found = IMPORT.findall(strip_comments(text) if self.mask else text)
        self._imports[module] = found
        return found

    def closure(self, modules: list[str]) -> set[str]:
        """Every Mathlib module reachable from `modules`, `modules` included.

        The size check is the cheap form of the self-test: a bare `import Mathlib` inside a
        docstring makes the closure the whole library, and no honest closure of a leaf module is
        anywhere near that.  It has fired, and `self_test` fires it deliberately by building an
        unmasked `Mathlib` — a check that has only ever been seen to pass is not evidence.

        It is a `raise` and not an `assert` because `python3 -O` removes assertions.
        """
        seen: set[str] = set()
        queue = deque(modules)
        while queue:
            m = queue.popleft()
            if m in seen:
                continue
            seen.add(m)
            for x in self.imports_of(m) or []:
                if x not in seen:
                    queue.append(x)
        mathlib_only = {m for m in seen if self.exists(m)}
        if len(mathlib_only) >= self.total:
            raise RuntimeError(
                f"closure of {modules} is {len(mathlib_only)} of {self.total} Mathlib files — "
                "that is the whole library, which means a phantom `import Mathlib` was followed"
            )
        return mathlib_only

    def cost(self, target: str, new: list[str]) -> tuple[int, int, set[str]]:
        """`(baseline, cost, the modules added)` for adding `new` to `target`'s closure."""
        base = self.closure([target])
        both = self.closure([target] + new)
        return len(base), len(both) - len(base), both - base


def unknown_modules(ml: Mathlib, modules: list[str]) -> list[str]:
    """Those of `modules` with no file under `Mathlib/`, in order.

    Dropping fileless modules is what implements *What is counted* — a closure is full of
    `Aesop.*` and `Init.*` names that are not Mathlib files — and it is also what makes a typo
    invisible: a module that does not exist contributes no imports and is filtered out of *both*
    sides of the subtraction, so it prices as `cost 0`.  **0 is by far the commonest correct
    answer here** — of the **55** files under `Oka/` with a Mathlib file at their mirror path,
    **41** cost 0 at the commit that adds `Oka/Topology/Maps/Proper/Basic.lean` — so a typo's
    answer is indistinguishable from a right one.  Callers reject instead of reporting.

    **This read *of the 40 files under `Oka/` with a Mathlib file at their mirror path, 31 cost 0*,
    with no commit beside it, until 2026-09-13.**  Both numerals were exact when written and both
    went stale as the mirror tree grew: at `003e38f`, the commit before the one that retires this
    wording, the population is **54** and the cost-0 count is **40**.  So the published population
    had come to equal the current cost-0 count, which is the staleness that reads as a right
    answer, and the pair is pinned here rather than left to drift again.
    """
    return [m for m in modules if not ml.exists(m)]


def target_of(mirror: str) -> str | None:
    """`Oka/X/Y.lean` -> `Mathlib.X.Y`, or `None` when the path is not a mirror path."""
    p = Path(mirror)
    if p.parts[:1] != ("Oka",) or p.suffix != ".lean" or len(p.parts) < 2:
        return None
    return "Mathlib." + ".".join(p.parts[1:-1] + (p.stem,))


def report(ml: Mathlib, target: str, new: list[str],
           skipped: list[str] | None = None) -> None:
    base_set = ml.closure([target])
    added = ml.closure([target] + new) - base_set
    base, delta = len(base_set), len(added)
    print(f"{target.replace('.', '/')}.lean: closure {base} Mathlib modules (Mathlib files only)")
    if not new:
        print("  no Mathlib imports to price")
    else:
        already = sum(1 for m in new if m in base_set)
        print(f"  + {len(new)} Mathlib import(s), {already} already in that closure "
              f"-> cost {delta} Mathlib module(s)")
    if 0 < len(added) <= 30:
        for m in sorted(added):
            print(f"      {m}")
    elif added:
        print(f"      ({len(added)} modules, not listed)")
    if skipped:
        print(f"  not in that sum: {len(skipped)} non-Mathlib import(s), priced one at a time "
              "below,\n  each against the baseline above — so those figures do not add, to each "
              "other or to the cost")
        for m in skipped:
            print(f"      {m}")
            own = target_of(m.replace(".", "/") + ".lean")
            if own is None:
                print("        not a mirror path — there is no target to price it against")
                continue
            if not ml.exists(own):
                print("        mirror path with no Mathlib file — its own figure has no target")
                continue
            _, own_delta, own_added = ml.cost(target, [own])
            print(f"        mirrors {own.replace('.', '/')}.lean, "
                  f"which costs this target {own_delta}")
            if 0 < own_delta <= LIST_SKIPPED_UPTO:
                for x in sorted(own_added):
                    print(f"            {x}")
            elif own_delta:
                print(f"            ({own_delta} modules, not listed)")


def self_test(ml: Mathlib) -> int:
    failures = 0

    def check(name: str, got: object, want: object) -> None:
        nonlocal failures
        ok = got == want
        print(f"  [{'ok' if ok else 'FAIL'}] {name}: got {got!r}, want {want!r}")
        failures += not ok

    # The case the two regression figures below cannot see.  This is the whole point of the file.
    fixture = "module\npublic import A.B\n/-!\n```\nimport Mathlib\n```\n-/\npublic import C.D\n"
    check("an `import` inside a docstring is not followed",
          IMPORT.findall(strip_comments(fixture)), ["A.B", "C.D"])
    check("...and the unmasked regex does follow it, so the fixture is not vacuous",
          IMPORT.findall(fixture), ["A.B", "Mathlib", "C.D"])
    check("a nested block comment closes correctly",
          IMPORT.findall(strip_comments("/- a /- b -/ c -/\npublic import E.F\n")), ["E.F"])
    check("a line comment hides an import",
          IMPORT.findall(strip_comments("-- import G.H\npublic import I.J\n")), ["I.J"])

    # The two figures the tree already carries.  Regression cases, and NOT a test of the masking:
    # both reproduce on an instrument that does not mask, because neither target's closure reaches
    # a comment-embedded import in a way that moves the delta.  See the module docstring.
    check("Localization.Finiteness into Modules/Tilde.lean",
          ml.cost("Mathlib.AlgebraicGeometry.Modules.Tilde",
                  ["Mathlib.RingTheory.Localization.Finiteness"])[1], 2)
    check("ModuleCat.Sheaf.Generators into Modules/Sheaf.lean",
          ml.cost("Mathlib.AlgebraicGeometry.Modules.Sheaf",
                  ["Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators"])[1], 3)

    # Finding: `--target` on a misspelled module used to print `cost 0` and exit 0.  Both
    # directions, so the check cannot go vacuous the way the two regression cases above can.
    check("a misspelled module is rejected rather than priced",
          unknown_modules(ml, ["Mathlib.RingTheory.Localization.Finitenes"]),
          ["Mathlib.RingTheory.Localization.Finitenes"])
    check("...and the correct spelling is not rejected, so the check is not vacuous",
          unknown_modules(ml, ["Mathlib.RingTheory.Localization.Finiteness"]), [])

    # The tripwire in `closure`, fired on purpose rather than reasoned about.  An unmasked
    # `Mathlib` follows the bare `import Mathlib` in `Mathlib/Tactic/Rify.lean`'s docstring and
    # reaches the whole library; the masked instance below is the control that says the fixture
    # is about masking and not about this particular target.
    unmasked = Mathlib(ml.root, mask=False)
    try:
        unmasked.closure(["Mathlib.Analysis.Complex.CoveringMap"])
        fired: object = "no error"
    except RuntimeError:
        fired = "RuntimeError"
    check("the whole-library tripwire fires on an unmasked closure", fired, "RuntimeError")
    check("...and does not fire on the masked one",
          len(ml.closure(["Mathlib.Analysis.Complex.CoveringMap"])) < ml.total, True)

    check("a mirror path maps to its target",
          target_of("Oka/Algebra/Category/ModuleCat/Sheaf/Free.lean"),
          "Mathlib.Algebra.Category.ModuleCat.Sheaf.Free")
    check("a non-mirror path maps to nothing", target_of("scripts/Foo.lean"), None)

    # The figures printed for a *dropped* `Oka.` import.  The first is the case that caused this
    # part of the script to exist: a module docstring said upstreaming cost its target nothing,
    # having read `not priced` as a zero.  Its control is the reverse direction, which really is
    # 0 — so the 3 is an asymmetry between two Mathlib files and not an artefact of the caller.
    check("PresheafedSpace/Gluing into LocallyRingedSpace/HasColimits.lean",
          ml.cost("Mathlib.Geometry.RingedSpace.LocallyRingedSpace.HasColimits",
                  ["Mathlib.Geometry.RingedSpace.PresheafedSpace.Gluing"])[1], 3)
    check("...and the other direction is free, so the 3 is not symmetric",
          ml.cost("Mathlib.Geometry.RingedSpace.PresheafedSpace.Gluing",
                  ["Mathlib.Geometry.RingedSpace.LocallyRingedSpace.HasColimits"])[1], 0)

    # The figure the module docstring quotes for `Oka/Geometry/RingedSpace/PresheafedSpace/
    # Gluing.lean`, which it stated by hand before the script produced it.
    check("GammaSpecAdjunction into PresheafedSpace/Gluing.lean",
          ml.cost("Mathlib.Geometry.RingedSpace.PresheafedSpace.Gluing",
                  ["Mathlib.AlgebraicGeometry.GammaSpecAdjunction"])[1], 359)

    # The asymmetry `Oka/RingTheory/Filtration.lean` records as the reason for its own placement,
    # and which `README.md` quotes as this project's worked example.  Both halves, because the
    # decision is the *comparison* — 33 on its own says nothing about where the file should go.
    check("ResidueField/Basic.lean into Filtration.lean",
          ml.cost("Mathlib.RingTheory.Filtration",
                  ["Mathlib.RingTheory.LocalRing.ResidueField.Basic"])[1], 33)
    check("...and Filtration.lean into ResidueField/Basic.lean, the direction not taken",
          ml.cost("Mathlib.RingTheory.LocalRing.ResidueField.Basic",
                  ["Mathlib.RingTheory.Filtration"])[1], 96)

    # The non-additivity the output warns about, pinned on the tree's own worked counterexample:
    # 3 + 5 is 8 and the joint cost is 5.  A warning nothing demonstrates is a warning nobody has
    # a reason to believe, and this one is cheap to demonstrate.
    sheaf = "Mathlib.AlgebraicGeometry.Modules.Sheaf"
    quasi = "Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent"
    own_mathlib = ["Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators", sheaf]
    check("Modules/Sheaf.lean: its own Mathlib imports cost 3",
          ml.cost(sheaf, own_mathlib)[1], 3)
    check("...its dropped Quasicoherent import costs 5",
          ml.cost(sheaf, [quasi])[1], 5)
    check("...and taking both costs 5, not 8 — the two figures overlap",
          ml.cost(sheaf, own_mathlib + [quasi])[1], 5)

    # The branch that prints no figure, and its control.  Both are facts about the Mathlib pin.
    check("a dropped import can mirror a Mathlib file that does not exist",
          ml.exists(target_of(
              "Oka/Algebra/Category/ModuleCat/Sheaf/Coherent/Presentation.lean") or ""), False)
    check("...and a dropped import beside it in the same file does exist",
          ml.exists(target_of("Oka/AlgebraicGeometry/Modules/Sheaf.lean") or ""), True)

    print("self-test failed" if failures else "self-test passed")
    return 1 if failures else 0


def reject_unknown(ml: Mathlib, modules: list[str]) -> bool:
    """Report any of `modules` that has no Mathlib file, and say why that is not a `cost 0`."""
    bad = unknown_modules(ml, modules)
    for m in bad:
        print(f"{m}: no file at {ml.path_of(m)}")
    if bad:
        print("no figure computed: an unknown module would price as `cost 0`, which is also the "
              "commonest correct answer, so it is rejected instead")
    return bool(bad)


def main() -> int:
    root = Path(
        subprocess.run(
            ["git", "rev-parse", "--show-toplevel"],
            capture_output=True, text=True, check=True,
        ).stdout.strip()
    )
    mathlib_root = Path(str(root) + MATHLIB)
    if not (mathlib_root / "Mathlib").is_dir():
        print(f"no Mathlib checkout at {mathlib_root}; run `lake exe cache get` first")
        return 2
    ml = Mathlib(mathlib_root)

    args = sys.argv[1:]
    if "--self-test" in args:
        return self_test(ml)

    if args[:1] == ["--target"]:
        if len(args) < 2:
            print("--target needs a module name")
            return 2
        target, mods = args[1], args[2:]
        if reject_unknown(ml, [target] + mods):
            return 2
        report(ml, target, mods)
        return 0

    if len(args) != 1:
        print(__doc__.split("Usage:")[1].split("It reads text")[0].strip())
        return 2

    mirror = args[0]
    target = target_of(mirror)
    if target is None:
        print(f"{mirror} is not a mirror path (`Oka/X/Y.lean`); use --target to price by hand")
        return 2
    if not ml.exists(target):
        print(f"{mirror} mirrors {target.replace('.', '/')}.lean, which does not exist in Mathlib")
        return 2
    path = root / mirror
    if not path.exists():
        print(f"{mirror} does not exist")
        return 2
    found = IMPORT.findall(strip_comments(path.read_text(encoding="utf-8")))
    mods = [m for m in found if m.startswith("Mathlib.")]
    if reject_unknown(ml, mods):
        return 2
    report(ml, target, mods, [m for m in found if not m.startswith("Mathlib.")])
    return 0


if __name__ == "__main__":
    sys.exit(main())
