/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.AnalyticSpace.FiniteEtaleBaseChange
import Oka.AnalyticSpace.FiniteEtaleOver

/-!
# Finite étaleness is a `CategoryTheory.MorphismProperty` stable under base change

`ComplexAnalytic.AnalyticSpace.isFiniteEtale` is `CategoryTheory.MorphismProperty` stable under
base change: for **every** pullback square in `ComplexAnalytic.AnalyticSpace` whose right-hand leg
is finite étale, the opposite leg is finite étale. The class is Mathlib's and asks nothing of the
four objects and nothing of the morphism being base-changed along —
`Mathlib/CategoryTheory/MorphismProperty/Limits.lean`:

```lean
class IsStableUnderBaseChange : Prop where
  of_isPullback {X Y Y' S : C} {f : X ⟶ S} {g : Y ⟶ S} {f' : Y' ⟶ Y} {g' : Y' ⟶ X}
    (sq : IsPullback f' g' g f) (hg : P g) : P g'
```

**In particular no separation axiom appears anywhere**, and that is what makes the statement
reachable: `ComplexAnalytic.AnalyticSpace.doubledLineFold` is a finite étale morphism whose source
is not Hausdorff, so the cospans this class quantifies over include ones no statement of this
repository could reach until `Oka/AnalyticSpace/FiniteEtaleBaseChange.lean` dropped `[T2Space E]`
on 2026-09-14. `OkaTest/FiniteEtaleBaseChangeNonHausdorff.lean` applies the instance below at that
cospan rather than citing it.

## Why this is one declaration in a file of its own

The statement is an assembly of two things that are on `master` and in neither's import closure.

* `ComplexAnalytic.AnalyticSpace.isFiniteEtale`, the `CategoryTheory.MorphismProperty`, is
  declared in `Oka/AnalyticSpace/FiniteEtaleOver.lean`.
* `ComplexAnalytic.AnalyticSpace.isFiniteEtale_pullback_snd_of_isFiniteEtale`, the base change at
  `CategoryTheory.Limits.pullback`, is in `Oka/AnalyticSpace/FiniteEtaleBaseChange.lean`.

**Neither of those two files is in the other's import closure**, by a transitive walk of the
`Oka`-prefixed `import` lines of the whole tree, the `public import` ones counted too — 57 modules
under `Oka/AnalyticSpace/FiniteEtaleOver.lean` and 56 under
`Oka/AnalyticSpace/FiniteEtaleBaseChange.lean`, neither set containing the other module — and the
direction that matters is the first: `ComplexAnalytic.AnalyticSpace.isFiniteEtale` is an
*Unknown constant* in a file importing `Oka.AnalyticSpace.FiniteEtaleBaseChange` alone, which was
run and not read off the import lines. So the instance cannot be written in the base-change file
without adding an import to it, and it cannot be written in
`Oka/AnalyticSpace/FiniteEtaleOver.lean` without putting the whole base-change construction into
the closure of every consumer of the category of covers.

**What is *not* true is that nothing joined them already, and the measurement is the reason this
file is placed where it is rather than merely that it exists.** The same walk reports **eleven**
modules under `Oka/` other than this one whose closure holds both, and exactly one of them is
minimal for that property — `Oka/AnalyticSpace/MonoDirectSummand.lean`, at 66, which
`Oka/AnalyticSpace/SeparatedOver.lean` is above and the remaining nine reach through that file.
The instance could have been written in any of the eleven.
**It is not, because each of them is about a narrower subject than the class**: monomorphisms and
the direct summand one cuts out, or the category of separated covers. A statement about every
finite étale morphism of `ComplexAnalytic.AnalyticSpace` placed in one of those is findable only
by a reader who is already there, and a consumer that wants the class would import that subject's
construction to get it. This file's closure is 65 modules, against 66 for
`Oka/AnalyticSpace/MonoDirectSummand.lean`, so the placement is also not paid for in imports.

**The count of modules joining the two read seven while this file was cut from `ddcc4c6` and has
moved four times since, under pushes touching no line of this file**: `8d50165`, `7577386`,
`321879e` and `fbe1e95` each add one module above `Oka/AnalyticSpace/SeparatedOver.lean` — the
last of them `Oka/AnalyticSpace/SeparatedFiberPullback.lean` — and it is re-taken at every re-cut.
**No dated record is owed and this is not one of this repository's** — no retired figure landed,
and each was exact at the base it was measured at. **This paragraph stands after the one it
qualifies rather than inside it**, so that the *It* and the *each of them* there resume the count
of modules and not a figure of this one.

## The proof, and the one place a choice is made

A pullback square is not *the* pullback, so the proof has to move the property across
`CategoryTheory.IsPullback.isoPullback`, the comparison of an arbitrary pullback square with
`CategoryTheory.Limits.pullback` of the same cospan. That comparison exists because
`ComplexAnalytic.AnalyticSpace.hasPullback_of_isFiniteEtale` supplies the limit at this cospan,
and the transfer is `CategoryTheory.IsPullback.isoPullback_hom_snd` together with
`ComplexAnalytic.AnalyticSpace.isFiniteEtale_of_isIso` and
`ComplexAnalytic.AnalyticSpace.isFiniteEtale_comp`.

**The same transfer is available as `(isFiniteEtale.{u}).RespectsIso`**, which
`Oka/AnalyticSpace/FiniteEtaleOver.lean` declares and which
`CategoryTheory.MorphismProperty.IsStableUnderBaseChange.mk'` asks for; that route is not taken
below because `mk'` is stated at `CategoryTheory.Limits.pullback.fst` of the cospan written the
other way round, so it would need the symmetry of the pullback on top of the transfer this file
already does in one rewrite. **Both routes spend the same two facts** — the limit at this cospan
and the invariance of the class under isomorphism — and neither spends anything else.

## Main results

- `ComplexAnalytic.AnalyticSpace.isStableUnderBaseChange_isFiniteEtale`: **finite étaleness is
  stable under base change**, as `CategoryTheory.MorphismProperty.IsStableUnderBaseChange` for
  `ComplexAnalytic.AnalyticSpace.isFiniteEtale`.

## What is not here

* **Nothing for `ComplexAnalytic.AnalyticSpace.IsFinite` and nothing for
  `ComplexAnalytic.AnalyticSpace.IsLocalIso`.** Neither is a `CategoryTheory.MorphismProperty` in
  this repository — `Oka/AnalyticSpace/FiniteEtaleOver.lean`'s docstring says so of the first —
  so the class cannot be stated for either, and the two halves of the base change that the proof
  of `ComplexAnalytic.AnalyticSpace.isFiniteEtale_baseChangeSnd` goes through are in
  `Oka/AnalyticSpace/FiniteEtaleBaseChange.lean` as plain theorems about the base map.
* **No base change in the category of covers.** `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver X`
  is a different category, its cospans are cospans of morphisms **of covers**, and a morphism of
  covers is not known to be finite étale without `[T2Space]` of its target. That is what
  `Oka/AnalyticSpace/FiniteEtaleOver.lean`'s bullet
  **No base change of the class over a cospan of morphisms of covers** is about, and this file
  does not narrow it. The same holds of
  `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver X`, whose fibre products
  `Oka/AnalyticSpace/SeparatedFiniteEtaleLimits.lean` builds.
* **No `CategoryTheory.MorphismProperty.IsStableUnderCobaseChange` and nothing about pushouts.**
  The dual class is not stated for anything in this repository and no pushout is constructed
  anywhere in it.
* **Nothing about the degree.** That the base change has the same number of sheets is
  `ComplexAnalytic.AnalyticSpace.degree_eq_card_fiber`'s subject and no declaration below bears on
  it; `Oka/AnalyticSpace/FiniteEtaleBaseChange.lean` records the same absence at its own
  statements.
* **No `CategoryTheory.Limits.HasPullbacks ComplexAnalytic.AnalyticSpace` is used or restated.**
  That class is a theorem of `Oka/AnalyticSpace/PullbackReduction.lean`, which is not in this
  file's import closure; the limit the proof below needs is the one
  `ComplexAnalytic.AnalyticSpace.hasPullback_of_isFiniteEtale` supplies at a cospan with a finite
  étale leg, and instance search finds that one.
-/

open CategoryTheory

universe u

namespace ComplexAnalytic.AnalyticSpace

/-- **Finite étaleness is stable under base change.** For every pullback square

```
Y' --f'--> Y
|          |
g'         g
v          v
X ---f---> S
```

in `ComplexAnalytic.AnalyticSpace` with `g` finite étale, `g'` is finite étale — with no
hypothesis on any of the four spaces and none on `f`.

**An `instance` and not a `theorem`, and that was measured.**
`#synth CategoryTheory.MorphismProperty.IsStableUnderBaseChange
ComplexAnalytic.AnalyticSpace.isFiniteEtale.{0}` **fails** at the commit this file is cut from,
both in a file importing `Oka.AnalyticSpace.FiniteEtaleOver` and in one importing the whole of
`Oka`; `OkaTest/FiniteEtaleBaseChangeNonHausdorff.lean` runs it as `inferInstance` at the head.
Mathlib consumes this class by instance search — `CategoryTheory.MorphismProperty.pullbacks_le`
and the instance giving
`CategoryTheory.MorphismProperty.IsStableUnderBaseChangeAlong` at every morphism both take it as
an instance argument — so a `theorem` would reach none of them.

The square is compared with `CategoryTheory.Limits.pullback` of the same cospan, which exists by
`ComplexAnalytic.AnalyticSpace.hasPullback_of_isFiniteEtale`; then
`ComplexAnalytic.AnalyticSpace.isFiniteEtale_pullback_snd_of_isFiniteEtale` is the property there
and it comes back along the comparison isomorphism. -/
instance isStableUnderBaseChange_isFiniteEtale :
    (isFiniteEtale.{u}).IsStableUnderBaseChange where
  of_isPullback {_ _ _ _ f g _ g'} sq hg := by
    haveI : IsFiniteEtale g := hg
    haveI := isFiniteEtale_pullback_snd_of_isFiniteEtale g f
    haveI := isFiniteEtale_of_isIso sq.isoPullback.hom
    change IsFiniteEtale g'
    rw [← sq.isoPullback_hom_snd]
    exact isFiniteEtale_comp _ _

end ComplexAnalytic.AnalyticSpace
