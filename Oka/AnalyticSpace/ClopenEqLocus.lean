/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.AnalyticSpace.SeparatedFiniteEtale
import Oka.Topology.SeparatedMap

/-!
# A local isomorphism is locally injective, and where two morphisms of covers agree is clopen

`Oka/AnalyticSpace/SeparatedFiniteEtale.lean` cuts the covers **separated** over the base out of
the covers, and the condition it adds is a statement about the underlying map: `IsSeparatedMap`
closes the locus where two lifts of it agree. This file supplies the other half
— `IsLocallyInjective`, which opens it — and puts the two together, so that for two morphisms of
that category into a common object the set where their underlying maps agree is **clopen** in the
source.

## Which half is new and which was already here

**The closing half is the category's defining condition and nothing below adds to it.**
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.isSeparatedMap_hom` is the second
component of an object's pair and is on `master`.

**The opening half is one line and it is Mathlib's**, which is the point of stating it here rather
than proving something: `ComplexAnalytic.AnalyticSpace.IsLocalIso` carries `IsLocalHomeomorph` as
its topological field, and `IsLocalHomeomorph.isLocallyInjective` is
`Mathlib/Topology/IsLocalHomeomorph.lean`'s. **The stalk field of
`ComplexAnalytic.AnalyticSpace.IsLocalIso` plays no part and cannot** — `IsLocallyInjective` is a
condition on the underlying map alone — which is the same reading
`Oka/AnalyticSpace/CoveringMap.lean` gives of its own rung and the reason this file is placed
beside that one in spirit: both take a topological field out of a class of morphisms and hand it
to a Mathlib theorem.

**The conjunction is `IsSeparatedMap.isClopen_eqLocus` of `Oka/Topology/SeparatedMap.lean`**, and
that statement's own docstring says what it adds over Mathlib: `IsSeparatedMap.isClosed_eqLocus`
and `IsLocallyInjective.isOpen_eqLocus` are both Mathlib's and their conjunction is formed inline
inside `IsSeparatedMap.eq_of_comp_eq` without being named.

## No hypothesis on the base, and that is a measurement

**Nothing below asks `[T2Space X]`**, and the `## Over a Hausdorff base` section of
`Oka/AnalyticSpace/SeparatedFiniteEtale.lean` is not entered: the two inputs at an object `A` are
`…SeparatedFiniteEtaleOver.isSeparatedMap_hom`, which carries no such hypothesis, and the
`ComplexAnalytic.AnalyticSpace.IsFiniteEtale` component of the same pair, which carries none
either. The `#synth` control in the pull request that adds this file was run with no `T2Space`
instance anywhere in scope.

## The asymmetry, which is in the target and not in a choice made here

The hypotheses are spent on the **target** `A` of the two morphisms and nothing whatever is asked
of their common source `B` beyond its being an object of the category. That is what the shape of
`IsSeparatedMap.isClopen_eqLocus` gives: the map being lifted along is `A`'s structure morphism,
and `B` contributes only the continuity of the two lifts, which a morphism of analytic spaces
carries with it. **`B` is not asked to be preconnected**, which is the hypothesis Mathlib's
`IsSeparatedMap.eq_of_comp_eq` spends to turn the same clopen set into an equality, and not
asking it is why the set is worth naming.

## Main results

- `ComplexAnalytic.AnalyticSpace.isLocallyInjective_base_of_isLocalIso`: **the underlying map of a
  local isomorphism is locally injective.**
- `ComplexAnalytic.AnalyticSpace.isClopen_eqLocus_base_of_isLocalIso`: **and where two morphisms
  into it agree is clopen**, when that local isomorphism's underlying map is also separated.
- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.isClopen_eqLocus`: **so where two
  morphisms of the category of separated covers agree is clopen**, with both hypotheses supplied
  by the target's own defining pair.
- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.isClopen_fixedLocus`: **and the fixed
  locus of an endomorphism of an object is clopen**, which is
  `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.isClopen_eqLocus` at the identity in the
  second slot.

## What is not here

* **No group, and no action.** A finite group acting on an object of this category by
  automorphisms over the base is a functor out of `CategoryTheory.SingleObj`, and `SingleObj`
  occurs in the comment-stripped code of no module of this repository at the commit that adds this
  file. `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.isClopen_fixedLocus` is the
  statement such an action would be read one element at a time through, and stating it is not
  stating the action.
* **No quotient, and nothing about `CategoryTheory.Limits.HasColimitsOfShape`.** No coequaliser and
  no pushout is stated for this category, for the covers, or for `ComplexAnalytic.AnalyticSpace`
  itself. Nothing below bears on that and no bullet anywhere may be rewritten as though it did.
  **This bullet opened *What a quotient by a finite action would need is a coequaliser*, until
  2026-09-15**, when `Oka/AnalyticSpace/QuotientColimit.lean` built that quotient as a colimit of
  shape `CategoryTheory.SingleObj G` out of the orbit space, citing no coequaliser and no finite
  colimit: what a quotient needs is the orbit space, and a coequaliser is what the **route through
  `CategoryTheory.Limits.HasFiniteColimits`** would have needed. The half of the sentence that is a
  measurement is unmoved and is re-run at the commit that retires the other half.
* **Nothing is concluded from the clopen set.** Over a preconnected source it would give that two
  morphisms agreeing at a point agree everywhere, which is Mathlib's
  `IsSeparatedMap.eq_of_comp_eq` and needs no line of this file; and even there what it would give
  is equality of the two **underlying maps**, not of the two morphisms of analytic spaces, since a
  morphism carries a map of structure sheaves that this says nothing about. **That gap is real and
  this file does not cross it.**
* **No converse and no sharpness.** That the locus is clopen for every pair of morphisms into `A`
  is not shown to imply either hypothesis on `A.hom`, and no object is exhibited at which dropping
  one of them leaves the conclusion false. `ComplexAnalytic.AnalyticSpace.doubledLineOver` is the
  standing witness that a cover of a Hausdorff base need not have a separated structure morphism,
  and it is **not** used below.
* **Nothing about the covers that are not separated.** `…FiniteEtaleOver` objects carry the
  local-isomorphism half and not the separated half, so the open half of the conclusion holds for
  them and the closed half does not follow; no statement below is made at that category, and the
  half that does hold there is `IsLocallyInjective.isOpen_eqLocus` read at the structure morphism,
  which is Mathlib's and is not restated.
-/

open CategoryTheory Topology

universe u

noncomputable section

namespace ComplexAnalytic.AnalyticSpace

/-- **The underlying map of a local isomorphism is locally injective.**

`IsLocalHomeomorph.isLocallyInjective` at the topological field of
`ComplexAnalytic.AnalyticSpace.IsLocalIso`, and that is the whole of it. **The stalk field is not
used and cannot be**: `IsLocallyInjective` is a condition on the underlying map alone, which is
the same observation `ComplexAnalytic.AnalyticSpace.isCoveringMap_base_of_isFiniteEtale` makes of
itself in `Oka/AnalyticSpace/CoveringMap.lean`.

**Nothing is asked of either space.** No separation axiom, no connectedness, and no finiteness —
in particular this is available at a morphism that is a local isomorphism without being finite
étale, which is why it is stated at `ComplexAnalytic.AnalyticSpace.IsLocalIso` and not at
`ComplexAnalytic.AnalyticSpace.IsFiniteEtale`. -/
theorem isLocallyInjective_base_of_isLocalIso {X Y : AnalyticSpace.{u}} (f : X ⟶ Y)
    [IsLocalIso f] : IsLocallyInjective (f.toLRSHom.base : X → Y) :=
  (IsLocalIso.isLocalHomeomorph (f := f)).isLocallyInjective

/-- **Where two morphisms into a separated local isomorphism agree is clopen.**

`IsSeparatedMap.isClopen_eqLocus` of `Oka/Topology/SeparatedMap.lean` at
`ComplexAnalytic.AnalyticSpace.isLocallyInjective_base_of_isLocalIso` and the given separatedness;
the two continuity hypotheses are carried by the morphisms, whose base maps are `TopCat`
morphisms, and the equation between the two composites is `congrArg` at `he`.

**The hypotheses are on `p` and nothing is asked of `F`.** In particular `F` is not asked to be
preconnected — Mathlib's `IsSeparatedMap.eq_of_comp_eq` is what spends that and concludes an
equality instead of producing a set — and neither space is asked for a separation axiom.

**Separatedness is a hypothesis here rather than an instance** because
`ComplexAnalytic.AnalyticSpace.isSeparatedMap` is a
`CategoryTheory.MorphismProperty` and not a class, so nothing can synthesise it; the caller below
reads it off an object's defining pair. -/
theorem isClopen_eqLocus_base_of_isLocalIso {E F Y : AnalyticSpace.{u}} (p : E ⟶ Y) [IsLocalIso p]
    (hsep : IsSeparatedMap (p.toLRSHom.base : E → Y)) {g₁ g₂ : F ⟶ E} (he : g₁ ≫ p = g₂ ≫ p) :
    IsClopen {x : (F : Type u) | g₁.toLRSHom.base x = g₂.toLRSHom.base x} :=
  IsSeparatedMap.isClopen_eqLocus hsep (isLocallyInjective_base_of_isLocalIso p)
    g₁.toLRSHom.base.hom.continuous g₂.toLRSHom.base.hom.continuous
    (congrArg (fun m ↦ ⇑(AnalyticSpace.Hom.toLRSHom m).base) he)

variable {X : AnalyticSpace.{u}}

/-- **Where two morphisms of the category of separated covers agree is clopen**, with no
hypothesis on the base.

`ComplexAnalytic.AnalyticSpace.isClopen_eqLocus_base_of_isLocalIso` at the target's structure
morphism. **Both of its hypotheses come out of the one pair the target carries**: the local
isomorphism is the `ComplexAnalytic.AnalyticSpace.IsFiniteEtale` component read through
`ComplexAnalytic.AnalyticSpace.IsFiniteEtale.isLocalIso`, and the separatedness is the second
component, `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.isSeparatedMap_hom`. That is
the whole reason this statement is at **this** category and not at the covers.

The equation between the two composites is the two triangles over `X`, each
`CategoryTheory.MorphismProperty.Over.w`, read against each other — `A.hom` is what both compose
to and neither triangle is spent on anything else. -/
theorem SeparatedFiniteEtaleOver.isClopen_eqLocus {A B : SeparatedFiniteEtaleOver.{u} X}
    (g₁ g₂ : B ⟶ A) :
    IsClopen {b : (B.left : Type u) | g₁.left.toLRSHom.base b = g₂.left.toLRSHom.base b} := by
  haveI : IsFiniteEtale A.hom := A.isFiniteEtale_hom
  exact isClopen_eqLocus_base_of_isLocalIso A.hom A.isSeparatedMap_hom
    ((MorphismProperty.Over.w g₁).trans (MorphismProperty.Over.w g₂).symm)

/-- **And the fixed locus of an endomorphism of an object is clopen**, with no hypothesis on the
base.

`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.isClopen_eqLocus` with the identity in the
second slot, and no massaging: the underlying map of `𝟙 A` is the identity of `A.left` by
definitional unfolding, so the set this states is the one that statement produces and the
application is the whole proof.

**This is the form a finite group acting on `A` by automorphisms over the base would be read
through**, one element at a time, and stating it is not stating such an action — `## What is not
here` says so in terms. An automorphism is not asked for: the statement is about any endomorphism
of the object, and `CategoryTheory.Iso` does not occur in its statement. -/
theorem SeparatedFiniteEtaleOver.isClopen_fixedLocus {A : SeparatedFiniteEtaleOver.{u} X}
    (g : A ⟶ A) : IsClopen {a : (A.left : Type u) | g.left.toLRSHom.base a = a} :=
  SeparatedFiniteEtaleOver.isClopen_eqLocus g (𝟙 A)

end ComplexAnalytic.AnalyticSpace
