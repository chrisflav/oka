/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.AnalyticSpace.QuotientCover
import Mathlib.CategoryTheory.SingleObj

/-!
# The quotient of a cover by a finite group is the colimit of the action

`Oka/AnalyticSpace/QuotientCover.lean` builds the quotient of a cover by a finite group acting on
its total space over the base, as an object of
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver` together with the quotient map, and its
`## What is not here` says that **no colimit of any shape** is stated there, that nothing there
says an invariant morphism out of the cover factors through the quotient, and that **no bridge**
carries a group acting by automorphisms of the cover to the action taken there. This file is those
two things: the universal property of that quotient, and the bridge — and their composite is
`CategoryTheory.Limits.HasColimitsOfShape (CategoryTheory.SingleObj G)` for the category of covers
separated over a Hausdorff base.

## What the obligation is, read at the pinned Mathlib

`Mathlib/CategoryTheory/Galois/Basic.lean` at the revision `lake-manifest.json` pins asks a
`PreGaloisCategory` for five things, the fourth of which is

```lean
  /-- `C` has quotients by finite groups (G2). -/
  hasQuotientsByFiniteGroups (G : Type u₂) [Group G] [Finite G] :
    HasColimitsOfShape (SingleObj G) C := by infer_instance
```

where `u₂` is the **hom universe** of `C`. That namespace is **not in this repository's import
closure** and so cannot be cited by name here, which is the spelling
`Oka/AnalyticSpace/SeparatedFiberFunctor.lean` and `Oka/AnalyticSpace/QuotientCover.lean` already
use for it, and the reason no instance of either of that file's two classes is declared anywhere
below. **The instance below asks nothing of the universe of `G`**, so it covers that field's `u₂`
whatever the hom universe of this category turns out to be, and asks `[Finite G]` rather than
`[Fintype G]`.

## Why the mirror-tree module does not answer this

`Oka/CategoryTheory/Limits/Shapes/SingleObj.lean` says that a category with **finite colimits** has
colimits of this shape for every finite group at every universe, and that is not a route here:
`#synth CategoryTheory.Limits.HasFiniteColimits (…SeparatedFiniteEtaleOver X)` **fails** at the
commit that adds this file, while `HasTerminal`, `HasPullbacks` and `HasFiniteCoproducts` are all
found — all four probes run rather than read off declarations. What that category is missing for
finite colimits is coequalisers, and **this file does not supply them**: the colimit below is
constructed at this one shape, out of the orbit space, and nothing here says that two morphisms of
covers have a coequaliser. **So the mirror-tree module is neither imported nor cited by any
declaration below**, which is one line of this file and one scan: the two `import` lines at its head
name `Oka/AnalyticSpace/QuotientCover.lean` and `Mathlib/CategoryTheory/SingleObj.lean`, and
`CategoryTheory.Limits.hasColimitsOfShape_singleObj` occurs in the comment-stripped code of no
module under `Oka/` at the commit that adds this file — `scripts/import_cost.py`'s `strip_comments`
the instrument, the one occurrence in the tree being the `#print axioms` line that guards it. The
two statements stand side by side answering the same question for different categories.

## The universal property is proved at the covering space and not at the category

The two halves of the argument live at different levels, and the reason is where the extensionality
comes from. `ComplexAnalytic.AnalyticSpace.quotientCover` is a
`ComplexAnalytic.AnalyticSpace.coveringSpace`, so
`ComplexAnalytic.AnalyticSpace.coveringSpace_hom_ext` — two morphisms **into** a covering space
which agree on underlying maps and over the base are equal — is available for morphisms into it,
and `ComplexAnalytic.AnalyticSpace.coveringSpaceMap` builds morphisms into one out of a continuous
map over the base. **Morphisms out of the quotient are the ones this file has to build**, and the
target of such a morphism is an arbitrary cover rather than a covering space on the nose; the
bridge is `ComplexAnalytic.AnalyticSpace.toCoveringSpace` at the target's own structure map, which
`ComplexAnalytic.AnalyticSpace.isIso_toCoveringSpace` makes an isomorphism. That is why every
statement below asks `[ComplexAnalytic.AnalyticSpace.IsLocalIso]` of the target's structure map and
nothing else of the target, and why the category-level statements pass their instances positionally
with `@`: the comma category spells the source of `A.hom` as `(𝟭 _).obj A.left`, which is not
reducibly `A.left`, and `Oka/AnalyticSpace/QuotientCover.lean` records the same seam at the same
two declarations.

## The bridge is a monoid homomorphism read at underlying maps

A functor `F : CategoryTheory.SingleObj G ⥤ …SeparatedFiniteEtaleOver X` is a group acting on one
object of that category by automorphisms. Its object is `F.obj (CategoryTheory.SingleObj.star G)`,
and `g • y := (F.map g).left.toLRSHom.base y` is the action on points: `one_smul` is `F.map_id`,
`mul_smul` is `F.map_comp` with `CategoryTheory.SingleObj`'s composition being `flip (*)`,
continuity is that each `F.map g` has a continuous underlying map because it is one, and the
hypothesis that the action is over the base is `CategoryTheory.MorphismProperty.Over.w` of
`F.map g` read at a point. **All three of `Oka/AnalyticSpace/QuotientCover.lean`'s hypotheses come
from the functor and none of them is assumed here.**

## Main definitions

- `ComplexAnalytic.AnalyticSpace.orbitLift`: the descent of an **invariant** morphism to the orbit
  space, as a morphism of `TopCat`.
- `ComplexAnalytic.AnalyticSpace.quotientCoverDesc`: **the morphism out of the quotient that an
  invariant morphism into a cover factors through**, as a morphism of analytic spaces.
- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.quotientDesc`: the same read at an object
  of the category of separated covers.
- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.singleObjAut` and
  `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.singleObjSMul`: **the bridge** — the
  endomorphism a group element names under a functor out of `CategoryTheory.SingleObj G`, and the
  action on points it gives.
- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.singleObjQuotient`,
  `…singleObjToQuotient` and `…singleObjCocone`: the quotient by that action, the quotient map, and
  the cocone under the functor they are.

## Main results

- `ComplexAnalytic.AnalyticSpace.toQuotientCover_comp_desc` and
  `ComplexAnalytic.AnalyticSpace.quotientCover_hom_ext`: **the factorisation and its uniqueness**,
  at the covering space.
- `ComplexAnalytic.AnalyticSpace.comp_toQuotientCover_eq`: **the quotient map coequalises the
  action** — any endomorphism over the base moving each point inside its own orbit is absorbed by
  it.
- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.singleObjIsColimit`: **the quotient
  cocone is a colimit.**
- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.hasColimitsOfShape_singleObj`: **the
  category of covers separated over a Hausdorff base has colimits of shape
  `CategoryTheory.SingleObj G` for every finite group `G`, at every universe** — which is the
  fourth `PreGaloisCategory` field, stated without the class.

## What is not here

* **No `PreGaloisCategory` instance and no `FiberFunctor` instance.** This is one field of one of
  those two classes and not the class; that namespace is not in this repository's import closure,
  and `PreGaloisCategory` occurs in the comment-stripped code of **no** module of this repository
  at the commit that adds this file. **With this file every one of that class's five fields has a
  statement on `master`**, and the two halves of that are different: four are classes and are found
  by instance search at this category — `HasTerminal`, `HasPullbacks`, `HasFiniteCoproducts` and
  the one below, all four `#synth` runs of mine — while the fifth is not a class at all and is the
  theorem
  `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.inducesIsoOnDirectSummand_of_mono'`,
  whose statement is the field's shape at `[T2Space X]`. **Assembling the five is not done below**,
  and it cannot be done by name while that namespace is out of the closure.
* **Nothing about preservation of this colimit by either fibre functor**, which is the fifth
  `FiberFunctor` field and a different statement: a colimit in the covers and a colimit of finite
  sets are two things, and no declaration below compares them.
* **No coequalisers and no finite colimits.** The colimit below is at one shape and is built by
  hand; nothing here says that this category has `CategoryTheory.Limits.HasFiniteColimits`, and the
  probe at the head says it does not.
* **Nothing about the action beyond its being over the base.** Freeness, fixed points, stabilisers
  and the degree of the quotient are all absent here exactly as they are in
  `Oka/AnalyticSpace/QuotientCover.lean`, and nothing below is a statement about orbits as sets.
* **Not stated at `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver`.** The category-level
  declarations are at the separated covers and at no other category; the general-purpose section
  asks for no category at all, and a caller at a different one should use that form.
* **Nothing about the quotient map as a morphism in a class** — not an epimorphism, not finite
  étale, not a local isomorphism. It is a colimit cocone leg below and nothing more, which is the
  same absence `Oka/AnalyticSpace/QuotientCover.lean` records for it.
-/

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry TopCat Topology

universe u

noncomputable section

namespace ComplexAnalytic.AnalyticSpace

section Orbits

variable {X Y : AnalyticSpace.{u}} (f : Y ⟶ X)
variable {G : Type*} [Group G] [MulAction G ↥Y] [ContinuousConstSMul G ↥Y]
variable (hover : ∀ (g : G) (y : ↥Y), f.toLRSHom.base (g • y) = f.toLRSHom.base y)
variable {Z : AnalyticSpace.{u}} (q : Z ⟶ X) [hq : IsLocalIso q]
variable (u : Y ⟶ Z)
  (hinv : ∀ (g : G) (y : ↥Y), u.toLRSHom.base (g • y) = u.toLRSHom.base y)

/-- **The descent of an invariant morphism to the orbit space.**

`Quotient.lift` of its base map at the constancy on orbits that the hypothesis `hinv` is, with
`continuous_quot_lift` for continuity — the same construction
`ComplexAnalytic.AnalyticSpace.orbitDesc` is, at a morphism into an arbitrary target rather than
at the structure map. **Neither the target nor the morphism is asked for anything here**: no
separation axiom, no finiteness, no class on `u`, and the group is not asked to be finite. -/
def orbitLift : orbitSpace (Y := Y) G ⟶ Z.toLocallyRingedSpace.toTopCat :=
  TopCat.ofHom ⟨Quotient.lift ⇑u.toLRSHom.base (by
      rintro a b ⟨g, rfl⟩
      exact hinv g b),
    continuous_quot_lift _ u.toLRSHom.base.hom.continuous⟩

omit [ContinuousConstSMul G ↥Y] hq in
/-- **Its defining equation**, as an equation of `TopCat` morphisms, and it is `rfl`: composing the
descent with the quotient map returns the morphism it was built from. -/
theorem orbitMk_comp_orbitLift : orbitMk (Y := Y) G ≫ orbitLift u hinv = u.toLRSHom.base := rfl

omit [ContinuousConstSMul G ↥Y] hq in
/-- **The two descents commute with the target's structure map**, which is the triangle over `X`
that `ComplexAnalytic.AnalyticSpace.coveringSpaceMap` asks for below.

`ComplexAnalytic.AnalyticSpace.orbitMk` is surjective, so it is enough to check the two sides at a
point of `Y`, where both are the hypothesis `hu` read at that point. **This is the only place `hu`
is spent** and it is spent as an equation of morphisms of analytic spaces and not of maps. -/
theorem orbitDesc_eq_orbitLift_comp (hu : u ≫ q = f) :
    orbitDesc f hover = orbitLift u hinv ≫ q.toLRSHom.base := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  rintro ⟨y⟩
  change f.toLRSHom.base y = q.toLRSHom.base (u.toLRSHom.base y)
  rw [← hu]
  rfl

variable [Finite G] [T2Space Y] [IsFiniteEtale f] (hu : u ≫ q = f)

/-- **The morphism out of the quotient that an invariant morphism over the base factors through.**

`ComplexAnalytic.AnalyticSpace.coveringSpaceMap` carries
`ComplexAnalytic.AnalyticSpace.orbitLift` across the triangle above into a morphism into the
covering space built on the target's own base map, and
`ComplexAnalytic.AnalyticSpace.toCoveringSpace` identifies the target with that covering space —
an isomorphism by `ComplexAnalytic.AnalyticSpace.isIso_toCoveringSpace`, which is where
`[ComplexAnalytic.AnalyticSpace.IsLocalIso]` of the target's structure map is spent and the only
place. **Nothing is glued and no sheaf map is written down**: both structures are `X`'s pulled
back, exactly as in `ComplexAnalytic.AnalyticSpace.toQuotientCover`. -/
def quotientCoverDesc : quotientCover f hover ⟶ Z :=
  coveringSpaceMap X q.toLRSHom.base hq.isLocalHomeomorph (orbitDesc f hover)
      (isCoveringMap_orbitDesc f hover).isLocalHomeomorph (orbitLift u hinv)
      (orbitDesc_eq_orbitLift_comp f hover q u hinv hu) ≫ inv (toCoveringSpace q)

/-- **Its defining equation**, published as a theorem for a caller: it is the shape a consumer of
`ComplexAnalytic.AnalyticSpace.quotientCoverDesc` rewrites with, and **no proof of this file uses
it** — the two below spell the `ComplexAnalytic.AnalyticSpace.coveringSpaceMap` term out instead,
which is a `git grep` of this name and not a reading.

**The reason it exists at all is what a `rw` naming the definition would cost.** Such a `rw` asks
Lean to generate that definition's equation lemma, which then stands in
`scripts/DumpOkaDecls.lean`'s output as a row this file did not write — measured and not expected:
the first green draft of this file held **twenty-five** declarations, this one not among them, and
anchored **twenty-eight** rows, `ComplexAnalytic.AnalyticSpace.quotientCoverDesc.eq_1` from that
`rw` and two congruence lemmas from a `congr 1` beside it. The cure for the first was this theorem;
the two proofs were then written without any rewrite at all, which is why nothing below cites it.
`Oka/AnalyticSpace/DirectSummand.lean` makes the same measured choice
twice and `Oka/Analytification/CrossMemberDatumGlue.lean` states it as a rule. -/
theorem quotientCoverDesc_eq :
    quotientCoverDesc f hover q u hinv hu
      = coveringSpaceMap X q.toLRSHom.base hq.isLocalHomeomorph (orbitDesc f hover)
          (isCoveringMap_orbitDesc f hover).isLocalHomeomorph (orbitLift u hinv)
          (orbitDesc_eq_orbitLift_comp f hover q u hinv hu) ≫ inv (toCoveringSpace q) :=
  rfl

/-- **It is a morphism over `X`.**

The triangle of `ComplexAnalytic.AnalyticSpace.coveringSpaceMap` composed with the inverse of
`ComplexAnalytic.AnalyticSpace.toCoveringSpace`'s, the second read through
`CategoryTheory.IsIso.inv_comp_eq`. -/
theorem quotientCoverDesc_comp :
    quotientCoverDesc f hover q u hinv hu ≫ q = quotientCoverHom f hover :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun k ↦ coveringSpaceMap X q.toLRSHom.base hq.isLocalHomeomorph (orbitDesc f hover)
      (isCoveringMap_orbitDesc f hover).isLocalHomeomorph (orbitLift u hinv)
      (orbitDesc_eq_orbitLift_comp f hover q u hinv hu) ≫ k)
        ((IsIso.inv_comp_eq _).2 (toCoveringSpace_comp q).symm)).trans
      (coveringSpaceMap_comp X q.toLRSHom.base hq.isLocalHomeomorph (orbitDesc f hover)
        (isCoveringMap_orbitDesc f hover).isLocalHomeomorph (orbitLift u hinv)
        (orbitDesc_eq_orbitLift_comp f hover q u hinv hu)))

/-- **And the invariant morphism factors through the quotient map by it.**

Both sides are morphisms into the target, which is not a covering space on the nose, so the two are
compared after composing with the isomorphism
`ComplexAnalytic.AnalyticSpace.toCoveringSpace` — a monomorphism because it is an isomorphism —
and `ComplexAnalytic.AnalyticSpace.coveringSpace_hom_ext` then asks for the two underlying maps and
the two triangles over `X`. The first is
`ComplexAnalytic.AnalyticSpace.orbitMk_comp_orbitLift`, which is `rfl`, and the second is the two
triangles already proved. -/
theorem toQuotientCover_comp_desc :
    toQuotientCover f hover ≫ quotientCoverDesc f hover q u hinv hu = u := by
  set cm := coveringSpaceMap X q.toLRSHom.base hq.isLocalHomeomorph (orbitDesc f hover)
    (isCoveringMap_orbitDesc f hover).isLocalHomeomorph (orbitLift u hinv)
    (orbitDesc_eq_orbitLift_comp f hover q u hinv hu) with hcm
  have hdesc : quotientCoverDesc f hover q u hinv hu ≫ toCoveringSpace q = cm :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun k ↦ cm ≫ k) (IsIso.inv_hom_id (toCoveringSpace q))).trans
        (Category.comp_id _))
  refine (cancel_mono (toCoveringSpace q)).1 (((Category.assoc _ _ _).trans
    (congrArg (fun k ↦ toQuotientCover f hover ≫ k) hdesc)).trans ?_)
  refine coveringSpace_hom_ext X q.toLRSHom.base hq.isLocalHomeomorph ?_ ?_
  · change (toQuotientCover f hover).toLRSHom.base ≫ _ = u.toLRSHom.base ≫ _
    rw [base_toQuotientCover, base_coveringSpaceMap, base_toCoveringSpace]
    exact (orbitMk_comp_orbitLift u hinv).trans (Category.comp_id _).symm
  · simp only [Category.assoc, toCoveringSpace_comp, hu]
    exact (congrArg (fun m ↦ toQuotientCover f hover ≫ m)
      (coveringSpaceMap_comp X q.toLRSHom.base hq.isLocalHomeomorph (orbitDesc f hover)
        (isCoveringMap_orbitDesc f hover).isLocalHomeomorph (orbitLift u hinv)
        (orbitDesc_eq_orbitLift_comp f hover q u hinv hu))).trans (toQuotientCover_comp f hover)

/-- **Two morphisms out of the quotient agreeing after the quotient map and over `X` are equal.**

The quotient map is an epimorphism of `TopCat` on underlying maps, because `Quotient.mk` is
surjective and `TopCat.epi_iff_surjective` is that criterion; that gives the two underlying maps
equal, and the second hypothesis gives the two triangles, so
`ComplexAnalytic.AnalyticSpace.coveringSpace_hom_ext` applies after composing with the isomorphism
onto the covering space as above.

**Both hypotheses are needed and neither implies the other.** Agreeing after a morphism whose base
map is surjective settles the underlying maps and says nothing about the sheaf maps, which is what
the statement this is read from is about; and the base map of a morphism of covers does not
determine it, which is the same reading
`ComplexAnalytic.AnalyticSpace.coveringSpace_hom_ext`'s own docstring records. -/
theorem quotientCover_hom_ext {v w : quotientCover f hover ⟶ Z}
    (hbase : toQuotientCover f hover ≫ v = toQuotientCover f hover ≫ w)
    (hcomm : v ≫ q = w ≫ q) : v = w := by
  rw [← cancel_mono (toCoveringSpace q)]
  refine coveringSpace_hom_ext X q.toLRSHom.base hq.isLocalHomeomorph ?_ ?_
  · change v.toLRSHom.base ≫ _ = w.toLRSHom.base ≫ _
    rw [base_toCoveringSpace]
    haveI : Epi (orbitMk (Y := Y) G) := (TopCat.epi_iff_surjective _).2 Quotient.mk_surjective
    have key : ∀ m : quotientCover f hover ⟶ Z,
        orbitMk (Y := Y) G ≫ m.toLRSHom.base = (toQuotientCover f hover ≫ m).toLRSHom.base := by
      intro m
      conv_rhs => rw [show (toQuotientCover f hover ≫ m).toLRSHom
        = (toQuotientCover f hover).toLRSHom ≫ m.toLRSHom from rfl]
      rw [LocallyRingedSpace.comp_base, base_toQuotientCover]
      rfl
    have hid : ∀ m : quotientCover f hover ⟶ Z,
        orbitMk (Y := Y) G ≫ m.toLRSHom.base ≫ 𝟙 Z.toLocallyRingedSpace.toTopCat
          = (toQuotientCover f hover ≫ m).toLRSHom.base :=
      fun m ↦ (congrArg (fun k ↦ orbitMk (Y := Y) G ≫ k) (Category.comp_id _)).trans (key m)
    exact (cancel_epi (orbitMk (Y := Y) G)).1
      ((hid v).trans ((congrArg (fun m ↦ m.toLRSHom.base) hbase).trans (hid w).symm))
  · simp only [Category.assoc, toCoveringSpace_comp]
    exact hcomm

/-- **The quotient map absorbs any endomorphism over the base that moves each point inside its own
orbit.**

This is the naturality of the cocone below, stated without a cocone and without a group acting by
automorphisms: the hypothesis is one point at a time, and a morphism of covers commuting with the
structure maps is all that is asked. The two underlying maps agree because `Quotient.sound` at the
orbit relation is exactly the hypothesis, and the two triangles are
`ComplexAnalytic.AnalyticSpace.toQuotientCover_comp` on both sides. -/
theorem comp_toQuotientCover_eq (m : Y ⟶ Y) (hm : m ≫ f = f)
    (horb : ∀ y : ↥Y, ∃ g : G, m.toLRSHom.base y = g • y) :
    m ≫ toQuotientCover f hover = toQuotientCover f hover := by
  refine coveringSpace_hom_ext X (orbitDesc f hover)
    (isCoveringMap_orbitDesc f hover).isLocalHomeomorph ?_ ?_
  · change (m ≫ toQuotientCover f hover).toLRSHom.base = _
    rw [show (m ≫ toQuotientCover f hover).toLRSHom
      = m.toLRSHom ≫ (toQuotientCover f hover).toLRSHom from rfl,
      LocallyRingedSpace.comp_base, base_toQuotientCover]
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro y
    obtain ⟨g, hg⟩ := horb y
    change Quotient.mk (MulAction.orbitRel G ↥Y) (m.toLRSHom.base y) = Quotient.mk _ y
    rw [hg]
    exact Quotient.sound ⟨g, rfl⟩
  · exact (Category.assoc m _ _).trans
      ((congrArg (fun k ↦ m ≫ k) (toQuotientCover_comp f hover)).trans
        (hm.trans (toQuotientCover_comp f hover).symm))

end Orbits

section Category

variable {X : AnalyticSpace.{u}} [T2Space (X : Type u)] {A B : SeparatedFiniteEtaleOver.{u} X}
variable {G : Type*} [Group G] [Finite G] [MulAction G ↥A.left] [ContinuousConstSMul G ↥A.left]
variable (hover : ∀ (g : G) (y : ↥A.left), A.hom.toLRSHom.base (g • y) = A.hom.toLRSHom.base y)
variable (u : A ⟶ B)
  (hinv : ∀ (g : G) (y : ↥A.left), u.left.toLRSHom.base (g • y) = u.left.toLRSHom.base y)

/-- **An invariant morphism of separated covers factors through the quotient**, and the factor is a
morphism of the category.

`ComplexAnalytic.AnalyticSpace.quotientCoverDesc` at the underlying morphism, with its triangle
over `X` for the second field of
`CategoryTheory.MorphismProperty.Over.homMk`. Both hypotheses of the section above are discharged
here rather than asked for, exactly as in
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.quotient`: the total space of the source is
Hausdorff by `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.t2Space_left`, and the target's
structure map is a local isomorphism because the object says it is finite étale.

**The instances are passed positionally with `@` and that is not decoration**, for the seam
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.quotient` records: the object of this comma
category spells its total space as `(𝟭 _).obj A.left`, which no `haveI` at the spelling
`A.left ⟶ X` is found at. -/
def SeparatedFiniteEtaleOver.quotientDesc : A.quotient hover ⟶ B :=
  MorphismProperty.Over.homMk
    (@quotientCoverDesc X A.left A.hom G _ _ _ hover B.left B.hom
      (@IsFiniteEtale.isLocalIso _ _ B.hom B.isFiniteEtale_hom) u.left hinv _ _
      A.isFiniteEtale_hom (MorphismProperty.Over.w u))
    (@quotientCoverDesc_comp X A.left A.hom G _ _ _ hover B.left B.hom
      (@IsFiniteEtale.isLocalIso _ _ B.hom B.isFiniteEtale_hom) u.left hinv _ _
      A.isFiniteEtale_hom (MorphismProperty.Over.w u))

/-- **The factorisation**, in the category.

`ComplexAnalytic.AnalyticSpace.toQuotientCover_comp_desc` under
`CategoryTheory.MorphismProperty.Over.Hom.ext`, which is the statement that a morphism of this
category is its underlying morphism: the right component is a morphism of the punctual category and
carries nothing. -/
theorem SeparatedFiniteEtaleOver.toQuotient_comp_quotientDesc :
    A.toQuotient hover ≫ SeparatedFiniteEtaleOver.quotientDesc hover u hinv = u := by
  apply MorphismProperty.Over.Hom.ext
  change (A.toQuotient hover).left ≫ (SeparatedFiniteEtaleOver.quotientDesc hover u hinv).left
    = u.left
  exact @toQuotientCover_comp_desc X A.left A.hom G _ _ _ hover B.left B.hom
    (@IsFiniteEtale.isLocalIso _ _ B.hom B.isFiniteEtale_hom) u.left hinv _ _
    A.isFiniteEtale_hom (MorphismProperty.Over.w u)

/-- **And its uniqueness**, which in the category needs only the factorisation and not the triangle.

`ComplexAnalytic.AnalyticSpace.quotientCover_hom_ext` asks for the two triangles over `X` as well
as for the agreement after the quotient map; here both morphisms are morphisms of this category, so
both triangles are `CategoryTheory.MorphismProperty.Over.w` and neither is a hypothesis. **That is
the whole of what the category buys over the covering space**, and it is why the colimit below
needs no second argument. -/
theorem SeparatedFiniteEtaleOver.quotient_hom_ext {v w : A.quotient hover ⟶ B}
    (h : A.toQuotient hover ≫ v = A.toQuotient hover ≫ w) : v = w := by
  apply MorphismProperty.Over.Hom.ext
  refine @quotientCover_hom_ext X A.left A.hom G _ _ _ hover B.left B.hom
    (@IsFiniteEtale.isLocalIso _ _ B.hom B.isFiniteEtale_hom) _ _ A.isFiniteEtale_hom v.left w.left
    ?_ ?_
  · change (A.toQuotient hover).left ≫ v.left = (A.toQuotient hover).left ≫ w.left
    exact congrArg (fun m ↦ m.left) h
  · exact (MorphismProperty.Over.w v).trans (MorphismProperty.Over.w w).symm

/-- **The quotient map absorbs an endomorphism of the cover moving each point inside its orbit**,
in the category.

`ComplexAnalytic.AnalyticSpace.comp_toQuotientCover_eq` at the underlying morphism, whose triangle
over `X` is `CategoryTheory.MorphismProperty.Over.w` and so is not a hypothesis here either. -/
theorem SeparatedFiniteEtaleOver.comp_toQuotient (m : A ⟶ A)
    (horb : ∀ y : ↥A.left, ∃ g : G, m.left.toLRSHom.base y = g • y) :
    m ≫ A.toQuotient hover = A.toQuotient hover := by
  apply MorphismProperty.Over.Hom.ext
  change m.left ≫ (A.toQuotient hover).left = (A.toQuotient hover).left
  exact @comp_toQuotientCover_eq X A.left A.hom G _ _ _ hover _ _ A.isFiniteEtale_hom m.left
    (MorphismProperty.Over.w m) horb

end Category

section SingleObj

variable {X : AnalyticSpace.{u}} [T2Space (X : Type u)]
variable {G : Type*} [Group G] (F : SingleObj G ⥤ SeparatedFiniteEtaleOver.{u} X)

/-- **The endomorphism of the object that a group element names.**

A functor out of `CategoryTheory.SingleObj G` has one object in its image and its action on
morphisms is a map `G → End`, which this names. It is an isomorphism, `G` being a group and
`CategoryTheory.SingleObj G` therefore a groupoid, and **nothing below uses that**: the two laws
and the three hypotheses the quotient asks for are all statements about the underlying maps. -/
def SeparatedFiniteEtaleOver.singleObjAut (g : G) :
    F.obj (SingleObj.star G) ⟶ F.obj (SingleObj.star G) :=
  F.map (X := SingleObj.star G) (Y := SingleObj.star G) g

omit [T2Space (X : Type u)] in
/-- **The unit acts as the identity**, which is `CategoryTheory.Functor.map_id` and the fact that
the identity of the single object is `1`. -/
theorem SeparatedFiniteEtaleOver.singleObjAut_one :
    SeparatedFiniteEtaleOver.singleObjAut F 1 = 𝟙 _ :=
  F.map_id (SingleObj.star G)

omit [T2Space (X : Type u)] in
/-- **And a product acts as the composite, in the other order.**

`CategoryTheory.Functor.map_comp`, with `CategoryTheory.SingleObj`'s composition being `flip (*)`
— `f ≫ g = g * f` — which is exactly what makes the action below a left action rather than a right
one. -/
theorem SeparatedFiniteEtaleOver.singleObjAut_mul (g₁ g₂ : G) :
    SeparatedFiniteEtaleOver.singleObjAut F (g₁ * g₂)
      = SeparatedFiniteEtaleOver.singleObjAut F g₂ ≫ SeparatedFiniteEtaleOver.singleObjAut F g₁ :=
  F.map_comp (X := SingleObj.star G) (Y := SingleObj.star G) (Z := SingleObj.star G) g₂ g₁

/-- **The action of `G` on the total space**, which is the first of the three hypotheses
`Oka/AnalyticSpace/QuotientCover.lean` asks of a group acting on a cover.

The two laws are the two statements above read at a point. **Reducible because it is a definition
of class type that a caller has to put into instance search by hand** — it depends on `F` and so
cannot be a global instance, and every declaration below introduces it with `letI`. -/
@[reducible] def SeparatedFiniteEtaleOver.singleObjSMul :
    MulAction G ↥(F.obj (SingleObj.star G)).left where
  smul g y := (SeparatedFiniteEtaleOver.singleObjAut F g).left.toLRSHom.base y
  one_smul y := by
    change ((SeparatedFiniteEtaleOver.singleObjAut F 1).left.toLRSHom.base) y = y
    rw [SeparatedFiniteEtaleOver.singleObjAut_one]
    rfl
  mul_smul g₁ g₂ y := by
    change ((SeparatedFiniteEtaleOver.singleObjAut F (g₁ * g₂)).left.toLRSHom.base) y
      = (SeparatedFiniteEtaleOver.singleObjAut F g₁).left.toLRSHom.base
        ((SeparatedFiniteEtaleOver.singleObjAut F g₂).left.toLRSHom.base y)
    rw [SeparatedFiniteEtaleOver.singleObjAut_mul]
    rfl

omit [T2Space (X : Type u)] in
/-- **Each group element acts continuously**, which is the second hypothesis and is the continuity
of a morphism of `TopCat` — no property of the action and no hypothesis on `G`. -/
theorem SeparatedFiniteEtaleOver.continuous_singleObjAut_base (g : G) :
    Continuous ⇑(SeparatedFiniteEtaleOver.singleObjAut F g).left.toLRSHom.base :=
  (SeparatedFiniteEtaleOver.singleObjAut F g).left.toLRSHom.base.hom.continuous

omit [T2Space (X : Type u)] in
/-- **And the action is over the base**, which is the third hypothesis and is
`CategoryTheory.MorphismProperty.Over.w` of the endomorphism read at a point. -/
theorem SeparatedFiniteEtaleOver.singleObjAut_base_over (g : G)
    (y : ↥(F.obj (SingleObj.star G)).left) :
    (F.obj (SingleObj.star G)).hom.toLRSHom.base
        ((SeparatedFiniteEtaleOver.singleObjAut F g).left.toLRSHom.base y)
      = (F.obj (SingleObj.star G)).hom.toLRSHom.base y :=
  congrArg (fun m ↦ (ConcreteCategory.hom m.toLRSHom.base) y)
    (MorphismProperty.Over.w (SeparatedFiniteEtaleOver.singleObjAut F g))

end SingleObj

section Colimit

variable {X : AnalyticSpace.{u}} [T2Space (X : Type u)]
variable {G : Type*} [Group G] [Finite G] (F : SingleObj G ⥤ SeparatedFiniteEtaleOver.{u} X)

/-- **The quotient of the object by the action the functor encodes**, as an object of the category.

`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.quotient` at the three hypotheses the
bridge supplies. The two instances are introduced with `letI` and `haveI` because they depend on
`F`; the second is a `Prop` and so carries no choice. -/
def SeparatedFiniteEtaleOver.singleObjQuotient : SeparatedFiniteEtaleOver.{u} X :=
  letI := SeparatedFiniteEtaleOver.singleObjSMul F
  haveI : ContinuousConstSMul G ↥(F.obj (SingleObj.star G)).left :=
    ⟨SeparatedFiniteEtaleOver.continuous_singleObjAut_base F⟩
  (F.obj (SingleObj.star G)).quotient (SeparatedFiniteEtaleOver.singleObjAut_base_over F)

/-- **The quotient map onto it**, which is the only leg the cocone below has. -/
def SeparatedFiniteEtaleOver.singleObjToQuotient :
    F.obj (SingleObj.star G) ⟶ SeparatedFiniteEtaleOver.singleObjQuotient F :=
  letI := SeparatedFiniteEtaleOver.singleObjSMul F
  haveI : ContinuousConstSMul G ↥(F.obj (SingleObj.star G)).left :=
    ⟨SeparatedFiniteEtaleOver.continuous_singleObjAut_base F⟩
  (F.obj (SingleObj.star G)).toQuotient (SeparatedFiniteEtaleOver.singleObjAut_base_over F)

/-- **The quotient cocone.**

`CategoryTheory.SingleObj G` has one object, so a cocone is one morphism together with one equation
per group element, and that equation is
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.comp_toQuotient` at the witness `⟨g, rfl⟩`:
the point `g • y` is in the orbit of `y` by definition of the action. -/
def SeparatedFiniteEtaleOver.singleObjCocone : Limits.Cocone F where
  pt := SeparatedFiniteEtaleOver.singleObjQuotient F
  ι :=
    { app := fun _ ↦ SeparatedFiniteEtaleOver.singleObjToQuotient F
      naturality := fun _ _ g ↦ by
        letI := SeparatedFiniteEtaleOver.singleObjSMul F
        haveI : ContinuousConstSMul G ↥(F.obj (SingleObj.star G)).left :=
          ⟨SeparatedFiniteEtaleOver.continuous_singleObjAut_base F⟩
        change SeparatedFiniteEtaleOver.singleObjAut F g
            ≫ SeparatedFiniteEtaleOver.singleObjToQuotient F
          = SeparatedFiniteEtaleOver.singleObjToQuotient F ≫ 𝟙 _
        rw [Category.comp_id]
        exact SeparatedFiniteEtaleOver.comp_toQuotient
          (SeparatedFiniteEtaleOver.singleObjAut_base_over F)
          (SeparatedFiniteEtaleOver.singleObjAut F g) (fun _ ↦ ⟨g, rfl⟩) }

/-- **The morphism a competing cocone factors through.**

`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.quotientDesc` at the cocone's one leg,
whose invariance is `CategoryTheory.Limits.Cocone.w` read at a point — the cocone's own equation at
`g` is exactly the hypothesis the factorisation asks for. -/
def SeparatedFiniteEtaleOver.singleObjDesc (s : Limits.Cocone F) :
    SeparatedFiniteEtaleOver.singleObjQuotient F ⟶ s.pt :=
  letI := SeparatedFiniteEtaleOver.singleObjSMul F
  haveI : ContinuousConstSMul G ↥(F.obj (SingleObj.star G)).left :=
    ⟨SeparatedFiniteEtaleOver.continuous_singleObjAut_base F⟩
  SeparatedFiniteEtaleOver.quotientDesc (SeparatedFiniteEtaleOver.singleObjAut_base_over F)
    (s.ι.app (SingleObj.star G))
    (fun g y ↦ congrArg
      (fun m : F.obj (SingleObj.star G) ⟶ s.pt ↦ (ConcreteCategory.hom m.left.toLRSHom.base) y)
      (s.w (j := SingleObj.star G) (j' := SingleObj.star G) g))

/-- **And it does factor the leg**, which is the factorisation of the category section. -/
theorem SeparatedFiniteEtaleOver.singleObjToQuotient_comp_desc (s : Limits.Cocone F) :
    SeparatedFiniteEtaleOver.singleObjToQuotient F ≫ SeparatedFiniteEtaleOver.singleObjDesc F s
      = s.ι.app (SingleObj.star G) := by
  letI := SeparatedFiniteEtaleOver.singleObjSMul F
  haveI : ContinuousConstSMul G ↥(F.obj (SingleObj.star G)).left :=
    ⟨SeparatedFiniteEtaleOver.continuous_singleObjAut_base F⟩
  exact SeparatedFiniteEtaleOver.toQuotient_comp_quotientDesc
    (SeparatedFiniteEtaleOver.singleObjAut_base_over F) _ _

/-- **The quotient cocone is a colimit.**

The three fields are the three statements above: the factor, the factorisation, and uniqueness
from `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.quotient_hom_ext`, which in the
category asks only that the two morphisms agree after the quotient map. **Every object of
`CategoryTheory.SingleObj G` is the one object**, so the two fields quantified over objects are
proved at `CategoryTheory.SingleObj.star` and carried to an arbitrary object by the definitional
eta of `Unit`. -/
def SeparatedFiniteEtaleOver.singleObjIsColimit :
    Limits.IsColimit (SeparatedFiniteEtaleOver.singleObjCocone F) where
  desc s := SeparatedFiniteEtaleOver.singleObjDesc F s
  fac s _ := SeparatedFiniteEtaleOver.singleObjToQuotient_comp_desc F s
  uniq s m h := by
    letI := SeparatedFiniteEtaleOver.singleObjSMul F
    haveI : ContinuousConstSMul G ↥(F.obj (SingleObj.star G)).left :=
      ⟨SeparatedFiniteEtaleOver.continuous_singleObjAut_base F⟩
    refine SeparatedFiniteEtaleOver.quotient_hom_ext
      (SeparatedFiniteEtaleOver.singleObjAut_base_over F) ?_
    change SeparatedFiniteEtaleOver.singleObjToQuotient F ≫ m
      = SeparatedFiniteEtaleOver.singleObjToQuotient F ≫ SeparatedFiniteEtaleOver.singleObjDesc F s
    rw [SeparatedFiniteEtaleOver.singleObjToQuotient_comp_desc]
    exact h (SingleObj.star G)

variable (X G) in
/-- **The category of covers separated over a Hausdorff base has colimits of shape
`CategoryTheory.SingleObj G` for every finite group `G`**, which is the fourth `PreGaloisCategory`
field stated without the class.

Every functor out of that shape gets the cocone and the colimit above, so the class is the one
`CategoryTheory.Limits.ColimitCocone` packaged as an existence statement. **The universe of `G` is
unconstrained**, which is what the field asks for — it quantifies over the hom universe of the
category — and `[Finite G]` rather than `[Fintype G]` is what it asks with; neither is weakened
here.

**An `instance` and not a `theorem`**: a consumer of that field arrives by instance search, and
`#synth` at this statement fails at the base and succeeds here. -/
instance SeparatedFiniteEtaleOver.hasColimitsOfShape_singleObj :
    Limits.HasColimitsOfShape (SingleObj G) (SeparatedFiniteEtaleOver.{u} X) where
  has_colimit F := ⟨⟨⟨SeparatedFiniteEtaleOver.singleObjCocone F,
    SeparatedFiniteEtaleOver.singleObjIsColimit F⟩⟩⟩

end Colimit

end ComplexAnalytic.AnalyticSpace
