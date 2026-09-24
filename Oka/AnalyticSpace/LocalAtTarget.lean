/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.AnalyticSpace.PullbackOpen
import Oka.Topology.IsLocalHomeomorph

/-!
# Finiteness, local isomorphism and finite étaleness are local on the target

A property `P` of morphisms is **local on the target** when, for every open cover `{Vᵢ}` of the
target, `P f` holds exactly if `P` holds of `f` restricted over each `Vᵢ`. This file says that of
`ComplexAnalytic.AnalyticSpace.IsFinite`, `ComplexAnalytic.AnalyticSpace.IsLocalIso` and
`ComplexAnalytic.AnalyticSpace.IsFiniteEtale`.

**Only one direction is new.** The restriction direction is already in the tree and is
unconditional in the open subset: `ComplexAnalytic.AnalyticSpace.isFinite_restrictHom` and
`ComplexAnalytic.AnalyticSpace.isFiniteEtale_restrictHom` in `Oka/AnalyticSpace/PullbackOpen.lean`
and `ComplexAnalytic.AnalyticSpace.isLocalIso_restrictHom` in
`Oka/AnalyticSpace/OpenSubspace.lean` are instances and theorems that ask nothing of `V`. What was
absent is the descent, and what existed of it was two statements at `V = ⊤` —
`ComplexAnalytic.AnalyticSpace.isFinite_of_restrictHom_top` and
`ComplexAnalytic.AnalyticSpace.isFiniteEtale_of_restrictHom_top`, with no `IsLocalIso` counterpart
at all.

## Where each field comes from

`ComplexAnalytic.AnalyticSpace.IsFiniteEtale` is `IsFinite` and `IsLocalIso` and nothing else, and
those two are four conditions between them. Three of the four are quotations and one is a theorem
this development had to write:

| condition | instrument |
| --- | --- |
| the base map is closed | Mathlib's `IsOpenCover.isClosedMap_iff_restrictPreimage` |
| the fibres are finite | `Subtype.val` carries one fibre onto the other |
| the stalk maps are isomorphisms | `ComplexAnalytic.stalkMap_restrictHom_eq'` |
| the base map is a local homeomorphism | `IsOpenCover.isLocalHomeomorph_of_restrictPreimage` |

`TopologicalSpace.IsOpenCover.isLocalHomeomorph_of_restrictPreimage` lives in
`Oka/Topology/IsLocalHomeomorph.lean`; the closed-map, finite-fibre and stalk rows were each
readable where they already stand.

**The local-homeomorphism row is the content.** `Mathlib/Topology/LocalAtTarget.lean` proves seven
properties of a continuous map local at the target and `IsLocalHomeomorph` is not among them, so
that statement is in this repository's Mathlib mirror; its docstring prices the two candidate homes
for it.

**And the bridge to Mathlib's spelling was already here.**
`ComplexAnalytic.AnalyticSpace.base_restrictHom_eq_restrictPreimage` says the base map of
`ComplexAnalytic.AnalyticSpace.restrictHom f V` **is** `Set.restrictPreimage`, and its own
docstring calls itself the bridge to `Mathlib/Topology/LocalAtTarget.lean`. Everything below that
touches a base map goes through it.

## Main results

- `ComplexAnalytic.AnalyticSpace.isFinite_of_isOpenCover`: **finiteness descends along an open
  cover of the target.**
- `ComplexAnalytic.AnalyticSpace.isLocalIso_of_isOpenCover`: **being a local isomorphism
  descends.**
- `ComplexAnalytic.AnalyticSpace.isFiniteEtale_of_isOpenCover`: **being finite étale descends**,
  which is the one taxis #1949's route B asks for.
- `ComplexAnalytic.AnalyticSpace.isFinite_iff_restrictHom`,
  `ComplexAnalytic.AnalyticSpace.isLocalIso_iff_restrictHom` and
  `ComplexAnalytic.AnalyticSpace.isFiniteEtale_iff_restrictHom`: the two directions together,
  the forward one costing nothing because it is already in the tree.

## What is not here

* **No descent for `IsCoveringMap`, and none for `[T2Space]`.** Being Hausdorff is not local on
  the target — the line with a doubled origin is covered by two copies of the line — and
  `ComplexAnalytic.AnalyticSpace.not_t2Space_doubledLine` is this repository's witness that the
  space it names is not one. Nothing here says or needs anything about either.
* **No degree.** Nothing below says the number of sheets of `f` is read off the sheets of its
  restrictions, and `ComplexAnalytic.AnalyticSpace.degree_eq_card_fiber` is not cited.
* **No base change.** These statements are along the inclusion of an open subspace, which
  `ComplexAnalytic.AnalyticSpace.isPullback_ofRestrict` makes a pullback square, so each is a base
  change along one particular shape of leg. **They are not
  `CategoryTheory.MorphismProperty.IsStableUnderBaseChange`**, which quantifies over every cospan;
  that class is
  `ComplexAnalytic.AnalyticSpace.isStableUnderBaseChange_isFiniteEtale`, in
  `Oka/AnalyticSpace/FiniteEtaleStableUnderBaseChange.lean`, and nothing below is stated from it or
  proves it. **This clause read *`Oka/AnalyticSpace/FiniteEtaleOver.lean`'s
  `## No base change of the class over a general cospan` bullet is where that absence is stated,
  and this file does not narrow it*, until 2026-09-15**, when the class stopped being an absence;
  that bullet is now headed
  **No base change of the class over a cospan of morphisms of covers**, which is a statement about
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver X` and not about the cospans of this file, and
  this file does not narrow that either.
* **No case analysis on the index type, and `ι` may be empty.** That is a decision and not an
  oversight: `TopologicalSpace.IsOpenCover U` at an empty `ι` says `⊥ = ⊤` in `Y.Opens`, which
  forces `Y`'s carrier to be empty, and each conclusion then holds because every condition below
  is a condition at a point of a space that has none. **No proof here special-cases it and none
  needs to** — `TopologicalSpace.IsOpenCover.exists_mem` is what would fail at an empty `ι`, and
  it does not, because it is applied to a point of `Y` and there is no such point to apply it to.
* **Nothing is built.** No space, no morphism and no cover is constructed here; the cover is a
  hypothesis in every statement. `Oka/AnalyticSpace/Glue.lean` is the file that builds a space out
  of a cover and shares nothing with this one but the word.
* **No witness, and no statement that the criteria reach a cover no member of which is `⊤`.**
* **Neither `…_of_restrictHom_top` theorem is replaced or deprecated.** Each keeps its own proof
  and its own consumers.
-/

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry Topology

universe u

namespace ComplexAnalytic.AnalyticSpace

variable {X Y : AnalyticSpace.{u}} (f : X ⟶ Y) {ι : Type*} {U : ι → Y.Opens}

/-! ### Finiteness -/

/-- **Finiteness descends along an open cover of the target.**

Both fields are conditions on the base map and both are carried by
`ComplexAnalytic.AnalyticSpace.base_restrictHom_eq_restrictPreimage`, which turns each restriction
into `Set.restrictPreimage`, the spelling Mathlib's local-at-target lemmas are stated in.

**Closedness is a quotation**, `TopologicalSpace.IsOpenCover.isClosedMap_iff_restrictPreimage`,
and it is the half that would be false for a single `V`: a map can be closed over each of two
opens covering the target without any one of them seeing all of it.

**The fibres are elementary and the only care needed is which direction the injection runs.** The
fibre of `f` over `y` is the image under `Subtype.val` of the fibre of the restriction over
`⟨y, hi⟩` at any member `U i` containing `y` — a point of `X` over `y` lies over a point of `U i`,
so it lies in the preimage and the two fibres correspond. `Set.finite_coe_iff` is what converts
between the `Finite ↥s` the class carries and the `Set.Finite` the image lemma takes;
`Set.toFinite` does not close it, because `Set.Elem` is not reducible and the two are different
instance-search problems. -/
theorem isFinite_of_isOpenCover (hU : IsOpenCover U)
    (h : ∀ i, IsFinite (restrictHom f (U i))) : IsFinite f where
  isClosedMap := by
    rw [hU.isClosedMap_iff_restrictPreimage]
    intro i
    have hcl := (h i).isClosedMap
    rwa [base_restrictHom_eq_restrictPreimage] at hcl
  finite_fiber y := by
    obtain ⟨i, hi⟩ := hU.exists_mem y
    have hfin := (h i).finite_fiber ⟨y, hi⟩
    rw [base_restrictHom_eq_restrictPreimage] at hfin
    have himg : (f.toLRSHom.base : X → Y) ⁻¹' {y} =
        Subtype.val ''
          (((U i : Set Y).restrictPreimage (f.toLRSHom.base : X → Y)) ⁻¹' {⟨y, hi⟩}) := by
      ext x
      constructor
      · intro hx
        have hx' : (f.toLRSHom.base : X → Y) x = y := hx
        refine ⟨⟨x, ?_⟩, ?_, rfl⟩
        · simp only [Set.mem_preimage, hx']
          exact hi
        · exact Subtype.ext hx'
      · rintro ⟨z, hz, rfl⟩
        exact congrArg Subtype.val hz
    rw [himg]
    exact ((Set.finite_coe_iff.mp hfin).image _).to_subtype

/-- **Finiteness is local on the target.**

The forward direction is `ComplexAnalytic.AnalyticSpace.isFinite_restrictHom`, which is an
instance and asks nothing of the open subset, so this `iff` costs exactly what
`ComplexAnalytic.AnalyticSpace.isFinite_of_isOpenCover` above costs.

**This is the statement two docstrings in this repository denied, and each carries a dated record
of the wording the push that added this file retired** — see
`ComplexAnalytic.AnalyticSpace.isLocalIso_restrictHom` in `Oka/AnalyticSpace/OpenSubspace.lean`
for what they were drawing a contrast with, which is a true contrast about a morphism that is not
finite and survives unchanged. **No record is written here**: this file is new, so it retires no
wording of its own, and a record in it would be a census match that is not a record. -/
theorem isFinite_iff_restrictHom (hU : IsOpenCover U) :
    IsFinite f ↔ ∀ i, IsFinite (restrictHom f (U i)) :=
  ⟨fun _ i ↦ isFinite_restrictHom f (U i), isFinite_of_isOpenCover f hU⟩

/-! ### Local isomorphisms -/

/-- **Being a local isomorphism descends along an open cover of the target.**

The topological field is
`TopologicalSpace.IsOpenCover.isLocalHomeomorph_of_restrictPreimage`, whose `Continuous`
hypothesis is the base map's own and costs nothing here.

**The stalk field is a peeling and not a transport.**
`ComplexAnalytic.stalkMap_restrictHom_eq'` already writes the restriction's stalk map as
`iso ≫ f.stalkMap _ ≫ iso`, so having it an isomorphism gives the middle factor by
`CategoryTheory.IsIso.of_isIso_comp_left` and then
`CategoryTheory.IsIso.of_isIso_comp_right`, and nothing is computed.

**The point of the restricted space is introduced by `obtain` and not written `⟨x, hx⟩`**, and
that is forced twice over. With an anonymous constructor,
`IsIso ((X.toLocallyRingedSpace.ofRestrict _).stalkMap ⟨x, hx⟩)` is not synthesised while the same
statement at a variable is; and the equation identifying that point's image with `x` cannot be
rewritten inside the hypothesis, because `ComplexAnalytic.restrictStalkEquiv`'s *type* mentions
it and the motive is not type correct. So the peeling happens at the original spelling and the
transport is the single `▸` at the end, where the motive is `fun a ↦ IsIso (f.stalkMap a)`. -/
theorem isLocalIso_of_isOpenCover (hU : IsOpenCover U)
    (h : ∀ i, IsLocalIso (restrictHom f (U i))) : IsLocalIso f where
  isLocalHomeomorph := by
    refine hU.isLocalHomeomorph_of_restrictPreimage f.toLRSHom.base.hom.continuous fun i ↦ ?_
    have hlh := (h i).isLocalHomeomorph
    rwa [base_restrictHom_eq_restrictPreimage] at hlh
  isIso_stalkMap x := by
    obtain ⟨i, hi⟩ := hU.exists_mem ((f.toLRSHom.base : X → Y) x)
    have hx : x ∈ ((Opens.map f.toLRSHom.base).obj (U i) : Set X) := hi
    obtain ⟨x', hx'⟩ : ∃ x' : X.restrict ((Opens.map f.toLRSHom.base).obj (U i)),
        ((X.toLocallyRingedSpace.ofRestrict
          ((Opens.map f.toLRSHom.base).obj (U i)).isOpenEmbedding).base x') = x :=
      ⟨⟨x, hx⟩, rfl⟩
    have hiso : IsIso ((ComplexAnalytic.restrictHom f.toLRSHom (U i)).stalkMap x') :=
      (h i).isIso_stalkMap x'
    rw [ComplexAnalytic.stalkMap_restrictHom_eq'] at hiso
    haveI := hiso
    haveI hBC : IsIso (f.toLRSHom.stalkMap
          ((X.toLocallyRingedSpace.ofRestrict
            ((Opens.map f.toLRSHom.base).obj (U i)).isOpenEmbedding).base x') ≫
        (X.toLocallyRingedSpace.ofRestrict
          ((Opens.map f.toLRSHom.base).obj (U i)).isOpenEmbedding).stalkMap x') :=
      IsIso.of_isIso_comp_left
        (ComplexAnalytic.restrictStalkEquiv f.toLRSHom (U i) x').hom _
    haveI hB : IsIso (f.toLRSHom.stalkMap
        ((X.toLocallyRingedSpace.ofRestrict
          ((Opens.map f.toLRSHom.base).obj (U i)).isOpenEmbedding).base x')) :=
      IsIso.of_isIso_comp_right _
        ((X.toLocallyRingedSpace.ofRestrict
          ((Opens.map f.toLRSHom.base).obj (U i)).isOpenEmbedding).stalkMap x')
    exact hx' ▸ hB

/-- **Being a local isomorphism is local on the target.**

The forward direction is `ComplexAnalytic.AnalyticSpace.isLocalIso_restrictHom`, whose docstring
already says that both fields of the class are conditions at a point and that a restriction moves
neither. **At the commit that writes this it is the only descent statement for `IsLocalIso` in this
repository at any open subset**, `⊤` included:
`ComplexAnalytic.AnalyticSpace.isFinite_of_restrictHom_top` and
`ComplexAnalytic.AnalyticSpace.isFiniteEtale_of_restrictHom_top` are the two
`…_of_restrictHom_top` theorems and neither is for this class. -/
theorem isLocalIso_iff_restrictHom (hU : IsOpenCover U) :
    IsLocalIso f ↔ ∀ i, IsLocalIso (restrictHom f (U i)) :=
  ⟨fun _ i ↦ isLocalIso_restrictHom f (U i), isLocalIso_of_isOpenCover f hU⟩

/-! ### Finite étale morphisms -/

/-- **Being finite étale descends along an open cover of the target.**

The two fields are `ComplexAnalytic.AnalyticSpace.isFinite_of_isOpenCover` and
`ComplexAnalytic.AnalyticSpace.isLocalIso_of_isOpenCover`, and there is no proof of its own:
`IsFiniteEtale` is `IsFinite` and `IsLocalIso` and carries no third field. -/
theorem isFiniteEtale_of_isOpenCover (hU : IsOpenCover U)
    (h : ∀ i, IsFiniteEtale (restrictHom f (U i))) : IsFiniteEtale f where
  isFinite := isFinite_of_isOpenCover f hU fun i ↦ (h i).isFinite
  isLocalIso := isLocalIso_of_isOpenCover f hU fun i ↦ (h i).isLocalIso

/-- **Being finite étale is local on the target.**

This is the criterion taxis #1949's route B is named for: it is what turns a statement proved over
each member of a cover of the base into a statement about the morphism. **It says nothing about
base change over a general cospan**, and the bullet in
`Oka/AnalyticSpace/FiniteEtaleOver.lean` that records that absence is untouched by it. -/
theorem isFiniteEtale_iff_restrictHom (hU : IsOpenCover U) :
    IsFiniteEtale f ↔ ∀ i, IsFiniteEtale (restrictHom f (U i)) :=
  ⟨fun _ i ↦ isFiniteEtale_restrictHom f (U i), isFiniteEtale_of_isOpenCover f hU⟩

end ComplexAnalytic.AnalyticSpace
