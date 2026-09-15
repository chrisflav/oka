/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.AnalyticSpace.CoveringMap
import Oka.AnalyticSpace.CoveringSpace
import Oka.Topology.Maps.Proper.Basic

/-!
# Base change of a finite étale morphism of complex analytic spaces

Let `q : E ⟶ B` be finite étale and let `f : B' ⟶ B` be **any** morphism of complex analytic
spaces. Then the fibre product `E ×_B B'` exists, its projection to `B'` is finite étale again,
and the square is a pullback in `ComplexAnalytic.AnalyticSpace`. **No separation axiom is asked
of any of the three spaces**, and `ComplexAnalytic.AnalyticSpace.doubledLineFold` is a finite
étale morphism whose source is not one — `OkaTest/FiniteEtaleBaseChangeNonHausdorff.lean`
applies four of this file's statements at that leg, one in each of four of its five `example`s,
which is what checks that they apply at all.

**The opening sentence read *Let `q : E ⟶ B` be finite étale with `E` Hausdorff* and the file
carried `[T2Space E]` in its `variable` block, until 2026-09-14**, when the route through
`ComplexAnalytic.AnalyticSpace.isCoveringMap_baseChangeSndBase` was replaced by the two
statements named in `## Where each hypothesis is spent`. The hypothesis was never spent on the
conclusion: it bought a covering map where a closed local homeomorphism is what
`ComplexAnalytic.AnalyticSpace.isFiniteEtale_coveringSpaceHom_of_isClosedMap` asks for, and that
statement was added to `Oka/AnalyticSpace/CoveringSpace.lean` on 2026-09-13 by `7b7ce5a`. **The
constructions are unchanged**: `ComplexAnalytic.AnalyticSpace.baseChange` and
`ComplexAnalytic.AnalyticSpace.baseChangeSnd` differ from what they were only in which proof of a
`Prop` is passed to `ComplexAnalytic.AnalyticSpace.coveringSpace`, so by proof irrelevance the
terms are the same and no consumer is transported.

`Oka/AnalyticSpace/FiniteEtaleOver.lean` records the absence of this base change in its
`## What is not here` bullet **No base change of the class over a cospan of morphisms of covers**,
and again in
the docstring of `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fintypeFiberFunctor`. **That bullet
was headed *No pullback over a general cospan, so no base change* when this sentence was written
and until 2026-09-08**, when `Oka/AnalyticSpace/PullbackReduction.lean` made
`CategoryTheory.Limits.HasPullbacks ComplexAnalytic.AnalyticSpace` a theorem and the first half of
the heading stopped being true; only the heading moved and what this file narrows is what it
always narrowed. **And it was headed *No base change of the class over a general cospan* until
2026-09-15**, when `Oka/AnalyticSpace/FiniteEtaleStableUnderBaseChange.lean` assembled the
statements below into
`CategoryTheory.MorphismProperty.IsStableUnderBaseChange` for
`ComplexAnalytic.AnalyticSpace.isFiniteEtale`; the heading moved again and what this file narrows
is still what it always narrowed. **The bullet is narrowed by this file and is not narrowed to
nothing, and this
file does not make that category a Galois category.** Those axioms quantify over cospans of
morphisms *of covers*, and a morphism of
covers is not known to be finite étale without `[T2Space]` of its target, which is taxis #1772's
remaining half; nor is a cover's total space assumed Hausdorff anywhere in that file. The four
further sentences of that file which cite the bullet by its heading assert of it what they always
asserted, and it says so. **That clause called them *unaffected* until 2026-09-15**, when the
heading moved a second time and all four were rewritten to name the new one — a rewriting of the
pointer and not of the claim, which is the distinction the clause was making and now makes in
words that do not also deny the edit.

## The route, and why it touches no local model

The construction is the topological one, carried across by `Oka/AnalyticSpace/CoveringSpace.lean`.

1. **The carrier is Mathlib's set-level pullback** `Function.Pullback q.base f.base`, a subspace of
   the product, and its second projection is a covering map with finite fibres — by
   `IsCoveringMap.pullback_snd` and `Function.Pullback.finite_fiber_snd`, both in
   `Oka/Topology/Covering/Basic.lean`, applied to
   `ComplexAnalytic.AnalyticSpace.isCoveringMap_base_of_isFiniteEtale`.
2. **A covering map of the base carries an analytic structure for free.**
   `ComplexAnalytic.AnalyticSpace.coveringSpace` puts `π₂⁻¹𝒪_{B'}` on that carrier and
   `ComplexAnalytic.AnalyticSpace.isFiniteEtale_coveringSpaceHom` makes the second projection
   finite étale. Nothing is glued: that file's docstring says why the `ℂ`-algebra structure lands
   in global sections and needs no cover.
3. **The first projection is a morphism out of an inverse image**, and that is what
   `AlgebraicGeometry.LocallyRingedSpace.inverseImageMap` is for. Composed with the comparison
   isomorphism `E ≅ q.base⁻¹B`, which exists because `q` is a local isomorphism, it lands in `E`.
4. **The universal property is the uniqueness in
   `AlgebraicGeometry.LocallyRingedSpace.inverseImage_hom_ext`** — twice, once for each half. A
   morphism into `π₂⁻¹B'` is pinned by its base map and its composite to `B'`, and the base map of
   a morphism into a set-level pullback is pinned by its two components.

**No local model, no zero locus, no cutting out and no gluing of spaces occurs anywhere below**,
which is worth saying because the fibre product of analytic spaces is usually built that way and
this repository has a whole ladder of issues doing it that way.

## Where each hypothesis is spent

**`[IsFiniteEtale q]` is the only hypothesis, and no separation axiom is spent anywhere.**
Nothing is assumed of `E`, of `B` or of `B'`, and `f` is an arbitrary morphism — not finite, not
étale, not injective.

**That paragraph opened *`[T2Space E]` is spent exactly once*, in
`ComplexAnalytic.AnalyticSpace.isCoveringMap_baseChangeSndBase`, until 2026-09-14.** That lemma
is still here and still true, and it is still the one declaration of this file that carries
`[T2Space E]`; what changed is that nothing consumes it. It is kept rather than deleted because it
is guarded, and because the covering-map statement is the one a reader coming from
`Oka/AnalyticSpace/CoveringMap.lean` will look for.

**`[IsFiniteEtale q]` is spent in both of its halves, and each half is spent twice.** Its
`IsFinite` field supplies the finite fibres, through
`ComplexAnalytic.AnalyticSpace.finite_fiber_baseChangeSndBase`, which needs no topology at all,
and the closedness of the second projection, through
`ComplexAnalytic.AnalyticSpace.isClosedMap_baseChangeSndBase`, which goes by properness; its
`IsLocalIso` field supplies the local-homeomorphism half, through
`ComplexAnalytic.AnalyticSpace.isLocalHomeomorph_baseChangeSndBase`, and the stalk isomorphisms
that make `ComplexAnalytic.AnalyticSpace.inverseImageIsoOfIsLocalIso` an isomorphism. **The first
projection does not need `q` finite** and the second does not need `q` a local isomorphism; both
are needed for the square to be a pullback, because the space is built out of the covering
property.

**That paragraph opened *`[IsFiniteEtale q]` is spent twice and in two different halves* and named
one statement per half, until 2026-09-14**, when the two statements that replace the covering-map
route were added and each half acquired a second consumer. The sentence was exact when written;
what moved is the route and not the accounting rule.

## Main definitions

- `ComplexAnalytic.AnalyticSpace.baseChange`: **the fibre product `E ×_B B'`**, whose carrier is
  `Function.Pullback q.base f.base` on the nose and whose structure sheaf is `π₂⁻¹𝒪_{B'}`.
- `ComplexAnalytic.AnalyticSpace.baseChangeFst` and
  `ComplexAnalytic.AnalyticSpace.baseChangeSnd`: its two projections.
- `ComplexAnalytic.AnalyticSpace.baseChangeLift`: the morphism a commuting square induces into it.
- `ComplexAnalytic.AnalyticSpace.inverseImageIsoOfIsLocalIso`: **the source of a local isomorphism
  is the inverse image of its target along its base map**, as an isomorphism of *locally ringed*
  spaces. `ComplexAnalytic.AnalyticSpace.coveringSpaceIso` is the analytic-space statement of the
  same fact and neither is stated in terms of the other.

## Main results

- `ComplexAnalytic.AnalyticSpace.isFiniteEtale_baseChangeSnd`: **the projection to `B'` is finite
  étale.**
- `ComplexAnalytic.AnalyticSpace.baseChange_square`: the square commutes.
- `ComplexAnalytic.AnalyticSpace.baseChange_hom_ext`: **two morphisms into the fibre product
  agreeing on both projections are equal.**
- `ComplexAnalytic.AnalyticSpace.isPullback_baseChange`: **the square is a pullback.**
- `ComplexAnalytic.AnalyticSpace.hasPullback_of_isFiniteEtale`: hence `Limits.HasPullback q f`, as
  an instance.
- `ComplexAnalytic.AnalyticSpace.isFiniteEtale_pullback_snd_of_isFiniteEtale`: and hence
  `Limits.pullback.snd q f` is finite étale — **the base-change statement in the spelling
  `CategoryTheory.MorphismProperty.IsStableUnderBaseChange` is written in**.

## What is not here

* **This is not `CategoryTheory.Limits.HasPullbacks ComplexAnalytic.AnalyticSpace`.** Every
  statement below has a finite étale leg in its cospan and a general cospan has none.
  `#synth CategoryTheory.Limits.HasPullbacks ComplexAnalytic.AnalyticSpace` **fails** at the
  commit that adds this file, on my own run, with the category positional so that it is fixed by
  the statement and not by a named argument. Gluing — taxis #1820's rung 3 — is what would close
  that, and this file goes around it rather than through it. **That prediction held**: the class
  became a theorem on 2026-09-08, in `Oka/AnalyticSpace/PullbackReduction.lean`, by gluing and by
  nothing else. The `#synth` sentence above is pinned to the commit that adds *this* file and is
  not retired; what this bullet still says is that no statement below is that class.
* **No weakening of `[IsFiniteEtale q]`.** Both of its fields are spent, and
  `## Where each hypothesis is spent` says which statement spends which; nothing below asks for
  less than the class.

  **This bullet read *`[T2Space E]` is not removed and nothing here tries*, and gave as its
  reason that the hypothesis is Mathlib's in the criterion that turns a proper local
  homeomorphism into a covering map, until 2026-09-14.** The reason was exact and is why the
  hypothesis was there; what it did not say is that the criterion is not the only route to the
  conclusion, which is what retired the bullet rather than a recount.
* **No `CategoryTheory.MorphismProperty.IsStableUnderBaseChange` instance.** That class is a
  statement about the *class* `ComplexAnalytic.AnalyticSpace.isFiniteEtale` as a
  `CategoryTheory.MorphismProperty`, and nothing below is stated at that spelling;
  `ComplexAnalytic.AnalyticSpace.isFiniteEtale_pullback_snd_of_isFiniteEtale` is the statement it
  is assembled from and the assembly is not here. **It is in
  `Oka/AnalyticSpace/FiniteEtaleStableUnderBaseChange.lean`**, which imports this file and
  `Oka/AnalyticSpace/FiniteEtaleOver.lean` — the second being where
  `ComplexAnalytic.AnalyticSpace.isFiniteEtale` is declared, and it is not in this file's import
  closure, which is why the assembly is not here and not merely why it is elsewhere.
  **The sentence ending *and the assembly is not here* read *is the statement it would be
  assembled from* and stopped there, until 2026-09-15**, when the assembly was made and the
  sentence naming where it is was added after it. What the bullet says of the statements *below*
  is unchanged, and the reason it is a bullet at all is that a reader looking here for the class
  should be sent somewhere rather than told it does not exist.

  **This bullet gave as its reason that the class quantifies over *all* cospans with a leg in the
  class, including those whose finite étale leg has a non-Hausdorff source, and that nothing
  below reaches one, until 2026-09-14.** The second half stopped being true in the same push that
  removed `[T2Space E]`: the statements below reach every cospan the class quantifies over, and
  `OkaTest/FiniteEtaleBaseChangeNonHausdorff.lean` compiles them at one whose finite étale leg has
  a non-Hausdorff source. What is absent **from this file** is the
  `CategoryTheory.MorphismProperty` spelling and not the reach. **That last sentence read *What is
  still absent is the `CategoryTheory.MorphismProperty` spelling and not the reach*, with no file
  named, until 2026-09-15**, when that spelling landed one module further on and *still absent*
  stopped being available as a reading of it.
* **Nothing about the degree.** `ComplexAnalytic.AnalyticSpace.degree_eq_card_fiber` would say the
  base change has the same number of sheets; the fibres do correspond, by
  `Function.Pullback.fst`, and no statement below says so.
* **No comparison with `ComplexAnalytic.AnalyticSpace.restrictHom`.** For `f` an open immersion
  `Oka/AnalyticSpace/PullbackOpen.lean` already builds this pullback, by restriction rather than
  by an inverse image, and the two are not compared here.
-/

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry TopCat Topology

universe u

noncomputable section

namespace ComplexAnalytic.AnalyticSpace

variable {E B B' : AnalyticSpace.{u}} (q : E ⟶ B) (f : B' ⟶ B)

/-! ### The carrier, and the two projections as continuous maps -/

/-- **The carrier of the fibre product**: Mathlib's set-level pullback `Function.Pullback`, a
subtype of the product, with the subspace topology. -/
def baseChangeCarrier : TopCat.{u} :=
  TopCat.of (Function.Pullback q.toLRSHom.base f.toLRSHom.base)

/-- The first projection of the carrier, as a morphism of topological spaces. -/
def baseChangeFstBase : baseChangeCarrier q f ⟶ E.toLocallyRingedSpace.toTopCat :=
  TopCat.ofHom ⟨Function.Pullback.fst, continuous_fst.comp continuous_subtype_val⟩

/-- The second projection of the carrier, as a morphism of topological spaces. -/
def baseChangeSndBase : baseChangeCarrier q f ⟶ B'.toLocallyRingedSpace.toTopCat :=
  TopCat.ofHom ⟨Function.Pullback.snd, continuous_snd.comp continuous_subtype_val⟩

/-- **The square of carriers commutes**, which is the defining property of a point of
`Function.Pullback` and is `rfl` at each point. It is stated in this direction — `snd ≫ f` on the
left — because that is the side the analytic structure is built on. -/
theorem baseChange_base_square :
    baseChangeSndBase q f ≫ f.toLRSHom.base = baseChangeFstBase q f ≫ q.toLRSHom.base := by
  ext z
  exact z.2.symm

/-- **The second projection is a covering map.** `IsCoveringMap.pullback_snd` at
`ComplexAnalytic.AnalyticSpace.isCoveringMap_base_of_isFiniteEtale`, whose `Continuous` hypothesis
is `f`'s. **This is the one declaration of this file that carries `[T2Space E]`, and nothing else
in the file uses it** — `ComplexAnalytic.AnalyticSpace.isLocalHomeomorph_baseChangeSndBase` and
`ComplexAnalytic.AnalyticSpace.isClosedMap_baseChangeSndBase` carry the same two halves of
`[IsFiniteEtale q]` across the base change without it, and they are what the construction
consumes.

**This docstring closed *This is the one place `[T2Space E]` is used in this
file*, until 2026-09-14**, when the construction stopped using this lemma; *place* is replaced by
*declaration* because a grep for the token now returns this file's prose about it as well as its
one binder. -/
theorem isCoveringMap_baseChangeSndBase [IsFiniteEtale q] [T2Space E] :
    IsCoveringMap ⇑(baseChangeSndBase q f) :=
  (isCoveringMap_base_of_isFiniteEtale q).pullback_snd f.toLRSHom.base.hom.continuous

/-- **And its fibres are finite.** `Function.Pullback.finite_fiber_snd` uses neither a topology
nor the covering property, so this asks only for the `IsFinite` half of `IsFiniteEtale` and not
for `[T2Space E]`. **It is one of the three statements about `baseChangeSndBase` that ask no
separation axiom** — the other two are
`ComplexAnalytic.AnalyticSpace.isLocalHomeomorph_baseChangeSndBase` and
`ComplexAnalytic.AnalyticSpace.isClosedMap_baseChangeSndBase` — and the three together are
everything the construction consumes. -/
theorem finite_fiber_baseChangeSndBase [IsFiniteEtale q] (y : B') :
    (⇑(baseChangeSndBase q f) ⁻¹' {y}).Finite :=
  Function.Pullback.finite_fiber_snd (fun x ↦ IsFinite.finite_fiber (f := q) x) y

/-- **The second projection is a local homeomorphism**, which is the `IsLocalIso` half of
`[IsFiniteEtale q]` and nothing else. `IsLocalHomeomorph.pullback_snd` is the base change of a
local homeomorphism along an arbitrary continuous map, and no separation axiom enters it. -/
theorem isLocalHomeomorph_baseChangeSndBase [IsFiniteEtale q] :
    IsLocalHomeomorph ⇑(baseChangeSndBase q f) :=
  (IsLocalIso.isLocalHomeomorph (f := q)).pullback_snd f.toLRSHom.base.hom.continuous

/-- **The second projection is a closed map**, which is the `IsFinite` half. A finite morphism of
analytic spaces has a proper base map, properness is stable under base change along an arbitrary
continuous map by `IsProperMap.pullback_snd`, and a proper map is closed. **No separation axiom
enters this either**, which is what makes it the route this file takes rather than
`ComplexAnalytic.AnalyticSpace.isCoveringMap_baseChangeSndBase`. -/
theorem isClosedMap_baseChangeSndBase [IsFiniteEtale q] :
    IsClosedMap ⇑(baseChangeSndBase q f) :=
  ((isProperMap_base_of_isFinite q).pullback_snd f.toLRSHom.base.hom.continuous).isClosedMap

variable [IsFiniteEtale q]

/-! ### The space and the projection to `B'` -/

/-- **The fibre product `E ×_B B'`**, as a complex analytic space: the covering space of `B'`
along the second projection of the carrier. Its structure sheaf is `π₂⁻¹𝒪_{B'}` and nothing is
glued. -/
def baseChange : AnalyticSpace.{u} :=
  AnalyticSpace.coveringSpace B' (baseChangeSndBase q f)
    (isLocalHomeomorph_baseChangeSndBase q f)

/-- **The projection to `B'`.** -/
def baseChangeSnd : baseChange q f ⟶ B' :=
  AnalyticSpace.coveringSpaceHom B' (baseChangeSndBase q f)
    (isLocalHomeomorph_baseChangeSndBase q f)

@[simp]
theorem base_baseChangeSnd :
    (baseChangeSnd q f).toLRSHom.base = baseChangeSndBase q f := rfl

/-- **The projection to `B'` is finite étale**, which is the whole of the base-change statement
for the class and needs none of the universal property below. -/
theorem isFiniteEtale_baseChangeSnd : IsFiniteEtale (baseChangeSnd q f) :=
  AnalyticSpace.isFiniteEtale_coveringSpaceHom_of_isClosedMap B' (baseChangeSndBase q f)
    (isLocalHomeomorph_baseChangeSndBase q f) (isClosedMap_baseChangeSndBase q f)
    (finite_fiber_baseChangeSndBase q f)

/-! ### The projection to `E` -/

/-- **The comparison morphism of a local isomorphism is an isomorphism**, which is
`AlgebraicGeometry.LocallyRingedSpace.isIso_toInverseImage` fed the stalk field of
`ComplexAnalytic.AnalyticSpace.IsLocalIso`. -/
theorem isIso_toInverseImage_of_isLocalIso : IsIso (LocallyRingedSpace.toInverseImage q.toLRSHom) :=
  LocallyRingedSpace.isIso_toInverseImage _ fun z ↦ IsLocalIso.isIso_stalkMap z

/-- **The source of a local isomorphism is the inverse image of its target along its base map**,
as an isomorphism of locally ringed spaces over the target.

`ComplexAnalytic.AnalyticSpace.coveringSpaceIso` says the same thing one category up, between
*analytic* spaces, and is not what is wanted here: what the first projection has to be built out
of is a morphism of locally ringed spaces, its `ℂ`-linearity being recovered afterwards from the
commuting square. -/
def inverseImageIsoOfIsLocalIso :
    E.toLocallyRingedSpace ≅
      LocallyRingedSpace.inverseImage B.toLocallyRingedSpace q.toLRSHom.base :=
  @asIso _ _ _ _ _ (isIso_toInverseImage_of_isLocalIso q)

set_option backward.isDefEq.respectTransparency false in
/-- **The fibre product's morphism to `B`**, which is the diagonal of the square and is the
morphism the first projection is built as a factorisation of. It is `π₂` followed by `f`. -/
def baseChangeToBase : (baseChange q f).toLocallyRingedSpace ⟶ B.toLocallyRingedSpace :=
  LocallyRingedSpace.inverseImageHom B'.toLocallyRingedSpace (baseChangeSndBase q f) ≫ f.toLRSHom

set_option backward.isDefEq.respectTransparency false in
/-- **The projection to `E`, as a morphism of locally ringed spaces.**

Three factors, and each is forced. `AlgebraicGeometry.LocallyRingedSpace.toInverseImage` at the
diagonal lands in `q.base⁻¹B` **along the diagonal's own base map**;
`AlgebraicGeometry.LocallyRingedSpace.inverseImageMapOfEq` at
`ComplexAnalytic.AnalyticSpace.baseChange_base_square` moves that to `q.base⁻¹B` along `q.base`,
which is the step whose base map is the first projection; and the inverse of
`ComplexAnalytic.AnalyticSpace.inverseImageIsoOfIsLocalIso` lands in `E`.

**The `ℂ`-linearity is not proved here and is not proved directly anywhere.** It is
`ComplexAnalytic.IsCLinearHom.of_comp` at the square below, which is the same move
`Oka/AnalyticSpace/Basic.lean` uses for the inverse of an isomorphism. -/
def baseChangeFstLRS : (baseChange q f).toLocallyRingedSpace ⟶ E.toLocallyRingedSpace :=
  LocallyRingedSpace.toInverseImage (baseChangeToBase q f) ≫
    LocallyRingedSpace.inverseImageMapOfEq q.toLRSHom.base (baseChangeFstBase q f)
      (baseChangeToBase q f).base (baseChange_base_square q f) ≫
    (inverseImageIsoOfIsLocalIso q).inv

set_option backward.isDefEq.respectTransparency false in
/-- **The square commutes, at the level of locally ringed spaces.**

Each of the three factors of the first projection contributes one step:
`AlgebraicGeometry.LocallyRingedSpace.toInverseImage_comp` for the outer one,
`AlgebraicGeometry.LocallyRingedSpace.inverseImageMapOfEq_comp` for the middle, and the
factorisation of `q` through its own inverse image for the inner. -/
theorem baseChangeFstLRS_comp :
    baseChangeFstLRS q f ≫ q.toLRSHom = baseChangeToBase q f := by
  have h0 : (inverseImageIsoOfIsLocalIso q).hom ≫
      LocallyRingedSpace.inverseImageHom B.toLocallyRingedSpace q.toLRSHom.base = q.toLRSHom :=
    LocallyRingedSpace.toInverseImage_comp q.toLRSHom
  have h1 := (inverseImageIsoOfIsLocalIso q).inv_hom_id_assoc
    (LocallyRingedSpace.inverseImageHom B.toLocallyRingedSpace q.toLRSHom.base)
  rw [h0] at h1
  rw [baseChangeFstLRS, Category.assoc, Category.assoc, h1,
    LocallyRingedSpace.inverseImageMapOfEq_comp, LocallyRingedSpace.toInverseImage_comp]

set_option backward.isDefEq.respectTransparency false in
/-- **The projection to `E` is `ℂ`-linear**, by `ComplexAnalytic.IsCLinearHom.of_comp` at the
square: both legs into `B` are `ℂ`-linear for the same structure on `B`, so any morphism
factorising one through the other is `ℂ`-linear, whatever it is. -/
theorem isCLinearHom_baseChangeFstLRS :
    IsCLinearHom (baseChangeFstLRS q f) (baseChange q f).algebraMap E.algebraMap :=
  IsCLinearHom.of_comp (baseChangeFstLRS_comp q f)
    (IsCLinearHom.comp (baseChangeSnd q f).isCLinear f.isCLinear) q.isCLinear

/-- **The projection to `E`.** -/
def baseChangeFst : baseChange q f ⟶ E :=
  ⟨baseChangeFstLRS q f, isCLinearHom_baseChangeFstLRS q f⟩

/-- **The square commutes.** -/
theorem baseChange_square : baseChangeFst q f ≫ q = baseChangeSnd q f ≫ f :=
  forgetToLocallyRingedSpace.map_injective (baseChangeFstLRS_comp q f)

/-- **The inverse of `ComplexAnalytic.AnalyticSpace.inverseImageIsoOfIsLocalIso` is the identity
on points**, since the comparison morphism's base map is the identity on the nose. -/
theorem inverseImageIsoOfIsLocalIso_inv_base_apply
    (x : LocallyRingedSpace.inverseImage B.toLocallyRingedSpace q.toLRSHom.base) :
    (inverseImageIsoOfIsLocalIso q).inv.base x = x :=
  LocallyRingedSpace.iso_hom_base_inv_base_apply (inverseImageIsoOfIsLocalIso q) x

set_option backward.isDefEq.respectTransparency false in
/-- **The base map of the projection to `E` is the first projection of the carrier.** Of the three
factors two are the identity on points and the middle one is `h` by
`AlgebraicGeometry.LocallyRingedSpace.inverseImageMapOfEq_base`. -/
@[simp]
theorem base_baseChangeFst :
    (baseChangeFst q f).toLRSHom.base = baseChangeFstBase q f := by
  ext z
  change (inverseImageIsoOfIsLocalIso q).inv.base
      ((LocallyRingedSpace.inverseImageMapOfEq q.toLRSHom.base (baseChangeFstBase q f)
          (baseChangeToBase q f).base (baseChange_base_square q f)).base
        ((LocallyRingedSpace.toInverseImage (baseChangeToBase q f)).base z)) = _
  rw [inverseImageIsoOfIsLocalIso_inv_base_apply, LocallyRingedSpace.inverseImageMapOfEq_base]
  rfl

/-! ### The universal property -/

variable {Z : AnalyticSpace.{u}} (a : Z ⟶ E) (b : Z ⟶ B') (hab : a ≫ q = b ≫ f)

/-- **The lift on carriers**: the pair of the two base maps, which lands in the set-level pullback
because the square of analytic spaces commutes. -/
def baseChangeLiftBase : Z.toLocallyRingedSpace.toTopCat ⟶ baseChangeCarrier q f :=
  TopCat.ofHom
    ⟨fun z ↦ ⟨(a.toLRSHom.base z, b.toLRSHom.base z),
        congrFun (congrArg (fun m : Z.toLocallyRingedSpace ⟶ B.toLocallyRingedSpace ↦
          (m.base : Z.toLocallyRingedSpace.toTopCat → B.toLocallyRingedSpace.toTopCat))
          (congrArg Hom.toLRSHom hab)) z⟩,
      Continuous.subtype_mk (Continuous.prodMk a.toLRSHom.base.hom.continuous
        b.toLRSHom.base.hom.continuous) _⟩

omit [IsFiniteEtale q] in
/-- **The lift is over `B'` on carriers**, by `rfl`. -/
theorem baseChangeLiftBase_snd :
    b.toLRSHom.base = baseChangeLiftBase q f a b hab ≫ baseChangeSndBase q f := rfl

omit [IsFiniteEtale q] in
/-- **And over `E` on carriers**, by `rfl`. This is the half the universal property below cannot
get from the inverse-image uniqueness and has to have on the nose. -/
theorem baseChangeLiftBase_fst :
    a.toLRSHom.base = baseChangeLiftBase q f a b hab ≫ baseChangeFstBase q f := rfl

set_option backward.isDefEq.respectTransparency false in
/-- **The lift, as a morphism of locally ringed spaces**: the comparison morphism of `b` followed
by the functoriality of the inverse image at the carrier-level factorisation of `b`'s base map
through the second projection. -/
def baseChangeLiftLRS : Z.toLocallyRingedSpace ⟶ (baseChange q f).toLocallyRingedSpace :=
  LocallyRingedSpace.toInverseImage b.toLRSHom ≫
    LocallyRingedSpace.inverseImageMapOfEq (baseChangeSndBase q f) (baseChangeLiftBase q f a b hab)
      b.toLRSHom.base (baseChangeLiftBase_snd q f a b hab)

set_option backward.isDefEq.respectTransparency false in
/-- **The lift is over `B'`.** -/
theorem baseChangeLiftLRS_comp :
    baseChangeLiftLRS q f a b hab ≫ (baseChangeSnd q f).toLRSHom = b.toLRSHom := by
  rw [baseChangeLiftLRS, Category.assoc]
  exact (congrArg (fun m ↦ LocallyRingedSpace.toInverseImage b.toLRSHom ≫ m)
    (LocallyRingedSpace.inverseImageMapOfEq_comp (baseChangeSndBase q f)
      (baseChangeLiftBase q f a b hab) b.toLRSHom.base
      (baseChangeLiftBase_snd q f a b hab))).trans
    (LocallyRingedSpace.toInverseImage_comp b.toLRSHom)

set_option backward.isDefEq.respectTransparency false in
/-- **The morphism a commuting square induces into the fibre product.** Its `ℂ`-linearity is
`ComplexAnalytic.IsCLinearHom.of_comp` at the factorisation through `B'`, the same move the first
projection's linearity uses. -/
def baseChangeLift : Z ⟶ baseChange q f :=
  ⟨baseChangeLiftLRS q f a b hab,
    IsCLinearHom.of_comp (baseChangeLiftLRS_comp q f a b hab) b.isCLinear
      (baseChangeSnd q f).isCLinear⟩

/-- **The lift factors the second leg.** -/
theorem baseChangeLift_snd : baseChangeLift q f a b hab ≫ baseChangeSnd q f = b :=
  forgetToLocallyRingedSpace.map_injective (baseChangeLiftLRS_comp q f a b hab)

set_option backward.isDefEq.respectTransparency false in
/-- **The base map of the lift is the pair.** -/
@[simp]
theorem base_baseChangeLift :
    (baseChangeLift q f a b hab).toLRSHom.base = baseChangeLiftBase q f a b hab := by
  change (LocallyRingedSpace.toInverseImage b.toLRSHom).base ≫
    (LocallyRingedSpace.inverseImageMapOfEq (baseChangeSndBase q f) (baseChangeLiftBase q f a b hab)
      b.toLRSHom.base (baseChangeLiftBase_snd q f a b hab)).base = _
  rw [LocallyRingedSpace.inverseImageMapOfEq_base, LocallyRingedSpace.toInverseImage_base]
  exact Category.id_comp _

set_option backward.isDefEq.respectTransparency false in
/-- **The lift factors the first leg**, which is the half that needs the uniqueness.

Both sides are morphisms `Z ⟶ E`; `ComplexAnalytic.AnalyticSpace.inverseImageIsoOfIsLocalIso` is
a monomorphism, so it is enough to compare them in `q.base⁻¹B`, where
`AlgebraicGeometry.LocallyRingedSpace.inverseImage_hom_ext` applies. Its base hypothesis is
`ComplexAnalytic.AnalyticSpace.baseChangeLiftBase_fst`, which is `rfl`, and its hypothesis over
`B` is the two ways round the square. -/
theorem baseChangeLift_fst : baseChangeLift q f a b hab ≫ baseChangeFst q f = a := by
  refine forgetToLocallyRingedSpace.map_injective ?_
  refine (cancel_mono (inverseImageIsoOfIsLocalIso q).hom).mp ?_
  refine LocallyRingedSpace.inverseImage_hom_ext _ q.toLRSHom.base ?_ ?_
  · change ((baseChangeLift q f a b hab).toLRSHom.base ≫ (baseChangeFst q f).toLRSHom.base) ≫
      (inverseImageIsoOfIsLocalIso q).hom.base
      = a.toLRSHom.base ≫ (inverseImageIsoOfIsLocalIso q).hom.base
    rw [base_baseChangeLift, base_baseChangeFst, ← baseChangeLiftBase_fst]
  · have h1 : (inverseImageIsoOfIsLocalIso q).hom ≫
        LocallyRingedSpace.inverseImageHom B.toLocallyRingedSpace q.toLRSHom.base = q.toLRSHom :=
      LocallyRingedSpace.toInverseImage_comp q.toLRSHom
    rw [Category.assoc, Category.assoc, h1, Functor.map_comp, Category.assoc]
    change baseChangeLiftLRS q f a b hab ≫ baseChangeFstLRS q f ≫ q.toLRSHom
      = a.toLRSHom ≫ q.toLRSHom
    rw [baseChangeFstLRS_comp]
    change baseChangeLiftLRS q f a b hab ≫ (baseChangeSnd q f).toLRSHom ≫ f.toLRSHom
      = a.toLRSHom ≫ q.toLRSHom
    rw [← Category.assoc, baseChangeLiftLRS_comp]
    exact (congrArg Hom.toLRSHom hab).symm

set_option backward.isDefEq.respectTransparency false in
/-- **Two morphisms into the fibre product agreeing on both projections are equal.**

`AlgebraicGeometry.LocallyRingedSpace.inverseImage_hom_ext` again, and it asks for less than the
hypotheses give: the composite to `B'` is the second projection alone, and the two projections are
used only to pin the base map, where a point of `Function.Pullback` is determined by its two
components. -/
theorem baseChange_hom_ext {u v : Z ⟶ baseChange q f}
    (h1 : u ≫ baseChangeFst q f = v ≫ baseChangeFst q f)
    (h2 : u ≫ baseChangeSnd q f = v ≫ baseChangeSnd q f) : u = v := by
  refine forgetToLocallyRingedSpace.map_injective
    (LocallyRingedSpace.inverseImage_hom_ext _ (baseChangeSndBase q f) ?_ ?_)
  · have e1 : u.toLRSHom.base ≫ baseChangeFstBase q f
        = v.toLRSHom.base ≫ baseChangeFstBase q f := by
      rw [← base_baseChangeFst]
      exact congrArg (fun m : Z ⟶ E ↦ m.toLRSHom.base) h1
    have e2 : u.toLRSHom.base ≫ baseChangeSndBase q f
        = v.toLRSHom.base ≫ baseChangeSndBase q f := by
      rw [← base_baseChangeSnd]
      exact congrArg (fun m : Z ⟶ B' ↦ m.toLRSHom.base) h2
    ext z
    refine Subtype.ext (Prod.ext ?_ ?_)
    · exact congrArg (fun g : Z.toLocallyRingedSpace.toTopCat ⟶
        E.toLocallyRingedSpace.toTopCat ↦ g z) e1
    · exact congrArg (fun g : Z.toLocallyRingedSpace.toTopCat ⟶
        B'.toLocallyRingedSpace.toTopCat ↦ g z) e2
  · exact congrArg Hom.toLRSHom h2

/-- **The square is a pullback.** -/
theorem isPullback_baseChange :
    CategoryTheory.IsPullback (baseChangeFst q f) (baseChangeSnd q f) q f :=
  CategoryTheory.IsPullback.of_isLimit
    (Limits.PullbackCone.IsLimit.mk (baseChange_square q f)
      (fun s ↦ baseChangeLift q f s.fst s.snd s.condition)
      (fun s ↦ baseChangeLift_fst q f s.fst s.snd s.condition)
      (fun s ↦ baseChangeLift_snd q f s.fst s.snd s.condition)
      (fun s _ hm1 hm2 ↦ baseChange_hom_ext q f
        (hm1.trans (baseChangeLift_fst q f s.fst s.snd s.condition).symm)
        (hm2.trans (baseChangeLift_snd q f s.fst s.snd s.condition).symm)))

/-- **So the fibre product exists**, at every cospan one of whose legs is finite étale. An
instance, so that `CategoryTheory.Limits.pullback q f` elaborates.

**This docstring said *at every cospan one of whose legs is finite étale with Hausdorff source*
until 2026-09-14**, when the separation axiom came out of this file. -/
instance hasPullback_of_isFiniteEtale : Limits.HasPullback q f :=
  (isPullback_baseChange q f).hasPullback

/-- **And the base change of a finite étale morphism is finite étale**, in the spelling that
mentions `CategoryTheory.Limits.pullback` rather than
`ComplexAnalytic.AnalyticSpace.baseChangeSnd`.

The two differ by `CategoryTheory.IsPullback.isoPullback`, and finite étaleness crosses it by
`ComplexAnalytic.AnalyticSpace.isFiniteEtale_of_isIso` and
`ComplexAnalytic.AnalyticSpace.isFiniteEtale_comp`. -/
theorem isFiniteEtale_pullback_snd_of_isFiniteEtale :
    IsFiniteEtale (Limits.pullback.snd q f) := by
  haveI := isFiniteEtale_baseChangeSnd q f
  haveI := isFiniteEtale_of_isIso (isPullback_baseChange q f).isoPullback.inv
  rw [← (isPullback_baseChange q f).isoPullback_inv_snd]
  exact isFiniteEtale_comp _ _

end ComplexAnalytic.AnalyticSpace
