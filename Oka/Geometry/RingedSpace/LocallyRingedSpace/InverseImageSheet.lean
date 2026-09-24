/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Geometry.RingedSpace.LocallyRingedSpace.InverseImage
import Oka.Geometry.RingedSpace.OpenImmersion

/-!
# Over a sheet, the inverse image is the base

Let `p : E ⟶ Y` be a continuous map into the space underlying a locally ringed space, and let
`V` be an open of `E` on which `p` is an open embedding — a **sheet**. Then the inverse image
`p⁻¹Y` restricted to `V` is isomorphic, as a locally ringed space, to `Y` restricted to the open
`p '' V`:

    (p⁻¹Y)|V  ≅  Y|(p '' V)

This is what turns `AlgebraicGeometry.LocallyRingedSpace.inverseImage` — which for an arbitrary
continuous map is a sheafification with no computable sections — into something with **charts**,
and it is where a local-homeomorphism hypothesis first does any work.

There is no analytic content here, so this file is a candidate for upstreaming; it lives in the
`Oka/Geometry/` mirror of the Mathlib directory tree for that reason, as a proposed new file
beside `Oka/Geometry/RingedSpace/LocallyRingedSpace/InverseImage.lean`.

## The stalks do all the work, and the sheafification is never opened

The obvious route is to compute: over a sheet the presheaf inverse image is
`W ↦ 𝒪_Y(p '' W)` (`IsOpenMap.pullbackObjIso`), that presheaf is already a sheaf on the opens
below `V` because `p` is injective there, and so the sheafification does nothing. **That
computation is not needed and is not done here.** The inverse-image file already proves that
every stalk map of `AlgebraicGeometry.LocallyRingedSpace.inverseImageHom` is an isomorphism, and
Mathlib turns a stalkwise statement into a global one twice over:

* `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.of_stalk_iso` — a morphism whose base is
  an open embedding and whose stalk maps are isomorphisms is an open immersion;
* `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.to_iso` — an open immersion with
  epimorphic base is an isomorphism.

So the whole file is: compose to `Y`, observe the two hypotheses, and factor through the open.
Nothing below mentions `TopCat.Sheaf.pullback`, `CategoryTheory.toSheafify` or a section over an
open set.

## Why this file and not the inverse-image file

`Mathlib.Geometry.RingedSpace.OpenImmersion` is not among the inverse-image file's imports, and it
is what everything here rests on. Against `Mathlib/Geometry/RingedSpace/LocallyRingedSpace.lean`,
whose closure is **1688** Mathlib modules, the imports of this file cost **7** — but **6** of
those are the inverse-image file's own (the `Mathlib.Topology.Sheaves.Sheafify` chain), so the
cost of this file over its intended neighbour is exactly **1**,
`Mathlib.Geometry.RingedSpace.OpenImmersion`. Both measured with
`python3 scripts/import_cost.py --target …`.

**`Oka/Topology/IsLocalHomeomorph.lean` is deliberately not imported.** The statement that the
sheets cover belongs with the map and not with the ringed space, and pulling
`Mathlib.Topology.IsLocalHomeomorph` in here would raise this file's cost against the same
destination from **7** to **16** — the `OpenPartialHomeomorph` chain, nine modules, none of which
anything below uses. Split by destination, not by subject.

## Main definitions

- `AlgebraicGeometry.LocallyRingedSpace.sheetToBase`: the sheet, mapped to `Y`.
- `AlgebraicGeometry.LocallyRingedSpace.sheetImage`: the open of `Y` the sheet lies over.
- `AlgebraicGeometry.LocallyRingedSpace.sheetHom`: the comparison `(p⁻¹Y)|V ⟶ Y|(p '' V)`.

## Main results

- `AlgebraicGeometry.LocallyRingedSpace.coe_sheetImage`: **the open is `p '' V`**, which is what
  makes the statement the one it is meant to be rather than one about an abstract range.
- `AlgebraicGeometry.LocallyRingedSpace.isIso_sheetHom`: **the comparison is an isomorphism.**
- `AlgebraicGeometry.LocallyRingedSpace.sheetIso`: the same, packaged as an isomorphism of
  locally ringed spaces.

## What is not here

* **No local homeomorphism, and that is still the hypothesis this file has.** It is one open
  embedding, on one open. That the sheets of a local homeomorphism cover is
  `IsLocalHomeomorph.sSup_sheetOpens` in `Oka/Topology/IsLocalHomeomorph.lean`, which this file
  does not import. **Assembling the two into a statement about the whole of `E` is no longer
  absent**: it is `Oka/AnalyticSpace/CoveringSpace.lean`, which is under `Oka/AnalyticSpace/` and
  not here because what it assembles the sheets into is a complex analytic structure.
* **Nothing about sections.** No formula for `𝒪_{p⁻¹Y}(W)` is proved even over a sheet; what is
  proved is that the *space* over a sheet is the base over its image, which is strictly weaker
  than a formula and is all a chart needs.
* **No cocycle and no gluing.** Two sheets `V₀`, `V₁` meeting give two isomorphisms over
  `p '' (V₀ ∩ V₁)` and nothing here compares them. The identity that makes them fit is
  `Set.InjOn.image_inter`, `p '' (V ∩ A) ∩ p '' (V ∩ B) = p '' (V ∩ A ∩ B)`; the naive
  `p '' (V₀ ∩ V₁) = p '' V₀ ∩ p '' V₁` is **false** for a covering map — the connected double
  cover of the circle, covered by two arcs each longer than a half, has `p '' V₀ = p '' V₁` the
  whole circle while `p '' (V₀ ∩ V₁)` is two proper arcs — and nothing below uses it.
* **No ℂ-algebra structure and no analytic space.** The comparison being `ComplexAnalytic`-linear
  when `Y` carries such a structure is a statement about a different category, with a different
  upstream destination, and belongs in a file under `Oka/AnalyticSpace/`.
-/

open CategoryTheory TopologicalSpace Opposite TopCat Topology

universe u

namespace AlgebraicGeometry.LocallyRingedSpace

noncomputable section

variable (Y : LocallyRingedSpace.{u}) {E : TopCat.{u}} (p : E ⟶ Y.toTopCat) (V : Opens E)

/-- **The sheet over `V`, mapped to the base**: the inclusion of `V` into `p⁻¹Y` followed by the
projection `p⁻¹Y ⟶ Y`. -/
def sheetToBase : (Y.inverseImage p).restrict V.isOpenEmbedding ⟶ Y :=
  (Y.inverseImage p).ofRestrict V.isOpenEmbedding ≫ Y.inverseImageHom p

@[simp]
theorem base_sheetToBase (x : V) : (sheetToBase Y p V).base x = p (x : E) := rfl

/-- **Every stalk map of `AlgebraicGeometry.LocallyRingedSpace.sheetToBase` is an isomorphism.**

Both factors are: the inclusion of an open subspace by
`AlgebraicGeometry.LocallyRingedSpace.ofRestrict_stalkMap_isIso`, and the projection by
`AlgebraicGeometry.LocallyRingedSpace.isIso_stalkMap_inverseImageHom`. Neither uses anything of
`V`, which is why this instance carries no hypothesis on it. -/
instance isIso_stalkMap_sheetToBase
    (x : ((Y.inverseImage p).restrict V.isOpenEmbedding).toTopCat) :
    IsIso ((sheetToBase Y p V).stalkMap x) := by
  haveI h1 : IsIso ((Y.inverseImageHom p).stalkMap
      (((Y.inverseImage p).ofRestrict V.isOpenEmbedding).base x)) :=
    isIso_stalkMap_inverseImageHom Y p _
  haveI h2 : IsIso (((Y.inverseImage p).ofRestrict V.isOpenEmbedding).stalkMap x) := inferInstance
  rw [sheetToBase, stalkMap_comp]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h1 h2

variable (hV : IsOpenEmbedding fun x : V ↦ p x)

include hV in
/-- **The sheet hypothesis, read on the composite.** The base of
`AlgebraicGeometry.LocallyRingedSpace.sheetToBase` is `fun x : V ↦ p x` on the nose, so this is
`hV` and not a transport of it. -/
theorem isOpenEmbedding_base_sheetToBase : IsOpenEmbedding (sheetToBase Y p V).base := hV

/-- **The open of `Y` that the sheet lies over.**

Defined as the range of `AlgebraicGeometry.LocallyRingedSpace.sheetToBase` rather than as
`p '' V`, so that the containment
`AlgebraicGeometry.LocallyRingedSpace.sheetHom` needs is `subset_rfl`;
`AlgebraicGeometry.LocallyRingedSpace.coe_sheetImage` says the two sets are equal. -/
def sheetImage : Opens Y.toTopCat :=
  ⟨Set.range (sheetToBase Y p V).base, (isOpenEmbedding_base_sheetToBase Y p V hV).isOpen_range⟩

/-- **The open the sheet lies over is `p '' V`.** -/
theorem coe_sheetImage : (sheetImage Y p V hV : Set Y.toTopCat) = p '' (V : Set E) :=
  (Set.image_eq_range _ _).symm

include hV in
/-- **The sheet is an open immersion into the base**: its base is an open embedding by hypothesis
and its stalk maps are isomorphisms by
`AlgebraicGeometry.LocallyRingedSpace.isIso_stalkMap_sheetToBase`. -/
theorem isOpenImmersion_sheetToBase : IsOpenImmersion (sheetToBase Y p V) :=
  IsOpenImmersion.of_stalk_iso _ (isOpenEmbedding_base_sheetToBase Y p V hV)

/-- **The comparison morphism `(p⁻¹Y)|V ⟶ Y|(p '' V)`**, obtained by factoring
`AlgebraicGeometry.LocallyRingedSpace.sheetToBase` through the open it lands in. -/
def sheetHom : (Y.inverseImage p).restrict V.isOpenEmbedding ⟶
    Y.restrict (sheetImage Y p V hV).isOpenEmbedding :=
  liftRestrict (sheetToBase Y p V) (sheetImage Y p V hV) subset_rfl

@[simp]
theorem base_ofRestrict_base_sheetHom
    (x : ((Y.inverseImage p).restrict V.isOpenEmbedding).toTopCat) :
    (Y.ofRestrict (sheetImage Y p V hV).isOpenEmbedding).base ((sheetHom Y p V hV).base x) =
      (sheetToBase Y p V).base x :=
  base_ofRestrict_base_liftRestrict _ _ _ x

instance isIso_stalkMap_sheetHom
    (x : ((Y.inverseImage p).restrict V.isOpenEmbedding).toTopCat) :
    IsIso ((sheetHom Y p V hV).stalkMap x) :=
  isIso_stalkMap_liftRestrict _ _ _ x

include hV in
/-- **The base of the comparison is an open embedding.**

Composed with the inclusion of `p '' V` it is the base of
`AlgebraicGeometry.LocallyRingedSpace.sheetToBase`, which is one by hypothesis, and
`Topology.IsOpenEmbedding.of_comp` cancels the inclusion.

**The substitution is `▸` and not `rw`, and that is forced.** The two sides are the same function
and `rw` refuses the rewrite, reporting that *"the target expression is not type-correct under the
`instances` transparency level"* — the `Full error:` block shows `V.inclusion'` wanted at
`… ⟶ (Y.inverseImage p).toTopCat` and supplied at `… ⟶ E`, which are equal by `rfl` and not at
that transparency. `Oka/Geometry/RingedSpace/OpenImmersion.lean` records the same seam for
`AlgebraicGeometry.LocallyRingedSpace.liftRestrict`. Nothing is transported: `IsOpenEmbedding` is
a `Prop` and the substitution is along a `funext`. -/
theorem isOpenEmbedding_base_sheetHom : IsOpenEmbedding (sheetHom Y p V hV).base := by
  refine IsOpenEmbedding.of_comp _ (sheetImage Y p V hV).isOpenEmbedding ?_
  have h : ⇑(ConcreteCategory.hom (sheetImage Y p V hV).inclusion') ∘
        ⇑(ConcreteCategory.hom (sheetHom Y p V hV).base) =
      ⇑(ConcreteCategory.hom (sheetToBase Y p V).base) :=
    funext (base_ofRestrict_base_sheetHom Y p V hV)
  exact h ▸ isOpenEmbedding_base_sheetToBase Y p V hV

include hV in
/-- **The base of the comparison is surjective**: the target open is by definition the range of
the map the comparison factors. -/
theorem surjective_base_sheetHom : Function.Surjective (sheetHom Y p V hV).base := by
  rintro ⟨y, x, hx⟩
  exact ⟨x, Subtype.ext ((base_ofRestrict_base_sheetHom Y p V hV x).trans hx)⟩

include hV in
theorem epi_base_sheetHom : Epi (sheetHom Y p V hV).base :=
  (TopCat.epi_iff_surjective _).2 (surjective_base_sheetHom Y p V hV)

include hV in
/-- **The comparison is an isomorphism.**

`AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.of_stalk_iso` makes it an open immersion —
its base is an open embedding and its stalk maps are isomorphisms — and
`AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.to_iso` upgrades an open immersion with
epimorphic base to an isomorphism. -/
theorem isIso_sheetHom : IsIso (sheetHom Y p V hV) :=
  haveI : IsOpenImmersion (sheetHom Y p V hV) :=
    IsOpenImmersion.of_stalk_iso _ (isOpenEmbedding_base_sheetHom Y p V hV)
  haveI := epi_base_sheetHom Y p V hV
  IsOpenImmersion.to_iso _

/-- **Over a sheet, the inverse image is the base**: `(p⁻¹Y)|V ≅ Y|(p '' V)`. -/
def sheetIso : (Y.inverseImage p).restrict V.isOpenEmbedding ≅
    Y.restrict (sheetImage Y p V hV).isOpenEmbedding :=
  haveI := isIso_sheetHom Y p V hV
  asIso (sheetHom Y p V hV)

@[simp]
theorem sheetIso_hom : (sheetIso Y p V hV).hom = sheetHom Y p V hV := rfl

end

end AlgebraicGeometry.LocallyRingedSpace
