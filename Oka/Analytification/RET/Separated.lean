/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.Hausdorff
import Oka.Analytification.RET.ClosedPoints

/-!
# Analytifications of affine morphisms are separated

The analytification of an affine scheme of finite type over `ℂ` is Hausdorff, since it is
isomorphic to the common zero locus of finitely many polynomials in some `ℂ^n`. Consequently the
analytification of an affine morphism `f : Y ⟶ X` (for example a finite morphism) is a separated
map on points: two points of `Y^an` over the same point of `X^an` lie in the analytification of
`f⁻¹ U` for an affine open `U` of `X`, which is Hausdorff and open in `Y^an`.

## Main results

- `ComplexAnalytic.t2Space_analytification_of_isAffine`: `T^an` is Hausdorff for `T` affine.
- `ComplexAnalytic.isSeparatedMap_analytification_map`: `f^an` is a separated map for `f`
  affine.
-/

open CategoryTheory AlgebraicGeometry Topology

universe u

namespace ComplexAnalytic

open AnalyticSpace

/-- **The analytification of an affine scheme of finite type over `ℂ` is Hausdorff.** -/
theorem t2Space_analytification_of_isAffine (T : SchemeLFTℂ.{u}) [IsAffine T.obj.left] :
    T2Space (analytification.obj T) := by
  obtain ⟨n, k, g, ⟨e⟩⟩ := SchemeLFTℂ.exists_iso_specPresentation T
  haveI : T2Space (forgetToLocallyRingedSpace.obj (AnalyticSpace.analytification g)) :=
    t2Space_analytification g
  exact (LocallyRingedSpace.homeoOfIso (forgetToLocallyRingedSpace.mapIso
    ((analytification.mapIso e).symm ≪≫ analytificationSpecIso g))).isEmbedding.t2Space

/-- **The analytification of an affine morphism is a separated map on points.** -/
theorem isSeparatedMap_analytification_map {Y X : SchemeLFTℂ.{u}} (f : Y ⟶ X)
    [IsAffineHom f.hom.left] :
    IsSeparatedMap (analytification.map f).toLRSHom.base := by
  intro y₁ y₂ hy hne
  obtain ⟨U, hU⟩ := exists_affineOpens_mem X.obj.left
    ((analytificationπ X).left.base ((analytification.map f).toLRSHom.base y₁))
  let V : Y.obj.left.Opens := f.hom.left ⁻¹ᵁ U.1
  haveI : IsAffine (Y.restrict V).obj.left := IsAffineHom.isAffine_preimage U.1 U.2
  haveI := t2Space_analytification_of_isAffine (Y.restrict V)
  let ι := (analytification.map (Y.restrictι V)).toLRSHom.base
  have hι : IsOpenEmbedding ι := isOpenEmbedding_analytification_map_restrictι Y V
  have hmem : ∀ y, (analytification.map f).toLRSHom.base y =
      (analytification.map f).toLRSHom.base y₁ → y ∈ Set.range ι := by
    intro y hy'
    rw [range_analytification_map_restrictι]
    change f.hom.left.base ((analytificationπ Y).left.base y) ∈ U.1
    rw [← analytificationπ_base_map_apply, hy']
    exact hU
  obtain ⟨w₁, rfl⟩ := hmem y₁ rfl
  obtain ⟨w₂, rfl⟩ := hmem y₂ hy.symm
  obtain ⟨O₁, O₂, hO₁, hO₂, hw₁, hw₂, hO⟩ :=
    t2_separation (fun h ↦ hne (congrArg ι h))
  exact ⟨ι '' O₁, ι '' O₂, hι.isOpenMap _ hO₁, hι.isOpenMap _ hO₂, ⟨w₁, hw₁, rfl⟩,
    ⟨w₂, hw₂, rfl⟩, (Set.disjoint_image_iff hι.injective).2 hO⟩

end ComplexAnalytic
