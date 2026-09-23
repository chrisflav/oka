/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.GAGA.CohomologyComparison
import Oka.AnalyticSpace.CohomologyModule

/-!
# The GAGA comparison map is `ℂ`-linear

A scheme `X` locally of finite type over `ℂ` carries the `ℂ`-algebra structure
`ComplexAnalytic.SchemeLFTℂ.algebraMap X : ℂ →+* Γ(X, 𝒪_X)` corresponding to its structure
morphism `X ⟶ Spec ℂ` (`ComplexAnalytic.SchemeLFTℂ.toSpecOfAlgMap_uliftAlgMap`). Through it the
cohomology `Hᵠ(X, F)` of a sheaf of `𝒪_X`-modules is a `ℂ`-vector space
(`ComplexAnalytic.SchemeLFTℂ.moduleH`), and since `π : X^an ⟶ X` is a morphism over `Spec ℂ`
(`ComplexAnalytic.isCLinearHom_analytificationπLRS`), the GAGA comparison map
`Hᵠ(X, F) → Hᵠ(X^an, F^an)` is `ℂ`-linear (`ComplexAnalytic.gagaMap_smul`,
`ComplexAnalytic.gagaMapₗ`).
-/

open CategoryTheory AlgebraicGeometry Opposite LocallyRingedSpace

universe u

noncomputable section

namespace ComplexAnalytic

namespace SchemeLFTℂ

variable (X : SchemeLFTℂ.{u})

/-- The `ULift ℂ`-algebra structure of a scheme over `Spec ℂ`: the ring map
`ULift ℂ →+* Γ(X, 𝒪_X)` corresponding to the structure morphism `X ⟶ Spec ℂ`. -/
def algebraMapULift : ULift.{u} ℂ →+* X.obj.left.toLocallyRingedSpace.presheaf.obj (op ⊤) :=
  ((ΓSpec.locallyRingedSpaceAdjunction.homEquiv X.obj.left.toLocallyRingedSpace
    (op (CommRingCat.of (ULift.{u} ℂ)))).symm X.obj.hom.toLRSHom).unop.hom

/-- The `ℂ`-algebra structure of a scheme over `Spec ℂ`. -/
def algebraMap : ℂ →+* X.obj.left.toLocallyRingedSpace.presheaf.obj (op ⊤) :=
  (algebraMapULift X).comp ULift.ringEquiv.symm.toRingHom

lemma uliftAlgMap_algebraMap : uliftAlgMap (algebraMap X) = algebraMapULift X := by
  ext c
  rfl

/-- The structure morphism `X ⟶ Spec ℂ` is the one given by `algebraMap X`. -/
lemma toSpecOfAlgMap_uliftAlgMap :
    X.obj.left.toLocallyRingedSpace.toSpecOfAlgMap (uliftAlgMap (algebraMap X)) =
      X.obj.hom.toLRSHom := by
  rw [uliftAlgMap_algebraMap, algebraMapULift, toSpecOfAlgMap_eq_homEquiv]
  exact (ΓSpec.locallyRingedSpaceAdjunction.homEquiv _ _).apply_symm_apply _

/-- **The cohomology of a sheaf of modules on a scheme over `ℂ` is a `ℂ`-vector space.** -/
instance moduleH (F : SheafOfModules.{u} X.obj.left.toLocallyRingedSpace.ringSheaf) (q : ℕ) :
    Module ℂ (H F q) :=
  Module.compHom _ (algebraMap X)

variable {X}

lemma smul_H_def {F : SheafOfModules.{u} X.obj.left.toLocallyRingedSpace.ringSheaf} {q : ℕ}
    (c : ℂ) (x : H F q) : c • x = algebraMap X c • x :=
  rfl

end SchemeLFTℂ

variable {X : SchemeLFTℂ.{u}}

/-- The comparison morphism `π : X^an ⟶ X` is `ℂ`-linear. -/
theorem isCLinearHom_analytificationπLRS :
    IsCLinearHom (analytificationπLRS X) (analytification.obj X).algebraMap
      (SchemeLFTℂ.algebraMap X) := by
  have hw : analytificationπLRS X ≫ X.obj.hom.toLRSHom =
      (analytification.obj X).toSpecℂ := Over.w (analytificationπ X)
  have h₁ := comp_toSpecOfAlgMap (analytificationπLRS X) (uliftAlgMap (SchemeLFTℂ.algebraMap X))
  have h := toSpecOfAlgMap_injective _ (h₁.symm.trans
    ((congrArg (analytificationπLRS X ≫ ·) (SchemeLFTℂ.toSpecOfAlgMap_uliftAlgMap X)).trans hw))
  intro c
  exact congrArg (fun γ : ULift.{u} ℂ →+* _ ↦ γ (ULift.up c)) h

/-- **The GAGA comparison map is `ℂ`-linear.** -/
theorem gagaMap_smul (F : SheafOfModules.{u} X.obj.left.toLocallyRingedSpace.ringSheaf) {q : ℕ}
    (c : ℂ) (x : H F q) : gagaMap X F q (c • x) = c • gagaMap X F q x :=
  isCLinearHom_analytificationπLRS.cohomologyMap_smul F c x

/-- The GAGA comparison map `Hᵠ(X, F) → Hᵠ(X^an, F^an)` as a `ℂ`-linear map. -/
def gagaMapₗ (F : SheafOfModules.{u} X.obj.left.toLocallyRingedSpace.ringSheaf) (q : ℕ) :
    H F q →ₗ[ℂ] H ((analytificationModules X).obj F) q where
  toFun := gagaMap X F q
  map_add' := map_add _
  map_smul' := gagaMap_smul F

@[simp]
lemma gagaMapₗ_apply (F : SheafOfModules.{u} X.obj.left.toLocallyRingedSpace.ringSheaf) {q : ℕ}
    (x : H F q) : gagaMapₗ F q x = gagaMap X F q x :=
  rfl

end ComplexAnalytic
