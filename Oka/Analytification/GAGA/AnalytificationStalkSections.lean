/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.AlgebraicGeometry.Modules.QuasicoherentSections
import Oka.Analytification.GAGA.SheafAnalytification
import Oka.Geometry.RingedSpace.LocallyRingedSpace.ModulesClosedEmbedding

/-!
# Stalks of analytified sheaves in terms of sections over affine opens

Let `F` be a quasi-coherent sheaf on a scheme `X` and `U ⊆ X` an affine open. For `x ∈ U` the germ
map `Γ(F, U) → F_x` is the localisation at the prime ideal of `x`
(`AlgebraicGeometry.Scheme.Modules.isLocalizedModule_germLinearMap`). If `X` is locally of finite
type over `ℂ` and `π : X^an ⟶ X` is the comparison morphism, then for `x ∈ π⁻¹ U` the map

  `𝒪_{X^an,x} ⊗[Γ(X, U)] Γ(F, U) → (F^an)_x`, `s ⊗ m ↦ s • (m^an)_x`,

is bijective (`ComplexAnalytic.isBaseChange_analytificationGermLinearMap`), where `m^an` is the
image of `m` under the unit `F ⟶ π_* F^an`. This combines the localisation statement with the
description `(F^an)_x ≅ 𝒪_{X^an,x} ⊗[𝒪_{X,π x}] F_{π x}` of the stalks of a pullback.

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.germLinearMap F x`: the germ map `Γ(F, U) → F_x`.
- `ComplexAnalytic.analytificationGermLinearMap F x`: the map `Γ(F, U) → (F^an)_x`,
  `m ↦ (m^an)_x`.
-/

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

universe u

namespace AlgebraicGeometry

noncomputable section

variable {X : Scheme.{u}} (F : X.Modules) {U : X.Opens} (x : U)

/-- The stalk `F_x`, as a module over `Γ(X, U)`. -/
instance Scheme.Modules.stalkModuleSections :
    Module Γ(X, U) ((X.toLocallyRingedSpace.stalkFunctor x.1).obj F) :=
  Module.compHom _ (algebraMap Γ(X, U) (X.presheaf.stalk x.1))

instance Scheme.Modules.isScalarTower_stalkModuleSections :
    IsScalarTower Γ(X, U) (X.presheaf.stalk x.1)
      ((X.toLocallyRingedSpace.stalkFunctor x.1).obj F) :=
  ⟨fun r s m ↦ by
    change (algebraMap Γ(X, U) (X.presheaf.stalk x.1) r * s) • m = _
    rw [mul_smul]
    rfl⟩

lemma Scheme.Modules.germ_smul' (r : Γ(X, U)) (s : Γ(F, U)) :
    (show (X.toLocallyRingedSpace.stalkFunctor x.1).obj F from
      TopCat.Presheaf.germ F.val.presheaf U x.1 x.2 (r • s)) =
      r • (show (X.toLocallyRingedSpace.stalkFunctor x.1).obj F from
        TopCat.Presheaf.germ F.val.presheaf U x.1 x.2 s) :=
  PresheafOfModules.germ_smul F.val x.1 U x.2 r s

/-- The germ at `x` of sections over `U`, as a `Γ(X, U)`-linear map. -/
def Scheme.Modules.germLinearMap :
    Γ(F, U) →ₗ[Γ(X, U)] (X.toLocallyRingedSpace.stalkFunctor x.1).obj F where
  toFun s := TopCat.Presheaf.germ F.val.presheaf U x.1 x.2 s
  map_add' s t := map_add _ s t
  map_smul' r s := Scheme.Modules.germ_smul' F x r s

section Localization

variable (hU : IsAffineOpen U)

include hU in
lemma IsAffineOpen.mem_primeCompl_primeIdealOf_iff (g : Γ(X, U)) :
    g ∈ (hU.primeIdealOf x).asIdeal.primeCompl ↔ x.1 ∈ X.basicOpen g := by
  haveI := hU.isLocalization_stalk x
  rw [← IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk x.1), X.mem_basicOpen' g x]
  rfl

variable [F.IsQuasicoherent]

include hU in
theorem Scheme.Modules.isLocalizedModule_germLinearMap :
    IsLocalizedModule (hU.primeIdealOf x).asIdeal.primeCompl
      (Scheme.Modules.germLinearMap F x) where
  map_units g := by
    haveI := hU.isLocalization_stalk x
    obtain ⟨v, hv⟩ := IsLocalization.map_units (X.presheaf.stalk x.1) g
    refine (Module.End.isUnit_iff _).2
      ⟨fun m m' h ↦ ?_, fun m ↦ ⟨(↑v⁻¹ : X.presheaf.stalk x.1) • m, ?_⟩⟩
    · have h' : (algebraMap Γ(X, U) (X.presheaf.stalk x.1) g) • m =
          (algebraMap Γ(X, U) (X.presheaf.stalk x.1) g) • m' := h
      rw [← hv] at h'
      have := congrArg (fun t ↦ (↑v⁻¹ : X.presheaf.stalk x.1) • t) h'
      simpa only [smul_smul, Units.inv_mul, one_smul] using this
    · change (algebraMap Γ(X, U) (X.presheaf.stalk x.1) g) • ((↑v⁻¹ : X.presheaf.stalk x.1) • m) = m
      rw [← hv, smul_smul, Units.mul_inv, one_smul]
  surj m := by
    obtain ⟨V, hxV, t, rfl⟩ := TopCat.Presheaf.exists_germ_eq F.val.presheaf m
    obtain ⟨f, hfV, hxf⟩ := hU.exists_basicOpen_le (V := V) ⟨x.1, hxV⟩ x.2
    obtain ⟨k, s, hs⟩ := hU.exists_restrictOpen_eq_pow_smul F f
      (TopCat.Presheaf.restrictOpen (F := F.presheaf) t _ hfV)
    have hf : f ∈ (hU.primeIdealOf x).asIdeal.primeCompl :=
      (hU.mem_primeCompl_primeIdealOf_iff x f).2 hxf
    refine ⟨⟨s, ⟨f ^ k, pow_mem hf k⟩⟩, ?_⟩
    have h1 := congrArg (TopCat.Presheaf.germ F.val.presheaf (X.basicOpen f) x.1 hxf) hs
    change (f ^ k) • (show (X.toLocallyRingedSpace.stalkFunctor x.1).obj F from
      TopCat.Presheaf.germ F.val.presheaf V x.1 hxV t) =
      TopCat.Presheaf.germ F.val.presheaf U x.1 x.2 s
    rw [← TopCat.Presheaf.germ_res_apply F.val.presheaf (homOfLE (X.basicOpen_le f)) x.1 hxf s]
    change _ = TopCat.Presheaf.germ F.val.presheaf (X.basicOpen f) x.1 hxf
      (TopCat.Presheaf.restrictOpen (F := F.presheaf) s _ (X.basicOpen_le f))
    rw [hs]
    erw [PresheafOfModules.germ_smul F.val x.1 (X.basicOpen f) hxf]
    erw [map_pow, TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]
    change (algebraMap Γ(X, U) (X.presheaf.stalk x.1) (f ^ k)) •
      (show (X.toLocallyRingedSpace.stalkFunctor x.1).obj F from
        TopCat.Presheaf.germ F.val.presheaf V x.1 hxV t) = _
    rw [map_pow]
    rfl
  exists_of_eq {s₁ s₂} h := by
    obtain ⟨W, hxW, i₁, i₂, hW⟩ := TopCat.Presheaf.germ_eq F.val.presheaf x.1 x.2 x.2 s₁ s₂ h
    obtain ⟨f, hfW, hxf⟩ := hU.exists_basicOpen_le (V := W) ⟨x.1, hxW⟩ x.2
    have hf : f ∈ (hU.primeIdealOf x).asIdeal.primeCompl :=
      (hU.mem_primeCompl_primeIdealOf_iff x f).2 hxf
    obtain ⟨k, hk⟩ := hU.exists_pow_smul_eq_zero F f (s₁ - s₂) (by
      rw [Scheme.Modules.mres_sub, ← Scheme.Modules.mres_res F i₁.le hfW,
        ← Scheme.Modules.mres_res F i₁.le hfW]
      have hW' : TopCat.Presheaf.restrictOpen (F := F.presheaf) s₁ W i₁.le =
          TopCat.Presheaf.restrictOpen (F := F.presheaf) s₂ W i₁.le := by
        rw [Subsingleton.elim i₁ i₂] at hW
        exact hW
      rw [hW', sub_self])
    refine ⟨⟨f ^ k, pow_mem hf k⟩, ?_⟩
    rw [Submonoid.smul_def, Submonoid.smul_def, ← sub_eq_zero, ← smul_sub]
    exact hk

end Localization

end

end AlgebraicGeometry

namespace ComplexAnalytic

open AnalyticSpace

noncomputable section

variable {X : SchemeLFTℂ.{u}} {U : X.obj.left.Opens}

/-- The point `π x` of `U`, for `x ∈ π⁻¹ U`. -/
def analytificationPreimage.toOpen (x : analytificationPreimage X U) : U :=
  ⟨(analytificationπLRS X).base x.1, x.2⟩

/-- For `x ∈ π⁻¹ U`, the stalk `𝒪_{X^an,x}` is an algebra over `Γ(X, U)`. -/
instance analytificationStalkSectionsAlgebra (x : analytificationPreimage X U) :
    Algebra Γ(X.obj.left, U) ((analytification.obj X).presheaf.stalk x.1) :=
  (((analytificationπLRS X).stalkMap x.1).hom.comp
    (X.obj.left.presheaf.germ U _ x.2).hom).toAlgebra

variable (F : X.obj.left.Modules) (x : analytificationPreimage X U)

/-- The stalk `(F^an)_x` at `x ∈ π⁻¹ U`, as a module over `Γ(X, U)`. -/
instance analytificationModulesStalkModule :
    Module Γ(X.obj.left, U) (((analytification.obj X).toLocallyRingedSpace.stalkFunctor x.1).obj
      ((analytificationModules X).obj F)) :=
  Module.compHom _ (algebraMap Γ(X.obj.left, U) ((analytification.obj X).presheaf.stalk x.1))

instance isScalarTower_analytificationModulesStalkModule :
    IsScalarTower Γ(X.obj.left, U) ((analytification.obj X).presheaf.stalk x.1)
      (((analytification.obj X).toLocallyRingedSpace.stalkFunctor x.1).obj
        ((analytificationModules X).obj F)) :=
  ⟨fun r s m ↦ by
    change (algebraMap Γ(X.obj.left, U) ((analytification.obj X).presheaf.stalk x.1) r * s) • m = _
    rw [mul_smul]
    rfl⟩

/-- The image of a section `m ∈ Γ(F, U)` in `F^an` over `π⁻¹ U`. -/
def analytificationSection (m : Γ(F, U)) :
    ((analytificationModules X).obj F).val.obj (op (analytificationPreimage X U)) :=
  ((analytificationModulesAdj X).unit.app F).val.app (op U) m

/-- The germ at `x ∈ π⁻¹ U` of the image in `F^an` of a section over `U`, as a `Γ(X, U)`-linear
map `Γ(F, U) → (F^an)_x`. -/
def analytificationGermLinearMap :
    Γ(F, U) →ₗ[Γ(X.obj.left, U)]
      (((analytification.obj X).toLocallyRingedSpace.stalkFunctor x.1).obj
        ((analytificationModules X).obj F)) where
  toFun m := TopCat.Presheaf.germ ((analytificationModules X).obj F).val.presheaf
    (analytificationPreimage X U) x.1 x.2 (analytificationSection F m)
  map_add' m m' := by
    simp only [analytificationSection]
    erw [map_add, map_add]
    rfl
  map_smul' r m := by
    simp only [analytificationSection]
    erw [(((analytificationModulesAdj X).unit.app F).val.app (op U)).hom.map_smul r m]
    erw [PresheafOfModules.germ_smul ((analytificationModules X).obj F).val x.1
      (analytificationPreimage X U) x.2]
    change _ = ((analytificationπLRS X).stalkMap x.1 (X.obj.left.presheaf.germ U _ x.2 r)) •
      (show ((analytification.obj X).toLocallyRingedSpace.stalkFunctor x.1).obj
        ((analytificationModules X).obj F) from TopCat.Presheaf.germ
          ((analytificationModules X).obj F).val.presheaf (analytificationPreimage X U) x.1 x.2
            (analytificationSection F m))
    erw [LocallyRingedSpace.stalkMap_germ_apply]
    rfl

lemma pullbackModulesStalkIso_hom_analytificationGermLinearMap (m : Γ(F, U)) :
    ((analytificationπLRS X).pullbackModulesStalkIso x.1).hom.app F
      (analytificationGermLinearMap F x m) =
    (ModuleCat.extendRestrictScalarsAdj ((analytificationπLRS X).stalkMap x.1).hom).unit.app
      ((X.obj.left.toLocallyRingedSpace.stalkFunctor
        (analytificationPreimage.toOpen x).1).obj F)
      (Scheme.Modules.germLinearMap F (analytificationPreimage.toOpen x) m) :=
  LocallyRingedSpace.Hom.pullbackModulesStalkIso_hom_app_germ_unit _ F U x.1 x.2 m

variable {F} in
/-- **The stalks of the analytification of a quasi-coherent sheaf**: for an affine open `U ⊆ X`
and `x ∈ π⁻¹ U`, the map `𝒪_{X^an,x} ⊗[Γ(X, U)] Γ(F, U) → (F^an)_x`, `s ⊗ m ↦ s • (m^an)_x`, is
bijective. -/
theorem isBaseChange_analytificationGermLinearMap (hU : IsAffineOpen U) [F.IsQuasicoherent] :
    IsBaseChange ((analytification.obj X).presheaf.stalk x.1)
      (analytificationGermLinearMap F x) := by
  let y := analytificationPreimage.toOpen x
  letI : Algebra (X.obj.left.presheaf.stalk y.1) ((analytification.obj X).presheaf.stalk x.1) :=
    ((analytificationπLRS X).stalkMap x.1).hom.toAlgebra
  haveI : IsScalarTower Γ(X.obj.left, U) (X.obj.left.presheaf.stalk y.1)
      ((analytification.obj X).presheaf.stalk x.1) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI := hU.isLocalization_stalk y
  haveI := Scheme.Modules.isLocalizedModule_germLinearMap F y hU
  have hγ : IsBaseChange (X.obj.left.presheaf.stalk y.1) (Scheme.Modules.germLinearMap F y) :=
    IsLocalizedModule.isBaseChange (hU.primeIdealOf y).asIdeal.primeCompl _ _
  have hu := TensorProduct.isBaseChange (X.obj.left.presheaf.stalk y.1)
    ((X.obj.left.toLocallyRingedSpace.stalkFunctor y.1).obj F)
    ((analytification.obj X).presheaf.stalk x.1)
  refine IsBaseChange.of_equiv ((hγ.comp hu).equiv.trans
    (((analytificationπLRS X).pullbackModulesStalkIso x.1).app F).symm.toLinearEquiv) fun m ↦ ?_
  rw [LinearEquiv.trans_apply, IsBaseChange.equiv_tmul, one_smul]
  change (((analytificationπLRS X).pullbackModulesStalkIso x.1).app F).inv
    ((ModuleCat.extendRestrictScalarsAdj ((analytificationπLRS X).stalkMap x.1).hom).unit.app
      ((X.obj.left.toLocallyRingedSpace.stalkFunctor
        (analytificationPreimage.toOpen x).1).obj F)
      (Scheme.Modules.germLinearMap F (analytificationPreimage.toOpen x) m)) = _
  rw [← pullbackModulesStalkIso_hom_analytificationGermLinearMap]
  exact Iso.hom_inv_id_apply _ _

end

end ComplexAnalytic
