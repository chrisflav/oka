/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.ES.CapExtension.ProjPoly

/-!
# Local conditions for twists and sections of twists of free sheaves

If two sheaves of modules have isomorphic sections over the opens inside `V`, compatibly with
restriction and scalars, then the local conditions for coherence at the points of `V` pass from
one to the other (`AlgebraicGeometry.LocallyRingedSpace.localConditions_of_iso`). In particular
the twists `𝒞(n)` of the sheaf of the cap are coherent over `U × ℙ¹` if `𝒜` satisfies the local
conditions for coherence over `U`
(`ComplexAnalytic.Cap.AnnulusDecomposition.isCoherent_restrictModules_twistMod_capModule`).

A section of `𝒪(e)^I` over `V × ℙ¹` is in the chart `w` a tuple of polynomials of degree `≤ e`
in `w` (`ComplexAnalytic.Cap.freeF0_eq_sum_lagrange`).
-/

open CategoryTheory Opposite Topology TopologicalSpace Set Filter Metric

universe u

namespace AlgebraicGeometry.LocallyRingedSpace

variable {X : LocallyRingedSpace.{u}} (V : Opens X.toPresheafedSpace)
  {M N : SheafOfModules.{u} X.ringSheaf}
  (e : ∀ O : Opens X.toPresheafedSpace, O ≤ V → M.val.obj (op O) ≃+ N.val.obj (op O))
  (he_res : ∀ (O₁ O₂ : Opens X.toPresheafedSpace) (h : O₁ ≤ O₂) (h₂ : O₂ ≤ V)
    (s : M.val.obj (op O₂)), e O₁ (h.trans h₂) (sectRes M h s) = sectRes N h (e O₂ h₂ s))
  (he_smul : ∀ (O : Opens X.toPresheafedSpace) (hO : O ≤ V) (r : X.presheaf.obj (op O))
    (s : M.val.obj (op O)), e O hO (r • s) = r • e O hO s)

lemma functor_obj_le (O : Opens (X.restrict V.isOpenEmbedding).toPresheafedSpace) :
    V.isOpenEmbedding.isOpenMap.functor.obj O ≤ V := by
  rintro _ ⟨y, -, rfl⟩
  exact y.2

/-- The chart identifying `M` with the restriction of `N` to `V`. -/
noncomputable def isoChart : ModuleChart M ((restrictOverEquiv X V).functor.obj (N.over V)) where
  g := (X.ofRestrict V.isOpenEmbedding).base
  isOpenEmbedding := V.isOpenEmbedding
  ψ _ := RingHom.id _
  bijective_ψ _ := Function.bijective_id
  ψ_res _ _ := rfl
  φ O := ((e _ (functor_obj_le V O)).trans (restrictSectionsEquiv V N O).symm).toAddMonoidHom
  bijective_φ O := ((e _ (functor_obj_le V O)).trans (restrictSectionsEquiv V N O).symm).bijective
  φ_res {_ O₂} _ s := he_res _ _ _ (functor_obj_le V O₂) s
  φ_smul O r s := he_smul _ (functor_obj_le V O) r s

include he_res he_smul in
/-- **Local conditions transfer along isomorphisms of sections over the opens inside `V`.** -/
theorem localConditions_of_iso {x : X} (hx : x ∈ V)
    (hN : IsLocallyFinitelyGeneratedModuleAt N x ∧ HasLocalModuleRelationsAt N x) :
    IsLocallyFinitelyGeneratedModuleAt M x ∧ HasLocalModuleRelationsAt M x := by
  have h₁ := (restrictModuleChart V N).isLocallyFinitelyGeneratedModuleAt_of
    (z := ⟨x, hx⟩) hN.1
  have h₂ := (restrictModuleChart V N).hasLocalModuleRelationsAt_of (z := ⟨x, hx⟩) hN.2
  exact ⟨(isoChart V e he_res he_smul).isLocallyFinitelyGeneratedModuleAt h₁,
    (isoChart V e he_res he_smul).hasLocalModuleRelationsAt h₂⟩

end AlgebraicGeometry.LocallyRingedSpace

namespace ComplexAnalytic.Cap.AnnulusDecomposition

open AnalyticSpace BoundedSections relProjectiveSpaceAn relProjectiveLine
open AlgebraicGeometry AlgebraicGeometry.LocallyRingedSpace

noncomputable section

variable {m : ℕ}

/-- **Local conditions for the twists** of a sheaf of modules on `P^an`. -/
theorem localConditions_twistMod
    {M : SheafOfModules.{u} (relProjectiveSpaceAn.{u} m 1).toLocallyRingedSpace.ringSheaf}
    (n : ℤ) {p : relProjectiveSpaceAn.{u} m 1}
    (hp : IsLocallyFinitelyGeneratedModuleAt M p ∧ HasLocalModuleRelationsAt M p) :
    IsLocallyFinitelyGeneratedModuleAt (twistMod M n) p ∧
      HasLocalModuleRelationsAt (twistMod M n) p := by
  obtain ⟨i, hi⟩ : ∃ i, p ∈ stdOpen.{u} m 1 i := by
    have : p ∈ (⊤ : (relProjectiveSpaceAn.{u} m 1).Opens) := trivial
    rw [← iSup_stdOpen] at this
    exact Opens.mem_iSup.1 this
  exact localConditions_of_iso (stdOpen.{u} m 1 i)
    (fun O hO ↦ (modTwistSectionsEquiv (N := M) (twistModCocycle.{u} m 1 n) i hO).toAddEquiv)
    (fun O₁ O₂ h h₂ s ↦ modTwistSectionsEquiv_res (N := M) _ i h₂ h s)
    (fun O hO r s ↦
      (modTwistSectionsEquiv (N := M) (twistModCocycle.{u} m 1 n) i hO).map_smul r s) hi hp

variable {N N₀ : (AnalyticSpace.complexAffineSpace.{u} (m + 1)).Opens}
  {W : FiniteEtaleOver (space N₀)} {F : WeierstrassForm N N₀}
  (D : AnnulusDecomposition W F.G F.ρ) (h₀ : N₀ ≤ N)

/-- **The local conditions for coherence of `𝒞` over `U × ℙ¹`** if `U ⊆ G` and `𝒜` satisfies the
local conditions for coherence at the points of `N` over `U`. -/
theorem capModule_localConditions {U : Opens (Fin m → ℂ)}
    (hUG : ∀ b ∈ U, ofBase b ∈ F.G)
    (hU : ∀ x : space N, baseCoord (baseOf x.1) ∈ U → IsCoherentAt h₀ W x)
    {p : relProjectiveSpaceAn.{u} m 1} (hp : p ∈ tube.{u} (N := 1) U) :
    IsLocallyFinitelyGeneratedModuleAt D.capModule p ∧
      HasLocalModuleRelationsAt D.capModule p := by
  obtain ⟨q, hqU, hq1, hq⟩ := exists_chartPt_norm_le_one hp
  have hqρ : ‖q.2‖ < F.ρ := hq1.trans_lt F.one_lt_ρ
  have hcoh : ∀ x : space N, x.1 = chartCoordHomeo.symm q → IsCoherentAt h₀ W x :=
    fun x hx ↦ hU x (by
      have : chartCoordHomeo x.1 = q := by rw [hx]; exact chartCoordHomeo.apply_symm_apply q
      have h1 : baseCoord (baseOf x.1) = q.1 := congrArg Prod.fst this
      exact h1 ▸ hqU)
  rcases hq with hq | hq
  · rw [← hq]
    exact D.capModule_isCoherentAt_chartPt h₀ (hUG _ hqU) hqρ fun _ ↦ hcoh
  · rw [← hq]
    exact D.capModule_isCoherentAt_chartPt h₀ (hUG _ hqU) hqρ fun h ↦ absurd h (by decide)

/-- **The twists of the sheaf of the cap are coherent over `U × ℙ¹`.** -/
theorem isCoherent_restrictModules_twistMod_capModule {U : Opens (Fin m → ℂ)}
    (hUG : ∀ b ∈ U, ofBase b ∈ F.G)
    (hU : ∀ x : space N, baseCoord (baseOf x.1) ∈ U → IsCoherentAt h₀ W x) (n : ℤ) :
    (((relProjectiveSpaceAn.{u} m 1).toLocallyRingedSpace.restrictModules
      (tube.{u} (N := 1) U)).obj (twistMod D.capModule n)).IsCoherent :=
  isCoherent_restrictModules_of_forall _ _ fun _ hp ↦
    localConditions_twistMod n (D.capModule_localConditions h₀ hUG hU hp)

end

end ComplexAnalytic.Cap.AnnulusDecomposition

namespace ComplexAnalytic.Cap

open AnalyticSpace relProjectiveSpaceAn relProjectiveLine
open AlgebraicGeometry AlgebraicGeometry.LocallyRingedSpace

noncomputable section

variable {m : ℕ}

/-! ### Sections of `𝒪(e)^I` -/

lemma f0_restrictOpen {W W' : (relProjectiveSpaceAn.{u} m 1).Opens} (h : W' ≤ W)
    (a : (relProjectiveSpaceAn.{u} m 1).presheaf.obj (op W)) {p : (Fin m → ℂ) × ℂ}
    (hp : chartPt.{u} 0 p ∈ W') : f0 (TopCat.Presheaf.restrictOpen a W' h) p = f0 a p := by
  rw [f0_eq_eval _ hp, f0_eq_eval _ (h hp), AnalyticSpace.eval_restrictOpen]

lemma f1_restrictOpen {W W' : (relProjectiveSpaceAn.{u} m 1).Opens} (h : W' ≤ W)
    (a : (relProjectiveSpaceAn.{u} m 1).presheaf.obj (op W)) {p : (Fin m → ℂ) × ℂ}
    (hp : chartPt.{u} 1 p ∈ W') : f1 (TopCat.Presheaf.restrictOpen a W' h) p = f1 a p := by
  rw [f1_eq_eval _ hp, f1_eq_eval _ (h hp), AnalyticSpace.eval_restrictOpen]

lemma chartBox_prodOpens_le (i : Fin 2) (V : Opens (Fin m → ℂ)) :
    chartBox.{u} i (prodOpens V ⊤) ≤ tube.{u} (N := 1) V ⊓ stdOpen.{u} m 1 i := by
  rintro _ ⟨q, hq, rfl⟩
  refine ⟨?_, chartBox_le_stdOpen i _ ⟨q, hq, rfl⟩⟩
  change baseY (chartPt.{u} i q) ∈ V
  rw [baseY_chartPt]
  exact hq.1

lemma differentiableOn_f0_tube {V : Opens (Fin m → ℂ)}
    (a : (relProjectiveSpaceAn.{u} m 1).presheaf.obj
      (op (tube.{u} (N := 1) V ⊓ stdOpen.{u} m 1 0))) :
    DifferentiableOn ℂ (f0 a) (prodOpens V ⊤) :=
  (differentiableOn_f0 (TopCat.Presheaf.restrictOpen a _ (chartBox_prodOpens_le 0 V))).congr
    fun p hp ↦ (f0_restrictOpen _ a
      (show chartPt.{u} 0 p ∈ chartBox.{u} 0 (prodOpens V ⊤) from ⟨p, hp, rfl⟩)).symm

lemma differentiableOn_f1_tube {V : Opens (Fin m → ℂ)}
    (a : (relProjectiveSpaceAn.{u} m 1).presheaf.obj
      (op (tube.{u} (N := 1) V ⊓ stdOpen.{u} m 1 1))) :
    DifferentiableOn ℂ (f1 a) (prodOpens V ⊤) :=
  (differentiableOn_f1 (TopCat.Presheaf.restrictOpen a _ (chartBox_prodOpens_le 1 V))).congr
    fun p hp ↦ (f1_restrictOpen _ a
      (show chartPt.{u} 1 p ∈ chartBox.{u} 1 (prodOpens V ⊤) from ⟨p, hp, rfl⟩)).symm

variable {I : Type u} [DecidableEq I] {e : ℕ} {V : Opens (Fin m → ℂ)}
  (P : (twistMod (SheafOfModules.free
    (R := (relProjectiveSpaceAn.{u} m 1).toLocallyRingedSpace.ringSheaf) I) (e : ℤ)).val.obj
      (op (tube.{u} (N := 1) V)))

/-- The `i`-th coordinate of a section of `𝒪(e)^I` over `V × ℙ¹` in the chart `w`. -/
def freeF0 (i : I) : (Fin m → ℂ) × ℂ → ℂ :=
  f0 (SheafOfModules.freeEval (op (tube.{u} (N := 1) V ⊓ stdOpen.{u} m 1 0))
    (modTwistComp P 0) i)

/-- The `i`-th coordinate of a section of `𝒪(e)^I` over `V × ℙ¹` in the chart `w'`. -/
def freeF1 (i : I) : (Fin m → ℂ) × ℂ → ℂ :=
  f1 (SheafOfModules.freeEval (op (tube.{u} (N := 1) V ⊓ stdOpen.{u} m 1 1))
    (modTwistComp P 1) i)

lemma differentiableOn_freeF0 (i : I) : DifferentiableOn ℂ (freeF0 P i) (prodOpens V ⊤) :=
  differentiableOn_f0_tube _

lemma differentiableOn_freeF1 (i : I) : DifferentiableOn ℂ (freeF1 P i) (prodOpens V ⊤) :=
  differentiableOn_f1_tube _

/-- **The coordinates in the two charts differ by `wᵉ`.** -/
lemma freeF0_eq (i : I) {y : Fin m → ℂ} (hy : y ∈ V) {w : ℂ} (hw : w ≠ 0) :
    freeF0 P i (y, w) = w ^ e * freeF1 P i (y, w⁻¹) := by
  set O' := tube.{u} (N := 1) V ⊓ (stdOpen.{u} m 1 0 ⊓ stdOpen.{u} m 1 1)
  have hc := modTwistComp_compat P 0 1
  have h := congrArg (fun s ↦ SheafOfModules.freeEval (op O') s i) hc
  erw [(SheafOfModules.freeEval (op O')).map_smul] at h
  rw [Pi.smul_apply, smul_eq_mul] at h
  erw [SheafOfModules.freeEval_naturality, SheafOfModules.freeEval_naturality] at h
  have hp : chartPt.{u} 0 (y, w) ∈ O' := by
    refine ⟨?_, BoundedSections.BlowupData.chartPt_mem_stdOpen 0 _, ?_⟩
    · change baseY (chartPt.{u} 0 _) ∈ V
      rw [baseY_chartPt]
      exact hy
    · rw [SetLike.mem_coe, Cap.AnnulusDecomposition.chartPt_zero_mem_stdOpen_one_iff]
      exact hw
  have hv := congrArg ((relProjectiveSpaceAn.{u} m 1).eval (chartPt.{u} 0 (y, w)) hp) h
  erw [map_mul, eval_presheaf_map, eval_presheaf_map, eval_presheaf_map] at hv
  rw [← f0_eq_eval ((twistModCocycle.{u} m 1 (e : ℤ)).g 0 1),
    f0_twistModCocycle _ hp.2] at hv
  have hp1 : chartPt.{u} 1 (y, w⁻¹) ∈ tube.{u} (N := 1) V ⊓ stdOpen.{u} m 1 1 := by
    rw [← chartPt_zero_eq_chartPt_one (p := (y, w)) hw]
    exact ⟨hp.1, hp.2.2⟩
  have hp0 : chartPt.{u} 0 (y, w) ∈ tube.{u} (N := 1) V ⊓ stdOpen.{u} m 1 0 := ⟨hp.1, hp.2.1⟩
  rw [freeF0, freeF1, f0_eq_eval _ hp0, f1_eq_eval _ hp1]
  rw [zpow_natCast] at hv
  refine hv.trans (congrArg _ (eval_congr_point (chartPt_zero_eq_chartPt_one hw) _ _ _))

lemma differentiable_freeF0 (i : I) {y : Fin m → ℂ} (hy : y ∈ V) :
    Differentiable ℂ fun w ↦ freeF0 P i (y, w) := fun w ↦
  ((differentiableOn_freeF0 P i).differentiableAt ((prodOpens V ⊤).isOpen.mem_nhds
    (mem_prodOpens.2 ⟨hy, trivial⟩))).comp w ((differentiableAt_const y).prodMk differentiableAt_id)

lemma differentiable_freeF1 (i : I) {y : Fin m → ℂ} (hy : y ∈ V) :
    Differentiable ℂ fun w ↦ freeF1 P i (y, w) := fun w ↦
  ((differentiableOn_freeF1 P i).differentiableAt ((prodOpens V ⊤).isOpen.mem_nhds
    (mem_prodOpens.2 ⟨hy, trivial⟩))).comp w ((differentiableAt_const y).prodMk differentiableAt_id)

/-- **A section of `𝒪(e)^I` is a tuple of polynomials of degree `≤ e` in `w`**, determined by
Lagrange interpolation at `e + 1` distinct points. -/
theorem freeF0_eq_sum_lagrange (i : I) {y : Fin m → ℂ} (hy : y ∈ V) {x : Fin (e + 1) → ℂ}
    (hx : Function.Injective x) (z : ℂ) :
    freeF0 P i (y, z) = ∑ l, freeF0 P i (y, x l) * (Lagrange.basis Finset.univ x l).eval z :=
  eq_sum_lagrange_of_eq_pow_mul_inv (g := fun w ↦ freeF0 P i (y, w))
    (h := fun w ↦ freeF1 P i (y, w)) (differentiable_freeF0 P i hy)
    (differentiable_freeF1 P i hy) (fun _ hw ↦ freeF0_eq P i hy hw) hx z

end

end ComplexAnalytic.Cap
