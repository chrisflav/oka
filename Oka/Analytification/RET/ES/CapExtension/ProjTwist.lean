/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.ES.CapExtension.ProjCoherent

/-!
# Sections of the twists of the sheaf of the cap

Keep the notation of `Oka/Analytification/RET/ES/CapExtension/ProjSheaf.lean`. A section `σ` of
the twist `𝒞(n)` over `B × ℙ¹` has components `σ₀`, `σ₁` in the two charts, sections of `𝒞`,
with `σ₀ = wⁿ σ₁` on the overlap (`ComplexAnalytic.Cap.AnnulusDecomposition.capWVal_twComp_zero`,
`ComplexAnalytic.Cap.AnnulusDecomposition.capKVal_twComp_zero`). The values of `σ₀` on `W` and
of `σ₁` on the Kummer pieces at infinity form a section of the cap with a pole of order `≤ n` at
infinity (`ComplexAnalytic.Cap.AnnulusDecomposition.capPoleOf_mem`).
-/

open CategoryTheory Opposite Topology TopologicalSpace Set Filter Metric

universe u

namespace ComplexAnalytic.Cap.AnnulusDecomposition

open AnalyticSpace BoundedSections relProjectiveSpaceAn relProjectiveLine
open AlgebraicGeometry AlgebraicGeometry.LocallyRingedSpace
open KummerModel (splitEquiv)

noncomputable section

variable {m : ℕ}

lemma chartPt_zero_mem_stdOpen_one_iff (p : (Fin m → ℂ) × ℂ) :
    chartPt.{u} 0 p ∈ stdOpen.{u} m 1 1 ↔ p.2 ≠ 0 := by
  rw [stdOpen_eq_chartOpens]
  exact chartPt_zero_mem_range_chart_one_iff p

lemma chartPt_one_mem_stdOpen_zero_iff (p : (Fin m → ℂ) × ℂ) :
    chartPt.{u} 1 p ∈ stdOpen.{u} m 1 0 ↔ p.2 ≠ 0 := by
  rw [stdOpen_eq_chartOpens]
  change chartPt.{u} 1 p ∈ Set.range (chartLRS.{u} (m := m) (N := 1) 0).base ↔ _
  rw [chartPt_one_eq, mem_range_chart_pointOfVec_iff]
  simp

lemma chartPt_one_eq_chartPt_zero_inv {p : (Fin m → ℂ) × ℂ} (hp : p.2 ≠ 0) :
    chartPt.{u} 1 p = chartPt.{u} 0 (p.1, p.2⁻¹) := by
  rw [chartPt_zero_eq_chartPt_one (p := (p.1, p.2⁻¹)) (inv_ne_zero hp), inv_inv]

/-- The value in the chart `0` of the transition function of `𝒪(n)`. -/
lemma eval_twistModCocycle {O : (relProjectiveSpaceAn.{u} m 1).Opens}
    (hO : O ≤ stdOpen.{u} m 1 0 ⊓ stdOpen.{u} m 1 1) (n : ℤ) {p : (Fin m → ℂ) × ℂ}
    (hp : chartPt.{u} 0 p ∈ O) :
    (relProjectiveSpaceAn.{u} m 1).eval (chartPt.{u} 0 p) hp
      (TopCat.Presheaf.restrictOpen ((twistModCocycle.{u} m 1 n).g 0 1) O hO) = p.2 ^ n := by
  rw [AnalyticSpace.eval_restrictOpen, ← f0_eq_eval, f0_twistModCocycle n (hO hp)]

variable {N N₀ : (AnalyticSpace.complexAffineSpace.{u} (m + 1)).Opens}
  {W : FiniteEtaleOver (space N₀)} {F : WeierstrassForm N N₀}
  {D : AnnulusDecomposition W F.G F.ρ} {n : ℕ} {B : Opens (Fin m → ℂ)}

/-! ### The components in the charts -/

/-- The component in the chart `i` of a section of `𝒞(n)` over `B × ℙ¹`, a section of `𝒞`. -/
def twComp (σ : (twistMod D.capModule (n : ℤ)).val.obj (op (tube.{u} (N := 1) B))) (i : Fin 2) :
    D.capModule.val.obj (op (tube.{u} (N := 1) B ⊓ stdOpen.{u} m 1 i)) :=
  modTwistSectionsEquiv (N := D.capModule) (twistModCocycle.{u} m 1 (n : ℤ)) i inf_le_right
    (modRes σ _ inf_le_left)

/-- The overlap of the two charts over `B`. -/
abbrev tubeOverlap (B : Opens (Fin m → ℂ)) : (relProjectiveSpaceAn.{u} m 1).Opens :=
  tube.{u} (N := 1) B ⊓ (stdOpen.{u} m 1 0 ⊓ stdOpen.{u} m 1 1)

lemma tubeOverlap_le (i : Fin 2) :
    tubeOverlap.{u} B ≤ tube.{u} (N := 1) B ⊓ stdOpen.{u} m 1 i := by
  fin_cases i
  exacts [inf_le_inf_left _ inf_le_left, inf_le_inf_left _ inf_le_right]

/-- **The components differ by `wⁿ`** on the overlap. -/
lemma twComp_rel (σ : (twistMod D.capModule (n : ℤ)).val.obj (op (tube.{u} (N := 1) B))) :
    modRes (twComp σ 0) (tubeOverlap.{u} B) (tubeOverlap_le 0) =
      TopCat.Presheaf.restrictOpen ((twistModCocycle.{u} m 1 (n : ℤ)).g 0 1) (tubeOverlap.{u} B)
        inf_le_right • modRes (twComp σ 1) (tubeOverlap.{u} B) (tubeOverlap_le 1) := by
  have e (i : Fin 2) : modTwistSectionsEquiv (N := D.capModule) (twistModCocycle.{u} m 1 (n : ℤ))
      i ((tubeOverlap_le i).trans inf_le_right)
      (modRes σ (tubeOverlap.{u} B) ((tubeOverlap_le i).trans inf_le_left)) =
      modRes (twComp σ i) (tubeOverlap.{u} B) (tubeOverlap_le i) := by
    rw [twComp, ← modTwistSectionsEquiv_res, modRes_res]
  have key := modTwistSectionsEquiv_change (N := D.capModule) (twistModCocycle.{u} m 1 (n : ℤ)) 0
    ((tubeOverlap_le 0).trans inf_le_right) 1 ((tubeOverlap_le 1).trans inf_le_right)
    (modRes σ (tubeOverlap.{u} B) ((tubeOverlap_le 0).trans inf_le_left))
  rw [e 0, e 1] at key
  exact key

lemma projW_mem_tubeOverlap {w : W.left}
    (hw : w ∈ (Opens.map (projW W).toLRSHom.base).obj (tube.{u} (N := 1) B))
    (h0 : fibOf (pt W w) ≠ 0) :
    w ∈ (Opens.map (projW W).toLRSHom.base).obj (tubeOverlap.{u} B) := by
  change (projW W).toLRSHom.base w ∈ tubeOverlap.{u} B
  refine ⟨hw, ?_, ?_⟩
  · rw [projW_base, chart0Pt]
    exact BlowupData.chartPt_mem_stdOpen 0 _
  · rw [projW_base, chart0Pt, SetLike.mem_coe, chartPt_zero_mem_stdOpen_one_iff]
    exact h0

/-- **`σ₀ = wⁿ σ₁` on `W`.** -/
lemma capWVal_twComp_zero
    (σ : (twistMod D.capModule (n : ℤ)).val.obj (op (tube.{u} (N := 1) B))) {w : W.left}
    (hw : w ∈ (Opens.map (projW W).toLRSHom.base).obj (tube.{u} (N := 1) B))
    (h0 : fibOf (pt W w) ≠ 0) :
    capWVal (twComp σ 0) w = fibOf (pt W w) ^ n * capWVal (twComp σ 1) w := by
  have hw' := projW_mem_tubeOverlap hw h0
  have := congrArg (fun s ↦ capWVal s w) (twComp_rel σ)
  erw [capWVal_res _ _ hw', capWVal_smul _ _ hw', capWVal_res _ _ hw'] at this
  rw [this]
  congr 1
  have hp : (projW W).toLRSHom.base w =
      chartPt.{u} 0 (baseCoord (baseOf (pt W w)), fibOf (pt W w)) := projW_base W w
  rw [eval_congr_point hp hw' (hp ▸ hw'), eval_twistModCocycle, zpow_natCast]

lemma kMap_mem_tubeOverlap {x : Cn.{u} (m + 1)}
    (hx : x ∈ img ((Opens.map D.kMap.toLRSHom.base).obj (tubeOverlap.{u} B))) :
    D.kVal x ≠ 0 ∧ D.kMap.toLRSHom.base ⟨x, img_le _ x hx⟩ =
      chartPt.{u} 0 (baseCoord (baseOf x), (D.kVal x)⁻¹) := by
  obtain ⟨hxK, hxO⟩ := mem_img_iff.1 hx
  change D.kMap.toLRSHom.base _ ∈ tubeOverlap.{u} B at hxO
  rw [D.kMap_base] at hxO ⊢
  have h0 : D.kVal x ≠ 0 := (chartPt_one_mem_stdOpen_zero_iff _).1 hxO.2.1
  exact ⟨h0, chartPt_one_eq_chartPt_zero_inv h0⟩

/-- **`σ₀ = wⁿ σ₁` on `K`**: at a point of `K` with `w' = kVal`, `w = kVal⁻¹`. -/
lemma capKVal_twComp_zero
    (σ : (twistMod D.capModule (n : ℤ)).val.obj (op (tube.{u} (N := 1) B)))
    {x : Cn.{u} (m + 1)}
    (hx : x ∈ img ((Opens.map D.kMap.toLRSHom.base).obj (tubeOverlap.{u} B))) :
    capKVal (twComp σ 0) x = (D.kVal x)⁻¹ ^ n * capKVal (twComp σ 1) x := by
  have := congrArg (fun s ↦ capKVal s x) (twComp_rel σ)
  erw [capKVal_res _ _ hx, capKVal_smul _ _ hx, capKVal_res _ _ hx] at this
  rw [this]
  congr 1
  obtain ⟨-, hp⟩ := kMap_mem_tubeOverlap hx
  rw [eval_congr_point hp _ (hp ▸ (mem_img_iff.1 hx).2), eval_twistModCocycle, zpow_natCast]

/-! ### The section of the cap -/

variable (B) in
/-- The base `B`, as a subset of `ℂᵐ` in the coordinates of `N`. -/
def baseSet : Set (Cm.{u} m) :=
  {b | baseCoord b ∈ B}

lemma isOpen_baseSet : IsOpen (baseSet.{u} B) :=
  B.isOpen.preimage continuous_baseCoord

variable (h₀ : N₀ ≤ N) (hB : ∀ y ∈ B, ofBase.{u} y ∈ F.G)
include hB

lemma baseSet_subset : baseSet.{u} B ⊆ F.G := fun b hb ↦ by
  have := hB _ hb
  rwa [ofBase_baseCoord] at this

omit hB in
lemma img0_tubeN_le :
    img0 N (tubeN N (baseSet.{u} B) isOpen_baseSet) ≤
      tube.{u} (N := 1) B ⊓ stdOpen.{u} m 1 0 := by
  intro p hp
  obtain ⟨x, hx, rfl⟩ := (mem_img0 N).1 hp
  refine ⟨?_, BlowupData.chartPt_mem_stdOpen 0 _⟩
  change baseY (chartPt.{u} 0 _) ∈ B
  rw [baseY_chartPt]
  exact (mem_img_iff.1 hx).2

omit hB in
lemma mem_preimW_of_mem_preim {w : W.left}
    (hw : w ∈ preim h₀ W (tubeN N (baseSet.{u} B) isOpen_baseSet)) :
    w ∈ (Opens.map (projW W).toLRSHom.base).obj (tube.{u} (N := 1) B ⊓ stdOpen.{u} m 1 0) :=
  img0_tubeN_le ((mem_preimW_img0_iff h₀).2 hw)

omit hB in
/-- The section of `𝒜` over `N ∩ (B × ℂ)` given by the values of `σ₀` on `W`. -/
def capW0 (σ : (twistMod D.capModule (n : ℤ)).val.obj (op (tube.{u} (N := 1) B))) :
    (boundedModule h₀ W).val.obj (op (tubeN N (baseSet.{u} B) isOpen_baseSet)) :=
  phi0 h₀ _ (sectRes D.capModule img0_tubeN_le (twComp σ 0))

omit hB in
lemma evalFun_capW0 (σ : (twistMod D.capModule (n : ℤ)).val.obj (op (tube.{u} (N := 1) B)))
    {w : W.left} (hw : w ∈ preim h₀ W (tubeN N (baseSet.{u} B) isOpen_baseSet)) :
    evalFun (secVal h₀ W (capW0 h₀ σ)) w = capWVal (twComp σ 0) w := by
  rw [capW0, evalFun_phi0 h₀ _ hw, capWVal_res _ _ ((mem_preimW_img0_iff h₀).2 hw)]

omit hB in
variable (D) in
/-- **The section of the cap given by a section `σ` of `𝒞(n)`**: the values of `σ₀` on `W` and
those of `σ₁` on the Kummer pieces at infinity. -/
def capPoleOf (σ : (twistMod D.capModule (n : ℤ)).val.obj (op (tube.{u} (N := 1) B))) :
    boundedSubring h₀ W (tubeN N (baseSet.{u} B) isOpen_baseSet) × (D.ι → Cm.{u} m × ℂ → ℂ) :=
  (⟨secVal h₀ W (capW0 h₀ σ), secVal_mem h₀ W _⟩, fun i z ↦ capKVal (twComp σ 1) (D.kPt i z))

omit hB in
lemma evalFun_capPoleOf (σ : (twistMod D.capModule (n : ℤ)).val.obj (op (tube.{u} (N := 1) B)))
    {w : W.left} (hw : w ∈ preim h₀ W (tubeN N (baseSet.{u} B) isOpen_baseSet)) :
    evalFun (D.capPoleOf h₀ σ).1.1 w = capWVal (twComp σ 0) w :=
  evalFun_capW0 h₀ σ hw

lemma kPt_mem_imgK1 {i : D.ι} {z : Cm.{u} m × ℂ}
    (hz : Kummer.powMap (D.deg i) z ∈ baseSet.{u} B ×ˢ ball (0 : ℂ) F.ρ) :
    D.kPt i z ∈ D.kPiece i ∧ D.kPt i z ∈ img ((Opens.map D.kMap.toLRSHom.base).obj
      (tube.{u} (N := 1) B ⊓ stdOpen.{u} m 1 1)) := by
  obtain ⟨hzB, hzρ⟩ := hz
  have hK : D.kPt i z ∈ D.kPiece i := D.kPt_mem (baseSet_subset hB hzB) (mem_ball_zero_iff.1 hzρ)
  refine ⟨hK, mem_img_iff.2 ⟨D.mem_kOpens.2 ⟨i, hK⟩, ?_⟩⟩
  change D.kMap.toLRSHom.base _ ∈ tube.{u} (N := 1) B ⊓ stdOpen.{u} m 1 1
  rw [D.kMap_base, D.kVal_kPt hK, baseOf_kPt]
  refine ⟨?_, BlowupData.chartPt_mem_stdOpen 1 _⟩
  change baseY (chartPt.{u} 1 _) ∈ B
  rw [baseY_chartPt]
  exact hzB

/-- **A section of `𝒞(n)` gives a section of the cap with a pole of order `≤ n`.** -/
theorem capPoleOf_mem
    (σ : (twistMod D.capModule (n : ℤ)).val.obj (op (tube.{u} (N := 1) B))) :
    D.capPoleOf h₀ σ ∈ D.capPole h₀ n (tubeN N (baseSet.{u} B) isOpen_baseSet)
      (baseSet.{u} B ×ˢ ball 0 F.ρ) := by
  refine ⟨fun i z hz ↦ ?_, fun i z hz hz' ↦ ?_⟩
  · have hx := (kPt_mem_imgK1 hB hz).2
    exact (((differentiableOn_holFun (kPart (twComp σ 1).1)).differentiableAt
      ((img _).isOpen.mem_nhds hx)).comp z (differentiable_kPt i z)).differentiableWithinAt
  · obtain ⟨hzb, hzO⟩ := hz
    have hw0 := mem_preimW_of_mem_preim h₀ hzO
    have hA : D.toFun ⟨i, ⟨z, hzb⟩⟩ ∈ pt W ⁻¹' annulusRegion F.G F.ρ := by
      rw [← D.range_eq]
      exact ⟨_, rfl⟩
    have hfib : fibOf (pt W (D.toFun ⟨i, ⟨z, hzb⟩⟩)) ≠ 0 := by
      have h2 : F.ρ⁻¹ < ‖fibOf (pt W (D.toFun ⟨i, ⟨z, hzb⟩⟩))‖ := hA.2.1
      exact norm_pos_iff.1 ((inv_pos.2 F.pos_ρ).trans h2)
    have hwO := projW_mem_tubeOverlap (B := B) hw0.1 hfib
    have hx := kPt_mem_img (z := ⟨z, hzb⟩) hwO
    have hiK := D.kPt_invCoord_mem hzb
    rw [D.kummerVal_of_mem _ _ hzb, evalFun_capPoleOf h₀ σ hzO,
      capWVal_compat (twComp σ 0) i ⟨z, hzb⟩ hw0, capKVal_twComp_zero σ hx, D.kVal_kPt hiK]
    change _ = _ * capKVal (twComp σ 1) (D.kPt i (invCoord z))
    congr 1
    simp only [invCoord, inv_pow, inv_inv, ← pow_mul, mul_comm]

end

end ComplexAnalytic.Cap.AnnulusDecomposition
