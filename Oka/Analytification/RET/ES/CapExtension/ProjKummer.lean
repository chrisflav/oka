/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.ES.CapExtension.ProjSheaf

/-!
# Sections of `𝒪_W` over the annulus from their Kummer coordinates

Keep the notation of `Oka/Analytification/RET/ES/Cap.lean`: `D` decomposes the part of `W` over the
annulus `G × {ρ⁻¹ < ‖w‖ < ρ}` into Kummer covers. A family of functions `hᵢ` of the Kummer
coordinates, holomorphic where the `i`-th piece meets an open `O ⊆ W` over the annulus, is the
family of values of a section of `𝒪_W` over `O`
(`ComplexAnalytic.Cap.AnnulusDecomposition.exists_eval_eq_of_kummer`).
-/

open CategoryTheory Opposite Topology TopologicalSpace Set Filter Metric

universe u

namespace ComplexAnalytic.Cap.AnnulusDecomposition

open AnalyticSpace BoundedSections Complex.ProjectiveLineBundle
open KummerModel (splitEquiv)

noncomputable section

variable {m : ℕ} {N₀ : (AnalyticSpace.complexAffineSpace.{u} (m + 1)).Opens}
  {W : FiniteEtaleOver (space N₀)} {G : Set (Cm.{u} m)} {ρ : ℝ}
  (D : AnnulusDecomposition W G ρ)

/-- **A section of `𝒪_W` over the annulus with prescribed values in Kummer coordinates.** -/
theorem exists_eval_eq_of_kummer (hGo : IsOpen G) {O : W.left.Opens}
    (hO : ∀ w ∈ O, pt W w ∈ annulusRegion G ρ) (h : D.ι → Cm.{u} m × ℂ → ℂ)
    (hh : ∀ i, ∀ z ∈ D.pieceSet O i, DifferentiableAt ℂ (h i) z) :
    ∃ a : W.left.presheaf.obj (op O), ∀ (i : D.ι) (z : Cm.{u} m × ℂ)
      (hz : z ∈ KummerAnnulus.base G ρ⁻¹ ρ (D.deg i)),
      D.toFun ⟨i, ⟨z, hz⟩⟩ ∈ O → evalFun a (D.toFun ⟨i, ⟨z, hz⟩⟩) = h i z := by
  classical
  let f : W.left → ℂ := fun w ↦
    if hw : w ∈ Set.range D.toFun then h hw.choose.1 hw.choose.2.1 else 0
  have hf (i : D.ι) (z : Cm.{u} m × ℂ) (hz : z ∈ KummerAnnulus.base G ρ⁻¹ ρ (D.deg i)) :
      f (D.toFun ⟨i, ⟨z, hz⟩⟩) = h i z := by
    have hw : D.toFun ⟨i, ⟨z, hz⟩⟩ ∈ Set.range D.toFun := ⟨_, rfl⟩
    simp only [f, dif_pos hw]
    have := D.toFun_injective hw.choose_spec
    rw [this]
  obtain ⟨a, ha⟩ := exists_eval_eq_of_local (isLocallyOpenInAffine_left W) (O := O) f
    fun w₀ hw₀ ↦ by
      set x₀ := splitEquiv m (pt W w₀)
      have hx₀ : x₀ ∈ G ×ˢ overlap ρ := hO w₀ hw₀
      obtain ⟨ε, hε0, hε⟩ := Metric.isOpen_iff.1 (isOpen_overlap ρ) _ hx₀.2
      set O' : W.left.Opens := O ⊓ ⟨(fun w ↦ splitEquiv m (pt W w)) ⁻¹' discRegion G x₀.2 ε,
        (hGo.prod isOpen_ball).preimage ((splitEquiv m).continuous.comp (continuous_pt W))⟩
      have hO' : ∀ w ∈ O', splitEquiv m (pt W w) ∈ discRegion G x₀.2 ε := fun w hw ↦ hw.2
      obtain ⟨σ, hσ⟩ := D.exists_sheetVal_eq hε hGo (O := O') hO'
        (fun i j z ↦ h i (sheetCoord (D.deg i) j x₀.2 z)) fun i j z hz hzO ↦ by
          refine (hh i _ ⟨sheetCoord_mem_base hε (D.deg i) j hz, hzO.1⟩).comp z
            (differentiableAt_sheetCoord hε _ _ hz)
      refine ⟨O', ⟨hw₀, hx₀.1, mem_ball_self hε0⟩, inf_le_left, σ, fun w hw ↦ ?_⟩
      obtain ⟨i, j, hj, hsw⟩ := D.exists_sheet_eq hε (hO' w hw) rfl
      have hsO : D.sheet hε i j _ (hO' w hw) ∈ O' := by rw [hsw]; exact hw
      have e1 := D.evalFun_sheet hε σ i j (hO' w hw)
      rw [hsw, evalFun_of_mem _ hw] at e1
      rw [e1, hσ i ⟨j, hj⟩ _ (hO' w hw) hsO]
      conv_rhs => rw [← hsw]
      exact (hf i _ _).symm
  refine ⟨a, fun i z hz hzO ↦ ?_⟩
  rw [evalFun_of_mem _ hzO, ha _ hzO, hf]

end

end ComplexAnalytic.Cap.AnnulusDecomposition
