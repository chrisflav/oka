/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.GAGA.ProjectiveSpaceAn

/-!
# The point at infinity of the analytic projective line

On `ℙ¹_an` the chart `0` is `z ↦ [1 : z]` and the chart `1` is `w ↦ [w : 1]`. The point at
infinity `∞ = [0 : 1]` (`ComplexAnalytic.ProjectiveLine.infty`) is the complement of the image of
the chart `0` (`ComplexAnalytic.ProjectiveLine.mem_range_chart_zero_iff`), and on the overlap
`w = 1 / z` (`ComplexAnalytic.ProjectiveLine.chart_zero_eq_chart_one`). The sets
`{∞} ∪ {[1 : z] | ‖z‖ > R}` form a basis of neighbourhoods of `∞`
(`ComplexAnalytic.ProjectiveLine.exists_forall_chart_zero_mem`,
`ComplexAnalytic.ProjectiveLine.nbd`).
-/

open CategoryTheory Topology Filter

universe u

namespace ComplexAnalytic.ProjectiveLine

open AnalyticSpace projectiveSpaceAn

noncomputable section

/-- The coordinate of a point of `ℂ¹`. -/
def coord (z : AnalyticSpace.complexAffineSpace.{u} 1) : ℂ :=
  (z : ULift.{u} (Fin 1) → ℂ) ⟨0⟩

/-- The point of `ℂ¹` with coordinate `c`. -/
def ofCoord (c : ℂ) : AnalyticSpace.complexAffineSpace.{u} 1 :=
  show ULift.{u} (Fin 1) → ℂ from fun _ ↦ c

@[simp]
lemma coord_ofCoord (c : ℂ) : coord.{u} (ofCoord c) = c :=
  rfl

@[simp]
lemma ofCoord_coord (z : AnalyticSpace.complexAffineSpace.{u} 1) : ofCoord (coord z) = z := by
  funext ⟨i⟩
  fin_cases i
  rfl

lemma continuous_coord : Continuous (coord.{u}) :=
  continuous_apply (⟨0⟩ : ULift.{u} (Fin 1))

lemma continuous_ofCoord : Continuous (ofCoord.{u}) :=
  continuous_pi fun _ ↦ continuous_id

/-- The chart `i` of `ℙ¹_an` on points. -/
abbrev chart (i : Fin 2) : AnalyticSpace.complexAffineSpace.{u} 1 → projectiveSpaceAn.{u} 1 :=
  (projectiveSpaceAnChart.{u} i).toLRSHom.base

/-- **The point at infinity** `∞ = [0 : 1]` of `ℙ¹_an`. -/
def infty : projectiveSpaceAn.{u} 1 :=
  chart 1 (ofCoord 0)

lemma homogCoord_zero (z : AnalyticSpace.complexAffineSpace.{u} 1) :
    homogCoord 0 z = ![1, coord z] := by
  funext k
  fin_cases k <;> rfl

lemma homogCoord_one (z : AnalyticSpace.complexAffineSpace.{u} 1) :
    homogCoord 1 z = ![coord z, 1] := by
  funext k
  fin_cases k <;> rfl

lemma chart_zero_eq_pointOfVec (z : AnalyticSpace.complexAffineSpace.{u} 1) :
    chart 0 z = pointOfVec.{u} ![1, coord z] (by simp) := by
  simp only [chart]
  rw [chart_eq_pointOfVec]
  congr 1
  exact homogCoord_zero z

lemma chart_one_eq_pointOfVec (z : AnalyticSpace.complexAffineSpace.{u} 1) :
    chart 1 z = pointOfVec.{u} ![coord z, 1] (by simp) := by
  simp only [chart]
  rw [chart_eq_pointOfVec]
  congr 1
  exact homogCoord_one z

lemma infty_eq_pointOfVec : infty.{u} = pointOfVec.{u} ![0, 1] (by simp) := by
  rw [infty, chart_one_eq_pointOfVec]
  rfl

/-- **The chart transition** `[1 : z] = [1 / z : 1]`. -/
lemma chart_zero_eq_chart_one (z : AnalyticSpace.complexAffineSpace.{u} 1) (hz : coord z ≠ 0) :
    chart 0 z = chart 1 (ofCoord (coord z)⁻¹) := by
  rw [chart_zero_eq_pointOfVec, chart_one_eq_pointOfVec, pointOfVec_eq_pointOfVec_iff]
  refine ⟨(coord z)⁻¹, inv_ne_zero hz, ?_⟩
  funext k
  fin_cases k <;> simp [inv_mul_cancel₀ hz]

lemma chart_one_eq_chart_zero (w : AnalyticSpace.complexAffineSpace.{u} 1) (hw : coord w ≠ 0) :
    chart 1 w = chart 0 (ofCoord (coord w)⁻¹) := by
  rw [chart_zero_eq_chart_one _ (by simpa using hw)]
  simp

lemma chart_zero_ne_infty (z : AnalyticSpace.complexAffineSpace.{u} 1) : chart 0 z ≠ infty := by
  rw [chart_zero_eq_pointOfVec, infty_eq_pointOfVec]
  intro h
  obtain ⟨c, -, hc⟩ := (pointOfVec_eq_pointOfVec_iff _ _ _ _).1 h
  have h0 := congrFun hc 0
  have h1 := congrFun hc 1
  simp only [Fin.isValue, Matrix.cons_val_zero, Pi.smul_apply, smul_eq_mul, mul_one,
    Matrix.cons_val_one] at h0 h1
  rw [← h0, zero_mul] at h1
  exact one_ne_zero h1

/-- **The image of the chart `0` is the complement of `∞`.** -/
lemma mem_range_chart_zero_iff (x : projectiveSpaceAn.{u} 1) :
    x ∈ Set.range (chart 0) ↔ x ≠ infty := by
  refine ⟨?_, fun hx ↦ ?_⟩
  · rintro ⟨z, rfl⟩
    exact chart_zero_ne_infty z
  obtain ⟨v, hv, rfl⟩ := pointOfVec_surjective x
  by_contra h
  rw [mem_range_chart_pointOfVec_iff, not_not] at h
  refine hx ?_
  rw [infty_eq_pointOfVec, pointOfVec_eq_pointOfVec_iff]
  have h1 : v 1 ≠ 0 := fun h1 ↦ hv (funext fun k ↦ by fin_cases k <;> assumption)
  refine ⟨(v 1)⁻¹, inv_ne_zero h1, ?_⟩
  funext k
  fin_cases k <;> simp [h, inv_mul_cancel₀ h1]

lemma infty_mem_range_chart_one : infty.{u} ∈ Set.range (chart 1) :=
  ⟨ofCoord 0, rfl⟩

lemma chart_one_eq_infty_iff (w : AnalyticSpace.complexAffineSpace.{u} 1) :
    chart 1 w = infty ↔ coord w = 0 := by
  refine ⟨fun h ↦ by_contra fun hw ↦ ?_, fun h ↦ by rw [infty, ← h, ofCoord_coord]⟩
  rw [chart_one_eq_chart_zero w hw] at h
  exact chart_zero_ne_infty _ h

/-- **Neighbourhoods of `∞` contain `{[1 : z] | ‖z‖ > R}` for some `R`.** -/
lemma exists_forall_chart_zero_mem {N : Set (projectiveSpaceAn.{u} 1)} (hN : N ∈ 𝓝 infty) :
    ∃ R : ℝ, 0 < R ∧ ∀ z, R < ‖coord z‖ → chart 0 z ∈ N := by
  have hc : Continuous (chart 1 ∘ ofCoord.{u}) :=
    (isOpenEmbedding_chart 1).continuous.comp continuous_ofCoord
  have h0 : chart 1 ∘ ofCoord.{u} ⁻¹' N ∈ 𝓝 (0 : ℂ) := hc.continuousAt.preimage_mem_nhds hN
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 h0
  refine ⟨ε⁻¹, inv_pos.2 hε, fun z hz ↦ ?_⟩
  have hz0 : coord z ≠ 0 := by
    intro h
    rw [h, norm_zero] at hz
    exact (not_lt.2 (inv_pos.2 hε).le) hz
  rw [chart_zero_eq_chart_one z hz0]
  refine hball ?_
  rw [Metric.mem_ball, dist_zero_right, norm_inv]
  exact inv_lt_of_inv_lt₀ hε hz

/-- The neighbourhood `{∞} ∪ {[1 : z] | ‖z‖ > R}` of `∞`, as the image of a disc under the
chart `1`. -/
def nbd (R : ℝ) : Set (projectiveSpaceAn.{u} 1) :=
  chart 1 '' {w | ‖coord w‖ < R⁻¹}

lemma isOpen_nbd (R : ℝ) : IsOpen (nbd.{u} R) :=
  (isOpenEmbedding_chart 1).isOpenMap _ (isOpen_lt (continuous_norm.comp continuous_coord)
    continuous_const)

lemma infty_mem_nbd {R : ℝ} (hR : 0 < R) : infty.{u} ∈ nbd R :=
  ⟨ofCoord 0, by simpa using hR, rfl⟩

lemma nbd_mem_nhds {R : ℝ} (hR : 0 < R) : nbd.{u} R ∈ 𝓝 infty :=
  (isOpen_nbd R).mem_nhds (infty_mem_nbd hR)

lemma chart_zero_mem_nbd_iff {R : ℝ} (hR : 0 < R) (z : AnalyticSpace.complexAffineSpace.{u} 1) :
    chart 0 z ∈ nbd R ↔ R < ‖coord z‖ := by
  constructor
  · rintro ⟨w, hw, hwz⟩
    have hw0 : coord w ≠ 0 := by
      intro h
      rw [(chart_one_eq_infty_iff w).2 h] at hwz
      exact chart_zero_ne_infty z hwz.symm
    rw [chart_one_eq_chart_zero w hw0] at hwz
    have hz := chart_injective 0 hwz
    rw [← hz, coord_ofCoord, norm_inv]
    rw [Set.mem_setOf_eq] at hw
    exact lt_inv_of_lt_inv₀ (norm_pos_iff.2 hw0) hw
  · intro hz
    have hz0 : coord z ≠ 0 := by
      intro h
      rw [h, norm_zero] at hz
      exact (not_lt.2 hR.le) hz
    refine ⟨ofCoord (coord z)⁻¹, ?_, (chart_zero_eq_chart_one z hz0).symm⟩
    rw [Set.mem_setOf_eq, coord_ofCoord, norm_inv]
    exact inv_lt_inv₀ (hR.trans hz) hR |>.2 hz

end

end ComplexAnalytic.ProjectiveLine
