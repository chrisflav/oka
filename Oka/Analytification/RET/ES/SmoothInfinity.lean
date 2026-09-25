/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.ES.SmoothSetup
import Oka.Polynomial

/-!
# The hyperplane at infinity of `ℙⁿ_an`

The chart `0` of `ℙⁿ_an` is `z ↦ [1 : z]`; its complement is the hyperplane at infinity `H_∞`
(`ComplexAnalytic.ProjectiveCompletion.infinity`). A point `v` of the chart `i` lies in the chart
`0` iff its homogeneous coordinate `0` is nonzero, and then it is the point `[1 : τ v]` of the chart
`0`, `τ v = (x_{k+1} / x₀)ₖ` for `x = homogCoord i v`
(`ComplexAnalytic.ProjectiveCompletion.chart_eq_chart_zero`). Every neighbourhood of `H_∞` contains
`{[1 : z] | ‖z‖ > R}` for some `R`
(`ComplexAnalytic.ProjectiveCompletion.exists_forall_chart_zero_mem`).

For a nonzero polynomial `e` in `n` variables, the function `v ↦ x₀^{d+1} e(τ v)`, `d` the total
degree of `e`, extends to a polynomial function on the chart `i`
(`ComplexAnalytic.ProjectiveCompletion.chartFun`), whose zero set is `H_∞ ∪ {e = 0}` in the chart
and has empty interior (`ComplexAnalytic.ProjectiveCompletion.interior_chartFun_eq_zero`).
-/

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry Topology Filter

universe u

namespace ComplexAnalytic.ProjectiveCompletion

open AnalyticSpace projectiveSpaceAn ProjectiveSpace

noncomputable section

variable {n : ℕ}

/-- The chart `i` of `ℙⁿ_an` on points. -/
abbrev chart (i : Fin (n + 1)) : AnalyticSpace.complexAffineSpace.{u} n → projectiveSpaceAn.{u} n :=
  (projectiveSpaceAnChart.{u} i).toLRSHom.base

/-- The sup norm of a point of `ℂⁿ`. -/
def vnorm (z : AnalyticSpace.complexAffineSpace.{u} n) : ℝ :=
  ‖(show ULift.{u} (Fin n) → ℂ from z)‖

lemma vnorm_nonneg (z : AnalyticSpace.complexAffineSpace.{u} n) : 0 ≤ vnorm z :=
  norm_nonneg (show ULift.{u} (Fin n) → ℂ from z)

lemma norm_apply_le_vnorm (z : AnalyticSpace.complexAffineSpace.{u} n) (m : Fin n) :
    ‖toFin z m‖ ≤ vnorm z :=
  norm_le_pi_norm (show ULift.{u} (Fin n) → ℂ from z) ⟨m⟩

lemma norm_homogCoord_apply_le (j : Fin (n + 1)) (z : AnalyticSpace.complexAffineSpace.{u} n)
    (k : Fin (n + 1)) : ‖homogCoord j z k‖ ≤ max 1 (vnorm z) := by
  obtain rfl | ⟨m, rfl⟩ := Fin.eq_self_or_eq_succAbove j k
  · rw [homogCoord_self, norm_one]
    exact le_max_left _ _
  · simp only [homogCoord, Fin.insertNth_apply_succAbove]
    exact (norm_apply_le_vnorm z m).trans (le_max_right _ _)

lemma vnorm_le_norm_homogCoord (j : Fin (n + 1)) (z : AnalyticSpace.complexAffineSpace.{u} n) :
    vnorm z ≤ ‖homogCoord j z‖ := by
  change ‖(show ULift.{u} (Fin n) → ℂ from z)‖ ≤ _
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg (homogCoord j z))).2 fun m ↦ ?_
  have : (show ULift.{u} (Fin n) → ℂ from z) m = homogCoord j z (j.succAbove m.down) := by
    simp [homogCoord, toFin]
  rw [this]
  exact norm_le_pi_norm (homogCoord j z) _

/-! ### The hyperplane at infinity -/

/-- **The hyperplane at infinity** `H_∞`, the complement of the chart `0`. -/
def infinity : Set (projectiveSpaceAn.{u} n) :=
  (Set.range (chart 0))ᶜ

lemma isClosed_infinity : IsClosed (infinity.{u} (n := n)) :=
  (isOpenEmbedding_chart 0).isOpenMap.isOpen_range.isClosed_compl

lemma chart_zero_notMem_infinity (z : AnalyticSpace.complexAffineSpace.{u} n) :
    chart 0 z ∉ infinity :=
  fun h ↦ h ⟨z, rfl⟩

/-- A point of the chart `i` lies in the chart `0` iff its homogeneous coordinate `0` is
nonzero. -/
lemma chart_mem_range_zero_iff (i : Fin (n + 1)) (v : AnalyticSpace.complexAffineSpace.{u} n) :
    chart i v ∈ Set.range (chart 0) ↔ homogCoord i v 0 ≠ 0 := by
  change (projectiveSpaceAnChart.{u} i).toLRSHom.base v ∈ _ ↔ _
  rw [chart_eq_pointOfVec]
  exact mem_range_chart_pointOfVec_iff _ _ 0

lemma chart_mem_infinity_iff (i : Fin (n + 1)) (v : AnalyticSpace.complexAffineSpace.{u} n) :
    chart i v ∈ infinity ↔ homogCoord i v 0 = 0 := by
  rw [infinity, Set.mem_compl_iff, chart_mem_range_zero_iff, not_not]

/-- The chart transition `τ v = (x_{k+1} / x₀)ₖ`, `x = homogCoord i v`, from the chart `i` to the
chart `0`. -/
def transition (i : Fin (n + 1)) (v : AnalyticSpace.complexAffineSpace.{u} n) :
    AnalyticSpace.complexAffineSpace.{u} n :=
  ofFin (dehomogenizeVec 0 (homogCoord i v))

/-- **The chart transition**: `[v]_i = [1 : τ v]`. -/
lemma chart_eq_chart_zero (i : Fin (n + 1)) (v : AnalyticSpace.complexAffineSpace.{u} n)
    (h : homogCoord i v 0 ≠ 0) : chart i v = chart 0 (transition i v) := by
  rw [chart, chart_eq_pointOfVec, pointOfVec_eq _ _ 0 h]
  rfl

lemma homogCoord_zero_transition (i : Fin (n + 1)) (v : AnalyticSpace.complexAffineSpace.{u} n)
    (h : homogCoord i v 0 ≠ 0) :
    homogCoord 0 (transition i v) = (homogCoord i v 0)⁻¹ • homogCoord i v := by
  rw [homogCoord, transition, toFin_ofFin]
  exact insertNth_dehomogenizeVec 0 _ h

lemma eq_transition_of_chart_eq (i : Fin (n + 1)) {v z : AnalyticSpace.complexAffineSpace.{u} n}
    (h : chart i v = chart 0 z) : homogCoord i v 0 ≠ 0 ∧ z = transition i v := by
  have h0 : homogCoord i v 0 ≠ 0 := (chart_mem_range_zero_iff i v).1 ⟨z, h.symm⟩
  exact ⟨h0, chart_injective 0 (h.symm.trans (chart_eq_chart_zero i v h0))⟩

/-- **Neighbourhoods of `H_∞`**: an open containing `H_∞` contains `{[1 : z] | ‖z‖ > R}` for
some `R`. -/
lemma exists_forall_chart_zero_mem {G : Set (projectiveSpaceAn.{u} n)} (hG : IsOpen G)
    (hinf : infinity ⊆ G) : ∃ R : ℝ, ∀ z, R < vnorm z → chart 0 z ∈ G := by
  have hK : IsCompact Gᶜ := hG.isClosed_compl.isCompact
  have hKr : Gᶜ ⊆ Set.range (chart.{u} (n := n) 0) := fun y hy ↦ by
    by_contra h
    exact hy (hinf h)
  have hc : IsCompact (chart.{u} (n := n) 0 ⁻¹' Gᶜ) :=
    (isOpenEmbedding_chart 0).isInducing.isCompact_preimage' hK hKr
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall
    (0 : ULift.{u} (Fin n) → ℂ)).1 (IsCompact.isBounded (α := ULift.{u} (Fin n) → ℂ) hc)
  refine ⟨R, fun z hz ↦ by_contra fun h ↦ ?_⟩
  have := hR h
  rw [Metric.mem_closedBall, dist_zero_right] at this
  exact (not_lt.2 this) (show R < ‖(show ULift.{u} (Fin n) → ℂ from z)‖ from hz)

/-! ### A polynomial vanishing on `H_∞ ∪ {e = 0}` in the chart `i` -/

/-- The homogeneous coordinate `k` of the chart `i`, as a polynomial. -/
def homogCoordPoly (i k : Fin (n + 1)) : MvPolynomial (ULift.{u} (Fin n)) ℂ :=
  Fin.insertNth (α := fun _ ↦ MvPolynomial (ULift.{u} (Fin n)) ℂ) i 1
    (fun m ↦ MvPolynomial.X (ULift.up m)) k

lemma eval_homogCoordPoly (i k : Fin (n + 1)) (v : AnalyticSpace.complexAffineSpace.{u} n) :
    MvPolynomial.eval (v : ULift.{u} (Fin n) → ℂ) (homogCoordPoly i k) = homogCoord i v k := by
  obtain rfl | ⟨m, rfl⟩ := Fin.eq_self_or_eq_succAbove i k
  · simp [homogCoordPoly, homogCoord]
  · simp [homogCoordPoly, homogCoord, toFin]

variable (e : MvPolynomial (Fin n) ℂ)

/-- The polynomial `x₀ · Σ_m c_m x₀^{d - |m|} ∏ₖ x_{k+1}^{m_k}` in the coordinates of the chart
`i`, `x = homogCoord i v`, `e = Σ_m c_m zᵐ` of total degree `d`. -/
def chartPoly (i : Fin (n + 1)) : MvPolynomial (ULift.{u} (Fin n)) ℂ :=
  homogCoordPoly i 0 * ∑ m ∈ e.support, MvPolynomial.C (e.coeff m) *
    homogCoordPoly i 0 ^ (e.totalDegree - ∑ k, m k) * ∏ k, homogCoordPoly i k.succ ^ m k

/-- The function `v ↦ x₀^{d+1} e(τ v)` on the chart `i`, extended polynomially across `H_∞`. -/
def chartFun (i : Fin (n + 1)) (v : ULift.{u} (Fin n) → ℂ) : ℂ :=
  MvPolynomial.eval v (chartPoly e i)

lemma chartFun_eq (i : Fin (n + 1)) (v : AnalyticSpace.complexAffineSpace.{u} n) :
    chartFun e i v = homogCoord i v 0 * ∑ m ∈ e.support, e.coeff m *
      homogCoord i v 0 ^ (e.totalDegree - ∑ k, m k) * ∏ k, homogCoord i v k.succ ^ m k := by
  simp [chartFun, chartPoly, eval_homogCoordPoly]

lemma chartFun_eq_zero_of_eq_zero (i : Fin (n + 1)) (v : AnalyticSpace.complexAffineSpace.{u} n)
    (h : homogCoord i v 0 = 0) : chartFun e i v = 0 := by
  rw [chartFun_eq, h, zero_mul]

lemma sum_le_totalDegree {m : Fin n →₀ ℕ} (hm : m ∈ e.support) : ∑ k, m k ≤ e.totalDegree := by
  calc ∑ k, m k = m.sum (fun _ e ↦ e) := (Finsupp.sum_fintype m (fun _ e ↦ e) fun _ ↦ rfl).symm
    _ ≤ e.totalDegree := MvPolynomial.le_totalDegree hm

/-- **Homogenisation**: `x₀ Σ_m c_m x₀^{d - |m|} ∏ₖ x_{k+1}^{m_k} = x₀^{d+1} e(x_{k+1} / x₀)` for
`x₀ ≠ 0`. -/
lemma homogenize_eq (x : Fin (n + 1) → ℂ) (hx : x 0 ≠ 0) :
    x 0 * ∑ m ∈ e.support, e.coeff m * x 0 ^ (e.totalDegree - ∑ k, m k) *
      ∏ k, x k.succ ^ m k =
      x 0 ^ (e.totalDegree + 1) * MvPolynomial.eval (dehomogenizeVec 0 x) e := by
  rw [MvPolynomial.eval_eq', Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  have hle := sum_le_totalDegree e hm
  have hprod : ∏ k, dehomogenizeVec 0 x k ^ m k = (∏ k, x k.succ ^ m k) / x 0 ^ ∑ k, m k := by
    simp only [dehomogenizeVec, Fin.succAbove_zero, div_pow]
    rw [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum]
  rw [hprod, pow_sub₀ _ hx hle]
  field_simp
  ring

/-- **Off `H_∞`**, `chartFun e i v = x₀^{d+1} e(τ v)`. -/
lemma chartFun_eq_of_ne (i : Fin (n + 1)) (v : AnalyticSpace.complexAffineSpace.{u} n)
    (h : homogCoord i v 0 ≠ 0) :
    chartFun e i v = homogCoord i v 0 ^ (e.totalDegree + 1) * polyEval e (transition i v) := by
  rw [chartFun_eq, homogenize_eq e _ h]
  rfl

lemma chartFun_ne_zero_iff (i : Fin (n + 1)) (v : AnalyticSpace.complexAffineSpace.{u} n) :
    chartFun e i v ≠ 0 ↔ homogCoord i v 0 ≠ 0 ∧ polyEval e (transition i v) ≠ 0 := by
  by_cases h : homogCoord i v 0 = 0
  · simp [chartFun_eq_zero_of_eq_zero e i v h, h]
  · rw [chartFun_eq_of_ne e i v h]
    simp [h]

lemma differentiable_chartFun (i : Fin (n + 1)) : Differentiable ℂ (chartFun.{u} e i) :=
  fun v ↦ (MvPolynomial.analyticAt_eval _ v).differentiableAt

/-- **The zero set of `chartFun e i` has empty interior**, for `e ≠ 0`. -/
lemma interior_chartFun_eq_zero (he : e ≠ 0) (i : Fin (n + 1)) :
    interior {v | chartFun.{u} e i v = 0} = ∅ := by
  classical
  -- a point of the chart `0` in the chart `i` at which `e` does not vanish
  let hc : (Fin n → ℂ) → Fin (n + 1) → ℂ := fun z ↦ Fin.insertNth (α := fun _ ↦ ℂ) 0 1 z
  let P : MvPolynomial (Fin n) ℂ :=
    Fin.insertNth (α := fun _ ↦ MvPolynomial (Fin n) ℂ) 0 1 (fun m ↦ MvPolynomial.X m) i
  have hP : ∀ z, MvPolynomial.eval z P = hc z i := fun z ↦ by
    obtain rfl | ⟨m, rfl⟩ := Fin.eq_self_or_eq_succAbove 0 i
    · simp [P, hc]
    · simp [P, hc]
  have hP0 : P ≠ 0 := by
    obtain rfl | ⟨m, rfl⟩ := Fin.eq_self_or_eq_succAbove 0 i
    · simp [P]
    · simp [P]
  obtain ⟨z, hz⟩ : ∃ z : Fin n → ℂ, MvPolynomial.eval z e * hc z i ≠ 0 := by
    by_contra! H
    refine mul_ne_zero he hP0 (MvPolynomial.funext fun z ↦ ?_)
    rw [map_mul, map_zero, hP]
    exact H z
  have hz1 : hc z i ≠ 0 := right_ne_zero_of_mul hz
  let v : AnalyticSpace.complexAffineSpace.{u} n := ofFin (dehomogenizeVec i (hc z))
  have hv : homogCoord i v = (hc z i)⁻¹ • hc z := by
    rw [homogCoord, toFin_ofFin]
    exact insertNth_dehomogenizeVec i _ hz1
  have hv0 : homogCoord i v 0 ≠ 0 := by
    rw [hv, Pi.smul_apply, smul_eq_mul]
    exact mul_ne_zero (inv_ne_zero hz1) (by simp [hc])
  have hτ : transition i v = ofFin z := by
    rw [transition, hv, dehomogenizeVec_smul _ _ (inv_ne_zero hz1)]
    exact congrArg ofFin (dehomogenizeVec_insertNth 0 z)
  have hne : chartFun e i v ≠ 0 := by
    rw [chartFun_ne_zero_iff, hτ]
    exact ⟨hv0, left_ne_zero_of_mul hz⟩
  have := AnalyticOnNhd.interior_inter_preimage_zero_eq_empty
    (fun y _ ↦ MvPolynomial.analyticAt_eval (chartPoly e i) y) isPreconnected_univ
    (Set.mem_univ (v : ULift.{u} (Fin n) → ℂ)) hne
  rwa [Set.univ_inter] at this

/-- The open `{chartFun e i ≠ 0}` of the chart `i`: the points off `H_∞ ∪ {e = 0}`. -/
def chartOpens (i : Fin (n + 1)) : (AnalyticSpace.complexAffineSpace.{u} n).Opens :=
  ⟨{v | chartFun e i v ≠ 0},
    isOpen_compl_singleton.preimage (differentiable_chartFun e i).continuous⟩

lemma mem_chartOpens_iff (i : Fin (n + 1)) (v : AnalyticSpace.complexAffineSpace.{u} n) :
    v ∈ chartOpens e i ↔ homogCoord i v 0 ≠ 0 ∧ polyEval e (transition i v) ≠ 0 :=
  chartFun_ne_zero_iff e i v

end

end ComplexAnalytic.ProjectiveCompletion
