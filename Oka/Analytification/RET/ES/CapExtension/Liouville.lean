/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.ES.Evaluation
import Mathlib.LinearAlgebra.Lagrange

/-!
# Coefficients of characteristic polynomials on the cap are polynomials

Keep the notation of `Oka/Analytification/RET/ES/Evaluation.lean`. A function `A` holomorphic on
`{‖w‖ < ρ}` which on the overlap is the `l`-th coefficient of the characteristic polynomial of
functions `φᵢ` on the Kummer covers at infinity, twisted by `wᵏ`, is a polynomial of degree
`≤ k ∑ kᵢ` (`ComplexAnalytic.Cap.exists_polynomial_of_infCoeff`), hence determined by its values at
more than `k ∑ kᵢ` points through Lagrange interpolation
(`ComplexAnalytic.Cap.eq_sum_lagrange_of_infCoeff`).
-/

open CategoryTheory Opposite Topology Set Filter Polynomial Metric

namespace ComplexAnalytic.Cap

open Complex.ProjectiveLineBundle AnnulusDecomposition

noncomputable section

variable {ι : Type*} [Fintype ι] {deg : ι → ℕ+} {k : ℕ} {φ : ι → ℂ → ℂ} {l : ℕ} {ρ : ℝ}

/-- **Liouville on the cap**, polynomial form: `A` is a polynomial of degree `≤ k ∑ kᵢ`. -/
theorem exists_polynomial_of_infCoeff (hρ : 1 < ρ)
    (hφ : ∀ i, DifferentiableOn ℂ (φ i) {u | ‖u ^ (deg i : ℕ)‖ < ρ})
    {A : ℂ → ℂ} (hA : DifferentiableOn ℂ A (ball 0 ρ))
    (hAB : ∀ w ∈ overlap ρ, A w = infCoeff deg k φ l w w) :
    ∃ p : ℂ[X], p.degree < ↑((∑ i, (deg i : ℕ)) * k + 1) ∧
      EqOn A (fun w ↦ p.eval w) (ball 0 ρ) := by
  classical
  have hρ0 : 0 < ρ := zero_lt_one.trans hρ
  have hρi : ρ⁻¹ < 1 := inv_lt_one_of_one_lt₀ hρ
  set d := ∑ i, (deg i : ℕ)
  set B : ℂ → ℂ := fun w ↦ infCoeff deg k φ l w w
  have hS (i : ι) : IsOpen {u : ℂ | ‖u ^ (deg i : ℕ)‖ < ρ} :=
    isOpen_lt (continuous_norm.comp (continuous_pow _)) continuous_const
  have hB (w₀ : ℂ) (hw₀ : ρ⁻¹ < ‖w₀‖) : DifferentiableAt ℂ B w₀ := by
    have hw₀0 : w₀ ≠ 0 := norm_pos_iff.1 ((inv_pos.2 hρ0).trans hw₀)
    have heq : (fun w ↦ infCoeff deg k φ l w₀ w) =ᶠ[𝓝 w₀] B := by
      filter_upwards [isOpen_ne.mem_nhds hw₀0] with w hw
      exact infCoeff_eq deg k φ l hw₀0 hw hw
    refine DifferentiableAt.congr_of_eventuallyEq ?_ heq.symm
    refine BoundedSections.differentiableAt_coeff_prod_X_sub_C _ _ (fun ij _ ↦ ?_) l
    have hk := differentiableAt_kroot (deg ij.1) (w₁ := w₀) (w := w₀)
      (by rw [div_self hw₀0]; exact Complex.one_mem_slitPlane)
    have hne := zeta_pow_mul_kroot_ne_zero (deg ij.1).ne_zero ij.2 hw₀0 hw₀0
    have hφd : DifferentiableAt ℂ (φ ij.1)
        (Kummer.zeta (deg ij.1) ^ (ij.2 : ℕ) * kroot (deg ij.1) w₀ w₀)⁻¹ := by
      refine (hφ ij.1).differentiableAt ((hS ij.1).mem_nhds ?_)
      change ‖_‖ < ρ
      rw [norm_pow_inv_zeta_pow_mul_kroot (deg ij.1).ne_zero ij.2 hw₀0 hw₀0]
      exact inv_lt_of_inv_lt₀ hρ0 hw₀
    exact (differentiableAt_pow k).mul (hφd.comp w₀ ((hk.const_mul _).inv hne))
  set E : ℂ → ℂ := fun w ↦ if ‖w‖ < ρ then A w else B w
  have hEA (w : ℂ) (h : ‖w‖ < ρ) : E w = A w := if_pos h
  have hEB (w : ℂ) (h : ρ⁻¹ < ‖w‖) : E w = B w := by
    by_cases h' : ‖w‖ < ρ
    · rw [hEA w h']
      exact hAB w ⟨h, h'⟩
    · exact if_neg h'
  have hE : Differentiable ℂ E := by
    intro w₀
    by_cases h : ‖w₀‖ < ρ
    · have hn : ball (0 : ℂ) ρ ∈ 𝓝 w₀ := isOpen_ball.mem_nhds (mem_ball_zero_iff.2 h)
      refine (hA.differentiableAt hn).congr_of_eventuallyEq ?_
      filter_upwards [hn] with w hw using hEA w (mem_ball_zero_iff.1 hw)
    · have h' : ρ⁻¹ < ‖w₀‖ := hρi.trans (hρ.trans_le (not_lt.1 h))
      refine (hB w₀ h').congr_of_eventuallyEq ?_
      filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds h'] with w hw
        using hEB w hw
  have hφb (i : ι) : ∃ c, ∀ u ∈ closedBall (0 : ℂ) 1, ‖φ i u‖ ≤ c :=
    (isCompact_closedBall 0 1).exists_bound_of_continuousOn ((hφ i).continuousOn.mono
      fun u hu ↦ by
        change ‖u ^ (deg i : ℕ)‖ < ρ
        rw [norm_pow]
        exact (pow_le_one₀ (norm_nonneg u) (mem_closedBall_zero_iff.1 hu)).trans_lt hρ)
  choose c hc using hφb
  set C₀ := ∑ i, |c i|
  have hC₀ : 0 ≤ C₀ := Finset.sum_nonneg fun i _ ↦ abs_nonneg _
  have hφC (i : ι) (u : ℂ) (hu : ‖u‖ ≤ 1) : ‖φ i u‖ ≤ C₀ :=
    (hc i u (mem_closedBall_zero_iff.2 hu)).trans ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun i ↦ |c i|) (fun j _ ↦ abs_nonneg _) (Finset.mem_univ i)))
  have hBb (w : ℂ) (hw : 1 ≤ ‖w‖) : ‖B w‖ ≤ (1 + C₀) ^ d * (1 + ‖w‖) ^ (d * k) := by
    have hw0 : w ≠ 0 := norm_pos_iff.1 (zero_lt_one.trans_le hw)
    have hcard : (Finset.univ : Finset (Σ i, Fin (deg i))).card = d := by
      simp [d]
    have h₁ := BoundedSections.norm_coeff_prod_X_sub_C_le
      (Finset.univ : Finset (Σ i, Fin (deg i)))
      (fun ij ↦ w ^ k * φ ij.1
        (Kummer.zeta (deg ij.1) ^ (ij.2 : ℕ) * kroot (deg ij.1) w w)⁻¹)
      (M := ‖w‖ ^ k * C₀) (by positivity) (fun ij _ ↦ ?_) l
    · rw [hcard] at h₁
      refine h₁.trans ?_
      rw [pow_mul', ← mul_pow]
      refine pow_le_pow_left₀ (by positivity) ?_ d
      have t₁ : 1 ≤ (1 + ‖w‖) ^ k := one_le_pow₀ (by linarith [norm_nonneg w])
      have t₂ : ‖w‖ ^ k ≤ (1 + ‖w‖) ^ k :=
        pow_le_pow_left₀ (norm_nonneg w) (by linarith) k
      nlinarith [mul_le_mul_of_nonneg_left t₂ hC₀]
    · rw [norm_mul, norm_pow]
      refine mul_le_mul_of_nonneg_left (hφC _ _ ?_) (by positivity)
      have h₂ := norm_pow_inv_zeta_pow_mul_kroot (deg ij.1).ne_zero ij.2 hw0 hw0
      rw [norm_pow] at h₂
      refine (pow_le_one_iff_of_nonneg (norm_nonneg _) (deg ij.1).ne_zero).1 ?_
      rw [h₂]
      exact inv_le_one_of_one_le₀ hw
  obtain ⟨C₂, hC₂⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn
    hE.continuous.continuousOn
  set C := max ((1 + C₀) ^ d) C₂
  have hbound (t : ℂ) : ‖E t‖ ≤ C * (1 + ‖t‖) ^ (d * k) := by
    have h₁ : 1 ≤ (1 + ‖t‖) ^ (d * k) := one_le_pow₀ (by linarith [norm_nonneg t])
    have hC : 0 ≤ C := (by positivity : (0 : ℝ) ≤ (1 + C₀) ^ d).trans (le_max_left _ _)
    by_cases ht : ‖t‖ ≤ 1
    · exact (hC₂ t (mem_closedBall_zero_iff.2 ht)).trans ((le_max_right _ _).trans
        (le_mul_of_one_le_right hC h₁))
    · rw [hEB t (hρi.trans (not_le.1 ht))]
      exact (hBb t (not_le.1 ht).le).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (by positivity))
  obtain ⟨p, hpdeg, hp⟩ := Differentiable.exists_polynomial_eq_of_norm_le_pow hE hbound
  exact ⟨p, hpdeg, fun w hw ↦ by rw [← hEA w (mem_ball_zero_iff.1 hw), hp]⟩

/-- **Lagrange interpolation on the cap**: `A` is determined by its values at more than
`k ∑ kᵢ` distinct points `wᵥ` of `{‖w‖ < ρ}`. -/
theorem eq_sum_lagrange_of_infCoeff (hρ : 1 < ρ)
    (hφ : ∀ i, DifferentiableOn ℂ (φ i) {u | ‖u ^ (deg i : ℕ)‖ < ρ})
    {A : ℂ → ℂ} (hA : DifferentiableOn ℂ A (ball 0 ρ))
    (hAB : ∀ w ∈ overlap ρ, A w = infCoeff deg k φ l w w)
    {M : ℕ} (hM : (∑ i, (deg i : ℕ)) * k < M) {w : Fin M → ℂ} (hw : Function.Injective w)
    (hwρ : ∀ ν, w ν ∈ ball (0 : ℂ) ρ) {z : ℂ} (hz : z ∈ ball (0 : ℂ) ρ) :
    A z = ∑ ν, A (w ν) * (Lagrange.basis Finset.univ w ν).eval z := by
  obtain ⟨p, hpdeg, hp⟩ := exists_polynomial_of_infCoeff hρ hφ hA hAB
  have hdeg : p.degree < (Finset.univ : Finset (Fin M)).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact hpdeg.trans_le (by exact_mod_cast hM)
  have h := Lagrange.eq_interpolate (s := Finset.univ) (v := w) hw.injOn hdeg
  have h1 : A z = p.eval z := hp hz
  rw [h1, h, Lagrange.interpolate_apply, eval_finsetSum]
  refine Finset.sum_congr rfl fun ν _ ↦ ?_
  have h2 : A (w ν) = p.eval (w ν) := hp (hwρ ν)
  rw [eval_mul, eval_C, h2]

end

end ComplexAnalytic.Cap
