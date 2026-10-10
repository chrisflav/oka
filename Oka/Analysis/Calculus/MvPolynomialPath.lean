/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Algebra.MvPolynomial

/-!
# Variation of a real polynomial along a monotone path

For a real polynomial `f` in finitely many variables:

* `MvPolynomial.hasDerivAt_eval_line`: along a line `s ↦ z + s • v`, the derivative of `f` is
  `∑ i, v i * ∂ᵢ f`, where `∂ᵢ f = MvPolynomial.pderiv i f` is the formal partial derivative;
* `MvPolynomial.abs_eval_sub_le`: if all `|∂ᵢ f| ≤ K` on the segment `[z, y]`, then
  `|f y - f z| ≤ K * ∑ i, |y i - z i|`;
* `MvPolynomial.abs_eval_sub_le_of_path`: if `x : ℝ → ℝ^ι` is continuous on `[s, t]`, every
  coordinate of `x` is monotone or antitone on `[s, t]`, and all `|∂ᵢ f (x u)| ≤ K` for
  `u ∈ [s, t]`, then `|f (x t) - f (x s)| ≤ K * ∑ i, |x t i - x s i|` — the integral of `∇f` along
  the path is bounded by `K` times the `ℓ¹`-length of the path, which equals the right-hand side
  for paths with monotone coordinates.

The last statement is the form in which the Łojasiewicz gradient inequality is derived from the
curve of minimisers of `‖∇f‖` on the level sets of `f`. Nothing here is in Mathlib (which does
not relate `MvPolynomial.pderiv` to analytic derivatives).
-/

open Set Filter Topology

namespace MvPolynomial

variable {ι : Type*} [Fintype ι]

/-- The derivative of a real polynomial along the line `s ↦ z + s • v`. -/
theorem hasDerivAt_eval_line (f : MvPolynomial ι ℝ) (z v : ι → ℝ) (s : ℝ) :
    HasDerivAt (fun s => eval (z + s • v) f)
      (∑ i, v i * eval (z + s • v) (pderiv i f)) s := by
  classical
  induction f using MvPolynomial.induction_on with
  | C a => simpa using hasDerivAt_const s a
  | add p q hp hq =>
    have := hp.add hq
    simp only [map_add, mul_add, Finset.sum_add_distrib]
    exact this
  | mul_X p j hp =>
    have hX : HasDerivAt (fun s => z j + s * v j) (v j) s := by
      simpa using (hasDerivAt_mul_const (v j)).const_add (z j)
    have hfun : (fun s => eval (z + s • v) (p * X j)) =
        fun s => eval (z + s • v) p * (z j + s * v j) := by
      funext s
      simp
    rw [hfun]
    refine (hp.mul hX).congr_deriv ?_
    simp only [pderiv_mul, pderiv_X, map_add, map_mul, eval_X, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, mul_add, Finset.sum_add_distrib, Finset.sum_mul]
    congr 1
    · congr 1 <;> exact Finset.sum_congr rfl fun i _ => by ring
    · rw [Finset.sum_eq_single j]
      · simp [mul_comm]
      · intro i _ hij
        simp [hij.symm]
      · simp

/-- **Mean value inequality** for real polynomials with the `ℓ¹`-norm of the displacement. -/
theorem abs_eval_sub_le (f : MvPolynomial ι ℝ) {y z : ι → ℝ} {K : ℝ}
    (hK : ∀ s ∈ Icc (0 : ℝ) 1, ∀ i, |eval (z + s • (y - z)) (pderiv i f)| ≤ K) :
    |eval y f - eval z f| ≤ K * ∑ i, |y i - z i| := by
  have hder : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt (fun s => eval (z + s • (y - z)) f)
      (∑ i, (y - z) i * eval (z + s • (y - z)) (pderiv i f)) (Icc 0 1) s :=
    fun s _ => (hasDerivAt_eval_line f z (y - z) s).hasDerivWithinAt
  have hbound : ∀ s ∈ Ico (0 : ℝ) 1,
      ‖∑ i, (y - z) i * eval (z + s • (y - z)) (pderiv i f)‖ ≤ K * ∑ i, |y i - z i| := by
    intro s hs
    rw [Real.norm_eq_abs, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hK s (Ico_subset_Icc_self hs) i) (abs_nonneg _)
  have := norm_image_sub_le_of_norm_deriv_le_segment' hder hbound 1 ⟨zero_le_one, le_rfl⟩
  simpa using this

/-- **Variation along a monotone path.** If `x` is continuous on `[s, t]` with monotone or
antitone coordinates and all partial derivatives of `f` are bounded by `K` along `x`, then
`|f (x t) - f (x s)| ≤ K * ∑ i, |x t i - x s i|`. -/
theorem abs_eval_sub_le_of_path (f : MvPolynomial ι ℝ) {x : ℝ → ι → ℝ} {s t K : ℝ} (hst : s ≤ t)
    (hx : ContinuousOn x (Icc s t))
    (hmono : ∀ i, MonotoneOn (fun u => x u i) (Icc s t) ∨ AntitoneOn (fun u => x u i) (Icc s t))
    (hK : ∀ u ∈ Icc s t, ∀ i, |eval (x u) (pderiv i f)| ≤ K) :
    |eval (x t) f - eval (x s) f| ≤ K * ∑ i, |x t i - x s i| := by
  set V : ℝ → ℝ := fun u => ∑ i, |x u i - x s i|
  -- additivity of the variation along monotone coordinates
  have hadd : ∀ u u', u ∈ Icc s t → u' ∈ Icc s t → u ≤ u' →
      V u' = V u + ∑ i, |x u' i - x u i| := by
    intro u u' hu hu' huu'
    simp only [V, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hsu : s ≤ u := hu.1
    rcases hmono i with hm | hm
    · have h1 := hm ⟨le_rfl, hst⟩ hu hsu
      have h2 := hm hu hu' huu'
      simp only at h1 h2
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
      ring
    · have h1 := hm ⟨le_rfl, hst⟩ hu hsu
      have h2 := hm hu hu' huu'
      simp only at h1 h2
      rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
      ring
  have hF : ContinuousOn (fun u => eval (x u) f) (Icc s t) :=
    (MvPolynomial.continuous_eval f).comp_continuousOn hx
  have hV : ContinuousOn V (Icc s t) :=
    continuousOn_finsetSum _ fun i _ =>
      (((continuous_apply i).comp_continuousOn hx).sub continuousOn_const).abs
  -- the estimate with an arbitrary slack `ε`
  have key : ∀ ε > 0, |eval (x t) f - eval (x s) f| ≤ (K + ε) * V t := by
    intro ε hε
    set A := {u | |eval (x u) f - eval (x s) f| ≤ (K + ε) * V u}
    have hcl : IsClosed (A ∩ Icc s t) := by
      have := ContinuousOn.preimage_isClosed_of_isClosed (f := fun u =>
        (K + ε) * V u - |eval (x u) f - eval (x s) f|) ((continuousOn_const.mul hV).sub
        (hF.sub continuousOn_const).abs) isClosed_Icc (isClosed_Ici (a := 0))
      convert this using 1
      ext u
      simp [A, and_comm]
    have hsA : s ∈ A := by simp [A, V]
    have hstep : ∀ u ∈ A ∩ Ico s t, A ∈ 𝓝[>] u := by
      rintro u ⟨huA, hu⟩
      have huI : u ∈ Icc s t := Ico_subset_Icc_self hu
      -- near `x u`, all partial derivatives are `< K + ε`
      have hnear : ∀ᶠ y in 𝓝 (x u), ∀ i, |eval y (pderiv i f)| < K + ε := by
        refine Filter.eventually_all.2 fun i => ?_
        have hc : Continuous fun y => |eval y (pderiv i f)| :=
          (MvPolynomial.continuous_eval _).abs
        exact hc.continuousAt.eventually_lt continuousAt_const
          ((hK u huI i).trans_lt (lt_add_of_pos_right K hε))
      obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 hnear
      have h1 : ∀ᶠ u' in 𝓝 u, u' ∈ Icc s t → x u' ∈ Metric.ball (x u) r :=
        eventually_nhdsWithin_iff.1 (hx u huI (Metric.ball_mem_nhds _ hr))
      have h2 : ∀ᶠ u' in 𝓝[>] u, u' ∈ Ioo u t := Ioo_mem_nhdsGT hu.2
      filter_upwards [h1.filter_mono nhdsWithin_le_nhds, h2] with u' hu'1 hu'2
      have hu'I : u' ∈ Icc s t := ⟨hu.1.trans hu'2.1.le, hu'2.2.le⟩
      have hxu' := hu'1 hu'I
      -- mean value inequality on the segment `[x u, x u']`
      have hmv := abs_eval_sub_le f (y := x u') (z := x u) (K := K + ε) fun l hl i => by
        refine (hball _ ?_ i).le
        rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg hl.1]
        rw [Metric.mem_ball, dist_eq_norm] at hxu'
        nlinarith [norm_nonneg (x u' - x u), hl.2]
      simp only [A, mem_setOf_eq] at huA ⊢
      rw [hadd u u' huI hu'I hu'2.1.le, mul_add]
      calc |eval (x u') f - eval (x s) f|
          ≤ |eval (x u) f - eval (x s) f| + |eval (x u') f - eval (x u) f| := by
            exact (abs_sub_le _ (eval (x u) f) _).trans_eq (add_comm _ _)
        _ ≤ (K + ε) * V u + (K + ε) * ∑ i, |x u' i - x u i| := add_le_add huA hmv
    have := hcl.Icc_subset_of_forall_mem_nhdsWithin hsA hstep ⟨hst, le_rfl⟩
    exact this
  -- let `ε → 0`
  have hV0 : 0 ≤ V t := Finset.sum_nonneg fun i _ => abs_nonneg _
  by_contra hlt
  push Not at hlt
  set D := |eval (x t) f - eval (x s) f| - K * V t
  have hD : 0 < D := by simp only [D]; linarith
  have := key (D / (2 * (V t + 1))) (div_pos hD (by linarith))
  have h3 : D / (2 * (V t + 1)) * V t ≤ D / 2 := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by linarith) (by norm_num)]
    nlinarith
  nlinarith
end MvPolynomial
