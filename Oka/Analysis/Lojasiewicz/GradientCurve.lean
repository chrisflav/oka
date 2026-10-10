/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Normed.Lp.PiLp

/-!
# Gradient curves of a nonnegative function: energy decay and Łojasiewicz's length estimate

Let `F : (ι → ℝ) → ℝ` be nonnegative and differentiable, with gradient `G`: the derivative of `F`
at `x` is `v ↦ ∑ i, G x i * v i`. A *gradient curve* is a curve `γ` with `γ' = -G ∘ γ`. Along it
the energy `F ∘ γ` has derivative `-∑ i, (G (γ t) i)²`, so it decreases. If moreover the curve
stays in a region where the **Łojasiewicz gradient inequality** `c * F x ^ θ ≤ ‖G x‖` holds, with
`0 ≤ θ < 1` and `c > 0`, then:

* its length is controlled by the energy it loses:
  `‖γ b - γ a‖ ≤ ((1 - θ) * c)⁻¹ * (F (γ a) ^ (1 - θ) - F (γ b) ^ (1 - θ))`
  (`Lojasiewicz.norm_sub_le_of_gradientCurve`), which is Łojasiewicz's argument: the derivative
  of `F (γ t) ^ (1 - θ)` dominates the speed;
* the energy decreases at a definite rate while it stays above a level `ε`
  (`Lojasiewicz.le_sub_of_gradientCurve`).

Norms are sup norms on `ι → ℝ`; the only place the Euclidean structure enters is
`Lojasiewicz.norm_sq_le_sum_sq`, `‖w‖² ≤ ∑ i, w i ²`.

Nothing here constructs a gradient curve, and the curves are only assumed to satisfy the
differential equation on a half-open interval `[a, b)` and to be continuous on `[a, b]`; the
construction, and the use of these estimates to build a retraction onto `F⁻¹(0)`, is in
`Oka/Analysis/Lojasiewicz/Retraction.lean`.
-/

open Set Filter Topology ContinuousLinearMap

namespace Lojasiewicz

variable {ι : Type*} [Fintype ι]

/-- The sup norm squared is at most the sum of the squares of the coordinates. -/
theorem norm_sq_le_sum_sq (w : ι → ℝ) : ‖w‖ ^ 2 ≤ ∑ i, w i ^ 2 := by
  have h : ‖w‖ ≤ √(∑ i, w i ^ 2) :=
    (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i ↦ by
      rw [Real.norm_eq_abs]
      exact Real.abs_le_sqrt
        (Finset.single_le_sum (fun j _ ↦ sq_nonneg (w j)) (Finset.mem_univ i))
  calc ‖w‖ ^ 2 ≤ √(∑ i, w i ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = ∑ i, w i ^ 2 := Real.sq_sqrt (Finset.sum_nonneg fun j _ ↦ sq_nonneg (w j))

variable {F : (ι → ℝ) → ℝ} {G : (ι → ℝ) → ι → ℝ}
  (hFG : ∀ x, HasFDerivAt F (∑ i, G x i • proj (R := ℝ) (φ := fun _ ↦ ℝ) i) x)
include hFG

/-- A function with gradient `G` everywhere is continuous. -/
theorem continuous_of_hasGradient : Continuous F :=
  continuous_iff_continuousAt.2 fun x ↦ (hFG x).continuousAt

/-- **The gradient of a nonnegative function vanishes on its zero set**, which is the set of its
minima. -/
theorem gradient_eq_zero_of_eq_zero (hF0 : ∀ x, 0 ≤ F x) {x : ι → ℝ} (hx : F x = 0) :
    G x = 0 := by
  have hmin : IsLocalMin F x := Eventually.of_forall fun y ↦ hx ▸ hF0 y
  have h := hmin.hasFDerivAt_eq_zero (hFG x)
  classical
  funext j
  have := congrArg (fun L : (ι → ℝ) →L[ℝ] ℝ ↦ L (Pi.single j 1)) h
  simpa [Pi.single_apply] using this

/-- **The energy derivative along a gradient curve**: if `γ' t = -G (γ t)`, then
`(F ∘ γ)' t = -∑ i, (G (γ t) i)²`. -/
theorem hasDerivAt_comp_of_gradientCurve {γ : ℝ → ι → ℝ} {t : ℝ}
    (hγ : HasDerivAt γ (-G (γ t)) t) :
    HasDerivAt (fun s ↦ F (γ s)) (-∑ i, G (γ t) i ^ 2) t :=
  ((hFG (γ t)).comp_hasDerivAt t hγ).congr_deriv (by
    simp [Finset.sum_neg_distrib, sq])

variable {γ : ℝ → ι → ℝ} {a b : ℝ} (hγc : ContinuousOn γ (Icc a b))
  (hγ : ∀ t ∈ Ico a b, HasDerivAt γ (-G (γ t)) t)
include hγc hγ

/-- **The energy decreases along a gradient curve.** -/
theorem antitoneOn_of_gradientCurve : AntitoneOn (fun t ↦ F (γ t)) (Icc a b) := by
  intro s hs t ht hst
  refine image_le_of_deriv_right_le_deriv_boundary (a := s) (b := b)
    (f' := fun u ↦ -∑ i, G (γ u) i ^ 2) (B := fun _ ↦ F (γ s)) (B' := fun _ ↦ 0)
    ((continuous_of_hasGradient hFG).comp_continuousOn
      (hγc.mono (Icc_subset_Icc_left hs.1)))
    (fun u hu ↦ (hasDerivAt_comp_of_gradientCurve hFG
      (hγ u ⟨hs.1.trans hu.1, hu.2⟩)).hasDerivWithinAt)
    le_rfl continuousOn_const (fun _ _ ↦ hasDerivWithinAt_const _ _ _)
    (fun u _ ↦ neg_nonpos.2 (Finset.sum_nonneg fun i _ ↦ sq_nonneg _)) ⟨hst, ht.2⟩

variable {θ c : ℝ} {S : Set (ι → ℝ)} (hS : ∀ x ∈ S, c * F x ^ θ ≤ ‖G x‖)
  (hγS : ∀ t ∈ Ico a b, γ t ∈ S)
include hS hγS

/-- **Łojasiewicz's length estimate.** Along a gradient curve of a nonnegative function, staying
in a region where `c * F ^ θ ≤ ‖G‖` with `0 ≤ θ < 1` and `0 < c`, the displacement is at most
`((1 - θ) * c)⁻¹` times the drop of `F ^ (1 - θ)`. -/
theorem norm_sub_le_of_gradientCurve (hF0 : ∀ x, 0 ≤ F x) (hθ : θ < 1) (hc : 0 < c)
    (hab : a ≤ b) :
    ‖γ b - γ a‖ ≤ ((1 - θ) * c)⁻¹ * (F (γ a) ^ (1 - θ) - F (γ b) ^ (1 - θ)) := by
  classical
  have hθ' : 0 < 1 - θ := sub_pos.2 hθ
  set C := ((1 - θ) * c)⁻¹ with hC
  have hC0 : 0 < C := inv_pos.2 (mul_pos hθ' hc)
  have hFc := continuous_of_hasGradient hFG
  have hanti := antitoneOn_of_gradientCurve hFG hγc hγ
  set B : ℝ → ℝ := fun t ↦ C * (F (γ a) ^ (1 - θ) - F (γ t) ^ (1 - θ)) with hB
  set B' : ℝ → ℝ := fun t ↦
    if F (γ t) = 0 then 0 else C * -((-∑ i, G (γ t) i ^ 2) * (1 - θ) * F (γ t) ^ (1 - θ - 1))
    with hB'
  refine image_norm_le_of_norm_deriv_right_le_deriv_boundary' (a := a) (b := b)
    (f := fun t ↦ γ t - γ a) (f' := fun t ↦ -G (γ t)) (B := B) (B' := B')
    (hγc.sub continuousOn_const)
    (fun t ht ↦ ((hγ t ht).sub_const (γ a)).hasDerivWithinAt) (by simp [hB])
    (continuousOn_const.mul (continuousOn_const.sub
      ((hFc.comp_continuousOn hγc).rpow_const fun _ _ ↦ Or.inr hθ'.le))) ?_ ?_
    ⟨hab, le_rfl⟩
  · intro t ht
    by_cases h0 : F (γ t) = 0
    · simp only [hB', h0, if_true]
      refine (hasDerivWithinAt_const t (Ici t) (B t)).congr_of_eventuallyEq ?_ rfl
      filter_upwards [Ico_mem_nhdsGE ht.2] with u hu
      have hu0 : F (γ u) = 0 :=
        le_antisymm (h0 ▸ hanti ⟨ht.1, ht.2.le⟩ ⟨ht.1.trans hu.1, hu.2.le⟩ hu.1) (hF0 _)
      simp [hB, hu0, h0]
    · simp only [hB', h0, if_false]
      exact (((hasDerivAt_comp_of_gradientCurve hFG (hγ t ht)).rpow_const
        (Or.inl h0)).const_sub _ |>.const_mul C).hasDerivWithinAt
  · intro t ht
    by_cases h0 : F (γ t) = 0
    · simp [hB', h0, gradient_eq_zero_of_eq_zero hFG hF0 h0]
    · simp only [hB', h0, if_false, norm_neg]
      have hpos : 0 < F (γ t) := lt_of_le_of_ne (hF0 _) (Ne.symm h0)
      have hpθ : 0 < F (γ t) ^ θ := Real.rpow_pos_of_pos hpos θ
      have hL := hS _ (hγS t ht)
      have hcp : 0 < c * F (γ t) ^ θ := mul_pos hc hpθ
      have hGpos : 0 < ‖G (γ t)‖ := hcp.trans_le hL
      have hsq := norm_sq_le_sum_sq (G (γ t))
      have hexp : F (γ t) ^ (1 - θ - 1) = (F (γ t) ^ θ)⁻¹ := by
        rw [show 1 - θ - 1 = -θ by ring, Real.rpow_neg (hF0 _)]
      have hrw : C * -((-∑ i, G (γ t) i ^ 2) * (1 - θ) * F (γ t) ^ (1 - θ - 1)) =
          (∑ i, G (γ t) i ^ 2) / (c * F (γ t) ^ θ) := by
        rw [hexp, hC]
        field_simp
      rw [hrw]
      calc ‖G (γ t)‖ = ‖G (γ t)‖ ^ 2 / ‖G (γ t)‖ := by field_simp
        _ ≤ ‖G (γ t)‖ ^ 2 / (c * F (γ t) ^ θ) :=
          div_le_div_of_nonneg_left (sq_nonneg _) hcp hL
        _ ≤ (∑ i, G (γ t) i ^ 2) / (c * F (γ t) ^ θ) :=
          div_le_div_of_nonneg_right hsq hcp.le

/-- **The energy drops at a definite rate while it stays above a level.** Along a gradient curve
staying in a region where `c * F ^ θ ≤ ‖G‖`, if `ε ≤ F (γ t)` on `[a, b)` with `0 ≤ ε` and
`0 ≤ c`, then `F (γ b) ≤ F (γ a) - (c * ε ^ θ) ^ 2 * (b - a)`. -/
theorem le_sub_of_gradientCurve (hθ : 0 ≤ θ) (hc : 0 ≤ c) {ε : ℝ} (hε : 0 ≤ ε)
    (hεF : ∀ t ∈ Ico a b, ε ≤ F (γ t)) (hab : a ≤ b) :
    F (γ b) ≤ F (γ a) - (c * ε ^ θ) ^ 2 * (b - a) := by
  refine image_le_of_deriv_right_le_deriv_boundary (a := a) (b := b)
    (f' := fun u ↦ -∑ i, G (γ u) i ^ 2) (B := fun t ↦ F (γ a) - (c * ε ^ θ) ^ 2 * (t - a))
    (B' := fun _ ↦ -(c * ε ^ θ) ^ 2)
    ((continuous_of_hasGradient hFG).comp_continuousOn hγc)
    (fun u hu ↦ (hasDerivAt_comp_of_gradientCurve hFG (hγ u hu)).hasDerivWithinAt)
    (by simp) (by fun_prop) (fun u _ ↦ ?_) (fun u hu ↦ ?_) ⟨hab, le_rfl⟩
  · exact (((hasDerivAt_id u).sub_const a).const_mul ((c * ε ^ θ) ^ 2) |>.const_sub
      (F (γ a))).hasDerivWithinAt.congr_deriv (by ring)
  · have h1 : c * ε ^ θ ≤ ‖G (γ u)‖ :=
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hε (hεF u hu) hθ) hc).trans
        (hS _ (hγS u hu))
    have h2 : (c * ε ^ θ) ^ 2 ≤ ‖G (γ u)‖ ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg hc (Real.rpow_nonneg hε θ)) h1 2
    linarith [norm_sq_le_sum_sq (G (γ u))]

end Lojasiewicz
