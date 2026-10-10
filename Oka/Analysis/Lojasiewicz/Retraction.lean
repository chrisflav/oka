/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Topology.UniformSpace.UniformConvergence
import Oka.Analysis.Lojasiewicz.GradientCurve
import Oka.Analysis.Normed.LocallyContractibleRetract
import Oka.Analysis.ODE.GlobalFlow

/-!
# Łojasiewicz's retraction: the zero set of a function with a gradient inequality is locally
contractible

Let `F : (ι → ℝ) → ℝ` be nonnegative, with a `C¹` gradient `G` (the derivative of `F` at `x` is
`v ↦ ∑ i, G x i * v i`), and suppose that near every zero `p` of `F` the **Łojasiewicz gradient
inequality** `c * F x ^ θ ≤ ‖G x‖` holds for some `0 ≤ θ < 1` and `c > 0`. Then the zero set
`Z = F⁻¹(0)` is locally contractible (`Lojasiewicz.locallyContractibleSpace_zeroSet`).

## The construction (Łojasiewicz)

Fix a zero `p` and a closed ball `B = B̄(p, r₀)` on which the inequality holds.

1. **The field.** The gradient flow `ẋ = -G x` is only good inside `B`, so the field is cut off:
   `V x = -G (clamp x)`, with `clamp` the coordinatewise projection onto the box `B` (sup norm). `V`
   is bounded and globally Lipschitz (`G` is Lipschitz on the compact convex `B`), so it has a
   global flow `φ` with continuous time-`t` maps (`Oka/Analysis/ODE/GlobalFlow.lean`).
2. **Trajectories from a small ball stay in `B`.** By Łojasiewicz's length estimate
   (`Lojasiewicz.norm_sub_le_of_gradientCurve`) a trajectory, as long as it is in `B`, has moved at
   most `C₀ * F(y) ^ (1 - θ)` from its start `y`; choosing `ρ` with `ρ + C₀ * F ^ (1 - θ) < r₀` on
   `B(p, ρ)`, a first-exit-time argument shows trajectories from `B(p, ρ)` never leave `B`.
3. **Uniform convergence.** Along such a trajectory `F` drops at rate `(c ε ^ θ)²` while above `ε`
   (`Lojasiewicz.le_sub_of_gradientCurve`), so `F(φ y t) → 0` uniformly on `B(p, ρ)`, and by the
   length estimate again `φ y N` is uniformly Cauchy. The limit `R` is continuous on `B(p, ρ)`,
   lands in `Z`, and is the identity on `Z` (a trajectory starting in `Z` does not move).
4. **Contraction.** `Oka/Analysis/Normed/LocallyContractibleRetract.lean` turns these local
   retractions into local contractibility.

## Main results

- `Lojasiewicz.exists_retraction`: the local retraction of step 3.
- `Lojasiewicz.locallyContractibleSpace_zeroSet`: **the zero set is locally contractible.**

The application to polynomials is `Oka/Analysis/Lojasiewicz/RealAlgebraic.lean`. Nothing here
proves a gradient inequality: it is a hypothesis.
-/

open Set Filter Topology Metric ContinuousLinearMap

open scoped NNReal

namespace Lojasiewicz

variable {ι : Type*} [Fintype ι] {F : (ι → ℝ) → ℝ} {G : (ι → ℝ) → ι → ℝ}

/-- The coordinatewise projection onto the closed sup-norm ball `B̄(p, r)`. -/
noncomputable def clamp (p : ι → ℝ) (r : ℝ) (x : ι → ℝ) : ι → ℝ :=
  fun i ↦ max (p i - r) (min (p i + r) (x i))

/-- `clamp p r` takes values in the closed ball `B̄(p, r)`. -/
theorem clamp_mem_closedBall (p : ι → ℝ) {r : ℝ} (hr : 0 ≤ r) (x : ι → ℝ) :
    clamp p r x ∈ closedBall p r := by
  rw [mem_closedBall, dist_pi_le_iff hr]
  intro i
  have h1 : p i - r ≤ clamp p r x i := le_max_left _ _
  have h2 : clamp p r x i ≤ p i + r := max_le (by linarith) (min_le_left _ _)
  rw [Real.dist_eq, abs_sub_le_iff]
  constructor <;> linarith

/-- `clamp p r` is the identity on the closed ball `B̄(p, r)`. -/
theorem clamp_eq_self {p : ι → ℝ} {r : ℝ} {x : ι → ℝ} (hx : x ∈ closedBall p r) :
    clamp p r x = x := by
  have hr : 0 ≤ r := dist_nonneg.trans hx
  rw [mem_closedBall, dist_pi_le_iff hr] at hx
  funext i
  have := hx i
  rw [Real.dist_eq, abs_sub_le_iff] at this
  simp only [clamp]
  rw [min_eq_right (by linarith), max_eq_right (by linarith)]

/-- `clamp p r` is `1`-Lipschitz for the sup norm. -/
theorem lipschitzWith_clamp (p : ι → ℝ) (r : ℝ) : LipschitzWith 1 (clamp p r) :=
  LipschitzWith.of_dist_le_mul fun x y ↦ by
    rw [NNReal.coe_one, one_mul]
    refine (dist_pi_le_iff dist_nonneg).2 fun i ↦ ?_
    have hi : LipschitzWith 1 fun x : ι → ℝ ↦ max (p i - r) (min (p i + r) (x i)) :=
      ((LipschitzWith.eval (α := fun _ : ι ↦ ℝ) i).const_min _).const_max _
    simpa [clamp] using hi.dist_le_mul x y

variable (hFG : ∀ x, HasFDerivAt F (∑ i, G x i • proj (R := ℝ) (φ := fun _ ↦ ℝ) i) x)
  (hG : ContDiff ℝ 1 G) (hF0 : ∀ x, 0 ≤ F x)
include hFG hG hF0

/-- **Łojasiewicz's local retraction.** If `F ≥ 0` has a `C¹` gradient `G` satisfying the
gradient inequality `c * F ^ θ ≤ ‖G‖` near a zero `p`, with `0 ≤ θ < 1` and `0 < c`, then some
ball around `p` retracts continuously onto its intersection with the zero set: there is a map
`R`, continuous on the ball, with values in `F⁻¹(0)`, and the identity on `F⁻¹(0)`. -/
theorem exists_retraction {p : ι → ℝ} (hp : F p = 0) {θ c : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hc : 0 < c) (hL : ∀ᶠ x in 𝓝 p, c * F x ^ θ ≤ ‖G x‖) :
    ∃ ρ > 0, ∃ R : (ι → ℝ) → ι → ℝ, ContinuousOn R (ball p ρ) ∧
      MapsTo R (ball p ρ) {x | F x = 0} ∧ ∀ y ∈ ball p ρ, F y = 0 → R y = y := by
  have hθ' : 0 < 1 - θ := sub_pos.2 hθ1
  have hFc : Continuous F := continuous_of_hasGradient hFG
  set C₀ := ((1 - θ) * c)⁻¹ with hC₀
  have hC₀ : 0 < C₀ := inv_pos.2 (mul_pos hθ' hc)
  -- the ball `B` on which the inequality holds
  obtain ⟨r₁, hr₁, hr₁L⟩ := Metric.eventually_nhds_iff.1 hL
  set r₀ := r₁ / 2 with hr₀
  have hr₀0 : 0 < r₀ := half_pos hr₁
  have hS : ∀ x ∈ closedBall p r₀, c * F x ^ θ ≤ ‖G x‖ := fun x hx ↦
    hr₁L (lt_of_le_of_lt (mem_closedBall.1 hx) (half_lt_self hr₁))
  -- Lipschitz constant and bound of `G` on `B`
  obtain ⟨K, hK⟩ := hG.contDiffOn.exists_lipschitzOnWith one_ne_zero (convex_closedBall p r₀)
    (isCompact_closedBall p r₀)
  obtain ⟨M₀, hM₀⟩ := (isCompact_closedBall p r₀).exists_bound_of_continuousOn
    hG.continuous.continuousOn
  -- the cut-off field and its flow
  set V : (ι → ℝ) → ι → ℝ := fun x ↦ -G (clamp p r₀ x) with hVdef
  have hVL : LipschitzWith K V := LipschitzWith.of_dist_le_mul fun x y ↦ by
    simp only [hVdef, dist_neg_neg]
    calc dist (G (clamp p r₀ x)) (G (clamp p r₀ y))
        ≤ K * dist (clamp p r₀ x) (clamp p r₀ y) :=
          hK.dist_le_mul _ (clamp_mem_closedBall p hr₀0.le x) _
            (clamp_mem_closedBall p hr₀0.le y)
      _ ≤ K * dist x y := by
          gcongr
          simpa using (lipschitzWith_clamp p r₀).dist_le_mul x y
  have hVM : ∀ x, ‖V x‖ ≤ Real.toNNReal M₀ := fun x ↦ by
    rw [hVdef, norm_neg]
    exact (hM₀ _ (clamp_mem_closedBall p hr₀0.le x)).trans (Real.le_coe_toNNReal M₀)
  obtain ⟨φ, hφ0, hφD, hφL⟩ := exists_flow_of_lipschitzWith hVL hVM
  have hφc (y : ι → ℝ) : Continuous (φ y) := continuous_iff_continuousAt.2 fun t ↦
    (hφD y t).continuousAt
  have hφV {y : ι → ℝ} {t : ℝ} (ht : φ y t ∈ closedBall p r₀) :
      HasDerivAt (φ y) (-G (φ y t)) t := by
    have := hφD y t
    simp only [hVdef, clamp_eq_self ht] at this
    exact this
  -- the radius `ρ`
  have hg : Continuous fun y ↦ C₀ * F y ^ (1 - θ) :=
    continuous_const.mul (hFc.rpow_const fun _ ↦ Or.inr hθ'.le)
  obtain ⟨ρ₁, hρ₁, hρ₁g⟩ := Metric.continuous_iff.1 hg p (r₀ / 2) (half_pos hr₀0)
  set ρ := min ρ₁ (r₀ / 2) with hρ
  have hρ0 : 0 < ρ := lt_min hρ₁ (half_pos hr₀0)
  have hgy {y : ι → ℝ} (hy : y ∈ ball p ρ) : C₀ * F y ^ (1 - θ) < r₀ / 2 := by
    have := hρ₁g y (lt_of_lt_of_le hy (min_le_left _ _))
    rw [hp, Real.zero_rpow hθ'.ne', mul_zero, Real.dist_eq, sub_zero] at this
    exact (le_abs_self _).trans_lt this
  -- the length estimate along a trajectory, while it stays in `B`
  have hlen {y : ι → ℝ} {a b : ℝ} (hab : a ≤ b)
      (hin : ∀ t ∈ Ico a b, φ y t ∈ closedBall p r₀) :
      ‖φ y b - φ y a‖ ≤ C₀ * (F (φ y a) ^ (1 - θ) - F (φ y b) ^ (1 - θ)) :=
    norm_sub_le_of_gradientCurve hFG (hφc y).continuousOn (fun t ht ↦ hφV (hin t ht)) hS hin
      hF0 hθ1 hc hab
  -- trajectories from `B(p, ρ)` stay in `B(p, r₀)`
  have hstay {y : ι → ℝ} (hy : y ∈ ball p ρ) {t : ℝ} (ht : 0 ≤ t) : φ y t ∈ ball p r₀ := by
    by_contra hout
    set S := Icc 0 t ∩ φ y ⁻¹' (ball p r₀)ᶜ with hSdef
    have hSc : IsClosed S := isClosed_Icc.inter (isOpen_ball.isClosed_compl.preimage (hφc y))
    have hSne : S.Nonempty := ⟨t, ⟨ht, le_rfl⟩, hout⟩
    have hSb : BddBelow S := ⟨0, fun s hs ↦ hs.1.1⟩
    have hτ := hSc.csInf_mem hSne hSb
    set τ := sInf S
    have hin : ∀ s ∈ Ico 0 τ, φ y s ∈ closedBall p r₀ := fun s hs ↦ by
      refine ball_subset_closedBall (by_contra fun hs' ↦ ?_)
      exact absurd (csInf_le hSb ⟨⟨hs.1, hs.2.le.trans hτ.1.2⟩, hs'⟩) (not_le.2 hs.2)
    have h1 := hlen hτ.1.1 hin
    rw [hφ0] at h1
    have h2 : C₀ * (F y ^ (1 - θ) - F (φ y τ) ^ (1 - θ)) ≤ C₀ * F y ^ (1 - θ) := by
      have := Real.rpow_nonneg (hF0 (φ y τ)) (1 - θ)
      nlinarith
    have hyp : dist y p < r₀ / 2 := lt_of_lt_of_le hy (min_le_right _ _)
    refine hτ.2 (mem_ball.2 ?_)
    calc dist (φ y τ) p ≤ dist (φ y τ) y + dist y p := dist_triangle _ _ _
      _ < r₀ / 2 + r₀ / 2 := by
          rw [dist_eq_norm]
          exact add_lt_add_of_le_of_lt (h1.trans (h2.trans (hgy hy).le)) hyp
      _ = r₀ := add_halves r₀
  have hinB {y : ι → ℝ} (hy : y ∈ ball p ρ) (a b : ℝ) (ha : 0 ≤ a) :
      ∀ t ∈ Ico a b, φ y t ∈ closedBall p r₀ := fun t ht ↦
    ball_subset_closedBall (hstay hy (ha.trans ht.1))
  -- uniform decay of `F` along trajectories
  obtain ⟨A, hA⟩ := (isCompact_closedBall p ρ).exists_bound_of_continuousOn hFc.continuousOn
  have hdecay : ∀ ε > 0, ∃ T₀ : ℝ, ∀ y ∈ ball p ρ, ∀ t ≥ T₀, F (φ y t) < ε := by
    intro ε hε
    set κ := (c * ε ^ θ) ^ 2 with hκ
    have hκ0 : 0 < κ := pow_pos (mul_pos hc (Real.rpow_pos_of_pos hε θ)) 2
    refine ⟨max 0 (A / κ + 1), fun y hy t ht ↦ by_contra fun hge ↦ ?_⟩
    rw [not_lt] at hge
    have ht0 : 0 ≤ t := (le_max_left _ _).trans ht
    have hanti := antitoneOn_of_gradientCurve hFG (hφc y).continuousOn
      (fun s hs ↦ hφV (hinB hy 0 t le_rfl s hs))
    have h := le_sub_of_gradientCurve hFG (hφc y).continuousOn
      (fun s hs ↦ hφV (hinB hy 0 t le_rfl s hs)) hS (hinB hy 0 t le_rfl) hθ0 hc.le hε.le
      (fun s hs ↦ hge.trans (hanti ⟨hs.1, hs.2.le⟩ ⟨ht0, le_rfl⟩ hs.2.le)) ht0
    rw [hφ0, sub_zero] at h
    have hFy : F y ≤ A := by
      have := hA y (ball_subset_closedBall hy)
      rwa [Real.norm_eq_abs, abs_of_nonneg (hF0 y)] at this
    have hκt : A + κ ≤ κ * t := by
      have : A / κ + 1 ≤ t := (le_max_right _ _).trans ht
      have := mul_le_mul_of_nonneg_left this hκ0.le
      rwa [mul_add, mul_div_cancel₀ _ hκ0.ne', mul_one] at this
    linarith
  -- the continuity of `s ↦ C₀ * s ^ (1 - θ)` at `0`
  have hpow : ∀ ε > 0, ∃ δ > 0, ∀ s : ℝ, 0 ≤ s → s < δ → C₀ * s ^ (1 - θ) < ε := by
    intro ε hε
    have hc' : Continuous fun s : ℝ ↦ C₀ * s ^ (1 - θ) :=
      continuous_const.mul (continuous_id.rpow_const fun _ ↦ Or.inr hθ'.le)
    obtain ⟨δ, hδ, h⟩ := Metric.continuous_iff.1 hc' 0 ε hε
    refine ⟨δ, hδ, fun s hs hsδ ↦ ?_⟩
    have := h s (by rwa [Real.dist_eq, sub_zero, abs_of_nonneg hs])
    rw [Real.zero_rpow hθ'.ne', mul_zero, Real.dist_eq, sub_zero] at this
    exact (le_abs_self _).trans_lt this
  -- the bound between two times
  have hstep {y : ι → ℝ} (hy : y ∈ ball p ρ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
      dist (φ y b) (φ y a) ≤ C₀ * F (φ y a) ^ (1 - θ) := by
    rw [dist_eq_norm]
    refine (hlen hab (hinB hy a b ha)).trans ?_
    have := Real.rpow_nonneg (hF0 (φ y b)) (1 - θ)
    nlinarith
  -- uniform smallness of the bound
  have hsmall : ∀ ε > 0, ∃ N₀ : ℕ, ∀ y ∈ ball p ρ, ∀ N : ℕ, N₀ ≤ N →
      C₀ * F (φ y N) ^ (1 - θ) < ε := by
    intro ε hε
    obtain ⟨δ, hδ, hδε⟩ := hpow ε hε
    obtain ⟨T₀, hT₀⟩ := hdecay δ hδ
    obtain ⟨N₀, hN₀⟩ := exists_nat_ge T₀
    exact ⟨N₀, fun y hy N hN ↦ hδε _ (hF0 _)
      (hT₀ y hy N (hN₀.trans (Nat.cast_le.2 hN)))⟩
  -- the limit map
  have hcauchy {y : ι → ℝ} (hy : y ∈ ball p ρ) : CauchySeq fun N : ℕ ↦ φ y N := by
    refine Metric.cauchySeq_iff'.2 fun ε hε ↦ ?_
    obtain ⟨N₀, hN₀⟩ := hsmall ε hε
    exact ⟨N₀, fun n hn ↦ (hstep hy (Nat.cast_nonneg _) (Nat.cast_le.2 hn)).trans_lt
      (hN₀ y hy N₀ le_rfl)⟩
  set R : (ι → ℝ) → ι → ℝ := fun y ↦ limUnder atTop fun N : ℕ ↦ φ y N with hRdef
  have hRlim {y : ι → ℝ} (hy : y ∈ ball p ρ) :
      Tendsto (fun N : ℕ ↦ φ y N) atTop (𝓝 (R y)) :=
    (hcauchy hy).tendsto_limUnder
  have hRdist {y : ι → ℝ} (hy : y ∈ ball p ρ) (N : ℕ) :
      dist (R y) (φ y N) ≤ C₀ * F (φ y N) ^ (1 - θ) :=
    le_of_tendsto ((hRlim hy).dist tendsto_const_nhds)
      (eventually_atTop.2 ⟨N, fun n hn ↦
        hstep hy (Nat.cast_nonneg _) (Nat.cast_le.2 hn)⟩)
  refine ⟨ρ, hρ0, R, ?_, fun y hy ↦ ?_, fun y hy hy0 ↦ ?_⟩
  · -- continuity, by uniform convergence
    have hU : TendstoUniformlyOn (fun (N : ℕ) y ↦ φ y N) R atTop (ball p ρ) := by
      refine Metric.tendstoUniformlyOn_iff.2 fun ε hε ↦ ?_
      obtain ⟨N₀, hN₀⟩ := hsmall ε hε
      exact eventually_atTop.2 ⟨N₀, fun N hN y hy ↦ (hRdist hy N).trans_lt (hN₀ y hy N hN)⟩
    exact hU.continuousOn (Eventually.of_forall (f := atTop) fun N ↦
      (continuous_flow_of_lipschitzWith hφL (Nat.cast_nonneg N)).continuousOn).frequently
  · -- the limit is a zero
    have h1 : Tendsto (fun N : ℕ ↦ F (φ y N)) atTop (𝓝 (F (R y))) :=
      (hFc.tendsto _).comp (hRlim hy)
    have h2 : Tendsto (fun N : ℕ ↦ F (φ y N)) atTop (𝓝 0) := by
      refine Metric.tendsto_atTop.2 fun ε hε ↦ ?_
      obtain ⟨T₀, hT₀⟩ := hdecay ε hε
      obtain ⟨N₀, hN₀⟩ := exists_nat_ge T₀
      refine ⟨N₀, fun N hN ↦ ?_⟩
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (hF0 _)]
      exact hT₀ y hy N (hN₀.trans (Nat.cast_le.2 hN))
    exact tendsto_nhds_unique h1 h2
  · -- the identity on the zero set
    have := hRdist hy 0
    rw [Nat.cast_zero, hφ0, hy0, Real.zero_rpow hθ'.ne', mul_zero] at this
    exact dist_le_zero.1 this

/-- **The zero set of a nonnegative function with a `C¹` gradient satisfying the Łojasiewicz
gradient inequality near each of its zeros is locally contractible.** -/
theorem locallyContractibleSpace_zeroSet
    (hL : ∀ p, F p = 0 → ∃ θ : ℝ, 0 ≤ θ ∧ θ < 1 ∧ ∃ c : ℝ, 0 < c ∧
      ∀ᶠ x in 𝓝 p, c * F x ^ θ ≤ ‖G x‖) :
    LocallyContractibleSpace {x // F x = 0} :=
  locallyContractibleSpace_of_forall_retraction (Z := {x | F x = 0}) fun p hp ↦ by
    obtain ⟨θ, hθ0, hθ1, c, hc, hpL⟩ := hL p hp
    exact exists_retraction hFG hG hF0 hp hθ0 hθ1 hc hpL

end Lojasiewicz
