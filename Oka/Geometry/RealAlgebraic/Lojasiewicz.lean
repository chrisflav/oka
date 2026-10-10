/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Oka.Analysis.Calculus.MvPolynomialPath
import Oka.Geometry.RealAlgebraic.Semialgebraic.Choice
import Oka.Geometry.RealAlgebraic.Semialgebraic.Growth
import Oka.Geometry.RealAlgebraic.Semialgebraic.Monotonicity

/-!
# The Łojasiewicz gradient inequality for real polynomials

**Theorem** (`MvPolynomial.exists_lojasiewicz_gradient`, Łojasiewicz 1963). Let `f` be a real
polynomial in `n` variables and `p` a zero of `f`. There are `θ ∈ [0, 1)` and `c > 0` such that
`c * |f x| ^ θ ≤ ‖∇f x‖` for all `x` near `p` (sup norm on `ℝⁿ`).

## Proof

Write `B` for the closed Euclidean unit ball around `p` and `G = ∑ᵢ (∂ᵢ f)²`. For `u > 0` let
`M u` be the set of minimisers of `G` on the compact fibre `B ∩ {f = u}`
(`exists_pos_side`; the case `f < 0` follows by applying it to `-f`).

1. By o-minimality, either `f` takes no value in some `(0, η)` on `B` (and there is nothing to
   prove), or all fibres over `(0, η₀)` are nonempty.
2. The lexicographically smallest point `x u` of `M u` is a semialgebraic curve
   (`IsSemialgebraicFun.lexMin_coord`). By the monotonicity theorem
   (`IsSemialgebraicFun.exists_continuousOn_monotoneOn`) it is continuous with monotone
   coordinates on some `(0, b₁)`; its coordinates have limits `q i` at `0⁺`, and by the Hölder
   estimate (`IsSemialgebraicFun.exists_pow_le`) `|x t i - q i| ^ N ≤ t` for small `t`.
3. Put `θ = 1 - 1 / (2N)`. The set `E` of `u > 0` such that `G ^ N < u ^ (2N - 1)` somewhere
   on the fibre over `u` is semialgebraic. If `E` contained some `(0, η₃)`, then along the curve
   `|∂ᵢ f (x u)| < u ^ θ`, and integrating `∇f` along `x` from `t / 2` to `t`
   (`MvPolynomial.abs_eval_sub_le_of_path`) would give
   `t / 2 ≤ t ^ θ * 2n * t ^ (1 / N)`, impossible for small `t`. Hence `E` avoids some
   `(0, η₃)`, which is the inequality `f ^ (2N - 1) ≤ G ^ N` near `p` on `{f > 0}`.

The ingredients are the Tarski–Seidenberg theorem (`IsSemialgebraic.exists_pi`), o-minimality of
the semialgebraic subsets of `ℝ`, the monotonicity theorem, semialgebraic choice and the Hölder
estimate, all proved in `Oka/Geometry/RealAlgebraic/Semialgebraic/`. Nothing here is in Mathlib.
-/

open Set Filter Topology

namespace MvPolynomial

namespace Lojasiewicz

variable {n : ℕ}

/-- `∑ᵢ (Xᵢ - pᵢ)²`, the squared Euclidean distance to `p`. -/
noncomputable def ballPoly (p : Fin n → ℝ) : MvPolynomial (Fin n) ℝ := ∑ i, (X i - C (p i)) ^ 2

/-- `∑ᵢ (∂ᵢ f)²`, the squared Euclidean norm of the gradient of `f`. -/
noncomputable def gradSq (f : MvPolynomial (Fin n) ℝ) : MvPolynomial (Fin n) ℝ :=
  ∑ i, pderiv i f ^ 2

/-- Evaluation of `ballPoly`. -/
lemma eval_ballPoly (p y : Fin n → ℝ) : eval y (ballPoly p) = ∑ i, (y i - p i) ^ 2 := by
  simp [ballPoly]

/-- Evaluation of `gradSq`. -/
lemma eval_gradSq (f : MvPolynomial (Fin n) ℝ) (y : Fin n → ℝ) :
    eval y (gradSq f) = ∑ i, eval y (pderiv i f) ^ 2 := by
  simp [gradSq]

/-- `gradSq` is invariant under `f ↦ -f`. -/
lemma gradSq_neg (f : MvPolynomial (Fin n) ℝ) : gradSq (-f) = gradSq f := by
  simp [gradSq]

/-- Points of the unit ball are within distance `1` of `p` in each coordinate. -/
lemma abs_sub_le_one {p y : Fin n → ℝ} (hy : eval y (ballPoly p) ≤ 1) (i : Fin n) :
    |y i - p i| ≤ 1 := by
  rw [eval_ballPoly] at hy
  have : (y i - p i) ^ 2 ≤ 1 := (Finset.single_le_sum (f := fun j => (y j - p j) ^ 2)
    (fun j _ => sq_nonneg _) (Finset.mem_univ i)).trans hy
  exact (sq_le_one_iff_abs_le_one _).1 this

/-- The fibres of `f` in the closed unit ball around `p` are compact. -/
lemma isCompact_fiber (f : MvPolynomial (Fin n) ℝ) (p : Fin n → ℝ) (u : ℝ) :
    IsCompact {y | eval y (ballPoly p) ≤ 1 ∧ eval y f = u} := by
  refine Metric.isCompact_of_isClosed_isBounded ((isClosed_le (continuous_eval _)
    continuous_const).inter (isClosed_eq (continuous_eval _) continuous_const))
    (Metric.isBounded_closedBall (x := p) (r := 1) |>.subset fun y hy => ?_)
  rw [Metric.mem_closedBall, dist_eq_norm, pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  rw [Pi.sub_apply, Real.norm_eq_abs]
  exact abs_sub_le_one hy.1 i

/-- **The inequality on `{f > 0}`**, with the Euclidean norm squared `G` of the gradient:
`f ^ (2N - 1) ≤ G ^ N` on the unit ball around `p` where `0 < f < η`. -/
theorem exists_pos_side (f : MvPolynomial (Fin n) ℝ) (p : Fin n → ℝ) :
    ∃ N : ℕ, 0 < N ∧ ∃ η > 0, ∀ y, eval y (ballPoly p) ≤ 1 → 0 < eval y f → eval y f < η →
      eval y f ^ (2 * N - 1) ≤ eval y (gradSq f) ^ N := by
  classical
  set B := ballPoly p
  set G := gradSq f
  -- Step 1: the fibres over small positive values are nonempty, or there is nothing to prove
  have hL : IsSemialgebraic₁ {u | ∃ y, eval y B ≤ 1 ∧ eval y f = u} := by
    have : IsSemialgebraic {x : Unit → ℝ | ∃ y : Fin n → ℝ, eval y B ≤ 1 ∧ eval y f = x ()} := by
      semialg
    exact this
  rcases hL.eventually_nhdsGT 0 with hLin | hLout
  swap
  · obtain ⟨η, hη, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hLout
    exact ⟨1, one_pos, η, hη, fun y hy hpos hlt => absurd ⟨y, hy, rfl⟩ (hsub ⟨hpos, hlt⟩)⟩
  obtain ⟨η₀, hη₀, hL0⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hLin
  -- Step 2: the curve of lexicographically smallest minimisers of `G` on the fibres
  set M : ℝ → Set (Fin n → ℝ) := fun u => {y | eval y B ≤ 1 ∧ eval y f = u ∧
    ∀ z : Fin n → ℝ, eval z B ≤ 1 → eval z f = u → eval y G ≤ eval z G}
  have hMc : ∀ u ∈ Ioo 0 η₀, IsCompact (M u) ∧ (M u).Nonempty := by
    intro u hu
    obtain ⟨y₀, hy₀⟩ := hL0 hu
    have hF := isCompact_fiber f p u
    obtain ⟨y, hy, hymin⟩ := hF.exists_isMinOn ⟨y₀, hy₀⟩ (continuous_eval G).continuousOn
    refine ⟨?_, y, hy.1, hy.2, fun z hz1 hz2 => hymin ⟨hz1, hz2⟩⟩
    have hMeq : M u = {y | eval y B ≤ 1 ∧ eval y f = u} ∩
        ⋂ z ∈ {y | eval y B ≤ 1 ∧ eval y f = u}, {y | eval y G ≤ eval z G} := by
      ext y
      simp only [M, mem_setOf_eq, mem_inter_iff, mem_iInter, and_imp, and_assoc]
    rw [hMeq]
    exact hF.inter_right (isClosed_biInter fun z _ => isClosed_le (continuous_eval G)
      continuous_const)
  have hD : IsSemialgebraic₁ (Ioo 0 η₀) := by
    have : IsSemialgebraic {x : Unit → ℝ | 0 < x () ∧ x () < η₀} := by semialg
    exact this
  have hMs : IsSemialgebraic {w : Option (Fin n) → ℝ | (fun j => w (some j)) ∈ M (w none)} := by
    simp only [M, mem_setOf_eq]
    semialg
  set x := IsSemialgebraicFun.lexMin (Ioo 0 η₀) M
  have hxs : ∀ i, IsSemialgebraicFun (fun u => x u i) :=
    IsSemialgebraicFun.lexMin_coord hD hMs hMc
  have hxM : ∀ u ∈ Ioo 0 η₀, x u ∈ M u := fun u hu =>
    (IsSemialgebraicFun.lexMin_spec hu (hMc u hu).1 (hMc u hu).2).1
  -- Step 3: the curve is continuous with monotone coordinates near `0⁺`
  have hev : ∀ i, ∀ᶠ b in 𝓝[>] (0 : ℝ), ContinuousOn (fun u => x u i) (Ioo 0 b) ∧
      (MonotoneOn (fun u => x u i) (Ioo 0 b) ∨ AntitoneOn (fun u => x u i) (Ioo 0 b)) := by
    intro i
    obtain ⟨b, hb, hc, hm⟩ := (hxs i).exists_continuousOn_monotoneOn 0
    filter_upwards [Ioo_mem_nhdsGT hb] with b' hb'
    have hsub : Ioo 0 b' ⊆ Ioo 0 b := Ioo_subset_Ioo_right hb'.2.le
    exact ⟨hc.mono hsub, hm.imp (fun h => h.mono hsub) (fun h => h.mono hsub)⟩
  obtain ⟨b₁, hcm, hb₁⟩ :=
    ((Filter.eventually_all.2 hev).and (Ioo_mem_nhdsGT hη₀)).exists
  -- Step 4: limits of the coordinates and the Hölder estimate
  have hbdd : ∀ u ∈ Ioo 0 b₁, ∀ i, |x u i - p i| ≤ 1 := fun u hu i =>
    abs_sub_le_one (hxM u ⟨hu.1, hu.2.trans hb₁.2⟩).1 i
  have hlim : ∀ i, ∃ q, Tendsto (fun u => x u i) (𝓝[>] 0) (𝓝 q) := by
    intro i
    have hne : (Ioo 0 b₁).Nonempty := ⟨b₁ / 2, by linarith [hb₁.1], by linarith [hb₁.1]⟩
    rcases (hcm i).2 with hm | hm
    · refine ⟨_, hm.tendsto_nhdsWithin_Ioo_right hne ⟨p i - 1, ?_⟩⟩
      rintro _ ⟨u, hu, rfl⟩
      linarith [(abs_le.1 (hbdd u hu i)).1]
    · refine ⟨_, hm.tendsto_nhdsWithin_Ioo_right hne ⟨p i + 1, ?_⟩⟩
      rintro _ ⟨u, hu, rfl⟩
      linarith [(abs_le.1 (hbdd u hu i)).2]
  choose q hq using hlim
  have hhol : ∀ i, ∃ N : ℕ, 0 < N ∧ ∀ᶠ t in 𝓝[>] 0, |x t i - q i| ^ N ≤ t := by
    intro i
    have hs : IsSemialgebraicFun (fun t => x t i - q i) := by
      have : IsSemialgebraic {w : Fin 2 → ℝ | ∃ v, x (w 0) i = v ∧ v - q i = w 1} := by
        semialg using (hxs i).setOf_graph
      exact this.congr (by ext w; simp)
    exact hs.exists_pow_le (by simpa using (hq i).sub_const (q i))
  choose Ns hNs hNsev using hhol
  set N := ∑ i, Ns i + 1 with hNdef
  have hNpos : 0 < N := Nat.succ_pos _
  have hNge : ∀ i, Ns i ≤ N := fun i =>
    (Finset.single_le_sum (fun j _ => Nat.zero_le (Ns j)) (Finset.mem_univ i)).trans
      (Nat.le_succ _)
  have hhold : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i, |x t i - q i| ^ N ≤ t := by
    refine Filter.eventually_all.2 fun i => ?_
    have h1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), |x t i - q i| ≤ 1 := by
      have := ((hq i).sub_const (q i)).abs
      rw [sub_self, abs_zero] at this
      exact (this.eventually (gt_mem_nhds one_pos)).mono fun t ht => ht.le
    filter_upwards [hNsev i, h1] with t ht ht1
    exact (pow_le_pow_of_le_one (abs_nonneg _) ht1 (hNge i)).trans ht
  -- Step 5: the dichotomy for the exceptional set `E`
  have hE : IsSemialgebraic₁
      {u | ∃ y, eval y B ≤ 1 ∧ eval y f = u ∧ eval y G ^ N < u ^ (2 * N - 1)} := by
    have : IsSemialgebraic {x : Unit → ℝ | ∃ y : Fin n → ℝ, eval y B ≤ 1 ∧ eval y f = x () ∧
        eval y G ^ N < x () ^ (2 * N - 1)} := by
      semialg
    exact this
  rcases hE.eventually_nhdsGT 0 with hEin | hEout
  swap
  · obtain ⟨η, hη, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hEout
    refine ⟨N, hNpos, η, hη, fun y hy hpos hlt => ?_⟩
    by_contra hcon
    exact hsub ⟨hpos, hlt⟩ ⟨y, hy, rfl, not_le.1 hcon⟩
  exfalso
  obtain ⟨η₃, hη₃, hE3⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hEin
  set b := min η₃ b₁
  have hb : 0 < b := lt_min hη₃ hb₁.1
  have hsub₁ : Ioo 0 b ⊆ Ioo 0 b₁ := Ioo_subset_Ioo_right (min_le_right _ _)
  -- the gradient is small along the curve
  have hgrad : ∀ u ∈ Ioo 0 b, ∀ i,
      |eval (x u) (pderiv i f)| ^ (2 * N) < u ^ (2 * N - 1) := by
    intro u hu i
    have hu0 : u ∈ Ioo 0 η₀ := ⟨hu.1, (hsub₁ hu).2.trans hb₁.2⟩
    obtain ⟨-, -, hxmin⟩ := hxM u hu0
    obtain ⟨y, hyB, hyf, hyG⟩ := hE3 ⟨hu.1, hu.2.trans_le (min_le_left _ _)⟩
    have h1 : eval (x u) G ≤ eval y G := hxmin y hyB hyf
    have hG0 : 0 ≤ eval (x u) G := by
      rw [eval_gradSq]
      positivity
    have h2 : eval (x u) (pderiv i f) ^ 2 ≤ eval (x u) G := by
      rw [eval_gradSq]
      exact Finset.single_le_sum (f := fun j => eval (x u) (pderiv j f) ^ 2)
        (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    calc |eval (x u) (pderiv i f)| ^ (2 * N) = (eval (x u) (pderiv i f) ^ 2) ^ N := by
          rw [pow_mul, sq_abs]
      _ ≤ eval (x u) G ^ N := pow_le_pow_left₀ (sq_nonneg _) h2 N
      _ ≤ eval y G ^ N := pow_le_pow_left₀ hG0 h1 N
      _ < u ^ (2 * N - 1) := hyG
  -- choose `t = τ ^ (2N)` small
  have hhalf : Tendsto (fun t : ℝ => t / 2) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have := ((continuous_id.div_const (2 : ℝ)).tendsto 0)
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
      exact half_pos ht
  have hpow : Tendsto (fun τ : ℝ => τ ^ (2 * N)) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have := ((continuous_pow (2 * N)).tendsto (0 : ℝ))
      rw [zero_pow (by omega)] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with τ (hτ : 0 < τ)
      exact pow_pos hτ _
  have hQ : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < b ∧ (∀ i, |x t i - q i| ^ N ≤ t) ∧
      ∀ i, |x (t / 2) i - q i| ^ N ≤ t / 2 :=
    Filter.Eventually.and (Filter.mem_of_superset (Ioo_mem_nhdsGT hb) (fun t ht => ht.2) :
      ∀ᶠ t in 𝓝[>] (0 : ℝ), t < b) (hhold.and (hhalf.eventually hhold))
  have hsmall : (0 : ℝ) < 1 / (4 * n + 1) := by positivity
  obtain ⟨τ, ⟨htb, ht1, ht2⟩, hτ0, hτs⟩ := ((hpow.eventually hQ).and
    ((eventually_mem_nhdsWithin : ∀ᶠ τ in 𝓝[>] (0 : ℝ), τ ∈ Ioi 0).and
      (Filter.mem_of_superset (Ioo_mem_nhdsGT hsmall) (fun t ht => ht.2) :
        ∀ᶠ τ : ℝ in 𝓝[>] (0 : ℝ), τ < 1 / (4 * (n : ℝ) + 1)))).exists
  rw [mem_Ioi] at hτ0
  set t := τ ^ (2 * N) with htdef
  have ht0 : 0 < t := pow_pos hτ0 _
  have hsub : Icc (t / 2) t ⊆ Ioo 0 b := fun u hu => ⟨by linarith [hu.1], hu.2.trans_lt htb⟩
  -- the gradient bound `τ ^ (2N - 1) = t ^ θ` on `[t / 2, t]`
  have hK : ∀ u ∈ Icc (t / 2) t, ∀ i, |eval (x u) (pderiv i f)| ≤ τ ^ (2 * N - 1) := by
    intro u hu i
    have h1 := hgrad u (hsub hu) i
    have h2 : u ^ (2 * N - 1) ≤ t ^ (2 * N - 1) := pow_le_pow_left₀ (by linarith [hu.1]) hu.2 _
    have h3 : t ^ (2 * N - 1) = (τ ^ (2 * N - 1)) ^ (2 * N) := by
      rw [htdef, ← pow_mul, ← pow_mul, mul_comm]
    rw [h3] at h2
    exact (pow_le_pow_iff_left₀ (abs_nonneg _) (pow_nonneg hτ0.le _) (by omega)).1
      (h1.le.trans h2)
  have hpath := abs_eval_sub_le_of_path f (x := x) (s := t / 2) (t := t) (by linarith)
    (continuousOn_pi.2 fun i => (hcm i).1.mono (hsub.trans hsub₁))
    (fun i => (hcm i).2.imp (fun h => h.mono (hsub.trans hsub₁))
      (fun h => h.mono (hsub.trans hsub₁))) hK
  have hft : eval (x t) f = t :=
    (hxM t ⟨ht0, (hsub₁ (hsub ⟨by linarith, le_rfl⟩)).2.trans hb₁.2⟩).2.1
  have hft2 : eval (x (t / 2)) f = t / 2 :=
    (hxM (t / 2) ⟨by linarith, (hsub₁ (hsub ⟨le_rfl, by linarith⟩)).2.trans hb₁.2⟩).2.1
  -- the displacement of the curve between `t / 2` and `t`
  have hcoord : ∀ i, |x t i - x (t / 2) i| ≤ 2 * τ ^ 2 := by
    intro i
    have e1 : |x t i - q i| ≤ τ ^ 2 :=
      (pow_le_pow_iff_left₀ (abs_nonneg _) (sq_nonneg τ) (by omega : N ≠ 0)).1
        (by rw [← pow_mul]; exact ht1 i)
    have e2 : |x (t / 2) i - q i| ≤ τ ^ 2 :=
      (pow_le_pow_iff_left₀ (abs_nonneg _) (sq_nonneg τ) (by omega : N ≠ 0)).1
        (by rw [← pow_mul]; exact (ht2 i).trans (by linarith))
    calc |x t i - x (t / 2) i| = |(x t i - q i) - (x (t / 2) i - q i)| := by ring_nf
      _ ≤ |x t i - q i| + |x (t / 2) i - q i| := abs_sub _ _
      _ ≤ 2 * τ ^ 2 := by linarith
  have hsum : ∑ i, |x t i - x (t / 2) i| ≤ n * (2 * τ ^ 2) := by
    calc ∑ i, |x t i - x (t / 2) i| ≤ ∑ _i : Fin n, 2 * τ ^ 2 :=
          Finset.sum_le_sum fun i _ => hcoord i
      _ = n * (2 * τ ^ 2) := by simp
  rw [hft, hft2, show t - t / 2 = t / 2 by ring, abs_of_pos (by linarith)] at hpath
  have hpow_eq : τ ^ (2 * N - 1) * τ ^ 2 = t * τ := by
    rw [htdef, ← pow_add, ← pow_succ, show 2 * N - 1 + 2 = 2 * N + 1 by omega]
  have h4 : t / 2 ≤ 2 * n * (t * τ) := by
    calc t / 2 ≤ τ ^ (2 * N - 1) * ∑ i, |x t i - x (t / 2) i| := hpath
      _ ≤ τ ^ (2 * N - 1) * (n * (2 * τ ^ 2)) :=
          mul_le_mul_of_nonneg_left hsum (pow_nonneg hτ0.le _)
      _ = 2 * n * (τ ^ (2 * N - 1) * τ ^ 2) := by ring
      _ = 2 * n * (t * τ) := by rw [hpow_eq]
  have h5 : 1 ≤ 4 * n * τ := by
    by_contra hcon
    push Not at hcon
    nlinarith
  rw [lt_div_iff₀ (by positivity)] at hτs
  nlinarith

/-- From `a ^ (2N - 1) ≤ (∑ gᵢ²) ^ N` to `a ^ θ / (n + 1) ≤ ‖g‖` (sup norm), for
`θ ≥ 1 - 1 / (2N)` and `0 < a < 1`. -/
lemma le_norm_of_pow_le {N : ℕ} (hN : 0 < N) (g : Fin n → ℝ) {a θ : ℝ} (ha : 0 < a)
    (ha1 : a ≤ 1) (hθ : 1 - 1 / (2 * N) ≤ θ)
    (h : a ^ (2 * N - 1) ≤ (∑ i, g i ^ 2) ^ N) : 1 / (n + 1) * a ^ θ ≤ ‖g‖ := by
  set θ₀ : ℝ := 1 - 1 / (2 * N)
  have hθa : a ^ θ ≤ a ^ θ₀ := Real.rpow_le_rpow_of_exponent_ge ha ha1 hθ
  have hc : (0 : ℝ) < 1 / (n + 1) := by positivity
  refine (mul_le_mul_of_nonneg_left hθa hc.le).trans ?_
  have hg : 0 ≤ ‖g‖ := norm_nonneg g
  have hsum : ∑ i, g i ^ 2 ≤ n * ‖g‖ ^ 2 := by
    calc ∑ i, g i ^ 2 ≤ ∑ _i : Fin n, ‖g‖ ^ 2 := Finset.sum_le_sum fun i _ => by
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (by simpa using norm_le_pi_norm g i) 2
      _ = n * ‖g‖ ^ 2 := by simp
  have h2N : (2 * N : ℕ) ≠ 0 := by omega
  rw [← pow_le_pow_iff_left₀ (by positivity) hg h2N]
  have hθ₀ : θ₀ * ((2 * N : ℕ) : ℝ) = ((2 * N - 1 : ℕ) : ℝ) := by
    have h1 : (1 : ℕ) ≤ 2 * N := by omega
    simp only [θ₀]
    push_cast [h1]
    rw [sub_mul, one_mul, one_div, inv_mul_cancel₀ (by positivity)]
  have hpow : (a ^ θ₀) ^ (2 * N) = a ^ (2 * N - 1) := by
    rw [← Real.rpow_mul_natCast ha.le, hθ₀, Real.rpow_natCast]
  rw [mul_pow, hpow]
  have hn : (n : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith
  calc (1 / (n + 1 : ℝ)) ^ (2 * N) * a ^ (2 * N - 1)
      ≤ (1 / (n + 1 : ℝ)) ^ (2 * N) * (n * ‖g‖ ^ 2) ^ N :=
        mul_le_mul_of_nonneg_left (h.trans (pow_le_pow_left₀ (by positivity) hsum N))
          (by positivity)
    _ ≤ (1 / (n + 1 : ℝ)) ^ (2 * N) * (((n : ℝ) + 1) ^ 2 * ‖g‖ ^ 2) ^ N :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity)
          (mul_le_mul_of_nonneg_right hn (by positivity)) N) (by positivity)
    _ = ‖g‖ ^ (2 * N) := by
        rw [mul_pow, ← pow_mul, ← pow_mul, ← mul_assoc, ← mul_pow, one_div,
          inv_mul_cancel₀ (by positivity), one_pow, one_mul]

end Lojasiewicz

open Lojasiewicz in
/-- **The Łojasiewicz gradient inequality** for real polynomials: near a zero `p` of a real
polynomial `f`, `c * |f x| ^ θ ≤ ‖∇f x‖` for some `θ ∈ [0, 1)` and `c > 0` (sup norm). -/
theorem exists_lojasiewicz_gradient {n : ℕ} (f : MvPolynomial (Fin n) ℝ)
    (p : Fin n → ℝ) (hp : MvPolynomial.eval p f = 0) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ < 1 ∧ ∃ c : ℝ, 0 < c ∧ ∀ᶠ x in nhds p,
      c * |MvPolynomial.eval x f| ^ θ ≤
        ‖fun i => MvPolynomial.eval x (MvPolynomial.pderiv i f)‖ := by
  obtain ⟨N₁, hN₁, η₁, hη₁, h₁⟩ := exists_pos_side f p
  obtain ⟨N₂, hN₂, η₂, hη₂, h₂⟩ := exists_pos_side (-f) p
  set θ := max (1 - 1 / (2 * (N₁ : ℝ))) (1 - 1 / (2 * (N₂ : ℝ)))
  have hlt : ∀ N : ℕ, 0 < N → 1 - 1 / (2 * (N : ℝ)) < 1 := fun N hN => by
    have : (0 : ℝ) < N := by exact_mod_cast hN
    have : (0 : ℝ) < 1 / (2 * N) := by positivity
    linarith
  have hθ1 : θ < 1 := max_lt (hlt N₁ hN₁) (hlt N₂ hN₂)
  have hθ0 : 0 < θ := by
    have : (1 : ℝ) ≤ N₁ := by exact_mod_cast hN₁
    have : 1 / (2 * (N₁ : ℝ)) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    exact lt_max_of_lt_left (by linarith)
  refine ⟨θ, hθ0.le, hθ1, 1 / (n + 1), by positivity, ?_⟩
  have hB : ∀ᶠ y in 𝓝 p, eval y (ballPoly p) < 1 :=
    (continuous_eval _).continuousAt.eventually_lt continuousAt_const (by simp [eval_ballPoly])
  have hf : ∀ᶠ y in 𝓝 p, |eval y f| < min (min η₁ η₂) 1 :=
    ((continuous_eval f).abs).continuousAt.eventually_lt continuousAt_const
      (by simp [hp, hη₁, hη₂])
  filter_upwards [hB, hf] with y hyB hyf
  have hyf1 := hyf.trans_le (min_le_left _ _)
  have hya : |eval y f| ≤ 1 := (hyf.trans_le (min_le_right _ _)).le
  rcases lt_trichotomy (eval y f) 0 with hneg | hzero | hpos
  · have h := h₂ y hyB.le (by simpa using hneg)
      (by have := hyf1.trans_le (min_le_right _ _); rw [abs_of_neg hneg] at this; simpa using this)
    rw [gradSq_neg, eval_gradSq] at h
    rw [show eval y (-f) = |eval y f| by simp [abs_of_neg hneg]] at h
    exact le_norm_of_pow_le hN₂ _ (abs_pos.2 hneg.ne) hya (le_max_right _ _) h
  · rw [hzero, abs_zero, Real.zero_rpow hθ0.ne', mul_zero]
    exact norm_nonneg _
  · have h := h₁ y hyB.le hpos
      (by have := hyf1.trans_le (min_le_left _ _); rwa [abs_of_pos hpos] at this)
    rw [eval_gradSq, ← abs_of_pos hpos] at h
    exact le_norm_of_pow_le hN₁ _ (abs_pos.2 hpos.ne') hya (le_max_left _ _) h

end MvPolynomial
