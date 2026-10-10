/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Uniformization.PmDeck

/-!
# Even elliptic functions with a pole of bounded order are polynomials in `℘`

For the lattice `Λ = ℤ t + ℤ`: an even, `Λ`-periodic function `H`, holomorphic on `ℂ ∖ Λ`, with
`|w|^{2N} |H w|` bounded near `0`, is a polynomial of degree at most `N` in `℘`
(`Peripheral.exists_poly_weierstrassP`).

Induction on `N`. For `N = 0`, `H` extends to a bounded entire function (removable singularities at
the lattice points, periodicity and compactness of the fundamental parallelogram), hence is
constant (Liouville). For `N + 1`, subtract `a ℘^{N+1}` with `a = lim w^{2N+2} H(w)`: the
difference `H₁` has `w^{2N+2} H₁(w) → 0`, and this function is even, so it vanishes to order `2`
at `0`, i.e. `|w|^{2N} |H₁ w|` is bounded.
-/

open Complex Metric Set Filter Topology Polynomial
open UpperHalfPlane hiding I I_re I_im

namespace Uniformization

namespace Peripheral

open Generators

variable {t : ℍ}

theorem notMem_lattice_of_small {w : ℂ} (hw0 : w ≠ 0) (hw : ‖w‖ < r₀ t) :
    w ∉ (Lt t).lattice :=
  Dst_notMem ⟨mem_ball_zero_iff.mpr hw, hw0⟩

variable (t) in
/-- The closed fundamental parallelogram. -/
def Pbar : Set ℂ := {k | 0 ≤ cx t k ∧ cx t k ≤ 1 ∧ 0 ≤ cy t k ∧ cy t k ≤ 1}

theorem isCompact_Pbar : IsCompact (Pbar t) := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · simp only [Pbar, setOf_and]
    exact (isClosed_le continuous_const (continuous_cx t)).inter
      ((isClosed_le (continuous_cx t) continuous_const).inter
      ((isClosed_le continuous_const (continuous_cy t)).inter
      (isClosed_le (continuous_cy t) continuous_const)))
  · refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 1 + ‖(t : ℂ)‖)).subset ?_
    rintro k ⟨h1, h2, h3, h4⟩
    rw [mem_closedBall_zero_iff, eq_cx_cy t k]
    calc ‖(cx t k : ℂ) + cy t k * t‖ ≤ ‖(cx t k : ℂ)‖ + ‖(cy t k : ℂ) * t‖ := norm_add_le _ _
      _ ≤ 1 + ‖(t : ℂ)‖ := by
        rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg h1,
          Real.norm_of_nonneg h3]
        gcongr
        nlinarith [norm_nonneg (t : ℂ)]

theorem exists_sub_mem_Pbar (z : ℂ) : ∃ l ∈ (Lt t).lattice, z - l ∈ Pbar t := by
  set l : ℂ := (⌊cx t z⌋ : ℝ) • (1 : ℂ) + (⌊cy t z⌋ : ℝ) • (t : ℂ)
  have hl : l ∈ (Lt t).lattice := by
    rw [mem_lattice_iff]
    refine ⟨⌊cy t z⌋, ⌊cx t z⌋, ?_, ?_⟩
    · simp only [l, cy_add, cy_smul, cy_one, cy_t]; ring
    · simp only [l, cx_add, cx_smul, cx_one, cx_t]; ring
  refine ⟨l, hl, ?_⟩
  have hx : cx t (z - l) = Int.fract (cx t z) := by
    simp only [l, cx_sub, cx_add, cx_smul, cx_one, cx_t, Int.fract]; ring
  have hy : cy t (z - l) = Int.fract (cy t z) := by
    simp only [l, cy_sub, cy_add, cy_smul, cy_one, cy_t, Int.fract]; ring
  exact ⟨hx ▸ Int.fract_nonneg _, hx ▸ (Int.fract_lt_one _).le, hy ▸ Int.fract_nonneg _,
    hy ▸ (Int.fract_lt_one _).le⟩

/-- **Base case**: a periodic function holomorphic off `Λ` and bounded near `0` is constant. -/
theorem const_of_bounded {H : ℂ → ℂ} (hd : DifferentiableOn ℂ H ((Lt t).lattice : Set ℂ)ᶜ)
    (hper : ∀ w, ∀ l ∈ (Lt t).lattice, H (w + l) = H w) {ρ C : ℝ} (hρ : 0 < ρ)
    (hb : ∀ w, w ≠ 0 → ‖w‖ < ρ → ‖H w‖ ≤ C) :
    ∃ c : ℂ, ∀ w ∉ (Lt t).lattice, H w = c := by
  set ρ' := min ρ (r₀ t)
  have hρ' : 0 < ρ' := lt_min hρ r₀_pos
  have hball : ball (0 : ℂ) ρ' ∈ 𝓝 (0 : ℂ) := ball_mem_nhds 0 hρ'
  have hdball : DifferentiableOn ℂ H (ball 0 ρ' \ {0}) := hd.mono fun w hw ↦
    notMem_lattice_of_small hw.2 ((mem_ball_zero_iff.mp hw.1).trans_le (min_le_right _ _))
  set H₀ := Function.update H 0 (limUnder (𝓝[≠] (0 : ℂ)) H)
  have hH₀ : DifferentiableOn ℂ H₀ (ball 0 ρ') :=
    Complex.differentiableOn_update_limUnder_of_bddAbove hball hdball
      ⟨C, by
        rintro _ ⟨w, hw, rfl⟩
        exact hb w hw.2 ((mem_ball_zero_iff.mp hw.1).trans_le (min_le_left _ _))⟩
  classical
  set Ĥ : ℂ → ℂ := fun z ↦ if z ∈ (Lt t).lattice then H₀ 0 else H z
  have hĤper : ∀ z, ∀ l ∈ (Lt t).lattice, Ĥ (z + l) = Ĥ z := by
    intro z l hl
    by_cases hz : z ∈ (Lt t).lattice
    · simp [Ĥ, hz, add_mem hz hl]
    · have : z + l ∉ (Lt t).lattice := fun h ↦ hz (by simpa using sub_mem h hl)
      simp only [Ĥ, hz, this, if_false]
      exact hper z l hl
  have hĤd : Differentiable ℂ Ĥ := by
    intro z
    by_cases hz : z ∈ (Lt t).lattice
    · have hev : Ĥ =ᶠ[𝓝 z] fun v ↦ H₀ (v - z) := by
        filter_upwards [ball_mem_nhds z hρ'] with v hv
        by_cases hvz : v = z
        · subst hvz; simp [Ĥ, hz]
        · have h1 : v - z ≠ 0 := sub_ne_zero.mpr hvz
          have h2 : ‖v - z‖ < r₀ t := by
            rw [← dist_eq_norm]; exact hv.trans_le (min_le_right _ _)
          have h3 : v ∉ (Lt t).lattice := fun h ↦
            notMem_lattice_of_small h1 h2 (sub_mem h hz)
          simp only [Ĥ, h3, if_false, H₀, Function.update_of_ne h1]
          have := hper (v - z) z hz
          rw [sub_add_cancel] at this
          exact this
      refine DifferentiableAt.congr_of_eventuallyEq ?_ hev
      have : DifferentiableAt ℂ H₀ (z - z) := by
        rw [sub_self]; exact hH₀.differentiableAt hball
      exact DifferentiableAt.comp (g := H₀) (f := fun v ↦ v - z) z this
        (differentiableAt_id.sub_const z)
    · have hopen : IsOpen ((Lt t).lattice : Set ℂ)ᶜ := (Lt t).isClosed_lattice.isOpen_compl
      have hev : Ĥ =ᶠ[𝓝 z] H := by
        filter_upwards [hopen.mem_nhds hz] with v hv
        simp [Ĥ, show v ∉ (Lt t).lattice from hv]
      exact ((hd.differentiableAt (hopen.mem_nhds hz)).congr_of_eventuallyEq hev)
  have hbdd : Bornology.IsBounded (range Ĥ) := by
    refine ((isCompact_Pbar (t := t)).image hĤd.continuous).isBounded.subset ?_
    rintro _ ⟨z, rfl⟩
    obtain ⟨l, hl, hzl⟩ := exists_sub_mem_Pbar (t := t) z
    refine ⟨z - l, hzl, ?_⟩
    have := hĤper (z - l) l hl
    rw [sub_add_cancel] at this
    exact this.symm
  refine ⟨Ĥ 0, fun w hw ↦ ?_⟩
  have := hĤd.apply_eq_apply_of_bounded hbdd w 0
  simpa [Ĥ, hw] using this

/-- The derivative of an even function at `0` vanishes. -/
theorem deriv_zero_of_even {f : ℂ → ℂ} (hf : DifferentiableAt ℂ f 0)
    (heven : ∀ w, f (-w) = f w) : deriv f 0 = 0 := by
  have h1 := hf.hasDerivAt
  have h2 : HasDerivAt (fun w ↦ f (-w)) (-deriv f 0) 0 := by
    have h1' : HasDerivAt f (deriv f 0) (-0) := by simpa using h1
    have := h1'.comp (0 : ℂ) (hasDerivAt_neg (0 : ℂ))
    simpa [Function.comp_def] using this
  have h3 : HasDerivAt f (-deriv f 0) 0 := by
    have e : (fun w ↦ f (-w)) = f := funext heven
    rwa [e] at h2
  have := h1.unique h3
  linear_combination this / 2

/-- **Even elliptic functions with bounded pole order are polynomials in `℘`.** -/
theorem exists_poly_weierstrassP : ∀ (N : ℕ) (H : ℂ → ℂ),
    DifferentiableOn ℂ H ((Lt t).lattice : Set ℂ)ᶜ →
    (∀ w, ∀ l ∈ (Lt t).lattice, H (w + l) = H w) → (∀ w, H (-w) = H w) →
    (∃ ρ > 0, ∃ C : ℝ, ∀ w, w ≠ 0 → ‖w‖ < ρ → ‖w‖ ^ (2 * N) * ‖H w‖ ≤ C) →
    ∃ p : ℂ[X], ∀ w ∉ (Lt t).lattice, H w = p.eval ((Lt t).weierstrassP w)
  | 0 => by
    intro H hd hper _ ⟨ρ, hρ, C, hb⟩
    obtain ⟨c, hc⟩ := const_of_bounded hd hper hρ (C := C) fun w hw0 hw ↦ by
      simpa using hb w hw0 hw
    exact ⟨Polynomial.C c, fun w hw ↦ by simp [hc w hw]⟩
  | N + 1 => by
    intro H hd hper heven ⟨ρ, hρ, C, hb⟩
    set ρ' := min ρ (r₀ t)
    have hρ' : 0 < ρ' := lt_min hρ r₀_pos
    have hball : ball (0 : ℂ) ρ' ∈ 𝓝 (0 : ℂ) := ball_mem_nhds 0 hρ'
    have hnot : ∀ w ∈ ball (0 : ℂ) ρ' \ {0}, w ∉ (Lt t).lattice := fun w hw ↦
      notMem_lattice_of_small hw.2 ((mem_ball_zero_iff.mp hw.1).trans_le (min_le_right _ _))
    have hwp : DifferentiableOn ℂ (Lt t).weierstrassP ((Lt t).lattice : Set ℂ)ᶜ :=
      fun w hw ↦ ((Lt t).analyticOnNhd_weierstrassP w hw).differentiableAt.differentiableWithinAt
    -- the leading coefficient
    set F : ℂ → ℂ := fun w ↦ w ^ (2 * (N + 1)) * H w
    have hFd : DifferentiableOn ℂ F (ball 0 ρ' \ {0}) :=
      (differentiableOn_id.pow _).mul (hd.mono hnot)
    have hFb : BddAbove (norm ∘ F '' (ball 0 ρ' \ {0})) := ⟨C, by
      rintro _ ⟨w, hw, rfl⟩
      simp only [Function.comp_apply, F, norm_mul, norm_pow]
      exact hb w hw.2 ((mem_ball_zero_iff.mp hw.1).trans_le (min_le_left _ _))⟩
    set a := limUnder (𝓝[≠] (0 : ℂ)) F
    have hFlim : Tendsto F (𝓝[≠] 0) (𝓝 a) := by
      have hF₀ := Complex.differentiableOn_update_limUnder_of_bddAbove hball hFd hFb
      have hc := (hF₀.differentiableAt hball).continuousAt
      have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
      rw [Function.update_self] at this
      refine this.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with w hw
      exact Function.update_of_ne hw _ _
    -- subtract `a ℘^{N+1}`
    set H₁ : ℂ → ℂ := fun w ↦ H w - a * (Lt t).weierstrassP w ^ (N + 1)
    have hH₁d : DifferentiableOn ℂ H₁ ((Lt t).lattice : Set ℂ)ᶜ :=
      hd.sub ((hwp.pow _).const_mul a)
    have hH₁per : ∀ w, ∀ l ∈ (Lt t).lattice, H₁ (w + l) = H₁ w := fun w l hl ↦ by
      simp only [H₁, hper w l hl, (Lt t).weierstrassP_add_coe w ⟨l, hl⟩]
    have hH₁even : ∀ w, H₁ (-w) = H₁ w := fun w ↦ by
      simp only [H₁, heven w, (Lt t).weierstrassP_neg]
    -- `f = w^{2N+2} H₁` tends to `0`
    set f : ℂ → ℂ := fun w ↦ w ^ (2 * (N + 1)) * H₁ w
    have hflim : Tendsto f (𝓝[≠] 0) (𝓝 0) := by
      have h1 : Tendsto (fun w : ℂ ↦ (w ^ 2 * (Lt t).weierstrassP w) ^ (N + 1)) (𝓝[≠] 0)
          (𝓝 (1 ^ (N + 1))) := (Heights.tendsto_sq_mul_weierstrassP_zero (Lt t)).pow _
      have h2 := hFlim.sub (h1.const_mul a)
      rw [one_pow, mul_one, sub_self] at h2
      refine h2.congr' (Eventually.of_forall fun w ↦ ?_)
      simp only [f, F, H₁]
      ring
    have hfd : DifferentiableOn ℂ f (ball 0 ρ' \ {0}) :=
      (differentiableOn_id.pow _).mul (hH₁d.mono hnot)
    set f₀ := Function.update f 0 0
    have hf₀d : DifferentiableOn ℂ f₀ (ball 0 ρ') := by
      refine (Complex.differentiableOn_compl_singleton_and_continuousAt_iff hball).mp
        ⟨hfd.congr fun w hw ↦ Function.update_of_ne hw.2 _ _, ?_⟩
      rw [continuousAt_update_same]; exact hflim
    have hf₀even : ∀ w, f₀ (-w) = f₀ w := by
      intro w
      by_cases hw : w = 0
      · subst hw; simp
      · simp only [f₀, Function.update_of_ne (neg_ne_zero.mpr hw), Function.update_of_ne hw, f,
          hH₁even, (even_two_mul (N + 1)).neg_pow]
    have hf₀0 : f₀ 0 = 0 := Function.update_self _ _ _
    have hdf₀ : deriv f₀ 0 = 0 := deriv_zero_of_even (hf₀d.differentiableAt hball) hf₀even
    set g₁ := dslope f₀ 0
    set g₂ := dslope g₁ 0
    have hg₁d : DifferentiableOn ℂ g₁ (ball 0 ρ') := (differentiableOn_dslope hball).mpr hf₀d
    have hg₂d : DifferentiableOn ℂ g₂ (ball 0 ρ') := (differentiableOn_dslope hball).mpr hg₁d
    have hg₁0 : g₁ 0 = 0 := by simp only [g₁, dslope_same, hdf₀]
    have hfg : ∀ w, f₀ w = w ^ 2 * g₂ w := fun w ↦ by
      have h1 := sub_smul_dslope f₀ 0 w
      have h2 := sub_smul_dslope g₁ 0 w
      simp only [sub_zero, smul_eq_mul, hf₀0, hg₁0] at h1 h2
      linear_combination -h1 - w * h2
    obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℂ) (ρ' / 2)).exists_bound_of_continuousOn
      (hg₂d.continuousOn.mono (closedBall_subset_ball (by linarith)))
    obtain ⟨q, hq⟩ := exists_poly_weierstrassP N H₁ hH₁d hH₁per hH₁even
      ⟨ρ' / 2, by positivity, B, fun w hw0 hw ↦ by
        have hfw : f₀ w = w ^ (2 * (N + 1)) * H₁ w := Function.update_of_ne hw0 _ _
        have hw2 : w ^ (2 * (N + 1)) = w ^ 2 * w ^ (2 * N) := by ring
        rw [hfg, hw2, mul_assoc] at hfw
        have := mul_left_cancel₀ (pow_ne_zero 2 hw0) hfw
        rw [← norm_pow, ← norm_mul, ← this]
        exact hB w (mem_closedBall_zero_iff.mpr hw.le)⟩
    refine ⟨q + Polynomial.C a * Polynomial.X ^ (N + 1), fun w hw ↦ ?_⟩
    have := hq w hw
    simp only [H₁] at this
    rw [eval_add, eval_mul, eval_C, eval_pow, eval_X, ← this]
    ring

end Peripheral

end Uniformization
