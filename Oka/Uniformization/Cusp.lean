/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Uniformization.CommutatorTrace

/-!
# The cusp normal form

Let `Σ : {Re s < log r₀} → ℍ` be the lift of `exp` through `ψ : ℍ → ℂ ∖ Λ`
(`Oka/Uniformization/Peripheral.lean`), with `Σ (s + 2πi) = C • Σ s` for the parabolic
`C = A⁻¹B⁻¹AB` of trace `-2` (`Oka/Uniformization/CommutatorTrace.lean`).

**Theorem** (`Peripheral.exists_cusp_normalForm`). There are `M ∈ SL(2, ℝ)`, `κ > 0`, `r₁ > 0`
and a function `φ`, bounded on `ball 0 r₁`, such that `M⁻¹ C M` acts as `z ↦ z + κ` and, for
`Re s < log r₁`,

`M⁻¹ • Σ s = (κ / 2πi) (s + φ (exp s))`.

So near the lattice point the covering `ψ` is, in the coordinate `M⁻¹ τ`, a perturbation of
`τ ↦ exp (2πi τ / κ)`: the parabolic cusp of `Γ` is a genuine cusp.

Proof. `E s = exp (2πi M⁻¹ Σ(s) / |κ|)` is `2πi`-periodic, so `G w = E (log w)` is holomorphic
on the punctured disc, bounded by `1`, extends over `0`, and is injective (`ψ ∘ Σ = exp`). It
vanishes at `0`: otherwise `M⁻¹ Σ (log w)` would converge in `ℍ` modulo `κ` and `ψ` would take the
value `0 ∈ Λ`. Hence `G′(0) ≠ 0`, `G w = w F(w)` with `F(0) ≠ 0`, `F = exp φ₀` near `0`, and
`2πi M⁻¹Σ(s)/|κ| - s - φ₀(e^s) ∈ 2πiℤ` is constant. Comparing with `Σ(s + 2πi) = C Σ(s)` gives
`κ = |κ|`.
-/

open Complex Metric Set Filter Topology
open UpperHalfPlane hiding I I_re I_im
open scoped MatrixGroups Real

namespace Uniformization

namespace Peripheral

open Generators

variable {t : ℍ} (U : Unif (Lt t))

/-- **Descent along `exp`.** A `2πi`-periodic function holomorphic on the half-plane
`{Re s < log r₀}` defines a holomorphic function `w ↦ E (log w)` on the punctured disc, with
`E s = (E ∘ log) (exp s)`. -/
theorem differentiableOn_comp_log {E : ℂ → ℂ} (hE : DifferentiableOn ℂ E (Hr t))
    (hper : ∀ s ∈ Hr t, E (s + 2 * π * I) = E s) :
    DifferentiableOn ℂ (fun w ↦ E (Complex.log w)) (Dst t) ∧
      ∀ s ∈ Hr t, E (Complex.log (Complex.exp s)) = E s := by
  have hperZ : ∀ s ∈ Hr t, ∀ k : ℤ, E (s + k * (2 * π * I)) = E s := by
    intro s hs k
    induction k using Int.induction_on with
    | zero => simp
    | succ n ih =>
      have h1 := hper _ (add_int_mem_Hr hs n)
      rw [← ih, ← h1]; congr 1; push_cast; ring
    | pred n ih =>
      have h1 := hper _ (add_int_mem_Hr hs (-n - 1))
      rw [← ih, ← h1]; congr 1; push_cast; ring
  have hexp : ∀ s ∈ Hr t, E (Complex.log (Complex.exp s)) = E s := by
    intro s hs
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp
      (Complex.exp_log (Complex.exp_ne_zero s))
    rw [hn, hperZ s hs n]
  refine ⟨fun p hp ↦ ?_, hexp⟩
  set s₁ := Complex.log p
  have hs₁ := log_mem_Hr hp
  have hps : Complex.exp s₁ = p := Complex.exp_log hp.2
  have hexps : HasStrictDerivAt Complex.exp (Complex.exp s₁) s₁ :=
    Complex.hasStrictDerivAt_exp s₁
  have hne : Complex.exp s₁ ≠ 0 := Complex.exp_ne_zero s₁
  set L := hexps.localInverse Complex.exp (Complex.exp s₁) s₁ hne
  have hL : HasStrictDerivAt L (Complex.exp s₁)⁻¹ (Complex.exp s₁) :=
    hexps.to_localInverse hne
  have hLs : L (Complex.exp s₁) = s₁ := (hexps.eventually_left_inverse hne).self_of_nhds
  have hLc : ContinuousAt L (Complex.exp s₁) := hL.hasDerivAt.continuousAt
  have hev : ∀ᶠ q in 𝓝 (Complex.exp s₁), E (Complex.log q) = E (L q) := by
    filter_upwards [hexps.eventually_right_inverse hne,
      hLc.preimage_mem_nhds (by rw [hLs]; exact isOpen_Hr.mem_nhds hs₁)] with q hq1 hq2
    rw [← hexp _ hq2, hq1]
  rw [← hps]
  refine (DifferentiableAt.congr_of_eventuallyEq ?_ hev).differentiableWithinAt
  have h1 : DifferentiableAt ℂ E (L (Complex.exp s₁)) := by
    rw [hLs]; exact hE.differentiableAt (isOpen_Hr.mem_nhds hs₁)
  exact h1.comp (Complex.exp s₁) hL.hasDerivAt.differentiableAt

/-- The monodromy `C` is conjugate to a translation. -/
theorem exists_conj_translation :
    ∃ M : SL(2, ℝ), ∃ κ : ℝ, κ ≠ 0 ∧ ∀ z : ℍ,
      (((M⁻¹ * Cm U * M) • z : ℍ) : ℂ) = z + κ := by
  have htr := trace_Cm U
  -- a conjugate with vanishing lower-left entry
  obtain ⟨M, hM⟩ : ∃ M : SL(2, ℝ), (M⁻¹ * Cm U * M) 1 0 = 0 := by
    by_cases hc : Cm U 1 0 = 0
    · exact ⟨1, by simpa using hc⟩
    · obtain ⟨η, hη⟩ := exists_real_fix (Cm U) (by rw [htr]; norm_num) hc
      exact ⟨conjFix η, by rw [conjFix_lowerLeft]; exact hη⟩
  set N := M⁻¹ * Cm U * M
  have hNtr : N 0 0 + N 1 1 = -2 := by
    have := trSL_conj M (Cm U); rw [htr] at this; exact this
  have hNdet : N 0 0 * N 1 1 = 1 := by have := det_SL N; rw [hM] at this; linarith
  have ha : N 0 0 = -1 := by nlinarith [sq_nonneg (N 0 0 + 1)]
  have hd : N 1 1 = -1 := by linarith
  refine ⟨M, -N 0 1, ?_, fun z ↦ ?_⟩
  · intro h0
    have h0' : N 0 1 = 0 := by linarith
    apply Cm_smul_ne U (M • UpperHalfPlane.I)
    have hN : ∀ z : ℍ, N • z = z := fun z ↦ by
      apply UpperHalfPlane.ext
      rw [coe_SL2R_smul, hM, ha, hd, h0']
      push_cast
      simp
    have := hN UpperHalfPlane.I
    calc Cm U • M • UpperHalfPlane.I = M • (N • UpperHalfPlane.I) := by
          simp only [N, ← mul_smul]; congr 1; group
      _ = M • UpperHalfPlane.I := by rw [this]
  · rw [coe_SL2R_smul, hM, ha, hd]
    push_cast
    field_simp
    ring

theorem isDiscrete_exp_preimage_one : IsDiscrete (Complex.exp ⁻¹' {1}) := by
  rw [isDiscrete_iff_discreteTopology]
  exact (Complex.isCoveringMapOn_exp 1 (by simp)).discreteTopology_fiber

/-- A continuous function `k` on a preconnected set with `exp (k s) = 1` is constant. -/
theorem const_of_exp_eq_one {S : Set ℂ} (hS : IsPreconnected S) {k : ℂ → ℂ}
    (hk : ContinuousOn k S) (h1 : ∀ s ∈ S, Complex.exp (k s) = 1) {x y : ℂ} (hx : x ∈ S)
    (hy : y ∈ S) : k x = k y :=
  hS.constant_of_mapsTo isDiscrete_exp_preimage_one hk (fun s hs ↦ h1 s hs) hx hy

theorem translation_zpow {M : SL(2, ℝ)} {κ : ℝ}
    (hM : ∀ z : ℍ, (((M⁻¹ * Cm U * M) • z : ℍ) : ℂ) = z + κ) (m : ℤ) (z : ℍ) :
    (((M⁻¹ * Cm U * M) ^ m • z : ℍ) : ℂ) = z + m * κ := by
  induction m using Int.induction_on generalizing z with
  | zero => simp
  | succ n ih => rw [zpow_add_one, mul_smul, ih, hM]; push_cast; ring
  | pred n ih =>
    have h := hM ((M⁻¹ * Cm U * M) ^ (-(n : ℤ) - 1) • z)
    rw [← mul_smul, ← zpow_one_add, show (1 : ℤ) + (-n - 1) = -n by ring, ih] at h
    push_cast at h ⊢
    linear_combination -h

/-- The lift in the normalised coordinate `M⁻¹ τ`. -/
noncomputable def τ' (M : SL(2, ℝ)) (s : ℂ) : ℂ := ((M⁻¹ • Sig U s : ℍ) : ℂ)

theorem τ'_im_pos (M : SL(2, ℝ)) (s : ℂ) : 0 < (τ' U M s).im := (M⁻¹ • Sig U s).im_pos

theorem differentiableOn_τ' (M : SL(2, ℝ)) : DifferentiableOn ℂ (τ' U M) (Hr t) := by
  have hS := differentiableOn_Sig U
  have : DifferentiableOn ℂ (fun s ↦ ((M⁻¹ 0 0 : ℂ) * (Sig U s : ℂ) + M⁻¹ 0 1) /
      ((M⁻¹ 1 0 : ℂ) * (Sig U s : ℂ) + M⁻¹ 1 1)) (Hr t) :=
    (((differentiableOn_const _).mul hS).add_const _).div
      (((differentiableOn_const _).mul hS).add_const _)
      fun s _ ↦ denom_SL2R_ne_zero M⁻¹ (Sig U s).im_pos
  exact this.congr fun s _ ↦ coe_SL2R_smul M⁻¹ (Sig U s)

theorem τ'_add_two_pi {M : SL(2, ℝ)} {κ : ℝ}
    (hM : ∀ z : ℍ, (((M⁻¹ * Cm U * M) • z : ℍ) : ℂ) = z + κ) {s : ℂ} (hs : s ∈ Hr t) :
    τ' U M (s + 2 * π * I) = τ' U M s + κ := by
  rw [τ', Sig_add_two_pi U hs, τ', ← hM, ← mul_smul, ← mul_smul]
  congr 2; group

theorem ψ_Cm_zpow_smul (m : ℤ) (ν : ℍ) : U.ψ ((Cm U) ^ m • ν) = U.ψ ν := by
  induction m using Int.induction_on generalizing ν with
  | zero => simp
  | succ n ih => rw [zpow_add_one, mul_smul, ih, ψ_Cm_smul]
  | pred n ih =>
    rw [show (-(n : ℤ) - 1) = -(n : ℤ) + (-1) by ring, zpow_add, zpow_neg_one, mul_smul, ih]
    have := ψ_Cm_smul U ((Cm U)⁻¹ • ν)
    rw [smul_inv_smul] at this
    exact this.symm

theorem conj_zpow_smul (M : SL(2, ℝ)) (m : ℤ) (ν : ℍ) :
    M • ((M⁻¹ * Cm U * M) ^ m • (M⁻¹ • ν)) = (Cm U) ^ m • ν := by
  have := conj_zpow (i := m) (a := M⁻¹) (b := Cm U)
  rw [inv_inv] at this
  rw [this, ← mul_smul, ← mul_smul]
  congr 1; group

/-- **The cusp normal form.** -/
theorem exists_cusp_normalForm :
    ∃ M : SL(2, ℝ), ∃ κ : ℝ, 0 < κ ∧ (∀ z : ℍ, (((M⁻¹ * Cm U * M) • z : ℍ) : ℂ) = z + κ) ∧
      ∃ r₁ : ℝ, 0 < r₁ ∧ r₁ ≤ r₀ t ∧ ∃ φ : ℂ → ℂ, ∃ Φ : ℝ,
        (∀ w ∈ ball (0 : ℂ) r₁, ‖φ w‖ ≤ Φ) ∧
        (∀ s : ℂ, s.re < Real.log r₁ →
          τ' U M s = (κ / (2 * π * I)) * (s + φ (Complex.exp s))) ∧
        ∃ G : ℂ → ℂ, DifferentiableOn ℂ G (ball 0 r₁) ∧ G 0 = 0 ∧ deriv G 0 ≠ 0 ∧
          ∀ s : ℂ, s.re < Real.log r₁ →
            Complex.exp (2 * π * I * τ' U M s / κ) = G (Complex.exp s) := by
  obtain ⟨M, κ, hκ, hM⟩ := exists_conj_translation U
  set a : ℝ := |κ|
  have ha : 0 < a := abs_pos.mpr hκ
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have h2πI : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  set E : ℂ → ℂ := fun s ↦ Complex.exp (2 * π * I * τ' U M s / a)
  have hEd : DifferentiableOn ℂ E (Hr t) :=
    (((differentiableOn_const _).mul (differentiableOn_τ' U M)).div_const _).cexp
  have hκa : Complex.exp (2 * π * I * κ / a) = 1 := by
    rcases abs_choice κ with h | h
    · rw [show (a : ℂ) = κ by simp [a, h], mul_div_assoc, div_self (by exact_mod_cast hκ),
        mul_one, Complex.exp_two_pi_mul_I]
    · rw [show (a : ℂ) = -κ by simp [a, h], show (2 * π * I * κ / -κ : ℂ) = -(2 * π * I) by
        field_simp [show (κ : ℂ) ≠ 0 by exact_mod_cast hκ]]
      rw [Complex.exp_neg, Complex.exp_two_pi_mul_I, inv_one]
  have hEper : ∀ s ∈ Hr t, E (s + 2 * π * I) = E s := by
    intro s hs
    simp only [E]
    rw [τ'_add_two_pi U hM hs, show 2 * π * I * (τ' U M s + κ) / a =
      2 * π * I * τ' U M s / a + 2 * π * I * κ / a by ring, Complex.exp_add, hκa, mul_one]
  have hEnorm : ∀ s, ‖E s‖ < 1 := by
    intro s
    simp only [E, Complex.norm_exp]
    rw [Real.exp_lt_one_iff]
    have him := τ'_im_pos U M s
    have : (2 * π * I * τ' U M s / a).re = -(2 * π * (τ' U M s).im) / a := by
      simp [div_ofReal_re]
    rw [this]
    exact div_neg_of_neg_of_pos (by nlinarith [Real.pi_pos]) ha
  obtain ⟨hgd, hgexp⟩ := differentiableOn_comp_log hEd hEper
  set g : ℂ → ℂ := fun w ↦ E (Complex.log w)
  -- the removable singularity
  set G := Function.update g 0 (limUnder (𝓝[≠] (0 : ℂ)) g)
  have hball : ball (0 : ℂ) (r₀ t) ∈ 𝓝 (0 : ℂ) := ball_mem_nhds 0 r₀_pos
  have hGd : DifferentiableOn ℂ G (ball 0 (r₀ t)) :=
    Complex.differentiableOn_update_limUnder_of_bddAbove hball hgd
      ⟨1, by rintro _ ⟨p, -, rfl⟩; exact (hEnorm _).le⟩
  have hGg : ∀ p ∈ Dst t, G p = g p := fun p hp ↦ Function.update_of_ne hp.2 _ _
  have hGc : ContinuousAt G 0 := (hGd.differentiableAt hball).continuousAt
  -- values in the normalised coordinate
  have hτ'log : ∀ p ∈ Dst t, ∀ q ∈ Dst t, g p = g q →
      ∃ m : ℤ, τ' U M (Complex.log p) = τ' U M (Complex.log q) + m * κ := by
    intro p hp q hq hpq
    simp only [g, E] at hpq
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hpq
    have : τ' U M (Complex.log p) = τ' U M (Complex.log q) + n * a := by
      field_simp at hn; linear_combination hn
    rcases abs_choice κ with h | h
    · exact ⟨n, by rw [this]; simp [a, h]⟩
    · exact ⟨-n, by rw [this]; simp [a, h]⟩
  -- injectivity on the punctured disc
  have hinj : ∀ p ∈ Dst t, ∀ q ∈ Dst t, g p = g q → p = q := by
    intro p hp q hq hpq
    obtain ⟨m, hm⟩ := hτ'log p hp q hq hpq
    have h1 : M⁻¹ • Sig U (Complex.log p) = (M⁻¹ * Cm U * M) ^ m • (M⁻¹ • Sig U (Complex.log q)) :=
      UpperHalfPlane.ext (by rw [translation_zpow U hM]; exact hm)
    have h2 : Sig U (Complex.log p) = (Cm U) ^ m • Sig U (Complex.log q) := by
      have := congrArg (fun z ↦ M • z) h1
      simp only [smul_inv_smul] at this
      rw [this, ← mul_smul, ← mul_smul]
      congr 1
      have := conj_zpow (i := m) (a := M⁻¹) (b := Cm U)
      rw [inv_inv] at this
      rw [this]
      group
    have h3 := congrArg U.ψ h2
    rw [ψ_Cm_zpow_smul, ψ_Sig U (log_mem_Hr hp), ψ_Sig U (log_mem_Hr hq), Complex.exp_log hp.2,
      Complex.exp_log hq.2] at h3
    exact h3
  have hgne : ∀ p, g p ≠ 0 := fun p ↦ Complex.exp_ne_zero _
  have hGle : ∀ z ∈ ball (0 : ℂ) (r₀ t), ‖G z‖ ≤ 1 := by
    intro z hz
    by_cases hz0 : z = 0
    · subst hz0
      have hlim : Tendsto G (𝓝[≠] 0) (𝓝 (G 0)) := hGc.tendsto.mono_left nhdsWithin_le_nhds
      refine le_of_tendsto hlim.norm ?_
      filter_upwards [inter_mem_nhdsWithin _ hball] with p hp
      rw [hGg p ⟨hp.2, hp.1⟩]; exact (hEnorm _).le
    · rw [hGg z ⟨hz, hz0⟩]; exact (hEnorm _).le
  have hp₁ : ((r₀ t / 2 : ℝ) : ℂ) ∈ Dst t := ⟨by
    rw [mem_ball_zero_iff]; simp [abs_of_pos r₀_pos]; linarith [r₀_pos (t := t)],
    by simp [r₀_pos.ne']⟩
  have hp₂ : ((r₀ t / 3 : ℝ) : ℂ) ∈ Dst t := ⟨by
    rw [mem_ball_zero_iff]; simp [abs_of_pos r₀_pos]; linarith [r₀_pos (t := t)],
    by simp [r₀_pos.ne']⟩
  have hp₁₂ : ((r₀ t / 2 : ℝ) : ℂ) ≠ ((r₀ t / 3 : ℝ) : ℂ) := by
    intro h
    have := congrArg Complex.re h
    simp at this; linarith [r₀_pos (t := t)]
  -- `G 0 = 0`
  have hG0 : G 0 = 0 := by
    by_contra hL
    set L := G 0
    have hLlt : ‖L‖ < 1 := by
      refine lt_of_le_of_ne (hGle 0 (mem_ball_self r₀_pos)) fun h1 ↦ ?_
      have hmax : IsMaxOn (norm ∘ G) (ball 0 (r₀ t)) 0 := fun z hz ↦ by
        simp only [mem_setOf_eq, Function.comp_apply]; rw [h1]; exact hGle z hz
      have hc := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm
        (convex_ball (0 : ℂ) (r₀ t)).isPreconnected isOpen_ball hGd (mem_ball_self r₀_pos) hmax
      apply hp₁₂
      apply hinj _ hp₁ _ hp₂
      rw [← hGg _ hp₁, ← hGg _ hp₂, hc hp₁.1, hc hp₂.1]
      rfl
    set ℓ₀ := Complex.log L
    have hℓ₀ : Complex.exp ℓ₀ = L := Complex.exp_log hL
    set τL : ℂ := (a / (2 * π * I)) * ℓ₀
    have hτL : 0 < τL.im := by
      have hre : ℓ₀.re = Real.log ‖L‖ := Complex.log_re L
      have hlog : Real.log ‖L‖ < 0 := Real.log_neg (norm_pos_iff.mpr hL) hLlt
      have : τL.im = -(a / (2 * π)) * ℓ₀.re := by
        simp only [τL]
        rw [show (a : ℂ) / (2 * π * I) = ((-(a / (2 * π)) : ℝ) : ℂ) * I by
          rw [div_eq_iff h2πI]; push_cast; field_simp; rw [show I ^ 2 = -1 from I_sq]; ring]
        simp only [mul_im, ofReal_re, ofReal_im, I_re, I_im, mul_zero, zero_mul,
          mul_one, zero_add, add_zero, re_ofReal_mul]
      rw [this, hre]
      have : 0 < a / (2 * π) := by positivity
      nlinarith
    -- the approximating points
    have hGL : Tendsto (fun w ↦ G w / L) (𝓝[≠] 0) (𝓝 1) := by
      have := (hGc.tendsto.mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))).div_const L
      rwa [show G 0 / L = 1 from div_self hL] at this
    have hΛ : Tendsto (fun w ↦ Complex.log (G w / L)) (𝓝[≠] 0) (𝓝 0) := by
      have := (continuousAt_clog Complex.one_mem_slitPlane).tendsto.comp hGL
      rw [Complex.log_one] at this
      exact this
    have hrel : ∀ p ∈ Dst t, ∃ m : ℤ, τ' U M (Complex.log p) - m * κ =
        (a / (2 * π * I)) * (ℓ₀ + Complex.log (G p / L)) := by
      intro p hp
      have hGp : G p / L ≠ 0 := div_ne_zero (by rw [hGg p hp]; exact hgne p) hL
      have h1 : Complex.exp (2 * π * I * τ' U M (Complex.log p) / a) =
          Complex.exp (ℓ₀ + Complex.log (G p / L)) := by
        rw [Complex.exp_add, hℓ₀, Complex.exp_log hGp, mul_div_cancel₀ _ hL, hGg p hp]
      obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp h1
      have hτ : τ' U M (Complex.log p) - n * a =
          (a / (2 * π * I)) * (ℓ₀ + Complex.log (G p / L)) := by
        field_simp at hn ⊢; linear_combination hn
      rcases abs_choice κ with h | h
      · exact ⟨n, by rw [← hτ]; simp [a, h]⟩
      · exact ⟨-n, by rw [← hτ]; simp [a, h]⟩
    choose! mp hmp using hrel
    set ν : ℂ → ℍ := fun p ↦ (M⁻¹ * Cm U * M) ^ (-mp p) • (M⁻¹ • Sig U (Complex.log p))
    have hν : ∀ p ∈ Dst t, (ν p : ℂ) = (a / (2 * π * I)) * (ℓ₀ + Complex.log (G p / L)) := by
      intro p hp
      simp only [ν]
      rw [translation_zpow U hM, ← hmp p hp]
      change τ' U M (Complex.log p) + _ = _
      push_cast; ring
    have hev : ∀ᶠ p in 𝓝[≠] (0 : ℂ), p ∈ Dst t := by
      filter_upwards [inter_mem_nhdsWithin _ hball] with p hp using ⟨hp.2, hp.1⟩
    have hlimν : Tendsto (fun p ↦ (ν p : ℂ)) (𝓝[≠] 0) (𝓝 τL) := by
      have : Tendsto (fun p ↦ (a / (2 * π * I)) * (ℓ₀ + Complex.log (G p / L))) (𝓝[≠] 0)
          (𝓝 ((a / (2 * π * I)) * (ℓ₀ + 0))) :=
        tendsto_const_nhds.mul (tendsto_const_nhds.add hΛ)
      rw [add_zero] at this
      exact this.congr' (hev.mono fun p hp ↦ (hν p hp).symm)
    set νL : ℍ := ⟨τL, hτL⟩
    have hlimν' : Tendsto ν (𝓝[≠] 0) (𝓝 νL) :=
      isOpenEmbedding_coe.isInducing.tendsto_nhds_iff.mpr hlimν
    have hψν : ∀ p ∈ Dst t, U.ψ (M • ν p) = p := by
      intro p hp
      simp only [ν]
      rw [conj_zpow_smul, ψ_Cm_zpow_smul, ψ_Sig U (log_mem_Hr hp), Complex.exp_log hp.2]
    have h1 : Tendsto (fun p ↦ U.ψ (M • ν p)) (𝓝[≠] 0) (𝓝 (U.ψ (M • νL))) :=
      ((U.continuous_ψ.comp (continuous_const_smul M)).tendsto νL).comp hlimν'
    have h2 : Tendsto (fun p ↦ U.ψ (M • ν p)) (𝓝[≠] 0) (𝓝 0) :=
      (tendsto_id.mono_left nhdsWithin_le_nhds).congr' (hev.mono fun p hp ↦ (hψν p hp).symm)
    exact U.ψ_notMem (M • νL) (by rw [tendsto_nhds_unique h1 h2]; exact zero_mem _)
  -- `G` is injective on the disc, so `G′(0) ≠ 0`
  have hGinj : InjOn G (ball 0 (r₀ t)) := by
    intro p hp q hq hpq
    by_cases hp0 : p = 0
    · by_cases hq0 : q = 0
      · rw [hp0, hq0]
      · rw [hp0, hG0, hGg q ⟨hq, hq0⟩] at hpq; exact absurd hpq.symm (hgne q)
    · by_cases hq0 : q = 0
      · rw [hq0, hG0, hGg p ⟨hp, hp0⟩] at hpq; exact absurd hpq (hgne p)
      · rw [hGg p ⟨hp, hp0⟩, hGg q ⟨hq, hq0⟩] at hpq
        exact hinj p ⟨hp, hp0⟩ q ⟨hq, hq0⟩ hpq
  have hG'0 : deriv G 0 ≠ 0 := deriv_ne_zero_of_injOn hGd hball hGinj
  -- `G w = w F(w)` with `F(0) ≠ 0`
  set F := dslope G 0
  have hFd : DifferentiableOn ℂ F (ball 0 (r₀ t)) := (differentiableOn_dslope hball).mpr hGd
  have hF0 : F 0 = deriv G 0 := dslope_same G 0
  have hGF : ∀ w, G w = w * F w := fun w ↦ by
    have := sub_smul_dslope G 0 w
    simp only [sub_zero, smul_eq_mul, hG0] at this
    exact this.symm
  have hFc : ContinuousAt F 0 := (hFd.differentiableAt hball).continuousAt
  have hFF : Tendsto (fun w ↦ F w / F 0) (𝓝 0) (𝓝 1) := by
    have := hFc.tendsto.div_const (F 0)
    rwa [div_self (hF0 ▸ hG'0)] at this
  obtain ⟨r₂', hr₂', hr₂'s⟩ := Metric.eventually_nhds_iff_ball.mp
    (hFF.eventually (Metric.ball_mem_nhds (1 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2)))
  set r₂ := min r₂' (r₀ t)
  have hr₂ : 0 < r₂ := lt_min hr₂' r₀_pos
  have hslit : ∀ w ∈ ball (0 : ℂ) r₂, F w / F 0 ∈ Complex.slitPlane := by
    intro w hw
    have h1 := hr₂'s w (ball_subset_ball (min_le_left _ _) hw)
    rw [dist_eq_norm] at h1
    refine Complex.mem_slitPlane_iff.mpr (Or.inl ?_)
    have := (abs_re_le_norm (F w / F 0 - 1)).trans_lt h1
    rw [sub_re, one_re, abs_lt] at this
    linarith [this.1]
  set φ₀ : ℂ → ℂ := fun w ↦ Complex.log (F w / F 0) + Complex.log (F 0)
  have hF0ne : F 0 ≠ 0 := hF0 ▸ hG'0
  have hφ₀ : ∀ w ∈ ball (0 : ℂ) r₂, Complex.exp (φ₀ w) = F w := by
    intro w hw
    simp only [φ₀]
    rw [Complex.exp_add, Complex.exp_log (Complex.slitPlane_ne_zero (hslit w hw)),
      Complex.exp_log hF0ne, div_mul_cancel₀ _ hF0ne]
  have hφ₀c : ContinuousOn φ₀ (ball 0 r₂) := by
    refine ContinuousOn.add ?_ continuousOn_const
    refine ContinuousOn.clog ?_ hslit
    exact (hFd.continuousOn.mono (ball_subset_ball (min_le_right _ _))).div_const _
  -- the half-plane `{Re s < log r₂}`
  set S : Set ℂ := {s | s.re < Real.log r₂}
  have hSHr : S ⊆ Hr t := fun s hs ↦ by
    simp only [Hr, mem_setOf_eq]
    exact hs.trans_le (Real.log_le_log hr₂ (min_le_right _ _))
  have hexpS : ∀ s ∈ S, Complex.exp s ∈ ball (0 : ℂ) r₂ := fun s hs ↦ by
    rw [mem_ball_zero_iff, Complex.norm_exp]
    calc Real.exp s.re < Real.exp (Real.log r₂) := Real.exp_lt_exp.mpr hs
      _ = r₂ := Real.exp_log hr₂
  have hk1 : ∀ s ∈ S, Complex.exp (2 * π * I * τ' U M s / a - s - φ₀ (Complex.exp s)) = 1 := by
    intro s hs
    have hsD : Complex.exp s ∈ Dst t := exp_mem_Dst (hSHr hs)
    have h1 : E s = Complex.exp s * F (Complex.exp s) := by
      rw [← hgexp s (hSHr hs), ← hGF, hGg _ hsD]
    rw [Complex.exp_sub, Complex.exp_sub, hφ₀ _ (hexpS s hs)]
    change E s / Complex.exp s / F (Complex.exp s) = 1
    rw [h1]
    field_simp [Complex.exp_ne_zero s, show F (Complex.exp s) ≠ 0 from fun h0 ↦ by
      have := hGF (Complex.exp s); rw [h0, mul_zero, hGg _ hsD] at this; exact hgne _ this]
  have hkc : ContinuousOn (fun s ↦ 2 * π * I * τ' U M s / a - s - φ₀ (Complex.exp s)) S := by
    refine ((((continuousOn_const.mul ((differentiableOn_τ' U M).continuousOn.mono hSHr)).div_const
      _).sub continuousOn_id).sub (hφ₀c.comp Complex.continuous_exp.continuousOn hexpS))
  have hSc : IsPreconnected S := (convex_halfSpace_re_lt _).isPreconnected
  set s₀ : ℂ := ((Real.log r₂ - 1 : ℝ) : ℂ)
  have hs₀ : s₀ ∈ S := by simp [S, s₀]
  set k₀ := 2 * π * I * τ' U M s₀ / a - s₀ - φ₀ (Complex.exp s₀)
  have hk : ∀ s ∈ S, 2 * π * I * τ' U M s / a - s - φ₀ (Complex.exp s) = k₀ := fun s hs ↦
    const_of_exp_eq_one hSc hkc hk1 hs hs₀
  have hform : ∀ s ∈ S, τ' U M s = (a / (2 * π * I)) * (s + (φ₀ (Complex.exp s) + k₀)) := by
    intro s hs
    rw [← hk s hs]
    field_simp
    ring
  -- `κ = a`
  have hκpos : κ = a := by
    have hs₂ : s₀ + 2 * π * I ∈ S := by simp [S, s₀]
    have h1 := τ'_add_two_pi U hM (hSHr hs₀)
    rw [hform _ hs₂, hform _ hs₀, show Complex.exp (s₀ + 2 * π * I) = Complex.exp s₀ by
      rw [Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]] at h1
    have h1' : (κ : ℂ) = a := by
      rw [mul_add, mul_add, mul_add] at h1
      have e : (a : ℂ) / (2 * π * I) * (2 * π * I) = a := div_mul_cancel₀ _ h2πI
      linear_combination -h1 + e
    have h2 : (2 * π * I) * ((κ : ℂ) - a) = 0 := by rw [h1', sub_self, mul_zero]
    have : (κ : ℂ) = a := sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_left h2πI)
    exact_mod_cast this
  -- the bound on `φ`
  set r₁ := r₂ / 2 with hr₁def
  have hr₁ : 0 < r₁ := by positivity
  have hr₁₂ : r₁ < r₂ := by rw [hr₁def]; linarith
  obtain ⟨Φ, hΦ⟩ := (isCompact_closedBall (0 : ℂ) r₁).exists_bound_of_continuousOn
    ((hφ₀c.mono (closedBall_subset_ball hr₁₂)).add continuousOn_const
      (g := fun _ ↦ k₀))
  have hr₁₀ : r₁ ≤ r₀ t := hr₁₂.le.trans (min_le_right _ _)
  have hsS : ∀ s : ℂ, s.re < Real.log r₁ → s ∈ S := fun s hs ↦ by
    simp only [S, mem_setOf_eq]
    exact hs.trans (Real.log_lt_log hr₁ hr₁₂)
  refine ⟨M, κ, hκpos ▸ ha, hM, r₁, hr₁, hr₁₀, fun w ↦ φ₀ w + k₀, Φ,
    fun w hw ↦ hΦ w (ball_subset_closedBall hw), fun s hs ↦ ?_, G,
    hGd.mono (ball_subset_ball hr₁₀), hG0, hG'0, fun s hs ↦ ?_⟩
  · rw [hform s (hsS s hs), hκpos]
  · have hsHr := hSHr (hsS s hs)
    rw [hκpos, hGg _ (exp_mem_Dst hsHr)]
    exact (hgexp s hsHr).symm

end Peripheral

end Uniformization
