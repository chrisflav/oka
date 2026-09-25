/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.GAGA.CartanSplit

/-!
# Cartan's lemma near the identity

Let `𝔸` be a finite-dimensional normed `ℂ`-algebra (e.g. matrices with an operator norm) and let
`H` be an `𝔸`-valued holomorphic function on `R_ε × P`, where `R_ε` is the open `ε`-neighbourhood
(in the sup-norm of real and imaginary part) of a closed rectangle with corners `p`, `q`, and `P`
is an open set of parameters. If `H` is uniformly close to `1`, then `H = F₁ F₂` on `R_{ε/2} × P`
with `F₁` holomorphic and invertible on the half-plane `{Re z < q.re + ε/2}` and `F₂` on the
half-strip `{Re z > p.re - ε/2, p.im - ε/2 < Im z < q.im + ε/2}` (times `P`).

The proof is the classical iteration: split `H - 1 = A₁ + A₂` additively
(`Complex.exists_cousin_split_bound`), replace `H` by `(1 - A₁) H (1 - A₂)`, which is quadratically
closer to `1`, on a slightly smaller rectangle, and pass to the limit. The loss of domain at the
`k`-th step is `ε / 2 ^ (k + 2)`, so that the bounds for the splitting grow like `2 ^ k`, which is
compensated by the quadratic convergence.

## Main definitions

- `Complex.rectNhd p q s`: the open rectangle `(p.re - s, q.re + s) × (p.im - s, q.im + s)`.
- `Complex.leftPlane q s`: the half-plane `{Re z < q.re + s}`.
- `Complex.rightStrip p q s`: the half-strip `{Re z > p.re - s, p.im - s < Im z < q.im + s}`.

## Main results

- `Complex.exists_mul_split_of_norm_sub_one_le`: **Cartan's lemma near the identity.**
-/

open Set Filter Metric
open scoped Topology Ring

namespace Complex

section Geometry

/-- The open rectangle `(p.re - s, q.re + s) × (p.im - s, q.im + s)`. -/
def rectNhd (p q : ℂ) (s : ℝ) : Set ℂ :=
  Ioo (p.re - s) (q.re + s) ×ℂ Ioo (p.im - s) (q.im + s)

/-- The open half-plane `{Re z < q.re + s}`. -/
def leftPlane (q : ℂ) (s : ℝ) : Set ℂ :=
  {z | z.re < q.re + s}

/-- The open half-strip `{Re z > p.re - s, p.im - s < Im z < q.im + s}`. -/
def rightStrip (p q : ℂ) (s : ℝ) : Set ℂ :=
  Ioi (p.re - s) ×ℂ Ioo (p.im - s) (q.im + s)

variable {p q z : ℂ} {s t : ℝ}

lemma mem_rectNhd : z ∈ rectNhd p q s ↔
    (p.re - s < z.re ∧ z.re < q.re + s) ∧ p.im - s < z.im ∧ z.im < q.im + s :=
  Iff.rfl

lemma mem_leftPlane : z ∈ leftPlane q s ↔ z.re < q.re + s :=
  Iff.rfl

lemma mem_rightStrip : z ∈ rightStrip p q s ↔
    p.re - s < z.re ∧ p.im - s < z.im ∧ z.im < q.im + s :=
  Iff.rfl

lemma isOpen_rectNhd : IsOpen (rectNhd p q s) :=
  isOpen_Ioo.reProdIm isOpen_Ioo

lemma isOpen_leftPlane : IsOpen (leftPlane q s) :=
  isOpen_lt continuous_re continuous_const

lemma isOpen_rightStrip : IsOpen (rightStrip p q s) :=
  isOpen_Ioi.reProdIm isOpen_Ioo

lemma rectNhd_mono (h : s ≤ t) : rectNhd p q s ⊆ rectNhd p q t := fun z hz ↦ by
  rw [mem_rectNhd] at hz ⊢
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith [hz.1.1, hz.1.2, hz.2.1, hz.2.2]

lemma leftPlane_mono (h : s ≤ t) : leftPlane q s ⊆ leftPlane q t := fun z hz ↦ by
  rw [mem_leftPlane] at hz ⊢
  linarith

lemma rightStrip_mono (h : s ≤ t) : rightStrip p q s ⊆ rightStrip p q t := fun z hz ↦ by
  rw [mem_rightStrip] at hz ⊢
  refine ⟨?_, ?_, ?_⟩ <;> linarith [hz.1, hz.2.1, hz.2.2]

lemma rectNhd_subset_leftPlane : rectNhd p q s ⊆ leftPlane q s :=
  fun _ hz ↦ hz.1.2

lemma rectNhd_subset_rightStrip : rectNhd p q s ⊆ rightStrip p q s :=
  fun _ hz ↦ ⟨hz.1.1, hz.2⟩

end Geometry

section Algebra

variable {𝔸 : Type*} [NormedRing 𝔸]

/-- If `h - 1 = a + b` with `a`, `b`, `h - 1` small, then `(1 - a) h (1 - b)` is quadratically
close to `1`. -/
lemma norm_one_sub_mul_mul_one_sub_sub_one_le {a b h : 𝔸} {s θ : ℝ} (ha : ‖a‖ ≤ s)
    (hb : ‖b‖ ≤ s) (hh : ‖h - 1‖ ≤ θ) (hθs : θ ≤ s) (hs : s ≤ 1) (hab : h - 1 = a + b) :
    ‖(1 - a) * h * (1 - b) - 1‖ ≤ 4 * s ^ 2 := by
  set X := h - 1 with hX
  have e : (1 - a) * h * (1 - b) - 1 = -(a * X) - X * b + a * b + a * X * b := by
    have : h = 1 + (a + b) := by rw [← hab, hX]; abel
    rw [hab, this]
    noncomm_ring
  have hs0 : 0 ≤ s := (norm_nonneg _).trans ha
  have hθ : ‖X‖ ≤ s := hh.trans hθs
  rw [e]
  calc _ ≤ ‖-(a * X) - X * b + a * b‖ + ‖a * X * b‖ := norm_add_le _ _
    _ ≤ ‖-(a * X) - X * b‖ + ‖a * b‖ + ‖a * X * b‖ := by gcongr; exact norm_add_le _ _
    _ ≤ ‖a * X‖ + ‖X * b‖ + ‖a * b‖ + ‖a * X * b‖ := by
        gcongr; exact (norm_sub_le _ _).trans (by rw [norm_neg])
    _ ≤ ‖a‖ * ‖X‖ + ‖X‖ * ‖b‖ + ‖a‖ * ‖b‖ + ‖a‖ * ‖X‖ * ‖b‖ := by
        gcongr
        · exact norm_mul_le _ _
        · exact norm_mul_le _ _
        · exact norm_mul_le _ _
        · exact (norm_mul_le _ _).trans (by gcongr; exact norm_mul_le _ _)
    _ ≤ s * s + s * s + s * s + s * s * s := by gcongr
    _ ≤ 4 * s ^ 2 := by nlinarith

variable [NormOneClass 𝔸] [CompleteSpace 𝔸]

/-- A sequence `u` starting at `1` with `‖u (k + 1) - u k‖ ≤ σ k ‖u k‖`, `σ k ≤ 1 / (64 · 2^k)`,
converges uniformly to a function `v` with `‖v - 1‖ ≤ 1 / 16`. -/
lemma exists_tendstoUniformlyOn_of_norm_succ_sub_le {X : Type*} {S : Set X} {u : ℕ → X → 𝔸}
    {σ : ℕ → ℝ} (hσ0 : ∀ k, 0 ≤ σ k) (hσ : ∀ k, σ k ≤ 1 / (64 * 2 ^ k))
    (hu0 : ∀ x ∈ S, u 0 x = 1)
    (hu : ∀ k, ∀ x ∈ S, ‖u (k + 1) x - u k x‖ ≤ σ k * ‖u k x‖) :
    ∃ v : X → 𝔸, TendstoUniformlyOn u v atTop S ∧ ∀ x ∈ S, ‖v x - 1‖ ≤ 1 / 16 := by
  have hb : ∀ k, ∀ x ∈ S, ‖u k x - 1‖ ≤ 1 / 16 - 1 / 16 / 2 ^ k ∧
      ‖u (k + 1) x - u k x‖ ≤ 1 / 16 / 2 / 2 ^ k := by
    intro k
    induction k with
    | zero =>
      intro x hx
      refine ⟨by simp [hu0 x hx], (hu 0 x hx).trans ?_⟩
      rw [hu0 x hx, norm_one, mul_one]
      exact (hσ 0).trans (by norm_num)
    | succ k ih =>
      intro x hx
      have h2k : (0 : ℝ) < 2 ^ k := by positivity
      have hk := ih x hx
      have h1 : ‖u (k + 1) x - 1‖ ≤ 1 / 16 - 1 / 16 / 2 ^ (k + 1) := by
        calc ‖u (k + 1) x - 1‖ ≤ ‖u (k + 1) x - u k x‖ + ‖u k x - 1‖ :=
              norm_sub_le_norm_sub_add_norm_sub _ _ _
          _ ≤ 1 / 16 / 2 / 2 ^ k + (1 / 16 - 1 / 16 / 2 ^ k) := add_le_add hk.2 hk.1
          _ = 1 / 16 - 1 / 16 / 2 ^ (k + 1) := by rw [pow_succ]; field_simp; ring
      refine ⟨h1, (hu (k + 1) x hx).trans ?_⟩
      have hn : ‖u (k + 1) x‖ ≤ 17 / 16 := by
        calc ‖u (k + 1) x‖ = ‖(u (k + 1) x - 1) + 1‖ := by rw [sub_add_cancel]
          _ ≤ ‖u (k + 1) x - 1‖ + ‖(1 : 𝔸)‖ := norm_add_le _ _
          _ ≤ 17 / 16 := by
              rw [norm_one]
              have : 0 ≤ 1 / 16 / (2 : ℝ) ^ (k + 1) := by positivity
              linarith
      have hσk := hσ (k + 1)
      have hσ0 := hσ0 (k + 1)
      calc σ (k + 1) * ‖u (k + 1) x‖ ≤ 1 / (64 * 2 ^ (k + 1)) * (17 / 16) := by gcongr
        _ ≤ 1 / 16 / 2 / 2 ^ (k + 1) := by
            rw [div_div, div_div, one_div_mul_eq_div, div_le_div_iff₀ (by positivity)
              (by positivity)]
            have : (0 : ℝ) < 2 ^ (k + 1) := by positivity
            nlinarith
  have hcauchy : ∀ x ∈ S, CauchySeq fun k ↦ u k x := fun x hx ↦
    cauchySeq_of_le_geometric_two (C := 1 / 16) fun k ↦ by
      rw [dist_eq_norm, norm_sub_rev]; exact (hb k x hx).2
  refine ⟨fun x ↦ limUnder atTop fun k ↦ u k x, ?_, fun x hx ↦ ?_⟩
  · rw [Metric.tendstoUniformlyOn_iff]
    intro δ hδ
    have ht : Tendsto (fun k : ℕ ↦ 1 / 16 * (1 / 2 : ℝ) ^ k) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num)).const_mul (1 / 16 : ℝ)
    filter_upwards [ht.eventually (gt_mem_nhds hδ)] with k hk x hx
    have := dist_le_of_le_geometric_two_of_tendsto (C := 1 / 16) (fun k ↦ by
      rw [dist_eq_norm, norm_sub_rev]; exact (hb k x hx).2) (hcauchy x hx).tendsto_limUnder k
    rw [dist_comm]
    refine this.trans_lt (lt_of_eq_of_lt ?_ hk)
    rw [one_div_pow, div_eq_mul_one_div]
  · have := dist_le_of_le_geometric_two_of_tendsto₀ (C := 1 / 16) (fun k ↦ by
      rw [dist_eq_norm, norm_sub_rev]; exact (hb k x hx).2) (hcauchy x hx).tendsto_limUnder
    rwa [hu0 x hx, dist_comm, dist_eq_norm] at this

/-- The numerical inequalities behind the quadratic convergence, for `λ = 1 / (64 D²)` and
`t = 2 ^ k`. -/
lemma cartan_numerics {D t : ℝ} (hD : 1 ≤ D) (ht : 1 ≤ t) :
    1 / (64 * D ^ 2) / t ^ 4 ≤ D * t * (1 / (64 * D ^ 2) / t ^ 4) ∧
      D * t * (1 / (64 * D ^ 2) / t ^ 4) ≤ 1 / (64 * t) ∧
      4 * (D * t * (1 / (64 * D ^ 2) / t ^ 4)) ^ 2 ≤ 1 / (64 * D ^ 2) / (t * 2) ^ 4 := by
  have hD0 : 0 < D := by linarith
  have ht0 : 0 < t := by linarith
  have e : D * t * (1 / (64 * D ^ 2) / t ^ 4) = 1 / (64 * (D * t ^ 3)) := by
    field_simp
  refine ⟨le_mul_of_one_le_left (by positivity) (one_le_mul_of_one_le_of_one_le hD ht), ?_, ?_⟩
  · rw [e]
    refine one_div_le_one_div_of_le (by positivity) ?_
    have h1 : t ≤ t ^ 3 := le_self_pow₀ ht (by norm_num)
    have h2 : t ^ 3 ≤ D * t ^ 3 := le_mul_of_one_le_left (by positivity) hD
    linarith
  · rw [e, show 4 * (1 / (64 * (D * t ^ 3))) ^ 2 = 1 / (1024 * D ^ 2 * t ^ 6) by
      field_simp; ring, show 1 / (64 * D ^ 2) / (t * 2) ^ 4 = 1 / (1024 * D ^ 2 * t ^ 4) by
      field_simp; ring]
    refine one_div_le_one_div_of_le (by positivity) ?_
    have : t ^ 4 ≤ t ^ 6 := pow_le_pow_right₀ ht (by norm_num)
    gcongr

end Algebra

section Step

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [FiniteDimensional ℂ 𝔸]

/-- One step of the iteration: the additive splitting of `H - 1` along the boundary of the
rectangle with offset `c`, with bounds on the regions with offset `s = c - η`. -/
lemma exists_cartan_step {p q : ℂ} (hre : p.re ≤ q.re) (him : p.im ≤ q.im) {P : Set E}
    (hP : IsOpen P) {r c s η : ℝ} (hs : 0 < s) (hη : 0 < η) (hsc : s + η = c) (hcr : c < r)
    {H : ℂ × E → 𝔸} (hH : DifferentiableOn ℂ H (rectNhd p q r ×ˢ P)) {θ : ℝ}
    (hHθ : ∀ x ∈ rectNhd p q r ×ˢ P, ‖H x - 1‖ ≤ θ) :
    ∃ A₁ A₂ : ℂ × E → 𝔸, DifferentiableOn ℂ A₁ (leftPlane q s ×ˢ P) ∧
      DifferentiableOn ℂ A₂ (rightStrip p q s ×ˢ P) ∧
      (∀ x ∈ leftPlane q s ×ˢ P,
        ‖A₁ x‖ ≤ cousinSplitConst 𝔸 * ((q.re - p.re) + (q.im - p.im) + 4 * c) * θ / η) ∧
      (∀ x ∈ rightStrip p q s ×ˢ P,
        ‖A₂ x‖ ≤ cousinSplitConst 𝔸 * ((q.re - p.re) + (q.im - p.im) + 4 * c) * θ / η) ∧
      ∀ x ∈ rectNhd p q s ×ˢ P, H x - 1 = A₁ x + A₂ x := by
  set a : ℂ := ⟨p.re - c, p.im - c⟩
  set b : ℂ := ⟨q.re + c, q.im + c⟩
  have hc : 0 < c := by linarith
  have ha_re : a.re = p.re - c := rfl
  have ha_im : a.im = p.im - c := rfl
  have hb_re : b.re = q.re + c := rfl
  have hb_im : b.im = q.im + c := rfl
  have hsub : Icc a.re b.re ×ℂ Icc a.im b.im ⊆ rectNhd p q r := by
    rintro z ⟨⟨h1, h2⟩, h3, h4⟩
    simp only [ha_re, hb_re, ha_im, hb_im] at h1 h2 h3 h4
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  obtain ⟨f₁, f₂, hf₁, hf₂, hsum, hb₁, hb₂⟩ := exists_cousin_split_bound (V := 𝔸)
    (by rw [ha_re, hb_re]; linarith) (by rw [ha_im, hb_im]; linarith) hsub hP (hH.sub_const 1)
    (fun z hz w hw ↦ hHθ (z, w) ⟨hsub hz, hw⟩)
  have hℓ : (b.re - a.re) + (b.im - a.im) = (q.re - p.re) + (q.im - p.im) + 4 * c := by
    rw [ha_re, ha_im, hb_re, hb_im]; ring
  rw [hℓ] at hb₁ hb₂
  refine ⟨f₁, f₂, hf₁.mono (prod_mono (fun z hz ↦ ?_) subset_rfl),
    hf₂.mono (prod_mono (fun z hz ↦ ?_) subset_rfl), ?_, ?_, ?_⟩
  · rw [mem_leftPlane] at hz
    change z.re < b.re
    rw [hb_re]; linarith
  · obtain ⟨h1, h2, h3⟩ := mem_rightStrip.1 hz
    refine ⟨?_, ?_, ?_⟩
    · change a.re < z.re; rw [ha_re]; linarith
    · change a.im < z.im; rw [ha_im]; linarith
    · change z.im < b.im; rw [hb_im]; linarith
  · rintro ⟨z, w⟩ ⟨hz, hw⟩
    rw [mem_leftPlane] at hz
    exact hb₁ η hη z (by rw [hb_re]; linarith) w hw
  · rintro ⟨z, w⟩ ⟨hz, hw⟩
    obtain ⟨h1, h2, h3⟩ := mem_rightStrip.1 hz
    exact hb₂ η hη z (by rw [ha_re]; linarith) (by rw [ha_im]; linarith)
      (by rw [hb_im]; linarith) w hw
  · rintro ⟨z, w⟩ ⟨hz, hw⟩
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := mem_rectNhd.1 hz
    refine hsum z ⟨⟨?_, ?_⟩, ?_, ?_⟩ w hw
    · change a.re < z.re; rw [ha_re]; linarith
    · change z.re < b.re; rw [hb_re]; linarith
    · change a.im < z.im; rw [ha_im]; linarith
    · change z.im < b.im; rw [hb_im]; linarith

variable [NormOneClass 𝔸]

/-- **Cartan's lemma near the identity.** For a closed rectangle with corners `p`, `q` and
`ε > 0` there is `θ > 0` such that the following holds. Let `H` be holomorphic on `R_ε × P`
(`R_ε = rectNhd p q ε`, `P` open) with `‖H - 1‖ ≤ θ`. Then `H = F₁ F₂` on `R_{ε/2} × P`, where `F₁`
is holomorphic and invertible on `leftPlane q (ε / 2) × P` and `F₂` on
`rightStrip p q (ε / 2) × P`. -/
theorem exists_mul_split_of_norm_sub_one_le {p q : ℂ} (hre : p.re ≤ q.re) (him : p.im ≤ q.im)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ θ > 0, ∀ {P : Set E}, IsOpen P → ∀ {H : ℂ × E → 𝔸},
      DifferentiableOn ℂ H (rectNhd p q ε ×ˢ P) → (∀ x ∈ rectNhd p q ε ×ˢ P, ‖H x - 1‖ ≤ θ) →
      ∃ F₁ F₂ : ℂ × E → 𝔸, DifferentiableOn ℂ F₁ (leftPlane q (ε / 2) ×ˢ P) ∧
        (∀ x ∈ leftPlane q (ε / 2) ×ˢ P, IsUnit (F₁ x)) ∧
        DifferentiableOn ℂ F₂ (rightStrip p q (ε / 2) ×ˢ P) ∧
        (∀ x ∈ rightStrip p q (ε / 2) ×ˢ P, IsUnit (F₂ x)) ∧
        ∀ x ∈ rectNhd p q (ε / 2) ×ˢ P, H x = F₁ x * F₂ x := by
  haveI : CompleteSpace 𝔸 := FiniteDimensional.complete ℂ 𝔸
  set C := cousinSplitConst 𝔸
  have hC : 0 < C := cousinSplitConst_pos
  set ℓ₀ := (q.re - p.re) + (q.im - p.im) + 4 * ε
  have hℓ₀ : 0 < ℓ₀ := by simp only [ℓ₀]; linarith
  set D := 8 * C * ℓ₀ / ε + 1
  have hD : 1 ≤ D := by
    have : 0 ≤ 8 * C * ℓ₀ / ε := by positivity
    linarith
  set lam := 1 / (64 * D ^ 2)
  have hlam : 0 < lam := by positivity
  refine ⟨lam, hlam, ?_⟩
  intro P hP H₀ hH₀ hH₀θ
  -- the shrinking offsets `r k = ε / 2 + ε / 2 ^ (k + 1)`
  set r : ℕ → ℝ := fun k ↦ ε / 2 + ε / 2 ^ (k + 1)
  have hr0 : r 0 = ε := by simp only [r]; ring
  have hr_le : ∀ k, r k ≤ ε := fun k ↦ by
    have : ε / 2 ^ (k + 1) ≤ ε / 2 := div_le_div_of_nonneg_left hε.le two_pos
      (le_self_pow₀ one_le_two (by omega))
    simp only [r]; linarith
  have hr_half : ∀ k, ε / 2 ≤ r k := fun k ↦ by
    have : 0 < ε / 2 ^ (k + 1) := by positivity
    simp only [r]; linarith
  have hr_succ : ∀ k, r (k + 1) + ε / 2 ^ (k + 3) + ε / 2 ^ (k + 3) = r k := fun k ↦ by
    simp only [r, pow_succ]; field_simp; ring
  set σ : ℕ → ℝ := fun k ↦ D * 2 ^ k * (lam / (2 ^ k) ^ 4)
  set Good : ℕ → (ℂ × E → 𝔸) → Prop := fun k H ↦
    DifferentiableOn ℂ H (rectNhd p q (r k) ×ˢ P) ∧
      ∀ x ∈ rectNhd p q (r k) ×ˢ P, ‖H x - 1‖ ≤ lam / (2 ^ k) ^ 4
  have hnum : ∀ k : ℕ, _ := fun k ↦ cartan_numerics hD (one_le_pow₀ one_le_two : (1 : ℝ) ≤ 2 ^ k)
  have step : ∀ k (H : ℂ × E → 𝔸), Good k H → ∃ A : (ℂ × E → 𝔸) × (ℂ × E → 𝔸),
      DifferentiableOn ℂ A.1 (leftPlane q (r (k + 1)) ×ˢ P) ∧
      DifferentiableOn ℂ A.2 (rightStrip p q (r (k + 1)) ×ˢ P) ∧
      (∀ x ∈ leftPlane q (r (k + 1)) ×ˢ P, ‖A.1 x‖ ≤ σ k) ∧
      (∀ x ∈ rightStrip p q (r (k + 1)) ×ˢ P, ‖A.2 x‖ ≤ σ k) ∧
      Good (k + 1) ((1 - A.1) * H * (1 - A.2)) := by
    rintro k H ⟨hH, hHθ⟩
    set η := ε / 2 ^ (k + 3)
    have hη : 0 < η := by positivity
    obtain ⟨A₁, A₂, h₁, h₂, hb₁, hb₂, hsum⟩ := exists_cartan_step hre him hP (r := r k)
      (c := r (k + 1) + η) (s := r (k + 1)) (by linarith [hr_half (k + 1)]) hη rfl
      (by linarith [hr_succ k]) hH hHθ
    have hσ : C * ((q.re - p.re) + (q.im - p.im) + 4 * (r (k + 1) + η)) *
        (lam / (2 ^ k) ^ 4) / η ≤ σ k := by
      have hℓ : (q.re - p.re) + (q.im - p.im) + 4 * (r (k + 1) + η) ≤ ℓ₀ := by
        simp only [ℓ₀]; linarith [hr_succ k, hr_le k]
      calc _ ≤ C * ℓ₀ * (lam / (2 ^ k) ^ 4) / η := by gcongr
        _ = 8 * C * ℓ₀ / ε * 2 ^ k * (lam / (2 ^ k) ^ 4) := by
            simp only [η, pow_add]; field_simp; ring
        _ ≤ σ k := by
            simp only [σ, D]
            gcongr
            linarith
    obtain ⟨hn1, -, hn3⟩ := hnum k
    have hσ1 : σ k ≤ 1 := (hnum k).2.1.trans (by
      rw [div_le_one (by positivity)]
      have : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ one_le_two
      linarith)
    have hsub₁ : rectNhd p q (r (k + 1)) ×ˢ P ⊆ leftPlane q (r (k + 1)) ×ˢ P :=
      prod_mono rectNhd_subset_leftPlane subset_rfl
    have hsub₂ : rectNhd p q (r (k + 1)) ×ˢ P ⊆ rightStrip p q (r (k + 1)) ×ˢ P :=
      prod_mono rectNhd_subset_rightStrip subset_rfl
    have hsub : rectNhd p q (r (k + 1)) ×ˢ P ⊆ rectNhd p q (r k) ×ˢ P :=
      prod_mono (rectNhd_mono (by linarith [hr_succ k])) subset_rfl
    refine ⟨(A₁, A₂), h₁, h₂, fun x hx ↦ (hb₁ x hx).trans hσ, fun x hx ↦ (hb₂ x hx).trans hσ,
      ?_, fun x hx ↦ ?_⟩
    · exact (((differentiableOn_const 1).sub (h₁.mono hsub₁)).mul (hH.mono hsub)).mul
        ((differentiableOn_const 1).sub (h₂.mono hsub₂))
    · have := norm_one_sub_mul_mul_one_sub_sub_one_le ((hb₁ x (hsub₁ hx)).trans hσ)
        ((hb₂ x (hsub₂ hx)).trans hσ) (hHθ x (hsub hx)) hn1 hσ1 (hsum x hx)
      rw [pow_succ]
      exact this.trans hn3
  choose! A hA using step
  -- the iteration
  obtain ⟨Hs, hHs0, hHs_succ⟩ : ∃ Hs : ℕ → ℂ × E → 𝔸, Hs 0 = H₀ ∧
      ∀ k, Hs (k + 1) = (1 - (A k (Hs k)).1) * Hs k * (1 - (A k (Hs k)).2) :=
    ⟨fun k ↦ Nat.rec (motive := fun _ ↦ ℂ × E → 𝔸) H₀
      (fun k Hk ↦ (1 - (A k Hk).1) * Hk * (1 - (A k Hk).2)) k, rfl, fun _ ↦ rfl⟩
  have hgood : ∀ k, Good k (Hs k) := by
    intro k
    induction k with
    | zero =>
      rw [hHs0]
      refine ⟨by rw [hr0]; exact hH₀, fun x hx ↦ ?_⟩
      rw [hr0] at hx
      simpa using hH₀θ x hx
    | succ k ih => rw [hHs_succ]; exact (hA k _ ih).2.2.2.2
  set a₁ : ℕ → ℂ × E → 𝔸 := fun k ↦ (A k (Hs k)).1
  set a₂ : ℕ → ℂ × E → 𝔸 := fun k ↦ (A k (Hs k)).2
  have hHs_succ' : ∀ k, Hs (k + 1) = (1 - a₁ k) * Hs k * (1 - a₂ k) := hHs_succ
  have ha₁def : ∀ k, a₁ k = (A k (Hs k)).1 := fun _ ↦ rfl
  have ha₂def : ∀ k, a₂ k = (A k (Hs k)).2 := fun _ ↦ rfl
  clear_value a₁ a₂
  obtain ⟨Ps, hPs0, hPs_succ⟩ : ∃ Ps : ℕ → ℂ × E → 𝔸, Ps 0 = 1 ∧
      ∀ k, Ps (k + 1) = (1 - a₁ k) * Ps k :=
    ⟨fun k ↦ Nat.rec (motive := fun _ ↦ ℂ × E → 𝔸) 1 (fun k Pk ↦ (1 - a₁ k) * Pk) k, rfl,
      fun _ ↦ rfl⟩
  obtain ⟨Qs, hQs0, hQs_succ⟩ : ∃ Qs : ℕ → ℂ × E → 𝔸, Qs 0 = 1 ∧
      ∀ k, Qs (k + 1) = Qs k * (1 - a₂ k) :=
    ⟨fun k ↦ Nat.rec (motive := fun _ ↦ ℂ × E → 𝔸) 1 (fun k Qk ↦ Qk * (1 - a₂ k)) k, rfl,
      fun _ ↦ rfl⟩
  have hid : ∀ k, Hs k = Ps k * H₀ * Qs k := by
    intro k
    induction k with
    | zero => rw [hHs0, hPs0, hQs0, one_mul, mul_one]
    | succ k ih =>
      rw [hHs_succ', hPs_succ, hQs_succ, ih]
      simp only [mul_assoc]
  set S₁ := leftPlane q (ε / 2) ×ˢ P
  set S₂ := rightStrip p q (ε / 2) ×ˢ P
  have hS₁ : ∀ k, S₁ ⊆ leftPlane q (r (k + 1)) ×ˢ P := fun k ↦
    prod_mono (leftPlane_mono (hr_half _)) subset_rfl
  have hS₂ : ∀ k, S₂ ⊆ rightStrip p q (r (k + 1)) ×ˢ P := fun k ↦
    prod_mono (rightStrip_mono (hr_half _)) subset_rfl
  have ha₁ : ∀ k, DifferentiableOn ℂ (a₁ k) S₁ ∧ ∀ x ∈ S₁, ‖a₁ k x‖ ≤ σ k := fun k ↦
    ⟨ha₁def k ▸ (hA k _ (hgood k)).1.mono (hS₁ k),
      fun x hx ↦ ha₁def k ▸ (hA k _ (hgood k)).2.2.1 x (hS₁ k hx)⟩
  have ha₂ : ∀ k, DifferentiableOn ℂ (a₂ k) S₂ ∧ ∀ x ∈ S₂, ‖a₂ k x‖ ≤ σ k := fun k ↦
    ⟨ha₂def k ▸ (hA k _ (hgood k)).2.1.mono (hS₂ k),
      fun x hx ↦ ha₂def k ▸ (hA k _ (hgood k)).2.2.2.1 x (hS₂ k hx)⟩
  have hσ0 : ∀ k, 0 ≤ σ k := fun k ↦ by positivity
  have hσle : ∀ k, σ k ≤ 1 / (64 * 2 ^ k) := fun k ↦ (hnum k).2.1
  obtain ⟨v₁, hv₁, hv₁1⟩ := exists_tendstoUniformlyOn_of_norm_succ_sub_le (S := S₁) (u := Ps)
    hσ0 hσle (fun x _ ↦ by rw [hPs0]; rfl) fun k x hx ↦ by
      rw [hPs_succ]
      change ‖(1 - a₁ k x) * Ps k x - Ps k x‖ ≤ _
      rw [sub_mul, one_mul, sub_sub_cancel_left, norm_neg]
      exact (norm_mul_le _ _).trans (by gcongr; exact (ha₁ k).2 x hx)
  obtain ⟨v₂, hv₂, hv₂1⟩ := exists_tendstoUniformlyOn_of_norm_succ_sub_le (S := S₂) (u := Qs)
    hσ0 hσle (fun x _ ↦ by rw [hQs0]; rfl) fun k x hx ↦ by
      rw [hQs_succ]
      change ‖Qs k x * (1 - a₂ k x) - Qs k x‖ ≤ _
      rw [mul_sub, mul_one, sub_sub_cancel_left, norm_neg, mul_comm (σ k)]
      exact (norm_mul_le _ _).trans (by gcongr; exact (ha₂ k).2 x hx)
  have hS₁o : IsOpen S₁ := isOpen_leftPlane.prod hP
  have hS₂o : IsOpen S₂ := isOpen_rightStrip.prod hP
  have hPsd : ∀ k, DifferentiableOn ℂ (Ps k) S₁ := by
    intro k
    induction k with
    | zero => rw [hPs0]; exact differentiableOn_const 1
    | succ k ih => rw [hPs_succ]; exact ((differentiableOn_const 1).sub (ha₁ k).1).mul ih
  have hQsd : ∀ k, DifferentiableOn ℂ (Qs k) S₂ := by
    intro k
    induction k with
    | zero => rw [hQs0]; exact differentiableOn_const 1
    | succ k ih => rw [hQs_succ]; exact ih.mul ((differentiableOn_const 1).sub (ha₂ k).1)
  have hv₁d : DifferentiableOn ℂ v₁ S₁ :=
    differentiableOn_of_tendstoLocallyUniformlyOn_of_finiteDimensional hS₁o hPsd
      hv₁.tendstoLocallyUniformlyOn
  have hv₂d : DifferentiableOn ℂ v₂ S₂ :=
    differentiableOn_of_tendstoLocallyUniformlyOn_of_finiteDimensional hS₂o hQsd
      hv₂.tendstoLocallyUniformlyOn
  have hunit : ∀ {w : 𝔸}, ‖w - 1‖ ≤ 1 / 16 → IsUnit w := fun {w} hw ↦ by
    have h : ‖1 - w‖ < 1 := by rw [norm_sub_rev]; linarith
    simpa using (Units.oneSub (1 - w) h).isUnit
  have hv₁u : ∀ x ∈ S₁, IsUnit (v₁ x) := fun x hx ↦ hunit (hv₁1 x hx)
  have hv₂u : ∀ x ∈ S₂, IsUnit (v₂ x) := fun x hx ↦ hunit (hv₂1 x hx)
  refine ⟨fun x ↦ (v₁ x)⁻¹ʳ, fun x ↦ (v₂ x)⁻¹ʳ, hv₁d.inverse hv₁u,
    fun x hx ↦ (hv₁u x hx).ringInverse, hv₂d.inverse hv₂u,
    fun x hx ↦ (hv₂u x hx).ringInverse, fun x hx ↦ ?_⟩
  have hx₁ : x ∈ S₁ := ⟨rectNhd_subset_leftPlane hx.1, hx.2⟩
  have hx₂ : x ∈ S₂ := ⟨rectNhd_subset_rightStrip hx.1, hx.2⟩
  have t1 : Tendsto (fun k ↦ Hs k x) atTop (𝓝 1) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ ↦ norm_nonneg _)
      (fun k ↦ (hgood k).2 x ⟨rectNhd_mono (hr_half k) hx.1, hx.2⟩) ?_
    exact tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (by norm_num : 4 ≠ 0)).comp
      (tendsto_pow_atTop_atTop_of_one_lt one_lt_two))
  have t2 : Tendsto (fun k ↦ Hs k x) atTop (𝓝 (v₁ x * H₀ x * v₂ x)) := by
    simp_rw [hid]
    exact ((hv₁.tendsto_at hx₁).mul tendsto_const_nhds).mul (hv₂.tendsto_at hx₂)
  have h1 := tendsto_nhds_unique t2 t1
  obtain ⟨u, hu⟩ := hv₁u x hx₁
  obtain ⟨w, hw⟩ := hv₂u x hx₂
  change H₀ x = (v₁ x)⁻¹ʳ * (v₂ x)⁻¹ʳ
  rw [← hu, ← hw, Ring.inverse_unit, Ring.inverse_unit]
  rw [← hu, ← hw] at h1
  calc H₀ x = ↑u⁻¹ * (↑u * H₀ x * ↑w) * ↑w⁻¹ := by
        simp only [mul_assoc, Units.inv_mul_cancel_left, Units.mul_inv, mul_one]
    _ = ↑u⁻¹ * ↑w⁻¹ := by rw [h1, mul_one]

end Step

end Complex
