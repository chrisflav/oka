/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Uniformization.Generators
import Oka.Uniformization.SL2Facts

/-!
# The monodromy around a lattice point is the commutator of the edge pairings

Let `Λ = ℤ t + ℤ` and `ψ : ℍ → ℂ ∖ Λ` with deck group `Γ` and edge pairings `A`, `B`
(`Oka/Uniformization/Generators.lean`). Near the lattice point `0`, the four parallelograms meeting
at `0` are the quadrants `Q₁ = {x, y ≥ 0}`, `Q₂ = {x ≤ 0 ≤ y}`, `Q₃ = {x, y ≤ 0}`,
`Q₄ = {y ≤ 0 ≤ x}` of the lattice coordinates, and over a small punctured disc `D*` the lifts
`σ₁ = sK`, `σ₂ = A⁻¹ sK(· + 1)`, `σ₃ = A⁻¹ B⁻¹ sK(· + 1 + t)`, `σ₄ = A⁻¹ B⁻¹ A sK(· + t)` of the
four pieces glue along the rays `Q₁ ∩ Q₂`, `Q₂ ∩ Q₃`, `Q₃ ∩ Q₄`, while `σ₄ = C σ₁` on `Q₄ ∩ Q₁`,
where `C = A⁻¹ B⁻¹ A B`.

Lifting `exp : {Re s < log r₀} → D*` through `ψ` to `Sig`, and following it across the five strips
`0 ≤ Im s ≤ α`, `α ≤ Im s ≤ π`, …, `2π ≤ Im s ≤ 2π + α` (`α = arg t`, the angle of the lattice
direction `t`), gives the monodromy relation (`Peripheral.Sig_add_two_pi`)

`Sig (s + 2π i) = C • Sig s`,

and `Sig` is holomorphic (`Peripheral.differentiableOn_Sig`).
-/

open Complex Metric Set Filter Topology
open UpperHalfPlane hiding I I_re I_im
open scoped MatrixGroups Real

namespace Uniformization

namespace Peripheral

open Generators

variable {t : ℍ} (U : Unif (Lt t))

/-! ### A small disc about `0` -/

theorem exists_r₀ (t : ℍ) :
    ∃ r > 0, ∀ z ∈ ball (0 : ℂ) r, |cx t z| < 1 / 2 ∧ |cy t z| < 1 / 2 := by
  have hO : IsOpen {z : ℂ | |cx t z| < 1 / 2 ∧ |cy t z| < 1 / 2} :=
    (isOpen_lt (continuous_abs.comp (continuous_cx t)) continuous_const).inter
      (isOpen_lt (continuous_abs.comp (continuous_cy t)) continuous_const)
  have h0 : (0 : ℂ) ∈ {z : ℂ | |cx t z| < 1 / 2 ∧ |cy t z| < 1 / 2} := by
    simp [cx, cy]
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hO 0 h0
  exact ⟨r, hr, fun z hz ↦ hsub hz⟩

/-- A radius `r₀` such that `ball 0 r₀` lies in the box `|x|, |y| < 1/2`. -/
noncomputable def r₀ (t : ℍ) : ℝ := (exists_r₀ t).choose

theorem r₀_pos : 0 < r₀ t := (exists_r₀ t).choose_spec.1

theorem box {z : ℂ} (hz : z ∈ ball (0 : ℂ) (r₀ t)) : |cx t z| < 1 / 2 ∧ |cy t z| < 1 / 2 :=
  (exists_r₀ t).choose_spec.2 z hz

/-- The punctured disc `D*`. -/
def Dst (t : ℍ) : Set ℂ := ball 0 (r₀ t) \ {0}

theorem eq_zero_of_cx_cy {z : ℂ} (hx : cx t z = 0) (hy : cy t z = 0) : z = 0 := by
  rw [eq_cx_cy t z, hx, hy]; simp

theorem Dst_notMem {z : ℂ} (hz : z ∈ Dst t) : z ∉ (Lt t).lattice := by
  intro hl
  obtain ⟨m, n, hm, hn⟩ := (mem_lattice_iff t z).mp hl
  obtain ⟨hx, hy⟩ := box hz.1
  rw [hm] at hy; rw [hn] at hx
  have hm0 : m = 0 := by
    have : |(m : ℝ)| < 1 := by linarith
    have : |m| < 1 := by exact_mod_cast this
    have := abs_lt.mp this
    omega
  have hn0 : n = 0 := by
    have : |(n : ℝ)| < 1 := by linarith
    have : |n| < 1 := by exact_mod_cast this
    have := abs_lt.mp this
    omega
  subst hm0; subst hn0
  exact hz.2 (eq_zero_of_cx_cy (by simpa using hn) (by simpa using hm))

/-! ### The four quadrants and the lifts over them -/

/-- `Q₁ = {x ≥ 0, y ≥ 0}`. -/
def Q₁ (t : ℍ) : Set ℂ := {z | 0 ≤ cx t z ∧ 0 ≤ cy t z}
/-- `Q₂ = {x ≤ 0, y ≥ 0}`. -/
def Q₂ (t : ℍ) : Set ℂ := {z | cx t z ≤ 0 ∧ 0 ≤ cy t z}
/-- `Q₃ = {x ≤ 0, y ≤ 0}`. -/
def Q₃ (t : ℍ) : Set ℂ := {z | cx t z ≤ 0 ∧ cy t z ≤ 0}
/-- `Q₄ = {x ≥ 0, y ≤ 0}`. -/
def Q₄ (t : ℍ) : Set ℂ := {z | 0 ≤ cx t z ∧ cy t z ≤ 0}

theorem mem_K₁ {z : ℂ} (hz : z ∈ Dst t) (hq : z ∈ Q₁ t) : z ∈ K t := by
  obtain ⟨hx, hy⟩ := box hz.1
  rw [abs_lt] at hx hy
  obtain ⟨h1, h2⟩ := hq
  rcases h2.lt_or_eq with h2 | h2
  · exact Or.inl ⟨h1, by linarith, h2, by linarith⟩
  · rcases h1.lt_or_eq with h1 | h1
    · exact Or.inr ⟨h1, by linarith, h2.le, by linarith⟩
    · exact absurd (eq_zero_of_cx_cy h1.symm h2.symm) hz.2

theorem mem_K₂ {z : ℂ} (hz : z ∈ Dst t) (hq : z ∈ Q₂ t) : z + 1 ∈ K t := by
  obtain ⟨hx, hy⟩ := box hz.1
  rw [abs_lt] at hx hy
  obtain ⟨h1, h2⟩ := hq
  have ex : cx t (z + 1) = cx t z + 1 := by rw [cx_add, cx_one]
  have ey : cy t (z + 1) = cy t z := by rw [cy_add, cy_one, add_zero]
  rcases h2.lt_or_eq with h2 | h2
  · exact Or.inl ⟨by rw [ex]; linarith, by rw [ex]; linarith, by rw [ey]; linarith,
      by rw [ey]; linarith⟩
  · rcases h1.lt_or_eq with h1 | h1
    · exact Or.inr ⟨by rw [ex]; linarith, by rw [ex]; linarith, by rw [ey]; linarith,
        by rw [ey]; linarith⟩
    · exact absurd (eq_zero_of_cx_cy h1 h2.symm) hz.2

theorem mem_K₃ {z : ℂ} (hz : z ∈ Dst t) (hq : z ∈ Q₃ t) : z + 1 + t ∈ K t := by
  obtain ⟨hx, hy⟩ := box hz.1
  rw [abs_lt] at hx hy
  obtain ⟨h1, h2⟩ := hq
  have ex : cx t (z + 1 + t) = cx t z + 1 := by rw [cx_add, cx_add, cx_one, cx_t]; ring
  have ey : cy t (z + 1 + t) = cy t z + 1 := by rw [cy_add, cy_add, cy_one, cy_t]; ring
  rcases h2.lt_or_eq with h2 | h2
  · exact Or.inl ⟨by rw [ex]; linarith, by rw [ex]; linarith, by rw [ey]; linarith,
      by rw [ey]; linarith⟩
  · rcases h1.lt_or_eq with h1 | h1
    · exact Or.inr ⟨by rw [ex]; linarith, by rw [ex]; linarith, by rw [ey]; linarith,
        by rw [ey]; linarith⟩
    · exact absurd (eq_zero_of_cx_cy h1 h2) hz.2

theorem mem_K₄ {z : ℂ} (hz : z ∈ Dst t) (hq : z ∈ Q₄ t) : z + t ∈ K t := by
  obtain ⟨hx, hy⟩ := box hz.1
  rw [abs_lt] at hx hy
  obtain ⟨h1, h2⟩ := hq
  have ex : cx t (z + t) = cx t z := by rw [cx_add, cx_t, add_zero]
  have ey : cy t (z + t) = cy t z + 1 := by rw [cy_add, cy_t]
  rcases h2.lt_or_eq with h2 | h2
  · exact Or.inl ⟨by rw [ex]; linarith, by rw [ex]; linarith, by rw [ey]; linarith,
      by rw [ey]; linarith⟩
  · rcases h1.lt_or_eq with h1 | h1
    · exact Or.inr ⟨by rw [ex]; linarith, by rw [ex]; linarith, by rw [ey]; linarith,
        by rw [ey]; linarith⟩
    · exact absurd (eq_zero_of_cx_cy h1.symm h2) hz.2

/-- The monodromy candidate `C = A⁻¹ B⁻¹ A B`. -/
noncomputable def Cm : SL(2, ℝ) := (A U)⁻¹ * (B U)⁻¹ * A U * B U

/-- The lift over `Q₁`. -/
noncomputable def σ₁ (z : ℂ) : ℍ := sK U z
/-- The lift over `Q₂`. -/
noncomputable def σ₂ (z : ℂ) : ℍ := (A U)⁻¹ • sK U (z + 1)
/-- The lift over `Q₃`. -/
noncomputable def σ₃ (z : ℂ) : ℍ := (A U)⁻¹ • (B U)⁻¹ • sK U (z + 1 + t)
/-- The lift over `Q₄`. -/
noncomputable def σ₄ (z : ℂ) : ℍ := (A U)⁻¹ • (B U)⁻¹ • A U • sK U (z + t)

theorem ψ_σ₁ {z : ℂ} (hz : z ∈ Dst t) (hq : z ∈ Q₁ t) : U.ψ (σ₁ U z) = z :=
  ψ_sK U (mem_K₁ hz hq)

theorem ψ_σ₂ {z : ℂ} (hz : z ∈ Dst t) (hq : z ∈ Q₂ t) : U.ψ (σ₂ U z) = z := by
  rw [σ₂, ψ_A_inv_smul, ψ_sK U (mem_K₂ hz hq)]; ring

theorem ψ_σ₃ {z : ℂ} (hz : z ∈ Dst t) (hq : z ∈ Q₃ t) : U.ψ (σ₃ U z) = z := by
  rw [σ₃, ψ_A_inv_smul, ψ_B_inv_smul, ψ_sK U (mem_K₃ hz hq)]; ring

theorem ψ_σ₄ {z : ℂ} (hz : z ∈ Dst t) (hq : z ∈ Q₄ t) : U.ψ (σ₄ U z) = z := by
  rw [σ₄, ψ_A_inv_smul, ψ_B_inv_smul, ψ_A_smul, ψ_sK U (mem_K₄ hz hq)]; ring

theorem ψ_Cm_smul (τ : ℍ) : U.ψ (Cm U • τ) = U.ψ τ := by
  rw [Cm, mul_smul, mul_smul, mul_smul, ψ_A_inv_smul, ψ_B_inv_smul, ψ_A_smul, ψ_B_smul]; ring

theorem Cm_mem : Cm U ∈ U.deckGroup := ⟨0, zero_mem _, fun τ ↦ by rw [ψ_Cm_smul, add_zero]⟩

/-- `sK` is continuous on the whole of `K`. -/
theorem continuousOn_sK : ContinuousOn (sK U) (K t) := by
  intro k hk
  rcases hk with hk | hk
  · refine ((continuousOn_sK₁ U) k hk).mono_of_mem_nhdsWithin ?_
    refine mem_nhdsWithin.mpr ⟨{z | 0 < cy t z ∧ cy t z < 1},
      (isOpen_lt continuous_const (continuous_cy t)).inter
        (isOpen_lt (continuous_cy t) continuous_const), ⟨hk.2.2.1, hk.2.2.2⟩, ?_⟩
    rintro z ⟨⟨h1, h2⟩, hz⟩
    rcases hz with hz | hz
    · exact hz
    · exact ⟨hz.1.le, hz.2.1.le, h1, h2⟩
  · refine ((continuousOn_sK₂ U) k hk).mono_of_mem_nhdsWithin ?_
    refine mem_nhdsWithin.mpr ⟨{z | 0 < cx t z ∧ cx t z < 1},
      (isOpen_lt continuous_const (continuous_cx t)).inter
        (isOpen_lt (continuous_cx t) continuous_const), ⟨hk.1, hk.2.1⟩, ?_⟩
    rintro z ⟨⟨h1, h2⟩, hz⟩
    rcases hz with hz | hz
    · exact ⟨h1, h2, hz.2.2.1.le, hz.2.2.2.le⟩
    · exact hz

theorem continuousOn_σ₁ : ContinuousOn (σ₁ U) (Dst t ∩ Q₁ t) :=
  (continuousOn_sK U).mono fun _ hz ↦ mem_K₁ hz.1 hz.2

theorem continuousOn_σ₂ : ContinuousOn (σ₂ U) (Dst t ∩ Q₂ t) :=
  (continuous_const_smul _).comp_continuousOn ((continuousOn_sK U).comp
    (continuous_add_const 1).continuousOn fun _ hz ↦ mem_K₂ hz.1 hz.2)

theorem continuousOn_σ₃ : ContinuousOn (σ₃ U) (Dst t ∩ Q₃ t) :=
  (continuous_const_smul _).comp_continuousOn ((continuous_const_smul _).comp_continuousOn
    ((continuousOn_sK U).comp ((continuous_add_const 1).add continuous_const).continuousOn
      fun _ hz ↦ mem_K₃ hz.1 hz.2))

theorem continuousOn_σ₄ : ContinuousOn (σ₄ U) (Dst t ∩ Q₄ t) :=
  (continuous_const_smul _).comp_continuousOn ((continuous_const_smul _).comp_continuousOn
    ((continuous_const_smul _).comp_continuousOn ((continuousOn_sK U).comp
      (continuous_add_const _).continuousOn fun _ hz ↦ mem_K₄ hz.1 hz.2)))

/-! ### The seams -/

theorem seam₁₂ {z : ℂ} (hz : z ∈ Dst t) (hx : cx t z = 0) (hy : 0 ≤ cy t z) :
    σ₂ U z = σ₁ U z := by
  obtain ⟨-, hby⟩ := box hz.1
  rw [abs_lt] at hby
  have hy' : 0 < cy t z := hy.lt_of_ne fun h ↦ hz.2 (eq_zero_of_cx_cy hx h.symm)
  have hE : z ∈ EL t := ⟨hx, hy', by linarith⟩
  rw [σ₂, σ₁, ← A_smul_sK U hE, inv_smul_smul]

theorem seam₂₃ {z : ℂ} (hz : z ∈ Dst t) (hx : cx t z ≤ 0) (hy : cy t z = 0) :
    σ₃ U z = σ₂ U z := by
  obtain ⟨hbx, -⟩ := box hz.1
  rw [abs_lt] at hbx
  have hx' : cx t z < 0 := hx.lt_of_ne fun h ↦ hz.2 (eq_zero_of_cx_cy h hy)
  have hE : z + 1 ∈ EB t := ⟨by rw [cy_add, cy_one, hy, add_zero],
    by rw [cx_add, cx_one]; linarith, by rw [cx_add, cx_one]; linarith⟩
  rw [σ₃, σ₂, ← B_smul_sK U hE, inv_smul_smul]

theorem seam₃₄ {z : ℂ} (hz : z ∈ Dst t) (hx : cx t z = 0) (hy : cy t z ≤ 0) :
    σ₄ U z = σ₃ U z := by
  obtain ⟨-, hby⟩ := box hz.1
  rw [abs_lt] at hby
  have hy' : cy t z < 0 := hy.lt_of_ne fun h ↦ hz.2 (eq_zero_of_cx_cy hx h)
  have hE : z + t ∈ EL t := ⟨by rw [cx_add, cx_t, hx, add_zero],
    by rw [cy_add, cy_t]; linarith, by rw [cy_add, cy_t]; linarith⟩
  rw [σ₄, σ₃, A_smul_sK U hE, show z + t + 1 = z + 1 + t by ring]

theorem seam₄₁ {z : ℂ} (hz : z ∈ Dst t) (hx : 0 ≤ cx t z) (hy : cy t z = 0) :
    σ₄ U z = Cm U • σ₁ U z := by
  obtain ⟨hbx, -⟩ := box hz.1
  rw [abs_lt] at hbx
  have hx' : 0 < cx t z := hx.lt_of_ne fun h ↦ hz.2 (eq_zero_of_cx_cy h.symm hy)
  have hE : z ∈ EB t := ⟨hy, hx', by linarith⟩
  rw [σ₄, σ₁, Cm, ← B_smul_sK U hE, mul_smul, mul_smul, mul_smul]

/-! ### The exponential and the angles of the quadrants -/

/-- The angle `α = arg t` of the lattice direction `t`. -/
noncomputable def α (t : ℍ) : ℝ := Complex.arg (t : ℂ)

theorem α_nonneg : 0 ≤ α t := Complex.arg_nonneg_iff.mpr t.im_pos.le
theorem α_le_pi : α t ≤ π := Complex.arg_le_pi _

theorem cy_exp (s : ℂ) : cy t (Complex.exp s) = Real.exp s.re * Real.sin s.im / t.im := by
  simp [cy, Complex.exp_im]

theorem cx_exp (s : ℂ) :
    cx t (Complex.exp s) = Real.exp s.re * (‖(t : ℂ)‖ * Real.sin (α t - s.im)) / t.im := by
  have ht := t.im_pos.ne'
  have h1 := Complex.norm_mul_cos_arg (t : ℂ)
  have h2 := Complex.norm_mul_sin_arg (t : ℂ)
  rw [cx, cy_exp, Real.sin_sub, mul_sub, ← mul_assoc, ← mul_assoc, α, h2, h1]
  simp only [Complex.exp_re, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  field_simp

theorem cx_exp_nonneg_iff (s : ℂ) : 0 ≤ cx t (Complex.exp s) ↔ 0 ≤ Real.sin (α t - s.im) := by
  have hpos : 0 < Real.exp s.re * ‖(t : ℂ)‖ / t.im :=
    div_pos (mul_pos (Real.exp_pos _) (norm_pos_iff.mpr (UpperHalfPlane.ne_zero t))) t.im_pos
  rw [cx_exp, show Real.exp s.re * (‖(t : ℂ)‖ * Real.sin (α t - s.im)) / t.im =
    Real.exp s.re * ‖(t : ℂ)‖ / t.im * Real.sin (α t - s.im) by ring]
  exact ⟨fun h ↦ nonneg_of_mul_nonneg_right h hpos |>.trans' le_rfl |> fun h' ↦ by
    by_contra hc; push Not at hc; nlinarith [mul_neg_of_pos_of_neg hpos hc],
    fun h ↦ mul_nonneg hpos.le h⟩

theorem cx_exp_nonpos_iff (s : ℂ) : cx t (Complex.exp s) ≤ 0 ↔ Real.sin (α t - s.im) ≤ 0 := by
  have hpos : 0 < Real.exp s.re * ‖(t : ℂ)‖ / t.im :=
    div_pos (mul_pos (Real.exp_pos _) (norm_pos_iff.mpr (UpperHalfPlane.ne_zero t))) t.im_pos
  rw [cx_exp, show Real.exp s.re * (‖(t : ℂ)‖ * Real.sin (α t - s.im)) / t.im =
    Real.exp s.re * ‖(t : ℂ)‖ / t.im * Real.sin (α t - s.im) by ring]
  constructor
  · intro h; by_contra hc; push Not at hc; nlinarith [mul_pos hpos hc]
  · intro h; exact mul_nonpos_of_nonneg_of_nonpos hpos.le h

theorem cy_exp_nonneg_iff (s : ℂ) : 0 ≤ cy t (Complex.exp s) ↔ 0 ≤ Real.sin s.im := by
  have hpos : 0 < Real.exp s.re / t.im := div_pos (Real.exp_pos _) t.im_pos
  rw [cy_exp, show Real.exp s.re * Real.sin s.im / t.im = Real.exp s.re / t.im * Real.sin s.im by
    ring]
  constructor
  · intro h; by_contra hc; push Not at hc; nlinarith [mul_neg_of_pos_of_neg hpos hc]
  · intro h; exact mul_nonneg hpos.le h

theorem cy_exp_nonpos_iff (s : ℂ) : cy t (Complex.exp s) ≤ 0 ↔ Real.sin s.im ≤ 0 := by
  have hpos : 0 < Real.exp s.re / t.im := div_pos (Real.exp_pos _) t.im_pos
  rw [cy_exp, show Real.exp s.re * Real.sin s.im / t.im = Real.exp s.re / t.im * Real.sin s.im by
    ring]
  constructor
  · intro h; by_contra hc; push Not at hc; nlinarith [mul_pos hpos hc]
  · intro h; exact mul_nonpos_of_nonneg_of_nonpos hpos.le h

theorem sin_nonneg' {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ π) : 0 ≤ Real.sin x :=
  Real.sin_nonneg_of_nonneg_of_le_pi h0 h1

theorem sin_nonpos' {x : ℝ} (h0 : x ≤ 0) (h1 : -π ≤ x) : Real.sin x ≤ 0 :=
  Real.sin_nonpos_of_nonpos_of_neg_pi_le h0 h1

theorem exp_mem_Q₁ {s : ℂ} (h0 : 0 ≤ s.im) (h1 : s.im ≤ α t) : Complex.exp s ∈ Q₁ t :=
  ⟨(cx_exp_nonneg_iff s).mpr (sin_nonneg' (by linarith) (by linarith [α_le_pi (t := t)])),
    (cy_exp_nonneg_iff s).mpr (sin_nonneg' h0 (by linarith [α_le_pi (t := t)]))⟩

theorem exp_mem_Q₂ {s : ℂ} (h0 : α t ≤ s.im) (h1 : s.im ≤ π) : Complex.exp s ∈ Q₂ t :=
  ⟨(cx_exp_nonpos_iff s).mpr (sin_nonpos' (by linarith) (by linarith [α_nonneg (t := t)])),
    (cy_exp_nonneg_iff s).mpr (sin_nonneg' (by linarith [α_nonneg (t := t)]) h1)⟩

theorem exp_mem_Q₃ {s : ℂ} (h0 : π ≤ s.im) (h1 : s.im ≤ π + α t) : Complex.exp s ∈ Q₃ t := by
  refine ⟨(cx_exp_nonpos_iff s).mpr (sin_nonpos' (by linarith [α_le_pi (t := t)])
    (by linarith)), (cy_exp_nonpos_iff s).mpr ?_⟩
  have : Real.sin s.im = -Real.sin (s.im - π) := by rw [Real.sin_sub_pi]; ring
  rw [this, neg_nonpos]
  exact sin_nonneg' (by linarith) (by linarith [α_le_pi (t := t)])

theorem exp_mem_Q₄ {s : ℂ} (h0 : π + α t ≤ s.im) (h1 : s.im ≤ 2 * π) : Complex.exp s ∈ Q₄ t := by
  refine ⟨(cx_exp_nonneg_iff s).mpr ?_, (cy_exp_nonpos_iff s).mpr ?_⟩
  · have : Real.sin (α t - s.im) = Real.sin (α t - s.im + 2 * π) := by
      rw [Real.sin_add_two_pi]
    rw [this]
    exact sin_nonneg' (by linarith [α_nonneg (t := t)]) (by linarith [α_le_pi (t := t)])
  · have : Real.sin s.im = -Real.sin (s.im - π) := by rw [Real.sin_sub_pi]; ring
    rw [this, neg_nonpos]
    exact sin_nonneg' (by linarith [α_nonneg (t := t)]) (by linarith)

theorem exp_sub_two_pi (s : ℂ) : Complex.exp (s - 2 * π * I) = Complex.exp s := by
  rw [Complex.exp_sub, Complex.exp_two_pi_mul_I, div_one]

theorem exp_mem_Q₁' {s : ℂ} (h0 : 2 * π ≤ s.im) (h1 : s.im ≤ 2 * π + α t) :
    Complex.exp s ∈ Q₁ t := by
  rw [← exp_sub_two_pi s]
  exact exp_mem_Q₁ (by simp; linarith) (by simp; linarith)

/-! ### The half-plane and its strips -/

/-- The half-plane `{Re s < log r₀}`, mapped onto `D*` by `exp`. -/
def Hr (t : ℍ) : Set ℂ := {s | s.re < Real.log (r₀ t)}

/-- A strip of the half-plane. -/
def strip (t : ℍ) (θ₁ θ₂ : ℝ) : Set ℂ := {s | s.re < Real.log (r₀ t) ∧ θ₁ ≤ s.im ∧ s.im ≤ θ₂}

theorem isOpen_Hr : IsOpen (Hr t) := isOpen_lt continuous_re continuous_const

theorem convex_Hr : Convex ℝ (Hr t) := convex_halfSpace_re_lt _

theorem convex_strip (θ₁ θ₂ : ℝ) : Convex ℝ (strip t θ₁ θ₂) :=
  (convex_halfSpace_re_lt _).inter ((convex_halfSpace_im_ge _).inter (convex_halfSpace_im_le _))

theorem strip_subset {θ₁ θ₂ : ℝ} : strip t θ₁ θ₂ ⊆ Hr t := fun _ h ↦ h.1

theorem exp_mem_Dst {s : ℂ} (hs : s ∈ Hr t) : Complex.exp s ∈ Dst t := by
  refine ⟨?_, Complex.exp_ne_zero s⟩
  rw [mem_ball_zero_iff, Complex.norm_exp]
  calc Real.exp s.re < Real.exp (Real.log (r₀ t)) := Real.exp_lt_exp.mpr hs
    _ = r₀ t := Real.exp_log r₀_pos

theorem exp_mem_Ω {s : ℂ} (hs : s ∈ Hr t) : Complex.exp s ∈ ((Lt t).lattice : Set ℂ)ᶜ :=
  Dst_notMem (exp_mem_Dst hs)

/-- A point of `Hr` with prescribed imaginary part. -/
noncomputable def pt (t : ℍ) (θ : ℝ) : ℂ := (Real.log (r₀ t) - 1 : ℝ) + θ * I

theorem pt_re (θ : ℝ) : (pt t θ).re = Real.log (r₀ t) - 1 := by simp [pt]
theorem pt_im (θ : ℝ) : (pt t θ).im = θ := by simp [pt]

theorem pt_mem_strip {θ θ₁ θ₂ : ℝ} (h1 : θ₁ ≤ θ) (h2 : θ ≤ θ₂) : pt t θ ∈ strip t θ₁ θ₂ :=
  ⟨by rw [pt_re]; linarith, by rw [pt_im]; exact h1, by rw [pt_im]; exact h2⟩

/-! ### The lift of the exponential -/

theorem exists_Sig : ∃ Sig : ℂ → ℍ, ContinuousOn Sig (Hr t) ∧
    (∀ s ∈ Hr t, U.ψ (Sig s) = Complex.exp s) ∧
    Sig (pt t (α t / 2)) = σ₁ U (Complex.exp (pt t (α t / 2))) := by
  have hmem : pt t (α t / 2) ∈ strip t 0 (α t) :=
    pt_mem_strip (by linarith [α_nonneg (t := t)]) (by linarith [α_nonneg (t := t)])
  exact U.covering.exists_lift_of_convex convex_Hr Complex.continuous_exp.continuousOn
    (fun s hs ↦ exp_mem_Ω hs) (strip_subset hmem)
    (ψ_σ₁ U (exp_mem_Dst (strip_subset hmem))
      (exp_mem_Q₁ (by rw [pt_im]; linarith [α_nonneg (t := t)])
        (by rw [pt_im]; linarith [α_nonneg (t := t)])))

/-- The lift `Sig` of `exp : Hr → D*` through `ψ`. -/
noncomputable def Sig : ℂ → ℍ := (exists_Sig U).choose

theorem continuousOn_Sig : ContinuousOn (Sig U) (Hr t) := (exists_Sig U).choose_spec.1

theorem ψ_Sig {s : ℂ} (hs : s ∈ Hr t) : U.ψ (Sig U s) = Complex.exp s :=
  (exists_Sig U).choose_spec.2.1 s hs

theorem Sig_base : Sig U (pt t (α t / 2)) = σ₁ U (Complex.exp (pt t (α t / 2))) :=
  (exists_Sig U).choose_spec.2.2

/-- Uniqueness of lifts of `exp` over a strip. -/
theorem Sig_eqOn {θ₁ θ₂ : ℝ} {σ : ℂ → ℍ} (hσ : ContinuousOn σ (strip t θ₁ θ₂))
    (hψ : ∀ s ∈ strip t θ₁ θ₂, U.ψ (σ s) = Complex.exp s) {s₀ : ℂ} (hs₀ : s₀ ∈ strip t θ₁ θ₂)
    (h₀ : Sig U s₀ = σ s₀) : EqOn (Sig U) σ (strip t θ₁ θ₂) :=
  U.covering.eqOn_of_lift (convex_strip θ₁ θ₂).isPreconnected
    ((continuousOn_Sig U).mono strip_subset) hσ
    (fun s hs ↦ by
      change U.ψ (Sig U s) ∈ _; rw [ψ_Sig U (strip_subset hs)]; exact exp_mem_Ω (strip_subset hs))
    (fun s hs ↦ by
      change U.ψ (Sig U s) = U.ψ (σ s); rw [ψ_Sig U (strip_subset hs), hψ s hs]) hs₀ h₀

theorem Sig_eq₁ : EqOn (Sig U) (σ₁ U ∘ Complex.exp) (strip t 0 (α t)) := by
  refine Sig_eqOn U ((continuousOn_σ₁ U).comp Complex.continuous_exp.continuousOn fun s hs ↦
    ⟨exp_mem_Dst (strip_subset hs), exp_mem_Q₁ hs.2.1 hs.2.2⟩) (fun s hs ↦
    ψ_σ₁ U (exp_mem_Dst (strip_subset hs)) (exp_mem_Q₁ hs.2.1 hs.2.2))
    (pt_mem_strip (by linarith [α_nonneg (t := t)]) (by linarith [α_nonneg (t := t)]))
    (Sig_base U)

theorem Sig_eq₂ : EqOn (Sig U) (σ₂ U ∘ Complex.exp) (strip t (α t) π) := by
  have hs : pt t (α t) ∈ strip t 0 (α t) := pt_mem_strip (α_nonneg) le_rfl
  have hs' : pt t (α t) ∈ strip t (α t) π := pt_mem_strip le_rfl α_le_pi
  have hz := exp_mem_Dst (t := t) (strip_subset hs)
  have hq₁ := exp_mem_Q₁ (t := t) hs.2.1 hs.2.2
  have hq₂ := exp_mem_Q₂ (t := t) hs'.2.1 hs'.2.2
  refine Sig_eqOn U ((continuousOn_σ₂ U).comp Complex.continuous_exp.continuousOn fun s hs ↦
    ⟨exp_mem_Dst (strip_subset hs), exp_mem_Q₂ hs.2.1 hs.2.2⟩) (fun s hs ↦
    ψ_σ₂ U (exp_mem_Dst (strip_subset hs)) (exp_mem_Q₂ hs.2.1 hs.2.2)) hs' ?_
  rw [Sig_eq₁ U hs, Function.comp_apply, Function.comp_apply,
    seam₁₂ U hz (le_antisymm hq₂.1 hq₁.1) hq₁.2]

theorem Sig_eq₃ : EqOn (Sig U) (σ₃ U ∘ Complex.exp) (strip t π (π + α t)) := by
  have hs : pt t π ∈ strip t (α t) π := pt_mem_strip α_le_pi le_rfl
  have hs' : pt t π ∈ strip t π (π + α t) := pt_mem_strip le_rfl (by linarith [α_nonneg (t := t)])
  have hz := exp_mem_Dst (t := t) (strip_subset hs)
  have hq₂ := exp_mem_Q₂ (t := t) hs.2.1 hs.2.2
  have hq₃ := exp_mem_Q₃ (t := t) hs'.2.1 hs'.2.2
  refine Sig_eqOn U ((continuousOn_σ₃ U).comp Complex.continuous_exp.continuousOn fun s hs ↦
    ⟨exp_mem_Dst (strip_subset hs), exp_mem_Q₃ hs.2.1 hs.2.2⟩) (fun s hs ↦
    ψ_σ₃ U (exp_mem_Dst (strip_subset hs)) (exp_mem_Q₃ hs.2.1 hs.2.2)) hs' ?_
  rw [Sig_eq₂ U hs, Function.comp_apply, Function.comp_apply,
    seam₂₃ U hz hq₂.1 (le_antisymm hq₃.2 hq₂.2)]

theorem Sig_eq₄ : EqOn (Sig U) (σ₄ U ∘ Complex.exp) (strip t (π + α t) (2 * π)) := by
  have hs : pt t (π + α t) ∈ strip t π (π + α t) :=
    pt_mem_strip (by linarith [α_nonneg (t := t)]) le_rfl
  have hs' : pt t (π + α t) ∈ strip t (π + α t) (2 * π) :=
    pt_mem_strip le_rfl (by linarith [α_le_pi (t := t)])
  have hz := exp_mem_Dst (t := t) (strip_subset hs)
  have hq₃ := exp_mem_Q₃ (t := t) hs.2.1 hs.2.2
  have hq₄ := exp_mem_Q₄ (t := t) hs'.2.1 hs'.2.2
  refine Sig_eqOn U ((continuousOn_σ₄ U).comp Complex.continuous_exp.continuousOn fun s hs ↦
    ⟨exp_mem_Dst (strip_subset hs), exp_mem_Q₄ hs.2.1 hs.2.2⟩) (fun s hs ↦
    ψ_σ₄ U (exp_mem_Dst (strip_subset hs)) (exp_mem_Q₄ hs.2.1 hs.2.2)) hs' ?_
  rw [Sig_eq₃ U hs, Function.comp_apply, Function.comp_apply,
    seam₃₄ U hz (le_antisymm hq₃.1 hq₄.1) hq₃.2]

theorem Sig_eq₅ :
    EqOn (Sig U) (fun s ↦ Cm U • σ₁ U (Complex.exp s)) (strip t (2 * π) (2 * π + α t)) := by
  have hs : pt t (2 * π) ∈ strip t (π + α t) (2 * π) :=
    pt_mem_strip (by linarith [α_le_pi (t := t)]) le_rfl
  have hs' : pt t (2 * π) ∈ strip t (2 * π) (2 * π + α t) :=
    pt_mem_strip le_rfl (by linarith [α_nonneg (t := t)])
  have hz := exp_mem_Dst (t := t) (strip_subset hs)
  have hq₄ := exp_mem_Q₄ (t := t) hs.2.1 hs.2.2
  have hq₁ := exp_mem_Q₁' (t := t) hs'.2.1 hs'.2.2
  refine Sig_eqOn U ((continuous_const_smul _).comp_continuousOn
    ((continuousOn_σ₁ U).comp Complex.continuous_exp.continuousOn fun s hs ↦
    ⟨exp_mem_Dst (strip_subset hs), exp_mem_Q₁' hs.2.1 hs.2.2⟩)) (fun s hs ↦ by
      rw [ψ_Cm_smul, ψ_σ₁ U (exp_mem_Dst (strip_subset hs)) (exp_mem_Q₁' hs.2.1 hs.2.2)])
    hs' ?_
  rw [Sig_eq₄ U hs, Function.comp_apply, seam₄₁ U hz hq₁.1 (le_antisymm hq₄.2 hq₁.2)]

theorem add_two_pi_mem_Hr {s : ℂ} (hs : s ∈ Hr t) : s + 2 * π * I ∈ Hr t := by
  simpa [Hr] using hs

/-- **The monodromy relation** `Sig (s + 2π i) = C • Sig s`. -/
theorem Sig_add_two_pi {s : ℂ} (hs : s ∈ Hr t) : Sig U (s + 2 * π * I) = Cm U • Sig U s := by
  have hcont₁ : ContinuousOn (fun s ↦ Sig U (s + 2 * π * I)) (Hr t) :=
    (continuousOn_Sig U).comp (continuous_add_const _).continuousOn fun s hs ↦ add_two_pi_mem_Hr hs
  have hcont₂ : ContinuousOn (fun s ↦ Cm U • Sig U s) (Hr t) :=
    (continuous_const_smul _).comp_continuousOn (continuousOn_Sig U)
  set s₀ := pt t (α t / 2)
  have hs₀ : s₀ ∈ strip t 0 (α t) :=
    pt_mem_strip (by linarith [α_nonneg (t := t)]) (by linarith [α_nonneg (t := t)])
  have hs₀' : s₀ + 2 * π * I ∈ strip t (2 * π) (2 * π + α t) := by
    refine ⟨by simpa using hs₀.1, ?_, ?_⟩ <;> simp [s₀, pt_im] <;> linarith [α_nonneg (t := t)]
  have h₀ : Sig U (s₀ + 2 * π * I) = Cm U • Sig U s₀ := by
    rw [Sig_eq₅ U hs₀', Sig_eq₁ U hs₀, Function.comp_apply]
    simp only
    rw [← exp_sub_two_pi (s₀ + 2 * π * I), add_sub_cancel_right]
  have := U.covering.eqOn_of_lift convex_Hr.isPreconnected hcont₁ hcont₂
    (fun s hs ↦ by
      change U.ψ (Sig U (s + 2 * π * I)) ∈ _
      rw [ψ_Sig U (add_two_pi_mem_Hr hs)]; exact exp_mem_Ω (add_two_pi_mem_Hr hs))
    (fun s hs ↦ by
      change U.ψ (Sig U (s + 2 * π * I)) = U.ψ (Cm U • Sig U s)
      rw [ψ_Sig U (add_two_pi_mem_Hr hs), ψ_Cm_smul, ψ_Sig U hs, ← exp_sub_two_pi (s + _),
        add_sub_cancel_right])
    (strip_subset hs₀) h₀
  exact this hs

/-- `Sig` is holomorphic. -/
theorem differentiableOn_Sig : DifferentiableOn ℂ (fun s ↦ (Sig U s : ℂ)) (Hr t) := by
  intro s hs
  have him := (Sig U s).im_pos
  refine (differentiableAt_of_comp_eq (f := U.Ψ) (g := Complex.exp)
    (U.hasStrictDerivAt_Ψ him) (U.deriv_ne_zero _ him)
    ((continuous_coe.comp_continuousOn (continuousOn_Sig U)).continuousAt
      (isOpen_Hr.mem_nhds hs)) ?_ Complex.differentiableAt_exp).differentiableWithinAt
  filter_upwards [isOpen_Hr.mem_nhds hs] with v hv
  exact ψ_Sig U hv

end Peripheral

end Uniformization
