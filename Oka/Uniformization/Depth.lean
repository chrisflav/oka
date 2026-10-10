/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Heights.WeierstrassPrincipalPart
import Oka.Uniformization.Cusp

/-!
# Depth in the cusp and the growth of `℘ ∘ ψ`

Let `ψ : ℍ → ℂ ∖ Λ` be the uniformisation with deck group `Γ`, `τ₀ = e₀` the base point over the
centre `c₀` of the fundamental parallelogram, and

`D(τ) = infDist τ₀ (Γ • τ)`

the hyperbolic distance from `τ₀` to the orbit of `τ` (its *depth*). This file proves:

* `Peripheral.depth_smul_le`: for `δ` in the commensurator of `Γ`, `D (δ τ) ≤ D τ + c_δ`.
* `Peripheral.exists_growth`: two-sided comparison between the depth and the size of `℘ ∘ ψ`:
  `log (1 + |℘ (ψ τ)|) ≤ α e^{D τ} + β` and `e^{D τ} ≤ α log (2 + |℘ (ψ τ)|) + β`.

Both come from the cusp normal form (`Peripheral.exists_cusp_normalForm`): near a lattice point
`w`, the orbit of `τ` contains `Σ (log w)`, whose height in the cusp coordinate is
`(κ / 2π) (log (1/|w|) + O(1))`, while the whole orbit of `τ₀` stays below a fixed height `h`
(`Peripheral.im_le_of_orbit_base`), and `|℘ w| ≍ |w|⁻²`.
-/

open Complex Metric Set Filter Topology
open UpperHalfPlane hiding I I_re I_im
open scoped MatrixGroups Real Pointwise

namespace Uniformization

namespace Peripheral

open Generators

variable {t : ℍ} (U : Unif (Lt t))

/-- The data of the cusp normal form. -/
structure CuspData where
  /-- The matrix conjugating the parabolic generator `Cm U` to a translation. -/
  M : SL(2, ℝ)
  /-- The translation length of the conjugated parabolic generator. -/
  κ : ℝ
  κ_pos : 0 < κ
  conj : ∀ z : ℍ, (((M⁻¹ * Cm U * M) • z : ℍ) : ℂ) = z + κ
  /-- The radius of the punctured disc on which the normal form holds. -/
  r₁ : ℝ
  r₁_pos : 0 < r₁
  r₁_le : r₁ ≤ r₀ t
  /-- The holomorphic correction term of the normal form. -/
  φ : ℂ → ℂ
  /-- A bound for `φ` on the disc of radius `r₁`. -/
  Φ : ℝ
  φ_le : ∀ w ∈ ball (0 : ℂ) r₁, ‖φ w‖ ≤ Φ
  normal : ∀ s : ℂ, s.re < Real.log r₁ → τ' U M s = (κ / (2 * π * I)) * (s + φ (Complex.exp s))
  /-- The local coordinate at the cusp. -/
  G : ℂ → ℂ
  G_diff : DifferentiableOn ℂ G (ball 0 r₁)
  G_zero : G 0 = 0
  G_deriv : deriv G 0 ≠ 0
  G_exp : ∀ s : ℂ, s.re < Real.log r₁ →
    Complex.exp (2 * π * I * τ' U M s / κ) = G (Complex.exp s)

/-- A choice of cusp data. -/
noncomputable def cuspData : CuspData U := by
  choose M κ hκ hM r₁ hr₁ hr₁₀ φ Φ hΦ hnf G hG using exists_cusp_normalForm U
  exact ⟨M, κ, hκ, hM, r₁, hr₁, hr₁₀, φ, Φ, hΦ, hnf, G, hG.1, hG.2.1, hG.2.2.1, hG.2.2.2⟩

variable {U}

theorem log_mem_ball (c : CuspData U) {w : ℂ} (hw : w ∈ ball (0 : ℂ) c.r₁) (hw0 : w ≠ 0) :
    (Complex.log w).re < Real.log c.r₁ := by
  rw [Complex.log_re]
  exact Real.log_lt_log (norm_pos_iff.mpr hw0) (mem_ball_zero_iff.mp hw)

theorem mem_Dst_of_ball (c : CuspData U) {w : ℂ} (hw : w ∈ ball (0 : ℂ) c.r₁) (hw0 : w ≠ 0) :
    w ∈ Dst t := ⟨ball_subset_ball c.r₁_le hw, hw0⟩

/-- **The horoball lemma**: points high up in the cusp coordinate lie in the `Σ`-region. -/
theorem exists_height (c : CuspData U) : ∃ h : ℝ, ∀ ν : ℍ, h < (c.M⁻¹ • ν).im →
    ∃ w ∈ ball (0 : ℂ) c.r₁, w ≠ 0 ∧ ∃ k : ℤ, ν = (Cm U) ^ k • Sig U (Complex.log w) := by
  have hGs : HasStrictDerivAt c.G (deriv c.G 0) 0 :=
    (c.G_diff.analyticAt (ball_mem_nhds 0 c.r₁_pos)).hasStrictDerivAt
  have hmap := hGs.map_nhds_eq c.G_deriv
  rw [c.G_zero] at hmap
  have himg : c.G '' ball 0 c.r₁ ∈ 𝓝 (0 : ℂ) := by
    rw [← hmap]; exact image_mem_map (ball_mem_nhds 0 c.r₁_pos)
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp himg
  refine ⟨(c.κ / (2 * π)) * Real.log (1 / ε), fun ν hν ↦ ?_⟩
  set ν' := c.M⁻¹ • ν
  set q := Complex.exp (2 * π * I * (ν' : ℂ) / c.κ)
  have hκ' : (c.κ : ℂ) ≠ 0 := by exact_mod_cast c.κ_pos.ne'
  have hq : q ∈ ball (0 : ℂ) ε := by
    rw [mem_ball_zero_iff, Complex.norm_exp]
    have hre : (2 * π * I * (ν' : ℂ) / c.κ).re = -(2 * π / c.κ) * ν'.im := by
      rw [show (2 * π * I * (ν' : ℂ) / c.κ) = (2 * π / c.κ : ℝ) * I * ν' by push_cast; ring]
      simp
    rw [hre]
    have h1 : Real.log (1 / ε) < (2 * π / c.κ) * ν'.im := by
      have := hν
      rw [show (c.κ / (2 * π)) * Real.log (1 / ε) = Real.log (1 / ε) / (2 * π / c.κ) by
        field_simp] at this
      rwa [div_lt_iff₀' (by have := c.κ_pos; positivity)] at this
    calc Real.exp (-(2 * π / c.κ) * ν'.im) < Real.exp (-Real.log (1 / ε)) :=
          Real.exp_lt_exp.mpr (by linarith)
      _ = ε := by rw [Real.exp_neg, Real.exp_log (by positivity)]; simp
  obtain ⟨w, hw, hGw⟩ := hεsub hq
  have hw0 : w ≠ 0 := by
    rintro rfl
    rw [c.G_zero] at hGw
    exact Complex.exp_ne_zero _ hGw.symm
  refine ⟨w, hw, hw0, ?_⟩
  set s := Complex.log w
  have hs := log_mem_ball c hw hw0
  have h1 := c.G_exp s hs
  rw [Complex.exp_log hw0, hGw] at h1
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp h1
  have h2πI : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  have hτ : τ' U c.M s = ν' + n * c.κ := by
    field_simp at hn; linear_combination hn
  refine ⟨-n, ?_⟩
  have h2 : c.M⁻¹ • Sig U s = (c.M⁻¹ * Cm U * c.M) ^ n • ν' :=
    UpperHalfPlane.ext (by rw [translation_zpow U c.conj]; exact hτ)
  have h3 := congrArg (fun z ↦ c.M • z) h2
  simp only [smul_inv_smul] at h3
  rw [show ν' = c.M⁻¹ • ν from rfl, conj_zpow_smul] at h3
  rw [h3, ← mul_smul, zpow_neg, inv_mul_cancel, one_smul]

/-! ### The orbit of the base point stays below a fixed height -/

theorem cx_c₀_add_lattice {l : ℂ} (hl : l ∈ (Lt t).lattice) :
    ∃ n : ℤ, cx t (c₀ t + l) = 1 / 2 + n := by
  obtain ⟨m, n, -, hn⟩ := (mem_lattice_iff t l).mp hl
  exact ⟨n, by rw [cx_add, cx_c₀, hn]⟩

/-- The orbit of `e₀` stays below a fixed height in the cusp coordinate. -/
theorem exists_orbit_height (c : CuspData U) :
    ∃ h : ℝ, ∀ γ ∈ U.deckGroup, (c.M⁻¹ • (γ • e₀ U)).im ≤ h := by
  obtain ⟨h, hh⟩ := exists_height c
  refine ⟨h, fun γ hγ ↦ ?_⟩
  by_contra hlt
  push Not at hlt
  obtain ⟨w, hw, hw0, k, hk⟩ := hh _ hlt
  have hψ : U.ψ (γ • e₀ U) = w := by
    rw [hk, ψ_Cm_zpow_smul, ψ_Sig U (log_mem_Hr (mem_Dst_of_ball c hw hw0)),
      Complex.exp_log hw0]
  obtain ⟨l, hl, hγψ⟩ := hγ
  rw [hγψ, ψ_e₀] at hψ
  obtain ⟨n, hn⟩ := cx_c₀_add_lattice hl
  have hbox := (box (ball_subset_ball c.r₁_le (hψ ▸ hw))).1
  rw [hn, abs_lt] at hbox
  have h1 : (n : ℝ) < 0 := by linarith [hbox.2]
  have h2 : (-1 : ℝ) < n := by linarith [hbox.1]
  have : n < 0 := by exact_mod_cast h1
  have : -1 < n := by exact_mod_cast h2
  omega

/-! ### Depth -/

variable (U) in
/-- The `Γ`-orbit of `τ`. -/
def orbit (τ : ℍ) : Set ℍ := {ν | ∃ γ ∈ U.deckGroup, ν = γ • τ}

variable (U) in
/-- The **depth** of `τ`: the distance from the base point `e₀` to the orbit of `τ`. -/
noncomputable def depth (τ : ℍ) : ℝ := infDist (e₀ U) (orbit U τ)

theorem orbit_nonempty (τ : ℍ) : (orbit U τ).Nonempty := ⟨τ, 1, one_mem _, by rw [one_smul]⟩

theorem depth_nonneg (τ : ℍ) : 0 ≤ depth U τ := infDist_nonneg

theorem depth_le {τ : ℍ} {γ : SL(2, ℝ)} (hγ : γ ∈ U.deckGroup) :
    depth U τ ≤ dist (γ • τ) (e₀ U) := by
  rw [dist_comm]; exact infDist_le_dist_of_mem ⟨γ, hγ, rfl⟩

theorem le_depth {τ : ℍ} {r : ℝ} (h : ∀ γ ∈ U.deckGroup, r ≤ dist (γ • τ) (e₀ U)) :
    r ≤ depth U τ := by
  refine (le_infDist (orbit_nonempty τ)).mpr ?_
  rintro _ ⟨γ, hγ, rfl⟩
  rw [dist_comm]; exact h γ hγ

theorem orbit_smul {τ : ℍ} {γ : SL(2, ℝ)} (hγ : γ ∈ U.deckGroup) :
    orbit U (γ • τ) = orbit U τ := by
  ext ν
  constructor
  · rintro ⟨η, hη, rfl⟩; exact ⟨η * γ, mul_mem hη hγ, (mul_smul _ _ _).symm⟩
  · rintro ⟨η, hη, rfl⟩
    exact ⟨η * γ⁻¹, mul_mem hη (inv_mem hγ), by rw [mul_smul, inv_smul_smul]⟩

theorem depth_smul {τ : ℍ} {γ : SL(2, ℝ)} (hγ : γ ∈ U.deckGroup) :
    depth U (γ • τ) = depth U τ := by
  rw [depth, depth, orbit_smul hγ]

/-- Finitely many coset representatives. -/
theorem exists_finset_reps {G : Type*} [Group G] {Γ Δ : Subgroup G} (h : Δ.relIndex Γ ≠ 0) :
    ∃ R : Finset G, (∀ g ∈ R, g ∈ Γ) ∧ ∀ γ ∈ Γ, ∃ g ∈ R, g⁻¹ * γ ∈ Δ := by
  haveI : (Δ.subgroupOf Γ).FiniteIndex := ⟨h⟩
  haveI : Finite (Γ ⧸ Δ.subgroupOf Γ) := Subgroup.finite_quotient_of_finiteIndex
  haveI := Fintype.ofFinite (Γ ⧸ Δ.subgroupOf Γ)
  classical
  refine ⟨Finset.univ.image fun q : Γ ⧸ Δ.subgroupOf Γ ↦ ((q.out : Γ) : G), ?_, ?_⟩
  · intro g hg
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hg
    exact (q.out).2
  · intro γ hγ
    refine ⟨(((QuotientGroup.mk ⟨γ, hγ⟩ : Γ ⧸ Δ.subgroupOf Γ).out : Γ) : G),
      Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩, ?_⟩
    obtain ⟨h', hh'⟩ := QuotientGroup.mk_out_eq_mul (Δ.subgroupOf Γ) ⟨γ, hγ⟩
    rw [hh']
    have : ((⟨γ, hγ⟩ * (h' : Γ) : Γ) : G) = γ * ((h' : Γ) : G) := rfl
    rw [this, mul_inv_rev, inv_mul_cancel_right]
    exact inv_mem (Subgroup.mem_subgroupOf.mp h'.2)

/-- Elements of the commensurator: `{h ∈ Γ | δ h δ⁻¹ ∈ Γ}` has finite index in `Γ`. -/
theorem relIndex_ne_zero_of_mem_commensurator {G : Type*} [Group G] {Γ : Subgroup G} {δ : G}
    (hδ : δ ∈ Subgroup.Commensurable.commensurator Γ) :
    (Γ ⊓ Γ.comap (MulAut.conj δ).toMonoidHom).relIndex Γ ≠ 0 := by
  have hδ' : δ⁻¹ ∈ Subgroup.Commensurable.commensurator Γ := inv_mem hδ
  rw [Subgroup.Commensurable.commensurator_mem_iff] at hδ'
  have h := hδ'.1
  have heq : (ConjAct.toConjAct δ⁻¹ • Γ : Subgroup G) ⊓ Γ =
      Γ ⊓ Γ.comap (MulAut.conj δ).toMonoidHom := by
    ext x
    simp only [Subgroup.mem_inf, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      Subgroup.mem_pointwise_smul_iff_inv_smul_mem, map_inv, inv_inv, ConjAct.smul_def,
      ConjAct.ofConjAct_toConjAct]
    tauto
  rw [Subgroup.relIndex, ← Subgroup.inf_subgroupOf_right, heq] at h
  rw [Subgroup.relIndex, ← Subgroup.inf_subgroupOf_right, inf_assoc,
    inf_comm (Subgroup.comap _ Γ) Γ, ← inf_assoc, inf_idem]
  exact h

/-- **Depth under the commensurator**: `D (δ τ) ≤ D τ + c_δ`. -/
theorem exists_depth_smul_le {δ : SL(2, ℝ)}
    (hδ : δ ∈ Subgroup.Commensurable.commensurator U.deckGroup) :
    ∃ c : ℝ, ∀ τ : ℍ, depth U (δ • τ) ≤ depth U τ + c := by
  set Γ := U.deckGroup
  obtain ⟨R, hRΓ, hR⟩ := exists_finset_reps (relIndex_ne_zero_of_mem_commensurator hδ)
  set c₂ := ∑ g ∈ R, dist (e₀ U) (g • e₀ U)
  refine ⟨c₂ + dist (e₀ U) (δ⁻¹ • e₀ U), fun τ ↦ ?_⟩
  have key : ∀ γ ∈ Γ, depth U (δ • τ) - (c₂ + dist (e₀ U) (δ⁻¹ • e₀ U)) ≤
      dist (γ • τ) (e₀ U) := by
    intro γ hγ
    obtain ⟨g, hgR, hgΔ⟩ := hR γ hγ
    set h := g⁻¹ * γ
    have hhΓ : h ∈ Γ := hgΔ.1
    have hδh : δ * h * δ⁻¹ ∈ Γ := hgΔ.2
    have h1 : depth U (δ • τ) ≤ dist (h • τ) (e₀ U) + dist (e₀ U) (δ⁻¹ • e₀ U) := by
      calc depth U (δ • τ) ≤ dist ((δ * h * δ⁻¹) • δ • τ) (e₀ U) := depth_le hδh
        _ = dist (h • τ) (δ⁻¹ • e₀ U) := by
          rw [← mul_smul, show δ * h * δ⁻¹ * δ = δ * h by group, mul_smul,
            ← dist_smul δ⁻¹, inv_smul_smul]
        _ ≤ _ := dist_triangle _ _ _
    have h2 : dist (h • τ) (e₀ U) ≤ dist (γ • τ) (e₀ U) + c₂ := by
      calc dist (h • τ) (e₀ U) = dist (γ • τ) (g • e₀ U) := by
            rw [← dist_smul g, ← mul_smul, show g * h = γ by simp [h]]
        _ ≤ dist (γ • τ) (e₀ U) + dist (e₀ U) (g • e₀ U) := dist_triangle _ _ _
        _ ≤ dist (γ • τ) (e₀ U) + c₂ := by
          gcongr
          exact Finset.single_le_sum (f := fun g ↦ dist (e₀ U) (g • e₀ U))
            (fun _ _ ↦ dist_nonneg) hgR
    linarith
  have := le_depth (τ := τ) key
  linarith

/-! ### The compact part and the cusp part of the fundamental domain -/

variable (t) in
/-- The fundamental parallelogram minus `ε`-discs about its corners. -/
def Kε (ε : ℝ) : Set ℂ :=
  {k | 0 ≤ cx t k ∧ cx t k ≤ 1 ∧ 0 ≤ cy t k ∧ cy t k ≤ 1 ∧
    ε ≤ dist k 0 ∧ ε ≤ dist k 1 ∧ ε ≤ dist k t ∧ ε ≤ dist k (1 + t)}

theorem isCompact_Kε (ε : ℝ) : IsCompact (Kε t ε) := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · simp only [Kε, setOf_and]
    refine ((isClosed_le continuous_const (continuous_cx t)).inter
      ((isClosed_le (continuous_cx t) continuous_const).inter
      ((isClosed_le continuous_const (continuous_cy t)).inter
      ((isClosed_le (continuous_cy t) continuous_const).inter ?_))))
    exact (isClosed_le continuous_const (continuous_id.dist continuous_const)).inter
      ((isClosed_le continuous_const (continuous_id.dist continuous_const)).inter
      ((isClosed_le continuous_const (continuous_id.dist continuous_const)).inter
      (isClosed_le continuous_const (continuous_id.dist continuous_const))))
  · refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 1 + ‖(t : ℂ)‖)).subset ?_
    rintro k ⟨h1, h2, h3, h4, -⟩
    rw [mem_closedBall_zero_iff, eq_cx_cy t k]
    calc ‖(cx t k : ℂ) + cy t k * t‖ ≤ ‖(cx t k : ℂ)‖ + ‖(cy t k : ℂ) * t‖ := norm_add_le _ _
      _ ≤ 1 + ‖(t : ℂ)‖ := by
        rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg h1,
          Real.norm_of_nonneg h3]
        gcongr
        nlinarith [norm_nonneg (t : ℂ)]

theorem Kε_subset {ε : ℝ} (hε : 0 < ε) : Kε t ε ⊆ K t := by
  rintro k ⟨h1, h2, h3, h4, d0, d1, dt, d1t⟩
  rcases h3.lt_or_eq with h3 | h3
  · rcases h4.lt_or_eq with h4 | h4
    · exact Or.inl ⟨h1, h2, h3, h4⟩
    · refine Or.inr ⟨?_, ?_, h3.le, h4.le⟩
      · rcases h1.lt_or_eq with h1 | h1
        · exact h1
        · exfalso
          have : k = t := ext_cx_cy t (by rw [← h1, cx_t]) (by rw [h4, cy_t])
          rw [this, dist_self] at dt; linarith
      · rcases h2.lt_or_eq with h2 | h2
        · exact h2
        · exfalso
          have : k = 1 + t := ext_cx_cy t (by rw [h2, cx_add, cx_one, cx_t]; ring)
            (by rw [h4, cy_add, cy_one, cy_t]; ring)
          rw [this, dist_self] at d1t; linarith
  · refine Or.inr ⟨?_, ?_, h3.le, by rw [← h3]; norm_num⟩
    · rcases h1.lt_or_eq with h1 | h1
      · exact h1
      · exfalso
        have : k = 0 := ext_cx_cy t (by rw [← h1]; simp [cx, cy]) (by rw [← h3]; simp [cy])
        rw [this, dist_self] at d0; linarith
    · rcases h2.lt_or_eq with h2 | h2
      · exact h2
      · exfalso
        have : k = 1 := ext_cx_cy t (by rw [h2, cx_one]) (by rw [← h3, cy_one])
        rw [this, dist_self] at d1; linarith

theorem corner_mem_lattice : (0 : ℂ) ∈ (Lt t).lattice ∧ (1 : ℂ) ∈ (Lt t).lattice ∧
    (t : ℂ) ∈ (Lt t).lattice ∧ (1 + t : ℂ) ∈ (Lt t).lattice :=
  ⟨zero_mem _, one_mem t, t_mem t, add_mem (one_mem t) (t_mem t)⟩

/-- **Decomposition of `ℍ`.** Up to `Γ`, every point is over the compact part `Kε` or is
`Σ (log w)` with `0 < |w| < ε`. -/
theorem compact_or_cusp {ε : ℝ} (hεr : ε ≤ r₀ t) (τ : ℍ) :
    (∃ γ ∈ U.deckGroup, ∃ k ∈ Kε t ε, γ • τ = sK U k) ∨
      ∃ γ ∈ U.deckGroup, ∃ w ∈ ball (0 : ℂ) ε, w ≠ 0 ∧ γ • τ = Sig U (Complex.log w) := by
  obtain ⟨g, hg, k, hk, rfl⟩ := exists_tile U τ
  have hgi := inv_mem hg
  by_cases hkε : k ∈ Kε t ε
  · exact Or.inl ⟨g⁻¹, hgi, k, hkε, by rw [inv_smul_smul]⟩
  · right
    obtain ⟨b1, b2, b3, b4⟩ := K_bounds hk
    have : ∃ c ∈ (Lt t).lattice, dist k c < ε := by
      simp only [Kε, mem_setOf_eq, not_and, not_le] at hkε
      by_cases h0 : ε ≤ dist k 0
      · by_cases h1 : ε ≤ dist k 1
        · by_cases h2 : ε ≤ dist k t
          · exact ⟨_, corner_mem_lattice.2.2.2, hkε b1 b2 b3 b4 h0 h1 h2⟩
          · exact ⟨_, corner_mem_lattice.2.2.1, not_le.mp h2⟩
        · exact ⟨_, corner_mem_lattice.2.1, not_le.mp h1⟩
      · exact ⟨_, corner_mem_lattice.1, not_le.mp h0⟩
    obtain ⟨c, hc, hkc⟩ := this
    set w := k - c
    have hw0 : w ≠ 0 := fun h ↦ K_notMem_lattice t hk (by rw [sub_eq_zero.mp h]; exact hc)
    have hwε : w ∈ ball (0 : ℂ) ε := by rwa [mem_ball_zero_iff, ← dist_eq_norm]
    have hwD : w ∈ Dst t := ⟨ball_subset_ball hεr hwε, hw0⟩
    obtain ⟨γ, hγ, hγτ⟩ := U.exists_mem_deckGroup (τ := g • sK U k)
      (τ' := Sig U (Complex.log w)) (by
        rw [ψ_Sig U (log_mem_Hr hwD), Complex.exp_log hw0]
        obtain ⟨l, hl, hgl⟩ := hg
        rw [hgl, ψ_sK U hk]
        have : w - (k + l) = -(c + l) := by simp only [w]; ring
        rw [this]
        exact neg_mem (add_mem hc hl))
    exact ⟨γ, hγ, w, hwε, hw0, hγτ⟩

/-! ### Growth estimates in the cusp -/

theorem τ'_mul (c : CuspData U) {s : ℂ} (hs : s.re < Real.log c.r₁) :
    τ' U c.M s * (2 * π * I) = c.κ * (s + c.φ (Complex.exp s)) := by
  rw [c.normal s hs]
  have : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  field_simp

theorem τ'_im (c : CuspData U) {s : ℂ} (hs : s.re < Real.log c.r₁) :
    (τ' U c.M s).im = (c.κ / (2 * π)) * (-s.re - (c.φ (Complex.exp s)).re) := by
  have h := congrArg Complex.re (τ'_mul c hs)
  simp only [mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im, add_re, add_im,
    re_ofNat, im_ofNat] at h
  field_simp
  nlinarith [h]

theorem τ'_re (c : CuspData U) {s : ℂ} (hs : s.re < Real.log c.r₁) :
    (τ' U c.M s).re = (c.κ / (2 * π)) * (s.im + (c.φ (Complex.exp s)).im) := by
  have h := congrArg Complex.im (τ'_mul c hs)
  simp only [mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im, add_re, add_im,
    re_ofNat, im_ofNat] at h
  field_simp
  nlinarith [h]

theorem exp_le_two_cosh (x : ℝ) : Real.exp x ≤ 2 * Real.cosh x := by
  rw [Real.cosh_eq]; nlinarith [Real.exp_pos (-x)]

theorem log_bounds_of_sq_mul {P r : ℝ} (hr : 0 < r) (hr1 : r < 1) (hP0 : 0 ≤ P)
    (hle : P * r ^ 2 ≤ 3 / 2) (hge : 1 / 2 ≤ P * r ^ 2) :
    Real.log (1 + P) ≤ Real.log 3 + 2 * Real.log (1 / r) ∧
      Real.log (1 / r) ≤ (Real.log (2 + P) + Real.log 2) / 2 := by
  have hr2 : 0 < r ^ 2 := by positivity
  have hlogw : Real.log (1 / r ^ 2) = 2 * Real.log (1 / r) := by
    rw [one_div, one_div, Real.log_inv, Real.log_inv, Real.log_pow]; push_cast; ring
  constructor
  · have hx : 1 ≤ 1 / r ^ 2 := by
      rw [le_div_iff₀ hr2, one_mul]; nlinarith
    have h1 : 1 + P ≤ 3 * (1 / r ^ 2) := by
      have : P ≤ (3 / 2) * (1 / r ^ 2) := by
        rw [mul_one_div, le_div_iff₀ hr2]; linarith
      linarith
    calc Real.log (1 + P) ≤ Real.log (3 * (1 / r ^ 2)) := Real.log_le_log (by positivity) h1
      _ = Real.log 3 + 2 * Real.log (1 / r) := by
          rw [Real.log_mul (by norm_num) (by positivity), hlogw]
  · have hx : 1 / r ^ 2 ≤ 2 * (2 + P) := by
      rw [div_le_iff₀ hr2]
      have : (2 * (2 + P)) * r ^ 2 = 4 * r ^ 2 + 2 * (P * r ^ 2) := by ring
      linarith
    have := Real.log_le_log (by positivity) hx
    rw [hlogw, Real.log_mul (by norm_num) (by positivity)] at this
    linarith

/-- **The cusp estimates.** Near a lattice point, the depth of `Σ (log w)` is comparable with
`log log (1/|w|)`, and `|℘ w|` with `|w|⁻²`. -/
theorem cusp_estimates (c : CuspData U) : ∃ ε > 0, ε ≤ c.r₁ ∧ ∃ A B : ℝ,
    ∀ w ∈ ball (0 : ℂ) ε, w ≠ 0 →
      Real.log (1 + ‖(Lt t).weierstrassP w‖) ≤
          A * Real.exp (depth U (Sig U (Complex.log w))) + B ∧
        Real.exp (depth U (Sig U (Complex.log w))) ≤
          A * Real.log (2 + ‖(Lt t).weierstrassP w‖) + B := by
  obtain ⟨h, hh⟩ := exists_orbit_height c
  set H := max h 1
  have hH : 0 < H := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hκ := c.κ_pos
  -- the asymptotics of `℘`
  obtain ⟨ε₁, hε₁, hε₁℘⟩ := Metric.eventually_nhds_iff_ball.mp
    (eventually_nhdsWithin_iff.mp ((Heights.tendsto_sq_mul_weierstrassP_zero (Lt t)).eventually
      (Metric.ball_mem_nhds (1 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2))))
  set Φ := c.Φ
  have hΦ0 : 0 ≤ Φ := le_trans (norm_nonneg _) (c.φ_le 0 (mem_ball_self c.r₁_pos))
  set ε := min (min c.r₁ ε₁) (min (1 / 2) (Real.exp (-(Φ + 2 * π / c.κ))))
  have hε : 0 < ε := lt_min (lt_min c.r₁_pos hε₁) (lt_min (by norm_num) (Real.exp_pos _))
  have hεr : ε ≤ c.r₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hεε₁ : ε ≤ ε₁ := (min_le_left _ _).trans (min_le_right _ _)
  have hεhalf : ε ≤ 1 / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hεexp : ε ≤ Real.exp (-(Φ + 2 * π / c.κ)) := (min_le_right _ _).trans (min_le_right _ _)
  set z₀ : ℍ := c.M⁻¹ • e₀ U
  set R := (c.κ / (2 * π)) * (π + Φ) + |z₀.re|
  set C₀ := (R ^ 2 + z₀.im ^ 2) / z₀.im
  refine ⟨ε, hε, hεr, max (4 * π * H / c.κ) (max (c.κ / (π * z₀.im)) 1),
    |Real.log 3| + 2 * Φ + 2 + 2 * C₀ + (c.κ / (π * z₀.im)) * (Φ + Real.log 2) + 10,
    fun w hw hw0 ↦ ?_⟩
  set s := Complex.log w
  have hwr : ‖w‖ < ε := mem_ball_zero_iff.mp hw
  have hw1 : ‖w‖ < 1 := hwr.trans_le (hεhalf.trans (by norm_num))
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  have hs : s.re < Real.log c.r₁ := log_mem_ball c (ball_subset_ball hεr hw) hw0
  set ℓ := -s.re
  have hℓ : ℓ = Real.log (1 / ‖w‖) := by
    simp only [ℓ, s, Complex.log_re, one_div, Real.log_inv]
  have hsim : |s.im| ≤ π := by
    rw [Complex.log_im]; exact abs_le.mpr ⟨(Complex.neg_pi_lt_arg w).le, Complex.arg_le_pi w⟩
  have hexp_s : Complex.exp s = w := Complex.exp_log hw0
  have hφw : ‖c.φ w‖ ≤ Φ := c.φ_le w (ball_subset_ball hεr hw)
  have hφre : |(c.φ w).re| ≤ Φ := (abs_re_le_norm _).trans hφw
  have hφim : |(c.φ w).im| ≤ Φ := (abs_im_le_norm _).trans hφw
  set z : ℍ := c.M⁻¹ • Sig U s
  have hzim : z.im = (c.κ / (2 * π)) * (ℓ - (c.φ w).re) := by
    have := τ'_im c hs; rw [hexp_s] at this
    change (τ' U c.M s).im = _; rw [this]
  have hzre : z.re = (c.κ / (2 * π)) * (s.im + (c.φ w).im) := by
    have := τ'_re c hs; rw [hexp_s] at this
    change (τ' U c.M s).re = _; exact this
  have hκ2π : 0 < c.κ / (2 * π) := by positivity
  -- `ℓ` is large
  have hℓbig : Φ + 2 * π / c.κ < ℓ := by
    rw [hℓ, one_div, Real.log_inv, lt_neg]
    calc Real.log ‖w‖ < Real.log ε := Real.log_lt_log hwpos hwr
      _ ≤ Real.log (Real.exp (-(Φ + 2 * π / c.κ))) := Real.log_le_log hε hεexp
      _ = -(Φ + 2 * π / c.κ) := Real.log_exp _
  have hzim1 : 1 ≤ z.im := by
    rw [hzim]
    have : 2 * π / c.κ ≤ ℓ - (c.φ w).re := by linarith [(abs_le.mp hφre).2]
    calc (1 : ℝ) = (c.κ / (2 * π)) * (2 * π / c.κ) := by field_simp
      _ ≤ _ := by gcongr
  -- the depth is at least `log (Im z / H)`
  have hdepth_ge : Real.log z.im - Real.log H ≤ depth U (Sig U s) := by
    refine le_depth fun γ hγ ↦ ?_
    have hγ' := inv_mem hγ
    have hht : (c.M⁻¹ • (γ⁻¹ • e₀ U)).im ≤ H := (hh _ hγ').trans (le_max_left _ _)
    calc Real.log z.im - Real.log H ≤ Real.log z.im - Real.log (c.M⁻¹ • (γ⁻¹ • e₀ U)).im := by
          gcongr
      _ ≤ dist (Real.log z.im) (Real.log (c.M⁻¹ • (γ⁻¹ • e₀ U)).im) := by
          rw [Real.dist_eq]; exact le_abs_self _
      _ ≤ dist z (c.M⁻¹ • (γ⁻¹ • e₀ U)) := UpperHalfPlane.dist_log_im_le _ _
      _ = dist (γ • Sig U s) (e₀ U) := by
          rw [dist_smul, ← dist_smul γ, smul_inv_smul]
  have hexpD_ge : z.im / H ≤ Real.exp (depth U (Sig U s)) := by
    have := Real.exp_le_exp.mpr hdepth_ge
    rwa [Real.exp_sub, Real.exp_log (by linarith), Real.exp_log hH] at this
  -- the size of `℘`
  have h℘ := hε₁℘ w (ball_subset_ball hεε₁ hw) hw0
  rw [dist_eq_norm] at h℘
  set P := ‖(Lt t).weierstrassP w‖
  have hw2 : 0 < ‖w‖ ^ 2 := by positivity
  have hP_le : P * ‖w‖ ^ 2 ≤ 3 / 2 := by
    have := norm_sub_norm_le (w ^ 2 * (Lt t).weierstrassP w) 1
    rw [norm_mul, norm_pow, norm_one] at this
    linarith [mul_comm P (‖w‖ ^ 2)]
  have hP_ge : 1 / 2 ≤ P * ‖w‖ ^ 2 := by
    have := norm_sub_norm_le 1 (w ^ 2 * (Lt t).weierstrassP w)
    rw [norm_mul, norm_pow, norm_one, norm_sub_rev] at this
    linarith [mul_comm P (‖w‖ ^ 2)]
  obtain ⟨hlog1, hlog2⟩ := log_bounds_of_sq_mul (P := P) hwpos hw1 (norm_nonneg _)
    (by linarith [mul_comm P (‖w‖ ^ 2)]) (by linarith [mul_comm P (‖w‖ ^ 2)])
  rw [← hℓ] at hlog1 hlog2
  constructor
  · -- `log (1 + |℘ w|) ≤ log 3 + 2ℓ ≤ A e^D + B`
    have h2 := hlog1
    have h3 : ℓ ≤ (2 * π * H / c.κ) * Real.exp (depth U (Sig U s)) + Φ := by
      have hz' : (c.κ / (2 * π)) * (ℓ - Φ) ≤ z.im := by
        rw [hzim]; gcongr; linarith [(abs_le.mp hφre).2]
      have : z.im ≤ H * Real.exp (depth U (Sig U s)) := by
        rw [div_le_iff₀' hH] at hexpD_ge; exact hexpD_ge
      have h4 : (c.κ / (2 * π)) * (ℓ - Φ) ≤ H * Real.exp (depth U (Sig U s)) := hz'.trans this
      have h5 : ℓ - Φ ≤ (2 * π / c.κ) * (H * Real.exp (depth U (Sig U s))) := by
        have := mul_le_mul_of_nonneg_left h4 (by positivity : (0 : ℝ) ≤ 2 * π / c.κ)
        have e : (2 * π / c.κ) * ((c.κ / (2 * π)) * (ℓ - Φ)) = ℓ - Φ := by field_simp
        linarith
      have e2 : (2 * π / c.κ) * (H * Real.exp (depth U (Sig U s))) =
          (2 * π * H / c.κ) * Real.exp (depth U (Sig U s)) := by ring
      linarith
    have hE := Real.exp_pos (depth U (Sig U s))
    have hA : 4 * π * H / c.κ ≤ max (4 * π * H / c.κ) (max (c.κ / (π * z₀.im)) 1) :=
      le_max_left _ _
    have : (4 * π * H / c.κ) * Real.exp (depth U (Sig U s)) ≤
        max (4 * π * H / c.κ) (max (c.κ / (π * z₀.im)) 1) * Real.exp (depth U (Sig U s)) :=
      mul_le_mul_of_nonneg_right hA hE.le
    have h6 : 2 * ((2 * π * H / c.κ) * Real.exp (depth U (Sig U s))) =
        (4 * π * H / c.κ) * Real.exp (depth U (Sig U s)) := by ring
    have hC₀ : 0 ≤ C₀ := by positivity
    have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hk0 : 0 ≤ (c.κ / (π * z₀.im)) * (Φ + Real.log 2) := by
      have := z₀.im_pos; positivity
    linarith [le_abs_self (Real.log 3)]
  · -- `e^D ≤ e^{dist(z, z₀)} ≤ 2 + C₀ + Im z / Im z₀`
    have hdist : depth U (Sig U s) ≤ dist z z₀ := by
      have := depth_le (U := U) (τ := Sig U s) (γ := 1) (one_mem _)
      rw [one_smul] at this
      rwa [show dist (Sig U s) (e₀ U) = dist z z₀ by rw [dist_smul]] at this
    have hz₀ := z₀.im_pos
    have hzre' : |z.re - z₀.re| ≤ R := by
      rw [hzre]
      calc |(c.κ / (2 * π)) * (s.im + (c.φ w).im) - z₀.re|
          ≤ |(c.κ / (2 * π)) * (s.im + (c.φ w).im)| + |z₀.re| := abs_sub _ _
        _ ≤ (c.κ / (2 * π)) * (π + Φ) + |z₀.re| := by
          gcongr
          rw [abs_mul, abs_of_pos hκ2π]
          gcongr
          exact (abs_add_le _ _).trans (add_le_add hsim hφim)
    set S := R ^ 2 + z.im ^ 2 + z₀.im ^ 2
    have hzi := z.im_pos
    have hnum : dist (z : ℂ) z₀ ^ 2 ≤ S := by
      have hd : dist (z : ℂ) z₀ ^ 2 = (z.re - z₀.re) ^ 2 + (z.im - z₀.im) ^ 2 := by
        rw [Complex.dist_eq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
        simp only [sub_re, sub_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]; ring
      have h1 : (z.re - z₀.re) ^ 2 ≤ R ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hzre' 2
      have h2 : (z.im - z₀.im) ^ 2 ≤ z.im ^ 2 + z₀.im ^ 2 := by
        have := mul_pos hzi hz₀; nlinarith
      rw [hd]; simp only [S]; linarith
    have hcosh : Real.cosh (dist z z₀) ≤ 1 + S / (z.im * z₀.im) := by
      rw [UpperHalfPlane.cosh_dist]
      have hp : 0 < z.im * z₀.im := mul_pos hzi hz₀
      have : dist (z : ℂ) z₀ ^ 2 / (2 * z.im * z₀.im) ≤ S / (z.im * z₀.im) := by
        rw [show 2 * z.im * z₀.im = 2 * (z.im * z₀.im) by ring]
        calc dist (z : ℂ) z₀ ^ 2 / (2 * (z.im * z₀.im)) ≤ S / (2 * (z.im * z₀.im)) := by
              gcongr
          _ ≤ S / (z.im * z₀.im) := by
              apply div_le_div_of_nonneg_left (by positivity) hp; linarith
      linarith
    have hsplit : S / (z.im * z₀.im) ≤ C₀ + z.im / z₀.im := by
      have e : S / (z.im * z₀.im) = (R ^ 2 + z₀.im ^ 2) / (z.im * z₀.im) + z.im / z₀.im := by
        simp only [S]; field_simp; ring
      rw [e]
      gcongr
      calc (R ^ 2 + z₀.im ^ 2) / (z.im * z₀.im) ≤ (R ^ 2 + z₀.im ^ 2) / z₀.im := by
            exact div_le_div_of_nonneg_left (add_nonneg (sq_nonneg R) (sq_nonneg _)) hz₀
              (le_mul_of_one_le_left hz₀.le hzim1)
        _ = C₀ := rfl
    have hℓ℘ := hlog2
    have hzim_le : z.im ≤ (c.κ / (2 * π)) * (ℓ + Φ) := by
      rw [hzim]; gcongr; linarith [(abs_le.mp hφre).1]
    have hE : Real.exp (depth U (Sig U s)) ≤ 2 + 2 * C₀ + 2 * (z.im / z₀.im) := by
      calc Real.exp (depth U (Sig U s)) ≤ Real.exp (dist z z₀) := Real.exp_le_exp.mpr hdist
        _ ≤ 2 * Real.cosh (dist z z₀) := exp_le_two_cosh _
        _ ≤ 2 * (1 + S / (z.im * z₀.im)) := by gcongr
        _ ≤ 2 * (1 + (C₀ + z.im / z₀.im)) := by gcongr
        _ = 2 + 2 * C₀ + 2 * (z.im / z₀.im) := by ring
    set K := c.κ / (π * z₀.im)
    have hK : 0 ≤ K := by positivity
    have hzz : 2 * (z.im / z₀.im) ≤ K * (ℓ + Φ) := by
      have e : K * (ℓ + Φ) = 2 * ((c.κ / (2 * π)) * (ℓ + Φ) / z₀.im) := by
        simp only [K]; field_simp
      rw [e]; gcongr
    have hA : K ≤ max (4 * π * H / c.κ) (max K 1) :=
      (le_max_left _ _).trans (le_max_right _ _)
    have hL : 0 ≤ Real.log (2 + P) :=
      Real.log_nonneg (by linarith [norm_nonneg ((Lt t).weierstrassP w)])
    have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have h7 : K * (ℓ + Φ) ≤ K * Real.log (2 + P) + K * (Φ + Real.log 2) := by
      have : ℓ + Φ ≤ Real.log (2 + P) + (Φ + Real.log 2) := by linarith
      calc K * (ℓ + Φ) ≤ K * (Real.log (2 + P) + (Φ + Real.log 2)) := by gcongr
        _ = _ := by ring
    have h9 : K * Real.log (2 + P) ≤ max (4 * π * H / c.κ) (max K 1) * Real.log (2 + P) :=
      mul_le_mul_of_nonneg_right hA hL
    have hl3' : 0 ≤ |Real.log 3| := abs_nonneg _
    linarith only [hE, hzz, h7, h9, hl3', hΦ0]

variable (U) in
/-- `℘ ∘ ψ` on `ℍ`. -/
noncomputable def wpΨ (τ : ℍ) : ℂ := (Lt t).weierstrassP (U.ψ τ)

theorem wpΨ_smul {γ : SL(2, ℝ)} (hγ : γ ∈ U.deckGroup) (τ : ℍ) :
    wpΨ U (γ • τ) = wpΨ U τ := by
  obtain ⟨l, hl, hψ⟩ := hγ
  simp only [wpΨ, hψ τ]
  exact (Lt t).weierstrassP_add_coe _ ⟨l, hl⟩

/-- **Growth of `℘ ∘ ψ` against the depth.** -/
theorem exists_growth : ∃ A B : ℝ, 0 ≤ A ∧ ∀ τ : ℍ,
    Real.log (1 + ‖wpΨ U τ‖) ≤ A * Real.exp (depth U τ) + B ∧
      Real.exp (depth U τ) ≤ A * Real.log (2 + ‖wpΨ U τ‖) + B := by
  set c := cuspData U
  obtain ⟨ε, hε, hεr, A₁, B₁, hest⟩ := cusp_estimates c
  have hεr₀ : ε ≤ r₀ t := hεr.trans c.r₁_le
  have hKc := isCompact_Kε (t := t) ε
  have hKK := Kε_subset (t := t) hε
  obtain ⟨C₁, hC₁⟩ := hKc.exists_bound_of_continuousOn (f := (Lt t).weierstrassP)
    (((Lt t).analyticOnNhd_weierstrassP.continuousOn).mono fun k hk ↦ K_subset t (hKK hk))
  obtain ⟨C₂, hC₂⟩ := hKc.exists_bound_of_continuousOn (f := fun k ↦ dist (sK U k) (e₀ U))
    (continuous_dist.comp_continuousOn (((continuousOn_sK U).mono hKK).prodMk continuousOn_const))
  refine ⟨max A₁ 1, max B₁ 0 + Real.log (1 + |C₁|) + Real.exp |C₂|, by positivity,
    fun τ ↦ ?_⟩
  have hA : A₁ ≤ max A₁ 1 := le_max_left _ _
  have hA0 : 0 ≤ max A₁ 1 := by positivity
  have hB : B₁ ≤ max B₁ 0 := le_max_left _ _
  have hB0 : 0 ≤ max B₁ 0 := le_max_right _ _
  have hL1 : 0 ≤ Real.log (1 + |C₁|) := Real.log_nonneg (by linarith [abs_nonneg C₁])
  have hE2 : 0 ≤ Real.exp |C₂| := (Real.exp_pos _).le
  have hlog2 : 0 ≤ Real.log (2 + ‖wpΨ U τ‖) :=
    Real.log_nonneg (by linarith [norm_nonneg (wpΨ U τ)])
  have hexpD := Real.exp_pos (depth U τ)
  rcases compact_or_cusp (U := U) hεr₀ τ with ⟨γ, hγ, k, hk, hγτ⟩ | ⟨γ, hγ, w, hw, hw0, hγτ⟩
  · have h℘ : ‖wpΨ U τ‖ ≤ |C₁| := by
      rw [← wpΨ_smul hγ, hγτ]
      simp only [wpΨ, ψ_sK U (hKK hk)]
      exact (hC₁ k hk).trans (le_abs_self _)
    have hD : depth U τ ≤ |C₂| := by
      rw [← depth_smul hγ, hγτ]
      have := depth_le (U := U) (τ := sK U k) (γ := 1) (one_mem _)
      rw [one_smul] at this
      have h2 := hC₂ k hk
      rw [Real.norm_eq_abs, abs_of_nonneg dist_nonneg] at h2
      exact this.trans (h2.trans (le_abs_self _))
    constructor
    · have : Real.log (1 + ‖wpΨ U τ‖) ≤ Real.log (1 + |C₁|) :=
        Real.log_le_log (by positivity) (by linarith)
      nlinarith
    · have : Real.exp (depth U τ) ≤ Real.exp |C₂| := Real.exp_le_exp.mpr hD
      nlinarith
  · have hψ : wpΨ U τ = (Lt t).weierstrassP w := by
      rw [← wpΨ_smul hγ, hγτ]
      simp only [wpΨ]
      rw [ψ_Sig U (log_mem_Hr ⟨ball_subset_ball hεr₀ hw, hw0⟩), Complex.exp_log hw0]
    have hD : depth U τ = depth U (Sig U (Complex.log w)) := by rw [← depth_smul hγ, hγτ]
    obtain ⟨h1, h2⟩ := hest w hw hw0
    rw [hψ, hD]
    rw [← hψ, ← hD] at h1 h2
    rw [← hψ, ← hD]
    constructor
    · have := mul_le_mul_of_nonneg_right hA hexpD.le
      linarith
    · have := mul_le_mul_of_nonneg_right hA hlog2
      linarith

end Peripheral

end Uniformization
