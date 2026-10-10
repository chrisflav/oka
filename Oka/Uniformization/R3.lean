/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Uniformization.Integrality
import Oka.Uniformization.RatFuncPoly
import Oka.Uniformization.R3Count
import Heights.WeierstrassSurjectivity
import Heights.WeierstrassFibers
import Heights.WeierstrassDifferential

/-!
# R3: the commensurator of `Γ̃` is `Γ̃` unless `j ∈ {0, 1728}`

Let `N` be a group with `Γ̃ ≤ N ≤ Comm(Γ̃)` and `[N : Γ̃] < ∞`, where `Γ̃ = pmDeck` is the
`±`-deck group of the uniformisation of `ℂ/Λ ∖ {0}` and `F = ℘ ∘ ψ`.

1. The `N`-invariant polynomials `R_N = {p | p ∘ F is N-invariant}` form a subalgebra of `ℂ[X]`
   containing the coefficients of `∏_{q ∈ N/Γ̃} (X - F ∘ q⁻¹)`; these are not all constant.
2. By Lüroth, `R_N ⊆ ℂ[s]` for a non-constant polynomial `s` with `s ∘ F` `N`-invariant; the
   fibres of `s ∘ F` are the `N`-orbits.
3. Local orders: at `τ` over `w = F τ`, `s ∘ F - s(w)` vanishes to order `e_s(w) m(w)` with
   `m(w) = 2` iff `w` is a root of `4X³ - g₂X - g₃`; this order is `N`-invariant.
4. The orbifold Riemann–Hurwitz count (`RatFuncPoly.orbifold_count`) gives `deg s = 1`, or
   `g₃ = 0`, or `g₂ = 0`; if `deg s = 1`, `F` is `N`-invariant and `N = Γ̃`.
-/

open Complex Metric Set Filter Topology Polynomial
open UpperHalfPlane hiding I I_re I_im
open scoped MatrixGroups Pointwise

namespace Uniformization

namespace Unif

variable {L : PeriodPair} {U : Unif L}

/-- Holomorphic functions on `ℍ` form a domain. -/
theorem HolH.eq_zero_of_mul {F G : ℍ → ℂ} (hF : HolH F) (hG : HolH G)
    (h : ∀ τ, F τ * G τ = 0) {τ₀ : ℍ} (hG0 : G τ₀ ≠ 0) (τ : ℍ) : F τ = 0 := by
  set F' : ℂ → ℂ := fun z ↦ F (ofComplex z)
  set G' : ℂ → ℂ := fun z ↦ G (ofComplex z)
  have hFa : AnalyticOnNhd ℂ F' {z | 0 < z.im} := hF.analyticOnNhd isOpen_upper
  have hG'c : ContinuousAt G' τ₀ :=
    (hG.continuousOn.continuousAt (isOpen_upper.mem_nhds τ₀.im_pos))
  have hG'0 : G' τ₀ ≠ 0 := by simp only [G', ofComplex_apply]; exact hG0
  have hev : F' =ᶠ[𝓝 (τ₀ : ℂ)] 0 := by
    filter_upwards [hG'c.eventually_ne hG'0, isOpen_upper.mem_nhds τ₀.im_pos] with z hz hzi
    have := h (ofComplex z)
    exact (mul_eq_zero.mp this).resolve_right hz
  have := hFa.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_halfSpace_im_gt 0).isPreconnected τ₀.im_pos hev (τ.im_pos)
  simpa [F', ofComplex_apply] using this

end Unif

namespace Peripheral

open Generators

variable {t : ℍ} {U : Unif (Lt t)}

theorem wpΨ_surjective (U : Unif (Lt t)) : Function.Surjective (wpΨ U) := by
  intro w
  obtain ⟨z, hz, hzw⟩ := Heights.exists_notMem_lattice_weierstrassP_eq (Lt t) w
  obtain ⟨τ, hτ⟩ := U.surj z hz
  exact ⟨τ, by rw [wpΨ, Unif.ψ, hτ, hzw]⟩

/-- The fibres of `℘ ∘ ψ` are the `Γ̃`-orbits. -/
theorem exists_mem_pmDeck_of_wpΨ_eq {τ₁ τ₂ : ℍ} (h : wpΨ U τ₁ = wpΨ U τ₂) :
    ∃ γ ∈ U.pmDeck, γ • τ₁ = τ₂ := by
  rcases (Heights.weierstrassP_eq_iff_sub_mem_or_add_mem (Lt t) (U.ψ τ₂) (U.ψ τ₁)
    (U.ψ_notMem τ₂) (U.ψ_notMem τ₁)).mp h.symm with h1 | h1
  · obtain ⟨γ, hγψ, hγ⟩ := U.exists_mem_pmDeck (ε := 1) (Or.inl rfl) (τ := τ₁) (τ' := τ₂)
      (by simpa using h1)
    exact ⟨γ, U.mem_pmDeck_of (Or.inl rfl) (by simpa using h1) hγψ, hγ⟩
  · obtain ⟨γ, hγψ, hγ⟩ := U.exists_mem_pmDeck (ε := -1) (Or.inr rfl) (τ := τ₁) (τ' := τ₂)
      (by simpa using h1)
    exact ⟨γ, U.mem_pmDeck_of (Or.inr rfl) (by simpa using h1) hγψ, hγ⟩

theorem holH_poly_wpΨ (U : Unif (Lt t)) (p : ℂ[X]) : Unif.HolH fun τ ↦ p.eval (wpΨ U τ) := by
  have h := Unif.holH_weierstrassP_ψ U
  exact (Polynomial.differentiable p).comp_differentiableOn h

section Orders

/-- The cubic `4X³ - g₂X - g₃` of a lattice. -/
noncomputable def cubic (L : PeriodPair) : ℂ[X] := C 4 * X ^ 3 - C L.g₂ * X - C L.g₃

/-- The `x`-coordinates of the nonzero `2`-torsion points: the roots of the cubic. -/
noncomputable def E₂ (L : PeriodPair) : Finset ℂ := (cubic L).roots.toFinset

theorem cubic_eval (L : PeriodPair) (w : ℂ) :
    (cubic L).eval w = 4 * w ^ 3 - L.g₂ * w - L.g₃ := by
  simp [cubic]

theorem cubic_ne_zero (L : PeriodPair) : cubic L ≠ 0 := by
  intro h
  have := congrArg (coeff · 3) h
  simp [cubic] at this

theorem mem_E₂ (L : PeriodPair) {w : ℂ} : w ∈ E₂ L ↔ 4 * w ^ 3 - L.g₂ * w - L.g₃ = 0 := by
  rw [E₂, Multiset.mem_toFinset, mem_roots (cubic_ne_zero L), IsRoot, cubic_eval]

theorem deriv_cubic_ne_zero {L : PeriodPair} (hΔ : L.g₂ ^ 3 - 27 * L.g₃ ^ 2 ≠ 0) {w : ℂ}
    (hw : 4 * w ^ 3 - L.g₂ * w - L.g₃ = 0) : 12 * w ^ 2 - L.g₂ ≠ 0 := by
  intro h
  apply hΔ
  have hg₂ : L.g₂ = 12 * w ^ 2 := by linear_combination -h
  have hg₃ : L.g₃ = -8 * w ^ 3 := by rw [hg₂] at hw; linear_combination -hw
  rw [hg₂, hg₃]; ring

theorem card_E₂ {L : PeriodPair} (hΔ : L.g₂ ^ 3 - 27 * L.g₃ ^ 2 ≠ 0) : (E₂ L).card = 3 := by
  have hdeg : (cubic L).natDegree = 3 := by
    rw [cubic]; compute_degree!
  have hnodup : (cubic L).roots.Nodup := by
    rw [Multiset.nodup_iff_count_le_one]
    intro r
    rw [count_roots]
    by_contra hr
    push Not at hr
    have hroot : (cubic L).IsRoot r := by
      rw [← rootMultiplicity_pos (cubic_ne_zero L)]; omega
    have h1 := derivative_rootMultiplicity_of_root hroot
    have h2 : (derivative (cubic L)).IsRoot r := by
      have hd0 : derivative (cubic L) ≠ 0 := by
        rw [derivative_ne_zero, hdeg]; norm_num
      rw [← rootMultiplicity_pos hd0, h1]; omega
    have h3 : (derivative (cubic L)).eval r = 12 * r ^ 2 - L.g₂ := by
      simp [cubic]; ring
    rw [IsRoot, h3] at h2
    exact deriv_cubic_ne_zero hΔ (by rw [IsRoot, cubic_eval] at hroot; exact hroot) h2
  rw [E₂, Multiset.toFinset_card_of_nodup hnodup, IsAlgClosed.card_roots_eq_natDegree, hdeg]

theorem derivWeierstrassP_eq_zero_iff {L : PeriodPair} {z : ℂ} (hz : z ∉ L.lattice) :
    L.derivWeierstrassP z = 0 ↔ L.weierstrassP z ∈ E₂ L := by
  rw [mem_E₂, ← L.derivWeierstrassP_sq z hz, sq_eq_zero_iff]

/-- The order of vanishing of `℘ - ℘(z)` at `z`: `2` at the half periods, `1` elsewhere. -/
theorem analyticOrderAt_weierstrassP {L : PeriodPair} (hΔ : L.g₂ ^ 3 - 27 * L.g₃ ^ 2 ≠ 0)
    {z : ℂ} (hz : z ∉ L.lattice) :
    analyticOrderAt (fun u ↦ L.weierstrassP u - L.weierstrassP z) z =
      RatFuncPoly.mult (E₂ L) (L.weierstrassP z) := by
  have ha : AnalyticAt ℂ L.weierstrassP z := L.analyticOnNhd_weierstrassP z hz
  have ha' : AnalyticAt ℂ L.derivWeierstrassP z := L.analyticOnNhd_derivWeierstrassP z hz
  rw [← ha.analyticOrderAt_deriv_add_one, PeriodPair.deriv_weierstrassP, RatFuncPoly.mult]
  by_cases h0 : L.derivWeierstrassP z = 0
  · rw [if_pos ((derivWeierstrassP_eq_zero_iff hz).mp h0)]
    have hd : deriv L.derivWeierstrassP z ≠ 0 := by
      rw [Heights.deriv_derivWeierstrassP L z hz]
      have := deriv_cubic_ne_zero hΔ ((mem_E₂ L).mp ((derivWeierstrassP_eq_zero_iff hz).mp h0))
      intro h; apply this; linear_combination 2 * h
    rw [ha'.analyticOrderAt_eq_one_of_zero_deriv_ne_zero h0 hd]
    rfl
  · rw [if_neg (fun h ↦ h0 ((derivWeierstrassP_eq_zero_iff hz).mpr h)),
      ha'.analyticOrderAt_eq_zero.mpr h0]
    rfl

/-- The order of vanishing of a polynomial is its root multiplicity. -/
theorem analyticOrderAt_eval {p : ℂ[X]} (hp : p ≠ 0) (w : ℂ) :
    analyticOrderAt (fun u ↦ p.eval u) w = rootMultiplicity w p := by
  obtain ⟨q, hq, hqw⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp w
  rw [(Polynomial.differentiable p).analyticAt w |>.analyticOrderAt_eq_natCast]
  refine ⟨fun u ↦ q.eval u, (Polynomial.differentiable q).analyticAt w, ?_, ?_⟩
  · rw [dvd_iff_isRoot] at hqw; exact hqw
  · filter_upwards with u
    conv_lhs => rw [hq]
    simp [smul_eq_mul]

end Orders

section OrderInvariance

/-- The Möbius map of `g ∈ SL(2, ℝ)` on `ℂ`. -/
noncomputable def mob (g : SL(2, ℝ)) (z : ℂ) : ℂ :=
  ((g 0 0 : ℂ) * z + g 0 1) / ((g 1 0 : ℂ) * z + g 1 1)

theorem mob_coe (g : SL(2, ℝ)) (τ : ℍ) : mob g τ = ((g • τ : ℍ) : ℂ) :=
  (coe_SL2R_smul g τ).symm

theorem differentiableOn_mob (g : SL(2, ℝ)) : DifferentiableOn ℂ (mob g) {z | 0 < z.im} :=
  (((differentiableOn_const _).mul differentiableOn_id).add_const _).div
    (((differentiableOn_const _).mul differentiableOn_id).add_const _)
    fun _ hz ↦ denom_SL2R_ne_zero g hz

theorem deriv_mob_ne_zero (g : SL(2, ℝ)) (τ : ℍ) : deriv (mob g) τ ≠ 0 := by
  refine deriv_ne_zero_of_injOn (differentiableOn_mob g) (isOpen_upper.mem_nhds τ.im_pos) ?_
  intro z₁ hz₁ z₂ hz₂ h
  have h' := mob_coe g ⟨z₁, hz₁⟩
  have h'' := mob_coe g ⟨z₂, hz₂⟩
  have : g • (⟨z₁, hz₁⟩ : ℍ) = g • ⟨z₂, hz₂⟩ := UpperHalfPlane.ext (by rw [← h', ← h'', h])
  have := smul_left_cancel g this
  exact congrArg UpperHalfPlane.coe this

variable (U) in
/-- `s ∘ ℘ ∘ Ψ` on `ℂ`. -/
noncomputable def sΦ (s : ℂ[X]) (z : ℂ) : ℂ := s.eval ((Lt t).weierstrassP (U.Ψ z))

theorem sΦ_coe (s : ℂ[X]) (τ : ℍ) : sΦ U s τ = s.eval (wpΨ U τ) := rfl

/-- The order of `s ∘ F - s(F τ)` at `τ` is `e_s(w) m(w)`, `w = F τ`. -/
theorem analyticOrderAt_sΦ {s : ℂ[X]} (hs : 0 < s.natDegree) (τ : ℍ) :
    analyticOrderAt (fun z ↦ sΦ U s z - sΦ U s τ) τ =
      (RatFuncPoly.ramIdx s (wpΨ U τ) * RatFuncPoly.mult (E₂ (Lt t)) (wpΨ U τ) : ℕ) := by
  have hΔ := Heights.periodPair_invariant_discriminant_ne_zero t
  set w := wpΨ U τ
  have hΨa : AnalyticAt ℂ U.Ψ τ :=
    U.differentiableOn.analyticAt (isOpen_upper.mem_nhds τ.im_pos)
  have hΨτ : U.Ψ τ ∉ (Lt t).lattice := U.ψ_notMem τ
  have h℘a : AnalyticAt ℂ (Lt t).weierstrassP (U.Ψ τ) :=
    (Lt t).analyticOnNhd_weierstrassP _ hΨτ
  have hga : AnalyticAt ℂ (fun z ↦ (Lt t).weierstrassP (U.Ψ z)) τ := h℘a.comp hΨa
  have hs0 := RatFuncPoly.sub_C_ne_zero hs (s.eval w)
  have hfa : AnalyticAt ℂ (fun u ↦ (s - C (s.eval w)).eval u)
      ((fun z ↦ (Lt t).weierstrassP (U.Ψ z)) τ) :=
    (Polynomial.differentiable _).analyticAt _
  have heq : (fun z ↦ sΦ U s z - sΦ U s τ) =
      (fun u ↦ (s - C (s.eval w)).eval u) ∘ (fun z ↦ (Lt t).weierstrassP (U.Ψ z)) := by
    funext z; simp [sΦ, w, wpΨ, Unif.ψ]
  rw [heq, AnalyticAt.analyticOrderAt_comp (g := fun z ↦ (Lt t).weierstrassP (U.Ψ z))
    (z₀ := (τ : ℂ)) hfa hga]
  have h1 : analyticOrderAt (fun u ↦ (s - C (s.eval w)).eval u)
      ((Lt t).weierstrassP (U.Ψ τ)) = RatFuncPoly.ramIdx s w := by
    rw [analyticOrderAt_eval hs0]; rfl
  have h2 : analyticOrderAt (fun z ↦ (Lt t).weierstrassP (U.Ψ z) -
      (Lt t).weierstrassP (U.Ψ τ)) τ = RatFuncPoly.mult (E₂ (Lt t)) w := by
    have := analyticOrderAt_comp_of_deriv_ne_zero
      (f := fun u ↦ (Lt t).weierstrassP u - (Lt t).weierstrassP (U.Ψ τ)) hΨa
      (U.deriv_ne_zero τ τ.im_pos)
    rw [Function.comp_def] at this
    rw [this, analyticOrderAt_weierstrassP hΔ hΨτ]; rfl
  rw [h1, h2, Nat.cast_mul]

/-- The order is invariant under Möbius maps preserving `s ∘ F`. -/
theorem analyticOrderAt_sΦ_smul {s : ℂ[X]} {n : SL(2, ℝ)}
    (hn : ∀ σ, s.eval (wpΨ U (n • σ)) = s.eval (wpΨ U σ)) (τ : ℍ) :
    analyticOrderAt (fun z ↦ sΦ U s z - sΦ U s (n • τ : ℍ)) (n • τ : ℍ) =
      analyticOrderAt (fun z ↦ sΦ U s z - sΦ U s τ) τ := by
  have hMa : AnalyticAt ℂ (mob n) τ :=
    (differentiableOn_mob n).analyticAt (isOpen_upper.mem_nhds τ.im_pos)
  have := analyticOrderAt_comp_of_deriv_ne_zero
    (f := fun z ↦ sΦ U s z - sΦ U s (n • τ : ℍ)) hMa (deriv_mob_ne_zero n τ)
  rw [mob_coe] at this
  rw [← this]
  apply analyticOrderAt_congr
  filter_upwards [isOpen_upper.mem_nhds τ.im_pos] with z hz
  have hz' : mob n z = ((n • (⟨z, hz⟩ : ℍ) : ℍ) : ℂ) := mob_coe n ⟨z, hz⟩
  simp only [Function.comp_apply, hz']
  rw [sΦ_coe, sΦ_coe, hn, hn]
  rfl

end OrderInvariance

section Comm

variable (U) in
/-- The polynomials `p` with `p ∘ ℘ ∘ ψ` invariant under `N`. -/
def invPoly (N : Subgroup SL(2, ℝ)) : Subalgebra ℂ ℂ[X] where
  carrier := {p | ∀ n ∈ N, ∀ τ, p.eval (wpΨ U (n • τ)) = p.eval (wpΨ U τ)}
  mul_mem' {p q} hp hq n hn τ := by simp only [eval_mul, hp n hn τ, hq n hn τ]
  add_mem' {p q} hp hq n hn τ := by simp only [eval_add, hp n hn τ, hq n hn τ]
  algebraMap_mem' c n _ τ := by simp

variable {N : Subgroup SL(2, ℝ)}

theorem mem_invPoly {p : ℂ[X]} :
    p ∈ invPoly U N ↔ ∀ n ∈ N, ∀ τ, p.eval (wpΨ U (n • τ)) = p.eval (wpΨ U τ) := Iff.rfl

/-- **The coset polynomial** `∏_{q ∈ N/Γ̃} (X - F ∘ q⁻¹)`: its coefficients are polynomials in `F`
lying in `R_N`. -/
theorem exists_cosetPoly (hΓN : U.pmDeck ≤ N)
    (hNC : N ≤ Subgroup.Commensurable.commensurator U.pmDeck)
    (hfin : U.pmDeck.relIndex N ≠ 0) :
    ∃ (ι : Type) (_ : Fintype ι) (g : ι → SL(2, ℝ)) (p : ℕ → ℂ[X]),
      (∀ i, g i ∈ N) ∧ (∀ k, p k ∈ invPoly U N) ∧
      (∀ τ k, (∏ i, (X - C (wpΨ U (g i • τ)))).coeff k = (p k).eval (wpΨ U τ)) ∧
      ∃ i₀, ∀ τ, wpΨ U (g i₀ • τ) = wpΨ U τ := by
  classical
  set Γ := U.pmDeck
  haveI : (Γ.subgroupOf N).FiniteIndex := ⟨hfin⟩
  haveI : Finite (N ⧸ Γ.subgroupOf N) := Subgroup.finite_quotient_of_finiteIndex
  letI := Fintype.ofFinite (N ⧸ Γ.subgroupOf N)
  have hinvΓ : ∀ γ ∈ Γ, ∀ τ, wpΨ U (γ • τ) = wpΨ U τ := fun γ hγ τ ↦ U.wp_ψ_smul_pm hγ τ
  let g : N ⧸ Γ.subgroupOf N → SL(2, ℝ) := fun q ↦ ((q.out : N) : SL(2, ℝ))⁻¹
  let f : N ⧸ Γ.subgroupOf N → ℍ → ℂ := fun q τ ↦ wpΨ U (g q • τ)
  have hf : ∀ x : N, ∀ τ, f (QuotientGroup.mk x) τ = wpΨ U (((x : SL(2, ℝ)))⁻¹ • τ) := by
    intro x τ
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (Γ.subgroupOf N) x
    have hmem : ((h : N) : SL(2, ℝ)) ∈ Γ := Subgroup.mem_subgroupOf.mp h.2
    simp only [f, g, hh, Subgroup.coe_mul, mul_inv_rev, mul_smul]
    exact hinvΓ _ (Γ.inv_mem hmem) _
  set P₀ : ℍ → ℂ[X] := fun τ ↦ ∏ q, (X - C (f q τ))
  have hP₀inv : ∀ m ∈ N, ∀ τ, P₀ (m • τ) = P₀ τ := by
    intro m hm τ
    set m' : N := ⟨m, hm⟩
    have hfq : ∀ q, f q (m • τ) = f (m'⁻¹ • q) τ := by
      intro q
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      rw [MulAction.Quotient.smul_mk, hf, hf, smul_eq_mul, Subgroup.coe_mul, Subgroup.coe_inv,
        mul_inv_rev, inv_inv, mul_smul]
    simp only [P₀, hfq]
    exact Fintype.prod_equiv (MulAction.toPerm m'⁻¹) _ _ fun q ↦ rfl
  have hσ : ∀ q, g q ∈ Subgroup.Commensurable.commensurator Γ := fun q ↦
    Subgroup.inv_mem _ (hNC (q.out : N).2)
  choose Cq Nq hq using fun q ↦ exists_poly_bound_smul (U := U) (hσ q)
  have hcoeff : ∀ k : ℕ, ∃ p : ℂ[X], ∀ τ, (P₀ τ).coeff k = p.eval (wpΨ U τ) := by
    intro k
    refine eq_poly_of_bound (U := U) (fun γ hγ τ ↦ by rw [hP₀inv γ (hΓN hγ) τ]) ?_
      (C := ∏ q, (1 + |Cq q|)) (N := ∑ q, Nq q) fun τ ↦ ?_
    · refine differentiableOn_coeff_prod_X_sub_C Finset.univ
        (a := fun q z ↦ f q (ofComplex z)) (fun q _ ↦ ?_) k
      exact (Unif.holH_weierstrassP_ψ U).comp_smul _
    · set w := ‖wpΨ U τ‖
      have hw1 : 1 ≤ 2 + w := by linarith [norm_nonneg (wpΨ U τ)]
      refine (norm_coeff_prod_X_sub_C_le _ _ k).trans ?_
      rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
      refine Finset.prod_le_prod (fun q _ ↦ by positivity) fun q _ ↦ ?_
      have h1 : 1 ≤ (2 + w) ^ Nq q := one_le_pow₀ hw1
      have h2 := hq q τ
      have h3 : Cq q * (2 + w) ^ Nq q ≤ |Cq q| * (2 + w) ^ Nq q :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      change 1 + ‖wpΨ U (g q • τ)‖ ≤ _
      nlinarith
  choose p hp using hcoeff
  refine ⟨N ⧸ Γ.subgroupOf N, inferInstance, g, p, fun q ↦ inv_mem (q.out : N).2,
    fun k n hn τ ↦ ?_, fun τ k ↦ hp k τ, QuotientGroup.mk 1, fun τ ↦ ?_⟩
  · rw [← hp, ← hp, hP₀inv n hn]
  · change f _ τ = _
    rw [hf, Subgroup.coe_one, inv_one, one_smul]

/-- **The generator**: a non-constant polynomial `s` with `s ∘ F` `N`-invariant, whose fibres are
the `N`-orbits. -/
theorem exists_generator (hΓN : U.pmDeck ≤ N)
    (hNC : N ≤ Subgroup.Commensurable.commensurator U.pmDeck)
    (hfin : U.pmDeck.relIndex N ≠ 0) :
    ∃ s : ℂ[X], 0 < s.natDegree ∧
      (∀ n ∈ N, ∀ τ, s.eval (wpΨ U (n • τ)) = s.eval (wpΨ U τ)) ∧
      ∀ τ τ', s.eval (wpΨ U τ) = s.eval (wpΨ U τ') → ∃ n ∈ N, n • τ = τ' := by
  classical
  obtain ⟨ι, _, g, p, hgN, hpN, hcoef, i₀, hi₀⟩ := exists_cosetPoly hΓN hNC hfin
  set P : ℍ → ℂ[X] := fun τ ↦ ∏ i, (X - C (wpΨ U (g i • τ)))
  have hP0 : ∀ τ, P τ ≠ 0 := fun τ ↦ (monic_prod_X_sub_C _ _).ne_zero
  have hroot : ∀ τ, (P τ).eval (wpΨ U τ) = 0 := fun τ ↦ by
    simp only [P, eval_prod, eval_sub, eval_X, eval_C]
    exact Finset.prod_eq_zero (Finset.mem_univ i₀) (by rw [hi₀, sub_self])
  -- some coefficient is non-constant
  have hnc : ∃ k, 0 < (p k).natDegree := by
    by_contra hcon
    push Not at hcon
    have hconst : ∀ τ τ', P τ = P τ' := fun τ τ' ↦ by
      ext k
      rw [hcoef, hcoef, eq_C_of_natDegree_le_zero (hcon k), eval_C, eval_C]
    obtain ⟨w, hw⟩ := Infinite.exists_notMem_finset (P UpperHalfPlane.I).roots.toFinset
    obtain ⟨τ, hτ⟩ := wpΨ_surjective U w
    apply hw
    rw [Multiset.mem_toFinset, mem_roots (hP0 _), IsRoot, ← hτ, hconst _ τ]
    exact hroot τ
  obtain ⟨k, hk⟩ := hnc
  obtain ⟨s, hs, ⟨r, hr, q, hq, hq0, hsq⟩, hcomp⟩ :=
    RatFuncPoly.exists_poly_generator (invPoly U N) ⟨p k, hpN k, hk⟩
  refine ⟨s, hs, fun n hn τ ↦ ?_, fun τ τ' hττ' ↦ ?_⟩
  · -- invariance
    have hmul : ∀ σ, (s.eval (wpΨ U (n • σ)) - s.eval (wpΨ U σ)) * q.eval (wpΨ U σ) = 0 := by
      intro σ
      have h1 := congrArg (eval (wpΨ U (n • σ))) hsq
      have h2 := congrArg (eval (wpΨ U σ)) hsq
      rw [eval_mul] at h1 h2
      linear_combination h1 - h2 + hr n hn σ - s.eval (wpΨ U (n • σ)) * hq n hn σ
    obtain ⟨w, hw⟩ := Infinite.exists_notMem_finset q.roots.toFinset
    obtain ⟨σ₀, hσ₀⟩ := wpΨ_surjective U w
    have hne : q.eval (wpΨ U σ₀) ≠ 0 := by
      intro h0
      apply hw
      rw [Multiset.mem_toFinset, mem_roots hq0, IsRoot, ← hσ₀, h0]
    have hF : Unif.HolH fun σ ↦ s.eval (wpΨ U (n • σ)) - s.eval (wpΨ U σ) :=
      DifferentiableOn.sub ((holH_poly_wpΨ U s).comp_smul n) (holH_poly_wpΨ U s)
    exact sub_eq_zero.mp (Unif.HolH.eq_zero_of_mul hF (holH_poly_wpΨ U q) hmul hne τ)
  · -- transitivity
    have hPeq : P τ = P τ' := by
      ext j
      obtain ⟨A, hA⟩ := hcomp (p j) (hpN j)
      rw [hcoef, hcoef, hA, eval_comp, eval_comp, hττ']
    have h1 := hroot τ'
    rw [← hPeq] at h1
    simp only [P, eval_prod, eval_sub, eval_X, eval_C, Finset.prod_eq_zero_iff,
      Finset.mem_univ, true_and, sub_eq_zero] at h1
    obtain ⟨i, hi⟩ := h1
    obtain ⟨γ, hγ, hγτ⟩ := exists_mem_pmDeck_of_wpΨ_eq hi.symm
    exact ⟨γ * g i, N.mul_mem (hΓN hγ) (hgN i), by rw [mul_smul, hγτ]⟩

/-- An element preserving `F = ℘ ∘ ψ` lies in `Γ̃`. -/
theorem mem_pmDeck_of_wpΨ_smul {n : SL(2, ℝ)} (hn : ∀ σ, wpΨ U (n • σ) = wpΨ U σ) :
    n ∈ U.pmDeck := by
  classical
  -- a point where `F` is locally injective
  obtain ⟨w, hw⟩ := Infinite.exists_notMem_finset (E₂ (Lt t))
  obtain ⟨τ₀, hτ₀⟩ := wpΨ_surjective U w
  have hΨτ : U.Ψ τ₀ ∉ (Lt t).lattice := U.ψ_notMem τ₀
  have hd : (Lt t).derivWeierstrassP (U.Ψ τ₀) ≠ 0 := fun h0 ↦
    hw (hτ₀ ▸ (derivWeierstrassP_eq_zero_iff hΨτ).mp h0)
  have hΨ : HasStrictDerivAt U.Ψ (deriv U.Ψ τ₀) τ₀ := U.hasStrictDerivAt_Ψ τ₀.im_pos
  have h℘ : HasStrictDerivAt (Lt t).weierstrassP ((Lt t).derivWeierstrassP (U.Ψ τ₀))
      (U.Ψ τ₀) := by
    have := ((Lt t).analyticOnNhd_weierstrassP _ hΨτ).hasStrictDerivAt
    rwa [PeriodPair.deriv_weierstrassP] at this
  have hg := h℘.comp (τ₀ : ℂ) hΨ
  have hg0 : (Lt t).derivWeierstrassP (U.Ψ τ₀) * deriv U.Ψ τ₀ ≠ 0 :=
    mul_ne_zero hd (U.deriv_ne_zero τ₀ τ₀.im_pos)
  obtain ⟨V, hV, hVinj⟩ : ∃ V ∈ 𝓝 (τ₀ : ℂ), ∀ x ∈ V, ∀ y ∈ V,
      (Lt t).weierstrassP (U.Ψ x) = (Lt t).weierstrassP (U.Ψ y) → x = y := by
    refine ⟨_, hg.eventually_left_inverse hg0, fun x hx y hy hxy ↦ ?_⟩
    have hx' : _ = x := hx
    have hy' : _ = y := hy
    simp only [Function.comp_apply] at hx' hy'
    rw [← hx', ← hy', hxy]
  -- reduce to an element fixing `τ₀`
  obtain ⟨γ, hγ, hγτ⟩ := exists_mem_pmDeck_of_wpΨ_eq (hn τ₀).symm
  set m := γ⁻¹ * n
  have hmτ : m • τ₀ = τ₀ := by rw [mul_smul, ← hγτ, inv_smul_smul]
  have hm : ∀ σ, wpΨ U (m • σ) = wpΨ U σ := fun σ ↦ by
    rw [mul_smul]
    exact (U.wp_ψ_smul_pm (U.pmDeck.inv_mem hγ) (n • σ)).trans (hn σ)
  -- `m` fixes a neighbourhood of `τ₀`
  have hmob : ContinuousAt (mob m) τ₀ :=
    ((differentiableOn_mob m).differentiableAt (isOpen_upper.mem_nhds τ₀.im_pos)).continuousAt
  have hmτ' : mob m τ₀ = τ₀ := by rw [mob_coe, hmτ]
  have hW : {z : ℂ | 0 < z.im ∧ z ∈ V ∧ mob m z ∈ V} ∈ 𝓝 (τ₀ : ℂ) := by
    refine Filter.inter_mem (isOpen_upper.mem_nhds τ₀.im_pos) (Filter.inter_mem hV ?_)
    exact hmob (by rw [hmτ']; exact hV)
  have hfix : ∀ z ∈ {z : ℂ | 0 < z.im ∧ z ∈ V ∧ mob m z ∈ V}, fixPoly m z = 0 := by
    rintro z ⟨hz, hzV, hmzV⟩
    have h1 := mob_coe m ⟨z, hz⟩
    have h2 : (Lt t).weierstrassP (U.Ψ (mob m z)) = (Lt t).weierstrassP (U.Ψ z) := by
      rw [h1]; exact hm ⟨z, hz⟩
    have h3 := hVinj _ hmzV _ hzV h2
    have h4 : m • (⟨z, hz⟩ : ℍ) = ⟨z, hz⟩ := UpperHalfPlane.ext (by rw [← h1, h3])
    have h5 := (smul_eq_self_iff m _).mp h4
    exact h5
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hW
  set E : Finset ℂ := {(τ₀ : ℂ), (τ₀ : ℂ) + ((ε / 2 : ℝ) : ℂ), (τ₀ : ℂ) + ((ε / 3 : ℝ) : ℂ)}
  have hE : E.card = 3 := by
    have h1 : (ε / 2 : ℝ) ≠ 0 := by positivity
    have h2 : (ε / 3 : ℝ) ≠ 0 := by positivity
    have h3 : (ε / 2 : ℝ) ≠ ε / 3 := by intro h; linarith
    rw [Finset.card_eq_three]
    refine ⟨_, _, _, ?_, ?_, ?_, rfl⟩
    · intro h; apply h1; exact_mod_cast (add_eq_left.mp h.symm)
    · intro h; apply h2; exact_mod_cast (add_eq_left.mp h.symm)
    · intro h; apply h3; exact_mod_cast (add_left_cancel h)
  have hEsub : ∀ z ∈ E, z ∈ Metric.ball (τ₀ : ℂ) ε := by
    intro z hz
    simp only [E, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl
    · exact Metric.mem_ball_self hε
    · rw [Metric.mem_ball, Complex.dist_eq, add_sub_cancel_left, Complex.norm_real,
        Real.norm_eq_abs,         abs_of_pos (by positivity)]; linarith
    · rw [Metric.mem_ball, Complex.dist_eq, add_sub_cancel_left, Complex.norm_real,
        Real.norm_eq_abs,         abs_of_pos (by positivity)]; linarith
  obtain ⟨hc, hb, ha⟩ := RatFuncPoly.quadratic_eq_zero (α := (m 1 0 : ℂ))
    (β := (m 1 1 - m 0 0 : ℂ)) (γ := -(m 0 1 : ℂ)) hE fun z hz ↦ by
      have := hfix z (hball (hEsub z hz))
      simpa [fixPoly, sub_eq_add_neg] using this
  have hc' : m 1 0 = 0 := by exact_mod_cast hc
  have hb' : m 1 1 = m 0 0 := by
    have : ((m 1 1 : ℝ) : ℂ) = (m 0 0 : ℝ) := by linear_combination hb
    exact_mod_cast this
  have ha' : m 0 1 = 0 := by
    have : ((m 0 1 : ℝ) : ℂ) = 0 := by linear_combination -ha
    exact_mod_cast this
  have hdet := det_SL m
  rw [hc', ha', hb'] at hdet
  have hsq : m 0 0 = 1 ∨ m 0 0 = -1 := by
    have : (m 0 0 - 1) * (m 0 0 + 1) = 0 := by linear_combination hdet
    rcases mul_eq_zero.mp this with h | h
    · left; linarith
    · right; linarith
  have hnγ : n = γ * m := by simp [m]
  rcases hsq with h1 | h1
  · have : m = 1 := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [h1, hc', ha', hb']
    rw [hnγ, this, mul_one]; exact hγ
  · have : m = -1 := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [h1, hc', ha', hb']
    rw [hnγ, this]
    exact U.pmDeck.mul_mem hγ (U.deckGroup_le_pmDeck (neg_one_mem_deckGroup U))

/-- The orbifold condition: `e_s m` is constant on the fibres of `s`. -/
theorem orbifold_condition {s : ℂ[X]} (hs : 0 < s.natDegree)
    (hinv : ∀ n ∈ N, ∀ σ, s.eval (wpΨ U (n • σ)) = s.eval (wpΨ U σ))
    (htrans : ∀ τ τ', s.eval (wpΨ U τ) = s.eval (wpΨ U τ') → ∃ n ∈ N, n • τ = τ')
    (w w' : ℂ) (hww' : s.eval w = s.eval w') :
    RatFuncPoly.ramIdx s w * RatFuncPoly.mult (E₂ (Lt t)) w =
      RatFuncPoly.ramIdx s w' * RatFuncPoly.mult (E₂ (Lt t)) w' := by
  obtain ⟨τ, rfl⟩ := wpΨ_surjective U w
  obtain ⟨τ', rfl⟩ := wpΨ_surjective U w'
  obtain ⟨n, hn, rfl⟩ := htrans τ τ' hww'
  have h1 := analyticOrderAt_sΦ (U := U) hs τ
  have h2 := analyticOrderAt_sΦ (U := U) hs (n • τ)
  rw [analyticOrderAt_sΦ_smul (hinv n hn)] at h2
  exact_mod_cast h1.symm.trans h2

/-- **R3.** If `Γ̃ ≤ N ≤ Comm(Γ̃)` with `[N : Γ̃] < ∞`, then `N = Γ̃`, unless `g₃ = 0`
(`j = 1728`) or `g₂ = 0` (`j = 0`). -/
theorem le_pmDeck_or (hΓN : U.pmDeck ≤ N)
    (hNC : N ≤ Subgroup.Commensurable.commensurator U.pmDeck)
    (hfin : U.pmDeck.relIndex N ≠ 0) :
    N ≤ U.pmDeck ∨ (Lt t).g₃ = 0 ∨ (Lt t).g₂ = 0 := by
  have hΔ := Heights.periodPair_invariant_discriminant_ne_zero t
  obtain ⟨s, hs, hinv, htrans⟩ := exists_generator hΓN hNC hfin
  have hroot : ∀ w ∈ E₂ (Lt t), 4 * w ^ 3 - (Lt t).g₂ * w - (Lt t).g₃ = 0 :=
    fun w hw ↦ (mem_E₂ _).mp hw
  rcases RatFuncPoly.orbifold_count hs (card_E₂ hΔ) (orbifold_condition hs hinv htrans) with
    hD | ⟨-, c, hc⟩ | ⟨-, c, ρ, hc⟩
  · left
    intro n hn
    apply mem_pmDeck_of_wpΨ_smul
    intro σ
    have hlin := eq_X_add_C_of_natDegree_le_one hD.le
    have ha : s.coeff 1 ≠ 0 := by
      have := leadingCoeff_ne_zero.mpr (show s ≠ 0 by rintro rfl; simp at hs)
      rwa [leadingCoeff, hD] at this
    have h := hinv n hn σ
    rw [hlin] at h
    simp only [eval_add, eval_mul, eval_C, eval_X, add_left_inj] at h
    exact mul_left_cancel₀ ha h
  · exact Or.inr (Or.inl (RatFuncPoly.g₃_eq_zero_of_symm (card_E₂ hΔ) hroot hc))
  · exact Or.inr (Or.inr (RatFuncPoly.g₂_eq_zero_of_cube (card_E₂ hΔ) hroot hc))

/-- **R3 for the commensurator.** If `Γ̃` has finite index in its commensurator, the
commensurator is `Γ̃`, unless `g₃ = 0` or `g₂ = 0`. -/
theorem commensurator_eq_pmDeck_or
    (hfin : U.pmDeck.relIndex (Subgroup.Commensurable.commensurator U.pmDeck) ≠ 0) :
    Subgroup.Commensurable.commensurator U.pmDeck = U.pmDeck ∨ (Lt t).g₃ = 0 ∨
      (Lt t).g₂ = 0 := by
  rcases le_pmDeck_or (le_commensurator _) le_rfl hfin with h | h
  · exact Or.inl (le_antisymm h (le_commensurator _))
  · exact Or.inr h

end Comm

end Peripheral

end Uniformization
