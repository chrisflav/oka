/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Uniformization.Depth
import Oka.Uniformization.EllipticPoly

/-!
# Integrality of `℘ ∘ ψ ∘ δ` over `ℂ[℘ ∘ ψ]` for `δ` in the commensurator

Let `ψ : ℍ → ℂ ∖ Λ` be the uniformisation of the once-punctured torus `ℂ/Λ ∖ {0}`,
`Γ̃ = pmDeck` its `±`-deck group and `F = ℘ ∘ ψ` (`Peripheral.wpΨ`).

* `Peripheral.eq_poly_of_bound`: a `Γ̃`-invariant holomorphic function `g` on `ℍ` with
  `|g| ≤ C (2 + |F|)^N` is a polynomial in `F`. (It descends to an even elliptic function with a
  pole of order at most `2N` at `0`; `Peripheral.exists_poly_weierstrassP`.)
* `Peripheral.exists_poly_bound_smul`: for `σ` in the commensurator of `Γ̃`,
  `|F ∘ σ| ≤ C (2 + |F|)^N` (depth moves by a bounded amount, and `log |F| ≍ e^{depth}`).
* `Peripheral.exists_monic_wpΨ_smul` (**key lemma K2**): for `δ` in the commensurator of `Γ̃`,
  `F ∘ δ` is a root of a monic polynomial with coefficients in `ℂ[F]`. The polynomial is
  `∏_{q ∈ Γ̃ / (Γ̃ ∩ δ⁻¹ Γ̃ δ)} (X - F ∘ δ ∘ q⁻¹)`: its coefficients are `Γ̃`-invariant, holomorphic
  and polynomially bounded in `F`.
-/

open Complex Metric Set Filter Topology Polynomial
open UpperHalfPlane hiding I I_re I_im
open scoped MatrixGroups Pointwise

namespace Uniformization

/-- Coefficients of `∏ (X - a i)` are bounded by `∏ (1 + |a i|)`. -/
theorem norm_coeff_prod_X_sub_C_le {ι : Type*} (s : Finset ι) (a : ι → ℂ) (k : ℕ) :
    ‖(∏ i ∈ s, (X - C (a i))).coeff k‖ ≤ ∏ i ∈ s, (1 + ‖a i‖) := by
  classical
  induction s using Finset.induction_on generalizing k with
  | empty =>
    rw [Finset.prod_empty, Finset.prod_empty, coeff_one]
    split_ifs <;> norm_num
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj, mul_comm (X - C _)]
    have hM : 0 ≤ ∏ i ∈ s, (1 + ‖a i‖) := Finset.prod_nonneg fun i _ ↦ by positivity
    cases k with
    | zero =>
      rw [mul_coeff_zero, coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub, norm_mul, norm_neg]
      nlinarith [ih 0, norm_nonneg (a j), norm_nonneg ((∏ i ∈ s, (X - C (a i))).coeff 0)]
    | succ k =>
      rw [coeff_mul_X_sub_C]
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul]
      nlinarith [ih k, ih (k + 1), norm_nonneg (a j),
        norm_nonneg ((∏ i ∈ s, (X - C (a i))).coeff (k + 1))]

/-- Coefficients of `∏ (X - a i z)` depend holomorphically on `z`. -/
theorem differentiableOn_coeff_prod_X_sub_C {ι : Type*} (s : Finset ι) {a : ι → ℂ → ℂ}
    {S : Set ℂ} (ha : ∀ i ∈ s, DifferentiableOn ℂ (a i) S) (k : ℕ) :
    DifferentiableOn ℂ (fun z ↦ (∏ i ∈ s, (X - C (a i z))).coeff k) S := by
  classical
  induction s using Finset.induction_on generalizing k with
  | empty => exact differentiableOn_const _
  | insert j s hj ih =>
    have ih' := ih fun i hi ↦ ha i (Finset.mem_insert_of_mem hi)
    have hj' := ha j (Finset.mem_insert_self j s)
    cases k with
    | zero =>
      have e : (fun z ↦ (∏ i ∈ insert j s, (X - C (a i z))).coeff 0) =
          fun z ↦ (∏ i ∈ s, (X - C (a i z))).coeff 0 * -a j z := by
        funext z
        rw [Finset.prod_insert hj, mul_comm (X - C _), mul_coeff_zero, coeff_sub, coeff_X_zero,
          coeff_C_zero, zero_sub]
      rw [e]
      exact (ih' 0).mul hj'.neg
    | succ k =>
      have e : (fun z ↦ (∏ i ∈ insert j s, (X - C (a i z))).coeff (k + 1)) =
          fun z ↦ (∏ i ∈ s, (X - C (a i z))).coeff k -
            (∏ i ∈ s, (X - C (a i z))).coeff (k + 1) * a j z := by
        funext z
        rw [Finset.prod_insert hj, mul_comm (X - C _), coeff_mul_X_sub_C]
      rw [e]
      exact (ih' k).sub ((ih' (k + 1)).mul hj')

namespace Unif

variable {L : PeriodPair} {U : Unif L}

theorem HolH.comp_smul {g : ℍ → ℂ} (hg : HolH g) (γ : SL(2, ℝ)) : HolH fun τ ↦ g (γ • τ) := by
  unfold HolH at *
  have hγ : DifferentiableOn ℂ (fun z ↦ ((γ 0 0 : ℂ) * z + γ 0 1) / ((γ 1 0 : ℂ) * z + γ 1 1))
      {z | 0 < z.im} :=
    (((differentiableOn_const _).mul differentiableOn_id).add_const _).div
      (((differentiableOn_const _).mul differentiableOn_id).add_const _)
      fun z hz ↦ denom_SL2R_ne_zero γ hz
  have hmaps : MapsTo (fun z ↦ ((γ 0 0 : ℂ) * z + γ 0 1) / ((γ 1 0 : ℂ) * z + γ 1 1))
      {z | 0 < z.im} {z | 0 < z.im} := fun z hz ↦ by
    have := (γ • (⟨z, hz⟩ : ℍ)).im_pos
    rwa [← UpperHalfPlane.coe_im, coe_SL2R_smul] at this
  refine (hg.comp hγ hmaps).congr fun z hz ↦ ?_
  simp only [Function.comp_apply]
  congr 1
  apply UpperHalfPlane.ext
  rw [ofComplex_of_im_pos (hmaps hz), ofComplex_apply_of_im_pos hz, coe_SL2R_smul]

variable (U) in
theorem holH_weierstrassP_ψ : HolH fun τ ↦ L.weierstrassP (U.ψ τ) := by
  intro z hz
  have h1 : DifferentiableAt ℂ U.Ψ z :=
    U.differentiableOn.differentiableAt (isOpen_upper.mem_nhds hz)
  have h2 : DifferentiableAt ℂ L.weierstrassP (U.Ψ z) :=
    (L.analyticOnNhd_weierstrassP _ (U.notMem z hz)).differentiableAt
  refine (h2.comp z h1).differentiableWithinAt.congr (fun w hw ↦ ?_) ?_
  · change L.weierstrassP (U.Ψ (ofComplex w : ℂ)) = L.weierstrassP (U.Ψ w)
    rw [ofComplex_of_im_pos hw]
  · change L.weierstrassP (U.Ψ (ofComplex z : ℂ)) = L.weierstrassP (U.Ψ z)
    rw [ofComplex_of_im_pos hz]

end Unif

namespace Peripheral

open Generators

variable {t : ℍ} {U : Unif (Lt t)}

/-- **Polynomially bounded `Γ̃`-invariant holomorphic functions are polynomials in `℘ ∘ ψ`.** -/
theorem eq_poly_of_bound {g : ℍ → ℂ} (hinv : Unif.PmInvariant (U := U) g) (hh : Unif.HolH g)
    {C : ℝ} {N : ℕ} (hb : ∀ τ, ‖g τ‖ ≤ C * (2 + ‖wpΨ U τ‖) ^ N) :
    ∃ p : ℂ[X], ∀ τ, g τ = p.eval (wpΨ U τ) := by
  have hC : 0 ≤ C := by
    have h := hb UpperHalfPlane.I
    have hpos : 0 < (2 + ‖wpΨ U UpperHalfPlane.I‖) ^ N := by positivity
    by_contra hC
    rw [not_le] at hC
    nlinarith [norm_nonneg (g UpperHalfPlane.I)]
  have hlim := Heights.tendsto_sq_mul_weierstrassP_zero (Lt t)
  have hev : ∀ᶠ w in 𝓝[≠] (0 : ℂ), ‖w ^ 2 * (Lt t).weierstrassP w‖ < 2 :=
    hlim.norm (gt_mem_nhds (by norm_num))
  obtain ⟨ρ, hρ, hρev⟩ := Metric.mem_nhdsWithin_iff.mp hev
  suffices hbd : ∀ w : ℂ, w ≠ 0 → ‖w‖ < min ρ 1 →
      ‖w‖ ^ (2 * N) * ‖U.descend g w‖ ≤ C * 4 ^ N by
    obtain ⟨p, hp⟩ := exists_poly_weierstrassP N (U.descend g)
      (U.differentiableOn_descend hinv hh) (fun w l hl ↦ Unif.descend_add hinv w hl)
      (Unif.descend_neg hinv) ⟨min ρ 1, lt_min hρ one_pos, C * 4 ^ N, hbd⟩
    refine ⟨p, fun τ ↦ ?_⟩
    rw [← Unif.descend_ψ hinv τ]
    exact hp _ (U.ψ_notMem τ)
  intro w hw0 hw
  · have hwρ : ‖w‖ < ρ := hw.trans_le (min_le_left _ _)
    have hw1 : ‖w‖ < 1 := hw.trans_le (min_le_right _ _)
    by_cases hL : w ∈ (Lt t).lattice
    · simp only [Unif.descend, hL, not_true_eq_false, dite_false, norm_zero, mul_zero]
      positivity
    · obtain ⟨τ, hτ⟩ := U.surj w hL
      have hτ' : U.ψ τ = w := hτ
      rw [show U.descend g w = g τ from hτ' ▸ Unif.descend_ψ hinv τ]
      have h2 : ‖w ^ 2 * (Lt t).weierstrassP w‖ < 2 :=
        hρev ⟨mem_ball_zero_iff.mpr hwρ, mem_compl_singleton_iff.mpr hw0⟩
      have hwp : wpΨ U τ = (Lt t).weierstrassP w := by rw [wpΨ, hτ']
      have key : ‖w‖ ^ 2 * (2 + ‖wpΨ U τ‖) ≤ 4 := by
        rw [hwp]
        rw [norm_mul, norm_pow] at h2
        have : ‖w‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg w) hw1.le
        nlinarith
      calc ‖w‖ ^ (2 * N) * ‖g τ‖ ≤ ‖w‖ ^ (2 * N) * (C * (2 + ‖wpΨ U τ‖) ^ N) :=
            mul_le_mul_of_nonneg_left (hb τ) (by positivity)
        _ = C * (‖w‖ ^ 2 * (2 + ‖wpΨ U τ‖)) ^ N := by rw [mul_pow, pow_mul]; ring
        _ ≤ C * 4 ^ N := by
            gcongr

/-- **Polynomial growth of `℘ ∘ ψ ∘ σ`** for `σ` in the commensurator. -/
theorem exists_poly_bound_smul {σ : SL(2, ℝ)}
    (hσ : σ ∈ Subgroup.Commensurable.commensurator U.pmDeck) :
    ∃ C : ℝ, ∃ N : ℕ, ∀ τ : ℍ, ‖wpΨ U (σ • τ)‖ ≤ C * (2 + ‖wpΨ U τ‖) ^ N := by
  rw [U.commensurator_pmDeck] at hσ
  obtain ⟨c, hc⟩ := exists_depth_smul_le hσ
  obtain ⟨A, B, hA, hAB⟩ := exists_growth (U := U)
  set N := ⌈A * Real.exp c * A⌉₊
  refine ⟨Real.exp (A * Real.exp c * B + B), N, fun τ ↦ ?_⟩
  set w := ‖wpΨ U τ‖
  set v := ‖wpΨ U (σ • τ)‖
  have hl : 0 ≤ Real.log (2 + w) := Real.log_nonneg (by linarith [norm_nonneg (wpΨ U τ)])
  have h1 := (hAB (σ • τ)).1
  have h2 := (hAB τ).2
  have h3 : Real.exp (depth U (σ • τ)) ≤ Real.exp c * Real.exp (depth U τ) := by
    rw [← Real.exp_add, add_comm]; exact Real.exp_le_exp.mpr (hc τ)
  have hN : A * Real.exp c * A ≤ N := Nat.le_ceil _
  have h4 : Real.log (1 + v) ≤ N * Real.log (2 + w) + (A * Real.exp c * B + B) := by
    have hec := Real.exp_pos c
    have : A * Real.exp (depth U (σ • τ)) ≤ A * Real.exp c * (A * Real.log (2 + w) + B) := by
      calc A * Real.exp (depth U (σ • τ)) ≤ A * (Real.exp c * Real.exp (depth U τ)) :=
            mul_le_mul_of_nonneg_left h3 hA
        _ ≤ A * (Real.exp c * (A * Real.log (2 + w) + B)) := by gcongr
        _ = _ := by ring
    nlinarith
  have hv : 0 < 1 + v := by positivity
  calc v ≤ 1 + v := by linarith
    _ = Real.exp (Real.log (1 + v)) := (Real.exp_log hv).symm
    _ ≤ Real.exp (N * Real.log (2 + w) + (A * Real.exp c * B + B)) := Real.exp_le_exp.mpr h4
    _ = Real.exp (A * Real.exp c * B + B) * (2 + w) ^ N := by
        rw [Real.exp_add, mul_comm, ← Real.log_pow, Real.exp_log (by positivity)]

theorem le_commensurator {G : Type*} [Group G] (Γ : Subgroup G) :
    Γ ≤ Subgroup.Commensurable.commensurator Γ := by
  intro g hg
  rw [Subgroup.Commensurable.commensurator_mem_iff]
  have : ConjAct.toConjAct g • Γ = Γ := by
    ext x
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, ConjAct.smul_def,
      ConjAct.ofConjAct_toConjAct, inv_inv]
    constructor
    · intro h
      have := Γ.mul_mem (Γ.mul_mem hg h) (Γ.inv_mem hg)
      simpa [mul_assoc] using this
    · intro h
      exact Γ.mul_mem (Γ.mul_mem (Γ.inv_mem hg) h) hg
  rw [this]

/-- **Key lemma K2**: for `δ` in the commensurator of `Γ̃`, `℘ ∘ ψ ∘ δ` is integral over
`ℂ[℘ ∘ ψ]`. -/
theorem exists_monic_wpΨ_smul {δ : SL(2, ℝ)}
    (hδ : δ ∈ Subgroup.Commensurable.commensurator U.pmDeck) :
    ∃ P : ℂ[X][X], P.Monic ∧
      ∀ τ : ℍ, (P.map (evalRingHom (wpΨ U τ))).eval (wpΨ U (δ • τ)) = 0 := by
  classical
  set Γ := U.pmDeck
  set K := Γ ⊓ Γ.comap (MulAut.conj δ).toMonoidHom
  have hK := relIndex_ne_zero_of_mem_commensurator hδ
  haveI : (K.subgroupOf Γ).FiniteIndex := ⟨hK⟩
  haveI : Finite (Γ ⧸ K.subgroupOf Γ) := Subgroup.finite_quotient_of_finiteIndex
  letI := Fintype.ofFinite (Γ ⧸ K.subgroupOf Γ)
  have hinvΓ : ∀ γ ∈ Γ, ∀ τ, wpΨ U (γ • τ) = wpΨ U τ := fun γ hγ τ ↦ U.wp_ψ_smul_pm hγ τ
  let f : Γ ⧸ K.subgroupOf Γ → ℍ → ℂ := fun q τ ↦
    wpΨ U ((δ * ((q.out : Γ) : SL(2, ℝ))⁻¹) • τ)
  have hf : ∀ x : Γ, ∀ τ, f (QuotientGroup.mk x) τ = wpΨ U (δ • ((x : SL(2, ℝ))⁻¹ • τ)) := by
    intro x τ
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (K.subgroupOf Γ) x
    have hmem : ((h : Γ) : SL(2, ℝ)) ∈ K := Subgroup.mem_subgroupOf.mp h.2
    have hconj : δ * ((h : Γ) : SL(2, ℝ)) * δ⁻¹ ∈ Γ := hmem.2
    simp only [f, hh, Subgroup.coe_mul, mul_inv_rev]
    have e : (δ * ((((h : Γ) : SL(2, ℝ)))⁻¹ * ((x : SL(2, ℝ)))⁻¹)) • τ =
        (δ * ((h : Γ) : SL(2, ℝ)) * δ⁻¹)⁻¹ • (δ • ((x : SL(2, ℝ))⁻¹ • τ)) := by
      rw [← mul_smul, ← mul_smul]; congr 1; group
    rw [e, hinvΓ _ (Γ.inv_mem hconj)]
  -- the polynomial `∏_q (X - f_q)`
  set P₀ : ℍ → ℂ[X] := fun τ ↦ ∏ q, (X - C (f q τ))
  have hP₀inv : ∀ γ ∈ Γ, ∀ τ, P₀ (γ • τ) = P₀ τ := by
    intro γ hγ τ
    set g : Γ := ⟨γ, hγ⟩
    have hfq : ∀ q, f q (γ • τ) = f (g⁻¹ • q) τ := by
      intro q
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      rw [MulAction.Quotient.smul_mk, hf, hf, smul_eq_mul, Subgroup.coe_mul, Subgroup.coe_inv,
        mul_inv_rev, inv_inv, mul_smul]
    simp only [P₀, hfq]
    exact Fintype.prod_equiv (MulAction.toPerm g⁻¹) _ _ fun q ↦ rfl
  have hσ : ∀ q : Γ ⧸ K.subgroupOf Γ, δ * ((q.out : Γ) : SL(2, ℝ))⁻¹ ∈
      Subgroup.Commensurable.commensurator Γ := fun q ↦
    Subgroup.mul_mem _ hδ (Subgroup.inv_mem _ (le_commensurator Γ (q.out : Γ).2))
  choose Cq Nq hq using fun q ↦ exists_poly_bound_smul (U := U) (hσ q)
  -- each coefficient is a polynomial in `℘ ∘ ψ`
  have hcoeff : ∀ k : ℕ, ∃ p : ℂ[X], ∀ τ, (P₀ τ).coeff k = p.eval (wpΨ U τ) := by
    intro k
    refine eq_poly_of_bound (U := U) (fun γ hγ τ ↦ by rw [hP₀inv γ hγ τ]) ?_
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
      change 1 + ‖wpΨ U ((δ * ((q.out : Γ) : SL(2, ℝ))⁻¹) • τ)‖ ≤ _
      nlinarith
  choose p hp using hcoeff
  set n := Fintype.card (Γ ⧸ K.subgroupOf Γ)
  refine ⟨X ^ n + ∑ i : Fin n, C (p i) * X ^ (i : ℕ), monic_X_pow_add (degree_sum_fin_lt _),
    fun τ ↦ ?_⟩
  have hmonic : (P₀ τ).Monic := monic_prod_X_sub_C _ _
  have hdeg : (P₀ τ).natDegree = n := by
    simp only [P₀, natDegree_finsetProd_X_sub_C_eq_card, Finset.card_univ, n]
  have hroot : (P₀ τ).eval (wpΨ U (δ • τ)) = 0 := by
    simp only [P₀, eval_prod, eval_sub, eval_X, eval_C]
    refine Finset.prod_eq_zero (Finset.mem_univ (QuotientGroup.mk 1)) ?_
    rw [hf, Subgroup.coe_one, inv_one, one_smul, sub_self]
  rw [hmonic.as_sum, hdeg, Finset.sum_range] at hroot
  simp only [Polynomial.map_add, Polynomial.map_pow, map_X, Polynomial.map_sum,
    Polynomial.map_mul, map_C, coe_evalRingHom, eval_add, eval_pow, eval_X, eval_finsetSum,
    eval_mul, eval_C] at hroot ⊢
  rw [← hroot]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [hp]

end Peripheral

end Uniformization
