/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Uniformization.FEtCurve
import Oka.Uniformization.R3

/-!
# Invariant holomorphic functions of polynomial growth on the explicit uniformisation

For `W = C • E_t` and the explicit uniformisation `π = uniformizationMap t C` (with deck group
`Γ = ⟨A, B⟩`), every `Γ`-invariant holomorphic function on `ℍ` of polynomial growth in the
`x`-coordinate lies in the image of `ℂ[W]` (`FEt.exists_coord_of_invariant`).

Write `P = ℘ ∘ ψ`, `D = ℘' ∘ ψ`, and `ι` for the lift of `z ↦ -z`. The even part `g + g ∘ ι` and
`(g - g ∘ ι) D` are invariant under `Γ̃ = pmDeck`, hence polynomials in `P`
(`Peripheral.eq_poly_of_bound`); the second vanishes at the roots of the cubic, so it is divisible
by `4P³ - g₂P - g₃ = D²`.
-/

open Complex Metric Set Filter Topology Polynomial
open UpperHalfPlane hiding I I_re I_im
open scoped MatrixGroups Polynomial.Bivariate

namespace Uniformization

namespace FEt

open Generators Peripheral

variable {t : ℍ} {C : WeierstrassCurve.VariableChange ℂ} {W : WeierstrassCurve ℂ}

/-- The explicit uniformisation is a uniformisation. -/
theorem isUniformization_map (hC : C • Heights.latticeWeierstrassCurve t = W) :
    IsUniformization W (A (unifOf (Lt t))) (B (unifOf (Lt t))) (uniformizationMap t C) := by
  obtain ⟨-, -, h3, h4, h5, h6⟩ := uniformization_of_variableChange t W C hC
  exact ⟨h3, h4, h5, h6⟩

/-- `℘' ∘ ψ`. -/
noncomputable def derΨ (U : Unif (Lt t)) (τ : ℍ) : ℂ := (Lt t).derivWeierstrassP (U.ψ τ)

theorem uniformizationMap_fst (τ : ℍ) :
    (uniformizationMap t C τ).1 = (C.u⁻¹ : ℂ) ^ 2 * (wpΨ (unifOf (Lt t)) τ - C.r) := rfl

theorem uniformizationMap_snd (τ : ℍ) :
    (uniformizationMap t C τ).2 = (C.u⁻¹ : ℂ) ^ 3 * (derΨ (unifOf (Lt t)) τ / 2 -
      C.s * (wpΨ (unifOf (Lt t)) τ - C.r) - C.t) := rfl

theorem wpΨ_eq (τ : ℍ) :
    wpΨ (unifOf (Lt t)) τ = (C.u : ℂ) ^ 2 * (uniformizationMap t C τ).1 + C.r := by
  rw [uniformizationMap_fst]
  have hu : (C.u : ℂ) ≠ 0 := C.u.ne_zero
  field_simp
  ring

theorem derΨ_eq (τ : ℍ) :
    derΨ (unifOf (Lt t)) τ = 2 * ((C.u : ℂ) ^ 3 * (uniformizationMap t C τ).2 +
      C.s * (C.u : ℂ) ^ 2 * (uniformizationMap t C τ).1 + C.t) := by
  rw [uniformizationMap_snd, uniformizationMap_fst]
  have hu : (C.u : ℂ) ≠ 0 := C.u.ne_zero
  field_simp
  ring

theorem holH_derΨ (U : Unif (Lt t)) : Unif.HolH (derΨ U) := by
  intro z hz
  have h1 : DifferentiableAt ℂ U.Ψ z :=
    U.differentiableOn.differentiableAt (isOpen_upper.mem_nhds hz)
  have h2 : DifferentiableAt ℂ (Lt t).derivWeierstrassP (U.Ψ z) :=
    ((Lt t).analyticOnNhd_derivWeierstrassP _ (U.notMem z hz)).differentiableAt
  refine (h2.comp z h1).differentiableWithinAt.congr (fun w hw ↦ ?_) ?_
  · change (Lt t).derivWeierstrassP (U.Ψ (ofComplex w : ℂ)) = (Lt t).derivWeierstrassP (U.Ψ w)
    rw [ofComplex_of_im_pos hw]
  · change (Lt t).derivWeierstrassP (U.Ψ (ofComplex z : ℂ)) = (Lt t).derivWeierstrassP (U.Ψ z)
    rw [ofComplex_of_im_pos hz]

/-- Elements of `Γ̃` act on `(P, D)` by `(P, D) ↦ (P, ε D)`. -/
theorem wpΨ_derΨ_smul (U : Unif (Lt t)) {γ : SL(2, ℝ)} {ε l : ℂ} (hε : ε = 1 ∨ ε = -1)
    (hl : l ∈ (Lt t).lattice) (hγ : ∀ τ, U.ψ (γ • τ) = ε * U.ψ τ + l) (τ : ℍ) :
    wpΨ U (γ • τ) = wpΨ U τ ∧ derΨ U (γ • τ) = ε * derΨ U τ := by
  simp only [wpΨ, derΨ, hγ τ]
  rw [(Lt t).weierstrassP_add_coe _ ⟨l, hl⟩, (Lt t).derivWeierstrassP_add_coe _ ⟨l, hl⟩]
  rcases hε with rfl | rfl
  · simp
  · simp [(Lt t).weierstrassP_neg, (Lt t).derivWeierstrassP_neg]

theorem PolyBdd.of_le {h₁ h₂ : ℍ → ℂ} {u : ℍ → ℝ} (hu : PolyBdd h₁ u) {K : ℝ}
    (h : ∀ τ, 2 + ‖h₁ τ‖ ≤ K * (2 + ‖h₂ τ‖)) : PolyBdd h₂ u := by
  obtain ⟨c, N, hc⟩ := hu
  refine ⟨|c| * K ^ N, N, fun τ ↦ ?_⟩
  have h0 : 0 ≤ 2 + ‖h₁ τ‖ := by positivity
  calc u τ ≤ c * (2 + ‖h₁ τ‖) ^ N := hc τ
    _ ≤ |c| * (2 + ‖h₁ τ‖) ^ N := mul_le_mul_of_nonneg_right (le_abs_self c) (by positivity)
    _ ≤ |c| * (K * (2 + ‖h₂ τ‖)) ^ N :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 (h τ) N) (abs_nonneg c)
    _ = |c| * K ^ N * (2 + ‖h₂ τ‖) ^ N := by rw [mul_pow]; ring

theorem aeval_pi_apply (f : ℍ → ℂ) (p : ℂ[X]) (τ : ℍ) : (aeval f p) τ = p.eval (f τ) := by
  have := Polynomial.aeval_algHom_apply (Pi.evalAlgHom ℂ (fun _ : ℍ ↦ ℂ) τ) f p
  rw [Pi.evalAlgHom_apply, Pi.evalAlgHom_apply, coe_aeval_eq_eval] at this
  exact this.symm

/-- **Invariant holomorphic functions of polynomial growth are regular functions on `W`.** -/
theorem exists_coord_of_invariant (hC : C • Heights.latticeWeierstrassCurve t = W)
    {g : ℍ → ℂ} (hg : Unif.HolH g)
    (hinv : ∀ γ ∈ Subgroup.closure {A (unifOf (Lt t)), B (unifOf (Lt t))}, ∀ τ, g (γ • τ) = g τ)
    (hb : PolyBdd (fun τ ↦ (uniformizationMap t C τ).1) fun τ ↦ ‖g τ‖) :
    ∃ a : W.toAffine.CoordinateRing, ∀ τ, coordFun W (fun τ ↦ (uniformizationMap t C τ).1)
      (fun τ ↦ (uniformizationMap t C τ).2) (isUniformization_map hC).mem a τ = g τ := by
  classical
  set U := unifOf (Lt t)
  have h := isUniformization_map hC
  set P := wpΨ U
  set D := derΨ U
  set x : ℍ → ℂ := fun τ ↦ (uniformizationMap t C τ).1
  have hΔ := Heights.periodPair_invariant_discriminant_ne_zero t
  -- `g` factors through `(P, D)`
  have hfib : ∀ τ₁ τ₂, P τ₁ = P τ₂ → D τ₁ = D τ₂ → g τ₁ = g τ₂ := by
    intro τ₁ τ₂ hP hD
    have hπ : uniformizationMap t C τ₁ = uniformizationMap t C τ₂ := by
      refine Prod.ext ?_ ?_
      · rw [uniformizationMap_fst, uniformizationMap_fst]; simp only [P] at hP; rw [hP]
      · rw [uniformizationMap_snd, uniformizationMap_snd]; simp only [P, D] at hP hD
        rw [hP, hD]
    obtain ⟨γ, hγ, rfl⟩ := (h.fibre τ₁ τ₂).mp hπ
    exact (hinv γ hγ τ₁).symm
  obtain ⟨ι, hιm, hιψ⟩ := U.exists_iota
  have hιPD : ∀ τ, P (ι • τ) = P τ ∧ D (ι • τ) = -D τ := fun τ ↦ by
    have := wpΨ_derΨ_smul U (Or.inr rfl) (zero_mem _) (fun τ ↦ by rw [hιψ]; ring) τ
    simpa using this
  have hγPD : ∀ γ ∈ U.pmDeck, ∀ τ, (P (γ • τ) = P τ ∧ D (γ • τ) = D τ) ∨
      (P (γ • τ) = P τ ∧ D (γ • τ) = -D τ) := by
    rintro γ ⟨ε, hε, l, hl, hγ⟩ τ
    have := wpΨ_derΨ_smul U hε hl hγ τ
    rcases hε with rfl | rfl
    · left; simpa using this
    · right; simpa using this
  -- the even and odd parts
  set gp : ℍ → ℂ := fun τ ↦ g τ + g (ι • τ)
  set gm : ℍ → ℂ := fun τ ↦ (g τ - g (ι • τ)) * D τ
  have hgpinv : Unif.PmInvariant (U := U) gp := by
    intro γ hγ τ
    rcases hγPD γ hγ τ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp only [gp]
      rw [hfib _ _ h1 h2, hfib (ι • γ • τ) (ι • τ) (by rw [(hιPD _).1, (hιPD _).1, h1])
        (by rw [(hιPD _).2, (hιPD _).2, h2])]
    · simp only [gp]
      rw [hfib (γ • τ) (ι • τ) (by rw [(hιPD _).1, h1]) (by rw [(hιPD _).2, h2]),
        hfib (ι • γ • τ) τ (by rw [(hιPD _).1, h1]) (by rw [(hιPD _).2, h2, neg_neg]), add_comm]
  have hgminv : Unif.PmInvariant (U := U) gm := by
    intro γ hγ τ
    rcases hγPD γ hγ τ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp only [gm]
      rw [hfib _ _ h1 h2, hfib (ι • γ • τ) (ι • τ) (by rw [(hιPD _).1, (hιPD _).1, h1])
        (by rw [(hιPD _).2, (hιPD _).2, h2]), h2]
    · simp only [gm]
      rw [hfib (γ • τ) (ι • τ) (by rw [(hιPD _).1, h1]) (by rw [(hιPD _).2, h2]),
        hfib (ι • γ • τ) τ (by rw [(hιPD _).1, h1]) (by rw [(hιPD _).2, h2, neg_neg]), h2]
      ring
  -- bounds in terms of `P`
  have hxP : ∀ τ, 2 + ‖x τ‖ ≤ (1 + ‖(C.u⁻¹ : ℂ) ^ 2‖ * (1 + ‖C.r‖)) * (2 + ‖P τ‖) := by
    intro τ
    have e : x τ = (C.u⁻¹ : ℂ) ^ 2 * (P τ - C.r) := uniformizationMap_fst τ
    rw [e, norm_mul]
    have h0 := norm_nonneg ((C.u⁻¹ : ℂ) ^ 2)
    have h1 := norm_nonneg (P τ)
    have h2 := norm_nonneg C.r
    have h3 : ‖P τ - C.r‖ ≤ (1 + ‖C.r‖) * (2 + ‖P τ‖) := by
      have := norm_sub_le (P τ) C.r
      nlinarith
    have h4 := mul_le_mul_of_nonneg_left h3 h0
    nlinarith
  have hxι : ∀ τ, x (ι • τ) = x τ := fun τ ↦ by
    simp only [x]; rw [uniformizationMap_fst, uniformizationMap_fst]
    exact congrArg (fun w ↦ (C.u⁻¹ : ℂ) ^ 2 * (w - C.r)) (hιPD τ).1
  have hbι : PolyBdd x fun τ ↦ ‖g (ι • τ)‖ := by
    obtain ⟨c, N, hc⟩ := hb
    exact ⟨c, N, fun τ ↦ by have := hc (ι • τ); rwa [hxι] at this⟩
  have hD : PolyBdd P fun τ ↦ ‖D τ‖ := by
    refine ((PolyBdd.const 1).add (PolyBdd.poly_eval (h₀ := P) (cubic (Lt t)))).mono
      fun τ ↦ ?_
    have hsq : D τ ^ 2 = (cubic (Lt t)).eval (P τ) := by
      rw [cubic_eval]; exact (Lt t).derivWeierstrassP_sq _ (U.ψ_notMem τ)
    have : ‖D τ‖ ^ 2 = ‖(cubic (Lt t)).eval (P τ)‖ := by rw [← hsq, norm_pow]
    simp only [Pi.add_apply]
    nlinarith [norm_nonneg (D τ)]
  have hbP : PolyBdd P fun τ ↦ ‖g τ‖ := hb.of_le hxP
  have hbιP : PolyBdd P fun τ ↦ ‖g (ι • τ)‖ := hbι.of_le hxP
  obtain ⟨Pp, hPp⟩ : ∃ Pp : ℂ[X], ∀ τ, gp τ = Pp.eval (P τ) := by
    have hgpb : PolyBdd P fun τ ↦ ‖gp τ‖ :=
      (hbP.add hbιP).mono fun τ ↦ (norm_add_le (g τ) (g (ι • τ)))
    obtain ⟨c, N, hc⟩ := hgpb
    exact eq_poly_of_bound hgpinv (DifferentiableOn.add hg (hg.comp_smul ι)) hc
  obtain ⟨Pm, hPm⟩ : ∃ Pm : ℂ[X], ∀ τ, gm τ = Pm.eval (P τ) := by
    have hgmb : PolyBdd P fun τ ↦ ‖gm τ‖ := ((hbP.add hbιP).mul hD
      (fun τ ↦ add_nonneg (norm_nonneg _) (norm_nonneg _)) (fun τ ↦ norm_nonneg _)).mono
        fun τ ↦ by
          simp only [gm, norm_mul, Pi.mul_apply, Pi.add_apply]
          exact mul_le_mul_of_nonneg_right (norm_sub_le _ _) (norm_nonneg _)
    obtain ⟨c, N, hc⟩ := hgmb
    exact eq_poly_of_bound hgminv
      (DifferentiableOn.mul (DifferentiableOn.sub hg (hg.comp_smul ι)) (holH_derΨ U)) hc
  -- `Pm` is divisible by the cubic
  have hsq : ∀ τ, D τ ^ 2 = (cubic (Lt t)).eval (P τ) := fun τ ↦ by
    rw [cubic_eval]; exact (Lt t).derivWeierstrassP_sq _ (U.ψ_notMem τ)
  have hroots : ∀ e ∈ E₂ (Lt t), Pm.IsRoot e := by
    intro e he
    obtain ⟨τ, hτ⟩ := wpΨ_surjective U e
    have hD0 : D τ = 0 := by
      have h1 := hsq τ
      rw [show P τ = e from hτ, cubic_eval, (mem_E₂ _).mp he] at h1
      exact pow_eq_zero_iff (two_ne_zero) |>.mp h1
    have := hPm τ
    simp only [gm, hD0, mul_zero] at this
    rw [IsRoot, ← show P τ = e from hτ]; exact this.symm
  have hdvd : cubic (Lt t) ∣ Pm := by
    by_cases hPm0 : Pm = 0
    · rw [hPm0]; exact dvd_zero _
    have hdeg : (cubic (Lt t)).natDegree = 3 := by rw [cubic]; compute_degree!
    have hcard : Multiset.card (cubic (Lt t)).roots = (cubic (Lt t)).natDegree := by
      rw [IsAlgClosed.card_roots_eq_natDegree]
    have hnd : (cubic (Lt t)).roots.Nodup := by
      rw [← Multiset.toFinset_card_eq_card_iff_nodup, hcard, hdeg]
      exact card_E₂ hΔ
    have hle : (cubic (Lt t)).roots ≤ Pm.roots :=
      (Multiset.le_iff_subset hnd).mpr fun e he ↦ (mem_roots hPm0).mpr
        (hroots e (Multiset.mem_toFinset.mpr he))
    have hprod := (Multiset.prod_X_sub_C_dvd_iff_le_roots hPm0 _).mpr hle
    rw [← C_leadingCoeff_mul_prod_multiset_X_sub_C hcard, C_mul_dvd
      (leadingCoeff_ne_zero.mpr (cubic_ne_zero _))]
    exact hprod
  obtain ⟨R, hR⟩ := hdvd
  -- the odd part is `D R(P)`
  obtain ⟨w₁, hw₁⟩ := Infinite.exists_notMem_finset (E₂ (Lt t))
  obtain ⟨τ₁, hτ₁⟩ := wpΨ_surjective U w₁
  have hD1 : D τ₁ ≠ 0 := fun h0 ↦
    hw₁ (hτ₁ ▸ (derivWeierstrassP_eq_zero_iff (U.ψ_notMem τ₁)).mp h0)
  have hodd : ∀ τ, g τ - g (ι • τ) = D τ * R.eval (P τ) := by
    have hF : Unif.HolH fun τ ↦ g τ - g (ι • τ) - D τ * R.eval (P τ) :=
      DifferentiableOn.sub (DifferentiableOn.sub hg (hg.comp_smul ι))
        (DifferentiableOn.mul (holH_derΨ U) (holH_poly_wpΨ U R))
    intro τ
    refine sub_eq_zero.mp (Unif.HolH.eq_zero_of_mul hF (holH_derΨ U) (fun σ ↦ ?_) hD1 τ)
    have h1 := hPm σ
    have h2 := hsq σ
    simp only [gm] at h1
    rw [hR, eval_mul] at h1
    linear_combination h1 - R.eval (P σ) * h2
  -- the regular function
  set X' : W.toAffine.CoordinateRing := (C.u : ℂ) ^ 2 • xA W + algebraMap ℂ _ C.r
  set Y' : W.toAffine.CoordinateRing :=
    (2 : ℂ) • ((C.u : ℂ) ^ 3 • yA W + (C.s * (C.u : ℂ) ^ 2) • xA W + algebraMap ℂ _ C.t)
  refine ⟨(1 / 2 : ℂ) • (aeval X' Pp + Y' * aeval X' R), fun τ ↦ ?_⟩
  set cf := coordFun W (fun τ ↦ (uniformizationMap t C τ).1)
    (fun τ ↦ (uniformizationMap t C τ).2) h.mem
  have hX' : cf X' τ = P τ := by
    simp only [X', cf, map_add, map_smul, AlgHom.commutes, Pi.add_apply, Pi.smul_apply,
      coordFun_xA, smul_eq_mul, Pi.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    exact (wpΨ_eq τ).symm
  have hY' : cf Y' τ = D τ := by
    simp only [Y', cf, map_add, map_smul, AlgHom.commutes, Pi.add_apply, Pi.smul_apply,
      coordFun_xA, coordFun_yA, smul_eq_mul, Pi.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply]
    exact (derΨ_eq (C := C) τ).symm
  have hA : ∀ p : ℂ[X], cf (aeval X' p) τ = p.eval (P τ) := fun p ↦ by
    rw [← Polynomial.aeval_algHom_apply, aeval_pi_apply, hX']
  simp only [map_smul, map_add, map_mul, Pi.smul_apply, Pi.add_apply, Pi.mul_apply, hA, hY',
    smul_eq_mul]
  rw [← hPp τ, ← hodd τ]
  simp only [gp]
  ring

end FEt

end Uniformization
