/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Uniformization.HalfPlaneAut
import Oka.Uniformization.LatticeComplement

/-!
# The deck group of `ℍ → ℂ ∖ Λ → (ℂ ∖ Λ) / Λ`

Let `ψ : ℍ → ℂ ∖ Λ` be the holomorphic universal covering of `PeriodPair.exists_uniformization`
(packaged as `Uniformization.Unif`). Every translation by a period lifts through `ψ` to a
holomorphic bijection of `ℍ`, which is a Möbius map (`exists_SL2R_eq_of_holomorphic`). So

`Γ = {g ∈ SL(2, ℝ) | ∃ l ∈ Λ, ∀ τ, ψ (g • τ) = ψ τ + l}`

is a subgroup of `SL(2, ℝ)` whose orbits are exactly the fibres of `ψ` modulo `Λ`
(`Unif.exists_mem_deckGroup`), and `Γ` acts freely modulo `±1` (`Unif.eq_one_or_neg_one`).
-/

open Complex Metric Set Filter Topology
open UpperHalfPlane hiding I I_re I_im
open scoped MatrixGroups

namespace Uniformization

/-- A holomorphic universal covering `ℍ → ℂ ∖ Λ` (as a function on `ℂ`, restricted to `ℍ`). -/
structure Unif (L : PeriodPair) where
  /-- The covering map, as a function on `ℂ`. -/
  Ψ : ℂ → ℂ
  covering : IsCoveringMapOn (fun τ : ℍ ↦ Ψ τ) (L.lattice : Set ℂ)ᶜ
  notMem : ∀ z : ℂ, 0 < z.im → Ψ z ∉ L.lattice
  differentiableOn : DifferentiableOn ℂ Ψ {z | 0 < z.im}
  deriv_ne_zero : ∀ z : ℂ, 0 < z.im → deriv Ψ z ≠ 0
  surj : ∀ w ∉ L.lattice, ∃ τ : ℍ, Ψ τ = w

/-- The uniformisation of `ℂ ∖ Λ` chosen by `PeriodPair.exists_uniformization`. -/
noncomputable def unifOf (L : PeriodPair) : Unif L :=
  let h := PeriodPair.exists_uniformization L
  ⟨h.choose, h.choose_spec.1, h.choose_spec.2.1, h.choose_spec.2.2.1, h.choose_spec.2.2.2.1,
    h.choose_spec.2.2.2.2⟩

namespace Unif

variable {L : PeriodPair} (U : Unif L)

/-- The covering `ψ : ℍ → ℂ ∖ Λ`. -/
def ψ (τ : ℍ) : ℂ := U.Ψ τ

theorem ψ_notMem (τ : ℍ) : U.ψ τ ∉ L.lattice := U.notMem τ τ.im_pos

theorem continuous_ψ : Continuous U.ψ :=
  U.differentiableOn.continuousOn.comp_continuous continuous_coe fun τ ↦ τ.im_pos

theorem add_notMem {z l : ℂ} (hz : z ∉ L.lattice) (hl : l ∈ L.lattice) : z + l ∉ L.lattice :=
  fun h ↦ hz (by simpa using sub_mem h hl)

/-- Uniqueness of lifts through `ψ` of maps out of `ℍ`. -/
theorem eq_of_comp_eq {A B : ℍ → ℍ} (hA : Continuous A) (hB : Continuous B)
    (h : ∀ τ, U.ψ (A τ) = U.ψ (B τ)) {τ₀ : ℍ} (h₀ : A τ₀ = B τ₀) : A = B := by
  obtain ⟨F, -, hF⟩ := U.covering.existsUnique_continuousMap_lifts ⟨fun τ ↦ U.ψ (A τ),
    U.continuous_ψ.comp hA⟩ (a₀ := τ₀) (e₀ := A τ₀) rfl fun τ ↦ U.ψ_notMem (A τ)
  have h1 := hF ⟨A, hA⟩ ⟨rfl, rfl⟩
  have h2 := hF ⟨B, hB⟩ ⟨h₀.symm, by funext τ; exact (h τ).symm⟩
  have := h2.trans h1.symm
  funext τ
  exact (congrArg (fun F : C(ℍ, ℍ) ↦ F τ) this).symm

/-- Translations by periods lift through `ψ`. -/
theorem exists_lift {l : ℂ} (hl : l ∈ L.lattice) (τ τ' : ℍ) (h : U.ψ τ' = U.ψ τ + l) :
    ∃ T : ℍ → ℍ, Continuous T ∧ T τ = τ' ∧ ∀ σ, U.ψ (T σ) = U.ψ σ + l := by
  obtain ⟨F, ⟨hF0, hF⟩, -⟩ := U.covering.existsUnique_continuousMap_lifts ⟨fun σ ↦ U.ψ σ + l,
    U.continuous_ψ.add continuous_const⟩ (a₀ := τ) (e₀ := τ') h
    fun σ ↦ add_notMem (U.ψ_notMem σ) hl
  exact ⟨F, F.continuous, hF0, fun σ ↦ congrFun hF σ⟩

theorem hasStrictDerivAt_Ψ {z : ℂ} (hz : 0 < z.im) : HasStrictDerivAt U.Ψ (deriv U.Ψ z) z :=
  (U.differentiableOn.analyticAt (isOpen_upper.mem_nhds hz)).hasStrictDerivAt

/-- A continuous lift of a translation is holomorphic. -/
theorem holomorphicH_of_lift {T : ℍ → ℍ} (hT : Continuous T) {l : ℂ}
    (h : ∀ σ, U.ψ (T σ) = U.ψ σ + l) : HolomorphicH T := by
  intro z hz
  have hz' : ofComplex z = ⟨z, hz⟩ := ofComplex_apply_of_im_pos hz
  refine (differentiableAt_of_comp_eq (f := U.Ψ) (g := fun w ↦ U.Ψ w + l)
    (U.hasStrictDerivAt_Ψ (T (ofComplex z)).im_pos) (U.deriv_ne_zero _ (T _).im_pos) ?_ ?_
    ?_).differentiableWithinAt
  · exact (continuous_coe.comp hT).continuousAt.comp
      (ofComplex.continuousOn.continuousAt (ofComplex.open_source.mem_nhds (by
        change z ∈ (isOpenEmbedding_coe.toOpenPartialHomeomorph _).target
        simp only [IsOpenEmbedding.toOpenPartialHomeomorph_target]
        exact ⟨⟨z, hz⟩, rfl⟩)))
  · filter_upwards [isOpen_upper.mem_nhds hz] with w hw
    have := h (ofComplex w)
    simp only [ψ] at this
    rw [this, ofComplex_of_im_pos hw]
  · exact ((U.differentiableOn.differentiableAt (isOpen_upper.mem_nhds hz)).add_const l)

/-- The deck group `Γ ⊆ SL(2, ℝ)` of `ℍ → ℂ ∖ Λ → (ℂ ∖ Λ)/Λ`. -/
def deckGroup : Subgroup SL(2, ℝ) where
  carrier := {g | ∃ l ∈ L.lattice, ∀ τ, U.ψ (g • τ) = U.ψ τ + l}
  one_mem' := ⟨0, zero_mem _, fun τ ↦ by simp⟩
  mul_mem' := by
    rintro g h ⟨l, hl, hg⟩ ⟨m, hm, hh⟩
    exact ⟨m + l, add_mem hm hl, fun τ ↦ by rw [mul_smul, hg, hh, add_assoc]⟩
  inv_mem' := by
    rintro g ⟨l, hl, hg⟩
    exact ⟨-l, neg_mem hl, fun τ ↦ by
      have := hg (g⁻¹ • τ)
      rw [smul_inv_smul] at this
      rw [this]; ring⟩

theorem mem_deckGroup {g : SL(2, ℝ)} :
    g ∈ U.deckGroup ↔ ∃ l ∈ L.lattice, ∀ τ, U.ψ (g • τ) = U.ψ τ + l := Iff.rfl

/-- **Transitivity on fibres.** If `ψ τ' - ψ τ` is a period, then `τ' = g • τ` for some `g ∈ Γ`. -/
theorem exists_mem_deckGroup {τ τ' : ℍ} (h : U.ψ τ' - U.ψ τ ∈ L.lattice) :
    ∃ g ∈ U.deckGroup, g • τ = τ' := by
  set l := U.ψ τ' - U.ψ τ
  obtain ⟨T, hTc, hTτ, hT⟩ := U.exists_lift h τ τ' (by ring)
  obtain ⟨S, hSc, hSτ, hS⟩ := U.exists_lift (neg_mem h) τ' τ (by ring)
  have hTS : T ∘ S = id := U.eq_of_comp_eq (hTc.comp hSc) continuous_id
    (fun σ ↦ by simp [hT, hS]) (τ₀ := τ') (by simp [hSτ, hTτ])
  have hST : S ∘ T = id := U.eq_of_comp_eq (hSc.comp hTc) continuous_id
    (fun σ ↦ by simp [hT, hS]) (τ₀ := τ) (by simp [hSτ, hTτ])
  obtain ⟨g, hg⟩ := exists_SL2R_eq_of_holomorphic (U.holomorphicH_of_lift hTc hT)
    (U.holomorphicH_of_lift hSc hS) (fun σ ↦ congrFun hTS σ) (fun σ ↦ congrFun hST σ)
  refine ⟨g, ⟨l, h, fun σ ↦ by rw [← hg, hT]⟩, by rw [← hg, hTτ]⟩

theorem smul_mem_iff {g : SL(2, ℝ)} (hg : g ∈ U.deckGroup) (τ : ℍ) :
    U.ψ (g • τ) - U.ψ τ ∈ L.lattice := by
  obtain ⟨l, hl, h⟩ := hg
  rw [h]; simpa using hl

/-- An element of the deck group with a fixed point acts trivially. -/
theorem smul_eq_self_of_fixed {g : SL(2, ℝ)} (hg : g ∈ U.deckGroup) {τ : ℍ} (hτ : g • τ = τ) :
    ∀ σ : ℍ, g • σ = σ := by
  obtain ⟨l, hl, h⟩ := hg
  have hl0 : l = 0 := by
    have := h τ; rw [hτ] at this; linear_combination -this
  have := U.eq_of_comp_eq (A := fun σ : ℍ ↦ g • σ) (B := id) (continuous_const_smul g) continuous_id
    (fun σ ↦ by simp [h, hl0]) (τ₀ := τ) hτ
  exact fun σ ↦ congrFun this σ

/-- An element of `SL(2, ℝ)` acting trivially on `ℍ` is `±1`. -/
theorem eq_one_or_neg_one_of_forall {g : SL(2, ℝ)} (h : ∀ σ : ℍ, g • σ = σ) : g = 1 ∨ g = -1 := by
  have key : ∀ σ : ℍ, (g 1 0 : ℂ) * σ ^ 2 + (g 1 1 - g 0 0) * σ - g 0 1 = 0 := fun σ ↦ by
    have e := congrArg (fun x : ℍ ↦ (x : ℂ)) (h σ)
    simp only [coe_SL2R_smul] at e
    have hd := denom_SL2R_ne_zero g σ.im_pos
    rw [div_eq_iff hd] at e
    linear_combination -e
  have h1 := key UpperHalfPlane.I
  have h2 := key ⟨2 * Complex.I, by simp⟩
  simp only [UpperHalfPlane.coe_I] at h1 h2
  have e1 := congrArg Complex.re h1; have e2 := congrArg Complex.im h1
  have e3 := congrArg Complex.re h2
  simp only [Fin.isValue, sq, I_mul_I, mul_neg, mul_one, sub_re, add_re, neg_re, ofReal_re, mul_re,
    I_re, mul_zero, sub_im, ofReal_im, sub_self, I_im, add_zero, zero_re, add_im, neg_im, neg_zero,
    mul_im, zero_add, sub_zero, zero_im, re_ofNat, im_ofNat, zero_sub, zero_mul] at e1 e2 e3
  have hc : g 1 0 = 0 := by linarith
  have hb : g 0 1 = 0 := by linarith
  have hd : g 1 1 = g 0 0 := by linarith
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    have := g.2; rw [Matrix.det_fin_two] at this; exact this
  rw [hb, hc, hd] at hdet
  have ha : g 0 0 = 1 ∨ g 0 0 = -1 := by
    have : (g 0 0 - 1) * (g 0 0 + 1) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · left; linarith
    · right; linarith
  rcases ha with ha | ha
  · left; ext i j; fin_cases i <;> fin_cases j <;> simp [ha, hb, hc, hd]
  · right; ext i j; fin_cases i <;> fin_cases j <;> simp [ha, hb, hc, hd]

theorem eq_one_or_neg_one {g : SL(2, ℝ)} (hg : g ∈ U.deckGroup) {τ : ℍ} (hτ : g • τ = τ) :
    g = 1 ∨ g = -1 :=
  eq_one_or_neg_one_of_forall (U.smul_eq_self_of_fixed hg hτ)

end Unif

end Uniformization
