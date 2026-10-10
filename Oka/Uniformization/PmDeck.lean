/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Uniformization.Depth

/-!
# The deck group extended by the elliptic involution

For the uniformisation `ψ : ℍ → ℂ ∖ Λ` (`Uniformization.Unif`), the maps `z ↦ ± z + l` (`l ∈ Λ`)
of `ℂ ∖ Λ` lift to Möbius transformations of `ℍ`. They form the group

`Γ̃ = {g ∈ SL(2, ℝ) | ∃ ε = ±1, ∃ l ∈ Λ, ψ ∘ g = ε ψ + l}`

(`Unif.pmDeck`), which contains the deck group `Γ` with index at most `2`, contains a lift `ι`
of `z ↦ -z`, and leaves `℘ ∘ ψ` invariant. Every function on `ℍ` invariant under `Γ̃` descends
to an even `Λ`-periodic function on `ℂ ∖ Λ` (`Unif.descend`), holomorphic if the function is.
-/

open Complex Metric Set Filter Topology
open UpperHalfPlane hiding I I_re I_im
open scoped MatrixGroups Pointwise

namespace Uniformization

namespace Unif

variable {L : PeriodPair} (U : Unif L)

theorem pm_add_notMem {ε z l : ℂ} (hε : ε = 1 ∨ ε = -1) (hz : z ∉ L.lattice)
    (hl : l ∈ L.lattice) : ε * z + l ∉ L.lattice := by
  intro h
  apply hz
  rcases hε with rfl | rfl
  · simpa using sub_mem h hl
  · have := neg_mem (sub_mem h hl); simpa using this

/-- Maps `z ↦ ε z + l` lift through `ψ`. -/
theorem exists_lift_pm {ε l : ℂ} (hε : ε = 1 ∨ ε = -1) (hl : l ∈ L.lattice) (τ τ' : ℍ)
    (h : U.ψ τ' = ε * U.ψ τ + l) :
    ∃ T : ℍ → ℍ, Continuous T ∧ T τ = τ' ∧ ∀ σ, U.ψ (T σ) = ε * U.ψ σ + l := by
  obtain ⟨F, ⟨hF0, hF⟩, -⟩ := U.covering.existsUnique_continuousMap_lifts
    ⟨fun σ ↦ ε * U.ψ σ + l, (continuous_const.mul U.continuous_ψ).add continuous_const⟩
    (a₀ := τ) (e₀ := τ') h fun σ ↦ pm_add_notMem hε (U.ψ_notMem σ) hl
  exact ⟨F, F.continuous, hF0, fun σ ↦ congrFun hF σ⟩

/-- A continuous lift of `z ↦ ε z + l` is holomorphic. -/
theorem holomorphicH_of_lift_pm {T : ℍ → ℍ} (hT : Continuous T) {ε l : ℂ}
    (h : ∀ σ, U.ψ (T σ) = ε * U.ψ σ + l) : HolomorphicH T := by
  intro z hz
  refine (differentiableAt_of_comp_eq (f := U.Ψ) (g := fun w ↦ ε * U.Ψ w + l)
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
  · exact (((U.differentiableOn.differentiableAt (isOpen_upper.mem_nhds hz)).const_mul
      ε).add_const l)

/-- The deck group extended by the elliptic involution. -/
def pmDeck : Subgroup SL(2, ℝ) where
  carrier := {g | ∃ ε : ℂ, (ε = 1 ∨ ε = -1) ∧ ∃ l ∈ L.lattice, ∀ τ, U.ψ (g • τ) = ε * U.ψ τ + l}
  one_mem' := ⟨1, Or.inl rfl, 0, zero_mem _, fun τ ↦ by simp⟩
  mul_mem' := by
    rintro g h ⟨ε, hε, l, hl, hg⟩ ⟨η, hη, m, hm, hh⟩
    refine ⟨ε * η, ?_, ε * m + l, ?_, fun τ ↦ by rw [mul_smul, hg, hh]; ring⟩
    · rcases hε with rfl | rfl <;> rcases hη with rfl | rfl <;> simp
    · rcases hε with rfl | rfl
      · simpa using add_mem hm hl
      · simpa [sub_eq_add_neg, add_comm] using add_mem (neg_mem hm) hl
  inv_mem' := by
    rintro g ⟨ε, hε, l, hl, hg⟩
    refine ⟨ε, hε, -(ε * l), ?_, fun τ ↦ ?_⟩
    · rcases hε with rfl | rfl
      · simpa using neg_mem hl
      · simpa using hl
    · have := hg (g⁻¹ • τ)
      rw [smul_inv_smul] at this
      have hεε : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
      rw [this, mul_add, ← mul_assoc, hεε, one_mul]; ring

theorem deckGroup_le_pmDeck : U.deckGroup ≤ U.pmDeck := by
  rintro g ⟨l, hl, hg⟩
  exact ⟨1, Or.inl rfl, l, hl, fun τ ↦ by rw [hg, one_mul]⟩

/-- **Transitivity**: if `ψ τ' = ± ψ τ` modulo `Λ`, some element of `Γ̃` moves `τ` to `τ'`. -/
theorem exists_mem_pmDeck {ε : ℂ} (hε : ε = 1 ∨ ε = -1) {τ τ' : ℍ}
    (h : U.ψ τ' - ε * U.ψ τ ∈ L.lattice) :
    ∃ g : SL(2, ℝ), (∀ σ, U.ψ (g • σ) = ε * U.ψ σ + (U.ψ τ' - ε * U.ψ τ)) ∧ g • τ = τ' := by
  have hεε : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  obtain ⟨T, hTc, hTτ, hT⟩ := U.exists_lift_pm hε h τ τ' (by ring)
  have hl' : -(ε * (U.ψ τ' - ε * U.ψ τ)) ∈ L.lattice := by
    rcases hε with rfl | rfl
    · simpa using neg_mem h
    · simpa using h
  obtain ⟨S, hSc, hSτ, hS⟩ := U.exists_lift_pm hε hl' τ' τ (by
    linear_combination (-(U.ψ τ)) * hεε)
  have hTS : T ∘ S = id := U.eq_of_comp_eq (hTc.comp hSc) continuous_id
    (fun σ ↦ by
      simp only [Function.comp_apply, id, hT, hS]
      linear_combination (U.ψ σ - U.ψ τ' + ε * U.ψ τ) * hεε) (τ₀ := τ') (by simp [hSτ, hTτ])
  have hST : S ∘ T = id := U.eq_of_comp_eq (hSc.comp hTc) continuous_id
    (fun σ ↦ by
      simp only [Function.comp_apply, id, hT, hS]
      linear_combination (U.ψ σ) * hεε) (τ₀ := τ) (by simp [hSτ, hTτ])
  obtain ⟨g, hg⟩ := exists_SL2R_eq_of_holomorphic (U.holomorphicH_of_lift_pm hTc hT)
    (U.holomorphicH_of_lift_pm hSc hS) (fun σ ↦ congrFun hTS σ) (fun σ ↦ congrFun hST σ)
  exact ⟨g, fun σ ↦ by rw [← hg, hT], by rw [← hg, hTτ]⟩

theorem mem_pmDeck_of {g : SL(2, ℝ)} {ε l : ℂ} (hε : ε = 1 ∨ ε = -1) (hl : l ∈ L.lattice)
    (h : ∀ σ, U.ψ (g • σ) = ε * U.ψ σ + l) : g ∈ U.pmDeck := ⟨ε, hε, l, hl, h⟩

/-- A lift `ι` of `z ↦ -z`. -/
theorem exists_iota : ∃ ι ∈ U.pmDeck, ∀ τ, U.ψ (ι • τ) = -U.ψ τ := by
  obtain ⟨τ', hτ'⟩ := U.surj (-U.ψ UpperHalfPlane.I) (by
    intro h; exact U.ψ_notMem UpperHalfPlane.I (by simpa using neg_mem h))
  have hτ'' : U.ψ τ' = -U.ψ UpperHalfPlane.I := hτ'
  obtain ⟨ι, hιψ, -⟩ := U.exists_mem_pmDeck (ε := -1) (Or.inr rfl)
    (τ := UpperHalfPlane.I) (τ' := τ') (by rw [hτ'']; simp)
  have h0 : U.ψ τ' - -1 * U.ψ UpperHalfPlane.I = 0 := by rw [hτ'']; ring
  rw [h0] at hιψ
  exact ⟨ι, U.mem_pmDeck_of (Or.inr rfl) (zero_mem _) hιψ, fun τ ↦ by rw [hιψ]; ring⟩

theorem wp_ψ_smul_pm {g : SL(2, ℝ)} (hg : g ∈ U.pmDeck) (τ : ℍ) :
    L.weierstrassP (U.ψ (g • τ)) = L.weierstrassP (U.ψ τ) := by
  obtain ⟨ε, hε, l, hl, hψ⟩ := hg
  rw [hψ, L.weierstrassP_add_coe _ ⟨l, hl⟩]
  rcases hε with rfl | rfl
  · rw [one_mul]
  · rw [neg_one_mul, L.weierstrassP_neg]

/-- The deck group has finite index in `Γ̃`. -/
theorem relIndex_deckGroup_pmDeck_ne_zero : U.deckGroup.relIndex U.pmDeck ≠ 0 := by
  obtain ⟨ι, hι, hιψ⟩ := U.exists_iota
  classical
  refine Subgroup.index_ne_zero_of_finite (hH := ?_)
  refine Finite.of_surjective (fun b : Bool ↦ if b then (QuotientGroup.mk (1 : U.pmDeck) :
    U.pmDeck ⧸ U.deckGroup.subgroupOf U.pmDeck) else QuotientGroup.mk ⟨ι, hι⟩) ?_
  intro q
  induction q using QuotientGroup.induction_on with
  | H g =>
    obtain ⟨ε, hε, l, hl, hgψ⟩ := g.2
    rcases hε with rfl | rfl
    · refine ⟨true, ?_⟩
      simp only [if_true]
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      refine ⟨l, hl, fun τ ↦ ?_⟩
      simp [hgψ]
    · refine ⟨false, ?_⟩
      simp only [Bool.false_eq_true, if_false]
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      refine ⟨-l, neg_mem hl, fun τ ↦ ?_⟩
      have h1 := hιψ (ι⁻¹ • ((g : SL(2, ℝ)) • τ))
      rw [smul_inv_smul] at h1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_smul]
      rw [hgψ] at h1
      linear_combination h1

theorem commensurator_pmDeck :
    Subgroup.Commensurable.commensurator U.pmDeck =
      Subgroup.Commensurable.commensurator U.deckGroup := by
  refine Subgroup.Commensurable.eq ⟨?_, U.relIndex_deckGroup_pmDeck_ne_zero⟩
  rw [Subgroup.relIndex_eq_one.mpr (U.deckGroup_le_pmDeck)]; exact one_ne_zero

/-- A `Γ̃`-invariant function on `ℍ` as a function on `ℂ ∖ Λ` (and `0` on `Λ`). -/
noncomputable def descend (g : ℍ → ℂ) (w : ℂ) : ℂ := by
  classical
  exact if h : w ∉ L.lattice then g (U.surj w h).choose else 0

variable {U}

/-- `Γ̃`-invariance. -/
def PmInvariant (g : ℍ → ℂ) : Prop := ∀ γ ∈ U.pmDeck, ∀ τ, g (γ • τ) = g τ

theorem descend_ψ {g : ℍ → ℂ} (hg : PmInvariant (U := U) g) (τ : ℍ) :
    U.descend g (U.ψ τ) = g τ := by
  have hτ := U.ψ_notMem τ
  simp only [descend, hτ, not_false_eq_true, dite_true]
  set τ₁ := (U.surj (U.ψ τ) hτ).choose
  have h₁ : U.ψ τ₁ = U.ψ τ := (U.surj (U.ψ τ) hτ).choose_spec
  obtain ⟨γ, hγψ, hγ⟩ := U.exists_mem_pmDeck (ε := 1) (Or.inl rfl) (τ := τ₁) (τ' := τ)
    (by rw [h₁]; simp)
  rw [← hγ, hg γ (U.mem_pmDeck_of (Or.inl rfl) (by rw [h₁]; simp) hγψ)]

theorem descend_neg {g : ℍ → ℂ} (hg : PmInvariant (U := U) g) (w : ℂ) :
    U.descend g (-w) = U.descend g w := by
  by_cases hw : w ∈ L.lattice
  · have : -w ∈ L.lattice := neg_mem hw
    simp [descend, hw, this]
  · obtain ⟨τ, hτ⟩ := U.surj w hw
    obtain ⟨ι, hι, hιψ⟩ := U.exists_iota
    have hτ₁ : U.ψ τ = w := hτ
    rw [← hτ₁, ← hιψ, descend_ψ hg, descend_ψ hg, hg ι hι]

theorem descend_add {g : ℍ → ℂ} (hg : PmInvariant (U := U) g) (w : ℂ) {l : ℂ}
    (hl : l ∈ L.lattice) : U.descend g (w + l) = U.descend g w := by
  by_cases hw : w ∈ L.lattice
  · have : w + l ∈ L.lattice := add_mem hw hl
    simp [descend, hw, this]
  · obtain ⟨τ, hτ⟩ := U.surj w hw
    have hτ₁ : U.ψ τ = w := hτ
    have hwl : w + l ∉ L.lattice := fun h ↦ hw (by simpa using sub_mem h hl)
    obtain ⟨τ₂, hτ₂⟩ := U.surj (w + l) hwl
    have hτ₃ : U.ψ τ₂ = w + l := hτ₂
    obtain ⟨γ, hγψ, hγ⟩ := U.exists_mem_pmDeck (ε := 1) (Or.inl rfl) (τ := τ) (τ' := τ₂)
      (by rw [hτ₃, hτ₁]; simpa using hl)
    rw [← hτ₃, ← hτ₁, ← hγ, descend_ψ hg, descend_ψ hg,
      hg γ (U.mem_pmDeck_of (Or.inl rfl) (by rw [hτ₃, hτ₁]; simpa using hl) hγψ)]

/-- Holomorphy on `ℍ`, as a function on `{Im > 0}`. -/
def HolH (g : ℍ → ℂ) : Prop := DifferentiableOn ℂ (fun z ↦ g (ofComplex z)) {z | 0 < z.im}

theorem differentiableOn_descend {g : ℍ → ℂ} (hg : PmInvariant (U := U) g) (hh : HolH g) :
    DifferentiableOn ℂ (U.descend g) (L.lattice : Set ℂ)ᶜ := by
  intro w₀ hw₀
  have hopen : IsOpen ((L.lattice : Set ℂ)ᶜ) := L.isClosed_lattice.isOpen_compl
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.mp hopen w₀ hw₀
  obtain ⟨τ₀, hτ₀⟩ := U.surj w₀ hw₀
  obtain ⟨σ, hσc, hσψ, hσ0⟩ := U.covering.exists_lift_of_convex (convex_ball w₀ ρ)
    continuousOn_id (fun w hw ↦ hρsub hw) (mem_ball_self hρ) (e₀ := τ₀) hτ₀
  have hσψ' : ∀ w ∈ ball w₀ ρ, U.ψ (σ w) = w := fun w hw ↦ hσψ w hw
  have heq : ∀ w ∈ ball w₀ ρ, U.descend g w = g (σ w) := fun w hw ↦ by
    conv_lhs => rw [← hσψ' w hw]
    exact descend_ψ hg _
  have hσd : DifferentiableAt ℂ (fun w ↦ ((σ w : ℍ) : ℂ)) w₀ := by
    refine differentiableAt_of_comp_eq (f := U.Ψ) (g := id)
      (U.hasStrictDerivAt_Ψ (σ w₀).im_pos) (U.deriv_ne_zero _ (σ w₀).im_pos)
      ((continuous_coe.comp_continuousOn hσc).continuousAt (ball_mem_nhds _ hρ)) ?_
      differentiableAt_id
    filter_upwards [ball_mem_nhds w₀ hρ] with w hw using hσψ' w hw
  have hgd : DifferentiableAt ℂ (fun z ↦ g (ofComplex z)) ((σ w₀ : ℍ) : ℂ) :=
    (hh _ (σ w₀).im_pos).differentiableAt (isOpen_upper.mem_nhds (σ w₀).im_pos)
  have hcomp : DifferentiableAt ℂ (fun w ↦ g (ofComplex ((σ w : ℍ) : ℂ))) w₀ :=
    DifferentiableAt.comp (g := fun z ↦ g (ofComplex z)) (f := fun w ↦ ((σ w : ℍ) : ℂ)) w₀ hgd hσd
  refine (hcomp.congr_of_eventuallyEq ?_).differentiableWithinAt
  filter_upwards [ball_mem_nhds w₀ hρ] with w hw
  rw [heq w hw, ofComplex_apply]

end Unif

end Uniformization
