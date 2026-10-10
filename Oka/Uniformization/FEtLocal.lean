/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Uniformization.Integrality
import Oka.Analysis.Complex.PolynomialSimpleRoot

/-!
# Finite étale algebras over a ring of holomorphic functions on `ℍ`: local structure

Let `ι₀ : A → (ℍ → ℂ)` be a `ℂ`-algebra map into holomorphic functions, `χ_τ = (a ↦ ι₀ a τ)` its
points, and `A → B` a finite étale algebra: every `χ_τ` has exactly `n` extensions to `B`
(`FEt.Over`), and near every `τ₀` there is a local presentation: `b₀ ∈ B` a root of a monic
`F ∈ A[X]` of degree `n`, and `δ ∈ A` with `δ(τ₀) ≠ 0` and `δ B ⊆ A[b₀]`.

`FEt.exists_local`: near `τ₀`, `F_τ = ∏_j (X - r_j(τ))` with holomorphic, pairwise distinct
`r_j`, and the points of `B` over `χ_τ` are exactly the `n` points with `ψ(b₀) = r_j(τ)`; their
values `ψ(b) = (P_b)_τ(r_j(τ)) / δ(τ)` depend holomorphically on `τ` (`δ b = P_b(b₀)`).
-/

open Complex Metric Set Filter Topology Polynomial
open UpperHalfPlane hiding I I_re I_im
open scoped MatrixGroups

namespace Uniformization

namespace FEt

variable {A B : Type*} [CommRing A] [Algebra ℂ A] [CommRing B] [Algebra ℂ B] [Algebra A B]

/-- The point `a ↦ ι₀ a τ`. -/
def pt (ι₀ : A →ₐ[ℂ] (ℍ → ℂ)) (τ : ℍ) : A →ₐ[ℂ] ℂ :=
  (Pi.evalAlgHom ℂ (fun _ : ℍ ↦ ℂ) τ).comp ι₀

@[simp] theorem pt_apply (ι₀ : A →ₐ[ℂ] (ℍ → ℂ)) (τ : ℍ) (a : A) : pt ι₀ τ a = ι₀ a τ := rfl

variable (B) in
/-- The points of `B` over a point `χ` of `A`. -/
abbrev Over (χ : A →ₐ[ℂ] ℂ) : Type _ := {ψ : B →ₐ[ℂ] ℂ // ∀ a, ψ (algebraMap A B a) = χ a}

/-- A point over `χ` evaluates polynomials in `b₀` through `χ`. -/
theorem Over.apply_aeval {χ : A →ₐ[ℂ] ℂ} (ψ : Over B χ) (b₀ : B) (P : A[X]) :
    ψ.1 (aeval b₀ P) = (P.map (χ : A →+* ℂ)).eval (ψ.1 b₀) := by
  rw [aeval_def, eval_map]
  have := Polynomial.hom_eval₂ P (algebraMap A B) (ψ.1 : B →+* ℂ) b₀
  rw [RingHom.coe_coe] at this
  rw [this]
  congr 1
  ext a
  exact ψ.2 a

/-- With a local presentation, points over `χ` with `χ δ ≠ 0` are determined by their value at
`b₀`. -/
theorem Over.ext_of_apply_eq {χ : A →ₐ[ℂ] ℂ} {b₀ : B} {δ : A} (hδ : χ δ ≠ 0)
    (hpres : ∀ b : B, algebraMap A B δ * b ∈ Algebra.adjoin A {b₀}) {ψ ψ' : Over B χ}
    (h : ψ.1 b₀ = ψ'.1 b₀) : ψ = ψ' := by
  apply Subtype.ext
  ext b
  obtain ⟨P, hP⟩ := (Algebra.adjoin_singleton_eq_range_aeval A b₀ ▸ hpres b :
    algebraMap A B δ * b ∈ (aeval b₀).range)
  have h1 := congrArg ψ.1 hP
  have h2 := congrArg ψ'.1 hP
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h1 h2
  rw [Over.apply_aeval, map_mul, ψ.2] at h1
  rw [Over.apply_aeval, map_mul, ψ'.2] at h2
  rw [h] at h1
  exact mul_left_cancel₀ hδ (h1.symm.trans h2)

/-- The values of the points over `χ` at `b₀` are roots of `F_χ`. -/
theorem Over.isRoot {χ : A →ₐ[ℂ] ℂ} (ψ : Over B χ) {b₀ : B} {F : A[X]} (hF : aeval b₀ F = 0) :
    (F.map (χ : A →+* ℂ)).IsRoot (ψ.1 b₀) := by
  rw [IsRoot, ← Over.apply_aeval, hF, map_zero]

variable (ι₀ : A →ₐ[ℂ] (ℍ → ℂ))

/-- **Local structure of a finite étale algebra.** -/
theorem exists_local (hhol : ∀ a, Unif.HolH (ι₀ a)) {n : ℕ}
    (hcount : ∀ τ, Nat.card (Over B (pt ι₀ τ)) = n) (τ₀ : ℍ) {b₀ : B} {F : A[X]} {δ : A}
    (hFm : F.Monic) (hFn : F.natDegree = n) (hF : aeval b₀ F = 0) (hδ : ι₀ δ τ₀ ≠ 0)
    (hpres : ∀ b, algebraMap A B δ * b ∈ Algebra.adjoin A {b₀}) :
    ∃ O : Set ℂ, IsOpen O ∧ (τ₀ : ℂ) ∈ O ∧ (∀ z ∈ O, 0 < z.im) ∧
      (∀ τ : ℍ, (τ : ℂ) ∈ O → ι₀ δ τ ≠ 0) ∧
      ∃ r : Fin n → ℂ → ℂ, (∀ j, AnalyticOnNhd ℂ (r j) O) ∧
        (∀ z ∈ O, Function.Injective fun j ↦ r j z) ∧
        (∀ τ : ℍ, (τ : ℂ) ∈ O → ∀ ψ : Over B (pt ι₀ τ), ∃ j, ψ.1 b₀ = r j τ) ∧
        ∀ τ : ℍ, (τ : ℂ) ∈ O → ∀ j, ∃ ψ : Over B (pt ι₀ τ), ψ.1 b₀ = r j τ := by
  classical
  set p : ℂ → ℂ[X] := fun z ↦ F.map (pt ι₀ (ofComplex z) : A →+* ℂ)
  have hpm : ∀ z, (p z).Monic := fun z ↦ hFm.map _
  have hpn : ∀ z, (p z).natDegree = n := fun z ↦ by rw [(hFm.natDegree_map _), hFn]
  have hpa : ∀ i, AnalyticAt ℂ (fun z ↦ (p z).coeff i) τ₀ := by
    intro i
    simp only [p, coeff_map]
    exact (hhol (F.coeff i)).analyticAt (isOpen_upper.mem_nhds τ₀.im_pos)
  have hp₀ : p τ₀ = F.map (pt ι₀ τ₀ : A →+* ℂ) := by simp [p]
  -- the points over `τ₀` inject into the roots
  have hinj₀ : Function.Injective fun ψ : Over B (pt ι₀ τ₀) ↦ ψ.1 b₀ :=
    fun ψ ψ' h ↦ Over.ext_of_apply_eq hδ hpres h
  have hsep : (p τ₀).Separable := by
    rw [← nodup_roots_iff_of_splits (hpm _).ne_zero (IsAlgClosed.splits _)]
    rw [← Multiset.toFinset_card_eq_card_iff_nodup]
    apply le_antisymm (Multiset.toFinset_card_le _)
    rw [IsAlgClosed.card_roots_eq_natDegree, hpn]
    have hmaps : ∀ ψ : Over B (pt ι₀ τ₀), ψ.1 b₀ ∈ (p τ₀).roots.toFinset := fun ψ ↦ by
      rw [Multiset.mem_toFinset, mem_roots (hpm _).ne_zero, hp₀]; exact ψ.isRoot hF
    have := Nat.card_le_card_of_injective (fun ψ : Over B (pt ι₀ τ₀) ↦
      (⟨ψ.1 b₀, hmaps ψ⟩ : (p τ₀).roots.toFinset)) (fun ψ ψ' h ↦ hinj₀ (congrArg Subtype.val h))
    rwa [hcount, Nat.card_eq_fintype_card, Fintype.card_coe] at this
  obtain ⟨U, hUo, hτU, r, hra, hr⟩ :=
    Polynomial.exists_analyticOnNhd_eq_prod_X_sub_C_of_separable hpm hpn hpa hsep
  -- the open set
  have hδc : ContinuousOn (fun z ↦ ι₀ δ (ofComplex z)) {z : ℂ | 0 < z.im} :=
    (hhol δ).continuousOn
  set O := U ∩ ({z : ℂ | 0 < z.im} ∩ (fun z ↦ ι₀ δ (ofComplex z)) ⁻¹' {0}ᶜ)
  have hOo : IsOpen O := hUo.inter (hδc.isOpen_inter_preimage isOpen_upper isOpen_compl_singleton)
  have hτO : (τ₀ : ℂ) ∈ O := ⟨hτU, τ₀.im_pos, by simpa [ofComplex_apply] using hδ⟩
  have hOi : ∀ z ∈ O, 0 < z.im := fun z hz ↦ hz.2.1
  have hOδ : ∀ τ : ℍ, (τ : ℂ) ∈ O → ι₀ δ τ ≠ 0 := fun τ hτ ↦ by
    have := hτ.2.2
    simpa [ofComplex_apply] using this
  have hpτ : ∀ τ : ℍ, p τ = F.map (pt ι₀ τ : A →+* ℂ) := fun τ ↦ by simp [p]
  have hroot : ∀ τ : ℍ, (τ : ℂ) ∈ O → ∀ ψ : Over B (pt ι₀ τ), ∃ j, ψ.1 b₀ = r j τ := by
    intro τ hτ ψ
    have h1 := ψ.isRoot hF
    rw [← hpτ, (hr τ hτ.1).2, IsRoot, eval_prod, Finset.prod_eq_zero_iff] at h1
    obtain ⟨j, -, hj⟩ := h1
    exact ⟨j, by simpa [sub_eq_zero] using hj⟩
  refine ⟨O, hOo, hτO, hOi, hOδ, r, fun j ↦ (hra j).mono inter_subset_left,
    fun z hz ↦ (hr z hz.1).1, hroot, fun τ hτ ↦ ?_⟩
  -- surjectivity by counting
  choose idx hidx using hroot τ hτ
  have hinj : Function.Injective idx := fun ψ ψ' h ↦
    Over.ext_of_apply_eq (hOδ τ hτ) hpres (by rw [hidx, hidx, h])
  have hbij := hinj.bijective_of_nat_card_le (by rw [Nat.card_eq_fintype_card, Fintype.card_fin,
    hcount])
  intro j
  obtain ⟨ψ, hψ⟩ := hbij.2 j
  exact ⟨ψ, by rw [hidx, hψ]⟩

end FEt

end Uniformization
