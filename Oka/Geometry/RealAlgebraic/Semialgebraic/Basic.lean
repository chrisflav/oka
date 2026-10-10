/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Data.Fintype.Option
import Mathlib.RingTheory.MvPolynomial.Basic
import Oka.Analysis.Polynomial.ParametricSignDiagram

/-!
# Semialgebraic sets and the Tarski–Seidenberg theorem

A subset `S` of `ℝ^ι` is *semialgebraic* (`IsSemialgebraic S`) when membership in `S` is
determined by the signs of finitely many real polynomials: there is a finite family `F` of
polynomials such that two points at which every member of `F` has the same sign are either both
in `S` or both outside it. Equivalently, `S` is a finite union of sets of the form
`{x | ∀ p ∈ F, sign (p x) = τ p}`, i.e. a finite boolean combination of sets `{p > 0}`; this is the
usual definition (Bochnak–Coste–Roy, *Real algebraic geometry*, Def. 2.1.4). The present form
makes the boolean closure properties immediate.

Main results:

* closure under complement, finite intersections and unions, and preimages by polynomial maps
  (`IsSemialgebraic.preimage_polynomial`), in particular by coordinate maps;
* the basic sets `{x | p x < q x}`, `{x | p x ≤ q x}`, `{x | p x = q x}`;
* **Tarski–Seidenberg** (`IsSemialgebraic.exists_option`, `IsSemialgebraic.exists_pi`): the
  projection of a semialgebraic set along finitely many coordinates is semialgebraic. The proof
  is Cohen–Hörmander's, `Polynomial.exists_signMatch_of_signsAgree`: the sign diagram in the
  eliminated variable is controlled by the signs of finitely many polynomials in the remaining
  ones.

Mathlib has no notion of semialgebraic set.
-/

open MvPolynomial

variable {ι κ : Type*}

/-- A set `S ⊆ ℝ^ι` is *semialgebraic* if membership in `S` is determined by the signs of finitely
many real polynomials. -/
def IsSemialgebraic (S : Set (ι → ℝ)) : Prop :=
  ∃ F : Finset (MvPolynomial ι ℝ), ∀ x y : ι → ℝ,
    (∀ p ∈ F, SignType.sign (eval x p) = SignType.sign (eval y p)) → x ∈ S → y ∈ S

namespace IsSemialgebraic

variable {S T : Set (ι → ℝ)}

/-- Transport semialgebraicity along an equality of sets. -/
lemma congr (h : IsSemialgebraic S) (hST : S = T) : IsSemialgebraic T := hST ▸ h

/-- The complement of a semialgebraic set is semialgebraic. -/
theorem compl (h : IsSemialgebraic S) : IsSemialgebraic Sᶜ := by
  obtain ⟨F, hF⟩ := h
  exact ⟨F, fun x y hxy hx hy => hx (hF y x (fun p hp => (hxy p hp).symm) hy)⟩

/-- The intersection of two semialgebraic sets is semialgebraic. -/
theorem inter (hS : IsSemialgebraic S) (hT : IsSemialgebraic T) : IsSemialgebraic (S ∩ T) := by
  classical
  obtain ⟨F, hF⟩ := hS
  obtain ⟨G, hG⟩ := hT
  exact ⟨F ∪ G, fun x y hxy hx => ⟨hF x y (fun p hp => hxy p (Finset.mem_union_left _ hp)) hx.1,
    hG x y (fun p hp => hxy p (Finset.mem_union_right _ hp)) hx.2⟩⟩

/-- The union of two semialgebraic sets is semialgebraic. -/
theorem union (hS : IsSemialgebraic S) (hT : IsSemialgebraic T) : IsSemialgebraic (S ∪ T) := by
  have := (hS.compl.inter hT.compl).compl
  rwa [← Set.compl_union, compl_compl] at this

/-- The difference of two semialgebraic sets is semialgebraic. -/
theorem diff (hS : IsSemialgebraic S) (hT : IsSemialgebraic T) : IsSemialgebraic (S \ T) :=
  hS.inter hT.compl

/-- The whole space is semialgebraic. -/
theorem univ : IsSemialgebraic (Set.univ : Set (ι → ℝ)) :=
  ⟨∅, fun _ _ _ _ => Set.mem_univ _⟩

/-- The empty set is semialgebraic. -/
theorem empty : IsSemialgebraic (∅ : Set (ι → ℝ)) := by
  simpa using (univ (ι := ι)).compl

/-- A finite intersection of semialgebraic sets is semialgebraic. -/
theorem biInter {α : Type*} (s : Finset α) {S : α → Set (ι → ℝ)}
    (h : ∀ a ∈ s, IsSemialgebraic (S a)) : IsSemialgebraic (⋂ a ∈ s, S a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using univ
  | insert a s _ ih =>
    rw [Finset.set_biInter_insert]
    exact (h a (Finset.mem_insert_self _ _)).inter
      (ih fun b hb => h b (Finset.mem_insert_of_mem hb))

/-- A finite union of semialgebraic sets is semialgebraic. -/
theorem biUnion {α : Type*} (s : Finset α) {S : α → Set (ι → ℝ)}
    (h : ∀ a ∈ s, IsSemialgebraic (S a)) : IsSemialgebraic (⋃ a ∈ s, S a) := by
  have := (biInter s (fun a ha => (h a ha).compl)).compl
  simpa [Set.compl_iInter] using this

/-- An intersection of semialgebraic sets indexed by a finite type is semialgebraic. -/
theorem iInter {α : Type*} [Finite α] {S : α → Set (ι → ℝ)} (h : ∀ a, IsSemialgebraic (S a)) :
    IsSemialgebraic (⋂ a, S a) := by
  have := Fintype.ofFinite α
  simpa using biInter Finset.univ (fun a _ => h a)

/-- A union of semialgebraic sets indexed by a finite type is semialgebraic. -/
theorem iUnion {α : Type*} [Finite α] {S : α → Set (ι → ℝ)} (h : ∀ a, IsSemialgebraic (S a)) :
    IsSemialgebraic (⋃ a, S a) := by
  have := Fintype.ofFinite α
  simpa using biUnion Finset.univ (fun a _ => h a)

/-- The set where a polynomial is positive. -/
theorem setOf_pos (p : MvPolynomial ι ℝ) : IsSemialgebraic {x | 0 < eval x p} := by
  refine ⟨{p}, fun x y hxy hx => ?_⟩
  have := hxy p (Finset.mem_singleton_self p)
  rw [sign_pos hx] at this
  exact sign_eq_one_iff.1 this.symm

/-- The set where one polynomial is smaller than another. -/
theorem setOf_lt (p q : MvPolynomial ι ℝ) : IsSemialgebraic {x | eval x p < eval x q} :=
  (setOf_pos (q - p)).congr (by ext x; simp)

/-- The set where one polynomial is at most another. -/
theorem setOf_le (p q : MvPolynomial ι ℝ) : IsSemialgebraic {x | eval x p ≤ eval x q} :=
  (setOf_lt q p).compl.congr (by ext x; simp)

/-- The set where two polynomials agree. -/
theorem setOf_eq (p q : MvPolynomial ι ℝ) : IsSemialgebraic {x | eval x p = eval x q} :=
  ((setOf_le p q).inter (setOf_le q p)).congr (by ext x; simp [le_antisymm_iff])

/-- The set where two polynomials differ. -/
theorem setOf_ne (p q : MvPolynomial ι ℝ) : IsSemialgebraic {x | eval x p ≠ eval x q} :=
  (setOf_eq p q).compl

/-- Preimage of a semialgebraic set by a polynomial map. -/
theorem preimage_polynomial (g : κ → MvPolynomial ι ℝ) {S : Set (κ → ℝ)}
    (h : IsSemialgebraic S) : IsSemialgebraic {x : ι → ℝ | (fun k => eval x (g k)) ∈ S} := by
  classical
  obtain ⟨F, hF⟩ := h
  have key : ∀ (x : ι → ℝ) (p : MvPolynomial κ ℝ),
      eval x (bind₁ g p) = eval (fun k => eval x (g k)) p := by
    intro x p
    exact eval₂Hom_bind₁ _ _ _ _
  refine ⟨F.image (bind₁ g), fun x y hxy hx => hF _ _ (fun p hp => ?_) hx⟩
  rw [← key, ← key]
  exact hxy _ (Finset.mem_image_of_mem _ hp)

/-- Preimage of a semialgebraic set by a coordinate map `x ↦ x ∘ σ`. -/
theorem preimage_comp (σ : κ → ι) {S : Set (κ → ℝ)} (h : IsSemialgebraic S) :
    IsSemialgebraic {x : ι → ℝ | x ∘ σ ∈ S} :=
  (preimage_polynomial (fun k => X (σ k)) h).congr (by ext x; simp [Function.comp_def])

/-- **Tarski–Seidenberg**, one variable: the projection of a semialgebraic subset of
`ℝ^(Option ι)` along the coordinate `none` is semialgebraic. -/
theorem exists_option {S : Set (Option ι → ℝ)} (h : IsSemialgebraic S) :
    IsSemialgebraic {x : ι → ℝ | ∃ y : ℝ, (fun o => Option.elim o y x) ∈ S} := by
  classical
  obtain ⟨F, hF⟩ := h
  obtain ⟨Q, hQ⟩ := Polynomial.exists_signMatch_of_signsAgree (A := MvPolynomial ι ℝ)
    (F.val.map (optionEquivLeft ℝ ι))
  refine ⟨Q, fun x x' hxx' ⟨y, hy⟩ => ?_⟩
  obtain ⟨φ, hφ⟩ := hQ (eval x) (eval x') hxx'
  refine ⟨φ y, hF _ _ (fun p hp => ?_) hy⟩
  rw [optionEquivLeft_elim_eval, optionEquivLeft_elim_eval]
  exact (hφ _ (Multiset.mem_map_of_mem _ hp) y).symm

/-- **Tarski–Seidenberg**: the projection of a semialgebraic subset of `ℝ^(ι ⊕ κ)` to `ℝ^ι`, for
`κ` finite, is semialgebraic. -/
theorem exists_pi [Finite κ] {S : Set (ι ⊕ κ → ℝ)} (h : IsSemialgebraic S) :
    IsSemialgebraic {x : ι → ℝ | ∃ y : κ → ℝ, Sum.elim x y ∈ S} := by
  revert S
  refine Finite.induction_empty_option (P := fun κ => ∀ {S : Set (ι ⊕ κ → ℝ)},
    IsSemialgebraic S → IsSemialgebraic {x : ι → ℝ | ∃ y : κ → ℝ, Sum.elim x y ∈ S})
    ?_ ?_ ?_ κ
  · intro α β e ih S hS
    have := ih (S := {w | w ∘ Sum.map id e.symm ∈ S}) (preimage_comp _ hS)
    refine this.congr (Set.ext fun x => ⟨fun ⟨y, hy⟩ => ⟨y ∘ e.symm, ?_⟩,
      fun ⟨y, hy⟩ => ⟨y ∘ e, ?_⟩⟩)
    · have key : Sum.elim x y ∘ Sum.map id e.symm = Sum.elim x (y ∘ e.symm) := by
        funext s
        rcases s with i | b <;> rfl
      rw [← key]
      exact hy
    · change Sum.elim x (y ∘ e) ∘ Sum.map id e.symm ∈ S
      have key : Sum.elim x (y ∘ e) ∘ Sum.map id e.symm = Sum.elim x y := by
        funext s
        rcases s with i | b <;> simp
      rw [key]
      exact hy
  · intro S hS
    refine (preimage_comp (fun s : ι ⊕ PEmpty => Sum.elim id PEmpty.elim s) hS).congr ?_
    ext x
    simp only [Set.mem_setOf_eq]
    have key : ∀ y : PEmpty → ℝ, (x ∘ fun s => Sum.elim id PEmpty.elim s) = Sum.elim x y := by
      intro y
      funext s
      rcases s with i | e
      · rfl
      · exact e.elim
    exact ⟨fun hx => ⟨PEmpty.elim, key _ ▸ hx⟩, fun ⟨y, hy⟩ => (key y).symm ▸ hy⟩
  · intro α _ ih S hS
    let σ : ι ⊕ Option α → Option (ι ⊕ α) :=
      Sum.elim (fun i => some (Sum.inl i)) (fun o => o.map Sum.inr)
    have h1 := exists_option (preimage_comp σ hS)
    have h2 := ih h1
    refine h2.congr (Set.ext fun x => ⟨fun ⟨y, t, ht⟩ => ⟨fun o => o.elim t y, ?_⟩,
      fun ⟨y, hy⟩ => ⟨y ∘ some, y none, ?_⟩⟩)
    · have key : (fun o => Option.elim o t (Sum.elim x y)) ∘ σ =
          Sum.elim x (fun o => o.elim t y) := by
        funext s
        rcases s with i | (_ | a) <;> rfl
      have ht' : (fun o => Option.elim o t (Sum.elim x y)) ∘ σ ∈ S := ht
      rw [key] at ht'
      exact ht'
    · change (fun o => Option.elim o (y none) (Sum.elim x (y ∘ some))) ∘ σ ∈ S
      have key : (fun o => Option.elim o (y none) (Sum.elim x (y ∘ some))) ∘ σ = Sum.elim x y := by
        funext s
        rcases s with i | (_ | a) <;> rfl
      rw [key]
      exact hy

/-- **Tarski–Seidenberg**, universal form. -/
theorem forall_pi [Finite κ] {S : Set (ι ⊕ κ → ℝ)} (h : IsSemialgebraic S) :
    IsSemialgebraic {x : ι → ℝ | ∀ y : κ → ℝ, Sum.elim x y ∈ S} :=
  (exists_pi h.compl).compl.congr (by ext x; simp)

end IsSemialgebraic
