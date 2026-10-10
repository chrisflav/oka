/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Geometry.RealAlgebraic.Semialgebraic.Basic

/-!
# Semialgebraic sets defined by first-order formulas

By the Tarski–Seidenberg theorem every set defined by a first-order formula over `(ℝ, +, ·, <)`
is semialgebraic. This file packages that fact as closure lemmas for sets of the form
`{x | P x}`, one for each logical connective and quantifier, so that semialgebraicity of a set
given by an explicit formula can be proved by following the formula:

* `IsSemialgebraic.setOf_and`, `setOf_or`, `setOf_not`, `setOf_imp`, `setOf_iff`;
* real quantifiers `IsSemialgebraic.setOf_exists`, `setOf_forall` (the new variable is the
  coordinate `none` of `ℝ^(Option ι)`), quantifiers over `ℝ^κ` for finite `κ`
  (`setOf_exists_pi`, `setOf_forall_pi`), and finite quantifiers over an index
  (`setOf_forall_finite`, `setOf_exists_finite`);
* atomic formulas `f x < g x`, `f x ≤ g x`, `f x = g x`, `f x ≠ g x` for *polynomial functions*
  `f`, `g` (`IsPolynomialFun`), which are closed under the ring operations and contain the
  coordinates and constants.

The tactic `semialg` applies these lemmas recursively and discharges the polynomial-function
side conditions with `poly_fun`.

Subsets of `ℝ` are handled through `ℝ^Unit` (`IsSemialgebraic₁`).
-/

open MvPolynomial

variable {ι κ : Type*}

/-- A function `ℝ^ι → ℝ` is a *polynomial function* if it is evaluation of a real polynomial. -/
def IsPolynomialFun (f : (ι → ℝ) → ℝ) : Prop := ∃ p : MvPolynomial ι ℝ, ∀ x, f x = eval x p

namespace IsPolynomialFun

/-- Constants are polynomial functions. -/
theorem const (c : ℝ) : IsPolynomialFun (fun _ : ι → ℝ => c) := ⟨C c, fun _ => by simp⟩

/-- Coordinates are polynomial functions. -/
theorem coord (i : ι) : IsPolynomialFun (fun x : ι → ℝ => x i) := ⟨X i, fun _ => by simp⟩

/-- Sums of polynomial functions are polynomial functions. -/
theorem add {f g : (ι → ℝ) → ℝ} (hf : IsPolynomialFun f) (hg : IsPolynomialFun g) :
    IsPolynomialFun (fun x => f x + g x) := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  exact ⟨p + q, fun x => by simp [hp, hq]⟩

/-- Products of polynomial functions are polynomial functions. -/
theorem mul {f g : (ι → ℝ) → ℝ} (hf : IsPolynomialFun f) (hg : IsPolynomialFun g) :
    IsPolynomialFun (fun x => f x * g x) := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  exact ⟨p * q, fun x => by simp [hp, hq]⟩

/-- Negatives of polynomial functions are polynomial functions. -/
theorem neg {f : (ι → ℝ) → ℝ} (hf : IsPolynomialFun f) : IsPolynomialFun (fun x => -f x) := by
  obtain ⟨p, hp⟩ := hf
  exact ⟨-p, fun x => by simp [hp]⟩

/-- Differences of polynomial functions are polynomial functions. -/
theorem sub {f g : (ι → ℝ) → ℝ} (hf : IsPolynomialFun f) (hg : IsPolynomialFun g) :
    IsPolynomialFun (fun x => f x - g x) := by
  simpa [sub_eq_add_neg] using hf.add hg.neg

/-- Powers of polynomial functions are polynomial functions. -/
theorem pow {f : (ι → ℝ) → ℝ} (hf : IsPolynomialFun f) (n : ℕ) :
    IsPolynomialFun (fun x => f x ^ n) := by
  obtain ⟨p, hp⟩ := hf
  exact ⟨p ^ n, fun x => by simp [hp]⟩

/-- Finite sums of polynomial functions are polynomial functions. -/
theorem sum {α : Type*} (s : Finset α) {f : α → (ι → ℝ) → ℝ}
    (hf : ∀ a ∈ s, IsPolynomialFun (f a)) : IsPolynomialFun (fun x => ∑ a ∈ s, f a x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using const 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self _ _)).add
      (ih fun b hb => hf b (Finset.mem_insert_of_mem hb))

/-- Evaluation of a fixed polynomial at polynomial functions. -/
theorem eval (p : MvPolynomial κ ℝ) {g : κ → (ι → ℝ) → ℝ} (hg : ∀ k, IsPolynomialFun (g k)) :
    IsPolynomialFun (fun x => MvPolynomial.eval (fun k => g k x) p) := by
  choose q hq using hg
  refine ⟨bind₁ q p, fun x => ?_⟩
  beta_reduce
  rw [show (fun k => g k x) = fun k => MvPolynomial.eval x (q k) from funext fun k => hq k x]
  exact (eval₂Hom_bind₁ _ _ _ _).symm

end IsPolynomialFun

/-- Discharge goals `IsPolynomialFun f` for `f` built from coordinates, constants, ring operations
and evaluation of fixed polynomials. -/
macro (name := polyFun) "poly_fun" : tactic => `(tactic| repeat' (first
  | exact IsPolynomialFun.coord _
  | exact IsPolynomialFun.const _
  | apply IsPolynomialFun.add
  | apply IsPolynomialFun.sub
  | apply IsPolynomialFun.mul
  | apply IsPolynomialFun.neg
  | apply IsPolynomialFun.pow
  | apply IsPolynomialFun.eval; intro))

namespace IsSemialgebraic

variable {P Q : (ι → ℝ) → Prop}

/-- Conjunction. -/
theorem setOf_and (hP : IsSemialgebraic {x | P x}) (hQ : IsSemialgebraic {x | Q x}) :
    IsSemialgebraic {x | P x ∧ Q x} :=
  hP.inter hQ

/-- Disjunction. -/
theorem setOf_or (hP : IsSemialgebraic {x | P x}) (hQ : IsSemialgebraic {x | Q x}) :
    IsSemialgebraic {x | P x ∨ Q x} :=
  hP.union hQ

/-- Negation. -/
theorem setOf_not (hP : IsSemialgebraic {x | P x}) : IsSemialgebraic {x | ¬ P x} :=
  hP.compl

/-- Implication. -/
theorem setOf_imp (hP : IsSemialgebraic {x | P x}) (hQ : IsSemialgebraic {x | Q x}) :
    IsSemialgebraic {x | P x → Q x} :=
  (hP.compl.union hQ).congr (by ext x; simp [imp_iff_not_or])

/-- Equivalence. -/
theorem setOf_iff (hP : IsSemialgebraic {x | P x}) (hQ : IsSemialgebraic {x | Q x}) :
    IsSemialgebraic {x | P x ↔ Q x} :=
  ((setOf_imp hP hQ).inter (setOf_imp hQ hP)).congr (by ext x; simp [iff_iff_implies_and_implies])

/-- A set defined by a formula not depending on the point. -/
theorem setOf_const (p : Prop) : IsSemialgebraic {_x : ι → ℝ | p} := by
  by_cases hp : p
  · exact univ.congr (by ext; simp [hp])
  · exact empty.congr (by ext; simp [hp])

/-- The formula `True`. -/
theorem setOf_true : IsSemialgebraic {_x : ι → ℝ | True} := univ.congr (by ext; simp)

/-- The formula `False`. -/
theorem setOf_false : IsSemialgebraic {_x : ι → ℝ | False} := empty.congr (by ext; simp)

/-- Existential quantification over a real variable (Tarski–Seidenberg). -/
theorem setOf_exists {P : (ι → ℝ) → ℝ → Prop}
    (h : IsSemialgebraic {w : Option ι → ℝ | P (fun i => w (some i)) (w none)}) :
    IsSemialgebraic {x | ∃ y, P x y} :=
  (exists_option h).congr rfl

/-- Universal quantification over a real variable. -/
theorem setOf_forall {P : (ι → ℝ) → ℝ → Prop}
    (h : IsSemialgebraic {w : Option ι → ℝ | P (fun i => w (some i)) (w none)}) :
    IsSemialgebraic {x | ∀ y, P x y} :=
  (setOf_exists (P := fun x y => ¬ P x y) h.compl).compl.congr (by ext x; simp)

/-- Existential quantification over `ℝ^κ`, `κ` finite. -/
theorem setOf_exists_pi [Finite κ] {P : (ι → ℝ) → (κ → ℝ) → Prop}
    (h : IsSemialgebraic {w : ι ⊕ κ → ℝ | P (fun i => w (Sum.inl i)) (fun k => w (Sum.inr k))}) :
    IsSemialgebraic {x | ∃ y, P x y} :=
  (exists_pi h).congr rfl

/-- Universal quantification over `ℝ^κ`, `κ` finite. -/
theorem setOf_forall_pi [Finite κ] {P : (ι → ℝ) → (κ → ℝ) → Prop}
    (h : IsSemialgebraic {w : ι ⊕ κ → ℝ | P (fun i => w (Sum.inl i)) (fun k => w (Sum.inr k))}) :
    IsSemialgebraic {x | ∀ y, P x y} :=
  (setOf_exists_pi (P := fun x y => ¬ P x y) h.compl).compl.congr (by ext x; simp)

/-- Universal quantification over a finite index type. -/
theorem setOf_forall_finite {α : Type*} [Finite α] {P : (ι → ℝ) → α → Prop}
    (h : ∀ a, IsSemialgebraic {x | P x a}) : IsSemialgebraic {x | ∀ a, P x a} :=
  (iInter h).congr (by ext x; simp)

/-- Existential quantification over a finite index type. -/
theorem setOf_exists_finite {α : Type*} [Finite α] {P : (ι → ℝ) → α → Prop}
    (h : ∀ a, IsSemialgebraic {x | P x a}) : IsSemialgebraic {x | ∃ a, P x a} :=
  (iUnion h).congr (by ext x; simp)

variable {f g : (ι → ℝ) → ℝ}

/-- The atomic formula `f x < g x` for polynomial functions. -/
theorem setOf_lt' (hf : IsPolynomialFun f) (hg : IsPolynomialFun g) :
    IsSemialgebraic {x | f x < g x} := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  exact (setOf_lt p q).congr (by ext x; simp [hp, hq])

/-- The atomic formula `f x ≤ g x` for polynomial functions. -/
theorem setOf_le' (hf : IsPolynomialFun f) (hg : IsPolynomialFun g) :
    IsSemialgebraic {x | f x ≤ g x} :=
  (setOf_lt' hg hf).compl.congr (by ext x; simp)

/-- The atomic formula `f x = g x` for polynomial functions. -/
theorem setOf_eq' (hf : IsPolynomialFun f) (hg : IsPolynomialFun g) :
    IsSemialgebraic {x | f x = g x} :=
  ((setOf_le' hf hg).inter (setOf_le' hg hf)).congr (by ext x; simp [le_antisymm_iff])

/-- The atomic formula `f x ≠ g x` for polynomial functions. -/
theorem setOf_ne' (hf : IsPolynomialFun f) (hg : IsPolynomialFun g) :
    IsSemialgebraic {x | f x ≠ g x} :=
  (setOf_eq' hf hg).compl

end IsSemialgebraic

/-- One step of `semialg`: apply the closure lemma matching the head of the formula. -/
macro (name := semialgStep) "semialg_step" : tactic => `(tactic| first
  | exact IsSemialgebraic.setOf_const _
  | apply IsSemialgebraic.setOf_and
  | apply IsSemialgebraic.setOf_or
  | apply IsSemialgebraic.setOf_imp
  | apply IsSemialgebraic.setOf_iff
  | apply IsSemialgebraic.setOf_not
  | exact IsSemialgebraic.setOf_true
  | exact IsSemialgebraic.setOf_false
  | apply IsSemialgebraic.setOf_exists
  | apply IsSemialgebraic.setOf_forall
  | apply IsSemialgebraic.setOf_exists_pi
  | apply IsSemialgebraic.setOf_forall_pi
  | (apply IsSemialgebraic.setOf_forall_finite; intro)
  | (apply IsSemialgebraic.setOf_exists_finite; intro)
  | (apply IsSemialgebraic.setOf_lt' <;> (poly_fun; done))
  | (apply IsSemialgebraic.setOf_le' <;> (poly_fun; done))
  | (apply IsSemialgebraic.setOf_eq' <;> (poly_fun; done))
  | (apply IsSemialgebraic.setOf_ne' <;> (poly_fun; done)))

/-- Prove `IsSemialgebraic {x | φ x}` by recursion on the formula `φ`. Leaves unsolved the atoms
it cannot handle. `semialg using h₁, h₂` first tries to close each subgoal with `exact hᵢ`
(for instance graphs of semialgebraic functions, `IsSemialgebraicFun.setOf_graph`). -/
syntax "semialg" (" using " term,+)? : tactic

macro_rules
  | `(tactic| semialg) => `(tactic| repeat' semialg_step)
  | `(tactic| semialg using $ts,*) => do
    let extra ← ts.getElems.mapM fun t => `(Lean.Parser.Tactic.tacticSeq| exact $t)
    `(tactic| repeat' (first $[| $extra]* | semialg_step))

/-- A subset of `ℝ` is semialgebraic if it is semialgebraic as a subset of `ℝ^Unit`. -/
def IsSemialgebraic₁ (S : Set ℝ) : Prop := IsSemialgebraic {x : Unit → ℝ | x () ∈ S}

section Test

example (c : ℝ) :
    IsSemialgebraic {x : Unit → ℝ | ∃ y, ∀ z, 0 < y ∧ (x () - z) ^ 2 * y ≤ c ∨ z = 1} := by
  semialg

example : IsSemialgebraic
    {x : Fin 3 → ℝ | ∀ i, ∃ j, x i ^ 2 < x j + 1 → ∃ y : Fin 2 → ℝ, y 0 = x i} := by
  semialg

end Test
