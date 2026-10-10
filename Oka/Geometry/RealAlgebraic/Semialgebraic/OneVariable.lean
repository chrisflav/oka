/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Analysis.Polynomial.SignGap
import Oka.Geometry.RealAlgebraic.Semialgebraic.Definable

/-!
# Semialgebraic subsets of the line and semialgebraic functions of one variable

A semialgebraic subset `S` of `ℝ` is a finite union of points and open intervals. We prove this in
the form used later (*o-minimality* of the semialgebraic structure):

* `IsSemialgebraic₁.exists_finset`: there is a finite set `Z` such that membership in `S` is
  constant on every segment avoiding `Z`;
* `IsSemialgebraic₁.eventually_nhdsGT`, `eventually_nhdsLT`: at every point, `S` either contains
  or avoids a one-sided neighbourhood;
* `IsSemialgebraic₁.exists_Ioo_subset_of_infinite`: an infinite semialgebraic subset of `ℝ`
  contains an open interval.

We also introduce semialgebraic functions `ℝ → ℝ` (`IsSemialgebraicFun`: the graph is a
semialgebraic subset of `ℝ²`), and `IsSemialgebraicFun.setOf_graph`, the atomic formula
`h (x a) = x b`, to be used with the `semialg` tactic.

None of this is in Mathlib.
-/

open Set Filter Topology MvPolynomial

/-- A function `h : ℝ → ℝ` is *semialgebraic* if its graph is a semialgebraic subset of `ℝ²`. -/
def IsSemialgebraicFun (h : ℝ → ℝ) : Prop := IsSemialgebraic {w : Fin 2 → ℝ | h (w 0) = w 1}

/-- The atomic formula `h (x a) = x b` for a semialgebraic function `h`. -/
theorem IsSemialgebraicFun.setOf_graph {h : ℝ → ℝ} (hh : IsSemialgebraicFun h) {ι : Type*}
    {a b : ι} : IsSemialgebraic {x : ι → ℝ | h (x a) = x b} :=
  (IsSemialgebraic.preimage_comp ![a, b] hh).congr (by ext x; simp)

/-- A finite set `Z ⊆ ℝ` has, to the right of every point `a`, an interval `(a, b)` disjoint
from `Z`. -/
lemma Finset.exists_gt_forall_notMem_Ioo (Z : Finset ℝ) (a : ℝ) :
    ∃ b, a < b ∧ ∀ z ∈ Z, z ∉ Set.Ioo a b := by
  classical
  by_cases h : (Z.filter (a < ·)).Nonempty
  · refine ⟨(Z.filter (a < ·)).min' h, (Finset.mem_filter.1 ((Z.filter _).min'_mem h)).2,
      fun z hz hzI => ?_⟩
    exact absurd ((Z.filter (a < ·)).min'_le z (Finset.mem_filter.2 ⟨hz, hzI.1⟩))
      (not_le.2 hzI.2)
  · refine ⟨a + 1, by linarith, fun z hz hzI => h ⟨z, Finset.mem_filter.2 ⟨hz, hzI.1⟩⟩⟩

/-- A finite set `Z ⊆ ℝ` has, to the left of every point `a`, an interval `(b, a)` disjoint
from `Z`. -/
lemma Finset.exists_lt_forall_notMem_Ioo (Z : Finset ℝ) (a : ℝ) :
    ∃ b, b < a ∧ ∀ z ∈ Z, z ∉ Set.Ioo b a := by
  classical
  by_cases h : (Z.filter (· < a)).Nonempty
  · refine ⟨(Z.filter (· < a)).max' h, (Finset.mem_filter.1 ((Z.filter _).max'_mem h)).2,
      fun z hz hzI => ?_⟩
    exact absurd ((Z.filter (· < a)).le_max' z (Finset.mem_filter.2 ⟨hz, hzI.2⟩))
      (not_le.2 hzI.1)
  · refine ⟨a - 1, by linarith, fun z hz hzI => h ⟨z, Finset.mem_filter.2 ⟨hz, hzI.2⟩⟩⟩

namespace IsSemialgebraic₁

variable {S : Set ℝ}

/-- Unfolding `IsSemialgebraic₁`. -/
lemma iff : IsSemialgebraic₁ S ↔ IsSemialgebraic {x : Unit → ℝ | x () ∈ S} := Iff.rfl

/-- Transport semialgebraicity along an equality of sets. -/
lemma congr {T : Set ℝ} (h : IsSemialgebraic₁ S) (hST : S = T) : IsSemialgebraic₁ T := hST ▸ h

private lemma eval_univ (p : MvPolynomial Unit ℝ) (t : ℝ) :
    (aeval (fun _ => Polynomial.X) p : Polynomial ℝ).eval t = eval (fun _ => t) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

/-- A semialgebraic subset of `ℝ` is a union of gaps of a finite set: there is a finite `Z` such
that membership is constant along every segment avoiding `Z`. -/
theorem exists_finset (hS : IsSemialgebraic₁ S) :
    ∃ Z : Finset ℝ, ∀ y y', (∀ z ∈ Z, z ∉ uIcc y y') → y ∈ S → y' ∈ S := by
  classical
  obtain ⟨F, hF⟩ := hS
  refine ⟨F.biUnion (fun p => (aeval (fun _ => Polynomial.X) p : Polynomial ℝ).roots.toFinset),
    fun y y' hfree hy => hF (fun _ => y) (fun _ => y') (fun p hp => ?_) hy⟩
  rw [← eval_univ, ← eval_univ]
  set P := (aeval (fun _ => Polynomial.X) p : Polynomial ℝ)
  by_cases hP : P = 0
  · simp [hP]
  refine Polynomial.sign_eval_eq_of_forall_ne_zero P (fun t ht h0 => hfree t ?_ ht)
  exact Finset.mem_biUnion.2 ⟨p, hp, Multiset.mem_toFinset.2 ((Polynomial.mem_roots hP).2 h0)⟩

/-- Membership is constant on an open interval avoiding the exceptional finite set. -/
private lemma mem_iff_of_free {Z : Finset ℝ}
    (hZ : ∀ y y', (∀ z ∈ Z, z ∉ uIcc y y') → y ∈ S → y' ∈ S) {a b : ℝ}
    (hfree : ∀ z ∈ Z, z ∉ Ioo a b) {s t : ℝ} (hs : s ∈ Ioo a b) (ht : t ∈ Ioo a b) :
    s ∈ S ↔ t ∈ S := by
  have h1 : ∀ z ∈ Z, z ∉ uIcc s t := fun z hz hzI =>
    hfree z hz (ordConnected_Ioo.uIcc_subset hs ht hzI)
  refine ⟨hZ s t h1, hZ t s fun z hz hzI => h1 z hz ?_⟩
  rwa [uIcc_comm]

/-- At every point, a semialgebraic subset of `ℝ` contains or avoids a right neighbourhood. -/
theorem eventually_nhdsGT (hS : IsSemialgebraic₁ S) (a : ℝ) :
    (∀ᶠ t in 𝓝[>] a, t ∈ S) ∨ ∀ᶠ t in 𝓝[>] a, t ∉ S := by
  obtain ⟨Z, hZ⟩ := hS.exists_finset
  obtain ⟨b, hab, hfree⟩ := Z.exists_gt_forall_notMem_Ioo a
  have hc : (a + b) / 2 ∈ Ioo a b := ⟨by linarith, by linarith⟩
  by_cases hcS : (a + b) / 2 ∈ S
  · exact Or.inl (Filter.mem_of_superset (Ioo_mem_nhdsGT hab)
      fun t ht => (mem_iff_of_free hZ hfree hc ht).1 hcS)
  · exact Or.inr (Filter.mem_of_superset (Ioo_mem_nhdsGT hab)
      fun t ht h => hcS ((mem_iff_of_free hZ hfree hc ht).2 h))

/-- At every point, a semialgebraic subset of `ℝ` contains or avoids a left neighbourhood. -/
theorem eventually_nhdsLT (hS : IsSemialgebraic₁ S) (a : ℝ) :
    (∀ᶠ t in 𝓝[<] a, t ∈ S) ∨ ∀ᶠ t in 𝓝[<] a, t ∉ S := by
  obtain ⟨Z, hZ⟩ := hS.exists_finset
  obtain ⟨b, hab, hfree⟩ := Z.exists_lt_forall_notMem_Ioo a
  have hc : (a + b) / 2 ∈ Ioo b a := ⟨by linarith, by linarith⟩
  by_cases hcS : (a + b) / 2 ∈ S
  · exact Or.inl (Filter.mem_of_superset (Ioo_mem_nhdsLT hab)
      fun t ht => (mem_iff_of_free hZ hfree hc ht).1 hcS)
  · exact Or.inr (Filter.mem_of_superset (Ioo_mem_nhdsLT hab)
      fun t ht h => hcS ((mem_iff_of_free hZ hfree hc ht).2 h))

/-- An infinite semialgebraic subset of `ℝ` contains an open interval. -/
theorem exists_Ioo_subset_of_infinite (hS : IsSemialgebraic₁ S) (hinf : S.Infinite) :
    ∃ a b, a < b ∧ Ioo a b ⊆ S := by
  obtain ⟨Z, hZ⟩ := hS.exists_finset
  obtain ⟨y, hyS, hyZ⟩ := (hinf.sdiff Z.finite_toSet).nonempty
  obtain ⟨b, hyb, hb⟩ := Z.exists_gt_forall_notMem_Ioo y
  obtain ⟨a, hay, ha⟩ := Z.exists_lt_forall_notMem_Ioo y
  have hfree : ∀ z ∈ Z, z ∉ Ioo a b := by
    intro z hz hzI
    rcases lt_trichotomy z y with h | rfl | h
    · exact ha z hz ⟨hzI.1, h⟩
    · exact hyZ hz
    · exact hb z hz ⟨h, hzI.2⟩
  exact ⟨a, b, hay.trans hyb, fun t ht => (mem_iff_of_free hZ hfree ⟨hay, hyb⟩ ht).1 hyS⟩

/-- A semialgebraic subset of `ℝ` containing no open interval is finite. -/
theorem finite_of_forall_not_Ioo_subset (hS : IsSemialgebraic₁ S)
    (h : ∀ a b, a < b → ¬ Ioo a b ⊆ S) : S.Finite := by
  by_contra hinf
  obtain ⟨a, b, hab, hsub⟩ := hS.exists_Ioo_subset_of_infinite hinf
  exact h a b hab hsub

end IsSemialgebraic₁
