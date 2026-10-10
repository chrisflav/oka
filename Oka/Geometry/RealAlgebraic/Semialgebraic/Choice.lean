/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Constructions
import Oka.Geometry.RealAlgebraic.Semialgebraic.OneVariable

/-!
# Semialgebraic choice for compact fibres

Let `M : ℝ → Set (ℝ^n)` be a family of sets whose total space `{(u, y) | y ∈ M u}` is
semialgebraic, and suppose `M u` is compact and nonempty for `u` in a semialgebraic set `D`. Then
choosing in each `M u` its lexicographically smallest point (`lexMin`) gives a map `ℝ → ℝ^n`
whose coordinates are semialgebraic functions (`IsSemialgebraicFun.lexMin_coord`).

* `Pi.LexLt` is the strict lexicographic order on `Fin n → ℝ`, written out as a formula so that
  it can be used in semialgebraic definitions;
* `IsCompact.exists_lexMin`: a nonempty compact subset of `ℝ^n` has a lexicographically smallest
  element (minimise the first coordinate, then the second on the minimisers, and so on), which is
  unique (`Pi.LexLt.eq_of_lexMin`).

This is the special case of definable choice needed for the Łojasiewicz inequality; it avoids the
cell decomposition used for general definable choice (van den Dries, *Tame topology*, Ch. 6).
-/

open Set

/-- Strict lexicographic order on `Fin n → ℝ`: `z` is smaller than `y` at the first coordinate
where they differ. -/
def Pi.LexLt {n : ℕ} (z y : Fin n → ℝ) : Prop := ∃ i, (∀ j, j < i → z j = y j) ∧ z i < y i

namespace Pi.LexLt

variable {n : ℕ}

/-- The lexicographic order is irreflexive. -/
theorem irrefl (y : Fin n → ℝ) : ¬ LexLt y y := fun ⟨_, _, h⟩ => lt_irrefl _ h

/-- Totality of the lexicographic order. -/
theorem total {y z : Fin n → ℝ} (hne : y ≠ z) : LexLt y z ∨ LexLt z y := by
  classical
  have hS : (Finset.univ.filter fun i => y i ≠ z i).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at h
    exact hne (funext fun i => not_not.1 (h (Finset.mem_univ i)))
  set i := (Finset.univ.filter fun i => y i ≠ z i).min' hS
  have hi : y i ≠ z i := (Finset.mem_filter.1 ((Finset.univ.filter _).min'_mem hS)).2
  have hj : ∀ j, j < i → y j = z j := by
    intro j hj
    by_contra hne'
    exact absurd ((Finset.univ.filter _).min'_le j (Finset.mem_filter.2 ⟨Finset.mem_univ _, hne'⟩))
      (not_le.2 hj)
  rcases lt_or_gt_of_ne hi with h | h
  · exact Or.inl ⟨i, hj, h⟩
  · exact Or.inr ⟨i, fun j hj' => (hj j hj').symm, h⟩

/-- A lexicographically minimal element of a set is unique. -/
theorem eq_of_lexMin {K : Set (Fin n → ℝ)} {y y' : Fin n → ℝ} (hy : y ∈ K)
    (hmin : ∀ z ∈ K, ¬ LexLt z y) (hy' : y' ∈ K) (hmin' : ∀ z ∈ K, ¬ LexLt z y') : y = y' := by
  by_contra hne
  rcases total hne with h | h
  · exact hmin' y hy h
  · exact hmin y' hy' h

end Pi.LexLt

/-- A nonempty compact subset of `ℝ^n` has a lexicographically smallest element. -/
theorem IsCompact.exists_lexMin {n : ℕ} {K : Set (Fin n → ℝ)} (hK : IsCompact K)
    (hne : K.Nonempty) : ∃ y ∈ K, ∀ z ∈ K, ¬ Pi.LexLt z y := by
  induction n with
  | zero =>
    obtain ⟨y, hy⟩ := hne
    exact ⟨y, hy, fun z _ ⟨i, _⟩ => i.elim0⟩
  | succ n ih =>
    obtain ⟨y₀, hy₀K, hy₀⟩ := hK.exists_isMinOn hne (continuous_apply 0).continuousOn
    set m := y₀ 0
    set K₀ := K ∩ {y | y 0 = m}
    have hK₀ : IsCompact K₀ := hK.inter_right (isClosed_eq (continuous_apply 0) continuous_const)
    set K' := Fin.tail '' K₀
    have hK' : IsCompact K' := hK₀.image (continuous_pi fun i => continuous_apply i.succ)
    obtain ⟨w, ⟨y', ⟨hy'K, hy'0⟩, rfl⟩, hw⟩ := ih hK' ⟨Fin.tail y₀, y₀, ⟨hy₀K, rfl⟩, rfl⟩
    refine ⟨y', hy'K, fun z hz ⟨i, hi, hzi⟩ => ?_⟩
    refine Fin.cases (fun hi hzi => ?_) (fun i hi hzi => ?_) i hi hzi
    · rw [hy'0] at hzi
      exact absurd (hy₀ hz) (not_le.2 hzi)
    · have hz0 : z 0 = y' 0 := hi 0 (Fin.succ_pos i)
      refine hw (Fin.tail z) ⟨z, ⟨hz, hz0.trans hy'0⟩, rfl⟩ ⟨i, fun j hj => ?_, hzi⟩
      exact hi j.succ (Fin.succ_lt_succ_iff.2 hj)

namespace IsSemialgebraicFun

variable {n : ℕ}

/-- The lexicographically smallest point of `M u` when `u ∈ D` (and `0` otherwise). -/
noncomputable def lexMin (D : Set ℝ) (M : ℝ → Set (Fin n → ℝ)) (u : ℝ) : Fin n → ℝ := by
  classical
  exact if h : u ∈ D ∧ IsCompact (M u) ∧ (M u).Nonempty then
    (h.2.1.exists_lexMin h.2.2).choose else 0

/-- For `u ∈ D` with `M u` compact and nonempty, `lexMin D M u` is the lexicographically
smallest point of `M u`. -/
theorem lexMin_spec {D : Set ℝ} {M : ℝ → Set (Fin n → ℝ)} {u : ℝ} (hu : u ∈ D)
    (hc : IsCompact (M u)) (hne : (M u).Nonempty) :
    lexMin D M u ∈ M u ∧ ∀ z ∈ M u, ¬ Pi.LexLt z (lexMin D M u) := by
  have h : u ∈ D ∧ IsCompact (M u) ∧ (M u).Nonempty := ⟨hu, hc, hne⟩
  simp only [lexMin, dif_pos h]
  exact (hc.exists_lexMin hne).choose_spec

/-- **Semialgebraic choice.** If the total space of `M` is semialgebraic and `M u` is compact
and nonempty for `u` in the semialgebraic set `D`, then the coordinates of `lexMin D M` are
semialgebraic functions. -/
theorem lexMin_coord {D : Set ℝ} {M : ℝ → Set (Fin n → ℝ)} (hD : IsSemialgebraic₁ D)
    (hM : IsSemialgebraic {w : Option (Fin n) → ℝ | (fun j => w (some j)) ∈ M (w none)})
    (hMc : ∀ u ∈ D, IsCompact (M u) ∧ (M u).Nonempty) (i : Fin n) :
    IsSemialgebraicFun (fun u => lexMin D M u i) := by
  have hDa : ∀ {ι : Type} {a : ι}, IsSemialgebraic {x : ι → ℝ | x a ∈ D} := fun {ι a} =>
    (IsSemialgebraic.preimage_comp (fun _ : Unit => a) hD).congr rfl
  have hMa : ∀ {ι : Type} {a : ι} {g : Fin n → ι},
      IsSemialgebraic {x : ι → ℝ | (fun j => x (g j)) ∈ M (x a)} := fun {ι a g} =>
    (IsSemialgebraic.preimage_comp (fun o : Option (Fin n) => o.elim a g) hM).congr rfl
  have : IsSemialgebraic {w : Fin 2 → ℝ | (w 0 ∈ D ∧ ∃ y : Fin n → ℝ, y ∈ M (w 0) ∧
      (∀ z : Fin n → ℝ, z ∈ M (w 0) → ¬ ∃ k, (∀ j, j < k → z j = y j) ∧ z k < y k) ∧
      y i = w 1) ∨ (w 0 ∉ D ∧ 0 = w 1)} := by
    semialg using hDa, hMa
  refine this.congr (Set.ext fun w => ?_)
  simp only [mem_setOf_eq]
  by_cases hw : w 0 ∈ D
  · obtain ⟨hc, hne⟩ := hMc _ hw
    obtain ⟨h1, h2⟩ := lexMin_spec hw hc hne
    refine ⟨fun h => ?_, fun h => Or.inl ⟨hw, _, h1, h2, h⟩⟩
    rcases h with ⟨-, y, hy, hymin, hyi⟩ | ⟨h, -⟩
    · rw [← hyi, Pi.LexLt.eq_of_lexMin h1 h2 hy hymin]
    · exact absurd hw h
  · have h0 : lexMin D M (w 0) = 0 := by
      simp only [lexMin, hw, false_and, dif_neg, not_false_eq_true]
    simp [hw, h0, eq_comm]

end IsSemialgebraicFun
