/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Tactic.LinearCombination

/-!
# Pseudo-division of polynomials over a domain

Over an integral domain `A`, a polynomial `p` can be divided by a non-constant `q` after
multiplying `p` by a power of the leading coefficient of `q`:
`C q.leadingCoeff ^ k * p = a * q + r` with `r.natDegree < q.natDegree`
(`Polynomial.exists_pseudoDivision`).

Mathlib has division with remainder by monic polynomials (`Polynomial.modByMonic`) and over fields
(`Polynomial.mod`), but no pseudo-division. Only the existence statement is proved here; it is
used in the proof of the Tarski–Seidenberg theorem, where the coefficient ring is a polynomial
ring `MvPolynomial ι ℝ` and the remainder must stay polynomial in the parameters.
-/

namespace Polynomial

variable {A : Type*} [CommRing A] [IsDomain A]

/-- **Pseudo-division.** For `q` of positive degree over a domain, some power of the leading
coefficient of `q` times `p` is congruent modulo `q` to a polynomial of smaller degree than `q`. -/
theorem exists_pseudoDivision (p q : A[X]) (hq : 1 ≤ q.natDegree) :
    ∃ (k : ℕ) (a r : A[X]), C q.leadingCoeff ^ k * p = a * q + r ∧ r.natDegree < q.natDegree := by
  induction h : p.natDegree using Nat.strong_induction_on generalizing p with
  | _ n ih =>
  by_cases hlt : p.natDegree < q.natDegree
  · exact ⟨0, 0, p, by simp, hlt⟩
  replace hlt := not_lt.1 hlt
  have hq0 : q ≠ 0 := by rintro rfl; simp at hq
  have hp0 : p ≠ 0 := by rintro rfl; simp at hlt; omega
  have hlq : q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hq0
  have hlp : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hp0
  set m := p.natDegree - q.natDegree
  set p₁ := C q.leadingCoeff * p - C p.leadingCoeff * X ^ m * q with hp₁
  have hdeg₁ : p₁.natDegree < p.natDegree := by
    by_cases h0 : p₁ = 0
    · rw [h0, natDegree_zero]; omega
    have hA : (C q.leadingCoeff * p).degree = p.degree := degree_C_mul hlq
    have hB : (C p.leadingCoeff * X ^ m * q).degree = p.degree := by
      rw [degree_mul, degree_C_mul_X_pow _ hlp, degree_eq_natDegree hq0,
        degree_eq_natDegree hp0, ← Nat.cast_add, Nat.sub_add_cancel hlt]
    have hlc : (C q.leadingCoeff * p).leadingCoeff = (C p.leadingCoeff * X ^ m * q).leadingCoeff :=
      by
      rw [leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_C, leadingCoeff_C,
        leadingCoeff_X_pow]
      ring
    have hlt' : p₁.degree < p.degree := by
      rw [hp₁, ← hA]
      exact degree_sub_lt (hA.trans hB.symm) (by simp [hlq, hp0]) hlc
    exact natDegree_lt_natDegree h0 hlt'
  obtain ⟨k, a, r, hk, hr⟩ := ih _ (h ▸ hdeg₁) p₁ rfl
  refine ⟨k + 1, a + C q.leadingCoeff ^ k * C p.leadingCoeff * X ^ m, r, ?_, hr⟩
  rw [hp₁] at hk
  linear_combination hk

end Polynomial
