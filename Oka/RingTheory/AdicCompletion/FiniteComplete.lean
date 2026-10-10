/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Henselian

/-!
# Finite modules over complete noetherian local rings are complete

Let `R` be a noetherian local ring which is complete for its maximal ideal `𝔪`. Every finite
`R`-module `M` is `𝔪`-adically complete (`IsAdicComplete.of_finite`): Hausdorffness is Krull's
intersection theorem, and precompleteness follows from the surjectivity of
`R^ ⊗ M → M^` (`AdicCompletion.ofTensorProduct_surjective_of_finite`) and `R^ = R`.

As a consequence, a finite `R`-algebra `A` which is a domain has no nontrivial idempotents modulo
`𝔪A` (`eq_zero_or_eq_one_mod_of_finite`): `A` is `𝔪A`-adically complete, hence Henselian at
`𝔪A`, and an idempotent of `A ⧸ 𝔪A` lifts to an idempotent of `A`, which is `0` or `1`.
-/

open IsLocalRing Polynomial

namespace IsAdicComplete

variable {R : Type*} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
  (M : Type*) [AddCommGroup M] [Module R M]

omit [IsAdicComplete I R] in
lemma of_smul_of (r : R) (x : M) :
    AdicCompletion.of I R r • AdicCompletion.of I M x = AdicCompletion.of I M (r • x) := by
  rw [map_smul]
  ext n
  rfl

/-- A finite module over an `I`-adically complete ring is `I`-adically precomplete. -/
theorem isPrecomplete_of_finite [Module.Finite R M] : IsPrecomplete I M := by
  rw [← AdicCompletion.of_surjective_iff]
  intro ξ
  obtain ⟨y, rfl⟩ := AdicCompletion.ofTensorProduct_surjective_of_finite I M ξ
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul r x =>
    obtain ⟨s, rfl⟩ := (AdicCompletion.of_surjective I R) r
    exact ⟨s • x, by rw [AdicCompletion.ofTensorProduct_tmul, of_smul_of]⟩
  | add y z hy hz =>
    obtain ⟨a, ha⟩ := hy
    obtain ⟨b, hb⟩ := hz
    exact ⟨a + b, by rw [map_add, ha, hb, map_add]⟩

/-- **A finite module over a complete noetherian local ring is complete.** -/
theorem of_finite [IsNoetherianRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R]
    [Module.Finite R M] : IsAdicComplete (maximalIdeal R) M where
  toIsHausdorff := inferInstance
  toIsPrecomplete := isPrecomplete_of_finite _ M

end IsAdicComplete

/-- **No nontrivial idempotents modulo `𝔪`.** Let `R` be a complete noetherian local ring and `A`
a finite `R`-algebra which is a domain. If `a ∈ A` is idempotent modulo `𝔪A`, then `a ∈ 𝔪A` or
`1 - a ∈ 𝔪A`. -/
theorem eq_zero_or_eq_one_mod_of_finite {R A : Type*} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R] [CommRing A] [IsDomain A] [Algebra R A]
    [Module.Finite R A] (a : A) (ha : a * a - a ∈ (maximalIdeal R).map (algebraMap R A)) :
    a ∈ (maximalIdeal R).map (algebraMap R A) ∨
      1 - a ∈ (maximalIdeal R).map (algebraMap R A) := by
  set I := (maximalIdeal R).map (algebraMap R A)
  haveI : IsAdicComplete (maximalIdeal R) A := IsAdicComplete.of_finite A
  haveI : IsAdicComplete I A :=
    { toIsHausdorff := IsHausdorff.map_algebraMap_iff.mpr inferInstance
      toIsPrecomplete := IsPrecomplete.map_algebraMap_iff.mpr inferInstance }
  let f : A[X] := X ^ 2 - X
  have hf : f.Monic := (monic_X_pow 2).sub_of_left (by rw [degree_X, degree_X_pow]; norm_num)
  have hfa : f.eval a ∈ I := by simpa [f, sq] using ha
  have hunit : IsUnit (Ideal.Quotient.mk I (f.derivative.eval a)) := by
    have hder : f.derivative.eval a = 2 * a - 1 := by
      simp only [f, derivative_sub, derivative_X_pow, derivative_X, eval_sub, eval_mul, eval_C,
        eval_X, eval_one, eval_pow]
      push_cast
      ring
    rw [hder]
    refine isUnit_iff_exists_inv.mpr ⟨Ideal.Quotient.mk I (2 * a - 1), ?_⟩
    rw [← map_mul, ← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq]
    have : (2 * a - 1) * (2 * a - 1) - 1 = 4 * (a * a - a) := by ring
    rw [this]
    exact I.mul_mem_left _ ha
  obtain ⟨b, hb, hba⟩ := HenselianRing.is_henselian f hf a hfa hunit
  have hb' : b * (b - 1) = 0 := by
    have := hb.eq_zero
    simp only [f, eval_sub, eval_pow, eval_X] at this
    linear_combination this
  rcases mul_eq_zero.mp hb' with h | h
  · left
    have : a = -(b - a) := by rw [h]; ring
    rw [this]
    exact I.neg_mem hba
  · right
    have : 1 - a = b - a := by linear_combination -h
    rw [this]
    exact hba
