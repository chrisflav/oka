/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Topology.Sheaves.Cohomology.Leray
import Oka.Topology.Sheaves.Cohomology.CechDegreeOne

/-!
# Leray's theorem, converse direction: sheaf vanishing implies Čech vanishing

Let `U` be an open cover of `X` and `F` an abelian sheaf with `Hᵖ(U_σ, F) = 0` for `p ≥ 1` on all
finite intersections `U_σ`. If `Hᵠ⁺¹(X, F) = 0`, then the Čech complex `Č•(U, F)` is exact in
degree `q + 1` (`TopCat.Sheaf.cech_exactAt_of_H_eq_zero`).

The proof is dimension shifting along `0 → F → I(F) → Q → 0` (`TopCat.Sheaf.injSES`), as in
`TopCat.Sheaf.H_eq_zero_of_isCechAcyclic`: the sequence of Čech complexes is short exact since
`H¹(U_σ, F) = 0`, `Č•(U, I(F))` is acyclic, and `Q` again has vanishing higher cohomology on the
`U_σ`. The base case `q = 0` is the injectivity of the comparison map
`H¹(U, F) → H¹(X, F)` (`TopCat.Sheaf.cechHomologyToH_injective`).

Together with the vanishing form of Leray's theorem this shows that Čech cohomology for such a cover
vanishes exactly where sheaf cohomology does.
-/

universe u

open CategoryTheory Limits TopologicalSpace Opposite

namespace TopCat.Sheaf

open TopCat.Presheaf

variable {X : TopCat.{u}} {ι : Type u} (U : ι → Opens X)

/-- **Leray, converse direction.** Let `U` cover `X` and let `F` have vanishing higher cohomology
on all finite intersections `U_σ`. If `Hᵠ⁺¹(X, F) = 0` then the Čech complex `Č•(U, F)` is exact
in degree `q + 1`. -/
theorem cech_exactAt_of_H_eq_zero (hU : ⨆ i, U i = ⊤) (F : AbSheaf X)
    (hF : ∀ (n : ℕ) (σ : Fin (n + 1) → ι) (q : ℕ)
      (x : H ((restrictOpen (cechOpen U σ)).obj F) (q + 1)), x = 0)
    (q : ℕ) (hq : ∀ x : H F (q + 1), x = 0) : (cechComplex U F.obj).ExactAt (q + 1) := by
  induction q generalizing F with
  | zero =>
    rw [HomologicalComplex.exactAt_iff_isZero_homology,
      AddCommGrpCat.isZero_iff_subsingleton]
    refine ⟨fun a b => cechHomologyToH_injective hU F ?_⟩
    rw [hq (cechHomologyToH hU F a), hq (cechHomologyToH hU F b)]
  | succ q ih =>
    let S := injSES F
    have hS : S.ShortExact := injSES_shortExact F
    have hsurj : ∀ (n : ℕ) (σ : Fin (n + 1) → ι),
        Function.Surjective (S.g.hom.app (op (cechOpen U σ))) :=
      fun n σ => surjective_of_H_one_restrictOpen _ hS (hF n σ 0)
    have hT := cechComplex_shortExact_of_sheaf hS hsurj
    have hQ : (cechComplex U S.X₃.obj).ExactAt (q + 1) :=
      ih S.X₃
        (fun n σ q' z' => H_succ_restrictOpen_eq_zero_of_H_succ_succ _ hS (hF n σ (q' + 1)) z')
        (fun z => H_succ_eq_zero_of_H_succ_succ hS hq z)
    have hI : (cechComplex U S.X₂.obj).ExactAt (q + 2) :=
      isCechAcyclic_of_injective_sheaf U S.X₂ (q + 1)
    have e := hT.homology_exact₁ (q + 1) (q + 2) (by simp)
    rw [HomologicalComplex.exactAt_iff_isZero_homology] at hQ hI ⊢
    exact e.isZero_X₂ (hQ.eq_of_src _ _) (hI.eq_of_tgt _ _)

end TopCat.Sheaf
