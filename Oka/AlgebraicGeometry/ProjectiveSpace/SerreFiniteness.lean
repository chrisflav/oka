/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.AlgebraicGeometry.Modules.CechModule
import Oka.AlgebraicGeometry.ProjectiveSpace.TwistCohomologyTop
import Oka.AlgebraicGeometry.ProjectiveSpace.SerreVanishing
import Oka.AlgebraicGeometry.ProjectiveSpace.GlobalSectionsFinite
import Oka.Topology.Sheaves.Cohomology.LerayCech

/-!
# Serre's finiteness theorem on projective space

Let `R` be a noetherian ring and `F` a coherent sheaf on `ℙⁿ = ℙ(n; R)`. Then the Čech cohomology
`Ȟᵠ(U, F)` for the standard cover `Uᵢ = D₊(Xᵢ)` is a finitely generated `R`-module for every `q`
(`ProjectiveSpace.cechFinite_of_isCoherent`). Here `R` acts through the constants
`ProjectiveSpace.globalRingHom` (`Scheme.Modules.CechFinite`).

The proof is Serre's descending induction on `q`:

* for `q ≥ n + 1`, `Ȟᵠ(U, F) = 0` for quasi-coherent `F`: sheaf cohomology vanishes in these
  degrees, and the converse direction of Leray's theorem (`TopCat.Sheaf.cech_exactAt_of_H_eq_zero`)
  applies since the `U_σ` are affine;
* `Ȟᵠ(U, O(k))` is finite for all `q` and `k` (`ProjectiveSpace.cechFinite_twistingSheaf`): in
  degree `0` these are the sections `Γ(O(k))`, in positive degrees this is
  `ProjectiveSpace.exists_eq_sum_cechSmul_add_cechD`;
* Theorem A gives `0 → K → ⊕ O(-m) → F → 0` with `K` coherent, which is surjective on the affine
  `U_σ`, and finiteness of `Ȟᵠ(⊕ O(-m))` and `Ȟᵠ⁺¹(K)` gives finiteness of `Ȟᵠ(F)`
  (`Scheme.Modules.cechFinite_X₃`).
-/

universe u

open CategoryTheory Limits TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.Modules
open scoped AlgebraicGeometry.ProjectiveSpace

namespace AlgebraicGeometry.ProjectiveSpace

variable {n : ℕ} {R : Type u} [CommRing R]

local notation "U" => stdCover n R

local notation "ρ" => globalRingHom n R

/-- **Vanishing in high degrees**: for quasi-coherent `F` and `q ≥ n + 1`, the Čech complex of
the standard cover is exact in degree `q`. -/
theorem cech_exactAt_of_le (F : ℙ(n; R).Modules) [F.IsQuasicoherent] (q : ℕ) (hq : n + 1 ≤ q) :
    (cech U F).ExactAt q := by
  obtain ⟨q, rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  exact TopCat.Sheaf.cech_exactAt_of_H_eq_zero U (iSup_stdCover n R) _
    (fun _ σ q x => H_restrictOpen_eq_zero_of_isAffineOpen F (isAffineOpen_cechOpen_stdCover σ)
      q x)
    q (fun x => H_eq_zero_of_le_of_isQuasicoherent F (q + 1) hq x)

lemma cechFinite_of_le (F : ℙ(n; R).Modules) [F.IsQuasicoherent] (q : ℕ) (hq : n + 1 ≤ q) :
    CechFinite U ρ F q :=
  cechFinite_of_exactAt U ρ F q (cech_exactAt_of_le F q hq)

variable [IsNoetherianRing R]

/-- **Čech cohomology of `O(k)` is finite** in every degree. -/
theorem cechFinite_twistingSheaf (k : ℤ) (q : ℕ) : CechFinite U ρ (twistingSheaf n R k) q := by
  cases q with
  | zero =>
    rw [cechFinite_zero_iff U ρ (iSup_stdCover n R)]
    exact finite_sections_twistingSheaf n R k
  | succ p =>
    obtain ⟨N, s, hs⟩ := exists_eq_sum_cechSmul_add_cechD (n := n) (R := R) k p
    have hd (m : ℕ) (z : (cech U (twistingSheaf n R k)).X m) :
        (cech U (twistingSheaf n R k)).d m (m + 1) z =
          TopCat.Presheaf.cechD _ (twistingSheafAb n R k).obj m z :=
      funext (TopCat.Presheaf.cechComplex_d_apply _ _ m z)
    refine cechFinite_of_cocycles U ρ _ p s fun z hz => ?_
    rw [hd] at hz
    obtain ⟨r, c, hzc⟩ := hs z hz
    exact ⟨r, c, by rw [hzc, hd]; rfl⟩

/-- Čech cohomology of `𝒪^I(k) = ⊕_I O(k)` is finite. -/
theorem cechFinite_twist_free {I : Type u} [Finite I] (k : ℤ) (q : ℕ) :
    CechFinite U ρ (twist (SheafOfModules.free I : ℙ(n; R).Modules) k) q :=
  cechFinite_of_iso U ρ (twistFreeIso (n := n) (R := R) I k).symm q
    (cechFinite_sigma U ρ _ q fun _ => cechFinite_twistingSheaf k q)

set_option backward.isDefEq.respectTransparency false in
/-- The descending induction behind Serre's finiteness theorem. -/
theorem cechFinite_aux (k : ℕ) :
    ∀ (F : ℙ(n; R).Modules) [F.IsCoherent] (q : ℕ), n + 1 ≤ q + k → CechFinite U ρ F q := by
  induction k with
  | zero =>
    intro F _ q hq
    haveI := SheafOfModules.IsCoherent.isQuasicoherent F
    exact cechFinite_of_le F q (by omega)
  | succ k ih =>
    intro F _ q hq
    obtain ⟨m₁, hm₁⟩ := exists_epi_twist_free_isCoherent_kernel F
    obtain ⟨I, _, π, _, -, hK⟩ := hm₁ m₁ le_rfl
    let S : ShortComplex ℙ(n; R).Modules :=
      ShortComplex.mk (Limits.kernel.ι π) π (Limits.kernel.condition π)
    have hS : S.ShortExact :=
      ShortComplex.ShortExact.mk' (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel π))
        inferInstance inferInstance
    have hS' : (S.map (SheafOfModules.toSheaf ℙ(n; R).ringCatSheaf)).ShortExact :=
      hS.map_of_exact (Scheme.Modules.toAbFunctor ℙ(n; R))
    haveI := SheafOfModules.IsCoherent.isQuasicoherent (Limits.kernel π)
    have hsurj : ∀ (m : ℕ) (σ : Fin (m + 1) → ULift.{u} (Fin (n + 1))),
        Function.Surjective (S.g.val.app (op (TopCat.Presheaf.cechOpen U σ))) :=
      fun m σ => TopCat.Sheaf.surjective_of_H_one_restrictOpen _ hS'
        (fun x => H_restrictOpen_eq_zero_of_isAffineOpen (Limits.kernel π)
          (isAffineOpen_cechOpen_stdCover σ) 0 x)
    exact cechFinite_X₃ U ρ hS' hsurj q (cechFinite_twist_free _ q)
      (ih (Limits.kernel π) (q + 1) (by omega))

/-- **Serre's finiteness theorem on `ℙⁿ`** (Čech form): for `R` noetherian and `F` coherent on
`ℙ(n; R)`, the Čech cohomology `Ȟᵠ(U, F)` of the standard cover is a finitely generated
`R`-module for every `q`. -/
theorem cechFinite_of_isCoherent (F : ℙ(n; R).Modules) [F.IsCoherent] (q : ℕ) :
    CechFinite U ρ F q :=
  cechFinite_aux (n + 1) F q (by omega)

end AlgebraicGeometry.ProjectiveSpace
