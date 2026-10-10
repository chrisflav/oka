/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.AlgebraicGeometry.ProjectiveSpace.TwistCohomology
import Oka.AlgebraicGeometry.ProjectiveSpace.GlobalSectionsFinite
import Oka.RingTheory.MvPolynomial.CechProjectiveTop

/-!
# The top Čech cohomology of `O(k)` on projective space is finitely generated

For the standard cover `U` of `ℙ(n; R)` (`ProjectiveSpace.stdCover`), the Čech complex of the
twisting sheaf `O(k)` is exact in degree `q ≥ 1`, except in degree `q = n` for `k ≤ -n - 1`
(`ProjectiveSpace.exactAt_cechComplex_twistingSheafAb`). Here we show that in all degrees the
Čech cohomology is generated, as an `R`-module, by finitely many cocycles
(`ProjectiveSpace.exists_eq_sum_cechSmul_add_cechD`).

## The `R`-action on Čech cochains

The `R`-action on cochains is `ProjectiveSpace.cechSmul k r c`, defined pointwise: its component at
`σ` is `(globalRingHom n R r)|_{U_σ} • c σ`, the action of the restriction to the open
`U_σ = cechOpen (stdCover n R) σ` of the constant `r` (a global section of `𝒪`) on the section
`c σ` of the module `O(k)` over `U_σ` (`ProjectiveSpace.cechSmul_apply`). This is the action of
`R` on `Γ(U_σ, O(k))` induced by `globalRingHom n R` and restriction of functions, and it is
compatible with the Laurent coefficients (`ProjectiveSpace.degCechCoeff_cechCochainEquiv_cechSmul`).
We do not register it as an instance.
-/

open CategoryTheory MvPolynomial TopologicalSpace Opposite SimplexCochain
open AlgebraicGeometry.Scheme.Modules
open scoped AlgebraicGeometry.ProjectiveSpace

universe u

namespace AlgebraicGeometry.ProjectiveSpace

variable {n : ℕ} {R : Type u} [CommRing R]

/-- On `UI I`, the constant `r` is the image of `C r` in `A[1 / X_I]`. -/
lemma toAway_restrict_globalRingHom' {I : Finset (Fin (n + 1))} (hI : I.Nonempty) (r : R) :
    toAway I hI (TopCat.Presheaf.restrictOpen (globalRingHom n R r) (UI n R I) le_top) =
      algebraMap (MvPolynomial (Fin (n + 1)) R) _ (C r) := by
  obtain ⟨i, hi⟩ := hI
  have hiI : {i} ⊆ I := Finset.singleton_subset_iff.mpr hi
  have h := toAway_res hiI (Finset.singleton_nonempty i)
    (TopCat.Presheaf.restrictOpen (globalRingHom n R r) (UI n R {i}) le_top)
  rw [toAway_restrict_globalRingHom, TopCat.Presheaf.restrict_restrict] at h
  rw [h]
  exact IsLocalization.lift_eq _ _

/-- Multiplication by `C r` on `A[1 / X_I]` is `r •` on Laurent coefficients. -/
lemma awayCoeff_algebraMap_C_mul (I : Finset (Fin (n + 1))) (r : R)
    (y : Localization.Away (∏ j ∈ I, X j : MvPolynomial (Fin (n + 1)) R)) :
    awayCoeff R I (algebraMap (MvPolynomial (Fin (n + 1)) R) _ (C r) * y) =
      r • awayCoeff R I y := by
  rw [awayCoeff_apply, awayCoeff_apply, map_mul, awayToLaurent_algebraMap,
    ← MvPolynomial.algebraMap_eq, AlgHom.commutes, ← Algebra.smul_def,
    AddMonoidAlgebra.coeff_smul]

variable (k : ℤ)

/-- **The `R`-action on Čech cochains of `O(k)`**: the component at `σ` of `cechSmul k r c` is
`(globalRingHom n R r)|_{U_σ} • c σ`, the action of the constant `r` restricted to
`U_σ = cechOpen (stdCover n R) σ` on the section `c σ` of `O(k)` (see `cechSmul_apply`). -/
noncomputable def cechSmul {p : ℕ} (r : R)
    (c : TopCat.Presheaf.CechCochain (stdCover n R) (twistingSheafAb n R k).obj p) :
    TopCat.Presheaf.CechCochain (stdCover n R) (twistingSheafAb n R k).obj p :=
  fun σ ↦ (TopCat.Presheaf.restrictOpen (globalRingHom n R r)
    (TopCat.Presheaf.cechOpen (stdCover n R) σ) le_top •
      (show Γ(twistingSheaf n R k, TopCat.Presheaf.cechOpen (stdCover n R) σ) from c σ) :
    Γ(twistingSheaf n R k, TopCat.Presheaf.cechOpen (stdCover n R) σ))

lemma cechSmul_apply {p : ℕ} (r : R)
    (c : TopCat.Presheaf.CechCochain (stdCover n R) (twistingSheafAb n R k).obj p)
    (σ : Fin (p + 1) → ULift.{u} (Fin (n + 1))) :
    (cechSmul k r c σ : Γ(twistingSheaf n R k, TopCat.Presheaf.cechOpen (stdCover n R) σ)) =
      TopCat.Presheaf.restrictOpen (globalRingHom n R r)
        (TopCat.Presheaf.cechOpen (stdCover n R) σ) le_top •
        (show Γ(twistingSheaf n R k, TopCat.Presheaf.cechOpen (stdCover n R) σ) from c σ) :=
  rfl

lemma sectionsUIEquiv_restrictOpen_smul {p : ℕ} (r : R)
    (σ : Fin (p + 1) → ULift.{u} (Fin (n + 1)))
    (t : Γ(twistingSheaf n R k, TopCat.Presheaf.cechOpen (stdCover n R) σ)) :
    (sectionsUIEquiv _ k (im_nonempty _) (TopCat.Presheaf.restrictOpen
      (TopCat.Presheaf.restrictOpen (globalRingHom n R r)
        (TopCat.Presheaf.cechOpen (stdCover n R) σ) le_top • t) _
        (cechOpen_stdCover σ).ge)).1 =
      algebraMap (MvPolynomial (Fin (n + 1)) R) _ (C r) *
        (sectionsUIEquiv _ k (im_nonempty _)
          (TopCat.Presheaf.restrictOpen t _ (cechOpen_stdCover σ).ge)).1 := by
  rw [mres_smul, sectionsUIEquiv_smul, TopCat.Presheaf.restrict_restrict,
    toAway_restrict_globalRingHom']

lemma cechSectionsEquiv_cechSmul {p : ℕ} (r : R)
    (c : TopCat.Presheaf.CechCochain (stdCover n R) (twistingSheafAb n R k).obj p)
    (σ : Fin (p + 1) → ULift.{u} (Fin (n + 1))) :
    (cechSectionsEquiv k σ (cechSmul k r c σ)).1 =
      algebraMap (MvPolynomial (Fin (n + 1)) R) _ (C r) * (cechSectionsEquiv k σ (c σ)).1 :=
  sectionsUIEquiv_restrictOpen_smul k r σ (c σ)

/-- The Laurent coefficients of Čech cochains of `O(k)` are `R`-linear for `cechSmul`. -/
lemma degCechCoeff_cechCochainEquiv_cechSmul (p : ℕ) (r : R)
    (c : TopCat.Presheaf.CechCochain (stdCover n R) (twistingSheafAb n R k).obj p) :
    degCechCoeff k p (cechCochainEquiv k p (cechSmul k r c)) =
      r • degCechCoeff k p (cechCochainEquiv k p c) := by
  funext i
  simp only [degCechCoeff, AddMonoidHom.mk'_apply, Pi.smul_apply, cechCochainEquiv_apply]
  rw [cechSectionsEquiv_cechSmul, awayCoeff_algebraMap_C_mul]

/-- The Laurent coefficients of the Čech cochains of `O(k)`. -/
noncomputable def cechCoeff (p : ℕ) :
    TopCat.Presheaf.CechCochain (stdCover n R) (twistingSheafAb n R k).obj p →+
      Cochain (Fin (n + 1)) ((Fin (n + 1) →₀ ℤ) →₀ R) p :=
  AddMonoidHom.mk' (fun c ↦ degCechCoeff k p (cechCochainEquiv k p c)) fun a b ↦ by
    rw [map_add, map_add]

lemma cechCoeff_apply (p : ℕ)
    (c : TopCat.Presheaf.CechCochain (stdCover n R) (twistingSheafAb n R k).obj p) :
    cechCoeff k p c = degCechCoeff k p (cechCochainEquiv k p c) :=
  rfl

/-- **The Čech cohomology of `O(k)` on `ℙ(n; R)` is finitely generated**: for every `k : ℤ` and
`p : ℕ`, there are finitely many `(p + 1)`-cochains `s₀, …, s_{N-1}` of `O(k)` for the standard
cover such that every cocycle `z` is `z = ∑ⱼ rⱼ • sⱼ + d c` for some `rⱼ ∈ R` and a `p`-cochain
`c`, where `R` acts by `cechSmul`. (By `exactAt_cechComplex_twistingSheafAb` one may take
`N = 0` unless `p + 1 = n` and `k ≤ -n - 1`; the statement is uniform in `p` and `k`.) -/
theorem exists_eq_sum_cechSmul_add_cechD (p : ℕ) :
    ∃ (N : ℕ) (s : Fin N →
        TopCat.Presheaf.CechCochain (stdCover n R) (twistingSheafAb n R k).obj (p + 1)),
      ∀ z : TopCat.Presheaf.CechCochain (stdCover n R) (twistingSheafAb n R k).obj (p + 1),
        TopCat.Presheaf.cechD _ _ (p + 1) z = 0 →
        ∃ (r : Fin N → R)
          (c : TopCat.Presheaf.CechCochain (stdCover n R) (twistingSheafAb n R k).obj p),
          z = ∑ j, cechSmul k (r j) (s j) + TopCat.Presheaf.cechD _ _ p c :=
  exists_eq_sum_add_of_laurentPart (ι := Fin (n + 1)) (R := R) (k := k)
    (fun p ↦ TopCat.Presheaf.cechD _ _ p)
    (cechCoeff k)
    (fun p _ _ h ↦ (cechCochainEquiv k p).injective (degCechCoeff_injective k p h))
    (fun p v ↦ by rw [cechCoeff_apply, cechCoeff_apply, cechCochainEquiv_cechD,
      degCechCoeff_degCechD])
    (fun p v i ↦ degCechCoeff_mem k p _ i)
    (fun p x hx ↦ by
      obtain ⟨y, hy⟩ := exists_degCechCoeff_eq k p x hx
      exact ⟨(cechCochainEquiv k p).symm y, by rw [cechCoeff_apply, AddEquiv.apply_symm_apply, hy]⟩)
    p (cechSmul k) (degCechCoeff_cechCochainEquiv_cechSmul k (p + 1))

end AlgebraicGeometry.ProjectiveSpace
