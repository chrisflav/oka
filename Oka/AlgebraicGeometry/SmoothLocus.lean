/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Oka.RingTheory.SmoothCodimOne

/-!
# The smooth locus contains the normal points of codimension at most one

Let `K` be a field of characteristic zero and `f : X ⟶ Spec K` locally of finite presentation.
A point `x` of `X` with an affine open neighbourhood whose ring of sections is an integrally closed
domain lies in the smooth locus of `f` as soon as `𝒪_{X,x}` has dimension at most one
(`AlgebraicGeometry.Scheme.Hom.mem_smoothLocus_of_ringKrullDim_le_one`).
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- **Normal points of codimension at most one are smooth.** Let `K` be a field of characteristic
zero, `f : X ⟶ Spec K` locally of finite presentation and `x ∈ V` for an affine open `V` whose ring
of sections is an integrally closed domain. If `𝒪_{X,x}` has dimension at most one, then `x` lies in
the smooth locus of `f`. -/
theorem Scheme.Hom.mem_smoothLocus_of_ringKrullDim_le_one {X : Scheme.{u}} {K : Type u} [Field K]
    [CharZero K] (f : X ⟶ Spec (.of K)) [LocallyOfFinitePresentation f] {x : X} {V : X.Opens}
    (hV : IsAffineOpen V) (hx : x ∈ V) [IsDomain Γ(X, V)] [IsIntegrallyClosed Γ(X, V)]
    (h : ringKrullDim (X.presheaf.stalk x) ≤ 1) : x ∈ f.smoothLocus := by
  have hVU : V ≤ f ⁻¹ᵁ ⊤ := by simp
  have := f.finitePresentation_appLE (isAffineOpen_top _) hV hVU
  algebraize [(f.appLE ⊤ V hVU).hom]
  let q := (hV.primeIdealOf ⟨x, hx⟩).asIdeal
  haveI : IsIntegrallyClosed (Localization.AtPrime q) :=
    isIntegrallyClosed_of_isLocalization _ q.primeCompl q.primeCompl_le_nonZeroDivisors
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hx⟩ : V)
  haveI := hV.isLocalization_stalk ⟨x, hx⟩
  have hdim : ringKrullDim (Localization.AtPrime q) ≤ 1 := by
    rwa [ringKrullDim_eq_of_ringEquiv
      (IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q)
        (X.presheaf.stalk x)).toRingEquiv]
  let e : Γ(Spec (.of K), ⊤) ≃+* K := (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv
  haveI : CharZero Γ(Spec (.of K), ⊤) :=
    charZero_of_injective_ringHom (f := e.symm.toRingHom) e.symm.injective
  have hsm : Algebra.IsSmoothAt Γ(Spec (.of K), ⊤) q :=
    Algebra.isSmoothAt_of_ringKrullDim_le_one_of_isField
      (e.toMulEquiv.isField (Field.toIsField K)) q hdim
  exact (formallySmooth_stalkMap_iff ⊤ (isAffineOpen_top _) V hV hVU hx).mpr hsm

end AlgebraicGeometry
