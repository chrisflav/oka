/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.ES.NormalToSmooth
import Oka.RingTheory.NormalDepthTwo

/-!
# Complements of codimension two in affine schemes

For an affine scheme `X` and a point `x`, `ComplexAnalytic.pointIdeal X x` is the prime of
`Γ(X, 𝒪_X)` corresponding to `x`. If the complement of an open `U` has codimension at least two,
every prime containing the ideal `ComplexAnalytic.complIdeal U` of functions vanishing off `U`
has height at least two (`ComplexAnalytic.two_le_height_of_complIdeal_le`).
-/

open CategoryTheory Opposite AlgebraicGeometry

universe u

namespace ComplexAnalytic

noncomputable section

variable {X : Scheme.{u}} [IsAffine X]

/-- The prime of `Γ(X, 𝒪_X)` of a point of an affine scheme. -/
def pointIdeal (x : X) : Ideal Γ(X, ⊤) :=
  ((isAffineOpen_top X).primeIdealOf ⟨x, trivial⟩).asIdeal

instance (x : X) : (pointIdeal x).IsPrime :=
  ((isAffineOpen_top X).primeIdealOf ⟨x, trivial⟩).isPrime

lemma isLocalization_stalk_pointIdeal (x : X) :
    letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, trivial⟩ : (⊤ : X.Opens))
    IsLocalization.AtPrime (X.presheaf.stalk x) (pointIdeal x) :=
  (isAffineOpen_top X).isLocalization_stalk ⟨x, trivial⟩

lemma mem_pointIdeal_iff (x : X) (a : Γ(X, ⊤)) : a ∈ pointIdeal x ↔ x ∉ X.basicOpen a := by
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, trivial⟩ : (⊤ : X.Opens))
  haveI := isLocalization_stalk_pointIdeal x
  rw [Scheme.mem_basicOpen X a x trivial]
  change _ ↔ ¬ IsUnit (algebraMap Γ(X, ⊤) (X.presheaf.stalk x) a)
  rw [IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk x) (pointIdeal x),
    Ideal.mem_primeCompl_iff, not_not]

lemma ringKrullDim_stalk_eq_height (x : X) :
    ringKrullDim (X.presheaf.stalk x) = (pointIdeal x).height := by
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, trivial⟩ : (⊤ : X.Opens))
  haveI := isLocalization_stalk_pointIdeal x
  exact IsLocalization.AtPrime.ringKrullDim_eq_height (pointIdeal x) (X.presheaf.stalk x)

lemma exists_pointIdeal_eq (P : Ideal Γ(X, ⊤)) [hP : P.IsPrime] : ∃ x : X, pointIdeal x = P := by
  let hU := isAffineOpen_top X
  refine ⟨(hU.isoSpec.inv.base ⟨P, hP⟩ : (⊤ : X.Opens)).1, ?_⟩
  change ((isAffineOpen_top X).isoSpec.hom.base (hU.isoSpec.inv.base ⟨P, hP⟩)).asIdeal = P
  rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]
  rfl

/-- The ideal of functions vanishing off `U`. -/
def complIdeal (U : X.Opens) : Ideal Γ(X, ⊤) :=
  ⨅ (x : X) (_ : x ∉ U), pointIdeal x

lemma mem_complIdeal_iff (U : X.Opens) (a : Γ(X, ⊤)) :
    a ∈ complIdeal U ↔ ∀ x : X, x ∉ U → a ∈ pointIdeal x := by
  simp [complIdeal, Submodule.mem_iInf]

/-- **Primes containing the ideal of the complement lie over the complement**: a prime containing
`complIdeal U` is the prime of a point outside `U`. -/
lemma not_mem_of_complIdeal_le {U : X.Opens} {x : X} (h : complIdeal U ≤ pointIdeal x) :
    x ∉ U := by
  intro hx
  obtain ⟨a, haU, hxa⟩ := (isAffineOpen_top X).exists_basicOpen_le (V := U) ⟨x, hx⟩ trivial
  have ha : a ∈ complIdeal U := (mem_complIdeal_iff U a).2 fun y hy ↦
    (mem_pointIdeal_iff y a).2 fun hya ↦ hy (haU hya)
  exact (mem_pointIdeal_iff x a).1 (h ha) hxa

/-- **Primes containing the ideal of a complement of codimension two have height at least two.** -/
theorem two_le_height_of_complIdeal_le {U : X.Opens} (hU : HasCodimTwoComplement U)
    (P : Ideal Γ(X, ⊤)) [P.IsPrime] (hP : complIdeal U ≤ P) : 2 ≤ P.height := by
  obtain ⟨x, rfl⟩ := exists_pointIdeal_eq P
  have h := hU x (not_mem_of_complIdeal_le hP)
  rw [ringKrullDim_stalk_eq_height] at h
  exact WithBot.coe_le_coe.1 h

/-- The ideal of functions vanishing at a point of `X^an` is the prime of its image in `X`. -/
lemma idealOfPoint_eq_pointIdeal (X : SchemeLFTℂ.{u}) [IsAffine X.obj.left]
    (v : analytification.obj X) :
    idealOfPoint X v = pointIdeal ((analytificationπLRS X).base v) := by
  rw [idealOfPoint_eq, pointIdeal, (isAffineOpen_top X.obj.left).primeIdealOf_eq_map_closedPoint]
  rfl

end

end ComplexAnalytic
