/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.ES.SeparatedLocal

/-!
# Separated covers over finite disjoint unions of affine schemes

Let `X` be an affine scheme locally of finite type over `ℂ` with `Γ(X, 𝒪_X) ≅ ∏ᵢ Dᵢ`, a finite
product. The basic opens `D(eᵢ)` of the corresponding idempotents cover `X`, and
`Γ(D(eᵢ), 𝒪_X) ≅ Dᵢ` is the localisation at `eᵢ`. By Zariski-locality,
`ComplexAnalytic.SeparatedCoversAlgebraic X` follows from the same statement for all affine
schemes with ring of global sections isomorphic to some `Dᵢ`
(`ComplexAnalytic.SeparatedCoversAlgebraic.of_ringEquiv_pi`).
-/

open CategoryTheory AlgebraicGeometry

universe u

namespace ComplexAnalytic

variable {ι : Type u} (D : ι → Type u) [∀ i, CommRing (D i)] {R : Type u} [CommRing R]
  (e : R ≃+* ∀ i, D i)

/-- The idempotent of `R ≅ ∏ᵢ Dᵢ` with components `δᵢⱼ`. -/
def piIdempotent [DecidableEq ι] (i : ι) : R :=
  e.symm (Pi.single i 1)

lemma isIdempotentElem_piIdempotent [DecidableEq ι] (i : ι) :
    IsIdempotentElem (piIdempotent D e i) := by
  refine e.injective ?_
  simp [piIdempotent, ← Pi.single_mul_left]

lemma span_range_piIdempotent [DecidableEq ι] [Finite ι] :
    Ideal.span (Set.range (piIdempotent D e)) = ⊤ := by
  haveI := Fintype.ofFinite ι
  rw [Ideal.eq_top_iff_one]
  have h1 : (1 : R) = ∑ i, piIdempotent D e i := by
    refine e.injective ?_
    simp only [map_one, map_sum, piIdempotent, RingEquiv.apply_symm_apply]
    exact (Finset.univ_sum_single (1 : ∀ i, D i)).symm
  rw [h1]
  exact Ideal.sum_mem _ fun i _ ↦ Ideal.subset_span ⟨i, rfl⟩

/-- `Dᵢ` is the localisation of `R ≅ ∏ᵢ Dᵢ` away from the idempotent `eᵢ`. -/
lemma isLocalization_away_piIdempotent [DecidableEq ι] (i : ι) :
    letI := ((Pi.evalRingHom D i).comp e.toRingHom).toAlgebra
    IsLocalization.Away (piIdempotent D e i) (D i) := by
  letI := ((Pi.evalRingHom D i).comp e.toRingHom).toAlgebra
  refine IsLocalization.away_of_isIdempotentElem_of_mul (isIdempotentElem_piIdempotent D e i)
    (fun x y ↦ ?_) fun d ↦ ⟨e.symm (Pi.single i d), by
      change e (e.symm (Pi.single i d)) i = d
      simp⟩
  change e x i = e y i ↔ _
  rw [← e.injective.eq_iff, map_mul, map_mul, piIdempotent, e.apply_symm_apply]
  refine ⟨fun hxy ↦ funext fun j ↦ ?_, fun hxy ↦ by simpa using congrFun hxy i⟩
  by_cases hj : j = i
  · subst hj
    simp [hxy]
  · simp [hj]

/-- **Finite products**: if `Γ(X, 𝒪_X) ≅ ∏ᵢ Dᵢ` for a finite family of rings, and every affine
scheme with ring of global sections isomorphic to some `Dᵢ` satisfies
`SeparatedCoversAlgebraic`, then so does `X`. -/
theorem SeparatedCoversAlgebraic.of_ringEquiv_pi (X : SchemeLFTℂ.{u}) [IsAffine X.obj.left]
    [Finite ι] (e : Γ(X.obj.left, ⊤) ≃+* ∀ i, D i)
    (h : ∀ (i : ι) (Y : SchemeLFTℂ.{u}) [IsAffine Y.obj.left],
      Nonempty (Γ(Y.obj.left, ⊤) ≃+* D i) → SeparatedCoversAlgebraic Y) :
    SeparatedCoversAlgebraic X := by
  classical
  haveI := Fintype.ofFinite ι
  let f := piIdempotent D e
  have hcov : ⨆ i, X.obj.left.basicOpen (f i) = ⊤ := by
    have h' := ((isAffineOpen_top X.obj.left).iSup_basicOpen_eq_self_iff
      (s := Set.range f)).2 (span_range_piIdempotent D e)
    rwa [iSup_range' (fun g ↦ X.obj.left.basicOpen g) f] at h'
  refine SeparatedCoversAlgebraic.of_cover _ hcov fun i ↦ ?_
  haveI : IsAffine (X.restrict (X.obj.left.basicOpen (f i))).obj.left :=
    (isAffineOpen_top X.obj.left).basicOpen (f i)
  refine h i _ ⟨?_⟩
  letI := ((Pi.evalRingHom D i).comp e.toRingHom).toAlgebra
  haveI := isLocalization_away_piIdempotent D e i
  haveI := (isAffineOpen_top X.obj.left).isLocalization_basicOpen (f i)
  exact (Scheme.Opens.topIso _).commRingCatIsoToRingEquiv.trans
    (IsLocalization.algEquiv (Submonoid.powers (f i)) _ (D i)).toRingEquiv

end ComplexAnalytic
