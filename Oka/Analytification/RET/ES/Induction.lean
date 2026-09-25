/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.ES.DimZero
import Oka.Analytification.RET.ES.NormalizationInCover
import Oka.Analytification.RET.ES.SmoothLocus

/-!
# Separated finite étale covers of affine schemes of any dimension

Assuming coherence of bounded sections (`ComplexAnalytic.BoundedCoherent m`) for `m ≤ n`, every
finite étale cover with separated structure map of the analytification of an affine scheme `X`
of finite type over `ℂ` with `dim Γ(X, 𝒪_X) ≤ n` is the analytification of a finite étale cover
of `X` (`ComplexAnalytic.separatedCoversAlgebraic_of_ringKrullDim_le`).

## Proof

If `Γ(X, 𝒪_X)` is a finite product of normal domains, the smooth locus `U` of `X` has complement
of codimension at least two (`ComplexAnalytic.hasCodimTwoComplement_smoothLocus`), so it suffices
to show that the restriction of the cover to `U^an` is algebraic
(`ComplexAnalytic.mem_essImage_of_restrict'`). This is Zariski-local on `U`, which is covered by
affine integral opens locally étale over affine spaces
(`ComplexAnalytic.exists_isAffineOpen_le_smoothLocus`), where it is
`ComplexAnalytic.mem_essImage_of_isLocallyEtaleOverAffineSpace`.

The general case follows by induction on `n`: pass to the reduced quotient and then, through the
Milnor square of the normalisation, to a finite product of normal domains of dimension `≤ n` and
to the conductor, of dimension `< n`.

## Main results

- `ComplexAnalytic.SeparatedCoversAlgebraic.of_isFiniteProductOfNormalDomains`: the normal case.
- `ComplexAnalytic.SeparatedCoversAlgebraic.of_ringKrullDim_le_of_normal`: the induction step.
- `ComplexAnalytic.separatedCoversAlgebraic_of_ringKrullDim_le`: affine schemes of dimension
  `≤ n`.
-/

open CategoryTheory AlgebraicGeometry

universe u

namespace ComplexAnalytic

open AnalyticSpace

noncomputable section

/-- An open `V ≤ U` of `X`, seen as an open subscheme of `U`, is isomorphic to `V` over `ℂ`. -/
def SchemeLFTℂ.restrictRestrictHom (X : SchemeLFTℂ.{u}) {U V : X.obj.left.Opens} (h : V ≤ U) :
    X.restrict V ⟶ (X.restrict U).restrict (U.ι ⁻¹ᵁ V) :=
  ObjectProperty.homMk (Over.homMk (Scheme.Opens.isoOfLE h).inv (by
    change (Scheme.Opens.isoOfLE h).inv ≫ (U.ι ⁻¹ᵁ V).ι ≫ U.ι ≫ X.obj.hom = V.ι ≫ X.obj.hom
    rw [← Scheme.Opens.isoOfLE_hom_ι_assoc h, Iso.inv_hom_id_assoc]))

instance (X : SchemeLFTℂ.{u}) {U V : X.obj.left.Opens} (h : V ≤ U) :
    IsIso (X.restrictRestrictHom h).hom.left :=
  inferInstanceAs (IsIso (Scheme.Opens.isoOfLE h).inv)

/-- `SeparatedCoversAlgebraic` passes from an affine open `V ≤ U` of `X` to `V` seen as an open
subscheme of `U`. -/
theorem SeparatedCoversAlgebraic.restrict_restrict (X : SchemeLFTℂ.{u}) {U V : X.obj.left.Opens}
    (h : V ≤ U) [IsAffine (X.restrict V).obj.left] (hV : SeparatedCoversAlgebraic (X.restrict V)) :
    SeparatedCoversAlgebraic ((X.restrict U).restrict (U.ι ⁻¹ᵁ V)) := by
  haveI : IsAffine (V : Scheme.{u}) := ‹IsAffine (X.restrict V).obj.left›
  haveI : IsAffine ((X.restrict U).restrict (U.ι ⁻¹ᵁ V)).obj.left :=
    IsAffine.of_isIso (Scheme.Opens.isoOfLE h).hom
  exact SeparatedCoversAlgebraic.of_isClosedImmersion (X.restrictRestrictHom h)
    (ConcreteCategory.bijective_of_isIso (X.restrictRestrictHom h).hom.left.base).2 hV

variable {n : ℕ} (hB : ∀ m ≤ n, BoundedCoherent.{u} m)

include hB in
/-- **The smooth locus of a normal affine scheme**: if `Γ(X, 𝒪_X)` is a finite product of normal
domains of dimension `≤ n` and bounded sections are coherent in dimensions `≤ n`, then
`SeparatedCoversAlgebraic` holds for the smooth locus of `X`. -/
theorem SeparatedCoversAlgebraic.restrict_smoothLocus (X : SchemeLFTℂ.{u}) [IsAffine X.obj.left]
    (hX : IsFiniteProductOfNormalDomains Γ(X.obj.left, ⊤))
    (hdim : ringKrullDim Γ(X.obj.left, ⊤) ≤ n) :
    SeparatedCoversAlgebraic (X.restrict X.smoothLocus) := by
  let U := X.smoothLocus
  choose V hxV hVU hV _ _ _ hloc m hm hmle using
    fun y : (U : Scheme.{u}) ↦ exists_isAffineOpen_le_smoothLocus X hX y.2
  refine SeparatedCoversAlgebraic.of_cover (X := X.restrict U) (fun y ↦ U.ι ⁻¹ᵁ V y)
    (eq_top_iff.2 fun y _ ↦ TopologicalSpace.Opens.mem_iSup.2 ⟨y, hxV y⟩) fun y ↦ ?_
  haveI : IsAffine (X.restrict (V y)).obj.left := hV y
  refine SeparatedCoversAlgebraic.restrict_restrict X (hVU y) fun W hW ↦ ?_
  haveI := t2Space_analytification_of_isAffine (X.restrict (V y))
  haveI := FiniteEtaleOver.t2Space_left_of_isSeparatedMap W hW
  exact mem_essImage_of_isLocallyEtaleOverAffineSpace
    (hB (m y) (by exact_mod_cast (hmle y).trans hdim)) _ (hm y) (hloc y) W

include hB in
/-- **Normal affine schemes**: if `Γ(X, 𝒪_X)` is a finite product of normal domains of dimension
`≤ n` and bounded sections are coherent in dimensions `≤ n`, then every finite étale cover of
`X^an` with separated structure map is the analytification of a finite étale cover of `X`. -/
theorem SeparatedCoversAlgebraic.of_isFiniteProductOfNormalDomains (X : SchemeLFTℂ.{u})
    [IsAffine X.obj.left] (hX : IsFiniteProductOfNormalDomains Γ(X.obj.left, ⊤))
    (hdim : ringKrullDim Γ(X.obj.left, ⊤) ≤ n) : SeparatedCoversAlgebraic X := fun W hW ↦ by
  haveI := t2Space_analytification_of_isAffine X
  haveI := FiniteEtaleOver.t2Space_left_of_isSeparatedMap W hW
  exact mem_essImage_of_restrict' X hX _ (hasCodimTwoComplement_smoothLocus X hX) W
    (SeparatedCoversAlgebraic.restrict_smoothLocus hB X hX hdim _
      (isSeparatedMap_restrictFiniteEtaleOver W hW _))

omit hB

section Step

variable (n)
  (hnorm : ∀ (Y : SchemeLFTℂ.{u}) [IsAffine Y.obj.left],
    IsFiniteProductOfNormalDomains Γ(Y.obj.left, ⊤) → ringKrullDim Γ(Y.obj.left, ⊤) ≤ n →
      SeparatedCoversAlgebraic Y)
  (hlow : ∀ (Y : SchemeLFTℂ.{u}) [IsAffine Y.obj.left], ringKrullDim Γ(Y.obj.left, ⊤) < n →
    SeparatedCoversAlgebraic Y)

include hnorm hlow in
/-- **The reduced case of the induction step, from normal schemes.** If `SeparatedCoversAlgebraic`
holds for all affine schemes of dimension `≤ n` whose ring of functions is a finite product of
normal domains and for all affine schemes of dimension `< n`, then it holds for every reduced
affine scheme of dimension `≤ n`. -/
theorem SeparatedCoversAlgebraic.of_isReduced_of_ringKrullDim_le_of_normal (X : SchemeLFTℂ.{u})
    [IsAffine X.obj.left] [IsReduced Γ(X.obj.left, ⊤)] (hX : ringKrullDim Γ(X.obj.left, ⊤) ≤ n) :
    SeparatedCoversAlgebraic X := by
  obtain ⟨_, _⟩ := X.exists_algebra_finiteType
  obtain ⟨S, _, _, _, hinj, hS, hdimS, I, hI, hdimI⟩ := exists_normalization Γ(X.obj.left, ⊤) ℂ
  exact SeparatedCoversAlgebraic.of_milnorSquare X S hinj I hI
    (hnorm _ (hS.of_ringEquiv (SchemeLFTℂ.specAlgebraΓEquiv X S))
      ((ringKrullDim_eq_of_ringEquiv (SchemeLFTℂ.specAlgebraΓEquiv X S)).trans_le
        (hdimS.trans hX)))
    (hlow _ ((ringKrullDim_eq_of_ringEquiv (SchemeLFTℂ.specAlgebraΓEquiv X _)).trans_lt
      (lt_natCast_of_add_one_le (hdimI.trans hX))))

include hnorm hlow in
/-- **The induction step, from normal schemes.** Under the hypotheses of
`ComplexAnalytic.SeparatedCoversAlgebraic.of_isReduced_of_ringKrullDim_le_of_normal`,
`SeparatedCoversAlgebraic` holds for every affine scheme of finite type over `ℂ` of dimension
`≤ n`. -/
theorem SeparatedCoversAlgebraic.of_ringKrullDim_le_of_normal (X : SchemeLFTℂ.{u})
    [IsAffine X.obj.left] (hX : ringKrullDim Γ(X.obj.left, ⊤) ≤ n) :
    SeparatedCoversAlgebraic X := by
  let R := Γ(X.obj.left, ⊤) ⧸ nilradical Γ(X.obj.left, ⊤)
  haveI : IsReduced R := (Ideal.isRadical_iff_quotient_reduced _).1 (Ideal.radical_isRadical _)
  haveI : IsReduced Γ((SchemeLFTℂ.specAlgebra X R).obj.left, ⊤) :=
    isReduced_of_injective (SchemeLFTℂ.specAlgebraΓEquiv X R).toRingHom
      (SchemeLFTℂ.specAlgebraΓEquiv X R).injective
  exact SeparatedCoversAlgebraic.of_quotient_nilradical X
    (SeparatedCoversAlgebraic.of_isReduced_of_ringKrullDim_le_of_normal n hnorm hlow _
      ((ringKrullDim_eq_of_ringEquiv (SchemeLFTℂ.specAlgebraΓEquiv X R)).trans_le
        ((ringKrullDim_le_of_surjective _ Ideal.Quotient.mk_surjective).trans hX)))

end Step

include hB in
/-- **Riemann existence for affine schemes of dimension `≤ n`, given coherence of bounded
sections.** If bounded sections are coherent in all dimensions `≤ n`, every finite étale cover
with separated structure map of the analytification of an affine scheme `X` of finite type over
`ℂ` with `dim Γ(X, 𝒪_X) ≤ n` is the analytification of a finite étale cover of `X`. -/
theorem separatedCoversAlgebraic_of_ringKrullDim_le (X : SchemeLFTℂ.{u}) [IsAffine X.obj.left]
    (hX : ringKrullDim Γ(X.obj.left, ⊤) ≤ n) : SeparatedCoversAlgebraic X := by
  induction n generalizing X with
  | zero =>
    exact SeparatedCoversAlgebraic.of_ringKrullDim_le_of_normal 0
      (fun Y _ hY hdim ↦ SeparatedCoversAlgebraic.of_isFiniteProductOfNormalDomains hB Y hY hdim)
      (fun Y _ hY ↦ separatedCoversAlgebraic_of_ringKrullDim_lt_zero Y (by exact_mod_cast hY))
      X hX
  | succ k ih =>
    exact SeparatedCoversAlgebraic.of_ringKrullDim_le_of_normal (k + 1)
      (fun Y _ hY hdim ↦ SeparatedCoversAlgebraic.of_isFiniteProductOfNormalDomains hB Y hY hdim)
      (fun Y _ hY ↦ ih (fun m hm ↦ hB m (hm.trans k.le_succ)) Y
        (ENat.WithBot.lt_add_one_iff.1 (by exact_mod_cast hY)))
      X hX

end

end ComplexAnalytic
