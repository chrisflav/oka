/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.AlgebraicGeometry.SmoothLocus
import Oka.Analytification.RET.ES.NormalHartogs
import Oka.Analytification.RET.ES.Smooth

/-!
# The smooth locus of a normal affine scheme

For `X` a scheme locally of finite type over `ℂ`, `ComplexAnalytic.SchemeLFTℂ.smoothLocus X` is
the open of points at which `X` is smooth over `ℂ`.

## Main results

- `ComplexAnalytic.SchemeLFTℂ.isLocallyEtaleOverAffineSpace_of_smooth`: a scheme smooth over `ℂ`
  is locally étale over affine spaces; in particular so is the smooth locus
  (`ComplexAnalytic.SchemeLFTℂ.isLocallyEtaleOverAffineSpace_restrict_smoothLocus`).
- `ComplexAnalytic.hasCodimTwoComplement_smoothLocus`: if `X` is affine with ring of functions a
  finite product of integrally closed domains, the complement of the smooth locus has codimension
  at least two. The points of codimension at most one are smooth by
  `AlgebraicGeometry.Scheme.Hom.mem_smoothLocus_of_ringKrullDim_le_one`.
- `ComplexAnalytic.exists_isAffineOpen_le_smoothLocus`: for such `X`, the smooth locus is covered
  by affine opens whose ring of functions is an integrally closed domain of finite dimension at
  most that of `X`, to which `ComplexAnalytic.mem_essImage_of_isLocallyEtaleOverAffineSpace`
  applies.
-/

open CategoryTheory AlgebraicGeometry

universe u

namespace ComplexAnalytic

namespace SchemeLFTℂ

/-- The **smooth locus** of a scheme locally of finite type over `ℂ`: the points at which it is
smooth over `ℂ`. -/
noncomputable def smoothLocus (X : SchemeLFTℂ.{u}) : X.obj.left.Opens :=
  haveI : LocallyOfFiniteType X.obj.hom := X.property
  X.obj.hom.smoothLocus

/-- A morphism of an affine scheme to affine space given by an étale ring map is étale. -/
lemma etale_toAffineSpace {Z : SchemeLFTℂ.{u}} [IsAffine Z.obj.left] {N : ℕ}
    (s : MvPolynomial (Fin N) (ULift.{u} ℂ) →+* Γ(Z.obj.left, ⊤))
    (hs : s.comp MvPolynomial.C = Z.constMap) (h : s.Etale) :
    Etale (toAffineSpace s hs).hom.left := by
  haveI : IsAffine (affineSpace.{u} N).obj.left :=
    inferInstanceAs (IsAffine (Spec (.of (MvPolynomial (Fin N) (ULift.{u} ℂ)))))
  rw [HasRingHomProperty.iff_of_isAffine (P := @Etale)]
  refine (RingHom.Etale.respectsIso.cancel_left_isIso
    (Scheme.ΓSpecIso (.of (MvPolynomial (Fin N) (ULift.{u} ℂ)))).inv _).1 ?_
  have e : ((Scheme.ΓSpecIso (.of (MvPolynomial (Fin N) (ULift.{u} ℂ)))).inv ≫
      (toAffineSpace s hs).hom.left.appTop).hom = s :=
    RingHom.ext fun p ↦ toAffineSpace_appTop s hs p
  exact (congrArg RingHom.Etale e).mpr h

/-- **Schemes smooth over `ℂ` are locally étale over affine spaces.** -/
theorem isLocallyEtaleOverAffineSpace_of_smooth (Y : SchemeLFTℂ.{u}) [Smooth Y.obj.hom] :
    Y.IsLocallyEtaleOverAffineSpace := by
  intro y
  obtain ⟨U', hU', V, hV, hyV, e, hst⟩ := Smooth.exists_isStandardSmooth Y.obj.hom y
  obtain rfl : U' = ⊤ := eq_top_iff.mpr fun z _ ↦ by
    rw [show z = Y.obj.hom y from Subsingleton.elim _ _]
    exact e hyV
  haveI : IsAffine (Y.restrict V).obj.left := hV
  let φ : ULift.{u} ℂ →+* Γ(Y.obj.left, V) :=
    ((Scheme.ΓSpecIso (.of (ULift.{u} ℂ))).inv ≫ Y.obj.hom.appLE ⊤ V e).hom
  have hφ : φ.IsStandardSmooth :=
    (RingHom.isStandardSmooth_respectsIso.cancel_left_isIso
      (Scheme.ΓSpecIso (.of (ULift.{u} ℂ))).inv _).2 hst
  letI := φ.toAlgebra
  haveI : Algebra.IsStandardSmooth (ULift.{u} ℂ) Γ(Y.obj.left, V) := hφ
  obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := this.out
  haveI := P.isStandardSmoothOfRelativeDimension rfl
  obtain ⟨g, hg⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial
    (n := P.dimension) (ULift.{u} ℂ) Γ(Y.obj.left, V)
  let s : MvPolynomial (Fin P.dimension) (ULift.{u} ℂ) →+* Γ((Y.restrict V).obj.left, ⊤) :=
    V.topIso.inv.hom.comp g.toRingHom
  have key : Y.obj.hom.appLE ⊤ V e ≫ V.topIso.inv = (V.ι ≫ Y.obj.hom).appTop := by
    rw [Scheme.Hom.comp_appTop, Scheme.Opens.ι_appTop, Scheme.Hom.appLE, Scheme.Opens.topIso,
      Category.assoc, Functor.mapIso_inv]
    erw [← Functor.map_comp]
    rfl
  have hs : s.comp MvPolynomial.C = (Y.restrict V).constMap := by
    refine RingHom.ext fun r ↦ ?_
    have h1 : g (MvPolynomial.C r) = φ r := g.commutes r
    change V.topIso.inv.hom (g (MvPolynomial.C r)) =
      ((Scheme.ΓSpecIso (.of (ULift.{u} ℂ))).inv ≫ (V.ι ≫ Y.obj.hom).appTop).hom r
    rw [h1, ← key]
    rfl
  refine ⟨V, hyV, P.dimension, toAffineSpace s hs, etale_toAffineSpace s hs ?_⟩
  exact RingHom.Etale.respectsIso.1 g.toRingHom V.topIso.symm.commRingCatIsoToRingEquiv hg

/-- An open inside the smooth locus is smooth over `ℂ`. -/
lemma smooth_restrict_of_le_smoothLocus (X : SchemeLFTℂ.{u}) {U : X.obj.left.Opens}
    (hU : U ≤ X.smoothLocus) : Smooth (X.restrict U).obj.hom := by
  haveI : LocallyOfFiniteType X.obj.hom := X.property
  change Smooth (U.ι ≫ X.obj.hom)
  rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq]
  exact eq_top_iff.mpr fun y _ ↦ hU y.2

/-- The smooth locus is smooth over `ℂ`. -/
instance smooth_restrict_smoothLocus (X : SchemeLFTℂ.{u}) :
    Smooth (X.restrict X.smoothLocus).obj.hom :=
  smooth_restrict_of_le_smoothLocus X le_rfl

/-- **The smooth locus is locally étale over affine spaces.** -/
theorem isLocallyEtaleOverAffineSpace_restrict_smoothLocus (X : SchemeLFTℂ.{u}) :
    (X.restrict X.smoothLocus).IsLocallyEtaleOverAffineSpace :=
  isLocallyEtaleOverAffineSpace_of_smooth _

end SchemeLFTℂ

/-- **The smooth locus of a normal affine scheme has complement of codimension at least two.** Let
`X` be an affine scheme of finite type over `ℂ` whose ring of functions is a finite product of
integrally closed domains. Then every point outside the smooth locus of `X` has a local ring of
dimension at least two. -/
theorem hasCodimTwoComplement_smoothLocus (X : SchemeLFTℂ.{u}) [IsAffine X.obj.left]
    (hX : IsFiniteProductOfNormalDomains Γ(X.obj.left, ⊤)) :
    HasCodimTwoComplement X.smoothLocus := by
  haveI : LocallyOfFiniteType X.obj.hom := X.property
  intro x hx
  by_contra hlt
  have h1 : ringKrullDim (X.obj.left.presheaf.stalk x) ≤ 1 := by
    rw [not_le, show (2 : WithBot ℕ∞) = 1 + 1 by norm_num] at hlt
    exact ENat.WithBot.lt_add_one_iff.mp hlt
  haveI : CharZero (ULift.{u} ℂ) :=
    charZero_of_injective_ringHom (f := (ULift.ringEquiv (R := ℂ)).symm.toRingHom)
      ULift.ringEquiv.symm.injective
  obtain ⟨f, hxf, hdom, hnorm⟩ := exists_basicOpen_isDomain hX x
  let V := X.obj.left.basicOpen f
  let e : Γ(V, ⊤) ≃+* Γ(X.obj.left, V) := V.topIso.commRingCatIsoToRingEquiv
  haveI : IsDomain Γ(X.obj.left, V) := e.symm.toMulEquiv.isDomain _
  haveI : IsIntegrallyClosed Γ(X.obj.left, V) := IsIntegrallyClosed.of_equiv e
  exact hx (Scheme.Hom.mem_smoothLocus_of_ringKrullDim_le_one X.obj.hom
    ((isAffineOpen_top _).basicOpen f) hxf h1)

/-- The Krull dimension does not increase under localization. -/
lemma ringKrullDim_le_of_isLocalization {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S] : ringKrullDim S ≤ ringKrullDim R :=
  Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R S)) fun _ _ hpq ↦
    (IsLocalization.orderEmbedding M S).strictMono hpq

/-- The ring of functions of an affine scheme of finite type over `ℂ` has finite dimension. -/
lemma exists_ringKrullDim_le_natCast (X : SchemeLFTℂ.{u}) [IsAffine X.obj.left] :
    ∃ k : ℕ, ringKrullDim Γ(X.obj.left, ⊤) ≤ k := by
  obtain ⟨_, _⟩ := X.exists_algebra_finiteType
  obtain ⟨k, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType ℂ Γ(X.obj.left, ⊤))
  refine ⟨k, (ringKrullDim_le_of_surjective f.toRingHom hf).trans_eq ?_⟩
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add,
    Nat.card_eq_fintype_card, Fintype.card_fin]

/-- A nontrivial ring of dimension at most a natural number has dimension a natural number. -/
lemma exists_ringKrullDim_eq_natCast {R : Type*} [CommRing R] [Nontrivial R] {k : ℕ}
    (h : ringKrullDim R ≤ k) : ∃ n : ℕ, ringKrullDim R = n := by
  have h0 : ringKrullDim R ≠ ⊥ :=
    ne_bot_of_le_ne_bot WithBot.zero_ne_bot ringKrullDim_nonneg_of_nontrivial
  obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.mp h0
  rw [← hd] at h ⊢
  have hdk : d ≤ k := by exact_mod_cast h
  obtain ⟨n, rfl⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_le_ne_top (ENat.coe_ne_top k) hdk)
  exact ⟨n, rfl⟩

/-- **An affine cover of the smooth locus by integral pieces.** Let `X` be an affine scheme of
finite type over `ℂ` whose ring of functions is a finite product of integrally closed domains.
Every point of the smooth locus of `X` has an affine open neighbourhood `V` inside the smooth locus
whose ring of functions is an integrally closed domain of dimension a natural number `n` at most
the dimension of `X`; in particular `V` is integral and locally étale over affine spaces. -/
theorem exists_isAffineOpen_le_smoothLocus (X : SchemeLFTℂ.{u}) [IsAffine X.obj.left]
    (hX : IsFiniteProductOfNormalDomains Γ(X.obj.left, ⊤)) {x : X.obj.left}
    (hx : x ∈ X.smoothLocus) :
    ∃ V : X.obj.left.Opens, x ∈ V ∧ V ≤ X.smoothLocus ∧ IsAffineOpen V ∧
      IsDomain Γ(X.obj.left, V) ∧ IsIntegrallyClosed Γ(X.obj.left, V) ∧
      IsIntegral (X.restrict V).obj.left ∧ (X.restrict V).IsLocallyEtaleOverAffineSpace ∧
      ∃ n : ℕ, ringKrullDim Γ((X.restrict V).obj.left, ⊤) = n ∧
        (n : WithBot ℕ∞) ≤ ringKrullDim Γ(X.obj.left, ⊤) := by
  haveI : LocallyOfFiniteType X.obj.hom := X.property
  obtain ⟨e, hxe, hdom, hnorm⟩ := exists_basicOpen_isDomain hX x
  let W := X.obj.left.basicOpen e
  have hW : IsAffineOpen W := (isAffineOpen_top _).basicOpen e
  let eW : Γ(W, ⊤) ≃+* Γ(X.obj.left, W) := W.topIso.commRingCatIsoToRingEquiv
  haveI : IsDomain Γ(X.obj.left, W) := eW.symm.toMulEquiv.isDomain _
  haveI : IsIntegrallyClosed Γ(X.obj.left, W) := IsIntegrallyClosed.of_equiv eW
  obtain ⟨f, hfle, hxf⟩ := hW.exists_basicOpen_le (V := X.smoothLocus) ⟨x, hx⟩ hxe
  let V := X.obj.left.basicOpen f
  have hV : IsAffineOpen V := hW.basicOpen f
  have hf0 : f ≠ 0 := by
    rintro rfl
    simp at hxf
  have hM := powers_le_nonZeroDivisors_of_noZeroDivisors hf0
  haveI := hW.isLocalization_basicOpen f
  haveI : IsDomain Γ(X.obj.left, V) := IsLocalization.isDomain_of_le_nonZeroDivisors _ hM
  haveI : IsIntegrallyClosed Γ(X.obj.left, V) :=
    isIntegrallyClosed_of_isLocalization _ (Submonoid.powers f) hM
  let eV : Γ(V, ⊤) ≃+* Γ(X.obj.left, V) := V.topIso.commRingCatIsoToRingEquiv
  haveI : IsAffine (X.restrict V).obj.left := hV
  haveI : IsDomain Γ((X.restrict V).obj.left, ⊤) := eV.toMulEquiv.isDomain _
  haveI : Nonempty (X.restrict V).obj.left := ⟨⟨x, hxf⟩⟩
  haveI := SchemeLFTℂ.smooth_restrict_of_le_smoothLocus X hfle
  have hdimV : ringKrullDim Γ((X.restrict V).obj.left, ⊤) ≤ ringKrullDim Γ(X.obj.left, ⊤) := by
    haveI := (isAffineOpen_top X.obj.left).isLocalization_basicOpen e
    exact (ringKrullDim_eq_of_ringEquiv eV).trans_le
      ((ringKrullDim_le_of_isLocalization (Submonoid.powers f)).trans
        (ringKrullDim_le_of_isLocalization (Submonoid.powers e)))
  obtain ⟨k, hk⟩ := exists_ringKrullDim_le_natCast X
  obtain ⟨n, hn⟩ := exists_ringKrullDim_eq_natCast (hdimV.trans hk)
  exact ⟨V, hxf, hfle, hV, inferInstance, inferInstance, isIntegral_of_isAffine_of_isDomain _,
    SchemeLFTℂ.isLocallyEtaleOverAffineSpace_of_smooth _, n, hn, hn ▸ hdimV⟩

/-- **A big open locally étale over affine spaces.** An affine scheme of finite type over `ℂ` whose
ring of functions is a finite product of integrally closed domains has an open with complement of
codimension at least two which is locally étale over affine spaces, namely its smooth locus. -/
theorem exists_hasCodimTwoComplement_isLocallyEtaleOverAffineSpace (X : SchemeLFTℂ.{u})
    [IsAffine X.obj.left] (hX : IsFiniteProductOfNormalDomains Γ(X.obj.left, ⊤)) :
    ∃ U : X.obj.left.Opens, HasCodimTwoComplement U ∧
      (X.restrict U).IsLocallyEtaleOverAffineSpace :=
  ⟨X.smoothLocus, hasCodimTwoComplement_smoothLocus X hX,
    SchemeLFTℂ.isLocallyEtaleOverAffineSpace_restrict_smoothLocus X⟩

end ComplexAnalytic
