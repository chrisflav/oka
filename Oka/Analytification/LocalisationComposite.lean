/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Analytification.LocalisationIndependence

/-!
# Localising a presentation twice is localising it once, at the product

`ComplexAnalytic.localisationPresentation g f` adjoins a variable `t` and the equation `t·f - 1`.
Doing that twice — first at `f`, then at a polynomial `f₁` in the *old* variables, renamed along
`ComplexAnalytic.localisationIncl` — adjoins two variables and two equations. This file says the
result is the single localisation at `f₁ * f`.

* `ComplexAnalytic.localisationPresentedAlgebraEquivMul` — **the two presented algebras are
  isomorphic**, as `ℂ`-algebras.
* `ComplexAnalytic.localisationPresentedAlgebraEquivMul_localisationRingHom` — **and the
  isomorphism is one of `A`-algebras**: it carries the composite of the two structure maps to the
  single structure map `A ⟶ A_{f₁·f}`. This is the half with content; the isomorphism alone would
  leave the composite unrelated to what it is a composite of.
* `ComplexAnalytic.localisationPresentationIsoMul` — the same as an isomorphism of objects of
  `ComplexAnalytic.Presentation`, and hence an isomorphism of analytic spaces through
  `ComplexAnalytic.analytificationFunctor`.
* `ComplexAnalytic.localisationPresentationIsoMul_hom_comp` — **the coherence triangle**: the
  composite of the two structure maps and the single one agree once the two members are identified
  by that isomorphism. This is the `trans_comp` law, at the level of presentations and up to the
  coherence isomorphism, which is the only level it can hold at.

## Where this is needed

Taxis #1006, split from #996. `Mathlib/AlgebraicGeometry/Sites/SmallAffineZariski.lean` indexes
the affine members of a scheme by *"is a distinguished open of"*, and the witness for a composite
arrow `U ≤ V ≤ W` is manufactured by `IsAffineOpen.basicOpen_basicOpen_is_basicOpen` — a third
section, neither of the two it is composed from. A transition morphism per arrow therefore has to
know that localising twice is localising once, and `trans_comp` is exactly that statement. The
polynomial version of that manufactured witness is the product, and this file is it.

Together with `ComplexAnalytic.localisationPresentationIsoOfDvdPow`, which says the presentation
does not depend on which polynomial cuts the open out, that is both halves of what a witness-built
transition needs. Neither is the transition, and neither mentions
`AlgebraicGeometry.Scheme`.

## The statement is `IsLocalization.Away.mul`, and the work is the transport

`IsLocalization.Away.mul` in `Mathlib/RingTheory/Localization/Away/Basic.lean` — with the two
instances beneath it for `Localization.Away` — already says that localising `R` at `x` and then at
the image of `y` is localising `R` at `y * x`. **Nothing about the composite is proved here.** What
is proved is that this development's presented algebras are those localisations, compatibly with
their structure maps.

That transport is not free, because of a deliberate absence recorded in
`Oka/Analytification/DistinguishedOpen.lean`, in the docstring of
`ComplexAnalytic.localisationPresentedAlgebraEquiv`: there is **no**
`Algebra (ComplexAnalytic.PresentedAlgebra n k g)` instance on the localised presented algebra,
and so `IsLocalization.Away.mul` cannot be applied to it. Three shapes were available:

1. add that instance, and apply `IsLocalization.Away.mul` directly;
2. add it as a `local instance`, in this file only;
3. **do the algebra where the instances already exist — on `Localization.Away` — and move the
   conclusion across `ComplexAnalytic.localisationPresentedAlgebraEquiv` by hand.**

**Shape 3, and the reason is not a preference between them.** An `Algebra` instance keyed on
`ComplexAnalytic.PresentedAlgebra` is an instance on the type this development uses everywhere,
so typeclass search would meet it on every unrelated goal; that is the cost the quoted paragraph
declines to pay, and paying it here would falsify that paragraph one file away. Shape 2 answers
the objection but not the arithmetic: `IsLocalization.Away.mul`'s own instance arguments are
resolved by search, so a `local instance` buys nothing that the explicit route below does not, at
the price of a second `Algebra` structure on a type that already has one over `ℂ`. Shape 3 needs
one extra step — `ComplexAnalytic.localisationAwayRingEquiv` — and introduces no instance at all.

The step that makes shape 3 short is
`ComplexAnalytic.localisationPresentedAlgebraEquiv_localisationRingHom`, which says the
identification with `Localization.Away` is over `A`. Without it the two structure maps are
unrelated and the transport has nothing to be compatible with.

## What is not here

**No cover, no transition morphism, and no `trans_comp`.** Taxis #996 keeps those. This file
supplies the algebra a transition would be built from and stops there; nothing below mentions
`AlgebraicGeometry.Scheme` or `ComplexAnalytic.coverGlueData`, and no Mathlib import is added —
`IsLocalization.Away.mul` arrives with `Oka/RingTheory/Localization/Away/Basic.lean`, which this
file's import already carries.

**No second polynomial in the new variable.** `f₁` is renamed along
`ComplexAnalytic.localisationIncl`, so it comes from the old variables. That is not a convenience:
localising at a polynomial that mentions `t` is not a localisation of `A` at all, so the composite
would not be one either and there would be no product to compare it with.
-/

open CategoryTheory MvPolynomial

namespace ComplexAnalytic

universe u

variable {n k : ℕ} (g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ)
  (f f₁ : MvPolynomial (ULift.{u} (Fin n)) ℂ)

/-! ### The localisation of `A_f` at `f₁`, transported to `Localization.Away` -/

/-- **The two ways of localising `A_f` at `f₁` agree**, as rings: on the left `f₁` is read in the
presented algebra `A_f`, as the class of its renaming — which is
`ComplexAnalytic.localisationRingHom` applied to the class of `f₁`, by
`ComplexAnalytic.localisationRingHom_mk` — and on the right in `Localization.Away`, through its
`algebraMap`. The renamed spelling is the one used throughout, because it is what
`ComplexAnalytic.localisationPresentedAlgebraEquiv` produces at the localised presentation.

This is `IsLocalization.ringEquivOfRingEquiv` along
`ComplexAnalytic.localisationPresentedAlgebraEquiv`; the hypothesis it wants — that the
isomorphism carries one powers-submonoid to the other — is
`ComplexAnalytic.localisationPresentedAlgebraEquiv_localisationRingHom` under
`Submonoid.map_powers`, and it is the whole reason that lemma is stated over `A`. -/
noncomputable def localisationAwayRingEquiv :
    Localization.Away (Ideal.Quotient.mk
        (presentationIdeal.{u} (localisationPresentation.{u} g f))
        (MvPolynomial.rename (localisationIncl.{u} n) f₁)) ≃+*
      Localization.Away (algebraMap (PresentedAlgebra.{u} n k g)
        (Localization.Away (Ideal.Quotient.mk (presentationIdeal.{u} g) f))
        (Ideal.Quotient.mk (presentationIdeal.{u} g) f₁)) :=
  IsLocalization.ringEquivOfRingEquiv
    (M := Submonoid.powers (Ideal.Quotient.mk
      (presentationIdeal.{u} (localisationPresentation.{u} g f))
      (MvPolynomial.rename (localisationIncl.{u} n) f₁)))
    (T := Submonoid.powers (algebraMap (PresentedAlgebra.{u} n k g)
      (Localization.Away (Ideal.Quotient.mk (presentationIdeal.{u} g) f))
      (Ideal.Quotient.mk (presentationIdeal.{u} g) f₁)))
    _ _ (localisationPresentedAlgebraEquiv.{u} g f).toRingEquiv
    (by
      rw [Submonoid.map_powers]
      exact congrArg Submonoid.powers (localisationPresentedAlgebraEquiv_localisationRingHom.{u}
        g f (Ideal.Quotient.mk (presentationIdeal.{u} g) f₁)))

/-- **`ComplexAnalytic.localisationAwayRingEquiv` on the image of `A_f`**: it is
`ComplexAnalytic.localisationPresentedAlgebraEquiv` on the element and the structure map on the
outside, which is `IsLocalization.ringEquivOfRingEquiv_eq` unfolded once. -/
theorem localisationAwayRingEquiv_algebraMap
    (y : PresentedAlgebra.{u} (n + 1) (k + 1) (localisationPresentation.{u} g f)) :
    localisationAwayRingEquiv.{u} g f f₁ (algebraMap _ _ y) =
      algebraMap (Localization.Away (Ideal.Quotient.mk (presentationIdeal.{u} g) f)) _
        (localisationPresentedAlgebraEquiv.{u} g f y) :=
  IsLocalization.ringEquivOfRingEquiv_eq _ y

/-- **`ComplexAnalytic.localisationAwayRingEquiv` is an isomorphism of `ℂ`-algebras**, which is
the category `ComplexAnalytic.Presentation` lives in. Both sides are `ℂ`-algebras through the
presented algebra they localise, so this is
`ComplexAnalytic.localisationPresentedAlgebraEquiv.commutes` conjugated by two scalar towers. -/
noncomputable def localisationAwayAlgEquiv :
    Localization.Away (Ideal.Quotient.mk
        (presentationIdeal.{u} (localisationPresentation.{u} g f))
        (MvPolynomial.rename (localisationIncl.{u} n) f₁)) ≃ₐ[ℂ]
      Localization.Away (algebraMap (PresentedAlgebra.{u} n k g)
        (Localization.Away (Ideal.Quotient.mk (presentationIdeal.{u} g) f))
        (Ideal.Quotient.mk (presentationIdeal.{u} g) f₁)) :=
  AlgEquiv.ofRingEquiv (f := localisationAwayRingEquiv.{u} g f f₁) fun c ↦ by
    rw [IsScalarTower.algebraMap_apply ℂ
        (PresentedAlgebra.{u} (n + 1) (k + 1) (localisationPresentation.{u} g f))
        (Localization.Away (Ideal.Quotient.mk
          (presentationIdeal.{u} (localisationPresentation.{u} g f))
          (MvPolynomial.rename (localisationIncl.{u} n) f₁))),
      localisationAwayRingEquiv, IsLocalization.ringEquivOfRingEquiv_eq,
      IsScalarTower.algebraMap_apply ℂ
        (Localization.Away (Ideal.Quotient.mk (presentationIdeal.{u} g) f))
        (Localization.Away (algebraMap (PresentedAlgebra.{u} n k g)
          (Localization.Away (Ideal.Quotient.mk (presentationIdeal.{u} g) f))
          (Ideal.Quotient.mk (presentationIdeal.{u} g) f₁)))]
    exact congrArg _ ((localisationPresentedAlgebraEquiv.{u} g f).commutes c)

/-! ### Localising twice is localising at the product -/

/-- The localisation of `A_f` at the image of `f₁` **is a localisation of `A` at `f₁·f`**.

This is `IsLocalization.Away.mul`, through the instance Mathlib supplies for `Localization.Away`,
with `Ideal.Quotient.mk` distributed over the product. Stated as a lemma rather than left to
`infer_instance` because the rewriting of `f₁ * f` is what makes the instance apply, and every use
below needs it. -/
instance isLocalization_away_mul :
    IsLocalization.Away (Ideal.Quotient.mk (presentationIdeal.{u} g) (f₁ * f))
      (Localization.Away (algebraMap (PresentedAlgebra.{u} n k g)
        (Localization.Away (Ideal.Quotient.mk (presentationIdeal.{u} g) f))
        (Ideal.Quotient.mk (presentationIdeal.{u} g) f₁))) := by
  rw [map_mul]
  infer_instance

/-- **Localising a presentation twice is localising it once, at the product.**

The left-hand side adjoins `t` with `t·f - 1` and then `s` with `s·f₁ - 1`; the right-hand side
adjoins one variable with `t·(f₁·f) - 1`. The four steps are: identify each side with a
`Localization.Away` by `ComplexAnalytic.localisationPresentedAlgebraEquiv`, cross the two readings
of `f₁` by `ComplexAnalytic.localisationAwayAlgEquiv`, and use that a localisation of a
localisation is a localisation at the product — `ComplexAnalytic.isLocalization_away_mul` — so
that `IsLocalization.algEquiv` identifies it with the localisation at `f₁·f`. -/
noncomputable def localisationPresentedAlgebraEquivMul :
    PresentedAlgebra.{u} (n + 1 + 1) (k + 1 + 1)
        (localisationPresentation.{u} (localisationPresentation.{u} g f)
          (MvPolynomial.rename (localisationIncl.{u} n) f₁)) ≃ₐ[ℂ]
      PresentedAlgebra.{u} (n + 1) (k + 1) (localisationPresentation.{u} g (f₁ * f)) :=
  (localisationPresentedAlgebraEquiv.{u} (localisationPresentation.{u} g f)
      (MvPolynomial.rename (localisationIncl.{u} n) f₁)).trans
    ((localisationAwayAlgEquiv.{u} g f f₁).trans
      (((IsLocalization.algEquiv
            (Submonoid.powers (Ideal.Quotient.mk (presentationIdeal.{u} g) (f₁ * f))) _
            _).restrictScalars ℂ).trans
        (localisationPresentedAlgebraEquiv.{u} g (f₁ * f)).symm))

/-- **The isomorphism is one of `A`-algebras**: it carries the composite of the two structure maps
`A ⟶ A_f ⟶ (A_f)_{f₁}` to the single structure map `A ⟶ A_{f₁·f}`.

This is the statement a coherence law consumes, and the isomorphism without it would say only that
two algebras are abstractly isomorphic. Each of the four steps is compatible with the structure
maps for its own reason: the two outer ones by
`ComplexAnalytic.localisationPresentedAlgebraEquiv_localisationRingHom`, the middle two because
`IsLocalization.algEquiv` is an `A`-algebra map and
`ComplexAnalytic.localisationAwayRingEquiv` was built from the same compatibility. -/
theorem localisationPresentedAlgebraEquivMul_localisationRingHom (x : PresentedAlgebra.{u} n k g) :
    localisationPresentedAlgebraEquivMul.{u} g f f₁
        (localisationRingHom.{u} (localisationPresentation.{u} g f)
          (MvPolynomial.rename (localisationIncl.{u} n) f₁) (localisationRingHom.{u} g f x)) =
      localisationRingHom.{u} g (f₁ * f) x := by
  rw [localisationPresentedAlgebraEquivMul, AlgEquiv.trans_apply,
    localisationPresentedAlgebraEquiv_localisationRingHom, AlgEquiv.trans_apply,
    localisationAwayAlgEquiv, AlgEquiv.ofRingEquiv_apply, localisationAwayRingEquiv_algebraMap,
    localisationPresentedAlgebraEquiv_localisationRingHom, AlgEquiv.trans_apply,
    AlgEquiv.restrictScalars_apply, ← IsScalarTower.algebraMap_apply, AlgEquiv.commutes,
    ← localisationPresentedAlgebraEquiv_localisationRingHom, AlgEquiv.symm_apply_apply]

/-- **The two presentations are isomorphic objects of `ComplexAnalytic.Presentation`**, hence have
isomorphic analytifications through `ComplexAnalytic.analytificationFunctor`.

Mind the direction: `ComplexAnalytic.Presentation.isoOfAlgEquiv` takes the algebra isomorphism
backwards, as `ComplexAnalytic.PresHom` does. -/
noncomputable def localisationPresentationIsoMul :
    (⟨n + 1 + 1, k + 1 + 1, localisationPresentation.{u} (localisationPresentation.{u} g f)
        (MvPolynomial.rename (localisationIncl.{u} n) f₁)⟩ : Presentation.{u}) ≅
      ⟨n + 1, k + 1, localisationPresentation.{u} g (f₁ * f)⟩ :=
  Presentation.isoOfAlgEquiv (localisationPresentedAlgebraEquivMul.{u} g f f₁).symm

/-- **The coherence triangle**: the composite of the two structure maps `A_{f₁·f} ⟶ A_f ⟶ A` and
the single structure map agree, once the two members are identified by
`ComplexAnalytic.localisationPresentationIsoMul`.

This is the `trans_comp` law of a locally directed cover, at the level of presentations and up to
the coherence isomorphism — which is where it has to live, since the composite arrow's witness is
`f₁ * f` and the composite morphism's target is the doubly localised presentation, and the two are
not the same object. It is
`ComplexAnalytic.localisationPresentedAlgebraEquivMul_localisationRingHom` read through
`ComplexAnalytic.PresHom.ext`, so nothing is proved here beyond the packaging. -/
theorem localisationPresentationIsoMul_hom_comp :
    (localisationPresentationIsoMul.{u} g f f₁).hom ≫ localisationHom.{u} g (f₁ * f) =
      localisationHom.{u} (localisationPresentation.{u} g f)
          (MvPolynomial.rename (localisationIncl.{u} n) f₁) ≫ localisationHom.{u} g f := by
  refine PresHom.ext (RingHom.ext fun x ↦ ?_)
  change (localisationPresentedAlgebraEquivMul.{u} g f f₁).symm
    (localisationRingHom.{u} g (f₁ * f) x) = _
  rw [AlgEquiv.symm_apply_eq]
  exact (localisationPresentedAlgebraEquivMul_localisationRingHom.{u} g f f₁ x).symm

end ComplexAnalytic
