/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Analytification.DistinguishedOpen
import Oka.Analytification.Functor

/-!
# The projection of a distinguished open is the analytification of the localisation map

`Oka/Analytification/DistinguishedOpen.lean` builds `ComplexAnalytic.localisationProj`, the
morphism `(A_f)^an ⟶ X^an`, out of the universal property: it is `liftHom` applied to the first
`n` coordinates. That says nothing about where the morphism *comes from*, and the construction
that consumes it — gluing an analytic space out of an affine cover — needs it to be the value of
the **functor** on the localisation map, because the transition isomorphisms of a glue data are
produced from isomorphisms of `ℂ`-algebras and nothing else.

This file supplies that link: `ComplexAnalytic.analytificationMap_localisationPresHom` says
`localisationProj` is `ComplexAnalytic.analytificationMap` of the structure map `A ⟶ A_f`.

It is a separate file rather than a section of `Oka/Analytification/DistinguishedOpen.lean`
because **neither `ComplexAnalytic.analytificationFunctor` nor
`ComplexAnalytic.analytificationMap` is in that file's import closure**: the first is declared in
`Oka/Analytification/Functor.lean` and the second in `Oka/Analytification/ChangeOfVariables.lean`,
and `Oka/Analytification/DistinguishedOpen.lean` reaches neither. This file is where the two sides
first meet, its two imports being that file and `Oka/Analytification/Functor.lean`; the theorem
below is the only thing in `Oka/Analytification/DistinguishedOpen.lean` that needs them.

**That sentence read *"because that file imports only `Oka/AnalyticSpace/Nonvanishing.lean` and
`Oka/Analytification/UniversalProperty.lean`, and the functor lives two files further on"* until
2026-09-07, and both halves of it were wrong.** `Oka/Analytification/DistinguishedOpen.lean` has a
**third** import, `Oka/RingTheory/MvPolynomial/Localization.lean`, so the enumeration was short by
one; and *further on* asserts an order that does not hold — `Oka/Analytification/Functor.lean` and
`Oka/Analytification/ChangeOfVariables.lean` are **incomparable** with
`Oka/Analytification/DistinguishedOpen.lean`, neither being in the other's import closure, so the
functor is not downstream of that file at any distance. What the argument needed all along is the
weaker and checkable statement now written above, and the two false halves were both reached by
reading the import block rather than the graph. Measured at `5a525bc` with
`scripts/import_cost.py`'s `IMPORT` pattern over its nesting-aware `strip_comments`.

## Which way the arrows go

`ComplexAnalytic.PresHom g g'` carries a ring map `PresentedAlgebra g' →+* PresentedAlgebra g`
and induces `analytification g ⟶ analytification g'`, so a morphism *of presentations* out of the
localisation is an algebra map **into** it. That is why
`ComplexAnalytic.localisationPresHom` has type `PresHom (localisationPresentation g f) g` and its
ring map is `A ⟶ A_f`: the two directions are the same statement read in opposite categories.

## Nothing here is about localisation

The ring map is induced by `MvPolynomial.rename (localisationIncl n)`, so it is an instance of
`ComplexAnalytic.PresHom.ofRename`, and the only thing to check is the hypothesis that construction
asks for: that the old equations, renamed, lie in the new ideal. They *are* new equations, by
`ComplexAnalytic.localisationPresentation_castSucc`. **That `PresentedAlgebra
(localisationPresentation g f)` is a localisation of `PresentedAlgebra g` is
`ComplexAnalytic.localisationPresentedAlgebraEquiv`, in the
`Oka/Analytification/DistinguishedOpen.lean` this file imports — and nothing below uses it**: a
structure map is all a `PresHom` wants, so every statement and every proof here is about
`ComplexAnalytic.localisationPresentation` as a tuple of polynomials. See
`Oka/Analytification/DistinguishedOpen.lean` on the naming, and its `## What is not here` on why
the equivalence was proved for a consumer elsewhere.

## Main definitions

- `ComplexAnalytic.localisationPresHom`: the `ℂ`-algebra map `A ⟶ A_f`, as a morphism of
  presentations.
- `ComplexAnalytic.localisationRingHom`: the same, as a bare ring map of presented algebras.

## Main results

- `ComplexAnalytic.analytificationMap_localisationPresHom` and
  `ComplexAnalytic.analytificationFunctor_map_localisationPresHom`: **the projection of a
  distinguished open is the analytification of the structure map**, as a bare morphism and as the
  functor's value.
- `ComplexAnalytic.localisationIso_inv_analytificationMap`: the inclusion of the open subspace,
  read through the functor — the form a glue data consumes.
- `ComplexAnalytic.isOpenImmersion_analytificationMap_localisationPresHom`: **the functor's value
  on the structure map is an open immersion**, which is
  `ComplexAnalytic.isOpenImmersion_localisationProj` at this spelling and is the one a glue data
  built out of `ComplexAnalytic.analytificationFunctor` will hold.
-/

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace ComplexAnalytic

noncomputable section

variable {n k : ℕ} (g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ)
  (f : MvPolynomial (ULift.{u} (Fin n)) ℂ)

/-- **The old equations, renamed into the bigger polynomial ring, lie in the new ideal** — they
*are* new equations, by `ComplexAnalytic.localisationPresentation_castSucc`. This is the whole
obligation of the two definitions below. -/
theorem rename_localisationIncl_mem (j : Fin k) :
    MvPolynomial.rename (localisationIncl.{u} n) (g j) ∈
      presentationIdeal.{u} (localisationPresentation.{u} g f) :=
  Ideal.subset_span ⟨j.castSucc, localisationPresentation_castSucc.{u} g f j⟩

/-- **The structure map as a morphism of presentations**, which by the direction convention of
`ComplexAnalytic.PresHom` points from the localisation to `A`.

It is `ComplexAnalytic.PresHom.ofRename` at `ComplexAnalytic.localisationIncl`: adjoining a
variable is a renaming of the variables, and the commutation with the structure maps that a
`PresHom` demands is `MvPolynomial.rename_C`, discharged there once and for all. -/
def localisationPresHom : PresHom.{u} (localisationPresentation.{u} g f) g :=
  PresHom.ofRename.{u} (localisationIncl.{u} n) (rename_localisationIncl_mem.{u} g f)

/-- **The structure map as a morphism of the two objects of `ComplexAnalytic.Presentation`**: the
same term as `ComplexAnalytic.localisationPresHom`, with its source and target read as objects of
the category.

Stated because the bare `ComplexAnalytic.PresHom` does not elaborate against `≫`, `Iso` or `IsIso`:
`Category Presentation` has `Hom P Q := PresHom P.g Q.g`, and the two objects are not recovered
from the term. -/
abbrev localisationHom :
    (⟨n + 1, k + 1, localisationPresentation.{u} g f⟩ : Presentation.{u}) ⟶ ⟨n, k, g⟩ :=
  localisationPresHom.{u} g f

/-- **The structure map `A ⟶ A_f`**, as a ring map of presented algebras: the underlying ring map
of `ComplexAnalytic.localisationPresHom`, and the spelling every consumer that does not need the
commutation uses. -/
def localisationRingHom :
    PresentedAlgebra.{u} n k g →+*
      PresentedAlgebra.{u} (n + 1) (k + 1) (localisationPresentation.{u} g f) :=
  (localisationPresHom.{u} g f).toRingHom

/-- **The tuple the morphism of presentations transports** is the tuple of old coordinates of
`(A_f)^an`, which is exactly the tuple `ComplexAnalytic.localisationProj` was built from. This is
the whole content of the identification below. -/
theorem transported_localisationPresHom (i : ULift.{u} (Fin n)) :
    transported.{u} (localisationPresHom.{u} g f) i =
      analytificationCoord.{u} (localisationPresentation.{u} g f) (localisationIncl.{u} n i) := by
  change quotientToGlobal.{u} (localisationPresentation.{u} g f)
    (localisationRingHom.{u} g f
      (Ideal.Quotient.mk (presentationIdeal.{u} g) (MvPolynomial.X i))) = _
  change quotientToGlobal.{u} (localisationPresentation.{u} g f)
    (Ideal.Quotient.mk (presentationIdeal.{u} (localisationPresentation.{u} g f))
      (MvPolynomial.rename (localisationIncl.{u} n) (MvPolynomial.X i))) = _
  rw [MvPolynomial.rename_X]
  exact polyToGlobal_X.{u} (localisationPresentation.{u} g f) (localisationIncl.{u} n i)

/-- **The projection of a distinguished open is the analytification of the structure map.**

Both sides are morphisms into `X^an`, so `ComplexAnalytic.hom_ext_analytification` reduces it to
the coordinates, where one side is `ComplexAnalytic.coordPullback_analytificationMap_comp` and the
other `ComplexAnalytic.coordPullback_localisationProj_comp`, and the two tuples agree by
`ComplexAnalytic.transported_localisationPresHom`. -/
theorem analytificationMap_localisationPresHom :
    analytificationMap.{u} (localisationPresHom.{u} g f) = localisationProj.{u} g f := by
  refine hom_ext_analytification.{u} g _ _ fun i ↦ ?_
  rw [coordPullback_analytificationMap_comp, coordPullback_localisationProj_comp,
    transported_localisationPresHom]

/-- **The same, as the functor's value on a morphism of `ComplexAnalytic.Presentation`.** This is
`ComplexAnalytic.analytificationMap_localisationPresHom`; `ComplexAnalytic.analytificationFunctor`
is `analytificationMap` on morphisms by definition. -/
theorem analytificationFunctor_map_localisationPresHom :
    analytificationFunctor.{u}.map
        (X := ⟨n + 1, k + 1, localisationPresentation.{u} g f⟩) (Y := ⟨n, k, g⟩)
        (localisationPresHom.{u} g f) =
      localisationProj.{u} g f :=
  analytificationMap_localisationPresHom.{u} g f

/-- **The inclusion of `D(f)` into `X^an`, read through the functor.**

`ComplexAnalytic.localisationIso_inv_localisationProj` says the inclusion is the inverse of the
comparison followed by the projection; with the identification above, the projection is the
analytification of an algebra map. So this exhibits `ofRestrict` — the open immersion, which is
not built from any algebra — as a composite of the comparison isomorphism with a morphism
produced by the functor from a `ℂ`-algebra map, and that is the form in which a glue data uses
it. -/
theorem localisationIso_inv_analytificationMap :
    (localisationIso.{u} g f).inv ≫ analytificationMap.{u} (localisationPresHom.{u} g f) =
      (AnalyticSpace.analytification.{u} g).ofRestrict (localisationOpen.{u} g f) :=
  (congrArg (fun m ↦ (localisationIso.{u} g f).inv ≫ m)
      (analytificationMap_localisationPresHom.{u} g f)).trans
    (localisationIso_inv_localisationProj.{u} g f)

/-- **The functor's value on the structure map `A ⟶ A_f` is an open immersion.**

`ComplexAnalytic.isOpenImmersion_localisationProj` at this spelling, by
`ComplexAnalytic.analytificationMap_localisationPresHom`. It is stated separately because a glue
data assembled out of `ComplexAnalytic.analytificationFunctor` holds its morphisms in this form
and not as `ComplexAnalytic.localisationProj`, and
`AlgebraicGeometry.LocallyRingedSpace.GlueData`'s `f_open` field is checked against the morphism
one actually has. -/
theorem isOpenImmersion_analytificationMap_localisationPresHom :
    LocallyRingedSpace.IsOpenImmersion
      (analytificationMap.{u} (localisationPresHom.{u} g f)).toLRSHom := by
  rw [analytificationMap_localisationPresHom]
  exact isOpenImmersion_localisationProj.{u} g f

/-- **The ring map on representatives**: the class of `p` goes to the class of `p` with its
variables renamed. Stated because every consumer of
`ComplexAnalytic.localisationPresHom` that needs to compute with it needs this and nothing
else. -/
theorem localisationRingHom_mk (p : MvPolynomial (ULift.{u} (Fin n)) ℂ) :
    localisationRingHom.{u} g f (Ideal.Quotient.mk (presentationIdeal.{u} g) p) =
      Ideal.Quotient.mk (presentationIdeal.{u} (localisationPresentation.{u} g f))
        (MvPolynomial.rename (localisationIncl.{u} n) p) :=
  rfl

end

end ComplexAnalytic
