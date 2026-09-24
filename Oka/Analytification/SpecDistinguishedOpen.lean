/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Analytification.Comparison
import Oka.Analytification.LocalisationIndependence

/-!
# `Spec` of the structure map `A ⟶ A_f` is an open immersion

`Oka/Analytification/LocalisationFunctor.lean` proves the analytic half of this:
`ComplexAnalytic.isOpenImmersion_analytificationMap_localisationPresHom` says the *analytification*
of the structure map is an open immersion, and its docstring says why it is stated in that
spelling — a glue data assembled out of `ComplexAnalytic.analytificationFunctor` holds its
morphisms in that form, and `AlgebraicGeometry.LocallyRingedSpace.GlueData`'s `f_open` field is
checked against the morphism one actually has.

This file is the same statement for `ComplexAnalytic.specFunctor`. It is what a glue data on the
`Spec` side of the same cover will hold, and that glue datum is the *target* of the comparison
morphism `X^an ⟶ X` for a glued scheme: `ComplexAnalytic.comm_coverGlueData` and
`AlgebraicGeometry.LocallyRingedSpace.GlueData.glueMorphisms` already produce a morphism out of
`X^an` into **any** locally ringed space, so what is missing on that line is the space on the
right and not the gluing.

## The proof is a triangle over `A`, and the file exists for its two ends

`ComplexAnalytic.localisationPresentedAlgebraEquiv` identifies `ℂ[x, t] ⧸ (g, t·f - 1)` with
`Localization.Away (mk f)`, and
`ComplexAnalytic.localisationPresentedAlgebraEquiv_localisationRingHom` says that identification
is an isomorphism **over `A`** — the structure map composed with it is
the localisation's own `algebraMap`. Mathlib knows `Spec` of that `algebraMap` is an open
immersion. So the content here is one commuting triangle and one rewrite, and everything else is
where the two halves live: `ComplexAnalytic.specFunctor` is in
`Oka/Analytification/Comparison.lean` and the compatibility is in
`Oka/Analytification/LocalisationIndependence.lean`, and **this file is the only module under
`Oka/` that imports both directly**. Hence a file rather than a section.

**That clause read *"and no file in this repository imports both"* until 2026-09-07**, and what
falsifies it is the import block at the head of this same file: those two lines are the whole of
it, so the sentence had a counterexample two screens above itself at the commit that wrote it.
**The argument it was making survives the repair and only its scope was wrong.** Measured at
`5a525bc` over the repository's own import graph, with `scripts/import_cost.py`'s `IMPORT` pattern
read through its nesting-aware `strip_comments`: **thirteen** modules under `Oka/` have both
`Oka.Analytification.Comparison` and `Oka.Analytification.LocalisationIndependence` in their import
closure — the aggregator `Oka.lean`, which imports every module of the library, is
excluded throughout — and
**twelve of the thirteen reach this file**, at edge distances one to five —
`Oka/Analytification/SpecAffineCover.lean` and `Oka/Analytification/SpecRefinedMember.lean` at
one, `Oka/Analytification/CoverComparison.lean`, `Oka/Analytification/SpecFunctoriality.lean`,
`Oka/Analytification/SpecRefinedMemberSection.lean` and `Oka/Analytification/SpecScheme.lean` at
two, `Oka/Analytification/ComparisonSquare.lean`, `Oka/Analytification/SpecRefinedChoice.lean` and
`Oka/Analytification/SpecTwoData.lean` at three,
`Oka/Analytification/SpecMemberSections.lean` and `Oka/Analytification/SpecRefinedCover.lean` at
four, and `Oka/Analytification/SpecMemberChoice.lean` at five. **So at `5a525bc` every module
with both in closure is this file or one of its own descendants**, and no module that could have
hosted the section had both, which is what the clause meant.

## Mathlib's scheme-level open immersions are available to this repository's glue data, and that
is worth more than the lemma

`AlgebraicGeometry.Spec.locallyRingedSpaceMap` — the spelling `ComplexAnalytic.specFunctor` is
built from, because a `GlueData` here is a locally-ringed-space object — is the same term as
`AlgebraicGeometry.Spec.map`'s underlying morphism: `(Spec.map φ).toLRSHom =
Spec.locallyRingedSpaceMap φ` is `rfl`, and `AlgebraicGeometry.IsOpenImmersion` is
`AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion` of that. So every open immersion Mathlib
proves about `Spec.map` is one about the morphisms this repository glues with.

**Instance search does not cross that identity**, which is why it has to be written down:
`inferInstance` at
`LocallyRingedSpace.IsOpenImmersion (Spec.locallyRingedSpaceMap (CommRingCat.ofHom (algebraMap R
(Localization.Away f))))` fails, while `inferInstanceAs` at the scheme-level spelling succeeds.
Measured 2026-08-30. `ComplexAnalytic.isOpenImmersion_specFunctor_map_localisationHom` below is
that crossing at the one place this development needs it, and its proof term is the scheme-level
theorem with no transport at all.

## Why not `AlgebraicGeometry.IsOpenImmersion.of_isLocalization`

Mathlib has exactly this statement for any `[IsLocalization.Away f S]`, which would make the proof
one line. It is not used, and the reason is a decision `Oka/Analytification/DistinguishedOpen.lean`
argues for in its own docstring: there is deliberately **no** `IsLocalization.Away` instance, and
no `Algebra (ComplexAnalytic.PresentedAlgebra n k g)` instance, on the localised presented algebra
— the identification is an isomorphism a consumer applies, not an instance keyed on a type this
development uses everywhere. Going through `ComplexAnalytic.specLocalisationRingIso` respects that
and costs three lines.

## Main definitions

- `ComplexAnalytic.specLocalisationRingIso`: `ComplexAnalytic.localisationPresentedAlgebraEquiv`,
  as an isomorphism in `CommRingCat` — the form `AlgebraicGeometry.Spec.map` consumes.
- `ComplexAnalytic.specLocalisationOpen`: `D(f) ⊆ Spec A`, as an open subset.
- `ComplexAnalytic.specLocalisationIso`: **the isomorphism `Spec (A_f) ≅ Spec A|D(f)`.**

## Main results

- `ComplexAnalytic.localisationRingHom_comp_eq`: **the triangle over `A`**, in `CommRingCat`:
  the structure map followed by the identification is the localisation's own structure map into
  `Localization.Away`.
- `ComplexAnalytic.isOpenImmersion_Spec_map_localisationRingHom`: **`Spec` of the structure map
  `A ⟶ A_f` is an open immersion**, at the scheme-level spelling, which is where Mathlib's API is.
- `ComplexAnalytic.isOpenImmersion_specFunctor_map_localisationHom`: the same for
  `ComplexAnalytic.specFunctor`'s value on the structure map — the spelling a glue data on the
  `Spec` side will hold, and the mirror of
  `ComplexAnalytic.isOpenImmersion_analytificationMap_localisationPresHom`. **This one is an
  `instance`** and the one above is not, because this is the spelling a glue datum presents to
  instance search; its docstring says so. The morphism of presentations it is taken at is named
  there rather than here: it is a definition, and `## Main results` is a list of results.
- `ComplexAnalytic.range_base_specFunctor_map_localisationHom`: **its image is exactly `D(f)`** —
  the equality, since the side condition of an open-immersion lift is a containment *in* a range,
  and what a `Spec`-side glue data's `hrange` obligation will be checked against.
- `ComplexAnalytic.specLocalisationIso_hom_ofRestrict` and
  `ComplexAnalytic.specLocalisationIso_inv_specFunctor_map`: **the isomorphism is one over
  `Spec A`.**
- `ComplexAnalytic.opensRange_Spec_map_localisationRingHom`: **the same image statement at
  `AlgebraicGeometry.Scheme.Hom.opensRange`**, which is the spelling a consumer that *composes*
  this open immersion with another needs, since
  `AlgebraicGeometry.Scheme.Hom.opensRange_comp` has no `Set.range` form. What it costs is
  recorded in its own docstring and in the first bullet below.
- `ComplexAnalytic.image_basicOpen_rename_Spec_map_localisationRingHom`: **and the image of the
  basic open a *renamed* polynomial cuts out upstairs is `D(f) ∩ D(q)`** — the bullet above with a
  second polynomial carried along, and that bullet again at the polynomial 1. It is what a consumer
  holding **two** polynomials on one member needs, and it is the geometric half of the
  doubly-distinguished condition at a same-member pair; its one consumer is named in its own
  docstring rather than here, for the reason the bullet above gives about backticked tokens.

## What is not here

* **Neither spelling of the range is absent any more — this bullet recorded the scheme-level one
  as missing and it is not.** `ComplexAnalytic.opensRange_Spec_map_localisationRingHom` above is
  `AlgebraicGeometry.Scheme.Hom.opensRange` at the structure map, proved out of
  `AlgebraicGeometry.Scheme.Hom.opensRange_localizationAway`, and it was added when a consumer
  that composes appeared. **The reason this bullet gave was right and is worth keeping**, because
  it is what the proof pays and not what the statement pays:
  `ComplexAnalytic.range_base_specFunctor_map_localisationHom` says the same thing at
  `Set.range … .base`, and it is stated that way because
  `ComplexAnalytic.specLocalisationOpen` is declared at the `ComplexAnalytic.specFunctor.obj`
  spelling: the `Opens → Set` coercion then lands in the type the range already lives in, and the
  unification the scheme-level spelling asks for — between `↥(Spec (CommRingCat.of
  (PresentedAlgebra n k g)))` and `PrimeSpectrum ↑(CommRingCat.of (PresentedAlgebra n k g))`,
  definitionally equal and not unified through that coercion — never arises **there**. It arises
  here, in the `rw` and not in the statement, and `simp only` is what abstracts the instance
  argument that makes the motive ill-typed. **Which of the two a `Spec`-side glue data wants is
  answered**: `Oka/Analytification/SpecAffineCover.lean`'s
  `ComplexAnalytic.specOpen` — the `V` of its glue datum — is `ComplexAnalytic.specLocalisationOpen`
  and nothing else, so it wants the `ComplexAnalytic.specFunctor.obj` spelling, which is the one
  this file has.
* **The `Spec`-side glue data, and the comparison morphism `X^an ⟶ X`.** They are
  `Oka/Analytification/SpecAffineCover.lean` and `Oka/Analytification/CoverComparison.lean` now,
  and **what they took from this file is the *open* and the *isomorphism*, not `f_open`**:
  `ComplexAnalytic.specLocalisationOpen` is that file's `ComplexAnalytic.specOpen` and
  `ComplexAnalytic.specLocalisationIso` is its `ComplexAnalytic.specOverlapIso`, while the glue
  datum's `f_open` field comes from
  `AlgebraicGeometry.LocallyRingedSpace.isOpenImmersion_ofRestrict` through
  `AlgebraicGeometry.LocallyRingedSpace.isOpenImmersion_f'`, which is the same choice the analytic
  side makes. **This bullet predicted "`f_open` and nothing else" and the delivered construction
  inverted it**, which is what a forward reference costs when the file it points at is written by
  somebody else. The `hrange` hypothesis that construction also needs is a statement about ranges
  of maps on points, and unlike the cocycle equation it does not transport along a functor — that
  half of the prediction held.
* **Anything analytic.** No morphism of analytic spaces appears below, and nothing in
  `Oka/Analytification/AffineCover.lean` changes.
-/

open CategoryTheory AlgebraicGeometry

universe u

namespace ComplexAnalytic

noncomputable section

variable {n k : ℕ} (g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ)
  (f : MvPolynomial (ULift.{u} (Fin n)) ℂ)

/-! ### The identification of the localised presentation, in `CommRingCat` -/

/-- **`ComplexAnalytic.localisationPresentedAlgebraEquiv` as an isomorphism in `CommRingCat`**:
`ℂ[x, t] ⧸ (g, t·f - 1)` and `Localization.Away (mk f)` are the same object of the category
`AlgebraicGeometry.Spec.map` is a functor out of.

A `≃ₐ[ℂ]` cannot be handed to `AlgebraicGeometry.Spec.map`, and the two rewrites below are about
composites of `CommRingCat` morphisms, so the bundled form is what both of them need. -/
def specLocalisationRingIso :
    CommRingCat.of (PresentedAlgebra.{u} (n + 1) (k + 1) (localisationPresentation.{u} g f)) ≅
      CommRingCat.of (Localization.Away (Ideal.Quotient.mk (presentationIdeal.{u} g) f)) :=
  (localisationPresentedAlgebraEquiv.{u} g f).toRingEquiv.toCommRingCatIso

/-- **The triangle over `A`**: the structure map `A ⟶ A_f`, followed by the identification of
`A_f` with the localisation, is the localisation's own `algebraMap`.

This is `ComplexAnalytic.localisationPresentedAlgebraEquiv_localisationRingHom` — the statement
that the identification is an isomorphism over `A` and not merely over `ℂ` — read in
`CommRingCat`, which is the only thing the two results below use it for. -/
theorem localisationRingHom_comp_eq :
    CommRingCat.ofHom (localisationRingHom.{u} g f) ≫ (specLocalisationRingIso.{u} g f).hom =
      CommRingCat.ofHom (algebraMap (PresentedAlgebra.{u} n k g)
        (Localization.Away (Ideal.Quotient.mk (presentationIdeal.{u} g) f))) :=
  CommRingCat.hom_ext (RingHom.ext (localisationPresentedAlgebraEquiv_localisationRingHom.{u} g f))

/-! ### The open immersion -/

/-- **`Spec` of the structure map `A ⟶ A_f` is an open immersion.**

The structure map is the localisation's `algebraMap` composed with an isomorphism, by the triangle
above; `AlgebraicGeometry.Spec.map` turns that into a composite of `Spec` of the `algebraMap` —
where Mathlib's `AlgebraicGeometry.Scheme.isOpenImmersion_SpecMap_localizationAway` applies — with
an isomorphism, and open immersions absorb isomorphisms.

Stated at the scheme-level spelling because that is where Mathlib's API is; the locally ringed
space this repository glues with is the same term, which is the next declaration. -/
theorem isOpenImmersion_Spec_map_localisationRingHom :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (localisationRingHom.{u} g f))) := by
  have h : CommRingCat.ofHom (localisationRingHom.{u} g f) =
      CommRingCat.ofHom (algebraMap (PresentedAlgebra.{u} n k g)
        (Localization.Away (Ideal.Quotient.mk (presentationIdeal.{u} g) f))) ≫
        (specLocalisationRingIso.{u} g f).inv := by
    rw [← localisationRingHom_comp_eq, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [h, Spec.map_comp]
  infer_instance

/-- **The functor's value on the structure map is an open immersion**, which is the form a glue
data on the `Spec` side of an affine cover holds its morphisms in.

**An `instance`, and stated at the `ComplexAnalytic.specFunctor` spelling rather than at
`AlgebraicGeometry.Spec.map`, because that is the one a glue datum presents to instance search.**
Two declarations below take it as one, both through
`AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.isoOfRangeEq`:
`ComplexAnalytic.specLocalisationIso`, and `ComplexAnalytic.specLocalisationIso_hom_ofRestrict`
through that lemma's `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.isoOfRangeEq_hom_fac`.
Demoting this declaration back to a `theorem` leaves exactly those two failing and nothing else,
which is how the pair was found rather than guessed. An instance at the other spelling would be
found for a goal about this one only up to the reducible unfolding the theorem above records, and
**instance search does not cross that identity** — measured in this file's module docstring.

Taken at `ComplexAnalytic.localisationHom`, which is the structure map read as a morphism of
*objects* of `ComplexAnalytic.Presentation` — `ComplexAnalytic.localisationPresHom` does not
elaborate against `Functor.map`, for the reason its own docstring gives.

The mirror of `ComplexAnalytic.isOpenImmersion_analytificationMap_localisationPresHom`, and the
proof is the theorem above **with no transport**: `ComplexAnalytic.specFunctor.map` is
`AlgebraicGeometry.Spec.locallyRingedSpaceMap` of the underlying ring map, which is
`(AlgebraicGeometry.Spec.map _).toLRSHom`, and `AlgebraicGeometry.IsOpenImmersion` of a scheme
morphism is `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion` of that, so the declaration is
what makes the scheme-level API reachable from a locally-ringed-space glue data. -/
instance isOpenImmersion_specFunctor_map_localisationHom :
    LocallyRingedSpace.IsOpenImmersion (specFunctor.{u}.map (localisationHom.{u} g f)) :=
  isOpenImmersion_Spec_map_localisationRingHom.{u} g f

/-! ### The image of the morphism -/

/-- **`D(f) ⊆ Spec A`**, the basic open at the class of `f`, as an open subset of
`ComplexAnalytic.specFunctor`'s value.

The counterpart of `ComplexAnalytic.localisationOpen`, and the two are deliberately not related
here: one is a non-vanishing locus in an analytic space and the other a basic open of a spectrum,
and the statement that the comparison morphism carries the second to the first is about a cover
and belongs wherever that cover is built.

**Naming it is what makes the range statable**, and that is the whole of the difficulty this
file's `## What is not here` used to record: a bare
`Set.range … = ↑(PrimeSpectrum.basicOpen (mk f))` asks the `Opens → Set` coercion to unify
`↥(specFunctor.obj ⟨n, k, g⟩)` with `PrimeSpectrum ↑(CommRingCat.of (PresentedAlgebra n k g))`,
which are definitionally equal and do not unify through it. An `Opens` declared **at the
`specFunctor.obj` spelling** never poses that question, because its coercion is to a set of the
type the range already lives in. -/
def specLocalisationOpen : TopologicalSpace.Opens (specFunctor.{u}.obj ⟨n, k, g⟩) :=
  PrimeSpectrum.basicOpen (Ideal.Quotient.mk (presentationIdeal.{u} g) f)

/-- **The image of the morphism is exactly `D(f)`.**

The equality and not the containment, for the reason
`ComplexAnalytic.range_base_localisationProj` gives on the analytic side: the side condition of an
open-immersion lift is a containment *in* this range, so an equality is what lets a statement about
`D(f)` discharge it. It is what a `Spec`-side glue data's `hrange` obligation will be checked
against — **still a prediction.** A containment goes through
`AlgebraicGeometry.LocallyRingedSpace.range_ofRestrict` without this theorem, as
`ComplexAnalytic.range_specTransitionHom_subset` does, so what is untested is not the containment
but **the equality** — nothing has yet needed the range of a distinguished open's inclusion to be
*exactly* `D(f)` rather than contained in it, which is what a three-member `Spec`-side cover would
be the first thing to ask for.

The triangle over `A` again: the isomorphism's half is surjective, and
`PrimeSpectrum.localization_away_comap_range` supplies the algebra map's half. -/
theorem range_base_specFunctor_map_localisationHom :
    Set.range (specFunctor.{u}.map (localisationHom.{u} g f)).base =
      (specLocalisationOpen.{u} g f : Set (specFunctor.{u}.obj ⟨n, k, g⟩)) := by
  have h : CommRingCat.ofHom (localisationRingHom.{u} g f) =
      CommRingCat.ofHom (algebraMap (PresentedAlgebra.{u} n k g)
        (Localization.Away (Ideal.Quotient.mk (presentationIdeal.{u} g) f))) ≫
        (specLocalisationRingIso.{u} g f).inv := by
    rw [← localisationRingHom_comp_eq, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  change Set.range (Spec.locallyRingedSpaceMap
    (CommRingCat.ofHom (localisationRingHom.{u} g f))).base = _
  rw [h, Spec.locallyRingedSpaceMap_comp, LocallyRingedSpace.comp_base, TopCat.coe_comp,
    Set.range_comp]
  have hiso : IsIso (Spec.locallyRingedSpaceMap (specLocalisationRingIso.{u} g f).inv) :=
    ⟨Spec.locallyRingedSpaceMap (specLocalisationRingIso.{u} g f).hom, by
      rw [← Spec.locallyRingedSpaceMap_comp, Iso.hom_inv_id, Spec.locallyRingedSpaceMap_id], by
      rw [← Spec.locallyRingedSpaceMap_comp, Iso.inv_hom_id, Spec.locallyRingedSpaceMap_id]⟩
  have hs : Set.range (Spec.locallyRingedSpaceMap (specLocalisationRingIso.{u} g f).inv).base =
      Set.univ :=
    Set.range_eq_univ.2 (LocallyRingedSpace.homeoOfIso (asIso (Spec.locallyRingedSpaceMap
      (specLocalisationRingIso.{u} g f).inv))).surjective
  rw [hs, Set.image_univ]
  exact PrimeSpectrum.localization_away_comap_range _ _

/-! ### The isomorphism with the open subspace -/

/-- **`Spec (A_f) ≅ Spec A|D(f)`**, the counterpart of `ComplexAnalytic.localisationIso`.

Where the analytic side builds its isomorphism by hand out of two morphisms and two round trips,
this one is `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.isoOfRangeEq` at the morphism and
the inclusion of the open subspace: both are open immersions and
`ComplexAnalytic.range_base_specFunctor_map_localisationHom` says they have the same image. That is
what the instance above is for. -/
def specLocalisationIso :
    specFunctor.{u}.obj ⟨n + 1, k + 1, localisationPresentation.{u} g f⟩ ≅
      (specFunctor.{u}.obj ⟨n, k, g⟩).restrict
        (specLocalisationOpen.{u} g f).isOpenEmbedding :=
  LocallyRingedSpace.IsOpenImmersion.isoOfRangeEq
    (specFunctor.{u}.map (localisationHom.{u} g f))
    ((specFunctor.{u}.obj ⟨n, k, g⟩).ofRestrict (specLocalisationOpen.{u} g f).isOpenEmbedding)
    ((range_base_specFunctor_map_localisationHom.{u} g f).trans
      ((specFunctor.{u}.obj ⟨n, k, g⟩).range_ofRestrict (specLocalisationOpen.{u} g f)).symm)

/-- **The isomorphism is one over `Spec A`**: followed by the inclusion of the open subspace it is
the morphism. -/
@[reassoc (attr := simp)]
theorem specLocalisationIso_hom_ofRestrict :
    (specLocalisationIso.{u} g f).hom ≫
        (specFunctor.{u}.obj ⟨n, k, g⟩).ofRestrict
          (specLocalisationOpen.{u} g f).isOpenEmbedding =
      specFunctor.{u}.map (localisationHom.{u} g f) :=
  LocallyRingedSpace.IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- **The inverse is a morphism over `Spec A` too**: followed by the morphism it is the inclusion
of the open subspace. -/
@[reassoc (attr := simp)]
theorem specLocalisationIso_inv_specFunctor_map :
    (specLocalisationIso.{u} g f).inv ≫ specFunctor.{u}.map (localisationHom.{u} g f) =
      (specFunctor.{u}.obj ⟨n, k, g⟩).ofRestrict
        (specLocalisationOpen.{u} g f).isOpenEmbedding := by
  rw [← specLocalisationIso_hom_ofRestrict.{u} g f, Iso.inv_hom_id_assoc]

/-! ### The range, at the scheme-level spelling -/

section OpensRange

attribute [local instance] isOpenImmersion_Spec_map_localisationRingHom

/-- **The range of `Spec` of the structure map is `D(f)`**, at
`AlgebraicGeometry.Scheme.Hom.opensRange` — Mathlib's idiomatic spelling, and the one a consumer
that composes this morphism with another open immersion has to have.

`ComplexAnalytic.range_base_specFunctor_map_localisationHom` above is the same fact at
`Set.range … .base` and at the `ComplexAnalytic.specFunctor.obj` spelling, which is what a
`Spec`-side glue datum wants. **This one is for a consumer that is composing**, since
`AlgebraicGeometry.Scheme.Hom.opensRange_comp` is stated at `opensRange` and has no `Set.range`
form: `Oka/Analytification/SpecRefinedMember.lean` is the first such consumer.

**The unification this file's `## What is not here` priced is real and it is the `rw` that pays
it, not the statement.** The two `Opens` types — over `↥(Spec (CommRingCat.of (PresentedAlgebra n
k g)))` and over `PrimeSpectrum ↑(CommRingCat.of (PresentedAlgebra n k g))` — are definitionally
equal, so the statement elaborates; what fails is `rw`, with *"motive is not type correct"*,
because `AlgebraicGeometry.Scheme.Hom.opensRange` carries an
`AlgebraicGeometry.IsOpenImmersion` argument that depends on the morphism being rewritten. **Two
things buy it and both are one word**: `simp only` rather than `rw`, which abstracts the instance
argument, and naming `R` explicitly in the final `exact`, since Mathlib's lemma is stated for
`R : CommRingCat` and the `algebraMap` here has a bare type as its source.

**`attribute [local instance]`, scoped to this section, rather than a `have`.** The instance is
needed to *state* the theorem, not only to prove it, so a `have` cannot supply it; and
`ComplexAnalytic.isOpenImmersion_Spec_map_localisationRingHom` is deliberately a theorem rather
than an instance, for the reason its sibling's docstring gives. Nothing above this section is
elaborated with it in scope. -/
theorem opensRange_Spec_map_localisationRingHom :
    (Spec.map (CommRingCat.ofHom (localisationRingHom.{u} g f))).opensRange =
      PrimeSpectrum.basicOpen (Ideal.Quotient.mk (presentationIdeal.{u} g) f) := by
  have h : CommRingCat.ofHom (localisationRingHom.{u} g f) =
      CommRingCat.ofHom (algebraMap (PresentedAlgebra.{u} n k g)
        (Localization.Away (Ideal.Quotient.mk (presentationIdeal.{u} g) f))) ≫
        (specLocalisationRingIso.{u} g f).inv := by
    rw [← localisationRingHom_comp_eq, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  simp only [h, Spec.map_comp, Scheme.Hom.opensRange_comp_of_isIso]
  exact Scheme.Hom.opensRange_localizationAway
    (R := CommRingCat.of (PresentedAlgebra.{u} n k g))
    (Ideal.Quotient.mk (presentationIdeal.{u} g) f)

/-- **And the image of a basic open of `A_f` cut out by a renamed polynomial is the overlap of the
two basic opens of `A`** — the theorem above with a second polynomial carried along.

`ComplexAnalytic.localisationIncl` adjoins the new variable, so
`MvPolynomial.rename (localisationIncl n) q` is `q` read as a polynomial on `D(f)`; this says the
open it cuts out of `D(f)` is exactly `D(f) ∩ D(q)`, computed downstairs in `Spec A`.

**It is the theorem above and not a second fact about the morphism.** The renamed polynomial's
class is the image of `q`'s class under the structure map — `ComplexAnalytic.localisationRingHom_mk`
says so by `rfl` — so the basic open upstairs is the *preimage* of `D(q)` by
`AlgebraicGeometry.SpecMap_preimage_basicOpen`, which is also `rfl`; the whole `have` below is
therefore one `rfl` and not a rewrite. What remains is
`AlgebraicGeometry.Scheme.Hom.image_preimage_eq_opensRange_inf`, the general fact that an open
immersion's image of a preimage is its range met with the open, and the range is the theorem above.

**`q = 1` is the theorem above**, since `MvPolynomial.rename` is a ring map, `D(1) = ⊤` and an open
immersion's image of `⊤` is its range — so nothing here is independent of it, and this is the form
a consumer that has *two* polynomials in hand needs.

**That consumer is `ComplexAnalytic.opensRange_presentationRefinedIota_rename`**
(`Oka/Analytification/SpecRefinedMemberSection.lean`), and it is the only one: it carries this
statement along an arbitrary open immersion by `AlgebraicGeometry.Scheme.Hom.comp_image` and is
the doubly-distinguished condition at a same-member pair. **It is named here and not in the
`## Main results` bullet that points at this docstring**, because a backticked name belonging to
another file under that heading is read as a result *this* file advertises.

**The trailing `rfl` is the same unification the theorem above pays for in its proof and not in its
statement**, and it is here for the same reason: the two `Opens` types are definitionally equal and
the `rw` closes the goal up to that identity rather than through it. -/
theorem image_basicOpen_rename_Spec_map_localisationRingHom
    (q : MvPolynomial (ULift.{u} (Fin n)) ℂ) :
    Spec.map (CommRingCat.ofHom (localisationRingHom.{u} g f)) ''ᵁ
        PrimeSpectrum.basicOpen (Ideal.Quotient.mk
          (presentationIdeal.{u} (localisationPresentation.{u} g f))
          (MvPolynomial.rename (localisationIncl.{u} n) q)) =
      PrimeSpectrum.basicOpen (Ideal.Quotient.mk (presentationIdeal.{u} g) f) ⊓
        PrimeSpectrum.basicOpen (Ideal.Quotient.mk (presentationIdeal.{u} g) q) := by
  have h : PrimeSpectrum.basicOpen (Ideal.Quotient.mk
      (presentationIdeal.{u} (localisationPresentation.{u} g f))
      (MvPolynomial.rename (localisationIncl.{u} n) q)) =
      Spec.map (CommRingCat.ofHom (localisationRingHom.{u} g f)) ⁻¹ᵁ
        PrimeSpectrum.basicOpen (Ideal.Quotient.mk (presentationIdeal.{u} g) q) := rfl
  rw [h, Scheme.Hom.image_preimage_eq_opensRange_inf,
    opensRange_Spec_map_localisationRingHom]
  rfl

end OpensRange

end

end ComplexAnalytic
