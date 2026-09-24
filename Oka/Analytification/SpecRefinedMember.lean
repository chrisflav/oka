/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Analytification.SpecScheme
import Oka.Analytification.SpecDistinguishedOpen

/-!
# A distinguished open of a member is an affine open of the glued scheme

`Oka/Analytification/SpecScheme.lean` glues a cover datum into a scheme `X` and shows that each
member is an affine open of it: `ComplexAnalytic.specSchemeIota` is the inclusion and
`ComplexAnalytic.isAffineOpen_specSchemeIota` is the statement. That file's
`ComplexAnalytic.exists_basicOpen_specSchemeIota_inter` then says that every point of an overlap
lies in an open **distinguished in each of the two members** — an existential about opens, with
nothing exhibiting those opens as members of anything.

This file exhibits them. For a member `i` and a polynomial `p` in that member's own variables,
`D(p)` carries the presentation `ComplexAnalytic.localisationPresentation (obj i).g p`, and the
composite of `Spec` of the structure map with the member's own inclusion is an open immersion into
`X` whose range is exactly `D(p)` seen in `X`. **So a refined member is the same kind of object as
the member it refines** — an affine open of `X`, presented — and no transport is needed to say so.

## Two levels, and the general one is where the content is

Everything below is stated **twice**: once at an arbitrary open immersion
`f : Spec (CommRingCat.of P.alg) ⟶ X` out of a presented algebra's spectrum, and once at
`ComplexAnalytic.specSchemeIota`, the inclusion of a member of a cover datum. **The member-level
form is the general one applied and every one of its proofs is a single application**; the
mathematics is in the general form and the specialisation only fixes the immersion.

**That is not symmetry for its own sake, and the cost of the one-level shape has already been paid
once in this development.** `Oka/Analytification/SpecMemberSections.lean` states
`ComplexAnalytic.presentationSection` and its two lemmas at an arbitrary immersion, and says on
the declaration why: a member of a *second* cover datum carried into the first datum's scheme is
`ComplexAnalytic.specSchemeIotaMap`, **which is not `ComplexAnalytic.specSchemeIota` of anything in
the first datum**, so a lemma stated only at `specSchemeIota` reaches one of the two sides of a
cross-datum statement and not the other. An earlier head of that file was one-level and mispriced
the cross-datum theorem as a consequence; `Oka/Analytification/SpecTwoData.lean`'s bullet on
`ComplexAnalytic.exists_index_mvPolynomial_basicOpen_specSchemeIotaMap` records the same event
from the other side — *"the statement became cheap when that file restated its three lemmas at an
arbitrary open immersion."*

**A refined member of the second datum is exactly that situation**: what the choice step
`ComplexAnalytic.exists_family_mvPolynomial_basicOpen_specSchemeIotaMap`
(`Oka/Analytification/SpecMemberChoice.lean`) hands a caller is, at every point, a member of each
of two data and a polynomial in each member's own variables, and only one of those two members is
a `specSchemeIota`. **The general form below is what makes both refinable by one name.** No
*statement* in this file mentions a second datum — the `## What is not here` bullet that says so
is still true and now says explicitly that a legal argument is not an appearance — but the
immersion is an argument rather than a fixed morphism, so a caller may supply one.

## Main definitions

- `ComplexAnalytic.presentationRefinedPres`: **`D(p)`'s presentation**, for a polynomial `p` in
  the variables of an arbitrary `ComplexAnalytic.Presentation` — that presentation with one
  variable and one equation adjoined.
- `ComplexAnalytic.presentationRefinedIota`: **its inclusion into `X`** along an arbitrary open
  immersion, as `Spec` of the structure map followed by that immersion.
- `ComplexAnalytic.refinedPres`: **the first at the `i`-th member of a cover datum.**
- `ComplexAnalytic.refinedIota`: **the second at `ComplexAnalytic.specSchemeIota`.**

## Main results

- `ComplexAnalytic.isOpenImmersion_presentationRefinedIota`: **the inclusion is an open
  immersion**, which is what lets the two below be stated at all.
- `ComplexAnalytic.isAffineOpen_presentationRefinedIota`: **its range is an affine open of `X`** —
  the statement in the title and the reason the file exists.
- `ComplexAnalytic.opensRange_presentationRefinedIota`: **and that range is exactly the image of
  `D(p)`**, so the open is the one a caller named rather than merely some open the construction
  produced.
- `ComplexAnalytic.opensRange_presentationRefinedIota_le`: **and it is contained in the open the
  immersion presents**, which is the containment the word *refinement* usually means and is the
  one-lemma consequence of the equation above.
- `ComplexAnalytic.isOpenImmersion_refinedIota`, `ComplexAnalytic.isAffineOpen_refinedIota`,
  `ComplexAnalytic.opensRange_refinedIota` and `ComplexAnalytic.opensRange_refinedIota_le`: **the
  same four at a member of a cover datum**, each the general form at the member's own inclusion
  and nothing else.

## What is not here, and the first two bullets are the operative ones

* **No choice function, and no family.** Taxis #1553 asks for a point-by-point existential —
  `ComplexAnalytic.exists_index_mvPolynomial_basicOpen_specSchemeIotaMap`, which gives at every
  point of `X` and an isomorphism of two cover data two indices and two polynomials in the
  members' own variables — to be turned into four chosen functions by `choose`. **That is one
  tactic and it is deliberately a separate file**, `Oka/Analytification/SpecMemberChoice.lean`,
  which has since landed. It was not merely out of scope when this file
  was written but unwritable: the theorem arrives with
  `Oka/Analytification/SpecMemberSections.lean`, which lana-agents/oka#374 added *after* this
  branch was cut, so there was nothing to `choose` from. Landing that branch removed the obstacle
  and did not put the step here. **This file indexes nothing by the points of `X`**, which is not
  a cover datum's index type and is not claimed to be one.
* **Nothing is said in terms of a polynomial read as a *section* of `X` either**, and that too is
  now a scope decision rather than a blocked one. `ComplexAnalytic.presentationSection` is the
  definition that reads a polynomial as a section over the range of an open immersion, and
  `ComplexAnalytic.basicOpen_presentationSection` says which open of `X` it cuts out; both arrived
  with lana-agents/oka#374, after this branch was cut.
  `ComplexAnalytic.opensRange_refinedIota` below states the range as the image of a
  `PrimeSpectrum.basicOpen` instead — **which is a statement about the open itself, and stays the
  usable one for a reader who has not imported that file.** **The section spelling of this range
  has since been added, and not to this file either**:
  `ComplexAnalytic.opensRange_presentationRefinedIota_eq_basicOpen`
  (`Oka/Analytification/SpecRefinedMemberSection.lean`) is
  `ComplexAnalytic.opensRange_presentationRefinedIota` composed with
  `ComplexAnalytic.basicOpen_presentationSection`, whose right-hand sides are the same term, and
  `ComplexAnalytic.opensRange_refinedIota_eq_basicOpen` is that at
  `ComplexAnalytic.specSchemeIota`. **This bullet named the member-level theorem as the
  composition until the general level landed, and that is now where the composing happens**; the
  correction is recorded rather than made silently, since the sentence was about a proof and the
  proof moved.
  **This bullet used to price that step as *one rewrite* and to say it belonged with the choice
  step; both are corrected rather than deleted.** It is `Eq.trans` and `Eq.symm` and no rewrite at
  all — the `AlgebraicGeometry.Scheme.Hom.opensRange` motive hazard never arises for a term — and
  the choice step landed without it: the file named in the bullet above has the `choose` and not
  this equation. **Keeping it out of this file is the decision that clause above records**, since
  the import would make this file's own reader one who has imported that file.
* **No `poly`, no `glue`, and none of a cover datum's three laws.** That is the rest of
  `Oka/Analytification/SpecScheme.lean`'s third piece and it is taxis #1287's line, not this one —
  `Oka/Analytification/CrossMemberDatum.lean`, `Oka/Analytification/CrossMemberDatumGlue.lean` and
  the `Oka/Analytification/RefineDatum*.lean` files. **Nothing here is a cover datum and nothing
  here claims to refine one.** Two members' distinguished opens are not compared, in either
  direction: `i` and `p` are one member and one polynomial.
* **No common refinement, and no second cover datum.** `ComplexAnalytic.specSchemeIotaMap` and
  `Oka/Analytification/SpecTwoData.lean`'s two-datum vocabulary do not appear. **What the general
  level changes is that such a morphism is now a legal argument, which is not the same as
  appearing**: no *statement* below mentions a second datum, quantifies over one, or says anything
  about two — the general declaration's own docstring names `ComplexAnalytic.specSchemeIotaMap` as
  the immersion this is for, and naming it in prose is not asserting anything about it. The
  immersion being an argument rather than a fixed morphism is exactly what keeps that true while
  making the statement usable there.
* **Nothing analytic.** No analytification, no `X^an`, no comparison morphism.
* **Nothing about `p` being non-zero, or `D(p)` being non-empty.** At `p = 0` everything below is
  a statement about the empty open and stays true; nothing here excludes it and nothing here
  needs to.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry

universe u

namespace ComplexAnalytic

noncomputable section

/-! ### A distinguished open of any presented affine open -/

/-- **The presentation of `D(p)` inside a presentation**, as an object of
`ComplexAnalytic.Presentation`.

`ComplexAnalytic.localisationPresentation` at that presentation's own relations: one variable and
one equation more. **An `abbrev` and not a `def`**, so that
`ComplexAnalytic.localisationRingHom`'s codomain and this object's
`ComplexAnalytic.Presentation.alg` are the same term without a `change` — the same reason
`ComplexAnalytic.refineDatumObj` (`Oka/Analytification/CrossMemberDatum.lean`) is one, and this is
that object at the `Spec` side's spelling of the same situation.

The tuple is `Fin.snoc`'d with `X_last · p − 1` and **not** with a reduced form of it; see
`ComplexAnalytic.localisationPresentation`'s own docstring.

**The presentation is an explicit argument of its own and not the section variable below**, which
is forced rather than chosen: this object does not mention the immersion, so a section variable
would not be included, and `P` is not inferable from `p : MvPolynomial (ULift (Fin P.n)) ℂ`
because `P.n` does not determine `P`. Stating it with the presentation implicit fails to
elaborate at the first use. -/
abbrev presentationRefinedPres (P : Presentation.{u})
    (p : MvPolynomial (ULift.{u} (Fin P.n)) ℂ) : Presentation.{u} :=
  ⟨P.n + 1, P.k + 1, localisationPresentation.{u} P.g p⟩

section

variable {X : Scheme.{u}} {P : Presentation.{u}} (f : Spec (CommRingCat.of P.alg) ⟶ X)
  [IsOpenImmersion f]

/-- **The inclusion of `D(p)` into `X`**, along an arbitrary open immersion out of a presented
algebra's spectrum.

`Spec` of the structure map `A ⟶ A_p`, followed by `f`. Both factors are already here — the first
is `Oka/Analytification/SpecDistinguishedOpen.lean`'s and the second is the caller's — and **the
only content is that they compose**, which they do because `ComplexAnalytic.Presentation.alg` is
an `abbrev` and the codomain of `ComplexAnalytic.localisationRingHom` is
`ComplexAnalytic.presentationRefinedPres`'s algebra on the nose.

The scheme-level spelling and not `ComplexAnalytic.specFunctor`'s: the target is an
`AlgebraicGeometry.Scheme` and `f` is a morphism of schemes.

**The immersion is arbitrary and that is the point**, for the reason
`ComplexAnalytic.presentationSection` (`Oka/Analytification/SpecMemberSections.lean`) gives of
itself: a member of a cover datum reaches this at `ComplexAnalytic.specSchemeIota`, and a member
of a *second* datum carried into the first datum's scheme reaches it at
`ComplexAnalytic.specSchemeIotaMap`, which is not `specSchemeIota` of anything in the first
datum. -/
def presentationRefinedIota (p : MvPolynomial (ULift.{u} (Fin P.n)) ℂ) :
    Spec (CommRingCat.of (presentationRefinedPres.{u} P p).alg) ⟶ X :=
  Spec.map (CommRingCat.ofHom (localisationRingHom.{u} P.g p)) ≫ f

/-- **It is an open immersion**, being a composite of two.

`AlgebraicGeometry.IsOpenImmersion.comp` at
`ComplexAnalytic.isOpenImmersion_Spec_map_localisationRingHom` — which is a *theorem* and not an
instance, so it is supplied by a `haveI` in the proof — and the `AlgebraicGeometry.IsOpenImmersion`
instance the caller supplies for `f`.

**A `haveI` here and an `attribute [local instance]` in
`Oka/Analytification/SpecDistinguishedOpen.lean`, and the difference is not a matter of taste**:
there the instance is needed to *state* the theorem, where a `haveI` cannot reach; here it is
needed only inside the proof, and the narrower tool is the right one.

**An `instance` and not a theorem**, because `AlgebraicGeometry.Scheme.Hom.opensRange` takes one
as an argument and the two statements below are about that range: without it neither of them can
be *stated*. -/
instance isOpenImmersion_presentationRefinedIota (p : MvPolynomial (ULift.{u} (Fin P.n)) ℂ) :
    IsOpenImmersion (presentationRefinedIota.{u} f p) :=
  haveI := isOpenImmersion_Spec_map_localisationRingHom.{u} P.g p
  IsOpenImmersion.comp _ _

/-- **A distinguished open of a presented affine open of `X` is an affine open of `X`** — the
statement this file exists for.

`AlgebraicGeometry.isAffineOpen_opensRange` at the instance above, exactly as
`ComplexAnalytic.isAffineOpen_specSchemeIota` gets a member's own statement: the
`AlgebraicGeometry.IsAffine` side condition is on the *source*, and the source here is a spectrum.

**What this adds to that theorem is that the affine opens of `X` this development can name are
closed under passing to a distinguished open of one of them**, with the presentation carried
along — `ComplexAnalytic.presentationRefinedPres` — rather than with the open produced abstractly
and its affineness argued afterwards. -/
theorem isAffineOpen_presentationRefinedIota (p : MvPolynomial (ULift.{u} (Fin P.n)) ℂ) :
    IsAffineOpen (presentationRefinedIota.{u} f p).opensRange :=
  isAffineOpen_opensRange _

/-- **And the open it is, is the one the caller named**: the image under `f` of the basic open of
`p`'s class in the presented algebra.

`AlgebraicGeometry.Scheme.Hom.opensRange_comp` and
`ComplexAnalytic.opensRange_Spec_map_localisationRingHom`. **Without this the two theorems above
say only that *some* affine open of `X` is presented by
`ComplexAnalytic.presentationRefinedPres`**, and a caller who chose `p` to cut out a particular
open — which is what `ComplexAnalytic.exists_basicOpen_specSchemeIota_inter` produces at a member
— could not tell that it got that one. This is the statement that makes
`ComplexAnalytic.presentationRefinedIota` a *refinement* of the open `f` presents rather than an
unrelated affine open of `X` that happens to sit inside it.

**The image and not a `Set.range`, and that is why
`ComplexAnalytic.opensRange_Spec_map_localisationRingHom` had to be stated**:
`AlgebraicGeometry.Scheme.Hom.opensRange_comp` is at `AlgebraicGeometry.Scheme.Hom.opensRange`
and has no `Set.range` form, so `ComplexAnalytic.range_base_specFunctor_map_localisationHom` — the
spelling `Oka/Analytification/SpecAffineCover.lean`'s glue datum wants — cannot be used here.

**The `have … := rfl` rather than naming `ComplexAnalytic.presentationRefinedIota` in the
`simp only`.** It is a `def`, and naming a definition as a rewrite rule generates its equation
lemma into this module, a hazard several files in this tree record. The composite is
definitionally the definition, so `rfl` proves the unfolding and `simp only` consumes it as an
ordinary hypothesis. -/
theorem opensRange_presentationRefinedIota (p : MvPolynomial (ULift.{u} (Fin P.n)) ℂ) :
    (presentationRefinedIota.{u} f p).opensRange =
      f ''ᵁ PrimeSpectrum.basicOpen (Ideal.Quotient.mk (presentationIdeal.{u} P.g) p) := by
  haveI := isOpenImmersion_Spec_map_localisationRingHom.{u} P.g p
  have h : presentationRefinedIota.{u} f p =
      Spec.map (CommRingCat.ofHom (localisationRingHom.{u} P.g p)) ≫ f := rfl
  simp only [h, Scheme.Hom.opensRange_comp, opensRange_Spec_map_localisationRingHom]

/-- **And it sits inside the open the immersion presents.**

`ComplexAnalytic.opensRange_presentationRefinedIota` and
`AlgebraicGeometry.Scheme.Hom.image_le_opensRange`, which is the general statement that the image
of any open is contained in the range.

**This is the statement that makes the word *refinement* mean what it usually means.** The theorem
above says which open the range *is*, in the vocabulary of a `PrimeSpectrum.basicOpen` pushed
forward; a caller who wants only that one affine open of `X` is contained in another — the
ordinary definition of one cover refining another — should not have to unfold an image to get it.
**The containment is a consequence and not an independent fact**, which is why the proof is the
equation followed by one Mathlib lemma and nothing else. -/
theorem opensRange_presentationRefinedIota_le (p : MvPolynomial (ULift.{u} (Fin P.n)) ℂ) :
    (presentationRefinedIota.{u} f p).opensRange ≤ f.opensRange := by
  rw [opensRange_presentationRefinedIota]
  exact Scheme.Hom.image_le_opensRange _ _

end

/-! ### A distinguished open of a member of a cover datum -/

variable {J : Type u} (obj : J → Presentation.{u})
  (poly : ∀ i : J, J → MvPolynomial (ULift.{u} (Fin (obj i).n)) ℂ)
  (glue : ∀ i j : J, coverOverlap.{u} obj poly i j ≅ coverOverlap.{u} obj poly j i)
  (hrange : ∀ i j k : J, i ≠ j → i ≠ k → j ≠ k →
    Set.range (specTripleIncl.{u} obj poly i j k ≫ specTransitionHom.{u} obj poly glue i j).base ⊆
      (specOpen.{u} obj poly j k : Set (specSpace.{u} obj j)))
  (hsymm : ∀ i j : J, glue j i = (glue i j).symm)
  (hcocycle : ∀ i j k : J, ∀ hij : i ≠ j, ∀ hik : i ≠ k, ∀ hjk : j ≠ k,
    specTriple.{u} obj poly glue hrange i j k hij hik hjk ≫
      specTriple.{u} obj poly glue hrange j k i hjk hij.symm hik.symm ≫
      specTriple.{u} obj poly glue hrange k i j hik.symm hjk.symm hij = 𝟙 _)

/-- **The presentation of `D(p)` inside the `i`-th member.**

`ComplexAnalytic.presentationRefinedPres` at the member's own presentation. What the
specialisation adds is the index: the general form is at a presentation the reader supplies, and
here it is the `i`-th member's, so the object is named by a member of this cover datum. -/
abbrev refinedPres (i : J) (p : MvPolynomial (ULift.{u} (Fin (obj i).n)) ℂ) : Presentation.{u} :=
  presentationRefinedPres.{u} (obj i) p

/-- **The inclusion of `D(p)` into `X`.**

`ComplexAnalytic.presentationRefinedIota` at `ComplexAnalytic.specSchemeIota`, which is an open
immersion out of `Spec` of `(obj i).alg`. It is a declaration of its own and not a local
abbreviation because the immersion carries the whole cover datum: the general form takes six
arguments before the index, and every statement below that mentions one member of one datum would
spell them twice. That is `ComplexAnalytic.specSchemeIotaSection`'s reason for existing, in that
declaration's own words, and it is this one's. -/
def refinedIota (i : J) (p : MvPolynomial (ULift.{u} (Fin (obj i).n)) ℂ) :
    Spec (CommRingCat.of (refinedPres.{u} obj i p).alg) ⟶
      specScheme.{u} obj poly glue hrange hsymm hcocycle :=
  presentationRefinedIota.{u} (specSchemeIota.{u} obj poly glue hrange hsymm hcocycle i) p

/-- **It is an open immersion.**

`ComplexAnalytic.isOpenImmersion_presentationRefinedIota` at the same immersion, whose own
`AlgebraicGeometry.IsOpenImmersion` instance is
`ComplexAnalytic.isOpenImmersion_specSchemeIota` and is found. **An `instance` and not a theorem**,
for the reason the general form gives: the two statements below are about a
`AlgebraicGeometry.Scheme.Hom.opensRange` and cannot be stated without one. -/
instance isOpenImmersion_refinedIota (i : J)
    (p : MvPolynomial (ULift.{u} (Fin (obj i).n)) ℂ) :
    IsOpenImmersion (refinedIota.{u} obj poly glue hrange hsymm hcocycle i p) :=
  isOpenImmersion_presentationRefinedIota.{u}
    (specSchemeIota.{u} obj poly glue hrange hsymm hcocycle i) p

/-- **A distinguished open of a member is an affine open of `X`** — the statement in this file's
title.

`ComplexAnalytic.isAffineOpen_presentationRefinedIota` at the same immersion. What the
specialisation adds is that the affine open is a distinguished open of a *member of this cover
datum*, which is the form `Oka/Analytification/SpecScheme.lean`'s
`ComplexAnalytic.exists_basicOpen_specSchemeIota_inter` produces its opens in. -/
theorem isAffineOpen_refinedIota (i : J) (p : MvPolynomial (ULift.{u} (Fin (obj i).n)) ℂ) :
    IsAffineOpen (refinedIota.{u} obj poly glue hrange hsymm hcocycle i p).opensRange :=
  isAffineOpen_presentationRefinedIota.{u}
    (specSchemeIota.{u} obj poly glue hrange hsymm hcocycle i) p

/-- **And the open it is, is the one the caller named**: the image under the member's inclusion of
the basic open of `p`'s class in the member's algebra.

`ComplexAnalytic.opensRange_presentationRefinedIota` at the same immersion. What the
specialisation adds is the index: the general form describes the open as the image under *an*
immersion, and here it is the image under the `i`-th member's own, so the open is named by a
member of this cover datum rather than by a morphism the reader has to supply. -/
theorem opensRange_refinedIota (i : J) (p : MvPolynomial (ULift.{u} (Fin (obj i).n)) ℂ) :
    (refinedIota.{u} obj poly glue hrange hsymm hcocycle i p).opensRange =
      specSchemeIota.{u} obj poly glue hrange hsymm hcocycle i ''ᵁ
        PrimeSpectrum.basicOpen (Ideal.Quotient.mk (presentationIdeal.{u} (obj i).g) p) :=
  opensRange_presentationRefinedIota.{u}
    (specSchemeIota.{u} obj poly glue hrange hsymm hcocycle i) p

/-- **And it sits inside the member it refines.**

`ComplexAnalytic.opensRange_presentationRefinedIota_le` at the same immersion. What the
specialisation adds is the index: this is the statement that the refined member is contained in
the `i`-th member of *this* cover datum, which is the form in which a caller comparing a
refinement with the cover it refines wants it. -/
theorem opensRange_refinedIota_le (i : J) (p : MvPolynomial (ULift.{u} (Fin (obj i).n)) ℂ) :
    (refinedIota.{u} obj poly glue hrange hsymm hcocycle i p).opensRange ≤
      (specSchemeIota.{u} obj poly glue hrange hsymm hcocycle i).opensRange :=
  opensRange_presentationRefinedIota_le.{u}
    (specSchemeIota.{u} obj poly glue hrange hsymm hcocycle i) p

end

end ComplexAnalytic
