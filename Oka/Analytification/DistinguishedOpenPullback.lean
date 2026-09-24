/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Analytification.ChangeOfVariables
import Oka.Analytification.DistinguishedOpen

/-!
# A distinguished open pulls back along an analytified algebra map to a distinguished open

`Oka/Analytification/ChangeOfVariables.lean` turns a `ℂ`-algebra map of presented algebras
`ψ : ℂ[y] ⧸ J → ℂ[x] ⧸ I` into a morphism `ComplexAnalytic.analytificationMap ψ : X^an ⟶ Y^an`,
and `Oka/Analytification/DistinguishedOpen.lean` attaches to a polynomial `p` of either
polynomial ring the open `D(p)` on which it does not vanish. This file is the one statement
relating the two:

  **`D(p')` upstairs pulls back to `D(p)`, for any `p` representing `ψ` of the class of `p'`.**

A representative always exists, because `Ideal.Quotient.mk` is surjective, so the existential
form `ComplexAnalytic.exists_localisationOpen_eq_comap_analytificationMap` needs no hypothesis at
all: **every distinguished open of the target pulls back to a distinguished open of the source.**

## There is no geometry in it, and that is the point

The proof is two steps and neither is analytic. Pulling a *section* back along a morphism of
analytic spaces multiplies its value at a point by nothing — `ComplexAnalytic.AnalyticSpace.
nonvanishing_pullbackΓ` says the non-vanishing locus of a pulled-back section is the preimage of
the non-vanishing locus, which is `ComplexAnalytic.AnalyticSpace.eval_c_app` read through
`ComplexAnalytic.AnalyticSpace.mem_nonvanishing_iff`. And the section attached to `p'` pulls back
to the section attached to `p` because `ComplexAnalytic.quotientToGlobal` is natural along the
induced morphism, which is `ComplexAnalytic.Γ_map_analytificationMap_comp_quotientToGlobal`,
proved in `Oka/Analytification/ChangeOfVariables.lean` for functoriality rather than for this.

So the content is the *bookkeeping* between a polynomial, its class in the presented algebra, and
the global section that class names — and the hypothesis is stated on the classes rather than on
the polynomials because that is what the naturality square gives and what a caller holding a
`ComplexAnalytic.PresHom` can check.

## What it is for: the cross-member overlap of a refinement

`Oka/Analytification/AffineCover.lean`'s `poly` field asks for **one polynomial per ordered
pair**, and a refinement of a cover that refines *across* members has to produce one for an
overlap that is cut out inside a localisation and then transported along the cover's own glue
isomorphism. `ComplexAnalytic.exists_localisationOpen_eq_rename` — the previous file — says a
distinguished open of a localisation `(A_f)^an` is always cut out by a renamed polynomial of the
base `A`. What was missing, and is here, is the step before it: that the transported open **is** a
distinguished open of `(A_f)^an` in the first place, which it is because the transport is
`ComplexAnalytic.analytificationMap` of an algebra map.

`ComplexAnalytic.exists_comap_analytificationMap_eq_comap_localisationProj` is the two composed,
and it is the form that answer takes: for any `ℂ`-algebra map out of a presented algebra
`(A_f)`-shaped and any distinguished open `D(p')` of its target, the preimage of `D(p')` is the
preimage along the projection of a distinguished open **of the base `A`** — one polynomial, on the
member the refined piece sits in. Taxis #1287 names this as its item (a); nothing here builds a
refinement. Of the remaining two items of that issue, the transport of the original cover's `glue`
through two localisations is `ComplexAnalytic.refineCrossGlue`
(`Oka/Analytification/CrossMemberGlue.lean`), whose extra factor and unit are **arguments**: that
file produces neither, and names the theorem above, with `ComplexAnalytic.exists_mk_rename_eq`,
as where a caller gets them. **The two geometric laws across members are no longer equally
untouched, and this sentence said they were**: it read *"the two geometric laws across members are
still untouched"*, and for `hrange` that has stopped being so — see the paragraph below. The
datum those two would be laws of now has two fields —
`ComplexAnalytic.refineDatumPoly` (`Oka/Analytification/CrossMemberDatum.lean`), its `poly`, whose
extra factor is the `q` the theorem above produces, and `ComplexAnalytic.refineDatumGlue`
(`Oka/Analytification/CrossMemberDatumGlue.lean`), its `glue`, the branch where the two refined
members lie over one member and the cross-member one under a case split. **The theorem above is
read on that second branch and still only by a caller**: the branch takes the extra factor, the
polynomial `r` and the unit as arguments. **What is no longer true is that nothing supplies them.**
This sentence ended *"and nothing instantiates the existentials that would supply them"* until
`ComplexAnalytic.exists_refineDatumCross` (`Oka/Analytification/CrossMemberChoice.lean`) produced
the extra factor, `r` and the unit at every ordered pair from the *input* datum's symmetry law,
algebraically. **Three existentials did not have to be instantiated; one did, and it is
`ComplexAnalytic.exists_mk_rename_eq`** — that is `Oka/Analytification/CrossMemberDatumGlue.lean`'s
own wording for the correction, and `ComplexAnalytic.exists_refineDatumCrossFactor` is where
`Oka/Analytification/CrossMemberChoice.lean` spends it. The two it does not spend are the two that
produce an equality of *opens*, and an equality of opens does not give an associate — so the
implication that was missing runs the other way, and **it is the one the theorem above supplies**:
`Oka/Analytification/RefineDatumRefinesCross.lean` reads the choice's rule, an identity between
classes, as an equality of opens, by this file's theorem and by the unit lemma beside it in
`Oka/Analytification/DistinguishedOpen.lean`, and concludes that the overlap so refined **is** the
geometric one. This paragraph ended *"that is where the caller still comes in, and this file had
not been opened"*; it has been, and by the consumer it was written for.

**And the two geometric laws no longer stand or fall together.** This paragraph ended *"`hrange`
and `hcocycle` are as untouched as the two laws are"*, which said of both what is now true of only
one. `ComplexAnalytic.refineDatumTransitionHom_localisationProj_of_ne`
(`Oka/Analytification/RefineDatumTransition.lean`) is `hrange`'s cross-member analogue: the refined
transition lies over the original datum's own `ComplexAnalytic.coverTransitionHom`, there being no
morphism between two members of a cover datum for it to lie over instead. **It does not prove
`hrange`.** At a triple whose three members are pairwise different what is left is one containment,
in the caller's own `D(q b c)`, and `ComplexAnalytic.range_refineDatumTransitionHom_subset_iff`
states that as an *equivalence* rather than a sufficient condition, so no weaker hypothesis on the
choice can discharge it; at the mixed triples `ComplexAnalytic.refineDatumGlue` takes its equal
branch, whose triangle is over a *member*, and **that** square has no statement there. The square
over an identification of the two members does, and it is what
`Oka/Analytification/RefineDatumRange.lean` reads the other four shapes off;
`Oka/Analytification/RefineDatumGlueData.lean` joins all five into one law. This sentence ended
*"and the square has no statement there at all"* until the first of those.
**This paragraph said `hcocycle` "keeps the clause", for the reason
`Oka/Analytification/CoverRefinement.lean` gives, and that clause is retired there.** The law is
stated — `ComplexAnalytic.RefineDatumCocycle`, which needed the assembled range law,
`ComplexAnalytic.coverTriple` taking a proof of it as an argument — and
`ComplexAnalytic.refineDatumHcocycle` (`Oka/Analytification/RefineDatumCocycle.lean`) proves it.
**So the two geometric laws do not merely no longer stand or fall together: neither of them is
what a refined datum still owes**, which is the two conditions
`Oka/Analytification/RefineDatumGlueData.lean` adopts and nothing here meets.

## Non-vacuity

Every statement here is an equation of open subsets, so all of them hold of `⊤ = ⊤` and none of
them says anything about a space it cannot see. Two readings would empty them: that the preimage
might always be the whole space, and that the map might always be one whose value on opens is
already known.

## Main results

- `ComplexAnalytic.pullbackΓ_analytificationMap_polyToGlobal`: **the section attached to `p'`
  pulls back to the section attached to any representative of `ψ` of its class.**
- `ComplexAnalytic.localisationOpen_eq_comap_analytificationMap`: **`D(p)` is the preimage of
  `D(p')`**, the statement above read on opens.
- `ComplexAnalytic.exists_localisationOpen_eq_comap_analytificationMap`: the same with the
  representative produced rather than supplied — **every distinguished open pulls back to one.**
- `ComplexAnalytic.exists_comap_analytificationMap_eq_comap_localisationProj`: **out of a
  localisation, that preimage comes from a distinguished open of the base** — the bullet above
  composed with the previous file's converse, that every distinguished open of a localisation is
  the preimage of one downstairs. `## What it is for` above names that one, in the spelling that
  produces the polynomial rather than the open.

## What is not here

* **Anything about a cover.** `ComplexAnalytic.coverOpen` and the refinement it is for live four
  files further on; the statements below mention a `ComplexAnalytic.PresHom` and a polynomial and
  nothing else.
* **The functor.** `Oka/Analytification/Functor.lean` bundles `ComplexAnalytic.analytificationMap`
  as `ComplexAnalytic.analytificationFunctor`, and a caller holding an isomorphism of
  `ComplexAnalytic.Presentation` reaches these statements through
  `ComplexAnalytic.Presentation` composing with `Functor.map`, which is `analytificationMap` by
  definition. This file imports only the two it names, in the manner of
  `Oka/Analytification/LocalisationFunctor.lean`'s own account of why it is a separate file.
* **Any converse.** Nothing says a preimage of a *general* open is distinguished, and nothing
  says the polynomial the existential produces is unique — it is not, since `D` sees only the
  non-vanishing locus (`ComplexAnalytic.localisationPresentationIsoOfDvdPow` is the statement one
  file over that records this at the level of presentations).
-/

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace ComplexAnalytic

noncomputable section

variable {n n' k k' : ℕ} {g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ}
  {g' : Fin k' → MvPolynomial (ULift.{u} (Fin n')) ℂ}

/-- **The section attached to `p'` pulls back to the section attached to `p`**, whenever `p`
represents the image under `ψ` of the class of `p'`.

`ComplexAnalytic.Γ_map_analytificationMap_comp_quotientToGlobal` at the class of `p'`: the
naturality of `ComplexAnalytic.quotientToGlobal` along the induced morphism, which was proved for
functoriality. The hypothesis is on the classes and not on the polynomials because that is what
the naturality square gives, and `ComplexAnalytic.polyToGlobal` factors through the quotient by
construction. -/
theorem pullbackΓ_analytificationMap_polyToGlobal (ψ : PresHom.{u} g g')
    (p' : MvPolynomial (ULift.{u} (Fin n')) ℂ) (p : MvPolynomial (ULift.{u} (Fin n)) ℂ)
    (h : ψ.toRingHom (Ideal.Quotient.mk (presentationIdeal.{u} g') p') =
      Ideal.Quotient.mk (presentationIdeal.{u} g) p) :
    (analytificationMap.{u} ψ).pullbackΓ (polyToGlobal.{u} g' p') = polyToGlobal.{u} g p :=
  (RingHom.congr_fun (Γ_map_analytificationMap_comp_quotientToGlobal.{u} ψ)
    (Ideal.Quotient.mk (presentationIdeal.{u} g') p')).trans (congrArg (quotientToGlobal.{u} g) h)

/-- **`D(p)` is the preimage of `D(p')` along the induced morphism**, whenever `p` represents the
image under `ψ` of the class of `p'`.

`ComplexAnalytic.pullbackΓ_analytificationMap_polyToGlobal` is the statement for the section and
`ComplexAnalytic.AnalyticSpace.nonvanishing_pullbackΓ` turns it into one about the locus. Neither
step is about the presentation, which is why the two numbers of variables are unrelated here as
they are throughout `Oka/Analytification/ChangeOfVariables.lean`. -/
theorem localisationOpen_eq_comap_analytificationMap (ψ : PresHom.{u} g g')
    (p' : MvPolynomial (ULift.{u} (Fin n')) ℂ) (p : MvPolynomial (ULift.{u} (Fin n)) ℂ)
    (h : ψ.toRingHom (Ideal.Quotient.mk (presentationIdeal.{u} g') p') =
      Ideal.Quotient.mk (presentationIdeal.{u} g) p) :
    localisationOpen.{u} g p =
      (Opens.map (analytificationMap.{u} ψ).toLRSHom.base).obj (localisationOpen.{u} g' p') :=
  (congrArg (AnalyticSpace.analytification.{u} g).nonvanishing
      (pullbackΓ_analytificationMap_polyToGlobal.{u} ψ p' p h)).symm.trans
    (AnalyticSpace.nonvanishing_pullbackΓ.{u} (analytificationMap.{u} ψ)
      (polyToGlobal.{u} g' p'))

/-- **Every distinguished open of the target pulls back to a distinguished open of the source.**

The hypothesis of `ComplexAnalytic.localisationOpen_eq_comap_analytificationMap` can always be
met, because `Ideal.Quotient.mk` is surjective: a class has a representative, and this is that
theorem with the representative produced rather than supplied. It is the form a caller obliged to
hand a *polynomial* to a cover datum needs, and the reason the hypothesis-carrying form is stated
first is that the polynomial such a caller already holds is rarely the one `Classical.choice`
would produce. -/
theorem exists_localisationOpen_eq_comap_analytificationMap (ψ : PresHom.{u} g g')
    (p' : MvPolynomial (ULift.{u} (Fin n')) ℂ) :
    ∃ p : MvPolynomial (ULift.{u} (Fin n)) ℂ,
      localisationOpen.{u} g p =
        (Opens.map (analytificationMap.{u} ψ).toLRSHom.base).obj
          (localisationOpen.{u} g' p') := by
  obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective
    (ψ.toRingHom (Ideal.Quotient.mk (presentationIdeal.{u} g') p'))
  exact ⟨p, localisationOpen_eq_comap_analytificationMap.{u} ψ p' p hp.symm⟩

/-- **Out of a localisation, the preimage of a distinguished open comes from a distinguished open
of the base** — one polynomial, on the member the localisation sits in.

`ComplexAnalytic.exists_localisationOpen_eq_comap_analytificationMap` says the preimage is a
distinguished open of `(A_f)^an`, and `ComplexAnalytic.exists_localisationOpen_eq_comap` says
every distinguished open of `(A_f)^an` is the preimage of one of `X^an`. Two existentials
composed, and the second is the whole content of the previous file.

**This is the arity statement a refinement across members needs**, and it is stated here rather
than in the vocabulary of a cover because nothing in it is about a cover: `ψ` is any `ℂ`-algebra
map out of a presented algebra of the shape `ComplexAnalytic.localisationPresentation` produces,
and `p'` is any polynomial of its target. What a caller does with `Q` — feed it to
`ComplexAnalytic.coverOpen`, having first met it with the polynomial cutting out the overlap it
started from — is not this file's business. -/
theorem exists_comap_analytificationMap_eq_comap_localisationProj
    (g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ) (f : MvPolynomial (ULift.{u} (Fin n)) ℂ)
    (ψ : PresHom.{u} (localisationPresentation.{u} g f) g')
    (p' : MvPolynomial (ULift.{u} (Fin n')) ℂ) :
    ∃ Q : MvPolynomial (ULift.{u} (Fin n)) ℂ,
      (Opens.map (analytificationMap.{u} ψ).toLRSHom.base).obj (localisationOpen.{u} g' p') =
        (Opens.map (localisationProj.{u} g f).toLRSHom.base).obj (localisationOpen.{u} g Q) := by
  obtain ⟨p, hp⟩ := exists_localisationOpen_eq_comap_analytificationMap.{u} ψ p'
  obtain ⟨Q, hQ⟩ := exists_localisationOpen_eq_comap.{u} g f p
  exact ⟨Q, hp.symm.trans hQ⟩

end

end ComplexAnalytic
