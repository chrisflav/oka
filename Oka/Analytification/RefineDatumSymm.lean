/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Analytification.CrossMemberChoice

/-!
# The structure map of a localisation is a monomorphism, and the refined datum's `hsymm` follows

`Oka/Analytification/CrossMemberDatumGlue.lean` builds the `glue` field of a refined cover datum
at a general `σ`, and hands the caller a choice at every ordered pair whose two members differ.
Both that file and `Oka/Analytification/CrossMemberChoice.lean` recorded, until this one landed
and the same push corrected them, that the symmetry law was blocked on those choices:

> A cover datum's symmetry law is quantified over every ordered pair. … on the other half the
> pair `(a, b)` and the pair `(b, a)` carry two *independent* choices of `r` and `u`, and whether
> they can be made compatibly is unproved in both directions.

> A refined `hsymm` would need one choice per *unordered* pair, read at both orders; whether both
> obligations can be met by one such choice is unmeasured here in both directions.

**Neither is what a refined `hsymm` needs, and the second question does not have to be answered.**
The symmetry law holds for two arbitrary independent choices, and so does more: the isomorphism
the cross-member branch produces **does not depend on the choice at all**. What buys both is one
statement about localisations that this repository did not have.

## The one statement, and its own supplier asked for it

`ComplexAnalytic.localisationPresentedAlgebraEquiv_localisationRingHom` says the identification of
a localised presented algebra with a `Localization.Away` is *over the member*. Its docstring in
`Oka/Analytification/LocalisationIndependence.lean` says what it is for, in terms — that it lets a
consumer use the universal property of the localisation on anything built from
`ComplexAnalytic.localisationRingHom`, *"for instance to see that two descriptions of the same
distinguished open agree over the member they sit in"*.

**Nobody had used it that way.** Both counts below are with `git grep -c` **on the commit this
file was cut from**, so they describe the tree without this file and are not claims about the
tree with it. It was named in three files — its own,
`Oka/Analytification/LocalisationComposite.lean` and
`Oka/Analytification/SpecDistinguishedOpen.lean` — and in none of them to conclude that two maps
out of a localisation agree: the first two used it as a rewrite and under
`congrArg Submonoid.powers`, the third through `CommRingCat.hom_ext (RingHom.ext …)`, which
compares two ring maps pointwise and is the opposite of an appeal to the universal property. The
independent count said the same: all seven call sites of `IsLocalization.ringHom_ext` were at an
`Ideal.primeCompl`, so the universal property was used at stalks and never at a distinguished
open. The first result below is the eighth call site and the first that is not.

`ComplexAnalytic.ringHom_ext_localisationRingHom` uses it at `Submonoid.powers`, and
`ComplexAnalytic.mono_localisationHom` is the three-line consequence: **the structure map
`A ⟶ A_f` is a monomorphism of presentations.** Everything else here is that instance applied.

## Why a monomorphism is the right shape, and not merely a convenient one

Every isomorphism built in this corner of the tree arrives with a coherence triangle saying it
sits over something — `ComplexAnalytic.refineCrossGlue_hom_comp`,
`ComplexAnalytic.refineDatumGlueNe_comp` and
`ComplexAnalytic.localisationPresentationIsoOfUnitMul_hom_comp` among them. Read with the
structure map merely a morphism, such a triangle **constrains** the isomorphism. Read with it a
monomorphism, the triangle **determines** it, and the three questions this file answers are the
same question:

* two callers' choices at one ordered pair give the same isomorphism, because both satisfy the
  same triangle (`ComplexAnalytic.refineDatumGlueNe_congr`);
* an isomorphism satisfying the triangle *is* the constructed one
  (`ComplexAnalytic.refineDatumGlueNe_unique`);
* the isomorphism at `(b, a)` is the inverse of the one at `(a, b)`, because the inverse satisfies
  the triangle at `(b, a)` (`ComplexAnalytic.refineDatumGlueNe_symm`).

The technique is not new here — `Oka/Analytification/CoverRefinement.lean` runs
`rw [← cancel_mono …]` at a `ComplexAnalytic.localisationProj` — but that is a monomorphism of
*analytic spaces*, obtained because an open immersion is one, and it lives a functor away.
Nothing said the presentation-level structure map is one.

## What the input's own symmetry does, and it is one step

`ComplexAnalytic.refineDatumGlueNe_symm` reads the original cover datum's `hsymm` exactly once, to
turn `(glue (σ b) (σ a)).hom` into `(glue (σ a) (σ b)).inv`. That is the same single use
`ComplexAnalytic.refineDatumCrossAlgEquiv_symm` makes of it one file over, and it is the whole of
what relates the two orders of a pair — the choices contribute nothing, which is the point.

## Main results

- `ComplexAnalytic.ringHom_ext_localisationRingHom`: **two ring maps out of a localised presented
  algebra that agree after the structure map are equal** — the universal property of the
  localisation, at a distinguished open rather than at a stalk.
- `ComplexAnalytic.mono_localisationHom`: **the structure map `A ⟶ A_f` is a monomorphism** of
  presentations.
- `ComplexAnalytic.mono_refineCrossProj` and `ComplexAnalytic.mono_refineDatumCrossProj`: **so is
  the projection of a cross-member refined overlap to the original overlap**, in both spellings,
  since each is an isomorphism followed by a structure map.
- `ComplexAnalytic.refineDatumGlueNe_unique`: **an isomorphism of the two refined overlaps
  satisfying the cross-member coherence triangle is the constructed one.**
- `ComplexAnalytic.refineDatumGlueNe_congr`: **the cross-member glue does not depend on the
  caller's choice** — two choices at the same ordered pair give the same isomorphism.
- `ComplexAnalytic.refineDatumGlueNe_symm`: **the symmetry law on the branch where the two members
  differ**, for two arbitrary independent choices, given the input datum's own symmetry.
- `ComplexAnalytic.refineDatumGlue_symm`: **the symmetry law of the refined cover datum**, at every
  ordered pair — the first of the three laws a cover datum has to satisfy to be discharged for a
  refinement whose `σ` is not constant.

## What is not here

* **No `hrange` and no `hcocycle` here.** They are the other two laws, they are geometric where
  everything here is algebraic, and nothing below is evidence about either. What is proved here
  is that one law is free; that says nothing about the two that are not. Both are proved
  elsewhere on this line — `ComplexAnalytic.refineDatumHrange` and
  `ComplexAnalytic.refineDatumHcocycle`. **This bullet said that the second of them *"consumes
  this file's theorem"*, and it does not**: `ComplexAnalytic.refineDatumGlue_symm` is named
  nowhere in `Oka/Analytification/RefineDatumCocycle.lean`. What the shapes with two of the three
  members equal cancel against is the original datum's own `hsymm` **hypothesis**, carried through
  `ComplexAnalytic.coverTransition_hom_comp` — the same hypothesis this file's theorem takes, and
  spent one level below it rather than through it. The theorem's only term-level consumers
  anywhere are `ComplexAnalytic.refineDatumGlueData` and
  `ComplexAnalytic.refineDatumAnalytification`
  (`Oka/Analytification/RefineDatumGlueData.lean`), where a symmetry law and a cocycle law are
  supplied to the same construction, and they were its only consumers before
  `Oka/Analytification/RefineDatumCocycle.lean` existed too.
* **Nothing about whether the refined overlap is the geometric one.**
  `Oka/Analytification/CrossMemberChoice.lean` records that the extra factor it produces obeys an
  algebraic rule and that nothing says the overlap the rule induces is the one the geometry names.
  **This file does not narrow that**, and `ComplexAnalytic.refineDatumGlueNe_congr` must not be
  read as though it did: the glue is independent of the choice, which is a different sentence from
  the glue being the right one. Independence of an arbitrary choice is exactly as strong when the
  construction is wrong.
* **No change to `ComplexAnalytic.refineDatumGlue`'s signature.** It still takes `r`, `u` and the
  two equations, and `ComplexAnalytic.refineDatumGlueNe_congr` says the result ignores the first
  two. Removing them would need the existence to be threaded through instead, which is a decision
  with consumers and belongs where the datum is assembled.
* **No witness at a non-constant `σ` *here***. This bullet said only *"no witness at a
  non-constant `σ`"*, and there is one — `Oka/Analytification/RefineDatumWitness.lean` exhibits a
  refined cover datum at an arbitrary index map, for every cover datum, by taking the refining
  family constantly `1`. It reads this file's theorem, through
  `ComplexAnalytic.refineDatumGlueData`, and nothing here is evidence for it. Nothing about
  `AlgebraicGeometry.Scheme` or `admissible` either, as in the four files this one sits beside.
* **The first two results are general and this is not their natural home.**
  `ComplexAnalytic.ringHom_ext_localisationRingHom` and `ComplexAnalytic.mono_localisationHom`
  mention nothing about covers, refinements or `σ`, and belong beside the equivalence they are
  proved from, in `Oka/Analytification/LocalisationIndependence.lean`. They are here because they
  arrive with their first consumer, and a second consumer earlier in the import order is what
  would decide the move; until there is one they stay here. **What is not a reason is the price,
  and this bullet used to give one**: it read *"moving them is an import change nothing needs"*,
  and the move is **no import change at all**, in either direction. Measured rather than read off
  the graph — both go through verbatim in a file whose only import is
  `Oka/Analytification/LocalisationIndependence.lean`, and this file would still name them after
  the move, because it already reaches that one transitively through
  `Oka/Analytification/CrossMemberChoice.lean`. So the question left is editorial and costs
  nothing either way.
-/

open CategoryTheory MvPolynomial

universe u

namespace ComplexAnalytic

noncomputable section

/-! ### The universal property of a localisation, at a distinguished open -/

variable {n k : ℕ} (g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ)
  (f : MvPolynomial (ULift.{u} (Fin n)) ℂ)

/-- **Two ring maps out of `A_f` that agree on `A` are equal.**

The universal property of the localisation, in the spelling this development's presented algebras
are in. `ComplexAnalytic.localisationPresentedAlgebraEquiv` identifies
`ComplexAnalytic.PresentedAlgebra` of a `ComplexAnalytic.localisationPresentation` with a
`Localization.Away`, where `IsLocalization.ringHom_ext` applies at
`Submonoid.powers (Ideal.Quotient.mk (presentationIdeal g) f)`, and
`ComplexAnalytic.localisationPresentedAlgebraEquiv_localisationRingHom` is what turns the
hypothesis stated here into the hypothesis that lemma wants.

**Through the equivalence and not through an `Algebra` instance**, which is the constraint
`Oka/Analytification/DistinguishedOpen.lean` records: an
`Algebra (ComplexAnalytic.PresentedAlgebra n k g)` instance on the localised presented algebra
would be keyed on a type this development uses everywhere, and the equivalence reaches the same
universal property without one. -/
theorem ringHom_ext_localisationRingHom {R : Type u} [CommRing R]
    (φ χ : PresentedAlgebra.{u} (n + 1) (k + 1) (localisationPresentation.{u} g f) →+* R)
    (h : φ.comp (localisationRingHom.{u} g f) = χ.comp (localisationRingHom.{u} g f)) :
    φ = χ := by
  set e := localisationPresentedAlgebraEquiv.{u} g f with he
  have key : φ.comp e.symm.toAlgHom.toRingHom = χ.comp e.symm.toAlgHom.toRingHom := by
    refine IsLocalization.ringHom_ext
      (Submonoid.powers (Ideal.Quotient.mk (presentationIdeal.{u} g) f)) (RingHom.ext fun x ↦ ?_)
    have hx : e.symm.toAlgHom.toRingHom
        (algebraMap (PresentedAlgebra.{u} n k g)
          (Localization.Away (Ideal.Quotient.mk (presentationIdeal.{u} g) f)) x) =
        localisationRingHom.{u} g f x := by
      change e.symm _ = _
      rw [AlgEquiv.symm_apply_eq, he, localisationPresentedAlgebraEquiv_localisationRingHom]
    simp only [RingHom.comp_apply, hx]
    exact congrArg (fun ψ ↦ ψ x) h
  refine RingHom.ext fun y ↦ ?_
  have := congrArg (fun ψ : _ →+* R ↦ ψ (e y)) key
  simpa using this

/-- **The structure map `A ⟶ A_f` is a monomorphism of presentations.**

The statement above read in the category, through `ComplexAnalytic.PresHom.ext`: a morphism of
presentations is its ring map and nothing else, and composition in `ComplexAnalytic.Presentation`
is composition of ring maps the other way round, so cancelling `ComplexAnalytic.localisationHom`
on the left of a composite is exactly cancelling `ComplexAnalytic.localisationRingHom` on the
right of a ring map.

**An `instance`, because everything below reaches it by `infer_instance` through
`CategoryTheory.mono_comp`.** -/
instance mono_localisationHom : Mono (localisationHom.{u} g f) :=
  ⟨fun {_} _ _ h ↦ PresHom.ext
    (ringHom_ext_localisationRingHom.{u} g f _ _ (congrArg PresHom.toRingHom h))⟩

/-- **The projection of a cross-member refined overlap to the original overlap is a
monomorphism.**

`ComplexAnalytic.refineCrossProj` is a re-association isomorphism followed by a structure map, so
this is `CategoryTheory.mono_comp` on an isomorphism and the instance above.

The `change` is not decoration: `refineCrossProj` is a `def` with no unfolding lemma, so the
composite has to be exhibited before instance synthesis can see two factors. -/
instance mono_refineCrossProj (x q : MvPolynomial (ULift.{u} (Fin n)) ℂ) :
    Mono (refineCrossProj.{u} g f x q) := by
  change Mono ((localisationPresentationIsoOfMulEq.{u} g x (f * q) f (q * x) (by ring)).hom ≫ _)
  infer_instance

/-! ### The cross-member glue is determined by its triangle -/

variable {J B : Type u} (obj : J → Presentation.{u})
  (σ : B → J) (fam : ∀ b : B, MvPolynomial (ULift.{u} (Fin (obj (σ b)).n)) ℂ)
  (poly : ∀ i : J, J → MvPolynomial (ULift.{u} (Fin (obj i).n)) ℂ)
  (q : ∀ a : B, B → MvPolynomial (ULift.{u} (Fin (obj (σ a)).n)) ℂ)
  (glue : ∀ i j : J, coverOverlap.{u} obj poly i j ≅ coverOverlap.{u} obj poly j i)

/-- **The same at the datum**, where the projection carries the transport that turns the datum's
own `poly` field into the polynomial the refined overlap is stated at.

`ComplexAnalytic.refineDatumCrossProj_eq` exhibits it as `CategoryTheory.eqToIso` composed with
`ComplexAnalytic.refineCrossProj`, and both factors are monomorphisms. -/
instance mono_refineDatumCrossProj {a b : B} (h : σ a ≠ σ b) :
    Mono (refineDatumCrossProj.{u} obj σ fam poly q h) := by
  rw [refineDatumCrossProj_eq]
  infer_instance

/-- **An isomorphism of the two refined overlaps satisfying the cross-member coherence triangle is
the constructed one.**

`ComplexAnalytic.refineDatumGlueNe_comp` says the constructed isomorphism satisfies the triangle;
with `ComplexAnalytic.refineDatumCrossProj` a monomorphism, the triangle has at most one solution,
so it says more than it appeared to. Everything else in this section is this lemma applied.

The hypothesis is the triangle at the *given* choice, and the conclusion names the constructed
isomorphism at *that* choice — the two `r`s and the two `u`s are the same. What happens when they
differ is the next result. -/
theorem refineDatumGlueNe_unique {a b : B} (h : σ a ≠ σ b)
    (r : MvPolynomial (ULift.{u} (Fin ((obj (σ b)).n + 1))) ℂ)
    (he : RefineDatumCrossEq.{u} obj σ fam poly q glue a b r)
    (u : (PresentedAlgebra.{u} ((obj (σ b)).n + 1) ((obj (σ b)).k + 1)
      (localisationPresentation.{u} (obj (σ b)).g (poly (σ b) (σ a))))ˣ)
    (hu : RefineDatumCrossUnit.{u} obj σ fam poly q a b r u)
    (G : coverOverlap.{u} (refineDatumObj.{u} obj σ fam)
        (refineDatumPoly.{u} obj poly σ fam q) a b ≅
      coverOverlap.{u} (refineDatumObj.{u} obj σ fam) (refineDatumPoly.{u} obj poly σ fam q) b a)
    (hG : G.hom ≫ refineDatumCrossProj.{u} obj σ fam poly q h.symm =
      refineDatumCrossProj.{u} obj σ fam poly q h ≫ (glue (σ a) (σ b)).hom) :
    G = refineDatumGlueNe.{u} obj σ fam poly q glue h r he u hu :=
  Iso.ext ((cancel_mono (refineDatumCrossProj.{u} obj σ fam poly q h.symm)).1
    (hG.trans (refineDatumGlueNe_comp.{u} obj σ fam poly q glue h r he u hu).symm))

/-- **The cross-member glue does not depend on the caller's choice.**

Two choices at the same ordered pair — two polynomials `r`, two units `u`, and the two equations
each — give the **same** isomorphism, because both satisfy the same coherence triangle and the
triangle has at most one solution.

**This is about the glue and not about the choice.** `Oka/Analytification/CrossMemberChoice.lean`
produces a choice by three `choose`s and a different run gives a different one; that is unchanged
and true. What is now also true is that the isomorphism built from it is the same either way, so a
consumer needing the *same* glue twice need not carry the choice that produced it.

**It says nothing about the glue being the right one.** The identification of the refined overlap
with the geometric one is still not made anywhere, and an isomorphism can be independent of an
arbitrary choice and still not be the map the geometry names. -/
theorem refineDatumGlueNe_congr {a b : B} (h : σ a ≠ σ b)
    (r₁ : MvPolynomial (ULift.{u} (Fin ((obj (σ b)).n + 1))) ℂ)
    (he₁ : RefineDatumCrossEq.{u} obj σ fam poly q glue a b r₁)
    (u₁ : (PresentedAlgebra.{u} ((obj (σ b)).n + 1) ((obj (σ b)).k + 1)
      (localisationPresentation.{u} (obj (σ b)).g (poly (σ b) (σ a))))ˣ)
    (hu₁ : RefineDatumCrossUnit.{u} obj σ fam poly q a b r₁ u₁)
    (r₂ : MvPolynomial (ULift.{u} (Fin ((obj (σ b)).n + 1))) ℂ)
    (he₂ : RefineDatumCrossEq.{u} obj σ fam poly q glue a b r₂)
    (u₂ : (PresentedAlgebra.{u} ((obj (σ b)).n + 1) ((obj (σ b)).k + 1)
      (localisationPresentation.{u} (obj (σ b)).g (poly (σ b) (σ a))))ˣ)
    (hu₂ : RefineDatumCrossUnit.{u} obj σ fam poly q a b r₂ u₂) :
    refineDatumGlueNe.{u} obj σ fam poly q glue h r₁ he₁ u₁ hu₁ =
      refineDatumGlueNe.{u} obj σ fam poly q glue h r₂ he₂ u₂ hu₂ :=
  refineDatumGlueNe_unique.{u} obj σ fam poly q glue h r₂ he₂ u₂ hu₂ _
    (refineDatumGlueNe_comp.{u} obj σ fam poly q glue h r₁ he₁ u₁ hu₁)

/-! ### The symmetry law -/

/-- **The symmetry law on the branch where the two members differ**, for two arbitrary independent
choices and given the original cover datum's own symmetry.

The choice at `(a, b)` and the choice at `(b, a)` are unrelated — different polynomials in
different rings, obtained from two unrelated runs of the existence — and **nothing here asks them
to be compatible.** The inverse of the isomorphism at `(a, b)` satisfies the coherence triangle at
`(b, a)`, so it is the isomorphism at `(b, a)`, whatever either choice was.

**The input's `hsymm` is used exactly once**, to read `(glue (σ b) (σ a)).hom` as
`(glue (σ a) (σ b)).inv`; that is the same single use
`ComplexAnalytic.refineDatumCrossAlgEquiv_symm` makes of it, and it is the only thing that
relates the two orders of a pair.

**Why the triangle at `(b, a)` is fed to `refine` and not to `rw`, and it is measured.** That
triangle mentions `refineDatumCrossProj … h.symm.symm` where the goal has
`refineDatumCrossProj … h`. The two are equal by proof irrelevance and are not syntactically
equal, so `rw` cannot find the pattern, and it does not fail quickly: it **times out at `whnf`
after 200000 heartbeats**, which is `maxHeartbeats` and not `synthInstance.maxHeartbeats`.
Supplying the triangle as `t.trans ?_` closes it at once, because `refine` checks up to defeq.
This is one of two shapes in which `rw` refuses a rewrite an equality plainly licenses, and they
have different causes and the same escape: in the other the goal is not type-correct once the
pattern is abstracted, and **in this one the pattern differs by a proof term.** Neither is fixed
by restating the pattern; both are fixed by supplying the equality as a term. -/
theorem refineDatumGlueNe_symm (hsym : ∀ i j : J, glue j i = (glue i j).symm)
    {a b : B} (h : σ a ≠ σ b)
    (r₁ : MvPolynomial (ULift.{u} (Fin ((obj (σ b)).n + 1))) ℂ)
    (he₁ : RefineDatumCrossEq.{u} obj σ fam poly q glue a b r₁)
    (u₁ : (PresentedAlgebra.{u} ((obj (σ b)).n + 1) ((obj (σ b)).k + 1)
      (localisationPresentation.{u} (obj (σ b)).g (poly (σ b) (σ a))))ˣ)
    (hu₁ : RefineDatumCrossUnit.{u} obj σ fam poly q a b r₁ u₁)
    (r₂ : MvPolynomial (ULift.{u} (Fin ((obj (σ a)).n + 1))) ℂ)
    (he₂ : RefineDatumCrossEq.{u} obj σ fam poly q glue b a r₂)
    (u₂ : (PresentedAlgebra.{u} ((obj (σ a)).n + 1) ((obj (σ a)).k + 1)
      (localisationPresentation.{u} (obj (σ a)).g (poly (σ a) (σ b))))ˣ)
    (hu₂ : RefineDatumCrossUnit.{u} obj σ fam poly q b a r₂ u₂) :
    refineDatumGlueNe.{u} obj σ fam poly q glue h.symm r₂ he₂ u₂ hu₂ =
      (refineDatumGlueNe.{u} obj σ fam poly q glue h r₁ he₁ u₁ hu₁).symm := by
  have t₁ := refineDatumGlueNe_comp.{u} obj σ fam poly q glue h r₁ he₁ u₁ hu₁
  have t₂ := refineDatumGlueNe_comp.{u} obj σ fam poly q glue h.symm r₂ he₂ u₂ hu₂
  refine Iso.ext ?_
  rw [Iso.symm_hom]
  refine (cancel_mono (refineDatumCrossProj.{u} obj σ fam poly q h)).1 (t₂.trans ?_)
  rw [hsym (σ a) (σ b), Iso.symm_hom, Iso.comp_inv_eq, Category.assoc, ← t₁,
    Iso.inv_hom_id_assoc]

variable (r : ∀ _ b : B, MvPolynomial (ULift.{u} (Fin ((obj (σ b)).n + 1))) ℂ)
  (u : ∀ a b : B, (PresentedAlgebra.{u} ((obj (σ b)).n + 1) ((obj (σ b)).k + 1)
    (localisationPresentation.{u} (obj (σ b)).g (poly (σ b) (σ a))))ˣ)

/-- **The symmetry law of the refined cover datum**, at every ordered pair, for any families of
choices and given the original datum's own symmetry.

The `dite`'s two branches, each with its own law: `ComplexAnalytic.refineDatumGlueEq_symm` where
the two refined members lie over one member, and
`ComplexAnalytic.refineDatumGlueNe_symm` where they do not.

**This is the first of the three laws a cover datum has to satisfy discharged for a refinement
whose `σ` is not constant.** The other two are `hrange` and `hcocycle`; they are geometric, they
are untouched *here*, and that one law came free is not evidence about them. Both have since been
proved — `ComplexAnalytic.refineDatumHrange` and `ComplexAnalytic.refineDatumHcocycle`. **This
docstring said the second was *"a consumer of this theorem rather than a repetition of it"*, and
it is neither**: it does not name this theorem, and what its mixed shapes cancel against is the
`hsym` hypothesis below, spent directly through
`ComplexAnalytic.coverTransition_hom_comp`. `ComplexAnalytic.refineDatumGlueData` is where the two
laws meet. -/
theorem refineDatumGlue_symm (hsym : ∀ i j : J, glue j i = (glue i j).symm)
    (he : ∀ a b : B, ∀ _ : σ a ≠ σ b,
      RefineDatumCrossEq.{u} obj σ fam poly q glue a b (r a b))
    (hu : ∀ a b : B, ∀ _ : σ a ≠ σ b,
      RefineDatumCrossUnit.{u} obj σ fam poly q a b (r a b) (u a b)) (a b : B) :
    refineDatumGlue.{u} obj σ fam poly q glue r u he hu b a =
      (refineDatumGlue.{u} obj σ fam poly q glue r u he hu a b).symm := by
  by_cases h : σ a = σ b
  · rw [refineDatumGlue_of_eq.{u} obj σ fam poly q glue r u he hu h.symm,
      refineDatumGlue_of_eq.{u} obj σ fam poly q glue r u he hu h, refineDatumGlueEq_symm]
  · rw [refineDatumGlue_of_ne.{u} obj σ fam poly q glue r u he hu (Ne.symm h),
      refineDatumGlue_of_ne.{u} obj σ fam poly q glue r u he hu h]
    exact refineDatumGlueNe_symm.{u} obj σ fam poly q glue hsym h _ _ _ _ _ _ _ _

end

end ComplexAnalytic
