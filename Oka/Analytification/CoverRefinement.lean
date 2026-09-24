/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Analytification.CoverIndependence
import Oka.Analytification.LocalisationComposite

/-!
# Refining one member of a cover by distinguished opens

`Oka/Analytification/CoverIndependence.lean` matches two cover data member for member, first at a
shared index type and then along an `Equiv`. In both, the morphism `σ` on indices and the family
`ψ` of member morphisms are **given by the caller**. A *refinement* is the first case where they
are not, and this file is the smallest such case: the refining members are distinguished opens
`D(f_a)` of **one fixed member** `A`.

## What this file measures, and it corrects an estimate the board had been planning against

`Oka/Analytification/CoverIndependence.lean` says of refinement that it *"is where
`ComplexAnalytic.coverMap`'s `σ` and `ψ` stop being given and have to be built"*, with the
implication that building them is the work. **The second half of that is wrong, and this file is
the measurement.** For a distinguished-open refinement `ψ` is `ComplexAnalytic.localisationHom`
and nothing else — one declaration that has been on `master` since taxis #1006, whose direction
convention (*"from the localisation to `A`"*) is already the one `ComplexAnalytic.coverMap` wants.
`σ` is constant. Neither costs a line.

**The work is the refined cover *datum*.** `ComplexAnalytic.coverMap` takes both sides as complete
data, and a refinement supplies only the members. What has to be built is the polynomial cutting
each overlap out, the isomorphism of the two descriptions of it, and the three laws. **This file
builds all of it**, and then the space the refined datum glues to and the morphism from it down to
the fixed member — the first `ComplexAnalytic.coverAnalytification` in this repository that is a
*construction* rather than an instance: it is uniform in `g` and `fam`.

**It is a morphism and not an identification.** `ComplexAnalytic.not_isIso_refineToBase` below
says so, at the smallest data that shows it: a refinement by no opens at all.

## Why one fixed member is the right first case, and it is not a vacuous one

With `σ` constant every overlap is a *same-member* overlap: `D(f_a) ∩ D(f_b)` inside `D(f_a)`. That
is exactly the configuration `Oka/Analytification/LocalisationComposite.lean` was written for —
localising twice is localising once, at the product — so the overlap has a second description as a
single localisation and the glue isomorphism is that description taken at both ends. **Nothing in
the same-member case needs the original cover's own `glue`**, which is what makes it separable
from the cross-member case rather than merely smaller than it.

**It is not vacuous, and the two halves of that claim are different claims.** The construction is
hypothesis-free — the refined data is a cover-datum shape over any index type `K` and any family
of polynomials, so nothing below can be vacuously *satisfied*. That says nothing about whether the
**objects** are degenerate, and they can be: `K` may be empty, and for `fam` constantly `0` every
`D(f_a)` is empty and every law below holds of nothing. They need not be: at an empty base in one
variable with `fam = (z₀, z₀ - 1)` every refined overlap is inhabited and the `(0, 1)` overlap is
a **proper** open of the refined member, so `ComplexAnalytic.refineGlue` there is an isomorphism
of non-empty spaces and the glue is along something smaller than the whole member.

`ComplexAnalytic.refineGlue_comp` below is in any case a statement with content — it is the
`trans_comp` coherence, and it is the reason the glue isomorphism is the *right* one rather than
merely one of the right type.

## The shape of the two proofs

Both laws below go through the single localisation and not through the double one.
`ComplexAnalytic.refineMulIso` is `ComplexAnalytic.localisationPresentationIsoMul` with its source
recognised as `ComplexAnalytic.coverOverlap` of the refined data, which is `rfl`.

**`ComplexAnalytic.refineObj` and `ComplexAnalytic.refinePoly` are `abbrev` and not `def` for
`ComplexAnalytic.refineGlue_comp`, and not for that `rfl`.** The sentence that stood here said
`ComplexAnalytic.refineMulIso`, and that is false: re-declaring the three definitions as `def`s
and rebuilding the chain, the isomorphism elaborates with no complaint, because elaboration
unfolds a `def` at default transparency and the source really does reduce. What needs the
`abbrev` is *rewriting*, which works at `instances` transparency — with `def`s the coherence proof
fails at its **first** `rw`, reporting a pattern it cannot find in a goal that displays as
containing it, with an application type mismatch between
`⟨n + 1, k + 1, localisationPresentation g (fam b)⟩` and the same object spelled through
`refineObj`'s projections.

`ComplexAnalytic.refineGlue_symm` is where the `Iso`s are compared, and `congr 1` is not the way:
it forces the `Category Presentation` instance open on a three-term `Iso.trans` and exhausts the
heartbeat budget, which is the pathology `Oka/Analytification/AffineCover.lean`'s own module
docstring describes at length. Rewriting to a common associated form and finishing with
`ComplexAnalytic.eqToIso_symm'` avoids ever unifying two composites.

`ComplexAnalytic.refineGlue_analytification_comp` meets the *other* recorded pathology:
`rw [← Functor.map_comp]` fails on a goal that displays as if it should apply, because the objects
carry unreduced `ComplexAnalytic.refineObj` projections —
`Oka/CategoryTheory/GlueData.lean`'s module docstring predicts exactly this. The cure here is not
the `mapIso` one `Oka/Analytification/CoverIndependence.lean` records: it is to build the equation
with `congrArg` and simplify the *hypothesis*, which is well-typed by construction, then discharge
the goal with `exact` so that the ascriptions `analytificationFunctor.obj ⟨n, k, g⟩` and
`AnalyticSpace.analytification g` are unified at default transparency. `simpa … using` does **not**
close it, and the difference between the two is the whole of that step.

Both proofs rewrite at a definition — `ComplexAnalytic.refineMul` in one and
`ComplexAnalytic.refineGlue` in the other — so the environment gains an auto-generated equation
lemma for each. Nothing below depends on them, and **the declaration dump is what shows such a
lemma while the build shows nothing**: `comm -13` on `scripts/DumpOkaDecls.lean`'s output.

(This paragraph used to add that a generated `eq_1` makes its own definition a namespace and so
switches off `scripts/check_docstring_names.py`'s field-notation rule. **It does not**: that
script's `GENERATED_COMPONENT` excludes `eq_\d+` from the namespace test and its own self-test
checks assert the exclusion. The hazard was real when taxis #1229 and #1243 recorded it and was
closed before this file was written; the correction is taxis #1301's, and
`Oka/Analytification/CrossMemberGlue.lean` opens its own definitions with `change` for the reason
that survives.)

## The shape of the geometric proofs, which is one sentence used three times

**Every refined member lies over the fixed member and every transition is a morphism over it.**
That is `ComplexAnalytic.refineTransitionHom_localisationProj`, which is
`ComplexAnalytic.refineGlue_analytification_comp` moved from the overlaps' own presentations to
the open subspaces a cover datum is stated at;
`ComplexAnalytic.coverOverlapIso_hom_coverIncl` in `Oka/Analytification/AffineCover.lean` is what
crosses between the two descriptions at each end.

Both laws are then read off it. `hrange` asks where a point goes, and
`ComplexAnalytic.localisationOpen_rename` turns "the image point is in `D(f_bc)`" into "the point
it lies over is in `D(fam c)`", where it already was. `hcocycle` asks for an equality of
morphisms, and the two cancellations that reduce it to nothing are
`AlgebraicGeometry.LocallyRingedSpace.hom_ext_restrict` and the fact that
`ComplexAnalytic.localisationProj` is a monomorphism, being an open immersion.

**Neither proof is an argument about refinements in general**, and the mono is where that shows.
This sentence read *"it is the projection of the one fixed member, and the cross-member case has
three triple overlaps sitting over three different members with no common target to cancel
against"*, and the second half of that is wrong about `hcocycle`: the mono is the projection of
the member the triple's *first* index lies over, which exists whatever `σ` is, and
`ComplexAnalytic.refineDatumCocycle_of_localisationProj`
(`Oka/Analytification/RefineDatumCocycle.lean`) is exactly these two cancellations at a general
`σ`. What is special to a constant `σ` is the step *after* them —
`ComplexAnalytic.refineTriple_localisationProj` reads all three edges of the triple over one
member, and at a general `σ` they lie over three.

## Main definitions

- `ComplexAnalytic.refineObj`: **the refined member**, the distinguished open `D(f_a)` of the fixed
  member, as an object of `ComplexAnalytic.Presentation`.
- `ComplexAnalytic.refinePoly`: **the polynomial cutting the overlap out of the `a`-th refined
  member** — the refining polynomial of the `b`-th, read in one more variable.
- `ComplexAnalytic.refineMul`: the single localisation at the product that both descriptions of the
  overlap reduce to.
- `ComplexAnalytic.refineMulIso` and `ComplexAnalytic.refineGlue`: **the overlap's two descriptions
  identified**, and the glue isomorphism of the refined data built out of it.
- `ComplexAnalytic.refineAnalytification`: **the analytic space the refinement glues to.**
- `ComplexAnalytic.refineToBase`: **the morphism from it down to the fixed member's
  analytification**, glued from the members' own projections.

## Main results

- `ComplexAnalytic.refineGlue_symm`: **the refined glue datum is symmetric**, which is the
  `hsymm` a cover datum asks for. (Named without a citation on purpose: every backticked
  repository name under this heading is read as a result *this* file advertises, and the
  declaration that asks for `hsymm` is another file's.)
- `ComplexAnalytic.refineGlue_comp`: **the coherence triangle** — the glue isomorphism commutes
  with the two structure maps down to the fixed member. This is the content of the file.
- `ComplexAnalytic.refineGlue_analytification_comp`: the same, analytified, which is the form the
  two geometric laws consume.
- `ComplexAnalytic.refineTransitionHom_localisationProj` and
  `ComplexAnalytic.refineTripleIncl_localisationProj`: **the transition is a morphism over the
  fixed member**, on a double overlap and on a triple one. The single sentence both laws below
  are read off.
- `ComplexAnalytic.refineHrange` and `ComplexAnalytic.refineHcocycle`: **the two geometric laws**,
  in the form a cover datum asks for them, with
  `ComplexAnalytic.refineTriple_localisationProj` the intermediate step of the second. The first
  does not use its distinctness hypotheses; the second cannot be stated without them, since the
  triple transition it composes takes them as arguments.
- `ComplexAnalytic.coverIota_comp_refineToBase`: **the morphism restricts to the `a`-th
  projection on the `a`-th member**, which is what says it is the intended one.
- `ComplexAnalytic.isEmpty_refineAnalytification` and
  `ComplexAnalytic.not_isIso_refineToBase`: **a refinement by no opens glues to a space with no
  points, so the morphism is not an isomorphism in general.**

## What is not here

* **No `ComplexAnalytic.coverMap` out of the refinement**, and the missing half is not a proof.
  `coverMap` runs between two cover *data*, and what a refinement maps to is a single
  presentation; the morphism below goes to `A^an` itself, built with
  `ComplexAnalytic.coverGlueMorphisms`. Presenting `A^an` as a one-member cover datum costs
  nothing — the index type is a `Subsingleton`, so both geometric laws are vacuous — but the
  space that datum glues to is a `ComplexAnalytic.coverAnalytification`, and **nothing in this
  repository identifies a one-member gluing with its member**, so a `coverMap` into it would land
  somewhere only known to be `A^an` up to work nobody has done. That identification, not the
  refinement, is what stands between this file and a literal `coverMap`.

  **That diagnosis is right about this file and it does not transfer, which is worth saying here
  because it was read as transferring.** The obstruction is a fact about the *target* being a
  single presentation, not about refinement; a **cross-member** refinement's target is a cover
  datum, so `ComplexAnalytic.refineDatumToBase`
  (`Oka/Analytification/RefineDatumToBase.lean`) is a literal `coverMap` and pays neither step.
  `Oka/Analytification/CoverIndependence.lean` quoted this paragraph's price as a tree-wide
  absence and has been corrected.

  **The two geometric laws are here and the obstruction that kept them out is retired.** They
  needed the refined overlap to be the *preimage* of the refining open along the projection;
  `ComplexAnalytic.localisationOpen_rename` (`Oka/Analytification/DistinguishedOpen.lean`) is
  that statement, it was written after this file and it is what
  `ComplexAnalytic.refineHrange` runs on. **The estimate that it was the whole obstruction was
  right**: nothing else had to be built, and both laws are corollaries of it and of the
  transition being a morphism over the fixed member.
* **No cross-member refinement.** `σ` is constant here, so no overlap of the refined data ever
  meets two different members of the original. The cross-member case has to transport the original
  `glue` through two localisations and it is the only part that uses the original data's own glue
  isomorphism at all; **nothing in this file is evidence about its size** — the whole reason the
  same-member case closes cheaply is that `Oka/Analytification/LocalisationComposite.lean` had
  already been written for exactly this configuration.

  **The transport itself is no longer absent**: `ComplexAnalytic.refineCrossGlue`
  (`Oka/Analytification/CrossMemberGlue.lean`) is the glue of a cross-member overlap, with the
  coherence triangle it satisfies, and `ComplexAnalytic.refineGlue` above is an instance by `rfl`
  of the re-association it is built from. What is still absent is a refined *datum* whose members
  cross, and its `poly` field is no longer part of that: `ComplexAnalytic.refineDatumPoly`
  (`Oka/Analytification/CrossMemberDatum.lean`) is one formula per ordered pair, and
  `ComplexAnalytic.refineDatumPoly_const` says `ComplexAnalytic.refinePoly` above is it at
  constant `σ`. Its `glue` is no longer part of it either on the branch where the two refined
  members lie over one member: `ComplexAnalytic.refineDatumGlueEq`
  (`Oka/Analytification/CrossMemberDatumGlue.lean`) is that branch, the transport between two
  objects of `ComplexAnalytic.Presentation` it needed costs one `subst`, and
  `ComplexAnalytic.refineDatumGlueEq_const` says `ComplexAnalytic.refineGlue` above is it at
  constant `σ` — by `rfl`, up to the two transports of the overlap. **Nor is the field itself**:
  `ComplexAnalytic.refineDatumGlue` is the two branches under a case split, and
  `ComplexAnalytic.refineDatumGlue_const` says `ComplexAnalytic.refineGlue` above is it at
  constant `σ` for every choice — not by `rfl` this time, for the reason that statement gives.
  **Nor is the choice that branch takes**: `ComplexAnalytic.exists_refineDatumCross`
  (`Oka/Analytification/CrossMemberChoice.lean`) produces the extra factor, the polynomial and the
  unit at every ordered pair from the input datum's symmetry law alone — algebraically, saying
  nothing about what the overlap so refined cuts out. **Nor is the symmetry law.** This sentence
  read *"what is left is an `hsymm` quantified over every pair rather than over the equal ones,
  and the two geometric laws"* until `ComplexAnalytic.refineDatumGlue_symm`
  (`Oka/Analytification/RefineDatumSymm.lean`) proved exactly that `hsymm` — at every ordered
  pair, and for two arbitrary independent choices, which is more than the sentence asked for. It
  came free because `ComplexAnalytic.refineDatumCrossProj` is a monomorphism, so the coherence
  triangle `ComplexAnalytic.refineDatumGlueNe_comp` *determines* its isomorphism rather than
  merely constraining it. **Nor do the two geometric laws stand or fall together any longer.**
  This sentence read *"what is left is the two geometric laws and nothing else, and they have no
  analogue for the reason the paragraph above gives"* until
  `ComplexAnalytic.refineDatumTransitionHom_localisationProj_of_ne`
  (`Oka/Analytification/RefineDatumTransition.lean`) gave `hrange` one. What *"every refined
  member lies over the fixed member"* becomes when there is no fixed member is that the refined
  transition lies over the original datum's own `ComplexAnalytic.coverTransitionHom`: a cover
  datum has no morphism between two of its members, so the lower edge of that square is the
  transition rather than a projection, and it is the *point-chase* half of the paragraph above
  that transfers, with the original datum's own `hrange` in place of the fixed member.
  **`hrange` is not proved by it.** At a triple whose three members are pairwise different what
  is left is a single containment, in the caller's own `D(q b c)`, and
  `ComplexAnalytic.range_refineDatumTransitionHom_subset_iff` states it as an *equivalence* and
  not as a sufficient condition, so no weaker hypothesis on the choice can discharge it. **This
  sentence ended "at the mixed triples `ComplexAnalytic.refineDatumGlue` takes its equal branch,
  whose triangle is over a *member*, and the square has no statement there at all", and a
  triangle over a member is the shape this file discharges both laws from at a constant `σ`**:
  `Oka/Analytification/RefineDatumRange.lean` is that statement at a general one, and reads all
  four remaining shapes off it. **This sentence said `hcocycle` "keeps the clause", for the reason
  the paragraph above gives — the cancellation is against the projection of the one fixed member —
  and it also said the law "cannot even be stated first". Both clauses are retired and the reason
  the first gave was the wrong step.** `Oka/Analytification/RefineDatumGlueData.lean` joins the
  five shapes into one proof and states the law off it, as
  `ComplexAnalytic.RefineDatumCocycle`; `ComplexAnalytic.refineDatumHcocycle`
  (`Oka/Analytification/RefineDatumCocycle.lean`) **proves it**, at every triple, from the original
  datum's own three laws and nothing else — the cancellation is against the member the triple's
  *first* index lies over, which is not a fixed one. **What a refined datum still owes is the two
  conditions, and they are not a law**: they are *equivalent* to the assembled `hrange`
  (`ComplexAnalytic.refineDatumHrange_iff`) rather than a discharge of it, so a caller carries the
  range law under another name, and nothing anywhere meets them. Those nine files'
  `## What is not here` state all of it.
* **No hypothesis under which the morphism *is* an isomorphism, and no morphism back.** The
  answer to whether it is one is **no** and it is proved rather than argued:
  `ComplexAnalytic.not_isIso_refineToBase`, at an empty family, where the refinement refines
  nothing and glues to a space with no points. What is *not* here is the positive half — the
  expected condition is that the `D(fam a)` cover `A^an`, and neither that condition nor any
  consequence of it is stated anywhere below. A refinement gives a morphism in one direction;
  both increments in `Oka/Analytification/CoverIndependence.lean` had both directions handed to
  them by the caller, so neither is evidence about the other one here.
* **No scheme, and no `admissible`.** As in the two files this one sits beside, and for the same
  reason: nothing below mentions an `AlgebraicGeometry.Scheme`, and `admissible` is a notion this
  repository does not have. **This bullet said *"there is no `AlgebraicGeometry.Scheme` in this
  line of files"* until 2026-09-02**, and `Oka/Analytification/SpecScheme.lean` now has the one
  there is; it is a separate module precisely so that the file-scoped form of this sentence stays
  true here and in nine other places. **What it does have is everything that notion asserts** —
  `Oka/Analytification/SpecAffineCover.lean`'s admissibility section — including the observation
  that bears directly on this file: a cover datum's pairwise overlaps are *distinguished* opens of
  each of their two members, which is what a refinement general enough for taxis #1107's fourth
  increment would have to reproduce, and what the refinements below produce for one fixed member.
-/

open CategoryTheory TopologicalSpace AlgebraicGeometry

universe u

namespace ComplexAnalytic

noncomputable section

variable {K : Type u} {n k : ℕ} (g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ)
  (fam : K → MvPolynomial (ULift.{u} (Fin n)) ℂ)

/-! ### The refined members and their overlaps -/

/-- **The `a`-th refined member**: the distinguished open `D(fam a)` of the fixed member, presented
by `ComplexAnalytic.localisationPresentation`.

An `abbrev` rather than a `def` on purpose, and what needs it is
`ComplexAnalytic.refineGlue_comp` rather than `ComplexAnalytic.refineMulIso`. That isomorphism
typechecks against `def`s too, since elaboration unfolds a `def` at default transparency; what
needs the reduction of `ComplexAnalytic.coverOverlap` to a double localisation to be available at
`instances` transparency is the *rewriting* in the coherence proof below, which as a `def` fails
at its first `rw` with an application type mismatch against a goal that displays correctly. -/
abbrev refineObj (a : K) : Presentation.{u} :=
  ⟨n + 1, k + 1, localisationPresentation.{u} g (fam a)⟩

/-- **The polynomial cutting the `b`-th overlap out of the `a`-th refined member.**

Inside `D(fam a)` the locus where `fam b` does not vanish is cut out by `fam b` read in the one
extra variable, which is `MvPolynomial.rename` along `ComplexAnalytic.localisationIncl` — the same
renaming `ComplexAnalytic.localisationPresentation` uses on the old equations. -/
abbrev refinePoly (a : K) (b : K) :
    MvPolynomial (ULift.{u} (Fin (refineObj.{u} g fam a).n)) ℂ :=
  MvPolynomial.rename (localisationIncl.{u} n) (fam b)

/-- **The single localisation both descriptions of the overlap reduce to**, at the product of the
two refining polynomials. -/
abbrev refineMul (a b : K) : Presentation.{u} :=
  ⟨n + 1, k + 1, localisationPresentation.{u} g (fam b * fam a)⟩

/-- **The overlap, described twice.**

Localising at `fam a` and then at `fam b` is localising at `fam b * fam a`, which is
`ComplexAnalytic.localisationPresentationIsoMul`. The content of this definition is that its source
*is* `ComplexAnalytic.coverOverlap` of the refined data — by `rfl`, and that is what the `abbrev`s
above buy. -/
def refineMulIso (a b : K) :
    coverOverlap.{u} (refineObj.{u} g fam) (refinePoly.{u} g fam) a b ≅
      refineMul.{u} g fam a b :=
  localisationPresentationIsoMul.{u} g (fam a) (fam b)

/-- **The product is symmetric**, and this is the only place the two orders are compared. -/
theorem refineMul_comm (a b : K) : refineMul.{u} g fam a b = refineMul.{u} g fam b a := by
  rw [refineMul, refineMul, mul_comm]

/-- **The glue isomorphism of the refined data**: each side's description of the overlap, carried
to the single localisation at the product, and the two products identified by `mul_comm`.

This is the `glue` a cover datum asks for, and it is built rather than given — which is the
difference between a refinement and the two increments of
`Oka/Analytification/CoverIndependence.lean`. -/
def refineGlue (a b : K) :
    coverOverlap.{u} (refineObj.{u} g fam) (refinePoly.{u} g fam) a b ≅
      coverOverlap.{u} (refineObj.{u} g fam) (refinePoly.{u} g fam) b a :=
  refineMulIso.{u} g fam a b ≪≫ eqToIso (refineMul_comm.{u} g fam a b) ≪≫
    (refineMulIso.{u} g fam b a).symm

/-! ### The two laws that are algebraic -/

/-- **The inverse of a transport is the transport of the inverse**, for objects of
`ComplexAnalytic.Presentation`.

Mathlib has `CategoryTheory.eqToIso.inv` for the underlying morphism; this is the `Iso`-level
statement, and it exists so that `ComplexAnalytic.refineGlue_symm` can be a chain of rewrites. It
is stated here rather than in general because it is one line either way and nothing else needs
it. -/
theorem eqToIso_symm' {X Y : Presentation.{u}} (h : X = Y) :
    (eqToIso h).symm = eqToIso h.symm :=
  Iso.ext (eqToIso.inv h)

/-- **The refined glue datum is symmetric**, which is `hsymm` for this data.

Everything cancels once both sides are associated the same way: the two `refineMulIso` factors
appear in opposite orders on the two sides and the `eqToIso` is its own opposite by
`ComplexAnalytic.eqToIso_symm'`. **`congr 1` is not available here** — it forces the
`Category Presentation` instance open on a three-term `Iso.trans` and runs the heartbeat budget
out, which is the cost `Oka/Analytification/AffineCover.lean`'s module docstring is about. -/
theorem refineGlue_symm (a b : K) :
    refineGlue.{u} g fam b a = (refineGlue.{u} g fam a b).symm := by
  rw [refineGlue, refineGlue, Iso.trans_symm, Iso.trans_symm, Iso.symm_symm_eq,
    Iso.trans_assoc, eqToIso_symm']

/-- **A transport along an equality of the localising polynomial cancels against the structure
map.**

`subst` is what does it, and it is available because `f` and `f'` are bound here where in
`ComplexAnalytic.refineGlue_comp` they are `fam b * fam a` and `fam a * fam b` and the transport
sits inside `ComplexAnalytic.localisationPresentation`'s argument. This is the same manoeuvre
`Oka/Analytification/CoverIndependence.lean`'s second increment needed and found in Mathlib as
`CategoryTheory.dcongr_arg`; here the family is `ComplexAnalytic.localisationHom` at a varying
polynomial rather than at a varying index, so `dcongr_arg` does not apply and the one-line
`subst` does. -/
theorem eqToHom_localisationHom {f f' : MvPolynomial (ULift.{u} (Fin n)) ℂ} (h : f = f') :
    eqToHom (show (⟨n + 1, k + 1, localisationPresentation.{u} g f⟩ : Presentation.{u}) =
        ⟨n + 1, k + 1, localisationPresentation.{u} g f'⟩ by rw [h]) ≫
      localisationHom.{u} g f' = localisationHom.{u} g f := by
  subst h; simp

/-- **The coherence triangle, and it is the content of this file.**

Going from the `a`-th description of the overlap to the `b`-th and then down to the fixed member
is going down directly. Without it the glue isomorphism would be an isomorphism of the right
*type* with no recorded relation to the two members it is supposed to identify parts of, which is
the same distinction `ComplexAnalytic.localisationPresentationIsoMul_hom_comp` exists to make one
level down — and that lemma, applied twice at the two orders, is the whole proof. -/
theorem refineGlue_comp (a b : K) :
    (refineGlue.{u} g fam a b).hom ≫
        localisationHom.{u} (refineObj.{u} g fam b).g (refinePoly.{u} g fam b a) ≫
          localisationHom.{u} g (fam b) =
      localisationHom.{u} (refineObj.{u} g fam a).g (refinePoly.{u} g fam a b) ≫
        localisationHom.{u} g (fam a) := by
  rw [← localisationPresentationIsoMul_hom_comp.{u} g (fam a) (fam b),
    ← localisationPresentationIsoMul_hom_comp.{u} g (fam b) (fam a), refineGlue]
  simp only [Iso.trans_hom, eqToIso.hom, Category.assoc, Iso.symm_hom]
  rw [show (refineMulIso.{u} g fam b a).inv ≫ (localisationPresentationIsoMul.{u} g (fam b)
      (fam a)).hom ≫ localisationHom.{u} g (fam a * fam b) =
    localisationHom.{u} g (fam a * fam b) from (refineMulIso.{u} g fam b a).inv_hom_id_assoc _]
  exact congrArg _ (eqToHom_localisationHom.{u} g (mul_comm (fam b) (fam a)))

/-- **The coherence triangle, analytified**, with the structure maps read as
`ComplexAnalytic.localisationProj`. This is the form the two geometric laws would consume, and the
reason it is stated here rather than where they are is that it needs nothing geometric.

**`rw [← Functor.map_comp]` does not close this**, on a goal that displays as if it should: the
objects carry unreduced `ComplexAnalytic.refineObj` projections, which is the pathology
`Oka/CategoryTheory/GlueData.lean`'s module docstring predicts. Building the equation with
`congrArg` and simplifying the *hypothesis* avoids it, because the hypothesis is well-typed by
construction. The final step must be `exact` and not `simpa … using`: what is left is the
ascription `analytificationFunctor.obj ⟨n, k, g⟩` against `AnalyticSpace.analytification g`, which
is a definitional unfolding `simp` will not perform and `exact` will. -/
theorem refineGlue_analytification_comp (a b : K) :
    analytificationFunctor.{u}.map (refineGlue.{u} g fam a b).hom ≫
        localisationProj.{u} (refineObj.{u} g fam b).g (refinePoly.{u} g fam b a) ≫
          localisationProj.{u} g (fam b) =
      localisationProj.{u} (refineObj.{u} g fam a).g (refinePoly.{u} g fam a b) ≫
        localisationProj.{u} g (fam a) := by
  have h := congrArg (analytificationFunctor.{u}.map) (refineGlue_comp.{u} g fam a b)
  simp only [Functor.map_comp, analytificationFunctor_map_localisationPresHom] at h
  exact h

/-! ### The two laws that are geometric

Everything above is algebra: an isomorphism of presentations, its symmetry, and two equations
between morphisms. The two remaining fields of a cover datum are about *where points go*, and one
sentence makes both of them cheap here — **every refined member lies over the fixed member, and
every transition is a morphism over it.** `ComplexAnalytic.refineTransitionHom_localisationProj`
is that sentence, `ComplexAnalytic.localisationOpen_rename` is what turns it into a statement
about the refined opens, and the two laws are corollaries of the pair.

**The two laws stand differently to their distinctness hypotheses and the difference is not
cosmetic.** `ComplexAnalytic.refineHrange` does not use them at all — they are named `_hab`,
`_hac`, `_hbc` for that reason, and its containment holds at every triple, repeated indices
included. `ComplexAnalytic.refineHcocycle` **cannot be stated without them**:
`ComplexAnalytic.coverTriple` takes the three proofs as arguments, so they occur in the statement
three times over and there is no such thing as the cocycle law at a repeated index. Its *proof*
uses them for nothing else. Both keep the hypotheses in the shape
`ComplexAnalytic.coverGlueData` asks for, which is what lets a caller pass them with no adapter.
-/

/-- **The transition is a morphism over the fixed member**: going from the `a`-th refined member
to the `b`-th and then down to `A^an` is going down directly.

This is the geometric content of `ComplexAnalytic.refineGlue_analytification_comp`, moved from the
overlaps' own presentations to the open subspaces the cover datum uses.
`ComplexAnalytic.coverOverlapIso_hom_coverIncl` is what crosses between the two descriptions at
each end, and once both ends are crossed the middle is that theorem carried down by
`ComplexAnalytic.AnalyticSpace.forgetToLocallyRingedSpace`.

**The functor has to be applied to the equation rather than the equation rewritten under it.**
`exact congrArg AnalyticSpace.Hom.toLRSHom …` on the goal as stated exhausts the heartbeat budget
in `whnf`; building the mapped equation as a hypothesis, normalising it with
`CategoryTheory.Functor.map_comp` and discharging with `exact` does not. That is the same shape as
`ComplexAnalytic.refineGlue_analytification_comp`'s own proof one level down, and for the same
reason: the hypothesis is well-typed by construction and the goal is what the unifier struggles
with. -/
theorem refineTransitionHom_localisationProj (a b : K) :
    coverTransitionHom.{u} (refineObj.{u} g fam) (refinePoly.{u} g fam)
          (refineGlue.{u} g fam) a b ≫ (localisationProj.{u} g (fam b)).toLRSHom =
      coverIncl.{u} (refineObj.{u} g fam) (refinePoly.{u} g fam) a b ≫
        (localisationProj.{u} g (fam a)).toLRSHom := by
  rw [coverTransitionHom, coverTransition, Iso.trans_hom, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Category.assoc, Category.assoc,
    reassoc_of%
      (coverOverlapIso_hom_coverIncl.{u} (refineObj.{u} g fam) (refinePoly.{u} g fam) b a),
    Iso.inv_comp_eq,
    reassoc_of%
      (coverOverlapIso_hom_coverIncl.{u} (refineObj.{u} g fam) (refinePoly.{u} g fam) a b),
    coverGlueIso, Functor.mapIso_hom, Functor.mapIso_hom]
  have h := congrArg (AnalyticSpace.forgetToLocallyRingedSpace.{u}.map)
    (refineGlue_analytification_comp.{u} g fam a b)
  simp only [Functor.map_comp] at h
  exact h

/-- **The same, restricted to a triple overlap**: the triple overlap of `a`, `b` and `c` maps into
`A^an` the same way whether it is followed into the `b`-th member or included into the `a`-th.

`ComplexAnalytic.refineTransitionHom_localisationProj` and
`AlgebraicGeometry.LocallyRingedSpace.restrictLE_fac`, which says that including a smaller open
subspace into a larger one and then into the ambient space is including it directly. Both laws
below are read off this one.

**The `rw` does not name `ComplexAnalytic.coverTripleIncl`, and that is deliberate.** It is an
`abbrev`, so the rewrite finds `restrictLE` underneath it at `instances` transparency without
being told to unfold it — and `rw [coverTripleIncl]` would plant an auto-generated equation
lemma on **another file's** definition, which is the effect
`Oka/Analytification/CoverComparison.lean` declines by the same manoeuvre and which taxis #1229
and #1243 record biting at a distance. Nothing this file proves generates an equation lemma
outside it. -/
theorem refineTripleIncl_localisationProj (a b c : K) :
    coverTripleIncl.{u} (refineObj.{u} g fam) (refinePoly.{u} g fam) a b c ≫
        coverTransitionHom.{u} (refineObj.{u} g fam) (refinePoly.{u} g fam)
          (refineGlue.{u} g fam) a b ≫ (localisationProj.{u} g (fam b)).toLRSHom =
      (coverSpace.{u} (refineObj.{u} g fam) a).ofRestrict
          (coverOpen.{u} (refineObj.{u} g fam) (refinePoly.{u} g fam) a b ⊓
            coverOpen.{u} (refineObj.{u} g fam) (refinePoly.{u} g fam) a c).isOpenEmbedding ≫
        (localisationProj.{u} g (fam a)).toLRSHom := by
  rw [refineTransitionHom_localisationProj, ← Category.assoc, LocallyRingedSpace.restrictLE_fac]

/-- **`hrange` for a same-member refinement**: the transition carries the part of the `a`-`b`
overlap that also meets `c` into the part of the `b`-th member that meets `c`.

**The proof is one sentence about points and both halves of it are lemmas.**
`ComplexAnalytic.localisationOpen_rename` says that the refined open `D(f_bc)` is the *preimage*
of `D(fam c)` along `ComplexAnalytic.localisationProj`, at both ends; so the assertion is that
the image point lies over `D(fam c)`, and by
`ComplexAnalytic.refineTripleIncl_localisationProj` the point it lies over is the one the
starting point already lay over — which is in `D(fam c)` because the starting point is in the
triple overlap.

**Nothing in it is about `fam b` or about the double localisation.** The refined overlaps are two
descriptions of the same open of `A^an`, and the whole law is that the transition does not move a
point of `A^an`; that is why the cross-member case, where the two members are different spaces
over nothing in common, is not this argument with more indices. -/
theorem refineHrange (a b c : K) (_hab : a ≠ b) (_hac : a ≠ c) (_hbc : b ≠ c) :
    Set.range (coverTripleIncl.{u} (refineObj.{u} g fam) (refinePoly.{u} g fam) a b c ≫
        coverTransitionHom.{u} (refineObj.{u} g fam) (refinePoly.{u} g fam)
          (refineGlue.{u} g fam) a b).base ⊆
      (coverOpen.{u} (refineObj.{u} g fam) (refinePoly.{u} g fam) b c :
        Set (coverSpace.{u} (refineObj.{u} g fam) b)) := by
  rintro _ ⟨x, rfl⟩
  refine (SetLike.ext_iff.1 (localisationOpen_rename.{u} g (fam b) (fam c)) _).2 ?_
  have hx := congrArg (fun m : _ ⟶ _ ↦ (ConcreteCategory.hom m.base) x)
    (refineTripleIncl_localisationProj.{u} g fam a b c)
  simp only [LocallyRingedSpace.comp_base, TopCat.hom_comp, ContinuousMap.comp_apply] at hx
  change (ConcreteCategory.hom (localisationProj.{u} g (fam b)).toLRSHom.base)
    ((ConcreteCategory.hom (coverTripleIncl.{u} (refineObj.{u} g fam) (refinePoly.{u} g fam) a b c ≫
      coverTransitionHom.{u} (refineObj.{u} g fam) (refinePoly.{u} g fam)
        (refineGlue.{u} g fam) a b).base) x) ∈ localisationOpen.{u} g (fam c)
  simp only [LocallyRingedSpace.comp_base, TopCat.hom_comp, ContinuousMap.comp_apply]
  rw [hx]
  exact (SetLike.ext_iff.1 (localisationOpen_rename.{u} g (fam a) (fam c)) _).1 x.2.2

/-- **`ComplexAnalytic.coverTriple` is a morphism over the fixed member**, which is
`ComplexAnalytic.refineTripleIncl_localisationProj` read through
`ComplexAnalytic.coverTriple_fac`.

That lemma says the triple transition followed into the ambient `b`-th member is the double one
precomposed with the inclusion; composing both sides with the projection to `A^an` and rewriting
the right-hand side is the whole proof. This is the form the cocycle law consumes, and it is
where the three transitions of that law each lose their index. -/
theorem refineTriple_localisationProj (a b c : K) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    coverTriple.{u} (refineObj.{u} g fam) (refinePoly.{u} g fam) (refineGlue.{u} g fam)
        (refineHrange.{u} g fam) a b c hab hac hbc ≫
      ((coverSpace.{u} (refineObj.{u} g fam) b).ofRestrict
          (coverOpen.{u} (refineObj.{u} g fam) (refinePoly.{u} g fam) b c ⊓
            coverOpen.{u} (refineObj.{u} g fam) (refinePoly.{u} g fam) b a).isOpenEmbedding ≫
        (localisationProj.{u} g (fam b)).toLRSHom) =
      (coverSpace.{u} (refineObj.{u} g fam) a).ofRestrict
          (coverOpen.{u} (refineObj.{u} g fam) (refinePoly.{u} g fam) a b ⊓
            coverOpen.{u} (refineObj.{u} g fam) (refinePoly.{u} g fam) a c).isOpenEmbedding ≫
        (localisationProj.{u} g (fam a)).toLRSHom := by
  rw [← Category.assoc, coverTriple_fac, Category.assoc, refineTripleIncl_localisationProj]

/-- **`hcocycle` for a same-member refinement**: going round `a`, `b`, `c` on triple overlaps is
the identity.

**Two cancellations and no computation.** A morphism into an open subspace is determined by its
composite with the inclusion (`AlgebraicGeometry.LocallyRingedSpace.hom_ext_restrict`), and a
morphism into the `a`-th refined member is determined by its composite with
`ComplexAnalytic.localisationProj` — because that projection is an open immersion
(`ComplexAnalytic.isOpenImmersion_localisationProj`) and so a monomorphism. After both
cancellations the goal is an equation between two morphisms into `A^an`, and
`ComplexAnalytic.refineTriple_localisationProj` applied three times walks the composite down to
the inclusion it started from.

**This docstring said the two cancellations are "the step that would not survive the cross-member
case unchanged", and they are not**: the mono is the projection of the member the triple's *first*
index lies over, and `ComplexAnalytic.refineDatumCocycle_of_localisationProj`
(`Oka/Analytification/RefineDatumCocycle.lean`) is both of them at a general `σ`. **The step that
does not survive is the third one**, `ComplexAnalytic.refineTriple_localisationProj`: it reads all
three edges over one member, and with `σ` non-constant they lie over three different members with
no common target. What replaces it is a statement per edge rather than one for the triple. -/
theorem refineHcocycle (a b c : K) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    coverTriple.{u} (refineObj.{u} g fam) (refinePoly.{u} g fam) (refineGlue.{u} g fam)
        (refineHrange.{u} g fam) a b c hab hac hbc ≫
      coverTriple.{u} (refineObj.{u} g fam) (refinePoly.{u} g fam) (refineGlue.{u} g fam)
        (refineHrange.{u} g fam) b c a hbc hab.symm hac.symm ≫
      coverTriple.{u} (refineObj.{u} g fam) (refinePoly.{u} g fam) (refineGlue.{u} g fam)
        (refineHrange.{u} g fam) c a b hac.symm hbc.symm hab = 𝟙 _ := by
  haveI := isOpenImmersion_localisationProj.{u} g (fam a)
  refine LocallyRingedSpace.hom_ext_restrict _ _ _ ?_
  rw [← cancel_mono ((localisationProj.{u} g (fam a)).toLRSHom)]
  simp only [Category.assoc, Category.id_comp]
  rw [refineTriple_localisationProj, refineTriple_localisationProj, refineTriple_localisationProj]

/-! ### The refined cover, and the morphism down to the fixed member -/

/-- **The analytic space the refinement glues to.**

`ComplexAnalytic.coverAnalytification` at the refined data, and the first object in this line of
files built from a cover datum nobody handed over: `σ`, `ψ`, the polynomials, the glue and all
three laws are constructed above out of `g` and `fam` alone.

It is a space and not an identification: **nothing here says it is `A^an`**, and
`ComplexAnalytic.not_isIso_refineToBase` below says it is not, in general. -/
def refineAnalytification : AnalyticSpace.{u} :=
  coverAnalytification.{u} (refineObj.{u} g fam) (refinePoly.{u} g fam) (refineGlue.{u} g fam)
    (refineHrange.{u} g fam) (refineGlue_symm.{u} g fam) (refineHcocycle.{u} g fam)

/-- **The morphism down to the fixed member**, glued from the members' own projections.

`ComplexAnalytic.coverGlueMorphisms` at the family `a ↦ localisationProj g (fam a)`, whose
compatibility hypothesis is `ComplexAnalytic.refineTransitionHom_localisationProj` and nothing
else — the hypothesis is *literally* that theorem, once
`ComplexAnalytic.coverTransitionHom` is folded back up out of its definition.

**This is the morphism `ComplexAnalytic.coverMap` would produce and it is not built with it**, for
a reason worth stating: `coverMap` goes between two *cover data*, and the target here is a single
presentation. Presenting `A^an` as a one-member cover is possible — the index type is a
`Subsingleton`, so `hrange` and `hcocycle` are vacuous — but the space it glues to is
`ComplexAnalytic.coverAnalytification` of that datum, and **nothing in this repository identifies
a one-member gluing with its member**, so the resulting morphism would land in a space that is
only known to be `A^an` up to work nobody has done. Gluing the projections lands in `A^an` on the
nose. -/
def refineToBase :
    refineAnalytification.{u} g fam ⟶ AnalyticSpace.analytification.{u} g :=
  coverGlueMorphisms.{u} (refineObj.{u} g fam) (refinePoly.{u} g fam) (refineGlue.{u} g fam)
    (refineHrange.{u} g fam) (refineGlue_symm.{u} g fam) (refineHcocycle.{u} g fam)
    (fun a ↦ localisationProj.{u} g (fam a))
    (fun a b _ ↦ by
      rw [← Category.assoc, ← coverTransitionHom, refineTransitionHom_localisationProj])

/-- **It restricts to the `a`-th projection on the `a`-th member**, which is the statement that
says the morphism is the intended one rather than a well-typed one.

`ComplexAnalytic.coverIota_comp_coverGlueMorphisms`, and by
`ComplexAnalytic.coverAnalytification_hom_ext` it is the only morphism that does. -/
theorem coverIota_comp_refineToBase (a : K) :
    coverIota.{u} (refineObj.{u} g fam) (refinePoly.{u} g fam) (refineGlue.{u} g fam)
        (refineHrange.{u} g fam) (refineGlue_symm.{u} g fam) (refineHcocycle.{u} g fam) a ≫
      refineToBase.{u} g fam = localisationProj.{u} g (fam a) :=
  coverIota_comp_coverGlueMorphisms.{u} _ _ _ _ _ _ _ _ a

/-- **A refinement with no members glues to a space with no points.**

`ComplexAnalytic.coverAnalytificationOpenCover` chooses, for each point of the gluing, an index
whose member contains it; with no indices there are no points. Stated at the analytic space rather
than at the glue datum's gluing because the cover is one of the analytic space **on the nose** —
`ComplexAnalytic.coverAnalytification_toLocallyRingedSpace` is `rfl` — so no transport is
involved.

This is the degeneracy of the construction, and it is what
`ComplexAnalytic.not_isIso_refineToBase` turns into an answer about the morphism. -/
theorem isEmpty_refineAnalytification [IsEmpty K] : IsEmpty (refineAnalytification.{u} g fam) :=
  ⟨fun x ↦ isEmptyElim (α := K) ((coverAnalytificationOpenCover.{u} (refineObj.{u} g fam)
    (refinePoly.{u} g fam) (refineGlue.{u} g fam) (refineHrange.{u} g fam)
    (refineGlue_symm.{u} g fam) (refineHcocycle.{u} g fam)).idx x)⟩

/-- **The morphism is not an isomorphism in general**, and this is the smallest reason: a
refinement by an empty family of distinguished opens refines nothing, and its glued space cannot
be a member with a point in it.

An isomorphism has an inverse, and the inverse applied to a point of `A^an` is a point of a space
that `ComplexAnalytic.isEmpty_refineAnalytification` says has none. The hypothesis is a point of
`A^an` and not an inhabitedness instance, because `A^an` may itself be empty — for `g` containing
a unit it is — and then there is nothing to contradict.

**What would make it an isomorphism is not proved anywhere and this is not a conjecture about
it.** The expected hypothesis is that the `D(fam a)` cover `A^an` — every point of `A^an` lies in
one of them — which is exactly what fails above and is a condition on `fam` that nothing in this
file states, let alone consumes. The honest reading of this theorem is that a *refinement is not
an identification*: it produces a morphism in one direction, and the two increments in
`Oka/Analytification/CoverIndependence.lean` produce isomorphisms only because their callers hand
over both directions. -/
theorem not_isIso_refineToBase [IsEmpty K] (y : AnalyticSpace.analytification.{u} g) :
    ¬ IsIso (refineToBase.{u} g fam) := by
  intro h
  exact (isEmpty_refineAnalytification.{u} g fam).elim
    ((inv (refineToBase.{u} g fam)).toLRSHom.base y)

end

end ComplexAnalytic
