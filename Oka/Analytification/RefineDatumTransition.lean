/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Analytification.CrossMemberDatumGlue

/-!
# The cross-member refined transition lies over the original cover's own transition

`Oka/Analytification/CoverRefinement.lean` discharges both geometric laws of a refined cover datum
with one sentence — **every refined member lies over the fixed member, and every transition is a
morphism over it**, which is `ComplexAnalytic.refineTransitionHom_localisationProj`. At a
non-constant `σ` there is no fixed member, and that file said so: the cross-member case has
"three triple overlaps sitting over three different members with no common target to cancel
against". That sentence is retired there — it was said of both laws, and it is true of neither.

**There is an analogue anyway, and what changes is what the transition is said to lie over.** A
cover datum carries no morphism between two of its members, so nothing can be stated over one. It
does carry a transition between the two descriptions of their *overlap*, and the cross-member
refined transition lies over exactly that:
`ComplexAnalytic.refineDatumTransitionHom_localisationProj_of_ne` below is the square whose lower
edge is `ComplexAnalytic.coverTransitionHom` of the original datum, at `σ a` and `σ b`.

## What it is assembled from, and both parts were waiting unread

The square is the two triangles `Oka/Analytification/CrossMemberDatumGlue.lean` ends with, joined:
`ComplexAnalytic.refineDatumGlueNe_analytification_comp` — the unequal branch's coherence triangle
over the original overlap — and
`ComplexAnalytic.refineDatumCrossProj_analytification_localisationProj`, which that file describes
as "what a consumer composes with to push the `a`-side projection down to its member".

**At `46525e6` neither had a consumer.** `git grep` at that commit finds each of them under `Oka/`
only in the file that proves it. This file is
the first consumer of both, and it uses the second at `(b, a)` as well as at `(a, b)` — the
`b`-side instance is what turns the triangle's left-hand side into the two structure maps a
transition is stated with.

## What this makes of `hrange`, and the residue is one open

`hrange` for the refined datum asks that the transition carry the part of the `a`-`b` overlap that
also meets `c` into the part of the `b`-th refined member that meets `c`. Where all three of
`σ a`, `σ b`, `σ c` are different, `ComplexAnalytic.coverOpen_refineDatumPoly_of_ne` splits the
target in two: the refined open `D(f_bc)` is the preimage along
`ComplexAnalytic.localisationProj` of `D(f_{σb σc}) ⊓ D(q b c)`, the first factor belonging to the
original datum and the second being the caller's extra factor and nothing else.

**The first half is free given the original datum's own `hrange`, and the second is the whole of
what is left.** `ComplexAnalytic.range_refineDatumTransitionHom_localisationProj_subset` is the
first half, proved by lifting the refined triple overlap to the original one
(`ComplexAnalytic.refineDatumCrossTriple`) and reading the original law there;
`ComplexAnalytic.range_refineDatumTransitionHom_subset_iff` is the statement that nothing else
remains — the refined law at such a triple is *equivalent* to the image landing in the preimage of
`D(q b c)`. That is a sharper form of the absence
`Oka/Analytification/CrossMemberGlue.lean` records as "nothing here produces `q`": it is not that
`q` is unconstrained in general, it is that this one containment is the only thing `hrange` asks
of it at a fully cross triple.

**Nothing here is evidence about `q`, in either direction.**
`ComplexAnalytic.exists_refineDatumCross` produces a choice algebraically and says nothing about
what the overlap so refined cuts out; the
equivalence above is what a geometric hypothesis on `q` would have to discharge, not a step
towards one.

## The `rw` discipline, and both recorded forms of it fired here

`Oka/Analytification/CrossMemberGlue.lean` states the rule — open a definition with a `rfl`
theorem or a `change`, not with `rw` — and `Oka/Analytification/CrossMemberDatumGlue.lean` adds
the variant where the planted lemma belongs to another file and is planted by `simp only` rather
than by `rw`. **Both fired on the first draft of this file, and the declaration dump is what saw
them**: that draft declared **twelve** things and `Δdump` was **+16**. The build was green
throughout.

* `rw [refineDatumCrossPart]` and `rw [refineDatumCrossTriple]` planted
  `ComplexAnalytic.refineDatumCrossPart.eq_1` and `ComplexAnalytic.refineDatumCrossTriple.eq_1`.
  The cure is the two `rfl` theorems above, which is the cure
  `Oka/Analytification/CrossMemberDatumGlue.lean` records and applies to its own two definitions.
* `simp only [Category.assoc]` on a goal mentioning `ComplexAnalytic.refineDatumCrossProjSpace`
  planted its congruence lemma, that definition taking a proof argument. The cure is a `rw` at
  `CategoryTheory.Category.assoc` — the association it had to fix was on one side only, so the
  ambiguity that makes `simp only` the easy choice was not there.
* **The other-file variant, and it was planted by the composition lemmas and not by a definition
  unfold.** `simp only [LocallyRingedSpace.comp_base, TopCat.hom_comp, ContinuousMap.comp_apply]`
  in the equivalence below traverses a goal mentioning `ComplexAnalytic.refineDatumGlue`, whose
  last two arguments are proofs, and plants `ComplexAnalytic.refineDatumGlue.congr_simp` **into
  this module** for a definition `Oka/Analytification/CrossMemberDatumGlue.lean` owns. The cure is
  that the bridge those three lemmas were doing is `rfl`: the two spellings of a composite applied
  to a point are definitionally equal, so `exact` closes what `simpa … using` was being asked to.
  **That is a third route to the same defect** — neither recorded file describes one where the
  `simp` set names no definition at all.

`Δdump` here is now **+14**, the number of declarations, and that is the figure to check a branch
on this file by.

**How much of the attribution is isolated, and how much is not.** Three dumps were taken: the
first draft, then the two `rfl` theorems and the `Category.assoc` rewrite together, then the
`exact`. The last step is a single change and its row disappeared with it. The middle step
bundles two changes, so which of the two removed
`ComplexAnalytic.refineDatumCrossProjSpace.congr_simp` is read off the shape of the lemma and not
off a run of its own — the `simp only` was the only tactic in the draft that traversed that
definition. A reader repairing a regression here should re-measure one change at a time.

## Main definitions

- `ComplexAnalytic.refineDatumCrossProjSpace`: **the cross-member projection at the level of
  spaces**, which is the one factor that has to be named rather than inlined.
- `ComplexAnalytic.refineDatumCrossPart`: **the refined overlap over the original overlap**, in
  the open-subspace vocabulary a cover datum is stated in.
- `ComplexAnalytic.refineDatumCrossTriple`: **the same on a triple overlap**, which is what lets
  the original datum's `hrange` be read at a refined triple.

## Main results

- `ComplexAnalytic.refineDatumCrossProjSpace_localisationProj`: **the `a`-side projection is a
  morphism over the `σ a`-th member**, at the level of spaces, which is the statement the next one
  is read off.
- `ComplexAnalytic.refineDatumCrossPart_eq` and `ComplexAnalytic.refineDatumCrossTriple_eq`:
  **the two definitions unfolded, by `rfl`**, so that a proof can open them without planting an
  equation lemma under their own names. See the section below for what that costs when they are
  absent.
- `ComplexAnalytic.refineDatumCrossPart_coverIncl`: **the comparison is a morphism over the
  `σ a`-th member.**
- `ComplexAnalytic.refineDatumGlueNe_analytification_localisationProj`: **the unequal branch's
  triangle with the `b`-side projection pushed down to its member**, which is the form the square
  below consumes.
- `ComplexAnalytic.refineDatumTransitionHom_localisationProj_of_ne`: **the refined transition lies
  over the original transition.** The content of this file, and the cross-member counterpart of
  the one sentence the same-member laws are read off.
- `ComplexAnalytic.coverOpen_refineDatumPoly_of_ne`: **the refined overlap is the preimage of the
  original overlap intersected with the caller's factor**, which is what splits `hrange` in two.
- `ComplexAnalytic.range_refineDatumCrossTriple_subset` and
  `ComplexAnalytic.refineDatumCrossTriple_coverTripleIncl`: **the refined triple overlap lies over
  the original triple overlap**, as a range containment and then as the morphism it builds.
- `ComplexAnalytic.range_refineDatumTransitionHom_localisationProj_subset`: **the half of the
  refined `hrange` that the original `hrange` gives.**
- `ComplexAnalytic.range_refineDatumTransitionHom_subset_iff`: **and it is the only half** — at a
  triple whose three members are different, the refined law is equivalent to a containment in the
  caller's own open.

## What is not here

* **`hrange` itself, and it is not one case away.** Everything above is at a triple with
  `σ a`, `σ b`, `σ c` pairwise different. The mixed triples — `σ a = σ b` with `σ c` different,
  and the two others — are untouched *here*, and they are not this argument with a hypothesis
  dropped: `ComplexAnalytic.refineDatumGlue` takes its equal branch there, whose triangle
  (`ComplexAnalytic.refineDatumGlueEq_analytification_comp`) is over a *member* and not over an
  overlap, so the square below has no statement at those triples and there is none to be had —
  at an equal pair there is no `ComplexAnalytic.coverTransitionHom` to lie over. **That reason
  is what settles them rather than what blocks them**: it is the shape a *different* square has,
  over an identification of the two members, and
  `Oka/Analytification/RefineDatumRange.lean` builds it and reads all four remaining shapes off
  it. This sentence ended *"let alone a proof"* until it did.
* **`hcocycle`, and it cannot be stated from anything in this file.**
  `ComplexAnalytic.coverTriple` takes `hrange` as an argument, so the cocycle law of the refined
  datum mentions a proof of the refined `hrange` three times in its own statement, and one shape
  of five is not one. It is stated in `Oka/Analytification/RefineDatumGlueData.lean`, as
  `ComplexAnalytic.RefineDatumCocycle`, off the assembled law. **This bullet said it is proved
  nowhere and that the cancellation the same-member proof uses — against the projection of the one
  fixed member, a monomorphism because it is an open immersion — has no analogue, for the reason
  `Oka/Analytification/CoverRefinement.lean` gives. That cancellation does have one**, against the
  projection of the member the triple's first index lies over, and
  `ComplexAnalytic.refineDatumHcocycle` (`Oka/Analytification/RefineDatumCocycle.lean`) proves the
  law. Nothing *here* is evidence about it: that file reads the square below at one edge of a
  triple and reopens nothing.
* **No hypothesis on `q`, and no refined cover datum.** This file adds no hypothesis and no
  structure. `ComplexAnalytic.coverGlueData` at a non-constant `σ` asks for all three laws at
  once and none of them is here; `Oka/Analytification/RefineDatumGlueData.lean` is where two of
  the three are supplied, the third is named and the datum is built.
* **Nothing about `hsymm`.** That law is `ComplexAnalytic.refineDatumGlue_symm`
  (`Oka/Analytification/RefineDatumSymm.lean`), it is algebraic where everything here is
  geometric, and neither is evidence about the other.
* **No scheme and no `admissible`**, as in the five files this one sits beside, and for the reason
  their `## What is not here` gives.
-/

open CategoryTheory MvPolynomial AlgebraicGeometry

universe u

namespace ComplexAnalytic

noncomputable section

variable {J B : Type u} (obj : J → Presentation.{u})
  (poly : ∀ i : J, J → MvPolynomial (ULift.{u} (Fin (obj i).n)) ℂ)
  (σ : B → J)
  (fam : ∀ b : B, MvPolynomial (ULift.{u} (Fin (obj (σ b)).n)) ℂ)
  (q : ∀ a : B, B → MvPolynomial (ULift.{u} (Fin (obj (σ a)).n)) ℂ)

/-! ### The refined overlap, over the original overlap -/

/-- **The cross-member projection, at the level of spaces**:
`ComplexAnalytic.refineDatumCrossProj` analytified and read through
`ComplexAnalytic.AnalyticSpace.forgetToLocallyRingedSpace`.

**Named rather than inlined into `ComplexAnalytic.refineDatumCrossPart` below, and for the reason
`ComplexAnalytic.coverOverlapIso` and `ComplexAnalytic.coverGlueIso` are named.** With the body
written out the composite still elaborates — a `def`'s declared type is checked at default
transparency — but the first `rw` that unfolds it leaves a target that is not type-correct at
`instances` transparency, `ComplexAnalytic.coverOverlapSpace` and
`AnalyticSpace.forgetToLocallyRingedSpace.obj (analytificationFunctor.obj (coverOverlap …))` being
the two spellings that then fail to unify. Ascribing the type once fixes it, and no proof below
has to mention either spelling. -/
def refineDatumCrossProjSpace {a b : B} (h : σ a ≠ σ b) :
    coverOverlapSpace.{u} (refineDatumObj.{u} obj σ fam)
        (refineDatumPoly.{u} obj poly σ fam q) a b ⟶
      coverOverlapSpace.{u} obj poly (σ a) (σ b) :=
  AnalyticSpace.forgetToLocallyRingedSpace.{u}.map
    (analytificationFunctor.{u}.map (refineDatumCrossProj.{u} obj σ fam poly q h))

/-- **The `a`-side projection is a morphism over the `σ a`-th member**, at the level of spaces:
`ComplexAnalytic.refineDatumCrossProj_analytification_localisationProj` carried down by
`ComplexAnalytic.AnalyticSpace.forgetToLocallyRingedSpace`.

The functor is applied to the equation rather than the equation rewritten under it, which is the
shape `ComplexAnalytic.refineTransitionHom_localisationProj` and both analytified triangles in
`Oka/Analytification/CrossMemberDatumGlue.lean` already use: the hypothesis is well-typed by
construction and the goal is what the unifier struggles with. -/
theorem refineDatumCrossProjSpace_localisationProj {a b : B} (h : σ a ≠ σ b) :
    refineDatumCrossProjSpace.{u} obj poly σ fam q h ≫
        (localisationProj.{u} (obj (σ a)).g (poly (σ a) (σ b))).toLRSHom =
      (localisationProj.{u} (refineDatumObj.{u} obj σ fam a).g
          (refineDatumPoly.{u} obj poly σ fam q a b)).toLRSHom ≫
        (localisationProj.{u} (obj (σ a)).g (fam a)).toLRSHom := by
  have e := congrArg (AnalyticSpace.forgetToLocallyRingedSpace.{u}.map)
    (refineDatumCrossProj_analytification_localisationProj.{u} obj σ fam poly q h)
  simp only [Functor.map_comp] at e
  exact e

/-- **The refined overlap of two different members, over the original overlap**, in the
open-subspace vocabulary a cover datum is stated in: the projection above conjugated by
`ComplexAnalytic.coverOverlapIso` at each end, so that it runs from `D(f_ab)` inside the `a`-th
refined member to `D(f_{σa σb})` inside the `σ a`-th member.

**There is no member-level version and there cannot be**, for the reason
`ComplexAnalytic.refineDatumCrossProj` gives: the two refined members lie over `obj (σ a)` and
`obj (σ b)`, and a cover datum carries no morphism between those. What it does carry is the
transition between the two descriptions of their overlap, and that is what the square below is
stated over. -/
def refineDatumCrossPart {a b : B} (h : σ a ≠ σ b) :
    coverPart.{u} (refineDatumObj.{u} obj σ fam) (refineDatumPoly.{u} obj poly σ fam q) a b ⟶
      coverPart.{u} obj poly (σ a) (σ b) :=
  (coverOverlapIso.{u} (refineDatumObj.{u} obj σ fam)
      (refineDatumPoly.{u} obj poly σ fam q) a b).inv ≫
    refineDatumCrossProjSpace.{u} obj poly σ fam q h ≫
    (coverOverlapIso.{u} obj poly (σ a) (σ b)).hom

/-- **The comparison unfolded**, by `rfl`, and stated for the reason
`ComplexAnalytic.refineDatumGlueNe_eq` is: the two proofs below have to open this definition, and
a `rw` at the definition itself plants an auto-generated equation lemma under its own name. -/
theorem refineDatumCrossPart_eq {a b : B} (h : σ a ≠ σ b) :
    refineDatumCrossPart.{u} obj poly σ fam q h =
      (coverOverlapIso.{u} (refineDatumObj.{u} obj σ fam)
          (refineDatumPoly.{u} obj poly σ fam q) a b).inv ≫
        refineDatumCrossProjSpace.{u} obj poly σ fam q h ≫
        (coverOverlapIso.{u} obj poly (σ a) (σ b)).hom :=
  rfl

/-- **It is a morphism over the `σ a`-th member**: the refined overlap included into the `a`-th
refined member and projected to `obj (σ a)^an` is the comparison followed into the original
overlap and then into the same member.

`ComplexAnalytic.coverOverlapIso_hom_coverIncl` at each end and the lemma above in the middle —
the same three steps `ComplexAnalytic.refineTransitionHom_localisationProj` takes, with the
transition replaced by a projection. This is the statement that identifies *which* point of
`obj (σ a)^an` a point of the refined overlap lies over, and both range computations below run on
it. -/
theorem refineDatumCrossPart_coverIncl {a b : B} (h : σ a ≠ σ b) :
    refineDatumCrossPart.{u} obj poly σ fam q h ≫ coverIncl.{u} obj poly (σ a) (σ b) =
      coverIncl.{u} (refineDatumObj.{u} obj σ fam) (refineDatumPoly.{u} obj poly σ fam q) a b ≫
        (localisationProj.{u} (obj (σ a)).g (fam a)).toLRSHom := by
  rw [refineDatumCrossPart_eq, Category.assoc, Category.assoc,
    coverOverlapIso_hom_coverIncl.{u} obj poly (σ a) (σ b),
    refineDatumCrossProjSpace_localisationProj, ← Category.assoc,
    ← coverOverlapIso_hom_coverIncl.{u} (refineDatumObj.{u} obj σ fam)
      (refineDatumPoly.{u} obj poly σ fam q) a b, Iso.inv_hom_id_assoc]

variable (glue : ∀ i j : J, coverOverlap.{u} obj poly i j ≅ coverOverlap.{u} obj poly j i)

/-- **The unequal branch's coherence triangle, with the `b`-side projection pushed down to its
member.**

`ComplexAnalytic.refineDatumGlueNe_analytification_comp` composed with
`ComplexAnalytic.localisationProj` and then rewritten by
`ComplexAnalytic.refineDatumCrossProj_analytification_localisationProj` **at `(b, a)`** — the
instance of that lemma with the two indices swapped, which is what turns
`ComplexAnalytic.refineDatumCrossProj … h.symm` into the two structure maps of the `b`-th refined
member. The `a`-side stays as it is; a consumer that wants it over its own member composes with
the same lemma at `(a, b)`.

**The rewrite is done in a hypothesis and not in the goal**, and the difference is not
stylistic: the goal as stated has
`ComplexAnalytic.analytificationFunctor.map (refineDatumGlueNe … ).hom` whose target is
`analytificationFunctor.obj (coverOverlap …)`, against which the structure map's source does not
match at `instances` transparency, and `rw` reports the pattern missing from a goal that displays
as containing it. Built with `CategoryTheory.reassoc_of%` and rewritten there, the same step is
immediate. -/
theorem refineDatumGlueNe_analytification_localisationProj {a b : B} (h : σ a ≠ σ b)
    (rr : MvPolynomial (ULift.{u} (Fin ((obj (σ b)).n + 1))) ℂ)
    (he : RefineDatumCrossEq.{u} obj σ fam poly q glue a b rr)
    (uu : (PresentedAlgebra.{u} ((obj (σ b)).n + 1) ((obj (σ b)).k + 1)
      (localisationPresentation.{u} (obj (σ b)).g (poly (σ b) (σ a))))ˣ)
    (hu : RefineDatumCrossUnit.{u} obj σ fam poly q a b rr uu) :
    analytificationFunctor.{u}.map
          (refineDatumGlueNe.{u} obj σ fam poly q glue h rr he uu hu).hom ≫
        localisationProj.{u} (refineDatumObj.{u} obj σ fam b).g
            (refineDatumPoly.{u} obj poly σ fam q b a) ≫
          localisationProj.{u} (obj (σ b)).g (fam b) =
      analytificationFunctor.{u}.map (refineDatumCrossProj.{u} obj σ fam poly q h) ≫
        analytificationFunctor.{u}.map (glue (σ a) (σ b)).hom ≫
          localisationProj.{u} (obj (σ b)).g (poly (σ b) (σ a)) := by
  have e2 := refineDatumCrossProj_analytification_localisationProj.{u} obj σ fam poly q h.symm
  have e := (reassoc_of% (refineDatumGlueNe_analytification_comp.{u} obj σ fam poly q glue h rr he
    uu hu)) (localisationProj.{u} (obj (σ b)).g (poly (σ b) (σ a)))
  rw [e2] at e
  exact e

variable (rr : ∀ _ b : B, MvPolynomial (ULift.{u} (Fin ((obj (σ b)).n + 1))) ℂ)
  (uu : ∀ a b : B, (PresentedAlgebra.{u} ((obj (σ b)).n + 1) ((obj (σ b)).k + 1)
    (localisationPresentation.{u} (obj (σ b)).g (poly (σ b) (σ a))))ˣ)

/-- **The refined transition lies over the original cover's own transition**, where the two
refined members lie over two different members.

Going from the `a`-th refined member to the `b`-th and then down to `obj (σ b)^an` is going down
to the original overlap first and taking the original transition there. This is the cross-member
counterpart of `ComplexAnalytic.refineTransitionHom_localisationProj`, and the counterpart is not
a statement over a member: **a cover datum has no morphism between two of its members**, so the
lower edge of the square is `ComplexAnalytic.coverTransitionHom` of the original datum rather than
a projection.

The proof unfolds both transitions, cancels the two outer comparison isomorphisms with
`ComplexAnalytic.coverOverlapIso_hom_coverIncl`, and is then the previous lemma under
`ComplexAnalytic.AnalyticSpace.forgetToLocallyRingedSpace` — with
`ComplexAnalytic.refineDatumGlue_of_ne` naming the branch the field takes at such a pair. The
last step is `congrArg` and not `rw`, for the reason recorded there. -/
theorem refineDatumTransitionHom_localisationProj_of_ne
    (he : ∀ a b : B, ∀ _ : σ a ≠ σ b,
      RefineDatumCrossEq.{u} obj σ fam poly q glue a b (rr a b))
    (hu : ∀ a b : B, ∀ _ : σ a ≠ σ b,
      RefineDatumCrossUnit.{u} obj σ fam poly q a b (rr a b) (uu a b)) {a b : B} (h : σ a ≠ σ b) :
    coverTransitionHom.{u} (refineDatumObj.{u} obj σ fam) (refineDatumPoly.{u} obj poly σ fam q)
          (refineDatumGlue.{u} obj σ fam poly q glue rr uu he hu) a b ≫
        (localisationProj.{u} (obj (σ b)).g (fam b)).toLRSHom =
      refineDatumCrossPart.{u} obj poly σ fam q h ≫
        coverTransitionHom.{u} obj poly glue (σ a) (σ b) := by
  rw [coverTransitionHom, coverTransition, Iso.trans_hom, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Category.assoc, Category.assoc,
    reassoc_of% (coverOverlapIso_hom_coverIncl.{u} (refineDatumObj.{u} obj σ fam)
      (refineDatumPoly.{u} obj poly σ fam q) b a),
    refineDatumCrossPart_eq, coverTransitionHom, coverTransition, Iso.trans_hom,
    Iso.trans_hom,
    Iso.symm_hom, Category.assoc, Category.assoc, Category.assoc, Iso.hom_inv_id_assoc]
  rw [Category.assoc, coverOverlapIso_hom_coverIncl.{u} obj poly (σ b) (σ a),
    coverGlueIso, coverGlueIso, Functor.mapIso_hom, Functor.mapIso_hom, Functor.mapIso_hom,
    Functor.mapIso_hom, refineDatumGlue_of_ne.{u} obj σ fam poly q glue rr uu he hu h]
  have key := congrArg (AnalyticSpace.forgetToLocallyRingedSpace.{u}.map)
    (refineDatumGlueNe_analytification_localisationProj.{u} obj poly σ fam q glue h (rr a b)
      (he a b h) (uu a b) (hu a b h))
  simp only [Functor.map_comp] at key
  exact congrArg ((coverOverlapIso.{u} (refineDatumObj.{u} obj σ fam)
    (refineDatumPoly.{u} obj poly σ fam q) a b).inv ≫ ·) key

/-! ### What `hrange` becomes -/

/-- **The refined overlap of two different members is the preimage of two opens**: of the
original datum's own `D(f_{σa σb})` and of the caller's extra factor `D(q a b)`, along the
projection of the `a`-th refined member down to `obj (σ a)^an`.

`ComplexAnalytic.refineDatumPoly_of_ne`, `ComplexAnalytic.localisationOpen_rename` and
`ComplexAnalytic.localisationOpen_mul`, in that order and nothing else. **This is what splits
`hrange` into a half the original datum supplies and a half only a hypothesis on `q` can**, and
the split is visible only at this spelling: the field `ComplexAnalytic.refineDatumPoly` is one
polynomial, and it is the factorisation of that polynomial that separates the two.

The `change` is what lets the rewrite reach `ComplexAnalytic.refineDatumPoly`, which sits under
`ComplexAnalytic.coverOpen`; going the other way, through a `congrArg` on the folded statement,
exhausts the heartbeat budget at `isDefEq`. It is `change` and not `show` because
`linter.style.show` reports a `show` that alters the goal, which this one does. -/
theorem coverOpen_refineDatumPoly_of_ne {a b : B} (h : σ a ≠ σ b) :
    coverOpen.{u} (refineDatumObj.{u} obj σ fam) (refineDatumPoly.{u} obj poly σ fam q) a b =
      (TopologicalSpace.Opens.map
          (localisationProj.{u} (obj (σ a)).g (fam a)).toLRSHom.base).obj
        (coverOpen.{u} obj poly (σ a) (σ b) ⊓
          localisationOpen.{u} (obj (σ a)).g (q a b)) := by
  change localisationOpen.{u} (localisationPresentation.{u} (obj (σ a)).g (fam a))
      (refineDatumPoly.{u} obj poly σ fam q a b) = _
  rw [refineDatumPoly_of_ne.{u} obj poly σ fam q h, localisationOpen_rename,
    localisationOpen_mul]

/-- **The refined triple overlap lands in the original triple overlap.**

Both halves are the same lemma read at two pairs: a point of the refined `a`-`b`-`c` triple
overlap lies over a point of `obj (σ a)^an` that is in `D(f_{σa σb})` because it is in the refined
`a`-`b` overlap, and in `D(f_{σa σc})` because it is in the refined `a`-`c` one. The caller's two
extra factors are discarded at both, which is the only use this file makes of the fact that a
preimage of an intersection is an intersection of preimages.

**The distinctness of `σ b` and `σ c` is not needed and is not taken**: this is a statement about
where the `a`-side of two refined overlaps sits, and `c` enters only through the second overlap.
-/
theorem range_refineDatumCrossTriple_subset {a b c : B} (hab : σ a ≠ σ b) (hac : σ a ≠ σ c) :
    Set.range (coverTripleIncl.{u} (refineDatumObj.{u} obj σ fam)
          (refineDatumPoly.{u} obj poly σ fam q) a b c ≫
        refineDatumCrossPart.{u} obj poly σ fam q hab ≫
          coverIncl.{u} obj poly (σ a) (σ b)).base ⊆
      ((coverOpen.{u} obj poly (σ a) (σ b) ⊓ coverOpen.{u} obj poly (σ a) (σ c) :
        TopologicalSpace.Opens (coverSpace.{u} obj (σ a))) : Set (coverSpace.{u} obj (σ a))) := by
  rw [refineDatumCrossPart_coverIncl, ← Category.assoc, LocallyRingedSpace.restrictLE_fac]
  rintro _ ⟨x, rfl⟩
  simp only [LocallyRingedSpace.comp_base, TopCat.hom_comp, ContinuousMap.comp_apply]
  exact ⟨((SetLike.ext_iff.1
      (coverOpen_refineDatumPoly_of_ne.{u} obj poly σ fam q hab) _).1 x.2.1).1,
    ((SetLike.ext_iff.1 (coverOpen_refineDatumPoly_of_ne.{u} obj poly σ fam q hac) _).1 x.2.2).1⟩

/-- **The refined triple overlap, over the original triple overlap.**

`AlgebraicGeometry.LocallyRingedSpace.liftRestrict` at the containment above. It exists so that
the original datum's `hrange` — which is stated at `ComplexAnalytic.coverTripleIncl` of the
original data — can be read at a refined triple, and that is its only consumer. -/
def refineDatumCrossTriple {a b c : B} (hab : σ a ≠ σ b) (hac : σ a ≠ σ c) :
    coverTriplePart.{u} (refineDatumObj.{u} obj σ fam)
        (refineDatumPoly.{u} obj poly σ fam q) a b c ⟶
      coverTriplePart.{u} obj poly (σ a) (σ b) (σ c) :=
  LocallyRingedSpace.liftRestrict
    (coverTripleIncl.{u} (refineDatumObj.{u} obj σ fam)
        (refineDatumPoly.{u} obj poly σ fam q) a b c ≫
      refineDatumCrossPart.{u} obj poly σ fam q hab ≫ coverIncl.{u} obj poly (σ a) (σ b)) _
    (range_refineDatumCrossTriple_subset.{u} obj poly σ fam q hab hac)

/-- **The lift unfolded**, by `rfl`, for the reason `ComplexAnalytic.refineDatumCrossPart_eq`
is. -/
theorem refineDatumCrossTriple_eq {a b c : B} (hab : σ a ≠ σ b) (hac : σ a ≠ σ c) :
    refineDatumCrossTriple.{u} obj poly σ fam q hab hac =
      LocallyRingedSpace.liftRestrict
        (coverTripleIncl.{u} (refineDatumObj.{u} obj σ fam)
            (refineDatumPoly.{u} obj poly σ fam q) a b c ≫
          refineDatumCrossPart.{u} obj poly σ fam q hab ≫ coverIncl.{u} obj poly (σ a) (σ b)) _
        (range_refineDatumCrossTriple_subset.{u} obj poly σ fam q hab hac) :=
  rfl

/-- **The lift is a factorisation**: followed by the original triple inclusion it is the refined
triple inclusion followed by the comparison of double overlaps.

`AlgebraicGeometry.LocallyRingedSpace.hom_ext_restrict` reduces it to an equation over the
`σ a`-th member, where both sides are the morphism the lift was built from —
`AlgebraicGeometry.LocallyRingedSpace.restrictLE_fac` on one side and
`AlgebraicGeometry.LocallyRingedSpace.liftRestrict_fac` on the other. -/
theorem refineDatumCrossTriple_coverTripleIncl {a b c : B} (hab : σ a ≠ σ b) (hac : σ a ≠ σ c) :
    refineDatumCrossTriple.{u} obj poly σ fam q hab hac ≫
        coverTripleIncl.{u} obj poly (σ a) (σ b) (σ c) =
      coverTripleIncl.{u} (refineDatumObj.{u} obj σ fam)
          (refineDatumPoly.{u} obj poly σ fam q) a b c ≫
        refineDatumCrossPart.{u} obj poly σ fam q hab := by
  refine LocallyRingedSpace.hom_ext_restrict _ _ _ ?_
  rw [Category.assoc, LocallyRingedSpace.restrictLE_fac, refineDatumCrossTriple_eq,
    LocallyRingedSpace.liftRestrict_fac]
  exact (Category.assoc _ _ _).symm

/-- **The half of the refined `hrange` that the original `hrange` gives**, at a triple whose
three members are all different: the refined transition carries the refined triple overlap into
the part of `obj (σ b)^an` that meets `obj (σ c)`.

The square above turns the composite into the comparison followed by the original transition, the
lift above factors the comparison through the original triple overlap, and what is left is the
original datum's own law. **Nothing in the proof is about the refinement** once those two steps
are taken, which is the point: the geometry is the original cover's and the refinement only has
to be shown to sit over it.

This is not yet `hrange` for the refined datum, and the next statement says exactly how much is
missing. -/
theorem range_refineDatumTransitionHom_localisationProj_subset
    (hrange : ∀ i j k : J, i ≠ j → i ≠ k → j ≠ k →
      Set.range (coverTripleIncl.{u} obj poly i j k ≫
          coverTransitionHom.{u} obj poly glue i j).base ⊆
        (coverOpen.{u} obj poly j k : Set (coverSpace.{u} obj j)))
    (he : ∀ a b : B, ∀ _ : σ a ≠ σ b,
      RefineDatumCrossEq.{u} obj σ fam poly q glue a b (rr a b))
    (hu : ∀ a b : B, ∀ _ : σ a ≠ σ b,
      RefineDatumCrossUnit.{u} obj σ fam poly q a b (rr a b) (uu a b)) {a b c : B}
    (hab : σ a ≠ σ b) (hac : σ a ≠ σ c) (hbc : σ b ≠ σ c) :
    Set.range (coverTripleIncl.{u} (refineDatumObj.{u} obj σ fam)
          (refineDatumPoly.{u} obj poly σ fam q) a b c ≫
        coverTransitionHom.{u} (refineDatumObj.{u} obj σ fam)
            (refineDatumPoly.{u} obj poly σ fam q)
            (refineDatumGlue.{u} obj σ fam poly q glue rr uu he hu) a b ≫
          (localisationProj.{u} (obj (σ b)).g (fam b)).toLRSHom).base ⊆
      (coverOpen.{u} obj poly (σ b) (σ c) : Set (coverSpace.{u} obj (σ b))) := by
  rw [refineDatumTransitionHom_localisationProj_of_ne.{u} obj poly σ fam q glue rr uu he hu hab,
    ← Category.assoc,
    ← refineDatumCrossTriple_coverTripleIncl.{u} obj poly σ fam q hab hac, Category.assoc,
    LocallyRingedSpace.comp_base, TopCat.coe_comp, Set.range_comp]
  exact subset_trans (Set.image_subset_range _ _) (hrange (σ a) (σ b) (σ c) hab hac hbc)

/-- **And it is the only half.** At a triple whose three members are all different, `hrange` for
the refined datum is *equivalent* to the image landing in the preimage of the caller's own open
`D(q b c)`.

`ComplexAnalytic.coverOpen_refineDatumPoly_of_ne` splits the target into two containments, the
previous theorem discharges the first unconditionally, and the second is what remains. So the
absence `Oka/Analytification/CrossMemberGlue.lean` records as "nothing here produces `q`" is
sharper than it reads for this law: `hrange` does not ask that the refined overlap be the
geometric one, it asks this one containment, at each ordered triple of pairwise different
members.

**It is an equivalence and not an implication on purpose.** A hypothesis on `q` strong enough for
`hrange` cannot be weaker than the right-hand side, so this also says what a caller may *not* be
asked for; and it is the form in which a later file can adopt the right-hand side as the
hypothesis itself and get the law with no further geometry. -/
theorem range_refineDatumTransitionHom_subset_iff
    (hrange : ∀ i j k : J, i ≠ j → i ≠ k → j ≠ k →
      Set.range (coverTripleIncl.{u} obj poly i j k ≫
          coverTransitionHom.{u} obj poly glue i j).base ⊆
        (coverOpen.{u} obj poly j k : Set (coverSpace.{u} obj j)))
    (he : ∀ a b : B, ∀ _ : σ a ≠ σ b,
      RefineDatumCrossEq.{u} obj σ fam poly q glue a b (rr a b))
    (hu : ∀ a b : B, ∀ _ : σ a ≠ σ b,
      RefineDatumCrossUnit.{u} obj σ fam poly q a b (rr a b) (uu a b)) {a b c : B}
    (hab : σ a ≠ σ b) (hac : σ a ≠ σ c) (hbc : σ b ≠ σ c) :
    Set.range (coverTripleIncl.{u} (refineDatumObj.{u} obj σ fam)
          (refineDatumPoly.{u} obj poly σ fam q) a b c ≫
        coverTransitionHom.{u} (refineDatumObj.{u} obj σ fam)
            (refineDatumPoly.{u} obj poly σ fam q)
            (refineDatumGlue.{u} obj σ fam poly q glue rr uu he hu) a b).base ⊆
        (coverOpen.{u} (refineDatumObj.{u} obj σ fam) (refineDatumPoly.{u} obj poly σ fam q) b c :
          Set (coverSpace.{u} (refineDatumObj.{u} obj σ fam) b)) ↔
      Set.range (coverTripleIncl.{u} (refineDatumObj.{u} obj σ fam)
            (refineDatumPoly.{u} obj poly σ fam q) a b c ≫
          coverTransitionHom.{u} (refineDatumObj.{u} obj σ fam)
              (refineDatumPoly.{u} obj poly σ fam q)
              (refineDatumGlue.{u} obj σ fam poly q glue rr uu he hu) a b ≫
            (localisationProj.{u} (obj (σ b)).g (fam b)).toLRSHom).base ⊆
        ↑(localisationOpen.{u} (obj (σ b)).g (q b c)) := by
  have hfree := Set.range_subset_iff.1
    (range_refineDatumTransitionHom_localisationProj_subset.{u} obj poly σ fam q glue rr uu
      hrange he hu hab hac hbc)
  rw [Set.range_subset_iff, Set.range_subset_iff]
  constructor
  · intro H x
    exact ((SetLike.ext_iff.1
      (coverOpen_refineDatumPoly_of_ne.{u} obj poly σ fam q hbc) _).1 (H x)).2
  · intro H x
    exact (SetLike.ext_iff.1
      (coverOpen_refineDatumPoly_of_ne.{u} obj poly σ fam q hbc) _).2 ⟨hfree x, H x⟩

end

end ComplexAnalytic
