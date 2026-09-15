/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import OkaTest.ProjectiveLineSpan

/-!
# The `directed` law of a locally directed cover, at `ℙ¹`

`OkaTest/ProjectiveLineSpan.lean` builds the diagram this law is a claim about — the overlap of
the two charts of `ℙ¹` and the two arrows out of it — and says in its `## What is not here` that
no `directed` law is stated there and that this is a choice rather than an obstruction. **This
file is that law.** With `OkaTest/LocalisationChain.lean`, which is the `trans_comp` half, both
laws of a locally directed cover now have an instance in this repository.

## What the law asks

`Mathlib/AlgebraicGeometry/Cover/Directed.lean:51-53` — cited by path, because that module is
**not** in the import closure of `Oka` and its names would resolve to nothing:

    directed {i j : 𝒰.I₀} (x : (pullback (𝒰.f i) (𝒰.f j)).carrier) :
      ∃ (k : 𝒰.I₀) (hki : k ⟶ i) (hkj : k ⟶ j) (y : 𝒰.X k),
        pullback.lift (trans hki) (trans hkj) (by simp [w]) y = x

So it is a statement about **points of a pullback**, and it needs three things: the pullback to
exist, a third member below both, and the lift out of that member to be surjective on points.

## The answer, and it is a negative worth having

**The law needs nothing about `ℙ¹`.** `OkaTest.ProjectiveLineDirected.exists_overlapLift_eq` is
proved for an arbitrary `AlgebraicGeometry.LocallyRingedSpace.GlueData`, and
`OkaTest.ProjectiveLineDirected.lineDirected` is that theorem applied to
`ComplexAnalytic.projectiveLineGlueData` and nothing else.

The reason is that all three ingredients are already on `master`, and the third one is not merely
present but *sharp*:

* the pullback exists, because the two inclusions are open immersions
  (`AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.hasPullback_of_left` and
  `…IsOpenImmersion.hasPullback_of_right`, in `Mathlib/Geometry/RingedSpace/OpenImmersion.lean`);
* the third member is the overlap `V (i, j)` the glue datum already carries;
* and `AlgebraicGeometry.LocallyRingedSpace.GlueData.vIsoPullback` says the comparison map is an
  **isomorphism**, not merely a surjection. `OkaTest.ProjectiveLineDirected.overlapLift_eq` is the
  identification, by the uniqueness half of `CategoryTheory.Limits.pullback.lift`, and the law
  then follows from an isomorphism of locally ringed spaces being a homeomorphism
  (`AlgebraicGeometry.LocallyRingedSpace.homeoOfIso`).

**Where the transition goes is the part worth reading.** The second leg of the lift is
`D.t i j ≫ D.f j i` — `OkaTest.ProjectiveLineDirected.overlapLift_snd` — and `D.t i j` at `ℙ¹`
is `ComplexAnalytic.lineSwapIso` analytified. So the transition is in the **statement** of the
law and never in its proof: `AlgebraicGeometry.LocallyRingedSpace.GlueData.vIsoPullback_hom_snd`
already carries it, and the proof below quotes that lemma rather than computing with it.
`AlgebraicGeometry.LocallyRingedSpace.GlueData.ι_jointly_surjective`, which one might expect to
be the surjectivity input, is not used by the law at all — an isomorphism supplies the
surjectivity outright, and the only use of it below is in the non-vacuity.

## Why that is not a vacuous instance

An isomorphism is surjective for any glue datum whatever, including one whose overlaps are empty
or whose overlap is the whole member. Three theorems below close those readings **at `ℙ¹`**, and
they are where this file's content specific to `ℙ¹` lives:

* `OkaTest.ProjectiveLineDirected.nonempty_linePullback`: for `i ≠ j` the pullback is **not
  empty**, so the law quantifies over something. It is
  `ComplexAnalytic.localisationOpen_lineRel_ne_bot` transported along the lift — the two charts of
  `ℙ¹` really do meet in the glued space.
* `OkaTest.ProjectiveLineDirected.not_surjective_linePullback_fst`: the first projection out of
  the pullback is **not surjective** onto the chart, so the witness `k` is a proper part of `i`
  and the law is not satisfied by taking `k = i`. It is
  `ComplexAnalytic.lineOrigin_notMem_localisationOpen` — the origin of `𝔸¹` is glued to nothing —
  through `ComplexAnalytic.range_f_subset_projectiveLineGlueData`.
* `OkaTest.ProjectiveLineDirected.not_range_ι_subset_range_ι`: **neither chart is contained in the
  other**, so the third member the law produces cannot be either of the two it is below. This is
  the statement `OkaTest/LocalisationChain.lean` asserted without proof and attributed to the two
  `localisationOpen` lemmas, which do not reach it; it is proved here from
  `AlgebraicGeometry.LocallyRingedSpace.GlueData.ι_jointly_surjective` and
  `ComplexAnalytic.not_surjective_ι_projectiveLineGlueData` instead, and that file's sentence is
  corrected in this pull request to cite what actually proves it.

A fourth degenerate reading, that the two legs out of the apex might be the same map, is **not**
closed here; see `## What is not here`.

## The witness is the apex of the span

`OkaTest.ProjectiveLineDirected.lineOverlapIsoSpanApex` identifies the `V (i, j)` this law hands
back with `OkaTest.ProjectiveLineSpan.analyticLineSpan`'s apex, by
`ComplexAnalytic.coverOverlapIso`. It is what makes the two files one exercise rather than two:
the object the span puts at the top of the diagram is the object the law produces as the member
below both charts.

## What is not here

**No `directed` law as a class field, and no `LocallyDirected` instance**, because there is no
cover for it to be an instance on. `AlgebraicGeometry.LocallyRingedSpace.GlueData.openCover` gives
`ComplexAnalytic.projectiveLineGlueData` a cover whose index type is `ComplexAnalytic.pair` — the
two charts — and **the overlap is not one of its members**. Making it one means a three-member
cover, which is a different construction and a different test.

**No claim that the two legs out of the apex are different morphisms of spaces.** They are
`D.f i j` and `D.t i j ≫ D.f j i`, and `ComplexAnalytic.lineSwapIso_ne_refl` says the underlying
isomorphism of *presentations* is not the identity, while
`OkaTest.ProjectiveLineSpan.lineSpanFst_ne_lineSpanSnd` says the two legs of the span differ as
morphisms of `ComplexAnalytic.Presentation`. **Neither of those is the geometric statement.**
Getting from either to it needs `ComplexAnalytic.analytificationFunctor` to be faithful on this
pair, or a point of the overlap at which the two legs disagree; nothing in this repository
supplies either, and no such claim is made below.

**No analytic analogue of the `LocallyDirected` class, and here is the measurement of what
defining one would still be missing.** The class has six fields — `trans`, `trans_id`,
`trans_comp`, `w`, `directed`, `property_trans`
(`Mathlib/AlgebraicGeometry/Cover/Directed.lean:46-54`). After this file and
`OkaTest/LocalisationChain.lean`:

* `directed` has an instance, and it is this file.
* `trans_comp` has an instance — `OkaTest.LocalisationChain.chainFunctor` — but **at the level of
  `ComplexAnalytic.Presentation`, not of a cover of a space.** So the two instances are not
  instances of the same structure, and a class quantifying over both would have to be stated at
  whichever of the two levels the other one can be moved to. That is the gap, and it is a design
  question rather than a missing proof.
* `trans`, `trans_id` and `w` have nothing exercising them at all.
  `AlgebraicGeometry.LocallyRingedSpace.OpenCover` carries a bare index type `J : Type u` with no
  `CategoryTheory.Category` instance on it, so there are no arrows for a transition map to be
  indexed by, and `w` — which says a transition composed into the larger member is the smaller
  one's map — has nothing to be about until there are.
* `property_trans` asks for a `CategoryTheory.MorphismProperty`. That class **is** reachable — it
  is Mathlib's and it is in this repository's import closure — and **this clause read *but a grep
  for `MorphismProperty` over `Oka/` is empty, so nothing here has ever used the framework*, and
  stopped being true on 2026-08-31**, when `1556d01` declared
  `ComplexAnalytic.AnalyticSpace.isFiniteEtale` as a property of that class and cut the category
  of covers out of it with `CategoryTheory.MorphismProperty.Over`. **The form is *stopped being
  true on* and not *until***: the day the clause stopped being true and the day it is rewritten
  here are three weeks apart, and this repository's `until <date>` record names the second, so
  neither date would be right in that form. `Oka/AnalyticSpace/LocalIso.lean` records a clause of
  its own the same way and for the same reason — *it had already stopped being true before the
  branch that removed it* — and that is the precedent followed here. **At
  the commit that repairs it** that grep returns **218** lines in **24** files under `Oka/`, and
  **13** modules under `Oka/` name the class in their comment-stripped code,
  `scripts/import_cost.py`'s `strip_comments` the instrument.
  **What the clause was evidence for survives it**, which is why the sentence below it does not
  move: which property a cover of a complex analytic space should carry as `property_trans` is
  undecided rather than merely unstated. The field asks the transition maps to satisfy the
  property the cover's own precoverage is taken with — `P` in the class's own binder at
  `Mathlib/AlgebraicGeometry/Cover/Directed.lean:44` — and nothing here has chosen one for an
  analytic cover. That `ComplexAnalytic.AnalyticSpace.isFiniteEtale` is a
  `CategoryTheory.MorphismProperty` of `ComplexAnalytic.AnalyticSpace` makes such a choice
  available and is not itself that choice.

So the class is three decisions away and not one: a category on the cover's index type, a choice
of morphism property, and which level `trans_comp` lives at. Defining it remains a design
decision and is declined here, as `OkaTest/LocalisationChain.lean` and
`OkaTest/ProjectiveLineSpan.lean` both declined it.

**`OkaTest.ProjectiveLineDirected.overlapLift` and its six lemmas are not library API.** They are
statements about an arbitrary `AlgebraicGeometry.LocallyRingedSpace.GlueData` with no analytic
content, and they belong beside
`AlgebraicGeometry.LocallyRingedSpace.GlueData.vIsoPullback` in
`Oka/Geometry/RingedSpace/PresheafedSpace/Gluing.lean` if anything outside a test ever wants
them. Nothing does; they are here because the `ℙ¹` instance is the only consumer, which is
`OkaTest.LocalisationChain.ofThree`'s disposition and the same reasoning.

**Nothing about `ℙ¹` that `OkaTest/ProjectiveLine.lean` does not already say.** That file is
explicit that nothing in it shows the glued space is `ℙ¹` — not compact, not shown to differ from
the analytification of a single presentation. This file adds no such statement and inherits that
disclaimer whole.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry ComplexAnalytic

universe u

namespace OkaTest.ProjectiveLineDirected

noncomputable section

/-! ### The lift out of the overlap, for an arbitrary glue datum

Not library API; see the header. -/

section GlueData

variable (D : LocallyRingedSpace.GlueData.{u})

/-- **The lift of the overlap into the pullback of the two inclusions**, which is the morphism the
`directed` law asks to be surjective on points.

Its two legs are the ones a locally directed cover would call `trans` at the two arrows out of
the member below: the inclusion `f i j` into the `i`-th member, and the transition followed by
the inclusion into the `j`-th. The commutation the lift needs is
`CategoryTheory.GlueData.glue_condition`. -/
def overlapLift (i j : D.J) :
    D.V (i, j) ⟶ Limits.pullback (D.toGlueData.ι i) (D.toGlueData.ι j) :=
  Limits.pullback.lift (D.toGlueData.f i j) (D.toGlueData.t i j ≫ D.toGlueData.f j i)
    (by rw [Category.assoc]; exact (D.toGlueData.glue_condition i j).symm)

/-- The first leg is the inclusion of the overlap into the `i`-th member. -/
@[reassoc (attr := simp)]
theorem overlapLift_fst (i j : D.J) :
    overlapLift D i j ≫ Limits.pullback.fst _ _ = D.toGlueData.f i j :=
  Limits.pullback.lift_fst _ _ _

/-- **The second leg carries the transition.** This lemma and the definition above are the only
two places in this file where `D.t i j` is mentioned at all, and at `ℙ¹` it is
`ComplexAnalytic.lineSwapIso` analytified — so the transition is part of the statement of the law
and of no proof. -/
@[reassoc (attr := simp)]
theorem overlapLift_snd (i j : D.J) :
    overlapLift D i j ≫ Limits.pullback.snd _ _ =
      D.toGlueData.t i j ≫ D.toGlueData.f j i :=
  Limits.pullback.lift_snd _ _ _

/-- **The lift is `AlgebraicGeometry.LocallyRingedSpace.GlueData.vIsoPullback`.**

Both are morphisms into a pullback and their two factorisations agree — `overlapLift_fst` against
`…vIsoPullback_hom_fst` and `overlapLift_snd` against `…vIsoPullback_hom_snd` — so the uniqueness
half of `CategoryTheory.Limits.pullback.lift` identifies them. This is the whole proof of the
law: what `vIsoPullback` adds over a bare surjection is that the comparison is invertible. -/
theorem overlapLift_eq (i j : D.J) : overlapLift D i j = (D.vIsoPullback i j).hom :=
  Limits.pullback.hom_ext
    ((overlapLift_fst D i j).trans (D.vIsoPullback_hom_fst i j).symm)
    ((overlapLift_snd D i j).trans (D.vIsoPullback_hom_snd i j).symm)

/-- The lift is an isomorphism, which is `OkaTest.ProjectiveLineDirected.overlapLift_eq` read as a
statement about the morphism rather than about which morphism it is. Deliberately not an
`instance`: nothing below needs it found by synthesis, and it would be registered for every glue
datum in the environment. -/
theorem isIso_overlapLift (i j : D.J) : IsIso (overlapLift D i j) :=
  (overlapLift_eq D i j).symm ▸ inferInstanceAs (IsIso (D.vIsoPullback i j).hom)

/-- **The lift is surjective on points.** An isomorphism of locally ringed spaces is a
homeomorphism of the carriers, by
`AlgebraicGeometry.LocallyRingedSpace.homeoOfIso`. -/
theorem overlapLift_surjective (i j : D.J) : Function.Surjective (overlapLift D i j).base := by
  rw [overlapLift_eq]
  exact (LocallyRingedSpace.homeoOfIso (D.vIsoPullback i j)).surjective

/-- **The `directed` law, for an arbitrary glue datum**: every point of the pullback of two
inclusions comes from the overlap they carry.

This is the same statement as the `directed` field quoted in the header, with the third member
taken to be `V (i, j)` and the two arrows out of it taken to be the two legs of
`OkaTest.ProjectiveLineDirected.overlapLift`. It is **not** an instance of that field, because
the overlap is not a member of the cover; see the header's `## What is not here`. -/
theorem exists_overlapLift_eq (i j : D.J)
    (x : (Limits.pullback (D.toGlueData.ι i) (D.toGlueData.ι j) : LocallyRingedSpace.{u})) :
    ∃ y : D.V (i, j), (overlapLift D i j).base y = x :=
  overlapLift_surjective D i j x

end GlueData

/-! ### At `ℙ¹` -/

/-- **The `directed` law at `ℙ¹`.**

`OkaTest.ProjectiveLineDirected.exists_overlapLift_eq` at
`ComplexAnalytic.projectiveLineGlueData` and nothing else — the law uses no property of this glue
datum. What is specific to `ℙ¹` is that the statement is not vacuous, which is the three
theorems below. -/
theorem lineDirected (i j : pair.{u})
    (x : (Limits.pullback (projectiveLineGlueData.{u}.toGlueData.ι i)
      (projectiveLineGlueData.{u}.toGlueData.ι j) : LocallyRingedSpace.{u})) :
    ∃ y : projectiveLineGlueData.{u}.V (i, j),
      (overlapLift projectiveLineGlueData.{u} i j).base y = x :=
  exists_overlapLift_eq projectiveLineGlueData.{u} i j x

/-- **Off the diagonal the overlap is `D(z)` as a space**, which is the `dif_neg` branch of
`CategoryTheory.GlueData.ofGlueData'`'s `V` field.

`ComplexAnalytic.f_projectiveLineGlueData` is the same unfolding for the `f` field, where it
costs an `eqToHom` because a morphism cannot be transported silently; here the two sides are
*objects*, so the equation is the branch itself. -/
theorem lineOverlap_eq (i j : pair.{u}) (hij : i ≠ j) :
    projectiveLineGlueData.{u}.V (i, j) =
      coverPart.{u} lineCoverObj.{u} lineCoverPoly.{u} i j :=
  dif_neg hij

/-- **The overlap of two distinct charts has a point.**
`ComplexAnalytic.localisationOpen_lineRel_ne_bot` says `D(z)` is not the empty open, and an open
subspace with no point is the empty open. -/
theorem nonempty_lineOverlap (i j : pair.{u}) (hij : i ≠ j) :
    Nonempty (projectiveLineGlueData.{u}.V (i, j)) := by
  rw [lineOverlap_eq i j hij]
  by_contra hcon
  refine localisationOpen_lineRel_ne_bot.{u} (TopologicalSpace.Opens.ext ?_)
  ext x
  simp only [Set.mem_empty_iff_false, iff_false, TopologicalSpace.Opens.coe_bot]
  exact fun hx ↦ hcon ⟨⟨x, hx⟩⟩

/-- **The two charts really do meet in the glued space**, so
`OkaTest.ProjectiveLineDirected.lineDirected` quantifies over something.

This is the first of the three non-vacuity statements: a glue datum whose overlaps were empty
would satisfy the law with nothing to prove. -/
theorem nonempty_linePullback (i j : pair.{u}) (hij : i ≠ j) :
    Nonempty (Limits.pullback (projectiveLineGlueData.{u}.toGlueData.ι i)
      (projectiveLineGlueData.{u}.toGlueData.ι j) : LocallyRingedSpace.{u}) :=
  (nonempty_lineOverlap i j hij).map (overlapLift projectiveLineGlueData.{u} i j).base

/-- **The overlap is a proper part of the chart**, so the member below both really is below them
and the law is not satisfied by taking `k = i`.

This is the second non-vacuity statement. The point that is missed is the origin of `𝔸¹`, which
`ComplexAnalytic.lineOrigin_notMem_localisationOpen` puts off `D(z)`; the first projection out of
the pullback lands in the range of `f i j`, which
`ComplexAnalytic.range_f_subset_projectiveLineGlueData` puts inside `D(z)`. -/
theorem not_surjective_linePullback_fst (i j : pair.{u}) (hij : i ≠ j) :
    ¬ Function.Surjective
      (Limits.pullback.fst (projectiveLineGlueData.{u}.toGlueData.ι i)
        (projectiveLineGlueData.{u}.toGlueData.ι j)).base := by
  intro hsurj
  obtain ⟨x, hx⟩ := hsurj lineOrigin.{u}
  obtain ⟨y, rfl⟩ := lineDirected i j x
  refine lineOrigin_notMem_localisationOpen.{u}
    (range_f_subset_projectiveLineGlueData i j hij ⟨y, ?_⟩)
  rw [← hx, ← overlapLift_fst projectiveLineGlueData.{u} i j]
  rfl

/-- **Neither chart is contained in the other**, so the member below both that
`OkaTest.ProjectiveLineDirected.lineDirected` produces cannot be one of the two charts, and the
`directed` law at `ℙ¹` genuinely needs a third object.

**This is the statement `OkaTest/LocalisationChain.lean` used to assert without proof**, and its
citation there was wrong: `ComplexAnalytic.localisationOpen_lineRel_ne_top` and `…_ne_bot` are
statements about one chart's open subset and do not reach the two charts' images in the glued
space. `OkaTest/ProjectiveLineSpan.lean` says so and declines the claim. The proof is instead by
covering: if one chart's image were inside the other's, the other would be surjective, because
`AlgebraicGeometry.LocallyRingedSpace.GlueData.ι_jointly_surjective` says the two together cover
and `ComplexAnalytic.pair_no_distinct_triple` says there is no third index — and
`ComplexAnalytic.not_surjective_ι_projectiveLineGlueData` says neither is surjective. -/
theorem not_range_ι_subset_range_ι (i j : pair.{u}) (hij : i ≠ j) :
    ¬ Set.range (projectiveLineGlueData.{u}.toGlueData.ι j).base ⊆
      Set.range (projectiveLineGlueData.{u}.toGlueData.ι i).base := by
  intro hsub
  refine not_surjective_ι_projectiveLineGlueData.{u} i fun x ↦ ?_
  obtain ⟨k, y, rfl⟩ := projectiveLineGlueData.{u}.ι_jointly_surjective x
  obtain rfl | hki := eq_or_ne k i
  · exact ⟨y, rfl⟩
  obtain rfl | hkj := eq_or_ne k j
  · exact hsub ⟨y, rfl⟩
  exact (pair_no_distinct_triple.{u} hki hkj hij).elim

/-- **The member the law produces is the apex of the span.**

`OkaTest/ProjectiveLineSpan.lean` puts `ComplexAnalytic.linePres` — the presentation of the
overlap — at `CategoryTheory.Limits.WalkingSpan.zero`, and
`ComplexAnalytic.coverOverlapIso` identifies its analytification with the open subspace `D(z)`
that this glue datum carries as `V (i, j)`. So the two files describe one object twice: the
diagram's apex and the `directed` law's witness. -/
def lineOverlapIsoSpanApex (i j : pair.{u}) (hij : i ≠ j) :
    (OkaTest.ProjectiveLineSpan.analyticLineSpan.{u}.obj
        WalkingSpan.zero).toLocallyRingedSpace ≅
      projectiveLineGlueData.{u}.V (i, j) :=
  coverOverlapIso.{u} lineCoverObj.{u} lineCoverPoly.{u} i j ≪≫
    eqToIso (lineOverlap_eq i j hij).symm

/-- The cover the law would have to be a `directed` field of is the one by the two charts, whose
index type is `ComplexAnalytic.pair` — recorded because it is what makes the overlap *not* a
member and so keeps this file a theorem rather than an instance. -/
example : projectiveLineGlueData.{u}.openCover.J = pair.{u} := rfl

/-- Its members are the inclusions, on the nose. -/
example (i : pair.{u}) :
    projectiveLineGlueData.{u}.openCover.map i = projectiveLineGlueData.{u}.toGlueData.ι i := rfl

end

end OkaTest.ProjectiveLineDirected
