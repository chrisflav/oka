/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Analytification.AffineCover

/-!
# A cover whose members overlap in the whole of themselves glues to one member

`Oka/Analytification/AffineCover.lean` glues an affine cover with distinguished overlaps, which
are typically proper. **This file is the opposite extreme**: if every off-diagonal
`ComplexAnalytic.coverOpen` is `⊤`, then each member's inclusion into the gluing is surjective,
and — being also an open immersion — an isomorphism.

## Why this is a `⊤` and not a `⊥` statement, and why it is worth having

The two degeneracies this development has already named are about the *refining family*: at
`fam ≡ 1` the refined cover is the original one reindexed
(`Oka/Analytification/RefineDatumWitness.lean`), and at `fam ≡ 0` every refined member is empty.
**Neither is about the overlaps**, and a cover can be non-degenerate in both of those senses and
still glue to one member, because what decides that is whether the members overlap in the whole
of themselves rather than what they are.

`ComplexAnalytic.coverOpen obj poly i j = ⊤` says exactly that, and the argument from it is short:
the inclusion `f i j` of the overlap into the `i`-th member is `ComplexAnalytic.coverIncl`
preceded by an `eqToHom`, so it is surjective; then any point of the `j`-th member is `f j i` of
something, and `AlgebraicGeometry.LocallyRingedSpace.GlueData.ι_eq_iff` identifies it with a point
of the `i`-th.

**So the pair of checks this line has been treating as a non-degeneracy test does not test for
this, and that is worth stating as a property of the checks rather than of any one instance.** A
refinement is customarily checked here by two statements about the refined *member*: that
`D(fam b)` is not the whole of its original member (so the refinement is not the reindexing at
`fam ≡ 1`) and that it is not empty (so it is not the family constantly `0`). **A cover can pass
both and still glue to one member**, because those two say nothing about the *overlaps*; the check
that would catch it is the third one, that the refined overlap is not the whole refined member,
and it is a different statement from either.

## The `eqToHom`, which is where the `CategoryTheory.GlueData'` route shows

`ComplexAnalytic.coverGlueData` is `CategoryTheory.GlueData.ofGlueData'` of
`ComplexAnalytic.coverGlueData'`, and `ofGlueData'` fills the diagonal with the member itself. So
`f i j` off the diagonal is `CategoryTheory.GlueData.ofGlueData'_f_of_ne`'s `eqToHom` followed by
the overlap's inclusion, and `ComplexAnalytic.f_coverGlueData_of_ne` below states this at every
cover datum. That theorem applies to a *refined* datum too, since
`ComplexAnalytic.refineDatumGlueData` is `coverGlueData` at the refined arguments — the
`CategoryTheory.GlueData'` it needs is solved from the goal and does not have to be named.

## Main results

- `ComplexAnalytic.f_coverGlueData_of_ne`: **the inclusion of an overlap into a member is
  `ComplexAnalytic.coverIncl` preceded by an equality coercion**, at every cover datum.
- `ComplexAnalytic.surjective_f_coverGlueData`: **and it is surjective when that overlap is the
  whole member.**
- `ComplexAnalytic.surjective_ι_coverGlueData`: **each member's inclusion into the gluing is then
  surjective.**
- `ComplexAnalytic.isoCoverGlued`: **so the gluing is that member**, up to isomorphism.

## What is not here

* **No converse.** Nothing says that a cover which glues to one member has all its overlaps `⊤`;
  a two-member cover of a space by two copies of itself along a proper open would be a
  counterexample if one existed on this line, and none is exhibited either way.
* **Nothing about the analytic structure.** `ComplexAnalytic.isoCoverGlued` is an isomorphism of
  locally ringed spaces, which is what `ComplexAnalytic.coverGlueData` produces;
  `ComplexAnalytic.coverAnalytification`'s `ComplexAnalytic.AnalyticSpace` structure is obtained
  from the same gluing, so the isomorphism transports along
  `ComplexAnalytic.coverAnalytification_toLocallyRingedSpace`, but no such transport is stated.
* **`ComplexAnalytic.surjective_base_eqToHom` is in the wrong file and is here on a price.** It is
  a fact about `AlgebraicGeometry.LocallyRingedSpace` and nothing else, and belongs beside
  `AlgebraicGeometry.LocallyRingedSpace.homeoOfIso` in
  `Oka/Geometry/RingedSpace/LocallyRingedSpace.lean`. **At `3187978`** that file has **210**
  downstream modules in this repository against **95** for this one — a reverse walk of the
  `import` lines with `scripts/import_cost.py`'s `IMPORT` pattern over its nesting-aware
  `strip_comments`, over the tracked `.lean` files of the repository at that commit, with the
  aggregator `Oka.lean` — which imports every module of the library, and so is downstream of
  every one of them — excluded from the two counts rather than from the graph — so putting a
  three-line helper there costs about a hundred and fifteen
  extra module rebuilds. Moving it is a follow-up and this docstring is the record that it is owed.

  **That clause read *"That file has **175 downstream modules** in this repository against **86**
  for a new module under `Oka/Analytification/`, measured by a reverse walk of the `import` lines,
  so putting a three-line helper there costs about ninety extra module rebuilds"* until
  2026-09-07**, and both figures were exact when they were taken: **175** at `1b13678`, the commit
  `8f1b040` was written on top of, and **86** at `8f1b040` itself, which is the commit that added
  this file — the first measured at that push's base and the second at its head, and the sentence
  pinned neither. **An unpinned count over
  the whole import graph is falsifiable by any push that adds a module**, which is what happened;
  what does not move is the ordering the argument rests on, and that is the reason the helper stays
  here rather than the numeral.
* **No scheme, no `admissible`, and no comparison functor**, as in the files this one sits beside.
-/

open CategoryTheory AlgebraicGeometry

universe u

namespace ComplexAnalytic

noncomputable section

/-- **The underlying map of an `eqToHom` of locally ringed spaces is surjective.**

It is the identity after the equality is substituted. Stated because
`ComplexAnalytic.f_coverGlueData_of_ne` produces one and surjectivity of a composite needs it;
`AlgebraicGeometry.LocallyRingedSpace.homeoOfIso` is the fact this is a special case of, and this
declaration belongs beside it — see this file's `## What is not here` for why it is here. -/
theorem surjective_base_eqToHom {A B : LocallyRingedSpace.{u}} (e : A = B) :
    Function.Surjective (eqToHom e).base := by
  subst e
  rw [eqToHom_refl]
  intro y
  exact ⟨y, rfl⟩

variable {J : Type u} (obj : J → Presentation.{u})
  (poly : ∀ i : J, J → MvPolynomial (ULift.{u} (Fin (obj i).n)) ℂ)
  (glue : ∀ i j : J, coverOverlap.{u} obj poly i j ≅ coverOverlap.{u} obj poly j i)
  (hrange : ∀ i j k : J, i ≠ j → i ≠ k → j ≠ k →
    Set.range (coverTripleIncl.{u} obj poly i j k ≫
        coverTransitionHom.{u} obj poly glue i j).base ⊆
      (coverOpen.{u} obj poly j k : Set (coverSpace.{u} obj j)))
  (hsymm : ∀ i j : J, glue j i = (glue i j).symm)
  (hcocycle : ∀ i j k : J, ∀ hij : i ≠ j, ∀ hik : i ≠ k, ∀ hjk : j ≠ k,
    coverTriple.{u} obj poly glue hrange i j k hij hik hjk ≫
      coverTriple.{u} obj poly glue hrange j k i hjk hij.symm hik.symm ≫
      coverTriple.{u} obj poly glue hrange k i j hik.symm hjk.symm hij = 𝟙 _)

/-! ### The inclusion of an overlap into a member -/

/-- **The inclusion of an overlap into a member is `ComplexAnalytic.coverIncl` after an
`eqToHom`**, off the diagonal.

`CategoryTheory.GlueData.ofGlueData'_f_of_ne` at `ComplexAnalytic.coverGlueData'`, and the
`eqToHom` is there because `CategoryTheory.GlueData.ofGlueData'` fills the diagonal with the
member itself, so its `V` is a `dite`.

**The `CategoryTheory.GlueData'` is left as `_` and the elaborator solves it from the goal.**
A statement of `CategoryTheory.GlueData'.f'` would have to name it, since an index there would be
checked against a projection of a metavariable; that difficulty is at that position and not at this
one. This applies to a **refined** datum as well, since `ComplexAnalytic.refineDatumGlueData` is
`ComplexAnalytic.coverGlueData` at the refined arguments. -/
theorem f_coverGlueData_of_ne {i j : J} (hij : i ≠ j) :
    (coverGlueData.{u} obj poly glue hrange hsymm hcocycle).toGlueData.f i j =
      eqToHom (dif_neg hij) ≫ coverIncl.{u} obj poly i j :=
  CategoryTheory.GlueData.ofGlueData'_f_of_ne _ hij

/-- **And it is surjective exactly where the overlap is the whole member.**

`AlgebraicGeometry.LocallyRingedSpace.range_ofRestrict` says the image of
`ComplexAnalytic.coverIncl` is the overlap; the hypothesis makes that the whole space, and
`ComplexAnalytic.surjective_base_eqToHom` handles the factor in front. -/
theorem surjective_f_coverGlueData
    (htop : ∀ i j : J, i ≠ j → coverOpen.{u} obj poly i j = ⊤) {i j : J} (hij : i ≠ j) :
    Function.Surjective
      ((coverGlueData.{u} obj poly glue hrange hsymm hcocycle).toGlueData.f i j).base := by
  have hincl : Function.Surjective (coverIncl.{u} obj poly i j).base := by
    intro y
    have hy : y ∈ Set.range (coverIncl.{u} obj poly i j).base := by
      rw [LocallyRingedSpace.range_ofRestrict, htop i j hij]
      trivial
    exact hy
  rw [f_coverGlueData_of_ne obj poly glue hrange hsymm hcocycle hij, LocallyRingedSpace.comp_base]
  exact hincl.comp (surjective_base_eqToHom _)

/-! ### The gluing is then one member -/

/-- **Each member's inclusion into the gluing is surjective**, when every off-diagonal overlap is
the whole member.

`AlgebraicGeometry.LocallyRingedSpace.GlueData.ι_jointly_surjective` puts an arbitrary point of
the gluing in some member `j`; if `j = i` there is nothing to do, and otherwise the point is
`f j i` of some `z'` by the theorem above, and `t j i` carries `z'` to a point of the `i`-`j`
overlap whose two images are related by
`AlgebraicGeometry.LocallyRingedSpace.GlueData.ι_eq_iff`. The step that makes the second
component come out is `CategoryTheory.GlueData.t_inv`, which undoes the transition. -/
theorem surjective_ι_coverGlueData
    (htop : ∀ i j : J, i ≠ j → coverOpen.{u} obj poly i j = ⊤) (i : J) :
    Function.Surjective
      ((coverGlueData.{u} obj poly glue hrange hsymm hcocycle).toGlueData.ι i).base := by
  set D := coverGlueData.{u} obj poly glue hrange hsymm hcocycle with hD
  intro p
  obtain ⟨j, y, rfl⟩ := D.ι_jointly_surjective p
  by_cases hij : i = j
  · subst hij
    exact ⟨y, rfl⟩
  · obtain ⟨z', hz'⟩ := surjective_f_coverGlueData obj poly glue hrange hsymm hcocycle htop
      (Ne.symm hij) y
    refine ⟨(D.toGlueData.f i j).base ((D.toGlueData.t j i).base z'), ?_⟩
    rw [LocallyRingedSpace.GlueData.ι_eq_iff]
    refine ⟨(D.toGlueData.t j i).base z', rfl, ?_⟩
    rw [LocallyRingedSpace.comp_base]
    change (D.toGlueData.f j i).base
      ((D.toGlueData.t i j).base ((D.toGlueData.t j i).base z')) = y
    have h : (D.toGlueData.t i j).base ((D.toGlueData.t j i).base z') = z' := by
      rw [← ConcreteCategory.comp_apply, ← LocallyRingedSpace.comp_base, D.toGlueData.t_inv j i]
      simp
    rw [h, hz']

/-- **So the gluing is one member.**

`AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.isoOfRangeEq` against the identity: the
member's inclusion is an open immersion at every cover datum
(`ComplexAnalytic.coverGlueData_ι_isOpenImmersion`) and the theorem above makes its image the
whole gluing. -/
def isoCoverGlued
    (htop : ∀ i j : J, i ≠ j → coverOpen.{u} obj poly i j = ⊤) (i : J) :
    (coverGlueData.{u} obj poly glue hrange hsymm hcocycle).toGlueData.U i ≅
      (coverGlueData.{u} obj poly glue hrange hsymm hcocycle).toGlueData.glued :=
  LocallyRingedSpace.IsOpenImmersion.isoOfRangeEq
    ((coverGlueData.{u} obj poly glue hrange hsymm hcocycle).toGlueData.ι i) (𝟙 _)
    ((surjective_ι_coverGlueData obj poly glue hrange hsymm hcocycle htop i).range_eq.trans
      (Set.range_eq_univ.2 (fun y ↦ ⟨y, rfl⟩)).symm)

end

end ComplexAnalytic
