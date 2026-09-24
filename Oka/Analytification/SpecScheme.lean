/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Analytification.SpecAffineCover

/-!
# `X` is a scheme

`Oka/Analytification/SpecAffineCover.lean` glues the members' `Spec`s into a locally ringed space
`ComplexAnalytic.specGlued`. This file says that space is a scheme, and that each member is an
**affine open** of it.

## Why this file exists, and it is a repaired cost estimate rather than a new idea

That the gluing is a scheme is not news — a gluing of affine schemes along opens is of course one.
What was here until this file is a *price*, in `Oka/Analytification/SpecAffineCover.lean`'s
`## What is not here`: that saying so needs `AlgebraicGeometry.Scheme.GlueData` and *"is not
free"*. **Both halves are measured false and that bullet has been repaired.**

* **It needs `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.scheme`**, the criterion that a
  locally ringed space covered by opens isomorphic to spectra is a scheme, and not
  `AlgebraicGeometry.Scheme.GlueData`, which would mean rebuilding `t`, `t'`, `t_fac`, `t_inv` and
  `cocycle` at the scheme level. The criterion consumes
  `AlgebraicGeometry.LocallyRingedSpace.GlueData.ι_jointly_surjective` and
  `ComplexAnalytic.isOpenImmersion_specIota`, both of which that file already has and the second
  of which it already states. Mathlib builds `AlgebraicGeometry.Scheme.GlueData.gluedScheme` this
  way too, so the cheaper route is the one the expensive object is made of.
* **The whole file is six declarations and no new import.** `Mathlib.AlgebraicGeometry.AffineScheme`
  and `Mathlib.AlgebraicGeometry.Gluing` were already in `Oka`'s closure, through
  `Mathlib.AlgebraicGeometry.Noetherian` and `Mathlib.AlgebraicGeometry.AffineSpace`; the import
  graph gains one edge, this file's own, and no Mathlib edge at all.

## A module of its own, and the reason is the sentence it repairs

Ten module docstrings in this line of files say, in one form or another, *"there is no
`AlgebraicGeometry.Scheme` in **this** file"*, and most of them defer for the reason to
`Oka/Analytification/Comparison.lean`'s titled section, which is about *that* file's statements.
Appending the six declarations below to `Oka/Analytification/SpecAffineCover.lean` costs no module
and would falsify the subject of that file's own bullet — which is to say it would move a
statement ten other files point at. **Putting them here leaves every one of those ten true
verbatim**, and it makes the property they assert enforced by the import graph rather than by
prose: a file that wants a scheme has to import `Oka.Analytification.SpecScheme`, and at
`3187978` **two** modules under `Oka/Analytification/` do —
`Oka/Analytification/SpecTwoData.lean` and `Oka/Analytification/SpecRefinedMember.lean` — beside
the aggregator `Oka.lean`, which imports every module of the library and is excluded from every
question of this shape.

**That clause ended *"and nothing in `Oka/Analytification/` does"* until 2026-09-07.** It was true
at `a421e49`, the commit that wrote it, where `Oka.lean` was this file's only importer, and it has
been false since `41b78dc` the next day, which gave `Oka/Analytification/SpecTwoData.lean` an import
of this file; `a711e47`, the same day, added `Oka/Analytification/SpecRefinedMember.lean` as a
second. **What the sentence got wrong is the count of importers and not the argument**, which
is about where the six declarations below *live*: they are here, and a file that wants the scheme
still has to take the edge. The instrument is one reverse edge of the import graph, read with
`scripts/import_cost.py`'s `IMPORT` pattern over its nesting-aware `strip_comments` — no closure
walk and no grep.

The four claims that were about the *line of files* rather than about
one file are falsified either way, and have been repaired in this same change.

**The numeral is scoped to this line and a fifth claim of the same shape sat outside it.**
`Oka/AnalyticSpace/FiniteEtaleOver.lean` said the line of files this one is on has no scheme, and
was repaired on 2026-09-02 rather than here. **The sweep that made the count above could not have
seen it, and this change is why that has to be said in the past tense**: at `74bffec` the phrase
there straddled a hard line break, so `grep "line of files does not have"` returned nothing and so
did `git log -S` on it. The repair un-wraps the phrase and quotes it whole, so from this commit on
both commands do find it — this paragraph included, since a pattern written into the tree it
searches joins the corpus it is searching. Normalise whitespace before believing a census of a
wrapped phrase, and pin a negative grep to the commit it was run at, because the repair it
motivates is what falsifies it.

The counter-argument is real and is recorded rather than dismissed:
`Oka/Analytification/SpecAffineCover.lean` is where the glue datum is, six declarations is a small
module, and this repository does not otherwise split a file at this size. It was decided on the
prose and not on the line count.

## Four spellings, recorded so they are not paid twice

1. **`AlgebraicGeometry.Scheme.Hom` is a one-field structure over an
   `AlgebraicGeometry.LocallyRingedSpace.Hom`**, so `AlgebraicGeometry.Scheme.Hom.mk` promotes
   `ComplexAnalytic.specIota` with no transport. That this typechecks at all is the fact that
   `(AlgebraicGeometry.Spec (CommRingCat.of (obj i).alg)).toLocallyRingedSpace` and
   `ComplexAnalytic.specSpace obj i` are **definitionally equal**: `ComplexAnalytic.specFunctor`
   sends a presentation to `AlgebraicGeometry.Spec.locallyRingedSpaceObj` of its algebra, and that
   is what `AlgebraicGeometry.Spec` is built from. **There is no `eqToHom` in this file.**
2. **`AlgebraicGeometry.IsOpenImmersion` for a `AlgebraicGeometry.Scheme.Hom` is *not* a one-field
   structure over the locally-ringed-space class**, and wrapping the hypothesis in an anonymous
   constructor fails: it unfolds to `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion` and asks
   for two explicit fields, the first of them a `Topology.IsOpenEmbedding`. Hand
   `ComplexAnalytic.isOpenImmersion_specIota` over bare and it is accepted.
3. **`AlgebraicGeometry.isAffineOpen_opensRange` needs `AlgebraicGeometry.IsAffine` on the
   *source*,** which instance search finds for a spectrum. That is the step turning "the member is
   an open immersion" into "the member is an **affine open**", and it is one term.
4. **`ComplexAnalytic.specGlueData_ι_isOpenImmersion` exists for a reason that applies here too**:
   instance search does not unfold `ComplexAnalytic.specIota`, so the instance below is stated by
   hand rather than found. It is an `instance` and not a `theorem` because
   `AlgebraicGeometry.isAffineOpen_opensRange` is the consumer and it needs one.

## What the last result is for, and it is `Oka/Analytification/CoverIndependence.lean`'s blocker

That file says, of taxis #1107's fourth increment, that what a common refinement of two cover data
has to reproduce is a condition nobody had named — every pairwise overlap is a *distinguished*
open of each of the two members it lies in. The local form of that condition is
`AlgebraicGeometry.exists_basicOpen_le_affine_inter`, it was already in this repository's import
closure, and once the members are affine opens it applies with no work.
`ComplexAnalytic.exists_basicOpen_specSchemeIota_inter` below is that application.

**Read what it says and what it does not.** For two members of **one** cover datum, every point of
their overlap has a neighbourhood distinguished in both. That is the local statement a common
refinement is assembled from; it is **not** a common refinement, which needs two data and an
isomorphism of what they glue, a choice of such an open at every point, and the refined family
assembled into a cover datum with its three laws. None of those three is here, and when this
section was written none of them was anywhere. **The first two are now here in full and the third
is not here at all**, which is what this sentence said of all three.

**The first is `Oka/Analytification/SpecTwoData.lean`** — a member of a second datum is an affine
open of this scheme, and at an isomorphism of the two gluings every point has a neighbourhood
distinguished in a member of each. **The second is complete in two more steps.** That file's two
sections are not polynomials, and it prices that step rather than taking it;
`Oka/Analytification/SpecMemberSections.lean` takes it, so the pointwise statement is in the
vocabulary a cover datum is written in, and
`ComplexAnalytic.exists_family_mvPolynomial_basicOpen_specSchemeIotaMap`
(`Oka/Analytification/SpecMemberChoice.lean`) is the word *choice* in it — four functions on this
scheme, by `choose` and nothing else. **The third is still nowhere**: no `poly`, no `glue` and no
law, and the family just named is indexed by the **points** of this scheme, which is not a cover
datum's index type. **Its size is still unmeasured on this side**; the same assembly on the
analytic side is `Oka/Analytification/CrossMemberDatum.lean` and the
`Oka/Analytification/RefineDatum*.lean` files, and how much of that transfers here is not
something any statement in this repository answers.

## Main definitions

- `ComplexAnalytic.specScheme`: **`X`, as a scheme.**
- `ComplexAnalytic.specSchemeIota`: the `i`-th member's inclusion, as a morphism of schemes.

## Main results

- `ComplexAnalytic.specScheme_toLocallyRingedSpace`: **the underlying locally ringed space is the
  one that was glued**, by `rfl` — stated for the reason `ComplexAnalytic.specGlueData_U` is:
  without it the scheme is a well-typed object with no recorded relation to the space it is the
  promotion of.
- `ComplexAnalytic.isOpenImmersion_specSchemeIota`: the inclusions are open immersions of schemes.
- `ComplexAnalytic.isAffineOpen_specSchemeIota`: **each member is an affine open of `X`.**
- `ComplexAnalytic.exists_basicOpen_specSchemeIota_inter`: **every point of the overlap of two
  members lies in an open distinguished in both.**

## What is not here

* **No `AlgebraicGeometry.Scheme.GlueData`, and no scheme-level glue datum of any kind.** The
  gluing stays where it is, in `Oka/Analytification/SpecAffineCover.lean`, at the level of locally
  ringed spaces; this file promotes its output and nothing else. That is the whole of the
  measurement above.
* **Nothing about `Oka/Analytification/Comparison.lean`'s titled section, which is not falsified
  by this file.** That section says `AlgebraicGeometry.Scheme` appears in no statement *in that
  file* and that the inverse of `ComplexAnalytic.analytificationFunctor` on its essential image is
  never needed. Both stay true. This file uses `AlgebraicGeometry.Spec` as an *object* and not
  `AlgebraicGeometry.Spec` as a functor into schemes, so that file's *"is not needed, not that it
  is missing"* stands as written.
* **No common refinement**, and no part of one *here*. The scope of that is worth spelling,
  because the bullet said *"see the three unbuilt pieces above"* and one of them is now built:
  `Oka/Analytification/SpecTwoData.lean` has the first and the local half of the second, and this
  file is unchanged, so what survives is the file-scoped half and what was falsified is the word
  *unbuilt*. The third piece — the refined family as a cover datum with its three laws — is
  unbuilt in the repository as well as absent here.
* **Nothing on the analytic side.** `X^an` is glued from analytic spaces and is not a scheme;
  nothing here touches it, and no comparison morphism is restated at the scheme level.
* **No `AlgebraicGeometry.IsAffine`, `AlgebraicGeometry.IsSeparated` or any other property of
  `X`.** Affineness of the *members* is what
  `AlgebraicGeometry.exists_basicOpen_le_affine_inter` consumes, and it is what
  `ComplexAnalytic.isAffineOpen_specSchemeIota` supplies; `X` itself is a scheme and nothing more
  is claimed of it.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry

universe u

namespace ComplexAnalytic

noncomputable section

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

/-! ### The gluing, as a scheme -/

/-- **`X`, as a scheme.**

`AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.scheme` at
`ComplexAnalytic.specGlued`: every point lies in the image of some member, and each member is
`Spec` of the algebra that member presents, included by an open immersion. The two facts are
`AlgebraicGeometry.LocallyRingedSpace.GlueData.ι_jointly_surjective` and
`ComplexAnalytic.isOpenImmersion_specIota`, and neither is new here.

**No `AlgebraicGeometry.Scheme.GlueData`**, which is what this was priced at; see this file's
module docstring for what that would have cost and what this costs instead. -/
def specScheme : Scheme.{u} :=
  LocallyRingedSpace.IsOpenImmersion.scheme
    (specGlued.{u} obj poly glue hrange hsymm hcocycle) <| by
  intro x
  obtain ⟨i, y, rfl⟩ :=
    (specGlueData.{u} obj poly glue hrange hsymm hcocycle).ι_jointly_surjective x
  exact ⟨CommRingCat.of (obj i).alg, specIota.{u} obj poly glue hrange hsymm hcocycle i,
    ⟨y, rfl⟩, isOpenImmersion_specIota.{u} obj poly glue hrange hsymm hcocycle i⟩

/-- **The underlying locally ringed space of `X` is the one that was glued**, by `rfl`.

`AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.scheme` changes nothing but the bundling, so
this is definitional. Stated for the reason `ComplexAnalytic.specGlueData_U` is stated: without it
the scheme above is a well-typed object with no recorded relation to the space it is the promotion
of. -/
@[simp]
theorem specScheme_toLocallyRingedSpace :
    (specScheme.{u} obj poly glue hrange hsymm hcocycle).toLocallyRingedSpace =
      specGlued.{u} obj poly glue hrange hsymm hcocycle :=
  rfl

/-! ### The members, as affine opens -/

/-- **The `i`-th member's inclusion, as a morphism of schemes.**

`AlgebraicGeometry.Scheme.Hom` is a one-field structure over an
`AlgebraicGeometry.LocallyRingedSpace.Hom`, and the source of `ComplexAnalytic.specIota` is
definitionally the spectrum below, so this is `ComplexAnalytic.specIota` rebundled and there is no
`eqToHom` in it. -/
def specSchemeIota (i : J) :
    Spec (CommRingCat.of (obj i).alg) ⟶ specScheme.{u} obj poly glue hrange hsymm hcocycle :=
  Scheme.Hom.mk (specIota.{u} obj poly glue hrange hsymm hcocycle i)

/-- **The inclusions are open immersions of schemes.**

`ComplexAnalytic.isOpenImmersion_specIota`, handed over bare: `AlgebraicGeometry.IsOpenImmersion`
for a morphism of schemes is *not* a one-field structure over the locally-ringed-space class, and
an anonymous constructor around the same proof is rejected. An `instance` rather than a `theorem`
because `AlgebraicGeometry.isAffineOpen_opensRange` below is a consumer that needs one, and
because instance search does not unfold `ComplexAnalytic.specSchemeIota` to find it. -/
instance isOpenImmersion_specSchemeIota (i : J) :
    IsOpenImmersion (specSchemeIota.{u} obj poly glue hrange hsymm hcocycle i) :=
  isOpenImmersion_specIota.{u} obj poly glue hrange hsymm hcocycle i

/-- **The `i`-th member is an affine open of `X`.**

`AlgebraicGeometry.isAffineOpen_opensRange` at the instance above, whose
`AlgebraicGeometry.IsAffine` side condition is on the *source* and is found for a spectrum. This
is the step that turns the open
cover of `Oka/Analytification/SpecAffineCover.lean` into a cover by **affine** opens, and it is
what the last theorem of this file consumes. -/
theorem isAffineOpen_specSchemeIota (i : J) :
    IsAffineOpen (specSchemeIota.{u} obj poly glue hrange hsymm hcocycle i).opensRange :=
  isAffineOpen_opensRange _

/-! ### Overlaps are distinguished in both members, locally -/

/-- **Every point of the overlap of two members lies in an open distinguished in both of them.**

`AlgebraicGeometry.exists_basicOpen_le_affine_inter` at the two affine opens above. This is the
condition `Oka/Analytification/CoverIndependence.lean` names as what a common refinement of two
cover data has to reproduce, in its local form and for two members of **one** datum; the module
docstring says what a common refinement needs beyond it, and none of that is here. -/
theorem exists_basicOpen_specSchemeIota_inter (i j : J)
    (x : specScheme.{u} obj poly glue hrange hsymm hcocycle)
    (hx : x ∈ (specSchemeIota.{u} obj poly glue hrange hsymm hcocycle i).opensRange ⊓
      (specSchemeIota.{u} obj poly glue hrange hsymm hcocycle j).opensRange) :
    ∃ (f : Γ(specScheme.{u} obj poly glue hrange hsymm hcocycle,
        (specSchemeIota.{u} obj poly glue hrange hsymm hcocycle i).opensRange))
      (g : Γ(specScheme.{u} obj poly glue hrange hsymm hcocycle,
        (specSchemeIota.{u} obj poly glue hrange hsymm hcocycle j).opensRange)),
      (specScheme.{u} obj poly glue hrange hsymm hcocycle).basicOpen f =
        (specScheme.{u} obj poly glue hrange hsymm hcocycle).basicOpen g ∧
      x ∈ (specScheme.{u} obj poly glue hrange hsymm hcocycle).basicOpen f :=
  exists_basicOpen_le_affine_inter
    (isAffineOpen_specSchemeIota.{u} obj poly glue hrange hsymm hcocycle i)
    (isAffineOpen_specSchemeIota.{u} obj poly glue hrange hsymm hcocycle j) x hx

end

end ComplexAnalytic
