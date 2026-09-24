/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Analytification.AffineCover
import Oka.Analytification.SpecDistinguishedOpen

/-!
# The glue data of the members' `Spec`s

`Oka/Analytification/AffineCover.lean` glues the *analytifications* of a family of presentations
along distinguished opens into `X^an`. This file glues their **`Spec`s** along the same data into
`X`, over the same input and with nothing added to it.

It exists because `X` did not. `ComplexAnalytic.comm_coverGlueData` and
`AlgebraicGeometry.LocallyRingedSpace.GlueData.glueMorphisms` already produce a morphism out of
`X^an` into **any** locally ringed space, so the comparison morphism `X^an ⟶ X` was never blocked
on the gluing — it was blocked on there being a target at all. **On `dab084a`, the commit before
this file, the census below counted nine declarations, and every one of them was on the
analytic side or generic in the space:**

    grep -rnE "^(noncomputable )?(def|abbrev) [^ ]*([Gg]lue[Dd]ata|gluedCover)" Oka

**This file's two are the tenth and eleventh and are neither**, which is why the sentence is
pinned to a revision and written in the past: a present-tense census in the file that changes it
is false from the moment it merges, and `Oka/Analytification/AffineCover.lean`'s policy paragraph
has been repaired twice for the same reason. The filter is on *names* rather than result types, so
it counts more than the glue data a cover produces — which is the point: under no reading of it
did anything glue `Spec`s.

## The input is the analytic side's input, unchanged, and that is the point

The variables below are the same six as `Oka/Analytification/AffineCover.lean`'s: a family of
presentations, a polynomial for each ordered pair cutting out the overlap, an isomorphism of the
two presentations of each overlap, and the three hypotheses `hrange`, `hsymm`, `hcocycle`. **No
new datum is asked for and none of the analytic side's is dropped.** A caller who has built
`ComplexAnalytic.coverAnalytification` has, verbatim, what this file needs — except for `hrange`,
which is discussed in its own section below and is the one place the two sides genuinely differ.

## What this file is, measured rather than described

Every declaration here that has a counterpart in `Oka/Analytification/AffineCover.lean` is that
counterpart with `ComplexAnalytic.specFunctor` where that file has
`ComplexAnalytic.analytificationFunctor ⋙ ComplexAnalytic.AnalyticSpace.forgetToLocallyRingedSpace`.
The two places that is *not* a literal substitution are both simplifications and both worth
knowing:

* **`ComplexAnalytic.specOverlapIso` needs no `Functor.mapIso`.**
  `ComplexAnalytic.specLocalisationIso` is already an isomorphism of locally ringed spaces, where
  `ComplexAnalytic.localisationIso` is one of analytic spaces and has to be pushed through the
  forgetful functor.
* **`ComplexAnalytic.specGlueIso_symm` is one rewrite shorter and needs no `rfl`.**
  `ComplexAnalytic.coverGlueIso_symm` pushes through two functors and closes with a `rfl` that
  reconciles the two `Functor.mapIso_symm`s; one functor needs one.

**"That has a counterpart" is a real qualification and not a hedge**, and the two declarations it
excludes are the *last* two a reader would guess. `ComplexAnalytic.specGlued` and
`ComplexAnalytic.specIota` are a `AlgebraicGeometry.LocallyRingedSpace.GlueData`'s `glued` and
`ι` taken directly, where `ComplexAnalytic.coverAnalytification` and `ComplexAnalytic.coverIota`
go through `ComplexAnalytic.AnalyticSpace.ofGlueDataCLinear` and carry a `ℂ`-linearity proof.
Those two are counterparts in *purpose* and are not renames of each other, which is the whole of
why this file is shorter than the one it mirrors.

`ComplexAnalytic.range_specTransitionHom_subset` and
`ComplexAnalytic.range_comp_specTransitionHom_subset` were written on this side first and had no
analytic mirror when this file merged. They have one now — taxis #1239 added
`ComplexAnalytic.range_coverTransitionHom_subset` and its composite — and the section below says
what they are for.

**`ComplexAnalytic.specGlueData'`'s six fields are identical to
`ComplexAnalytic.coverGlueData'`'s, proofs included** — `t_fac`'s rewrite chain, `t_inv`'s
`simp only` list and `cocycle`'s `reassoc_of%` are the same text. Nothing analytic was ever in
them: they are statements about `AlgebraicGeometry.LocallyRingedSpace.restrict` and about
`Oka/CategoryTheory/GlueData.lean`.

## Half of `hrange` is a theorem and not a hypothesis, on **both** sides

The `hrange` hypothesis below asks that the transition from `i` to `j` carries the part of the
`i`-`j` overlap that also meets `k` into `D(f_jk)`, and
`Oka/Analytification/AffineCover.lean`'s hypothesis of the same name has the same shape.

**It asked for `D(f_jk) ⊓ D(f_ji)` when this file was written, and the second conjunct was free.**
`ComplexAnalytic.specTransitionHom` is defined as the transition followed by
`ComplexAnalytic.specIncl`, whose range *is* that open, so no composite ending in it can leave it
— that is `ComplexAnalytic.range_comp_specTransitionHom_subset` below, and
`ComplexAnalytic.specTriple` now supplies it with `Set.subset_inter` rather than asking a caller
for it. Only the surviving conjunct, that the overlap with `k` goes to the overlap with `k`, is a
condition on the input, and it is what `hcocycle` is about.

**Both sides were weakened together, by taxis #1239, and the symmetry is the reason.**
`Oka/Analytification/CoverComparison.lean` holds *both* glue data over one input and checks its
family against both; two hypotheses of the same shape are one thing for a caller to discharge
twice, and two of different shapes are two things.
The redundancy was identical on the analytic side, where `ComplexAnalytic.coverTransitionHom`
factors through `ComplexAnalytic.coverIncl` by the same definition, so weakening one without the
other would have made the pair *less* symmetric and not more.
`Oka/Analytification/AffineCover.lean` carries the mirror of each theorem below.

## The members are an admissible affine cover of `X`, and nothing had to be defined or proved

taxis #1107's headline is *"two **admissible** covers of a scheme give canonically isomorphic
analytifications"*, and three files in this line record `admissible` as a notion this repository
does not have. It has none, and it does not need one: for the analytification of a scheme locally
of finite type over `ℂ`, an admissible cover is an open cover by affine opens each of finite type
over `ℂ`, and **every one of those three parts was already a declaration** when the question was
asked. The heading says *or proved* because the first draft of this section proved the first
bullet again, next to `ComplexAnalytic.PresentedAlgebra`, having failed to find the instance that
had been discharging it since `ComplexAnalytic.toFGAlg` was written — the two arrived in one
commit, and the instance exists because that functor needs it.

* **Affine and of finite type over `ℂ`** — `ComplexAnalytic.finiteType_presentationAlg`: a
  `ComplexAnalytic.Presentation` is `n : ℕ` variables and `k : ℕ` relations, so the algebra it
  presents is a quotient of a polynomial ring in `n` of them and the instance is one term. The
  repository has a sharper form still, in the same file — `ComplexAnalytic.toFGAlg` is that
  instance read as a functor into the finite-type `ℂ`-algebras, and
  `ComplexAnalytic.instIsEquivalenceToFGAlg` says presentations *are* exactly those.
* **Open in `X`** — `ComplexAnalytic.isOpenImmersion_specIota` below.
* **Covering `X`** — `AlgebraicGeometry.LocallyRingedSpace.GlueData.ι_jointly_surjective`.

`ComplexAnalytic.specGluedOpenCover` below is the three packaged, and it is one term at
`AlgebraicGeometry.LocallyRingedSpace.GlueData.openCover`. **It is the only declaration
admissibility cost on this side**, and it is a packaging rather than a fact.

**What a cover datum asks *beyond* admissibility is the thing worth carrying away, and nobody had
named it.** `ComplexAnalytic.specOpen obj poly i j` is `ComplexAnalytic.specLocalisationOpen` —
the **distinguished** open `D(f_ij)` of the `i`-th member — and `glue i j` identifies it with
`D(f_ji)` in the `j`-th. So the data forces every pairwise overlap to be a distinguished open of
*each* of the two members it lies in, which an affine cover of a scheme need not satisfy: `U ∩ V`
is not in general a basic open of either, and separatedness does not make it one. **That, and not
a definition of `admissible`, is what a common refinement of two data has to reproduce**, and
`Oka/Analytification/CoverRefinement.lean` builds refinements by distinguished opens of one fixed
member only. Nothing here is about two data at once; taxis #1329 has the measurement.

## Main definitions

- `ComplexAnalytic.specSpace`, `ComplexAnalytic.specOpen`, `ComplexAnalytic.specPart`,
  `ComplexAnalytic.specIncl`: the `i`-th member `Spec A_i`, the basic open `D(f_ij)` in it, that
  open as a space, and its inclusion — the `U`, `V` and `f` of a glue datum.
- `ComplexAnalytic.specOverlapIso`: `Spec` of the presented overlap is that open subspace.
- `ComplexAnalytic.specTransition`: **the transition `Spec A_i|D(f_ij) ≅ Spec A_j|D(f_ji)`**, the
  only place the input's algebraic content is used.
- `ComplexAnalytic.specTriple`: the transition on triple overlaps.
- `ComplexAnalytic.specGlueData'` and `ComplexAnalytic.specGlueData`: **the glue data of the
  members' `Spec`s**, which is what this file exists for.
- `ComplexAnalytic.specGlued` and `ComplexAnalytic.specIota`: the glued locally ringed space `X`
  and the `i`-th member's inclusion into it.
- `ComplexAnalytic.specGluedOpenCover`: **the members, as an open cover of `X`** — the
  counterpart of `ComplexAnalytic.coverAnalytificationOpenCover`.

## Main results

- `ComplexAnalytic.specGlueIso_symm`: the transitions are inverse to each other.
- `ComplexAnalytic.specTriple_fac`: `ComplexAnalytic.specTriple` is a morphism over the ambient
  member, which is the only property of it anything consumes.
- `ComplexAnalytic.range_specTransitionHom_subset` and
  `ComplexAnalytic.range_comp_specTransitionHom_subset`: **the transition into the ambient member
  cannot leave `D(f_ji)`**, whatever the input is — the half of the range condition that is a
  theorem, and `ComplexAnalytic.specTriple` is what consumes the second of the two.
- `ComplexAnalytic.specGlueData_U`: the members of the glue datum are the `Spec`s one put in.
- `ComplexAnalytic.isOpenImmersion_specIota`: **each member is an open subspace of `X`**, which
  together with `AlgebraicGeometry.LocallyRingedSpace.GlueData.ι_jointly_surjective` is the
  statement that the construction is a *cover*.
- `ComplexAnalytic.specGluedOpenCover_obj` and `ComplexAnalytic.specGluedOpenCover_map`: **that
  cover is by the members one started from, mapped by the inclusions above** — both `rfl`, and
  without them the definition above is a cover of a gluing by objects of a glue datum.
- `ComplexAnalytic.specIncl_comp_specIota`: **the inclusions agree over the overlaps**, in the
  vocabulary the input is written in rather than in `CategoryTheory.GlueData.ofGlueData'`'s. This
  is the statement taxis #1105 consumes, and it is the one thing here that a construction ignoring
  its input could not satisfy.

## What is not here

* **The comparison morphism `X^an ⟶ X`.** It is in
  `Oka/Analytification/CoverComparison.lean`, which imports this file, and it is built out of
  exactly what this bullet predicted before that file existed:
  `ComplexAnalytic.comm_coverGlueData` at the family
  `fun i ↦ analytificationToSpec (obj i).g ≫ specIota i`, whose overlap hypothesis is
  `ComplexAnalytic.specIncl_comp_specIota` composed with the naturality of
  `ComplexAnalytic.analytificationToSpecNatTrans`. It is not here because that file needs both
  gluings and this one is only half of the input.
* **Any statement that `X` is a scheme — it is in `Oka/Analytification/SpecScheme.lean`, which
  imports this file.** `ComplexAnalytic.specFunctor` lands in
  `AlgebraicGeometry.LocallyRingedSpace`, so the gluing below is a locally ringed space and
  nothing below mentions a scheme; `Oka/Analytification/Comparison.lean` argues in a titled
  section that the absence of `AlgebraicGeometry.Scheme` from *its* statements is a result rather
  than an omission, and that section is about that file and is untouched by this one.

  **Until 2026-09-02 this bullet also priced the statement, and the price was wrong in both
  halves.** It said saying so *"needs `AlgebraicGeometry.Scheme.GlueData` and is not free, and no
  consumer has asked for it"*. It needs
  `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.scheme`, which consumes
  `AlgebraicGeometry.LocallyRingedSpace.GlueData.ι_jointly_surjective` and
  `ComplexAnalytic.isOpenImmersion_specIota` — both of them below — where
  `AlgebraicGeometry.Scheme.GlueData` would mean rebuilding this file's `t`, `t'`, `t_fac`,
  `t_inv` and `cocycle` at the scheme level. It cost six declarations and no new import, and what
  had asked for it is taxis #1107's fourth increment, in
  `Oka/Analytification/CoverIndependence.lean`. **This sentence said that file "is the consumer"
  and named the condition it wants without a qualifier the same push states twice elsewhere; both
  were repaired on 2026-09-02.** What that Mathlib statement is,
  `AlgebraicGeometry.exists_basicOpen_le_affine_inter`, is the **local form** of the condition —
  it is stated at a *point* of the overlap of two affine opens and returns an open distinguished
  in both through that point, where the condition asks that the overlap *be* a distinguished open
  of each member — so it is **strictly weaker**, as
  `Oka/Analytification/SpecScheme.lean` and `Oka/Analytification/CoverIndependence.lean` both say.
  It applies once the members are affine opens and is
  `ComplexAnalytic.exists_basicOpen_specSchemeIota_inter` there. **That theorem now has a Lean
  consumer and this clause used to say it had none.**
  `ComplexAnalytic.exists_mvPolynomial_basicOpen_specSchemeIota_inter`
  (`Oka/Analytification/SpecMemberSections.lean`) restates it with polynomials in the two members'
  own variables, and its proof term reads this one. **What that consumer does not do is the thing
  this bullet is about**: it moves the local form into the vocabulary a cover datum is written in
  and builds no refinement, so what asked for the condition is still a deliverable and not a proof
  term.

  **A separate module rather than the end of this file, and the reason is this bullet**: ten
  docstrings on this line say there is no `AlgebraicGeometry.Scheme` in *their* file, so keeping
  the scheme out of this one leaves all ten true verbatim and makes the property an import-graph
  fact rather than a prose one. `Oka/Analytification/SpecScheme.lean` records the counter-argument.
* **No input exhibited, and so no non-vacuity of the *input*.** As in
  `Oka/Analytification/AffineCover.lean`, nothing here builds a family. What *is*
  ruled out is a degenerate *output*: `ComplexAnalytic.specIncl_comp_specIota` is false of a
  construction that ignores the transitions.
* **Any comparison between `ComplexAnalytic.specOpen` and `ComplexAnalytic.coverOpen`.** One is a
  basic open of a spectrum and the other a non-vanishing locus in an analytic space; that the
  comparison morphism carries the second into the first is a statement about the cover and belongs
  wherever that morphism is built. `Oka/Analytification/SpecDistinguishedOpen.lean` makes the same
  point about the affine case in its own docstring.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry

universe u

namespace ComplexAnalytic

noncomputable section

variable {J : Type u} (obj : J → Presentation.{u})
  (poly : ∀ i : J, J → MvPolynomial (ULift.{u} (Fin (obj i).n)) ℂ)

/-! ### The members of the cover and their overlaps -/

/-- **The `i`-th member of the cover**, `Spec A_i`, as a locally ringed space.

`ComplexAnalytic.specFunctor` lands in `AlgebraicGeometry.LocallyRingedSpace` already, so unlike
`ComplexAnalytic.coverSpace` this needs no forgetful functor and the whole file works at one
level. -/
abbrev specSpace (i : J) : LocallyRingedSpace.{u} :=
  specFunctor.{u}.obj (obj i)

/-- **The part of the `i`-th member that meets the `j`-th**, as an open subset: `D(f_ij)`.

The counterpart of `ComplexAnalytic.coverOpen`, at `ComplexAnalytic.specLocalisationOpen`. -/
abbrev specOpen (i j : J) : Opens (specSpace.{u} obj i) :=
  specLocalisationOpen.{u} (obj i).g (poly i j)

/-- **That open, as a space** — the object a glue data calls `V (i, j)`. -/
abbrev specPart (i j : J) : LocallyRingedSpace.{u} :=
  (specSpace.{u} obj i).restrict (specOpen.{u} obj poly i j).isOpenEmbedding

/-- **Its inclusion into the `i`-th member** — the morphism a glue data calls `f i j`, and the one
its `f_open` field is about. -/
abbrev specIncl (i j : J) : specPart.{u} obj poly i j ⟶ specSpace.{u} obj i :=
  (specSpace.{u} obj i).ofRestrict (specOpen.{u} obj poly i j).isOpenEmbedding

/-- **`Spec` of the presentation of the overlap**, `Spec ((A_i)_{f_ij})`.

The presentation itself is `ComplexAnalytic.coverOverlap`, shared with
`Oka/Analytification/AffineCover.lean` and not restated: the *input* to the two constructions is
one family of presentations, and only the functor applied to it differs. -/
abbrev specOverlapSpace (i j : J) : LocallyRingedSpace.{u} :=
  specFunctor.{u}.obj (coverOverlap.{u} obj poly i j)

/-- **`ComplexAnalytic.specLocalisationIso` in this file's vocabulary**: `Spec` of `(A_i)_{f_ij}`
is the open subspace `D(f_ij)` of `Spec A_i`.

The counterpart of `ComplexAnalytic.coverOverlapIso`, and **it needs no `Functor.mapIso`** —
`ComplexAnalytic.specLocalisationIso` is an isomorphism of locally ringed spaces already, where
`ComplexAnalytic.localisationIso` is one of analytic spaces. Named as a definition of its own for
the reason the analytic side gives: the three-term `Iso.trans` below unifies its intermediate
objects, and doing that against the *body* of a composite rather than a declared type is what
exhausts the heartbeat budget. -/
def specOverlapIso (i j : J) :
    specOverlapSpace.{u} obj poly i j ≅ specPart.{u} obj poly i j :=
  specLocalisationIso.{u} (obj i).g (poly i j)

variable (glue : ∀ i j : J, coverOverlap.{u} obj poly i j ≅ coverOverlap.{u} obj poly j i)

/-- **The given isomorphism of presentations, under `ComplexAnalytic.specFunctor`.** Named for the
same reason as `ComplexAnalytic.specOverlapIso`. -/
def specGlueIso (i j : J) :
    specOverlapSpace.{u} obj poly i j ≅ specOverlapSpace.{u} obj poly j i :=
  specFunctor.{u}.mapIso (glue i j)

/-- **The transition isomorphism `Spec A_i|D(f_ij) ≅ Spec A_j|D(f_ji)`** — the morphism a glue
data calls `t i j`.

It is the given algebra isomorphism read through `ComplexAnalytic.specLocalisationIso` at each
end. This is the only place the input's algebraic content is used, and it is why this file needs
`Oka/Analytification/SpecDistinguishedOpen.lean` rather than only
`Oka/Analytification/Comparison.lean`. -/
def specTransition (i j : J) : specPart.{u} obj poly i j ≅ specPart.{u} obj poly j i :=
  (specOverlapIso.{u} obj poly i j).symm ≪≫ specGlueIso.{u} obj poly glue i j ≪≫
    specOverlapIso.{u} obj poly j i

/-- **The transition, followed into the ambient `j`-th member.** This is the morphism the range
hypothesis below is about: where the overlap of `i` and `j` goes inside `Spec A_j`. -/
def specTransitionHom (i j : J) : specPart.{u} obj poly i j ⟶ specSpace.{u} obj j :=
  (specTransition.{u} obj poly glue i j).hom ≫ specIncl.{u} obj poly j i

/-- **The transition isomorphisms are inverse to each other**, provided the input isomorphisms are.

`Functor.mapIso` commutes with `Iso.symm` **once**, where
`ComplexAnalytic.coverGlueIso_symm` needs it twice and a `rfl` to reconcile them: that file pushes
through `ComplexAnalytic.analytificationFunctor` and then
`ComplexAnalytic.AnalyticSpace.forgetToLocallyRingedSpace`, and this one through
`ComplexAnalytic.specFunctor` alone. -/
theorem specGlueIso_symm (hsymm : ∀ i j : J, glue j i = (glue i j).symm) (i j : J) :
    specGlueIso.{u} obj poly glue j i = (specGlueIso.{u} obj poly glue i j).symm := by
  rw [specGlueIso, specGlueIso, hsymm i j, Functor.mapIso_symm]

/-! ### The range hypothesis, half of which is free -/

/-- **The transition into the ambient member lands in `D(f_ji)`**, whatever the input is.

`ComplexAnalytic.specTransitionHom` is a composite ending in `ComplexAnalytic.specIncl`, whose
range is that open by `AlgebraicGeometry.LocallyRingedSpace.range_ofRestrict`. Nothing about the
input enters. -/
theorem range_specTransitionHom_subset (i j : J) :
    Set.range (specTransitionHom.{u} obj poly glue i j).base ⊆
      (specOpen.{u} obj poly j i : Set (specSpace.{u} obj j)) := by
  rw [specTransitionHom, LocallyRingedSpace.comp_base, TopCat.coe_comp, Set.range_comp]
  refine subset_trans (Set.image_subset_range _ _) ?_
  exact ((specSpace.{u} obj j).range_ofRestrict (specOpen.{u} obj poly j i)).le

/-! ### Triple overlaps -/

/-- **The triple overlap `D(f_ij) ⊓ D(f_ik)` inside the `i`-th member**, as a space. -/
abbrev specTriplePart (i j k : J) : LocallyRingedSpace.{u} :=
  (specSpace.{u} obj i).restrict
    (specOpen.{u} obj poly i j ⊓ specOpen.{u} obj poly i k).isOpenEmbedding

/-- **The inclusion of the triple overlap into the double overlap of `i` and `j`.** -/
abbrev specTripleIncl (i j k : J) :
    specTriplePart.{u} obj poly i j k ⟶ specPart.{u} obj poly i j :=
  (specSpace.{u} obj i).restrictLE (inf_le_left :
    specOpen.{u} obj poly i j ⊓ specOpen.{u} obj poly i k ≤ specOpen.{u} obj poly i j)

/-- **The second conjunct of the range hypothesis below is free**, restated at the composite the
hypothesis is actually about.

`ComplexAnalytic.range_specTransitionHom_subset` precomposed. So the content of `hrange` is the
*first* conjunct alone — that the part of the `i`-`j` overlap meeting `k` goes to the part of the
`j`-`i` overlap meeting `k` — and the same is true of
`Oka/Analytification/AffineCover.lean`'s hypothesis for the same reason. The hypothesis is
nevertheless stated in the analytic side's shape; this file's module docstring argues why. -/
theorem range_comp_specTransitionHom_subset (i j k : J) :
    Set.range (specTripleIncl.{u} obj poly i j k ≫
        specTransitionHom.{u} obj poly glue i j).base ⊆
      (specOpen.{u} obj poly j i : Set (specSpace.{u} obj j)) := by
  rw [LocallyRingedSpace.comp_base, TopCat.coe_comp, Set.range_comp]
  exact subset_trans (Set.image_subset_range _ _)
    (range_specTransitionHom_subset.{u} obj poly glue i j)

variable (hrange : ∀ i j k : J, i ≠ j → i ≠ k → j ≠ k →
  Set.range (specTripleIncl.{u} obj poly i j k ≫ specTransitionHom.{u} obj poly glue i j).base ⊆
    (specOpen.{u} obj poly j k : Set (specSpace.{u} obj j)))

/-- **The transition on triple overlaps**, `Spec A_i|(D(f_ij) ⊓ D(f_ik)) ⟶
Spec A_j|(D(f_jk) ⊓ D(f_ji))`.

This is `t'` before it is conjugated into the pullbacks. As on the analytic side, `hrange` and
`hcocycle` are what rule out two members being glued along an open without the gluings agreeing on
triple overlaps. -/
def specTriple (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    specTriplePart.{u} obj poly i j k ⟶ specTriplePart.{u} obj poly j k i :=
  LocallyRingedSpace.liftRestrict
    (specTripleIncl.{u} obj poly i j k ≫ specTransitionHom.{u} obj poly glue i j) _
    (Set.subset_inter (hrange i j k hij hik hjk)
      (range_comp_specTransitionHom_subset.{u} obj poly glue i j k))

/-- **`ComplexAnalytic.specTriple` is a morphism over the ambient member**, which is the only
property of it anything consumes. -/
@[reassoc (attr := simp)]
theorem specTriple_fac (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    specTriple.{u} obj poly glue hrange i j k hij hik hjk ≫
        (specSpace.{u} obj j).ofRestrict
          (specOpen.{u} obj poly j k ⊓ specOpen.{u} obj poly j i).isOpenEmbedding =
      specTripleIncl.{u} obj poly i j k ≫ specTransitionHom.{u} obj poly glue i j :=
  LocallyRingedSpace.liftRestrict_fac _ _ _

/-! ### The glue data -/

/-- **The glue data of the cover of `Spec`s, in the form that only asks for the overlaps when
`i ≠ j`.**

Every field is `ComplexAnalytic.coverGlueData'`'s, with the same proof: `t_fac`'s rewrite chain,
`t_inv`'s `simp only` list and `cocycle`'s `reassoc_of%` say nothing analytic and are statements
about `AlgebraicGeometry.LocallyRingedSpace.restrict` and `Oka/CategoryTheory/GlueData.lean`. Why
`t'` is conjugated by `AlgebraicGeometry.LocallyRingedSpace.restrictInfIsoPullback` at each end is
in `Oka/Analytification/AffineCover.lean`'s **module** docstring — *"it identifies
`pullback (f i j) (f i k)` with the open subspace `X_i|(D(f_ij) ⊓ D(f_ik))`, an object one can
name and restrict"*, and the two bullets after it — and **not** in
`Oka/CategoryTheory/GlueData.lean`'s, which never mentions that identification. -/
def specGlueData' (hsymm : ∀ i j : J, glue j i = (glue i j).symm)
    (hcocycle : ∀ i j k : J, ∀ hij : i ≠ j, ∀ hik : i ≠ k, ∀ hjk : j ≠ k,
      specTriple.{u} obj poly glue hrange i j k hij hik hjk ≫
        specTriple.{u} obj poly glue hrange j k i hjk hij.symm hik.symm ≫
        specTriple.{u} obj poly glue hrange k i j hik.symm hjk.symm hij = 𝟙 _) :
    GlueData' LocallyRingedSpace.{u} where
  J := J
  U := specSpace.{u} obj
  V i j _ := specPart.{u} obj poly i j
  f i j _ := specIncl.{u} obj poly i j
  t i j _ := (specTransition.{u} obj poly glue i j).hom
  t' i j k hij hik hjk :=
    ((specSpace.{u} obj i).restrictInfIsoPullback
      (specOpen.{u} obj poly i j) (specOpen.{u} obj poly i k)).inv ≫
      specTriple.{u} obj poly glue hrange i j k hij hik hjk ≫
      ((specSpace.{u} obj j).restrictInfIsoPullback
        (specOpen.{u} obj poly j k) (specOpen.{u} obj poly j i)).hom
  t_fac i j k hij hik hjk := by
    rw [Category.assoc, Category.assoc,
      LocallyRingedSpace.restrictInfIsoPullback_hom_snd, Iso.inv_comp_eq, ← Category.assoc,
      LocallyRingedSpace.restrictInfIsoPullback_hom_fst]
    refine LocallyRingedSpace.hom_ext_restrict _ _ _ ?_
    rw [Category.assoc, LocallyRingedSpace.restrictLE_fac, specTriple_fac]
    rfl
  t_inv i j _ := by
    simp only [specTransition, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      Iso.hom_inv_id_assoc, specGlueIso_symm.{u} obj poly glue hsymm i j, Iso.symm_hom,
      Iso.hom_inv_id_assoc, Iso.inv_hom_id]
  cocycle i j k hij hik hjk := by
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [reassoc_of% hcocycle i j k hij hik hjk, Iso.inv_hom_id]

/-- **The glue data of the members' `Spec`s.**

`CategoryTheory.GlueData.ofGlueData'` of `ComplexAnalytic.specGlueData'`, with `f_open` supplied by
`AlgebraicGeometry.LocallyRingedSpace.isOpenImmersion_f'`.

Which open-immersion fact this uses is the same choice `Oka/Analytification/AffineCover.lean`
records: `AlgebraicGeometry.LocallyRingedSpace.isOpenImmersion_ofRestrict`, **not**
`ComplexAnalytic.isOpenImmersion_specFunctor_map_localisationHom`. The two are the same fact at
the two spellings of the overlap — as the open subspace, and as `Spec` of the localisation — and
this file takes the first, because that is the spelling at which the range computations `t'` needs
are statements about `ComplexAnalytic.specOpen`. The algebraic description enters only through
`ComplexAnalytic.specTransition`. -/
def specGlueData (hsymm : ∀ i j : J, glue j i = (glue i j).symm)
    (hcocycle : ∀ i j k : J, ∀ hij : i ≠ j, ∀ hik : i ≠ k, ∀ hjk : j ≠ k,
      specTriple.{u} obj poly glue hrange i j k hij hik hjk ≫
        specTriple.{u} obj poly glue hrange j k i hjk hij.symm hik.symm ≫
        specTriple.{u} obj poly glue hrange k i j hik.symm hjk.symm hij = 𝟙 _) :
    LocallyRingedSpace.GlueData.{u} where
  toGlueData :=
    GlueData.ofGlueData' (specGlueData'.{u} obj poly glue hrange hsymm hcocycle)
  f_open i j :=
    LocallyRingedSpace.isOpenImmersion_f'
      (specGlueData'.{u} obj poly glue hrange hsymm hcocycle)
      (fun _ _ _ ↦ LocallyRingedSpace.isOpenImmersion_ofRestrict _ _) i j

variable (hsymm : ∀ i j : J, glue j i = (glue i j).symm)
  (hcocycle : ∀ i j k : J, ∀ hij : i ≠ j, ∀ hik : i ≠ k, ∀ hjk : j ≠ k,
    specTriple.{u} obj poly glue hrange i j k hij hik hjk ≫
      specTriple.{u} obj poly glue hrange j k i hjk hij.symm hik.symm ≫
      specTriple.{u} obj poly glue hrange k i j hik.symm hjk.symm hij = 𝟙 _)

/-- **The members of the glue data are the `Spec`s one put in.**

`rfl`, and stated for the reason `ComplexAnalytic.coverGlueData_U` is: without it the glue datum
is a well-typed object with no recorded relation to its input, since
`CategoryTheory.GlueData.ofGlueData'` has no projection lemmas in Mathlib —
`Oka/CategoryTheory/GlueData.lean` is where that is measured, with the version and the command.
**The clause carried the universal bare until 2026-09-21**, when taxis #2118 made it a
pointer. -/
@[simp]
theorem specGlueData_U (i : J) :
    (specGlueData.{u} obj poly glue hrange hsymm hcocycle).U i = specSpace.{u} obj i :=
  rfl

/-! ### The glued space and its members -/

/-- **`X`**, the locally ringed space glued from the members' `Spec`s.

There is no promotion step here and there is one on the analytic side: `X^an` has to be given an
analytic-space structure by `ComplexAnalytic.AnalyticSpace.ofGlueDataCLinear`, and about a hundred
lines of `Oka/Analytification/AffineCover.lean` exist to check the `ℂ`-linearity that needs. A
glue datum's gluing *is* a locally ringed space, so this is the object itself. -/
abbrev specGlued : LocallyRingedSpace.{u} :=
  (specGlueData.{u} obj poly glue hrange hsymm hcocycle).toGlueData.glued

/-- **The `i`-th member's inclusion into `X`.** -/
abbrev specIota (i : J) :
    specSpace.{u} obj i ⟶ specGlued.{u} obj poly glue hrange hsymm hcocycle :=
  (specGlueData.{u} obj poly glue hrange hsymm hcocycle).toGlueData.ι i

/-- **The members are open subspaces of `X`.**

`AlgebraicGeometry.LocallyRingedSpace.GlueData.ι_isOpenImmersion` at this glue datum. Stated at
the glue datum's own `ι` and then transported, because `inferInstance` **fails** at the
`ComplexAnalytic.specIota` spelling: instance search does not unfold the abbreviation, and the
same is true of `ComplexAnalytic.coverGlueData_ι_isOpenImmersion`, which is stated the same way. -/
theorem specGlueData_ι_isOpenImmersion (i : J) :
    LocallyRingedSpace.IsOpenImmersion
      ((specGlueData.{u} obj poly glue hrange hsymm hcocycle).toGlueData.ι i) :=
  inferInstance

/-- **`ComplexAnalytic.specIota` is an open immersion**, which together with
`AlgebraicGeometry.LocallyRingedSpace.GlueData.ι_jointly_surjective` says the `Spec`s one started
from are an open cover of `X`. -/
theorem isOpenImmersion_specIota (i : J) :
    LocallyRingedSpace.IsOpenImmersion (specIota.{u} obj poly glue hrange hsymm hcocycle i) :=
  specGlueData_ι_isOpenImmersion.{u} obj poly glue hrange hsymm hcocycle i

/-! ### The members as an open cover of `X` -/

/-- **The members are an open cover of `X`.**

`AlgebraicGeometry.LocallyRingedSpace.GlueData.openCover` at this glue datum, and it is the
counterpart of `ComplexAnalytic.coverAnalytificationOpenCover`, which
`Oka/Analytification/AffineCover.lean` has had since taxis #1105 and which this file did not.
As there, the two `rfl` lemmas below are what make it a cover *by the members one started from*
rather than a cover of a gluing by objects of a glue datum that happen to be them.

Noncomputable and non-canonical for the reason
`AlgebraicGeometry.LocallyRingedSpace.GlueData.openCover` is: the index of a point is *chosen*,
and nothing downstream depends on which. -/
noncomputable def specGluedOpenCover :
    LocallyRingedSpace.OpenCover.{u} (specGlued.{u} obj poly glue hrange hsymm hcocycle) :=
  (specGlueData.{u} obj poly glue hrange hsymm hcocycle).openCover

/-- **The `i`-th member of the cover is the `i`-th member's `Spec`**, by `rfl` —
`ComplexAnalytic.specGlueData_U` at the glue datum. -/
@[simp]
theorem specGluedOpenCover_obj (i : J) :
    (specGluedOpenCover.{u} obj poly glue hrange hsymm hcocycle).obj i = specSpace.{u} obj i :=
  rfl

/-- **The `i`-th map of the cover is `ComplexAnalytic.specIota`**, by `rfl`.

Stated against `ComplexAnalytic.specIota` rather than against
`(specGlueData …).toGlueData.ι`, which is the same choice
`ComplexAnalytic.isOpenImmersion_specIota` makes directly above and
`ComplexAnalytic.coverAnalytificationOpenCover_map` makes on the analytic side: a consumer of this
cover is working in the vocabulary the input was written in. -/
@[simp]
theorem specGluedOpenCover_map (i : J) :
    (specGluedOpenCover.{u} obj poly glue hrange hsymm hcocycle).map i =
      specIota.{u} obj poly glue hrange hsymm hcocycle i :=
  rfl

/-- **The inclusions agree over the overlaps**, stated in the vocabulary the input is written in.

This is the statement taxis #1105 consumes and **the one thing here a construction ignoring its
transitions could not satisfy**; every other result in this file is true of a glue datum that
threw its input away.

It is not `CategoryTheory.GlueData.glue_condition`, which is stated at
`CategoryTheory.GlueData.ofGlueData'`'s `f` and `t` and so carries the `dite`s that fill the
diagonal. `CategoryTheory.GlueData.comm_of_ofGlueData'_comm` is exactly the translation, and
`Oka/CategoryTheory/GlueData.lean`'s docstring says so: *"reading a glue datum's own
`CategoryTheory.GlueData.glue_condition` … back into the vocabulary a caller built the datum in".*
**Deriving it by hand instead runs into that file's documented `rw [Category.assoc]` failure**,
where the object positions carry unreduced `CategoryTheory.GlueData.ofGlueData'` projections. -/
theorem specIncl_comp_specIota (i j : J) (hij : i ≠ j) :
    specIncl.{u} obj poly i j ≫ specIota.{u} obj poly glue hrange hsymm hcocycle i =
      (specTransition.{u} obj poly glue i j).hom ≫ specIncl.{u} obj poly j i ≫
        specIota.{u} obj poly glue hrange hsymm hcocycle j :=
  CategoryTheory.GlueData.comm_of_ofGlueData'_comm _
    (fun i ↦ specIota.{u} obj poly glue hrange hsymm hcocycle i)
    (fun i j ↦ ((specGlueData.{u} obj poly glue hrange hsymm hcocycle).toGlueData.glue_condition
      i j).symm) hij

end

end ComplexAnalytic
