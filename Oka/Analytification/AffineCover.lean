/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Analytification.LocalisationFunctor
import Oka.AnalyticSpace.Glue
import Oka.CategoryTheory.GlueData

/-!
# The glue data of an affine cover with distinguished overlaps

`Oka/Analytification/DistinguishedOpen.lean` identifies the analytification of `A_f` with the
distinguished open `D(f) ⊆ X^an`, **over `X^an`**, and `Oka/AnalyticSpace/Glue.lean` glues an
analytic space out of an `AlgebraicGeometry.LocallyRingedSpace.GlueData` whose pieces are
analytic. This file is the step between them: from a family of presentations, a distinguished
open of each for every other member, and a `ℂ`-algebra isomorphism identifying the two
descriptions of each overlap, it builds the glue data.

## The input, and why it is presentations rather than a scheme

**Nothing here turns an `AlgebraicGeometry.Scheme` into the data below, and the obstruction is
the arity of `poly`.** The `variable` line below declares it as `∀ i : J, J → MvPolynomial …`:
for each *ordered pair*, one polynomial, hence **one** distinguished open of the `i`-th member.
A scheme supplies less. `AlgebraicGeometry.exists_basicOpen_le_affine_inter` is stated at a
*point* of `U ⊓ V` and returns an open distinguished in both that contains it, so the
intersection of two affine members is a **union** of such opens, and nothing makes one of them
the whole of it. That is a claim about this file's own input, and **only an edit to this file can
falsify it** — which is the property the sentence it replaces lacked. That one counted
occurrences of `Scheme` across the whole tree at `master` = `31f5a2f` and concluded that every
scheme here is a `Spec`; `Oka/AlgebraicGeometry/Modules/Coherent.lean` carries
`AlgebraicGeometry.Scheme.isCoherentStructureSheaf`, a theorem about an arbitrary scheme, and has
falsified it since fourteen and a half hours after this file landed.

**What is missing is the construction, not the sentence**, which that measurement also got wrong:
the target is sayable, and needs nothing from this repository. With
`AlgebraicGeometry.Scheme.Over` in scope for the structure morphism, so that `↘` names it, and
`AlgebraicGeometry.LocallyOfFiniteType` asserted of that morphism, a well-formed target is

    noncomputable def analytificationOfScheme (X : Scheme.{0})
        [X.Over (Spec (CommRingCat.of ℂ))]
        [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of ℂ))] :
        ComplexAnalytic.AnalyticSpace.{0}

— note the universe, which is forced to `0` because `ℂ : Type` makes `Spec (CommRingCat.of ℂ)` a
`Scheme.{0}`. Everything else on this line is `{u}`-polymorphic and the scheme-level statement
cannot be.

So what this file takes is the cover **as data**: an index type `J`, a
`ComplexAnalytic.Presentation` for each index, a polynomial `poly i j` cutting out the part of the
`i`-th member that meets the `j`-th, and an isomorphism of the two presentations of the overlap.
The **members** lose nothing by that: `ComplexAnalytic.toFGAlg` is an equivalence onto the
finitely generated `ℂ`-algebras (`ComplexAnalytic.instIsEquivalenceToFGAlg`), so each of them is
an affine scheme locally of finite type over `ℂ`, transported. The **overlaps** are where the
general form differs, by the paragraph above, and what it would add is a comparison theorem —
that every such scheme arises this way, or that a cover of one can be refined until it does —
together with a choice among Mathlib's cover APIs. Neither is needed by anything downstream.
`Oka/Analytification/Comparison.lean` argues separately, in a titled section, that the absence of
`Scheme` from *its* statements is a result rather than an omission.

Only the **distinguished** case appears, and the reason is this repository's machinery rather
than the shape of a scheme's cover. `Oka/Analytification/DistinguishedOpen.lean` analytifies the
distinguished open `D(f)` and nothing else, and says in its own docstring that the
analytification of a general open immersion is neither proved nor wanted; a distinguished open
is therefore the only overlap this file has anything to build a transition from. That a scheme's
pairwise intersections are merely *covered by* opens distinguished in both is true, and is what
makes one open per pair a **restriction** rather than what licenses it — the paragraph above
says that of `poly`'s arity, and the one below names the Mathlib shape that carries the weaker
datum.

Mathlib does have a shape that carries what a scheme supplies at an overlap, and it is not the one
below: a **locally directed** cover, `Mathlib/AlgebraicGeometry/Cover/Directed.lean`. It indexes
the members by a category, gives a transition morphism for each arrow, and asks only that every
point of a pairwise overlap be hit by a third member mapping into both — so overlaps are not
chosen at all, they are covered by other members of the same family.
`Mathlib/AlgebraicGeometry/Sites/SmallAffineZariski.lean` instantiates it for *every* scheme with
no hypotheses, indexed by the affine opens with an arrow `U ⟶ V` exactly when `U` is a
distinguished open of `V`, which is the data `Oka/Analytification/DistinguishedOpen.lean`
analytifies. Two things come with the shape and are the argument for it: the scheme is the colimit
of the family, and a morphism out of it glues from morphisms out of the members with compatibility
along the transition morphisms alone — no triple-overlap condition, where
`ComplexAnalytic.coverGlueData` below needs `hrange` and `hcocycle`. Adopting it here would
replace `poly`, `hrange` and `hcocycle` together, and would need the analytified transition
morphism to be functorial in composition of arrows, which is not in this repository. Nothing
downstream of this file needs any of it yet.

## The shape of the construction, and where the content is

The route is `CategoryTheory.GlueData'` — the variant that asks for the overlaps only when
`i ≠ j` — followed by `CategoryTheory.GlueData.ofGlueData'` and
`AlgebraicGeometry.LocallyRingedSpace.isOpenImmersion_f'` for the `f_open` field. `GlueData'`
discharges `f_id`, `t_id` and the three degenerate branches of `t'`, all of which are bookkeeping.

What is left is `t'` and the cocycle, and **the whole of the difficulty is that `t'` is a
morphism between categorical pullbacks**, which no tactic can compute with. That is what
`AlgebraicGeometry.LocallyRingedSpace.restrictInfIsoPullback` is for: it identifies
`pullback (f i j) (f i k)` with the open subspace `X_i|(D(f_ij) ⊓ D(f_ik))`, an object one can
name and restrict. With that identification:

* `t'` is `ComplexAnalytic.coverTriple` conjugated by two copies of it, and `t_fac` follows from
  the two factorisations of the identification together with the mono-ness of an open immersion;
* the **cocycle condition becomes exactly the hypothesis `hcocycle`**, because the conjugating
  isomorphisms cancel in pairs — the middle one of `t' i j k` is the same isomorphism as the
  first one of `t' j k i`, by construction.

So the two hypotheses this file asks the caller for, `hrange` and `hcocycle`, are statements
about morphisms of *open subspaces of the members*, which is the spelling a geometric input
arrives in and the one `Oka/Geometry/RingedSpace/PresheafedSpace/Gluing.lean`'s module docstring
argues for.

**And `hrange` asks for its content and no more.** The natural statement of it is a containment in
`D(f_jk) ⊓ D(f_ji)` — that is the open `ComplexAnalytic.coverTriplePart` restricts to, and it is
what `AlgebraicGeometry.LocallyRingedSpace.liftRestrict` consumes — but the `D(f_ji)` half of that
is a theorem. `ComplexAnalytic.coverTransitionHom` is *defined* as a composite ending in
`ComplexAnalytic.coverIncl`, whose range is exactly `D(f_ji)`, so nothing can land outside it
whatever the input is: `ComplexAnalytic.range_comp_coverTransitionHom_subset` proves it and
`ComplexAnalytic.coverTriple` supplies it with `Set.subset_inter`, leaving a caller the other half
alone. `Oka/Analytification/SpecAffineCover.lean`'s hypothesis of the same name was weakened
**together with this one, by taxis #1239**, and for the same reason:
`Oka/Analytification/CoverComparison.lean` holds both glue data over one input, and two hypotheses
of the same shape are one obligation discharged twice where two shapes are two.

## The diagonal

`poly` and `glue` are asked for at **every** pair, including `i = i`, but `hrange` and `hcocycle`
are required only at triples of *distinct* indices, which is all `CategoryTheory.GlueData'`
consumes. So the diagonal data is unused. It is not unconstrained: `hsymm` is quantified over
every pair and at `i = i` it says `glue i i = (glue i i).symm`, which a caller has to prove even
though nothing below reads it. That is weaker than `glue i i = Iso.refl` — it says only that the
transition is its own inverse — and `poly i i = 1` with `glue i i = Iso.refl` is the natural
choice, satisfies it, and is checked by nothing. Making `poly` partial instead would push a
`i ≠ j` argument through every definition below and into the type of every open subspace, which is
a much larger tax than one unused value per index.

## Main definitions

- `ComplexAnalytic.coverSpace`, `ComplexAnalytic.coverOpen`, `ComplexAnalytic.coverPart`: the
  `i`-th member `A_i^an`, the distinguished open `D(f_ij)` inside it, and that open as a space.
- `ComplexAnalytic.coverTransition`: the transition isomorphism `X_i|D(f_ij) ≅ X_j|D(f_ji)`,
  obtained from the given isomorphism of presentations by transporting it across
  `ComplexAnalytic.localisationIso` at each end.
- `ComplexAnalytic.coverTriple`: the transition on triple overlaps,
  `X_i|(D(f_ij) ⊓ D(f_ik)) ⟶ X_j|(D(f_jk) ⊓ D(f_ji))`, which is what `t'` is built from.
- `ComplexAnalytic.coverGlueData'` and `ComplexAnalytic.coverGlueData`: **the glue data.**
- `ComplexAnalytic.coverAnalytification`: **the analytic space the cover glues to** — the
  gluing of the members' analytifications, and the first declaration in this file that is an
  `ComplexAnalytic.AnalyticSpace` rather than a locally ringed space.
- `ComplexAnalytic.coverIota`: the `i`-th member's analytification, as a morphism of analytic
  spaces into it.
- `ComplexAnalytic.coverAnalytificationOpenCover`: **`X^an` as an open cover by them**, which is
  the form `ComplexAnalytic.AnalyticSpace.glueMorphisms` consumes.
- `ComplexAnalytic.coverGlueMorphisms`: **a morphism out of `X^an`**, glued from morphisms out of
  the members which agree over the overlaps.

## Main results

- `ComplexAnalytic.coverGlueData_U` and `ComplexAnalytic.coverGlueData_ι_isOpenImmersion`: the
  members of the glue data are the analytifications one put in, and they are open subspaces of
  the gluing. Without the first, `coverGlueData` would be a well-typed object with no stated
  relation to its input.
- `ComplexAnalytic.glueDataCLinear_coverGlueData`: **the transitions are `ℂ`-linear**, for every
  input, so `ComplexAnalytic.AnalyticSpace.ofGlueDataCLinear` applies and the gluing is an
  analytic space. The three lemmas it is built from —
  `ComplexAnalytic.comapAlgMap_coverOverlapIso`, `ComplexAnalytic.comapAlgMap_coverGlueIso` and
  `ComplexAnalytic.comapAlgMap_coverIncl_eq` — say where each factor of the transition gets its
  `ℂ`-linearity from.
- `ComplexAnalytic.coverAnalytification_toLocallyRingedSpace`: **the analytic space is the glue
  data's gluing**, with no transport — which is what lets every statement about
  `ComplexAnalytic.coverGlueData`'s gluing be read as a statement about `X^an`.
- `ComplexAnalytic.isOpenImmersion_coverIota`: **the members are open subspaces of `X^an`**,
  which with `AlgebraicGeometry.LocallyRingedSpace.GlueData.ι_jointly_surjective` is the
  statement that they cover it.
- `ComplexAnalytic.coverAnalytificationOpenCover_obj` and
  `ComplexAnalytic.coverAnalytificationOpenCover_map`: **the cover's members are the
  analytifications and its maps are `ComplexAnalytic.coverIota`**, both by `rfl`. Without them
  the cover is opaque and a consumer would be reading the glue data rather than `X^an`.
  (Naming `ComplexAnalytic.coverIota` here advertises it, so it is guarded below alongside them.)
- `ComplexAnalytic.coverOverlapIso_hom_coverIncl`: **the overlap's comparison isomorphism is one
  over the ambient member** — followed by the inclusion of `D(f_ij)` it is the projection of
  `Oka/Analytification/DistinguishedOpen.lean`. This is what lets a computation with
  `ComplexAnalytic.coverTransition` be pushed down to the member it sits over: it is what a
  refinement of a cover needs, it is why the declaration moved here from
  `Oka/Analytification/CoverComparison.lean`, and nothing in this file consumes it. (Named
  without citing the projection: every backticked repository name under this heading is read as
  a result *this* file advertises, and that one is another file's.)
- `ComplexAnalytic.range_coverTransitionHom_subset` and
  `ComplexAnalytic.range_comp_coverTransitionHom_subset`: **the transition into the ambient member
  cannot leave `D(f_ji)`**, whatever the input is. This is the half of the range condition that is
  a theorem rather than a hypothesis, and `ComplexAnalytic.coverTriple` is what consumes the
  second of the two. The mirrors on the `Spec` side are
  `ComplexAnalytic.range_specTransitionHom_subset` and
  `ComplexAnalytic.range_comp_specTransitionHom_subset`.
- `ComplexAnalytic.range_coverTransitionHom`: **and it is onto `D(f_ji)`**, which is the first of
  the two that a statement about *which* points of the `j`-th member are reached can use.
- `ComplexAnalytic.comm_coverGlueData`: **agreement over the overlaps is the glue datum's
  compatibility condition**, which is what makes `ComplexAnalytic.coverGlueMorphisms` statable —
  `ComplexAnalytic.AnalyticSpace.glueMorphisms` asks for agreement over a categorical pullback
  and a glue datum has no such object in it. Its hypothesis is at `i ≠ j`, since a caller has
  nothing to say about the diagonal.
- `ComplexAnalytic.coverIota_comp_coverGlueMorphisms` and
  `ComplexAnalytic.coverAnalytification_hom_ext`: **the glued morphism restricts to the given one
  on each member, and it is the only one that does** — the universal property in the form a
  caller uses it. `ComplexAnalytic.toLRSHom_coverGlueMorphisms` puts the first at the
  locally-ringed-space level.
- `ComplexAnalytic.coverGlueMorphisms_eq_glueMorphismsOfGlueData`: **the construction is
  `ComplexAnalytic.AnalyticSpace.glueMorphismsOfGlueData` at this file's glue datum**, by `rfl`,
  so it is an instance of the general one and not a sibling of it. The general declaration was
  written afterwards, out of the two ingredients this one had already put together.
- `ComplexAnalytic.coverIncl_comp_coverIota`: **the members' own inclusions agree over the
  overlaps**, the glue datum's `glue_condition` read back into this file's vocabulary, and
- `ComplexAnalytic.coverGlueMorphisms_coverIota`: **gluing them returns the identity.** The
  readable instance of `ComplexAnalytic.coverIota_comp_coverGlueMorphisms` at the members' own
  inclusions, and a corollary of it in one rewrite — which is worth saying, because the statement
  that rules out a definition ignoring its family is that one and not this one.
- `ComplexAnalytic.injective_base_coverIota`: **each member's inclusion is injective on points**,
  which an intersection of two members' images has to be told.
- `ComplexAnalytic.coverIota_image_coverOpen`: **the two members meet where the datum says they
  do** — `D(f_ij)` and `D(f_ji)` have the same image in `X^an`. A fact about the two composites
  out of the overlap as an open subspace of a member, and not by itself a statement that the two
  members meet in nothing else; **that one is the next bullet**, and it was absent until
  2026-09-04.
- `ComplexAnalytic.preimage_range_coverIota` and `ComplexAnalytic.range_coverIota_inter`: **and
  they meet in nothing else** — what of the `j`-th member lies in the `i`-th is exactly `D(f_ji)`,
  so the intersection of the two members inside `X^an` is the image of the overlap the datum
  names. This is a statement about the *gluing* rather than about the two composites, and what
  settles it is the mirror tree's description of when two points of two members become one point
  of `X^an` — cited at the declarations, since a backticked name under this heading is read as a
  result of this file. Both are at `i ≠ j`, where the glue datum's overlap is the one the input
  supplied.
- `ComplexAnalytic.coverOverlapIso_hom_coverTransitionHom` and
  `ComplexAnalytic.base_coverIota_localisationProj`: **the overlap's own space maps into `X^an` by
  two routes and they agree** — down into the `i`-th member and in, or across by the analytified
  glue and down into the `j`-th member and in. The first is the equation of morphisms and the
  second is it at a point, which is the form a computation with images of sets consumes.
- `ComplexAnalytic.image_localisationOpen_localisationProj`: **a distinguished open of the
  overlap's own space, pushed down into the member it lies over** — `D(f_ij) ⊓ D(x)`, for `x` a
  polynomial of that member read in the localisation's extra variable.

## What is not here

* **No input exhibited in this file, and no scheme.** Nothing below exhibits an input for
  `ComplexAnalytic.coverAnalytification`. `ComplexAnalytic.GlueShape.hRange_of_no_three` and
  `ComplexAnalytic.GlueShape.hCocycle_of_no_three` make both triple-overlap hypotheses vacuous
  below three members, so a two-member input exercises neither. Nor is any of this related to a
  *scheme*: the input is presentations and isomorphisms, and no statement here
  says they present one. **This bullet's heading said "no non-vacuity in this file" until the
  statements about `ComplexAnalytic.coverGlueMorphisms` arrived** — chiefly
  `ComplexAnalytic.coverIota_comp_coverGlueMorphisms`, which rules out a
  `ComplexAnalytic.coverGlueMorphisms` that ignores its family, and its instance
  `ComplexAnalytic.coverGlueMorphisms_coverIota` — and so reads to a grep as this bullet's
  contradiction. The two senses are different and both hold: nothing here exhibits an *input*, and
  statements here rule out a degenerate *output*.
* **Any statement that a gluing is not affine.** Nothing here shows that the glued space is equal
  to no one member, nor exhibits a space that is not the analytification of *some* presentation,
  which is stronger again and needs an invariant nothing here computes.
* **`Localization.Away`.** Nothing here needs
  `ComplexAnalytic.PresentedAlgebra (localisationPresentation g f)` to *be* a localisation; it
  needs the structure map and its analytification, both of which
  `Oka/Analytification/LocalisationFunctor.lean` provides. See that file and
  `Oka/Analytification/DistinguishedOpen.lean`'s `## What is not here`.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry

universe u

namespace ComplexAnalytic

noncomputable section

variable {J : Type u} (obj : J → Presentation.{u})
  (poly : ∀ i : J, J → MvPolynomial (ULift.{u} (Fin (obj i).n)) ℂ)

/-! ### The members of the cover and their overlaps -/

/-- **The `i`-th member of the cover**, `A_i^an`, as a locally ringed space.

Everything in this file before `ComplexAnalytic.coverAnalytification` is spelled at the
locally-ringed-space level, and deliberately: `ComplexAnalytic.AnalyticSpace`'s `Category`
instance defines composition through `toLRSHom`, so unifying two composites of analytic morphisms
forces it open and is expensive enough to exhaust the heartbeat budget on a three-term
`Iso.trans`. A glue data is a locally-ringed-space object anyway.

**The last two sections are the exceptions and cannot be anything else**, their whole point being
to produce an analytic space and then a morphism out of it: `### The analytic space, and its
members` and `### Morphisms out of X^an`. They are named rather than called "the last", because
this paragraph has now gone stale twice — once as each of them arrived — and both times the
pointer broke before any claim did.

**What keeps the policy in force there is that each exception carries its own way back down.**
`ComplexAnalytic.toLRSHom_coverIota` puts `ComplexAnalytic.coverIota` at the level the rest of the
file works at, which is how `ComplexAnalytic.isOpenImmersion_coverIota` is a statement the glue
data's own `ι` lemma proves, and `ComplexAnalytic.toLRSHom_coverGlueMorphisms` is the same `rfl`
for `ComplexAnalytic.coverGlueMorphisms`.

**Two statements in `### Morphisms out of X^an` do compose in the
`ComplexAnalytic.AnalyticSpace` category** — `ComplexAnalytic.coverIota_comp_coverGlueMorphisms`
and `ComplexAnalytic.coverAnalytification_hom_ext`, and the `reassoc` on the first generates a
three-term composite as well. So "it composes nothing", which was arithmetic about this file until
that section arrived, is no longer why the exception is cheap. **The reason now is that every one
of those proofs goes back down before it unifies anything**, through
`ComplexAnalytic.AnalyticSpace.forgetToLocallyRingedSpace.map_injective` — under a `change` in the
first and a `congrArg` in the second — so the `Category` instance is never forced open on a
composite. Stating a composite in that category is affordable; asking a proof to unify two of them
is what this paragraph is about, and there is still no such proof in this file. -/
abbrev coverSpace (i : J) : LocallyRingedSpace.{u} :=
  (AnalyticSpace.analytification.{u} (obj i).g).toLocallyRingedSpace

/-- **The part of the `i`-th member that meets the `j`-th**, as an open subset: `D(f_ij)`. -/
abbrev coverOpen (i j : J) : Opens (coverSpace.{u} obj i) :=
  localisationOpen.{u} (obj i).g (poly i j)

/-- **That open, as a space** — the object a glue data calls `V (i, j)`. -/
abbrev coverPart (i j : J) : LocallyRingedSpace.{u} :=
  (coverSpace.{u} obj i).restrict (coverOpen.{u} obj poly i j).isOpenEmbedding

/-- **Its inclusion into the `i`-th member** — the morphism a glue data calls `f i j`, and the
one its `f_open` field is about. -/
abbrev coverIncl (i j : J) : coverPart.{u} obj poly i j ⟶ coverSpace.{u} obj i :=
  (coverSpace.{u} obj i).ofRestrict (coverOpen.{u} obj poly i j).isOpenEmbedding

/-- **The presentation of the overlap, from the `i` side**: `(A_i)_{f_ij}`, presented by
`ComplexAnalytic.localisationPresentation`. This is the object the input isomorphism is between,
and it is where the *algebra* enters — everything else in this file is geometry. -/
abbrev coverOverlap (i j : J) : Presentation.{u} :=
  ⟨(obj i).n + 1, (obj i).k + 1, localisationPresentation.{u} (obj i).g (poly i j)⟩

/-- **The analytification of that presentation**, as a locally ringed space. -/
abbrev coverOverlapSpace (i j : J) : LocallyRingedSpace.{u} :=
  (AnalyticSpace.analytification.{u}
    (localisationPresentation.{u} (obj i).g (poly i j))).toLocallyRingedSpace

/-- **`ComplexAnalytic.localisationIso` at the locally-ringed-space level**: the analytification
of `(A_i)_{f_ij}` is the open subspace `D(f_ij)` of `A_i^an`.

Stated as a definition of its own rather than inlined into
`ComplexAnalytic.coverTransition` because the three-term `Iso.trans` there has to unify the
intermediate objects, and doing that against the *body* of a composite rather than against a
declared type is what runs the heartbeat budget out. Naming the two factors fixes it. -/
def coverOverlapIso (i j : J) :
    coverOverlapSpace.{u} obj poly i j ≅ coverPart.{u} obj poly i j :=
  AnalyticSpace.forgetToLocallyRingedSpace.{u}.mapIso (localisationIso.{u} (obj i).g (poly i j))

/-- **The comparison isomorphism is one over the ambient member**: followed by the inclusion of
`D(f_ij)` into `A_i^an` it is the projection `(A_i)_{f_ij}^an ⟶ A_i^an`.

`ComplexAnalytic.toLRSHom_localisationProj` in this file's vocabulary:
`ComplexAnalytic.coverOverlapIso` is `ComplexAnalytic.localisationIso` pushed through the
forgetful functor and `ComplexAnalytic.coverIncl` is the inclusion of the open subspace, so their
composite is `ComplexAnalytic.localisationProj`. It holds definitionally and is stated because
its consumers need it in this spelling: inside a `rw` in
`Oka/Analytification/CoverRefinement.lean`, and as the argument of a `congrArg` in a `calc` in
`Oka/Analytification/CoverComparison.lean`.

**It is the only route from `ComplexAnalytic.coverTransition` to a statement about the ambient
members**, whose two outer factors are this isomorphism at the two ends. A caller who knows what
the *algebraic* glue does over a common base can conclude what the transition does over it, and
that is what discharges `hrange` and `hcocycle` for a cover whose members all lie over one space
— `Oka/Analytification/CoverRefinement.lean`.

It stood in `Oka/Analytification/CoverComparison.lean` until it acquired that second consumer,
which cannot reach it there: that file imports the whole `Spec` side, and a refinement of an
analytic cover has nothing to do with schemes. Here it costs nothing —
`ComplexAnalytic.toLRSHom_localisationProj` is in this file's import closure already — where the
other direction would have cost `Oka/Analytification/CoverRefinement.lean` four `Oka` modules to
say something about `ComplexAnalytic.coverIncl`. Nothing in this file consumes it. -/
theorem coverOverlapIso_hom_coverIncl (i j : J) :
    (coverOverlapIso.{u} obj poly i j).hom ≫ coverIncl.{u} obj poly i j =
      (localisationProj.{u} (obj i).g (poly i j)).toLRSHom :=
  (toLRSHom_localisationProj.{u} (obj i).g (poly i j)).symm

variable (glue : ∀ i j : J, coverOverlap.{u} obj poly i j ≅ coverOverlap.{u} obj poly j i)

/-- **The given isomorphism of presentations, analytified**, at the locally-ringed-space level.
Named for the same reason as `ComplexAnalytic.coverOverlapIso`. -/
def coverGlueIso (i j : J) :
    coverOverlapSpace.{u} obj poly i j ≅ coverOverlapSpace.{u} obj poly j i :=
  AnalyticSpace.forgetToLocallyRingedSpace.{u}.mapIso
    (analytificationFunctor.{u}.mapIso (glue i j))

/-- **The transition isomorphism `X_i|D(f_ij) ≅ X_j|D(f_ji)`** — the morphism a glue data calls
`t i j`.

It is the given algebra isomorphism read through `ComplexAnalytic.localisationIso` at each end.
This is the only place the input's algebraic content is used, and it is why the file needs
`Oka/Analytification/DistinguishedOpen.lean` rather than only the functor. -/
def coverTransition (i j : J) : coverPart.{u} obj poly i j ≅ coverPart.{u} obj poly j i :=
  (coverOverlapIso.{u} obj poly i j).symm ≪≫ coverGlueIso.{u} obj poly glue i j ≪≫
    coverOverlapIso.{u} obj poly j i

/-- **The transition, followed into the ambient `j`-th member.** This is the morphism the range
hypothesis below is about: where the overlap of `i` and `j` goes inside `A_j^an`. -/
def coverTransitionHom (i j : J) : coverPart.{u} obj poly i j ⟶ coverSpace.{u} obj j :=
  (coverTransition.{u} obj poly glue i j).hom ≫ coverIncl.{u} obj poly j i

/-- **The analytified glue isomorphisms are inverse to each other**, provided the input
isomorphisms are. `Functor.mapIso` commutes with `Iso.symm`, twice.

This is the statement one level below `ComplexAnalytic.coverTransition`, between the two
`ComplexAnalytic.coverOverlapSpace`s; the transitions themselves are the next declaration, which
is this one conjugated by `ComplexAnalytic.coverOverlapIso` at each end. -/
theorem coverGlueIso_symm (hsymm : ∀ i j : J, glue j i = (glue i j).symm) (i j : J) :
    coverGlueIso.{u} obj poly glue j i = (coverGlueIso.{u} obj poly glue i j).symm := by
  rw [coverGlueIso, coverGlueIso, hsymm i j, Functor.mapIso_symm, Functor.mapIso_symm]
  rfl

/-- **Going from `i` to `j` and back is the identity of the overlap**, provided the input
isomorphisms are inverse to each other.

The previous lemma conjugated: the two inner comparison isomorphisms of the two transitions cancel
against each other, the two glue isomorphisms cancel by that lemma, and the two outer ones cancel
last. Nothing in the proof is about analytification.

**This is `hsymm`'s only geometric consequence in this file**, and it is what a caller reaching for
"the transition is invertible" wants: `ComplexAnalytic.coverTransition` is an isomorphism whatever
the input is, and this says which isomorphism its inverse is. Its consumer is the cocycle law of a
cross-member refinement (`Oka/Analytification/RefineDatumCocycle.lean`), where the three edges of a
triple whose members are not all different compose to a *pair* going out and back, and not to a
triple of the original datum's own — an original triple `(i, i, j)` is not one
`ComplexAnalytic.coverTriple` accepts. -/
theorem coverTransition_hom_comp (hsymm : ∀ i j : J, glue j i = (glue i j).symm) (i j : J) :
    (coverTransition.{u} obj poly glue i j).hom ≫ (coverTransition.{u} obj poly glue j i).hom =
      𝟙 _ := by
  rw [coverTransition, coverTransition, Iso.trans_hom, Iso.trans_hom, Iso.trans_hom,
    Iso.trans_hom, Iso.symm_hom, Iso.symm_hom,
    coverGlueIso_symm.{u} obj poly glue hsymm i j, Iso.symm_hom]
  simp

/-! ### The range hypothesis, half of which is free -/

/-- **The transition into the ambient member lands in `D(f_ji)`**, whatever the input is.

`ComplexAnalytic.coverTransitionHom` is a composite ending in `ComplexAnalytic.coverIncl`, whose
range is that open by `AlgebraicGeometry.LocallyRingedSpace.range_ofRestrict`. Nothing about the
input enters. The mirror of `ComplexAnalytic.range_specTransitionHom_subset`. -/
theorem range_coverTransitionHom_subset (i j : J) :
    Set.range (coverTransitionHom.{u} obj poly glue i j).base ⊆
      (coverOpen.{u} obj poly j i : Set (coverSpace.{u} obj j)) := by
  rw [coverTransitionHom, LocallyRingedSpace.comp_base, TopCat.coe_comp, Set.range_comp]
  refine subset_trans (Set.image_subset_range _ _) ?_
  exact ((coverSpace.{u} obj j).range_ofRestrict (coverOpen.{u} obj poly j i)).le

/-! ### Triple overlaps -/

/-- **The triple overlap `D(f_ij) ⊓ D(f_ik)` inside the `i`-th member**, as a space.

By `ComplexAnalytic.localisationOpen_mul` this is again a distinguished open of `A_i^an`, namely
`D(f_ij · f_ik)`; nothing below uses that, but it is the reason the classical construction works
and the reason that lemma exists. -/
abbrev coverTriplePart (i j k : J) : LocallyRingedSpace.{u} :=
  (coverSpace.{u} obj i).restrict
    (coverOpen.{u} obj poly i j ⊓ coverOpen.{u} obj poly i k).isOpenEmbedding

/-- **The inclusion of the triple overlap into the double overlap of `i` and `j`.** -/
abbrev coverTripleIncl (i j k : J) :
    coverTriplePart.{u} obj poly i j k ⟶ coverPart.{u} obj poly i j :=
  (coverSpace.{u} obj i).restrictLE (inf_le_left :
    coverOpen.{u} obj poly i j ⊓ coverOpen.{u} obj poly i k ≤ coverOpen.{u} obj poly i j)

/-- **The `D(f_ji)` half of the range hypothesis is free**, at the composite the hypothesis is
actually stated at: `ComplexAnalytic.range_coverTransitionHom_subset` precomposed. So the content
of `hrange` is the *other* half alone, and that is the form the hypothesis below takes. -/
theorem range_comp_coverTransitionHom_subset (i j k : J) :
    Set.range (coverTripleIncl.{u} obj poly i j k ≫
        coverTransitionHom.{u} obj poly glue i j).base ⊆
      (coverOpen.{u} obj poly j i : Set (coverSpace.{u} obj j)) := by
  rw [LocallyRingedSpace.comp_base, TopCat.coe_comp, Set.range_comp]
  exact subset_trans (Set.image_subset_range _ _)
    (range_coverTransitionHom_subset.{u} obj poly glue i j)

variable (hrange : ∀ i j k : J, i ≠ j → i ≠ k → j ≠ k →
  Set.range (coverTripleIncl.{u} obj poly i j k ≫ coverTransitionHom.{u} obj poly glue i j).base ⊆
    (coverOpen.{u} obj poly j k : Set (coverSpace.{u} obj j)))

/-- **The transition on triple overlaps**, `X_i|(D(f_ij) ⊓ D(f_ik)) ⟶ X_j|(D(f_jk) ⊓ D(f_ji))`.

This is `t'` before it is conjugated into the pullbacks.
`AlgebraicGeometry.LocallyRingedSpace.liftRestrict` wants the image inside `D(f_jk) ⊓ D(f_ji)`;
`hrange` is the `D(f_jk)` half — the classical statement that the transition from `i` to `j`
carries the part of the overlap that also meets `k` into the part that meets `k` — and
`ComplexAnalytic.range_comp_coverTransitionHom_subset` is the other, which holds whatever the
input is. Only the first is not implied by anything: two members can be glued along an open
without their glueings agreeing on triple overlaps, and that is what `hrange` and `hcocycle` rule
out. -/
def coverTriple (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    coverTriplePart.{u} obj poly i j k ⟶ coverTriplePart.{u} obj poly j k i :=
  LocallyRingedSpace.liftRestrict
    (coverTripleIncl.{u} obj poly i j k ≫ coverTransitionHom.{u} obj poly glue i j) _
    (Set.subset_inter (hrange i j k hij hik hjk)
      (range_comp_coverTransitionHom_subset.{u} obj poly glue i j k))

/-- **`coverTriple` is a morphism over the ambient member**, which is the only property of it
anything consumes. -/
@[reassoc (attr := simp)]
theorem coverTriple_fac (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    coverTriple.{u} obj poly glue hrange i j k hij hik hjk ≫
        (coverSpace.{u} obj j).ofRestrict
          (coverOpen.{u} obj poly j k ⊓ coverOpen.{u} obj poly j i).isOpenEmbedding =
      coverTripleIncl.{u} obj poly i j k ≫ coverTransitionHom.{u} obj poly glue i j :=
  LocallyRingedSpace.liftRestrict_fac _ _ _

/-! ### The glue data -/

/-- **The glue data of the cover, in the form that only asks for the overlaps when `i ≠ j`.**

`t'` is `ComplexAnalytic.coverTriple` conjugated by
`AlgebraicGeometry.LocallyRingedSpace.restrictInfIsoPullback` at each end, which is what turns a
morphism of open subspaces into a morphism of categorical pullbacks. Two consequences, and they
are the whole reason for going through that identification:

* `t_fac` reduces to an equation between two morphisms into `X_j|D(f_ji)`, which
  `AlgebraicGeometry.LocallyRingedSpace.hom_ext_restrict` turns into an equation over `X_j`, and
  there both sides are `coverTripleIncl ≫ coverTransitionHom` by `coverTriple_fac`;
* `cocycle` is `hcocycle` and nothing else: the second conjugating isomorphism of `t' i j k` is
  the *same* isomorphism as the first of `t' j k i`, so all six cancel in pairs. -/
def coverGlueData' (hsymm : ∀ i j : J, glue j i = (glue i j).symm)
    (hcocycle : ∀ i j k : J, ∀ hij : i ≠ j, ∀ hik : i ≠ k, ∀ hjk : j ≠ k,
      coverTriple.{u} obj poly glue hrange i j k hij hik hjk ≫
        coverTriple.{u} obj poly glue hrange j k i hjk hij.symm hik.symm ≫
        coverTriple.{u} obj poly glue hrange k i j hik.symm hjk.symm hij = 𝟙 _) :
    GlueData' LocallyRingedSpace.{u} where
  J := J
  U := coverSpace.{u} obj
  V i j _ := coverPart.{u} obj poly i j
  f i j _ := coverIncl.{u} obj poly i j
  t i j _ := (coverTransition.{u} obj poly glue i j).hom
  t' i j k hij hik hjk :=
    ((coverSpace.{u} obj i).restrictInfIsoPullback
      (coverOpen.{u} obj poly i j) (coverOpen.{u} obj poly i k)).inv ≫
      coverTriple.{u} obj poly glue hrange i j k hij hik hjk ≫
      ((coverSpace.{u} obj j).restrictInfIsoPullback
        (coverOpen.{u} obj poly j k) (coverOpen.{u} obj poly j i)).hom
  t_fac i j k hij hik hjk := by
    rw [Category.assoc, Category.assoc,
      LocallyRingedSpace.restrictInfIsoPullback_hom_snd, Iso.inv_comp_eq, ← Category.assoc,
      LocallyRingedSpace.restrictInfIsoPullback_hom_fst]
    refine LocallyRingedSpace.hom_ext_restrict _ _ _ ?_
    rw [Category.assoc, LocallyRingedSpace.restrictLE_fac, coverTriple_fac]
    rfl
  t_inv i j _ := by
    simp only [coverTransition, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      Iso.hom_inv_id_assoc, coverGlueIso_symm.{u} obj poly glue hsymm i j, Iso.symm_hom,
      Iso.hom_inv_id_assoc, Iso.inv_hom_id]
  cocycle i j k hij hik hjk := by
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [reassoc_of% hcocycle i j k hij hik hjk, Iso.inv_hom_id]

/-- **The glue data of an affine cover with distinguished overlaps.**

`CategoryTheory.GlueData.ofGlueData'` of `ComplexAnalytic.coverGlueData'`, with the `f_open`
field supplied by `AlgebraicGeometry.LocallyRingedSpace.isOpenImmersion_f'` — whose hypothesis is
that each `f i j` is an open immersion, and each is `ofRestrict`.

Note which of the two open-immersion facts about a distinguished open this uses:
`AlgebraicGeometry.LocallyRingedSpace.isOpenImmersion_ofRestrict`, not
`ComplexAnalytic.isOpenImmersion_localisationProj`. The two are the same fact at the two
spellings of the overlap — as the open subspace, and as the analytification of the localisation —
and this file takes the first, because that is the spelling at which the range computations `t'`
needs are statements about `ComplexAnalytic.localisationOpen`. The algebraic description enters
only through `ComplexAnalytic.coverTransition`. -/
def coverGlueData (hsymm : ∀ i j : J, glue j i = (glue i j).symm)
    (hcocycle : ∀ i j k : J, ∀ hij : i ≠ j, ∀ hik : i ≠ k, ∀ hjk : j ≠ k,
      coverTriple.{u} obj poly glue hrange i j k hij hik hjk ≫
        coverTriple.{u} obj poly glue hrange j k i hjk hij.symm hik.symm ≫
        coverTriple.{u} obj poly glue hrange k i j hik.symm hjk.symm hij = 𝟙 _) :
    LocallyRingedSpace.GlueData.{u} where
  toGlueData :=
    GlueData.ofGlueData' (coverGlueData'.{u} obj poly glue hrange hsymm hcocycle)
  f_open i j :=
    LocallyRingedSpace.isOpenImmersion_f'
      (coverGlueData'.{u} obj poly glue hrange hsymm hcocycle)
      (fun _ _ _ ↦ LocallyRingedSpace.isOpenImmersion_ofRestrict _ _) i j

variable (hsymm : ∀ i j : J, glue j i = (glue i j).symm)
  (hcocycle : ∀ i j k : J, ∀ hij : i ≠ j, ∀ hik : i ≠ k, ∀ hjk : j ≠ k,
    coverTriple.{u} obj poly glue hrange i j k hij hik hjk ≫
      coverTriple.{u} obj poly glue hrange j k i hjk hij.symm hik.symm ≫
      coverTriple.{u} obj poly glue hrange k i j hik.symm hjk.symm hij = 𝟙 _)

/-- **The members of the glue data are the analytifications one put in.**

`rfl`, and stated because without it `ComplexAnalytic.coverGlueData` is a well-typed object with
no recorded relation to its input: `CategoryTheory.GlueData.ofGlueData'` has no projection lemmas
in Mathlib, so nothing else says what `U` is. `Oka/CategoryTheory/GlueData.lean` is where that
absence is measured, with the version, the rev and the command as run; **this clause carried the
universal with no instrument and no pointer until 2026-09-21**, when taxis #2118 swept the family
onto the one site that measures it. -/
@[simp]
theorem coverGlueData_U (i : J) :
    (coverGlueData.{u} obj poly glue hrange hsymm hcocycle).U i = coverSpace.{u} obj i :=
  rfl

/-- **The `i`-th member is an open subspace of the gluing.**

`AlgebraicGeometry.LocallyRingedSpace.GlueData.ι_isOpenImmersion` at this glue data, and the
statement in which the construction is a *cover*: together with
`AlgebraicGeometry.LocallyRingedSpace.GlueData.ι_jointly_surjective`, the analytifications one
started from are an open cover of the space this builds. -/
theorem coverGlueData_ι_isOpenImmersion (i : J) :
    LocallyRingedSpace.IsOpenImmersion
      ((coverGlueData.{u} obj poly glue hrange hsymm hcocycle).toGlueData.ι i) :=
  inferInstance

/-! ### The transitions are `ℂ`-linear

`ComplexAnalytic.AnalyticSpace.ofGlueDataCLinear` turns a glue data of analytic pieces into an
analytic space provided its transitions are `ℂ`-linear (`ComplexAnalytic.GlueDataCLinear`). For a
glue data built here that hypothesis is **automatic**, and the reason is that every morphism in
sight is a morphism of *analytic* spaces, whose `ℂ`-linearity is a field rather than something to
prove: `ComplexAnalytic.coverOverlapIso` is `ComplexAnalytic.localisationIso` and
`ComplexAnalytic.coverGlueIso` is the given algebra isomorphism analytified, both read through
`ComplexAnalytic.AnalyticSpace.forgetToLocallyRingedSpace`.

The work is therefore transport rather than algebra, and it is done in the three lemmas below:
each factor of `ComplexAnalytic.coverTransition` is recognised as an analytic morphism, and
`ComplexAnalytic.AnalyticSpace.comapAlgMap_toLRSHom` turns that into the equation of
`AlgebraicGeometry.LocallyRingedSpace.comapAlgMap`s the predicate is stated with.
-/

/-- **The overlap's own analytic structure is the one it inherits from the `i`-th member.**

`ComplexAnalytic.coverOverlapIso` followed by the inclusion of `D(f_ij)` is
`ComplexAnalytic.localisationProj` (`ComplexAnalytic.toLRSHom_localisationProj`), which is a
morphism of analytic spaces, so this is that morphism's `ℂ`-linearity field. -/
theorem comapAlgMap_coverOverlapIso (i j : J) :
    LocallyRingedSpace.comapAlgMap
        ((coverOverlapIso.{u} obj poly i j).hom ≫ coverIncl.{u} obj poly i j)
        (AnalyticSpace.analytification.{u} (obj i).g).algebraMap =
      (AnalyticSpace.analytification.{u} (coverOverlap.{u} obj poly i j).g).algebraMap := by
  rw [show (coverOverlapIso.{u} obj poly i j).hom ≫ coverIncl.{u} obj poly i j =
      (localisationProj.{u} (obj i).g (poly i j)).toLRSHom from
    (toLRSHom_localisationProj.{u} (obj i).g (poly i j)).symm]
  exact AnalyticSpace.comapAlgMap_toLRSHom _

/-- **The given algebra isomorphism, analytified, carries one overlap's structure to the
other's.**

This is where the input's algebraic content is used, and it is free: `glue i j` is an isomorphism
of *presentations*, so `ComplexAnalytic.analytificationFunctor` sends it to an isomorphism of
analytic spaces, and its `ℂ`-linearity is that morphism's own field. Nothing here computes with
the isomorphism. -/
theorem comapAlgMap_coverGlueIso (i j : J) :
    LocallyRingedSpace.comapAlgMap (coverGlueIso.{u} obj poly glue i j).hom
        (AnalyticSpace.analytification.{u} (coverOverlap.{u} obj poly j i).g).algebraMap =
      (AnalyticSpace.analytification.{u} (coverOverlap.{u} obj poly i j).g).algebraMap :=
  AnalyticSpace.comapAlgMap_toLRSHom (analytificationFunctor.{u}.map (glue i j).hom)

/-- **The two structures the overlap inherits agree**, before the `dite`s of
`CategoryTheory.GlueData.ofGlueData'` are in the way: from the `i`-th member directly, and from
the `j`-th through the transition.

Both are compared after `ComplexAnalytic.coverOverlapIso`, which is legitimate because
`AlgebraicGeometry.LocallyRingedSpace.comapAlgMap_hom_injective` says pulling back along an
isomorphism loses nothing; there both sides become the overlap's own structure, by the two lemmas
above and the cancellation of `ComplexAnalytic.coverOverlapIso` against itself inside
`ComplexAnalytic.coverTransition`. -/
theorem comapAlgMap_coverIncl_eq (i j : J) :
    LocallyRingedSpace.comapAlgMap (coverIncl.{u} obj poly i j)
        (AnalyticSpace.analytification.{u} (obj i).g).algebraMap =
      LocallyRingedSpace.comapAlgMap
        ((coverTransition.{u} obj poly glue i j).hom ≫ coverIncl.{u} obj poly j i)
        (AnalyticSpace.analytification.{u} (obj j).g).algebraMap := by
  refine LocallyRingedSpace.comapAlgMap_hom_injective (coverOverlapIso.{u} obj poly i j) ?_
  dsimp only
  rw [← LocallyRingedSpace.comapAlgMap_comp, ← LocallyRingedSpace.comapAlgMap_comp,
    comapAlgMap_coverOverlapIso]
  have ht : (coverOverlapIso.{u} obj poly i j).hom ≫
      (coverTransition.{u} obj poly glue i j).hom ≫ coverIncl.{u} obj poly j i =
        (coverGlueIso.{u} obj poly glue i j).hom ≫
          ((coverOverlapIso.{u} obj poly j i).hom ≫ coverIncl.{u} obj poly j i) := by
    simp [coverTransition]
  rw [ht, LocallyRingedSpace.comapAlgMap_comp, comapAlgMap_coverOverlapIso,
    comapAlgMap_coverGlueIso]

/-- **The transitions of the glue data of an affine cover are `ℂ`-linear**, for the structures the
members carry as analytifications. This is the hypothesis
`ComplexAnalytic.AnalyticSpace.ofGlueDataCLinear` asks for, so an affine cover with distinguished
overlaps produces an *analytic space* and not merely a locally ringed space.

The content is `ComplexAnalytic.comapAlgMap_coverIncl_eq`; the rest is getting past the `dite`s
that `CategoryTheory.GlueData.ofGlueData'` fills the diagonal with, by
`CategoryTheory.GlueData.ofGlueData'_f_of_ne` and
`CategoryTheory.GlueData.ofGlueData'_t_comp_f_of_ne`.

Two places want a term rather than a rewrite and the second is not optional. The diagonal case is
an equation of *morphisms*, so `congrArg` disposes of it without touching the structures. Off the
diagonal both sides carry the same `eqToHom` prefix, and
`AlgebraicGeometry.LocallyRingedSpace.comapAlgMap_comp` has to be applied **as a term**: the
corresponding `rw` reports *did not find an occurrence of the pattern
`comapAlgMap (?f ≫ ?g) ?γ`* against a goal that visibly has that shape, and it still does after
`dsimp only [CategoryTheory.GlueData.ofGlueData']`, so delta-reducing the projections in the goal
is not the remedy. **Why it fails is not established here** and no explanation should be read
into it; the contrast worth having is that
`ComplexAnalytic.comapAlgMap_coverIncl_eq` above rewrites with the same lemma twice and
successfully, at the same category, on a composite that has not come through
`CategoryTheory.GlueData.ofGlueData'_f_of_ne` carrying its `eqToHom`. -/
theorem glueDataCLinear_coverGlueData :
    GlueDataCLinear.{u} (coverGlueData.{u} obj poly glue hrange hsymm hcocycle)
      fun j ↦ (AnalyticSpace.analytification.{u} (obj j).g).algebraMap := by
  intro i j
  by_cases h : i = j
  · subst h
    refine congrArg (fun m ↦ LocallyRingedSpace.comapAlgMap m
      (AnalyticSpace.analytification.{u} (obj i).g).algebraMap) ?_
    change (CategoryTheory.GlueData.ofGlueData'
        (coverGlueData'.{u} obj poly glue hrange hsymm hcocycle)).f i i =
      (CategoryTheory.GlueData.ofGlueData'
        (coverGlueData'.{u} obj poly glue hrange hsymm hcocycle)).t i i ≫
        (CategoryTheory.GlueData.ofGlueData'
          (coverGlueData'.{u} obj poly glue hrange hsymm hcocycle)).f i i
    rw [CategoryTheory.GlueData.ofGlueData'_f_self, CategoryTheory.GlueData.ofGlueData'_t_self]
    simp
  · change LocallyRingedSpace.comapAlgMap ((CategoryTheory.GlueData.ofGlueData'
        (coverGlueData'.{u} obj poly glue hrange hsymm hcocycle)).f i j) _ =
      LocallyRingedSpace.comapAlgMap ((CategoryTheory.GlueData.ofGlueData'
        (coverGlueData'.{u} obj poly glue hrange hsymm hcocycle)).t i j ≫
        (CategoryTheory.GlueData.ofGlueData'
          (coverGlueData'.{u} obj poly glue hrange hsymm hcocycle)).f j i) _
    rw [CategoryTheory.GlueData.ofGlueData'_f_of_ne _ h,
      CategoryTheory.GlueData.ofGlueData'_t_comp_f_of_ne _ h]
    dsimp only [coverGlueData']
    exact (LocallyRingedSpace.comapAlgMap_comp _ _ _).trans
      ((congrArg (LocallyRingedSpace.comapAlgMap (eqToHom (dif_neg h)))
        (comapAlgMap_coverIncl_eq.{u} obj poly glue i j)).trans
          (LocallyRingedSpace.comapAlgMap_comp _ _ _).symm)

/-! ### The analytic space, and its members

`ComplexAnalytic.AnalyticSpace.ofGlueDataCLinear` needs three things beyond the glue data: the
`ℂ`-algebra structure on each member, the `ℂ`-linearity of the transitions, and local models on
each member. The first and third are the analytification's own — `coverSpace obj i` **is**
`(analytification (obj i).g).toLocallyRingedSpace`, by `rfl`, so `local_model` applies verbatim
— and the second is `ComplexAnalytic.glueDataCLinear_coverGlueData` above. So the construction
costs nothing at this level, and the content is in the two statements after it.
-/

/-- **The analytic space an affine cover with distinguished overlaps glues to.**

`ComplexAnalytic.AnalyticSpace.ofGlueDataCLinear` at `ComplexAnalytic.coverGlueData`, with the
members' own `ℂ`-algebra structures and local models. Every hypothesis is discharged by a
declaration above or by the analytification itself; nothing new is proved by this definition, and
the two theorems below are what make it usable.

**Not "the analytification of a scheme", and the module docstring's titled section is why.**
Nothing here says the input presents one, and a scheme's cover does not supply this input in
general: `poly` asks for **one** distinguished open of the `i`-th member per *ordered pair*, while
`AlgebraicGeometry.exists_basicOpen_le_affine_inter` is stated at a *point* of an intersection and
gives one such open there — so the intersection of two affine members is a **union of such
opens**, and nothing makes one of them the whole of it. -/
def coverAnalytification : AnalyticSpace.{u} :=
  AnalyticSpace.ofGlueDataCLinear
    (coverGlueData.{u} obj poly glue hrange hsymm hcocycle)
    (fun i ↦ (AnalyticSpace.analytification.{u} (obj i).g).algebraMap)
    (glueDataCLinear_coverGlueData.{u} obj poly glue hrange hsymm hcocycle)
    (fun i ↦ (AnalyticSpace.analytification.{u} (obj i).g).local_model)

/-- **The underlying locally ringed space is the glue data's gluing**, with no transport.

`ComplexAnalytic.AnalyticSpace.ofGlueDataCLinear_toLocallyRingedSpace`, and the reason it is
worth stating separately is that everything already proved about
`ComplexAnalytic.coverGlueData`'s gluing — `ι_isOpenImmersion`, `ι_jointly_surjective`, and the
non-surjectivity statements the test files prove — is a statement about `X^an` only through
this. -/
theorem coverAnalytification_toLocallyRingedSpace :
    (coverAnalytification.{u} obj poly glue hrange hsymm hcocycle).toLocallyRingedSpace =
      (coverGlueData.{u} obj poly glue hrange hsymm hcocycle).toGlueData.glued :=
  AnalyticSpace.ofGlueDataCLinear_toLocallyRingedSpace _ _ _ _

/-- **The `i`-th member's analytification, as a morphism of analytic spaces into `X^an`.**

Its underlying morphism is the glue data's `ι i` — that is `ComplexAnalytic.toLRSHom_coverIota`,
by `rfl` — and its `ℂ`-linearity is
`ComplexAnalytic.AnalyticSpace.comapAlgMap_ofGlueDataCLinear_algebraMap`, which says the glued
structure pulls back along `ι i` to the member's own, read through
`ComplexAnalytic.isCLinearHom_comapAlgMap`. -/
def coverIota (i : J) :
    AnalyticSpace.analytification.{u} (obj i).g ⟶
      coverAnalytification.{u} obj poly glue hrange hsymm hcocycle :=
  ⟨(coverGlueData.{u} obj poly glue hrange hsymm hcocycle).toGlueData.ι i, by
    have h := AnalyticSpace.comapAlgMap_ofGlueDataCLinear_algebraMap
      (coverGlueData.{u} obj poly glue hrange hsymm hcocycle)
      (fun i ↦ (AnalyticSpace.analytification.{u} (obj i).g).algebraMap)
      (glueDataCLinear_coverGlueData.{u} obj poly glue hrange hsymm hcocycle)
      (fun i ↦ (AnalyticSpace.analytification.{u} (obj i).g).local_model) i
    exact h ▸ isCLinearHom_comapAlgMap _ _⟩

/-- The underlying morphism of `ComplexAnalytic.coverIota` is the glue data's `ι`. -/
@[simp]
theorem toLRSHom_coverIota (i : J) :
    (coverIota.{u} obj poly glue hrange hsymm hcocycle i).toLRSHom =
      (coverGlueData.{u} obj poly glue hrange hsymm hcocycle).toGlueData.ι i :=
  rfl

/-- **The members are open subspaces of `X^an`.**

`ComplexAnalytic.coverGlueData_ι_isOpenImmersion` read through
`ComplexAnalytic.toLRSHom_coverIota`. Together with
`AlgebraicGeometry.LocallyRingedSpace.GlueData.ι_jointly_surjective` this says the
analytifications one started from are an open cover of the space built from them. -/
theorem isOpenImmersion_coverIota (i : J) :
    LocallyRingedSpace.IsOpenImmersion
      (coverIota.{u} obj poly glue hrange hsymm hcocycle i).toLRSHom :=
  coverGlueData_ι_isOpenImmersion.{u} obj poly glue hrange hsymm hcocycle i

/-- **`X^an` as covered by the members' analytifications**, in the form anything that consumes a
cover asks for.

`ComplexAnalytic.AnalyticSpace.glueMorphisms` glues a morphism *out of* an analytic space `X` from
morphisms out of the members of an `AlgebraicGeometry.LocallyRingedSpace.OpenCover` of its
underlying locally ringed space, and until this there was no such cover of
`ComplexAnalytic.coverAnalytification` — so the space this file builds could not be the source of
a glued morphism.

**The transport is free and that is worth recording, because it need not have been.** This is
`AlgebraicGeometry.LocallyRingedSpace.GlueData.openCover` at
`ComplexAnalytic.coverGlueData`, applied with no rewrite, no `▸` and no `eqToIso`: the cover it
produces is one of `(coverGlueData …).toGlueData.glued`, and that is *the same term* as
`(coverAnalytification …).toLocallyRingedSpace` because
`ComplexAnalytic.coverAnalytification_toLocallyRingedSpace` is
`ComplexAnalytic.AnalyticSpace.ofGlueDataCLinear_toLocallyRingedSpace`, which is `rfl`. The same
three `rfl`s make the two lemmas below `rfl` as well: `ComplexAnalytic.coverGlueData_U` for the
members and `ComplexAnalytic.toLRSHom_coverIota` for the maps.

**Those two lemmas are not decoration.** Without them this is a cover whose members and maps are
spelled in the glue data's vocabulary — a cover of a gluing wearing an analytic space's name —
and a consumer would have to unfold `ComplexAnalytic.coverGlueData` to say what it covers `X^an`
by. With them it is a cover by the analytifications one started from, mapped by
`ComplexAnalytic.coverIota`.

Noncomputable and non-canonical for the reason
`AlgebraicGeometry.LocallyRingedSpace.GlueData.openCover` is: the index of a point is *chosen*,
and nothing downstream depends on which. -/
noncomputable def coverAnalytificationOpenCover :
    LocallyRingedSpace.OpenCover.{u}
      (coverAnalytification.{u} obj poly glue hrange hsymm hcocycle).toLocallyRingedSpace :=
  (coverGlueData.{u} obj poly glue hrange hsymm hcocycle).openCover

/-- **The `i`-th member of the cover is the `i`-th member's analytification**, by `rfl` —
`ComplexAnalytic.coverGlueData_U` at the glue data. -/
@[simp]
theorem coverAnalytificationOpenCover_obj (i : J) :
    (coverAnalytificationOpenCover.{u} obj poly glue hrange hsymm hcocycle).obj i =
      (AnalyticSpace.analytification.{u} (obj i).g).toLocallyRingedSpace :=
  rfl

/-- **The `i`-th map of the cover is `ComplexAnalytic.coverIota`**, by `rfl` —
`ComplexAnalytic.toLRSHom_coverIota` at the glue data.

Stated against `ComplexAnalytic.coverIota` rather than against
`(coverGlueData …).toGlueData.ι`, because a consumer of this cover is working with morphisms of
analytic spaces and the glue data's `ι` is not one; `ComplexAnalytic.isOpenImmersion_coverIota` is
the same choice made for the open-immersion statement. -/
@[simp]
theorem coverAnalytificationOpenCover_map (i : J) :
    (coverAnalytificationOpenCover.{u} obj poly glue hrange hsymm hcocycle).map i =
      (coverIota.{u} obj poly glue hrange hsymm hcocycle i).toLRSHom :=
  rfl

/-! ### Morphisms out of `X^an`

`ComplexAnalytic.coverAnalytificationOpenCover` makes
`ComplexAnalytic.AnalyticSpace.glueMorphisms` *applicable* to `X^an`; it does not make it usable.
Its hypothesis is agreement over the **categorical pullback** of two members' inclusions, and
nothing in this file produces one: what a caller holds is a family of morphisms out of the
`A_i^an` together with a statement about `ComplexAnalytic.coverIncl` and
`ComplexAnalytic.coverTransition`, which are the only overlap data the input carries.

Two transports close the gap and neither is this file's own.
`AlgebraicGeometry.LocallyRingedSpace.GlueData.pullback_condition_of_comm` turns agreement over a
glue datum's chosen overlaps into the pullback condition; `CategoryTheory.GlueData.ofGlueData'_comm`
turns agreement over *these* overlaps into agreement over the glue datum's, which is not the same
statement because `ComplexAnalytic.coverGlueData` goes through
`CategoryTheory.GlueData.ofGlueData'` and that fills the diagonal with `dite`s. The composite is
`ComplexAnalytic.comm_coverGlueData` below, and the hypothesis it asks for is at `i ≠ j` — a
caller has nothing to say about `coverTransition i i`, which is whatever `glue i i` is.

**`ComplexAnalytic.comm_coverGlueData` is stated at a locally ringed space target and not at an
analytic one**, deliberately: the comparison morphism `X^an ⟶ X` maps to a scheme, which is a
locally ringed space and not an analytic space, so a version tied to
`ComplexAnalytic.AnalyticSpace` would serve one consumer of this file and not the other.

**`ComplexAnalytic.coverIota_comp_coverGlueMorphisms` is what says the construction is not
degenerate**, and `ComplexAnalytic.coverGlueMorphisms_coverIota` is its instance at the members'
own inclusions rather than a second control — it constrains `ComplexAnalytic.coverGlueMorphisms`
at one family where the general lemma constrains it at every family.

**The criterion is "is about `ComplexAnalytic.coverGlueMorphisms` and mentions `f`", and exactly
two statements here meet it**: that one and `ComplexAnalytic.toLRSHom_coverGlueMorphisms`. Having
`f` on the right-hand side is not the criterion and would give three —
`ComplexAnalytic.comm_coverGlueData` does too, and a `coverGlueMorphisms` ignoring its family
would satisfy it perfectly well, because that theorem is about the glue datum and an arbitrary
family and never mentions this construction at all. **The two come apart on exactly that
statement**, which is why the criterion is worth stating rather than leaving to be read off the
right-hand sides.

**Nothing else here constrains the definition at all**, and that is a statement about the
statements rather than about hypothetical definitions:
`ComplexAnalytic.coverAnalytification_hom_ext`, `ComplexAnalytic.comm_coverGlueData` and
`ComplexAnalytic.coverIncl_comp_coverIota` do not mention `ComplexAnalytic.coverGlueMorphisms`, so
their truth is independent of how it is defined; and the round trip, being an instantiation,
constrains it only where the family is `ComplexAnalytic.coverIota`.
-/

/-- **A family of morphisms out of the members which agrees over the overlaps satisfies the glue
datum's compatibility condition.**

`CategoryTheory.GlueData.ofGlueData'_comm` at `ComplexAnalytic.coverGlueData'`. The hypothesis is
at `i ≠ j` and the conclusion at every pair: `ComplexAnalytic.coverGlueData`'s diagonal is
`CategoryTheory.GlueData.ofGlueData'`'s `eqToHom`s and not `ComplexAnalytic.coverTransition i i`,
so there is nothing there for a caller to check.

The target is a `AlgebraicGeometry.LocallyRingedSpace`, so that this serves both the analytic
morphism below and the comparison morphism to the scheme, whose target is not an analytic
space. -/
theorem comm_coverGlueData {Y : LocallyRingedSpace.{u}} (f : ∀ i, coverSpace.{u} obj i ⟶ Y)
    (h : ∀ i j : J, i ≠ j → coverIncl.{u} obj poly i j ≫ f i =
      (coverTransition.{u} obj poly glue i j).hom ≫ coverIncl.{u} obj poly j i ≫ f j) (i j : J) :
    (coverGlueData.{u} obj poly glue hrange hsymm hcocycle).f i j ≫ f i =
      (coverGlueData.{u} obj poly glue hrange hsymm hcocycle).t i j ≫
        (coverGlueData.{u} obj poly glue hrange hsymm hcocycle).f j i ≫ f j :=
  CategoryTheory.GlueData.ofGlueData'_comm
    (coverGlueData'.{u} obj poly glue hrange hsymm hcocycle) f (fun i j hij ↦ h i j hij) i j

/-- **A morphism of analytic spaces out of `X^an`, glued from morphisms out of the members.**

`ComplexAnalytic.AnalyticSpace.glueMorphisms` at
`ComplexAnalytic.coverAnalytificationOpenCover`, with the pullback hypothesis supplied by
`ComplexAnalytic.comm_coverGlueData` through
`AlgebraicGeometry.LocallyRingedSpace.GlueData.pullback_condition_of_comm`, and the `ℂ`-linearity
of each piece by that of `f i` itself: `ComplexAnalytic.AnalyticSpace`'s structure on the `i`-th
member of the cover is the analytification's own, which is
`ComplexAnalytic.AnalyticSpace.comapAlgMap_ofGlueDataCLinear_algebraMap` and is the same rewrite
`ComplexAnalytic.coverIota` makes. -/
def coverGlueMorphisms {Y : AnalyticSpace.{u}}
    (f : ∀ i, AnalyticSpace.analytification.{u} (obj i).g ⟶ Y)
    (h : ∀ i j : J, i ≠ j → coverIncl.{u} obj poly i j ≫ (f i).toLRSHom =
      (coverTransition.{u} obj poly glue i j).hom ≫
        coverIncl.{u} obj poly j i ≫ (f j).toLRSHom) :
    coverAnalytification.{u} obj poly glue hrange hsymm hcocycle ⟶ Y :=
  AnalyticSpace.glueMorphisms
    (coverAnalytificationOpenCover.{u} obj poly glue hrange hsymm hcocycle)
    (fun i ↦ (f i).toLRSHom)
    (LocallyRingedSpace.GlueData.pullback_condition_of_comm _ _
      (comm_coverGlueData.{u} obj poly glue hrange hsymm hcocycle _ h))
    (fun i ↦ by
      have hc := AnalyticSpace.comapAlgMap_ofGlueDataCLinear_algebraMap
        (coverGlueData.{u} obj poly glue hrange hsymm hcocycle)
        (fun i ↦ (AnalyticSpace.analytification.{u} (obj i).g).algebraMap)
        (glueDataCLinear_coverGlueData.{u} obj poly glue hrange hsymm hcocycle)
        (fun i ↦ (AnalyticSpace.analytification.{u} (obj i).g).local_model) i
      exact hc ▸ (f i).isCLinear)

/-- **It is `ComplexAnalytic.AnalyticSpace.glueMorphismsOfGlueData` at this file's glue datum**, on
the nose.

`ComplexAnalytic.coverGlueMorphisms` composes `AlgebraicGeometry.LocallyRingedSpace.GlueData`'s
`pullback_condition_of_comm` for one hypothesis with
`ComplexAnalytic.AnalyticSpace.comapAlgMap_ofGlueDataCLinear_algebraMap` for the other, which is
what `ComplexAnalytic.AnalyticSpace.glueMorphismsOfGlueData` does for an arbitrary datum. So this
construction is an instance of that one and not a sibling of it, and the general declaration was
written after this one rather than the other way round.

It is `rfl` because `ComplexAnalytic.coverAnalytification` *is*
`ComplexAnalytic.AnalyticSpace.ofGlueDataCLinear` at `ComplexAnalytic.coverGlueData` and
`ComplexAnalytic.coverAnalytificationOpenCover` *is* that datum's own cover, which is the same
reason `ComplexAnalytic.toLRSHom_coverGlueMorphisms` is `rfl`. -/
theorem coverGlueMorphisms_eq_glueMorphismsOfGlueData {Y : AnalyticSpace.{u}}
    (f : ∀ i, AnalyticSpace.analytification.{u} (obj i).g ⟶ Y)
    (h : ∀ i j : J, i ≠ j → coverIncl.{u} obj poly i j ≫ (f i).toLRSHom =
      (coverTransition.{u} obj poly glue i j).hom ≫
        coverIncl.{u} obj poly j i ≫ (f j).toLRSHom) :
    coverGlueMorphisms.{u} obj poly glue hrange hsymm hcocycle f h =
      AnalyticSpace.glueMorphismsOfGlueData
        (coverGlueData.{u} obj poly glue hrange hsymm hcocycle)
        (fun i ↦ (AnalyticSpace.analytification.{u} (obj i).g).algebraMap)
        (glueDataCLinear_coverGlueData.{u} obj poly glue hrange hsymm hcocycle)
        (fun i ↦ (AnalyticSpace.analytification.{u} (obj i).g).local_model)
        (fun i ↦ (f i).toLRSHom)
        (comm_coverGlueData.{u} obj poly glue hrange hsymm hcocycle (fun i ↦ (f i).toLRSHom) h)
        (fun i ↦ (f i).isCLinear) :=
  rfl

/-- **Its underlying morphism is the glue datum's**, by `rfl` — the same three `rfl`s that make
`ComplexAnalytic.coverAnalytificationOpenCover` a cover of `X^an` on the nose. -/
@[simp]
theorem toLRSHom_coverGlueMorphisms {Y : AnalyticSpace.{u}}
    (f : ∀ i, AnalyticSpace.analytification.{u} (obj i).g ⟶ Y)
    (h : ∀ i j : J, i ≠ j → coverIncl.{u} obj poly i j ≫ (f i).toLRSHom =
      (coverTransition.{u} obj poly glue i j).hom ≫
        coverIncl.{u} obj poly j i ≫ (f j).toLRSHom) :
    (coverGlueMorphisms.{u} obj poly glue hrange hsymm hcocycle f h).toLRSHom =
      (coverGlueData.{u} obj poly glue hrange hsymm hcocycle).glueMorphisms
        (fun i ↦ (f i).toLRSHom)
        (comm_coverGlueData.{u} obj poly glue hrange hsymm hcocycle _ h) :=
  rfl

/-- **It restricts to the given morphism on each member**, which is what a caller consumes. -/
@[reassoc (attr := simp)]
theorem coverIota_comp_coverGlueMorphisms {Y : AnalyticSpace.{u}}
    (f : ∀ i, AnalyticSpace.analytification.{u} (obj i).g ⟶ Y)
    (h : ∀ i j : J, i ≠ j → coverIncl.{u} obj poly i j ≫ (f i).toLRSHom =
      (coverTransition.{u} obj poly glue i j).hom ≫
        coverIncl.{u} obj poly j i ≫ (f j).toLRSHom) (i : J) :
    coverIota.{u} obj poly glue hrange hsymm hcocycle i ≫
        coverGlueMorphisms.{u} obj poly glue hrange hsymm hcocycle f h = f i :=
  AnalyticSpace.forgetToLocallyRingedSpace.{u}.map_injective <| by
    change (coverIota.{u} obj poly glue hrange hsymm hcocycle i).toLRSHom ≫
      (coverGlueMorphisms.{u} obj poly glue hrange hsymm hcocycle f h).toLRSHom = (f i).toLRSHom
    exact LocallyRingedSpace.GlueData.ι_glueMorphisms
      (coverGlueData.{u} obj poly glue hrange hsymm hcocycle) (fun i ↦ (f i).toLRSHom)
      (comm_coverGlueData.{u} obj poly glue hrange hsymm hcocycle _ h) i

/-- **And it is the only morphism that does.**

`AlgebraicGeometry.LocallyRingedSpace.GlueData.hom_ext` through the faithfulness of
`ComplexAnalytic.AnalyticSpace.forgetToLocallyRingedSpace`, which is why no `ℂ`-linear version of
the uniqueness statement is needed. -/
theorem coverAnalytification_hom_ext {Y : AnalyticSpace.{u}}
    (φ ψ : coverAnalytification.{u} obj poly glue hrange hsymm hcocycle ⟶ Y)
    (h : ∀ i, coverIota.{u} obj poly glue hrange hsymm hcocycle i ≫ φ =
      coverIota.{u} obj poly glue hrange hsymm hcocycle i ≫ ψ) : φ = ψ :=
  AnalyticSpace.forgetToLocallyRingedSpace.{u}.map_injective <|
    LocallyRingedSpace.GlueData.hom_ext _ _ _ fun i ↦
      congrArg AnalyticSpace.forgetToLocallyRingedSpace.{u}.map (h i)

/-- **The members' inclusions into `X^an` agree over the overlaps**, in this file's own
vocabulary: the transition from the `i`-th member to the `j`-th commutes with the two inclusions.

`CategoryTheory.GlueData.comm_of_ofGlueData'_comm` at
`CategoryTheory.GlueData.glue_condition`, which is the same statement about
`ComplexAnalytic.coverGlueData`'s `f` and `t` and so is not directly usable. -/
theorem coverIncl_comp_coverIota (i j : J) (hij : i ≠ j) :
    coverIncl.{u} obj poly i j ≫
        (coverIota.{u} obj poly glue hrange hsymm hcocycle i).toLRSHom =
      (coverTransition.{u} obj poly glue i j).hom ≫ coverIncl.{u} obj poly j i ≫
        (coverIota.{u} obj poly glue hrange hsymm hcocycle j).toLRSHom :=
  CategoryTheory.GlueData.comm_of_ofGlueData'_comm
    (coverGlueData'.{u} obj poly glue hrange hsymm hcocycle)
    (fun i ↦ (coverGlueData.{u} obj poly glue hrange hsymm hcocycle).toGlueData.ι i)
    (fun i j ↦ ((coverGlueData.{u} obj poly glue hrange hsymm hcocycle).toGlueData.glue_condition
      i j).symm) hij

/-- **The members are subspaces of `X^an` and not merely mapped into it**: the inclusion of the
`i`-th is injective on points.

`ComplexAnalytic.isOpenImmersion_coverIota` and nothing else — an open immersion of locally ringed
spaces is one whose base is an `IsOpenEmbedding`, and an open embedding is injective. Stated
because the consumers below want the *set* the `i`-th member occupies and want to intersect two of
them, and `Set.image_inter` is where an injectivity hypothesis is asked for. -/
theorem injective_base_coverIota (i : J) :
    Function.Injective
      (coverIota.{u} obj poly glue hrange hsymm hcocycle i).toLRSHom.base := by
  haveI := isOpenImmersion_coverIota.{u} obj poly glue hrange hsymm hcocycle i
  exact (PresheafedSpace.IsOpenImmersion.base_open
    (f := (coverIota.{u} obj poly glue hrange hsymm hcocycle i).toLRSHom.toShHom.hom)).injective

/-- **The two members meet where the datum says they do**, as one subset of `X^an`: the part of
the `i`-th member that meets the `j`-th and the part of the `j`-th that meets the `i`-th have the
same image.

`ComplexAnalytic.coverIncl_comp_coverIota` is the whole content, read on ranges rather than on
morphisms: the range of `ComplexAnalytic.coverIncl` is the open it restricts to
(`AlgebraicGeometry.LocallyRingedSpace.range_ofRestrict`), so each side is the range of a composite
out of `ComplexAnalytic.coverPart`, and the transition between the two composites is an
isomorphism, whose base is therefore surjective.

**This is not the statement that the two members meet in *nothing else***, which says
`Set.range` of the two inclusions intersect in exactly this set and is a statement about the
gluing rather than about the two composites. That one is
`ComplexAnalytic.range_coverIota_inter` below, proved from
`AlgebraicGeometry.LocallyRingedSpace.GlueData.ι_eq_iff` and not from anything here; this
docstring read *"nothing here is evidence about it in either direction"* until it was proved, and
that clause was true of this proof and is not a description of the tree. -/
theorem coverIota_image_coverOpen (i j : J) (hij : i ≠ j) :
    (coverIota.{u} obj poly glue hrange hsymm hcocycle i).toLRSHom.base ''
        (coverOpen.{u} obj poly i j : Set (coverSpace.{u} obj i)) =
      (coverIota.{u} obj poly glue hrange hsymm hcocycle j).toLRSHom.base ''
        (coverOpen.{u} obj poly j i : Set (coverSpace.{u} obj j)) := by
  have hrangei : Set.range ⇑(coverIncl.{u} obj poly i j).base =
      (coverOpen.{u} obj poly i j : Set (coverSpace.{u} obj i)) :=
    (coverSpace.{u} obj i).range_ofRestrict (coverOpen.{u} obj poly i j)
  have hrangej : Set.range ⇑(coverIncl.{u} obj poly j i).base =
      (coverOpen.{u} obj poly j i : Set (coverSpace.{u} obj j)) :=
    (coverSpace.{u} obj j).range_ofRestrict (coverOpen.{u} obj poly j i)
  rw [← hrangei, ← hrangej, ← Set.range_comp, ← Set.range_comp]
  change Set.range ⇑(coverIncl.{u} obj poly i j ≫
      (coverIota.{u} obj poly glue hrange hsymm hcocycle i).toLRSHom).base = _
  rw [coverIncl_comp_coverIota.{u} obj poly glue hrange hsymm hcocycle i j hij]
  change Set.range (⇑(coverIncl.{u} obj poly j i ≫
      (coverIota.{u} obj poly glue hrange hsymm hcocycle j).toLRSHom).base ∘
      ⇑(coverTransition.{u} obj poly glue i j).hom.base) = _
  have hsurj : Set.range ⇑(coverTransition.{u} obj poly glue i j).hom.base = Set.univ :=
    Set.range_eq_univ.2
      (LocallyRingedSpace.homeoOfIso (coverTransition.{u} obj poly glue i j)).surjective
  rw [Set.range_comp, hsurj, Set.image_univ]
  rfl

/-- **Gluing the members' own inclusions returns the identity of `X^an`.**

The round trip, and the readable form of `ComplexAnalytic.coverIota_comp_coverGlueMorphisms`: the
proof below is that lemma and `Category.comp_id`, so this is its instance at
`f = ComplexAnalytic.coverIota` and not an independent statement. **The statement that rules out a
definition ignoring its family is therefore that one**; a corollary in one rewrite cannot carry
content its premise lacks, and this docstring claimed it did until 2026-08-30. What this adds is
that the general lemma's instance at the members' own inclusions is the *identity* — which is a
fact about `ComplexAnalytic.coverIota` and worth a name. -/
theorem coverGlueMorphisms_coverIota :
    coverGlueMorphisms.{u} obj poly glue hrange hsymm hcocycle
        (coverIota.{u} obj poly glue hrange hsymm hcocycle)
        (coverIncl_comp_coverIota.{u} obj poly glue hrange hsymm hcocycle) = 𝟙 _ :=
  coverAnalytification_hom_ext.{u} obj poly glue hrange hsymm hcocycle _ _ fun i ↦ by
    rw [coverIota_comp_coverGlueMorphisms, Category.comp_id]

/-! ### The two members meet in the overlap and in nothing else -/

/-- **The transition into the ambient member is onto `D(f_ji)`**, and not merely into it.

`ComplexAnalytic.range_coverTransitionHom_subset` is the containment, which is all
`ComplexAnalytic.coverTriple` needs; this is the equality, and it is what a statement about *which*
points of the `j`-th member are reached asks for. The extra step is that the first factor of
`ComplexAnalytic.coverTransitionHom` is an isomorphism, hence surjective on points
(`AlgebraicGeometry.LocallyRingedSpace.homeoOfIso`), so the range of the composite is the range of
`ComplexAnalytic.coverIncl`, which is
`AlgebraicGeometry.LocallyRingedSpace.range_ofRestrict`. **Nothing about the input enters here
either** — the containment and the equality are both true of every `glue`. -/
theorem range_coverTransitionHom (i j : J) :
    Set.range (coverTransitionHom.{u} obj poly glue i j).base =
      (coverOpen.{u} obj poly j i : Set (coverSpace.{u} obj j)) := by
  rw [coverTransitionHom, LocallyRingedSpace.comp_base, TopCat.coe_comp, Set.range_comp]
  have hs : Set.range ⇑(coverTransition.{u} obj poly glue i j).hom.base = Set.univ :=
    Set.range_eq_univ.2
      (LocallyRingedSpace.homeoOfIso (coverTransition.{u} obj poly glue i j)).surjective
  rw [hs, Set.image_univ]
  exact ((coverSpace.{u} obj j).range_ofRestrict (coverOpen.{u} obj poly j i))

/-- **What of the `j`-th member lies in the `i`-th is exactly `D(f_ji)`**: the preimage along the
`j`-th member's inclusion of where the `i`-th member sits is the open the datum says the two meet
in.

This is the statement `ComplexAnalytic.coverIota_image_coverOpen`'s docstring records as *not*
being it: that one compares two composites out of `ComplexAnalytic.coverPart` and holds because
the transition between them is an isomorphism, and it is silent about points of the two members
that are identified for some *other* reason. This one is about the gluing, and what settles it is
`AlgebraicGeometry.LocallyRingedSpace.GlueData.ι_eq_iff` — the description of when two points of
two members become one point of `X^an`, which says they do exactly when a point of the overlap
carries one to the other.

The unfolding is the two `eqToHom`s `CategoryTheory.GlueData.ofGlueData'` inserts:
`CategoryTheory.GlueData.ofGlueData'_t_comp_f_of_ne` puts the glue datum's `t i j ≫ f j i` at
`ComplexAnalytic.coverTransitionHom` after one of them, and an `eqToHom` is an isomorphism, so
the two have the same range — which `ComplexAnalytic.range_coverTransitionHom` computes.

**The hypothesis `i ≠ j` is not removable**, and not for a bookkeeping reason: at `i = j` the glue
datum's `V (i, i)` is the member itself and the statement would read `D(f_ii) = ⊤`, which the
input does not supply. -/
theorem preimage_range_coverIota (i j : J) (hij : i ≠ j) :
    (coverIota.{u} obj poly glue hrange hsymm hcocycle j).toLRSHom.base ⁻¹'
        Set.range (coverIota.{u} obj poly glue hrange hsymm hcocycle i).toLRSHom.base =
      (coverOpen.{u} obj poly j i : Set (coverSpace.{u} obj j)) := by
  have hcomp : (coverGlueData.{u} obj poly glue hrange hsymm hcocycle).toGlueData.t i j ≫
      (coverGlueData.{u} obj poly glue hrange hsymm hcocycle).toGlueData.f j i =
      eqToHom (dif_neg hij) ≫ coverTransitionHom.{u} obj poly glue i j :=
    CategoryTheory.GlueData.ofGlueData'_t_comp_f_of_ne
      (coverGlueData'.{u} obj poly glue hrange hsymm hcocycle) hij
  have hrangeeq : Set.range ⇑((coverGlueData.{u} obj poly glue hrange hsymm hcocycle).toGlueData.t
        i j ≫ (coverGlueData.{u} obj poly glue hrange hsymm hcocycle).toGlueData.f j i).base =
      Set.range (coverTransitionHom.{u} obj poly glue i j).base := by
    rw [hcomp, LocallyRingedSpace.comp_base]
    have hs : Set.range ⇑(eqToHom (dif_neg hij) :
        (coverGlueData.{u} obj poly glue hrange hsymm hcocycle).toGlueData.V (i, j) ⟶
          coverPart.{u} obj poly i j).base = Set.univ :=
      Set.range_eq_univ.2 (LocallyRingedSpace.homeoOfIso
        (asIso (eqToHom (dif_neg hij) :
          (coverGlueData.{u} obj poly glue hrange hsymm hcocycle).toGlueData.V (i, j) ⟶
            coverPart.{u} obj poly i j))).surjective
    change Set.range (⇑(coverTransitionHom.{u} obj poly glue i j).base ∘
      ⇑(eqToHom (dif_neg hij) :
        (coverGlueData.{u} obj poly glue hrange hsymm hcocycle).toGlueData.V (i, j) ⟶
          coverPart.{u} obj poly i j).base) = _
    rw [Set.range_comp, hs, Set.image_univ]
  rw [← range_coverTransitionHom.{u} obj poly glue i j, ← hrangeeq]
  ext x
  simp only [Set.mem_preimage, Set.mem_range]
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨z, hz1, hz2⟩ :=
      ((coverGlueData.{u} obj poly glue hrange hsymm hcocycle).ι_eq_iff i j y x).1 hy
    exact ⟨z, hz2⟩
  · rintro ⟨z, hz⟩
    refine ⟨((coverGlueData.{u} obj poly glue hrange hsymm hcocycle).toGlueData.f i j).base z, ?_⟩
    exact ((coverGlueData.{u} obj poly glue hrange hsymm hcocycle).ι_eq_iff i j _ x).2
      ⟨z, rfl, hz⟩

/-- **The two members meet in nothing else**: where they meet in `X^an` is the image of the open
the datum says they meet in.

`ComplexAnalytic.preimage_range_coverIota` read as an image —
`Set.image_preimage_eq_inter_range` — and then carried from the `j`-th member to the `i`-th by
`ComplexAnalytic.coverIota_image_coverOpen`.

**This is the statement whose absence that lemma's docstring recorded**, and the two are worth
keeping apart: it says `D(f_ij)` and `D(f_ji)` have the same image, which is a fact about the two
composites, and this says that image is the *whole* of the intersection of the two members, which
is a fact about the gluing. -/
theorem range_coverIota_inter (i j : J) (hij : i ≠ j) :
    Set.range (coverIota.{u} obj poly glue hrange hsymm hcocycle i).toLRSHom.base ∩
        Set.range (coverIota.{u} obj poly glue hrange hsymm hcocycle j).toLRSHom.base =
      (coverIota.{u} obj poly glue hrange hsymm hcocycle i).toLRSHom.base ''
        (coverOpen.{u} obj poly i j : Set (coverSpace.{u} obj i)) := by
  rw [coverIota_image_coverOpen.{u} obj poly glue hrange hsymm hcocycle i j hij,
    ← preimage_range_coverIota.{u} obj poly glue hrange hsymm hcocycle i j hij,
    Set.image_preimage_eq_inter_range]

/-- **The transition, read on the overlap's own space, is the analytified glue followed by the
projection into the other member.**

`ComplexAnalytic.coverTransition` is the analytified glue conjugated by
`ComplexAnalytic.coverOverlapIso` at each end; precomposing with that isomorphism cancels the
first conjugating factor, and `ComplexAnalytic.coverOverlapIso_hom_coverIncl` turns the second
into `ComplexAnalytic.localisationProj`. Nothing is proved here that is not in those two — what
the lemma supplies is the *spelling*, in which both sides are morphisms out of
`(A_i)_{f_ij}^an` and the algebra is on the right of the equation.

**This is what makes a statement about the two members' opens computable.** The overlap's own
space is where a polynomial of either member is read as a class in the overlap algebra, and this
says the two readings differ by the analytified glue and by nothing else. -/
theorem coverOverlapIso_hom_coverTransitionHom (i j : J) :
    (coverOverlapIso.{u} obj poly i j).hom ≫ coverTransitionHom.{u} obj poly glue i j =
      (coverGlueIso.{u} obj poly glue i j).hom ≫
        (localisationProj.{u} (obj j).g (poly j i)).toLRSHom := by
  rw [coverTransitionHom, coverTransition, Iso.trans_hom, Iso.trans_hom, Iso.symm_hom,
    ← Category.assoc, ← Category.assoc, Iso.hom_inv_id, Category.id_comp, Category.assoc,
    coverOverlapIso_hom_coverIncl]

/-- **A point of the overlap has one image in `X^an`, computed on either side.**

The previous lemma and `ComplexAnalytic.coverIncl_comp_coverIota` composed and read at a point:
going down into the `i`-th member and including that, or crossing by the analytified glue and
going down into the `j`-th member and including that, give the same point.

Stated pointwise rather than as an equation of morphisms because its consumers are computations
with images of *sets*, where `Set.image_congr'` wants a function equality and a categorical one
would have to be pushed through `AlgebraicGeometry.LocallyRingedSpace.comp_base` at each use. -/
theorem base_coverIota_localisationProj (i j : J) (hij : i ≠ j)
    (w : AnalyticSpace.analytification.{u}
      (localisationPresentation.{u} (obj i).g (poly i j))) :
    (coverIota.{u} obj poly glue hrange hsymm hcocycle i).toLRSHom.base
        ((localisationProj.{u} (obj i).g (poly i j)).toLRSHom.base w) =
      (coverIota.{u} obj poly glue hrange hsymm hcocycle j).toLRSHom.base
        ((localisationProj.{u} (obj j).g (poly j i)).toLRSHom.base
          ((coverGlueIso.{u} obj poly glue i j).hom.base w)) := by
  have e : (localisationProj.{u} (obj i).g (poly i j)).toLRSHom ≫
      (coverIota.{u} obj poly glue hrange hsymm hcocycle i).toLRSHom =
      (coverGlueIso.{u} obj poly glue i j).hom ≫
        (localisationProj.{u} (obj j).g (poly j i)).toLRSHom ≫
          (coverIota.{u} obj poly glue hrange hsymm hcocycle j).toLRSHom := by
    have e2 : (coverTransition.{u} obj poly glue i j).hom ≫ coverIncl.{u} obj poly j i =
        coverTransitionHom.{u} obj poly glue i j := rfl
    rw [← coverOverlapIso_hom_coverIncl.{u} obj poly i j, Category.assoc,
      coverIncl_comp_coverIota.{u} obj poly glue hrange hsymm hcocycle i j hij,
      ← Category.assoc ((coverTransition.{u} obj poly glue i j).hom), e2, ← Category.assoc,
      coverOverlapIso_hom_coverTransitionHom.{u} obj poly glue i j, Category.assoc]
  exact congrArg (fun m ↦ (ConcreteCategory.hom m.base) w) e

/-- **A distinguished open of the overlap's own space, pushed down into the member it lies over.**

For a polynomial of the `i`-th member read in the localisation's extra variable, the image under
the projection of the open it cuts out of `(A_i)_{f_ij}^an` is `D(f_ij) ⊓ D(x)` inside `A_i^an`.

`ComplexAnalytic.localisationOpen_rename` says the open upstairs is the preimage of `D(x)`, and
`ComplexAnalytic.range_base_localisationProj` — the **equality**, not the containment — says the
range of the projection is `D(f_ij)`; the image of a preimage is the set met with the range. -/
theorem image_localisationOpen_localisationProj (i j : J)
    (x : MvPolynomial (ULift.{u} (Fin (obj i).n)) ℂ) :
    (localisationProj.{u} (obj i).g (poly i j)).toLRSHom.base ''
        (localisationOpen.{u} (localisationPresentation.{u} (obj i).g (poly i j))
          (MvPolynomial.rename (localisationIncl.{u} (obj i).n) x) :
          Set (AnalyticSpace.analytification.{u}
            (localisationPresentation.{u} (obj i).g (poly i j)))) =
      (coverOpen.{u} obj poly i j : Set (coverSpace.{u} obj i)) ∩
        (localisationOpen.{u} (obj i).g x :
          Set (AnalyticSpace.analytification.{u} (obj i).g)) := by
  have hpre : (localisationOpen.{u} (localisationPresentation.{u} (obj i).g (poly i j))
      (MvPolynomial.rename (localisationIncl.{u} (obj i).n) x) :
      Set (AnalyticSpace.analytification.{u}
        (localisationPresentation.{u} (obj i).g (poly i j)))) =
      ⇑(localisationProj.{u} (obj i).g (poly i j)).toLRSHom.base ⁻¹'
        (localisationOpen.{u} (obj i).g x :
          Set (AnalyticSpace.analytification.{u} (obj i).g)) := by
    rw [localisationOpen_rename.{u} (obj i).g (poly i j) x]
    rfl
  rw [hpre, Set.image_preimage_eq_inter_range,
    range_base_localisationProj.{u} (obj i).g (poly i j)]
  exact Set.inter_comm _ _

end

end ComplexAnalytic
