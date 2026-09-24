/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Analytification.RefineDatumCocycle

/-!
# The morphism from a cross-member refinement down to the cover it refines

`Oka/Analytification/RefineDatumCocycle.lean` ends with
`ComplexAnalytic.refineDatumAnalytificationOfLaws`, the analytic space a cross-member refined
cover datum glues to, and its `## What is not here` records what is missing next:

> * **Nothing that says the refined cover's analytic space is the original one.** It is a space,
>   and `ComplexAnalytic.not_isIso_refineToBase` says at a constant `σ` that the comparison need
>   not be an isomorphism; **there is no morphism between the two gluings here in either
>   direction.**

**This file supplies one direction of it**, as `ComplexAnalytic.refineDatumToBase`. The other
direction is still absent and this file says nothing about it.

## The price two files quote for this is the one-member case's price, and it is not owed here

`Oka/Analytification/CoverIndependence.lean` and `Oka/Analytification/CoverRefinement.lean` both
say a literal `ComplexAnalytic.coverMap` out of a refinement is blocked, and both give the same
reason — that it *"needs `A^an` presented as a one-member cover datum and that gluing identified
with `A^an`, an identification nothing in this repository states"*.

**That is a true statement about `ComplexAnalytic.refineToBase` and a false prediction about this
one.** `coverMap` goes between two *cover data*. The one-member refinement's target is a single
`ComplexAnalytic.Presentation`, so presenting it as a cover datum and identifying the gluing with
its member is exactly what stands in the way there — `refineToBase`'s own docstring says so and
glues the projections instead. **A cross-member refinement's target is
`ComplexAnalytic.coverAnalytification` of the original datum, which is already a cover datum**, so
neither step exists to be paid and `coverMap` applies with nothing in between. The obstruction was
never about refinement; it was about the shape of the target, and the shape changed when the
refinement did.

## What the instantiation costs, and the two squares were already theorems

`ComplexAnalytic.coverMap` asks for a map of index types, a morphism of presentations over it, and
one geometric hypothesis:

* **`σ`** is the refinement's own index map, unchanged.
* **`ψ`** is `ComplexAnalytic.localisationHom`, whose direction convention is already the one
  `coverMap` wants — `Oka/Analytification/CoverIndependence.lean` records that and records that it
  was measured — and whose source is `ComplexAnalytic.refineDatumObj` on the nose, that being an
  `abbrev` for the very `ComplexAnalytic.Presentation` `localisationHom` is declared at.
* **`hcomm`** is `ComplexAnalytic.comm_refineDatumMapPart` below, and it is two theorems this line
  already had, one per branch of the case split on `σ a = σ b`:
  `ComplexAnalytic.refineDatumTransitionHom_localisationProj_of_ne`
  (`Oka/Analytification/RefineDatumTransition.lean`) puts the refined transition over the
  *original datum's own transition*, which the members' inclusions then absorb by
  `ComplexAnalytic.coverIncl_comp_coverIota`; and
  `ComplexAnalytic.refineDatumTransitionHom_localisationProj_of_eq`
  (`Oka/Analytification/RefineDatumRange.lean`) puts it over its member across an identification,
  which `ComplexAnalytic.coverSpaceHomOfEq_comp_coverIota` absorbs.

**The second of those two absorptions is the only thing the tree did not have**, and it is `subst`
followed by `ComplexAnalytic.coverSpaceHomOfEq_refl`. It is in
`Oka/Analytification/RefineDatumRange.lean` rather than here, under the placement rule
`Oka/Analytification/RefineDatumCocycle.lean` states; that file's docstring gives the argument.

## `hcomm` holds at every pair and `coverMap` only asks for it at `a ≠ b`

`ComplexAnalytic.comm_refineDatumMapPart` is stated at **every** ordered pair of `B`, with no
`a ≠ b`. That is not a strengthening anybody planned: the hypothesis was written with `a ≠ b` and
the proof never used it, because the case split that runs the proof is on `σ a = σ b` and both
branches are theorems at every pair. `ComplexAnalytic.coverMap` is then fed
`fun a b _ ↦ …`. Nothing below consumes the extra generality; it is recorded because a hypothesis
that turns out to be inert is a fact about the construction and not a tidying detail.

## The first `coverMap` whose compatibility is discharged outside its home file

**Where the qualifier comes from, since an earlier draft of this heading did without it and was
false.** `ComplexAnalytic.coverMap`'s compatibility hypothesis is already discharged twice inside
`Oka/Analytification/CoverFunctoriality.lean`, by the two functor laws:
`ComplexAnalytic.coverMap_id` is fed `ComplexAnalytic.comm_coverMapPart_id`, and
`ComplexAnalytic.coverMap_comp` is fed `ComplexAnalytic.comm_coverMapPart_comp`, which
`ComplexAnalytic.coverMap_comp`'s own docstring says in terms — it calls the composite's
compatibility that lemma *"rather than a hypothesis a caller has to supply"*.

**Both are the functor laws' own data**: `id` with `fun i ↦ 𝟙 (obj i)`, and the
composite `τ ∘ σ` with `fun i ↦ ψ i ≫ χ (σ i)` of two cover maps a caller supplies — and the
second proves nothing from nothing, deriving the composite's hypothesis from the two `hcomm`s of
the morphisms being composed. **So the qualifier is the whole of what this section claims**, and
what is new below is the data the discharge is at rather than the fact of a discharge.

`Oka/Analytification/CoverFunctoriality.lean`'s `## What is not here` says *"No non-identity
instance. Nothing below exhibits a `σ` and a `ψ` other than the identity."* **That bullet is about
that file and is still true of it**, and the census outside it separates two things a count would
conflate. Outside its home file, `ComplexAnalytic.coverMap` is *applied* by these declarations and
no others — named rather than counted, because a count of the contents of one directory is a dated
claim with no instrument watching it:

* `Oka/Analytification/CoverIndependence.lean` — `ComplexAnalytic.coverMap_hom_inv`,
  `ComplexAnalytic.coverMap_inv_hom`, `ComplexAnalytic.coverAnalytificationIso`,
  `ComplexAnalytic.coverMap_reindex_hom_inv`, `ComplexAnalytic.coverMap_reindex_inv_hom`,
  `ComplexAnalytic.coverAnalytificationReindexIso`;
* `Oka/Analytification/ComparisonSquare.lean` —
  `ComplexAnalytic.toLRSHom_coverMap_comp_analytificationToSpecGlued`.

**At every one of them `σ` is `id` or an `Equiv` the caller hands over, `ψ` is an isomorphism the
caller hands over, and `hcomm` is a hypothesis.** So the discharges are the two named above and
both are inside the home file: `ComplexAnalytic.comm_coverMapPart_id` unconditionally, for the
identity data, and `ComplexAnalytic.comm_coverMapPart_comp` conditionally, from two hypotheses of
the same shape.

So what is new here is not "a non-identity `σ`" but **a `σ` that is an arbitrary map of index
types, a `ψ` this repository constructs, and an `hcomm` proved *of that data*, from the geometry
of the refinement** — and of the three it is the third that was the open question, since the first
two are one line each and `Oka/Analytification/CoverIndependence.lean` had already said so.

## No `rw` here names a definition, and that is measured rather than stylistic

Both proofs below are one step away from the obvious `rw [coverMapPart, …]` and
`rw [refineDatumToBase, …]`, and both spellings were written first. Naming a definition as a
rewrite rule asks Lean to generate its equation lemma, and `scripts/DumpOkaDecls.lean` on that
draft reports **nine** declarations for this branch where it declares seven: the extra two are
`ComplexAnalytic.refineDatumToBase.eq_1` and `ComplexAnalytic.coverMapPart.eq_1` — and the second
belongs to `Oka/Analytification/CoverFunctoriality.lean`, so this module was adding a lemma to
another file's definition.

`Oka/Analytification/RefineDatumRange.lean` and `Oka/Analytification/RefineDatumCocycle.lean`
record the same hazard by two other routes, a `simp only` naming nothing and
`CategoryTheory.reassoc_of%`; **this is the third route and the one hardest to avoid by taste,
because naming the definition is what the proof is *about*.** What replaces it is `congrArg` and
`Eq.trans` at the definition's own unfolding, which go through definitional unfolding and generate
nothing. `Δdump` is the number of declarations a branch adds and no more, and that equality is the
figure to check a branch on this file by.

## Main definitions

- `ComplexAnalytic.refineDatumPresHom`: **the `b`-th refined member's morphism down to the member
  it lies over**, which is `ComplexAnalytic.localisationHom` named in this file's vocabulary.
- `ComplexAnalytic.refineDatumToBase`: **the morphism from the refined cover's analytic space to
  the original cover's**, which is what this file exists for.

## Main results

- `ComplexAnalytic.comm_refineDatumMapPart`: **the members' morphisms agree over the refined
  overlaps** — `ComplexAnalytic.coverMap`'s hypothesis, discharged, at every ordered pair.
- `ComplexAnalytic.coverIota_comp_refineDatumToBase`: **it restricts on the `b`-th refined member
  to that member's projection followed by the inclusion of the `σ b`-th member.** This is the
  statement that says the construction is the intended one rather than a well-typed one; a
  definition ignoring `fam` would satisfy the type and nothing else here.
- `ComplexAnalytic.refineDatumToBase_unique`: **and it is the only morphism that does.**

## What is not here

* **No morphism in the other direction, and no claim that this one is an isomorphism.**
  `ComplexAnalytic.not_isIso_refineToBase` is the one-member analogue and it is a *negative* about
  a different morphism; nothing here inherits from it in either direction, and nothing here is a
  conjecture. What would make a comparison an isomorphism is the condition
  `Oka/Analytification/CoverRefinement.lean` names — that the refining family covers — and this
  file does not state it. **The clause here that said nobody had stated it is retired**:
  `Oka/Analytification/RefineDatumCover.lean` states it, as
  `ComplexAnalytic.RefineDatumCovers`. **That does not weaken this bullet and the distinction is
  the whole of why not**: what that condition buys there is that the base map of the morphism
  below is *surjective*, and a surjection is not an isomorphism. Nothing anywhere says a word
  about injectivity or about a morphism back, which is what both halves of this bullet are.
* **Nothing *below* that says the refined datum covers the original space, and this bullet said
  nothing anywhere did.** The surjectivity of this morphism is not proved, stated or needed in
  this file, and nothing below changes; what is retired is the general half.
  `Oka/Analytification/RefineDatumCover.lean` computes the image of the morphism below outright —
  the union of the images of the `D(fam b)`, on no hypothesis at all — and proves the base map
  surjective when the refining family covers, with an instance at
  `Oka/Analytification/RefineDatumWitness.lean`'s trivial family and a concrete one at the node.
  `Oka/Analytification/CrossMemberDatum.lean`'s *"No statement that the refined data cover
  anything"* is narrowed there too, and its remaining half — that the refined overlaps are cut out
  where `ComplexAnalytic.refineDatumPoly` says they are — is a statement about that definition and
  is untouched by any of it. It is settled elsewhere and, since 2026-09-04, outright:
  `Oka/Analytification/RefineDatumRefines.lean` proves it wherever the two refined members lie
  over one member of the original cover, and `Oka/Analytification/RefineDatumRefinesCross.lean`
  proves it where they lie over two, at a family of extra factors it produces — this sentence read
  *"only in part"* and named the containment that was all the second case had. **That bears on
  this bullet in neither half**: it is about `ComplexAnalytic.refineDatumMemberIota`,
  which reads no refined datum, and an equality of images says nothing about the morphism below or
  about its fibres.
* **No general form taking the refined cocycle law as an argument**, unlike
  `ComplexAnalytic.refineDatumGlueData` beside
  `ComplexAnalytic.refineDatumGlueDataOfLaws`. There would be no such thing to state: the
  **target** is `ComplexAnalytic.coverAnalytification` of the original datum, which takes that
  datum's own `hcocycle`, so a caller must have it whatever the source is stated at — and with it
  in hand `ComplexAnalytic.refineDatumHcocycle` supplies the refined law for nothing. The
  `…OfLaws` spelling is the only one with a caller.
* **No functor law.** That this morphism is compatible with `ComplexAnalytic.coverMap_comp` for a
  refinement of a refinement is not stated, and there is no refinement of a refinement in the
  repository to state it at.
* **No `Spec` side, no scheme and no `admissible`**, as in the files this one sits beside.
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
  (glue : ∀ i j : J, coverOverlap.{u} obj poly i j ≅ coverOverlap.{u} obj poly j i)
  (rr : ∀ _ b : B, MvPolynomial (ULift.{u} (Fin ((obj (σ b)).n + 1))) ℂ)
  (uu : ∀ a b : B, (PresentedAlgebra.{u} ((obj (σ b)).n + 1) ((obj (σ b)).k + 1)
    (localisationPresentation.{u} (obj (σ b)).g (poly (σ b) (σ a))))ˣ)
  (he : ∀ a b : B, ∀ _ : σ a ≠ σ b,
    RefineDatumCrossEq.{u} obj σ fam poly q glue a b (rr a b))
  (hu : ∀ a b : B, ∀ _ : σ a ≠ σ b,
    RefineDatumCrossUnit.{u} obj σ fam poly q a b (rr a b) (uu a b))
  (hsym : ∀ i j : J, glue j i = (glue i j).symm)
  (hrange : ∀ i j k : J, i ≠ j → i ≠ k → j ≠ k →
    Set.range (coverTripleIncl.{u} obj poly i j k ≫
        coverTransitionHom.{u} obj poly glue i j).base ⊆
      (coverOpen.{u} obj poly j k : Set (coverSpace.{u} obj j)))
  (hq : RefineDatumRangeCross.{u} obj poly σ fam q glue rr uu he hu)
  (hf : RefineDatumRangeEq.{u} obj poly σ fam q glue rr uu he hu)
  (hcocycle : ∀ i j k : J, ∀ hij : i ≠ j, ∀ hik : i ≠ k, ∀ hjk : j ≠ k,
    coverTriple.{u} obj poly glue hrange i j k hij hik hjk ≫
      coverTriple.{u} obj poly glue hrange j k i hjk hij.symm hik.symm ≫
        coverTriple.{u} obj poly glue hrange k i j hik.symm hjk.symm hij = 𝟙 _)

/-! ### The member morphism -/

/-- **The `b`-th refined member's morphism down to the member it lies over**, as a morphism of
`ComplexAnalytic.Presentation` in the direction `ComplexAnalytic.coverMap` asks for.

It is `ComplexAnalytic.localisationHom` and nothing else, and the two types match on the nose:
`ComplexAnalytic.refineDatumObj` is an `abbrev` for
`⟨(obj (σ b)).n + 1, (obj (σ b)).k + 1, localisationPresentation (obj (σ b)).g (fam b)⟩`, which is
the source `localisationHom` is declared at. **An `abbrev` and not a `def`**, so that the
statements below reduce through it without a lemma; it exists to keep
`ComplexAnalytic.coverMapPart`'s arguments readable and carries no content. -/
abbrev refineDatumPresHom (b : B) : refineDatumObj.{u} obj σ fam b ⟶ obj (σ b) :=
  localisationHom.{u} (obj (σ b)).g (fam b)

/-! ### The compatibility over the overlaps -/

/-- **The members' morphisms agree over the refined overlaps**, which is
`ComplexAnalytic.coverMap`'s one hypothesis and the whole content of this file.

The proof is one case split and two squares that already exist. Reading the refined transition down
to `obj (σ b)^an` and then into the glued space:

* at **`σ a ≠ σ b`**, `ComplexAnalytic.refineDatumTransitionHom_localisationProj_of_ne` puts it
  over `ComplexAnalytic.coverTransitionHom` of the *original* datum;
  `ComplexAnalytic.coverIncl_comp_coverIota` turns that transition-then-inclusion into the
  `σ a`-th inclusion, and `ComplexAnalytic.refineDatumCrossPart_coverIncl` — which says the refined
  overlap included into the `a`-th refined member and projected down is the comparison followed
  into the original overlap — closes it;
* at **`σ a = σ b`**, `ComplexAnalytic.refineDatumTransitionHom_localisationProj_of_eq` puts it
  over the `a`-th member across `ComplexAnalytic.coverSpaceHomOfEq`, and
  `ComplexAnalytic.coverSpaceHomOfEq_comp_coverIota` absorbs the identification into the
  inclusion.

**There is no `a ≠ b` hypothesis and there was one in the draft.** The split that runs the proof is
on `σ a = σ b`, both branches hold at every ordered pair, and the unused-variable linter is what
reported it. `ComplexAnalytic.refineDatumToBase` therefore passes `fun a b _ ↦ …`.

**The `hpart` step is a `congrArg` and not `rw [coverMapPart, …]`**, which would plant an equation
lemma on `Oka/Analytification/CoverFunctoriality.lean`'s definition; the header says what that was
measured at. `ComplexAnalytic.coverMapPart` is an `abbrev` and
`ComplexAnalytic.AnalyticSpace`'s composition is `⟨f.toLRSHom ≫ g.toLRSHom, _⟩`, so both
unfoldings the step needs are definitional and the term needs no rewrite at all.

**The two `conv_rhs` blocks are not decoration.** `Category.assoc` and its inverse are rewritten by
`rw` at the *first* occurrence, and after the first re-association both sides of the goal carry a
`(f ≫ g) ≫ h`, so an unscoped `rw [← Category.assoc]` moves the left-hand side when the right-hand
side is meant. Scoping the step is shorter than naming the morphism it should fire at. -/
theorem comm_refineDatumMapPart (a b : B) :
    coverIncl.{u} (refineDatumObj.{u} obj σ fam) (refineDatumPoly.{u} obj poly σ fam q) a b ≫
        (coverMapPart.{u} (refineDatumObj.{u} obj σ fam) obj poly glue hrange hsym hcocycle σ
          (refineDatumPresHom.{u} obj σ fam) a).toLRSHom =
      (coverTransition.{u} (refineDatumObj.{u} obj σ fam)
            (refineDatumPoly.{u} obj poly σ fam q)
            (refineDatumGlue.{u} obj σ fam poly q glue rr uu he hu) a b).hom ≫
        coverIncl.{u} (refineDatumObj.{u} obj σ fam)
            (refineDatumPoly.{u} obj poly σ fam q) b a ≫
          (coverMapPart.{u} (refineDatumObj.{u} obj σ fam) obj poly glue hrange hsym hcocycle σ
            (refineDatumPresHom.{u} obj σ fam) b).toLRSHom := by
  have hpart : ∀ c : B,
      (coverMapPart.{u} (refineDatumObj.{u} obj σ fam) obj poly glue hrange hsym hcocycle σ
          (refineDatumPresHom.{u} obj σ fam) c).toLRSHom =
        (localisationProj.{u} (obj (σ c)).g (fam c)).toLRSHom ≫
          (coverIota.{u} obj poly glue hrange hsym hcocycle (σ c)).toLRSHom := by
    intro c
    exact congrArg (· ≫ (coverIota.{u} obj poly glue hrange hsym hcocycle (σ c)).toLRSHom)
      (congrArg AnalyticSpace.Hom.toLRSHom
        (analytificationFunctor_map_localisationPresHom.{u} (obj (σ c)).g (fam c)))
  rw [hpart a, hpart b]
  conv_rhs => rw [← Category.assoc, ← coverTransitionHom, ← Category.assoc]
  by_cases h : σ a = σ b
  · rw [refineDatumTransitionHom_localisationProj_of_eq (he := he) (hu := hu) (h := h),
      Category.assoc, Category.assoc, coverSpaceHomOfEq_comp_coverIota]
  · rw [refineDatumTransitionHom_localisationProj_of_ne (he := he) (hu := hu) (h := h)]
    conv_rhs => rw [Category.assoc, coverTransitionHom, Category.assoc,
      ← coverIncl_comp_coverIota obj poly glue hrange hsym hcocycle (σ a) (σ b) h]
    rw [← Category.assoc]
    conv_rhs => rw [← Category.assoc]
    rw [refineDatumCrossPart_coverIncl]

/-! ### The morphism -/

/-- **The morphism from the refined cover's analytic space down to the original cover's.**

`ComplexAnalytic.coverMap` at `σ`, at `ComplexAnalytic.refineDatumPresHom` and at the theorem
above, and **nothing is built here**: the file's content is that those three arguments exist, and
two of the three cost a line.

Stated out of `ComplexAnalytic.refineDatumAnalytificationOfLaws` rather than out of the general
`ComplexAnalytic.refineDatumAnalytification`, and that is not the shape
`Oka/Analytification/RefineDatumGlueData.lean` and `Oka/Analytification/RefineDatumCocycle.lean`
use for their pairs of definitions — see this file's `## What is not here` for why there is nothing
for a general version to be general in. -/
def refineDatumToBase :
    refineDatumAnalytificationOfLaws.{u} obj poly σ fam q glue rr uu he hu hrange hq hf hsym
        hcocycle ⟶
      coverAnalytification.{u} obj poly glue hrange hsym hcocycle :=
  coverMap.{u} (refineDatumObj.{u} obj σ fam) (refineDatumPoly.{u} obj poly σ fam q)
    (refineDatumGlue.{u} obj σ fam poly q glue rr uu he hu)
    (refineDatumHrange.{u} obj poly σ fam q glue rr uu he hu hrange hq hf)
    (refineDatumGlue_symm.{u} obj σ fam poly q glue rr uu hsym he hu)
    (refineDatumHcocycle.{u} obj poly σ fam q glue rr uu he hu hrange hq hf hsym hcocycle)
    obj poly glue hrange hsym hcocycle σ (refineDatumPresHom.{u} obj σ fam)
    (fun a b _ ↦ comm_refineDatumMapPart.{u} obj poly σ fam q glue rr uu he hu hsym hrange
      hcocycle a b)

/-- **It restricts on the `b`-th refined member to that member's projection followed by the
inclusion of the member it lies over**, which is the statement that says this is the intended
morphism rather than a well-typed one.

`ComplexAnalytic.coverIota_comp_coverMap` and then
`ComplexAnalytic.analytificationFunctor_map_localisationPresHom`, which is what turns the functor's
value on `ComplexAnalytic.refineDatumPresHom` into `ComplexAnalytic.localisationProj`. **Both steps
are terms and neither is a `rw`** — `Eq.trans` at the first and `congrArg` under
`(· ≫ coverIota …)` at the second — for the reason this file's header gives: the `rw` form names
`ComplexAnalytic.refineDatumToBase` and plants its equation lemma.

**A definition ignoring `fam` would satisfy `ComplexAnalytic.refineDatumToBase`'s type**, and this
is the statement that rules it out. `@[reassoc (attr := simp)]` for the reason
`Oka/Analytification/CoverFunctoriality.lean` gives at the lemma this one rests on: without the
associated form a `rw [Category.assoc]` fails against a goal that displays as `(f ≫ g) ≫ h`, the
objects here carrying unreduced projections. -/
@[reassoc (attr := simp)]
theorem coverIota_comp_refineDatumToBase (b : B) :
    coverIota.{u} (refineDatumObj.{u} obj σ fam) (refineDatumPoly.{u} obj poly σ fam q)
        (refineDatumGlue.{u} obj σ fam poly q glue rr uu he hu)
        (refineDatumHrange.{u} obj poly σ fam q glue rr uu he hu hrange hq hf)
        (refineDatumGlue_symm.{u} obj σ fam poly q glue rr uu hsym he hu)
        (refineDatumHcocycle.{u} obj poly σ fam q glue rr uu he hu hrange hq hf hsym hcocycle)
        b ≫
      refineDatumToBase.{u} obj poly σ fam q glue rr uu he hu hsym hrange hq hf hcocycle =
    localisationProj.{u} (obj (σ b)).g (fam b) ≫
      coverIota.{u} obj poly glue hrange hsym hcocycle (σ b) := by
  refine Eq.trans (coverIota_comp_coverMap.{u} (refineDatumObj.{u} obj σ fam)
    (refineDatumPoly.{u} obj poly σ fam q)
    (refineDatumGlue.{u} obj σ fam poly q glue rr uu he hu)
    (refineDatumHrange.{u} obj poly σ fam q glue rr uu he hu hrange hq hf)
    (refineDatumGlue_symm.{u} obj σ fam poly q glue rr uu hsym he hu)
    (refineDatumHcocycle.{u} obj poly σ fam q glue rr uu he hu hrange hq hf hsym hcocycle)
    obj poly glue hrange hsym hcocycle σ (refineDatumPresHom.{u} obj σ fam) _ b) ?_
  exact congrArg (· ≫ coverIota.{u} obj poly glue hrange hsym hcocycle (σ b))
    (analytificationFunctor_map_localisationPresHom.{u} (obj (σ b)).g (fam b))

/-- **And it is the only morphism that restricts that way**, by
`ComplexAnalytic.coverAnalytification_hom_ext`: a morphism out of a gluing is determined by its
restrictions to the members.

It is not `ComplexAnalytic.coverMap_unique` transported, and the difference is one rewrite: that
lemma's hypothesis is stated at `analytificationFunctor.map (ψ b)` where this one's is at
`ComplexAnalytic.localisationProj`, which is the spelling a caller has. The two are the theorem
above. -/
theorem refineDatumToBase_unique
    (φ : refineDatumAnalytificationOfLaws.{u} obj poly σ fam q glue rr uu he hu hrange hq hf
        hsym hcocycle ⟶
      coverAnalytification.{u} obj poly glue hrange hsym hcocycle)
    (h : ∀ b : B,
      coverIota.{u} (refineDatumObj.{u} obj σ fam) (refineDatumPoly.{u} obj poly σ fam q)
          (refineDatumGlue.{u} obj σ fam poly q glue rr uu he hu)
          (refineDatumHrange.{u} obj poly σ fam q glue rr uu he hu hrange hq hf)
          (refineDatumGlue_symm.{u} obj σ fam poly q glue rr uu hsym he hu)
          (refineDatumHcocycle.{u} obj poly σ fam q glue rr uu he hu hrange hq hf hsym hcocycle)
          b ≫ φ =
        localisationProj.{u} (obj (σ b)).g (fam b) ≫
          coverIota.{u} obj poly glue hrange hsym hcocycle (σ b)) :
    φ = refineDatumToBase.{u} obj poly σ fam q glue rr uu he hu hsym hrange hq hf hcocycle :=
  coverAnalytification_hom_ext.{u} _ _ _ _ _ _ _ _ fun b ↦ by
    rw [h b, coverIota_comp_refineDatumToBase]

end

end ComplexAnalytic
