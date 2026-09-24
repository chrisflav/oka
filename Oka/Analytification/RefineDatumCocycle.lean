/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Analytification.RefineDatumGlueData

/-!
# The cocycle law of a cross-member refinement, and the analytic space it leaves unconditional

`Oka/Analytification/RefineDatumGlueData.lean` assembles the range law of a cross-member refined
cover datum out of five shape theorems and names the last law, `ComplexAnalytic.RefineDatumCocycle`
— *"named here and proved nowhere"*, and *"nothing on this line is evidence about it in either
direction"*. **This file proves it.** With `ComplexAnalytic.refineDatumHcocycle` the three laws a
refinement needs are all theorems at a general `σ`, and
`ComplexAnalytic.refineDatumAnalytificationOfLaws` is the analytic space a cross-member refinement
glues to, asking a caller for nothing but the original cover's own three laws and the two
conditions that file adopted.

## The obstruction on record, and which half of it was right

Four files say some version of `Oka/Analytification/CoverRefinement.lean`'s sentence — *"`hcocycle`
keeps the clause, for the reason the paragraph above gives — the cancellation is against the
projection of the one fixed member"*. **The outer cancellation is not what fails, and it transfers
with the fixed member replaced by the member the *first* index lies over.**
`ComplexAnalytic.refineDatumCocycle_of_localisationProj` is that step at a general `σ`: a morphism
into the `a`-th refined triple overlap is determined by its composite into
`obj (σ a)^an`, because that overlap is an open subspace and
`ComplexAnalytic.localisationProj` is an open immersion — and neither fact knows where `σ` sends
`b` or `c`. What has no analogue is `ComplexAnalytic.refineTriple_localisationProj`, which reads
all three transitions of the triple over *one* member; at a general `σ` they lie over three.

## What replaces it, and the finding is which law each shape spends

The composite is read down one edge at a time. Each edge has two shapes and each is a square that
already exists: at `σ a ≠ σ b` the transition lies over the original datum's own
`ComplexAnalytic.coverTransitionHom` (`Oka/Analytification/RefineDatumTransition.lean`), and at
`σ a = σ b` it lies over its member across an identification
(`Oka/Analytification/RefineDatumRange.lean`). Those are
`ComplexAnalytic.refineDatumTriple_localisationProj_of_ne` and
`ComplexAnalytic.refineDatumTriple_localisationProj_of_eq` below, and they are the whole of the
intermediate statement.

The triple then splits into the same five shapes the range law splits into — the split is the
triple's and not either law's — and **the three of them turn out to spend three different things**:

* **pairwise different members**: the original datum's own `hcocycle`, through the lift
  `ComplexAnalytic.refineDatumCrossTriple` and the square
  `ComplexAnalytic.refineDatumCrossTriple_coverTriple` below, which says the refined triple
  transition lies over the original one;
* **exactly one pair of members equal**: the original datum's own **`hsymm`**, and *not* its
  `hcocycle`. The three edges compose to a pair going out and back rather than to a triple of the
  original datum's, and they have to: with `σ a = σ b` the original index triple is
  `(σ a, σ a, σ c)`, which `ComplexAnalytic.coverTriple` does not accept. What cancels is
  `ComplexAnalytic.coverTransition_hom_comp`, added to `Oka/Analytification/AffineCover.lean`
  rather than here;
* **all three members equal**: neither, exactly as the range law's all-equal shape reads neither
  condition. The composite is three identifications of one member with itself.

**So the count of the original datum's laws this file consumes is three and not one**, and the
sentence those four files carry — that the obstruction is one cancellation against one fixed member
— named the wrong step and understated what the mixed shapes cost.

## No `CategoryTheory.reassoc_of%` below, and that is not a style choice

Every proof here walks a three-fold composite one factor at a time, which is what `reassoc_of%` is
for; **it is not used, because it plants congruence lemmas.** Measured at `1915807`, the push that
created this file: with the four `reassoc_of%`s the obvious draft has,
`scripts/DumpOkaDecls.lean` reports `Δdump` of `+31` where that push declares 27 things, and the
four extra rows are the `congr_simp` companions of
`ComplexAnalytic.coverSpaceHomOfEq`, `ComplexAnalytic.refineDatumGlue`,
`ComplexAnalytic.refineDatumCrossTriple` and `ComplexAnalytic.refineDatumTripleCross` — three of
them on *other files'* definitions.
That is the hazard `Oka/Analytification/RefineDatumRange.lean` records at a `simp only`, at a
fifth site and reached by a fourth route: `reassoc_of%` normalises with `simp`, and every
definition here with a proof argument that occurs in the goal gets one.

What replaces it is `(Category.assoc _ _ _).symm.trans (e =≫ _)`, which is `reassoc_of%`'s
statement built as a *term* out of `CategoryTheory.eq_whisker` and associativity, consults no
simp set and normalises nothing. The cost is that its right-hand side is left as the equation's
own, so each use is followed by a `Category.assoc` the elaborated form would have done — that, and
nothing else, is why the rewrite chains below are longer than they look as though they need to be.
`Δdump` for that push was `+27` — the 27 declarations it adds, 26 here and
`ComplexAnalytic.coverTransition_hom_comp` in `Oka/Analytification/AffineCover.lean`, with its
`comm -23` empty so that nothing was displaced against them; `+31` is those 27 plus the four
companion rows. **That figure is derived from the declaration count and the empty `comm -23`, not
read off a dump built at `1915807`.** **It is that push's and not a count of this file**, which
has since lost `ComplexAnalytic.coverSpaceHomOfEq_self`,
`ComplexAnalytic.coverSpaceHomOfEq_trans` and `ComplexAnalytic.coverSpaceHomOfEq_comp_symm` to
`Oka/Analytification/RefineDatumRange.lean`, the file that owns their definition — **a move that
made `6de872c`'s own `comm -23` non-empty, which is that check reporting and not that check
failing.** **What a branch on this file owes is a `comm -23` that is empty or accounted for row
by row, and no `congr_simp`, `.eq_1` or `match_` row among the ones it adds**: both are questions
about the push being made rather than figures about the file, so neither goes stale the way a
`Δdump` written in the present tense does. `Oka/Analytification/RefineDatumRange.lean` writes its
own figure this way, for the same reason and about the same construction.

## The transports, and why they are stated at abstract indices

The three mixed shapes each need the pair cancellation across an equality of members, and the
equality is between `σ a` and `σ b` — terms, not variables, so `subst` is unavailable where they
are used. `ComplexAnalytic.coverTransitionHom_of_fac_eq_ab`,
`ComplexAnalytic.coverTransitionHom_of_fac_eq_bc` and
`ComplexAnalytic.coverTransitionHom_of_fac_eq_ac` are therefore stated at abstract `i`, `j`, `k`
with the equality as a hypothesis, where `subst` *is* available and reduces all three to
`ComplexAnalytic.coverTransitionHom_of_fac`. This is the move
`ComplexAnalytic.mem_localisationOpen_coverSpaceHomOfEq` makes in
`Oka/Analytification/RefineDatumRange.lean`, for the same reason. (This sentence read *"one file
up"*; that file is **two** import edges up, through
`Oka/Analytification/RefineDatumGlueData.lean`.)

## Where the helper lemmas this file needed were put, and why the two answers differ

Three lemmas this file's proofs run on are not in it, and one that is could be read as belonging
elsewhere. The rule applied is **the file that owns the vocabulary**, not the file that consumes
it, and it separates them:

* `ComplexAnalytic.coverTransition_hom_comp` — `t i j ≫ t j i = 𝟙` — is in
  `Oka/Analytification/AffineCover.lean`, which declares `ComplexAnalytic.coverTransition` and
  already holds `ComplexAnalytic.coverGlueIso_symm`, the same statement one level down. Its only
  consumer is this file, **ten import edges below it with nine modules in between**, and it went
  up anyway. (This bullet read *"four files downstream"* until the distance was measured. Four is
  the gap from `Oka/Analytification/CrossMemberDatumGlue.lean`, which is neither endpoint here.)
* `ComplexAnalytic.coverSpaceHomOfEq_trans`, `ComplexAnalytic.coverSpaceHomOfEq_self` and
  `ComplexAnalytic.coverSpaceHomOfEq_comp_symm` are in
  `Oka/Analytification/RefineDatumRange.lean` for the same reason: that file declares
  `ComplexAnalytic.coverSpaceHomOfEq` and holds `ComplexAnalytic.coverSpaceHomOfEq_refl` beside
  it, and the three are the groupoid facts about a transport, whose statements say nothing about a
  triple. This file is their only consumer. **They were written here first and moved.**
* `ComplexAnalytic.coverTransitionHom_of_fac_eq_ab`,
  `ComplexAnalytic.coverTransitionHom_of_fac_eq_bc` and
  `ComplexAnalytic.coverTransitionHom_of_fac_eq_ac` **stay here**, and that is not an
  inconsistency. They are stated with two morphisms and a factorisation hypothesis *because that
  is the form a triple's edges arrive in* — the paragraph above is the whole reason they exist —
  so they are consumer-shaped, and `Oka/Analytification/AffineCover.lean` would carry a statement
  written for a caller it does not know about.

## Main definitions

- `ComplexAnalytic.refineDatumTripleProj`: **the refined triple overlap read down on the member
  its first index lies over** — the mono everything is cancelled against.
- `ComplexAnalytic.refineDatumTripleCross`: the same overlap read into the original datum's own
  overlap, where the two members are different.
- `ComplexAnalytic.refineDatumGlueDataOfLaws` and
  `ComplexAnalytic.refineDatumAnalytificationOfLaws`: **the refined cover's glue data and analytic
  space with no law left over**, taking the original datum's three laws and the two adopted
  conditions and nothing else.

## Main results

- `ComplexAnalytic.refineDatumHcocycle`: **the cocycle law of a cross-member refined cover datum**,
  at every triple and at a general `σ`. This is the file.
- `ComplexAnalytic.refineDatumTriple_localisationProj_of_ne` and
  `ComplexAnalytic.refineDatumTriple_localisationProj_of_eq`: **the intermediate statement**, one
  edge of the triple at a time, in the two shapes an edge has.
- `ComplexAnalytic.refineDatumCocycle_of_localisationProj`: **the outer cancellation**, which is
  the step four files said has no analogue and which has one.
- `ComplexAnalytic.refineDatumCrossTriple_coverTriple`: **the refined triple transition lies over
  the original one**, where the three members are pairwise different.
- `ComplexAnalytic.coverTransitionHom_of_fac`: **out along a transition and back is the
  inclusion**, in the factorised form the three mixed shapes consume.
- `ComplexAnalytic.refineDatumAnalytificationOfLaws_toLocallyRingedSpace`: the space is the glue
  data's gluing, with no transport.

## What is not here

* **No witness *here*.** This bullet said *"there is still no example of a refined cover datum at
  a non-constant `σ`"*, and there is one: `Oka/Analytification/RefineDatumWitness.lean` meets
  both conditions `Oka/Analytification/RefineDatumGlueData.lean` adopts, for every cover datum
  and every index map, and instantiates
  `ComplexAnalytic.refineDatumAnalytificationOfLaws` below at them. **Nothing here discharges
  either condition**, and whether `ComplexAnalytic.exists_refineDatumCross`'s choice satisfies
  them is untouched in both directions — the witness does not call it. **What this file removes
  is the last law, not the last hypothesis**: the two conditions are the hypothesis, and
  `ComplexAnalytic.refineDatumHrange_iff` says no weaker pair will do.
* **Nothing that says the refined cover's analytic space is the original one.** It is a space, and
  `ComplexAnalytic.not_isIso_refineToBase` says at a constant `σ` that the comparison need not be
  an isomorphism. **This bullet ended *"there is no morphism between the two gluings here in either
  direction"*, and one direction of that is retired**:
  `ComplexAnalytic.refineDatumToBase` (`Oka/Analytification/RefineDatumToBase.lean`) is
  `ComplexAnalytic.coverMap` at this file's own space, and its whole cost was one hypothesis, both
  branches of which were theorems on this line already. **The direction that stays absent is the
  other one**, from the original gluing to the refined one, and so does the identification: a
  morphism down is not an isomorphism and nothing here or there is evidence that it is one.
* **No `hrange` reproved and no shape statement reopened.**
  `Oka/Analytification/RefineDatumGlueData.lean`,
  `Oka/Analytification/RefineDatumRange.lean` and
  `Oka/Analytification/RefineDatumTransition.lean` are consumed and not opened.
* **The scheme side, `admissible`, and the comparison functor**, as in the files this one sits
  beside.
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

/-! ### Out along a transition and back -/

/-- **Out along the transition from `i` to `j` and back is the inclusion**, in the form the mixed
shapes below consume: a morphism into the `j`-`i` overlap that lies over the transition of one into
the `i`-`j` overlap comes back, along the transition the other way, to that one included.

`ComplexAnalytic.coverIncl` is an open immersion and so a monomorphism, which is what identifies
the second morphism as the first followed by `ComplexAnalytic.coverTransition`; then
`ComplexAnalytic.coverTransition_hom_comp` is the whole content, and it is the original datum's
`hsymm` and nothing else.

**Stated with the two morphisms rather than as an equation between the two transitions** because
that is how the composite around a triple arrives: each of the three edges is known only through
its composite with an inclusion, never on the nose. -/
theorem coverTransitionHom_of_fac (hsymm : ∀ i j : J, glue j i = (glue i j).symm) {i j : J}
    {Z : LocallyRingedSpace.{u}} (φ : Z ⟶ coverPart.{u} obj poly i j)
    (ψ : Z ⟶ coverPart.{u} obj poly j i)
    (hψ : ψ ≫ coverIncl.{u} obj poly j i = φ ≫ coverTransitionHom.{u} obj poly glue i j) :
    ψ ≫ coverTransitionHom.{u} obj poly glue j i = φ ≫ coverIncl.{u} obj poly i j := by
  have hcancel : ψ = φ ≫ (coverTransition.{u} obj poly glue i j).hom := by
    rw [← cancel_mono (coverIncl.{u} obj poly j i), hψ, Category.assoc, coverTransitionHom]
  rw [hcancel, Category.assoc, coverTransitionHom,
    (Category.assoc _ _ _).symm.trans (coverTransition_hom_comp.{u} obj poly glue hsymm i j =≫ _),
    Category.id_comp]

/-! ### The pair cancellation across an equality of members -/

/-- **The pair cancellation where the equal members are the triple's first two**, which is the
shape `σ a = σ b`.

The transport is the only difference from `ComplexAnalytic.coverTransitionHom_of_fac`: the morphism
that comes back lands in the member `i`, the inclusion available is the one at `k`, and the two are
the same member. **Stated at abstract `i`, `j`, `k` because that is what makes `subst` available** —
at the call site the equality is between `σ a` and `σ b`, which are terms and not variables, and
`Oka/Analytification/RefineDatumRange.lean` records the same reason for the same move. -/
theorem coverTransitionHom_of_fac_eq_ab (hsymm : ∀ i j : J, glue j i = (glue i j).symm)
    {i j k : J} (h : i = k) {Z : LocallyRingedSpace.{u}}
    (φ : Z ⟶ coverPart.{u} obj poly k j) (ψ : Z ⟶ coverPart.{u} obj poly j i)
    (hψ : ψ ≫ coverIncl.{u} obj poly j i = φ ≫ coverTransitionHom.{u} obj poly glue k j) :
    ψ ≫ coverTransitionHom.{u} obj poly glue j i =
      φ ≫ coverIncl.{u} obj poly k j ≫ coverSpaceHomOfEq.{u} obj h.symm := by
  subst h
  rw [coverSpaceHomOfEq_refl, Category.comp_id]
  exact coverTransitionHom_of_fac.{u} obj poly glue hsymm φ ψ hψ

/-- **The pair cancellation where the equal members are the triple's last two**, which is the shape
`σ b = σ c`. Here the transport sits inside the hypothesis rather than in the conclusion, and it is
`subst` and the previous section's lemmas again. -/
theorem coverTransitionHom_of_fac_eq_bc (hsymm : ∀ i j : J, glue j i = (glue i j).symm)
    {i j k : J} (h : j = k) {Z : LocallyRingedSpace.{u}}
    (φ : Z ⟶ coverPart.{u} obj poly i j) (ψ : Z ⟶ coverPart.{u} obj poly k i)
    (hψ : ψ ≫ coverIncl.{u} obj poly k i =
      φ ≫ coverTransitionHom.{u} obj poly glue i j ≫ coverSpaceHomOfEq.{u} obj h) :
    ψ ≫ coverTransitionHom.{u} obj poly glue k i = φ ≫ coverIncl.{u} obj poly i j := by
  subst h
  rw [coverSpaceHomOfEq_refl, Category.comp_id] at hψ
  exact coverTransitionHom_of_fac.{u} obj poly glue hsymm φ ψ hψ

/-- **The pair cancellation where the equal members are the triple's outer two**, which is the
shape `σ a = σ c`. The transport is on the far side of the returning transition, which is where the
triple's third edge puts it. -/
theorem coverTransitionHom_of_fac_eq_ac (hsymm : ∀ i j : J, glue j i = (glue i j).symm)
    {i j k : J} (h : i = k) {Z : LocallyRingedSpace.{u}}
    (φ : Z ⟶ coverPart.{u} obj poly i j) (ψ : Z ⟶ coverPart.{u} obj poly j k)
    (hψ : ψ ≫ coverIncl.{u} obj poly j k = φ ≫ coverTransitionHom.{u} obj poly glue i j) :
    ψ ≫ coverTransitionHom.{u} obj poly glue j k ≫ coverSpaceHomOfEq.{u} obj h.symm =
      φ ≫ coverIncl.{u} obj poly i j := by
  subst h
  rw [coverSpaceHomOfEq_refl, Category.comp_id]
  exact coverTransitionHom_of_fac.{u} obj poly glue hsymm φ ψ hψ

/-! ### The refined triple overlap, read down -/

/-- **The refined triple overlap read down on the member its first index lies over.**

This is the mono the cocycle law is cancelled against, and it is the whole of what replaces "the
projection of the one fixed member": the `a`-th refined member is `D(fam a)` inside
`obj (σ a)^an` whatever `σ` does elsewhere, and the triple overlap is an open subspace of it.

A `def` and not an `abbrev` deliberately, and the difference is measured: with an `abbrev`,
`CategoryTheory.reassoc_of%` normalises through the reducible definition and produces a pattern in
which this composite is split and reassociated, against goals in which it is not, and the rewrites
below fail to match. The unfolding lemma next to it is what the two proofs that need to open it
use, which is the construction `ComplexAnalytic.refineDatumCrossPart_eq` and
`ComplexAnalytic.refineDatumCrossTriple_eq` already use in this line of files, and for the further
reason they give: a `rw` at the definition itself plants an auto-generated equation lemma under
its own name. -/
def refineDatumTripleProj (a b c : B) :
    coverTriplePart.{u} (refineDatumObj.{u} obj σ fam)
        (refineDatumPoly.{u} obj poly σ fam q) a b c ⟶ coverSpace.{u} obj (σ a) :=
  (coverSpace.{u} (refineDatumObj.{u} obj σ fam) a).ofRestrict
      (coverOpen.{u} (refineDatumObj.{u} obj σ fam) (refineDatumPoly.{u} obj poly σ fam q) a b ⊓
        coverOpen.{u} (refineDatumObj.{u} obj σ fam)
          (refineDatumPoly.{u} obj poly σ fam q) a c).isOpenEmbedding ≫
    (localisationProj.{u} (obj (σ a)).g (fam a)).toLRSHom

/-- **The descent unfolded**, by `rfl`, for the reason the definition's docstring gives. -/
theorem refineDatumTripleProj_eq (a b c : B) :
    refineDatumTripleProj.{u} obj poly σ fam q a b c =
      (coverSpace.{u} (refineDatumObj.{u} obj σ fam) a).ofRestrict
          (coverOpen.{u} (refineDatumObj.{u} obj σ fam)
              (refineDatumPoly.{u} obj poly σ fam q) a b ⊓
            coverOpen.{u} (refineDatumObj.{u} obj σ fam)
              (refineDatumPoly.{u} obj poly σ fam q) a c).isOpenEmbedding ≫
        (localisationProj.{u} (obj (σ a)).g (fam a)).toLRSHom :=
  rfl

/-- **The refined triple overlap read into the original datum's own overlap**, where the two
members are different: `ComplexAnalytic.refineDatumCrossPart` restricted along the triple
inclusion.

This is the object the transition of an unequal edge descends *to*, and the reason the descent of
such an edge is not a statement over a member: the original datum has no morphism between two of
its members, so what the composite lands on is the overlap and not the member. -/
def refineDatumTripleCross {a b : B} (h : σ a ≠ σ b) (c : B) :
    coverTriplePart.{u} (refineDatumObj.{u} obj σ fam)
        (refineDatumPoly.{u} obj poly σ fam q) a b c ⟶ coverPart.{u} obj poly (σ a) (σ b) :=
  coverTripleIncl.{u} (refineDatumObj.{u} obj σ fam)
      (refineDatumPoly.{u} obj poly σ fam q) a b c ≫
    refineDatumCrossPart.{u} obj poly σ fam q h

/-- **That restriction unfolded**, by `rfl`, for the same reason. -/
theorem refineDatumTripleCross_eq {a b : B} (h : σ a ≠ σ b) (c : B) :
    refineDatumTripleCross.{u} obj poly σ fam q h c =
      coverTripleIncl.{u} (refineDatumObj.{u} obj σ fam)
          (refineDatumPoly.{u} obj poly σ fam q) a b c ≫
        refineDatumCrossPart.{u} obj poly σ fam q h :=
  rfl

/-- **The two descents agree over the member**: reading the refined triple overlap into the
original overlap and then into the member is reading it down.

`ComplexAnalytic.refineDatumCrossPart_coverIncl` and
`AlgebraicGeometry.LocallyRingedSpace.restrictLE_fac`. **This is what lets a composite known only
through its descent be identified as a morphism into the original overlap**, and every mixed shape
below uses it exactly once per unequal edge. -/
theorem refineDatumTripleCross_coverIncl {a b : B} (h : σ a ≠ σ b) (c : B) :
    refineDatumTripleCross.{u} obj poly σ fam q h c ≫ coverIncl.{u} obj poly (σ a) (σ b) =
      refineDatumTripleProj.{u} obj poly σ fam q a b c := by
  rw [refineDatumTripleCross_eq, Category.assoc, refineDatumCrossPart_coverIncl,
    ← Category.assoc, LocallyRingedSpace.restrictLE_fac, refineDatumTripleProj_eq]

variable (hrange : ∀ i j k : J, i ≠ j → i ≠ k → j ≠ k →
    Set.range (coverTripleIncl.{u} obj poly i j k ≫
        coverTransitionHom.{u} obj poly glue i j).base ⊆
      (coverOpen.{u} obj poly j k : Set (coverSpace.{u} obj j)))
  (hq : RefineDatumRangeCross.{u} obj poly σ fam q glue rr uu he hu)
  (hf : RefineDatumRangeEq.{u} obj poly σ fam q glue rr uu he hu)

/-! ### The intermediate statement: one edge of the triple -/

/-- **One edge of the refined triple transition, read down, where its two members are
different**: the triple transition from `a` to `b` followed down onto `obj (σ b)^an` is the descent
into the original overlap followed by the original datum's own transition.

`ComplexAnalytic.coverTriple_fac` and
`ComplexAnalytic.refineDatumTransitionHom_localisationProj_of_ne`, in that order and nothing else.
**This and the next statement are what replace
`ComplexAnalytic.refineTriple_localisationProj`**, which at a constant `σ` reads all three edges
over one member; here each edge is read over the member its own first index lies over, and the
three targets are three different members. -/
theorem refineDatumTriple_localisationProj_of_ne
    {a b c : B} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (h : σ a ≠ σ b) :
    coverTriple.{u} (refineDatumObj.{u} obj σ fam) (refineDatumPoly.{u} obj poly σ fam q)
          (refineDatumGlue.{u} obj σ fam poly q glue rr uu he hu)
          (refineDatumHrange.{u} obj poly σ fam q glue rr uu he hu hrange hq hf)
          a b c hab hac hbc ≫
        refineDatumTripleProj.{u} obj poly σ fam q b c a =
      refineDatumTripleCross.{u} obj poly σ fam q h c ≫
        coverTransitionHom.{u} obj poly glue (σ a) (σ b) := by
  rw [refineDatumTripleProj_eq, ← Category.assoc, coverTriple_fac, Category.assoc,
    refineDatumTransitionHom_localisationProj_of_ne.{u} obj poly σ fam q glue rr uu he hu h,
    refineDatumTripleCross_eq, Category.assoc]

/-- **The same edge where its two members are equal**: it is the descent of the source, across the
identification of the two members.

`ComplexAnalytic.coverTriple_fac` and
`ComplexAnalytic.refineDatumTripleIncl_localisationProj_of_eq`. At a constant `σ` the
identification is the identity and this is
`ComplexAnalytic.refineTriple_localisationProj` exactly; the identification is the whole
difference, and it is what the three shapes below have to carry around. -/
theorem refineDatumTriple_localisationProj_of_eq
    {a b c : B} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (h : σ a = σ b) :
    coverTriple.{u} (refineDatumObj.{u} obj σ fam) (refineDatumPoly.{u} obj poly σ fam q)
          (refineDatumGlue.{u} obj σ fam poly q glue rr uu he hu)
          (refineDatumHrange.{u} obj poly σ fam q glue rr uu he hu hrange hq hf)
          a b c hab hac hbc ≫
        refineDatumTripleProj.{u} obj poly σ fam q b c a =
      refineDatumTripleProj.{u} obj poly σ fam q a b c ≫ coverSpaceHomOfEq.{u} obj h := by
  rw [refineDatumTripleProj_eq, ← Category.assoc, coverTriple_fac, Category.assoc,
    refineDatumTripleIncl_localisationProj_of_eq.{u} obj poly σ fam q glue rr uu he hu h c,
    refineDatumTripleProj_eq, Category.assoc]

/-! ### The outer cancellation -/

/-- **The cocycle law at one triple follows from its descent onto the first member.**

**This is the step four files say has no analogue, and it has one.** A morphism into the `a`-th
refined triple overlap is determined by its composite with the inclusion into the `a`-th refined
member (`AlgebraicGeometry.LocallyRingedSpace.hom_ext_restrict`), and a morphism into that member
is determined by its composite with the projection down to `obj (σ a)^an`, because
`ComplexAnalytic.isOpenImmersion_localisationProj` makes that projection a monomorphism. **Neither
step knows where `σ` sends `b` or `c`**: the cancellation is against the *first* index's own
member and not against a fixed one, and at a constant `σ` those are the same thing, which is why
`Oka/Analytification/CoverRefinement.lean`'s proof reads as though it were about a fixed member.
What that file's `ComplexAnalytic.refineHcocycle` does after this step is what has no analogue,
and the two edge statements above are what replace it. -/
theorem refineDatumCocycle_of_localisationProj
    {a b c : B} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (H : coverTriple.{u} (refineDatumObj.{u} obj σ fam) (refineDatumPoly.{u} obj poly σ fam q)
          (refineDatumGlue.{u} obj σ fam poly q glue rr uu he hu)
          (refineDatumHrange.{u} obj poly σ fam q glue rr uu he hu hrange hq hf)
          a b c hab hac hbc ≫
        coverTriple.{u} (refineDatumObj.{u} obj σ fam) (refineDatumPoly.{u} obj poly σ fam q)
            (refineDatumGlue.{u} obj σ fam poly q glue rr uu he hu)
            (refineDatumHrange.{u} obj poly σ fam q glue rr uu he hu hrange hq hf)
            b c a hbc hab.symm hac.symm ≫
          coverTriple.{u} (refineDatumObj.{u} obj σ fam) (refineDatumPoly.{u} obj poly σ fam q)
              (refineDatumGlue.{u} obj σ fam poly q glue rr uu he hu)
              (refineDatumHrange.{u} obj poly σ fam q glue rr uu he hu hrange hq hf)
              c a b hac.symm hbc.symm hab ≫
            refineDatumTripleProj.{u} obj poly σ fam q a b c =
      refineDatumTripleProj.{u} obj poly σ fam q a b c) :
    coverTriple.{u} (refineDatumObj.{u} obj σ fam) (refineDatumPoly.{u} obj poly σ fam q)
        (refineDatumGlue.{u} obj σ fam poly q glue rr uu he hu)
        (refineDatumHrange.{u} obj poly σ fam q glue rr uu he hu hrange hq hf)
        a b c hab hac hbc ≫
      coverTriple.{u} (refineDatumObj.{u} obj σ fam) (refineDatumPoly.{u} obj poly σ fam q)
          (refineDatumGlue.{u} obj σ fam poly q glue rr uu he hu)
          (refineDatumHrange.{u} obj poly σ fam q glue rr uu he hu hrange hq hf)
          b c a hbc hab.symm hac.symm ≫
        coverTriple.{u} (refineDatumObj.{u} obj σ fam) (refineDatumPoly.{u} obj poly σ fam q)
            (refineDatumGlue.{u} obj σ fam poly q glue rr uu he hu)
            (refineDatumHrange.{u} obj poly σ fam q glue rr uu he hu hrange hq hf)
            c a b hac.symm hbc.symm hab = 𝟙 _ := by
  haveI := isOpenImmersion_localisationProj.{u} (obj (σ a)).g (fam a)
  refine LocallyRingedSpace.hom_ext_restrict _ _ _ ?_
  rw [Category.id_comp, ← cancel_mono ((localisationProj.{u} (obj (σ a)).g (fam a)).toLRSHom),
    Category.assoc, Category.assoc, Category.assoc, ← refineDatumTripleProj_eq]
  exact H


/-! ### The shape where all three members are equal -/

/-- **The descended cocycle law where the three members are equal**, and it holds outright: no
hypothesis on the caller's `q`, and neither of the original datum's two geometric laws is read.

Three equal edges, three identifications, and
`ComplexAnalytic.coverSpaceHomOfEq_trans` twice composes them into one along a proof of
`σ a = σ a`, which `ComplexAnalytic.coverSpaceHomOfEq_self` is the identity along. **The all-equal
shape of the range law reads neither adopted condition, and this is the matching fact for the
cocycle law**: at a triple lying over one member a cross-member refinement costs nothing at all.
-/
theorem refineDatumTripleProj_cocycle_of_eq_eq
    {a b c : B} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (h₁ : σ a = σ b) (h₂ : σ b = σ c) :
    coverTriple.{u} (refineDatumObj.{u} obj σ fam) (refineDatumPoly.{u} obj poly σ fam q)
          (refineDatumGlue.{u} obj σ fam poly q glue rr uu he hu)
          (refineDatumHrange.{u} obj poly σ fam q glue rr uu he hu hrange hq hf)
          a b c hab hac hbc ≫
        coverTriple.{u} (refineDatumObj.{u} obj σ fam) (refineDatumPoly.{u} obj poly σ fam q)
            (refineDatumGlue.{u} obj σ fam poly q glue rr uu he hu)
            (refineDatumHrange.{u} obj poly σ fam q glue rr uu he hu hrange hq hf)
            b c a hbc hab.symm hac.symm ≫
          coverTriple.{u} (refineDatumObj.{u} obj σ fam) (refineDatumPoly.{u} obj poly σ fam q)
              (refineDatumGlue.{u} obj σ fam poly q glue rr uu he hu)
              (refineDatumHrange.{u} obj poly σ fam q glue rr uu he hu hrange hq hf)
              c a b hac.symm hbc.symm hab ≫
            refineDatumTripleProj.{u} obj poly σ fam q a b c =
      refineDatumTripleProj.{u} obj poly σ fam q a b c := by
  rw [refineDatumTriple_localisationProj_of_eq.{u} obj poly σ fam q glue rr uu he hu hrange hq hf
      hac.symm hbc.symm hab (h₂.symm.trans h₁.symm),
    (Category.assoc _ _ _).symm.trans
      (refineDatumTriple_localisationProj_of_eq.{u} obj poly σ fam q glue rr uu he hu
        hrange hq hf hbc hab.symm hac.symm h₂ =≫ _),
    Category.assoc,
    (Category.assoc _ _ _).symm.trans
      (refineDatumTriple_localisationProj_of_eq.{u} obj poly σ fam q glue rr uu he hu
        hrange hq hf hab hac hbc h₁ =≫ _),
    Category.assoc,
    coverSpaceHomOfEq_trans, coverSpaceHomOfEq_trans, coverSpaceHomOfEq_self, Category.comp_id]


/-! ### The shape where the three members are pairwise different -/

/-- **The lift of the refined triple overlap is a morphism over the member**: followed by the
original triple overlap's inclusion it is the descent.

`AlgebraicGeometry.LocallyRingedSpace.liftRestrict_fac` and the agreement above. It is what makes
`ComplexAnalytic.refineDatumCrossTriple` — built in
`Oka/Analytification/RefineDatumTransition.lean` for the range law, where its only consumer read
the original datum's `hrange` through it — usable for the cocycle law as well. -/
theorem refineDatumCrossTriple_ofRestrict {a b c : B} (hab : σ a ≠ σ b) (hac : σ a ≠ σ c) :
    refineDatumCrossTriple.{u} obj poly σ fam q hab hac ≫
        (coverSpace.{u} obj (σ a)).ofRestrict
          (coverOpen.{u} obj poly (σ a) (σ b) ⊓
            coverOpen.{u} obj poly (σ a) (σ c)).isOpenEmbedding =
      refineDatumTripleProj.{u} obj poly σ fam q a b c := by
  rw [refineDatumCrossTriple_eq, LocallyRingedSpace.liftRestrict_fac, ← Category.assoc,
    ← refineDatumTripleCross_eq, refineDatumTripleCross_coverIncl]

/-- **The refined triple transition lies over the original one**, where the three members are
pairwise different.

The square of the whole file, and the only place the original datum's `ComplexAnalytic.coverTriple`
appears. Both sides are morphisms into a restriction, so
`AlgebraicGeometry.LocallyRingedSpace.hom_ext_restrict` reduces it to an equation over
`obj (σ b)^an`: on the left the unequal edge's descent, on the right
`ComplexAnalytic.coverTriple_fac` and
`ComplexAnalytic.refineDatumCrossTriple_coverTripleIncl`, and the two meet at
`ComplexAnalytic.refineDatumTripleCross`.

**This is the statement `Oka/Analytification/CoverRefinement.lean` predicted could not exist** —
"three cross-member triple overlaps sit over three different members with no common target". They
do; what they have instead is the original datum's own triple overlap over them, and that is a
target. -/
theorem refineDatumCrossTriple_coverTriple
    {a b c : B} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hσab : σ a ≠ σ b) (hσac : σ a ≠ σ c) (hσbc : σ b ≠ σ c) :
    coverTriple.{u} (refineDatumObj.{u} obj σ fam) (refineDatumPoly.{u} obj poly σ fam q)
          (refineDatumGlue.{u} obj σ fam poly q glue rr uu he hu)
          (refineDatumHrange.{u} obj poly σ fam q glue rr uu he hu hrange hq hf)
          a b c hab hac hbc ≫
        refineDatumCrossTriple.{u} obj poly σ fam q hσbc hσab.symm =
      refineDatumCrossTriple.{u} obj poly σ fam q hσab hσac ≫
        coverTriple.{u} obj poly glue hrange (σ a) (σ b) (σ c) hσab hσac hσbc := by
  refine LocallyRingedSpace.hom_ext_restrict _ _ _ ?_
  rw [Category.assoc, refineDatumCrossTriple_ofRestrict,
    refineDatumTriple_localisationProj_of_ne.{u} obj poly σ fam q glue rr uu he hu hrange hq hf
      hab hac hbc hσab,
    Category.assoc, coverTriple_fac, ← Category.assoc,
    refineDatumCrossTriple_coverTripleIncl, refineDatumTripleCross_eq, Category.assoc]

/-- **The descended cocycle law where the three members are pairwise different**, from the
original datum's own `hcocycle` and nothing else about the refinement.

Three applications of the square above walk the composite down to
`ComplexAnalytic.coverTriple` at `(σ a, σ b, σ c)` three times over, where the original datum's law
collapses it to the identity. **This is the only shape that spends the original `hcocycle`** — the
matching fact to `Oka/Analytification/RefineDatumRange.lean`'s finding that the pairwise different
triple is the only shape of the range law that spends the original `hrange`. -/
theorem refineDatumTripleProj_cocycle_of_ne_ne
    (hcocycle : ∀ i j k : J, ∀ hij : i ≠ j, ∀ hik : i ≠ k, ∀ hjk : j ≠ k,
      coverTriple.{u} obj poly glue hrange i j k hij hik hjk ≫
        coverTriple.{u} obj poly glue hrange j k i hjk hij.symm hik.symm ≫
          coverTriple.{u} obj poly glue hrange k i j hik.symm hjk.symm hij = 𝟙 _)
    {a b c : B} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hσab : σ a ≠ σ b) (hσac : σ a ≠ σ c) (hσbc : σ b ≠ σ c) :
    coverTriple.{u} (refineDatumObj.{u} obj σ fam) (refineDatumPoly.{u} obj poly σ fam q)
          (refineDatumGlue.{u} obj σ fam poly q glue rr uu he hu)
          (refineDatumHrange.{u} obj poly σ fam q glue rr uu he hu hrange hq hf)
          a b c hab hac hbc ≫
        coverTriple.{u} (refineDatumObj.{u} obj σ fam) (refineDatumPoly.{u} obj poly σ fam q)
            (refineDatumGlue.{u} obj σ fam poly q glue rr uu he hu)
            (refineDatumHrange.{u} obj poly σ fam q glue rr uu he hu hrange hq hf)
            b c a hbc hab.symm hac.symm ≫
          coverTriple.{u} (refineDatumObj.{u} obj σ fam) (refineDatumPoly.{u} obj poly σ fam q)
              (refineDatumGlue.{u} obj σ fam poly q glue rr uu he hu)
              (refineDatumHrange.{u} obj poly σ fam q glue rr uu he hu hrange hq hf)
              c a b hac.symm hbc.symm hab ≫
            refineDatumTripleProj.{u} obj poly σ fam q a b c =
      refineDatumTripleProj.{u} obj poly σ fam q a b c := by
  rw [← refineDatumCrossTriple_ofRestrict.{u} obj poly σ fam q hσab hσac,
    (Category.assoc _ _ _).symm.trans
      (refineDatumCrossTriple_coverTriple.{u} obj poly σ fam q glue rr uu he hu
        hrange hq hf hac.symm hbc.symm hab hσac.symm hσbc.symm hσab =≫ _),
    Category.assoc,
    (Category.assoc _ _ _).symm.trans
      (refineDatumCrossTriple_coverTriple.{u} obj poly σ fam q glue rr uu he hu
        hrange hq hf hbc hab.symm hac.symm hσbc hσab.symm hσac.symm =≫ _),
    Category.assoc,
    (Category.assoc _ _ _).symm.trans
      (refineDatumCrossTriple_coverTriple.{u} obj poly σ fam q glue rr uu he hu
        hrange hq hf hab hac hbc hσab hσac hσbc =≫ _),
    Category.assoc,
    ← Category.assoc _ (coverTriple.{u} obj poly glue hrange (σ c) (σ a) (σ b) hσac.symm
      hσbc.symm hσab) _,
    (Category.assoc _ _ _).symm.trans (hcocycle (σ a) (σ b) (σ c) hσab hσac hσbc =≫ _),
    Category.id_comp]


/-! ### The three shapes with exactly one pair of members equal -/

/-- **The descended cocycle law where the first two members are equal and the third is
different.**

The three edges are, in order, equal, unequal and unequal, and **what they compose to is a pair of
the original datum's transitions going out and coming back** — not a triple of them, and there
could not be one: the original index triple here is `(σ a, σ a, σ c)`, which
`ComplexAnalytic.coverTriple` does not accept. So what this shape spends is the original datum's
**`hsymm`**, through `ComplexAnalytic.coverTransitionHom_of_fac_eq_ab`, and its `hcocycle` is not
read at all.

The two unequal edges are identified as morphisms into the original datum's overlaps by
`ComplexAnalytic.refineDatumTripleCross_coverIncl`, which is the only way a composite of lifts is
known here; the equal edge contributes the identification, and its inverse comes back out of the
cancellation, so `ComplexAnalytic.coverSpaceHomOfEq_comp_symm` closes it. -/
theorem refineDatumTripleProj_cocycle_of_eq_ab
    (hsymm : ∀ i j : J, glue j i = (glue i j).symm)
    {a b c : B} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (h : σ a = σ b) (hσbc : σ b ≠ σ c) :
    coverTriple.{u} (refineDatumObj.{u} obj σ fam) (refineDatumPoly.{u} obj poly σ fam q)
          (refineDatumGlue.{u} obj σ fam poly q glue rr uu he hu)
          (refineDatumHrange.{u} obj poly σ fam q glue rr uu he hu hrange hq hf)
          a b c hab hac hbc ≫
        coverTriple.{u} (refineDatumObj.{u} obj σ fam) (refineDatumPoly.{u} obj poly σ fam q)
            (refineDatumGlue.{u} obj σ fam poly q glue rr uu he hu)
            (refineDatumHrange.{u} obj poly σ fam q glue rr uu he hu hrange hq hf)
            b c a hbc hab.symm hac.symm ≫
          coverTriple.{u} (refineDatumObj.{u} obj σ fam) (refineDatumPoly.{u} obj poly σ fam q)
              (refineDatumGlue.{u} obj σ fam poly q glue rr uu he hu)
              (refineDatumHrange.{u} obj poly σ fam q glue rr uu he hu hrange hq hf)
              c a b hac.symm hbc.symm hab ≫
            refineDatumTripleProj.{u} obj poly σ fam q a b c =
      refineDatumTripleProj.{u} obj poly σ fam q a b c := by
  have hσac : σ a ≠ σ c := fun e ↦ hσbc (h.symm.trans e)
  have e2 := refineDatumTriple_localisationProj_of_ne.{u} obj poly σ fam q glue rr uu he hu
    hrange hq hf hbc hab.symm hac.symm hσbc
  have e3 := refineDatumTriple_localisationProj_of_ne.{u} obj poly σ fam q glue rr uu he hu
    hrange hq hf hac.symm hbc.symm hab hσac.symm
  have hψ : ((coverTriple.{u} (refineDatumObj.{u} obj σ fam)
          (refineDatumPoly.{u} obj poly σ fam q)
          (refineDatumGlue.{u} obj σ fam poly q glue rr uu he hu)
          (refineDatumHrange.{u} obj poly σ fam q glue rr uu he hu hrange hq hf)
          a b c hab hac hbc ≫
        coverTriple.{u} (refineDatumObj.{u} obj σ fam) (refineDatumPoly.{u} obj poly σ fam q)
            (refineDatumGlue.{u} obj σ fam poly q glue rr uu he hu)
            (refineDatumHrange.{u} obj poly σ fam q glue rr uu he hu hrange hq hf)
            b c a hbc hab.symm hac.symm) ≫
      refineDatumTripleCross.{u} obj poly σ fam q hσac.symm b) ≫
        coverIncl.{u} obj poly (σ c) (σ a) =
      (coverTriple.{u} (refineDatumObj.{u} obj σ fam) (refineDatumPoly.{u} obj poly σ fam q)
            (refineDatumGlue.{u} obj σ fam poly q glue rr uu he hu)
            (refineDatumHrange.{u} obj poly σ fam q glue rr uu he hu hrange hq hf)
            a b c hab hac hbc ≫
          refineDatumTripleCross.{u} obj poly σ fam q hσbc a) ≫
        coverTransitionHom.{u} obj poly glue (σ b) (σ c) := by
    rw [Category.assoc, Category.assoc, refineDatumTripleCross_coverIncl, e2, ← Category.assoc]
  have key := coverTransitionHom_of_fac_eq_ab.{u} obj poly glue hsymm h _ _ hψ
  rw [e3, ← Category.assoc, ← Category.assoc, key, Category.assoc,
    (Category.assoc _ _ _).symm.trans
      (refineDatumTripleCross_coverIncl.{u} obj poly σ fam q hσbc a =≫ _),
    (Category.assoc _ _ _).symm.trans
      (refineDatumTriple_localisationProj_of_eq.{u} obj poly σ fam q glue rr uu he hu
        hrange hq hf hab hac hbc h =≫ _),
    Category.assoc, coverSpaceHomOfEq_comp_symm, Category.comp_id]

/-- **The descended cocycle law where the last two members are equal.**

The same pair cancellation with the identification in the middle edge rather than the first, so it
sits inside the hypothesis of `ComplexAnalytic.coverTransitionHom_of_fac_eq_bc` and not in its
conclusion, and nothing is left over at the end. -/
theorem refineDatumTripleProj_cocycle_of_eq_bc
    (hsymm : ∀ i j : J, glue j i = (glue i j).symm)
    {a b c : B} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hσab : σ a ≠ σ b) (h : σ b = σ c) :
    coverTriple.{u} (refineDatumObj.{u} obj σ fam) (refineDatumPoly.{u} obj poly σ fam q)
          (refineDatumGlue.{u} obj σ fam poly q glue rr uu he hu)
          (refineDatumHrange.{u} obj poly σ fam q glue rr uu he hu hrange hq hf)
          a b c hab hac hbc ≫
        coverTriple.{u} (refineDatumObj.{u} obj σ fam) (refineDatumPoly.{u} obj poly σ fam q)
            (refineDatumGlue.{u} obj σ fam poly q glue rr uu he hu)
            (refineDatumHrange.{u} obj poly σ fam q glue rr uu he hu hrange hq hf)
            b c a hbc hab.symm hac.symm ≫
          coverTriple.{u} (refineDatumObj.{u} obj σ fam) (refineDatumPoly.{u} obj poly σ fam q)
              (refineDatumGlue.{u} obj σ fam poly q glue rr uu he hu)
              (refineDatumHrange.{u} obj poly σ fam q glue rr uu he hu hrange hq hf)
              c a b hac.symm hbc.symm hab ≫
            refineDatumTripleProj.{u} obj poly σ fam q a b c =
      refineDatumTripleProj.{u} obj poly σ fam q a b c := by
  have hσac : σ a ≠ σ c := fun e ↦ hσab (e.trans h.symm)
  have e1 := refineDatumTriple_localisationProj_of_ne.{u} obj poly σ fam q glue rr uu he hu
    hrange hq hf hab hac hbc hσab
  have e2 := refineDatumTriple_localisationProj_of_eq.{u} obj poly σ fam q glue rr uu he hu
    hrange hq hf hbc hab.symm hac.symm h
  have e3 := refineDatumTriple_localisationProj_of_ne.{u} obj poly σ fam q glue rr uu he hu
    hrange hq hf hac.symm hbc.symm hab hσac.symm
  have hψ : ((coverTriple.{u} (refineDatumObj.{u} obj σ fam) (refineDatumPoly.{u} obj poly σ fam q)
            (refineDatumGlue.{u} obj σ fam poly q glue rr uu he hu)
            (refineDatumHrange.{u} obj poly σ fam q glue rr uu he hu hrange hq hf)
            a b c hab hac hbc ≫
          coverTriple.{u} (refineDatumObj.{u} obj σ fam) (refineDatumPoly.{u} obj poly σ fam q)
              (refineDatumGlue.{u} obj σ fam poly q glue rr uu he hu)
              (refineDatumHrange.{u} obj poly σ fam q glue rr uu he hu hrange hq hf)
              b c a hbc hab.symm hac.symm) ≫
        refineDatumTripleCross.{u} obj poly σ fam q hσac.symm b) ≫
      coverIncl.{u} obj poly (σ c) (σ a) =
      refineDatumTripleCross.{u} obj poly σ fam q hσab c ≫
        coverTransitionHom.{u} obj poly glue (σ a) (σ b) ≫ coverSpaceHomOfEq.{u} obj h := by
    rw [Category.assoc, Category.assoc, refineDatumTripleCross_coverIncl, e2, ← Category.assoc,
      e1, Category.assoc]
  have key := coverTransitionHom_of_fac_eq_bc.{u} obj poly glue hsymm h _ _ hψ
  rw [e3, ← Category.assoc, ← Category.assoc, key, refineDatumTripleCross_coverIncl]

/-- **The descended cocycle law where the outer two members are equal.**

The identification is on the far side of the returning transition here, which is what
`ComplexAnalytic.coverTransitionHom_of_fac_eq_ac` is stated for. **These three shapes are cyclic
rotations of one another and none of them is a corollary of another**: the law at `(a, b, c)` and
the law at `(b, c, a)` are equations between endomorphisms of two different objects, and a
`ComplexAnalytic.coverTriple` is not known to be an isomorphism. -/
theorem refineDatumTripleProj_cocycle_of_eq_ac
    (hsymm : ∀ i j : J, glue j i = (glue i j).symm)
    {a b c : B} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hσab : σ a ≠ σ b) (h : σ a = σ c) :
    coverTriple.{u} (refineDatumObj.{u} obj σ fam) (refineDatumPoly.{u} obj poly σ fam q)
          (refineDatumGlue.{u} obj σ fam poly q glue rr uu he hu)
          (refineDatumHrange.{u} obj poly σ fam q glue rr uu he hu hrange hq hf)
          a b c hab hac hbc ≫
        coverTriple.{u} (refineDatumObj.{u} obj σ fam) (refineDatumPoly.{u} obj poly σ fam q)
            (refineDatumGlue.{u} obj σ fam poly q glue rr uu he hu)
            (refineDatumHrange.{u} obj poly σ fam q glue rr uu he hu hrange hq hf)
            b c a hbc hab.symm hac.symm ≫
          coverTriple.{u} (refineDatumObj.{u} obj σ fam) (refineDatumPoly.{u} obj poly σ fam q)
              (refineDatumGlue.{u} obj σ fam poly q glue rr uu he hu)
              (refineDatumHrange.{u} obj poly σ fam q glue rr uu he hu hrange hq hf)
              c a b hac.symm hbc.symm hab ≫
            refineDatumTripleProj.{u} obj poly σ fam q a b c =
      refineDatumTripleProj.{u} obj poly σ fam q a b c := by
  have hσbc : σ b ≠ σ c := fun e ↦ hσab (h.trans e.symm)
  have e1 := refineDatumTriple_localisationProj_of_ne.{u} obj poly σ fam q glue rr uu he hu
    hrange hq hf hab hac hbc hσab
  have e2 := refineDatumTriple_localisationProj_of_ne.{u} obj poly σ fam q glue rr uu he hu
    hrange hq hf hbc hab.symm hac.symm hσbc
  have e3 := refineDatumTriple_localisationProj_of_eq.{u} obj poly σ fam q glue rr uu he hu
    hrange hq hf hac.symm hbc.symm hab h.symm
  have hψ : (coverTriple.{u} (refineDatumObj.{u} obj σ fam) (refineDatumPoly.{u} obj poly σ fam q)
            (refineDatumGlue.{u} obj σ fam poly q glue rr uu he hu)
            (refineDatumHrange.{u} obj poly σ fam q glue rr uu he hu hrange hq hf)
            a b c hab hac hbc ≫
        refineDatumTripleCross.{u} obj poly σ fam q hσbc a) ≫
      coverIncl.{u} obj poly (σ b) (σ c) =
      refineDatumTripleCross.{u} obj poly σ fam q hσab c ≫
        coverTransitionHom.{u} obj poly glue (σ a) (σ b) := by
    rw [Category.assoc, refineDatumTripleCross_coverIncl, e1]
  have key := coverTransitionHom_of_fac_eq_ac.{u} obj poly glue hsymm h _ _ hψ
  rw [e3, (Category.assoc _ _ _).symm.trans (e2 =≫ _), Category.assoc,
    ← Category.assoc _ (refineDatumTripleCross.{u} obj poly σ fam q hσbc a) _, key,
    refineDatumTripleCross_coverIncl]


/-! ### The law -/

/-- **The cocycle law of a cross-member refined cover datum**, at every triple of distinct
indices and at a general `σ`.

`Oka/Analytification/RefineDatumGlueData.lean` named this law and said of it that nothing on this
line was evidence about it in either direction. It is a theorem, and it asks a caller for exactly
the original datum's own three laws: `hsymm`, `hrange` and `hcocycle`.

The case split is the same five shapes the range law splits into, in the same order and with the
same `by_cases` structure, and **that is a structural fact about a triple and not a coincidence of
either law**: `σ a = σ b` and `σ b = σ c` force `σ a = σ c`, so of the eight combinations only five
occur. **Note which hypothesis each shape spends**, since the three are not interchangeable: the
pairwise different triple spends `hcocycle`, the three with exactly one pair equal spend `hsymm`,
and the all-equal triple spends neither. -/
theorem refineDatumHcocycle
    (hsymm : ∀ i j : J, glue j i = (glue i j).symm)
    (hcocycle : ∀ i j k : J, ∀ hij : i ≠ j, ∀ hik : i ≠ k, ∀ hjk : j ≠ k,
      coverTriple.{u} obj poly glue hrange i j k hij hik hjk ≫
        coverTriple.{u} obj poly glue hrange j k i hjk hij.symm hik.symm ≫
          coverTriple.{u} obj poly glue hrange k i j hik.symm hjk.symm hij = 𝟙 _) :
    RefineDatumCocycle.{u} obj poly σ fam q glue rr uu he hu hrange hq hf := by
  intro a b c hab hac hbc
  refine refineDatumCocycle_of_localisationProj.{u} obj poly σ fam q glue rr uu he hu
    hrange hq hf hab hac hbc ?_
  by_cases h : σ b = σ c
  · by_cases h' : σ a = σ b
    · exact refineDatumTripleProj_cocycle_of_eq_eq.{u} obj poly σ fam q glue rr uu he hu
        hrange hq hf hab hac hbc h' h
    · exact refineDatumTripleProj_cocycle_of_eq_bc.{u} obj poly σ fam q glue rr uu he hu
        hrange hq hf hsymm hab hac hbc h' h
  · by_cases h₁ : σ a = σ b
    · exact refineDatumTripleProj_cocycle_of_eq_ab.{u} obj poly σ fam q glue rr uu he hu
        hrange hq hf hsymm hab hac hbc h₁ h
    · by_cases h₂ : σ a = σ c
      · exact refineDatumTripleProj_cocycle_of_eq_ac.{u} obj poly σ fam q glue rr uu he hu
          hrange hq hf hsymm hab hac hbc h₁ h₂
      · exact refineDatumTripleProj_cocycle_of_ne_ne.{u} obj poly σ fam q glue rr uu he hu
          hrange hq hf hcocycle hab hac hbc h₁ h₂ h

/-! ### The refined cover's analytic space, with no law left over -/

/-- **The glue data of a cross-member refined cover, with no law left over.**

`ComplexAnalytic.refineDatumGlueData` with its one remaining hypothesis discharged by the theorem
above. What a caller supplies is the original datum's three laws and the two conditions
`Oka/Analytification/RefineDatumGlueData.lean` adopts — and those two are a hypothesis on the
caller's own choice of `q`, not a law of the refinement:
`ComplexAnalytic.refineDatumHrange_iff` says they are equivalent to the range law, so they cannot
be weakened and they are not what is left of the cocycle law.

**It is a separate definition and not a replacement.** The general one takes the cocycle law as an
argument and stays useful: a caller who has a refinement whose original datum's `hcocycle` is not
in hand, or who wants the law at a proof of its own, still needs it. -/
def refineDatumGlueDataOfLaws
    (hsym : ∀ i j : J, glue j i = (glue i j).symm)
    (hcocycle : ∀ i j k : J, ∀ hij : i ≠ j, ∀ hik : i ≠ k, ∀ hjk : j ≠ k,
      coverTriple.{u} obj poly glue hrange i j k hij hik hjk ≫
        coverTriple.{u} obj poly glue hrange j k i hjk hij.symm hik.symm ≫
          coverTriple.{u} obj poly glue hrange k i j hik.symm hjk.symm hij = 𝟙 _) :
    LocallyRingedSpace.GlueData.{u} :=
  refineDatumGlueData.{u} obj poly σ fam q glue rr uu he hu hsym hrange hq hf
    (refineDatumHcocycle.{u} obj poly σ fam q glue rr uu he hu hrange hq hf hsym hcocycle)

/-- **The analytic space a cross-member refinement glues to, with no law left over**, and this is
what the whole line of files was for.

`ComplexAnalytic.refineDatumAnalytification` at the same arguments. **Nothing here is a witness**,
and this docstring said there was none anywhere: *"there is still no example of a refined cover
datum at a non-constant `σ` whose two conditions anything meets"*.
`Oka/Analytification/RefineDatumWitness.lean` is one, at every cover datum and every index map,
and it is a caller of this definition rather than a part of it. What has changed is
that a caller who meets them owes nothing further — before this file the object also asked for a
law nothing could prove. -/
def refineDatumAnalytificationOfLaws
    (hsym : ∀ i j : J, glue j i = (glue i j).symm)
    (hcocycle : ∀ i j k : J, ∀ hij : i ≠ j, ∀ hik : i ≠ k, ∀ hjk : j ≠ k,
      coverTriple.{u} obj poly glue hrange i j k hij hik hjk ≫
        coverTriple.{u} obj poly glue hrange j k i hjk hij.symm hik.symm ≫
          coverTriple.{u} obj poly glue hrange k i j hik.symm hjk.symm hij = 𝟙 _) :
    AnalyticSpace.{u} :=
  refineDatumAnalytification.{u} obj poly σ fam q glue rr uu he hu hsym hrange hq hf
    (refineDatumHcocycle.{u} obj poly σ fam q glue rr uu he hu hrange hq hf hsym hcocycle)

/-- **That space has that glue data's gluing underneath it**, with no transport.

`ComplexAnalytic.refineDatumAnalytification_toLocallyRingedSpace` at the discharged law, and it is
here for that theorem's own reason: without it the two definitions above are two well-typed objects
with no recorded relation to each other. -/
theorem refineDatumAnalytificationOfLaws_toLocallyRingedSpace
    (hsym : ∀ i j : J, glue j i = (glue i j).symm)
    (hcocycle : ∀ i j k : J, ∀ hij : i ≠ j, ∀ hik : i ≠ k, ∀ hjk : j ≠ k,
      coverTriple.{u} obj poly glue hrange i j k hij hik hjk ≫
        coverTriple.{u} obj poly glue hrange j k i hjk hij.symm hik.symm ≫
          coverTriple.{u} obj poly glue hrange k i j hik.symm hjk.symm hij = 𝟙 _) :
    (refineDatumAnalytificationOfLaws.{u} obj poly σ fam q glue rr uu he hu hrange hq hf hsym
        hcocycle).toLocallyRingedSpace =
      (refineDatumGlueDataOfLaws.{u} obj poly σ fam q glue rr uu he hu hrange hq hf hsym
        hcocycle).toGlueData.glued :=
  refineDatumAnalytification_toLocallyRingedSpace.{u} obj poly σ fam q glue rr uu he hu hsym
    hrange hq hf _

end

end ComplexAnalytic
