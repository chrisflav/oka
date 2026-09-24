/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Analytification.RefineDatumRange
import Oka.Analytification.RefineDatumSymm

/-!
# The refined cover datum's glue data: `hrange` assembled, and `hcocycle` named

`Oka/Analytification/RefineDatumTransition.lean` and `Oka/Analytification/RefineDatumRange.lean`
settle the range law of a cross-member refined cover datum at each of the five ways the three
members `σ a`, `σ b`, `σ c` of a triple of *different indices* can coincide. That is five
statements and not one law, and `ComplexAnalytic.coverGlueData` takes one: `hrange` is a single
`∀ i j k`, and `ComplexAnalytic.coverTriple` takes a *proof* of it as an argument, which is why
the cocycle law could not so much as be stated while the range law was five separate theorems.

**This file joins them, and the joining is where the hypothesis a caller carries gets decided.**

## Two conditions and not one, which is `Oka/Analytification/RefineDatumRange.lean`'s finding

Four of the five shapes are equivalences, and their right-hand sides are of two shapes:

* at the three triples with `σ b ≠ σ c` the residue is the containment in the caller's own
  `D(q b c)` that `Oka/Analytification/RefineDatumTransition.lean` isolated, and it is the *same*
  containment whichever branch `ComplexAnalytic.refineDatumGlue` takes at `(a, b)` and wherever
  the free half came from — `ComplexAnalytic.RefineDatumRangeCross` below;
* at `σ b = σ c` the law asks for a containment in `D(fam c)`, which belongs to the caller's
  refining family and not to the original datum, and there is no free half at all —
  `ComplexAnalytic.RefineDatumRangeEq` below.

So the assembled hypothesis is a pair, and **the second half of it is asked for only where
`σ a ≠ σ b`**: at an all-equal triple the law is
`ComplexAnalytic.range_refineDatumTransitionHom_subset_of_eq`, a theorem with no hypothesis on
the caller's `q` and none on the original datum's own `hrange`, and asking a caller for something
already proved would misstate what this construction costs.

**And the pair is necessary as well as sufficient**
(`ComplexAnalytic.refineDatumHrange_iff`). Each shape statement is an equivalence rather than an
implication precisely so that this direction is available, and without it the file would have
adopted a hypothesis without saying that no weaker one can do.

## What is left, and it is one law with a name

With `hrange` a single proof, `ComplexAnalytic.coverTriple` applies at the refined datum and the
cocycle law becomes statable: `ComplexAnalytic.RefineDatumCocycle`. Naming it is most of what
this file is for. `ComplexAnalytic.refineDatumGlueData` and
`ComplexAnalytic.refineDatumAnalytification` then take it as their one remaining hypothesis, the
symmetry law being `ComplexAnalytic.refineDatumGlue_symm` and the range law being
`ComplexAnalytic.refineDatumHrange` — so of the three laws a cross-member refinement needs, one
was **already proved** before this file, one is **proved here from two conditions this file adopts
and shows equivalent to it**, and the third is **named here and proved in the file that consumes
this one.** Neither geometric law was available at a non-constant `σ` before this file; the
symmetry law was, and bringing all
three together is what `ComplexAnalytic.refineDatumGlueData` is.

**Nothing here is evidence about the cocycle law**, and this paragraph gave a reason that was on
record and wrong: *"the cancellation `Oka/Analytification/CoverRefinement.lean` uses at a constant
`σ` is against the projection of the one fixed member, and at a general `σ` there is no one fixed
member to project to"*. There is — the member the triple's first index lies over —, and
`ComplexAnalytic.refineDatumHcocycle` (`Oka/Analytification/RefineDatumCocycle.lean`) proves the
law from the original datum's own three. **Nothing here is still evidence about it**: that file
consumes this one and reopens nothing in it.

## Main definitions

- `ComplexAnalytic.RefineDatumRangeCross`: **the residue of the range law wherever
  `σ b ≠ σ c`**, one condition for three shapes.
- `ComplexAnalytic.RefineDatumRangeEq`: **the whole of the range law where `σ b = σ c` and
  `σ a ≠ σ b`**, which is a containment in the caller's own refining family.
- `ComplexAnalytic.RefineDatumCocycle`: **the cocycle law of the refined datum**, statable
  because the range law is now one proof — and proved, in
  `Oka/Analytification/RefineDatumCocycle.lean`, which is what this name being writable was for.
- `ComplexAnalytic.refineDatumGlueData`: **the glue data of the refined cover** at a general
  `σ`, with the cocycle law as its one hypothesis.
- `ComplexAnalytic.refineDatumAnalytification`: **the analytic space it glues to.**

## Main results

- `ComplexAnalytic.refineDatumHrange`: **`hrange` for the refined cover datum**, the five shapes
  joined, in the form `ComplexAnalytic.coverGlueData` takes.
- `ComplexAnalytic.refineDatumHrange_iff`: **and the two conditions are exactly what it asks** —
  the law is equivalent to their conjunction, so no weaker pair will do.
- `ComplexAnalytic.refineDatumAnalytification_toLocallyRingedSpace`: **the analytic space's
  underlying locally ringed space is the glue data's gluing**, with no transport.

## What is not here

* **`ComplexAnalytic.RefineDatumCocycle` is named and not proved *here*.** This bullet said it
  was proved nowhere and that nothing on this line was evidence about it in either direction;
  `ComplexAnalytic.refineDatumHcocycle` (`Oka/Analytification/RefineDatumCocycle.lean`) proves it,
  from the original datum's own three laws, and the hypothesis-free forms of the two definitions
  below are there. Nothing in *this* file is evidence about it, which is what the bullet is now
  saying.
* **Nothing that discharges either adopted condition.** Whether
  `ComplexAnalytic.exists_refineDatumCross`'s choice satisfies `RefineDatumRangeCross`, and
  whether a caller can arrange `RefineDatumRangeEq`, are untouched here in both directions; this
  file adopts, and `Oka/Analytification/CrossMemberGlue.lean`'s record that nothing produces `q`
  stands. **Two files below do discharge both**, and a reader should not stop at the *"no free
  half at all"* above: `Oka/Analytification/RefineDatumWitness.lean` at a refining family
  constantly `1`, and `Oka/Analytification/RefineDatumUnitFamily.lean` at every family once `σ` is
  injective — `RefineDatumRangeEq`'s binders ask for `b ≠ c` together with `σ b = σ c`, and an
  injective `σ` admits no such pair. Neither fact is about the containment, which is what the
  sentence above is about and which remains as free of a free half as it says.
* **No witness *here*.** This bullet said *"there is still no example of a refined cover datum at
  a non-constant `σ` … a construction whose hypotheses nobody has met is not one"*, and both
  hypotheses this file adopts have since been met:
  `Oka/Analytification/RefineDatumWitness.lean` discharges `ComplexAnalytic.RefineDatumRangeCross`
  and `ComplexAnalytic.RefineDatumRangeEq` for every cover datum and every index map, by taking
  the refining family constantly `1`. **Nothing in this file is evidence for that** — it is the
  file the two conditions are stated in, and a condition being satisfiable is a fact about the
  caller, not about the statement.
* **None of the five shapes is reproved.** `Oka/Analytification/RefineDatumRange.lean` and
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

/-! ### The two conditions the range law reduces to -/

/-- **The residue of the refined range law wherever `σ b ≠ σ c`**: the transition, read down on
the member it lies over, lands in the caller's own `D(q b c)`.

**One condition for three of the five shapes**, which is
`Oka/Analytification/RefineDatumRange.lean`'s finding and is not obvious in advance: the free
half differs between them — the original datum's own `hrange` at a pairwise different triple, the
unconditional half of the transition law at `σ a = σ c`, the source's own second overlap at
`σ a = σ b` — and the residue does not differ at all, including on the equal branch. -/
abbrev RefineDatumRangeCross : Prop :=
  ∀ a b c : B, a ≠ b → a ≠ c → b ≠ c → σ b ≠ σ c →
    Set.range (coverTripleIncl.{u} (refineDatumObj.{u} obj σ fam)
          (refineDatumPoly.{u} obj poly σ fam q) a b c ≫
        coverTransitionHom.{u} (refineDatumObj.{u} obj σ fam)
            (refineDatumPoly.{u} obj poly σ fam q)
            (refineDatumGlue.{u} obj σ fam poly q glue rr uu he hu) a b ≫
          (localisationProj.{u} (obj (σ b)).g (fam b)).toLRSHom).base ⊆
      ↑(localisationOpen.{u} (obj (σ b)).g (q b c))

/-- **The whole of the refined range law where `σ b = σ c`**, which is a containment in
`D(fam c)` and not a residue: the target there belongs to the caller's refining family, so no
half of it is free and the original cover's geometry bears on it not at all.

**It is asked for only where `σ a ≠ σ b`, and that asymmetry is deliberate.** At
`σ a = σ b = σ c` the law is `ComplexAnalytic.range_refineDatumTransitionHom_subset_of_eq`, a
theorem with no hypothesis on `q` at all, so quantifying this condition over every `a` would ask
a caller for something already proved and would misstate what the construction costs. -/
abbrev RefineDatumRangeEq : Prop :=
  ∀ a b c : B, a ≠ b → a ≠ c → b ≠ c → σ a ≠ σ b → ∀ hbc : σ b = σ c,
    Set.range (coverTripleIncl.{u} (refineDatumObj.{u} obj σ fam)
          (refineDatumPoly.{u} obj poly σ fam q) a b c ≫
        coverTransitionHom.{u} (refineDatumObj.{u} obj σ fam)
            (refineDatumPoly.{u} obj poly σ fam q)
            (refineDatumGlue.{u} obj σ fam poly q glue rr uu he hu) a b ≫
          (localisationProj.{u} (obj (σ b)).g (fam b)).toLRSHom).base ⊆
      ↑(localisationOpen.{u} (obj (σ b)).g (hbc ▸ fam c))

/-! ### `hrange` for the refined datum -/

/-- **`hrange` for the refined cover datum, at a general `σ`**, in the exact form
`ComplexAnalytic.coverGlueData` takes it.

The case split is on `(σ a, σ b, σ c)` and it is exhaustive and disjoint: the all-equal triple is
a theorem, the two mixed ones with `σ b ≠ σ c` and the pairwise different one are the first
condition, and `σ b = σ c` with `σ a ≠ σ b` is the second. **Note which hypotheses each branch
spends**: the original datum's own `hrange` is read at the pairwise different triple and nowhere
else, and the two conditions are read at four of the five shapes and not at the fifth. -/
theorem refineDatumHrange
    (hrange : ∀ i j k : J, i ≠ j → i ≠ k → j ≠ k →
      Set.range (coverTripleIncl.{u} obj poly i j k ≫
          coverTransitionHom.{u} obj poly glue i j).base ⊆
        (coverOpen.{u} obj poly j k : Set (coverSpace.{u} obj j)))
    (hq : RefineDatumRangeCross.{u} obj poly σ fam q glue rr uu he hu)
    (hf : RefineDatumRangeEq.{u} obj poly σ fam q glue rr uu he hu) :
    ∀ a b c : B, a ≠ b → a ≠ c → b ≠ c →
      Set.range (coverTripleIncl.{u} (refineDatumObj.{u} obj σ fam)
            (refineDatumPoly.{u} obj poly σ fam q) a b c ≫
          coverTransitionHom.{u} (refineDatumObj.{u} obj σ fam)
              (refineDatumPoly.{u} obj poly σ fam q)
              (refineDatumGlue.{u} obj σ fam poly q glue rr uu he hu) a b).base ⊆
        (coverOpen.{u} (refineDatumObj.{u} obj σ fam) (refineDatumPoly.{u} obj poly σ fam q) b c :
          Set (coverSpace.{u} (refineDatumObj.{u} obj σ fam) b)) := by
  intro a b c hab hac hbc
  by_cases h : σ b = σ c
  · by_cases h' : σ a = σ b
    · exact range_refineDatumTransitionHom_subset_of_eq.{u} obj poly σ fam q glue rr uu he hu
        h' (h'.trans h)
    · exact (range_refineDatumTransitionHom_subset_iff_of_eq_bc.{u} obj poly σ fam q glue rr uu
        he hu h).2 (hf a b c hab hac hbc h' h)
  · by_cases h₁ : σ a = σ b
    · exact (range_refineDatumTransitionHom_subset_iff_of_eq_ab.{u} obj poly σ fam q glue rr uu
        he hu h₁ fun e ↦ h (h₁.symm.trans e)).2 (hq a b c hab hac hbc h)
    · by_cases h₂ : σ a = σ c
      · exact (range_refineDatumTransitionHom_subset_iff_of_eq_ac.{u} obj poly σ fam q glue rr uu
          he hu h₁ h₂).2 (hq a b c hab hac hbc h)
      · exact (range_refineDatumTransitionHom_subset_iff.{u} obj poly σ fam q glue rr uu
          hrange he hu h₁ h₂ h).2 (hq a b c hab hac hbc h)

/-- **And the two conditions are exactly what the refined law asks**, so no weaker pair will do.

The four shape statements are equivalences and this is their `.1` directions collected; the
all-equal triple contributes nothing, since neither condition is quantified there. **It is what
makes the previous theorem an assembly rather than a strengthening**: a file that adopts a
hypothesis owes the statement that it adopted no more than the law, and
`ComplexAnalytic.range_refineDatumTransitionHom_subset_iff` set that standard on this line and
gave its reason. -/
theorem refineDatumHrange_iff
    (hrange : ∀ i j k : J, i ≠ j → i ≠ k → j ≠ k →
      Set.range (coverTripleIncl.{u} obj poly i j k ≫
          coverTransitionHom.{u} obj poly glue i j).base ⊆
        (coverOpen.{u} obj poly j k : Set (coverSpace.{u} obj j))) :
    (∀ a b c : B, a ≠ b → a ≠ c → b ≠ c →
        Set.range (coverTripleIncl.{u} (refineDatumObj.{u} obj σ fam)
              (refineDatumPoly.{u} obj poly σ fam q) a b c ≫
            coverTransitionHom.{u} (refineDatumObj.{u} obj σ fam)
                (refineDatumPoly.{u} obj poly σ fam q)
                (refineDatumGlue.{u} obj σ fam poly q glue rr uu he hu) a b).base ⊆
          (coverOpen.{u} (refineDatumObj.{u} obj σ fam) (refineDatumPoly.{u} obj poly σ fam q)
            b c : Set (coverSpace.{u} (refineDatumObj.{u} obj σ fam) b))) ↔
      RefineDatumRangeCross.{u} obj poly σ fam q glue rr uu he hu ∧
        RefineDatumRangeEq.{u} obj poly σ fam q glue rr uu he hu := by
  constructor
  · intro H
    refine ⟨fun a b c hab hac hbc h ↦ ?_, fun a b c hab hac hbc h' h ↦ ?_⟩
    · by_cases h₁ : σ a = σ b
      · exact (range_refineDatumTransitionHom_subset_iff_of_eq_ab.{u} obj poly σ fam q glue rr uu
          he hu h₁ fun e ↦ h (h₁.symm.trans e)).1 (H a b c hab hac hbc)
      · by_cases h₂ : σ a = σ c
        · exact (range_refineDatumTransitionHom_subset_iff_of_eq_ac.{u} obj poly σ fam q glue
            rr uu he hu h₁ h₂).1 (H a b c hab hac hbc)
        · exact (range_refineDatumTransitionHom_subset_iff.{u} obj poly σ fam q glue rr uu
            hrange he hu h₁ h₂ h).1 (H a b c hab hac hbc)
    · exact (range_refineDatumTransitionHom_subset_iff_of_eq_bc.{u} obj poly σ fam q glue rr uu
        he hu h).1 (H a b c hab hac hbc)
  · exact fun H ↦ refineDatumHrange.{u} obj poly σ fam q glue rr uu he hu hrange H.1 H.2

/-! ### The cocycle law, and the glue data -/

/-- **The cocycle law of the refined cover datum**, and this is the first file in which it can be
written down.

`ComplexAnalytic.coverTriple` takes a proof of `hrange` as an argument and this statement mentions
it three times, so it is not one case away from anything the five shape statements say: it needs
the range law as a *single* proof, which is `ComplexAnalytic.refineDatumHrange` above and nothing
earlier. Which proof is immaterial — the law is a `Prop` and any two proofs of it are
definitionally equal — but that there is one is the whole of the obstruction that stood here. -/
abbrev RefineDatumCocycle
    (hrange : ∀ i j k : J, i ≠ j → i ≠ k → j ≠ k →
      Set.range (coverTripleIncl.{u} obj poly i j k ≫
          coverTransitionHom.{u} obj poly glue i j).base ⊆
        (coverOpen.{u} obj poly j k : Set (coverSpace.{u} obj j)))
    (hq : RefineDatumRangeCross.{u} obj poly σ fam q glue rr uu he hu)
    (hf : RefineDatumRangeEq.{u} obj poly σ fam q glue rr uu he hu) : Prop :=
  ∀ a b c : B, ∀ hab : a ≠ b, ∀ hac : a ≠ c, ∀ hbc : b ≠ c,
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
            c a b hac.symm hbc.symm hab = 𝟙 _

/-- **The glue data of the refined cover, at a general `σ`.**

`ComplexAnalytic.coverGlueData` at the refined datum, and every argument of it is now supplied:
the members and the overlaps are `ComplexAnalytic.refineDatumObj` and
`ComplexAnalytic.refineDatumPoly`, the glue is `ComplexAnalytic.refineDatumGlue`, the symmetry
law is `ComplexAnalytic.refineDatumGlue_symm` and the range law is
`ComplexAnalytic.refineDatumHrange`. **The cocycle law is the one hypothesis left**, and it is
here as an explicit argument rather than as an absence for the reason this file exists: a law
that a definition asks for by name is a smaller thing to leave open than three laws that no
statement mentions. It is left open here and supplied in
`Oka/Analytification/RefineDatumCocycle.lean`, whose
`ComplexAnalytic.refineDatumGlueDataOfLaws` is this definition at
`ComplexAnalytic.refineDatumHcocycle` — so **this definition stays because it is the general one**,
not because the law is open. -/
def refineDatumGlueData
    (hsym : ∀ i j : J, glue j i = (glue i j).symm)
    (hrange : ∀ i j k : J, i ≠ j → i ≠ k → j ≠ k →
      Set.range (coverTripleIncl.{u} obj poly i j k ≫
          coverTransitionHom.{u} obj poly glue i j).base ⊆
        (coverOpen.{u} obj poly j k : Set (coverSpace.{u} obj j)))
    (hq : RefineDatumRangeCross.{u} obj poly σ fam q glue rr uu he hu)
    (hf : RefineDatumRangeEq.{u} obj poly σ fam q glue rr uu he hu)
    (hcocycle : RefineDatumCocycle.{u} obj poly σ fam q glue rr uu he hu hrange hq hf) :
    LocallyRingedSpace.GlueData.{u} :=
  coverGlueData.{u} (refineDatumObj.{u} obj σ fam) (refineDatumPoly.{u} obj poly σ fam q)
    (refineDatumGlue.{u} obj σ fam poly q glue rr uu he hu)
    (refineDatumHrange.{u} obj poly σ fam q glue rr uu he hu hrange hq hf)
    (refineDatumGlue_symm.{u} obj σ fam poly q glue rr uu hsym he hu) hcocycle

/-- **The analytic space the refined cover glues to.**

`ComplexAnalytic.coverAnalytification` at the same arguments. Nothing is proved here that the
previous definition does not already carry; it is separate because an
`AlgebraicGeometry.LocallyRingedSpace.GlueData` is gluing *data* and not a space — the space is
its `.toGlueData.glued`, which is what the theorem below says — and this is the object the
comparison of two covers is a statement about. -/
def refineDatumAnalytification
    (hsym : ∀ i j : J, glue j i = (glue i j).symm)
    (hrange : ∀ i j k : J, i ≠ j → i ≠ k → j ≠ k →
      Set.range (coverTripleIncl.{u} obj poly i j k ≫
          coverTransitionHom.{u} obj poly glue i j).base ⊆
        (coverOpen.{u} obj poly j k : Set (coverSpace.{u} obj j)))
    (hq : RefineDatumRangeCross.{u} obj poly σ fam q glue rr uu he hu)
    (hf : RefineDatumRangeEq.{u} obj poly σ fam q glue rr uu he hu)
    (hcocycle : RefineDatumCocycle.{u} obj poly σ fam q glue rr uu he hu hrange hq hf) :
    AnalyticSpace.{u} :=
  coverAnalytification.{u} (refineDatumObj.{u} obj σ fam) (refineDatumPoly.{u} obj poly σ fam q)
    (refineDatumGlue.{u} obj σ fam poly q glue rr uu he hu)
    (refineDatumHrange.{u} obj poly σ fam q glue rr uu he hu hrange hq hf)
    (refineDatumGlue_symm.{u} obj σ fam poly q glue rr uu hsym he hu) hcocycle

/-- **The refined cover's analytic space has the refined glue data's gluing underneath it**, with
no transport.

`ComplexAnalytic.coverAnalytification_toLocallyRingedSpace`, and it is stated here for that
theorem's own reason: without it the two definitions above are two well-typed objects with no
recorded relation to each other, and everything already proved about a
`ComplexAnalytic.coverGlueData`'s gluing reaches the analytic space only through this. -/
theorem refineDatumAnalytification_toLocallyRingedSpace
    (hsym : ∀ i j : J, glue j i = (glue i j).symm)
    (hrange : ∀ i j k : J, i ≠ j → i ≠ k → j ≠ k →
      Set.range (coverTripleIncl.{u} obj poly i j k ≫
          coverTransitionHom.{u} obj poly glue i j).base ⊆
        (coverOpen.{u} obj poly j k : Set (coverSpace.{u} obj j)))
    (hq : RefineDatumRangeCross.{u} obj poly σ fam q glue rr uu he hu)
    (hf : RefineDatumRangeEq.{u} obj poly σ fam q glue rr uu he hu)
    (hcocycle : RefineDatumCocycle.{u} obj poly σ fam q glue rr uu he hu hrange hq hf) :
    (refineDatumAnalytification.{u} obj poly σ fam q glue rr uu he hu hsym hrange hq hf
        hcocycle).toLocallyRingedSpace =
      (refineDatumGlueData.{u} obj poly σ fam q glue rr uu he hu hsym hrange hq hf
        hcocycle).toGlueData.glued :=
  coverAnalytification_toLocallyRingedSpace.{u} _ _ _ _ _ _

end

end ComplexAnalytic
