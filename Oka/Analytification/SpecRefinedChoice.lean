/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Analytification.SpecMemberChoice
import Oka.Analytification.SpecRefinedMemberSection

/-!
# The two-datum choice, read through the refined member

`Oka/Analytification/SpecMemberChoice.lean` ends at
`ComplexAnalytic.exists_family_mvPolynomial_basicOpen_specSchemeIotaMap`: given two cover data and
an isomorphism `Φ` of what they glue, there are four functions on the points of the glued scheme
`X` — a member of each datum and a polynomial in each member's own variables — such that at every
point the two polynomials cut out **the same open of `X`**, and that open contains the point. The
statement is in the *section* vocabulary: both sides are an `AlgebraicGeometry.Scheme.basicOpen`
of a `ComplexAnalytic.presentationSection`.

`Oka/Analytification/SpecRefinedMember.lean` reads a polynomial the other way, as a **presented
affine open**: `ComplexAnalytic.presentationRefinedIota` is an open immersion into `X` whose range
is that same open, and `ComplexAnalytic.isAffineOpen_presentationRefinedIota` says the range is an
affine open. `Oka/Analytification/SpecRefinedMemberSection.lean`'s
`ComplexAnalytic.opensRange_presentationRefinedIota_eq_basicOpen` is the equation between the two
vocabularies.

**This file applies the second to the first.** The one theorem below says the chosen data of a
two-datum choice, read as refined members, are the same affine open of `X` at every point, and
that the first family covers `X`.

## Why this needed the immersion to be arbitrary, and what that cost

The second conjunct of the choice step is about
`ComplexAnalytic.specSchemeIotaMap … Φ (idx' x)` — the `idx' x`-th member of the *second* datum,
carried into the first datum's scheme. **That morphism is not
`ComplexAnalytic.specSchemeIota` of anything in the first datum**, so until
`ComplexAnalytic.presentationRefinedIota` was stated at an arbitrary open immersion there was no
term for its refined member and the equation below could not be written down at all — only its
left-hand side could. `Oka/Analytification/SpecRefinedMember.lean`'s two-level section is the
argument in full and this file does not restate it; **what this file adds to it is a caller**,
which is the only thing that shows the generality was worth stating.

## Main results

- `ComplexAnalytic.exists_family_opensRange_presentationRefinedIota_eq`: **the two chosen refined
  members are the same affine open of the glued scheme at every point, and the first family covers
  it** — the choice step's conclusion, restated in the vocabulary of presented affine opens rather
  than of sections.

## Why this is a module of its own rather than a line in either file it imports

**Both candidate homes have a `## What is not here` bullet that is true today and that the theorem
below would falsify**, and that is the whole argument; the closure cost points the other way and is
the smaller consideration.

* `Oka/Analytification/SpecMemberChoice.lean` says **"No statement that the chosen opens cover
  anything"**, and spells out that *"the range of the family is a cover in any sense that a glue
  datum would accept is a statement about the assembly and is not made here."* The second conjunct
  below is exactly `⨆ x, … = ⊤` in the lattice of opens of `X`, so an append there falsifies that
  bullet outright rather than narrowing it.
* `Oka/Analytification/SpecRefinedMemberSection.lean` says **"No second cover datum"** — of which
  it says in terms that a carried member being a *legal argument* is not the same as one
  *appearing*, and that no statement there mentions two data — and also **"Nothing indexed by the
  points of `X`"**. The theorem below quantifies over two data, names
  `ComplexAnalytic.specSchemeIotaMap` inside a statement, and is indexed by points. It falsifies
  both.

**The closure figures say the opposite and are quoted so the trade is visible rather than
implied**: this module's closure is 92 `Oka` modules and 72 Mathlib roots, itself counted in,
against 91 and 72 for either append. **One `Oka` module and no Mathlib root is what a true
file-scoped bullet is worth here**, which is the same trade
`Oka/Analytification/SpecRefinedMemberSection.lean` recorded making for its own existence, and
`Oka/Analytification/SpecMemberChoice.lean` before it.

## What is not here

* **No index type for a refinement**, and nothing that turns the point-indexed family below into
  one. `Oka/Analytification/SpecMemberChoice.lean`'s `## What the index type is` says that a family
  indexed by the points of `X` is not a cover datum's index type and that **a refinement indexed by
  points is not a refinement anybody would assemble as a cover datum**; that stands, and the
  theorem below is indexed by points exactly as the theorem it is proved from is. Choosing a set of
  opens and an index type for it is the assembly step and is not here.
  **A cover has since been assembled out of this family, and not in this file**:
  `Oka/Analytification/SpecRefinedCover.lean` builds an
  `AlgebraicGeometry.Scheme.AffineOpenCover` of `X` indexed by the points, whose covering field is
  the second conjunct below. **That does not weaken this bullet**, which is about a cover *datum*'s
  index type — the three words added to the quoted sentence are that narrowing, made in the file
  that owns it — and it is one module downstream rather than here for the reason this file's own
  existence records: appending it would have falsified this bullet's first clause.
* **No `poly`, no `glue`, and none of a cover datum's three laws**, so nothing here is or produces
  a common refinement. That is `Oka/Analytification/CrossMemberDatum.lean`,
  `Oka/Analytification/CrossMemberDatumGlue.lean` and the `Oka/Analytification/RefineDatum*.lean`
  files, and this file adds to none of them.
* **Nothing that constructs the isomorphism `Φ`**, in either direction. It is a hypothesis here
  exactly as it is in `Oka/Analytification/SpecTwoData.lean`, and nothing in this repository
  produces one.
* **No affineness statement.** `ComplexAnalytic.isAffineOpen_presentationRefinedIota` applies to
  both sides of the equation below and a corollary saying so would carry no content that the two
  imports do not already have; a caller that wants it names that theorem directly.
* **No `def`s for the four functions.** The theorem below is an existential and recovers its
  witnesses from an `obtain`, for the three reasons
  `Oka/Analytification/SpecMemberChoice.lean`'s `## Existential over four functions, and not four
  definitions` gives of the theorem this one consumes. **Those reasons apply here unchanged**, and
  the first of them — that nothing consumes such definitions — is still true: this file consumes
  the existential and not any definition.
* **Nothing analytic.** No analytification, no `X^an`, no comparison morphism: everything here is
  on the `Spec` side, about a scheme glued from presented algebras.
* **Nothing about the chosen polynomials being non-zero, or the chosen opens being non-empty.**
  The covering statement forces the family to be jointly non-trivial when `X` is, and says nothing
  about any one member of it.
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

variable {K : Type u} (obj' : K → Presentation.{u})
  (poly' : ∀ i : K, K → MvPolynomial (ULift.{u} (Fin (obj' i).n)) ℂ)
  (glue' : ∀ i j : K, coverOverlap.{u} obj' poly' i j ≅ coverOverlap.{u} obj' poly' j i)
  (hrange' : ∀ i j k : K, i ≠ j → i ≠ k → j ≠ k →
    Set.range (specTripleIncl.{u} obj' poly' i j k ≫
        specTransitionHom.{u} obj' poly' glue' i j).base ⊆
      (specOpen.{u} obj' poly' j k : Set (specSpace.{u} obj' j)))
  (hsymm' : ∀ i j : K, glue' j i = (glue' i j).symm)
  (hcocycle' : ∀ i j k : K, ∀ hij : i ≠ j, ∀ hik : i ≠ k, ∀ hjk : j ≠ k,
    specTriple.{u} obj' poly' glue' hrange' i j k hij hik hjk ≫
      specTriple.{u} obj' poly' glue' hrange' j k i hjk hij.symm hik.symm ≫
      specTriple.{u} obj' poly' glue' hrange' k i j hik.symm hjk.symm hij = 𝟙 _)

/-- **The chosen members of a two-datum choice, read as refined members: the same affine open of
`X` at every point, and the first family covers `X`.**

`ComplexAnalytic.exists_family_mvPolynomial_basicOpen_specSchemeIotaMap` gives the four functions
and states the same two facts about `AlgebraicGeometry.Scheme.basicOpen` of a
`ComplexAnalytic.presentationSection`;
`ComplexAnalytic.opensRange_presentationRefinedIota_eq_basicOpen` rewrites each of the three
occurrences into the range of a `ComplexAnalytic.presentationRefinedIota`. **There is no new
mathematics here and the docstring says so rather than implying otherwise**: what the statement
buys is that both sides are now ranges of open immersions with a presentation attached, so
`ComplexAnalytic.isAffineOpen_presentationRefinedIota` applies to each and the opens are objects a
cover datum could be built out of rather than subsets named by a section.

**The second conjunct is a covering statement and the first is not.** `⨆ x, … = ⊤` is a statement
about the *range* of the family; the choice step states only that each point lies in its own
chosen open, and turning that into a supremum is `eq_top_iff` and `Opens.mem_iSup` and nothing
else. `Oka/Analytification/SpecMemberChoice.lean` declines to make that statement, in a
`## What is not here` bullet that stays true of that file; it is made here.

**The `⨆` is over the points of `X` and that is not a cover datum's index type.** This statement
assembles nothing, and the family is not a refinement in any sense a glue datum would accept —
`Oka/Analytification/SpecMemberChoice.lean`'s `## What the index type is` is the standing statement
and this theorem does not move it.

**The rewrite direction matters and the proof is not symmetric in it.** Each `rw` replaces a range
by a basic open, which is the direction that turns this file's statement into the imported one; the
opposite direction would leave the goal in a vocabulary `ComplexAnalytic.presentationSection` is
not stated in. -/
theorem exists_family_opensRange_presentationRefinedIota_eq
    (Φ : specScheme.{u} obj' poly' glue' hrange' hsymm' hcocycle' ⟶
      specScheme.{u} obj poly glue hrange hsymm hcocycle) [IsIso Φ] :
    ∃ (idx : specScheme.{u} obj poly glue hrange hsymm hcocycle → J)
      (idx' : specScheme.{u} obj poly glue hrange hsymm hcocycle → K)
      (fam : ∀ x, MvPolynomial (ULift.{u} (Fin (obj (idx x)).n)) ℂ)
      (fam' : ∀ x, MvPolynomial (ULift.{u} (Fin (obj' (idx' x)).n)) ℂ),
      (∀ x, (presentationRefinedIota.{u}
              (specSchemeIota.{u} obj poly glue hrange hsymm hcocycle (idx x))
                (fam x)).opensRange =
            (presentationRefinedIota.{u} (specSchemeIotaMap.{u} obj poly glue hrange hsymm hcocycle
              obj' poly' glue' hrange' hsymm' hcocycle' Φ (idx' x)) (fam' x)).opensRange) ∧
        ⨆ x, (presentationRefinedIota.{u}
          (specSchemeIota.{u} obj poly glue hrange hsymm hcocycle (idx x))
            (fam x)).opensRange = ⊤ := by
  obtain ⟨idx, idx', fam, fam', h⟩ :=
    exists_family_mvPolynomial_basicOpen_specSchemeIotaMap.{u} obj poly glue hrange hsymm hcocycle
      obj' poly' glue' hrange' hsymm' hcocycle' Φ
  refine ⟨idx, idx', fam, fam', fun x => ?_, ?_⟩
  · rw [opensRange_presentationRefinedIota_eq_basicOpen,
      opensRange_presentationRefinedIota_eq_basicOpen]
    exact (h x).1
  · rw [eq_top_iff]
    intro x _
    rw [Opens.mem_iSup]
    exact ⟨x, by rw [opensRange_presentationRefinedIota_eq_basicOpen]; exact (h x).2⟩

end

end ComplexAnalytic
