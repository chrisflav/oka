/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Analytification.SpecMemberSections

/-!
# The open at every point becomes a family of opens, chosen

`Oka/Analytification/SpecScheme.lean` says what a common refinement of two cover data needs, and
names three pieces: **two data and an isomorphism of what they glue**, **a choice of such an open
at every point**, and **the refined family assembled into a cover datum with its three laws**.
`Oka/Analytification/SpecTwoData.lean` is the first. `Oka/Analytification/SpecMemberSections.lean`
ends with `ComplexAnalytic.exists_index_mvPolynomial_basicOpen_specSchemeIotaMap`, which is the
second **at each point separately**: for every point of the first datum's scheme *there exist* a
member of each datum and polynomials in their own variables cutting out the same open, containing
that point.

**This file takes the word *choice* in that sentence.** One `choose` turns the pointwise
existential into four functions defined on the whole scheme — two indices and two polynomials —
and that is the entire content: no new mathematics, and `Classical.choice` at every point.

## What the index type is, said here rather than left to be inferred

**The four functions are indexed by the points of `X`.** That is not a cover datum's index type,
and nothing below claims it is. A refinement indexed by points is not a refinement anybody would
assemble **as a cover datum** — the assembly step chooses a *set* of opens and an index type for
it, out of the family below or otherwise, and that choice is not made here. **So this file is the
second piece and not the third**, and the third is
`Oka/Analytification/CrossMemberDatum.lean`'s line, on the other side of the comparison.

**Those three words are a narrowing and the sentence was wider when it was written; the wider form
is false and the reason is worth having here.** `AlgebraicGeometry.Scheme.AffineOpenCover`'s index
type is arbitrary and it carries its own choice function from the points of the scheme, so the
family below *is* an affine open cover of `X` with no set chosen and no index type invented —
`Oka/Analytification/SpecRefinedCover.lean` assembles exactly that and says so. What a cover
**datum** additionally needs is `poly`, the three laws, and the condition that every pairwise
overlap be a distinguished open of *each* of the two members it lies in; that condition is what
makes the third piece the work it is, and it is what this section is about.

**It is not equally out of reach at every pair, and the two halves are not the same size.** At
two chosen opens sitting inside the **same** member the overlap is a chosen open of *that* member
again, at the product of the two polynomials —
`ComplexAnalytic.opensRange_presentationRefinedIota_inf`, which is
`AlgebraicGeometry.Scheme.basicOpen_mul` and needs nothing else. **That is a statement about the
member the two sit inside, and it is not the condition at either of them**: the condition asks
for a polynomial in each chosen open's *own* variables, of which a chosen open has one more than
the member does, and the map that carries a polynomial across is the one
`ComplexAnalytic.localisationIncl` names. **A statement on this line does carry one across it** —
`ComplexAnalytic.opensRange_presentationRefinedIota_rename`
(`Oka/Analytification/SpecRefinedMemberSection.lean`) says the overlap is the chosen open of the
first at the second's polynomial renamed along that map, and at the exchanged pair it is the
condition at the second. **So at a same-member pair the condition holds**; what is still absent
there is a `poly` — a function of two *indices* — and the three laws, and not the geometry.

At two sitting inside **different** members the two sections live over different opens,
`AlgebraicGeometry.Scheme.basicOpen_mul` does not typecheck, and what is available is the
**pointwise** statement this section produces and not a statement about the overlap itself.
**That half is what the points of `X` cannot supply**, and it is the half the third piece is
against.

## Existential over four functions, and not four definitions

The `choose` below can as easily produce four `def`s with three theorems relating them, and that
is the shape a cover datum would consume. **This file states the existential**, for three reasons
worth having on the record rather than in a commit message:

* **Nothing consumes them.** Four `noncomputable` definitions whose value at every point is
  `Classical.choice` would be four names in the environment and no caller. A consumer that wants
  them recovers them from the statement below with the same one-tactic `choose` that produced it.
* **The definitions would not be canonical.** Nothing distinguishes one choice of index and
  polynomial at a point from another, so a `def` would name an arbitrary member of a class and
  every later statement about it would have to carry the arbitrariness anyway.
* **The existential is what a reader can use without unfolding.**
  `Oka/Analytification/CrossMemberChoice.lean`, which is the same step on the analytic side, made
  the same call: it ends at `ComplexAnalytic.exists_refineDatumCross`, an existential over three
  families with two laws, and its own `## What is not here` says of it that the file *"produces a
  choice"* and that *"applying `ComplexAnalytic.refineDatumGlue` to it and reading the result back
  is a separate step"*. It stopped there with the field already waiting —
  `ComplexAnalytic.refineDatumGlueNe` takes that choice as explicit arguments and is *upstream* of
  that file, in `Oka/Analytification/CrossMemberDatumGlue.lean`, its only import. So the precedent
  is for the existential, and it is stronger than this file needs: there, a field was waiting and
  the existential was still the right shape; here there is no field at all.

**If the assembly step lands and wants definitions, this is one `choose` away and the change is
additive.** Recording the decision rather than the alternative is the point of this section.

## Main results

- `ComplexAnalytic.exists_family_mvPolynomial_basicOpen_specSchemeIotaMap`: **the pointwise
  existential of `ComplexAnalytic.exists_index_mvPolynomial_basicOpen_specSchemeIotaMap` as four
  functions on the scheme** — at every point, the two chosen members' two chosen polynomials cut
  out the same open of the glued scheme, and that open contains the point.

## What is not here

* **No `poly`, no `glue`, and none of a cover datum's three laws**, so nothing here is or produces
  a common refinement. That is `Oka/Analytification/CrossMemberDatum.lean`,
  `Oka/Analytification/CrossMemberDatumGlue.lean` and the `Oka/Analytification/RefineDatum*.lean`
  files, and this file adds to none of them.
* **No index type for a refinement**, as the section above says: the family is indexed by points.
  **A cover of `X` has since been built out of that family, and not in this file**:
  `Oka/Analytification/SpecRefinedCover.lean` assembles it into an
  `AlgebraicGeometry.Scheme.AffineOpenCover` indexed by the points. That is not a cover *datum* and
  does not weaken this bullet, which is about the index type a refinement would be assembled at.
* **Nothing that constructs the isomorphism `Φ`**, in either direction. It is a hypothesis here
  exactly as it is in `Oka/Analytification/SpecTwoData.lean`, and nothing in this repository
  produces one.
* **Nothing analytic.** No analytification, no `X^an`, no comparison morphism: everything here is
  on the `Spec` side, about a scheme glued from presented algebras.
* **No statement that the chosen opens cover anything.** Every point lies in its own chosen open,
  which is what the theorem says; that the *range* of the family is a cover in any sense that a
  glue datum would accept is a statement about the assembly and is not made here. **A supremum
  statement about the same family has since been added, and not to this file**:
  `Oka/Analytification/SpecRefinedChoice.lean` says `⨆ x, … = ⊤` in the lattice of opens of the
  glued scheme, over the points of that scheme. **That does not weaken this bullet and the
  distinction is the one this bullet already draws**: a supremum over the points of `X` is not a
  cover *a glue datum would accept*, because the points of `X` are not a cover datum's index type
  — this file's `## What the index type is` section is the standing statement on that — and the
  supremum is one module downstream rather than here for the reason that file gives, which is that
  appending it would have falsified this bullet.
-/

open CategoryTheory AlgebraicGeometry

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

/-- **The pointwise existential of
`ComplexAnalytic.exists_index_mvPolynomial_basicOpen_specSchemeIotaMap`, chosen into four
functions on the whole scheme.**

At an isomorphism `Φ` of what the two data glue, there are functions assigning to every point of
the first datum's scheme a member of each datum and a polynomial in each member's own variables,
such that the two opens those polynomials cut out agree and contain the point.

**`choose` is the whole proof and the dependency is the only thing in it that could fail**: `fam x`
is a polynomial in `(obj (idx x))`'s variables, so its type mentions `idx`, which is being chosen
in the same call. It elaborates.

**The functions are indexed by the points of the scheme**, which is not a cover datum's index type;
this file's `## What is not here` says so, and nothing below is a common refinement. -/
theorem exists_family_mvPolynomial_basicOpen_specSchemeIotaMap
    (Φ : specScheme.{u} obj' poly' glue' hrange' hsymm' hcocycle' ⟶
      specScheme.{u} obj poly glue hrange hsymm hcocycle) [IsIso Φ] :
    ∃ (idx : specScheme.{u} obj poly glue hrange hsymm hcocycle → J)
      (idx' : specScheme.{u} obj poly glue hrange hsymm hcocycle → K)
      (fam : ∀ x, MvPolynomial (ULift.{u} (Fin (obj (idx x)).n)) ℂ)
      (fam' : ∀ x, MvPolynomial (ULift.{u} (Fin (obj' (idx' x)).n)) ℂ),
      ∀ x, (specScheme.{u} obj poly glue hrange hsymm hcocycle).basicOpen
            (presentationSection.{u}
              (specSchemeIota.{u} obj poly glue hrange hsymm hcocycle (idx x)) (fam x)) =
          (specScheme.{u} obj poly glue hrange hsymm hcocycle).basicOpen
            (presentationSection.{u} (specSchemeIotaMap.{u} obj poly glue hrange hsymm hcocycle
              obj' poly' glue' hrange' hsymm' hcocycle' Φ (idx' x)) (fam' x)) ∧
        x ∈ (specScheme.{u} obj poly glue hrange hsymm hcocycle).basicOpen
          (presentationSection.{u}
            (specSchemeIota.{u} obj poly glue hrange hsymm hcocycle (idx x)) (fam x)) := by
  choose idx idx' fam fam' h using
    exists_index_mvPolynomial_basicOpen_specSchemeIotaMap.{u} obj poly glue hrange hsymm hcocycle
      obj' poly' glue' hrange' hsymm' hcocycle' Φ
  exact ⟨idx, idx', fam, fam', h⟩

end

end ComplexAnalytic
