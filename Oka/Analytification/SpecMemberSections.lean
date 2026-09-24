/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Analytification.SpecTwoData
import Oka.AlgebraicGeometry.OpenImmersion

/-!
# A section over a member of the glued `Spec` is a polynomial in that member's variables

`Oka/Analytification/SpecScheme.lean` glues the spectra of the algebras a cover datum presents
into a scheme `X`, exhibits each member as an affine open
(`ComplexAnalytic.isAffineOpen_specSchemeIota`), and ends with
`ComplexAnalytic.exists_basicOpen_specSchemeIota_inter`: every point of the overlap of two members
lies in an open distinguished in both. `Oka/Analytification/SpecTwoData.lean` carries the members
of a *second* cover datum into the same scheme along a morphism `Φ` of what the two glue and ends
with the same statement across the two data. **Both produce sections, and a cover datum is not
written in sections.** Its `poly i j` is a polynomial in the member's own variables, and the gap
between the two vocabularies is what this file closes, at one datum and at two.

**`ComplexAnalytic.exists_mvPolynomial_basicOpen_specSchemeIota_inter` is the first declaration in
this repository whose proof term reads `ComplexAnalytic.exists_basicOpen_specSchemeIota_inter`**,
and **two** files recorded that theorem as having none:
`Oka/Analytification/SpecAffineCover.lean`'s *"which no declaration consumes yet"* and
`Oka/Analytification/SpecTwoData.lean`'s *"That theorem still has none"*. **The commit that adds
this file repairs both.** An earlier head of it said the first was *the only* such site; that was
true when it was written and stopped being true when lana-agents/oka#371 landed the second while
this branch was in review. **A claim about the whole tree, made from a branch, is falsified by
whatever lands next, and this one was.**

The sweep is a `grep` and not a reading, so the pattern rather than the adjective: `grep -rniE`
over `Oka/` for *no declaration consumes*, *nothing consumes*, *has no consumer*
and *no consumer of*. Its other hits are `Oka/Analytic/DividedDifference.lean` and
`Oka/AnalyticSpace/SimpleZeroStalk.lean`, about other objects, and
`Oka/Analytification/CoverIndependence.lean`'s *"Nothing consumes it yet"*, which is about
naturality of the cover-datum isomorphism. **Being its consumer is not being what asked for it**:
what the repaired clauses are about is a common refinement, and the theorems below restate the
local form rather than assembling one.

The bridge is `AlgebraicGeometry.IsOpenImmersion.specΓIsoTop`
(`Oka/AlgebraicGeometry/OpenImmersion.lean`, a mirror-tree file with no analytic content):
sections of `𝒪_X` over the range of an open immersion out of `Spec` of a presented algebra are
that algebra, which is `ComplexAnalytic.PresentedAlgebra` and so a quotient of a polynomial ring
by `abbrev`. One application of `Ideal.Quotient.mk_surjective` turns an element of it into a
polynomial. **Nothing below turns on how routine that step is elsewhere in the tree, and the three
attempts to say so by counting disagree**: taxis #1513 priced it at *"fifteen sites"*, taxis #1521
corrected that to *"29 sites in 18 files"*, and re-running the grep at `master` = `bbc30d6` gave
**28 in 17**. No two agree and nothing checks any of them, which is why the claim this paragraph
makes is that the step is *one application* — a fact about the declarations below and not a census
of the repository.

## The immersion is the argument, and that is what makes the two-datum statement sayable

`ComplexAnalytic.presentationSection` takes an **arbitrary** open immersion
`f : Spec (CommRingCat.of P.alg) ⟶ X` out of a presentation's spectrum, and the three theorems
about it are stated there rather than at a member of a cover datum. That is not generality for its
own sake and it was not the first shape this file had. **A member of the second datum, carried
into the first datum's scheme, is `ComplexAnalytic.specSchemeIotaMap` and is not
`ComplexAnalytic.specSchemeIota` of anything in the first datum**, so a lemma stated only at
`specSchemeIota` reaches one of the two sides of the cross-datum statement and not the other.
Stated at the immersion, one name spells both sides.

An earlier head of this file stated the three at `ComplexAnalytic.specSchemeIota` and declined the
cross-datum theorem, pricing it at *"the same two `obtain`s"* as the one-datum form. **That price
was wrong for exactly this reason** — the second lift had no lemma to be an `obtain` at, and the
second side of the conclusion had no name — and it was found by compiling the sentence rather than
by reading it (lana-agents/oka#374, `oka-slot-2-ea`). With the general form the price is right:
the last two theorems below are two lifts and an `exact`, the same shape as the one-datum theorem
above them. **The sentence became true by a change to the library and not by a change to the
sentence**, which is the only repair of a price that is worth more than deleting it.

`ComplexAnalytic.specSchemeIotaSection` survives as the one-datum spelling, defined as the general
form at `ComplexAnalytic.specSchemeIota`, because the immersion carries six arguments of cover
datum in front of the index and every one-datum statement would spell them twice without it. It is
a specialisation and not a second definition: the three theorems about it are the general ones
applied, with no proof of their own.

## Which open the statement is about, and it is a theorem here rather than a decision

`X.basicOpen f` for a section `f` is an open of the **glued scheme**; what a cover datum's
`poly i j` cuts out is an open of the **member**, `Spec` of that member's algebra. A statement in
polynomials has to say which of the two it means, and the two descriptions are not interchangeable
by fiat. `ComplexAnalytic.basicOpen_presentationSection` says they agree: the distinguished open
of `ComplexAnalytic.presentationSection f p` in `X` **is** the image under `f` of `D(p)` in the
member. So the statements below are about opens of `X` — which is what
`ComplexAnalytic.exists_basicOpen_specSchemeIota_inter` and
`ComplexAnalytic.exists_index_basicOpen_specSchemeIotaMap` are already about, so nothing had to be
restated — and the member-side reading is available from the same theorem read backwards.

## Why a module of its own

Three facts, and only the last one is now load-bearing.

* **`Oka/Analytification/SpecScheme.lean` was being edited by lana-agents/oka#371 when this file
  was written**, in the module-docstring paragraphs a `## Main results` entry here would sit
  between. Nothing here needed any part of that edit, so a new module bought a merge with no
  conflict for the price of one import line. **That branch has since landed and this reason is
  spent.**
* **Folding this back into `Oka/Analytification/SpecScheme.lean` is no longer a move and a
  deletion**, which is what an earlier head of this file said it was. The last two theorems below
  are about two cover data, so they read `ComplexAnalytic.specSchemeIotaMap` and this module now
  imports `Oka/Analytification/SpecTwoData.lean`; `Oka/Analytification/SpecScheme.lean` is
  upstream of that file and cannot state them. **Folding back is available for the first four
  declarations only, and would split the file.**
* The subject is different. Those files' subjects are *the members are affine opens* and *the
  members of a second datum are affine opens of the first's scheme*; this one's is *what a section
  over a member is*, which is the vocabulary a common refinement is stated in and not a fact about
  the covers.

## Main definitions

- `ComplexAnalytic.presentationSection`: the section of `𝒪_X` over the range of an open immersion
  out of a presented algebra's spectrum, attached to a polynomial in that presentation's
  variables.
- `ComplexAnalytic.specSchemeIotaSection`: that at `ComplexAnalytic.specSchemeIota`, the section
  over the `i`-th member's range.

## Main results

- `ComplexAnalytic.surjective_presentationSection`: **every section over the range comes from a
  polynomial in the presentation's variables**, and
  `ComplexAnalytic.surjective_specSchemeIotaSection` is that at a member of a cover datum.
- `ComplexAnalytic.basicOpen_presentationSection`: **the open it cuts out in `X` is the image of
  `D(p)`**, with `ComplexAnalytic.basicOpen_specSchemeIotaSection` the same at a member.
- `ComplexAnalytic.exists_mvPolynomial_basicOpen_specSchemeIota_inter`: **the polynomial form of
  `ComplexAnalytic.exists_basicOpen_specSchemeIota_inter`** — every point of the overlap of two
  members lies in an open cut out by a polynomial in either member's variables.
- `ComplexAnalytic.exists_mvPolynomial_basicOpen_specSchemeIotaMap_inter`: **the same across two
  cover data**, at a member of each.
- `ComplexAnalytic.exists_index_mvPolynomial_basicOpen_specSchemeIotaMap`: **the polynomial form
  of `ComplexAnalytic.exists_index_basicOpen_specSchemeIotaMap`** — at every point of the first
  datum's scheme there are a member of each datum and polynomials in their own variables cutting
  out the same open through the point, with no index handed in.

## What is not here

* **No common refinement**, and no part of one. There is no choice function, no refined family and
  none of a cover datum's three laws; `Oka/Analytification/SpecScheme.lean` names those three
  pieces and this file adds to none of them. What it adds is the vocabulary they would be stated
  in. **The last theorem below is the second piece pointwise** — a statement at every point,
  across two data, in polynomials — **and it is an existential rather than a choice, which is
  what keeps this file clear of that piece.** This bullet said it was *"the closest this
  repository comes"* to the second piece; that is no longer true of the repository, only of this
  file. `ComplexAnalytic.exists_family_mvPolynomial_basicOpen_specSchemeIotaMap`
  (`Oka/Analytification/SpecMemberChoice.lean`) takes the word *choice*, in one `choose` on the
  theorem below and nothing else, and the second piece is therefore no longer anywhere absent.
* **Nothing that constructs `Φ`**, and nothing that says two cover data with isomorphic gluings
  have anything else in common. `Oka/Analytification/SpecTwoData.lean` says the same of itself and
  the last two theorems here inherit its hypotheses unchanged: an open immersion for the fixed-index
  form, an isomorphism for the one that produces its indices.
* **Nothing about `ComplexAnalytic.coverOverlap` or `poly`.** The polynomials produced below are
  existential and are not claimed to be the cover datum's own `poly i j`, nor related to it. That
  they could be chosen to agree is a different statement and nothing here bears on it.
* **Nothing on the analytic side.** No analytification, no comparison morphism, and no statement
  about `X^an`.

**One instrument fact this file paid for and is worth keeping now that it no longer applies.**
While `Oka/Analytification/SpecTwoData.lean` was unmerged, a `## What is not here` bullet here
cited `ComplexAnalytic.exists_index_basicOpen_specSchemeIotaMap` and deliberately did not backtick
it: the name resolved to nothing, and `scripts/check_docstring_names.py` reports a forward
reference to an unmerged declaration rather than passing it — which it did to a first draft.
**A backticked *path* is checked by nothing in either state**, for the opposite reason: the checker
skips any backticked token containing `/`, so a path that does not exist is never reported. While
the name could not be cited, the pull-request number was what made the citation checkable; now the
name is, and it is a hypothesis of a theorem rather than a citation.
-/

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

universe u

namespace ComplexAnalytic

noncomputable section

/-! ### A polynomial as a section over any member -/

section

variable {X : Scheme.{u}} {P : Presentation.{u}} (f : Spec (CommRingCat.of P.alg) ⟶ X)
  [IsOpenImmersion f]

/-- **The section of `𝒪_X` over the range of an open immersion out of a presented algebra's
spectrum, attached to a polynomial in that presentation's variables.**

`AlgebraicGeometry.IsOpenImmersion.specΓIsoTop` at `f`, whose source is `Spec` of `P.alg`, applied
to the class of `p`. `ComplexAnalytic.Presentation.alg` is `ComplexAnalytic.PresentedAlgebra` by
`abbrev` and that is a quotient of the polynomial ring by `abbrev` again, so `Ideal.Quotient.mk` is
the only step between a polynomial and an element of the algebra and no coercion is inserted here.

**The morphism is arbitrary and that is the point.** A member of a cover datum reaches this at
`ComplexAnalytic.specSchemeIota`; a member of a *second* datum carried into the first datum's
scheme reaches it at `ComplexAnalytic.specSchemeIotaMap`, which is not `specSchemeIota` of anything
in the first datum. Stating it once at the immersion is what lets the cross-datum theorem at the
end of this file spell its two sides with the same word. -/
def presentationSection (p : MvPolynomial (ULift.{u} (Fin P.n)) ℂ) : Γ(X, f.opensRange) :=
  (IsOpenImmersion.specΓIsoTop f).hom (Ideal.Quotient.mk (presentationIdeal.{u} P.g) p)

/-- **Every section over the range comes from a polynomial in the presentation's variables.**

Two surjections composed: `AlgebraicGeometry.IsOpenImmersion.specΓIsoTop` is an isomorphism, and
`Ideal.Quotient.mk_surjective` covers its target. Nothing else is used — in particular the
presentation's relations `P.g` play no part, and the polynomial produced is unique only modulo
them.

**`simp` does not close the last step and `CategoryTheory.Iso.inv_hom_id_apply` does.** The goal
after the rewrite is `e.hom (e.inv s) = s` for the isomorphism `e`, which is that lemma on the
nose; the `simp` set reaches it only through the `ConcreteCategory` coercion and does not here.
(The direction is the one it is because
`AlgebraicGeometry.IsOpenImmersion.specΓIsoTop` runs `R ≅ Γ(Y, f.opensRange)`, following
`AlgebraicGeometry.IsOpenImmersion.ΓIsoTop`; a first version of this file ran the other way and
this sentence named `CategoryTheory.Iso.hom_inv_id_apply`.)

**The `change` is what keeps the definition above from acquiring an equation lemma, and that is
measured rather than assumed.** The step it replaces was `rw [presentationSection, hp]`, which
names a `def` as a rewrite rule and so asks Lean to generate `presentationSection.eq_1`:
`scripts/DumpOkaDecls.lean` then reports one declaration more for this module than it declares.
`change` goes through definitional unfolding and generates nothing. It is `change` and not `show`
because the style linter rejects `show` in this position, and this repository already uses `change`
for exactly this job. -/
theorem surjective_presentationSection :
    Function.Surjective (presentationSection.{u} f) := by
  intro s
  obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective ((IsOpenImmersion.specΓIsoTop f).inv s)
  refine ⟨p, ?_⟩
  change (IsOpenImmersion.specΓIsoTop f).hom
    (Ideal.Quotient.mk (presentationIdeal.{u} P.g) p) = s
  rw [hp]
  exact Iso.inv_hom_id_apply _ s

/-- **The open that section cuts out in `X` is the image of `D(p)` under the immersion.**

`AlgebraicGeometry.IsOpenImmersion.image_primeSpectrum_basicOpen` read backwards. This is what
makes a statement in polynomials say the same thing whichever of the two spaces it is read in, and
it is why the theorems below could be stated about opens of `X` without a second description: an
open of the glued scheme distinguished by a section over a member **is** an open of that member,
transported. -/
theorem basicOpen_presentationSection (p : MvPolynomial (ULift.{u} (Fin P.n)) ℂ) :
    X.basicOpen (presentationSection.{u} f p) =
      f ''ᵁ PrimeSpectrum.basicOpen (Ideal.Quotient.mk (presentationIdeal.{u} P.g) p) :=
  (IsOpenImmersion.image_primeSpectrum_basicOpen _ _).symm

end

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

/-! ### A polynomial as a section over a member of one cover datum -/

/-- **The section of `𝒪_X` over the `i`-th member's range attached to a polynomial in that
member's variables.**

`ComplexAnalytic.presentationSection` at `ComplexAnalytic.specSchemeIota`, which is an open
immersion out of `Spec` of `(obj i).alg`. It is a declaration of its own and not a local
abbreviation because the immersion carries the whole cover datum: the general form takes six
arguments before the index, and every statement below that mentions one member of one datum would
spell them twice. -/
def specSchemeIotaSection (i : J) (p : MvPolynomial (ULift.{u} (Fin (obj i).n)) ℂ) :
    Γ(specScheme.{u} obj poly glue hrange hsymm hcocycle,
      (specSchemeIota.{u} obj poly glue hrange hsymm hcocycle i).opensRange) :=
  presentationSection.{u} (specSchemeIota.{u} obj poly glue hrange hsymm hcocycle i) p

/-- **Every section over the `i`-th member's range comes from a polynomial in that member's
variables.**

`ComplexAnalytic.surjective_presentationSection` at the same immersion. The two are the same
statement: `ComplexAnalytic.specSchemeIotaSection` at a fixed `i` is that function eta-expanded,
and the term closes the difference definitionally. -/
theorem surjective_specSchemeIotaSection (i : J) :
    Function.Surjective (specSchemeIotaSection.{u} obj poly glue hrange hsymm hcocycle i) :=
  surjective_presentationSection.{u} (specSchemeIota.{u} obj poly glue hrange hsymm hcocycle i)

/-- **The open that section cuts out in `X` is the image of `D(p)` in the member.**

`ComplexAnalytic.basicOpen_presentationSection` at the same immersion. What the specialisation
adds is the index: the general form describes the open as the image under *an* immersion, and here
it is the image under the `i`-th member's own, so the open is named by a member of this cover datum
rather than by a morphism the reader has to supply. -/
theorem basicOpen_specSchemeIotaSection (i : J)
    (p : MvPolynomial (ULift.{u} (Fin (obj i).n)) ℂ) :
    (specScheme.{u} obj poly glue hrange hsymm hcocycle).basicOpen
        (specSchemeIotaSection.{u} obj poly glue hrange hsymm hcocycle i p) =
      (specSchemeIota.{u} obj poly glue hrange hsymm hcocycle i) ''ᵁ
        PrimeSpectrum.basicOpen (Ideal.Quotient.mk (presentationIdeal.{u} (obj i).g) p) :=
  basicOpen_presentationSection.{u} (specSchemeIota.{u} obj poly glue hrange hsymm hcocycle i) p

/-! ### The overlap of two members, in polynomials -/

/-- **The polynomial form of `ComplexAnalytic.exists_basicOpen_specSchemeIota_inter`**: every
point of the overlap of two members lies in an open cut out by a polynomial in either member's
variables.

That theorem's two sections, lifted by `ComplexAnalytic.surjective_specSchemeIotaSection` at each
member. **No new geometry**: the equality of opens and the membership are the ones it already
produces and are carried across the lift by `rfl`, which is why the proof destructures that
theorem's output and lifts each of its two sections and there is nothing between the last `obtain`
and the `exact`.

**One cover datum and two of its members**, not two data. The cross-datum statement this is the
single-datum shadow of is at the end of this file. -/
theorem exists_mvPolynomial_basicOpen_specSchemeIota_inter (i j : J)
    (x : specScheme.{u} obj poly glue hrange hsymm hcocycle)
    (hx : x ∈ (specSchemeIota.{u} obj poly glue hrange hsymm hcocycle i).opensRange ⊓
      (specSchemeIota.{u} obj poly glue hrange hsymm hcocycle j).opensRange) :
    ∃ (p : MvPolynomial (ULift.{u} (Fin (obj i).n)) ℂ)
      (q : MvPolynomial (ULift.{u} (Fin (obj j).n)) ℂ),
      (specScheme.{u} obj poly glue hrange hsymm hcocycle).basicOpen
          (specSchemeIotaSection.{u} obj poly glue hrange hsymm hcocycle i p) =
        (specScheme.{u} obj poly glue hrange hsymm hcocycle).basicOpen
          (specSchemeIotaSection.{u} obj poly glue hrange hsymm hcocycle j q) ∧
      x ∈ (specScheme.{u} obj poly glue hrange hsymm hcocycle).basicOpen
        (specSchemeIotaSection.{u} obj poly glue hrange hsymm hcocycle i p) := by
  obtain ⟨s, t, hst, hxs⟩ :=
    exists_basicOpen_specSchemeIota_inter.{u} obj poly glue hrange hsymm hcocycle i j x hx
  obtain ⟨p, rfl⟩ := surjective_specSchemeIotaSection.{u} obj poly glue hrange hsymm hcocycle i s
  obtain ⟨q, rfl⟩ := surjective_specSchemeIotaSection.{u} obj poly glue hrange hsymm hcocycle j t
  exact ⟨p, q, hst, hxs⟩

/-! ### The overlap across two cover data, in polynomials -/

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

/-- **The polynomial form of `ComplexAnalytic.exists_basicOpen_specSchemeIotaMap_inter`**: every
point of the overlap of a member of the first datum with a carried member of the second lies in an
open cut out by a polynomial in either member's own variables.

That theorem's two sections, lifted by `ComplexAnalytic.surjective_presentationSection` at each of
the two immersions. **The second side is not a `ComplexAnalytic.specSchemeIotaSection`**: a carried
member is `ComplexAnalytic.specSchemeIotaMap`, an immersion of the *second* datum's `j`-th spectrum
into the *first* datum's scheme, and it is not `ComplexAnalytic.specSchemeIota` of anything in the
first datum. That is what the general form at the head of this file is for, and with it the two
sides are the same word at two different immersions. -/
theorem exists_mvPolynomial_basicOpen_specSchemeIotaMap_inter
    (Φ : specScheme.{u} obj' poly' glue' hrange' hsymm' hcocycle' ⟶
      specScheme.{u} obj poly glue hrange hsymm hcocycle) [IsOpenImmersion Φ] (i : J) (j : K)
    (x : specScheme.{u} obj poly glue hrange hsymm hcocycle)
    (hx : x ∈ (specSchemeIota.{u} obj poly glue hrange hsymm hcocycle i).opensRange ⊓
      (specSchemeIotaMap.{u} obj poly glue hrange hsymm hcocycle obj' poly' glue' hrange' hsymm'
        hcocycle' Φ j).opensRange) :
    ∃ (p : MvPolynomial (ULift.{u} (Fin (obj i).n)) ℂ)
      (q : MvPolynomial (ULift.{u} (Fin (obj' j).n)) ℂ),
      (specScheme.{u} obj poly glue hrange hsymm hcocycle).basicOpen
          (presentationSection.{u}
            (specSchemeIota.{u} obj poly glue hrange hsymm hcocycle i) p) =
        (specScheme.{u} obj poly glue hrange hsymm hcocycle).basicOpen
          (presentationSection.{u} (specSchemeIotaMap.{u} obj poly glue hrange hsymm hcocycle
            obj' poly' glue' hrange' hsymm' hcocycle' Φ j) q) ∧
      x ∈ (specScheme.{u} obj poly glue hrange hsymm hcocycle).basicOpen
        (presentationSection.{u}
          (specSchemeIota.{u} obj poly glue hrange hsymm hcocycle i) p) := by
  obtain ⟨f, g, hfg, hxf⟩ :=
    exists_basicOpen_specSchemeIotaMap_inter.{u} obj poly glue hrange hsymm hcocycle obj' poly'
      glue' hrange' hsymm' hcocycle' Φ i j x hx
  obtain ⟨p, rfl⟩ := surjective_presentationSection.{u}
    (specSchemeIota.{u} obj poly glue hrange hsymm hcocycle i) f
  obtain ⟨q, rfl⟩ := surjective_presentationSection.{u}
    (specSchemeIotaMap.{u} obj poly glue hrange hsymm hcocycle obj' poly' glue' hrange' hsymm'
      hcocycle' Φ j) g
  exact ⟨p, q, hfg, hxf⟩

/-- **The polynomial form of `ComplexAnalytic.exists_index_basicOpen_specSchemeIotaMap`**: at every
point of the first datum's scheme there are a member of each datum and polynomials in their own
variables cutting out the same open, which contains the point.

`ComplexAnalytic.exists_index_basicOpen_specSchemeIotaMap`'s two sections, lifted by
`ComplexAnalytic.surjective_presentationSection` at each of the two immersions; no index is handed
in, and none is chosen here either.

**This is the vocabulary a common refinement of two covers is stated in**, and it is as far as this
file goes towards one: the statement is an existential at each point, with no choice function, no
refined family and none of a cover datum's three laws. -/
theorem exists_index_mvPolynomial_basicOpen_specSchemeIotaMap
    (Φ : specScheme.{u} obj' poly' glue' hrange' hsymm' hcocycle' ⟶
      specScheme.{u} obj poly glue hrange hsymm hcocycle) [IsIso Φ]
    (x : specScheme.{u} obj poly glue hrange hsymm hcocycle) :
    ∃ (i : J) (j : K) (p : MvPolynomial (ULift.{u} (Fin (obj i).n)) ℂ)
      (q : MvPolynomial (ULift.{u} (Fin (obj' j).n)) ℂ),
      (specScheme.{u} obj poly glue hrange hsymm hcocycle).basicOpen
          (presentationSection.{u}
            (specSchemeIota.{u} obj poly glue hrange hsymm hcocycle i) p) =
        (specScheme.{u} obj poly glue hrange hsymm hcocycle).basicOpen
          (presentationSection.{u} (specSchemeIotaMap.{u} obj poly glue hrange hsymm hcocycle
            obj' poly' glue' hrange' hsymm' hcocycle' Φ j) q) ∧
      x ∈ (specScheme.{u} obj poly glue hrange hsymm hcocycle).basicOpen
        (presentationSection.{u}
          (specSchemeIota.{u} obj poly glue hrange hsymm hcocycle i) p) := by
  obtain ⟨i, j, f, g, hfg, hxf⟩ :=
    exists_index_basicOpen_specSchemeIotaMap.{u} obj poly glue hrange hsymm hcocycle obj' poly'
      glue' hrange' hsymm' hcocycle' Φ x
  obtain ⟨p, rfl⟩ := surjective_presentationSection.{u}
    (specSchemeIota.{u} obj poly glue hrange hsymm hcocycle i) f
  obtain ⟨q, rfl⟩ := surjective_presentationSection.{u}
    (specSchemeIotaMap.{u} obj poly glue hrange hsymm hcocycle obj' poly' glue' hrange' hsymm'
      hcocycle' Φ j) g
  exact ⟨i, j, p, q, hfg, hxf⟩

end

end ComplexAnalytic
