/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Analytification.SpecRefinedMember
import Oka.Analytification.SpecMemberSections

/-!
# The refined member's range, in the section vocabulary

`Oka/Analytification/SpecRefinedMember.lean` builds, for a polynomial `p` in the variables of a
presentation `P` and an open immersion `f` out of `Spec` of `P`'s algebra, an open immersion
`ComplexAnalytic.presentationRefinedIota` into `X`, and
`ComplexAnalytic.opensRange_presentationRefinedIota` says its range is the image under `f` of
`D(p)` — a statement about `Spec` of the presented algebra, transported into `X`. It states both
at a member `i` of a cover datum as well, as `ComplexAnalytic.refinedIota` and
`ComplexAnalytic.opensRange_refinedIota`, each the general form at
`ComplexAnalytic.specSchemeIota`.

`Oka/Analytification/SpecMemberSections.lean` reads the same polynomial the other way, as a
**section of `𝒪_X`** over the immersion's range: `ComplexAnalytic.presentationSection`, whose
`ComplexAnalytic.basicOpen_presentationSection` describes the open it cuts out by the same image,
and `ComplexAnalytic.specSchemeIotaSection` with
`ComplexAnalytic.basicOpen_specSchemeIotaSection` at a member.

**So the two files describe one open twice, and this file says so — at both levels.** The
right-hand sides of the two theorems are the same term, so the equation between the two
descriptions is `Eq.trans` and `Eq.symm` and nothing else — no rewrite under a dependent argument,
and in particular no `rw` at `AlgebraicGeometry.Scheme.Hom.opensRange`, whose `IsOpenImmersion`
argument makes a `rw` at the morphism fail with *"motive is not type correct"*. **The predicted
hazard does not arise there because the proof is a term** — and it *does* arise in
`ComplexAnalytic.opensRange_presentationRefinedIota_rename` below, in a second form the sentence
above does not cover: a `ComplexAnalytic.presentationSection` is indexed by the open being
rewritten, so a rewrite at that open is ill-typed even with the morphism left alone. That theorem's
docstring records the failing rewrite and the route around it.

## Why this is a file of its own rather than a line in either of them

`Oka/Analytification/SpecRefinedMember.lean` does not import
`Oka/Analytification/SpecMemberSections.lean` and **states in its own `## What is not here` that
this is a property of it worth having**: `ComplexAnalytic.opensRange_refinedIota` is *"a statement
about the open itself, and stays the usable one for a reader who has not imported that file."*
Appending this theorem there would make that clause false about its own file — the reader of it
would have imported that file — and would cost that module's transitive closure **three `Oka`
modules and one Mathlib root**: `Oka.Analytification.SpecMemberSections`,
`Oka.Analytification.SpecTwoData`, `Oka.AlgebraicGeometry.OpenImmersion` and
`Mathlib.AlgebraicGeometry.OpenImmersion`, taking it from 86 modules and 71 roots to 89 and 72 —
counted with the file itself in, as `scripts/import_cost.py`'s comment-stripping and `IMPORT`
regex read the tree. **This file's own closure is 90 and 72**, which is that same 89 plus this
file, so the reader who wants the bridge pays for both sides and the reader who wants only the
range does not. `lake build` does not grow either way, since both modules are already in
`Oka.lean`'s closure; what grows is what a reader importing one file in isolation pays.

Adding it to `Oka/Analytification/SpecMemberSections.lean` instead is the mirror problem: that
file would gain `Oka.Analytification.SpecRefinedMember`, and its subject is a section over a
member rather than a refinement of one.

**A third module that imports both and states the bridge costs one build job and grows no
existing closure**, which is the same trade `Oka/Analytification/SpecMemberChoice.lean` took for
the analogous one-theorem step, and for the same reason: appending would have falsified a
file-scoped `## What is not here` bullet that is informative about where a line is drawn.

## Two theorems, and why that is not the two spellings this file already declined

**These two are not two names for one statement.** The first is at an **arbitrary** open immersion
and the second is the first at `ComplexAnalytic.specSchemeIota`; they differ in how general the
immersion is, and the general one reaches immersions the specialised one cannot name — a member of
a *second* cover datum carried into the first datum's scheme is
`ComplexAnalytic.specSchemeIotaMap`, and is not `specSchemeIota` of anything in the first datum.
`Oka/Analytification/SpecRefinedMember.lean`'s own two-level section has the argument in full and
this file follows it rather than restating it.

**What this file still declines is the other thing**, which is a *re-spelling at one fixed
immersion*. `ComplexAnalytic.specSchemeIotaSection` is `ComplexAnalytic.presentationSection` at
`ComplexAnalytic.specSchemeIota`, by definition, so the member-level equation below could equally
be stated with `presentationSection` on its right-hand side; that statement differs from the one
below by unfolding a `def` and is one `rfl` away for a reader who wants it. **It is not stated**,
for the reason `ComplexAnalytic.specSchemeIotaSection` exists at all and gives in its own
docstring: a caller holding a cover datum and an index should not have to spell the six arguments
of the general form, and `Oka/Analytification/SpecMemberSections.lean` already argues against
stating both. **Generality in the immersion is content; a second name at one immersion is not.**

## The overlap of two refined members at one immersion, and the sentence it narrows

Two files on this line say, in two spellings, that what a cover **datum** additionally needs over
an affine open cover is `poly`, the three laws, and *the condition that every pairwise overlap be a
distinguished open of each of the two members it lies in* — and that **that** is what the points of
`X` cannot supply. `Oka/Analytification/SpecMemberChoice.lean` and
`Oka/Analytification/SpecRefinedCover.lean` are the two, and both sentences are now narrowed rather
than deleted, because their true half is what makes the remaining piece work.

**At two refined members of the *same* immersion the overlap is a refined member of that
immersion again, at the product of the two polynomials.** Both chosen sections are sections over
one open — the immersion's range — so `AlgebraicGeometry.Scheme.basicOpen_mul` applies on the nose
and the overlap is cut out by `p * q`, a polynomial in the **ambient** member's variables. The
other reading of the same fact puts the overlap inside the *refined* member rather than the ambient
one, and that is `AlgebraicGeometry.Scheme.basicOpen_res` with **no affineness hypothesis at all**.

**And the doubly-distinguished condition at such a pair holds, in both vocabularies and at both
members.** The condition quantifies over the two members the overlap lies in — here `D(p)` and
`D(q)` — and asks for a polynomial in *each* of their own variables.
`ComplexAnalytic.presentationRefinedPres` gives `D(p)` a presentation with one variable more than
`P`'s, so `p * q` is not a polynomial on `D(p)` at all and does not typecheck there; the map that
carries `q` across is the one `ComplexAnalytic.localisationIncl` names, and
`ComplexAnalytic.opensRange_presentationRefinedIota_rename` says the refined member of `D(p)` it
names **is** the overlap. In the vocabulary of *sections* the same is
`ComplexAnalytic.basicOpen_res_presentationSection` at `D(p)` and
`ComplexAnalytic.basicOpen_res_presentationSection'` at `D(q)`. **So the same-member half of the
condition is supplied and not described**, which is what this file's `## What is not here` said of
it before those two theorems, and it is still not a `poly`: a `poly` is a function of two *indices*
satisfying three laws.

**At two refined members of different immersions nothing here applies and none of it is claimed.**
The two sections live over different opens, so `AlgebraicGeometry.Scheme.basicOpen_mul` does not
typecheck and `AlgebraicGeometry.Scheme.basicOpen_res` has no containment to restrict along. What
is available there is `AlgebraicGeometry.exists_basicOpen_le_affine_inter`'s **pointwise**
statement — at each point of the intersection there is *some* doubly-distinguished open containing
it — which `Oka/Analytification/SpecRefinedChoice.lean` already spends and which does not say the
overlap *itself* is distinguished. That is the half those two sentences are right about.

**The same split is on record one level down**, and a reader estimating from the theorems below
should have it: for a one-datum refinement of an analytic cover, the same-member overlaps are
`Oka/Analytification/LocalisationComposite.lean`'s `D(f₁) ∩ D(f) = D(f₁·f)` at the presentation
level, and the cross-member ones need the original transition transported through two
localisations. **The two halves are not the same size, and it is the first that this file is
about** — supplied here, where the second is short of a `poly` entry by an amount nobody has
measured.

## Main results

- `ComplexAnalytic.opensRange_presentationRefinedIota_eq_basicOpen`: **the range of the refined
  immersion is the basic open of the section attached to the same polynomial** — one open, named
  on the left in the vocabulary of the file that builds the immersion and on the right in the
  vocabulary of the file that reads the same polynomial as a section.
- `ComplexAnalytic.opensRange_refinedIota_eq_basicOpen`: **the same at a member of a cover
  datum**, which is the previous theorem at that member's own inclusion and nothing else.
- `ComplexAnalytic.presentationSection_mul`: **the section a product of polynomials names is the
  product of the sections they name**, which is the algebra step of the next theorem stated apart
  from its geometry.
- `ComplexAnalytic.opensRange_presentationRefinedIota_inf`: **the overlap of two refined members at
  one immersion is a refined member at that immersion**, at the product of the two polynomials —
  a statement about the member the two sit inside, and not about either of the two members the
  overlap lies in, for the reason the section above gives.
- `ComplexAnalytic.basicOpen_res_presentationSection`: **and that overlap is a distinguished open
  of the first refined member itself**, cut out by the second section restricted to it — which is
  the doubly-distinguished condition at that one of the two members, in the vocabulary of sections
  and not of polynomials.
- `ComplexAnalytic.basicOpen_res_presentationSection'`: **and of the second**, which is the
  previous theorem at the exchanged pair with the overlap written in the same order. Stated rather
  than left to a caller because the condition quantifies over *both* members.
- `ComplexAnalytic.opensRange_presentationRefinedIota_rename`: **and the same in the vocabulary of
  polynomials**, which is the vocabulary a cover datum's overlap data is written in: the overlap is
  the refined member of the first at the second's polynomial renamed into the first's own
  variables. **This is the same-member half of the doubly-distinguished condition and not a
  description of it**, and the same statement at the exchanged pair is the condition at the second
  member. The renaming map is named in its docstring rather than here, for the reason the paragraph
  above this heading gives.

## What is not here

* **No affineness theorem in the section vocabulary**, at either level, and in particular nothing
  restating `ComplexAnalytic.isAffineOpen_presentationRefinedIota` or
  `ComplexAnalytic.isAffineOpen_refinedIota` as *the basic open of that section is an affine open
  of `X`*. It does follow, in one `Eq.mpr` on
  `ComplexAnalytic.opensRange_presentationRefinedIota_eq_basicOpen`, and it is left out on purpose:
  nothing asks for it, and a caller that wants it rewrites with that theorem in the direction
  it needs rather than reading a third name off this file.
* **No `poly`, no `glue`, and none of a cover datum's three laws**, so nothing here is or produces
  a common refinement — that is `Oka/Analytification/CrossMemberDatum.lean`,
  `Oka/Analytification/CrossMemberDatumGlue.lean` and the `Oka/Analytification/RefineDatum*.lean`
  files. **Nothing here is a cover datum and nothing here claims to refine one**: the overlap
  theorems here are at **one** immersion and **two** polynomials, and a `poly` is a function of
  two *indices* satisfying three laws. **The gap between them is not arithmetic, and only one part
  of it has narrowed.** A `poly` entry at a pair of refined members is a polynomial in each of
  *their* variables; `ComplexAnalytic.opensRange_presentationRefinedIota_inf` names one in the
  ambient member's and `ComplexAnalytic.opensRange_presentationRefinedIota_rename` names one in
  each of theirs, so **the entry is named at a same-member pair and is not named at a pair whose
  two members are different — and the indices and the three laws are missing at every pair**.
  **This bullet said two things were missing there — the rename `ComplexAnalytic.localisationIncl`
  names and the companion of `ComplexAnalytic.basicOpen_res_presentationSection` at the second
  member — and both are now stated**, the second as
  `ComplexAnalytic.basicOpen_res_presentationSection'`. At a pair whose two members are different
  none of the overlap theorems applies at all, and **that** is the half nobody has sized.
* **Nothing about overlaps of three or more.** Every overlap theorem here —
  `ComplexAnalytic.opensRange_presentationRefinedIota_inf`,
  `ComplexAnalytic.basicOpen_res_presentationSection`, its primed companion and
  `ComplexAnalytic.opensRange_presentationRefinedIota_rename` — is stated at **two** polynomials;
  the triple overlaps a `hcocycle` quantifies over are not here, and iterating one of them is not
  the same as stating the law.
* **Nothing indexed by the points of `X`.**
  `ComplexAnalytic.exists_family_mvPolynomial_basicOpen_specSchemeIotaMap`
  (`Oka/Analytification/SpecMemberChoice.lean`) is a family and it is indexed by points, which is
  not a cover datum's index type; the theorems below take polynomials and not points, and none of
  them is a refinement of that family.
* **No second cover datum.** `ComplexAnalytic.specSchemeIotaMap` and
  `Oka/Analytification/SpecTwoData.lean`'s two-datum vocabulary do not appear, even though the
  import above makes them reachable. **What the general theorem changes is that such a morphism is
  now a legal argument, which is not the same as appearing**: no *statement* below mentions a
  second datum, quantifies over one, or says anything about two.
* **Nothing analytic.** No analytification, no `X^an`, no comparison morphism.
* **Nothing about `p` being non-zero, or the open being non-empty.** At `p = 0` both sides are the
  empty open and both theorems stay true.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry

universe u

namespace ComplexAnalytic

noncomputable section

section

variable {X : Scheme.{u}} {P : Presentation.{u}} (f : Spec (CommRingCat.of P.alg) ⟶ X)
  [IsOpenImmersion f]

/-- **The range of the refined immersion is the basic open of the section the same polynomial
names.**

`ComplexAnalytic.opensRange_presentationRefinedIota` describes that range as `f ''ᵁ D(p)`, and
`ComplexAnalytic.basicOpen_presentationSection` describes `X.basicOpen (presentationSection f p)`
by the same expression. **The two right-hand sides are literally the same term**, so this is
`Eq.trans` of the first with the symmetric form of the second and there is nothing else in it.

**Stated as a term rather than by rewriting, and that is not only a style choice.**
`AlgebraicGeometry.Scheme.Hom.opensRange` takes an `AlgebraicGeometry.IsOpenImmersion` argument,
so a `rw` at the morphism under it fails with *"motive is not type correct"* and needs a
`simp only`; composing the two equations sidesteps the question, since neither side is ever
rewritten under that argument.

**What it buys is that a caller who has chosen `p` to cut out a particular open of `X` can name
the affine open `ComplexAnalytic.isAffineOpen_presentationRefinedIota` gives it in the vocabulary
the choice was made in**, without transporting anything: the section is a section of `𝒪_X`, and
the open is one of its basic opens. **The immersion being arbitrary is what makes that available
on both sides of a two-datum choice**, where one member is a `ComplexAnalytic.specSchemeIota` and
the other is not. -/
theorem opensRange_presentationRefinedIota_eq_basicOpen
    (p : MvPolynomial (ULift.{u} (Fin P.n)) ℂ) :
    (presentationRefinedIota.{u} f p).opensRange = X.basicOpen (presentationSection.{u} f p) :=
  (opensRange_presentationRefinedIota.{u} f p).trans
    (basicOpen_presentationSection.{u} f p).symm

/-! #### And the overlap of two of them, at one immersion -/

/-- **The section a product of polynomials names is the product of the sections they name.**

`ComplexAnalytic.presentationSection` is `AlgebraicGeometry.IsOpenImmersion.specΓIsoTop` applied to
`Ideal.Quotient.mk` of the polynomial, and both are ring homomorphisms, so this is `map_mul` twice
and nothing else.

**Stated because the next theorem is about the *open* and this is about the *section*.** A reader
checking that the overlap below is cut out by the product wants to see the algebra step separately
from the geometric one; folding them into one proof would leave the geometric step's content —
`AlgebraicGeometry.Scheme.basicOpen_mul` — sharing a line with a rewrite that has nothing to do
with it. -/
theorem presentationSection_mul (p q : MvPolynomial (ULift.{u} (Fin P.n)) ℂ) :
    presentationSection.{u} f (p * q) =
      presentationSection.{u} f p * presentationSection.{u} f q :=
  (congrArg (IsOpenImmersion.specΓIsoTop f).hom
      (map_mul (Ideal.Quotient.mk (presentationIdeal.{u} P.g)) p q)).trans (map_mul _ _ _)

/-- **The overlap of two refined members at one immersion is a refined member at that immersion**,
at the product of the two polynomials.

`AlgebraicGeometry.Scheme.basicOpen_mul` read through
`ComplexAnalytic.opensRange_presentationRefinedIota_eq_basicOpen` at all three polynomials, with
`ComplexAnalytic.presentationSection_mul` closing the algebra step. The two sections are sections
over **the same** open — the immersion's range — which is the whole hypothesis and the whole
limitation.

**What this settles and what it does not.** A cover datum requires every pairwise overlap of
members to be a distinguished open of *each* of the two members it lies in, cut out by a polynomial
in that member's own variables. The two members here are `D(p)` and `D(q)`, and `p * q` is a
polynomial in **`f`'s** variables and not in theirs: `ComplexAnalytic.presentationRefinedPres`
gives `D(p)` a presentation with one variable more, so `p * q` does not typecheck as a polynomial
on it. **So this is the condition's shape at the member the two sit inside, and not the condition
at either of the two members it quantifies over** — for those two see
`ComplexAnalytic.opensRange_presentationRefinedIota_rename` below, which is this overlap named as a
refined member of `D(p)` at a polynomial in `D(p)`'s own variables and, at the exchanged pair, of
`D(q)`. `Oka/Analytification/SpecMemberChoice.lean` and
`Oka/Analytification/SpecRefinedCover.lean` say that condition is what the points of `X` cannot
supply; their sentences are now narrowed to the pairs whose two members are different, and this
theorem is why there are two halves. **This theorem is still the ambient member's statement and is
not superseded by the one below**: `p * q` is the polynomial a caller who is cutting `f`'s own
member down again wants, and it is what that proof lands on.

**Nothing here is a `poly`.** A cover datum's `poly` is a function of *two indices* satisfying
three laws, and this is one equation at one immersion and two polynomials; see this file's
`## What is not here`. -/
theorem opensRange_presentationRefinedIota_inf (p q : MvPolynomial (ULift.{u} (Fin P.n)) ℂ) :
    (presentationRefinedIota.{u} f p).opensRange ⊓ (presentationRefinedIota.{u} f q).opensRange =
      (presentationRefinedIota.{u} f (p * q)).opensRange := by
  rw [opensRange_presentationRefinedIota_eq_basicOpen,
    opensRange_presentationRefinedIota_eq_basicOpen,
    opensRange_presentationRefinedIota_eq_basicOpen, presentationSection_mul,
    Scheme.basicOpen_mul]

/-- **And that overlap is a distinguished open of the first refined member itself**, cut out by the
second section restricted to it.

`AlgebraicGeometry.Scheme.basicOpen_res` at the inclusion `AlgebraicGeometry.Scheme.basicOpen_le`
gives, and **it has no affineness hypothesis at all**: the statement is about a scheme's basic
opens and nothing about presentations, cover data or affine members enters it.

**Why both this and the theorem above.** That one says the overlap is distinguished in the
*ambient* member, in the vocabulary of polynomials, which is the vocabulary a cover datum's `poly`
is written in; this one says it is distinguished in `D(p)`, which is one of the two members the
overlap actually lies in, in the vocabulary of sections, and that is the form a caller holding one
refined member and wanting to cut it down again needs. **The two are about different members**, so
neither implies the other and neither implies the other's spelling. The companion at `D(q)` is this
theorem with `p` and `q` exchanged and is `ComplexAnalytic.basicOpen_res_presentationSection'`
below; the polynomial vocabulary the condition is written in is
`ComplexAnalytic.opensRange_presentationRefinedIota_rename`, which reaches both members from one
statement. -/
theorem basicOpen_res_presentationSection (p q : MvPolynomial (ULift.{u} (Fin P.n)) ℂ) :
    X.basicOpen (X.presheaf.map (homOfLE (X.basicOpen_le (presentationSection.{u} f p))).op
        (presentationSection.{u} f q)) =
      X.basicOpen (presentationSection.{u} f p) ⊓ X.basicOpen (presentationSection.{u} f q) :=
  Scheme.basicOpen_res _ _ _

/-- **And a distinguished open of the second refined member**, cut out by the first section
restricted to it — the theorem above at the other of the two members the overlap lies in.

**A prime, and the reason is that no token distinguishes the two.** Both statements are
`AlgebraicGeometry.Scheme.basicOpen` of a restricted `ComplexAnalytic.presentationSection`, so
their left-hand sides have the same *shape* and differ only in which of `p` and `q` is restricted
along; a descriptive suffix
would have to name an argument position rather than a subject. **The prime is not a new convention
here**: `Oka/` already carries primed declaration names — `ComplexAnalytic.coverGlueData'` and
`ComplexAnalytic.stalkMap_restrictHom_eq'` among them. **No figure is
quoted for that because the reading decides it**: declaration sites whose name *contains* a prime,
sites whose name *ends* in one, and rows of the environment dump are three different counts over
one tree, and a sentence quoting one of them beside another rots the moment a reader checks the
other. **The alternative — restating both as one theorem taking
the member as an argument — was rejected**: it renames a declaration that is advertised in the
`## Main results` above, and is cited at eight sites in two files, and it buys nothing a
caller can use.

**It is the theorem above at `q` and `p` composed with `inf_comm`, and that is the whole of it.**
`AlgebraicGeometry.Scheme.basicOpen_res` at the exchanged pair gives the right-hand side in the
order `D(q) ⊓ D(p)`, and this states it in the order the theorem above uses, which is the order a
caller matching against one fixed overlap has. **Bare `inf_comm` does not typecheck here** — it
needs both arguments explicitly, an application type mismatch otherwise.

**Why it is stated rather than left to the caller.** The doubly-distinguished condition quantifies
over *both* members an overlap lies in, so a file that supplies it at one of them and leaves the
other to an `Eq.trans` is describing the condition and not meeting it — which is what this file's
`## What is not here` said of itself before this theorem existed. -/
theorem basicOpen_res_presentationSection' (p q : MvPolynomial (ULift.{u} (Fin P.n)) ℂ) :
    X.basicOpen (X.presheaf.map (homOfLE (X.basicOpen_le (presentationSection.{u} f q))).op
        (presentationSection.{u} f p)) =
      X.basicOpen (presentationSection.{u} f p) ⊓ X.basicOpen (presentationSection.{u} f q) :=
  (Scheme.basicOpen_res _ _ _).trans (inf_comm _ _)

/-- **The overlap of two refined members at one immersion is a refined member of each of them**,
cut out by the other's polynomial renamed into its variables — the doubly-distinguished condition
at a same-member pair, in the vocabulary of polynomials.

`ComplexAnalytic.presentationRefinedPres` gives `D(p)` one variable more than `P` has, and
`ComplexAnalytic.localisationIncl` is the map that adjoins it, so
`MvPolynomial.rename (localisationIncl P.n) q` is `q` read as a polynomial **on `D(p)`**. This says
the refined member it names inside `D(p)` is exactly the overlap.

**Both members, from one statement.** `p` and `q` are both universally quantified, so this theorem
at the exchanged pair is the condition at `D(q)`; its right-hand side comes out as `D(q) ⊓ D(p)`,
which is one `inf_comm` from this one. That companion is **not** stated, and the asymmetry with
`ComplexAnalytic.basicOpen_res_presentationSection'` above is a choice and not a principle: that
one was named as missing by this file's `## What is not here` and this one was not. A reader who
wants it writes `(opensRange_presentationRefinedIota_rename f q p).trans (inf_comm _ _)`.

**The proof does not go through the two section theorems above, and that is measured rather than
assumed.** Rewriting with `ComplexAnalytic.opensRange_presentationRefinedIota_eq_basicOpen` and
then backwards with `ComplexAnalytic.basicOpen_res_presentationSection` fails with *"motive is not
type correct"*: `ComplexAnalytic.presentationSection` of the renamed polynomial has type
`Γ(X, (presentationRefinedIota f p).opensRange)`, and that is the very open the rewrite is at.
**This is the hazard this file's header names and says does not arise in its own proofs** — it does
arise here, because the term being rewritten is indexed by the open. The route that works goes down
to `Spec` and never mentions a section:
`ComplexAnalytic.image_basicOpen_rename_Spec_map_localisationRingHom`
(`Oka/Analytification/SpecDistinguishedOpen.lean`) is the whole geometric content, and
`AlgebraicGeometry.Scheme.Hom.comp_image` carries it up along `f`.

**The right-hand side is then the product**, by
`ComplexAnalytic.opensRange_presentationRefinedIota_inf` above — so this theorem and that one are
the same overlap named at three different members, and it is the earlier one that supplies the
`p * q` the proof lands on.

**Still not a `poly`.** A cover datum's `poly` is a function of two *indices* satisfying three
laws; this is one equation at one immersion and two polynomials, and every pair it reaches has both
members refining the same one. See this file's `## What is not here` for the half that does not. -/
theorem opensRange_presentationRefinedIota_rename (p q : MvPolynomial (ULift.{u} (Fin P.n)) ℂ) :
    (presentationRefinedIota.{u} (presentationRefinedIota.{u} f p)
        (MvPolynomial.rename (localisationIncl.{u} P.n) q)).opensRange =
      (presentationRefinedIota.{u} f p).opensRange ⊓
        (presentationRefinedIota.{u} f q).opensRange := by
  haveI := isOpenImmersion_Spec_map_localisationRingHom.{u} P.g p
  rw [opensRange_presentationRefinedIota_inf, opensRange_presentationRefinedIota,
    opensRange_presentationRefinedIota]
  have hc : presentationRefinedIota.{u} f p ''ᵁ
      PrimeSpectrum.basicOpen (Ideal.Quotient.mk
        (presentationIdeal.{u} (localisationPresentation.{u} P.g p))
        (MvPolynomial.rename (localisationIncl.{u} P.n) q)) =
      f ''ᵁ (Spec.map (CommRingCat.ofHom (localisationRingHom.{u} P.g p)) ''ᵁ
        PrimeSpectrum.basicOpen (Ideal.Quotient.mk
          (presentationIdeal.{u} (localisationPresentation.{u} P.g p))
          (MvPolynomial.rename (localisationIncl.{u} P.n) q))) :=
    Scheme.Hom.comp_image _ _ _
  rw [hc, image_basicOpen_rename_Spec_map_localisationRingHom, map_mul,
    PrimeSpectrum.basicOpen_mul]

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

/-- **The range of the refined member's inclusion is the basic open of the section the same
polynomial names.**

`ComplexAnalytic.opensRange_presentationRefinedIota_eq_basicOpen` at
`ComplexAnalytic.specSchemeIota`. What the specialisation adds is the index: the general form
names the open by a morphism the reader has to supply, and here both sides are named by a member
of this cover datum — `ComplexAnalytic.specSchemeIotaSection` on the right, which is
`ComplexAnalytic.presentationSection` at the same immersion by definition, so the term closes the
difference definitionally and nothing is rewritten.

**What it buys is that a caller who has chosen `p` to cut out a particular open of `X` — which is
what `ComplexAnalytic.exists_mvPolynomial_basicOpen_specSchemeIota_inter` produces — can name the
affine open `ComplexAnalytic.isAffineOpen_refinedIota` gives it in the vocabulary the choice was
made in**, without transporting anything: the section is a section of `𝒪_X`, and the open is one
of its basic opens. -/
theorem opensRange_refinedIota_eq_basicOpen (i : J)
    (p : MvPolynomial (ULift.{u} (Fin (obj i).n)) ℂ) :
    (refinedIota.{u} obj poly glue hrange hsymm hcocycle i p).opensRange =
      (specScheme.{u} obj poly glue hrange hsymm hcocycle).basicOpen
        (specSchemeIotaSection.{u} obj poly glue hrange hsymm hcocycle i p) :=
  opensRange_presentationRefinedIota_eq_basicOpen.{u}
    (specSchemeIota.{u} obj poly glue hrange hsymm hcocycle i) p

end

end ComplexAnalytic
