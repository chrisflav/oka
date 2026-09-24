/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Analytification.CrossMemberDatumGlue

/-!
# The caller's choice in a cross-member `glue` is one unit, and it exists algebraically

`Oka/Analytification/CrossMemberDatumGlue.lean` builds the `glue` field of a refined cover datum
whose members may lie over different members of the original cover, and hands the choice it needs
to the caller. **Until this file landed its `## What is not here` said** — the sentence is quoted
here because this file is what retired it, and it no longer stands there in this form:

> **Nothing produces `r` or `u`, and so nothing produces a `glue` field that takes no arguments.**
> The field below is a function of the caller's choice at every ordered pair; the existentials
> that would supply one are `ComplexAnalytic.exists_localisationOpen_eq_rename` with
> `ComplexAnalytic.exists_mk_rename_eq` for the algebra and
> `ComplexAnalytic.exists_comap_analytificationMap_eq_comap_localisationProj` for the geometry, and
> none of them is instantiated here.

**That reads as three existentials to instantiate. It is one, and this file spends it.**

**What that buys is that the field can be applied, and not that the result is the refinement.**
The two obligations are equations between elements of the overlap algebras, and the choice
produced below satisfies them; **no statement here says the refined overlap that choice induces
is the geometric one**, and the two existentials this file does *not* use are where that would
be paid for. The `## What is not here` section says so again at the end, because it is the
sentence most easily lost between the title and the results.

## Two obligations, one of which is not a choice

At an ordered pair `(a, b)` the field asks for a polynomial `r` and a unit `u` subject to
`ComplexAnalytic.RefineDatumCrossEq` and `ComplexAnalytic.RefineDatumCrossUnit`. The first says
that a *determined* element of the overlap algebra — the class of `q a b * fam a`, carried across
by the datum's own glue — is the class of `r`, and `r` occurs nowhere else in it. Since
`Ideal.Quotient.mk` is surjective that is satisfiable for every `q` and settles nothing:
`ComplexAnalytic.exists_refineDatumCrossEq` is the whole proof. **So `r` is not a choice, it is a
preimage of something already fixed**, and since both obligations see it only through its class it
can be eliminated outright. That is `ComplexAnalytic.refineDatumCross_exists_iff`, and what is
left after it is a single statement: **are the class of `q b a * fam b` and the glue-image of the
class of `q a b * fam a` associates in the overlap algebra on the `σ b` side?**

**Knowing that is what says which existential to reach for**, and the answer is not the obvious
one. Two of the three quoted above produce an equality of *opens*, and an equality of opens does
not give an associate — `ComplexAnalytic.exists_mk_rename_eq`'s own docstring says that
implication is a Nullstellensatz statement nothing in this repository proves. So a construction
that starts from "the two sides cut out the same open" starts on the wrong side of a gap that is
already recorded. The third keeps the unit, and it is the one used below.

## The choice, and why it is symmetric enough to serve both orders of a pair

`ComplexAnalytic.RefineDatumCrossFactor` is the rule: the class of `q a b` on the `σ a` side is a
unit multiple of the class of `fam b` carried back from the `σ b` side. **It names one entry of
the family and no other**, so the whole family can be chosen entry by entry —
`ComplexAnalytic.exists_refineDatumCrossFactor`, which is one application of
`ComplexAnalytic.exists_mk_rename_eq` to a preimage.

The associate then falls out of arithmetic. Writing `Φ` for the datum's algebra isomorphism from
the `σ a` side to the `σ b` side and `α`, `β` for the classes of `fam a` and `fam b`, the rule at
`(b, a)` gives `q b a ↦ u₂ · Φ α` and the rule at `(a, b)` gives `q a b ↦ u₁ · Φ⁻¹ β`, so the two
products are `u₂ · Φ α · β` and `Φ u₁ · β · Φ α` — **the same three factors in two orders**, and
they differ by the unit `u₂ · (Φ u₁)⁻¹`.

**The input's `hsymm` is used exactly once and it is what makes this work.** The rule at `(b, a)`
is stated with the algebra isomorphism of the swapped pair, and turning that into `Φ⁻¹` is
`ComplexAnalytic.refineDatumCrossAlgEquiv_symm`, which is the datum's `glue j i = (glue i j).symm`
and nothing else. Without it the two orders of a pair carry two unrelated isomorphisms and there
is nothing to relate the two products by.

## What the existence needs, and it is less than one might expect

Nothing about `σ`, nothing about the two members being distinct, and no condition on the cover
beyond the `hsymm` every consumer of a cover datum here already carries. In particular **no
polynomial is required to cut anything out**: every statement below is an identity between
elements of an overlap algebra, and the geometry never enters. That is why the file is short,
and it is also the reason to be careful about what it does *not* claim — see below.

**What the rule below means geometrically is not stated here and is stated**:
`Oka/Analytification/RefineDatumRefinesCross.lean` reads `ComplexAnalytic.RefineDatumCrossFactor`
as an equality of non-vanishing loci and proves that a refined datum built at a family obeying it
refines the space it refines. Nothing below is changed by that, and the division is the point —
the condition is chosen and checked in an algebra, and what it buys is geometric.

## Main definitions

- `ComplexAnalytic.coverOverlapClass`: **the class of a member's polynomial in an overlap
  algebra**, which is what both obligations are equations between.
- `ComplexAnalytic.RefineDatumCrossFactor`: **the rule the caller's extra factor follows** at one
  ordered pair, and the only condition the construction imposes on it.

## Main results

- `ComplexAnalytic.coverOverlapClass_mul`: the class is multiplicative.
- `ComplexAnalytic.refineDatumCrossAlgEquiv_symm`: **swapping the pair inverts the algebra
  isomorphism a cross-member glue reads**, given the input datum's symmetry law. The one place
  that hypothesis is used.
- `ComplexAnalytic.exists_refineDatumCrossEq`: **the first obligation is satisfiable at every
  ordered pair and for every extra factor**, by surjectivity of the quotient map alone.
- `ComplexAnalytic.refineDatumCross_exists_iff`: **the two obligations together are exactly an
  associate statement**, with the polynomial eliminated.
- `ComplexAnalytic.exists_refineDatumCrossFactor`: **an extra factor obeying the rule exists** at
  every ordered pair.
- `ComplexAnalytic.exists_refineDatumCrossUnit_of_factor`: **the rule at both orders of a pair
  gives the associate at that pair.**
- `ComplexAnalytic.exists_refineDatumCross`: **the three families and the two laws, all at once** —
  the choice a cross-member `glue` field asks of its caller exists. **Algebraically**: it says the
  two obligations are satisfiable and nothing about what the resulting overlap cuts out.

## What is not here

* **No `glue` field taking no arguments, and no refined cover datum.** This file produces a choice;
  applying `ComplexAnalytic.refineDatumGlue` to it and reading the result back is a separate
  step, and the two coherence triangles that step would consume are stated in the facing file
  against a *given* choice rather than against this one.
* **No `hsymm` for the refined datum, and nothing here was in its way.** The construction is
  symmetric in shape — the rule at `(b, a)` is the rule at `(a, b)` with the members exchanged —
  but that is not a proof that the resulting `glue` satisfies a symmetry law, and no such proof is
  attempted here. **The asymmetry that was expected is absent.** The route guessed in advance was
  to *define* `q b a` out of `q a b`, which picks an order on the pair and builds an asymmetry in;
  this file does not, each entry obeys the same rule on its own, and what relates the two orders
  is the input datum's own `hsymm`.

  **This bullet then named the choosing as the remaining obstacle, and it was not one.** It read:
  *"What is in the way instead is the choosing. `ComplexAnalytic.exists_refineDatumCross` runs
  `choose` over ordered pairs, so the entry at `(a, b)` and the entry at `(b, a)` are two
  unrelated runs of `ComplexAnalytic.exists_mk_rename_eq`. … A refined `hsymm` would need one
  choice per unordered pair, read at both orders; whether both obligations can be met by one such
  choice is unmeasured here in both directions."* **A refined `hsymm` needs no such thing.**
  `Oka/Analytification/RefineDatumSymm.lean` proves the law for two arbitrary independent choices,
  by making the coherence triangle of the cross-member glue determine it; the question of one
  choice per unordered pair is not answered there and does not have to be. The two runs of the
  existence being unrelated is still true and is still what the bullet below says.
* **No `hrange` and no `hcocycle`**, in either branch. They are geometric where everything here is
  algebraic, and nothing below is evidence about them.
* **No canonical choice, and after `Oka/Analytification/RefineDatumSymm.lean` that matters less
  than this bullet used to say.** Three `choose`s: a different run of
  `ComplexAnalytic.exists_mk_rename_eq` gives a different extra factor, and nothing here says two
  choices are related — **all of which stands**. What no longer follows is the sentence this
  bullet ended with, *"a consumer that needs the same choice twice has to carry it rather than
  re-derive it"*: `ComplexAnalytic.refineDatumGlueNe_congr` says the glue a choice produces is the
  same for every choice, so a consumer that needs the same *glue* twice may re-derive it. One that
  needs the same `q` — a polynomial and not an isomorphism — still has to carry it.
* **No geometric reading of the extra factor.** `Oka/Analytification/CrossMemberDatum.lean`'s
  chain says the refined overlap is cut out by the original overlap's polynomial times an extra
  one; the factor produced here obeys an algebraic rule and **nothing below says it is that
  polynomial**, or that the resulting refined overlap is the geometric one. That identification is
  where the two existentials this file does not use would be spent, and it is not made.
* **No witness at a non-constant `σ` *here*, and the one that exists does not come from this
  file.** This bullet said only *"no witness at a non-constant `σ`"*;
  `Oka/Analytification/RefineDatumWitness.lean` has one, and it is built by exhibiting `r` and
  `u` rather than by calling `ComplexAnalytic.exists_refineDatumCross` — which it cannot, since
  that lemma produces `q` in its conclusion and a witness names its own. **Whether the choice
  this file produces meets the two conditions a refined datum adopts is still untouched in both
  directions.** Nothing about `AlgebraicGeometry.Scheme` or `admissible` either, as in the files
  this one sits beside.
-/

open CategoryTheory MvPolynomial

universe u

namespace ComplexAnalytic

noncomputable section

variable {J B : Type u} (obj : J → Presentation.{u})
  (poly : ∀ i : J, J → MvPolynomial (ULift.{u} (Fin (obj i).n)) ℂ)

/-! ### The class of a member's polynomial in an overlap algebra -/

/-- **The class of a polynomial of the member `i`, in the algebra of the overlap of `i` and `j`.**

Every statement in this file is an equation between elements of one such algebra, and each side of
it is a polynomial of a member pushed forward twice — renamed into the localised polynomial ring
and then taken modulo the ideal. Spelled once here rather than inline because the two spellings
that occur differ only in which member the polynomial came from, and because `Ideal.Quotient.mk`
applied to a `MvPolynomial.rename` is four lines of arguments every time it is written out.

An `abbrev`, so that `map_mul` and `map_one` still fire through it and the two obligations of
`Oka/Analytification/CrossMemberDatumGlue.lean` — which are stated in the unfolded spelling — are
literally these. -/
abbrev coverOverlapClass (i j : J) (x : MvPolynomial (ULift.{u} (Fin (obj i).n)) ℂ) :
    PresentedAlgebra.{u} ((obj i).n + 1) ((obj i).k + 1)
      (localisationPresentation.{u} (obj i).g (poly i j)) :=
  Ideal.Quotient.mk (presentationIdeal.{u} (localisationPresentation.{u} (obj i).g (poly i j)))
    (rename (localisationIncl.{u} (obj i).n) x)

/-- **It is multiplicative**, which is the only property of it this file uses, and it is two
`map_mul`s because both stages are ring maps. Stated rather than inlined because the goals below
are large and `simp` on them is what plants an equation lemma for someone else's definition. -/
theorem coverOverlapClass_mul (i j : J) (x y : MvPolynomial (ULift.{u} (Fin (obj i).n)) ℂ) :
    coverOverlapClass.{u} obj poly i j (x * y) =
      coverOverlapClass.{u} obj poly i j x * coverOverlapClass.{u} obj poly i j y := by
  change Ideal.Quotient.mk _ (rename _ (x * y)) = _
  rw [map_mul, map_mul]

variable (glue : ∀ i j : J, coverOverlap.{u} obj poly i j ≅ coverOverlap.{u} obj poly j i)

/-! ### The datum's algebra isomorphism at the swapped pair -/

/-- **Swapping the pair inverts the algebra isomorphism the cross-member glue reads**, as soon as
the original datum's glue is symmetric.

This is the one place the input's `hsymm` is used, and it is what makes the choice below symmetric
enough to serve both orders of a pair. Without it the two orders carry two unrelated algebra
isomorphisms and the construction has nothing to relate them by.

Proved by opening the definition with `change` rather than with `rw`: rewriting with a definition
from another module plants that module's equation lemma into this one, which is the discipline
`Oka/Analytification/CrossMemberDatumGlue.lean` records at length. After the rewrite both sides
are `CategoryTheory.Iso.symm` applied twice and the remaining step is `rfl`.

**`change` and not `show`**, here and at the multiplicativity above: a goal-changing `show` is
flagged by `linter.style.show`, which `lake build --wfail` turns into a build failure — the
warning `Oka/Analytification/AffineSpace.lean` already records against the same idiom, and it does
not fire under `lake env lean`. -/
theorem refineDatumCrossAlgEquiv_symm (hsymm : ∀ i j : J, glue j i = (glue i j).symm) (i j : J) :
    refineDatumCrossAlgEquiv.{u} obj poly glue j i =
      (refineDatumCrossAlgEquiv.{u} obj poly glue i j).symm := by
  change (Presentation.algEquivOfIso.{u} (glue j i)).symm = _
  rw [hsymm]
  rfl

variable (σ : B → J) (fam : ∀ b : B, MvPolynomial (ULift.{u} (Fin (obj (σ b)).n)) ℂ)
  (q : ∀ a : B, B → MvPolynomial (ULift.{u} (Fin (obj (σ a)).n)) ℂ)

/-! ### The first obligation is free, and the second is an associate question -/

/-- **The first of the two obligations is satisfiable at every ordered pair, for every `q`.**

`ComplexAnalytic.RefineDatumCrossEq` says that a determined element of the overlap algebra is the
class of `r`, and `r` occurs nowhere else in it, so `Ideal.Quotient.mk` being surjective settles
it. Nothing about the cover, the glue or the choice of `q` is used.

**This retires half of a sentence one file carried until this one landed**, and that file is
`Oka/Analytification/CrossMemberDatumGlue.lean`. *"Nothing produces `r` or `u`"* was true of `u`
and not of `r`: what a caller has to produce is a preimage of something already determined. The
rest of it goes with `ComplexAnalytic.exists_refineDatumCross` below, and both facing bullets are
rewritten in the same push.

**This paragraph said *"two files carried"* until somebody ran the grep.** At the commit this file
was cut from, `git grep -c` for that sentence returns one file and it is the one named above —
which is what the quotation block at the top of this module docstring and the docstring of
`ComplexAnalytic.exists_refineDatumCross` below had both said all along, each naming that file and
no second one. A count is a claim like any other and this one was outvoted twice inside its own
file. -/
theorem exists_refineDatumCrossEq (a b : B) :
    ∃ r : MvPolynomial (ULift.{u} (Fin ((obj (σ b)).n + 1))) ℂ,
      RefineDatumCrossEq.{u} obj σ fam poly q glue a b r :=
  (Ideal.Quotient.mk_surjective _).imp fun _ h ↦ h.symm

/-- **The caller's choice exists at an ordered pair exactly when two classes are associates.**

The left-hand side is the pair of obligations `ComplexAnalytic.refineDatumGlueNe` takes; the
right-hand side mentions no `r` at all. **That is the content**: by the lemma above `r` is
determined modulo the ideal by the first obligation, and both obligations see it only through its
class, so it can be eliminated. What is left is one statement about one unit.

Forward is the two equations chained; backward is the surjectivity above and then the same chain
read the other way. There is no geometry in either direction and none of the three existentials
`Oka/Analytification/CrossMemberDatumGlue.lean` names is used.

**Why it is worth stating rather than inlining.** It says which of those three existentials the
construction below has to be built out of. Two of them produce an equality of *opens*, and an
equality of opens does not give an associate — `ComplexAnalytic.exists_mk_rename_eq`'s own
docstring says that implication is a Nullstellensatz statement nothing here proves. The third does
produce the unit, and it is the one the construction below uses. -/
theorem refineDatumCross_exists_iff (a b : B) :
    (∃ (r : MvPolynomial (ULift.{u} (Fin ((obj (σ b)).n + 1))) ℂ)
        (u : (PresentedAlgebra.{u} ((obj (σ b)).n + 1) ((obj (σ b)).k + 1)
          (localisationPresentation.{u} (obj (σ b)).g (poly (σ b) (σ a))))ˣ),
        RefineDatumCrossEq.{u} obj σ fam poly q glue a b r ∧
          RefineDatumCrossUnit.{u} obj σ fam poly q a b r u) ↔
      ∃ u : (PresentedAlgebra.{u} ((obj (σ b)).n + 1) ((obj (σ b)).k + 1)
          (localisationPresentation.{u} (obj (σ b)).g (poly (σ b) (σ a))))ˣ,
        coverOverlapClass.{u} obj poly (σ b) (σ a) (q b a * fam b) =
          (u : PresentedAlgebra.{u} ((obj (σ b)).n + 1) ((obj (σ b)).k + 1)
              (localisationPresentation.{u} (obj (σ b)).g (poly (σ b) (σ a)))) *
            refineDatumCrossAlgEquiv.{u} obj poly glue (σ a) (σ b)
              (coverOverlapClass.{u} obj poly (σ a) (σ b) (q a b * fam a)) := by
  constructor
  · rintro ⟨r, u, he, hu⟩
    exact ⟨u, hu.trans (congrArg (fun z ↦ (u : PresentedAlgebra.{u} ((obj (σ b)).n + 1)
      ((obj (σ b)).k + 1) (localisationPresentation.{u} (obj (σ b)).g (poly (σ b) (σ a)))) * z)
      he.symm)⟩
  · rintro ⟨u, h⟩
    obtain ⟨r, hr⟩ := exists_refineDatumCrossEq.{u} obj poly glue σ fam q a b
    exact ⟨r, u, hr, h.trans (congrArg (fun z ↦ (u : PresentedAlgebra.{u} ((obj (σ b)).n + 1)
      ((obj (σ b)).k + 1) (localisationPresentation.{u} (obj (σ b)).g (poly (σ b) (σ a)))) * z)
      hr)⟩

/-! ### The choice of extra factor that makes the associate hold -/

/-- **The rule the caller's extra factor has to follow at an ordered pair**: the class of
`q a b`, read in the overlap algebra on the `σ a` side, is a unit multiple of the class of
`fam b` carried over from the `σ b` side by the datum's own glue.

**This is a condition on one entry of the family and it names no other entry**, which is why the
whole family can be chosen entry by entry below. It is also symmetric in shape rather than in
fact: the condition at `(b, a)` is the same sentence with the two members exchanged, and what
relates the two is the input's `hsymm` and nothing else. -/
def RefineDatumCrossFactor (a b : B) : Prop :=
  ∃ u : (PresentedAlgebra.{u} ((obj (σ a)).n + 1) ((obj (σ a)).k + 1)
      (localisationPresentation.{u} (obj (σ a)).g (poly (σ a) (σ b))))ˣ,
    coverOverlapClass.{u} obj poly (σ a) (σ b) (q a b) =
      (u : PresentedAlgebra.{u} ((obj (σ a)).n + 1) ((obj (σ a)).k + 1)
          (localisationPresentation.{u} (obj (σ a)).g (poly (σ a) (σ b)))) *
        (refineDatumCrossAlgEquiv.{u} obj poly glue (σ a) (σ b)).symm
          (coverOverlapClass.{u} obj poly (σ b) (σ a) (fam b))

/-- **Such a factor exists at every ordered pair**, and this is where
`ComplexAnalytic.exists_mk_rename_eq` is spent.

The element to be matched lives in the overlap algebra, which is a quotient, so it has a preimage
in the localised polynomial ring; that preimage is a polynomial in the *localisation's* variables
and the field wants one in the member's own. `ComplexAnalytic.exists_mk_rename_eq` is exactly the
statement that every polynomial of a localisation is a unit multiple of a renamed one, and the
unit it keeps — the one its geometric counterpart drops — is the unit this condition asks for.

**Nothing here is a choice of cover or of refinement.** The polynomial produced is whatever that
lemma returns, and the only property claimed for it is the displayed one. -/
theorem exists_refineDatumCrossFactor (a b : B) :
    ∃ x : MvPolynomial (ULift.{u} (Fin (obj (σ a)).n)) ℂ,
      ∃ u : (PresentedAlgebra.{u} ((obj (σ a)).n + 1) ((obj (σ a)).k + 1)
          (localisationPresentation.{u} (obj (σ a)).g (poly (σ a) (σ b))))ˣ,
        coverOverlapClass.{u} obj poly (σ a) (σ b) x =
          (u : PresentedAlgebra.{u} ((obj (σ a)).n + 1) ((obj (σ a)).k + 1)
              (localisationPresentation.{u} (obj (σ a)).g (poly (σ a) (σ b)))) *
            (refineDatumCrossAlgEquiv.{u} obj poly glue (σ a) (σ b)).symm
              (coverOverlapClass.{u} obj poly (σ b) (σ a) (fam b)) := by
  obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective
    ((refineDatumCrossAlgEquiv.{u} obj poly glue (σ a) (σ b)).symm
      (coverOverlapClass.{u} obj poly (σ b) (σ a) (fam b)))
  obtain ⟨x, u, hx⟩ := exists_mk_rename_eq.{u} (obj (σ a)).g (poly (σ a) (σ b)) p
  exact ⟨x, u, hx.trans (congrArg (fun z ↦ (u : PresentedAlgebra.{u} ((obj (σ a)).n + 1)
    ((obj (σ a)).k + 1) (localisationPresentation.{u} (obj (σ a)).g (poly (σ a) (σ b)))) * z) hp)⟩

/-- **A family obeying the rule at both orders of a pair makes the associate hold at that pair.**

The computation, with `Φ` the datum's algebra isomorphism from the `σ a` side to the `σ b` side
and `α`, `β` the classes of `fam a` and `fam b` on their own sides:

* the rule at `(b, a)` gives `q b a ↦ u₂ · Φ α`, once the input's `hsymm` has turned the swapped
  isomorphism into `Φ` — this is the only step that uses it;
* the rule at `(a, b)` gives `q a b ↦ u₁ · Φ⁻¹ β`, so `Φ` of the `a`-side product is
  `Φ u₁ · β · Φ α`;
* the `b`-side product is `u₂ · Φ α · β`.

The two differ by `u₂ · (Φ u₁)⁻¹`, and `Φ u₁` is a unit because `Φ` is an isomorphism. **The
commutativity of the overlap algebra is doing real work here** — the two products are the same
three factors in two orders — and that is why the last step is `ring`.

Note what is *not* needed: the two members may be equal, and nothing below asks whether they are.
The hypothesis a consumer has at the unequal pairs is a hypothesis about where the field reads
this, not about where the statement holds. -/
theorem exists_refineDatumCrossUnit_of_factor
    (hsymm : ∀ i j : J, glue j i = (glue i j).symm) (a b : B)
    (hab : RefineDatumCrossFactor.{u} obj poly glue σ fam q a b)
    (hba : RefineDatumCrossFactor.{u} obj poly glue σ fam q b a) :
    ∃ u : (PresentedAlgebra.{u} ((obj (σ b)).n + 1) ((obj (σ b)).k + 1)
        (localisationPresentation.{u} (obj (σ b)).g (poly (σ b) (σ a))))ˣ,
      coverOverlapClass.{u} obj poly (σ b) (σ a) (q b a * fam b) =
        (u : PresentedAlgebra.{u} ((obj (σ b)).n + 1) ((obj (σ b)).k + 1)
            (localisationPresentation.{u} (obj (σ b)).g (poly (σ b) (σ a)))) *
          refineDatumCrossAlgEquiv.{u} obj poly glue (σ a) (σ b)
            (coverOverlapClass.{u} obj poly (σ a) (σ b) (q a b * fam a)) := by
  obtain ⟨u₁, h₁⟩ := hab
  obtain ⟨u₂, h₂⟩ := hba
  rw [refineDatumCrossAlgEquiv_symm.{u} obj poly glue hsymm (σ a) (σ b), AlgEquiv.symm_symm] at h₂
  set Φ := refineDatumCrossAlgEquiv.{u} obj poly glue (σ a) (σ b) with hΦ
  obtain ⟨U, hU⟩ : ∃ U : (PresentedAlgebra.{u} ((obj (σ b)).n + 1) ((obj (σ b)).k + 1)
      (localisationPresentation.{u} (obj (σ b)).g (poly (σ b) (σ a))))ˣ,
      (U : PresentedAlgebra.{u} ((obj (σ b)).n + 1) ((obj (σ b)).k + 1)
        (localisationPresentation.{u} (obj (σ b)).g (poly (σ b) (σ a)))) =
        Φ (u₁ : PresentedAlgebra.{u} ((obj (σ a)).n + 1) ((obj (σ a)).k + 1)
          (localisationPresentation.{u} (obj (σ a)).g (poly (σ a) (σ b)))) :=
    ⟨Units.map (Φ : _ →ₐ[ℂ] _).toRingHom.toMonoidHom u₁, rfl⟩
  refine ⟨u₂ * U⁻¹, ?_⟩
  rw [coverOverlapClass_mul, coverOverlapClass_mul, h₁, h₂, map_mul, map_mul,
    AlgEquiv.apply_symm_apply, ← hU, Units.val_mul,
    show (u₂ : PresentedAlgebra.{u} ((obj (σ b)).n + 1) ((obj (σ b)).k + 1)
        (localisationPresentation.{u} (obj (σ b)).g (poly (σ b) (σ a)))) * (U⁻¹ : _) *
        ((U : _) * coverOverlapClass.{u} obj poly (σ b) (σ a) (fam b) *
          Φ (coverOverlapClass.{u} obj poly (σ a) (σ b) (fam a))) =
      ((U⁻¹ : _) * (U : _)) * ((u₂ : _) *
        coverOverlapClass.{u} obj poly (σ b) (σ a) (fam b) *
          Φ (coverOverlapClass.{u} obj poly (σ a) (σ b) (fam a))) from by ring,
    U.inv_mul, one_mul]
  ring

/-! ### The producer -/

/-- **The caller's choice exists, at every ordered pair at once**, as soon as the original cover
datum's glue is symmetric.

This is what `Oka/Analytification/CrossMemberDatumGlue.lean` recorded as absent until this file
landed: the field it builds is a function of `q`, `r`, `u` and two equations, and *"nothing
produces `r` or `u`"*. Something does now, and the three families come out together because each
is chosen from the previous one pointwise. That file's bullet is rewritten in the same push, so
the quotation above is of a sentence no longer on the tree — **`ComplexAnalytic.refineDatumGlue`
still takes the choice as an argument, and what changed is only that one can be supplied.**

**The input hypothesis is the datum's own `hsymm` and nothing more.** No hypothesis on `σ`, none
on the members being distinct, and no condition on the cover beyond the one every consumer of a
cover datum in this repository already carries. In particular the polynomials are not required to
cut anything out: the statement is an identity in the overlap algebras and the geometry never
enters.

**What it does not say.** It produces *a* choice, not a canonical one — three `choose`s, and a
different run of `ComplexAnalytic.exists_mk_rename_eq` gives a different `q`. Nor does it say the
choice is compatible across the two orders of a pair in the sense a `hsymm` for the *refined*
datum would need; that is a statement about the resulting `glue` field and it is not this one. -/
theorem exists_refineDatumCross (hsymm : ∀ i j : J, glue j i = (glue i j).symm) :
    ∃ (q : ∀ a : B, B → MvPolynomial (ULift.{u} (Fin (obj (σ a)).n)) ℂ)
      (r : ∀ _ b : B, MvPolynomial (ULift.{u} (Fin ((obj (σ b)).n + 1))) ℂ)
      (u : ∀ a b : B, (PresentedAlgebra.{u} ((obj (σ b)).n + 1) ((obj (σ b)).k + 1)
        (localisationPresentation.{u} (obj (σ b)).g (poly (σ b) (σ a))))ˣ),
      (∀ a b : B, RefineDatumCrossEq.{u} obj σ fam poly q glue a b (r a b)) ∧
        ∀ a b : B, RefineDatumCrossUnit.{u} obj σ fam poly q a b (r a b) (u a b) := by
  choose x hx using exists_refineDatumCrossFactor.{u} obj poly glue σ fam
  have hfac : ∀ a b : B, RefineDatumCrossFactor.{u} obj poly glue σ fam x a b := hx
  choose r u hre hru using fun a b ↦
    (refineDatumCross_exists_iff.{u} obj poly glue σ fam x a b).2
      (exists_refineDatumCrossUnit_of_factor.{u} obj poly glue σ fam x hsymm a b
        (hfac a b) (hfac b a))
  exact ⟨x, r, u, hre, hru⟩

end

end ComplexAnalytic
