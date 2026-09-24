/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Analytification.RefineDatumTransition

/-!
# The refined `hrange` at the triples whose three members are not all different

`Oka/Analytification/RefineDatumTransition.lean` settles the range law of a cross-member refined
cover datum at a triple `(a, b, c)` whose three members `σ a`, `σ b`, `σ c` are pairwise
different, up to one containment in the caller's own `D(q b c)`. Its `## What is not here` says
why the rest of the law is not that argument with a hypothesis dropped:

> **`hrange` itself, and it is not one case away.** … The mixed triples — `σ a = σ b` with `σ c`
> different, and the two others — are untouched, and they are not this argument with a hypothesis
> dropped: `ComplexAnalytic.refineDatumGlue` takes its equal branch there, whose triangle
> (`ComplexAnalytic.refineDatumGlueEq_analytification_comp`) is over a *member* and not over an
> overlap, so the square below has no statement at those triples, let alone a proof.

**Both halves of that are right and neither is an obstruction.** A triangle over a member is
exactly what `Oka/Analytification/CoverRefinement.lean` discharges *both* geometric laws from at a
constant `σ` — `ComplexAnalytic.refineTransitionHom_localisationProj` — and what was missing is
that statement for a general `σ` at the pairs where it happens to be equal.
`ComplexAnalytic.refineDatumTransitionHom_localisationProj_of_eq` below is it, and with it the
four remaining shapes separate, one of them into a theorem with no hypothesis at all.

## The four shapes, and what each one costs

Which branch `ComplexAnalytic.refineDatumGlue` takes at `(a, b)` is decided by `σ a = σ b`; which
form the target `D(f_bc)` takes is decided by `σ b = σ c`. Beyond the pairwise-different triple
that leaves four:

* **`σ a = σ b = σ c`.** Equal branch, equal target, and the law **holds outright** —
  `ComplexAnalytic.range_refineDatumTransitionHom_subset_of_eq`. Neither the caller's `q` nor the
  original datum's own `hrange` is read. The transition does not move a point of the member, and
  the point is in `D(fam c)` already because it is in the refined `a`-`c` overlap. That is
  `ComplexAnalytic.refineHrange`'s sentence, at a `σ` which is equal at these three indices and
  arbitrary elsewhere.
* **`σ a = σ c` with `σ a ≠ σ b`.** Cross branch, cross target, and **the original datum's
  `hrange` is not read here either.** `ComplexAnalytic.range_coverTransitionHom_subset` puts the
  image in `D(f_{σb σa})` whatever the input is, and `σ c = σ a` makes that the open the law asks
  for. Where the pairwise-different triple spends the original law, this one spends the
  unconditional half of it.
* **`σ a = σ b` with `σ b ≠ σ c`.** Equal branch, cross target. The free half is there and comes
  from the *source*: the point is in `D(f_{σa σc})` because it is in the refined `a`-`c` overlap,
  and `σ a = σ b` carries that to `D(f_{σb σc})`.
* **`σ b = σ c` with `σ a ≠ σ b`.** Cross branch, **equal target**, and **there is no free half.**
  The law asks the image to land in `D(fam c)`, which is the caller's refining family and not the
  original datum's polynomial, so nothing about the original cover bears on it.
  `ComplexAnalytic.range_refineDatumTransitionHom_subset_iff_of_eq_bc` is therefore an equivalence
  whose right-hand side is the *whole* law and not a residue, which is the one place on this line
  where those two readings differ.

**So the residue is the same at three of the four shapes and different at the fourth**, and that
is the finding worth carrying: at every triple with `σ b ≠ σ c` what is left of `hrange` is the
containment in `D(q b c)` that `Oka/Analytification/RefineDatumTransition.lean` already isolated,
and only the source of the free half changes.
`ComplexAnalytic.range_refineDatumTransitionHom_subset_iff_of_ne_bc` is that statement with the
free half taken as a hypothesis; the two shape-specific corollaries below supply it, and that
file's `ComplexAnalytic.range_refineDatumTransitionHom_subset_iff` is the third instance of it and
is **not** reproved here.

## The transport, and why it is a named `def`

The equal branch's triangle ends over `obj (σ a)` where the law is stated over `obj (σ b)`, so the
statement carries an identification of the two members as its last factor.
`ComplexAnalytic.coverSpaceHomOfEq` is that factor, and it exists as a type-ascribed `def` for the
reason `ComplexAnalytic.refineDatumCrossProjSpace` does — **this is that reason's second site, and
it bites harder here.** Written out as
`AnalyticSpace.forgetToLocallyRingedSpace.map (analytificationFunctor.map (eqToHom …))` the factor
has type `forgetToLocallyRingedSpace.obj (analytificationFunctor.obj (obj (σ a))) ⟶ …` where
`ComplexAnalytic.coverSpace` is asked for, and the two agree only by unfolding a semireducible
definition. The goal is then ill-typed at `instances` transparency, and what fails is not the step
that mentions the factor: **`rw` refuses a pattern it can see, five factors away, and
`simp only [CategoryTheory.Functor.map_comp]` leaves the whole side of an equation unsplit.** Both
were measured on the way to `ComplexAnalytic.refineDatumTransitionHom_localisationProj_of_eq`, and
in both the error names a pattern that is visibly present. Ascribing the type once removes both,
and no proof below has to mention either spelling.

`ComplexAnalytic.coverSpaceHomOfEq_refl` is what the two transport lemmas run on: with the two
indices abstract, `subst` reduces the identification to the identity, and the two `▸`s in the
statements then disappear by proof irrelevance rather than by a rewrite. That is why those lemmas
are stated at abstract `i`, `j`, `k` in the index type rather than at `σ a`, `σ b`, `σ c`, where
nothing is a variable and `subst` has nothing to eliminate.

## The `simp` discipline, and this is the recorded defect's fourth site

`Oka/Analytification/RefineDatumTransition.lean` records three routes by which a tactic plants an
equation or congruence lemma into the module that ran it, the third being a `simp only` naming no
definition at all — `[LocallyRingedSpace.comp_base, TopCat.hom_comp, ContinuousMap.comp_apply]` —
which traverses a goal mentioning a definition whose arguments include proofs. **The first draft
of this file ran that same `simp only` in the two range proofs below and planted two congruence
lemmas**, one for `ComplexAnalytic.coverSpaceHomOfEq` and one for
`ComplexAnalytic.refineDatumGlue`, which belongs to
`Oka/Analytification/CrossMemberDatumGlue.lean`. The build was green and `Δdump` was `+16` where
the draft declared fourteen things.

The cure is that file's: the bridge is `rfl`, so
`ComplexAnalytic.refineDatumTripleIncl_localisationProj_apply_of_eq` states the composite applied
to a point with its type written out and proves it by `congrArg`, and no tactic below has to
traverse either term. `Δdump` for the push that created this file was **+15**, the number of
declarations it then had, and *`Δdump` equal to the declaration count* is the figure to check a
branch on this file by. It has since taken in three more declarations from
`Oka/Analytification/RefineDatumCocycle.lean` — the groupoid facts about the identification, named
under `## Main results` below — so fifteen is that push's figure and not a count of this file.

## Main definitions

- `ComplexAnalytic.coverSpaceHomOfEq`: **two members the index map sends two indices to,
  identified**, as a morphism of `ComplexAnalytic.coverSpace`.

## Main results

- `ComplexAnalytic.coverSpaceHomOfEq_refl`: **the identification at `rfl` is the identity**, which
  is the whole content of the two transport lemmas.
- `ComplexAnalytic.coverSpaceHomOfEq_trans`, `ComplexAnalytic.coverSpaceHomOfEq_self` and
  `ComplexAnalytic.coverSpaceHomOfEq_comp_symm`: **the identification composes, is the identity at
  every proof of `i = i`, and cancels its own inverse.** They are the groupoid facts about the
  definition above and are stated here for that reason and not for their consumer's: everything
  that reads them is under `ComplexAnalytic.refineDatumHcocycle`, in
  `Oka/Analytification/RefineDatumCocycle.lean` — **two import edges below this file**, through
  `Oka/Analytification/RefineDatumGlueData.lean`. (This bullet read *"four files downstream"*
  until the distance was measured.)
- `ComplexAnalytic.coverSpaceHomOfEq_comp_coverIota`: **the identification is one over the glued
  space** — including the `j`-th member after it is including the `i`-th. It is here for the same
  reason as the three above and by the same rule, and it is the only statement in this repository
  that mentions both `ComplexAnalytic.coverSpaceHomOfEq` and `ComplexAnalytic.coverIota`; its
  consumer is `Oka/Analytification/RefineDatumToBase.lean`.
- `ComplexAnalytic.mem_localisationOpen_coverSpaceHomOfEq` and
  `ComplexAnalytic.mem_coverOpen_coverSpaceHomOfEq`: **the identification carries a distinguished
  open to the corresponding one**, once for a polynomial of the refining family and once for one
  of the original datum.
- `ComplexAnalytic.coverOpen_refineDatumPoly_of_eq`: **the refined overlap of two members lying
  over one is the preimage of `D(fam b)`**, the mirror of
  `ComplexAnalytic.coverOpen_refineDatumPoly_of_ne`.
- `ComplexAnalytic.refineDatumTransitionHom_localisationProj_of_eq`: **the equal branch's
  transition lies over its member.** The statement whose absence the bullet quoted above records,
  and the counterpart at a general `σ` of
  `ComplexAnalytic.refineTransitionHom_localisationProj`.
- `ComplexAnalytic.refineDatumTripleIncl_localisationProj_of_eq` and
  `ComplexAnalytic.refineDatumTripleIncl_localisationProj_apply_of_eq`: **the same restricted to a
  triple overlap**, and then read at a point of it, which is the form the two range statements
  below consume and the form that keeps a `simp only` from planting two congruence lemmas.
- `ComplexAnalytic.range_refineDatumTransitionHom_subset_of_eq`: **`hrange` at a triple whose
  three members are all equal**, with no hypothesis on the caller's `q`.
- `ComplexAnalytic.range_refineDatumTransitionHom_localisationProj_subset_of_eq_ac` and
  `ComplexAnalytic.range_refineDatumTransitionHom_localisationProj_subset_of_eq_ab`: **the free
  half at the two mixed triples that have one**, from the unconditional half of the original
  transition law and from the source's own second overlap respectively.
- `ComplexAnalytic.range_refineDatumTransitionHom_subset_iff_of_ne_bc`: **wherever `σ b ≠ σ c`,
  the law is the free half and one containment in `D(q b c)`** — the residue, isolated once and
  with the free half as a hypothesis.
- `ComplexAnalytic.range_refineDatumTransitionHom_subset_iff_of_eq_ac` and
  `ComplexAnalytic.range_refineDatumTransitionHom_subset_iff_of_eq_ab`: **that residue at the two
  shapes**, with the free half discharged.
- `ComplexAnalytic.range_refineDatumTransitionHom_subset_iff_of_eq_bc`: **and where `σ b = σ c`
  the law is equivalent to a containment in `D(fam c)`, which is the whole of it.**

## What is not here

* **No single `hrange` here, and so no `hcocycle` here.** This file produces one theorem and
  three equivalences at four disjoint shapes, not one proof of the law; and
  `ComplexAnalytic.coverTriple` takes `hrange` as an argument, so the cocycle law of the refined
  datum mentions such a proof three times in its own statement. Assembling the shapes needs a
  hypothesis on `q`, which is the next bullet, and the assembly is a decision nothing here makes.
  `Oka/Analytification/RefineDatumGlueData.lean` makes it, joins these four shapes to the
  pairwise different one and states the cocycle law off the result — which it does not prove.
* **No hypothesis on `q`, and no refined cover datum.** As in
  `Oka/Analytification/RefineDatumTransition.lean`: nothing here adopts a right-hand side as an
  assumption. `ComplexAnalytic.coverGlueData` at a non-constant `σ` asks for all three laws at
  once and this file supplies part of one; the file above supplies two and takes the third as a
  hypothesis, which is as close to reachable as it is.
* **Nothing about the fourth shape's residue.** That `D(fam c)` containment relates the caller's
  extra factor to the caller's refining family, and this file says only that it is what the law
  asks — not whether `ComplexAnalytic.exists_refineDatumCross`'s choice satisfies it, in either
  direction.
* **The pairwise-different triple is not reproved.**
  `ComplexAnalytic.range_refineDatumTransitionHom_subset_iff` stands where it is and is an
  instance of `ComplexAnalytic.range_refineDatumTransitionHom_subset_iff_of_ne_bc` here; the
  earlier file is not opened.
* **Nothing about `hsymm`**, which is `ComplexAnalytic.refineDatumGlue_symm`
  (`Oka/Analytification/RefineDatumSymm.lean`) and is algebraic where everything here is
  geometric.
* **No scheme and no `admissible`**, as in the files this one sits beside.
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

/-! ### Two members the index map sends two indices to, identified -/

/-- **Two members of the original cover that are equal, identified**, as a morphism of
`ComplexAnalytic.coverSpace`: the equality of presentations analytified and read at the
locally-ringed-space level.

**The type ascription is the point and it is not cosmetic**; see this file's module docstring for
what the unascribed spelling costs and where the two failures show up. -/
def coverSpaceHomOfEq {i j : J} (h : i = j) :
    coverSpace.{u} obj i ⟶ coverSpace.{u} obj j :=
  AnalyticSpace.forgetToLocallyRingedSpace.{u}.map
    (analytificationFunctor.{u}.map (eqToHom (congrArg obj h)))

/-- **At `rfl` the identification is the identity**, which is all either transport lemma below
uses.

Both functors carry the identity to the identity, and `eqToHom` of `congrArg obj rfl` is the
identity already. It is a term and not a `rw`: the goal is ill-typed at `instances` transparency
for the reason the definition above is ascribed, and a `rw` chain fails on `𝟙` where an `exact`
does not. -/
theorem coverSpaceHomOfEq_refl (i : J) :
    coverSpaceHomOfEq.{u} obj (rfl : i = i) = 𝟙 (coverSpace.{u} obj i) :=
  (congrArg AnalyticSpace.forgetToLocallyRingedSpace.{u}.map
      (CategoryTheory.Functor.map_id analytificationFunctor.{u} (obj i))).trans
    (CategoryTheory.Functor.map_id AnalyticSpace.forgetToLocallyRingedSpace.{u} _)

/-- **The identification of two equal members composes**, which is the whole content of the shape
where a triple's three members are all equal, once its three edges are read down.

`subst` on the first equality and `ComplexAnalytic.coverSpaceHomOfEq_refl`; the second transport is
then along the same proof it started as. Its consumer is
`Oka/Analytification/RefineDatumCocycle.lean`. -/
theorem coverSpaceHomOfEq_trans {i j k : J} (h₁ : i = j) (h₂ : j = k) :
    coverSpaceHomOfEq.{u} obj h₁ ≫ coverSpaceHomOfEq.{u} obj h₂ =
      coverSpaceHomOfEq.{u} obj (h₁.trans h₂) := by
  subst h₁
  rw [coverSpaceHomOfEq_refl, Category.id_comp]

/-- **An identification of a member with itself is the identity**, whatever proof it is along.

It is `ComplexAnalytic.coverSpaceHomOfEq_refl` verbatim: a proof of `i = i` and `rfl` are the same
proof, so no `subst` and no transport is involved. Stated because the all-equal shape of the
cocycle law in `Oka/Analytification/RefineDatumCocycle.lean` composes three identifications and
lands on a proof built out of that triple's three equalities and not on `rfl`, and a reader should
not have to reconstruct why that costs nothing. -/
theorem coverSpaceHomOfEq_self {i : J} (h : i = i) :
    coverSpaceHomOfEq.{u} obj h = 𝟙 (coverSpace.{u} obj i) :=
  coverSpaceHomOfEq_refl.{u} obj i

/-- **An identification and its inverse compose to the identity**, which is what the shape with two
of a triple's three members equal is left with after its pair cancellation, in
`Oka/Analytification/RefineDatumCocycle.lean`. -/
theorem coverSpaceHomOfEq_comp_symm {i j : J} (h : i = j) :
    coverSpaceHomOfEq.{u} obj h ≫ coverSpaceHomOfEq.{u} obj h.symm = 𝟙 _ := by
  subst h
  rw [coverSpaceHomOfEq_refl]
  exact Category.comp_id _

section

variable (glue : ∀ i j : J, coverOverlap.{u} obj poly i j ≅ coverOverlap.{u} obj poly j i)
  (hrangeC : ∀ i j k : J, i ≠ j → i ≠ k → j ≠ k →
    Set.range (coverTripleIncl.{u} obj poly i j k ≫
        coverTransitionHom.{u} obj poly glue i j).base ⊆
      (coverOpen.{u} obj poly j k : Set (coverSpace.{u} obj j)))
  (hsymmC : ∀ i j : J, glue j i = (glue i j).symm)
  (hcocycleC : ∀ i j k : J, ∀ hij : i ≠ j, ∀ hik : i ≠ k, ∀ hjk : j ≠ k,
    coverTriple.{u} obj poly glue hrangeC i j k hij hik hjk ≫
      coverTriple.{u} obj poly glue hrangeC j k i hjk hij.symm hik.symm ≫
        coverTriple.{u} obj poly glue hrangeC k i j hik.symm hjk.symm hij = 𝟙 _)

/-- **The identification of two equal members is one over the glued space**: including the `j`-th
member after it is including the `i`-th.

`subst` and `ComplexAnalytic.coverSpaceHomOfEq_refl`, as with the three groupoid facts above and
for the same reason — at abstract indices the equality is a variable and `subst` has something to
eliminate.

**It is here rather than in `Oka/Analytification/AffineCover.lean`, and that is not a free
choice**: this file declares `ComplexAnalytic.coverSpaceHomOfEq`, and the module it would
otherwise go to does not know the name. It is the only statement in this repository that mentions
both that definition and `ComplexAnalytic.coverIota`, so the placement rule
`Oka/Analytification/RefineDatumCocycle.lean` states — the file that owns the vocabulary, not the
file that consumes it — has one answer even though the vocabulary is two files'. Its consumer is
`Oka/Analytification/RefineDatumToBase.lean`. -/
theorem coverSpaceHomOfEq_comp_coverIota {i j : J} (h : i = j) :
    coverSpaceHomOfEq.{u} obj h ≫
        (coverIota.{u} obj poly glue hrangeC hsymmC hcocycleC j).toLRSHom =
      (coverIota.{u} obj poly glue hrangeC hsymmC hcocycleC i).toLRSHom := by
  subst h
  rw [coverSpaceHomOfEq_refl, Category.id_comp]

end

/-- **The identification carries `D(y)` to `D(y)`**, for a polynomial `y` of a third member equal
to both — the form the all-equal triple below reads, where the polynomial is `fam c` and the three
transports are the three equalities of the triple.

Stated at abstract indices rather than at `σ a`, `σ b`, `σ c` **because that is what makes `subst`
available**: at the latter nothing is a variable. After the two substitutions the remaining
transport is along a proof of `i = i`, which is `rfl` by proof irrelevance, so the two sides are
the same membership and nothing has to be rewritten. -/
theorem mem_localisationOpen_coverSpaceHomOfEq {i j k : J} (hij : i = j) (hik : i = k)
    (hjk : j = k) (y : MvPolynomial (ULift.{u} (Fin (obj k).n)) ℂ) (p : coverSpace.{u} obj i) :
    (ConcreteCategory.hom (coverSpaceHomOfEq.{u} obj hij).base) p ∈
        localisationOpen.{u} (obj j).g (hjk ▸ y) ↔
      p ∈ localisationOpen.{u} (obj i).g (hik ▸ y) := by
  subst hij
  subst hik
  rw [coverSpaceHomOfEq_refl]
  exact Iff.rfl

/-- **The identification carries the original datum's own `D(f_ik)` to `D(f_jk)`**, which is the
form the mixed triple with `σ a = σ b` reads.

One transport where the previous lemma has three: the datum's polynomial is indexed by the member
and the third index is untouched, so `subst` leaves both sides literally equal. -/
theorem mem_coverOpen_coverSpaceHomOfEq {i j : J} (h : i = j) (k : J) (p : coverSpace.{u} obj i) :
    (ConcreteCategory.hom (coverSpaceHomOfEq.{u} obj h).base) p ∈ coverOpen.{u} obj poly j k ↔
      p ∈ coverOpen.{u} obj poly i k := by
  subst h
  rw [coverSpaceHomOfEq_refl]
  exact Iff.rfl

/-! ### The refined overlap of two members lying over one -/

/-- **The refined overlap of two members lying over one member is the preimage of `D(fam b)`**
along the projection of the `a`-th refined member down to that member.

`ComplexAnalytic.refineDatumPoly_of_eq` and `ComplexAnalytic.localisationOpen_rename`, in that
order and nothing else — the mirror of `ComplexAnalytic.coverOpen_refineDatumPoly_of_ne`, and
shorter than it because there is no product to split: the diagonal normalisation has already
removed the datum's own polynomial from this branch.

The `change` is what lets the rewrite reach `ComplexAnalytic.refineDatumPoly` under
`ComplexAnalytic.coverOpen`, for the reason that theorem's proof records. -/
theorem coverOpen_refineDatumPoly_of_eq {a b : B} (h : σ a = σ b) :
    coverOpen.{u} (refineDatumObj.{u} obj σ fam) (refineDatumPoly.{u} obj poly σ fam q) a b =
      (TopologicalSpace.Opens.map
          (localisationProj.{u} (obj (σ a)).g (fam a)).toLRSHom.base).obj
        (localisationOpen.{u} (obj (σ a)).g (h ▸ fam b)) := by
  change localisationOpen.{u} (localisationPresentation.{u} (obj (σ a)).g (fam a))
      (refineDatumPoly.{u} obj poly σ fam q a b) = _
  rw [refineDatumPoly_of_eq.{u} obj poly σ fam q h, localisationOpen_rename]

variable (glue : ∀ i j : J, coverOverlap.{u} obj poly i j ≅ coverOverlap.{u} obj poly j i)
  (rr : ∀ _ b : B, MvPolynomial (ULift.{u} (Fin ((obj (σ b)).n + 1))) ℂ)
  (uu : ∀ a b : B, (PresentedAlgebra.{u} ((obj (σ b)).n + 1) ((obj (σ b)).k + 1)
    (localisationPresentation.{u} (obj (σ b)).g (poly (σ b) (σ a))))ˣ)

/-! ### The equal branch's transition, over its member -/

/-- **The refined transition lies over its member**, where the two refined members lie over one:
going from the `a`-th refined member to the `b`-th and then down is going down and identifying the
two members.

This is `ComplexAnalytic.refineTransitionHom_localisationProj` at a general `σ`, and the
identification is the only difference — at a constant `σ` the two members are the same object and
the last factor is the identity by `ComplexAnalytic.coverSpaceHomOfEq_refl`.

The proof is that theorem's, with `ComplexAnalytic.refineDatumGlue_of_eq` naming the branch the
field takes at such a pair: unfold both transitions, cancel the two outer comparison isomorphisms
with `ComplexAnalytic.coverOverlapIso_hom_coverIncl`, and what is left is
`ComplexAnalytic.refineDatumGlueEq_analytification_comp` carried down by
`ComplexAnalytic.AnalyticSpace.forgetToLocallyRingedSpace`. The functor is applied to the equation
rather than the equation rewritten under it, for the reason recorded at both. -/
theorem refineDatumTransitionHom_localisationProj_of_eq
    (he : ∀ a b : B, ∀ _ : σ a ≠ σ b,
      RefineDatumCrossEq.{u} obj σ fam poly q glue a b (rr a b))
    (hu : ∀ a b : B, ∀ _ : σ a ≠ σ b,
      RefineDatumCrossUnit.{u} obj σ fam poly q a b (rr a b) (uu a b)) {a b : B} (h : σ a = σ b) :
    coverTransitionHom.{u} (refineDatumObj.{u} obj σ fam) (refineDatumPoly.{u} obj poly σ fam q)
          (refineDatumGlue.{u} obj σ fam poly q glue rr uu he hu) a b ≫
        (localisationProj.{u} (obj (σ b)).g (fam b)).toLRSHom =
      coverIncl.{u} (refineDatumObj.{u} obj σ fam) (refineDatumPoly.{u} obj poly σ fam q) a b ≫
        (localisationProj.{u} (obj (σ a)).g (fam a)).toLRSHom ≫ coverSpaceHomOfEq.{u} obj h := by
  rw [coverTransitionHom, coverTransition, Iso.trans_hom, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Category.assoc, Category.assoc,
    reassoc_of% (coverOverlapIso_hom_coverIncl.{u} (refineDatumObj.{u} obj σ fam)
      (refineDatumPoly.{u} obj poly σ fam q) b a),
    Iso.inv_comp_eq,
    reassoc_of% (coverOverlapIso_hom_coverIncl.{u} (refineDatumObj.{u} obj σ fam)
      (refineDatumPoly.{u} obj poly σ fam q) a b),
    coverGlueIso, Functor.mapIso_hom, Functor.mapIso_hom,
    refineDatumGlue_of_eq.{u} obj σ fam poly q glue rr uu he hu h]
  have key := congrArg (AnalyticSpace.forgetToLocallyRingedSpace.{u}.map)
    (refineDatumGlueEq_analytification_comp.{u} obj σ fam poly q h)
  simp only [Functor.map_comp] at key
  exact key

/-- **The same, restricted to a triple overlap**: the triple overlap of `a`, `b` and `c` reaches
the `σ b`-th member the same way whether it is followed into the `b`-th refined member or included
into the `a`-th and identified.

The previous statement and `AlgebraicGeometry.LocallyRingedSpace.restrictLE_fac`. The `rw` does
not name `ComplexAnalytic.coverTripleIncl`, which is an `abbrev`, for the reason
`ComplexAnalytic.refineTripleIncl_localisationProj` gives: naming it would plant an equation
lemma on another file's definition. -/
theorem refineDatumTripleIncl_localisationProj_of_eq
    (he : ∀ a b : B, ∀ _ : σ a ≠ σ b,
      RefineDatumCrossEq.{u} obj σ fam poly q glue a b (rr a b))
    (hu : ∀ a b : B, ∀ _ : σ a ≠ σ b,
      RefineDatumCrossUnit.{u} obj σ fam poly q a b (rr a b) (uu a b)) {a b : B} (h : σ a = σ b)
    (c : B) :
    coverTripleIncl.{u} (refineDatumObj.{u} obj σ fam) (refineDatumPoly.{u} obj poly σ fam q)
          a b c ≫
        coverTransitionHom.{u} (refineDatumObj.{u} obj σ fam)
            (refineDatumPoly.{u} obj poly σ fam q)
            (refineDatumGlue.{u} obj σ fam poly q glue rr uu he hu) a b ≫
          (localisationProj.{u} (obj (σ b)).g (fam b)).toLRSHom =
      (coverSpace.{u} (refineDatumObj.{u} obj σ fam) a).ofRestrict
          (coverOpen.{u} (refineDatumObj.{u} obj σ fam) (refineDatumPoly.{u} obj poly σ fam q)
              a b ⊓
            coverOpen.{u} (refineDatumObj.{u} obj σ fam) (refineDatumPoly.{u} obj poly σ fam q)
              a c).isOpenEmbedding ≫
        (localisationProj.{u} (obj (σ a)).g (fam a)).toLRSHom ≫ coverSpaceHomOfEq.{u} obj h := by
  rw [refineDatumTransitionHom_localisationProj_of_eq.{u} obj poly σ fam q glue rr uu he hu h,
    ← Category.assoc, LocallyRingedSpace.restrictLE_fac]

/-- **The same read at a point of the refined triple overlap**, which is the form both range
statements below consume.

It exists so that neither of them has to normalise a composite applied to a point with
`simp only [LocallyRingedSpace.comp_base, TopCat.hom_comp, ContinuousMap.comp_apply]`.
**That `simp only` is green and plants two congruence lemmas**, one for
`ComplexAnalytic.coverSpaceHomOfEq` and one for `ComplexAnalytic.refineDatumGlue` — a definition
of `Oka/Analytification/CrossMemberDatumGlue.lean` — because both take proof arguments and both
occur in the goal. That is the third route
`Oka/Analytification/RefineDatumTransition.lean` records, at a fourth site, and the declaration
dump is what showed it: `Δdump` was `+16` where the file declared fourteen things. The cure is
the same one that file gives — the bridge is `rfl`, so a `congrArg` with its type written out
does it and no tactic has to traverse the term. -/
theorem refineDatumTripleIncl_localisationProj_apply_of_eq
    (he : ∀ a b : B, ∀ _ : σ a ≠ σ b,
      RefineDatumCrossEq.{u} obj σ fam poly q glue a b (rr a b))
    (hu : ∀ a b : B, ∀ _ : σ a ≠ σ b,
      RefineDatumCrossUnit.{u} obj σ fam poly q a b (rr a b) (uu a b)) {a b : B} (h : σ a = σ b)
    (c : B) (x : coverTriplePart.{u} (refineDatumObj.{u} obj σ fam)
      (refineDatumPoly.{u} obj poly σ fam q) a b c) :
    (ConcreteCategory.hom (coverTripleIncl.{u} (refineDatumObj.{u} obj σ fam)
          (refineDatumPoly.{u} obj poly σ fam q) a b c ≫
        coverTransitionHom.{u} (refineDatumObj.{u} obj σ fam)
            (refineDatumPoly.{u} obj poly σ fam q)
            (refineDatumGlue.{u} obj σ fam poly q glue rr uu he hu) a b ≫
          (localisationProj.{u} (obj (σ b)).g (fam b)).toLRSHom).base) x =
      (ConcreteCategory.hom (coverSpaceHomOfEq.{u} obj h).base)
        ((ConcreteCategory.hom ((coverSpace.{u} (refineDatumObj.{u} obj σ fam) a).ofRestrict
              (coverOpen.{u} (refineDatumObj.{u} obj σ fam)
                  (refineDatumPoly.{u} obj poly σ fam q) a b ⊓
                coverOpen.{u} (refineDatumObj.{u} obj σ fam)
                  (refineDatumPoly.{u} obj poly σ fam q) a c).isOpenEmbedding ≫
            (localisationProj.{u} (obj (σ a)).g (fam a)).toLRSHom).base) x) :=
  congrArg (fun m : _ ⟶ _ ↦ (ConcreteCategory.hom m.base) x)
    (refineDatumTripleIncl_localisationProj_of_eq.{u} obj poly σ fam q glue rr uu he hu h c)

/-! ### `hrange` where the three members are equal -/

/-- **`hrange` for the refined datum at a triple whose three members are equal**, and it holds
outright: no hypothesis on the caller's `q`, and the original datum's own `hrange` is not read.

**This is `ComplexAnalytic.refineHrange`'s one sentence about points**, at a `σ` that is equal at
these three indices and arbitrary elsewhere. The transition does not move the point of the member
it lies over, and that point is in `D(fam c)` already because the starting point is in the refined
`a`-`c` overlap; `ComplexAnalytic.coverOpen_refineDatumPoly_of_eq` is what says so at both ends
and `ComplexAnalytic.mem_localisationOpen_coverSpaceHomOfEq` is what crosses the identification of
the two members.

It is not a corollary of that theorem: `ComplexAnalytic.refineDatumGlue` is the field of a datum
built over a general `σ`, and only `ComplexAnalytic.refineDatumGlue_of_eq` — inside
`ComplexAnalytic.refineDatumTransitionHom_localisationProj_of_eq` above — says which branch it
takes at these pairs. -/
theorem range_refineDatumTransitionHom_subset_of_eq
    (he : ∀ a b : B, ∀ _ : σ a ≠ σ b,
      RefineDatumCrossEq.{u} obj σ fam poly q glue a b (rr a b))
    (hu : ∀ a b : B, ∀ _ : σ a ≠ σ b,
      RefineDatumCrossUnit.{u} obj σ fam poly q a b (rr a b) (uu a b)) {a b c : B}
    (hab : σ a = σ b) (hac : σ a = σ c) :
    Set.range (coverTripleIncl.{u} (refineDatumObj.{u} obj σ fam)
          (refineDatumPoly.{u} obj poly σ fam q) a b c ≫
        coverTransitionHom.{u} (refineDatumObj.{u} obj σ fam)
            (refineDatumPoly.{u} obj poly σ fam q)
            (refineDatumGlue.{u} obj σ fam poly q glue rr uu he hu) a b).base ⊆
      (coverOpen.{u} (refineDatumObj.{u} obj σ fam) (refineDatumPoly.{u} obj poly σ fam q) b c :
        Set (coverSpace.{u} (refineDatumObj.{u} obj σ fam) b)) := by
  rintro _ ⟨x, rfl⟩
  refine (SetLike.ext_iff.1 (coverOpen_refineDatumPoly_of_eq.{u} obj poly σ fam q
    (hab.symm.trans hac)) _).2 ?_
  change (ConcreteCategory.hom (coverTripleIncl.{u} (refineDatumObj.{u} obj σ fam)
        (refineDatumPoly.{u} obj poly σ fam q) a b c ≫
      coverTransitionHom.{u} (refineDatumObj.{u} obj σ fam)
          (refineDatumPoly.{u} obj poly σ fam q)
          (refineDatumGlue.{u} obj σ fam poly q glue rr uu he hu) a b ≫
        (localisationProj.{u} (obj (σ b)).g (fam b)).toLRSHom).base) x ∈
    localisationOpen.{u} (obj (σ b)).g ((hab.symm.trans hac) ▸ fam c)
  rw [refineDatumTripleIncl_localisationProj_apply_of_eq.{u} obj poly σ fam q glue rr uu
    he hu hab c x]
  refine (mem_localisationOpen_coverSpaceHomOfEq.{u} obj hab hac (hab.symm.trans hac)
    (fam c) _).2 ?_
  exact (SetLike.ext_iff.1
    (coverOpen_refineDatumPoly_of_eq.{u} obj poly σ fam q hac) _).1 x.2.2

/-! ### The free half at the two mixed triples that have one -/

/-- **The free half where `σ a = σ c` and `σ a ≠ σ b`, and the original datum's `hrange` is not
what supplies it.**

`ComplexAnalytic.range_coverTransitionHom_subset` says the original transition from `σ a` to `σ b`
lands in `D(f_{σb σa})` whatever the input is, and `σ c = σ a` is what makes that the open the
refined law asks for. So where the pairwise-different triple spends the original law — through
`ComplexAnalytic.refineDatumCrossTriple` and
`ComplexAnalytic.range_refineDatumTransitionHom_localisationProj_subset` — this shape spends only
its unconditional half, and needs no lift of the refined triple overlap at all. -/
theorem range_refineDatumTransitionHom_localisationProj_subset_of_eq_ac
    (he : ∀ a b : B, ∀ _ : σ a ≠ σ b,
      RefineDatumCrossEq.{u} obj σ fam poly q glue a b (rr a b))
    (hu : ∀ a b : B, ∀ _ : σ a ≠ σ b,
      RefineDatumCrossUnit.{u} obj σ fam poly q a b (rr a b) (uu a b)) {a b c : B}
    (hab : σ a ≠ σ b) (hac : σ a = σ c) :
    Set.range (coverTripleIncl.{u} (refineDatumObj.{u} obj σ fam)
          (refineDatumPoly.{u} obj poly σ fam q) a b c ≫
        coverTransitionHom.{u} (refineDatumObj.{u} obj σ fam)
            (refineDatumPoly.{u} obj poly σ fam q)
            (refineDatumGlue.{u} obj σ fam poly q glue rr uu he hu) a b ≫
          (localisationProj.{u} (obj (σ b)).g (fam b)).toLRSHom).base ⊆
      (coverOpen.{u} obj poly (σ b) (σ c) : Set (coverSpace.{u} obj (σ b))) := by
  rw [← hac, refineDatumTransitionHom_localisationProj_of_ne.{u} obj poly σ fam q glue rr uu
    he hu hab, ← Category.assoc, LocallyRingedSpace.comp_base, TopCat.coe_comp, Set.range_comp]
  exact subset_trans (Set.image_subset_range _ _)
    (range_coverTransitionHom_subset.{u} obj poly glue (σ a) (σ b))

/-- **The free half where `σ a = σ b` and `σ a ≠ σ c`, and it comes from the source.**

The transition lies over its member by
`ComplexAnalytic.refineDatumTripleIncl_localisationProj_of_eq`, so the image point is the point
the starting point already lay over, identified across the two members. That point is in
`D(f_{σa σc})` because the starting point is in the refined `a`-`c` overlap — the first factor of
`ComplexAnalytic.coverOpen_refineDatumPoly_of_ne`, the caller's `q a c` being discarded — and
`ComplexAnalytic.mem_coverOpen_coverSpaceHomOfEq` carries that to `D(f_{σb σc})`. The original
datum's `hrange` is not read here either. -/
theorem range_refineDatumTransitionHom_localisationProj_subset_of_eq_ab
    (he : ∀ a b : B, ∀ _ : σ a ≠ σ b,
      RefineDatumCrossEq.{u} obj σ fam poly q glue a b (rr a b))
    (hu : ∀ a b : B, ∀ _ : σ a ≠ σ b,
      RefineDatumCrossUnit.{u} obj σ fam poly q a b (rr a b) (uu a b)) {a b c : B}
    (hab : σ a = σ b) (hac : σ a ≠ σ c) :
    Set.range (coverTripleIncl.{u} (refineDatumObj.{u} obj σ fam)
          (refineDatumPoly.{u} obj poly σ fam q) a b c ≫
        coverTransitionHom.{u} (refineDatumObj.{u} obj σ fam)
            (refineDatumPoly.{u} obj poly σ fam q)
            (refineDatumGlue.{u} obj σ fam poly q glue rr uu he hu) a b ≫
          (localisationProj.{u} (obj (σ b)).g (fam b)).toLRSHom).base ⊆
      (coverOpen.{u} obj poly (σ b) (σ c) : Set (coverSpace.{u} obj (σ b))) := by
  rintro _ ⟨x, rfl⟩
  rw [refineDatumTripleIncl_localisationProj_apply_of_eq.{u} obj poly σ fam q glue rr uu
    he hu hab c x]
  refine (mem_coverOpen_coverSpaceHomOfEq.{u} obj poly hab (σ c) _).2 ?_
  exact ((SetLike.ext_iff.1
    (coverOpen_refineDatumPoly_of_ne.{u} obj poly σ fam q hac) _).1 x.2.2).1

/-! ### What is left, at each shape -/

/-- **Wherever `σ b ≠ σ c`, the refined law is the free half and one containment in `D(q b c)`**,
whichever branch the field takes at `(a, b)` and wherever the free half came from.

`ComplexAnalytic.coverOpen_refineDatumPoly_of_ne` splits the target in two and the hypothesis
discharges the first, which is the argument
`ComplexAnalytic.range_refineDatumTransitionHom_subset_iff` makes at a pairwise-different triple.
**It is stated with the free half as a hypothesis because that is the part that differs between
the three shapes it covers** — the original datum's `hrange` there, the unconditional half of the
transition law at `σ a = σ c`, the source's own second overlap at `σ a = σ b` — while the residue
does not differ at all. That earlier theorem is the instance of this one at a pairwise-different
triple and is not reproved here. -/
theorem range_refineDatumTransitionHom_subset_iff_of_ne_bc
    (he : ∀ a b : B, ∀ _ : σ a ≠ σ b,
      RefineDatumCrossEq.{u} obj σ fam poly q glue a b (rr a b))
    (hu : ∀ a b : B, ∀ _ : σ a ≠ σ b,
      RefineDatumCrossUnit.{u} obj σ fam poly q a b (rr a b) (uu a b)) {a b c : B}
    (hbc : σ b ≠ σ c)
    (hfree : Set.range (coverTripleIncl.{u} (refineDatumObj.{u} obj σ fam)
          (refineDatumPoly.{u} obj poly σ fam q) a b c ≫
        coverTransitionHom.{u} (refineDatumObj.{u} obj σ fam)
            (refineDatumPoly.{u} obj poly σ fam q)
            (refineDatumGlue.{u} obj σ fam poly q glue rr uu he hu) a b ≫
          (localisationProj.{u} (obj (σ b)).g (fam b)).toLRSHom).base ⊆
      (coverOpen.{u} obj poly (σ b) (σ c) : Set (coverSpace.{u} obj (σ b)))) :
    Set.range (coverTripleIncl.{u} (refineDatumObj.{u} obj σ fam)
          (refineDatumPoly.{u} obj poly σ fam q) a b c ≫
        coverTransitionHom.{u} (refineDatumObj.{u} obj σ fam)
            (refineDatumPoly.{u} obj poly σ fam q)
            (refineDatumGlue.{u} obj σ fam poly q glue rr uu he hu) a b).base ⊆
        (coverOpen.{u} (refineDatumObj.{u} obj σ fam) (refineDatumPoly.{u} obj poly σ fam q) b c :
          Set (coverSpace.{u} (refineDatumObj.{u} obj σ fam) b)) ↔
      Set.range (coverTripleIncl.{u} (refineDatumObj.{u} obj σ fam)
            (refineDatumPoly.{u} obj poly σ fam q) a b c ≫
          coverTransitionHom.{u} (refineDatumObj.{u} obj σ fam)
              (refineDatumPoly.{u} obj poly σ fam q)
              (refineDatumGlue.{u} obj σ fam poly q glue rr uu he hu) a b ≫
            (localisationProj.{u} (obj (σ b)).g (fam b)).toLRSHom).base ⊆
        ↑(localisationOpen.{u} (obj (σ b)).g (q b c)) := by
  have hfree' := Set.range_subset_iff.1 hfree
  rw [Set.range_subset_iff, Set.range_subset_iff]
  constructor
  · intro H x
    exact ((SetLike.ext_iff.1
      (coverOpen_refineDatumPoly_of_ne.{u} obj poly σ fam q hbc) _).1 (H x)).2
  · intro H x
    exact (SetLike.ext_iff.1
      (coverOpen_refineDatumPoly_of_ne.{u} obj poly σ fam q hbc) _).2 ⟨hfree' x, H x⟩

/-- **The residue at the mixed triple with `σ a = σ c`**, the previous statement with its free
half discharged by
`ComplexAnalytic.range_refineDatumTransitionHom_localisationProj_subset_of_eq_ac`. -/
theorem range_refineDatumTransitionHom_subset_iff_of_eq_ac
    (he : ∀ a b : B, ∀ _ : σ a ≠ σ b,
      RefineDatumCrossEq.{u} obj σ fam poly q glue a b (rr a b))
    (hu : ∀ a b : B, ∀ _ : σ a ≠ σ b,
      RefineDatumCrossUnit.{u} obj σ fam poly q a b (rr a b) (uu a b)) {a b c : B}
    (hab : σ a ≠ σ b) (hac : σ a = σ c) :
    Set.range (coverTripleIncl.{u} (refineDatumObj.{u} obj σ fam)
          (refineDatumPoly.{u} obj poly σ fam q) a b c ≫
        coverTransitionHom.{u} (refineDatumObj.{u} obj σ fam)
            (refineDatumPoly.{u} obj poly σ fam q)
            (refineDatumGlue.{u} obj σ fam poly q glue rr uu he hu) a b).base ⊆
        (coverOpen.{u} (refineDatumObj.{u} obj σ fam) (refineDatumPoly.{u} obj poly σ fam q) b c :
          Set (coverSpace.{u} (refineDatumObj.{u} obj σ fam) b)) ↔
      Set.range (coverTripleIncl.{u} (refineDatumObj.{u} obj σ fam)
            (refineDatumPoly.{u} obj poly σ fam q) a b c ≫
          coverTransitionHom.{u} (refineDatumObj.{u} obj σ fam)
              (refineDatumPoly.{u} obj poly σ fam q)
              (refineDatumGlue.{u} obj σ fam poly q glue rr uu he hu) a b ≫
            (localisationProj.{u} (obj (σ b)).g (fam b)).toLRSHom).base ⊆
        ↑(localisationOpen.{u} (obj (σ b)).g (q b c)) :=
  range_refineDatumTransitionHom_subset_iff_of_ne_bc.{u} obj poly σ fam q glue rr uu he hu
    (fun h ↦ hab (hac.trans h.symm))
    (range_refineDatumTransitionHom_localisationProj_subset_of_eq_ac.{u} obj poly σ fam q glue
      rr uu he hu hab hac)

/-- **The residue at the mixed triple with `σ a = σ b`**, the same with its free half discharged
by `ComplexAnalytic.range_refineDatumTransitionHom_localisationProj_subset_of_eq_ab`.

**The residue is the same containment as at the two cross-branch shapes**, which is not obvious in
advance: the field takes its *equal* branch here, and nothing about that branch enters the
right-hand side. -/
theorem range_refineDatumTransitionHom_subset_iff_of_eq_ab
    (he : ∀ a b : B, ∀ _ : σ a ≠ σ b,
      RefineDatumCrossEq.{u} obj σ fam poly q glue a b (rr a b))
    (hu : ∀ a b : B, ∀ _ : σ a ≠ σ b,
      RefineDatumCrossUnit.{u} obj σ fam poly q a b (rr a b) (uu a b)) {a b c : B}
    (hab : σ a = σ b) (hac : σ a ≠ σ c) :
    Set.range (coverTripleIncl.{u} (refineDatumObj.{u} obj σ fam)
          (refineDatumPoly.{u} obj poly σ fam q) a b c ≫
        coverTransitionHom.{u} (refineDatumObj.{u} obj σ fam)
            (refineDatumPoly.{u} obj poly σ fam q)
            (refineDatumGlue.{u} obj σ fam poly q glue rr uu he hu) a b).base ⊆
        (coverOpen.{u} (refineDatumObj.{u} obj σ fam) (refineDatumPoly.{u} obj poly σ fam q) b c :
          Set (coverSpace.{u} (refineDatumObj.{u} obj σ fam) b)) ↔
      Set.range (coverTripleIncl.{u} (refineDatumObj.{u} obj σ fam)
            (refineDatumPoly.{u} obj poly σ fam q) a b c ≫
          coverTransitionHom.{u} (refineDatumObj.{u} obj σ fam)
              (refineDatumPoly.{u} obj poly σ fam q)
              (refineDatumGlue.{u} obj σ fam poly q glue rr uu he hu) a b ≫
            (localisationProj.{u} (obj (σ b)).g (fam b)).toLRSHom).base ⊆
        ↑(localisationOpen.{u} (obj (σ b)).g (q b c)) :=
  range_refineDatumTransitionHom_subset_iff_of_ne_bc.{u} obj poly σ fam q glue rr uu he hu
    (fun h ↦ hac (hab.trans h))
    (range_refineDatumTransitionHom_localisationProj_subset_of_eq_ab.{u} obj poly σ fam q glue
      rr uu he hu hab hac)

/-- **Where `σ b = σ c` the refined law is equivalent to a containment in `D(fam c)`, and that is
the whole of it and not a residue.**

`ComplexAnalytic.coverOpen_refineDatumPoly_of_eq` at `(b, c)`, and there is nothing to split: the
target belongs to the caller's refining family, so **no half of this is free.** That is the one
shape where the original cover's geometry bears on the law not at all, and the difference between
this statement and the three above is that difference and not a matter of proof length.

**It is stated for every `a`, whichever branch the field takes at `(a, b)`**, because the split of
the target does not read that pair. At `σ a = σ b` its right-hand side is discharged by
`ComplexAnalytic.range_refineDatumTransitionHom_subset_of_eq`; at `σ a ≠ σ b` nothing here
discharges it. -/
theorem range_refineDatumTransitionHom_subset_iff_of_eq_bc
    (he : ∀ a b : B, ∀ _ : σ a ≠ σ b,
      RefineDatumCrossEq.{u} obj σ fam poly q glue a b (rr a b))
    (hu : ∀ a b : B, ∀ _ : σ a ≠ σ b,
      RefineDatumCrossUnit.{u} obj σ fam poly q a b (rr a b) (uu a b)) {a b c : B}
    (hbc : σ b = σ c) :
    Set.range (coverTripleIncl.{u} (refineDatumObj.{u} obj σ fam)
          (refineDatumPoly.{u} obj poly σ fam q) a b c ≫
        coverTransitionHom.{u} (refineDatumObj.{u} obj σ fam)
            (refineDatumPoly.{u} obj poly σ fam q)
            (refineDatumGlue.{u} obj σ fam poly q glue rr uu he hu) a b).base ⊆
        (coverOpen.{u} (refineDatumObj.{u} obj σ fam) (refineDatumPoly.{u} obj poly σ fam q) b c :
          Set (coverSpace.{u} (refineDatumObj.{u} obj σ fam) b)) ↔
      Set.range (coverTripleIncl.{u} (refineDatumObj.{u} obj σ fam)
            (refineDatumPoly.{u} obj poly σ fam q) a b c ≫
          coverTransitionHom.{u} (refineDatumObj.{u} obj σ fam)
              (refineDatumPoly.{u} obj poly σ fam q)
              (refineDatumGlue.{u} obj σ fam poly q glue rr uu he hu) a b ≫
            (localisationProj.{u} (obj (σ b)).g (fam b)).toLRSHom).base ⊆
        ↑(localisationOpen.{u} (obj (σ b)).g (hbc ▸ fam c)) := by
  rw [Set.range_subset_iff, Set.range_subset_iff]
  constructor
  · intro H x
    exact (SetLike.ext_iff.1
      (coverOpen_refineDatumPoly_of_eq.{u} obj poly σ fam q hbc) _).1 (H x)
  · intro H x
    exact (SetLike.ext_iff.1
      (coverOpen_refineDatumPoly_of_eq.{u} obj poly σ fam q hbc) _).2 (H x)

end

end ComplexAnalytic
