/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Analytification.RefineDatumCocycle

/-!
# A cross-member refined cover datum at a non-constant `σ`, for every cover datum

`Oka/Analytification/RefineDatumCocycle.lean` leaves `ComplexAnalytic.refineDatumGlueDataOfLaws`
and `ComplexAnalytic.refineDatumAnalytificationOfLaws` asking a caller for the original datum's
three laws and the two conditions `Oka/Analytification/RefineDatumGlueData.lean` adopts,
`ComplexAnalytic.RefineDatumRangeCross` and `ComplexAnalytic.RefineDatumRangeEq`. Its own
`## What is not here` says, as five files on this line say:

> **No witness.** There is still no example of a refined cover datum at a non-constant `σ`, which
> is taxis #1107's fourth deliverable, and nothing here discharges either of the two conditions.

**There is one now, and it is not one example.** For *every* cover datum and *every* index map
`σ : B → J`, the refinement whose refining family is constantly `1` and whose cutting polynomial
is the original datum's own meets both conditions, with no hypothesis beyond the original datum's
`hrange`. `σ` is not constant as soon as `J` has two elements, which
`ComplexAnalytic.not_isConstant_id` records.

## The route, and the negative it corrects

`ComplexAnalytic.exists_refineDatumCross` (`Oka/Analytification/CrossMemberChoice.lean`) has `q`
in its **conclusion**, so a caller cannot name `q` and then ask it for `r` and `u`, and a witness
built by picking a small `q` and appealing to it does not exist. That is a fact about that lemma
and not about the construction: `ComplexAnalytic.refineDatumGlue` and everything above it take
`q`, `r`, `u` and the two equations **as arguments**, so a witness never calls it — it exhibits
`r` and `u`.

`ComplexAnalytic.exists_refineDatumCross_of_isUnit`
(`Oka/Analytification/CrossMemberDatumGlue.lean`) is what exhibits them, at any `q` and `fam`
whose four polynomials are units in the two localisations. Here:

* `q a b := poly (σ a) (σ b)` is the polynomial that was **inverted** in the algebra the equations
  live in, so `ComplexAnalytic.isUnit_mk_rename_localisationIncl` is the hypothesis verbatim;
* `fam a := 1`, and `1` is a unit.

## Why the two range conditions cost nothing at this `q`

**`ComplexAnalytic.RefineDatumRangeCross` becomes the free half.** Its target is
`D(q b c)` inside `obj (σ b)^an`, and at `q b c = poly (σ b) (σ c)` that open **is**
`ComplexAnalytic.coverOpen obj poly (σ b) (σ c)` — which is precisely the containment
`Oka/Analytification/RefineDatumTransition.lean` and `Oka/Analytification/RefineDatumRange.lean`
prove unconditionally at each of the three shapes the condition is quantified over:
`ComplexAnalytic.range_refineDatumTransitionHom_localisationProj_subset_of_eq_ab` at
`σ a = σ b`, `..._of_eq_ac` at `σ a = σ c`, and
`ComplexAnalytic.range_refineDatumTransitionHom_localisationProj_subset` — the only one that
reads the original datum's `hrange` — where the three members are different. The fourth
combination cannot occur: `σ a = σ b` with `σ a = σ c` forces `σ b = σ c`, which the condition
excludes. **So the residue this whole line adopted as a hypothesis on the caller is, at the
caller's own `q = poly ∘ σ`, a theorem.**

**`ComplexAnalytic.RefineDatumRangeEq` becomes `D(1) = ⊤`**, which is
`ComplexAnalytic.localisationOpen_one`. Its target is `D(fam c)` transported across `σ b = σ c`,
and `ComplexAnalytic.mem_localisationOpen_transport_one` below states that transported form **at
abstract indices**, because `σ b` and `σ c` are terms and `subst` is unavailable where it is used
— the move `ComplexAnalytic.mem_localisationOpen_coverSpaceHomOfEq` makes and
`ComplexAnalytic.coverTransitionHom_of_fac_eq_ab` makes, at a third site.

## What this witness is not, and the honest reading of it

**The refining family is trivial, so nothing is refined.** Every refined member is the
localisation of its original member at `1`, which is the whole of it, so what this exhibits is the
original cover **reindexed along an arbitrary `σ`** and not a proper refinement. What it does
exhibit, and what makes it a witness rather than a degeneracy, is that the cross-member `glue`
reads the original datum's own `glue` — through `ComplexAnalytic.refineDatumCrossAlgEquiv`,
exactly once, as `ComplexAnalytic.refineDatumGlueNe` does at any input — and that the refined
overlaps are the original overlaps, so nothing here is empty unless the original cover's overlaps
are. At `fam` constantly `0` every overlap is empty; this is the opposite extreme and it is named
rather than left for a reader to notice.

## What is not here

* **No witness at a refining family that is not a unit *here*, and the diagnosis this bullet gave
  was wrong.** It ended *"the one condition that would not come free is `RefineDatumRangeEq`, which
  asks the transition's image to land in `D(fam c)` and has no free half at any file on this
  line"*. Every clause of that is true of the condition and none of it is what blocks a proper
  refinement: `ComplexAnalytic.RefineDatumRangeEq` is quantified over triples with `b ≠ c` **and**
  `σ b = σ c`, so an injective `σ` admits none and
  `ComplexAnalytic.refineDatumRangeEq_of_injective`
  (`Oka/Analytification/RefineDatumUnitFamily.lean`) closes it in one line at every refining
  family. That file also generalises `ComplexAnalytic.refineDatumOneRangeCross` below off
  `fam ≡ 1`.
  **What stays open is what `ComplexAnalytic.exists_refineDatumCross_of_isUnit` asks of the
  family** — `fam a` a unit in the localisation at `f_{σa σb}`, which is the geometric statement
  that the refined member contains the whole overlap — since that is a hypothesis there and no
  file discharges it; and **nothing here builds any of it.**
* **Nothing about `ComplexAnalytic.exists_refineDatumCross`.** Whether the `q` it produces
  satisfies either condition is untouched here in both directions, and the associate question
  `Oka/Analytification/CrossMemberGlue.lean` records is not narrowed.
* **Nothing about whether the refined overlap is the geometric one**, which is the same file's
  other absence and is about the construction rather than about any input to it.
* **No scheme, no `admissible`, and no comparison functor**, as in the files this one sits beside.

## Main definitions

- `ComplexAnalytic.refineDatumOneR` and `ComplexAnalytic.refineDatumOneU`: **the caller's `r` and
  `u` at the trivial refining family**, chosen from the criterion above.
- `ComplexAnalytic.refineDatumOneGlueData` and `ComplexAnalytic.refineDatumOneAnalytification`:
  **the glue data and the analytic space this witness produces**, taking the original datum's
  three laws and nothing else.

## Main results

- `ComplexAnalytic.mem_localisationOpen_transport_one`: **every point lies in `D(1)`, in the
  transported form the range condition asks for**, at abstract indices.
- `ComplexAnalytic.refineDatumOneRangeCross` and `ComplexAnalytic.refineDatumOneRangeEq`: **the
  two adopted conditions, discharged** — the first from the original datum's `hrange` and the two
  free halves, the second from `D(1) = ⊤`.
- `ComplexAnalytic.not_isConstant_id`: **the identity is not a constant map on a type with two
  elements**, which is what makes the witness one at a non-constant `σ`.
-/

open MvPolynomial CategoryTheory AlgebraicGeometry

universe u

namespace ComplexAnalytic

noncomputable section

variable {J B : Type u} (obj : J → Presentation.{u})

/-! ### The whole space, transported -/

/-- **Every point lies in `D(1)`, read across an equality of two members.**

`ComplexAnalytic.localisationOpen_one` is the untransported statement.

**Stated at abstract `i` and `j` because that is what makes `subst` available**: at the call site
the equality is between `σ b` and `σ c`, which are terms and not variables, and neither a `rw` of
the untransported form nor a `simp` reaches inside the `▸`. This is the move
`ComplexAnalytic.mem_localisationOpen_coverSpaceHomOfEq` records for the same reason.

**And it is a membership rather than an equality of opens on purpose.** The equality form is the
more natural statement, but discharging the range condition with it needs a `simp only` at a goal
mentioning `ComplexAnalytic.refineDatumGlue` — a definition with proof arguments — and that plants
a `congr_simp` companion for it into this module. Measured: `Δdump` was `+14` for thirteen
declarations and the extra row was `ComplexAnalytic.refineDatumGlue.congr_simp`, on
`Oka/Analytification/CrossMemberDatumGlue.lean`'s definition. In the membership form the condition
closes by `exact` and no tactic traverses the goal. That is
`Oka/Analytification/RefineDatumRange.lean`'s recorded hazard at a further site, by its own
`simp only` route. -/
theorem mem_localisationOpen_transport_one {i j : J} (h : i = j)
    (y : AnalyticSpace.analytification.{u} (obj i).g) :
    y ∈ localisationOpen.{u} (obj i).g
      (h ▸ (1 : MvPolynomial (ULift.{u} (Fin (obj j).n)) ℂ)) := by
  subst h
  rw [localisationOpen_one.{u}]
  trivial

variable (poly : ∀ i : J, J → MvPolynomial (ULift.{u} (Fin (obj i).n)) ℂ)
  (σ : B → J)
  (glue : ∀ i j : J, coverOverlap.{u} obj poly i j ≅ coverOverlap.{u} obj poly j i)

/-! ### The choice, at the trivial refining family -/

/-- **Both equations have a solution at every ordered pair**, for the refinement whose family is
constantly `1` and whose cutting polynomial is the original datum's own.

`ComplexAnalytic.exists_refineDatumCross_of_isUnit` at four units: two of them are
`ComplexAnalytic.isUnit_mk_rename_localisationIncl` — the polynomial inverted in the algebra is a
unit there — and two are `1`. **No hypothesis on the pair**, so the two families below are total
and the two laws are proved without the `σ a ≠ σ b` the datum only asks them at. -/
theorem exists_refineDatumCross_one (a b : B) :
    ∃ (r : MvPolynomial (ULift.{u} (Fin ((obj (σ b)).n + 1))) ℂ)
      (u : (PresentedAlgebra.{u} ((obj (σ b)).n + 1) ((obj (σ b)).k + 1)
        (localisationPresentation.{u} (obj (σ b)).g (poly (σ b) (σ a))))ˣ),
      RefineDatumCrossEq.{u} obj σ (fun _ ↦ 1) poly (fun x y ↦ poly (σ x) (σ y)) glue a b r ∧
        RefineDatumCrossUnit.{u} obj σ (fun _ ↦ 1) poly (fun x y ↦ poly (σ x) (σ y)) a b r u := by
  refine exists_refineDatumCross_of_isUnit.{u} obj σ (fun _ ↦ 1) poly
    (fun x y ↦ poly (σ x) (σ y)) glue a b
    (isUnit_mk_rename_localisationIncl.{u} (obj (σ a)).g (poly (σ a) (σ b))) ?_
    (isUnit_mk_rename_localisationIncl.{u} (obj (σ b)).g (poly (σ b) (σ a))) ?_ <;>
  · rw [map_one, map_one]
    exact isUnit_one

/-- **The caller's `r` at the trivial refining family**, at every ordered pair. -/
def refineDatumOneR (a b : B) : MvPolynomial (ULift.{u} (Fin ((obj (σ b)).n + 1))) ℂ :=
  (exists_refineDatumCross_one.{u} obj poly σ glue a b).choose

/-- **The caller's unit at the trivial refining family**, at every ordered pair. -/
def refineDatumOneU (a b : B) : (PresentedAlgebra.{u} ((obj (σ b)).n + 1) ((obj (σ b)).k + 1)
    (localisationPresentation.{u} (obj (σ b)).g (poly (σ b) (σ a))))ˣ :=
  (exists_refineDatumCross_one.{u} obj poly σ glue a b).choose_spec.choose

/-- **The first equation, at every ordered pair.** The `σ a ≠ σ b` a refined datum asks it at is
taken and discarded, since the choice above is made without it. -/
theorem refineDatumOneCrossEq (a b : B) (_h : σ a ≠ σ b) :
    RefineDatumCrossEq.{u} obj σ (fun _ ↦ 1) poly (fun x y ↦ poly (σ x) (σ y)) glue a b
      (refineDatumOneR.{u} obj poly σ glue a b) :=
  (exists_refineDatumCross_one.{u} obj poly σ glue a b).choose_spec.choose_spec.1

/-- **The second equation, at every ordered pair**, and the same remark. -/
theorem refineDatumOneCrossUnit (a b : B) (_h : σ a ≠ σ b) :
    RefineDatumCrossUnit.{u} obj σ (fun _ ↦ 1) poly (fun x y ↦ poly (σ x) (σ y)) a b
      (refineDatumOneR.{u} obj poly σ glue a b) (refineDatumOneU.{u} obj poly σ glue a b) :=
  (exists_refineDatumCross_one.{u} obj poly σ glue a b).choose_spec.choose_spec.2

/-! ### The two adopted conditions, discharged -/

/-- **The second adopted condition holds, and it is `D(1) = ⊤`.**

`ComplexAnalytic.RefineDatumRangeEq` asks the transition's image to land in `D(fam c)` read on the
member `σ b = σ c`; at a family constantly `1` that open is the whole space and there is nothing
left. **This is the condition with no free half**, so it is the one the trivial family is doing
the work for: at any other family it is a statement about where the original cover's transition
goes, and no file on this line proves one **at a `σ` that collapses two indices**. At an injective
`σ` it has no triple to speak about at all, which is
`ComplexAnalytic.refineDatumRangeEq_of_injective`
(`Oka/Analytification/RefineDatumUnitFamily.lean`) and holds at every family — so what `fam ≡ 1`
buys here is exactly the collapsing case. -/
theorem refineDatumOneRangeEq :
    RefineDatumRangeEq.{u} obj poly σ (fun _ ↦ 1) (fun x y ↦ poly (σ x) (σ y)) glue
      (refineDatumOneR.{u} obj poly σ glue) (refineDatumOneU.{u} obj poly σ glue)
      (refineDatumOneCrossEq.{u} obj poly σ glue)
      (refineDatumOneCrossUnit.{u} obj poly σ glue) :=
  fun _ _ _ _ _ _ _ hbc _ _ ↦ mem_localisationOpen_transport_one.{u} obj hbc _

/-- **The first adopted condition holds, and at this `q` it is the free half.**

`ComplexAnalytic.RefineDatumRangeCross`'s target is `D(q b c)`, and at
`q b c = poly (σ b) (σ c)` that is `ComplexAnalytic.coverOpen obj poly (σ b) (σ c)` — the open the
three unconditional statements land in. The split is on `σ a` against `σ b` and `σ c`, and the
fourth branch is absent because `σ a = σ b` and `σ a = σ c` force the `σ b = σ c` the condition
excludes.

**Only the third branch reads the original datum's `hrange`**, which is what
`Oka/Analytification/RefineDatumRange.lean` found and is why this proof has three cases rather
than one. -/
theorem refineDatumOneRangeCross
    (hrange : ∀ i j k : J, i ≠ j → i ≠ k → j ≠ k →
      Set.range (coverTripleIncl.{u} obj poly i j k ≫
          coverTransitionHom.{u} obj poly glue i j).base ⊆
        (coverOpen.{u} obj poly j k : Set (coverSpace.{u} obj j))) :
    RefineDatumRangeCross.{u} obj poly σ (fun _ ↦ 1) (fun x y ↦ poly (σ x) (σ y)) glue
      (refineDatumOneR.{u} obj poly σ glue) (refineDatumOneU.{u} obj poly σ glue)
      (refineDatumOneCrossEq.{u} obj poly σ glue)
      (refineDatumOneCrossUnit.{u} obj poly σ glue) := by
  intro a b c _ _ _ hbc
  by_cases hab : σ a = σ b
  · exact range_refineDatumTransitionHom_localisationProj_subset_of_eq_ab.{u} obj poly σ
      (fun _ ↦ 1) (fun x y ↦ poly (σ x) (σ y)) glue (refineDatumOneR.{u} obj poly σ glue)
      (refineDatumOneU.{u} obj poly σ glue) (refineDatumOneCrossEq.{u} obj poly σ glue)
      (refineDatumOneCrossUnit.{u} obj poly σ glue) hab fun e ↦ hbc (hab ▸ e)
  · by_cases hac : σ a = σ c
    · exact range_refineDatumTransitionHom_localisationProj_subset_of_eq_ac.{u} obj poly σ
        (fun _ ↦ 1) (fun x y ↦ poly (σ x) (σ y)) glue (refineDatumOneR.{u} obj poly σ glue)
        (refineDatumOneU.{u} obj poly σ glue) (refineDatumOneCrossEq.{u} obj poly σ glue)
        (refineDatumOneCrossUnit.{u} obj poly σ glue) hab hac
    · exact range_refineDatumTransitionHom_localisationProj_subset.{u} obj poly σ (fun _ ↦ 1)
        (fun x y ↦ poly (σ x) (σ y)) glue (refineDatumOneR.{u} obj poly σ glue)
        (refineDatumOneU.{u} obj poly σ glue) hrange (refineDatumOneCrossEq.{u} obj poly σ glue)
        (refineDatumOneCrossUnit.{u} obj poly σ glue) hab hac hbc

/-! ### The glue data and the space -/

variable (hsym : ∀ i j : J, glue j i = (glue i j).symm)
  (hrange : ∀ i j k : J, i ≠ j → i ≠ k → j ≠ k →
    Set.range (coverTripleIncl.{u} obj poly i j k ≫
        coverTransitionHom.{u} obj poly glue i j).base ⊆
      (coverOpen.{u} obj poly j k : Set (coverSpace.{u} obj j)))

/-- **The glue data of a cross-member refined cover datum, for every cover datum and every index
map**, and it asks for the original datum's three laws and nothing else.

`ComplexAnalytic.refineDatumGlueDataOfLaws` at the trivial refining family, with both adopted
conditions discharged above. -/
def refineDatumOneGlueData
    (hcocycle : ∀ i j k : J, ∀ hij : i ≠ j, ∀ hik : i ≠ k, ∀ hjk : j ≠ k,
      coverTriple.{u} obj poly glue hrange i j k hij hik hjk ≫
        coverTriple.{u} obj poly glue hrange j k i hjk hij.symm hik.symm ≫
          coverTriple.{u} obj poly glue hrange k i j hik.symm hjk.symm hij = 𝟙 _) :
    LocallyRingedSpace.GlueData.{u} :=
  refineDatumGlueDataOfLaws.{u} obj poly σ (fun _ ↦ 1) (fun x y ↦ poly (σ x) (σ y)) glue
    (refineDatumOneR.{u} obj poly σ glue) (refineDatumOneU.{u} obj poly σ glue)
    (refineDatumOneCrossEq.{u} obj poly σ glue) (refineDatumOneCrossUnit.{u} obj poly σ glue)
    hrange (refineDatumOneRangeCross.{u} obj poly σ glue hrange)
    (refineDatumOneRangeEq.{u} obj poly σ glue) hsym hcocycle

/-- **The analytic space that datum glues to**, and this is the object the absence five files
record says does not exist.

`ComplexAnalytic.refineDatumAnalytificationOfLaws` at the same arguments. **`σ` is arbitrary**, so
taking `B = J` and `σ = id` on a type with two elements gives one at a `σ` that is not constant —
which is `ComplexAnalytic.not_isConstant_id`. -/
def refineDatumOneAnalytification
    (hcocycle : ∀ i j k : J, ∀ hij : i ≠ j, ∀ hik : i ≠ k, ∀ hjk : j ≠ k,
      coverTriple.{u} obj poly glue hrange i j k hij hik hjk ≫
        coverTriple.{u} obj poly glue hrange j k i hjk hij.symm hik.symm ≫
          coverTriple.{u} obj poly glue hrange k i j hik.symm hjk.symm hij = 𝟙 _) :
    AnalyticSpace.{u} :=
  refineDatumAnalytificationOfLaws.{u} obj poly σ (fun _ ↦ 1) (fun x y ↦ poly (σ x) (σ y)) glue
    (refineDatumOneR.{u} obj poly σ glue) (refineDatumOneU.{u} obj poly σ glue)
    (refineDatumOneCrossEq.{u} obj poly σ glue) (refineDatumOneCrossUnit.{u} obj poly σ glue)
    hrange (refineDatumOneRangeCross.{u} obj poly σ glue hrange)
    (refineDatumOneRangeEq.{u} obj poly σ glue) hsym hcocycle

end

/-! ### And the index map may be non-constant -/

/-- **The identity is not a constant map on a type with two elements.**

Everything above is at an arbitrary `σ`, so what makes it a witness *at a non-constant `σ`* is
this and nothing else. It is stated rather than left to the reader because the absence it retires
is worded about `σ` and not about the construction: five files say there is no example **at a
non-constant `σ`**, and an arbitrary `σ` includes the constant ones. -/
theorem not_isConstant_id {J : Type u} [Nontrivial J] : ¬ ∃ j : J, ∀ b : J, (id : J → J) b = j := by
  rintro ⟨j, hj⟩
  obtain ⟨x, y, hxy⟩ := exists_pair_ne J
  exact hxy ((hj x).trans (hj y).symm)

end ComplexAnalytic
