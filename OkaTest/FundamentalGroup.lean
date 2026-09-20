/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka
import OkaTest.FiniteEtaleOver

/-!
# The fundamental group of the punctured line is not trivial

`Oka/AnalyticSpace/SimplyConnected.lean` says that a base whose fundamental group at a point is
trivial has only trivial covers, and exhibits no base whose group is trivial. **This file is the
other side of that statement and is the first computation of anything about this group in this
repository**: the punctured line has a cover that is not the base over itself, so its fundamental
group at any point is not trivial.

## The argument is the contrapositive and nothing else

`OkaTest/FiniteEtaleOver.lean`'s `sqOver` — `z ↦ z²` on the punctured line — is a connected cover
separated over a Hausdorff, preconnected, nonempty base, and
`OkaTest.FiniteEtaleOver.not_iso_id_sqOver` says it is not isomorphic to the base over itself. If
the group were trivial then
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.nonempty_iso_id` would make it so.

**What this file has to supply is that `sqOver` is an object of the *separated* category and is
connected in the categorical sense**, and only the first of those is a quotation:

* **separated** is `T2Space.isSeparatedMap` at
  `OkaTest.FiniteEtaleOver.t2Space_left_sqOver` — a map out of a Hausdorff space is separated, and
  that instance is the one that file declares because instance search does not reach `T2Space`
  through an object's `.left`. **The object condition of the separated category is a pair**, so the
  finite étaleness is `ComplexAnalytic.isFiniteEtale_sq` unchanged;
* **connected** is `…SeparatedFiniteEtaleOver.isConnected_of_connectedSpace` at a
  `ConnectedSpace` instance on the total space, and that instance is built here rather than
  quoted. The **three** instances below are the whole of it: `ConnectedSpace` at the base, from
  `ComplexAnalytic.preconnectedSpace_restrict_punctured` and the non-emptiness search already
  finds; `inferInstanceAs` carrying it across the `.left` seam, which is the only one of the three
  that crosses it; and the theorem applied. **`OkaTest/FiniteEtaleOver.lean` declares
  `PreconnectedSpace` at `sqOver.left` and no proof term below contains it** — that file
  measures the same seam for the same object, and this file reaches the same class by the other
  side of it.

## The two forgetful identities are `rfl`, which is what makes the contradiction free

`(…SeparatedFiniteEtaleOver.toFiniteEtaleOver B).obj sqSeparated` is `sqOver` and
`(…SeparatedFiniteEtaleOver.toFiniteEtaleOver B).obj (…SeparatedFiniteEtaleOver.id B)` is
`…FiniteEtaleOver.id B`, both **by `rfl`**, checked below as two `example`s. So
`CategoryTheory.Functor.mapIso` carries an isomorphism of separated covers to one of covers with no
transport and no `CategoryTheory.eqToHom`, and `OkaTest.FiniteEtaleOver.not_iso_id_sqOver` applies
to it as it stands. **Both `example`s are here because a `rfl` that a proof depends on and that
nothing states is a fact about definitional unfolding that the next change to either definition
breaks silently.**

## What this file does not say

* **Nothing about `Complex.fundamentalGroupPuncturedEquivInt`.** That is the **topologist's**
  fundamental group of `ℂ ∖ {0}` (`Oka/Analysis/Complex/FundamentalGroup.lean`), which this
  repository computes to be `ℤ`; the group below is the automorphism group of a fibre functor.
  `Oka/AnalyticSpace/FundamentalGroup.lean`'s `## What is not here` records that nothing relates
  the two, and **this file does not relate them.** That the same space now carries two
  non-triviality statements is a coincidence of the witness and not a theorem: the covering
  `z ↦ z²` is what proves the one below, and `Complex.infinite_fundamentalGroupPunctured` is proved
  from the periods of `Complex.exp`.
* **No cardinality and no degree.** The statement below is `Nontrivial` and nothing more; the
  degree of `sqOver` is `2` (`OkaTest.FiniteEtaleOver.degree_sqOver`) and no statement here reads
  it, nor does anything relate it to the order of the group.
* **Nothing about a second base, and what the witness has to be is *connected*.** Covers that are
  not the base over itself are everywhere in this repository:
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isEmpty_iso_trivial_id` gives one over **every**
  non-empty base, for every finite index type whose `Nat.card` is not `1`. **None of them is a
  witness here**, because over a base with trivial fundamental group
  `…SeparatedFiniteEtaleOver.exists_iso_coprod_id` makes a trivial cover a coproduct of copies of
  the base over itself and there is nothing to contradict; what
  `…SeparatedFiniteEtaleOver.nonempty_iso_id` asks of a cover and a trivial one does not meet is
  `CategoryTheory.PreGaloisCategory.IsConnected`, which the third instance below supplies for
  `sqSeparated`. **What the argument needs is therefore the conjunction and not either half of
  it** — a cover that is connected *and* that a statement already in this repository separates
  from the base over itself — and `sqSeparated` is where this file has both at once.
* **The neighbourhood that conjunction was chosen from, scanned and not asserted.**
  `IsEmpty (… ≅ …)` occurs **seven** times in the comment-stripped code under `Oka/` and
  `OkaTest/`: four in `Oka/AnalyticSpace/FiniteEtaleOver.lean`, universally quantified over their
  objects; `OkaTest.FiniteEtaleOver.pairwise_not_iso_trivial`, which separates two trivial covers
  of this same base from each other and not from the base; and two about `sqOver`, of which
  `OkaTest.FiniteEtaleOver.not_iso_id_sqOver` is the one whose other side is the base over itself
  and is the statement the theorem below contradicts. **Seven is a paren scan and six is a line
  scan**: `pairwise_not_iso_trivial` wraps its `≅` onto the line after its `IsEmpty (`, so a
  `grep` anchored on one line cannot see it and reports it as absent, which is what taxis #1712
  records of `git log -S`. `≇` and `¬ Nonempty (… ≅ …)` occur **0** times, so the spelling is
  the whole population as well as the count.
-/

open CategoryTheory CategoryTheory.Limits ComplexAnalytic ComplexAnalytic.AnalyticSpace
open scoped FintypeCatDiscrete

universe u

noncomputable section

namespace OkaTest.FundamentalGroup

/-- **The punctured line**, `ℂ¹` restricted to `ComplexAnalytic.punctured`, which is the base
`OkaTest/FiniteEtaleOver.lean`'s `sqOver` is a cover of. It is written here as an abbreviation
because the spelling is four tokens long and nine uses of it stand below, in six of the seven
declarations that follow. -/
abbrev puncturedLine : AnalyticSpace.{u} :=
  (AnalyticSpace.complexAffineSpace.{u} 1).restrict ComplexAnalytic.punctured.{u}

/-- **`z ↦ z²` on the punctured line, as an object of the category of covers *separated* over it.**

The object condition is a pair: `ComplexAnalytic.isFiniteEtale_sq` and separatedness of the base
map, the latter `T2Space.isSeparatedMap` at `OkaTest.FiniteEtaleOver.t2Space_left_sqOver`, since a
map out of a Hausdorff space is separated whatever the map is. **`OkaTest.FiniteEtaleOver.sqOver`
is this object's image under the forgetful functor by `rfl`**, which the first `example` below
records. -/
def sqSeparated : AnalyticSpace.SeparatedFiniteEtaleOver.{u} puncturedLine.{u} :=
  MorphismProperty.Over.mk _ ComplexAnalytic.sq.{u}
    ⟨ComplexAnalytic.isFiniteEtale_sq.{u},
      T2Space.isSeparatedMap (X := (OkaTest.FiniteEtaleOver.sqOver.{u}.left : Type u)) _⟩

example : (AnalyticSpace.SeparatedFiniteEtaleOver.toFiniteEtaleOver.{u}
    puncturedLine.{u}).obj sqSeparated.{u} = OkaTest.FiniteEtaleOver.sqOver.{u} := rfl

example : (AnalyticSpace.SeparatedFiniteEtaleOver.toFiniteEtaleOver.{u} puncturedLine.{u}).obj
    (AnalyticSpace.SeparatedFiniteEtaleOver.id.{u} puncturedLine.{u}) =
      AnalyticSpace.FiniteEtaleOver.id.{u} puncturedLine.{u} := rfl

/-- **The punctured line is connected**, as `ConnectedSpace` and not only as `PreconnectedSpace`.

`ComplexAnalytic.preconnectedSpace_restrict_punctured` and the non-emptiness instance search
already finds; it is declared because `ConnectedSpace` is the class
`…SeparatedFiniteEtaleOver.isConnected_of_connectedSpace` asks for and nothing in this repository
states it of this space. -/
instance connectedSpace_puncturedLine : ConnectedSpace (puncturedLine.{u} : Type u) :=
  ⟨inferInstance⟩

/-- **And so is the total space of `sqSeparated`**, which is the same space.

`inferInstanceAs` at the instance above: the total space of this object is the punctured line by
`rfl` and not reducibly so, which is the seam `OkaTest/FiniteEtaleOver.lean` measures for
`T2Space` and `PreconnectedSpace` at `sqOver.left` and documents there at length. Nothing is
proved here. -/
instance connectedSpace_left_sqSeparated :
    ConnectedSpace ((sqSeparated.{u}).left : Type u) :=
  inferInstanceAs (ConnectedSpace (puncturedLine.{u} : Type u))

/-- **`sqSeparated` is connected as an object of the category**, which is
`CategoryTheory.PreGaloisCategory.IsConnected` and not a condition on a space.

`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.isConnected_of_connectedSpace` at the
instance above. **That theorem is the direction of taxis #2082's equivalence that needs no
hypothesis on the base beyond the section's**, and it is what makes the categorical condition
reachable from a topological one at a concrete object. -/
instance isConnected_sqSeparated : PreGaloisCategory.IsConnected sqSeparated.{u} :=
  AnalyticSpace.SeparatedFiniteEtaleOver.isConnected_of_connectedSpace.{u} sqSeparated.{u}

/-- **The fundamental group of the punctured line is not trivial**, at every point of it.

The contrapositive of
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.nonempty_iso_id`: a trivial group would
make the connected cover `sqSeparated` isomorphic to the base over itself, and
`OkaTest.FiniteEtaleOver.not_iso_id_sqOver` says its image under the forgetful functor is not.
`Nontrivial` rather than `¬ Subsingleton` because the two are equivalent for a type with a point
and the positive form is what a consumer would state.

**This says nothing about which group it is.** It is not related below to
`Complex.fundamentalGroupPuncturedEquivInt`, the topologist's group of the same space, and the
module docstring says why that is not an omission to be repaired in passing. -/
theorem nontrivial_fundamentalGroup (x : puncturedLine.{u}) :
    Nontrivial (AnalyticSpace.SeparatedFiniteEtaleOver.fundamentalGroup.{u} x) := by
  rw [← not_subsingleton_iff_nontrivial]
  intro _
  obtain ⟨e⟩ := AnalyticSpace.SeparatedFiniteEtaleOver.nonempty_iso_id.{u} x sqSeparated.{u}
  exact OkaTest.FiniteEtaleOver.not_iso_id_sqOver.{u}.elim
    ((AnalyticSpace.SeparatedFiniteEtaleOver.toFiniteEtaleOver.{u} puncturedLine.{u}).mapIso e)

end OkaTest.FundamentalGroup
