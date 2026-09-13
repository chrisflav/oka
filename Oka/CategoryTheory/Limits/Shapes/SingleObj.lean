/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
module

public import Mathlib.Algebra.Group.TransferInstance
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
public import Mathlib.CategoryTheory.SingleObj

/-!
# Colimits of shape `CategoryTheory.SingleObj G` in a category with finite colimits

Material for `Mathlib/CategoryTheory/Limits/Shapes/SingleObj.lean`; see `README.md` on the mirror
tree. **That file exists at the pinned Mathlib revision** — it characterises limits and colimits
of this shape in the category of types, and says in terms that types are all it covers — so the
mirror path names a target to add to and not a proposed new file, and `scripts/import_cost.py`
prices the addition at **33** modules against that target's closure of **519**. **Nothing declared
in this repository occurs below**, and the statement would make sense to a reader who had never
heard of Oka's theorem.

A functor out of `CategoryTheory.SingleObj G` for a group `G` is a group acting on one object by
automorphisms, and its colimit is the quotient by that action. This file says that **a category
with finite colimits has such a colimit for every finite group, at every universe**.

## What Mathlib already answers, and the two places it stops

`CategoryTheory.Limits.hasColimitsOfShape_of_hasFiniteColimits` is an instance giving
`CategoryTheory.Limits.HasColimitsOfShape J C` from `CategoryTheory.Limits.HasFiniteColimits C`
for **any** `J` that is a `CategoryTheory.SmallCategory` and a `CategoryTheory.FinCategory`, at an
arbitrary universe for `J`. So the only question is whether `CategoryTheory.SingleObj G` is one,
and the answer has two edges. **All three probes below were run as `inferInstance` rather than
read off the declarations**, in a file importing the same three Mathlib modules this one does and
nothing else; the first succeeds and the other two are the edges:

* `G : Type` with `[Fintype G]` — search **succeeds** without this file, through
  `CategoryTheory.SingleObj.finCategoryOfFintype`;
* `G : Type` with `[Finite G]` — search **fails**, because that instance asks for `Fintype` and
  `Finite` does not supply one by search;
* `G : Type u` for a universe *variable* `u`, with `[Finite G]` — search **fails**, and this is
  the edge that is not about finiteness at all. `CategoryTheory.SingleObj G` is `Unit`, so its
  object type is in `Type`, while its hom type is `G`; `CategoryTheory.SingleObj.category` is
  therefore a `CategoryTheory.Category.{u, 0}`. A `CategoryTheory.SmallCategory` on a type in
  `Type` is a `CategoryTheory.Category.{0, 0}`, and `CategoryTheory.FinCategory` asks for one, so
  the shape is a `CategoryTheory.FinCategory` only when `G` itself is in `Type`.

**The statement below asks `[Finite G]` at an arbitrary universe**, which is the form a class
whose group ranges over the hom universe of `C` asks for. `Mathlib/CategoryTheory/Galois/Basic.lean`
has a field of exactly that shape; its namespace is not in this repository's import closure, so it
cannot be cited by name here.

## The proof, which is Mathlib's own move with the category left general

`Finite.exists_type_univ_nonempty_mulEquiv` produces a finite group `G'` in `Type` together with
`G ≃* G'`, `MulEquiv.toSingleObjEquiv` turns that isomorphism into an equivalence of the two
one-object categories, and `CategoryTheory.Limits.hasColimitsOfShape_of_equivalence` transports
the class along it; the hypothesis is discharged at `G'` by the instance named above, `G'` being in
`Type` and a `Fintype`. **Those are the same three steps Mathlib takes twice**, in
`Mathlib/CategoryTheory/Galois/Basic.lean` and in `Mathlib/CategoryTheory/Galois/Examples.lean` —
in the first under a class one of whose own fields is this very shape at the hom universe of the
category, so that the three steps there buy the universe and nothing else, and in the second at
one fixed category. **What is new here is only that the category is a variable and the
hypothesis is `CategoryTheory.Limits.HasFiniteColimits`**, so that it reads at any category whose
finite colimits are known; a search for `HasColimitsOfShape (SingleObj` over `Mathlib/` at the
pinned revision returns those two sites and the field itself, and no statement with the category
left general.

## Main results

- `CategoryTheory.Limits.hasColimitsOfShape_singleObj`: **a category with finite colimits has
  colimits of shape `CategoryTheory.SingleObj G` for every finite group `G`, at every universe**.

## What is not here

* **No colimit is constructed and no quotient is named.** This is the existence class and nothing
  below says what the colimit of such a functor is, nor that its object is a quotient of anything,
  nor anything about the action a functor out of `CategoryTheory.SingleObj G` encodes.
* **Nothing is added to `CategoryTheory.Limits.HasFiniteColimits`.** It is a hypothesis here and
  there is no converter into it below; a category has to be known to have finite colimits by some
  other route before this reads at it, and two of Mathlib's converters into that class —
  `CategoryTheory.Limits.hasFiniteColimits_of_hasCoequalizers_and_finite_coproducts` and
  `CategoryTheory.Limits.hasFiniteColimits_of_hasInitial_and_pushouts` — ask for coequalisers
  beside finite coproducts, or for an initial object and pushouts. **They are named as two routes
  and not as the routes**: that class has further converters in Mathlib, and this bullet counts
  none of them.
* **Nothing about preservation.** That a functor preserves colimits of this shape is a different
  statement and no declaration below bears on it.
* **Nothing about `Finite` versus `Fintype` in general.** The probes under *What Mathlib already
  answers* measure instance search at this one shape and are not a claim about how the two classes
  relate.
-/

@[expose] public section

universe v u w

open CategoryTheory

namespace CategoryTheory.Limits

/-- **A category with finite colimits has colimits of shape `CategoryTheory.SingleObj G` for every
finite group `G`, at every universe.**

A functor out of `CategoryTheory.SingleObj G` is a group acting on one object by automorphisms, and
this says the quotient by such an action exists whenever finite colimits do.

**The universe of `G` is unconstrained, and that is the whole of what this adds.**
`CategoryTheory.SingleObj G` is a `CategoryTheory.FinCategory` only for `G` in `Type` with a
`Fintype` instance — the module docstring measures both edges — so
`CategoryTheory.Limits.hasColimitsOfShape_of_hasFiniteColimits` does not reach this shape at a
universe variable. The proof replaces `G` by an isomorphic finite group in `Type` and transports
along the induced equivalence of one-object categories.

**An `instance` and not a `theorem`, and that was measured.** Without this declaration
`inferInstance` at this statement fails, so instance search gains something it did not have;
a consumer asking for colimits of this shape is asking by instance search and not by name. -/
instance hasColimitsOfShape_singleObj (C : Type u) [Category.{v} C] [HasFiniteColimits C]
    (G : Type w) [Group G] [Finite G] : HasColimitsOfShape (SingleObj G) C := by
  obtain ⟨G', _, _, ⟨e⟩⟩ := Finite.exists_type_univ_nonempty_mulEquiv G
  exact hasColimitsOfShape_of_equivalence e.toSingleObjEquiv.symm

end CategoryTheory.Limits
