/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.AnalyticSpace.SeparatedDirectSummand
import Oka.AnalyticSpace.SeparatedFiberFunctorCoproducts
import Oka.AnalyticSpace.SeparatedFiberFunctorEpi
import Oka.AnalyticSpace.SeparatedFiberPullback
import Oka.AnalyticSpace.SeparatedFiberQuotient
import Mathlib.CategoryTheory.Galois.Basic

/-!
# The covers separated over a Hausdorff base form a Galois category

`Mathlib/CategoryTheory/Galois/Basic.lean` asks eleven things across two classes:
`CategoryTheory.PreGaloisCategory` has five fields and
`CategoryTheory.PreGaloisCategory.FiberFunctor` has six. **Every one of the eleven has had a
statement at `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver` since the commit before this
one, in ten modules under `Oka/AnalyticSpace/`, and none of them could say so**: until this file
that namespace was outside this repository's import closure, so no module could name either class.
**This file is the import and the two instances, and it is nothing else.**

## This is the file that retires *cannot be cited by name here*

That clause — in the spellings *whose namespace is not in this repository's import closure*, *that
namespace is not in this repository's import closure* and *cannot be cited by name here* — stood in
this tree from the first module of the ladder. **It was exact at every commit that wrote it and
this push is what falsifies it**, so this push repairs every live instance of it rather than
leaving the sweep to whoever edits each file next, and each repair carries a dated record where the
clause it replaces was not already pinned to a commit.

**The class can now be cited by name from any module downstream of this one, and only from there.**
A module that does not import this one still cannot name either class, which is why the repaired
clauses say *this file's import closure* where that is what they are about and *this repository's*
only where they were.

**A second class of sentence is retired by the same push and no scan keyed on that clause can see
it.** *This repository has no `PreGaloisCategory` instance* is a claim about **existence** and not
about citability; it stands in different files, in different words, and a sweep over the
import-closure wording passes straight over it. The sentences of that class which carried no date
are in `Oka/AnalyticSpace/FiniteEtaleOver.lean`, `Oka/AnalyticSpace/SeparatedDirectSummand.lean`,
`Oka/AnalyticSpace/SeparatedFiberFunctor.lean`,
`Oka/AnalyticSpace/SeparatedFiberFunctorEpi.lean`,
`Oka/AnalyticSpace/SeparatedFiniteEtaleLimits.lean`, `OkaTest/Axioms.lean` and
`OkaTest/Axioms/Morphisms.lean`, and each is rewritten at its commit here. **Every other sentence
of that class in the tree already carries a commit or a hash beside it and stays exact**, and
those seven are where the argument for writing a census *at* a commit rather than in the present
tense had not been taken. **The enumeration is a scan and not a memory, and it took two widenings
to become one.** A scan keyed on a repository-wide quantifier and on either class name written
out returns **five**, and the two it cannot see are the two ways a sentence of this class hides:
`Oka/AnalyticSpace/SeparatedFiniteEtaleLimits.lean` quantifies as *no module reachable from
`Oka.lean`* and over *the whole tree* rather than over this repository, and
`Oka/AnalyticSpace/SeparatedDirectSummand.lean` names the class anaphorically, as *that class*, in
a declaration docstring rather than in a `## What is not here` bullet. **So the rule this section
states holds one level out from where it was first applied**: a sweep keyed on the spelling of the
quantifier, or on the class being named at all, passes over the claim spelled another way. Over
every tracked `.lean` under `Oka/` and `OkaTest/`, whitespace-flattened because such a sentence
wraps, the sentences pairing any tree-wide quantifier with either class — named or referred to —
and carrying neither a date nor a commit beside them are those seven and no others. **And the
census behind them is the tree and not a wording**: `PreGaloisCategory` occurs in the
comment-stripped code of **no** module of this repository at the commit this file is cut from and
of **two** at the commit that adds it,
this one and `OkaTest/GaloisCategory.lean`, with `scripts/import_cost.py`'s `strip_comments` the
instrument.

## What the import costs, measured in the environment and not by a scan

**At the commit this file is cut from**, `import Oka` brings **5508** modules and `import Oka`
together with `import Mathlib.CategoryTheory.Galois.Basic` brings **5510**: **the cost is two**,
and the two are `Mathlib.CategoryTheory.Galois.Basic` itself and
`Mathlib.CategoryTheory.Limits.FintypeCat` — named rather than counted, by a set difference over
`Lean.Environment.allImportedModuleNames` in a `run_cmd`, which is exact where a transitive walk of
`import` lines is an estimate.

**At the commit that adds this file the same pair of runs gives 5511 and 5511, and the cost is
zero**, this file having paid it: 5508 plus the two plus this module. **A marginal import cost is a
figure about the importer at a commit and is meaningless without one**, which is why both are
dated here and neither is written in the present tense.

**That figure is a statement about this repository's closure and not about Mathlib's file**, so it
falls whenever the closure grows: taxis #2027's filing priced it at **five** at `fbe1e95`, and
three of those five — `Mathlib.CategoryTheory.SingleObj`, `Mathlib.Combinatorics.Quiver.Cast` and
`Mathlib.Combinatorics.Quiver.SingleObj` — were paid for in the meantime by the push that gave the
category colimits of shape `CategoryTheory.SingleObj G`.

## The five `Oka` imports are each load-bearing, and withholding one names the field it carries

Each of the five imports above was removed on its own and the file re-elaborated. **All five fail,
and the failure names the obligation**:

* `Oka/AnalyticSpace/SeparatedDirectSummand.lean` — the name
  `…SeparatedFiniteEtaleOver.inducesIsoOnDirectSummand_of_mono'` becomes an unknown identifier,
  which is the `monoInducesIsoOnDirectSummand` field.
* `Oka/AnalyticSpace/SeparatedFiberPullback.lean` — the `hasPullbacks` **and** the
  `preservesPullbacks` field, two of the eleven from one import.
* `Oka/AnalyticSpace/SeparatedFiberQuotient.lean` — the `hasQuotientsByFiniteGroups` **and** the
  `preservesQuotientsByFiniteGroups` field, the other import that carries two.
* `Oka/AnalyticSpace/SeparatedFiberFunctorCoproducts.lean` — the `preservesFiniteCoproducts` field.
* `Oka/AnalyticSpace/SeparatedFiberFunctorEpi.lean` — the `preservesEpis` field.

**So the withholding instrument attributes seven of the eleven obligations to a unique import and
four of them to none**: `hasTerminal`, `hasFiniteCoproducts`, `preservesTerminalObjects` and
`reflectsIsos` are reachable through more than one of the five, so no single withholding is a
statement about them. **That is a fact about the import graph and not about the proofs**, and it is
why this file names five modules where the eleven statements live in ten: what a withholding
reports is the field an import makes reachable and not the module the statement is written in.

## Three fields are written and eight are found by search

`hasQuotientsByFiniteGroups` and `preservesQuotientsByFiniteGroups` are written as
`inferInstance` at the group rather than left to the class's `by infer_instance` default. **That is
not a failure of search**: those two fields take `(G : Type u₂) [Group G] [Finite G]` as their own
binders, so the default tactic is run against the whole `∀`-type rather than against the
instance goal underneath it, and `infer_instance` cannot see a class there. With the group bound,
search finds both.

`monoInducesIsoOnDirectSummand` is written because it is not a class and never could be found:
it is an existential statement, and
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.inducesIsoOnDirectSummand_of_mono'` is it
in the field's own shape, character for character. **The other eight fields are discharged by the
class's own defaults**, which is what the five modules were written to make true.

## The hypotheses, and why the second instance carries one more

`CategoryTheory.PreGaloisCategory` is stated over `[T2Space X]` alone. The `FiberFunctor` instance
carries `[PreconnectedSpace X]` as well, and **it is the `reflectsIsos` field that spends it and
nothing else**: conservativity goes through
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.isIso_of_bijective_fiberMap`, which reads
bijectivity at **one** point of the base and concludes an isomorphism, and that step is false over a
base with two components. **So this is a hypothesis of the mathematics and not of the placement** —
the distinction `Oka/AnalyticSpace/SeparatedFiberFunctor.lean` records for its own pair.

**Neither hypothesis is one either Mathlib class asks**, and this is where this repository's
Hausdorff assumption lives; `Oka/AnalyticSpace/SeparatedFiniteEtale.lean` says so of the category
and `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.t2Space_left` is where the first is
spent.

## Main results

- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.preGaloisCategory`: **the covers
  separated over a Hausdorff analytic space form a `CategoryTheory.PreGaloisCategory`.**
- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.fintypeFiberFunctor_isFiberFunctor`:
  **the `FintypeCat`-valued fibre functor at a point of a preconnected Hausdorff base is a
  `CategoryTheory.PreGaloisCategory.FiberFunctor`.**

## What is not here

* **No `CategoryTheory.GaloisCategory` instance**, and the reason is a hypothesis and not a proof.
  That class asks for a fibre functor to **exist**, and every fibre functor this repository has is
  taken at a point of the base, so the instance needs `[Nonempty X]` — which neither of the two
  above needs and which nothing else in this neighbourhood carries. **The price is one line beyond
  that hypothesis and it is compiled**: the field
  `hasFiberFunctor := ⟨…fintypeFiberFunctor x, ⟨inferInstance⟩⟩`
  elaborates at a given `x`, and `#synth` for the class fails at the commit that adds this file,
  which the control file records. **Adding a hypothesis to reach a class is a decision and not a
  step**, and it is left to the filing that wants the class rather than taken here.
* **Nothing at `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver`.** The ambient covers are not
  separated and the `monoInducesIsoOnDirectSummand` field is stated at the separated category, so
  `#synth` for `CategoryTheory.PreGaloisCategory` there fails at the commit that adds this file and
  the control file records that too. **No statement of this file is transported to the covers and
  none could be.**
* **No limit or colimit that was not already there.** The class's own downstream instances —
  `CategoryTheory.Limits.HasFiniteLimits`, `CategoryTheory.Limits.HasInitial` and
  `CategoryTheory.Limits.HasEqualizers` at this category — are all found by search **at the base of
  this push as well**, three runs of mine in a checkout without this file, so declaring the class
  buys none of them. `CategoryTheory.Limits.HasFiniteColimits` is **not** found at either end, and
  this push does not touch it.
* **One thing the class does buy, and it is named rather than gestured at**:
  `(…SeparatedFiniteEtaleOver.fintypeFiberFunctor x).ReflectsMonomorphisms` is not synthesizable at
  the base **even in a file that imports `Mathlib.CategoryTheory.Galois.Basic` directly**, and is
  synthesizable here. The control file carries both halves of that.
* **Nothing about the Riemann Existence Theorem and nothing about an equivalence.** The two
  instances are the statement that this category with this functor is a Galois category; the
  comparison functor is taxis #1113 and the equivalence is taxis #1115, and neither is narrowed by
  anything below.
-/

open CategoryTheory

universe u

namespace ComplexAnalytic.AnalyticSpace

variable {X : AnalyticSpace.{u}} [T2Space (X : Type u)]

/-- **The covers separated over a Hausdorff analytic space form a
`CategoryTheory.PreGaloisCategory`**, which is the first of that file's two classes and the one the
fibre functor's class is stated over.

Three of the five fields are the class's own `by infer_instance` default, at
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.hasTerminal`,
`…SeparatedFiniteEtaleOver.hasPullbacks` and `…SeparatedFiniteEtaleOver.hasFiniteCoproducts`.

`hasQuotientsByFiniteGroups` is written out because the field binds the group itself, so the
default tactic meets a `∀` rather than a class; with `G` bound, search finds
`…SeparatedFiniteEtaleOver.hasColimitsOfShape_singleObj` and the universe of `G` is unconstrained
there, so it covers the field's `u₂` whatever the hom universe of this category is.

`monoInducesIsoOnDirectSummand` is not a class and is supplied by name. -/
instance SeparatedFiniteEtaleOver.preGaloisCategory :
    PreGaloisCategory (SeparatedFiniteEtaleOver.{u} X) where
  hasQuotientsByFiniteGroups G := inferInstance
  monoInducesIsoOnDirectSummand i :=
    SeparatedFiniteEtaleOver.inducesIsoOnDirectSummand_of_mono' i

variable [PreconnectedSpace (X : Type u)]

/-- **The `FintypeCat`-valued fibre functor at a point is a
`CategoryTheory.PreGaloisCategory.FiberFunctor`**, which is the second of that file's two classes
and the reason the fibre functor is `FintypeCat`-valued at all.

Five of the six fields are the class's own default, at
`…SeparatedFiniteEtaleOver.preservesTerminal_fintypeFiberFunctor`,
`…SeparatedFiniteEtaleOver.preservesPullbacks_fintypeFiberFunctor`,
`…SeparatedFiniteEtaleOver.preservesFiniteCoproducts_fintypeFiber`,
`…SeparatedFiniteEtaleOver.preservesEpimorphisms_fintypeFiberFunctor` and
`…SeparatedFiniteEtaleOver.reflectsIsos_fintypeFiberFunctor`. The sixth is written out for the
reason the instance above gives of its own quotient field.

**`[PreconnectedSpace X]` is spent by the fifth of those and by nothing else here**, for the reason
the module docstring gives. -/
instance SeparatedFiniteEtaleOver.fintypeFiberFunctor_isFiberFunctor (x : X) :
    PreGaloisCategory.FiberFunctor (SeparatedFiniteEtaleOver.fintypeFiberFunctor.{u} x) where
  preservesQuotientsByFiniteGroups G := inferInstance

end ComplexAnalytic.AnalyticSpace
