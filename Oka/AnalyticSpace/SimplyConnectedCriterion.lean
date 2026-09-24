/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.AnalyticSpace.SimplyConnected

/-!
# A trivial fundamental group is a property of the base and not of the point

`Oka/AnalyticSpace/SimplyConnected.lean` proves that a connected cover separated over a base whose
fundamental group **at a named point** is trivial is the base over itself
(`…SeparatedFiniteEtaleOver.nonempty_iso_id`). **This file is that implication run backwards.**
Together the two make the triviality of the group a *criterion*: it holds exactly when every
connected cover separated over the base is isomorphic to the base over itself. The right-hand side
of that criterion names no point, so the left-hand side cannot depend on which point is named, and
the two transports at the end of this file are what that observation is worth.

## What the previous module leaves, and the census is a scan rather than a memory

At the commit this file is cut from, `…SeparatedFiniteEtaleOver.nonempty_iso_id` and
`…SeparatedFiniteEtaleOver.exists_iso_coprod_id` occur in the comment-stripped code of **one**
module, `Oka/AnalyticSpace/SimplyConnected.lean`, which declares them.

**The places that say `…SeparatedFiniteEtaleOver.fundamentalGroup` is trivial are all in one
module and all of them are hypotheses.** At that same commit
`Subsingleton (…SeparatedFiniteEtaleOver.fundamentalGroup …)`
occurs **three** times in the comment-stripped code of the tree, all in
`Oka/AnalyticSpace/SimplyConnected.lean` and all as the instance argument of one of its three
theorems, and **no declaration under `Oka/` concluded it**. At the commit that adds this file it
occurs **seven** times, the other four being in this file, and the first theorem below is the
declaration that concludes it — **the sentence before this one is a figure about the base commit,
and this push is what falsifies it**, which is why it is pinned and not written in the present
tense. What this file adds is an implication and decides nothing about any base on its own. So a
consumer that wanted the hypothesis had no way to get it, and one that had it at a point had no
way to move it.

**Which spelling the scan counts is part of its figure.** The population is every tracked `.lean`
file under `Oka/` together with the root module, the stripper is
`scripts/import_cost.py`'s `strip_comments`, and what is counted is the name **not preceded or
followed by a letter, a digit or `_`**, with a `.` allowed before it. That is the spelling
`Oka/AnalyticSpace/SimplyConnected.lean` publishes and the reason it gives holds here unchanged:
every occurrence of these names in code is dotted.

## The whole of the mathematics is that a terminal object has one automorphism

`CategoryTheory.PreGaloisCategory.autMulEquivAutGalois` identifies the automorphism group of a
fibre functor with the multiplicative opposite of
`CategoryTheory.PreGaloisCategory.AutGalois`, the limit of the automorphism groups of the pointed
Galois objects, and `CategoryTheory.PreGaloisCategory.AutGalois.ext` says an element of that limit
is determined by its projections. A Galois object is connected —
`CategoryTheory.PreGaloisCategory.IsGalois` is declared `extends IsConnected` — so the hypothesis
applies to it and makes it isomorphic to `…SeparatedFiniteEtaleOver.id X`, which
`…SeparatedFiniteEtaleOver.isTerminalId` says is terminal;
`CategoryTheory.Limits.IsTerminal.ofIso` carries terminality across that isomorphism and
`CategoryTheory.Limits.IsTerminal.hom_ext` then collapses the automorphism group of the Galois
object to one element. Every projection of the limit therefore lands in a subsingleton, and the
limit is one.

**No step of that evaluates anything at the point.** The hypothesis does not mention it; the point
enters only through the functor whose automorphism group is being computed, and it enters the same
way for every point of the base. **That is why the two transports below are one line each and are
not a second theorem**: `…SeparatedFiniteEtaleOver.subsingleton_fundamentalGroup_congr` is the
criterion at one point composed with the criterion at another, and the second transport is the
first under `not_subsingleton_iff_nontrivial` twice.

**This is not the argument the forward direction runs.** That one goes through the fibre — the
group acts transitively on it, a trivial group makes it a one-point set, and the fibre functor
reflects isomorphisms — and the fibre is where it meets the point. Neither direction is the other
read backwards at the level of proofs; only the statements are converse.

## The two converses of that module, which are different sentences

`Oka/AnalyticSpace/SimplyConnected.lean`'s `## What is not here` says *The converse direction is
the one this repository can witness, and it is not in this file.* **That is a different converse
from this one and that bullet is not retired by this file.** What it refers to is a *refutation*:
a cover that is not isomorphic to the base over itself refutes the hypothesis. What is below is
the *implication* run backwards — from the conclusion holding for every connected cover to the
hypothesis — and it is a statement about the base and not about any one cover. **The refutation
is an instance of the forward direction and needs nothing here.**

## What the import costs, measured in the environment and not by a scan

This file's only `import` is `Oka.AnalyticSpace.SimplyConnected`, which is in `import Oka`'s
closure already, so **the cost is zero and it is a run and not a diff**: at the commit this file is
cut from `import Oka` brings **5538** modules and at the commit that adds it **5539**, by a set
difference over `Lean.Environment.allImportedModuleNames`, and the one module the difference
contains is this one. **No Mathlib module enters the closure**, and in particular
`Mathlib/CategoryTheory/Galois/Prorepresentability.lean` — where
`CategoryTheory.PreGaloisCategory.autMulEquivAutGalois` and
`CategoryTheory.PreGaloisCategory.AutGalois.ext`, the two rungs below that
`Oka/AnalyticSpace/SimplyConnected.lean` does not itself use, are declared — is already there:
`Oka/AnalyticSpace/FundamentalGroup.lean` brings it in four steps —
`Mathlib.CategoryTheory.Galois.Equivalence`, `Mathlib.CategoryTheory.Galois.EssSurj`,
`Mathlib.CategoryTheory.Galois.Topology`, `Mathlib.CategoryTheory.Galois.Prorepresentability` —
each of which is an import line of the one before it, the third being the second line of the
second and the other two the first of theirs. The base figure is taken by elaborating the base
`Oka.lean` at this checkout, which imports 5537 modules and is one short of `import Oka` there by
the root module itself. **A marginal import cost is a figure about the importer at a commit and is
meaningless without one**, which is why both are pinned here and neither is in the present tense.

## What the census scripts return

`scripts/DumpOkaDecls.lean` writes **4** rows at this module — the four declarations, with **no**
equation lemma, match lemma or congruence lemma — and the dump total moves **4984 → 4988**.
`scripts/DumpEnvNames.lean` moves **338257 → 338262**, which is those four declarations and this
one module and nothing else.

`scripts/check_docstring_names.py` goes **17962 → 17990** backticked names (**4374 → 4392**
distinct) and **332 → 349** elided citations (**160 → 164** distinct), with **0** unresolved at
both ends, **6** resolving under more than one namespace at both, and **239** dotless at both.
**Both ends of every figure in this section are runs**: the base column is that script run **in a
worktree at the base commit** against dumps synthesised from the head ones by deleting this
module's four rows from the declaration dump and its five — four declarations and one module —
from the environment-name dump, which is exact because both dumps are per-name and that script
reads the prose of the tree it is run in.

## Main results

- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.subsingleton_fundamentalGroup_of_iso_id`:
  **if every connected cover separated over the base is isomorphic to the base over itself, then
  the fundamental group at any point of the base is trivial.**
- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.subsingleton_fundamentalGroup_iff`:
  **and that is a criterion** — the two conditions are equivalent.
- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.subsingleton_fundamentalGroup_congr`:
  **so triviality of the group at one point is triviality at any other.**
- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.nontrivial_fundamentalGroup_congr`: the
  same transport in the positive form a consumer states.

## The list above is written in full

**Every head in the list above is the whole name**, with the house `…` elision kept for the prose
outside it, because an elided backticked token of a `## Main results` section resolves to nothing
against the declaration dump. That is the trap `Oka/AnalyticSpace/FundamentalGroup.lean` records
at length and it is not restated here.

## What is not here

* **No base is exhibited whose fundamental group is trivial, and none is claimed to exist.** That
  is the first bullet of `Oka/AnalyticSpace/SimplyConnected.lean`'s own `## What is not here`, said
  there of that file, and it is still true of the tree. **What this file changes is the shape of
  the question and not its answer**: to exhibit one it is now enough to classify the connected
  covers of a base, a statement in which
  neither the group nor a point of the base occurs. Nothing below does that for any base.
* **The coproduct form of the criterion is not here.**
  `…SeparatedFiniteEtaleOver.exists_iso_coprod_id` says a trivial group makes every cover a finite
  coproduct of copies of the base over itself; the converse of *that* — from every cover being such
  a coproduct to the group being trivial — is neither stated nor refuted below. **It is not
  obtained by composing anything here**, because the criterion's hypothesis is about connected
  covers one at a time, and the step that gets from the one to the other is
  `…SeparatedFiniteEtaleOver.nonempty_iso_id_of_iso_coprod_id` in
  `Oka/AnalyticSpace/SimplyConnectedCoprod.lean`, where both directions and the second criterion
  are.

  **Until 2026-09-21 this bullet priced that step at one statement, and named the wrong one**: it
  read *what it needs and this file does not have is that a connected object isomorphic to a finite
  coproduct of copies of a terminal object has a one-element index type.* That statement is true
  and **is not what the step needs**; the index type is never counted. A coprojection into a
  coproduct is a monomorphism — `CategoryTheory.Limits.MonoCoprod.mono_ι`, at the
  `CategoryTheory.Limits.MonoCoprod` instance `Mathlib/CategoryTheory/Galois/Basic.lean` declares
  for every `CategoryTheory.GaloisCategory` — so one coprojection composed with the given
  isomorphism is a mono into the connected object and
  `CategoryTheory.PreGaloisCategory.IsConnected.noTrivialComponent` makes it an isomorphism
  outright. **A count of the index type is a consequence of that conclusion and not a step towards
  it**, and the retired clause is kept here rather than struck because a prescription that was
  acted on is worth a record.
* **Nothing relates the groups at two different points.** The transports below carry the
  *triviality* of the group from one point to another, and its *failure* back, through a condition
  that mentions neither point; whether `…SeparatedFiniteEtaleOver.fundamentalGroup x` and
  `…SeparatedFiniteEtaleOver.fundamentalGroup y` are isomorphic as groups is neither stated nor
  refuted below. **Mathlib does relate the automorphism groups of two fibre functors of one
  category when the second is a whiskering of the first, and two points of one base do not give
  such a pair.** `CategoryTheory.PreGaloisCategory.autEquivAutWhiskerRight` is an isomorphism of
  topological groups between the automorphism groups of `F` and `F ⋙ G` at a fully faithful `G`,
  and `CategoryTheory.PreGaloisCategory.FiberFunctor.comp_right` makes `F ⋙ E` a fibre functor
  again when `E` is an equivalence, so a pair of fibre functors of one category *can* be compared
  there — `Mathlib/CategoryTheory/Galois/Equivalence.lean` compares such a pair across a universe
  switch. But `…SeparatedFiniteEtaleOver.fintypeFiberFunctor x` and
  `…SeparatedFiniteEtaleOver.fintypeFiberFunctor y` are not a functor and a whiskering of it, and
  nothing below makes them one. **A route to such a comparison does exist in
  `Mathlib/CategoryTheory/Galois/`, and it is in the one module of that folder this repository
  does not import.**
  `Mathlib/CategoryTheory/Galois/IsFundamentalgroup.lean` makes a compact topological group acting
  suitably on the fibres isomorphic to the automorphism group of the functor, so a single group
  serving at two points would relate the two; **it is not in the environment of `Oka` at the
  commit that adds this file**, which is why it is cited here by path — its declarations
  resolve to nothing in the dump `scripts/check_docstring_names.py` checks against, so naming one
  would fail that check rather than help a reader. **A transport of a property is not an
  isomorphism of the objects that have it**, and reading the second off the first is the error
  this bullet exists to stop.
* **No comparison with the topologist's fundamental group**, for the reason
  `Oka/AnalyticSpace/FundamentalGroup.lean`'s own bullet gives.
  `Oka/Analysis/Complex/FundamentalGroup.lean` is a different group of a different kind and
  nothing below bears on it.
* **Nothing about analytification and nothing about a scheme.** This is the analytic side alone.
* **No instance and no definition.** All four declarations below are theorems; this file declares
  no instance and no `def`, and every class instance the four consume is declared elsewhere.
-/

universe u

open CategoryTheory CategoryTheory.Limits
open scoped FintypeCatDiscrete

namespace ComplexAnalytic.AnalyticSpace

variable {X : AnalyticSpace.{u}} [T2Space (X : Type u)] [PreconnectedSpace (X : Type u)]
  [Nonempty (X : Type u)]

/-- **A base over which every connected cover is the base over itself has trivial fundamental
group**, at every point of it.

`CategoryTheory.PreGaloisCategory.autMulEquivAutGalois` replaces the group by the limit of the
automorphism groups of the pointed Galois objects and
`CategoryTheory.PreGaloisCategory.AutGalois.ext` reduces an equality there to its projections. A
`CategoryTheory.PreGaloisCategory.PointedGaloisObject` is Galois and so connected, the hypothesis
makes it isomorphic to the base over itself, and
`CategoryTheory.Limits.IsTerminal.ofIso` at `…SeparatedFiniteEtaleOver.isTerminalId` makes it
terminal — after which `CategoryTheory.Limits.IsTerminal.hom_ext` leaves its automorphism group one
element.

**The point appears in the conclusion and in no hypothesis**, which is what
`…SeparatedFiniteEtaleOver.subsingleton_fundamentalGroup_congr` below reads off this statement.

**The hypothesis is a plain `∀` and not an instance argument**, because the cover it speaks of is
quantified over: an instance argument would have to be discharged by search at a fixed object, and
there is no fixed object here. -/
theorem SeparatedFiniteEtaleOver.subsingleton_fundamentalGroup_of_iso_id (x : X)
    (h : ∀ A : SeparatedFiniteEtaleOver.{u} X, PreGaloisCategory.IsConnected A →
      Nonempty (A ≅ SeparatedFiniteEtaleOver.id.{u} X)) :
    Subsingleton (SeparatedFiniteEtaleOver.fundamentalGroup.{u} x) := by
  have hsub : Subsingleton (PreGaloisCategory.AutGalois
      (SeparatedFiniteEtaleOver.fintypeFiberFunctor.{u} x)) := by
    refine ⟨fun f g ↦ PreGaloisCategory.AutGalois.ext _ fun A ↦ ?_⟩
    have hterm : IsTerminal A.obj :=
      (SeparatedFiniteEtaleOver.isTerminalId.{u} X).ofIso (h A.obj inferInstance).some.symm
    exact Aut.ext (hterm.hom_ext _ _)
  exact (PreGaloisCategory.autMulEquivAutGalois
    (SeparatedFiniteEtaleOver.fintypeFiberFunctor.{u} x)).toEquiv.subsingleton

/-- **The fundamental group at a point is trivial exactly when every connected cover separated over
the base is isomorphic to the base over itself.**

The two directions are `…SeparatedFiniteEtaleOver.nonempty_iso_id` and
`…SeparatedFiniteEtaleOver.subsingleton_fundamentalGroup_of_iso_id` above and nothing is added to
either.

**What is worth having is that the right-hand side names no point**, which is what makes this an
`Iff` and not a pair: a condition on the base alone has been shown equivalent to a condition
carrying a point of it. -/
theorem SeparatedFiniteEtaleOver.subsingleton_fundamentalGroup_iff (x : X) :
    Subsingleton (SeparatedFiniteEtaleOver.fundamentalGroup.{u} x) ↔
      ∀ A : SeparatedFiniteEtaleOver.{u} X, PreGaloisCategory.IsConnected A →
        Nonempty (A ≅ SeparatedFiniteEtaleOver.id.{u} X) :=
  ⟨fun _ A _ ↦ SeparatedFiniteEtaleOver.nonempty_iso_id.{u} x A,
    SeparatedFiniteEtaleOver.subsingleton_fundamentalGroup_of_iso_id.{u} x⟩

/-- **Triviality of the fundamental group does not depend on the point.**

The criterion above at one point composed with the criterion at another; the condition they are
both equivalent to is the same condition, because it mentions neither point.

**This is what lets a hypothesis be moved.** Three of the four declarations of
`Oka/AnalyticSpace/SimplyConnected.lean` carry
`[Subsingleton (…SeparatedFiniteEtaleOver.fundamentalGroup x)]` at a named `x` — every one of them
that mentions the group at all — and before this a consumer holding it at one point and wanting a
conclusion at another had no way across. -/
theorem SeparatedFiniteEtaleOver.subsingleton_fundamentalGroup_congr (x y : X) :
    Subsingleton (SeparatedFiniteEtaleOver.fundamentalGroup.{u} x) ↔
      Subsingleton (SeparatedFiniteEtaleOver.fundamentalGroup.{u} y) :=
  (SeparatedFiniteEtaleOver.subsingleton_fundamentalGroup_iff.{u} x).trans
    (SeparatedFiniteEtaleOver.subsingleton_fundamentalGroup_iff.{u} y).symm

/-- **Non-triviality of the fundamental group does not depend on the point either.**

The transport above under `not_subsingleton_iff_nontrivial` at each side. `Nontrivial` rather than
`¬ Subsingleton` because the two are equivalent for a group and the positive form is what a
consumer states. -/
theorem SeparatedFiniteEtaleOver.nontrivial_fundamentalGroup_congr (x y : X) :
    Nontrivial (SeparatedFiniteEtaleOver.fundamentalGroup.{u} x) ↔
      Nontrivial (SeparatedFiniteEtaleOver.fundamentalGroup.{u} y) := by
  rw [← not_subsingleton_iff_nontrivial, ← not_subsingleton_iff_nontrivial]
  exact not_congr (SeparatedFiniteEtaleOver.subsingleton_fundamentalGroup_congr.{u} x y)

end ComplexAnalytic.AnalyticSpace
