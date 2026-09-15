/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka

/-!
# The base change of a finite étale morphism whose source is not Hausdorff

`Oka/AnalyticSpace/FiniteEtaleBaseChange.lean` asked `[T2Space E]` of the source of its finite
étale leg until the push that adds this file, and `Oka/AnalyticSpace/Double.lean` supplies a
finite étale morphism whose source is not Hausdorff:
`ComplexAnalytic.AnalyticSpace.doubledLineFold`, the fold of the complex line with two origins
down to `ℂ¹`, with `ComplexAnalytic.AnalyticSpace.not_t2Space_doubledLine` as the proof that its
source is not.

**The two files existed side by side and did not meet.** Every statement of the base-change file
was out of reach at that morphism, and not because a proof was missing: the hypothesis it asked
for is **false** there, so no instance could ever have supplied it and the statements did not
elaborate at all. This file is the demonstration that they now do, and it is the whole of what
the hypothesis removal buys that a signature cannot show.

The cospan is `doubledLineFold` against itself — `E ×_{ℂ¹} E` for `E` the line with two origins
— which is the cheapest cospan that is non-Hausdorff in **both** legs and is not the identity in
either. Nothing below is proved: every `example` is an application of the corresponding statement
of `Oka/AnalyticSpace/FiniteEtaleBaseChange.lean` or of
`Oka/AnalyticSpace/FiniteEtaleStableUnderBaseChange.lean` to that cospan, which is the point —
what is checked is that they apply.

**The `### The morphism property at this cospan` section was added on 2026-09-15**, when
`ComplexAnalytic.AnalyticSpace.isFiniteEtale` became
`CategoryTheory.MorphismProperty.IsStableUnderBaseChange`. That class quantifies over every cospan
with a finite étale leg and asks no separation axiom, so this cospan is one of the ones it reaches
and could not have been reached by any earlier form of the statement; applying the class here
rather than citing it is what says so.

## What is not here

* **No new declaration.** Everything below is an `example`, so this file adds no row to
  `scripts/DumpOkaDecls.lean`'s dump and nothing here is guarded or can be cited.
* **No control for the hypothesis removal itself.** This file's first push removed a hypothesis
  rather than adding a class, so there was no instance of its own whose absence at one end and
  presence at the other would say anything. The control that applied was the signature, and it
  belonged in the pull request rather than in the tree:
  `#check @ComplexAnalytic.AnalyticSpace.isFiniteEtale_baseChangeSnd` loses its `[T2Space E]`
  argument. The first `example` below is the sharper statement in any case — the hypothesis is
  not merely unavailable at this cospan, it is refutable.

  **This bullet was headed *No `#synth` control* and said that this file has none, until
  2026-09-15**, when `Oka/AnalyticSpace/FiniteEtaleStableUnderBaseChange.lean` added a class and
  the first `example` of `### The morphism property at this cospan` became exactly that control:
  `inferInstance` at `(isFiniteEtale.{u}).IsStableUnderBaseChange`, which fails at the commit this
  section is cut from. What the bullet says of the hypothesis removal is unchanged and is why it
  is narrowed rather than struck.
* **Nothing about the fibre product's own separation.** `E ×_{ℂ¹} E` is not Hausdorff either, and
  no statement here says so; `ComplexAnalytic.AnalyticSpace.baseChange` imposes no separation
  axiom on what it builds and this file asks none of it.
* **Nothing about the degree.** The fold has two sheets and so does its base change; that is
  `Oka/AnalyticSpace/FiniteEtaleBaseChange.lean`'s own `## What is not here` bullet
  **Nothing about the degree** and this file does not close it.
-/

open CategoryTheory ComplexAnalytic ComplexAnalytic.AnalyticSpace

universe u

/-- **The source of the finite étale morphism below is not Hausdorff.** This is the hypothesis
`Oka/AnalyticSpace/FiniteEtaleBaseChange.lean` carried until the push that adds this file, and it
is false here — which is why nothing below elaborated before. -/
example : ¬ T2Space (doubledLine.{u} : Type u) := not_t2Space_doubledLine.{u}

/-- **The projection is finite étale.** -/
example : IsFiniteEtale (baseChangeSnd doubledLineFold.{u} doubledLineFold.{u}) :=
  isFiniteEtale_baseChangeSnd _ _

/-- **The square is a pullback in `ComplexAnalytic.AnalyticSpace`.** -/
example : IsPullback (baseChangeFst doubledLineFold.{u} doubledLineFold.{u})
    (baseChangeSnd doubledLineFold.{u} doubledLineFold.{u}) doubledLineFold.{u}
    doubledLineFold.{u} :=
  isPullback_baseChange _ _

/-- **So the fibre product exists**, as an instance found by search. -/
example : Limits.HasPullback doubledLineFold.{u} doubledLineFold.{u} := inferInstance

/-- **And the base change is finite étale in the `CategoryTheory.Limits.pullback` spelling**,
which is the one `CategoryTheory.MorphismProperty.IsStableUnderBaseChange` quantifies. It
does not elaborate at all unless the instance above is found. **The verb read *would quantify*
until 2026-09-15**, when that class became a theorem of this repository for
`ComplexAnalytic.AnalyticSpace.isFiniteEtale` and the section below started applying it; what
this `example` checks is unchanged. -/
example : IsFiniteEtale (Limits.pullback.snd doubledLineFold.{u} doubledLineFold.{u}) :=
  isFiniteEtale_pullback_snd_of_isFiniteEtale _ _

/-! ### The morphism property at this cospan -/

/-- **The class, as an instance found by search.** This is the `#synth` control at the positive
end: the same query fails at the commit this section is cut from, in a file importing
`Oka.AnalyticSpace.FiniteEtaleOver` and in one importing the whole of `Oka` alike. -/
example : (isFiniteEtale.{u}).IsStableUnderBaseChange := inferInstance

/-- **The class applied at a cospan whose finite étale leg has a non-Hausdorff source.** This is
what the section head is for: `CategoryTheory.MorphismProperty.IsStableUnderBaseChange` asks
nothing of the four spaces, so this cospan is inside it, and nothing weaker than the whole class
would let the square below be an arbitrary pullback square rather than the constructed one.
The conclusion is `ComplexAnalytic.AnalyticSpace.isFiniteEtale_baseChangeSnd` again, reached
through the class instead of directly. -/
example : isFiniteEtale.{u} (baseChangeSnd doubledLineFold.{u} doubledLineFold.{u}) :=
  MorphismProperty.of_isPullback (isPullback_baseChange _ _)
    (inferInstance : IsFiniteEtale doubledLineFold.{u})

/-- **A Mathlib consequence that instance search reaches only through the class**, at this
morphism: every base change along `ComplexAnalytic.AnalyticSpace.doubledLineFold` of a finite
étale morphism is finite étale. `CategoryTheory.MorphismProperty.IsStableUnderBaseChangeAlong` is
Mathlib's, and the instance producing it takes
`CategoryTheory.MorphismProperty.IsStableUnderBaseChange` as an instance argument, which is why a
`theorem` in place of the instance would not be found here. -/
example : (isFiniteEtale.{u}).IsStableUnderBaseChangeAlong doubledLineFold.{u} := inferInstance

/-- **And the same for `CategoryTheory.MorphismProperty.pullbacks`**, which is the other Mathlib
consumer taking the class as an instance argument: a morphism exhibited as a pullback of a finite
étale morphism is finite étale. Nothing about this cospan enters — it is the general statement,
compiled here because this is the file that exercises the class. -/
example : (isFiniteEtale.{u}).pullbacks ≤ isFiniteEtale.{u} :=
  MorphismProperty.pullbacks_le _
