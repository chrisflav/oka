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
of `Oka/AnalyticSpace/FiniteEtaleBaseChange.lean` to that cospan, which is the point — what is
checked is that they apply.

## What is not here

* **No new declaration.** Everything below is an `example`, so this file adds no row to
  `scripts/DumpOkaDecls.lean`'s dump and nothing here is guarded or can be cited.
* **No `#synth` control.** This push removes a hypothesis rather than adding a class, so there is
  no instance whose absence at one end and presence at the other would say anything. The control
  that applies is the signature, and it belongs in the pull request rather than in the tree:
  `#check @ComplexAnalytic.AnalyticSpace.isFiniteEtale_baseChangeSnd` loses its `[T2Space E]`
  argument. The first `example` below is the sharper statement in any case — the hypothesis is
  not merely unavailable at this cospan, it is refutable.
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
which is the one `CategoryTheory.MorphismProperty.IsStableUnderBaseChange` would quantify. It
does not elaborate at all unless the instance above is found. -/
example : IsFiniteEtale (Limits.pullback.snd doubledLineFold.{u} doubledLineFold.{u}) :=
  isFiniteEtale_pullback_snd_of_isFiniteEtale _ _
