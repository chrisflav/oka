/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka

/-!
# Which `PreservesEpimorphisms` instance search finds, and which it does not

`Oka/AnalyticSpace/SeparatedFiberFunctorEpi.lean` declares
`CategoryTheory.Functor.PreservesEpimorphisms` at the two fibre functors of
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver` and says in its `## What is not here` that
the same statement at the two fibre functors of `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver` is
absent, and that it is **not** a corollary of what is there: a full subcategory has fewer objects to
test against, so `CategoryTheory.Epi` in the covers is the stronger hypothesis and neither statement
implies the other.

**This file is the control for both halves of that sentence, and it is a control and not a
theorem.** The two `example`s that succeed are there so that a reader can see the instances are
found by search and not only by name, and the two `#guard_msgs` probes are there so that the claimed
absence is a failure this file records rather than an assertion the prose makes. **A probe that
fails is the point of the second pair**: if the instances above it were ever declared at the
ambient category, these two `#guard_msgs` would fail and this file would stop compiling, which is
what makes the absence checked rather than believed.

**Nothing here is guarded in `OkaTest/Axioms/Morphisms.lean` and nothing here should be.** An
`example` has no name, so `#print axioms` cannot be pointed at it; the five declarations this file
probes are guarded there, under
`### Both fibre functors at the separated covers preserve epimorphisms`.

**The hypotheses are the ones the library statements carry and no object is built.** Nothing below
needs a concrete analytic space: the instances are stated at a variable base with `[T2Space]` and a
variable point, which is exactly the shape a caller meets them in, and a concrete witness would test
the witness as well as the search.
-/

universe u

open CategoryTheory

namespace OkaTest.SeparatedFiberFunctorEpi

variable {X : ComplexAnalytic.AnalyticSpace.{u}} [T2Space (X : Type u)] (x : X)

/-- The instance at the `Type u`-valued fibre functor of the separated covers is found by search. -/
example :
    Functor.PreservesEpimorphisms
      (ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.fiberFunctor.{u} x) := by
  infer_instance

/-- And so is the one at the `FintypeCat`-valued fibre functor. -/
example :
    Functor.PreservesEpimorphisms
      (ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.fintypeFiberFunctor.{u} x) := by
  infer_instance

/--
error: failed to synthesize instance of type class
  (ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fiberFunctor x).PreservesEpimorphisms

Hint: Type class instance resolution failures can be inspected with the `set_option
trace.Meta.synthInstance true` command.
-/
#guard_msgs (whitespace := lax) in
/-- The same statement at the ambient covers is not found, which is the absence the module
docstring of `Oka/AnalyticSpace/SeparatedFiberFunctorEpi.lean` records. -/
example :
    Functor.PreservesEpimorphisms
      (ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fiberFunctor.{u} x) := by
  infer_instance

/--
error: failed to synthesize instance of type class
  (ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fintypeFiberFunctor x).PreservesEpimorphisms

Hint: Type class instance resolution failures can be inspected with the `set_option
trace.Meta.synthInstance true` command.
-/
#guard_msgs (whitespace := lax) in
/-- Nor is it at the ambient `FintypeCat`-valued one. -/
example :
    Functor.PreservesEpimorphisms
      (ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fintypeFiberFunctor.{u} x) := by
  infer_instance

end OkaTest.SeparatedFiberFunctorEpi
