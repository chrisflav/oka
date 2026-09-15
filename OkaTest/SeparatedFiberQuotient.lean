/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka

/-!
# Which preservation of quotients instance search finds, and which it does not

`Oka/AnalyticSpace/SeparatedFiberQuotient.lean` declares
`CategoryTheory.Limits.PreservesColimitsOfShape (CategoryTheory.SingleObj G)` at the two fibre
functors of `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver` for every finite group `G`,
and says in its `## What is not here` that **nothing at
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver`** says anything about that shape.

**This file is the control for both halves of that, and it is a control and not a theorem.** The
two `example`s that succeed are there so that a reader can see the instances are found by **search**
and not only by name — which is the form
`Mathlib/CategoryTheory/Galois/Basic.lean`'s `FiberFunctor` asks its fields in — and the two
`#guard_msgs` probes are there so that the claimed absences are failures this file records rather
than assertions the prose makes.

**The second probe is the deliberate failure that makes the first pair worth reading**, and it
fails for a reason unrelated to the quotient: the inclusion of the separated covers into the covers
preserves colimits of no shape in this repository, so a probe at it fails however the fibre
functors are stated. If the two instances above it were ever restated at the ambient covers, or the
inclusion given such a statement, these probes would fail and this file would stop compiling.

**Nothing here is guarded in `OkaTest/Axioms/Morphisms.lean` and nothing here should be.** An
`example` has no name, so `#print axioms` cannot be pointed at it; the ten declarations this file
probes are guarded there, under
`### Both fibre functors at the separated covers preserve quotients by finite group actions`.

**The hypotheses are the ones the library statements carry and no object is built.** Nothing below
needs a concrete analytic space, a concrete group or a concrete functor: the instances are stated at
a variable base with `[T2Space]`, a variable finite group and a variable point, which is exactly the
shape a caller meets them in.
-/

universe u

open CategoryTheory

namespace OkaTest.SeparatedFiberQuotient

variable {X : ComplexAnalytic.AnalyticSpace.{u}} [T2Space (X : Type u)]
variable (G : Type*) [Group G] [Finite G] (x : X)

/-- The `Type u`-valued fibre functor preserves colimits of shape `CategoryTheory.SingleObj G`,
found by search. -/
example :
    Limits.PreservesColimitsOfShape (SingleObj G)
      (ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.fiberFunctor.{u} x) := by
  infer_instance

/-- And so does the `FintypeCat`-valued one, which is the functor the class asks it of. -/
example :
    Limits.PreservesColimitsOfShape (SingleObj G)
      (ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.fintypeFiberFunctor.{u} x) := by
  infer_instance

/--
error: failed to synthesize instance of type class
  Limits.PreservesColimitsOfShape (SingleObj G) (ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fiberFunctor x)

Hint: Type class instance resolution failures can be inspected with the `set_option
trace.Meta.synthInstance true` command.
-/
#guard_msgs (whitespace := lax) in
/-- The same statement at the ambient covers is not found, which is the absence the module
docstring of `Oka/AnalyticSpace/SeparatedFiberQuotient.lean` records: the quotient it is about is
the separated category's, and no declaration of this repository builds one at the covers. -/
example :
    Limits.PreservesColimitsOfShape (SingleObj G)
      (ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fiberFunctor.{u} x) := by
  infer_instance

/--
error: failed to synthesize instance of type class
  Limits.PreservesColimitsOfShape (SingleObj G)
    (ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.toFiniteEtaleOver X)

Hint: Type class instance resolution failures can be inspected with the `set_option
trace.Meta.synthInstance true` command.
-/
#guard_msgs (whitespace := lax) in
/-- And the probe that fails for an unrelated reason: the inclusion of the separated covers into
the covers preserves colimits of no shape in this repository, so this fails however the two fibre
functors are stated, and a green tick above without a red one here would mean the search had
stopped discriminating. -/
example :
    Limits.PreservesColimitsOfShape (SingleObj G)
      (ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.toFiniteEtaleOver.{u} X) := by
  infer_instance

end OkaTest.SeparatedFiberQuotient
