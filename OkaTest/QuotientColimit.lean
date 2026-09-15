/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka

/-!
# Which colimit instance search finds at the separated covers, and which it does not

`Oka/AnalyticSpace/QuotientColimit.lean` declares
`CategoryTheory.Limits.HasColimitsOfShape (CategoryTheory.SingleObj G)` at
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver` for every finite group `G`, and says in its
`## What is not here` that it supplies **no** coequaliser and no finite colimits, and that nothing
below it is stated at `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver`.

**This file is the control for both halves of that, and it is a control and not a theorem.** The
`example` that succeeds is there so that a reader can see the instance is found by **search** and
not only by name — which is the whole reason that declaration is an `instance` rather than a
`theorem`, since the `PreGaloisCategory` field it answers is discharged by `infer_instance` — and
the two `#guard_msgs` probes are there so that the claimed absences are failures this file records
rather than assertions the prose makes.

**The second probe is the deliberate failure that makes the first one worth reading.**
`CategoryTheory.Limits.HasFiniteColimits` is what `Oka/CategoryTheory/Limits/Shapes/SingleObj.lean`
would need to give the same conclusion, and it is still not available here: if it ever becomes
available, that probe fails and this file stops compiling, which is what turns *the colimit is
constructed at the one shape and not through finite colimits* from a claim into a check.

**Nothing here is guarded in `OkaTest/Axioms/Morphisms.lean` and nothing here should be.** An
`example` has no name, so `#print axioms` cannot be pointed at it; the twenty-six declarations this
file probes are guarded there, under
`### The quotient of a cover by a finite group is the colimit of the action`.

**The hypotheses are the ones the library statements carry and no object is built.** Nothing below
needs a concrete analytic space or a concrete group: the instance is stated at a variable base with
`[T2Space]` and a variable finite group, which is exactly the shape a caller meets it in, and a
concrete witness would test the witness as well as the search.
-/

universe u

open CategoryTheory

namespace OkaTest.QuotientColimit

variable {X : ComplexAnalytic.AnalyticSpace.{u}} [T2Space (X : Type u)]
variable (G : Type*) [Group G] [Finite G]

/-- The colimit of shape `CategoryTheory.SingleObj G` at the separated covers is found by search,
which is the form `Mathlib/CategoryTheory/Galois/Basic.lean`'s fourth `PreGaloisCategory` field
asks for it in. -/
example :
    Limits.HasColimitsOfShape (SingleObj G)
      (ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.{u} X) := by
  infer_instance

/--
error: failed to synthesize instance of type class
  Limits.HasColimitsOfShape (SingleObj G) X.FiniteEtaleOver

Hint: Type class instance resolution failures can be inspected with the `set_option
trace.Meta.synthInstance true` command.
-/
#guard_msgs (whitespace := lax) in
/-- The same statement at the ambient covers is not found, which is the absence the module
docstring of `Oka/AnalyticSpace/QuotientColimit.lean` records under *Not stated at
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver`*: the quotient there would be a cover with no
separatedness to carry, and no declaration of this repository builds one. -/
example :
    Limits.HasColimitsOfShape (SingleObj G)
      (ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.{u} X) := by
  infer_instance

/--
error: failed to synthesize instance of type class
  Limits.HasFiniteColimits X.SeparatedFiniteEtaleOver

Hint: Type class instance resolution failures can be inspected with the `set_option
trace.Meta.synthInstance true` command.
-/
#guard_msgs (whitespace := lax) in
/-- And finite colimits are still not found at the separated covers, which is the probe that makes
the first `example` above worth reading: the instance it finds is **not** reached through
`CategoryTheory.Limits.hasColimitsOfShape_singleObj`, the mirror-tree declaration that takes this
class as a hypothesis, because this class is not there to be taken. -/
example :
    Limits.HasFiniteColimits (ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.{u} X) := by
  infer_instance

end OkaTest.QuotientColimit
