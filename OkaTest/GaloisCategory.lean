/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka

/-!
# Which Galois-category class instance search finds, and which it does not

`Oka/AnalyticSpace/GaloisCategory.lean` declares
`CategoryTheory.PreGaloisCategory` at
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver` and
`CategoryTheory.PreGaloisCategory.FiberFunctor` at its `FintypeCat`-valued fibre functor, and its
`## What is not here` claims three absences and one consequence. **This file is the control for all
four, and it is a control and not a theorem.**

**The two `example`s that succeed are there so that a reader can see the instances are found by
search** and not only by name, which is the form every consumer of those classes meets them in.
**The two `#guard_msgs` probes are there so that the claimed absences are failures this file
records rather than assertions the prose makes.**

**The probe at `CategoryTheory.GaloisCategory` is the priced one.** That class asks for a fibre
functor to **exist**, and every fibre functor this repository has is taken at a point of the base,
so reaching it costs `[Nonempty X]` — a hypothesis neither instance below carries. The probe is
what makes *no `CategoryTheory.GaloisCategory` instance* a measurement rather than an omission, and
it would start failing the moment somebody declared one, which is the point of writing it as a
probe rather than as a sentence.

**The probe at `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver` is the one that fails for a reason
unrelated to this file** and is therefore what makes a silent no-op visible: the ambient covers are
not separated, the `monoInducesIsoOnDirectSummand` field is stated only at the separated category,
and no statement of this repository puts either class at the ambient covers. If the two instances
were ever restated there this probe would fail and this file would stop compiling.

**One `example` is not an absence but a purchase.**
`CategoryTheory.Functor.ReflectsMonomorphisms` at that fibre functor is **not** synthesizable at
the commit before this one — not even in a file that imports
`Mathlib.CategoryTheory.Galois.Basic` directly, since the derivation Mathlib gives for it runs off
the `FiberFunctor` instance and not off the functor — and is synthesizable here. It is the one
thing in this neighbourhood that the class instance buys and that the eleven statements underneath
it did not already give.

**Nothing here is guarded in `OkaTest/Axioms/Morphisms.lean` and nothing here should be.** An
`example` has no name, so `#print axioms` cannot be pointed at it; the two declarations this file
probes are guarded there, under
`### The covers separated over a Hausdorff base form a Galois category`.

**The hypotheses are the ones the library statements carry and no object is built.** Nothing below
needs a concrete analytic space or a concrete point: the instances are stated at a variable base
with `[T2Space]`, a variable point and — for the second — `[PreconnectedSpace]`, which is exactly
the shape a caller meets them in.
-/

universe u

open CategoryTheory

namespace OkaTest.GaloisCategory

variable {X : ComplexAnalytic.AnalyticSpace.{u}} [T2Space (X : Type u)]

/-- The covers separated over a Hausdorff analytic space form a
`CategoryTheory.PreGaloisCategory`, found by search and with no hypothesis beyond `[T2Space]`. -/
example : PreGaloisCategory (ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.{u} X) := by
  infer_instance

/--
error: failed to synthesize instance of type class
  PreGaloisCategory X.FiniteEtaleOver

Hint: Type class instance resolution failures can be inspected with the `set_option
trace.Meta.synthInstance true` command.
-/
#guard_msgs (whitespace := lax) in
/-- The same class at the **ambient** covers is not found, which is the absence
`Oka/AnalyticSpace/GaloisCategory.lean`'s `## What is not here` records: the objects there carry no
separatedness, and the `monoInducesIsoOnDirectSummand` field is stated only at the category that
does. -/
example : PreGaloisCategory (ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.{u} X) := by
  infer_instance

variable [PreconnectedSpace (X : Type u)] (x : X)

/-- The `FintypeCat`-valued fibre functor at a point of a preconnected Hausdorff base is a
`CategoryTheory.PreGaloisCategory.FiberFunctor`, found by search. -/
example :
    PreGaloisCategory.FiberFunctor
      (ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.fintypeFiberFunctor.{u} x) := by
  infer_instance

/-- And what that instance buys: Mathlib derives `CategoryTheory.Functor.ReflectsMonomorphisms`
from the class, and it is not synthesizable at the commit before this one even with
`Mathlib.CategoryTheory.Galois.Basic` imported directly. -/
example :
    (ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.fintypeFiberFunctor.{u}
      x).ReflectsMonomorphisms := by
  infer_instance

/--
error: failed to synthesize instance of type class
  GaloisCategory X.SeparatedFiniteEtaleOver

Hint: Type class instance resolution failures can be inspected with the `set_option
trace.Meta.synthInstance true` command.
-/
#guard_msgs (whitespace := lax) in
/-- And the priced absence: `CategoryTheory.GaloisCategory` is the two classes above together with
the **existence** of a fibre functor, and this repository's fibre functors are taken at a point, so
it is not found without `[Nonempty X]` even here, where both of its other ingredients are
instances. -/
example : GaloisCategory (ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.{u} X) := by
  infer_instance

end OkaTest.GaloisCategory
