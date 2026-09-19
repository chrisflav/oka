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
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver`,
`CategoryTheory.PreGaloisCategory.FiberFunctor` at its `FintypeCat`-valued fibre functor and
`CategoryTheory.GaloisCategory` at that category again over a base that is in addition nonempty.
**This file is the control for what that module claims about all three, and it is a control and not
a theorem.**

**The `example`s that succeed are there so that a reader can see the instances are found by
search** and not only by name, which is the form every consumer of those classes meets them in.
**The `#guard_msgs` probes are there so that the claimed absences are failures this file records
rather than assertions the prose makes.**

**The probe at `CategoryTheory.GaloisCategory` called itself a canary and is not one, and that is
the one thing in this file worth reading twice.** Its paragraph read *The probe at
`CategoryTheory.GaloisCategory` is the priced one … it would start failing the moment somebody
declared one, which is the point of writing it as a probe rather than as a sentence*, from the
commit that added this file until this push, which is what falsifies it. **The instance was
declared and the probe did not start failing**: the probe is stated in a context carrying
`[T2Space]` and `[PreconnectedSpace]` and no `[Nonempty X]`, and the instance carries
`[Nonempty X]`, so nothing about the probe's context changed. **A probe is a control for the
context it is stated in and not for the tree** — the general form of the rule
`Oka/AnalyticSpace/GaloisCategory.lean`'s own head description states for a scan keyed on a
wording. **What this one measures is worth keeping and is not what its prose claimed**: that
the class is unreachable from the two hypotheses the fibre-functor instance carries, which is
the statement that `[Nonempty X]` is load-bearing. It is kept, with that written beside it, and the
`example`s under `variable [Nonempty (X : Type u)]` below are what record the class being
reachable at all.

**The instrument that would have been a canary is a second probe on the other side of the same
line.** `CategoryTheory.Limits.MonoCoprod` is probed twice — failing in the context without
`[Nonempty X]` and found in the one with it — so the pair says both halves and neither half can
be read as the other. **A single failing probe cannot distinguish *the class is not declared* from
*this context does not reach it*, and that distinction is the whole of what went wrong above.**

**The probe at `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver` is the one that fails for a reason
unrelated to this file** and is therefore what makes a silent no-op visible: the ambient covers are
not separated, the `monoInducesIsoOnDirectSummand` field is stated only at the separated category,
and no statement of this repository puts either class at the ambient covers. If the two instances
were ever restated there this probe would fail and this file would stop compiling.

**A *purchase* here is an `example` for a declaration of Mathlib's that this repository does not
state and that instance search reaches only through one of the three instances the module declares;
there are six, five of them added by this push, and one of those five is a definition.** The
`example`s for the three instances themselves and the `#guard_msgs` probes are neither, which is
what the count is a count of. The sixth is the one the commit that added this file carried:
`CategoryTheory.Functor.ReflectsMonomorphisms` at that fibre functor is **not** synthesizable at
`386d6ab`, the commit *before* the one that added this file — not even in a file that imports
`Mathlib.CategoryTheory.Galois.Basic` directly, since the derivation Mathlib gives for it runs off
the `FiberFunctor` instance and not off the functor, and that instance is what the commit that
added this file declares — and is synthesizable here and at `642ae9b`. **That sentence went on to
say it was *the one thing in this neighbourhood that the class instance buys*, from the commit that
added this file until this push, which is what falsifies it**: the **four** instances
`Mathlib/CategoryTheory/Galois/Basic.lean` declares under `[GaloisCategory C]` are
`CategoryTheory.Limits.MonoCoprod` at the category, `Finite (A ⟶ Y)` and `Finite (Aut A)` at a
connected object, and `CategoryTheory.PreGaloisCategory.FiberFunctor` at
`CategoryTheory.PreGaloisCategory.GaloisCategory.getFiberFunctor`, **none of the four is
synthesizable at `642ae9b` and all four are here**, and that `getFiberFunctor` is the definition,
which elaborates. **The one thing the `FiberFunctor` instance buys is what that clause was about
and is unmoved**; what moved is that there is now a second instance above it with a purchase of its
own.

**Nothing here is guarded in `OkaTest/Axioms/Morphisms.lean` and nothing here should be.** An
`example` has no name, so `#print axioms` cannot be pointed at it; the three declarations this file
probes are guarded there, under
`### The covers separated over a Hausdorff base form a Galois category`. **That clause read *the
two declarations* from the commit that added this file until this push**, which adds the third
guard in the same section.

**The hypotheses are the ones the library statements carry, and one object is built.** The three
instances are probed at a variable base with `[T2Space]`, a variable point, `[PreconnectedSpace]`
for the second and `[Nonempty]` as well for the third, which is exactly the shape a caller meets
them in; the `EmptyBase` section is the one place a concrete analytic space appears, and it appears
because a refutation stated under a hypothesis says nothing until something satisfies the
hypothesis. **That sentence read *and no object is built* and closed *Nothing below needs a
concrete analytic space or a concrete point*, until 2026-09-19**, when that section built one.

**The `EmptyBase` section is a refutation at a named space and not a probe of this file's usual
kind.**
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.not_galoisCategory_of_isEmpty`
(`Oka/AnalyticSpace/EmptyBase.lean`) is a theorem of the library and what this file adds is the
instantiation: the space is `ComplexAnalytic.AnalyticSpace.sigma` at `PEmpty.elim` and
`ComplexAnalytic.AnalyticSpace.isEmpty_sigma` is what says it has no points, both of them
`Oka/AnalyticSpace/Sigma.lean`'s and neither new. **That section and this file's `#guard_msgs`
probe at `CategoryTheory.GaloisCategory` say different things**: the probe says instance search
does not reach the class from `[T2Space]` and `[PreconnectedSpace]` alone, and the section says the
class is false at a base that has both. **None of its three `example`s is a purchase** in the sense
the paragraph opening *A purchase here is an `example`* uses, emphasis stripped — two are
statements of this repository and the third is the emptiness of that object — so that paragraph's
count is unmoved by it.

**The last `section` binds a second base and the reason is a hypothesis and not a name.** It
restates the base as `Y` with `[ConnectedSpace Y]` in place of `[PreconnectedSpace X]` and
`[Nonempty X]`, which cannot be done by adding a `variable` to what is above it: those two are
already in scope there, and the point of the `example` is that a caller holding neither of them
separately still reaches the class. **It records that the implication runs one way**, which is why
the instance is stated over the pair and not over `ConnectedSpace`.
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
from the class, and it is not synthesizable at `386d6ab` even with
`Mathlib.CategoryTheory.Galois.Basic` imported directly.

That read *at the commit before this one* until this push, and the module docstring above carries
the same claim and was pinned one push earlier: **an indexical names the parent of whatever the
file's latest commit is**, so it moved when this file was pushed to a second time, and at that
second parent — `642ae9b` — the class **is** synthesizable. A run at each: `failed to synthesize`
at `386d6ab`, found at `642ae9b`. -/
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

/--
error: failed to synthesize instance of type class
  Limits.MonoCoprod X.SeparatedFiniteEtaleOver

Hint: Type class instance resolution failures can be inspected with the `set_option
trace.Meta.synthInstance true` command.
-/
#guard_msgs (whitespace := lax) in
/-- And one of the four the class buys, probed in the same context: it is not reached without
`[Nonempty X]` either, because the only route to it is through the class above. **It is the only
one of the four with a failing counterpart**; the other three are recorded below as purchases, and
their absence at `642ae9b` is one of the eight `#synth` runs the module's prose reports and not a
probe of this file. -/
example : Limits.MonoCoprod (ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.{u} X) := by
  infer_instance

variable [Nonempty (X : Type u)]

/-- The class itself, with the one hypothesis the two probes above are missing, found by search. -/
example : GaloisCategory (ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.{u} X) := by
  infer_instance

/-- The first of the four the class buys. -/
example : Limits.MonoCoprod (ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.{u} X) := by
  infer_instance

/-- The second of the four, which asks its source to be a connected object. -/
example (A Y : ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.{u} X)
    [PreGaloisCategory.IsConnected A] : Finite (A ⟶ Y) := by
  infer_instance

/-- The third of the four, at the same object. -/
example (A : ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.{u} X)
    [PreGaloisCategory.IsConnected A] : Finite (Aut A) := by
  infer_instance

/-- And the definition the class carries, which needs no hypothesis on an object. -/
noncomputable example :
    ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.{u} X ⥤ FintypeCat :=
  PreGaloisCategory.GaloisCategory.getFiberFunctor _

/-- The fourth of the four, and it is stated at that definition: Mathlib's arbitrarily chosen fibre
functor is a `CategoryTheory.PreGaloisCategory.FiberFunctor`. It is the instance a read of
`Mathlib/CategoryTheory/Galois/Basic.lean` that stops at the `variable {C}` line misses, since that
line is `:436` and this instance is `:433`, above it and below the definition at `:429`. At
`642ae9b` it is not synthesizable, and what instance search reports there is the class and not
this instance: `failed to synthesize instance of type class GaloisCategory
X.SeparatedFiniteEtaleOver`, because `getFiberFunctor` consumes the class in its own statement, so
the elaboration stops before this instance is reached. -/
noncomputable example :
    PreGaloisCategory.FiberFunctor
      (PreGaloisCategory.GaloisCategory.getFiberFunctor
        (ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.{u} X)) := by
  infer_instance

section EmptyBase

/-- The disjoint union of the **empty** family of analytic spaces, which is the object this
section's refutation is read at: `ComplexAnalytic.AnalyticSpace.isEmpty_sigma` says a disjoint
union at an empty index type has no points, and `PEmpty` is that index type. -/
example : IsEmpty
    ((ComplexAnalytic.AnalyticSpace.sigma
      (PEmpty.elim : PEmpty.{u + 1} → ComplexAnalytic.AnalyticSpace.{u})) : Type u) :=
  ComplexAnalytic.AnalyticSpace.isEmpty_sigma _

/-- **`CategoryTheory.PreGaloisCategory` is still found there**, by search and with no hypothesis
supplied by hand beyond the emptiness: an empty space is Hausdorff, which is the only thing that
instance asks of the base. **This is what makes this section's refutation a statement about the
existence of a fibre functor** and not about either of the class's other two ingredients. -/
example : PreGaloisCategory (ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.{u}
    (ComplexAnalytic.AnalyticSpace.sigma
      (PEmpty.elim : PEmpty.{u + 1} → ComplexAnalytic.AnalyticSpace.{u}))) :=
  haveI := ComplexAnalytic.AnalyticSpace.isEmpty_sigma
    (PEmpty.elim : PEmpty.{u + 1} → ComplexAnalytic.AnalyticSpace.{u})
  inferInstance

/-- **And `CategoryTheory.GaloisCategory` is false there.** This file's `#guard_msgs` probe at that
class says search does not reach it from `[T2Space]` and `[PreconnectedSpace]`; this says no
instance of it exists at this base, which is the statement that `[Nonempty X]` on
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.galoisCategory` is a hypothesis of the
mathematics. -/
example : ¬ GaloisCategory (ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.{u}
    (ComplexAnalytic.AnalyticSpace.sigma
      (PEmpty.elim : PEmpty.{u + 1} → ComplexAnalytic.AnalyticSpace.{u}))) :=
  haveI := ComplexAnalytic.AnalyticSpace.isEmpty_sigma
    (PEmpty.elim : PEmpty.{u + 1} → ComplexAnalytic.AnalyticSpace.{u})
  ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.not_galoisCategory_of_isEmpty

end EmptyBase

section Connected

variable {Y : ComplexAnalytic.AnalyticSpace.{u}} [T2Space (Y : Type u)]
  [ConnectedSpace (Y : Type u)]

/-- A caller holding `[ConnectedSpace Y]` reaches the class by search, `ConnectedSpace` projecting
to both `PreconnectedSpace` and `Nonempty`: **this is why the instance is stated over the pair and
not over `ConnectedSpace`**, since the implication runs only this way. -/
example : GaloisCategory (ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.{u} Y) := by
  infer_instance

end Connected

end OkaTest.GaloisCategory
