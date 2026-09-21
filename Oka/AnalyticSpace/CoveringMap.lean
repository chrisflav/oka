/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.AnalyticSpace.LocalIso
import Oka.Topology.Covering.Basic

/-!
# A finite étale morphism of complex analytic spaces is a covering map

The third rung of the Riemann existence theorem's analytic side: the underlying map of a finite
étale morphism is a covering map in the sense of `IsCoveringMap`. The first rung is
`Oka/AnalyticSpace/Finite.lean` and the second `Oka/AnalyticSpace/LocalIso.lean`.

## What the rung actually needs

`ComplexAnalytic.AnalyticSpace.IsFinite` is *closed with finite fibres* and
`ComplexAnalytic.AnalyticSpace.IsLocalIso` carries `IsLocalHomeomorph` as its topological field.
Those three conditions are exactly the hypotheses of Mathlib's
`IsClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn`, so all of the mathematics here is Mathlib's;
`IsClosedMap.isCoveringMap_of_isLocalHomeomorph` in `Oka/Topology/Covering/Basic.lean` is that
theorem at `Set.univ` and is the only thing this file uses. **The stalk field of `IsLocalIso` is
not used**, and cannot be: `IsCoveringMap` is a condition on the underlying map alone.

**The source is required Hausdorff, and for a general analytic space this development does not
give that for free.** `ComplexAnalytic.AnalyticSpace` imposes no separation axiom — see
`Oka/AnalyticSpace/Basic.lean`, which says so for the same reason `AlgebraicGeometry.Scheme` does
— so `[T2Space X]` is a genuine hypothesis on the class and not a consequence of it. It is
Mathlib's hypothesis, used to separate the finitely many points of a fibre, and it is where the
statement below is weaker than the classical one, which is stated for Hausdorff spaces throughout.

**At the spaces this development constructs it is found, and that sentence used to stand without
this one.** `Oka/AnalyticSpace/Hausdorff.lean` gives the instance for a zero locus inside an open
subset of `ℂ^n` and for an open subspace of any Hausdorff analytic space, and
`Oka/Analytification/Hausdorff.lean` for an analytification; between them a caller who built the
source out of polynomials supplies nothing.
`ComplexAnalytic.isCoveringMap_base_restrictHom_analytificationMap_etalePresHom_comp` is what that
buys — the theorem below at the analytification of a standard étale morphism — and it is the
second application of this rung anywhere, `ComplexAnalytic.isCoveringMap_base_sq`
(`OkaTest/FiniteMorphism.lean`) being the first and
`ComplexAnalytic.isCoveringMap_base_restrictHom_analytificationMap_etalePresHom`
(`Oka/Analytification/HausdorffBase.lean`) the third since 2026-09-21, at the structure map to
`X^an` over a presented base rather than at the composite to `ℂ^n`. **No wording was retired
here**: both ordinals were right when written and are right now, and the sentence ended at the
second only because there was no third. **What stays true is the hypothesis**: `X` is
arbitrary below and no instance fires at a variable.

**Connectedness of the target is not needed for the rung**, and `Oka/AnalyticSpace/LocalIso.lean`
used to phrase it as being about a connected base, which the argument never uses: a point outside
the range is evenly covered by the empty index type.

## What connectedness *is* for, and it is now here

`ComplexAnalytic.AnalyticSpace.nonempty_homeomorph_fiber_of_isFiniteEtale`: over a **preconnected**
target, any two fibres of a finite étale morphism are homeomorphic, and
`ComplexAnalytic.AnalyticSpace.card_fiber_eq_of_isFiniteEtale` is the same statement counted. That
is the *number of sheets*, and it is the statement the connectedness hypothesis the earlier
phrasing carried was reaching for.

None of it is analytic. It is `IsCoveringMap.nonempty_homeomorph_fiber` in
`Oka/Topology/Covering/Basic.lean` — a clopen argument resting on local constancy of the fibre —
composed with the rung above, and the module docstring there is where the mathematics is
described.

**`Nat.card` is not a junk value here, and that is worth saying because in general it is.**
`Nat.card` of an infinite type is `0`, so an equality of `Nat.card`s is uninformative unless the
types are known finite. They are: `ComplexAnalytic.AnalyticSpace.IsFinite.finite_fiber` is a field
of the hypothesis. A reader who does not have that in view cannot distinguish
`card_fiber_eq_of_isFiniteEtale` from `0 = 0`, so the homeomorphism form is stated as well and is
the one that survives without finiteness.

**`PreconnectedSpace` and not `ConnectedSpace`**, for the reason given in the mirror-tree file: the
base being nonempty is never used.

## What is not here

* **The degree of a finite étale morphism that is neither the squaring map nor a trivial cover.**
  The bullet that used to stand here said no particular morphism had any particular degree
  computed, and then that exactly one did. Both are retired. The value is known for two things
  now, and they are known for unrelated reasons:
  `ComplexAnalytic.card_fiber_base_sq` in `OkaTest/FiniteMorphism.lean` puts every fibre of the
  squaring map of the punctured line at **2** points — a statement about roots in `ℂ` and not
  about covering maps, its content being `IsAlgClosed.card_setOf_pow_eq` — and
  `ComplexAnalytic.AnalyticSpace.card_fiber_sigmaFold` in
  `Oka/AnalyticSpace/SigmaFiniteEtale.lean` puts every fibre of the trivial `ι`-sheeted cover
  `∐_{i : ι} X ⟶ X` at `Nat.card ι` points, for **every** `ι` and every `X`, with no analysis in
  it at all. So the constant is realised at every value and not only at 2; what is still true is
  that no morphism outside those two descriptions has a computed degree, and in particular
  **nothing here computes the degree of a cover that is not trivial and not the squaring map.**
* **A `degree` function on morphisms — this is no longer absent, and it is not in this file.**
  The bullet that used to stand here said a `Nat`-valued definition would carry a
  well-definedness obligation and that nothing consumed one. Both halves are answered in
  `Oka/AnalyticSpace/Degree.lean`: `ComplexAnalytic.AnalyticSpace.degree_eq_card_fiber` is the
  obligation, and it is `ComplexAnalytic.AnalyticSpace.card_fiber_eq_of_isFiniteEtale` — the
  theorem below — read at the definition, so this file is where its content lives; and
  `ComplexAnalytic.AnalyticSpace.isHomeomorph_base_of_degree_eq_one` is the consumer.

  **Multiplicativity of the degree in a composite stood in this sentence as absent and is not
  absent any more**: `ComplexAnalytic.AnalyticSpace.degree_comp` is in that same file, and the
  theorem below is again where its content lives — the fibrewise count is elementary and what
  costs the hypotheses is `ComplexAnalytic.AnalyticSpace.card_fiber_eq_of_isFiniteEtale` applied
  at each factor, so the `[T2Space]` and `[PreconnectedSpace]` it carries are this file's and not
  the count's. **What is still absent is any consequence of the degree that sees the structure
  sheaves rather than the underlying map**, which is the other half of the sentence this paragraph
  replaces and is untouched by that theorem.
* **The converse for a *given* morphism.** `IsCoveringMap.isLocalHomeomorph` returns the
  topological field of `IsLocalIso`, but no topological hypothesis can return the stalk field of a
  morphism whose structure sheaves are already fixed, so there is no `↔` and none is stated.
  **What a topological hypothesis does give is a morphism**, once the source is allowed a
  structure sheaf of its own: `Oka/AnalyticSpace/CoveringSpace.lean` puts the inverse image of
  `𝒪_Y` on the source of a covering map with finite fibres and gets `IsFiniteEtale`, with the
  stalk field free because every stalk map of an inverse image is an isomorphism. That is a
  construction and not a converse. **The two are now comparable, and that still does not close
  this bullet**: `ComplexAnalytic.AnalyticSpace.exists_iso_coveringSpace` in that file identifies
  the source of any morphism satisfying `ComplexAnalytic.AnalyticSpace.IsLocalIso` with the space
  built on that morphism's own base map, compatibly with the two maps to the base — but it reads
  `IsLocalIso` as a *hypothesis* rather than producing it, so what a topological hypothesis would
  have to supply is exactly what it assumes. The comparison is available; the implication is not.
* **The Riemann existence theorem**, and any statement relating covers to field extensions.
* **The analytification of a finite étale morphism**, and **Grauert's finite mapping theorem** —
  the two absences `Oka/AnalyticSpace/LocalIso.lean` and `Oka/AnalyticSpace/Finite.lean` record.

## Main results

- `ComplexAnalytic.AnalyticSpace.isCoveringMap_base_of_isFiniteEtale`: **the underlying map of a
  finite étale morphism out of a Hausdorff analytic space is a covering map.**
- `ComplexAnalytic.AnalyticSpace.nonempty_homeomorph_fiber_of_isFiniteEtale` and
  `ComplexAnalytic.AnalyticSpace.card_fiber_eq_of_isFiniteEtale`: **the number of sheets is
  constant over a preconnected base.**

## References

- [Hans Grauert and Reinhold Remmert, *Coherent analytic sheaves*][grauert-remmert1984]
-/

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry Topology

universe u

namespace ComplexAnalytic.AnalyticSpace

/-- **The underlying map of a finite étale morphism out of a Hausdorff analytic space is a
covering map.**

The three inputs are the two fields of `ComplexAnalytic.AnalyticSpace.IsFinite` and the
topological field of `ComplexAnalytic.AnalyticSpace.IsLocalIso`; the stalk field plays no part,
since `IsCoveringMap` sees only the underlying map. `[T2Space X]` is not automatic — an analytic
space is not assumed Hausdorff here — and the target is not assumed connected, which the module
docstring explains.

Stated for `ComplexAnalytic.AnalyticSpace.IsFiniteEtale` rather than for the two conditions
separately because that is the class the Riemann existence theorem is about; its two fields are
instances, so the proof below reads them off. -/
theorem isCoveringMap_base_of_isFiniteEtale {X Y : AnalyticSpace.{u}} (f : X ⟶ Y)
    [IsFiniteEtale f] [T2Space X] : IsCoveringMap f.toLRSHom.base :=
  (IsFinite.isClosedMap (f := f)).isCoveringMap_of_isLocalHomeomorph
    (fun y ↦ have := IsFinite.finite_fiber (f := f) y; Set.toFinite _)
    IsLocalIso.isLocalHomeomorph

/-- **The number of sheets of a finite étale morphism is constant over a preconnected base**, in
the form that does not mention counting: any two fibres are homeomorphic.

The rung above, then `IsCoveringMap.nonempty_homeomorph_fiber`. Nothing analytic is added; the
content is the clopen argument in `Oka/Topology/Covering/Basic.lean`, and the only reason this
statement exists separately is that the two hypotheses it needs — `[T2Space X]` on the source and
`[PreconnectedSpace Y]` on the target — belong to different halves of the composite and neither is
automatic for an analytic space.

`Nonempty` rather than a chosen homeomorphism: the identification comes from an evenly covered
neighbourhood and depends on it. -/
theorem nonempty_homeomorph_fiber_of_isFiniteEtale {X Y : AnalyticSpace.{u}} (f : X ⟶ Y)
    [IsFiniteEtale f] [T2Space X] [PreconnectedSpace Y] (y₁ y₂ : Y) :
    Nonempty ((f.toLRSHom.base ⁻¹' {y₁}) ≃ₜ (f.toLRSHom.base ⁻¹' {y₂})) :=
  IsCoveringMap.nonempty_homeomorph_fiber (isCoveringMap_base_of_isFiniteEtale f) y₁ y₂

/-- **The same, counted.**

`Nat.card` is the honest spelling here **only because the fibres are known finite**:
`ComplexAnalytic.AnalyticSpace.IsFinite.finite_fiber` is a field of `IsFiniteEtale`, so no junk
value is involved. Without that this would be `0 = 0` for a morphism with infinite fibres, which
is why `ComplexAnalytic.AnalyticSpace.nonempty_homeomorph_fiber_of_isFiniteEtale` is stated too
and is the form to quote when finiteness is not in hand.

It says the fibres all have the same size; it does **not** say what that size is. Computing it for
a given morphism is a separate matter with no covering-space content — see the module
docstring. -/
theorem card_fiber_eq_of_isFiniteEtale {X Y : AnalyticSpace.{u}} (f : X ⟶ Y)
    [IsFiniteEtale f] [T2Space X] [PreconnectedSpace Y] (y₁ y₂ : Y) :
    Nat.card (f.toLRSHom.base ⁻¹' {y₁}) = Nat.card (f.toLRSHom.base ⁻¹' {y₂}) :=
  Nat.card_congr (nonempty_homeomorph_fiber_of_isFiniteEtale f y₁ y₂).some.toEquiv

end ComplexAnalytic.AnalyticSpace
