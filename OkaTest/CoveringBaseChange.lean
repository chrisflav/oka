/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import OkaTest.FiniteEtaleCancel

/-!
# The continuity hypothesis of three base-change statements, and the one witness all three need

`IsCoveringMap.pullback_snd` (`Oka/Topology/Covering/Basic.lean`) base-changes a covering map
`f : E → X` along a map `g : Y → X` and asks `g` to be continuous. The set-level statement beside
it, `Function.Pullback.finite_fiber_snd`, asks for no topology at all, so a reader has every reason
to ask what the continuity is spent on. It is spent on two facts — `g ⁻¹' U` being open for an
evenly covered `U`, and the continuity of `z ↦ (g z.1 : U)` inside the inverse of the trivialisation
that proof builds over `g ⁻¹' U` — and this file compiles the fact that it cannot be recovered:
dropping it makes the conclusion false.

**`IsLocalHomeomorph.pullback_snd` (`Oka/Topology/IsLocalHomeomorph.lean`) and
`IsProperMap.pullback_snd` (`Oka/Topology/Maps/Proper/Basic.lean`) ask the same of `g`, and the one
witness below settles all three statements.** Two of the three spend the continuity on two facts and
the third on one: `IsCoveringMap.pullback_snd` on `g ⁻¹' U` being open and on the continuity of
`z ↦ (g z.1 : U)`; `IsLocalHomeomorph.pullback_snd` on `g ⁻¹' e.target` being open and on the
continuity of `y ↦ e.symm (g y)`; `IsProperMap.pullback_snd` on `f ∘ Function.Pullback.fst` tending
to `g y` along a filter, and on nothing else. **Counted instead as occurrences of the hypothesis in
the three proofs the figures are three, two and one** — `IsCoveringMap.pullback_snd`'s proof names
the openness of `g ⁻¹' U` twice for the one fact — so the two instruments disagree at that statement
and agree at the other two, which is why facts and not occurrences are what is counted here. **What
the three share is two set-level failures and not three**: at this witness the projection is not an
open map, which kills the covering-map and the local-homeomorphism conclusions through
`IsCoveringMap.isOpenMap` and `IsLocalHomeomorph.isOpenMap`, and it is not a closed map, which
kills properness through `IsProperMap.isClosedMap`.

**The heading above read *The continuity hypothesis of `IsCoveringMap.pullback_snd`, and the witness
that it is needed* until 2026-09-13**, when the two further statements were appended. **The clause
read *It is spent once, on `g ⁻¹' U` being open for an evenly covered `U`* until 2026-09-13**, when
the spend of the continuity was read off all three proofs and `IsCoveringMap.pullback_snd`'s came
out two; the same numeral was in `Oka/Topology/Covering/Basic.lean`'s docstring for that statement
and is repaired there by the same push.

## The witness

`TwoIndiscrete` (`OkaTest/FiniteEtaleCancel.lean`) is a two-element type carrying the indiscrete
topology, introduced there as the non-Hausdorff middle space of
`TwoIndiscrete.not_isClosedMap_pt_of_isClosedMap_comp`. It is reused rather than re-declared, and
this file adds `TwoIndiscrete.toBool` — the identity of the two elements, read into `Bool` and hence
into the discrete topology — to the same namespace.

Take `f` to be the identity of `Bool`, which is a covering map because both its source and its
target are discrete (`IsCoveringMap.of_discreteTopology`), and take `g` to be
`TwoIndiscrete.toBool`. The pullback is then the graph of `TwoIndiscrete.toBool` inside
`Bool × TwoIndiscrete`, and its first coordinate makes the singleton `{true}` open in it, where the
image of that singleton under `Function.Pullback.snd` is a one-element subset of `TwoIndiscrete`
and so is neither empty nor everything. A covering map is an open map
(`IsCoveringMap.isOpenMap`), so `Function.Pullback.snd` is not one.

**The conjunction says how strong the surviving hypotheses are.** The one hypothesis
`IsCoveringMap.pullback_snd` asks for besides continuity of `g` — that `f` be a covering map —
holds at this witness; the projection is a continuous bijection; and
`Function.Pullback.finite_fiber_snd` applies to it and gives finite fibres, that statement being
independent of the topology, which is the reason the two are stated apart. What fails is the
conclusion of `IsCoveringMap.pullback_snd`, the one of the two that asks for continuity.

## Main results

- `TwoIndiscrete.not_continuous_toBool`: the identity out of the indiscrete two-element space into
  the discrete one is not continuous.
- `TwoIndiscrete.not_isOpenMap_pullback_snd` and `TwoIndiscrete.not_isClosedMap_pullback_snd`: the
  projection out of the base change is **neither an open nor a closed map** at this witness. These
  are the two set-level failures the three conjunctions below read off, and they share the image
  computation `TwoIndiscrete.image_pullback_snd_fst_true`.
- `TwoIndiscrete.not_isCoveringMap_pullback_snd_of_not_continuous`: **the continuity hypothesis of
  `IsCoveringMap.pullback_snd` cannot be dropped**, stated as one conjunction with the hypotheses
  that do hold at the witness.
- `TwoIndiscrete.not_isLocalHomeomorph_pullback_snd_of_not_continuous` and
  `TwoIndiscrete.not_isProperMap_pullback_snd_of_not_continuous`: **the same for
  `IsLocalHomeomorph.pullback_snd` and for `IsProperMap.pullback_snd`.**

## What is not here

* **No witness for anything but the continuity.** Each of the three statements has exactly one
  other hypothesis — that `f` be a covering map, a local homeomorphism, or proper — and each
  conjunction below exhibits that hypothesis *holding*. Nothing here says any of the three is
  needed.
* **Nothing about the fibres.** `Function.Pullback.finite_fiber_snd` applies at this witness and two
  of the conjunctions say so; what fails is never the fibres.
-/

namespace TwoIndiscrete

/-- **The two indistinguishable points, read as the two points of `Bool`.** The identity of the
underlying type, so it is a bijection; what it is not is continuous, since its source carries the
indiscrete topology and its target the discrete one.

`TwoIndiscrete` is a `def` and not an `abbrev` for the reason `OkaTest/FiniteEtaleCancel.lean`
gives, so this map has to be written down in order to be spoken about at all: a term of the
underlying type has its type inferred as `Bool` and carries `Bool`'s discrete topology with it. -/
def toBool : TwoIndiscrete → Bool := fun b ↦ b

/-- **The identity out of the indiscrete two-element space is not continuous.** The preimage of
`{true}` is a one-element subset, which under the indiscrete topology is neither empty nor
everything and so is not open (`TopologicalSpace.isOpen_top_iff`). -/
theorem not_continuous_toBool : ¬ Continuous toBool := by
  intro h
  rcases (TopologicalSpace.isOpen_top_iff (toBool ⁻¹' {true})).1
    ((isOpen_discrete _).preimage h) with hc | hc
  · have hmem : ((true : Bool) : TwoIndiscrete) ∈ toBool ⁻¹' {true} := rfl
    rw [hc] at hmem; exact hmem
  · have hmem : ((false : Bool) : TwoIndiscrete) ∈ toBool ⁻¹' {true} := hc ▸ Set.mem_univ _
    exact Bool.false_ne_true hmem

/-- **The image under `Function.Pullback.snd` of the subset the first coordinate cuts out** is the
one-element subset `TwoIndiscrete.toBool ⁻¹' {true}`.

Stated once and consumed twice below, at the two set-level properties of the projection the
three witnesses rest on. The
forward inclusion is the defining equation of a point of the pullback and the backward one names
the point `(true, b)`, which lies in the pullback exactly when `b` is in that subset. -/
theorem image_pullback_snd_fst_true :
    (Function.Pullback.snd : (id : Bool → Bool).Pullback toBool → TwoIndiscrete) ''
      ((fun p : (id : Bool → Bool).Pullback toBool ↦ (p : Bool × TwoIndiscrete).1) ⁻¹' {true})
      = toBool ⁻¹' {true} := by
  ext b
  refine ⟨?_, fun hb ↦ ⟨⟨(true, b), hb.symm⟩, rfl, rfl⟩⟩
  rintro ⟨p, hp, rfl⟩
  exact p.2.symm.trans hp

/-- **A one-element subset of the indiscrete two-element space is not closed**, its complement
being the other one-element subset and so neither empty nor everything
(`TopologicalSpace.isOpen_top_iff`).

This is the closed-set counterpart of the openness argument in
`TwoIndiscrete.not_continuous_toBool`, and it is what the properness witness below needs: a proper
map is a closed map and not an open one. -/
theorem not_isClosed_toBool_preimage_true : ¬ IsClosed (toBool ⁻¹' {true}) := by
  intro h
  rcases (TopologicalSpace.isOpen_top_iff ((toBool ⁻¹' {true})ᶜ)).1 h.isOpen_compl with hc | hc
  · have hmem : ((false : Bool) : TwoIndiscrete) ∈ (toBool ⁻¹' {true})ᶜ := Bool.false_ne_true
    rw [hc] at hmem; exact hmem
  · have hmem : ((true : Bool) : TwoIndiscrete) ∈ (toBool ⁻¹' {true})ᶜ := hc ▸ Set.mem_univ _
    exact hmem rfl

/-- **`Function.Pullback.snd` is not a closed map at this witness.**

The subset the first coordinate cuts out is *closed* as well as open — the first coordinate is
continuous into a discrete space and `{true}` is closed there — and its image is the subset
`TwoIndiscrete.not_isClosed_toBool_preimage_true` shows is not closed. -/
theorem not_isClosedMap_pullback_snd :
    ¬ IsClosedMap (Function.Pullback.snd :
      (id : Bool → Bool).Pullback toBool → TwoIndiscrete) := by
  intro h
  have himg := h ((fun p : (id : Bool → Bool).Pullback toBool ↦
      (p : Bool × TwoIndiscrete).1) ⁻¹' {true})
    (IsClosed.preimage (continuous_fst.comp continuous_subtype_val)
      (isClosed_discrete ({true} : Set Bool)))
  rw [image_pullback_snd_fst_true] at himg
  exact not_isClosed_toBool_preimage_true himg

/-- **`Function.Pullback.snd` is not an open map at this witness**, which is what
`TwoIndiscrete.not_isCoveringMap_pullback_snd` and the local-homeomorphism witness below both
consume.

The subset the first coordinate cuts out is open and its image is the subset
`TwoIndiscrete.not_continuous_toBool` shows is not open. -/
theorem not_isOpenMap_pullback_snd :
    ¬ IsOpenMap (Function.Pullback.snd :
      (id : Bool → Bool).Pullback toBool → TwoIndiscrete) := by
  intro h
  have himg := h ((fun p : (id : Bool → Bool).Pullback toBool ↦
      (p : Bool × TwoIndiscrete).1) ⁻¹' {true})
    ((continuous_fst.comp continuous_subtype_val).isOpen_preimage _
      (isOpen_discrete ({true} : Set Bool)))
  rw [image_pullback_snd_fst_true] at himg
  rcases (TopologicalSpace.isOpen_top_iff (toBool ⁻¹' {true})).1 himg with hc | hc
  · have hmem : ((true : Bool) : TwoIndiscrete) ∈ toBool ⁻¹' {true} := rfl
    rw [hc] at hmem; exact hmem
  · have hmem : ((false : Bool) : TwoIndiscrete) ∈ toBool ⁻¹' {true} := hc ▸ Set.mem_univ _
    exact Bool.false_ne_true hmem

/-- **`Function.Pullback.snd` is not a covering map at this witness.**

A covering map is an open map (`IsCoveringMap.isOpenMap`) and this projection is not one, by
`TwoIndiscrete.not_isOpenMap_pullback_snd`. -/
theorem not_isCoveringMap_pullback_snd :
    ¬ IsCoveringMap (Function.Pullback.snd :
      (id : Bool → Bool).Pullback toBool → TwoIndiscrete) :=
  fun h ↦ not_isOpenMap_pullback_snd h.isOpenMap

/-- **The continuity hypothesis of `IsCoveringMap.pullback_snd` cannot be dropped.**

`¬ Continuous TwoIndiscrete.toBool` is the hypothesis that fails and
`¬ IsCoveringMap Function.Pullback.snd` is the conclusion that fails with it. The conjuncts beside
them say how little else is wrong: the identity of `Bool` is a covering map with finite fibres,
which is everything `IsCoveringMap.pullback_snd` asks for other than the continuity;
`Function.Pullback.snd` out of the base change is continuous and bijective; and its fibres are
finite by `Function.Pullback.finite_fiber_snd`, which asks for no continuity — so what fails is the
covering conclusion and not the fibres.

Stated as one conjunction rather than as separate theorems for the reason
`TwoIndiscrete.not_isClosedMap_pt_of_isClosedMap_comp` gives: each conjunct alone is uninteresting
and what is exhibited is that they hold together. -/
theorem not_isCoveringMap_pullback_snd_of_not_continuous :
    IsCoveringMap (id : Bool → Bool) ∧
      (∀ x, ((id : Bool → Bool) ⁻¹' {x}).Finite) ∧
      Continuous (Function.Pullback.snd :
        (id : Bool → Bool).Pullback toBool → TwoIndiscrete) ∧
      Function.Bijective (Function.Pullback.snd :
        (id : Bool → Bool).Pullback toBool → TwoIndiscrete) ∧
      (∀ y, ((Function.Pullback.snd :
        (id : Bool → Bool).Pullback toBool → TwoIndiscrete) ⁻¹' {y}).Finite) ∧
      ¬ Continuous toBool ∧
      ¬ IsCoveringMap (Function.Pullback.snd :
        (id : Bool → Bool).Pullback toBool → TwoIndiscrete) :=
  ⟨IsCoveringMap.of_discreteTopology _, fun _ ↦ Set.toFinite _,
    continuous_snd.comp continuous_subtype_val,
    ⟨by
      intro p p' hpp'
      have h : (p : Bool × TwoIndiscrete).1 = toBool (p : Bool × TwoIndiscrete).2 := p.2
      have h' : (p' : Bool × TwoIndiscrete).1 = toBool (p' : Bool × TwoIndiscrete).2 := p'.2
      exact Subtype.ext (Prod.ext (h.trans ((congrArg toBool hpp').trans h'.symm)) hpp'),
      fun b ↦ ⟨⟨(toBool b, b), rfl⟩, rfl⟩⟩,
    Function.Pullback.finite_fiber_snd fun _ ↦ Set.toFinite _,
    not_continuous_toBool, not_isCoveringMap_pullback_snd⟩

/-- **The continuity hypothesis of `IsLocalHomeomorph.pullback_snd` cannot be dropped.**

The same witness as for `IsCoveringMap.pullback_snd`, and the same failure: a local homeomorphism
is an open map (`IsLocalHomeomorph.isOpenMap`) and this projection is not one. **The identity of
`Bool` is a local homeomorphism** — it is a homeomorphism — so the one surviving hypothesis holds,
and the projection is still a continuous bijection.

Stated as one conjunction for the reason
`TwoIndiscrete.not_isCoveringMap_pullback_snd_of_not_continuous` gives. -/
theorem not_isLocalHomeomorph_pullback_snd_of_not_continuous :
    IsLocalHomeomorph (id : Bool → Bool) ∧
      Continuous (Function.Pullback.snd :
        (id : Bool → Bool).Pullback toBool → TwoIndiscrete) ∧
      ¬ Continuous toBool ∧
      ¬ IsLocalHomeomorph (Function.Pullback.snd :
        (id : Bool → Bool).Pullback toBool → TwoIndiscrete) :=
  ⟨(Homeomorph.refl Bool).isLocalHomeomorph, continuous_snd.comp continuous_subtype_val,
    not_continuous_toBool, fun h ↦ not_isOpenMap_pullback_snd h.isOpenMap⟩

/-- **The continuity hypothesis of `IsProperMap.pullback_snd` cannot be dropped.**

The same witness again, and the failure is one step further out: a proper map is a *closed* map
(`IsProperMap.isClosedMap`) and this projection is not one, by
`TwoIndiscrete.not_isClosedMap_pullback_snd`. **The identity of `Bool` is proper**
(`isProperMap_id`), so the one surviving hypothesis holds; and the fibres of the projection are
finite, so what fails is neither the fibres nor a compactness condition on them but the closedness.

Stated as one conjunction for the reason
`TwoIndiscrete.not_isCoveringMap_pullback_snd_of_not_continuous` gives. -/
theorem not_isProperMap_pullback_snd_of_not_continuous :
    IsProperMap (id : Bool → Bool) ∧
      (∀ y, ((Function.Pullback.snd :
        (id : Bool → Bool).Pullback toBool → TwoIndiscrete) ⁻¹' {y}).Finite) ∧
      ¬ Continuous toBool ∧
      ¬ IsProperMap (Function.Pullback.snd :
        (id : Bool → Bool).Pullback toBool → TwoIndiscrete) :=
  ⟨isProperMap_id, Function.Pullback.finite_fiber_snd fun _ ↦ Set.toFinite _,
    not_continuous_toBool, fun h ↦ not_isClosedMap_pullback_snd h.isClosedMap⟩

end TwoIndiscrete
