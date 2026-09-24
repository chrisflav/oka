/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Mathlib.Topology.Homeomorph.Lemmas
import Oka.Topology.Connected.Clopen

/-!
# What a homeomorphism does to connected components

**A homeomorphism carries the connected component of a point to the connected component of its
image.** Mathlib has the *relative* form of that statement and not the absolute one:
`Homeomorph.image_connectedComponentIn`, in `Mathlib/Topology/Homeomorph/Lemmas.lean`, which is
this file's target. The absolute case is that statement at `Set.univ` and is
`Homeomorph.image_connectedComponent` below.

**The absolute case is reachable from Mathlib by two other routes and both ask for something to be
discharged first.** `Topology.IsCoinducing.image_connectedComponent`
(`Mathlib/Topology/Connected/Clopen.lean`) concludes the same equation for a coinducing map, but
only from a hypothesis that every fibre is connected; `Continuous.image_connectedComponent_subset`
(`Mathlib/Topology/Connected/Basic.lean`) gives one inclusion and has to be applied twice. Neither
is a rewrite a caller can use without an argument, which is what makes the named lemma worth
having. **The first result is three lines of `simpa` over the relative statement**; the second is
it composed with `connectedComponent_sigmaMk`, and the third is the second read at a
representative of each component.

**Upstreaming costs the target nothing.** `Mathlib.Topology.Connected.Clopen`, which the second
and third results reach through `Oka/Topology/Connected/Clopen.lean`, is already among the **624**
Mathlib modules in the transitive closure of `Mathlib.Topology.Homeomorph.Lemmas`, measured with
`python3 scripts/import_cost.py --target Mathlib.Topology.Homeomorph.Lemmas
Mathlib.Topology.Connected.Clopen`.

**This file and `Oka/Topology/Connected/Clopen.lean` are split by destination and the split is
measured.** `connectedComponent_sigmaMk` names no homeomorphism and goes to
`Mathlib/Topology/Connected/Clopen.lean`; every statement here names one, and putting it in that
file instead would cost that file **10** Mathlib modules —
`Mathlib.Topology.Homeomorph.Lemmas` itself and nine more,
`Mathlib.Topology.Baire.Lemmas` and `Mathlib.Topology.GDelta.Basic` among them — by the same
script run the other way round. `README.md`'s mirror-tree section is what asks for the split to be
by destination and not by subject.

## Main results

- `Homeomorph.image_connectedComponent`: **the image of a connected component under a
  homeomorphism is the connected component of the image.**
- `Homeomorph.connectedComponent_sigma`: **so in a space homeomorphic to a disjoint union of
  connected spaces the components are the preimages of the members**, one for each index.
- `Homeomorph.finite_connectedComponents_of_sigma`: **and there are finitely many of them** when
  the index type is finite.

## What is not here

* **Nothing for a continuous bijection**, and the hypothesis is not idle: the identity from a
  two-point discrete space to a two-point indiscrete one is a continuous bijection whose source
  has two components and whose target has one, so it carries neither a component nor the count.
  Every statement below asks for a homeomorphism for that reason.
* **No statement that the index type is the type of components.** The third result below is a
  surjection from the index type onto the components and not a bijection; it would be one exactly
  when the members are pairwise distinct as subsets, and no consumer of this file asks. The second
  result is what a consumer that wants the components individually uses.
* **Nothing about `connectedComponentIn`**, the relative notion, beyond the one application of
  Mathlib's relative statement inside the first proof.
-/

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- **The image of a connected component under a homeomorphism is the connected component of the
image of the point.**

`Homeomorph.image_connectedComponentIn` at `Set.univ`, with `connectedComponentIn_univ` on both
sides and `Set.range_eq_univ` for the image of `Set.univ` under a surjection. -/
theorem Homeomorph.image_connectedComponent (h : X ≃ₜ Y) (x : X) :
    h '' connectedComponent x = connectedComponent (h x) := by
  simpa [connectedComponentIn_univ, Set.image_univ, Set.range_eq_univ.2 h.surjective] using
    h.image_connectedComponentIn (Set.mem_univ x)

variable {ι : Type*} {Z : ι → Type*} [∀ i, TopologicalSpace (Z i)]

/-- **In a space homeomorphic to a disjoint union of connected spaces, the connected component of
a point is the preimage of the member the point lands in.**

`connectedComponent_sigmaMk` transported along the homeomorphism by
`Homeomorph.image_connectedComponent`, an image of a component being read as a preimage through
`Function.Injective.preimage_image`.

**Neither ingredient is about the space `X`**, which carries no hypothesis of its own: what makes
the components the members is that the members are connected and clopen, and the homeomorphism is
what makes the decomposition a decomposition of `X`. -/
theorem Homeomorph.connectedComponent_sigma [∀ i, ConnectedSpace (Z i)] (h : X ≃ₜ Σ i, Z i)
    (x : X) : connectedComponent x = h ⁻¹' Set.range (Sigma.mk (h x).1) := by
  rw [← h.injective.preimage_image (connectedComponent x), h.image_connectedComponent]
  exact congrArg _ (connectedComponent_sigmaMk (h x).1 (h x).2)

/-- **A space homeomorphic to a disjoint union of finitely many connected spaces has finitely many
connected components.**

The map sending an index to the component of an arbitrary point of that member is surjective: by
the statement above, the component of a point `x` and the component of an arbitrary point of the
member `x` lands in are the preimage of the same member's range, hence equal.
`Classical.arbitrary` is available because a `ConnectedSpace` is nonempty, and that is the only
place the nonemptiness half of the class is used.

**The conclusion is `Finite` and not a cardinality.** `Nat.card` of the components is at most the
cardinality of the index type by the same surjection; nothing here states it, because the count
agrees with the index type only when the members are distinct, which this does not assume. -/
theorem Homeomorph.finite_connectedComponents_of_sigma [Finite ι] [∀ i, ConnectedSpace (Z i)]
    (h : X ≃ₜ Σ i, Z i) : Finite (ConnectedComponents X) :=
  Finite.of_surjective
    (fun i : ι ↦ ConnectedComponents.mk (h.symm ⟨i, Classical.arbitrary (Z i)⟩))
    fun q ↦ by
      obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe q
      refine ⟨(h x).1, ?_⟩
      rw [ConnectedComponents.coe_eq_coe, h.connectedComponent_sigma, h.connectedComponent_sigma,
        h.apply_symm_apply]
