/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
import Mathlib.Topology.Homotopy.LocallyContractible
import Oka.Topology.Covering.PathCover

/-!
# Locally contractible spaces are locally path connected and semilocally simply connected

Mathlib's `LocallyContractibleSpace` is the classical (weak) notion: every neighbourhood `U` of a
point contains a neighbourhood `V` whose inclusion into `U` is null-homotopic. Mathlib proves that
the *strong* notion (`StronglyLocallyContractibleSpace`) implies local path connectedness; for the
weak notion neither of the two consequences below is in Mathlib.

## Main results

- `LocallyContractibleSpace.locallyPathConnectedSpace`.
- `LocallyContractibleSpace.semilocallySimplyConnected`: in the path form `IsPathSimple` used by
  `Oka/Topology/Covering/PathCover.lean`. The proof is the naturality of the homotopy between the
  inclusion `V ↪ B` and a constant map (`Path.Homotopic.map_trans_evalAt`).
-/

open Topology Set CategoryTheory ContinuousMap

variable {X : Type*} [TopologicalSpace X]

/-- **A locally contractible space is locally path connected.** If `V ⊆ U` is a neighbourhood of
`x` whose inclusion into `U` is homotopic to the constant map at `c`, every point of `V` is joined
to `c` inside `U`. -/
theorem LocallyContractibleSpace.locallyPathConnectedSpace (h : LocallyContractibleSpace X) :
    LocallyPathConnectedSpace X := by
  rw [locallyPathConnectedSpace_iff_pathComponentIn_mem_nhds]
  intro x U hU hxU
  obtain ⟨V, hVU, hV, c, ⟨F⟩⟩ := h x U (hU.mem_nhds hxU)
  have hj (v : X) (hv : v ∈ V) : JoinedIn U v c :=
    ⟨(F.evalAt ⟨v, hv⟩).map continuous_subtype_val, fun t ↦ (F.evalAt ⟨v, hv⟩ t).2⟩
  exact Filter.mem_of_superset hV fun v hv ↦ (hj x (mem_of_mem_nhds hV)).trans (hj v hv).symm

/-- **A locally contractible space is semilocally simply connected**: every point has a
neighbourhood `V` in which any two paths with the same end points are homotopic in `X`. -/
theorem LocallyContractibleSpace.semilocallySimplyConnected (h : LocallyContractibleSpace X) :
    SemilocallySimplyConnected X := by
  intro x
  obtain ⟨V, hVU, hV, c, ⟨F⟩⟩ := h x univ Filter.univ_mem
  let ι : C(V, X) := ⟨Subtype.val, continuous_subtype_val⟩
  let F' : Homotopy ι (ContinuousMap.const V c.1) :=
    (Homotopy.refl (⟨Subtype.val, continuous_subtype_val⟩ : C((univ : Set X), X))).comp F
  refine ⟨V, hV, fun y z γ γ' hγ hγ' ↦ ?_⟩
  have hy : y ∈ V := γ.source ▸ hγ 0
  have hz : z ∈ V := γ.target ▸ hγ 1
  let toV (δ : Path y z) (hδ : ∀ t, δ t ∈ V) : Path (⟨y, hy⟩ : V) ⟨z, hz⟩ :=
    { toFun t := ⟨δ t, hδ t⟩
      continuous_toFun := by fun_prop
      source' := Subtype.ext δ.source
      target' := Subtype.ext δ.target }
  have key (δ : Path y z) (hδ : ∀ t, δ t ∈ V) :
      PathCover.hom δ ≫ PathCover.hom (F'.evalAt ⟨z, hz⟩) =
        PathCover.hom (F'.evalAt ⟨y, hy⟩) ≫ PathCover.hom (Path.refl c.1) := by
    have := Path.Homotopic.map_trans_evalAt F' (toV δ hδ)
    rw [← PathCover.hom_trans, ← PathCover.hom_trans]
    exact Path.Homotopic.Quotient.eq.2 this
  have := (key γ hγ).trans (key γ' hγ').symm
  exact Path.Homotopic.Quotient.eq.1 ((cancel_mono _).1 this)

/-- **Local path connectedness lifts along local homeomorphisms.** -/
theorem IsLocalHomeomorph.locallyPathConnectedSpace {E Y : Type*} [TopologicalSpace E]
    [TopologicalSpace Y] [LocallyPathConnectedSpace Y] {p : E → Y} (hp : IsLocalHomeomorph p) :
    LocallyPathConnectedSpace E := by
  rw [locallyPathConnectedSpace_iff_pathComponentIn_mem_nhds]
  intro e U hU heU
  obtain ⟨φ, he, rfl⟩ := hp e
  have hW : φ.source ∩ U ∈ 𝓝 e :=
    Filter.inter_mem (φ.open_source.mem_nhds he) (hU.mem_nhds heU)
  have hP := pathComponentIn_mem_nhds (φ.image_mem_nhds he hW)
  refine Filter.mem_of_superset
    (Filter.inter_mem (φ.open_source.mem_nhds he) (φ.continuousAt he hP)) ?_
  rintro e' ⟨he's, δ, hδ⟩
  have hmem (t : unitInterval) : δ t ∈ φ.target := by
    obtain ⟨x, hx, hxe⟩ := hδ t
    exact hxe ▸ φ.map_source hx.1
  refine ⟨⟨⟨fun t ↦ φ.symm (δ t), φ.continuousOn_symm.comp_continuous δ.continuous hmem⟩,
    by simp [φ.left_inv he], by simp [φ.left_inv he's]⟩, fun t ↦ ?_⟩
  obtain ⟨x, hx, hxe⟩ := hδ t
  change φ.symm (δ t) ∈ U
  rw [← hxe, φ.left_inv hx.1]
  exact hx.2
