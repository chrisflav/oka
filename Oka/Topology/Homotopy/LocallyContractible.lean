/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Mathlib.Topology.Homotopy.LocallyContractible

/-!
# Classical local contractibility is local, and passes along open embeddings

Mathlib's `LocallyContractibleSpace X` (`Mathlib/Topology/Homotopy/LocallyContractible.lean`) is
the classical notion: every neighbourhood `U` of every point `x` contains a neighbourhood `V` of
`x` whose inclusion into `U` is null-homotopic. At `v4.32.0` Mathlib proves the permanence
properties of the *strong* notion `StronglyLocallyContractibleSpace` (open embeddings, open
subsets, products) but none for the classical one, which is a `def` and not a class. This file
supplies the three that a gluing argument needs.

The notion is pointwise, so the work is done at a point: `LocallyContractibleAt x` is the
condition of `LocallyContractibleSpace` at the single point `x`, and
`LocallyContractibleAt.of_isOpenEmbedding` / `LocallyContractibleAt.image_of_isOpenEmbedding` say
that an open embedding `e` neither creates nor destroys it: `x` satisfies it in the source iff
`e x` satisfies it in the target. Everything else is a corollary.

## Main results

- `Topology.IsOpenEmbedding.locallyContractibleSpace`: the source of an open embedding into a
  locally contractible space is locally contractible; `IsOpen.locallyContractibleSpace` is the case
  of an open subspace.
- `Homeomorph.locallyContractibleSpace`: local contractibility is invariant under homeomorphism.
- `LocallyContractibleSpace.of_isOpenEmbedding_cover`: **local contractibility is local**: if every
  point lies in the image of an open embedding from a locally contractible space, the space is
  locally contractible. `LocallyContractibleSpace.of_isOpen_cover` is the version with open
  subsets.

There is no analytic content here; the file mirrors the Mathlib path it would be upstreamed to.
-/

open Topology Filter Set ContinuousMap

universe v

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- **Classical local contractibility at a point**: every neighbourhood `U` of `x` contains a
neighbourhood `V` of `x` whose inclusion into `U` is null-homotopic. `LocallyContractibleSpace X`
is this at every point (`locallyContractibleSpace_iff_forall_locallyContractibleAt`). -/
def LocallyContractibleAt (x : X) : Prop :=
  ∀ U : Set X, U ∈ 𝓝 x → ∃ (V : Set X) (hVU : V ⊆ U), V ∈ 𝓝 x ∧ Nullhomotopic (inclusion hVU)

/-- `LocallyContractibleSpace X` is `LocallyContractibleAt` at every point, by definition. -/
theorem locallyContractibleSpace_iff_forall_locallyContractibleAt :
    LocallyContractibleSpace X ↔ ∀ x : X, LocallyContractibleAt x :=
  Iff.rfl

namespace LocallyContractibleAt

variable {e : Y → X} (he : IsOpenEmbedding e)
include he

/-- A point of `e '' A`, for an embedding `e`, as a point of `A`: continuous, and a section of
`e`. -/
private theorem exists_continuous_section (A : Set Y) :
    ∃ s : C(e '' A, A), ∀ w, e (s w) = w := by
  have h (w : e '' A) : ∃ a : A, e a = w := by
    obtain ⟨a, ha, hw⟩ := w.2
    exact ⟨⟨a, ha⟩, hw⟩
  choose s hs using h
  refine ⟨⟨s, ?_⟩, hs⟩
  rw [(he.isEmbedding.comp IsEmbedding.subtypeVal).continuous_iff]
  have : (e ∘ Subtype.val) ∘ s = Subtype.val := funext hs
  rw [this]
  exact continuous_subtype_val

/-- **An open embedding carries local contractibility at `y` to local contractibility at
`e y`.** -/
theorem image_of_isOpenEmbedding {y : Y} (hy : LocallyContractibleAt y) :
    LocallyContractibleAt (e y) := by
  intro U hU
  obtain ⟨V, hVU, hV, hnull⟩ := hy (e ⁻¹' U) (he.continuous.continuousAt.preimage_mem_nhds hU)
  refine ⟨e '' V, image_subset_iff.2 hVU, he.isOpenMap.image_mem_nhds hV, ?_⟩
  obtain ⟨s, hs⟩ := exists_continuous_section he V
  let φ : C(e ⁻¹' U, U) := ⟨fun u ↦ ⟨e u, u.2⟩, by fun_prop⟩
  convert (hnull.comp_right φ).comp_left s using 1
  ext w
  exact (hs w).symm

/-- **An open embedding reflects local contractibility**: if `e y` satisfies it in the target,
`y` satisfies it in the source. -/
theorem of_isOpenEmbedding {y : Y} (hy : LocallyContractibleAt (e y)) :
    LocallyContractibleAt y := by
  intro U hU
  obtain ⟨V, hVU, hV, hnull⟩ := hy (e '' U) (he.isOpenMap.image_mem_nhds hU)
  have hV'U : e ⁻¹' V ⊆ U := fun v hv ↦ by
    obtain ⟨u, hu, huv⟩ := hVU hv
    exact he.injective huv ▸ hu
  refine ⟨e ⁻¹' V, hV'U, he.continuous.continuousAt.preimage_mem_nhds hV, ?_⟩
  obtain ⟨s, hs⟩ := exists_continuous_section he U
  let ψ : C(e ⁻¹' V, V) := ⟨fun v ↦ ⟨e v, v.2⟩, by fun_prop⟩
  convert (hnull.comp_right s).comp_left ψ using 1
  ext v
  exact he.injective (hs (Set.inclusion hVU (ψ v))).symm

end LocallyContractibleAt

/-- **The source of an open embedding into a locally contractible space is locally
contractible.** -/
theorem Topology.IsOpenEmbedding.locallyContractibleSpace {e : Y → X} (he : IsOpenEmbedding e)
    (hX : LocallyContractibleSpace X) : LocallyContractibleSpace Y :=
  fun y ↦ LocallyContractibleAt.of_isOpenEmbedding he (hX (e y))

/-- **An open subspace of a locally contractible space is locally contractible.** -/
theorem IsOpen.locallyContractibleSpace {U : Set X} (hU : IsOpen U)
    (hX : LocallyContractibleSpace X) : LocallyContractibleSpace U :=
  hU.isOpenEmbedding_subtypeVal.locallyContractibleSpace hX

/-- **Local contractibility is invariant under homeomorphism.** -/
theorem Homeomorph.locallyContractibleSpace (e : X ≃ₜ Y) (hX : LocallyContractibleSpace X) :
    LocallyContractibleSpace Y := fun y ↦ by
  have h := LocallyContractibleAt.image_of_isOpenEmbedding e.isOpenEmbedding (hX (e.symm y))
  rwa [e.apply_symm_apply] at h

/-- **Local contractibility is local**: if every point of `X` lies in the image of an open
embedding from a locally contractible space, then `X` is locally contractible. -/
theorem LocallyContractibleSpace.of_isOpenEmbedding_cover
    (h : ∀ x : X, ∃ (Y : Type v) (_ : TopologicalSpace Y) (e : Y → X),
      IsOpenEmbedding e ∧ x ∈ range e ∧ LocallyContractibleSpace Y) :
    LocallyContractibleSpace X := fun x ↦ by
  obtain ⟨Y, _, e, he, ⟨y, rfl⟩, hY⟩ := h x
  exact LocallyContractibleAt.image_of_isOpenEmbedding he (hY y)

/-- **Local contractibility is local**, for a cover by open subsets: if every point of `X` has an
open neighbourhood that is locally contractible, then `X` is locally contractible. -/
theorem LocallyContractibleSpace.of_isOpen_cover
    (h : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ LocallyContractibleSpace U) :
    LocallyContractibleSpace X := fun x ↦ by
  obtain ⟨U, hU, hxU, hLC⟩ := h x
  exact LocallyContractibleAt.image_of_isOpenEmbedding (y := ⟨x, hxU⟩)
    hU.isOpenEmbedding_subtypeVal (hLC _)
