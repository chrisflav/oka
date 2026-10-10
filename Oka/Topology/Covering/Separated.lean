/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.SeparatedMap

/-!
# A closed separated local homeomorphism with finite fibres is a covering map

Mathlib's `IsClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn` asks the total space to be
Hausdorff, which it uses only to separate the finitely many points of one fibre. A **separated
map** (`IsSeparatedMap`) separates exactly such points, so the same proof goes through; this is
what is needed over a base that is not Hausdorff, e.g. the analytification of a non-separated
scheme. The proof of `IsClosedMap.isEvenlyCovered_of_openPartialHomeomorph_of_isSeparatedMap` is
Mathlib's proof of `IsClosedMap.isEvenlyCovered_of_openPartialHomeomorph` with that one step
replaced.

## Main results

- `IsClosedMap.isCoveringMap_of_isLocalHomeomorph_of_isSeparatedMap`.
-/

open Bundle Topology

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {f : E → X}

open Set in
/-- If `f : E → X` is a closed separated map between topological spaces, such that the
fiber over a point `x : X` is finite and `f` restricts to a homeomorphism on a neighborhood of
every point of the fiber, then `x` admits an evenly covered neighborhood. -/
theorem IsClosedMap.isEvenlyCovered_of_openPartialHomeomorph_of_isSeparatedMap {x : X}
    (hsep : IsSeparatedMap f) (hf : IsClosedMap f) (fin : (f ⁻¹' {x}).Finite)
    (h : ∀ e ∈ f ⁻¹' {x}, ∃ φ : OpenPartialHomeomorph E X, e ∈ φ.source ∧ φ = f) :
    IsEvenlyCovered f x (f ⁻¹' {x}) := by
  have : DiscreteTopology (f ⁻¹' {x}) :=
    (IsDiscrete.of_openPartialHomeomorph f subset_rfl h).1
  /- for each preimage e of x, choose a homeomorphism φₑ
    from a neighborhood of e to its image -/
  choose φ hφ using fun e : f ⁻¹' {x} ↦ h e e.2
  -- separately, choose pairwise disjoint neighborhoods Vₑ by Hausdorff-ness
  have hnhds : (f ⁻¹' {x}).PairwiseDisjoint 𝓝 := fun e he e' he' hne ↦ by
    obtain ⟨s₁, s₂, hs₁, hs₂, he₁, he₂, hs⟩ :=
      hsep e e' ((he : f e = x).trans (he' : f e' = x).symm) hne
    exact Filter.disjoint_of_disjoint_of_mem hs (hs₁.mem_nhds he₁) (hs₂.mem_nhds he₂)
  have ⟨V, hV, disj⟩ := hnhds.exists_mem_filter_basis fin nhds_basis_opens
  -- let Vₑ' be the intersection Vₑ ∩ dom(φₑ)
  let V' (e : f ⁻¹' {x}) := V e ∩ (φ e).source
  have hV' e : IsOpen (V' e) := (hV e).2.inter (φ e).open_source
  have : ⋃ e, V' e ∈ nhdsSet (f ⁻¹' {x}) :=
    (isOpen_iUnion hV').mem_nhdsSet.2 fun e he ↦ mem_iUnion_of_mem ⟨e, he⟩ ⟨(hV e).1, (hφ _).1⟩
  -- since f is a closed map, the union of the Vₑ' contains the preimage of a neighborhood U of x
  have ⟨W, hWx, hWV⟩ := isClosedMap_iff_comap_nhds_le.mp hf this
  cases isEmpty_or_nonempty (f ⁻¹' {x})
  · exact .of_preimage_eq_empty _ hWx (by simpa using hWV)
  have ⟨U, hUW, hU, hxU⟩ := mem_nhds_iff.mp hWx
  -- show that the intersection of U with the images of Vₑ' is evenly covered
  let U' := U ∩ ⋂ e : f ⁻¹' {x}, f '' (V' e)
  have : Finite (f ⁻¹' {x}) := fin
  have hU' : IsOpen U' := hU.inter <| isOpen_iInter_of_finite fun e ↦ by
    convert! ← (φ e).isOpen_image_of_subset_source (hV' _) inter_subset_right; exact (hφ e).2
  have hUV e : U' ⊆ f '' V' e := inter_subset_right.trans (iInter_subset ..)
  have : Nonempty E := ⟨Classical.arbitrary (f ⁻¹' {x})⟩
  refine .of_trivialization (t := hU'.trivializationDiscrete _ _
    (fun e s hs ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩) (fun e ↦ ?_)
    (fun e ↦ .mono subset_rfl (hUV e) (surjOn_image f _))
    (pairwise_disjoint_mono disj.subtype fun e ↦ inter_subset_left)
    ((preimage_mono (inter_subset_left.trans hUW)).trans hWV))
    ⟨hxU, Set.mem_iInter.mpr fun e ↦ ⟨e, ⟨(hV e).1, (hφ e).1⟩, e.2⟩⟩
  · convert! ((φ e).isOpen_inter_preimage h).inter (hV e).2 using 1
    simp_rw [(hφ e).2, V']; ac_rfl
  · have : s ⊆ (φ e).target := hs.trans <| (hUV e).trans <| by
      rw [← (φ e).image_source_eq_target, (hφ e).2]; exact image_mono inter_subset_right
    rw [← (φ e).isOpen_symm_image_iff_of_subset_target this,
      (φ e).symm_image_eq_source_inter_preimage this, (hφ e).2, inter_comm]
    convert! h using 1
    refine inter_eq_inter_iff_left.mpr ⟨fun e' h ↦ h.2.2, fun e' h ↦ ⟨?_ , h.2⟩⟩
    have ⟨e'', ⟨_, mem⟩, eq⟩ := mem_iInter.mp (hs h.1).2 e
    rwa [← (φ e).injOn mem h.2 (by rwa [(hφ e).2])]
  · convert! ← (φ e).injOn.mono inter_subset_right; exact (hφ e).2


/-- **A closed separated local homeomorphism with finite fibres is a covering map.** -/
theorem IsClosedMap.isCoveringMap_of_isLocalHomeomorph_of_isSeparatedMap (hsep : IsSeparatedMap f)
    (hf : IsClosedMap f) (hfin : ∀ x, (f ⁻¹' {x}).Finite) (h : IsLocalHomeomorph f) :
    IsCoveringMap f := fun x ↦
  hf.isEvenlyCovered_of_openPartialHomeomorph_of_isSeparatedMap hsep (hfin x) fun e _ ↦
    (h e).imp fun _ hφ ↦ ⟨hφ.1, hφ.2.symm⟩
