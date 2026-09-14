/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.Sets.Opens

/-!
# The sheets of a map as a family of opens, and base change of a local homeomorphism

`IsLocalHomeomorph f` says that every point of the source has *some* neighbourhood on which `f`
restricts to an open embedding. What a construction indexed by opens needs instead is the family
of all such opens together with the statement that it covers, and that is what is here:
`sheetOpens f` is the set of opens on which `f` is an open embedding, and
`IsLocalHomeomorph.sSup_sheetOpens` says its supremum is `⊤`.

**And the class is stable under base change**: `IsLocalHomeomorph.pullback_snd` carries it along an
arbitrary continuous map, at Mathlib's set-level fibre product `Function.Pullback`. The two
statements are independent of each other and share only their destination.

**The heading above read *The sheets of a map, as a family of opens* and the paragraph under it
ended at `IsLocalHomeomorph.sSup_sheetOpens` says its supremum is `⊤`, until 2026-09-13**, when the
base-change statement was appended. The heading is broadened rather than replaced: what it named is
still here and is still the first half of the file.

There is no analytic content here, so this file is a candidate for upstreaming; it lives in the
`Oka/Topology/` mirror of the Mathlib directory tree for that reason. Upstreaming to
`Mathlib/Topology/IsLocalHomeomorph.lean` costs that file **no** new imports — its closure of 649
Mathlib modules already contains `Mathlib.Topology.Sets.Opens`, measured with
`python3 scripts/import_cost.py --target Mathlib.Topology.IsLocalHomeomorph`.

## Why the `Opens` form rather than Mathlib's

`isLocalHomeomorph_iff_isOpenEmbedding_restrict` gives, for each `x`, some `U ∈ 𝓝 x` with
`IsOpenEmbedding (U.restrict f)`. A neighbourhood is not an open, and a consumer that glues over
a cover — `AlgebraicGeometry.LocallyRingedSpace.sheetIso` is the one this was written for — needs
opens and needs them as a *family with a supremum*, not one at a time. Passing through the
source of the `OpenPartialHomeomorph` that `IsLocalHomeomorph` unfolds to, which is open by
`OpenPartialHomeomorph.open_source`, avoids taking an interior and the proof that restricting an
open embedding to a smaller open is again one.

## Main definitions

- `sheetOpens`: the opens of the source on which the map is an open embedding.

## Main results

- `IsLocalHomeomorph.exists_mem_sheetOpens`: **every point lies in a sheet.**
- `IsLocalHomeomorph.sSup_sheetOpens`: **the sheets cover**, `sSup (sheetOpens f) = ⊤`.
- `IsLocalHomeomorph.pullback_snd`: **a local homeomorphism stays a local homeomorphism under base
  change along a continuous map.**

## What is not here

* **Nothing about the fibres.** `sheetOpens f` is a set of opens and says nothing about how many
  of them meet a fibre; finiteness of the fibres is a separate hypothesis everywhere it is needed.
* **No sheet is distinguished and no choice is made.** `IsLocalHomeomorph.exists_mem_sheetOpens`
  is an existence statement; a consumer that wants one sheet per point chooses it itself.
* **No converse.** A map whose sheets cover *is* a local homeomorphism, by
  `isLocalHomeomorph_iff_isOpenEmbedding_restrict` and `Opens.isOpen`, but nothing below needs
  that direction and it is not stated.
* **Nothing about the sheets of a base change.** `IsLocalHomeomorph.pullback_snd` is stated through
  `isLocalHomeomorph_iff_isOpenEmbedding_restrict` and says nothing about how `sheetOpens` of the
  projection relates to `sheetOpens` of the map being base-changed; the two halves of this file do
  not meet.
* **Nothing about the other three statements under `Oka/` whose conclusion is about
  `Function.Pullback.snd`.** A covering map base-changes by `IsCoveringMap.pullback_snd` and the
  fibres stay finite by `Function.Pullback.finite_fiber_snd` — both in
  `Oka/Topology/Covering/Basic.lean` — and a proper map stays proper by `IsProperMap.pullback_snd`
  in `Oka/Topology/Maps/Proper/Basic.lean`. **This file imports neither of those two modules and
  neither imports it**, each mirroring the Mathlib module its own statement belongs in.
-/

open TopologicalSpace Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y)

/-- **The sheets of `f`**: the opens of the source on which `f` restricts to an open embedding. -/
def sheetOpens : Set (Opens X) := {V | IsOpenEmbedding ((V : Set X).restrict f)}

theorem mem_sheetOpens {V : Opens X} :
    V ∈ sheetOpens f ↔ IsOpenEmbedding ((V : Set X).restrict f) := Iff.rfl

/-- **Every point of the source lies in a sheet.**

The sheet produced is the source of the `OpenPartialHomeomorph` that `IsLocalHomeomorph` supplies,
which is open by construction — so no interior has to be taken. -/
theorem IsLocalHomeomorph.exists_mem_sheetOpens (hf : IsLocalHomeomorph f) (x : X) :
    ∃ V ∈ sheetOpens f, x ∈ V := by
  obtain ⟨e, hxe, he⟩ := hf x
  exact ⟨⟨e.source, e.open_source⟩, he ▸ e.isOpenEmbedding_restrict, hxe⟩

/-- **The sheets of a local homeomorphism cover its source.** -/
theorem IsLocalHomeomorph.sSup_sheetOpens (hf : IsLocalHomeomorph f) :
    sSup (sheetOpens f) = ⊤ := by
  refine top_le_iff.1 fun x _ ↦ ?_
  obtain ⟨V, hV, hxV⟩ := IsLocalHomeomorph.exists_mem_sheetOpens f hf x
  exact Opens.mem_sSup.2 ⟨V, hV, hxV⟩

section BaseChange

variable {f}
variable {Z : Type*} [TopologicalSpace Z] {g : Z → Y}

/-- **A local homeomorphism stays a local homeomorphism under base change along a continuous
map**, at Mathlib's set-level fibre product `Function.Pullback`. -/
theorem IsLocalHomeomorph.pullback_snd (hf : IsLocalHomeomorph f) (hg : Continuous g) :
    IsLocalHomeomorph (Function.Pullback.snd : f.Pullback g → Z) := by
  rw [isLocalHomeomorph_iff_isOpenEmbedding_restrict]
  intro p
  obtain ⟨e, hmem, hfe⟩ := hf (Function.Pullback.fst p)
  have hfx : ∀ x, f x = e x := fun x ↦ congrFun hfe x
  have hcsnd : Continuous (Function.Pullback.snd : f.Pullback g → Z) :=
    continuous_snd.comp continuous_subtype_val
  have hUopen : IsOpen ((Function.Pullback.fst : f.Pullback g → X) ⁻¹' e.source) :=
    e.open_source.preimage (continuous_fst.comp continuous_subtype_val)
  have hTopen : IsOpen (g ⁻¹' e.target) := e.open_target.preimage hg
  refine ⟨_, hUopen.mem_nhds hmem, ?_⟩
  have hmapT : ∀ q : ((Function.Pullback.fst : f.Pullback g → X) ⁻¹' e.source),
      Function.Pullback.snd (q : f.Pullback g) ∈ g ⁻¹' e.target := by
    intro q
    have h1 : f (Function.Pullback.fst (q : f.Pullback g))
        = g (Function.Pullback.snd (q : f.Pullback g)) := (q : f.Pullback g).2
    change g (Function.Pullback.snd (q : f.Pullback g)) ∈ e.target
    rw [← h1, hfx]
    exact e.map_source q.2
  have hmapU : ∀ t : (g ⁻¹' e.target), f (e.symm (g (t : Z))) = g (t : Z) := by
    intro t
    rw [hfx]
    exact e.right_inv t.2
  have hmemU : ∀ t : (g ⁻¹' e.target),
      (⟨(e.symm (g (t : Z)), (t : Z)), hmapU t⟩ : f.Pullback g)
        ∈ (Function.Pullback.fst : f.Pullback g → X) ⁻¹' e.source :=
    fun t ↦ e.map_target t.2
  let φ : ((Function.Pullback.fst : f.Pullback g → X) ⁻¹' e.source) ≃ₜ (g ⁻¹' e.target) :=
    { toFun q := ⟨Function.Pullback.snd (q : f.Pullback g), hmapT q⟩
      invFun t := ⟨⟨(e.symm (g (t : Z)), (t : Z)), hmapU t⟩, hmemU t⟩
      left_inv q := by
        refine Subtype.ext (Subtype.ext (Prod.ext ?_ rfl))
        have h1 : f (Function.Pullback.fst (q : f.Pullback g))
            = g (Function.Pullback.snd (q : f.Pullback g)) := (q : f.Pullback g).2
        change e.symm (g (Function.Pullback.snd (q : f.Pullback g))) = _
        rw [← h1, hfx]
        exact e.left_inv q.2
      right_inv t := Subtype.ext rfl
      continuous_toFun := Continuous.subtype_mk (hcsnd.comp continuous_subtype_val) _
      continuous_invFun := by
        refine Continuous.subtype_mk (Continuous.subtype_mk (Continuous.prodMk ?_
          continuous_subtype_val) _) _
        exact (e.continuousOn_symm.comp hg.continuousOn fun t ht ↦ ht).restrict }
  exact hTopen.isOpenEmbedding_subtypeVal.comp φ.isOpenEmbedding

end BaseChange
