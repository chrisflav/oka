/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytic.RiemannExtension
import Oka.Analytification.GAGA.CousinCoordinate

/-!
# The Riemann extension theorem for holomorphic functions on opens of `ℂ^ι`

This file restates the Riemann extension theorem of `Oka.Analytic.RiemannExtension` for the rings
`OkaRing U` of holomorphic functions on open subsets `U ⊆ ℂ^ι`.

## Main results

- `OkaRing.interior_inter_preimage_zero_eq_empty`: on a connected open set, the zero set of a
  nonzero holomorphic function has empty interior.
- `OkaRing.existsUnique_restrict_eq`: **Riemann extension theorem.** Let `g` be holomorphic on
  `U` with nowhere dense zero set and let `V ⊆ U` be open containing `U \ {g = 0}`. A
  holomorphic function on `V` which is bounded near every point of `U` is the restriction of a
  unique holomorphic function on `U`.
-/

open Set Filter TopologicalSpace
open scoped Topology

variable {ι : Type*} [Fintype ι]

namespace OkaRing

/-- A holomorphic function on `U` is analytic at every point of `U`. -/
lemma analyticOnNhd_toGlobalFun {U : Opens (ι → ℂ)} (g : OkaRing U) :
    AnalyticOnNhd ℂ (g.toGlobalFun _) U :=
  (okaAnalytic_iff _).mp g.2

/-- On a preconnected open set, the zero set of a nonzero holomorphic function has empty
interior. -/
theorem interior_inter_preimage_zero_eq_empty {U : Opens (ι → ℂ)}
    (hU : IsPreconnected (U : Set (ι → ℂ))) {g : OkaRing U} (hg : g ≠ 0) :
    interior ((U : Set (ι → ℂ)) ∩ g.toGlobalFun _ ⁻¹' {0}) = ∅ := by
  obtain ⟨x, hx⟩ : ∃ x : U, g.toFun _ x ≠ 0 := by
    by_contra! h
    exact hg (OkaRing.ext (funext h))
  refine g.analyticOnNhd_toGlobalFun.interior_inter_preimage_zero_eq_empty hU x.2 ?_
  rwa [g.toGlobalFun_apply x.2]

/-- **Riemann extension theorem.** Let `g` be holomorphic on `U` such that its zero set has empty
interior, and let `V ⊆ U` be open containing `U \ {g = 0}`. A holomorphic function on `V` which
is bounded near every point of `U` is the restriction of a unique holomorphic function on `U`. -/
theorem existsUnique_restrict_eq {U V : Opens (ι → ℂ)} (hVU : V ≤ U) (g : OkaRing U)
    (hZ : interior ((U : Set (ι → ℂ)) ∩ g.toGlobalFun _ ⁻¹' {0}) = ∅)
    (hV : (U : Set (ι → ℂ)) \ g.toGlobalFun _ ⁻¹' {0} ⊆ V) (f : OkaRing V)
    (hbdd : ∀ z ∈ U, IsBoundedUnder (· ≤ ·) (𝓝[V] z) fun w ↦ ‖f.toGlobalFun _ w‖) :
    ∃! F : OkaRing U, OkaRing.restrict hVU F = f := by
  set G := g.toGlobalFun _
  have hf : DifferentiableOn ℂ (f.toGlobalFun _) ((U : Set (ι → ℂ)) \ G ⁻¹' {0}) :=
    f.differentiableOn_toGlobalFun.mono hV
  obtain ⟨F₀, hF₀d, hF₀f⟩ := exists_differentiableOn_eqOn_of_isBoundedUnder U.isOpen
    g.differentiableOn_toGlobalFun hZ hf fun z hz ↦ (hbdd z hz).mono (nhdsWithin_mono _ hV)
  -- `F₀` agrees with `f` on all of `V`, as `V \ {g = 0}` is dense in `V`.
  have hZV : interior ((V : Set (ι → ℂ)) ∩ G ⁻¹' {0}) = ∅ :=
    subset_empty_iff.mp (hZ ▸ interior_mono (inter_subset_inter_left _ hVU))
  have hF₀V : EqOn F₀ (f.toGlobalFun _) V :=
    EqOn.of_eqOn_diff_zero V.isOpen hZV (hF₀d.continuousOn.mono hVU) f.continuousOn_toGlobalFun
      fun x hx ↦ hF₀f ⟨hVU hx.1, hx.2⟩
  refine ⟨ofDifferentiableOn F₀ hF₀d, ?_, fun F hF ↦ ?_⟩
  · ext x
    simp [hF₀V x.2, f.toGlobalFun_apply x.2]
  · have hFU : EqOn (F.toGlobalFun _) F₀ U := by
      refine EqOn.of_eqOn_diff_zero U.isOpen hZ F.continuousOn_toGlobalFun hF₀d.continuousOn
        fun x hx ↦ ?_
      have hxV : x ∈ V := hV hx
      rw [hF₀V hxV, F.toGlobalFun_apply hx.1, f.toGlobalFun_apply hxV, ← hF]
      rfl
    ext x
    simp [← hFU x.2, F.toGlobalFun_apply x.2]

end OkaRing
