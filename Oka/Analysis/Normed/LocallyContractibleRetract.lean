/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Homotopy.LocallyContractible
import Mathlib.Topology.UnitInterval

/-!
# A set that is locally a retract of balls is locally contractible

Let `Z` be a subset of a real normed space. Suppose that every `p ∈ Z` has a ball `B(p, ρ)` and a
map `R : B(p, ρ) → Z`, continuous and the identity on `Z ∩ B(p, ρ)`. Then `Z` is locally
contractible in the classical sense (`LocallyContractibleSpace`): for a neighbourhood `U` of `p`
in `Z`, choose `ρ'` so small that `R` maps `B(p, ρ')` into `U` (continuity of `R` at `p`, where
`R p = p`); then `(z, t) ↦ R (p + (1 - t) • (z - p))` is a homotopy, inside `U`, from the inclusion
of `Z ∩ B(p, ρ')` to the constant map at `p`, the segment from `z` to `p` staying in `B(p, ρ')`.

This is the last, purely topological step of Łojasiewicz's proof that real algebraic sets are
locally contractible; the retraction itself is constructed in
`Oka/Analysis/Lojasiewicz/Retraction.lean`.

## Main results

- `locallyContractibleSpace_of_forall_retraction`: the statement above.
-/

open Set Metric Topology ContinuousMap

/-- **A subset of a normed space that is, near each of its points, a retract of a ball is locally
contractible.** -/
theorem locallyContractibleSpace_of_forall_retraction {E : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] {Z : Set E}
    (h : ∀ p ∈ Z, ∃ ρ > 0, ∃ R : E → E, ContinuousOn R (ball p ρ) ∧ MapsTo R (ball p ρ) Z ∧
      ∀ y ∈ ball p ρ, y ∈ Z → R y = y) :
    LocallyContractibleSpace Z := by
  rintro ⟨p, hp⟩ U hU
  obtain ⟨ρ, hρ, R, hRc, hRZ, hRid⟩ := h p hp
  obtain ⟨u, hu, huU⟩ := mem_nhds_subtype Z ⟨p, hp⟩ U |>.1 hU
  obtain ⟨ε, hε, hεu⟩ := Metric.mem_nhds_iff.1 hu
  have hRp : R p = p := hRid p (mem_ball_self hρ) hp
  obtain ⟨δ, hδ, hRδ⟩ := Metric.continuousAt_iff.1 (hRc.continuousAt (ball_mem_nhds p hρ)) ε hε
  set ρ' := min δ (min ρ ε) with hρ'
  have hρ'0 : 0 < ρ' := lt_min hδ (lt_min hρ hε)
  set V : Set Z := Subtype.val ⁻¹' ball p ρ' with hV
  have hVU : V ⊆ U := fun z hz ↦
    huU (hεu (ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _)) hz))
  refine ⟨V, hVU, (isOpen_ball.preimage continuous_subtype_val).mem_nhds (mem_ball_self hρ'0),
    ⟨⟨⟨p, hp⟩, hVU (mem_ball_self hρ'0)⟩, ⟨?_⟩⟩⟩
  -- the segment from `z` to `p`
  set q : unitInterval × V → E := fun x ↦ p + (1 - (x.1 : ℝ)) • (((x.2 : Z) : E) - p) with hq
  have hqc : Continuous q := by fun_prop
  have hqb (x : unitInterval × V) : q x ∈ ball p ρ' := by
    rw [mem_ball, dist_eq_norm, hq]
    simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    have h1 : |1 - (x.1 : ℝ)| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith [x.1.2.1, x.1.2.2]
    have h2 : ‖((x.2 : Z) : E) - p‖ < ρ' := by
      exact mem_ball_iff_norm.1 x.2.2
    calc |1 - (x.1 : ℝ)| * ‖((x.2 : Z) : E) - p‖ ≤ 1 * ‖((x.2 : Z) : E) - p‖ := by gcongr
      _ < ρ' := by rwa [one_mul]
  have hqρ (x) : q x ∈ ball p ρ :=
    ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _)) (hqb x)
  have hRU (x) : (⟨R (q x), hRZ (hqρ x)⟩ : Z) ∈ U := by
    refine huU (hεu ?_)
    have := hRδ (lt_of_lt_of_le (hqb x) (min_le_left _ _))
    rwa [hRp] at this
  refine
    { toFun := fun x ↦ ⟨⟨R (q x), hRZ (hqρ x)⟩, hRU x⟩
      continuous_toFun := ?_
      map_zero_left := fun z ↦ ?_
      map_one_left := fun z ↦ ?_ }
  · exact ((hRc.comp_continuous hqc hqρ).subtype_mk _).subtype_mk _
  · apply Subtype.ext; apply Subtype.ext
    simp only [hq, Set.Icc.coe_zero, sub_zero, one_smul, add_sub_cancel]
    exact hRid _ (ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _)) z.2) (z : Z).2
  · apply Subtype.ext; apply Subtype.ext
    simp [hq, hRp]
