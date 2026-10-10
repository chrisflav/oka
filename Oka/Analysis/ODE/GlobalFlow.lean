/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Mathlib.Analysis.ODE.ExistUnique

/-!
# The global flow of a bounded, globally Lipschitz autonomous vector field

Mathlib's Picard–Lindelöf theorem (`Mathlib/Analysis/ODE/PicardLindelof.lean`,
`Mathlib/Analysis/ODE/ExistUnique.lean`) produces solutions on a compact time interval whose
length is limited by the bound and the radius of the ball on which the hypotheses hold. For a
time-independent vector field `V` that is bounded and globally Lipschitz on the whole space,
the hypotheses hold on balls of every radius, so solutions exist on `[-T, T]` for every `T`; by
uniqueness (`ODE_solution_unique_of_mem_Icc`) they glue to a solution on all of `ℝ`. This file
records that gluing, and the Grönwall estimate (`dist_le_of_trajectories_ODE`) that makes the
time-`t` map continuous in the initial point.

## Main results

- `exists_flow_of_lipschitzWith`: for `V : E → E` bounded and `K`-Lipschitz on a complete normed
  space, there is `φ : E → ℝ → E` with `φ y 0 = y`, `φ y` an integral curve of `V` defined on all
  of `ℝ`, and `dist (φ y t) (φ y' t) ≤ dist y y' * exp (K * t)` for `t ≥ 0`.
- `continuous_flow_of_lipschitzWith`: the time-`t` map `y ↦ φ y t` of such a flow is continuous
  for `t ≥ 0` (a consequence of the estimate).

Nothing is said about the flow property `φ (φ y s) t = φ y (s + t)`, or about non-autonomous
fields; neither is needed downstream.
-/

open Set Metric

open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Picard–Lindelöf on `[-(N + 1), N + 1]` for a bounded, globally Lipschitz autonomous field. -/
private theorem exists_solution_Icc {V : E → E} {K M : ℝ≥0} (hV : LipschitzWith K V)
    (hM : ∀ x, ‖V x‖ ≤ M) (N : ℕ) (y : E) :
    ∃ α : ℝ → E, α 0 = y ∧ ∀ t ∈ Icc (-((N : ℝ) + 1)) ((N : ℝ) + 1),
      HasDerivWithinAt α (V (α t)) (Icc (-((N : ℝ) + 1)) ((N : ℝ) + 1)) t := by
  have h0 : (0 : ℝ) ∈ Icc (-((N : ℝ) + 1)) ((N : ℝ) + 1) := ⟨by linarith, by linarith⟩
  have hPL : IsPicardLindelof (fun _ ↦ V) (⟨0, h0⟩ : Icc (-((N : ℝ) + 1)) ((N : ℝ) + 1)) y
      (M * (N + 1)) 0 M K :=
    IsPicardLindelof.of_time_independent (fun x _ ↦ hM x) hV.lipschitzOnWith (by
      push_cast
      rw [sub_zero, zero_sub, neg_neg, sub_zero, max_self])
  exact hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt (mem_closedBall_self le_rfl)

/-- **The global flow of a bounded, globally Lipschitz autonomous vector field.** Every initial
point `y` has an integral curve `φ y : ℝ → E` of `V` defined on all of `ℝ` with `φ y 0 = y`, and
trajectories separate at most exponentially in forward time. -/
theorem exists_flow_of_lipschitzWith {V : E → E} {K M : ℝ≥0} (hV : LipschitzWith K V)
    (hM : ∀ x, ‖V x‖ ≤ M) :
    ∃ φ : E → ℝ → E, (∀ y, φ y 0 = y) ∧ (∀ y t, HasDerivAt (φ y) (V (φ y t)) t) ∧
      ∀ y y' t, 0 ≤ t → dist (φ y t) (φ y' t) ≤ dist y y' * Real.exp (K * t) := by
  choose α hα0 hα using exists_solution_Icc hV hM
  set I : ℕ → Set ℝ := fun N ↦ Icc (-((N : ℝ) + 1)) ((N : ℝ) + 1) with hI
  have hC (N : ℕ) (y : E) : ContinuousOn (α N y) (I N) :=
    fun t ht ↦ (hα N y t ht).continuousWithinAt
  have hD (N : ℕ) (y : E) (t : ℝ) (ht : |t| < N + 1) : HasDerivAt (α N y) (V (α N y t)) t := by
    rw [abs_lt] at ht
    exact (hα N y t ⟨ht.1.le, ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  have hcons (N N' : ℕ) (y : E) (hN : N ≤ N') : EqOn (α N y) (α N' y) (I N) := by
    have hN' : (N : ℝ) ≤ N' := Nat.cast_le.2 hN
    have hsub : I N ⊆ I N' := Icc_subset_Icc (by linarith) (by linarith)
    refine ODE_solution_unique_of_mem_Icc (v := fun _ ↦ V) (s := fun _ ↦ univ) (K := K)
      (fun _ _ ↦ hV.lipschitzOnWith) (t₀ := 0) ⟨by linarith, by linarith⟩ (hC N y)
      (fun t ht ↦ hD N y t (abs_lt.2 ht)) (fun _ _ ↦ trivial) ((hC N' y).mono hsub)
      (fun t ht ↦ hD N' y t (abs_lt.2 ⟨by linarith [ht.1], by linarith [ht.2]⟩))
      (fun _ _ ↦ trivial) ((hα0 N y).trans (hα0 N' y).symm)
  have heq (N : ℕ) (y : E) (s : ℝ) (hs : |s| < N + 1) : α ⌈|s|⌉₊ y s = α N y s := by
    rcases le_total ⌈|s|⌉₊ N with h | h
    · refine hcons _ _ y h ?_
      have := Nat.le_ceil |s|
      exact abs_le.1 (by linarith)
    · exact (hcons _ _ y h (abs_le.1 hs.le)).symm
  set φ : E → ℝ → E := fun y t ↦ α ⌈|t|⌉₊ y t
  have hφD (y : E) (t : ℝ) : HasDerivAt (φ y) (V (φ y t)) t := by
    have ht : |t| < ⌈|t|⌉₊ + 1 := (Nat.le_ceil |t|).trans_lt (lt_add_one _)
    refine (hD ⌈|t|⌉₊ y t ht).congr_of_eventuallyEq ?_
    have : {s : ℝ | |s| < ⌈|t|⌉₊ + 1} ∈ nhds t :=
      (isOpen_lt continuous_abs continuous_const).mem_nhds ht
    filter_upwards [this] with s hs
    exact heq _ y s hs
  refine ⟨φ, fun y ↦ ?_, hφD, fun y y' t ht ↦ ?_⟩
  · simp only [φ, abs_zero, Nat.ceil_zero]
    exact hα0 0 y
  · have h := dist_le_of_trajectories_ODE (v := fun _ ↦ V) (K := K) (a := 0) (b := t)
      (fun _ ↦ hV) (fun s _ ↦ (hφD y s).continuousAt.continuousWithinAt)
      (fun s _ ↦ (hφD y s).hasDerivWithinAt)
      (fun s _ ↦ (hφD y' s).continuousAt.continuousWithinAt)
      (fun s _ ↦ (hφD y' s).hasDerivWithinAt) (δ := dist y y') (by
        rw [show φ y 0 = y from by simp only [φ, abs_zero, Nat.ceil_zero]; exact hα0 0 y,
          show φ y' 0 = y' from by simp only [φ, abs_zero, Nat.ceil_zero]; exact hα0 0 y'])
      t ⟨ht, le_rfl⟩
    rwa [sub_zero] at h

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- **The time-`t` map of such a flow is continuous** for `t ≥ 0`: it is `exp (K t)`-Lipschitz. -/
theorem continuous_flow_of_lipschitzWith {K : ℝ≥0} {φ : E → ℝ → E}
    (hφ : ∀ y y' t, 0 ≤ t → dist (φ y t) (φ y' t) ≤ dist y y' * Real.exp (K * t)) {t : ℝ}
    (ht : 0 ≤ t) : Continuous fun y ↦ φ y t :=
  (LipschitzWith.of_dist_le_mul (K := ⟨Real.exp (K * t), (Real.exp_pos _).le⟩) fun y y' ↦ by
    change _ ≤ Real.exp (K * t) * _
    rw [mul_comm]
    exact hφ y y' t ht).continuous
