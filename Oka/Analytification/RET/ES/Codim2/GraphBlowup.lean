/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.ES.Codim2.GraphConfig

/-!
# Blowing up a graph configuration

Let `c` be a graph configuration on `N` (`ComplexAnalytic.BoundedSections.GraphConfig`) all of
whose contact orders are positive, i.e. all graphs pass through `C = {t = 0, w = ψᵢ₀}`. Blow up
`C` (`ComplexAnalytic.BoundedSections.GraphConfig.centre`).

- In the first chart `(…, t, v) ↦ (…, t, ψᵢ₀ + t v)` the pullback of `N ∖ N°` is again a graph
  configuration, with graphs the strict transforms `χᵢ = (ψᵢ - ψᵢ₀) / t` and contact orders
  lowered by one (`…GraphConfig.chart₁Config`). Since `χᵢ₀ = 0`, the part of the first chart over
  `N°` lies in `v ≠ 0` (`…GraphConfig.ne_zero_of_mem_M₁₀`).
- The second chart `(…, s, v') ↦ (…, s v', ψᵢ₀ + s)` agrees with the first on `v v' = 1` via
  `(…, t, v) ↦ (…, t v, v⁻¹)` (`ComplexAnalytic.BoundedSections.swapChart`), which is an
  involution of `v ≠ 0` identifying the first chart over `N°` with the second
  (`…GraphConfig.swapMap`, `…GraphConfig.swapBiholo`). Near `v' = 0` the pullback of `N ∖ N°` to
  the second chart is `{s v' = 0}`.
- Downstairs, `N ∖ N°` has normal crossings off `C`.

## Main definitions

- `ComplexAnalytic.BoundedSections.GraphConfig.centre`: the centre `{t = 0, w = ψᵢ₀}`.
- `ComplexAnalytic.BoundedSections.GraphConfig.strict`: the strict transforms `χᵢ`.
- `ComplexAnalytic.BoundedSections.GraphConfig.chart₁Config`: the configuration on the first
  chart.
-/

open CategoryTheory Opposite AlgebraicGeometry Topology TopologicalSpace Filter Set

universe u

namespace ComplexAnalytic.BoundedSections

open AnalyticSpace

noncomputable section

variable {n : ℕ}

/-- The hyperplane `xᵢ = 0` of `ℂⁿ` has empty interior. -/
lemma interior_setOf_apply_eq_zero (i : ULift.{u} (Fin n)) :
    interior {x : Cn.{u} n | x i = 0} = ∅ := by
  refine eq_empty_of_forall_notMem fun x hx ↦ ?_
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 isOpen_interior x hx
  have hmem : Function.update x i (x i + ((r / 2 : ℝ) : ℂ)) ∈ Metric.ball x r := by
    rw [Metric.mem_ball, dist_pi_lt_iff hr]
    intro j
    by_cases hj : j = i
    · subst hj
      simp only [Function.update_self, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
        Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ r / 2)]
      linarith
    · simp [Function.update_of_ne hj, hr]
  have h := interior_subset (hball hmem)
  simp only [mem_setOf_eq, Function.update_self] at h
  have hx0 : x i = 0 := (interior_subset (s := {x : Cn.{u} n | x i = 0}) hx : _)
  rw [hx0, zero_add] at h
  exact (by exact_mod_cast (by positivity : (r / 2 : ℝ) ≠ 0) : ((r / 2 : ℝ) : ℂ) ≠ 0) h

/-! ### The transition between the charts -/

section Swap

variable {it iw : ULift.{u} (Fin n)}

/-- The transition `(…, t, v) ↦ (…, t v, v⁻¹)` between the two charts of a blow-up; it is an
involution of `v ≠ 0`. -/
def swapChart (it iw : ULift.{u} (Fin n)) (x : Cn.{u} n) : Cn.{u} n :=
  Function.update (Function.update x it (x it * x iw)) iw (x iw)⁻¹

lemma swapChart_iw (x : Cn.{u} n) : swapChart it iw x iw = (x iw)⁻¹ :=
  Function.update_self _ _ _

lemma swapChart_it (hne : it ≠ iw) (x : Cn.{u} n) : swapChart it iw x it = x it * x iw := by
  rw [swapChart, Function.update_of_ne hne, Function.update_self]

lemma swapChart_swapChart (hne : it ≠ iw) {x : Cn.{u} n} (hx : x iw ≠ 0) :
    swapChart it iw (swapChart it iw x) = x := by
  have e : swapChart it iw x it * swapChart it iw x iw = x it := by
    rw [swapChart_it hne, swapChart_iw]
    field_simp
  rw [swapChart, e, swapChart_iw, inv_inv]
  funext j
  by_cases hj : j = iw
  · subst hj
    simp
  by_cases hj' : j = it
  · subst hj'
    simp [Function.update_of_ne hj]
  · simp [swapChart, Function.update_of_ne hj, Function.update_of_ne hj']

lemma differentiableOn_swapChart :
    DifferentiableOn ℂ (swapChart it iw) {x : Cn.{u} n | x iw ≠ 0} :=
  differentiableOn_update (differentiableOn_update differentiableOn_id
    ((differentiable_apply it).mul (differentiable_apply iw)).differentiableOn it)
    ((differentiable_apply iw).differentiableOn.inv fun _ hx ↦ hx) iw

/-- The second chart after the transition is the first chart. -/
lemma BlowupCentre.ch₂_swapChart {N N₀ : (AnalyticSpace.complexAffineSpace.{u} n).Opens}
    (C : BlowupCentre N N₀) {x : Cn.{u} n} (hx : x C.iw ≠ 0) :
    C.ch₂ (swapChart C.it C.iw x) = C.ch₁ x := by
  have hne := C.it_ne_iw
  have hta : C.ta (swapChart C.it C.iw x) = Function.update x C.iw (x C.iw)⁻¹ := by
    rw [BlowupCentre.ta, swapChart_it hne, swapChart_iw, mul_assoc, mul_inv_cancel₀ hx, mul_one]
    funext j
    by_cases hj : j = C.iw
    · subst hj
      simp [swapChart, Function.update_of_ne hne.symm]
    by_cases hj' : j = C.it
    · subst hj'
      simp [Function.update_of_ne hj]
    · simp [swapChart, Function.update_of_ne hj, Function.update_of_ne hj']
  rw [BlowupCentre.ch₂, hta, C.φ_update, swapChart_it hne, Function.update_idem,
    BlowupCentre.ch₁]

/-- The first chart after the transition is the second chart. -/
lemma BlowupCentre.ch₁_swapChart {N N₀ : (AnalyticSpace.complexAffineSpace.{u} n).Opens}
    (C : BlowupCentre N N₀) {a : Cn.{u} n} (ha : a C.iw ≠ 0) :
    C.ch₁ (swapChart C.it C.iw a) = C.ch₂ a := by
  have h : swapChart C.it C.iw a C.iw ≠ 0 := by
    rw [swapChart_iw]
    exact inv_ne_zero ha
  rw [← C.ch₂_swapChart h, swapChart_swapChart C.it_ne_iw ha]

end Swap

namespace GraphConfig

variable {N N₀ : (AnalyticSpace.complexAffineSpace.{u} n).Opens} (c : GraphConfig N N₀)

/-! ### Chosen units -/

open Classical in
/-- A chosen unit `uᵢⱼ` with `ψᵢ - ψⱼ = t ^ kᵢⱼ uᵢⱼ` (and `1` for `i = j`). -/
def unit (i j : Fin c.m) : Cn.{u} n → ℂ :=
  if h : i ≠ j then (c.exists_unit i j h).choose else fun _ ↦ 1

lemma unit_update (i j : Fin c.m) (x : Cn.{u} n) (a : ℂ) :
    c.unit i j (Function.update x c.iw a) = c.unit i j x := by
  unfold unit
  split_ifs with h
  · exact (c.exists_unit i j h).choose_spec.1 x a
  · rfl

lemma differentiableOn_unit (i j : Fin c.m) : DifferentiableOn ℂ (c.unit i j) (cyl N c.iw) := by
  unfold unit
  split_ifs with h
  · exact (c.exists_unit i j h).choose_spec.2.1
  · exact differentiableOn_const 1

lemma unit_ne_zero (i j : Fin c.m) {x : Cn.{u} n} (hx : x ∈ cyl N c.iw) : c.unit i j x ≠ 0 := by
  unfold unit
  split_ifs with h
  · exact (c.exists_unit i j h).choose_spec.2.2.1 x hx
  · exact one_ne_zero

lemma sub_eq_unit {i j : Fin c.m} (h : i ≠ j) {x : Cn.{u} n} (hx : x ∈ cyl N c.iw) :
    c.ψ i x - c.ψ j x = x c.it ^ c.k i j * c.unit i j x := by
  unfold unit
  rw [dif_pos h]
  exact (c.exists_unit i j h).choose_spec.2.2.2 x hx

/-! ### The centre -/

variable (h₀ : N₀ ≤ N) (i₀ : Fin c.m)

/-- **The centre** `{t = 0, w = ψᵢ₀}` of the blow-up. -/
def centre : BlowupCentre N N₀ where
  it := c.it
  iw := c.iw
  it_ne_iw := c.it_ne_iw
  φ := c.ψ i₀
  φ_update := c.ψ_update i₀
  differentiableOn_φ := c.differentiableOn_ψ i₀
  ne_zero _ hx := c.ne_zero_of_mem hx h₀

@[simp]
lemma centre_it : (c.centre h₀ i₀).it = c.it :=
  rfl

@[simp]
lemma centre_iw : (c.centre h₀ i₀).iw = c.iw :=
  rfl

@[simp]
lemma centre_φ : (c.centre h₀ i₀).φ = c.ψ i₀ :=
  rfl

/-! ### Strict transforms -/

open Classical in
/-- **The strict transforms** `χᵢ = (ψᵢ - ψᵢ₀) / t = t ^ (kᵢᵢ₀ - 1) uᵢᵢ₀`. -/
def strict (i : Fin c.m) (x : Cn.{u} n) : ℂ :=
  if i = i₀ then 0 else x c.it ^ (c.k i i₀ - 1) * c.unit i i₀ x

variable {i₀}

lemma strict_self (x : Cn.{u} n) : c.strict i₀ i₀ x = 0 := by
  simp [strict]

lemma strict_update (i : Fin c.m) (x : Cn.{u} n) (a : ℂ) :
    c.strict i₀ i (Function.update x c.iw a) = c.strict i₀ i x := by
  simp only [strict, c.update_it_iw, c.unit_update]

lemma differentiableOn_strict (i : Fin c.m) :
    DifferentiableOn ℂ (c.strict i₀ i) (cyl N c.iw) := by
  unfold strict
  split_ifs
  · exact differentiableOn_const 0
  · exact ((differentiable_apply c.it).pow _).differentiableOn.mul (c.differentiableOn_unit _ _)

variable (hk : ∀ i j, i ≠ j → 1 ≤ c.k i j)
include hk

lemma ψ_eq_strict (i : Fin c.m) {x : Cn.{u} n} (hx : x ∈ cyl N c.iw) :
    c.ψ i x = c.ψ i₀ x + x c.it * c.strict i₀ i x := by
  unfold strict
  split_ifs with h
  · subst h
    ring
  · rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel (hk i i₀ h), ← c.sub_eq_unit h hx]
    ring

lemma strict_sub (i j : Fin c.m) (hij : i ≠ j) {x : Cn.{u} n} (hx : x ∈ cyl N c.iw) :
    c.strict i₀ i x - c.strict i₀ j x = x c.it ^ (c.k i j - 1) * c.unit i j x := by
  have hU := isOpen_cyl N c.iw
  have hZ : interior (cyl N c.iw ∩ (fun x : Cn.{u} n ↦ x c.it) ⁻¹' {0}) = ∅ :=
    subset_empty_iff.1 ((interior_mono inter_subset_right).trans
      (interior_setOf_apply_eq_zero c.it).subset)
  refine EqOn.of_eqOn_diff_zero hU hZ (((c.differentiableOn_strict i).sub
    (c.differentiableOn_strict j)).continuousOn)
    ((((differentiable_apply c.it).pow _).differentiableOn.mul
      (c.differentiableOn_unit i j)).continuousOn) (fun x hx ↦ ?_) hx
  have ht : x c.it ≠ 0 := hx.2
  refine mul_left_cancel₀ ht ?_
  simp only [Pi.sub_apply, Pi.mul_apply, Pi.pow_apply]
  rw [mul_sub, ← mul_assoc, ← pow_succ', Nat.sub_add_cancel (hk i j hij), ← c.sub_eq_unit hij hx.1,
    c.ψ_eq_strict (i₀ := i₀) hk i hx.1, c.ψ_eq_strict (i₀ := i₀) hk j hx.1]
  ring

omit hk in
lemma mem_cyl_of_mem_cyl_M₁ {x : Cn.{u} n} (hx : x ∈ cyl (c.centre h₀ i₀).M₁ c.iw) :
    x ∈ cyl N c.iw := by
  obtain ⟨a, ha⟩ := hx
  change (c.centre h₀ i₀).ch₁ (Function.update x c.iw a) ∈ N at ha
  simp only [BlowupCentre.ch₁, centre_iw, Function.update_idem] at ha
  exact ⟨_, ha⟩

/-- **The configuration on the first chart**: the strict transforms, with contact orders lowered
by one. -/
def chart₁Config : GraphConfig (c.centre h₀ i₀).M₁ ((c.centre h₀ i₀).M₁₀ h₀) where
  it := c.it
  iw := c.iw
  it_ne_iw := c.it_ne_iw
  m := c.m
  ψ := c.strict i₀
  ψ_update := c.strict_update
  differentiableOn_ψ i :=
    (c.differentiableOn_strict i).mono fun _ hx ↦ c.mem_cyl_of_mem_cyl_M₁ h₀ hx
  k i j := c.k i j - 1
  exists_unit i j hij := ⟨c.unit i j, c.unit_update i j,
    (c.differentiableOn_unit i j).mono fun _ hx ↦ c.mem_cyl_of_mem_cyl_M₁ h₀ hx,
    fun _ hx ↦ c.unit_ne_zero i j (c.mem_cyl_of_mem_cyl_M₁ h₀ hx),
    fun _ hx ↦ c.strict_sub hk i j hij (c.mem_cyl_of_mem_cyl_M₁ h₀ hx)⟩
  mem_iff x hx := by
    have hxN : (c.centre h₀ i₀).ch₁ x ∈ N := hx
    have hxc : x ∈ cyl N c.iw := (c.centre h₀ i₀).mem_cyl_of_ch₁_mem hxN
    change (c.centre h₀ i₀).ch₁ x ∈ N₀ ↔ _
    refine (c.mem_iff _ hxN).trans ?_
    have e₁ : (c.centre h₀ i₀).ch₁ x c.it = x c.it := (c.centre h₀ i₀).ch₁_it x
    have e₂ : (c.centre h₀ i₀).ch₁ x c.iw = c.ψ i₀ x + x c.it * x c.iw :=
      (c.centre h₀ i₀).ch₁_iw x
    have e₃ (i : Fin c.m) : c.ψ i ((c.centre h₀ i₀).ch₁ x) = c.ψ i₀ x + x c.it * c.strict i₀ i x
        := by
      rw [BlowupCentre.ch₁, centre_iw, c.ψ_update, c.ψ_eq_strict hk i hxc]
    simp only [e₁, e₂, e₃, ne_eq, add_right_inj]
    exact and_congr_right fun ht ↦ forall_congr' fun i ↦ not_congr (mul_right_inj' ht)

@[simp]
lemma chart₁Config_k (i j : Fin c.m) :
    (c.chart₁Config h₀ (i₀ := i₀) hk).k i j = c.k i j - 1 :=
  rfl

omit hk in
/-- Over `N°`, the first chart lies in `v ≠ 0`: the graph `w = ψᵢ₀` becomes `v = 0`. -/
lemma ne_zero_of_mem_M₁₀ {x : Cn.{u} n} (hx : x ∈ (c.centre h₀ i₀).M₁₀ h₀) : x c.iw ≠ 0 := by
  have hx' : (c.centre h₀ i₀).ch₁ x ∈ N₀ := hx
  have := ((c.mem_iff _ (h₀ hx')).1 hx').2 i₀
  rw [BlowupCentre.ch₁, centre_iw, c.ψ_update, Function.update_self, centre_φ, ne_eq,
    add_eq_left, mul_eq_zero, not_or] at this
  exact this.2

/-! ### The transition from the first to the second chart -/

omit hk in
lemma swapChart_mem_M₂₀_iff (x : Cn.{u} n) :
    swapChart c.it c.iw x ∈ (c.centre h₀ i₀).M₂₀ h₀ ↔ x ∈ (c.centre h₀ i₀).M₁₀ h₀ := by
  set C := c.centre h₀ i₀
  constructor
  · intro hx
    have hx' : C.ch₂ (swapChart C.it C.iw x) ∈ N₀ := hx
    by_cases hv : x c.iw = 0
    · refine absurd (C.ne_zero _ hx') ?_
      rw [BlowupCentre.ch₂_it]
      change ¬(swapChart c.it c.iw x c.it * swapChart c.it c.iw x c.iw ≠ 0)
      rw [swapChart_iw, hv, inv_zero, mul_zero, ne_eq, not_not]
    · change C.ch₁ x ∈ N₀
      rwa [← C.ch₂_swapChart hv]
  · intro hx
    have hv := c.ne_zero_of_mem_M₁₀ h₀ hx
    change C.ch₂ (swapChart C.it C.iw x) ∈ N₀
    rw [C.ch₂_swapChart hv]
    exact hx

omit hk in
variable (i₀) in
/-- **The transition** `(…, t, v) ↦ (…, t v, v⁻¹)` from the first chart over `N°` to the second.
-/
def swapMap : ChartMap ((c.centre h₀ i₀).M₁₀ h₀) ((c.centre h₀ i₀).M₂₀ h₀) where
  χ := swapChart c.it c.iw
  χInv := swapChart c.it c.iw
  R := {a | a c.iw ≠ 0}
  isOpen_R := isOpen_ne_fun (continuous_apply c.iw) continuous_const
  differentiableOn_χ := differentiableOn_swapChart.mono fun _ hx ↦ c.ne_zero_of_mem_M₁₀ h₀ hx
  differentiableOn_χInv := differentiableOn_swapChart
  mem_iff x := (c.swapChart_mem_M₂₀_iff h₀ x).symm
  χ_mem_R x hx := by
    change swapChart c.it c.iw x c.iw ≠ 0
    rw [swapChart_iw]
    exact inv_ne_zero (c.ne_zero_of_mem_M₁₀ h₀ hx)
  χInv_χ x hx := swapChart_swapChart c.it_ne_iw (c.ne_zero_of_mem_M₁₀ h₀ hx)
  χ_χInv y hy _ := swapChart_swapChart c.it_ne_iw hy

variable (i₀) in
/-- The part `v ≠ 0` of the first chart. -/
def swapDom : (AnalyticSpace.complexAffineSpace.{u} n).Opens :=
  ⟨{x | x ∈ (c.centre h₀ i₀).M₁ ∧ x c.iw ≠ 0}, by
    change IsOpen ({x : Cn.{u} n | x ∈ (c.centre h₀ i₀).M₁} ∩ {x : Cn.{u} n | x c.iw ≠ 0})
    exact (isOpen_setOf_mem _).inter (isOpen_ne_fun (continuous_apply c.iw) continuous_const)⟩

omit hk in
lemma swapDom_le : c.swapDom h₀ i₀ ≤ (c.centre h₀ i₀).M₁ :=
  fun _ hx ↦ hx.1

omit hk in
lemma M₁₀_le_swapDom : (c.centre h₀ i₀).M₁₀ h₀ ≤ c.swapDom h₀ i₀ :=
  fun _ hx ↦ ⟨(c.centre h₀ i₀).M₁₀_le h₀ hx, c.ne_zero_of_mem_M₁₀ h₀ hx⟩

variable (i₀) in
/-- The transition is a biholomorphism from `v ≠ 0` in the first chart onto `v' ≠ 0` in the
second chart. -/
def swapBiholo : ChartBiholo (c.swapMap h₀ i₀) (c.swapDom h₀ i₀) (c.centre h₀ i₀).M₂ where
  D := {x | x ∈ (c.centre h₀ i₀).M₁ ∧ x c.iw ≠ 0}
  E := {a | a ∈ (c.centre h₀ i₀).M₂ ∧ a c.iw ≠ 0}
  isOpen_D := (c.swapDom h₀ i₀).isOpen
  isOpen_E := (c.centre h₀ i₀).M₂.isOpen.inter
    (isOpen_ne_fun (continuous_apply c.iw) continuous_const)
  D_sub _ hx := hx
  E_sub _ ha := ha.1
  E_sub_R _ ha := ha.2
  mapsTo x hx := by
    refine ⟨?_, ?_⟩
    · have h₁ : (c.centre h₀ i₀).ch₁ x ∈ N := hx.1
      have e : (c.centre h₀ i₀).ch₂ (swapChart c.it c.iw x) = (c.centre h₀ i₀).ch₁ x :=
        (c.centre h₀ i₀).ch₂_swapChart hx.2
      rw [← e] at h₁
      exact h₁
    · change swapChart c.it c.iw x c.iw ≠ 0
      rw [swapChart_iw]
      exact inv_ne_zero hx.2
  inv_mem a ha := by
    refine ⟨?_, ?_⟩
    · have h₁ : (c.centre h₀ i₀).ch₂ a ∈ N := ha.1
      have e : (c.centre h₀ i₀).ch₁ (swapChart c.it c.iw a) = (c.centre h₀ i₀).ch₂ a :=
        (c.centre h₀ i₀).ch₁_swapChart ha.2
      rw [← e] at h₁
      exact h₁
    · change swapChart c.it c.iw a c.iw ≠ 0
      rw [swapChart_iw]
      exact inv_ne_zero ha.2
  inv_χ x hx := swapChart_swapChart c.it_ne_iw hx.2
  χ_inv a ha := swapChart_swapChart c.it_ne_iw ha.2
  differentiableOn_χ := differentiableOn_swapChart.mono fun _ hx ↦ hx.2
  differentiableOn_χInv := differentiableOn_swapChart.mono fun _ ha ↦ ha.2

/-! ### Freeness near `v' = 0` in the second chart and off the centre -/

section Free

variable (W : FiniteEtaleOver (space N₀)) [T2Space W.left]

omit hk in
lemma ta_mem_cyl {a : Cn.{u} n} (ha : a ∈ (c.centre h₀ i₀).M₂) :
    (c.centre h₀ i₀).ta a ∈ cyl N c.iw :=
  (c.centre h₀ i₀).M₂_le_dom₂ ha

/-- The pullback of `N ∖ N°` to the second chart near `v' = 0` is `{s v' = 0}`. -/
theorem exists_isFreeSpanAt_chart₂ {W₂ : FiniteEtaleOver (space ((c.centre h₀ i₀).M₂₀ h₀))}
    [T2Space W₂.left] {a₀ : Cn.{u} n} (ha₀ : a₀ ∈ (c.centre h₀ i₀).M₂) (hv : a₀ c.iw = 0) :
    ∃ (U : (space (c.centre h₀ i₀).M₂).Opens) (k : ℕ)
      (e : Fin k → (boundedModule ((c.centre h₀ i₀).M₂₀_le h₀) W₂).val.obj (op U)),
      a₀ ∈ img U ∧ ∀ y ∈ U, IsFreeSpanAt ((c.centre h₀ i₀).M₂₀_le h₀) W₂ e y := by
  let C := c.centre h₀ i₀
  set O : Set (Cn.{u} n) :=
    {a | a ∈ C.M₂ ∧ ∀ i ∈ Finset.univ, a c.iw * c.strict i₀ i (C.ta a) ≠ 1}
  have hc (i : Fin c.m) : ContinuousOn (fun a ↦ a c.iw * c.strict i₀ i (C.ta a))
      {a : Cn.{u} n | a ∈ C.M₂} :=
    (continuous_apply c.iw).continuousOn.mul ((c.differentiableOn_strict i).continuousOn.comp
      C.continuous_ta.continuousOn fun _ ha ↦ c.ta_mem_cyl h₀ ha)
  have hO : IsOpen O := by
    have : O = {a : Cn.{u} n | a ∈ C.M₂} ∩
        ⋂ i ∈ Finset.univ, {a | a ∈ C.M₂ ∧ a c.iw * c.strict i₀ i (C.ta a) ≠ 1} := by
      ext a
      simp only [O, mem_setOf_eq, mem_inter_iff, mem_iInter]
      exact ⟨fun h ↦ ⟨h.1, fun i hi ↦ ⟨h.1, h.2 i hi⟩⟩, fun h ↦ ⟨h.1, fun i hi ↦ (h.2 i hi).2⟩⟩
    rw [this]
    refine (isOpen_setOf_mem _).inter (isOpen_biInter_finset fun i _ ↦ ?_)
    have := (hc i).isOpen_inter_preimage C.M₂.isOpen (isOpen_compl_singleton (x := (1 : ℂ)))
    exact this
  refine exists_isFreeSpanAt_of_form (C.M₂₀_le h₀) W₂ c.it_ne_iw isOpen_univ
    (fun _ _ _ ↦ mem_univ _) (ψ₀ := fun _ ↦ 0) (fun _ _ ↦ rfl) (differentiableOn_const 0) hO
    (subset_univ _) (fun a ha ↦ ha.1) True True (fun a ha ↦ ?_)
    ⟨ha₀, fun i _ ↦ by rw [hv, zero_mul]; exact zero_ne_one⟩
  have haN : C.ch₂ a ∈ N := ha.1
  have hta := c.ta_mem_cyl h₀ ha.1
  change C.ch₂ a ∈ N₀ ↔ _
  refine (c.mem_iff _ haN).trans ?_
  have e₁ : C.ch₂ a c.it = a c.it * a c.iw := C.ch₂_it a
  have e₂ : C.ch₂ a c.iw = c.ψ i₀ (C.ta a) + a c.it := C.ch₂_iw a
  have e₃ (i : Fin c.m) : c.ψ i (C.ch₂ a) = c.ψ i₀ (C.ta a) + a c.it * a c.iw *
      c.strict i₀ i (C.ta a) := by
    rw [BlowupCentre.ch₂, centre_iw, c.ψ_update, c.ψ_eq_strict hk i hta]
    congr 2
    exact Function.update_self _ _ _
  simp only [e₁, e₂, e₃, ne_eq, add_right_inj, mul_eq_zero, not_or, forall_const]
  constructor
  · rintro ⟨h, -⟩
    exact h
  · rintro ⟨hs, hv'⟩
    refine ⟨⟨hs, hv'⟩, fun i h ↦ ha.2 i (Finset.mem_univ i) ?_⟩
    have h' : a c.it * 1 = a c.it * (a c.iw * c.strict i₀ i (C.ta a)) := by
      rw [mul_one]
      nth_rewrite 1 [h]
      ring
    exact (mul_left_cancel₀ hs h').symm

/-- **Off the centre, `N ∖ N°` has normal crossings**, so `𝒜` is free there. -/
theorem exists_isFreeSpanAt_of_not_mem_centre {x₀ : Cn.{u} n} (hx₀ : x₀ ∈ N)
    (hC : x₀ ∉ (c.centre h₀ i₀).toBlowupData.centre) :
    ∃ (U : (space N).Opens) (k : ℕ) (e : Fin k → (boundedModule h₀ W).val.obj (op U)),
      x₀ ∈ img U ∧ ∀ y ∈ U, IsFreeSpanAt h₀ W e y := by
  refine c.exists_isFreeSpanAt_of_subsingleton h₀ W hx₀ fun i j hi hj ↦ ?_
  have hcyl : x₀ ∈ cyl N c.iw := mem_cyl_of_mem hx₀
  by_cases ht : x₀ c.it = 0
  · refine absurd ⟨ht, ?_⟩ hC
    change x₀ c.iw - c.ψ i₀ x₀ = 0
    rw [← hi, c.ψ_eq_strict hk i hcyl, ht, zero_mul, add_zero, sub_self]
  · by_contra hij
    exact c.ψ_ne_of_ne hij hcyl ht (hi.trans hj.symm)

end Free

end GraphConfig

end

end ComplexAnalytic.BoundedSections
