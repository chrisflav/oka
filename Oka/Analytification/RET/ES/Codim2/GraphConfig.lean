/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.ES.Codim2.CoordFreeness
import Oka.Analytification.RET.ES.Codim2.BlowupPushdown

/-!
# Families of graphs meeting along `t = 0`

Let `t = x_{i_t}` and `w = x_{i_w}` be two coordinates of `ℂⁿ`. A *graph configuration* on `N`
(`ComplexAnalytic.BoundedSections.GraphConfig`) consists of finitely many functions `ψᵢ`
independent of `w` and holomorphic over `N`, whose pairwise differences are `t ^ kᵢⱼ` times
functions without zeros, such that `N ∖ N°` is the union of the hyperplane `t = 0` and the graphs
`w = ψᵢ`. This is the shape of the branch locus near a point of `t = 0` after a Puiseux base
change, and it is preserved by blowing up `{t = 0, w = ψᵢ₀}` (in the first chart, with contact
orders lowered by one).

This file proves the elementary properties of graph configurations:

- the complement of `N°` is thin (`…GraphConfig.hasThinComplement`);
- near a point through which at most one graph passes, `N ∖ N°` has normal crossings and `𝒜` is
  free (`…GraphConfig.exists_isFreeSpanAt_of_subsingleton`);
- the configuration restricts to open subsets containing `N°`
  (`…GraphConfig.mono`), and near a point only the graphs through it matter
  (`…GraphConfig.localize`).

## Main definitions

- `ComplexAnalytic.BoundedSections.GraphConfig N N₀`: a graph configuration.
-/

open CategoryTheory Opposite AlgebraicGeometry Topology TopologicalSpace Filter Set

universe u

namespace ComplexAnalytic.BoundedSections

open AnalyticSpace

noncomputable section

variable {n : ℕ}

/-- **A configuration of graphs meeting along `t = 0`.** Two coordinates `t = x_{i_t}`,
`w = x_{i_w}` and finitely many functions `ψᵢ` independent of `w` and holomorphic on the cylinder
over `N` in the direction of `w`, such that `ψᵢ - ψⱼ = t ^ kᵢⱼ uᵢⱼ` with `uᵢⱼ` independent of `w`
and without zeros, and such that a point of `N` lies in `N°` if and only if `t ≠ 0` and `w ≠ ψᵢ`
for all `i`. -/
structure GraphConfig (N N₀ : (AnalyticSpace.complexAffineSpace.{u} n).Opens) where
  /-- The coordinate `t`. -/
  it : ULift.{u} (Fin n)
  /-- The coordinate `w`. -/
  iw : ULift.{u} (Fin n)
  it_ne_iw : it ≠ iw
  /-- The number of graphs. -/
  m : ℕ
  /-- The graphs `w = ψᵢ`. -/
  ψ : Fin m → Cn.{u} n → ℂ
  ψ_update : ∀ i x a, ψ i (Function.update x iw a) = ψ i x
  differentiableOn_ψ : ∀ i, DifferentiableOn ℂ (ψ i) (cyl N iw)
  /-- The contact orders. -/
  k : Fin m → Fin m → ℕ
  exists_unit : ∀ i j, i ≠ j → ∃ u : Cn.{u} n → ℂ, (∀ x a, u (Function.update x iw a) = u x) ∧
    DifferentiableOn ℂ u (cyl N iw) ∧ (∀ x ∈ cyl N iw, u x ≠ 0) ∧
    ∀ x ∈ cyl N iw, ψ i x - ψ j x = x it ^ k i j * u x
  mem_iff : ∀ x ∈ N, x ∈ N₀ ↔ x it ≠ 0 ∧ ∀ i, x iw ≠ ψ i x

/-! ### Normal crossings of `t = 0` and a graph -/

section Form

variable {N N₀ : (AnalyticSpace.complexAffineSpace.{u} n).Opens} (h₀ : N₀ ≤ N)
  (W : FiniteEtaleOver (space N₀)) [T2Space W.left]

/-- **`𝒜` is free near a point of `{t = 0} ∪ {w = ψ₀}`.** Let `ψ₀` be independent of `w` and
holomorphic on an open `G` stable under changing `w`, and suppose that on an open `O ⊆ G ∩ N` a
point lies in `N°` if and only if `t ≠ 0` (if `vt` holds) and `w ≠ ψ₀` (if `gr` holds). Then
`𝒜` is free near every point of a neighbourhood of each point of `O`. -/
theorem exists_isFreeSpanAt_of_form {it iw : ULift.{u} (Fin n)} (hne : it ≠ iw)
    {G : Set (Cn.{u} n)} (hG : IsOpen G) (hGsat : ∀ x ∈ G, ∀ a, Function.update x iw a ∈ G)
    {ψ₀ : Cn.{u} n → ℂ} (hψ₀ : ∀ x a, ψ₀ (Function.update x iw a) = ψ₀ x)
    (hψ₀d : DifferentiableOn ℂ ψ₀ G) {O : Set (Cn.{u} n)} (hO : IsOpen O) (hOG : O ⊆ G)
    (hON : ∀ x ∈ O, x ∈ N) (vt gr : Prop)
    (hmem : ∀ x ∈ O, x ∈ N₀ ↔ (vt → x it ≠ 0) ∧ (gr → x iw ≠ ψ₀ x)) {x₀ : Cn.{u} n}
    (hx₀ : x₀ ∈ O) :
    ∃ (U : (space N).Opens) (k : ℕ) (e : Fin k → (boundedModule h₀ W).val.obj (op U)),
      x₀ ∈ img U ∧ ∀ y ∈ U, IsFreeSpanAt h₀ W e y := by
  classical
  set O₁ : Set (Cn.{u} n) := O ∩ {x | x₀ it ≠ 0 → x it ≠ 0} ∩ {x | x₀ iw ≠ ψ₀ x₀ → x iw ≠ ψ₀ x}
  have hO₁ : IsOpen O₁ := by
    have h₁ : IsOpen {x : Cn.{u} n | x₀ it ≠ 0 → x it ≠ 0} := by
      by_cases h : x₀ it = 0
      · simp [h]
      · simpa [h] using isOpen_ne_fun (continuous_apply it) continuous_const
    have h₂ : IsOpen (O ∩ {x : Cn.{u} n | x₀ iw ≠ ψ₀ x₀ → x iw ≠ ψ₀ x}) := by
      by_cases h : x₀ iw = ψ₀ x₀
      · simpa [h] using hO
      · simp only [ne_eq, h, not_false_eq_true, forall_const]
        have := ((continuous_apply iw).continuousOn.sub (hψ₀d.mono hOG).continuousOn
          |>.isOpen_inter_preimage hO (isOpen_compl_singleton (x := (0 : ℂ))))
        convert this using 1
        ext x
        simp [sub_eq_zero]
    have : O₁ = (O ∩ {x : Cn.{u} n | x₀ iw ≠ ψ₀ x₀ → x iw ≠ ψ₀ x}) ∩
        {x | x₀ it ≠ 0 → x it ≠ 0} := by
      ext x; simp only [O₁, mem_inter_iff]; tauto
    rw [this]
    exact h₂.inter h₁
  set Φ : Cn.{u} n → Cn.{u} n := fun x ↦ Function.update x iw (x iw - ψ₀ x)
  set Φ' : Cn.{u} n → Cn.{u} n := fun z ↦ Function.update z iw (z iw + ψ₀ z)
  have hΦ'Φ (x : Cn.{u} n) : Φ' (Φ x) = x := by
    simp only [Φ, Φ', hψ₀, Function.update_self, Function.update_idem, sub_add_cancel,
      Function.update_eq_self]
  have hΦΦ' (z : Cn.{u} n) : Φ (Φ' z) = z := by
    simp only [Φ, Φ', hψ₀, Function.update_self, Function.update_idem, add_sub_cancel_right,
      Function.update_eq_self]
  have hΦt (x : Cn.{u} n) : Φ x it = x it := Function.update_of_ne hne _ _
  have hΦw (x : Cn.{u} n) : Φ x iw = x iw - ψ₀ x := Function.update_self _ _ _
  have hΦ'G : ∀ z ∈ G, Φ' z ∈ G := fun z hz ↦ hGsat z hz _
  have hΦ'd : DifferentiableOn ℂ Φ' G :=
    differentiableOn_update differentiableOn_id
      ((differentiable_apply iw).differentiableOn.add hψ₀d) iw
  set O' : Set (Cn.{u} n) := G ∩ Φ' ⁻¹' O₁
  have hO' : IsOpen O' := hΦ'd.continuousOn.isOpen_inter_preimage hG hO₁
  have hx₀O₁ : x₀ ∈ O₁ := ⟨⟨hx₀, fun h ↦ h⟩, fun h ↦ h⟩
  refine exists_isFreeSpanAt_of_coords h₀ W hO₁ (fun x hx ↦ hON x hx.1.1) hO'
    (Φ := Φ) (Φ' := Φ')
    ((differentiableOn_update differentiableOn_id
      ((differentiable_apply iw).differentiableOn.sub hψ₀d) iw).mono
        fun x hx ↦ hOG hx.1.1) (hΦ'd.mono fun z hz ↦ hz.1)
    (fun x hx ↦ ⟨hGsat x (hOG hx.1.1) _, by simp only [mem_preimage, hΦ'Φ]; exact hx⟩)
    (fun z hz ↦ hz.2) (fun x _ ↦ hΦ'Φ x) (fun z _ ↦ hΦΦ' z)
    ((if vt ∧ x₀ it = 0 then {it} else ∅) ∪ (if gr ∧ x₀ iw = ψ₀ x₀ then {iw} else ∅))
    (fun x hx ↦ ?_) hx₀O₁ fun j hj ↦ ?_
  · rw [hmem x hx.1.1]
    simp only [Finset.mem_union]
    constructor
    · rintro ⟨h₁, h₂⟩ j hj
      rcases hj with hj | hj
      · split_ifs at hj with h
        · rw [Finset.mem_singleton.1 hj, hΦt]
          exact h₁ h.1
        · simp at hj
      · split_ifs at hj with h
        · rw [Finset.mem_singleton.1 hj, hΦw, sub_ne_zero]
          exact h₂ h.1
        · simp at hj
    · intro h
      refine ⟨fun hvt ↦ ?_, fun hgr ↦ ?_⟩
      · by_cases h0 : x₀ it = 0
        · have := h it (Or.inl (by simp [hvt, h0]))
          rwa [hΦt] at this
        · exact hx.1.2 h0
      · by_cases h0 : x₀ iw = ψ₀ x₀
        · have := h iw (Or.inr (by simp [hgr, h0]))
          rwa [hΦw, sub_ne_zero] at this
        · exact hx.2 h0
  · simp only [Finset.mem_union] at hj
    rcases hj with hj | hj
    · split_ifs at hj with h
      · rw [Finset.mem_singleton.1 hj, hΦt]
        exact h.2
      · simp at hj
    · split_ifs at hj with h
      · rw [Finset.mem_singleton.1 hj, hΦw, sub_eq_zero]
        exact h.2
      · simp at hj

end Form

namespace GraphConfig

variable {N N₀ : (AnalyticSpace.complexAffineSpace.{u} n).Opens} (c : GraphConfig N N₀)

lemma ne_zero_of_mem {x : Cn.{u} n} (hx : x ∈ N₀) (h₀ : N₀ ≤ N) : x c.it ≠ 0 :=
  ((c.mem_iff x (h₀ hx)).1 hx).1

lemma update_it_iw (x : Cn.{u} n) (a : ℂ) : Function.update x c.iw a c.it = x c.it :=
  Function.update_of_ne c.it_ne_iw _ _

/-- Distinct graphs are disjoint over `t ≠ 0`. -/
lemma ψ_ne_of_ne {i j : Fin c.m} (hij : i ≠ j) {x : Cn.{u} n} (hx : x ∈ cyl N c.iw)
    (ht : x c.it ≠ 0) : c.ψ i x ≠ c.ψ j x := by
  obtain ⟨u, -, -, hu0, hψ⟩ := c.exists_unit i j hij
  rw [ne_eq, ← sub_eq_zero, hψ x hx]
  exact mul_ne_zero (pow_ne_zero _ ht) (hu0 x hx)

/-- Two graphs meet over a point of `t = 0` if and only if their contact order is positive. -/
lemma ψ_eq_iff {i j : Fin c.m} (hij : i ≠ j) {x : Cn.{u} n} (hx : x ∈ cyl N c.iw)
    (ht : x c.it = 0) : c.ψ i x = c.ψ j x ↔ 1 ≤ c.k i j := by
  obtain ⟨u, -, -, hu0, hψ⟩ := c.exists_unit i j hij
  rw [← sub_eq_zero, hψ x hx, ht, mul_eq_zero, pow_eq_zero_iff', Nat.one_le_iff_ne_zero]
  simp [hu0 x hx]

lemma continuousOn_ψ (i : Fin c.m) : ContinuousOn (c.ψ i) (cyl N c.iw) :=
  (c.differentiableOn_ψ i).continuousOn

/-! ### Restriction -/

/-- **Restriction** to an open `N' ⊆ N` containing `N°`. -/
def mono {N' : (AnalyticSpace.complexAffineSpace.{u} n).Opens} (hN' : N' ≤ N) :
    GraphConfig N' N₀ where
  it := c.it
  iw := c.iw
  it_ne_iw := c.it_ne_iw
  m := c.m
  ψ := c.ψ
  ψ_update := c.ψ_update
  differentiableOn_ψ i := (c.differentiableOn_ψ i).mono fun _ ⟨a, ha⟩ ↦ ⟨a, hN' ha⟩
  k := c.k
  exists_unit i j hij := by
    obtain ⟨u, hu, hud, hu0, hψ⟩ := c.exists_unit i j hij
    exact ⟨u, hu, hud.mono fun _ ⟨a, ha⟩ ↦ ⟨a, hN' ha⟩, fun x ⟨a, ha⟩ ↦ hu0 x ⟨a, hN' ha⟩,
      fun x ⟨a, ha⟩ ↦ hψ x ⟨a, hN' ha⟩⟩
  mem_iff x hx := c.mem_iff x (hN' hx)

/-- **Localization** to an open `N' ⊆ N` containing `N°` over which only the graphs indexed by
`J` meet `N'`. -/
def localize {N' : (AnalyticSpace.complexAffineSpace.{u} n).Opens} (hN' : N' ≤ N)
    (J : Finset (Fin c.m)) (hJ : ∀ x ∈ N', ∀ i ∉ J, x c.iw ≠ c.ψ i x) : GraphConfig N' N₀ where
  it := c.it
  iw := c.iw
  it_ne_iw := c.it_ne_iw
  m := J.card
  ψ i := c.ψ (J.equivFin.symm i)
  ψ_update i := c.ψ_update _
  differentiableOn_ψ i := (c.differentiableOn_ψ _).mono fun _ ⟨a, ha⟩ ↦ ⟨a, hN' ha⟩
  k i j := c.k (J.equivFin.symm i) (J.equivFin.symm j)
  exists_unit i j hij := by
    obtain ⟨u, hu, hud, hu0, hψ⟩ := c.exists_unit (J.equivFin.symm i) (J.equivFin.symm j)
      fun h ↦ hij (J.equivFin.symm.injective (Subtype.ext h))
    exact ⟨u, hu, hud.mono fun _ ⟨a, ha⟩ ↦ ⟨a, hN' ha⟩, fun x ⟨a, ha⟩ ↦ hu0 x ⟨a, hN' ha⟩,
      fun x ⟨a, ha⟩ ↦ hψ x ⟨a, hN' ha⟩⟩
  mem_iff x hx := by
    rw [c.mem_iff x (hN' hx)]
    refine and_congr_right fun _ ↦ ⟨fun h i ↦ h _, fun h i ↦ ?_⟩
    by_cases hi : i ∈ J
    · simpa using h (J.equivFin ⟨i, hi⟩)
    · exact hJ x hx i hi

/-! ### The complement of `N°` is thin -/

include c in
/-- **The complement of `N°` is thin**: it lies in the zero set of `t ∏ᵢ (w - ψᵢ)`. -/
theorem hasThinComplement : HasThinComplement N N₀ := by
  classical
  refine ⟨fun x ↦ x c.it * ∏ i, (x c.iw - c.ψ i x), ?_, ?_, fun x hx hx₀ ↦ ?_⟩
  · have e : (fun x : Cn.{u} n ↦ ∏ i, (x c.iw - c.ψ i x)) = ∏ i, fun x ↦ x c.iw - c.ψ i x := by
      funext x
      simp [Finset.prod_apply]
    refine (differentiable_apply c.it).differentiableOn.mul ?_
    rw [e]
    refine Finset.prod_induction _ (fun g ↦ DifferentiableOn ℂ g {x : Cn.{u} n | x ∈ N})
      (fun f g hf hg ↦ hf.mul hg) (differentiableOn_const 1) fun i _ ↦ ?_
    exact (differentiable_apply c.iw).differentiableOn.sub
      ((c.differentiableOn_ψ i).mono fun _ hy ↦ mem_cyl_of_mem hy)
  · change interior (({x : Cn.{u} n | x ∈ N}) ∩
      (fun x : Cn.{u} n ↦ x c.it * ∏ i, (x c.iw - c.ψ i x)) ⁻¹' {0}) = ∅
    refine eq_empty_of_forall_notMem fun x hx ↦ ?_
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 isOpen_interior x hx
    have hr2 : 0 < r / 2 := half_pos hr
    -- a point near `x` off `t = 0`
    set δ : ℂ := if x c.it = 0 then ((r / 4 : ℝ) : ℂ) else 0 with hδ
    have hδr : ‖δ‖ < r / 2 := by
      rw [hδ]
      split_ifs
      · rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
        linarith
      · simpa using hr2
    have hδt : x c.it + δ ≠ 0 := by
      rw [hδ]
      split_ifs with h
      · rw [h, zero_add]
        exact_mod_cast (by positivity : (r / 4 : ℝ) ≠ 0)
      · simpa using h
    set x' := Function.update x c.it (x c.it + δ)
    -- a value of `w` near `x c.iw` off the graphs
    have hinf : (Metric.ball (x c.iw) (r / 2)).Infinite :=
      infinite_of_mem_nhds _ (Metric.ball_mem_nhds _ hr2)
    obtain ⟨a, ha, haF⟩ := (hinf.sdiff (Set.finite_range fun i ↦ c.ψ i x')).nonempty
    set z := Function.update x' c.iw a
    have hz : z ∈ Metric.ball x r := by
      rw [Metric.mem_ball, dist_pi_lt_iff hr]
      intro j
      by_cases hjw : j = c.iw
      · subst hjw
        simp only [z, Function.update_self]
        exact (Metric.mem_ball.1 ha).trans (by linarith)
      by_cases hjt : j = c.it
      · subst hjt
        simp only [z, x', Function.update_of_ne hjw, Function.update_self, dist_eq_norm,
          add_sub_cancel_left]
        exact hδr.trans (by linarith)
      · simp [z, x', Function.update_of_ne hjw, Function.update_of_ne hjt, hr]
    have hzZ := interior_subset (hball hz)
    refine absurd hzZ.2 ?_
    change ¬(z c.it * ∏ i, (z c.iw - c.ψ i z) = 0)
    have hzt : z c.it = x c.it + δ := by
      simp [z, x', c.update_it_iw, Function.update_self]
    have hzw : z c.iw = a := Function.update_self _ _ _
    have hψz (i : Fin c.m) : c.ψ i z = c.ψ i x' := c.ψ_update _ _ _
    rw [hzt, hzw, mul_eq_zero, not_or]
    refine ⟨hδt, Finset.prod_ne_zero_iff.2 fun i _ ↦ sub_ne_zero.2 fun h ↦ haF ⟨i, ?_⟩⟩
    change c.ψ i x' = a
    rw [← hψz, h]
  · have := (c.mem_iff x hx).not.1 hx₀
    simp only [not_and_or, not_forall, not_not] at this
    rcases this with h | ⟨i, hi⟩
    · simp [h]
    · exact mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ i) (sub_eq_zero.2 hi))

/-! ### Points on at most one graph -/

lemma isOpen_setOf_ne (i : Fin c.m) :
    IsOpen {x : Cn.{u} n | x ∈ cyl N c.iw ∧ x c.iw ≠ c.ψ i x} := by
  have := ((continuous_apply c.iw).continuousOn.sub (c.continuousOn_ψ i)).isOpen_inter_preimage
    (isOpen_cyl N c.iw) (isOpen_compl_singleton (x := (0 : ℂ)))
  convert this using 1
  ext x
  simp [sub_eq_zero]

/-- The points of `N` off the graphs `w = ψᵢ` for the `i ∈ J`. -/
lemma isOpen_off (J : Finset (Fin c.m)) :
    IsOpen {x : Cn.{u} n | x ∈ N ∧ ∀ i ∈ J, x c.iw ≠ c.ψ i x} := by
  have : {x : Cn.{u} n | x ∈ N ∧ ∀ i ∈ J, x c.iw ≠ c.ψ i x} =
      {x : Cn.{u} n | x ∈ N} ∩ ⋂ i ∈ J, {x | x ∈ cyl N c.iw ∧ x c.iw ≠ c.ψ i x} := by
    ext x
    simp only [mem_setOf_eq, mem_inter_iff, mem_iInter]
    exact ⟨fun h ↦ ⟨h.1, fun i hi ↦ ⟨mem_cyl_of_mem h.1, h.2 i hi⟩⟩,
      fun h ↦ ⟨h.1, fun i hi ↦ (h.2 i hi).2⟩⟩
  rw [this]
  exact (isOpen_setOf_mem N).inter (isOpen_biInter_finset fun i _ ↦ c.isOpen_setOf_ne i)

variable (h₀ : N₀ ≤ N) (W : FiniteEtaleOver (space N₀)) [T2Space W.left]

/-- **`𝒜` is free near a point on at most one graph**: near such a point `N ∖ N°` is contained
in `{t = 0} ∪ {w = ψᵢ}`, which has normal crossings. -/
theorem exists_isFreeSpanAt_of_subsingleton {x₀ : Cn.{u} n} (hx₀ : x₀ ∈ N)
    (hsub : ∀ i j, c.ψ i x₀ = x₀ c.iw → c.ψ j x₀ = x₀ c.iw → i = j) :
    ∃ (U : (space N).Opens) (k : ℕ) (e : Fin k → (boundedModule h₀ W).val.obj (op U)),
      x₀ ∈ img U ∧ ∀ y ∈ U, IsFreeSpanAt h₀ W e y := by
  classical
  have hsat : ∀ x ∈ cyl N c.iw, ∀ a, Function.update x c.iw a ∈ cyl N c.iw :=
    fun x hx a ↦ (update_mem_cyl a).2 hx
  set J := Finset.univ.filter fun i ↦ c.ψ i x₀ ≠ x₀ c.iw
  set O := {x : Cn.{u} n | x ∈ N ∧ ∀ i ∈ J, x c.iw ≠ c.ψ i x}
  have hO := c.isOpen_off J
  have hOG : O ⊆ cyl N c.iw := fun x hx ↦ mem_cyl_of_mem hx.1
  have hx₀O : x₀ ∈ O := ⟨hx₀, fun i hi h ↦ (Finset.mem_filter.1 hi).2 h.symm⟩
  by_cases hex : ∃ i, c.ψ i x₀ = x₀ c.iw
  · obtain ⟨i₀, hi₀⟩ := hex
    refine exists_isFreeSpanAt_of_form h₀ W c.it_ne_iw (isOpen_cyl N c.iw) hsat (c.ψ_update i₀)
      (c.differentiableOn_ψ i₀) hO hOG (fun x hx ↦ hx.1) True True (fun x hx ↦ ?_) hx₀O
    refine (c.mem_iff x hx.1).trans ?_
    simp only [forall_const]
    refine and_congr_right fun _ ↦ ⟨fun h ↦ h i₀, fun h i ↦ ?_⟩
    by_cases hi : c.ψ i x₀ = x₀ c.iw
    · rwa [hsub i i₀ hi hi₀]
    · exact hx.2 i (Finset.mem_filter.2 ⟨Finset.mem_univ i, hi⟩)
  · push Not at hex
    refine exists_isFreeSpanAt_of_form h₀ W c.it_ne_iw isOpen_univ (fun _ _ _ ↦ mem_univ _)
      (ψ₀ := fun _ ↦ 0) (fun _ _ ↦ rfl) (differentiableOn_const 0) hO (subset_univ _)
      (fun x hx ↦ hx.1) True False (fun x hx ↦ ?_) hx₀O
    refine (c.mem_iff x hx.1).trans ?_
    simp only [forall_const, IsEmpty.forall_iff, and_true]
    exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, fun i ↦ hx.2 i (Finset.mem_filter.2 ⟨Finset.mem_univ i,
      hex i⟩)⟩⟩

end GraphConfig

end

end ComplexAnalytic.BoundedSections
