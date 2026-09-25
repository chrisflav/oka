/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.ES.Codim2.GraphBlowup

/-!
# Coherence of bounded sections along a graph configuration

Let `c` be a graph configuration on `N` (`ComplexAnalytic.BoundedSections.GraphConfig`): `N ∖ N°`
is the union of `t = 0` and graphs `w = ψᵢ` with `ψᵢ - ψⱼ = t ^ kᵢⱼ uᵢⱼ`. Then the sheaf `𝒜` of
bounded sections of every Hausdorff finite étale cover of `N°` is coherent
(`ComplexAnalytic.BoundedSections.GraphConfig.isCoherent`).

The proof is by induction on a bound `d > kᵢⱼ` for the contact orders. Near a point on at most one
graph, `N ∖ N°` has normal crossings and `𝒜` is free. Near a point `x₀` on several graphs, only the
graphs through `x₀` matter; they pass through `C = {t = 0, w = ψᵢ₀}`, so their contact orders are
positive (`…GraphConfig.localize`). Blow up `C`:

- in the first chart the pullback is a graph configuration with contact orders lowered by one, so
  its bounded sections are coherent by induction;
- in the second chart, near `v' = 0` the pullback of `N ∖ N°` is `{s v' = 0}`, and near
  `v' ≠ 0` the second chart is the first chart
  (`ComplexAnalytic.BoundedSections.GraphConfig.swapBiholo`), so the local conditions for
  coherence transfer along `ComplexAnalytic.BoundedSections.ChartBiholo.isCoherentAt`;
- off `C`, `N ∖ N°` has normal crossings.

By `ComplexAnalytic.BoundedSections.BlowupCentre.exists_isFreeSpanAt` there are sections of `𝒜`
near `x₀` spanning local bases off `C`, and `C` is the zero set of the regular pair
`(t, w - ψᵢ₀)` (`…GraphConfig.centrePair`), so the reflexive hull criterion gives coherence near
`x₀`. Finally the local conditions transfer from the localization back to `N`
(`ComplexAnalytic.BoundedSections.ChartBiholo.ofLE`).

## Main results

- `ComplexAnalytic.BoundedSections.GraphConfig.isCoherent`: `𝒜` is coherent.
-/

open CategoryTheory Opposite AlgebraicGeometry Topology TopologicalSpace Filter Set

universe u

namespace ComplexAnalytic.BoundedSections

open AnalyticSpace

noncomputable section

variable {n : ℕ}

/-! ### Shrinking `N` -/

/-- The identity of `N°` as a `ComplexAnalytic.BoundedSections.ChartMap`. -/
def ChartMap.refl (N₀ : (AnalyticSpace.complexAffineSpace.{u} n).Opens) : ChartMap N₀ N₀ where
  χ := id
  χInv := id
  R := univ
  isOpen_R := isOpen_univ
  differentiableOn_χ := differentiableOn_id
  differentiableOn_χInv := differentiableOn_id
  mem_iff _ := Iff.rfl
  χ_mem_R _ _ := mem_univ _
  χInv_χ _ _ := rfl
  χ_χInv _ _ _ := rfl

lemma IsMapPullback.refl {N₀ : (AnalyticSpace.complexAffineSpace.{u} n).Opens}
    (W : FiniteEtaleOver (space N₀)) : IsMapPullback (ChartMap.refl N₀) W W id where
  continuous := continuous_id
  pt_eq _ := rfl
  ext _ _ _ h := h
  exists_lift w _ h := ⟨w, h, rfl⟩

/-- The inclusion of an open `N' ⊆ N` containing `N°` as a
`ComplexAnalytic.BoundedSections.ChartBiholo`. -/
def ChartBiholo.ofLE {N N' N₀ : (AnalyticSpace.complexAffineSpace.{u} n).Opens} (h : N' ≤ N) :
    ChartBiholo (ChartMap.refl N₀) N' N where
  D := {x | x ∈ N'}
  E := {x | x ∈ N'}
  isOpen_D := isOpen_setOf_mem N'
  isOpen_E := isOpen_setOf_mem N'
  D_sub _ hx := hx
  E_sub _ hx := h hx
  E_sub_R _ _ := mem_univ _
  mapsTo _ hx := hx
  inv_mem _ hx := hx
  inv_χ _ _ := rfl
  χ_inv _ _ := rfl
  differentiableOn_χ := differentiableOn_id
  differentiableOn_χInv := differentiableOn_id

/-- **The local conditions for coherence transfer from an open `N' ⊆ N` containing `N°`.** -/
theorem IsCoherentAt.of_le {N N' N₀ : (AnalyticSpace.complexAffineSpace.{u} n).Opens}
    (h : N' ≤ N) (h₀ : N₀ ≤ N) (h₀' : N₀ ≤ N') {W : FiniteEtaleOver (space N₀)}
    {x : Cn.{u} n} (hx : x ∈ N') (hc : IsCoherentAt h₀' W ⟨x, hx⟩) :
    IsCoherentAt h₀ W ⟨x, h hx⟩ :=
  (ChartBiholo.ofLE (N₀ := N₀) h).isCoherentAt (h₀ := h₀) (fun _ hy ↦ hy)
    (IsMapPullback.refl W) hc

namespace GraphConfig

variable {N N₀ : (AnalyticSpace.complexAffineSpace.{u} n).Opens} (c : GraphConfig N N₀)

/-! ### The regular pair cutting out the centre -/

variable (i₀ : Fin c.m)

lemma differentiableOn_centreEq (V : Set (Cn.{u} n)) (hV : ∀ x ∈ V, x ∈ N) :
    DifferentiableOn ℂ (fun x ↦ x c.iw - c.ψ i₀ x) V :=
  (differentiable_apply c.iw).differentiableOn.sub
    ((c.differentiableOn_ψ i₀).mono fun x hx ↦ mem_cyl_of_mem (hV x hx))

lemma not_eventually_centreEq {z : Cn.{u} n} (hzt : z c.it = 0) (hz : z c.iw - c.ψ i₀ z = 0) :
    ¬ ∀ᶠ x in 𝓝 z, x c.it = 0 → x c.iw - c.ψ i₀ x = 0 := by
  intro hev
  have ht : Tendsto (fun ε : ℂ ↦ Function.update z c.iw (z c.iw + ε)) (𝓝 0) (𝓝 z) := by
    have hc : Continuous fun ε : ℂ ↦ Function.update z c.iw (z c.iw + ε) :=
      continuous_const.update c.iw (continuous_const.add continuous_id)
    simpa using hc.tendsto 0
  have h₁ : ∀ᶠ ε in 𝓝 (0 : ℂ), ε = 0 := by
    filter_upwards [ht.eventually hev] with ε hε
    have := hε (by rw [c.update_it_iw, hzt])
    rwa [Function.update_self, c.ψ_update, add_sub_right_comm, hz, zero_add] at this
  obtain ⟨ε, h0, hne⟩ := ((h₁.filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin : {(0 : ℂ)}ᶜ ∈ 𝓝[≠] 0)).exists
  exact hne h0

/-- **The regular pair `(t, w - ψᵢ₀)`** on an open of `N`, whose zero set is the centre of the
blow-up. -/
def centrePair (V : (space N).Opens) : RegularPairFamily (img V : Set (Cn.{u} n)) :=
  RegularPairFamily.ofCoord (img V).isOpen c.it (c.differentiableOn_centreEq i₀ _ (img_le V))
    fun _ _ hzt hz ↦ c.not_eventually_centreEq i₀ hzt hz

lemma centre_subset_zeroSet (h₀ : N₀ ≤ N) (V : (space N).Opens) :
    (c.centre h₀ i₀).toBlowupData.centre ⊆ (c.centrePair i₀ V).zeroSet := by
  rw [centrePair, RegularPairFamily.ofCoord_zeroSet]
  exact fun _ hx ↦ hx

/-! ### Coherence near the centre from the charts -/

variable (h₀ : N₀ ≤ N) (W : FiniteEtaleOver (space N₀)) [T2Space W.left]
  {i₀} (hk : ∀ i j, i ≠ j → 1 ≤ c.k i j)
include hk

/-- **Coherence from the charts of the blow-up.** If all contact orders are positive and the
bounded sections on the first chart satisfy the local conditions for coherence (for every
Hausdorff finite étale cover), then `𝒜` satisfies them at every point. -/
theorem isCoherentAt_of_charts
    (h₁ : ∀ (W₁ : FiniteEtaleOver (space ((c.centre h₀ i₀).M₁₀ h₀))) [T2Space W₁.left]
      (x : space (c.centre h₀ i₀).M₁), IsCoherentAt ((c.centre h₀ i₀).M₁₀_le h₀) W₁ x)
    (h₂ : ∀ (W' : FiniteEtaleOver (space ((c.centre h₀ i₀).M₁₀ h₀))) [T2Space W'.left]
      (x : space (c.swapDom h₀ i₀)), IsCoherentAt (c.M₁₀_le_swapDom h₀) W' x)
    (x₀ : space N) : IsCoherentAt h₀ W x₀ := by
  set C := c.centre h₀ i₀
  have hβ₁ := isMapPullback_mapCover (C.chart₁Map h₀) W
  have hβ₂ := isMapPullback_mapCover (C.chart₂Map h₀) W
  have hcoh₁ := isCoherent_of_forall_isCoherentAt _ _ (h₁ (mapCover (C.chart₁Map h₀) W))
  have hcoh₂ : (boundedModule (C.M₂₀_le h₀) (mapCover (C.chart₂Map h₀) W)).IsCoherent := by
    refine isCoherent_of_forall_isCoherentAt _ _ fun a ↦ ?_
    by_cases hv : a.1 c.iw = 0
    · obtain ⟨U, k, e, haU, hfree⟩ := c.exists_isFreeSpanAt_chart₂ h₀ hk
        (W₂ := mapCover (C.chart₂Map h₀) W) a.2 hv
      exact isCoherentAt_of_isFreeSpanAt _ _ (hfree a (mem_img_iff.1 haU).2)
    · have hβ' := isMapPullback_mapCover (c.swapMap h₀ i₀) (mapCover (C.chart₂Map h₀) W)
      have hxD : swapChart c.it c.iw a.1 ∈ c.swapDom h₀ i₀ :=
        (c.swapBiholo h₀ i₀).inv_mem _ ⟨a.2, hv⟩
      have := (c.swapBiholo h₀ i₀).isCoherentAt (h₀ := C.M₂₀_le h₀) (fun _ hx ↦ hx) hβ'
        (h₂ (mapCover (c.swapMap h₀ i₀) (mapCover (C.chart₂Map h₀) W)) ⟨_, hxD⟩)
      convert this using 2
      exact Subtype.ext (swapChart_swapChart c.it_ne_iw hv).symm
  obtain ⟨V, m, s, hx₀V, hs⟩ := C.exists_isFreeSpanAt hβ₁ hβ₂ hcoh₁ hcoh₂
    (fun y hy ↦ by
      obtain ⟨U, k, e, hyU, hfree⟩ := c.exists_isFreeSpanAt_of_not_mem_centre h₀ hk W y.2 hy
      exact ⟨U, k, e, hfree y (mem_img_iff.1 hyU).2⟩) x₀
  exact isCoherentAt_of_criterion h₀ W c.hasThinComplement (c.centrePair i₀ V) s hx₀V
    (c.centre_subset_zeroSet i₀ h₀ V) hs

end GraphConfig

/-! ### The induction on the contact orders -/

namespace GraphConfig

/-- **Coherence along a graph configuration whose contact orders are bounded by `d`**, by
induction on `d`. -/
theorem isCoherentAt_of_lt (d : ℕ) : ∀ {N N₀ : (AnalyticSpace.complexAffineSpace.{u} n).Opens}
    (h₀ : N₀ ≤ N) (W : FiniteEtaleOver (space N₀)) [T2Space W.left] (c : GraphConfig N N₀),
    (∀ i j, i ≠ j → c.k i j < d) → ∀ x, IsCoherentAt h₀ W x := by
  induction d with
  | zero =>
    intro N N₀ h₀ W _ c hd x
    obtain ⟨U, k, e, hxU, hfree⟩ := c.exists_isFreeSpanAt_of_subsingleton h₀ W x.2
      fun i j _ _ ↦ by_contra fun hij ↦ Nat.not_lt_zero _ (hd i j hij)
    exact isCoherentAt_of_isFreeSpanAt _ _ (hfree x (mem_img_iff.1 hxU).2)
  | succ d ih =>
    intro N N₀ h₀ W _ c hd x
    by_cases hsub : ∀ i j, c.ψ i x.1 = x.1 c.iw → c.ψ j x.1 = x.1 c.iw → i = j
    · obtain ⟨U, k, e, hxU, hfree⟩ := c.exists_isFreeSpanAt_of_subsingleton h₀ W x.2 hsub
      exact isCoherentAt_of_isFreeSpanAt _ _ (hfree x (mem_img_iff.1 hxU).2)
    push Not at hsub
    obtain ⟨i₁, i₂, h₁, h₂, h₁₂⟩ := hsub
    have hcyl : x.1 ∈ cyl N c.iw := mem_cyl_of_mem x.2
    have ht : x.1 c.it = 0 := by
      by_contra ht
      exact c.ψ_ne_of_ne h₁₂ hcyl ht (h₁.trans h₂.symm)
    classical
    -- localize to the graphs through `x`
    set J := Finset.univ.filter fun i ↦ c.ψ i x.1 = x.1 c.iw
    set Jc := Finset.univ.filter fun i ↦ c.ψ i x.1 ≠ x.1 c.iw
    let N' : (AnalyticSpace.complexAffineSpace.{u} n).Opens :=
      ⟨{y | y ∈ N ∧ ∀ i ∈ Jc, y c.iw ≠ c.ψ i y} ∪ {y | y ∈ N₀}, by
        change IsOpen ({y : Cn.{u} n | y ∈ N ∧ ∀ i ∈ Jc, y c.iw ≠ c.ψ i y} ∪ {y | y ∈ N₀})
        exact (c.isOpen_off Jc).union (isOpen_setOf_mem N₀)⟩
    have hN' : N' ≤ N := fun y hy ↦ hy.elim (fun h ↦ h.1) fun h ↦ h₀ h
    have h₀' : N₀ ≤ N' := fun y hy ↦ Or.inr hy
    have hxN' : x.1 ∈ N' :=
      Or.inl ⟨x.2, fun i hi h ↦ (Finset.mem_filter.1 hi).2 h.symm⟩
    have hJ : ∀ y ∈ N', ∀ i ∉ J, y c.iw ≠ c.ψ i y := by
      rintro y (⟨-, hy⟩ | hy) i hi
      · exact hy i (Finset.mem_filter.2 ⟨Finset.mem_univ i, fun h ↦ hi
          (Finset.mem_filter.2 ⟨Finset.mem_univ i, h⟩)⟩)
      · exact ((c.mem_iff y (h₀ hy)).1 hy).2 i
    set c' := c.localize hN' J hJ
    have hk' : ∀ i j, i ≠ j → 1 ≤ c'.k i j := fun i j hij ↦ by
      have hi := (Finset.mem_filter.1 (J.equivFin.symm i).2).2
      have hj := (Finset.mem_filter.1 (J.equivFin.symm j).2).2
      refine (c.ψ_eq_iff (fun h ↦ hij (J.equivFin.symm.injective (Subtype.ext h))) hcyl ht).1
        (hi.trans hj.symm)
    have hpos : 0 < J.card :=
      Finset.card_pos.2 ⟨i₁, Finset.mem_filter.2 ⟨Finset.mem_univ _, h₁⟩⟩
    have hbound : ∀ i j, i ≠ j → (c'.chart₁Config h₀' (i₀ := ⟨0, hpos⟩) hk').k i j < d :=
      fun i j hij ↦ by
        have h₁ := hk' i j hij
        have h₂ := hd (J.equivFin.symm i) (J.equivFin.symm j)
          fun h ↦ hij (J.equivFin.symm.injective (Subtype.ext h))
        change c'.k i j - 1 < d
        change 1 ≤ c'.k i j at h₁
        change c'.k i j < d + 1 at h₂
        omega
    have := c'.isCoherentAt_of_charts h₀' W hk' (i₀ := ⟨0, hpos⟩)
      (fun W₁ _ y ↦ ih _ W₁ (c'.chart₁Config h₀' hk') hbound y)
      (fun W' _ y ↦ ih _ W' ((c'.chart₁Config h₀' hk').mono (c'.swapDom_le h₀')) hbound y)
      ⟨x.1, hxN'⟩
    exact IsCoherentAt.of_le hN' h₀ h₀' hxN' this

/-- **The bounded sections along a graph configuration are coherent.** -/
theorem isCoherent {N N₀ : (AnalyticSpace.complexAffineSpace.{u} n).Opens} (h₀ : N₀ ≤ N)
    (W : FiniteEtaleOver (space N₀)) [T2Space W.left] (c : GraphConfig N N₀) :
    (boundedModule h₀ W).IsCoherent :=
  isCoherent_of_forall_isCoherentAt h₀ W (isCoherentAt_of_lt
    ((Finset.univ.sup fun p : Fin c.m × Fin c.m ↦ c.k p.1 p.2) + 1) h₀ W c fun i j _ ↦
      Nat.lt_succ_of_le (Finset.le_sup (f := fun p : Fin c.m × Fin c.m ↦ c.k p.1 p.2)
        (Finset.mem_univ (i, j))))

end GraphConfig

end

end ComplexAnalytic.BoundedSections
