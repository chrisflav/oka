/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytic.LeviRegular
import Oka.Analytic.HartogsRegularFamily

/-!
# Levi's extension theorem across the zero set of a family of regular pairs

Let `U ⊆ ℂ^ι` be open, `P` a family of regular pairs on `U` with zero set `Z`, and `f` a function
on `U`. The *regular points* of `f` (`RegularPairFamily.regPts`) are the points off `Z` near which
`f` agrees off `Z` with a holomorphic function. A *local quotient representation* of `f` at `z`
(`RegularPairFamily.IsQuotRep`) is a pair of holomorphic functions `u`, `w` near `z`, with `w` not
vanishing on any open set, such that `f = u / w` at the regular points where `w ≠ 0`.

If the regular points are dense in `U` and `f` has local quotient representations at all points
of `U ∖ Z`, then it has local quotient representations at all points of `U`
(`RegularPairFamily.isQuotRep_of_forall`). This follows from Levi's theorem for one pair
(`hasDenominatorAt_of_isWeaklyRegular`), applied to the pairs one at a time to the regularisation
of `f` (`RegularPairFamily.regularize`), which replaces the values of `f` by the values of its
local holomorphic representatives wherever these exist.
-/

open Set Filter
open scoped Topology

variable {ι : Type*}

namespace RegularPairFamily

variable (Z : Set (ι → ℂ)) (f : (ι → ℂ) → ℂ)

/-- The **regular points** of `f`: the points off `Z` near which `f` agrees off `Z` with a
holomorphic function. -/
def regPts : Set (ι → ℂ) :=
  {y | y ∉ Z ∧ ∃ N ∈ 𝓝 y, ∃ F : (ι → ℂ) → ℂ, DifferentiableOn ℂ F N ∧
    ∀ y' ∈ N, y' ∉ Z → f y' = F y'}

/-- A **local quotient representation** of `f` at `z`: holomorphic `u`, `w` near `z`, with `w` not
vanishing on any open set, such that `f = u / w` at the regular points where `w ≠ 0`. -/
def IsQuotRep (z : ι → ℂ) : Prop :=
  ∃ N ∈ 𝓝 z, ∃ u w : (ι → ℂ) → ℂ, DifferentiableOn ℂ u N ∧ DifferentiableOn ℂ w N ∧
    interior (N ∩ w ⁻¹' {0}) = ∅ ∧ ∀ y ∈ N, y ∈ regPts Z f → w y ≠ 0 → f y = u y / w y

/-- `f` agrees near `y`, at the regular points, with a holomorphic function. -/
def HasRegRep (y : ι → ℂ) : Prop :=
  ∃ N ∈ 𝓝 y, ∃ F : (ι → ℂ) → ℂ, DifferentiableOn ℂ F N ∧ ∀ y' ∈ N, y' ∈ regPts Z f → f y' = F y'

open Classical in
/-- The **regularisation** of `f`: the value at `y` of a local holomorphic representative of `f`
at its regular points, if there is one, and `f y` otherwise. -/
noncomputable def regularize (y : ι → ℂ) : ℂ :=
  if h : HasRegRep Z f y then h.choose_spec.2.choose y else f y

variable {Z f}

/-- Two functions continuous at `y` which agree at the regular points near `y` agree at `y`, if
`y` is in the closure of the regular points. -/
lemma eq_of_eqOn_regPts {y : ι → ℂ} (hy : y ∈ closure (regPts Z f)) {N : Set (ι → ℂ)}
    (hN : N ∈ 𝓝 y) {F₁ F₂ : (ι → ℂ) → ℂ} (h₁ : ContinuousAt F₁ y) (h₂ : ContinuousAt F₂ y)
    (h : ∀ y' ∈ N, y' ∈ regPts Z f → F₁ y' = F₂ y') : F₁ y = F₂ y := by
  have hne : (𝓝[N ∩ regPts Z f] y).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot]
    rw [mem_closure_iff_nhds] at hy ⊢
    intro t ht
    obtain ⟨z, hz, hzr⟩ := hy (t ∩ N) (inter_mem ht hN)
    exact ⟨z, hz.1, hz.2, hzr⟩
  refine tendsto_nhds_unique (h₁.tendsto.mono_left (nhdsWithin_le_nhds (s := N ∩ regPts Z f))) ?_
  refine (h₂.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y' hy'
  exact (h y' hy'.1 hy'.2).symm

lemma regularize_eq {y : ι → ℂ} (hy : y ∈ closure (regPts Z f)) {N : Set (ι → ℂ)}
    (hN : N ∈ 𝓝 y) {F : (ι → ℂ) → ℂ} (hF : DifferentiableOn ℂ F N)
    (hfF : ∀ y' ∈ N, y' ∈ regPts Z f → f y' = F y') :
    regularize Z f y = F y := by
  have h : HasRegRep Z f y := ⟨N, hN, F, hF, hfF⟩
  rw [regularize, dif_pos h]
  have hN' := h.choose_spec.1
  obtain ⟨hF', hfF'⟩ := h.choose_spec.2.choose_spec
  refine eq_of_eqOn_regPts hy (inter_mem hN hN') (hF'.continuousOn.continuousAt hN')
    (hF.continuousOn.continuousAt hN) fun y' hy' hr ↦ ?_
  rw [← hfF' y' hy'.2 hr, hfF y' hy'.1 hr]


section Normed

variable [Fintype ι]

/-- A local quotient representation of `f` is one of its regularisation, in the sense of Levi's
theorem. -/
lemma IsQuotRep.isLocallyQuotientAt {z : ι → ℂ} (hdense : ∀ᶠ y in 𝓝 z, y ∈ closure (regPts Z f))
    (h : IsQuotRep Z f z) : IsLocallyQuotientAt (regularize Z f) z := by
  obtain ⟨N, hN, u, w, hu, hw, hw0, hf⟩ := h
  obtain ⟨N₀, hN₀N, hN₀o, hzN₀⟩ := mem_nhds_iff.1 (inter_mem hN hdense)
  refine ⟨N₀, hN₀o.mem_nhds hzN₀, u, w, hu.mono fun y hy ↦ (hN₀N hy).1,
    hw.mono fun y hy ↦ (hN₀N hy).1, subset_empty_iff.1 (hw0 ▸ interior_mono fun y hy ↦
      ⟨(hN₀N hy.1).1, hy.2⟩), fun y hy hwy ↦ ?_⟩
  have hO : IsOpen (N₀ ∩ {y | w y ≠ 0}) :=
    (hw.mono fun y hy ↦ (hN₀N hy).1).continuousOn.isOpen_inter_preimage hN₀o isOpen_ne
  have hu' : DifferentiableOn ℂ u (N₀ ∩ {y | w y ≠ 0}) := hu.mono fun y hy ↦ (hN₀N hy.1).1
  have hw' : DifferentiableOn ℂ w (N₀ ∩ {y | w y ≠ 0}) := hw.mono fun y hy ↦ (hN₀N hy.1).1
  refine regularize_eq (F := fun y ↦ u y / w y) (hN₀N hy).2 (hO.mem_nhds ⟨hy, hwy⟩)
    ((hu'.mul (hw'.inv fun y hy ↦ hy.2)).congr fun y _ ↦ div_eq_mul_inv _ _)
    fun y' hy' hr ↦ hf y' (hN₀N hy'.1).1 hr hy'.2

/-- A denominator of the regularisation of `f` at `z` in Levi's sense gives a local quotient
representation of `f` at `z`. -/
lemma isQuotRep_of_hasDenominatorAt {S : Set (ι → ℂ)} (hSZ : S ⊆ Z) {U : Set (ι → ℂ)}
    (hU : IsOpen U) (hdense : ∀ y ∈ U, y ∈ closure (regPts Z f)) {z : ι → ℂ} (hz : z ∈ U)
    (h : HasDenominatorAt S (regularize Z f) z) : IsQuotRep Z f z := by
  obtain ⟨W, hWo, hzW, c, F, hc, hF, hc0, hcF⟩ := h
  refine ⟨W ∩ U, inter_mem (hWo.mem_nhds hzW) (hU.mem_nhds hz), F, c, hF.mono inter_subset_left,
    hc.mono inter_subset_left, subset_empty_iff.1 (hc0 ▸ interior_mono fun y hy ↦
      ⟨hy.1.1, hy.2⟩), fun y hy hr hcy ↦ ?_⟩
  obtain ⟨hyZ, N, hN, G, hG, hfG⟩ := hr
  obtain ⟨N₀, hN₀N, hN₀o, hyN₀⟩ := mem_nhds_iff.1 (inter_mem hN (hU.mem_nhds hy.2))
  -- near `y`, the regularisation is `G`
  have hreg : ∀ y' ∈ N₀, regularize Z f y' = G y' := fun y' hy' ↦
    regularize_eq (hdense y' (hN₀N hy').2) (hN₀o.mem_nhds hy') (hG.mono fun _ h ↦ (hN₀N h).1)
      fun y'' hy'' hr ↦ hfG y'' (hN₀N hy'').1 hr.1
  have hcont : ContinuousAt (regularize Z f) y := by
    refine (hG.continuousOn.continuousAt hN).congr ?_
    filter_upwards [hN₀o.mem_nhds hyN₀] with y' hy'
    exact (hreg y' hy').symm
  have := hcF y hy.1 (fun h ↦ hyZ (hSZ h)) hcont
  rw [hreg y hyN₀, ← hfG y (mem_of_mem_nhds hN) hyZ] at this
  rw [this, mul_div_cancel_left₀ _ hcy]

end Normed

variable [Finite ι] {U : Set (ι → ℂ)} (P : RegularPairFamily U)

/-- **Levi's extension theorem across the zero set of a family of regular pairs**: if the regular
points of `f` are dense in `U` and `f` has local quotient representations at the points of `U`
off the zero set of `P`, then it has local quotient representations at all points of `U`. -/
theorem isQuotRep_of_forall (hU : IsOpen U) (hdense : ∀ y ∈ U, y ∈ closure (regPts P.zeroSet f))
    (hq : ∀ y ∈ U, y ∉ P.zeroSet → IsQuotRep P.zeroSet f y) :
    ∀ z ∈ U, IsQuotRep P.zeroSet f z := by
  classical
  have := Fintype.ofFinite ι
  suffices H : ∀ s : Finset (Fin P.k), ∀ y ∈ U, (∀ i ∉ s, y ∉ P.zeroSetOf i) →
      IsQuotRep P.zeroSet f y from
    fun z hz ↦ H Finset.univ z hz fun i hi ↦ absurd (Finset.mem_univ i) hi
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro y hy h
    exact hq y hy fun hZ ↦ by
      obtain ⟨i, hi⟩ := mem_iUnion.1 hZ
      exact h i (Finset.notMem_empty i) hi
  | insert i s his ih =>
    intro y hy h
    set U' := U \ ⋃ j ∈ Finset.univ \ insert i s, P.zeroSetOf j
    have hU' : IsOpen U' := P.isOpen_diff_biUnion hU subset_rfl _
    have hyU' : y ∈ U' := ⟨hy, fun hj ↦ by
      obtain ⟨j, hj, hyj⟩ := mem_iUnion₂.1 hj
      exact h j (Finset.mem_sdiff.1 hj).2 hyj⟩
    have hden := hasDenominatorAt_of_isWeaklyRegular hU' hyU' (P.isWeaklyRegular i y hy)
      (f := regularize P.zeroSet f) fun z hz hzi ↦ by
        refine IsQuotRep.isLocallyQuotientAt ?_ (ih z hz.1 fun j hj ↦ ?_)
        · filter_upwards [hU.mem_nhds hz.1] with y' hy' using hdense y' hy'
        · by_cases hji : j = i
          · subst hji
            exact hzi
          · exact fun hzj ↦ hz.2 (mem_iUnion₂.2 ⟨j, Finset.mem_sdiff.2 ⟨Finset.mem_univ j,
              fun h ↦ (Finset.mem_insert.1 h).elim hji hj⟩, hzj⟩)
    exact isQuotRep_of_hasDenominatorAt (fun x hx ↦ mem_iUnion.2 ⟨i, hx⟩) hU hdense hy hden

open Classical in
/-- **The complement of the zero set of a family of regular pairs in a connected open set is
connected**: the indicator function of a clopen part extends holomorphically across the zero set,
and the extension takes only the values `0` and `1`. -/
theorem isPreconnected_sdiff_zeroSet {V : Set (ι → ℂ)} (hV : IsOpen V) (hVU : V ⊆ U)
    (hVc : IsPreconnected V) : IsPreconnected (V \ P.zeroSet) := by
  have := Fintype.ofFinite ι
  have hs : IsOpen (V \ P.zeroSet) := P.isOpen_diff_zeroSet hV hVU
  intro u v hu hv hsuv ⟨a, has, hau⟩ ⟨b, hbs, hbv⟩
  by_contra hne
  rw [not_nonempty_iff_eq_empty] at hne
  have hsep : ∀ y ∈ V \ P.zeroSet, y ∈ v → y ∉ u := fun y hy hyv hyu ↦
    (eq_empty_iff_forall_notMem.1 hne) y ⟨hy, hyu, hyv⟩
  set f : (ι → ℂ) → ℂ := fun y ↦ if y ∈ u then 1 else 0
  have hf : DifferentiableOn ℂ f (V \ P.zeroSet) := by
    intro y hy
    refine DifferentiableAt.differentiableWithinAt ?_
    by_cases hyu : y ∈ u
    · refine (differentiableAt_const (1 : ℂ)).congr_of_eventuallyEq ?_
      filter_upwards [hu.mem_nhds hyu] with y' hy'
      simp [f, hy']
    · have hyv : y ∈ v := (hsuv hy).resolve_left hyu
      refine (differentiableAt_const (0 : ℂ)).congr_of_eventuallyEq ?_
      filter_upwards [(hs.inter hv).mem_nhds ⟨hy, hyv⟩] with y' hy'
      simp [f, hsep y' hy'.1 hy'.2]
  obtain ⟨F, hF, hFf⟩ := P.exists_differentiableOn_eqOn hV hVU hf
  have h01 : EqOn (fun y ↦ F y * (F y - 1)) (fun _ ↦ 0) V := by
    refine P.eqOn_of_eqOn_diff hV hVU (hF.continuousOn.mul (hF.continuousOn.sub
      continuousOn_const)) continuousOn_const fun y hy ↦ ?_
    rw [hFf hy]
    by_cases hyu : y ∈ u <;> simp [f, hyu]
  have hc := hF.continuousOn
  have hopen : ∀ c : ℂ, IsOpen (V ∩ F ⁻¹' Metric.ball c (1 / 2)) := fun c ↦
    hc.isOpen_inter_preimage hV Metric.isOpen_ball
  obtain ⟨y, hyV, hy0, hy1⟩ := hVc _ _ (hopen 0) (hopen 1) (fun y hy ↦ by
      have := h01 hy
      simp only [mul_eq_zero, sub_eq_zero] at this
      rcases this with h | h
      · exact Or.inl ⟨hy, by simp [h]⟩
      · exact Or.inr ⟨hy, by simp [h]⟩)
    ⟨b, hbs.1, hbs.1, by
      have : F b = 0 := by rw [hFf hbs]; simp [f, hsep b hbs hbv]
      simp [this]⟩
    ⟨a, has.1, has.1, by
      have : F a = 1 := by rw [hFf has]; simp [f, hau]
      simp [this]⟩
  have h1 := hy0.2
  have h2 := hy1.2
  simp only [mem_preimage, Metric.mem_ball, dist_eq_norm, sub_zero] at h1 h2
  have : ‖(1 : ℂ)‖ < 1 := calc
    ‖(1 : ℂ)‖ = ‖F y - (F y - 1)‖ := by ring_nf
    _ ≤ ‖F y‖ + ‖F y - 1‖ := norm_sub_le _ _
    _ < 1 / 2 + 1 / 2 := add_lt_add h1 h2
    _ = 1 := by norm_num
  simp at this

end RegularPairFamily
