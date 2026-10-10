/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Heights.WeierstrassFiniteAnalytic
import Oka.Uniformization.OncePunctured

/-!
# Uniformisations of once-punctured elliptic curves are coverings, and are unique

`Uniformization.IsUniformization W A B π` bundles the conclusions of
`Uniformization.uniformization_oncePunctured` about `π` (holomorphic immersion on `ℍ`, onto the
affine points `V W` of `W`, fibres the orbits of `⟨A, B⟩`).

* `IsUniformization.isCoveringMap`: `π : ℍ → V W` is a covering map. It is a local
  homeomorphism onto the curve (near a point where `∂π₁ ≠ 0`, the curve is a graph over the
  `x`-coordinate and the local inverse of `π₁` gives a section; symmetrically for `y`), and local
  sections through one point of a fibre are moved to every other point by the group.
* `IsUniformization.unique`: two uniformisations of the same curve differ by `g ∈ SL(2, ℝ)`:
  `π' = π ∘ g` on `ℍ` and `±⟨A', B'⟩ = g⁻¹ (±⟨A, B⟩) g`. The lift of `π'` through `π` is a
  biholomorphism of `ℍ`, hence Möbius (`exists_SL2R_eq_of_holomorphic`).
-/

open Complex Metric Set Filter Topology
open UpperHalfPlane hiding I I_re I_im
open scoped MatrixGroups

namespace Uniformization

/-- The affine points of a Weierstrass curve over `ℂ`. -/
def V (W : WeierstrassCurve ℂ) : Set (ℂ × ℂ) := {p | W.toAffine.Equation p.1 p.2}

/-- `(A, B, π)` **uniformises** `W ∖ O`: `π` is a holomorphic immersion on `ℍ` onto the affine
points of `W` whose fibres are the orbits of `⟨A, B⟩`. -/
structure IsUniformization (W : WeierstrassCurve ℂ) (A B : SL(2, ℝ)) (π : ℂ → ℂ × ℂ) : Prop where
  holo : ∀ z : ℍ, DifferentiableAt ℂ π z ∧ deriv π z ≠ 0
  mem : ∀ z : ℍ, W.toAffine.Equation (π z).1 (π z).2
  surj : ∀ x y : ℂ, W.toAffine.Equation x y → ∃ z : ℍ, π z = (x, y)
  fibre : ∀ z w : ℍ, π z = π w ↔ ∃ γ ∈ Subgroup.closure {A, B}, γ • z = w

/-- **U1** in the bundled form. -/
theorem exists_isUniformization (W : WeierstrassCurve ℂ) [W.IsElliptic] :
    ∃ (A B : SL(2, ℝ)) (π : ℂ → ℂ × ℂ),
      Matrix.trace ((A * B * A⁻¹ * B⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) = -2 ∧
      Matrix.trace (A : Matrix (Fin 2) (Fin 2) ℝ) ≠ 0 ∧ IsUniformization W A B π := by
  obtain ⟨A, B, π, h1, h2, h3, h4, h5, h6⟩ := uniformization_oncePunctured W
  exact ⟨A, B, π, h1, h2, ⟨h3, h4, h5, h6⟩⟩

namespace IsUniformization

variable {W : WeierstrassCurve ℂ} {A B : SL(2, ℝ)} {π : ℂ → ℂ × ℂ}

/-- The map `ℍ → V W`. -/
def toV (h : IsUniformization W A B π) (z : ℍ) : V W := ⟨π z, h.mem z⟩

theorem hasDerivAt (h : IsUniformization W A B π) (z : ℍ) :
    HasDerivAt π (deriv π z) z := (h.holo z).1.hasDerivAt

theorem hasDerivAt_fst (h : IsUniformization W A B π) (z : ℍ) :
    HasDerivAt (fun w ↦ (π w).1) (deriv π z).1 z :=
  (ContinuousLinearMap.fst ℂ ℂ ℂ).hasFDerivAt.comp_hasDerivAt _ (h.hasDerivAt z)

theorem hasDerivAt_snd (h : IsUniformization W A B π) (z : ℍ) :
    HasDerivAt (fun w ↦ (π w).2) (deriv π z).2 z :=
  (ContinuousLinearMap.snd ℂ ℂ ℂ).hasFDerivAt.comp_hasDerivAt _ (h.hasDerivAt z)

theorem differentiableOn (h : IsUniformization W A B π) :
    DifferentiableOn ℂ π {z | 0 < z.im} := fun z hz ↦
  (h.holo ⟨z, hz⟩).1.differentiableWithinAt

theorem continuous_toV (h : IsUniformization W A B π) : Continuous h.toV :=
  (h.differentiableOn.continuousOn.comp_continuous continuous_coe
    fun z ↦ z.im_pos).subtype_mk _

theorem hasStrictDerivAt_fst (h : IsUniformization W A B π) (z : ℍ) :
    HasStrictDerivAt (fun w ↦ (π w).1) (deriv π z).1 z := by
  have han : AnalyticAt ℂ (fun w ↦ (π w).1) z :=
    ((ContinuousLinearMap.fst ℂ ℂ ℂ).differentiable.comp_differentiableOn
      h.differentiableOn).analyticAt (isOpen_upper.mem_nhds z.im_pos)
  rw [← (h.hasDerivAt_fst z).deriv]; exact han.hasStrictDerivAt

theorem hasStrictDerivAt_snd (h : IsUniformization W A B π) (z : ℍ) :
    HasStrictDerivAt (fun w ↦ (π w).2) (deriv π z).2 z := by
  have han : AnalyticAt ℂ (fun w ↦ (π w).2) z :=
    ((ContinuousLinearMap.snd ℂ ℂ ℂ).differentiable.comp_differentiableOn
      h.differentiableOn).analyticAt (isOpen_upper.mem_nhds z.im_pos)
  rw [← (h.hasDerivAt_snd z).deriv]; exact han.hasStrictDerivAt

/-- Differentiating the equation along `π`: `F_x ⬝ π₁′ + F_y ⬝ π₂′ = 0`. -/
theorem equation_deriv (h : IsUniformization W A B π) (z : ℍ) :
    Heights.complexWeierstrassEquationX W (π z) * (deriv π z).1 +
      Heights.complexWeierstrassEquationY W (π z) * (deriv π z).2 = 0 := by
  have hF : ∀ᶠ w in 𝓝 (z : ℂ), Heights.complexWeierstrassEquation W (π w) = 0 := by
    filter_upwards [isOpen_upper.mem_nhds z.im_pos] with w hw
    exact (Heights.complexWeierstrassEquation_eq_zero_iff W _).mpr (h.mem ⟨w, hw⟩)
  have hd := ((Heights.hasFDerivAt_complexWeierstrassEquation W (π z)).comp_hasDerivAt _
    (h.hasDerivAt z))
  have hzero : HasDerivAt (fun w ↦ Heights.complexWeierstrassEquation W (π w)) 0 z :=
    (hasDerivAt_const (z : ℂ) (0 : ℂ)).congr_of_eventuallyEq hF
  have := hd.unique hzero
  simp only [add_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul] at this
  linear_combination this

theorem nonsingular [W.IsElliptic] (h : IsUniformization W A B π) (z : ℍ) :
    Heights.complexWeierstrassEquationX W (π z) ≠ 0 ∨
      Heights.complexWeierstrassEquationY W (π z) ≠ 0 :=
  ((WeierstrassCurve.Affine.nonsingular_iff' _ _).mp
    (WeierstrassCurve.Affine.equation_iff_nonsingular.mp (h.mem z))).2

/-- **Local sections from a graph chart.** If near `π z` the curve is the graph of `G` over the
coordinate `pr` and `pr ∘ π` has nonzero derivative at `z`, then `π` has a continuous section over
an open preconnected neighbourhood of `π z` in `V W` through `z`. -/
theorem exists_section_of_graph (h : IsUniformization W A B π) (z : ℍ) {pr pr' : ℂ × ℂ → ℂ}
    (hpr : Continuous pr)
    (hdet : ∀ q q' : ℂ × ℂ, pr q = pr q' → pr' q = pr' q' → q = q') {G : ℂ → ℂ}
    (hgraph : ∀ᶠ q in 𝓝 (π z), (W.toAffine.Equation q.1 q.2 ↔ G (pr q) = pr' q)) {d : ℂ}
    (hd : HasStrictDerivAt (fun w ↦ pr (π w)) d z) (hd0 : d ≠ 0) :
    ∃ N : Set (V W), IsOpen N ∧ h.toV z ∈ N ∧ IsPreconnected N ∧
      ∃ s : V W → ℍ, ContinuousOn s N ∧ (∀ q ∈ N, h.toV (s q) = q) ∧ s (h.toV z) = z := by
  obtain ⟨ε₁, hε₁, σ, hσc, hσ, hσz⟩ := exists_localSection hd hd0
  set a₀ := pr (π z)
  obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhds_iff.mp hgraph
  have hσa₀ : ContinuousAt σ a₀ := hσc.continuousAt (ball_mem_nhds _ hε₁)
  have hπz : ContinuousAt π z := (h.holo z).1.continuousAt
  have h1 : ∀ᶠ a in 𝓝 a₀, 0 < (σ a).im := hσa₀.eventually (by
    rw [hσz]; exact isOpen_upper.mem_nhds z.im_pos)
  have h2 : ∀ᶠ a in 𝓝 a₀, π (σ a) ∈ ball (π z) δ := by
    have : ContinuousAt (fun a ↦ π (σ a)) a₀ := by
      refine ContinuousAt.comp (f := σ) (g := π) ?_ hσa₀
      rw [hσz]; exact hπz
    have e : (fun a ↦ π (σ a)) a₀ = π z := by simp only [hσz]
    exact this.eventually (by rw [e]; exact ball_mem_nhds _ hδ)
  obtain ⟨ε₂, hε₂, hε₂s⟩ := Metric.eventually_nhds_iff_ball.mp (h1.and h2)
  set ε := min ε₁ ε₂
  have hε : 0 < ε := lt_min hε₁ hε₂
  have hb₁ : ball a₀ ε ⊆ ball a₀ ε₁ := ball_subset_ball (min_le_left _ _)
  have hb₂ : ∀ a ∈ ball a₀ ε, 0 < (σ a).im ∧ π (σ a) ∈ ball (π z) δ := fun a ha ↦
    hε₂s a (ball_subset_ball (min_le_right _ _) ha)
  classical
  set s : V W → ℍ := fun q ↦ if hq : 0 < (σ (pr q.1)).im then ⟨σ (pr q.1), hq⟩ else z
  set N : Set (V W) := {q | pr q.1 ∈ ball a₀ ε ∧ q.1 ∈ ball (π z) δ}
  have hNo : IsOpen N :=
    ((isOpen_ball.preimage (hpr.comp continuous_subtype_val))).inter
      (isOpen_ball.preimage continuous_subtype_val)
  have hs_val : ∀ q ∈ N, (s q : ℂ) = σ (pr q.1) := fun q hq ↦ by
    simp [s, (hb₂ _ hq.1).1]
  have hsec : ∀ q ∈ N, h.toV (s q) = q := by
    intro q hq
    apply Subtype.ext
    change π (s q) = q.1
    rw [hs_val q hq]
    set a := pr q.1
    have hπσ : pr (π (σ a)) = a := hσ a (hb₁ hq.1)
    have hq1 : G (pr q.1) = pr' q.1 := (hδU hq.2).mp q.2
    obtain ⟨hpos, hball⟩ := hb₂ a hq.1
    have hq2 : G (pr (π (σ a))) = pr' (π (σ a)) := (hδU hball).mp (h.mem ⟨σ a, hpos⟩)
    exact hdet _ _ hπσ (by rw [← hq2, ← hq1, hπσ])
  have hz : h.toV z ∈ N := ⟨mem_ball_self hε, mem_ball_self hδ⟩
  refine ⟨N, hNo, hz, ?_, s, ?_, hsec, ?_⟩
  · -- `N` is the image of a ball
    set φ : ℂ → V W := fun a ↦ if hq : 0 < (σ a).im then h.toV ⟨σ a, hq⟩ else h.toV z
    have hφ : ∀ a ∈ ball a₀ ε, (φ a).1 = π (σ a) := fun a ha ↦ by
      simp [φ, (hb₂ a ha).1, toV]
    have hN : N = φ '' ball a₀ ε := by
      ext q
      constructor
      · intro hq
        refine ⟨pr q.1, hq.1, ?_⟩
        apply Subtype.ext
        rw [hφ _ hq.1, ← hs_val q hq]
        exact congrArg Subtype.val (hsec q hq)
      · rintro ⟨a, ha, rfl⟩
        refine ⟨?_, ?_⟩
        · rw [hφ a ha, hσ a (hb₁ ha)]; exact ha
        · rw [hφ a ha]; exact (hb₂ a ha).2
    rw [hN]
    refine (convex_ball a₀ ε).isPreconnected.image φ ?_
    rw [continuousOn_iff_continuous_restrict]
    refine continuous_induced_rng.mpr ?_
    have : (fun a : ball a₀ ε ↦ ((ball a₀ ε).restrict φ a).1) = fun a ↦ π (σ a.1) := by
      funext a; exact hφ a a.2
    rw [Function.comp_def, this]
    refine ContinuousOn.comp_continuous (s := {w : ℂ | 0 < w.im}) h.differentiableOn.continuousOn
      ((hσc.mono hb₁).comp_continuous continuous_subtype_val fun a ↦ a.2) fun a ↦ (hb₂ a a.2).1
  · rw [continuousOn_iff_continuous_restrict]
    refine isOpenEmbedding_coe.isInducing.continuous_iff.mpr ?_
    have : (fun q : N ↦ ((N.restrict s q : ℍ) : ℂ)) = fun q : N ↦ σ (pr q.1.1) := by
      funext q; exact hs_val q q.2
    rw [Function.comp_def]; simp only [restrict_apply] at this ⊢
    rw [this]
    exact (hσc.mono hb₁).comp_continuous ((hpr.comp continuous_subtype_val).comp
      continuous_subtype_val) fun q ↦ q.2.1
  · apply UpperHalfPlane.ext
    rw [show ((s (h.toV z) : ℍ) : ℂ) = σ (pr (π z)) from hs_val _ hz, hσz]

theorem deriv_fst_or_snd (h : IsUniformization W A B π) (z : ℍ) :
    (deriv π z).1 ≠ 0 ∨ (deriv π z).2 ≠ 0 := by
  by_contra hc
  push Not at hc
  exact (h.holo z).2 (Prod.ext hc.1 hc.2)

/-- `π` has local sections through every point. -/
theorem exists_section [W.IsElliptic] (h : IsUniformization W A B π) (z : ℍ) :
    ∃ N : Set (V W), IsOpen N ∧ h.toV z ∈ N ∧ IsPreconnected N ∧
      ∃ s : V W → ℍ, ContinuousOn s N ∧ (∀ q ∈ N, h.toV (s q) = q) ∧ s (h.toV z) = z := by
  have hF0 : Heights.complexWeierstrassEquation W (π z) = 0 :=
    (Heights.complexWeierstrassEquation_eq_zero_iff W _).mpr (h.mem z)
  have hEq := h.equation_deriv z
  rcases h.deriv_fst_or_snd z with h1 | h2
  · have hy : Heights.complexWeierstrassEquationY W (π z) ≠ 0 := by
      intro hy
      rw [hy, zero_mul, add_zero] at hEq
      rcases h.nonsingular z with hx | hy'
      · exact hx ((mul_eq_zero.mp hEq).resolve_right h1)
      · exact hy' hy
    refine h.exists_section_of_graph z continuous_fst (pr' := Prod.snd)
      (G := Heights.complexWeierstrassImplicitY W (π z) hy)
      (fun q q' e1 e2 ↦ Prod.ext e1 e2) ?_ (h.hasStrictDerivAt_fst z) h1
    filter_upwards [Heights.eventually_complexWeierstrassEquation_iff_implicitY W (π z) hy]
      with q hq
    rw [← Heights.complexWeierstrassEquation_eq_zero_iff, ← hF0]; exact hq
  · have hx : Heights.complexWeierstrassEquationX W (π z) ≠ 0 := by
      intro hx
      rw [hx, zero_mul, zero_add] at hEq
      rcases h.nonsingular z with hx' | hy
      · exact hx' hx
      · exact hy ((mul_eq_zero.mp hEq).resolve_right h2)
    refine h.exists_section_of_graph z continuous_snd (pr' := Prod.fst)
      (G := Heights.complexWeierstrassImplicitX W (π z) hx)
      (fun q q' e1 e2 ↦ Prod.ext e2 e1) ?_ (h.hasStrictDerivAt_snd z) h2
    filter_upwards [Heights.eventually_complexWeierstrassEquation_iff_implicitX W (π z) hx]
      with q hq
    rw [← Heights.complexWeierstrassEquation_eq_zero_iff, ← hF0]; exact hq

/-- `π` is injective near every point. -/
theorem exists_nhds_injOn (h : IsUniformization W A B π) (z : ℍ) :
    ∃ U ∈ 𝓝 z, InjOn h.toV U := by
  have key : ∀ {f : ℂ → ℂ} {d : ℂ}, HasStrictDerivAt f d z → d ≠ 0 →
      ∃ U ∈ 𝓝 z, ∀ x ∈ U, ∀ y ∈ U, f (x : ℂ) = f y → x = y := by
    intro f d hf hd
    have hev := hf.eventually_left_inverse hd
    have hev' : ∀ᶠ x : ℍ in 𝓝 z, hf.localInverse f d z hd (f x) = x :=
      continuous_coe.continuousAt.eventually hev
    refine ⟨_, hev', fun x hx y hy hxy ↦ UpperHalfPlane.ext ?_⟩
    have := congrArg (hf.localInverse f d z hd) hxy
    simp only [mem_setOf_eq] at hx hy
    rw [hx, hy] at this; exact this
  rcases h.deriv_fst_or_snd z with h1 | h2
  · obtain ⟨U, hU, hinj⟩ := key (h.hasStrictDerivAt_fst z) h1
    exact ⟨U, hU, fun x hx y hy hxy ↦ hinj x hx y hy (congrArg (fun q : V W ↦ q.1.1) hxy)⟩
  · obtain ⟨U, hU, hinj⟩ := key (h.hasStrictDerivAt_snd z) h2
    exact ⟨U, hU, fun x hx y hy hxy ↦ hinj x hx y hy (congrArg (fun q : V W ↦ q.1.2) hxy)⟩

theorem toV_smul (h : IsUniformization W A B π) {γ : SL(2, ℝ)}
    (hγ : γ ∈ Subgroup.closure {A, B}) (z : ℍ) : h.toV (γ • z) = h.toV z :=
  Subtype.ext ((h.fibre z (γ • z)).mpr ⟨γ, hγ, rfl⟩).symm

/-- **The uniformisation is a covering map** `ℍ → V W`. -/
theorem isCoveringMap [W.IsElliptic] (h : IsUniformization W A B π) : IsCoveringMap h.toV := by
  rw [isCoveringMap_iff_isCoveringMapOn_univ]
  refine isCoveringMapOn_of_sections (by simp) h.continuous_toV.continuousOn
    (fun e _ ↦ h.exists_nhds_injOn e) fun x _ ↦ ?_
  obtain ⟨z, hz⟩ := h.surj x.1.1 x.1.2 x.2
  have hxz : h.toV z = x := Subtype.ext hz
  obtain ⟨N, hNo, hzN, hNc, s₀, hs₀c, hs₀, -⟩ := h.exists_section z
  refine ⟨N, hNo, hxz ▸ hzN, subset_univ _, hNc, fun e he ↦ ?_⟩
  obtain ⟨γ, hγ, hγe⟩ := (h.fibre (s₀ (h.toV e)) e).mp
    (congrArg Subtype.val (hs₀ _ he))
  refine ⟨fun q ↦ γ • s₀ q, (continuous_const_smul γ).comp_continuousOn hs₀c,
    fun q hq ↦ by rw [h.toV_smul hγ, hs₀ q hq], hγe⟩

/-- A continuous lift `T : ℍ → ℍ` of a uniformisation `π'` through `π` is holomorphic. -/
theorem holomorphicH_of_lift (h : IsUniformization W A B π) {A' B' : SL(2, ℝ)}
    {π' : ℂ → ℂ × ℂ} (h' : IsUniformization W A' B' π') {T : ℍ → ℍ} (hT : Continuous T)
    (hTπ : ∀ τ, π (T τ) = π' τ) : HolomorphicH T := by
  intro w hw
  set τ : ℍ := ⟨w, hw⟩
  have hofc : ContinuousAt (fun v ↦ ((T (ofComplex v) : ℍ) : ℂ)) w := by
    refine (continuous_coe.comp hT).continuousAt.comp ?_
    exact ofComplex.continuousOn.continuousAt (ofComplex.open_source.mem_nhds (by
      change w ∈ (isOpenEmbedding_coe.toOpenPartialHomeomorph _).target
      simp only [IsOpenEmbedding.toOpenPartialHomeomorph_target]
      exact ⟨τ, rfl⟩))
  have hofw : (ofComplex w : ℍ) = τ := ofComplex_apply_of_im_pos hw
  have hev : ∀ᶠ v in 𝓝 w, π (T (ofComplex v)) = π' v := by
    filter_upwards [isOpen_upper.mem_nhds hw] with v hv
    rw [hTπ, ofComplex_of_im_pos hv]
  rcases h.deriv_fst_or_snd (T τ) with h1 | h2
  · refine (differentiableAt_of_comp_eq (f := fun v ↦ (π v).1) (g := fun v ↦ (π' v).1)
      (by rw [hofw]; exact h.hasStrictDerivAt_fst (T τ)) h1 hofc
      (hev.mono fun v hv ↦ by simp only [hv]) ?_).differentiableWithinAt
    exact ((ContinuousLinearMap.fst ℂ ℂ ℂ).differentiable.differentiableAt).comp w
      (h'.holo τ).1
  · refine (differentiableAt_of_comp_eq (f := fun v ↦ (π v).2) (g := fun v ↦ (π' v).2)
      (by rw [hofw]; exact h.hasStrictDerivAt_snd (T τ)) h2 hofc
      (hev.mono fun v hv ↦ by simp only [hv]) ?_).differentiableWithinAt
    exact ((ContinuousLinearMap.snd ℂ ℂ ℂ).differentiable.differentiableAt).comp w
      (h'.holo τ).1

/-- The group generated by `A`, `B` and `-1`. -/
def pmGroup (A B : SL(2, ℝ)) : Subgroup SL(2, ℝ) := Subgroup.closure {A, B, -1}

theorem closure_le_pmGroup (A B : SL(2, ℝ)) : Subgroup.closure {A, B} ≤ pmGroup A B :=
  Subgroup.closure_mono (by
    intro x hx; simp only [mem_insert_iff, mem_singleton_iff] at hx ⊢; tauto)

theorem neg_one_mem_pmGroup (A B : SL(2, ℝ)) : (-1 : SL(2, ℝ)) ∈ pmGroup A B :=
  Subgroup.subset_closure (by simp)

/-- Deck transformations of `π` (with respect to any base point) lie in `±⟨A, B⟩`. -/
theorem mem_pmGroup_of_deck [W.IsElliptic] (h : IsUniformization W A B π) {D : SL(2, ℝ)}
    (hD : ∀ w : ℍ, h.toV (D • w) = h.toV w) : D ∈ pmGroup A B := by
  obtain ⟨γ, hγ, hγD⟩ := (h.fibre UpperHalfPlane.I (D • UpperHalfPlane.I)).mp
    (congrArg Subtype.val (hD _).symm)
  have heq := h.isCoveringMap.eq_of_comp_eq (A := ℍ) (g₁ := fun w ↦ D • w) (g₂ := fun w ↦ γ • w)
    (continuous_const_smul D) (continuous_const_smul γ)
    (by funext w; simp only [Function.comp_apply, hD, h.toV_smul hγ]) UpperHalfPlane.I hγD.symm
  have htriv : ∀ w : ℍ, (γ⁻¹ * D) • w = w := fun w ↦ by
    rw [mul_smul, show D • w = γ • w from congrFun heq w, inv_smul_smul]
  rcases Unif.eq_one_or_neg_one_of_forall htriv with h1 | h1
  · rw [show D = γ * (γ⁻¹ * D) by group, h1, mul_one]
    exact closure_le_pmGroup A B hγ
  · rw [show D = γ * (γ⁻¹ * D) by group, h1]
    exact mul_mem (closure_le_pmGroup A B hγ) (neg_one_mem_pmGroup A B)

theorem toV_smul_pm (h : IsUniformization W A B π) {γ : SL(2, ℝ)} (hγ : γ ∈ pmGroup A B)
    (z : ℍ) : h.toV (γ • z) = h.toV z := by
  induction hγ using Subgroup.closure_induction generalizing z with
  | mem g hg =>
    simp only [mem_insert_iff, mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · exact h.toV_smul (Subgroup.subset_closure (by simp)) z
    · exact h.toV_smul (Subgroup.subset_closure (by simp)) z
    · rw [Generators.neg_one_smul']
  | one => rw [one_smul]
  | mul g₁ g₂ _ _ ih₁ ih₂ => rw [mul_smul, ih₁, ih₂]
  | inv g _ ih => rw [← ih (g⁻¹ • z), smul_inv_smul]

/-- **Uniqueness of the uniformisation.** Two uniformisations of the same curve differ by an
element `g ∈ SL(2, ℝ)`: `π' = π ∘ g` on `ℍ`, and `±⟨A', B'⟩ = g⁻¹ ±⟨A, B⟩ g`. -/
theorem unique [W.IsElliptic] (h : IsUniformization W A B π) {A' B' : SL(2, ℝ)}
    {π' : ℂ → ℂ × ℂ} (h' : IsUniformization W A' B' π') :
    ∃ g : SL(2, ℝ), (∀ z : ℍ, π' z = π ((g • z : ℍ) : ℂ)) ∧
      ∀ γ : SL(2, ℝ), γ ∈ pmGroup A' B' ↔ g * γ * g⁻¹ ∈ pmGroup A B := by
  have hcov := h.isCoveringMap
  have hcov' := h'.isCoveringMap
  set x₀ := h'.toV UpperHalfPlane.I
  obtain ⟨z₀, hz₀⟩ := h.surj x₀.1.1 x₀.1.2 x₀.2
  have hz₀' : h.toV z₀ = x₀ := Subtype.ext hz₀
  obtain ⟨T, ⟨hT0, hT⟩, -⟩ := hcov.existsUnique_continuousMap_lifts
    ⟨h'.toV, h'.continuous_toV⟩ UpperHalfPlane.I z₀ hz₀'
  obtain ⟨S, ⟨hS0, hS⟩, -⟩ := hcov'.existsUnique_continuousMap_lifts
    ⟨h.toV, h.continuous_toV⟩ z₀ UpperHalfPlane.I hz₀'.symm
  have hT' : ∀ w, h.toV (T w) = h'.toV w := fun w ↦ congrFun hT w
  have hS' : ∀ w, h'.toV (S w) = h.toV w := fun w ↦ congrFun hS w
  have hTS : ∀ w, T (S w) = w := fun w ↦ congrFun (hcov.eq_of_comp_eq (A := ℍ)
    (g₁ := fun w ↦ T (S w)) (g₂ := id) (T.continuous.comp S.continuous) continuous_id
    (by funext w; simp [hT', hS']) z₀ (by simp [hS0, hT0])) w
  have hST : ∀ w, S (T w) = w := fun w ↦ congrFun (hcov'.eq_of_comp_eq (A := ℍ)
    (g₁ := fun w ↦ S (T w)) (g₂ := id) (S.continuous.comp T.continuous) continuous_id
    (by funext w; simp [hT', hS']) UpperHalfPlane.I (by simp [hS0, hT0])) w
  have hπT : ∀ τ, π (T τ) = π' τ := fun τ ↦ congrArg Subtype.val (hT' τ)
  have hπS : ∀ τ, π' (S τ) = π τ := fun τ ↦ congrArg Subtype.val (hS' τ)
  obtain ⟨g, hg⟩ := exists_SL2R_eq_of_holomorphic (h.holomorphicH_of_lift h' T.continuous hπT)
    (h'.holomorphicH_of_lift h S.continuous hπS) hTS hST
  have hgT : ∀ τ, h.toV (g • τ) = h'.toV τ := fun τ ↦ by rw [← hg, hT']
  refine ⟨g, fun z ↦ by rw [← hg, hπT], fun γ ↦ ⟨fun hγ ↦ ?_, fun hγ ↦ ?_⟩⟩
  · refine h.mem_pmGroup_of_deck fun w ↦ ?_
    rw [mul_smul, mul_smul, hgT, h'.toV_smul_pm hγ, ← hgT, smul_inv_smul]
  · have : γ = g⁻¹ * (g * γ * g⁻¹) * g := by group
    rw [this]
    refine h'.mem_pmGroup_of_deck fun w ↦ ?_
    rw [← hgT, ← hgT, ← mul_smul, show g * (g⁻¹ * (g * γ * g⁻¹) * g) = (g * γ * g⁻¹) * g by
      group, mul_smul, h.toV_smul_pm hγ]

end IsUniformization

end Uniformization
