/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.ES.GrauertRemmert.GraphPoint
import Oka.Analytification.RET.ES.GrauertRemmert.RegularPair

/-!
# Coherence of bounded sections off a codimension two set

Let `N° = {x ∈ N | g(x) ≠ 0}` for a holomorphic function `g` on `N ⊆ ℂ^{m+1}` which does not vanish
identically near any point, and let `g(x₀) = 0`. After an affine change of coordinates,
`(N, N°)` is near `x₀` in Weierstrass form
(`ComplexAnalytic.BoundedSections.exists_weierstrassForm_chart`): `N° = {P(b)(w) ≠ 0}` over a
ball `G` in the base, with `P` reduced. Let `δ` be the discriminant of `P`. If `δ(x₀) ≠ 0`, the
bounded sections are free over `G`. Otherwise, after a linear change of coordinates of the base,
the zero set of `δ` is the zero set of a reduced Weierstrass polynomial `Q(y)(v)` with discriminant
`d(y) ≢ 0`, and over every point of `G` off `Z = {Q(y)(v) = 0, d(y) = 0}` the polynomial `P` is
separable or `{δ = 0}` is a smooth graph `v = φ(y)`, a b-point. Hence the bounded sections satisfy
the local conditions for coherence at all points off the zero set `Z` of the regular pair
`(Q(y)(v), d(y))` (`ComplexAnalytic.BoundedSections.exists_localForm`).

## Main results

- `ComplexAnalytic.BoundedSections.exists_localForm`: a Weierstrass form near `x₀` and a regular
  pair off whose zero set the local conditions for coherence hold.
-/

open CategoryTheory Opposite AlgebraicGeometry Topology TopologicalSpace Filter Set Metric
  Polynomial

universe u

namespace ComplexAnalytic.BoundedSections

open AnalyticSpace KummerModel Cap

noncomputable section

variable {m : ℕ}

lemma mkPt_zero_zero : mkPt (0 : Cm.{u} m) (0 : ℂ) = 0 := by
  rw [← mkPt_baseOf_fibOf (0 : Cn.{u} (m + 1))]
  rfl

lemma norm_baseOf_le (x : Cn.{u} (m + 1)) : ‖baseOf x‖ ≤ ‖x‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg x)).2 fun i ↦ norm_le_pi_norm x ⟨i.down.succ⟩

/-- **The Weierstrass chart.** Let `L₁` be a linear change of coordinates and `P` a monic
polynomial such that, over `B(0, r₁)`, `x₀ + L₁(b, w) ∈ N` for `‖w‖ < 2s`, with
`g(x₀ + L₁(b, w)) = 0` if and only if `P(b)(w) = 0`, and the roots of `P(b)` have norm `< s / 2`.
Then for a linear change of coordinates `L₂` of the base mapping `B(0, r)` into `B(0, r₁)`, the
map `(b, w) ↦ x₀ + L₁(L₂ b, s w)` is a chart in which `(N, N°)` has a Weierstrass form over
`G = B(0, r)` with polynomial `s⁻ᵈ P(L₂ b)(s w)`. -/
theorem exists_weierstrassForm_chart {N N₀ : (AnalyticSpace.complexAffineSpace.{u} (m + 1)).Opens}
    {g : Cn.{u} (m + 1) → ℂ} (hN₀ : ∀ x ∈ N, x ∈ N₀ ↔ g x ≠ 0) {x₀ : Cn.{u} (m + 1)}
    (L₁ : Cn.{u} (m + 1) ≃L[ℂ] Cn.{u} (m + 1)) {P : Polynomial (Cm.{u} m → ℂ)} (hPm : P.Monic)
    {s r₁ : ℝ} (hs : 0 < s)
    (hN : ∀ b ∈ ball (0 : Cm.{u} m) r₁, ∀ w : ℂ, ‖w‖ < 2 * s → x₀ + L₁ (mkPt b w) ∈ N ∧
      (g (x₀ + L₁ (mkPt b w)) = 0 ↔ (evalPoly P b).eval w = 0))
    (hPd : ∀ k, DifferentiableOn ℂ (P.coeff k) (ball 0 r₁))
    (hroot : ∀ b ∈ ball (0 : Cm.{u} m) r₁, ∀ w, (evalPoly P b).IsRoot w → ‖w‖ < s / 2)
    (L₂ : Cm.{u} m ≃L[ℂ] Cm.{u} m) {r : ℝ} (hr : 0 < r) (hL₂ : ∀ b ∈ ball 0 r, L₂ b ∈ ball 0 r₁) :
    ∃ (B : LocalBiholo N) (F : WeierstrassForm B.A (B.A₀ N₀)), F.G = ball 0 r ∧ x₀ ∈ B.E ∧
      ∀ b ∈ F.G, (evalPoly P (L₂ b)).Separable → (evalPoly F.P b).Separable := by
  have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  set Φ : Cn.{u} (m + 1) → Cn.{u} (m + 1) := fun x ↦ x₀ + L₁ (mkPt (L₂ (baseOf x)) (s * fibOf x))
  set Ψ : Cn.{u} (m + 1) → Cn.{u} (m + 1) := fun y ↦
    mkPt (L₂.symm (baseOf (L₁.symm (y - x₀)))) (fibOf (L₁.symm (y - x₀)) / s)
  have hΦ : Differentiable ℂ Φ := by
    have h₁ : Differentiable ℂ fun x : Cn.{u} (m + 1) ↦ (L₂ (baseOf x), (s : ℂ) * fibOf x) :=
      (L₂.differentiable.comp differentiable_baseOf).prodMk
        (differentiable_fibOf.const_mul _)
    exact (differentiable_const _).add (L₁.differentiable.comp (differentiable_mkPt.comp h₁))
  have hΨ : Differentiable ℂ Ψ := by
    have h₀ : Differentiable ℂ fun y : Cn.{u} (m + 1) ↦ L₁.symm (y - x₀) :=
      L₁.symm.differentiable.comp (differentiable_id.sub_const _)
    have hb : Differentiable ℂ fun y : Cn.{u} (m + 1) ↦ L₂.symm (baseOf (L₁.symm (y - x₀))) :=
      L₂.symm.differentiable.comp
        (Differentiable.comp (g := baseOf.{u} (m := m)) differentiable_baseOf h₀)
    have hw : Differentiable ℂ fun y : Cn.{u} (m + 1) ↦ fibOf (L₁.symm (y - x₀)) / (s : ℂ) := by
      have := (Differentiable.comp (g := fibOf.{u} (m := m)) differentiable_fibOf h₀).mul_const
        ((s : ℂ)⁻¹)
      simpa [div_eq_mul_inv] using this
    exact differentiable_mkPt.comp (hb.prodMk hw)
  have hΨΦ : ∀ x, Ψ (Φ x) = x := fun x ↦ by
    simp only [Φ, Ψ, add_sub_cancel_left, ContinuousLinearEquiv.symm_apply_apply, baseOf_mkPt,
      fibOf_mkPt]
    rw [mul_div_cancel_left₀ _ hs0, mkPt_baseOf_fibOf]
  have hΦΨ : ∀ y, Φ (Ψ y) = y := fun y ↦ by
    simp only [Φ, Ψ, baseOf_mkPt, fibOf_mkPt, ContinuousLinearEquiv.apply_symm_apply]
    rw [mul_div_cancel₀ _ hs0, mkPt_baseOf_fibOf, ContinuousLinearEquiv.apply_symm_apply,
      add_sub_cancel]
  set A : (AnalyticSpace.complexAffineSpace.{u} (m + 1)).Opens :=
    ⟨{x | baseOf x ∈ ball 0 r ∧ ‖fibOf x‖ < 2}, by
      change IsOpen (baseOf ⁻¹' ball 0 r ∩ {x | ‖fibOf x‖ < 2})
      exact (isOpen_ball.preimage continuous_baseOf).inter
        (isOpen_lt continuous_fibOf.norm continuous_const)⟩
  have hAN : ∀ x : Cn.{u} (m + 1), x ∈ A → Φ x ∈ N ∧
      (g (Φ x) = 0 ↔ (evalPoly P (L₂ (baseOf x))).eval (s * fibOf x) = 0) := fun x hx ↦ by
    refine hN _ (hL₂ _ hx.1) _ ?_
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hs.le]
    nlinarith [hx.2, norm_nonneg (fibOf x)]
  have hx₀E : Ψ x₀ ∈ A := by
    have hΨ0 : Ψ x₀ = mkPt (0 : Cm.{u} m) 0 := by
      have h0 : baseOf (0 : Cn.{u} (m + 1)) = 0 := rfl
      have h0' : fibOf (0 : Cn.{u} (m + 1)) = 0 := rfl
      simp only [Ψ, sub_self, map_zero, h0, h0', zero_div]
    rw [hΨ0]
    refine ⟨?_, ?_⟩
    · rw [baseOf_mkPt]
      exact mem_ball_self hr
    · rw [fibOf_mkPt, norm_zero]
      exact two_pos
  let B : LocalBiholo N :=
    { A := A
      E := Ψ ⁻¹' {x | x ∈ A}
      isOpen_E := (isOpen_setOf_mem A).preimage hΨ.continuous
      E_sub := fun y hy ↦ hΦΨ y ▸ (hAN _ hy).1
      Φ := Φ
      Ψ := Ψ
      differentiableOn_Φ := hΦ.differentiableOn
      differentiableOn_Ψ := hΨ.differentiableOn
      mapsTo_Φ := fun x hx ↦ by
        change Ψ (Φ x) ∈ A
        rw [hΨΦ]
        exact hx
      mapsTo_Ψ := fun y hy ↦ hy
      Ψ_Φ := fun x _ ↦ hΨΦ x
      Φ_Ψ := fun y _ ↦ hΦΨ y }
  set P₂ := P.map (precompHom (L₂ : Cm.{u} m → Cm.{u} m))
  have hP₂m : P₂.Monic := hPm.map _
  have hP₂ev : ∀ b, evalPoly P₂ b = evalPoly P (L₂ b) := fun b ↦ evalPoly_map_precompHom _ _ _
  have hP₂d : ∀ k, DifferentiableOn ℂ (P₂.coeff k) (ball 0 r) := fun k b hb ↦ by
    rw [coeff_map_precompHom]
    exact ((hPd k).differentiableAt (isOpen_ball.mem_nhds (hL₂ b hb))).comp b
      L₂.differentiableAt |>.differentiableWithinAt
  have heval : ∀ b w, (evalPoly (scalePoly P₂ s) b).eval w = 0 ↔
      (evalPoly P (L₂ b)).eval (s * w) = 0 := fun b w ↦ by
    rw [eval_scalePoly hP₂m hs0, hP₂ev, mul_eq_zero, or_iff_right (pow_ne_zero _ (inv_ne_zero hs0))]
  let F : WeierstrassForm B.A (B.A₀ N₀) :=
    { G := ball 0 r
      isOpen_G := isOpen_ball
      convex_G := convex_ball _ _
      ρ := 2
      one_lt_ρ := one_lt_two
      mem_N := fun x ↦ Iff.rfl
      P := scalePoly P₂ s
      monic := monic_scalePoly _ _
      differentiableOn_coeff := differentiableOn_coeff_scalePoly hP₂d s
      mem_N₀ := fun x hx ↦ by
        refine (and_iff_right hx).trans ((hN₀ _ (hAN x hx).1).trans ?_)
        rw [ne_eq, ne_eq, not_iff_not, heval]
        exact (hAN x hx).2
      norm_lt_of_isRoot := fun b hb w hw ↦ by
        have h := hroot _ (hL₂ b hb) _ ((heval b w).1 hw)
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hs.le] at h
        have : ‖w‖ < 1 / 2 := by
          by_contra hle
          push Not at hle
          nlinarith [norm_nonneg w]
        simpa using this }
  refine ⟨B, F, rfl, hx₀E, fun b _ hsep ↦ ?_⟩
  · exact separable_scalePoly hP₂m hs0 (by rwa [hP₂ev])

/-- The empty family of regular pairs. -/
def RegularPairFamily.empty {ι : Type*} (U : Set (ι → ℂ)) : RegularPairFamily U where
  k := 0
  g i := i.elim0
  h i := i.elim0
  continuousOn_g i := i.elim0
  continuousOn_h i := i.elim0
  isWeaklyRegular i := i.elim0

lemma RegularPairFamily.zeroSet_empty {ι : Type*} (U : Set (ι → ℂ)) :
    (RegularPairFamily.empty U).zeroSet = ∅ := by
  ext z
  simp [RegularPairFamily.zeroSet, RegularPairFamily.empty]

lemma differentiableOn_coeff_of_eventually {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {P : Polynomial (E → ℂ)} (hP : ∀ k, ∀ᶠ y in 𝓝 (0 : E), DifferentiableAt ℂ (P.coeff k) y) :
    ∃ r > 0, ∀ k, DifferentiableOn ℂ (P.coeff k) (ball 0 r) := by
  obtain ⟨r, hr, hrd⟩ := Metric.eventually_nhds_iff_ball.1
    ((Finset.eventually_all (Finset.range (P.natDegree + 1))).2 fun k _ ↦ hP k)
  refine ⟨r, hr, fun k y hy ↦ ?_⟩
  by_cases hk : k ∈ Finset.range (P.natDegree + 1)
  · exact (hrd y hy k hk).differentiableWithinAt
  · rw [coeff_eq_zero_of_natDegree_lt (by simpa using hk)]
    exact differentiableWithinAt_const _

lemma not_eventuallyEq_zero_of_ball {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] {h : E → ℂ} {r : ℝ} (hh : DifferentiableOn ℂ h (ball 0 r))
    (h0 : ¬ h =ᶠ[𝓝 0] 0) (hr : 0 < r) : ∀ z ∈ ball (0 : E) r, ¬ h =ᶠ[𝓝 z] 0 := by
  intro z hz hzh
  have hA : AnalyticOnNhd ℂ h (ball 0 r) := fun y hy ↦
    analyticAt_of_differentiableOn_of_finiteDimensional isOpen_ball hh hy
  have heq := hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball 0 r).isPreconnected
    hz hzh
  exact h0 (Filter.eventually_of_mem (isOpen_ball.mem_nhds (mem_ball_self hr)) heq)

/-- **Coherence off the zero set of a regular pair.** Let `N° = {x ∈ N | g(x) ≠ 0}` for `g`
holomorphic on `N`, not vanishing identically near any point, and let `g(x₀) = 0`. Then there are
an affine chart `B` around `x₀`, a Weierstrass form `F` of `(N, N°)` in this chart and a family `R`
of regular pairs on the base `G` of `F` such that the bounded sections of every Hausdorff finite
étale cover satisfy the local conditions for coherence at all points of the chart not lying over
the zero set of `R`. For `m ≤ 1` the zero set of `R` is empty. -/
theorem exists_localForm {N N₀ : (AnalyticSpace.complexAffineSpace.{u} (m + 1)).Opens}
    {g : Cn.{u} (m + 1) → ℂ} (hg : DifferentiableOn ℂ g {x | x ∈ N})
    (hne : ∀ x ∈ N, ¬ g =ᶠ[𝓝 x] 0) (hN₀ : ∀ x ∈ N, x ∈ N₀ ↔ g x ≠ 0) {x₀ : Cn.{u} (m + 1)}
    (hx₀ : x₀ ∈ N) (hgx₀ : g x₀ = 0) :
    ∃ (B : LocalBiholo N) (F : WeierstrassForm B.A (B.A₀ N₀)) (R : RegularPairFamily F.G),
      x₀ ∈ B.E ∧ (m ≤ 1 → R.zeroSet = ∅) ∧
      ∀ (W : FiniteEtaleOver (space (B.A₀ N₀))) [T2Space W.left] (x : space B.A),
        baseOf x.1 ∉ R.zeroSet → IsCoherentAt (B.A₀_le N₀) W x := by
  -- the function near `x₀`
  set f : Cn.{u} (m + 1) → ℂ := fun x ↦ g (x₀ + x)
  have hf : AnalyticAt ℂ f 0 :=
    (analyticAt_of_differentiableOn_of_finiteDimensional (isOpen_setOf_mem N) hg hx₀).comp_of_eq
      (analyticAt_const.add analyticAt_id) (by simp)
  have hf0 : f 0 = 0 := by simp [f, hgx₀]
  have hfne : ¬ f =ᶠ[𝓝 0] 0 := fun h ↦ hne x₀ hx₀ (by
    have ht : Tendsto (fun x ↦ x - x₀) (𝓝 x₀) (𝓝 0) := by
      simpa using (continuous_sub_right x₀).tendsto x₀
    refine (ht.eventually h).mono fun (x : Cn.{u} (m + 1)) hx ↦ ?_
    have hx' : g (x₀ + (x - x₀)) = 0 := hx
    rw [add_sub_cancel] at hx'
    exact hx')
  obtain ⟨L₁, P, hPm, hPd, hPc, hP0, hPz, hPδ⟩ := exists_reducedWeierstrass hf hf0 hfne
  -- a product neighbourhood on which the zero sets agree
  have hev : ∀ᶠ p : Cm.{u} m × ℂ in 𝓝 (0, 0), x₀ + L₁ (mkPt p.1 p.2) ∈ N ∧
      (g (x₀ + L₁ (mkPt p.1 p.2)) = 0 ↔ (evalPoly P p.1).eval p.2 = 0) := by
    have hmk : Tendsto (fun p : Cm.{u} m × ℂ ↦ mkPt p.1 p.2) (𝓝 (0, 0)) (𝓝 0) := by
      have := differentiable_mkPt.continuous.tendsto ((0 : Cm.{u} m), (0 : ℂ))
      rwa [mkPt_zero_zero] at this
    have hN' : ∀ᶠ x in 𝓝 (0 : Cn.{u} (m + 1)), x₀ + L₁ x ∈ N := by
      have hc : Continuous fun x ↦ x₀ + L₁ x := by fun_prop
      have h := hc.tendsto 0
      rw [map_zero, add_zero] at h
      exact h.eventually ((isOpen_setOf_mem N).mem_nhds hx₀)
    filter_upwards [hmk.eventually (hN'.and hPz)] with p hp
    refine ⟨hp.1, ?_⟩
    have h := hp.2
    rwa [show splitEquiv m (mkPt p.1 p.2) = (p.1, p.2) from
      Homeomorph.apply_symm_apply _ _] at h
  obtain ⟨δ, hδ, hδev⟩ := Metric.eventually_nhds_iff.1 hev
  obtain ⟨rc, hrc, hPd'⟩ := differentiableOn_coeff_of_eventually hPc
  set s := δ / 2
  have hs : 0 < s := half_pos hδ
  obtain ⟨rr, hrr, hrrr⟩ := Metric.eventually_nhds_iff_ball.1
    (eventually_forall_isRoot_norm_lt hPm (c := 0)
      (fun k hk ↦ ⟨(hPc k).self_of_nhds.continuousAt, hP0 k hk⟩) (half_pos hs))
  set r₁ := min δ (min rc rr)
  have hr₁ : 0 < r₁ := lt_min hδ (lt_min hrc hrr)
  have hr₁c : ball (0 : Cm.{u} m) r₁ ⊆ ball 0 rc :=
    ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _))
  have hPd₁ : ∀ k, DifferentiableOn ℂ (P.coeff k) (ball 0 r₁) := fun k ↦ (hPd' k).mono hr₁c
  have hN1 : ∀ b ∈ ball (0 : Cm.{u} m) r₁, ∀ w : ℂ, ‖w‖ < 2 * s → x₀ + L₁ (mkPt b w) ∈ N ∧
      (g (x₀ + L₁ (mkPt b w)) = 0 ↔ (evalPoly P b).eval w = 0) := fun b hb w hw ↦ by
    refine hδev (y := (b, w)) ?_
    rw [Prod.dist_eq, max_lt_iff, dist_zero_right, dist_zero_right]
    refine ⟨(mem_ball_zero_iff.1 hb).trans_le (min_le_left _ _), ?_⟩
    have : 2 * s = δ := by ring
    linarith
  have hroot1 : ∀ b ∈ ball (0 : Cm.{u} m) r₁, ∀ w, (evalPoly P b).IsRoot w → ‖w‖ < s / 2 :=
    fun b hb ↦ hrrr b (ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _)) hb)
  -- the discriminant
  set Δ := discrFun P
  have hΔd : DifferentiableOn ℂ Δ (ball 0 r₁) := differentiableOn_discrFun hPd₁
  have hsepΔ : ∀ b, Δ b ≠ 0 → (evalPoly P b).Separable := fun b hb ↦
    separable_evalPoly_of_discrFun_ne_zero hPd hb
  by_cases hΔ0 : Δ 0 = 0
  · -- the discriminant locus passes through `0`
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := by
      rcases m with _ | m'
      · exfalso
        refine hPδ (Eventually.of_forall fun b ↦ ?_)
        rw [Subsingleton.elim b 0]
        exact hΔ0
      · exact ⟨m', rfl⟩
    have hΔA : AnalyticAt ℂ Δ 0 :=
      analyticAt_of_differentiableOn_of_finiteDimensional isOpen_ball hΔd (mem_ball_self hr₁)
    obtain ⟨L₂, Q, hQm, hQdeg, hQc, -, hQz, hQδ⟩ := exists_reducedWeierstrass (m := m') hΔA hΔ0 hPδ
    obtain ⟨rq, hrq, hQd⟩ := differentiableOn_coeff_of_eventually hQc
    set d := discrFun Q
    have hdd : DifferentiableOn ℂ d (ball 0 rq) := differentiableOn_discrFun hQd
    have hd0 := not_eventuallyEq_zero_of_ball hdd hQδ hrq
    -- the base radius
    have hL₂ : ∀ᶠ b in 𝓝 (0 : Cm.{u} (m' + 1)), L₂ b ∈ ball 0 r₁ := by
      have h := L₂.continuous.tendsto 0
      rw [map_zero] at h
      exact h.eventually (isOpen_ball.mem_nhds (mem_ball_self hr₁))
    have hbase : ∀ᶠ b in 𝓝 (0 : Cm.{u} (m' + 1)), baseOf b ∈ ball (0 : Cm.{u} m') rq := by
      have h := (continuous_baseOf (m := m')).tendsto 0
      exact h.eventually (isOpen_ball.mem_nhds (mem_ball_self hrq))
    obtain ⟨r, hr, hrb⟩ := Metric.eventually_nhds_iff_ball.1 (hL₂.and (hQz.and hbase))
    obtain ⟨B, F, hG, hx₀E, hsep⟩ := exists_weierstrassForm_chart hN₀ L₁ hPm hs hN1 hPd₁
      hroot1 L₂ hr fun b hb ↦ (hrb b hb).1
    have hGU : ∀ b ∈ F.G, baseOf b ∈ ball (0 : Cm.{u} m') rq := fun b hb ↦
      (hrb b (hG ▸ hb)).2.2
    refine ⟨B, F, polyPair hQm isOpen_ball hQd hdd hd0 hGU, hx₀E, fun hm ↦ ?_, fun W _ x hx ↦ ?_⟩
    · obtain rfl : m' = 0 := by omega
      rw [polyPair_zeroSet, eq_empty_iff_forall_notMem]
      rintro b ⟨-, hb⟩
      refine hQδ (Eventually.of_forall fun y ↦ ?_)
      rw [Subsingleton.elim y (baseOf b)]
      exact hb
    rw [polyPair_zeroSet] at hx
    set b := baseOf x.1
    have hbG : b ∈ F.G := ((F.mem_N x.1).1 x.2).1
    have hbr : b ∈ ball 0 r := hG ▸ hbG
    by_cases hΔb : Δ (L₂ b) = 0
    · -- a b-point
      have hQb : polyFun Q b = 0 := ((hrb b hbr).2.1).1 hΔb
      have hdb : d (baseOf b) ≠ 0 := fun h ↦ hx ⟨hQb, h⟩
      have hQsep := separable_evalPoly_of_discrFun_ne_zero hQdeg hdb
      have hsimple : (evalPoly Q (baseOf b)).derivative.eval (fibOf b) ≠ 0 := by
        have := hQsep.aeval_derivative_ne_zero (x := fibOf b) (by rwa [coe_aeval_eq_eval])
        rwa [coe_aeval_eq_eval] at this
      obtain ⟨r', hr', ε', hε', -, φ, hφd, hφb, hφ⟩ := exists_simpleRoot_branch hQm isOpen_ball
        hQd (hGU b hbG) hQb hsimple
      refine F.isCoherentAt_of_graph (B.A₀_le N₀) W hbG hr' hε' hφd hφb
        (fun b' hb'G hb'1 hb'2 hb'3 ↦ hsep b' hb'G (hsepΔ _ fun h ↦ hb'3 ?_)) x rfl
      have hQb' : polyFun Q b' = 0 := ((hrb b' (hG ▸ hb'G)).2.1).1 h
      exact ((hφ _ hb'1).2 _ hb'2).1 hQb'
    · exact F.isCoherentAt_of_separable (B.A₀_le N₀) W x (hsep b hbG (hsepΔ _ hΔb))
  · -- the discriminant does not vanish near `0`
    have hΔc : ContinuousAt Δ 0 :=
      hΔd.continuousOn.continuousAt (isOpen_ball.mem_nhds (mem_ball_self hr₁))
    obtain ⟨r, hr, hrΔ⟩ := Metric.eventually_nhds_iff_ball.1
      ((hΔc.eventually_ne hΔ0).and (isOpen_ball.mem_nhds (mem_ball_self hr₁)))
    obtain ⟨B, F, hG, hx₀E, hsep⟩ := exists_weierstrassForm_chart hN₀ L₁ hPm hs hN1 hPd₁
      hroot1 (ContinuousLinearEquiv.refl ℂ _) hr fun b hb ↦ (hrΔ b hb).2
    refine ⟨B, F, RegularPairFamily.empty _, hx₀E, fun _ ↦ RegularPairFamily.zeroSet_empty _,
      fun W _ x _ ↦ ?_⟩
    have hbG : baseOf x.1 ∈ F.G := ((F.mem_N x.1).1 x.2).1
    exact F.isCoherentAt_of_separable (B.A₀_le N₀) W x
      (hsep _ hbG (hsepΔ _ (hrΔ _ (hG ▸ hbG)).1))

end

end ComplexAnalytic.BoundedSections
