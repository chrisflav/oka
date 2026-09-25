/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.ES.Cap
import Oka.Analytification.RET.ES.Codim2.CoordFreeness
import Oka.Analytification.RET.ES.GrauertRemmert.HolomorphicPolynomial
import Oka.Analytification.RET.ES.GrauertRemmert.LocalChart
import Oka.UliftCoord

/-!
# Weierstrass form of the complement of `N°`

Write the points of `ℂ^{m+1}` as `(b, w)`, `b ∈ ℂ^m`, `w` the coordinate `0`
(`ComplexAnalytic.KummerModel.splitEquiv`). A **Weierstrass form** of `(N, N°)`
(`ComplexAnalytic.BoundedSections.WeierstrassForm`) consists of a convex open `G ⊆ ℂ^m`, a radius
`ρ > 1` and a monic polynomial `P` in `w` with coefficients holomorphic on `G`, such that
`N = G × {‖w‖ < ρ}`, `N° = {P(b)(w) ≠ 0}` and the roots of `P(b)` lie in `{‖w‖ < ρ⁻¹}`. In
particular `N°` contains the annulus region `G × {ρ⁻¹ < ‖w‖ < ρ}` of
`Oka/Analytification/RET/ES/Cap.lean` (`…WeierstrassForm.annulusRegion_subset`).

Near every point of a hypersurface, after a linear change of coordinates, the zero set is the zero
set of a Weierstrass polynomial whose discriminant does not vanish identically
(`ComplexAnalytic.BoundedSections.exists_reducedWeierstrass`, the form of
`ComplexAnalytic.exists_reducedWeierstrass_fin` in the coordinates `(b, w)`).

Over a point `b` where `P(b)` is separable, `N ∖ N°` is a union of disjoint smooth graphs, so the
bounded sections are free (`…WeierstrassForm.isCoherentAt_of_separable`).

## Main definitions

- `ComplexAnalytic.BoundedSections.WeierstrassForm N N₀`: the data above.

## Main results

- `ComplexAnalytic.BoundedSections.exists_reducedWeierstrass`: the reduced Weierstrass polynomial.
- `ComplexAnalytic.BoundedSections.WeierstrassForm.isCoherentAt_of_separable`: the local
  conditions for coherence over points where `P` is separable.
-/

open CategoryTheory Opposite AlgebraicGeometry Topology TopologicalSpace Filter Set Metric
  Polynomial

universe u

namespace ComplexAnalytic.BoundedSections

open AnalyticSpace KummerModel Cap Complex.ProjectiveLineBundle

noncomputable section

variable {m : ℕ}

/-! ### The reduced Weierstrass polynomial in the coordinates `(b, w)` -/

/-- The relabelling of `Fin (m + 1)` sending the last index to `0`. -/
def rotIdx (m : ℕ) : ULift.{u} (Fin (m + 1)) ≃ Fin (m + 1) :=
  Equiv.ulift.trans (finRotate (m + 1)).symm

lemma rotIdx_zero : rotIdx.{u} m ⟨0⟩ = Fin.last m := by
  rw [rotIdx, Equiv.trans_apply, Equiv.symm_apply_eq]
  exact (finRotate_last).symm

lemma rotIdx_succ (i : Fin m) : rotIdx.{u} m ⟨i.succ⟩ = i.castSucc := by
  rw [rotIdx, Equiv.trans_apply, Equiv.symm_apply_eq]
  refine Fin.ext ?_
  rw [coe_finRotate_of_ne_last (Fin.castSucc_ne_last i)]
  simp

/-- The identification of `Fin (m + 1) → ℂ` with `ℂ^{m+1}` sending the last coordinate to `w`. -/
def rotCoord (m : ℕ) : (Fin (m + 1) → ℂ) ≃L[ℂ] Cn.{u} (m + 1) :=
  (LinearEquiv.funCongrLeft ℂ ℂ (rotIdx.{u} m)).toContinuousLinearEquiv

lemma splitEquiv_rotCoord (y : Fin (m + 1) → ℂ) :
    splitEquiv.{u} m (rotCoord.{u} m y) =
      (LocalOkaRing.uliftCoord.{u} (Fin m) (Fin.init y), y (Fin.last m)) := by
  refine Prod.ext (funext fun i ↦ ?_) ?_
  · change y (rotIdx.{u} m ⟨i.down.succ⟩) = Fin.init y i.down
    rw [rotIdx_succ]
    rfl
  · change y (rotIdx.{u} m ⟨0⟩) = _
    rw [rotIdx_zero]

/-- **The reduced Weierstrass polynomial** in the coordinates `(b, w)`: after a linear change of
coordinates `L`, the zero set of `f` near `0` is the zero set of a Weierstrass polynomial `P` in `w`
whose discriminant does not vanish identically near `0`. -/
theorem exists_reducedWeierstrass {f : Cn.{u} (m + 1) → ℂ} (hf : AnalyticAt ℂ f 0)
    (hf0 : f 0 = 0) (hne : ¬ f =ᶠ[𝓝 0] 0) :
    ∃ (L : Cn.{u} (m + 1) ≃L[ℂ] Cn.{u} (m + 1)) (P : Polynomial (Cm.{u} m → ℂ)),
      P.Monic ∧ 0 < P.natDegree ∧ (∀ k, ∀ᶠ y in 𝓝 0, DifferentiableAt ℂ (P.coeff k) y) ∧
      (∀ k < P.natDegree, P.coeff k 0 = 0) ∧
      (∀ᶠ x in 𝓝 0, f (L x) = 0 ↔ (evalPoly P (splitEquiv m x).1).eval (splitEquiv m x).2 = 0) ∧
      ¬ discrFun P =ᶠ[𝓝 0] 0 := by
  set e := rotCoord.{u} m
  set ι := LocalOkaRing.uliftCoord.{u} (Fin m)
  have he : Tendsto (e.symm : Cn.{u} (m + 1) → (Fin (m + 1) → ℂ)) (𝓝 0) (𝓝 0) := by
    simpa using e.symm.continuous.tendsto 0
  have hι : Tendsto (ι : (Fin m → ℂ) → Cm.{u} m) (𝓝 0) (𝓝 0) := by
    simpa using ι.continuous.tendsto 0
  have hι' : Tendsto (ι.symm : Cm.{u} m → (Fin m → ℂ)) (𝓝 0) (𝓝 0) := by
    simpa using ι.symm.continuous.tendsto 0
  obtain ⟨LF, PF, hPm, hPd, hPc, hP0, hPz, hPδ⟩ := exists_reducedWeierstrass_fin (f := f ∘ e)
    (hf.comp_of_eq (e.analyticAt 0) (map_zero e)) (by simpa using hf0) fun h ↦ hne (by
      have := he.eventually h
      filter_upwards [this] with x hx
      simpa using hx)
  set P := PF.map (precompHom (ι.symm : Cm.{u} m → (Fin m → ℂ)))
  have hPdeg : P.natDegree = PF.natDegree := hPm.natDegree_map _
  refine ⟨(e.symm.trans LF).trans e, P, hPm.map _, hPdeg ▸ hPd, fun k ↦ ?_, fun k hk ↦ ?_, ?_, ?_⟩
  · rw [coeff_map_precompHom]
    filter_upwards [hι'.eventually (hPc k)] with y hy
    exact hy.comp y (ι.symm.differentiableAt)
  · rw [coeff_map_precompHom, Function.comp_apply, map_zero]
    exact hP0 k (hPdeg ▸ hk)
  · filter_upwards [he.eventually hPz] with x hx
    have hsplit := splitEquiv_rotCoord.{u} (e.symm x)
    rw [ContinuousLinearEquiv.apply_symm_apply] at hsplit
    rw [hsplit, evalPoly_map_precompHom, ContinuousLinearEquiv.symm_apply_apply]
    exact hx
  · intro h
    have hδ : discrFun P = discrFun PF ∘ (ι.symm : Cm.{u} m → (Fin m → ℂ)) := by
      rw [discrFun, discrFun, hPdeg, derivative_map, resultant_map_map]
      rfl
    refine hPδ ?_
    rw [hδ] at h
    filter_upwards [hι.eventually h] with y hy
    simpa using hy

/-! ### Weierstrass forms -/

/-- The base point `b` of `x = (b, w) ∈ ℂ^{m+1}`. -/
abbrev baseOf (x : Cn.{u} (m + 1)) : Cm.{u} m := (splitEquiv m x).1

/-- The coordinate `w` of `x = (b, w) ∈ ℂ^{m+1}`. -/
abbrev fibOf (x : Cn.{u} (m + 1)) : ℂ := (splitEquiv m x).2


lemma differentiable_baseOf : Differentiable ℂ (baseOf.{u} (m := m)) :=
  Cap.differentiable_splitEquiv.fst

lemma differentiable_fibOf : Differentiable ℂ (fibOf.{u} (m := m)) :=
  Cap.differentiable_splitEquiv.snd

lemma continuous_baseOf : Continuous (baseOf.{u} (m := m)) :=
  differentiable_baseOf.continuous

lemma continuous_fibOf : Continuous (fibOf.{u} (m := m)) :=
  differentiable_fibOf.continuous

/-- The point `(b, w)` of `ℂ^{m+1}`. -/
abbrev mkPt (b : Cm.{u} m) (w : ℂ) : Cn.{u} (m + 1) := (splitEquiv m).symm (b, w)

@[simp]
lemma baseOf_mkPt (b : Cm.{u} m) (w : ℂ) : baseOf (mkPt b w) = b := by
  simp only [baseOf, mkPt, Homeomorph.apply_symm_apply]

@[simp]
lemma fibOf_mkPt (b : Cm.{u} m) (w : ℂ) : fibOf (mkPt b w) = w := by
  simp only [fibOf, mkPt, Homeomorph.apply_symm_apply]

lemma mkPt_baseOf_fibOf (x : Cn.{u} (m + 1)) : mkPt (baseOf x) (fibOf x) = x :=
  (splitEquiv m).symm_apply_apply x

lemma mkPt_zero (b : Cm.{u} m) (w : ℂ) : mkPt b w zero = w :=
  rfl

lemma differentiable_mkPt : Differentiable ℂ fun p : Cm.{u} m × ℂ ↦ mkPt p.1 p.2 :=
  Cap.differentiable_splitEquiv_symm

/-- **A Weierstrass form of `(N, N°)`**: `N = G × {‖w‖ < ρ}` with `G` convex and open and `ρ > 1`,
and `N° = {P(b)(w) ≠ 0}` for a monic polynomial `P` in `w` with coefficients holomorphic on `G`
whose roots lie in `{‖w‖ < ρ⁻¹}`. -/
structure WeierstrassForm (N N₀ : (AnalyticSpace.complexAffineSpace.{u} (m + 1)).Opens) where
  /-- The base. -/
  G : Set (Cm.{u} m)
  isOpen_G : IsOpen G
  convex_G : Convex ℝ G
  /-- The radius. -/
  ρ : ℝ
  one_lt_ρ : 1 < ρ
  mem_N : ∀ x, x ∈ N ↔ baseOf x ∈ G ∧ ‖fibOf x‖ < ρ
  /-- The Weierstrass polynomial. -/
  P : Polynomial (Cm.{u} m → ℂ)
  monic : P.Monic
  differentiableOn_coeff : ∀ k, DifferentiableOn ℂ (P.coeff k) G
  mem_N₀ : ∀ x ∈ N, x ∈ N₀ ↔ (evalPoly P (baseOf x)).eval (fibOf x) ≠ 0
  norm_lt_of_isRoot : ∀ b ∈ G, ∀ w, (evalPoly P b).IsRoot w → ‖w‖ < ρ⁻¹

namespace WeierstrassForm

variable {N N₀ : (AnalyticSpace.complexAffineSpace.{u} (m + 1)).Opens} (F : WeierstrassForm N N₀)

lemma pos_ρ : 0 < F.ρ :=
  zero_lt_one.trans F.one_lt_ρ

/-- The annulus region `G × {ρ⁻¹ < ‖w‖ < ρ}` lies in `N°`. -/
lemma annulusRegion_subset : ∀ x ∈ annulusRegion F.G F.ρ, x ∈ N₀ := by
  intro x hx
  have hx' : baseOf x ∈ F.G ∧ fibOf x ∈ overlap F.ρ := hx
  have hxN : x ∈ N := (F.mem_N x).2 ⟨hx'.1, hx'.2.2⟩
  refine (F.mem_N₀ x hxN).2 fun h ↦ ?_
  exact lt_asymm (F.norm_lt_of_isRoot _ hx'.1 _ h) hx'.2.1

/-- A point outside `N`. -/
def outPt : Cn.{u} (m + 1) := (splitEquiv m).symm (0, F.ρ)

lemma outPt_not_mem (h₀ : N₀ ≤ N) : F.outPt ∉ N₀ := fun h ↦ by
  have := ((F.mem_N _).1 (h₀ h)).2
  rw [fibOf, outPt, Homeomorph.apply_symm_apply, Complex.norm_real,
    Real.norm_of_nonneg F.pos_ρ.le] at this
  exact lt_irrefl _ this


/-- **Freeness over points where `P` is separable**: there `N ∖ N°` is a union of disjoint smooth
graphs `w = φ(b)`, i.e. a coordinate hyperplane in the coordinates `(b, w - φ(b))`. -/
theorem isCoherentAt_of_separable (h₀ : N₀ ≤ N) (W : FiniteEtaleOver (space N₀))
    [T2Space W.left] (x : space N) (hsep : (evalPoly F.P (baseOf x.1)).Separable) :
    IsCoherentAt h₀ W x := by
  classical
  obtain ⟨hbG, hwρ⟩ := (F.mem_N x.1).1 x.2
  set b := baseOf x.1
  set w₀ := fibOf x.1
  by_cases hroot : (evalPoly F.P b).eval w₀ = 0
  · have hsimple : (evalPoly F.P b).derivative.eval w₀ ≠ 0 := by
      have := hsep.aeval_derivative_ne_zero (x := w₀) (by rwa [coe_aeval_eq_eval])
      rwa [coe_aeval_eq_eval] at this
    obtain ⟨r, hr, ε, hε, hrG, φ, hφd, hφb, hφ⟩ := exists_simpleRoot_branch F.monic F.isOpen_G
      F.differentiableOn_coeff hbG hroot hsimple
    set ε' := min ε (F.ρ - ‖w₀‖)
    have hε' : 0 < ε' := lt_min hε (sub_pos.2 hwρ)
    set O : Set (Cn.{u} (m + 1)) := {y | baseOf y ∈ ball b r ∧ ‖fibOf y - w₀‖ < ε'}
    set O' : Set (Cn.{u} (m + 1)) := {z | baseOf z ∈ ball b r ∧ ‖fibOf z + φ (baseOf z) - w₀‖ < ε'}
    have hO : IsOpen O := by
      change IsOpen (baseOf ⁻¹' ball b r ∩ {y | ‖fibOf y - w₀‖ < ε'})
      exact (isOpen_ball.preimage continuous_baseOf).inter
        (isOpen_lt (continuous_fibOf.sub continuous_const).norm continuous_const)
    have hφc : ContinuousOn (fun z : Cn.{u} (m + 1) ↦ ‖fibOf z + φ (baseOf z) - w₀‖)
        (baseOf ⁻¹' ball b r) :=
      ((continuous_fibOf.continuousOn.add (hφd.continuousOn.comp continuous_baseOf.continuousOn
        fun _ h ↦ h)).sub continuousOn_const).norm
    have hO' : IsOpen O' := by
      have := hφc.isOpen_inter_preimage (isOpen_ball.preimage continuous_baseOf)
        (isOpen_Iio (a := ε'))
      exact this
    have hON : ∀ y ∈ O, y ∈ N := fun y hy ↦ (F.mem_N y).2 ⟨hrG hy.1, by
      calc ‖fibOf y‖ = ‖(fibOf y - w₀) + w₀‖ := by ring_nf
        _ ≤ ‖fibOf y - w₀‖ + ‖w₀‖ := norm_add_le _ _
        _ < (F.ρ - ‖w₀‖) + ‖w₀‖ := by linarith [hy.2.trans_le (min_le_right ε _)]
        _ = F.ρ := by ring⟩
    set Φ : Cn.{u} (m + 1) → Cn.{u} (m + 1) := fun y ↦ mkPt (baseOf y) (fibOf y - φ (baseOf y))
    set Φ' : Cn.{u} (m + 1) → Cn.{u} (m + 1) := fun z ↦ mkPt (baseOf z) (fibOf z + φ (baseOf z))
    have hφO : DifferentiableOn ℂ (fun y ↦ φ (baseOf y)) (baseOf ⁻¹' ball b r) :=
      hφd.comp differentiable_baseOf.differentiableOn fun _ h ↦ h
    have hΦ : DifferentiableOn ℂ Φ O := fun y hy ↦
      (differentiable_mkPt (baseOf y, fibOf y - φ (baseOf y))).comp_differentiableWithinAt y
        ((differentiable_baseOf.differentiableAt.differentiableWithinAt).prodMk
          (differentiable_fibOf.differentiableAt.differentiableWithinAt.sub
            ((hφO y hy.1).mono fun _ h ↦ h.1)))
    have hΦ' : DifferentiableOn ℂ Φ' O' := fun y hy ↦
      (differentiable_mkPt (baseOf y, fibOf y + φ (baseOf y))).comp_differentiableWithinAt y
        ((differentiable_baseOf.differentiableAt.differentiableWithinAt).prodMk
          (differentiable_fibOf.differentiableAt.differentiableWithinAt.add
            ((hφO y hy.1).mono fun _ h ↦ h.1)))
    obtain ⟨U, k, e, hxU, hfree⟩ := exists_isFreeSpanAt_of_coords h₀ W hO hON hO' hΦ hΦ'
      (fun y hy ↦ ⟨by simpa [Φ] using hy.1, by simpa [Φ] using hy.2⟩)
      (fun z hz ↦ ⟨by simpa [Φ'] using hz.1, by simpa [Φ'] using hz.2⟩)
      (fun y _ ↦ by simp [Φ, Φ', mkPt_baseOf_fibOf])
      (fun z _ ↦ by simp [Φ, Φ', mkPt_baseOf_fibOf]) {zero}
      (fun y hy ↦ by
        refine (F.mem_N₀ y (hON y hy)).trans ?_
        simp only [Finset.mem_singleton, forall_eq]
        change _ ↔ fibOf y - φ (baseOf y) ≠ 0
        rw [ne_eq, ne_eq, sub_eq_zero, ← (hφ (baseOf y) hy.1).2 _
          (hy.2.trans_le (min_le_left _ _))]
        rfl)
      (x₀ := x.1) ⟨mem_ball_self hr, show ‖w₀ - w₀‖ < ε' by simpa using hε'⟩
      (fun j hj ↦ by
        rw [Finset.mem_singleton.1 hj]
        change w₀ - φ b = 0
        rw [hφb, sub_self])
    exact isCoherentAt_of_isFreeSpanAt _ _ (hfree x (mem_img_iff.1 hxU).2)
  · have hx₀ : x.1 ∈ N₀ := (F.mem_N₀ x.1 x.2).2 hroot
    obtain ⟨U, k, e, hxU, hfree⟩ := exists_isFreeSpanAt_of_coords h₀ W
      (isOpen_setOf_mem N₀) (fun _ hy ↦ h₀ hy) (isOpen_setOf_mem N₀) (Φ := id) (Φ' := id)
      differentiableOn_id differentiableOn_id (fun _ h ↦ h) (fun _ h ↦ h) (fun _ _ ↦ rfl)
      (fun _ _ ↦ rfl) ∅ (fun y hy ↦ by simpa using hy) (x₀ := x.1) hx₀ (by simp)
    exact isCoherentAt_of_isFreeSpanAt _ _ (hfree x (mem_img_iff.1 hxU).2)

end WeierstrassForm

end

end ComplexAnalytic.BoundedSections
