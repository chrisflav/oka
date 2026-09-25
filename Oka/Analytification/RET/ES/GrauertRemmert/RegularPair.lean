/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytic.HartogsRegularCoord
import Oka.Analytification.RET.ES.Codim2.BPointConfig
import Oka.Analytification.RET.ES.GrauertRemmert.WeierstrassForm

/-!
# A monic polynomial and a function of the other variables form a regular pair

Write the points of `ℂ^{k+1}` as `(y, v)`. Let `Q` be a monic polynomial in `v` whose coefficients
are holomorphic functions of `y`, and let `h` be a holomorphic function of `y` which does not
vanish identically near any point. Then at every point the germs of `Q(y)(v)` and `h(y)` form a
regular sequence (`ComplexAnalytic.BoundedSections.isWeaklyRegular_polyPair`), so they give a
family of regular pairs (`ComplexAnalytic.BoundedSections.polyPair`).

## Proof

At the origin, in coordinates in which `v` is the last one, the germ `G` of `Q(y)(v)` is general
in `v` since `Q(0)(v)` is a nonzero polynomial, so by the Weierstrass preparation theorem it is a
unit times a Weierstrass polynomial `W`, and the germ of `h` is `incl H₀` for a nonzero germ `H₀`
in `y`. If `W ∣ incl H₀ · a`, divide `a = α W + b` with `deg b < deg W`; then `W` divides
`H₀ b`, which has smaller degree, so `b = 0` (`LocalOkaRing.fromPolynomial_dvd_of_dvd_incl_mul`).
-/

open Filter Topology Polynomial Metric Set RingTheory.Sequence

universe u

namespace LocalOkaRing

variable {k : ℕ}

/-- **`incl H₀` is a nonzerodivisor modulo a Weierstrass polynomial**, for a nonzero germ `H₀` in
the other variables. -/
lemma fromPolynomial_dvd_of_dvd_incl_mul {W : (LocalOkaRing (Fin k))[X]}
    (hW : IsLocalWeierstrassPolynomial
      (Polynomial.map (Subring.subtype (localOkaSubring _).toSubring) W))
    {H₀ : LocalOkaRing (Fin k)} (hH₀ : H₀ ≠ 0) {y : LocalOkaRing (Fin (k + 1))}
    (h : fromPolynomial W ∣ incl H₀ * y) : fromPolynomial W ∣ y := by
  obtain ⟨a, b, hb, rfl⟩ := localweierstrass_division W hW y
  have hWm : W.Monic := monic_of_isLocalWeierstrass hW
  have hdvd : fromPolynomial W ∣ fromPolynomial (C H₀ * b) := by
    have heq : fromPolynomial (C H₀ * b) =
        incl H₀ * (a * fromPolynomial W + fromPolynomial b) - incl H₀ * a * fromPolynomial W := by
      rw [map_mul, fromPolynomial_C]
      ring
    rw [heq]
    exact dvd_sub h (dvd_mul_left _ _)
  have h0 : C H₀ * b = 0 := by
    refine eq_zero_of_dvd_of_degree_lt (dvd_of_fromPolynomial_dvd hW hdvd) ?_
    exact (degree_mul_le _ _).trans_lt (by
      rw [degree_C hH₀, zero_add]
      exact hb)
  rw [mul_eq_zero, C_eq_zero] at h0
  rw [h0.resolve_left hH₀, map_zero, add_zero]
  exact dvd_mul_left _ _

/-- **A germ general in the last variable and a nonzero germ in the other variables form a
regular pair**, in the form of its two conditions. -/
lemma dvd_of_dvd_incl_mul_of_isGeneralIn {G : LocalOkaRing (Fin (k + 1))}
    (hG : (G : MvPowerSeries (Fin (k + 1)) ℂ).IsGeneralIn (Fin.last k))
    {H₀ : LocalOkaRing (Fin k)} (hH₀ : H₀ ≠ 0) {y : LocalOkaRing (Fin (k + 1))}
    (h : G ∣ incl H₀ * y) : G ∣ y := by
  obtain ⟨u, hu, W, hW, rfl⟩ := localweierstrass_preparation G hG
  have h' : fromPolynomial W ∣ incl H₀ * y := (dvd_mul_right _ _).trans h
  obtain ⟨c, hc⟩ := fromPolynomial_dvd_of_dvd_incl_mul hW hH₀ h'
  refine ⟨hu.unit⁻¹ * c, ?_⟩
  rw [hc, mul_assoc, ← mul_assoc u, IsUnit.mul_val_inv, one_mul]

lemma ne_zero_of_isGeneralIn {G : LocalOkaRing (Fin (k + 1))}
    (hG : (G : MvPowerSeries (Fin (k + 1)) ℂ).IsGeneralIn (Fin.last k)) : G ≠ 0 := by
  rintro rfl
  exact hG (by simp [MvPowerSeries.partialEval])

end LocalOkaRing

namespace ComplexAnalytic.BoundedSections

open AnalyticSpace KummerModel Cap LocalOkaRing

noncomputable section

variable {k : ℕ}

/-- The function `(y, v) ↦ Q(y)(v)` on `ℂ^{k+1}`. -/
def polyFun (Q : Polynomial (Cm.{u} k → ℂ)) (b : Cm.{u} (k + 1)) : ℂ :=
  (evalPoly Q (baseOf b)).eval (fibOf b)

lemma differentiableOn_polyFun {Q : Polynomial (Cm.{u} k → ℂ)} {U : Set (Cm.{u} k)}
    (hQd : ∀ j, DifferentiableOn ℂ (Q.coeff j) U) :
    DifferentiableOn ℂ (polyFun Q) (baseOf ⁻¹' U) := by
  have h : polyFun Q = fun b ↦ ∑ j ∈ Finset.range (Q.natDegree + 1),
      Q.coeff j (baseOf b) * fibOf b ^ j := funext fun b ↦ by
    rw [polyFun, eval_eq_sum_range' (Nat.lt_succ_of_le (natDegree_evalPoly_le Q _))]
    simp
  rw [h]
  exact DifferentiableOn.fun_sum fun j _ ↦ ((hQd j).comp differentiable_baseOf.differentiableOn
    fun _ h ↦ h).mul (differentiable_fibOf.pow j).differentiableOn

lemma baseOf_add (a b : Cm.{u} (k + 1)) : baseOf (a + b) = baseOf a + baseOf b :=
  rfl

lemma fibOf_add (a b : Cm.{u} (k + 1)) : fibOf (a + b) = fibOf a + fibOf b :=
  rfl

/-- **`Q(y)(v)` and `h(y)` form a regular pair** at every point `z` over `U`, if `h` does not
vanish identically near any point of `U`. -/
theorem isWeaklyRegular_polyPair {Q : Polynomial (Cm.{u} k → ℂ)} (hQ : Q.Monic)
    {U : Set (Cm.{u} k)} (hU : IsOpen U) (hQd : ∀ j, DifferentiableOn ℂ (Q.coeff j) U)
    {h : Cm.{u} k → ℂ} (hh : DifferentiableOn ℂ h U) (hh0 : ∀ z ∈ U, ¬ h =ᶠ[𝓝 z] 0)
    {z : Cm.{u} (k + 1)} (hz : baseOf z ∈ U) :
    ∃ G H : LocalOkaRing (ULift.{u} (Fin (k + 1))),
      (G : MvPowerSeries _ ℂ).Represents (fun w ↦ polyFun Q (w + z)) ∧
      (H : MvPowerSeries _ ℂ).Represents (fun w ↦ h (baseOf (w + z))) ∧
      IsWeaklyRegular (LocalOkaRing (ULift.{u} (Fin (k + 1)))) [G, H] := by
  classical
  set e := rotCoord.{u} k
  set ι := LocalOkaRing.uliftCoord.{u} (Fin k)
  have hsplit (y : Fin (k + 1) → ℂ) :
      baseOf (e y) = ι (Fin.init y) ∧ fibOf (e y) = y (Fin.last k) :=
    Prod.ext_iff.1 (splitEquiv_rotCoord y)
  -- the germ of `h`
  set h₀ : (Fin k → ℂ) → ℂ := fun a ↦ h (ι a + baseOf z)
  have hh₀ : AnalyticAt ℂ h₀ 0 := by
    have hA := analyticAt_of_differentiableOn_of_finiteDimensional hU hh hz
    exact hA.comp_of_eq ((ι.analyticAt 0).add analyticAt_const) (by simp)
  obtain ⟨P₀, hP₀c, hP₀⟩ := MvPowerSeries.exists_represents hh₀
  obtain ⟨H₀, hH₀e⟩ : ∃ H : LocalOkaRing (Fin k), (H : MvPowerSeries (Fin k) ℂ) = P₀ :=
    ⟨⟨P₀, hP₀c⟩, rfl⟩
  rw [← hH₀e] at hP₀
  have hH₀ : H₀ ≠ 0 := fun h0 ↦ hh0 _ hz (by
    have h1 : h₀ =ᶠ[𝓝 0] 0 := by
      have := (MvPowerSeries.represents_zero (ι := Fin k)).eventuallyEq
        (show ((0 : LocalOkaRing (Fin k)) : MvPowerSeries (Fin k) ℂ).Represents h₀ from
          h0 ▸ hP₀)
      filter_upwards [this] with a ha using ha.symm
    have ht : Tendsto (fun b ↦ ι.symm (b - baseOf z)) (𝓝 (baseOf z)) (𝓝 0) := by
      have hc : Continuous fun b ↦ ι.symm (b - baseOf z) := by fun_prop
      simpa using hc.tendsto (baseOf z)
    filter_upwards [ht.eventually h1] with b hb
    simpa [h₀] using hb)
  have hHF : ((incl H₀ : LocalOkaRing (Fin (k + 1))) : MvPowerSeries (Fin (k + 1)) ℂ).Represents
      (fun y ↦ h (baseOf (e y + z))) := by
    refine (MvPowerSeries.Represents.rename_castSucc hP₀).congr (Eventually.of_forall fun y ↦ ?_)
    change h (ι (Fin.init y) + baseOf z) = h (baseOf (e y + z))
    rw [baseOf_add, (hsplit y).1]
  -- the germ of `Q(y)(v)`
  have hqd : DifferentiableOn ℂ (fun y ↦ polyFun Q (e y + z))
      ((fun y ↦ e y + z) ⁻¹' (baseOf ⁻¹' U)) :=
    (differentiableOn_polyFun hQd).comp
      ((by fun_prop : Differentiable ℂ fun y ↦ e y + z).differentiableOn) fun _ h ↦ h
  have hqA : AnalyticAt ℂ (fun y ↦ polyFun Q (e y + z)) 0 :=
    analyticAt_of_differentiableOn_of_finiteDimensional
      ((hU.preimage differentiable_baseOf.continuous).preimage (by fun_prop)) hqd
      (by simpa using hz)
  obtain ⟨PG, hPGc, hPG⟩ := MvPowerSeries.exists_represents hqA
  obtain ⟨GF, hGFe⟩ : ∃ G : LocalOkaRing (Fin (k + 1)), (G : MvPowerSeries (Fin (k + 1)) ℂ) = PG :=
    ⟨⟨PG, hPGc⟩, rfl⟩
  rw [← hGFe] at hPG
  have haxis (t : ℂ) : polyFun Q (e (t • Pi.single (Fin.last k) (1 : ℂ)) + z) =
      (evalPoly Q (baseOf z)).eval (fibOf z + t) := by
    have hy : Fin.init (t • Pi.single (Fin.last k) (1 : ℂ)) = 0 := by
      funext j
      simp [Fin.init, (Fin.castSucc_lt_last j).ne]
    have hl : (t • Pi.single (Fin.last k) (1 : ℂ)) (Fin.last k) = t := by simp
    have h₁ := (hsplit (t • Pi.single (Fin.last k) (1 : ℂ))).1
    have h₂ := (hsplit (t • Pi.single (Fin.last k) (1 : ℂ))).2
    rw [hy, map_zero] at h₁
    rw [hl] at h₂
    rw [polyFun, baseOf_add, fibOf_add, h₁, h₂, zero_add, add_comm]
  have hGF : (GF : MvPowerSeries (Fin (k + 1)) ℂ).IsGeneralIn (Fin.last k) := by
    intro h0
    have hax := hPG.eventually_axis_eq_zero (Fin.last k) h0
    refine BPointData.not_eventually_eval_eq_zero (hQ.map
      (Pi.evalRingHom (fun _ ↦ ℂ) (baseOf z))).ne_zero (fibOf z) ?_
    filter_upwards [hax] with t ht
    rw [haxis] at ht
    exact ht
  -- transport to the coordinates `ULift (Fin (k + 1))`
  refine ⟨LocalOkaRing.congr e GF, LocalOkaRing.congr e (incl H₀), ?_, ?_, ?_⟩
  · refine (congr_represents (φ := e) hPG).congr (Eventually.of_forall fun w ↦ ?_)
    change polyFun Q (e (e.symm w) + z) = polyFun Q (w + z)
    rw [ContinuousLinearEquiv.apply_symm_apply]
  · refine (congr_represents (φ := e) hHF).congr (Eventually.of_forall fun w ↦ ?_)
    change h (baseOf (e (e.symm w) + z)) = h (baseOf (w + z))
    rw [ContinuousLinearEquiv.apply_symm_apply]
  · have hne : LocalOkaRing.congr e GF ≠ 0 := by
      rw [ne_eq, map_eq_zero_iff _ (LocalOkaRing.congr e).injective]
      exact ne_zero_of_isGeneralIn hGF
    refine isWeaklyRegular_pair (fun a b hab ↦ mul_left_cancel₀ hne hab) fun y hy ↦ ?_
    have h₁ : GF ∣ incl H₀ * (LocalOkaRing.congr e).symm y := by
      have := map_dvd (LocalOkaRing.congr e).symm hy
      rwa [map_mul, AlgEquiv.symm_apply_apply, AlgEquiv.symm_apply_apply] at this
    have h₂ := map_dvd (LocalOkaRing.congr e) (dvd_of_dvd_incl_mul_of_isGeneralIn hGF hH₀ h₁)
    rwa [AlgEquiv.apply_symm_apply] at h₂

/-- **The regular pair `(Q(y)(v), h(y))`** on an open `G` of `ℂ^{k+1}` lying over `U`. -/
def polyPair {Q : Polynomial (Cm.{u} k → ℂ)} (hQ : Q.Monic) {U : Set (Cm.{u} k)} (hU : IsOpen U)
    (hQd : ∀ j, DifferentiableOn ℂ (Q.coeff j) U) {h : Cm.{u} k → ℂ}
    (hh : DifferentiableOn ℂ h U) (hh0 : ∀ z ∈ U, ¬ h =ᶠ[𝓝 z] 0) {G : Set (Cm.{u} (k + 1))}
    (hGU : ∀ b ∈ G, baseOf b ∈ U) : RegularPairFamily G where
  k := 1
  g _ := polyFun Q
  h _ := fun b ↦ h (baseOf b)
  continuousOn_g _ := (differentiableOn_polyFun hQd).continuousOn.mono fun b hb ↦ hGU b hb
  continuousOn_h _ := (hh.comp differentiable_baseOf.differentiableOn fun _ h ↦ h).continuousOn.mono
    fun b hb ↦ hGU b hb
  isWeaklyRegular _ z hz _ _ := isWeaklyRegular_polyPair hQ hU hQd hh hh0 (hGU z hz)

lemma polyPair_zeroSet {Q : Polynomial (Cm.{u} k → ℂ)} (hQ : Q.Monic) {U : Set (Cm.{u} k)}
    (hU : IsOpen U) (hQd : ∀ j, DifferentiableOn ℂ (Q.coeff j) U) {h : Cm.{u} k → ℂ}
    (hh : DifferentiableOn ℂ h U) (hh0 : ∀ z ∈ U, ¬ h =ᶠ[𝓝 z] 0) {G : Set (Cm.{u} (k + 1))}
    (hGU : ∀ b ∈ G, baseOf b ∈ U) :
    (polyPair hQ hU hQd hh hh0 hGU).zeroSet = {b | polyFun Q b = 0 ∧ h (baseOf b) = 0} := by
  ext b
  simp [RegularPairFamily.zeroSet, RegularPairFamily.zeroSetOf, polyPair]

end

end ComplexAnalytic.BoundedSections
