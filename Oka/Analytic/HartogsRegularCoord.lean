/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytic.HartogsRegularFamily
import Oka.Analytification.GAGA.ParametricIntervalIntegral
import Oka.ChangeOfCoordinates
import Oka.Regular

/-!
# Regular pairs `(xᵢ, h)`

Let `h` be holomorphic near a point `z` of the hyperplane `xᵢ = 0` of `ℂ^ι`. If `h` does not vanish
identically on the hyperplane near `z`, then the germs of `xᵢ` and `h` at `z` form a regular
sequence (`LocalOkaRing.isWeaklyRegular_coord`): `xᵢ` is a nonzerodivisor, and modulo `xᵢ` the germ
of `h` is its restriction to the hyperplane (Weierstrass division by a coordinate,
`LocalOkaRing.exists_eq_mul_lastVar_add_incl`), which is a nonzero element of a domain.

This gives families of regular pairs `(xᵢ, h)` on opens of `ℂ^ι`
(`RegularPairFamily.ofCoord`), across whose common zero sets holomorphic functions extend.

## Main results

- `RingTheory.Sequence.isWeaklyRegular_pair`: a pair `[g, h]` is weakly regular if `g` is a
  nonzerodivisor and `h` is a nonzerodivisor modulo `g`.
- `LocalOkaRing.isWeaklyRegular_coord`: the regularity of `(xᵢ, h)`.
- `RegularPairFamily.ofCoord`: the family consisting of the pair `(xᵢ, h)`.
-/

open Set Filter Topology RingTheory.Sequence Pointwise

/-- A pair `[g, h]` in a ring is weakly regular if `g` is a nonzerodivisor and `h` is a
nonzerodivisor modulo `g`. -/
theorem RingTheory.Sequence.isWeaklyRegular_pair {R : Type*} [CommRing R] {g h : R}
    (hg : IsSMulRegular R g) (hh : ∀ y, g ∣ h * y → g ∣ y) : IsWeaklyRegular R [g, h] := by
  rw [isWeaklyRegular_cons_iff, isWeaklyRegular_cons_iff]
  refine ⟨hg, fun x y hxy ↦ ?_, IsWeaklyRegular.nil _ _⟩
  have hmem : ∀ z : R, Submodule.Quotient.mk (p := g • (⊤ : Submodule R R)) z = 0 ↔ g ∣ z :=
    fun z ↦ by
      rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_pointwise_iff_exists]
      simp [dvd_def, eq_comm]
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  have hxy' : Submodule.Quotient.mk (p := g • (⊤ : Submodule R R)) (h * (x - y)) = 0 := by
    rw [mul_sub, Submodule.Quotient.mk_sub, sub_eq_zero]
    exact hxy
  rw [← sub_eq_zero, ← Submodule.Quotient.mk_sub, hmem]
  exact hh _ ((hmem _).1 hxy')

namespace LocalOkaRing

variable {m : ℕ}

/-- **Division modulo the last coordinate.** If the germ `H` represents a function `h` which does
not vanish identically on the hyperplane `x_last = 0` near the origin, then `H` is a nonzerodivisor
modulo the last coordinate. -/
theorem lastVar_dvd_of_dvd_mul {H : LocalOkaRing (Fin (m + 1))}
    {h : (Fin (m + 1) → ℂ) → ℂ} (hH : (H : MvPowerSeries (Fin (m + 1)) ℂ).Represents h)
    (hne : ¬ ∀ᶠ y in 𝓝 (0 : Fin m → ℂ), h (Fin.snoc y 0) = 0) {a : LocalOkaRing (Fin (m + 1))}
    (ha : lastVar ∣ H * a) : lastVar ∣ a := by
  obtain ⟨p, c, rfl⟩ := exists_eq_mul_lastVar_add_incl H
  obtain ⟨q, a₀, rfl⟩ := exists_eq_mul_lastVar_add_incl a
  have hmem : incl (c * a₀) ∈ Ideal.span {(lastVar : LocalOkaRing (Fin (m + 1)))} := by
    rw [Ideal.mem_span_singleton]
    have : incl (c * a₀) = (p * lastVar + incl c) * (q * lastVar + incl a₀) -
        lastVar * (p * (q * lastVar + incl a₀) + q * incl c) := by
      rw [map_mul]
      ring
    rw [this]
    exact dvd_sub ha (dvd_mul_right _ _)
  rcases mul_eq_zero.1 (incl_eq_zero_of_mem_span_lastVar hmem) with hc | ha₀
  · refine absurd ?_ hne
    subst hc
    rw [map_zero, add_zero] at hH
    have hrep := MvPowerSeries.Represents.mul p.2 (MvPowerSeries.locallyConvergent_X _)
      p.2.represents_eval (MvPowerSeries.represents_X (Fin.last m))
    have heq := hH.eventuallyEq hrep
    have ht : Tendsto (fun y : Fin m → ℂ ↦ (Fin.snoc y 0 : Fin (m + 1) → ℂ)) (𝓝 0) (𝓝 0) := by
      have hc : Continuous fun y : Fin m → ℂ ↦ (Fin.snoc y 0 : Fin (m + 1) → ℂ) :=
        continuous_pi fun j ↦ by
          refine Fin.lastCases ?_ (fun j ↦ ?_) j
          · simpa using continuous_const
          · simpa using continuous_apply j
      have h0 : (Fin.snoc (0 : Fin m → ℂ) 0 : Fin (m + 1) → ℂ) = 0 :=
        funext fun j ↦ Fin.lastCases (by simp) (fun j ↦ by simp) j
      simpa [h0] using hc.tendsto 0
    filter_upwards [ht.eventually heq] with y hy
    rw [hy]
    simp
  · subst ha₀
    rw [map_zero, add_zero]
    exact dvd_mul_left _ _

variable {ι : Type*} [Finite ι]

/-- **`(xᵢ, h)` is a regular sequence** in the ring of germs at the origin if `h` represents a
function which does not vanish identically on the hyperplane `xᵢ = 0` near the origin. -/
theorem isWeaklyRegular_coord {i : ι} {H : LocalOkaRing ι} {h : (ι → ℂ) → ℂ}
    (hH : (H : MvPowerSeries ι ℂ).Represents h)
    (hne : ¬ ∀ᶠ x in 𝓝 (0 : ι → ℂ), x i = 0 → h x = 0) :
    IsWeaklyRegular (LocalOkaRing ι) [coord i, H] := by
  classical
  have := Fintype.ofFinite ι
  obtain ⟨m, hm⟩ : ∃ m, Fintype.card ι = m + 1 :=
    Nat.exists_eq_succ_of_ne_zero (Fintype.card_pos_iff.2 ⟨i⟩).ne'
  set e₀ : ι ≃ Fin (m + 1) := Fintype.equivFinOfCardEq hm
  set e : ι ≃ Fin (m + 1) := e₀.trans (Equiv.swap (e₀ i) (Fin.last m))
  have hei : e i = Fin.last m := by simp [e]
  set φ : (ι → ℂ) ≃L[ℂ] (Fin (m + 1) → ℂ) :=
    (LinearEquiv.funCongrLeft ℂ ℂ e.symm).toContinuousLinearEquiv
  have hφ (x : ι → ℂ) (j : Fin (m + 1)) : φ x j = x (e.symm j) := rfl
  have hφs (v : Fin (m + 1) → ℂ) (k : ι) : φ.symm v k = v (e k) := by
    calc φ.symm v k = φ (φ.symm v) (e k) := by rw [hφ, Equiv.symm_apply_apply]
      _ = v (e k) := by rw [φ.apply_symm_apply]
  set E := congr φ
  have hEc : E (coord i) = lastVar := by
    refine congr_eq_of_represents (MvPowerSeries.represents_X i) ?_
    refine (MvPowerSeries.represents_X (Fin.last m)).congr (Eventually.of_forall fun v ↦ ?_)
    simp only [Function.comp_apply, hφs, hei]
  have hEH := congr_represents (φ := φ) hH
  have hne' : ¬ ∀ᶠ y in 𝓝 (0 : Fin m → ℂ), (h ∘ φ.symm) (Fin.snoc y 0) = 0 := by
    refine fun hev ↦ hne ?_
    have ht : Tendsto (fun x : ι → ℂ ↦ Fin.init (φ x)) (𝓝 0) (𝓝 0) := by
      have hc : Continuous fun x : ι → ℂ ↦ Fin.init (φ x) :=
        continuous_pi fun j ↦ (continuous_apply _).comp φ.continuous
      simpa using hc.tendsto 0
    filter_upwards [ht.eventually hev] with x hx hxi
    have hx' : (Fin.snoc (Fin.init (φ x)) 0 : Fin (m + 1) → ℂ) = φ x := by
      conv_rhs => rw [← Fin.snoc_init_self (φ x)]
      rw [hφ, ← hei, Equiv.symm_apply_apply, hxi]
    rw [Function.comp_apply, hx', ContinuousLinearEquiv.symm_apply_apply] at hx
    exact hx
  refine isWeaklyRegular_pair (fun a b hab ↦ mul_left_cancel₀ (coord_ne_zero i) hab)
    fun y hy ↦ ?_
  have h₁ : lastVar ∣ E H * E y := by
    rw [← hEc, ← map_mul]
    exact map_dvd E hy
  have h₂ := lastVar_dvd_of_dvd_mul hEH hne' h₁
  rw [← hEc] at h₂
  simpa using map_dvd E.symm h₂

end LocalOkaRing

namespace RegularPairFamily

variable {ι : Type*} [Fintype ι]

/-- **The regular pair `(xᵢ, h)`** on an open `U ⊆ ℂ^ι`, for `h` holomorphic on `U` which does
not vanish identically on the hyperplane `xᵢ = 0` near any of its zeros there. -/
noncomputable def ofCoord {U : Set (ι → ℂ)} (hU : IsOpen U) (i : ι) {h : (ι → ℂ) → ℂ}
    (hh : DifferentiableOn ℂ h U)
    (hne : ∀ z ∈ U, z i = 0 → h z = 0 → ¬ ∀ᶠ x in 𝓝 z, x i = 0 → h x = 0) :
    RegularPairFamily U where
  k := 1
  g _ := fun x ↦ x i
  h _ := h
  continuousOn_g _ := (continuous_apply i).continuousOn
  continuousOn_h _ := hh.continuousOn
  isWeaklyRegular _ z hz hzi hhz := by
    have hA : AnalyticAt ℂ (fun w ↦ h (w + z)) 0 := by
      have := analyticAt_of_differentiableOn_of_finiteDimensional hU hh hz
      exact this.comp_of_eq (by fun_prop) (zero_add z)
    obtain ⟨P, hPc, hP⟩ := MvPowerSeries.exists_represents hA
    refine ⟨LocalOkaRing.coord i, ⟨P, hPc⟩, ?_, hP, ?_⟩
    · refine (MvPowerSeries.represents_X i).congr (Eventually.of_forall fun w ↦ ?_)
      change w i = (w + z) i
      rw [Pi.add_apply, hzi, add_zero]
    · refine LocalOkaRing.isWeaklyRegular_coord hP fun hev ↦ hne z hz hzi hhz ?_
      have ht : Tendsto (fun x : ι → ℂ ↦ x - z) (𝓝 z) (𝓝 0) := by
        simpa using (continuous_sub_right z).tendsto z
      filter_upwards [ht.eventually hev] with x hx hxi
      simpa [Pi.sub_apply, hxi, hzi] using hx (by simp [hxi, hzi])

lemma ofCoord_zeroSet {U : Set (ι → ℂ)} (hU : IsOpen U) (i : ι) {h : (ι → ℂ) → ℂ}
    (hh : DifferentiableOn ℂ h U)
    (hne : ∀ z ∈ U, z i = 0 → h z = 0 → ¬ ∀ᶠ x in 𝓝 z, x i = 0 → h x = 0) :
    (ofCoord hU i hh hne).zeroSet = {z | z i = 0 ∧ h z = 0} := by
  ext z
  simp [zeroSet, zeroSetOf, ofCoord]

end RegularPairFamily
