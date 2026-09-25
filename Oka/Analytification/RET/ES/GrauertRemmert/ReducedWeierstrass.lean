/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.FieldTheory.Perfect
import Mathlib.Order.Filter.Germ.Basic
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.Radical.Basic
import Oka.UFD
import Oka.Analytification.RET.ES.GrauertRemmert.SimpleRoot

/-!
# Reduced Weierstrass polynomials

Let `f` be holomorphic near the origin of `ℂ^{m+1}` with `f(0) = 0`, not vanishing identically
near `0`. After a linear change of coordinates, the zero set of `f` near `0` is the zero set of a
monic polynomial `P` in the last coordinate, whose coefficients are holomorphic functions of the
other coordinates vanishing at `0` (a Weierstrass polynomial), such that the resultant
`δ = Res(P, ∂P/∂w)` does not vanish identically near `0`
(`ComplexAnalytic.exists_reducedWeierstrass_fin`). Where `δ ≠ 0`, `P` is separable
(`ComplexAnalytic.separable_evalPoly_of_discrFun_ne_zero`).

## Proof

The germ `F` of `f` is replaced by its radical `F_red` in the factorial ring of germs, which has
the same zero set. Weierstrass preparation writes `F_red`, after a change of coordinates, as a
unit times a Weierstrass polynomial `g`, which is squarefree since `F_red` is. By Gauss's lemma
`g` stays squarefree over the field of fractions, where it is separable
(`ComplexAnalytic.resultant_derivative_ne_zero`). The germs of the sums of convergent power series
form a ring homomorphism into the germs of functions (`LocalOkaRing.evalGerm`), which transports
these algebraic facts to the functions.
-/

open Filter Topology Polynomial Metric

namespace LocalOkaRing

noncomputable section

variable {ι : Type*} [Finite ι]

/-- The germ at the origin of the sum of a locally convergent power series. -/
def evalGerm : LocalOkaRing ι →+* Germ (𝓝 (0 : ι → ℂ)) ℂ where
  toFun P := (((P : MvPowerSeries ι ℂ).eval : (ι → ℂ) → ℂ) : Germ (𝓝 (0 : ι → ℂ)) ℂ)
  map_one' := Germ.coe_eq.2 (Eventually.of_forall fun x ↦ MvPowerSeries.eval_one x)
  map_mul' P Q := by
    haveI := Fintype.ofFinite ι
    exact Germ.coe_eq.2 ((P * Q).2.represents_eval.eventuallyEq
    (MvPowerSeries.Represents.mul P.2 Q.2 P.2.represents_eval Q.2.represents_eval))
  map_zero' := Germ.coe_eq.2 (Eventually.of_forall fun x ↦ MvPowerSeries.eval_of_zero x)
  map_add' P Q := Germ.coe_eq.2 ((P + Q).2.represents_eval.eventuallyEq
    (P.2.represents_eval.add Q.2.represents_eval))

omit [Finite ι] in
lemma evalGerm_apply (P : LocalOkaRing ι) :
    evalGerm P = (((P : MvPowerSeries ι ℂ).eval : (ι → ℂ) → ℂ) : Germ (𝓝 (0 : ι → ℂ)) ℂ) :=
  rfl

omit [Finite ι] in
lemma evalGerm_eq_iff {P : LocalOkaRing ι} {f : (ι → ℂ) → ℂ} :
    evalGerm P = (f : Germ (𝓝 (0 : ι → ℂ)) ℂ) ↔ (P : MvPowerSeries ι ℂ).Represents f := by
  rw [evalGerm_apply, Germ.coe_eq]
  exact ⟨fun h ↦ P.2.represents_eval.congr h, fun h ↦ P.2.represents_eval.eventuallyEq h⟩

lemma evalGerm_injective : Function.Injective (evalGerm (ι := ι)) := fun P Q h ↦ by
  rw [evalGerm_apply Q, evalGerm_eq_iff] at h
  exact Subtype.ext (h.unique Q.2.represents_eval)

end

end LocalOkaRing

namespace ComplexAnalytic

noncomputable section

/-! ### Squarefree monic polynomials over a factorial domain -/

section Algebra

variable {R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]

/-- **A squarefree monic polynomial over a factorial domain stays squarefree over the field of
fractions** (Gauss's lemma). -/
lemma squarefree_map_fractionRing {g : R[X]} (hg : g.Monic) (hsq : Squarefree g) :
    Squarefree (g.map (algebraMap R (FractionRing R))) := by
  set K := FractionRing R
  intro d hd
  have hne : g.map (algebraMap R K) ≠ 0 := (hg.map _).ne_zero
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact hne (zero_dvd_iff.1 (by simpa using hd))
  set d' := d * C d.leadingCoeff⁻¹
  have hlc : d.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hd0
  have hd'm : d'.Monic := monic_mul_leadingCoeff_inv hd0
  have hassoc : Associated d' d :=
    (associated_mul_isUnit_left_iff (isUnit_C.2 (inv_ne_zero hlc).isUnit)).2 (Associated.refl d)
  have hd'd' : d' * d' ∣ g.map (algebraMap R K) :=
    (hassoc.mul_mul hassoc).dvd.trans hd
  obtain ⟨d₀, hd₀⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd K hg
    ((dvd_mul_right d' d').trans hd'd')
  rw [hd'm.leadingCoeff, C_1, mul_one] at hd₀
  have hd₀m : d₀.Monic := monic_of_injective (IsFractionRing.injective R K) (hd₀ ▸ hd'm)
  have hdvd : d₀ * d₀ ∣ g := by
    refine hg.dvd_of_fraction_map_dvd_fraction_map (K := K) (hd₀m.mul hd₀m) ?_
    rwa [Polynomial.map_mul, hd₀]
  have hd₀1 : d₀ = 1 := hd₀m.isUnit_iff.1 (hsq d₀ hdvd)
  rw [hd₀1, Polynomial.map_one] at hd₀
  exact hassoc.isUnit_iff.1 (hd₀ ▸ isUnit_one)

variable [Algebra ℂ R]

/-- **The resultant of a squarefree monic polynomial of positive degree and its derivative does
not vanish**, over a factorial domain containing `ℂ`. -/
lemma resultant_derivative_ne_zero {g : R[X]} (hg : g.Monic) (hsq : Squarefree g) :
    resultant g (derivative g) g.natDegree (g.natDegree - 1) ≠ 0 := by
  set K := FractionRing R
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℂ K).injective
  set gK := g.map (algebraMap R K)
  have hsep : gK.Separable :=
    PerfectField.separable_iff_squarefree.2 (squarefree_map_fractionRing hg hsq)
  have hdeg : gK.natDegree = g.natDegree := hg.natDegree_map _
  have h := resultant_ne_zero gK (derivative gK) hsep
  rw [natDegree_derivative, hdeg, derivative_map, resultant_map_map] at h
  exact fun h0 ↦ h (by rw [h0, map_zero])

end Algebra

/-! ### Separability where the resultant does not vanish -/

section Separable

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The resultant of `P` and `∂P/∂w`, as a function of the parameters. -/
def discrFun (P : Polynomial (E → ℂ)) : E → ℂ :=
  resultant P (derivative P) P.natDegree (P.natDegree - 1)

omit [NormedAddCommGroup E] [NormedSpace ℂ E] in
/-- **`P(y)` is separable where `Res(P, ∂P/∂w)` does not vanish.** -/
lemma separable_evalPoly_of_discrFun_ne_zero {P : Polynomial (E → ℂ)} (hP : 0 < P.natDegree)
    {y : E} (hy : discrFun P y ≠ 0) : (evalPoly P y).Separable := by
  obtain ⟨p, q, -, -, hpq⟩ := exists_mul_add_mul_eq_C_resultant P (derivative P) le_rfl
    (natDegree_derivative_le P) (Or.inl hP.ne')
  have h := congrArg (Polynomial.map (Pi.evalRingHom (fun _ ↦ ℂ) y)) hpq
  rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C,
    ← derivative_map] at h
  refine ⟨C (discrFun P y)⁻¹ * p.map (Pi.evalRingHom (fun _ ↦ ℂ) y),
    C (discrFun P y)⁻¹ * q.map (Pi.evalRingHom (fun _ ↦ ℂ) y), ?_⟩
  have h' : evalPoly P y * p.map (Pi.evalRingHom (fun _ ↦ ℂ) y) +
      derivative (evalPoly P y) * q.map (Pi.evalRingHom (fun _ ↦ ℂ) y) = C (discrFun P y) := h
  calc C (discrFun P y)⁻¹ * p.map (Pi.evalRingHom (fun _ ↦ ℂ) y) * evalPoly P y +
        C (discrFun P y)⁻¹ * q.map (Pi.evalRingHom (fun _ ↦ ℂ) y) * derivative (evalPoly P y)
      = C (discrFun P y)⁻¹ * C (discrFun P y) := by rw [← h']; ring
    _ = 1 := by rw [← C_mul, inv_mul_cancel₀ hy, C_1]

end Separable


/-! ### The reduced Weierstrass polynomial -/

section Main

open LocalOkaRing

variable {m : ℕ}

/-- The sum of a locally convergent power series is holomorphic near the origin. -/
lemma eventually_differentiableAt_eval {ι : Type*} [Finite ι] (P : LocalOkaRing ι) :
    ∀ᶠ y in 𝓝 (0 : ι → ℂ), DifferentiableAt ℂ (P : MvPowerSeries ι ℂ).eval y :=
  haveI := Fintype.ofFinite ι
  P.2.analyticAt.eventually_analyticAt.mono fun _ h ↦ h.differentiableAt

/-- **The reduced Weierstrass polynomial**, in the coordinates `Fin (m + 1) → ℂ`: after a linear
change of coordinates `L`, the zero set of `f` near `0` is the zero set of a Weierstrass polynomial
`P` in the last coordinate whose discriminant does not vanish identically near `0`. -/
theorem exists_reducedWeierstrass_fin {f : (Fin (m + 1) → ℂ) → ℂ} (hf : AnalyticAt ℂ f 0)
    (hf0 : f 0 = 0) (hne : ¬ f =ᶠ[𝓝 0] 0) :
    ∃ (L : (Fin (m + 1) → ℂ) ≃L[ℂ] (Fin (m + 1) → ℂ)) (P : Polynomial ((Fin m → ℂ) → ℂ)),
      P.Monic ∧ 0 < P.natDegree ∧ (∀ k, ∀ᶠ y in 𝓝 0, DifferentiableAt ℂ (P.coeff k) y) ∧
      (∀ k < P.natDegree, P.coeff k 0 = 0) ∧
      (∀ᶠ x in 𝓝 0, f (L x) = 0 ↔ (evalPoly P (Fin.init x)).eval (x (Fin.last m)) = 0) ∧
      ¬ discrFun P =ᶠ[𝓝 0] 0 := by
  classical
  letI : NormalizationMonoid (LocalOkaRing (Fin (m + 1))) :=
    UniqueFactorizationMonoid.strongNormalizationMonoid.toNormalizationMonoid
  obtain ⟨Pf, hPfc, hPf⟩ := MvPowerSeries.exists_represents hf
  set F : LocalOkaRing (Fin (m + 1)) := ⟨Pf, hPfc⟩
  have hF : evalGerm F = (f : Germ (𝓝 (0 : Fin (m + 1) → ℂ)) ℂ) := evalGerm_eq_iff.2 hPf
  have hF0 : F ≠ 0 := fun h ↦ hne (by
    rw [h, map_zero] at hF
    exact Germ.coe_eq.1 hF.symm)
  have hFu : ¬ IsUnit F := by
    rw [LocalOkaRing.isUnit_iff, not_not, constantCoeff_apply]
    exact (hPf.apply_zero).symm.trans hf0
  obtain ⟨A, hA⟩ := UniqueFactorizationMonoid.radical_dvd_self (a := F)
  obtain ⟨k, B, hB⟩ := UniqueFactorizationMonoid.exists_dvd_radical_self_pow hF0
  set Fr := UniqueFactorizationMonoid.radical F with hFr
  have hFr0 : Fr ≠ 0 := by
    intro h
    rw [h, zero_mul] at hA
    exact hF0 hA
  obtain ⟨φ, u, hu, g, hg, hfr⟩ := exists_congr_localweierstrass_preparation hFr0
  have hgm : g.Monic := monic_of_isLocalWeierstrass hg
  -- `g` is squarefree
  have hsqF : Squarefree (congr φ Fr) := fun x hx ↦ by
    have h := UniqueFactorizationMonoid.squarefree_radical (a := F) ((congr φ).symm x) (by
      obtain ⟨y, hy⟩ := hx
      refine ⟨(congr φ).symm y, ?_⟩
      rw [← map_mul, ← map_mul, ← hy, AlgEquiv.symm_apply_apply])
    simpa using h.map (congr φ)
  have hsq : Squarefree g := fun a ⟨b, hb⟩ ↦ by
    refine isUnit_of_isUnit_fromPolynomial hg (p := a) (q := a * b) (by rw [hb, mul_assoc])
      (hsqF _ ⟨fromPolynomial b * u, ?_⟩)
    rw [hfr, hb, map_mul, map_mul]
    ring
  -- `g` has positive degree
  have hdeg : 0 < g.natDegree := by
    by_contra h0
    have hg1 : g = 1 := hgm.natDegree_eq_zero.1 (by omega)
    have h1 : IsUnit (congr φ Fr) := by rw [hfr, hg1, map_one, one_mul]; exact hu
    have h2 : IsUnit Fr := by simpa using h1.map (congr φ).symm
    exact hFu (isUnit_of_dvd_unit ⟨B, hB⟩ (h2.pow k))
  -- the coefficient functions
  set d := g.natDegree
  set c : ℕ → (Fin m → ℂ) → ℂ := fun i ↦
    ((g.coeff i : LocalOkaRing (Fin m)) : MvPowerSeries (Fin m) ℂ).eval
  set P : Polynomial ((Fin m → ℂ) → ℂ) := weierstrassOfCoeffs (fun j : Fin d ↦ c j)
  have hPm : P.Monic := weierstrassOfCoeffs_monic _
  have hPd : P.natDegree = d := weierstrassOfCoeffs_natDegree _
  have hPc : ∀ i, P.coeff i = c i := fun i ↦ by
    rcases lt_trichotomy i d with hi | rfl | hi
    · exact weierstrassOfCoeffs_coeff_of_lt _ hi
    · rw [weierstrassOfCoeffs_coeff_self]
      funext y
      simp only [c, show g.coeff d = 1 from hgm.coeff_natDegree, OneMemClass.coe_one,
        Pi.one_apply, MvPowerSeries.eval_one]
    · rw [weierstrassOfCoeffs_coeff_of_gt _ hi]
      funext y
      simp only [c, coeff_eq_zero_of_natDegree_lt hi, ZeroMemClass.coe_zero, Pi.zero_apply,
        MvPowerSeries.eval_of_zero]
  have hmap : P.map (Germ.coeRingHom (𝓝 (0 : Fin m → ℂ))) = g.map evalGerm := by
    ext i
    rw [coeff_map, coeff_map, hPc]
    rfl
  refine ⟨φ.symm, P, hPm, hPd ▸ hdeg, fun i ↦ ?_, fun i hi ↦ ?_, ?_, ?_⟩
  · rw [hPc]
    exact eventually_differentiableAt_eval _
  · rw [hPc]
    have hi' : (i : WithBot ℕ) <
        (g.map (Subring.subtype (localOkaSubring _).toSubring)).degree := by
      rw [degree_map_eq_of_injective (f := (localOkaSubring (Fin m)).toSubring.subtype)
        Subtype.val_injective, degree_eq_natDegree (Polynomial.Monic.ne_zero hgm)]
      rw [hPd] at hi
      exact_mod_cast hi
    have := hg.apply_zero i hi'
    rw [coeff_map] at this
    simp only [c, MvPowerSeries.eval_zero]
    exact this
  · -- the zero sets of `f` and of its radical agree
    set fr := ((Fr : LocalOkaRing (Fin (m + 1))) : MvPowerSeries (Fin (m + 1)) ℂ).eval
    have hfA : f =ᶠ[𝓝 0] fr * ((A : LocalOkaRing (Fin (m + 1))) :
        MvPowerSeries (Fin (m + 1)) ℂ).eval := by
      have := congrArg evalGerm hA
      rw [hF, map_mul] at this
      exact Germ.coe_eq.1 this
    have hfB : fr ^ k =ᶠ[𝓝 0] f * ((B : LocalOkaRing (Fin (m + 1))) :
        MvPowerSeries (Fin (m + 1)) ℂ).eval := by
      have := congrArg evalGerm hB
      rw [map_pow, map_mul, hF] at this
      exact Germ.coe_eq.1 this
    have hz : ∀ᶠ y in 𝓝 (0 : Fin (m + 1) → ℂ), f y = 0 ↔ fr y = 0 := by
      filter_upwards [hfA, hfB] with y h₁ h₂
      refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
      · simp only [Pi.pow_apply, Pi.mul_apply, h, zero_mul] at h₂
        exact pow_eq_zero_iff'.1 h₂ |>.1
      · simp only [Pi.mul_apply, h, zero_mul] at h₁
        exact h₁
    -- the radical in the new coordinates
    have hcongr : evalGerm (congr φ Fr) =
        ((fr ∘ (φ.symm : (Fin (m + 1) → ℂ) → (Fin (m + 1) → ℂ)) : _ → ℂ) : Germ _ ℂ) :=
      evalGerm_eq_iff.2 (congr_represents Fr.2.represents_eval)
    have hpoly : evalGerm (fromPolynomial g) =
        ((fun x : Fin (m + 1) → ℂ ↦ (evalPoly P (Fin.init x)).eval (x (Fin.last m)) : _ → ℂ) :
          Germ _ ℂ) := by
      rw [evalGerm_apply, Germ.coe_eq]
      have hinit : Tendsto (Fin.init : (Fin (m + 1) → ℂ) → (Fin m → ℂ)) (𝓝 0) (𝓝 0) := by
        have hc : Continuous (Fin.init : (Fin (m + 1) → ℂ) → (Fin m → ℂ)) :=
          continuous_pi fun i ↦ continuous_apply i.castSucc
        simpa using hc.tendsto 0
      filter_upwards [hinit.eventually (eventually_summableAt_coeffs g)] with x hx
      rw [eval_fromPolynomial g x fun i ↦ ?_]
      · rw [eval_eq_sum_range' (n := d + 1) (Nat.lt_succ_of_le
          ((natDegree_evalPoly_le P _).trans hPd.le))]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [coeff_evalPoly, hPc]
        rfl
      · by_cases hi : i ∈ Finset.range (g.natDegree + 1)
        · exact hx i hi
        · rw [coeff_eq_zero_of_natDegree_lt (by simpa using hi)]
          exact MvPowerSeries.summableAt_zero _
    have hu0 : ∀ᶠ x in 𝓝 (0 : Fin (m + 1) → ℂ),
        ((u : LocalOkaRing (Fin (m + 1))) : MvPowerSeries (Fin (m + 1)) ℂ).eval x ≠ 0 := by
      refine u.2.analyticAt.continuousAt.eventually_ne ?_
      rw [MvPowerSeries.eval_zero]
      exact LocalOkaRing.isUnit_iff.1 hu
    have hprod := congrArg evalGerm hfr
    rw [hcongr, map_mul, hpoly, evalGerm_apply u] at hprod
    have hφ : Tendsto (φ.symm : (Fin (m + 1) → ℂ) → (Fin (m + 1) → ℂ)) (𝓝 0) (𝓝 0) := by
      simpa using φ.symm.continuous.tendsto 0
    filter_upwards [hφ.eventually hz, Germ.coe_eq.1 hprod, hu0] with x h₁ h₂ h₃
    rw [h₁]
    change fr (φ.symm x) = (evalPoly P (Fin.init x)).eval (x (Fin.last m)) * _ at h₂
    rw [h₂, mul_eq_zero, or_iff_left h₃]
  · intro h
    have h1 : Germ.coeRingHom (𝓝 (0 : Fin m → ℂ)) (discrFun P) = 0 := Germ.coe_eq.2 h
    rw [discrFun, ← resultant_map_map, ← derivative_map, hmap, derivative_map, resultant_map_map,
      hPd] at h1
    exact resultant_derivative_ne_zero hgm hsq (evalGerm_injective (h1.trans (map_zero _).symm))

end Main

end

end ComplexAnalytic
