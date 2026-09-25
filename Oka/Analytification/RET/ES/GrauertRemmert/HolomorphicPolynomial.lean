/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.ES.GrauertRemmert.ReducedWeierstrass
import Oka.Nullstellensatz.CommonRoot

/-!
# Polynomials with holomorphic coefficients

Let `P` be a monic polynomial whose coefficients are functions on a complex normed space `E`. This
file collects operations on such polynomials used to put a hypersurface into Weierstrass form:

* the resultant `Res(P, ∂P/∂w)` is holomorphic where the coefficients are
  (`ComplexAnalytic.differentiableOn_discrFun`);
* rescaling the variable, `s⁻ᵈ P(s w)` (`ComplexAnalytic.scalePoly`), preserves separability
  (`ComplexAnalytic.separable_scalePoly`);
* changing the parameters along a map `φ` (`ComplexAnalytic.precompHom`);
* if the lower coefficients vanish at `c`, the roots of `P(y)` are small for `y` near `c`
  (`ComplexAnalytic.eventually_forall_isRoot_norm_lt`).
-/

open Filter Topology Polynomial Metric

namespace ComplexAnalytic

noncomputable section

section Holomorphic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-! ### Holomorphic coefficients -/

/-- The subring of the functions holomorphic on `G`. -/
def holSubring (G : Set E) : Subring (E → ℂ) where
  carrier := {h | DifferentiableOn ℂ h G}
  mul_mem' ha hb := DifferentiableOn.mul ha hb
  one_mem' := differentiableOn_const 1
  add_mem' ha hb := DifferentiableOn.add ha hb
  zero_mem' := differentiableOn_const 0
  neg_mem' ha := DifferentiableOn.neg ha

lemma mem_holSubring {G : Set E} {h : E → ℂ} : h ∈ holSubring G ↔ DifferentiableOn ℂ h G :=
  Iff.rfl

lemma exists_map_holSubring {G : Set E} {P : Polynomial (E → ℂ)}
    (hP : ∀ k, DifferentiableOn ℂ (P.coeff k) G) :
    ∃ P' : Polynomial (holSubring G), P'.map (holSubring G).subtype = P := by
  refine (mem_lifts P).1 ((lifts_iff_coeff_lifts P).2 fun k ↦ ⟨⟨P.coeff k, hP k⟩, rfl⟩)

/-- The resultant of `P` and `∂P/∂w` is holomorphic where the coefficients of `P` are. -/
lemma differentiableOn_discrFun {G : Set E} {P : Polynomial (E → ℂ)}
    (hP : ∀ k, DifferentiableOn ℂ (P.coeff k) G) : DifferentiableOn ℂ (discrFun P) G := by
  obtain ⟨P', rfl⟩ := exists_map_holSubring hP
  rw [discrFun, derivative_map, resultant_map_map]
  exact (resultant P' (derivative P') _ _).2

end Holomorphic

/-! ### Rescaling the variable -/

section Algebraic

variable {E : Type*}

/-- The monic polynomial `s⁻ᵈ P(s w)`, `d` the degree of `P`. -/
def scalePoly (P : Polynomial (E → ℂ)) (s : ℂ) : Polynomial (E → ℂ) :=
  weierstrassOfCoeffs fun j : Fin P.natDegree ↦
    P.coeff j * fun _ ↦ s ^ (j : ℕ) * s⁻¹ ^ P.natDegree

lemma monic_scalePoly (P : Polynomial (E → ℂ)) (s : ℂ) : (scalePoly P s).Monic :=
  weierstrassOfCoeffs_monic _

lemma natDegree_scalePoly [Nonempty E] (P : Polynomial (E → ℂ)) (s : ℂ) :
    (scalePoly P s).natDegree = P.natDegree :=
  weierstrassOfCoeffs_natDegree _

lemma differentiableOn_coeff_scalePoly [NormedAddCommGroup E] [NormedSpace ℂ E]
    {G : Set E} {P : Polynomial (E → ℂ)}
    (hP : ∀ k, DifferentiableOn ℂ (P.coeff k) G) (s : ℂ) (k : ℕ) :
    DifferentiableOn ℂ ((scalePoly P s).coeff k) G := by
  rcases lt_trichotomy k P.natDegree with hk | rfl | hk
  · rw [scalePoly, weierstrassOfCoeffs_coeff_of_lt _ hk]
    exact (hP k).mul (differentiableOn_const _)
  · rw [scalePoly, weierstrassOfCoeffs_coeff_self]
    exact differentiableOn_const 1
  · rw [scalePoly, weierstrassOfCoeffs_coeff_of_gt _ hk]
    exact differentiableOn_const 0

lemma eval_scalePoly {P : Polynomial (E → ℂ)} (hP : P.Monic) {s : ℂ} (hs : s ≠ 0) (y : E)
    (w : ℂ) : (evalPoly (scalePoly P s) y).eval w =
      s⁻¹ ^ P.natDegree * (evalPoly P y).eval (s * w) := by
  set d := P.natDegree
  rw [evalPoly, scalePoly, weierstrassOfCoeffs_map, weierstrassOfCoeffs, eval_add, eval_pow,
    eval_X, eval_finsetSum, eval_eq_sum_range' (n := d + 1)
      (Nat.lt_succ_of_le (natDegree_evalPoly_le P y)), Finset.sum_range_succ, coeff_evalPoly,
    hP.coeff_natDegree, Finset.sum_range, mul_add, Finset.mul_sum]
  have h1 : w ^ d = s⁻¹ ^ d * ((1 : E → ℂ) y * (s * w) ^ d) := by
    rw [Pi.one_apply, one_mul, mul_pow, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hs, one_pow,
      one_mul]
  rw [h1, add_comm]
  congr 1
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [eval_mul, eval_C, eval_pow, eval_X, Pi.evalRingHom_apply, Pi.mul_apply,
    coeff_evalPoly, mul_pow]
  ring

lemma evalPoly_scalePoly {P : Polynomial (E → ℂ)} (hP : P.Monic) {s : ℂ} (hs : s ≠ 0) (y : E) :
    evalPoly (scalePoly P s) y = C (s⁻¹ ^ P.natDegree) * (evalPoly P y).comp (C s * X) :=
  Polynomial.funext fun w ↦ by
    rw [eval_scalePoly hP hs, eval_mul, eval_C, eval_comp, eval_mul, eval_C, eval_X]

/-- **Rescaling the variable preserves separability.** -/
lemma separable_scalePoly {P : Polynomial (E → ℂ)} (hP : P.Monic) {s : ℂ} (hs : s ≠ 0) {y : E}
    (hsep : (evalPoly P y).Separable) : (evalPoly (scalePoly P s) y).Separable := by
  rw [evalPoly_scalePoly hP hs]
  set q := evalPoly P y
  set c := s⁻¹ ^ P.natDegree
  have hc : c ≠ 0 := pow_ne_zero _ (inv_ne_zero hs)
  obtain ⟨a, b, hab⟩ := hsep
  refine ⟨C c⁻¹ * a.comp (C s * X), C (c⁻¹ * s⁻¹) * b.comp (C s * X), ?_⟩
  rw [derivative_mul, derivative_C, zero_mul, zero_add, derivative_comp, derivative_mul,
    derivative_C, derivative_X, zero_mul, zero_add, mul_one]
  have h := congrArg (fun p ↦ p.comp (C s * X)) hab
  simp only [add_comp, mul_comp, one_comp] at h
  rw [← h]
  have hcs : C c⁻¹ * C c = 1 := by rw [← C_mul, inv_mul_cancel₀ hc, C_1]
  have hss : C (c⁻¹ * s⁻¹) * (C c * C s) = 1 := by
    rw [← C_mul, ← C_mul]
    field_simp
    rw [C_1]
  calc C c⁻¹ * a.comp (C s * X) * (C c * q.comp (C s * X)) +
        C (c⁻¹ * s⁻¹) * b.comp (C s * X) * (C c * (C s * (derivative q).comp (C s * X)))
      = (C c⁻¹ * C c) * (a.comp (C s * X) * q.comp (C s * X)) +
          (C (c⁻¹ * s⁻¹) * (C c * C s)) * (b.comp (C s * X) * (derivative q).comp (C s * X)) := by
        ring
    _ = _ := by rw [hcs, hss, one_mul, one_mul]

/-! ### Changing the parameters -/

variable {E' : Type*}

/-- Precomposition with `φ : E' → E`, as a ring homomorphism of functions. -/
def precompHom (φ : E' → E) : (E → ℂ) →+* (E' → ℂ) :=
  RingHom.pi fun y ↦ Pi.evalRingHom (fun _ ↦ ℂ) (φ y)

lemma precompHom_apply (φ : E' → E) (h : E → ℂ) : precompHom φ h = h ∘ φ :=
  rfl

lemma evalPoly_map_precompHom (φ : E' → E) (P : Polynomial (E → ℂ)) (y : E') :
    evalPoly (P.map (precompHom φ)) y = evalPoly P (φ y) := by
  rw [evalPoly, evalPoly, Polynomial.map_map]
  rfl

lemma coeff_map_precompHom (φ : E' → E) (P : Polynomial (E → ℂ)) (k : ℕ) :
    (P.map (precompHom φ)).coeff k = P.coeff k ∘ φ := by
  rw [coeff_map]
  rfl

end Algebraic

/-! ### Small roots -/

section Roots

variable {E : Type*} [TopologicalSpace E]


/-- **If the lower coefficients of a monic `P` vanish at `c`, the roots of `P(y)` are small for `y`
near `c`.** -/
lemma eventually_forall_isRoot_norm_lt {P : Polynomial (E → ℂ)} (hP : P.Monic) {c : E}
    (hc : ∀ k < P.natDegree, ContinuousAt (P.coeff k) c ∧ P.coeff k c = 0) {ε : ℝ}
    (hε : 0 < ε) : ∀ᶠ y in 𝓝 c, ∀ w, (evalPoly P y).IsRoot w → ‖w‖ < ε := by
  set d := P.natDegree
  have hcont : ContinuousAt (fun y ↦ ∑ i ∈ Finset.range d, ‖P.coeff i y‖ * ε ^ i) c :=
    tendsto_finsetSum _ fun i hi ↦
      ((hc i (Finset.mem_range.1 hi)).1.norm).mul continuousAt_const
  have h0 : (fun y ↦ ∑ i ∈ Finset.range d, ‖P.coeff i y‖ * ε ^ i) c = 0 :=
    Finset.sum_eq_zero fun i hi ↦ by rw [(hc i (Finset.mem_range.1 hi)).2, norm_zero, zero_mul]
  have hlt := hcont.eventually (gt_mem_nhds (show (fun y ↦ ∑ i ∈ Finset.range d,
    ‖P.coeff i y‖ * ε ^ i) c < ε ^ d by rw [h0]; positivity))
  filter_upwards [hlt] with y hy w hw
  have hdeg : (evalPoly P y).natDegree = d := hP.natDegree_map _
  refine Polynomial.norm_lt_of_isRoot (hP.map _) hε ?_ hw
  rw [hdeg]
  simpa [coeff_evalPoly] using hy

end Roots

end

end ComplexAnalytic
