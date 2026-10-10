/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pi

/-!
# The derivative of a polynomial function is given by its formal partial derivatives

For `f : MvPolynomial σ 𝕜` with `σ` finite, the function `x ↦ MvPolynomial.eval x f` on `σ → 𝕜`
has Fréchet derivative `v ↦ ∑ i, eval x (pderiv i f) * v i` at every point `x`. Mathlib knows
that this function is analytic (`AnalyticOnNhd.eval_mvPolynomial`) but, at `v4.32.0`, does not
identify its derivative with `MvPolynomial.pderiv`; that identification is what is here.

## Main results

- `MvPolynomial.hasFDerivAt_eval`: the derivative of `x ↦ eval x f` at `x` is
  `∑ i, eval x (pderiv i f) • ContinuousLinearMap.proj i`.
- `MvPolynomial.contDiff_eval`: `x ↦ eval x f` is `C^n` for every `n` (from analyticity).
-/

open ContinuousLinearMap

namespace MvPolynomial

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {σ : Type*} [Fintype σ]

/-- **The derivative of a polynomial function is given by the formal partial derivatives.** -/
theorem hasFDerivAt_eval (f : MvPolynomial σ 𝕜) (x : σ → 𝕜) :
    HasFDerivAt (fun y ↦ eval y f) (∑ i, eval x (pderiv i f) • proj (R := 𝕜) (φ := fun _ ↦ 𝕜) i)
      x := by
  classical
  induction f using MvPolynomial.induction_on with
  | C a =>
    simp only [eval_C]
    exact (hasFDerivAt_const (𝕜 := 𝕜) (E := σ → 𝕜) a x).congr_fderiv
      (ContinuousLinearMap.ext fun v ↦ by simp)
  | add p q hp hq =>
    simp only [map_add]
    exact (hp.add hq).congr_fderiv
      (ContinuousLinearMap.ext fun v ↦ by simp [add_mul, Finset.sum_add_distrib])
  | mul_X p n hp =>
    simp only [eval_mul, eval_X]
    refine (hp.mul (hasFDerivAt_apply n x)).congr_fderiv ?_
    refine ContinuousLinearMap.ext fun v ↦ ?_
    simp [Derivation.leibniz, pderiv_X, Pi.single_apply, apply_ite (eval x), mul_add,
      Finset.sum_add_distrib, Finset.mul_sum, mul_comm, mul_left_comm]

/-- A polynomial function is `C^n` for every `n`. -/
theorem contDiff_eval [CompleteSpace 𝕜] (f : MvPolynomial σ 𝕜) {n : WithTop ℕ∞} :
    ContDiff 𝕜 n fun x : σ → 𝕜 ↦ eval x f :=
  (AnalyticOnNhd.eval_mvPolynomial f).contDiff

end MvPolynomial
