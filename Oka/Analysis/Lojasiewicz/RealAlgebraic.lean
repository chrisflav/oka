/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Mathlib.Topology.Homeomorph.Lemmas
import Oka.Analysis.Calculus.MvPolynomialDeriv
import Oka.Analysis.Lojasiewicz.Retraction
import Oka.Topology.Homotopy.LocallyContractible

/-!
# Real algebraic sets are locally contractible, given the Łojasiewicz gradient inequality

`MvPolynomial.LojasiewiczGradient f` is the **Łojasiewicz gradient inequality** for a real
polynomial `f` at every zero `p` of `f`: there are `0 ≤ θ < 1` and `c > 0` with
`c * |f x| ^ θ ≤ ‖∇f x‖` near `p` (sup norm). It is a theorem for every real polynomial
(Łojasiewicz 1963), proved elsewhere (semialgebraic geometry); here it is a **hypothesis**.

Given it, the zero set of `f` is locally contractible
(`MvPolynomial.locallyContractibleSpace_zeroSet_of_lojasiewicz`). The proof applies
`Lojasiewicz.locallyContractibleSpace_zeroSet` (`Oka/Analysis/Lojasiewicz/Retraction.lean`) to
`F = f²`, which is nonnegative, has the same zero set, has gradient `2 f ∇f` (by
`MvPolynomial.hasFDerivAt_eval`), and satisfies the gradient inequality with exponent
`(1 + θ) / 2 < 1`: `‖2 f ∇f‖ ≥ 2 c |f| ^ (1 + θ) = 2 c (f²) ^ ((1 + θ) / 2)`.

## Main results

- `MvPolynomial.LojasiewiczGradient`: the hypothesis.
- `MvPolynomial.locallyContractibleSpace_zeroSet_of_lojasiewicz`: **the zero set of a real
  polynomial satisfying the gradient inequality is locally contractible.**
- `MvPolynomial.locallyContractibleSpace_zeroSet_finset_of_lojasiewicz`: the same for the common
  zero set of a finite family `s`, assuming the inequality for `∑ g ∈ s, g ^ 2`.
- `MvPolynomial.locallyContractibleSpace_zeroSet_of_fin`: the zero-set statement for polynomials in
  finitely many variables indexed by an arbitrary finite type follows from the one indexed by
  `Fin n`.
-/

open Set Filter Topology ContinuousLinearMap

namespace MvPolynomial

/-- **The Łojasiewicz gradient inequality** for a real polynomial `f` at each of its zeros: there
are `0 ≤ θ < 1` and `c > 0` such that `c * |f x| ^ θ ≤ ‖∇f x‖` for `x` near the zero (sup norm
on the gradient `∇f x = (∂f/∂xᵢ (x))ᵢ`). -/
def LojasiewiczGradient {n : ℕ} (f : MvPolynomial (Fin n) ℝ) : Prop :=
  ∀ p : Fin n → ℝ, MvPolynomial.eval p f = 0 →
    ∃ θ : ℝ, 0 ≤ θ ∧ θ < 1 ∧ ∃ c : ℝ, 0 < c ∧ ∀ᶠ x in nhds p,
      c * |MvPolynomial.eval x f| ^ θ ≤ ‖fun i => MvPolynomial.eval x (MvPolynomial.pderiv i f)‖

/-- **The zero set of a real polynomial satisfying the Łojasiewicz gradient inequality is locally
contractible.** -/
theorem locallyContractibleSpace_zeroSet_of_lojasiewicz {n : ℕ} (f : MvPolynomial (Fin n) ℝ)
    (hf : f.LojasiewiczGradient) :
    LocallyContractibleSpace {x : Fin n → ℝ // MvPolynomial.eval x f = 0} := by
  set F : (Fin n → ℝ) → ℝ := fun x ↦ eval x f * eval x f with hF
  set G : (Fin n → ℝ) → Fin n → ℝ := fun x i ↦ 2 * eval x f * eval x (pderiv i f) with hG
  have hFG : ∀ x, HasFDerivAt F
      (∑ i : Fin n, G x i • proj (R := ℝ) (φ := fun _ : Fin n ↦ ℝ) i : (Fin n → ℝ) →L[ℝ] ℝ) x :=
    fun x ↦
    ((hasFDerivAt_eval f x).mul (hasFDerivAt_eval f x)).congr_fderiv
      (ContinuousLinearMap.ext fun v ↦ by
        simp only [hG, add_apply, smul_apply, sum_apply, proj_apply, smul_eq_mul, Finset.mul_sum,
          ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ ↦ by ring)
  have hGc : ContDiff ℝ 1 G := contDiff_pi.2 fun i ↦
    (contDiff_const.mul (contDiff_eval f)).mul (contDiff_eval _)
  have hF0 : ∀ x, 0 ≤ F x := fun x ↦ mul_self_nonneg _
  have hLF : ∀ p, F p = 0 → ∃ θ : ℝ, 0 ≤ θ ∧ θ < 1 ∧ ∃ c : ℝ, 0 < c ∧
      ∀ᶠ x in 𝓝 p, c * F x ^ θ ≤ ‖G x‖ := by
    intro p hp
    obtain ⟨θ, hθ0, hθ1, c, hc, hpL⟩ := hf p (mul_self_eq_zero.1 hp)
    refine ⟨(1 + θ) / 2, by linarith, by linarith, 2 * c, by linarith, ?_⟩
    filter_upwards [hpL] with x hx
    have hGx : G x = (2 * eval x f) • fun i ↦ eval x (pderiv i f) := by
      funext i; simp [hG, smul_eq_mul, mul_assoc]
    have hFx : F x ^ ((1 + θ) / 2) = |eval x f| * |eval x f| ^ θ := by
      have h1 : F x = |eval x f| ^ (2 : ℝ) := by
        rw [Real.rpow_two, sq_abs, hF, sq]
      rw [h1, ← Real.rpow_mul (abs_nonneg _), show 2 * ((1 + θ) / 2) = 1 + θ by ring,
        Real.rpow_add' (abs_nonneg _) (by linarith), Real.rpow_one]
    rw [hGx, norm_smul, hFx, Real.norm_eq_abs, abs_mul, abs_two]
    have := mul_le_mul_of_nonneg_left hx (mul_nonneg zero_le_two (abs_nonneg (eval x f)))
    linarith
  have h := Lojasiewicz.locallyContractibleSpace_zeroSet hFG hGc hF0 hLF
  exact (Homeomorph.subtype (Homeomorph.refl _) fun x ↦ mul_self_eq_zero).locallyContractibleSpace
    h

/-- **The common zero set of a finite family of real polynomials is locally contractible**,
given the Łojasiewicz gradient inequality for the sum of their squares (whose zero set it is). -/
theorem locallyContractibleSpace_zeroSet_finset_of_lojasiewicz {n : ℕ}
    (s : Finset (MvPolynomial (Fin n) ℝ)) (hs : (∑ g ∈ s, g ^ 2).LojasiewiczGradient) :
    LocallyContractibleSpace {x : Fin n → ℝ // ∀ g ∈ s, MvPolynomial.eval x g = 0} :=
  (Homeomorph.subtype (Homeomorph.refl _) fun x ↦ by
    simp only [Homeomorph.refl_apply, id, map_sum, map_pow]
    rw [Finset.sum_eq_zero_iff_of_nonneg fun g _ ↦ sq_nonneg _]
    simp only [sq_eq_zero_iff]).locallyContractibleSpace
    (locallyContractibleSpace_zeroSet_of_lojasiewicz _ hs)

/-- **Changing the index type of the variables.** If zero sets of real polynomials in the
variables `Fin n` are locally contractible for every `n`, so are zero sets of real polynomials in
the variables of any finite type. -/
theorem locallyContractibleSpace_zeroSet_of_fin
    (h : ∀ (n : ℕ) (f : MvPolynomial (Fin n) ℝ),
      LocallyContractibleSpace {x : Fin n → ℝ // MvPolynomial.eval x f = 0})
    {σ : Type*} [Finite σ] (f : MvPolynomial σ ℝ) :
    LocallyContractibleSpace {x : σ → ℝ // MvPolynomial.eval x f = 0} := by
  cases nonempty_fintype σ
  set e := Fintype.equivFin σ
  let H : (Fin (Fintype.card σ) → ℝ) ≃ₜ (σ → ℝ) :=
    { toFun := fun y ↦ y ∘ e
      invFun := fun x ↦ x ∘ e.symm
      left_inv := fun y ↦ by funext i; simp
      right_inv := fun x ↦ by funext i; simp
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  refine (Homeomorph.subtype H fun y ↦ ?_).locallyContractibleSpace
    (h _ (rename e f))
  rw [eval_rename]
  rfl

end MvPolynomial
