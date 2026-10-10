/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Analysis.Complex.Basic
import Oka.Analysis.Lojasiewicz.RealAlgebraic

/-!
# A complex algebraic set is a real algebraic set

The common zero set of finitely many complex polynomials `g₁, …, g_k` in the variables `σ` is,
after identifying `ℂ^σ` with `ℝ^(σ ⊕ σ)` by real and imaginary parts
(`MvPolynomial.complexEquivReal`), the zero set of the single real polynomial
`∑ⱼ (Re gⱼ)² + (Im gⱼ)²` (`MvPolynomial.normSqSum`), whose value at `z` is
`∑ⱼ |gⱼ(z)|²` (`MvPolynomial.eval_normSqSum`). Here `Re q` and `Im q` are obtained from `q` by
substituting `xᵢ ↦ uᵢ + vᵢ * i` (`MvPolynomial.bind₁`) and then taking real and imaginary parts
of the coefficients (`AddMonoidAlgebra.map` along `Complex.reAddGroupHom`,
`Complex.imAddGroupHom`); at real points this commutes with evaluation
(`MvPolynomial.eval_map_re`, `MvPolynomial.eval_map_im`) because the monomials then take real
values.

## Main results

- `MvPolynomial.complexZeroSetHomeomorph`: `{z : σ → ℂ // ∀ j, eval z (g j) = 0}` is homeomorphic
  to `{w : σ ⊕ σ → ℝ // eval w (normSqSum g) = 0}`.
- `MvPolynomial.locallyContractibleSpace_complexZeroSet`: if real algebraic sets (zero sets of one
  real polynomial in `Fin n` variables) are locally contractible, so are complex algebraic sets.
-/

open Set Complex

namespace MvPolynomial

variable {σ : Type*}

/-- At real points, taking an additive `ℝ`-homogeneous map of the coefficients commutes with
evaluation. -/
private theorem eval_map_addMonoidHom (g : ℂ →+ ℝ) (hg : ∀ (a : ℂ) (r : ℝ), g (a * r) = g a * r)
    (w : σ → ℝ) (q : MvPolynomial σ ℂ) :
    eval w (AddMonoidAlgebra.map g q) = g (eval (fun i ↦ (w i : ℂ)) q) := by
  induction q using MvPolynomial.induction_on' with
  | monomial u a =>
    rw [← single_eq_monomial, AddMonoidAlgebra.map_single, single_eq_monomial, eval_monomial,
      single_eq_monomial,
      eval_monomial, show (u.prod fun n e ↦ ((w n : ℂ)) ^ e) = ((u.prod fun n e ↦ w n ^ e : ℝ) : ℂ)
        by simp [Finsupp.prod, Complex.ofReal_prod], hg]
  | add p q hp hq =>
    rw [AddMonoidAlgebra.map_add, map_add, hp, hq, map_add, map_add]

/-- At real points, taking real parts of coefficients commutes with evaluation. -/
theorem eval_map_re (w : σ → ℝ) (q : MvPolynomial σ ℂ) :
    eval w (AddMonoidAlgebra.map reAddGroupHom q) = (eval (fun i ↦ (w i : ℂ)) q).re :=
  eval_map_addMonoidHom _ (fun a r ↦ by simp) w q

/-- At real points, taking imaginary parts of coefficients commutes with evaluation. -/
theorem eval_map_im (w : σ → ℝ) (q : MvPolynomial σ ℂ) :
    eval w (AddMonoidAlgebra.map imAddGroupHom q) = (eval (fun i ↦ (w i : ℂ)) q).im :=
  eval_map_addMonoidHom _ (fun a r ↦ by simp) w q

/-- The substitution `xᵢ ↦ uᵢ + vᵢ * i`, from polynomials in `σ` to polynomials in `σ ⊕ σ`. -/
noncomputable def realify (q : MvPolynomial σ ℂ) : MvPolynomial (σ ⊕ σ) ℂ :=
  bind₁ (fun i ↦ X (Sum.inl i) + X (Sum.inr i) * C I) q

/-- Evaluating the substitution `xᵢ ↦ uᵢ + vᵢ * i` at `w` is evaluating at
`wₗ + wᵣ * i`. -/
theorem eval_realify (w : σ ⊕ σ → ℂ) (q : MvPolynomial σ ℂ) :
    eval w (realify q) = eval (fun i ↦ w (Sum.inl i) + w (Sum.inr i) * I) q := by
  have := eval₂Hom_bind₁ (RingHom.id ℂ) w (fun i ↦ X (Sum.inl i) + X (Sum.inr i) * C I) q
  simpa [realify] using this

/-- **The identification `ℂ^σ ≃ ℝ^(σ ⊕ σ)`** by real and imaginary parts. -/
noncomputable def complexEquivReal : (σ → ℂ) ≃ₜ (σ ⊕ σ → ℝ) where
  toFun z := Sum.elim (fun i ↦ (z i).re) (fun i ↦ (z i).im)
  invFun w i := (w (Sum.inl i) : ℂ) + w (Sum.inr i) * I
  left_inv z := by funext i; simp [re_add_im]
  right_inv w := by funext k; cases k <;> simp
  continuous_toFun := continuous_pi fun k ↦ by
    cases k with
    | inl i => exact continuous_re.comp (continuous_apply i)
    | inr i => exact continuous_im.comp (continuous_apply i)
  continuous_invFun := by fun_prop

section Fintype

variable {ι : Type*} [Fintype ι]

/-- **The real polynomial `∑ⱼ (Re gⱼ)² + (Im gⱼ)²`**, whose value at the real point corresponding
to `z` is `∑ⱼ |gⱼ(z)|²`. -/
noncomputable def normSqSum (g : ι → MvPolynomial σ ℂ) : MvPolynomial (σ ⊕ σ) ℝ :=
  ∑ j, (AddMonoidAlgebra.map reAddGroupHom (realify (g j)) ^ 2 +
    AddMonoidAlgebra.map imAddGroupHom (realify (g j)) ^ 2)

/-- **The value of `normSqSum g` at the real point of `z` is `∑ⱼ |gⱼ(z)|²`.** -/
theorem eval_normSqSum (g : ι → MvPolynomial σ ℂ) (z : σ → ℂ) :
    eval (complexEquivReal z) (normSqSum g) = ∑ j, normSq (eval z (g j)) := by
  simp only [normSqSum, map_sum, map_add, map_pow, eval_map_re, eval_map_im, eval_realify]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hz : (fun i ↦ ((complexEquivReal z (Sum.inl i) : ℝ) : ℂ) +
      ((complexEquivReal z (Sum.inr i) : ℝ) : ℂ) * I) = z := by
    funext i; exact re_add_im (z i)
  rw [hz, normSq_apply]
  ring

/-- **A complex algebraic set is homeomorphic to a real algebraic set.** -/
noncomputable def complexZeroSetHomeomorph (g : ι → MvPolynomial σ ℂ) :
    {z : σ → ℂ // ∀ j, eval z (g j) = 0} ≃ₜ
      {w : σ ⊕ σ → ℝ // eval w (normSqSum g) = 0} :=
  Homeomorph.subtype complexEquivReal fun z ↦ by
    rw [eval_normSqSum, Finset.sum_eq_zero_iff_of_nonneg fun j _ ↦ normSq_nonneg _]
    simp only [Finset.mem_univ, true_imp_iff, normSq_eq_zero]

end Fintype

/-- **Complex algebraic sets are locally contractible if real algebraic sets are.** -/
theorem locallyContractibleSpace_complexZeroSet {ι : Type*} [Finite ι] [Finite σ]
    (h : ∀ (n : ℕ) (f : MvPolynomial (Fin n) ℝ),
      LocallyContractibleSpace {x : Fin n → ℝ // MvPolynomial.eval x f = 0})
    (g : ι → MvPolynomial σ ℂ) :
    LocallyContractibleSpace {z : σ → ℂ // ∀ j, eval z (g j) = 0} := by
  cases nonempty_fintype ι
  exact (complexZeroSetHomeomorph g).symm.locallyContractibleSpace
    (locallyContractibleSpace_zeroSet_of_fin h _)

end MvPolynomial
