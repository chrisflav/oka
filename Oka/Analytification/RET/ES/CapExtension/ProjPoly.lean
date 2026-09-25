/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.ES.CapExtension.ProjFromCap
import Oka.Analysis.Complex.LiouvillePolynomial
import Mathlib.LinearAlgebra.Lagrange

/-!
# Polynomial multiples of sections of the cap

An entire function `g` with `g(w) = wᵉ h(w⁻¹)`, `h` entire, is a polynomial of degree `≤ e`, so it
is determined by its values at `e + 1` distinct points through Lagrange interpolation
(`ComplexAnalytic.Cap.eq_sum_lagrange_of_eq_pow_mul_inv`).

A polynomial `p` of degree `≤ e` in the fibre coordinate `w` multiplies a section of the cap with a
pole of order `≤ n` at infinity into a section with a pole of order `≤ n + e`: at infinity it is
`u'^{e kᵢ} p(u'^{-kᵢ})`, the reversed polynomial evaluated at `u'^{kᵢ}`
(`ComplexAnalytic.Cap.AnnulusDecomposition.polyShift_mem`).
-/

open CategoryTheory Opposite Topology TopologicalSpace Set Filter Metric Polynomial

universe u

namespace ComplexAnalytic.Cap

noncomputable section

/-! ### Lagrange interpolation of functions with a pole of order `≤ e` at infinity -/

/-- **Entire functions with a pole of order `≤ e` at infinity are polynomials of degree `≤ e`.** -/
theorem exists_polynomial_of_eq_pow_mul_inv {g h : ℂ → ℂ} (hg : Differentiable ℂ g)
    (hh : Differentiable ℂ h) {e : ℕ} (hgh : ∀ w ≠ 0, g w = w ^ e * h w⁻¹) :
    ∃ p : ℂ[X], p.degree < ↑(e + 1) ∧ ∀ w, g w = p.eval w := by
  obtain ⟨C₁, hC₁⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn
    hh.continuous.continuousOn
  obtain ⟨C₂, hC₂⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn
    hg.continuous.continuousOn
  refine Differentiable.exists_polynomial_eq_of_norm_le_pow hg (C := max C₁ C₂) fun w ↦ ?_
  have hC : 0 ≤ max C₁ C₂ := (norm_nonneg _).trans ((hC₂ 0 (mem_closedBall_self zero_le_one)).trans
    (le_max_right _ _))
  have h1 : 1 ≤ (1 + ‖w‖) ^ e := one_le_pow₀ (by linarith [norm_nonneg w])
  by_cases hw : ‖w‖ ≤ 1
  · exact (hC₂ w (mem_closedBall_zero_iff.2 hw)).trans ((le_max_right _ _).trans
      (le_mul_of_one_le_right hC h1))
  · push Not at hw
    have hw0 : w ≠ 0 := norm_pos_iff.1 (zero_lt_one.trans hw)
    rw [hgh w hw0, norm_mul, norm_pow, mul_comm]
    refine mul_le_mul ((hC₁ _ (mem_closedBall_zero_iff.2 ?_)).trans (le_max_left _ _))
      (pow_le_pow_left₀ (norm_nonneg _) (by linarith) e) (by positivity) hC
    rw [norm_inv]
    exact inv_le_one_of_one_le₀ hw.le

/-- **Lagrange interpolation** of an entire function with a pole of order `≤ e` at infinity at
`e + 1` distinct points. -/
theorem eq_sum_lagrange_of_eq_pow_mul_inv {g h : ℂ → ℂ} (hg : Differentiable ℂ g)
    (hh : Differentiable ℂ h) {e : ℕ} (hgh : ∀ w ≠ 0, g w = w ^ e * h w⁻¹)
    {x : Fin (e + 1) → ℂ} (hx : Function.Injective x) (z : ℂ) :
    g z = ∑ l, g (x l) * (Lagrange.basis Finset.univ x l).eval z := by
  obtain ⟨p, hpdeg, hp⟩ := exists_polynomial_of_eq_pow_mul_inv hg hh hgh
  have hdeg : p.degree < (Finset.univ : Finset (Fin (e + 1))).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact hpdeg
  have h := Lagrange.eq_interpolate (s := Finset.univ) (v := x) hx.injOn hdeg
  rw [hp z, h, Lagrange.interpolate_apply, eval_finsetSum]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [eval_mul, eval_C, hp (x l)]

/-- The Lagrange basis polynomials at `e + 1` points have degree `≤ e`. -/
lemma natDegree_lagrange_basis_le {e : ℕ} {x : Fin (e + 1) → ℂ} (hx : Function.Injective x)
    (l : Fin (e + 1)) : (Lagrange.basis Finset.univ x l).natDegree ≤ e := by
  have := Lagrange.natDegree_basis (s := Finset.univ) hx.injOn (Finset.mem_univ l)
  rw [this, Finset.card_univ, Fintype.card_fin, Nat.add_sub_cancel]

/-! ### The reversed polynomial -/

/-- The reversed polynomial `xᵉ p(x⁻¹)` of a polynomial of degree `≤ e`, evaluated at `x`. -/
def revEval (p : ℂ[X]) (e : ℕ) (x : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (e + 1), p.coeff j * x ^ (e - j)

lemma differentiable_revEval (p : ℂ[X]) (e : ℕ) : Differentiable ℂ (revEval p e) := by
  unfold revEval
  fun_prop

lemma pow_mul_revEval_inv {p : ℂ[X]} {e : ℕ} (hp : p.natDegree ≤ e) {u : ℂ} (hu : u ≠ 0) :
    u ^ e * revEval p e u⁻¹ = p.eval u := by
  rw [eval_eq_sum_range' (Nat.lt_succ_of_le hp), revEval, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have hje : j ≤ e := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  rw [inv_pow, mul_left_comm, ← Nat.add_sub_cancel' hje, pow_add, Nat.add_sub_cancel_left,
    mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hu), mul_one]

namespace AnnulusDecomposition

open AnalyticSpace BoundedSections
open KummerModel (splitEquiv)

variable {m : ℕ} {N N₀ : (AnalyticSpace.complexAffineSpace.{u} (m + 1)).Opens} (h₀ : N₀ ≤ N)
  {W : FiniteEtaleOver (space N₀)} {F : WeierstrassForm N N₀}
  (D : AnnulusDecomposition W F.G F.ρ) {V : (space N).Opens} {V' : Set (Cm.{u} m × ℂ)}

/-- The polynomial `p(w)` in the fibre coordinate, as a holomorphic function on `V`. -/
def polyFun (V : (space N).Opens) (p : ℂ[X]) : (space N).presheaf.obj (op V) :=
  OkaRing.ofDifferentiableOn (fun x ↦ p.eval (fibOf x))
    ((p.differentiable.comp differentiable_fibOf).differentiableOn)

/-- **The product of a section of the cap with a polynomial `p` in the fibre coordinate.** -/
def polyShift (p : ℂ[X]) (e : ℕ) (s : boundedSubring h₀ W V × (D.ι → Cm.{u} m × ℂ → ℂ)) :
    boundedSubring h₀ W V × (D.ι → Cm.{u} m × ℂ → ℂ) :=
  (algebraMapBounded h₀ W V (polyFun V p) * s.1,
    fun i z ↦ revEval p e (z.2 ^ (D.deg i : ℕ)) * s.2 i z)

lemma evalFun_polyShift (p : ℂ[X]) (e : ℕ) (s : boundedSubring h₀ W V × (D.ι → Cm.{u} m × ℂ → ℂ))
    {w : W.left} (hw : w ∈ preim h₀ W V) :
    evalFun (D.polyShift h₀ p e s).1.1 w = p.eval (fibOf (pt W w)) * evalFun s.1.1 w := by
  change evalFun (pullback h₀ W V (polyFun V p) * s.1.1) w = _
  rw [evalFun_mul W _ _ hw, evalFun_pullback h₀ W _ hw, polyFun,
    holFun_ofDifferentiableOn _ ((mem_preim_iff h₀ W).1 hw)]

/-- **A polynomial of degree `≤ e` in `w` raises the order of the pole at infinity by `≤ e`.** -/
theorem polyShift_mem {p : ℂ[X]} {e : ℕ} (hp : p.natDegree ≤ e) {n : ℕ}
    {s : boundedSubring h₀ W V × (D.ι → Cm.{u} m × ℂ → ℂ)} (hs : s ∈ D.capPole h₀ n V V') :
    D.polyShift h₀ p e s ∈ D.capPole h₀ (n + e) V V' := by
  refine ⟨fun i ↦ ?_, fun i z hz hz' ↦ ?_⟩
  · exact (((differentiable_revEval p e).comp (differentiable_snd.pow _)).differentiableOn).mul
      (hs.1 i)
  · have hz0 : z.2 ≠ 0 := norm_pos_iff.1 (KummerAnnulus.pos_of_mem_base F.G
      (inv_nonneg.2 F.pos_ρ.le) (D.deg i).ne_zero hz.1)
    obtain ⟨hzb, hzO⟩ := hz
    change D.kummerVal (pullback h₀ W V (polyFun V p) * s.1.1) i z = _
    rw [D.kummerVal_mul ⟨hzb, hzO⟩, hs.2 i z ⟨hzb, hzO⟩ hz', D.kummerVal_of_mem _ _ hzb,
      evalFun_pullback h₀ W _ hzO, polyFun,
      holFun_ofDifferentiableOn _ ((mem_preim_iff h₀ W).1 hzO)]
    have hfib : fibOf (pt W (D.toFun ⟨i, ⟨z, hzb⟩⟩)) = z.2 ^ (D.deg i : ℕ) := by
      change (splitEquiv m (pt W (D.toFun ⟨i, ⟨z, hzb⟩⟩))).2 = _
      rw [D.splitEquiv_pt]
    rw [hfib, ← pow_mul_revEval_inv hp (pow_ne_zero (D.deg i : ℕ) hz0)]
    simp only [polyShift, invCoord, inv_pow]
    rw [add_mul, pow_add, ← pow_mul, mul_comm e]
    ring

end AnnulusDecomposition

end

end ComplexAnalytic.Cap
