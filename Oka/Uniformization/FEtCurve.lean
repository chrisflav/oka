/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Uniformization.FEtAut

/-!
# The coordinate ring of a once-punctured elliptic curve as functions on `ℍ`

For a Weierstrass curve `W` over `ℂ` and functions `x, y` on `ℍ` satisfying the equation of `W`,
`FEt.coordFun` is the evaluation `ℂ[W] → (ℍ → ℂ)`. The `ℂ`-points of `ℂ[W]` are determined by
their values on the coordinate functions (`FEt.algHom_ext_coord`) and satisfy the equation
(`FEt.equation_coord`). For holomorphic `x, y` the functions are holomorphic, and if every point
of `W` is reached, the evaluation is injective.
-/

open Complex Metric Set Filter Topology Polynomial
open UpperHalfPlane hiding I I_re I_im
open scoped MatrixGroups Polynomial.Bivariate

namespace Uniformization

namespace FEt

variable (W : WeierstrassCurve ℂ)

/-- The coordinate function `x` of `ℂ[W]`. -/
noncomputable abbrev xA : W.toAffine.CoordinateRing :=
  WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine (C X)

/-- The coordinate function `y` of `ℂ[W]`. -/
noncomputable abbrev yA : W.toAffine.CoordinateRing :=
  WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine X

variable {W}

/-- `ℂ`-points of `ℂ[W]` evaluate bivariate polynomials at their coordinates. -/
theorem algHom_mk (χ : W.toAffine.CoordinateRing →ₐ[ℂ] ℂ) (g : ℂ[X][Y]) :
    χ (WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine g) =
      g.evalEval (χ (xA W)) (χ (yA W)) := by
  set f : ℂ[X][Y] →+* ℂ := (χ : W.toAffine.CoordinateRing →+* ℂ).comp
    (WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine)
  set e : ℂ[X][Y] →+* ℂ := (evalRingHom (χ (xA W))).comp (evalRingHom (C (χ (yA W))))
  have he : ∀ g, e g = g.evalEval (χ (xA W)) (χ (yA W)) := fun g ↦ rfl
  have hC : f.comp C = e.comp C := by
    refine Polynomial.ringHom_ext (fun c ↦ ?_) ?_
    · simp only [RingHom.comp_apply, f, he]
      rw [evalEval_C, eval_C]
      have : WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine (C (C c)) =
          algebraMap ℂ W.toAffine.CoordinateRing c := rfl
      rw [RingHom.coe_coe, this, AlgHom.commutes]; rfl
    · simp only [RingHom.comp_apply, f, he]
      rw [evalEval_C, eval_X]; rfl
  have hfe : f = e := by
    refine Polynomial.ringHom_ext (fun a ↦ congrFun (congrArg DFunLike.coe hC) a) ?_
    simp only [f, he, RingHom.comp_apply]
    rw [evalEval_X]; rfl
  exact congrFun (congrArg DFunLike.coe hfe) g

/-- `ℂ`-points of `ℂ[W]` are determined by the coordinates. -/
theorem algHom_ext_coord {χ χ' : W.toAffine.CoordinateRing →ₐ[ℂ] ℂ} (hx : χ (xA W) = χ' (xA W))
    (hy : χ (yA W) = χ' (yA W)) : χ = χ' := by
  refine AlgHom.ext fun a ↦ ?_
  obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective a
  have h1 := algHom_mk χ g
  have h2 := algHom_mk χ' g
  rw [hx, hy] at h1
  exact h1.trans h2.symm

/-- `ℂ`-points of `ℂ[W]` lie on `W`. -/
theorem equation_coord (χ : W.toAffine.CoordinateRing →ₐ[ℂ] ℂ) :
    W.toAffine.Equation (χ (xA W)) (χ (yA W)) := by
  have := algHom_mk χ W.toAffine.polynomial
  rw [AdjoinRoot.mk_self, map_zero] at this
  exact this.symm

variable (W) in
/-- The `ℂ`-point of `ℂ[W]` at a point of `W`. -/
noncomputable def ptAlg {x₀ y₀ : ℂ} (h : W.toAffine.Equation x₀ y₀) :
    W.toAffine.CoordinateRing →ₐ[ℂ] ℂ :=
  { AdjoinRoot.evalEval (p := W.toAffine.polynomial) h with
    commutes' := fun c ↦ by
      have : algebraMap ℂ W.toAffine.CoordinateRing c =
          WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine (C (C c)) := rfl
      simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
        MonoidHom.coe_coe]
      rw [this, AdjoinRoot.evalEval_mk, evalEval_C, eval_C]; rfl }

theorem ptAlg_mk {x₀ y₀ : ℂ} (h : W.toAffine.Equation x₀ y₀) (g : ℂ[X][Y]) :
    ptAlg W h (WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine g) = g.evalEval x₀ y₀ :=
  AdjoinRoot.evalEval_mk h g

variable (W) in
/-- The evaluation `ℂ[W] → (ℍ → ℂ)` at functions `x, y` satisfying the equation. -/
noncomputable def coordFun (x y : ℍ → ℂ) (hxy : ∀ τ, W.toAffine.Equation (x τ) (y τ)) :
    W.toAffine.CoordinateRing →ₐ[ℂ] (ℍ → ℂ) :=
  AlgHom.pi fun τ ↦ ptAlg W (hxy τ)

theorem coordFun_mk {x y : ℍ → ℂ} (hxy : ∀ τ, W.toAffine.Equation (x τ) (y τ)) (g : ℂ[X][Y])
    (τ : ℍ) : coordFun W x y hxy (WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine g) τ =
      g.evalEval (x τ) (y τ) :=
  ptAlg_mk (hxy τ) g

theorem coordFun_xA {x y : ℍ → ℂ} (hxy : ∀ τ, W.toAffine.Equation (x τ) (y τ)) (τ : ℍ) :
    coordFun W x y hxy (xA W) τ = x τ := by
  rw [coordFun_mk, evalEval_C, eval_X]

theorem coordFun_yA {x y : ℍ → ℂ} (hxy : ∀ τ, W.toAffine.Equation (x τ) (y τ)) (τ : ℍ) :
    coordFun W x y hxy (yA W) τ = y τ := by
  rw [coordFun_mk, evalEval_X]

/-- Holomorphy of the evaluation. -/
theorem holH_coordFun {x y : ℍ → ℂ} (hxy : ∀ τ, W.toAffine.Equation (x τ) (y τ))
    (hx : Unif.HolH x) (hy : Unif.HolH y) (a : W.toAffine.CoordinateRing) :
    Unif.HolH (coordFun W x y hxy a) := by
  obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective a
  have key : ∀ g : ℂ[X][Y], Unif.HolH fun τ ↦ g.evalEval (x τ) (y τ) := by
    intro g
    induction g using Polynomial.induction_on with
    | C p =>
      simp only [evalEval_C]
      exact (Polynomial.differentiable p).comp_differentiableOn hx
    | add p q hp hq =>
      simp only [evalEval_add]
      exact DifferentiableOn.add hp hq
    | monomial n p hp =>
      simp only [evalEval_mul, evalEval_pow, evalEval_X, evalEval_C] at hp ⊢
      have := hp.mul hy
      refine this.congr fun z _ ↦ ?_
      simp only [Pi.mul_apply, pow_succ]; ring
  have := key g
  refine this.congr fun z _ ↦ ?_
  exact coordFun_mk hxy g _

theorem coordFun_smul_basis {x y : ℍ → ℂ} (hxy : ∀ τ, W.toAffine.Equation (x τ) (y τ))
    (p q : ℂ[X]) (τ : ℍ) :
    coordFun W x y hxy (p • (1 : W.toAffine.CoordinateRing) + q • yA W) τ =
      p.eval (x τ) + q.eval (x τ) * y τ := by
  rw [WeierstrassCurve.Affine.CoordinateRing.smul, WeierstrassCurve.Affine.CoordinateRing.smul,
    mul_one, ← map_mul, ← map_add, coordFun_mk]
  simp [evalEval_add, evalEval_mul, evalEval_C, evalEval_X]

/-- Over every `x₀` outside a finite set there are two distinct points of `W`. -/
theorem exists_two_points (W : WeierstrassCurve ℂ) :
    ∃ D : ℂ[X], D ≠ 0 ∧ ∀ x₀, D.eval x₀ ≠ 0 → ∃ y₁ y₂, y₁ ≠ y₂ ∧
      W.toAffine.Equation x₀ y₁ ∧ W.toAffine.Equation x₀ y₂ := by
  refine ⟨C (W.a₁ ^ 2) * X ^ 2 + C (2 * W.a₁ * W.a₃) * X + C (W.a₃ ^ 2) +
    C 4 * (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆), ?_, fun x₀ hx₀ ↦ ?_⟩
  · intro h
    have := congrArg (coeff · 3) h
    simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X, coeff_zero] at this
    norm_num at this
  · set b := W.a₁ * x₀ + W.a₃
    set c := x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆
    have hd : b ^ 2 + 4 * c ≠ 0 := by
      convert hx₀ using 1; simp [b, c]; ring
    obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (b ^ 2 + 4 * c) two_pos
    have hs0 : s ≠ 0 := by rintro rfl; apply hd; rw [← hs]; ring
    refine ⟨(-b + s) / 2, (-b - s) / 2, fun h ↦ hs0 (by linear_combination h), ?_, ?_⟩
    · rw [WeierstrassCurve.Affine.equation_iff]
      linear_combination (1 / 4 : ℂ) * hs
    · rw [WeierstrassCurve.Affine.equation_iff]
      linear_combination (1 / 4 : ℂ) * hs

/-- If the functions `x, y` reach every point of `W`, the evaluation is injective. -/
theorem coordFun_injective {x y : ℍ → ℂ} (hxy : ∀ τ, W.toAffine.Equation (x τ) (y τ))
    (hsurj : ∀ x₀ y₀, W.toAffine.Equation x₀ y₀ → ∃ τ, x τ = x₀ ∧ y τ = y₀) :
    Function.Injective (coordFun W x y hxy) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨p, q, rfl⟩ := WeierstrassCurve.Affine.CoordinateRing.exists_smul_basis_eq a
  have hval : ∀ x₀ y₀, W.toAffine.Equation x₀ y₀ → p.eval x₀ + q.eval x₀ * y₀ = 0 := by
    intro x₀ y₀ h
    obtain ⟨τ, hτx, hτy⟩ := hsurj x₀ y₀ h
    have := congrFun ha τ
    rw [coordFun_smul_basis, hτx, hτy] at this
    exact this
  obtain ⟨D, hD, hD2⟩ := exists_two_points W
  have hq : q = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    have hsub : {x₀ | D.eval x₀ ≠ 0} ⊆ {x₀ | q.IsRoot x₀} := by
      intro x₀ hx₀
      obtain ⟨y₁, y₂, hne, h1, h2⟩ := hD2 x₀ hx₀
      have := (hval x₀ y₁ h1).trans (hval x₀ y₂ h2).symm
      have : q.eval x₀ * (y₁ - y₂) = 0 := by linear_combination this
      exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hne)
    refine Set.Infinite.mono hsub ?_
    have hfin : {x₀ | D.eval x₀ = 0}.Finite := by
      refine (D.roots.toFinset.finite_toSet).subset fun x₀ hx₀ ↦ ?_
      simp only [Finset.mem_coe, Multiset.mem_toFinset, mem_roots hD]
      exact hx₀
    have := hfin.infinite_compl
    simpa [Set.compl_setOf] using this
  have hp : p = 0 := by
    apply Polynomial.funext
    intro x₀
    set b := W.a₁ * x₀ + W.a₃
    set c := x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆
    obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (b ^ 2 + 4 * c) two_pos
    have h1 : W.toAffine.Equation x₀ ((-b + s) / 2) := by
      rw [WeierstrassCurve.Affine.equation_iff]
      linear_combination (1 / 4 : ℂ) * hs
    have := hval x₀ _ h1
    rw [hq, eval_zero, zero_mul, add_zero] at this
    rw [this, eval_zero]
  rw [hp, hq, zero_smul, zero_smul, add_zero]

theorem PolyBdd.poly_eval {h₀ : ℍ → ℂ} (p : ℂ[X]) :
    PolyBdd h₀ fun τ ↦ ‖p.eval (h₀ τ)‖ := by
  refine ⟨∑ i ∈ Finset.range (p.natDegree + 1), ‖p.coeff i‖, p.natDegree, fun τ ↦ ?_⟩
  change ‖p.eval (h₀ τ)‖ ≤ _
  rw [eval_eq_sum_range, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi ↦ ?_)
  rw [norm_mul, norm_pow]
  have h1 : 1 ≤ 2 + ‖h₀ τ‖ := by linarith [norm_nonneg (h₀ τ)]
  have h2 : ‖h₀ τ‖ ^ i ≤ (2 + ‖h₀ τ‖) ^ p.natDegree :=
    (pow_le_pow_left₀ (norm_nonneg _) (by linarith) i).trans
      (pow_le_pow_right₀ h1 (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))
  exact mul_le_mul_of_nonneg_left h2 (norm_nonneg _)

theorem norm_le_of_sq_add {y b c : ℂ} (h : y ^ 2 + b * y = c) : ‖y‖ ≤ 1 + ‖b‖ + ‖c‖ := by
  have h1 : ‖y‖ ^ 2 ≤ ‖c‖ + ‖b‖ * ‖y‖ := by
    rw [← norm_pow, show y ^ 2 = c - b * y by linear_combination h, ← norm_mul]
    exact norm_sub_le _ _
  by_contra hc
  push Not at hc
  nlinarith [norm_nonneg b, norm_nonneg c, norm_nonneg y]

/-- Values of `ℂ[W]` are polynomially bounded in the `x`-coordinate. -/
theorem polyBdd_coordFun {x y : ℍ → ℂ} (hxy : ∀ τ, W.toAffine.Equation (x τ) (y τ))
    (a : W.toAffine.CoordinateRing) : PolyBdd x fun τ ↦ ‖coordFun W x y hxy a τ‖ := by
  obtain ⟨p, q, rfl⟩ := WeierstrassCurve.Affine.CoordinateRing.exists_smul_basis_eq a
  set bP : ℂ[X] := C W.a₁ * X + C W.a₃
  set cP : ℂ[X] := X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆
  have hy : PolyBdd x fun τ ↦ ‖y τ‖ := by
    refine ((PolyBdd.const 1).add ((PolyBdd.poly_eval (h₀ := x) bP).add
      (PolyBdd.poly_eval cP))).mono fun τ ↦ ?_
    have h := hxy τ
    rw [WeierstrassCurve.Affine.equation_iff] at h
    have := norm_le_of_sq_add (y := y τ) (b := bP.eval (x τ)) (c := cP.eval (x τ))
      (by simp only [bP, cP, eval_add, eval_mul, eval_C, eval_X, eval_pow]; linear_combination h)
    simp only [Pi.add_apply]
    linarith
  refine (((PolyBdd.poly_eval (h₀ := x) p).add ((PolyBdd.poly_eval (h₀ := x) q).mul hy
    (fun _ ↦ norm_nonneg _) (fun _ ↦ norm_nonneg _)))).mono fun τ ↦ ?_
  rw [coordFun_smul_basis]
  simp only [Pi.add_apply, Pi.mul_apply]
  exact (norm_add_le _ _).trans (by rw [norm_mul])

end FEt

end Uniformization
