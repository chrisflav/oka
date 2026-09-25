/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.GAGA.MittagLeffler
import Oka.Analytification.GAGA.Runge

/-!
# Cousin splitting with bounds, for vector-valued functions

The additive input for Cartan's matrix lemma: the Cousin splitting `f = f₁ + f₂` of
`Complex.exists_cousin_split_re`, for functions with values in a finite-dimensional complex
normed space `V`, together with sup-norm bounds for `f₁` and `f₂` at a distance `η` from the
sides of the rectangle. We also record Weierstrass' theorem and Runge approximation on rectangles
for `V`-valued functions, reduced to the scalar case by choosing a basis.

## Main results

- `Complex.norm_cauchyRight_le` (and `Left`, `Bottom`, `Top`): the side integrals are bounded by
  `length * M / η` at distance `η` from the side, if `‖f‖ ≤ M` on the closed rectangle.
- `Complex.exists_cousin_split_bound`: **Cousin splitting with bounds** for `V`-valued functions.
- `Complex.differentiableOn_of_tendstoLocallyUniformlyOn_of_finiteDimensional`: Weierstrass'
  theorem for `V`-valued functions.
- `Complex.exists_approx_entire_of_rect_of_finiteDimensional`: Runge approximation on rectangles
  for `V`-valued functions.
-/

open Set MeasureTheory Filter
open scoped Interval Real Topology

namespace Complex

section Bounds

variable {E : Type*}

/-- A Cauchy integral along a path at distance at least `η` from `z` is bounded by
`length * M / η`, if the integrand is bounded by `M` on the path. -/
lemma norm_cauchyEdge_le {f : ℂ × E → ℂ} {γ : ℝ → ℂ} {t₀ t₁ : ℝ} {z : ℂ} {w : E} {M η : ℝ}
    (hη : 0 < η) (hM : 0 ≤ M) (hγ : ∀ t ∈ [[t₀, t₁]], η ≤ ‖γ t - z‖)
    (hf : ∀ t ∈ [[t₀, t₁]], ‖f (γ t, w)‖ ≤ M) :
    ‖∫ t in t₀..t₁, (γ t - z)⁻¹ * f (γ t, w)‖ ≤ |t₁ - t₀| * M / η := by
  have h : ∀ t ∈ Ι t₀ t₁, ‖(γ t - z)⁻¹ * f (γ t, w)‖ ≤ M / η := by
    intro t ht
    have ht' := uIoc_subset_uIcc ht
    have hpos : 0 < ‖γ t - z‖ := hη.trans_le (hγ t ht')
    rw [norm_mul, norm_inv, inv_mul_eq_div]
    calc ‖f (γ t, w)‖ / ‖γ t - z‖ ≤ M / ‖γ t - z‖ := by gcongr; exact hf t ht'
      _ ≤ M / η := div_le_div_of_nonneg_left hM hη (hγ t ht')
  calc _ ≤ M / η * |t₁ - t₀| := intervalIntegral.norm_integral_le_of_norm_le_const h
    _ = |t₁ - t₀| * M / η := by ring

variable {f : ℂ × E → ℂ} {a b z : ℂ} {w : E} {M η : ℝ}

private lemma norm_two_pi_I_inv_mul_le (x : ℂ) : ‖(2 * π * I)⁻¹ * x‖ ≤ ‖x‖ := by
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) norm_two_pi_I_inv_le_one

variable (hre : a.re ≤ b.re) (him : a.im ≤ b.im)
  (hf : ∀ ζ ∈ Icc a.re b.re ×ℂ Icc a.im b.im, ‖f (ζ, w)‖ ≤ M)
include hre him hf

private lemma nonneg_of_bound : 0 ≤ M :=
  (norm_nonneg _).trans (hf a ⟨⟨le_rfl, hre⟩, le_rfl, him⟩)

private lemma bound_vertical {x : ℝ} (hx : x = a.re ∨ x = b.re) :
    ∀ y ∈ [[a.im, b.im]], ‖f ((x : ℂ) + y * I, w)‖ ≤ M :=
  fun _ hy ↦ hf _ (mapsTo_vertical_rectBoundary hre him hx hy).1

private lemma bound_horizontal {y : ℝ} (hy : y = a.im ∨ y = b.im) :
    ∀ x ∈ [[a.re, b.re]], ‖f ((x : ℂ) + y * I, w)‖ ≤ M :=
  fun _ hx ↦ hf _ (mapsTo_horizontal_rectBoundary hre him hy hx).1

/-- The right side integral is bounded at distance `η` to the left of the right side. -/
lemma norm_cauchyRight_le (hη : 0 < η) (hz : z.re + η ≤ b.re) :
    ‖cauchyRight f a b (z, w)‖ ≤ (b.im - a.im) * M / η := by
  have hi := norm_cauchyEdge_le (f := f) (w := w) (z := z) (t₀ := a.im) (t₁ := b.im)
    (γ := fun y : ℝ ↦ (b.re : ℂ) + y * I) hη (nonneg_of_bound hre him hf)
    (fun y _ ↦ by
      refine le_trans ?_ (abs_re_le_norm _)
      simp only [sub_re, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im]
      rw [abs_of_nonneg (by linarith)]
      linarith) (bound_vertical hre him hf (Or.inr rfl))
  rw [abs_of_nonneg (sub_nonneg.2 him)] at hi
  refine (norm_two_pi_I_inv_mul_le _).trans ?_
  rw [norm_mul, norm_I, one_mul]
  exact hi

/-- The left side integral is bounded at distance `η` to the right of the left side. -/
lemma norm_cauchyLeft_le (hη : 0 < η) (hz : a.re + η ≤ z.re) :
    ‖cauchyLeft f a b (z, w)‖ ≤ (b.im - a.im) * M / η := by
  have hi := norm_cauchyEdge_le (f := f) (w := w) (z := z) (t₀ := a.im) (t₁ := b.im)
    (γ := fun y : ℝ ↦ (a.re : ℂ) + y * I) hη (nonneg_of_bound hre him hf)
    (fun y _ ↦ by
      refine le_trans ?_ (abs_re_le_norm _)
      simp only [sub_re, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im]
      rw [abs_of_nonpos (by linarith)]
      linarith) (bound_vertical hre him hf (Or.inl rfl))
  rw [abs_of_nonneg (sub_nonneg.2 him)] at hi
  rw [cauchyLeft, norm_neg]
  refine (norm_two_pi_I_inv_mul_le _).trans ?_
  rw [norm_mul, norm_I, one_mul]
  exact hi

/-- The bottom side integral is bounded at distance `η` above the bottom side. -/
lemma norm_cauchyBottom_le (hη : 0 < η) (hz : a.im + η ≤ z.im) :
    ‖cauchyBottom f a b (z, w)‖ ≤ (b.re - a.re) * M / η := by
  have hi := norm_cauchyEdge_le (f := f) (w := w) (z := z) (t₀ := a.re) (t₁ := b.re)
    (γ := fun x : ℝ ↦ (x : ℂ) + a.im * I) hη (nonneg_of_bound hre him hf)
    (fun x _ ↦ by
      refine le_trans ?_ (abs_im_le_norm _)
      simp only [sub_im, add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im]
      rw [abs_of_nonpos (by linarith)]
      linarith) (bound_horizontal hre him hf (Or.inl rfl))
  rw [abs_of_nonneg (sub_nonneg.2 hre)] at hi
  exact (norm_two_pi_I_inv_mul_le _).trans hi

/-- The top side integral is bounded at distance `η` below the top side. -/
lemma norm_cauchyTop_le (hη : 0 < η) (hz : z.im + η ≤ b.im) :
    ‖cauchyTop f a b (z, w)‖ ≤ (b.re - a.re) * M / η := by
  have hi := norm_cauchyEdge_le (f := f) (w := w) (z := z) (t₀ := a.re) (t₁ := b.re)
    (γ := fun x : ℝ ↦ (x : ℂ) + b.im * I) hη (nonneg_of_bound hre him hf)
    (fun x _ ↦ by
      refine le_trans ?_ (abs_im_le_norm _)
      simp only [sub_im, add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im]
      rw [abs_of_nonneg (by linarith)]
      linarith) (bound_horizontal hre him hf (Or.inr rfl))
  rw [abs_of_nonneg (sub_nonneg.2 hre)] at hi
  rw [cauchyTop, norm_neg]
  exact (norm_two_pi_I_inv_mul_le _).trans hi

end Bounds

section Vector

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
variable (V : Type*) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

/-- The coordinate functionals of `Module.finBasis ℂ V`, as continuous linear maps. -/
noncomputable def finBasisCoord (i : Fin (Module.finrank ℂ V)) : V →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap ((Module.finBasis ℂ V).coord i)

/-- The constant `∑ i, ‖coord i‖ * ‖b i‖` of the basis `b = Module.finBasis ℂ V`. -/
noncomputable def finBasisConst : ℝ :=
  ∑ i, ‖finBasisCoord V i‖ * ‖Module.finBasis ℂ V i‖

variable {V}

lemma sum_finBasisCoord_smul (v : V) : ∑ i, finBasisCoord V i v • Module.finBasis ℂ V i = v := by
  simp [finBasisCoord, Module.Basis.coord_apply, (Module.finBasis ℂ V).sum_repr v]

lemma finBasisConst_nonneg : 0 ≤ finBasisConst V :=
  Finset.sum_nonneg fun _ _ ↦ by positivity

lemma norm_sum_smul_finBasis_le {s : Fin (Module.finrank ℂ V) → ℂ} {X : ℝ}
    (hs : ∀ i, ‖s i‖ ≤ ‖finBasisCoord V i‖ * X) :
    ‖∑ i, s i • Module.finBasis ℂ V i‖ ≤ finBasisConst V * X := by
  refine (norm_sum_le _ _).trans ?_
  rw [finBasisConst, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  rw [norm_smul]
  calc ‖s i‖ * ‖Module.finBasis ℂ V i‖ ≤ ‖finBasisCoord V i‖ * X * ‖Module.finBasis ℂ V i‖ := by
        gcongr; exact hs i
    _ = _ := by ring

variable (V) in
/-- The constant in the bounds of the Cousin splitting `Complex.exists_cousin_split_bound`. -/
noncomputable def cousinSplitConst : ℝ :=
  2 * (finBasisConst V + 1)

lemma cousinSplitConst_pos : 0 < cousinSplitConst V := by
  have := finBasisConst_nonneg (V := V)
  rw [cousinSplitConst]
  positivity

/-- **Cousin splitting with bounds.** Let `f` be holomorphic on `Ω × P` with values in a
finite-dimensional space `V`, where `Ω` contains the closed rectangle with corners `a`, `b`, and
let `‖f‖ ≤ M` on this rectangle (times `P`). Then `f = f₁ + f₂` on the open rectangle, with `f₁`
holomorphic on the half-plane `{Re z < b.re}` and `f₂` on the half-strip
`{Re z > a.re, a.im < Im z < b.im}`, and both are bounded by `C ℓ M / η` at distance `η` from the
sides they avoid; here `ℓ` is the half-perimeter of the rectangle and `C = cousinSplitConst V`. -/
theorem exists_cousin_split_bound {a b : ℂ} (hre : a.re < b.re) (him : a.im < b.im)
    {Ω : Set ℂ} (hab : Icc a.re b.re ×ℂ Icc a.im b.im ⊆ Ω) {P : Set E} (hP : IsOpen P)
    {f : ℂ × E → V} (hf : DifferentiableOn ℂ f (Ω ×ˢ P)) {M : ℝ}
    (hM : ∀ z ∈ Icc a.re b.re ×ℂ Icc a.im b.im, ∀ w ∈ P, ‖f (z, w)‖ ≤ M) :
    ∃ f₁ f₂ : ℂ × E → V, DifferentiableOn ℂ f₁ ({z : ℂ | z.re < b.re} ×ˢ P) ∧
      DifferentiableOn ℂ f₂ ((Ioi a.re ×ℂ Ioo a.im b.im) ×ˢ P) ∧
      (∀ z ∈ Ioo a.re b.re ×ℂ Ioo a.im b.im, ∀ w ∈ P, f (z, w) = f₁ (z, w) + f₂ (z, w)) ∧
      (∀ η > 0, ∀ z : ℂ, z.re + η ≤ b.re → ∀ w ∈ P,
        ‖f₁ (z, w)‖ ≤ cousinSplitConst V * ((b.re - a.re) + (b.im - a.im)) * M / η) ∧
      (∀ η > 0, ∀ z : ℂ, a.re + η ≤ z.re → a.im + η ≤ z.im → z.im + η ≤ b.im → ∀ w ∈ P,
        ‖f₂ (z, w)‖ ≤ cousinSplitConst V * ((b.re - a.re) + (b.im - a.im)) * M / η) := by
  set bv := Module.finBasis ℂ V
  set c := finBasisCoord V
  set g : Fin (Module.finrank ℂ V) → ℂ × E → ℂ := fun i p ↦ c i (f p) with hg_def
  have hg : ∀ i, DifferentiableOn ℂ (g i) (Ω ×ˢ P) := fun i ↦
    (c i).differentiable.comp_differentiableOn hf
  have hgM : ∀ i, ∀ w ∈ P, ∀ ζ ∈ Icc a.re b.re ×ℂ Icc a.im b.im,
      ‖g i (ζ, w)‖ ≤ ‖c i‖ * M := fun i w hw ζ hζ ↦
    ((c i).le_opNorm _).trans (by gcongr; exact hM ζ hζ w hw)
  set ℓ := (b.re - a.re) + (b.im - a.im)
  have hℓ : 0 ≤ ℓ := by linarith
  set C := cousinSplitConst V
  -- the bound in terms of the basis constant
  have hfin : ∀ {s : Fin (Module.finrank ℂ V) → ℂ} {X : ℝ}, 0 ≤ X →
      (∀ i, ‖s i‖ ≤ ‖c i‖ * (2 * X)) → ‖∑ i, s i • bv i‖ ≤ C * X := by
    intro s X hX hs
    refine (norm_sum_smul_finBasis_le hs).trans ?_
    have := finBasisConst_nonneg (V := V)
    simp only [C, cousinSplitConst]
    nlinarith
  refine ⟨fun p ↦ ∑ i, cauchyRight (g i) a b p • bv i,
    fun p ↦ ∑ i, (cauchyBottom (g i) a b p + cauchyTop (g i) a b p +
      cauchyLeft (g i) a b p) • bv i, ?_, ?_, ?_, ?_, ?_⟩
  · refine DifferentiableOn.fun_sum fun i _ ↦ DifferentiableOn.smul_const ?_ _
    refine (differentiableOn_cauchyRight hab hP (hg i) hre.le him.le).mono
      (prod_mono (fun z hz ↦ ?_) subset_rfl)
    rintro ⟨y, -, rfl⟩
    simp at hz
  · refine DifferentiableOn.fun_sum fun i _ ↦ DifferentiableOn.smul_const ?_ _
    refine (((differentiableOn_cauchyBottom hab hP (hg i) hre.le him.le).mono
      (prod_mono (fun z hz ↦ ?_) subset_rfl)).add
      ((differentiableOn_cauchyTop hab hP (hg i) hre.le him.le).mono
      (prod_mono (fun z hz ↦ ?_) subset_rfl))).add
      ((differentiableOn_cauchyLeft hab hP (hg i) hre.le him.le).mono
      (prod_mono (fun z hz ↦ ?_) subset_rfl))
    all_goals
      rintro ⟨t, -, rfl⟩
      simp [mem_reProdIm] at hz
  · intro z hz w hw
    rw [← Finset.sum_add_distrib]
    conv_lhs => rw [← sum_finBasisCoord_smul (f (z, w))]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← add_smul]
    congr 1
    rw [show finBasisCoord V i (f (z, w)) = g i (z, w) from rfl,
      ← sum_cauchySides_of_mem hab (hg i) hz hw]
    ring
  · intro η hη z hz w hw
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM a ⟨⟨le_rfl, hre.le⟩, le_rfl, him.le⟩ w hw)
    have : C * ℓ * M / η = C * (ℓ * M / η) := by ring
    rw [this]
    refine hfin (by positivity) fun i ↦ ?_
    refine (norm_cauchyRight_le hre.le him.le (hgM i w hw) hη hz).trans ?_
    rw [div_le_iff₀ hη]
    have : 0 ≤ ‖c i‖ * M := by positivity
    have e : ‖c i‖ * (2 * (ℓ * M / η)) * η = 2 * ℓ * (‖c i‖ * M) := by field_simp
    rw [e]
    nlinarith
  · intro η hη z h1 h2 h3 w hw
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM a ⟨⟨le_rfl, hre.le⟩, le_rfl, him.le⟩ w hw)
    have : C * ℓ * M / η = C * (ℓ * M / η) := by ring
    rw [this]
    refine hfin (by positivity) fun i ↦ ?_
    have e1 := norm_cauchyBottom_le hre.le him.le (hgM i w hw) hη h2
    have e2 := norm_cauchyTop_le hre.le him.le (hgM i w hw) hη h3
    have e3 := norm_cauchyLeft_le hre.le him.le (hgM i w hw) hη h1
    refine (norm_add_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans ?_)
    have : 0 ≤ ‖c i‖ * M := by positivity
    have e : ‖c i‖ * (2 * (ℓ * M / η)) = 2 * ℓ * (‖c i‖ * M) / η := by field_simp
    rw [e]
    calc _ ≤ (b.re - a.re) * (‖c i‖ * M) / η + (b.re - a.re) * (‖c i‖ * M) / η +
          (b.im - a.im) * (‖c i‖ * M) / η := by gcongr
      _ = (2 * (b.re - a.re) + (b.im - a.im)) * (‖c i‖ * M) / η := by ring
      _ ≤ 2 * ℓ * (‖c i‖ * M) / η := by
          gcongr
          simp only [ℓ]
          linarith

/-- **Weierstrass' theorem** for functions with values in a finite-dimensional space. -/
theorem differentiableOn_of_tendstoLocallyUniformlyOn_of_finiteDimensional {ι : Type*}
    {l : Filter ι} [l.NeBot] {U : Set E} (hU : IsOpen U) {F : ι → E → V} {G : E → V}
    (hF : ∀ n, DifferentiableOn ℂ (F n) U) (hFG : TendstoLocallyUniformlyOn F G l U) :
    DifferentiableOn ℂ G U := by
  have hG : G = fun x ↦ ∑ i, finBasisCoord V i (G x) • Module.finBasis ℂ V i :=
    funext fun x ↦ (sum_finBasisCoord_smul (G x)).symm
  rw [hG]
  refine DifferentiableOn.fun_sum fun i _ ↦ DifferentiableOn.smul_const ?_ _
  exact differentiableOn_of_tendstoLocallyUniformlyOn hU
    (fun n ↦ (finBasisCoord V i).differentiable.comp_differentiableOn (hF n))
    ((finBasisCoord V i).uniformContinuous.comp_tendstoLocallyUniformlyOn hFG)

/-- **Runge approximation on a rectangle** for functions with values in a finite-dimensional
space, with holomorphic parameters. -/
theorem exists_approx_entire_of_rect_of_finiteDimensional {a b : ℂ} (hre : a.re < b.re)
    (him : a.im < b.im) {Ω : Set ℂ} (hab : Icc a.re b.re ×ℂ Icc a.im b.im ⊆ Ω) {P : Set E}
    (hP : IsOpen P) {f : ℂ × E → V} (hf : DifferentiableOn ℂ f (Ω ×ˢ P)) {K : Set ℂ}
    (hK : IsCompact K) (hKab : K ⊆ Ioo a.re b.re ×ℂ Ioo a.im b.im) {L : Set E}
    (hL : IsCompact L) (hLP : L ⊆ P) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℂ × E → V, DifferentiableOn ℂ g (univ ×ˢ P) ∧
      ∀ z ∈ K, ∀ w ∈ L, ‖f (z, w) - g (z, w)‖ ≤ ε := by
  set bv := Module.finBasis ℂ V
  set c := finBasisCoord V
  set B := ∑ i, ‖bv i‖ + 1
  have hB : 0 < B := by positivity
  have hε' : 0 < ε / B := by positivity
  have happrox := fun i ↦ exists_approx_entire_of_rect hre him hab hP
    ((c i).differentiable.comp_differentiableOn hf) hK hKab hL hLP hε'
  choose g hg hgf using happrox
  refine ⟨fun p ↦ ∑ i, g i p • bv i,
    DifferentiableOn.fun_sum fun i _ ↦ (hg i).smul_const _, fun z hz w hw ↦ ?_⟩
  have hsum : f (z, w) - ∑ i, g i (z, w) • bv i =
      ∑ i, (c i (f (z, w)) - g i (z, w)) • bv i := by
    simp only [sub_smul, Finset.sum_sub_distrib, c, bv, sum_finBasisCoord_smul]
  rw [hsum]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i, ‖(c i (f (z, w)) - g i (z, w)) • bv i‖ ≤ ∑ i, ε / B * ‖bv i‖ := by
        refine Finset.sum_le_sum fun i _ ↦ ?_
        rw [norm_smul]
        gcongr
        exact hgf i z hz w hw
    _ = ε / B * (B - 1) := by rw [← Finset.mul_sum]; simp only [B]; ring
    _ ≤ ε := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hB]
        nlinarith

end Vector

end Complex
