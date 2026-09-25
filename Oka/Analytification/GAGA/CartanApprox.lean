/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Oka.Analytification.GAGA.CartanNearOne

/-!
# Approximation of invertible holomorphic functions by entire ones

Let `𝔸` be a finite-dimensional normed `ℂ`-algebra and let `F` be holomorphic with invertible
values near `R × L`, where `R ⊆ ℂ` is a closed rectangle and `L` a compact set of parameters. Then
`F` is approximated near `R × L` by functions `G` which are holomorphic with invertible values on
`ℂ × P` (`P ⊇ L` open), in the sense that `F G⁻¹` is uniformly close to `1`.

The proof: the invertible functions on a compact set `K` which are uniform limits of such `G`
form a closed subgroup of the units of the Banach algebra `C(K, 𝔸)`. It contains `exp A` for
every `A` holomorphic near `K` (Runge approximation of `A`). The dilations
`F_t (z, w) = F (p + t (z - p), w)`, `t ∈ [0, 1]`, connect `F` with `F_0`, which does not depend on
`z`, and `F_t⁻¹ F_s = exp (log (F_t⁻¹ F_s))` is such an exponential for `s` close to `t`, with a
holomorphic logarithm `Complex.exists_local_log` near `1`.

## Main definitions

- `ContinuousMap.unitOfIsUnit`: a continuous map with invertible values, as a unit of `C(X, 𝔸)`.
- `Complex.holomorphicUnits K P`: the units of `C(K, 𝔸)` which are restrictions of functions
  holomorphic with invertible values on `ℂ × P`.

## Main results

- `Complex.exists_local_log`: a holomorphic logarithm near `1`.
- `Complex.exists_approx_isUnit`: **approximation by entire invertible functions.**
-/

open Set Filter Metric NormedSpace
open scoped Topology Ring

section Log

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [CompleteSpace 𝔸]

/-- A holomorphic logarithm near `1` in a complex Banach algebra. -/
theorem Complex.exists_local_log : ∃ r > 0, ∃ g : 𝔸 → 𝔸, ∀ y ∈ ball (1 : 𝔸) r,
    NormedSpace.exp (g y) = y ∧ DifferentiableAt ℂ g y := by
  have hc : ContDiffAt ℂ 1 (NormedSpace.exp : 𝔸 → 𝔸) 0 :=
    (exp_analytic (𝕂 := ℂ) (0 : 𝔸)).contDiffAt
  have hf' : HasFDerivAt (NormedSpace.exp : 𝔸 → 𝔸)
      ((ContinuousLinearEquiv.refl ℂ 𝔸 : 𝔸 →L[ℂ] 𝔸)) 0 :=
    hasFDerivAt_exp_zero (𝕂 := ℂ) (𝔸 := 𝔸)
  have hn : (1 : WithTop ℕ∞) ≠ 0 := one_ne_zero
  set e := ContDiffAt.toOpenPartialHomeomorph NormedSpace.exp hc hf' hn
  have hg := ContDiffAt.to_localInverse hc hf' hn
  rw [NormedSpace.exp_zero] at hg
  have h1 : ∀ᶠ y in 𝓝 (1 : 𝔸), y ∈ e.target := by
    have := ContDiffAt.image_mem_toOpenPartialHomeomorph_target hc hf' hn
    rw [NormedSpace.exp_zero] at this
    exact e.open_target.mem_nhds this
  have h2 : ∀ᶠ y in 𝓝 (1 : 𝔸), ContDiffAt ℂ 1 (ContDiffAt.localInverse hc hf' hn) y :=
    hg.eventually (by simp)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 (h1.and h2)
  refine ⟨r, hr, ContDiffAt.localInverse hc hf' hn,
    fun y hy ↦ ⟨?_, (hball y hy).2.differentiableAt one_ne_zero⟩⟩
  exact e.right_inv (hball y hy).1

lemma NormedSpace.continuous_exp_of_complex : Continuous (NormedSpace.exp : 𝔸 → 𝔸) :=
  continuous_iff_continuousAt.2 fun x ↦ (exp_analytic (𝕂 := ℂ) x).continuousAt

lemma NormedSpace.isUnit_exp_of_complex (x : 𝔸) : IsUnit (NormedSpace.exp x) := by
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℂ 𝔸
  exact isUnit_exp x

end Log

namespace ContinuousMap

variable {X : Type*} [TopologicalSpace X] {𝔸 : Type*} [NormedRing 𝔸]

/-- A continuous map with invertible values, as a unit of `C(X, 𝔸)`. -/
noncomputable def unitOfIsUnit [CompleteSpace 𝔸] (f : C(X, 𝔸)) (hf : ∀ x, IsUnit (f x)) :
    C(X, 𝔸)ˣ where
  val := f
  inv := ⟨fun x ↦ (f x)⁻¹ʳ, continuous_iff_continuousAt.2 fun x ↦ by
    have := NormedRing.inverse_continuousAt (hf x).unit
    rw [IsUnit.unit_spec] at this
    exact this.comp f.continuous.continuousAt⟩
  val_inv := by ext x; simp [Ring.mul_inverse_cancel _ (hf x)]
  inv_val := by ext x; simp [Ring.inverse_mul_cancel _ (hf x)]

@[simp]
lemma val_unitOfIsUnit [CompleteSpace 𝔸] (f : C(X, 𝔸)) (hf : ∀ x, IsUnit (f x)) :
    (unitOfIsUnit f hf : C(X, 𝔸)) = f :=
  rfl

lemma isUnit_units_apply (u : C(X, 𝔸)ˣ) (x : X) : IsUnit ((u : C(X, 𝔸)) x) :=
  ⟨⟨(u : C(X, 𝔸)) x, (↑u⁻¹ : C(X, 𝔸)) x,
    by rw [← mul_apply, Units.mul_inv]; rfl, by rw [← mul_apply, Units.inv_mul]; rfl⟩, rfl⟩

lemma units_inv_apply (u : C(X, 𝔸)ˣ) (x : X) :
    (↑u⁻¹ : C(X, 𝔸)) x = ((u : C(X, 𝔸)) x)⁻¹ʳ := by
  have h : ((u : C(X, 𝔸)) x) * (↑u⁻¹ : C(X, 𝔸)) x = 1 := by
    rw [← mul_apply, Units.mul_inv]; rfl
  rw [← Ring.inverse_mul_cancel_left _ ((↑u⁻¹ : C(X, 𝔸)) x) (isUnit_units_apply u x), h,
    mul_one]

end ContinuousMap

namespace Complex

open ContinuousMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [CompleteSpace 𝔸]

variable (𝔸) in
/-- The units of `C(K, 𝔸)` which are restrictions of functions holomorphic with invertible values
on `ℂ × P`. -/
def holomorphicUnits (K : Set (ℂ × E)) (P : Set E) : Subgroup C(K, 𝔸)ˣ where
  carrier := {u | ∃ G : ℂ × E → 𝔸, DifferentiableOn ℂ G (univ ×ˢ P) ∧
    (∀ x ∈ univ ×ˢ P, IsUnit (G x)) ∧ ∀ x : K, (u : C(K, 𝔸)) x = G x}
  one_mem' := ⟨1, differentiableOn_const 1, fun _ _ ↦ isUnit_one, fun _ ↦ rfl⟩
  mul_mem' := by
    rintro u v ⟨G, hG, hGu, hGe⟩ ⟨G', hG', hG'u, hG'e⟩
    refine ⟨G * G', hG.mul hG', fun x hx ↦ (hGu x hx).mul (hG'u x hx), fun x ↦ ?_⟩
    simp [hGe, hG'e]
  inv_mem' := by
    rintro u ⟨G, hG, hGu, hGe⟩
    exact ⟨fun x ↦ (G x)⁻¹ʳ, hG.inverse hGu, fun x hx ↦ (hGu x hx).ringInverse,
      fun x ↦ by rw [units_inv_apply, hGe]⟩

section Closure

variable [FiniteDimensional ℂ 𝔸]

/-- `exp A` lies in the closure of `holomorphicUnits 𝔸 K P` if `A` is holomorphic on `Ω × P`,
where `Ω` contains a closed rectangle whose interior contains the compact set `Kz`, and
`K ⊆ Kz × L` with `L ⊆ P` compact. -/
theorem unitOfIsUnit_exp_mem_topologicalClosure {K : Set (ℂ × E)} [CompactSpace K] {a b : ℂ}
    (hre : a.re < b.re) (him : a.im < b.im) {Ω : Set ℂ}
    (hab : Icc a.re b.re ×ℂ Icc a.im b.im ⊆ Ω) {P : Set E} (hP : IsOpen P) {Kz : Set ℂ}
    (hKz : IsCompact Kz) (hKzab : Kz ⊆ Ioo a.re b.re ×ℂ Ioo a.im b.im) {L : Set E}
    (hL : IsCompact L) (hLP : L ⊆ P) (hK : K ⊆ Kz ×ˢ L) {A : ℂ × E → 𝔸}
    (hA : DifferentiableOn ℂ A (Ω ×ˢ P)) (f : C(K, 𝔸)) (hf : ∀ x : K, f x = A x) :
    unitOfIsUnit ((⟨NormedSpace.exp, continuous_exp_of_complex⟩ : C(𝔸, 𝔸)).comp f)
      (fun _ ↦ isUnit_exp_of_complex _) ∈ (holomorphicUnits 𝔸 K P).topologicalClosure := by
  set expC : C(𝔸, 𝔸) := ⟨NormedSpace.exp, continuous_exp_of_complex⟩
  have hε : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n ↦ by positivity
  choose B hB hBe using fun n : ℕ ↦ exists_approx_entire_of_rect_of_finiteDimensional hre him
    hab hP hA hKz hKzab hL hLP (hε n)
  have hKP : ∀ x : K, (x : ℂ × E) ∈ univ ×ˢ P := fun x ↦ ⟨mem_univ _, hLP (hK x.2).2⟩
  set fn : ℕ → C(K, 𝔸) := fun n ↦ ⟨fun x ↦ B n x,
    (hB n).continuousOn.comp_continuous continuous_subtype_val hKP⟩
  have hconv : Tendsto fn atTop (𝓝 f) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun _ ↦ dist_nonneg) (fun n ↦ ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat
    rw [ContinuousMap.dist_le (hε n).le]
    intro x
    obtain ⟨hz, hw⟩ := hK x.2
    rw [dist_eq_norm, hf x, norm_sub_rev]
    exact hBe n x.1.1 hz x.1.2 hw
  have hmem : ∀ n, unitOfIsUnit (expC.comp (fn n)) (fun _ ↦ isUnit_exp_of_complex _) ∈
      holomorphicUnits 𝔸 K P := fun n ↦
    ⟨fun x ↦ NormedSpace.exp (B n x), fun x hx ↦
      ((exp_analytic (𝕂 := ℂ) _).differentiableAt.comp_differentiableWithinAt x (hB n x hx)),
      fun _ _ ↦ isUnit_exp_of_complex _, fun _ ↦ rfl⟩
  have hlim : Tendsto (fun n ↦ unitOfIsUnit (expC.comp (fn n)) (fun _ ↦ isUnit_exp_of_complex _))
      atTop
      (𝓝 (unitOfIsUnit (expC.comp f) (fun _ ↦ isUnit_exp_of_complex _))) := by
    rw [Units.isOpenEmbedding_val.isEmbedding.tendsto_nhds_iff]
    exact ((ContinuousMap.continuous_postcomp expC).tendsto f).comp hconv
  rw [← SetLike.mem_coe, Subgroup.topologicalClosure_coe]
  exact mem_closure_of_tendsto hlim (Eventually.of_forall hmem)

end Closure

section Geometry

/-- The closed rectangle `[p.re - s, q.re + s] × [p.im - s, q.im + s]`. -/
def closedRectNhd (p q : ℂ) (s : ℝ) : Set ℂ :=
  Icc (p.re - s) (q.re + s) ×ℂ Icc (p.im - s) (q.im + s)

variable {p q z : ℂ} {s t c : ℝ}

lemma isCompact_closedRectNhd : IsCompact (closedRectNhd p q s) :=
  isCompact_Icc.reProdIm isCompact_Icc

lemma rectNhd_subset_closedRectNhd : rectNhd p q s ⊆ closedRectNhd p q s :=
  fun _ hz ↦ ⟨Ioo_subset_Icc_self hz.1, Ioo_subset_Icc_self hz.2⟩

lemma closedRectNhd_subset_rectNhd (h : s < t) : closedRectNhd p q s ⊆ rectNhd p q t :=
  fun _ hz ↦ ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, by linarith [hz.2.1],
    by linarith [hz.2.2]⟩

private lemma convex_comb_mem_Icc {l u x y : ℝ} (hx : x ∈ Icc l u) (hy : y ∈ Icc l u)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) : x + c * (y - x) ∈ Icc l u :=
  ⟨by nlinarith [hx.1, hy.1], by nlinarith [hx.2, hy.2]⟩

private lemma convex_comb_mem_Ioo {l u x y : ℝ} (hx : x ∈ Ioo l u) (hy : y ∈ Ioo l u)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) : x + c * (y - x) ∈ Ioo l u := by
  obtain ⟨h1, h2⟩ := hx
  obtain ⟨h3, h4⟩ := hy
  rcases le_total x y with h | h
  · exact ⟨by nlinarith, by nlinarith⟩
  · exact ⟨by nlinarith, by nlinarith⟩

lemma add_mul_sub_mem_closedRectNhd (hre : p.re ≤ q.re) (him : p.im ≤ q.im) (hs : 0 ≤ s)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hz : z ∈ closedRectNhd p q s) :
    p + (c : ℂ) * (z - p) ∈ closedRectNhd p q s := by
  have hre' : p.re ∈ Icc (p.re - s) (q.re + s) := ⟨by linarith, by linarith⟩
  have him' : p.im ∈ Icc (p.im - s) (q.im + s) := ⟨by linarith, by linarith⟩
  refine ⟨?_, ?_⟩
  · simpa using convex_comb_mem_Icc hre' hz.1 hc0 hc1
  · simpa using convex_comb_mem_Icc him' hz.2 hc0 hc1

lemma add_mul_sub_mem_rectNhd (hre : p.re ≤ q.re) (him : p.im ≤ q.im) (hs : 0 < s)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hz : z ∈ rectNhd p q s) :
    p + (c : ℂ) * (z - p) ∈ rectNhd p q s := by
  have hre' : p.re ∈ Ioo (p.re - s) (q.re + s) := ⟨by linarith, by linarith⟩
  have him' : p.im ∈ Ioo (p.im - s) (q.im + s) := ⟨by linarith, by linarith⟩
  refine ⟨?_, ?_⟩
  · simpa using convex_comb_mem_Ioo hre' hz.1 hc0 hc1
  · simpa using convex_comb_mem_Ioo him' hz.2 hc0 hc1

private lemma abs_sub_clamp_le {l u x : ℝ} (hs : 0 ≤ s) (hlu : l ≤ u)
    (hx : x ∈ Icc (l - s) (u + s)) : |x - max l (min x u)| ≤ s := by
  obtain ⟨h1, h2⟩ := hx
  rcases le_total x u with h | h <;> rcases le_total l x with h' | h'
  · rw [min_eq_left h, max_eq_right h', sub_self, abs_zero]; exact hs
  · rw [min_eq_left h, max_eq_left h', abs_sub_le_iff]; constructor <;> linarith
  · rw [min_eq_right h, max_eq_right hlu, abs_sub_le_iff]; constructor <;> linarith
  · rw [min_eq_right h, max_eq_right hlu, abs_sub_le_iff]; constructor <;> linarith

lemma closedRectNhd_subset_thickening (hre : p.re ≤ q.re) (him : p.im ≤ q.im) (hs : 0 ≤ s)
    {δ : ℝ} (hδ : 2 * s < δ) : closedRectNhd p q s ⊆ thickening δ (closedRectNhd p q 0) := by
  intro z hz
  rw [mem_thickening_iff]
  refine ⟨⟨max p.re (min z.re q.re), max p.im (min z.im q.im)⟩, ⟨?_, ?_⟩, ?_⟩
  · simp only [sub_zero, add_zero]
    exact ⟨le_max_left _ _, max_le hre (min_le_right _ _)⟩
  · simp only [sub_zero, add_zero]
    exact ⟨le_max_left _ _, max_le him (min_le_right _ _)⟩
  · rw [dist_eq_norm]
    refine (norm_le_abs_re_add_abs_im _).trans_lt ?_
    have e1 := abs_sub_clamp_le hs hre hz.1
    have e2 := abs_sub_clamp_le hs him hz.2
    simp only [sub_re, sub_im]
    linarith

end Geometry

section Approx

variable [FiniteDimensional ℂ 𝔸]

/-- **Approximation by entire invertible functions.** Let `F` be holomorphic with invertible
values on an open `U ⊇ R × L`, where `R` is the closed rectangle with corners `p`, `q` and `L` is
compact. Then there are `ρ > 0` and an open `P ⊇ L` with `R_ρ × P ⊆ U` (`R_ρ = rectNhd p q ρ`)
such that for every `θ > 0` there is `G` holomorphic with invertible values on `ℂ × P` with
`‖F G⁻¹ - 1‖ ≤ θ` on `R_ρ × P`. -/
theorem exists_approx_isUnit {p q : ℂ} (hre : p.re ≤ q.re) (him : p.im ≤ q.im) {L : Set E}
    (hL : IsCompact L) {U : Set (ℂ × E)} (hU : IsOpen U)
    (hRL : closedRectNhd p q 0 ×ˢ L ⊆ U) {F : ℂ × E → 𝔸} (hF : DifferentiableOn ℂ F U)
    (hFu : ∀ x ∈ U, IsUnit (F x)) :
    ∃ ρ > 0, ∃ P : Set E, IsOpen P ∧ L ⊆ P ∧ rectNhd p q ρ ×ˢ P ⊆ U ∧ ∀ θ > 0,
      ∃ G : ℂ × E → 𝔸, DifferentiableOn ℂ G (univ ×ˢ P) ∧ (∀ x ∈ univ ×ˢ P, IsUnit (G x)) ∧
        ∀ x ∈ rectNhd p q ρ ×ˢ P, ‖F x * (G x)⁻¹ʳ - 1‖ ≤ θ := by
  -- the neighbourhoods
  obtain ⟨u, v, hu, hv, hRu, hLv, huv⟩ :=
    generalized_tube_lemma isCompact_closedRectNhd hL hU hRL
  obtain ⟨δ, hδ, hδu⟩ := isCompact_closedRectNhd.exists_thickening_subset_open hu hRu
  set ρ := δ / 8 with hρ_def
  have hρ : 0 < ρ := by positivity
  obtain ⟨P₂, hP₂o, hLP₂, hP₂v, hP₂c⟩ := exists_open_between_and_isCompact_closure hL hv hLv
  obtain ⟨P, hPo, hLP, hPP₂, hPc⟩ := exists_open_between_and_isCompact_closure hL hP₂o hLP₂
  set T := closedRectNhd p q (3 * ρ) ×ˢ closure P₂ with hT_def
  have hTc : IsCompact T := isCompact_closedRectNhd.prod hP₂c
  have hTU : T ⊆ U := fun x hx ↦ huv ⟨hδu (closedRectNhd_subset_thickening hre him
    (by positivity) (by linarith) hx.1), hP₂v hx.2⟩
  set O := rectNhd p q (3 * ρ) ×ˢ P₂ with hO_def
  have hOT : O ⊆ T := prod_mono rectNhd_subset_closedRectNhd subset_closure
  set S := closedRectNhd p q ρ ×ˢ closure P with hS_def
  have hSc : IsCompact S := isCompact_closedRectNhd.prod hPc
  haveI : CompactSpace S := isCompact_iff_compactSpace.1 hSc
  have hSO : S ⊆ O := prod_mono (closedRectNhd_subset_rectNhd (by linarith)) hPP₂
  have hpR : p ∈ closedRectNhd p q (3 * ρ) :=
    ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  -- the dilations `F_t`
  set cl : ℝ → ℝ := fun t ↦ max 0 (min t 1) with hcl_def
  have hcl0 : ∀ t, 0 ≤ cl t := fun t ↦ le_max_left _ _
  have hcl1 : ∀ t, cl t ≤ 1 := fun t ↦ max_le zero_le_one (min_le_right _ _)
  have hclc : Continuous cl := continuous_const.max (continuous_id.min continuous_const)
  set dil : ℝ → ℂ × E → ℂ × E := fun t x ↦ (p + (cl t : ℂ) * (x.1 - p), x.2) with hdil_def
  have hdilT : ∀ t, ∀ x ∈ T, dil t x ∈ T := fun t x hx ↦
    ⟨add_mul_sub_mem_closedRectNhd hre him (by positivity) (hcl0 t) (hcl1 t) hx.1, hx.2⟩
  have hdilO : ∀ t, ∀ x ∈ O, dil t x ∈ O := fun t x hx ↦
    ⟨add_mul_sub_mem_rectNhd hre him (by positivity) (hcl0 t) (hcl1 t) hx.1, hx.2⟩
  set Ft : ℝ → ℂ × E → 𝔸 := fun t x ↦ F (dil t x) with hFt_def
  have hdilc : Continuous fun y : ℝ × (ℂ × E) ↦ dil y.1 y.2 := by
    simp only [hdil_def]
    fun_prop
  have hFt_cont : ContinuousOn (fun y : ℝ × (ℂ × E) ↦ Ft y.1 y.2) (univ ×ˢ T) :=
    hF.continuousOn.comp hdilc.continuousOn fun y hy ↦ hTU (hdilT y.1 y.2 hy.2)
  have hFt_diff : ∀ t, DifferentiableOn ℂ (Ft t) O := fun t ↦
    hF.comp (by simp only [hdil_def]; fun_prop : Differentiable ℂ (dil t)).differentiableOn
      fun x hx ↦ hTU (hOT (hdilO t x hx))
  have hFt_unit : ∀ t, ∀ x ∈ T, IsUnit (Ft t x) := fun t x hx ↦ hFu _ (hTU (hdilT t x hx))
  have hFt_contT : ∀ t, ContinuousOn (Ft t) T := fun t ↦
    hFt_cont.comp (continuous_const.prodMk continuous_id).continuousOn
      fun x hx ↦ ⟨mem_univ _, hx⟩
  have hST : ∀ x : S, (x : ℂ × E) ∈ T := fun x ↦ hOT (hSO x.2)
  set φ : ℝ → C(S, 𝔸)ˣ := fun t ↦ unitOfIsUnit ⟨fun x ↦ Ft t x,
    (hFt_contT t).comp_continuous continuous_subtype_val hST⟩ fun x ↦ hFt_unit t x (hST x)
    with hφ_def
  set 𝒢 := (holomorphicUnits 𝔸 S P₂).topologicalClosure
  obtain ⟨r, hr, g, hg⟩ := exists_local_log (𝔸 := 𝔸)
  -- `F_t⁻¹ F_s` is an exponential for `s` close to `t`
  have hloc : ∀ t, ∀ᶠ s in 𝓝 t, (φ t)⁻¹ * φ s ∈ 𝒢 := by
    intro t
    set Φ : ℝ × (ℂ × E) → 𝔸 := fun y ↦ (Ft t y.2)⁻¹ʳ * Ft y.1 y.2
    have hinv : ContinuousOn (fun y : ℝ × (ℂ × E) ↦ (Ft t y.2)⁻¹ʳ) (univ ×ˢ T) := by
      intro y hy
      have h1 := NormedRing.inverse_continuousAt (hFt_unit t y.2 hy.2).unit
      rw [IsUnit.unit_spec] at h1
      exact ContinuousAt.comp_continuousWithinAt (f := fun y : ℝ × (ℂ × E) ↦ Ft t y.2) (x := y) h1
        ((hFt_contT t).comp continuousOn_snd (fun y hy ↦ hy.2) y hy)
    have hΦc : ContinuousOn Φ (univ ×ˢ T) := hinv.mul hFt_cont
    have hnear : ∀ᶠ s in 𝓝 t, ∀ y ∈ T, y ∈ T → ‖Φ (s, y) - 1‖ < r := by
      refine hTc.eventually_forall_of_forall_eventually fun y hy ↦ ?_
      have hcw := hΦc (t, y) ⟨mem_univ _, hy⟩
      rw [ContinuousWithinAt, show Φ (t, y) = 1 from
        Ring.inverse_mul_cancel _ (hFt_unit t y hy)] at hcw
      have h2 := eventually_nhdsWithin_iff.1 (hcw.eventually (ball_mem_nhds (1 : 𝔸) hr))
      filter_upwards [h2] with z hz hzT
      have := hz ⟨mem_univ _, hzT⟩
      rwa [dist_eq_norm] at this
    filter_upwards [hnear] with s hs
    set Ψ : ℂ × E → 𝔸 := fun x ↦ (Ft t x)⁻¹ʳ * Ft s x
    have hΨO : ∀ x ∈ O, Ψ x ∈ ball (1 : 𝔸) r := fun x hx ↦ by
      rw [mem_ball, dist_eq_norm]
      exact hs x (hOT hx) (hOT hx)
    have hΨd : DifferentiableOn ℂ Ψ O :=
      ((hFt_diff t).inverse fun x hx ↦ hFt_unit t x (hOT hx)).mul (hFt_diff s)
    set A : ℂ × E → 𝔸 := fun x ↦ g (Ψ x)
    have hAd : DifferentiableOn ℂ A O := fun x hx ↦
      (hg _ (hΨO x hx)).2.comp_differentiableWithinAt x (hΨd x hx)
    set fA : C(S, 𝔸) := ⟨fun x ↦ A x,
      hAd.continuousOn.comp_continuous continuous_subtype_val fun x ↦ hSO x.2⟩
    have key := unitOfIsUnit_exp_mem_topologicalClosure (K := S)
      (a := ⟨p.re - 2 * ρ, p.im - 2 * ρ⟩) (b := ⟨q.re + 2 * ρ, q.im + 2 * ρ⟩)
      (show p.re - 2 * ρ < q.re + 2 * ρ by linarith)
      (show p.im - 2 * ρ < q.im + 2 * ρ by linarith) (Ω := rectNhd p q (3 * ρ))
      (closedRectNhd_subset_rectNhd (by linarith)) hP₂o isCompact_closedRectNhd
      (closedRectNhd_subset_rectNhd (by linarith)) hPc hPP₂ subset_rfl hAd fA (fun _ ↦ rfl)
    convert key using 1
    ext x
    simp only [Units.val_mul, ContinuousMap.mul_apply, units_inv_apply, hφ_def,
      val_unitOfIsUnit, ContinuousMap.coe_mk, ContinuousMap.comp_apply, fA, A]
    exact ((hg _ (hΨO x (hSO x.2))).1).symm
  -- connectedness of `ℝ`
  have hrel : ∀ s t : ℝ, (φ s)⁻¹ * φ t ∈ 𝒢 := by
    intro s t
    refine PreconnectedSpace.induction₂' (fun s t ↦ (φ s)⁻¹ * φ t ∈ 𝒢) (fun x ↦ ?_)
      ⟨fun a b c hab hbc ↦ ?_⟩ s t
    · filter_upwards [hloc x] with y hy
      refine ⟨hy, ?_⟩
      simpa [mul_inv_rev] using 𝒢.inv_mem hy
    · simpa [mul_assoc] using 𝒢.mul_mem hab hbc
  have h0 : φ 0 ∈ 𝒢 := by
    apply Subgroup.le_topologicalClosure
    refine ⟨fun x ↦ F (p, x.2), ?_, fun x hx ↦ hFu _ (hTU ⟨hpR, subset_closure hx.2⟩),
      fun x ↦ ?_⟩
    · exact hF.comp (by fun_prop : Differentiable ℂ fun x : ℂ × E ↦ (p, x.2)).differentiableOn
        fun x hx ↦ hTU ⟨hpR, subset_closure hx.2⟩
    · simp [hφ_def, hFt_def, hdil_def, hcl_def]
  have h1 : φ 1 ∈ 𝒢 := by simpa using 𝒢.mul_mem h0 (hrel 0 1)
  refine ⟨ρ, hρ, P, hPo, hLP, fun x hx ↦ hTU (hOT ⟨rectNhd_mono (by linarith) hx.1,
    hPP₂ (subset_closure hx.2)⟩), fun θ hθ ↦ ?_⟩
  -- extract an approximation
  set N := {w : C(S, 𝔸)ˣ | ‖(φ 1 : C(S, 𝔸)) * ↑w⁻¹ - 1‖ < θ}
  have hNo : IsOpen N := isOpen_lt
    ((continuous_const.mul (Units.continuous_val.comp continuous_inv)).sub
      continuous_const).norm continuous_const
  have hN1 : φ 1 ∈ N := by simp [N, hθ]
  rw [← SetLike.mem_coe, Subgroup.topologicalClosure_coe] at h1
  obtain ⟨w, hwN, G, hG, hGu, hGe⟩ := mem_closure_iff.1 h1 N hNo hN1
  have hPP₂' : P ⊆ P₂ := subset_closure.trans hPP₂
  refine ⟨G, hG.mono (prod_mono subset_rfl hPP₂'),
    fun x hx ↦ hGu x ⟨hx.1, hPP₂' hx.2⟩, fun x hx ↦ ?_⟩
  have hxS : x ∈ S := ⟨rectNhd_subset_closedRectNhd hx.1, subset_closure hx.2⟩
  have hle := ContinuousMap.norm_coe_le_norm ((φ 1 : C(S, 𝔸)) * (↑w⁻¹ : C(S, 𝔸)) - 1) (⟨x, hxS⟩ : S)
  have e : ((φ 1 : C(S, 𝔸)) * (↑w⁻¹ : C(S, 𝔸)) - 1) (⟨x, hxS⟩ : S) = F x * (G x)⁻¹ʳ - 1 := by
    simp [hφ_def, hFt_def, hdil_def, hcl_def, units_inv_apply, hGe]
  rw [e] at hle
  exact hle.trans hwN.le

end Approx

end Complex
