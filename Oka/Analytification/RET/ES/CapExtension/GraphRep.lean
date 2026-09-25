/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.ES.CapExtension.FibreImage
import Oka.Analytification.RET.ES.CapExtension.LeviFamily
import Oka.Analytic.RiemannExtension
import Oka.Analytification.GAGA.ParametricIntervalIntegral

/-!
# The graph of the evaluation of the sections of the cap

Keep the notation of `Oka/Analytification/RET/ES/CapExtension/FibreImage.lean`, and let `V ⊆ G` be
open and connected, `Z` the zero set of a family of regular pairs `R` on `G`, and suppose that the
sections of the cap with a pole of order `≤ n` are locally finitely generated at the points of
`G ∖ Z`. Let `r` be the maximal dimension of the fibres `E_b`, `b ∈ V ∖ Z`, and `I₀` indices such
that the coordinates on `I₀` identify some `E_{b*}` with `ℂ^r`. At the *good* points `y`, where
the coordinates on `I₀` identify `E_y` with `ℂ^r`
(`ComplexAnalytic.Cap.AnnulusDecomposition.IsGood`), `E_y` is the graph of the matrix
`Φ(y) = (graphFun x e y)` (`ComplexAnalytic.Cap.AnnulusDecomposition.graphFun`).

Near every point of `V ∖ Z` the good points are dense: `V ∖ Z` is connected, and near a point of
`V ∖ Z` with local generators `s` the good points are the points where a maximal minor `δ` of the
evaluation of `s` does not vanish (`ComplexAnalytic.Cap.AnnulusDecomposition.exists_chart`). There,
by Cramer's rule, `Φ = adj / δ` is a quotient of holomorphic functions. By Levi's theorem across
the zero set of `R` (`RegularPairFamily.isQuotRep_of_forall`), `Φ` has a holomorphic denominator
near every point of `V` (`ComplexAnalytic.Cap.AnnulusDecomposition.exists_graph_rep`).
-/

open CategoryTheory Opposite Topology Set Filter Metric Module
open scoped Matrix

universe u

namespace RegularPairFamily

variable {ι : Type*} [Finite ι] {Z : Set (ι → ℂ)}

/-- **A common denominator** for finitely many local quotient representations. -/
theorem exists_common_isQuotRep {κ : Type*} [Finite κ] {f : κ → (ι → ℂ) → ℂ} {z : ι → ℂ}
    (h : ∀ k, IsQuotRep Z (f k) z) :
    ∃ N : Set (ι → ℂ), IsOpen N ∧ z ∈ N ∧ ∃ (c : (ι → ℂ) → ℂ) (Ψ : κ → (ι → ℂ) → ℂ),
      DifferentiableOn ℂ c N ∧ (∀ k, DifferentiableOn ℂ (Ψ k) N) ∧
      interior (N ∩ c ⁻¹' {0}) = ∅ ∧
      ∀ y ∈ N, ∀ k, y ∈ regPts Z (f k) → c y ≠ 0 → f k y = Ψ k y / c y := by
  classical
  have := Fintype.ofFinite ι
  have := Fintype.ofFinite κ
  choose N hN u w hu hw hw0 hf using h
  set N₀ : Set (ι → ℂ) := ⋂ k, interior (N k)
  have hN₀N : ∀ k, N₀ ⊆ N k := fun k ↦ (iInter_subset _ k).trans interior_subset
  have hN₀o : IsOpen N₀ := isOpen_iInter_of_finite fun _ ↦ isOpen_interior
  refine ⟨N₀, hN₀o, mem_iInter.2 fun k ↦ mem_interior_iff_mem_nhds.2 (hN k),
    fun y ↦ ∏ k, w k y, fun k y ↦ u k y * ∏ k' ∈ Finset.univ.erase k, w k' y,
    ComplexAnalytic.Cap.differentiableOn_finsetProd _ fun k _ ↦ (hw k).mono (hN₀N k),
    fun k ↦ ((hu k).mono (hN₀N k)).mul
      (ComplexAnalytic.Cap.differentiableOn_finsetProd _ fun k' _ ↦ (hw k').mono (hN₀N k')),
    interior_inter_preimage_zero_prod_eq_empty Finset.univ
      (fun k _ ↦ ((hw k).mono (hN₀N k)).continuousOn) fun k _ ↦ subset_empty_iff.1
        (hw0 k ▸ interior_mono fun y hy ↦ ⟨hN₀N k hy.1, hy.2⟩), fun y hy k hr hc ↦ ?_⟩
  have hne : ∀ k', w k' y ≠ 0 := fun k' ↦ (Finset.prod_ne_zero_iff.1 hc) k' (Finset.mem_univ _)
  change f k y = u k y * (∏ k' ∈ Finset.univ.erase k, w k' y) / ∏ k, w k y
  rw [hf k y (hN₀N k hy) hr (hne k), ← Finset.mul_prod_erase Finset.univ (fun k' ↦ w k' y)
    (Finset.mem_univ k), mul_div_mul_right _ _
      (Finset.prod_ne_zero_iff.2 fun k' _ ↦ hne k')]

end RegularPairFamily

namespace ComplexAnalytic.Cap.AnnulusDecomposition

open AnalyticSpace BoundedSections Complex.ProjectiveLineBundle AlgebraicGeometry.LocallyRingedSpace
open KummerModel (splitEquiv)

noncomputable section

variable {m : ℕ} {N N₀ : (AnalyticSpace.complexAffineSpace.{u} (m + 1)).Opens} (h₀ : N₀ ≤ N)
  {W : FiniteEtaleOver (space N₀)} {F : WeierstrassForm N N₀}
  (D : AnnulusDecomposition W F.G F.ρ) (n : ℕ) {M : ℕ} (w : Fin M → ℂ) {r : ℕ}
  (I₀ : Fin r → D.EvIdx M)

/-- A point `y` is **good** if the coordinates on `I₀` identify the fibre `E_y` with `ℂ^r`. -/
def IsGood (y : Cm.{u} m) : Prop :=
  Function.Bijective ((D.fibImage h₀ n w y).coordProj I₀)

open Classical in
/-- The entries of the matrix whose graph is the fibre at a good point: the coordinate `x` of the
vector of `E_y` with coordinates `Pi.single e 1` on `I₀`. -/
def graphFun (x : D.EvIdx M) (e : Fin r) (y : Cm.{u} m) : ℂ :=
  if h : D.IsGood h₀ n w I₀ y then Submodule.graphVec h e x else 0

/-- The matrix `(λ(s_{J j})(y)_{I₀ i})_{i j}`. -/
def evalMat {V : (space N).Opens} {K : ℕ} (s : Fin K → W.left.presheaf.obj (op (preim h₀ W V)))
    (J : Fin r → Fin K) (y : Cm.{u} m) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun i j ↦ D.evalVec w (s (J j)) y (I₀ i)

variable {h₀ D n w I₀}

/-- Generators of the sections of the cap restrict to generators. -/
lemma IsCapGenAt.capRestrict {B B' : Set (Cm.{u} m)} {hB : IsOpen B} {hB' : IsOpen B'}
    (hB'B : B' ⊆ B) {K : ℕ}
    {s : Fin K → boundedSubring h₀ W (tubeN N B hB) × (D.ι → Cm.{u} m × ℂ → ℂ)} {b : Cm.{u} m}
    (h : D.IsCapGenAt h₀ n s b) :
    D.IsCapGenAt h₀ n (fun k ↦ D.capRestrict h₀ (tubeN_mono (hV := hB) (hV' := hB') hB'B) (s k))
      b := by
  intro V hV hVB' hbV t ht
  obtain ⟨V', hV'V, hV', hbV', e, he, hrel⟩ := h V hV (hVB'.trans hB'B) hbV t ht
  refine ⟨V', hV'V, hV', hbV', e, he, fun y hy hyV' ↦ ?_⟩
  have hy' : y ∈ preim h₀ W (tubeN N B' hB') := preim_mono h₀ W (tubeN_mono hVB') hy
  rw [hrel y hy hyV']
  exact Finset.sum_congr rfl fun k _ ↦ congrArg (e k (baseOf (pt W y)) * ·)
    (evalFun_map W _ _ hy').symm

lemma differentiableOn_det_evalMat (hwρ : ∀ ν, w ν ∈ overlap F.ρ) {B : Set (Cm.{u} m)}
    {hB : IsOpen B} (hBG : B ⊆ F.G) {K : ℕ}
    (s : Fin K → W.left.presheaf.obj (op (preim h₀ W (tubeN N B hB)))) (J : Fin r → Fin K) :
    DifferentiableOn ℂ (fun y ↦ (D.evalMat h₀ w I₀ s J y).det) B :=
  differentiableOn_det fun i j ↦ (D.differentiableOn_evalVec F.isOpen_G hwρ (s (J j)) (I₀ i)).mono
    fun y hy ↦ ⟨hBG hy, by
      rw [F.mem_img_tubeN hBG, Homeomorph.apply_symm_apply]
      exact ⟨hy, mem_ball_zero_iff.2 (hwρ _).2⟩⟩

/-- **Goodness from a minor**: if the fibre at `y` has dimension at most `r` and a maximal minor on
the rows `I₀` of the evaluation of sections of the cap does not vanish at `y`, then `y` is good. -/
lemma isGood_of_det {B : Set (Cm.{u} m)} {hB : IsOpen B} (hBG : B ⊆ F.G) {K : ℕ}
    {s : Fin K → boundedSubring h₀ W (tubeN N B hB) × (D.ι → Cm.{u} m × ℂ → ℂ)}
    (hs : ∀ k, s k ∈ D.capPole h₀ n (tubeN N B hB) (B ×ˢ ball 0 F.ρ)) {y : Cm.{u} m}
    (hyB : y ∈ B) (hdim : finrank ℂ (D.fibImage h₀ n w y) ≤ r) {J : Fin r → Fin K}
    (hdet : (D.evalMat h₀ w I₀ (fun k ↦ (s k).1.1) J y).det ≠ 0) : D.IsGood h₀ n w I₀ y :=
  Submodule.bijective_coordProj_of_det hdim (fun j ↦ D.evalVec w (s (J j)).1.1 y)
    (fun j ↦ evalVec_mem_fibImage hBG hyB (hs (J j))) hdet

/-- **Cramer's rule** for the graph: at a good point where the minor does not vanish, the vectors
`Φ(y) eₑ` are combinations of the evaluations of the sections. -/
lemma graphVec_eq_sum {B : Set (Cm.{u} m)} {hB : IsOpen B} (hBG : B ⊆ F.G) {K : ℕ}
    {s : Fin K → boundedSubring h₀ W (tubeN N B hB) × (D.ι → Cm.{u} m × ℂ → ℂ)}
    (hs : ∀ k, s k ∈ D.capPole h₀ n (tubeN N B hB) (B ×ˢ ball 0 F.ρ)) {y : Cm.{u} m}
    (hyB : y ∈ B) (hgood : D.IsGood h₀ n w I₀ y) {J : Fin r → Fin K}
    (hdet : (D.evalMat h₀ w I₀ (fun k ↦ (s k).1.1) J y).det ≠ 0) (e : Fin r) :
    Submodule.graphVec hgood e = ∑ j, (D.evalMat h₀ w I₀ (fun k ↦ (s k).1.1) J y)⁻¹ j e •
      D.evalVec w (s (J j)).1.1 y := by
  set A := D.evalMat h₀ w I₀ (fun k ↦ (s k).1.1) J y
  refine Submodule.eq_of_coord_eq hgood (Submodule.graphVec_mem hgood e)
    (Submodule.sum_mem _ fun j _ ↦ Submodule.smul_mem _ _
      (evalVec_mem_fibImage hBG hyB (hs (J j)))) fun i ↦ ?_
  rw [Submodule.graphVec_apply]
  have : (A * A⁻¹) i e = (1 : Matrix (Fin r) (Fin r) ℂ) i e := by
    rw [Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdet)]
  rw [Matrix.mul_apply, Matrix.one_apply] at this
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  rw [← this]
  exact Finset.sum_congr rfl fun j _ ↦ mul_comm _ _

lemma graphFun_eq_div {B : Set (Cm.{u} m)} {hB : IsOpen B} (hBG : B ⊆ F.G) {K : ℕ}
    {s : Fin K → boundedSubring h₀ W (tubeN N B hB) × (D.ι → Cm.{u} m × ℂ → ℂ)}
    (hs : ∀ k, s k ∈ D.capPole h₀ n (tubeN N B hB) (B ×ˢ ball 0 F.ρ)) {y : Cm.{u} m}
    (hyB : y ∈ B) (hgood : D.IsGood h₀ n w I₀ y) {J : Fin r → Fin K}
    (hdet : (D.evalMat h₀ w I₀ (fun k ↦ (s k).1.1) J y).det ≠ 0) (x : D.EvIdx M) (e : Fin r) :
    D.graphFun h₀ n w I₀ x e y =
      (∑ j, (D.evalMat h₀ w I₀ (fun k ↦ (s k).1.1) J y).adjugate j e *
        D.evalVec w (s (J j)).1.1 y x) / (D.evalMat h₀ w I₀ (fun k ↦ (s k).1.1) J y).det := by
  rw [graphFun, dif_pos hgood, graphVec_eq_sum hBG hs hyB hgood hdet e]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  field_simp

variable (R : RegularPairFamily F.G) {V : Set (Cm.{u} m)}

/-- **Local charts of the graph**: near a point `b` of `V ∖ Z` near which there are good points,
local generators `s` of the sections of the cap have a maximal minor `δ` on the rows `I₀` which
does not vanish on any open set, and the points where `δ ≠ 0` are good. -/
theorem exists_chart (hwρ : ∀ ν, w ν ∈ overlap F.ρ)
    (hloc : ∀ b ∈ F.G, b ∉ R.zeroSet → D.CapLocallyFinite h₀ n b) (hVo : IsOpen V)
    (hVG : V ⊆ F.G) (hr : ∀ y ∈ V \ R.zeroSet, finrank ℂ (D.fibImage h₀ n w y) ≤ r)
    {b : Cm.{u} m} (hb : b ∈ V \ R.zeroSet) (hgood : ∀ O ∈ 𝓝 b, ∃ y ∈ O, D.IsGood h₀ n w I₀ y) :
    ∃ (B : Set (Cm.{u} m)) (hB : IsOpen B), b ∈ B ∧ B ⊆ V \ R.zeroSet ∧ Convex ℝ B ∧
      ∃ (K : ℕ) (s : Fin K → boundedSubring h₀ W (tubeN N B hB) × (D.ι → Cm.{u} m × ℂ → ℂ)),
        (∀ k, s k ∈ D.capPole h₀ n (tubeN N B hB) (B ×ˢ ball 0 F.ρ)) ∧
        (∀ b' ∈ B, D.IsCapGenAt h₀ n s b') ∧ ∃ J : Fin r → Fin K,
          interior (B ∩ (fun y ↦ (D.evalMat h₀ w I₀ (fun k ↦ (s k).1.1) J y).det) ⁻¹' {0}) = ∅ ∧
          ∀ y ∈ B, (D.evalMat h₀ w I₀ (fun k ↦ (s k).1.1) J y).det ≠ 0 →
            D.IsGood h₀ n w I₀ y := by
  obtain ⟨B₀, hB₀, -, hbB₀, K, s₀, hs₀, hgen₀⟩ := hloc b (hVG hb.1) hb.2
  have hSo : IsOpen (V \ R.zeroSet) := R.isOpen_diff_zeroSet hVo hVG
  obtain ⟨ε, hε, hεB⟩ := Metric.isOpen_iff.1 (hB₀.inter hSo) b ⟨hbB₀, hb⟩
  have hBB₀ : ball b ε ⊆ B₀ := fun y hy ↦ (hεB hy).1
  have hBS : ball b ε ⊆ V \ R.zeroSet := fun y hy ↦ (hεB hy).2
  have hBG : ball b ε ⊆ F.G := fun y hy ↦ hVG (hBS hy).1
  have hle : tubeN N (ball b ε) isOpen_ball ≤ tubeN N B₀ hB₀ := tubeN_mono hBB₀
  set s := fun k ↦ D.capRestrict h₀ hle (s₀ k)
  have hs : ∀ k, s k ∈ D.capPole h₀ n (tubeN N (ball b ε) isOpen_ball) (ball b ε ×ˢ ball 0 F.ρ) :=
    fun k ↦ D.capRestrict_mem_capPole h₀ hle (prod_mono hBB₀ subset_rfl) (hs₀ k)
  have hgen : ∀ b' ∈ ball b ε, D.IsCapGenAt h₀ n s b' := fun b' hb' ↦
    (hgen₀ b' (hBB₀ hb')).capRestrict hBB₀
  obtain ⟨y, hyB, hy⟩ := hgood _ (isOpen_ball.mem_nhds (mem_ball_self hε))
  obtain ⟨J, hJ⟩ := Submodule.exists_det_ne_zero hy (fun k ↦ D.evalVec w (s k).1.1 y)
    (D.fibImage_le_span hwρ hyB (hgen y hyB))
  refine ⟨ball b ε, isOpen_ball, mem_ball_self hε, hBS, convex_ball b ε, K, s, hs, hgen, J, ?_,
    fun y' hy' hdet ↦ isGood_of_det hBG hs hy' (hr y' (hBS hy')) hdet⟩
  exact AnalyticOnNhd.interior_inter_preimage_zero_eq_empty (fun x hx ↦
    analyticAt_of_differentiableOn_of_finiteDimensional isOpen_ball
      (differentiableOn_det_evalMat hwρ hBG _ J) hx) (convex_ball b ε).isPreconnected hyB hJ

/-- Near a point of `V ∖ Z` near which there are good points, the good points are dense. -/
lemma exists_nhds_frequently_isGood (hwρ : ∀ ν, w ν ∈ overlap F.ρ)
    (hloc : ∀ b ∈ F.G, b ∉ R.zeroSet → D.CapLocallyFinite h₀ n b) (hVo : IsOpen V)
    (hVG : V ⊆ F.G) (hr : ∀ y ∈ V \ R.zeroSet, finrank ℂ (D.fibImage h₀ n w y) ≤ r)
    {b : Cm.{u} m} (hb : b ∈ V \ R.zeroSet) (hgood : ∀ O ∈ 𝓝 b, ∃ y ∈ O, D.IsGood h₀ n w I₀ y) :
    ∃ B ∈ 𝓝 b, ∀ b' ∈ B, ∀ O ∈ 𝓝 b', ∃ y ∈ O, D.IsGood h₀ n w I₀ y := by
  obtain ⟨B, hB, hbB, -, -, K, s, hs, -, J, hint, hJ⟩ :=
    D.exists_chart R hwρ hloc hVo hVG hr hb hgood
  refine ⟨B, hB.mem_nhds hbB, fun b' hb' O hO ↦ ?_⟩
  obtain ⟨y, hyO, hyB, hy0⟩ := mem_closure_iff_nhds.1 (subset_closure_diff_zero hB hint hb') O hO
  exact ⟨y, hyO, hJ y hyB hy0⟩

/-- **The good points are dense near every point of `V ∖ Z`**, since `V ∖ Z` is connected. -/
theorem forall_frequently_isGood (hwρ : ∀ ν, w ν ∈ overlap F.ρ)
    (hloc : ∀ b ∈ F.G, b ∉ R.zeroSet → D.CapLocallyFinite h₀ n b) (hVo : IsOpen V)
    (hVG : V ⊆ F.G) (hVc : IsPreconnected V)
    (hr : ∀ y ∈ V \ R.zeroSet, finrank ℂ (D.fibImage h₀ n w y) ≤ r)
    (hb₀ : ∃ b ∈ V \ R.zeroSet, D.IsGood h₀ n w I₀ b) :
    ∀ b ∈ V \ R.zeroSet, ∀ O ∈ 𝓝 b, ∃ y ∈ O, D.IsGood h₀ n w I₀ y := by
  set P : Cm.{u} m → Prop := fun b ↦ ∀ O ∈ 𝓝 b, ∃ y ∈ O, D.IsGood h₀ n w I₀ y
  set U₁ : Set (Cm.{u} m) := {b | ∃ B ∈ 𝓝 b, ∀ b' ∈ B, P b'}
  set U₂ : Set (Cm.{u} m) := {b | ∃ O ∈ 𝓝 b, ∀ y ∈ O, ¬D.IsGood h₀ n w I₀ y}
  have hU₁ : IsOpen U₁ := isOpen_iff_mem_nhds.2 fun b ⟨B, hB, hP⟩ ↦
    Filter.mem_of_superset (interior_mem_nhds.2 hB) fun b' hb' ↦
      ⟨B, mem_interior_iff_mem_nhds.1 hb', hP⟩
  have hU₂ : IsOpen U₂ := isOpen_iff_mem_nhds.2 fun b ⟨O, hO, hP⟩ ↦
    Filter.mem_of_superset (interior_mem_nhds.2 hO) fun b' hb' ↦
      ⟨O, mem_interior_iff_mem_nhds.1 hb', hP⟩
  have hdisj : Disjoint U₁ U₂ := Set.disjoint_left.2 fun b ⟨B, hB, hP⟩ ⟨O, hO, hQ⟩ ↦ by
    obtain ⟨y, hyO, hy⟩ := hP b (mem_of_mem_nhds hB) O hO
    exact hQ y hyO hy
  have hspread : ∀ b ∈ V \ R.zeroSet, P b → b ∈ U₁ := fun b hb hPb ↦
    D.exists_nhds_frequently_isGood R hwρ hloc hVo hVG hr hb hPb
  have hsub : V \ R.zeroSet ⊆ U₁ ∪ U₂ := fun b hb ↦ by
    by_cases h : ∃ O ∈ 𝓝 b, ∀ y ∈ O, ¬D.IsGood h₀ n w I₀ y
    · exact Or.inr h
    · push Not at h
      exact Or.inl (hspread b hb h)
  obtain ⟨b₀, hb₀S, hb₀⟩ := hb₀
  have hconn := (R.restrict hVG).isPreconnected_sdiff_zeroSet hVo subset_rfl hVc
  have hS₁ := hconn.subset_left_of_subset_union hU₁ hU₂ hdisj hsub
    ⟨b₀, hb₀S, hspread b₀ hb₀S fun O hO ↦ ⟨b₀, mem_of_mem_nhds hO, hb₀⟩⟩
  intro b hb
  obtain ⟨B, hB, hP⟩ := hS₁ hb
  exact hP b (mem_of_mem_nhds hB)

lemma differentiableOn_evalMat (hwρ : ∀ ν, w ν ∈ overlap F.ρ) {B : Set (Cm.{u} m)}
    {hB : IsOpen B} (hBG : B ⊆ F.G) {K : ℕ}
    (s : Fin K → W.left.presheaf.obj (op (preim h₀ W (tubeN N B hB)))) (J : Fin r → Fin K)
    (i j : Fin r) : DifferentiableOn ℂ (fun y ↦ D.evalMat h₀ w I₀ s J y i j) B :=
  (D.differentiableOn_evalVec F.isOpen_G hwρ (s (J j)) (I₀ i)).mono fun y hy ↦ ⟨hBG hy, by
    rw [F.mem_img_tubeN hBG, Homeomorph.apply_symm_apply]
    exact ⟨hy, mem_ball_zero_iff.2 (hwρ _).2⟩⟩

lemma differentiableOn_cramerNum (hwρ : ∀ ν, w ν ∈ overlap F.ρ) {B : Set (Cm.{u} m)}
    {hB : IsOpen B} (hBG : B ⊆ F.G) {K : ℕ}
    (s : Fin K → W.left.presheaf.obj (op (preim h₀ W (tubeN N B hB)))) (J : Fin r → Fin K)
    (x : D.EvIdx M) (e : Fin r) :
    DifferentiableOn ℂ (fun y ↦ ∑ j, (D.evalMat h₀ w I₀ s J y).adjugate j e *
      D.evalVec w (s (J j)) y x) B :=
  DifferentiableOn.fun_sum fun j _ ↦
    (differentiableOn_adjugate (D.differentiableOn_evalMat hwρ hBG s J) j e).mul
      ((D.differentiableOn_evalVec F.isOpen_G hwρ (s (J j)) x).mono fun y hy ↦ ⟨hBG hy, by
        rw [F.mem_img_tubeN hBG, Homeomorph.apply_symm_apply]
        exact ⟨hy, mem_ball_zero_iff.2 (hwρ _).2⟩⟩)

variable (h₀ n w I₀) in
/-- The **good regular points**: the good points of `V ∖ Z` at which all entries of `Φ` are
regular. -/
def goodSet (V : Set (Cm.{u} m)) : Set (Cm.{u} m) :=
  {y | y ∈ V \ R.zeroSet ∧ D.IsGood h₀ n w I₀ y ∧
    ∀ x e, y ∈ RegularPairFamily.regPts R.zeroSet (D.graphFun h₀ n w I₀ x e)}

/-- In a chart, the points where the minor does not vanish are good regular points, and there
`Φ = adj / δ`. -/
lemma mem_goodSet_of_chart (hwρ : ∀ ν, w ν ∈ overlap F.ρ) (hVG : V ⊆ F.G)
    {B : Set (Cm.{u} m)} {hB : IsOpen B} (hBS : B ⊆ V \ R.zeroSet) {K : ℕ}
    {s : Fin K → boundedSubring h₀ W (tubeN N B hB) × (D.ι → Cm.{u} m × ℂ → ℂ)}
    (hs : ∀ k, s k ∈ D.capPole h₀ n (tubeN N B hB) (B ×ˢ ball 0 F.ρ)) {J : Fin r → Fin K}
    (hJ : ∀ y ∈ B, (D.evalMat h₀ w I₀ (fun k ↦ (s k).1.1) J y).det ≠ 0 → D.IsGood h₀ n w I₀ y)
    {y : Cm.{u} m} (hyB : y ∈ B) (hy : (D.evalMat h₀ w I₀ (fun k ↦ (s k).1.1) J y).det ≠ 0) :
    y ∈ D.goodSet h₀ n w I₀ R V := by
  have hBG : B ⊆ F.G := fun y hy ↦ hVG (hBS hy).1
  set δ := fun y ↦ (D.evalMat h₀ w I₀ (fun k ↦ (s k).1.1) J y).det
  have hδ : DifferentiableOn ℂ δ B := D.differentiableOn_det_evalMat hwρ hBG _ J
  set O := B ∩ {y | δ y ≠ 0}
  have hO : IsOpen O := hδ.continuousOn.isOpen_inter_preimage hB isOpen_ne
  refine ⟨hBS hyB, hJ y hyB hy, fun x e ↦ ⟨(hBS hyB).2, O, hO.mem_nhds ⟨hyB, hy⟩, _,
    (((D.differentiableOn_cramerNum hwρ hBG _ J x e).mono inter_subset_left).mul
      ((hδ.mono inter_subset_left).inv fun y' hy' ↦ hy'.2)).congr fun y' _ ↦ div_eq_mul_inv _ _,
    fun y' hy' _ ↦ graphFun_eq_div hBG hs hy'.1 (hJ y' hy'.1 hy'.2) hy'.2 x e⟩⟩

/-- The complement of `Z` is dense in `V`. -/
lemma subset_closure_sdiff_zeroSet (hVo : IsOpen V) (hVG : V ⊆ F.G) :
    V ⊆ closure (V \ R.zeroSet) := fun y hy ↦ by
  rw [mem_closure_iff_nhds]
  intro t ht
  have hO : IsOpen (interior (t ∩ V)) := isOpen_interior
  obtain ⟨b, hb, hbZ⟩ := exists_mem_sdiff_zeroSet R hO
    (interior_subset.trans (inter_subset_right.trans hVG))
    (interior_mem_nhds.2 (inter_mem ht (hVo.mem_nhds hy)) |> mem_of_mem_nhds)
  have := interior_subset hb
  exact ⟨b, this.1, this.2, hbZ⟩

/-- **The good regular points are dense in `V`.** -/
theorem subset_closure_goodSet (hwρ : ∀ ν, w ν ∈ overlap F.ρ)
    (hloc : ∀ b ∈ F.G, b ∉ R.zeroSet → D.CapLocallyFinite h₀ n b) (hVo : IsOpen V)
    (hVG : V ⊆ F.G) (hVc : IsPreconnected V)
    (hr : ∀ y ∈ V \ R.zeroSet, finrank ℂ (D.fibImage h₀ n w y) ≤ r)
    (hb₀ : ∃ b ∈ V \ R.zeroSet, D.IsGood h₀ n w I₀ b) :
    V ⊆ closure (D.goodSet h₀ n w I₀ R V) := by
  have hS : V \ R.zeroSet ⊆ closure (D.goodSet h₀ n w I₀ R V) := fun b hb ↦ by
    obtain ⟨B, hB, hbB, hBS, -, K, s, hs, -, J, hint, hJ⟩ := D.exists_chart R hwρ hloc hVo hVG hr hb
      (D.forall_frequently_isGood R hwρ hloc hVo hVG hVc hr hb₀ b hb)
    refine closure_mono ?_ (subset_closure_diff_zero hB hint hbB)
    exact fun y hy ↦ D.mem_goodSet_of_chart R hwρ hVG hBS hs hJ hy.1 hy.2
  exact (subset_closure_sdiff_zeroSet R hVo hVG).trans (closure_minimal hS isClosed_closure)

/-- **Local quotient representations of `Φ` off `Z`**, from Cramer's rule in a chart. -/
theorem isQuotRep_graphFun (hwρ : ∀ ν, w ν ∈ overlap F.ρ)
    (hloc : ∀ b ∈ F.G, b ∉ R.zeroSet → D.CapLocallyFinite h₀ n b) (hVo : IsOpen V)
    (hVG : V ⊆ F.G) (hVc : IsPreconnected V)
    (hr : ∀ y ∈ V \ R.zeroSet, finrank ℂ (D.fibImage h₀ n w y) ≤ r)
    (hb₀ : ∃ b ∈ V \ R.zeroSet, D.IsGood h₀ n w I₀ b) {b : Cm.{u} m} (hb : b ∈ V \ R.zeroSet)
    (x : D.EvIdx M) (e : Fin r) :
    RegularPairFamily.IsQuotRep R.zeroSet (D.graphFun h₀ n w I₀ x e) b := by
  obtain ⟨B, hB, hbB, hBS, -, K, s, hs, -, J, hint, hJ⟩ := D.exists_chart R hwρ hloc hVo hVG hr hb
    (D.forall_frequently_isGood R hwρ hloc hVo hVG hVc hr hb₀ b hb)
  have hBG : B ⊆ F.G := fun y hy ↦ hVG (hBS hy).1
  exact ⟨B, hB.mem_nhds hbB, _, _, D.differentiableOn_cramerNum hwρ hBG _ J x e,
    D.differentiableOn_det_evalMat hwρ hBG _ J, hint,
    fun y hy _ hdet ↦ graphFun_eq_div hBG hs hy (hJ y hy hdet) hdet x e⟩

/-- **The graph has a holomorphic denominator near every point of `V`**, by Levi's theorem across
the zero set of the regular pairs. -/
theorem exists_graph_rep (hwρ : ∀ ν, w ν ∈ overlap F.ρ)
    (hloc : ∀ b ∈ F.G, b ∉ R.zeroSet → D.CapLocallyFinite h₀ n b) (hVo : IsOpen V)
    (hVG : V ⊆ F.G) (hVc : IsPreconnected V)
    (hr : ∀ y ∈ V \ R.zeroSet, finrank ℂ (D.fibImage h₀ n w y) ≤ r)
    (hb₀ : ∃ b ∈ V \ R.zeroSet, D.IsGood h₀ n w I₀ b) {z : Cm.{u} m} (hz : z ∈ V) :
    ∃ N' : Set (Cm.{u} m), IsOpen N' ∧ z ∈ N' ∧ N' ⊆ V ∧ ∃ (c : Cm.{u} m → ℂ)
      (Ψ : D.EvIdx M → Fin r → Cm.{u} m → ℂ), DifferentiableOn ℂ c N' ∧
      (∀ x e, DifferentiableOn ℂ (Ψ x e) N') ∧ interior (N' ∩ c ⁻¹' {0}) = ∅ ∧
      ∀ y ∈ N', y ∈ D.goodSet h₀ n w I₀ R V → c y ≠ 0 →
        ∀ x e, D.graphFun h₀ n w I₀ x e y = Ψ x e y / c y := by
  have hdense := D.subset_closure_goodSet R hwρ hloc hVo hVG hVc hr hb₀
  have hq : ∀ p : D.EvIdx M × Fin r,
      RegularPairFamily.IsQuotRep R.zeroSet (D.graphFun h₀ n w I₀ p.1 p.2) z := fun p ↦
    (R.restrict hVG).isQuotRep_of_forall hVo
      (fun y hy ↦ closure_mono (fun y' hy' ↦ hy'.2.2 p.1 p.2) (hdense hy))
      (fun y hy hyZ ↦ D.isQuotRep_graphFun R hwρ hloc hVo hVG hVc hr hb₀ ⟨hy, hyZ⟩ p.1 p.2) z hz
  obtain ⟨N', hN'o, hzN', c, Ψ, hc, hΨ, hc0, hΦ⟩ := RegularPairFamily.exists_common_isQuotRep hq
  refine ⟨N' ∩ V, hN'o.inter hVo, ⟨hzN', hz⟩, inter_subset_right, c, fun x e ↦ Ψ (x, e),
    hc.mono inter_subset_left, fun x e ↦ (hΨ (x, e)).mono inter_subset_left,
    subset_empty_iff.1 (hc0 ▸ interior_mono fun y hy ↦ ⟨hy.1.1, hy.2⟩),
    fun y hy hyg hcy x e ↦ hΦ y hy.1 (x, e) (hyg.2.2 x e) hcy⟩

end

end ComplexAnalytic.Cap.AnnulusDecomposition
