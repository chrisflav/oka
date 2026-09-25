/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.ES.CapExtension.BaseSheaf
import Oka.Nullstellensatz.Minors

/-!
# The fibres of the evaluation of the sections of the cap

Keep the notation of `Oka/Analytification/RET/ES/CapExtension/Setup.lean`. For a point `b` of the
base, the values at `b` of the evaluations `λ(t)` of the sections `t` of the cap with a pole of
order `≤ n` at infinity near `b` span a subspace `E_b ⊆ ℂ^{M ∑ kᵢ}`
(`ComplexAnalytic.Cap.AnnulusDecomposition.fibImage`). If sections `s` generate the sections of the
cap at `b`, then `E_b` is spanned by the `λ(sₖ)(b)`
(`ComplexAnalytic.Cap.AnnulusDecomposition.fibImage_le_span`).

We also collect the linear algebra of graphs used later: a subspace `E ⊆ ℂ^X` of dimension `r` is
the graph of a linear map on `r` suitable coordinates `I₀` (`Submodule.exists_bijective_coordProj`),
and then every element of `E` is the combination of the vectors of `E` with unit coordinates on
`I₀` (`Submodule.eq_sum_graphVec`).
-/

open CategoryTheory Opposite Topology Set Filter Metric Module
open scoped Matrix

universe u

namespace Submodule

section LinAlg

variable {X : Type*} {r : ℕ} (I₀ : Fin r → X) (E : Submodule ℂ (X → ℂ))

/-- The coordinates on `I₀` of the elements of `E`. -/
noncomputable def coordProj : E →ₗ[ℂ] (Fin r → ℂ) :=
  (LinearMap.pi fun i ↦ LinearMap.proj (I₀ i)) ∘ₗ E.subtype

@[simp]
lemma coordProj_apply (v : E) (i : Fin r) : E.coordProj I₀ v i = (v : X → ℂ) (I₀ i) :=
  rfl

variable {I₀ E}

/-- If `r` vectors of `E` have an invertible matrix of coordinates on `I₀` and `E` has dimension
at most `r`, the coordinates on `I₀` identify `E` with `ℂ^r`. -/
theorem bijective_coordProj_of_det [Finite X] (hdim : finrank ℂ E ≤ r) (vs : Fin r → X → ℂ)
    (hvs : ∀ j, vs j ∈ E) (hdet : (Matrix.of fun i j ↦ vs j (I₀ i)).det ≠ 0) :
    Function.Bijective (E.coordProj I₀) := by
  set A : Matrix (Fin r) (Fin r) ℂ := Matrix.of fun i j ↦ vs j (I₀ i)
  have hsurj : Function.Surjective (E.coordProj I₀) := by
    intro c
    set a := A⁻¹ *ᵥ c
    refine ⟨⟨∑ j, a j • vs j, sum_mem fun j _ ↦ smul_mem _ _ (hvs j)⟩, funext fun i ↦ ?_⟩
    have : (A *ᵥ a) i = c i := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdet),
        Matrix.one_mulVec]
    rw [← this]
    simp [Matrix.mulVec, dotProduct, A, mul_comm]
  have hr : finrank ℂ E = r := le_antisymm hdim (by
    simpa using LinearMap.finrank_range_le (E.coordProj I₀) |>.trans_eq' (by
      rw [LinearMap.range_eq_top.2 hsurj, finrank_top, finrank_fin_fun]))
  refine ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp [hr])).2 hsurj,
    hsurj⟩

/-- **Coordinates of a subspace**: a subspace `E ⊆ ℂ^X` of dimension `r` is identified with `ℂ^r`
by the coordinates on some `r` indices. -/
theorem exists_bijective_coordProj [Finite X] (E : Submodule ℂ (X → ℂ)) :
    ∃ I₀ : Fin (finrank ℂ E) → X, Function.Bijective (E.coordProj I₀) := by
  classical
  have := Fintype.ofFinite X
  set r := finrank ℂ E
  set bs := Module.finBasis ℂ E
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective E.subtype (ker_subtype E)
  set A : Matrix (Fin r) X ℂ := Matrix.of fun i x ↦ (bs i : X → ℂ) x
  set C : Matrix X (Fin r) ℂ := Matrix.of fun x j ↦ bs.repr (g (Pi.single x 1)) j
  have hAC : A * C = 1 := by
    ext i j
    have hsum : (bs i : X → ℂ) = ∑ x, (bs i : X → ℂ) x • Pi.single x 1 := by
      ext y
      simp [Finset.sum_apply, Pi.single_apply]
    have := congrArg (fun v ↦ bs.repr (g v) j) hsum
    simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
      smul_eq_mul] at this
    have hgi : g (bs i : X → ℂ) = bs i := LinearMap.congr_fun hg (bs i)
    rw [hgi, Basis.repr_self] at this
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [A, C, Matrix.of_apply]
    rw [← this, Finsupp.single_apply]
  obtain ⟨σ, hσ⟩ := Matrix.exists_isUnit_det_submatrix_of_mul_eq_one hAC
  refine ⟨σ, bijective_coordProj_of_det le_rfl (fun j ↦ (bs j : X → ℂ)) (fun j ↦ (bs j).2) ?_⟩
  have : (Matrix.of fun i j ↦ (bs j : X → ℂ) (σ i)) = (A.submatrix id σ).transpose := by
    ext i j
    rfl
  rw [this, Matrix.det_transpose]
  exact hσ.ne_zero

variable (hbij : Function.Bijective (E.coordProj I₀))

/-- The vector of `E` with coordinates `Pi.single e 1` on `I₀`. -/
noncomputable def graphVec (e : Fin r) : X → ℂ :=
  ((LinearEquiv.ofBijective (E.coordProj I₀) hbij).symm (Pi.single e 1) : E)

lemma graphVec_mem (e : Fin r) : graphVec hbij e ∈ E :=
  ((LinearEquiv.ofBijective (E.coordProj I₀) hbij).symm (Pi.single e 1)).2

lemma graphVec_apply (e i : Fin r) :
    graphVec hbij e (I₀ i) = (Pi.single e (1 : ℂ) : Fin r → ℂ) i := by
  have := (LinearEquiv.ofBijective (E.coordProj I₀) hbij).apply_symm_apply (Pi.single e 1)
  exact congrFun this i

include hbij in
/-- The elements of `E` are determined by their coordinates on `I₀`. -/
lemma eq_of_coord_eq {v v' : X → ℂ} (hv : v ∈ E) (hv' : v' ∈ E) (h : ∀ i, v (I₀ i) = v' (I₀ i)) :
    v = v' := by
  have := hbij.1 (a₁ := ⟨v, hv⟩) (a₂ := ⟨v', hv'⟩) (funext h)
  exact congrArg Subtype.val this

/-- **Every element of `E` is the combination of the `graphVec`s with its coordinates on `I₀`.** -/
theorem eq_sum_graphVec {v : X → ℂ} (hv : v ∈ E) : v = ∑ e, v (I₀ e) • graphVec hbij e := by
  refine eq_of_coord_eq hbij hv (sum_mem fun e _ ↦ smul_mem _ _ (graphVec_mem hbij e))
    fun i ↦ ?_
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, graphVec_apply]
  simp [Pi.single_apply]

include hbij in
/-- **The matrix of coordinates of a spanning family has an invertible maximal minor.** -/
theorem exists_det_ne_zero {K : Type*} [Finite K] (vs : K → X → ℂ)
    (hE : E ≤ span ℂ (range vs)) :
    ∃ J : Fin r → K, (Matrix.of fun i j ↦ vs (J j) (I₀ i)).det ≠ 0 := by
  classical
  have := Fintype.ofFinite K
  have hc : ∀ j, ∃ c : K → ℂ, ∑ k, c k • vs k = graphVec hbij j := fun j ↦
    (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hE (graphVec_mem hbij j))
  choose c hc using hc
  set A : Matrix (Fin r) K ℂ := Matrix.of fun i k ↦ vs k (I₀ i)
  have hAC : A * Matrix.of (fun k j ↦ c j k) = 1 := by
    ext i j
    have := congrFun (hc j) (I₀ i)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, graphVec_apply] at this
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [A, Matrix.of_apply]
    rw [← Pi.single_apply, ← this]
    exact Finset.sum_congr rfl fun k _ ↦ mul_comm _ _
  obtain ⟨σ, hσ⟩ := Matrix.exists_isUnit_det_submatrix_of_mul_eq_one hAC
  exact ⟨σ, hσ.ne_zero⟩

end LinAlg

end Submodule

namespace ComplexAnalytic.Cap.AnnulusDecomposition

open AnalyticSpace BoundedSections Complex.ProjectiveLineBundle AlgebraicGeometry.LocallyRingedSpace
open KummerModel (splitEquiv)

noncomputable section

variable {m : ℕ} {N N₀ : (AnalyticSpace.complexAffineSpace.{u} (m + 1)).Opens} (h₀ : N₀ ≤ N)
  {W : FiniteEtaleOver (space N₀)} {F : WeierstrassForm N N₀}
  (D : AnnulusDecomposition W F.G F.ρ) (n : ℕ) {M : ℕ} (w : Fin M → ℂ)

/-- **The fibre of the evaluation** at `b`: the span of the values at `b` of the evaluations of
the sections of the cap with a pole of order `≤ n` at infinity near `b`. -/
def fibImage (b : Cm.{u} m) : Submodule ℂ (D.EvIdx M → ℂ) :=
  Submodule.span ℂ {v | ∃ (B : Set (Cm.{u} m)) (hB : IsOpen B), B ⊆ F.G ∧ b ∈ B ∧
    ∃ t ∈ D.capPole h₀ n (tubeN N B hB) (B ×ˢ ball 0 F.ρ), v = D.evalVec w t.1.1 b}

variable {h₀ D n w}

lemma evalVec_mem_fibImage {B : Set (Cm.{u} m)} {hB : IsOpen B} (hBG : B ⊆ F.G) {b : Cm.{u} m}
    (hb : b ∈ B) {t : boundedSubring h₀ W (tubeN N B hB) × (D.ι → Cm.{u} m × ℂ → ℂ)}
    (ht : t ∈ D.capPole h₀ n (tubeN N B hB) (B ×ˢ ball 0 F.ρ)) :
    D.evalVec w t.1.1 b ∈ D.fibImage h₀ n w b :=
  Submodule.subset_span ⟨B, hB, hBG, hb, t, ht, rfl⟩

/-- **The fibre is spanned by the values of generators.** -/
theorem fibImage_le_span (hwρ : ∀ ν, w ν ∈ overlap F.ρ) {B : Set (Cm.{u} m)} {hB : IsOpen B}
    {K : ℕ}
    {s : Fin K → boundedSubring h₀ W (tubeN N B hB) × (D.ι → Cm.{u} m × ℂ → ℂ)} {b : Cm.{u} m}
    (hbB : b ∈ B) (hgen : D.IsCapGenAt h₀ n s b) :
    D.fibImage h₀ n w b ≤ Submodule.span ℂ (range fun k ↦ D.evalVec w (s k).1.1 b) := by
  refine Submodule.span_le.2 ?_
  rintro v ⟨B', hB', hB'G, hbB', t, ht, rfl⟩
  have hVo : IsOpen (B' ∩ B) := hB'.inter hB
  have hle : tubeN N (B' ∩ B) hVo ≤ tubeN N B' hB' := tubeN_mono inter_subset_left
  have hVG : B' ∩ B ⊆ F.G := inter_subset_left.trans hB'G
  obtain ⟨V', hV'V, hV', hbV', e, -, hrel⟩ := hgen (B' ∩ B) hVo inter_subset_right ⟨hbB', hbB⟩
    (D.capRestrict h₀ hle t)
    (D.capRestrict_mem_capPole h₀ hle (prod_mono inter_subset_left subset_rfl) ht)
  have hv : D.evalVec w t.1.1 b = ∑ k, e k b • D.evalVec w (s k).1.1 b := by
    funext x
    rw [← D.evalVec_capRestrict h₀ hwρ hVG (hV' := hVo) inter_subset_left t ⟨hbB', hbB⟩,
      D.evalVec_eq_sum_of_evalFun' h₀ hVG hV'V inter_subset_right hwρ hrel hbV' x]
    simp [Finset.sum_apply]
  rw [SetLike.mem_coe, hv]
  exact Submodule.sum_mem _ fun k _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

end

end ComplexAnalytic.Cap.AnnulusDecomposition
