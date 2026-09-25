/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytic.LeviExtension
import Oka.Analytification.RET.ES.Evaluation

/-!
# Minors of the evaluation and Cramer's rule

Keep the notation of `Oka/Analytification/RET/ES/Evaluation.lean`. For sections `s₀, …, s_{p-1}`
of the cap and indices `I(0), …, I(p-1)` of the evaluation, the matrix
`Λ_I(b) = (λ(s_q)(b)_{I(e)})_{e, q}` (`ComplexAnalytic.Cap.AnnulusDecomposition.evalMatrix`) is
holomorphic in `b`, and so is its determinant, the minor `Δ_I`. Where `Δ_I ≠ 0`, Cramer's rule
gives the sections `σ_I(e) = ∑_q (Λ_I⁻¹)_{q e} s_q` of the cap with `λ_I(σ_I(e)) = e`
(`ComplexAnalytic.Cap.AnnulusDecomposition.exists_cramerSection`). Their coordinates
`(Λ_I⁻¹)_{q e} = adj(Λ_I)_{q e} / Δ_I` are meromorphic: locally quotients of holomorphic functions
(`ComplexAnalytic.Cap.AnnulusDecomposition.isLocallyQuotientAt_cramerCoeff`).

## Main definitions

- `ComplexAnalytic.Cap.AnnulusDecomposition.evalMatrix`: the matrix `Λ_I`.
- `ComplexAnalytic.Cap.AnnulusDecomposition.cramerCoeff`: the entries of `Λ_I⁻¹`.
-/

open CategoryTheory Opposite Topology Set Filter Metric

universe u

namespace ComplexAnalytic.Cap

section Matrix

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {S : Set E}

lemma differentiableOn_finsetProd {ι : Type*} (u : Finset ι) {f : ι → E → ℂ}
    (h : ∀ i ∈ u, DifferentiableOn ℂ (f i) S) :
    DifferentiableOn ℂ (fun b ↦ ∏ i ∈ u, f i b) S := by
  classical
  induction u using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    exact differentiableOn_const 1
  | insert j u hj ih =>
    simp only [Finset.prod_insert hj]
    exact (h j (Finset.mem_insert_self j u)).mul
      (ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi))

variable {n : Type*} [Fintype n] [DecidableEq n] {A : E → Matrix n n ℂ}

/-- The determinant of a matrix of holomorphic functions is holomorphic. -/
lemma differentiableOn_det (hA : ∀ i j, DifferentiableOn ℂ (fun b ↦ A b i j) S) :
    DifferentiableOn ℂ (fun b ↦ (A b).det) S := by
  simp only [Matrix.det_apply']
  exact DifferentiableOn.fun_sum fun σ _ ↦ (differentiableOn_const _).mul
    (differentiableOn_finsetProd _ fun i _ ↦ hA _ _)

/-- The adjugate of a matrix of holomorphic functions is holomorphic. -/
lemma differentiableOn_adjugate (hA : ∀ i j, DifferentiableOn ℂ (fun b ↦ A b i j) S) (i j : n) :
    DifferentiableOn ℂ (fun b ↦ (A b).adjugate i j) S := by
  simp only [Matrix.adjugate_apply]
  refine differentiableOn_det fun i' j' ↦ ?_
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact differentiableOn_const _
  · exact hA i' j'

end Matrix

end ComplexAnalytic.Cap

namespace ComplexAnalytic.Cap.AnnulusDecomposition

open AnalyticSpace BoundedSections KummerModel Complex.ProjectiveLineBundle

noncomputable section

variable {m : ℕ} {N₀ : (AnalyticSpace.complexAffineSpace.{u} (m + 1)).Opens}
  {W : FiniteEtaleOver (space N₀)} {G : Set (Cm.{u} m)} {ρ : ℝ}
  (D : AnnulusDecomposition W G ρ) {M : ℕ} (w : Fin M → ℂ) {p : ℕ}

/-- The matrix `(λ(a_q)(b)_{I(e)})_{e, q}` of the evaluations of `p` sections `a_q` at `p`
indices `I(e)`. -/
def evalMatrix {O : W.left.Opens} (a : Fin p → W.left.presheaf.obj (op O))
    (I : Fin p → Fin M × (Σ i, Fin (D.deg i))) (b : Cm.{u} m) : Matrix (Fin p) (Fin p) ℂ :=
  Matrix.of fun e q ↦ D.evalVec w (a q) b (I e)

/-- The entries `(Λ_I(b)⁻¹)_{q e}` of the inverse of the evaluation matrix: the coordinates of the
sections given by Cramer's rule. -/
def cramerCoeff {O : W.left.Opens} (a : Fin p → W.left.presheaf.obj (op O))
    (I : Fin p → Fin M × (Σ i, Fin (D.deg i))) (q e : Fin p) (b : Cm.{u} m) : ℂ :=
  (D.evalMatrix w a I b)⁻¹ q e

variable {N : (AnalyticSpace.complexAffineSpace.{u} (m + 1)).Opens} {h₀ : N₀ ≤ N}
  {V : (space N).Opens} {w}

/-- The entries of the evaluation matrix are holomorphic. -/
lemma differentiableOn_evalMatrix (hGo : IsOpen G) (hw : ∀ ν, w ν ∈ overlap ρ)
    (a : Fin p → W.left.presheaf.obj (op (preim h₀ W V)))
    (I : Fin p → Fin M × (Σ i, Fin (D.deg i))) (e q : Fin p) :
    DifferentiableOn ℂ (fun b ↦ D.evalMatrix w a I b e q)
      {b | b ∈ G ∧ ∀ ν, (splitEquiv m).symm (b, w ν) ∈ img V} :=
  (D.differentiableOn_evalVec hGo hw (a q) (I e)).mono fun _ hb ↦ ⟨hb.1, hb.2 _⟩

/-- **The minors of the evaluation are holomorphic.** -/
theorem differentiableOn_det_evalMatrix (hGo : IsOpen G) (hw : ∀ ν, w ν ∈ overlap ρ)
    (a : Fin p → W.left.presheaf.obj (op (preim h₀ W V)))
    (I : Fin p → Fin M × (Σ i, Fin (D.deg i))) :
    DifferentiableOn ℂ (fun b ↦ (D.evalMatrix w a I b).det)
      {b | b ∈ G ∧ ∀ ν, (splitEquiv m).symm (b, w ν) ∈ img V} :=
  differentiableOn_det (D.differentiableOn_evalMatrix hGo hw a I)

lemma cramerCoeff_eq_div {O : W.left.Opens} (a : Fin p → W.left.presheaf.obj (op O))
    (I : Fin p → Fin M × (Σ i, Fin (D.deg i))) (q e : Fin p) (b : Cm.{u} m) :
    D.cramerCoeff w a I q e b =
      (D.evalMatrix w a I b).adjugate q e / (D.evalMatrix w a I b).det := by
  rw [cramerCoeff, Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul,
    div_eq_inv_mul]

/-- **The coordinates of the Cramer sections are holomorphic off the zero set of the minor.** -/
theorem differentiableOn_cramerCoeff (hGo : IsOpen G) (hw : ∀ ν, w ν ∈ overlap ρ)
    (a : Fin p → W.left.presheaf.obj (op (preim h₀ W V)))
    (I : Fin p → Fin M × (Σ i, Fin (D.deg i))) (q e : Fin p) :
    DifferentiableOn ℂ (D.cramerCoeff w a I q e)
      {b | (b ∈ G ∧ ∀ ν, (splitEquiv m).symm (b, w ν) ∈ img V) ∧
        (D.evalMatrix w a I b).det ≠ 0} := by
  set Ω := {b | (b ∈ G ∧ ∀ ν, (splitEquiv m).symm (b, w ν) ∈ img V) ∧
    (D.evalMatrix w a I b).det ≠ 0}
  have hΩ : Ω ⊆ {b | b ∈ G ∧ ∀ ν, (splitEquiv m).symm (b, w ν) ∈ img V} := fun b hb ↦ hb.1
  refine DifferentiableOn.congr ?_ fun b _ ↦
    (D.cramerCoeff_eq_div a I q e b).trans (div_eq_mul_inv _ _)
  exact ((differentiableOn_adjugate (D.differentiableOn_evalMatrix hGo hw a I) q e).mono hΩ).mul
    (((D.differentiableOn_det_evalMatrix hGo hw a I).mono hΩ).inv fun b hb ↦ hb.2)

/-- **The coordinates of the Cramer sections are meromorphic**: if the minor `Δ_I` does not vanish
identically on any open subset of the open `U`, then near every point of `U` the coordinate
`(Λ_I⁻¹)_{q e}` is the quotient `adj(Λ_I)_{q e} / Δ_I`. -/
theorem isLocallyQuotientAt_cramerCoeff (hGo : IsOpen G) (hw : ∀ ν, w ν ∈ overlap ρ)
    (a : Fin p → W.left.presheaf.obj (op (preim h₀ W V)))
    (I : Fin p → Fin M × (Σ i, Fin (D.deg i))) {U : Set (Cm.{u} m)} (hU : IsOpen U)
    (hUG : U ⊆ {b | b ∈ G ∧ ∀ ν, (splitEquiv m).symm (b, w ν) ∈ img V})
    (hΔ : interior (U ∩ (fun b ↦ (D.evalMatrix w a I b).det) ⁻¹' {0}) = ∅) (q e : Fin p)
    {z : Cm.{u} m} (hz : z ∈ U) : IsLocallyQuotientAt (D.cramerCoeff w a I q e) z :=
  ⟨U, hU.mem_nhds hz, _, _,
    (differentiableOn_adjugate (D.differentiableOn_evalMatrix hGo hw a I) q e).mono hUG,
    (D.differentiableOn_det_evalMatrix hGo hw a I).mono hUG, hΔ,
    fun b _ _ ↦ D.cramerCoeff_eq_div a I q e b⟩

variable (h₀) in
/-- **Restriction of sections of the cap with a pole at infinity.** -/
theorem capRestrict_mem_capPole {k : ℕ} {V₂ : (space N).Opens} (h : V₂ ≤ V)
    {V' V₂' : Set (Cm.{u} m × ℂ)} (h' : V₂' ⊆ V')
    {s : boundedSubring h₀ W V × (D.ι → Cm.{u} m × ℂ → ℂ)} (hs : s ∈ D.capPole h₀ k V V') :
    D.capRestrict h₀ h s ∈ D.capPole h₀ k V₂ V₂' := by
  refine ⟨fun i ↦ (hs.1 i).mono fun _ hx ↦ h' hx, fun i z hz hz' ↦ ?_⟩
  change D.kummerVal (W.left.presheaf.map (homOfLE (preim_mono h₀ W h)).op s.1.1) i z = _
  rw [D.kummerVal_map _ hz]
  exact hs.2 i z (D.pieceSet_mono (preim_mono h₀ W h) i hz) (h' hz')

/-- A function `c` holomorphic on `U`, as a section of the cap over `U × ℙ¹` constant along `ℙ¹`. -/
lemma exists_const_mem_capSubring {U : Set (Cm.{u} m)}
    (hV : ∀ x, x ∈ img V ↔ splitEquiv m x ∈ U ×ˢ ball (0 : ℂ) ρ) {c : Cm.{u} m → ℂ}
    (hc : DifferentiableOn ℂ c U) :
    ∃ t ∈ D.capSubring h₀ V (U ×ˢ ball 0 ρ),
      (∀ y ∈ preim h₀ W V, evalFun t.1.1 y = c (splitEquiv m (pt W y)).1) ∧
        ∀ i x, t.2 i x = c x.1 := by
  have hF : DifferentiableOn ℂ (fun x ↦ c (splitEquiv m x).1) (img V) :=
    hc.comp (differentiable_fst.comp differentiable_splitEquiv).differentiableOn
      fun x hx ↦ ((hV x).1 hx).1
  let r : (space N).presheaf.obj (op V) := OkaRing.ofDifferentiableOn _ hF
  have hr (x : Cn.{u} (m + 1)) (hx : x ∈ img V) : holFun r x = c (splitEquiv m x).1 := by
    rw [holFun, OkaRing.toGlobalFun_apply _ hx]
    rfl
  refine ⟨_, D.algebraMap_mem_capSubring h₀ r (g := fun x ↦ c x.1)
    (hc.comp differentiableOn_fst fun x hx ↦ hx.1) fun b _ w' _ hbV _ ↦ ?_,
    fun y hy ↦ ?_, fun i x ↦ rfl⟩
  · rw [hr _ hbV, Homeomorph.apply_symm_apply]
  · rw [evalFun_of_mem _ hy]
    change W.left.eval y hy (pullback h₀ W V r) = _
    rw [eval_pullback, hr _ ((mem_preim_iff h₀ W).1 hy)]

/-- **Cramer's rule**: where the minor `Δ_I` does not vanish, the section
`σ_I(e) = ∑_q (Λ_I⁻¹)_{q e} s_q` of the cap with a pole of order `≤ k` at infinity satisfies
`λ_I(σ_I(e)) = e`. Here `Λ_I` is the matrix of the evaluations of the sections `s_q` at the
indices `I`, and `σ_I(e)` lives over `U × ℙ¹` for `U` open with `Δ_I ≠ 0` on `U`. -/
theorem exists_cramerSection (hGo : IsOpen G) (hw : ∀ ν, w ν ∈ overlap ρ) {k : ℕ}
    {V' : Set (Cm.{u} m × ℂ)} {s : Fin p → boundedSubring h₀ W V × (D.ι → Cm.{u} m × ℂ → ℂ)}
    (hs : ∀ q, s q ∈ D.capPole h₀ k V V') (I : Fin p → Fin M × (Σ i, Fin (D.deg i)))
    {U : Set (Cm.{u} m)} (hUG : U ⊆ G) {V₂ : (space N).Opens} (hV₂V : V₂ ≤ V)
    (hV₂ : ∀ x, x ∈ img V₂ ↔ splitEquiv m x ∈ U ×ˢ ball (0 : ℂ) ρ) (hV' : U ×ˢ ball 0 ρ ⊆ V')
    (hΔ : ∀ b ∈ U, (D.evalMatrix w (fun q ↦ (s q).1.1) I b).det ≠ 0) (e : Fin p) :
    ∃ σ ∈ D.capPole h₀ k V₂ (U ×ˢ ball 0 ρ),
      (∀ y ∈ preim h₀ W V₂, evalFun σ.1.1 y = ∑ q, D.cramerCoeff w (fun q ↦ (s q).1.1) I q e
        (splitEquiv m (pt W y)).1 * evalFun (s q).1.1 y) ∧
      (∀ i x, σ.2 i x = ∑ q, D.cramerCoeff w (fun q ↦ (s q).1.1) I q e x.1 * (s q).2 i x) ∧
      ∀ b ∈ U, ∀ e', D.evalVec w σ.1.1 b (I e') = if e' = e then 1 else 0 := by
  classical
  set a : Fin p → W.left.presheaf.obj (op (preim h₀ W V)) := fun q ↦ (s q).1.1
  have hbV₂ (b : Cm.{u} m) (hb : b ∈ U) (ν : Fin M) : (splitEquiv m).symm (b, w ν) ∈ img V₂ := by
    rw [hV₂, Homeomorph.apply_symm_apply]
    exact ⟨hb, mem_ball_zero_iff.2 (hw ν).2⟩
  have hUΩ : U ⊆ {b | (b ∈ G ∧ ∀ ν, (splitEquiv m).symm (b, w ν) ∈ img V) ∧
      (D.evalMatrix w a I b).det ≠ 0} := fun b hb ↦
    ⟨⟨hUG hb, fun ν ↦ img_mono hV₂V (hbV₂ b hb ν)⟩, hΔ b hb⟩
  have hc (q : Fin p) : DifferentiableOn ℂ (D.cramerCoeff w a I q e) U :=
    (D.differentiableOn_cramerCoeff hGo hw a I q e).mono hUΩ
  choose t ht hte ht2 using fun q ↦ D.exists_const_mem_capSubring (h₀ := h₀) hV₂ (hc q)
  set σ := ∑ q, t q * D.capRestrict h₀ hV₂V (s q)
  have hσ1 (y : W.left) (hy : y ∈ preim h₀ W V₂) : evalFun σ.1.1 y =
      ∑ q, D.cramerCoeff w a I q e (splitEquiv m (pt W y)).1 * evalFun (s q).1.1 y := by
    have hσ : σ.1.1 = ∑ q, (t q).1.1 *
        W.left.presheaf.map (homOfLE (preim_mono h₀ W hV₂V)).op (s q).1.1 := by
      simp only [σ, Prod.fst_sum, Prod.fst_mul, AddSubmonoidClass.coe_finsetSum,
        MulMemClass.coe_mul]
      rfl
    rw [evalFun_of_mem _ hy, hσ, map_sum]
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    rw [map_mul, ← evalFun_of_mem _ hy, hte q y hy, eval_presheaf_map,
      evalFun_of_mem _ (preim_mono h₀ W hV₂V hy)]
  refine ⟨σ, AddSubgroup.sum_mem _ fun q _ ↦ D.mul_mem_capPole_of_mem_capSubring (ht q)
    (D.capRestrict_mem_capPole h₀ hV₂V hV' (hs q)), hσ1, fun i x ↦ ?_, fun b hb e' ↦ ?_⟩
  · simp only [σ, Prod.snd_sum, Prod.snd_mul, Finset.sum_apply, Pi.mul_apply, ht2]
    rfl
  · obtain ⟨y, hy, hpt, h⟩ := D.exists_evalVec_eq (h₀ := h₀) hw (hUG hb) (I e') (hbV₂ b hb _)
    have hval (q : Fin p) : evalFun (s q).1.1 y = D.evalVec w (s q).1.1 b (I e') := by
      rw [← D.evalVec_map hV₂V hw (hUG hb) (I e') (hbV₂ b hb _), h, eval_presheaf_map,
        evalFun_of_mem]
    rw [h, ← evalFun_of_mem _ hy, hσ1 y hy, hpt, Homeomorph.apply_symm_apply]
    have hsum : ∑ q, D.cramerCoeff w a I q e b * evalFun (s q).1.1 y =
        (D.evalMatrix w a I b * (D.evalMatrix w a I b)⁻¹) e' e := by
      rw [Matrix.mul_apply]
      exact Finset.sum_congr rfl fun q _ ↦ by rw [hval, mul_comm]; rfl
    rw [hsum, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (hΔ b hb)), Matrix.one_apply]

end

end ComplexAnalytic.Cap.AnnulusDecomposition
