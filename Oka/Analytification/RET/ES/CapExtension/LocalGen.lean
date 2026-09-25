/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.ES.CapExtension.Combine

/-!
# Combinations of sections of the cap and their evaluations

Keep the notation of `Oka/Analytification/RET/ES/CapExtension/Setup.lean`. A section of the cap
with a pole of order `≤ n` at infinity is a combination of sections `sₖ` with coefficients
holomorphic functions of `b` if and only if its evaluation `λ` at more than `n ∑ kᵢ` points of the
annulus is the corresponding combination of the `λ(sₖ)`
(`ComplexAnalytic.Cap.AnnulusDecomposition.evalVec_eq_sum_of_evalFun`,
`ComplexAnalytic.Cap.AnnulusDecomposition.evalFun_eq_sum_of_evalVec`).
-/

open CategoryTheory Opposite Topology Set Filter Metric

universe u

namespace ComplexAnalytic.Cap.AnnulusDecomposition

open AnalyticSpace BoundedSections Complex.ProjectiveLineBundle AlgebraicGeometry.LocallyRingedSpace
open KummerModel (splitEquiv)

noncomputable section

variable {m : ℕ} {N N₀ : (AnalyticSpace.complexAffineSpace.{u} (m + 1)).Opens} (h₀ : N₀ ≤ N)
  {W : FiniteEtaleOver (space N₀)} {F : WeierstrassForm N N₀}
  (D : AnnulusDecomposition W F.G F.ρ)

/-- The evaluation of a combination of sections with coefficients functions of `b`. -/
lemma evalVec_eq_sum_of_evalFun {V : Set (Cm.{u} m)} {hV : IsOpen V} (hVG : V ⊆ F.G) {M : ℕ}
    {w : Fin M → ℂ} (hwρ : ∀ ν, w ν ∈ overlap F.ρ) {K : ℕ}
    {t : W.left.presheaf.obj (op (preim h₀ W (tubeN N V hV)))}
    {s : Fin K → W.left.presheaf.obj (op (preim h₀ W (tubeN N V hV)))}
    {e : Fin K → Cm.{u} m → ℂ}
    (h : ∀ y ∈ preim h₀ W (tubeN N V hV),
      evalFun t y = ∑ k, e k (baseOf (pt W y)) * evalFun (s k) y)
    {b : Cm.{u} m} (hb : b ∈ V) (x : Fin M × (Σ i, Fin (D.deg i))) :
    D.evalVec w t b x = ∑ k, e k b * D.evalVec w (s k) b x := by
  obtain ⟨y, hy, hyb, hval⟩ := D.exists_evalVec_eq_tube h₀ hwρ hVG hb x
  rw [hval, h y hy, hyb]
  simp_rw [hval]

variable [T2Space W.left]

/-- **Combinations from evaluations**: if the evaluation of a section `t` of the cap with a pole
of order `≤ n` is, over `V'`, a combination of the evaluations of sections `sₖ` with holomorphic
coefficients, then `t` is this combination of the `sₖ` over `V'`. -/
theorem evalFun_eq_sum_of_evalVec {n : ℕ} {V V' B : Set (Cm.{u} m)} {hV : IsOpen V}
    (hV' : IsOpen V') {hB : IsOpen B} (hVG : V ⊆ F.G) (hV'V : V' ⊆ V) (hVB : V ⊆ B)
    {t : boundedSubring h₀ W (tubeN N V hV) × (D.ι → Cm.{u} m × ℂ → ℂ)}
    (ht : t ∈ D.capPole h₀ n (tubeN N V hV) (V ×ˢ ball 0 F.ρ)) {K : ℕ}
    {s : Fin K → boundedSubring h₀ W (tubeN N B hB) × (D.ι → Cm.{u} m × ℂ → ℂ)}
    (hs : ∀ k, s k ∈ D.capPole h₀ n (tubeN N B hB) (B ×ˢ ball 0 F.ρ)) {M : ℕ}
    (hM : (∑ i, (D.deg i : ℕ)) * n < M) {w : Fin M → ℂ} (hw : Function.Injective w)
    (hwρ : ∀ ν, w ν ∈ overlap F.ρ) {e : Fin K → Cm.{u} m → ℂ}
    (he : ∀ k, DifferentiableOn ℂ (e k) V')
    (h : ∀ b ∈ V', ∀ x, D.evalVec w t.1.1 b x = ∑ k, e k b * D.evalVec w (s k).1.1 b x) :
    ∀ y ∈ preim h₀ W (tubeN N V hV), baseOf (pt W y) ∈ V' →
      evalFun t.1.1 y = ∑ k, e k (baseOf (pt W y)) * evalFun (s k).1.1 y := by
  have hV'G : V' ⊆ F.G := hV'V.trans hVG
  have hle : tubeN N V' hV' ≤ tubeN N V hV := tubeN_mono hV'V
  have hleB : tubeN N V' hV' ≤ tubeN N B hB := tubeN_mono (hV'V.trans hVB)
  set t₁ := D.capRestrict h₀ hle t
  have ht₁ : t₁ ∈ D.capPole h₀ n (tubeN N V' hV') (V' ×ˢ ball 0 F.ρ) :=
    D.capRestrict_mem_capPole h₀ hle (prod_mono hV'V subset_rfl) ht
  set s₁ : Fin K → _ := fun k ↦ D.capRestrict h₀ hleB (s k)
  have hs₁ : ∀ k, s₁ k ∈ D.capPole h₀ n (tubeN N V' hV') (V' ×ˢ ball 0 F.ρ) := fun k ↦
    D.capRestrict_mem_capPole h₀ hleB (prod_mono (hV'V.trans hVB) subset_rfl) (hs k)
  obtain ⟨t₂, ht₂, ht₂v, -⟩ := D.exists_capPole_sum h₀ hV'G hs₁ he
  obtain ⟨h1, -⟩ := D.capPole_ext h₀ hV'G ht₁ ht₂ hM hw hwρ fun b hb ↦ funext fun x ↦ by
    rw [D.evalVec_capRestrict h₀ hwρ hV'G hV'V _ hb, h b hb x,
      D.evalVec_eq_sum_of_evalFun h₀ hV'G hwρ ht₂v hb x]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [D.evalVec_capRestrict h₀ hwρ hV'G (hV'V.trans hVB) _ hb]
  intro y hy hyV'
  have hy' : y ∈ preim h₀ W (tubeN N V' hV') := by
    obtain ⟨hyN, -⟩ := mem_img_iff.1 ((mem_preim_iff h₀ W).1 hy)
    exact (mem_preim_iff h₀ W).2 (mem_img_iff.2 ⟨hyN, hyV'⟩)
  have h2 := congrArg (fun a : boundedSubring h₀ W _ ↦ evalFun a.1 y) h1
  simp only [t₁, capRestrict] at h2
  rw [evalFun_map W _ _ hy', ht₂v y hy'] at h2
  rw [h2]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  simp only [s₁, capRestrict]
  rw [evalFun_map W _ _ hy']

end

end ComplexAnalytic.Cap.AnnulusDecomposition
