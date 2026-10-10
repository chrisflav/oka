/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Heights.ModularJ
import Heights.ModularJFibers
import Mathlib.NumberTheory.Modular
import Mathlib.NumberTheory.ModularForms.ProperlyDiscontinuous
import Oka.Uniformization.CoveringLift
import Oka.Uniformization.Holomorphic

/-!
# The modular `j`-function off its branch values

`Heights.modularJ : ℍ → ℂ` is holomorphic and its fibres are exactly the `SL(2, ℤ)`-orbits
(`Heights.exists_smul_eq_of_modularJ_eq`). A point of `ℍ` with a nontrivial stabiliser (other than
`±1`) lies in the orbit of `i` or of `ρ` (Mathlib's `ModularGroup.stabilizer_of_ne`), so its
`j`-value lies in `jBranch = {j(i), j(ρ)}`. Off `jBranch`, `SL(2, ℤ)` acts with trivial stabilisers,
proper discontinuity makes `j` locally injective, and the inverse function theorem together with
transitivity on fibres gives continuous sections of `j` through every point over small discs
(`exists_section_jC`). This is the covering of `ℂ ∖ jBranch` by an open subset of `ℍ` from which the
uniformisation of `ℂ ∖ Λ` starts.

We work with `jC : ℂ → ℂ`, equal to `j` on `ℍ` and to `j(i) ∈ jBranch` elsewhere.
-/

open UpperHalfPlane ModularGroup Set Filter Topology Metric Matrix

open scoped MatrixGroups

namespace Uniformization

/-- The modular `j`-function as a function on `ℂ`: `j` on the upper half-plane, and the branch
value `j(i)` elsewhere. -/
noncomputable def jC (z : ℂ) : ℂ := by
  classical
  exact if h : 0 < z.im then Heights.modularJ ⟨z, h⟩ else Heights.modularJ I

/-- The two branch values `j(i)` and `j(ρ)`. -/
def jBranch : Set ℂ := {Heights.modularJ I, Heights.modularJ ρ}

theorem jC_coe (τ : ℍ) : jC τ = Heights.modularJ τ := by
  simp [jC, τ.im_pos]

theorem jC_of_im_pos {z : ℂ} (hz : 0 < z.im) : jC z = Heights.modularJ ⟨z, hz⟩ := by
  simp [jC, hz]

theorem im_pos_of_jC_notMem {z : ℂ} (h : jC z ∉ jBranch) : 0 < z.im := by
  by_contra hz
  apply h
  simp [jC, hz, jBranch]

theorem isClosed_jBranch : IsClosed jBranch :=
  ((Set.finite_singleton _).insert _).isClosed

theorem differentiableOn_jC : DifferentiableOn ℂ jC {z | 0 < z.im} := by
  have h := UpperHalfPlane.mdifferentiable_iff.mp Heights.modularJ_mdifferentiable
  refine h.congr fun z hz ↦ ?_
  simp only [Function.comp_apply, jC_of_im_pos hz, ofComplex_apply_of_im_pos hz]

theorem continuousOn_jC : ContinuousOn jC {z | 0 < z.im} := differentiableOn_jC.continuousOn

/-- Points with a stabiliser in `SL(2, ℤ)` other than `±1` have `j`-value in `jBranch`. -/
theorem modularJ_mem_jBranch_of_smul_eq {τ : ℍ} {γ : SL(2, ℤ)} (h : γ • τ = τ) (h1 : γ ≠ 1)
    (h2 : γ ≠ -1) : Heights.modularJ τ ∈ jBranch := by
  obtain ⟨g, hg⟩ := exists_smul_mem_fd τ
  have hfix : (g * γ * g⁻¹) • (g • τ) = g • τ := by
    rw [mul_smul, mul_smul, inv_smul_smul, h]
  have hj : Heights.modularJ τ = Heights.modularJ (g • τ) := (Heights.modularJ_smul g τ).symm
  by_contra hB
  have hI : g • τ ≠ I := fun e ↦ hB (by rw [hj, e]; simp [jBranch])
  have hρ : g • τ ≠ ρ := fun e ↦ hB (by rw [hj, e]; simp [jBranch])
  have hρ' : g • τ ≠ (1 : ℝ) +ᵥ ρ := fun e ↦ hB (by
    rw [hj, e, ← modular_T_smul, Heights.modularJ_smul]; simp [jBranch])
  rcases stabilizer_of_ne hg hfix hI hρ hρ' with h' | h'
  · apply h1
    have := congrArg (fun x ↦ g⁻¹ * x * g) h'
    simpa [mul_assoc] using this
  · apply h2
    have := congrArg (fun x ↦ g⁻¹ * x * g) h'
    simpa [mul_assoc] using this

/-- `j` is locally injective at points whose `j`-value is not a branch value. -/
theorem exists_nhds_injOn_modularJ {τ₀ : ℍ} (h : Heights.modularJ τ₀ ∉ jBranch) :
    ∃ U ∈ 𝓝 τ₀, InjOn Heights.modularJ U := by
  obtain ⟨U, hU, hUγ⟩ := ProperlyDiscontinuousSMul.exists_nhds_image_smul_eq_self 𝒮ℒ τ₀
  refine ⟨U, hU, fun τ hτ τ' hτ' hjj ↦ ?_⟩
  obtain ⟨γ, hγ⟩ := Heights.exists_smul_eq_of_modularJ_eq τ τ' hjj
  let g : 𝒮ℒ := ⟨SpecialLinearGroup.mapGL ℝ γ, γ, rfl⟩
  have hg : ∀ x : ℍ, g • x = γ • x := fun x ↦ rfl
  have hfix : g • τ₀ = τ₀ := hUγ g ⟨τ, ⟨τ', hτ', show g • τ' = τ by rw [hg, hγ]⟩, hτ⟩
  rw [hg] at hfix
  by_cases h1 : γ = 1
  · rw [← hγ, h1, one_smul]
  by_cases h2 : γ = -1
  · rw [← hγ, h2, SL_neg_smul, one_smul]
  exact absurd (modularJ_mem_jBranch_of_smul_eq hfix h1 h2) h

theorem exists_nhds_injOn_jC {z : ℂ} (h : jC z ∉ jBranch) : ∃ W ∈ 𝓝 z, InjOn jC W := by
  have hz := im_pos_of_jC_notMem h
  set τ₀ : ℍ := ⟨z, hz⟩
  rw [jC_of_im_pos hz] at h
  obtain ⟨U, hU, hinj⟩ := exists_nhds_injOn_modularJ (τ₀ := τ₀) h
  refine ⟨(↑) '' U, ?_, ?_⟩
  · have := isOpenEmbedding_coe.isOpenMap.image_mem_nhds hU
    simpa using this
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy
    rw [jC_coe, jC_coe] at hxy
    rw [hinj hx hy hxy]

theorem deriv_jC_ne_zero {z : ℂ} (h : jC z ∉ jBranch) : deriv jC z ≠ 0 := by
  obtain ⟨W, hW, hinj⟩ := exists_nhds_injOn_jC h
  have hz := im_pos_of_jC_notMem h
  have hopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  exact deriv_ne_zero_of_injOn (differentiableOn_jC.mono inter_subset_right)
    (inter_mem hW (hopen.mem_nhds hz)) (hinj.mono inter_subset_left)

theorem hasStrictDerivAt_jC {z : ℂ} (hz : 0 < z.im) : HasStrictDerivAt jC (deriv jC z) z := by
  have hopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  exact (differentiableOn_jC.analyticAt (hopen.mem_nhds hz)).hasStrictDerivAt

/-- The Möbius action of `γ ∈ SL(2, ℤ)` as a function on `ℂ` (zero off `ℍ`). -/
noncomputable def smulC (γ : SL(2, ℤ)) (z : ℂ) : ℂ := by
  classical
  exact if h : 0 < z.im then ((γ • (⟨z, h⟩ : ℍ) : ℍ) : ℂ) else 0

theorem smulC_of_im_pos (γ : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) :
    smulC γ z = ((γ • (⟨z, hz⟩ : ℍ) : ℍ) : ℂ) := by
  simp [smulC, hz]

theorem continuousOn_smulC (γ : SL(2, ℤ)) : ContinuousOn (smulC γ) {z | 0 < z.im} := by
  have hopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  rw [hopen.continuousOn_iff]
  intro z hz
  have hcont : ContinuousAt (fun τ : ℍ ↦ ((γ • τ : ℍ) : ℂ)) (ofComplex z) :=
    (continuous_coe.comp (continuous_const_smul (γ : GL (Fin 2) ℝ))).continuousAt
  have heq : smulC γ =ᶠ[𝓝 z] (fun τ : ℍ ↦ ((γ • τ : ℍ) : ℂ)) ∘ ofComplex := by
    filter_upwards [hopen.mem_nhds hz] with w hw
    simp [smulC_of_im_pos γ hw, ofComplex_apply_of_im_pos hw]
  refine ContinuousAt.congr ?_ heq.symm
  refine hcont.comp ?_
  have hsrc : z ∈ ofComplex.source := by
    change z ∈ (isOpenEmbedding_coe.toOpenPartialHomeomorph _).target
    simp only [IsOpenEmbedding.toOpenPartialHomeomorph_target]
    exact ⟨⟨z, hz⟩, rfl⟩
  exact ofComplex.continuousOn.continuousAt (ofComplex.open_source.mem_nhds hsrc)

theorem jC_smulC (γ : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) : jC (smulC γ z) = jC z := by
  rw [smulC_of_im_pos γ hz, jC_coe, Heights.modularJ_smul, jC_of_im_pos hz]

theorem im_smulC_pos (γ : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) : 0 < (smulC γ z).im := by
  rw [smulC_of_im_pos γ hz]; exact (γ • (⟨z, hz⟩ : ℍ)).im_pos

/-- **Sections of `j`.** Every point `w ∉ jBranch` has a disc `ball w ε`, disjoint from `jBranch`,
over which `j` has a continuous section through every point of `ℍ` above the disc. -/
theorem exists_section_jC {w : ℂ} (hw : w ∉ jBranch) :
    ∃ ε > 0, Disjoint (ball w ε) jBranch ∧ ∀ z, jC z ∈ ball w ε →
      ∃ s : ℂ → ℂ, ContinuousOn s (ball w ε) ∧ (∀ y ∈ ball w ε, jC (s y) = y) ∧
        (∀ y ∈ ball w ε, 0 < (s y).im) ∧ s (jC z) = z := by
  obtain ⟨τ₀, hτ₀⟩ := Heights.modularJ_surjective w
  have hj₀ : jC τ₀ = w := by rw [jC_coe, hτ₀]
  have hne : deriv jC τ₀ ≠ 0 := deriv_jC_ne_zero (by rwa [hj₀])
  obtain ⟨ε₁, hε₁, s₀, hs₀c, hs₀, -⟩ := exists_localSection (hasStrictDerivAt_jC τ₀.im_pos) hne
  rw [hj₀] at hs₀c hs₀
  obtain ⟨ε₂, hε₂, hε₂B⟩ := Metric.isOpen_iff.mp isClosed_jBranch.isOpen_compl w hw
  set ε := min ε₁ ε₂
  have hε : 0 < ε := lt_min hε₁ hε₂
  have hsub₁ : ball w ε ⊆ ball w ε₁ := ball_subset_ball (min_le_left _ _)
  have hsub₂ : ball w ε ⊆ ball w ε₂ := ball_subset_ball (min_le_right _ _)
  have hdisj : Disjoint (ball w ε) jBranch :=
    Set.disjoint_left.mpr fun y hy hyB ↦ hε₂B (hsub₂ hy) hyB
  have hs₀im : ∀ y ∈ ball w ε, 0 < (s₀ y).im := fun y hy ↦
    im_pos_of_jC_notMem (by rw [hs₀ y (hsub₁ hy)]; exact Set.disjoint_left.mp hdisj hy)
  refine ⟨ε, hε, hdisj, fun z hz ↦ ?_⟩
  have hzim : 0 < z.im := im_pos_of_jC_notMem (Set.disjoint_left.mp hdisj hz)
  have hy0 := hs₀im _ hz
  obtain ⟨γ, hγ⟩ := Heights.exists_smul_eq_of_modularJ_eq ⟨z, hzim⟩ ⟨s₀ (jC z), hy0⟩ (by
    rw [← jC_of_im_pos hzim, ← jC_of_im_pos hy0, hs₀ _ (hsub₁ hz)])
  refine ⟨smulC γ ∘ s₀, (continuousOn_smulC γ).comp (hs₀c.mono hsub₁) hs₀im,
    fun y hy ↦ ?_, fun y hy ↦ im_smulC_pos γ (hs₀im y hy), ?_⟩
  · simp only [Function.comp_apply]
    rw [jC_smulC γ (hs₀im y hy), hs₀ y (hsub₁ hy)]
  · simp only [Function.comp_apply]
    rw [smulC_of_im_pos γ hy0, hγ]

end Uniformization
