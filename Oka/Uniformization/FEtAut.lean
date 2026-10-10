/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Uniformization.FEtTransitive
import Oka.Uniformization.Uniqueness

/-!
# Automorphisms of finite étale covers lift to Möbius transformations

Let `(G₁, G₂, π)` uniformise a once-punctured elliptic curve `W ∖ O`, and let `A` be a
`ℂ`-algebra whose points are the affine points of `W` (through coordinates `x, y ∈ A`), with
`ι₀ : A → (ℍ → ℂ)` the pull-back along `π`. For a finite étale `A`-algebra `B` (hypotheses of
`FEtCovering`, `FEtTransitive`), a holomorphic lift `ι` of `B` and a `ℂ`-algebra automorphism `σ`
of `B` (not necessarily over `A`), there is `g ∈ SL(2, ℝ)` with `ι τ (σ b) = ι (g • τ) b`
(`FEt.exists_mobius`).

The map `τ ↦ ι τ ∘ σ ∘ (A → B)` is a holomorphic map to the curve; its lift `T` through `π`
(normalised by transitivity) satisfies `ι (T τ) = ι τ ∘ σ` by uniqueness of lifts in the covering
of points of `B`. The lifts for `σ` and `σ⁻¹` compose to deck transformations, so `T` is a
holomorphic bijection of `ℍ`, i.e. a Möbius transformation.
-/

open Complex Metric Set Filter Topology Polynomial
open UpperHalfPlane hiding I I_re I_im
open scoped MatrixGroups

namespace Uniformization

namespace IsUniformization

variable {W : WeierstrassCurve ℂ} {G₁ G₂ : SL(2, ℝ)} {π : ℂ → ℂ × ℂ}

/-- A continuous lift through `π` of a holomorphic map is holomorphic. -/
theorem holomorphicH_of_lift' (h : IsUniformization W G₁ G₂ π) {π' : ℂ → ℂ × ℂ}
    (hπ' : ∀ τ : ℍ, DifferentiableAt ℂ π' τ) {T : ℍ → ℍ} (hT : Continuous T)
    (hTπ : ∀ τ, π (T τ) = π' τ) : HolomorphicH T := by
  intro w hw
  set τ : ℍ := ⟨w, hw⟩
  have hofc : ContinuousAt (fun v ↦ ((T (ofComplex v) : ℍ) : ℂ)) w := by
    refine (continuous_coe.comp hT).continuousAt.comp ?_
    exact ofComplex.continuousOn.continuousAt (ofComplex.open_source.mem_nhds (by
      change w ∈ (isOpenEmbedding_coe.toOpenPartialHomeomorph _).target
      simp only [IsOpenEmbedding.toOpenPartialHomeomorph_target]
      exact ⟨τ, rfl⟩))
  have hofw : (ofComplex w : ℍ) = τ := ofComplex_apply_of_im_pos hw
  have hev : ∀ᶠ v in 𝓝 w, π (T (ofComplex v)) = π' v := by
    filter_upwards [isOpen_upper.mem_nhds hw] with v hv
    rw [hTπ, ofComplex_of_im_pos hv]
  rcases h.deriv_fst_or_snd (T τ) with h1 | h2
  · refine (differentiableAt_of_comp_eq (f := fun v ↦ (π v).1) (g := fun v ↦ (π' v).1)
      (by rw [hofw]; exact h.hasStrictDerivAt_fst (T τ)) h1 hofc
      (hev.mono fun v hv ↦ by simp only [hv]) ?_).differentiableWithinAt
    exact ((ContinuousLinearMap.fst ℂ ℂ ℂ).differentiable.differentiableAt).comp w (hπ' τ)
  · refine (differentiableAt_of_comp_eq (f := fun v ↦ (π v).2) (g := fun v ↦ (π' v).2)
      (by rw [hofw]; exact h.hasStrictDerivAt_snd (T τ)) h2 hofc
      (hev.mono fun v hv ↦ by simp only [hv]) ?_).differentiableWithinAt
    exact ((ContinuousLinearMap.snd ℂ ℂ ℂ).differentiable.differentiableAt).comp w (hπ' τ)

end IsUniformization

namespace FEt

variable {A B : Type*} [CommRing A] [Algebra ℂ A] [CommRing B] [Algebra ℂ B] [Algebra A B]
  [IsScalarTower ℂ A B] {ι₀ : A →ₐ[ℂ] (ℍ → ℂ)}
  {W : WeierstrassCurve ℂ} {G₁ G₂ : SL(2, ℝ)} {π : ℂ → ℂ × ℂ}

omit [IsScalarTower ℂ A B] in
/-- The value of a lift on `A` is `ι₀`. -/
theorem IsLift.apply_algebraMap {ι : ℍ → B → ℂ} (hι : IsLift ι₀ ι) (τ : ℍ) (a : A) :
    ι τ (algebraMap A B a) = ι₀ a τ := by
  obtain ⟨ψ, hψ⟩ := hι.pt τ
  rw [← hψ, ψ.2, pt_apply]

variable [IsDomain B] [Algebra.IsIntegral A B]

/-- A lift of an automorphism of `B` to a holomorphic map of `ℍ`. -/
theorem exists_lift_aut [W.IsElliptic] (h : IsUniformization W G₁ G₂ π) {x y : A}
    (hx : ∀ τ, ι₀ x τ = (π τ).1) (hy : ∀ τ, ι₀ y τ = (π τ).2)
    (hxy : ∀ χ χ' : A →ₐ[ℂ] ℂ, χ x = χ' x → χ y = χ' y → χ = χ')
    (hW : ∀ χ : A →ₐ[ℂ] ℂ, W.toAffine.Equation (χ x) (χ y))
    (hhol : ∀ a, Unif.HolH (ι₀ a)) {n : ℕ}
    (hcount : ∀ τ, Nat.card (Over B (FEt.pt ι₀ τ)) = n) (hloc : ∀ τ, LocPres ι₀ (B := B) n τ)
    {h₀ : ℍ → ℂ} (hgrowth : ∀ a, PolyBdd h₀ fun τ ↦ ‖ι₀ a τ‖)
    (hpoly : ∀ g : ℍ → ℂ, Unif.HolH g → (∀ γ ∈ Subgroup.closure {G₁, G₂}, ∀ τ, g (γ • τ) = g τ) →
      PolyBdd h₀ (fun τ ↦ ‖g τ‖) → ∃ a, ∀ τ, ι₀ a τ = g τ)
    (hinj : Function.Injective ι₀) (σ : B ≃ₐ[ℂ] B) {ι : ℍ → B → ℂ} (hι : IsLift ι₀ ι)
    (hιh : ∀ b, Unif.HolH fun τ ↦ ι τ b) :
    ∃ T : ℍ → ℍ, Continuous T ∧ HolomorphicH T ∧ ∀ τ b, ι (T τ) b = ι τ (σ b) := by
  classical
  -- invariance and surjectivity of points
  have hpt_eq : ∀ τ τ' : ℍ, π τ = π τ' → FEt.pt ι₀ τ = FEt.pt ι₀ τ' := fun τ τ' hππ ↦
    hxy _ _ (by simp [hx, hππ]) (by simp [hy, hππ])
  have hΓ : ∀ γ ∈ Subgroup.closure {G₁, G₂}, ∀ (a : A) (τ : ℍ), ι₀ a (γ • τ) = ι₀ a τ := by
    intro γ hγ a τ
    have := hpt_eq (γ • τ) τ ((h.fibre τ (γ • τ)).mpr ⟨γ, hγ, rfl⟩).symm
    exact congrArg (fun χ : A →ₐ[ℂ] ℂ ↦ χ a) this
  have hsurj : ∀ χ : A →ₐ[ℂ] ℂ, ∃ τ, FEt.pt ι₀ τ = χ := by
    intro χ
    obtain ⟨τ, hτ⟩ := h.surj (χ x) (χ y) (hW χ)
    exact ⟨τ, hxy _ _ (by simp [hx, hτ]) (by simp [hy, hτ])⟩
  -- the twisted points
  choose ψτ hψτ using hι.pt
  set j : A →ₐ[ℂ] B := IsScalarTower.toAlgHom ℂ A B
  set χσ : ℍ → A →ₐ[ℂ] ℂ := fun τ ↦ (ψτ τ).1.comp (σ.toAlgHom.comp j)
  have hχσ : ∀ τ a, χσ τ a = ι τ (σ (algebraMap A B a)) := fun τ a ↦ by
    simp [χσ, j, ← hψτ]
  set Q : ℍ → V W := fun τ ↦ ⟨(χσ τ x, χσ τ y), hW _⟩
  have hQc : Continuous Q := by
    refine Continuous.subtype_mk ?_ _
    simp only [hχσ]
    exact (hι.cont _).prodMk (hι.cont _)
  -- the base point
  set τ₀ := UpperHalfPlane.I
  obtain ⟨τ', hτ'⟩ := hsurj (χσ τ₀)
  set ψ' : Over B (FEt.pt ι₀ τ') := ⟨(ψτ τ₀).1.comp σ.toAlgHom, fun a ↦ by
    rw [hτ']; simp [χσ, j]⟩
  obtain ⟨ι'', hι'', hι''τ, -⟩ := exists_isLift hhol hcount hloc τ' ψ'
  obtain ⟨γ, -, hγ⟩ := exists_smul_eq hhol hcount hloc hΓ hgrowth hpoly hinj hι hιh hι''
  set τ₁ := γ • τ'
  have hτ₁ : ∀ b, ι τ₁ b = ι τ₀ (σ b) := by
    intro b
    have := congrFun (congrFun hγ τ') b
    rw [← this, hι''τ]
    simp [ψ', ← hψτ]
  have hπτ₁ : h.toV τ₁ = Q τ₀ := by
    apply Subtype.ext
    simp only [IsUniformization.toV, Q]
    rw [hχσ, hχσ, ← hτ₁, ← hτ₁, hι.apply_algebraMap, hι.apply_algebraMap, hx, hy]
  obtain ⟨T, ⟨hT0, hT⟩, -⟩ := h.isCoveringMap.existsUnique_continuousMap_lifts ⟨Q, hQc⟩ τ₀ τ₁
    hπτ₁
  have hTQ : ∀ τ, π (T τ) = (χσ τ x, χσ τ y) := fun τ ↦ congrArg Subtype.val (congrFun hT τ)
  -- `ι ∘ T = ι ∘ σ`
  have hcovB := isCoveringMap_proj hhol hcount hloc
  have hmem : ∀ τ, ∃ ψ : Over B (FEt.pt ι₀ (T τ)), ⇑ψ.1 = fun b ↦ ι τ (σ b) := by
    intro τ
    have hχ : χσ τ = FEt.pt ι₀ (T τ) := hxy _ _ (by simp [hx, hTQ]) (by simp [hy, hTQ])
    refine ⟨⟨(ψτ τ).1.comp σ.toAlgHom, fun a ↦ ?_⟩, ?_⟩
    · rw [← hχ]; simp [χσ, j]
    · funext b; simp [← hψτ]
  set s₂ : ℍ → Tot B ι₀ := fun τ ↦ ⟨(T τ, fun b ↦ ι τ (σ b)), hmem τ⟩
  have hs₂ : Continuous s₂ :=
    (T.continuous.prodMk (continuous_pi fun b ↦ hι.cont (σ b))).subtype_mk _
  have hs₁ : Continuous (fun τ ↦ hι.sec (T τ)) := hι.continuous_sec.comp T.continuous
  have heq := hcovB.eq_of_comp_eq hs₁ hs₂ rfl τ₀ (by
    apply Subtype.ext
    simp only [IsLift.sec, s₂, hT0]
    exact Prod.ext rfl (funext hτ₁))
  have hιT : ∀ τ b, ι (T τ) b = ι τ (σ b) := fun τ b ↦
    congrFun (congrArg (fun p : Tot B ι₀ ↦ p.1.2) (congrFun heq τ)) b
  -- holomorphy
  refine ⟨T, T.continuous, h.holomorphicH_of_lift'
    (π' := fun z ↦ (ι (ofComplex z) (σ (algebraMap A B x)), ι (ofComplex z) (σ (algebraMap A B y))))
    (fun τ ↦ ?_) T.continuous (fun τ ↦ ?_), hιT⟩
  · have h1 := ((hιh (σ (algebraMap A B x))) _ τ.im_pos).differentiableAt
      (isOpen_upper.mem_nhds τ.im_pos)
    have h2 := ((hιh (σ (algebraMap A B y))) _ τ.im_pos).differentiableAt
      (isOpen_upper.mem_nhds τ.im_pos)
    exact h1.prodMk h2
  · rw [hTQ, hχσ, hχσ, ofComplex_apply]

/-- **Automorphisms of `B` are Möbius transformations**: for a `ℂ`-algebra automorphism `σ` of
`B` and a holomorphic lift `ι`, there is `g ∈ SL(2, ℝ)` with `ι τ (σ b) = ι (g • τ) b`. -/
theorem exists_mobius [W.IsElliptic] (h : IsUniformization W G₁ G₂ π) {x y : A}
    (hx : ∀ τ, ι₀ x τ = (π τ).1) (hy : ∀ τ, ι₀ y τ = (π τ).2)
    (hxy : ∀ χ χ' : A →ₐ[ℂ] ℂ, χ x = χ' x → χ y = χ' y → χ = χ')
    (hW : ∀ χ : A →ₐ[ℂ] ℂ, W.toAffine.Equation (χ x) (χ y))
    (hhol : ∀ a, Unif.HolH (ι₀ a)) {n : ℕ}
    (hcount : ∀ τ, Nat.card (Over B (FEt.pt ι₀ τ)) = n) (hloc : ∀ τ, LocPres ι₀ (B := B) n τ)
    {h₀ : ℍ → ℂ} (hgrowth : ∀ a, PolyBdd h₀ fun τ ↦ ‖ι₀ a τ‖)
    (hpoly : ∀ g : ℍ → ℂ, Unif.HolH g → (∀ γ ∈ Subgroup.closure {G₁, G₂}, ∀ τ, g (γ • τ) = g τ) →
      PolyBdd h₀ (fun τ ↦ ‖g τ‖) → ∃ a, ∀ τ, ι₀ a τ = g τ)
    (hinj : Function.Injective ι₀) (σ : B ≃ₐ[ℂ] B) {ι : ℍ → B → ℂ} (hι : IsLift ι₀ ι)
    (hιh : ∀ b, Unif.HolH fun τ ↦ ι τ b) :
    ∃ g : SL(2, ℝ), ∀ τ b, ι τ (σ b) = ι (g • τ) b := by
  obtain ⟨T, hTc, hTh, hT⟩ := exists_lift_aut h hx hy hxy hW hhol hcount hloc hgrowth hpoly hinj
    σ hι hιh
  obtain ⟨T', hT'c, hT'h, hT'⟩ := exists_lift_aut h hx hy hxy hW hhol hcount hloc hgrowth hpoly
    hinj σ.symm hι hιh
  -- `T ∘ T'` and `T' ∘ T` are deck transformations
  have hdeck : ∀ {S : ℍ → ℍ}, Continuous S → (∀ τ b, ι (S τ) b = ι τ b) →
      ∃ γ ∈ Subgroup.closure {G₁, G₂}, ∀ τ, S τ = γ • τ := by
    intro S hSc hS
    have hπ : ∀ τ, π (S τ) = π τ := fun τ ↦ by
      have h1 := hS τ (algebraMap A B x)
      have h2 := hS τ (algebraMap A B y)
      rw [hι.apply_algebraMap, hι.apply_algebraMap, hx, hx] at h1
      rw [hι.apply_algebraMap, hι.apply_algebraMap, hy, hy] at h2
      exact Prod.ext h1 h2
    obtain ⟨γ, hγ, hγτ⟩ := (h.fibre UpperHalfPlane.I (S UpperHalfPlane.I)).mp
      (hπ UpperHalfPlane.I).symm
    refine ⟨γ, hγ, fun τ ↦ ?_⟩
    have := h.isCoveringMap.eq_of_comp_eq hSc (continuous_const_smul γ) (by
      funext τ; simp only [Function.comp_apply, h.toV_smul hγ]; exact Subtype.ext (hπ τ))
      UpperHalfPlane.I hγτ.symm
    exact congrFun this τ
  obtain ⟨γ, -, hγ⟩ := hdeck (hTc.comp hT'c) fun τ b ↦ by
    simp only [Function.comp_apply]; rw [hT, hT', AlgEquiv.symm_apply_apply]
  obtain ⟨γ', -, hγ'⟩ := hdeck (hT'c.comp hTc) fun τ b ↦ by
    simp only [Function.comp_apply]; rw [hT', hT, AlgEquiv.apply_symm_apply]
  have hTinj : Function.Injective T := fun a b hab ↦ by
    have := congrArg T' hab
    rw [show T' (T a) = γ' • a from hγ' a, show T' (T b) = γ' • b from hγ' b] at this
    exact smul_left_cancel γ' this
  set S : ℍ → ℍ := fun τ ↦ T' (γ⁻¹ • τ)
  have hTS : ∀ τ, T (S τ) = τ := fun τ ↦ by
    simp only [S]; rw [show T (T' (γ⁻¹ • τ)) = γ • γ⁻¹ • τ from hγ _, smul_inv_smul]
  have hST : ∀ τ, S (T τ) = τ := fun τ ↦ hTinj (hTS (T τ))
  obtain ⟨g, hg⟩ := exists_SL2R_eq_of_holomorphic hTh (hT'h.comp_smul γ⁻¹) hTS hST
  exact ⟨g, fun τ b ↦ by rw [← hg, hT]⟩

end FEt

end Uniformization
