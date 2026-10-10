/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Uniformization.FEtLocal
import Oka.Uniformization.CoveringLift

/-!
# Finite étale algebras over holomorphic functions on `ℍ` embed into holomorphic functions

With the hypotheses of `FEtLocal` at every point of `ℍ`, the space of pairs `(τ, ψ)` with `ψ` a
point of `B` over `χ_τ` is a covering of `ℍ` (`FEt.isCoveringMap_proj`); since `ℍ` is simply
connected, every point `ψ₀` over `χ_{τ₀}` lies on a global section, i.e. extends to an
`A`-algebra map `ι : B → (ℍ → ℂ)` into holomorphic functions (`FEt.exists_lift`), unique among
continuous ones (`FEt.lift_unique`).
-/

open Complex Metric Set Filter Topology Polynomial
open UpperHalfPlane hiding I I_re I_im
open scoped MatrixGroups

namespace Uniformization

namespace FEt

variable {A B : Type*} [CommRing A] [Algebra ℂ A] [CommRing B] [Algebra ℂ B] [Algebra A B]
  (ι₀ : A →ₐ[ℂ] (ℍ → ℂ))

variable (B) in
/-- The total space: points `(τ, ψ)` with `ψ` a point of `B` over `χ_τ`. -/
abbrev Tot : Type _ := {p : ℍ × (B → ℂ) // ∃ ψ : Over B (pt ι₀ p.1), ⇑ψ.1 = p.2}

/-- The projection to `ℍ`. -/
def proj (p : Tot B ι₀) : ℍ := p.1.1

theorem continuous_proj : Continuous (proj ι₀ (B := B)) :=
  continuous_fst.comp continuous_subtype_val

/-- The local presentations. -/
def LocPres (n : ℕ) (τ : ℍ) : Prop :=
  ∃ (b₀ : B) (F : A[X]) (δ : A), F.Monic ∧ F.natDegree = n ∧ aeval b₀ F = 0 ∧ ι₀ δ τ ≠ 0 ∧
    ∀ b : B, algebraMap A B δ * b ∈ Algebra.adjoin A {b₀}

/-- **A chart**: near `τ₁`, the points over `χ_τ` are `n` explicit holomorphic families,
separated by their values at `b₀`. -/
theorem exists_chart (hhol : ∀ a, Unif.HolH (ι₀ a)) {n : ℕ}
    (hcount : ∀ τ, Nat.card (Over B (pt ι₀ τ)) = n) (τ₁ : ℍ) (hloc : LocPres ι₀ (B := B) n τ₁) :
    ∃ V : Set ℍ, IsOpen V ∧ τ₁ ∈ V ∧ IsPreconnected V ∧
      ∃ (b₀ : B) (ε : ℝ) (σ : Fin n → ℍ → B → ℂ), 0 < ε ∧
        (∀ τ ∈ V, ∀ j k, j ≠ k → ε < ‖σ j τ b₀ - σ k τ b₀‖) ∧
        (∀ τ ∈ V, ∀ j, ∃ ψ : Over B (pt ι₀ τ), ⇑ψ.1 = σ j τ) ∧
        (∀ τ ∈ V, ∀ ψ : Over B (pt ι₀ τ), ∃ j, ⇑ψ.1 = σ j τ) ∧
        (∀ j b, DifferentiableOn ℂ (fun z ↦ σ j (ofComplex z) b) ((↑) '' V)) ∧
        (∀ j b, ContinuousOn (fun τ ↦ σ j τ b) V) ∧
        (∀ j, ContinuousOn (fun τ ↦ σ j τ b₀) V) := by
  classical
  obtain ⟨b₀, F, δ, hFm, hFn, hF, hδ, hpres⟩ := hloc
  obtain ⟨O, hOo, hτO, hOi, hOδ, r, hra, hrinj, hroot, hsurj⟩ :=
    exists_local ι₀ hhol hcount τ₁ hFm hFn hF hδ hpres
  -- the polynomial expressions `δ b = P_b(b₀)`
  have hP : ∀ b : B, ∃ P : A[X], aeval b₀ P = algebraMap A B δ * b := fun b ↦ by
    have := hpres b
    rw [Algebra.adjoin_singleton_eq_range_aeval] at this
    exact this
  choose P hPb using hP
  set σ : Fin n → ℍ → B → ℂ := fun j τ b ↦ ((P b).map (pt ι₀ τ : A →+* ℂ)).eval (r j τ) / ι₀ δ τ
  have hσψ : ∀ τ : ℍ, (τ : ℂ) ∈ O → ∀ j, ∀ ψ : Over B (pt ι₀ τ), ψ.1 b₀ = r j τ →
      ⇑ψ.1 = σ j τ := by
    intro τ hτ j ψ hψ
    funext b
    have h1 := congrArg ψ.1 (hPb b)
    rw [Over.apply_aeval, map_mul, ψ.2, hψ] at h1
    simp only [σ]
    rw [h1, pt_apply, mul_div_cancel_left₀ _ (hOδ τ hτ)]
  have hσb₀ : ∀ τ : ℍ, (τ : ℂ) ∈ O → ∀ j, σ j τ b₀ = r j τ := by
    intro τ hτ j
    obtain ⟨ψ, hψ⟩ := hsurj τ hτ j
    rw [← hσψ τ hτ j ψ hψ, hψ]
  -- separation at `τ₁`
  obtain ⟨ε, hε, hεsep⟩ : ∃ ε > 0, ∀ j k : Fin n, j ≠ k → 2 * ε < ‖r j τ₁ - r k τ₁‖ := by
    rcases (Finset.univ.offDiag : Finset (Fin n × Fin n)).eq_empty_or_nonempty with he | hne
    · refine ⟨1, one_pos, fun j k hjk ↦ ?_⟩
      have : (j, k) ∈ (Finset.univ.offDiag : Finset (Fin n × Fin n)) :=
        Finset.mem_offDiag.mpr ⟨Finset.mem_univ _, Finset.mem_univ _, hjk⟩
      rw [he] at this; simp at this
    · set m := (Finset.univ.offDiag).inf' hne fun jk : Fin n × Fin n ↦ ‖r jk.1 τ₁ - r jk.2 τ₁‖
      have hm : 0 < m := by
        rw [Finset.lt_inf'_iff]
        rintro ⟨j, k⟩ hjk
        simp only [Finset.mem_offDiag, Finset.mem_univ, true_and] at hjk
        exact norm_pos_iff.mpr (sub_ne_zero.mpr fun h ↦ hjk (hrinj _ hτO h))
      refine ⟨m / 4, by positivity, fun j k hjk ↦ ?_⟩
      have : m ≤ ‖r j τ₁ - r k τ₁‖ := Finset.inf'_le (f := fun jk : Fin n × Fin n ↦
        ‖r jk.1 τ₁ - r jk.2 τ₁‖) (b := (j, k))
        (Finset.mem_offDiag.mpr ⟨Finset.mem_univ _, Finset.mem_univ _, hjk⟩)
      linarith
  -- the separation persists near `τ₁`
  have hsepO : ∀ᶠ z in 𝓝 (τ₁ : ℂ), ∀ j k : Fin n, j ≠ k → ε < ‖r j z - r k z‖ := by
    rw [eventually_all]; intro j; rw [eventually_all]; intro k
    by_cases hjk : j = k
    · exact Eventually.of_forall fun _ h ↦ absurd hjk h
    · have hc : ContinuousAt (fun z ↦ ‖r j z - r k z‖) τ₁ :=
        (((hra j) _ hτO).continuousAt.sub ((hra k) _ hτO).continuousAt).norm
      have := hc.eventually (lt_mem_nhds (show ε < ‖r j τ₁ - r k τ₁‖ by
        linarith [hεsep j k hjk]))
      exact this.mono fun z hz _ ↦ hz
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem (hOo.mem_nhds hτO) hsepO)
  set V : Set ℍ := (↑) ⁻¹' ball (τ₁ : ℂ) ρ
  have hVO : ∀ τ ∈ V, (τ : ℂ) ∈ O := fun τ hτ ↦ (hball hτ).1
  have himg : ((↑) : ℍ → ℂ) '' V = ball (τ₁ : ℂ) ρ := by
    ext z
    constructor
    · rintro ⟨τ, hτ, rfl⟩; exact hτ
    · intro hz
      exact ⟨⟨z, hOi z (hball hz).1⟩, hz, rfl⟩
  have hVpre : IsPreconnected V := by
    rw [← UpperHalfPlane.isEmbedding_coe.isInducing.isPreconnected_image, himg]
    exact (convex_ball _ _).isPreconnected
  have hσdiff : ∀ j b, DifferentiableOn ℂ (fun z ↦ σ j (ofComplex z) b) ((↑) '' V) := by
    intro j b
    rw [himg]
    have hsub : ball (τ₁ : ℂ) ρ ⊆ O := fun z hz ↦ (hball hz).1
    have hup : ball (τ₁ : ℂ) ρ ⊆ {z | 0 < z.im} := fun z hz ↦ hOi z (hsub hz)
    have hr' : DifferentiableOn ℂ (fun z ↦ r j z) (ball (τ₁ : ℂ) ρ) :=
      ((hra j).differentiableOn).mono hsub
    have hr'' : DifferentiableOn ℂ (fun z ↦ r j (ofComplex z : ℂ)) (ball (τ₁ : ℂ) ρ) :=
      hr'.congr fun z hz ↦ by rw [ofComplex_apply_of_im_pos (hup hz)]
    simp only [σ, eval_map, eval₂_eq_sum_range]
    refine DifferentiableOn.div ?_ ((hhol δ).mono hup) fun z hz ↦ ?_
    · refine DifferentiableOn.fun_sum fun i _ ↦ ?_
      exact ((hhol _).mono hup).mul (hr''.pow _)
    · have := hOδ (ofComplex z) (by rw [ofComplex_apply_of_im_pos (hup hz)]; exact hsub hz)
      exact this
  have hσcont : ∀ j b, ContinuousOn (fun τ ↦ σ j τ b) V := by
    intro j b
    have h1 := (hσdiff j b).continuousOn
    have h2 : ContinuousOn ((↑) : ℍ → ℂ) V := continuous_coe.continuousOn
    have := h1.comp h2 (mapsTo_image _ _)
    refine this.congr fun τ _ ↦ ?_
    simp [Function.comp_apply]
  refine ⟨V, isOpen_ball.preimage continuous_coe, by simp [V, hρ], hVpre, b₀, ε, σ, hε,
    fun τ hτ j k hjk ↦ ?_, fun τ hτ j ↦ ?_, fun τ hτ ψ ↦ ?_, hσdiff, hσcont,
    fun j ↦ hσcont j b₀⟩
  · rw [hσb₀ τ (hVO τ hτ), hσb₀ τ (hVO τ hτ)]
    exact (hball hτ).2 j k hjk
  · obtain ⟨ψ, hψ⟩ := hsurj τ (hVO τ hτ) j
    exact ⟨ψ, hσψ τ (hVO τ hτ) j ψ hψ⟩
  · obtain ⟨j, hj⟩ := hroot τ (hVO τ hτ) ψ
    exact ⟨j, hσψ τ (hVO τ hτ) j ψ hj⟩

variable {ι₀}

/-- **The points of `B` form a covering of `ℍ`.** -/
theorem isCoveringMap_proj (hhol : ∀ a, Unif.HolH (ι₀ a)) {n : ℕ}
    (hcount : ∀ τ, Nat.card (Over B (pt ι₀ τ)) = n) (hloc : ∀ τ, LocPres ι₀ (B := B) n τ) :
    IsCoveringMap (proj ι₀ (B := B)) := by
  classical
  rw [isCoveringMap_iff_isCoveringMapOn_univ]
  refine isCoveringMapOn_of_sections (by simp) (continuous_proj ι₀).continuousOn ?_ ?_
  · -- local injectivity
    rintro ⟨⟨τ₁, φ⟩, hφ⟩ -
    obtain ⟨V, hVo, hτV, -, b₀, ε, σ, hε, hsep, -, hroot, -, -, hσb₀⟩ :=
      exists_chart ι₀ hhol hcount τ₁ (hloc τ₁)
    obtain ⟨ψ, hψ⟩ := hφ
    obtain ⟨j, hj⟩ := hroot τ₁ hτV ψ
    set g : Tot B ι₀ → ℂ := fun p ↦ p.1.2 b₀ - σ j (proj ι₀ p) b₀
    have hg : ContinuousOn g (proj ι₀ ⁻¹' V) :=
      ((continuous_apply b₀).comp (continuous_snd.comp continuous_subtype_val)).continuousOn.sub
        ((hσb₀ j).comp (continuous_proj ι₀).continuousOn (mapsTo_preimage _ _))
    have hWo : IsOpen (proj ι₀ ⁻¹' V ∩ g ⁻¹' ball 0 (ε / 2)) :=
      hg.isOpen_inter_preimage (hVo.preimage (continuous_proj ι₀)) isOpen_ball
    refine ⟨_, hWo.mem_nhds ⟨hτV, ?_⟩, ?_⟩
    · have hψ' : ⇑ψ.1 = φ := hψ
      simp only [mem_preimage, mem_ball, dist_zero_right, g, proj]
      rw [← hψ', hj, sub_self, norm_zero]; positivity
    · rintro ⟨⟨τ, φ₁⟩, hφ₁⟩ ⟨h1V, h1g⟩ ⟨⟨τ', φ₂⟩, hφ₂⟩ ⟨h2V, h2g⟩ (hττ' : τ = τ')
      subst hττ'
      obtain ⟨ψ₁, hψ₁⟩ := hφ₁
      obtain ⟨ψ₂, hψ₂⟩ := hφ₂
      replace hψ₁ : ⇑ψ₁.1 = φ₁ := hψ₁
      replace hψ₂ : ⇑ψ₂.1 = φ₂ := hψ₂
      obtain ⟨k, hk⟩ := hroot τ h1V ψ₁
      obtain ⟨l, hl⟩ := hroot τ h2V ψ₂
      simp only [mem_preimage, mem_ball, dist_zero_right, g, proj] at h1g h2g
      rw [← hψ₁, hk] at h1g
      rw [← hψ₂, hl] at h2g
      have hkj : k = j := by
        by_contra h
        have := hsep τ h1V k j h
        linarith
      have hlj : l = j := by
        by_contra h
        have := hsep τ h2V l j h
        linarith
      apply Subtype.ext
      simp only [Prod.mk.injEq, true_and]
      rw [← hψ₁, ← hψ₂, hk, hl, hkj, hlj]
  · -- local sections
    intro x _
    obtain ⟨V, hVo, hxV, hVpre, b₀, ε, σ, hε, hsep, hex, hroot, -, hσc, -⟩ :=
      exists_chart ι₀ hhol hcount x (hloc x)
    refine ⟨V, hVo, hxV, subset_univ _, hVpre, fun e he ↦ ?_⟩
    obtain ⟨ψe, hψe⟩ := e.2
    obtain ⟨j, hj⟩ := hroot _ he ψe
    have hmem : ∀ v ∈ V, ∃ ψ : Over B (pt ι₀ v), ⇑ψ.1 = σ j v := fun v hv ↦ hex v hv j
    let s : ℍ → Tot B ι₀ := fun v ↦ if hv : v ∈ V then ⟨(v, σ j v), hmem v hv⟩ else e
    refine ⟨s, ?_, fun v hv ↦ by simp [s, hv, proj], ?_⟩
    · rw [Topology.IsEmbedding.subtypeVal.isInducing.continuousOn_iff]
      have : ContinuousOn (fun v : ℍ ↦ (v, σ j v)) V :=
        continuousOn_id.prodMk (continuousOn_pi.mpr (hσc j))
      refine this.congr fun v hv ↦ ?_
      simp [s, hv]
    · have heV : proj ι₀ e ∈ V := he
      simp only [s, heV, dif_pos]
      apply Subtype.ext
      have h2 : σ j e.1.1 = e.1.2 := hj.symm.trans hψe
      simp only [proj, h2]

/-- **Lifting**: every point `ψ₀` over `χ_{τ₀}` extends to a holomorphic family of points. -/
theorem exists_lift (hhol : ∀ a, Unif.HolH (ι₀ a)) {n : ℕ}
    (hcount : ∀ τ, Nat.card (Over B (pt ι₀ τ)) = n) (hloc : ∀ τ, LocPres ι₀ (B := B) n τ)
    (τ₀ : ℍ) (ψ₀ : Over B (pt ι₀ τ₀)) :
    ∃ ι : ℍ → B → ℂ, (∀ τ, ∃ ψ : Over B (pt ι₀ τ), ⇑ψ.1 = ι τ) ∧ ι τ₀ = ⇑ψ₀.1 ∧
      ∀ b, Unif.HolH fun τ ↦ ι τ b := by
  classical
  have hcov := isCoveringMap_proj hhol hcount hloc
  set e₀ : Tot B ι₀ := ⟨(τ₀, ⇑ψ₀.1), ψ₀, rfl⟩
  obtain ⟨F, ⟨hF0, hF⟩, -⟩ := hcov.existsUnique_continuousMap_lifts ⟨id, continuous_id⟩ τ₀ e₀ rfl
  have hFp : ∀ τ, (F τ).1.1 = τ := fun τ ↦ congrFun hF τ
  have key : ∀ p : Tot B ι₀, ∀ τ, p.1.1 = τ → ∃ ψ : Over B (pt ι₀ τ), ⇑ψ.1 = p.1.2 := by
    rintro p τ rfl; exact p.2
  refine ⟨fun τ ↦ (F τ).1.2, fun τ ↦ key (F τ) τ (hFp τ), by change (F τ₀).1.2 = _; rw [hF0],
    fun b ↦ ?_⟩
  · intro z hz
    set τ₁ : ℍ := ⟨z, hz⟩
    obtain ⟨V, hVo, hτV, hVpre, b₀, ε, σ, hε, hsep, hex, hroot, hσd, hσc, -⟩ :=
      exists_chart ι₀ hhol hcount τ₁ (hloc τ₁)
    obtain ⟨ψ₁, hψ₁⟩ := key (F τ₁) τ₁ (hFp τ₁)
    obtain ⟨j, hj⟩ := hroot τ₁ hτV ψ₁
    have hmem : ∀ v ∈ V, ∃ ψ : Over B (pt ι₀ v), ⇑ψ.1 = σ j v := fun v hv ↦ hex v hv j
    let s : ℍ → Tot B ι₀ := fun v ↦ if hv : v ∈ V then ⟨(v, σ j v), hmem v hv⟩ else F τ₁
    have hsc : ContinuousOn s V := by
      rw [Topology.IsEmbedding.subtypeVal.isInducing.continuousOn_iff]
      have : ContinuousOn (fun v : ℍ ↦ (v, σ j v)) V :=
        continuousOn_id.prodMk (continuousOn_pi.mpr (hσc j))
      refine this.congr fun v hv ↦ ?_
      simp [s, hv]
    have hFs : EqOn F s V := hcov.eqOn_of_comp_eqOn hVpre F.continuous.continuousOn hsc
      (fun v hv ↦ by simp [s, hv, proj, hFp]) hτV (by
        simp only [s, hτV, dif_pos]
        apply Subtype.ext
        exact Prod.ext (hFp τ₁) (hψ₁.symm.trans hj))
    have hVz : ((↑) : ℍ → ℂ) '' V ∈ 𝓝 z :=
      (UpperHalfPlane.isOpenEmbedding_coe.isOpenMap V hVo).mem_nhds ⟨τ₁, hτV, rfl⟩
    have hd : DifferentiableAt ℂ (fun w ↦ σ j (ofComplex w) b) z := (hσd j b).differentiableAt hVz
    refine (hd.congr_of_eventuallyEq ?_).differentiableWithinAt
    filter_upwards [hVz] with w hw
    obtain ⟨τ, hτ, rfl⟩ := hw
    simp only [ofComplex_apply]
    rw [hFs hτ]
    simp [s, hτ]

/-- A holomorphic function on `ℍ` is continuous. -/
theorem _root_.Uniformization.Unif.HolH.continuous {f : ℍ → ℂ} (hf : Unif.HolH f) :
    Continuous f := by
  have := hf.continuousOn.comp_continuous continuous_coe fun τ ↦ τ.im_pos
  simpa [Function.comp_def, ofComplex_apply] using this

variable (ι₀) in
/-- A lift: a continuous family of points of `B` over the points `χ_τ`. -/
structure IsLift (ι : ℍ → B → ℂ) : Prop where
  pt : ∀ τ, ∃ ψ : Over B (pt ι₀ τ), ⇑ψ.1 = ι τ
  cont : ∀ b, Continuous fun τ ↦ ι τ b

/-- The section of `proj` given by a lift. -/
def IsLift.sec {ι : ℍ → B → ℂ} (h : IsLift ι₀ ι) (τ : ℍ) : Tot B ι₀ := ⟨(τ, ι τ), h.pt τ⟩

theorem IsLift.continuous_sec {ι : ℍ → B → ℂ} (h : IsLift ι₀ ι) : Continuous h.sec :=
  (continuous_id.prodMk (continuous_pi h.cont)).subtype_mk _

/-- **Uniqueness of lifts.** -/
theorem IsLift.eq (hcov : IsCoveringMap (proj ι₀ (B := B))) {ι ι' : ℍ → B → ℂ}
    (h : IsLift ι₀ ι) (h' : IsLift ι₀ ι') {τ₀ : ℍ} (h0 : ι τ₀ = ι' τ₀) : ι = ι' := by
  have := hcov.eq_of_comp_eq h.continuous_sec h'.continuous_sec rfl τ₀
    (Subtype.ext (Prod.ext rfl h0))
  funext τ
  exact congrArg (fun p : Tot B ι₀ ↦ p.1.2) (congrFun this τ)

/-- Lifts through every point exist and are holomorphic. -/
theorem exists_isLift (hhol : ∀ a, Unif.HolH (ι₀ a)) {n : ℕ}
    (hcount : ∀ τ, Nat.card (Over B (pt ι₀ τ)) = n) (hloc : ∀ τ, LocPres ι₀ (B := B) n τ)
    (τ₀ : ℍ) (ψ₀ : Over B (pt ι₀ τ₀)) :
    ∃ ι : ℍ → B → ℂ, IsLift ι₀ ι ∧ ι τ₀ = ⇑ψ₀.1 ∧ ∀ b, Unif.HolH fun τ ↦ ι τ b := by
  obtain ⟨ι, h1, h2, h3⟩ := exists_lift hhol hcount hloc τ₀ ψ₀
  exact ⟨ι, ⟨h1, fun b ↦ (h3 b).continuous⟩, h2, h3⟩

end FEt

end Uniformization
