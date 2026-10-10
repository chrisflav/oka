/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Oka.Uniformization.Cayley
import Oka.Uniformization.CoveringLimit
import Oka.Uniformization.ModularCovering

/-!
# The universal covering of the complement of a lattice

For a period lattice `Λ ⊆ ℂ` we construct a holomorphic covering map `Ψ : ℍ → ℂ ∖ Λ`, onto, with
nonvanishing derivative (`PeriodPair.exists_uniformization`).

The input covering for the Koebe iteration comes from the modular function: an affine map `T`
sends `0` and `ω₂` onto the branch values `j(i)`, `j(ρ)` of `j`, so `T(ℂ ∖ Λ) ⊆ ℂ ∖ jBranch` and
`p₀ = T⁻¹ ∘ j ∘ C⁻¹ ∘ mob t` (`C` the Cayley map `ℍ → 𝔻`, `mob t` a disc automorphism moving `0`
to a point over `T(ω₂ / 2)`) is a holomorphic covering of `ℂ ∖ Λ` by an open subset of `𝔻`
containing `0`: its sections are the sections of `j` (`Uniformization.exists_section_jC`)
transported by `T`, `C` and `mob t`. The plane uniformisation theorem
`Uniformization.PlaneData.exists_covering` then gives `ψ₀ : 𝔻 → ℂ ∖ Λ`, and `Ψ = ψ₀ ∘ C`.
-/

open Complex Metric Set Filter Topology
open UpperHalfPlane hiding I I_re I_im

namespace Uniformization

/-! ### The lattice complement -/

namespace LatticeData

variable (L : PeriodPair)

/-- The branch values `j(i)`, `j(ρ)`. -/
noncomputable abbrev b₁ : ℂ := Heights.modularJ UpperHalfPlane.I
/-- The branch values `j(i)`, `j(ρ)`. -/
noncomputable abbrev b₂ : ℂ := Heights.modularJ UpperHalfPlane.ρ

/-- The slope of the affine map `T`. -/
noncomputable def slope : ℂ := by
  classical
  exact if b₂ = b₁ then 1 else (b₂ - b₁) / L.ω₂

/-- The affine map `T z = j(i) + c z`, sending `0 ↦ j(i)` and `ω₂ ↦ j(ρ)`. -/
noncomputable def aff (z : ℂ) : ℂ := b₁ + slope L * z

/-- The inverse of `aff`. -/
noncomputable def affInv (y : ℂ) : ℂ := (y - b₁) / slope L

theorem ω₂_ne_zero : L.ω₂ ≠ 0 := by
  intro h
  have := L.ω₂_div_two_notMem_lattice
  rw [h, zero_div] at this
  exact this (zero_mem _)

theorem slope_ne_zero : slope L ≠ 0 := by
  unfold slope
  split_ifs with h
  · exact one_ne_zero
  · exact div_ne_zero (sub_ne_zero.mpr h) (ω₂_ne_zero L)

theorem affInv_aff (z : ℂ) : affInv L (aff L z) = z := by
  simp [affInv, aff, mul_div_cancel_left₀ _ (slope_ne_zero L)]

theorem aff_affInv (y : ℂ) : aff L (affInv L y) = y := by
  simp [affInv, aff, mul_div_cancel₀ _ (slope_ne_zero L)]

theorem jBranch_subset : jBranch ⊆ aff L '' (L.lattice : Set ℂ) := by
  rintro y (rfl | rfl)
  · exact ⟨0, zero_mem _, by simp [aff]⟩
  · by_cases h : b₂ = b₁
    · exact ⟨0, zero_mem _, by simp [aff, h]⟩
    · refine ⟨L.ω₂, L.ω₂_mem_lattice, ?_⟩
      simp only [aff, slope, h, if_false]
      field_simp [ω₂_ne_zero L]
      ring

theorem aff_notMem_jBranch {z : ℂ} (hz : z ∉ L.lattice) : aff L z ∉ jBranch := by
  intro h
  obtain ⟨l, hl, hlz⟩ := jBranch_subset L h
  have := congrArg (affInv L) hlz
  rw [affInv_aff, affInv_aff] at this
  exact hz (this ▸ hl)

/-- The domain `Ω = ℂ ∖ Λ`. -/
def Ω : Set ℂ := (L.lattice : Set ℂ)ᶜ

theorem isOpen_Ω : IsOpen (Ω L) := L.isClosed_lattice.isOpen_compl

theorem countable_lattice : (L.lattice : Set ℂ).Countable := by
  have : (L.lattice : Set ℂ) = Set.range (fun p : ℤ × ℤ ↦ (p.1 : ℂ) * L.ω₁ + p.2 * L.ω₂) := by
    ext x
    simp only [SetLike.mem_coe, PeriodPair.mem_lattice, mem_range, Prod.exists]
  rw [this]
  exact countable_range _

theorem isPreconnected_Ω : IsPreconnected (Ω L) :=
  ((countable_lattice L).isConnected_compl_of_one_lt_rank
    (by rw [rank_real_complex]; norm_num)).isPreconnected

theorem half_mem_Ω : L.ω₂ / 2 ∈ Ω L := L.ω₂_div_two_notMem_lattice

/-- A point of `ℍ` over `T(ω₂ / 2)`. -/
noncomputable def τ₁ : ℍ := (Heights.modularJ_surjective (aff L (L.ω₂ / 2))).choose

theorem jC_τ₁ : jC (τ₁ L) = aff L (L.ω₂ / 2) := by
  rw [jC_coe]; exact (Heights.modularJ_surjective _).choose_spec

/-- The base point of the disc. -/
noncomputable def t : ℂ := cayley (τ₁ L)

theorem t_mem : t L ∈ ball (0 : ℂ) 1 := cayley_mem_ball (τ₁ L).im_pos

/-- The map `𝔻 → ℍ`, `w ↦ C⁻¹ (mob t w)`. -/
noncomputable def hmap (w : ℂ) : ℂ := cayleyInv (mob (t L) w)

/-- Its inverse `ℍ → 𝔻`. -/
noncomputable def hinv (z : ℂ) : ℂ := mob (-t L) (cayley z)

theorem im_hmap_pos {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) : 0 < (hmap L w).im :=
  im_cayleyInv_pos (mob_mem_ball (t_mem L) hw)

theorem hinv_mem {z : ℂ} (hz : 0 < z.im) : hinv L z ∈ ball (0 : ℂ) 1 :=
  mob_mem_ball (by simpa using t_mem L) (cayley_mem_ball hz)

theorem hinv_hmap {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) : hinv L (hmap L w) = w := by
  rw [hinv, hmap, cayley_cayleyInv (mob_mem_ball (t_mem L) hw), mob_neg_mob (t_mem L) hw]

theorem hmap_hinv {z : ℂ} (hz : 0 < z.im) : hmap L (hinv L z) = z := by
  rw [hinv, hmap, mob_mob_neg (t_mem L) (cayley_mem_ball hz), cayleyInv_cayley hz]

theorem continuousOn_hmap : ContinuousOn (hmap L) (ball 0 1) :=
  differentiableOn_cayleyInv.continuousOn.comp (continuousOn_mob (t_mem L))
    fun _ hw ↦ mob_mem_ball (t_mem L) hw

theorem differentiableOn_hmap : DifferentiableOn ℂ (hmap L) (ball 0 1) :=
  differentiableOn_cayleyInv.comp (differentiableOn_mob (t_mem L))
    fun _ hw ↦ mob_mem_ball (t_mem L) hw

theorem continuousOn_hinv : ContinuousOn (hinv L) {z | 0 < z.im} :=
  (continuousOn_mob (by simpa using t_mem L)).comp differentiableOn_cayley.continuousOn
    fun _ hz ↦ cayley_mem_ball hz

theorem hmap_zero : hmap L 0 = τ₁ L := by
  rw [hmap, mob_zero, t, cayleyInv_cayley (τ₁ L).im_pos]

/-- The starting covering `p₀ = T⁻¹ ∘ j ∘ hmap` on the disc, `0` outside. -/
noncomputable def p₀ (w : ℂ) : ℂ := by
  classical
  exact if w ∈ ball (0 : ℂ) 1 then affInv L (jC (hmap L w)) else 0

theorem p₀_of_mem {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) : p₀ L w = affInv L (jC (hmap L w)) := by
  simp [p₀, hw]

theorem mem_ball_of_p₀_mem {w : ℂ} (h : p₀ L w ∈ Ω L) : w ∈ ball (0 : ℂ) 1 := by
  by_contra hw
  simp only [p₀, hw, if_false] at h
  exact h (zero_mem _)

theorem continuousOn_p₀ : ContinuousOn (p₀ L) (ball 0 1) := by
  have : ContinuousOn (fun w ↦ affInv L (jC (hmap L w))) (ball 0 1) :=
    ((continuousOn_id.sub continuousOn_const).div_const _).comp
      (continuousOn_jC.comp (continuousOn_hmap L) fun _ hw ↦ im_hmap_pos L hw) (mapsTo_univ _ _)
  exact this.congr fun w hw ↦ p₀_of_mem L hw

theorem differentiableOn_p₀ : DifferentiableOn ℂ (p₀ L) (ball 0 1) := by
  have : DifferentiableOn ℂ (fun w ↦ (jC (hmap L w) - b₁) / slope L) (ball 0 1) :=
    ((differentiableOn_jC.comp (differentiableOn_hmap L) fun _ hw ↦ im_hmap_pos L hw).sub_const
      _).div_const _
  exact this.congr fun w hw ↦ p₀_of_mem L hw

theorem preimage_p₀_eq : p₀ L ⁻¹' Ω L = ball 0 1 ∩ p₀ L ⁻¹' Ω L := by
  ext w; exact ⟨fun h ↦ ⟨mem_ball_of_p₀_mem L h, h⟩, fun h ↦ h.2⟩

theorem isOpen_preimage_p₀ : IsOpen (p₀ L ⁻¹' Ω L) := by
  rw [preimage_p₀_eq]
  exact (continuousOn_p₀ L).isOpen_inter_preimage isOpen_ball (isOpen_Ω L)

theorem jC_hmap_of_p₀ {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) : jC (hmap L w) = aff L (p₀ L w) := by
  rw [p₀_of_mem L hw, aff_affInv]

theorem isCoveringMapOn_p₀ : IsCoveringMapOn (p₀ L) (Ω L) := by
  refine isCoveringMapOn_of_sections (isOpen_preimage_p₀ L)
    ((continuousOn_p₀ L).mono fun w hw ↦ mem_ball_of_p₀_mem L hw) ?_ ?_
  · -- local injectivity
    intro e he
    have heD := mem_ball_of_p₀_mem L he
    have hB : jC (hmap L e) ∉ jBranch := by rw [jC_hmap_of_p₀ L heD]; exact aff_notMem_jBranch L he
    obtain ⟨W, hW, hWinj⟩ := exists_nhds_injOn_jC hB
    refine ⟨ball 0 1 ∩ hmap L ⁻¹' W, inter_mem (isOpen_ball.mem_nhds heD)
      (((continuousOn_hmap L).continuousAt (isOpen_ball.mem_nhds heD)).preimage_mem_nhds hW), ?_⟩
    intro x hx y hy hxy
    rw [p₀_of_mem L hx.1, p₀_of_mem L hy.1] at hxy
    have h1 : jC (hmap L x) = jC (hmap L y) := by
      have := congrArg (aff L) hxy; rwa [aff_affInv, aff_affInv] at this
    have h2 := hWinj hx.2 hy.2 h1
    rw [← hinv_hmap L hx.1, ← hinv_hmap L hy.1, h2]
  · -- sections
    intro x hx
    obtain ⟨ε, hε, -, hsec⟩ := exists_section_jC (aff_notMem_jBranch L hx)
    obtain ⟨δ', hδ', hδ'Ω⟩ := Metric.isOpen_iff.mp (isOpen_Ω L) x hx
    have hc := norm_pos_iff.mpr (slope_ne_zero L)
    set δ := min δ' (ε / ‖slope L‖)
    have hδ : 0 < δ := lt_min hδ' (div_pos hε hc)
    have hVΩ : ball x δ ⊆ Ω L := (ball_subset_ball (min_le_left _ _)).trans hδ'Ω
    have hVaff : ∀ y ∈ ball x δ, aff L y ∈ ball (aff L x) ε := by
      intro y hy
      rw [mem_ball, dist_eq_norm, aff, aff, add_sub_add_left_eq_sub, ← mul_sub, norm_mul]
      have : ‖y - x‖ < ε / ‖slope L‖ := by
        rw [← dist_eq_norm]; exact hy.trans_le (min_le_right _ _)
      rwa [lt_div_iff₀' hc] at this
    refine ⟨ball x δ, isOpen_ball, mem_ball_self hδ, hVΩ, (convex_ball x δ).isPreconnected,
      fun e he ↦ ?_⟩
    have heD := mem_ball_of_p₀_mem L (hVΩ he)
    have hje : jC (hmap L e) ∈ ball (aff L x) ε := by
      rw [jC_hmap_of_p₀ L heD]; exact hVaff _ he
    obtain ⟨s, hsc, hsj, hsim, hse⟩ := hsec _ hje
    refine ⟨fun y ↦ hinv L (s (aff L y)), ?_, fun y hy ↦ ?_, ?_⟩
    · refine (continuousOn_hinv L).comp (hsc.comp (continuous_const.add
        (continuous_const.mul continuous_id)).continuousOn hVaff) fun y hy ↦ hsim _ (hVaff y hy)
    · have hmem := hinv_mem L (hsim _ (hVaff y hy))
      rw [p₀_of_mem L hmem, hmap_hinv L (hsim _ (hVaff y hy)), hsj _ (hVaff y hy), affInv_aff]
    · simp only
      rw [← jC_hmap_of_p₀ L heD, hse, hinv_hmap L heD]

theorem planeData : PlaneData (Ω L) (p₀ L ⁻¹' Ω L) (p₀ L) where
  good :=
    { isOpen := isOpen_preimage_p₀ L
      subset_ball := fun _ h ↦ mem_ball_of_p₀_mem L h
      zero_mem := by
        change p₀ L 0 ∈ Ω L
        rw [p₀_of_mem L (mem_ball_self one_pos), hmap_zero, jC_τ₁, affInv_aff]
        exact half_mem_Ω L }
  isOpen := isOpen_Ω L
  isPreconnected := isPreconnected_Ω L
  covering := isCoveringMapOn_p₀ L
  preimage_eq := rfl
  differentiableOn := (differentiableOn_p₀ L).mono fun _ h ↦ mem_ball_of_p₀_mem L h

end LatticeData

open LatticeData in
/-- **Uniformisation of `ℂ ∖ Λ`.** For a period lattice `Λ` there is a function `Ψ : ℂ → ℂ`,
holomorphic with nonvanishing derivative on the upper half-plane, whose restriction to `ℍ` is a
covering map onto `ℂ ∖ Λ`. -/
theorem PeriodPair.exists_uniformization (L : PeriodPair) :
    ∃ Ψ : ℂ → ℂ, IsCoveringMapOn (fun τ : ℍ ↦ Ψ τ) (L.lattice : Set ℂ)ᶜ ∧
      (∀ z : ℂ, 0 < z.im → Ψ z ∉ L.lattice) ∧
      DifferentiableOn ℂ Ψ {z | 0 < z.im} ∧ (∀ z : ℂ, 0 < z.im → deriv Ψ z ≠ 0) ∧
      ∀ w ∉ L.lattice, ∃ τ : ℍ, Ψ τ = w := by
  obtain ⟨ψ₀, hcov, hpre, hd, hderiv, hsurj⟩ := (planeData L).exists_covering (c₀ := 0)
    (fun h ↦ h (zero_mem _))
  set Ψ : ℂ → ℂ := fun z ↦ ψ₀ (cayley z)
  have hΨΩ : ∀ z : ℂ, 0 < z.im → Ψ z ∈ Ω L := fun z hz ↦ by
    change ψ₀ (cayley z) ∈ Ω L
    rw [← mem_preimage, hpre]; exact cayley_mem_ball hz
  refine ⟨Ψ, ?_, hΨΩ, ?_, ?_, ?_⟩
  · -- the covering property, transported along `ℍ ≃ₜ 𝔻`
    have hcov' := hcov.isCoveringMap_restrictPreimage
    let e : ℍ ≃ₜ ψ₀ ⁻¹' Ω L :=
      { toFun := fun τ ↦ ⟨cayley τ, by rw [hpre]; exact cayley_mem_ball τ.im_pos⟩
        invFun := fun w ↦ ⟨cayleyInv w, im_cayleyInv_pos (hpre ▸ w.2)⟩
        left_inv := fun τ ↦ UpperHalfPlane.ext (cayleyInv_cayley τ.im_pos)
        right_inv := fun w ↦ Subtype.ext (cayley_cayleyInv (hpre ▸ w.2))
        continuous_toFun := by
          refine Continuous.subtype_mk ?_ _
          exact differentiableOn_cayley.continuousOn.comp_continuous continuous_coe
            fun τ ↦ τ.im_pos
        continuous_invFun := by
          refine isOpenEmbedding_coe.isInducing.continuous_iff.mpr ?_
          change Continuous fun w : ψ₀ ⁻¹' Ω L ↦ cayleyInv w
          exact differentiableOn_cayleyInv.continuousOn.comp_continuous continuous_subtype_val
            fun w ↦ hpre ▸ w.2 }
    refine IsCoveringMapOn.of_isCoveringMap_subtype (isOpen_Ω L) (fun τ ↦ hΨΩ τ τ.im_pos) ?_
    convert hcov'.comp_homeomorph e using 1
    funext τ; rfl
  · exact hd.comp differentiableOn_cayley fun z hz ↦ cayley_mem_ball hz
  · intro z hz
    have hzD := cayley_mem_ball hz
    obtain ⟨φ, hφs, hφ⟩ := hcov.isLocalHomeomorphOn (cayley z) (by rw [hpre]; exact hzD)
    have hinj : InjOn Ψ ({z | 0 < z.im} ∩ cayley ⁻¹' φ.source) := by
      intro x hx y hy hxy
      have h1 : cayley x = cayley y := φ.injOn hx.2 hy.2 (by rw [← hφ]; exact hxy)
      rw [← cayleyInv_cayley hx.1, h1, cayleyInv_cayley hy.1]
    refine deriv_ne_zero_of_injOn ((hd.comp differentiableOn_cayley fun z hz ↦
      cayley_mem_ball hz).mono inter_subset_left) (inter_mem (isOpen_upper.mem_nhds hz)
      ((differentiableOn_cayley.continuousOn.continuousAt
        (isOpen_upper.mem_nhds hz)).preimage_mem_nhds (φ.open_source.mem_nhds hφs))) hinj
  · intro w hw
    obtain ⟨v, hv, hvw⟩ := hsurj hw
    refine ⟨⟨cayleyInv v, im_cayleyInv_pos hv⟩, ?_⟩
    change ψ₀ (cayley (cayleyInv v)) = w
    rw [cayley_cayleyInv hv, hvw]

end Uniformization
