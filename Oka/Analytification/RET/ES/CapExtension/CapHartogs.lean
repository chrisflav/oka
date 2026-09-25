/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.ES.CapExtension.CapSections

/-!
# Hartogs extension for sections of the cap

Keep the notation of `Oka/Analytification/RET/ES/CapExtension/CapSections.lean`, and let `Z` be
the zero set of a family of regular pairs on `G`. A section of the cap over `(U ∖ Z) × ℙ¹` extends
to a section over `U × ℙ¹` (`ComplexAnalytic.Cap.AnnulusDecomposition.exists_capPole_extend`): the
part over `N` extends by Hartogs extension for bounded sections across `(U ∩ Z) × {‖w‖ < ρ}`, whose
defining pairs pulled back to `ℂ^{m+1}` are regular (`RegularPairFamily.pullBase`), and the
functions at infinity extend by Hartogs extension on the Kummer covers.
-/

open CategoryTheory Opposite Topology Set Filter Metric

universe u

namespace ComplexAnalytic.Cap.AnnulusDecomposition

open AnalyticSpace BoundedSections Complex.ProjectiveLineBundle AlgebraicGeometry.LocallyRingedSpace
open KummerModel (splitEquiv)

noncomputable section

variable {m : ℕ} {G : Set (Cm.{u} m)} (R : RegularPairFamily G)

lemma isOpen_splitEquiv_preimage {Ω : Set (Cm.{u} m × ℂ)} (hΩ : IsOpen Ω) :
    IsOpen (splitEquiv m ⁻¹' Ω) :=
  hΩ.preimage (splitEquiv m).continuous

/-- Two functions continuous on an open `Ω ⊆ G × ℂ` which agree off `Z × ℂ` agree on `Ω`. -/
lemma eqOn_of_eqOn_off_zeroSet {Ω : Set (Cm.{u} m × ℂ)} (hΩ : IsOpen Ω)
    (hΩG : ∀ z ∈ Ω, z.1 ∈ G) {f g : Cm.{u} m × ℂ → ℂ} (hf : ContinuousOn f Ω)
    (hg : ContinuousOn g Ω) (h : ∀ z ∈ Ω, z.1 ∉ R.zeroSet → f z = g z) : EqOn f g Ω := by
  set S := splitEquiv m ⁻¹' Ω
  have hSG : ∀ x ∈ S, baseOf x ∈ G := fun x hx ↦ hΩG _ hx
  have hc : ∀ {φ : Cm.{u} m × ℂ → ℂ}, ContinuousOn φ Ω → ContinuousOn (φ ∘ splitEquiv m) S :=
    fun hφ ↦ hφ.comp (splitEquiv m).continuous.continuousOn fun _ hx ↦ hx
  have := (R.pullBase hSG).eqOn_of_eqOn_diff (isOpen_splitEquiv_preimage hΩ) subset_rfl
    (hc hf) (hc hg) fun x hx ↦ by
      rw [RegularPairFamily.zeroSet_pullBase] at hx
      exact h _ hx.1 hx.2
  intro z hz
  have h' := this (show (splitEquiv m).symm z ∈ S by simpa [S] using hz)
  simpa using h'

/-- **Hartogs extension on `G × ℂ`**: a function holomorphic on `Ω` off `Z × ℂ` extends to a
holomorphic function on `Ω`. -/
lemma exists_extension_off_zeroSet {Ω : Set (Cm.{u} m × ℂ)} (hΩ : IsOpen Ω)
    (hΩG : ∀ z ∈ Ω, z.1 ∈ G) {f : Cm.{u} m × ℂ → ℂ}
    (hf : DifferentiableOn ℂ f {z | z ∈ Ω ∧ z.1 ∉ R.zeroSet}) :
    ∃ f' : Cm.{u} m × ℂ → ℂ, DifferentiableOn ℂ f' Ω ∧
      ∀ z ∈ Ω, z.1 ∉ R.zeroSet → f' z = f z := by
  set S := splitEquiv m ⁻¹' Ω
  have hSG : ∀ x ∈ S, baseOf x ∈ G := fun x hx ↦ hΩG _ hx
  obtain ⟨F', hF', hF'f⟩ := (R.pullBase hSG).exists_differentiableOn_eqOn
    (isOpen_splitEquiv_preimage hΩ) subset_rfl (f := f ∘ splitEquiv m)
    (hf.comp Cap.differentiable_splitEquiv.differentiableOn fun x hx ↦ by
      rw [RegularPairFamily.zeroSet_pullBase] at hx
      exact ⟨hx.1, hx.2⟩)
  refine ⟨F' ∘ (splitEquiv m).symm, hF'.comp Cap.differentiable_splitEquiv_symm.differentiableOn
    fun z hz ↦ by simpa [S] using hz, fun z hz hzZ ↦ ?_⟩
  have := hF'f (x := (splitEquiv m).symm z) ⟨by simpa [S] using hz, by
    rw [RegularPairFamily.zeroSet_pullBase]
    simpa [baseOf] using hzZ⟩
  simpa using this

variable {N N₀ : (AnalyticSpace.complexAffineSpace.{u} (m + 1)).Opens} (h₀ : N₀ ≤ N)
  {W : FiniteEtaleOver (space N₀)} [T2Space W.left] {F : WeierstrassForm N N₀}
  (D : AnnulusDecomposition W F.G F.ρ)

omit [T2Space W.left] in
/-- The part of the Kummer cover `i` over the overlap on which the relation of the cap is
imposed, an open set. -/
lemma isOpen_pieceSet_inter {U : Set (Cm.{u} m)} (hU : IsOpen U) {V : (space N).Opens}
    (i : D.ι) : IsOpen (D.pieceSet (preim h₀ W V) i ∩
      invCoord ⁻¹' (Kummer.powMap (D.deg i) ⁻¹' (U ×ˢ ball 0 F.ρ))) := by
  have hρ0 : 0 < F.ρ := F.pos_ρ
  have hpo := D.isOpen_pieceSet F.isOpen_G (preim h₀ W V) i
  have hne : ∀ y ∈ D.pieceSet (preim h₀ W V) i, y.2 ≠ 0 := by
    intro y hy h
    have := hy.1.2.1
    rw [h, norm_zero, zero_pow (D.deg i).ne_zero] at this
    exact (inv_pos.2 hρ0).not_gt this
  have hinvc : ContinuousOn invCoord (D.pieceSet (preim h₀ W V) i) :=
    fun y hy ↦ (continuousAt_fst.prodMk (continuousAt_snd.inv₀ (hne y hy))).continuousWithinAt
  exact hinvc.isOpen_inter_preimage hpo
    ((hU.prod isOpen_ball).preimage (Kummer.continuous_powMap _))

omit [T2Space W.left] in
lemma continuousOn_invCoord_pieceSet {V : (space N).Opens} (i : D.ι) :
    ContinuousOn invCoord (D.pieceSet (preim h₀ W V) i) := by
  have hρ0 : 0 < F.ρ := F.pos_ρ
  intro y hy
  have hne : y.2 ≠ 0 := by
    intro h
    have := hy.1.2.1
    rw [h, norm_zero, zero_pow (D.deg i).ne_zero] at this
    exact (inv_pos.2 hρ0).not_gt this
  exact (continuousAt_fst.prodMk (continuousAt_snd.inv₀ hne)).continuousWithinAt

/-- **Hartogs extension for sections of the cap** across `Z × ℙ¹`. -/
theorem exists_capPole_extend {n : ℕ} {U : Set (Cm.{u} m)} {hU : IsOpen U} (hUG : U ⊆ F.G)
    (R : RegularPairFamily F.G) (hU' : IsOpen (U \ R.zeroSet))
    {t : boundedSubring h₀ W (tubeN N (U \ R.zeroSet) hU') × (D.ι → Cm.{u} m × ℂ → ℂ)}
    (ht : t ∈ D.capPole h₀ n (tubeN N (U \ R.zeroSet) hU') ((U \ R.zeroSet) ×ˢ ball 0 F.ρ)) :
    ∃ t' ∈ D.capPole h₀ n (tubeN N U hU) (U ×ˢ ball 0 F.ρ),
      (∀ y ∈ preim h₀ W (tubeN N (U \ R.zeroSet) hU'), evalFun t'.1.1 y = evalFun t.1.1 y) ∧
      ∀ i z, z.1 ∈ U \ R.zeroSet → ‖z.2 ^ (D.deg i : ℕ)‖ < F.ρ → t'.2 i z = t.2 i z := by
  have hD := F.hasThinComplement
  have hle : tubeN N (U \ R.zeroSet) hU' ≤ tubeN N U hU := tubeN_mono sdiff_subset
  have hPG : ∀ x ∈ (img (tubeN N U hU) : Set (Cn.{u} (m + 1))), baseOf x ∈ F.G :=
    fun x hx ↦ hUG (mem_img_iff.1 hx).2
  obtain ⟨a, ha⟩ := (bijective_boundedModule_map (R.pullBase hPG) h₀ W le_rfl hle
    (fun x hx ↦ by
      rw [RegularPairFamily.zeroSet_pullBase] at hx
      obtain ⟨hxN, hxU⟩ := mem_img_iff.1 hx.1
      exact mem_img_iff.2 ⟨hxN, hxU, hx.2⟩) hD).2 (mkSec h₀ W t.1.1 t.1.2)
  have hav : ∀ y ∈ preim h₀ W (tubeN N (U \ R.zeroSet) hU'),
      evalFun (secVal h₀ W a) y = evalFun t.1.1 y := by
    intro y hy
    have := congrArg (fun c ↦ evalFun (secVal h₀ W c) y) ha
    simp only [secVal_map, evalFun_map W _ _ hy, secVal_mkSec] at this
    exact this
  -- the functions at infinity
  have hinf : ∀ i, ∃ f' : Cm.{u} m × ℂ → ℂ,
      DifferentiableOn ℂ f' (Kummer.powMap (D.deg i) ⁻¹' (U ×ˢ ball 0 F.ρ)) ∧
      ∀ z ∈ Kummer.powMap (D.deg i) ⁻¹' (U ×ˢ ball 0 F.ρ), z.1 ∉ R.zeroSet → f' z = t.2 i z := by
    intro i
    exact exists_extension_off_zeroSet R (((hU.prod isOpen_ball)).preimage
      (Kummer.continuous_powMap _)) (fun z hz ↦ hUG hz.1)
      ((ht.1 i).mono fun z hz ↦ ⟨⟨hz.1.1, hz.2⟩, hz.1.2⟩)
  choose f' hf' hf'eq using hinf
  refine ⟨(⟨secVal h₀ W a, secVal_mem h₀ W a⟩, f'), ⟨hf', fun i z hz hz' ↦ ?_⟩, hav,
    fun i z hz hzρ ↦ hf'eq i z ⟨hz.1, mem_ball_zero_iff.2 hzρ⟩ hz.2⟩
  have hΩ := D.isOpen_pieceSet_inter h₀ hU (V := tubeN N U hU) i
  refine eqOn_of_eqOn_off_zeroSet R hΩ (fun y hy ↦ hUG hy.2.1)
    ((D.differentiableOn_kummerVal F.isOpen_G (secVal h₀ W a) i).continuousOn.mono
      inter_subset_left)
    ((continuous_snd.pow _).continuousOn.mul ((hf' i).continuousOn.comp
      ((D.continuousOn_invCoord_pieceSet h₀ i).mono inter_subset_left) fun y hy ↦ hy.2))
    (fun y hy hyZ ↦ ?_) ⟨hz, hz'⟩
  obtain ⟨⟨hyb, hyO⟩, hy'⟩ := hy
  have hyO' : D.toFun ⟨i, ⟨y, hyb⟩⟩ ∈ preim h₀ W (tubeN N (U \ R.zeroSet) hU') := by
    obtain ⟨hN, -⟩ := mem_img_iff.1 ((mem_preim_iff h₀ W).1 hyO)
    refine (mem_preim_iff h₀ W).2 (mem_img_iff.2 ⟨hN, ?_⟩)
    change baseOf (pt W (D.toFun ⟨i, ⟨y, hyb⟩⟩)) ∈ U \ R.zeroSet
    rw [D.pt_toFun]
    simpa [baseOf] using (⟨hy'.1, hyZ⟩ : y.1 ∈ U \ R.zeroSet)
  have hrel := ht.2 i y ⟨hyb, hyO'⟩ ⟨⟨hy'.1, hyZ⟩, hy'.2⟩
  change D.kummerVal (secVal h₀ W a) i y = y.2 ^ (n * D.deg i) * f' i (invCoord y)
  rw [D.kummerVal_of_mem _ _ hyb, hav _ hyO', ← D.kummerVal_of_mem _ _ hyb, hrel,
    hf'eq i (invCoord y) hy' hyZ]

end

end ComplexAnalytic.Cap.AnnulusDecomposition
