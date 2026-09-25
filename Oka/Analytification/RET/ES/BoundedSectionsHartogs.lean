/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.ES.BoundedSectionsTrace
import Oka.Analytic.HartogsRegularFamily

/-!
# Hartogs extension for bounded sections

Keep the notation of `Oka/Analytification/RET/ES/BoundedSectionsTrace.lean`. Let `U ⊆ N` be open
and `P` a finite family of regular pairs on `U` (`RegularPairFamily`) with union of common zero sets
`Z`. For opens `V' ≤ V ≤ U` with `V \ Z ⊆ V'`, restriction along `V' ≤ V` is bijective on
sections of `𝒪_N` (`ComplexAnalytic.BoundedSections.bijective_map_of_regularPairFamily`) and on
sections of `𝒜` (`ComplexAnalytic.BoundedSections.bijective_boundedModule_map`).

For `𝒜`, a section over `V'` is first extended as a section of `𝒪_W` over `p⁻¹(V ∩ N°)`, sheet by
sheet, by Hartogs extension in `ℂⁿ` (`ComplexAnalytic.BoundedSections.exists_map_eq`). The
extension is bounded near `V ∖ N°`: the coefficients of its characteristic polynomial extend
across `Z` as sections of `𝒪_N`, and by density it remains a root of the extended polynomial, so
it is bounded by the usual root bound
(`ComplexAnalytic.BoundedSections.mem_boundedSubring_of_map_mem`).
-/

open CategoryTheory Opposite AlgebraicGeometry Topology TopologicalSpace Filter Polynomial

universe u

namespace ComplexAnalytic.BoundedSections

open AnalyticSpace

noncomputable section

variable {n : ℕ} {N N₀ : (AnalyticSpace.complexAffineSpace.{u} n).Opens}
  {U : (space N).Opens} (P : RegularPairFamily (img U : Set (Cn.{u} n)))

/-! ### Hartogs extension for `𝒪_N` -/

/-- **Hartogs extension for `𝒪_N`**: if `V ≤ U` and `V' ≤ V` contains `V` off the zero set of a
family of regular pairs on `U`, restriction `𝒪_N(V) → 𝒪_N(V')` is bijective. -/
theorem bijective_map_of_regularPairFamily {V V' : (space N).Opens} (hVU : V ≤ U)
    (hV'V : V' ≤ V) (hV' : (img V : Set (Cn.{u} n)) \ P.zeroSet ⊆ img V') :
    Function.Bijective ((space N).presheaf.map (homOfLE hV'V).op) := by
  have hVU' : (img V : Set (Cn.{u} n)) ⊆ img U := img_mono hVU
  have hext : ∀ {r r' : (space N).presheaf.obj (op V)},
      Set.EqOn (holFun r) (holFun r') (img V) → r = r' := fun h ↦
    OkaRing.ext (funext fun x ↦ (OkaRing.toGlobalFun_apply (U := img V) _ x.2).symm.trans
      ((h x.2).trans (OkaRing.toGlobalFun_apply (U := img V) _ x.2)))
  refine ⟨fun r r' hrr' ↦ hext ?_, fun r' ↦ ?_⟩
  · refine P.eqOn_of_eqOn_diff (img V).isOpen hVU' (differentiableOn_holFun r).continuousOn
      (differentiableOn_holFun r').continuousOn fun x hx ↦ ?_
    have hx' := hV' hx
    rw [← holFun_map hV'V r hx', ← holFun_map hV'V r' hx']
    change holFun ((space N).presheaf.map (homOfLE hV'V).op r) x =
      holFun ((space N).presheaf.map (homOfLE hV'V).op r') x
    rw [hrr']
  · obtain ⟨F, hF, hFr⟩ := P.exists_differentiableOn_eqOn (img V).isOpen hVU'
      ((differentiableOn_holFun r').mono hV')
    refine ⟨OkaRing.ofDifferentiableOn F hF, ?_⟩
    refine OkaRing.ext (funext fun x ↦ ?_)
    refine (OkaRing.toGlobalFun_apply (U := img V') _ x.2).symm.trans ?_
    refine Eq.trans ?_ (OkaRing.toGlobalFun_apply (U := img V') r' x.2)
    change holFun ((space N).presheaf.map (homOfLE hV'V).op _) x.1 = holFun r' x.1
    rw [holFun_map hV'V _ x.2]
    refine P.eqOn_of_eqOn_diff (img V').isOpen ((img_mono hV'V).trans hVU')
      ((differentiableOn_holFun _).continuousOn.mono (img_mono hV'V))
      (differentiableOn_holFun r').continuousOn (fun y hy ↦ ?_) x.2
    rw [holFun, OkaRing.toGlobalFun_apply _ (img_mono hV'V hy.1)]
    exact hFr ⟨img_mono hV'V hy.1, hy.2⟩

/-! ### Hartogs extension for `𝒪_W` -/

variable (h₀ : N₀ ≤ N) (W : FiniteEtaleOver (space N₀))

/-- The image in `ℂⁿ` of a sheet cut down to `p⁻¹(V ∩ N°)`, as an open subset of `img V`. -/
lemma isOpen_image_pt (O : W.left.Opens) : IsOpen (pt W '' (O : Set W.left)) :=
  isOpenMap_pt W _ O.isOpen

lemma image_pt_subset {V : (space N).Opens} (O : W.left.Opens) :
    pt W '' ((O ⊓ preim h₀ W V : W.left.Opens) : Set W.left) ⊆ img V := by
  rintro _ ⟨w, hw, rfl⟩
  exact (mem_preim_iff h₀ W).1 hw.2

variable {V V' : (space N).Opens} (hVU : V ≤ U) (hV'V : V' ≤ V)
  (hV' : (img V : Set (Cn.{u} n)) \ P.zeroSet ⊆ img V')
include hVU hV'V hV'

/-- A section of `𝒪_W` over `p⁻¹(V ∩ N°)` vanishing over `V'` vanishes. -/
theorem eq_zero_of_map_eq_zero {a : W.left.presheaf.obj (op (preim h₀ W V))}
    (ha : W.left.presheaf.map (homOfLE (preim_mono h₀ W hV'V)).op a = 0) : a = 0 := by
  refine eq_of_forall_eval_eq (isLocallyOpenInAffine_left W) fun w hw ↦ ?_
  rw [map_zero]
  obtain ⟨O, hwO, -, hsheet⟩ := exists_sheet W w
  obtain ⟨F, hFd, hF⟩ := hsheet (O' := O ⊓ preim h₀ W V) inf_le_left
    (W.left.presheaf.map (homOfLE inf_le_right).op a)
  set G : Set (Cn.{u} n) := pt W '' ((O ⊓ preim h₀ W V : W.left.Opens) : Set W.left)
  have hGU : G ⊆ img U := (image_pt_subset h₀ W O).trans (img_mono hVU)
  have hFc : ContinuousOn F G := by
    rintro _ ⟨w', hw', rfl⟩
    exact (hFd w' hw').continuousAt.continuousWithinAt
  have h0 := P.eqOn_of_eqOn_diff (isOpen_image_pt W _) hGU hFc (continuousOn_const (c := 0))
    (fun x hx ↦ ?_) ⟨w, ⟨hwO, hw⟩, rfl⟩
  · have := hF w ⟨hwO, hw⟩
    rw [eval_presheaf_map] at this
    exact this.trans h0
  · obtain ⟨⟨w', hw', rfl⟩, hxZ⟩ := hx
    have hw'V' : w' ∈ preim h₀ W V' :=
      (mem_preim_iff h₀ W).2 (hV' ⟨(mem_preim_iff h₀ W).1 hw'.2, hxZ⟩)
    rw [← hF w' hw', eval_presheaf_map]
    have := congrArg (W.left.eval w' hw'V') ha
    rwa [eval_presheaf_map, map_zero] at this

/-- Near every point of `W`, a section over `p⁻¹(V' ∩ N°)` is a holomorphic function on the image
of a sheet over `V`. -/
lemma exists_sheet_extension (b : W.left.presheaf.obj (op (preim h₀ W V'))) (w : W.left) :
    ∃ O : W.left.Opens, w ∈ O ∧ ∃ F : Cn.{u} n → ℂ,
      DifferentiableOn ℂ F (pt W '' ((O ⊓ preim h₀ W V : W.left.Opens) : Set W.left)) ∧
      ∀ w' ∈ O ⊓ preim h₀ W V', evalFun b w' = F (pt W w') := by
  obtain ⟨O, hwO, -, hsheet⟩ := exists_sheet W w
  obtain ⟨F, hFd, hF⟩ := hsheet (O' := O ⊓ preim h₀ W V') inf_le_left
    (W.left.presheaf.map (homOfLE inf_le_right).op b)
  have hF' : ∀ w' (hw' : w' ∈ O ⊓ preim h₀ W V'), evalFun b w' = F (pt W w') := fun w' hw' ↦ by
    rw [evalFun_of_mem b hw'.2, ← hF w' hw', eval_presheaf_map]
  set G := pt W '' ((O ⊓ preim h₀ W V : W.left.Opens) : Set W.left)
  have hGU : G ⊆ img U := (image_pt_subset h₀ W O).trans (img_mono hVU)
  have hG'Z : ∀ x ∈ G \ P.zeroSet, ∃ w' ∈ O ⊓ preim h₀ W V', pt W w' = x := by
    rintro _ ⟨⟨w', hw', rfl⟩, hxZ⟩
    exact ⟨w', ⟨hw'.1, (mem_preim_iff h₀ W).2 (hV' ⟨(mem_preim_iff h₀ W).1 hw'.2, hxZ⟩)⟩, rfl⟩
  obtain ⟨F', hF'd, hF'F⟩ := P.exists_differentiableOn_eqOn (isOpen_image_pt W _) hGU
    (f := F) fun x hx ↦ by
      obtain ⟨w', hw', rfl⟩ := hG'Z x hx
      exact (hFd w' hw').differentiableWithinAt
  refine ⟨O, hwO, F', hF'd, fun w' hw' ↦ (hF' w' hw').trans ?_⟩
  -- `F'` and `F` agree on the image of `O ⊓ p⁻¹(V')`
  set G' := pt W '' ((O ⊓ preim h₀ W V' : W.left.Opens) : Set W.left)
  have hG'G : G' ⊆ G := Set.image_mono fun w'' hw'' ↦ ⟨hw''.1, preim_mono h₀ W hV'V hw''.2⟩
  refine (P.eqOn_of_eqOn_diff (isOpen_image_pt W _) (hG'G.trans hGU)
    (fun x hx ↦ ?_) (hF'd.continuousOn.mono hG'G) (fun x hx ↦ ?_) ⟨w', hw', rfl⟩)
  · obtain ⟨w'', hw'', rfl⟩ := hx
    exact (hFd w'' hw'').continuousAt.continuousWithinAt
  · exact (hF'F ⟨hG'G hx.1, hx.2⟩).symm

omit hV'V in
/-- Two holomorphic functions on images of sheets which agree with a section over `V'` agree on
the images of the common points over `V`. -/
lemma eq_of_sheet_extension (b : W.left.presheaf.obj (op (preim h₀ W V'))) {O₁ O₂ : W.left.Opens}
    {F₁ F₂ : Cn.{u} n → ℂ}
    (hF₁ : DifferentiableOn ℂ F₁ (pt W '' ((O₁ ⊓ preim h₀ W V : W.left.Opens) : Set W.left)))
    (hF₂ : DifferentiableOn ℂ F₂ (pt W '' ((O₂ ⊓ preim h₀ W V : W.left.Opens) : Set W.left)))
    (hb₁ : ∀ w' ∈ O₁ ⊓ preim h₀ W V', evalFun b w' = F₁ (pt W w'))
    (hb₂ : ∀ w' ∈ O₂ ⊓ preim h₀ W V', evalFun b w' = F₂ (pt W w')) {w : W.left}
    (hw : w ∈ O₁ ⊓ O₂ ⊓ preim h₀ W V) : F₁ (pt W w) = F₂ (pt W w) := by
  set G := pt W '' ((O₁ ⊓ O₂ ⊓ preim h₀ W V : W.left.Opens) : Set W.left)
  have hG₁ : G ⊆ pt W '' ((O₁ ⊓ preim h₀ W V : W.left.Opens) : Set W.left) :=
    Set.image_mono fun w' hw' ↦ ⟨hw'.1.1, hw'.2⟩
  have hG₂ : G ⊆ pt W '' ((O₂ ⊓ preim h₀ W V : W.left.Opens) : Set W.left) :=
    Set.image_mono fun w' hw' ↦ ⟨hw'.1.2, hw'.2⟩
  have hGU : G ⊆ img U := hG₁.trans ((image_pt_subset h₀ W O₁).trans (img_mono hVU))
  refine P.eqOn_of_eqOn_diff (isOpen_image_pt W _) hGU (hF₁.continuousOn.mono hG₁)
    (hF₂.continuousOn.mono hG₂) (fun x hx ↦ ?_) ⟨w, hw, rfl⟩
  obtain ⟨⟨w', hw', rfl⟩, hxZ⟩ := hx
  have hw'V' : w' ∈ preim h₀ W V' :=
    (mem_preim_iff h₀ W).2 (hV' ⟨(mem_preim_iff h₀ W).1 hw'.2, hxZ⟩)
  exact (hb₁ w' ⟨hw'.1.1, hw'V'⟩).symm.trans (hb₂ w' ⟨hw'.1.2, hw'V'⟩)

/-- **Hartogs extension for `𝒪_W`**: every section of `𝒪_W` over `p⁻¹(V' ∩ N°)` extends to
`p⁻¹(V ∩ N°)`. -/
theorem exists_map_eq (b : W.left.presheaf.obj (op (preim h₀ W V'))) :
    ∃ a : W.left.presheaf.obj (op (preim h₀ W V)),
      W.left.presheaf.map (homOfLE (preim_mono h₀ W hV'V)).op a = b := by
  have hW := isLocallyOpenInAffine_left W
  choose O hwO F hFd hFb using exists_sheet_extension P h₀ W hVU hV'V hV' b
  have hcons : ∀ w w' (hw' : w' ∈ O w ⊓ preim h₀ W V), F w (pt W w') = F w' (pt W w') :=
    fun w w' hw' ↦ eq_of_sheet_extension P h₀ W hVU hV' b (hFd w) (hFd w') (hFb w) (hFb w')
      ⟨⟨hw'.1, hwO w'⟩, hw'.2⟩
  obtain ⟨a, ha⟩ := exists_eval_eq_of_local hW (O := preim h₀ W V) (fun w ↦ F w (pt W w))
    fun w hw ↦ by
      obtain ⟨σ, hσ⟩ := exists_eval_eq_of_differentiableAt W (O := O w ⊓ preim h₀ W V) (F w)
        fun w' hw' ↦ (hFd w).differentiableAt
          ((isOpen_image_pt W _).mem_nhds ⟨w', hw', rfl⟩)
      exact ⟨O w ⊓ preim h₀ W V, ⟨hwO w, hw⟩, inf_le_right, σ, fun w' hw' ↦
        (hσ w' hw').trans (hcons w w' hw')⟩
  refine ⟨a, eq_of_forall_eval_eq hW fun w hw ↦ ?_⟩
  rw [eval_presheaf_map, ha, ← evalFun_of_mem b hw]
  exact (hFb w w ⟨hwO w, hw⟩).symm

/-- **Boundedness extends across the zero set**: a section of `𝒪_W` over `p⁻¹(V ∩ N°)` whose
restriction to `V'` lies in `𝒜(V')` lies in `𝒜(V)`. The coefficients of its characteristic
polynomial extend across the zero set, and the section remains a root. -/
theorem mem_boundedSubring_of_map_mem [T2Space W.left] (hD : HasThinComplement N N₀)
    {a : W.left.presheaf.obj (op (preim h₀ W V))}
    (ha : W.left.presheaf.map (homOfLE (preim_mono h₀ W hV'V)).op a ∈ boundedSubring h₀ W V') :
    a ∈ boundedSubring h₀ W V := by
  classical
  set a' := W.left.presheaf.map (homOfLE (preim_mono h₀ W hV'V)).op a
  have ha' : ∀ w ∈ preim h₀ W V', evalFun a' w = evalFun a w := fun w hw ↦
    evalFun_map W _ a hw
  intro y hy _
  set x₀ : Cn.{u} n := y.1
  have hx₀ : x₀ ∈ img V := mem_img_iff.2 ⟨y.2, hy⟩
  -- the coefficients of the characteristic polynomial, extended to `V`
  choose c hc using exists_coeff_charPolyFun hD ha
  have hc' : ∀ k, ∃ c' : (space N).presheaf.obj (op V), ∀ x ∈ img V', x ∈ N₀ →
      holFun c' x = (charPolyFun W (evalFun a) x).coeff k := fun k ↦ by
    obtain ⟨c', hc'⟩ := (bijective_map_of_regularPairFamily P hVU hV'V hV').2 (c k)
    refine ⟨c', fun x hx hxN ↦ ?_⟩
    rw [← holFun_map hV'V c' hx, hc', hc k x hx hxN]
    congr 1
    refine charPolyFun_congr W fun w hw ↦ ha' w ((mem_preim_iff h₀ W).2 (hw ▸ hx))
  choose c' hc' using hc'
  -- a ball around `x₀` in `img V`, over which the number of sheets is constant
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (img V).isOpen x₀ hx₀
  set B := Metric.ball x₀ ε
  have hBU : B ⊆ img U := fun x hx ↦ img_mono hVU (hball hx)
  by_cases hne : ∃ x₁ ∈ B, x₁ ∈ N₀
  swap
  · refine ⟨Subtype.val ⁻¹' B, continuous_subtype_val.continuousAt.preimage_mem_nhds
      (Metric.ball_mem_nhds x₀ hε), 0, fun w hw hwB ↦ ?_⟩
    rw [Set.mem_preimage, coe_proj_base] at hwB
    exact (hne ⟨_, hwB, pt_mem W w⟩).elim
  obtain ⟨x₁, hx₁B, hx₁N⟩ := hne
  set d := (fiberFinset W x₁).card
  have hd : ∀ x ∈ B, x ∈ N₀ → (fiberFinset W x).card = d := fun x hx hxN ↦
    card_fiberFinset_eq W hD Metric.isOpen_ball (convex_ball x₀ ε).isPreconnected
      (fun z hz ↦ img_le V z (hball hz)) hx hxN hx₁B hx₁N
  -- `a` is a root of the extended characteristic polynomial over `B`
  have hroot : ∀ w (hw : w ∈ preim h₀ W V), pt W w ∈ B →
      evalFun a w ^ d + ∑ k ∈ Finset.range d, holFun (c' k) (pt W w) * evalFun a w ^ k = 0 := by
    intro w hw hwB
    obtain ⟨O, hwO, -, hsheet⟩ := exists_sheet W w
    obtain ⟨F, hFd, hF⟩ := hsheet (O' := O ⊓ preim h₀ W V) inf_le_left
      (W.left.presheaf.map (homOfLE inf_le_right).op a)
    have hF' : ∀ w' (hw' : w' ∈ O ⊓ preim h₀ W V), evalFun a w' = F (pt W w') := fun w' hw' ↦ by
      rw [evalFun_of_mem a hw'.2, ← hF w' hw', eval_presheaf_map]
    set G := pt W '' ((O ⊓ preim h₀ W V : W.left.Opens) : Set W.left) ∩ B
    have hGU : G ⊆ img U := fun x hx ↦ hBU hx.2
    have hFc : ContinuousOn F G := by
      rintro _ ⟨⟨w', hw', rfl⟩, -⟩
      exact (hFd w' hw').continuousAt.continuousWithinAt
    have hcc : ∀ k, ContinuousOn (holFun (c' k)) G := fun k ↦
      (differentiableOn_holFun (c' k)).continuousOn.mono fun x hx ↦ hball hx.2
    have h0 := P.eqOn_of_eqOn_diff ((isOpen_image_pt W _).inter Metric.isOpen_ball) hGU
      (F₁ := fun x ↦ F x ^ d + ∑ k ∈ Finset.range d, holFun (c' k) x * F x ^ k)
      (F₂ := fun _ ↦ 0) ((hFc.pow d).add (continuousOn_finsetSum _ fun k _ ↦
        (hcc k).mul (hFc.pow k))) continuousOn_const (fun x hx ↦ ?_) ⟨⟨w, ⟨hwO, hw⟩, rfl⟩, hwB⟩
    · simpa only [← hF' w ⟨hwO, hw⟩] using h0
    · obtain ⟨⟨⟨w', hw', rfl⟩, hw'B⟩, hxZ⟩ := hx
      have hxV' : pt W w' ∈ img V' := hV' ⟨(mem_preim_iff h₀ W).1 hw'.2, hxZ⟩
      have := eval_charPolyFun W (evalFun a) (rfl : pt W w' = pt W w')
      rw [eval_charPolyFun_eq W _ (hd _ hw'B (pt_mem W w'))] at this
      simp only
      rw [← hF' w' hw', ← this]
      congr 1
      exact Finset.sum_congr rfl fun k _ ↦ by rw [hc' k _ hxV' (pt_mem W w')]
  -- the root bound
  have hev : ∀ᶠ z in 𝓝 x₀, ∀ k ∈ Finset.range d,
      ‖holFun (c' k) z‖ ≤ ‖holFun (c' k) x₀‖ + 1 := by
    refine (Filter.eventually_all_finset _).2 fun k _ ↦ ?_
    have hcont := ((differentiableOn_holFun (c' k)).continuousOn.continuousAt
      ((img V).isOpen.mem_nhds hx₀)).norm
    filter_upwards [hcont.eventually (gt_mem_nhds (lt_add_one _))] with z hz using hz.le
  set A := ∑ k ∈ Finset.range d, (‖holFun (c' k) x₀‖ + 1)
  refine ⟨Subtype.val ⁻¹' (B ∩ {z | ∀ k ∈ Finset.range d,
      ‖holFun (c' k) z‖ ≤ ‖holFun (c' k) x₀‖ + 1}),
    continuous_subtype_val.continuousAt.preimage_mem_nhds
      (inter_mem (Metric.ball_mem_nhds x₀ hε) hev), max 1 (d * A), fun w hw hwM ↦ ?_⟩
  rw [Set.mem_preimage, coe_proj_base] at hwM
  rw [← evalFun_of_mem a hw]
  refine Kummer.norm_le_of_pow_add_sum_eq_zero (a := fun k ↦ holFun (c' k) (pt W w))
    (fun k hk ↦ (hwM.2 k (Finset.mem_range.2 hk)).trans (Finset.single_le_sum
      (f := fun k ↦ ‖holFun (c' k) x₀‖ + 1) (fun _ _ ↦ by positivity)
      (Finset.mem_range.2 hk))) (hroot w hw hwM.1)

/-- **Hartogs extension for `𝒜`**: if `V ≤ U` and `V' ≤ V` contains `V` off the zero set of a
family of regular pairs on `U`, restriction `𝒜(V) → 𝒜(V')` is bijective. -/
theorem bijective_boundedModule_map [T2Space W.left] (hD : HasThinComplement N N₀) :
    Function.Bijective (LocallyRingedSpace.sectRes (boundedModule h₀ W) hV'V) := by
  refine ⟨fun s t hst ↦ secVal_injective h₀ W ?_, fun t ↦ ?_⟩
  · have hst' := congrArg (secVal h₀ W) hst
    rw [secVal_map, secVal_map] at hst'
    have h0 : W.left.presheaf.map (homOfLE (preim_mono h₀ W hV'V)).op
        (secVal h₀ W s - secVal h₀ W t) = 0 := by
      rw [map_sub, hst', sub_self]
    exact sub_eq_zero.1 (eq_zero_of_map_eq_zero P h₀ W hVU hV'V hV' h0)
  · obtain ⟨a, ha⟩ := exists_map_eq P h₀ W hVU hV'V hV' (secVal h₀ W t)
    have hmem : a ∈ boundedSubring h₀ W V :=
      mem_boundedSubring_of_map_mem P h₀ W hVU hV'V hV' hD (ha ▸ secVal_mem h₀ W t)
    exact ⟨mkSec h₀ W a hmem, secVal_injective h₀ W ha⟩

end

end ComplexAnalytic.BoundedSections
