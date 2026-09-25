/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.ES.Codim2.CoordFreeness
import Oka.Analytic.RiemannExtension

/-!
# Removing a thin set from `N°`

Keep the notation of `Oka/Analytification/RET/ES/BoundedSections.lean`. Let `N°' ⊆ N°` be the
complement in `N°` of the zero set of a function `g` holomorphic on `N°` whose zero set has empty
interior, and let `W'` be the restriction of `W` to `N°'`
(`ComplexAnalytic.BoundedSections.restrictMap`, `ComplexAnalytic.BoundedSections.mapCover`).
By the Riemann extension theorem on the sheets of `W`
(`ComplexAnalytic.BoundedSections.exists_isHolOn_extension`), a section of `𝒪_{W'}` bounded near
`N ∖ N°'` extends to a section of `𝒪_W`; hence the sheaves of bounded sections of `W` and of `W'`
on `N` agree (`ComplexAnalytic.BoundedSections.restrictChart`), and the local conditions for
coherence transfer (`ComplexAnalytic.BoundedSections.isCoherentAt_of_restrict`).

## Main definitions

- `ComplexAnalytic.BoundedSections.restrictMap`: the inclusion `N°' → N°`, as a
  `ComplexAnalytic.BoundedSections.ChartMap`.
- `ComplexAnalytic.BoundedSections.restrictChart`: the identification of the bounded sections.

## Main results

- `ComplexAnalytic.BoundedSections.exists_isHolOn_extension`: Riemann extension on `W`.
- `ComplexAnalytic.BoundedSections.isCoherentAt_of_restrict`: transfer of local coherence.
-/

open CategoryTheory Opposite AlgebraicGeometry Topology TopologicalSpace Filter Set

universe u

namespace ComplexAnalytic.BoundedSections

open AnalyticSpace AlgebraicGeometry.LocallyRingedSpace

noncomputable section

variable {n : ℕ}

/-! ### Riemann extension on `W` -/

section Riemann

variable {N₀ : (AnalyticSpace.complexAffineSpace.{u} n).Opens} {W : FiniteEtaleOver (space N₀)}
  {g : Cn.{u} n → ℂ} (hg : DifferentiableOn ℂ g {x | x ∈ N₀})
  (hgZ : interior ({x : Cn.{u} n | x ∈ N₀} ∩ g ⁻¹' {0}) = ∅)
include hg hgZ

omit hgZ in
lemma isOpen_setOf_ne_zero : IsOpen {w : W.left | g (pt W w) ≠ 0} := by
  have h := hg.continuousOn.isOpen_inter_preimage (isOpen_setOf_mem N₀)
    (isOpen_compl_singleton (x := (0 : ℂ)))
  have : {w : W.left | g (pt W w) ≠ 0} = pt W ⁻¹' ({x : Cn.{u} n | x ∈ N₀} ∩ g ⁻¹' {0}ᶜ) := by
    ext w
    simp [pt_mem W w]
  rw [this]
  exact h.preimage (continuous_pt W)

omit hg in
lemma interior_image_inter_eq_empty {D : Set (Cn.{u} n)} (hD : ∀ x ∈ D, x ∈ N₀) :
    interior (D ∩ g ⁻¹' {0}) = ∅ :=
  subset_empty_iff.1 (hgZ ▸ interior_mono fun x hx ↦ ⟨hD x hx.1, hx.2⟩)

/-- **Riemann extension on `W`.** A function on an open `O ⊆ W` which is holomorphic off the zero
set of `g ∘ p` and bounded near the points of this zero set, uniformly over the fibres, extends to
a holomorphic function on `O`. -/
theorem exists_isHolOn_extension {O : W.left.Opens} {f : W.left → ℂ}
    (hf : IsHolOn W f {w | w ∈ O ∧ g (pt W w) ≠ 0})
    (hb : ∀ w ∈ O, g (pt W w) = 0 → ∃ M ∈ 𝓝 (pt W w), ∃ C, ∀ w', w' ∈ O → pt W w' ∈ M →
      g (pt W w') ≠ 0 → ‖f w'‖ ≤ C) :
    ∃ F : W.left → ℂ, IsHolOn W F O ∧ ∀ w ∈ O, g (pt W w) ≠ 0 → F w = f w := by
  classical
  let O₀ : W.left.Opens := O ⊓ ⟨_, isOpen_setOf_ne_zero (W := W) hg⟩
  obtain ⟨b₀, hb₀⟩ := (hf.mono fun w hw ↦ hw).exists_eval_eq (O := O₀)
  have hloc : ∀ w ∈ O, ∃ S : W.left.Opens, w ∈ S ∧ ∃ F : Cn.{u} n → ℂ,
      DifferentiableOn ℂ F (pt W '' ((S ⊓ O : W.left.Opens) : Set W.left)) ∧
      ∀ v ∈ S ⊓ O, g (pt W v) ≠ 0 → F (pt W v) = f v := by
    intro w hw
    obtain ⟨S, hwS, -, hsheet⟩ := exists_sheet W w
    obtain ⟨F, hFd, hF⟩ := hsheet (O' := S ⊓ O₀) inf_le_left
      (W.left.presheaf.map (homOfLE inf_le_right).op b₀)
    have hF' : ∀ v ∈ S ⊓ O, g (pt W v) ≠ 0 → F (pt W v) = f v := fun v hv hgv ↦ by
      have hv₀ : v ∈ S ⊓ O₀ := ⟨hv.1, hv.2, hgv⟩
      rw [← hF v hv₀, eval_presheaf_map, hb₀]
    set D := pt W '' ((S ⊓ O : W.left.Opens) : Set W.left)
    have hDo : IsOpen D := isOpenMap_pt W _ (S ⊓ O).isOpen
    have hDN : ∀ x ∈ D, x ∈ N₀ := by
      rintro _ ⟨v, -, rfl⟩
      exact pt_mem W v
    have hFD : DifferentiableOn ℂ F (D \ g ⁻¹' {0}) := by
      rintro _ ⟨⟨v, hv, rfl⟩, hgv⟩
      exact (hFd v ⟨hv.1, hv.2, hgv⟩).differentiableWithinAt
    have hbdd : ∀ z ∈ D, IsBoundedUnder (· ≤ ·) (𝓝[D \ g ⁻¹' {0}] z) fun x ↦ ‖F x‖ := by
      rintro _ ⟨v, hv, rfl⟩
      by_cases hgv : g (pt W v) = 0
      · obtain ⟨M, hM, C, hC⟩ := hb v hv.2 hgv
        refine ⟨C, eventually_map.2 ?_⟩
        filter_upwards [nhdsWithin_le_nhds hM, self_mem_nhdsWithin] with x hxM hx
        obtain ⟨⟨v', hv', rfl⟩, hgv'⟩ := hx
        rw [hF' v' hv' hgv']
        exact hC v' hv'.2 hxM hgv'
      · have hc : ContinuousAt F (pt W v) := (hFd v ⟨hv.1, hv.2, hgv⟩).continuousAt
        exact IsBoundedUnder.mono nhdsWithin_le_nhds hc.norm.tendsto.isBoundedUnder_le
    obtain ⟨F', hF'd, hF'F⟩ := exists_differentiableOn_eqOn_of_isBoundedUnder hDo
      (hg.mono hDN) (interior_image_inter_eq_empty hgZ hDN) hFD hbdd
    refine ⟨S, hwS, F', hF'd, fun v hv hgv ↦ ?_⟩
    rw [hF'F ⟨⟨v, hv, rfl⟩, hgv⟩, hF' v hv hgv]
  choose! S hwS F hFd hFf using hloc
  -- two local extensions agree on the common points
  have hcons : ∀ w₁ ∈ O, ∀ w₂ ∈ O, ∀ v ∈ S w₁ ⊓ S w₂ ⊓ O, F w₁ (pt W v) = F w₂ (pt W v) := by
    intro w₁ hw₁ w₂ hw₂ v hv
    set D := pt W '' ((S w₁ ⊓ S w₂ ⊓ O : W.left.Opens) : Set W.left)
    have hD₁ : D ⊆ pt W '' ((S w₁ ⊓ O : W.left.Opens) : Set W.left) :=
      image_mono fun v' hv' ↦ ⟨hv'.1.1, hv'.2⟩
    have hD₂ : D ⊆ pt W '' ((S w₂ ⊓ O : W.left.Opens) : Set W.left) :=
      image_mono fun v' hv' ↦ ⟨hv'.1.2, hv'.2⟩
    have hDN : ∀ x ∈ D, x ∈ N₀ := by
      rintro _ ⟨v', -, rfl⟩
      exact pt_mem W v'
    refine EqOn.of_eqOn_diff_zero (isOpenMap_pt W _ (S w₁ ⊓ S w₂ ⊓ O).isOpen)
      (interior_image_inter_eq_empty hgZ hDN) ((hFd w₁ hw₁).continuousOn.mono hD₁)
      ((hFd w₂ hw₂).continuousOn.mono hD₂) (fun x hx ↦ ?_) ⟨v, hv, rfl⟩
    obtain ⟨⟨v', hv', rfl⟩, hgv'⟩ := hx
    rw [hFf w₁ hw₁ v' ⟨hv'.1.1, hv'.2⟩ hgv', hFf w₂ hw₂ v' ⟨hv'.1.2, hv'.2⟩ hgv']
  refine ⟨fun w ↦ F w (pt W w), fun w hw ↦ ⟨F w, ?_⟩, fun w hw hgw ↦ hFf w hw w ⟨hwS w hw, hw⟩ hgw⟩
  filter_upwards [(S w ⊓ O).isOpen.mem_nhds ⟨hwS w hw, hw⟩] with v hv
  refine ⟨(hFd w hw).differentiableAt ((isOpenMap_pt W _ (S w ⊓ O).isOpen).mem_nhds
    ⟨v, hv, rfl⟩), ?_⟩
  exact (hcons v hv.2 w hw v ⟨⟨hwS v hv.2, hv.1⟩, hv.2⟩)

omit hg in
/-- Points of `W` off the zero set of `g ∘ p` accumulate at every point of `W`. -/
lemma frequently_ne_zero (w : W.left) : ∃ᶠ w' in 𝓝 w, g (pt W w') ≠ 0 := by
  intro hev
  obtain ⟨U, hUw, hUo, hwU⟩ := eventually_nhds_iff.1 (hev.mono fun _ h ↦ not_not.1 h)
  have hsub : pt W '' U ⊆ interior ({x : Cn.{u} n | x ∈ N₀} ∩ g ⁻¹' {0}) :=
    interior_maximal (by rintro _ ⟨v, hv, rfl⟩; exact ⟨pt_mem W v, hUw v hv⟩)
      (isOpenMap_pt W U hUo)
  rw [hgZ] at hsub
  exact hsub ⟨w, hwU, rfl⟩

end Riemann

/-! ### Local bounds over `N°` -/

section Bound

variable {N N₀ : (AnalyticSpace.complexAffineSpace.{u} n).Opens} (h₀ : N₀ ≤ N)
  (W : FiniteEtaleOver (space N₀)) [T2Space W.left]

/-- Sections of `𝒜` are bounded near every point of `N°`, uniformly over the fibre. -/
lemma exists_bound_of_mem {V : (space N).Opens} (a : (boundedModule h₀ W).val.obj (op V))
    {x : Cn.{u} n} (hx : x ∈ img V) (hxN : x ∈ N₀) :
    ∃ M ∈ 𝓝 x, ∃ C, ∀ w, pt W w ∈ M → pt W w ∈ img V → ‖evalFun (secVal h₀ W a) w‖ ≤ C := by
  classical
  obtain ⟨B, I, _, σ, hBo, hxB, -, hσ, hσc, huniq, -⟩ := exists_local_sheets W hxN
  set f := evalFun (secVal h₀ W a)
  have hc (i : I) : ContinuousAt (fun y ↦ f (σ i y)) x := by
    have hmem : σ i x ∈ preim h₀ W V := (mem_preim_iff h₀ W).2 (by rw [hσ i x hxB]; exact hx)
    exact ((isHolOn_secVal h₀ W a).continuousAt hmem).comp
      ((hσc i).continuousAt (hBo.mem_nhds hxB))
  have hev : ∀ᶠ y in 𝓝 x, ∀ i, ‖f (σ i y)‖ < ‖f (σ i x)‖ + 1 :=
    eventually_all.2 fun i ↦ (hc i).norm.eventually (gt_mem_nhds (lt_add_one _))
  refine ⟨B ∩ {y | ∀ i, ‖f (σ i y)‖ < ‖f (σ i x)‖ + 1}, inter_mem (hBo.mem_nhds hxB) hev,
    ∑ i, (‖f (σ i x)‖ + 1), fun w hw _ ↦ ?_⟩
  obtain ⟨i, hi, -⟩ := huniq w hw.1
  rw [← hi]
  exact (hw.2 i).le.trans (Finset.single_le_sum (f := fun i ↦ ‖f (σ i x)‖ + 1)
    (fun j _ ↦ by positivity) (Finset.mem_univ i))

end Bound

/-! ### The restriction of `W` to `N°'` -/

section Restrict

variable {N₀ N₀' : (AnalyticSpace.complexAffineSpace.{u} n).Opens}

open Classical in
/-- **The inclusion `N°' → N°`** as a `ComplexAnalytic.BoundedSections.ChartMap`; off `N°'` it
takes a fixed value `p ∉ N°`. -/
def restrictMap (h₀' : N₀' ≤ N₀) {p : Cn.{u} n} (hp : p ∉ N₀) : ChartMap N₀' N₀ where
  χ x := if x ∈ N₀' then x else p
  χInv := id
  R := univ
  isOpen_R := isOpen_univ
  differentiableOn_χ := differentiableOn_id.congr fun x hx ↦ if_pos hx
  differentiableOn_χInv := differentiableOn_id
  mem_iff x := by
    change x ∈ N₀' ↔ (if x ∈ N₀' then x else p) ∈ N₀
    by_cases hx : x ∈ N₀'
    · rw [if_pos hx]
      exact ⟨fun _ ↦ h₀' hx, fun _ ↦ hx⟩
    · rw [if_neg hx]
      exact ⟨fun h ↦ absurd h hx, fun h ↦ absurd h hp⟩
  χ_mem_R _ _ := mem_univ _
  χInv_χ x hx := if_pos hx
  χ_χInv _ _ hy := if_pos hy

lemma restrictMap_χ (h₀' : N₀' ≤ N₀) {p : Cn.{u} n} (hp : p ∉ N₀) {x : Cn.{u} n}
    (hx : x ∈ N₀') : (restrictMap h₀' hp).χ x = x :=
  if_pos hx

end Restrict

/-! ### The identification of the bounded sections -/

section Chart

variable {N : (AnalyticSpace.complexAffineSpace.{u} n).Opens}

lemma isOpenEmbedding_idHom : IsOpenEmbedding (𝟙 (space N).toPresheafedSpace.carrier) :=
  IsOpenEmbedding.id

/-- The image of an open under the identity. -/
abbrev idImg (O : (space N).Opens) : (space N).Opens :=
  (isOpenEmbedding_idHom (N := N)).isOpenMap.functor.obj O

lemma idImg_eq (O : (space N).Opens) : idImg O = O :=
  Opens.ext (Set.image_id _)

lemma idImg_le (O : (space N).Opens) : idImg O ≤ O :=
  (idImg_eq O).le

lemma le_idImg (O : (space N).Opens) : O ≤ idImg O :=
  (idImg_eq O).ge

/-- The identification of the sections of `𝒪_N` over `O` and over its image under the identity.
-/
def idψ (O : (space N).Opens) :
    (space N).presheaf.obj (op (idImg O)) →+* (space N).presheaf.obj (op O) :=
  ((space N).presheaf.map (homOfLE (le_idImg O)).op).hom

lemma bijective_idψ (O : (space N).Opens) : Function.Bijective (idψ O) := by
  refine ⟨fun r r' h ↦ ?_, fun s ↦ ⟨(space N).res (idImg_le O) s, ?_⟩⟩
  · have := congrArg ((space N).res (idImg_le O)) h
    change (space N).res _ ((space N).res _ r) = (space N).res _ ((space N).res _ r') at this
    rwa [res_res, res_res, res_self, res_self] at this
  · change (space N).res _ ((space N).res _ s) = s
    rw [res_res, res_self]

lemma idψ_res {O₁ O₂ : (space N).Opens} (h : O₁ ≤ O₂)
    (r : (space N).presheaf.obj (op (idImg O₂))) :
    idψ O₁ ((space N).res ((isOpenEmbedding_idHom (N := N)).isOpenMap.functor.monotone h) r) =
      (space N).res h (idψ O₂ r) := by
  change (space N).res _ ((space N).res _ r) = (space N).res _ ((space N).res _ r)
  rw [res_res, res_res]

variable {N₀ N₀' : (AnalyticSpace.complexAffineSpace.{u} n).Opens} {h₀ : N₀ ≤ N}
  (h₀' : N₀' ≤ N₀) {W : FiniteEtaleOver (space N₀)} {W' : FiniteEtaleOver (space N₀')}
  {Φ : ChartMap N₀' N₀} {β : W'.left → W.left} (hβ : IsMapPullback Φ W W' β)
  (hΦ : ∀ x ∈ N₀', Φ.χ x = x)
include hβ hΦ

lemma pt_β (w' : W'.left) : pt W (β w') = pt W' w' := by
  rw [hβ.pt_eq, hΦ _ (pt_mem W' w')]

lemma exists_β {w : W.left} (hw : pt W w ∈ N₀') : ∃ w', β w' = w ∧ pt W' w' = pt W w := by
  obtain ⟨w', h₁, h₂⟩ := hβ.exists_lift w (pt W w) (hΦ _ hw).symm
  exact ⟨w', h₂, h₁⟩

lemma β_mem_preim {O : (space N).Opens} {w' : W'.left} (hw' : w' ∈ preim (h₀'.trans h₀) W' O) :
    β w' ∈ preim h₀ W (idImg O) := by
  rw [mem_preim_iff, pt_β hβ hΦ, idImg_eq]
  exact (mem_preim_iff _ W').1 hw'

variable [T2Space W.left]

lemma isBddOn_comp_β {O : (space N).Opens}
    (a : (boundedModule h₀ W).val.obj (op (idImg O))) :
    IsBddOn W' O (fun w' ↦ evalFun (secVal h₀ W a) (β w')) := by
  intro x hx hxN
  have hx' : x ∈ img (idImg O) := by rwa [idImg_eq]
  by_cases hx₀ : x ∈ N₀
  · obtain ⟨M, hM, C, hC⟩ := exists_bound_of_mem h₀ W a hx' hx₀
    refine ⟨M, hM, C, fun w' hw'M hw'O ↦ hC (β w') ?_ ?_⟩
    · rwa [pt_β hβ hΦ]
    · rw [pt_β hβ hΦ, idImg_eq]
      exact hw'O
  · obtain ⟨M, hM, C, hC⟩ := isBddOn_secVal h₀ W a x hx' hx₀
    refine ⟨M, hM, C, fun w' hw'M hw'O ↦ hC (β w') ?_ ?_⟩
    · rwa [pt_β hβ hΦ]
    · rw [pt_β hβ hΦ, idImg_eq]
      exact hw'O

/-- Sections of `𝒜` over `O` as sections of `𝒜'` over `O`: composition with `β`. -/
def restrictFun (O : (space N).Opens) (a : (boundedModule h₀ W).val.obj (op (idImg O))) :
    (boundedModule (h₀'.trans h₀) W').val.obj (op O) :=
  (exists_secVal_eq (h₀'.trans h₀) W' (hβ.isHolOn_comp (isHolOn_secVal h₀ W a)
    fun _ hw' ↦ β_mem_preim h₀' hβ hΦ hw') (isBddOn_comp_β hβ hΦ a)).choose

lemma evalFun_restrictFun (O : (space N).Opens)
    (a : (boundedModule h₀ W).val.obj (op (idImg O))) {w' : W'.left}
    (hw' : w' ∈ preim (h₀'.trans h₀) W' O) :
    evalFun (secVal (h₀'.trans h₀) W' (restrictFun h₀' hβ hΦ O a)) w' =
      evalFun (secVal h₀ W a) (β w') :=
  (exists_secVal_eq (h₀'.trans h₀) W' (hβ.isHolOn_comp (isHolOn_secVal h₀ W a)
    fun _ hw' ↦ β_mem_preim h₀' hβ hΦ hw') (isBddOn_comp_β hβ hΦ a)).choose_spec w' hw'

/-- The identification of the sections of `𝒜` over `O` with the sections of `𝒜'` over `O`. -/
def restrictφ (O : (space N).Opens) :
    (boundedModule h₀ W).val.obj (op (idImg O)) →+
      (boundedModule (h₀'.trans h₀) W').val.obj (op O) where
  toFun := restrictFun h₀' hβ hΦ O
  map_zero' := secVal_ext _ W' fun w' hw' ↦ by
    rw [evalFun_restrictFun h₀' hβ hΦ O _ hw', evalFun_secVal_zero hw',
      evalFun_secVal_zero (β_mem_preim h₀' hβ hΦ hw')]
  map_add' a b := secVal_ext _ W' fun w' hw' ↦ by
    rw [evalFun_restrictFun h₀' hβ hΦ O _ hw', evalFun_secVal_add _ _ hw',
      evalFun_restrictFun h₀' hβ hΦ O _ hw', evalFun_restrictFun h₀' hβ hΦ O _ hw',
      evalFun_secVal_add _ _ (β_mem_preim h₀' hβ hΦ hw')]

lemma evalFun_restrictφ (O : (space N).Opens)
    (a : (boundedModule h₀ W).val.obj (op (idImg O))) {w' : W'.left}
    (hw' : w' ∈ preim (h₀'.trans h₀) W' O) :
    evalFun (secVal (h₀'.trans h₀) W' (restrictφ h₀' hβ hΦ O a)) w' =
      evalFun (secVal h₀ W a) (β w') :=
  evalFun_restrictFun h₀' hβ hΦ O a hw'

lemma restrictφ_res {O₁ O₂ : (space N).Opens} (h : O₁ ≤ O₂)
    (a : (boundedModule h₀ W).val.obj (op (idImg O₂))) :
    restrictφ h₀' hβ hΦ O₁ (sectRes (boundedModule h₀ W)
      ((isOpenEmbedding_idHom (N := N)).isOpenMap.functor.monotone h) a) =
      sectRes (boundedModule (h₀'.trans h₀) W') h (restrictφ h₀' hβ hΦ O₂ a) :=
  secVal_ext _ W' fun w' hw' ↦ by
    rw [evalFun_restrictφ h₀' hβ hΦ _ _ hw',
      evalFun_secVal_sectRes _ _ (β_mem_preim h₀' hβ hΦ hw'), evalFun_secVal_sectRes _ _ hw',
      evalFun_restrictφ h₀' hβ hΦ _ _ (preim_mono _ W' h hw')]

lemma restrictφ_smul (O : (space N).Opens) (r : (space N).presheaf.obj (op (idImg O)))
    (a : (boundedModule h₀ W).val.obj (op (idImg O))) :
    restrictφ h₀' hβ hΦ O (r • a) = idψ O r • restrictφ h₀' hβ hΦ O a :=
  secVal_ext _ W' fun w' hw' ↦ by
    rw [evalFun_restrictφ h₀' hβ hΦ _ _ hw',
      evalFun_secVal_smul _ _ (β_mem_preim h₀' hβ hΦ hw'), evalFun_secVal_smul _ _ hw',
      evalFun_restrictφ h₀' hβ hΦ _ _ hw', pt_β hβ hΦ]
    congr 1
    exact (holFun_map (le_idImg O) r ((mem_preim_iff _ W').1 hw')).symm

variable {g : Cn.{u} n → ℂ} (hg : DifferentiableOn ℂ g {x | x ∈ N₀})
  (hgZ : interior ({x : Cn.{u} n | x ∈ N₀} ∩ g ⁻¹' {0}) = ∅)
  (hgN : ∀ x ∈ N₀, x ∈ N₀' ↔ g x ≠ 0)
include hgZ hgN

lemma injective_restrictφ (O : (space N).Opens) :
    Function.Injective (restrictφ (h₀ := h₀) h₀' hβ hΦ O) := by
  intro a b h
  have hval : ∀ w' ∈ preim (h₀'.trans h₀) W' O,
      evalFun (secVal h₀ W a) (β w') = evalFun (secVal h₀ W b) (β w') := fun w' hw' ↦ by
    have := congrArg (fun c ↦ evalFun (secVal (h₀'.trans h₀) W' c) w') h
    rwa [evalFun_restrictφ h₀' hβ hΦ _ _ hw', evalFun_restrictφ h₀' hβ hΦ _ _ hw'] at this
  set P := preim h₀ W (idImg O)
  have hN' : ∀ v ∈ P, pt W v ∈ N₀' →
      evalFun (secVal h₀ W a) v = evalFun (secVal h₀ W b) v := fun v hv hvN ↦ by
    obtain ⟨v', rfl, hv'⟩ := exists_β hβ hΦ hvN
    refine hval v' ((mem_preim_iff _ W').2 ?_)
    rw [hv', ← idImg_eq O]
    exact (mem_preim_iff h₀ W).1 hv
  refine secVal_ext h₀ W fun w hw ↦ ?_
  obtain ⟨S, hwS, -, hsheet⟩ := exists_sheet W w
  obtain ⟨Fa, hFad, hFa⟩ := hsheet (O' := S ⊓ P) inf_le_left
    (W.left.presheaf.map (homOfLE inf_le_right).op (secVal h₀ W a))
  obtain ⟨Fb, hFbd, hFb⟩ := hsheet (O' := S ⊓ P) inf_le_left
    (W.left.presheaf.map (homOfLE inf_le_right).op (secVal h₀ W b))
  have hFa' : ∀ v (hv : v ∈ S ⊓ P), evalFun (secVal h₀ W a) v = Fa (pt W v) := fun v hv ↦ by
    rw [← hFa v hv, eval_presheaf_map, evalFun_of_mem _ hv.2]
  have hFb' : ∀ v (hv : v ∈ S ⊓ P), evalFun (secVal h₀ W b) v = Fb (pt W v) := fun v hv ↦ by
    rw [← hFb v hv, eval_presheaf_map, evalFun_of_mem _ hv.2]
  set D := pt W '' ((S ⊓ P : W.left.Opens) : Set W.left)
  have hDN : ∀ x ∈ D, x ∈ N₀ := by
    rintro _ ⟨v, -, rfl⟩
    exact pt_mem W v
  have hc : ∀ {F : Cn.{u} n → ℂ}, (∀ v ∈ S ⊓ P, DifferentiableAt ℂ F (pt W v)) →
      ContinuousOn F D := fun hF ↦ by
    rintro _ ⟨v, hv, rfl⟩
    exact (hF v hv).continuousAt.continuousWithinAt
  have hEq := EqOn.of_eqOn_diff_zero (isOpenMap_pt W _ (S ⊓ P).isOpen)
    (interior_image_inter_eq_empty hgZ hDN) (hc hFad) (hc hFbd) (fun x hx ↦ ?_)
    ⟨w, ⟨hwS, hw⟩, rfl⟩
  · rw [hFa' w ⟨hwS, hw⟩, hFb' w ⟨hwS, hw⟩]
    exact hEq
  · obtain ⟨⟨v, hv, rfl⟩, hgv⟩ := hx
    rw [← hFa' v hv, ← hFb' v hv]
    exact hN' v hv.2 ((hgN _ (pt_mem W v)).2 hgv)

include hg in
lemma surjective_restrictφ (O : (space N).Opens) :
    Function.Surjective (restrictφ (h₀ := h₀) h₀' hβ hΦ O) := by
  intro b
  set P := preim h₀ W (idImg O)
  set f := IsMapPullback.liftFun β (evalFun (secVal (h₀'.trans h₀) W' b))
  have hPO : ∀ {w : W.left}, w ∈ P ↔ pt W w ∈ img O := fun {w} ↦ by
    rw [mem_preim_iff, idImg_eq]
  have hmem : ∀ w ∈ P, g (pt W w) ≠ 0 → ∃ w', β w' = w ∧ w' ∈ preim (h₀'.trans h₀) W' O :=
    fun w hw hgw ↦ by
      obtain ⟨w', rfl, hw'⟩ := exists_β hβ hΦ ((hgN _ (pt_mem W w)).2 hgw)
      exact ⟨w', rfl, (mem_preim_iff _ W').2 (hw' ▸ hPO.1 hw)⟩
  have hf : IsHolOn W f {w | w ∈ P ∧ g (pt W w) ≠ 0} :=
    (hβ.isHolOn_liftFun (isHolOn_secVal (h₀'.trans h₀) W' b)).mono fun w hw ↦ by
      obtain ⟨w', rfl, hw'⟩ := hmem w hw.1 hw.2
      exact ⟨w', hw', rfl⟩
  have hbd : ∀ x ∈ img O, x ∉ N₀' → ∃ M ∈ 𝓝 x, ∃ C, ∀ w ∈ P, pt W w ∈ M →
      g (pt W w) ≠ 0 → ‖f w‖ ≤ C := fun x hx hxN ↦ by
    obtain ⟨M, hM, C, hC⟩ := isBddOn_secVal (h₀'.trans h₀) W' b x hx hxN
    refine ⟨M, hM, C, fun w hw hwM hgw ↦ ?_⟩
    obtain ⟨w', rfl, hw'⟩ := hmem w hw hgw
    change ‖IsMapPullback.liftFun β _ (β w')‖ ≤ C
    rw [hβ.liftFun_apply]
    rw [pt_β hβ hΦ] at hwM
    exact hC w' hwM ((mem_preim_iff _ W').1 hw')
  obtain ⟨F, hFh, hFf⟩ := exists_isHolOn_extension hg hgZ (O := P) hf fun w hw hgw ↦
    hbd (pt W w) (hPO.1 hw) fun h ↦ ((hgN _ (pt_mem W w)).1 h) hgw
  have hFb : IsBddOn W (idImg O) F := by
    intro x hx hxN
    rw [idImg_eq] at hx
    obtain ⟨M, hM, C, hC⟩ := hbd x hx fun h ↦ hxN (h₀' h)
    refine ⟨interior M, interior_mem_nhds.2 hM, C, fun w hwM hwO ↦ ?_⟩
    have hwP : w ∈ P := (mem_preim_iff h₀ W).2 hwO
    by_contra hlt
    push Not at hlt
    have hev : ∀ᶠ w' in 𝓝 w, C < ‖F w'‖ ∧ w' ∈ P ∧ pt W w' ∈ interior M := by
      refine (((hFh.continuousAt hwP).norm.eventually (lt_mem_nhds hlt)).and
        (P.isOpen.mem_nhds hwP)).and ?_ |>.mono fun _ h ↦ ⟨h.1.1, h.1.2, h.2⟩
      exact (continuous_pt W).continuousAt.preimage_mem_nhds (isOpen_interior.mem_nhds hwM)
    obtain ⟨w', ⟨hlt', hw'P, hw'M⟩, hgw'⟩ := (hev.and_frequently
      (frequently_ne_zero hgZ w)).exists
    rw [hFf w' hw'P hgw'] at hlt'
    exact absurd (hC w' hw'P (interior_subset hw'M) hgw') (not_le.2 hlt')
  obtain ⟨a, ha⟩ := exists_secVal_eq h₀ W hFh hFb
  refine ⟨a, secVal_ext _ W' fun w' hw' ↦ ?_⟩
  have hβw := β_mem_preim (h₀ := h₀) h₀' hβ hΦ hw'
  have hgw : g (pt W (β w')) ≠ 0 := by
    rw [pt_β hβ hΦ]
    exact (hgN _ (h₀' (pt_mem W' w'))).1 (pt_mem W' w')
  rw [evalFun_restrictφ h₀' hβ hΦ _ _ hw', ha _ hβw, hFf _ hβw hgw]
  exact hβ.liftFun_apply _ w'

include hg in
/-- **The bounded sections of `W` and of its restriction `W'` to `N°'` agree.** -/
def restrictChart : ModuleChart (boundedModule h₀ W) (boundedModule (h₀'.trans h₀) W') where
  g := 𝟙 _
  isOpenEmbedding := isOpenEmbedding_idHom
  ψ := idψ
  bijective_ψ := bijective_idψ
  ψ_res := idψ_res
  φ := restrictφ h₀' hβ hΦ
  bijective_φ O := ⟨injective_restrictφ h₀' hβ hΦ hgZ hgN O,
    surjective_restrictφ h₀' hβ hΦ hg hgZ hgN O⟩
  φ_res := restrictφ_res h₀' hβ hΦ
  φ_smul := restrictφ_smul h₀' hβ hΦ

include hg in
/-- **The local conditions for coherence transfer from `W'` to `W`.** -/
theorem isCoherentAt_of_restrict {x : space N} (hx : IsCoherentAt (h₀'.trans h₀) W' x) :
    IsCoherentAt h₀ W x :=
  ⟨(restrictChart h₀' hβ hΦ hg hgZ hgN).isLocallyFinitelyGeneratedModuleAt hx.1,
    (restrictChart h₀' hβ hΦ hg hgZ hgN).hasLocalModuleRelationsAt hx.2⟩

end Chart

end

end ComplexAnalytic.BoundedSections
