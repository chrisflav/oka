/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.ES.Codim2.BlowupCoherent
import Oka.Analytification.RET.ES.Codim2.ChartFreeness

/-!
# Pushing generators of bounded sections down along a blow-up

Keep the notation of `Oka/Analytification/RET/ES/Codim2/BlowupSheaf.lean`: `τ`, `ω` are
holomorphic on `N` with `τ ≠ 0` on `N°`, `C = {τ = ω = 0}`, and `𝒢` is the sheaf on
`P^an = ℂⁿ × ℙ¹` of sections of `ρ_* 𝒪_W` bounded near the points over `ℂⁿ ∖ N°`, i.e. the
pushforward of the sheaf of bounded sections on the blow-up `Ñ` of `N` along `C`.

Suppose that `𝒢` is coherent over `U × ℙ¹` and that `𝒜` is free near every point of `U ∖ C`.
Then near every point of `U` there are finitely many sections of `𝒜` such that near every point
off `C` the sheaf `𝒜` is free with a basis in their span
(`ComplexAnalytic.BoundedSections.BlowupData.exists_isFreeSpanAt`).

By relative Theorem A (`ComplexAnalytic.relProjectiveLine.exists_finite_generates_twistMod`),
for `k ≫ 0` finitely many sections `σⱼ` of `𝒢(k)` over `B × ℙ¹` generate `𝒢(k)`, `B` a box.
In the chart `i` the section `σⱼ` is a section `gᵢⱼ` of `𝒢`, with `g₀ⱼ = (ω / τ)ᵏ g₁ⱼ`, and
`sⱼ = τᵏ g₀ⱼ = ωᵏ g₁ⱼ` is a function on `W` over `B`
(`ComplexAnalytic.BoundedSections.BlowupData.pushFun`, `…BlowupData.pushFun_eq`). It is bounded
near every point `x ∉ N°`: the `gᵢⱼ` are bounded near every point of the compact fibre
`{x} × ℙ¹`, hence over a neighbourhood of `x` (`…BlowupData.isBddOn_pushFun`). So the `sⱼ` are
sections of `𝒜` over `B` (`…BlowupData.pushSec`). Near a point `y ∉ C` with `θᵢ(y) ≠ 0`
(`θ₀ = τ`, `θ₁ = ω`), a section `a` of `𝒜` gives the section `θᵢ⁻ᵏ a` of `𝒢 = 𝒢(k)` over the
chart `i`; writing it as a combination of the `σⱼ` near `(y, [τ(y) : ω(y)])` and multiplying by
`θᵢᵏ` writes `a` as a combination of the `sⱼ` near `y` (`…BlowupData.exists_span_pushSec`).
Together with the freeness of `𝒜` near `y` this gives a basis in the span of the `sⱼ`.

For the blow-up of `C = {t = 0, w = φ}` (`ComplexAnalytic.BoundedSections.BlowupCentre`) both
hypotheses follow from the charts: `𝒢` is coherent if the bounded sections of the pullbacks `W₁`,
`W₂` of `W` to the two charts are (`…BlowupCentre.isCoherent_module`), and `𝒜` is free off `C` if
they are free off the exceptional divisor, since the charts are biholomorphic there
(`…BlowupCentre.exists_isFreeSpanAt_of_not_mem_centre`). This gives
`…BlowupCentre.exists_isFreeSpanAt_of_charts`, which only assumes coherence of the bounded
sections on the blow-up, so it applies to iterated blow-ups.

## Main definitions

- `ComplexAnalytic.BoundedSections.BlowupData.centre`: the centre `C = {τ = ω = 0}`.
- `ComplexAnalytic.BoundedSections.BlowupData.pushSec`: the sections `τᵏ g₀ⱼ` of `𝒜`.

## Main results

- `ComplexAnalytic.BoundedSections.BlowupData.exists_span_pushSec`: the `sⱼ` generate `𝒜` near
  every point off `C`.
- `ComplexAnalytic.BoundedSections.BlowupData.exists_isFreeSpanAt`: generators of `𝒜` near
  points of `C` which span local bases off `C`.
- `ComplexAnalytic.BoundedSections.BlowupCentre.exists_isFreeSpanAt_of_charts`: the same, from
  coherence of the bounded sections on the two charts of the blow-up and their freeness off the
  exceptional divisor.
-/

open CategoryTheory Opposite AlgebraicGeometry Topology TopologicalSpace Filter

universe u

namespace ComplexAnalytic.BoundedSections

open AnalyticSpace relProjectiveSpaceAn relProjectiveLine AlgebraicGeometry.LocallyRingedSpace

noncomputable section

namespace BlowupData

variable {n : ℕ} {N N₀ : (AnalyticSpace.complexAffineSpace.{u} n).Opens} {h₀ : N₀ ≤ N}
  {c : BlowupData N N₀} {W : FiniteEtaleOver (space N₀)}

variable (c) in
/-- The centre `C = {τ = ω = 0}` of the blow-up. -/
def centre : Set (Cn.{u} n) :=
  {x | c.τ x = 0 ∧ c.ω x = 0}

lemma exists_θ_ne_zero {x : Cn.{u} n} (hx : x ∉ c.centre) : ∃ i, c.θ i x ≠ 0 := by
  by_contra h
  push Not at h
  exact hx ⟨h 0, h 1⟩

/-! ### The components of sections of `𝒢(k)` in the charts -/

variable {B : Opens (Fin n → ℂ)} {k : ℕ} {I : Type u}
  (σ : I → (twistMod (c.module h₀ W) k).val.obj (op (tube.{u} (N := 1) B)))

/-- The component in the chart `i` of a section `σⱼ` of `𝒢(k)` over `B × ℙ¹`: a section of `𝒢`
over `B × ℙ¹ ∩ π⁻¹ Uᵢ`. -/
def comp (i : Fin 2) (j : I) :
    (c.module h₀ W).val.obj (op (tube.{u} (N := 1) B ⊓ stdOpen.{u} n 1 i)) :=
  modTwistSectionsEquiv (N := c.module h₀ W) (twistModCocycle.{u} n 1 k) i inf_le_right
    (modRes (σ j) _ inf_le_left)

/-- The function `τᵏ g₀ⱼ` on `W`, where `g₀ⱼ` is the component of `σⱼ` in the chart `0`. -/
def pushFun (j : I) (w : W.left) : ℂ :=
  c.τ (pt W w) ^ k * evalFun (gVal (comp σ 0 j)) w

lemma pushFun_eq_one (j : I) {w : W.left}
    (hw : w ∈ (Opens.map (c.proj h₀ W).toLRSHom.base).obj
      (tube.{u} (N := 1) B ⊓ stdOpen.{u} n 1 1)) :
    pushFun σ j w = c.ω (pt W w) ^ k * evalFun (gVal (comp σ 1 j)) w := by
  have hτ : c.τ (pt W w) ≠ 0 := c.τ_ne_zero _ (pt_mem W w)
  have hθ : c.ω (pt W w) ≠ 0 := c.θ_ne_zero_of_mem_stdOpen 1 hτ
    (mem_proj_preimage.1 (show w ∈ (Opens.map _).obj (stdOpen.{u} n 1 1) from hw.2))
  let O' := tube.{u} (N := 1) B ⊓ (stdOpen.{u} n 1 0 ⊓ stdOpen.{u} n 1 1)
  have h0 : O' ≤ tube.{u} (N := 1) B ⊓ stdOpen.{u} n 1 0 := inf_le_inf_left _ inf_le_left
  have h1 : O' ≤ tube.{u} (N := 1) B ⊓ stdOpen.{u} n 1 1 := inf_le_inf_left _ inf_le_right
  have hwO' : w ∈ (Opens.map (c.proj h₀ W).toLRSHom.base).obj O' :=
    ⟨hw.1, mem_proj_preimage.2 (c.blowupPt_mem_stdOpen_zero _), hw.2⟩
  have e (i : Fin 2) (hi : O' ≤ tube.{u} (N := 1) B ⊓ stdOpen.{u} n 1 i) :
      modTwistSectionsEquiv (N := c.module h₀ W) (twistModCocycle.{u} n 1 k) i
        (hi.trans inf_le_right) (modRes (σ j) O' (hi.trans inf_le_left)) =
        modRes (comp σ i j) O' hi := by
    rw [comp, ← modTwistSectionsEquiv_res, modRes_res]
  have key := modTwistSectionsEquiv_change (N := c.module h₀ W) (twistModCocycle.{u} n 1 k) 0
    (h0.trans inf_le_right) 1 (h1.trans inf_le_right) (modRes (σ j) O' (h0.trans inf_le_left))
  rw [e 0 h0, e 1 h1] at key
  have hv := congrArg (fun s ↦ evalFun (gVal s) w) key
  rw [evalFun_gVal_modRes h0 _ hwO', evalFun_gVal_smul _ _ hwO', evalFun_gVal_modRes h1 _ hwO',
    AnalyticSpace.eval_restrictOpen, eval_proj_base _ _ 0 hτ] at hv
  have hp : chartPt.{u} 0 (baseCoord (pt W w), c.ω (pt W w) / c.τ (pt W w)) ∈
      stdOpen.{u} n 1 0 ⊓ stdOpen.{u} n 1 1 := by
    have h := hwO'.2
    rw [proj_base] at h
    exact h
  rw [pushFun, hv]
  change c.τ (pt W w) ^ k * (f0 _ (baseCoord (pt W w), c.ω (pt W w) / c.τ (pt W w)) * _) = _
  rw [f0_twistModCocycle k hp, zpow_natCast, ← mul_assoc, ← mul_pow, mul_div_cancel₀ _ hτ]

/-- **`τᵏ g₀ⱼ = θᵢᵏ gᵢⱼ`** in the chart `i`: the transition function of `𝒢(k)` from the chart `1`
to the chart `0` is `(ω / τ)ᵏ`. -/
lemma pushFun_eq (i : Fin 2) (j : I) {w : W.left}
    (hw : w ∈ (Opens.map (c.proj h₀ W).toLRSHom.base).obj
      (tube.{u} (N := 1) B ⊓ stdOpen.{u} n 1 i)) :
    pushFun σ j w = c.θ i (pt W w) ^ k * evalFun (gVal (comp σ i j)) w := by
  fin_cases i
  exacts [rfl, pushFun_eq_one σ j hw]

/-! ### The pushed-down sections -/

lemma mem_closedBox_self_iff {a y : Fin n → ℂ} : y ∈ Complex.closedBox a a ↔ y = a := by
  simp only [Complex.closedBox, Set.mem_univ_pi, Complex.mem_reProdIm, Set.Icc_self,
    Set.mem_singleton_iff]
  exact ⟨fun h ↦ funext fun j ↦ Complex.ext (h j).1 (h j).2, fun h j ↦ by simp [h]⟩

lemma baseY_of_mem_tubeCompact {a : Fin n → ℂ} {p : relProjectiveSpaceAn.{u} n 1}
    (hp : p ∈ tubeCompact.{u} (Complex.closedBox a a)) : baseY p = a := by
  rcases hp with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩ <;>
  · rw [baseY_chartPt]
    exact mem_closedBox_self_iff.1 hq.1

variable (N) in
/-- The open of `N` over an open `B ⊆ Fin n → ℂ`. -/
def overBox (B : Opens (Fin n → ℂ)) : (space N).Opens :=
  ⟨{y | baseCoord y.1 ∈ B},
    (B.isOpen.preimage continuous_baseCoord).preimage continuous_subtype_val⟩

lemma mem_img_overBox {x : Cn.{u} n} : x ∈ img (overBox N B) ↔ x ∈ N ∧ baseCoord x ∈ B := by
  rw [mem_img_iff]
  exact ⟨fun ⟨h, h'⟩ ↦ ⟨h, h'⟩, fun ⟨h, h'⟩ ↦ ⟨h, h'⟩⟩

lemma mem_proj_tube_of_mem_preim {w : W.left} (hw : w ∈ preim h₀ W (overBox N B)) (i : Fin 2)
    (hi : c.blowupPt (pt W w) ∈ stdOpen.{u} n 1 i) :
    w ∈ (Opens.map (c.proj h₀ W).toLRSHom.base).obj
      (tube.{u} (N := 1) B ⊓ stdOpen.{u} n 1 i) := by
  refine mem_proj_preimage.2 ⟨?_, hi⟩
  change baseY (c.blowupPt (pt W w)) ∈ B
  rw [baseY_blowupPt]
  exact (mem_img_overBox.1 ((mem_preim_iff h₀ W).1 hw)).2

lemma isHolOn_pushFun (j : I) : IsHolOn W (pushFun σ j) (preim h₀ W (overBox N B)) := by
  have h₁ : IsHolOn W (fun w ↦ c.τ (pt W w) ^ k) (preim h₀ W (overBox N B)) :=
    isHolOn_comp_pt N.isOpen (c.differentiableOn_τ.pow k) fun w _ ↦ h₀ (pt_mem W w)
  have h₂ : IsHolOn W (evalFun (gVal (comp σ 0 j))) (preim h₀ W (overBox N B)) :=
    (isHolOn_evalFun _).mono fun w hw ↦
      mem_proj_tube_of_mem_preim hw 0 (c.blowupPt_mem_stdOpen_zero _)
  exact h₁.mul h₂

/-- **`τᵏ g₀ⱼ` is bounded near every point of `B ∖ N°`**: the components `gᵢⱼ` are bounded near
every point of the compact fibre over such a point, hence over a neighbourhood of it. -/
lemma isBddOn_pushFun (j : I) : IsBddOn W (overBox N B) (pushFun σ j) := by
  classical
  intro x hx hxN
  obtain ⟨hxN', hxB⟩ := mem_img_overBox.1 hx
  set a := baseCoord x
  have hloc : ∀ p ∈ tubeCompact.{u} (Complex.closedBox a a), ∃ (i : Fin 2)
      (U : Set (relProjectiveSpaceAn.{u} n 1)), IsOpen U ∧ p ∈ U ∧
      U ⊆ ((tube.{u} (N := 1) B ⊓ stdOpen.{u} n 1 i : (relProjectiveSpaceAn.{u} n 1).Opens) :
        Set _) ∧ ∃ C : ℝ, ∀ (w : W.left)
        (hw : w ∈ (Opens.map (c.proj h₀ W).toLRSHom.base).obj
          (tube.{u} (N := 1) B ⊓ stdOpen.{u} n 1 i)),
        (c.proj h₀ W).toLRSHom.base w ∈ U → ‖evalFun (gVal (comp σ i j)) w‖ ≤ C := by
    intro p hp
    obtain ⟨i, hi⟩ : ∃ i, p ∈ stdOpen.{u} n 1 i := by
      rcases exists_chartPt p with ⟨q, rfl⟩ | ⟨q, rfl⟩
      exacts [⟨0, chartPt_mem_stdOpen 0 q⟩, ⟨1, chartPt_mem_stdOpen 1 q⟩]
    have hpT : p ∈ tube.{u} (N := 1) B ⊓ stdOpen.{u} n 1 i := by
      refine ⟨?_, hi⟩
      rw [SetLike.mem_coe, mem_tube, baseY_of_mem_tubeCompact hp]
      exact hxB
    have hpD : p ∈ removed N₀ := by
      change ofBase (baseY p) ∉ N₀
      rw [baseY_of_mem_tubeCompact hp]
      exact hxN
    obtain ⟨M, hM, C, hC⟩ := gVal_mem (comp σ i j) p hpT hpD
    obtain ⟨U, hUM, hUo, hpU⟩ := mem_nhds_iff.1 hM
    refine ⟨i, U ∩ ((tube.{u} (N := 1) B ⊓ stdOpen.{u} n 1 i :
      (relProjectiveSpaceAn.{u} n 1).Opens) : Set _),
      hUo.inter (Opens.isOpen _), ⟨hpU, hpT⟩, Set.inter_subset_right, C, fun w hw hwU ↦ ?_⟩
    rw [evalFun_of_mem _ hw]
    exact hC w hw (hUM hwU.1)
  choose! ι U hUo hpU hUsub C hC using hloc
  obtain ⟨t, htK, htf, hcov⟩ := (isCompact_tubeCompact.{u} (Complex.isCompact_closedBox a a))
    |>.elim_finite_subcover_image hUo fun p hp ↦ Set.mem_biUnion hp (hpU p hp)
  let O : (relProjectiveSpaceAn.{u} n 1).Opens :=
    ⟨⋃ p ∈ t, U p, isOpen_biUnion fun p hp ↦ hUo p (htK hp)⟩
  obtain ⟨a', b', hab', -, htube⟩ := exists_openBox_tube_subset (O := O) hcov isOpen_univ
    (Set.subset_univ _)
  have hcτ : ContinuousAt c.τ x :=
    c.differentiableOn_τ.continuousOn.continuousAt (N.isOpen.mem_nhds hxN')
  have hcω : ContinuousAt c.ω x :=
    c.differentiableOn_ω.continuousOn.continuousAt (N.isOpen.mem_nhds hxN')
  set A := ‖c.τ x‖ + ‖c.ω x‖ + 1
  have hM : {x' : Cn.{u} n | baseCoord x' ∈ Complex.openBox a' b'} ∩
      {x' | ‖c.τ x'‖ < A} ∩ {x' | ‖c.ω x'‖ < A} ∈ 𝓝 x := by
    refine inter_mem (inter_mem ?_ ?_) ?_
    · exact continuous_baseCoord.continuousAt.preimage_mem_nhds
        ((isOpen_openBox a' b').mem_nhds (hab' (mem_closedBox_self_iff.2 rfl)))
    · exact hcτ.norm.preimage_mem_nhds (Iio_mem_nhds (by linarith [norm_nonneg (c.ω x)]))
    · exact hcω.norm.preimage_mem_nhds (Iio_mem_nhds (by linarith [norm_nonneg (c.τ x)]))
  refine ⟨_, hM, ∑ p ∈ htf.toFinset, A ^ k * ‖C p‖, fun w hwM hwV ↦ ?_⟩
  have hwO : (c.proj h₀ W).toLRSHom.base w ∈ O := by
    refine htube ?_
    change baseY ((c.proj h₀ W).toLRSHom.base w) ∈ Complex.openBox a' b'
    rw [proj_base, baseY_blowupPt]
    exact hwM.1.1
  obtain ⟨p, hpt, hwp⟩ := Set.mem_iUnion₂.1 hwO
  have hw' : w ∈ (Opens.map (c.proj h₀ W).toLRSHom.base).obj
      (tube.{u} (N := 1) B ⊓ stdOpen.{u} n 1 (ι p)) := hUsub p (htK hpt) hwp
  have hθ : ∀ i, ‖c.θ i (pt W w)‖ ≤ A := by
    intro i
    fin_cases i
    exacts [hwM.1.2.le, hwM.2.le]
  rw [pushFun_eq σ (ι p) j hw', norm_mul, norm_pow]
  refine le_trans ?_ (Finset.single_le_sum (f := fun p ↦ A ^ k * ‖C p‖)
    (fun _ _ ↦ by positivity) (htf.mem_toFinset.2 hpt))
  exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hθ _) k)
    ((hC p (htK hpt) w hw' hwp).trans (le_abs_self _)) (norm_nonneg _) (by positivity)

variable (h₀) in
/-- **The section `τᵏ g₀ⱼ = θᵢᵏ gᵢⱼ` of `𝒜` over `B`.** -/
def pushSec (j : I) : (boundedModule h₀ W).val.obj (op (overBox N B)) :=
  (exists_secVal_eq h₀ W (isHolOn_pushFun σ j) (isBddOn_pushFun σ j)).choose

lemma evalFun_pushSec (j : I) {w : W.left} (hw : w ∈ preim h₀ W (overBox N B)) :
    evalFun (secVal h₀ W (pushSec h₀ σ j)) w = pushFun σ j w :=
  (exists_secVal_eq h₀ W (isHolOn_pushFun σ j) (isBddOn_pushFun σ j)).choose_spec w hw

/-! ### Generation off the centre -/

variable (c) in
/-- The open `{y ∈ V | θᵢ(y) ≠ 0}` of `N`. -/
def nzOpens (i : Fin 2) (V : (space N).Opens) : (space N).Opens :=
  ⟨{y | y ∈ V ∧ c.θ i y.1 ≠ 0}, by
    have hc : Continuous fun y : space N ↦ c.θ i y.1 :=
      (c.differentiableOn_θ i).continuousOn.comp_continuous continuous_subtype_val fun y ↦ y.2
    exact V.isOpen.inter (isOpen_ne_fun hc continuous_const)⟩

lemma mem_img_nzOpens {i : Fin 2} {V : (space N).Opens} {x : Cn.{u} n} :
    x ∈ img (c.nzOpens i V) ↔ x ∈ img V ∧ c.θ i x ≠ 0 := by
  rw [mem_img_iff, mem_img_iff]
  exact ⟨fun ⟨h, h', h''⟩ ↦ ⟨⟨h, h'⟩, h''⟩, fun ⟨⟨h, h'⟩, h''⟩ ↦ ⟨h, h', h''⟩⟩

lemma nzOpens_le (i : Fin 2) (V : (space N).Opens) : c.nzOpens i V ≤ V :=
  fun _ h ↦ h.1

variable [Fintype I]

/-- **The `sⱼ` generate `𝒜` near every point off the centre.** Let `y` be a point of `B` with
`θᵢ(y) ≠ 0` and `a` a section of `𝒜` near `y`. Then `θᵢ⁻ᵏ a` is a section of `𝒢 = 𝒢(k)` over
the chart `i`; near `(y, [τ(y) : ω(y)])` it is a combination of the `σⱼ`, and multiplying by
`θᵢᵏ` writes `a` as a combination of the `sⱼ` near `y`. -/
theorem exists_span_pushSec (hσ : GeneratesLocally σ) {y : space N} (i : Fin 2)
    (hy : c.θ i y.1 ≠ 0) {V₁ : (space N).Opens} (hV₁ : V₁ ≤ overBox N B) (hyV₁ : y ∈ V₁)
    (a : (boundedModule h₀ W).val.obj (op V₁)) :
    ∃ (V₂ : (space N).Opens) (h : V₂ ≤ V₁), y ∈ V₂ ∧
      ∃ f : I → (space N).presheaf.obj (op V₂), sectRes (boundedModule h₀ W) h a =
        ∑ j, f j • sectRes (boundedModule h₀ W) (h.trans hV₁) (pushSec h₀ σ j) := by
  set G := img (c.nzOpens i V₁)
  let O : (relProjectiveSpaceAn.{u} n 1).Opens := tube.{u} (N := 1) (baseOpens G) ⊓ stdOpen n 1 i
  have hOB : O ≤ tube.{u} (N := 1) B := fun p hp ↦ by
    obtain ⟨hN, hV, -⟩ := mem_img_iff.1 hp.1
    exact hV₁ hV
  have hGN : ∀ x ∈ G, x ∈ N ∧ c.θ i x ≠ 0 := fun x hx ↦
    ⟨img_le _ x (mem_img_nzOpens.1 hx).1, (mem_img_nzOpens.1 hx).2⟩
  have hρO : ∀ w, w ∈ (Opens.map (c.proj h₀ W).toLRSHom.base).obj O ↔ pt W w ∈ G := by
    intro w
    rw [mem_proj_preimage]
    constructor
    · rintro ⟨h₁, -⟩
      change ofBase (baseY (c.blowupPt (pt W w))) ∈ G at h₁
      rwa [baseY_blowupPt] at h₁
    · intro h
      refine ⟨show ofBase (baseY (c.blowupPt (pt W w))) ∈ G by rwa [baseY_blowupPt], ?_⟩
      rw [c.blowupPt_eq_chartPt i (c.τ_ne_zero _ (pt_mem W w)) (hGN _ h).2]
      exact chartPt_mem_stdOpen i _
  have hdiff : DifferentiableOn ℂ (fun x ↦ (c.θ i x)⁻¹ ^ k) G := fun x hx ↦
    ((((c.differentiableOn_θ i) x (hGN x hx).1).mono fun x' hx' ↦ (hGN x' hx').1).inv
      (hGN x hx).2).pow k
  -- the section `θᵢ⁻ᵏ a` of `𝒢`
  have hA : IsHolOn W (fun w ↦ (c.θ i (pt W w))⁻¹ ^ k * evalFun (secVal h₀ W a) w)
      ((Opens.map (c.proj h₀ W).toLRSHom.base).obj O) :=
    (isHolOn_comp_pt G.isOpen hdiff fun w hw ↦ (hρO w).1 hw).mul
      ((isHolOn_secVal h₀ W a).mono fun w hw ↦ (mem_preim_iff h₀ W).2
        (img_mono (c.nzOpens_le i V₁) ((hρO w).1 hw)))
  obtain ⟨s', hs'⟩ := hA.exists_eval_eq
  have hs'b : IsBoundedNear (c.proj h₀ W) (removed N₀) s' := by
    intro p hp hpD
    have hxG : ofBase (baseY p) ∈ G := hp.1
    obtain ⟨M, hM, C, hC⟩ := isBddOn_secVal h₀ W a (ofBase (baseY p))
      (img_mono (c.nzOpens_le i V₁) hxG) hpD
    have hc : ContinuousAt (fun x ↦ (c.θ i x)⁻¹ ^ k) (ofBase (baseY p)) :=
      hdiff.continuousOn.continuousAt (G.isOpen.mem_nhds hxG)
    refine ⟨(fun p ↦ ofBase (baseY p)) ⁻¹' (M ∩ {x | ‖(c.θ i x)⁻¹ ^ k‖ <
        ‖(c.θ i (ofBase (baseY p)))⁻¹ ^ k‖ + 1}),
      (continuous_ofBase.comp continuous_baseY).continuousAt.preimage_mem_nhds
        (inter_mem hM (hc.norm.preimage_mem_nhds (Iio_mem_nhds (lt_add_one _)))),
      (‖(c.θ i (ofBase (baseY p)))⁻¹ ^ k‖ + 1) * C, fun w hw hwM ↦ ?_⟩
    have e : ofBase (baseY ((c.proj h₀ W).toLRSHom.base w)) = pt W w := by
      rw [proj_base, baseY_blowupPt, ofBase_baseCoord]
    rw [Set.mem_preimage, e] at hwM
    rw [hs' w hw, norm_mul]
    exact mul_le_mul hwM.2.le (hC w hwM.1 (img_mono (c.nzOpens_le i V₁) ((hρO w).1 hw)))
      (norm_nonneg _) (by positivity)
  -- its expression in terms of the `σⱼ`
  let τ' := (modTwistSectionsEquiv (N := c.module h₀ W) (twistModCocycle.{u} n 1 k) i
    (inf_le_right : O ≤ stdOpen.{u} n 1 i)).symm (mkG h₀ c W s' hs'b)
  have hp₀ : chartPt.{u} i (baseCoord y.1, c.ζ i y.1) ∈ O := by
    refine ⟨?_, chartPt_mem_stdOpen i _⟩
    change ofBase (baseY (chartPt.{u} i (baseCoord y.1, c.ζ i y.1))) ∈ G
    rw [baseY_chartPt, ofBase_baseCoord]
    exact mem_img_iff.2 ⟨y.2, hyV₁, hy⟩
  obtain ⟨W'', hW''O, hp₀W'', d, hd⟩ := hσ O hOB τ' _ hp₀
  have hW''i : W'' ≤ stdOpen.{u} n 1 i := hW''O.trans inf_le_right
  have hd' := congrArg (modTwistSectionsEquiv (N := c.module h₀ W) (twistModCocycle.{u} n 1 k) i
    hW''i) hd
  rw [modTwistSectionsEquiv_res _ i inf_le_right hW''O, LinearEquiv.apply_symm_apply,
    map_sum] at hd'
  simp only [LinearEquiv.map_smul] at hd'
  have e (j : I) : modTwistSectionsEquiv (N := c.module h₀ W) (twistModCocycle.{u} n 1 k) i hW''i
      (modRes (σ j) W'' (hW''O.trans hOB)) =
      modRes (comp σ i j) W'' (le_inf (hW''O.trans hOB) hW''i) := by
    rw [comp, ← modTwistSectionsEquiv_res, modRes_res]
  simp only [e] at hd'
  -- the coefficients, in the coordinates of the chart `i`
  let S : Opens ((Fin n → ℂ) × ℂ) :=
    ⟨chartPt.{u} i ⁻¹' W'', W''.isOpen.preimage (isOpenEmbedding_chartPt i).continuous⟩
  have hSW : chartBox.{u} i S ≤ W'' := by
    rintro _ ⟨q, hq, rfl⟩
    exact hq
  let d' : I → (relProjectiveSpaceAn.{u} n 1).presheaf.obj (op (chartBox.{u} i S)) :=
    fun j ↦ TopCat.Presheaf.restrictOpen (d j) _ hSW
  have hcont : ContinuousOn (fun y' : space N ↦ ((baseCoord y'.1, c.ζ i y'.1) :
      (Fin n → ℂ) × ℂ)) (c.nzOpens i V₁) :=
    (continuous_baseCoord.comp continuous_subtype_val).continuousOn.prodMk
      ((c.differentiableOn_ζ i).continuousOn.comp continuous_subtype_val.continuousOn
        fun y' hy' ↦ ⟨y'.2, hy'.2⟩)
  let V₂ : (space N).Opens := ⟨c.nzOpens i V₁ ∩ (fun y' : space N ↦
      ((baseCoord y'.1, c.ζ i y'.1) : (Fin n → ℂ) × ℂ)) ⁻¹' S,
    hcont.isOpen_inter_preimage (c.nzOpens i V₁).isOpen S.isOpen⟩
  have hV₂V₁ : V₂ ≤ V₁ := fun y' hy' ↦ hy'.1.1
  have hV₂ : ∀ x ∈ img V₂, x ∈ N ∧ c.θ i x ≠ 0 ∧ x ∈ img V₁ ∧
      ((baseCoord x, c.ζ i x) : (Fin n → ℂ) × ℂ) ∈ S := by
    intro x hx
    obtain ⟨hxN, ⟨hxV₁, hθ⟩, hxS⟩ := mem_img_iff.1 hx
    exact ⟨hxN, hθ, mem_img_iff.2 ⟨hxN, hxV₁⟩, hxS⟩
  have hfd (j : I) : DifferentiableOn ℂ
      (fun x ↦ chartFun i (d' j) ((baseCoord x, c.ζ i x) : (Fin n → ℂ) × ℂ)) (img V₂) :=
    (differentiableOn_chartFun i (d' j)).comp
      (differentiable_baseCoord.differentiableOn.prodMk ((c.differentiableOn_ζ i).mono
        fun x hx ↦ ⟨(hV₂ x hx).1, (hV₂ x hx).2.1⟩)) fun x hx ↦ (hV₂ x hx).2.2.2
  refine ⟨V₂, hV₂V₁, ⟨⟨hyV₁, hy⟩, hp₀W''⟩, fun j ↦ OkaRing.ofDifferentiableOn _ (hfd j), ?_⟩
  -- compare the values
  refine secVal_ext h₀ W fun w hw ↦ ?_
  obtain ⟨-, hθw, hwV₁, hwS⟩ := hV₂ _ ((mem_preim_iff h₀ W).1 hw)
  have hwG : pt W w ∈ G := mem_img_nzOpens.2 ⟨hwV₁, hθw⟩
  have hwO : w ∈ (Opens.map (c.proj h₀ W).toLRSHom.base).obj O := (hρO w).2 hwG
  have hρw : (c.proj h₀ W).toLRSHom.base w = chartPt.{u} i (baseCoord (pt W w), c.ζ i (pt W w)) :=
    (c.proj_base h₀ W w).trans (c.blowupPt_eq_chartPt i (c.τ_ne_zero _ (pt_mem W w)) hθw)
  have hwW'' : w ∈ (Opens.map (c.proj h₀ W).toLRSHom.base).obj W'' := by
    change (c.proj h₀ W).toLRSHom.base w ∈ W''
    rw [hρw]
    exact hwS
  have hwB : w ∈ preim h₀ W (overBox N B) := (mem_preim_iff h₀ W).2 (img_mono hV₁ hwV₁)
  have hv := congrArg (fun s ↦ evalFun (gVal s) w) hd'
  simp only [evalFun_gVal_modRes _ _ hwW'', evalFun_gVal_sum _ _ hwW'',
    evalFun_gVal_smul _ _ hwW''] at hv
  rw [gVal_mkG, evalFun_of_mem _ hwO, hs' w hwO] at hv
  rw [evalFun_secVal_sectRes _ _ hw, evalFun_secVal_sum_smul _ _ _ hw]
  have hterm (j : I) : holFun (OkaRing.ofDifferentiableOn _ (hfd j) :
        (space N).presheaf.obj (op V₂)) (pt W w) *
      evalFun (secVal h₀ W (sectRes (boundedModule h₀ W) (hV₂V₁.trans hV₁) (pushSec h₀ σ j))) w =
      c.θ i (pt W w) ^ k * ((relProjectiveSpaceAn.{u} n 1).eval
        ((c.proj h₀ W).toLRSHom.base w) hwW'' (d j) * evalFun (gVal (comp σ i j)) w) := by
    rw [holFun_ofDifferentiableOn (hfd j) ((mem_preim_iff h₀ W).1 hw),
      evalFun_secVal_sectRes _ _ hw, evalFun_pushSec σ j hwB,
      pushFun_eq σ i j (mem_proj_tube_of_mem_preim hwB i (by
        rw [c.blowupPt_eq_chartPt i (c.τ_ne_zero _ (pt_mem W w)) hθw]
        exact chartPt_mem_stdOpen i _)),
      eval_proj_base _ hwW'' i hθw, chartFun_restrictOpen i hSW _ ⟨_, hwS, rfl⟩]
    ring
  rw [Finset.sum_congr rfl fun j _ ↦ hterm j, ← Finset.mul_sum, ← hv, ← mul_assoc, ← mul_pow,
    mul_inv_cancel₀ hθw, one_pow, one_mul]

/-- **Freeness in the span of the `sⱼ`** at a point `y ∈ B ∖ C` near which `𝒜` is free. -/
theorem isFreeSpanAt_pushSec (hσ : GeneratesLocally σ) {m : ℕ} (e : I ≃ Fin m)
    {y : space N} (hyB : y ∈ overBox N B) (hyC : y.1 ∉ c.centre) {U₂ : (space N).Opens}
    {m₂ : ℕ} {b₀ : Fin m₂ → (boundedModule h₀ W).val.obj (op U₂)}
    (hfree : IsFreeSpanAt h₀ W b₀ y) :
    IsFreeSpanAt h₀ W (fun j ↦ pushSec h₀ σ (e.symm j)) y := by
  obtain ⟨i, hi⟩ := exists_θ_ne_zero hyC
  obtain ⟨Ve, -, r, b, -, hyVe, -, hspan, hindep⟩ := hfree
  let V' := Ve ⊓ overBox N B
  have hV'e : V' ≤ Ve := inf_le_left
  have hV'B : V' ≤ overBox N B := inf_le_right
  let b' : Fin r → (boundedModule h₀ W).val.obj (op V') :=
    fun l ↦ sectRes (boundedModule h₀ W) hV'e (b l)
  have hloc (l : Fin r) := exists_span_pushSec σ hσ i hi hV'B ⟨hyVe, hyB⟩ (b' l)
  choose V₂ hV₂ hyV₂ f hf using hloc
  let V'' : (space N).Opens := V' ⊓ ⟨⋂ l, (V₂ l : Set (space N)),
    isOpen_iInter_of_finite fun l ↦ (V₂ l).isOpen⟩
  have hV''V' : V'' ≤ V' := inf_le_left
  have hV''₂ (l : Fin r) : V'' ≤ V₂ l := fun y' hy' ↦ Set.mem_iInter.1 hy'.2 l
  refine isFreeSpanAt_of_basis hV'B b' (fun V₃ h a ↦ ?_) (fun V₃ h c' hc' ↦ ?_) hV''V'
    ⟨⟨hyVe, hyB⟩, Set.mem_iInter.2 hyV₂⟩
    (fun l j ↦ (space N).res (hV''₂ l) (f l (e.symm j))) fun l ↦ ?_
  · obtain ⟨c', hc'⟩ := hspan V₃ (h.trans hV'e) a
    exact ⟨c', by simpa only [b', sectRes_sectRes] using hc'⟩
  · exact hindep V₃ (h.trans hV'e) c' (by simpa only [b', sectRes_sectRes] using hc')
  · have h₁ := congrArg (sectRes (boundedModule h₀ W) (hV''₂ l)) (hf l)
    rw [sectRes_sectRes, sectRes_sum] at h₁
    simp only [sectRes_smul, sectRes_sectRes] at h₁
    rw [h₁]
    exact (Equiv.sum_comp e.symm fun j ↦ (space N).res (hV''₂ l) (f l j) •
      sectRes (boundedModule h₀ W) (hV''V'.trans hV'B) (pushSec h₀ σ j)).symm

end BlowupData

/-! ### Pushing down generators -/

namespace BlowupData

variable {n : ℕ} {N N₀ : (AnalyticSpace.complexAffineSpace.{u} n).Opens} {h₀ : N₀ ≤ N}
  {c : BlowupData N N₀} {W : FiniteEtaleOver (space N₀)}

/-- **Pushing down generators along the blow-up of `C = {τ = ω = 0}`.** Suppose that the sheaf
`𝒢` on `P^an = ℂⁿ × ℙ¹` (the bounded sections on the blow-up) is coherent over `U × ℙ¹` and that
`𝒜` is free near every point of `U ∖ C`. Then every point `y₀` over `U` has an open
neighbourhood `V` with finitely many sections `s` of `𝒜` over `V` such that near every point of
`V ∖ C` the sheaf `𝒜` is free with a basis in the span of `s`. -/
theorem exists_isFreeSpanAt {U : Opens (Fin n → ℂ)}
    (h𝒢 : (((relProjectiveSpaceAn.{u} n 1).toLocallyRingedSpace.restrictModules
      (tube.{u} (N := 1) U)).obj (c.module h₀ W)).IsCoherent)
    (hfree : ∀ y : space N, baseCoord y.1 ∈ U → y.1 ∉ c.centre →
      ∃ (U₂ : (space N).Opens) (m₂ : ℕ) (b : Fin m₂ → (boundedModule h₀ W).val.obj (op U₂)),
        IsFreeSpanAt h₀ W b y)
    {y₀ : space N} (hy₀ : baseCoord y₀.1 ∈ U) :
    ∃ (V : (space N).Opens) (m : ℕ) (s : Fin m → (boundedModule h₀ W).val.obj (op V)),
      y₀ ∈ V ∧ ∀ y ∈ V, y.1 ∉ c.centre → IsFreeSpanAt h₀ W s y := by
  set a := baseCoord y₀.1
  have ha : a ∈ Complex.closedBox a a := mem_closedBox_self_iff.2 rfl
  have hK : Complex.closedBox a a ⊆ U := fun z hz ↦ by
    rw [mem_closedBox_self_iff.1 hz]
    exact hy₀
  obtain ⟨n₀, hn₀⟩ := exists_finite_generates_twistMod (c.module h₀ W) h𝒢 hK ⟨a, ha⟩
  obtain ⟨a', b', hab', hBU, I, hI, σ, hσ⟩ := hn₀ n₀.toNat (Int.self_le_toNat n₀)
  let e := Fintype.equivFin I
  refine ⟨overBox N (boxOpens a' b'), Fintype.card I, fun j ↦ pushSec h₀ σ (e.symm j),
    hab' ha, fun y hy hyC ↦ ?_⟩
  obtain ⟨U₂, m₂, b, hb⟩ := hfree y (hBU hy) hyC
  exact isFreeSpanAt_pushSec σ hσ e hy hyC hb

end BlowupData

/-! ### The blow-up of `{t = 0, w = φ}` -/

namespace BlowupCentre

variable {n : ℕ} {N N₀ : (AnalyticSpace.complexAffineSpace.{u} n).Opens} {h₀ : N₀ ≤ N}
  (C : BlowupCentre N N₀) {W : FiniteEtaleOver (space N₀)}

/-- **Pushing down generators along the blow-up of `C = {t = 0, w = φ}`, from the charts.** Let
`W₁`, `W₂` be the pullbacks of `W` to the two charts of the blow-up (e.g.
`ComplexAnalytic.BoundedSections.mapCover`). If the sheaves of bounded sections of `W₁` and `W₂`
are coherent and `𝒜` is free near every point of `N ∖ C`, then every point of `N` has an open
neighbourhood `V` with finitely many sections `s` of `𝒜` over `V` such that near every point of
`V ∖ C` the sheaf `𝒜` is free with a basis in the span of `s`. -/
theorem exists_isFreeSpanAt {W₁ : FiniteEtaleOver (space (C.M₁₀ h₀))}
    {W₂ : FiniteEtaleOver (space (C.M₂₀ h₀))} {β₁ : W₁.left → W.left} {β₂ : W₂.left → W.left}
    (hβ₁ : IsMapPullback (C.chart₁Map h₀) W W₁ β₁) (hβ₂ : IsMapPullback (C.chart₂Map h₀) W W₂ β₂)
    (h₁ : (boundedModule (C.M₁₀_le h₀) W₁).IsCoherent)
    (h₂ : (boundedModule (C.M₂₀_le h₀) W₂).IsCoherent)
    (hfree : ∀ y : space N, y.1 ∉ C.toBlowupData.centre →
      ∃ (U₂ : (space N).Opens) (m₂ : ℕ) (b : Fin m₂ → (boundedModule h₀ W).val.obj (op U₂)),
        IsFreeSpanAt h₀ W b y)
    (y₀ : space N) :
    ∃ (V : (space N).Opens) (m : ℕ) (s : Fin m → (boundedModule h₀ W).val.obj (op V)),
      y₀ ∈ V ∧ ∀ y ∈ V, y.1 ∉ C.toBlowupData.centre → IsFreeSpanAt h₀ W s y :=
  C.toBlowupData.exists_isFreeSpanAt (C.isCoherent_module hβ₁ hβ₂ h₁ h₂)
    (fun y _ hy ↦ hfree y hy) (show ofBase (baseCoord y₀.1) ∈ N from y₀.2)


variable (h₀) in
/-- The first chart is biholomorphic off the exceptional divisor `t = 0`. -/
def chart₁Biholo : ChartBiholo (C.chart₁Map h₀) C.M₁ N where
  D := {x | x ∈ C.M₁ ∧ x C.it ≠ 0}
  E := {y | y ∈ N ∧ y C.it ≠ 0}
  isOpen_D := C.M₁.isOpen.inter (isOpen_ne_fun (continuous_apply _) continuous_const)
  isOpen_E := N.isOpen.inter (isOpen_ne_fun (continuous_apply _) continuous_const)
  D_sub _ hx := hx.1
  E_sub _ hy := hy.1
  E_sub_R _ hy := ⟨mem_cyl_of_mem hy.1, hy.2⟩
  mapsTo x hx := ⟨C.ch₁_mem_of_mem_M₁ hx.1, by
    change C.ch₁ x C.it ≠ 0
    rw [ch₁_it]
    exact hx.2⟩
  inv_mem y hy := ⟨show C.ch₁ (C.ch₁Inv y) ∈ N by rw [C.ch₁_ch₁Inv hy.2]; exact hy.1, by
    change Function.update y C.iw _ C.it ≠ 0
    rw [Function.update_of_ne C.it_ne_iw]
    exact hy.2⟩
  inv_χ _ hx := C.ch₁Inv_ch₁ hx.2
  χ_inv _ hy := C.ch₁_ch₁Inv hy.2
  differentiableOn_χ := C.differentiableOn_ch₁.mono fun _ hx ↦ C.M₁_le_cyl hx.1
  differentiableOn_χInv := C.differentiableOn_ch₁Inv.mono fun _ hy ↦ ⟨mem_cyl_of_mem hy.1, hy.2⟩

variable (h₀) in
/-- The second chart is biholomorphic off the exceptional divisor `s = 0`. -/
def chart₂Biholo : ChartBiholo (C.chart₂Map h₀) C.M₂ N where
  D := {a | a ∈ C.M₂ ∧ a C.it ≠ 0}
  E := {y | y ∈ N ∧ y C.iw - C.φ y ≠ 0}
  isOpen_D := C.M₂.isOpen.inter (isOpen_ne_fun (continuous_apply _) continuous_const)
  isOpen_E := by
    have hc : ContinuousOn (fun y ↦ y C.iw - C.φ y) {y : Cn.{u} n | y ∈ N} :=
      (continuous_apply C.iw).continuousOn.sub
        (C.differentiableOn_φ.continuousOn.mono fun _ hy ↦ mem_cyl_of_mem hy)
    exact hc.isOpen_inter_preimage N.isOpen isOpen_compl_singleton
  D_sub _ ha := ha.1
  E_sub _ hy := hy.1
  E_sub_R _ hy := ⟨mem_cyl_of_mem hy.1, hy.2⟩
  mapsTo a ha := ⟨show C.ch₂ a ∈ N from ha.1, by
    change C.ch₂ a C.iw - C.φ (C.ch₂ a) ≠ 0
    rw [ch₂_iw, φ_ch₂, add_sub_cancel_left]
    exact ha.2⟩
  inv_mem y hy := ⟨show C.ch₂ (C.ch₂Inv y) ∈ N by rw [C.ch₂_ch₂Inv hy.2]; exact hy.1, by
    change Function.update (Function.update y C.it _) C.iw _ C.it ≠ 0
    rw [Function.update_of_ne C.it_ne_iw, Function.update_self]
    exact hy.2⟩
  inv_χ _ ha := C.ch₂Inv_ch₂ ha.2
  χ_inv _ hy := C.ch₂_ch₂Inv hy.2
  differentiableOn_χ := C.differentiableOn_ch₂.mono fun _ ha ↦ C.M₂_le_dom₂ ha.1
  differentiableOn_χInv := C.differentiableOn_ch₂Inv.mono fun _ hy ↦ ⟨mem_cyl_of_mem hy.1, hy.2⟩

/-- **Freeness of `𝒜` off the centre from the charts**: if the bounded sections of `W₁` are free
off `t = 0` and those of `W₂` are free off `s = 0`, then `𝒜` is free near every point of
`N ∖ C`. -/
theorem exists_isFreeSpanAt_of_not_mem_centre {W₁ : FiniteEtaleOver (space (C.M₁₀ h₀))}
    {W₂ : FiniteEtaleOver (space (C.M₂₀ h₀))} {β₁ : W₁.left → W.left} {β₂ : W₂.left → W.left}
    (hβ₁ : IsMapPullback (C.chart₁Map h₀) W W₁ β₁) (hβ₂ : IsMapPullback (C.chart₂Map h₀) W W₂ β₂)
    (hfree₁ : ∀ x : space C.M₁, x.1 C.it ≠ 0 →
      ∃ (U₂ : (space C.M₁).Opens) (m₂ : ℕ) (b : Fin m₂ →
        (boundedModule (C.M₁₀_le h₀) W₁).val.obj (op U₂)), IsFreeSpanAt (C.M₁₀_le h₀) W₁ b x)
    (hfree₂ : ∀ a : space C.M₂, a.1 C.it ≠ 0 →
      ∃ (U₂ : (space C.M₂).Opens) (m₂ : ℕ) (b : Fin m₂ →
        (boundedModule (C.M₂₀_le h₀) W₂).val.obj (op U₂)), IsFreeSpanAt (C.M₂₀_le h₀) W₂ b a)
    (y : space N) (hy : y.1 ∉ C.toBlowupData.centre) :
    ∃ (U₂ : (space N).Opens) (m₂ : ℕ) (b : Fin m₂ → (boundedModule h₀ W).val.obj (op U₂)),
      IsFreeSpanAt h₀ W b y := by
  by_cases ht : y.1 C.it = 0
  · have hω : y.1 C.iw - C.φ y.1 ≠ 0 := fun h ↦ hy ⟨ht, h⟩
    have hyE : y.1 ∈ (C.chart₂Biholo h₀).E := ⟨y.2, hω⟩
    have ha := (C.chart₂Biholo h₀).inv_mem _ hyE
    obtain ⟨U₂, m₂, b, hb⟩ := hfree₂ ⟨_, ha.1⟩ ha.2
    obtain ⟨U, r, e, he⟩ := (C.chart₂Biholo h₀).isFreeSpanAt (h₀ := h₀) hβ₂ (x := ⟨_, ha.1⟩) ha hb
    refine ⟨U, r, e, ?_⟩
    convert he using 1
    exact Subtype.ext ((C.chart₂Biholo h₀).χ_inv _ hyE).symm
  · have hyE : y.1 ∈ (C.chart₁Biholo h₀).E := ⟨y.2, ht⟩
    have hx := (C.chart₁Biholo h₀).inv_mem _ hyE
    obtain ⟨U₂, m₂, b, hb⟩ := hfree₁ ⟨_, hx.1⟩ hx.2
    obtain ⟨U, r, e, he⟩ := (C.chart₁Biholo h₀).isFreeSpanAt (h₀ := h₀) hβ₁ (x := ⟨_, hx.1⟩) hx hb
    refine ⟨U, r, e, ?_⟩
    convert he using 1
    exact Subtype.ext ((C.chart₁Biholo h₀).χ_inv _ hyE).symm

/-- **Pushing down generators along the blow-up of `C = {t = 0, w = φ}`, from the charts
only.** Let `W₁`, `W₂` be the pullbacks of `W` to the two charts of the blow-up. If the sheaves of
bounded sections of `W₁` and `W₂` are coherent, and free off the exceptional divisor, then every
point of `N` has an open neighbourhood `V` with finitely many sections `s` of `𝒜` over `V` such
that near every point of `V ∖ C` the sheaf `𝒜` is free with a basis in the span of `s`. -/
theorem exists_isFreeSpanAt_of_charts {W₁ : FiniteEtaleOver (space (C.M₁₀ h₀))}
    {W₂ : FiniteEtaleOver (space (C.M₂₀ h₀))} {β₁ : W₁.left → W.left} {β₂ : W₂.left → W.left}
    (hβ₁ : IsMapPullback (C.chart₁Map h₀) W W₁ β₁) (hβ₂ : IsMapPullback (C.chart₂Map h₀) W W₂ β₂)
    (h₁ : (boundedModule (C.M₁₀_le h₀) W₁).IsCoherent)
    (h₂ : (boundedModule (C.M₂₀_le h₀) W₂).IsCoherent)
    (hfree₁ : ∀ x : space C.M₁, x.1 C.it ≠ 0 →
      ∃ (U₂ : (space C.M₁).Opens) (m₂ : ℕ) (b : Fin m₂ →
        (boundedModule (C.M₁₀_le h₀) W₁).val.obj (op U₂)), IsFreeSpanAt (C.M₁₀_le h₀) W₁ b x)
    (hfree₂ : ∀ a : space C.M₂, a.1 C.it ≠ 0 →
      ∃ (U₂ : (space C.M₂).Opens) (m₂ : ℕ) (b : Fin m₂ →
        (boundedModule (C.M₂₀_le h₀) W₂).val.obj (op U₂)), IsFreeSpanAt (C.M₂₀_le h₀) W₂ b a)
    (y₀ : space N) :
    ∃ (V : (space N).Opens) (m : ℕ) (s : Fin m → (boundedModule h₀ W).val.obj (op V)),
      y₀ ∈ V ∧ ∀ y ∈ V, y.1 ∉ C.toBlowupData.centre → IsFreeSpanAt h₀ W s y :=
  C.exists_isFreeSpanAt hβ₁ hβ₂ h₁ h₂
    (C.exists_isFreeSpanAt_of_not_mem_centre hβ₁ hβ₂ hfree₁ hfree₂) y₀

end BlowupCentre

end

end ComplexAnalytic.BoundedSections
