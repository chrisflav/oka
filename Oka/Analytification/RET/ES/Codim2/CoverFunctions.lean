/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.ES.Codim2.NormalCrossingsBasis

/-!
# Sections of `𝒜` given by their values

Keep the notation of `Oka/Analytification/RET/ES/BoundedSections.lean`: `p : W ⟶ N°` is a finite
étale cover, `N° ⊆ N ⊆ ℂⁿ`, and `𝒜` is the sheaf of sections of `p_* 𝒪_W` bounded near `N ∖ N°`.
Sections of `𝒪_W` are determined by their values, so a section of `𝒜` over `V` is the same as a
function `f` on `W` which is near every point of `p⁻¹(V)` a holomorphic function of the point
below (`ComplexAnalytic.BoundedSections.IsHolOn`) and which is bounded near every point of
`V ∖ N°` (`ComplexAnalytic.BoundedSections.IsBddOn`). This file provides the calculus of such
functions and the passage to sections (`ComplexAnalytic.BoundedSections.exists_secVal_eq`).

## Main definitions

- `ComplexAnalytic.BoundedSections.IsHolOn W f O`: `f` is locally a holomorphic function of the
  point below near every point of `O`.
- `ComplexAnalytic.BoundedSections.IsBddOn W V f`: `f` is bounded near every point of `V ∖ N°`.

## Main results

- `ComplexAnalytic.BoundedSections.exists_secVal_eq`: such a function is the value of a section of
  `𝒜`.
- `ComplexAnalytic.BoundedSections.secVal_ext`: sections of `𝒜` are determined by their values.
- `ComplexAnalytic.BoundedSections.IsHolOn.comp`: composition with a continuous map over a
  holomorphic map of the bases.
-/

open CategoryTheory Opposite AlgebraicGeometry Topology TopologicalSpace Filter

universe u

namespace ComplexAnalytic.BoundedSections

open AnalyticSpace

noncomputable section

variable {n : ℕ} {N N₀ : (AnalyticSpace.complexAffineSpace.{u} n).Opens}

/-! ### Holomorphic functions on `W` -/

section Hol

variable (W : FiniteEtaleOver (space N₀))

/-- **`f` is holomorphic on `O`**: near every point of `O` it is a holomorphic function of the point
below. -/
def IsHolOn (f : W.left → ℂ) (O : Set W.left) : Prop :=
  ∀ w ∈ O, ∃ F : Cn.{u} n → ℂ, ∀ᶠ w' in 𝓝 w, DifferentiableAt ℂ F (pt W w') ∧ f w' = F (pt W w')

variable {W}

/-- The values of a section of `𝒪_W` are holomorphic. -/
lemma isHolOn_evalFun {O : W.left.Opens} (a : W.left.presheaf.obj (op O)) :
    IsHolOn W (evalFun a) O := by
  intro w hw
  obtain ⟨O₁, hwO₁, -, hsheet⟩ := exists_sheet W w
  obtain ⟨F, hFd, hF⟩ := hsheet (O' := O₁ ⊓ O) inf_le_left
    (W.left.presheaf.map (homOfLE inf_le_right).op a)
  refine ⟨F, ?_⟩
  filter_upwards [(O₁ ⊓ O).isOpen.mem_nhds ⟨hwO₁, hw⟩] with w' hw'
  refine ⟨hFd w' hw', ?_⟩
  rw [evalFun_of_mem a hw'.2, ← hF w' hw', eval_presheaf_map]

/-- **A holomorphic function on an open `O` of `W` is the value of a section of `𝒪_W`.** -/
lemma IsHolOn.exists_eval_eq {f : W.left → ℂ} {O : W.left.Opens} (hf : IsHolOn W f O) :
    ∃ a : W.left.presheaf.obj (op O), ∀ w (hw : w ∈ O), W.left.eval w hw a = f w := by
  refine exists_eval_eq_of_local (isLocallyOpenInAffine_left W) f fun w hw ↦ ?_
  obtain ⟨F, hF⟩ := hf w hw
  obtain ⟨t, ht, hto, hwt⟩ := eventually_nhds_iff.1 hF
  obtain ⟨σ, hσ⟩ := exists_eval_eq_of_differentiableAt (O := O ⊓ ⟨t, hto⟩) W F
    fun w' hw' ↦ (ht w' hw'.2).1
  exact ⟨O ⊓ ⟨t, hto⟩, ⟨hw, hwt⟩, inf_le_left, σ, fun w' hw' ↦
    (hσ w' hw').trans (ht w' hw'.2).2.symm⟩

lemma IsHolOn.mono {f : W.left → ℂ} {O O' : Set W.left} (hf : IsHolOn W f O) (h : O' ⊆ O) :
    IsHolOn W f O' :=
  fun w hw ↦ hf w (h hw)

/-- Holomorphy is local: it only depends on the germs of `f` at the points of `O`. -/
lemma IsHolOn.congr {f g : W.left → ℂ} {O : Set W.left} (hf : IsHolOn W f O)
    (h : ∀ w ∈ O, f =ᶠ[𝓝 w] g) : IsHolOn W g O := by
  intro w hw
  obtain ⟨F, hF⟩ := hf w hw
  refine ⟨F, ?_⟩
  filter_upwards [hF, h w hw] with w' h₁ h₂
  exact ⟨h₁.1, h₂ ▸ h₁.2⟩

lemma IsHolOn.congr_of_isOpen {f g : W.left → ℂ} {O : Set W.left} (hO : IsOpen O)
    (hf : IsHolOn W f O) (h : Set.EqOn f g O) : IsHolOn W g O :=
  hf.congr fun _ hw ↦ Filter.eventuallyEq_of_mem (hO.mem_nhds hw) h

lemma IsHolOn.add {f g : W.left → ℂ} {O : Set W.left} (hf : IsHolOn W f O)
    (hg : IsHolOn W g O) : IsHolOn W (fun w ↦ f w + g w) O := by
  intro w hw
  obtain ⟨F, hF⟩ := hf w hw
  obtain ⟨G, hG⟩ := hg w hw
  refine ⟨fun x ↦ F x + G x, ?_⟩
  filter_upwards [hF, hG] with w' h₁ h₂
  exact ⟨h₁.1.add h₂.1, by rw [h₁.2, h₂.2]⟩

lemma IsHolOn.mul {f g : W.left → ℂ} {O : Set W.left} (hf : IsHolOn W f O)
    (hg : IsHolOn W g O) : IsHolOn W (fun w ↦ f w * g w) O := by
  intro w hw
  obtain ⟨F, hF⟩ := hf w hw
  obtain ⟨G, hG⟩ := hg w hw
  refine ⟨fun x ↦ F x * G x, ?_⟩
  filter_upwards [hF, hG] with w' h₁ h₂
  exact ⟨h₁.1.mul h₂.1, by rw [h₁.2, h₂.2]⟩

lemma isHolOn_const (c : ℂ) (O : Set W.left) : IsHolOn W (fun _ ↦ c) O :=
  fun _ _ ↦ ⟨fun _ ↦ c, Eventually.of_forall fun _ ↦ ⟨differentiableAt_const c, rfl⟩⟩

lemma IsHolOn.sum {ι : Type*} (t : Finset ι) {f : ι → W.left → ℂ} {O : Set W.left}
    (hf : ∀ i ∈ t, IsHolOn W (f i) O) : IsHolOn W (fun w ↦ ∑ i ∈ t, f i w) O := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using isHolOn_const 0 O
  | insert j t hj ih =>
    simp_rw [Finset.sum_insert hj]
    exact (hf j (Finset.mem_insert_self j t)).add
      (ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))

/-- A holomorphic function of the point below is holomorphic. -/
lemma isHolOn_comp_pt {F : Cn.{u} n → ℂ} {G : Set (Cn.{u} n)} (hG : IsOpen G)
    (hF : DifferentiableOn ℂ F G) {O : Set W.left} (hO : ∀ w ∈ O, pt W w ∈ G) :
    IsHolOn W (fun w ↦ F (pt W w)) O := by
  intro w hw
  refine ⟨F, ?_⟩
  filter_upwards [(continuous_pt W).continuousAt.preimage_mem_nhds (hG.mem_nhds (hO w hw))]
    with w' hw'
  exact ⟨hF.differentiableAt (hG.mem_nhds hw'), rfl⟩

lemma IsHolOn.continuousAt {f : W.left → ℂ} {O : Set W.left} (hf : IsHolOn W f O) {w : W.left}
    (hw : w ∈ O) : ContinuousAt f w := by
  obtain ⟨F, hF⟩ := hf w hw
  have hc : ContinuousAt (fun w' ↦ F (pt W w')) w :=
    hF.self_of_nhds.1.continuousAt.comp (continuous_pt W).continuousAt
  exact hc.congr (hF.mono fun _ h ↦ h.2.symm)

/-- **Composition along a continuous map over a holomorphic map of the bases.** -/
lemma IsHolOn.comp {m : ℕ} {M₀ : (AnalyticSpace.complexAffineSpace.{u} m).Opens}
    {W₁ : FiniteEtaleOver (space M₀)} {φ : W₁.left → W.left} {g : Cn.{u} m → Cn.{u} n}
    (hg : Differentiable ℂ g) (hpt : ∀ w, pt W (φ w) = g (pt W₁ w)) {f : W.left → ℂ}
    {O : Set W.left} (hf : IsHolOn W f O) {O₁ : Set W₁.left} (hφ : ∀ w ∈ O₁, ContinuousAt φ w)
    (hmaps : ∀ w ∈ O₁, φ w ∈ O) : IsHolOn W₁ (fun w ↦ f (φ w)) O₁ := by
  intro w hw
  obtain ⟨F, hF⟩ := hf (φ w) (hmaps w hw)
  refine ⟨fun x ↦ F (g x), ?_⟩
  filter_upwards [(hφ w hw).preimage_mem_nhds hF] with w' hw'
  have h₁ := hw'.1
  rw [hpt] at h₁
  exact ⟨h₁.comp _ (hg _), hw'.2.trans (by rw [hpt])⟩

end Hol

/-! ### Bounded functions -/

section Bdd

variable (W : FiniteEtaleOver (space N₀))

/-- **`f` is bounded near every point of `V ∖ N°`.** -/
def IsBddOn (V : (space N).Opens) (f : W.left → ℂ) : Prop :=
  ∀ x ∈ img V, x ∉ N₀ → ∃ M ∈ 𝓝 x, ∃ C, ∀ w, pt W w ∈ M → pt W w ∈ img V → ‖f w‖ ≤ C

variable {W}

lemma IsBddOn.add {V : (space N).Opens} {f g : W.left → ℂ} (hf : IsBddOn W V f)
    (hg : IsBddOn W V g) : IsBddOn W V (fun w ↦ f w + g w) := by
  intro x hx hxN
  obtain ⟨M, hM, C, hC⟩ := hf x hx hxN
  obtain ⟨M', hM', C', hC'⟩ := hg x hx hxN
  exact ⟨M ∩ M', inter_mem hM hM', C + C', fun w hw hwV ↦
    (norm_add_le _ _).trans (add_le_add (hC w hw.1 hwV) (hC' w hw.2 hwV))⟩

lemma IsBddOn.mul {V : (space N).Opens} {f g : W.left → ℂ} (hf : IsBddOn W V f)
    (hg : IsBddOn W V g) : IsBddOn W V (fun w ↦ f w * g w) := by
  intro x hx hxN
  obtain ⟨M, hM, C, hC⟩ := hf x hx hxN
  obtain ⟨M', hM', C', hC'⟩ := hg x hx hxN
  refine ⟨M ∩ M', inter_mem hM hM', max C 0 * max C' 0, fun w hw hwV ↦ ?_⟩
  rw [norm_mul]
  exact mul_le_mul ((hC w hw.1 hwV).trans (le_max_left _ _))
    ((hC' w hw.2 hwV).trans (le_max_left _ _)) (norm_nonneg _) (le_max_right _ _)

lemma isBddOn_const (V : (space N).Opens) (c : ℂ) : IsBddOn W V (fun _ ↦ c) :=
  fun _ _ _ ↦ ⟨Set.univ, univ_mem, ‖c‖, fun _ _ _ ↦ le_rfl⟩

lemma IsBddOn.sum {V : (space N).Opens} {ι : Type*} (t : Finset ι) {f : ι → W.left → ℂ}
    (hf : ∀ i ∈ t, IsBddOn W V (f i)) : IsBddOn W V (fun w ↦ ∑ i ∈ t, f i w) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using isBddOn_const (W := W) V 0
  | insert j t hj ih =>
    simp_rw [Finset.sum_insert hj]
    exact (hf j (Finset.mem_insert_self j t)).add
      (ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))

/-- A function of the point below which is continuous on `V` is bounded. -/
lemma isBddOn_comp_pt {V : (space N).Opens} {F : Cn.{u} n → ℂ}
    (hF : ContinuousOn F (img V)) : IsBddOn W V (fun w ↦ F (pt W w)) := by
  intro x hx _
  have hc : ContinuousAt F x := hF.continuousAt ((img V).isOpen.mem_nhds hx)
  obtain ⟨M, hM, hMb⟩ : ∃ M ∈ 𝓝 x, ∀ z ∈ M, ‖F z‖ ≤ ‖F x‖ + 1 := by
    refine ⟨_, hc.norm.preimage_mem_nhds (Iio_mem_nhds (lt_add_one ‖F x‖)), fun z hz ↦ ?_⟩
    exact (Set.mem_Iio.1 hz).le
  exact ⟨M, hM, ‖F x‖ + 1, fun w hw _ ↦ hMb _ hw⟩

lemma IsBddOn.mono {V V' : (space N).Opens} (h : V' ≤ V) {f : W.left → ℂ}
    (hf : IsBddOn W V f) : IsBddOn W V' f := by
  intro x hx hxN
  obtain ⟨M, hM, C, hC⟩ := hf x (img_mono h hx) hxN
  exact ⟨M, hM, C, fun w hw hwV ↦ hC w hw (img_mono h hwV)⟩

end Bdd

/-! ### Sections of `𝒜` by their values -/

section Sections

variable (h₀ : N₀ ≤ N) (W : FiniteEtaleOver (space N₀))

/-- The values of a section of `𝒜` are bounded. -/
lemma isBddOn_secVal {V : (space N).Opens} (a : (boundedModule h₀ W).val.obj (op V)) :
    IsBddOn W V (evalFun (secVal h₀ W a)) := by
  intro x hx hxN
  obtain ⟨M, hM, C, -, hC⟩ := exists_bound_of_mem_boundedSubring (secVal_mem h₀ W a) hx hxN
  exact ⟨M, hM, C, hC⟩

lemma isHolOn_secVal {V : (space N).Opens} (a : (boundedModule h₀ W).val.obj (op V)) :
    IsHolOn W (evalFun (secVal h₀ W a)) (preim h₀ W V) :=
  isHolOn_evalFun _

/-- **A bounded holomorphic function is the value of a section of `𝒜`.** -/
theorem exists_secVal_eq {V : (space N).Opens} {f : W.left → ℂ}
    (hf : IsHolOn W f (preim h₀ W V)) (hb : IsBddOn W V f) :
    ∃ a : (boundedModule h₀ W).val.obj (op V),
      ∀ w ∈ preim h₀ W V, evalFun (secVal h₀ W a) w = f w := by
  obtain ⟨σ, hσ⟩ := hf.exists_eval_eq
  have hσb : σ ∈ boundedSubring h₀ W V := by
    intro y hy hyD
    obtain ⟨M, hM, C, hC⟩ := hb y.1 (mem_img_iff.2 ⟨y.2, hy⟩) hyD
    refine ⟨Subtype.val ⁻¹' M, continuous_subtype_val.continuousAt.preimage_mem_nhds hM, C,
      fun w hw hwM ↦ ?_⟩
    have hpt : ((proj h₀ W).toLRSHom.base w).1 = pt W w := coe_proj_base h₀ W w
    rw [hσ w hw]
    refine hC w (hpt ▸ hwM) ((mem_preim_iff h₀ W).1 hw)
  exact ⟨mkSec h₀ W σ hσb, fun w hw ↦ by rw [secVal_mkSec, evalFun_of_mem σ hw, hσ w hw]⟩

/-- **Sections of `𝒜` are determined by their values.** -/
theorem secVal_ext {V : (space N).Opens} {a b : (boundedModule h₀ W).val.obj (op V)}
    (h : ∀ w ∈ preim h₀ W V, evalFun (secVal h₀ W a) w = evalFun (secVal h₀ W b) w) : a = b :=
  secVal_injective h₀ W (eq_of_forall_eval_eq (isLocallyOpenInAffine_left W) fun w hw ↦ by
    rw [← evalFun_of_mem _ hw, ← evalFun_of_mem _ hw, h w hw])

variable {h₀ W}

lemma evalFun_secVal_add {V : (space N).Opens} (a b : (boundedModule h₀ W).val.obj (op V))
    {w : W.left} (hw : w ∈ preim h₀ W V) :
    evalFun (secVal h₀ W (a + b)) w = evalFun (secVal h₀ W a) w + evalFun (secVal h₀ W b) w := by
  rw [secVal_add, evalFun_add W _ _ hw]

lemma evalFun_secVal_zero {V : (space N).Opens} {w : W.left} (hw : w ∈ preim h₀ W V) :
    evalFun (secVal h₀ W (0 : (boundedModule h₀ W).val.obj (op V))) w = 0 := by
  rw [secVal_zero, evalFun_of_mem _ hw, map_zero]

lemma evalFun_secVal_smul {V : (space N).Opens} (r : (space N).presheaf.obj (op V))
    (a : (boundedModule h₀ W).val.obj (op V)) {w : W.left} (hw : w ∈ preim h₀ W V) :
    evalFun (secVal h₀ W (r • a)) w = holFun r (pt W w) * evalFun (secVal h₀ W a) w := by
  rw [secVal_smul, evalFun_mul W _ _ hw, evalFun_pullback h₀ W _ hw]

lemma evalFun_secVal_sum {V : (space N).Opens} {ι : Type*} (t : Finset ι)
    (a : ι → (boundedModule h₀ W).val.obj (op V)) {w : W.left} (hw : w ∈ preim h₀ W V) :
    evalFun (secVal h₀ W (∑ i ∈ t, a i)) w = ∑ i ∈ t, evalFun (secVal h₀ W (a i)) w := by
  rw [secVal_sum, evalFun_of_mem _ hw, map_sum]
  simp_rw [← evalFun_of_mem _ hw]

lemma evalFun_secVal_sectRes {V V' : (space N).Opens} (h : V' ≤ V)
    (a : (boundedModule h₀ W).val.obj (op V)) {w : W.left} (hw : w ∈ preim h₀ W V') :
    evalFun (secVal h₀ W (LocallyRingedSpace.sectRes (boundedModule h₀ W) h a)) w =
      evalFun (secVal h₀ W a) w := by
  rw [secVal_map, evalFun_map W _ _ hw]

lemma evalFun_secVal_sum_smul {V : (space N).Opens} {ι : Type*} (t : Finset ι)
    (r : ι → (space N).presheaf.obj (op V)) (a : ι → (boundedModule h₀ W).val.obj (op V))
    {w : W.left} (hw : w ∈ preim h₀ W V) :
    evalFun (secVal h₀ W (∑ i ∈ t, r i • a i)) w =
      ∑ i ∈ t, holFun (r i) (pt W w) * evalFun (secVal h₀ W (a i)) w := by
  rw [evalFun_secVal_sum t _ hw]
  exact Finset.sum_congr rfl fun i _ ↦ evalFun_secVal_smul _ _ hw

end Sections

end

end ComplexAnalytic.BoundedSections
