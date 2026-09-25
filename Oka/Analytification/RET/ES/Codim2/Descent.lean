/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.ES.Codim2.DescentSections

/-!
# Descent of generators of bounded sections along the Puiseux map

Keep the notation of `Oka/Analytification/RET/ES/Codim2/DescentSections.lean`: `α` is the Puiseux
map `t ↦ tˢ`, `W'` is the base change of `W` along `α`, and `𝒜`, `𝒜'` are the sheaves of bounded
sections. Let `σ₁, …, σ_m ∈ 𝒜'(α⁻¹(U))`. The averages
`R(tⁱ σⱼ) ∈ 𝒜(U)` for `i < s` (`…IsPuiseuxPullback.avgSec`) inherit generation and local freeness:

- If `σ` generates `𝒜'` near the point `y'` over a point `y` with `t(y) = 0`, then the averages
  generate `𝒜` near `y` (`…IsPuiseuxPullback.exists_span_avgSec_of_eq_zero`): writing
  `α^* a = ∑ⱼ fⱼ σⱼ` and `fⱼ = ∑ᵢ tⁱ gᵢⱼ ∘ α` (`Kummer.exists_eqOn_sum_pow_mul_comp_coordPow`), one
  gets `a = R(α^* a) = ∑ gᵢⱼ R(tⁱ σⱼ)`.
- If `𝒜'` is free near one point `y'` over `y` with a basis in the span of `σ` and `t(y) ≠ 0`,
  then `𝒜` is free near `y` with a basis in the span of the averages
  (`…IsPuiseuxPullback.isFreeSpanAt_avgSec_of_ne_zero`). Near `y` the preimage `α⁻¹(V)` is the
  disjoint union of the rotations of a piece `P₀ ∋ y'` (`Kummer.exists_pieces_coordPow`); a
  section `e` of `𝒜'` near `y'` gives the invariant section `∑_ζ ζ · (1_{P₀} e)`, and the
  descents of these sections for a basis `e` form a basis of `𝒜` near `y`.

Over a point `y` with `t(y) = 0` only generation is proved: freeness of `𝒜` near such a point has
to be supplied, and then the averages span a basis (`…IsPuiseuxPullback.isFreeSpanAt_avgSec`).

## Main definitions

- `ComplexAnalytic.BoundedSections.tPow`: the function `tⁱ` on an open of `N'`.
- `…IsPuiseuxPullback.avgSec`: the averages `R(tⁱ σⱼ)`, descended to `𝒜(U)`, indexed by
  `Fin (s * m)`.

## Main results

- `…IsPuiseuxPullback.exists_span_avgSec_of_eq_zero`: generation over `t = 0`.
- `…IsPuiseuxPullback.isFreeSpanAt_avgSec_of_ne_zero`: freeness off `t = 0`.
- `…IsPuiseuxPullback.isFreeSpanAt_avgSec`: if `𝒜'` is free with a basis in the span of `σ` near
  every point of `α⁻¹(U)` off `S'`, then `𝒜` is free with a basis in the span of the averages near
  every point `y ∈ U ∖ α(S')` with `t(y) ≠ 0`, and near every point `y ∈ U ∖ α(S')` near which
  `𝒜` is known to be free.
- `ComplexAnalytic.BoundedSections.isFreeSpanAt_of_isFreeSpanAt_of_span`: freeness near `y` and
  generation by `s` near `y` give freeness with a basis in the span of `s`.
-/

open CategoryTheory Opposite AlgebraicGeometry Topology TopologicalSpace Filter Kummer

universe u

namespace ComplexAnalytic.BoundedSections

open AnalyticSpace AlgebraicGeometry.LocallyRingedSpace

noncomputable section

variable {n : ℕ} {N N₀ : (AnalyticSpace.complexAffineSpace.{u} n).Opens}

/-- **Freeness and generation give freeness in the span**: if `𝒜` is free near `y` (with a basis
in the span of some family `e`) and the sections `s` generate `𝒜` near `y`, then `𝒜` is free near
`y` with a basis in the span of `s`. -/
theorem isFreeSpanAt_of_isFreeSpanAt_of_span {h₀ : N₀ ≤ N} {W : FiniteEtaleOver (space N₀)}
    {U U₂ : (space N).Opens} {m m₂ : ℕ} {s : Fin m → (boundedModule h₀ W).val.obj (op U)}
    {e : Fin m₂ → (boundedModule h₀ W).val.obj (op U₂)} {y : space N}
    (he : IsFreeSpanAt h₀ W e y) {V : (space N).Opens} (hVU : V ≤ U) (hyV : y ∈ V)
    (hs : ∀ (V'' : (space N).Opens) (h : V'' ≤ V) (a : (boundedModule h₀ W).val.obj (op V'')),
      ∃ f : Fin m → (space N).presheaf.obj (op V''),
        a = ∑ i, f i • sectRes (boundedModule h₀ W) (h.trans hVU) (s i)) :
    IsFreeSpanAt h₀ W s y := by
  obtain ⟨Ve, -, r, b, -, hyVe, -, hspan, hindep⟩ := he
  have h₁ : Ve ⊓ V ≤ Ve := inf_le_left
  have h₂ : Ve ⊓ V ≤ V := inf_le_right
  choose P hP using fun k ↦ hs (Ve ⊓ V) h₂ (sectRes (boundedModule h₀ W) h₁ (b k))
  refine isFreeSpanAt_of_basis (h₂.trans hVU) (fun k ↦ sectRes (boundedModule h₀ W) h₁ (b k))
    (fun V' h a ↦ ?_) (fun V' h c hc ↦ hindep V' (h.trans h₁) c ?_) le_rfl ⟨hyVe, hyV⟩ P
    fun k ↦ ?_
  · obtain ⟨c, hc⟩ := hspan V' (h.trans h₁) a
    exact ⟨c, by simpa only [sectRes_sectRes] using hc⟩
  · simpa only [sectRes_sectRes] using hc
  · simpa only [sectRes_sectRes, homOfLE_refl, op_id, (boundedModule h₀ W).val.map_id] using hP k

variable {i₀ : ULift.{u} (Fin n)} {s : ℕ} {N' N₀' : (AnalyticSpace.complexAffineSpace.{u} n).Opens}

variable (i₀) in
/-- The function `tⁱ = x i₀ ^ i` on an open of `N'`. -/
def tPow (V' : (space N').Opens) (i : ℕ) : (space N').presheaf.obj (op V') :=
  OkaRing.ofDifferentiableOn (fun x : Cn.{u} n ↦ x i₀ ^ i) (by fun_prop)

lemma holFun_tPow {V' : (space N').Opens} (i : ℕ) {x : Cn.{u} n} (hx : x ∈ img V') :
    holFun (tPow i₀ V' i) x = x i₀ ^ i :=
  holFun_ofDifferentiableOn _ hx

namespace IsPuiseuxPullback

variable {h₀ : N₀ ≤ N} {h₀' : N₀' ≤ N'} {W : FiniteEtaleOver (space N₀)}
  {W' : FiniteEtaleOver (space N₀')} {β : W'.left → W.left} (P : IsPuiseuxPullback i₀ s W W' β)
  (hN : ∀ x, x ∈ N' ↔ coordPow i₀ s x ∈ N) [T2Space W.left] [T2Space W'.left]
include P hN

/-- The averages `R(tⁱ σⱼ)`, descended to `𝒜(U)`, indexed by `(i, j)`. -/
def avg {U : (space N).Opens} {m : ℕ}
    (σ : Fin m → (boundedModule h₀' W').val.obj (op (pullOpens i₀ s N' U))) (p : Fin s × Fin m) :
    (boundedModule h₀ W).val.obj (op U) :=
  P.descend hN (P.reynolds hN (tPow i₀ (pullOpens i₀ s N' U) p.1 • σ p.2))
    (P.isInvariant_reynolds hN _)

/-- **The averages `R(tⁱ σⱼ)`** for `i < s`, descended to `𝒜(U)`, indexed by `Fin (s * m)`. -/
def avgSec {U : (space N).Opens} {m : ℕ}
    (σ : Fin m → (boundedModule h₀' W').val.obj (op (pullOpens i₀ s N' U))) (l : Fin (s * m)) :
    (boundedModule h₀ W).val.obj (op U) :=
  P.avg hN (h₀ := h₀) σ (finProdFinEquiv.symm l)

lemma evalFun_avg {U : (space N).Opens} {m : ℕ}
    (σ : Fin m → (boundedModule h₀' W').val.obj (op (pullOpens i₀ s N' U))) (p : Fin s × Fin m)
    {w : W'.left} (hw : w ∈ preim h₀' W' (pullOpens i₀ s N' U)) :
    evalFun (secVal h₀ W (P.avg hN σ p)) (β w) = (s : ℂ)⁻¹ * ∑ l,
      pt W' (P.rotW l w) i₀ ^ (p.1 : ℕ) * evalFun (secVal h₀' W' (σ p.2)) (P.rotW l w) := by
  rw [avg, P.evalFun_descend hN _ hw, P.evalFun_reynolds hN _ hw]
  congr 1
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  have hl := P.rotW_mem_preim hN l hw
  rw [evalFun_secVal_smul _ _ hl, holFun_tPow _ ((mem_preim_iff h₀' W').1 hl)]

/-- The values of a combination of the averages. If `Fⱼ = ∑ᵢ tⁱ gᵢⱼ ∘ α`, then
`∑ gᵢⱼ R(tⁱ σⱼ)` takes at `β(w)` the value `s⁻¹ ∑_ζ ∑ⱼ Fⱼ(ζ w) σⱼ(ζ w)`. -/
lemma evalFun_sum_smul_avg {U V : (space N).Opens} (hVU : V ≤ U) {m : ℕ}
    (σ : Fin m → (boundedModule h₀' W').val.obj (op (pullOpens i₀ s N' U)))
    (g : Fin s × Fin m → (space N).presheaf.obj (op V)) (F : Fin m → Cn.{u} n → ℂ)
    (hF : ∀ j, ∀ x ∈ img (pullOpens i₀ s N' V),
      F j x = ∑ i : Fin s, x i₀ ^ (i : ℕ) * holFun (g (i, j)) (coordPow i₀ s x))
    {w : W'.left} (hw : w ∈ preim h₀' W' (pullOpens i₀ s N' V)) :
    evalFun (secVal h₀ W (∑ p, g p • sectRes (boundedModule h₀ W) hVU (P.avg hN σ p))) (β w) =
      (s : ℂ)⁻¹ * ∑ l, ∑ j, F j (pt W' (P.rotW l w)) *
        evalFun (secVal h₀' W' (σ j)) (P.rotW l w) := by
  have hwU : w ∈ preim h₀' W' (pullOpens i₀ s N' U) := preim_mono h₀' W' (pullOpens_mono hVU) hw
  rw [evalFun_secVal_sum_smul _ _ _ (P.apply_mem_preim hN hw)]
  simp_rw [evalFun_secVal_sectRes _ _ (P.apply_mem_preim hN hw), P.evalFun_avg hN σ _ hwU]
  have hF' : ∀ l j, F j (pt W' (P.rotW l w)) = ∑ i : Fin s, pt W' (P.rotW l w) i₀ ^ (i : ℕ) *
      holFun (g (i, j)) (pt W (β w)) := fun l j ↦ by
    rw [hF j _ ((mem_preim_iff h₀' W').1 (P.rotW_mem_preim hN l hw)), P.pt_eq, P.pt_rotW,
      P.coordPow_coordRot_zeta]
  simp_rw [hF', Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_
  ring

omit [T2Space W.left] [T2Space W'.left] in
lemma evalFun_eq_sum_of_eq_sum_smul {V : (space N).Opens} {m : ℕ} {V' : (space N').Opens}
    (hV : pullOpens i₀ s N' V ≤ V')
    (σ : Fin m → (boundedModule h₀' W').val.obj (op V'))
    (a : (boundedModule h₀ W).val.obj (op V)) (f : Fin m → (space N').presheaf.obj
      (op (pullOpens i₀ s N' V)))
    (hf : P.pullSec hN h₀' a = ∑ j, f j • sectRes (boundedModule h₀' W') hV (σ j))
    {w : W'.left} (hw : w ∈ preim h₀' W' (pullOpens i₀ s N' V)) :
    evalFun (secVal h₀ W a) (β w) =
      ∑ j, holFun (f j) (pt W' w) * evalFun (secVal h₀' W' (σ j)) w := by
  rw [← P.evalFun_pullSec hN a hw, hf, evalFun_secVal_sum_smul _ _ _ hw]
  simp_rw [evalFun_secVal_sectRes _ _ hw]

omit [T2Space W.left] [T2Space W'.left] in
/-- The decomposition `f = ∑ᵢ tⁱ gᵢ ∘ α` of the holomorphic functions on `α⁻¹(V)`, with the `gᵢ`
as sections over `V`. -/
lemma exists_holFun_eq_sum {V : (space N).Opens}
    (f : (space N').presheaf.obj (op (pullOpens i₀ s N' V))) :
    ∃ g : Fin s → (space N).presheaf.obj (op V), ∀ x ∈ img (pullOpens i₀ s N' V),
      holFun f x = ∑ i : Fin s, x i₀ ^ (i : ℕ) * holFun (g i) (coordPow i₀ s x) := by
  have hf : DifferentiableOn ℂ (holFun f) (coordPow i₀ s ⁻¹' (img V : Set (Cn.{u} n))) :=
    (differentiableOn_holFun f).mono fun x hx ↦ (mem_img_pullOpens hN).2 hx
  obtain ⟨g, hgd, hgeq⟩ := exists_eqOn_sum_pow_mul_comp_coordPow P.pos (img V).isOpen hf
  refine ⟨fun i ↦ OkaRing.ofDifferentiableOn (g i) (hgd i), fun x hx ↦ ?_⟩
  have hx' : coordPow i₀ s x ∈ img V := (mem_img_pullOpens hN).1 hx
  rw [hgeq hx']
  exact Finset.sum_congr rfl fun i _ ↦ by rw [holFun_ofDifferentiableOn _ hx']

/-- **Generation over `t = 0`.** Let `y ∈ U` with `t(y) = 0`, so that `y` is the only point over
`y`. If `σ` generates `𝒜'` near `y`, then the averages `R(tⁱ σⱼ)` generate `𝒜` near `y`. -/
theorem exists_span_avg_of_eq_zero {U : (space N).Opens} {m : ℕ}
    (σ : Fin m → (boundedModule h₀' W').val.obj (op (pullOpens i₀ s N' U))) {y : space N}
    (hyU : y ∈ U) (ht : y.1 i₀ = 0) {V' : (space N').Opens} (hV'U : V' ≤ pullOpens i₀ s N' U)
    (hyV' : y.1 ∈ img V')
    (hspan : ∀ (V'' : (space N').Opens) (h : V'' ≤ V')
      (b : (boundedModule h₀' W').val.obj (op V'')), ∃ f : Fin m → (space N').presheaf.obj (op V''),
        b = ∑ j, f j • sectRes (boundedModule h₀' W') (h.trans hV'U) (σ j)) :
    ∃ (V : (space N).Opens) (hVU : V ≤ U), y ∈ V ∧ ∀ (V'' : (space N).Opens) (h : V'' ≤ V)
      (a : (boundedModule h₀ W).val.obj (op V'')),
        ∃ g : Fin s × Fin m → (space N).presheaf.obj (op V''),
          a = ∑ p, g p • sectRes (boundedModule h₀ W) (h.trans hVU) (P.avg hN σ p) := by
  obtain ⟨r, hr, hrV'⟩ := Metric.isOpen_iff.1 (img V').isOpen _ hyV'
  have hyy : coordPow i₀ s y.1 = y.1 := by
    funext j
    by_cases hj : j = i₀
    · subst hj
      rw [coordPow_self, ht, zero_pow P.pos.ne']
    · exact coordPow_of_ne _ _ hj
  set B : Set (Cn.{u} n) := Metric.ball (y.1 : Cn.{u} n) (min r (r ^ s))
  have hBo : IsOpen B := Metric.isOpen_ball
  let V : (space N).Opens := U ⊓ ⟨Subtype.val ⁻¹' B, hBo.preimage
    continuous_subtype_val⟩
  have hVU : V ≤ U := inf_le_left
  have hyV : y ∈ V := ⟨hyU, Metric.mem_ball_self (lt_min hr (pow_pos hr s))⟩
  have hαV : ∀ x, coordPow i₀ s x ∈ img V → x ∈ img V' := fun x hx ↦ by
    obtain ⟨_, hxV⟩ := mem_img_iff.1 hx
    have hxB : ‖coordPow i₀ s x - coordPow i₀ s y.1‖ < min r (r ^ s) := by
      rw [hyy, ← dist_eq_norm]
      exact hxV.2
    obtain ⟨k, hk⟩ := exists_coordRot_norm_sub_lt P.pos hr hxB
    refine hrV' ?_
    have hrot : coordRot i₀ (zeta s ^ (k : ℕ)) y.1 = y.1 := by
      funext j
      by_cases hj : j = i₀
      · subst hj
        rw [coordRot_self, ht, mul_zero]
      · exact coordRot_of_ne _ _ hj
    rw [Metric.mem_ball, dist_eq_norm, ← hrot]
    exact hk
  refine ⟨V, hVU, hyV, fun V'' h a ↦ ?_⟩
  have hle : pullOpens i₀ s N' V'' ≤ V' := fun z hz ↦ by
    obtain ⟨_, hz'⟩ := mem_img_iff.1 (hαV z.1 (img_mono h hz))
    exact hz'
  obtain ⟨f, hf⟩ := hspan _ hle (P.pullSec hN h₀' a)
  choose g hg using fun j ↦ P.exists_holFun_eq_sum hN (f j)
  refine ⟨fun p ↦ g p.2 p.1, secVal_ext h₀ W fun w hw ↦ ?_⟩
  obtain ⟨w', hw', rfl⟩ := P.exists_lift_mem (h₀' := h₀') hN hw
  rw [P.evalFun_sum_smul_avg hN (h.trans hVU) σ _ (fun j ↦ holFun (f j)) (fun j x hx ↦ hg j x hx)
    hw']
  have hl : ∀ l, evalFun (secVal h₀ W a) (β w') = ∑ j, holFun (f j) (pt W' (P.rotW l w')) *
      evalFun (secVal h₀' W' (σ j)) (P.rotW l w') := fun l ↦ by
    rw [← P.apply_rotW l w', P.evalFun_eq_sum_of_eq_sum_smul hN _ σ a f hf
      (P.rotW_mem_preim hN l hw')]
  simp_rw [← hl]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ (Nat.cast_ne_zero.2 P.pos.ne'), one_mul]

/-! ### Spreading a section over the rotations of a piece -/

section Piece

variable {V₀ P₀ : Set (Cn.{u} n)} (hP : IsPiece i₀ s V₀ P₀)

omit P hN [T2Space W.left] [T2Space W'.left] in
open Classical in
variable (h₀' P₀) in
/-- The function `1_{P₀} b` on `W'`. -/
def cutFun {V' : (space N').Opens} (b : (boundedModule h₀' W').val.obj (op V')) (w : W'.left) :
    ℂ :=
  if pt W' w ∈ P₀ then evalFun (secVal h₀' W' b) w else 0

omit P [T2Space W.left] [T2Space W'.left] in
lemma mem_of_mem_preim {V : (space N).Opens} (hV : ∀ x ∈ img V, x ∈ V₀) {w : W'.left}
    (hw : w ∈ preim h₀' W' (pullOpens i₀ s N' V)) : pt W' w ∈ coordPow i₀ s ⁻¹' V₀ :=
  hV _ ((mem_preim_pullOpens hN).1 hw)

omit P [T2Space W.left] [T2Space W'.left] in
include hP in
lemma isHolOn_cutFun {V' : (space N').Opens} (hPV' : P₀ ⊆ img V') {V : (space N).Opens}
    (hV : ∀ x ∈ img V, x ∈ V₀) (b : (boundedModule h₀' W').val.obj (op V')) :
    IsHolOn W' (cutFun h₀' P₀ b) (preim h₀' W' (pullOpens i₀ s N' V)) := by
  classical
  intro w hw
  have hev : ∀ᶠ w'' in 𝓝 w, (pt W' w'' ∈ P₀ ↔ pt W' w ∈ P₀) :=
    (continuous_pt W').continuousAt.eventually (hP.eventually_mem_iff _ (mem_of_mem_preim hN hV hw))
  by_cases hwP : pt W' w ∈ P₀
  · obtain ⟨F, hF⟩ := isHolOn_secVal h₀' W' b w ((mem_preim_iff h₀' W').2 (hPV' hwP))
    refine ⟨F, ?_⟩
    filter_upwards [hF, hev] with w'' h₁ h₂
    exact ⟨h₁.1, by rw [cutFun, if_pos (h₂.2 hwP), h₁.2]⟩
  · refine ⟨fun _ ↦ 0, ?_⟩
    filter_upwards [hev] with w'' h₂
    exact ⟨differentiableAt_const _, by rw [cutFun, if_neg fun h ↦ hwP (h₂.1 h)]⟩

omit P [T2Space W.left] [T2Space W'.left] in
include hP in
lemma isBddOn_cutFun {V' : (space N').Opens} (hPV' : P₀ ⊆ img V') {V : (space N).Opens}
    (hV : ∀ x ∈ img V, x ∈ V₀) (b : (boundedModule h₀' W').val.obj (op V')) :
    IsBddOn W' (pullOpens i₀ s N' V) (cutFun h₀' P₀ b) := by
  classical
  intro x hx hxN
  have hxV₀ : x ∈ coordPow i₀ s ⁻¹' V₀ := hV _ ((mem_img_pullOpens hN).1 hx)
  by_cases hxP : x ∈ P₀
  · obtain ⟨M, hM, C, hC⟩ := isBddOn_secVal h₀' W' b x (hPV' hxP) hxN
    refine ⟨M ∩ P₀, inter_mem hM (hP.isOpen_piece.mem_nhds hxP), C, fun w hw _ ↦ ?_⟩
    rw [cutFun, if_pos hw.2]
    exact hC w hw.1 (hPV' hw.2)
  · refine ⟨{z | z ∈ P₀ ↔ x ∈ P₀}, hP.eventually_mem_iff x hxV₀, 0, fun w hw _ ↦ ?_⟩
    rw [cutFun, if_neg fun h ↦ hxP (hw.1 h), norm_zero]

omit [T2Space W.left] in
include hP in
lemma exists_spread {V' : (space N').Opens} (hPV' : P₀ ⊆ img V') {V : (space N).Opens}
    (hV : ∀ x ∈ img V, x ∈ V₀) (b : (boundedModule h₀' W').val.obj (op V')) :
    ∃ c : (boundedModule h₀' W').val.obj (op (pullOpens i₀ s N' V)),
      ∀ w ∈ preim h₀' W' (pullOpens i₀ s N' V),
        evalFun (secVal h₀' W' c) w = ∑ l, cutFun h₀' P₀ b (P.rotW l w) :=
  exists_secVal_eq h₀' W'
    (IsHolOn.sum Finset.univ fun l _ ↦ P.isHolOn_comp_rotW hN (isHolOn_cutFun hN hP hPV' hV b) l)
    (IsBddOn.sum Finset.univ fun l _ ↦ P.isBddOn_comp_rotW hN (isBddOn_cutFun hN hP hPV' hV b) l)

omit [T2Space W.left] in
/-- **The spread `∑_ζ ζ · (1_{P₀} b)`** of a section `b` of `𝒜'` near `P₀`, an invariant section
over `α⁻¹(V)`. -/
def spread {V' : (space N').Opens} (hPV' : P₀ ⊆ img V') {V : (space N).Opens}
    (hV : ∀ x ∈ img V, x ∈ V₀) (b : (boundedModule h₀' W').val.obj (op V')) :
    (boundedModule h₀' W').val.obj (op (pullOpens i₀ s N' V)) :=
  (P.exists_spread hN hP hPV' hV b).choose

omit [T2Space W.left] in
lemma evalFun_spread {V' : (space N').Opens} (hPV' : P₀ ⊆ img V') {V : (space N).Opens}
    (hV : ∀ x ∈ img V, x ∈ V₀) (b : (boundedModule h₀' W').val.obj (op V')) {w : W'.left}
    (hw : w ∈ preim h₀' W' (pullOpens i₀ s N' V)) :
    evalFun (secVal h₀' W' (P.spread hN hP hPV' hV b)) w = ∑ l, cutFun h₀' P₀ b (P.rotW l w) :=
  (P.exists_spread hN hP hPV' hV b).choose_spec w hw

omit [T2Space W.left] in
lemma isInvariant_spread {V' : (space N').Opens} (hPV' : P₀ ⊆ img V') {V : (space N).Opens}
    (hV : ∀ x ∈ img V, x ∈ V₀) (b : (boundedModule h₀' W').val.obj (op V')) :
    P.IsInvariant (P.spread hN hP hPV' hV b) := fun k w hw ↦ by
  haveI : NeZero s := ⟨P.pos.ne'⟩
  rw [P.evalFun_spread hN hP hPV' hV b (P.rotW_mem_preim hN k hw),
    P.evalFun_spread hN hP hPV' hV b hw]
  simp_rw [P.rotW_rotW]
  exact Fintype.sum_equiv (Equiv.addRight k) _ _ fun _ ↦ rfl

omit [T2Space W.left] in
/-- Over `P₀`, the spread of `b` is `b`. -/
lemma evalFun_spread_of_mem {V' : (space N').Opens} (hPV' : P₀ ⊆ img V') {V : (space N).Opens}
    (hV : ∀ x ∈ img V, x ∈ V₀) (b : (boundedModule h₀' W').val.obj (op V')) {w : W'.left}
    (hw : w ∈ preim h₀' W' (pullOpens i₀ s N' V)) (hwP : pt W' w ∈ P₀) :
    evalFun (secVal h₀' W' (P.spread hN hP hPV' hV b)) w = evalFun (secVal h₀' W' b) w := by
  classical
  rw [P.evalFun_spread hN hP hPV' hV b hw]
  simp_rw [cutFun, P.pt_rotW]
  rw [hP.sum_ite P.pos hwP (fun l ↦ evalFun (secVal h₀' W' b) (P.rotW l w)), P.rotW_zero]

omit [T2Space W.left] [T2Space W'.left] in
include hP in
/-- Every point of `W` over `V` has a lift over `P₀`. -/
lemma exists_lift_mem_piece {V : (space N).Opens} (hV : ∀ x ∈ img V, x ∈ V₀) {w : W.left}
    (hw : w ∈ preim h₀ W V) : ∃ w', w' ∈ preim h₀' W' (pullOpens i₀ s N' V) ∧ β w' = w ∧
      pt W' w' ∈ P₀ := by
  obtain ⟨w₁, hw₁, rfl⟩ := P.exists_lift_mem (h₀' := h₀') hN hw
  obtain ⟨l, hl⟩ := hP.exists_coordRot_mem (mem_of_mem_preim hN hV hw₁)
  exact ⟨P.rotW l w₁, P.rotW_mem_preim hN l hw₁, P.apply_rotW l w₁, by rw [P.pt_rotW]; exact hl⟩

end Piece

/-! ### Freeness off `t = 0` -/


/-- **Freeness off `t = 0`.** Let `y ∈ U` with `t(y) ≠ 0` and let `y'` be a point over `y`. If
`𝒜'` is free near `y'` with a basis in the span of `σ`, then `𝒜` is free near `y` with a basis in
the span of the averages `R(tⁱ σⱼ)`. -/
theorem isFreeSpanAt_avgSec_of_ne_zero {U : (space N).Opens} {m : ℕ}
    (σ : Fin m → (boundedModule h₀' W').val.obj (op (pullOpens i₀ s N' U))) {y : space N}
    (hyU : y ∈ U) (ht : y.1 i₀ ≠ 0) {y' : space N'} (hy' : coordPow i₀ s y'.1 = y.1)
    (hfree : IsFreeSpanAt h₀' W' σ y') : IsFreeSpanAt h₀ W (P.avgSec hN σ) y := by
  classical
  obtain ⟨Vb, hVbU, r, e, Pm, hy'Vb, he, hspan, hindep⟩ := hfree
  have hy'0 : y'.1 i₀ ≠ 0 := fun h ↦ ht (by rw [← hy', coordPow_self, h, zero_pow P.pos.ne'])
  obtain ⟨V₀, P₀, hyV₀, hP₀Vb, hP⟩ := exists_isPiece P.pos hy'0
    ((img Vb).isOpen.mem_nhds (mem_img_iff.2 ⟨y'.2, hy'Vb⟩))
  rw [hy'] at hyV₀
  have hP₀o : IsOpen P₀ := hP.isOpen_piece
  let V : (space N).Opens := U ⊓ ⟨Subtype.val ⁻¹' V₀, hP.isOpen.preimage continuous_subtype_val⟩
  have hVU : V ≤ U := inf_le_left
  have hV : ∀ x ∈ img V, x ∈ V₀ := fun x hx ↦ (mem_img_iff.1 hx).2.2
  have hyV : y ∈ V := ⟨hyU, hyV₀⟩
  have hV'' : ∀ {V'' : (space N).Opens}, V'' ≤ V → ∀ x ∈ img V'', x ∈ V₀ :=
    fun h x hx ↦ hV x (img_mono h hx)
  -- the pieces over `V''`
  let Q : (space N).Opens → (space N').Opens := fun V'' ↦
    pullOpens i₀ s N' V'' ⊓ ⟨Subtype.val ⁻¹' P₀, hP₀o.preimage continuous_subtype_val⟩
  have hQVb : ∀ V'', Q V'' ≤ Vb := fun V'' z hz ↦ by
    obtain ⟨_, h⟩ := mem_img_iff.1 (hP₀Vb hz.2)
    exact h
  have hQpull : ∀ V'', Q V'' ≤ pullOpens i₀ s N' V'' := fun _ ↦ inf_le_left
  have hmemQ : ∀ V'' {w : W'.left}, w ∈ preim h₀' W' (pullOpens i₀ s N' V'') →
      pt W' w ∈ P₀ → w ∈ preim h₀' W' (Q V'') := fun V'' w h₁ h₂ ↦
    ⟨h₁, by change ((proj h₀' W').toLRSHom.base w).1 ∈ P₀; rw [coe_proj_base]; exact h₂⟩
  have himgQ : ∀ V'' {x : Cn.{u} n}, coordPow i₀ s x ∈ img V'' → x ∈ P₀ → x ∈ img (Q V'') :=
    fun V'' x h₁ h₂ ↦ mem_img_iff.2 ⟨(hN x).2 (img_le V'' _ h₁), h₁, h₂⟩
  have himgQ' : ∀ V'' {x : Cn.{u} n}, x ∈ img (Q V'') → x ∈ P₀ ∧ coordPow i₀ s x ∈ img V'' :=
    fun V'' x hx ↦ by
      obtain ⟨_, h₁, h₂⟩ := mem_img_iff.1 hx
      exact ⟨h₂, h₁⟩
  -- the basis downstairs
  let e' : Fin r → (boundedModule h₀ W).val.obj (op V) := fun k ↦
    P.descend hN (P.spread hN hP hP₀Vb hV (e k)) (P.isInvariant_spread hN hP hP₀Vb hV (e k))
  have he' : ∀ k {w : W'.left}, w ∈ preim h₀' W' (pullOpens i₀ s N' V) → pt W' w ∈ P₀ →
      evalFun (secVal h₀ W (e' k)) (β w) = evalFun (secVal h₀' W' (e k)) w := fun k w hw hwP ↦ by
    rw [P.evalFun_descend hN _ hw, P.evalFun_spread_of_mem hN hP hP₀Vb hV _ hw hwP]
  have he'' : ∀ {V''} (h : V'' ≤ V) k {w : W'.left},
      w ∈ preim h₀' W' (pullOpens i₀ s N' V'') → pt W' w ∈ P₀ →
      evalFun (secVal h₀ W (sectRes (boundedModule h₀ W) h (e' k))) (β w) =
        evalFun (secVal h₀' W' (e k)) w := fun h k w hw hwP ↦ by
    rw [evalFun_secVal_sectRes _ _ (P.apply_mem_preim hN hw),
      he' k (preim_mono h₀' W' (pullOpens_mono h) hw) hwP]
  -- the value of a combination of the `eₖ` at a point over `P₀`
  have hval : ∀ V'' (c : Fin r → (space N').presheaf.obj (op (Q V''))) {w : W'.left},
      w ∈ preim h₀' W' (Q V'') → evalFun (secVal h₀' W'
        (∑ k, c k • sectRes (boundedModule h₀' W') (hQVb V'') (e k))) w =
        ∑ k, holFun (c k) (pt W' w) * evalFun (secVal h₀' W' (e k)) w := fun V'' c w hw ↦ by
    rw [evalFun_secVal_sum_smul _ _ _ hw]
    simp_rw [evalFun_secVal_sectRes _ _ hw]
  -- the coefficients of the `e'ₖ` in terms of the averages
  have hF : ∀ k j, DifferentiableOn ℂ (fun x ↦ if x ∈ P₀ then (s : ℂ) * holFun (Pm k j) x else 0)
      (img (pullOpens i₀ s N' V)) := fun k j ↦ by
    refine (hP.differentiableOn_ite (Z := coordPow i₀ s ⁻¹' (img V))
      ((img V).isOpen.preimage (continuous_coordPow s)) (fun x hx ↦ hV _ hx) ?_).mono
      fun x hx ↦ (mem_img_pullOpens hN).1 hx
    exact ((differentiableOn_holFun (Pm k j)).const_mul (s : ℂ)).mono fun x hx ↦ hP₀Vb hx.1
  let Fs : Fin r → Fin m → (space N').presheaf.obj (op (pullOpens i₀ s N' V)) := fun k j ↦
    OkaRing.ofDifferentiableOn _ (hF k j)
  choose g hg using fun k j ↦ P.exists_holFun_eq_sum hN (Fs k j)
  let Pco : Fin r → Fin (s * m) → (space N).presheaf.obj (op V) := fun k l ↦
    g k (finProdFinEquiv.symm l).2 (finProdFinEquiv.symm l).1
  have hPco : ∀ k, sectRes (boundedModule h₀ W) le_rfl (e' k) = ∑ l, Pco k l •
      sectRes (boundedModule h₀ W) (le_rfl.trans hVU) (P.avgSec hN σ l) := by
    intro k
    have hre : ∑ l, Pco k l • sectRes (boundedModule h₀ W) (le_rfl.trans hVU)
        (P.avgSec hN σ l) = ∑ p : Fin s × Fin m, g k p.2 p.1 •
          sectRes (boundedModule h₀ W) hVU (P.avg hN σ p) :=
      (Fintype.sum_equiv finProdFinEquiv _ _ fun p ↦ by
        simp only [Pco, avgSec, Equiv.symm_apply_apply]).symm
    rw [hre]
    refine secVal_ext h₀ W fun w hw ↦ ?_
    obtain ⟨w', hw', rfl, hw'P⟩ := P.exists_lift_mem_piece hN hP hV hw
    rw [evalFun_secVal_sectRes _ _ hw, he' k hw' hw'P,
      P.evalFun_sum_smul_avg hN hVU σ (fun p ↦ g k p.2 p.1) (fun j ↦ holFun (Fs k j))
        (fun j x hx ↦ hg k j x hx) hw']
    have hw'b : w' ∈ preim h₀' W' Vb := (mem_preim_iff h₀' W').2 (hP₀Vb hw'P)
    rw [he k, evalFun_secVal_sum_smul _ _ _ hw'b]
    simp_rw [evalFun_secVal_sectRes _ _ hw'b]
    have hFs : ∀ l j, holFun (Fs k j) (pt W' (P.rotW l w')) =
        if coordRot i₀ (zeta s ^ (l : ℕ)) (pt W' w') ∈ P₀ then
          (s : ℂ) * holFun (Pm k j) (coordRot i₀ (zeta s ^ (l : ℕ)) (pt W' w')) else 0 :=
      fun l j ↦ by
        rw [holFun_ofDifferentiableOn _ ((mem_preim_iff h₀' W').1 (P.rotW_mem_preim hN l hw')),
          P.pt_rotW]
    simp_rw [hFs, ite_mul, zero_mul]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [hP.sum_ite P.pos hw'P (fun l ↦ (s : ℂ) * holFun (Pm k j)
      (coordRot i₀ (zeta s ^ (l : ℕ)) (pt W' w')) * evalFun (secVal h₀' W' (σ j)) (P.rotW l w'))]
    simp only [pow_zero, coordRot_one, P.rotW_zero]
    rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.2 P.pos.ne'), one_mul]
  refine isFreeSpanAt_of_basis hVU e' (fun V'' h a ↦ ?_) (fun V'' h c hc ↦ ?_) le_rfl hyV
    Pco hPco
  · -- spanning
    obtain ⟨c, hc⟩ := hspan (Q V'') (hQVb V'')
      (sectRes (boundedModule h₀' W') (hQpull V'') (P.pullSec hN h₀' a))
    set Z : Set (Cn.{u} n) := coordPow i₀ s ⁻¹' (img V'')
    have hZ : IsOpen Z := (img V'').isOpen.preimage (continuous_coordPow s)
    have hZV : Z ⊆ coordPow i₀ s ⁻¹' V₀ := fun x hx ↦ hV'' h _ hx
    set G : Fin r → Cn.{u} n → ℂ := fun k x ↦ if x ∈ P₀ then holFun (c k) x else 0
    have hG : ∀ k, DifferentiableOn ℂ (G k) Z :=
      fun k ↦ hP.differentiableOn_ite hZ hZV ((differentiableOn_holFun (c k)).mono
        fun x hx ↦ himgQ V'' hx.2 hx.1)
    set H : Fin r → Cn.{u} n → ℂ := fun k x ↦ ∑ l : Fin s, G k (coordRot i₀ (zeta s ^ (l : ℕ)) x)
    have hHroot : ∀ k x, H k (coordRoot i₀ s (coordPow i₀ s x)) = H k x := fun k x ↦
      sum_comp_coordRot_coordRoot P.pos (G k) x
    have hH : ∀ k, DifferentiableOn ℂ (H k) Z := fun k ↦
      DifferentiableOn.fun_sum fun l _ ↦ (hG k).comp (differentiable_coordRot _).differentiableOn
        fun x hx ↦ by
          change coordPow i₀ s _ ∈ img V''
          rw [P.coordPow_coordRot_zeta]
          exact hx
    have hd : ∀ k, DifferentiableOn ℂ (fun x ↦ H k (coordRoot i₀ s x)) (img V'') := fun k ↦
      differentiableOn_of_comp_coordPow (i₀ := i₀) P.pos (img V'').isOpen
        ((hH k).congr fun x _ ↦ hHroot k x)
    refine ⟨fun k ↦ OkaRing.ofDifferentiableOn _ (hd k), secVal_ext h₀ W fun w hw ↦ ?_⟩
    obtain ⟨w', hw', rfl, hw'P⟩ := P.exists_lift_mem_piece hN hP (hV'' h) hw
    have hw'Q := hmemQ V'' hw' hw'P
    rw [evalFun_secVal_sum_smul _ _ _ hw, ← P.evalFun_pullSec hN a hw',
      ← evalFun_secVal_sectRes (hQpull V'') _ hw'Q, hc, hval V'' c hw'Q]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [he'' h k hw' hw'P, holFun_ofDifferentiableOn _ ((mem_preim_iff h₀ W).1 hw), P.pt_eq,
      hHroot]
    congr 1
    change _ = ∑ l : Fin s, (if coordRot i₀ (zeta s ^ (l : ℕ)) (pt W' w') ∈ P₀ then
      holFun (c k) (coordRot i₀ (zeta s ^ (l : ℕ)) (pt W' w')) else 0)
    rw [hP.sum_ite P.pos hw'P (fun l ↦ holFun (c k) (coordRot i₀ (zeta s ^ (l : ℕ)) (pt W' w')))]
    simp
  · -- independence
    have hCd : ∀ k, DifferentiableOn ℂ (fun x ↦ holFun (c k) (coordPow i₀ s x)) (img (Q V'')) :=
      fun k ↦ (differentiableOn_holFun (c k)).comp (differentiable_coordPow s).differentiableOn
        fun x hx ↦ (himgQ' V'' hx).2
    let C : Fin r → (space N').presheaf.obj (op (Q V'')) := fun k ↦
      OkaRing.ofDifferentiableOn _ (hCd k)
    have hC0 : ∑ k, C k • sectRes (boundedModule h₀' W') (hQVb V'') (e k) = 0 := by
      refine secVal_ext h₀' W' fun w hw ↦ ?_
      have hwP : pt W' w ∈ P₀ := (himgQ' V'' ((mem_preim_iff h₀' W').1 hw)).1
      have hwV : w ∈ preim h₀' W' (pullOpens i₀ s N' V'') := hw.1
      rw [hval V'' C hw, evalFun_secVal_zero hw]
      have := congrArg (fun a ↦ evalFun (secVal h₀ W a) (β w)) hc
      beta_reduce at this
      rw [evalFun_secVal_sum_smul _ _ _ (P.apply_mem_preim hN hwV),
        evalFun_secVal_zero (P.apply_mem_preim hN hwV)] at this
      rw [← this]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [he'' h k hwV hwP, holFun_ofDifferentiableOn _ ((mem_preim_iff h₀' W').1 hw), P.pt_eq]
    intro k
    have hCk := hindep (Q V'') (hQVb V'') C hC0 k
    refine eq_of_holFun_eq fun x hx ↦ ?_
    have hxV₀ : coordRoot i₀ s x ∈ coordPow i₀ s ⁻¹' V₀ := by
      rw [Set.mem_preimage, coordPow_coordRoot P.pos.ne']
      exact hV'' h x hx
    obtain ⟨l, hl⟩ := hP.exists_coordRot_mem hxV₀
    have hαx : coordPow i₀ s (coordRot i₀ (zeta s ^ (l : ℕ)) (coordRoot i₀ s x)) = x := by
      rw [P.coordPow_coordRot_zeta, coordPow_coordRoot P.pos.ne']
    have hmem := himgQ V'' (x := coordRot i₀ (zeta s ^ (l : ℕ)) (coordRoot i₀ s x))
      (by rw [hαx]; exact hx) hl
    have := holFun_ofDifferentiableOn (hCd k) hmem
    rw [hαx] at this
    rw [← this, holFun_zero hx]
    change holFun (C k) _ = 0
    rw [hCk, holFun_zero hmem]

/-- **Generation over `t = 0`**, for the averages indexed by `Fin (s * m)`. -/
theorem exists_span_avgSec_of_eq_zero {U : (space N).Opens} {m : ℕ}
    (σ : Fin m → (boundedModule h₀' W').val.obj (op (pullOpens i₀ s N' U))) {y : space N}
    (hyU : y ∈ U) (ht : y.1 i₀ = 0) {V' : (space N').Opens} (hV'U : V' ≤ pullOpens i₀ s N' U)
    (hyV' : y.1 ∈ img V')
    (hspan : ∀ (V'' : (space N').Opens) (h : V'' ≤ V')
      (b : (boundedModule h₀' W').val.obj (op V'')), ∃ f : Fin m → (space N').presheaf.obj (op V''),
        b = ∑ j, f j • sectRes (boundedModule h₀' W') (h.trans hV'U) (σ j)) :
    ∃ (V : (space N).Opens) (hVU : V ≤ U), y ∈ V ∧ ∀ (V'' : (space N).Opens) (h : V'' ≤ V)
      (a : (boundedModule h₀ W).val.obj (op V'')),
        ∃ g : Fin (s * m) → (space N).presheaf.obj (op V''),
          a = ∑ l, g l • sectRes (boundedModule h₀ W) (h.trans hVU) (P.avgSec hN σ l) := by
  obtain ⟨V, hVU, hyV, hV⟩ := P.exists_span_avg_of_eq_zero hN σ hyU ht hV'U hyV' hspan
  refine ⟨V, hVU, hyV, fun V'' h a ↦ ?_⟩
  obtain ⟨g, rfl⟩ := hV V'' h a
  exact ⟨fun l ↦ g (finProdFinEquiv.symm l), Fintype.sum_equiv finProdFinEquiv _ _ fun p ↦ by
    simp only [avgSec, Equiv.symm_apply_apply]⟩

/-- **Descent of local freeness along the Puiseux map.** Suppose that near every point of
`α⁻¹(U)` off a set `S'`, the sheaf `𝒜'` is free with a basis in the span of `σ`. Let `y ∈ U` with
`y ∉ α(S')`. If `t(y) ≠ 0`, or if `𝒜` is known to be free near `y`, then `𝒜` is free near `y`
with a basis in the span of the averages `R(tⁱ σⱼ)`. -/
theorem isFreeSpanAt_avgSec {U : (space N).Opens} {m : ℕ}
    (σ : Fin m → (boundedModule h₀' W').val.obj (op (pullOpens i₀ s N' U))) {S' : Set (Cn.{u} n)}
    (hfree : ∀ y' ∈ pullOpens i₀ s N' U, y'.1 ∉ S' → IsFreeSpanAt h₀' W' σ y') {y : space N}
    (hyU : y ∈ U) (hyS : y.1 ∉ coordPow i₀ s '' S')
    (hy : y.1 i₀ ≠ 0 ∨ ∃ (U₂ : (space N).Opens) (m₂ : ℕ)
      (e : Fin m₂ → (boundedModule h₀ W).val.obj (op U₂)), IsFreeSpanAt h₀ W e y) :
    IsFreeSpanAt h₀ W (P.avgSec hN σ) y := by
  have hroot : coordPow i₀ s (coordRoot i₀ s y.1) = y.1 := coordPow_coordRoot P.pos.ne' _
  let y' : space N' := ⟨coordRoot i₀ s y.1, (hN _).2 (by rw [hroot]; exact y.2)⟩
  have hy'U : y' ∈ pullOpens i₀ s N' U := by
    change coordPow i₀ s (coordRoot i₀ s y.1) ∈ img U
    rw [hroot]
    exact mem_img_iff.2 ⟨y.2, hyU⟩
  have hfree' := hfree y' hy'U fun h ↦ hyS ⟨_, h, hroot⟩
  by_cases ht : y.1 i₀ = 0
  · obtain ⟨U₂, m₂, e, he⟩ := hy.resolve_left (not_not.2 ht)
    obtain ⟨V', hV'U, hyV', hspan⟩ := exists_span_of_isFreeSpanAt hfree'
    have hyV'' : y.1 ∈ img V' := by
      have : coordRoot i₀ s y.1 = y.1 := coordRoot_of_eq_zero P.pos.ne' ht
      have h₁ : coordRoot i₀ s y.1 ∈ img V' := mem_img_iff.2 ⟨y'.2, hyV'⟩
      rwa [this] at h₁
    obtain ⟨V, hVU, hyV, hV⟩ := P.exists_span_avgSec_of_eq_zero hN σ hyU ht hV'U hyV'' hspan
    exact isFreeSpanAt_of_isFreeSpanAt_of_span he hVU hyV hV
  · exact P.isFreeSpanAt_avgSec_of_ne_zero hN σ hyU ht hroot hfree'

end IsPuiseuxPullback

end

end ComplexAnalytic.BoundedSections
