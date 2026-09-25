/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.ES.KummerSectionsGlue

/-!
# The canonical extension of a finite étale cover of `B × Δ*` across `t = 0`

Let `S ⊆ ℂ^{m+1}` be the open subspace `{b ∈ B, ‖t‖ < 1}`, `S° ⊆ S` the complement of
`D = {t = 0}` and `p : W → S°` a finite étale cover. The **canonical extension** `𝒞̄` of `p_* 𝒪_W`
is the sheaf of rings on `S` whose sections over `V` are the sections of `𝒪_W` over
`p⁻¹(V ∩ S°)` which are bounded near `D` (`ComplexAnalytic.KummerModel.IsBoundedNearZero`). The
defining condition is local on `S` and does not refer to any decomposition of `W`, so the
extensions over overlapping charts agree.

## Main definitions

- `ComplexAnalytic.KummerModel.disc hB`: the open subspace `S` of `ℂ^{m+1}`.
- `ComplexAnalytic.KummerModel.boundedSubring W V`: the bounded sections over `V`.
- `ComplexAnalytic.KummerModel.extensionPresheaf W`: the presheaf of rings `V ↦ 𝒞̄(V)` on `S`.
- `ComplexAnalytic.KummerModel.extensionSheaf W hW`: the same, as a sheaf.

## Main results

- `ComplexAnalytic.KummerModel.isSheaf_extensionPresheaf`: `𝒞̄` is a sheaf.
-/

open CategoryTheory Opposite AlgebraicGeometry Topology TopologicalSpace Filter

universe u

namespace ComplexAnalytic.KummerModel

open AnalyticSpace

noncomputable section

variable {m : ℕ} (B : Set (ULift.{u} (Fin m) → ℂ))

/-- The open subset `{b ∈ B, ‖t‖ < 1}` of `ℂ^{m+1}`. -/
def discOpens (hB : IsOpen B) : (AnalyticSpace.complexAffineSpace.{u} (m + 1)).Opens :=
  ⟨splitEquiv m ⁻¹' (B ×ˢ Metric.ball 0 1),
    (hB.prod Metric.isOpen_ball).preimage (splitEquiv m).continuous⟩

variable {B}

/-- The open subspace `S = {b ∈ B, ‖t‖ < 1}` of `ℂ^{m+1}`. -/
abbrev disc (hB : IsOpen B) : AnalyticSpace.{u} :=
  (AnalyticSpace.complexAffineSpace.{u} (m + 1)).restrict (discOpens B hB)

variable {hB : IsOpen B}

/-- The subset of `ℂ^{m+1}` underlying an open subset of `S`. -/
def coeOpens (V : (disc hB).Opens) : Set (ULift.{u} (Fin (m + 1)) → ℂ) :=
  Subtype.val '' (V : Set (disc hB))

lemma isOpen_coeOpens (V : (disc hB).Opens) : IsOpen (coeOpens V) :=
  ((discOpens B hB).isOpenEmbedding.isOpenMap.functor.obj V).isOpen

lemma mem_coeOpens_iff (V : (disc hB).Opens) (x : ULift.{u} (Fin (m + 1)) → ℂ) :
    x ∈ coeOpens V ↔ ∃ hx : x ∈ discOpens B hB, (⟨x, hx⟩ : disc hB) ∈ V := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, h⟩
    exact ⟨_, h, rfl⟩

lemma coeOpens_mono {V V' : (disc hB).Opens} (h : V' ≤ V) : coeOpens V' ⊆ coeOpens V :=
  Set.image_mono h

lemma mem_disc_of_mem_coeOpens (V : (disc hB).Opens) {x : ULift.{u} (Fin (m + 1)) → ℂ}
    (hx : x ∈ coeOpens V) : (splitEquiv m x).1 ∈ B ∧ ‖x zero‖ < 1 := by
  obtain ⟨y, -, rfl⟩ := hx
  have h := y.2
  change splitEquiv m y.1 ∈ B ×ˢ Metric.ball 0 1 at h
  exact ⟨h.1, by simpa using h.2⟩

variable (W : FiniteEtaleOver (punctured hB))

/-- The open `p⁻¹(V ∩ S°)` of `W`. -/
abbrev preim (V : (disc hB).Opens) : W.left.Opens :=
  (Opens.map W.hom.toLRSHom.base).obj (puncturedPreimage hB (isOpen_coeOpens V))

lemma preim_mono {V V' : (disc hB).Opens} (h : V' ≤ V) : preim W V' ≤ preim W V :=
  fun _ hw ↦ coeOpens_mono h hw

/-- The sections of `𝒪_W` over `p⁻¹(V ∩ S°)` which are bounded near `t = 0`. -/
def boundedSubring (V : (disc hB).Opens) : Subring (W.left.presheaf.obj (op (preim W V))) where
  carrier := {s | IsBoundedNearZero hB W (isOpen_coeOpens V) s}
  mul_mem' {s s'} hs hs' x hx hx0 := by
    obtain ⟨N, hN, M, hM⟩ := hs x hx hx0
    obtain ⟨N', hN', M', hM'⟩ := hs' x hx hx0
    refine ⟨N ∩ N', inter_mem hN hN', max M 0 * max M' 0, fun w hw hwN ↦ ?_⟩
    rw [map_mul, norm_mul]
    exact mul_le_mul ((hM w hw hwN.1).trans (le_max_left _ _))
      ((hM' w hw hwN.2).trans (le_max_left _ _)) (norm_nonneg _) (le_max_right _ _)
  one_mem' x _ _ := ⟨Set.univ, univ_mem, 1, fun w hw _ ↦ by rw [map_one, norm_one]⟩
  add_mem' {s s'} hs hs' x hx hx0 := by
    obtain ⟨N, hN, M, hM⟩ := hs x hx hx0
    obtain ⟨N', hN', M', hM'⟩ := hs' x hx hx0
    refine ⟨N ∩ N', inter_mem hN hN', M + M', fun w hw hwN ↦ ?_⟩
    rw [map_add]
    exact (norm_add_le _ _).trans (add_le_add (hM w hw hwN.1) (hM' w hw hwN.2))
  zero_mem' x _ _ := ⟨Set.univ, univ_mem, 0, fun w hw _ ↦ by rw [map_zero, norm_zero]⟩
  neg_mem' {s} hs x hx hx0 := by
    obtain ⟨N, hN, M, hM⟩ := hs x hx hx0
    exact ⟨N, hN, M, fun w hw hwN ↦ by rw [map_neg, norm_neg]; exact hM w hw hwN⟩

lemma mem_boundedSubring_iff (V : (disc hB).Opens) (s : W.left.presheaf.obj (op (preim W V))) :
    s ∈ boundedSubring W V ↔ IsBoundedNearZero hB W (isOpen_coeOpens V) s :=
  Iff.rfl

/-- Restriction of sections along `V' ≤ V` preserves boundedness. -/
lemma map_mem_boundedSubring {V V' : (disc hB).Opens} (h : V' ≤ V)
    {s : W.left.presheaf.obj (op (preim W V))} (hs : s ∈ boundedSubring W V) :
    W.left.presheaf.map (homOfLE (preim_mono W h)).op s ∈ boundedSubring W V' := by
  intro x hx hx0
  obtain ⟨N, hN, M, hM⟩ := hs x (coeOpens_mono h hx) hx0
  refine ⟨N, hN, M, fun w hw hwN ↦ ?_⟩
  rw [eval_presheaf_map]
  exact hM w (preim_mono W h hw) hwN

/-- The presheaf of rings `V ↦ 𝒞̄(V)` of sections of `p_* 𝒪_W` bounded near `t = 0`. -/
def extensionPresheaf :
    TopCat.Presheaf CommRingCat.{u} (disc hB).toLocallyRingedSpace.toTopCat where
  obj V := CommRingCat.of (boundedSubring W V.unop)
  map {V V'} f := CommRingCat.ofHom ((W.left.presheaf.map
    (homOfLE (preim_mono W f.unop.le)).op).hom.restrict _ _
      fun _ hs ↦ map_mem_boundedSubring W f.unop.le hs)
  map_id V := by
    ext s
    change W.left.presheaf.map (homOfLE _).op s.1 = s.1
    rw [Subsingleton.elim (homOfLE _).op (𝟙 _), W.left.presheaf.map_id]
    rfl
  map_comp f g := by
    ext s
    change W.left.presheaf.map (homOfLE _).op s.1 =
      W.left.presheaf.map (homOfLE _).op (W.left.presheaf.map (homOfLE _).op s.1)
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl

lemma extensionPresheaf_map_val {V V' : (disc hB).Opens} (f : V' ⟶ V)
    (s : (extensionPresheaf W).obj (op V)) :
    ((extensionPresheaf W).map f.op s).1 =
      W.left.presheaf.map (homOfLE (preim_mono W f.le)).op s.1 :=
  rfl

lemma mem_preim_iff (V : (disc hB).Opens) (w : W.left) :
    w ∈ preim W V ↔
      ((W.hom.toLRSHom.base w : punctured hB).1 : ULift.{u} (Fin (m + 1)) → ℂ) ∈ coeOpens V :=
  Iff.rfl

variable {W}

/-- **The canonical extension is a sheaf.** -/
theorem isSheaf_extensionPresheaf (hW : IsLocallyOpenInAffine W.left) :
    (extensionPresheaf W).IsSheaf := by
  classical
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro ι U sf hsf
  have hcomp (i j : ι) (w : W.left) (hi : w ∈ preim W (U i)) (hj : w ∈ preim W (U j)) :
      W.left.eval w hi (sf i).1 = W.left.eval w hj (sf j).1 := by
    obtain ⟨hx, h₁⟩ := (mem_coeOpens_iff _ _).1 ((mem_preim_iff W _ w).1 hi)
    obtain ⟨hx', h₂⟩ := (mem_coeOpens_iff _ _).1 ((mem_preim_iff W _ w).1 hj)
    have hij : w ∈ preim W (U i ⊓ U j) := (mem_coeOpens_iff _ _).2 ⟨hx, h₁, h₂⟩
    have := congrArg (fun s : (extensionPresheaf W).obj (op (U i ⊓ U j)) ↦
      W.left.eval w hij s.1) (hsf i j)
    exact (eval_presheaf_map W.left _ w hij (sf i).1).symm.trans
      (this.trans (eval_presheaf_map W.left _ w hij (sf j).1))
  let f : W.left → ℂ := fun w ↦
    if h : ∃ i, w ∈ preim W (U i) then W.left.eval w h.choose_spec (sf h.choose).1 else 0
  have hf (i : ι) (w : W.left) (hw : w ∈ preim W (U i)) : f w = W.left.eval w hw (sf i).1 := by
    have h : ∃ i, w ∈ preim W (U i) := ⟨i, hw⟩
    simp only [f, dif_pos h]
    exact hcomp _ _ _ _ _
  have hcov (w : W.left) (hw : w ∈ preim W (iSup U)) : ∃ i, w ∈ preim W (U i) := by
    obtain ⟨hx, hV⟩ := (mem_coeOpens_iff _ _).1 ((mem_preim_iff W _ w).1 hw)
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 hV
    exact ⟨i, (mem_coeOpens_iff _ _).2 ⟨hx, hi⟩⟩
  obtain ⟨s, hs⟩ := exists_eval_eq_of_local hW (O := preim W (iSup U)) f fun w hw ↦ by
    obtain ⟨i, hi⟩ := hcov w hw
    exact ⟨preim W (U i), hi, preim_mono W (le_iSup U i), (sf i).1,
      fun w' hw' ↦ (hf i w' hw').symm⟩
  have hsb : s ∈ boundedSubring W (iSup U) := by
    intro x hx hx0
    obtain ⟨hxd, hV⟩ := (mem_coeOpens_iff _ _).1 hx
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 hV
    have hxi : x ∈ coeOpens (U i) := (mem_coeOpens_iff _ _).2 ⟨hxd, hi⟩
    obtain ⟨N, hN, M, hM⟩ := (sf i).2 x hxi hx0
    refine ⟨N ∩ coeOpens (U i), inter_mem hN ((isOpen_coeOpens _).mem_nhds hxi), M,
      fun w hw hwN ↦ ?_⟩
    rw [hs w hw, hf i w hwN.2]
    exact hM w hwN.2 hwN.1
  refine ⟨⟨s, hsb⟩, fun i ↦ Subtype.ext ?_, fun s' hs' ↦ Subtype.ext ?_⟩
  · change W.left.presheaf.map _ s = _
    refine eq_of_forall_eval_eq hW fun w hw ↦ ?_
    exact (eval_presheaf_map W.left _ w hw s).trans ((hs _ _).trans (hf i w hw))
  · refine eq_of_forall_eval_eq hW fun w hw ↦ ?_
    obtain ⟨i, hi⟩ := hcov w hw
    have := congrArg (fun s : (extensionPresheaf W).obj (op (U i)) ↦ W.left.eval w hi s.1)
      (hs' i)
    exact (eval_presheaf_map W.left _ w hi s'.1).symm.trans
      (this.trans ((hf i w hi).symm.trans (hs w hw).symm))

variable (W) in
/-- **The canonical extension** `𝒞̄` of `p_* 𝒪_W` across `t = 0`, as a sheaf of rings on `S`. -/
def extensionSheaf (hW : IsLocallyOpenInAffine W.left) :
    TopCat.Sheaf CommRingCat.{u} (disc hB).toLocallyRingedSpace.toTopCat :=
  ⟨extensionPresheaf W, isSheaf_extensionPresheaf hW⟩

end

end ComplexAnalytic.KummerModel
