/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.ES.CapExtension.ProjTwist

/-!
# Sections of the twists of the sheaf of the cap from sections of the cap

Keep the notation of `Oka/Analytification/RET/ES/CapExtension/ProjTwist.lean`. Conversely to
`ComplexAnalytic.Cap.AnnulusDecomposition.capPoleOf`, a section `t = (a, (fᵢ))` of the cap with a
pole of order `≤ n` over `B × ℙ¹` gives a section of `𝒞(n)` over `B × ℙ¹`
(`ComplexAnalytic.Cap.AnnulusDecomposition.twistOfCap`): its component in the chart `w` is `a` on
`W` and `w'⁻ⁿ fᵢ` on `K`, its component in the chart `w'` is `w⁻ⁿ a` on `W` and `fᵢ` on `K`.
-/

open CategoryTheory Opposite Topology TopologicalSpace Set Filter Metric

universe u

namespace ComplexAnalytic.Cap.AnnulusDecomposition

open AnalyticSpace BoundedSections relProjectiveSpaceAn relProjectiveLine
open AlgebraicGeometry AlgebraicGeometry.LocallyRingedSpace
open KummerModel (splitEquiv)

noncomputable section

variable {m : ℕ} {N N₀ : (AnalyticSpace.complexAffineSpace.{u} (m + 1)).Opens} (h₀ : N₀ ≤ N)
  {W : FiniteEtaleOver (space N₀)} {F : WeierstrassForm N N₀}
  {D : AnnulusDecomposition W F.G F.ρ} {n : ℕ} {B : Opens (Fin m → ℂ)}

/-! ### Membership lemmas -/

lemma mem_img_tubeN_of_chart0Pt {x : Cn.{u} (m + 1)} (hxN : x ∈ N)
    (hx : chart0Pt x ∈ tube.{u} (N := 1) B) :
    x ∈ img (tubeN N (baseSet.{u} B) isOpen_baseSet) := by
  refine mem_img_iff.2 ⟨hxN, ?_⟩
  change baseY (chartPt.{u} 0 _) ∈ B at hx
  rw [baseY_chartPt] at hx
  exact hx

lemma preimW_tube_le (i : Fin 2) :
    (Opens.map (projW W).toLRSHom.base).obj (tube.{u} (N := 1) B ⊓ stdOpen.{u} m 1 i) ≤
      preim h₀ W (tubeN N (baseSet.{u} B) isOpen_baseSet) := fun w hw ↦ by
  refine (mem_preim_iff h₀ W).2 (mem_img_tubeN_of_chart0Pt (h₀ (pt_mem W w)) ?_)
  have := hw.1
  rwa [SetLike.mem_coe, projW_base] at this

lemma baseOf_pt_toFun (i : D.ι) (z : KummerAnnulus.base F.G F.ρ⁻¹ F.ρ (D.deg i)) :
    baseOf (pt W (D.toFun ⟨i, z⟩)) = z.1.1 := by
  change (splitEquiv m (pt W (D.toFun ⟨i, z⟩))).1 = z.1.1
  rw [D.splitEquiv_pt]

lemma fibOf_pt_toFun (i : D.ι) (z : KummerAnnulus.base F.G F.ρ⁻¹ F.ρ (D.deg i)) :
    fibOf (pt W (D.toFun ⟨i, z⟩)) = z.1.2 ^ (D.deg i : ℕ) := by
  change (splitEquiv m (pt W (D.toFun ⟨i, z⟩))).2 = _
  rw [D.splitEquiv_pt]

lemma ne_zero_of_mem_base {i : D.ι} {z : Cm.{u} m × ℂ}
    (hz : z ∈ KummerAnnulus.base F.G F.ρ⁻¹ F.ρ (D.deg i)) : z.2 ≠ 0 :=
  norm_pos_iff.1 (KummerAnnulus.pos_of_mem_base F.G (inv_nonneg.2 F.pos_ρ.le)
    (D.deg i).ne_zero hz)

include h₀ in
/-- The inverse Kummer coordinates of a point of `W` over `B` and the annulus lie in the domain of
the functions at infinity. -/
lemma invCoord_mem {i : D.ι} {z : KummerAnnulus.base F.G F.ρ⁻¹ F.ρ (D.deg i)} {j : Fin 2}
    (hz : D.toFun ⟨i, z⟩ ∈ (Opens.map (projW W).toLRSHom.base).obj
      (tube.{u} (N := 1) B ⊓ stdOpen.{u} m 1 j)) :
    invCoord z.1 ∈ Kummer.powMap (D.deg i) ⁻¹' (baseSet.{u} B ×ˢ ball (0 : ℂ) F.ρ) := by
  refine ⟨?_, ?_⟩
  · have h := ((mem_preim_iff h₀ W).1 (preimW_tube_le h₀ j hz))
    have h2 := (mem_img_iff.1 h).2
    change baseOf (pt W (D.toFun ⟨i, z⟩)) ∈ baseSet.{u} B at h2
    rw [baseOf_pt_toFun] at h2
    exact h2
  · have h1 : F.ρ⁻¹ < ‖z.1.2‖ ^ (D.deg i : ℕ) := z.2.2.1
    rw [mem_ball_zero_iff]
    change ‖(z.1.2⁻¹) ^ (D.deg i : ℕ)‖ < F.ρ
    rw [norm_pow, norm_inv, inv_pow]
    exact inv_lt_of_inv_lt₀ F.pos_ρ h1

/-! ### The values on `K` -/

open Classical in
/-- The values at infinity of a section of the cap, as a function on `K`. -/
def kFunCap (f : D.ι → Cm.{u} m × ℂ → ℂ) (x : Cn.{u} (m + 1)) : ℂ :=
  ∑ i, if x ∈ D.kPiece i then f i (baseOf x, D.kCoord x) else 0

lemma kFunCap_of_mem (f : D.ι → Cm.{u} m × ℂ → ℂ) {i : D.ι} {x : Cn.{u} (m + 1)}
    (hx : x ∈ D.kPiece i) : kFunCap (D := D) f x = f i (baseOf x, D.kCoord x) := by
  classical
  rw [kFunCap, Finset.sum_eq_single i
    (fun j _ hji ↦ if_neg fun hj ↦ hji (D.eq_of_mem_kPiece hj hx))
    (fun h ↦ absurd (Finset.mem_univ i) h), if_pos hx]

lemma kFunCap_kPt (f : D.ι → Cm.{u} m × ℂ → ℂ) {i : D.ι} {z : Cm.{u} m × ℂ}
    (hz : D.kPt i z ∈ D.kPiece i) : kFunCap (D := D) f (D.kPt i z) = f i z := by
  rw [kFunCap_of_mem f hz, baseOf_kPt, D.kCoord_kPt hz]

lemma baseCoord_mem_of_mem_imgK {j : Fin 2} {x : Cn.{u} (m + 1)}
    (hx : x ∈ img ((Opens.map D.kMap.toLRSHom.base).obj
      (tube.{u} (N := 1) B ⊓ stdOpen.{u} m 1 j))) : baseOf x ∈ baseSet.{u} B := by
  obtain ⟨hxK, hxO⟩ := mem_img_iff.1 hx
  have h : D.kMap.toLRSHom.base ⟨x, hxK⟩ ∈ tube.{u} (N := 1) B := hxO.1
  rw [D.kMap_base] at h
  change baseY (chartPt.{u} 1 _) ∈ B at h
  rw [baseY_chartPt] at h
  exact h

lemma powMap_mem_of_mem_imgK {j : Fin 2} {i : D.ι} {x : Cn.{u} (m + 1)}
    (hx : x ∈ img ((Opens.map D.kMap.toLRSHom.base).obj
      (tube.{u} (N := 1) B ⊓ stdOpen.{u} m 1 j))) (hi : x ∈ D.kPiece i) :
    Kummer.powMap (D.deg i) (baseOf x, D.kCoord x) ∈ baseSet.{u} B ×ˢ ball (0 : ℂ) F.ρ := by
  refine ⟨baseCoord_mem_of_mem_imgK hx, ?_⟩
  rw [mem_ball_zero_iff]
  change ‖D.kCoord x ^ (D.deg i : ℕ)‖ < F.ρ
  rw [← D.kVal_eq_kCoord_pow hi, D.kVal_of_mem hi]
  exact hi.2

lemma isOpen_powMap_preimage (i : D.ι) :
    IsOpen (Kummer.powMap (D.deg i) ⁻¹' (baseSet.{u} B ×ˢ ball (0 : ℂ) F.ρ)) :=
  (Kummer.continuous_powMap _).isOpen_preimage _ (isOpen_baseSet.prod isOpen_ball)

lemma differentiableOn_kFunCap {f : D.ι → Cm.{u} m × ℂ → ℂ}
    (hf : ∀ i, DifferentiableOn ℂ (f i)
      (Kummer.powMap (D.deg i) ⁻¹' (baseSet.{u} B ×ˢ ball (0 : ℂ) F.ρ))) (j : Fin 2) :
    DifferentiableOn ℂ (kFunCap (D := D) f)
      (img ((Opens.map D.kMap.toLRSHom.base).obj (tube.{u} (N := 1) B ⊓ stdOpen.{u} m 1 j))) := by
  intro x hx
  have hxK : x ∈ D.kOpens := img_le _ x hx
  obtain ⟨i, hi⟩ := D.mem_kOpens.1 hxK
  have hd : DifferentiableAt ℂ (f i) (baseOf x, D.kCoord x) :=
    (hf i).differentiableAt ((isOpen_powMap_preimage i).mem_nhds (powMap_mem_of_mem_imgK hx hi))
  have hφ : DifferentiableAt ℂ (fun y : Cn.{u} (m + 1) ↦ (baseOf y, D.kCoord y)) x :=
    (differentiable_baseOf x).prodMk (D.differentiableOn_kCoord.differentiableAt
      ((D.kOpens).isOpen.mem_nhds hxK))
  refine ((hd.comp x hφ).congr_of_eventuallyEq ?_).differentiableWithinAt
  filter_upwards [(D.isOpen_kPiece i).mem_nhds hi] with y hy
  exact kFunCap_of_mem f hy

lemma kVal_ne_zero_of_mem_imgK0 {x : Cn.{u} (m + 1)}
    (hx : x ∈ img ((Opens.map D.kMap.toLRSHom.base).obj
      (tube.{u} (N := 1) B ⊓ stdOpen.{u} m 1 0))) : D.kVal x ≠ 0 := by
  obtain ⟨hxK, hxO⟩ := mem_img_iff.1 hx
  have h := hxO.2
  change D.kMap.toLRSHom.base _ ∈ stdOpen.{u} m 1 0 at h
  rw [D.kMap_base] at h
  exact (chartPt_one_mem_stdOpen_zero_iff _).1 h

/-! ### Boundedness -/

/-- A section of `𝒪_W` over the preimage of an open `O` of `P^an` which is bounded near every
point of `N ∖ N°` in `O`, in the coordinates of `ℂ^{m+1}`, is bounded near `removedW`. -/
lemma isBoundedNear_of_forall {O : (relProjectiveSpaceAn.{u} m 1).Opens}
    (a : W.left.presheaf.obj (op ((Opens.map (projW W).toLRSHom.base).obj O)))
    (ha : ∀ x ∈ N, x ∉ N₀ → chart0Pt x ∈ O → ∃ M ∈ 𝓝 x, ∃ C : ℝ,
      ∀ w, w ∈ (Opens.map (projW W).toLRSHom.base).obj O → pt W w ∈ M → ‖evalFun a w‖ ≤ C) :
    IsBoundedNear (projW W) (removedW N N₀) a := by
  rintro p hp ⟨x, ⟨hxN, hxN₀⟩, rfl⟩
  obtain ⟨M, hM, C, hC⟩ := ha x hxN hxN₀ hp
  have hopen : IsOpen (chart0Pt.{u} '' interior M) := by
    have : chart0Pt.{u} (m := m) = chartPt 0 ∘ chartCoordHomeo := rfl
    rw [this, Set.image_comp]
    exact (isOpenEmbedding_chartPt 0).isOpenMap _ (chartCoordHomeo.isOpenMap _ isOpen_interior)
  refine ⟨_, hopen.mem_nhds ⟨x, mem_interior_iff_mem_nhds.2 hM, rfl⟩, C, fun w hw hwM ↦ ?_⟩
  obtain ⟨x', hx'M, hx'⟩ := hwM
  rw [projW_base] at hx'
  have hpt : pt W w = x' := chart0Pt_injective hx'.symm
  have h1 := hC w hw (hpt ▸ interior_subset hx'M)
  rw [evalFun_of_mem a hw] at h1
  exact h1

variable {t : boundedSubring h₀ W (tubeN N (baseSet.{u} B) isOpen_baseSet) ×
    (D.ι → Cm.{u} m × ℂ → ℂ)}

/-! ### The component in the chart `w` -/

/-- The values on `W` of the component in the chart `w`. -/
def capA0 (t : boundedSubring h₀ W (tubeN N (baseSet.{u} B) isOpen_baseSet) ×
    (D.ι → Cm.{u} m × ℂ → ℂ)) :
    W.left.presheaf.obj (op ((Opens.map (projW W).toLRSHom.base).obj
      (tube.{u} (N := 1) B ⊓ stdOpen.{u} m 1 0))) :=
  W.left.presheaf.map (homOfLE (preimW_tube_le h₀ 0)).op t.1.1

lemma evalFun_capA0 {w : W.left} (hw : w ∈ (Opens.map (projW W).toLRSHom.base).obj
    (tube.{u} (N := 1) B ⊓ stdOpen.{u} m 1 0)) :
    evalFun (capA0 h₀ t) w = evalFun t.1.1 w :=
  evalFun_map W _ _ hw

lemma isBoundedNear_capA0 : IsBoundedNear (projW W) (removedW N N₀) (capA0 h₀ t) := by
  refine isBoundedNear_of_forall _ fun x hxN hxN₀ hx ↦ ?_
  obtain ⟨M, hM, C, -, hC⟩ := exists_bound_of_mem_boundedSubring t.1.2
    (mem_img_tubeN_of_chart0Pt hxN hx.1) hxN₀
  refine ⟨M, hM, C, fun w hw hwM ↦ ?_⟩
  rw [evalFun_capA0 h₀ hw]
  exact hC w hwM ((mem_preim_iff h₀ W).1 (preimW_tube_le h₀ 0 hw))

/-- The values on `K` of the component in the chart `w`. -/
def capG0 (ht : t ∈ D.capPole h₀ n (tubeN N (baseSet.{u} B) isOpen_baseSet)
    (baseSet.{u} B ×ˢ ball 0 F.ρ)) :
    (space D.kOpens).presheaf.obj (op ((Opens.map D.kMap.toLRSHom.base).obj
      (tube.{u} (N := 1) B ⊓ stdOpen.{u} m 1 0))) :=
  OkaRing.ofDifferentiableOn (fun x ↦ (D.kVal x)⁻¹ ^ n * kFunCap t.2 x)
    (fun x hx ↦ (((D.differentiableOn_kVal x (img_le _ x hx)).mono fun y hy ↦ img_le _ y hy).inv
      (kVal_ne_zero_of_mem_imgK0 hx)).pow n |>.mul (differentiableOn_kFunCap ht.1 0 x hx))

lemma holFun_capG0 (ht : t ∈ D.capPole h₀ n (tubeN N (baseSet.{u} B) isOpen_baseSet)
    (baseSet.{u} B ×ˢ ball 0 F.ρ)) {x : Cn.{u} (m + 1)}
    (hx : x ∈ img ((Opens.map D.kMap.toLRSHom.base).obj
      (tube.{u} (N := 1) B ⊓ stdOpen.{u} m 1 0))) :
    holFun (capG0 h₀ ht) x = (D.kVal x)⁻¹ ^ n * kFunCap t.2 x :=
  holFun_ofDifferentiableOn _ hx

lemma capA0_compat (ht : t ∈ D.capPole h₀ n (tubeN N (baseSet.{u} B) isOpen_baseSet)
    (baseSet.{u} B ×ˢ ball 0 F.ρ)) (i : D.ι) (z : KummerAnnulus.base F.G F.ρ⁻¹ F.ρ (D.deg i))
    (hz : D.toFun ⟨i, z⟩ ∈ (Opens.map (projW W).toLRSHom.base).obj
      (tube.{u} (N := 1) B ⊓ stdOpen.{u} m 1 0)) :
    evalFun (capA0 h₀ t) (D.toFun ⟨i, z⟩) = holFun (capG0 h₀ ht) (D.kPt i (invCoord z.1)) := by
  have hiK := D.kPt_invCoord_mem z.2
  rw [evalFun_capA0 h₀ hz, holFun_capG0 h₀ ht (kPt_mem_img hz), kFunCap_kPt _ hiK,
    D.kVal_kPt hiK, ← D.kummerVal_of_mem _ _ z.2,
    ht.2 i z.1 ⟨z.2, preimW_tube_le h₀ 0 hz⟩ (invCoord_mem h₀ hz)]
  simp only [invCoord, inv_pow, inv_inv, ← pow_mul, mul_comm]

/-- **The component in the chart `w`** of the section of `𝒞(n)` given by `t`. -/
def cap0 (ht : t ∈ D.capPole h₀ n (tubeN N (baseSet.{u} B) isOpen_baseSet)
    (baseSet.{u} B ×ˢ ball 0 F.ρ)) :
    D.capModule.val.obj (op (tube.{u} (N := 1) B ⊓ stdOpen.{u} m 1 0)) :=
  D.mkCap (capA0 h₀ t) (isBoundedNear_capA0 h₀) (capG0 h₀ ht) (capA0_compat h₀ ht)

/-! ### The component in the chart `w'` -/

lemma fibOf_ne_zero_of_mem {w : W.left} (hw : w ∈ (Opens.map (projW W).toLRSHom.base).obj
    (tube.{u} (N := 1) B ⊓ stdOpen.{u} m 1 1)) : fibOf (pt W w) ≠ 0 := by
  have h := hw.2
  change (projW W).toLRSHom.base w ∈ stdOpen.{u} m 1 1 at h
  rw [projW_base, chart0Pt] at h
  exact (chartPt_zero_mem_stdOpen_one_iff _).1 h

lemma isHolOn_capA1 : IsHolOn W (fun w ↦ (fibOf (pt W w))⁻¹ ^ n * evalFun t.1.1 w)
    ((Opens.map (projW W).toLRSHom.base).obj (tube.{u} (N := 1) B ⊓ stdOpen.{u} m 1 1)) :=
  (isHolOn_comp_pt (G := {x | fibOf x ≠ 0}) (isOpen_ne_fun continuous_fibOf continuous_const)
      (fun x hx ↦ ((differentiable_fibOf x).inv hx).pow n |>.differentiableWithinAt)
      fun _ hw ↦ fibOf_ne_zero_of_mem hw).mul
    ((isHolOn_evalFun t.1.1).mono fun _ hw ↦ preimW_tube_le h₀ 1 hw)

/-- The values on `W` of the component in the chart `w'`. -/
def capA1 (t : boundedSubring h₀ W (tubeN N (baseSet.{u} B) isOpen_baseSet) ×
    (D.ι → Cm.{u} m × ℂ → ℂ)) :
    W.left.presheaf.obj (op ((Opens.map (projW W).toLRSHom.base).obj
      (tube.{u} (N := 1) B ⊓ stdOpen.{u} m 1 1))) :=
  (isHolOn_capA1 h₀ (t := t) (n := n)).exists_eval_eq.choose

lemma evalFun_capA1 {w : W.left} (hw : w ∈ (Opens.map (projW W).toLRSHom.base).obj
    (tube.{u} (N := 1) B ⊓ stdOpen.{u} m 1 1)) :
    evalFun (capA1 h₀ (n := n) t) w = (fibOf (pt W w))⁻¹ ^ n * evalFun t.1.1 w := by
  rw [evalFun_of_mem _ hw]
  exact (isHolOn_capA1 h₀ (t := t) (n := n)).exists_eval_eq.choose_spec w hw

lemma isBoundedNear_capA1 : IsBoundedNear (projW W) (removedW N N₀) (capA1 h₀ (n := n) t) := by
  refine isBoundedNear_of_forall _ fun x hxN hxN₀ hx ↦ ?_
  have hx0 : fibOf x ≠ 0 := by
    have h := hx.2
    change chartPt.{u} 0 _ ∈ stdOpen.{u} m 1 1 at h
    exact (chartPt_zero_mem_stdOpen_one_iff _).1 h
  obtain ⟨M, hM, C, -, hC⟩ := exists_bound_of_mem_boundedSubring t.1.2
    (mem_img_tubeN_of_chart0Pt hxN hx.1) hxN₀
  have hc : ContinuousAt (fun x' : Cn.{u} (m + 1) ↦ (fibOf x')⁻¹ ^ n) x :=
    ((continuous_fibOf.continuousAt).inv₀ hx0).pow n
  refine ⟨M ∩ {x' | ‖(fibOf x')⁻¹ ^ n‖ < ‖(fibOf x)⁻¹ ^ n‖ + 1},
    inter_mem hM (hc.norm.preimage_mem_nhds (Iio_mem_nhds (lt_add_one _))),
    (‖(fibOf x)⁻¹ ^ n‖ + 1) * C, fun w hw hwM ↦ ?_⟩
  rw [evalFun_capA1 h₀ hw, norm_mul]
  exact mul_le_mul hwM.2.le (hC w hwM.1 ((mem_preim_iff h₀ W).1 (preimW_tube_le h₀ 1 hw)))
    (norm_nonneg _) (by positivity)

/-- The values on `K` of the component in the chart `w'`. -/
def capG1 (ht : t ∈ D.capPole h₀ n (tubeN N (baseSet.{u} B) isOpen_baseSet)
    (baseSet.{u} B ×ˢ ball 0 F.ρ)) :
    (space D.kOpens).presheaf.obj (op ((Opens.map D.kMap.toLRSHom.base).obj
      (tube.{u} (N := 1) B ⊓ stdOpen.{u} m 1 1))) :=
  OkaRing.ofDifferentiableOn _ (differentiableOn_kFunCap ht.1 1)

lemma capA1_compat (ht : t ∈ D.capPole h₀ n (tubeN N (baseSet.{u} B) isOpen_baseSet)
    (baseSet.{u} B ×ˢ ball 0 F.ρ)) (i : D.ι) (z : KummerAnnulus.base F.G F.ρ⁻¹ F.ρ (D.deg i))
    (hz : D.toFun ⟨i, z⟩ ∈ (Opens.map (projW W).toLRSHom.base).obj
      (tube.{u} (N := 1) B ⊓ stdOpen.{u} m 1 1)) :
    evalFun (capA1 h₀ (n := n) t) (D.toFun ⟨i, z⟩) =
      holFun (capG1 h₀ ht) (D.kPt i (invCoord z.1)) := by
  have hiK := D.kPt_invCoord_mem z.2
  have hz0 := ne_zero_of_mem_base z.2
  rw [evalFun_capA1 h₀ hz, capG1, holFun_ofDifferentiableOn _ (kPt_mem_img hz),
    kFunCap_kPt _ hiK, fibOf_pt_toFun, ← D.kummerVal_of_mem _ _ z.2,
    ht.2 i z.1 ⟨z.2, preimW_tube_le h₀ 1 hz⟩ (invCoord_mem h₀ hz), inv_pow, ← pow_mul,
    mul_comm (D.deg i : ℕ) n, inv_mul_cancel_left₀ (pow_ne_zero _ hz0)]

/-- **The component in the chart `w'`** of the section of `𝒞(n)` given by `t`. -/
def cap1 (ht : t ∈ D.capPole h₀ n (tubeN N (baseSet.{u} B) isOpen_baseSet)
    (baseSet.{u} B ×ˢ ball 0 F.ρ)) :
    D.capModule.val.obj (op (tube.{u} (N := 1) B ⊓ stdOpen.{u} m 1 1)) :=
  D.mkCap (capA1 h₀ t) (isBoundedNear_capA1 h₀) (capG1 h₀ ht) (capA1_compat h₀ ht)

variable (ht : t ∈ D.capPole h₀ n (tubeN N (baseSet.{u} B) isOpen_baseSet)
    (baseSet.{u} B ×ˢ ball 0 F.ρ))

lemma capWVal_cap0 {w : W.left} (hw : w ∈ (Opens.map (projW W).toLRSHom.base).obj
    (tube.{u} (N := 1) B ⊓ stdOpen.{u} m 1 0)) :
    capWVal (cap0 h₀ ht) w = evalFun t.1.1 w := by
  rw [cap0, capWVal_mkCap, evalFun_capA0 h₀ hw]

lemma capKVal_cap0 {x : Cn.{u} (m + 1)} (hx : x ∈ img ((Opens.map D.kMap.toLRSHom.base).obj
    (tube.{u} (N := 1) B ⊓ stdOpen.{u} m 1 0))) :
    capKVal (cap0 h₀ ht) x = (D.kVal x)⁻¹ ^ n * kFunCap t.2 x := by
  rw [cap0, capKVal_mkCap, holFun_capG0 h₀ ht hx]

lemma capWVal_cap1 {w : W.left} (hw : w ∈ (Opens.map (projW W).toLRSHom.base).obj
    (tube.{u} (N := 1) B ⊓ stdOpen.{u} m 1 1)) :
    capWVal (cap1 h₀ ht) w = (fibOf (pt W w))⁻¹ ^ n * evalFun t.1.1 w := by
  rw [cap1, capWVal_mkCap, evalFun_capA1 h₀ hw]

lemma capKVal_cap1 {x : Cn.{u} (m + 1)} (hx : x ∈ img ((Opens.map D.kMap.toLRSHom.base).obj
    (tube.{u} (N := 1) B ⊓ stdOpen.{u} m 1 1))) :
    capKVal (cap1 h₀ ht) x = kFunCap t.2 x := by
  rw [cap1, capKVal_mkCap, capG1, holFun_ofDifferentiableOn _ hx]

omit h₀ ht in
/-- The value in the chart `0` of the transition function of `𝒪(n)` from the chart `0` to the
chart `1`. -/
lemma eval_twistModCocycle_one_zero {O : (relProjectiveSpaceAn.{u} m 1).Opens}
    (hO : O ≤ stdOpen.{u} m 1 1 ⊓ stdOpen.{u} m 1 0) (k : ℤ) {p : (Fin m → ℂ) × ℂ}
    (hp : chartPt.{u} 0 p ∈ O) :
    (relProjectiveSpaceAn.{u} m 1).eval (chartPt.{u} 0 p) hp
      (TopCat.Presheaf.restrictOpen ((twistModCocycle.{u} m 1 k).g 1 0) O hO) =
      (p.2 ^ k)⁻¹ := by
  have hO' : O ≤ stdOpen.{u} m 1 0 ⊓ stdOpen.{u} m 1 1 := fun x hx ↦ ⟨(hO hx).2, (hO hx).1⟩
  have h := congrArg ((relProjectiveSpaceAn.{u} m 1).eval (chartPt.{u} 0 p) hp)
    ((twistModCocycle.{u} m 1 k).mul_res_symm 0 1 O hO')
  rw [map_mul, map_one, eval_twistModCocycle hO' k hp] at h
  exact (eq_inv_of_mul_eq_one_right h)

omit ht in
lemma projW_eq_chartPt (w : W.left) :
    (projW W).toLRSHom.base w = chartPt.{u} 0 (baseCoord (baseOf (pt W w)), fibOf (pt W w)) :=
  projW_base W w

/-! ### Gluing the components -/

/-- The overlap of the two charts over `B`, in the order `(1, 0)`. -/
abbrev tubeOverlap' (B : Opens (Fin m → ℂ)) : (relProjectiveSpaceAn.{u} m 1).Opens :=
  tube.{u} (N := 1) B ⊓ (stdOpen.{u} m 1 1 ⊓ stdOpen.{u} m 1 0)

omit ht in
lemma tubeOverlap'_le (i : Fin 2) :
    tubeOverlap'.{u} B ≤ tube.{u} (N := 1) B ⊓ stdOpen.{u} m 1 i := by
  fin_cases i
  exacts [inf_le_inf_left _ inf_le_right, inf_le_inf_left _ inf_le_left]

lemma cap_compat01 :
    modRes (cap0 h₀ ht) (tubeOverlap.{u} B) (tubeOverlap_le 0) =
      TopCat.Presheaf.restrictOpen ((twistModCocycle.{u} m 1 (n : ℤ)).g 0 1) (tubeOverlap.{u} B)
        inf_le_right • modRes (cap1 h₀ ht) (tubeOverlap.{u} B) (tubeOverlap_le 1) := by
  refine capModule_ext (fun w hw ↦ ?_) (fun x hx ↦ ?_)
  · erw [capWVal_res _ _ hw, capWVal_smul _ _ hw, capWVal_res _ _ hw]
    rw [capWVal_cap0 h₀ ht (tubeOverlap_le 0 hw), capWVal_cap1 h₀ ht (tubeOverlap_le 1 hw),
      eval_congr_point (projW_eq_chartPt w) hw ((projW_eq_chartPt w) ▸ hw),
      eval_twistModCocycle, zpow_natCast, ← mul_assoc, ← mul_pow,
      mul_inv_cancel₀ (fibOf_ne_zero_of_mem (tubeOverlap_le 1 hw)), one_pow, one_mul]
  · erw [capKVal_res _ _ hx, capKVal_smul _ _ hx, capKVal_res _ _ hx]
    rw [capKVal_cap0 h₀ ht (img_mono ((Opens.map _).monotone (tubeOverlap_le 0)) hx),
      capKVal_cap1 h₀ ht (img_mono ((Opens.map _).monotone (tubeOverlap_le 1)) hx)]
    obtain ⟨-, hp⟩ := kMap_mem_tubeOverlap hx
    rw [eval_congr_point hp _ (hp ▸ (mem_img_iff.1 hx).2), eval_twistModCocycle, zpow_natCast]

lemma cap_compat10 :
    modRes (cap1 h₀ ht) (tubeOverlap'.{u} B) (tubeOverlap'_le 1) =
      TopCat.Presheaf.restrictOpen ((twistModCocycle.{u} m 1 (n : ℤ)).g 1 0) (tubeOverlap'.{u} B)
        inf_le_right • modRes (cap0 h₀ ht) (tubeOverlap'.{u} B) (tubeOverlap'_le 0) := by
  have hle : tubeOverlap'.{u} B ≤ tubeOverlap.{u} B := fun p hp ↦ ⟨hp.1, hp.2.2, hp.2.1⟩
  refine capModule_ext (fun w hw ↦ ?_) (fun x hx ↦ ?_)
  · erw [capWVal_res _ _ hw, capWVal_smul _ _ hw, capWVal_res _ _ hw]
    rw [capWVal_cap0 h₀ ht (tubeOverlap'_le 0 hw), capWVal_cap1 h₀ ht (tubeOverlap'_le 1 hw),
      eval_congr_point (projW_eq_chartPt w) hw ((projW_eq_chartPt w) ▸ hw),
      eval_twistModCocycle_one_zero, zpow_natCast, inv_pow]
  · erw [capKVal_res _ _ hx, capKVal_smul _ _ hx, capKVal_res _ _ hx]
    rw [capKVal_cap0 h₀ ht (img_mono ((Opens.map _).monotone (tubeOverlap'_le 0)) hx),
      capKVal_cap1 h₀ ht (img_mono ((Opens.map _).monotone (tubeOverlap'_le 1)) hx)]
    have hx' := img_mono ((Opens.map D.kMap.toLRSHom.base).monotone hle) hx
    obtain ⟨h0, hp⟩ := kMap_mem_tubeOverlap hx'
    rw [eval_congr_point hp _ (hp ▸ (mem_img_iff.1 hx).2), eval_twistModCocycle_one_zero,
      zpow_natCast, ← mul_assoc, inv_pow, inv_inv, mul_inv_cancel₀ (pow_ne_zero _ h0), one_mul]

/-- The components of the section of `𝒞(n)` given by `t`. -/
def capComp : ∀ i : Fin 2, D.capModule.val.obj (op (tube.{u} (N := 1) B ⊓ stdOpen.{u} m 1 i))
  | ⟨0, _⟩ => cap0 h₀ ht
  | ⟨1, _⟩ => cap1 h₀ ht

/-- **The section of `𝒞(n)` given by a section of the cap with a pole of order `≤ n`.** -/
def twistOfCap : (twistMod D.capModule (n : ℤ)).val.obj (op (tube.{u} (N := 1) B)) :=
  modTwistMk (c := twistModCocycle.{u} m 1 (n : ℤ)) (capComp h₀ ht) fun i j ↦ by
    by_cases hij : i = j
    · subst hij
      rw [(twistModCocycle.{u} m 1 (n : ℤ)).self_res _ _ inf_le_right, one_smul]
    · fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · exact cap_compat01 h₀ ht
      · exact cap_compat10 h₀ ht
      · exact absurd rfl hij

/-- **The component in the chart `w`** of the section of `𝒞(n)` given by `t` has the values of `t`
on `W`. -/
lemma capWVal_twComp_twistOfCap {w : W.left} (hw : w ∈ (Opens.map (projW W).toLRSHom.base).obj
    (tube.{u} (N := 1) B ⊓ stdOpen.{u} m 1 0)) :
    capWVal (twComp (twistOfCap h₀ ht) 0) w = evalFun t.1.1 w := by
  rw [twComp, modTwistSectionsEquiv_apply, modTwistComp_res]
  have hw2 : w ∈ (Opens.map (projW W).toLRSHom.base).obj
      (tube.{u} (N := 1) B ⊓ stdOpen.{u} m 1 0 ⊓ stdOpen.{u} m 1 0) := ⟨hw, hw.2⟩
  erw [capWVal_res _ _ hw, capWVal_res _ _ hw2]
  exact capWVal_cap0 h₀ ht hw

end

end ComplexAnalytic.Cap.AnnulusDecomposition
