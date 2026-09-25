/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.ES.Codim2.BPointConfig

/-!
# Coherence of bounded sections at a b-point

Keep the notation of `Oka/Analytification/RET/ES/Codim2/BPointConfig.lean`: near a b-point, `N°`
is the complement in `N` of the zero set of a monic polynomial `P(x)(w)` which is separable over
`t ≠ 0` (`ComplexAnalytic.BoundedSections.BPointData`). Then the sheaf `𝒜` of bounded sections of
every Hausdorff finite étale cover `W` of `N°` is coherent
(`ComplexAnalytic.BoundedSections.BPointData.isCoherent`).

The proof:

1. Remove `t = 0` from `N°`: the bounded sections of `W` and of its restriction `W⁻` to
   `N° ∩ {t ≠ 0}` agree (`ComplexAnalytic.BoundedSections.isCoherentAt_of_restrict`).
2. After the Puiseux base change `α : t ↦ tˢ`, the preimage of `N ∖ (N° ∩ {t ≠ 0})` is a graph
   configuration (`…BPointData.PuiseuxData.config`), so the bounded sections of the base change
   `W'` of `W⁻` are coherent (`ComplexAnalytic.BoundedSections.GraphConfig.isCoherent`).
3. Near a point `x₀` with `t = 0` (where `α⁻¹(x₀) = {x₀}`), local generators of `𝒜'` near `x₀`
   span local bases of `𝒜'` at all points off `S' = {t = 0} ∩ α⁻¹(N ∖ N°)`, where at most one
   graph passes. Their averages over the roots of unity
   (`ComplexAnalytic.BoundedSections.IsPuiseuxPullback.isFreeSpanAt_avgSec`) span local bases of
   `𝒜⁻` off `Σ = {t = 0, P(x)(w) = 0}`, the zero set of the regular pair `(t, P(x)(w))`, and the
   reflexive hull criterion applies.
4. Near a point with `t ≠ 0`, `𝒜'` is free near a point over it, and `𝒜⁻` is free by
   `ComplexAnalytic.BoundedSections.IsPuiseuxPullback.isFreeSpanAt_avgSec_of_ne_zero`.

## Main results

- `ComplexAnalytic.BoundedSections.BPointData.isCoherent`: `𝒜` is coherent.
-/

open CategoryTheory Opposite AlgebraicGeometry Topology TopologicalSpace Filter Set Metric
  Polynomial Kummer

universe u

namespace ComplexAnalytic.BoundedSections

open AnalyticSpace AlgebraicGeometry.LocallyRingedSpace

noncomputable section

variable {n : ℕ}

/-- **Freeness in the span of local generators**: if `𝒜` is free near `y` and the sections `σᵢ`
generate `𝒜` locally near `y`, then `𝒜` is free near `y` with a basis in the span of the `σᵢ`. -/
theorem isFreeSpanAt_of_locGen {N N₀ : (AnalyticSpace.complexAffineSpace.{u} n).Opens}
    {h₀ : N₀ ≤ N} {W : FiniteEtaleOver (space N₀)} {U : (space N).Opens} {m : ℕ}
    {σ : Fin m → (boundedModule h₀ W).val.obj (op U)} {y : space N} {U₂ : (space N).Opens}
    {m₂ : ℕ} {e : Fin m₂ → (boundedModule h₀ W).val.obj (op U₂)} (he : IsFreeSpanAt h₀ W e y)
    (hyU : y ∈ U)
    (hgen : ∀ (W'' : (space N).Opens) (h : W'' ≤ U) (t : (boundedModule h₀ W).val.obj (op W'')),
      y ∈ W'' → ∃ (W''' : (space N).Opens) (h' : W''' ≤ W''), y ∈ W''' ∧
        ∃ c : Fin m → (space N).presheaf.obj (op W'''),
          sectRes (boundedModule h₀ W) h' t =
            ∑ i, c i • sectRes (boundedModule h₀ W) (h'.trans h) (σ i)) :
    IsFreeSpanAt h₀ W σ y := by
  obtain ⟨V, -, r, b, -, hyV, -, hspan, hindep⟩ := he
  have h₁ : V ⊓ U ≤ V := inf_le_left
  have h₂ : V ⊓ U ≤ U := inf_le_right
  choose Wk hWk hyWk c hc using fun k ↦
    hgen (V ⊓ U) h₂ (sectRes (boundedModule h₀ W) h₁ (b k)) ⟨hyV, hyU⟩
  let V' : (space N).Opens := (V ⊓ U) ⊓
    ⟨⋂ k, (Wk k : Set (space N)), isOpen_iInter_of_finite fun k ↦ (Wk k).isOpen⟩
  have hV'V : V' ≤ V ⊓ U := inf_le_left
  have hV'W : ∀ k, V' ≤ Wk k := fun k x hx ↦ Set.mem_iInter.1 hx.2 k
  refine isFreeSpanAt_of_basis h₂ (fun k ↦ sectRes (boundedModule h₀ W) h₁ (b k))
    (fun V'' h a ↦ ?_) (fun V'' h c' hc' ↦ hindep V'' (h.trans h₁) c' ?_) hV'V
    ⟨⟨hyV, hyU⟩, Set.mem_iInter.2 hyWk⟩ (fun k i ↦ (space N).res (hV'W k) (c k i)) fun k ↦ ?_
  · obtain ⟨c', hc'⟩ := hspan V'' (h.trans h₁) a
    exact ⟨c', by simpa only [sectRes_sectRes] using hc'⟩
  · simpa only [sectRes_sectRes] using hc'
  · have := congrArg (sectRes (boundedModule h₀ W) (hV'W k)) (hc k)
    rw [sectRes_sectRes, sectRes_sum_smul] at this
    simp only [sectRes_sectRes] at this ⊢
    exact this

namespace BPointData

variable {N N₀ : (AnalyticSpace.complexAffineSpace.{u} n).Opens} (d : BPointData N N₀)

/-! ### The zero set of `P(x)(w)` -/

lemma interior_val_eq_zero : interior ({x : Cn.{u} n | x ∈ N} ∩ d.val ⁻¹' {0}) = ∅ := by
  refine eq_empty_of_forall_notMem fun x hx ↦ d.not_eventually_val x ?_
  filter_upwards [isOpen_interior.mem_nhds hx] with y hy _
  exact (interior_subset hy).2

lemma val_eq_zero_of_not_mem {x : Cn.{u} n} (hx : x ∈ N) (hx₀ : x ∉ N₀) : d.val x = 0 := by
  by_contra h
  exact hx₀ ((d.mem_iff x hx).2 h)

/-- **The complement of `N° ∩ {t ≠ 0}` is thin**: it lies in the zero set of `t P(x)(w)`. -/
theorem hasThinComplement : HasThinComplement N d.N₀t := by
  refine ⟨(fun x : Cn.{u} n ↦ x d.it) * d.val, ?_, ?_, fun x hx hx₀ ↦ ?_⟩
  · exact (differentiable_apply d.it).differentiableOn.mul
      (d.differentiableOn_val.mono fun x hx ↦ d.subset_region x hx)
  · exact interior_inter_preimage_zero_mul_eq_empty (continuous_apply d.it).continuousOn
      (subset_empty_iff.1 ((interior_mono inter_subset_right).trans
        (interior_setOf_apply_eq_zero d.it).subset)) d.interior_val_eq_zero
  · have hx₀' : ¬(x ∈ N₀ ∧ x d.it ≠ 0) := hx₀
    rw [not_and_or, not_not] at hx₀'
    rcases hx₀' with h | h
    · simp [d.val_eq_zero_of_not_mem hx h]
    · simp [h]

/-- **Freeness off `N ∖ N°` along `t = 0`**: near a point of `N°`, the complement of
`N° ∩ {t ≠ 0}` is `{t = 0}`. -/
theorem exists_isFreeSpanAt_of_mem (h₀ : N₀ ≤ N) (W : FiniteEtaleOver (space d.N₀t))
    [T2Space W.left] {x₀ : Cn.{u} n} (hx₀ : x₀ ∈ N₀) :
    ∃ (U : (space N).Opens) (k : ℕ)
      (e : Fin k → (boundedModule (d.N₀t_le.trans h₀) W).val.obj (op U)),
      x₀ ∈ img U ∧ ∀ y ∈ U, IsFreeSpanAt (d.N₀t_le.trans h₀) W e y :=
  exists_isFreeSpanAt_of_form (d.N₀t_le.trans h₀) W d.it_ne_iw isOpen_univ
    (fun _ _ _ ↦ mem_univ _) (ψ₀ := fun _ ↦ 0) (fun _ _ ↦ rfl) (differentiableOn_const 0)
    (isOpen_setOf_mem N₀) (subset_univ _) (fun x hx ↦ h₀ hx) True False
    (fun x hx ↦ d.mem_N₀t.trans (by simp [show x ∈ N₀ from hx])) hx₀

/-! ### Descent along the Puiseux base change -/

variable (h₀ : N₀ ≤ N) (D : d.PuiseuxData) (W : FiniteEtaleOver (space d.N₀t)) [T2Space W.left]

include D in
/-- **Freeness near a point with `t ≠ 0`**: `𝒜'` is free near a point over it, and the spread of
a local basis descends to a local basis. -/
theorem isCoherentAt_of_ne_zero {x₀ : space N} (ht : x₀.1 d.it ≠ 0) :
    IsCoherentAt (d.N₀t_le.trans h₀) W x₀ := by
  classical
  have hN₀' : ∀ x, x ∈ D.N₀' ↔ coordPow d.it D.s x ∈ d.N₀t := D.mem_N₀'_iff
  have hN : ∀ x, x ∈ D.N' ↔ coordPow d.it D.s x ∈ N := fun _ ↦ Iff.rfl
  have P := isPuiseuxPullback_puiseuxCover hN₀' W D.pos
  set W' := puiseuxCover hN₀' W
  set c := D.config
  set h₀' := D.N₀'_le h₀
  -- a point over `x₀` and a local basis there
  set y₁ := coordRoot d.it D.s x₀.1
  have hy₁ : coordPow d.it D.s y₁ = x₀.1 := coordPow_coordRoot D.pos.ne' _
  have hy₁N : y₁ ∈ D.N' := (hN y₁).2 (hy₁ ▸ x₀.2)
  have hy₁t : y₁ d.it ≠ 0 := fun h ↦ ht (by
    rw [← hy₁, coordPow_self, h, zero_pow D.pos.ne'])
  obtain ⟨Ue, k, e, hy₁Ue, hfreeE⟩ := c.exists_isFreeSpanAt_of_subsingleton h₀' W' hy₁N
    fun i j hi hj ↦ by
      by_contra hij
      exact c.ψ_ne_of_ne hij (mem_cyl_of_mem hy₁N) hy₁t (hi.trans hj.symm)
  obtain ⟨Vb, -, r, b, -, hy₁Vb, -, hspan, hindep⟩ :=
    hfreeE ⟨y₁, hy₁N⟩ (mem_img_iff.1 hy₁Ue).2
  obtain ⟨V₀, P₀, hV₀, hP₀Vb, hP⟩ := exists_isPiece D.pos hy₁t
    ((img Vb).isOpen.mem_nhds (mem_img_iff.2 ⟨hy₁N, hy₁Vb⟩))
  rw [hy₁] at hV₀
  -- the point over `x₀` in the piece
  obtain ⟨l, hl, -⟩ := hP.existsUnique y₁ (by rw [mem_preimage, hy₁]; exact hV₀)
  set y₂ := coordRot d.it (zeta D.s ^ (l : ℕ)) y₁
  have hy₂ : coordPow d.it D.s y₂ = x₀.1 := by
    rw [coordPow_coordRot (zeta_pow_pow D.pos _), hy₁]
  have hy₂Vb : y₂ ∈ img Vb := hP₀Vb hl
  have hy₂N : y₂ ∈ D.N' := img_le Vb _ hy₂Vb
  -- the spread of the basis
  let V : (space N).Opens := ⟨Subtype.val ⁻¹' V₀, hP.isOpen.preimage continuous_subtype_val⟩
  have hV : ∀ x ∈ img V, x ∈ V₀ := fun x hx ↦ (mem_img_iff.1 hx).2
  have hx₀V : x₀ ∈ V := hV₀
  let σ : Fin r → (boundedModule h₀' W').val.obj (op (pullOpens d.it D.s D.N' V)) :=
    fun k ↦ P.spread hN hP hP₀Vb hV (b k)
  obtain ⟨Q, hQVb, hQpull, hy₂Q, hQP⟩ : ∃ Q : (space D.N').Opens, Q ≤ Vb ∧
      Q ≤ pullOpens d.it D.s D.N' V ∧ (⟨y₂, hy₂N⟩ : space D.N') ∈ Q ∧ ∀ z ∈ Q, z.1 ∈ P₀ :=
    ⟨Vb ⊓ pullOpens d.it D.s D.N' V ⊓ ⟨Subtype.val ⁻¹' P₀,
      hP.isOpen_piece.preimage continuous_subtype_val⟩, inf_le_left.trans inf_le_left,
      inf_le_left.trans inf_le_right, ⟨⟨(mem_img_iff.1 hy₂Vb).2,
        show coordPow d.it D.s y₂ ∈ img V by rw [hy₂]; exact mem_img_iff.2 ⟨x₀.2, hx₀V⟩⟩, hl⟩,
      fun _ hz ↦ hz.2⟩
  have hfree : IsFreeSpanAt h₀' W' σ ⟨y₂, hy₂N⟩ := by
    refine isFreeSpanAt_of_basis hQpull
      (fun k ↦ sectRes (boundedModule h₀' W') hQVb (b k))
      (fun V'' h a ↦ ?_) (fun V'' h c' hc' ↦ hindep V'' (h.trans hQVb) c' ?_) le_rfl hy₂Q
      (fun k i ↦ if k = i then 1 else 0) fun k ↦ ?_
    · obtain ⟨c', hc'⟩ := hspan V'' (h.trans hQVb) a
      exact ⟨c', by simpa only [sectRes_sectRes] using hc'⟩
    · simpa only [sectRes_sectRes] using hc'
    · simp only [ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      refine secVal_ext h₀' W' fun w hw ↦ ?_
      have hwP : pt W' w ∈ P₀ := by
        have := hQP _ ((mem_preim_iff h₀' W').1 hw |> mem_img_iff.1).2
        exact this
      have hwpull : w ∈ preim h₀' W' (pullOpens d.it D.s D.N' V) := preim_mono h₀' W' hQpull hw
      rw [evalFun_secVal_sectRes _ _ hw, evalFun_secVal_sectRes _ _ hw]
      exact (P.evalFun_spread_of_mem hN hP hP₀Vb hV (b k) hwpull hwP).symm.trans
        (evalFun_secVal_sectRes (h₀ := h₀') (W := W') hQpull (σ k) hw).symm
  exact isCoherentAt_of_isFreeSpanAt _ _
    (P.isFreeSpanAt_avgSec_of_ne_zero hN σ hx₀V ht hy₂ hfree)

lemma coordPow_of_eq_zero {x : Cn.{u} n} (ht : x d.it = 0) : coordPow d.it D.s x = x := by
  rw [coordPow, ht, zero_pow D.pos.ne', ← ht, Function.update_eq_self]

include D in
/-- **Coherence near a point with `t = 0`**: local generators of `𝒜'` near the unique point over
it span local bases off `{t = 0} ∩ α⁻¹(N ∖ N°)`; their averages span local bases of `𝒜` off the
zero set of the regular pair `(t, P(x)(w))`. -/
theorem isCoherentAt_of_eq_zero {x₀ : space N} (ht : x₀.1 d.it = 0) :
    IsCoherentAt (d.N₀t_le.trans h₀) W x₀ := by
  classical
  have hN₀' : ∀ x, x ∈ D.N₀' ↔ coordPow d.it D.s x ∈ d.N₀t := D.mem_N₀'_iff
  have hN : ∀ x, x ∈ D.N' ↔ coordPow d.it D.s x ∈ N := fun _ ↦ Iff.rfl
  have P := isPuiseuxPullback_puiseuxCover hN₀' W D.pos
  set W' := puiseuxCover hN₀' W
  set c := D.config
  set h₀' := D.N₀'_le h₀
  have hx₀N' : x₀.1 ∈ D.N' := (hN _).2 ((d.coordPow_of_eq_zero D ht).symm ▸ x₀.2)
  -- local generators upstairs
  obtain ⟨V', m, σ₀, hx₀V', hgen⟩ :=
    (IsCoherentAt.of_isCoherent h₀' W' (c.isCoherent h₀' W') ⟨x₀.1, hx₀N'⟩).1
  -- a neighbourhood of `x₀` whose preimage lies in `V'`
  obtain ⟨x₁, hx₁⟩ : ∃ x₁ : Cn.{u} n, x₁ = x₀.1 := ⟨_, rfl⟩
  have ht₁ : x₁ d.it = 0 := hx₁ ▸ ht
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (img V').isOpen x₁
    (hx₁ ▸ mem_img_iff.2 ⟨hx₀N', hx₀V'⟩)
  have hδ : 0 < min ε (ε ^ D.s) := lt_min hε (pow_pos hε _)
  let U : (space N).Opens := opensOf N (isOpen_ball (x := x₁) (ε := min ε (ε ^ D.s)))
  have hx₀U : x₀ ∈ U := by
    have hmem : x₁ ∈ ball x₁ (min ε (ε ^ D.s)) := mem_ball_self hδ
    nth_rewrite 2 [hx₁] at hmem
    exact hmem
  have hUV' : pullOpens d.it D.s D.N' U ≤ V' := fun y hy ↦ by
    obtain ⟨y₁, hy₁⟩ : ∃ y₁ : Cn.{u} n, y₁ = y.1 := ⟨_, rfl⟩
    have h₁ : coordPow d.it D.s y₁ ∈ ball x₁ (min ε (ε ^ D.s)) := hy₁ ▸ (mem_img_iff.1 hy).2
    have h₂ : y₁ ∈ ball x₁ ε := by
      rw [mem_ball, dist_pi_lt_iff hε]
      rw [mem_ball, dist_pi_lt_iff hδ] at h₁
      intro j
      have hj := h₁ j
      by_cases hjt : j = d.it
      · subst hjt
        rw [coordPow_self, ht₁, dist_zero_right, norm_pow] at hj
        rw [ht₁, dist_zero_right]
        exact (pow_lt_pow_iff_left₀ (norm_nonneg _) hε.le D.pos.ne').1
          (hj.trans_le (min_le_right _ _))
      · rw [coordPow_of_ne _ _ hjt] at hj
        exact hj.trans_le (min_le_left _ _)
    have := (mem_img_iff.1 (hball h₂)).2
    rwa [show (⟨y₁, _⟩ : space D.N') = y from Subtype.ext hy₁] at this
  let σ : Fin m → (boundedModule h₀' W').val.obj (op (pullOpens d.it D.s D.N' U)) :=
    fun i ↦ sectRes (boundedModule h₀' W') hUV' (σ₀ i)
  -- freeness upstairs off `S' = {t = 0} ∩ α⁻¹(N ∖ N°)`
  set S' : Set (Cn.{u} n) := {x | x d.it = 0 ∧ ∃ j, x d.iw = D.ψ j x}
  have hfree : ∀ y' ∈ pullOpens d.it D.s D.N' U, y'.1 ∉ S' → IsFreeSpanAt h₀' W' σ y' := by
    intro y' hy' hyS
    have hsub : ∀ i j, c.ψ i y'.1 = y'.1 c.iw → c.ψ j y'.1 = y'.1 c.iw → i = j := by
      intro i j hi hj
      by_cases ht' : y'.1 d.it = 0
      · exact absurd ⟨ht', i, hi.symm⟩ hyS
      · by_contra hij
        exact c.ψ_ne_of_ne hij (mem_cyl_of_mem y'.2) ht' (hi.trans hj.symm)
    obtain ⟨Ue, k, e, hy'Ue, hfreeE⟩ := c.exists_isFreeSpanAt_of_subsingleton h₀' W' y'.2 hsub
    refine isFreeSpanAt_of_locGen (hfreeE y' (mem_img_iff.1 hy'Ue).2) hy'
      fun W'' h t hy'W ↦ ?_
    obtain ⟨W''', h', hy''', c', hc'⟩ := hgen W'' (h.trans hUV') t y' hy'W
    exact ⟨W''', h', hy''', c', by rw [hc']; simp only [σ, sectRes_sectRes]⟩
  -- freeness downstairs off `Σ = {t = 0, P(x)(w) = 0}`
  have hSig : ∀ y ∈ U, y.1 ∉ {x : Cn.{u} n | x d.it = 0 ∧ d.val x = 0} →
      IsFreeSpanAt (d.N₀t_le.trans h₀) W (P.avgSec hN σ) y := by
    intro y hyU hySig
    refine P.isFreeSpanAt_avgSec hN σ hfree hyU ?_ ?_
    · rintro ⟨x, hxS, hxy⟩
      rw [d.coordPow_of_eq_zero D hxS.1] at hxy
      subst hxy
      refine hySig ⟨hxS.1, ?_⟩
      obtain ⟨j, hj⟩ := hxS.2
      have hxN' : y.1 ∈ D.N' := (hN _).2 ((d.coordPow_of_eq_zero D hxS.1).symm ▸ y.2)
      have hprod := D.prod_eq_of_mem (mem_cyl_of_mem hxN')
      rw [d.coordPow_of_eq_zero D hxS.1] at hprod
      rw [val, hprod, eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ j) (by rw [eval_sub, eval_X, eval_C, hj, sub_self])
    · by_cases hyt : y.1 d.it = 0
      · right
        have hyN₀ : y.1 ∈ N₀ := (d.mem_iff y.1 y.2).2 fun h ↦ hySig ⟨hyt, h⟩
        obtain ⟨U₂, k, e, hyU₂, hfreeE⟩ := d.exists_isFreeSpanAt_of_mem h₀ W hyN₀
        exact ⟨U₂, k, e, hfreeE y (mem_img_iff.1 hyU₂).2⟩
      · exact Or.inl hyt
  -- the regular pair `(t, P(x)(w))`
  refine isCoherentAt_of_criterion (d.N₀t_le.trans h₀) W d.hasThinComplement
    (RegularPairFamily.ofCoord (img U).isOpen d.it (h := d.val)
      (d.differentiableOn_val.mono fun x hx ↦ d.subset_region x (img_le U x hx))
      fun z _ hzt _ hev ↦ d.not_eventually_val z ?_)
    (P.avgSec hN σ) hx₀U ?_ hSig
  · filter_upwards [hev] with y hy hyt
    exact hy (hyt.trans hzt)
  · rw [RegularPairFamily.ofCoord_zeroSet]

include d in
/-- **Coherence of bounded sections at a b-point.** Let `N°` be the complement in `N` of the zero
set of a monic polynomial `P(x)(w)` in `w`, separable over `t ≠ 0`
(`ComplexAnalytic.BoundedSections.BPointData`). Then the sheaf `𝒜` of bounded sections of every
Hausdorff finite étale cover of `N°` is coherent. -/
theorem isCoherent (h₀ : N₀ ≤ N) (W : FiniteEtaleOver (space N₀)) [T2Space W.left] :
    (boundedModule h₀ W).IsCoherent := by
  obtain ⟨D⟩ := d.nonempty_puiseuxData
  have hp : Function.update (0 : Cn.{u} n) d.it (d.r : ℂ) ∉ N₀ := fun h ↦ by
    have := (d.mem_region _ (h₀ h)).2
    rw [Function.update_self, Complex.norm_real, Real.norm_of_nonneg d.pos.le] at this
    exact lt_irrefl _ this
  have hβ := isMapPullback_mapCover (restrictMap d.N₀t_le hp) W
  refine isCoherent_of_forall_isCoherentAt h₀ W fun x ↦ isCoherentAt_of_restrict
    (h₀ := h₀) d.N₀t_le hβ (fun _ hx ↦ restrictMap_χ d.N₀t_le hp hx)
    (g := fun x : Cn.{u} n ↦ x d.it) (differentiable_apply d.it).differentiableOn
    (subset_empty_iff.1 ((interior_mono inter_subset_right).trans
      (interior_setOf_apply_eq_zero d.it).subset))
    (fun x hx ↦ ⟨fun h ↦ h.2, fun h ↦ ⟨hx, h⟩⟩) ?_
  by_cases ht : x.1 d.it = 0
  · exact d.isCoherentAt_of_eq_zero h₀ D _ ht
  · exact d.isCoherentAt_of_ne_zero h₀ D _ ht

end BPointData

end

end ComplexAnalytic.BoundedSections
