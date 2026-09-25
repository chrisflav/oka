/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.ES.CapExtension.Setup

/-!
# The evaluation of sections of the cap has saturated image

Keep the notation of `Oka/Analytification/RET/ES/CapExtension/Setup.lean`. Let `wᵥ`, `ν < M`, be
distinct points of the annulus with `M > n ∑ kᵢ`, and let `λ` be the evaluation of sections of the
cap on the sheets over the points `(b, wᵥ)`
(`ComplexAnalytic.Cap.AnnulusDecomposition.evalVec`). The coefficients of the characteristic
polynomial of a section `t` of the cap with a pole of order `≤ n` at infinity are polynomials of
degree `≤ n ∑ kᵢ` in `w`, hence given by Lagrange interpolation from the values of `λ(t)`
(`ComplexAnalytic.Cap.AnnulusDecomposition.coeff_charPolyFun_eq_sum`).

Consequently the image of `λ` is saturated
(`ComplexAnalytic.Cap.AnnulusDecomposition.exists_capPole_evalVec_eq_of_mul`): if `λ(t) = c v`
for a function `c` of `b` whose zero set has empty interior and a holomorphic `v`, then `v = λ(t')`
for a section `t'`. Off `{c = 0}`, `t' = t / c`; its characteristic polynomial has coefficients
given by Lagrange interpolation from `v`, which are holomorphic across `{c = 0}`, so `t'` is bounded
and extends by the Riemann extension theorem on `W`. The functions at infinity extend by the
maximum principle along the fibres of the Kummer covers.
-/

open CategoryTheory Opposite Topology Set Filter Polynomial Metric

universe u


namespace ComplexAnalytic.BoundedSections

open AnalyticSpace

noncomputable section

variable {n : ℕ} {N₀ : (AnalyticSpace.complexAffineSpace.{u} n).Opens}
  {W : FiniteEtaleOver (space N₀)} {E : Set (Cn.{u} n)} {g : Cn.{u} n → ℂ}

/-- **Riemann extension on `W`** across the zero set of a function `g` holomorphic on an open `E`
containing the image of `O`, whose zero set has empty interior in `E`. -/
theorem exists_isHolOn_extension_of_isOpen (hE : IsOpen E) (hg : DifferentiableOn ℂ g E)
    (hgZ : interior (E ∩ g ⁻¹' {0}) = ∅) {O : W.left.Opens} (hOE : ∀ w ∈ O, pt W w ∈ E)
    {f : W.left → ℂ} (hf : IsHolOn W f {w | w ∈ O ∧ g (pt W w) ≠ 0})
    (hb : ∀ w ∈ O, g (pt W w) = 0 → ∃ M ∈ 𝓝 (pt W w), ∃ C, ∀ w', w' ∈ O → pt W w' ∈ M →
      g (pt W w') ≠ 0 → ‖f w'‖ ≤ C) :
    ∃ F : W.left → ℂ, IsHolOn W F O ∧ ∀ w ∈ O, g (pt W w) ≠ 0 → F w = f w := by
  classical
  have hT : IsOpen (E ∩ g ⁻¹' {0}ᶜ) :=
    hg.continuousOn.isOpen_inter_preimage hE isOpen_compl_singleton
  let O₀ : W.left.Opens := O ⊓ ⟨pt W ⁻¹' (E ∩ g ⁻¹' {0}ᶜ), hT.preimage (continuous_pt W)⟩
  have hO₀ : ∀ w, w ∈ O₀ ↔ w ∈ O ∧ g (pt W w) ≠ 0 := fun w ↦
    ⟨fun h ↦ ⟨h.1, h.2.2⟩, fun h ↦ ⟨h.1, hOE w h.1, h.2⟩⟩
  obtain ⟨b₀, hb₀⟩ := (hf.mono fun w hw ↦ (hO₀ w).1 hw).exists_eval_eq (O := O₀)
  have hint : ∀ D ⊆ E, interior (D ∩ g ⁻¹' {0}) = ∅ := fun D hD ↦
    subset_empty_iff.1 (hgZ ▸ interior_mono (inter_subset_inter_left _ hD))
  have hloc : ∀ w ∈ O, ∃ S : W.left.Opens, w ∈ S ∧ ∃ F : Cn.{u} n → ℂ,
      DifferentiableOn ℂ F (pt W '' ((S ⊓ O : W.left.Opens) : Set W.left)) ∧
      ∀ v ∈ S ⊓ O, g (pt W v) ≠ 0 → F (pt W v) = f v := by
    intro w hw
    obtain ⟨S, hwS, -, hsheet⟩ := exists_sheet W w
    obtain ⟨F, hFd, hF⟩ := hsheet (O' := S ⊓ O₀) inf_le_left
      (W.left.presheaf.map (homOfLE inf_le_right).op b₀)
    have hF' : ∀ v ∈ S ⊓ O, g (pt W v) ≠ 0 → F (pt W v) = f v := fun v hv hgv ↦ by
      have hv₀ : v ∈ S ⊓ O₀ := ⟨hv.1, (hO₀ v).2 ⟨hv.2, hgv⟩⟩
      rw [← hF v hv₀, eval_presheaf_map, hb₀]
    set D := pt W '' ((S ⊓ O : W.left.Opens) : Set W.left)
    have hDo : IsOpen D := isOpenMap_pt W _ (S ⊓ O).isOpen
    have hDE : D ⊆ E := by
      rintro _ ⟨v, hv, rfl⟩
      exact hOE v hv.2
    have hFD : DifferentiableOn ℂ F (D \ g ⁻¹' {0}) := by
      rintro _ ⟨⟨v, hv, rfl⟩, hgv⟩
      exact (hFd v ⟨hv.1, (hO₀ v).2 ⟨hv.2, hgv⟩⟩).differentiableWithinAt
    have hbdd : ∀ z ∈ D, IsBoundedUnder (· ≤ ·) (𝓝[D \ g ⁻¹' {0}] z) fun x ↦ ‖F x‖ := by
      rintro _ ⟨v, hv, rfl⟩
      by_cases hgv : g (pt W v) = 0
      · obtain ⟨M, hM, C, hC⟩ := hb v hv.2 hgv
        refine ⟨C, eventually_map.2 ?_⟩
        filter_upwards [nhdsWithin_le_nhds hM, self_mem_nhdsWithin] with x hxM hx
        obtain ⟨⟨v', hv', rfl⟩, hgv'⟩ := hx
        rw [hF' v' hv' hgv']
        exact hC v' hv'.2 hxM hgv'
      · have hc : ContinuousAt F (pt W v) :=
          (hFd v ⟨hv.1, (hO₀ v).2 ⟨hv.2, hgv⟩⟩).continuousAt
        exact IsBoundedUnder.mono nhdsWithin_le_nhds hc.norm.tendsto.isBoundedUnder_le
    obtain ⟨F', hF'd, hF'F⟩ := exists_differentiableOn_eqOn_of_isBoundedUnder hDo
      (hg.mono hDE) (hint D hDE) hFD hbdd
    refine ⟨S, hwS, F', hF'd, fun v hv hgv ↦ ?_⟩
    rw [hF'F ⟨⟨v, hv, rfl⟩, hgv⟩, hF' v hv hgv]
  choose! S hwS F hFd hFf using hloc
  have hcons : ∀ w₁ ∈ O, ∀ w₂ ∈ O, ∀ v ∈ S w₁ ⊓ S w₂ ⊓ O, F w₁ (pt W v) = F w₂ (pt W v) := by
    intro w₁ hw₁ w₂ hw₂ v hv
    set D := pt W '' ((S w₁ ⊓ S w₂ ⊓ O : W.left.Opens) : Set W.left)
    have hD₁ : D ⊆ pt W '' ((S w₁ ⊓ O : W.left.Opens) : Set W.left) :=
      image_mono fun v' hv' ↦ ⟨hv'.1.1, hv'.2⟩
    have hD₂ : D ⊆ pt W '' ((S w₂ ⊓ O : W.left.Opens) : Set W.left) :=
      image_mono fun v' hv' ↦ ⟨hv'.1.2, hv'.2⟩
    have hDE : D ⊆ E := by
      rintro _ ⟨v', hv', rfl⟩
      exact hOE v' hv'.2
    refine EqOn.of_eqOn_diff_zero (isOpenMap_pt W _ (S w₁ ⊓ S w₂ ⊓ O).isOpen)
      (hint D hDE) ((hFd w₁ hw₁).continuousOn.mono hD₁)
      ((hFd w₂ hw₂).continuousOn.mono hD₂) (fun x hx ↦ ?_) ⟨v, hv, rfl⟩
    obtain ⟨⟨v', hv', rfl⟩, hgv'⟩ := hx
    rw [hFf w₁ hw₁ v' ⟨hv'.1.1, hv'.2⟩ hgv', hFf w₂ hw₂ v' ⟨hv'.1.2, hv'.2⟩ hgv']
  refine ⟨fun w ↦ F w (pt W w), fun w hw ↦ ⟨F w, ?_⟩, fun w hw hgw ↦ hFf w hw w ⟨hwS w hw, hw⟩ hgw⟩
  filter_upwards [(S w ⊓ O).isOpen.mem_nhds ⟨hwS w hw, hw⟩] with v hv
  refine ⟨(hFd w hw).differentiableAt ((isOpenMap_pt W _ (S w ⊓ O).isOpen).mem_nhds
    ⟨v, hv, rfl⟩), ?_⟩
  exact (hcons v hv.2 w hw v ⟨⟨hwS v hv.2, hv.1⟩, hv.2⟩)

/-- Points of `W` off the zero set of `g ∘ p` accumulate at every point over `E`. -/
lemma frequently_ne_zero_of_isOpen (hgZ : interior (E ∩ g ⁻¹' {0}) = ∅) {O : W.left.Opens}
    (hOE : ∀ w ∈ O, pt W w ∈ E) {w : W.left} (hw : w ∈ O) : ∃ᶠ w' in 𝓝 w, g (pt W w') ≠ 0 := by
  intro hev
  obtain ⟨U, hUw, hUo, hwU⟩ := eventually_nhds_iff.1 (hev.mono fun _ h ↦ not_not.1 h)
  have hsub : pt W '' (U ∩ O) ⊆ interior (E ∩ g ⁻¹' {0}) :=
    interior_maximal (by rintro _ ⟨v, hv, rfl⟩; exact ⟨hOE v hv.2, hUw v hv.1⟩)
      (isOpenMap_pt W _ (hUo.inter O.isOpen))
  rw [hgZ] at hsub
  exact hsub ⟨w, ⟨hwU, hw⟩, rfl⟩

end

end ComplexAnalytic.BoundedSections

namespace ComplexAnalytic.Cap.AnnulusDecomposition

open AnalyticSpace BoundedSections Complex.ProjectiveLineBundle
open KummerModel (splitEquiv)

noncomputable section

variable {m : ℕ} {N N₀ : (AnalyticSpace.complexAffineSpace.{u} (m + 1)).Opens} (h₀ : N₀ ≤ N)
  {W : FiniteEtaleOver (space N₀)} [T2Space W.left] {F : WeierstrassForm N N₀}
  (D : AnnulusDecomposition W F.G F.ρ)

/-- The polynomial `∏_{(i, j)} (T - vᵥᵢⱼ)` of the values at the node `ν`. -/
def nodePoly {M : ℕ} (v : Fin M × (Σ i, Fin (D.deg i)) → ℂ) (ν : Fin M) : ℂ[X] :=
  ∏ ij : Σ i, Fin (D.deg i), (X - C (v (ν, ij)))

/-- **Lagrange interpolation for characteristic polynomials**: the `l`-th coefficient of the
characteristic polynomial of a section `t` of the cap with a pole of order `≤ n` at a point `x` of
`N°` over `V` is `∑ᵥ coeff_l(∏ (T - λ(t)(b)ᵥᵢⱼ)) Lᵥ(w)`, `Lᵥ` the Lagrange basis of the nodes. -/
theorem coeff_charPolyFun_eq_sum {n : ℕ} {V : Set (Cm.{u} m)} {hV : IsOpen V} (hVG : V ⊆ F.G)
    {t : boundedSubring h₀ W (tubeN N V hV) × (D.ι → Cm.{u} m × ℂ → ℂ)}
    (ht : t ∈ D.capPole h₀ n (tubeN N V hV) (V ×ˢ ball 0 F.ρ)) {M : ℕ}
    (hM : (∑ i, (D.deg i : ℕ)) * n < M) {w : Fin M → ℂ} (hw : Function.Injective w)
    (hwρ : ∀ ν, w ν ∈ overlap F.ρ) (l : ℕ) {x : Cn.{u} (m + 1)}
    (hx : x ∈ img (tubeN N V hV)) (hxN : x ∈ N₀) :
    (charPolyFun W (evalFun t.1.1) x).coeff l =
      ∑ ν, (D.nodePoly (D.evalVec w t.1.1 (baseOf x)) ν).coeff l *
        (Lagrange.basis Finset.univ w ν).eval (fibOf x) := by
  classical
  have hD := F.hasThinComplement
  have hρ := F.one_lt_ρ
  have hV' := F.mem_img_tubeN (hV := hV) hVG
  have hxb : (splitEquiv m).symm (baseOf x, fibOf x) = x := mkPt_baseOf_fibOf x
  have hb' : baseOf x ∈ V := ((hV' x).1 hx).1
  have hfib : fibOf x ∈ ball (0 : ℂ) F.ρ := ((hV' x).1 hx).2
  generalize baseOf x = b at hxb hb' ⊢
  have hb : b ∈ V := hb'
  have hmemV (w' : ℂ) (hw' : ‖w'‖ < F.ρ) :
      (splitEquiv m).symm (b, w') ∈ img (tubeN N V hV) := by
    rw [hV', Homeomorph.apply_symm_apply]
    exact ⟨hb, mem_ball_zero_iff.2 hw'⟩
  have hmemN (w' : ℂ) (hw' : w' ∈ overlap F.ρ) : (splitEquiv m).symm (b, w') ∈ N₀ :=
    F.annulusRegion_subset _ (by
      rw [annulusRegion, mem_preimage, Homeomorph.apply_symm_apply]
      exact ⟨hVG hb, hw'⟩)
  have hchar (w' : ℂ) (hw' : w' ∈ overlap F.ρ) :
      charPolyFun W (evalFun t.1.1) ((splitEquiv m).symm (b, w')) =
        ∏ ij : Σ i, Fin (D.deg i), (X - C (D.sheetVal (w₁ := w') t.1.1 ij.1 ij.2 (b, w'))) := by
    obtain ⟨ε, hε0, hε⟩ := Metric.isOpen_iff.1 (isOpen_overlap F.ρ) _ hw'
    have hz : (b, w') ∈ discRegion F.G w' ε := ⟨hVG hb, mem_ball_self hε0⟩
    rw [D.charPolyFun_eq_prod_sheet hε hz]
    exact Finset.prod_congr rfl fun ij _ ↦ by rw [D.evalFun_sheet hε]
  obtain ⟨r, hr⟩ := exists_coeff_charPolyFun hD t.1.2 l
  have hφ (i : D.ι) : DifferentiableOn ℂ (fun u ↦ t.2 i (b, u))
      {u | ‖u ^ (D.deg i : ℕ)‖ < F.ρ} :=
    (ht.1 i).comp ((differentiable_const b).prodMk differentiable_id).differentiableOn
      fun u hu ↦ ⟨hb, mem_ball_zero_iff.2 hu⟩
  have hA : DifferentiableOn ℂ (fun w' ↦ holFun r ((splitEquiv m).symm (b, w')))
      (ball 0 F.ρ) :=
    fun w' hw' ↦ ((differentiableOn_holFun r).differentiableAt ((img _).isOpen.mem_nhds
      (hmemV w' (mem_ball_zero_iff.1 hw')))).comp_differentiableWithinAt w'
        ((differentiable_splitEquiv_symm.comp ((differentiable_const b).prodMk
          differentiable_id)).differentiableAt.differentiableWithinAt)
  have hAB : ∀ w' ∈ overlap F.ρ, holFun r ((splitEquiv m).symm (b, w')) =
      infCoeff D.deg n (fun i u ↦ t.2 i (b, u)) l w' w' := by
    intro w' hw'
    rw [hr _ (hmemV w' hw'.2) (hmemN w' hw'), hchar w' hw', infCoeff]
    have hprod : ∏ ij : Σ i, Fin (D.deg i),
        (X - C (D.sheetVal (w₁ := w') t.1.1 ij.1 ij.2 (b, w'))) =
        ∏ ij : Σ i, Fin (D.deg i), (X - C (w' ^ n * t.2 ij.1
          (b, (Kummer.zeta (D.deg ij.1) ^ (ij.2 : ℕ) * kroot (D.deg ij.1) w' w')⁻¹))) :=
      Finset.prod_congr rfl fun ij _ ↦ by
        rw [D.sheetVal_eq_of_mem_capPole hVG hV' ht hb hw' ij.1 ij.2]
    rw [hprod]
  have key := eq_sum_lagrange_of_infCoeff F.one_lt_ρ hφ hA hAB hM hw
    (fun ν ↦ mem_ball_zero_iff.2 (hwρ ν).2) hfib
  rw [hxb, hr _ hx hxN] at key
  rw [key]
  apply Finset.sum_congr rfl
  intro ν _
  rw [hr _ (hmemV _ (hwρ ν).2) (hmemN _ (hwρ ν)), hchar _ (hwρ ν)]
  rfl

omit [T2Space W.left] in
/-- **Division of a section of the cap by a nonvanishing function of the base.** -/
theorem exists_capPole_inv_mul {n : ℕ} {V V₀ : Set (Cm.{u} m)} {hV : IsOpen V} {hV₀ : IsOpen V₀}
    (hVG : V ⊆ F.G) (hV₀V : V₀ ⊆ V)
    {t : boundedSubring h₀ W (tubeN N V hV) × (D.ι → Cm.{u} m × ℂ → ℂ)}
    (ht : t ∈ D.capPole h₀ n (tubeN N V hV) (V ×ˢ ball 0 F.ρ)) {c : Cm.{u} m → ℂ}
    (hc : DifferentiableOn ℂ c V₀) (hc0 : ∀ b ∈ V₀, c b ≠ 0) :
    ∃ t₀ ∈ D.capPole h₀ n (tubeN N V₀ hV₀) (V₀ ×ˢ ball 0 F.ρ),
      (∀ y ∈ preim h₀ W (tubeN N V₀ hV₀),
        evalFun t₀.1.1 y = (c (baseOf (pt W y)))⁻¹ * evalFun t.1.1 y) ∧
      ∀ i x, t₀.2 i x = (c x.1)⁻¹ * t.2 i x := by
  have hVG₀ : V₀ ⊆ F.G := hV₀V.trans hVG
  have hle : tubeN N V₀ hV₀ ≤ tubeN N V hV := tubeN_mono hV₀V
  obtain ⟨ci, hci, hcie, hci2⟩ := D.exists_const_mem_capSubring (h₀ := h₀)
    (V := tubeN N V₀ hV₀) (U := V₀) (F.mem_img_tubeN hVG₀) (c := fun b ↦ (c b)⁻¹)
    (hc.inv hc0)
  have htr := D.capRestrict_mem_capPole h₀ hle
    (prod_mono hV₀V subset_rfl : V₀ ×ˢ ball (0 : ℂ) F.ρ ⊆ V ×ˢ ball 0 F.ρ) ht
  refine ⟨ci * D.capRestrict h₀ hle t, D.mul_mem_capPole_of_mem_capSubring hci htr,
    fun y hy ↦ ?_, fun i x ↦ ?_⟩
  · change evalFun (ci.1.1 * W.left.presheaf.map (homOfLE (preim_mono h₀ W hle)).op t.1.1) y = _
    rw [evalFun_mul W _ _ hy, hcie y hy, evalFun_map W _ _ hy]
  · change ci.2 i x * t.2 i x = _
    rw [hci2]

omit [T2Space W.left] in
/-- Near a point of `E`, finitely many continuous functions are uniformly bounded. -/
lemma exists_nhds_bound {E : Set (Cn.{u} (m + 1))} (hE : IsOpen E) {d : ℕ}
    {Q : ℕ → Cn.{u} (m + 1) → ℂ} (hQ : ∀ l, ContinuousOn (Q l) E) {x₀ : Cn.{u} (m + 1)}
    (hx₀ : x₀ ∈ E) : ∃ M ∈ 𝓝 x₀, ∃ A : ℝ, ∀ x ∈ M, ∀ l < d, ‖Q l x‖ ≤ A := by
  have hev : ∀ᶠ x in 𝓝 x₀, ∀ l ∈ Finset.range d, ‖Q l x‖ ≤ ‖Q l x₀‖ + 1 := by
    refine (Filter.eventually_all_finset _).2 fun l _ ↦ ?_
    have hc := ((hQ l).continuousAt (hE.mem_nhds hx₀)).norm
    filter_upwards [hc.eventually (gt_mem_nhds (lt_add_one _))] with z hz using hz.le
  refine ⟨_, hev, ∑ l ∈ Finset.range d, (‖Q l x₀‖ + 1), fun x hx l hl ↦ ?_⟩
  exact (hx l (Finset.mem_range.2 hl)).trans (Finset.single_le_sum
    (f := fun l ↦ ‖Q l x₀‖ + 1) (fun _ _ ↦ by positivity) (Finset.mem_range.2 hl))

omit [T2Space W.left] in
lemma interior_inter_baseOf_eq_empty {V : Set (Cm.{u} m)} {hV : IsOpen V} {c : Cm.{u} m → ℂ}
    (hcZ : interior (V ∩ c ⁻¹' {0}) = ∅) :
    interior ((img (tubeN N V hV) : Set (Cn.{u} (m + 1))) ∩ (c ∘ baseOf) ⁻¹' {0}) = ∅ := by
  refine eq_empty_iff_forall_notMem.2 fun x hx ↦ ?_
  have hopen : IsOpenMap (baseOf (m := m)) := isOpenMap_fst.comp (splitEquiv m).isOpenMap
  have hsub : baseOf '' interior ((img (tubeN N V hV) : Set (Cn.{u} (m + 1))) ∩
      (c ∘ baseOf) ⁻¹' {0}) ⊆ interior (V ∩ c ⁻¹' {0}) := by
    refine interior_maximal ?_ (hopen _ isOpen_interior)
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨hyV, hy0⟩ := interior_subset hy
    exact ⟨(mem_img_iff.1 hyV).2, hy0⟩
  rw [hcZ] at hsub
  exact hsub ⟨x, hx, rfl⟩

omit [T2Space W.left] in
/-- **Extension of a root of a monic polynomial with holomorphic coefficients.** A function `f`,
holomorphic on `W` over `V ∩ {c ≠ 0}` and a root of `Tᵈ + ∑ Qₗ Tˡ` with `Qₗ` holomorphic over `V`,
is the restriction of a section of `𝒜` over `V`. -/
theorem exists_secVal_eq_of_root {V : Set (Cm.{u} m)} {hV : IsOpen V}
    {c : Cm.{u} m → ℂ} (hc : DifferentiableOn ℂ c V) (hcZ : interior (V ∩ c ⁻¹' {0}) = ∅)
    {d : ℕ} {Q : ℕ → Cn.{u} (m + 1) → ℂ}
    (hQ : ∀ l, DifferentiableOn ℂ (Q l) (img (tubeN N V hV))) {f : W.left → ℂ}
    (hf : IsHolOn W f {w | w ∈ preim h₀ W (tubeN N V hV) ∧ c (baseOf (pt W w)) ≠ 0})
    (hroot : ∀ w ∈ preim h₀ W (tubeN N V hV), c (baseOf (pt W w)) ≠ 0 →
      f w ^ d + ∑ l ∈ Finset.range d, Q l (pt W w) * f w ^ l = 0) :
    ∃ a : (boundedModule h₀ W).val.obj (op (tubeN N V hV)),
      ∀ w ∈ preim h₀ W (tubeN N V hV), c (baseOf (pt W w)) ≠ 0 →
        evalFun (secVal h₀ W a) w = f w := by
  set E : Set (Cn.{u} (m + 1)) := (img (tubeN N V hV) : Set (Cn.{u} (m + 1)))
  set O := preim h₀ W (tubeN N V hV)
  have hE : IsOpen E := (img (tubeN N V hV)).isOpen
  have hOE : ∀ w ∈ O, pt W w ∈ E := fun w hw ↦ (mem_preim_iff h₀ W).1 hw
  have hEV : ∀ x ∈ E, baseOf x ∈ V := fun x hx ↦ (mem_img_iff.1 hx).2
  have hg : DifferentiableOn ℂ (c ∘ baseOf) E :=
    hc.comp differentiable_baseOf.differentiableOn fun x hx ↦ hEV x hx
  have hgZ := interior_inter_baseOf_eq_empty (N := N) (hV := hV) hcZ
  have hQc : ∀ l, ContinuousOn (Q l) E := fun l ↦ (hQ l).continuousOn
  obtain ⟨F', hF', hF'f⟩ := exists_isHolOn_extension_of_isOpen hE hg hgZ hOE hf
    fun w hw _ ↦ by
      obtain ⟨M, hM, A, hA⟩ := exists_nhds_bound (d := d) hE hQc (hOE w hw)
      refine ⟨M, hM, max 1 (d * A), fun w' hw' hw'M hgw' ↦ ?_⟩
      exact Kummer.norm_le_of_pow_add_sum_eq_zero (a := fun l ↦ Q l (pt W w'))
        (fun l hl ↦ hA _ hw'M l hl) (hroot w' hw' hgw')
  -- `F'` is a root everywhere
  have hroot' : ∀ w ∈ O, F' w ^ d + ∑ l ∈ Finset.range d, Q l (pt W w) * F' w ^ l = 0 := by
    intro w hw
    by_contra hne
    have hcont : ContinuousAt (fun w' ↦ F' w' ^ d + ∑ l ∈ Finset.range d,
        Q l (pt W w') * F' w' ^ l) w :=
      ((hF'.continuousAt hw).pow d).add (tendsto_finsetSum _ fun l _ ↦
        (((hQc l).continuousAt (hE.mem_nhds (hOE w hw))).comp
          (continuous_pt W).continuousAt).mul ((hF'.continuousAt hw).pow l))
    have hev := (hcont.eventually_ne hne).and (O.isOpen.mem_nhds hw)
    obtain ⟨w', ⟨hw'ne, hw'O⟩, hgw'⟩ :=
      (hev.and_frequently (frequently_ne_zero_of_isOpen hgZ hOE hw)).exists
    exact hw'ne (by rw [hF'f w' hw'O hgw']; exact hroot w' hw'O hgw')
  obtain ⟨a, ha⟩ := exists_secVal_eq h₀ W hF' fun x hx _ ↦ by
    obtain ⟨M, hM, A, hA⟩ := exists_nhds_bound (d := d) hE hQc hx
    refine ⟨M, hM, max 1 (d * A), fun w hwM hwV ↦ ?_⟩
    exact Kummer.norm_le_of_pow_add_sum_eq_zero (a := fun l ↦ Q l (pt W w))
      (fun l hl ↦ hA _ hwM l hl) (hroot' w ((mem_preim_iff h₀ W).2 hwV))
  exact ⟨a, fun w hw hgw ↦ (ha w hw).trans (hF'f w hw hgw)⟩

/-- **Extension of functions on a Kummer cover at infinity across `{c = 0}`.** Let `φ` be
holomorphic on `{(b, u) | b ∈ V, c(b) ≠ 0, ‖uᵏ‖ < ρ}` and equal, on the part over the annulus
`ρ⁻¹ < ‖uᵏ‖ < ρ`, to a function `Φ` continuous there over all of `V`. Then `φ` extends
holomorphically over `{c = 0}`: over the annulus it is bounded by continuity of `Φ`, and near
`u = 0` by the maximum principle on a circle in the annulus. -/
theorem exists_extension_infinity {V : Set (Cm.{u} m)} (hV : IsOpen V) {c : Cm.{u} m → ℂ}
    (hc : DifferentiableOn ℂ c V) (hcZ : interior (V ∩ c ⁻¹' {0}) = ∅) {k : ℕ} (hk : 0 < k)
    {ρ : ℝ} (hρ : 1 < ρ) {φ Φ : Cm.{u} m × ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ {z | z.1 ∈ V ∧ c z.1 ≠ 0 ∧ ‖z.2 ^ k‖ < ρ})
    (hΦ : ContinuousOn Φ {z | z.1 ∈ V ∧ ρ⁻¹ < ‖z.2 ^ k‖ ∧ ‖z.2 ^ k‖ < ρ})
    (hφΦ : ∀ z, z.1 ∈ V → c z.1 ≠ 0 → ρ⁻¹ < ‖z.2 ^ k‖ → ‖z.2 ^ k‖ < ρ → φ z = Φ z) :
    ∃ φ' : Cm.{u} m × ℂ → ℂ, DifferentiableOn ℂ φ' {z | z.1 ∈ V ∧ ‖z.2 ^ k‖ < ρ} ∧
      ∀ z, z.1 ∈ V → c z.1 ≠ 0 → ‖z.2 ^ k‖ < ρ → φ' z = φ z := by
  have hρ0 : 0 < ρ := zero_lt_one.trans hρ
  set U : Set (Cm.{u} m × ℂ) := {z | z.1 ∈ V ∧ ‖z.2 ^ k‖ < ρ}
  have hpow : Continuous fun z : Cm.{u} m × ℂ ↦ ‖z.2 ^ k‖ := (continuous_snd.pow k).norm
  have hU : IsOpen U := (hV.preimage continuous_fst).inter (isOpen_lt hpow continuous_const)
  set A : Set (Cm.{u} m × ℂ) := {z | z.1 ∈ V ∧ ρ⁻¹ < ‖z.2 ^ k‖ ∧ ‖z.2 ^ k‖ < ρ}
  have hA : IsOpen A := (hV.preimage continuous_fst).inter
    ((isOpen_lt continuous_const hpow).inter (isOpen_lt hpow continuous_const))
  have hg : DifferentiableOn ℂ (c ∘ Prod.fst) U :=
    hc.comp differentiableOn_fst fun z hz ↦ hz.1
  have hgZ : interior (U ∩ (c ∘ Prod.fst) ⁻¹' {0}) = ∅ := by
    refine eq_empty_iff_forall_notMem.2 fun z hz ↦ ?_
    have hsub : Prod.fst '' interior (U ∩ (c ∘ Prod.fst) ⁻¹' {0}) ⊆ interior (V ∩ c ⁻¹' {0}) :=
      interior_maximal (by
        rintro _ ⟨y, hy, rfl⟩
        exact ⟨(interior_subset hy).1.1, (interior_subset hy).2⟩) (isOpenMap_fst _ isOpen_interior)
    rw [hcZ] at hsub
    exact hsub ⟨z, hz, rfl⟩
  have hdiff : U \ (c ∘ Prod.fst) ⁻¹' {0} = {z | z.1 ∈ V ∧ c z.1 ≠ 0 ∧ ‖z.2 ^ k‖ < ρ} := by
    ext z
    simp only [U, Set.mem_sdiff, mem_setOf_eq, mem_preimage, Function.comp_apply, mem_singleton_iff]
    tauto
  -- the circle in the annulus
  set s : ℝ := (ρ⁻¹ + 1) / 2
  have hs₁ : ρ⁻¹ < s := by
    have := inv_lt_one_of_one_lt₀ hρ
    simp only [s]
    linarith
  have hs₂ : s < ρ := by
    have := inv_lt_one_of_one_lt₀ hρ
    simp only [s]
    linarith
  have hs0 : 0 < s := (inv_pos.2 hρ0).trans hs₁
  set r : ℝ := s ^ ((k : ℝ)⁻¹)
  have hr0 : 0 < r := Real.rpow_pos_of_pos hs0 _
  have hrk : r ^ k = s := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hs0.le, inv_mul_cancel₀ (by positivity),
      Real.rpow_one]
  have hbdd : ∀ z ∈ U, IsBoundedUnder (· ≤ ·) (𝓝[U \ (c ∘ Prod.fst) ⁻¹' {0}] z)
      (fun w ↦ ‖φ w‖) := by
    intro z hz
    by_cases hz0 : ‖z.2‖ < r
    · -- the maximum principle on the circle of radius `r`
      obtain ⟨δ, hδ, hδV⟩ := Metric.isOpen_iff.1 hV z.1 hz.1
      have hK : IsCompact (closedBall z.1 (δ / 2) ×ˢ sphere (0 : ℂ) r) :=
        (isCompact_closedBall _ _).prod (isCompact_sphere _ _)
      have hKA : closedBall z.1 (δ / 2) ×ˢ sphere (0 : ℂ) r ⊆ A := by
        rintro ⟨b, u⟩ ⟨hb, hu⟩
        refine ⟨hδV (closedBall_subset_ball (by linarith) hb), ?_, ?_⟩ <;>
          rw [norm_pow, mem_sphere_zero_iff_norm.1 hu, hrk] <;> assumption
      obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hΦ.mono hKA)
      refine ⟨C, eventually_map.2 ?_⟩
      filter_upwards [nhdsWithin_le_nhds (prod_mem_nhds (ball_mem_nhds z.1 (half_pos hδ))
        (isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hz0))), self_mem_nhdsWithin]
        with w hw hwU
      rw [hdiff] at hwU
      obtain ⟨hwb, hwu⟩ := hw
      have hdisc : DifferentiableOn ℂ (fun u ↦ φ (w.1, u)) (closure (ball (0 : ℂ) r)) := by
        rw [closure_ball _ hr0.ne']
        refine hφ.comp ((differentiable_const _).prodMk differentiable_id).differentiableOn
          fun u hu ↦ ⟨hwU.1, hwU.2.1, ?_⟩
        rw [norm_pow]
        calc ‖u‖ ^ k ≤ r ^ k :=
              pow_le_pow_left₀ (norm_nonneg u) (mem_closedBall_zero_iff.1 hu) k
          _ = s := hrk
          _ < ρ := hs₂
      have := Complex.norm_le_of_forall_mem_frontier_norm_le (isBounded_ball)
        hdisc.diffContOnCl (C := C) (fun u hu ↦ ?_) (subset_closure (show w.2 ∈ ball 0 r from hwu))
      · exact this
      · rw [frontier_ball _ hr0.ne'] at hu
        have hwA : (w.1, u) ∈ A := hKA ⟨ball_subset_closedBall hwb, hu⟩
        rw [hφΦ (w.1, u) hwA.1 hwU.2.1 hwA.2.1 hwA.2.2]
        exact hC _ ⟨ball_subset_closedBall hwb, hu⟩
    · -- over the annulus, by continuity of `Φ`
      have hzA : z ∈ A := by
        refine ⟨hz.1, ?_, hz.2⟩
        rw [norm_pow]
        calc ρ⁻¹ < s := hs₁
          _ = r ^ k := hrk.symm
          _ ≤ ‖z.2‖ ^ k := pow_le_pow_left₀ hr0.le (not_lt.1 hz0) k
      have hc := (hΦ.continuousAt (hA.mem_nhds hzA)).norm
      refine ⟨‖Φ z‖ + 1, eventually_map.2 ?_⟩
      filter_upwards [nhdsWithin_le_nhds (hc.eventually (gt_mem_nhds (lt_add_one _))),
        nhdsWithin_le_nhds (hA.mem_nhds hzA), self_mem_nhdsWithin] with w hw hwA hwU
      rw [hdiff] at hwU
      rw [hφΦ w hwA.1 hwU.2.1 hwA.2.1 hwA.2.2]
      exact hw.le
  obtain ⟨φ', hφ', hφ'φ⟩ := exists_differentiableOn_eqOn_of_isBoundedUnder hU hg hgZ
    (by rw [hdiff]; exact hφ) hbdd
  exact ⟨φ', hφ', fun z hzV hcz hzρ ↦ hφ'φ (by rw [hdiff]; exact ⟨hzV, hcz, hzρ⟩)⟩

omit [T2Space W.left] in
/-- The evaluation of a section over `V₀ ⊆ V`, computed by a restriction. -/
lemma exists_evalVec_eq_restrict {M : ℕ} {w : Fin M → ℂ} (hwρ : ∀ ν, w ν ∈ overlap F.ρ)
    {V₀ : (space N).Opens} {b : Cm.{u} m} (hb : b ∈ F.G) (x : Fin M × (Σ i, Fin (D.deg i)))
    (hbV : (splitEquiv m).symm (b, w x.1) ∈ img V₀) :
    ∃ y ∈ preim h₀ W V₀, pt W y = (splitEquiv m).symm (b, w x.1) ∧
      ∀ (V : (space N).Opens), V₀ ≤ V → ∀ (a : W.left.presheaf.obj (op (preim h₀ W V))),
        D.evalVec w a b x = evalFun a y := by
  obtain ⟨y, hy, hpt, h⟩ := D.exists_evalVec_eq (h₀ := h₀) hwρ hb x hbV
  refine ⟨y, hy, hpt, fun V hV a ↦ ?_⟩
  rw [← D.evalVec_map hV hwρ hb x hbV, h, ← evalFun_of_mem _ hy, evalFun_map W _ _ hy]

omit [T2Space W.left] in
lemma differentiableOn_coeff_nodePoly {M : ℕ} {E : Set (Cm.{u} m)} (hE : IsOpen E)
    {v : Fin M × (Σ i, Fin (D.deg i)) → Cm.{u} m → ℂ} (hv : ∀ x, DifferentiableOn ℂ (v x) E)
    (ν : Fin M) (l : ℕ) :
    DifferentiableOn ℂ (fun b ↦ (D.nodePoly (fun y ↦ v y b) ν).coeff l) E := fun _ hb ↦
  (differentiableAt_coeff_prod_X_sub_C Finset.univ (fun ij b' ↦ v (ν, ij) b')
    (fun _ _ ↦ (hv _).differentiableAt (hE.mem_nhds hb)) l).differentiableWithinAt

/-- **The evaluation of sections of the cap has saturated image.** Let `t` be a section of the cap
with a pole of order `≤ n` at infinity over `V × ℙ¹`, `V ⊆ G` open and convex, and suppose that
`λ(t) = c v` for a function `c` holomorphic on `V` whose zero set has empty interior and a tuple `v`
of holomorphic functions on `V`. Then `v = λ(t')` for a section `t'` of the cap over `V × ℙ¹`. -/
theorem exists_capPole_evalVec_eq_of_mul {n : ℕ} {V : Set (Cm.{u} m)} {hV : IsOpen V}
    (hVG : V ⊆ F.G) (hVc : Convex ℝ V)
    {t : boundedSubring h₀ W (tubeN N V hV) × (D.ι → Cm.{u} m × ℂ → ℂ)}
    (ht : t ∈ D.capPole h₀ n (tubeN N V hV) (V ×ˢ ball 0 F.ρ)) {c : Cm.{u} m → ℂ}
    (hc : DifferentiableOn ℂ c V) (hcZ : interior (V ∩ c ⁻¹' {0}) = ∅) {M : ℕ}
    (hM : (∑ i, (D.deg i : ℕ)) * n < M) {w : Fin M → ℂ} (hw : Function.Injective w)
    (hwρ : ∀ ν, w ν ∈ overlap F.ρ) {v : Fin M × (Σ i, Fin (D.deg i)) → Cm.{u} m → ℂ}
    (hv : ∀ x, DifferentiableOn ℂ (v x) V)
    (htv : ∀ b ∈ V, ∀ x, D.evalVec w t.1.1 b x = c b * v x b) :
    ∃ t' ∈ D.capPole h₀ n (tubeN N V hV) (V ×ˢ ball 0 F.ρ),
      ∀ b ∈ V, ∀ x, D.evalVec w t'.1.1 b x = v x b := by
  classical
  have hρ := F.one_lt_ρ
  have hρ0 : 0 < F.ρ := zero_lt_one.trans hρ
  have hD := F.hasThinComplement
  set d := ∑ i, (D.deg i : ℕ)
  set V₀ : Set (Cm.{u} m) := V ∩ c ⁻¹' {0}ᶜ
  have hV₀ : IsOpen V₀ := hc.continuousOn.isOpen_inter_preimage hV isOpen_compl_singleton
  have hV₀V : V₀ ⊆ V := inter_subset_left
  have hc0 : ∀ b ∈ V₀, c b ≠ 0 := fun b hb ↦ hb.2
  have hVG₀ : V₀ ⊆ F.G := hV₀V.trans hVG
  obtain ⟨t₀, ht₀, ht₀1, ht₀2⟩ := D.exists_capPole_inv_mul h₀ (hV₀ := hV₀) hVG hV₀V ht
    (hc.mono hV₀V) hc0
  have hM0 : 0 < M := lt_of_le_of_lt (Nat.zero_le _) hM
  -- the evaluation of `t₀` is `v`
  have hev₀ : ∀ b ∈ V₀, ∀ x, D.evalVec w t₀.1.1 b x = v x b := by
    intro b hb x
    have hbV : (splitEquiv m).symm (b, w x.1) ∈ img (tubeN N V₀ hV₀) := by
      rw [F.mem_img_tubeN hVG₀, Homeomorph.apply_symm_apply]
      exact ⟨hb, mem_ball_zero_iff.2 (hwρ x.1).2⟩
    obtain ⟨y, hy, hpt, h⟩ := D.exists_evalVec_eq_restrict h₀ hwρ (hVG₀ hb) x hbV
    rw [h _ le_rfl, ht₀1 y hy, ← h _ (tubeN_mono hV₀V), htv b (hV₀V hb), hpt]
    simp only [baseOf, Homeomorph.apply_symm_apply]
    rw [← mul_assoc, inv_mul_cancel₀ (hc0 b hb), one_mul]
  -- the coefficients of the characteristic polynomial
  set Q : ℕ → Cn.{u} (m + 1) → ℂ := fun l x ↦
    ∑ ν, (D.nodePoly (fun y ↦ v y (baseOf x)) ν).coeff l *
      (Lagrange.basis Finset.univ w ν).eval (fibOf x)
  have hQ : ∀ l, DifferentiableOn ℂ (Q l) (img (tubeN N V hV)) := by
    intro l
    refine DifferentiableOn.fun_sum fun ν _ ↦ ?_
    refine DifferentiableOn.mul ?_ ?_
    · exact (D.differentiableOn_coeff_nodePoly hV hv ν l).comp
        differentiable_baseOf.differentiableOn fun x hx ↦ (mem_img_iff.1 hx).2
    · exact ((Polynomial.differentiable _).comp
        (differentiable_fibOf.{u} (m := m))).differentiableOn
  have hcoeff : ∀ l, ∀ x ∈ img (tubeN N V₀ hV₀), x ∈ N₀ →
      (charPolyFun W (evalFun t₀.1.1) x).coeff l = Q l x := by
    intro l x hx hxN
    rw [D.coeff_charPolyFun_eq_sum h₀ hVG₀ ht₀ hM hw hwρ l hx hxN]
    have hbx : baseOf x ∈ V₀ := (mem_img_iff.1 hx).2
    have : D.evalVec w t₀.1.1 (baseOf x) = fun y ↦ v y (baseOf x) :=
      funext fun y ↦ hev₀ _ hbx y
    rw [this]
  -- the number of sheets
  have hcard : ∀ x ∈ img (tubeN N V hV), x ∈ N₀ → (fiberFinset W x).card = d := by
    intro x hx hxN
    set x₁ := (splitEquiv m).symm (baseOf x, w ⟨0, hM0⟩)
    have hx₁ : x₁ ∈ annulusRegion F.G F.ρ := by
      rw [annulusRegion, mem_preimage, Homeomorph.apply_symm_apply]
      exact ⟨hVG (mem_img_iff.1 hx).2, hwρ _⟩
    have hx₁V : x₁ ∈ img (tubeN N V hV) := by
      rw [F.mem_img_tubeN hVG, Homeomorph.apply_symm_apply]
      exact ⟨(mem_img_iff.1 hx).2, mem_ball_zero_iff.2 (hwρ _).2⟩
    rw [card_fiberFinset_eq W hD (img _).isOpen (F.isPreconnected_img_tubeN hVG hVc)
      (img_le _) hx hxN hx₁V (F.annulusRegion_subset _ hx₁), D.card_fiberFinset hx₁]
  -- the part over `N`
  set O₀ := preim h₀ W (tubeN N V₀ hV₀)
  have hO₀ : ∀ y, y ∈ O₀ ↔ y ∈ preim h₀ W (tubeN N V hV) ∧ c (baseOf (pt W y)) ≠ 0 := by
    intro y
    rw [mem_preim_iff, mem_preim_iff, mem_img_iff, mem_img_iff]
    exact ⟨fun ⟨h₁, h₂⟩ ↦ ⟨⟨h₁, h₂.1⟩, h₂.2⟩, fun ⟨⟨h₁, h₂⟩, h₃⟩ ↦ ⟨h₁, h₂, h₃⟩⟩
  obtain ⟨a, ha⟩ := exists_secVal_eq_of_root h₀ hc hcZ (d := d) hQ
    (f := evalFun t₀.1.1)
    ((isHolOn_evalFun t₀.1.1).mono fun y hy ↦ (hO₀ y).2 hy)
    fun y hy hcy ↦ by
      have hy₀ : y ∈ O₀ := (hO₀ y).2 ⟨hy, hcy⟩
      have hyV₀ : pt W y ∈ img (tubeN N V₀ hV₀) := (mem_preim_iff h₀ W).1 hy₀
      have h₁ := eval_charPolyFun W (evalFun t₀.1.1) (rfl : pt W y = pt W y)
      rw [eval_charPolyFun_eq W _ (hcard _ ((mem_preim_iff h₀ W).1 hy) (pt_mem W y))] at h₁
      rw [← h₁]
      congr 1
      exact Finset.sum_congr rfl fun l _ ↦ by rw [hcoeff l _ hyV₀ (pt_mem W y)]
  -- points of the Kummer covers
  have hinvnorm : ∀ (k : ℕ) (u : ℂ), ‖u⁻¹‖ ^ k = ‖u ^ k‖⁻¹ := fun k u ↦ by
    rw [norm_inv, inv_pow, norm_pow]
  have hpiece : ∀ (i : D.ι) {V' : Set (Cm.{u} m)} {hV' : IsOpen V'}, V' ⊆ F.G →
      ∀ z : Cm.{u} m × ℂ, z.1 ∈ V' → F.ρ⁻¹ < ‖z.2 ^ (D.deg i : ℕ)‖ →
        ‖z.2 ^ (D.deg i : ℕ)‖ < F.ρ → invCoord z ∈ D.pieceSet (preim h₀ W (tubeN N V' hV')) i := by
    intro i V' hV' hV'G z hz1 h1 h2
    have hpos : 0 < ‖z.2 ^ (D.deg i : ℕ)‖ := (inv_pos.2 hρ0).trans h1
    rw [D.mem_pieceSet_preim h₀]
    refine ⟨⟨hV'G hz1, ?_, ?_⟩, ?_⟩
    · change F.ρ⁻¹ < ‖z.2⁻¹‖ ^ (D.deg i : ℕ)
      rw [hinvnorm]
      exact (inv_lt_inv₀ hρ0 hpos).2 h2
    · change ‖z.2⁻¹‖ ^ (D.deg i : ℕ) < F.ρ
      rw [hinvnorm]
      exact inv_lt_of_inv_lt₀ hρ0 h1
    · rw [F.mem_img_tubeN hV'G, Homeomorph.apply_symm_apply]
      refine ⟨hz1, mem_ball_zero_iff.2 ?_⟩
      change ‖(z.2⁻¹) ^ (D.deg i : ℕ)‖ < F.ρ
      rw [norm_pow, hinvnorm]
      exact inv_lt_of_inv_lt₀ hρ0 h1
  -- on the pieces over `V₀`, the values of `a` are those of `t₀`
  have hkv : ∀ (i : D.ι) (z : Cm.{u} m × ℂ), z ∈ D.pieceSet (preim h₀ W (tubeN N V hV)) i →
      c z.1 ≠ 0 → D.kummerVal (secVal h₀ W a) i z = D.kummerVal t₀.1.1 i z := by
    intro i z hz hcz
    obtain ⟨hzb, hzO⟩ := hz
    have hz₀ : D.toFun ⟨i, ⟨z, hzb⟩⟩ ∈ O₀ := by
      refine (hO₀ _).2 ⟨hzO, ?_⟩
      rw [D.pt_toFun]
      simpa [baseOf] using hcz
    rw [D.kummerVal_of_mem _ _ hzb, D.kummerVal_of_mem _ _ hzb]
    exact ha _ hzO ((hO₀ _).1 hz₀).2
  have hinf : ∀ i, ∃ φ' : Cm.{u} m × ℂ → ℂ,
      DifferentiableOn ℂ φ' {z | z.1 ∈ V ∧ ‖z.2 ^ (D.deg i : ℕ)‖ < F.ρ} ∧
      ∀ z, z.1 ∈ V → c z.1 ≠ 0 → ‖z.2 ^ (D.deg i : ℕ)‖ < F.ρ → φ' z = t₀.2 i z := by
    intro i
    refine exists_extension_infinity hV hc hcZ (D.deg i).pos hρ (φ := t₀.2 i)
      (Φ := fun z ↦ z.2 ^ (n * D.deg i) * D.kummerVal (secVal h₀ W a) i (invCoord z))
      ((ht₀.1 i).mono fun z hz ↦ ⟨⟨hz.1, hz.2.1⟩, mem_ball_zero_iff.2 hz.2.2⟩) ?_ ?_
    · have hkd := D.differentiableOn_kummerVal F.isOpen_G (secVal h₀ W a) i
      refine (continuous_snd.pow _).continuousOn.mul (hkd.continuousOn.comp ?_ ?_)
      · intro z hz
        have hz0 : z.2 ≠ 0 := by
          intro h
          have := hz.2.1
          rw [h, zero_pow (D.deg i).ne_zero, norm_zero] at this
          exact (inv_pos.2 hρ0).not_gt this
        exact (continuousAt_fst.prodMk (continuousAt_snd.inv₀ hz0)).continuousWithinAt
      · intro z hz
        exact hpiece i hVG z hz.1 hz.2.1 hz.2.2
    · intro z hzV hcz h1 h2
      have hz0 : z.2 ≠ 0 := by
        intro h
        rw [h, zero_pow (D.deg i).ne_zero, norm_zero] at h1
        exact (inv_pos.2 hρ0).not_gt h1
      have hmem := hpiece i (hV' := hV₀) hVG₀ z ⟨hzV, hcz⟩ h1 h2
      have hrel := ht₀.2 i (invCoord z) hmem
        (show Kummer.powMap (D.deg i) (invCoord (invCoord z)) ∈ V₀ ×ˢ ball 0 F.ρ by
          simp only [invCoord, inv_inv]
          exact ⟨⟨hzV, hcz⟩, mem_ball_zero_iff.2 h2⟩)
      have hinvinv : invCoord (invCoord z) = z := by simp [invCoord]
      rw [hinvinv] at hrel
      rw [hkv i (invCoord z) (D.pieceSet_mono (preim_mono h₀ W (tubeN_mono hV₀V)) i hmem) hcz,
        hrel]
      change t₀.2 i z = z.2 ^ (n * D.deg i) * ((z.2⁻¹) ^ (n * D.deg i) * t₀.2 i z)
      rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hz0, one_pow, one_mul]
  choose φ' hφ' hφ'eq using hinf
  refine ⟨(⟨secVal h₀ W a, secVal_mem h₀ W a⟩, φ'), ⟨fun i ↦ (hφ' i).mono fun z hz ↦
    ⟨hz.1, mem_ball_zero_iff.1 hz.2⟩, fun i z hz hz' ↦ ?_⟩, fun b hb x ↦ ?_⟩
  · -- the relation at infinity, by density
    set Ω : Set (Cm.{u} m × ℂ) := D.pieceSet (preim h₀ W (tubeN N V hV)) i ∩
      invCoord ⁻¹' (Kummer.powMap (D.deg i) ⁻¹' (V ×ˢ ball 0 F.ρ))
    have hpo := D.isOpen_pieceSet F.isOpen_G (preim h₀ W (tubeN N V hV)) i
    have hne : ∀ y ∈ D.pieceSet (preim h₀ W (tubeN N V hV)) i, y.2 ≠ 0 := by
      intro y hy h
      have := hy.1.2.1
      rw [h, norm_zero, zero_pow (D.deg i).ne_zero] at this
      exact (inv_pos.2 hρ0).not_gt this
    have hinvc : ContinuousOn invCoord (D.pieceSet (preim h₀ W (tubeN N V hV)) i) :=
      fun y hy ↦ (continuousAt_fst.prodMk (continuousAt_snd.inv₀ (hne y hy))).continuousWithinAt
    have hΩ : IsOpen Ω := hinvc.isOpen_inter_preimage hpo
      ((hV.prod isOpen_ball).preimage (Kummer.continuous_powMap _))
    have hΩV : ∀ y ∈ Ω, y.1 ∈ V := fun y hy ↦ hy.2.1
    have hZΩ : interior (Ω ∩ (c ∘ Prod.fst) ⁻¹' {0}) = ∅ := by
      refine eq_empty_iff_forall_notMem.2 fun y hy ↦ ?_
      have hsub : Prod.fst '' interior (Ω ∩ (c ∘ Prod.fst) ⁻¹' {0}) ⊆
          interior (V ∩ c ⁻¹' {0}) :=
        interior_maximal (by
          rintro _ ⟨y', hy', rfl⟩
          exact ⟨hΩV _ (interior_subset hy').1, (interior_subset hy').2⟩)
          (isOpenMap_fst _ isOpen_interior)
      rw [hcZ] at hsub
      exact hsub ⟨y, hy, rfl⟩
    have hL : ContinuousOn (D.kummerVal (secVal h₀ W a) i) Ω :=
      (D.differentiableOn_kummerVal F.isOpen_G (secVal h₀ W a) i).continuousOn.mono
        inter_subset_left
    have hR : ContinuousOn (fun y : Cm.{u} m × ℂ ↦
        y.2 ^ (n * D.deg i) * φ' i (invCoord y)) Ω :=
      (continuous_snd.pow _).continuousOn.mul ((hφ' i).continuousOn.comp
        (hinvc.mono inter_subset_left) fun y hy ↦ ⟨hy.2.1, mem_ball_zero_iff.1 hy.2.2⟩)
    refine EqOn.of_eqOn_diff_zero hΩ hZΩ hL hR (fun y hy ↦ ?_) ⟨hz, hz'⟩
    obtain ⟨⟨hy₁, hy₂⟩, hy₃⟩ := hy
    have hcy : c y.1 ≠ 0 := hy₃
    beta_reduce
    have hy₀ : y ∈ D.pieceSet (preim h₀ W (tubeN N V₀ hV₀)) i := by
      refine ⟨hy₁.1, ?_⟩
      refine (hO₀ _).2 ⟨hy₁.2, ?_⟩
      rw [D.pt_toFun]
      simpa [baseOf] using hcy
    rw [hkv i y hy₁ hcy, ht₀.2 i y hy₀ ⟨⟨hy₂.1, hcy⟩, hy₂.2⟩,
      hφ'eq i (invCoord y) hy₂.1 hcy (mem_ball_zero_iff.1 hy₂.2)]
  · -- the evaluation, by density
    have hL : ContinuousOn (fun b ↦ D.evalVec w (secVal h₀ W a) b x) V :=
      (D.differentiableOn_evalVec F.isOpen_G hwρ (secVal h₀ W a) x).continuousOn.mono
        fun b hb ↦ ⟨hVG hb, by
          rw [F.mem_img_tubeN hVG, Homeomorph.apply_symm_apply]
          exact ⟨hb, mem_ball_zero_iff.2 (hwρ x.1).2⟩⟩
    refine EqOn.of_eqOn_diff_zero hV hcZ hL (hv x).continuousOn (fun b' hb' ↦ ?_) hb
    obtain ⟨hb'V, hb'c⟩ := hb'
    have hb'₀ : b' ∈ V₀ := ⟨hb'V, hb'c⟩
    have hbV : (splitEquiv m).symm (b', w x.1) ∈ img (tubeN N V₀ hV₀) := by
      rw [F.mem_img_tubeN hVG₀, Homeomorph.apply_symm_apply]
      exact ⟨hb'₀, mem_ball_zero_iff.2 (hwρ x.1).2⟩
    obtain ⟨y, hy, hpt, h⟩ := D.exists_evalVec_eq_restrict h₀ hwρ (hVG hb'V) x hbV
    have hyc : c (baseOf (pt W y)) ≠ 0 := by
      rw [hpt]
      simpa [baseOf] using hb'c
    change D.evalVec w (secVal h₀ W a) b' x = v x b'
    rw [h _ (tubeN_mono hV₀V), ha y ((hO₀ y).1 hy).1 hyc, ← h _ le_rfl, hev₀ b' hb'₀ x]


end

end ComplexAnalytic.Cap.AnnulusDecomposition
