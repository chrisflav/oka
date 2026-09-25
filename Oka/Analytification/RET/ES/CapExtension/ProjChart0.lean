/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.ES.CapExtension.ProjSections
import Oka.Analytification.RET.ES.CapExtension.ChartReverse

/-!
# The sheaf of the cap in the chart `w`

Keep the notation of `Oka/Analytification/RET/ES/CapExtension/ProjSheaf.lean`. Over the part
`N = G × {‖w‖ < ρ}` of the chart `w` of `P^an`, the sheaf of the cap `𝒞` is the sheaf `𝒜` of bounded
sections: a section of `𝒞` is determined by its values on `W`, and the values of a section of `𝒜`
on the Kummer pieces over the annulus extend it to `K`. This is a chart in the sense of
`AlgebraicGeometry.LocallyRingedSpace.ModuleChart`
(`ComplexAnalytic.Cap.AnnulusDecomposition.chart0ModuleChart`), so the local conditions for
coherence of `𝒜` at `x ∈ N` give those of `𝒞` at the corresponding point of `P^an`
(`ComplexAnalytic.Cap.AnnulusDecomposition.capModule_isCoherentAt_chart0`).
-/

open CategoryTheory Opposite Topology TopologicalSpace Set Filter Metric Limits

universe u

namespace ComplexAnalytic.relProjectiveSpaceAn

open AnalyticSpace

variable {m : ℕ} {O : (relProjectiveSpaceAn.{u} m 1).Opens}

/-- **Sections of `𝒪_{P^an}` are determined by their values.** -/
lemma eq_of_forall_eval_eq {s t : (relProjectiveSpaceAn.{u} m 1).presheaf.obj (op O)}
    (h : ∀ p (hp : p ∈ O), (relProjectiveSpaceAn.{u} m 1).eval p hp s =
      (relProjectiveSpaceAn.{u} m 1).eval p hp t) : s = t :=
  eq_of_secFun fun q hq ↦ by
    rw [secFun_of_mem s hq.1 hq.2, secFun_of_mem t hq.1 hq.2]
    exact h _ _

end ComplexAnalytic.relProjectiveSpaceAn

namespace ComplexAnalytic.Cap.AnnulusDecomposition

open AnalyticSpace BoundedSections relProjectiveSpaceAn relProjectiveLine
open AlgebraicGeometry AlgebraicGeometry.LocallyRingedSpace
open KummerModel (splitEquiv)

noncomputable section

variable {m : ℕ}

/-- The coordinates `(b, w)` of `ℂ^{m+1}`, as a homeomorphism onto `ℂᵐ × ℂ`. -/
def chartCoordHomeo : Cn.{u} (m + 1) ≃ₜ (Fin m → ℂ) × ℂ where
  toFun x := (baseCoord (baseOf x), fibOf x)
  invFun p := mkPt (ofBase p.1) p.2
  left_inv x := by simp [mkPt_baseOf_fibOf]
  right_inv p := by simp [baseOf_mkPt, fibOf_mkPt]
  continuous_toFun := (continuous_baseCoord.comp continuous_baseOf).prodMk continuous_fibOf
  continuous_invFun := (differentiable_mkPt.continuous).comp
    ((continuous_ofBase.comp continuous_fst).prodMk continuous_snd)

lemma differentiable_chartCoordHomeo_symm :
    Differentiable ℂ (chartCoordHomeo.{u} (m := m)).symm := fun p ↦ by
  have h0 : Differentiable ℂ (ofBase.{u} (n := m)) :=
    differentiable_pi.2 fun j ↦ differentiable_apply _
  have h1 : DifferentiableAt ℂ (ofBase.{u} ∘ Prod.fst) p := (h0 p.1).comp p differentiableAt_fst
  have h2 := (differentiable_mkPt.{u} (m := m) ((ofBase.{u} ∘ Prod.fst) p, p.2)).comp p
    (h1.prodMk differentiableAt_snd)
  exact h2

lemma chart0Pt_eq (x : Cn.{u} (m + 1)) : chart0Pt x = chartPt 0 (chartCoordHomeo x) :=
  rfl

lemma chart0Pt_injective : Function.Injective (chart0Pt.{u} (m := m)) :=
  (chartPt_injective 0).comp chartCoordHomeo.injective

variable (N : (AnalyticSpace.complexAffineSpace.{u} (m + 1)).Opens)

lemma isOpenEmbedding_chart0Map : IsOpenEmbedding (chart0Map N).toLRSHom.base := by
  have : ⇑(chart0Map N).toLRSHom.base = chartPt 0 ∘ chartCoordHomeo ∘ Subtype.val :=
    funext fun x ↦ chart0Map_base N x
  rw [this]
  exact (isOpenEmbedding_chartPt 0).comp
    (chartCoordHomeo.isOpenEmbedding.comp N.isOpenEmbedding)

/-- The image in `P^an` of an open of `N`. -/
abbrev img0 (V : (space N).Opens) : (relProjectiveSpaceAn.{u} m 1).Opens :=
  (isOpenEmbedding_chart0Map N).isOpenMap.functor.obj V

lemma mem_img0 {V : (space N).Opens} {p : relProjectiveSpaceAn.{u} m 1} :
    p ∈ img0 N V ↔ ∃ x ∈ img V, chart0Pt x = p := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.1, mem_img_iff.2 ⟨y.2, hy⟩, (chart0Map_base N y).symm⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨hxN, hxV⟩ := mem_img_iff.1 hx
    exact ⟨⟨x, hxN⟩, hxV, chart0Map_base N _⟩

lemma chart0Pt_mem_img0 {V : (space N).Opens} {x : Cn.{u} (m + 1)} :
    chart0Pt x ∈ img0 N V ↔ x ∈ img V := by
  rw [mem_img0]
  exact ⟨fun ⟨x', hx', h⟩ ↦ chart0Pt_injective h ▸ hx', fun h ↦ ⟨x, h, rfl⟩⟩

lemma le_preimage_img0 (V : (space N).Opens) :
    V ≤ (Opens.map (chart0Map N).toLRSHom.base).obj (img0 N V) :=
  fun x hx ↦ ⟨x, hx, rfl⟩

/-- The identification of sections of `𝒪_{P^an}` over the image of `V` with holomorphic functions
on `V`. -/
def psi0 (V : (space N).Opens) :
    (relProjectiveSpaceAn.{u} m 1).presheaf.obj (op (img0 N V)) →+* (space N).presheaf.obj (op V) :=
  ((space N).presheaf.map (homOfLE (le_preimage_img0 N V)).op).hom.comp
    ((chart0Map N).toLRSHom.c.app (op (img0 N V))).hom

lemma holFun_psi0 {V : (space N).Opens} (r : (relProjectiveSpaceAn.{u} m 1).presheaf.obj
    (op (img0 N V))) {x : Cn.{u} (m + 1)} (hx : x ∈ img V) :
    holFun (psi0 N V r) x = (relProjectiveSpaceAn.{u} m 1).eval (chart0Pt x)
      ((chart0Pt_mem_img0 N).2 hx) r := by
  obtain ⟨hxN, hxV⟩ := mem_img_iff.1 hx
  rw [holFun_eq_eval _ hx, psi0, RingHom.comp_apply]
  erw [eval_presheaf_map]
  erw [eval_c_app (chart0Map N).toLRSHom (chart0Map N).isCLinear ⟨x, hxN⟩
    (le_preimage_img0 N V hxV)]
  exact eval_congr_point (chart0Map_base N ⟨x, hxN⟩) _ _ r

lemma psi0_res {V₁ V₂ : (space N).Opens} (h : V₁ ≤ V₂)
    (r : (relProjectiveSpaceAn.{u} m 1).presheaf.obj (op (img0 N V₂))) :
    psi0 N V₁ ((relProjectiveSpaceAn.{u} m 1).res
      ((isOpenEmbedding_chart0Map N).isOpenMap.functor.monotone h) r) =
      (space N).res h (psi0 N V₂ r) := by
  simp only [psi0, RingHom.coe_comp, Function.comp_apply]
  change (space N).res _ ((chart0Map N).toLRSHom.c.app _ ((relProjectiveSpaceAn.{u} m 1).res _ r))
    = (space N).res h ((space N).res _ ((chart0Map N).toLRSHom.c.app _ r))
  rw [c_app_res, res_res, res_res]

lemma bijective_psi0 (V : (space N).Opens) : Function.Bijective (psi0 N V) := by
  constructor
  · intro r r' h
    refine eq_of_forall_eval_eq fun p hp ↦ ?_
    obtain ⟨x, hx, rfl⟩ := (mem_img0 N).1 hp
    have := congrArg (fun q ↦ holFun q x) h
    rwa [holFun_psi0 N r hx, holFun_psi0 N r' hx] at this
  · intro q
    set S : TopologicalSpace.Opens ((Fin m → ℂ) × ℂ) := ⟨chartCoordHomeo '' (img V),
      chartCoordHomeo.isOpenMap _ (img V).isOpen⟩
    have hF : DifferentiableOn ℂ (fun p ↦ holFun q (chartCoordHomeo.symm p)) S := by
      rintro _ ⟨x, hx, rfl⟩
      have hd := (differentiableOn_holFun q).differentiableAt ((img V).isOpen.mem_nhds hx)
      have hc : DifferentiableAt ℂ (chartCoordHomeo.symm : (Fin m → ℂ) × ℂ → Cn.{u} (m + 1))
          (chartCoordHomeo x) := differentiable_chartCoordHomeo_symm _
      have hd' : DifferentiableAt ℂ (holFun q) (chartCoordHomeo.symm (chartCoordHomeo x)) := by
        rw [Homeomorph.symm_apply_apply]
        exact hd
      exact (hd'.comp _ hc).differentiableWithinAt
    obtain ⟨a, ha⟩ := exists_f0_eq S _ hF
    have hle : img0 N V ≤ chartBox 0 S := by
      intro p hp
      obtain ⟨x, hx, rfl⟩ := (mem_img0 N).1 hp
      exact ⟨chartCoordHomeo x, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨(relProjectiveSpaceAn.{u} m 1).res hle a, eq_of_holFun_eq fun x hx ↦ ?_⟩
    rw [holFun_psi0 N _ hx]
    erw [eval_presheaf_map]
    refine (f0_eq_eval a (p := chartCoordHomeo x) (hle ((chart0Pt_mem_img0 N).2 hx))).symm.trans ?_
    rw [ha _ ⟨x, hx, rfl⟩, Homeomorph.symm_apply_apply]

/-- A point of the chart `1` which lies in the chart `0` has nonzero fibre coordinate, and its
fibre coordinate in the chart `0` is the inverse. -/
lemma chartPt_one_eq_chartPt_zero {p q : (Fin m → ℂ) × ℂ}
    (h : chartPt.{u} 1 p = chartPt.{u} 0 q) : p.2 ≠ 0 ∧ q = (p.1, p.2⁻¹) := by
  have hq : q.2 ≠ 0 := (chartPt_zero_mem_range_chart_one_iff q).1 ⟨cpt p, h⟩
  rw [chartPt_zero_eq_chartPt_one hq] at h
  have e := chartPt_injective 1 h
  have hp : p.2 ≠ 0 := by rw [e]; exact inv_ne_zero hq
  refine ⟨hp, Prod.ext (congrArg Prod.fst e).symm ?_⟩
  rw [e, inv_inv]

variable {N}
variable {N₀ : (AnalyticSpace.complexAffineSpace.{u} (m + 1)).Opens}
  {W : FiniteEtaleOver (space N₀)} {F : WeierstrassForm N N₀}
  {D : AnnulusDecomposition W F.G F.ρ}

/-- **The point of `W` corresponding to a point of `K` over the annulus.** -/
lemma exists_partner {i : D.ι} {x : Cn.{u} (m + 1)} (hx : x ∈ D.kPiece i) (h0 : D.kVal x ≠ 0)
    (hρ : ‖D.kVal x‖⁻¹ < F.ρ) :
    ∃ z : KummerAnnulus.base F.G F.ρ⁻¹ F.ρ (D.deg i), D.kPt i (invCoord z.1) = x := by
  have hc0 : D.kCoord x ≠ 0 := fun h ↦ h0 (by rw [D.kVal_eq_kCoord_pow hx, h, zero_pow
    (D.deg i).ne_zero])
  have hk := D.kVal_eq_kCoord_pow hx
  have hlt : ‖D.kVal x‖ < F.ρ := by rw [D.kVal_of_mem hx]; exact hx.2
  refine ⟨⟨(baseOf x, (D.kCoord x)⁻¹), hx.1, ?_, ?_⟩, ?_⟩
  · change F.ρ⁻¹ < ‖(D.kCoord x)⁻¹‖ ^ (D.deg i : ℕ)
    rw [norm_inv, inv_pow, ← norm_pow, ← hk]
    exact inv_lt_inv₀ F.pos_ρ (norm_pos_iff.2 h0) |>.2 hlt
  · change ‖(D.kCoord x)⁻¹‖ ^ (D.deg i : ℕ) < F.ρ
    rw [norm_inv, inv_pow, ← norm_pow, ← hk]
    exact hρ
  · simp only [invCoord, inv_inv]
    exact D.kPt_kCoord hx

variable (N) in
/-- A point of `K` over the image of `V ⊆ N` lies over the annulus. -/
lemma kVal_ne_zero_of_mem_img0 {V : (space N).Opens} {x : Cn.{u} (m + 1)}
    (hx : x ∈ img ((Opens.map D.kMap.toLRSHom.base).obj (img0 N V))) :
    D.kVal x ≠ 0 ∧ ‖D.kVal x‖⁻¹ < F.ρ := by
  obtain ⟨hxK, hxV⟩ := mem_img_iff.1 hx
  obtain ⟨y, hy, hyx⟩ := (mem_img0 N).1 hxV
  change chartPt 0 _ = D.kMap.toLRSHom.base _ at hyx
  rw [D.kMap_base] at hyx
  obtain ⟨h0, e⟩ := chartPt_one_eq_chartPt_zero hyx.symm
  refine ⟨h0, ?_⟩
  have hyN : y ∈ N := img_le V y hy
  have := ((F.mem_N y).1 hyN).2
  have e2 := congrArg Prod.snd e
  simp only at e2
  rw [← norm_inv, ← e2]
  exact this

/-! ### The chart map on sections -/

variable (h₀ : N₀ ≤ N)

lemma mem_preimW_img0_iff {V : (space N).Opens} {w : W.left} :
    w ∈ (Opens.map (projW W).toLRSHom.base).obj (img0 N V) ↔ w ∈ preim h₀ W V := by
  change (projW W).toLRSHom.base w ∈ img0 N V ↔ _
  rw [projW_base, chart0Pt_mem_img0, mem_preim_iff]

lemma wPart_isBoundedNear {O : (relProjectiveSpaceAn.{u} m 1).Opens}
    (s : D.capAmb.val.obj (op O)) : IsBoundedNear (projW W) (removedW N N₀) (wPart s) :=
  ((biprod.fst : D.capAmb ⟶ capW W).val.app (op O) s).2

lemma continuous_chart0Pt : Continuous (chart0Pt.{u} (m := m)) :=
  (isOpenEmbedding_chartPt 0).continuous.comp chartCoordHomeo.continuous

lemma isBddOn_capWVal {V : (space N).Opens} (s : D.capModule.val.obj (op (img0 N V))) :
    IsBddOn W V (capWVal s) := by
  intro x hx hxN₀
  have hxP : chart0Pt x ∈ img0 N V := (chart0Pt_mem_img0 N).2 hx
  obtain ⟨M, hM, C, hC⟩ := wPart_isBoundedNear s.1 (chart0Pt x) hxP
    ⟨x, ⟨img_le V x hx, hxN₀⟩, rfl⟩
  refine ⟨chart0Pt ⁻¹' M, continuous_chart0Pt.continuousAt.preimage_mem_nhds hM, C,
    fun w hwM hwV ↦ ?_⟩
  have hw : w ∈ (Opens.map (projW W).toLRSHom.base).obj (img0 N V) := by
    change (projW W).toLRSHom.base w ∈ img0 N V
    rw [projW_base]
    exact (chart0Pt_mem_img0 N).2 hwV
  have := hC w hw (by rw [projW_base]; exact hwM)
  rwa [capWVal, evalFun_of_mem _ hw]

lemma isHolOn_capWVal {V : (space N).Opens} (s : D.capModule.val.obj (op (img0 N V))) :
    IsHolOn W (capWVal s) (preim h₀ W V) :=
  (isHolOn_evalFun (wPart s.1)).mono fun _ hw ↦ (mem_preimW_img0_iff h₀).2 hw

/-- The section of `𝒜` given by the values on `W` of a section of `𝒞`. -/
def phi0Fun {V : (space N).Opens} (s : D.capModule.val.obj (op (img0 N V))) :
    (boundedModule h₀ W).val.obj (op V) :=
  (exists_secVal_eq h₀ W (isHolOn_capWVal h₀ s) (isBddOn_capWVal s)).choose

lemma evalFun_phi0Fun {V : (space N).Opens} (s : D.capModule.val.obj (op (img0 N V)))
    {w : W.left} (hw : w ∈ preim h₀ W V) :
    evalFun (secVal h₀ W (phi0Fun h₀ s)) w = capWVal s w :=
  (exists_secVal_eq h₀ W (isHolOn_capWVal h₀ s) (isBddOn_capWVal s)).choose_spec w hw

/-- **The chart map** `𝒞(img V) → 𝒜(V)`: the values on `W`. -/
def phi0 (V : (space N).Opens) :
    D.capModule.val.obj (op (img0 N V)) →+ (boundedModule h₀ W).val.obj (op V) where
  toFun s := phi0Fun h₀ s
  map_zero' := secVal_ext h₀ W fun w hw ↦ by
    rw [evalFun_phi0Fun h₀ _ hw, evalFun_secVal_zero hw]
    change evalFun (wPart (0 : D.capAmb.val.obj (op (img0 N V)))) w = 0
    rw [wPart_zero, evalFun_of_mem _ ((mem_preimW_img0_iff h₀).2 hw), map_zero]
  map_add' s t := secVal_ext h₀ W fun w hw ↦ by
    rw [evalFun_secVal_add _ _ hw, evalFun_phi0Fun h₀ _ hw, evalFun_phi0Fun h₀ _ hw,
      evalFun_phi0Fun h₀ _ hw, capWVal_add _ _ ((mem_preimW_img0_iff h₀).2 hw)]

lemma evalFun_phi0 {V : (space N).Opens} (s : D.capModule.val.obj (op (img0 N V)))
    {w : W.left} (hw : w ∈ preim h₀ W V) :
    evalFun (secVal h₀ W (phi0 h₀ V s)) w = capWVal s w :=
  evalFun_phi0Fun h₀ s hw

variable (N) in
lemma kMap_toFun_mem_img0 {V : (space N).Opens} {x : Cn.{u} (m + 1)}
    (hx : x ∈ img ((Opens.map D.kMap.toLRSHom.base).obj (img0 N V))) {i : D.ι}
    {z : KummerAnnulus.base F.G F.ρ⁻¹ F.ρ (D.deg i)} (hz : D.kPt i (invCoord z.1) = x) :
    D.toFun ⟨i, z⟩ ∈ (Opens.map (projW W).toLRSHom.base).obj (img0 N V) := by
  change (projW W).toLRSHom.base _ ∈ img0 N V
  rw [D.projW_toFun i z]
  subst hz
  obtain ⟨hxK, hxV⟩ := mem_img_iff.1 hx
  exact hxV

lemma injective_phi0 (V : (space N).Opens) : Function.Injective (phi0 (D := D) h₀ V) := by
  intro s t h
  have hW : ∀ w ∈ (Opens.map (projW W).toLRSHom.base).obj (img0 N V),
      capWVal s w = capWVal t w := fun w hw ↦ by
    have hw' := (mem_preimW_img0_iff h₀).1 hw
    rw [← evalFun_phi0 h₀ s hw', ← evalFun_phi0 h₀ t hw', h]
  refine capModule_ext hW fun x hx ↦ ?_
  obtain ⟨hxK, -⟩ := mem_img_iff.1 hx
  obtain ⟨i, hi⟩ := D.mem_kOpens.1 hxK
  obtain ⟨h0, hρ⟩ := kVal_ne_zero_of_mem_img0 N hx
  obtain ⟨z, hz⟩ := exists_partner hi h0 hρ
  have hzO := kMap_toFun_mem_img0 N hx hz
  rw [← hz, ← capWVal_compat s i z hzO, ← capWVal_compat t i z hzO]
  exact hW _ hzO

open Classical in
/-- The values on `K` of a section of `𝒜`: on the `i`-th piece, the value at the point of `W`
with Kummer coordinates `(b, u'⁻¹)`. -/
def kFunOf {V : (space N).Opens} (a : (boundedModule h₀ W).val.obj (op V)) (x : Cn.{u} (m + 1)) :
    ℂ :=
  ∑ i, if x ∈ D.kPiece i then D.kummerVal (secVal h₀ W a) i (baseOf x, (D.kCoord x)⁻¹) else 0

lemma kFunOf_of_mem {V : (space N).Opens} (a : (boundedModule h₀ W).val.obj (op V)) {i : D.ι}
    {x : Cn.{u} (m + 1)} (hx : x ∈ D.kPiece i) :
    kFunOf (D := D) h₀ a x = D.kummerVal (secVal h₀ W a) i (baseOf x, (D.kCoord x)⁻¹) := by
  classical
  rw [kFunOf, Finset.sum_eq_single i (fun j _ hji ↦ if_neg fun hj ↦ hji (D.eq_of_mem_kPiece hj hx))
    (fun h ↦ absurd (Finset.mem_univ i) h), if_pos hx]

lemma differentiableOn_kFunOf {V : (space N).Opens} (a : (boundedModule h₀ W).val.obj (op V)) :
    DifferentiableOn ℂ (kFunOf (D := D) h₀ a)
      (img ((Opens.map D.kMap.toLRSHom.base).obj (img0 N V))) := by
  intro x hx
  obtain ⟨hxK, -⟩ := mem_img_iff.1 hx
  obtain ⟨i, hi⟩ := D.mem_kOpens.1 hxK
  obtain ⟨h0, hρ⟩ := kVal_ne_zero_of_mem_img0 N hx
  obtain ⟨z, hz⟩ := exists_partner hi h0 hρ
  have hc0 : D.kCoord x ≠ 0 := fun h ↦ h0 (by rw [D.kVal_eq_kCoord_pow hi, h, zero_pow
    (D.deg i).ne_zero])
  have hzO := kMap_toFun_mem_img0 N hx hz
  have hzx : ((baseOf x, (D.kCoord x)⁻¹) : Cm.{u} m × ℂ) = z.1 := by
    rw [← hz]
    simp only [baseOf_kPt, invCoord]
    rw [D.kCoord_kPt (hz ▸ hi), inv_inv]
  have hpiece : z.1 ∈ D.pieceSet (preim h₀ W V) i :=
    ⟨z.2, (mem_preimW_img0_iff h₀).1 hzO⟩
  have hdk : DifferentiableAt ℂ (D.kummerVal (secVal h₀ W a) i) z.1 :=
    (D.differentiableOn_kummerVal F.isOpen_G _ i).differentiableAt
      ((D.isOpen_pieceSet F.isOpen_G _ i).mem_nhds hpiece)
  have hφ : DifferentiableAt ℂ (fun y : Cn.{u} (m + 1) ↦ (baseOf y, (D.kCoord y)⁻¹)) x :=
    (differentiable_baseOf x).prodMk ((D.differentiableOn_kCoord.differentiableAt
      ((D.kOpens).isOpen.mem_nhds hxK)).inv hc0)
  rw [← hzx] at hdk
  refine ((hdk.comp x hφ).congr_of_eventuallyEq ?_).differentiableWithinAt
  filter_upwards [(D.isOpen_kPiece i).mem_nhds hi] with y hy
  exact kFunOf_of_mem h₀ a hy

lemma preimW_img0_le (V : (space N).Opens) :
    (Opens.map (projW W).toLRSHom.base).obj (img0 N V) ≤ preim h₀ W V :=
  fun _ hw ↦ (mem_preimW_img0_iff h₀).1 hw

lemma isBoundedNear_res_secVal {V : (space N).Opens} (a : (boundedModule h₀ W).val.obj (op V)) :
    IsBoundedNear (projW W) (removedW N N₀)
      (W.left.presheaf.map (homOfLE (preimW_img0_le h₀ V)).op (secVal h₀ W a)) := by
  rintro p hp ⟨x, ⟨hxN, hxN₀⟩, rfl⟩
  have hx : x ∈ img V := (chart0Pt_mem_img0 N).1 hp
  obtain ⟨M₀, hM₀, C, -, hC⟩ := exists_bound_of_mem_boundedSubring (secVal_mem h₀ W a) hx hxN₀
  have hopen : IsOpen (chart0Pt.{u} '' interior M₀) :=
    ((isOpenEmbedding_chartPt 0).isOpenMap.comp chartCoordHomeo.isOpenMap) _ isOpen_interior
  refine ⟨_, hopen.mem_nhds ⟨x, mem_interior_iff_mem_nhds.2 hM₀, rfl⟩, C, fun w hw hwM ↦ ?_⟩
  obtain ⟨x', hx'M, hx'⟩ := hwM
  rw [projW_base] at hx'
  have hpt : pt W w = x' := chart0Pt_injective hx'.symm
  rw [eval_presheaf_map, ← evalFun_of_mem _ (preimW_img0_le h₀ V hw)]
  refine hC w (hpt ▸ interior_subset hx'M) ?_
  exact (mem_preim_iff h₀ W).1 (preimW_img0_le h₀ V hw)

lemma surjective_phi0 (V : (space N).Opens) : Function.Surjective (phi0 (D := D) h₀ V) := by
  intro a
  set a' := W.left.presheaf.map (homOfLE (preimW_img0_le h₀ V)).op (secVal h₀ W a)
  set g : (space D.kOpens).presheaf.obj (op ((Opens.map D.kMap.toLRSHom.base).obj (img0 N V))) :=
    OkaRing.ofDifferentiableOn _ (differentiableOn_kFunOf (D := D) h₀ a)
  have hc : ∀ (i : D.ι) (z : KummerAnnulus.base F.G F.ρ⁻¹ F.ρ (D.deg i)),
      D.toFun ⟨i, z⟩ ∈ (Opens.map (projW W).toLRSHom.base).obj (img0 N V) →
        evalFun a' (D.toFun ⟨i, z⟩) = holFun g (D.kPt i (invCoord z.1)) := by
    intro i z hz
    rw [holFun_ofDifferentiableOn _ (kPt_mem_img hz), evalFun_map W _ _ hz,
      kFunOf_of_mem h₀ a (D.kPt_invCoord_mem z.2), D.kCoord_kPt (D.kPt_invCoord_mem z.2),
      baseOf_kPt]
    simp only [invCoord, inv_inv]
    rw [D.kummerVal_of_mem _ _ z.2]
  refine ⟨D.mkCap a' (isBoundedNear_res_secVal h₀ a) g hc, secVal_ext h₀ W fun w hw ↦ ?_⟩
  rw [evalFun_phi0 h₀ _ hw, capWVal_mkCap, evalFun_map W _ _ ((mem_preimW_img0_iff h₀).2 hw)]

lemma phi0_res {V₁ V₂ : (space N).Opens} (h : V₁ ≤ V₂)
    (s : D.capModule.val.obj (op (img0 N V₂))) :
    phi0 h₀ V₁ (sectRes D.capModule
      ((isOpenEmbedding_chart0Map N).isOpenMap.functor.monotone h) s) =
      sectRes (boundedModule h₀ W) h (phi0 h₀ V₂ s) :=
  secVal_ext h₀ W fun w hw ↦ by
    rw [evalFun_phi0 h₀ _ hw, evalFun_secVal_sectRes _ _ hw,
      evalFun_phi0 h₀ _ (preim_mono h₀ W h hw), capWVal_res _ _ ((mem_preimW_img0_iff h₀).2 hw)]

lemma phi0_smul (V : (space N).Opens) (r : (relProjectiveSpaceAn.{u} m 1).presheaf.obj
    (op (img0 N V))) (s : D.capModule.val.obj (op (img0 N V))) :
    phi0 h₀ V (r • s) = psi0 N V r • phi0 h₀ V s :=
  secVal_ext h₀ W fun w hw ↦ by
    have hw' := (mem_preimW_img0_iff h₀).2 hw
    rw [evalFun_phi0 h₀ _ hw, evalFun_secVal_smul _ _ hw, evalFun_phi0 h₀ _ hw,
      capWVal_smul _ _ hw', holFun_psi0 N r ((mem_preim_iff h₀ W).1 hw)]
    congr 1
    exact eval_congr_point (projW_base W w) _ _ r

variable (D) in
/-- **The chart of `𝒞` in the chart `w`**: over `N`, the sheaf of the cap is `𝒜`. -/
def chart0ModuleChart : ModuleChart D.capModule (boundedModule h₀ W) where
  g := (chart0Map N).toLRSHom.base
  isOpenEmbedding := isOpenEmbedding_chart0Map N
  ψ := psi0 N
  bijective_ψ := bijective_psi0 N
  ψ_res := psi0_res N
  φ := phi0 h₀
  bijective_φ V := ⟨injective_phi0 h₀ V, surjective_phi0 h₀ V⟩
  φ_res := phi0_res h₀
  φ_smul := phi0_smul h₀

/-- **The local conditions for coherence of `𝒞` at the points of `N`.** -/
theorem capModule_isCoherentAt_chart0 {x : space N} (hx : IsCoherentAt h₀ W x) :
    IsLocallyFinitelyGeneratedModuleAt D.capModule (chart0Pt x.1) ∧
      HasLocalModuleRelationsAt D.capModule (chart0Pt x.1) := by
  rw [← chart0Map_base N x]
  exact ⟨(D.chart0ModuleChart h₀).isLocallyFinitelyGeneratedModuleAt hx.1,
    (D.chart0ModuleChart h₀).hasLocalModuleRelationsAt hx.2⟩

end

end ComplexAnalytic.Cap.AnnulusDecomposition
