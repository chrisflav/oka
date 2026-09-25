/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.ES.CapExtension.ProjChart0

/-!
# The sheaf of the cap at infinity

Keep the notation of `Oka/Analytification/RET/ES/CapExtension/ProjSheaf.lean`. Over the disc
`G × {‖w'‖ < ρ}` of the chart `w' = w⁻¹` of `P^an` at infinity, a section of the sheaf of the
cap `𝒞` is determined by its values on `K`, and on the `i`-th Kummer piece these are
`∑_{j < kᵢ} u'ʲ gᵢⱼ(b, u'^{kᵢ})` with unique holomorphic `gᵢⱼ`
(`ComplexAnalytic.Cap.exists_coeff_eqOn`).
The coefficients identify `𝒞` over the disc with the free sheaf of rank `∑ kᵢ`, a chart in the
sense of `AlgebraicGeometry.LocallyRingedSpace.ModuleChart`
(`ComplexAnalytic.Cap.AnnulusDecomposition.chartInfModuleChart`); hence `𝒞` satisfies the local
conditions for coherence at the points of the disc
(`ComplexAnalytic.Cap.AnnulusDecomposition.capModule_isCoherentAt_chartInf`).
-/

open CategoryTheory Opposite Topology TopologicalSpace Set Filter Metric Limits

universe u

namespace ComplexAnalytic.Cap.AnnulusDecomposition

open AnalyticSpace BoundedSections relProjectiveSpaceAn relProjectiveLine
open AlgebraicGeometry AlgebraicGeometry.LocallyRingedSpace
open KummerModel (splitEquiv)

noncomputable section

variable {m : ℕ}

/-! ### The chart `w'` -/

/-- The point of `P^an` with base coordinates `b` and fibre coordinate `w'` in the chart `1`, for
`x = (b, w') ∈ ℂ^{m+1}`. -/
def chart1Pt (x : Cn.{u} (m + 1)) : relProjectiveSpaceAn.{u} m 1 :=
  chartPt 1 (chartCoordHomeo x)

lemma chart1Pt_injective : Function.Injective (chart1Pt.{u} (m := m)) :=
  (chartPt_injective 1).comp chartCoordHomeo.injective

variable (N' : (AnalyticSpace.complexAffineSpace.{u} (m + 1)).Opens)

/-- The coordinates of the chart `1` of `P^an`, as holomorphic functions on `N'`. -/
def chart1Coord (k : ULift.{u} (Fin (1 + m))) : (space N').presheaf.obj (op ⊤) :=
  OkaRing.ofDifferentiableOn (fun x ↦ cptFun.{u} (baseCoord (baseOf x), fibOf x) k)
    ((differentiable_pi.1 differentiable_chart0Fun k).differentiableOn)

/-- The map `N' ⟶ P^an`, `(b, w') ↦ (b, [w' : 1])`. -/
def chart1Map : space N' ⟶ relProjectiveSpaceAn.{u} m 1 :=
  okaMapOpen (chart1Coord N') ≫ relProjectiveSpaceAnChart.{u} 1

lemma chart1Map_base (x : space N') : (chart1Map N').toLRSHom.base x = chart1Pt x.1 := by
  change (chartLRS.{u} 1).base ((okaMapOpenHom (chart1Coord N')).base x) = _
  rw [base_okaMapOpenHom, chart1Pt, chartPt]
  congr 1
  funext k
  exact OkaRing.toGlobalFun_apply (U := img (⊤ : (space N').Opens)) _
    ((mem_functor_obj_top_iff N' x.1).2 x.2)

lemma isOpenEmbedding_chart1Map : IsOpenEmbedding (chart1Map N').toLRSHom.base := by
  have : ⇑(chart1Map N').toLRSHom.base = chartPt 1 ∘ chartCoordHomeo ∘ Subtype.val :=
    funext fun x ↦ chart1Map_base N' x
  rw [this]
  exact (isOpenEmbedding_chartPt 1).comp
    (chartCoordHomeo.isOpenEmbedding.comp N'.isOpenEmbedding)

/-- The image in `P^an` of an open of `N'` in the chart `1`. -/
abbrev img1 (V : (space N').Opens) : (relProjectiveSpaceAn.{u} m 1).Opens :=
  (isOpenEmbedding_chart1Map N').isOpenMap.functor.obj V

lemma mem_img1 {V : (space N').Opens} {p : relProjectiveSpaceAn.{u} m 1} :
    p ∈ img1 N' V ↔ ∃ x ∈ img V, chart1Pt x = p := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.1, mem_img_iff.2 ⟨y.2, hy⟩, (chart1Map_base N' y).symm⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨hxN, hxV⟩ := mem_img_iff.1 hx
    exact ⟨⟨x, hxN⟩, hxV, chart1Map_base N' _⟩

lemma chart1Pt_mem_img1 {V : (space N').Opens} {x : Cn.{u} (m + 1)} :
    chart1Pt x ∈ img1 N' V ↔ x ∈ img V := by
  rw [mem_img1]
  exact ⟨fun ⟨x', hx', h⟩ ↦ chart1Pt_injective h ▸ hx', fun h ↦ ⟨x, h, rfl⟩⟩

lemma le_preimage_img1 (V : (space N').Opens) :
    V ≤ (Opens.map (chart1Map N').toLRSHom.base).obj (img1 N' V) :=
  fun x hx ↦ ⟨x, hx, rfl⟩

/-- The identification of sections of `𝒪_{P^an}` over the image of `V` in the chart `1` with
holomorphic functions on `V`. -/
def psi1 (V : (space N').Opens) :
    (relProjectiveSpaceAn.{u} m 1).presheaf.obj (op (img1 N' V)) →+*
      (space N').presheaf.obj (op V) :=
  ((space N').presheaf.map (homOfLE (le_preimage_img1 N' V)).op).hom.comp
    ((chart1Map N').toLRSHom.c.app (op (img1 N' V))).hom

lemma holFun_psi1 {V : (space N').Opens} (r : (relProjectiveSpaceAn.{u} m 1).presheaf.obj
    (op (img1 N' V))) {x : Cn.{u} (m + 1)} (hx : x ∈ img V) :
    holFun (psi1 N' V r) x = (relProjectiveSpaceAn.{u} m 1).eval (chart1Pt x)
      ((chart1Pt_mem_img1 N').2 hx) r := by
  obtain ⟨hxN, hxV⟩ := mem_img_iff.1 hx
  rw [holFun_eq_eval _ hx, psi1, RingHom.comp_apply]
  erw [eval_presheaf_map]
  erw [eval_c_app (chart1Map N').toLRSHom (chart1Map N').isCLinear ⟨x, hxN⟩
    (le_preimage_img1 N' V hxV)]
  exact eval_congr_point (chart1Map_base N' ⟨x, hxN⟩) _ _ r

lemma psi1_res {V₁ V₂ : (space N').Opens} (h : V₁ ≤ V₂)
    (r : (relProjectiveSpaceAn.{u} m 1).presheaf.obj (op (img1 N' V₂))) :
    psi1 N' V₁ ((relProjectiveSpaceAn.{u} m 1).res
      ((isOpenEmbedding_chart1Map N').isOpenMap.functor.monotone h) r) =
      (space N').res h (psi1 N' V₂ r) := by
  simp only [psi1, RingHom.coe_comp, Function.comp_apply]
  change (space N').res _ ((chart1Map N').toLRSHom.c.app _
    ((relProjectiveSpaceAn.{u} m 1).res _ r)) =
    (space N').res h ((space N').res _ ((chart1Map N').toLRSHom.c.app _ r))
  rw [c_app_res, res_res, res_res]

lemma bijective_psi1 (V : (space N').Opens) : Function.Bijective (psi1 N' V) := by
  constructor
  · intro r r' h
    refine eq_of_forall_eval_eq fun p hp ↦ ?_
    obtain ⟨x, hx, rfl⟩ := (mem_img1 N').1 hp
    have := congrArg (fun q ↦ holFun q x) h
    rwa [holFun_psi1 N' r hx, holFun_psi1 N' r' hx] at this
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
    obtain ⟨a, ha⟩ := exists_f1_eq S _ hF
    have hle : img1 N' V ≤ chartBox 1 S := by
      intro p hp
      obtain ⟨x, hx, rfl⟩ := (mem_img1 N').1 hp
      exact ⟨chartCoordHomeo x, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨(relProjectiveSpaceAn.{u} m 1).res hle a, eq_of_holFun_eq fun x hx ↦ ?_⟩
    rw [holFun_psi1 N' _ hx]
    erw [eval_presheaf_map]
    refine (f1_eq_eval a (p := chartCoordHomeo x)
      (hle ((chart1Pt_mem_img1 N').2 hx))).symm.trans ?_
    rw [ha _ ⟨x, hx, rfl⟩, Homeomorph.symm_apply_apply]

/-! ### The disc at infinity -/

variable {N N₀ : (AnalyticSpace.complexAffineSpace.{u} (m + 1)).Opens}
  {W : FiniteEtaleOver (space N₀)} {F : WeierstrassForm N N₀}
  {D : AnnulusDecomposition W F.G F.ρ}

variable (F) in
/-- The disc `G × {‖w'‖ < ρ}` of the chart at infinity, as an open of `ℂ^{m+1}`. -/
def infOpens : (AnalyticSpace.complexAffineSpace.{u} (m + 1)).Opens :=
  ⟨{x | baseOf x ∈ F.G ∧ ‖fibOf x‖ < F.ρ}, (F.isOpen_G.preimage continuous_baseOf).inter
    (isOpen_lt (continuous_norm.comp continuous_fibOf) continuous_const)⟩

lemma chart1Pt_mkPt (b : Cm.{u} m) (t : ℂ) :
    chart1Pt (mkPt b t) = chartPt 1 (baseCoord b, t) := by
  rw [chart1Pt]
  congr 1

/-- The domain of the coefficients over `V`, in the coordinates `(b, w')`. -/
def infDom (V : (space (infOpens F)).Opens) : Set (Cm.{u} m × ℂ) :=
  {z | mkPt z.1 z.2 ∈ img V}

lemma isOpen_infDom (V : (space (infOpens F)).Opens) : IsOpen (infDom V) :=
  (img V).isOpen.preimage differentiable_mkPt.continuous

variable (D) in
/-- The points of `K` over the image of `V`. -/
abbrev imgK (V : (space (infOpens F)).Opens) : TopologicalSpace.Opens (Cn.{u} (m + 1)) :=
  img ((Opens.map D.kMap.toLRSHom.base).obj (img1 (infOpens F) V))

lemma kPt_mem_imgK {V : (space (infOpens F)).Opens} (i : D.ι) {z : Cm.{u} m × ℂ}
    (hz : Kummer.powMap (D.deg i) z ∈ infDom V) : D.kPt i z ∈ D.imgK V := by
  have hzV : mkPt z.1 (z.2 ^ (D.deg i : ℕ)) ∈ img V := hz
  have hinf := img_le V _ hzV
  obtain ⟨hG, hρ⟩ : baseOf (mkPt z.1 (z.2 ^ (D.deg i : ℕ))) ∈ F.G ∧
      ‖fibOf (mkPt z.1 (z.2 ^ (D.deg i : ℕ)))‖ < F.ρ := hinf
  rw [baseOf_mkPt] at hG
  rw [fibOf_mkPt] at hρ
  have hK : D.kPt i z ∈ D.kPiece i := D.kPt_mem hG hρ
  refine mem_img_iff.2 ⟨D.mem_kOpens.2 ⟨i, hK⟩, ?_⟩
  change D.kMap.toLRSHom.base _ ∈ img1 (infOpens F) V
  rw [D.kMap_base, D.kVal_kPt hK, baseOf_kPt, ← chart1Pt_mkPt]
  exact (chart1Pt_mem_img1 _).2 hzV

/-- A point of `K` over the image of `V` is the point with its Kummer coordinates, and these lie
over `infDom V`. -/
lemma mem_infDom_of_mem_imgK {V : (space (infOpens F)).Opens} {i : D.ι} {x : Cn.{u} (m + 1)}
    (hx : x ∈ D.imgK V) (hi : x ∈ D.kPiece i) :
    Kummer.powMap (D.deg i) (baseOf x, D.kCoord x) ∈ infDom V := by
  obtain ⟨hxK, hxV⟩ := mem_img_iff.1 hx
  change D.kMap.toLRSHom.base _ ∈ img1 (infOpens F) V at hxV
  rw [D.kMap_base, ← chart1Pt_mkPt] at hxV
  change mkPt (baseOf x) (D.kCoord x ^ (D.deg i : ℕ)) ∈ img V
  rw [← D.kVal_eq_kCoord_pow hi]
  exact (chart1Pt_mem_img1 _).1 hxV

/-- The values of a section of `𝒞` on the `i`-th Kummer piece, in Kummer coordinates. -/
def kfun {O : (relProjectiveSpaceAn.{u} m 1).Opens} (s : D.capModule.val.obj (op O)) (i : D.ι)
    (z : Cm.{u} m × ℂ) : ℂ :=
  capKVal s (D.kPt i z)

lemma differentiable_kPt (i : D.ι) : Differentiable ℂ (D.kPt i) := fun z ↦
  (differentiable_mkPt (z.1, z.2 + D.kShift i)).comp z
    (differentiableAt_fst.prodMk (differentiableAt_snd.add_const _))

lemma differentiableOn_kfun {V : (space (infOpens F)).Opens}
    (s : D.capModule.val.obj (op (img1 (infOpens F) V))) (i : D.ι) :
    DifferentiableOn ℂ (kfun s i) (Kummer.powMap (D.deg i) ⁻¹' infDom V) := fun z hz ↦
  ((differentiableOn_holFun (kPart s.1)).differentiableAt
    ((D.imgK V).isOpen.mem_nhds (kPt_mem_imgK i hz))).comp z (differentiable_kPt i z)
    |>.differentiableWithinAt

/-- The coefficients of a section of `𝒞` over the disc at infinity. -/
def coeffInf {V : (space (infOpens F)).Opens} (s : D.capModule.val.obj (op (img1 (infOpens F) V)))
    (i : D.ι) : Fin (D.deg i) → Cm.{u} m × ℂ → ℂ :=
  (exists_coeff_eqOn (D.deg i).pos (isOpen_infDom V) (differentiableOn_kfun s i)).choose

lemma differentiableOn_coeffInf {V : (space (infOpens F)).Opens}
    (s : D.capModule.val.obj (op (img1 (infOpens F) V))) (i : D.ι) (j : Fin (D.deg i)) :
    DifferentiableOn ℂ (coeffInf s i j) (infDom V) :=
  (exists_coeff_eqOn (D.deg i).pos (isOpen_infDom V) (differentiableOn_kfun s i)).choose_spec.1 j

lemma kfun_eq_sum {V : (space (infOpens F)).Opens}
    (s : D.capModule.val.obj (op (img1 (infOpens F) V))) (i : D.ι) :
    EqOn (kfun s i) (fun z ↦ ∑ j : Fin (D.deg i), z.2 ^ (j : ℕ) *
      coeffInf s i j (Kummer.powMap (D.deg i) z)) (Kummer.powMap (D.deg i) ⁻¹' infDom V) :=
  (exists_coeff_eqOn (D.deg i).pos (isOpen_infDom V) (differentiableOn_kfun s i)).choose_spec.2

lemma coeffInf_unique {V : (space (infOpens F)).Opens}
    (s : D.capModule.val.obj (op (img1 (infOpens F) V))) (i : D.ι)
    {g : Fin (D.deg i) → Cm.{u} m × ℂ → ℂ} (hg : ∀ j, ContinuousOn (g j) (infDom V))
    (h : ∀ z ∈ Kummer.powMap (D.deg i) ⁻¹' infDom V,
      kfun s i z = ∑ j : Fin (D.deg i), z.2 ^ (j : ℕ) * g j (Kummer.powMap (D.deg i) z))
    (j : Fin (D.deg i)) : EqOn (coeffInf s i j) (g j) (infDom V) :=
  eqOn_of_coeff (D.deg i).pos (isOpen_infDom V)
    (fun j ↦ (differentiableOn_coeffInf s i j).continuousOn) hg
    (fun z hz ↦ (kfun_eq_sum s i hz).symm.trans (h z hz)) j

lemma mem_infDom_coord {V : (space (infOpens F)).Opens} {x : Cn.{u} (m + 1)} (hx : x ∈ img V) :
    ((baseOf x, fibOf x) : Cm.{u} m × ℂ) ∈ infDom V := by
  change mkPt (baseOf x) (fibOf x) ∈ img V
  rw [mkPt_baseOf_fibOf]
  exact hx

lemma differentiableOn_coeffInf_coord {V : (space (infOpens F)).Opens}
    (s : D.capModule.val.obj (op (img1 (infOpens F) V))) (i : D.ι) (j : Fin (D.deg i)) :
    DifferentiableOn ℂ (fun x : Cn.{u} (m + 1) ↦ coeffInf s i j (baseOf x, fibOf x)) (img V) :=
  (differentiableOn_coeffInf s i j).comp
    (differentiable_baseOf.prodMk differentiable_fibOf).differentiableOn
    fun _ hx ↦ mem_infDom_coord hx

variable (D) in
/-- The index set `Σᵢ Fin kᵢ` of the coefficients at infinity. -/
abbrev infIdx : Type u := Σ i, Fin (D.deg i)

open Classical in
/-- **The chart map at infinity** on sections: the coefficients. -/
def phiInfFun {V : (space (infOpens F)).Opens}
    (s : D.capModule.val.obj (op (img1 (infOpens F) V))) :
    (SheafOfModules.free (R := (space (infOpens F)).ringSheaf) D.infIdx).val.obj (op V) :=
  SheafOfModules.freeEvalSymm (op V) fun ij ↦
    OkaRing.ofDifferentiableOn _ (differentiableOn_coeffInf_coord s ij.1 ij.2)

open Classical in
lemma holFun_freeEval_phiInfFun {V : (space (infOpens F)).Opens}
    (s : D.capModule.val.obj (op (img1 (infOpens F) V))) (ij : D.infIdx) {x : Cn.{u} (m + 1)}
    (hx : x ∈ img V) :
    holFun (V := V) (SheafOfModules.freeEval (op V) (phiInfFun s) ij) x =
      coeffInf s ij.1 ij.2 (baseOf x, fibOf x) := by
  rw [phiInfFun, SheafOfModules.freeEval_freeEvalSymm]
  exact holFun_ofDifferentiableOn _ hx

open Classical in
/-- A section of the free sheaf over `V` with prescribed values of its coordinates. -/
lemma free_ext {V : (space (infOpens F)).Opens}
    {τ τ' : (SheafOfModules.free (R := (space (infOpens F)).ringSheaf) D.infIdx).val.obj (op V)}
    (h : ∀ ij, ∀ x ∈ img V, holFun (V := V) (SheafOfModules.freeEval (op V) τ ij) x =
      holFun (V := V) (SheafOfModules.freeEval (op V) τ' ij) x) : τ = τ' :=
  SheafOfModules.freeEval_injective _ (funext fun ij ↦ eq_of_holFun_eq fun x hx ↦ h ij x hx)

lemma kfun_add {O : (relProjectiveSpaceAn.{u} m 1).Opens} (s t : D.capModule.val.obj (op O))
    (i : D.ι) {z : Cm.{u} m × ℂ}
    (hz : D.kPt i z ∈ img ((Opens.map D.kMap.toLRSHom.base).obj O)) :
    kfun (s + t) i z = kfun s i z + kfun t i z :=
  capKVal_add s t hz

lemma kfun_zero {O : (relProjectiveSpaceAn.{u} m 1).Opens} (i : D.ι) {z : Cm.{u} m × ℂ}
    (hz : D.kPt i z ∈ img ((Opens.map D.kMap.toLRSHom.base).obj O)) :
    kfun (0 : D.capModule.val.obj (op O)) i z = 0 := by
  change holFun (kPart (0 : D.capAmb.val.obj (op O))) _ = 0
  rw [kPart_zero, holFun_zero hz]

open Classical in
/-- **The chart map at infinity**, as an additive map. -/
def phiInf (V : (space (infOpens F)).Opens) :
    D.capModule.val.obj (op (img1 (infOpens F) V)) →+
      (SheafOfModules.free (R := (space (infOpens F)).ringSheaf) D.infIdx).val.obj (op V) where
  toFun s := phiInfFun s
  map_zero' := free_ext fun ij x hx ↦ by
    rw [holFun_freeEval_phiInfFun _ ij hx, map_zero, Pi.zero_apply]
    erw [holFun_zero hx]
    refine coeffInf_unique _ ij.1 (g := fun _ _ ↦ 0) (fun _ ↦ continuousOn_const)
      (fun z hz ↦ ?_) ij.2 (mem_infDom_coord hx)
    rw [kfun_zero _ (kPt_mem_imgK ij.1 hz)]
    simp
  map_add' s t := free_ext fun ij x hx ↦ by
    rw [holFun_freeEval_phiInfFun _ ij hx, map_add, Pi.add_apply]
    erw [holFun_add _ _ hx]
    rw [holFun_freeEval_phiInfFun _ ij hx, holFun_freeEval_phiInfFun _ ij hx]
    refine coeffInf_unique _ ij.1 (g := fun j z ↦ coeffInf s ij.1 j z + coeffInf t ij.1 j z)
      (fun j ↦ ((differentiableOn_coeffInf s _ j).add
        (differentiableOn_coeffInf t _ j)).continuousOn)
      (fun z hz ↦ ?_) ij.2 (mem_infDom_coord hx)
    rw [kfun_add _ _ _ (kPt_mem_imgK ij.1 hz), kfun_eq_sum s _ hz, kfun_eq_sum t _ hz,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ ↦ by ring

open Classical in
lemma holFun_freeEval_phiInf {V : (space (infOpens F)).Opens}
    (s : D.capModule.val.obj (op (img1 (infOpens F) V))) (ij : D.infIdx) {x : Cn.{u} (m + 1)}
    (hx : x ∈ img V) :
    holFun (V := V) (SheafOfModules.freeEval (op V) (phiInf V s) ij) x =
      coeffInf s ij.1 ij.2 (baseOf x, fibOf x) :=
  holFun_freeEval_phiInfFun s ij hx

/-- **The points of `W` over the disc at infinity lie over the annulus.** -/
lemma pt_mem_annulusRegion (h₀ : N₀ ≤ N) {V : (space (infOpens F)).Opens} {w : W.left}
    (hw : w ∈ (Opens.map (projW W).toLRSHom.base).obj (img1 (infOpens F) V)) :
    pt W w ∈ annulusRegion F.G F.ρ := by
  change (projW W).toLRSHom.base w ∈ img1 (infOpens F) V at hw
  rw [projW_base] at hw
  obtain ⟨y, hy, hyw⟩ := (mem_img1 _).1 hw
  obtain ⟨h0, e⟩ := chartPt_one_eq_chartPt_zero hyw
  have e2 : fibOf (pt W w) = (fibOf y)⁻¹ := congrArg Prod.snd e
  have hyD := img_le V y hy
  have hρy : ‖fibOf y‖ < F.ρ := hyD.2
  have hwN := (F.mem_N (pt W w)).1 (h₀ (pt_mem W w))
  refine ⟨hwN.1, ?_, hwN.2⟩
  change F.ρ⁻¹ < ‖fibOf (pt W w)‖
  rw [e2, norm_inv]
  exact (inv_lt_inv₀ F.pos_ρ (norm_pos_iff.2 h0)).2 hρy

variable (h₀ : N₀ ≤ N)

open Classical in
lemma coeffInf_eq_of_phiInf_eq {V : (space (infOpens F)).Opens}
    {s t : D.capModule.val.obj (op (img1 (infOpens F) V))} (h : phiInf V s = phiInf V t)
    (i : D.ι) (j : Fin (D.deg i)) {z : Cm.{u} m × ℂ} (hz : z ∈ infDom V) :
    coeffInf s i j z = coeffInf t i j z := by
  have := congrArg (fun τ ↦ holFun (V := V) (SheafOfModules.freeEval (op V) τ ⟨i, j⟩)
    (mkPt z.1 z.2)) h
  rwa [holFun_freeEval_phiInf s _ hz, holFun_freeEval_phiInf t _ hz, baseOf_mkPt,
    fibOf_mkPt] at this

include h₀ in
lemma injective_phiInf (V : (space (infOpens F)).Opens) :
    Function.Injective (phiInf (D := D) V) := by
  intro s t h
  have hK : ∀ x ∈ D.imgK V, capKVal s x = capKVal t x := fun x hx ↦ by
    obtain ⟨hxK, -⟩ := mem_img_iff.1 hx
    obtain ⟨i, hi⟩ := D.mem_kOpens.1 hxK
    have hz := mem_infDom_of_mem_imgK hx hi
    have e : D.kPt i (baseOf x, D.kCoord x) = x := D.kPt_kCoord hi
    change capKVal s x = capKVal t x
    rw [← e]
    change kfun s i _ = kfun t i _
    rw [kfun_eq_sum s i hz, kfun_eq_sum t i hz]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [coeffInf_eq_of_phiInf_eq h i j hz]
  refine capModule_ext (fun w hw ↦ ?_) hK
  have hA : w ∈ pt W ⁻¹' annulusRegion F.G F.ρ := pt_mem_annulusRegion h₀ hw
  rw [← D.range_eq] at hA
  obtain ⟨⟨i, z⟩, rfl⟩ := hA
  rw [capWVal_compat s i z hw, capWVal_compat t i z hw]
  exact hK _ (kPt_mem_img hw)

lemma not_mem_removedW_of_mem_img1 {V : (space (infOpens F)).Opens}
    {p : relProjectiveSpaceAn.{u} m 1} (hp : p ∈ img1 (infOpens F) V) : p ∉ removedW N N₀ := by
  rintro ⟨x, ⟨hxN, hxN₀⟩, rfl⟩
  obtain ⟨y, hy, hyx⟩ := (mem_img1 _).1 hp
  obtain ⟨h0, e⟩ := chartPt_one_eq_chartPt_zero hyx
  have e2 : fibOf x = (fibOf y)⁻¹ := congrArg Prod.snd e
  have hρy : ‖fibOf y‖ < F.ρ := (img_le V y hy).2
  have hroot : (evalPoly F.P (baseOf x)).IsRoot (fibOf x) := by
    by_contra hne
    exact hxN₀ ((F.mem_N₀ x hxN).2 hne)
  have hlt := F.norm_lt_of_isRoot _ ((F.mem_N x).1 hxN).1 _ hroot
  rw [e2, norm_inv] at hlt
  have := (inv_lt_inv₀ F.pos_ρ (norm_pos_iff.2 h0)).2 hρy
  exact lt_asymm hlt this

/-! ### Surjectivity -/

lemma kPt_mem_kPiece_of {V : (space (infOpens F)).Opens} (i : D.ι) {z : Cm.{u} m × ℂ}
    (hz : Kummer.powMap (D.deg i) z ∈ infDom V) : D.kPt i z ∈ D.kPiece i := by
  have hzV : mkPt z.1 (z.2 ^ (D.deg i : ℕ)) ∈ img V := hz
  obtain ⟨hG, hρ⟩ : baseOf (mkPt z.1 (z.2 ^ (D.deg i : ℕ))) ∈ F.G ∧
      ‖fibOf (mkPt z.1 (z.2 ^ (D.deg i : ℕ)))‖ < F.ρ := img_le V _ hzV
  rw [baseOf_mkPt] at hG
  rw [fibOf_mkPt] at hρ
  exact D.kPt_mem hG hρ

open Classical in
/-- The coordinate functions of a section of the free sheaf, in the coordinates `(b, w')`. -/
def freeCoeff {V : (space (infOpens F)).Opens}
    (τ : (SheafOfModules.free (R := (space (infOpens F)).ringSheaf) D.infIdx).val.obj (op V))
    (ij : D.infIdx) (z : Cm.{u} m × ℂ) : ℂ :=
  holFun (V := V) (SheafOfModules.freeEval (op V) τ ij) (mkPt z.1 z.2)

lemma differentiableOn_freeCoeff {V : (space (infOpens F)).Opens}
    (τ : (SheafOfModules.free (R := (space (infOpens F)).ringSheaf) D.infIdx).val.obj (op V))
    (ij : D.infIdx) : DifferentiableOn ℂ (freeCoeff τ ij) (infDom V) := fun z hz ↦
  (((differentiableOn_holFun _).differentiableAt ((img V).isOpen.mem_nhds hz)).comp z
    (differentiable_mkPt (z.1, z.2))).differentiableWithinAt

/-- The function on the `i`-th Kummer piece with prescribed coefficients. -/
def freeKummer {V : (space (infOpens F)).Opens}
    (τ : (SheafOfModules.free (R := (space (infOpens F)).ringSheaf) D.infIdx).val.obj (op V))
    (i : D.ι) (z : Cm.{u} m × ℂ) : ℂ :=
  ∑ j : Fin (D.deg i), z.2 ^ (j : ℕ) * freeCoeff τ ⟨i, j⟩ (Kummer.powMap (D.deg i) z)

lemma differentiableOn_freeKummer {V : (space (infOpens F)).Opens}
    (τ : (SheafOfModules.free (R := (space (infOpens F)).ringSheaf) D.infIdx).val.obj (op V))
    (i : D.ι) :
    DifferentiableOn ℂ (freeKummer τ i) (Kummer.powMap (D.deg i) ⁻¹' infDom V) :=
  DifferentiableOn.fun_sum fun j _ ↦ (differentiableOn_snd.pow _).mul
    ((differentiableOn_freeCoeff τ ⟨i, j⟩).comp
      (Kummer.differentiable_powMap _).differentiableOn fun _ hz ↦ hz)

open Classical in
/-- The function on `K` with prescribed coefficients. -/
def freeKFun {V : (space (infOpens F)).Opens}
    (τ : (SheafOfModules.free (R := (space (infOpens F)).ringSheaf) D.infIdx).val.obj (op V))
    (x : Cn.{u} (m + 1)) : ℂ :=
  ∑ i, if x ∈ D.kPiece i then freeKummer τ i (baseOf x, D.kCoord x) else 0

lemma freeKFun_of_mem {V : (space (infOpens F)).Opens}
    (τ : (SheafOfModules.free (R := (space (infOpens F)).ringSheaf) D.infIdx).val.obj (op V))
    {i : D.ι} {x : Cn.{u} (m + 1)} (hx : x ∈ D.kPiece i) :
    freeKFun τ x = freeKummer τ i (baseOf x, D.kCoord x) := by
  classical
  rw [freeKFun, Finset.sum_eq_single i
    (fun j _ hji ↦ if_neg fun hj ↦ hji (D.eq_of_mem_kPiece hj hx))
    (fun h ↦ absurd (Finset.mem_univ i) h), if_pos hx]

lemma freeKFun_kPt {V : (space (infOpens F)).Opens}
    (τ : (SheafOfModules.free (R := (space (infOpens F)).ringSheaf) D.infIdx).val.obj (op V))
    {i : D.ι} {z : Cm.{u} m × ℂ} (hz : D.kPt i z ∈ D.kPiece i) :
    freeKFun τ (D.kPt i z) = freeKummer τ i z := by
  rw [freeKFun_of_mem τ hz, baseOf_kPt, D.kCoord_kPt hz]

lemma differentiableOn_freeKFun {V : (space (infOpens F)).Opens}
    (τ : (SheafOfModules.free (R := (space (infOpens F)).ringSheaf) D.infIdx).val.obj (op V)) :
    DifferentiableOn ℂ (freeKFun τ) (D.imgK V) := by
  intro x hx
  obtain ⟨hxK, -⟩ := mem_img_iff.1 hx
  obtain ⟨i, hi⟩ := D.mem_kOpens.1 hxK
  have hz := mem_infDom_of_mem_imgK hx hi
  have hd : DifferentiableAt ℂ (freeKummer τ i) (baseOf x, D.kCoord x) :=
    (differentiableOn_freeKummer τ i).differentiableAt
      (((isOpen_infDom V).preimage (Kummer.differentiable_powMap _).continuous).mem_nhds hz)
  have hφ : DifferentiableAt ℂ (fun y : Cn.{u} (m + 1) ↦ (baseOf y, D.kCoord y)) x :=
    (differentiable_baseOf x).prodMk (D.differentiableOn_kCoord.differentiableAt
      ((D.kOpens).isOpen.mem_nhds hxK))
  refine ((hd.comp x hφ).congr_of_eventuallyEq ?_).differentiableWithinAt
  filter_upwards [(D.isOpen_kPiece i).mem_nhds hi] with y hy
  exact freeKFun_of_mem τ hy

include h₀ in
lemma exists_wPart_of_free {V : (space (infOpens F)).Opens}
    (τ : (SheafOfModules.free (R := (space (infOpens F)).ringSheaf) D.infIdx).val.obj (op V)) :
    ∃ a : W.left.presheaf.obj
        (op ((Opens.map (projW W).toLRSHom.base).obj (img1 (infOpens F) V))),
      ∀ (i : D.ι) (z : KummerAnnulus.base F.G F.ρ⁻¹ F.ρ (D.deg i)),
        D.toFun ⟨i, z⟩ ∈ (Opens.map (projW W).toLRSHom.base).obj (img1 (infOpens F) V) →
          evalFun a (D.toFun ⟨i, z⟩) = freeKummer τ i (invCoord z.1) := by
  obtain ⟨a, ha⟩ := D.exists_eval_eq_of_kummer F.isOpen_G
    (O := (Opens.map (projW W).toLRSHom.base).obj (img1 (infOpens F) V))
    (fun w hw ↦ pt_mem_annulusRegion h₀ hw) (fun i z ↦ freeKummer τ i (invCoord z))
    fun i z ⟨hz, hzO⟩ ↦ by
      have hx := kPt_mem_img (z := ⟨z, hz⟩) hzO
      have hi := D.kPt_invCoord_mem hz
      have hmem := mem_infDom_of_mem_imgK hx hi
      rw [baseOf_kPt, D.kCoord_kPt hi] at hmem
      have h0 : z.2 ≠ 0 := norm_pos_iff.1
        (KummerAnnulus.pos_of_mem_base F.G (inv_nonneg.2 F.pos_ρ.le) (D.deg i).ne_zero hz)
      have hd : DifferentiableAt ℂ (freeKummer τ i) (invCoord z) :=
        (differentiableOn_freeKummer τ i).differentiableAt
          (((isOpen_infDom V).preimage (Kummer.differentiable_powMap _).continuous).mem_nhds
            hmem)
      exact hd.comp z (differentiableAt_fst.prodMk (differentiableAt_snd.inv h0))
  exact ⟨a, fun i z hz ↦ ha i z.1 z.2 hz⟩

open Classical in
include h₀ in
lemma surjective_phiInf (V : (space (infOpens F)).Opens) :
    Function.Surjective (phiInf (D := D) V) := by
  intro τ
  obtain ⟨a, ha⟩ := exists_wPart_of_free h₀ τ
  have hb : IsBoundedNear (projW W) (removedW N N₀) a := fun p hp hpr ↦
    absurd hpr (not_mem_removedW_of_mem_img1 hp)
  set g : (space D.kOpens).presheaf.obj
      (op ((Opens.map D.kMap.toLRSHom.base).obj (img1 (infOpens F) V))) :=
    OkaRing.ofDifferentiableOn _ (differentiableOn_freeKFun (D := D) τ)
  have hg : ∀ (i : D.ι) (z : Cm.{u} m × ℂ), D.kPt i z ∈ D.kPiece i → D.kPt i z ∈ D.imgK V →
      holFun g (D.kPt i z) = freeKummer τ i z := fun i z hi hx ↦ by
    rw [holFun_ofDifferentiableOn _ hx, freeKFun_kPt τ hi]
  have hc : ∀ (i : D.ι) (z : KummerAnnulus.base F.G F.ρ⁻¹ F.ρ (D.deg i)),
      D.toFun ⟨i, z⟩ ∈ (Opens.map (projW W).toLRSHom.base).obj (img1 (infOpens F) V) →
        evalFun a (D.toFun ⟨i, z⟩) = holFun g (D.kPt i (invCoord z.1)) := fun i z hz ↦ by
    rw [ha i z hz, hg i _ (D.kPt_invCoord_mem z.2) (kPt_mem_img hz)]
  refine ⟨D.mkCap a hb g hc, free_ext fun ij x hx ↦ ?_⟩
  rw [holFun_freeEval_phiInf _ ij hx]
  have e : holFun (V := V) (SheafOfModules.freeEval (op V) τ ij) x =
      freeCoeff τ ij (baseOf x, fibOf x) := by
    rw [freeCoeff, mkPt_baseOf_fibOf]
  rw [e]
  obtain ⟨i, j⟩ := ij
  refine coeffInf_unique _ i (g := fun j ↦ freeCoeff τ ⟨i, j⟩)
    (fun j ↦ (differentiableOn_freeCoeff τ _).continuousOn) (fun z hz ↦ ?_) j
    (mem_infDom_coord hx)
  have hx' := kPt_mem_imgK i hz
  have hi : D.kPt i z ∈ D.kPiece i := kPt_mem_kPiece_of i hz
  change capKVal _ _ = _
  rw [capKVal, kPart_mkCap, hg i z hi hx']
  rfl

/-! ### Compatibility with restriction and scalars -/

open Classical in
lemma holFun_freeEval_sectRes {V₁ V₂ : (space (infOpens F)).Opens} (h : V₁ ≤ V₂)
    (τ : (SheafOfModules.free (R := (space (infOpens F)).ringSheaf) D.infIdx).val.obj (op V₂))
    (ij : D.infIdx) {x : Cn.{u} (m + 1)} (hx : x ∈ img V₁) :
    holFun (V := V₁) (SheafOfModules.freeEval (op V₁) (sectRes _ h τ) ij) x =
      holFun (V := V₂) (SheafOfModules.freeEval (op V₂) τ ij) x := by
  erw [SheafOfModules.freeEval_naturality]
  exact holFun_map h _ hx

open Classical in
lemma phiInf_res {V₁ V₂ : (space (infOpens F)).Opens} (h : V₁ ≤ V₂)
    (s : D.capModule.val.obj (op (img1 (infOpens F) V₂))) :
    phiInf V₁ (sectRes D.capModule
      ((isOpenEmbedding_chart1Map (infOpens F)).isOpenMap.functor.monotone h) s) =
      sectRes _ h (phiInf V₂ s) :=
  free_ext fun ij x hx ↦ by
    rw [holFun_freeEval_sectRes h _ ij hx, holFun_freeEval_phiInf _ ij hx,
      holFun_freeEval_phiInf _ ij (img_mono h hx)]
    have hdom : infDom V₁ ⊆ infDom V₂ := fun z hz ↦ img_mono h hz
    refine coeffInf_unique _ ij.1 (g := coeffInf s ij.1)
      (fun j ↦ ((differentiableOn_coeffInf s _ j).mono hdom).continuousOn) (fun z hz ↦ ?_) ij.2
      (mem_infDom_coord hx)
    change capKVal _ _ = _
    rw [capKVal_res _ _ (kPt_mem_imgK ij.1 hz)]
    exact kfun_eq_sum s ij.1 (hdom hz)

lemma eval_kMap_kPt {V : (space (infOpens F)).Opens}
    (r : (relProjectiveSpaceAn.{u} m 1).presheaf.obj (op (img1 (infOpens F) V))) (i : D.ι)
    {z : Cm.{u} m × ℂ} (hz : Kummer.powMap (D.deg i) z ∈ infDom V) :
    (relProjectiveSpaceAn.{u} m 1).eval (D.kMap.toLRSHom.base ⟨D.kPt i z,
      img_le _ _ (kPt_mem_imgK i hz)⟩) (mem_img_iff.1 (kPt_mem_imgK i hz)).2 r =
      holFun (psi1 (infOpens F) V r) (mkPt z.1 (z.2 ^ (D.deg i : ℕ))) := by
  rw [holFun_psi1 _ r (show mkPt z.1 (z.2 ^ (D.deg i : ℕ)) ∈ img V from hz)]
  refine eval_congr_point ?_ _ _ r
  rw [D.kMap_base, D.kVal_kPt (kPt_mem_kPiece_of i hz), baseOf_kPt, chart1Pt_mkPt]

open Classical in
lemma holFun_freeEval_smul {V : (space (infOpens F)).Opens}
    (c : (space (infOpens F)).presheaf.obj (op V))
    (τ : (SheafOfModules.free (R := (space (infOpens F)).ringSheaf) D.infIdx).val.obj (op V))
    (ij : D.infIdx) {x : Cn.{u} (m + 1)} (hx : x ∈ img V) :
    holFun (V := V) (SheafOfModules.freeEval (op V) (c • τ) ij) x =
      holFun c x * holFun (V := V) (SheafOfModules.freeEval (op V) τ ij) x := by
  have h2 := congrFun ((SheafOfModules.freeEval (op V)).map_smul c τ) ij
  erw [h2]
  exact holFun_mul _ _ hx

open Classical in
lemma phiInf_smul (V : (space (infOpens F)).Opens)
    (r : (relProjectiveSpaceAn.{u} m 1).presheaf.obj (op (img1 (infOpens F) V)))
    (s : D.capModule.val.obj (op (img1 (infOpens F) V))) :
    phiInf V (r • s) = psi1 (infOpens F) V r • phiInf V s :=
  free_ext fun ij x hx ↦ by
    rw [holFun_freeEval_phiInf _ ij hx]
    refine Eq.trans ?_ (holFun_freeEval_smul _ _ ij hx).symm
    rw [holFun_freeEval_phiInf _ ij hx]
    set r' : Cm.{u} m × ℂ → ℂ := fun z ↦ holFun (psi1 (infOpens F) V r) (mkPt z.1 z.2)
    have hr' : DifferentiableOn ℂ r' (infDom V) := fun z hz ↦
      (((differentiableOn_holFun _).differentiableAt ((img V).isOpen.mem_nhds hz)).comp z
        (differentiable_mkPt (z.1, z.2))).differentiableWithinAt
    have e : holFun (psi1 (infOpens F) V r) x = r' (baseOf x, fibOf x) := by
      simp only [r', mkPt_baseOf_fibOf]
    rw [e]
    refine coeffInf_unique _ ij.1 (g := fun j z ↦ r' z * coeffInf s ij.1 j z)
      (fun j ↦ (hr'.mul (differentiableOn_coeffInf s _ j)).continuousOn) (fun z hz ↦ ?_) ij.2
      (mem_infDom_coord hx)
    change capKVal _ _ = _
    rw [capKVal_smul _ _ (kPt_mem_imgK ij.1 hz), eval_kMap_kPt r ij.1 hz]
    change _ * kfun s ij.1 z = _
    rw [kfun_eq_sum s ij.1 hz, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by simp only [r', Kummer.powMap_apply]; ring

/-! ### The chart at infinity -/

variable (D) in
open Classical in
/-- **The chart of `𝒞` at infinity**: over the disc `G × {‖w'‖ < ρ}`, the sheaf of the cap is
free of rank `∑ kᵢ`, via the Kummer coefficients. -/
def chartInfModuleChart :
    ModuleChart D.capModule (SheafOfModules.free (R := (space (infOpens F)).ringSheaf) D.infIdx)
    where
  g := (chart1Map (infOpens F)).toLRSHom.base
  isOpenEmbedding := isOpenEmbedding_chart1Map (infOpens F)
  ψ := psi1 (infOpens F)
  bijective_ψ := bijective_psi1 (infOpens F)
  ψ_res := psi1_res (infOpens F)
  φ := phiInf
  bijective_φ V := ⟨injective_phiInf h₀ V, surjective_phiInf h₀ V⟩
  φ_res := phiInf_res
  φ_smul := phiInf_smul

include h₀ in
/-- **The local conditions for coherence of `𝒞` at the points of the disc at infinity.** -/
theorem capModule_isCoherentAt_chartInf (x : space (infOpens F)) :
    IsLocallyFinitelyGeneratedModuleAt D.capModule (chart1Pt x.1) ∧
      HasLocalModuleRelationsAt D.capModule (chart1Pt x.1) := by
  classical
  rw [← chart1Map_base (infOpens F) x]
  have hcoh : (SheafOfModules.free (R := (space (infOpens F)).ringSheaf) D.infIdx).IsCoherent :=
    AnalyticSpace.isCoherent_free _ _
  exact ⟨(D.chartInfModuleChart h₀).isLocallyFinitelyGeneratedModuleAt
      (isLocallyFinitelyGeneratedModule_of_isFiniteType _ x),
    (D.chartInfModuleChart h₀).hasLocalModuleRelationsAt
      ((hasLocalModuleRelations_iff _).1 (hasLocalModuleRelations_of_isCoherent _) x)⟩

end

end ComplexAnalytic.Cap.AnnulusDecomposition
