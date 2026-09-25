/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.ES.Codim2.BlowupChartData
import Oka.Analytification.RET.ES.Codim2.MapPullback
import Oka.Geometry.RingedSpace.LocallyRingedSpace.CoherentModuleOpenEmbedding
import Oka.Geometry.RingedSpace.LocallyRingedSpace.RestrictModulesOver
import Oka.Geometry.RingedSpace.LocallyRingedSpace.HomSheafCoherent
import Oka.Analytification.RET.ES.CurveExtension

/-!
# Coherence of the bounded sections on the blow-up from the charts

Keep the notation of `Oka/Analytification/RET/ES/Codim2/BlowupChartData.lean`: `C` is the centre
`{t = 0, w = φ}`, `𝒢` is the sheaf on `P^an = ℂⁿ × ℙ¹` of
`Oka/Analytification/RET/ES/Codim2/BlowupSheaf.lean` for `τ = t`, `ω = w - φ`, and `W₁`, `W₂` are
the pullbacks of `W` to the two charts `ch₁`, `ch₂` of the blow-up
(`ComplexAnalytic.BoundedSections.IsMapPullback`, e.g. `ComplexAnalytic.BoundedSections.mapCover`).
If the sheaves of bounded sections of `W₁` and `W₂` are coherent, then `𝒢` is coherent over
`N × ℙ¹` (`ComplexAnalytic.BoundedSections.BlowupCentre.isCoherent_module`).

Over the part `Bᵢ` of the chart `i - 1` of `P^an` which retracts onto the chart `chᵢ`, `𝒢` is the
pushforward of the bounded sections of `Wᵢ` along the embedding `Γᵢ` (`ModuleChart` of
`…BlowupChartPkg.moduleChart`): a section of `𝒢` is a function on `W`, and composing with
`βᵢ : Wᵢ → W` gives a section over the preimage under `Γᵢ`. Pushforwards along `Γᵢ` preserve
coherence (`ComplexAnalytic.BoundedSections.GraphEmbeddingData.isCoherent_pushforward`). The
remaining points of `N × ℙ¹` lie off the blow-up `Ñ`, and near them `𝒢` vanishes.

## Main definitions

- `ComplexAnalytic.BoundedSections.BlowupChartPkg`: an embedding of a chart of the blow-up into a
  chart of `P^an`, compatible with `x ↦ (x, [τ(x) : ω(x)])`.
- `ComplexAnalytic.BoundedSections.BlowupCentre.chart₁Pkg`, `…BlowupCentre.chart₂Pkg`: the two
  charts.

## Main results

- `ComplexAnalytic.BoundedSections.BlowupCentre.isCoherent_module`: coherence of `𝒢` over
  `N × ℙ¹`.
-/

open CategoryTheory Opposite AlgebraicGeometry Topology TopologicalSpace Filter

universe u

namespace ComplexAnalytic.BoundedSections

open AnalyticSpace relProjectiveSpaceAn relProjectiveLine AlgebraicGeometry.LocallyRingedSpace

noncomputable section

variable {n : ℕ} {N N₀ : (AnalyticSpace.complexAffineSpace.{u} n).Opens} {h₀ : N₀ ≤ N}

/-- **A chart of the blow-up in a chart of `P^an`**: an embedding `Γ : A → B` into the chart `i`
of `P^an = ℂⁿ × ℙ¹` over `N`, and a holomorphic open embedding `χ : A° → N°` with
`(χ x, [τ : ω]) = Γ x` for `x ∈ A°`, such that every point of `N°` whose image lies in the chart
`i` is in the image of `χ`. -/
structure BlowupChartPkg (c : BlowupData N N₀) where
  /-- The chart of `P^an`. -/
  i : Fin 2
  /-- The chart of the blow-up. -/
  A : (AnalyticSpace.complexAffineSpace.{u} n).Opens
  /-- The part of the chart of the blow-up over `N°`. -/
  A₀ : (AnalyticSpace.complexAffineSpace.{u} n).Opens
  le : A₀ ≤ A
  /-- The part of the chart of `P^an` retracting onto `A`. -/
  B : (AnalyticSpace.complexAffineSpace.{u} (1 + n)).Opens
  /-- The embedding. -/
  G : GraphEmbeddingData A B
  /-- The chart map on `A°`. -/
  Φ : ChartMap A₀ N₀
  cptBase_mem : ∀ p ∈ B, cptBase p ∈ N
  compat : ∀ x ∈ A₀, c.blowupPt (Φ.χ x) = (chartLRS.{u} (m := n) (N := 1) i).base (G.Γ x)
  cptBase_Γ : ∀ x ∈ A, cptBase (G.Γ x) = Φ.χ x
  mem_range : ∀ x ∈ N₀, c.blowupPt x ∈ Set.range (chartLRS.{u} (m := n) (N := 1) i).base →
    x ∈ Φ.R ∧ Φ.χInv x ∈ A₀
  continuousOn_h : ContinuousOn G.h {p | cptBase p ∈ N}
  mem_B_of_h_eq_zero : ∀ p, cptBase p ∈ N → G.h p = 0 → p ∈ B

namespace BlowupCentre

variable (C : BlowupCentre N N₀) (h₀)

/-- The first chart as a `ComplexAnalytic.BoundedSections.ChartMap`. -/
def chart₁Map : ChartMap (C.M₁₀ h₀) N₀ where
  χ := C.ch₁
  χInv := C.ch₁Inv
  R := {y | y ∈ cyl N C.iw ∧ y C.it ≠ 0}
  isOpen_R := (isOpen_cyl N C.iw).inter (isOpen_ne_fun (continuous_apply C.it) continuous_const)
  differentiableOn_χ := C.differentiableOn_ch₁.mono fun _ hx ↦ C.mem_cyl_of_ch₁_mem (h₀ hx)
  differentiableOn_χInv := C.differentiableOn_ch₁Inv
  mem_iff _ := Iff.rfl
  χ_mem_R _ hx := ⟨mem_cyl_of_mem (h₀ hx), C.ne_zero _ hx⟩
  χInv_χ _ hx := C.ch₁Inv_ch₁ (C.it_ne_zero_of_mem_M₁₀ h₀ hx)
  χ_χInv _ hy _ := C.ch₁_ch₁Inv hy.2

/-- The second chart as a `ComplexAnalytic.BoundedSections.ChartMap`. -/
def chart₂Map : ChartMap (C.M₂₀ h₀) N₀ where
  χ := C.ch₂
  χInv := C.ch₂Inv
  R := {y | y ∈ cyl N C.iw ∧ y C.iw - C.φ y ≠ 0}
  isOpen_R := by
    have hc : ContinuousOn (fun y ↦ y C.iw - C.φ y) (cyl N C.iw) :=
      (continuous_apply C.iw).continuousOn.sub C.differentiableOn_φ.continuousOn
    exact hc.isOpen_inter_preimage (isOpen_cyl N C.iw) isOpen_compl_singleton
  differentiableOn_χ := C.differentiableOn_ch₂.mono fun _ ha ↦ C.mem_dom₂_of_ch₂_mem (h₀ ha)
  differentiableOn_χInv := C.differentiableOn_ch₂Inv
  mem_iff _ := Iff.rfl
  χ_mem_R a ha := by
    refine ⟨mem_cyl_of_mem (h₀ ha), ?_⟩
    rw [ch₂_iw, φ_ch₂, add_sub_cancel_left]
    exact (C.ne_zero_of_mem_M₂₀ h₀ ha).1
  χInv_χ a ha := C.ch₂Inv_ch₂ (C.ne_zero_of_mem_M₂₀ h₀ ha).1
  χ_χInv _ hy _ := C.ch₂_ch₂Inv hy.2

/-- **The first chart of the blow-up in the chart `0` of `P^an`.** -/
def chart₁Pkg : BlowupChartPkg C.toBlowupData where
  i := 0
  A := C.M₁
  A₀ := C.M₁₀ h₀
  le := C.M₁₀_le h₀
  B := C.B₁
  G := C.graph₁
  Φ := C.chart₁Map h₀
  cptBase_mem _ hp := hp.1
  compat x hx := C.blowupPt_ch₁ (C.it_ne_zero_of_mem_M₁₀ h₀ hx)
  cptBase_Γ x _ := by
    change cptBase (C.Γ₁ x) = C.ch₁ x
    simp [Γ₁]
  mem_range x hx _ := by
    refine ⟨⟨mem_cyl_of_mem (h₀ hx), C.ne_zero x hx⟩, ?_⟩
    change C.ch₁ (C.ch₁Inv x) ∈ N₀
    rw [C.ch₁_ch₁Inv (C.ne_zero x hx)]
    exact hx
  continuousOn_h := by
    have hφ : ContinuousOn (fun p ↦ C.φ (cptBase p)) {p : Cn.{u} (1 + n) | cptBase p ∈ N} :=
      C.differentiableOn_φ.continuousOn.comp differentiable_cptBase.continuous.continuousOn
        fun _ hp ↦ mem_cyl_of_mem hp
    have hb := differentiable_cptBase.{u} (n := n).continuous
    have hf := differentiable_cptFib.{u} (n := n).continuous
    change ContinuousOn (fun p ↦ cptBase p C.iw - C.φ (cptBase p) - cptBase p C.it * cptFib p) _
    fun_prop
  mem_B_of_h_eq_zero p hp hh := by
    refine ⟨hp, ?_⟩
    change C.h₁ p = 0 at hh
    change C.ch₁ (C.L₁ p) ∈ N
    have e : C.φ (C.L₁ p) + C.L₁ p C.it * C.L₁ p C.iw = cptBase p C.iw := by
      rw [φ_L₁, L₁_apply_it, L₁_apply_iw]
      rw [h₁] at hh
      linear_combination -hh
    rw [ch₁, e, L₁, Function.update_idem, Function.update_eq_self]
    exact hp

/-- **The second chart of the blow-up in the chart `1` of `P^an`.** -/
def chart₂Pkg : BlowupChartPkg C.toBlowupData where
  i := 1
  A := C.M₂
  A₀ := C.M₂₀ h₀
  le := C.M₂₀_le h₀
  B := C.B₂
  G := C.graph₂
  Φ := C.chart₂Map h₀
  cptBase_mem _ hp := hp.1
  compat _ ha := C.blowupPt_ch₂ (C.ne_zero_of_mem_M₂₀ h₀ ha).1 (C.ne_zero_of_mem_M₂₀ h₀ ha).2
  cptBase_Γ x _ := by
    change cptBase (C.Γ₂ x) = C.ch₂ x
    simp [Γ₂]
  mem_range x hx hr := by
    have hω : C.toBlowupData.θ 1 x ≠ 0 := C.toBlowupData.θ_ne_zero_of_mem_stdOpen 1
      (C.ne_zero x hx) (by rw [stdOpen_eq_chartOpens]; exact hr)
    change x C.iw - C.φ x ≠ 0 at hω
    refine ⟨⟨mem_cyl_of_mem (h₀ hx), hω⟩, ?_⟩
    change C.ch₂ (C.ch₂Inv x) ∈ N₀
    rw [C.ch₂_ch₂Inv hω]
    exact hx
  continuousOn_h := by
    have hφ : ContinuousOn (fun p ↦ C.φ (cptBase p)) {p : Cn.{u} (1 + n) | cptBase p ∈ N} :=
      C.differentiableOn_φ.continuousOn.comp differentiable_cptBase.continuous.continuousOn
        fun _ hp ↦ mem_cyl_of_mem hp
    have hb := differentiable_cptBase.{u} (n := n).continuous
    have hf := differentiable_cptFib.{u} (n := n).continuous
    change ContinuousOn (fun p ↦ cptBase p C.it - cptFib p * (cptBase p C.iw - C.φ (cptBase p))) _
    fun_prop
  mem_B_of_h_eq_zero p hp hh := by
    refine ⟨hp, ?_⟩
    change C.h₂ p = 0 at hh
    change C.ch₂ (C.L₂ p) ∈ N
    have hta : C.ta (C.L₂ p) = Function.update (cptBase p) C.iw (cptFib p) := by
      rw [← C.ta'_L₂, hh]
      simp [ta, ta']
    rw [ch₂, hta, C.φ_update, L₂_it, add_sub_cancel, Function.update_idem,
      Function.update_eq_self]
    exact hp

end BlowupCentre

/-! ### The sheaf over `N × ℙ¹` in the charts -/

variable (N) in
/-- The open `N`, as an open of `Fin n → ℂ`. -/
def baseN : Opens (Fin n → ℂ) :=
  baseOpens ⟨{x : Cn.{u} n | x ∈ N}, N.isOpen⟩

lemma mem_baseN {y : Fin n → ℂ} : y ∈ baseN N ↔ ofBase y ∈ N :=
  Iff.rfl

variable (h₀) in
/-- The restriction of `𝒢` to `N × ℙ¹`, as a sheaf on the open subspace `N × ℙ¹` of `P^an`. -/
abbrev resModule (c : BlowupData N N₀) (W : FiniteEtaleOver (space N₀)) :
    SheafOfModules.{u} ((relProjectiveSpaceAn.{u} n 1).restrict
      (tube.{u} (N := 1) (baseN N))).ringSheaf :=
  (restrictOverEquiv (relProjectiveSpaceAn.{u} n 1).toLocallyRingedSpace
    (tube.{u} (N := 1) (baseN N))).functor.obj ((c.module h₀ W).over (tube.{u} (N := 1) (baseN N)))

/-- A lift of an open immersion along an open immersion is an open immersion. -/
lemma isOpenImmersion_lift {X Y Z : LocallyRingedSpace.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    [LocallyRingedSpace.IsOpenImmersion f] [LocallyRingedSpace.IsOpenImmersion g]
    (H : Set.range g.base ⊆ Set.range f.base) :
    LocallyRingedSpace.IsOpenImmersion (LocallyRingedSpace.IsOpenImmersion.lift f g H) := by
  unfold LocallyRingedSpace.IsOpenImmersion.lift
  infer_instance

section ChartHom

variable (i : Fin 2) (B : (AnalyticSpace.complexAffineSpace.{u} (1 + n)).Opens)
  (hB : ∀ p ∈ B, cptBase p ∈ N)

lemma chartLRS_base_mem_tube {p : Cn.{u} (1 + n)} (hp : cptBase p ∈ N) :
    (chartLRS.{u} (m := n) (N := 1) i).base p ∈ tube.{u} (N := 1) (baseN N) := by
  rw [mem_tube, baseY_chart]
  exact hp

/-- The chart `i` of `P^an` on an open `B` over `N`, as a morphism into the open subspace
`N × ℙ¹`. -/
def chartHomOn :
    space B ⟶ (relProjectiveSpaceAn.{u} n 1).restrict (tube.{u} (N := 1) (baseN N)) :=
  AnalyticSpace.liftRestrict ((AnalyticSpace.complexAffineSpace.{u} (1 + n)).ofRestrict B ≫
    relProjectiveSpaceAnChart.{u} i) _ (by
      rintro _ ⟨z, rfl⟩
      exact chartLRS_base_mem_tube i (hB z.1 z.2))

lemma chartHomOn_fac : chartHomOn i B hB ≫ (relProjectiveSpaceAn.{u} n 1).ofRestrict _ =
    (AnalyticSpace.complexAffineSpace.{u} (1 + n)).ofRestrict B ≫
      relProjectiveSpaceAnChart.{u} i :=
  AnalyticSpace.liftRestrict_fac _ _ _

lemma chartHomOn_base (z : space B) :
    ((chartHomOn i B hB).toLRSHom.base z).1 = (chartLRS.{u} (m := n) (N := 1) i).base z.1 :=
  congrArg (fun φ ↦ φ.toLRSHom.base z) (chartHomOn_fac i B hB)

instance isOpenImmersion_chartHomOn :
    LocallyRingedSpace.IsOpenImmersion (chartHomOn i B hB).toLRSHom := by
  haveI : LocallyRingedSpace.IsOpenImmersion
      ((AnalyticSpace.complexAffineSpace.{u} (1 + n)).ofRestrict B).toLRSHom :=
    LocallyRingedSpace.isOpenImmersion_ofRestrict _ B
  haveI : LocallyRingedSpace.IsOpenImmersion
      ((AnalyticSpace.complexAffineSpace.{u} (1 + n)).ofRestrict B ≫
        relProjectiveSpaceAnChart.{u} i).toLRSHom :=
    LocallyRingedSpace.IsOpenImmersion.comp
      ((AnalyticSpace.complexAffineSpace.{u} (1 + n)).ofRestrict B).toLRSHom (chartLRS i)
  rw [chartHomOn, toLRSHom_liftRestrict]
  unfold LocallyRingedSpace.liftRestrict
  exact @isOpenImmersion_lift _ _ _ _ _
    (LocallyRingedSpace.isOpenImmersion_ofRestrict _ _) inferInstance _

/-- The image in `P^an` of an open of `B`. -/
abbrev imgOn (O : (space B).Opens) : (relProjectiveSpaceAn.{u} n 1).Opens :=
  (tube.{u} (N := 1) (baseN N)).isOpenEmbedding.isOpenMap.functor.obj
    (openImmersionImg (chartHomOn i B hB).toLRSHom O)

lemma mem_imgOn {O : (space B).Opens} {q : relProjectiveSpaceAn.{u} n 1} :
    q ∈ imgOn i B hB O ↔ ∃ z ∈ O, (chartLRS.{u} (m := n) (N := 1) i).base z.1 = q := by
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z, hz, (chartHomOn_base i B hB z).symm⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨(chartHomOn i B hB).toLRSHom.base z, ⟨z, hz, rfl⟩, chartHomOn_base i B hB z⟩

end ChartHom

namespace BlowupChartPkg

open BlowupData

variable {c : BlowupData N N₀} (K : BlowupChartPkg c)

/-- The chart `i` of `P^an` on `B`, as a morphism into the open subspace `N × ℙ¹`. -/
abbrev chartHom :
    space K.B ⟶ (relProjectiveSpaceAn.{u} n 1).restrict (tube.{u} (N := 1) (baseN N)) :=
  chartHomOn K.i K.B K.cptBase_mem

lemma chartHom_base (z : space K.B) :
    (K.chartHom.toLRSHom.base z).1 = (chartLRS.{u} (m := n) (N := 1) K.i).base z.1 :=
  chartHomOn_base _ _ _ z

/-- The image in `P^an` of an open of `B`. -/
abbrev Pimg (O : (space K.B).Opens) : (relProjectiveSpaceAn.{u} n 1).Opens :=
  (tube.{u} (N := 1) (baseN N)).isOpenEmbedding.isOpenMap.functor.obj
    (openImmersionImg K.chartHom.toLRSHom O)

lemma mem_Pimg {O : (space K.B).Opens} {q : relProjectiveSpaceAn.{u} n 1} :
    q ∈ K.Pimg O ↔ ∃ z ∈ O, (chartLRS.{u} (m := n) (N := 1) K.i).base z.1 = q := by
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z, hz, (K.chartHom_base z).symm⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨K.chartHom.toLRSHom.base z, ⟨z, hz, rfl⟩, K.chartHom_base z⟩

variable {W : FiniteEtaleOver (space N₀)} {W' : FiniteEtaleOver (space K.A₀)}
  {β : W'.left → W.left}

lemma mem_preim_G_iff {O : (space K.B).Opens} {w' : W'.left} :
    w' ∈ preim K.le W' ((Opens.map K.G.hom.toLRSHom.base).obj O) ↔
      ∃ hB : K.G.Γ (pt W' w') ∈ K.B, (⟨_, hB⟩ : space K.B) ∈ O := by
  rw [mem_preim_iff, mem_img_iff]
  constructor
  · rintro ⟨hA, hO⟩
    refine ⟨K.G.Γ_mem _ hA, ?_⟩
    change K.G.hom.toLRSHom.base ⟨_, hA⟩ ∈ O at hO
    have e : K.G.hom.toLRSHom.base ⟨_, hA⟩ = ⟨K.G.Γ (pt W' w'), K.G.Γ_mem _ hA⟩ :=
      Subtype.ext (K.G.hom_base _)
    rwa [e] at hO
  · rintro ⟨hB, hO⟩
    refine ⟨K.le (pt_mem W' w'), ?_⟩
    change K.G.hom.toLRSHom.base ⟨_, K.le (pt_mem W' w')⟩ ∈ O
    have e : K.G.hom.toLRSHom.base ⟨_, K.le (pt_mem W' w')⟩ = ⟨K.G.Γ (pt W' w'), hB⟩ :=
      Subtype.ext (K.G.hom_base _)
    rwa [e]

variable (hβ : IsMapPullback K.Φ W W' β)
include hβ

lemma proj_β (w' : W'.left) : (c.proj h₀ W).toLRSHom.base (β w') =
    (chartLRS.{u} (m := n) (N := 1) K.i).base (K.G.Γ (pt W' w')) := by
  rw [BlowupData.proj_base, hβ.pt_eq, K.compat _ (pt_mem W' w')]

lemma β_mem_Pimg {O : (space K.B).Opens} {w' : W'.left}
    (hw' : w' ∈ preim K.le W' ((Opens.map K.G.hom.toLRSHom.base).obj O)) :
    β w' ∈ (Opens.map (c.proj h₀ W).toLRSHom.base).obj (K.Pimg O) := by
  change (c.proj h₀ W).toLRSHom.base (β w') ∈ K.Pimg O
  rw [K.proj_β hβ, K.mem_Pimg]
  obtain ⟨hB, hO⟩ := K.mem_preim_G_iff.1 hw'
  exact ⟨_, hO, rfl⟩

lemma exists_β_of_mem {O : (space K.B).Opens} {w : W.left}
    (hw : w ∈ (Opens.map (c.proj h₀ W).toLRSHom.base).obj (K.Pimg O)) :
    ∃ w', β w' = w ∧ w' ∈ preim K.le W' ((Opens.map K.G.hom.toLRSHom.base).obj O) := by
  have hw' : (c.proj h₀ W).toLRSHom.base w ∈ K.Pimg O := hw
  obtain ⟨z, hz, hzw⟩ := K.mem_Pimg.1 hw'
  have hzw' := hzw
  rw [BlowupData.proj_base] at hzw'
  obtain ⟨hR, hA⟩ := K.mem_range _ (pt_mem W w) ⟨_, hzw'⟩
  obtain ⟨w', rfl⟩ := hβ.mem_range_iff.2 ⟨hR, hA⟩
  refine ⟨w', rfl, K.mem_preim_G_iff.2 ⟨K.G.Γ_mem _ (K.le (pt_mem W' w')), ?_⟩⟩
  have e : z.1 = K.G.Γ (pt W' w') := chart_injective _ (hzw.trans (K.proj_β hβ w'))
  have e' : (⟨K.G.Γ (pt W' w'), K.G.Γ_mem _ (K.le (pt_mem W' w'))⟩ : space K.B) = z :=
    Subtype.ext e.symm
  rw [e']
  exact hz

lemma isHolOn_comp_β {O : (space K.B).Opens} (s : (c.module h₀ W).val.obj (op (K.Pimg O))) :
    IsHolOn W' (fun w' ↦ evalFun (gVal s) (β w'))
      (preim K.le W' ((Opens.map K.G.hom.toLRSHom.base).obj O)) :=
  hβ.isHolOn_comp (isHolOn_evalFun _) fun _ hw' ↦ K.β_mem_Pimg hβ hw'

lemma isBddOn_comp_β {O : (space K.B).Opens} (s : (c.module h₀ W).val.obj (op (K.Pimg O))) :
    IsBddOn W' ((Opens.map K.G.hom.toLRSHom.base).obj O) (fun w' ↦ evalFun (gVal s) (β w')) := by
  intro x hx hxA₀
  obtain ⟨hxA, hxO⟩ := mem_img_iff.1 hx
  have hzO : K.G.hom.toLRSHom.base ⟨x, hxA⟩ ∈ O := hxO
  have hz : (K.G.hom.toLRSHom.base ⟨x, hxA⟩).1 = K.G.Γ x := K.G.hom_base _
  have hpP : (chartLRS.{u} (m := n) (N := 1) K.i).base (K.G.Γ x) ∈ K.Pimg O :=
    K.mem_Pimg.2 ⟨_, hzO, by rw [hz]⟩
  have hpD : (chartLRS.{u} (m := n) (N := 1) K.i).base (K.G.Γ x) ∈ removed N₀ := by
    change ofBase (baseY _) ∉ N₀
    rw [baseY_chart]
    change cptBase (K.G.Γ x) ∉ N₀
    rw [K.cptBase_Γ x hxA]
    exact fun h ↦ hxA₀ ((K.Φ.mem_iff x).2 h)
  obtain ⟨M, hM, C, hC⟩ := gVal_mem s _ hpP hpD
  have hcont : ContinuousAt (fun x' ↦ (chartLRS.{u} (m := n) (N := 1) K.i).base (K.G.Γ x')) x :=
    (chartLRS K.i).base.hom.continuous.continuousAt.comp
      (K.G.differentiableOn_Γ.continuousOn.continuousAt (K.A.isOpen.mem_nhds hxA))
  refine ⟨_, hcont.preimage_mem_nhds hM, C, fun w' hw'M hw'V ↦ ?_⟩
  have hw' : w' ∈ preim K.le W' ((Opens.map K.G.hom.toLRSHom.base).obj O) :=
    (mem_preim_iff _ _).2 hw'V
  have hmem := K.β_mem_Pimg (h₀ := h₀) hβ hw'
  change ‖evalFun (gVal s) (β w')‖ ≤ C
  rw [evalFun_of_mem _ hmem]
  refine hC (β w') hmem ?_
  rw [K.proj_β (h₀ := h₀) hβ]
  exact hw'M

omit hβ in
variable (W') in
/-- The pushforward along `Γ` of the bounded sections of `W'`. -/
abbrev pushModule : SheafOfModules.{u} (space K.B).ringSheaf :=
  (SheafOfModules.pushforward.{u} K.G.hom.toLRSHom.toRingSheafHom).obj (boundedModule K.le W')

/-- The section of `Γ_* 𝒜'` with values `s ∘ β`. -/
def φFun {O : (space K.B).Opens} (s : (c.module h₀ W).val.obj (op (K.Pimg O))) :
    (K.pushModule W').val.obj (op O) :=
  (exists_secVal_eq K.le W' (K.isHolOn_comp_β hβ s) (K.isBddOn_comp_β hβ s)).choose

lemma evalFun_φFun {O : (space K.B).Opens} (s : (c.module h₀ W).val.obj (op (K.Pimg O)))
    {w' : W'.left} (hw' : w' ∈ preim K.le W' ((Opens.map K.G.hom.toLRSHom.base).obj O)) :
    evalFun (secVal K.le W' (K.φFun hβ s)) w' = evalFun (gVal s) (β w') :=
  (exists_secVal_eq K.le W' (K.isHolOn_comp_β hβ s) (K.isBddOn_comp_β hβ s)).choose_spec w' hw'

/-- **The chart map on sections**: a section `s` of `𝒢` over the image of `O` goes to the section
of `Γ_* 𝒜'` over `O` with values `s ∘ β`. -/
def φ (O : (space K.B).Opens) :
    (resModule h₀ c W).val.obj (op (openImmersionImg K.chartHom.toLRSHom O)) →+
      (K.pushModule W').val.obj (op O) where
  toFun s := K.φFun hβ s
  map_zero' := secVal_ext K.le W' fun w' hw' ↦ by
    rw [K.evalFun_φFun hβ _ hw']
    have h₁ : evalFun (gVal (0 : (c.module h₀ W).val.obj (op (K.Pimg O)))) (β w') = 0 :=
      (evalFun_of_mem _ (K.β_mem_Pimg (h₀ := h₀) hβ hw')).trans (map_zero _)
    have h₂ : evalFun (secVal K.le W' (0 : (boundedModule K.le W').val.obj
        (op ((Opens.map K.G.hom.toLRSHom.base).obj O)))) w' = 0 := evalFun_secVal_zero hw'
    exact h₁.trans h₂.symm
  map_add' s t := secVal_ext K.le W' fun w' hw' ↦ by
    rw [K.evalFun_φFun hβ _ hw']
    have e₁ := evalFun_gVal_add (show (c.module h₀ W).val.obj (op (K.Pimg O)) from s) t
      (K.β_mem_Pimg (h₀ := h₀) hβ hw')
    have e₂ := evalFun_secVal_add (h₀ := K.le) (W := W') (K.φFun hβ s) (K.φFun hβ t) hw'
    rw [K.evalFun_φFun hβ _ hw', K.evalFun_φFun hβ _ hw'] at e₂
    exact e₁.trans e₂.symm
lemma φ_apply {O : (space K.B).Opens}
    (s : (resModule h₀ c W).val.obj (op (openImmersionImg K.chartHom.toLRSHom O))) :
    K.φ hβ O s = K.φFun hβ s :=
  rfl

lemma injective_φ (O : (space K.B).Opens) : Function.Injective (K.φ (h₀ := h₀) hβ O) := by
  intro s t h
  have hv : ∀ w' ∈ preim K.le W' ((Opens.map K.G.hom.toLRSHom.base).obj O),
      evalFun (gVal (show (c.module h₀ W).val.obj (op (K.Pimg O)) from s)) (β w') =
        evalFun (gVal (show (c.module h₀ W).val.obj (op (K.Pimg O)) from t)) (β w') := by
    intro w' hw'
    rw [← K.evalFun_φFun hβ s hw', ← K.evalFun_φFun hβ t hw']
    exact congrArg (fun a ↦ evalFun (secVal K.le W' a) w') h
  refine gVal_injective (h₀ := h₀) (c := c) (W := W) (O := K.Pimg O)
    (eq_of_forall_eval_eq (isLocallyOpenInAffine_left W) fun w hw ↦ ?_)
  obtain ⟨w', rfl, hw'⟩ := K.exists_β_of_mem hβ hw
  rw [← evalFun_of_mem _ hw, ← evalFun_of_mem _ hw]
  exact hv w' hw'

/-- A function on `W` over the image of `O` which is `a ∘ β⁻¹` for a section `a` of `𝒜'` is
bounded near the points over `ℂⁿ ∖ N°`. -/
lemma isBoundedNear_of_liftFun {O : (space K.B).Opens}
    (a : (boundedModule K.le W').val.obj (op ((Opens.map K.G.hom.toLRSHom.base).obj O)))
    (s₀ : W.left.presheaf.obj (op ((Opens.map (c.proj h₀ W).toLRSHom.base).obj (K.Pimg O))))
    (hs₀ : ∀ w (hw : w ∈ (Opens.map (c.proj h₀ W).toLRSHom.base).obj (K.Pimg O)),
      W.left.eval w hw s₀ = IsMapPullback.liftFun β (evalFun (secVal K.le W' a)) w) :
    IsBoundedNear (c.proj h₀ W) (removed N₀) s₀ := by
  intro p hp hpD
  obtain ⟨z, hz, rfl⟩ := K.mem_Pimg.1 hp
  have hchart := isOpenEmbedding_chart.{u} (m := n) (N := 1) K.i
  have hw_pt : ∀ w (hw : w ∈ (Opens.map (c.proj h₀ W).toLRSHom.base).obj (K.Pimg O)),
      ∃ w', β w' = w ∧ w' ∈ preim K.le W' ((Opens.map K.G.hom.toLRSHom.base).obj O) ∧
        (c.proj h₀ W).toLRSHom.base w =
          (chartLRS.{u} (m := n) (N := 1) K.i).base (K.G.Γ (pt W' w')) := by
    intro w hw
    obtain ⟨w', rfl, hw'⟩ := K.exists_β_of_mem hβ hw
    exact ⟨w', rfl, hw', K.proj_β hβ w'⟩
  by_cases hh : K.G.h z.1 = 0
  · -- `p` lies on the blow-up
    have hxA := K.G.L_mem _ z.2
    have hΓx : K.G.Γ (K.G.L z.1) = z.1 := by
      rw [← K.G.Θ_zero _ hxA, ← hh, K.G.Θ_L _ z.2]
    have hxA₀ : K.G.L z.1 ∉ K.A₀ := by
      intro h
      apply hpD
      rw [baseY_chart]
      change cptBase z.1 ∈ N₀
      rw [← hΓx, K.cptBase_Γ _ hxA]
      exact (K.Φ.mem_iff _).1 h
    have hximg : K.G.L z.1 ∈ img ((Opens.map K.G.hom.toLRSHom.base).obj O) := by
      refine mem_img_iff.2 ⟨hxA, ?_⟩
      change K.G.hom.toLRSHom.base ⟨_, hxA⟩ ∈ O
      have e : K.G.hom.toLRSHom.base ⟨_, hxA⟩ = z := Subtype.ext ((K.G.hom_base _).trans hΓx)
      rw [e]
      exact hz
    obtain ⟨M, hM, C, hC⟩ := isBddOn_secVal K.le W' a _ hximg hxA₀
    have hLc : ContinuousAt K.G.L z.1 :=
      K.G.differentiableOn_L.continuousOn.continuousAt (K.B.isOpen.mem_nhds z.2)
    have hnhds : {o : Cn.{u} (1 + n) | o ∈ K.B ∧ K.G.L o ∈ M} ∈ 𝓝 z.1 :=
      Filter.inter_mem (K.B.isOpen.mem_nhds z.2) (hLc.preimage_mem_nhds hM)
    refine ⟨_, hchart.image_mem_nhds.2 hnhds, C, fun w hw hwM ↦ ?_⟩
    obtain ⟨w', rfl, hw', hρ⟩ := hw_pt w hw
    rw [hs₀, hβ.liftFun_apply]
    obtain ⟨o, ⟨-, hoM⟩, ho⟩ := hwM
    rw [hρ] at ho
    have ho' : o = K.G.Γ (pt W' w') := hchart.injective ho
    rw [ho', K.G.L_Γ _ (K.le (pt_mem W' w'))] at hoM
    exact hC w' hoM ((mem_preim_iff _ _).1 hw')
  · -- `p` lies off the blow-up
    have hhc : ContinuousAt K.G.h z.1 :=
      K.G.differentiableOn_h.continuousOn.continuousAt (K.B.isOpen.mem_nhds z.2)
    have hnhds : {o : Cn.{u} (1 + n) | o ∈ K.B ∧ K.G.h o ≠ 0} ∈ 𝓝 z.1 :=
      Filter.inter_mem (K.B.isOpen.mem_nhds z.2) (hhc.eventually_ne hh)
    refine ⟨_, hchart.image_mem_nhds.2 hnhds, 0, fun w hw hwM ↦ ?_⟩
    obtain ⟨w', rfl, -, hρ⟩ := hw_pt w hw
    obtain ⟨o, ⟨-, hoh⟩, ho⟩ := hwM
    rw [hρ] at ho
    rw [hchart.injective ho, K.G.h_Γ _ (K.le (pt_mem W' w'))] at hoh
    exact absurd rfl hoh

lemma surjective_φ (O : (space K.B).Opens) : Function.Surjective (K.φ (h₀ := h₀) hβ O) := by
  intro a
  let a' : (boundedModule K.le W').val.obj (op ((Opens.map K.G.hom.toLRSHom.base).obj O)) := a
  have hF : IsHolOn W (IsMapPullback.liftFun β (evalFun (secVal K.le W' a')))
      ((Opens.map (c.proj h₀ W).toLRSHom.base).obj (K.Pimg O)) :=
    (hβ.isHolOn_liftFun (isHolOn_secVal K.le W' a')).mono fun w hw ↦ by
      obtain ⟨w', rfl, hw'⟩ := K.exists_β_of_mem hβ hw
      exact ⟨w', hw', rfl⟩
  obtain ⟨s₀, hs₀⟩ := hF.exists_eval_eq
  refine ⟨mkG h₀ c W s₀ (K.isBoundedNear_of_liftFun hβ a' s₀ hs₀),
    secVal_ext K.le W' fun w' hw' ↦ ?_⟩
  rw [φ_apply, K.evalFun_φFun hβ _ hw']
  change evalFun s₀ (β w') = _
  rw [evalFun_of_mem _ (K.β_mem_Pimg (h₀ := h₀) hβ hw'), hs₀, hβ.liftFun_apply]

omit hβ in
lemma Pimg_mono {O₁ O₂ : (space K.B).Opens} (h : O₁ ≤ O₂) : K.Pimg O₁ ≤ K.Pimg O₂ :=
  fun _ hq ↦ by
    obtain ⟨z, hz, rfl⟩ := K.mem_Pimg.1 hq
    exact K.mem_Pimg.2 ⟨z, h hz, rfl⟩

lemma φ_res {O₁ O₂ : (space K.B).Opens} (h : O₁ ≤ O₂)
    (s : (resModule h₀ c W).val.obj (op (openImmersionImg K.chartHom.toLRSHom O₂))) :
    K.φ hβ O₁ (sectRes (resModule h₀ c W) ((PresheafedSpace.IsOpenImmersion.base_open
      (f := K.chartHom.toLRSHom.toHom)).isOpenMap.functor.monotone h) s) =
      sectRes (K.pushModule W') h (K.φ hβ O₂ s) := by
  refine secVal_ext K.le W' fun w' hw' ↦ ?_
  have hw'₂ : w' ∈ preim K.le W' ((Opens.map K.G.hom.toLRSHom.base).obj O₂) :=
    preim_mono K.le W' ((Opens.map K.G.hom.toLRSHom.base).monotone h) hw'
  rw [φ_apply, K.evalFun_φFun hβ _ hw']
  have e₁ : evalFun (gVal (modRes (show (c.module h₀ W).val.obj (op (K.Pimg O₂)) from s)
      (K.Pimg O₁) (K.Pimg_mono h))) (β w') =
      evalFun (gVal (show (c.module h₀ W).val.obj (op (K.Pimg O₂)) from s)) (β w') :=
    evalFun_gVal_modRes (K.Pimg_mono h) _ (K.β_mem_Pimg (h₀ := h₀) hβ hw')
  have e₂ : evalFun (secVal K.le W' (LocallyRingedSpace.sectRes (boundedModule K.le W')
      ((Opens.map K.G.hom.toLRSHom.base).monotone h) (K.φ hβ O₂ s))) w' =
      evalFun (secVal K.le W' (K.φ hβ O₂ s)) w' :=
    evalFun_secVal_sectRes _ _ hw'
  rw [φ_apply, K.evalFun_φFun hβ _ hw'₂] at e₂
  exact e₁.trans e₂.symm

lemma φ_smul (O : (space K.B).Opens)
    (r : ((relProjectiveSpaceAn.{u} n 1).restrict (tube.{u} (N := 1) (baseN N))).presheaf.obj
      (op (openImmersionImg K.chartHom.toLRSHom O)))
    (s : (resModule h₀ c W).val.obj (op (openImmersionImg K.chartHom.toLRSHom O))) :
    K.φ hβ O (r • s) = openImmersionψ K.chartHom.toLRSHom O r • K.φ hβ O s := by
  refine secVal_ext K.le W' fun w' hw' ↦ ?_
  have hmem := K.β_mem_Pimg (h₀ := h₀) hβ hw'
  have hsm := restrictSectionsEquiv_smul (M := c.module h₀ W) _ r s
  have hL : evalFun (secVal K.le W' (K.φ hβ O (r • s))) w' =
      evalFun (gVal (restrictSectionsEquiv _ _ _ (r • s))) (β w') :=
    K.evalFun_φFun hβ _ hw'
  have hR : evalFun (secVal K.le W' (openImmersionψ K.chartHom.toLRSHom O r • K.φ hβ O s)) w' =
      holFun (K.G.hom.toLRSHom.c.app (op O) (openImmersionψ K.chartHom.toLRSHom O r))
        (pt W' w') * evalFun (secVal K.le W' (K.φ hβ O s)) w' :=
    evalFun_secVal_smul _ _ hw'
  have hV := (congrArg (fun x ↦ evalFun (gVal x) (β w')) hsm).trans
    (evalFun_gVal_smul _ _ hmem)
  rw [hL, hR, φ_apply, K.evalFun_φFun hβ _ hw']
  refine hV.trans ?_
  congr 1
  obtain ⟨hA, hO⟩ := mem_img_iff.1 ((mem_preim_iff _ _).1 hw')
  rw [← eval_space _ ⟨pt W' w', hA⟩ hO, eval_c_app _ K.G.hom.isCLinear _ hO,
    ProjectiveLine.eval_openImmersionψ K.chartHom O r _ hO,
    ProjectiveLine.eval_restrict_section]
  refine eval_congr_point ?_ _ _ r
  rw [K.proj_β hβ, K.chartHom_base, K.G.hom_base]

/-- **The chart of `𝒢` at a chart of the blow-up**: over `B`, the sheaf `𝒢` is `Γ_* 𝒜'`. -/
def moduleChart : ModuleChart (resModule h₀ c W) (K.pushModule W') :=
  ModuleChart.ofIsOpenImmersion K.chartHom.toLRSHom (K.φ (h₀ := h₀) hβ)
    (fun O ↦ ⟨K.injective_φ hβ O, K.surjective_φ hβ O⟩) (K.φ_res hβ) (K.φ_smul hβ)

omit hβ

/-- The part of the chart `i` of `P^an` over `N` off the blow-up. -/
def offOpen : (AnalyticSpace.complexAffineSpace.{u} (1 + n)).Opens :=
  ⟨{p | cptBase p ∈ N ∧ K.G.h p ≠ 0}, by
    change IsOpen {p : Cn.{u} (1 + n) | cptBase p ∈ N ∧ K.G.h p ≠ 0}
    exact K.continuousOn_h.isOpen_inter_preimage
      (N.isOpen.preimage differentiable_cptBase.continuous) isOpen_compl_singleton⟩

lemma cptBase_mem_of_mem_offOpen : ∀ p ∈ K.offOpen, cptBase p ∈ N :=
  fun _ hp ↦ hp.1

lemma not_mem_proj_offOpen (w : W.left) (O : (space K.offOpen).Opens) :
    w ∉ (Opens.map (c.proj h₀ W).toLRSHom.base).obj
      (imgOn K.i K.offOpen K.cptBase_mem_of_mem_offOpen O) := by
  intro hw
  have hw' : (c.proj h₀ W).toLRSHom.base w ∈ imgOn K.i K.offOpen K.cptBase_mem_of_mem_offOpen O :=
    hw
  obtain ⟨z, -, hz⟩ := (mem_imgOn _ _ _).1 hw'
  rw [BlowupData.proj_base] at hz
  obtain ⟨hR, hA⟩ := K.mem_range _ (pt_mem W w) ⟨_, hz⟩
  have hχ := K.compat _ hA
  rw [K.Φ.χ_χInv _ hR hA, ← hz] at hχ
  have hzΓ : z.1 = K.G.Γ (K.Φ.χInv (pt W w)) := chart_injective _ hχ
  exact z.2.2 (by rw [hzΓ, K.G.h_Γ _ (K.le hA)])

/-- **The charts of `𝒢` off the blow-up**: there, `𝒢` vanishes. -/
def offChart : ModuleChart (resModule h₀ c W)
    (SheafOfModules.free (R := (space K.offOpen).ringSheaf) PEmpty.{u + 1}) := by
  have hK (O : (space K.offOpen).Opens) : Subsingleton
      ((SheafOfModules.free (R := (space K.offOpen).ringSheaf) PEmpty.{u + 1}).val.obj (op O)) :=
    ModuleCat.subsingleton_of_isZero (Functor.map_isZero (SheafOfModules.evaluation _ (op O))
      (SheafOfModules.isZero_free_of_isEmpty PEmpty.{u + 1}))
  have hM (O : (space K.offOpen).Opens) : Subsingleton ((resModule h₀ c W).val.obj
      (op (openImmersionImg (chartHomOn K.i K.offOpen K.cptBase_mem_of_mem_offOpen).toLRSHom
        O))) := by
    refine ⟨fun s t ↦ gVal_injective (h₀ := h₀) (c := c) (W := W)
      (O := imgOn K.i K.offOpen K.cptBase_mem_of_mem_offOpen O)
      (eq_of_forall_eval_eq (isLocallyOpenInAffine_left W) fun w hw ↦ ?_)⟩
    exact absurd hw (K.not_mem_proj_offOpen w O)
  exact ModuleChart.ofIsOpenImmersion
    (chartHomOn K.i K.offOpen K.cptBase_mem_of_mem_offOpen).toLRSHom
    (fun _ ↦ 0) (fun O ↦ ⟨fun a b _ ↦ (hM O).elim a b, fun b ↦ ⟨0, (hK O).elim _ b⟩⟩)
    (fun _ _ ↦ (hK _).elim _ _) (fun O _ _ ↦ (hK O).elim _ _)

end BlowupChartPkg

/-! ### Coherence -/

namespace BlowupCentre

variable (C : BlowupCentre N N₀) {W : FiniteEtaleOver (space N₀)}

/-- **A chart of `𝒢` through every point of `N × ℙ¹` over the chart `i` of a package.** -/
lemma exists_moduleChart (K : BlowupChartPkg C.toBlowupData) {W' : FiniteEtaleOver (space K.A₀)}
    {β : W'.left → W.left} (hβ : IsMapPullback K.Φ W W' β)
    (hK : (boundedModule K.le W').IsCoherent)
    (y : (relProjectiveSpaceAn.{u} n 1).restrict (tube.{u} (N := 1) (baseN N)))
    (q : (Fin n → ℂ) × ℂ) (hq : chartPt.{u} K.i q = y.1) :
    ∃ (Z : LocallyRingedSpace.{u}) (K' : SheafOfModules.{u} Z.ringSheaf) (_ : K'.IsCoherent)
      (C' : ModuleChart (resModule h₀ C.toBlowupData W) K') (z : Z), C'.g z = y := by
  have hyN : cptBase (cpt.{u} q : Cn.{u} (1 + n)) ∈ N := by
    have := y.2
    change baseY y.1 ∈ baseN N at this
    rw [← hq, baseY_chartPt] at this
    change ofBase (yPart.{u} (N := 1) (cpt.{u} q)) ∈ N
    rw [yPart_cpt]
    exact mem_baseN.1 this
  by_cases hh : K.G.h (cpt.{u} q) = 0
  · have hB := K.mem_B_of_h_eq_zero _ hyN hh
    haveI := hK
    refine ⟨_, K.pushModule W', K.G.isCoherent_pushforward _, K.moduleChart (h₀ := h₀) hβ,
      ⟨cpt.{u} q, hB⟩, Subtype.ext ?_⟩
    exact (K.chartHom_base _).trans hq
  · refine ⟨_, _, isCoherent_of_isZero (SheafOfModules.isZero_free_of_isEmpty PEmpty.{u + 1}),
      K.offChart (h₀ := h₀) (W := W), ⟨cpt.{u} q, hyN, hh⟩, Subtype.ext ?_⟩
    exact (chartHomOn_base _ _ K.cptBase_mem_of_mem_offOpen _).trans hq

/-- **Coherence of the bounded sections on the blow-up.** Let `W₁`, `W₂` be the pullbacks of `W`
to the two charts of the blow-up of `N` along `{t = 0, w = φ}`. If the sheaves of bounded sections
of `W₁` and `W₂` are coherent, then `𝒢` is coherent over `N × ℙ¹`. -/
theorem isCoherent_module {W₁ : FiniteEtaleOver (space (C.M₁₀ h₀))}
    {W₂ : FiniteEtaleOver (space (C.M₂₀ h₀))} {β₁ : W₁.left → W.left} {β₂ : W₂.left → W.left}
    (hβ₁ : IsMapPullback (C.chart₁Map h₀) W W₁ β₁) (hβ₂ : IsMapPullback (C.chart₂Map h₀) W W₂ β₂)
    (h₁ : (boundedModule (C.M₁₀_le h₀) W₁).IsCoherent)
    (h₂ : (boundedModule (C.M₂₀_le h₀) W₂).IsCoherent) :
    (((relProjectiveSpaceAn.{u} n 1).toLocallyRingedSpace.restrictModules
      (tube.{u} (N := 1) (baseN N))).obj (C.toBlowupData.module h₀ W)).IsCoherent := by
  have hM : (resModule h₀ C.toBlowupData W).IsCoherent := by
    refine isCoherent_of_forall_moduleChart _ fun y ↦ ?_
    rcases exists_chartPt y.1 with ⟨q, hq⟩ | ⟨q, hq⟩
    · exact C.exists_moduleChart (C.chart₁Pkg h₀) hβ₁ h₁ y q hq
    · exact C.exists_moduleChart (C.chart₂Pkg h₀) hβ₂ h₂ y q hq
  exact @SheafOfModules.IsCoherent.of_iso.{u} _ _ _ _ _ _ _ _ _ _
    (restrictModulesObjIso _ _ _).symm hM

end BlowupCentre

end

end ComplexAnalytic.BoundedSections
