/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.ES.CurveInfinity
import Oka.Analytification.RET.ES.KummerExtensionCoherent
import Oka.AnalyticSpace.BoundedPushforward
import Oka.AnalyticSpace.LocalAtTarget
import Oka.AnalyticSpace.PullbackOpen
import Oka.Geometry.RingedSpace.LocallyRingedSpace.CoherentModuleOpenEmbedding

/-!
# The canonical extension of a finite cover of `ℂ` to `ℙ¹`

Let `ρ₀ : W ⟶ ℂ¹` be a finite morphism with Hausdorff source which is a local isomorphism over
`{‖z‖ > 1}`, and let `ρ : W ⟶ ℙ¹_an` be its composite with the chart `z ↦ [1 : z]`. The sections
of `ρ_* 𝒪_W` bounded near `∞` form a sheaf of `𝒪_{ℙ¹_an}`-modules
`ComplexAnalytic.ProjectiveLine.extension ρ₀`. It is coherent
(`ComplexAnalytic.ProjectiveLine.isCoherent_extension`) if `ρ₀_* 𝒪_W` is: away from `∞` it is
`ρ₀_* 𝒪_W` read in the chart `0`, and near `∞` it is the canonical extension of the finite étale
cover of the punctured disc `{0 < ‖w‖ < 1}` of the chart `1` given by `W` over `{‖z‖ > 1}`
(`ComplexAnalytic.KummerModel.extensionModule`), which is free.

## Main definitions

- `ComplexAnalytic.ProjectiveLine.extension ρ₀`: the sections of `ρ_* 𝒪_W` bounded near `∞`.
- `ComplexAnalytic.ProjectiveLine.coverAtInfinity ρ₀`: the finite étale cover of the punctured disc
  of the chart `1` given by `W`.
-/

open CategoryTheory Opposite TopologicalSpace Topology Filter AlgebraicGeometry

universe u

namespace ComplexAnalytic.ProjectiveLine

open AnalyticSpace projectiveSpaceAn

noncomputable section

/-- The open `{‖z‖ > 1}` of `ℂ¹`. -/
def outerOpens : (AnalyticSpace.complexAffineSpace.{u} 1).Opens :=
  ⟨{z | 1 < ‖coord z‖}, isOpen_lt continuous_const (continuous_norm.comp continuous_coord)⟩

/-- The trivial base `ℂ⁰` of the Kummer model at infinity. -/
abbrev baseSet : Set (ULift.{u} (Fin 0) → ℂ) := Set.univ

lemma isOpen_baseSet : IsOpen baseSet.{u} := isOpen_univ

lemma coord_mem_puncturedOpens_iff (w : AnalyticSpace.complexAffineSpace.{u} 1) :
    w ∈ KummerModel.puncturedOpens baseSet isOpen_baseSet ↔ coord w ≠ 0 ∧ ‖coord w‖ < 1 := by
  change KummerModel.splitEquiv 0 w ∈ Kummer.base baseSet ↔ _
  rw [Kummer.mem_base]
  simp only [Set.mem_univ, true_and]
  rfl

/-- The chart `1` restricted to the punctured disc. -/
def puncturedChart : KummerModel.punctured isOpen_baseSet.{u} ⟶ projectiveSpaceAn.{u} 1 :=
  (AnalyticSpace.complexAffineSpace.{u} 1).ofRestrict _ ≫ projectiveSpaceAnChart 1

/-- The chart `0` restricted to `{‖z‖ > 1}`. -/
def outerChart :
    (AnalyticSpace.complexAffineSpace.{u} 1).restrict outerOpens ⟶ projectiveSpaceAn.{u} 1 :=
  (AnalyticSpace.complexAffineSpace.{u} 1).ofRestrict _ ≫ projectiveSpaceAnChart 0

instance isOpenImmersion_ofRestrict (X : AnalyticSpace.{u}) (U : X.Opens) :
    LocallyRingedSpace.IsOpenImmersion (X.ofRestrict U).toLRSHom :=
  inferInstanceAs (LocallyRingedSpace.IsOpenImmersion
    (X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding))

instance : LocallyRingedSpace.IsOpenImmersion puncturedChart.{u}.toLRSHom :=
  LocallyRingedSpace.IsOpenImmersion.comp _ _

instance : LocallyRingedSpace.IsOpenImmersion outerChart.{u}.toLRSHom :=
  LocallyRingedSpace.IsOpenImmersion.comp _ _

lemma range_outerChart_eq :
    Set.range outerChart.{u}.toLRSHom.base = Set.range puncturedChart.{u}.toLRSHom.base := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    have hz : 1 < ‖coord z.1‖ := z.2
    have hz0 : coord z.1 ≠ 0 := norm_pos_iff.1 (one_pos.trans hz)
    refine ⟨⟨ofCoord (coord z.1)⁻¹, (coord_mem_puncturedOpens_iff _).2 ⟨by simpa using hz0, ?_⟩⟩,
      (chart_zero_eq_chart_one z.1 hz0).symm⟩
    rw [coord_ofCoord, norm_inv]
    exact inv_lt_one_of_one_lt₀ hz
  · rintro ⟨w, rfl⟩
    obtain ⟨hw0, hw1⟩ := (coord_mem_puncturedOpens_iff w.1).1 w.2
    refine ⟨⟨ofCoord (coord w.1)⁻¹, ?_⟩, (chart_one_eq_chart_zero w.1 hw0).symm⟩
    change 1 < ‖coord (ofCoord (coord w.1)⁻¹)‖
    rw [coord_ofCoord, norm_inv]
    exact one_lt_inv₀ (norm_pos_iff.2 hw0) |>.2 hw1

/-- The identification of `{‖z‖ > 1}` with the punctured disc, `z ↦ 1 / z`, as a morphism of
complex analytic spaces. -/
def outerToPunctured :
    (AnalyticSpace.complexAffineSpace.{u} 1).restrict outerOpens ⟶
      KummerModel.punctured isOpen_baseSet.{u} :=
  ⟨LocallyRingedSpace.IsOpenImmersion.lift puncturedChart.toLRSHom outerChart.toLRSHom
    range_outerChart_eq.le,
    IsCLinearHom.of_comp (LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ _)
      outerChart.isCLinear puncturedChart.isCLinear⟩

lemma outerToPunctured_comp : outerToPunctured.{u} ≫ puncturedChart = outerChart :=
  forgetToLocallyRingedSpace.map_injective
    (LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ range_outerChart_eq.le)

instance : IsIso outerToPunctured.{u} := by
  haveI : IsIso (forgetToLocallyRingedSpace.map outerToPunctured.{u}) :=
    (LocallyRingedSpace.IsOpenImmersion.isoOfRangeEq _ _ range_outerChart_eq).isIso_hom
  exact isIso_of_reflects_iso _ forgetToLocallyRingedSpace

/-! ### The cover at infinity -/

section Cover

variable {W : AnalyticSpace.{u}} (ρ₀ : W ⟶ AnalyticSpace.complexAffineSpace.{u} 1)

/-- The open of `W` over `{‖z‖ > 1}`. -/
abbrev outerPreimage : W.Opens := (Opens.map ρ₀.toLRSHom.base).obj outerOpens

/-- The map from the part of `W` over `{‖z‖ > 1}` to the punctured disc of the chart `1`. -/
def coverAtInfinityHom :
    W.restrict (outerPreimage ρ₀) ⟶ KummerModel.punctured isOpen_baseSet.{u} :=
  AnalyticSpace.restrictHom ρ₀ outerOpens ≫ outerToPunctured

lemma coverAtInfinityHom_comp :
    coverAtInfinityHom ρ₀ ≫ puncturedChart =
      W.ofRestrict (outerPreimage ρ₀) ≫ ρ₀ ≫ projectiveSpaceAnChart 0 := by
  rw [coverAtInfinityHom, Category.assoc, outerToPunctured_comp, outerChart,
    ← Category.assoc, AnalyticSpace.restrictHom_fac, Category.assoc]

lemma chart_one_coverAtInfinityHom (w : W.restrict (outerPreimage ρ₀)) :
    chart 1 ((coverAtInfinityHom ρ₀).toLRSHom.base w).1 =
      chart 0 (ρ₀.toLRSHom.base w.1) :=
  congrArg (fun f ↦ f.toLRSHom.base w) (coverAtInfinityHom_comp ρ₀)

variable [IsFinite ρ₀] [IsLocalIso (AnalyticSpace.restrictHom ρ₀ outerOpens)]

instance : IsFiniteEtale (coverAtInfinityHom ρ₀) where
  isFinite := haveI := isFinite_of_isIso outerToPunctured.{u}; isFinite_comp _ _
  isLocalIso := haveI := isLocalIso_of_isIso outerToPunctured.{u}; isLocalIso_comp _ _

/-- **The cover at infinity**: the part of `W` over `{‖z‖ > 1}`, as a finite étale cover of the
punctured disc `{0 < ‖w‖ < 1}` of the chart `1`. -/
def coverAtInfinity : FiniteEtaleOver (KummerModel.punctured isOpen_baseSet.{u}) :=
  MorphismProperty.Over.mk ⊤ (coverAtInfinityHom ρ₀) (inferInstance : IsFiniteEtale _)

@[simp]
lemma coverAtInfinity_hom : (coverAtInfinity ρ₀).hom = coverAtInfinityHom ρ₀ :=
  rfl

variable [T2Space W]

instance : T2Space (coverAtInfinity ρ₀).left :=
  inferInstanceAs (T2Space (outerPreimage ρ₀))

lemma exists_iso_sigma_coverAtInfinity :
    ∃ (ι : Type u) (_ : Finite ι) (k : ι → ℕ+),
      Nonempty (coverAtInfinity ρ₀ ≅ FiniteEtaleOver.sigma fun i ↦
        KummerModel.cover isOpen_baseSet.{u} (k i)) :=
  KummerModel.exists_iso_sigma_cover isOpen_baseSet convex_univ (coverAtInfinity ρ₀)

lemma isLocallyOpenInAffine_coverAtInfinity :
    IsLocallyOpenInAffine (coverAtInfinity ρ₀).left := by
  obtain ⟨ι, hι, k, ⟨e⟩⟩ := exists_iso_sigma_coverAtInfinity ρ₀
  exact KummerModel.isLocallyOpenInAffine_left e

/-- The canonical extension of the cover at infinity across `w = 0`. -/
def extensionAtInfinity : SheafOfModules.{u}
    (KummerModel.disc isOpen_baseSet.{u}).toLocallyRingedSpace.ringSheaf :=
  KummerModel.extensionModule (isLocallyOpenInAffine_coverAtInfinity ρ₀)

lemma isCoherent_extensionAtInfinity : (extensionAtInfinity ρ₀).IsCoherent := by
  obtain ⟨ι, hι, k, ⟨e⟩⟩ := exists_iso_sigma_coverAtInfinity ρ₀
  exact KummerModel.isCoherent_extensionModule e _

end Cover

/-! ### The extension and its chart at `0` -/

section Extension

open LocallyRingedSpace

variable {W : AnalyticSpace.{u}} (ρ₀ : W ⟶ AnalyticSpace.complexAffineSpace.{u} 1)

/-- The composite `W ⟶ ℂ¹ ⟶ ℙ¹_an` with the chart `0`. -/
abbrev toProjectiveLine : W ⟶ projectiveSpaceAn.{u} 1 := ρ₀ ≫ projectiveSpaceAnChart 0

/-- **The canonical extension** of `ρ₀_* 𝒪_W` to `ℙ¹_an`: the sections of `ρ_* 𝒪_W` bounded
near `∞`, for `ρ : W ⟶ ℙ¹_an` the composite of `ρ₀` with the chart `0`. -/
def extension : SheafOfModules.{u} (projectiveSpaceAn.{u} 1).toLocallyRingedSpace.ringSheaf :=
  boundedPushforward (toProjectiveLine ρ₀) {infty}

lemma preimage_openImmersionImg_chartZero
    (O : Opens (AnalyticSpace.complexAffineSpace.{u} 1).toPresheafedSpace) :
    (Opens.map (toProjectiveLine ρ₀).toLRSHom.base).obj
      (openImmersionImg (projectiveSpaceAnChart.{u} 0).toLRSHom O) =
      (Opens.map ρ₀.toLRSHom.base).obj O := by
  ext w
  refine ⟨fun ⟨z, hz, h⟩ ↦ ?_, fun h ↦ ⟨_, h, rfl⟩⟩
  have := chart_injective 0 h
  subst this
  exact hz

/-- The sections of the extension over the image of `O` under the chart `0` are the sections of
`ρ₀_* 𝒪_W` over `O`. -/
def chartZeroφ (O : Opens (AnalyticSpace.complexAffineSpace.{u} 1).toPresheafedSpace) :
    (extension ρ₀).val.obj (op (openImmersionImg (projectiveSpaceAnChart.{u} 0).toLRSHom O)) →+
      (Hom.pushUnit ρ₀.toLRSHom).val.obj (op O) :=
  (W.presheaf.map (homOfLE (preimage_openImmersionImg_chartZero ρ₀ O).ge).op).hom.toAddMonoidHom
    |>.comp
    ((boundedSubmodule (toProjectiveLine ρ₀) {infty}).obj _).subtype.toAddMonoidHom

lemma presheaf_map_map_of_le {X : AnalyticSpace.{u}} {A B : X.Opens} (h₁ : B ≤ A) (h₂ : A ≤ B)
    (t : X.presheaf.obj (op A)) :
    X.presheaf.map (homOfLE h₂).op (X.presheaf.map (homOfLE h₁).op t) = t := by
  rw [← ConcreteCategory.comp_apply, ← X.presheaf.map_comp, ← op_comp,
    Subsingleton.elim (homOfLE h₂ ≫ homOfLE h₁) (𝟙 A), op_id, X.presheaf.map_id]
  rfl

lemma bijective_chartZeroφ (O : Opens (AnalyticSpace.complexAffineSpace.{u} 1).toPresheafedSpace) :
    Function.Bijective (chartZeroφ ρ₀ O) := by
  refine ⟨fun s t h ↦ Subtype.ext ?_, fun t ↦ ?_⟩
  · have h' : W.presheaf.map (homOfLE (preimage_openImmersionImg_chartZero ρ₀ O).ge).op s.1 =
        W.presheaf.map (homOfLE (preimage_openImmersionImg_chartZero ρ₀ O).ge).op t.1 := h
    have := congrArg (W.presheaf.map (homOfLE (preimage_openImmersionImg_chartZero ρ₀ O).le).op) h'
    rwa [presheaf_map_map_of_le, presheaf_map_map_of_le] at this
  · refine ⟨⟨W.presheaf.map (homOfLE (preimage_openImmersionImg_chartZero ρ₀ O).le).op t,
      isBoundedNear_of_disjoint (Set.disjoint_singleton_right.2 ?_) _⟩, ?_⟩
    · rintro ⟨z, -, hz⟩
      exact chart_zero_ne_infty z hz
    · exact presheaf_map_map_of_le _ _ t

lemma chartZeroφ_res {O₁ O₂ : Opens (AnalyticSpace.complexAffineSpace.{u} 1).toPresheafedSpace}
    (h : O₁ ≤ O₂)
    (s : (extension ρ₀).val.obj
      (op (openImmersionImg (projectiveSpaceAnChart.{u} 0).toLRSHom O₂))) :
    chartZeroφ ρ₀ O₁ (sectRes (extension ρ₀) ((PresheafedSpace.IsOpenImmersion.base_open
      (f := (projectiveSpaceAnChart.{u} 0).toLRSHom.toHom)).isOpenMap.functor.monotone h) s) =
      sectRes (Hom.pushUnit ρ₀.toLRSHom) h (chartZeroφ ρ₀ O₂ s) := by
  change W.presheaf.map _ (W.presheaf.map _ s.1) = W.presheaf.map _ (W.presheaf.map _ s.1)
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← W.presheaf.map_comp,
    ← W.presheaf.map_comp]
  rfl

lemma chartZeroφ_smul (O : Opens (AnalyticSpace.complexAffineSpace.{u} 1).toPresheafedSpace)
    (r : (projectiveSpaceAn.{u} 1).presheaf.obj
      (op (openImmersionImg (projectiveSpaceAnChart.{u} 0).toLRSHom O)))
    (s : (extension ρ₀).val.obj (op (openImmersionImg (projectiveSpaceAnChart.{u} 0).toLRSHom O))) :
    chartZeroφ ρ₀ O (r • s) =
      openImmersionψ (projectiveSpaceAnChart.{u} 0).toLRSHom O r • chartZeroφ ρ₀ O s := by
  have hBA := (preimage_openImmersionImg_chartZero ρ₀ O).ge
  change W.presheaf.map (homOfLE hBA).op ((show W.presheaf.obj (op ((Opens.map
      (toProjectiveLine ρ₀).toLRSHom.base).obj (openImmersionImg _ O))) from
      (toProjectiveLine ρ₀).toLRSHom.c.app (op _) r) *
      (show W.presheaf.obj (op ((Opens.map (toProjectiveLine ρ₀).toLRSHom.base).obj
        (openImmersionImg _ O))) from s.1)) =
    (show W.presheaf.obj (op ((Opens.map ρ₀.toLRSHom.base).obj O)) from
      ρ₀.toLRSHom.c.app (op O) (openImmersionψ _ O r)) * W.presheaf.map (homOfLE hBA).op s.1
  rw [map_mul]
  congr 1
  change _ = ρ₀.toLRSHom.c.app (op O) (LocallyRingedSpace.res _
    (le_preimage_openImmersionImg (projectiveSpaceAnChart.{u} 0).toLRSHom O)
    ((projectiveSpaceAnChart.{u} 0).toLRSHom.c.app _ r))
  rw [c_app_res]
  rfl

/-- **The chart `0` of the extension**: over the image of the chart `0` the extension is
`ρ₀_* 𝒪_W`. -/
def chartZeroModuleChart :
    ModuleChart (extension ρ₀) (Hom.pushUnit ρ₀.toLRSHom) :=
  ModuleChart.ofIsOpenImmersion (projectiveSpaceAnChart.{u} 0).toLRSHom (chartZeroφ ρ₀)
    (bijective_chartZeroφ ρ₀) (chartZeroφ_res ρ₀) (chartZeroφ_smul ρ₀)

end Extension

/-! ### The chart at infinity and coherence -/

section Infinity

open LocallyRingedSpace

lemma eval_restrict_presheaf_map (X : AnalyticSpace.{u}) (U : X.Opens) {V : X.Opens}
    {O' : (X.restrict U).Opens} (h : U.isOpenEmbedding.isOpenMap.functor.obj O' ≤ V)
    (σ : X.presheaf.obj (op V)) (x : X.restrict U) (hx : x ∈ O') :
    (X.restrict U).eval x hx (X.presheaf.map (homOfLE h).op σ) = X.eval x.1 (h ⟨x, hx, rfl⟩) σ := by
  have hO' : O' ≤ (Opens.map (X.ofRestrict U).toLRSHom.base).obj V := fun y hy ↦ h ⟨y, hy, rfl⟩
  have : X.presheaf.map (homOfLE h).op σ = (X.restrict U).presheaf.map (homOfLE hO').op
      ((X.ofRestrict U).toLRSHom.c.app (op V) σ) := by
    change _ = X.presheaf.map _ (X.presheaf.map _ σ)
    rw [← ConcreteCategory.comp_apply, ← X.presheaf.map_comp]
    rfl
  rw [this, eval_presheaf_map, eval_c_app _ (X.ofRestrict U).isCLinear]
  rfl

lemma eval_restrict_section (X : AnalyticSpace.{u}) (U : X.Opens) {O' : (X.restrict U).Opens}
    (σ : (X.restrict U).presheaf.obj (op O')) (x : X.restrict U) (hx : x ∈ O') :
    (X.restrict U).eval x hx σ =
      X.eval x.1 (show x.1 ∈ U.isOpenEmbedding.isOpenMap.functor.obj O' from ⟨x, hx, rfl⟩) σ := by
  have := eval_restrict_presheaf_map X U (le_refl _) σ x hx
  have h1 : X.presheaf.map (homOfLE (le_refl (U.isOpenEmbedding.isOpenMap.functor.obj O'))).op σ =
      σ := by
    exact ConcreteCategory.congr_hom (X.presheaf.map_id _) σ
  rwa [h1] at this

/-- The value of `openImmersionψ g O r` at `z` is the value of `r` at `g z`. -/
lemma eval_openImmersionψ {Z Y : AnalyticSpace.{u}} (g : Z ⟶ Y)
    [LocallyRingedSpace.IsOpenImmersion g.toLRSHom] (O : Opens Z.toPresheafedSpace)
    (r : Y.presheaf.obj (op (openImmersionImg g.toLRSHom O))) (z : Z) (hz : z ∈ O) :
    Z.eval z hz (openImmersionψ g.toLRSHom O r) =
      Y.eval (g.toLRSHom.base z) (show g.toLRSHom.base z ∈ openImmersionImg g.toLRSHom O from
        ⟨z, hz, rfl⟩) r := by
  rw [openImmersionψ, RingHom.comp_apply]
  erw [eval_presheaf_map]
  exact eval_c_app _ g.isCLinear z _ r

/-- The chart `1` restricted to the unit disc. -/
def discChart : KummerModel.disc isOpen_baseSet.{u} ⟶ projectiveSpaceAn.{u} 1 :=
  (AnalyticSpace.complexAffineSpace.{u} 1).ofRestrict _ ≫ projectiveSpaceAnChart 1

instance : LocallyRingedSpace.IsOpenImmersion discChart.{u}.toLRSHom :=
  LocallyRingedSpace.IsOpenImmersion.comp _ _

lemma discChart_base (x : KummerModel.disc isOpen_baseSet.{u}) :
    discChart.toLRSHom.base x = chart 1 x.1 :=
  rfl

variable {W : AnalyticSpace.{u}} (ρ₀ : W ⟶ AnalyticSpace.complexAffineSpace.{u} 1)

lemma mem_outerPreimage_of_mem {w : W} {x : KummerModel.disc isOpen_baseSet.{u}}
    (h : chart 0 (ρ₀.toLRSHom.base w) = chart 1 x.1) : w ∈ outerPreimage ρ₀ := by
  have hx0 : coord x.1 ≠ 0 := fun h0 ↦
    chart_zero_ne_infty _ (h.trans ((chart_one_eq_infty_iff x.1).2 h0))
  rw [chart_one_eq_chart_zero x.1 hx0] at h
  have hx1 : ‖coord x.1‖ < 1 := by
    have := (KummerModel.mem_disc_of_mem_coeOpens (hB := isOpen_baseSet.{u}) ⊤
      ⟨x, trivial, rfl⟩).2
    exact this
  change 1 < ‖coord (ρ₀.toLRSHom.base w)‖
  rw [chart_injective 0 h, coord_ofCoord, norm_inv]
  exact one_lt_inv₀ (norm_pos_iff.2 hx0) |>.2 hx1

variable [IsFinite ρ₀] [IsLocalIso (AnalyticSpace.restrictHom ρ₀ outerOpens)]

lemma mem_preim_coverAtInfinity_iff (O : (KummerModel.disc isOpen_baseSet.{u}).Opens)
    (w : (coverAtInfinity ρ₀).left) :
    w ∈ KummerModel.preim (coverAtInfinity ρ₀) O ↔
      (toProjectiveLine ρ₀).toLRSHom.base w.1 ∈ openImmersionImg discChart.toLRSHom O := by
  rw [KummerModel.mem_preim_iff]
  have e := chart_one_coverAtInfinityHom ρ₀ w
  constructor
  · rintro ⟨y, hy, hyw⟩
    refine ⟨y, hy, ?_⟩
    rw [discChart_base, hyw]
    exact e
  · rintro ⟨y, hy, hyw⟩
    exact ⟨y, hy, chart_injective 1 (hyw.trans e.symm)⟩

lemma image_preim_coverAtInfinity (O : (KummerModel.disc isOpen_baseSet.{u}).Opens) :
    (outerPreimage ρ₀).isOpenEmbedding.isOpenMap.functor.obj
      (KummerModel.preim (coverAtInfinity ρ₀) O) =
      (Opens.map (toProjectiveLine ρ₀).toLRSHom.base).obj
        (openImmersionImg discChart.toLRSHom O) := by
  ext w
  constructor
  · rintro ⟨w', hw', rfl⟩
    exact (mem_preim_coverAtInfinity_iff ρ₀ O w').1 hw'
  · intro hw
    obtain ⟨x, -, hx⟩ := id hw
    have hw' : w ∈ outerPreimage ρ₀ := mem_outerPreimage_of_mem ρ₀ hx.symm
    exact ⟨⟨w, hw'⟩, (mem_preim_coverAtInfinity_iff ρ₀ O ⟨w, hw'⟩).2 hw, rfl⟩


lemma chart_one_eq_infty_of_zero {x : AnalyticSpace.complexAffineSpace.{u} 1}
    (hx : x KummerModel.zero = 0) : chart 1 x = infty :=
  (chart_one_eq_infty_iff x).2 hx

lemma isBoundedNearZero_restrict (O : (KummerModel.disc isOpen_baseSet.{u}).Opens)
    {s : W.presheaf.obj (op ((Opens.map (toProjectiveLine ρ₀).toLRSHom.base).obj
      (openImmersionImg discChart.toLRSHom O)))}
    (hs : IsBoundedNear (toProjectiveLine ρ₀) {infty} s) :
    KummerModel.IsBoundedNearZero isOpen_baseSet (coverAtInfinity ρ₀)
      (KummerModel.isOpen_coeOpens O)
      (W.presheaf.map (homOfLE (image_preim_coverAtInfinity ρ₀ O).le).op s) := by
  intro x hx hx0
  have hxinf := chart_one_eq_infty_of_zero hx0
  obtain ⟨y, hyO, rfl⟩ := hx
  have hinf : infty ∈ openImmersionImg discChart.{u}.toLRSHom O := ⟨y, hyO, hxinf⟩
  obtain ⟨N₀, hN₀, C, hC⟩ := hs infty hinf rfl
  have hN₀' : N₀ ∈ 𝓝 (chart 1 y.1) := hxinf.symm ▸ hN₀
  refine ⟨chart 1 ⁻¹' N₀, (isOpenEmbedding_chart 1).continuous.continuousAt.preimage_mem_nhds
    hN₀', C, fun w hw hwN ↦ ?_⟩
  refine (congrArg norm (eval_restrict_presheaf_map W (outerPreimage ρ₀)
    (image_preim_coverAtInfinity ρ₀ O).le s w hw)).le.trans (hC w.1 _ ?_)
  have e : (toProjectiveLine ρ₀).toLRSHom.base w.1 =
      chart 1 ((coverAtInfinityHom ρ₀).toLRSHom.base w).1 :=
    (chart_one_coverAtInfinityHom ρ₀ w).symm
  rw [e]
  exact hwN

lemma isBoundedNear_restrict (O : (KummerModel.disc isOpen_baseSet.{u}).Opens)
    {t : (coverAtInfinity ρ₀).left.presheaf.obj (op (KummerModel.preim (coverAtInfinity ρ₀) O))}
    (ht : KummerModel.IsBoundedNearZero isOpen_baseSet (coverAtInfinity ρ₀)
      (KummerModel.isOpen_coeOpens O) t) :
    IsBoundedNear (toProjectiveLine ρ₀) {infty}
      (W.presheaf.map (homOfLE (image_preim_coverAtInfinity ρ₀ O).ge).op t) := by
  rintro _ ⟨x, hxO, hx⟩ rfl
  have hx0 : x.1 KummerModel.zero = 0 := (chart_one_eq_infty_iff x.1).1 hx
  obtain ⟨N, hN, M, hM⟩ := ht x.1 ⟨x, hxO, rfl⟩ hx0
  have hN' : chart 1 '' N ∈ 𝓝 infty := by
    have := (isOpenEmbedding_chart 1).isOpenMap.image_mem_nhds hN
    rwa [show (projectiveSpaceAnChart.{u} 1).toLRSHom.base x.1 = infty from hx] at this
  refine ⟨chart 1 '' N, hN', M, fun w hw hwN ↦ ?_⟩
  obtain ⟨n, hnN, hn⟩ := hwN
  obtain ⟨x', -, hx'⟩ := id hw
  have hw' : w ∈ outerPreimage ρ₀ := mem_outerPreimage_of_mem ρ₀ hx'.symm
  have hwp : (⟨w, hw'⟩ : (coverAtInfinity ρ₀).left) ∈ KummerModel.preim (coverAtInfinity ρ₀) O :=
    (mem_preim_coverAtInfinity_iff ρ₀ O ⟨w, hw'⟩).2 hw
  rw [eval_presheaf_map]
  have e := eval_restrict_section W (outerPreimage ρ₀) t ⟨w, hw'⟩ hwp
  refine (congrArg norm e).symm.le.trans (hM _ hwp ?_)
  have := chart_one_coverAtInfinityHom ρ₀ ⟨w, hw'⟩
  rw [show chart 0 (ρ₀.toLRSHom.base w) = chart 1 n from hn.symm] at this
  have hn' : (((coverAtInfinity ρ₀).hom.toLRSHom.base ⟨w, hw'⟩ :
      KummerModel.punctured isOpen_baseSet.{u}).1 : ULift.{u} (Fin 1) → ℂ) = n :=
    chart_injective 1 this
  exact (congrArg (· ∈ N) hn').mpr hnN

variable [T2Space W]

/-- The sections of the extension over the image of `O` under the chart `1` are the bounded
sections of the cover at infinity over `O`. -/
def infinityφ (O : (KummerModel.disc isOpen_baseSet.{u}).Opens) :
    (extension ρ₀).val.obj (op (openImmersionImg discChart.toLRSHom O)) →+
      (extensionAtInfinity ρ₀).val.obj (op O) where
  toFun s := (⟨W.presheaf.map (homOfLE (image_preim_coverAtInfinity ρ₀ O).le).op s.1,
    isBoundedNearZero_restrict ρ₀ O s.2⟩ : KummerModel.boundedSubring (coverAtInfinity ρ₀) O)
  map_zero' := Subtype.ext (map_zero (W.presheaf.map _).hom)
  map_add' s t := Subtype.ext (map_add (W.presheaf.map _).hom s.1 t.1)

lemma infinityφ_val (O : (KummerModel.disc isOpen_baseSet.{u}).Opens)
    (s : (extension ρ₀).val.obj (op (openImmersionImg discChart.toLRSHom O))) :
    (show KummerModel.boundedSubring (coverAtInfinity ρ₀) O from infinityφ ρ₀ O s).1 =
      W.presheaf.map (homOfLE (image_preim_coverAtInfinity ρ₀ O).le).op s.1 :=
  rfl

lemma bijective_infinityφ (O : (KummerModel.disc isOpen_baseSet.{u}).Opens) :
    Function.Bijective (infinityφ ρ₀ O) := by
  refine ⟨fun s t h ↦ Subtype.ext ?_, fun t ↦ ?_⟩
  · have h' := congrArg (fun x : KummerModel.boundedSubring (coverAtInfinity ρ₀) O ↦
      W.presheaf.map (homOfLE (image_preim_coverAtInfinity ρ₀ O).ge).op x.1) h
    simp only [infinityφ_val, presheaf_map_map_of_le] at h'
    exact h'
  · let t' : KummerModel.boundedSubring (coverAtInfinity ρ₀) O := t
    refine ⟨⟨W.presheaf.map (homOfLE (image_preim_coverAtInfinity ρ₀ O).ge).op t'.1,
      isBoundedNear_restrict ρ₀ O t'.2⟩, Subtype.ext ?_⟩
    exact presheaf_map_map_of_le (X := W) (image_preim_coverAtInfinity ρ₀ O).ge
      (image_preim_coverAtInfinity ρ₀ O).le t'.1

lemma infinityφ_res {O₁ O₂ : (KummerModel.disc isOpen_baseSet.{u}).Opens} (h : O₁ ≤ O₂)
    (s : (extension ρ₀).val.obj (op (openImmersionImg discChart.toLRSHom O₂))) :
    infinityφ ρ₀ O₁ (sectRes (extension ρ₀) ((PresheafedSpace.IsOpenImmersion.base_open
      (f := discChart.toLRSHom.toHom)).isOpenMap.functor.monotone h) s) =
      sectRes (extensionAtInfinity ρ₀) h (infinityφ ρ₀ O₂ s) := by
  apply Subtype.ext
  change W.presheaf.map _ (W.presheaf.map _ s.1) = W.presheaf.map _ (W.presheaf.map _ s.1)
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← W.presheaf.map_comp,
    ← W.presheaf.map_comp]
  rfl

omit [T2Space W] in
lemma eval_coverAtInfinity (O : (KummerModel.disc isOpen_baseSet.{u}).Opens) {V : W.Opens}
    (h : (outerPreimage ρ₀).isOpenEmbedding.isOpenMap.functor.obj
      (KummerModel.preim (coverAtInfinity ρ₀) O) ≤ V) (σ : W.presheaf.obj (op V))
    (w : (coverAtInfinity ρ₀).left) (hw : w ∈ KummerModel.preim (coverAtInfinity ρ₀) O) :
    (coverAtInfinity ρ₀).left.eval w hw (W.presheaf.map (homOfLE h).op σ) =
      W.eval w.1 (h ⟨w, hw, rfl⟩) σ :=
  eval_restrict_presheaf_map W (outerPreimage ρ₀) h σ w hw

lemma infinityφ_smul (O : (KummerModel.disc isOpen_baseSet.{u}).Opens)
    (r : (projectiveSpaceAn.{u} 1).presheaf.obj (op (openImmersionImg discChart.toLRSHom O)))
    (s : (extension ρ₀).val.obj (op (openImmersionImg discChart.toLRSHom O))) :
    infinityφ ρ₀ O (r • s) = openImmersionψ discChart.toLRSHom O r • infinityφ ρ₀ O s := by
  apply Subtype.ext
  refine eq_of_forall_eval_eq (isLocallyOpenInAffine_coverAtInfinity ρ₀) fun w hw ↦ ?_
  change (coverAtInfinity ρ₀).left.eval w hw (W.presheaf.map _
    ((show W.presheaf.obj (op ((Opens.map (toProjectiveLine ρ₀).toLRSHom.base).obj
      (openImmersionImg discChart.toLRSHom O))) from
      (toProjectiveLine ρ₀).toLRSHom.c.app (op _) r) *
      (show W.presheaf.obj (op ((Opens.map (toProjectiveLine ρ₀).toLRSHom.base).obj
        (openImmersionImg discChart.toLRSHom O))) from s.1))) =
    (coverAtInfinity ρ₀).left.eval w hw (KummerModel.pullbackHom (coverAtInfinity ρ₀) O
      (openImmersionψ discChart.toLRSHom O r) *
      (show (coverAtInfinity ρ₀).left.presheaf.obj (op (KummerModel.preim _ O)) from
        W.presheaf.map (homOfLE (image_preim_coverAtInfinity ρ₀ O).le).op s.1))
  dsimp only
  rw [map_mul, map_mul]
  refine (map_mul ((coverAtInfinity ρ₀).left.eval w hw) _ _).trans ?_
  congr 1
  · refine (eval_coverAtInfinity ρ₀ O _ _ w hw).trans ?_
    rw [KummerModel.eval_pullbackHom, eval_c_app _ (toProjectiveLine ρ₀).isCLinear w.1
      ((mem_preim_coverAtInfinity_iff ρ₀ O w).1 hw)]
    obtain ⟨y, hyO, hy⟩ := (KummerModel.mem_preim_iff _ O w).1 hw
    rw [← hy, ← KummerModel.eval_disc _ y hyO, eval_openImmersionψ discChart O r y hyO]
    have hpt : discChart.toLRSHom.base y = (toProjectiveLine ρ₀).toLRSHom.base w.1 := by
      rw [discChart_base, hy]
      exact chart_one_coverAtInfinityHom ρ₀ w
    have key : ∀ (p q : projectiveSpaceAn.{u} 1) (hp : p ∈ openImmersionImg discChart.toLRSHom O)
        (hq : q ∈ openImmersionImg discChart.toLRSHom O), p = q →
        (projectiveSpaceAn.{u} 1).eval p hp r = (projectiveSpaceAn.{u} 1).eval q hq r := by
      rintro p _ hp hq rfl
      rfl
    exact key _ _ _ _ hpt.symm

/-- **The chart at infinity of the extension**: over the image of the disc of the chart `1` the
extension is the canonical extension of the cover at infinity. -/
def infinityModuleChart : ModuleChart (extension ρ₀) (extensionAtInfinity ρ₀) :=
  ModuleChart.ofIsOpenImmersion discChart.toLRSHom (infinityφ ρ₀) (bijective_infinityφ ρ₀)
    (infinityφ_res ρ₀) (infinityφ_smul ρ₀)

/-- **The canonical extension is coherent**, if `ρ₀_* 𝒪_W` is. -/
theorem isCoherent_extension (hK : (Hom.pushUnit ρ₀.toLRSHom).IsCoherent) :
    (extension ρ₀).IsCoherent := by
  refine isCoherent_of_forall_moduleChart _ fun y ↦ ?_
  by_cases hy : y = infty
  · subst hy
    have h0 : ofCoord.{u} 0 ∈ KummerModel.discOpens baseSet isOpen_baseSet := by
      change KummerModel.splitEquiv 0 _ ∈ baseSet ×ˢ Metric.ball 0 1
      exact ⟨trivial, show (0 : ℂ) ∈ Metric.ball 0 1 by simp⟩
    exact ⟨_, _, isCoherent_extensionAtInfinity ρ₀, infinityModuleChart ρ₀, ⟨ofCoord 0, h0⟩, rfl⟩
  · obtain ⟨z, rfl⟩ := (mem_range_chart_zero_iff y).2 hy
    exact ⟨_, _, hK, chartZeroModuleChart ρ₀, z, rfl⟩

end Infinity

end

end ComplexAnalytic.ProjectiveLine
