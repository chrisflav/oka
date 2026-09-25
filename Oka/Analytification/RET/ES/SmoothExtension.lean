/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.ES.SmoothInfinity
import Oka.Analytification.RET.ES.SmoothRiemann
import Oka.Analytification.RET.ES.GrauertRemmert

/-!
# The canonical extension of a finite cover of `ℂⁿ` to `ℙⁿ`

Let `ρ₀ : W ⟶ ℂⁿ` be a finite morphism and `ρ : W ⟶ ℙⁿ_an` its composite with the chart
`z ↦ [1 : z]`. The sections of `ρ_* 𝒪_W` bounded near the hyperplane at infinity `H_∞` form a
sheaf of `𝒪_{ℙⁿ_an}`-modules `ComplexAnalytic.ProjectiveCompletion.extension ρ₀`.

Suppose that `ρ₀` is a local isomorphism over `{e ≠ 0}` for a nonzero polynomial `e`, that `W` is
Hausdorff and locally isomorphic to opens of affine spaces, and that the zero set of `e ∘ ρ₀` has
empty interior in `W`. In the chart `i` of `ℙⁿ_an`, `H_∞ ∪ {e = 0}` is the zero set of the
polynomial `chartFun e i`, and `W` restricts to a finite étale cover of its complement
(`ComplexAnalytic.ProjectiveCompletion.cover`). By the Riemann extension theorem on `W`, the
extension is, in the chart `i`, the sheaf of bounded sections of this cover
(`ComplexAnalytic.ProjectiveCompletion.chartModuleChart`). Hence the extension is coherent as soon
as the sheaves of bounded sections of finite étale covers of complements of thin sets in `ℂⁿ` are
(`ComplexAnalytic.BoundedCoherent n`, `ComplexAnalytic.ProjectiveCompletion.isCoherent_extension`).

## Main definitions

- `ComplexAnalytic.BoundedCoherent n`: the sheaves of bounded sections of Hausdorff finite étale
  covers of complements of thin sets in opens of `ℂⁿ` are coherent.
- `ComplexAnalytic.ProjectiveCompletion.extension ρ₀`: the sections of `ρ_* 𝒪_W` bounded near
  `H_∞`.
-/

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry Topology Filter

universe u

namespace ComplexAnalytic

open AnalyticSpace BoundedSections

/-- **Coherence of bounded sections in dimension `n`**: for opens `N° ⊆ N` of `ℂⁿ` such that
`N ∖ N°` is thin, the sheaf of bounded sections of every Hausdorff finite étale cover of `N°` is a
coherent sheaf of `𝒪_N`-modules. -/
def BoundedCoherent (n : ℕ) : Prop :=
  ∀ (N N₀ : (AnalyticSpace.complexAffineSpace.{u} n).Opens) (h₀ : N₀ ≤ N)
    (W : FiniteEtaleOver (space N₀)) [T2Space W.left], HasThinComplement N N₀ →
      (boundedModule h₀ W).IsCoherent

/-- Bounded sections are coherent in dimension `n`, assuming the extension statement across sets
of codimension two in dimension `n - 1` if `n ≥ 3`. -/
theorem boundedCoherent_of_capExtension {n : ℕ}
    (hext : ∀ m, n = m + 1 → 2 ≤ m → CapExtension.{u} m) : BoundedCoherent.{u} n :=
  fun _ _ h₀ W _ hD ↦ isCoherent_boundedModule_of_capExtension h₀ W hext hD

/-- Bounded sections are coherent in dimension at most two. -/
theorem boundedCoherent_of_le_two {n : ℕ} (hn : n ≤ 2) : BoundedCoherent.{u} n :=
  fun _ _ h₀ W _ hD ↦ isCoherent_boundedModule_of_le_two h₀ W hn hD

namespace ProjectiveCompletion

open projectiveSpaceAn LocallyRingedSpace

noncomputable section

variable {n : ℕ}

instance isLocalIso_projectiveSpaceAnChart (i : Fin (n + 1)) :
    IsLocalIso (projectiveSpaceAnChart.{u} i) := by
  haveI := isLocalIso_of_isIso (analytificationAffineSpaceIso.{u} n).inv
  haveI := isLocalIso_analytification_map_of_etale (projectiveSpaceChart.{u} i)
  exact isLocalIso_comp _ _

/-! ### Charts restricted to opens -/

section ChartOn

variable (N : (AnalyticSpace.complexAffineSpace.{u} n).Opens) (i : Fin (n + 1))

/-- The chart `i` restricted to an open `N` of `ℂⁿ`. -/
def chartOn : space N ⟶ projectiveSpaceAn.{u} n :=
  (AnalyticSpace.complexAffineSpace.{u} n).ofRestrict N ≫ projectiveSpaceAnChart i

instance : LocallyRingedSpace.IsOpenImmersion (chartOn N i).toLRSHom :=
  LocallyRingedSpace.IsOpenImmersion.comp _ _

lemma chartOn_base (y : space N) : (chartOn N i).toLRSHom.base y = chart i y.1 :=
  rfl

/-- The image of `N` under the chart `i`. -/
def chartImage : (projectiveSpaceAn.{u} n).Opens :=
  ⟨chart i '' (N : Set (AnalyticSpace.complexAffineSpace.{u} n)),
    (isOpenEmbedding_chart i).isOpenMap _ N.isOpen⟩

lemma range_ofRestrict_chartImage :
    Set.range ((projectiveSpaceAn.{u} n).ofRestrict (chartImage N i)).toLRSHom.base ⊆
      Set.range (chartOn N i).toLRSHom.base := by
  rintro _ ⟨⟨_, ⟨v, hv, rfl⟩⟩, rfl⟩
  exact ⟨⟨v, hv⟩, rfl⟩

/-- The inverse of the chart `i` on its image of `N`. -/
def chartInv : (projectiveSpaceAn.{u} n).restrict (chartImage N i) ⟶ space N :=
  ⟨LocallyRingedSpace.IsOpenImmersion.lift (chartOn N i).toLRSHom
    ((projectiveSpaceAn.{u} n).ofRestrict (chartImage N i)).toLRSHom
    (range_ofRestrict_chartImage N i),
    IsCLinearHom.of_comp
      (LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ (range_ofRestrict_chartImage N i))
      ((projectiveSpaceAn.{u} n).ofRestrict (chartImage N i)).isCLinear (chartOn N i).isCLinear⟩

lemma chartInv_comp :
    chartInv N i ≫ chartOn N i = (projectiveSpaceAn.{u} n).ofRestrict (chartImage N i) :=
  forgetToLocallyRingedSpace.map_injective
    (LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ (range_ofRestrict_chartImage N i))

lemma chart_chartInv (x : (projectiveSpaceAn.{u} n).restrict (chartImage N i)) :
    chart i ((chartInv N i).toLRSHom.base x).1 = x.1 :=
  congrArg (fun f ↦ f.toLRSHom.base x) (chartInv_comp N i)

instance : IsIso (chartInv N i) := by
  have hr : Set.range ((projectiveSpaceAn.{u} n).ofRestrict (chartImage N i)).toLRSHom.base =
      Set.range (chartOn N i).toLRSHom.base := by
    refine (range_ofRestrict_chartImage N i).antisymm ?_
    rintro _ ⟨y, rfl⟩
    exact ⟨⟨_, ⟨y.1, y.2, rfl⟩⟩, rfl⟩
  haveI : IsIso (forgetToLocallyRingedSpace.map (chartInv N i)) :=
    (LocallyRingedSpace.IsOpenImmersion.isoOfRangeEq _ _ hr).isIso_hom
  exact isIso_of_reflects_iso _ forgetToLocallyRingedSpace

end ChartOn

/-! ### The extension -/

variable {W : AnalyticSpace.{u}} (ρ₀ : W ⟶ AnalyticSpace.complexAffineSpace.{u} n)

/-- The composite `W ⟶ ℂⁿ ⟶ ℙⁿ_an` with the chart `0`. -/
abbrev toProj : W ⟶ projectiveSpaceAn.{u} n := ρ₀ ≫ projectiveSpaceAnChart 0

lemma toProj_base (w : W) : (toProj ρ₀).toLRSHom.base w = chart 0 (ρ₀.toLRSHom.base w) :=
  rfl

/-- **The canonical extension** of `ρ₀_* 𝒪_W` to `ℙⁿ_an`: the sections of `ρ_* 𝒪_W` bounded near
the hyperplane at infinity. -/
def extension : SheafOfModules.{u} (projectiveSpaceAn.{u} n).toLocallyRingedSpace.ringSheaf :=
  boundedPushforward (toProj ρ₀) infinity

/-! ### The cover in the chart `i` -/

section Cover

variable (e : MvPolynomial (Fin n) ℂ) (i : Fin (n + 1))

/-- The open `ρ⁻¹(chart i (N°))` of `W`, `N° = chartOpens e i`. -/
abbrev coverOpens : W.Opens :=
  (Opens.map (toProj ρ₀).toLRSHom.base).obj (chartImage (chartOpens e i) i)

/-- The part of `W` over the complement of `H_∞ ∪ {e = 0}` in the chart `i`, mapped to that
complement. -/
def coverHom : W.restrict (coverOpens ρ₀ e i) ⟶ space (chartOpens e i) :=
  AnalyticSpace.restrictHom (toProj ρ₀) (chartImage (chartOpens e i) i) ≫
    chartInv (chartOpens e i) i

lemma chart_coverHom (w : W.restrict (coverOpens ρ₀ e i)) :
    chart i ((coverHom ρ₀ e i).toLRSHom.base w).1 = chart 0 (ρ₀.toLRSHom.base w.1) := by
  change chart i ((chartInv (chartOpens e i) i).toLRSHom.base
    ((AnalyticSpace.restrictHom (toProj ρ₀) _).toLRSHom.base w)).1 = _
  rw [chart_chartInv]
  exact ComplexAnalytic.base_restrictHom (toProj ρ₀).toLRSHom _ w

lemma mem_polyOpens_of_mem_coverOpens {w : W} (hw : w ∈ coverOpens ρ₀ e i) :
    ρ₀.toLRSHom.base w ∈ polyOpens e := by
  obtain ⟨v, hv, hvw⟩ := hw
  obtain ⟨-, hτ⟩ := eq_transition_of_chart_eq i hvw
  have : polyEval e (ρ₀.toLRSHom.base w) = polyEval e (transition i v) := congrArg _ hτ
  rw [mem_polyOpens_iff, this]
  exact ((mem_chartOpens_iff e i v).1 hv).2

variable [hloc : IsLocalIso (AnalyticSpace.restrictHom ρ₀ (polyOpens e))]

include hloc in
lemma isLocalIso_restrictHom_toProj :
    IsLocalIso (AnalyticSpace.restrictHom (toProj ρ₀) (chartImage (chartOpens e i) i)) := by
  haveI : IsLocalIso (W.ofRestrict ((Opens.map ρ₀.toLRSHom.base).obj (polyOpens e)) ≫
      toProj ρ₀) := by
    rw [← Category.assoc, ← AnalyticSpace.restrictHom_fac, Category.assoc]
    infer_instance
  refine isLocalIso_restrictHom_of_subset_range
    (W.ofRestrict ((Opens.map ρ₀.toLRSHom.base).obj (polyOpens e))) _ _ fun w hw ↦ ?_
  exact ⟨⟨w, mem_polyOpens_of_mem_coverOpens ρ₀ e i hw⟩, rfl⟩

omit hloc in
lemma isFinite_restrictHom_toProj [IsFinite ρ₀] :
    IsFinite (AnalyticSpace.restrictHom (toProj ρ₀) (chartImage (chartOpens e i) i)) := by
  rw [AnalyticSpace.restrictHom_comp]
  haveI : IsFinite (AnalyticSpace.restrictHom (projectiveSpaceAnChart.{u} (n := n) 0)
      (chartImage (chartOpens e i) i)) := by
    refine isFinite_restrictHom_of_subset_range (isOpenEmbedding_chart 0).isEmbedding ?_
    rintro _ ⟨v, hv, rfl⟩
    exact (chart_mem_range_zero_iff i v).2 ((mem_chartOpens_iff e i v).1 hv).1
  exact @isFinite_comp _ _ _ _ _ (AnalyticSpace.isFinite_restrictHom ρ₀ _) this

variable [IsFinite ρ₀]

instance : IsFiniteEtale (coverHom ρ₀ e i) where
  isFinite := by
    haveI := isFinite_restrictHom_toProj ρ₀ e i
    haveI := isFinite_of_isIso (chartInv (chartOpens e i) i)
    exact isFinite_comp _ _
  isLocalIso := by
    haveI := isLocalIso_restrictHom_toProj ρ₀ e i
    haveI := isLocalIso_of_isIso (chartInv (chartOpens e i) i)
    exact isLocalIso_comp _ _

/-- **The cover in the chart `i`**: the part of `W` over the complement `N°` of `H_∞ ∪ {e = 0}` in
the chart `i`, as a finite étale cover of `N°`. -/
def cover : FiniteEtaleOver (space (chartOpens e i)) :=
  MorphismProperty.Over.mk ⊤ (coverHom ρ₀ e i) (inferInstance : IsFiniteEtale _)

instance [T2Space W] : T2Space (cover ρ₀ e i).left :=
  inferInstanceAs (T2Space (coverOpens ρ₀ e i))

lemma pt_cover (w : (cover ρ₀ e i).left) :
    chart i (pt (cover ρ₀ e i) w) = chart 0 (ρ₀.toLRSHom.base w.1) :=
  chart_coverHom ρ₀ e i w

end Cover

/-! ### Sections near points of the chart `0` -/

/-- A continuous function on an open containing the fibre of a closed map with finite fibres is
bounded on the preimage of a neighbourhood of the point. -/
lemma _root_.IsClosedMap.exists_bound_near_fiber {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} (hf : IsClosedMap f) {y : Y} (hfin : (f ⁻¹' {y}).Finite)
    {A : Set X} (hA : IsOpen A) (hyA : f ⁻¹' {y} ⊆ A) {s : X → ℂ} (hs : ContinuousOn s A) :
    ∃ N ∈ 𝓝 y, ∃ C : ℝ, ∀ x ∈ A, f x ∈ N → ‖s x‖ ≤ C := by
  obtain ⟨C₀, hC₀⟩ := (hfin.image fun x ↦ ‖s x‖).bddAbove
  let Q : Opens X := ⟨A ∩ (fun x ↦ ‖s x‖) ⁻¹' Set.Iio (C₀ + 1),
    hs.norm.isOpen_inter_preimage hA isOpen_Iio⟩
  obtain ⟨V, hyV, hV⟩ := hf.exists_preimage_le Q fun x hx ↦
    ⟨hyA hx, show ‖s x‖ < C₀ + 1 from (hC₀ ⟨x, hx, rfl⟩).trans_lt (lt_add_one _)⟩
  exact ⟨V, V.isOpen.mem_nhds hyV, C₀ + 1, fun x _ hx ↦ (hV hx).2.le⟩

variable [IsFinite ρ₀]

/-- **Sections are bounded near points of the chart `0`**: `ρ₀` is finite. -/
lemma exists_bound_near_chart_zero {A : W.Opens} (s : W.presheaf.obj (op A))
    (z : AnalyticSpace.complexAffineSpace.{u} n) (hz : ρ₀.toLRSHom.base ⁻¹' {z} ⊆ A) :
    ∃ N ∈ 𝓝 (chart 0 z), ∃ C : ℝ, ∀ w (hw : w ∈ A),
      chart 0 (ρ₀.toLRSHom.base w) ∈ N → ‖W.eval w hw s‖ ≤ C := by
  haveI := IsFinite.finite_fiber (f := ρ₀) z
  obtain ⟨N, hN, C, hC⟩ := (IsFinite.isClosedMap (f := ρ₀)).exists_bound_near_fiber
    (Set.toFinite _) A.isOpen hz (continuousOn_evalFun s)
  refine ⟨chart 0 '' N, (isOpenEmbedding_chart 0).isOpenMap.image_mem_nhds hN, C,
    fun w hw hwN ↦ ?_⟩
  obtain ⟨z', hz', h⟩ := hwN
  rw [← evalFun_of_mem s hw]
  exact hC w hw (chart_injective 0 h ▸ hz')

/-! ### The extension in the chart `i` -/

section Chart

variable (e : MvPolynomial (Fin n) ℂ) (i : Fin (n + 1))

/-- The global function `e ∘ ρ₀` on `W`. -/
def polyPullback : W.presheaf.obj (op ⊤) :=
  ρ₀.pullbackΓ (polyFun n (uliftPolyN n e))

omit [IsFinite ρ₀] in
lemma eval_polyPullback (w : W) :
    W.eval (U := ⊤) w trivial (polyPullback ρ₀ e) = polyEval e (ρ₀.toLRSHom.base w) := by
  rw [polyPullback, ← affineEval_uliftPolyN, ← eval_polyFun]
  exact eval_c_app _ ρ₀.isCLinear (U := ⊤) w trivial _

/-- The open `ρ⁻¹(chart i (O))` of `W`. -/
abbrev extOpens (O : (space (⊤ : (AnalyticSpace.complexAffineSpace.{u} n).Opens)).Opens) :
    W.Opens :=
  (Opens.map (toProj ρ₀).toLRSHom.base).obj (openImmersionImg (chartOn ⊤ i).toLRSHom O)

variable [IsLocalIso (AnalyticSpace.restrictHom ρ₀ (polyOpens e))]

/-- The open of `W` below `O` in the cover of the chart `i`. -/
abbrev coverImg (O : (space (⊤ : (AnalyticSpace.complexAffineSpace.{u} n).Opens)).Opens) :
    W.Opens :=
  (coverOpens ρ₀ e i).isOpenEmbedding.isOpenMap.functor.obj
    (preim le_top (cover ρ₀ e i) O)

lemma mem_coverImg_iff (O : (space (⊤ : (AnalyticSpace.complexAffineSpace.{u} n).Opens)).Opens)
    (w : W) :
    w ∈ coverImg ρ₀ e i O ↔ w ∈ extOpens ρ₀ i O ∧ polyEval e (ρ₀.toLRSHom.base w) ≠ 0 := by
  constructor
  · rintro ⟨w', hw', rfl⟩
    obtain ⟨hx, hmem⟩ := mem_img_iff.1 ((mem_preim_iff le_top (cover ρ₀ e i)).1 hw')
    refine ⟨⟨_, hmem, (pt_cover ρ₀ e i w').trans rfl⟩, ?_⟩
    exact mem_polyOpens_of_mem_coverOpens ρ₀ e i w'.2
  · rintro ⟨⟨y, hyO, hy⟩, hpe⟩
    have hy' : chart i y.1 = chart 0 (ρ₀.toLRSHom.base w) := hy
    obtain ⟨h0, hτ⟩ := eq_transition_of_chart_eq i hy'
    have hN₀ : y.1 ∈ chartOpens e i := (mem_chartOpens_iff e i y.1).2 ⟨h0, hτ ▸ hpe⟩
    have hw : w ∈ coverOpens ρ₀ e i := ⟨y.1, hN₀, hy'⟩
    refine ⟨⟨w, hw⟩, (mem_preim_iff le_top (cover ρ₀ e i)).2 (mem_img_iff.2 ⟨trivial, ?_⟩), rfl⟩
    have : pt (cover ρ₀ e i) ⟨w, hw⟩ = y.1 :=
      chart_injective i ((pt_cover ρ₀ e i ⟨w, hw⟩).trans hy'.symm)
    have hyy : (⟨pt (cover ρ₀ e i) ⟨w, hw⟩, trivial⟩ :
        space (⊤ : (AnalyticSpace.complexAffineSpace.{u} n).Opens)) = y := Subtype.ext this
    change (⟨pt (cover ρ₀ e i) ⟨w, hw⟩, trivial⟩ :
        space (⊤ : (AnalyticSpace.complexAffineSpace.{u} n).Opens)) ∈ O
    rw [hyy]
    exact hyO

lemma coverImg_le (O : (space (⊤ : (AnalyticSpace.complexAffineSpace.{u} n).Opens)).Opens) :
    coverImg ρ₀ e i O ≤ extOpens ρ₀ i O :=
  fun w hw ↦ ((mem_coverImg_iff ρ₀ e i O w).1 hw).1

lemma chartOn_proj (w : (cover ρ₀ e i).left) :
    (chartOn ⊤ i).toLRSHom.base ((proj le_top (cover ρ₀ e i)).toLRSHom.base w) =
      (toProj ρ₀).toLRSHom.base w.1 := by
  rw [chartOn_base, coe_proj_base]
  exact pt_cover ρ₀ e i w

/-- A bound for a section of `ρ_* 𝒪_W` near a point of the chart `i`, which lies in the chart
`0` or at which the section is bounded. -/
lemma exists_bound_near_chart
    {O : (space (⊤ : (AnalyticSpace.complexAffineSpace.{u} n).Opens)).Opens}
    (s : W.presheaf.obj (op (extOpens ρ₀ i O))) (y : space ⊤) (hy : y ∈ O)
    (hs : chart i y.1 ∈ infinity → ∃ N ∈ 𝓝 (chart i y.1), ∃ C : ℝ,
      ∀ w (hw : w ∈ extOpens ρ₀ i O), (toProj ρ₀).toLRSHom.base w ∈ N → ‖W.eval w hw s‖ ≤ C) :
    ∃ N ∈ 𝓝 (chart i y.1), ∃ C : ℝ,
      ∀ w (hw : w ∈ extOpens ρ₀ i O), (toProj ρ₀).toLRSHom.base w ∈ N → ‖W.eval w hw s‖ ≤ C := by
  by_cases hinf : chart i y.1 ∈ infinity
  · exact hs hinf
  · obtain ⟨z, hz⟩ : chart i y.1 ∈ Set.range (chart 0) := not_not.1 hinf
    rw [← hz]
    exact exists_bound_near_chart_zero ρ₀ s z fun w hw ↦ ⟨y, hy, hz.symm.trans
      (congrArg (chart 0) hw.symm)⟩

/-- The restriction of a section of the extension to the cover of the chart `i`. -/
abbrev chartVal {O : (space (⊤ : (AnalyticSpace.complexAffineSpace.{u} n).Opens)).Opens}
    (s : (extension ρ₀).val.obj (op (openImmersionImg (chartOn ⊤ i).toLRSHom O))) :
    (cover ρ₀ e i).left.presheaf.obj (op (preim le_top (cover ρ₀ e i) O)) :=
  W.presheaf.map (homOfLE (coverImg_le ρ₀ e i O)).op s.1

lemma isBoundedNear_chartφ
    {O : (space (⊤ : (AnalyticSpace.complexAffineSpace.{u} n).Opens)).Opens}
    (s : (extension ρ₀).val.obj (op (openImmersionImg (chartOn ⊤ i).toLRSHom O))) :
    IsBoundedNear (proj le_top (cover ρ₀ e i)) (removedSet ⊤ (chartOpens e i))
      (chartVal ρ₀ e i s) := by
  intro y hy _
  obtain ⟨N, hN, C, hC⟩ := exists_bound_near_chart ρ₀ i s.1 y hy fun hinf ↦
    s.2 _ ⟨y, hy, rfl⟩ hinf
  refine ⟨(chartOn ⊤ i).toLRSHom.base ⁻¹' N,
    (chartOn ⊤ i).toLRSHom.base.hom.continuous.continuousAt.preimage_mem_nhds hN, C,
    fun w hw hwN ↦ ?_⟩
  refine (congrArg norm (ProjectiveLine.eval_restrict_presheaf_map W (coverOpens ρ₀ e i)
    (coverImg_le ρ₀ e i O) s.1 w hw)).le.trans ?_
  exact hC _ _ ((chartOn_proj ρ₀ e i w).symm ▸ hwN)

/-- The sections of the extension over the image of `O` under the chart `i` are the bounded
sections of the cover of the chart `i` over `O`. -/
def chartφ (O : (space (⊤ : (AnalyticSpace.complexAffineSpace.{u} n).Opens)).Opens) :
    (extension ρ₀).val.obj (op (openImmersionImg (chartOn ⊤ i).toLRSHom O)) →+
      (boundedModule le_top (cover ρ₀ e i)).val.obj (op O) where
  toFun s := mkSec le_top (cover ρ₀ e i) (chartVal ρ₀ e i s) (isBoundedNear_chartφ ρ₀ e i s)
  map_zero' := Subtype.ext (map_zero (W.presheaf.map _).hom)
  map_add' s t := Subtype.ext (map_add (W.presheaf.map _).hom s.1 t.1)

lemma secVal_chartφ (O : (space (⊤ : (AnalyticSpace.complexAffineSpace.{u} n).Opens)).Opens)
    (s : (extension ρ₀).val.obj (op (openImmersionImg (chartOn ⊤ i).toLRSHom O))) :
    secVal le_top (cover ρ₀ e i) (chartφ ρ₀ e i O s) = chartVal ρ₀ e i s :=
  rfl

variable (hW : IsLocallyOpenInAffine W)
  (hZ : interior {w | polyEval e (ρ₀.toLRSHom.base w) = 0} = ∅)

omit [IsFinite ρ₀] [IsLocalIso (AnalyticSpace.restrictHom ρ₀ (polyOpens e))] in
include hZ in
lemma interior_polyPullback_eq_zero :
    interior {w | W.eval (U := ⊤) w trivial (polyPullback ρ₀ e) = 0} = ∅ := by
  simp_rw [eval_polyPullback]
  exact hZ

/-- A bounded section of the cover of the chart `i` is bounded near points of `H_∞ ∪ {e = 0}`,
read on `W`. -/
lemma exists_bound_secVal {O : (space (⊤ : (AnalyticSpace.complexAffineSpace.{u} n).Opens)).Opens}
    (t : (boundedModule le_top (cover ρ₀ e i)).val.obj (op O)) {y : space ⊤} (hyO : y ∈ O)
    (hy : y.1 ∉ chartOpens e i) :
    ∃ M : Set (space (⊤ : (AnalyticSpace.complexAffineSpace.{u} n).Opens)), IsOpen M ∧ y ∈ M ∧
      ∃ C : ℝ, ∀ w (hw : w ∈ coverImg ρ₀ e i O),
        (toProj ρ₀).toLRSHom.base w ∈ (chartOn ⊤ i).toLRSHom.base '' M →
          ‖W.eval w hw (secVal le_top (cover ρ₀ e i) t)‖ ≤ C := by
  obtain ⟨M, hM, C, hC⟩ := secVal_mem le_top (cover ρ₀ e i) t y hyO hy
  obtain ⟨M', hM'M, hM'o, hyM'⟩ := mem_nhds_iff.1 hM
  refine ⟨M', hM'o, hyM', C, fun w hw hwM ↦ ?_⟩
  obtain ⟨w', hw', rfl⟩ := id hw
  obtain ⟨y', hy', hyw'⟩ := hwM
  have hproj : (proj le_top (cover ρ₀ e i)).toLRSHom.base w' = y' :=
    (PresheafedSpace.IsOpenImmersion.base_open (f := (chartOn ⊤ i).toLRSHom.toHom)).injective
      ((chartOn_proj ρ₀ e i w').trans hyw'.symm)
  calc ‖W.eval w'.1 hw (secVal le_top (cover ρ₀ e i) t)‖
      = ‖(cover ρ₀ e i).left.eval w' hw' (secVal le_top (cover ρ₀ e i) t)‖ :=
        congrArg norm (ProjectiveLine.eval_restrict_section W (coverOpens ρ₀ e i) _ w' hw').symm
    _ ≤ C := hC w' hw' (hM'M (hproj ▸ hy'))

omit [IsFinite ρ₀] [IsLocalIso (AnalyticSpace.restrictHom ρ₀ (polyOpens e))] in
lemma isOpen_preimage_chartOn_image
    (M : Set (space (⊤ : (AnalyticSpace.complexAffineSpace.{u} n).Opens))) (hM : IsOpen M) :
    IsOpen ((toProj ρ₀).toLRSHom.base ⁻¹' ((chartOn ⊤ i).toLRSHom.base '' M)) :=
  ((PresheafedSpace.IsOpenImmersion.base_open
    (f := (chartOn ⊤ i).toLRSHom.toHom)).isOpenMap _ hM).preimage
    (toProj ρ₀).toLRSHom.base.hom.continuous

include hW hZ in
lemma bijective_chartφ (O : (space (⊤ : (AnalyticSpace.complexAffineSpace.{u} n).Opens)).Opens) :
    Function.Bijective (chartφ ρ₀ e i O) := by
  have hZ' := interior_polyPullback_eq_zero ρ₀ e hZ
  have hO'O : ∀ w ∈ extOpens ρ₀ i O, W.eval (U := ⊤) w trivial (polyPullback ρ₀ e) ≠ 0 →
      w ∈ coverImg ρ₀ e i O := fun w hw hw0 ↦
    (mem_coverImg_iff ρ₀ e i O w).2 ⟨hw, by rwa [eval_polyPullback] at hw0⟩
  refine ⟨fun s t hst ↦ Subtype.ext ?_, fun t ↦ ?_⟩
  · refine eq_of_eval_eq_off hW _ hZ' fun w hw hw0 ↦ ?_
    have h := congrArg (fun a ↦ W.eval w (hO'O w hw hw0)
      (secVal le_top (cover ρ₀ e i) a)) hst
    simp only [secVal_chartφ, eval_presheaf_map] at h
    exact h
  -- extend `t` across the zero set of `e ∘ ρ₀`
  let σ : W.presheaf.obj (op (coverImg ρ₀ e i O)) := secVal le_top (cover ρ₀ e i) t
  have hb : ∀ w ∈ extOpens ρ₀ i O, ∃ M ∈ 𝓝 w, ∃ C : ℝ, ∀ w' (hw' : w' ∈ coverImg ρ₀ e i O),
      w' ∈ M → ‖W.eval w' hw' σ‖ ≤ C := by
    rintro w ⟨y, hyO, hyw⟩
    by_cases hy : y.1 ∈ chartOpens e i
    · have hw : w ∈ coverImg ρ₀ e i O := hO'O w ⟨y, hyO, hyw⟩ (by
        rw [eval_polyPullback]
        obtain ⟨-, hτ⟩ := eq_transition_of_chart_eq i hyw
        rw [show polyEval e (ρ₀.toLRSHom.base w) = polyEval e (transition i y.1) from
          congrArg _ hτ]
        exact ((mem_chartOpens_iff e i y.1).1 hy).2)
      have hc := ((continuousOn_evalFun σ).continuousAt
        ((coverImg ρ₀ e i O).isOpen.mem_nhds hw)).norm
      refine ⟨_, hc.preimage_mem_nhds (Iio_mem_nhds (lt_add_one _)), ‖evalFun σ w‖ + 1,
        fun w' hw' hw'M ↦ ?_⟩
      rw [← evalFun_of_mem σ hw']
      exact le_of_lt hw'M
    · obtain ⟨M, hMo, hyM, C, hC⟩ := exists_bound_secVal ρ₀ e i t hyO hy
      exact ⟨_, (isOpen_preimage_chartOn_image ρ₀ i M hMo).mem_nhds ⟨y, hyM, hyw⟩, C,
        fun w' hw' hw'M ↦ hC w' hw' hw'M⟩
  obtain ⟨s₀, hs₀⟩ := exists_extension_of_isBounded hW _ hZ' (coverImg_le ρ₀ e i O) hO'O σ hb
  have hval : ∀ w (hw : w ∈ coverImg ρ₀ e i O),
      W.eval w (coverImg_le ρ₀ e i O hw) s₀ = W.eval w hw σ := fun w hw ↦ by
    rw [← hs₀, eval_presheaf_map]
  have hs₀b : IsBoundedNear (toProj ρ₀) infinity s₀ := by
    rintro _ ⟨y, hyO, rfl⟩ hinf
    have hy : y.1 ∉ chartOpens e i := fun h ↦
      ((mem_chartOpens_iff e i y.1).1 h).1 ((chart_mem_infinity_iff i y.1).1 hinf)
    obtain ⟨M, hMo, hyM, C, hC⟩ := exists_bound_secVal ρ₀ e i t hyO hy
    refine ⟨_, (PresheafedSpace.IsOpenImmersion.base_open
      (f := (chartOn ⊤ i).toLRSHom.toHom)).isOpenMap.image_mem_nhds (hMo.mem_nhds hyM), C,
      fun w hw hwM ↦ ?_⟩
    refine norm_eval_le_of_le_off _ hZ' s₀ (isOpen_preimage_chartOn_image ρ₀ i M hMo)
      (fun w' hw' hw'M hw'0 ↦ ?_) w hw hwM
    rw [hval w' (hO'O w' hw' hw'0)]
    exact hC w' _ hw'M
  refine ⟨⟨s₀, hs₀b⟩, secVal_injective le_top (cover ρ₀ e i) ?_⟩
  rw [secVal_chartφ]
  exact hs₀

lemma chartφ_res {O₁ O₂ : (space (⊤ : (AnalyticSpace.complexAffineSpace.{u} n).Opens)).Opens}
    (h : O₁ ≤ O₂)
    (s : (extension ρ₀).val.obj (op (openImmersionImg (chartOn ⊤ i).toLRSHom O₂))) :
    chartφ ρ₀ e i O₁ (sectRes (extension ρ₀) ((PresheafedSpace.IsOpenImmersion.base_open
      (f := (chartOn ⊤ i).toLRSHom.toHom)).isOpenMap.functor.monotone h) s) =
      sectRes (boundedModule le_top (cover ρ₀ e i)) h (chartφ ρ₀ e i O₂ s) := by
  apply Subtype.ext
  change W.presheaf.map _ (W.presheaf.map _ s.1) = W.presheaf.map _ (W.presheaf.map _ s.1)
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← W.presheaf.map_comp,
    ← W.presheaf.map_comp]
  rfl

omit [IsFinite ρ₀] [IsLocalIso (AnalyticSpace.restrictHom ρ₀ (polyOpens e))] in
lemma eval_congr_point {X : AnalyticSpace.{u}} {O : X.Opens} {p q : X} (h : p = q) (hp : p ∈ O)
    (hq : q ∈ O) (s : X.presheaf.obj (op O)) : X.eval p hp s = X.eval q hq s := by
  subst h
  rfl

lemma chartφ_smul (O : (space (⊤ : (AnalyticSpace.complexAffineSpace.{u} n).Opens)).Opens)
    (r : (projectiveSpaceAn.{u} n).presheaf.obj
      (op (openImmersionImg (chartOn ⊤ i).toLRSHom O)))
    (s : (extension ρ₀).val.obj (op (openImmersionImg (chartOn ⊤ i).toLRSHom O))) :
    chartφ ρ₀ e i O (r • s) =
      openImmersionψ (chartOn ⊤ i).toLRSHom O r • chartφ ρ₀ e i O s := by
  refine secVal_injective le_top (cover ρ₀ e i) ?_
  refine eq_of_forall_eval_eq (isLocallyOpenInAffine_left (cover ρ₀ e i)) fun w hw ↦ ?_
  rw [secVal_smul, map_mul, secVal_chartφ, secVal_chartφ, eval_pullback]
  have hw' : w.1 ∈ extOpens ρ₀ i O := coverImg_le ρ₀ e i O ⟨w, hw, rfl⟩
  have e1 : (cover ρ₀ e i).left.eval w hw (chartVal ρ₀ e i (r • s)) =
      W.eval w.1 hw' ((r • s).1) :=
    ProjectiveLine.eval_restrict_presheaf_map W (coverOpens ρ₀ e i) (coverImg_le ρ₀ e i O) _ w hw
  have e2 : (cover ρ₀ e i).left.eval w hw (chartVal ρ₀ e i s) = W.eval w.1 hw' s.1 :=
    ProjectiveLine.eval_restrict_presheaf_map W (coverOpens ρ₀ e i) (coverImg_le ρ₀ e i O) _ w hw
  rw [e1, e2]
  change W.eval w.1 hw' ((show W.presheaf.obj (op (extOpens ρ₀ i O)) from
    (toProj ρ₀).toLRSHom.c.app (op _) r) *
      (show W.presheaf.obj (op (extOpens ρ₀ i O)) from s.1)) = _
  rw [map_mul, eval_c_app _ (toProj ρ₀).isCLinear w.1 hw']
  congr 1
  have hpt : pt (cover ρ₀ e i) w ∈ img O :=
    (mem_preim_iff le_top (cover ρ₀ e i)).1 hw
  obtain ⟨hx, hmem⟩ := mem_img_iff.1 hpt
  rw [← eval_space _ _ hmem, ProjectiveLine.eval_openImmersionψ (chartOn ⊤ i) O r _ hmem]
  exact eval_congr_point (pt_cover ρ₀ e i w).symm _ _ r

include hW hZ in
/-- **The extension in the chart `i`**: over the image of the chart `i` the extension is the sheaf
of bounded sections of the cover of the chart `i`. -/
def chartModuleChart :
    ModuleChart (extension ρ₀) (boundedModule le_top (cover ρ₀ e i)) :=
  ModuleChart.ofIsOpenImmersion (chartOn ⊤ i).toLRSHom (chartφ ρ₀ e i)
    (bijective_chartφ ρ₀ e i hW hZ) (chartφ_res ρ₀ e i) (chartφ_smul ρ₀ e i)

end Chart

omit [IsFinite ρ₀] in
/-- The complement of `H_∞ ∪ {e = 0}` in the chart `i` has thin complement. -/
theorem hasThinComplement_chartOpens {e : MvPolynomial (Fin n) ℂ} (he : e ≠ 0) (i : Fin (n + 1)) :
    HasThinComplement ⊤ (chartOpens.{u} e i) := by
  refine ⟨chartFun e i, (differentiable_chartFun e i).differentiableOn, ?_,
    fun x _ hx ↦ not_not.1 hx⟩
  exact Set.eq_empty_of_subset_empty ((interior_mono fun v hv ↦ hv.2).trans
    (interior_chartFun_eq_zero e he i).le)

/-- **The canonical extension is coherent.** Let `ρ₀ : W ⟶ ℂⁿ` be finite with Hausdorff source
locally isomorphic to opens of affine spaces, a local isomorphism over `{e ≠ 0}` for a nonzero
polynomial `e`, such that the zero set of `e ∘ ρ₀` has empty interior. If bounded sections are
coherent in dimension `n`, then the sections of `ρ_* 𝒪_W` bounded near `H_∞` form a coherent sheaf
on `ℙⁿ_an`. -/
theorem isCoherent_extension (hB : BoundedCoherent.{u} n) [T2Space W]
    {e : MvPolynomial (Fin n) ℂ} (he : e ≠ 0)
    [IsLocalIso (AnalyticSpace.restrictHom ρ₀ (polyOpens e))] (hW : IsLocallyOpenInAffine W)
    (hZ : interior {w | polyEval e (ρ₀.toLRSHom.base w) = 0} = ∅) :
    (extension ρ₀).IsCoherent := by
  refine isCoherent_of_forall_moduleChart _ fun y ↦ ?_
  obtain ⟨i, v, rfl⟩ := exists_mem_range_chart y
  exact ⟨_, _, hB ⊤ (chartOpens e i) le_top (cover ρ₀ e i) (hasThinComplement_chartOpens he i),
    chartModuleChart ρ₀ e i hW hZ, ⟨v, trivial⟩, rfl⟩

end

end ProjectiveCompletion

end ComplexAnalytic
