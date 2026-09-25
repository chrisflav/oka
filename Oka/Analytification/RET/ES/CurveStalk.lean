/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.ES.CurveSections
import Oka.AlgebraicGeometry.Modules.TildeExact

/-!
# The functions of polynomial growth on a finite cover of `ℂ`

Keep the notation of `Oka/Analytification/RET/ES/CurveSections.lean`: `ρ₀ : W ⟶ ℂ¹` is finite
with Hausdorff source, a local isomorphism over `{‖z‖ > 1}`, with `ρ₀_* 𝒪_W` coherent, and
`ρ : W ⟶ ℙ¹_an` is its composite with the chart `0`. The global sections of `𝒪_W` of polynomial
growth in `z` form a ring `P` (`ComplexAnalytic.ProjectiveLine.polyGrowth`). By GAGA-3 the
canonical extension `𝒞̄` of `ρ₀_* 𝒪_W` to `ℙ¹_an` is `F^an` for a coherent `F` on `ℙ¹`, and `P` is
the image of `Γ(F, U₀)`. Hence:

- `ComplexAnalytic.ProjectiveLine.module_finite_polyGrowth`: `P` is a finite module over
  `Γ(ℙ¹, U₀) ≅ ℂ[z]`;
- `ComplexAnalytic.ProjectiveLine.bijective_polyGrowthStalkMap`: for `x` in the chart `0`, the map
  `𝒪_{ℙ¹_an,x} ⊗[Γ(ℙ¹, U₀)] P → ∏_{w ∈ ρ⁻¹ x} 𝒪_{W,w}` is bijective. It factors through
  `𝒪_{ℙ¹_an,x} ⊗ Γ(F, U₀) ≅ (F^an)_x ≅ 𝒞̄_x`
  (`ComplexAnalytic.isBaseChange_analytificationGermLinearMap`)
  and the map `𝒞̄_x → ∏_{w ∈ ρ⁻¹ x} 𝒪_{W,w}` (`ComplexAnalytic.ProjectiveLine.extensionStalkToPi`),
  which is bijective since `ρ` is finite over the chart `0`.
-/

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry Topology Filter Limits

universe u

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
/-- **The sections of a quasi-coherent sheaf of finite type over an affine open are a finite
module.** -/
theorem module_finite_sections_of_isAffineOpen_of_isFiniteType {X : Scheme.{u}} (F : X.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] {U : X.Opens} (hU : IsAffineOpen U) :
    Module.Finite Γ(X, U) Γ(F, U) := by
  haveI hΓ : Module.Finite Γ(X, U)
      (moduleSpecΓFunctor.obj (F.restrict hU.fromSpec) : Type u) :=
    module_finite_Γ_restrict hU.fromSpec F
  letI : Module Γ(X, U) Γ(F.restrict hU.fromSpec, ⊤) :=
    inferInstanceAs (Module Γ(X, U) (moduleSpecΓFunctor.obj (F.restrict hU.fromSpec) : Type u))
  haveI : Module.Finite Γ(X, U) Γ(F.restrict hU.fromSpec, ⊤) := hΓ
  haveI : Module.Finite Γ(Spec Γ(X, U), ⊤) Γ(F.restrict hU.fromSpec, ⊤) :=
    Module.Finite.of_ringEquiv (Scheme.ΓSpecIso Γ(X, U)).symm.commRingCatIsoToRingEquiv
      fun _ _ ↦ rfl
  haveI h := module_finite_sections_of_restrict hU.fromSpec F ⊤
  have he : (hU.fromSpec ''ᵁ (⊤ : (Spec Γ(X, U)).Opens) : X.Opens) = U := by
    rw [Scheme.Hom.image_top_eq_opensRange, hU.opensRange_fromSpec]
  exact he ▸ h

end AlgebraicGeometry.Scheme.Modules

namespace ComplexAnalytic.ProjectiveLine

open AnalyticSpace projectiveSpaceAn LocallyRingedSpace AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules TensorProduct

noncomputable section

variable {W : AnalyticSpace.{u}} (ρ₀ : W ⟶ AnalyticSpace.complexAffineSpace.{u} 1)
  (x : projectiveSpaceAn.{u} 1)

/-- The germs along the fibre of a section of the extension. -/
def extensionGerms (U : OpenNhds x) (s : (extension ρ₀).val.obj (op U.1)) :
    ∀ w : (toProjectiveLine ρ₀).toLRSHom.base ⁻¹' {x}, W.presheaf.stalk w.1 :=
  fun w ↦ W.presheaf.germ _ w.1 (show _ ∈ U.1 by rw [w.2]; exact U.2) (extVal ρ₀ s)

/-- **The map from the stalk of the extension to the product of the stalks of `𝒪_W` along the
fibre**, `s_x ↦ (s_w)_w`. -/
def extensionStalkToPi :
    TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (extension ρ₀).val.presheaf x →+
      ∀ w : (toProjectiveLine ρ₀).toLRSHom.base ⁻¹' {x}, W.presheaf.stalk w.1 :=
  (colimit.desc ((OpenNhds.inclusion x).op ⋙ (extension ρ₀).val.presheaf)
    { pt := AddCommGrpCat.of (∀ w : (toProjectiveLine ρ₀).toLRSHom.base ⁻¹' {x},
        W.presheaf.stalk w.1)
      ι :=
        { app U := AddCommGrpCat.ofHom
            { toFun s := extensionGerms ρ₀ x U.unop s
              map_zero' := funext fun _ ↦ map_zero _
              map_add' s t := funext fun _ ↦ map_add _ _ _ }
          naturality U V i := by
            ext s
            funext w
            exact W.presheaf.germ_res_apply _ _ _ _ } }).hom

lemma extensionStalkToPi_germ (U : (projectiveSpaceAn.{u} 1).Opens) (hx : x ∈ U)
    (s : (extension ρ₀).val.obj (op U)) (w : (toProjectiveLine ρ₀).toLRSHom.base ⁻¹' {x}) :
    extensionStalkToPi ρ₀ x (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
      (extension ρ₀).val.presheaf U x hx s) w =
      W.presheaf.germ _ w.1 (show _ ∈ U by rw [w.2]; exact hx) (extVal ρ₀ s) := by
  simp only [extensionStalkToPi, TopCat.Presheaf.germ]
  erw [← ConcreteCategory.comp_apply, colimit.ι_desc]
  rfl

variable {x} in
/-- **The map `ρ` is closed at the points of the chart `0`**: every open neighbourhood of a fibre
contains the preimage of an open neighbourhood of the point inside the chart. -/
lemma exists_preimage_le_of_mem_range [IsFinite ρ₀] (hx : x ∈ Set.range (chart 0))
    (G : W.Opens) (hG : (toProjectiveLine ρ₀).toLRSHom.base ⁻¹' {x} ⊆ G) :
    ∃ O : (projectiveSpaceAn.{u} 1).Opens, x ∈ O ∧ (O : Set _) ⊆ Set.range (chart 0) ∧
      (toProjectiveLine ρ₀).toLRSHom.base ⁻¹' O ⊆ G := by
  obtain ⟨z, rfl⟩ := hx
  obtain ⟨V, hzV, hV⟩ := (IsFinite.isClosedMap (f := ρ₀)).exists_preimage_le G fun w hw ↦
    hG (show chart 0 _ = chart 0 z from congrArg _ hw)
  refine ⟨⟨chart 0 '' V, (isOpenEmbedding_chart 0).isOpenMap _ V.isOpen⟩, ⟨z, hzV, rfl⟩,
    Set.image_subset_range _ _, fun w hw ↦ hV ?_⟩
  obtain ⟨z', hz', h⟩ := hw
  have e : z' = ρ₀.toLRSHom.base w := chart_injective 0 h
  change ρ₀.toLRSHom.base w ∈ V
  exact e ▸ hz'

lemma extVal_presheaf_map {U U' : (projectiveSpaceAn.{u} 1).Opens} (i : U' ⟶ U)
    (s : (extension ρ₀).val.obj (op U)) :
    extVal ρ₀ ((extension ρ₀).val.presheaf.map i.op s) =
      W.presheaf.map (homOfLE ((Opens.map (toProjectiveLine ρ₀).toLRSHom.base).monotone
        i.le)).op (extVal ρ₀ s) :=
  rfl

variable {x} in
theorem injective_extensionStalkToPi [IsFinite ρ₀] (hx : x ∈ Set.range (chart 0)) :
    Function.Injective (extensionStalkToPi ρ₀ x) := by
  intro a b hab
  obtain ⟨U, hxU, s, rfl⟩ :=
    TopCat.Presheaf.exists_germ_eq (C := AddCommGrpCat.{u}) (extension ρ₀).val.presheaf a
  obtain ⟨U', hxU', s', rfl⟩ :=
    TopCat.Presheaf.exists_germ_eq (C := AddCommGrpCat.{u}) (extension ρ₀).val.presheaf b
  have hw : ∀ w : (toProjectiveLine ρ₀).toLRSHom.base ⁻¹' {x}, ∃ (G : W.Opens) (_ : w.1 ∈ G)
      (iU : G ⟶ (Opens.map (toProjectiveLine ρ₀).toLRSHom.base).obj U)
      (iU' : G ⟶ (Opens.map (toProjectiveLine ρ₀).toLRSHom.base).obj U'),
      W.presheaf.map iU.op (extVal ρ₀ s) = W.presheaf.map iU'.op (extVal ρ₀ s') := fun w ↦ by
    have h := congrFun hab w
    rw [extensionStalkToPi_germ, extensionStalkToPi_germ] at h
    exact W.presheaf.germ_eq w.1 _ _ _ _ h
  choose G hwG iU iU' hG using hw
  obtain ⟨O, hxO, hOr, hOG⟩ := exists_preimage_le_of_mem_range ρ₀ hx (⨆ w, G w) fun w hw ↦
    Opens.mem_iSup.2 ⟨⟨w, hw⟩, hwG _⟩
  let O' : (projectiveSpaceAn.{u} 1).Opens := O ⊓ U ⊓ U'
  have hxO' : x ∈ O' := ⟨⟨hxO, hxU⟩, hxU'⟩
  have i1 : O' ⟶ U := homOfLE (inf_le_left.trans inf_le_right)
  have i2 : O' ⟶ U' := homOfLE inf_le_right
  rw [← TopCat.Presheaf.germ_res_apply (C := AddCommGrpCat.{u}) _ i1 x hxO' s,
    ← TopCat.Presheaf.germ_res_apply (C := AddCommGrpCat.{u}) _ i2 x hxO' s']
  congr 1
  apply Subtype.ext
  change extVal ρ₀ _ = extVal ρ₀ _
  rw [extVal_presheaf_map, extVal_presheaf_map]
  refine TopCat.Sheaf.eq_of_locally_eq' W.sheaf (fun w ↦ G w ⊓
    (Opens.map (toProjectiveLine ρ₀).toLRSHom.base).obj O')
    ((Opens.map (toProjectiveLine ρ₀).toLRSHom.base).obj O') (fun _ ↦ homOfLE inf_le_right)
    (fun v hv ↦ ?_) _ _ fun w ↦ ?_
  · obtain ⟨w, hw⟩ := Opens.mem_iSup.1 (hOG hv.1.1)
    exact Opens.mem_iSup.2 ⟨w, hw, hv⟩
  · change W.presheaf.map _ (W.presheaf.map _ _) = W.presheaf.map _ (W.presheaf.map _ _)
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← W.presheaf.map_comp,
      ← W.presheaf.map_comp]
    have e1 : ((homOfLE ((Opens.map (toProjectiveLine ρ₀).toLRSHom.base).monotone i1.le)).op ≫
        (homOfLE inf_le_right : G w ⊓ (Opens.map (toProjectiveLine ρ₀).toLRSHom.base).obj O' ⟶
          _).op) = (iU w).op ≫ (homOfLE inf_le_left).op := rfl
    have e2 : ((homOfLE ((Opens.map (toProjectiveLine ρ₀).toLRSHom.base).monotone i2.le)).op ≫
        (homOfLE inf_le_right : G w ⊓ (Opens.map (toProjectiveLine ρ₀).toLRSHom.base).obj O' ⟶
          _).op) = (iU' w).op ≫ (homOfLE inf_le_left).op := rfl
    rw [e1, e2, W.presheaf.map_comp, W.presheaf.map_comp, ConcreteCategory.comp_apply,
      ConcreteCategory.comp_apply, hG w]

variable {x} in
theorem surjective_extensionStalkToPi [IsFinite ρ₀] [T2Space W]
    (hx : x ∈ Set.range (chart 0)) :
    Function.Surjective (extensionStalkToPi ρ₀ x) := by
  intro t
  have hfin : ((toProjectiveLine ρ₀).toLRSHom.base ⁻¹' {x}).Finite := by
    obtain ⟨z, rfl⟩ := hx
    have : (toProjectiveLine ρ₀).toLRSHom.base ⁻¹' {chart 0 z} = ρ₀.toLRSHom.base ⁻¹' {z} := by
      ext w
      exact ⟨fun h ↦ chart_injective 0 h, fun h ↦ congrArg (chart 0) h⟩
    rw [this]
    haveI := IsFinite.finite_fiber (f := ρ₀) z
    exact Set.toFinite _
  have hw : ∀ w : (toProjectiveLine ρ₀).toLRSHom.base ⁻¹' {x}, ∃ (G : W.Opens) (_ : w.1 ∈ G)
      (s : W.presheaf.obj (op G)), W.presheaf.germ G w.1 ‹_› s = t w :=
    fun w ↦ W.presheaf.exists_germ_eq (t w)
  choose G hwG s hs using hw
  obtain ⟨D, hD, hdisj⟩ := hfin.t2_separation
  let D' : (toProjectiveLine ρ₀).toLRSHom.base ⁻¹' {x} → W.Opens :=
    fun w ↦ G w ⊓ ⟨D w.1, (hD w.1).2⟩
  have hwD' : ∀ w, w.1 ∈ D' w := fun w ↦ ⟨hwG w, (hD w.1).1⟩
  let sf : ∀ w, W.presheaf.obj (op (D' w)) := fun w ↦ W.presheaf.map (homOfLE inf_le_left).op (s w)
  have hcompat : TopCat.Presheaf.IsCompatible W.presheaf D' sf := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rfl
    · refine TopCat.Presheaf.eq_of_le_bot W.sheaf.2 (fun v hv ↦ ?_) _ _
      exact (hdisj i.2 j.2 (fun h ↦ hij (Subtype.ext h))).le_bot ⟨hv.1.2, hv.2.2⟩
  obtain ⟨g, hg, -⟩ := TopCat.Sheaf.existsUnique_gluing W.sheaf D' sf hcompat
  obtain ⟨O, hxO, hOr, hOD⟩ := exists_preimage_le_of_mem_range ρ₀ hx (⨆ w, D' w) fun w hw ↦
    Opens.mem_iSup.2 ⟨⟨w, hw⟩, hwD' _⟩
  let s₀ : W.presheaf.obj (op ((Opens.map (toProjectiveLine ρ₀).toLRSHom.base).obj O)) :=
    W.presheaf.map (homOfLE hOD : (Opens.map (toProjectiveLine ρ₀).toLRSHom.base).obj O ⟶ _).op g
  have hs₀ : s₀ ∈ (boundedSubmodule (toProjectiveLine ρ₀) {infty}).obj (op O) :=
    isBoundedNear_of_disjoint (Set.disjoint_singleton_right.2 fun h ↦
      ((mem_range_chart_zero_iff _).1 (hOr h)) rfl) s₀
  refine ⟨TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) (extension ρ₀).val.presheaf O x hxO
    ⟨s₀, hs₀⟩, funext fun w ↦ ?_⟩
  rw [extensionStalkToPi_germ, ← hs w]
  change W.presheaf.germ _ _ _ (W.presheaf.map _ g) = _
  rw [W.presheaf.germ_res_apply]
  calc W.presheaf.germ (⨆ w, D' w) w.1 _ g
      = W.presheaf.germ (D' w) w.1 (hwD' w) (W.presheaf.map (Opens.leSupr D' w).op g) :=
        (W.presheaf.germ_res_apply (Opens.leSupr D' w) w.1 (hwD' w) g).symm
    _ = W.presheaf.germ (D' w) w.1 (hwD' w) (sf w) := congrArg _ (hg w)
    _ = W.presheaf.germ (G w) w.1 (hwG w) (s w) := W.presheaf.germ_res_apply _ _ _ _

lemma extensionStalkToPi_smul (t : (projectiveSpaceAn.{u} 1).presheaf.stalk x)
    (g : ((projectiveSpaceAn.{u} 1).toLocallyRingedSpace.stalkFunctor x).obj (extension ρ₀))
    (w : (toProjectiveLine ρ₀).toLRSHom.base ⁻¹' {x}) :
    extensionStalkToPi ρ₀ x (t • g) w =
      fibreStalkMap (toProjectiveLine ρ₀) x w t * extensionStalkToPi ρ₀ x g w := by
  obtain ⟨U, hxU, r, rfl⟩ := (projectiveSpaceAn.{u} 1).presheaf.exists_germ_eq t
  obtain ⟨U', hxU', s, rfl⟩ :=
    TopCat.Presheaf.exists_germ_eq (C := AddCommGrpCat.{u}) (extension ρ₀).val.presheaf g
  have hxV : x ∈ U ⊓ U' := ⟨hxU, hxU'⟩
  rw [← (projectiveSpaceAn.{u} 1).presheaf.germ_res_apply (homOfLE inf_le_left) x hxV r,
    ← TopCat.Presheaf.germ_res_apply (C := AddCommGrpCat.{u}) _ (homOfLE inf_le_right) x hxV s]
  erw [← PresheafOfModules.germ_smul]
  erw [extensionStalkToPi_germ]
  rw [fibreStalkMap_germ, extVal_smul, map_mul]
  erw [extensionStalkToPi_germ]

/-! ### The ring of functions of polynomial growth -/

lemma hasPolyGrowth_one : HasPolyGrowth ρ₀ (1 : W.presheaf.obj (op ⊤)) :=
  ⟨0, 1, 0, fun w _ ↦ by rw [map_one, norm_one, pow_zero, mul_one]⟩

lemma HasPolyGrowth.neg {f : W.presheaf.obj (op ⊤)} (hf : HasPolyGrowth ρ₀ f) :
    HasPolyGrowth ρ₀ (-f) := by
  obtain ⟨k, C, R, h⟩ := hf
  exact ⟨k, C, R, fun w hw ↦ by rw [map_neg, norm_neg]; exact h w hw⟩

lemma HasPolyGrowth.add {f g : W.presheaf.obj (op ⊤)} (hf : HasPolyGrowth ρ₀ f)
    (hg : HasPolyGrowth ρ₀ g) : HasPolyGrowth ρ₀ (f + g) := by
  obtain ⟨k, C, R, h⟩ := hf
  obtain ⟨k', C', R', h'⟩ := hg
  refine ⟨max k k', max C 0 + max C' 0, max (max R R') 1, fun w hw ↦ ?_⟩
  set z := ‖coord (ρ₀.toLRSHom.base w)‖
  have hz1 : 1 ≤ z := (le_max_right _ _).trans hw.le
  have hk : z ^ k ≤ z ^ max k k' := pow_le_pow_right₀ hz1 (le_max_left _ _)
  have hk' : z ^ k' ≤ z ^ max k k' := pow_le_pow_right₀ hz1 (le_max_right _ _)
  rw [map_add, add_mul]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · exact (h w ((le_max_left _ _).trans_lt ((le_max_left _ _).trans_lt hw))).trans
      (mul_le_mul (le_max_left _ _) hk (by positivity) (le_max_right _ _))
  · exact (h' w ((le_max_right _ _).trans_lt ((le_max_left _ _).trans_lt hw))).trans
      (mul_le_mul (le_max_left _ _) hk' (by positivity) (le_max_right _ _))

lemma HasPolyGrowth.mul {f g : W.presheaf.obj (op ⊤)} (hf : HasPolyGrowth ρ₀ f)
    (hg : HasPolyGrowth ρ₀ g) : HasPolyGrowth ρ₀ (f * g) := by
  obtain ⟨k, C, R, h⟩ := hf
  obtain ⟨k', C', R', h'⟩ := hg
  refine ⟨k + k', max C 0 * max C' 0, max R R', fun w hw ↦ ?_⟩
  rw [map_mul, norm_mul, pow_add, mul_mul_mul_comm]
  exact mul_le_mul ((h w ((le_max_left _ _).trans_lt hw)).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)))
    ((h' w ((le_max_right _ _).trans_lt hw)).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)))
    (norm_nonneg _) (by positivity)

/-- **The ring of functions of polynomial growth** on `W`. -/
def polyGrowth : Subring (W.presheaf.obj (op ⊤)) where
  carrier := {f | HasPolyGrowth ρ₀ f}
  one_mem' := hasPolyGrowth_one ρ₀
  mul_mem' := fun hf hg ↦ hf.mul ρ₀ hg
  zero_mem' := by simpa using (hasPolyGrowth_one ρ₀).add ρ₀ ((hasPolyGrowth_one ρ₀).neg ρ₀)
  add_mem' := fun hf hg ↦ hf.add ρ₀ hg
  neg_mem' := fun hf ↦ hf.neg ρ₀

/-! ### Algebraisation -/

section Algebraisation

variable (F : (projectiveSpace.{u} 1).obj.left.Modules)
  (e : (analytificationModules (projectiveSpace.{u} 1)).obj F ≅ extension ρ₀)
  (hF : SheafOfModules.IsCoherent
    (R := (projectiveSpace.{u} 1).obj.left.toLocallyRingedSpace.ringSheaf) F)

include hF in
lemma mem_polyGrowth_iff (f : W.presheaf.obj (op ⊤)) :
    f ∈ polyGrowth ρ₀ ↔ ∃ m : Γ(F, stdU 0), sectionFun ρ₀ F e m = f :=
  ⟨exists_sectionFun_eq ρ₀ F e hF f, fun ⟨m, hm⟩ ↦ hm ▸ hasPolyGrowth_sectionFun ρ₀ F e hF m⟩

include e hF in
lemma toSections_mem_polyGrowth (r : Γ((projectiveSpace.{u} 1).obj.left, stdU 0)) :
    toSections ρ₀ r ∈ polyGrowth ρ₀ := by
  obtain ⟨m, hm⟩ := (mem_polyGrowth_iff ρ₀ F e hF 1).1 (hasPolyGrowth_one ρ₀)
  refine (mem_polyGrowth_iff ρ₀ F e hF _).2 ⟨r • m, ?_⟩
  rw [sectionFun_smul, hm, mul_one]

end Algebraisation

section Main

variable [IsFinite ρ₀] [T2Space W] [IsLocalIso (AnalyticSpace.restrictHom ρ₀ outerOpens)]
  (hK : (Hom.pushUnit ρ₀.toLRSHom).IsCoherent)

include hK in
/-- **GAGA-3 for the canonical extension**: it is the analytification of a coherent sheaf on
`ℙ¹`. -/
lemma exists_algebraisation :
    ∃ (F : (projectiveSpace.{u} 1).obj.left.Modules) (_ : SheafOfModules.IsCoherent
      (R := (projectiveSpace.{u} 1).obj.left.toLocallyRingedSpace.ringSheaf) F),
      Nonempty ((analytificationModules (projectiveSpace.{u} 1)).obj F ≅ extension ρ₀) := by
  obtain ⟨F, hF, ⟨e⟩⟩ := gaga₃_projectiveSpace_of_isCoherent 1 _ (isCoherent_extension ρ₀ hK)
  exact ⟨F, hF, ⟨e⟩⟩

include hK in
lemma toSections_mem_polyGrowth' (r : Γ((projectiveSpace.{u} 1).obj.left, stdU 0)) :
    toSections ρ₀ r ∈ polyGrowth ρ₀ := by
  obtain ⟨F, hF, ⟨e⟩⟩ := exists_algebraisation ρ₀ hK
  exact toSections_mem_polyGrowth ρ₀ F e hF r

/-- The ring `Γ(ℙ¹, U₀)`. -/
abbrev ringU₀ : CommRingCat.{u} := Γ((projectiveSpace.{u} 1).obj.left, stdU 0)

/-- The functions of polynomial growth form an algebra over `Γ(ℙ¹, U₀)`. -/
@[reducible] def polyGrowthAlgebra : Algebra ringU₀ (polyGrowth ρ₀) :=
  ((toSections ρ₀).codRestrict _ (toSections_mem_polyGrowth' ρ₀ hK)).toAlgebra

/-- **The stalk comparison map** `𝒪_{ℙ¹_an,x} ⊗[Γ(ℙ¹, U₀)] P → ∏_{w ∈ ρ⁻¹ x} 𝒪_{W,w}` for the
ring `P` of functions of polynomial growth, `s ⊗ f ↦ (ρ^♯ s · f_w)_w`. -/
def polyGrowthStalkMap (x : analytificationPreimage (projectiveSpace.{u} 1) (stdU 0)) :
    letI := polyGrowthAlgebra ρ₀ hK
    (projectiveSpaceAn.{u} 1).presheaf.stalk x.1 ⊗[ringU₀]
      polyGrowth ρ₀ →+*
      ((w : (toProjectiveLine ρ₀).toLRSHom.base ⁻¹' {x.1}) → W.presheaf.stalk w.1) :=
  letI := polyGrowthAlgebra ρ₀ hK
  letI : Algebra ((projectiveSpaceAn.{u} 1).presheaf.stalk x.1)
      ((w : (toProjectiveLine ρ₀).toLRSHom.base ⁻¹' {x.1}) → W.presheaf.stalk w.1) :=
    (RingHom.pi fun w ↦ fibreStalkMap (toProjectiveLine ρ₀) x.1 w).toAlgebra
  letI : Algebra ringU₀.{u}
      ((w : (toProjectiveLine ρ₀).toLRSHom.base ⁻¹' {x.1}) → W.presheaf.stalk w.1) :=
    ((RingHom.pi fun w ↦ fibreStalkMap (toProjectiveLine ρ₀) x.1 w).comp
      (algebraMap ringU₀.{u}
        ((projectiveSpaceAn.{u} 1).presheaf.stalk x.1))).toAlgebra
  haveI : IsScalarTower ringU₀.{u}
      ((projectiveSpaceAn.{u} 1).presheaf.stalk x.1)
      ((w : (toProjectiveLine ρ₀).toLRSHom.base ⁻¹' {x.1}) → W.presheaf.stalk w.1) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  (Algebra.TensorProduct.lift (Algebra.ofId _ _)
    { toRingHom := RingHom.pi fun w ↦ (W.presheaf.Γgerm w.1).hom.comp (polyGrowth ρ₀).subtype
      commutes' := fun r ↦ funext fun w ↦ by
        change W.presheaf.Γgerm w.1 (toSections ρ₀ r) = fibreStalkMap _ x.1 w
          ((πP.stalkMap x.1).hom ((projectiveSpace.{u} 1).obj.left.presheaf.germ _ _ x.2 r))
        rw [LocallyRingedSpace.stalkMap_germ_apply, fibreStalkMap_germ]
        exact W.presheaf.germ_res_apply _ _ _ _ }
    fun _ _ ↦ Commute.all _ _).toRingHom

lemma polyGrowthStalkMap_tmul (x : analytificationPreimage (projectiveSpace.{u} 1) (stdU 0))
    (s : (projectiveSpaceAn.{u} 1).presheaf.stalk x.1) (f : polyGrowth ρ₀)
    (w : (toProjectiveLine ρ₀).toLRSHom.base ⁻¹' {x.1}) :
    letI := polyGrowthAlgebra ρ₀ hK
    polyGrowthStalkMap ρ₀ hK x (s ⊗ₜ f) w =
      fibreStalkMap (toProjectiveLine ρ₀) x.1 w s * W.presheaf.Γgerm w.1 f.1 :=
  rfl

/-- **The stalks of the pushforward are the base change of the functions of polynomial
growth**: at every point of the chart `0` the map
`𝒪_{ℙ¹_an,x} ⊗[Γ(ℙ¹, U₀)] P → ∏_{w ∈ ρ⁻¹ x} 𝒪_{W,w}` is bijective. -/
theorem bijective_polyGrowthStalkMap
    (x : analytificationPreimage (projectiveSpace.{u} 1) (stdU 0)) :
    letI := polyGrowthAlgebra ρ₀ hK
    Function.Bijective (polyGrowthStalkMap ρ₀ hK x) := by
  letI := polyGrowthAlgebra ρ₀ hK
  obtain ⟨F, hF, ⟨e⟩⟩ := exists_algebraisation ρ₀ hK
  haveI : SheafOfModules.IsCoherent
      (R := (projectiveSpace.{u} 1).obj.left.toLocallyRingedSpace.ringSheaf) F := hF
  haveI : F.IsQuasicoherent := Scheme.Modules.isQuasicoherent_of_isCoherent F
  have hSF := isBaseChange_analytificationGermLinearMap (F := F) x
    (isAffineOpen_U (n := 1) (R := ULift.{u} ℂ) 0)
  let σ : Γ(F, stdU 0) →ₗ[ringU₀] polyGrowth ρ₀ :=
    { toFun m := ⟨sectionFun ρ₀ F e m, hasPolyGrowth_sectionFun ρ₀ F e hF m⟩
      map_add' m m' := Subtype.ext (sectionFun_add ρ₀ F e m m')
      map_smul' r m := Subtype.ext (sectionFun_smul ρ₀ F e r m) }
  have hσ : Function.Surjective σ := fun f ↦ by
    obtain ⟨m, hm⟩ := exists_sectionFun_eq ρ₀ F e hF f.1 f.2
    exact ⟨m, Subtype.ext hm⟩
  have hx : x.1 ∈ Set.range (chart 0) := by
    rw [range_chart]
    exact x.2
  let ex := ((projectiveSpaceAn.{u} 1).toLocallyRingedSpace.stalkFunctor x.1).map e.hom
  have key : ∀ z, extensionStalkToPi ρ₀ x.1 (ex (hSF.equiv z)) =
      polyGrowthStalkMap ρ₀ hK x (LinearMap.lTensor _ σ z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero =>
      simp only [map_zero]
      exact map_zero (extensionStalkToPi ρ₀ x.1)
    | add a b ha hb =>
      simp only [map_add]
      rw [← ha, ← hb]
      exact map_add (extensionStalkToPi ρ₀ x.1) _ _
    | tmul s m =>
      rw [IsBaseChange.equiv_tmul, LinearMap.lTensor_tmul]
      funext w
      rw [polyGrowthStalkMap_tmul]
      erw [LinearMap.map_smul]
      rw [extensionStalkToPi_smul]
      congr 1
      have hg : ex (analytificationGermLinearMap F x m) =
          TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) (extension ρ₀).val.presheaf _ x.1 x.2
            (e.hom.val.app _ (analytificationSection F m)) :=
        PresheafOfModules.stalkFunctor_map_germ x.1 _ _ e.hom.val _ x.2 _
      erw [hg, extensionStalkToPi_germ]
      exact (W.presheaf.germ_res_apply _ _ _ _).symm
  have hex : Function.Bijective ex := (ConcreteCategory.isIso_iff_bijective ex).1 inferInstance
  refine ⟨(injective_iff_map_eq_zero _).2 fun y hy ↦ ?_, fun y ↦ ?_⟩
  · obtain ⟨z, rfl⟩ := LinearMap.lTensor_surjective _ hσ y
    rw [← key] at hy
    have h0 : hSF.equiv z = 0 := by
      refine hex.1 (injective_extensionStalkToPi ρ₀ hx ?_)
      rw [hy, map_zero]
      exact (map_zero (extensionStalkToPi ρ₀ x.1)).symm
    rw [LinearEquiv.map_eq_zero_iff] at h0
    rw [h0, map_zero]
  · obtain ⟨g, hg⟩ := surjective_extensionStalkToPi ρ₀ hx y
    obtain ⟨g', rfl⟩ := hex.2 g
    obtain ⟨z, rfl⟩ := hSF.equiv.surjective g'
    exact ⟨_, (key z).symm.trans hg⟩

theorem module_finite_polyGrowth :
    letI := polyGrowthAlgebra ρ₀ hK
    Module.Finite ringU₀ (polyGrowth ρ₀) := by
  letI := polyGrowthAlgebra ρ₀ hK
  obtain ⟨F, hF, ⟨e⟩⟩ := exists_algebraisation ρ₀ hK
  haveI : SheafOfModules.IsCoherent
      (R := (projectiveSpace.{u} 1).obj.left.toLocallyRingedSpace.ringSheaf) F := hF
  haveI : F.IsQuasicoherent := Scheme.Modules.isQuasicoherent_of_isCoherent F
  haveI : F.IsFiniteType := hF.isFiniteType
  haveI := Scheme.Modules.module_finite_sections_of_isAffineOpen_of_isFiniteType F
    (isAffineOpen_U (n := 1) (R := ULift.{u} ℂ) 0)
  let σ : Γ(F, stdU 0) →ₗ[ringU₀] polyGrowth ρ₀ :=
    { toFun m := ⟨sectionFun ρ₀ F e m, hasPolyGrowth_sectionFun ρ₀ F e hF m⟩
      map_add' m m' := Subtype.ext (sectionFun_add ρ₀ F e m m')
      map_smul' r m := Subtype.ext (sectionFun_smul ρ₀ F e r m) }
  refine Module.Finite.of_surjective σ fun f ↦ ?_
  obtain ⟨m, hm⟩ := exists_sectionFun_eq ρ₀ F e hF f.1 f.2
  exact ⟨m, Subtype.ext hm⟩

end Main

end
end ComplexAnalytic.ProjectiveLine
