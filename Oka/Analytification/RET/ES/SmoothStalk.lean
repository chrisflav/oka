/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.ES.SmoothSections
import Oka.Analytification.RET.ES.CurveStalk

/-!
# The functions of polynomial growth on a finite cover of `ℂⁿ`

Keep the notation of `Oka/Analytification/RET/ES/SmoothSections.lean`: `ρ₀ : W ⟶ ℂⁿ` is finite
with Hausdorff source and `ρ : W ⟶ ℙⁿ_an` is its composite with the chart `0`; suppose that the
canonical extension `𝒞̄` of `ρ₀_* 𝒪_W` to `ℙⁿ_an` is coherent. The global sections of `𝒪_W` of
polynomial growth in `z = ρ₀` form a ring `P` (`ComplexAnalytic.ProjectiveCompletion.polyGrowth`).
By GAGA-3, `𝒞̄ = F^an` for a coherent `F` on `ℙⁿ`, and `P` is the image of `Γ(F, U₀)`. Hence:

- `ComplexAnalytic.ProjectiveCompletion.module_finite_polyGrowth`: `P` is a finite module over
  `Γ(ℙⁿ, U₀) ≅ ℂ[z₁, …, zₙ]`;
- `ComplexAnalytic.ProjectiveCompletion.bijective_polyGrowthStalkMap`: for `x` in the chart `0`,
  the map `𝒪_{ℙⁿ_an,x} ⊗[Γ(ℙⁿ, U₀)] P → ∏_{w ∈ ρ⁻¹ x} 𝒪_{W,w}` is bijective. It factors through
  `𝒪_{ℙⁿ_an,x} ⊗ Γ(F, U₀) ≅ (F^an)_x ≅ 𝒞̄_x` and the map `𝒞̄_x → ∏_{w ∈ ρ⁻¹ x} 𝒪_{W,w}`
  (`ComplexAnalytic.ProjectiveCompletion.extensionStalkToPi`), which is bijective since `ρ` is
  finite over the chart `0`.
-/

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry Topology Filter Limits

universe u

namespace ComplexAnalytic.ProjectiveCompletion

open AnalyticSpace projectiveSpaceAn LocallyRingedSpace AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules TensorProduct

noncomputable section

variable {n : ℕ} {W : AnalyticSpace.{u}} (ρ₀ : W ⟶ AnalyticSpace.complexAffineSpace.{u} n)
  (x : projectiveSpaceAn.{u} n)

/-- The germs along the fibre of a section of the extension. -/
def extensionGerms (U : OpenNhds x) (s : (extension ρ₀).val.obj (op U.1)) :
    ∀ w : (toProj ρ₀).toLRSHom.base ⁻¹' {x}, W.presheaf.stalk w.1 :=
  fun w ↦ W.presheaf.germ _ w.1 (show _ ∈ U.1 by rw [w.2]; exact U.2) (extVal ρ₀ s)

/-- **The map from the stalk of the extension to the product of the stalks of `𝒪_W` along the
fibre**, `s_x ↦ (s_w)_w`. -/
def extensionStalkToPi :
    TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (extension ρ₀).val.presheaf x →+
      ∀ w : (toProj ρ₀).toLRSHom.base ⁻¹' {x}, W.presheaf.stalk w.1 :=
  (colimit.desc ((OpenNhds.inclusion x).op ⋙ (extension ρ₀).val.presheaf)
    { pt := AddCommGrpCat.of (∀ w : (toProj ρ₀).toLRSHom.base ⁻¹' {x},
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

lemma extensionStalkToPi_germ (U : (projectiveSpaceAn.{u} n).Opens) (hx : x ∈ U)
    (s : (extension ρ₀).val.obj (op U)) (w : (toProj ρ₀).toLRSHom.base ⁻¹' {x}) :
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
    (G : W.Opens) (hG : (toProj ρ₀).toLRSHom.base ⁻¹' {x} ⊆ G) :
    ∃ O : (projectiveSpaceAn.{u} n).Opens, x ∈ O ∧
      (O : Set (projectiveSpaceAn.{u} n)) ⊆ Set.range (chart 0) ∧
      (toProj ρ₀).toLRSHom.base ⁻¹' O ⊆ G := by
  obtain ⟨z, rfl⟩ := hx
  obtain ⟨V, hzV, hV⟩ := (IsFinite.isClosedMap (f := ρ₀)).exists_preimage_le G fun w hw ↦
    hG (show chart 0 _ = chart 0 z from congrArg _ hw)
  refine ⟨⟨chart 0 '' V, (isOpenEmbedding_chart 0).isOpenMap _ V.isOpen⟩, ⟨z, hzV, rfl⟩,
    Set.image_subset_range _ _, fun w hw ↦ hV ?_⟩
  obtain ⟨z', hz', h⟩ := hw
  have e : z' = ρ₀.toLRSHom.base w := chart_injective 0 h
  change ρ₀.toLRSHom.base w ∈ V
  exact e ▸ hz'

lemma extVal_presheaf_map {U U' : (projectiveSpaceAn.{u} n).Opens} (i : U' ⟶ U)
    (s : (extension ρ₀).val.obj (op U)) :
    extVal ρ₀ ((extension ρ₀).val.presheaf.map i.op s) =
      W.presheaf.map (homOfLE ((Opens.map (toProj ρ₀).toLRSHom.base).monotone
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
  have hw : ∀ w : (toProj ρ₀).toLRSHom.base ⁻¹' {x}, ∃ (G : W.Opens) (_ : w.1 ∈ G)
      (iU : G ⟶ (Opens.map (toProj ρ₀).toLRSHom.base).obj U)
      (iU' : G ⟶ (Opens.map (toProj ρ₀).toLRSHom.base).obj U'),
      W.presheaf.map iU.op (extVal ρ₀ s) = W.presheaf.map iU'.op (extVal ρ₀ s') := fun w ↦ by
    have h := congrFun hab w
    rw [extensionStalkToPi_germ, extensionStalkToPi_germ] at h
    exact W.presheaf.germ_eq w.1 _ _ _ _ h
  choose G hwG iU iU' hG using hw
  obtain ⟨O, hxO, hOr, hOG⟩ := exists_preimage_le_of_mem_range ρ₀ hx (⨆ w, G w) fun w hw ↦
    Opens.mem_iSup.2 ⟨⟨w, hw⟩, hwG _⟩
  let O' : (projectiveSpaceAn.{u} n).Opens := O ⊓ U ⊓ U'
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
    (Opens.map (toProj ρ₀).toLRSHom.base).obj O')
    ((Opens.map (toProj ρ₀).toLRSHom.base).obj O') (fun _ ↦ homOfLE inf_le_right)
    (fun v hv ↦ ?_) _ _ fun w ↦ ?_
  · obtain ⟨w, hw⟩ := Opens.mem_iSup.1 (hOG hv.1.1)
    exact Opens.mem_iSup.2 ⟨w, hw, hv⟩
  · change W.presheaf.map _ (W.presheaf.map _ _) = W.presheaf.map _ (W.presheaf.map _ _)
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← W.presheaf.map_comp,
      ← W.presheaf.map_comp]
    have e1 : ((homOfLE ((Opens.map (toProj ρ₀).toLRSHom.base).monotone i1.le)).op ≫
        (homOfLE inf_le_right : G w ⊓ (Opens.map (toProj ρ₀).toLRSHom.base).obj O' ⟶
          _).op) = (iU w).op ≫ (homOfLE inf_le_left).op := rfl
    have e2 : ((homOfLE ((Opens.map (toProj ρ₀).toLRSHom.base).monotone i2.le)).op ≫
        (homOfLE inf_le_right : G w ⊓ (Opens.map (toProj ρ₀).toLRSHom.base).obj O' ⟶
          _).op) = (iU' w).op ≫ (homOfLE inf_le_left).op := rfl
    rw [e1, e2, W.presheaf.map_comp, W.presheaf.map_comp, ConcreteCategory.comp_apply,
      ConcreteCategory.comp_apply, hG w]

variable {x} in
theorem surjective_extensionStalkToPi [IsFinite ρ₀] [T2Space W]
    (hx : x ∈ Set.range (chart 0)) :
    Function.Surjective (extensionStalkToPi ρ₀ x) := by
  intro t
  have hfin : ((toProj ρ₀).toLRSHom.base ⁻¹' {x}).Finite := by
    obtain ⟨z, rfl⟩ := hx
    have : (toProj ρ₀).toLRSHom.base ⁻¹' {chart 0 z} = ρ₀.toLRSHom.base ⁻¹' {z} := by
      ext w
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      rw [toProj_base]
      exact (chart_injective 0).eq_iff
    rw [this]
    haveI := IsFinite.finite_fiber (f := ρ₀) z
    exact Set.toFinite _
  have hw : ∀ w : (toProj ρ₀).toLRSHom.base ⁻¹' {x}, ∃ (G : W.Opens) (_ : w.1 ∈ G)
      (s : W.presheaf.obj (op G)), W.presheaf.germ G w.1 ‹_› s = t w :=
    fun w ↦ W.presheaf.exists_germ_eq (t w)
  choose G hwG s hs using hw
  obtain ⟨D, hD, hdisj⟩ := hfin.t2_separation
  let D' : (toProj ρ₀).toLRSHom.base ⁻¹' {x} → W.Opens :=
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
  let s₀ : W.presheaf.obj (op ((Opens.map (toProj ρ₀).toLRSHom.base).obj O)) :=
    W.presheaf.map (homOfLE hOD : (Opens.map (toProj ρ₀).toLRSHom.base).obj O ⟶ _).op g
  have hs₀ : s₀ ∈ (boundedSubmodule (toProj ρ₀) infinity).obj (op O) :=
    isBoundedNear_of_disjoint (Set.disjoint_left.2 fun y
      (hy : y ∈ (O : Set (projectiveSpaceAn.{u} n))) (hyinf : y ∈ infinity) ↦ hyinf (hOr hy)) s₀
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

lemma extensionStalkToPi_smul (t : (projectiveSpaceAn.{u} n).presheaf.stalk x)
    (g : ((projectiveSpaceAn.{u} n).toLocallyRingedSpace.stalkFunctor x).obj (extension ρ₀))
    (w : (toProj ρ₀).toLRSHom.base ⁻¹' {x}) :
    extensionStalkToPi ρ₀ x (t • g) w =
      fibreStalkMap (toProj ρ₀) x w t * extensionStalkToPi ρ₀ x g w := by
  obtain ⟨U, hxU, r, rfl⟩ := (projectiveSpaceAn.{u} n).presheaf.exists_germ_eq t
  obtain ⟨U', hxU', s, rfl⟩ :=
    TopCat.Presheaf.exists_germ_eq (C := AddCommGrpCat.{u}) (extension ρ₀).val.presheaf g
  have hxV : x ∈ U ⊓ U' := ⟨hxU, hxU'⟩
  rw [← (projectiveSpaceAn.{u} n).presheaf.germ_res_apply (homOfLE inf_le_left) x hxV r,
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
  set z := vnorm (ρ₀.toLRSHom.base w)
  have hz1 : 1 ≤ z := (le_max_right _ _).trans hw.le
  have hk : z ^ k ≤ z ^ max k k' := pow_le_pow_right₀ hz1 (le_max_left _ _)
  have hk' : z ^ k' ≤ z ^ max k k' := pow_le_pow_right₀ hz1 (le_max_right _ _)
  rw [map_add, add_mul]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · exact (h w ((le_max_left _ _).trans_lt ((le_max_left _ _).trans_lt hw))).trans
      (mul_le_mul (le_max_left _ _) hk (pow_nonneg (vnorm_nonneg _) _) (le_max_right _ _))
  · exact (h' w ((le_max_right _ _).trans_lt ((le_max_left _ _).trans_lt hw))).trans
      (mul_le_mul (le_max_left _ _) hk' (pow_nonneg (vnorm_nonneg _) _) (le_max_right _ _))

lemma HasPolyGrowth.mul {f g : W.presheaf.obj (op ⊤)} (hf : HasPolyGrowth ρ₀ f)
    (hg : HasPolyGrowth ρ₀ g) : HasPolyGrowth ρ₀ (f * g) := by
  obtain ⟨k, C, R, h⟩ := hf
  obtain ⟨k', C', R', h'⟩ := hg
  refine ⟨k + k', max C 0 * max C' 0, max R R', fun w hw ↦ ?_⟩
  rw [map_mul, norm_mul, pow_add, mul_mul_mul_comm]
  exact mul_le_mul ((h w ((le_max_left _ _).trans_lt hw)).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (vnorm_nonneg _) _)))
    ((h' w ((le_max_right _ _).trans_lt hw)).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (vnorm_nonneg _) _)))
    (norm_nonneg _) (mul_nonneg (le_max_right _ _) (pow_nonneg (vnorm_nonneg _) _))

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

variable (F : (projectiveSpace.{u} n).obj.left.Modules)
  (e : (analytificationModules (projectiveSpace.{u} n)).obj F ≅ extension ρ₀)
  (hF : SheafOfModules.IsCoherent
    (R := (projectiveSpace.{u} n).obj.left.toLocallyRingedSpace.ringSheaf) F)

include hF in
lemma mem_polyGrowth_iff (f : W.presheaf.obj (op ⊤)) :
    f ∈ polyGrowth ρ₀ ↔ ∃ m : Γ(F, stdU 0), sectionFun ρ₀ F e m = f :=
  ⟨exists_sectionFun_eq ρ₀ F e hF f, fun ⟨m, hm⟩ ↦ hm ▸ hasPolyGrowth_sectionFun ρ₀ F e hF m⟩

include e hF in
lemma toSections_mem_polyGrowth (r : Γ((projectiveSpace.{u} n).obj.left, stdU 0)) :
    toSections ρ₀ r ∈ polyGrowth ρ₀ := by
  obtain ⟨m, hm⟩ := (mem_polyGrowth_iff ρ₀ F e hF 1).1 (hasPolyGrowth_one ρ₀)
  refine (mem_polyGrowth_iff ρ₀ F e hF _).2 ⟨r • m, ?_⟩
  rw [sectionFun_smul, hm, mul_one]

end Algebraisation

section Main

variable [IsFinite ρ₀] [T2Space W]
  (hC : (extension ρ₀).IsCoherent)

omit [IsFinite ρ₀] [T2Space W] in
include hC in
/-- **GAGA-3 for the canonical extension**: it is the analytification of a coherent sheaf on
`ℙⁿ`. -/
lemma exists_algebraisation :
    ∃ (F : (projectiveSpace.{u} n).obj.left.Modules) (_ : SheafOfModules.IsCoherent
      (R := (projectiveSpace.{u} n).obj.left.toLocallyRingedSpace.ringSheaf) F),
      Nonempty ((analytificationModules (projectiveSpace.{u} n)).obj F ≅ extension ρ₀) := by
  obtain ⟨F, hF, ⟨e⟩⟩ := gaga₃_projectiveSpace_of_isCoherent n _ hC
  exact ⟨F, hF, ⟨e⟩⟩

omit [IsFinite ρ₀] [T2Space W] in
include hC in
lemma toSections_mem_polyGrowth' (r : Γ((projectiveSpace.{u} n).obj.left, stdU 0)) :
    toSections ρ₀ r ∈ polyGrowth ρ₀ := by
  obtain ⟨F, hF, ⟨e⟩⟩ := exists_algebraisation ρ₀ hC
  exact toSections_mem_polyGrowth ρ₀ F e hF r

/-- The ring `Γ(ℙⁿ, U₀)`. -/
abbrev ringU₀ (n : ℕ) : CommRingCat.{u} := Γ((projectiveSpace.{u} n).obj.left, stdU 0)

/-- The functions of polynomial growth form an algebra over `Γ(ℙⁿ, U₀)`. -/
@[reducible] def polyGrowthAlgebra : Algebra (ringU₀ n) (polyGrowth ρ₀) :=
  ((toSections ρ₀).codRestrict _ (toSections_mem_polyGrowth' ρ₀ hC)).toAlgebra

/-- **The stalk comparison map** `𝒪_{ℙⁿ_an,x} ⊗[Γ(ℙⁿ, U₀)] P → ∏_{w ∈ ρ⁻¹ x} 𝒪_{W,w}` for the
ring `P` of functions of polynomial growth, `s ⊗ f ↦ (ρ^♯ s · f_w)_w`. -/
def polyGrowthStalkMap (x : analytificationPreimage (projectiveSpace.{u} n) (stdU 0)) :
    letI := polyGrowthAlgebra ρ₀ hC
    (projectiveSpaceAn.{u} n).presheaf.stalk x.1 ⊗[ringU₀ n]
      polyGrowth ρ₀ →+*
      ((w : (toProj ρ₀).toLRSHom.base ⁻¹' {x.1}) → W.presheaf.stalk w.1) :=
  letI := polyGrowthAlgebra ρ₀ hC
  letI : Algebra ((projectiveSpaceAn.{u} n).presheaf.stalk x.1)
      ((w : (toProj ρ₀).toLRSHom.base ⁻¹' {x.1}) → W.presheaf.stalk w.1) :=
    (RingHom.pi fun w ↦ fibreStalkMap (toProj ρ₀) x.1 w).toAlgebra
  letI : Algebra (ringU₀.{u} n)
      ((w : (toProj ρ₀).toLRSHom.base ⁻¹' {x.1}) → W.presheaf.stalk w.1) :=
    ((RingHom.pi fun w ↦ fibreStalkMap (toProj ρ₀) x.1 w).comp
      (algebraMap (ringU₀.{u} n)
        ((projectiveSpaceAn.{u} n).presheaf.stalk x.1))).toAlgebra
  haveI : IsScalarTower (ringU₀.{u} n)
      ((projectiveSpaceAn.{u} n).presheaf.stalk x.1)
      ((w : (toProj ρ₀).toLRSHom.base ⁻¹' {x.1}) → W.presheaf.stalk w.1) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  (Algebra.TensorProduct.lift (Algebra.ofId _ _)
    { toRingHom := RingHom.pi fun w ↦ (W.presheaf.Γgerm w.1).hom.comp (polyGrowth ρ₀).subtype
      commutes' := fun r ↦ funext fun w ↦ by
        change W.presheaf.Γgerm w.1 (toSections ρ₀ r) = fibreStalkMap _ x.1 w
          ((πP.stalkMap x.1).hom ((projectiveSpace.{u} n).obj.left.presheaf.germ _ _ x.2 r))
        rw [LocallyRingedSpace.stalkMap_germ_apply, fibreStalkMap_germ]
        exact W.presheaf.germ_res_apply _ _ _ _ }
    fun _ _ ↦ Commute.all _ _).toRingHom

omit [IsFinite ρ₀] [T2Space W] in
lemma polyGrowthStalkMap_tmul (x : analytificationPreimage (projectiveSpace.{u} n) (stdU 0))
    (s : (projectiveSpaceAn.{u} n).presheaf.stalk x.1) (f : polyGrowth ρ₀)
    (w : (toProj ρ₀).toLRSHom.base ⁻¹' {x.1}) :
    letI := polyGrowthAlgebra ρ₀ hC
    polyGrowthStalkMap ρ₀ hC x (s ⊗ₜ f) w =
      fibreStalkMap (toProj ρ₀) x.1 w s * W.presheaf.Γgerm w.1 f.1 :=
  rfl

/-- **The stalks of the pushforward are the base change of the functions of polynomial
growth**: at every point of the chart `0` the map
`𝒪_{ℙⁿ_an,x} ⊗[Γ(ℙⁿ, U₀)] P → ∏_{w ∈ ρ⁻¹ x} 𝒪_{W,w}` is bijective. -/
theorem bijective_polyGrowthStalkMap
    (x : analytificationPreimage (projectiveSpace.{u} n) (stdU 0)) :
    letI := polyGrowthAlgebra ρ₀ hC
    Function.Bijective (polyGrowthStalkMap ρ₀ hC x) := by
  letI := polyGrowthAlgebra ρ₀ hC
  obtain ⟨F, hF, ⟨e⟩⟩ := exists_algebraisation ρ₀ hC
  haveI : SheafOfModules.IsCoherent
      (R := (projectiveSpace.{u} n).obj.left.toLocallyRingedSpace.ringSheaf) F := hF
  haveI : F.IsQuasicoherent := Scheme.Modules.isQuasicoherent_of_isCoherent F
  have hSF := isBaseChange_analytificationGermLinearMap (F := F) x
    (isAffineOpen_U (n := n) (R := ULift.{u} ℂ) 0)
  let σ : Γ(F, stdU 0) →ₗ[ringU₀ n] polyGrowth ρ₀ :=
    { toFun m := ⟨sectionFun ρ₀ F e m, hasPolyGrowth_sectionFun ρ₀ F e hF m⟩
      map_add' m m' := Subtype.ext (sectionFun_add ρ₀ F e m m')
      map_smul' r m := Subtype.ext (sectionFun_smul ρ₀ F e r m) }
  have hσ : Function.Surjective σ := fun f ↦ by
    obtain ⟨m, hm⟩ := exists_sectionFun_eq ρ₀ F e hF f.1 f.2
    exact ⟨m, Subtype.ext hm⟩
  have hx : x.1 ∈ Set.range (chart 0) := by
    rw [range_chart]
    exact x.2
  let ex := ((projectiveSpaceAn.{u} n).toLocallyRingedSpace.stalkFunctor x.1).map e.hom
  have key : ∀ z, extensionStalkToPi ρ₀ x.1 (ex (hSF.equiv z)) =
      polyGrowthStalkMap ρ₀ hC x (LinearMap.lTensor _ σ z) := by
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

omit [IsFinite ρ₀] [T2Space W] in
theorem module_finite_polyGrowth :
    letI := polyGrowthAlgebra ρ₀ hC
    Module.Finite (ringU₀ n) (polyGrowth ρ₀) := by
  letI := polyGrowthAlgebra ρ₀ hC
  obtain ⟨F, hF, ⟨e⟩⟩ := exists_algebraisation ρ₀ hC
  haveI : SheafOfModules.IsCoherent
      (R := (projectiveSpace.{u} n).obj.left.toLocallyRingedSpace.ringSheaf) F := hF
  haveI : F.IsQuasicoherent := Scheme.Modules.isQuasicoherent_of_isCoherent F
  haveI : F.IsFiniteType := hF.isFiniteType
  haveI := Scheme.Modules.module_finite_sections_of_isAffineOpen_of_isFiniteType F
    (isAffineOpen_U (n := n) (R := ULift.{u} ℂ) 0)
  let σ : Γ(F, stdU 0) →ₗ[ringU₀ n] polyGrowth ρ₀ :=
    { toFun m := ⟨sectionFun ρ₀ F e m, hasPolyGrowth_sectionFun ρ₀ F e hF m⟩
      map_add' m m' := Subtype.ext (sectionFun_add ρ₀ F e m m')
      map_smul' r m := Subtype.ext (sectionFun_smul ρ₀ F e r m) }
  refine Module.Finite.of_surjective σ fun f ↦ ?_
  obtain ⟨m, hm⟩ := exists_sectionFun_eq ρ₀ F e hF f.1 f.2
  exact ⟨m, Subtype.ext hm⟩

end Main

end
end ComplexAnalytic.ProjectiveCompletion
