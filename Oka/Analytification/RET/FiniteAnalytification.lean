/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.Topology.LocalAtTarget
import Oka.Analytification.RET.SpecBridge
import Oka.Analytification.SpecFiniteAnalytification
import Oka.Analytification.GAGA.ClosedImmersion

/-!
# The analytification of a finite morphism is finite

For a finite morphism `f : Y ⟶ X` of schemes locally of finite type over `ℂ`, the analytification
`f^an : Y^an ⟶ X^an` is a finite morphism of complex analytic spaces, i.e. closed with finite
fibres (`ComplexAnalytic.isFinite_analytification_map_of_isFinite`).

The affine case is `ComplexAnalytic.isFinite_analytificationMap_of_isFinite_specMap`, transported
along `ComplexAnalytic.analytification_map_specPresHom_eq`. The general case covers `X` by affine
opens `U`, over which `f` restricts to the finite morphism of affine schemes `f⁻¹ U ⟶ U`; finiteness
of analytic morphisms descends along such covers of the target
(`ComplexAnalytic.AnalyticSpace.isFinite_of_forall_isOpenEmbedding`).
-/

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace Topology

universe u

namespace ComplexAnalytic

open AnalyticSpace

noncomputable section

/-! ### Finiteness is local on the target -/

/-- A map `f` which, over the image of an open embedding `b`, is conjugate by open embeddings to a
closed map `g`, restricts to a closed map over the image of `b`. -/
theorem _root_.IsClosedMap.restrictPreimage_range_of_comp_eq {X Y X' Y' : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace X'] [TopologicalSpace Y']
    {f : X → Y} {g : X' → Y'} {a : X' → X} {b : Y' → Y} (ha : IsOpenEmbedding a)
    (hb : IsOpenEmbedding b) (hra : Set.range a = f ⁻¹' Set.range b) (hw : f ∘ a = b ∘ g)
    (hg : IsClosedMap g) : IsClosedMap ((Set.range b).restrictPreimage f) := by
  let hA : X' ≃ₜ (f ⁻¹' Set.range b) :=
    ha.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hra)
  let hB : Y' ≃ₜ Set.range b := hb.isEmbedding.toHomeomorph
  have e : (Set.range b).restrictPreimage f = hB ∘ g ∘ hA.symm := by
    funext z
    have hz : a (hA.symm z) = z.1 := congrArg Subtype.val (hA.apply_symm_apply z)
    apply Subtype.ext
    change f z.1 = b (g (hA.symm z))
    rw [← hz]
    exact congrFun hw _
  rw [e]
  exact hB.isClosedMap.comp (hg.comp hA.symm.isClosedMap)

/-- **Finiteness of analytic morphisms descends along open embeddings covering the target.**

If every point of `B` lies in the image of an open embedding `b : B' ⟶ B` such that, over that
image, `f` is conjugate to a finite morphism `g : A' ⟶ B'` by an open embedding `a : A' ⟶ A` onto
the preimage, then `f` is finite. -/
theorem AnalyticSpace.isFinite_of_forall_isOpenEmbedding {A B : AnalyticSpace.{u}} (f : A ⟶ B)
    (h : ∀ y : B, ∃ (A' B' : AnalyticSpace.{u}) (g : A' ⟶ B') (a : A' ⟶ A) (b : B' ⟶ B),
      AnalyticSpace.IsFinite g ∧ IsOpenEmbedding a.toLRSHom.base ∧
      IsOpenEmbedding b.toLRSHom.base ∧ y ∈ Set.range b.toLRSHom.base ∧
      Set.range a.toLRSHom.base = f.toLRSHom.base ⁻¹' Set.range b.toLRSHom.base ∧
      a ≫ f = g ≫ b) :
    AnalyticSpace.IsFinite f := by
  choose A' B' g a b hg ha hb hy hra hw using h
  have hw' : ∀ y, (f.toLRSHom.base : A → B) ∘ (a y).toLRSHom.base =
      (b y).toLRSHom.base ∘ (g y).toLRSHom.base := fun y ↦
    congrArg (fun φ ↦ (φ.toLRSHom.base : A' y → B)) (hw y)
  let U : B → B.Opens := fun y ↦ ⟨Set.range (b y).toLRSHom.base, (hb y).isOpen_range⟩
  have hU : IsOpenCover U :=
    IsOpenCover.mk (eq_top_iff.2 fun y _ ↦ Opens.mem_iSup.2 ⟨y, hy y⟩)
  refine ⟨?_, fun y ↦ ?_⟩
  · rw [hU.isClosedMap_iff_restrictPreimage]
    intro y
    exact IsClosedMap.restrictPreimage_range_of_comp_eq (ha y) (hb y) (hra y) (hw' y)
      (hg y).isClosedMap
  · obtain ⟨y', hy'⟩ := hy y
    haveI := (hg y).finite_fiber y'
    have hsub : (f.toLRSHom.base : A → B) ⁻¹' {y} ⊆
        (a y).toLRSHom.base '' ((g y).toLRSHom.base ⁻¹' {y'}) := by
      intro x hx
      have hx' : (f.toLRSHom.base : A → B) x = y := hx
      have hxr : x ∈ Set.range (a y).toLRSHom.base := by
        rw [hra y]
        exact ⟨y', hy'.trans hx'.symm⟩
      obtain ⟨x', rfl⟩ := hxr
      refine ⟨x', ?_, rfl⟩
      apply (hb y).injective
      exact (congrFun (hw' y) x').symm.trans (hx'.trans hy'.symm)
    exact ((Set.toFinite _).image _ |>.subset hsub).to_subtype

/-! ### The affine case -/

/-- **A finite morphism of affine schemes of finite type over `ℂ` analytifies to a finite
morphism.** -/
theorem isFinite_analytification_map_of_isFinite_of_isAffine {T S : SchemeLFTℂ.{u}}
    (φ : T ⟶ S) [IsAffine T.obj.left] [IsAffine S.obj.left]
    [AlgebraicGeometry.IsFinite φ.hom.left] :
    AnalyticSpace.IsFinite (analytification.map φ) := by
  obtain ⟨n, k, g, ⟨eS⟩⟩ := SchemeLFTℂ.exists_iso_specPresentation S
  obtain ⟨n', k', g', ⟨eT⟩⟩ := SchemeLFTℂ.exists_iso_specPresentation T
  obtain ⟨ψ, hψ⟩ := exists_specPresHom_eq (eT.hom ≫ φ ≫ eS.inv)
  have hφ : φ = eT.inv ≫ specPresHom ψ ≫ eS.hom := by simp [hψ]
  haveI : IsIso eT.hom.hom.left :=
    (Functor.map_isIso (locallyOfFiniteTypeℂ.ι ⋙ Over.forget _) eT.hom :)
  haveI : IsIso eS.inv.hom.left :=
    (Functor.map_isIso (locallyOfFiniteTypeℂ.ι ⋙ Over.forget _) eS.inv :)
  have hfin : AlgebraicGeometry.IsFinite (Spec.map (CommRingCat.ofHom ψ.toRingHom)) := by
    rw [← specPresHom_hom_left, hψ]
    change AlgebraicGeometry.IsFinite (eT.hom.hom.left ≫ φ.hom.left ≫ eS.inv.hom.left)
    infer_instance
  haveI := isFinite_analytificationMap_of_isFinite_specMap ψ hfin
  haveI := isFinite_of_isIso (analytification.map eT.inv)
  haveI := isFinite_of_isIso (analytification.map eS.hom)
  haveI := isFinite_of_isIso (analytificationSpecIso g').hom
  haveI := isFinite_of_isIso (analytificationSpecIso g).inv
  rw [hφ, Functor.map_comp, Functor.map_comp, analytification_map_specPresHom_eq]
  infer_instance

/-! ### The general case -/

/-- **The analytification of a finite morphism is finite.** -/
theorem isFinite_analytification_map_of_isFinite {Y X : SchemeLFTℂ.{u}} (f : Y ⟶ X)
    [AlgebraicGeometry.IsFinite f.hom.left] :
    AnalyticSpace.IsFinite (analytification.map f) := by
  refine AnalyticSpace.isFinite_of_forall_isOpenEmbedding _ fun p ↦ ?_
  obtain ⟨U, hU⟩ := exists_affineOpens_mem X.obj.left ((analytificationπLRS X).base p)
  let V : Y.obj.left.affineOpens := ⟨f.hom.left ⁻¹ᵁ (U : X.obj.left.Opens), U.2.preimage _⟩
  haveI : IsAffine (Y.restrict V).obj.left := V.2
  haveI : IsAffine (X.restrict U).obj.left := U.2
  haveI : AlgebraicGeometry.IsFinite (restrictHomLFT f U).hom.left := by
    change AlgebraicGeometry.IsFinite (f.hom.left ∣_ (U : X.obj.left.Opens))
    infer_instance
  refine ⟨_, _, analytification.map (restrictHomLFT f U),
    analytification.map (Y.restrictι V), analytification.map (X.restrictι U),
    isFinite_analytification_map_of_isFinite_of_isAffine _,
    isOpenEmbedding_analytification_map_restrictι _ _,
    isOpenEmbedding_analytification_map_restrictι _ _, ?_, ?_, ?_⟩
  · rw [range_analytification_map_restrictι]
    exact hU
  · rw [range_analytification_map_restrictι, range_analytification_map_restrictι]
    ext z
    change (analytificationπLRS Y).base z ∈ f.hom.left ⁻¹ᵁ (U : X.obj.left.Opens) ↔
      (analytificationπLRS X).base ((analytification.map f).toLRSHom.base z) ∈
        (U : X.obj.left.Opens)
    rw [analytificationπ_base_map]
    rfl
  · rw [← Functor.map_comp, ← Functor.map_comp, restrictHomLFT_restrictι]

end

end ComplexAnalytic
