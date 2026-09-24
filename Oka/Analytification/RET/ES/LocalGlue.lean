/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.AlgebraicGeometry.RelativeGluing
import Oka.Analytification.RET.ES.LocalModel

/-!
# Gluing local algebraic models

Let `X` be a scheme locally of finite type over `ℂ` and `q : T ⟶ X^an` a morphism of analytic
spaces. Suppose every point of `X` has an open neighbourhood over which `q` has a local model
(`ComplexAnalytic.LocalModel`). The opens admitting a local model form a basis of `X`, hence a
locally directed open cover, and the transition morphisms between the chosen local models form a
relative gluing datum over it (`AlgebraicGeometry.Scheme.Cover.RelativeGluingData`). The glued
scheme `Y` is finite étale over `X`, and each chosen local model is the preimage of its open.

## Main definitions

- `ComplexAnalytic.LocalModel.modelCover`: the open cover of `X` by the opens admitting a local
  model.
- `ComplexAnalytic.LocalModel.gluingData`: the relative gluing datum of the chosen local models.
- `ComplexAnalytic.LocalModel.glued`: the glued scheme, locally of finite type over `ℂ`.
- `ComplexAnalytic.LocalModel.gluedCover`: the glued finite étale cover of `X`.
- `ComplexAnalytic.LocalModel.gluedι`: the inclusion of a chosen local model into the glued
  scheme.
-/

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

universe u

namespace ComplexAnalytic

open AnalyticSpace SchemeLFTℂ

noncomputable section

variable {X : SchemeLFTℂ.{u}} {T : AnalyticSpace.{u}} (q : T ⟶ analytification.obj X)
  (hq : ∀ x : X.obj.left, ∃ V : X.obj.left.Opens, x ∈ V ∧ Nonempty (LocalModel q V))

namespace LocalModel

include hq

/-- **The opens admitting a local model form a basis.** -/
theorem isBasis_setOf_nonempty : Opens.IsBasis {V : X.obj.left.Opens | Nonempty (LocalModel q V)} :=
  Opens.isBasis_iff_nbhd.mpr fun {U x} hx ↦ by
    obtain ⟨V, hxV, ⟨M⟩⟩ := hq x
    exact ⟨V ⊓ U, ⟨M.restrict inf_le_left⟩, ⟨hxV, hx⟩, inf_le_right⟩

/-- **The open cover of `X` by the opens admitting a local model.** -/
@[simps I₀ X f]
def modelCover : X.obj.left.OpenCover where
  I₀ := {V : X.obj.left.Opens // Nonempty (LocalModel q V)}
  X V := V.1
  f V := V.1.ι
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, inferInstance⟩
    obtain ⟨V, hxV, hV⟩ := hq x
    exact ⟨⟨V, hV⟩, by simpa using hxV⟩

instance : Preorder (modelCover q hq).I₀ :=
  inferInstanceAs (Preorder {V : X.obj.left.Opens // Nonempty (LocalModel q V)})

lemma opensRange_modelCover_f (V : (modelCover q hq).I₀) :
    ((modelCover q hq).f V).opensRange = V.1 :=
  Scheme.Opens.opensRange_ι _

instance : Scheme.Cover.LocallyDirected (modelCover q hq) :=
  .ofIsBasisOpensRange (fun {i j} ↦ by
      rw [opensRange_modelCover_f, opensRange_modelCover_f]
      exact Iff.rfl) <| by
    convert isBasis_setOf_nonempty q hq
    ext V
    simp only [Set.mem_range, Set.mem_setOf_eq, opensRange_modelCover_f]
    exact ⟨fun ⟨y, hy⟩ ↦ hy ▸ y.2, fun h ↦ ⟨⟨V, h⟩, rfl⟩⟩

lemma modelCover_trans {V' V : (modelCover q hq).I₀} (h : V' ⟶ V) :
    (modelCover q hq).trans h = X.obj.left.homOfLE (leOfHom h) :=
  (cancel_mono V.1.ι).1 ((Scheme.Cover.trans_map _ h).trans (Scheme.homOfLE_ι _ _).symm)

/-- The chosen local model over a member of `modelCover q hq`. -/
def model (V : (modelCover q hq).I₀) : LocalModel q V.1 :=
  V.2.some

/-- The diagram of the chosen local models and their transition morphisms. -/
@[simps]
def gluingFunctor : (modelCover q hq).I₀ ⥤ Scheme.{u} where
  obj V := (model q hq V).Y.obj.left
  map {V' V} h := (transition (leOfHom h) (model q hq V') (model q hq V)).hom.left
  map_id V := congrArg (fun φ ↦ φ.hom.left) (transition_self (model q hq V))
  map_comp {V'' V' V} h' h := (congrArg (fun φ ↦ φ.hom.left) (transition_comp (leOfHom h)
    (model q hq V') (model q hq V) (leOfHom h') (model q hq V''))).symm

/-- The structure morphisms of the chosen local models, as a natural transformation. -/
@[simps]
def gluingNatTrans : gluingFunctor q hq ⟶ (modelCover q hq).functorOfLocallyDirected where
  app V := (model q hq V).p.hom.left
  naturality {V' V} h := by
    rw [Scheme.Cover.functorOfLocallyDirected_map, modelCover_trans]
    exact congrArg (fun φ ↦ φ.hom.left) (transition_p _ _ _)

/-- **The relative gluing datum of the chosen local models.** -/
def gluingData : (modelCover q hq).RelativeGluingData where
  functor := gluingFunctor q hq
  natTrans := gluingNatTrans q hq
  equifibered {V' V} h := by
    rw [gluingFunctor_map, gluingNatTrans_app, gluingNatTrans_app,
      Scheme.Cover.functorOfLocallyDirected_map, modelCover_trans]
    exact isPullback_transition _ _ _

instance : Quiver.IsThin (modelCover q hq).I₀ :=
  inferInstanceAs (Quiver.IsThin {V : X.obj.left.Opens // Nonempty (LocalModel q V)})

lemma isPullback_pullbackHom_toBase (V : (modelCover q hq).I₀) :
    IsPullback (colimit.ι (gluingData q hq).functor V) ((model q hq V).p.hom.left)
      (gluingData q hq).toBase ((modelCover q hq).f V) :=
  ((gluingData q hq).isPullback_natTrans_ι_toBase V).flip

lemma property_toBase (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P]
    (hP : ∀ V : (modelCover q hq).I₀, P (model q hq V).p.hom.left) :
    P (gluingData q hq).toBase := by
  refine IsZariskiLocalAtTarget.of_openCover (modelCover q hq) fun V ↦ ?_
  have := (P.cancel_left_of_respectsIso (isPullback_pullbackHom_toBase q hq V).isoPullback.inv
    ((model q hq V).p.hom.left)).mpr (hP V)
  have e := (isPullback_pullbackHom_toBase q hq V).isoPullback_inv_snd
  change P (pullback.snd _ _)
  exact e ▸ this

instance isFinite_toBase : AlgebraicGeometry.IsFinite (gluingData q hq).toBase :=
  property_toBase q hq @AlgebraicGeometry.IsFinite fun V ↦ (model q hq V).isFiniteEtale_p.1

instance etale_toBase : Etale (gluingData q hq).toBase :=
  property_toBase q hq @Etale fun V ↦ (model q hq V).isFiniteEtale_p.2

/-- **The glued scheme**, locally of finite type over `ℂ`. -/
def glued : SchemeLFTℂ.{u} :=
  ⟨Over.mk ((gluingData q hq).toBase ≫ X.obj.hom), by
    haveI : LocallyOfFiniteType X.obj.hom := X.property
    change LocallyOfFiniteType ((gluingData q hq).toBase ≫ X.obj.hom)
    infer_instance⟩

/-- The structure morphism of the glued scheme. -/
def gluedHom : glued q hq ⟶ X :=
  ObjectProperty.homMk (Over.homMk (gluingData q hq).toBase rfl)

@[simp]
lemma gluedHom_hom_left : (gluedHom q hq).hom.left = (gluingData q hq).toBase :=
  rfl

/-- **The glued finite étale cover of `X`.** -/
def gluedCover : SchemeLFTℂ.FiniteEtaleOver X :=
  MorphismProperty.Over.mk ⊤ (gluedHom q hq)
    ⟨isFinite_toBase q hq, etale_toBase q hq⟩

/-- The inclusion of a chosen local model into the glued scheme. -/
def gluedι (V : (modelCover q hq).I₀) : (model q hq V).Y ⟶ glued q hq :=
  ObjectProperty.homMk (Over.homMk (colimit.ι (gluingData q hq).functor V) (by
    change colimit.ι (gluingData q hq).functor V ≫ (gluingData q hq).toBase ≫ X.obj.hom = _
    rw [Scheme.Cover.RelativeGluingData.ι_toBase_assoc]
    exact Over.w (model q hq V).p.hom))

@[simp]
lemma gluedι_hom_left (V : (modelCover q hq).I₀) :
    (gluedι q hq V).hom.left = colimit.ι (gluingData q hq).functor V :=
  rfl

instance (V : (modelCover q hq).I₀) : IsOpenImmersion (gluedι q hq V).hom.left :=
  inferInstanceAs (IsOpenImmersion (colimit.ι (gluingData q hq).functor V))

@[reassoc (attr := simp)]
lemma gluedι_gluedHom (V : (modelCover q hq).I₀) :
    gluedι q hq V ≫ gluedHom q hq = (model q hq V).p ≫ X.restrictι V.1 := by
  ext1
  exact Over.OverMorphism.ext (Scheme.Cover.RelativeGluingData.ι_toBase (gluingData q hq) V)

@[reassoc (attr := simp)]
lemma transition_gluedι {V' V : (modelCover q hq).I₀} (h : V' ≤ V) :
    transition h (model q hq V') (model q hq V) ≫ gluedι q hq V = gluedι q hq V' := by
  ext1
  exact Over.OverMorphism.ext (colimit.w (gluingData q hq).functor (homOfLE h))

lemma range_gluedι (V : (modelCover q hq).I₀) :
    Set.range (gluedι q hq V).hom.left.base = (gluingData q hq).toBase ⁻¹' (V.1 : Set _) := by
  have := (gluingData q hq).preimage_toBase_eq_range_ι V
  exact this.symm.trans (congrArg ((gluingData q hq).toBase ⁻¹' ·) (Scheme.Opens.range_ι V.1))

end LocalModel

end

end ComplexAnalytic
