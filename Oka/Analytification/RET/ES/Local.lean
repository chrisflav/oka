/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.ES.LocalGlue
import Oka.AnalyticSpace.Glue

/-!
# Essential surjectivity of the analytification is Zariski-local

Let `X` be a scheme locally of finite type over `ℂ` and `W` a finite étale cover of `X^an`.
If every point of `X` has an open neighbourhood `V` such that `W` restricted to `V^an` is the
analytification of a finite étale cover of `V`, then `W` is the analytification of a finite étale
cover of `X`.

The local models glue to a finite étale cover `Y ⟶ X` (`Oka/Analytification/RET/ES/LocalGlue.lean`).
The maps `e_V : Y_V^an ⟶ W` glue to a morphism `Y^an ⟶ W` over `X^an`: on overlaps they agree on
points, since the cover by opens with local models is locally directed, and a morphism into a
local isomorphism over a fixed base is determined by its map on points. The glued morphism is a
bijective local isomorphism, hence an isomorphism.

## Main results

- `ComplexAnalytic.mem_essImage_of_forall_exists_localModel`: `W` is in the essential image if it
  has local models around every point (`ComplexAnalytic.mem_essImage_of_forall_exists_localModel'`
  for a finite étale morphism `q : T ⟶ X^an`).
- `ComplexAnalytic.mem_essImage_of_cover`: `W` is in the essential image if its restrictions to
  the members of an open cover are.
- `ComplexAnalytic.essSurj_of_forall_isAffine`: if the analytification is essentially surjective
  on finite étale covers of affine schemes, it is so for all schemes.
-/

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

universe u

namespace ComplexAnalytic

open AnalyticSpace SchemeLFTℂ

lemma AnalyticSpace.comp_toLRSHom_base_apply {A B C : AnalyticSpace.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (a : A) : (f ≫ g).toLRSHom.base a = g.toLRSHom.base (f.toLRSHom.base a) :=
  rfl

noncomputable section

namespace LocalModel

variable {X : SchemeLFTℂ.{u}} {T : AnalyticSpace.{u}} (q : T ⟶ analytification.obj X)
  (hq : ∀ x : X.obj.left, ∃ V : X.obj.left.Opens, x ∈ V ∧ Nonempty (LocalModel q V))

/-- The open subspace of `Y^an` over the chosen local model at `V`. -/
abbrev gluedOpens (V : (modelCover q hq).I₀) : (analytification.obj (glued q hq)).Opens :=
  analytificationOpenImmersionPreimage (gluedι q hq V)

/-- The map from the open subspace of `Y^an` over `V` to `T`. -/
def gluedPiece (V : (modelCover q hq).I₀) :
    (analytification.obj (glued q hq)).restrict (gluedOpens q hq V) ⟶ T :=
  (analytificationOpenImmersionIso (gluedι q hq V)).inv ≫ (model q hq V).e

lemma gluedPiece_comp (V : (modelCover q hq).I₀) :
    gluedPiece q hq V ≫ q = (analytification.obj (glued q hq)).ofRestrict (gluedOpens q hq V) ≫
      analytification.map (gluedHom q hq) := by
  rw [gluedPiece, Category.assoc, (model q hq V).isPullback.w, ← Iso.inv_hom_id_assoc
    (analytificationOpenImmersionIso (gluedι q hq V))
    ((analytification.obj (glued q hq)).ofRestrict (gluedOpens q hq V) ≫
      analytification.map (gluedHom q hq)), analytificationOpenImmersionIso_hom_ofRestrict_assoc,
    ← Functor.map_comp, ← Functor.map_comp, gluedι_gluedHom]

lemma mem_gluedOpens_iff (V : (modelCover q hq).I₀) (y : analytification.obj (glued q hq)) :
    y ∈ gluedOpens q hq V ↔
      (gluingData q hq).toBase ((analytificationπ (glued q hq)).left.base y) ∈ V.1 := by
  rw [mem_analytificationOpenImmersionPreimage_iff, range_gluedι]
  rfl

lemma mem_gluedOpens_iff' (V : (modelCover q hq).I₀) (y : analytification.obj (glued q hq)) :
    y ∈ gluedOpens q hq V ↔ (analytificationπ X).left.base
      ((analytification.map (gluedHom q hq)).toLRSHom.base y) ∈ V.1 := by
  rw [mem_gluedOpens_iff, analytificationπ_base_map_apply]
  rfl

lemma mem_range_iff (V : (modelCover q hq).I₀) (y : analytification.obj (glued q hq)) :
    y ∈ Set.range (analytification.map (gluedι q hq V)).toLRSHom.base ↔
      y ∈ gluedOpens q hq V := by
  rw [range_analytification_map]
  rfl

/-- The value of `gluedPiece` at a point in the image of a smaller local model. -/
lemma gluedPiece_apply {V' V : (modelCover q hq).I₀} (h : V' ≤ V)
    (s : (analytification.obj (glued q hq)).restrict (gluedOpens q hq V))
    (y : analytification.obj (model q hq V').Y)
    (hy : (analytification.map (gluedι q hq V')).toLRSHom.base y = s.1) :
    (gluedPiece q hq V).toLRSHom.base s = (model q hq V').e.toLRSHom.base y := by
  let y₀ := (analytification.map (transition h (model q hq V') (model q hq V))).toLRSHom.base y
  have hy₀ : (analytificationOpenImmersionIso (gluedι q hq V)).hom.toLRSHom.base y₀ = s := by
    apply Subtype.ext
    rw [← hy, ← transition_gluedι q hq h, Functor.map_comp,
      ← analytificationOpenImmersionIso_hom_ofRestrict (gluedι q hq V)]
    rfl
  have h₁ : (analytificationOpenImmersionIso (gluedι q hq V)).inv.toLRSHom.base
      ((analytificationOpenImmersionIso (gluedι q hq V)).hom.toLRSHom.base y₀) = y₀ :=
    congrArg (fun (φ : analytification.obj (model q hq V).Y ⟶ _) ↦ φ.toLRSHom.base y₀)
      (Iso.hom_inv_id (analytificationOpenImmersionIso (gluedι q hq V)))
  refine (congrArg (fun t ↦ (model q hq V).e.toLRSHom.base
    ((analytificationOpenImmersionIso (gluedι q hq V)).inv.toLRSHom.base t)) hy₀.symm).trans ?_
  refine (congrArg (model q hq V).e.toLRSHom.base h₁).trans ?_
  exact congrArg (fun φ ↦ φ.toLRSHom.base y) (analytification_map_transition_e _ _ _)

include hq in
lemma exists_le_mem_gluedOpens (V : (modelCover q hq).I₀) (V' : (modelCover q hq).I₀)
    (y : analytification.obj (glued q hq)) (hV : y ∈ gluedOpens q hq V)
    (hV' : y ∈ gluedOpens q hq V') :
    ∃ (V'' : (modelCover q hq).I₀) (_ : V'' ≤ V) (_ : V'' ≤ V'),
      y ∈ Set.range (analytification.map (gluedι q hq V'')).toLRSHom.base := by
  rw [mem_gluedOpens_iff] at hV hV'
  obtain ⟨V₀, hV₀, ⟨M⟩⟩ :=
    hq ((gluingData q hq).toBase ((analytificationπ (glued q hq)).left.base y))
  refine ⟨⟨V₀ ⊓ (V.1 ⊓ V'.1), ⟨M.restrict inf_le_left⟩⟩,
    show V₀ ⊓ (V.1 ⊓ V'.1) ≤ V.1 from inf_le_right.trans inf_le_left,
    show V₀ ⊓ (V.1 ⊓ V'.1) ≤ V'.1 from inf_le_right.trans inf_le_right, ?_⟩
  rw [mem_range_iff, mem_gluedOpens_iff]
  exact ⟨hV₀, hV, hV'⟩

include hq in
lemma exists_mem_gluedOpens (y : analytification.obj (glued q hq)) :
    ∃ V, y ∈ gluedOpens q hq V := by
  obtain ⟨V, hV, hM⟩ := hq ((gluingData q hq).toBase ((analytificationπ (glued q hq)).left.base y))
  exact ⟨⟨V, hM⟩, (mem_gluedOpens_iff q hq _ y).2 hV⟩

include hq in
lemma exists_mem_range (x : analytification.obj X) :
    ∃ V : (modelCover q hq).I₀,
      x ∈ Set.range (analytification.map (X.restrictι V.1)).toLRSHom.base := by
  obtain ⟨V, hV, hM⟩ := hq ((analytificationπ X).left.base x)
  exact ⟨⟨V, hM⟩, by rw [range_analytification_map_restrictι]; exact hV⟩

variable [IsLocalIso q]

lemma gluedPiece_compat (V V' : (modelCover q hq).I₀) :
    (analytification.obj (glued q hq)).restrictLE
        (inf_le_left : gluedOpens q hq V ⊓ gluedOpens q hq V' ≤ _) ≫ gluedPiece q hq V =
      (analytification.obj (glued q hq)).restrictLE
        (inf_le_right : gluedOpens q hq V ⊓ gluedOpens q hq V' ≤ _) ≫ gluedPiece q hq V' := by
  have hcomp : ∀ (V₁ : (modelCover q hq).I₀) (hle : gluedOpens q hq V ⊓ gluedOpens q hq V' ≤
      gluedOpens q hq V₁),
      ((analytification.obj (glued q hq)).restrictLE hle ≫ gluedPiece q hq V₁) ≫ q =
        (analytification.obj (glued q hq)).ofRestrict _ ≫ analytification.map (gluedHom q hq) :=
    fun V₁ hle ↦ by rw [Category.assoc, gluedPiece_comp, ← Category.assoc, restrictLE_fac]
  refine forgetToLocallyRingedSpace.map_injective
    (LocallyRingedSpace.hom_ext_of_comp_eq q.toLRSHom _ _ ?_ ?_)
  · ext z
    obtain ⟨V'', h, h', y, hy⟩ := exists_le_mem_gluedOpens q hq V V' z.1 z.2.1 z.2.2
    exact (gluedPiece_apply q hq h _ y (hy.trans (congrArg (fun φ ↦ φ.toLRSHom.base z)
      (restrictLE_fac _ _)).symm)).trans (gluedPiece_apply q hq h' _ y (hy.trans
      (congrArg (fun φ ↦ φ.toLRSHom.base z) (restrictLE_fac _ _)).symm)).symm
  · exact congrArg Hom.toLRSHom ((hcomp V _).trans (hcomp V' _).symm)

/-- **The glued morphism `Y^an ⟶ T`.** -/
def gluedMap : analytification.obj (glued q hq) ⟶ T :=
  glueMorphismsOfOpens (gluedOpens q hq) (exists_mem_gluedOpens q hq) (gluedPiece q hq)
    (gluedPiece_compat q hq)

@[reassoc]
lemma ofRestrict_gluedMap (V : (modelCover q hq).I₀) :
    (analytification.obj (glued q hq)).ofRestrict (gluedOpens q hq V) ≫ gluedMap q hq =
      gluedPiece q hq V :=
  ofRestrict_comp_glueMorphismsOfOpens _ _ _ _ V

@[reassoc]
lemma gluedMap_comp : gluedMap q hq ≫ q = analytification.map (gluedHom q hq) :=
  hom_ext_of_opens (gluedOpens q hq) (exists_mem_gluedOpens q hq) fun V ↦ by
    rw [ofRestrict_gluedMap_assoc, gluedPiece_comp]

lemma gluedMap_apply (V : (modelCover q hq).I₀) (y : analytification.obj (model q hq V).Y) :
    (gluedMap q hq).toLRSHom.base ((analytification.map (gluedι q hq V)).toLRSHom.base y) =
      (model q hq V).e.toLRSHom.base y := by
  have hy : (analytification.map (gluedι q hq V)).toLRSHom.base y ∈ gluedOpens q hq V :=
    (mem_range_iff q hq V _).1 ⟨y, rfl⟩
  rw [← gluedPiece_apply q hq le_rfl ⟨_, hy⟩ y rfl, ← ofRestrict_gluedMap]
  rfl

lemma bijective_gluedMap : Function.Bijective (gluedMap q hq).toLRSHom.base := by
  have hcomp (y : analytification.obj (glued q hq)) :
      q.toLRSHom.base ((gluedMap q hq).toLRSHom.base y) =
        (analytification.map (gluedHom q hq)).toLRSHom.base y := by
    rw [← comp_toLRSHom_base_apply, gluedMap_comp]
  have hmem (V : (modelCover q hq).I₀) (y : analytification.obj (glued q hq))
      (hy : (analytification.map (gluedHom q hq)).toLRSHom.base y ∈
        Set.range (analytification.map (X.restrictι V.1)).toLRSHom.base) :
      ∃ y', (analytification.map (gluedι q hq V)).toLRSHom.base y' = y := by
    rw [range_analytification_map_restrictι] at hy
    exact (mem_range_iff q hq V y).2 ((mem_gluedOpens_iff' q hq V y).2 hy)
  refine ⟨fun a b hab ↦ ?_, fun t ↦ ?_⟩
  · obtain ⟨V, hV⟩ := exists_mem_range q hq ((analytification.map (gluedHom q hq)).toLRSHom.base a)
    obtain ⟨a', rfl⟩ := hmem V a hV
    obtain ⟨b', rfl⟩ := hmem V b (by rwa [← hcomp, ← hab, hcomp])
    rw [gluedMap_apply, gluedMap_apply] at hab
    rw [(model q hq V).injective_e hab]
  · obtain ⟨V, hV⟩ := exists_mem_range q hq (q.toLRSHom.base t)
    obtain ⟨y, rfl⟩ := (model q hq V).mem_range_e t hV
    exact ⟨_, gluedMap_apply q hq V y⟩

end LocalModel

open LocalModel

variable {X : SchemeLFTℂ.{u}}

/-- **A finite étale morphism `q : T ⟶ X^an` with local algebraic models around every point of
`X` is the analytification of a finite étale cover of `X`.** -/
theorem mem_essImage_of_forall_exists_localModel' {T : AnalyticSpace.{u}}
    (q : T ⟶ analytification.obj X) [IsFiniteEtale q]
    (hq : ∀ x : X.obj.left, ∃ V : X.obj.left.Opens, x ∈ V ∧ Nonempty (LocalModel q V)) :
    (analytificationFiniteEtaleOver X).essImage
      (MorphismProperty.Over.mk ⊤ q (inferInstanceAs (IsFiniteEtale q))) := by
  haveI : IsFiniteEtale (analytification.map (gluedHom q hq)) :=
    isFiniteEtale_analytification_map _ (gluedCover q hq).prop
  haveI : IsLocalIso (gluedMap q hq ≫ q) := by
    rw [gluedMap_comp]
    infer_instance
  haveI : IsLocalIso (gluedMap q hq) := isLocalIso_of_comp _ q
  haveI : IsIso (gluedMap q hq) := isIso_of_isLocalIso_of_bijective _ (bijective_gluedMap q hq)
  let φ : (analytificationFiniteEtaleOver X).obj (gluedCover q hq) ⟶
      MorphismProperty.Over.mk ⊤ q (inferInstanceAs (IsFiniteEtale q)) :=
    MorphismProperty.Over.homMk (gluedMap q hq) (gluedMap_comp q hq)
  haveI : IsIso φ := FiniteEtaleOver.isIso_of_isIso_left φ (inferInstanceAs (IsIso (gluedMap q hq)))
  exact ⟨gluedCover q hq, ⟨asIso φ⟩⟩

/-- **A finite étale cover of `X^an` with local algebraic models around every point of `X` is
the analytification of a finite étale cover of `X`.** -/
theorem mem_essImage_of_forall_exists_localModel
    (W : AnalyticSpace.FiniteEtaleOver (analytification.obj X))
    (hW : ∀ x : X.obj.left, ∃ V : X.obj.left.Opens, x ∈ V ∧ Nonempty (LocalModel W.hom V)) :
    (analytificationFiniteEtaleOver X).essImage W :=
  @mem_essImage_of_forall_exists_localModel' _ _ W.hom W.prop hW

/-- **The restriction `W|_{V^an}`** of a finite étale cover `W` of `X^an` to the analytification
of an open `V ⊆ X`: the pullback of `W` along `V^an ⟶ X^an`. -/
def restrictFiniteEtaleOver (W : AnalyticSpace.FiniteEtaleOver (analytification.obj X))
    (V : X.obj.left.Opens) : AnalyticSpace.FiniteEtaleOver (analytification.obj (X.restrict V)) :=
  haveI : IsFiniteEtale W.hom := W.prop
  MorphismProperty.Over.mk ⊤ (pullback.snd W.hom (analytification.map (X.restrictι V)))
    (isFiniteEtale_pullback_snd_of_isFiniteEtale _ _)

/-- If `W|_{V^an}` is the analytification of a finite étale cover of `V`, then `W` has a local
model over `V`. -/
lemma nonempty_localModel_of_mem_essImage
    (W : AnalyticSpace.FiniteEtaleOver (analytification.obj X)) (V : X.obj.left.Opens)
    (h : (analytificationFiniteEtaleOver (X.restrict V)).essImage (restrictFiniteEtaleOver W V)) :
    Nonempty (LocalModel W.hom V) := by
  haveI : IsFiniteEtale W.hom := W.prop
  obtain ⟨Y, ⟨φ⟩⟩ := h
  refine ⟨⟨Y.left, Y.hom, Y.prop, φ.hom.left ≫ pullback.fst _ _, ?_⟩⟩
  refine (IsPullback.of_hasPullback W.hom (analytification.map (X.restrictι V))).of_iso
    ((MorphismProperty.Over.forget _ _ _ ⋙ Over.forget _).mapIso φ).symm (Iso.refl _)
    (Iso.refl _) (Iso.refl _) ?_ ?_ ((Category.comp_id _).trans (Category.id_comp _).symm)
    ((Category.comp_id _).trans (Category.id_comp _).symm)
  · change pullback.fst _ _ ≫ 𝟙 _ = φ.inv.left ≫ φ.hom.left ≫ pullback.fst _ _
    have hφ : φ.inv.left ≫ φ.hom.left = 𝟙 _ :=
      congrArg (fun ψ : restrictFiniteEtaleOver W V ⟶ _ ↦ ψ.left) φ.inv_hom_id
    rw [reassoc_of% hφ, Category.comp_id]
  · exact ((Category.comp_id _).trans (MorphismProperty.Over.w φ.inv).symm)

/-- **Essential surjectivity of the analytification on finite étale covers is Zariski-local**:
if `X` is covered by opens `U i` such that each restriction `W|_{(U i)^an}` is the
analytification of a finite étale cover of `U i`, then `W` is the analytification of a finite
étale cover of `X`. -/
theorem mem_essImage_of_cover (W : AnalyticSpace.FiniteEtaleOver (analytification.obj X))
    {ι : Type*} (U : ι → X.obj.left.Opens) (hU : ⨆ i, U i = ⊤)
    (h : ∀ i, (analytificationFiniteEtaleOver (X.restrict (U i))).essImage
      (restrictFiniteEtaleOver W (U i))) :
    (analytificationFiniteEtaleOver X).essImage W :=
  mem_essImage_of_forall_exists_localModel W fun x ↦ by
    have hx : x ∈ ⨆ i, U i := by
      rw [hU]
      trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 hx
    exact ⟨U i, hi, nonempty_localModel_of_mem_essImage W (U i) (h i)⟩

/-- **Essential surjectivity reduces to affine schemes**: if the analytification functor on finite
étale covers is essentially surjective for every affine scheme locally of finite type over `ℂ`,
it is so for every scheme locally of finite type over `ℂ`. -/
theorem essSurj_of_forall_isAffine
    (h : ∀ (V : SchemeLFTℂ.{u}) [IsAffine V.obj.left], (analytificationFiniteEtaleOver V).EssSurj)
    (X : SchemeLFTℂ.{u}) : (analytificationFiniteEtaleOver X).EssSurj :=
  ⟨fun W ↦ mem_essImage_of_forall_exists_localModel W fun x ↦ by
    obtain ⟨V, hV⟩ := exists_affineOpens_mem X.obj.left x
    haveI : IsAffine (X.restrict V.1).obj.left := V.2
    haveI := h (X.restrict V.1)
    exact ⟨V.1, hV, nonempty_localModel_of_mem_essImage W V.1
      (Functor.EssSurj.mem_essImage _ _)⟩⟩

end

end ComplexAnalytic
