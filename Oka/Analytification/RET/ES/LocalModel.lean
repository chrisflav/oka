/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.FullyFaithful
import Oka.Analytification.RET.Pullback
import Oka.AnalyticSpace.PullbackOpen

/-!
# Local algebraic models of analytic finite étale covers

Let `X` be a scheme locally of finite type over `ℂ` and `q : T ⟶ X^an` a morphism of complex
analytic spaces, typically a finite étale cover. For an open `V ⊆ X`, a local model of `q` over
`V` is a finite étale cover `Y ⟶ V` together with a morphism `e : Y^an ⟶ T` exhibiting `Y^an` as
the pullback of `q` along `V^an ⟶ X^an`.

Local models restrict to smaller opens, and by full faithfulness of the analytification on
finite étale covers, a local model over `V` and one over `V' ≤ V` are related by a unique
morphism `Y' ⟶ Y` over `V' ⟶ V` compatible with the maps to `T`; the resulting square is a
pullback. The map `e` identifies `Y^an` with the open subspace `q⁻¹(V^an)` of `T`.

## Main definitions

- `ComplexAnalytic.SchemeLFTℂ.restrictHomOfLE`: the inclusion `X|_{V'} ⟶ X|_V` for `V' ≤ V`.
- `ComplexAnalytic.LocalModel q V`: a local model of `q` over `V`.
- `ComplexAnalytic.LocalModel.restrict`: the restriction of a local model to a smaller open.
- `ComplexAnalytic.LocalModel.transition`: the morphism `Y' ⟶ Y` between local models over
  `V' ≤ V`.

## Main results

- `ComplexAnalytic.LocalModel.transition_ext`: uniqueness of morphisms between local models.
- `ComplexAnalytic.LocalModel.isPullback_transition`: the transition square is a pullback.
- `ComplexAnalytic.LocalModel.injective_e`, `ComplexAnalytic.LocalModel.mem_range_e`: `e` is
  injective with image `q⁻¹(V^an)`.
-/

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace ComplexAnalytic

open AnalyticSpace

noncomputable section

namespace SchemeLFTℂ

variable (X : SchemeLFTℂ.{u})

/-- The inclusion `X|_{V'} ⟶ X|_V` of open subschemes for `V' ≤ V`. -/
def restrictHomOfLE {V' V : X.obj.left.Opens} (h : V' ≤ V) : X.restrict V' ⟶ X.restrict V :=
  ObjectProperty.homMk (Over.homMk (X.obj.left.homOfLE h) (by
    change X.obj.left.homOfLE h ≫ V.ι ≫ X.obj.hom = V'.ι ≫ X.obj.hom
    rw [Scheme.homOfLE_ι_assoc]))

@[simp]
lemma restrictHomOfLE_hom_left {V' V : X.obj.left.Opens} (h : V' ≤ V) :
    (X.restrictHomOfLE h).hom.left = X.obj.left.homOfLE h :=
  rfl

@[reassoc (attr := simp)]
lemma restrictHomOfLE_restrictι {V' V : X.obj.left.Opens} (h : V' ≤ V) :
    X.restrictHomOfLE h ≫ X.restrictι V = X.restrictι V' := by
  ext1
  exact Over.OverMorphism.ext (Scheme.homOfLE_ι _ h)

@[simp]
lemma restrictHomOfLE_rfl (V : X.obj.left.Opens) : X.restrictHomOfLE le_rfl = 𝟙 (X.restrict V) := by
  ext1
  exact Over.OverMorphism.ext (Scheme.homOfLE_rfl _ _)

@[reassoc (attr := simp)]
lemma restrictHomOfLE_restrictHomOfLE {V'' V' V : X.obj.left.Opens} (h₁ : V'' ≤ V')
    (h₂ : V' ≤ V) :
    X.restrictHomOfLE h₁ ≫ X.restrictHomOfLE h₂ = X.restrictHomOfLE (h₁.trans h₂) := by
  ext1
  exact Over.OverMorphism.ext (Scheme.homOfLE_homOfLE _ h₁ h₂)

@[reassoc (attr := simp)]
lemma analytification_map_restrictHomOfLE_restrictι {V' V : X.obj.left.Opens} (h : V' ≤ V) :
    analytification.map (X.restrictHomOfLE h) ≫ analytification.map (X.restrictι V) =
      analytification.map (X.restrictι V') :=
  (analytification.map_comp _ _).symm.trans (congrArg _ (X.restrictHomOfLE_restrictι h))

instance {V : X.obj.left.Opens} : IsOpenImmersion (X.restrictι V).hom.left :=
  inferInstanceAs (IsOpenImmersion V.ι)

end SchemeLFTℂ

open SchemeLFTℂ

variable {X : SchemeLFTℂ.{u}} {T : AnalyticSpace.{u}} (q : T ⟶ analytification.obj X)

/-- **A local model of `q : T ⟶ X^an` over an open `V ⊆ X`**: a finite étale cover `Y ⟶ V` with a
morphism `e : Y^an ⟶ T` such that the square
```
Y^an ---e---> T
 |            |
V^an -------> X^an
```
is a pullback. -/
structure LocalModel (V : X.obj.left.Opens) where
  /-- The total space of the cover. -/
  Y : SchemeLFTℂ.{u}
  /-- The finite étale morphism `Y ⟶ V`. -/
  p : Y ⟶ X.restrict V
  /-- `Y ⟶ V` is finite étale. -/
  isFiniteEtale_p : SchemeLFTℂ.isFiniteEtale p
  /-- The map from the analytification of `Y` to `T`. -/
  e : analytification.obj Y ⟶ T
  /-- The analytified square is a pullback. -/
  isPullback : IsPullback e (analytification.map p) q
    (analytification.map (X.restrictι V))

/-- The pullback of `q` along `V^an ⟶ X^an`, presented as the open subspace `q⁻¹(V^an)`. -/
lemma isPullback_ofRestrict_preimage_restrictι (V : X.obj.left.Opens) :
    IsPullback (T.ofRestrict ((TopologicalSpace.Opens.map q.toLRSHom.base).obj
        (analytificationOpenImmersionPreimage (X.restrictι V))))
      (AnalyticSpace.restrictHom q (analytificationOpenImmersionPreimage (X.restrictι V)) ≫
        (analytificationOpenImmersionIso (X.restrictι V)).inv)
      q (analytification.map (X.restrictι V)) :=
  (AnalyticSpace.isPullback_ofRestrict q _).of_iso (Iso.refl _) (Iso.refl _)
    (analytificationOpenImmersionIso (X.restrictι V)).symm (Iso.refl _) (by simp) (by simp)
    (by simp) (by rw [Iso.symm_hom, Iso.refl_hom, Category.comp_id,
      ← analytificationOpenImmersionIso_hom_ofRestrict (X.restrictι V), Iso.inv_hom_id_assoc])

namespace LocalModel

variable {q}

/-- The finite étale cover of `V` underlying a local model. -/
def cover {V : X.obj.left.Opens} (M : LocalModel q V) : SchemeLFTℂ.FiniteEtaleOver (X.restrict V) :=
  MorphismProperty.Over.mk ⊤ M.p M.isFiniteEtale_p

instance {V : X.obj.left.Opens} (M : LocalModel q V) :
    AlgebraicGeometry.IsFinite M.p.hom.left :=
  M.isFiniteEtale_p.1

instance {V : X.obj.left.Opens} (M : LocalModel q V) : Etale M.p.hom.left :=
  M.isFiniteEtale_p.2

/-- The structure map of a base change of a finite étale cover of `X|_V` is finite étale. -/
lemma isFiniteEtale_fibreProdSnd {V' V : X.obj.left.Opens} (h : V' ≤ V) (M : LocalModel q V) :
    SchemeLFTℂ.isFiniteEtale (fibreProdSnd M.p (X.restrictHomOfLE h)) := by
  change AlgebraicGeometry.IsFinite (pullback.snd _ _) ∧ Etale (pullback.snd _ _)
  exact ⟨inferInstance, inferInstance⟩

/-- The base change of the cover of a local model along `V' ⟶ V`, as a finite étale cover of
`V'`. -/
def baseChange {V' V : X.obj.left.Opens} (h : V' ≤ V) (M : LocalModel q V) :
    SchemeLFTℂ.FiniteEtaleOver (X.restrict V') :=
  MorphismProperty.Over.mk ⊤ (fibreProdSnd M.p (X.restrictHomOfLE h))
    (isFiniteEtale_fibreProdSnd h M)

/-- The base change square of a local model, analytified and pasted with the defining square, is
a pullback. -/
lemma isPullback_baseChange {V' V : X.obj.left.Opens} (h : V' ≤ V) (M : LocalModel q V) :
    IsPullback (analytification.map (fibreProdFst M.p (X.restrictHomOfLE h)) ≫ M.e)
      (analytification.map (fibreProdSnd M.p (X.restrictHomOfLE h))) q
      (analytification.map (X.restrictι V')) := by
  have := (isPullback_analytification_map_fibreProd M.p
    (X.restrictHomOfLE h)).paste_horiz M.isPullback
  rwa [analytification_map_restrictHomOfLE_restrictι] at this

/-- **The restriction of a local model to a smaller open.** -/
def restrict {V' V : X.obj.left.Opens} (h : V' ≤ V) (M : LocalModel q V) : LocalModel q V' where
  Y := fibreProd M.p (X.restrictHomOfLE h)
  p := fibreProdSnd M.p (X.restrictHomOfLE h)
  isFiniteEtale_p := isFiniteEtale_fibreProdSnd h M
  e := analytification.map (fibreProdFst M.p (X.restrictHomOfLE h)) ≫ M.e
  isPullback := isPullback_baseChange h M

variable {V' V : X.obj.left.Opens} (h : V' ≤ V) (M' : LocalModel q V') (M : LocalModel q V)

/-- **Morphisms between local models are unique**: two morphisms `Y' ⟶ Y` over `V' ⟶ V` that
are compatible with the maps to `T` agree. -/
theorem transition_ext {g₁ g₂ : M'.Y ⟶ M.Y}
    (hg₁ : g₁ ≫ M.p = M'.p ≫ X.restrictHomOfLE h)
    (hg₂ : g₂ ≫ M.p = M'.p ≫ X.restrictHomOfLE h)
    (he₁ : analytification.map g₁ ≫ M.e = M'.e) (he₂ : analytification.map g₂ ≫ M.e = M'.e) :
    g₁ = g₂ := by
  haveI : FormallyUnramified M.p.hom.left := by
    haveI : Etale M.p.hom.left := M.isFiniteEtale_p.2
    infer_instance
  refine eq_of_analytification_map_eq M.p (hg₁.trans hg₂.symm) ?_
  refine M.isPullback.hom_ext (he₁.trans he₂.symm) ?_
  rw [← Functor.map_comp, ← Functor.map_comp, hg₁, hg₂]

/-- The map `Y'^an ⟶ Y^an` induced by the pullback property of `M`. -/
def transitionAn : analytification.obj M'.Y ⟶ analytification.obj M.Y :=
  M.isPullback.lift M'.e (analytification.map (M'.p ≫ X.restrictHomOfLE h)) (by
    rw [M'.isPullback.w, Functor.map_comp, Category.assoc,
      analytification_map_restrictHomOfLE_restrictι])

@[reassoc (attr := simp)]
lemma transitionAn_e : transitionAn h M' M ≫ M.e = M'.e :=
  M.isPullback.lift_fst _ _ _

@[reassoc]
lemma transitionAn_hom :
    transitionAn h M' M ≫ analytification.map M.p =
      analytification.map (M'.p ≫ X.restrictHomOfLE h) :=
  M.isPullback.lift_snd _ _ _

/-- The map `Y'^an ⟶ (Y ×_V V')^an` induced by the pullback property of the analytified fibre
product. -/
def comparisonAn :
    analytification.obj M'.Y ⟶ analytification.obj (fibreProd M.p (X.restrictHomOfLE h)) :=
  (isPullback_analytification_map_fibreProd M.p (X.restrictHomOfLE h)).lift
    (transitionAn h M' M) (analytification.map M'.p) (by
      rw [transitionAn_hom, Functor.map_comp])

@[reassoc (attr := simp)]
lemma comparisonAn_fst :
    comparisonAn h M' M ≫ analytification.map (fibreProdFst M.p (X.restrictHomOfLE h)) =
      transitionAn h M' M :=
  IsPullback.lift_fst _ _ _ _

@[reassoc (attr := simp)]
lemma comparisonAn_snd :
    comparisonAn h M' M ≫ analytification.map (fibreProdSnd M.p (X.restrictHomOfLE h)) =
      analytification.map M'.p :=
  IsPullback.lift_snd _ _ _ _

lemma comparisonAn_eq :
    comparisonAn h M' M = (M'.isPullback.isoIsPullback _ _ (isPullback_baseChange h M)).hom := by
  refine (isPullback_baseChange h M).hom_ext ?_ ?_
  · rw [IsPullback.isoIsPullback_hom_fst, comparisonAn_fst_assoc, transitionAn_e]
  · rw [IsPullback.isoIsPullback_hom_snd, comparisonAn_snd]

instance : IsIso (comparisonAn h M' M) := by
  rw [comparisonAn_eq]
  infer_instance

/-- The comparison map `Y'^an ⟶ (Y ×_V V')^an`, as a morphism of finite étale covers of `V'^an`. -/
def comparisonAnHom : (analytificationFiniteEtaleOver _).obj M'.cover ⟶
    (analytificationFiniteEtaleOver _).obj (baseChange h M) :=
  MorphismProperty.Over.homMk (comparisonAn h M' M) (comparisonAn_snd h M' M)

/-- The comparison map `Y' ⟶ Y ×_V V'`, as a morphism of finite étale covers of `V'`. -/
def comparison : M'.cover ⟶ baseChange h M :=
  (fullyFaithfulAnalytificationFiniteEtaleOver (X.restrict V')).preimage (comparisonAnHom h M' M)

/-- The comparison map `Y' ⟶ Y ×_V V'`, as a morphism of schemes. -/
def comparisonHom : M'.Y ⟶ fibreProd M.p (X.restrictHomOfLE h) :=
  (comparison h M' M).left

lemma analytification_map_comparisonHom :
    analytification.map (comparisonHom h M' M) = comparisonAn h M' M := by
  have := congrArg (fun (φ : (analytificationFiniteEtaleOver _).obj M'.cover ⟶
      (analytificationFiniteEtaleOver _).obj (baseChange h M)) ↦ φ.left)
    ((fullyFaithfulAnalytificationFiniteEtaleOver (X.restrict V')).map_preimage
      (comparisonAnHom h M' M))
  exact this

@[reassoc]
lemma comparisonHom_snd :
    comparisonHom h M' M ≫ fibreProdSnd M.p (X.restrictHomOfLE h) = M'.p :=
  MorphismProperty.Over.w (comparison h M' M)

instance : IsIso (comparison h M' M) := by
  haveI : IsIso ((analytificationFiniteEtaleOver (X.restrict V')).map (comparison h M' M)) := by
    refine FiniteEtaleOver.isIso_of_isIso_left _ ?_
    change IsIso (analytification.map (comparisonHom h M' M))
    rw [analytification_map_comparisonHom]
    infer_instance
  exact (fullyFaithfulAnalytificationFiniteEtaleOver (X.restrict V')).isIso_of_isIso_map _

lemma isIso_comparisonHom_hom_left : IsIso (comparisonHom h M' M).hom.left := by
  haveI : IsIso (comparisonHom h M' M) :=
    inferInstanceAs (IsIso ((MorphismProperty.Over.forget _ _ _ ⋙ Over.forget _).map
      (comparison h M' M)))
  exact inferInstanceAs (IsIso ((ObjectProperty.ι _ ⋙ Over.forget _).map (comparisonHom h M' M)))

/-- **The transition morphism `Y' ⟶ Y` between local models over `V' ≤ V`.** -/
def transition : M'.Y ⟶ M.Y :=
  comparisonHom h M' M ≫ fibreProdFst M.p (X.restrictHomOfLE h)

@[reassoc]
lemma transition_p : transition h M' M ≫ M.p = M'.p ≫ X.restrictHomOfLE h := by
  rw [transition, Category.assoc, fibreProd_condition, comparisonHom_snd_assoc]

@[reassoc (attr := simp)]
lemma analytification_map_transition_e : analytification.map (transition h M' M) ≫ M.e = M'.e := by
  rw [transition, Functor.map_comp, analytification_map_comparisonHom, Category.assoc,
    comparisonAn_fst_assoc, transitionAn_e]

/-- **The transition square is a pullback.** -/
theorem isPullback_transition :
    IsPullback (transition h M' M).hom.left M'.p.hom.left M.p.hom.left
      (X.restrictHomOfLE h).hom.left := by
  refine IsPullback.of_iso_pullback ⟨?_⟩
    (@asIso _ _ _ _ (comparisonHom h M' M).hom.left (isIso_comparisonHom_hom_left h M' M)) ?_ ?_
  · exact congrArg (fun φ ↦ φ.hom.left) (transition_p h M' M)
  · rfl
  · exact congrArg (fun φ ↦ φ.hom.left) (comparisonHom_snd h M' M)

omit M' in
@[simp]
lemma transition_self : transition le_rfl M M = 𝟙 M.Y :=
  transition_ext le_rfl M M (transition_p le_rfl M M) (by simp)
    (analytification_map_transition_e le_rfl M M) (by simp)

lemma transition_comp {V'' : X.obj.left.Opens} (h' : V'' ≤ V') (M'' : LocalModel q V'') :
    transition h' M'' M' ≫ transition h M' M = transition (h'.trans h) M'' M := by
  refine transition_ext (h'.trans h) M'' M ?_ (transition_p _ M'' M) ?_
    (analytification_map_transition_e _ M'' M)
  · rw [Category.assoc, transition_p, transition_p_assoc, restrictHomOfLE_restrictHomOfLE]
  · rw [Functor.map_comp, Category.assoc, analytification_map_transition_e,
      analytification_map_transition_e]

/-! ### The map `e` is an open embedding -/

omit M' in
/-- `e` identifies `Y^an` with the open subspace `q⁻¹(V^an)` of `T`. -/
lemma e_eq : M.e =
    (M.isPullback.isoIsPullback _ _ (isPullback_ofRestrict_preimage_restrictι q V)).hom ≫
      T.ofRestrict _ :=
  (IsPullback.isoIsPullback_hom_fst _ _ _ _).symm

omit M' in
/-- **`e` is injective on points.** -/
theorem injective_e : Function.Injective (M.e.toLRSHom.base : analytification.obj M.Y → T) := by
  rw [e_eq]
  exact Subtype.val_injective.comp (bijective_base_of_isIso _).1

omit M' in
/-- **The image of `e` contains every point over `V^an`.** -/
theorem mem_range_e (t : T)
    (ht : q.toLRSHom.base t ∈ Set.range (analytification.map (X.restrictι V)).toLRSHom.base) :
    t ∈ Set.range (M.e.toLRSHom.base : analytification.obj M.Y → T) := by
  rw [range_analytification_map] at ht
  obtain ⟨y, hy⟩ := (bijective_base_of_isIso (M.isPullback.isoIsPullback _ _
    (isPullback_ofRestrict_preimage_restrictι q V)).hom).2 ⟨t, ht⟩
  refine ⟨y, ?_⟩
  rw [e_eq]
  exact congrArg Subtype.val hy

end LocalModel

end

end ComplexAnalytic
