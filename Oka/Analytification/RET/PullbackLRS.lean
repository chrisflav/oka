/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Oka.Geometry.RingedSpace.PresheafedSpace.Gluing

/-!
# Fibre products of schemes are fibre products of locally ringed spaces

The forgetful functor from schemes to locally ringed spaces preserves pullbacks.

For affine schemes this holds because `Spec` is a right adjoint on locally ringed spaces. In
general, given morphisms `u : T ⟶ X` and `v : T ⟶ Y` of locally ringed spaces over `S`, cover
`T` by the opens `u⁻¹ X' ∩ v⁻¹ Y'` for affine opens `X'` and `Y'` of `X` and `Y` lying over an
affine open `S'` of `S`. Over such an open, `u` and `v` factor through `X'` and `Y'`, and hence
through the open subscheme `X' ×_{S'} Y'` of `X ×_S Y`, by the affine case. These factorisations
glue, and they are unique by the same argument.

## Main results

- `AlgebraicGeometry.isPullback_forgetToLocallyRingedSpace`: the square of a fibre product of
  schemes is a pullback square of locally ringed spaces.
-/

open CategoryTheory Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The composite `AffineScheme ⥤ Scheme ⥤ LocallyRingedSpace` preserves limits. -/
instance AffineScheme.preservesLimits_forgetToScheme_forgetToLocallyRingedSpace :
    PreservesLimits (AffineScheme.forgetToScheme.{u} ⋙ Scheme.forgetToLocallyRingedSpace) := by
  apply +allowSynthFailures @preservesLimits_of_natIso _ _ _ _ _ _
    (Functor.isoWhiskerRight AffineScheme.equivCommRingCat.unitIso
      (AffineScheme.forgetToScheme ⋙ Scheme.forgetToLocallyRingedSpace)).symm
  change PreservesLimits (AffineScheme.equivCommRingCat.functor ⋙ Spec.toLocallyRingedSpace)
  haveI : Spec.toLocallyRingedSpace.{u}.IsRightAdjoint :=
    ΓSpec.locallyRingedSpaceAdjunction.isRightAdjoint
  infer_instance

/-- **Pullbacks of affine schemes are pullbacks of locally ringed spaces.** -/
instance preservesLimit_cospan_forgetToLocallyRingedSpace_of_isAffine {X Y S : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) [IsAffine X] [IsAffine Y] [IsAffine S] :
    PreservesLimit (cospan f g) Scheme.forgetToLocallyRingedSpace := by
  let f' := AffineScheme.ofHom f
  let g' := AffineScheme.ofHom g
  let e : cospan f' g' ⋙ AffineScheme.forgetToScheme ≅ cospan f g :=
    cospanCompIso _ _ _ ≪≫ cospanExt (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp [f', AffineScheme.ofHom]) (by simp [g', AffineScheme.ofHom])
  suffices PreservesLimit (cospan f' g' ⋙ AffineScheme.forgetToScheme)
      Scheme.forgetToLocallyRingedSpace from preservesLimit_of_iso_diagram _ e
  have hc := isLimitOfPreserves AffineScheme.forgetToScheme (limit.isLimit (cospan f' g'))
  refine preservesLimit_of_preserves_limit_cone hc ?_
  exact isLimitOfPreserves (AffineScheme.forgetToScheme ⋙ Scheme.forgetToLocallyRingedSpace)
    (limit.isLimit (cospan f' g'))

/-- Two morphisms of locally ringed spaces agreeing on the members of an open cover are equal. -/
theorem LocallyRingedSpace.hom_ext_of_forall_ofRestrict {T Z : LocallyRingedSpace.{u}}
    {ι : Type u} (U : ι → Opens T) (hU : ∀ x : T, ∃ i, x ∈ U i) {φ ψ : T ⟶ Z}
    (h : ∀ i, T.ofRestrict (U i).isOpenEmbedding ≫ φ = T.ofRestrict (U i).isOpenEmbedding ≫ ψ) :
    φ = ψ :=
  (LocallyRingedSpace.existsUnique_glueMorphisms_of_opens U hU
    (fun i ↦ T.ofRestrict (U i).isOpenEmbedding ≫ φ)
    fun i j ↦ by rw [LocallyRingedSpace.restrictLE_fac_assoc,
      LocallyRingedSpace.restrictLE_fac_assoc]).unique (fun _ ↦ rfl) fun i ↦ (h i).symm

namespace Scheme.Pullback

variable {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}

section Chart

variable {S' : S.Opens} {X' : X.Opens} {Y' : Y.Opens} (hX : X' ≤ f ⁻¹ᵁ S') (hY : Y' ≤ g ⁻¹ᵁ S')

/-- The inclusion of the open subscheme `X' ×_{S'} Y'` into `X ×_S Y`, for opens `X' ⊆ f⁻¹ S'`
and `Y' ⊆ g⁻¹ S'`. -/
noncomputable def chartι :
    pullback (f.resLE S' X' hX) (g.resLE S' Y' hY) ⟶ pullback f g :=
  pullback.map _ _ f g X'.ι Y'.ι S'.ι (Scheme.Hom.resLE_comp_ι _ _) (Scheme.Hom.resLE_comp_ι _ _)

@[reassoc (attr := simp)]
lemma chartι_fst : chartι hX hY ≫ pullback.fst f g = pullback.fst _ _ ≫ X'.ι :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma chartι_snd : chartι hX hY ≫ pullback.snd f g = pullback.snd _ _ ≫ Y'.ι :=
  pullback.lift_snd _ _ _

instance : IsOpenImmersion (chartι hX hY) := by
  dsimp only [chartι]
  infer_instance

lemma range_chartι :
    Set.range (chartι hX hY).base =
      (pullback.fst f g).base ⁻¹' X' ∩ (pullback.snd f g).base ⁻¹' Y' := by
  rw [chartι, Scheme.Pullback.range_map, Scheme.Opens.range_ι, Scheme.Opens.range_ι]

variable (hS' : IsAffineOpen S') (hX' : IsAffineOpen X') (hY' : IsAffineOpen Y')
include hX hY hS' hX' hY'

/-- The affine chart is a pullback of locally ringed spaces. -/
lemma isPullback_chart :
    IsPullback (pullback.fst (f.resLE S' X' hX) (g.resLE S' Y' hY)).toLRSHom
      (pullback.snd (f.resLE S' X' hX) (g.resLE S' Y' hY)).toLRSHom
      (f.resLE S' X' hX).toLRSHom (g.resLE S' Y' hY).toLRSHom := by
  haveI : IsAffine S' := hS'
  haveI : IsAffine X' := hX'
  haveI : IsAffine Y' := hY'
  exact (IsPullback.of_hasPullback _ _).map Scheme.forgetToLocallyRingedSpace

/-- **Local existence**: morphisms of locally ringed spaces into `X'` and `Y'` which agree over
`S` factor through `X ×_S Y`. -/
lemma exists_lift_of_range_subset {T : LocallyRingedSpace.{u}} (u : T ⟶ X.toLocallyRingedSpace)
    (v : T ⟶ Y.toLocallyRingedSpace) (h : u ≫ f.toLRSHom = v ≫ g.toLRSHom)
    (hu : Set.range u.base ⊆ X') (hv : Set.range v.base ⊆ Y') :
    ∃ w : T ⟶ (pullback f g).toLocallyRingedSpace,
      w ≫ (pullback.fst f g).toLRSHom = u ∧ w ≫ (pullback.snd f g).toLRSHom = v := by
  haveI : LocallyRingedSpace.IsOpenImmersion X'.ι.toLRSHom := (inferInstance : IsOpenImmersion _)
  haveI : LocallyRingedSpace.IsOpenImmersion Y'.ι.toLRSHom := (inferInstance : IsOpenImmersion _)
  haveI : LocallyRingedSpace.IsOpenImmersion S'.ι.toLRSHom := (inferInstance : IsOpenImmersion _)
  let u' := LocallyRingedSpace.IsOpenImmersion.lift X'.ι.toLRSHom u
    (by change _ ⊆ Set.range X'.ι.base; rwa [Scheme.Opens.range_ι])
  let v' := LocallyRingedSpace.IsOpenImmersion.lift Y'.ι.toLRSHom v
    (by change _ ⊆ Set.range Y'.ι.base; rwa [Scheme.Opens.range_ι])
  have hu' : u' ≫ X'.ι.toLRSHom = u := LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ _
  have hv' : v' ≫ Y'.ι.toLRSHom = v := LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ _
  have hc : u' ≫ (f.resLE S' X' hX).toLRSHom = v' ≫ (g.resLE S' Y' hY).toLRSHom := by
    rw [← cancel_mono S'.ι.toLRSHom, Category.assoc, Category.assoc, ← Scheme.Hom.comp_toLRSHom,
      ← Scheme.Hom.comp_toLRSHom, Scheme.Hom.resLE_comp_ι, Scheme.Hom.resLE_comp_ι,
      Scheme.Hom.comp_toLRSHom, Scheme.Hom.comp_toLRSHom, reassoc_of% hu', reassoc_of% hv', h]
  have hP := isPullback_chart hX hY hS' hX' hY'
  refine ⟨hP.lift u' v' hc ≫ (chartι hX hY).toLRSHom, ?_, ?_⟩
  · rw [Category.assoc, ← Scheme.Hom.comp_toLRSHom, chartι_fst, Scheme.Hom.comp_toLRSHom,
      hP.lift_fst_assoc, hu']
  · rw [Category.assoc, ← Scheme.Hom.comp_toLRSHom, chartι_snd, Scheme.Hom.comp_toLRSHom,
      hP.lift_snd_assoc, hv']

/-- **Local uniqueness**: morphisms into `X ×_S Y` with the same projections, which land in
`X'` and `Y'`, are equal. -/
lemma eq_of_range_subset {T : LocallyRingedSpace.{u}}
    {w₁ w₂ : T ⟶ (pullback f g).toLocallyRingedSpace}
    (h₁ : w₁ ≫ (pullback.fst f g).toLRSHom = w₂ ≫ (pullback.fst f g).toLRSHom)
    (h₂ : w₁ ≫ (pullback.snd f g).toLRSHom = w₂ ≫ (pullback.snd f g).toLRSHom)
    (hu : Set.range (w₁ ≫ (pullback.fst f g).toLRSHom).base ⊆ X')
    (hv : Set.range (w₁ ≫ (pullback.snd f g).toLRSHom).base ⊆ Y') : w₁ = w₂ := by
  haveI : LocallyRingedSpace.IsOpenImmersion X'.ι.toLRSHom := (inferInstance : IsOpenImmersion _)
  haveI : LocallyRingedSpace.IsOpenImmersion Y'.ι.toLRSHom := (inferInstance : IsOpenImmersion _)
  haveI : LocallyRingedSpace.IsOpenImmersion (chartι hX hY).toLRSHom :=
    (inferInstance : IsOpenImmersion _)
  have hr (w : T ⟶ (pullback f g).toLocallyRingedSpace)
      (hw₁ : Set.range (w ≫ (pullback.fst f g).toLRSHom).base ⊆ X')
      (hw₂ : Set.range (w ≫ (pullback.snd f g).toLRSHom).base ⊆ Y') :
      Set.range w.base ⊆ Set.range (chartι hX hY).toLRSHom.base := by
    rintro _ ⟨t, rfl⟩
    change _ ∈ Set.range (chartι hX hY).base
    rw [range_chartι]
    exact ⟨hw₁ ⟨t, rfl⟩, hw₂ ⟨t, rfl⟩⟩
  let l₁ := LocallyRingedSpace.IsOpenImmersion.lift _ w₁ (hr w₁ hu hv)
  let l₂ := LocallyRingedSpace.IsOpenImmersion.lift _ w₂ (hr w₂ (h₁ ▸ hu) (h₂ ▸ hv))
  have hl₁ : l₁ ≫ (chartι hX hY).toLRSHom = w₁ := LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ _
  have hl₂ : l₂ ≫ (chartι hX hY).toLRSHom = w₂ := LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ _
  have hl : l₁ = l₂ := by
    refine (isPullback_chart hX hY hS' hX' hY').hom_ext ?_ ?_
    · rw [← cancel_mono X'.ι.toLRSHom, Category.assoc, Category.assoc, ← Scheme.Hom.comp_toLRSHom,
        ← chartι_fst hX hY, Scheme.Hom.comp_toLRSHom, reassoc_of% hl₁, reassoc_of% hl₂, h₁]
    · rw [← cancel_mono Y'.ι.toLRSHom, Category.assoc, Category.assoc, ← Scheme.Hom.comp_toLRSHom,
        ← chartι_snd hX hY, Scheme.Hom.comp_toLRSHom, reassoc_of% hl₁, reassoc_of% hl₂, h₂]
  rw [← hl₁, ← hl₂, hl]

end Chart
variable (f g)

/-- Every pair of points over the same point of `S` lies in an affine chart. -/
lemma exists_chart (x : X) (y : Y) (h : f.base x = g.base y) :
    ∃ (S' : S.Opens) (X' : X.Opens) (Y' : Y.Opens), X' ≤ f ⁻¹ᵁ S' ∧ Y' ≤ g ⁻¹ᵁ S' ∧
      IsAffineOpen S' ∧ IsAffineOpen X' ∧ IsAffineOpen Y' ∧ x ∈ X' ∧ y ∈ Y' := by
  obtain ⟨_, ⟨S', hS', rfl⟩, hxS, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f.base x)) isOpen_univ
  obtain ⟨X', hX', hxX', hXS⟩ := (Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens)
    (show x ∈ f ⁻¹ᵁ S' from hxS)
  obtain ⟨Y', hY', hyY', hYS⟩ := (Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens)
    (show y ∈ g ⁻¹ᵁ S' by change g.base y ∈ S'; rw [← h]; exact hxS)
  exact ⟨S', X', Y', hXS, hYS, hS', hX', hY', hxX', hyY'⟩

variable {f g}

lemma pullback_condition_toLRSHom :
    (pullback.fst f g).toLRSHom ≫ f.toLRSHom = (pullback.snd f g).toLRSHom ≫ g.toLRSHom := by
  rw [← Scheme.Hom.comp_toLRSHom, ← Scheme.Hom.comp_toLRSHom, pullback.condition]

/-- **Uniqueness**: morphisms of locally ringed spaces into `X ×_S Y` with the same projections
are equal. -/
theorem hom_ext_toLocallyRingedSpace {T : LocallyRingedSpace.{u}}
    {w₁ w₂ : T ⟶ (pullback f g).toLocallyRingedSpace}
    (h₁ : w₁ ≫ (pullback.fst f g).toLRSHom = w₂ ≫ (pullback.fst f g).toLRSHom)
    (h₂ : w₁ ≫ (pullback.snd f g).toLRSHom = w₂ ≫ (pullback.snd f g).toLRSHom) : w₁ = w₂ := by
  let u := w₁ ≫ (pullback.fst f g).toLRSHom
  let v := w₁ ≫ (pullback.snd f g).toLRSHom
  have huv : u ≫ f.toLRSHom = v ≫ g.toLRSHom := by
    simp only [u, v, Category.assoc, pullback_condition_toLRSHom]
  choose S' X' Y' hX hY hS' hX' hY' hx hy using fun t : T ↦ exists_chart f g (u.base t) (v.base t)
    (congrArg (fun φ : T ⟶ S.toLocallyRingedSpace ↦ φ.base t) huv)
  let V : T → TopologicalSpace.Opens T := fun t ↦
    (TopologicalSpace.Opens.map u.base).obj (X' t) ⊓ (TopologicalSpace.Opens.map v.base).obj (Y' t)
  refine LocallyRingedSpace.hom_ext_of_forall_ofRestrict V (fun t ↦ ⟨t, hx t, hy t⟩) fun t ↦ ?_
  refine eq_of_range_subset (hX t) (hY t) (hS' t) (hX' t) (hY' t)
    (by rw [Category.assoc, Category.assoc, h₁]) (by rw [Category.assoc, Category.assoc, h₂]) ?_ ?_
  · rintro _ ⟨s, rfl⟩
    exact s.2.1
  · rintro _ ⟨s, rfl⟩
    exact s.2.2
/-- **Existence**: morphisms of locally ringed spaces into `X` and `Y` which agree over `S`
factor through `X ×_S Y`. -/
theorem exists_lift_toLocallyRingedSpace {T : LocallyRingedSpace.{u}}
    (u : T ⟶ X.toLocallyRingedSpace) (v : T ⟶ Y.toLocallyRingedSpace)
    (h : u ≫ f.toLRSHom = v ≫ g.toLRSHom) :
    ∃ w : T ⟶ (pullback f g).toLocallyRingedSpace,
      w ≫ (pullback.fst f g).toLRSHom = u ∧ w ≫ (pullback.snd f g).toLRSHom = v := by
  choose S' X' Y' hX hY hS' hX' hY' hx hy using fun t : T ↦ exists_chart f g (u.base t) (v.base t)
    (congrArg (fun φ : T ⟶ S.toLocallyRingedSpace ↦ φ.base t) h)
  let V : T → TopologicalSpace.Opens T := fun t ↦
    (TopologicalSpace.Opens.map u.base).obj (X' t) ⊓ (TopologicalSpace.Opens.map v.base).obj (Y' t)
  have hV : ∀ t : T, ∃ s, t ∈ V s := fun t ↦ ⟨t, hx t, hy t⟩
  let ι (t : T) := T.ofRestrict (V t).isOpenEmbedding
  choose w hw₁ hw₂ using fun t : T ↦ exists_lift_of_range_subset (hX t) (hY t) (hS' t) (hX' t)
    (hY' t) (ι t ≫ u) (ι t ≫ v) (by rw [Category.assoc, Category.assoc, h])
    (by rintro _ ⟨s, rfl⟩; exact s.2.1) (by rintro _ ⟨s, rfl⟩; exact s.2.2)
  obtain ⟨φ, hφ, -⟩ := LocallyRingedSpace.existsUnique_glueMorphisms_of_opens V hV w
    fun i j ↦ hom_ext_toLocallyRingedSpace
      (by rw [Category.assoc, Category.assoc, hw₁, hw₁, LocallyRingedSpace.restrictLE_fac_assoc,
        LocallyRingedSpace.restrictLE_fac_assoc])
      (by rw [Category.assoc, Category.assoc, hw₂, hw₂, LocallyRingedSpace.restrictLE_fac_assoc,
        LocallyRingedSpace.restrictLE_fac_assoc])
  refine ⟨φ, LocallyRingedSpace.hom_ext_of_forall_ofRestrict V hV fun t ↦ ?_,
    LocallyRingedSpace.hom_ext_of_forall_ofRestrict V hV fun t ↦ ?_⟩
  · rw [reassoc_of% hφ t, hw₁]
  · rw [reassoc_of% hφ t, hw₂]

end Scheme.Pullback

open Scheme.Pullback in
/-- **A fibre product of schemes is a fibre product of locally ringed spaces.** -/
theorem isPullback_forgetToLocallyRingedSpace {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) :
    IsPullback (pullback.fst f g).toLRSHom (pullback.snd f g).toLRSHom f.toLRSHom g.toLRSHom :=
  IsPullback.of_isLimit (PullbackCone.IsLimit.mk pullback_condition_toLRSHom
    (fun s ↦ (exists_lift_toLocallyRingedSpace s.fst s.snd s.condition).choose)
    (fun s ↦ (exists_lift_toLocallyRingedSpace s.fst s.snd s.condition).choose_spec.1)
    (fun s ↦ (exists_lift_toLocallyRingedSpace s.fst s.snd s.condition).choose_spec.2)
    fun s _ h₁ h₂ ↦ hom_ext_toLocallyRingedSpace
      (h₁.trans (exists_lift_toLocallyRingedSpace s.fst s.snd s.condition).choose_spec.1.symm)
      (h₂.trans (exists_lift_toLocallyRingedSpace s.fst s.snd s.condition).choose_spec.2.symm))

/-- **The forgetful functor from schemes to locally ringed spaces preserves pullbacks.** -/
instance preservesLimit_cospan_forgetToLocallyRingedSpace {X Y S : Scheme.{u}} (f : X ⟶ S)
    (g : Y ⟶ S) : PreservesLimit (cospan f g) Scheme.forgetToLocallyRingedSpace :=
  preservesLimit_of_preserves_limit_cone (pullbackIsPullback f g)
    ((isLimitMapConePullbackConeEquiv _ pullback.condition).symm
      (isPullback_forgetToLocallyRingedSpace f g).isLimit)

/-- **The forgetful functor from schemes to locally ringed spaces preserves pullbacks.** -/
instance preservesLimitsOfShape_walkingCospan_forgetToLocallyRingedSpace :
    PreservesLimitsOfShape WalkingCospan Scheme.forgetToLocallyRingedSpace.{u} where
  preservesLimit {K} := preservesLimit_of_iso_diagram _ (diagramIsoCospan K).symm

end AlgebraicGeometry
