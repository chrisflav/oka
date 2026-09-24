/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Oka.Analytification.RET.ClosedPoints
import Oka.Analytification.RET.PullbackLRS
import Oka.AnalyticSpace.PullbackReduction

/-!
# Fibre products of schemes locally of finite type over `ℂ`

For morphisms `a : A ⟶ X` and `b : B ⟶ X` of schemes locally of finite type over `ℂ`, the fibre
product `A ×_X B` of the underlying schemes is again locally of finite type over `ℂ`. Its closed
points are the pairs of closed points of `A` and `B` with the same image in `X`: a closed point
of `A ×_X B` is determined by its two projections, since closed points are `ℂ`-points, and every
pair of closed points over the same point of `X` is the image of a closed point.

Since `A ×_X B` is also a fibre product of locally ringed spaces
(`AlgebraicGeometry.isPullback_forgetToLocallyRingedSpace`), the universal property of the
analytification shows that `(A ×_X B)^an` is the fibre product `A^an ×_{X^an} B^an`.

## Main definitions

- `ComplexAnalytic.SchemeLFTℂ.fibreProd a b`: the fibre product `A ×_X B`.
- `ComplexAnalytic.SchemeLFTℂ.fibreProdFst`, `ComplexAnalytic.SchemeLFTℂ.fibreProdSnd`: its
  projections.
- `ComplexAnalytic.analytificationFibreProdIso a b`: the isomorphism
  `(A ×_X B)^an ≅ A^an ×_{X^an} B^an`.

## Main results

- `ComplexAnalytic.SchemeLFTℂ.fibreProd_ext_of_isClosed`: closed points of `A ×_X B` with the
  same projections are equal.
- `ComplexAnalytic.SchemeLFTℂ.exists_isClosed_fibreProd`: a pair of closed points of `A` and `B`
  over the same point of `X` is the image of a closed point of `A ×_X B`.
- `ComplexAnalytic.isPullback_analytification_map_fibreProd`: the analytification of the fibre
  product square is a pullback square.
-/

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace ComplexAnalytic

namespace SchemeLFTℂ

/-- A morphism of schemes locally of finite type over `ℂ` is locally of finite type. -/
instance locallyOfFiniteType_hom_left {Y X : SchemeLFTℂ.{u}} (f : Y ⟶ X) :
    LocallyOfFiniteType f.hom.left := by
  haveI : LocallyOfFiniteType X.obj.hom := X.property
  haveI : LocallyOfFiniteType (f.hom.left ≫ X.obj.hom) := by
    rw [Over.w f.hom]
    exact Y.property
  exact locallyOfFiniteType_of_comp f.hom.left X.obj.hom

variable {A B X : SchemeLFTℂ.{u}} (a : A ⟶ X) (b : B ⟶ X)

/-- **The fibre product `A ×_X B`** of schemes locally of finite type over `ℂ`: the fibre product
of the underlying schemes, over `ℂ` through `A`. -/
noncomputable def fibreProd : SchemeLFTℂ.{u} :=
  ⟨Over.mk (pullback.fst a.hom.left b.hom.left ≫ A.obj.hom), by
    haveI : LocallyOfFiniteType A.obj.hom := A.property
    change LocallyOfFiniteType (pullback.fst a.hom.left b.hom.left ≫ A.obj.hom)
    infer_instance⟩

@[simp]
lemma fibreProd_obj_left : (fibreProd a b).obj.left = pullback a.hom.left b.hom.left := rfl

lemma fibreProd_obj_hom :
    (fibreProd a b).obj.hom = pullback.fst a.hom.left b.hom.left ≫ A.obj.hom := rfl

lemma pullback_snd_comp_hom :
    pullback.snd a.hom.left b.hom.left ≫ B.obj.hom =
      pullback.fst a.hom.left b.hom.left ≫ A.obj.hom := by
  rw [← Over.w b.hom, ← Over.w a.hom, pullback.condition_assoc]

/-- The first projection `A ×_X B ⟶ A`. -/
noncomputable def fibreProdFst : fibreProd a b ⟶ A :=
  ObjectProperty.homMk (Over.homMk (pullback.fst a.hom.left b.hom.left) rfl)

/-- The second projection `A ×_X B ⟶ B`. -/
noncomputable def fibreProdSnd : fibreProd a b ⟶ B :=
  ObjectProperty.homMk (Over.homMk (pullback.snd a.hom.left b.hom.left)
    (pullback_snd_comp_hom a b))

@[simp]
lemma fibreProdFst_hom_left : (fibreProdFst a b).hom.left = pullback.fst a.hom.left b.hom.left :=
  rfl

@[simp]
lemma fibreProdSnd_hom_left : (fibreProdSnd a b).hom.left = pullback.snd a.hom.left b.hom.left :=
  rfl

@[reassoc]
lemma fibreProd_condition : fibreProdFst a b ≫ a = fibreProdSnd a b ≫ b := by
  ext1
  exact Over.OverMorphism.ext pullback.condition

/-- **Closed points of `A ×_X B` are determined by their projections.** -/
theorem fibreProd_ext_of_isClosed {z z' : (fibreProd a b).obj.left} (hz : IsClosed {z})
    (hz' : IsClosed {z'})
    (h₁ : (pullback.fst a.hom.left b.hom.left).base z =
      (pullback.fst a.hom.left b.hom.left).base z')
    (h₂ : (pullback.snd a.hom.left b.hom.left).base z =
      (pullback.snd a.hom.left b.hom.left).base z') : z = z' := by
  haveI : LocallyOfFiniteType A.obj.hom := A.property
  haveI : LocallyOfFiniteType B.obj.hom := B.property
  haveI : LocallyOfFiniteType (fibreProd a b).obj.hom := (fibreProd a b).property
  let s := (fibreProd a b).obj.hom
  let p := pointOfClosedPoint s z hz
  let p' := pointOfClosedPoint s z' hz'
  have hp : p ≫ s = 𝟙 _ := pointOfClosedPoint_comp s z hz
  have hp' : p' ≫ s = 𝟙 _ := pointOfClosedPoint_comp s z' hz'
  have hpp : p = p' := by
    refine pullback.hom_ext (ext_of_apply_closedPoint_eq A.obj.hom ?_ ?_ ?_)
      (ext_of_apply_closedPoint_eq B.obj.hom ?_ ?_ ?_)
    · rw [Category.assoc]; exact hp
    · rw [Category.assoc]; exact hp'
    · simpa [p, p'] using h₁
    · rw [Category.assoc, pullback_snd_comp_hom]; exact hp
    · rw [Category.assoc, pullback_snd_comp_hom]; exact hp'
    · simpa [p, p'] using h₂
  rw [← pointOfClosedPoint_apply s z hz (IsLocalRing.closedPoint _),
    ← pointOfClosedPoint_apply s z' hz' (IsLocalRing.closedPoint _)]
  exact congrArg (fun q : Spec _ ⟶ _ ↦ q (IsLocalRing.closedPoint _)) hpp

/-- **Every pair of closed points over the same point of `X` comes from a closed point of
`A ×_X B`.** -/
theorem exists_isClosed_fibreProd {y : A.obj.left} {y' : B.obj.left} (hy : IsClosed {y})
    (hy' : IsClosed {y'}) (h : a.hom.left.base y = b.hom.left.base y') :
    ∃ z : (fibreProd a b).obj.left, IsClosed {z} ∧
      (pullback.fst a.hom.left b.hom.left).base z = y ∧
      (pullback.snd a.hom.left b.hom.left).base z = y' := by
  obtain ⟨t, ht, ht'⟩ := Scheme.Pullback.exists_preimage_pullback y y' h
  haveI : JacobsonSpace (pullback a.hom.left b.hom.left : Scheme.{u}) :=
    SchemeLFTℂ.jacobsonSpace (fibreProd a b)
  obtain ⟨z, hzt, hz⟩ := nonempty_inter_closedPoints (Set.singleton_nonempty t).closure
    isClosed_closure.isLocallyClosed
  have hs : t ⤳ z := specializes_iff_mem_closure.2 hzt
  refine ⟨z, hz, ?_, ?_⟩
  · have := (hs.map (pullback.fst a.hom.left b.hom.left).continuous)
    rw [specializes_iff_mem_closure] at this
    change _ ∈ closure {(pullback.fst a.hom.left b.hom.left) t} at this
    rw [ht, hy.closure_eq] at this
    exact this
  · have := (hs.map (pullback.snd a.hom.left b.hom.left).continuous)
    rw [specializes_iff_mem_closure] at this
    change _ ∈ closure {(pullback.snd a.hom.left b.hom.left) t} at this
    rw [ht', hy'.closure_eq] at this
    exact this

end SchemeLFTℂ

/-! ### The analytification of the fibre product -/

open AnalyticSpace SchemeLFTℂ

lemma analytificationHomEquiv_comp {T : AnalyticSpace.{u}} {Y X : SchemeLFTℂ.{u}}
    (φ : T ⟶ analytification.obj Y) (f : Y ⟶ X) :
    analytificationHomEquiv T X (φ ≫ analytification.map f) =
      analytificationHomEquiv T Y φ ≫ schemeToOverSpec.map f.hom := by
  rw [analytificationHomEquiv_apply, analytificationHomEquiv_apply, Functor.map_comp,
    Category.assoc, analytificationπ_naturality, Category.assoc]

variable {A B X : SchemeLFTℂ.{u}} (a : A ⟶ X) (b : B ⟶ X)

/-- **The analytification preserves fibre products**: `(A ×_X B)^an` is the fibre product
`A^an ×_{X^an} B^an`. -/
theorem isPullback_analytification_map_fibreProd :
    IsPullback (analytification.map (fibreProdFst a b)) (analytification.map (fibreProdSnd a b))
      (analytification.map a) (analytification.map b) := by
  have hL := isPullback_forgetToLocallyRingedSpace a.hom.left b.hom.left
  have hsq : analytification.map (fibreProdFst a b) ≫ analytification.map a =
      analytification.map (fibreProdSnd a b) ≫ analytification.map b := by
    rw [← Functor.map_comp, ← Functor.map_comp, fibreProd_condition]
  let e := fun (T : AnalyticSpace.{u}) (Y : SchemeLFTℂ.{u}) ↦ analytificationHomEquiv T Y
  -- the lift of a cone, as a morphism of locally ringed spaces
  let l : (s : PullbackCone (analytification.map a) (analytification.map b)) →
      s.pt.toLocallyRingedSpace ⟶ (pullback a.hom.left b.hom.left).toLocallyRingedSpace :=
    fun s ↦ hL.lift (e _ A s.fst).left (e _ B s.snd).left (by
      have := congrArg (fun φ ↦ (e _ X φ).left) s.condition
      simp only [e, analytificationHomEquiv_comp] at this
      exact this)
  have hl₁ (s : PullbackCone (analytification.map a) (analytification.map b)) :
      l s ≫ (pullback.fst a.hom.left b.hom.left).toLRSHom = (e _ A s.fst).left := hL.lift_fst _ _ _
  have hl₂ (s : PullbackCone (analytification.map a) (analytification.map b)) :
      l s ≫ (pullback.snd a.hom.left b.hom.left).toLRSHom = (e _ B s.snd).left := hL.lift_snd _ _ _
  let L : (s : PullbackCone (analytification.map a) (analytification.map b)) →
      toOverSpec.obj s.pt ⟶ schemeToOverSpec.obj (fibreProd a b).obj := fun s ↦
    Over.homMk (l s) (by
      change l s ≫ (pullback.fst a.hom.left b.hom.left).toLRSHom ≫ A.obj.hom.toLRSHom = _
      rw [reassoc_of% hl₁]
      exact Over.w (e _ A s.fst))
  have hfst {T : AnalyticSpace.{u}} (φ : T ⟶ analytification.obj (fibreProd a b)) :
      (e _ A (φ ≫ analytification.map (fibreProdFst a b))).left =
        (e _ _ φ).left ≫ (pullback.fst a.hom.left b.hom.left).toLRSHom := by
    simp only [e, analytificationHomEquiv_comp]
    rfl
  have hsnd {T : AnalyticSpace.{u}} (φ : T ⟶ analytification.obj (fibreProd a b)) :
      (e _ B (φ ≫ analytification.map (fibreProdSnd a b))).left =
        (e _ _ φ).left ≫ (pullback.snd a.hom.left b.hom.left).toLRSHom := by
    simp only [e, analytificationHomEquiv_comp]
    rfl
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk hsq (fun s ↦ (e _ _).symm (L s))
    (fun s ↦ ?_) (fun s ↦ ?_) (fun s m hm₁ hm₂ ↦ ?_))
  · refine (e _ A).injective (Over.OverMorphism.ext ?_)
    rw [hfst, Equiv.apply_symm_apply]
    exact hl₁ s
  · refine (e _ B).injective (Over.OverMorphism.ext ?_)
    rw [hsnd, Equiv.apply_symm_apply]
    exact hl₂ s
  · rw [Equiv.eq_symm_apply]
    refine Over.OverMorphism.ext (hL.hom_ext ?_ ?_)
    · change (e _ _ m).left ≫ (pullback.fst a.hom.left b.hom.left).toLRSHom =
        l s ≫ (pullback.fst a.hom.left b.hom.left).toLRSHom
      rw [hl₁, ← hfst, hm₁]
    · change (e _ _ m).left ≫ (pullback.snd a.hom.left b.hom.left).toLRSHom =
        l s ≫ (pullback.snd a.hom.left b.hom.left).toLRSHom
      rw [hl₂, ← hsnd, hm₂]

/-- **The analytification of `A ×_X B` is `A^an ×_{X^an} B^an`.** -/
noncomputable def analytificationFibreProdIso :
    analytification.obj (fibreProd a b) ≅
      pullback (analytification.map a) (analytification.map b) :=
  (isPullback_analytification_map_fibreProd a b).isoPullback

@[reassoc (attr := simp)]
lemma analytificationFibreProdIso_hom_fst :
    (analytificationFibreProdIso a b).hom ≫ pullback.fst _ _ =
      analytification.map (fibreProdFst a b) :=
  IsPullback.isoPullback_hom_fst _

@[reassoc (attr := simp)]
lemma analytificationFibreProdIso_hom_snd :
    (analytificationFibreProdIso a b).hom ≫ pullback.snd _ _ =
      analytification.map (fibreProdSnd a b) :=
  IsPullback.isoPullback_hom_snd _

@[reassoc (attr := simp)]
lemma analytificationFibreProdIso_inv_fst :
    (analytificationFibreProdIso a b).inv ≫ analytification.map (fibreProdFst a b) =
      pullback.fst _ _ :=
  IsPullback.isoPullback_inv_fst _

@[reassoc (attr := simp)]
lemma analytificationFibreProdIso_inv_snd :
    (analytificationFibreProdIso a b).inv ≫ analytification.map (fibreProdSnd a b) =
      pullback.snd _ _ :=
  IsPullback.isoPullback_inv_snd _

end ComplexAnalytic
