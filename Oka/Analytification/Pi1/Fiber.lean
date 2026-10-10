/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.Pi1.FiniteEtale
import Oka.Analytification.RET.ClosedPoints
import Oka.Analytification.RET.RiemannExistence
import Oka.AnalyticSpace.GaloisCategory

/-!
# The étale and the analytic fibre functors agree

For `X` locally of finite type over `ℂ` and a point `x` of `X^an`, let `ξₓ : Spec ℂ ⟶ X` be the
`ℂ`-point at the closed point `π(x)` (`ComplexAnalytic.geometricPoint`, Mathlib's
`AlgebraicGeometry.pointOfClosedPoint`). This file shows that pi1's fibre functor
`AlgebraicGeometry.FiniteEtale.fiber ξₓ` is isomorphic to the analytic fibre functor at `x`
composed with the Riemann existence equivalence (`ComplexAnalytic.fiberGeometricPointIso`).

Both fibres of a cover `A` are identified with the set of points of `A` over `π(x)`: the points of
`A ×_X Spec ℂ` through the first projection (the base change of the preimmersion `ξₓ`), and the
points of `A^an` over `x` through `π_A`, which is injective with image the closed points
(`Oka/Analytification/RET/ClosedPoints.lean`); a point over a closed point under a finite morphism
of Jacobson schemes is closed (`AlgebraicGeometry.isClosed_singleton_of_isFinite`).
-/

universe u

open CategoryTheory AlgebraicGeometry Limits

namespace AlgebraicGeometry

/-- **Under a finite morphism out of a Jacobson scheme, a point over a closed point is closed.** -/
lemma isClosed_singleton_of_isFinite {A Y : Scheme.{u}} (f : A ⟶ Y) [IsFinite f] [JacobsonSpace A]
    {z : A} (hz : IsClosed {f z}) : IsClosed {z} := by
  set S := closure {z}
  have hS : S ⊆ f ⁻¹' {f z} := by
    intro w hw
    have := image_closure_subset_closure_image (f := f.base) f.continuous ⟨w, hw, rfl⟩
    rwa [Set.image_singleton, hz.closure_eq] at this
  have hfin : (S ∩ closedPoints A).Finite :=
    (f.finite_preimage_singleton (f z)).subset (Set.inter_subset_left.trans hS)
  have hcl : IsClosed (S ∩ closedPoints A) := by
    rw [← Set.biUnion_of_singleton (S ∩ closedPoints A)]
    exact hfin.isClosed_biUnion fun w hw ↦ hw.2
  have h := closure_inter_closedPoints (X := A) (Z := S) isClosed_closure
  rw [hcl.closure_eq] at h
  have hzS : z ∈ S := subset_closure rfl
  rw [← h] at hzS
  exact hzS.2

end AlgebraicGeometry

namespace ComplexAnalytic

noncomputable section

variable (X : SchemeLFTℂ.{u}) (x : analytification.obj X)

lemma isClosed_analytificationπ_base :
    IsClosed {(analytificationπ X).left.base x} :=
  (mem_range_analytificationπ_base_iff X _).1 ⟨x, rfl⟩

/-- **The geometric point of `X` at a point `x` of `X^an`**: the `ℂ`-point of `X` at the closed
point `π(x)`. -/
def geometricPoint : Spec (CommRingCat.of (ULift.{u} ℂ)) ⟶ X.obj.left :=
  haveI : LocallyOfFiniteType X.obj.hom := X.property
  pointOfClosedPoint X.obj.hom _ (isClosed_analytificationπ_base X x)

instance : IsPreimmersion (geometricPoint X x) := by
  unfold geometricPoint pointOfClosedPoint
  infer_instance

lemma geometricPoint_apply (a : Spec (CommRingCat.of (ULift.{u} ℂ))) :
    geometricPoint X x a = (analytificationπ X).left.base x := by
  haveI : LocallyOfFiniteType X.obj.hom := X.property
  exact pointOfClosedPoint_apply X.obj.hom _ _ a

lemma range_geometricPoint :
    Set.range (geometricPoint X x).base = {(analytificationπ X).left.base x} := by
  ext y
  refine ⟨?_, fun (h : y = _) ↦ ?_⟩
  · rintro ⟨a, rfl⟩
    exact geometricPoint_apply X x a
  · obtain ⟨a⟩ : Nonempty (Spec (CommRingCat.of (ULift.{u} ℂ))) := inferInstance
    exact ⟨a, (geometricPoint_apply X x a).trans h.symm⟩

variable {X}

/-- For any `f : Y ⟶ X`, the points of `Y ×_X Spec ℂ` (along `ξₓ`) are the points of `Y` over
`π(x)`, through the first projection. -/
def pullbackGeometricPointEquiv {Y : Scheme.{u}} (f : Y ⟶ X.obj.left) :
    ((Limits.pullback f (geometricPoint X x) : Scheme.{u}) : Type u) ≃
      {z : Y // f z = (analytificationπ X).left.base x} :=
  Equiv.ofBijective
    (fun p ↦ ⟨Limits.pullback.fst f (geometricPoint X x) p, by
      have h : Limits.pullback.fst f (geometricPoint X x) p ∈
          f ⁻¹' Set.range (geometricPoint X x) := by
        rw [← Scheme.Pullback.range_fst]
        exact ⟨p, rfl⟩
      rwa [range_geometricPoint] at h⟩)
    ⟨fun p q h ↦ (Limits.pullback.fst f (geometricPoint X x)).isEmbedding.injective
        (congr_arg Subtype.val h),
      fun ⟨z, hz⟩ ↦ by
        have h : z ∈ Set.range (Limits.pullback.fst f (geometricPoint X x)) := by
          rw [Scheme.Pullback.range_fst, range_geometricPoint]
          exact hz
        obtain ⟨p, hp⟩ := h
        exact ⟨p, Subtype.ext hp⟩⟩

instance (A : FiniteEtale X.obj.left) : IsFinite (SchemeLFTℂ.ofFiniteEtaleHom X A).hom.left := by
  change IsFinite A.hom
  infer_instance

/-- For a finite `g : T ⟶ X`, the points of `T^an` over `x` are the points of `T` over `π(x)`,
through `π_T`. -/
def analyticFiberEquivAux {T : SchemeLFTℂ.{u}} (g : T ⟶ X) [IsFinite g.hom.left] :
    {a : analytification.obj T // (analytification.map g).toLRSHom.base a = x} ≃
      {z : T.obj.left // g.hom.left z = (analytificationπ X).left.base x} :=
  haveI := SchemeLFTℂ.jacobsonSpace T
  Equiv.ofBijective
    (fun a ↦ ⟨(analytificationπ T).left.base a.1, by
      rw [← analytificationπ_base_map_apply, a.2]⟩)
    ⟨fun a b h ↦ Subtype.ext (analytificationπ_base_injective _ (congr_arg Subtype.val h)),
      fun ⟨z, hz⟩ ↦ by
        have hzc : IsClosed {z} :=
          isClosed_singleton_of_isFinite g.hom.left (hz ▸ isClosed_analytificationπ_base X x)
        obtain ⟨a, rfl⟩ := (mem_range_analytificationπ_base_iff T z).2 hzc
        refine ⟨⟨a, analytificationπ_base_injective X ?_⟩, rfl⟩
        rw [analytificationπ_base_map_apply]
        exact hz⟩

/-- The composite of the two equivalences `FEt(X) ≌ FEtℂ(X) ≌ SepFEt(X^an)`. -/
abbrev analytificationFiniteEtale (X : SchemeLFTℂ.{u}) :
    FiniteEtale X.obj.left ⥤ AnalyticSpace.SeparatedFiniteEtaleOver (analytification.obj X) :=
  finiteEtaleToSchemeLFTℂ X ⋙ analytificationSepFiniteEtaleOver X

instance : (analytificationFiniteEtale X).IsEquivalence := by
  haveI := riemannExistenceTheorem X
  infer_instance

lemma pullbackGeometricPointEquiv_naturality {A B : FiniteEtale X.obj.left} (f : A ⟶ B)
    (p : (FiniteEtale.fiber (geometricPoint X x)).obj A) :
    (pullbackGeometricPointEquiv x B.hom ((FiniteEtale.fiber (geometricPoint X x)).map f p)).1 =
      f.left (pullbackGeometricPointEquiv x A.hom p).1 := by
  change Limits.pullback.fst B.hom (geometricPoint X x)
      (((FiniteEtale.pullback (geometricPoint X x)).map f).left p) =
    f.left (Limits.pullback.fst A.hom (geometricPoint X x) p)
  have h : ((FiniteEtale.pullback (geometricPoint X x)).map f).left ≫
      Limits.pullback.fst B.hom (geometricPoint X x) =
      Limits.pullback.fst A.hom (geometricPoint X x) ≫ f.left := by
    simp only [FiniteEtale.pullback]
    exact Limits.pullback.lift_fst _ _ _
  exact congr_arg (fun g ↦ g.base p) h

/-- **The étale fibre functor at `ξₓ` is the analytic fibre functor at `x`**, through the Riemann
existence equivalence: both fibres of `A` are the points of `A` over `π(x)`. -/
def fiberGeometricPointIso :
    FiniteEtale.fiber (geometricPoint X x) ≅
      analytificationFiniteEtale X ⋙ AnalyticSpace.SeparatedFiniteEtaleOver.fintypeFiberFunctor x :=
  NatIso.ofComponents
    (fun A ↦ FintypeCat.equivEquivIso ((pullbackGeometricPointEquiv x A.hom).trans
        (analyticFiberEquivAux x (SchemeLFTℂ.ofFiniteEtaleHom X A)).symm))
    (fun {A B} f ↦ by
      ext p
      apply (analyticFiberEquivAux x (SchemeLFTℂ.ofFiniteEtaleHom X B)).injective
      apply Subtype.ext
      have h2 (a : {a : analytification.obj (SchemeLFTℂ.ofFiniteEtale X A) //
          (analytification.map (SchemeLFTℂ.ofFiniteEtaleHom X A)).toLRSHom.base a = x}) :
          (analyticFiberEquivAux x (SchemeLFTℂ.ofFiniteEtaleHom X B)
            ((analytificationFiniteEtale X ⋙
              AnalyticSpace.SeparatedFiniteEtaleOver.fintypeFiberFunctor x).map f a)).1 =
            f.left (analyticFiberEquivAux x (SchemeLFTℂ.ofFiniteEtaleHom X A) a).1 :=
        analytificationπ_base_map_apply ((finiteEtaleToSchemeLFTℂ X).map f).left a.1
      change (analyticFiberEquivAux x (SchemeLFTℂ.ofFiniteEtaleHom X B)
          ((analyticFiberEquivAux x (SchemeLFTℂ.ofFiniteEtaleHom X B)).symm
            (pullbackGeometricPointEquiv x B.hom
              ((FiniteEtale.fiber (geometricPoint X x)).map f p)))).1 =
        (analyticFiberEquivAux x (SchemeLFTℂ.ofFiniteEtaleHom X B)
          ((analytificationFiniteEtale X ⋙
            AnalyticSpace.SeparatedFiniteEtaleOver.fintypeFiberFunctor x).map f
            ((analyticFiberEquivAux x (SchemeLFTℂ.ofFiniteEtaleHom X A)).symm
              (pullbackGeometricPointEquiv x A.hom p)))).1
      rw [Equiv.apply_symm_apply, pullbackGeometricPointEquiv_naturality, h2,
        Equiv.apply_symm_apply])

end

end ComplexAnalytic
