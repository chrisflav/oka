/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.AlgebraicGeometry.AlgClosed.Basic
import Oka.Analytification.RET.ClosedPoints
import Oka.Analytification.RET.FiniteEtaleFunctor

/-!
# Faithfulness of the analytification on unramified morphisms

Let `b : B ⟶ X` be a morphism of schemes locally of finite type over `ℂ` which is formally
unramified (for example étale), and let `φ ψ : A ⟶ B` be morphisms over `X`. If
`φ^an = ψ^an`, then `φ` and `ψ` agree on the image of `π_A : A^an ⟶ A`, which is the set of
closed points of `A` (`ComplexAnalytic.range_analytificationπ_base`). Since the diagonal of `b`
is an open immersion, the equaliser of `φ` and `ψ` is an open subscheme of `A` containing all
closed points, hence all of `A` (`AlgebraicGeometry.ext_of_apply_eq_of_formallyUnramified`).

## Main results

- `ComplexAnalytic.eq_of_analytification_map_eq`: `φ^an = ψ^an` implies `φ = ψ` for morphisms
  over a formally unramified `B ⟶ X`.
- `ComplexAnalytic.faithful_analytificationFiniteEtaleOver`: the analytification functor
  `FEt(X) ⥤ FEt(X^an)` is faithful.
-/

open CategoryTheory AlgebraicGeometry

universe u

namespace ComplexAnalytic

open AnalyticSpace

/-- Two morphisms `φ ψ : A ⟶ B` over `X` which agree on the closed points of `A` are equal, if
`B ⟶ X` is formally unramified. -/
theorem SchemeLFTℂ.ext_of_apply_eq_of_formallyUnramified {A B X : SchemeLFTℂ.{u}}
    {φ ψ : A ⟶ B} (b : B ⟶ X) [FormallyUnramified b.hom.left] (hb : φ ≫ b = ψ ≫ b)
    (H : ∀ a : A.obj.left, IsClosed {a} → φ.hom.left.base a = ψ.hom.left.base a) : φ = ψ := by
  haveI : LocallyOfFiniteType X.obj.hom := X.property
  haveI : LocallyOfFiniteType B.obj.hom := B.property
  haveI : LocallyOfFiniteType b.hom.left :=
    haveI : LocallyOfFiniteType (b.hom.left ≫ X.obj.hom) := by rw [Over.w b.hom]; infer_instance
    locallyOfFiniteType_of_comp b.hom.left X.obj.hom
  have hA : φ.hom.left ≫ b.hom.left ≫ X.obj.hom = A.obj.hom := by
    rw [Over.w b.hom, Over.w φ.hom]
  haveI : LocallyOfFiniteType (φ.hom.left ≫ b.hom.left ≫ X.obj.hom) := by
    rw [hA]
    exact A.property
  ext1
  refine Over.OverMorphism.ext (AlgebraicGeometry.ext_of_apply_eq_of_formallyUnramified
    b.hom.left X.obj.hom ?_ H)
  exact congrArg (fun f ↦ f.hom.left) hb

/-- **The analytification is faithful on morphisms over a formally unramified morphism**: if
`b : B ⟶ X` is formally unramified and `φ ψ : A ⟶ B` satisfy `φ ≫ b = ψ ≫ b` and
`φ^an = ψ^an`, then `φ = ψ`. -/
theorem eq_of_analytification_map_eq {A B X : SchemeLFTℂ.{u}} {φ ψ : A ⟶ B} (b : B ⟶ X)
    [FormallyUnramified b.hom.left] (hb : φ ≫ b = ψ ≫ b)
    (h : analytification.map φ = analytification.map ψ) : φ = ψ := by
  refine SchemeLFTℂ.ext_of_apply_eq_of_formallyUnramified b hb fun a ha ↦ ?_
  obtain ⟨y, rfl⟩ := (mem_range_analytificationπ_base_iff A a).2 ha
  rw [← analytificationπ_base_map_apply, ← analytificationπ_base_map_apply, h]

/-- **The analytification functor on finite étale covers is faithful.** -/
instance faithful_analytificationFiniteEtaleOver (X : SchemeLFTℂ.{u}) :
    (analytificationFiniteEtaleOver X).Faithful where
  map_injective {A B} φ ψ h := by
    have hu : FormallyUnramified B.hom.hom.left := by
      haveI : Etale B.hom.hom.left := B.prop.2
      infer_instance
    refine MorphismProperty.Over.Hom.ext (@eq_of_analytification_map_eq _ _ _ _ _ B.hom hu ?_
      (congrArg (fun f ↦ f.left) h))
    rw [MorphismProperty.Over.w φ, MorphismProperty.Over.w ψ]

end ComplexAnalytic
