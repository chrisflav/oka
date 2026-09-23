/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Analytification.RET.EtaleLocalIso
import Oka.Analytification.RET.FiniteAnalytification
import Oka.AnalyticSpace.FiniteEtaleOver

/-!
# Analytification of finite étale covers

A morphism `f : Y ⟶ X` of schemes locally of finite type over `ℂ` is finite étale if its
underlying morphism of schemes is finite and étale. Its analytification is then finite étale in
the sense of `ComplexAnalytic.AnalyticSpace.IsFiniteEtale`: it is finite
(`ComplexAnalytic.isFinite_analytification_map_of_isFinite`) and a local isomorphism
(`ComplexAnalytic.isLocalIso_analytification_map_of_etale`).

## Main definitions

- `ComplexAnalytic.SchemeLFTℂ.isFiniteEtale`: finite étale morphisms of schemes locally of finite
  type over `ℂ`.
- `ComplexAnalytic.SchemeLFTℂ.FiniteEtaleOver X`: the category of finite étale covers of `X`.
- `ComplexAnalytic.analytificationFiniteEtaleOver X`: the analytification functor
  `FEt(X) ⥤ FEt(X^an)`.
-/

open CategoryTheory AlgebraicGeometry

universe u

namespace ComplexAnalytic

open AnalyticSpace

noncomputable section

/-- **Finite étale morphisms** of schemes locally of finite type over `ℂ`: the underlying
morphism of schemes is finite and étale. -/
def SchemeLFTℂ.isFiniteEtale : MorphismProperty SchemeLFTℂ.{u} :=
  fun _ _ f ↦ AlgebraicGeometry.IsFinite f.hom.left ∧ Etale f.hom.left

instance : SchemeLFTℂ.isFiniteEtale.{u}.IsStableUnderComposition where
  comp_mem f g hf hg := by
    haveI := hf.1; haveI := hf.2; haveI := hg.1; haveI := hg.2
    change AlgebraicGeometry.IsFinite (f.hom.left ≫ g.hom.left) ∧
      Etale (f.hom.left ≫ g.hom.left)
    exact ⟨inferInstance, inferInstance⟩

instance : SchemeLFTℂ.isFiniteEtale.{u}.ContainsIdentities where
  id_mem X := by
    change AlgebraicGeometry.IsFinite (𝟙 X.obj.left) ∧ Etale (𝟙 X.obj.left)
    exact ⟨inferInstance, inferInstance⟩

instance : SchemeLFTℂ.isFiniteEtale.{u}.IsMultiplicative where

/-- **The analytification of a finite étale morphism is finite étale**: finite and a local
isomorphism of complex analytic spaces. -/
theorem isFiniteEtale_analytification_map {Y X : SchemeLFTℂ.{u}} (f : Y ⟶ X)
    (hf : SchemeLFTℂ.isFiniteEtale f) : IsFiniteEtale (analytification.map f) :=
  haveI := hf.1
  haveI := hf.2
  ⟨isFinite_analytification_map_of_isFinite f, isLocalIso_analytification_map_of_etale f⟩

/-- **The finite étale covers of `X`**, as a category: finite étale morphisms into `X`, with all
morphisms over `X`. -/
abbrev SchemeLFTℂ.FiniteEtaleOver (X : SchemeLFTℂ.{u}) : Type _ :=
  (SchemeLFTℂ.isFiniteEtale.{u}).Over ⊤ X

/-- **The analytification functor on finite étale covers**, `FEt(X) ⥤ FEt(X^an)`. -/
def analytificationFiniteEtaleOver (X : SchemeLFTℂ.{u}) :
    SchemeLFTℂ.FiniteEtaleOver X ⥤ AnalyticSpace.FiniteEtaleOver (analytification.obj X) where
  obj A := MorphismProperty.Over.mk ⊤ (analytification.map A.hom)
    (isFiniteEtale_analytification_map A.hom A.prop)
  map {A B} φ := MorphismProperty.Over.homMk (analytification.map φ.left) (by
    change analytification.map φ.left ≫ analytification.map B.hom = analytification.map A.hom
    rw [← Functor.map_comp]
    exact congrArg analytification.map (MorphismProperty.Over.w φ))
  map_id A := MorphismProperty.Over.Hom.ext (analytification.map_id A.left)
  map_comp φ ψ := MorphismProperty.Over.Hom.ext (analytification.map_comp φ.left ψ.left)

@[simp]
lemma analytificationFiniteEtaleOver_obj_hom (X : SchemeLFTℂ.{u})
    (A : SchemeLFTℂ.FiniteEtaleOver X) :
    ((analytificationFiniteEtaleOver X).obj A).hom = analytification.map A.hom :=
  rfl

@[simp]
lemma analytificationFiniteEtaleOver_map_left (X : SchemeLFTℂ.{u})
    {A B : SchemeLFTℂ.FiniteEtaleOver X} (φ : A ⟶ B) :
    ((analytificationFiniteEtaleOver X).map φ).left = analytification.map φ.left :=
  rfl

end

end ComplexAnalytic
