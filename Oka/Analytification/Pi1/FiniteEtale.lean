/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.FiniteEtaleFunctor
import Pi1.FundamentalGroup.Galois

/-!
# Finite étale covers of a scheme over `ℂ`, two ways

pi1's `AlgebraicGeometry.FiniteEtale S` is the category of finite étale schemes over a scheme `S`
(the category whose fibre functors define `π₁ᵉᵗ`), while the Riemann existence theorem of this
repository is stated for `ComplexAnalytic.SchemeLFTℂ.FiniteEtaleOver X`, finite étale covers in
the category of schemes locally of finite type over `ℂ`. This file identifies the two: a finite
étale `A ⟶ X` is locally of finite type over `ℂ` through `X`, and morphisms over `X` are
automatically over `ℂ`.

## Main definitions

- `ComplexAnalytic.finiteEtaleToSchemeLFTℂ X`, the functor
  `FiniteEtale X.obj.left ⥤ SchemeLFTℂ.FiniteEtaleOver X`;
  it is an equivalence (`ComplexAnalytic.isEquivalence_finiteEtaleToSchemeLFTℂ`).
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace ComplexAnalytic

noncomputable section

variable (X : SchemeLFTℂ.{u})

/-- A finite étale scheme over `X`, as a scheme locally of finite type over `ℂ` through `X`. -/
def SchemeLFTℂ.ofFiniteEtale (A : FiniteEtale X.obj.left) : SchemeLFTℂ.{u} :=
  ⟨Over.mk (A.hom ≫ X.obj.hom), by
    have h₁ : LocallyOfFiniteType A.hom := haveI : IsFiniteEtale A.hom := A.2; inferInstance
    exact MorphismProperty.comp_mem @LocallyOfFiniteType _ _ h₁ X.property⟩

/-- Its structure morphism to `X`. -/
def SchemeLFTℂ.ofFiniteEtaleHom (A : FiniteEtale X.obj.left) : SchemeLFTℂ.ofFiniteEtale X A ⟶ X :=
  ObjectProperty.homMk (Over.homMk A.hom rfl)

/-- **Finite étale schemes over `X` as finite étale covers in `SchemeLFTℂ`.** -/
def finiteEtaleToSchemeLFTℂ : FiniteEtale X.obj.left ⥤ SchemeLFTℂ.FiniteEtaleOver X where
  obj A := MorphismProperty.Over.mk ⊤ (SchemeLFTℂ.ofFiniteEtaleHom X A)
    ⟨inferInstanceAs (IsFinite A.hom), inferInstanceAs (Etale A.hom)⟩
  map {A B} f := MorphismProperty.Over.homMk
    (ObjectProperty.homMk (Over.homMk f.left (by
      change f.left ≫ B.hom ≫ X.obj.hom = A.hom ≫ X.obj.hom
      rw [← Category.assoc, MorphismProperty.Over.w f]
      rfl)))
    (by
      ext1
      exact Over.OverMorphism.ext (MorphismProperty.Over.w f))

@[simp]
lemma finiteEtaleToSchemeLFTℂ_obj_hom_hom_left (A : FiniteEtale X.obj.left) :
    ((finiteEtaleToSchemeLFTℂ X).obj A).hom.hom.left = A.hom :=
  rfl

@[simp]
lemma finiteEtaleToSchemeLFTℂ_obj_left_obj_left (A : FiniteEtale X.obj.left) :
    ((finiteEtaleToSchemeLFTℂ X).obj A).left.obj.left = A.left :=
  rfl

@[simp]
lemma finiteEtaleToSchemeLFTℂ_map_left_hom_left {A B : FiniteEtale X.obj.left} (f : A ⟶ B) :
    ((finiteEtaleToSchemeLFTℂ X).map f).left.hom.left = f.left :=
  rfl

instance : (finiteEtaleToSchemeLFTℂ X).Faithful where
  map_injective {A B} f g h := by
    apply MorphismProperty.Over.Hom.ext
    exact congr_arg (fun φ ↦ φ.left.hom.left) h

instance : (finiteEtaleToSchemeLFTℂ X).Full where
  map_surjective {A B} g := ⟨MorphismProperty.Over.homMk g.left.hom.left
    (congr_arg (fun φ ↦ φ.hom.left) (MorphismProperty.Over.w g)), rfl⟩

instance : (finiteEtaleToSchemeLFTℂ X).EssSurj where
  mem_essImage A' := by
    haveI : IsFinite A'.hom.hom.left := A'.prop.1
    haveI : Etale A'.hom.hom.left := A'.prop.2
    have hA : IsFiniteEtale A'.hom.hom.left := ⟨⟩
    let A : FiniteEtale X.obj.left := MorphismProperty.Over.mk ⊤ A'.hom.hom.left hA
    refine ⟨A, ⟨MorphismProperty.Over.isoMk ?_ ?_⟩⟩
    · exact (ObjectProperty.fullyFaithfulι _).preimageIso
        (Over.isoMk (Iso.refl _) (by
          simp only [Iso.refl_hom]
          exact (Over.w A'.hom.hom).symm))
    · ext1
      exact Over.OverMorphism.ext (Category.id_comp _)

instance isEquivalence_finiteEtaleToSchemeLFTℂ : (finiteEtaleToSchemeLFTℂ X).IsEquivalence where

end

end ComplexAnalytic
