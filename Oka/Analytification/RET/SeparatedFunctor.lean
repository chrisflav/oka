/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.FullyFaithful
import Oka.Analytification.RET.Separated
import Oka.AnalyticSpace.SeparatedFiniteEtale

/-!
# Analytification into separated finite étale covers

The analytification of a finite étale cover `Y ⟶ X` of schemes locally of finite type over `ℂ`
has separated structure map (`ComplexAnalytic.isSeparatedMap_analytification_map`), so the
analytification functor on finite étale covers factors through the category
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver (X^an)` of covers with separated structure
map. The factorisation is fully faithful.

## Main definitions

- `ComplexAnalytic.analytificationSepFiniteEtaleOver X`: the functor
  `FEt(X) ⥤ SepFEt(X^an)`.
- `ComplexAnalytic.SeparatedCoversAlgebraic X`: every finite étale cover of `X^an` with separated
  structure map is the analytification of a finite étale cover of `X`.

## Main results

- `ComplexAnalytic.fullyFaithfulAnalytificationSepFiniteEtaleOver`: the functor is fully
  faithful.
- `ComplexAnalytic.separatedCoversAlgebraic_iff_essSurj`: `SeparatedCoversAlgebraic X` is
  essential surjectivity of the functor.
-/

open CategoryTheory AlgebraicGeometry

universe u

namespace ComplexAnalytic

open AnalyticSpace

noncomputable section

variable (X : SchemeLFTℂ.{u})

/-- **The analytification functor on finite étale covers, landing in separated covers**,
`FEt(X) ⥤ SepFEt(X^an)`. -/
def analytificationSepFiniteEtaleOver :
    SchemeLFTℂ.FiniteEtaleOver X ⥤ SeparatedFiniteEtaleOver (analytification.obj X) where
  obj A := MorphismProperty.Over.mk ⊤ (analytification.map A.hom)
    ⟨isFiniteEtale_analytification_map A.hom A.prop,
      haveI : AlgebraicGeometry.IsFinite A.hom.hom.left := A.prop.1
      isSeparatedMap_analytification_map A.hom⟩
  map {A B} φ := MorphismProperty.Over.homMk (analytification.map φ.left) (by
    change analytification.map φ.left ≫ analytification.map B.hom = analytification.map A.hom
    rw [← Functor.map_comp]
    exact congrArg analytification.map (MorphismProperty.Over.w φ))
  map_id A := MorphismProperty.Over.Hom.ext (analytification.map_id A.left)
  map_comp φ ψ := MorphismProperty.Over.Hom.ext (analytification.map_comp φ.left ψ.left)

@[simp]
lemma analytificationSepFiniteEtaleOver_obj_hom (A : SchemeLFTℂ.FiniteEtaleOver X) :
    ((analytificationSepFiniteEtaleOver X).obj A).hom = analytification.map A.hom :=
  rfl

@[simp]
lemma analytificationSepFiniteEtaleOver_map_left {A B : SchemeLFTℂ.FiniteEtaleOver X}
    (φ : A ⟶ B) :
    ((analytificationSepFiniteEtaleOver X).map φ).left = analytification.map φ.left :=
  rfl

/-- The functor followed by the inclusion into all finite étale covers is the analytification
functor on finite étale covers. -/
def analytificationSepFiniteEtaleOverCompIso :
    analytificationSepFiniteEtaleOver X ⋙
        SeparatedFiniteEtaleOver.toFiniteEtaleOver (analytification.obj X) ≅
      analytificationFiniteEtaleOver X :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) fun _ ↦ by
    ext
    exact (Category.comp_id _).trans (Category.id_comp _).symm

/-- **The analytification functor into separated finite étale covers is fully faithful.** -/
def fullyFaithfulAnalytificationSepFiniteEtaleOver :
    (analytificationSepFiniteEtaleOver X).FullyFaithful :=
  .ofCompFaithful (G := SeparatedFiniteEtaleOver.toFiniteEtaleOver (analytification.obj X))
    ((fullyFaithfulAnalytificationFiniteEtaleOver X).ofIso
      (analytificationSepFiniteEtaleOverCompIso X).symm)

instance : (analytificationSepFiniteEtaleOver X).Full :=
  (fullyFaithfulAnalytificationSepFiniteEtaleOver X).full

instance : (analytificationSepFiniteEtaleOver X).Faithful :=
  (fullyFaithfulAnalytificationSepFiniteEtaleOver X).faithful

/-- A separated cover lies in the essential image of `analytificationSepFiniteEtaleOver X` if and
only if it lies in the essential image of `analytificationFiniteEtaleOver X`. -/
lemma mem_essImage_analytificationSepFiniteEtaleOver_iff
    (W : SeparatedFiniteEtaleOver (analytification.obj X)) :
    (analytificationSepFiniteEtaleOver X).essImage W ↔ (analytificationFiniteEtaleOver X).essImage
      ((SeparatedFiniteEtaleOver.toFiniteEtaleOver (analytification.obj X)).obj W) := by
  refine ⟨fun ⟨Y, ⟨e⟩⟩ ↦ ⟨Y, ⟨(SeparatedFiniteEtaleOver.toFiniteEtaleOver _).mapIso e⟩⟩,
    fun ⟨Y, ⟨e⟩⟩ ↦ ⟨Y, ⟨?_⟩⟩⟩
  exact (MorphismProperty.Comma.fullyFaithfulChangeProp _ _ _).preimageIso e

/-- **Every finite étale cover of `X^an` with separated structure map is the analytification of
a finite étale cover of `X`.** -/
def SeparatedCoversAlgebraic : Prop :=
  ∀ W : AnalyticSpace.FiniteEtaleOver (analytification.obj X),
    IsSeparatedMap W.hom.toLRSHom.base → (analytificationFiniteEtaleOver X).essImage W

/-- `SeparatedCoversAlgebraic X` is essential surjectivity of the analytification functor into
separated finite étale covers. -/
theorem separatedCoversAlgebraic_iff_essSurj :
    SeparatedCoversAlgebraic X ↔ (analytificationSepFiniteEtaleOver X).EssSurj := by
  refine ⟨fun h ↦ ⟨fun W ↦ (mem_essImage_analytificationSepFiniteEtaleOver_iff X W).2
    (h _ W.isSeparatedMap_hom)⟩, fun h W hW ↦ ?_⟩
  let W' : SeparatedFiniteEtaleOver (analytification.obj X) :=
    MorphismProperty.Over.mk ⊤ W.hom ⟨W.prop, hW⟩
  exact (mem_essImage_analytificationSepFiniteEtaleOver_iff X W').1
    (Functor.EssSurj.mem_essImage _ _)

end

end ComplexAnalytic
