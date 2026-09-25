/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.ES.Normalization
import Oka.Analytification.RET.SeparatedFunctor
import Oka.AnalyticSpace.SeparatedFiniteEtaleBaseChange

/-!
# Reductions for separated finite étale covers

Structural reductions for `ComplexAnalytic.SeparatedCoversAlgebraic X`, the statement that every
finite étale cover of `X^an` with separated structure map is the analytification of a finite
étale cover of `X`. Separatedness of the structure map is stable under the pullbacks and
transports used below, so the object-wise reductions of `Oka/Analytification/RET/ES/Local.lean`,
`Oka/Analytification/RET/ES/NilThickening.lean` and `Oka/Analytification/RET/ES/Normalization.lean`
apply.

## Main results

- `ComplexAnalytic.SeparatedCoversAlgebraic.of_cover`: Zariski-locality.
- `ComplexAnalytic.SeparatedCoversAlgebraic.of_isClosedImmersion`,
  `ComplexAnalytic.SeparatedCoversAlgebraic.of_quotient_nilradical`: nil-thickenings.
- `ComplexAnalytic.SeparatedCoversAlgebraic.of_milnorSquare`: Milnor squares.
- `ComplexAnalytic.separatedCoversAlgebraic_of_isEmpty`,
  `ComplexAnalytic.separatedCoversAlgebraic_of_subsingleton`: the empty scheme.
- `ComplexAnalytic.mem_essImage_pullbackFiniteEtaleOver`: the essential image of the
  analytification is stable under pullback.
-/

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace ComplexAnalytic

open AnalyticSpace

noncomputable section

/-- The restriction of a cover with separated structure map has separated structure map. -/
lemma isSeparatedMap_restrictFiniteEtaleOver {X : SchemeLFTℂ.{u}}
    (W : AnalyticSpace.FiniteEtaleOver (analytification.obj X))
    (hW : IsSeparatedMap W.hom.toLRSHom.base) (V : X.obj.left.Opens) :
    IsSeparatedMap (restrictFiniteEtaleOver W V).hom.toLRSHom.base :=
  haveI : IsFiniteEtale W.hom := W.prop
  isSeparatedMap_pullback_snd_of_isSeparatedMap W.hom _ hW

/-- The pullback of a cover with separated structure map has separated structure map. -/
lemma isSeparatedMap_pullbackFiniteEtaleOver {X Y : SchemeLFTℂ.{u}}
    (W : AnalyticSpace.FiniteEtaleOver (analytification.obj X))
    (hW : IsSeparatedMap W.hom.toLRSHom.base) (f : Y ⟶ X) :
    IsSeparatedMap (pullbackFiniteEtaleOver W f).hom.toLRSHom.base :=
  haveI : IsFiniteEtale W.hom := W.prop
  isSeparatedMap_pullback_snd_of_isSeparatedMap W.hom _ hW

/-- **Zariski-locality**: if `X` is covered by opens `U i` with `SeparatedCoversAlgebraic` for
each `U i`, then `SeparatedCoversAlgebraic X`. -/
theorem SeparatedCoversAlgebraic.of_cover {X : SchemeLFTℂ.{u}} {ι : Type*}
    (U : ι → X.obj.left.Opens) (hU : ⨆ i, U i = ⊤)
    (h : ∀ i, SeparatedCoversAlgebraic (X.restrict (U i))) : SeparatedCoversAlgebraic X :=
  fun W hW ↦ mem_essImage_of_cover W U hU fun i ↦
    h i _ (isSeparatedMap_restrictFiniteEtaleOver W hW (U i))

/-- **Descent along surjective closed immersions into affine schemes.** -/
theorem SeparatedCoversAlgebraic.of_isClosedImmersion {Z X : SchemeLFTℂ.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i.hom.left] [IsAffine X.obj.left]
    (hi : Function.Surjective i.hom.left.base) (hZ : SeparatedCoversAlgebraic Z) :
    SeparatedCoversAlgebraic X := by
  intro W hW
  let hg := isHomeomorph_analytification_map_of_surjective i hi
  let W' := FiniteEtaleOver.transport (analytification.map i) hg W
  have hW' : IsSeparatedMap W'.hom.toLRSHom.base :=
    hW.comp_left (hg.homeomorph _).symm.injective
  obtain ⟨Y₀, ⟨e⟩⟩ := hZ W' hW'
  obtain ⟨Y, j, hj, hjs, hjY⟩ := SchemeLFTℂ.FiniteEtaleOver.exists_lift i hi Y₀
  obtain ⟨e'⟩ := FiniteEtaleOver.nonempty_iso_of_iso_transport (analytification.map i) hg e
    (A := (analytificationFiniteEtaleOver X).obj Y) (analytification.map j)
    (isHomeomorph_analytification_map_of_surjective j hjs) (by
      change analytification.map j ≫ analytification.map Y.hom =
        analytification.map Y₀.hom ≫ analytification.map i
      exact (Functor.map_comp _ _ _).symm.trans
        ((congrArg analytification.map hjY).trans (Functor.map_comp _ _ _)))
  exact ⟨Y, ⟨e'⟩⟩

/-- **Reduction to the reduced quotient**: for `X` affine, `SeparatedCoversAlgebraic` for
`Spec (Γ(X, 𝒪_X) ⧸ nilradical)` implies it for `X`. -/
theorem SeparatedCoversAlgebraic.of_quotient_nilradical (X : SchemeLFTℂ.{u}) [IsAffine X.obj.left]
    (h : SeparatedCoversAlgebraic
      (SchemeLFTℂ.specAlgebra X (Γ(X.obj.left, ⊤) ⧸ nilradical Γ(X.obj.left, ⊤)))) :
    SeparatedCoversAlgebraic X := by
  let R := Γ(X.obj.left, ⊤) ⧸ nilradical Γ(X.obj.left, ⊤)
  haveI : IsClosedImmersion (SchemeLFTℂ.specAlgebraHom X R).hom.left := by
    haveI := IsClosedImmersion.spec_of_surjective
      (CommRingCat.ofHom (algebraMap Γ(X.obj.left, ⊤) R)) Ideal.Quotient.mk_surjective
    change IsClosedImmersion (specAlgebraToBase X R)
    rw [specAlgebraToBase]
    infer_instance
  refine SeparatedCoversAlgebraic.of_isClosedImmersion (SchemeLFTℂ.specAlgebraHom X R) ?_ h
  change Function.Surjective (specAlgebraToBase X R).base
  rw [specAlgebraToBase, Scheme.Hom.comp_base, TopCat.coe_comp]
  refine (ConcreteCategory.bijective_of_isIso X.obj.left.isoSpec.inv.base).2.comp
    (surjective_Spec_map_base_of_ker_le_nilradical _ Ideal.Quotient.mk_surjective ?_)
  change RingHom.ker (Ideal.Quotient.mk _) ≤ _
  rw [Ideal.mk_ker]

attribute [local instance] MilnorPatching.quotientAlgebra in
/-- **Milnor squares.** For `X` reduced affine with `A = Γ(X, 𝒪_X)`, `A → S` finite and injective
and `I ⊆ A` an ideal of `S`, `SeparatedCoversAlgebraic` for `Spec S` and `Spec (A ⧸ I)` implies it
for `X`. -/
theorem SeparatedCoversAlgebraic.of_milnorSquare (X : SchemeLFTℂ.{u}) [IsAffine X.obj.left]
    [IsReduced Γ(X.obj.left, ⊤)] (S : Type u) [CommRing S] [Algebra Γ(X.obj.left, ⊤) S]
    [Module.Finite Γ(X.obj.left, ⊤) S] (hinj : Function.Injective (algebraMap Γ(X.obj.left, ⊤) S))
    (I : Ideal Γ(X.obj.left, ⊤))
    (hI : ∀ i ∈ I, ∀ s : S, ∃ r ∈ I,
      algebraMap Γ(X.obj.left, ⊤) S r = algebraMap Γ(X.obj.left, ⊤) S i * s)
    (hS : SeparatedCoversAlgebraic (SchemeLFTℂ.specAlgebra X S))
    (hC : SeparatedCoversAlgebraic (SchemeLFTℂ.specAlgebra X (Γ(X.obj.left, ⊤) ⧸ I))) :
    SeparatedCoversAlgebraic X := fun W hW ↦
  mem_essImage_of_milnorSquare X S hinj I hI W
    (hS _ (isSeparatedMap_pullbackFiniteEtaleOver W hW _))
    (hC _ (isSeparatedMap_pullbackFiniteEtaleOver W hW _))

/-- The identity cover `X ⟶ X`. -/
def SchemeLFTℂ.FiniteEtaleOver.id (X : SchemeLFTℂ.{u}) : SchemeLFTℂ.FiniteEtaleOver X :=
  MorphismProperty.Over.mk ⊤ (𝟙 X) (MorphismProperty.id_mem _ X)

/-- **The empty scheme**: every finite étale cover of the analytification of an empty scheme is
algebraic. -/
theorem separatedCoversAlgebraic_of_isEmpty (X : SchemeLFTℂ.{u}) (hX : IsEmpty X.obj.left) :
    SeparatedCoversAlgebraic X := by
  intro W _
  have hE : IsEmpty (analytification.obj X) :=
    @Function.isEmpty _ ↑↑(schemeToOverSpec.obj X.obj).left.toPresheafedSpace hX
      (analytificationπ X).left.base
  haveI := isIso_of_isEmpty W.hom hE
  refine ⟨SchemeLFTℂ.FiniteEtaleOver.id X, ⟨MorphismProperty.Over.isoMk (asIso W.hom).symm ?_⟩⟩
  exact (IsIso.inv_hom_id W.hom).trans (analytification.map_id X).symm

/-- An affine scheme with trivial ring of global sections satisfies
`SeparatedCoversAlgebraic`. -/
theorem separatedCoversAlgebraic_of_subsingleton (X : SchemeLFTℂ.{u}) [IsAffine X.obj.left]
    [Subsingleton Γ(X.obj.left, ⊤)] : SeparatedCoversAlgebraic X :=
  haveI : IsEmpty (PrimeSpectrum Γ(X.obj.left, ⊤)) := inferInstance
  separatedCoversAlgebraic_of_isEmpty X
    (@Function.isEmpty _ (PrimeSpectrum Γ(X.obj.left, ⊤)) this X.obj.left.isoSpec.hom.base)

/-- **The essential image of the analytification is stable under pullback**: if `W` is the
analytification of a finite étale cover of `X`, then so is its pullback along `f^an`. -/
theorem mem_essImage_pullbackFiniteEtaleOver {X Y : SchemeLFTℂ.{u}}
    {W : AnalyticSpace.FiniteEtaleOver (analytification.obj X)}
    (hW : (analytificationFiniteEtaleOver X).essImage W) (f : Y ⟶ X) :
    (analytificationFiniteEtaleOver Y).essImage (pullbackFiniteEtaleOver W f) := by
  obtain ⟨Z, ⟨e⟩⟩ := hW
  haveI : AlgebraicGeometry.IsFinite Z.hom.hom.left := Z.prop.1
  haveI : Etale Z.hom.hom.left := Z.prop.2
  have hZ' : SchemeLFTℂ.isFiniteEtale (SchemeLFTℂ.fibreProdSnd Z.hom f) := by
    change AlgebraicGeometry.IsFinite (pullback.snd Z.hom.hom.left f.hom.left) ∧
      Etale (pullback.snd Z.hom.hom.left f.hom.left)
    exact ⟨inferInstance, inferInstance⟩
  let Z' : SchemeLFTℂ.FiniteEtaleOver Y := MorphismProperty.Over.mk ⊤ _ hZ'
  let eL := (MorphismProperty.Over.forget _ _ _ ⋙ CategoryTheory.Over.forget _).mapIso e
  have hw : e.hom.left ≫ W.hom = analytification.map Z.hom := MorphismProperty.Over.w e.hom
  have hP : IsPullback (analytification.map (SchemeLFTℂ.fibreProdFst Z.hom f) ≫ e.hom.left)
      (analytification.map (SchemeLFTℂ.fibreProdSnd Z.hom f)) W.hom (analytification.map f) :=
    (isPullback_analytification_map_fibreProd Z.hom f).of_iso (Iso.refl _) eL (Iso.refl _)
      (Iso.refl _) (by simp [eL]) (by simp) ((Category.comp_id _).trans hw.symm)
      (Category.comp_id _)
  refine ⟨Z', ⟨MorphismProperty.Over.isoMk hP.isoPullback ?_⟩⟩
  exact hP.isoPullback_hom_snd

end

end ComplexAnalytic
