/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.GAGA.ClosedImmersion
import Oka.Analytification.RET.FiniteEtaleFunctor
import Oka.AnalyticSpace.CoveringSpaceHomeomorph
import Oka.RingTheory.EtaleNilpotentLift

/-!
# Essential surjectivity along surjective closed immersions

Let `i : Z ⟶ X` be a closed immersion of schemes locally of finite type over `ℂ` which is
surjective on underlying spaces, with `X` affine. If every finite étale cover of `Z^an` is the
analytification of a finite étale cover of `Z`, then the same holds for `X`.

The analytification `i^an` is a homeomorphism, so a finite étale cover `W` of `X^an` transports to
a finite étale cover of `Z^an`, which is algebraic, say `Y₀^an`. The cover `Y₀ ⟶ Z` lifts to a
finite étale cover `Y ⟶ X` together with a surjective closed immersion `Y₀ ⟶ Y` over `i`
(`Algebra.Etale.exists_lift_of_ker_le_nilradical`), and then `Y^an ≅ W` because a finite étale
cover is determined by its underlying topological cover.

## Main results

- `ComplexAnalytic.isHomeomorph_analytification_map_of_surjective`: the analytification of a
  surjective closed immersion is a homeomorphism.
- `ComplexAnalytic.SchemeLFTℂ.FiniteEtaleOver.exists_lift`: finite étale covers lift along
  surjective closed immersions into affine schemes.
- `ComplexAnalytic.essSurj_analytificationFiniteEtaleOver_of_isClosedImmersion`: essential
  surjectivity of the analytification on finite étale covers descends along `i`.
-/

open CategoryTheory AlgebraicGeometry

universe u

namespace ComplexAnalytic

open AnalyticSpace

noncomputable section

variable {Z X : SchemeLFTℂ.{u}} (i : Z ⟶ X) [IsClosedImmersion i.hom.left]

/-- **The analytification of a surjective closed immersion is a homeomorphism.** -/
theorem isHomeomorph_analytification_map_of_surjective
    (hi : Function.Surjective i.hom.left.base) :
    IsHomeomorph ((analytification.map i).toLRSHom.base :
      analytification.obj Z → analytification.obj X) := by
  have h := isClosedEmbedding_analytification_map i
  refine isHomeomorph_iff_isEmbedding_surjective.mpr ⟨h.isEmbedding, fun x ↦ ?_⟩
  have : x ∈ Set.range (analytification.map i).toLRSHom.base := by
    rw [range_analytification_map_of_isClosedImmersion, hi.range_eq]
    trivial
  exact this

/-- The kernel of the map on global sections of a surjective closed immersion consists of
nilpotent elements. -/
lemma ker_appTop_le_nilradical {Z X : Scheme.{u}} (i : Z ⟶ X) [IsAffine X]
    (hi : Function.Surjective i.base) :
    RingHom.ker i.appTop.hom ≤ nilradical Γ(X, ⊤) := by
  intro a ha
  rw [mem_nilradical, Scheme.isNilpotent_iff_basicOpen_eq_bot]
  have h : i ⁻¹ᵁ X.basicOpen a = ⊥ := by
    rw [Scheme.preimage_basicOpen_top, RingHom.mem_ker.mp ha, Scheme.basicOpen_zero]
  refine eq_bot_iff.mpr fun x hx ↦ ?_
  obtain ⟨z, rfl⟩ := hi x
  have : z ∈ i ⁻¹ᵁ X.basicOpen a := hx
  rw [h] at this
  exact this

/-- The underlying map of `Spec` of a surjective ring map with kernel contained in the nilradical
is surjective. -/
lemma surjective_Spec_map_base_of_ker_le_nilradical {R S : CommRingCat.{u}} (f : R ⟶ S)
    (hf : Function.Surjective f.hom) (hker : RingHom.ker f.hom ≤ nilradical R) :
    Function.Surjective (Spec.map f).base := by
  intro q
  have hq : RingHom.ker f.hom ≤ q.asIdeal := hker.trans (nilradical_le_prime _)
  have hp : (Ideal.map f.hom q.asIdeal).IsPrime := Ideal.map_isPrime_of_surjective hf hq
  refine ⟨⟨Ideal.map f.hom q.asIdeal, hp⟩, PrimeSpectrum.ext ?_⟩
  change Ideal.comap f.hom (Ideal.map f.hom q.asIdeal) = q.asIdeal
  rw [Ideal.comap_map_of_surjective' f.hom hf, sup_eq_left.mpr hq]

namespace SchemeLFTℂ.FiniteEtaleOver

variable [IsAffine X.obj.left]

/-- **Finite étale covers lift along surjective closed immersions into affine schemes.** For a
finite étale cover `Y₀ ⟶ Z` there is a finite étale cover `Y ⟶ X` and a surjective closed
immersion `Y₀ ⟶ Y` over `i`. -/
theorem exists_lift (hi : Function.Surjective i.hom.left.base)
    (Y₀ : SchemeLFTℂ.FiniteEtaleOver Z) :
    ∃ (Y : SchemeLFTℂ.FiniteEtaleOver X) (j : Y₀.left ⟶ Y.left),
      IsClosedImmersion j.hom.left ∧ Function.Surjective j.hom.left.base ∧
        j ≫ Y.hom = Y₀.hom ≫ i := by
  obtain ⟨hZ, hπ⟩ := IsClosedImmersion.isAffine_surjective_of_isAffine i.hom.left
  let f : Y₀.left.obj.left ⟶ Z.obj.left := Y₀.hom.hom.left
  haveI : IsFinite f := Y₀.prop.1
  haveI : Etale f := Y₀.prop.2
  haveI : IsAffine Y₀.left.obj.left := isAffine_of_isAffineHom f
  let A := Γ(X.obj.left, ⊤)
  let A₀ := Γ(Z.obj.left, ⊤)
  let B₀ := Γ(Y₀.left.obj.left, ⊤)
  letI : Algebra A₀ B₀ := f.appTop.hom.toAlgebra
  haveI : Algebra.Etale A₀ B₀ :=
    (HasRingHomProperty.iff_of_isAffine (P := @Etale)).mp ‹Etale f›
  haveI : Module.Finite A₀ B₀ := f.finite_appTop
  obtain ⟨B, _, _, φ, hEt, hfin, hφs, hφker, hcomp⟩ :=
    Algebra.Etale.exists_lift_of_ker_le_nilradical (B₀ := B₀) i.hom.left.appTop.hom hπ
      (ker_appTop_le_nilradical i.hom.left hi)
  let α : A ⟶ CommRingCat.of B := CommRingCat.ofHom (algebraMap A B)
  let φ' : CommRingCat.of B ⟶ B₀ := CommRingCat.ofHom φ
  haveI : IsFinite (Spec.map α) := (IsFinite.SpecMap_iff α).mpr
    (RingHom.finite_algebraMap.mpr hfin)
  haveI : Etale (Spec.map α) := (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
    (RingHom.etale_algebraMap.mpr hEt)
  let q : Spec (CommRingCat.of B) ⟶ X.obj.left := Spec.map α ≫ X.obj.left.isoSpec.inv
  let Yl : SchemeLFTℂ.{u} := ⟨Over.mk (q ≫ X.obj.hom), by
    haveI : LocallyOfFiniteType X.obj.hom := X.property
    change LocallyOfFiniteType (q ≫ X.obj.hom)
    infer_instance⟩
  let Yh : Yl ⟶ X := ObjectProperty.homMk (Over.homMk q rfl)
  have hYh : SchemeLFTℂ.isFiniteEtale Yh := by
    change AlgebraicGeometry.IsFinite q ∧ Etale q
    exact ⟨inferInstance, inferInstance⟩
  let Y : SchemeLFTℂ.FiniteEtaleOver X := MorphismProperty.Over.mk ⊤ Yh hYh
  let jl : Y₀.left.obj.left ⟶ Spec (CommRingCat.of B) :=
    Y₀.left.obj.left.isoSpec.hom ≫ Spec.map φ'
  have hsq : jl ≫ q = f ≫ i.hom.left := by
    have hαφ : α ≫ φ' = (f ≫ i.hom.left).appTop := by
      rw [Scheme.Hom.comp_appTop]
      ext1
      exact hcomp
    simp only [jl, q, Category.assoc]
    rw [← Spec.map_comp_assoc, hαφ, ← Category.assoc,
      Scheme.isoSpec_hom_naturality, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  let j : Y₀.left ⟶ Y.left := ObjectProperty.homMk (Over.homMk jl (by
    change jl ≫ q ≫ X.obj.hom = Y₀.left.obj.hom
    rw [← Category.assoc, hsq]
    refine (Category.assoc _ _ _).trans ?_
    exact congrArg (f ≫ ·) (Over.w i.hom) |>.trans (Over.w Y₀.hom.hom)))
  refine ⟨Y, j, ?_, ?_, ?_⟩
  · haveI : IsClosedImmersion (Spec.map φ') := IsClosedImmersion.spec_of_surjective φ' hφs
    change IsClosedImmersion jl
    infer_instance
  · change Function.Surjective (Y₀.left.obj.left.isoSpec.hom ≫ Spec.map φ').base
    rw [Scheme.Hom.comp_base, TopCat.coe_comp]
    exact (surjective_Spec_map_base_of_ker_le_nilradical φ' hφs hφker).comp
      (ConcreteCategory.bijective_of_isIso Y₀.left.obj.left.isoSpec.hom.base).2
  · ext1
    exact Over.OverMorphism.ext hsq

end SchemeLFTℂ.FiniteEtaleOver

/-- **Essential surjectivity descends along surjective closed immersions into affine schemes.**
If `i : Z ⟶ X` is a closed immersion, surjective on underlying spaces, with `X` affine, and every
finite étale cover of `Z^an` is the analytification of a finite étale cover of `Z`, then every
finite étale cover of `X^an` is the analytification of a finite étale cover of `X`. -/
theorem essSurj_analytificationFiniteEtaleOver_of_isClosedImmersion [IsAffine X.obj.left]
    (hi : Function.Surjective i.hom.left.base) [(analytificationFiniteEtaleOver Z).EssSurj] :
    (analytificationFiniteEtaleOver X).EssSurj where
  mem_essImage W := by
    let hg := isHomeomorph_analytification_map_of_surjective i hi
    let W' := FiniteEtaleOver.transport (analytification.map i) hg W
    let Y₀ := (analytificationFiniteEtaleOver Z).objPreimage W'
    let e := (analytificationFiniteEtaleOver Z).objObjPreimageIso W'
    obtain ⟨Y, j, hj, hjs, hjY⟩ := SchemeLFTℂ.FiniteEtaleOver.exists_lift i hi Y₀
    obtain ⟨e'⟩ := FiniteEtaleOver.nonempty_iso_of_iso_transport (analytification.map i) hg e
      (A := (analytificationFiniteEtaleOver X).obj Y) (analytification.map j)
      (isHomeomorph_analytification_map_of_surjective j hjs) (by
        change analytification.map j ≫ analytification.map Y.hom =
          analytification.map Y₀.hom ≫ analytification.map i
        exact (Functor.map_comp _ _ _).symm.trans
          ((congrArg analytification.map hjY).trans (Functor.map_comp _ _ _)))
    exact ⟨Y, ⟨e'⟩⟩

end

end ComplexAnalytic
