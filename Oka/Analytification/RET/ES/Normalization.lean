/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.ES.Algebraize
import Oka.Analytification.RET.ES.Local
import Oka.Analytification.RET.ES.NilThickening
import Oka.Analytification.RET.FullyFaithful
import Oka.AnalyticSpace.CoveringSpaceHomeomorph
import Oka.AnalyticSpace.FiniteEtaleBaseChange
import Oka.RingTheory.MilnorPatching
import Oka.RingTheory.FiniteNormalization

/-!
# Essential surjectivity across a Milnor square

Let `X` be a reduced affine scheme of finite type over `ℂ` with `A = Γ(X, 𝒪_X)`, let `A → S` be
finite and injective and let `I ⊆ A` be an ideal which is also an ideal of `S`, so that
`A = S ×_{S ⧸ I S} A ⧸ I`. If a finite étale cover `W` of `X^an` becomes algebraic after pulling
back to `(Spec S)^an` and to `(Spec (A ⧸ I))^an`, then `W` is algebraic
(`ComplexAnalytic.mem_essImage_of_milnorSquare`). Taking for `S` the normalisation of `A` and for
`I` the conductor, essential surjectivity of the analytification of finite étale covers of affine
schemes of dimension `≤ n` follows from the normal case in dimension `≤ n` and the general case in
dimension `< n` (`ComplexAnalytic.essSurj_of_ringKrullDim_le`).

The proof: the algebraic models `P` over `S` and `Q` over `A ⧸ I` (`ComplexAnalytic.CoverModel`)
both analytify to `W` over `(Spec (S ⧸ I S))^an`, so by full faithfulness of the analytification
over `Spec (S ⧸ I S)` they are identified there by an isomorphism
`(S ⧸ I S) ⊗[A ⧸ I] Q ≅ (S ⧸ I S) ⊗[S] P` compatible with the maps to `W`
(`ComplexAnalytic.CoverModel.exists_gluingEquiv`). Milnor patching
(`Oka/RingTheory/MilnorPatching.lean`) makes `B = P ×_{(S ⧸ I S) ⊗[S] P} Q` a finite étale
`A`-algebra with `S ⊗[A] B ≅ P` and `(A ⧸ I) ⊗[A] B ≅ Q`. The map `(Spec P)^an ⟶ W` is constant on
the fibres of the closed surjection `(Spec P)^an ⟶ (Spec B)^an`: away from `V(I)` these fibres are
points, and over `V(I)` the value is read off from `Q` through the gluing isomorphism. The induced
map `(Spec B)^an → W` is a bijective local homeomorphism over `X^an`, hence `W ≅ (Spec B)^an`.

## Main definitions

- `ComplexAnalytic.SchemeLFTℂ.specAlgebraMap`: `Spec` of a map of finite `Γ(X, 𝒪_X)`-algebras.
- `ComplexAnalytic.pullbackFiniteEtaleOver`: the pullback of a finite étale cover of `X^an` along
  the analytification of a morphism.
- `ComplexAnalytic.CoverModel`: an algebraic model of a finite étale cover of `X^an` over
  `Spec R`.

## Main results

- `ComplexAnalytic.isPullback_analytification_map_of_isPullback`: the analytification of a
  pullback square of schemes is a pullback square.
- `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.nonempty_iso_of_closed_surjective`: recognising
  a finite étale cover through a closed surjection.
- `ComplexAnalytic.mem_essImage_of_milnorSquare`: essential surjectivity across a Milnor square.
- `ComplexAnalytic.essSurj_of_isReduced_of_ringKrullDim_le`,
  `ComplexAnalytic.essSurj_of_ringKrullDim_le`: the induction step on the dimension.
-/

open CategoryTheory Limits Opposite AlgebraicGeometry TensorProduct

universe u

namespace ComplexAnalytic

open AnalyticSpace

noncomputable section

/-! ### `Spec` of algebra maps over an affine base -/

section SpecAlgebraMap

variable (X : SchemeLFTℂ.{u}) [IsAffine X.obj.left] {R₁ R₂ R₃ : Type u} [CommRing R₁]
  [CommRing R₂] [CommRing R₃] [Algebra Γ(X.obj.left, ⊤) R₁] [Algebra Γ(X.obj.left, ⊤) R₂]
  [Algebra Γ(X.obj.left, ⊤) R₃] [Module.Finite Γ(X.obj.left, ⊤) R₁]
  [Module.Finite Γ(X.obj.left, ⊤) R₂] [Module.Finite Γ(X.obj.left, ⊤) R₃]

/-- `Spec f : Spec R₂ ⟶ Spec R₁` of a map `f : R₁ → R₂` of finite `Γ(X, 𝒪_X)`-algebras, as a
morphism of schemes locally of finite type over `ℂ`. -/
def SchemeLFTℂ.specAlgebraMap (f : R₁ →ₐ[Γ(X.obj.left, ⊤)] R₂) :
    SchemeLFTℂ.specAlgebra X R₂ ⟶ SchemeLFTℂ.specAlgebra X R₁ :=
  ObjectProperty.homMk (Over.homMk (Spec.map (CommRingCat.ofHom f.toRingHom)) (by
    change Spec.map _ ≫ Spec.map _ ≫ X.obj.left.isoSpec.inv ≫ X.obj.hom =
      Spec.map _ ≫ X.obj.left.isoSpec.inv ≫ X.obj.hom
    rw [← Spec.map_comp_assoc]
    congr 2
    ext a
    exact f.commutes a))

@[simp]
lemma SchemeLFTℂ.specAlgebraMap_hom_left (f : R₁ →ₐ[Γ(X.obj.left, ⊤)] R₂) :
    (SchemeLFTℂ.specAlgebraMap X f).hom.left = Spec.map (CommRingCat.ofHom f.toRingHom) :=
  rfl

@[reassoc (attr := simp)]
lemma SchemeLFTℂ.specAlgebraMap_specAlgebraHom (f : R₁ →ₐ[Γ(X.obj.left, ⊤)] R₂) :
    SchemeLFTℂ.specAlgebraMap X f ≫ SchemeLFTℂ.specAlgebraHom X R₁ =
      SchemeLFTℂ.specAlgebraHom X R₂ := by
  ext1
  refine Over.OverMorphism.ext ?_
  change Spec.map _ ≫ Spec.map _ ≫ X.obj.left.isoSpec.inv = Spec.map _ ≫ X.obj.left.isoSpec.inv
  rw [← Spec.map_comp_assoc]
  congr 2
  ext a
  exact f.commutes a

@[reassoc (attr := simp)]
lemma SchemeLFTℂ.specAlgebraMap_comp (f : R₁ →ₐ[Γ(X.obj.left, ⊤)] R₂)
    (g : R₂ →ₐ[Γ(X.obj.left, ⊤)] R₃) :
    SchemeLFTℂ.specAlgebraMap X g ≫ SchemeLFTℂ.specAlgebraMap X f =
      SchemeLFTℂ.specAlgebraMap X (g.comp f) := by
  ext1
  refine Over.OverMorphism.ext ?_
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  rfl

/-- `Spec` of a finite étale algebra map is finite étale. -/
lemma SchemeLFTℂ.isFiniteEtale_specAlgebraMap (f : R₁ →ₐ[Γ(X.obj.left, ⊤)] R₂)
    (hf : f.toRingHom.Finite) (he : f.toRingHom.Etale) :
    SchemeLFTℂ.isFiniteEtale (SchemeLFTℂ.specAlgebraMap X f) :=
  ⟨(IsFinite.SpecMap_iff (CommRingCat.ofHom f.toRingHom)).2 hf,
    (HasRingHomProperty.Spec_iff (P := @Etale)).2 he⟩

/-- `Spec` of a finite algebra map is finite. -/
instance SchemeLFTℂ.isFinite_specAlgebraMap (f : R₁ →ₐ[Γ(X.obj.left, ⊤)] R₂) :
    AlgebraicGeometry.IsFinite (SchemeLFTℂ.specAlgebraMap X f).hom.left := by
  letI := f.toRingHom.toAlgebra
  haveI : IsScalarTower Γ(X.obj.left, ⊤) R₁ R₂ :=
    IsScalarTower.of_algebraMap_eq fun a ↦ (f.commutes a).symm
  haveI : Module.Finite R₁ R₂ := Module.Finite.of_restrictScalars_finite Γ(X.obj.left, ⊤) R₁ R₂
  exact (IsFinite.SpecMap_iff (CommRingCat.ofHom f.toRingHom)).2 (RingHom.finite_algebraMap.2 ‹_›)

end SpecAlgebraMap

/-! ### Points -/

section Points

variable {X : SchemeLFTℂ.{u}} [IsAffine X.obj.left] {R₁ R₂ : Type u} [CommRing R₁]
  [CommRing R₂] [Algebra Γ(X.obj.left, ⊤) R₁] [Algebra Γ(X.obj.left, ⊤) R₂]
  [Module.Finite Γ(X.obj.left, ⊤) R₁] [Module.Finite Γ(X.obj.left, ⊤) R₂]

/-- The prime ideal of `R` corresponding to a point of `(Spec R)^an`. -/
def specPt (y : analytification.obj (SchemeLFTℂ.specAlgebra X R₁)) : PrimeSpectrum R₁ :=
  (analytificationπLRS _).base y

/-- The prime ideal of `Γ(X, 𝒪_X)` corresponding to a point of `X^an`. -/
def affinePt (x : analytification.obj X) : PrimeSpectrum Γ(X.obj.left, ⊤) :=
  X.obj.left.isoSpec.hom.base ((analytificationπLRS X).base x)

lemma specPt_injective :
    Function.Injective (specPt : analytification.obj (SchemeLFTℂ.specAlgebra X R₁) → _) :=
  analytificationπ_base_injective _

lemma affinePt_injective : Function.Injective (affinePt : analytification.obj X → _) :=
  (ConcreteCategory.bijective_of_isIso X.obj.left.isoSpec.hom.base).1.comp
    (analytificationπ_base_injective X)

lemma specPt_specAlgebraMap (f : R₁ →ₐ[Γ(X.obj.left, ⊤)] R₂)
    (y : analytification.obj (SchemeLFTℂ.specAlgebra X R₂)) :
    specPt ((analytification.map (SchemeLFTℂ.specAlgebraMap X f)).toLRSHom.base y) =
      PrimeSpectrum.comap f.toRingHom (specPt y) :=
  congrArg (fun φ ↦ φ.base y) (analytificationπLRS_naturality (SchemeLFTℂ.specAlgebraMap X f))

lemma affinePt_specAlgebraHom (y : analytification.obj (SchemeLFTℂ.specAlgebra X R₁)) :
    affinePt ((analytification.map (SchemeLFTℂ.specAlgebraHom X R₁)).toLRSHom.base y) =
      PrimeSpectrum.comap (algebraMap Γ(X.obj.left, ⊤) R₁) (specPt y) := by
  have h := congrArg (fun φ ↦ φ.base y)
    (analytificationπLRS_naturality (SchemeLFTℂ.specAlgebraHom X R₁))
  change X.obj.left.isoSpec.hom.base ((Hom.toLRSHom (analytification.map
    (SchemeLFTℂ.specAlgebraHom X R₁)) ≫ analytificationπLRS X).base y) = _
  rw [h]
  change ((Spec.map (CommRingCat.ofHom (algebraMap Γ(X.obj.left, ⊤) R₁)) ≫
    X.obj.left.isoSpec.inv) ≫ X.obj.left.isoSpec.hom).base (specPt y) = _
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

lemma isMaximal_specPt (y : analytification.obj (SchemeLFTℂ.specAlgebra X R₁)) :
    (specPt y).asIdeal.IsMaximal :=
  (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).1
    ((mem_range_analytificationπ_base_iff _ _).1 ⟨y, rfl⟩)

lemma exists_specPt_eq (p : PrimeSpectrum R₁) (hp : p.asIdeal.IsMaximal) :
    ∃ y : analytification.obj (SchemeLFTℂ.specAlgebra X R₁), specPt y = p :=
  (mem_range_analytificationπ_base_iff (SchemeLFTℂ.specAlgebra X R₁) p).2
    ((PrimeSpectrum.isClosed_singleton_iff_isMaximal _).2 hp)

lemma isMaximal_affinePt (x : analytification.obj X) : (affinePt x).asIdeal.IsMaximal := by
  refine (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).1 ?_
  have h := (mem_range_analytificationπ_base_iff X ((analytificationπLRS X).base x)).1 ⟨x, rfl⟩
  have := (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso X.obj.left.isoSpec)).isClosedMap _ h
  rwa [Set.image_singleton] at this

/-- A point of `(Spec R₁)^an` whose prime contains the kernel of a surjection `f : R₁ → R₂` comes
from `(Spec R₂)^an`. -/
lemma exists_specAlgebraMap_eq (f : R₁ →ₐ[Γ(X.obj.left, ⊤)] R₂)
    (hf : Function.Surjective f) (y : analytification.obj (SchemeLFTℂ.specAlgebra X R₁))
    (hy : RingHom.ker f.toRingHom ≤ (specPt y).asIdeal) :
    ∃ z, (analytification.map (SchemeLFTℂ.specAlgebraMap X f)).toLRSHom.base z = y := by
  haveI := isMaximal_specPt y
  have hmax : ((specPt y).asIdeal.map f.toRingHom).IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le hf hy
  obtain ⟨z, hz⟩ := exists_specPt_eq (X := X) ⟨_, hmax.isPrime⟩ hmax
  refine ⟨z, specPt_injective ?_⟩
  rw [specPt_specAlgebraMap, hz]
  ext1
  exact (Ideal.comap_map_of_surjective' _ hf _).trans (sup_eq_left.2 hy)

end Points

/-! ### Points of pullbacks along finite étale morphisms -/

section PullbackPoints

variable {P X Y Z : AnalyticSpace.{u}} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
  [hf : IsFiniteEtale f]

/-- A pair of points with the same image lifts to a pullback along a finite étale morphism. -/
lemma exists_base_eq_of_isPullback (h : IsPullback fst snd f g) {a : X} {b : Y}
    (hab : f.toLRSHom.base a = g.toLRSHom.base b) :
    ∃ p, fst.toLRSHom.base p = a ∧ snd.toLRSHom.base p = b := by
  let e := h.isoIsPullback _ _ (isPullback_baseChange f g)
  let z : baseChange f g := ⟨(a, b), hab⟩
  refine ⟨e.inv.toLRSHom.base z, ?_, ?_⟩
  · have := congrArg (fun φ : baseChange f g ⟶ X ↦ φ.toLRSHom.base z)
      (h.isoIsPullback_inv_fst _ _ (isPullback_baseChange f g))
    exact this.trans (by rw [base_baseChangeFst]; rfl)
  · have := congrArg (fun φ : baseChange f g ⟶ Y ↦ φ.toLRSHom.base z)
      (h.isoIsPullback_inv_snd _ _ (isPullback_baseChange f g))
    exact this.trans (by rw [base_baseChangeSnd]; rfl)

/-- A point of a pullback along a finite étale morphism is determined by its projections. -/
lemma base_ext_of_isPullback (h : IsPullback fst snd f g) {p p' : P}
    (h₁ : fst.toLRSHom.base p = fst.toLRSHom.base p')
    (h₂ : snd.toLRSHom.base p = snd.toLRSHom.base p') : p = p' := by
  let e := h.isoIsPullback _ _ (isPullback_baseChange f g)
  have hf (q : P) : ((e.hom.toLRSHom.base q : baseChange f g) :
      Function.Pullback f.toLRSHom.base g.toLRSHom.base).1.1 = fst.toLRSHom.base q := by
    have := congrArg (fun φ : P ⟶ X ↦ φ.toLRSHom.base q)
      (h.isoIsPullback_hom_fst _ _ (isPullback_baseChange f g))
    change (baseChangeFst f g).toLRSHom.base (e.hom.toLRSHom.base q) = _ at this
    rw [base_baseChangeFst] at this
    exact this
  have hs (q : P) : ((e.hom.toLRSHom.base q : baseChange f g) :
      Function.Pullback f.toLRSHom.base g.toLRSHom.base).1.2 = snd.toLRSHom.base q := by
    have := congrArg (fun φ : P ⟶ Y ↦ φ.toLRSHom.base q)
      (h.isoIsPullback_hom_snd _ _ (isPullback_baseChange f g))
    change (baseChangeSnd f g).toLRSHom.base (e.hom.toLRSHom.base q) = _ at this
    rw [base_baseChangeSnd] at this
    exact this
  refine (isHomeomorph_base_of_isIso e.hom).injective ?_
  exact Subtype.ext (Prod.ext ((hf p).trans (h₁.trans (hf p').symm))
    ((hs p).trans (h₂.trans (hs p').symm)))

end PullbackPoints

/-! ### Analytification of pullback squares -/

section AnalytificationPullback

variable {P A B Z : SchemeLFTℂ.{u}} {fst : P ⟶ A} {snd : P ⟶ B} {f : A ⟶ Z} {g : B ⟶ Z}

/-- **The analytification of a pullback square of schemes is a pullback square.** -/
theorem isPullback_analytification_map_of_isPullback
    (h : IsPullback fst.hom.left snd.hom.left f.hom.left g.hom.left) :
    IsPullback (analytification.map fst) (analytification.map snd) (analytification.map f)
      (analytification.map g) := by
  let e : P ≅ SchemeLFTℂ.fibreProd f g :=
    (ObjectProperty.fullyFaithfulι _).preimageIso (Over.isoMk h.isoPullback (by
      change h.isoPullback.hom ≫ pullback.fst _ _ ≫ A.obj.hom = P.obj.hom
      rw [IsPullback.isoPullback_hom_fst_assoc]
      exact Over.w fst.hom))
  have he₁ : e.inv ≫ fst = SchemeLFTℂ.fibreProdFst f g := by
    ext1
    exact Over.OverMorphism.ext (h.isoPullback_inv_fst)
  have he₂ : e.inv ≫ snd = SchemeLFTℂ.fibreProdSnd f g := by
    ext1
    exact Over.OverMorphism.ext (h.isoPullback_inv_snd)
  refine (isPullback_analytification_map_fibreProd f g).of_iso
    (analytification.mapIso e).symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp [← he₁]
  · simp [← he₂]
  · simp
  · simp

variable (X : SchemeLFTℂ.{u}) [IsAffine X.obj.left] {R₀ R₁ R₂ R₃ : Type u} [CommRing R₀]
  [CommRing R₁] [CommRing R₂] [CommRing R₃] [Algebra Γ(X.obj.left, ⊤) R₀]
  [Algebra Γ(X.obj.left, ⊤) R₁] [Algebra Γ(X.obj.left, ⊤) R₂] [Algebra Γ(X.obj.left, ⊤) R₃]
  [Module.Finite Γ(X.obj.left, ⊤) R₀] [Module.Finite Γ(X.obj.left, ⊤) R₁]
  [Module.Finite Γ(X.obj.left, ⊤) R₂] [Module.Finite Γ(X.obj.left, ⊤) R₃]

/-- The analytification of `Spec` of a pushout square of finite `Γ(X, 𝒪_X)`-algebras is a
pullback square. -/
theorem isPullback_specAlgebraMap (f₁ : R₀ →ₐ[Γ(X.obj.left, ⊤)] R₁)
    (f₂ : R₀ →ₐ[Γ(X.obj.left, ⊤)] R₂) (g₁ : R₁ →ₐ[Γ(X.obj.left, ⊤)] R₃)
    (g₂ : R₂ →ₐ[Γ(X.obj.left, ⊤)] R₃)
    (h : IsPushout (CommRingCat.ofHom f₁.toRingHom) (CommRingCat.ofHom f₂.toRingHom)
      (CommRingCat.ofHom g₁.toRingHom) (CommRingCat.ofHom g₂.toRingHom)) :
    IsPullback (analytification.map (SchemeLFTℂ.specAlgebraMap X g₁))
      (analytification.map (SchemeLFTℂ.specAlgebraMap X g₂))
      (analytification.map (SchemeLFTℂ.specAlgebraMap X f₁))
      (analytification.map (SchemeLFTℂ.specAlgebraMap X f₂)) :=
  isPullback_analytification_map_of_isPullback (isPullback_SpecMap_of_isPushout _ _ _ _ h)

/-- The analytification of `Spec` of a pushout square of finite `Γ(X, 𝒪_X)`-algebras with
`Γ(X, 𝒪_X)` in the corner is a pullback square over `X^an`. -/
theorem isPullback_specAlgebraHom (g₁ : R₁ →ₐ[Γ(X.obj.left, ⊤)] R₃)
    (g₂ : R₂ →ₐ[Γ(X.obj.left, ⊤)] R₃)
    (h : IsPushout (CommRingCat.ofHom (algebraMap Γ(X.obj.left, ⊤) R₁))
      (CommRingCat.ofHom (algebraMap Γ(X.obj.left, ⊤) R₂))
      (CommRingCat.ofHom g₁.toRingHom) (CommRingCat.ofHom g₂.toRingHom)) :
    IsPullback (analytification.map (SchemeLFTℂ.specAlgebraMap X g₁))
      (analytification.map (SchemeLFTℂ.specAlgebraMap X g₂))
      (analytification.map (SchemeLFTℂ.specAlgebraHom X R₁))
      (analytification.map (SchemeLFTℂ.specAlgebraHom X R₂)) := by
  refine isPullback_analytification_map_of_isPullback ?_
  exact (isPullback_SpecMap_of_isPushout _ _ _ _ h).of_iso (Iso.refl _) (Iso.refl _)
    (Iso.refl _) X.obj.left.isoSpec.symm ((Category.comp_id _).trans (Category.id_comp _).symm)
    ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.id_comp _).symm
    (Category.id_comp _).symm

/-- A square of algebras is a pushout if the induced map from the tensor product is bijective. -/
theorem isPushout_of_bijective_productMap {R : Type u} [CommRing R] [Algebra R R₁]
    [Algebra R R₂] [Algebra R R₃] (g₁ : R₁ →ₐ[R] R₃) (g₂ : R₂ →ₐ[R] R₃)
    (h : Function.Bijective (Algebra.TensorProduct.productMap g₁ g₂)) :
    IsPushout (CommRingCat.ofHom (algebraMap R R₁)) (CommRingCat.ofHom (algebraMap R R₂))
      (CommRingCat.ofHom g₁.toRingHom) (CommRingCat.ofHom g₂.toRingHom) :=
  (CommRingCat.isPushout_tensorProduct R R₁ R₂).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (AlgEquiv.ofBijective _ h).toRingEquiv.toCommRingCatIso (by simp) (by simp)
    (by ext x; simp) (by ext x; simp)

end AnalytificationPullback

/-! ### Algebraic models of covers over `Spec` of a finite algebra -/

section CoverModel

/-- The pullback `W ×_{X^an} Y^an` of a finite étale cover `W` of `X^an` along the analytification
of a morphism `f : Y ⟶ X`, as a finite étale cover of `Y^an`. -/
def pullbackFiniteEtaleOver {X Y : SchemeLFTℂ.{u}}
    (W : AnalyticSpace.FiniteEtaleOver (analytification.obj X)) (f : Y ⟶ X) :
    AnalyticSpace.FiniteEtaleOver (analytification.obj Y) :=
  haveI : IsFiniteEtale W.hom := W.prop
  MorphismProperty.Over.mk ⊤ (pullback.snd W.hom (analytification.map f))
    (isFiniteEtale_pullback_snd_of_isFiniteEtale _ _)

variable (X : SchemeLFTℂ.{u}) [IsAffine X.obj.left] (R : Type u) [CommRing R]
  [Algebra Γ(X.obj.left, ⊤) R] [Module.Finite Γ(X.obj.left, ⊤) R]
  (W : AnalyticSpace.FiniteEtaleOver (analytification.obj X))

/-- **An algebraic model of `W` over `Spec R`**: a finite étale `R`-algebra `P` together with a
morphism `(Spec P)^an ⟶ W` identifying `(Spec P)^an` with `W ×_{X^an} (Spec R)^an`. -/
structure CoverModel where
  /-- The algebra. -/
  P : Type u
  [commRing : CommRing P]
  [algebra : Algebra R P]
  [algebraBase : Algebra Γ(X.obj.left, ⊤) P]
  [isScalarTower : IsScalarTower Γ(X.obj.left, ⊤) R P]
  [finite : Module.Finite R P]
  [finiteBase : Module.Finite Γ(X.obj.left, ⊤) P]
  [etale : Algebra.Etale R P]
  /-- The morphism to `W`. -/
  g : analytification.obj (SchemeLFTℂ.specAlgebra X P) ⟶ W.left
  isPullback : IsPullback g
    (analytification.map (SchemeLFTℂ.specAlgebraMap X (IsScalarTower.toAlgHom _ R P)))
    W.hom (analytification.map (SchemeLFTℂ.specAlgebraHom X R))

attribute [instance] CoverModel.commRing CoverModel.algebra CoverModel.algebraBase
  CoverModel.isScalarTower CoverModel.finite CoverModel.finiteBase CoverModel.etale

variable {X R W}

/-- **A cover in the essential image has an algebraic model.** -/
theorem CoverModel.nonempty_of_mem_essImage
    (h : (analytificationFiniteEtaleOver (SchemeLFTℂ.specAlgebra X R)).essImage
      (pullbackFiniteEtaleOver W (SchemeLFTℂ.specAlgebraHom X R))) :
    Nonempty (CoverModel X R W) := by
  obtain ⟨Y, ⟨e⟩⟩ := h
  haveI : IsFiniteEtale W.hom := W.prop
  let f : Y.left.obj.left ⟶ Spec (CommRingCat.of R) := Y.hom.hom.left
  haveI : AlgebraicGeometry.IsFinite f := Y.prop.1
  haveI : Etale f := Y.prop.2
  haveI : IsAffine Y.left.obj.left := isAffine_of_isAffineHom f
  let φ : CommRingCat.of R ⟶ Γ(Y.left.obj.left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop
  let P : Type u := Γ(Y.left.obj.left, ⊤)
  letI : Algebra R P := φ.hom.toAlgebra
  letI : Algebra Γ(X.obj.left, ⊤) P :=
    ((algebraMap R P).comp (algebraMap Γ(X.obj.left, ⊤) R)).toAlgebra
  haveI : IsScalarTower Γ(X.obj.left, ⊤) R P := .of_algebraMap_eq fun _ ↦ rfl
  let eΓ : R ≃+* Γ(Spec (CommRingCat.of R), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv
  haveI : Module.Finite R P := RingHom.finite_algebraMap.1
    (RingHom.finite_respectsIso.2 f.appTop.hom eΓ f.finite_appTop)
  haveI : Algebra.Etale R P := RingHom.etale_algebraMap.1
    (RingHom.Etale.respectsIso.2 f.appTop.hom eΓ
      ((HasRingHomProperty.iff_of_isAffine (P := @Etale)).mp ‹Etale f›))
  haveI : Module.Finite Γ(X.obj.left, ⊤) P := Module.Finite.trans R P
  have hE : Y.left.obj.left.isoSpec.inv ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R P)) := by
    rw [← Scheme.isoSpec_inv_naturality, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
    rfl
  let τ : SchemeLFTℂ.specAlgebra X P ≅ Y.left :=
    (ObjectProperty.fullyFaithfulι _).preimageIso (Over.isoMk Y.left.obj.left.isoSpec.symm (by
      change Y.left.obj.left.isoSpec.inv ≫ Y.left.obj.hom =
        Spec.map _ ≫ X.obj.left.isoSpec.inv ≫ X.obj.hom
      have hw0 : f ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(X.obj.left, ⊤) R)) ≫
          X.obj.left.isoSpec.inv ≫ X.obj.hom = Y.left.obj.hom := Over.w Y.hom.hom
      rw [← hw0, ← Category.assoc, hE]
      change Spec.map _ ≫ Spec.map _ ≫ X.obj.left.isoSpec.inv ≫ X.obj.hom = _
      rw [← Spec.map_comp_assoc]
      rfl))
  have hτ : τ.hom ≫ Y.hom = SchemeLFTℂ.specAlgebraMap X (IsScalarTower.toAlgHom _ R P) := by
    ext1
    exact Over.OverMorphism.ext hE
  have hw : e.hom.left ≫ pullback.snd W.hom (analytification.map (SchemeLFTℂ.specAlgebraHom X R))
      = analytification.map Y.hom := MorphismProperty.Over.w e.hom
  let εe := (MorphismProperty.Over.forget _ _ _ ⋙ CategoryTheory.Over.forget _).mapIso e
  have hεe : εe.inv ≫ e.hom.left = 𝟙 _ := εe.inv_hom_id
  let ε := analytification.mapIso τ ≪≫ εe
  have hε : ε.inv ≫ analytification.map τ.hom ≫ e.hom.left = 𝟙 _ := by
    change εe.inv ≫ (analytification.mapIso τ).inv ≫ (analytification.mapIso τ).hom ≫
      e.hom.left = _
    exact (congrArg (εe.inv ≫ ·) (Iso.inv_hom_id_assoc _ _)).trans hεe
  refine ⟨⟨P, analytification.map τ.hom ≫ e.hom.left ≫ pullback.fst _ _, ?_⟩⟩
  refine (IsPullback.of_hasPullback W.hom
    (analytification.map (SchemeLFTℂ.specAlgebraHom X R))).of_iso ε.symm (Iso.refl _)
    (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)
  · exact (Category.comp_id _).trans ((reassoc_of% hε) (pullback.fst _ _)).symm
  · refine (Category.comp_id _).trans ?_
    have h2 : analytification.map (SchemeLFTℂ.specAlgebraMap X (IsScalarTower.toAlgHom _ R P)) =
        analytification.map τ.hom ≫ e.hom.left ≫ pullback.snd _ _ := by
      rw [← hτ]
      exact (Functor.map_comp _ _ _).trans (congrArg (analytification.map τ.hom ≫ ·) hw.symm)
    rw [h2]
    exact ((reassoc_of% hε) (pullback.snd _ _)).symm

end CoverModel

/-! ### Recognising a finite étale cover through a closed surjection -/

/-- **Recognising a finite étale cover through a closed surjection.** Let `V` and `W` be finite
étale covers of `T`, `q : Ṽ ⟶ V` a morphism which is closed and surjective on points and
`g : Ṽ ⟶ W` a morphism over `T`. If `g` is constant on the fibres of `q`, surjective, and
`g a = g b` implies `q a = q b`, then `V ≅ W`. -/
theorem AnalyticSpace.FiniteEtaleOver.nonempty_iso_of_closed_surjective {T : AnalyticSpace.{u}}
    (V W : AnalyticSpace.FiniteEtaleOver T) {V' : AnalyticSpace.{u}} (q : V' ⟶ V.left)
    (g : V' ⟶ W.left) (hqc : IsClosedMap q.toLRSHom.base)
    (hqs : Function.Surjective q.toLRSHom.base) (hcomm : g ≫ W.hom = q ≫ V.hom)
    (h₁ : ∀ a b, q.toLRSHom.base a = q.toLRSHom.base b → g.toLRSHom.base a = g.toLRSHom.base b)
    (h₂ : Function.Surjective g.toLRSHom.base)
    (h₃ : ∀ a b, g.toLRSHom.base a = g.toLRSHom.base b → q.toLRSHom.base a = q.toLRSHom.base b) :
    Nonempty (V ≅ W) := by
  choose sec hsec using hqs
  let g₀ : V.left → W.left := fun v ↦ g.toLRSHom.base (sec v)
  have hg₀ (a : V') : g₀ (q.toLRSHom.base a) = g.toLRSHom.base a := h₁ _ _ (hsec _)
  have hcont : Continuous g₀ := by
    refine ((hqc.isQuotientMap q.toLRSHom.base.hom.continuous
      fun v ↦ ⟨sec v, hsec v⟩).continuous_iff).2 ?_
    have : g₀ ∘ q.toLRSHom.base = g.toLRSHom.base := funext hg₀
    rw [this]
    exact g.toLRSHom.base.hom.continuous
  have hover (v : V.left) : W.hom.toLRSHom.base (g₀ v) = V.hom.toLRSHom.base v := by
    have := congrArg (fun φ : V' ⟶ T ↦ φ.toLRSHom.base (sec v)) hcomm
    exact this.trans (congrArg V.hom.toLRSHom.base (hsec v))
  have hbij : Function.Bijective g₀ := by
    refine ⟨fun v₁ v₂ h ↦ ?_, fun w ↦ ?_⟩
    · rw [← hsec v₁, ← hsec v₂]
      exact h₃ _ _ h
    · obtain ⟨a, rfl⟩ := h₂ w
      exact ⟨_, hg₀ a⟩
  haveI : IsLocalIso V.hom := V.prop.isLocalIso
  haveI : IsLocalIso W.hom := W.prop.isLocalIso
  have hloc : IsLocalHomeomorph g₀ := by
    refine IsLocalHomeomorph.of_comp ?_ (IsLocalIso.isLocalHomeomorph (f := W.hom)) hcont
    have : W.hom.toLRSHom.base ∘ g₀ = V.hom.toLRSHom.base := funext hover
    exact (congrArg IsLocalHomeomorph this).mpr (IsLocalIso.isLocalHomeomorph (f := V.hom))
  exact ⟨AnalyticSpace.FiniteEtaleOver.isoOfHomeomorph V W
    ((Equiv.ofBijective g₀ hbij).toHomeomorphOfContinuousOpen hcont hloc.isOpenMap) hover⟩

/-! ### Points of the Milnor square -/

section MilnorPoints

attribute [local instance] MilnorPatching.quotientAlgebra

variable {X : SchemeLFTℂ.{u}} [IsAffine X.obj.left] {S : Type u} [CommRing S]
  [Algebra Γ(X.obj.left, ⊤) S] [Module.Finite Γ(X.obj.left, ⊤) S]

instance (R T : Type*) [CommRing R] [CommRing T] [Algebra R T] [Module.Finite R T]
    (J : Ideal T) : Module.Finite R (T ⧸ J) :=
  Module.Finite.of_surjective (Ideal.Quotient.mkₐ R J).toLinearMap Ideal.Quotient.mk_surjective

variable (hinj : Function.Injective (algebraMap Γ(X.obj.left, ⊤) S)) {I : Ideal Γ(X.obj.left, ⊤)}
  (hI : ∀ i ∈ I, ∀ s : S, ∃ r ∈ I,
    algebraMap Γ(X.obj.left, ⊤) S r = algebraMap Γ(X.obj.left, ⊤) S i * s)

include hinj in
/-- `(Spec S)^an ⟶ X^an` is surjective for `Γ(X, 𝒪_X) → S` finite and injective. -/
lemma surjective_specAlgebraHom (x : analytification.obj X) :
    ∃ y : analytification.obj (SchemeLFTℂ.specAlgebra X S),
      (analytification.map (SchemeLFTℂ.specAlgebraHom X S)).toLRSHom.base y = x := by
  haveI := isMaximal_affinePt x
  have hker : (⊥ : Ideal S).comap (algebraMap Γ(X.obj.left, ⊤) S) ≤ (affinePt x).asIdeal := by
    intro a ha
    rw [Ideal.mem_comap, Ideal.mem_bot, ← map_zero (algebraMap Γ(X.obj.left, ⊤) S)] at ha
    rw [hinj ha]
    exact zero_mem _
  obtain ⟨q, -, hq, hqc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (affinePt x).asIdeal ⊥ hker
  have hqm : q.IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_comap q (by rw [hqc]; infer_instance)
  obtain ⟨y, hy⟩ := exists_specPt_eq (X := X) ⟨q, hq⟩ hqm
  refine ⟨y, affinePt_injective ?_⟩
  rw [affinePt_specAlgebraHom, hy]
  ext1
  exact hqc

include hI in
/-- `(Spec S)^an ⟶ X^an` is injective away from `V(I)`. -/
lemma eq_of_specAlgebraHom_eq (y₁ y₂ : analytification.obj (SchemeLFTℂ.specAlgebra X S))
    (h : (analytification.map (SchemeLFTℂ.specAlgebraHom X S)).toLRSHom.base y₁ =
      (analytification.map (SchemeLFTℂ.specAlgebraHom X S)).toLRSHom.base y₂)
    (hIy : ¬ I ≤ (affinePt ((analytification.map
      (SchemeLFTℂ.specAlgebraHom X S)).toLRSHom.base y₁)).asIdeal) : y₁ = y₂ := by
  obtain ⟨f, hfI, hfm⟩ := Set.not_subset.1 hIy
  have hc : (specPt y₁).comap (algebraMap Γ(X.obj.left, ⊤) S) =
      (specPt y₂).comap (algebraMap Γ(X.obj.left, ⊤) S) := by
    rw [← affinePt_specAlgebraHom, ← affinePt_specAlgebraHom, h]
  rw [affinePt_specAlgebraHom] at hfm
  have key : ∀ q₁ q₂ : PrimeSpectrum S, q₁.comap (algebraMap Γ(X.obj.left, ⊤) S) =
      q₂.comap (algebraMap Γ(X.obj.left, ⊤) S) →
      algebraMap Γ(X.obj.left, ⊤) S f ∉ q₁.asIdeal → q₁.asIdeal ≤ q₂.asIdeal := by
    intro q₁ q₂ hq hf s hs
    obtain ⟨r, -, hr⟩ := hI f hfI s
    have h1 : r ∈ (q₁.comap (algebraMap Γ(X.obj.left, ⊤) S)).asIdeal := by
      change algebraMap Γ(X.obj.left, ⊤) S r ∈ q₁.asIdeal
      rw [hr]
      exact Ideal.mul_mem_left _ _ hs
    rw [hq] at h1
    change algebraMap Γ(X.obj.left, ⊤) S r ∈ q₂.asIdeal at h1
    rw [hr] at h1
    refine (q₂.isPrime.mem_or_mem h1).resolve_left fun hf₂ ↦ hf ?_
    have : f ∈ (q₂.comap (algebraMap Γ(X.obj.left, ⊤) S)).asIdeal := hf₂
    rw [← hq] at this
    exact this
  haveI := isMaximal_specPt y₁
  refine specPt_injective (PrimeSpectrum.ext ((isMaximal_specPt y₁).eq_of_le
    (isMaximal_specPt y₂).ne_top (key _ _ hc hfm)))

/-- Points of `(Spec S)^an` over `V(I)` come from `(Spec (S ⧸ I S))^an`. -/
lemma exists_specAlgebraMap_mk_eq (y : analytification.obj (SchemeLFTℂ.specAlgebra X S))
    (hIy : I ≤ (affinePt ((analytification.map
      (SchemeLFTℂ.specAlgebraHom X S)).toLRSHom.base y)).asIdeal) :
    ∃ z, (analytification.map (SchemeLFTℂ.specAlgebraMap X
      (Ideal.Quotient.mkₐ Γ(X.obj.left, ⊤) (I.map (algebraMap Γ(X.obj.left, ⊤) S))))).toLRSHom.base
        z = y := by
  refine exists_specAlgebraMap_eq _ Ideal.Quotient.mk_surjective y ?_
  change RingHom.ker (Ideal.Quotient.mk _) ≤ _
  rw [Ideal.mk_ker, Ideal.map_le_iff_le_comap]
  rw [affinePt_specAlgebraHom] at hIy
  exact hIy

omit [Module.Finite Γ(X.obj.left, ⊤) S] in
/-- Points of `X^an` over `V(I)` come from `(Spec (Γ(X, 𝒪_X) ⧸ I))^an`. -/
lemma exists_specAlgebraHom_quotient_eq (x : analytification.obj X)
    (hIx : I ≤ (affinePt x).asIdeal) :
    ∃ c : analytification.obj (SchemeLFTℂ.specAlgebra X (Γ(X.obj.left, ⊤) ⧸ I)),
      (analytification.map (SchemeLFTℂ.specAlgebraHom X _)).toLRSHom.base c = x := by
  haveI := isMaximal_affinePt x
  have hk : RingHom.ker (Ideal.Quotient.mk I) ≤ (affinePt x).asIdeal := by
    rw [Ideal.mk_ker]
    exact hIx
  have hmax := Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective hk
  obtain ⟨c, hc⟩ := exists_specPt_eq (X := X) ⟨_, hmax.isPrime⟩ hmax
  refine ⟨c, affinePt_injective ?_⟩
  rw [affinePt_specAlgebraHom, hc]
  ext1
  exact (Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective _).trans (sup_eq_left.2 hk)

omit [Module.Finite Γ(X.obj.left, ⊤) S] in
/-- `(Spec R)^an ⟶ X^an` is injective for `Γ(X, 𝒪_X) → R` surjective. -/
lemma injective_specAlgebraHom {R : Type u} [CommRing R] [Algebra Γ(X.obj.left, ⊤) R]
    [Module.Finite Γ(X.obj.left, ⊤) R] (hR : Function.Surjective (algebraMap Γ(X.obj.left, ⊤) R)) :
    Function.Injective (analytification.map (SchemeLFTℂ.specAlgebraHom X R)).toLRSHom.base :=
  fun c₁ c₂ h ↦ specPt_injective (PrimeSpectrum.comap_injective_of_surjective _ hR (by
    rw [← affinePt_specAlgebraHom, ← affinePt_specAlgebraHom, h]))

end MilnorPoints

/-! ### The gluing datum over `Spec (S ⧸ I S)` -/

section Gluing

attribute [local instance] MilnorPatching.quotientAlgebra

instance {R T A B : Type*} [CommRing R] [CommRing T] [Algebra R T] [CommRing A] [Algebra T A]
    [Algebra R A] [IsScalarTower R T A] [Module.Finite R A] [CommRing B] [Algebra T B]
    [Module.Finite T B] : Module.Finite R (A ⊗[T] B) :=
  Module.Finite.trans A (A ⊗[T] B)

variable {X : SchemeLFTℂ.{u}} [IsAffine X.obj.left] {S : Type u} [CommRing S]
  [Algebra Γ(X.obj.left, ⊤) S] [Module.Finite Γ(X.obj.left, ⊤) S] {I : Ideal Γ(X.obj.left, ⊤)}
  {W : AnalyticSpace.FiniteEtaleOver (analytification.obj X)}

variable (X) in
/-- An isomorphism `Spec R ≅ Spec R'` over `Spec T`, for finite `Γ(X, 𝒪_X)`-algebras, is `Spec` of
a `T`-algebra isomorphism. -/
theorem SchemeLFTℂ.exists_algEquiv_of_iso {T R R' : Type u} [CommRing T] [CommRing R]
    [CommRing R'] [Algebra Γ(X.obj.left, ⊤) T] [Algebra Γ(X.obj.left, ⊤) R]
    [Algebra Γ(X.obj.left, ⊤) R'] [Algebra T R] [Algebra T R'] [IsScalarTower Γ(X.obj.left, ⊤) T R]
    [IsScalarTower Γ(X.obj.left, ⊤) T R'] [Module.Finite Γ(X.obj.left, ⊤) T]
    [Module.Finite Γ(X.obj.left, ⊤) R] [Module.Finite Γ(X.obj.left, ⊤) R']
    (θ : SchemeLFTℂ.specAlgebra X R ≅ SchemeLFTℂ.specAlgebra X R')
    (hθ : θ.hom ≫ SchemeLFTℂ.specAlgebraMap X (IsScalarTower.toAlgHom _ T R') =
      SchemeLFTℂ.specAlgebraMap X (IsScalarTower.toAlgHom _ T R)) :
    ∃ e : R' ≃ₐ[T] R,
      SchemeLFTℂ.specAlgebraMap X ((e : R' →ₐ[T] R).restrictScalars _) = θ.hom := by
  let ρ := Spec.preimage θ.hom.hom.left
  let ρ' := Spec.preimage θ.inv.hom.left
  have hρ : Spec.map ρ = θ.hom.hom.left := Spec.map_preimage _
  have hρ' : Spec.map ρ' = θ.inv.hom.left := Spec.map_preimage _
  have h₁ : ρ ≫ ρ' = 𝟙 _ := Spec.map_injective (by
    rw [Spec.map_comp, hρ, hρ', Spec.map_id]
    exact congrArg (fun φ ↦ φ.hom.left) θ.inv_hom_id)
  have h₂ : ρ' ≫ ρ = 𝟙 _ := Spec.map_injective (by
    rw [Spec.map_comp, hρ, hρ', Spec.map_id]
    exact congrArg (fun φ ↦ φ.hom.left) θ.hom_inv_id)
  have hbij : Function.Bijective ρ :=
    Function.bijective_iff_has_inverse.2 ⟨ρ', fun x ↦ congrArg (fun φ ↦ φ.hom x) h₁,
      fun x ↦ congrArg (fun φ ↦ φ.hom x) h₂⟩
  have hover : CommRingCat.ofHom (Algebra.algebraMap T R') ≫ ρ =
      CommRingCat.ofHom (Algebra.algebraMap T R) :=
    Spec.map_injective (by
      rw [Spec.map_comp, hρ]
      exact congrArg (fun φ ↦ φ.hom.left) hθ)
  let ρT : R' →ₐ[T] R := { ρ.hom with commutes' := fun s ↦ congrArg (fun φ ↦ φ.hom s) hover }
  refine ⟨AlgEquiv.ofBijective ρT hbij, ?_⟩
  ext1
  exact Over.OverMorphism.ext hρ

/-- `Spec ((S ⧸ I S) ⊗[S] P)` as a finite étale cover of `Spec (S ⧸ I S)`. -/
def CoverModel.restrictFst (M : CoverModel X S W) :
    SchemeLFTℂ.FiniteEtaleOver
      (SchemeLFTℂ.specAlgebra X (S ⧸ I.map (algebraMap Γ(X.obj.left, ⊤) S))) :=
  MorphismProperty.Over.mk ⊤ (SchemeLFTℂ.specAlgebraMap X
    (IsScalarTower.toAlgHom Γ(X.obj.left, ⊤) (S ⧸ I.map (algebraMap Γ(X.obj.left, ⊤) S))
      ((S ⧸ I.map (algebraMap Γ(X.obj.left, ⊤) S)) ⊗[S] M.P)))
    (SchemeLFTℂ.isFiniteEtale_specAlgebraMap X _ (RingHom.finite_algebraMap.2 inferInstance)
      (RingHom.etale_algebraMap.2 inferInstance))

/-- `Spec ((S ⧸ I S) ⊗[Γ(X, 𝒪_X) ⧸ I] Q)` as a finite étale cover of `Spec (S ⧸ I S)`. -/
def CoverModel.restrictSnd (N : CoverModel X (Γ(X.obj.left, ⊤) ⧸ I) W) :
    SchemeLFTℂ.FiniteEtaleOver
      (SchemeLFTℂ.specAlgebra X (S ⧸ I.map (algebraMap Γ(X.obj.left, ⊤) S))) :=
  MorphismProperty.Over.mk ⊤ (SchemeLFTℂ.specAlgebraMap X
    (IsScalarTower.toAlgHom Γ(X.obj.left, ⊤) (S ⧸ I.map (algebraMap Γ(X.obj.left, ⊤) S))
      ((S ⧸ I.map (algebraMap Γ(X.obj.left, ⊤) S)) ⊗[Γ(X.obj.left, ⊤) ⧸ I] N.P)))
    (SchemeLFTℂ.isFiniteEtale_specAlgebraMap X _ (RingHom.finite_algebraMap.2 inferInstance)
      (RingHom.etale_algebraMap.2 inferInstance))

/-- The analytification of the square `Spec ((S ⧸ I S) ⊗[S] P) → Spec P → Spec S` is a
pullback. -/
theorem CoverModel.isPullback_restrictFstSquare (M : CoverModel X S W) :
    IsPullback (analytification.map (SchemeLFTℂ.specAlgebraMap X
        ((Algebra.TensorProduct.includeRight : M.P →ₐ[S]
          (S ⧸ I.map (algebraMap Γ(X.obj.left, ⊤) S)) ⊗[S] M.P).restrictScalars _)))
      (analytification.map (SchemeLFTℂ.specAlgebraMap X
        (IsScalarTower.toAlgHom Γ(X.obj.left, ⊤) (S ⧸ I.map (algebraMap Γ(X.obj.left, ⊤) S))
          ((S ⧸ I.map (algebraMap Γ(X.obj.left, ⊤) S)) ⊗[S] M.P))))
      (analytification.map (SchemeLFTℂ.specAlgebraMap X (IsScalarTower.toAlgHom _ S M.P)))
      (analytification.map (SchemeLFTℂ.specAlgebraMap X
        (Ideal.Quotient.mkₐ Γ(X.obj.left, ⊤) (I.map (algebraMap Γ(X.obj.left, ⊤) S))))) :=
  isPullback_specAlgebraMap X (IsScalarTower.toAlgHom _ S M.P) (Ideal.Quotient.mkₐ _ _)
    ((Algebra.TensorProduct.includeRight : M.P →ₐ[S]
      (S ⧸ I.map (algebraMap Γ(X.obj.left, ⊤) S)) ⊗[S] M.P).restrictScalars _)
    (IsScalarTower.toAlgHom _ _ _)
    (CommRingCat.isPushout_tensorProduct S (S ⧸ I.map (algebraMap Γ(X.obj.left, ⊤) S)) M.P).flip

/-- `(Spec ((S ⧸ I S) ⊗[S] P))^an` is `W ×_{X^an} (Spec (S ⧸ I S))^an`. -/
theorem CoverModel.isPullback_restrictFst (M : CoverModel X S W) :
    IsPullback (analytification.map (SchemeLFTℂ.specAlgebraMap X
        ((Algebra.TensorProduct.includeRight : M.P →ₐ[S]
          (S ⧸ I.map (algebraMap Γ(X.obj.left, ⊤) S)) ⊗[S] M.P).restrictScalars _)) ≫ M.g)
      (analytification.map (SchemeLFTℂ.specAlgebraMap X
        (IsScalarTower.toAlgHom Γ(X.obj.left, ⊤) (S ⧸ I.map (algebraMap Γ(X.obj.left, ⊤) S))
          ((S ⧸ I.map (algebraMap Γ(X.obj.left, ⊤) S)) ⊗[S] M.P))))
      W.hom (analytification.map
        (SchemeLFTℂ.specAlgebraHom X (S ⧸ I.map (algebraMap Γ(X.obj.left, ⊤) S)))) := by
  haveI : IsFiniteEtale W.hom := W.prop
  convert M.isPullback_restrictFstSquare.paste_horiz M.isPullback using 1
  exact ((Functor.map_comp _ _ _).symm.trans
    (congrArg _ (SchemeLFTℂ.specAlgebraMap_specAlgebraHom X _))).symm

/-- `(Spec ((S ⧸ I S) ⊗[Γ(X, 𝒪_X) ⧸ I] Q))^an` is `W ×_{X^an} (Spec (S ⧸ I S))^an`. -/
theorem CoverModel.isPullback_restrictSnd (N : CoverModel X (Γ(X.obj.left, ⊤) ⧸ I) W) :
    IsPullback (analytification.map (SchemeLFTℂ.specAlgebraMap X
        ((Algebra.TensorProduct.includeRight : N.P →ₐ[Γ(X.obj.left, ⊤) ⧸ I]
          (S ⧸ I.map (algebraMap Γ(X.obj.left, ⊤) S)) ⊗[Γ(X.obj.left, ⊤) ⧸ I] N.P).restrictScalars
            _)) ≫ N.g)
      (analytification.map (SchemeLFTℂ.specAlgebraMap X
        (IsScalarTower.toAlgHom Γ(X.obj.left, ⊤) (S ⧸ I.map (algebraMap Γ(X.obj.left, ⊤) S))
          ((S ⧸ I.map (algebraMap Γ(X.obj.left, ⊤) S)) ⊗[Γ(X.obj.left, ⊤) ⧸ I] N.P))))
      W.hom (analytification.map
        (SchemeLFTℂ.specAlgebraHom X (S ⧸ I.map (algebraMap Γ(X.obj.left, ⊤) S)))) := by
  haveI : IsFiniteEtale W.hom := W.prop
  have hsq := isPullback_specAlgebraMap X (IsScalarTower.toAlgHom _ (Γ(X.obj.left, ⊤) ⧸ I) N.P)
    (IsScalarTower.toAlgHom _ (Γ(X.obj.left, ⊤) ⧸ I) (S ⧸ I.map (algebraMap Γ(X.obj.left, ⊤) S)))
    ((Algebra.TensorProduct.includeRight : N.P →ₐ[Γ(X.obj.left, ⊤) ⧸ I]
      (S ⧸ I.map (algebraMap Γ(X.obj.left, ⊤) S)) ⊗[Γ(X.obj.left, ⊤) ⧸ I] N.P).restrictScalars _)
    (IsScalarTower.toAlgHom _ _ _)
    (CommRingCat.isPushout_tensorProduct (Γ(X.obj.left, ⊤) ⧸ I)
      (S ⧸ I.map (algebraMap Γ(X.obj.left, ⊤) S)) N.P).flip
  convert hsq.paste_horiz N.isPullback using 1
  exact ((Functor.map_comp _ _ _).symm.trans
    (congrArg _ (SchemeLFTℂ.specAlgebraMap_specAlgebraHom X _))).symm

/-- The isomorphism of the analytifications of the two restrictions to `Spec (S ⧸ I S)`. -/
def CoverModel.gluingIso (M : CoverModel X S W) (N : CoverModel X (Γ(X.obj.left, ⊤) ⧸ I) W) :
    (analytificationFiniteEtaleOver _).obj M.restrictFst ≅
      (analytificationFiniteEtaleOver _).obj N.restrictSnd :=
  haveI : IsFiniteEtale W.hom := W.prop
  MorphismProperty.Over.isoMk (M.isPullback_restrictFst.isoIsPullback _ _ N.isPullback_restrictSnd)
    (IsPullback.isoIsPullback_hom_snd _ _ _ _)

/-- **The gluing datum.** Models `P` of `W` over `Spec S` and `Q` of `W` over
`Spec (Γ(X, 𝒪_X) ⧸ I)` give an isomorphism `(S ⧸ I S) ⊗[Γ(X, 𝒪_X) ⧸ I] Q ≅ (S ⧸ I S) ⊗[S] P` of
`S ⧸ I S`-algebras compatible with the maps to `W`. This is where full faithfulness of the
analytification over `Spec (S ⧸ I S)` is used. -/
theorem CoverModel.exists_gluingEquiv (M : CoverModel X S W)
    (N : CoverModel X (Γ(X.obj.left, ⊤) ⧸ I) W) :
    ∃ e : (S ⧸ I.map (algebraMap Γ(X.obj.left, ⊤) S)) ⊗[Γ(X.obj.left, ⊤) ⧸ I] N.P
        ≃ₐ[S ⧸ I.map (algebraMap Γ(X.obj.left, ⊤) S)]
        (S ⧸ I.map (algebraMap Γ(X.obj.left, ⊤) S)) ⊗[S] M.P,
      analytification.map (SchemeLFTℂ.specAlgebraMap X
          (e.toAlgHom.restrictScalars Γ(X.obj.left, ⊤))) ≫
        analytification.map (SchemeLFTℂ.specAlgebraMap X
          ((Algebra.TensorProduct.includeRight : N.P →ₐ[Γ(X.obj.left, ⊤) ⧸ I]
            (S ⧸ I.map (algebraMap Γ(X.obj.left, ⊤) S)) ⊗[Γ(X.obj.left, ⊤) ⧸ I]
              N.P).restrictScalars Γ(X.obj.left, ⊤))) ≫ N.g =
      analytification.map (SchemeLFTℂ.specAlgebraMap X
          ((Algebra.TensorProduct.includeRight : M.P →ₐ[S]
            (S ⧸ I.map (algebraMap Γ(X.obj.left, ⊤) S)) ⊗[S] M.P).restrictScalars
              Γ(X.obj.left, ⊤))) ≫ M.g := by
  haveI : IsFiniteEtale W.hom := W.prop
  let θ := (fullyFaithfulAnalytificationFiniteEtaleOver _).preimageIso (M.gluingIso N)
  obtain ⟨e, he⟩ := SchemeLFTℂ.exists_algEquiv_of_iso X
    ((MorphismProperty.Over.forget _ _ _ ⋙ CategoryTheory.Over.forget _).mapIso θ)
    (MorphismProperty.Over.w θ.hom)
  refine ⟨e, ?_⟩
  have hθ : analytification.map θ.hom.left = (M.gluingIso N).hom.left :=
    congrArg (fun φ ↦ φ.left) ((fullyFaithfulAnalytificationFiniteEtaleOver _).map_preimage
      (M.gluingIso N).hom)
  have he' : SchemeLFTℂ.specAlgebraMap X (e.toAlgHom.restrictScalars Γ(X.obj.left, ⊤)) =
      θ.hom.left := he
  exact (congrArg (· ≫ _) ((congrArg analytification.map he').trans hθ)).trans
    (IsPullback.isoIsPullback_hom_fst _ _ _ _)

end Gluing

/-! ### The patched cover -/

section Patch

attribute [local instance] MilnorPatching.quotientAlgebra

variable {X : SchemeLFTℂ.{u}} [IsAffine X.obj.left] {S : Type u} [CommRing S]
  [Algebra Γ(X.obj.left, ⊤) S] [Module.Finite Γ(X.obj.left, ⊤) S] {I : Ideal Γ(X.obj.left, ⊤)}
  {W : AnalyticSpace.FiniteEtaleOver (analytification.obj X)}
  (M : CoverModel X S W) (N : CoverModel X (Γ(X.obj.left, ⊤) ⧸ I) W)
  (e : (S ⧸ I.map (algebraMap Γ(X.obj.left, ⊤) S)) ⊗[Γ(X.obj.left, ⊤) ⧸ I] N.P
    ≃ₐ[S ⧸ I.map (algebraMap Γ(X.obj.left, ⊤) S)]
      (S ⧸ I.map (algebraMap Γ(X.obj.left, ⊤) S)) ⊗[S] M.P)

/-- The map `P → (S ⧸ I S) ⊗[S] P`. -/
abbrev CoverModel.patchφ : M.P →ₐ[S] (S ⧸ I.map (algebraMap Γ(X.obj.left, ⊤) S)) ⊗[S] M.P :=
  Algebra.TensorProduct.includeRight

/-- The map `Q → (S ⧸ I S) ⊗[S] P` given by a gluing isomorphism. -/
abbrev CoverModel.patchψ :
    N.P →ₐ[Γ(X.obj.left, ⊤) ⧸ I] (S ⧸ I.map (algebraMap Γ(X.obj.left, ⊤) S)) ⊗[S] M.P :=
  (e.toAlgHom.restrictScalars _).comp
    Algebra.TensorProduct.includeRight

lemma CoverModel.isBaseChange_patchφ :
    IsBaseChange (S ⧸ I.map (algebraMap Γ(X.obj.left, ⊤) S)) (M.patchφ (I := I)).toLinearMap :=
  IsBaseChange.of_equiv (LinearEquiv.refl _ _) fun _ ↦ rfl

lemma CoverModel.isBaseChange_patchψ :
    IsBaseChange (S ⧸ I.map (algebraMap Γ(X.obj.left, ⊤) S)) (M.patchψ N e).toLinearMap :=
  IsBaseChange.of_equiv e.toLinearEquiv fun _ ↦ rfl

/-- The patched algebra `P ×_{(S ⧸ I S) ⊗[S] P} Q`. -/
abbrev CoverModel.patch : Type u := MilnorPatching.patch (M.patchφ (I := I)) (M.patchψ N e)

/-- The first projection of the patched algebra, over `Γ(X, 𝒪_X)`. -/
abbrev CoverModel.patchFst : M.patch N e →ₐ[Γ(X.obj.left, ⊤)] M.P :=
  MilnorPatching.fst _ _

/-- The second projection of the patched algebra, over `Γ(X, 𝒪_X)`. -/
abbrev CoverModel.patchSnd : M.patch N e →ₐ[Γ(X.obj.left, ⊤)] N.P :=
  MilnorPatching.snd _ _

/-- The two composites `B → (S ⧸ I S) ⊗[S] P` agree. -/
lemma CoverModel.patch_comm :
    ((M.patchφ (I := I)).restrictScalars Γ(X.obj.left, ⊤)).comp (M.patchFst N e) =
      ((e.toAlgHom.restrictScalars _).comp
        ((Algebra.TensorProduct.includeRight : N.P →ₐ[Γ(X.obj.left, ⊤) ⧸ I]
          (S ⧸ I.map (algebraMap Γ(X.obj.left, ⊤) S)) ⊗[Γ(X.obj.left, ⊤) ⧸ I] N.P).restrictScalars
            _)).comp (M.patchSnd N e) :=
  AlgHom.ext fun x ↦ MilnorPatching.φ_fst _ _ x

variable [IsReduced Γ(X.obj.left, ⊤)] (hinj : Function.Injective (algebraMap Γ(X.obj.left, ⊤) S))
  (hI : ∀ i ∈ I, ∀ s : S, ∃ r ∈ I,
    algebraMap Γ(X.obj.left, ⊤) S r = algebraMap Γ(X.obj.left, ⊤) S i * s)

include hinj hI in
/-- **The patched algebra is finite étale** over `Γ(X, 𝒪_X)`, with base changes `P` and `Q`. -/
theorem CoverModel.etale_patch :
    Algebra.Etale Γ(X.obj.left, ⊤) (M.patch N e) ∧ Module.Finite Γ(X.obj.left, ⊤) (M.patch N e) ∧
      Function.Bijective (MilnorPatching.baseChangeFst (M.patchφ (I := I)) (M.patchψ N e)) ∧
      Function.Bijective (MilnorPatching.baseChangeSnd (M.patchφ (I := I)) (M.patchψ N e)) := by
  haveI : IsNoetherianRing Γ(X.obj.left, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
  exact MilnorPatching.etale_patch M.isBaseChange_patchφ (M.isBaseChange_patchψ N e) hI hinj

instance CoverModel.finite_patch : Module.Finite Γ(X.obj.left, ⊤) (M.patch N e) :=
  haveI : IsNoetherianRing Γ(X.obj.left, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
  MilnorPatching.finite_patch

omit [IsReduced Γ(X.obj.left, ⊤)] in
/-- `(Spec P)^an` is the fibre product of `(Spec B)^an` and `(Spec S)^an` over `X^an`, for the
patched algebra `B`. -/
theorem CoverModel.isPullback_patchFst
    (hb : Function.Bijective (MilnorPatching.baseChangeFst (M.patchφ (I := I)) (M.patchψ N e))) :
    IsPullback (analytification.map (SchemeLFTℂ.specAlgebraMap X (M.patchFst N e)))
      (analytification.map (SchemeLFTℂ.specAlgebraMap X (IsScalarTower.toAlgHom _ S M.P)))
      (analytification.map (SchemeLFTℂ.specAlgebraHom X (M.patch N e)))
      (analytification.map (SchemeLFTℂ.specAlgebraHom X S)) := by
  refine isPullback_specAlgebraHom X _ _ (isPushout_of_bijective_productMap _ _ ?_).flip
  have : Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom _ S M.P) (M.patchFst N e) =
      (MilnorPatching.baseChangeFst (M.patchφ (I := I)) (M.patchψ N e)).restrictScalars _ :=
    Algebra.TensorProduct.ext' fun _ _ ↦ rfl
  rw [this]
  exact hb

omit [IsReduced Γ(X.obj.left, ⊤)] in
/-- `(Spec Q)^an` is the fibre product of `(Spec B)^an` and `(Spec (Γ(X, 𝒪_X) ⧸ I))^an` over
`X^an`, for the patched algebra `B`. -/
theorem CoverModel.isPullback_patchSnd
    (hb : Function.Bijective (MilnorPatching.baseChangeSnd (M.patchφ (I := I)) (M.patchψ N e))) :
    IsPullback (analytification.map (SchemeLFTℂ.specAlgebraMap X (M.patchSnd N e)))
      (analytification.map (SchemeLFTℂ.specAlgebraMap X
        (IsScalarTower.toAlgHom _ (Γ(X.obj.left, ⊤) ⧸ I) N.P)))
      (analytification.map (SchemeLFTℂ.specAlgebraHom X (M.patch N e)))
      (analytification.map (SchemeLFTℂ.specAlgebraHom X (Γ(X.obj.left, ⊤) ⧸ I))) := by
  refine isPullback_specAlgebraHom X _ _ (isPushout_of_bijective_productMap _ _ ?_).flip
  have : Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom _ (Γ(X.obj.left, ⊤) ⧸ I) N.P)
      (M.patchSnd N e) =
      (MilnorPatching.baseChangeSnd (M.patchφ (I := I)) (M.patchψ N e)).restrictScalars _ :=
    Algebra.TensorProduct.ext' fun _ _ ↦ rfl
  rw [this]
  exact hb

omit [IsReduced Γ(X.obj.left, ⊤)] in
lemma CoverModel.specAlgebraMap_patch_comm₁ :
    SchemeLFTℂ.specAlgebraMap X (e.toAlgHom.restrictScalars Γ(X.obj.left, ⊤)) ≫
      SchemeLFTℂ.specAlgebraMap X
        ((Algebra.TensorProduct.includeRight : N.P →ₐ[Γ(X.obj.left, ⊤) ⧸ I]
          (S ⧸ I.map (algebraMap Γ(X.obj.left, ⊤) S)) ⊗[Γ(X.obj.left, ⊤) ⧸ I]
            N.P).restrictScalars Γ(X.obj.left, ⊤)) ≫
      SchemeLFTℂ.specAlgebraMap X (M.patchSnd N e) =
      SchemeLFTℂ.specAlgebraMap X
        ((Algebra.TensorProduct.includeRight : M.P →ₐ[S]
          (S ⧸ I.map (algebraMap Γ(X.obj.left, ⊤) S)) ⊗[S] M.P).restrictScalars
            Γ(X.obj.left, ⊤)) ≫ SchemeLFTℂ.specAlgebraMap X (M.patchFst N e) := by
    rw [SchemeLFTℂ.specAlgebraMap_comp, SchemeLFTℂ.specAlgebraMap_comp,
      SchemeLFTℂ.specAlgebraMap_comp]
    exact congrArg _ (M.patch_comm N e).symm

omit [IsReduced Γ(X.obj.left, ⊤)] in
lemma CoverModel.specAlgebraMap_patch_comm₂ :
    SchemeLFTℂ.specAlgebraMap X (e.toAlgHom.restrictScalars Γ(X.obj.left, ⊤)) ≫
      SchemeLFTℂ.specAlgebraMap X
        ((Algebra.TensorProduct.includeRight : N.P →ₐ[Γ(X.obj.left, ⊤) ⧸ I]
          (S ⧸ I.map (algebraMap Γ(X.obj.left, ⊤) S)) ⊗[Γ(X.obj.left, ⊤) ⧸ I]
            N.P).restrictScalars Γ(X.obj.left, ⊤)) ≫
      SchemeLFTℂ.specAlgebraMap X (IsScalarTower.toAlgHom _ (Γ(X.obj.left, ⊤) ⧸ I) N.P) =
      SchemeLFTℂ.specAlgebraMap X (IsScalarTower.toAlgHom Γ(X.obj.left, ⊤)
        (S ⧸ I.map (algebraMap Γ(X.obj.left, ⊤) S))
        ((S ⧸ I.map (algebraMap Γ(X.obj.left, ⊤) S)) ⊗[S] M.P)) ≫
      SchemeLFTℂ.specAlgebraMap X (IsScalarTower.toAlgHom Γ(X.obj.left, ⊤)
        (Γ(X.obj.left, ⊤) ⧸ I) (S ⧸ I.map (algebraMap Γ(X.obj.left, ⊤) S))) := by
    rw [SchemeLFTℂ.specAlgebraMap_comp, SchemeLFTℂ.specAlgebraMap_comp,
      SchemeLFTℂ.specAlgebraMap_comp]
    exact congrArg _ (Ideal.Quotient.algHom_ext _ (Subsingleton.elim _ _))

omit [IsReduced Γ(X.obj.left, ⊤)] in
lemma specAlgebraMap_quotient_comm :
    SchemeLFTℂ.specAlgebraMap X (IsScalarTower.toAlgHom Γ(X.obj.left, ⊤)
        (Γ(X.obj.left, ⊤) ⧸ I) (S ⧸ I.map (algebraMap Γ(X.obj.left, ⊤) S))) ≫
      SchemeLFTℂ.specAlgebraHom X (Γ(X.obj.left, ⊤) ⧸ I) =
      SchemeLFTℂ.specAlgebraMap X
        (Ideal.Quotient.mkₐ Γ(X.obj.left, ⊤) (I.map (algebraMap Γ(X.obj.left, ⊤) S))) ≫
      SchemeLFTℂ.specAlgebraHom X S := by
    rw [SchemeLFTℂ.specAlgebraMap_specAlgebraHom, SchemeLFTℂ.specAlgebraMap_specAlgebraHom]


omit [IsReduced Γ(X.obj.left, ⊤)] in
lemma CoverModel.specAlgebraMap_patch_comm₁_apply
    (z : analytification.obj (SchemeLFTℂ.specAlgebra X
      ((S ⧸ I.map (algebraMap Γ(X.obj.left, ⊤) S)) ⊗[S] M.P))) :
    (analytification.map (SchemeLFTℂ.specAlgebraMap X (M.patchSnd N e))).toLRSHom.base
      ((analytification.map (SchemeLFTℂ.specAlgebraMap X
        ((Algebra.TensorProduct.includeRight : N.P →ₐ[Γ(X.obj.left, ⊤) ⧸ I]
          (S ⧸ I.map (algebraMap Γ(X.obj.left, ⊤) S)) ⊗[Γ(X.obj.left, ⊤) ⧸ I]
            N.P).restrictScalars Γ(X.obj.left, ⊤)))).toLRSHom.base
        ((analytification.map (SchemeLFTℂ.specAlgebraMap X
          (e.toAlgHom.restrictScalars Γ(X.obj.left, ⊤)))).toLRSHom.base z)) =
    (analytification.map (SchemeLFTℂ.specAlgebraMap X (M.patchFst N e))).toLRSHom.base
      ((analytification.map (SchemeLFTℂ.specAlgebraMap X
        ((Algebra.TensorProduct.includeRight : M.P →ₐ[S]
          (S ⧸ I.map (algebraMap Γ(X.obj.left, ⊤) S)) ⊗[S] M.P).restrictScalars
            Γ(X.obj.left, ⊤)))).toLRSHom.base z) := by
  have := congrArg (fun φ ↦ (analytification.map φ).toLRSHom.base z)
    (M.specAlgebraMap_patch_comm₁ N e)
  simp only [Functor.map_comp] at this
  exact this

omit [IsReduced Γ(X.obj.left, ⊤)] in
lemma CoverModel.specAlgebraMap_patch_comm₂_apply
    (z : analytification.obj (SchemeLFTℂ.specAlgebra X
      ((S ⧸ I.map (algebraMap Γ(X.obj.left, ⊤) S)) ⊗[S] M.P))) :
    (analytification.map (SchemeLFTℂ.specAlgebraMap X
        (IsScalarTower.toAlgHom _ (Γ(X.obj.left, ⊤) ⧸ I) N.P))).toLRSHom.base
      ((analytification.map (SchemeLFTℂ.specAlgebraMap X
        ((Algebra.TensorProduct.includeRight : N.P →ₐ[Γ(X.obj.left, ⊤) ⧸ I]
          (S ⧸ I.map (algebraMap Γ(X.obj.left, ⊤) S)) ⊗[Γ(X.obj.left, ⊤) ⧸ I]
            N.P).restrictScalars Γ(X.obj.left, ⊤)))).toLRSHom.base
        ((analytification.map (SchemeLFTℂ.specAlgebraMap X
          (e.toAlgHom.restrictScalars Γ(X.obj.left, ⊤)))).toLRSHom.base z)) =
    (analytification.map (SchemeLFTℂ.specAlgebraMap X (IsScalarTower.toAlgHom Γ(X.obj.left, ⊤)
        (Γ(X.obj.left, ⊤) ⧸ I) (S ⧸ I.map (algebraMap Γ(X.obj.left, ⊤) S))))).toLRSHom.base
      ((analytification.map (SchemeLFTℂ.specAlgebraMap X (IsScalarTower.toAlgHom Γ(X.obj.left, ⊤)
        (S ⧸ I.map (algebraMap Γ(X.obj.left, ⊤) S))
        ((S ⧸ I.map (algebraMap Γ(X.obj.left, ⊤) S)) ⊗[S] M.P)))).toLRSHom.base z) := by
  have := congrArg (fun φ ↦ (analytification.map φ).toLRSHom.base z)
    (M.specAlgebraMap_patch_comm₂ N e)
  simp only [Functor.map_comp] at this
  exact this

omit [IsReduced Γ(X.obj.left, ⊤)] in
lemma specAlgebraMap_quotient_comm_apply
    (c : analytification.obj (SchemeLFTℂ.specAlgebra X
      (S ⧸ I.map (algebraMap Γ(X.obj.left, ⊤) S)))) :
    (analytification.map (SchemeLFTℂ.specAlgebraHom X (Γ(X.obj.left, ⊤) ⧸ I))).toLRSHom.base
      ((analytification.map (SchemeLFTℂ.specAlgebraMap X (IsScalarTower.toAlgHom Γ(X.obj.left, ⊤)
        (Γ(X.obj.left, ⊤) ⧸ I) (S ⧸ I.map (algebraMap Γ(X.obj.left, ⊤) S))))).toLRSHom.base c) =
    (analytification.map (SchemeLFTℂ.specAlgebraHom X S)).toLRSHom.base
      ((analytification.map (SchemeLFTℂ.specAlgebraMap X
        (Ideal.Quotient.mkₐ Γ(X.obj.left, ⊤)
          (I.map (algebraMap Γ(X.obj.left, ⊤) S))))).toLRSHom.base
          c) := by
  have := congrArg (fun φ ↦ (analytification.map φ).toLRSHom.base c)
    (specAlgebraMap_quotient_comm (X := X) (S := S) (I := I))
  simp only [Functor.map_comp] at this
  exact this

omit [IsReduced Γ(X.obj.left, ⊤)] in
/-- Over `V(I)`: two points of `(Spec ((S ⧸ I S) ⊗[S] P))^an` with the same image in `(Spec B)^an`
and the same image in `X^an` have the same image in `W`. -/
theorem CoverModel.g_eq_of_restrict
    (he : analytification.map (SchemeLFTℂ.specAlgebraMap X
          (e.toAlgHom.restrictScalars Γ(X.obj.left, ⊤))) ≫
        analytification.map (SchemeLFTℂ.specAlgebraMap X
          ((Algebra.TensorProduct.includeRight : N.P →ₐ[Γ(X.obj.left, ⊤) ⧸ I]
            (S ⧸ I.map (algebraMap Γ(X.obj.left, ⊤) S)) ⊗[Γ(X.obj.left, ⊤) ⧸ I]
              N.P).restrictScalars Γ(X.obj.left, ⊤))) ≫ N.g =
      analytification.map (SchemeLFTℂ.specAlgebraMap X
          ((Algebra.TensorProduct.includeRight : M.P →ₐ[S]
            (S ⧸ I.map (algebraMap Γ(X.obj.left, ⊤) S)) ⊗[S] M.P).restrictScalars
              Γ(X.obj.left, ⊤))) ≫ M.g)
    [Algebra.Etale Γ(X.obj.left, ⊤) (M.patch N e)]
    (hQ₄ : IsPullback (analytification.map (SchemeLFTℂ.specAlgebraMap X (M.patchSnd N e)))
      (analytification.map (SchemeLFTℂ.specAlgebraMap X
        (IsScalarTower.toAlgHom _ (Γ(X.obj.left, ⊤) ⧸ I) N.P)))
      (analytification.map (SchemeLFTℂ.specAlgebraHom X (M.patch N e)))
      (analytification.map (SchemeLFTℂ.specAlgebraHom X (Γ(X.obj.left, ⊤) ⧸ I))))
    (za zb : analytification.obj (SchemeLFTℂ.specAlgebra X
      ((S ⧸ I.map (algebraMap Γ(X.obj.left, ⊤) S)) ⊗[S] M.P)))
    (h₁ : (analytification.map (SchemeLFTℂ.specAlgebraMap X (M.patchFst N e))).toLRSHom.base
      ((analytification.map (SchemeLFTℂ.specAlgebraMap X
        ((Algebra.TensorProduct.includeRight : M.P →ₐ[S]
          (S ⧸ I.map (algebraMap Γ(X.obj.left, ⊤) S)) ⊗[S] M.P).restrictScalars
            Γ(X.obj.left, ⊤)))).toLRSHom.base za) =
      (analytification.map (SchemeLFTℂ.specAlgebraMap X (M.patchFst N e))).toLRSHom.base
      ((analytification.map (SchemeLFTℂ.specAlgebraMap X
        ((Algebra.TensorProduct.includeRight : M.P →ₐ[S]
          (S ⧸ I.map (algebraMap Γ(X.obj.left, ⊤) S)) ⊗[S] M.P).restrictScalars
            Γ(X.obj.left, ⊤)))).toLRSHom.base zb))
    (h₂ : (analytification.map (SchemeLFTℂ.specAlgebraHom X S)).toLRSHom.base
      ((analytification.map (SchemeLFTℂ.specAlgebraMap X
        (Ideal.Quotient.mkₐ Γ(X.obj.left, ⊤)
          (I.map (algebraMap Γ(X.obj.left, ⊤) S))))).toLRSHom.base
      ((analytification.map (SchemeLFTℂ.specAlgebraMap X (IsScalarTower.toAlgHom Γ(X.obj.left, ⊤)
        (S ⧸ I.map (algebraMap Γ(X.obj.left, ⊤) S))
        ((S ⧸ I.map (algebraMap Γ(X.obj.left, ⊤) S)) ⊗[S] M.P)))).toLRSHom.base za)) =
      (analytification.map (SchemeLFTℂ.specAlgebraHom X S)).toLRSHom.base
      ((analytification.map (SchemeLFTℂ.specAlgebraMap X
        (Ideal.Quotient.mkₐ Γ(X.obj.left, ⊤)
          (I.map (algebraMap Γ(X.obj.left, ⊤) S))))).toLRSHom.base
      ((analytification.map (SchemeLFTℂ.specAlgebraMap X (IsScalarTower.toAlgHom Γ(X.obj.left, ⊤)
        (S ⧸ I.map (algebraMap Γ(X.obj.left, ⊤) S))
        ((S ⧸ I.map (algebraMap Γ(X.obj.left, ⊤) S)) ⊗[S] M.P)))).toLRSHom.base zb))) :
    M.g.toLRSHom.base ((analytification.map (SchemeLFTℂ.specAlgebraMap X
        ((Algebra.TensorProduct.includeRight : M.P →ₐ[S]
          (S ⧸ I.map (algebraMap Γ(X.obj.left, ⊤) S)) ⊗[S] M.P).restrictScalars
            Γ(X.obj.left, ⊤)))).toLRSHom.base za) =
    M.g.toLRSHom.base ((analytification.map (SchemeLFTℂ.specAlgebraMap X
        ((Algebra.TensorProduct.includeRight : M.P →ₐ[S]
          (S ⧸ I.map (algebraMap Γ(X.obj.left, ⊤) S)) ⊗[S] M.P).restrictScalars
            Γ(X.obj.left, ⊤)))).toLRSHom.base zb) := by
  haveI : IsFiniteEtale (analytification.map (SchemeLFTℂ.specAlgebraHom X (M.patch N e))) :=
    isFiniteEtale_analytification_map _ (SchemeLFTℂ.isFiniteEtale_specAlgebraHom X _)
  have hc := injective_specAlgebraHom (R := Γ(X.obj.left, ⊤) ⧸ I) Ideal.Quotient.mk_surjective
    ((specAlgebraMap_quotient_comm_apply _).trans (h₂.trans
      (specAlgebraMap_quotient_comm_apply _).symm))
  have hU := base_ext_of_isPullback hQ₄
    ((M.specAlgebraMap_patch_comm₁_apply N e za).trans
      (h₁.trans (M.specAlgebraMap_patch_comm₁_apply N e zb).symm))
    ((M.specAlgebraMap_patch_comm₂_apply N e za).trans
      (hc.trans (M.specAlgebraMap_patch_comm₂_apply N e zb).symm))
  exact (congrArg (fun φ ↦ φ.toLRSHom.base za) he).symm.trans
    ((congrArg N.g.toLRSHom.base hU).trans (congrArg (fun φ ↦ φ.toLRSHom.base zb) he))

omit [IsReduced Γ(X.obj.left, ⊤)] in
include hI in
/-- **`(Spec P)^an ⟶ W` is constant on the fibres of `(Spec P)^an ⟶ (Spec B)^an`**, for the
patched algebra `B`: away from `V(I)` these fibres are points, and over `V(I)` the values are read
off from `Q` through the gluing isomorphism. -/
theorem CoverModel.g_eq_of_patchFst_eq
    (he : analytification.map (SchemeLFTℂ.specAlgebraMap X
          (e.toAlgHom.restrictScalars Γ(X.obj.left, ⊤))) ≫
        analytification.map (SchemeLFTℂ.specAlgebraMap X
          ((Algebra.TensorProduct.includeRight : N.P →ₐ[Γ(X.obj.left, ⊤) ⧸ I]
            (S ⧸ I.map (algebraMap Γ(X.obj.left, ⊤) S)) ⊗[Γ(X.obj.left, ⊤) ⧸ I]
              N.P).restrictScalars Γ(X.obj.left, ⊤))) ≫ N.g =
      analytification.map (SchemeLFTℂ.specAlgebraMap X
          ((Algebra.TensorProduct.includeRight : M.P →ₐ[S]
            (S ⧸ I.map (algebraMap Γ(X.obj.left, ⊤) S)) ⊗[S] M.P).restrictScalars
              Γ(X.obj.left, ⊤))) ≫ M.g)
    [Algebra.Etale Γ(X.obj.left, ⊤) (M.patch N e)]
    (hQ₃ : IsPullback (analytification.map (SchemeLFTℂ.specAlgebraMap X (M.patchFst N e)))
      (analytification.map (SchemeLFTℂ.specAlgebraMap X (IsScalarTower.toAlgHom _ S M.P)))
      (analytification.map (SchemeLFTℂ.specAlgebraHom X (M.patch N e)))
      (analytification.map (SchemeLFTℂ.specAlgebraHom X S)))
    (hQ₄ : IsPullback (analytification.map (SchemeLFTℂ.specAlgebraMap X (M.patchSnd N e)))
      (analytification.map (SchemeLFTℂ.specAlgebraMap X
        (IsScalarTower.toAlgHom _ (Γ(X.obj.left, ⊤) ⧸ I) N.P)))
      (analytification.map (SchemeLFTℂ.specAlgebraHom X (M.patch N e)))
      (analytification.map (SchemeLFTℂ.specAlgebraHom X (Γ(X.obj.left, ⊤) ⧸ I))))
    (a b : analytification.obj (SchemeLFTℂ.specAlgebra X M.P))
    (h : (analytification.map (SchemeLFTℂ.specAlgebraMap X (M.patchFst N e))).toLRSHom.base a =
      (analytification.map (SchemeLFTℂ.specAlgebraMap X (M.patchFst N e))).toLRSHom.base b) :
    M.g.toLRSHom.base a = M.g.toLRSHom.base b := by
  haveI : IsFiniteEtale (analytification.map (SchemeLFTℂ.specAlgebraHom X (M.patch N e))) :=
    isFiniteEtale_analytification_map _ (SchemeLFTℂ.isFiniteEtale_specAlgebraHom X _)
  haveI : IsFiniteEtale (analytification.map
      (SchemeLFTℂ.specAlgebraMap X (IsScalarTower.toAlgHom Γ(X.obj.left, ⊤) S M.P))) :=
    isFiniteEtale_analytification_map _ (SchemeLFTℂ.isFiniteEtale_specAlgebraMap X _
      (RingHom.finite_algebraMap.2 inferInstance) (RingHom.etale_algebraMap.2 inferInstance))
  have hpq (t : analytification.obj (SchemeLFTℂ.specAlgebra X M.P)) :
      (analytification.map (SchemeLFTℂ.specAlgebraHom X S)).toLRSHom.base
        ((analytification.map (SchemeLFTℂ.specAlgebraMap X
          (IsScalarTower.toAlgHom _ S M.P))).toLRSHom.base t) =
      (analytification.map (SchemeLFTℂ.specAlgebraHom X (M.patch N e))).toLRSHom.base
        ((analytification.map (SchemeLFTℂ.specAlgebraMap X (M.patchFst N e))).toLRSHom.base t) :=
    (congrArg (fun φ ↦ φ.toLRSHom.base t) hQ₃.w).symm
  have hx := (hpq a).trans ((congrArg _ h).trans (hpq b).symm)
  by_cases hIx : I ≤ (affinePt ((analytification.map (SchemeLFTℂ.specAlgebraHom X S)).toLRSHom.base
      ((analytification.map (SchemeLFTℂ.specAlgebraMap X
        (IsScalarTower.toAlgHom _ S M.P))).toLRSHom.base a))).asIdeal
  swap
  · rw [base_ext_of_isPullback hQ₃ h (eq_of_specAlgebraHom_eq hI _ _ hx hIx)]
  obtain ⟨ca, hca⟩ := exists_specAlgebraMap_mk_eq _ hIx
  obtain ⟨cb, hcb⟩ := exists_specAlgebraMap_mk_eq _ (hx ▸ hIx)
  obtain ⟨za, hza, hza'⟩ := exists_base_eq_of_isPullback M.isPullback_restrictFstSquare hca.symm
  obtain ⟨zb, hzb, hzb'⟩ := exists_base_eq_of_isPullback M.isPullback_restrictFstSquare hcb.symm
  have key := M.g_eq_of_restrict N e he hQ₄ za zb
    ((congrArg _ hza).trans (h.trans (congrArg _ hzb).symm))
    ((congrArg (fun c ↦ (analytification.map (SchemeLFTℂ.specAlgebraHom X S)).toLRSHom.base
      ((analytification.map (SchemeLFTℂ.specAlgebraMap X (Ideal.Quotient.mkₐ Γ(X.obj.left, ⊤)
        (I.map (algebraMap Γ(X.obj.left, ⊤) S))))).toLRSHom.base c)) hza').trans
      ((congrArg _ hca).trans (hx.trans ((congrArg _ hcb).symm.trans
        (congrArg (fun c ↦ (analytification.map (SchemeLFTℂ.specAlgebraHom X S)).toLRSHom.base
          ((analytification.map (SchemeLFTℂ.specAlgebraMap X (Ideal.Quotient.mkₐ Γ(X.obj.left, ⊤)
            (I.map (algebraMap Γ(X.obj.left, ⊤) S))))).toLRSHom.base c)) hzb').symm))))
  exact (congrArg M.g.toLRSHom.base hza).symm.trans (key.trans (congrArg _ hzb))

omit [IsReduced Γ(X.obj.left, ⊤)] in
include hinj in
/-- `(Spec P)^an ⟶ W` is surjective. -/
lemma CoverModel.surjective_g : Function.Surjective M.g.toLRSHom.base := by
  haveI : IsFiniteEtale W.hom := W.prop
  intro w
  obtain ⟨x, hx⟩ := surjective_specAlgebraHom hinj (W.hom.toLRSHom.base w)
  obtain ⟨p, hp, -⟩ := exists_base_eq_of_isPullback (hf := W.prop) M.isPullback hx.symm
  exact ⟨p, hp⟩

omit [IsReduced Γ(X.obj.left, ⊤)] in
include hinj in
/-- `(Spec P)^an ⟶ (Spec B)^an` is surjective. -/
lemma CoverModel.surjective_patchFst [Algebra.Etale Γ(X.obj.left, ⊤) (M.patch N e)]
    (hQ₃ : IsPullback (analytification.map (SchemeLFTℂ.specAlgebraMap X (M.patchFst N e)))
      (analytification.map (SchemeLFTℂ.specAlgebraMap X (IsScalarTower.toAlgHom _ S M.P)))
      (analytification.map (SchemeLFTℂ.specAlgebraHom X (M.patch N e)))
      (analytification.map (SchemeLFTℂ.specAlgebraHom X S))) :
    Function.Surjective
      (analytification.map (SchemeLFTℂ.specAlgebraMap X (M.patchFst N e))).toLRSHom.base := by
  haveI : IsFiniteEtale (analytification.map (SchemeLFTℂ.specAlgebraHom X (M.patch N e))) :=
    isFiniteEtale_analytification_map _ (SchemeLFTℂ.isFiniteEtale_specAlgebraHom X _)
  intro y
  obtain ⟨x, hx⟩ := surjective_specAlgebraHom hinj
    ((analytification.map (SchemeLFTℂ.specAlgebraHom X (M.patch N e))).toLRSHom.base y)
  obtain ⟨p, hp, -⟩ := exists_base_eq_of_isPullback hQ₃ hx.symm
  exact ⟨p, hp⟩

omit [IsReduced Γ(X.obj.left, ⊤)] in
/-- Points of `(Spec P)^an` with the same image in `W` have the same image in `(Spec B)^an`. -/
lemma CoverModel.patchFst_eq_of_g_eq [Algebra.Etale Γ(X.obj.left, ⊤) (M.patch N e)]
    (hQ₃ : IsPullback (analytification.map (SchemeLFTℂ.specAlgebraMap X (M.patchFst N e)))
      (analytification.map (SchemeLFTℂ.specAlgebraMap X (IsScalarTower.toAlgHom _ S M.P)))
      (analytification.map (SchemeLFTℂ.specAlgebraHom X (M.patch N e)))
      (analytification.map (SchemeLFTℂ.specAlgebraHom X S)))
    (h₁ : ∀ a b, (analytification.map (SchemeLFTℂ.specAlgebraMap X (M.patchFst N e))).toLRSHom.base
      a = (analytification.map (SchemeLFTℂ.specAlgebraMap X (M.patchFst N e))).toLRSHom.base b →
        M.g.toLRSHom.base a = M.g.toLRSHom.base b)
    (a b : analytification.obj (SchemeLFTℂ.specAlgebra X M.P))
    (hab : M.g.toLRSHom.base a = M.g.toLRSHom.base b) :
    (analytification.map (SchemeLFTℂ.specAlgebraMap X (M.patchFst N e))).toLRSHom.base a =
      (analytification.map (SchemeLFTℂ.specAlgebraMap X (M.patchFst N e))).toLRSHom.base b := by
  haveI : IsFiniteEtale W.hom := W.prop
  haveI : IsFiniteEtale (analytification.map (SchemeLFTℂ.specAlgebraHom X (M.patch N e))) :=
    isFiniteEtale_analytification_map _ (SchemeLFTℂ.isFiniteEtale_specAlgebraHom X _)
  have hν (t : analytification.obj (SchemeLFTℂ.specAlgebra X M.P)) :
      (analytification.map (SchemeLFTℂ.specAlgebraHom X S)).toLRSHom.base
        ((analytification.map (SchemeLFTℂ.specAlgebraMap X
          (IsScalarTower.toAlgHom _ S M.P))).toLRSHom.base t) =
      W.hom.toLRSHom.base (M.g.toLRSHom.base t) :=
    (congrArg (fun φ ↦ φ.toLRSHom.base t) M.isPullback.w).symm
  have hq := ((congrArg (fun φ ↦ φ.toLRSHom.base b) hQ₃.w).trans
    ((hν b).trans ((congrArg _ hab).symm.trans (hν a).symm)))
  obtain ⟨b', hb₁, hb₂⟩ := exists_base_eq_of_isPullback hQ₃ hq
  have : b' = a :=
    base_ext_of_isPullback (hf := W.prop) M.isPullback ((h₁ b' b hb₁).trans hab.symm) hb₂
  rw [← this]
  exact hb₁

omit [IsReduced Γ(X.obj.left, ⊤)] in
include hinj hI in
/-- **`W` is the analytification of `Spec` of the patched algebra.** -/
theorem CoverModel.mem_essImage_of_gluing
    (he : analytification.map (SchemeLFTℂ.specAlgebraMap X
          (e.toAlgHom.restrictScalars Γ(X.obj.left, ⊤))) ≫
        analytification.map (SchemeLFTℂ.specAlgebraMap X
          ((Algebra.TensorProduct.includeRight : N.P →ₐ[Γ(X.obj.left, ⊤) ⧸ I]
            (S ⧸ I.map (algebraMap Γ(X.obj.left, ⊤) S)) ⊗[Γ(X.obj.left, ⊤) ⧸ I]
              N.P).restrictScalars Γ(X.obj.left, ⊤))) ≫ N.g =
      analytification.map (SchemeLFTℂ.specAlgebraMap X
          ((Algebra.TensorProduct.includeRight : M.P →ₐ[S]
            (S ⧸ I.map (algebraMap Γ(X.obj.left, ⊤) S)) ⊗[S] M.P).restrictScalars
              Γ(X.obj.left, ⊤))) ≫ M.g)
    (hEt : Algebra.Etale Γ(X.obj.left, ⊤) (M.patch N e))
    (hbS : Function.Bijective (MilnorPatching.baseChangeFst (M.patchφ (I := I)) (M.patchψ N e)))
    (hbC : Function.Bijective (MilnorPatching.baseChangeSnd (M.patchφ (I := I)) (M.patchψ N e))) :
    (analytificationFiniteEtaleOver X).essImage W := by
  have hQ₃ := M.isPullback_patchFst N e hbS
  have h₁ := M.g_eq_of_patchFst_eq N e hI he hQ₃ (M.isPullback_patchSnd N e hbC)
  haveI : AnalyticSpace.IsFinite
      (analytification.map (SchemeLFTℂ.specAlgebraMap X (M.patchFst N e))) :=
    isFinite_analytification_map_of_isFinite _
  obtain ⟨iso⟩ := AnalyticSpace.FiniteEtaleOver.nonempty_iso_of_closed_surjective
    ((analytificationFiniteEtaleOver X).obj
      (SchemeLFTℂ.specAlgebraFiniteEtaleOver X (M.patch N e) hEt)) W
    (analytification.map (SchemeLFTℂ.specAlgebraMap X (M.patchFst N e))) M.g
    (IsFinite.isClosedMap
      (f := analytification.map (SchemeLFTℂ.specAlgebraMap X (M.patchFst N e))))
    (M.surjective_patchFst N e hinj hQ₃) (M.isPullback.w.trans hQ₃.w.symm) h₁
    (M.surjective_g hinj) (M.patchFst_eq_of_g_eq N e hQ₃ h₁)
  exact ⟨_, ⟨iso⟩⟩

end Patch

/-! ### The main theorem -/

attribute [local instance] MilnorPatching.quotientAlgebra

/-- **Essential surjectivity across a Milnor square.** Let `X` be a reduced affine scheme of finite
type over `ℂ` with `A = Γ(X, 𝒪_X)`, let `A → S` be finite and injective and let `I ⊆ A` be an ideal
of `S` (so that `A = S ×_{S ⧸ I S} A ⧸ I`). If `W` is a finite étale cover of `X^an` whose pullbacks
to `(Spec S)^an` and `(Spec (A ⧸ I))^an` are analytifications of finite étale covers, then `W` is
the analytification of a finite étale cover of `X`. -/
theorem mem_essImage_of_milnorSquare (X : SchemeLFTℂ.{u}) [IsAffine X.obj.left]
    [IsReduced Γ(X.obj.left, ⊤)] (S : Type u) [CommRing S] [Algebra Γ(X.obj.left, ⊤) S]
    [Module.Finite Γ(X.obj.left, ⊤) S] (hinj : Function.Injective (algebraMap Γ(X.obj.left, ⊤) S))
    (I : Ideal Γ(X.obj.left, ⊤))
    (hI : ∀ i ∈ I, ∀ s : S, ∃ r ∈ I,
      algebraMap Γ(X.obj.left, ⊤) S r = algebraMap Γ(X.obj.left, ⊤) S i * s)
    (W : AnalyticSpace.FiniteEtaleOver (analytification.obj X))
    (hS : (analytificationFiniteEtaleOver (SchemeLFTℂ.specAlgebra X S)).essImage
      (pullbackFiniteEtaleOver W (SchemeLFTℂ.specAlgebraHom X S)))
    (hC : (analytificationFiniteEtaleOver
        (SchemeLFTℂ.specAlgebra X (Γ(X.obj.left, ⊤) ⧸ I))).essImage
      (pullbackFiniteEtaleOver W (SchemeLFTℂ.specAlgebraHom X (Γ(X.obj.left, ⊤) ⧸ I)))) :
    (analytificationFiniteEtaleOver X).essImage W := by
  obtain ⟨M⟩ := CoverModel.nonempty_of_mem_essImage hS
  obtain ⟨N⟩ := CoverModel.nonempty_of_mem_essImage hC
  obtain ⟨e, he⟩ := M.exists_gluingEquiv N
  obtain ⟨hEt, -, hbS, hbC⟩ := M.etale_patch N e hinj hI
  exact M.mem_essImage_of_gluing N e hinj hI he hEt hbS hbC

/-! ### Induction on the dimension -/

section Dimension

/-- The `ℂ`-algebra `Γ(X, 𝒪_X)` of an affine scheme of finite type over `ℂ` is of finite type. -/
lemma SchemeLFTℂ.exists_algebra_finiteType (X : SchemeLFTℂ.{u}) [IsAffine X.obj.left] :
    ∃ _ : Algebra ℂ Γ(X.obj.left, ⊤), Algebra.FiniteType ℂ Γ(X.obj.left, ⊤) := by
  set ψ : CommRingCat.of (ULift.{u} ℂ) ⟶ Γ(X.obj.left, ⊤) :=
    Spec.preimage (X.obj.left.isoSpec.inv ≫ X.obj.hom) with hψdef
  have hψ : Spec.map ψ = X.obj.left.isoSpec.inv ≫ X.obj.hom := Spec.map_preimage _
  have hft : ψ.hom.FiniteType := by
    rw [← HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType), hψ]
    haveI : LocallyOfFiniteType X.obj.hom := X.property
    infer_instance
  letI : Algebra ℂ Γ(X.obj.left, ⊤) := (ψ.hom.comp ULift.ringEquiv.symm.toRingHom).toAlgebra
  refine ⟨this, ?_⟩
  change (ψ.hom.comp ULift.ringEquiv.symm.toRingHom).FiniteType
  exact hft.comp (RingHom.FiniteType.of_surjective _ ULift.ringEquiv.symm.surjective)

/-- `Γ(Spec R, 𝒪) ≅ R`, for `Spec R` over an affine base. -/
def SchemeLFTℂ.specAlgebraΓEquiv (X : SchemeLFTℂ.{u}) [IsAffine X.obj.left] (R : Type u)
    [CommRing R] [Algebra Γ(X.obj.left, ⊤) R] [Module.Finite Γ(X.obj.left, ⊤) R] :
    Γ((SchemeLFTℂ.specAlgebra X R).obj.left, ⊤) ≃+* R :=
  (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv

instance (X : SchemeLFTℂ.{u}) [IsAffine X.obj.left] (R : Type u) [CommRing R]
    [Algebra Γ(X.obj.left, ⊤) R] [Module.Finite Γ(X.obj.left, ⊤) R] :
    IsAffine (SchemeLFTℂ.specAlgebra X R).obj.left :=
  inferInstanceAs (IsAffine (Spec (CommRingCat.of R)))

/-- A dimension `x` with `x + 1 ≤ n` is `< n`. -/
lemma lt_natCast_of_add_one_le {x : WithBot ℕ∞} {n : ℕ} (h : x + 1 ≤ n) : x < n := by
  by_contra hc
  have h₂ : ((n : WithBot ℕ∞) + 1) ≤ n := (add_le_add (not_lt.1 hc) le_rfl).trans h
  have : ((n + 1 : ℕ) : WithBot ℕ∞) ≤ (n : ℕ) := by exact_mod_cast h₂
  exact absurd (by exact_mod_cast this) (Nat.not_succ_le_self n)

variable (n : ℕ)
  (hnorm : ∀ (Y : SchemeLFTℂ.{u}) [IsAffine Y.obj.left],
    IsFiniteProductOfNormalDomains Γ(Y.obj.left, ⊤) → ringKrullDim Γ(Y.obj.left, ⊤) ≤ n →
      (analytificationFiniteEtaleOver Y).EssSurj)
  (hlow : ∀ (Y : SchemeLFTℂ.{u}) [IsAffine Y.obj.left], ringKrullDim Γ(Y.obj.left, ⊤) < n →
    (analytificationFiniteEtaleOver Y).EssSurj)

include hnorm hlow in
/-- **Essential surjectivity for reduced affine schemes by induction on the dimension.** If the
analytification of finite étale covers is essentially surjective for all affine schemes of finite
type over `ℂ` whose ring of functions is a finite product of integrally closed domains of
dimension `≤ n`, and for all affine schemes of dimension `< n`, then it is essentially surjective
for every reduced affine scheme of dimension `≤ n`. -/
theorem essSurj_of_isReduced_of_ringKrullDim_le (X : SchemeLFTℂ.{u}) [IsAffine X.obj.left]
    [IsReduced Γ(X.obj.left, ⊤)] (hX : ringKrullDim Γ(X.obj.left, ⊤) ≤ n) :
    (analytificationFiniteEtaleOver X).EssSurj := by
  obtain ⟨_, _⟩ := X.exists_algebra_finiteType
  obtain ⟨S, _, _, _, hinj, hS, hdimS, I, hI, hdimI⟩ := exists_normalization Γ(X.obj.left, ⊤) ℂ
  haveI := hnorm (SchemeLFTℂ.specAlgebra X S)
    (hS.of_ringEquiv (SchemeLFTℂ.specAlgebraΓEquiv X S))
    ((ringKrullDim_eq_of_ringEquiv (SchemeLFTℂ.specAlgebraΓEquiv X S)).trans_le
      (hdimS.trans hX))
  haveI := hlow (SchemeLFTℂ.specAlgebra X (Γ(X.obj.left, ⊤) ⧸ I))
    ((ringKrullDim_eq_of_ringEquiv (SchemeLFTℂ.specAlgebraΓEquiv X _)).trans_lt
      (lt_natCast_of_add_one_le (hdimI.trans hX)))
  exact ⟨fun W ↦ mem_essImage_of_milnorSquare X S hinj I hI W
    (Functor.EssSurj.mem_essImage _ _) (Functor.EssSurj.mem_essImage _ _)⟩

include hnorm hlow in
/-- **Essential surjectivity for affine schemes by induction on the dimension.** Under the
hypotheses of `ComplexAnalytic.essSurj_of_isReduced_of_ringKrullDim_le`, the analytification of
finite étale covers is essentially surjective for every affine scheme of finite type over `ℂ` of
dimension `≤ n`. -/
theorem essSurj_of_ringKrullDim_le (X : SchemeLFTℂ.{u}) [IsAffine X.obj.left]
    (hX : ringKrullDim Γ(X.obj.left, ⊤) ≤ n) :
    (analytificationFiniteEtaleOver X).EssSurj := by
  let R := Γ(X.obj.left, ⊤) ⧸ nilradical Γ(X.obj.left, ⊤)
  haveI : IsReduced R := (Ideal.isRadical_iff_quotient_reduced _).1 (Ideal.radical_isRadical _)
  haveI : IsReduced Γ((SchemeLFTℂ.specAlgebra X R).obj.left, ⊤) :=
    isReduced_of_injective (SchemeLFTℂ.specAlgebraΓEquiv X R).toRingHom
      (SchemeLFTℂ.specAlgebraΓEquiv X R).injective
  haveI := essSurj_of_isReduced_of_ringKrullDim_le n hnorm hlow (SchemeLFTℂ.specAlgebra X R)
    ((ringKrullDim_eq_of_ringEquiv (SchemeLFTℂ.specAlgebraΓEquiv X R)).trans_le
      ((ringKrullDim_le_of_surjective _ Ideal.Quotient.mk_surjective).trans hX))
  haveI : IsClosedImmersion (SchemeLFTℂ.specAlgebraHom X R).hom.left := by
    haveI := IsClosedImmersion.spec_of_surjective
      (CommRingCat.ofHom (algebraMap Γ(X.obj.left, ⊤) R)) Ideal.Quotient.mk_surjective
    change IsClosedImmersion (specAlgebraToBase X R)
    rw [specAlgebraToBase]
    infer_instance
  refine essSurj_analytificationFiniteEtaleOver_of_isClosedImmersion
    (SchemeLFTℂ.specAlgebraHom X R) ?_
  change Function.Surjective (specAlgebraToBase X R).base
  rw [specAlgebraToBase, Scheme.Hom.comp_base, TopCat.coe_comp]
  refine (ConcreteCategory.bijective_of_isIso X.obj.left.isoSpec.inv.base).2.comp
    (surjective_Spec_map_base_of_ker_le_nilradical _ Ideal.Quotient.mk_surjective ?_)
  change RingHom.ker (Ideal.Quotient.mk _) ≤ _
  rw [Ideal.mk_ker]

end Dimension

end

end ComplexAnalytic
