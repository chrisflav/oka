/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.ES.EtaleCriterion
import Oka.Analytification.RET.ES.FinitePushforward
import Oka.Analytification.RET.FiniteEtaleFunctor
import Oka.Analytification.RET.ClosedPoints
import Oka.Analytification.RET.Pullback
import Oka.Analytification.GAGA.StalkFlat
import Oka.Analytification.GAGA.CohomologyComparisonLinear
import Oka.Analytification.SchemeLFTNoetherian
import Oka.AnalyticSpace.Evaluation

/-!
# Algebraising finite étale covers from algebra data

Let `V` be an affine scheme of finite type over `ℂ` with `A = Γ(V, 𝒪_V)`, let `p : W ⟶ V^an` be a
finite étale cover and `B` a finite `A`-algebra together with a ring map `φ : B → Γ(W, 𝒪_W)` over
`A`. For every `v ∈ V^an` this gives the map of `𝒪_{V^an,v}`-algebras
`𝒪_{V^an,v} ⊗[A] B → ∏_{w ∈ p⁻¹ v} 𝒪_{W,w}` (`ComplexAnalytic.stalkTensorMap`).

If all these maps are bijective, then `B` is étale over `A`, so `Y = Spec B` is a finite étale
cover of `V`, and the morphism `W ⟶ Y^an` induced by `φ` is an isomorphism over `V^an`
(`ComplexAnalytic.exists_iso_of_bijective_stalkTensorMap`).

The proof: the stalk maps of `p` are isomorphisms, so `𝒪_{V^an,v} ⊗[A] B` is free over
`𝒪_{V^an,v}`; as `𝒪_{V,π v} → 𝒪_{V^an,v}` is faithfully flat and every maximal ideal of `A` is
the ideal of a point `π v`, `B` is flat over `A`. Reducing modulo the maximal ideal of
`𝒪_{V^an,v}` identifies the fibre `ℂ ⊗[A] B` with `ℂ^{p⁻¹ v}`, which is unramified, and whose
maximal ideals are the points of `p⁻¹ v`; so `A → B` is étale and `W ⟶ Y^an` is bijective. It is a
local isomorphism since `W ⟶ V^an` and `Y^an ⟶ V^an` are.

## Main definitions

- `ComplexAnalytic.stalkTensorMap`: the map `𝒪_{V^an,v} ⊗[A] B → ∏_{w ∈ p⁻¹ v} 𝒪_{W,w}`.
- `ComplexAnalytic.SchemeLFTℂ.specAlgebra`: `Spec B` as a scheme of finite type over `ℂ`, over
  `V`.
- `ComplexAnalytic.homSpecAlgebra`: the morphism `W ⟶ (Spec B)^an` induced by `φ`.

## Main results

- `ComplexAnalytic.etale_of_bijective_stalkTensorMap`: `B` is étale over `A`.
- `ComplexAnalytic.isIso_homSpecAlgebra`: `W ⟶ (Spec B)^an` is an isomorphism.
- `ComplexAnalytic.exists_idealOfPoint_eq`: every maximal ideal of `A` is the ideal of a point of
  `V^an`.
- `ComplexAnalytic.exists_iso_of_bijective_stalkTensorMap`: `W` is the analytification of a
  finite étale cover of `V`.
- `ComplexAnalytic.exists_iso_of_bijective_pushforwardStalkTensorMap`: the same, for `W`
  Hausdorff, with the hypothesis on the stalks `(p_* 𝒪_W)_v`
  (`ComplexAnalytic.pushforwardStalkTensorMap`).

## Hypotheses recorded, not proved

- `ComplexAnalytic.FiniteAnalyticSplitting`: for a finite morphism `q : Y ⟶ S` of affine schemes,
  `𝒪_{S^an,s} ⊗ Γ(Y, 𝒪_Y) → ∏_{y ∈ (q^an)⁻¹ s} 𝒪_{Y^an,y}` is bijective, i.e. analytification
  commutes with pushforward along finite morphisms on stalks.
-/

open CategoryTheory Opposite AlgebraicGeometry TensorProduct IsLocalRing

universe u

namespace ComplexAnalytic

open AnalyticSpace

noncomputable section

/-! ### The map on stalks -/

section StalkTensor

variable (V : SchemeLFTℂ.{u})

/-- Pulling back global sections along `π : V^an ⟶ V`. -/
abbrev analytificationΓ :
    Γ(V.obj.left, ⊤) →+* (analytification.obj V).presheaf.obj (op ⊤) :=
  (LocallyRingedSpace.Γ.map (analytificationπLRS V).op).hom

/-- The stalks of `V^an` are `Γ(V, 𝒪_V)`-algebras through `π : V^an ⟶ V`. -/
instance analytificationStalkAlgebra (v : analytification.obj V) :
    Algebra Γ(V.obj.left, ⊤) ((analytification.obj V).presheaf.stalk v) :=
  (((analytification.obj V).presheaf.Γgerm v).hom.comp (analytificationΓ V)).toAlgebra

lemma analytificationStalkAlgebra_algebraMap_apply (v : analytification.obj V)
    (a : Γ(V.obj.left, ⊤)) :
    algebraMap Γ(V.obj.left, ⊤) ((analytification.obj V).presheaf.stalk v) a =
      (analytification.obj V).presheaf.Γgerm v (analytificationΓ V a) :=
  rfl

variable {V} {W : AnalyticSpace.{u}} (p : W ⟶ analytification.obj V) {B : Type u}
  [CommRing B] [Algebra Γ(V.obj.left, ⊤) B] (φ : B →+* W.presheaf.obj (op ⊤))
  (hφ : ∀ a, φ (algebraMap Γ(V.obj.left, ⊤) B a) = p.pullbackΓ (analytificationΓ V a))

/-- **The stalk comparison map** `𝒪_{V^an,v} ⊗[A] B → ∏_{w ∈ p⁻¹ v} 𝒪_{W,w}`, for
`A = Γ(V, 𝒪_V)`, a morphism `p : W ⟶ V^an` and a ring map `φ : B → Γ(W, 𝒪_W)` over `A`:
`s ⊗ b ↦ (p^♯ s · φ(b)_w)_w`. -/
def stalkTensorMap (v : analytification.obj V) :
    (analytification.obj V).presheaf.stalk v ⊗[Γ(V.obj.left, ⊤)] B →+*
      ((w : p.toLRSHom.base ⁻¹' {v}) → W.presheaf.stalk w.1) :=
  letI : Algebra ((analytification.obj V).presheaf.stalk v)
      ((w : p.toLRSHom.base ⁻¹' {v}) → W.presheaf.stalk w.1) :=
    (RingHom.pi fun w ↦ fibreStalkMap p v w).toAlgebra
  letI : Algebra Γ(V.obj.left, ⊤)
      ((w : p.toLRSHom.base ⁻¹' {v}) → W.presheaf.stalk w.1) :=
    ((RingHom.pi fun w ↦ fibreStalkMap p v w).comp
      (algebraMap Γ(V.obj.left, ⊤) ((analytification.obj V).presheaf.stalk v))).toAlgebra
  haveI : IsScalarTower Γ(V.obj.left, ⊤) ((analytification.obj V).presheaf.stalk v)
      ((w : p.toLRSHom.base ⁻¹' {v}) → W.presheaf.stalk w.1) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  (Algebra.TensorProduct.lift (Algebra.ofId _ _)
    { toRingHom := RingHom.pi fun w ↦ (W.presheaf.Γgerm w.1).hom.comp φ
      commutes' := fun a ↦ funext fun w ↦ by
        change W.presheaf.Γgerm w.1 (φ _) = fibreStalkMap p v w
          ((analytification.obj V).presheaf.Γgerm v (analytificationΓ V a))
        rw [hφ]
        exact (fibreStalkMap_Γgerm p v w _).symm }
    fun _ _ ↦ Commute.all _ _).toRingHom

lemma stalkTensorMap_tmul (v : analytification.obj V)
    (s : (analytification.obj V).presheaf.stalk v) (b : B) (w : p.toLRSHom.base ⁻¹' {v}) :
    stalkTensorMap p φ hφ v (s ⊗ₜ b) w =
      fibreStalkMap p v w s * W.presheaf.Γgerm w.1 (φ b) :=
  rfl

end StalkTensor

/-! ### Points of `V^an` and maximal ideals of `Γ(V, 𝒪_V)` -/

section Points

variable (V : SchemeLFTℂ.{u})

/-- The ideal of `Γ(V, 𝒪_V)` of functions vanishing at `v ∈ V^an`. -/
def idealOfPoint (v : analytification.obj V) : Ideal Γ(V.obj.left, ⊤) :=
  Ideal.comap (algebraMap Γ(V.obj.left, ⊤) ((analytification.obj V).presheaf.stalk v))
    (maximalIdeal _)

/-- Evaluation `Γ(V, 𝒪_V) → ℂ` at a point of `V^an`. -/
def evalPoint (v : analytification.obj V) : Γ(V.obj.left, ⊤) →+* ℂ :=
  ((analytification.obj V).evalStalk v).comp
    (algebraMap Γ(V.obj.left, ⊤) ((analytification.obj V).presheaf.stalk v))

lemma evalPoint_algebraMap (v : analytification.obj V) (c : ℂ) :
    evalPoint V v (SchemeLFTℂ.algebraMap V c) = c := by
  have h : analytificationΓ V (SchemeLFTℂ.algebraMap V c) =
      (analytification.obj V).algebraMap c :=
    isCLinearHom_analytificationπLRS c
  change (analytification.obj V).evalStalk v
    ((analytification.obj V).presheaf.Γgerm v (analytificationΓ V _)) = c
  rw [h]
  exact (analytification.obj V).eval_algebraMap v c

lemma evalPoint_surjective (v : analytification.obj V) : Function.Surjective (evalPoint V v) :=
  fun c ↦ ⟨_, evalPoint_algebraMap V v c⟩

lemma ker_evalPoint (v : analytification.obj V) :
    RingHom.ker (evalPoint V v) = idealOfPoint V v := by
  ext a
  simp [evalPoint, idealOfPoint, RingHom.mem_ker]

/-- The ideal of `v ∈ V^an` is the ideal of the point `π v` of `V`. -/
lemma idealOfPoint_eq (v : analytification.obj V) :
    idealOfPoint V v = Ideal.comap (V.obj.left.presheaf.Γgerm
      ((analytificationπLRS V).base v)).hom (maximalIdeal _) := by
  have h : algebraMap Γ(V.obj.left, ⊤) ((analytification.obj V).presheaf.stalk v) =
      ((analytificationπLRS V).stalkMap v).hom.comp
        (V.obj.left.presheaf.Γgerm ((analytificationπLRS V).base v)).hom := by
    ext a
    exact (LocallyRingedSpace.stalkMap_germ_apply (analytificationπLRS V) ⊤ v trivial a).symm
  rw [idealOfPoint, h, ← Ideal.comap_comap, IsLocalRing.maximalIdeal_comap]

lemma isMaximal_idealOfPoint (v : analytification.obj V) : (idealOfPoint V v).IsMaximal := by
  rw [← ker_evalPoint]
  exact RingHom.ker_isMaximal_of_surjective _ (evalPoint_surjective V v)

/-- **Every maximal ideal of `Γ(V, 𝒪_V)` is the ideal of a point of `V^an`**, for `V` affine. -/
theorem exists_idealOfPoint_eq [IsAffine V.obj.left] (P : Ideal Γ(V.obj.left, ⊤))
    [hP : P.IsMaximal] : ∃ v, idealOfPoint V v = P := by
  let y : PrimeSpectrum Γ(V.obj.left, ⊤) := ⟨P, hP.isPrime⟩
  let x := V.obj.left.isoSpec.inv.base y
  have hx : IsClosed ({x} : Set V.obj.left) := by
    rw [← Set.image_singleton]
    exact V.obj.left.isoSpec.inv.isClosedEmbedding.isClosedMap _
      ((PrimeSpectrum.isClosed_singleton_iff_isMaximal y).2 hP)
  obtain ⟨v, hv⟩ := (mem_range_analytificationπ_base_iff V x).2 hx
  refine ⟨v, ?_⟩
  have hy : V.obj.left.toSpecΓ.base x = y := by
    change (V.obj.left.isoSpec.inv ≫ V.obj.left.isoSpec.hom).base y = y
    simp
  rw [idealOfPoint_eq, show (analytificationπLRS V).base v = x from hv]
  exact congrArg PrimeSpectrum.asIdeal hy

end Points

/-! ### The splitting of `𝒪_{V^an,v} ⊗[A] B` -/

section Split

variable {V : SchemeLFTℂ.{u}} {W : AnalyticSpace.{u}} (p : W ⟶ analytification.obj V)
  [hp : IsFiniteEtale p] {B : Type u} [CommRing B] [Algebra Γ(V.obj.left, ⊤) B]
  (φ : B →+* W.presheaf.obj (op ⊤))
  (hφ : ∀ a, φ (algebraMap Γ(V.obj.left, ⊤) B a) = p.pullbackΓ (analytificationΓ V a))
  (v : analytification.obj V)

/-- `stalkTensorMap` composed with the inverses of the stalk maps of `p`:
`𝒪_{V^an,v} ⊗[A] B → 𝒪_{V^an,v}^{p⁻¹ v}`. -/
def stalkSplit : (analytification.obj V).presheaf.stalk v ⊗[Γ(V.obj.left, ⊤)] B →ₐ[
    (analytification.obj V).presheaf.stalk v]
      (p.toLRSHom.base ⁻¹' {v} → (analytification.obj V).presheaf.stalk v) where
  toRingHom := (RingEquiv.piCongrRight fun w ↦ (RingEquiv.ofBijective (fibreStalkMap p v w)
    (bijective_fibreStalkMap p v w)).symm).toRingHom.comp (stalkTensorMap p φ hφ v)
  commutes' s := funext fun w ↦ by
    change (RingEquiv.ofBijective (fibreStalkMap p v w) (bijective_fibreStalkMap p v w)).symm
      (stalkTensorMap p φ hφ v (s ⊗ₜ 1) w) = s
    rw [stalkTensorMap_tmul, map_one, map_one, mul_one]
    exact (RingEquiv.ofBijective _ _).symm_apply_apply s

lemma bijective_stalkSplit (hv : Function.Bijective (stalkTensorMap p φ hφ v)) :
    Function.Bijective (stalkSplit p φ hφ v) := by
  change Function.Bijective ((RingEquiv.piCongrRight fun w ↦ (RingEquiv.ofBijective
    (fibreStalkMap p v w) (bijective_fibreStalkMap p v w)).symm) ∘ stalkTensorMap p φ hφ v)
  exact (RingEquiv.bijective _).comp hv

lemma evalStalk_stalkSplit_one_tmul (b : B) (w : p.toLRSHom.base ⁻¹' {v}) :
    (analytification.obj V).evalStalk v (stalkSplit p φ hφ v (1 ⊗ₜ b) w) =
      W.eval w.1 (U := ⊤) trivial (φ b) := by
  change (analytification.obj V).evalStalk v ((RingEquiv.ofBijective (fibreStalkMap p v w)
      (bijective_fibreStalkMap p v w)).symm (stalkTensorMap p φ hφ v (1 ⊗ₜ b) w)) = _
  rw [← evalStalk_fibreStalkMap p v w, stalkTensorMap_tmul, map_one, one_mul]
  exact congrArg _ ((RingEquiv.ofBijective _ (bijective_fibreStalkMap p v w)).apply_symm_apply
    (W.presheaf.Γgerm w.1 (φ b)))

section Fibre

/-- **The fibre at `v`**: `ℂ ⊗[A] B ≅ ℂ^{p⁻¹ v}`, for `ℂ` an `A`-algebra by evaluation at `v`. -/
lemma exists_fibreAlgEquiv (hv : Function.Bijective (stalkTensorMap p φ hφ v)) :
    letI := (evalPoint V v).toAlgebra
    ∃ E : ℂ ⊗[Γ(V.obj.left, ⊤)] B ≃ₐ[ℂ] (p.toLRSHom.base ⁻¹' {v} → ℂ),
      ∀ b w, E (1 ⊗ₜ b) w = W.eval w.1 (U := ⊤) trivial (φ b) := by
  letI := (evalPoint V v).toAlgebra
  letI : Algebra ((analytification.obj V).presheaf.stalk v) ℂ :=
    ((analytification.obj V).evalStalk v).toAlgebra
  haveI : IsScalarTower Γ(V.obj.left, ⊤) ((analytification.obj V).presheaf.stalk v) ℂ :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI : Finite (p.toLRSHom.base ⁻¹' {v}) := IsFinite.finite_fiber v
  refine ⟨Algebra.TensorProduct.fibreAlgEquivOfBijective _ (bijective_stalkSplit p φ hφ v hv) ℂ,
    fun b w ↦ ?_⟩
  rw [Algebra.TensorProduct.fibreAlgEquivOfBijective_one_tmul]
  exact evalStalk_stalkSplit_one_tmul p φ hφ v b w

end Fibre
/-! ### Étaleness of `B` -/

variable [IsAffine V.obj.left] (hbij : ∀ v, Function.Bijective (stalkTensorMap p φ hφ v))

include hbij in
/-- `B` is flat over `A = Γ(V, 𝒪_V)` at every maximal ideal. -/
theorem flat_localizedModule_of_bijective_stalkTensorMap (P : Ideal Γ(V.obj.left, ⊤))
    [P.IsMaximal] : Module.Flat Γ(V.obj.left, ⊤) (LocalizedModule P.primeCompl B) := by
  obtain ⟨v, rfl⟩ := exists_idealOfPoint_eq V P
  have hU := AlgebraicGeometry.isAffineOpen_top V.obj.left
  let x : (⊤ : V.obj.left.Opens) := ⟨(analytificationπLRS V).base v, trivial⟩
  have hprime : (hU.primeIdealOf x).asIdeal = idealOfPoint V v := by
    rw [idealOfPoint_eq, hU.primeIdealOf_eq_map_closedPoint]
    rfl
  letI : Algebra Γ(V.obj.left, ⊤) (V.obj.left.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk V.obj.left.presheaf x
  letI : Algebra (V.obj.left.presheaf.stalk x) ((analytification.obj V).presheaf.stalk v) :=
    ((analytificationπLRS V).stalkMap v).hom.toAlgebra
  haveI : IsScalarTower Γ(V.obj.left, ⊤) (V.obj.left.presheaf.stalk x)
      ((analytification.obj V).presheaf.stalk v) :=
    IsScalarTower.of_algebraMap_eq fun a ↦
      (LocallyRingedSpace.stalkMap_germ_apply (analytificationπLRS V) ⊤ v trivial a).symm
  haveI : IsLocalization.AtPrime (V.obj.left.presheaf.stalk x) (idealOfPoint V v) := by
    have e : (idealOfPoint V v).primeCompl = (hU.primeIdealOf x).asIdeal.primeCompl := by
      ext a
      rw [Ideal.mem_primeCompl_iff, Ideal.mem_primeCompl_iff, hprime]
    change IsLocalization _ _
    rw [e]
    exact hU.isLocalization_stalk x
  haveI : Module.FaithfullyFlat (V.obj.left.presheaf.stalk x)
      ((analytification.obj V).presheaf.stalk v) :=
    faithfullyFlat_stalkMap_analytificationπ V v
  haveI : Finite (p.toLRSHom.base ⁻¹' {v}) := IsFinite.finite_fiber v
  haveI := Algebra.TensorProduct.flat_of_bijective _ (bijective_stalkSplit p φ hφ v (hbij v))
  exact Module.flat_localizedModule_of_faithfullyFlat _ (V.obj.left.presheaf.stalk x)
    ((analytification.obj V).presheaf.stalk v)

include hbij in
/-- **`B` is étale over `A = Γ(V, 𝒪_V)`** when all the maps `stalkTensorMap` are bijective. -/
theorem etale_of_bijective_stalkTensorMap [Module.Finite Γ(V.obj.left, ⊤) B] :
    Algebra.Etale Γ(V.obj.left, ⊤) B := by
  haveI : IsNoetherianRing Γ(V.obj.left, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
  refine Algebra.Etale.of_forall_isMaximal
    (fun P _ ↦ flat_localizedModule_of_bijective_stalkTensorMap p φ hφ hbij P) fun P hP ↦ ?_
  obtain ⟨v, rfl⟩ := exists_idealOfPoint_eq V P
  letI := (evalPoint V v).toAlgebra
  obtain ⟨E, -⟩ := exists_fibreAlgEquiv p φ hφ v (hbij v)
  haveI : Finite (p.toLRSHom.base ⁻¹' {v}) := IsFinite.finite_fiber v
  exact ⟨ℂ, inferInstance, (evalPoint V v).toAlgebra, evalPoint_surjective V v,
    ker_evalPoint V v, .of_equiv E.symm⟩

end Split
/-! ### `Spec B` as a cover of `V` -/

section SpecAlgebra

variable (V : SchemeLFTℂ.{u}) [IsAffine V.obj.left] (B : Type u) [CommRing B]
  [Algebra Γ(V.obj.left, ⊤) B]

/-- The structure morphism `Spec B ⟶ Spec Γ(V, 𝒪_V) ≅ V`. -/
def specAlgebraToBase : Spec (CommRingCat.of B) ⟶ V.obj.left :=
  Spec.map (CommRingCat.ofHom (algebraMap Γ(V.obj.left, ⊤) B)) ≫ V.obj.left.isoSpec.inv

instance [Module.Finite Γ(V.obj.left, ⊤) B] : IsFinite (specAlgebraToBase V B) := by
  have : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap Γ(V.obj.left, ⊤) B))) := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.2 inferInstance
  rw [specAlgebraToBase]
  infer_instance

instance [Algebra.Etale Γ(V.obj.left, ⊤) B] : Etale (specAlgebraToBase V B) := by
  have : Etale (Spec.map (CommRingCat.ofHom (algebraMap Γ(V.obj.left, ⊤) B))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    exact RingHom.etale_algebraMap.2 inferInstance
  rw [specAlgebraToBase]
  infer_instance

variable [Module.Finite Γ(V.obj.left, ⊤) B]

/-- `Spec B`, for a finite `Γ(V, 𝒪_V)`-algebra `B`, as a scheme of finite type over `ℂ`. -/
def SchemeLFTℂ.specAlgebra : SchemeLFTℂ.{u} :=
  ⟨Over.mk (specAlgebraToBase V B ≫ V.obj.hom), by
    haveI : LocallyOfFiniteType V.obj.hom := V.property
    change LocallyOfFiniteType (specAlgebraToBase V B ≫ V.obj.hom)
    infer_instance⟩

/-- The finite morphism `Spec B ⟶ V`. -/
def SchemeLFTℂ.specAlgebraHom : SchemeLFTℂ.specAlgebra V B ⟶ V :=
  ObjectProperty.homMk (Over.homMk (specAlgebraToBase V B))

@[simp]
lemma SchemeLFTℂ.specAlgebraHom_hom_left :
    (SchemeLFTℂ.specAlgebraHom V B).hom.left = specAlgebraToBase V B :=
  rfl

/-- For `B` étale over `Γ(V, 𝒪_V)`, `Spec B ⟶ V` is finite étale. -/
theorem SchemeLFTℂ.isFiniteEtale_specAlgebraHom [Algebra.Etale Γ(V.obj.left, ⊤) B] :
    SchemeLFTℂ.isFiniteEtale (SchemeLFTℂ.specAlgebraHom V B) :=
  ⟨(inferInstance : IsFinite (specAlgebraToBase V B)),
    (inferInstance : Etale (specAlgebraToBase V B))⟩

/-- `Spec B`, for a finite étale `Γ(V, 𝒪_V)`-algebra `B`, as a finite étale cover of `V`. -/
def SchemeLFTℂ.specAlgebraFiniteEtaleOver (h : Algebra.Etale Γ(V.obj.left, ⊤) B) :
    SchemeLFTℂ.FiniteEtaleOver V :=
  MorphismProperty.Over.mk ⊤ (SchemeLFTℂ.specAlgebraHom V B)
    (SchemeLFTℂ.isFiniteEtale_specAlgebraHom V B)

end SpecAlgebra

/-! ### The morphism `W ⟶ (Spec B)^an` -/

section Hom

variable {V : SchemeLFTℂ.{u}} [IsAffine V.obj.left] {W : AnalyticSpace.{u}}
  (p : W ⟶ analytification.obj V) {B : Type u} [CommRing B] [Algebra Γ(V.obj.left, ⊤) B]
  [Module.Finite Γ(V.obj.left, ⊤) B] (φ : B →+* W.presheaf.obj (op ⊤))
  (hφ : ∀ a, φ (algebraMap Γ(V.obj.left, ⊤) B a) = p.pullbackΓ (analytificationΓ V a))

variable (V) in
/-- The morphism `W ⟶ Spec B` of locally ringed spaces corresponding to `φ`. -/
def specAlgebraLRSHom :
    W.toLocallyRingedSpace ⟶ (SchemeLFTℂ.specAlgebra V B).obj.left.toLocallyRingedSpace :=
  W.toLocallyRingedSpace.toSpecOfAlgMap φ

include hφ in
lemma specAlgebraLRSHom_comp_specMap :
    specAlgebraLRSHom V φ ≫
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(V.obj.left, ⊤) B))).toLRSHom =
      W.toLocallyRingedSpace.toΓSpec ≫ Spec.locallyRingedSpaceMap
        (LocallyRingedSpace.Γ.map (p.toLRSHom ≫ analytificationπLRS V).op) := by
  change W.toLocallyRingedSpace.toΓSpec ≫ Spec.locallyRingedSpaceMap (CommRingCat.ofHom φ) ≫
    Spec.locallyRingedSpaceMap (CommRingCat.ofHom (algebraMap Γ(V.obj.left, ⊤) B)) = _
  rw [← Spec.locallyRingedSpaceMap_comp]
  congr 2
  ext a
  change φ (algebraMap _ B a) =
    (LocallyRingedSpace.Γ.map (p.toLRSHom ≫ analytificationπLRS V).op).hom a
  rw [hφ, LocallyRingedSpace.Γ_map_comp_apply]
  rfl

include hφ in
lemma specAlgebraLRSHom_comp :
    specAlgebraLRSHom V φ ≫ (specAlgebraToBase V B).toLRSHom =
      p.toLRSHom ≫ analytificationπLRS V := by
  have h2 := LocallyRingedSpace.toΓSpec_naturality (p.toLRSHom ≫ analytificationπLRS V)
  have h4 : V.obj.left.toLocallyRingedSpace.toΓSpec ≫ V.obj.left.isoSpec.inv.toLRSHom = 𝟙 _ :=
    congrArg Scheme.Hom.toLRSHom V.obj.left.isoSpec.hom_inv_id
  calc specAlgebraLRSHom V φ ≫ (specAlgebraToBase V B).toLRSHom
      = (specAlgebraLRSHom V φ ≫
          (Spec.map (CommRingCat.ofHom (algebraMap Γ(V.obj.left, ⊤) B))).toLRSHom) ≫
          V.obj.left.isoSpec.inv.toLRSHom := rfl
    _ = ((p.toLRSHom ≫ analytificationπLRS V) ≫ V.obj.left.toLocallyRingedSpace.toΓSpec) ≫
          V.obj.left.isoSpec.inv.toLRSHom := by
        rw [specAlgebraLRSHom_comp_specMap p φ hφ, h2]
        rfl
    _ = p.toLRSHom ≫ analytificationπLRS V := by
        rw [Category.assoc, h4, Category.comp_id]

include hφ in
/-- The morphism `W ⟶ Spec B` over `Spec ℂ` corresponding to `φ`. -/
def specAlgebraOverHom :
    toOverSpec.obj W ⟶ schemeToOverSpec.obj (SchemeLFTℂ.specAlgebra V B).obj :=
  Over.homMk (specAlgebraLRSHom V φ) (by
    have hπ : analytificationπLRS V ≫ V.obj.hom.toLRSHom = (analytification.obj V).toSpecℂ :=
      Over.w (analytificationπ V)
    calc specAlgebraLRSHom V φ ≫ (specAlgebraToBase V B ≫ V.obj.hom).toLRSHom
        = (specAlgebraLRSHom V φ ≫ (specAlgebraToBase V B).toLRSHom) ≫ V.obj.hom.toLRSHom := rfl
      _ = p.toLRSHom ≫ (analytification.obj V).toSpecℂ := by
        rw [specAlgebraLRSHom_comp p φ hφ, Category.assoc, hπ]
        rfl
      _ = W.toSpecℂ := Over.w (toOverSpec.map p))

/-- **The morphism `W ⟶ (Spec B)^an`** induced by `φ : B → Γ(W, 𝒪_W)`. -/
def homSpecAlgebra : W ⟶ analytification.obj (SchemeLFTℂ.specAlgebra V B) :=
  (analytificationHomEquiv W _).symm (specAlgebraOverHom p φ hφ)

lemma homSpecAlgebra_comp_analytificationπLRS :
    (homSpecAlgebra p φ hφ).toLRSHom ≫ analytificationπLRS _ = specAlgebraLRSHom V φ := by
  have h := analytificationHomEquiv_apply (homSpecAlgebra p φ hφ)
  rw [homSpecAlgebra, Equiv.apply_symm_apply] at h
  exact (congrArg CommaMorphism.left h).symm

@[reassoc (attr := simp)]
lemma homSpecAlgebra_comp :
    homSpecAlgebra p φ hφ ≫ analytification.map (SchemeLFTℂ.specAlgebraHom V B) = p := by
  apply (analytificationHomEquiv W V).injective
  rw [analytificationHomEquiv_comp, homSpecAlgebra, Equiv.apply_symm_apply,
    analytificationHomEquiv_apply]
  exact Over.OverMorphism.ext (specAlgebraLRSHom_comp p φ hφ)

lemma mem_specAlgebraLRSHom_base_iff (w : W) (b : B) :
    b ∈ ((specAlgebraLRSHom V φ).base w).asIdeal ↔ W.eval w (U := ⊤) trivial (φ b) = 0 := by
  rw [eval_eq_zero_iff]
  rfl

end Hom
/-! ### The main theorem -/

section Main

variable {V : SchemeLFTℂ.{u}} [IsAffine V.obj.left] {W : AnalyticSpace.{u}}
  (p : W ⟶ analytification.obj V) [hp : IsFiniteEtale p] {B : Type u} [CommRing B]
  [Algebra Γ(V.obj.left, ⊤) B] [Module.Finite Γ(V.obj.left, ⊤) B]
  (φ : B →+* W.presheaf.obj (op ⊤))
  (hφ : ∀ a, φ (algebraMap Γ(V.obj.left, ⊤) B a) = p.pullbackΓ (analytificationΓ V a))
  (hbij : ∀ v, Function.Bijective (stalkTensorMap p φ hφ v))

/-- The prime of `B` of a point `y ∈ (Spec B)^an` contracts to the ideal of its image in `V^an`. -/
lemma comap_analytificationπLRS_base (y : analytification.obj (SchemeLFTℂ.specAlgebra V B)) :
    ((analytificationπLRS _).base y).asIdeal.comap (algebraMap Γ(V.obj.left, ⊤) B) =
      idealOfPoint V ((analytification.map (SchemeLFTℂ.specAlgebraHom V B)).toLRSHom.base y) := by
  set n := (analytificationπLRS _).base y
  have e1 : (analytificationπLRS V).base
      ((analytification.map (SchemeLFTℂ.specAlgebraHom V B)).toLRSHom.base y) =
      (specAlgebraToBase V B).base n :=
    congrArg (fun f ↦ f.base y)
      (analytificationπLRS_naturality (SchemeLFTℂ.specAlgebraHom V B))
  have e2 : V.obj.left.toSpecΓ.base ((analytificationπLRS V).base
      ((analytification.map (SchemeLFTℂ.specAlgebraHom V B)).toLRSHom.base y)) =
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(V.obj.left, ⊤) B))).base n := by
    rw [e1]
    change (Spec.map (CommRingCat.ofHom (algebraMap Γ(V.obj.left, ⊤) B)) ≫
      V.obj.left.isoSpec.inv ≫ V.obj.left.isoSpec.hom).base n = _
    simp
  rw [idealOfPoint_eq]
  exact (congrArg PrimeSpectrum.asIdeal e2).symm

include hbij in
/-- **`W ⟶ (Spec B)^an` is bijective.** -/
theorem bijective_homSpecAlgebra :
    Function.Bijective (homSpecAlgebra p φ hφ).toLRSHom.base := by
  have hc : ∀ w, (analytification.map (SchemeLFTℂ.specAlgebraHom V B)).toLRSHom.base
      ((homSpecAlgebra p φ hφ).toLRSHom.base w) = p.toLRSHom.base w := fun w ↦
    congrArg (fun f : W ⟶ _ ↦ f.toLRSHom.base w) (homSpecAlgebra_comp p φ hφ)
  have hπ : ∀ w, (analytificationπLRS _).base ((homSpecAlgebra p φ hφ).toLRSHom.base w) =
      (specAlgebraLRSHom V φ).base w := fun w ↦
    congrArg (fun f ↦ f.base w) (homSpecAlgebra_comp_analytificationπLRS p φ hφ)
  constructor
  · intro w₁ w₂ h
    have h2 : p.toLRSHom.base w₂ ∈ ({p.toLRSHom.base w₁} : Set _) := by
      change p.toLRSHom.base w₂ = p.toLRSHom.base w₁
      rw [← hc w₂, ← h, hc]
    letI := (evalPoint V (p.toLRSHom.base w₁)).toAlgebra
    obtain ⟨E, hE⟩ := exists_fibreAlgEquiv p φ hφ _ (hbij (p.toLRSHom.base w₁))
    have := Algebra.TensorProduct.eq_of_forall_fibre_eq_zero_iff
      (evalPoint_surjective V (p.toLRSHom.base w₁)) E (i := ⟨w₁, rfl⟩) (j := ⟨w₂, h2⟩)
      fun b ↦ by
        rw [hE, hE, ← mem_specAlgebraLRSHom_base_iff (V := V),
          ← mem_specAlgebraLRSHom_base_iff (V := V), ← hπ, ← hπ, h]
    exact congrArg Subtype.val this
  · intro y
    set v := (analytification.map (SchemeLFTℂ.specAlgebraHom V B)).toLRSHom.base y
    letI := (evalPoint V v).toAlgebra
    obtain ⟨E, hE⟩ := exists_fibreAlgEquiv p φ hφ v (hbij v)
    have hn : RingHom.ker (algebraMap Γ(V.obj.left, ⊤) ℂ) ≤
        ((analytificationπLRS _).base y).asIdeal.comap (algebraMap Γ(V.obj.left, ⊤) B) := by
      rw [comap_analytificationπLRS_base]
      exact (ker_evalPoint V v).le
    haveI : Finite (p.toLRSHom.base ⁻¹' {v}) := IsFinite.finite_fiber v
    obtain ⟨w, hw⟩ := Algebra.TensorProduct.exists_forall_mem_iff_fibre_eq_zero
      (evalPoint_surjective V v) E _ hn
    refine ⟨w.1, analytificationπ_base_injective _ ?_⟩
    change (analytificationπLRS _).base _ = (analytificationπLRS _).base y
    rw [hπ]
    refine PrimeSpectrum.ext (Ideal.ext fun b ↦ ?_)
    rw [mem_specAlgebraLRSHom_base_iff (V := V), ← hE, hw b]

include hbij in
/-- **`W ⟶ (Spec B)^an` is an isomorphism.** -/
theorem isIso_homSpecAlgebra : IsIso (homSpecAlgebra p φ hφ) := by
  haveI := etale_of_bijective_stalkTensorMap p φ hφ hbij
  haveI : Etale (SchemeLFTℂ.specAlgebraHom V B).hom.left :=
    (inferInstance : Etale (specAlgebraToBase V B))
  haveI := isLocalIso_analytification_map_of_etale (SchemeLFTℂ.specAlgebraHom V B)
  haveI : IsLocalIso (homSpecAlgebra p φ hφ ≫
      analytification.map (SchemeLFTℂ.specAlgebraHom V B)) := by
    rw [homSpecAlgebra_comp]
    infer_instance
  haveI := isLocalIso_of_comp (homSpecAlgebra p φ hφ)
    (analytification.map (SchemeLFTℂ.specAlgebraHom V B))
  exact isIso_of_isLocalIso_of_bijective _ (bijective_homSpecAlgebra p φ hφ hbij)

end Main

/-- **Algebraisation of a finite étale cover from algebra data.** Let `V` be an affine scheme of
finite type over `ℂ`, `W` a finite étale cover of `V^an`, `B` a finite `Γ(V, 𝒪_V)`-algebra and
`φ : B → Γ(W, 𝒪_W)` a ring map over `Γ(V, 𝒪_V)` such that for every `v ∈ V^an` the map
`𝒪_{V^an,v} ⊗[Γ(V, 𝒪_V)] B → ∏_{w ∈ p⁻¹ v} 𝒪_{W,w}` is bijective. Then `B` is étale over
`Γ(V, 𝒪_V)` and `W` is the analytification of the finite étale cover `Spec B` of `V`. -/
theorem exists_iso_of_bijective_stalkTensorMap (V : SchemeLFTℂ.{u}) [IsAffine V.obj.left]
    (W : AnalyticSpace.FiniteEtaleOver (analytification.obj V)) (B : Type u) [CommRing B]
    [Algebra Γ(V.obj.left, ⊤) B] [Module.Finite Γ(V.obj.left, ⊤) B]
    (φ : B →+* W.left.presheaf.obj (op ⊤))
    (hφ : ∀ a, φ (algebraMap Γ(V.obj.left, ⊤) B a) = W.hom.pullbackΓ (analytificationΓ V a))
    (hbij : ∀ v, Function.Bijective (stalkTensorMap W.hom φ hφ v)) :
    ∃ h : Algebra.Etale Γ(V.obj.left, ⊤) B,
      Nonempty ((analytificationFiniteEtaleOver V).obj
        (SchemeLFTℂ.specAlgebraFiniteEtaleOver V B h) ≅ W) := by
  haveI := isIso_homSpecAlgebra (hp := W.prop) W.hom φ hφ hbij
  refine ⟨etale_of_bijective_stalkTensorMap (hp := W.prop) W.hom φ hφ hbij,
    ⟨MorphismProperty.Over.isoMk (asIso (homSpecAlgebra W.hom φ hφ)).symm ?_⟩⟩
  change inv (homSpecAlgebra W.hom φ hφ) ≫ W.hom =
    analytification.map (SchemeLFTℂ.specAlgebraHom V B)
  rw [IsIso.inv_comp_eq]
  exact (homSpecAlgebra_comp W.hom φ hφ).symm
/-! ### The criterion in terms of `p_* 𝒪_W` -/

section Pushforward

variable {V : SchemeLFTℂ.{u}} {W : AnalyticSpace.{u}} (p : W ⟶ analytification.obj V)
  {B : Type u} [CommRing B] [Algebra Γ(V.obj.left, ⊤) B] (φ : B →+* W.presheaf.obj (op ⊤))
  (hφ : ∀ a, φ (algebraMap Γ(V.obj.left, ⊤) B a) = p.pullbackΓ (analytificationΓ V a))

/-- **The map `𝒪_{V^an,v} ⊗[A] B → (p_* 𝒪_W)_v`**, `s ⊗ b ↦ p^♯ s · φ(b)_v`, for
`A = Γ(V, 𝒪_V)`; here `φ(b)` is a global section of `p_* 𝒪_W`. -/
def pushforwardStalkTensorMap (v : analytification.obj V) :
    (analytification.obj V).presheaf.stalk v ⊗[Γ(V.obj.left, ⊤)] B →+*
      (p.toLRSHom.base _* W.presheaf).stalk v :=
  letI : Algebra ((analytification.obj V).presheaf.stalk v)
      ((p.toLRSHom.base _* W.presheaf).stalk v) :=
    (pushforwardStalkAlgebraMap p v).toAlgebra
  letI : Algebra Γ(V.obj.left, ⊤) ((p.toLRSHom.base _* W.presheaf).stalk v) :=
    ((pushforwardStalkAlgebraMap p v).comp
      (algebraMap Γ(V.obj.left, ⊤) ((analytification.obj V).presheaf.stalk v))).toAlgebra
  haveI : IsScalarTower Γ(V.obj.left, ⊤) ((analytification.obj V).presheaf.stalk v)
      ((p.toLRSHom.base _* W.presheaf).stalk v) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  (Algebra.TensorProduct.lift (Algebra.ofId _ _)
    { toRingHom := ((p.toLRSHom.base _* W.presheaf).germ ⊤ v trivial).hom.comp φ
      commutes' := fun a ↦ by
        change (p.toLRSHom.base _* W.presheaf).germ ⊤ v trivial (φ _) =
          pushforwardStalkAlgebraMap p v
            ((analytification.obj V).presheaf.Γgerm v (analytificationΓ V a))
        rw [hφ]
        erw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
        rfl }
    fun _ _ ↦ Commute.all _ _).toRingHom

lemma pushforwardStalkTensorMap_tmul (v : analytification.obj V)
    (s : (analytification.obj V).presheaf.stalk v) (b : B) :
    pushforwardStalkTensorMap p φ hφ v (s ⊗ₜ b) =
      pushforwardStalkAlgebraMap p v s * (p.toLRSHom.base _* W.presheaf).germ ⊤ v trivial (φ b) :=
  rfl

/-- `stalkTensorMap` is `pushforwardStalkTensorMap` followed by
`(p_* 𝒪_W)_v → ∏_{w ∈ p⁻¹ v} 𝒪_{W,w}`. -/
lemma pushforwardStalkToPi_pushforwardStalkTensorMap (v : analytification.obj V)
    (x : (analytification.obj V).presheaf.stalk v ⊗[Γ(V.obj.left, ⊤)] B) :
    TopCat.Presheaf.pushforwardStalkToPi p.toLRSHom.base W.presheaf v
      (pushforwardStalkTensorMap p φ hφ v x) = stalkTensorMap p φ hφ v x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul s b =>
    funext w
    rw [pushforwardStalkTensorMap_tmul, map_mul, Pi.mul_apply,
      pushforwardStalkToPi_stalkFunctor_map, TopCat.Presheaf.pushforwardStalkToPi_germ,
      stalkTensorMap_tmul]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- **Algebraisation of a finite étale cover from algebra data, in terms of `p_* 𝒪_W`.** For a
Hausdorff finite étale cover `p : W ⟶ V^an` of an affine `V`, a finite `Γ(V, 𝒪_V)`-algebra `B`
and a ring map `φ : B → Γ(W, 𝒪_W)` over `Γ(V, 𝒪_V)` such that
`𝒪_{V^an,v} ⊗[Γ(V, 𝒪_V)] B → (p_* 𝒪_W)_v` is bijective for every `v`, `W` is the
analytification of the finite étale cover `Spec B` of `V`. -/
theorem exists_iso_of_bijective_pushforwardStalkTensorMap (V : SchemeLFTℂ.{u})
    [IsAffine V.obj.left] (W : AnalyticSpace.FiniteEtaleOver (analytification.obj V))
    [T2Space W.left] (B : Type u) [CommRing B] [Algebra Γ(V.obj.left, ⊤) B]
    [Module.Finite Γ(V.obj.left, ⊤) B] (φ : B →+* W.left.presheaf.obj (op ⊤))
    (hφ : ∀ a, φ (algebraMap Γ(V.obj.left, ⊤) B a) = W.hom.pullbackΓ (analytificationΓ V a))
    (hbij : ∀ v, Function.Bijective (pushforwardStalkTensorMap W.hom φ hφ v)) :
    ∃ h : Algebra.Etale Γ(V.obj.left, ⊤) B,
      Nonempty ((analytificationFiniteEtaleOver V).obj
        (SchemeLFTℂ.specAlgebraFiniteEtaleOver V B h) ≅ W) := by
  refine exists_iso_of_bijective_stalkTensorMap V W B φ hφ fun v ↦ ?_
  have h : ⇑(stalkTensorMap W.hom φ hφ v) =
      TopCat.Presheaf.pushforwardStalkToPi W.hom.toLRSHom.base W.left.presheaf v ∘
        pushforwardStalkTensorMap W.hom φ hφ v :=
    funext fun x ↦ (pushforwardStalkToPi_pushforwardStalkTensorMap W.hom φ hφ v x).symm
  rw [h]
  have hfin : AnalyticSpace.IsFinite (W.hom : W.left ⟶ analytification.obj V) :=
    IsFiniteEtale.isFinite (self := W.prop)
  exact (@bijective_pushforwardStalkToPi W.left (analytification.obj V) W.hom v hfin
    ‹_›).comp (hbij v)

end Pushforward
/-! ### Finite morphisms of schemes -/

section Finite

variable {Y S : SchemeLFTℂ.{u}} (q : Y ⟶ S)

/-- Pulling back global sections commutes with analytification. -/
lemma analytificationΓ_naturality (a : Γ(S.obj.left, ⊤)) :
    analytificationΓ Y (q.hom.left.appTop a) =
      (analytification.map q).pullbackΓ (analytificationΓ S a) := by
  have h := congrArg (fun f : (analytification.obj Y).toLocallyRingedSpace ⟶
      S.obj.left.toLocallyRingedSpace ↦ (LocallyRingedSpace.Γ.map f.op).hom a)
    (analytificationπLRS_naturality q)
  simp only [op_comp, Functor.map_comp, CommRingCat.hom_comp, RingHom.coe_comp,
    Function.comp_apply] at h
  exact h.symm

/-- **Analytic splitting of finite morphisms**: for a finite morphism `q : Y ⟶ S` of affine
schemes of finite type over `ℂ` and `s ∈ S^an`, the map
`𝒪_{S^an,s} ⊗[Γ(S, 𝒪_S)] Γ(Y, 𝒪_Y) → ∏_{y ∈ (q^an)⁻¹ s} 𝒪_{Y^an,y}` is bijective. With
`TopCat.Presheaf.pushforwardStalkToPi` this is the statement that
`(q_* 𝒪_Y)^an → q^an_* 𝒪_{Y^an}` is an isomorphism on stalks. It is recorded here as a
hypothesis; it is not proved in this file. -/
def FiniteAnalyticSplitting : Prop :=
  ∀ (Y S : SchemeLFTℂ.{u}) [IsAffine Y.obj.left] [IsAffine S.obj.left] (q : Y ⟶ S)
    [AlgebraicGeometry.IsFinite q.hom.left] (s : analytification.obj S),
    letI := q.hom.left.appTop.hom.toAlgebra
    Function.Bijective (stalkTensorMap (analytification.map q) (analytificationΓ Y)
      (analytificationΓ_naturality q) s)

end Finite

end

end ComplexAnalytic
