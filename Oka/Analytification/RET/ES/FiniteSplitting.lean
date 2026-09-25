/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.ES.Algebraize
import Oka.Analytification.GAGA.Proper.RelativeBaseChangeIso
import Oka.AnalyticSpace.HomToComplex
import Oka.AnalyticSpace.MonicSplitting

/-!
# Analytification commutes with finite pushforward on stalks

Let `q : Y ⟶ S` be a finite morphism of affine schemes of finite type over `ℂ`, with
`A = Γ(S, 𝒪_S)` and `B = Γ(Y, 𝒪_Y)`. For every `s ∈ S^an` the map

  `𝒪_{S^an,s} ⊗[A] B → ∏_{y ∈ (q^an)⁻¹ s} 𝒪_{Y^an,y}`

is bijective (`ComplexAnalytic.finiteAnalyticSplitting`), which discharges
`ComplexAnalytic.FiniteAnalyticSplitting`.

Choose a surjection `ℂ[x₁, …, x_n] → A` and module generators `b₁, …, b_m` of `B` over `A`; each
`b_j` is a root of a monic `P_j ∈ ℂ[x][t]`. This gives closed immersions `S ⟶ 𝔸ⁿ` and
`Y ⟶ 𝔸^{n+m}`, whose analytifications, composed with `(𝔸^N)^an ≅ ℂ^N`, are cut out by
polynomials (`ComplexAnalytic.SchemeLFTℂ.exists_cutOut`). Writing `w₀ ∈ ℂⁿ` for the image of `s`,
both sides are then quotients of `ℂ{x}[t₁, …, t_m]`, the germs at `w₀` of functions of `x` with
the variables `t` adjoined, and the statement follows from the splitting
`ℂ{x}[t] ⧸ (P_j(t_j)) ≅ ∏_c ℂ{x, t - c} ⧸ (P_j(t_j))` (`LocalOkaRing.isPiQuotient_germMap`) by
passing to the quotient by the ideal of `Y`.

## Main definitions

- `ComplexAnalytic.polyFun`: polynomials as holomorphic functions on `ℂ^N`.
- `ComplexAnalytic.taylorGerm`: the germ of a polynomial at a point of `ℂ^N`, expanded there.
- `ComplexAnalytic.stalkEquiv`: the stalks of `ℂ^N` as germs at the origin.
- `ComplexAnalytic.SchemeLFTℂ.toAffineSpace`: the morphism `Z ⟶ 𝔸^N` given by global sections.
- `ComplexAnalytic.SchemeLFTℂ.anToAffine`: its analytification, as a morphism `Z^an ⟶ ℂ^N`.

## Main results

- `ComplexAnalytic.SchemeLFTℂ.exists_cutOut`: cut-out data for `Z^an ⟶ ℂ^N`.
- `ComplexAnalytic.bijective_stalkTensorMap_of_presentation`: the splitting for presented `q`.
- `ComplexAnalytic.finiteAnalyticSplitting`: `ComplexAnalytic.FiniteAnalyticSplitting` holds.
-/

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open scoped Polynomial TensorProduct

universe u

namespace ComplexAnalytic

open AnalyticSpace

noncomputable section

variable {N : ℕ}

/-- Polynomials in `N` variables as holomorphic functions on `ℂ^N`. -/
def polyFun (N : ℕ) : MvPolynomial (Fin N) (ULift.{u} ℂ) →+*
    (AnalyticSpace.complexAffineSpace.{u} N).presheaf.obj (op ⊤) :=
  MvPolynomial.eval₂Hom ((algebraMap ℂ (OkaRing (⊤ : Opens (ULift.{u} (Fin N) → ℂ)))).comp
    ULift.ringEquiv.toRingHom) fun i ↦ coord ⟨i⟩

lemma eval_polyFun (w : AnalyticSpace.complexAffineSpace.{u} N)
    (p : MvPolynomial (Fin N) (ULift.{u} ℂ)) :
    (AnalyticSpace.complexAffineSpace.{u} N).eval (U := ⊤) w trivial (polyFun N p) =
      affineEval N w p := by
  refine congrArg (fun φ : MvPolynomial (Fin N) (ULift.{u} ℂ) →+* ℂ ↦ φ p)
    (MvPolynomial.ringHom_ext (fun c ↦ ?_) (fun i ↦ ?_) :
      ((AnalyticSpace.complexAffineSpace.{u} N).eval (U := ⊤) w trivial).comp (polyFun N) =
        affineEval N w)
  · simp only [RingHom.coe_comp, Function.comp_apply, polyFun, MvPolynomial.eval₂Hom_C,
      affineEval]
    exact AnalyticSpace.eval_algebraMap _ w _
  · simp only [RingHom.coe_comp, Function.comp_apply, polyFun, MvPolynomial.eval₂Hom_X',
      affineEval]
    exact eval_coord w ⟨i⟩

/-- The value at `x ∈ (𝔸^N)^an` of the pullback of a polynomial is its value at the coordinates
of `x`. -/
lemma eval_analytificationΓ_affineSpace (x : analytification.obj (affineSpace.{u} N))
    (p : MvPolynomial (Fin N) (ULift.{u} ℂ)) :
    (analytification.obj (affineSpace.{u} N)).eval (U := ⊤) x trivial
      (analytificationΓ (affineSpace.{u} N) ((Scheme.ΓSpecIso (.of _)).inv p)) =
      affineEval N ((analytificationAffineSpaceIso.{u} N).hom.toLRSHom.base x) p := by
  refine eval_analytificationπ_eq (V := ⊤) _ x trivial _ ?_
  erw [TopCat.Presheaf.restrict_self]
  rw [relProjectiveSpaceAn.schemeConst_affineSpace]
  change ¬IsUnit ((Spec (CommRingCat.of (MvPolynomial (Fin N) (ULift.{u} ℂ)))).presheaf.germ ⊤
    ((analytificationπLRS (affineSpace.{u} N)).base x) trivial (_ - _))
  rw [← map_sub, ← Scheme.mem_basicOpen, basicOpen_eq_of_affine]
  intro hmem
  refine hmem ?_
  erw [relProjectiveSpaceAn.analytificationπ_affineSpace_base x]
  rw [complexAffineSpaceπ_base_asIdeal, RingHom.mem_ker, map_sub, sub_eq_zero]
  simp [affineEval]
  rfl

/-- **Polynomials on `(𝔸^N)^an ≅ ℂ^N`**: the pullback of the polynomial function `p` on `ℂ^N`
is the pullback of `p` along `(𝔸^N)^an ⟶ 𝔸^N`. -/
lemma Γ_map_polyFun (p : MvPolynomial (Fin N) (ULift.{u} ℂ)) :
    (LocallyRingedSpace.Γ.map (analytificationAffineSpaceIso.{u} N).hom.toLRSHom.op).hom
      (polyFun N p) =
      analytificationΓ (affineSpace.{u} N) ((Scheme.ΓSpecIso (.of _)).inv p) := by
  refine relProjectiveSpaceAn.eq_of_eval (W := ⊤) fun x hx ↦ ?_
  rw [eval_analytificationΓ_affineSpace, ← eval_polyFun]
  exact eval_c_app _ (analytificationAffineSpaceIso.{u} N).hom.isCLinear (U := ⊤) x trivial _

/-- The germ at `w ∈ ℂ^N` of a polynomial, as a germ at the origin in `Fin N` variables:
`p(w + x)`. -/
def taylorGerm (w : ULift.{u} (Fin N) → ℂ) :
    MvPolynomial (Fin N) (ULift.{u} ℂ) →+* LocalOkaRing (Fin N) :=
  MvPolynomial.eval₂Hom ((algebraMap ℂ _).comp ULift.ringEquiv.toRingHom)
    fun i ↦ LocalOkaRing.coord i + algebraMap ℂ _ (w ⟨i⟩)

lemma constantCoeff_taylorGerm (w : ULift.{u} (Fin N) → ℂ)
    (p : MvPolynomial (Fin N) (ULift.{u} ℂ)) :
    LocalOkaRing.constantCoeff (taylorGerm w p) = affineEval N w p := by
  refine congrArg (fun φ : MvPolynomial (Fin N) (ULift.{u} ℂ) →+* ℂ ↦ φ p)
    (MvPolynomial.ringHom_ext (fun c ↦ ?_) (fun i ↦ ?_) :
      LocalOkaRing.constantCoeff.comp (taylorGerm w) = affineEval N w)
  · simp only [RingHom.coe_comp, Function.comp_apply, taylorGerm, MvPolynomial.eval₂Hom_C,
      affineEval, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    exact LocalOkaRing.constantCoeff_algebraMap _
  · simp only [RingHom.coe_comp, Function.comp_apply, taylorGerm, MvPolynomial.eval₂Hom_X',
      affineEval]
    rw [map_add, LocalOkaRing.constantCoeff_coord, LocalOkaRing.constantCoeff_algebraMap, zero_add]

/-- The stalks of `ℂ^N`, as germs at the origin in `Fin N` variables. -/
def stalkEquiv (w : AnalyticSpace.complexAffineSpace.{u} N) :
    (AnalyticSpace.complexAffineSpace.{u} N).presheaf.stalk w ≃+* LocalOkaRing (Fin N) :=
  (okaStalkEquiv (ι := ULift.{u} (Fin N)) w).trans
    (LocalOkaRing.uliftEquiv (Fin N)).toRingEquiv

lemma stalkEquiv_Γgerm_polyFun (w : AnalyticSpace.complexAffineSpace.{u} N)
    (p : MvPolynomial (Fin N) (ULift.{u} ℂ)) :
    stalkEquiv w ((AnalyticSpace.complexAffineSpace.{u} N).presheaf.Γgerm w (polyFun N p)) =
      taylorGerm w p := by
  refine congrArg (fun φ : MvPolynomial (Fin N) (ULift.{u} ℂ) →+* LocalOkaRing (Fin N) ↦ φ p)
    (MvPolynomial.ringHom_ext (fun c ↦ ?_) (fun i ↦ ?_) :
      ((stalkEquiv w).toRingHom.comp
        ((AnalyticSpace.complexAffineSpace.{u} N).presheaf.Γgerm w).hom).comp (polyFun N) =
        taylorGerm w)
  · simp only [RingHom.coe_comp, Function.comp_apply, polyFun, MvPolynomial.eval₂Hom_C,
      taylorGerm, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    change (LocalOkaRing.uliftEquiv (Fin N)) (okaStalkEquiv w
      ((okaCommPresheaf (ULift.{u} (Fin N))).germ ⊤ w trivial
        (algebraMap ℂ (OkaRing (⊤ : Opens (ULift.{u} (Fin N) → ℂ))) _))) = _
    rw [okaStalkEquiv_germ_algebraMap, AlgEquiv.commutes]
    rfl
  · simp only [RingHom.coe_comp, Function.comp_apply, polyFun, MvPolynomial.eval₂Hom_X',
      taylorGerm, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    change (LocalOkaRing.uliftEquiv (Fin N)) (okaStalkEquiv w
      ((okaCommPresheaf (ULift.{u} (Fin N))).germ ⊤ w trivial (coord ⟨i⟩))) = _
    rw [okaStalkEquiv_germ, coord_def, OkaRing.germ_ofMvPolynomial_X, map_add, AlgEquiv.commutes,
      LocalOkaRing.uliftEquiv_eq_renameEmb, LocalOkaRing.renameEmb_coord, add_comm]
    rfl

/-! ### Morphisms of affine schemes to affine space -/

namespace SchemeLFTℂ

variable (Z : SchemeLFTℂ.{u})

/-- The ring map `ℂ → Γ(Z, 𝒪_Z)` induced by the structure morphism. -/
def constMap : ULift.{u} ℂ →+* Γ(Z.obj.left, ⊤) :=
  ((Scheme.ΓSpecIso (.of (ULift.{u} ℂ))).inv ≫ Z.obj.hom.appTop).hom

lemma toSpecΓ_SpecMap_constMap :
    Z.obj.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom Z.constMap) = Z.obj.hom := by
  have h := Scheme.toSpecΓ_naturality Z.obj.hom
  rw [← SpecMap_ΓSpecIso_hom] at h
  rw [constMap, CommRingCat.ofHom_hom, Spec.map_comp, ← Category.assoc, ← h, Category.assoc,
    ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.comp_id]

variable {Z} (s : MvPolynomial (Fin N) (ULift.{u} ℂ) →+* Γ(Z.obj.left, ⊤))
  (hs : s.comp MvPolynomial.C = Z.constMap)

include hs in
lemma toSpecΓ_SpecMap_comp_SpecMap_C :
    Z.obj.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom s) ≫
      Spec.map (CommRingCat.ofHom (MvPolynomial.C (σ := Fin N) (R := ULift.{u} ℂ))) =
      Z.obj.hom := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hs, toSpecΓ_SpecMap_constMap]

/-- The morphism `Z ⟶ 𝔸^N` given by `N` global sections. -/
def toAffineSpace : Z ⟶ affineSpace.{u} N :=
  ObjectProperty.homMk (Over.homMk (Z.obj.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom s)) (by
    rw [affineSpace_obj_hom, Category.assoc]
    exact toSpecΓ_SpecMap_comp_SpecMap_C s hs))

lemma toAffineSpace_appTop (p : MvPolynomial (Fin N) (ULift.{u} ℂ)) :
    (toAffineSpace s hs).hom.left.appTop ((Scheme.ΓSpecIso (.of _)).inv p) = s p := by
  change (Z.obj.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom s)).appTop _ = _
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, Scheme.toSpecΓ_appTop]
  have h := congrArg (fun φ ↦ φ.hom ((Scheme.ΓSpecIso (.of _)).inv p))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom s))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
  exact h.trans (congrArg s ((Scheme.ΓSpecIso (.of _)).inv_hom_id_apply p))

lemma isClosedImmersion_toAffineSpace [IsAffine Z.obj.left] (hsurj : Function.Surjective s) :
    IsClosedImmersion (toAffineSpace s hs).hom.left := by
  haveI := IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom s) hsurj
  change IsClosedImmersion (Z.obj.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom s))
  infer_instance

/-- The morphism `Z^an ⟶ ℂ^N` induced by `N` global sections of `Z`. -/
abbrev anToAffine : analytification.obj Z ⟶ AnalyticSpace.complexAffineSpace.{u} N :=
  analytification.map (toAffineSpace s hs) ≫ (analytificationAffineSpaceIso.{u} N).hom

/-- Pulling polynomial functions back along `Z^an ⟶ ℂ^N`. -/
lemma pullbackΓ_anToAffine_polyFun (p : MvPolynomial (Fin N) (ULift.{u} ℂ)) :
    (anToAffine s hs).pullbackΓ (polyFun N p) = analytificationΓ Z (s p) := by
  change (LocallyRingedSpace.Γ.map ((analytification.map (toAffineSpace s hs)).toLRSHom ≫
    (analytificationAffineSpaceIso.{u} N).hom.toLRSHom).op).hom _ = _
  rw [LocallyRingedSpace.Γ_map_comp_apply, Γ_map_polyFun, ← toAffineSpace_appTop s hs p,
    analytificationΓ_naturality]

/-- Values of polynomials in the given sections are values of polynomials on `ℂ^N`. -/
lemma eval_analytificationΓ (z : analytification.obj Z) (p : MvPolynomial (Fin N) (ULift.{u} ℂ)) :
    (analytification.obj Z).eval (U := ⊤) z trivial (analytificationΓ Z (s p)) =
      affineEval N ((anToAffine s hs).toLRSHom.base z) p := by
  rw [← pullbackΓ_anToAffine_polyFun, ← eval_polyFun]
  exact eval_c_app _ (anToAffine s hs).isCLinear (U := ⊤) z trivial _

/-- Germs of polynomials in the given sections are images of Taylor expansions. -/
lemma stalkMap_anToAffine_taylorGerm (z : analytification.obj Z)
    (p : MvPolynomial (Fin N) (ULift.{u} ℂ)) :
    (anToAffine s hs).toLRSHom.stalkMap z
        ((stalkEquiv ((anToAffine s hs).toLRSHom.base z)).symm
          (taylorGerm ((anToAffine s hs).toLRSHom.base z) p)) =
      (analytification.obj Z).presheaf.Γgerm z (analytificationΓ Z (s p)) := by
  rw [← stalkEquiv_Γgerm_polyFun, RingEquiv.symm_apply_apply, ← pullbackΓ_anToAffine_polyFun]
  exact LocallyRingedSpace.stalkMap_germ_apply (anToAffine s hs).toLRSHom ⊤ z trivial _

/-- **Cut-out data for a closed embedding into affine space.** For surjective `s`, the morphism
`Z^an ⟶ ℂ^N` is injective, surjective on stalks with kernels generated by the germs of finitely
many polynomials `h i` generating `ker s`, and its image is the common zero locus of the `h i`. -/
theorem exists_cutOut [IsAffine Z.obj.left] (hsurj : Function.Surjective s) :
    ∃ (k : ℕ) (h : Fin k → MvPolynomial (Fin N) (ULift.{u} ℂ)), (∀ i, s (h i) = 0) ∧
      (∀ q, s q = 0 → q ∈ Ideal.span (Set.range h)) ∧
      (∀ z, Function.Surjective ((anToAffine s hs).toLRSHom.stalkMap z)) ∧
      (∀ z, RingHom.ker (((anToAffine s hs).toLRSHom.stalkMap z).hom.comp
          (stalkEquiv ((anToAffine s hs).toLRSHom.base z)).symm.toRingHom) =
        Ideal.span (Set.range fun i ↦ taylorGerm ((anToAffine s hs).toLRSHom.base z) (h i))) ∧
      (∀ w, (∀ i, affineEval N w (h i) = 0) → w ∈ Set.range (anToAffine s hs).toLRSHom.base) ∧
      Function.Injective (anToAffine s hs).toLRSHom.base := by
  haveI := isClosedImmersion_toAffineSpace s hs hsurj
  haveI : IsAffine (affineSpace.{u} N).obj.left := inferInstanceAs (IsAffine (Spec _))
  let j := toAffineSpace s hs
  let e := analytificationAffineSpaceIso.{u} N
  let γ := Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin N) (ULift.{u} ℂ)))
  obtain ⟨k, h', hh'⟩ := exists_generators j
  have hγ : ∀ i, h' i = γ.inv (γ.hom (h' i)) := fun i ↦ (γ.hom_inv_id_apply (h' i)).symm
  have hcut := isCutOutBy_analytification_map j h' hh'
  have hker0 : ∀ i, s (γ.hom (h' i)) = 0 := fun i ↦ by
    rw [← toAffineSpace_appTop s hs, ← hγ]
    have : h' i ∈ RingHom.ker j.hom.left.appTop.hom := hh' ▸ Ideal.subset_span ⟨i, rfl⟩
    exact this
  have hsec : ∀ i, analytificationSections h' i =
      analytificationΓ (affineSpace.{u} N) (γ.inv (γ.hom (h' i))) := fun i ↦ by
    rw [← hγ]
    rfl
  have hebij : ∀ x, Function.Bijective (e.hom.toLRSHom.stalkMap x) := fun x ↦
    ConcreteCategory.bijective_of_isIso
      ((forgetToLocallyRingedSpace.mapIso e).hom.stalkMap x)
  have hgerm : ∀ (x : analytification.obj (affineSpace.{u} N)) p,
      e.hom.toLRSHom.stalkMap x
        ((AnalyticSpace.complexAffineSpace.{u} N).presheaf.Γgerm (e.hom.toLRSHom.base x)
          (polyFun N p)) =
        (analytification.obj (affineSpace.{u} N)).presheaf.Γgerm x
          (analytificationΓ (affineSpace.{u} N) (γ.inv p)) := fun x p ↦ by
    rw [← Γ_map_polyFun]
    exact LocallyRingedSpace.stalkMap_germ_apply e.hom.toLRSHom ⊤ x trivial _
  refine ⟨k, fun i ↦ γ.hom (h' i), hker0, fun q hq ↦ ?_, fun z ↦ ?_, fun z ↦ ?_, fun w hw ↦ ?_, ?_⟩
  · have hq' : γ.inv q ∈ RingHom.ker j.hom.left.appTop.hom := by
      exact (toAffineSpace_appTop s hs q).trans hq
    rw [← hh'] at hq'
    have := Ideal.mem_map_of_mem γ.hom.hom hq'
    rw [γ.inv_hom_id_apply] at this
    refine (Ideal.map_le_iff_le_comap.2 (Ideal.span_le.2 ?_)) this
    rintro _ ⟨i, rfl⟩
    exact Ideal.subset_span ⟨i, rfl⟩
  · change Function.Surjective
      (((analytification.map j).toLRSHom ≫ e.hom.toLRSHom).stalkMap z)
    rw [LocallyRingedSpace.stalkMap_comp]
    exact (hcut.surjective_stalkMap z).comp (hebij _).2
  · have hk := hcut.ker_stalkMap z
    change RingHom.ker ((((analytification.map j).toLRSHom ≫ e.hom.toLRSHom).stalkMap z).hom.comp
      _) = _
    rw [LocallyRingedSpace.stalkMap_comp]
    erw [CommRingCat.hom_comp]
    rw [← RingHom.comap_ker,
      ← RingHom.comap_ker, hk]
    have hspan : Ideal.span (Set.range fun i ↦
        (analytification.obj (affineSpace.{u} N)).presheaf.Γgerm
          ((analytification.map j).toLRSHom.base z) (analytificationSections h' i)) =
        Ideal.map (e.hom.toLRSHom.stalkMap ((analytification.map j).toLRSHom.base z)).hom
          (Ideal.span (Set.range fun i ↦ (AnalyticSpace.complexAffineSpace.{u} N).presheaf.Γgerm
            ((anToAffine s hs).toLRSHom.base z) (polyFun N (γ.hom (h' i))))) := by
      rw [Ideal.map_span, ← Set.range_comp]
      refine congrArg Ideal.span (congrArg Set.range (funext fun i ↦ ?_))
      rw [Function.comp_apply, hsec]
      exact (hgerm _ _).symm
    rw [hspan]
    erw [Ideal.comap_map_of_bijective _ (hebij _)]
    rw [RingEquiv.toRingHom_eq_coe,
      Ideal.comap_coe, Ideal.comap_symm, Ideal.map_span, ← Set.range_comp]
    exact congrArg Ideal.span (congrArg Set.range (funext fun i ↦ stalkEquiv_Γgerm_polyFun _ _))
  · have hx : e.inv.toLRSHom.base w ∈ Set.range (analytification.map j).toLRSHom.base := by
      rw [hcut.range_base]
      intro i
      refine (eval_eq_zero_iff (U := ⊤) (hz := trivial)).1 ?_
      rw [hsec, eval_analytificationΓ_affineSpace,
        relProjectiveSpaceAn.analytificationAffineSpaceIso_hom_inv_base]
      exact hw i
    obtain ⟨y, hy⟩ := hx
    refine ⟨y, ?_⟩
    change e.hom.toLRSHom.base ((analytification.map j).toLRSHom.base y) = w
    rw [hy, relProjectiveSpaceAn.analytificationAffineSpaceIso_hom_inv_base]
  · exact (bijective_base_of_isIso e.hom).1.comp
      (isClosedEmbedding_analytification_map j).injective

end SchemeLFTℂ

open SchemeLFTℂ

lemma affineEval_X (w : ULift.{u} (Fin N) → ℂ) (i : Fin N) :
    affineEval N w (MvPolynomial.X i) = w ⟨i⟩ := by
  simp [affineEval]

/-! ### The splitting -/

section Splitting

variable {Y S : SchemeLFTℂ.{u}} (q : Y ⟶ S) {n m : ℕ}
  (sS : MvPolynomial (Fin n) (ULift.{u} ℂ) →+* Γ(S.obj.left, ⊤))
  (hsS : sS.comp MvPolynomial.C = S.constMap)
  (sY : MvPolynomial (Fin (n + m)) (ULift.{u} ℂ) →+* Γ(Y.obj.left, ⊤))
  (hsY : sY.comp MvPolynomial.C = Y.constMap)
  (hcomp : ∀ p, sY (MvPolynomial.rename (Fin.castAdd m) p) = q.hom.left.appTop (sS p))

include hcomp in
lemma eval_anToAffine_castAdd (y : analytification.obj Y) (p : MvPolynomial (Fin n) (ULift.{u} ℂ)) :
    affineEval (n + m) ((anToAffine sY hsY).toLRSHom.base y)
        (MvPolynomial.rename (Fin.castAdd m) p) =
      affineEval n
        ((anToAffine sS hsS).toLRSHom.base ((analytification.map q).toLRSHom.base y)) p := by
  rw [← eval_analytificationΓ, ← eval_analytificationΓ, hcomp, analytificationΓ_naturality]
  exact eval_c_app _ (analytification.map q).isCLinear (U := ⊤) y trivial _

include hcomp in
lemma anToAffine_castAdd (y : analytification.obj Y) (i : Fin n) :
    (anToAffine sY hsY).toLRSHom.base y ⟨Fin.castAdd m i⟩ =
      (anToAffine sS hsS).toLRSHom.base ((analytification.map q).toLRSHom.base y) ⟨i⟩ := by
  have h := eval_anToAffine_castAdd q sS hsS sY hsY hcomp y (MvPolynomial.X i)
  rwa [MvPolynomial.rename_X, affineEval_X, affineEval_X] at h

end Splitting

/-- A polynomial in `x₁, …, x_n, t₁, …, t_m`, read as a polynomial in `t` over the germs at `w₀`
of functions of `x`. -/
def hatMap (m : ℕ) {n : ℕ} (w₀ : ULift.{u} (Fin n) → ℂ) :
    MvPolynomial (Fin (n + m)) (ULift.{u} ℂ) →+* MvPolynomial (Fin m) (LocalOkaRing (Fin n)) :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp ((taylorGerm w₀).comp MvPolynomial.C))
    (Fin.addCases (fun i ↦ MvPolynomial.C (taylorGerm w₀ (MvPolynomial.X i))) MvPolynomial.X)

section HatMap

variable {n m : ℕ} (w₀ : ULift.{u} (Fin n) → ℂ)

lemma hatMap_comp_rename :
    (hatMap m w₀).comp (MvPolynomial.rename (Fin.castAdd m)).toRingHom =
      MvPolynomial.C.comp (taylorGerm w₀) := by
  refine MvPolynomial.ringHom_ext (fun c ↦ ?_) (fun i ↦ ?_)
  · simp [hatMap]
  · simp [hatMap, taylorGerm]

lemma hatMap_X_natAdd (j : Fin m) :
    hatMap m w₀ (MvPolynomial.X (Fin.natAdd n j)) = MvPolynomial.X j := by
  simp [hatMap]

/-- The point of `ℂ^{n+m}` with coordinates `w₀` and `c`. -/
def appendPt (w₀ : ULift.{u} (Fin n) → ℂ) (c : Fin m → ℂ) : ULift.{u} (Fin (n + m)) → ℂ :=
  fun v ↦ Fin.addCases (fun i ↦ w₀ ⟨i⟩) c v.down

lemma germMap_comp_hatMap (c : Fin m → ℂ) :
    (LocalOkaRing.germMap n m c).comp (hatMap m w₀) = taylorGerm (appendPt w₀ c) := by
  refine MvPolynomial.ringHom_ext (fun a ↦ ?_) (fun v ↦ ?_)
  · simp [hatMap, taylorGerm, AlgHom.commutes]
  · refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) v
    · simp [hatMap, taylorGerm, appendPt, LocalOkaRing.inclAdd, LocalOkaRing.renameEmb_coord,
        AlgHom.commutes]
    · simp [hatMap, taylorGerm, appendPt]

lemma polyVar_map_taylorGerm (P : Fin m → (MvPolynomial (Fin n) (ULift.{u} ℂ))[X]) (j : Fin m) :
    LocalOkaRing.polyVar (fun j ↦ (P j).map (taylorGerm w₀)) j =
      hatMap m w₀ ((P j).eval₂ (MvPolynomial.rename (Fin.castAdd m)).toRingHom
        (MvPolynomial.X (Fin.natAdd n j))) := by
  rw [LocalOkaRing.polyVar, Polynomial.hom_eval₂, hatMap_comp_rename, hatMap_X_natAdd,
    Polynomial.eval₂_map]

lemma inclAdd_taylorGerm (w : ULift.{u} (Fin (n + m)) → ℂ)
    (hw : ∀ i, w ⟨Fin.castAdd m i⟩ = w₀ ⟨i⟩) (p : MvPolynomial (Fin n) (ULift.{u} ℂ)) :
    LocalOkaRing.inclAdd n m (taylorGerm w₀ p) =
      taylorGerm w (MvPolynomial.rename (Fin.castAdd m) p) := by
  refine congrArg (fun φ : _ →+* _ ↦ φ p) (MvPolynomial.ringHom_ext (fun c ↦ ?_) (fun i ↦ ?_) :
    (LocalOkaRing.inclAdd n m).toRingHom.comp (taylorGerm w₀) =
      (taylorGerm w).comp (MvPolynomial.rename (Fin.castAdd m)).toRingHom)
  · simp [taylorGerm, AlgHom.commutes]
  · simp [taylorGerm, LocalOkaRing.inclAdd, LocalOkaRing.renameEmb_coord, AlgHom.commutes, hw]

lemma polyFun_C (c : ℂ) :
    polyFun.{u} n (MvPolynomial.C ⟨c⟩) =
      algebraMap ℂ (OkaRing (⊤ : Opens (ULift.{u} (Fin n) → ℂ))) c := by
  rw [polyFun, MvPolynomial.eval₂Hom_C]
  rfl

lemma polyFun_X (i : ULift.{u} (Fin n)) :
    polyFun.{u} n (MvPolynomial.X i.down) = OkaRing.ofMvPolynomial ⊤ (MvPolynomial.X i) := by
  rw [polyFun, MvPolynomial.eval₂Hom_X']
  rfl

end HatMap

section Splitting

variable {Y S : SchemeLFTℂ.{u}} (q : Y ⟶ S) {n m : ℕ}
  (sS : MvPolynomial (Fin n) (ULift.{u} ℂ) →+* Γ(S.obj.left, ⊤))
  (hsS : sS.comp MvPolynomial.C = S.constMap)
  (sY : MvPolynomial (Fin (n + m)) (ULift.{u} ℂ) →+* Γ(Y.obj.left, ⊤))
  (hsY : sY.comp MvPolynomial.C = Y.constMap)
  (hcomp : ∀ p, sY (MvPolynomial.rename (Fin.castAdd m) p) = q.hom.left.appTop (sS p))

include hcomp in
/-- On germs of functions of `x`, the fibre stalk maps of `q^an` are the renamings
`ℂ{x} → ℂ{x, t}` followed by the stalk maps of `Y^an ⟶ ℂ^{n+m}`. -/
lemma fibreStalkMap_stalkMap_anToAffine (s : analytification.obj S)
    (y : (analytification.map q).toLRSHom.base ⁻¹' {s}) (r : LocalOkaRing (Fin n)) :
    fibreStalkMap (analytification.map q) s y (((anToAffine sS hsS).toLRSHom.stalkMap s).hom
        ((stalkEquiv ((anToAffine sS hsS).toLRSHom.base s)).symm r)) =
      ((anToAffine sY hsY).toLRSHom.stalkMap y.1).hom
        ((stalkEquiv ((anToAffine sY hsY).toLRSHom.base y.1)).symm
          (LocalOkaRing.inclAdd n m r)) := by
  set w₀ := (anToAffine sS hsS).toLRSHom.base s
  set w := (anToAffine sY hsY).toLRSHom.base y.1
  have hw : ∀ i, w ⟨Fin.castAdd m i⟩ = w₀ ⟨i⟩ := fun i ↦ by
    have := anToAffine_castAdd q sS hsS sY hsY hcomp y.1 i
    rwa [show (analytification.map q).toLRSHom.base y.1 = s from y.2] at this
  obtain ⟨u, rfl⟩ := (stalkEquiv w₀).surjective r
  let θ₁ := (fibreStalkMap (analytification.map q) s y).comp
    ((anToAffine sS hsS).toLRSHom.stalkMap s).hom
  let θ₂ := (((anToAffine sY hsY).toLRSHom.stalkMap y.1).hom.comp
      (stalkEquiv w).symm.toRingHom).comp
    ((LocalOkaRing.inclAdd n m).toRingHom.comp (stalkEquiv w₀).toRingHom)
  haveI : IsLocalHom θ₁ := ⟨fun a ha ↦ by
    rw [← evalStalk_ne_zero_iff_isUnit] at ha ⊢
    simp only [θ₁, RingHom.comp_apply] at ha
    rwa [evalStalk_fibreStalkMap, evalStalk_stalkMap_hom] at ha⟩
  have hΓ1 : ∀ p, θ₁ ((AnalyticSpace.complexAffineSpace.{u} n).presheaf.Γgerm w₀
      (polyFun n p)) = (analytification.obj Y).presheaf.Γgerm y.1
        (analytificationΓ Y (sY (MvPolynomial.rename (Fin.castAdd m) p))) := fun p ↦ by
    simp only [θ₁, RingHom.comp_apply]
    rw [((stalkEquiv w₀).symm_apply_eq.2 (stalkEquiv_Γgerm_polyFun w₀ p).symm).symm,
      stalkMap_anToAffine_taylorGerm, fibreStalkMap_Γgerm, hcomp, analytificationΓ_naturality]
  have hΓ2 : ∀ p, θ₂ ((AnalyticSpace.complexAffineSpace.{u} n).presheaf.Γgerm w₀
      (polyFun n p)) = (analytification.obj Y).presheaf.Γgerm y.1
        (analytificationΓ Y (sY (MvPolynomial.rename (Fin.castAdd m) p))) := fun p ↦ by
    simp only [θ₂, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe]
    rw [stalkEquiv_Γgerm_polyFun, inclAdd_taylorGerm w₀ w hw]
    exact stalkMap_anToAffine_taylorGerm sY hsY y.1 _
  have key : θ₁ = θ₂ := @okaStalk_ringHom_ext (ULift.{u} (Fin n)) _ w₀ _ _ _ _ θ₁ θ₂ ‹_›
    (fun c ↦ by
      have h1 := hΓ1 (MvPolynomial.C ⟨c⟩)
      have h2 := hΓ2 (MvPolynomial.C ⟨c⟩)
      rw [polyFun_C] at h1 h2
      exact h1.trans h2.symm)
    (fun i ↦ by
      have h1 := hΓ1 (MvPolynomial.X i.down)
      have h2 := hΓ2 (MvPolynomial.X i.down)
      rw [polyFun_X] at h1 h2
      exact h1.trans h2.symm)
  have := RingHom.congr_fun key u
  simp only [θ₁, θ₂, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe] at this
  exact (congrArg _ (congrArg _ ((stalkEquiv w₀).symm_apply_apply u))).trans this

variable (P : Fin m → (MvPolynomial (Fin n) (ULift.{u} ℂ))[X]) (hPm : ∀ j, (P j).Monic)
  (hP0 : ∀ j, sY ((P j).eval₂ (MvPolynomial.rename (Fin.castAdd m)).toRingHom
    (MvPolynomial.X (Fin.natAdd n j))) = 0)

include hsS hsY hcomp hPm hP0 in
theorem bijective_stalkTensorMap_of_presentation [IsAffine Y.obj.left] [IsAffine S.obj.left]
    (hsSsurj : Function.Surjective sS) (hsYsurj : Function.Surjective sY)
    (s : analytification.obj S) :
    letI := q.hom.left.appTop.hom.toAlgebra
    Function.Bijective (stalkTensorMap (analytification.map q) (analytificationΓ Y)
      (analytificationΓ_naturality q) s) := by
  letI := q.hom.left.appTop.hom.toAlgebra
  classical
  set w₀ := (anToAffine sS hsS).toLRSHom.base s with hw₀
  obtain ⟨k, h, hh0, hhspan, hsurjY, hkerY, hrangeY, hinjY⟩ := exists_cutOut sY hsY hsYsurj
  obtain ⟨-, -, -, -, hsurjS, -, -, hinjS⟩ := exists_cutOut sS hsS hsSsurj
  set Pt : Fin m → (LocalOkaRing (Fin n))[X] := fun j ↦ (P j).map (taylorGerm w₀) with hPt
  have hPtm : ∀ j, (Pt j).Monic := fun j ↦ (hPm j).map _
  set H : Fin k → MvPolynomial (Fin m) (LocalOkaRing (Fin n)) := fun i ↦ hatMap m w₀ (h i)
    with hH
  have hKH : Ideal.span (Set.range (LocalOkaRing.polyVar Pt)) ≤ Ideal.span (Set.range H) := by
    rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    rw [hPt, polyVar_map_taylorGerm]
    have := Ideal.mem_map_of_mem (hatMap m w₀) (hhspan _ (hP0 j))
    rwa [Ideal.map_span, ← Set.range_comp] at this
  have hcore := (LocalOkaRing.isPiQuotient_germMap m Pt hPtm).sup (Ideal.span (Set.range H))
  rw [sup_eq_right.2 hKH] at hcore
  -- the fibre, and the coordinates of its points
  let F := (analytification.map q).toLRSHom.base ⁻¹' {s}
  let wy : F → ULift.{u} (Fin (n + m)) → ℂ := fun y ↦ (anToAffine sY hsY).toLRSHom.base y.1
  have hqy : ∀ y : F, (analytification.map q).toLRSHom.base y.1 = s := fun y ↦ y.2
  have hwy : ∀ (y : F) (i : Fin n), wy y ⟨Fin.castAdd m i⟩ = w₀ ⟨i⟩ := fun y i ↦ by
    change (anToAffine sY hsY).toLRSHom.base y.1 ⟨Fin.castAdd m i⟩ = _
    rw [anToAffine_castAdd q sS hsS sY hsY hcomp, hqy y]
  have hwyp : ∀ (y : F) p, affineEval (n + m) (wy y) (MvPolynomial.rename (Fin.castAdd m) p) =
      affineEval n w₀ p := fun y p ↦ by
    change affineEval (n + m) ((anToAffine sY hsY).toLRSHom.base y.1) _ = _
    rw [eval_anToAffine_castAdd q sS hsS sY hsY hcomp, hqy y]
  have hroot : ∀ (y : F) j,
      ((Pt j).map LocalOkaRing.constantCoeff).IsRoot (wy y ⟨Fin.natAdd n j⟩) := fun y j ↦ by
    have h1 : (Pt j).map LocalOkaRing.constantCoeff = (P j).map (affineEval n w₀) := by
      rw [hPt, Polynomial.map_map]
      exact congrArg (fun φ ↦ (P j).map φ) (RingHom.ext fun p ↦ constantCoeff_taylorGerm w₀ p)
    have h2 : affineEval (n + m) (wy y) ((P j).eval₂ (MvPolynomial.rename (Fin.castAdd m)).toRingHom
        (MvPolynomial.X (Fin.natAdd n j))) = 0 := by
      change affineEval (n + m) ((anToAffine sY hsY).toLRSHom.base y.1) _ = 0
      rw [← eval_analytificationΓ sY hsY, hP0 j, map_zero, map_zero]
    rw [Polynomial.hom_eval₂, affineEval_X] at h2
    rw [Polynomial.IsRoot, h1, Polynomial.eval_map, ← h2]
    exact congrArg (fun φ ↦ (P j).eval₂ φ _) (RingHom.ext fun p ↦ (hwyp y p).symm)
  let ι : F → ∀ j, LocalOkaRing.rootsFinset (Pt j) := fun y j ↦
    ⟨wy y ⟨Fin.natAdd n j⟩, (LocalOkaRing.mem_rootsFinset (hPtm j)).2 (hroot y j)⟩
  have happ : ∀ y : F, appendPt w₀ (fun j ↦ (ι y j : ℂ)) = wy y := fun y ↦ by
    funext ⟨v⟩
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) v
    · simp only [appendPt, Fin.addCases_left]
      exact (hwy y i).symm
    · simp only [appendPt, Fin.addCases_right]
      rfl
  have hinj : Function.Injective ι := fun y y' hyy ↦ by
    have : wy y = wy y' := by rw [← happ, ← happ, hyy]
    exact Subtype.ext (hinjY this)
  have htop : ∀ c ∉ Set.range ι,
      Ideal.span (Set.range fun j ↦
          LocalOkaRing.germMap n m (fun j ↦ (c j : ℂ)) (LocalOkaRing.polyVar Pt j)) ⊔
        Ideal.map (LocalOkaRing.germMap n m fun j ↦ (c j : ℂ)) (Ideal.span (Set.range H)) = ⊤ := by
    intro c hc
    have hex : ∃ i, affineEval (n + m) (appendPt w₀ fun j ↦ (c j : ℂ)) (h i) ≠ 0 := by
      by_contra hall
      push Not at hall
      obtain ⟨y, hy⟩ := hrangeY _ hall
      have hqy' : (analytification.map q).toLRSHom.base y = s := by
        apply hinjS
        funext ⟨i⟩
        rw [← anToAffine_castAdd q sS hsS sY hsY hcomp, hy]
        simp only [appendPt, Fin.addCases_left]
        rfl
      refine hc ⟨⟨y, hqy'⟩, funext fun j ↦ Subtype.ext ?_⟩
      change (anToAffine sY hsY).toLRSHom.base y ⟨Fin.natAdd n j⟩ = _
      rw [hy]
      simp only [appendPt, Fin.addCases_right]
    obtain ⟨i, hi⟩ := hex
    refine Ideal.eq_top_of_isUnit_mem _
      (Ideal.mem_sup_right (Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨i, rfl⟩))) ?_
    rw [hH]
    change IsUnit (((LocalOkaRing.germMap n m fun j ↦ (c j : ℂ)).comp (hatMap m w₀)) (h i))
    rw [germMap_comp_hatMap, LocalOkaRing.isUnit_iff, constantCoeff_taylorGerm]
    exact hi
  have hres := hcore.restrict ι hinj htop
  -- the stalks of `Y^an` along the fibre
  let σ : ∀ y : F, LocalOkaRing (Fin (n + m)) →+* (analytification.obj Y).presheaf.stalk y.1 :=
    fun y ↦ ((anToAffine sY hsY).toLRSHom.stalkMap y.1).hom.comp (stalkEquiv (wy y)).symm.toRingHom
  have hσtay : ∀ (y : F) p, σ y (taylorGerm (wy y) p) =
      (analytification.obj Y).presheaf.Γgerm y.1 (analytificationΓ Y (sY p)) := fun y p ↦
    stalkMap_anToAffine_taylorGerm sY hsY y.1 p
  have hgt : ∀ (y : F), (LocalOkaRing.germMap n m fun j ↦ (ι y j : ℂ)).comp (hatMap m w₀) =
      taylorGerm (wy y) := fun y ↦ by rw [germMap_comp_hatMap, happ]
  have hσk : ∀ y : F, RingHom.ker (σ y) =
      Ideal.span (Set.range fun j ↦
          LocalOkaRing.germMap n m (fun j ↦ (ι y j : ℂ)) (LocalOkaRing.polyVar Pt j)) ⊔
        Ideal.map (LocalOkaRing.germMap n m fun j ↦ (ι y j : ℂ)) (Ideal.span (Set.range H)) := by
    intro y
    change RingHom.ker (((anToAffine sY hsY).toLRSHom.stalkMap y.1).hom.comp
      (stalkEquiv ((anToAffine sY hsY).toLRSHom.base y.1)).symm.toRingHom) = _
    rw [hkerY y.1]
    have hmapH : Ideal.map (LocalOkaRing.germMap n m fun j ↦ (ι y j : ℂ))
        (Ideal.span (Set.range H)) =
        Ideal.span (Set.range fun i ↦ taylorGerm (wy y) (h i)) := by
      rw [Ideal.map_span, ← Set.range_comp]
      refine congrArg Ideal.span (congrArg Set.range (funext fun i ↦ ?_))
      rw [Function.comp_apply, hH, ← RingHom.comp_apply, hgt]
    rw [← hmapH]
    refine (sup_eq_right.2 ?_).symm
    rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    exact Ideal.mem_map_of_mem _ (hKH (Ideal.subset_span ⟨j, rfl⟩))
  obtain ⟨hcs, hck⟩ := hres.surjective_and_ker_eq σ
    (fun y ↦ (hsurjY y.1).comp (stalkEquiv _).symm.surjective) hσk
  -- the map `ℂ{x}[t] → 𝒪_{S^an,s} ⊗[Γ(S)] Γ(Y)`
  let ρ : LocalOkaRing (Fin n) →+* (analytification.obj S).presheaf.stalk s :=
    ((anToAffine sS hsS).toLRSHom.stalkMap s).hom.comp (stalkEquiv w₀).symm.toRingHom
  have hρ : ∀ p, ρ (taylorGerm w₀ p) =
      (analytification.obj S).presheaf.Γgerm s (analytificationΓ S (sS p)) := fun p ↦
    stalkMap_anToAffine_taylorGerm sS hsS s p
  have hρs : Function.Surjective ρ := (hsurjS s).comp (stalkEquiv _).symm.surjective
  let θ : MvPolynomial (Fin m) (LocalOkaRing (Fin n)) →+*
      (analytification.obj S).presheaf.stalk s ⊗[Γ(S.obj.left, ⊤)] Γ(Y.obj.left, ⊤) :=
    MvPolynomial.eval₂Hom (Algebra.TensorProduct.includeLeftRingHom.comp ρ)
      fun j ↦ 1 ⊗ₜ sY (MvPolynomial.X (Fin.natAdd n j))
  have hθC' : ∀ r, θ (MvPolynomial.C r) = ρ r ⊗ₜ 1 := fun r ↦ MvPolynomial.eval₂Hom_C _ _ r
  have hθC : ∀ p, θ (MvPolynomial.C (taylorGerm w₀ p)) = 1 ⊗ₜ q.hom.left.appTop (sS p) :=
    fun p ↦ by
      rw [hθC', hρ, ← analytificationStalkAlgebra_algebraMap_apply]
      exact Algebra.TensorProduct.tmul_one_eq_one_tmul _
  have hθhat : ∀ p, θ (hatMap m w₀ p) = 1 ⊗ₜ sY p := fun p ↦ by
    refine congrArg (fun φ : _ →+* _ ↦ φ p) (MvPolynomial.ringHom_ext (fun c ↦ ?_) (fun v ↦ ?_) :
      θ.comp (hatMap m w₀) = Algebra.TensorProduct.includeRight.toRingHom.comp sY)
    · simp only [RingHom.comp_apply, hatMap, MvPolynomial.eval₂Hom_C]
      rw [hθC, ← hcomp, MvPolynomial.rename_C]
      rfl
    · refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) v
      · simp only [RingHom.comp_apply, hatMap, MvPolynomial.eval₂Hom_X', Fin.addCases_left]
        rw [hθC, ← hcomp, MvPolynomial.rename_X]
        rfl
      · simp only [RingHom.comp_apply, hatMap, MvPolynomial.eval₂Hom_X', Fin.addCases_right]
        exact MvPolynomial.eval₂Hom_X' _ _ j
  have hθs : Function.Surjective θ := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero θ⟩
    | tmul a b =>
      obtain ⟨r, rfl⟩ := hρs a
      obtain ⟨p, rfl⟩ := hsYsurj b
      refine ⟨MvPolynomial.C r * hatMap m w₀ p, ?_⟩
      rw [map_mul, hθhat, hθC', Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    | add x x' hx hx' =>
      obtain ⟨f, rfl⟩ := hx
      obtain ⟨f', rfl⟩ := hx'
      exact ⟨f + f', map_add θ f f'⟩
  have hθH : ∀ i, θ (H i) = 0 := fun i ↦ by
    rw [hH]
    dsimp only
    rw [hθhat, hh0, TensorProduct.tmul_zero]
  let Φ := stalkTensorMap (analytification.map q) (analytificationΓ Y)
    (analytificationΓ_naturality q) s
  have hΦθ : Φ.comp θ = RingHom.pi fun y ↦
      (σ y).comp (LocalOkaRing.germMap n m fun j ↦ (ι y j : ℂ)) := by
    refine MvPolynomial.ringHom_ext (fun r ↦ funext fun y ↦ ?_) (fun j ↦ funext fun y ↦ ?_)
    · change Φ (θ (MvPolynomial.C r)) y =
        σ y (LocalOkaRing.germMap n m (fun j ↦ (ι y j : ℂ)) (MvPolynomial.C r))
      rw [hθC', LocalOkaRing.germMap_C]
      change stalkTensorMap _ _ _ s (ρ r ⊗ₜ 1) y = _
      rw [stalkTensorMap_tmul, map_one, map_one, mul_one]
      exact fibreStalkMap_stalkMap_anToAffine q sS hsS sY hsY hcomp s y r
    · change Φ (θ (MvPolynomial.X j)) y =
        σ y (LocalOkaRing.germMap n m (fun j ↦ (ι y j : ℂ)) (MvPolynomial.X j))
      have e2 : LocalOkaRing.germMap n m (fun j ↦ (ι y j : ℂ)) (MvPolynomial.X j) =
          taylorGerm (wy y) (MvPolynomial.X (Fin.natAdd n j)) := by
        rw [← hatMap_X_natAdd w₀ j, ← RingHom.comp_apply, hgt]
      rw [e2, hσtay]
      change stalkTensorMap _ _ _ s (θ (MvPolynomial.X j)) y = _
      rw [show θ (MvPolynomial.X j) = 1 ⊗ₜ sY (MvPolynomial.X (Fin.natAdd n j)) from
        MvPolynomial.eval₂Hom_X' _ _ j, stalkTensorMap_tmul, map_one, one_mul]
  refine ⟨(injective_iff_map_eq_zero Φ).2 fun x hx ↦ ?_, fun z ↦ ?_⟩
  · obtain ⟨f, rfl⟩ := hθs x
    have hf : f ∈ RingHom.ker (RingHom.pi fun y ↦
        (σ y).comp (LocalOkaRing.germMap n m fun j ↦ (ι y j : ℂ))) := by
      rw [RingHom.mem_ker, ← hΦθ, RingHom.comp_apply]
      exact hx
    rw [hck] at hf
    exact (Ideal.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hθH i) :
      Ideal.span (Set.range H) ≤ RingHom.ker θ) hf
  · obtain ⟨f, hf⟩ := hcs z
    exact ⟨θ f, by rw [← RingHom.comp_apply, hΦθ, hf]⟩

end Splitting

namespace SchemeLFTℂ

/-- The ring of global sections of an affine scheme of finite type over `ℂ` is a quotient of a
polynomial ring, compatibly with the structure maps from `ℂ`. -/
lemma exists_surjective (Z : SchemeLFTℂ.{u}) [IsAffine Z.obj.left] :
    ∃ (n : ℕ) (s : MvPolynomial (Fin n) (ULift.{u} ℂ) →+* Γ(Z.obj.left, ⊤)),
      Function.Surjective s ∧ s.comp MvPolynomial.C = Z.constMap := by
  haveI : LocallyOfFiniteType Z.obj.hom := Z.property
  have h : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom Z.constMap)) := by
    rw [← MorphismProperty.cancel_left_of_respectsIso @LocallyOfFiniteType Z.obj.left.toSpecΓ,
      toSpecΓ_SpecMap_constMap]
    infer_instance
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at h
  letI := Z.constMap.toAlgebra
  haveI : Algebra.FiniteType (ULift.{u} ℂ) Γ(Z.obj.left, ⊤) := h
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 this
  exact ⟨n, f.toRingHom, hf, f.comp_algebraMap⟩

lemma appTop_constMap {Y S : SchemeLFTℂ.{u}} (q : Y ⟶ S) (c : ULift.{u} ℂ) :
    q.hom.left.appTop (S.constMap c) = Y.constMap c := by
  simp only [constMap, CommRingCat.hom_comp, RingHom.comp_apply]
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, Over.w q.hom]

end SchemeLFTℂ

/-- **Analytic splitting of finite morphisms of affine schemes**: for a finite morphism
`q : Y ⟶ S` of affine schemes of finite type over `ℂ` and `s ∈ S^an`,
`𝒪_{S^an,s} ⊗[Γ(S, 𝒪_S)] Γ(Y, 𝒪_Y) → ∏_{y ∈ (q^an)⁻¹ s} 𝒪_{Y^an,y}` is bijective. -/
theorem finiteAnalyticSplitting : FiniteAnalyticSplitting.{u} := by
  intro Y S _ _ q _ s
  obtain ⟨n, sS, hsSsurj, hsS⟩ := S.exists_surjective
  letI := q.hom.left.appTop.hom.toAlgebra
  haveI : Module.Finite Γ(S.obj.left, ⊤) Γ(Y.obj.left, ⊤) := q.hom.left.finite_appTop
  obtain ⟨m, b, hb⟩ := Module.Finite.exists_fin (R := Γ(S.obj.left, ⊤)) (M := Γ(Y.obj.left, ⊤))
  let sY : MvPolynomial (Fin (n + m)) (ULift.{u} ℂ) →+* Γ(Y.obj.left, ⊤) :=
    MvPolynomial.eval₂Hom ((algebraMap Γ(S.obj.left, ⊤) Γ(Y.obj.left, ⊤)).comp
      (sS.comp MvPolynomial.C))
      (Fin.addCases
        (fun i ↦ algebraMap Γ(S.obj.left, ⊤) Γ(Y.obj.left, ⊤) (sS (MvPolynomial.X i))) b)
  have hcomp' : sY.comp (MvPolynomial.rename (Fin.castAdd m)).toRingHom =
      (algebraMap Γ(S.obj.left, ⊤) Γ(Y.obj.left, ⊤)).comp sS := by
    refine MvPolynomial.ringHom_ext (fun c ↦ ?_) (fun i ↦ ?_)
    · simp [sY]
    · simp [sY]
  have hcomp : ∀ p, sY (MvPolynomial.rename (Fin.castAdd m) p) = q.hom.left.appTop (sS p) :=
    fun p ↦ RingHom.congr_fun hcomp' p
  have hsY : sY.comp MvPolynomial.C = Y.constMap := by
    ext c
    rw [RingHom.comp_apply, ← MvPolynomial.rename_C (Fin.castAdd m), hcomp,
      show sS (MvPolynomial.C c) = S.constMap c from RingHom.congr_fun hsS c,
      SchemeLFTℂ.appTop_constMap]
  have hsYsurj : Function.Surjective sY := by
    intro x
    have hx : x ∈ Submodule.span Γ(S.obj.left, ⊤) (Set.range b) := hb ▸ Submodule.mem_top
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hx
    choose p hp using fun j ↦ hsSsurj (a j)
    refine ⟨∑ j, MvPolynomial.rename (Fin.castAdd m) (p j) * MvPolynomial.X (Fin.natAdd n j), ?_⟩
    simp only [map_sum, map_mul, hcomp, hp, Algebra.smul_def]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp [sY]
    rfl
  have hint : ∀ j, ∃ P : (MvPolynomial (Fin n) (ULift.{u} ℂ))[X], P.Monic ∧
      P.eval₂ ((algebraMap Γ(S.obj.left, ⊤) Γ(Y.obj.left, ⊤)).comp sS) (b j) = 0 := fun j ↦ by
    obtain ⟨Q, hQm, hQ⟩ := Algebra.IsIntegral.isIntegral (R := Γ(S.obj.left, ⊤)) (b j)
    obtain ⟨P, hPQ, -, hPm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
      (Polynomial.mem_lifts_of_surjective hsSsurj Q) hQm
    refine ⟨P, hPm, ?_⟩
    rw [← Polynomial.eval₂_map, hPQ]
    exact hQ
  choose P hPm hP using hint
  have hP0 : ∀ j, sY ((P j).eval₂ (MvPolynomial.rename (Fin.castAdd m)).toRingHom
      (MvPolynomial.X (Fin.natAdd n j))) = 0 := fun j ↦ by
    rw [Polynomial.hom_eval₂, hcomp']
    simpa [sY] using hP j
  exact bijective_stalkTensorMap_of_presentation q sS hsS sY hsY hcomp P hPm hP0 hsSsurj hsYsurj s

end

end ComplexAnalytic
