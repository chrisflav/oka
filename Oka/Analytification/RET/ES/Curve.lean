/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.ES.CurveCompare

/-!
# Finite étale covers of affine curves are algebraic

Let `V` be an affine integral scheme of finite type over `ℂ` of dimension one and `p : W ⟶ V^an`
a finite étale cover with Hausdorff source. Then `W` is the analytification of a finite étale
cover of `V`
(`ComplexAnalytic.mem_essImage_analytificationFiniteEtaleOver_of_ringKrullDim_eq_one`).

## Proof

Choose a finite `q : V ⟶ 𝔸¹`, given by a function `z`, which is étale over `{‖z‖ > 1}`
(`ComplexAnalytic.exists_curveCoordinate`), and let `ρ₀ = q^an ∘ p : W ⟶ ℂ¹`. The ring `P` of
functions on `W` of polynomial growth in `z` is a finite `Γ(V, 𝒪_V)`-algebra containing the
functions pulled back from `V` (`ComplexAnalytic.module_finite_polyGrowthMap`,
`ComplexAnalytic.ProjectiveLine.hasPolyGrowth_pullbackΓ`), and for every `v ∈ V^an` the map
`𝒪_{V^an,v} ⊗[Γ(V, 𝒪_V)] P → ∏_{w ∈ p⁻¹ v} 𝒪_{W,w}` is bijective
(`ComplexAnalytic.bijective_stalkTensorMap_polyGrowthMap`): this holds over `ℙ¹_an` by GAGA
(`ComplexAnalytic.ProjectiveLine.bijective_polyGrowthStalkMap`), is moved to `𝔸¹^an` along the
chart `0` (`ComplexAnalytic.TensorTower.bijective_transferLift`) and is split along
`V^an ⟶ 𝔸¹^an` (`ComplexAnalytic.finiteAnalyticSplitting`,
`ComplexAnalytic.TensorTower.bijective_liftAt`). Then `W ≅ (Spec P)^an` by
`ComplexAnalytic.exists_iso_of_bijective_stalkTensorMap`.

Normality of `V` is not needed. The Hausdorff hypothesis is: the analytification of a finite
étale cover of `V` has Hausdorff source, while `ComplexAnalytic.AnalyticSpace.doubledLineOver`
is a finite étale cover of `ℂ¹` whose source is not Hausdorff.
-/

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry Topology TensorProduct

universe u

namespace ComplexAnalytic

open AnalyticSpace ProjectiveLine TensorTower

noncomputable section

section Assembly

variable {V : SchemeLFTℂ.{u}} [IsAffine V.obj.left]
  {s : MvPolynomial (Fin 1) (ULift.{u} ℂ) →+* Γ(V.obj.left, ⊤)}
  (hs : s.comp MvPolynomial.C = V.constMap) (hsfin : s.Finite) {W : AnalyticSpace.{u}}
  (p : W ⟶ analytification.obj V)

/-- The functions on `V`, pulled back to `W`, as functions of polynomial growth. -/
def polyGrowthMap : Γ(V.obj.left, ⊤) →+* polyGrowth (p ≫ SchemeLFTℂ.anToAffine s hs) :=
  ((LocallyRingedSpace.Γ.map p.toLRSHom.op).hom.comp (analytificationΓ V)).codRestrict _
    (hasPolyGrowth_pullbackΓ hs p hsfin)

variable [IsFinite (SchemeLFTℂ.toAffineSpace s hs).hom.left]
  (hfin : AnalyticSpace.IsFinite (p ≫ SchemeLFTℂ.anToAffine s hs)) [T2Space W]
  (hloc : IsLocalIso (AnalyticSpace.restrictHom (p ≫ SchemeLFTℂ.anToAffine s hs) outerOpens))
  (hK : (LocallyRingedSpace.Hom.pushUnit (p ≫ SchemeLFTℂ.anToAffine s hs).toLRSHom).IsCoherent)

omit [IsAffine V.obj.left] [IsFinite (SchemeLFTℂ.toAffineSpace s hs).hom.left] in
include hfin hloc hK in
/-- **The functions of polynomial growth form a finite algebra over `Γ(V, 𝒪_V)`.** -/
theorem module_finite_polyGrowthMap :
    letI := (polyGrowthMap hs hsfin p).toAlgebra
    Module.Finite Γ(V.obj.left, ⊤) (polyGrowth (p ≫ SchemeLFTℂ.anToAffine s hs)) := by
  haveI := hfin
  haveI := hloc
  letI := polyGrowthAlgebra (p ≫ SchemeLFTℂ.anToAffine s hs) hK
  letI := (polyGrowthMap hs hsfin p).toAlgebra
  letI : Algebra ringU₀.{u} Γ(V.obj.left, ⊤) :=
    ((SchemeLFTℂ.toAffineSpace s hs).hom.left.appTop.hom.comp chartΓ).toAlgebra
  haveI : IsScalarTower ringU₀.{u} Γ(V.obj.left, ⊤)
      (polyGrowth (p ≫ SchemeLFTℂ.anToAffine s hs)) :=
    IsScalarTower.of_algebraMap_eq fun r ↦ Subtype.ext (toSections_eq hs p r)
  haveI := module_finite_polyGrowth (p ≫ SchemeLFTℂ.anToAffine s hs) hK
  exact Module.Finite.of_restrictScalars_finite ringU₀.{u} _ _

include hfin hloc hK in
/-- **The stalks of `W` are the base changes of the functions of polynomial growth**: for every
`v ∈ V^an` the map `𝒪_{V^an,v} ⊗[Γ(V, 𝒪_V)] P → ∏_{w ∈ p⁻¹ v} 𝒪_{W,w}` is bijective. The
splitting over `ℙ¹_an` (`ComplexAnalytic.ProjectiveLine.bijective_polyGrowthStalkMap`) is moved to
`𝔸¹^an` along the chart and then split along `V^an ⟶ 𝔸¹^an`
(`ComplexAnalytic.finiteAnalyticSplitting`, `ComplexAnalytic.TensorTower.bijective_liftAt`). -/
theorem bijective_stalkTensorMap_polyGrowthMap (v : analytification.obj V) :
    letI := (polyGrowthMap hs hsfin p).toAlgebra
    Function.Bijective (stalkTensorMap p (polyGrowth (p ≫ SchemeLFTℂ.anToAffine s hs)).subtype
      (fun _ ↦ rfl) v) := by
  haveI : IsAffine (affineSpace.{u} 1).obj.left := inferInstanceAs (IsAffine (Spec _))
  haveI := hfin
  haveI := hloc
  set ρ₀ := p ≫ SchemeLFTℂ.anToAffine s hs with hρ₀
  letI alg₀ := polyGrowthAlgebra ρ₀ hK
  set φA := polyGrowthMap hs hsfin p
  letI : Algebra Γ(V.obj.left, ⊤) (polyGrowth ρ₀) := φA.toAlgebra
  -- the tower `Γ(𝔸¹, 𝒪) → Γ(V, 𝒪_V) → P` over the point `c = q^an v`
  set q := SchemeLFTℂ.toAffineSpace s hs with hq
  letI : Algebra Γ((affineSpace.{u} 1).obj.left, ⊤) Γ(V.obj.left, ⊤) :=
    q.hom.left.appTop.hom.toAlgebra
  letI : Algebra Γ((affineSpace.{u} 1).obj.left, ⊤) (polyGrowth ρ₀) :=
    (φA.comp q.hom.left.appTop.hom).toAlgebra
  haveI : IsScalarTower Γ((affineSpace.{u} 1).obj.left, ⊤) Γ(V.obj.left, ⊤) (polyGrowth ρ₀) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  obtain ⟨c, hc⟩ : ∃ c, (analytification.map q).toLRSHom.base v = c := ⟨_, rfl⟩
  let ι := (analytification.map q).toLRSHom.base ⁻¹' {c}
  let P : ι → Type u := fun v' ↦ (analytification.obj V).presheaf.stalk v'.1
  let αP : ∀ v', (analytification.obj (affineSpace.{u} 1)).presheaf.stalk c →+* P v' :=
    fun v' ↦ fibreStalkMap (analytification.map q) c v'
  let βP : ∀ v', Γ(V.obj.left, ⊤) →+* P v' :=
    fun v' ↦ ((analytification.obj V).presheaf.Γgerm v'.1).hom.comp (analytificationΓ V)
  have hαβ : ∀ v' r, αP v' (algebraMap Γ((affineSpace.{u} 1).obj.left, ⊤)
      ((analytification.obj (affineSpace.{u} 1)).presheaf.stalk c) r) =
      βP v' (algebraMap Γ((affineSpace.{u} 1).obj.left, ⊤) Γ(V.obj.left, ⊤) r) := by
    intro v' r
    change fibreStalkMap _ c v' ((analytification.obj (affineSpace.{u} 1)).presheaf.Γgerm c
      (analytificationΓ _ r)) = (analytification.obj V).presheaf.Γgerm v'.1
        (analytificationΓ V (q.hom.left.appTop r))
    rw [fibreStalkMap_Γgerm, analytificationΓ_naturality]
  let J := (toProjectiveLine ρ₀).toLRSHom.base ⁻¹' {(chartPt c).1}
  have hρ : ∀ w, (toProjectiveLine ρ₀).toLRSHom.base w =
      chartAn.toLRSHom.base ((analytification.map q).toLRSHom.base (p.toLRSHom.base w)) :=
    fun w ↦ by
      have e := congrArg (fun f : W ⟶ projectiveSpaceAn.{u} 1 ↦
        f.toLRSHom.base w) (toProjectiveLine_eq hs p)
      rw [Functor.map_comp] at e
      exact e
  have hinj : Function.Injective chartAn.{u}.toLRSHom.base :=
    (PresheafedSpace.IsOpenImmersion.base_open (f := chartAn.{u}.toLRSHom.toHom)).injective
  have hJ : ∀ w : J, (analytification.map q).toLRSHom.base (p.toLRSHom.base w.1) = c :=
    fun w ↦ hinj ((hρ w.1).symm.trans w.2)
  let π : J → ι := fun w ↦ ⟨p.toLRSHom.base w.1, hJ w⟩
  let Q : J → Type u := fun w ↦ W.presheaf.stalk w.1
  let γ : ∀ v' (w : {w // π w = v'}), P v' →+* Q w.1 :=
    fun v' w ↦ fibreStalkMap p v'.1 ⟨w.1.1, congrArg Subtype.val w.2⟩
  let δ : ∀ w, polyGrowth ρ₀ →+* Q w :=
    fun w ↦ (W.presheaf.Γgerm w.1).hom.comp (polyGrowth ρ₀).subtype
  have hγδ : ∀ w a, δ w (algebraMap Γ(V.obj.left, ⊤) (polyGrowth ρ₀) a) =
      γ (π w) ⟨w, rfl⟩ (βP (π w) a) :=
    fun w a ↦ (fibreStalkMap_Γgerm p _ ⟨w.1, rfl⟩ _).symm
  have h₁ : Function.Bijective (lift₁ P αP βP hαβ) :=
    finiteAnalyticSplitting.{u} V (affineSpace.{u} 1) q c
  -- the splitting of `P` over `c`, from the splitting over `ℙ¹_an`
  have h₂ : Function.Bijective (lift₂ P αP βP hαβ π Q γ δ hγδ) := by
    letI : Algebra ringU₀.{u} ((projectiveSpaceAn.{u} 1).presheaf.stalk (chartPt c).1) :=
      analytificationStalkSectionsAlgebra (chartPt c)
    let θ := chartΓEquiv.{u}.symm
    have hθ : ∀ r, chartΓ (θ r) = r := chartΓ_chartΓEquiv_symm
    let σ := chartStalkEquiv.{u} c
    have hσ : ∀ r, σ (algebraMap ringU₀.{u} ((projectiveSpaceAn.{u} 1).presheaf.stalk (chartPt c).1)
        (θ r)) =
        algebraMap Γ((affineSpace.{u} 1).obj.left, ⊤)
          ((analytification.obj (affineSpace.{u} 1)).presheaf.stalk c) r := fun r ↦
      (stalkMap_chartAn_algebraMap c (θ r)).trans (by rw [hθ])
    have hS : ∀ r, algebraMap ringU₀.{u} (polyGrowth ρ₀) (θ r) =
        algebraMap Γ((affineSpace.{u} 1).obj.left, ⊤) (polyGrowth ρ₀) r := fun r ↦
      Subtype.ext ((toSections_eq hs p (θ r)).trans (by rw [hθ]; rfl))
    let α : (analytification.obj (affineSpace.{u} 1)).presheaf.stalk c →+* ∀ w, Q w :=
      RingHom.pi fun w ↦ (γ (π w) ⟨w, rfl⟩).comp (αP (π w))
    let β : polyGrowth ρ₀ →+* ∀ w, Q w := RingHom.pi δ
    have hαβ' : ∀ r, α (algebraMap Γ((affineSpace.{u} 1).obj.left, ⊤) _ r) =
        β (algebraMap Γ((affineSpace.{u} 1).obj.left, ⊤) _ r) := fun r ↦
      funext fun w ↦ comp_γ_comp_αP P αP βP hαβ π Q γ δ hγδ w r
    have h₀ : Function.Bijective (transferLift₀ θ σ hσ hS α β hαβ') := by
      have hpg := bijective_polyGrowthStalkMap ρ₀ hK (chartPt c)
      have key : ∀ y, transferLift₀ θ σ hσ hS α β hαβ' y =
          polyGrowthStalkMap ρ₀ hK (chartPt c) y := by
        intro y
        induction y using TensorProduct.induction_on with
        | zero => exact (map_zero _).trans (map_zero _).symm
        | tmul t b =>
          funext w
          exact congrArg (· * W.presheaf.Γgerm w.1 b.1)
            (fibreStalkMap_comp_chartAn hs p c w.1 w.2 (hJ w) t)
        | add y y' hy hy' =>
          exact (map_add _ _ _).trans ((congrArg₂ (· + ·) hy hy').trans (map_add _ _ _).symm)
      exact ⟨fun a b h ↦ hpg.1 ((key a).symm.trans (h.trans (key b))), fun y ↦
        (hpg.2 y).imp fun a ha ↦ (key a).trans ha⟩
    exact bijective_transferLift θ σ hσ hS α β hαβ' h₀
  -- the splitting over `v`
  have h₃ := bijective_liftAt P αP βP hαβ π Q γ δ hγδ h₁ h₂ ⟨v, hc⟩
  have hwJ : ∀ w : p.toLRSHom.base ⁻¹' {v},
      (toProjectiveLine ρ₀).toLRSHom.base w.1 = (chartPt c).1 := fun w ↦
    (hρ w.1).trans (congrArg chartAn.toLRSHom.base
      ((congrArg (analytification.map q).toLRSHom.base (w.2 : _ = v)).trans hc))
  let R : (∀ w : {w // π w = ⟨v, hc⟩}, Q w.1) →
      ∀ w : p.toLRSHom.base ⁻¹' {v}, W.presheaf.stalk w.1 :=
    fun g w ↦ g ⟨⟨w.1, hwJ w⟩, Subtype.ext w.2⟩
  have hR : Function.Bijective R :=
    ⟨fun g g' h ↦ funext fun w' ↦ congrFun h ⟨w'.1.1, congrArg Subtype.val w'.2⟩,
      fun f ↦ ⟨fun w' ↦ f ⟨w'.1.1, congrArg Subtype.val w'.2⟩, rfl⟩⟩
  have key : ∀ y, stalkTensorMap p (polyGrowth ρ₀).subtype (fun _ ↦ rfl) v y =
      R (liftAt P βP π Q γ δ hγδ ⟨v, hc⟩ y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => exact (map_zero _).trans (congrArg R (map_zero _).symm)
    | tmul t b => rfl
    | add y y' hy hy' =>
      exact (map_add _ _ _).trans ((congrArg₂ (· + ·) hy hy').trans
        (congrArg R (map_add _ _ _).symm))
  exact ⟨fun a b h ↦ h₃.1 (hR.1 ((key a).symm.trans (h.trans (key b)))), fun y ↦
    (hR.2 y).elim fun g hg ↦ (h₃.2 g).imp fun a ha ↦ (key a).trans ((congrArg R ha).trans hg)⟩

end Assembly

/-- **Finite étale covers of an affine curve with a coordinate are algebraic.** Let `V` be an
affine scheme of finite type over `ℂ` and `z ∈ Γ(V, 𝒪_V)` a function over which `Γ(V, 𝒪_V)` is
finite, such that `z : V^an ⟶ ℂ` is a local isomorphism over `{‖z‖ > 1}`. Then every finite
étale cover of `V^an` with Hausdorff source is the analytification of a finite étale cover of
`V`. -/
theorem mem_essImage_of_curveCoordinate (V : SchemeLFTℂ.{u}) [IsAffine V.obj.left]
    {s : MvPolynomial (Fin 1) (ULift.{u} ℂ) →+* Γ(V.obj.left, ⊤)}
    (hs : s.comp MvPolynomial.C = V.constMap) (hsfin : s.Finite)
    (hloc : IsLocalIso (AnalyticSpace.restrictHom (SchemeLFTℂ.anToAffine s hs) outerOpens))
    (W : AnalyticSpace.FiniteEtaleOver (analytification.obj V)) [T2Space W.left] :
    (analytificationFiniteEtaleOver V).essImage W := by
  haveI : IsFinite (SchemeLFTℂ.toAffineSpace s hs).hom.left := isFinite_toAffineSpace hs hsfin
  haveI hpl : IsLocalIso W.hom := (W.prop : IsFiniteEtale W.hom).isLocalIso
  have hfin : AnalyticSpace.IsFinite (W.hom ≫ SchemeLFTℂ.anToAffine s hs) :=
    isFinite_comp_anToAffine W
  have hloc' : IsLocalIso (AnalyticSpace.restrictHom (W.hom ≫ SchemeLFTℂ.anToAffine s hs)
      outerOpens) := by
    rw [AnalyticSpace.restrictHom_comp]
    haveI := AnalyticSpace.isLocalIso_restrictHom W.hom
      ((Opens.map (SchemeLFTℂ.anToAffine s hs).toLRSHom.base).obj outerOpens)
    exact @AnalyticSpace.isLocalIso_comp _ _ _ _ _ this hloc
  have hK := isCoherent_pushUnit_comp_anToAffine (s := s) (hs := hs) W
  haveI : T2Space ((𝟭 AnalyticSpace.{u}).obj W.left).toPresheafedSpace :=
    ‹T2Space W.left.toPresheafedSpace›
  letI := (polyGrowthMap hs hsfin W.hom).toAlgebra
  haveI := module_finite_polyGrowthMap hs hsfin W.hom hfin hloc' hK
  exact (exists_iso_of_bijective_stalkTensorMap V W _ _ (fun _ ↦ rfl)
    (bijective_stalkTensorMap_polyGrowthMap hs hsfin W.hom hfin hloc' hK)).elim fun _ he ↦
      ⟨_, he⟩


/-- **Riemann existence for affine curves.** Let `V` be an affine integral scheme of finite type
over `ℂ` of dimension one. Every finite étale cover of `V^an` with Hausdorff source is the
analytification of a finite étale cover of `V`. -/
theorem mem_essImage_analytificationFiniteEtaleOver_of_ringKrullDim_eq_one
    (V : SchemeLFTℂ.{u}) [IsAffine V.obj.left] [IsIntegral V.obj.left]
    (hdim : ringKrullDim Γ(V.obj.left, ⊤) = 1)
    (W : AnalyticSpace.FiniteEtaleOver (analytification.obj V)) [T2Space W.left] :
    (analytificationFiniteEtaleOver V).essImage W := by
  obtain ⟨s, hs, hsfin, hloc⟩ := exists_curveCoordinate V hdim
  exact mem_essImage_of_curveCoordinate V hs hsfin hloc W

/-- **Riemann existence for affine curves**, for a curve all of whose finite étale analytic covers
have Hausdorff source: the analytification of finite étale covers is essentially surjective. -/
theorem essSurj_analytificationFiniteEtaleOver_of_ringKrullDim_eq_one
    (V : SchemeLFTℂ.{u}) [IsAffine V.obj.left] [IsIntegral V.obj.left]
    (hdim : ringKrullDim Γ(V.obj.left, ⊤) = 1)
    (hT2 : ∀ W : AnalyticSpace.FiniteEtaleOver (analytification.obj V), T2Space W.left) :
    (analytificationFiniteEtaleOver V).EssSurj :=
  ⟨fun W ↦ haveI := hT2 W
    mem_essImage_analytificationFiniteEtaleOver_of_ringKrullDim_eq_one V hdim W⟩

end

end ComplexAnalytic
