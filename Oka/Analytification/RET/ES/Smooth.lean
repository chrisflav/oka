/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.ES.SmoothCompare
import Oka.Analytification.RET.ES.Curve

/-!
# Finite étale covers of smooth affine varieties are algebraic, given coherence of bounded sections

Let `V` be an affine integral scheme of finite type over `ℂ` of dimension `n` whose analytification
is locally isomorphic to opens of affine spaces (e.g. `V` smooth), and `p : W ⟶ V^an` a finite
étale cover with Hausdorff source. Assume that bounded sections are coherent in dimension `n`
(`ComplexAnalytic.BoundedCoherent n`). Then `W` is the analytification of a finite étale cover of
`V` (`ComplexAnalytic.mem_essImage_of_smooth`). This holds unconditionally for `n ≤ 2`
(`ComplexAnalytic.mem_essImage_of_smooth_of_le_two`).

## Proof

Choose a finite `q : V ⟶ 𝔸ⁿ` and a nonzero polynomial `e` such that `q^an` is a local isomorphism
over `{e ≠ 0}` (`ComplexAnalytic.exists_smoothCoordinate`), and let `ρ₀ = q^an ∘ p : W ⟶ ℂⁿ`. The
sections of `ρ_* 𝒪_W` bounded near the hyperplane at infinity form a coherent sheaf on `ℙⁿ_an`
(`ComplexAnalytic.ProjectiveCompletion.isCoherent_extension`): in the chart `i`, by the Riemann
extension theorem on `W`, it is the sheaf of bounded sections of the finite étale cover of the
complement of `H_∞ ∪ {e = 0}` given by `W`. As in the curve case
(`Oka/Analytification/RET/ES/Curve.lean`), the ring `P` of functions on `W` of polynomial growth
is a finite `Γ(V, 𝒪_V)`-algebra (`ComplexAnalytic.ProjectiveCompletion.module_finite_polyGrowthMap`)
and `𝒪_{V^an,v} ⊗[Γ(V, 𝒪_V)] P → ∏_{w ∈ p⁻¹ v} 𝒪_{W,w}` is bijective for every `v`
(`ComplexAnalytic.ProjectiveCompletion.bijective_stalkTensorMap_polyGrowthMap`), by GAGA on `ℙⁿ`.
Then `W ≅ (Spec P)^an` by `ComplexAnalytic.exists_iso_of_bijective_stalkTensorMap`.
-/

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry Topology TensorProduct

universe u

namespace ComplexAnalytic

open AnalyticSpace TensorTower

noncomputable section

namespace ProjectiveCompletion

section Assembly

variable {n : ℕ} {V : SchemeLFTℂ.{u}} [IsAffine V.obj.left]
  {s : MvPolynomial (Fin n) (ULift.{u} ℂ) →+* Γ(V.obj.left, ⊤)}
  (hs : s.comp MvPolynomial.C = V.constMap) (hsfin : s.Finite) {W : AnalyticSpace.{u}}
  (p : W ⟶ analytification.obj V)

/-- The functions on `V`, pulled back to `W`, as functions of polynomial growth. -/
def polyGrowthMap : Γ(V.obj.left, ⊤) →+* polyGrowth (p ≫ SchemeLFTℂ.anToAffine s hs) :=
  ((LocallyRingedSpace.Γ.map p.toLRSHom.op).hom.comp (analytificationΓ V)).codRestrict _
    (hasPolyGrowth_pullbackΓ hs p hsfin)

variable [IsFinite (SchemeLFTℂ.toAffineSpace s hs).hom.left]
  (hfin : AnalyticSpace.IsFinite (p ≫ SchemeLFTℂ.anToAffine s hs)) [T2Space W]
  (hC : (extension (p ≫ SchemeLFTℂ.anToAffine s hs)).IsCoherent)

omit [IsAffine V.obj.left] [IsFinite (SchemeLFTℂ.toAffineSpace s hs).hom.left] [T2Space W] in
include hC in
/-- **The functions of polynomial growth form a finite algebra over `Γ(V, 𝒪_V)`.** -/
theorem module_finite_polyGrowthMap :
    letI := (polyGrowthMap hs hsfin p).toAlgebra
    Module.Finite Γ(V.obj.left, ⊤) (polyGrowth (p ≫ SchemeLFTℂ.anToAffine s hs)) := by
  letI := polyGrowthAlgebra (p ≫ SchemeLFTℂ.anToAffine s hs) hC
  letI := (polyGrowthMap hs hsfin p).toAlgebra
  letI : Algebra (ringU₀.{u} n) Γ(V.obj.left, ⊤) :=
    ((SchemeLFTℂ.toAffineSpace s hs).hom.left.appTop.hom.comp (chartΓ n)).toAlgebra
  haveI : IsScalarTower (ringU₀.{u} n) Γ(V.obj.left, ⊤)
      (polyGrowth (p ≫ SchemeLFTℂ.anToAffine s hs)) :=
    IsScalarTower.of_algebraMap_eq fun r ↦ Subtype.ext (toSections_eq hs p r)
  haveI := module_finite_polyGrowth (p ≫ SchemeLFTℂ.anToAffine s hs) hC
  exact Module.Finite.of_restrictScalars_finite (ringU₀.{u} n) _ _

include hfin hC in
/-- **The stalks of `W` are the base changes of the functions of polynomial growth**: for every
`v ∈ V^an` the map `𝒪_{V^an,v} ⊗[Γ(V, 𝒪_V)] P → ∏_{w ∈ p⁻¹ v} 𝒪_{W,w}` is bijective. The
splitting over `ℙⁿ_an` (`ComplexAnalytic.ProjectiveCompletion.bijective_polyGrowthStalkMap`) is
moved to `𝔸ⁿ^an` along the chart and then split along `V^an ⟶ 𝔸ⁿ^an`
(`ComplexAnalytic.finiteAnalyticSplitting`, `ComplexAnalytic.TensorTower.bijective_liftAt`). -/
theorem bijective_stalkTensorMap_polyGrowthMap (v : analytification.obj V) :
    letI := (polyGrowthMap hs hsfin p).toAlgebra
    Function.Bijective (stalkTensorMap p (polyGrowth (p ≫ SchemeLFTℂ.anToAffine s hs)).subtype
      (fun _ ↦ rfl) v) := by
  haveI : IsAffine (affineSpace.{u} n).obj.left := inferInstanceAs (IsAffine (Spec _))
  haveI := hfin
  set ρ₀ := p ≫ SchemeLFTℂ.anToAffine s hs with hρ₀
  letI alg₀ := polyGrowthAlgebra ρ₀ hC
  set φA := polyGrowthMap hs hsfin p
  letI : Algebra Γ(V.obj.left, ⊤) (polyGrowth ρ₀) := φA.toAlgebra
  -- the tower `Γ(𝔸ⁿ, 𝒪) → Γ(V, 𝒪_V) → P` over the point `c = q^an v`
  set q := SchemeLFTℂ.toAffineSpace s hs with hq
  letI : Algebra Γ((affineSpace.{u} n).obj.left, ⊤) Γ(V.obj.left, ⊤) :=
    q.hom.left.appTop.hom.toAlgebra
  letI : Algebra Γ((affineSpace.{u} n).obj.left, ⊤) (polyGrowth ρ₀) :=
    (φA.comp q.hom.left.appTop.hom).toAlgebra
  haveI : IsScalarTower Γ((affineSpace.{u} n).obj.left, ⊤) Γ(V.obj.left, ⊤) (polyGrowth ρ₀) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  obtain ⟨c, hc⟩ : ∃ c, (analytification.map q).toLRSHom.base v = c := ⟨_, rfl⟩
  let ι := (analytification.map q).toLRSHom.base ⁻¹' {c}
  let P : ι → Type u := fun v' ↦ (analytification.obj V).presheaf.stalk v'.1
  let αP : ∀ v', (analytification.obj (affineSpace.{u} n)).presheaf.stalk c →+* P v' :=
    fun v' ↦ fibreStalkMap (analytification.map q) c v'
  let βP : ∀ v', Γ(V.obj.left, ⊤) →+* P v' :=
    fun v' ↦ ((analytification.obj V).presheaf.Γgerm v'.1).hom.comp (analytificationΓ V)
  have hαβ : ∀ v' r, αP v' (algebraMap Γ((affineSpace.{u} n).obj.left, ⊤)
      ((analytification.obj (affineSpace.{u} n)).presheaf.stalk c) r) =
      βP v' (algebraMap Γ((affineSpace.{u} n).obj.left, ⊤) Γ(V.obj.left, ⊤) r) := by
    intro v' r
    change fibreStalkMap _ c v' ((analytification.obj (affineSpace.{u} n)).presheaf.Γgerm c
      (analytificationΓ _ r)) = (analytification.obj V).presheaf.Γgerm v'.1
        (analytificationΓ V (q.hom.left.appTop r))
    rw [fibreStalkMap_Γgerm, analytificationΓ_naturality]
  let J := (toProj ρ₀).toLRSHom.base ⁻¹' {(chartPt c).1}
  have hρ : ∀ w, (toProj ρ₀).toLRSHom.base w =
      chartAn.toLRSHom.base ((analytification.map q).toLRSHom.base (p.toLRSHom.base w)) :=
    fun w ↦ by
      have e := congrArg (fun f : W ⟶ projectiveSpaceAn.{u} n ↦
        f.toLRSHom.base w) (toProj_eq hs p)
      rw [Functor.map_comp] at e
      exact e
  have hinj : Function.Injective (chartAn.{u} (n := n)).toLRSHom.base :=
    (PresheafedSpace.IsOpenImmersion.base_open
      (f := (chartAn.{u} (n := n)).toLRSHom.toHom)).injective
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
    finiteAnalyticSplitting.{u} V (affineSpace.{u} n) q c
  -- the splitting of `P` over `c`, from the splitting over `ℙⁿ_an`
  have h₂ : Function.Bijective (lift₂ P αP βP hαβ π Q γ δ hγδ) := by
    letI : Algebra (ringU₀.{u} n) ((projectiveSpaceAn.{u} n).presheaf.stalk (chartPt c).1) :=
      analytificationStalkSectionsAlgebra (chartPt c)
    let θ := (chartΓEquiv.{u} n).symm
    have hθ : ∀ r, chartΓ n (θ r) = r := chartΓ_chartΓEquiv_symm
    let σ := chartStalkEquiv.{u} c
    have hσ : ∀ r, σ (algebraMap (ringU₀.{u} n)
        ((projectiveSpaceAn.{u} n).presheaf.stalk (chartPt c).1)
        (θ r)) =
        algebraMap Γ((affineSpace.{u} n).obj.left, ⊤)
          ((analytification.obj (affineSpace.{u} n)).presheaf.stalk c) r := fun r ↦
      (stalkMap_chartAn_algebraMap c (θ r)).trans (by rw [hθ])
    have hS : ∀ r, algebraMap (ringU₀.{u} n) (polyGrowth ρ₀) (θ r) =
        algebraMap Γ((affineSpace.{u} n).obj.left, ⊤) (polyGrowth ρ₀) r := fun r ↦
      Subtype.ext ((toSections_eq hs p (θ r)).trans (by rw [hθ]; rfl))
    let α : (analytification.obj (affineSpace.{u} n)).presheaf.stalk c →+* ∀ w, Q w :=
      RingHom.pi fun w ↦ (γ (π w) ⟨w, rfl⟩).comp (αP (π w))
    let β : polyGrowth ρ₀ →+* ∀ w, Q w := RingHom.pi δ
    have hαβ' : ∀ r, α (algebraMap Γ((affineSpace.{u} n).obj.left, ⊤) _ r) =
        β (algebraMap Γ((affineSpace.{u} n).obj.left, ⊤) _ r) := fun r ↦
      funext fun w ↦ comp_γ_comp_αP P αP βP hαβ π Q γ δ hγδ w r
    have h₀ : Function.Bijective (transferLift₀ θ σ hσ hS α β hαβ') := by
      have hpg := bijective_polyGrowthStalkMap ρ₀ hC (chartPt c)
      have key : ∀ y, transferLift₀ θ σ hσ hS α β hαβ' y =
          polyGrowthStalkMap ρ₀ hC (chartPt c) y := by
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
      (toProj ρ₀).toLRSHom.base w.1 = (chartPt c).1 := fun w ↦
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

end ProjectiveCompletion

open ProjectiveCompletion

/-- **Finite étale covers are algebraic, given a coherent extension to `ℙⁿ`.** Let `V` be an
affine scheme of finite type over `ℂ`, `q : V ⟶ 𝔸ⁿ` finite, given by `n` global functions, and
`W` a finite étale cover of `V^an` with Hausdorff source such that the sections of `𝒪_W` bounded
near the hyperplane at infinity form a coherent sheaf on `ℙⁿ_an`. Then `W` is the
analytification of a finite étale cover of `V`. -/
theorem mem_essImage_of_isCoherent_extension (V : SchemeLFTℂ.{u}) [IsAffine V.obj.left] {n : ℕ}
    {s : MvPolynomial (Fin n) (ULift.{u} ℂ) →+* Γ(V.obj.left, ⊤)}
    (hs : s.comp MvPolynomial.C = V.constMap) (hsfin : s.Finite)
    (W : AnalyticSpace.FiniteEtaleOver (analytification.obj V)) [T2Space W.left]
    (hC : (extension (W.hom ≫ SchemeLFTℂ.anToAffine s hs)).IsCoherent) :
    (analytificationFiniteEtaleOver V).essImage W := by
  haveI : IsFinite (SchemeLFTℂ.toAffineSpace s hs).hom.left := isFinite_toAffineSpace hs hsfin
  have hfin : AnalyticSpace.IsFinite (W.hom ≫ SchemeLFTℂ.anToAffine s hs) :=
    isFinite_hom_comp_anToAffine W
  haveI : T2Space ((𝟭 AnalyticSpace.{u}).obj W.left).toPresheafedSpace :=
    ‹T2Space W.left.toPresheafedSpace›
  letI := (ProjectiveCompletion.polyGrowthMap hs hsfin W.hom).toAlgebra
  haveI := ProjectiveCompletion.module_finite_polyGrowthMap hs hsfin W.hom hC
  exact (exists_iso_of_bijective_stalkTensorMap V W _ _ (fun _ ↦ rfl)
    (ProjectiveCompletion.bijective_stalkTensorMap_polyGrowthMap hs hsfin W.hom hfin hC)).elim
      fun _ he ↦ ⟨_, he⟩

/-- **Riemann existence for smooth affine varieties, given coherence of bounded sections.** Let
`V` be an affine integral scheme of finite type over `ℂ` of dimension `n` whose analytification
is locally isomorphic to opens of affine spaces. If bounded sections are coherent in dimension `n`,
then every finite étale cover of `V^an` with Hausdorff source is the analytification of a finite
étale cover of `V`. -/
theorem mem_essImage_of_smooth {n : ℕ} (hB : BoundedCoherent.{u} n) (V : SchemeLFTℂ.{u})
    [IsAffine V.obj.left] [IsIntegral V.obj.left] (hdim : ringKrullDim Γ(V.obj.left, ⊤) = n)
    (hV : IsLocallyOpenInAffine (analytification.obj V))
    (W : AnalyticSpace.FiniteEtaleOver (analytification.obj V)) [T2Space W.left] :
    (analytificationFiniteEtaleOver V).essImage W := by
  obtain ⟨s, hs, e, hsfin, hsinj, he, hloc⟩ := exists_smoothCoordinate V hdim
  haveI : IsFinite (SchemeLFTℂ.toAffineSpace s hs).hom.left := isFinite_toAffineSpace hs hsfin
  have hpl : IsLocalIso W.hom := (W.prop : IsFiniteEtale W.hom).isLocalIso
  haveI : T2Space ((𝟭 AnalyticSpace.{u}).obj W.left).toPresheafedSpace :=
    ‹T2Space W.left.toPresheafedSpace›
  haveI : AnalyticSpace.IsFinite (W.hom ≫ SchemeLFTℂ.anToAffine s hs) :=
    isFinite_hom_comp_anToAffine W
  haveI : IsLocalIso (AnalyticSpace.restrictHom (W.hom ≫ SchemeLFTℂ.anToAffine s hs)
      (polyOpens e)) :=
    @isLocalIso_restrictHom_comp_anToAffine V n s hs _ W.hom hpl (polyOpens e) hloc
  have hW : IsLocallyOpenInAffine W.left := @IsLocallyOpenInAffine.of_isLocalIso _ _ W.hom hpl hV
  have hZ : interior {w | polyEval e ((W.hom ≫ SchemeLFTℂ.anToAffine s hs).toLRSHom.base w) = 0}
      = ∅ := by
    have ha : s (uliftPolyN n e) ≠ 0 := fun h ↦ he ((uliftPolyN n).injective
      (hsinj (h.trans (map_zero s).symm)))
    have h := @interior_preimage_eq_empty_of_isLocalIso _ _ W.hom hpl _
      (interior_setOf_evalPoint_eq_zero V hV ha)
    have hset : {w | polyEval e ((W.hom ≫ SchemeLFTℂ.anToAffine s hs).toLRSHom.base w) = 0} =
        W.hom.toLRSHom.base ⁻¹' {v | evalPoint V v (s (uliftPolyN n e)) = 0} := by
      ext w
      simp only [Set.mem_setOf_eq, Set.mem_preimage]
      rw [evalPoint_eq_affineEval s hs, affineEval_uliftPolyN]
      rfl
    rw [hset]
    exact h
  exact mem_essImage_of_isCoherent_extension V hs hsfin W
    (isCoherent_extension _ hB he hW hZ)

/-- A scheme of finite type over `ℂ` is **locally étale over affine spaces** if every point has an
open neighbourhood with an étale morphism to some `𝔸ᵐ`; for instance, `V` smooth over `ℂ`. -/
def SchemeLFTℂ.IsLocallyEtaleOverAffineSpace (V : SchemeLFTℂ.{u}) : Prop :=
  ∀ x : V.obj.left, ∃ (U : V.obj.left.Opens) (_ : x ∈ U) (m : ℕ)
    (f : V.restrict U ⟶ affineSpace.{u} m), Etale f.hom.left

/-- **The analytification of a scheme locally étale over affine spaces is locally isomorphic to
opens of affine spaces.** -/
theorem isLocallyOpenInAffine_analytification {V : SchemeLFTℂ.{u}}
    (hV : V.IsLocallyEtaleOverAffineSpace) :
    IsLocallyOpenInAffine (analytification.obj V) := by
  intro v
  obtain ⟨U, hxU, m, f, hf⟩ := hV ((analytificationπLRS V).base v)
  haveI := isLocalIso_analytification_map_of_etale f
  haveI : Etale (V.restrictι U).hom.left := by
    change Etale U.ι
    infer_instance
  haveI := isLocalIso_analytification_map_of_etale (V.restrictι U)
  haveI := isLocalIso_of_isIso (analytificationAffineSpaceIso.{u} m).hom
  let g := analytification.map f ≫ (analytificationAffineSpaceIso.{u} m).hom
  let g' := liftRestrict g (⊤ : (AnalyticSpace.complexAffineSpace.{u} m).Opens)
    fun _ _ ↦ trivial
  haveI : IsLocalIso (g' ≫ (AnalyticSpace.complexAffineSpace.{u} m).ofRestrict ⊤) := by
    rw [liftRestrict_fac]
    infer_instance
  haveI : IsLocalIso g' :=
    isLocalIso_of_comp g' ((AnalyticSpace.complexAffineSpace.{u} m).ofRestrict ⊤)
  have hv : v ∈ Set.range (analytification.map (V.restrictι U)).toLRSHom.base := by
    rw [range_analytification_map_restrictι]
    exact hxU
  obtain ⟨z, rfl⟩ := hv
  obtain ⟨k, U', ψ, y, hψ, hy⟩ := isLocallyOpenInAffine_of_isLocalIso g' z
  haveI := hψ
  exact ⟨k, U', ψ ≫ analytification.map (V.restrictι U), y, inferInstance,
    congrArg (analytification.map (V.restrictι U)).toLRSHom.base hy⟩

/-- **Riemann existence for affine varieties locally étale over affine spaces, given coherence of
bounded sections.** Let `V` be an affine integral scheme of finite type over `ℂ` of dimension `n`
which is locally étale over affine spaces (for instance, smooth). If bounded sections are
coherent in dimension `n`, then every finite étale cover of `V^an` with Hausdorff source is the
analytification of a finite étale cover of `V`. -/
theorem mem_essImage_of_isLocallyEtaleOverAffineSpace {n : ℕ} (hB : BoundedCoherent.{u} n)
    (V : SchemeLFTℂ.{u}) [IsAffine V.obj.left] [IsIntegral V.obj.left]
    (hdim : ringKrullDim Γ(V.obj.left, ⊤) = n) (hV : V.IsLocallyEtaleOverAffineSpace)
    (W : AnalyticSpace.FiniteEtaleOver (analytification.obj V)) [T2Space W.left] :
    (analytificationFiniteEtaleOver V).essImage W :=
  mem_essImage_of_smooth hB V hdim (isLocallyOpenInAffine_analytification hV) W

/-- **Riemann existence for smooth affine surfaces and curves.** Let `V` be an affine integral
scheme of finite type over `ℂ` of dimension at most two whose analytification is locally
isomorphic to opens of affine spaces. Every finite étale cover of `V^an` with Hausdorff source is
the analytification of a finite étale cover of `V`. -/
theorem mem_essImage_of_smooth_of_le_two {n : ℕ} (hn : n ≤ 2) (V : SchemeLFTℂ.{u})
    [IsAffine V.obj.left] [IsIntegral V.obj.left] (hdim : ringKrullDim Γ(V.obj.left, ⊤) = n)
    (hV : IsLocallyOpenInAffine (analytification.obj V))
    (W : AnalyticSpace.FiniteEtaleOver (analytification.obj V)) [T2Space W.left] :
    (analytificationFiniteEtaleOver V).essImage W :=
  mem_essImage_of_smooth (boundedCoherent_of_le_two hn) V hdim hV W

/-- **Riemann existence for affine surfaces and curves locally étale over affine spaces.** Let `V`
be an affine integral scheme of finite type over `ℂ` of dimension at most two which is locally
étale over affine spaces (for instance, smooth). Every finite étale cover of `V^an` with Hausdorff
source is the analytification of a finite étale cover of `V`. -/
theorem mem_essImage_of_isLocallyEtaleOverAffineSpace_of_le_two {n : ℕ} (hn : n ≤ 2)
    (V : SchemeLFTℂ.{u}) [IsAffine V.obj.left] [IsIntegral V.obj.left]
    (hdim : ringKrullDim Γ(V.obj.left, ⊤) = n) (hV : V.IsLocallyEtaleOverAffineSpace)
    (W : AnalyticSpace.FiniteEtaleOver (analytification.obj V)) [T2Space W.left] :
    (analytificationFiniteEtaleOver V).essImage W :=
  mem_essImage_of_isLocallyEtaleOverAffineSpace (boundedCoherent_of_le_two hn) V hdim hV W

end

end ComplexAnalytic
