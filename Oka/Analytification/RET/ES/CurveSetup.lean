/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.ES.CurveEtale
import Oka.Analytification.RET.ES.CurveExtension
import Oka.Analytification.RET.ES.FiniteCoherent
import Oka.Analytification.RET.EtaleLocalIso
import Oka.Analytification.RET.FiniteAnalytification
import Oka.Analytification.GAGA.ClosedImmersion
import Oka.Geometry.RingedSpace.LocallyRingedSpace.CoherentModuleOpenEmbedding

/-!
# A coordinate on an affine curve

Let `V` be an affine integral scheme of finite type over `ℂ` of dimension one. There is a finite
morphism `q : V ⟶ 𝔸¹` given by one global function `z`, such that `q` is étale over
`{‖z‖ > 1}` (`ComplexAnalytic.exists_curveCoordinate`): by Noether normalisation `Γ(V, 𝒪_V)` is
finite over `ℂ[z]`, by generic étaleness it is étale over `ℂ[z]` after inverting a nonzero
polynomial `e`, and after rescaling `z` the zeros of `e` lie in the unit disc.

For a finite étale cover `p : W ⟶ V^an` with Hausdorff source, the composite `ρ₀ : W ⟶ ℂ¹` of `p`
with `q^an` is then finite, a local isomorphism over `{‖z‖ > 1}`, and `ρ₀_* 𝒪_W` is coherent
(`ComplexAnalytic.isCoherent_pushUnit_comp_anToAffine`).
-/

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry Topology

universe u

namespace ComplexAnalytic

open AnalyticSpace ProjectiveLine

noncomputable section

/-- **A morphism is a local isomorphism over an open covered by local isomorphisms**: if
`j : Z ⟶ X` and `j ≫ f` are local isomorphisms and `f⁻¹ V` lies in the image of `j`, then
`f` restricted over `V` is a local isomorphism. -/
theorem AnalyticSpace.isLocalIso_restrictHom_of_subset_range {X Y Z : AnalyticSpace.{u}}
    (j : Z ⟶ X) (f : X ⟶ Y) (V : Y.Opens) [IsLocalIso j] [IsLocalIso (j ≫ f)]
    (hV : f.toLRSHom.base ⁻¹' V ⊆ Set.range j.toLRSHom.base) :
    IsLocalIso (AnalyticSpace.restrictHom f V) where
  isLocalHomeomorph := by
    have hsq : ((Y.ofRestrict V).toLRSHom.base : Y.restrict V → Y) ∘
        ((AnalyticSpace.restrictHom f V).toLRSHom.base : _ → Y.restrict V) =
        (f.toLRSHom.base : X → Y) ∘
          ((X.ofRestrict ((Opens.map f.toLRSHom.base).obj V)).toLRSHom.base : _ → X) :=
      funext fun x ↦ ComplexAnalytic.base_restrictHom f.toLRSHom V x
    have hf : IsLocalHomeomorphOn (f.toLRSHom.base : X → Y) (Set.range j.toLRSHom.base) := by
      have h : IsLocalHomeomorphOn ((f.toLRSHom.base : X → Y) ∘ (j.toLRSHom.base : Z → X))
          Set.univ := (IsLocalIso.isLocalHomeomorph (f := j ≫ f)).isLocalHomeomorphOn
      rw [← Set.image_univ]
      exact h.of_comp_right (IsLocalIso.isLocalHomeomorph (f := j)).isLocalHomeomorphOn
    refine IsLocalHomeomorph.of_comp (g := ((Y.ofRestrict V).toLRSHom.base : Y.restrict V → Y))
      ?_ V.isOpenEmbedding.isLocalHomeomorph
      (AnalyticSpace.restrictHom f V).toLRSHom.base.hom.continuous
    rw [hsq, isLocalHomeomorph_iff_isLocalHomeomorphOn_univ]
    have hinc : IsLocalHomeomorph
        ((X.ofRestrict ((Opens.map f.toLRSHom.base).obj V)).toLRSHom.base : _ → X) :=
      ((Opens.map f.toLRSHom.base).obj V).isOpenEmbedding.isLocalHomeomorph
    exact hf.comp hinc.isLocalHomeomorphOn fun x _ ↦ hV x.2
  isIso_stalkMap x := by
    obtain ⟨x, hx⟩ := x
    obtain ⟨z, rfl⟩ := hV hx
    have h2 : IsIso (f.toLRSHom.stalkMap (j.toLRSHom.base z)) := by
      have h1 : IsIso ((j ≫ f).toLRSHom.stalkMap z) := IsLocalIso.isIso_stalkMap z
      rw [show (j ≫ f).toLRSHom = j.toLRSHom ≫ f.toLRSHom from rfl,
        LocallyRingedSpace.stalkMap_comp] at h1
      exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ (j.toLRSHom.stalkMap z) inferInstance h1
    exact (ComplexAnalytic.stalkMap_restrictHom_eq' f.toLRSHom V _).symm ▸
      IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' h2 (inferInstance : IsIso
        ((X.toLocallyRingedSpace.ofRestrict ((Opens.map f.toLRSHom.base).obj V).isOpenEmbedding
          ).stalkMap _)))

section Points

variable (V : SchemeLFTℂ.{u})

lemma mem_basicOpen_of_evalPoint_ne_zero (v : analytification.obj V) (f : Γ(V.obj.left, ⊤))
    (h : evalPoint V v f ≠ 0) : (analytificationπLRS V).base v ∈ V.obj.left.basicOpen f := by
  rw [Scheme.mem_basicOpen_top]
  by_contra hu
  apply h
  rw [← RingHom.mem_ker, ker_evalPoint, idealOfPoint_eq, Ideal.mem_comap]
  exact (IsLocalRing.mem_maximalIdeal _).2 hu

variable {V} {N : ℕ} (s : MvPolynomial (Fin N) (ULift.{u} ℂ) →+* Γ(V.obj.left, ⊤))
  (hs : s.comp MvPolynomial.C = V.constMap)

lemma evalPoint_eq_affineEval (v : analytification.obj V)
    (p : MvPolynomial (Fin N) (ULift.{u} ℂ)) :
    evalPoint V v (s p) = affineEval N ((SchemeLFTℂ.anToAffine s hs).toLRSHom.base v) p :=
  SchemeLFTℂ.eval_analytificationΓ s hs v p

end Points

section Etale

variable {V : SchemeLFTℂ.{u}} [IsAffine V.obj.left] {N : ℕ}
  (s : MvPolynomial (Fin N) (ULift.{u} ℂ) →+* Γ(V.obj.left, ⊤))
  (hs : s.comp MvPolynomial.C = V.constMap)

/-- If `Γ(V, 𝒪_V)_f` is étale over `ℂ[z₁, …, z_N]`, then `V` is étale over `𝔸ᴺ` on `D(f)`. -/
lemma etale_restrictι_comp_toAffineSpace (f : Γ(V.obj.left, ⊤))
    (hf : ((algebraMap Γ(V.obj.left, ⊤) Γ(V.obj.left, V.obj.left.basicOpen f)).comp s).Etale) :
    Etale (V.restrictι (V.obj.left.basicOpen f) ≫ SchemeLFTℂ.toAffineSpace s hs).hom.left := by
  set U := V.obj.left.basicOpen f
  haveI : IsAffine (V.restrict U).obj.left := (isAffineOpen_top V.obj.left).basicOpen f
  haveI : IsAffine (affineSpace.{u} N).obj.left :=
    inferInstanceAs (IsAffine (Spec (.of (MvPolynomial (Fin N) (ULift.{u} ℂ)))))
  rw [HasRingHomProperty.iff_of_isAffine (P := @Etale)]
  change RingHom.Etale (Scheme.Hom.appTop (U.ι ≫ (SchemeLFTℂ.toAffineSpace s hs).hom.left)).hom
  rw [Scheme.Hom.comp_appTop]
  refine (RingHom.Etale.respectsIso.cancel_left_isIso
    (Scheme.ΓSpecIso (.of (MvPolynomial (Fin N) (ULift.{u} ℂ)))).inv _).1
    ((RingHom.Etale.respectsIso.cancel_right_isIso _ U.topIso.hom).1 ?_)
  convert hf using 2
  · rfl
  · refine RingHom.ext fun p ↦ ?_
    change U.topIso.hom (U.ι.appTop ((SchemeLFTℂ.toAffineSpace s hs).hom.left.appTop
      ((Scheme.ΓSpecIso (.of (MvPolynomial (Fin N) (ULift.{u} ℂ)))).inv p))) = _
    rw [SchemeLFTℂ.toAffineSpace_appTop]
    change (U.ι.appTop ≫ U.topIso.hom) (s p) = V.obj.left.presheaf.map _ (s p)
    rw [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom]
    erw [← Functor.map_comp]
    rfl

end Etale

section Coordinate

/-- A nonzero polynomial in one variable has no zeros of large norm. -/
lemma exists_forall_eval_ne_zero {e : MvPolynomial (Fin 1) ℂ} (he : e ≠ 0) :
    ∃ M : ℝ, 0 < M ∧ ∀ z : ℂ, M < ‖z‖ → MvPolynomial.eval (fun _ ↦ z) e ≠ 0 := by
  let φ : MvPolynomial (Fin 1) ℂ →ₐ[ℂ] Polynomial ℂ := MvPolynomial.aeval fun _ ↦ Polynomial.X
  let ψ : Polynomial ℂ →ₐ[ℂ] MvPolynomial (Fin 1) ℂ := Polynomial.aeval (MvPolynomial.X 0)
  have hψφ : ψ.comp φ = AlgHom.id ℂ _ := by
    refine MvPolynomial.algHom_ext fun i ↦ ?_
    rw [Subsingleton.elim i 0]
    simp [φ, ψ]
  have hφ : φ e ≠ 0 := fun h ↦ he (by
    have := congrArg (fun F : MvPolynomial (Fin 1) ℂ →ₐ[ℂ] MvPolynomial (Fin 1) ℂ ↦ F e) hψφ
    simpa [h] using this.symm)
  have heval (z : ℂ) : (φ e).eval z = MvPolynomial.eval (fun _ ↦ z) e := by
    have : (Polynomial.aeval z).comp φ = MvPolynomial.aeval (fun _ ↦ z) := by
      refine MvPolynomial.algHom_ext fun i ↦ ?_
      simp [φ]
    exact congrArg (fun F : MvPolynomial (Fin 1) ℂ →ₐ[ℂ] ℂ ↦ F e) this
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).1
    (Polynomial.finite_setOf_isRoot hφ).isBounded
  refine ⟨max r 0 + 1, by positivity, fun z hz h0 ↦ ?_⟩
  have hz' : z ∈ Metric.closedBall (0 : ℂ) r := hr (show (φ e).IsRoot z by
    rw [Polynomial.IsRoot, heval, h0])
  rw [Metric.mem_closedBall, dist_zero_right] at hz'
  linarith [le_max_left r 0]

/-- The rescaling `z ↦ c z` of the coordinate of `𝔸¹`. -/
def scaleHom (c : ℂ) :
    MvPolynomial (Fin 1) (ULift.{u} ℂ) →ₐ[ULift.{u} ℂ] MvPolynomial (Fin 1) (ULift.{u} ℂ) :=
  MvPolynomial.aeval fun i ↦ MvPolynomial.C ⟨c⟩ * MvPolynomial.X i

lemma scaleHom_scaleHom {c d : ℂ} (h : c * d = 1) (p : MvPolynomial (Fin 1) (ULift.{u} ℂ)) :
    scaleHom c (scaleHom d p) = p := by
  have : (scaleHom c).comp (scaleHom d) = AlgHom.id _ _ := by
    refine MvPolynomial.algHom_ext fun i ↦ ?_
    simp only [scaleHom, AlgHom.comp_apply, MvPolynomial.aeval_X, map_mul,
      MvPolynomial.aeval_C, AlgHom.id_apply]
    rw [MvPolynomial.algebraMap_eq, ← mul_assoc, ← map_mul,
      show ((⟨d⟩ : ULift.{u} ℂ) * ⟨c⟩) = 1 from ULift.ext _ _ (by
        change d * c = 1
        rw [mul_comm]
        exact h), map_one, one_mul]
  exact congrArg (fun F : MvPolynomial (Fin 1) (ULift.{u} ℂ) →ₐ[ULift.{u} ℂ] _ ↦ F p) this

lemma bijective_scaleHom {c : ℂ} (hc : c ≠ 0) : Function.Bijective (scaleHom.{u} c) :=
  Function.bijective_iff_has_inverse.2 ⟨scaleHom c⁻¹,
    scaleHom_scaleHom (inv_mul_cancel₀ hc), scaleHom_scaleHom (mul_inv_cancel₀ hc)⟩

/-- Polynomials over `ℂ` as polynomials over `ULift ℂ`. -/
abbrev uliftPoly : MvPolynomial (Fin 1) ℂ ≃+* MvPolynomial (Fin 1) (ULift.{u} ℂ) :=
  MvPolynomial.mapEquiv (Fin 1) ULift.ringEquiv.symm

lemma affineEval_scaleHom_uliftPoly (c : ℂ) (w : AnalyticSpace.complexAffineSpace.{u} 1)
    (p : MvPolynomial (Fin 1) ℂ) :
    affineEval 1 w (scaleHom c (uliftPoly p)) =
      MvPolynomial.eval (fun _ ↦ c * ProjectiveLine.coord w) p := by
  have : (affineEval 1 w).comp ((scaleHom c).toRingHom.comp uliftPoly.toRingHom) =
      MvPolynomial.eval fun _ ↦ c * ProjectiveLine.coord w := by
    refine MvPolynomial.ringHom_ext (fun a ↦ ?_) fun i ↦ ?_
    · simp [scaleHom, affineEval]
    · rw [Subsingleton.elim i 0]
      simp [scaleHom, affineEval]
      rfl
  exact RingHom.congr_fun this p

end Coordinate

section Curve

variable (V : SchemeLFTℂ.{u}) [IsAffine V.obj.left]

variable {V} in
lemma isFinite_toAffineSpace {N : ℕ} {s : MvPolynomial (Fin N) (ULift.{u} ℂ) →+* Γ(V.obj.left, ⊤)}
    (hs : s.comp MvPolynomial.C = V.constMap) (hsfin : s.Finite) :
    IsFinite (SchemeLFTℂ.toAffineSpace s hs).hom.left := by
  haveI : IsFinite (Spec.map (CommRingCat.ofHom s)) := by
    rw [IsFinite.SpecMap_iff]
    exact hsfin
  change IsFinite (V.obj.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom s))
  infer_instance

/-- **A coordinate on an affine curve.** For an affine integral scheme `V` of finite type over
`ℂ` of dimension one there is a finite morphism `q : V ⟶ 𝔸¹`, given by a global function, such
that `q^an : V^an ⟶ ℂ¹` is a local isomorphism over `{‖z‖ > 1}`. -/
theorem exists_curveCoordinate [IsIntegral V.obj.left]
    (hdim : ringKrullDim Γ(V.obj.left, ⊤) = 1) :
    ∃ (s : MvPolynomial (Fin 1) (ULift.{u} ℂ) →+* Γ(V.obj.left, ⊤))
      (hs : s.comp MvPolynomial.C = V.constMap),
      s.Finite ∧
        IsLocalIso (AnalyticSpace.restrictHom (SchemeLFTℂ.anToAffine s hs) outerOpens) := by
  classical
  letI : Algebra (ULift.{u} ℂ) Γ(V.obj.left, ⊤) := V.constMap.toAlgebra
  obtain ⟨n, s₀, hs₀surj, hs₀⟩ := V.exists_surjective
  haveI : Algebra.FiniteType (ULift.{u} ℂ) Γ(V.obj.left, ⊤) :=
    Algebra.FiniteType.of_surjective (R := ULift.{u} ℂ)
      { s₀ with commutes' := fun c ↦ RingHom.congr_fun hs₀ c } hs₀surj
  obtain ⟨g₀, hg₀inj, hg₀fin⟩ := exists_finite_injective_of_ringKrullDim_eq_one
    (k := ULift.{u} ℂ) (A := Γ(V.obj.left, ⊤)) hdim
  letI : Algebra (MvPolynomial (Fin 1) ℂ) Γ(V.obj.left, ⊤) :=
    (g₀.toRingHom.comp uliftPoly.toRingHom).toAlgebra
  haveI : Module.Finite (MvPolynomial (Fin 1) ℂ) Γ(V.obj.left, ⊤) :=
    RingHom.Finite.comp hg₀fin (RingHom.Finite.of_surjective _ uliftPoly.surjective)
  haveI : FaithfulSMul (MvPolynomial (Fin 1) ℂ) Γ(V.obj.left, ⊤) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (hg₀inj.comp uliftPoly.injective)
  obtain ⟨e, he0, het⟩ := exists_etale_localizationAway.{u, u} (d := 1) (A := Γ(V.obj.left, ⊤))
  obtain ⟨M, hM0, hM⟩ := exists_forall_eval_ne_zero he0
  set f : Γ(V.obj.left, ⊤) := g₀ (uliftPoly e)
  set U := V.obj.left.basicOpen f
  haveI : IsLocalization.Away (algebraMap (MvPolynomial (Fin 1) ℂ) Γ(V.obj.left, ⊤) e)
      Γ(V.obj.left, U) := (isAffineOpen_top V.obj.left).isLocalization_basicOpen f
  have hM' : (M : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hM0.ne'
  let s : MvPolynomial (Fin 1) (ULift.{u} ℂ) →+* Γ(V.obj.left, ⊤) :=
    g₀.toRingHom.comp (scaleHom.{u} (M : ℂ)⁻¹).toRingHom
  have hs : s.comp MvPolynomial.C = V.constMap := by
    ext c
    simp only [s, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, AlgHom.commutes]
    rfl
  have hsf : f = s (scaleHom (M : ℂ) (uliftPoly e)) := by
    simp only [s, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [scaleHom_scaleHom (inv_mul_cancel₀ hM')]
  refine ⟨s, hs, ?_, ?_⟩
  · exact RingHom.Finite.comp hg₀fin
      (RingHom.Finite.of_surjective _ (bijective_scaleHom (inv_ne_zero hM')).2)
  · have hfet : ((algebraMap Γ(V.obj.left, ⊤) Γ(V.obj.left, U)).comp s).Etale := by
      have e1 : (algebraMap Γ(V.obj.left, ⊤) Γ(V.obj.left, U)).comp s =
          ((algebraMap Γ(V.obj.left, ⊤) Γ(V.obj.left, U)).comp
            (algebraMap (MvPolynomial (Fin 1) ℂ) Γ(V.obj.left, ⊤))).comp
            (uliftPoly.symm.toRingHom.comp (scaleHom.{u} (M : ℂ)⁻¹).toRingHom) := by
        refine RingHom.ext fun p ↦ ?_
        change algebraMap Γ(V.obj.left, ⊤) Γ(V.obj.left, U) (g₀ (scaleHom _ p)) =
          algebraMap Γ(V.obj.left, ⊤) Γ(V.obj.left, U)
            (g₀ (uliftPoly (uliftPoly.symm (scaleHom _ p))))
        rw [RingEquiv.apply_symm_apply]
      rw [e1]
      exact RingHom.Etale.comp_of_bijective (f := uliftPoly.symm.toRingHom.comp
        (scaleHom.{u} (M : ℂ)⁻¹).toRingHom) (uliftPoly.symm.bijective.comp
          (bijective_scaleHom.{u} (inv_ne_zero hM'))) (het Γ(V.obj.left, U))
    haveI := etale_restrictι_comp_toAffineSpace s hs f hfet
    let j := (analytificationRestrictIso V U).hom ≫
      (analytification.obj V).ofRestrict (analytificationPreimage V U)
    haveI : IsLocalIso j := by
      haveI := isLocalIso_of_isIso (analytificationRestrictIso V U).hom
      infer_instance
    haveI : IsLocalIso (j ≫ SchemeLFTℂ.anToAffine s hs) := by
      have e2 : j ≫ SchemeLFTℂ.anToAffine s hs =
          analytification.map (V.restrictι U ≫ SchemeLFTℂ.toAffineSpace s hs) ≫
            (analytificationAffineSpaceIso.{u} 1).hom := by
        rw [Functor.map_comp, analytification_map_restrictι]
        simp only [j, Category.assoc]
      rw [e2]
      haveI := isLocalIso_analytification_map_of_etale
        (V.restrictι U ≫ SchemeLFTℂ.toAffineSpace s hs)
      haveI := isLocalIso_of_isIso (analytificationAffineSpaceIso.{u} 1).hom
      infer_instance
    refine isLocalIso_restrictHom_of_subset_range j _ outerOpens fun v hv ↦ ?_
    have hvU : v ∈ analytificationPreimage V U := by
      refine mem_basicOpen_of_evalPoint_ne_zero V v f ?_
      rw [hsf, evalPoint_eq_affineEval s hs, affineEval_scaleHom_uliftPoly]
      refine hM _ ?_
      have hv' : 1 < ‖ProjectiveLine.coord ((SchemeLFTℂ.anToAffine s hs).toLRSHom.base v)‖ := hv
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hM0.le]
      nlinarith
    refine ⟨(analytificationRestrictIso V U).inv.toLRSHom.base ⟨v, hvU⟩, ?_⟩
    change ((analytificationRestrictIso V U).inv ≫ j).toLRSHom.base ⟨v, hvU⟩ = v
    rw [Iso.inv_hom_id_assoc]
    rfl

end Curve

section Cover

variable {V : SchemeLFTℂ.{u}} [IsAffine V.obj.left]
  {s : MvPolynomial (Fin 1) (ULift.{u} ℂ) →+* Γ(V.obj.left, ⊤)}
  {hs : s.comp MvPolynomial.C = V.constMap} [IsFinite (SchemeLFTℂ.toAffineSpace s hs).hom.left]
  (W : AnalyticSpace.FiniteEtaleOver (analytification.obj V))

omit [IsAffine V.obj.left] in
/-- The composite of a finite étale cover of `V^an` with `q^an : V^an ⟶ ℂ¹` is finite. -/
theorem isFinite_comp_anToAffine :
    AnalyticSpace.IsFinite (W.hom ≫ SchemeLFTℂ.anToAffine s hs) := by
  haveI : IsFiniteEtale W.hom := W.prop
  haveI := isFinite_analytification_map_of_isFinite (SchemeLFTℂ.toAffineSpace s hs)
  haveI := isFinite_of_isIso (analytificationAffineSpaceIso.{u} 1).hom
  haveI : AnalyticSpace.IsFinite (SchemeLFTℂ.anToAffine s hs) :=
    isFinite_comp _ _
  exact @isFinite_comp _ _ _ W.hom (SchemeLFTℂ.anToAffine s hs) inferInstance this

/-- **The pushforward of `𝒪_W` to `ℂ¹` is coherent**, for a finite étale cover `W` of `V^an`
with Hausdorff source. -/
theorem isCoherent_pushUnit_comp_anToAffine [T2Space W.left] :
    (LocallyRingedSpace.Hom.pushUnit (W.hom ≫ SchemeLFTℂ.anToAffine s hs).toLRSHom).IsCoherent := by
  haveI : IsAffine (affineSpace.{u} 1).obj.left := inferInstanceAs (IsAffine (Spec _))
  have hK := @isCoherent_pushforward_pushUnit_of_isFiniteEtale V (affineSpace.{u} 1) _ _
    (SchemeLFTℂ.toAffineSpace s hs) _ W.left W.hom W.prop _
  haveI : IsIso (analytificationAffineSpaceIso.{u} 1).hom.toLRSHom :=
    (forgetToLocallyRingedSpace.{u}.mapIso (analytificationAffineSpaceIso.{u} 1)).isIso_hom
  exact @LocallyRingedSpace.isCoherent_pushforward_of_isIso _ _
    (analytificationAffineSpaceIso.{u} 1).hom.toLRSHom inferInstance _ hK

end Cover

end

end ComplexAnalytic
