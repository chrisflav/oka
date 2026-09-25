/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.ES.CurveSetup
import Oka.Analytification.RET.ES.BoundedSections
import Oka.Analytification.GAGA.StalkFlat

/-!
# A generically étale Noether normalisation

Let `V` be an affine integral scheme of finite type over `ℂ` of dimension `n`. There is a finite
morphism `q : V ⟶ 𝔸ⁿ` given by `n` global functions and a nonzero polynomial `e` such that `q^an`
is a local isomorphism over `{e ≠ 0}` (`ComplexAnalytic.exists_smoothCoordinate`): by Noether
normalisation `Γ(V, 𝒪_V)` is finite over `ℂ[z₁, …, zₙ]`, and by generic étaleness it is étale
over `ℂ[z₁, …, zₙ]` after inverting `e`.

If `V^an` is locally isomorphic to opens of affine spaces, then so is every space with a local
isomorphism to `V^an` (`ComplexAnalytic.AnalyticSpace.IsLocallyOpenInAffine.of_isLocalIso`), and
the zero set of a nonzero function on `V` has empty interior in such a space
(`ComplexAnalytic.interior_setOf_evalPoint_eq_zero`).
-/

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry Topology

universe u

namespace ComplexAnalytic

open AnalyticSpace

noncomputable section

section Dimension

/-- **Noether normalisation**: a ring of finite type and of dimension `n` over a field `k` is
finite over a polynomial ring in `n` variables. -/
theorem exists_finite_injective_of_ringKrullDim_eq {k A : Type*} [Field k] [CommRing A]
    [Algebra k A] [Algebra.FiniteType k A] {n : ℕ} (hdim : ringKrullDim A = n) :
    ∃ g : MvPolynomial (Fin n) k →ₐ[k] A, Function.Injective g ∧ g.Finite := by
  haveI : Nontrivial A := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    rw [ringKrullDim_eq_bot_of_subsingleton] at hdim
    exact WithBot.bot_ne_coe hdim
  obtain ⟨s, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg k A
  letI := g.toRingHom.toAlgebra
  haveI : Module.Finite (MvPolynomial (Fin s) k) A := hfin
  have hdimP : ringKrullDim (MvPolynomial (Fin s) k) = s := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field,
      Nat.card_eq_fintype_card, Fintype.card_fin, zero_add]
  have h1 := ringKrullDim_le_of_isIntegral (R := MvPolynomial (Fin s) k) (S := A)
  have h2 := ringKrullDim_le_of_isIntegral_of_injective (R := MvPolynomial (Fin s) k) (S := A)
    hinj
  rw [hdim, hdimP] at h1 h2
  obtain rfl : s = n := by exact_mod_cast le_antisymm h2 h1
  exact ⟨g, hinj, hfin⟩

end Dimension

section Polynomial

variable {n : ℕ}

/-- Polynomials over `ℂ` as polynomials over `ULift ℂ`. -/
abbrev uliftPolyN (n : ℕ) : MvPolynomial (Fin n) ℂ ≃+* MvPolynomial (Fin n) (ULift.{u} ℂ) :=
  MvPolynomial.mapEquiv (Fin n) ULift.ringEquiv.symm

/-- The value of a polynomial at a point of `ℂⁿ`. -/
def polyEval (e : MvPolynomial (Fin n) ℂ) (z : AnalyticSpace.complexAffineSpace.{u} n) : ℂ :=
  MvPolynomial.eval (projectiveSpaceAn.toFin z) e

lemma affineEval_uliftPolyN (e : MvPolynomial (Fin n) ℂ)
    (z : AnalyticSpace.complexAffineSpace.{u} n) :
    affineEval n z (uliftPolyN n e) = polyEval e z := by
  have : (affineEval n z).comp (uliftPolyN.{u} n).toRingHom =
      MvPolynomial.eval (projectiveSpaceAn.toFin z) := by
    refine MvPolynomial.ringHom_ext (fun a ↦ ?_) fun i ↦ ?_
    · simp [affineEval]
    · simp [affineEval]
      rfl
  exact RingHom.congr_fun this e

lemma continuous_polyEval (e : MvPolynomial (Fin n) ℂ) : Continuous (polyEval.{u} e) :=
  (MvPolynomial.continuous_eval e).comp (continuous_pi fun m ↦ continuous_apply (ULift.up m))

/-- The open `{e ≠ 0}` of `ℂⁿ`. -/
def polyOpens (e : MvPolynomial (Fin n) ℂ) : (AnalyticSpace.complexAffineSpace.{u} n).Opens :=
  ⟨{z | polyEval e z ≠ 0}, isOpen_compl_singleton.preimage (continuous_polyEval e)⟩

lemma mem_polyOpens_iff (e : MvPolynomial (Fin n) ℂ)
    (z : AnalyticSpace.complexAffineSpace.{u} n) : z ∈ polyOpens e ↔ polyEval e z ≠ 0 :=
  Iff.rfl

end Polynomial

section Coordinate

/-- **A generically étale Noether normalisation.** For an affine integral scheme `V` of finite type
over `ℂ` of dimension `n` there is a finite morphism `q : V ⟶ 𝔸ⁿ`, given by `n` global functions,
and a nonzero polynomial `e` such that `q^an : V^an ⟶ ℂⁿ` is a local isomorphism over
`{e ≠ 0}`. -/
theorem exists_smoothCoordinate (V : SchemeLFTℂ.{u}) [IsAffine V.obj.left] [IsIntegral V.obj.left]
    {n : ℕ} (hdim : ringKrullDim Γ(V.obj.left, ⊤) = n) :
    ∃ (s : MvPolynomial (Fin n) (ULift.{u} ℂ) →+* Γ(V.obj.left, ⊤))
      (hs : s.comp MvPolynomial.C = V.constMap) (e : MvPolynomial (Fin n) ℂ),
      s.Finite ∧ Function.Injective s ∧ e ≠ 0 ∧
        IsLocalIso (AnalyticSpace.restrictHom (SchemeLFTℂ.anToAffine s hs) (polyOpens e)) := by
  classical
  letI : Algebra (ULift.{u} ℂ) Γ(V.obj.left, ⊤) := V.constMap.toAlgebra
  obtain ⟨N, s₀, hs₀surj, hs₀⟩ := V.exists_surjective
  haveI : Algebra.FiniteType (ULift.{u} ℂ) Γ(V.obj.left, ⊤) :=
    Algebra.FiniteType.of_surjective (R := ULift.{u} ℂ)
      { s₀ with commutes' := fun c ↦ RingHom.congr_fun hs₀ c } hs₀surj
  obtain ⟨g₀, hg₀inj, hg₀fin⟩ := exists_finite_injective_of_ringKrullDim_eq
    (k := ULift.{u} ℂ) (A := Γ(V.obj.left, ⊤)) hdim
  letI : Algebra (MvPolynomial (Fin n) ℂ) Γ(V.obj.left, ⊤) :=
    (g₀.toRingHom.comp (uliftPolyN n).toRingHom).toAlgebra
  haveI : Module.Finite (MvPolynomial (Fin n) ℂ) Γ(V.obj.left, ⊤) :=
    RingHom.Finite.comp hg₀fin (RingHom.Finite.of_surjective _ (uliftPolyN n).surjective)
  haveI : FaithfulSMul (MvPolynomial (Fin n) ℂ) Γ(V.obj.left, ⊤) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (hg₀inj.comp (uliftPolyN n).injective)
  obtain ⟨e, he0, het⟩ := exists_etale_localizationAway.{u, u} (d := n) (A := Γ(V.obj.left, ⊤))
  set f : Γ(V.obj.left, ⊤) := g₀ (uliftPolyN n e)
  set U := V.obj.left.basicOpen f
  haveI : IsLocalization.Away (algebraMap (MvPolynomial (Fin n) ℂ) Γ(V.obj.left, ⊤) e)
      Γ(V.obj.left, U) := (isAffineOpen_top V.obj.left).isLocalization_basicOpen f
  let s : MvPolynomial (Fin n) (ULift.{u} ℂ) →+* Γ(V.obj.left, ⊤) := g₀.toRingHom
  have hs : s.comp MvPolynomial.C = V.constMap := by
    ext c
    simp only [s, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes]
    rfl
  refine ⟨s, hs, e, hg₀fin, hg₀inj, he0, ?_⟩
  have hfet : ((algebraMap Γ(V.obj.left, ⊤) Γ(V.obj.left, U)).comp s).Etale := by
    have e1 : (algebraMap Γ(V.obj.left, ⊤) Γ(V.obj.left, U)).comp s =
        ((algebraMap Γ(V.obj.left, ⊤) Γ(V.obj.left, U)).comp
          (algebraMap (MvPolynomial (Fin n) ℂ) Γ(V.obj.left, ⊤))).comp
          (uliftPolyN.{u} n).symm.toRingHom := by
      refine RingHom.ext fun p ↦ ?_
      change algebraMap Γ(V.obj.left, ⊤) Γ(V.obj.left, U) (g₀ p) =
        algebraMap Γ(V.obj.left, ⊤) Γ(V.obj.left, U) (g₀ (uliftPolyN n ((uliftPolyN n).symm p)))
      rw [RingEquiv.apply_symm_apply]
    rw [e1]
    exact RingHom.Etale.comp_of_bijective (uliftPolyN.{u} n).symm.bijective (het Γ(V.obj.left, U))
  haveI := etale_restrictι_comp_toAffineSpace s hs f hfet
  let j := (analytificationRestrictIso V U).hom ≫
    (analytification.obj V).ofRestrict (analytificationPreimage V U)
  haveI : IsLocalIso j := by
    haveI := isLocalIso_of_isIso (analytificationRestrictIso V U).hom
    infer_instance
  haveI : IsLocalIso (j ≫ SchemeLFTℂ.anToAffine s hs) := by
    have e2 : j ≫ SchemeLFTℂ.anToAffine s hs =
        analytification.map (V.restrictι U ≫ SchemeLFTℂ.toAffineSpace s hs) ≫
          (analytificationAffineSpaceIso.{u} n).hom := by
      rw [Functor.map_comp, analytification_map_restrictι]
      simp only [j, Category.assoc]
    rw [e2]
    haveI := isLocalIso_analytification_map_of_etale
      (V.restrictι U ≫ SchemeLFTℂ.toAffineSpace s hs)
    haveI := isLocalIso_of_isIso (analytificationAffineSpaceIso.{u} n).hom
    infer_instance
  refine isLocalIso_restrictHom_of_subset_range j _ (polyOpens e) fun v hv ↦ ?_
  have hvU : v ∈ analytificationPreimage V U := by
    refine mem_basicOpen_of_evalPoint_ne_zero V v f ?_
    change evalPoint V v (s (uliftPolyN n e)) ≠ 0
    rw [evalPoint_eq_affineEval s hs, affineEval_uliftPolyN]
    exact hv
  refine ⟨(analytificationRestrictIso V U).inv.toLRSHom.base ⟨v, hvU⟩, ?_⟩
  change ((analytificationRestrictIso V U).inv ≫ j).toLRSHom.base ⟨v, hvU⟩ = v
  rw [Iso.inv_hom_id_assoc]
  rfl

end Coordinate

section Cover

variable {V : SchemeLFTℂ.{u}} {n : ℕ} {s : MvPolynomial (Fin n) (ULift.{u} ℂ) →+* Γ(V.obj.left, ⊤)}
  {hs : s.comp MvPolynomial.C = V.constMap}

/-- The composite of a finite étale cover of `V^an` with a finite `q^an : V^an ⟶ ℂⁿ` is finite. -/
theorem isFinite_hom_comp_anToAffine [IsFinite (SchemeLFTℂ.toAffineSpace s hs).hom.left]
    (W : AnalyticSpace.FiniteEtaleOver (analytification.obj V)) :
    AnalyticSpace.IsFinite (W.hom ≫ SchemeLFTℂ.anToAffine s hs) := by
  haveI : IsFiniteEtale W.hom := W.prop
  haveI := isFinite_analytification_map_of_isFinite (SchemeLFTℂ.toAffineSpace s hs)
  haveI := isFinite_of_isIso (analytificationAffineSpaceIso.{u} n).hom
  haveI : AnalyticSpace.IsFinite (SchemeLFTℂ.anToAffine s hs) :=
    isFinite_comp _ _
  exact @isFinite_comp _ _ _ W.hom (SchemeLFTℂ.anToAffine s hs) inferInstance this

/-- The composite of a local isomorphism with `q^an`, restricted over an open over which `q^an` is
a local isomorphism, is a local isomorphism. -/
theorem isLocalIso_restrictHom_comp_anToAffine {W : AnalyticSpace.{u}}
    (p : W ⟶ analytification.obj V) [IsLocalIso p]
    (O : (AnalyticSpace.complexAffineSpace.{u} n).Opens)
    (hloc : IsLocalIso (AnalyticSpace.restrictHom (SchemeLFTℂ.anToAffine s hs) O)) :
    IsLocalIso (AnalyticSpace.restrictHom (p ≫ SchemeLFTℂ.anToAffine s hs) O) := by
  rw [AnalyticSpace.restrictHom_comp]
  haveI := AnalyticSpace.isLocalIso_restrictHom p
    ((Opens.map (SchemeLFTℂ.anToAffine s hs).toLRSHom.base).obj O)
  exact @AnalyticSpace.isLocalIso_comp _ _ _ _ _ this hloc

end Cover

section LocallyAffine

/-- **Spaces locally isomorphic to opens of affine spaces are stable under local
isomorphisms**: if `φ : Z ⟶ X` is a local isomorphism and `X` is locally isomorphic to opens of
affine spaces, then so is `Z`. -/
theorem AnalyticSpace.IsLocallyOpenInAffine.of_isLocalIso {Z X : AnalyticSpace.{u}} (φ : Z ⟶ X)
    [IsLocalIso φ] (hX : IsLocallyOpenInAffine X) : IsLocallyOpenInAffine Z := by
  intro z
  obtain ⟨E, hzE, hE⟩ := IsLocalIso.isLocalHomeomorph (f := φ) z
  let O : Z.Opens := ⟨E.source, E.open_source⟩
  let j := Z.ofRestrict O ≫ φ
  have hjinj : Function.Injective j.toLRSHom.base := by
    intro x y hxy
    change φ.toLRSHom.base x.1 = φ.toLRSHom.base y.1 at hxy
    rw [hE] at hxy
    exact Subtype.ext (E.injOn x.2 y.2 hxy)
  haveI : LocallyRingedSpace.IsOpenImmersion j.toLRSHom :=
    LocallyRingedSpace.IsOpenImmersion.of_stalk_iso _
      ((IsLocalIso.isLocalHomeomorph (f := j)).isOpenEmbedding_of_injective hjinj)
  obtain ⟨m, U, ψ, x, hψ, hx⟩ := hX (φ.toLRSHom.base z)
  haveI := hψ
  let V' : ((complexAffineSpace.{u} m).restrict U).Opens :=
    (Opens.map ψ.toLRSHom.base).obj ⟨Set.range j.toLRSHom.base,
      (IsLocalIso.isLocalHomeomorph (f := j)).isOpenMap.isOpen_range⟩
  have hxV' : x ∈ V' := ⟨⟨z, hzE⟩, hx.symm⟩
  let U'' : (complexAffineSpace.{u} m).Opens := U.isOpenEmbedding.isOpenMap.functor.obj V'
  have hU'' : U'' ≤ U := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  let r := (complexAffineSpace.{u} m).restrictLE hU''
  have hr : ∀ y, (r.toLRSHom.base y).1 = y.1 := coe_base_restrictLE hU''
  have hrV : ∀ y, r.toLRSHom.base y ∈ V' := by
    intro y
    obtain ⟨y', hy', hyy'⟩ := y.2
    have : r.toLRSHom.base y = y' := Subtype.ext ((hr y).trans hyy'.symm)
    rw [this]
    exact hy'
  haveI : IsLocalIso ((complexAffineSpace.{u} m).ofRestrict U) := inferInstance
  haveI : IsLocalIso (r ≫ (complexAffineSpace.{u} m).ofRestrict U) := by
    rw [restrictLE_fac]
    infer_instance
  haveI : IsLocalIso r := isLocalIso_of_comp r ((complexAffineSpace.{u} m).ofRestrict U)
  have hrange : Set.range (r ≫ ψ).toLRSHom.base ⊆ Set.range j.toLRSHom.base := by
    rintro _ ⟨y, rfl⟩
    exact hrV y
  let χ : (complexAffineSpace.{u} m).restrict U'' ⟶ Z.restrict O :=
    ⟨LocallyRingedSpace.IsOpenImmersion.lift j.toLRSHom (r ≫ ψ).toLRSHom hrange,
      IsCLinearHom.of_comp (LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ hrange)
        (r ≫ ψ).isCLinear j.isCLinear⟩
  have hχ : χ ≫ j = r ≫ ψ := forgetToLocallyRingedSpace.map_injective
    (LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ hrange)
  haveI : IsLocalIso j := inferInstance
  haveI : IsLocalIso (χ ≫ j) := by
    rw [hχ]
    infer_instance
  haveI : IsLocalIso χ := isLocalIso_of_comp χ j
  have hxU'' : x.1 ∈ U'' := ⟨x, hxV', rfl⟩
  refine ⟨m, U'', χ ≫ Z.ofRestrict O, ⟨x.1, hxU''⟩, inferInstance, ?_⟩
  have h1 : r.toLRSHom.base ⟨x.1, hxU''⟩ = x := Subtype.ext (hr _)
  have h2 : χ.toLRSHom.base ⟨x.1, hxU''⟩ = ⟨z, hzE⟩ := by
    apply hjinj
    have := congrArg (fun f ↦ f.toLRSHom.base ⟨x.1, hxU''⟩) hχ
    refine this.trans ?_
    change ψ.toLRSHom.base (r.toLRSHom.base ⟨x.1, hxU''⟩) = φ.toLRSHom.base z
    rw [h1, hx]
  change (Z.ofRestrict O).toLRSHom.base (χ.toLRSHom.base ⟨x.1, hxU''⟩) = z
  rw [h2]
  rfl

end LocallyAffine

section ZeroSet

variable (V : SchemeLFTℂ.{u})

lemma eval_analytificationΓ_eq_evalPoint (v : analytification.obj V) (a : Γ(V.obj.left, ⊤)) :
    (analytification.obj V).eval (U := ⊤) v trivial (analytificationΓ V a) = evalPoint V v a :=
  rfl

/-- **The zero set of a nonzero function on an integral scheme has empty interior in the
analytification**, if the analytification is locally isomorphic to opens of affine spaces. -/
theorem interior_setOf_evalPoint_eq_zero [IsIntegral V.obj.left]
    (hV : IsLocallyOpenInAffine (analytification.obj V)) {a : Γ(V.obj.left, ⊤)} (ha : a ≠ 0) :
    interior {v | evalPoint V v a = 0} = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.2 fun v hv ↦ ha ?_
  let O : (analytification.obj V).Opens := ⟨interior {v | evalPoint V v a = 0}, isOpen_interior⟩
  have hvO : v ∈ O := hv
  have h0 : (analytification.obj V).presheaf.map (homOfLE le_top : O ⟶ ⊤).op
      (analytificationΓ V a) = 0 := by
    refine eq_of_forall_eval_eq hV fun y hy ↦ ?_
    rw [eval_presheaf_map, map_zero]
    exact interior_subset (s := {v | evalPoint V v a = 0}) hy
  have hgerm : algebraMap Γ(V.obj.left, ⊤) ((analytification.obj V).presheaf.stalk v) a = 0 := by
    change (analytification.obj V).presheaf.germ ⊤ v trivial (analytificationΓ V a) = 0
    rw [← (analytification.obj V).presheaf.germ_res_apply (homOfLE le_top : O ⟶ ⊤) v hvO, h0,
      map_zero]
  have hinj := RingHom.FaithfullyFlat.injective
    (faithfullyFlat_stalkMap_analytificationπ V v)
  have h1 : algebraMap Γ(V.obj.left, ⊤) ((analytification.obj V).presheaf.stalk v) a =
      ((analytificationπLRS V).stalkMap v).hom
        (V.obj.left.presheaf.germ ⊤ ((analytificationπLRS V).base v) trivial a) :=
    (LocallyRingedSpace.stalkMap_germ_apply (analytificationπLRS V) ⊤ v trivial a).symm
  rw [h1] at hgerm
  have h2 : V.obj.left.presheaf.germ ⊤ ((analytificationπLRS V).base v) trivial a = 0 :=
    hinj (hgerm.trans (map_zero _).symm)
  exact germ_injective_of_isIntegral V.obj.left (U := ⊤) _ trivial (h2.trans (map_zero _).symm)

/-- **The preimage under a local isomorphism of a set with empty interior has empty
interior.** -/
theorem interior_preimage_eq_empty_of_isLocalIso {Z X : AnalyticSpace.{u}} (φ : Z ⟶ X)
    [IsLocalIso φ] {S : Set X} (hS : interior S = ∅) :
    interior (φ.toLRSHom.base ⁻¹' S) = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.2 fun z hz ↦ ?_
  have hopen : IsOpen (φ.toLRSHom.base '' interior (φ.toLRSHom.base ⁻¹' S)) :=
    (IsLocalIso.isLocalHomeomorph (f := φ)).isOpenMap _ isOpen_interior
  have hsub : φ.toLRSHom.base '' interior (φ.toLRSHom.base ⁻¹' S) ⊆ S := by
    rintro _ ⟨y, hy, rfl⟩
    exact interior_subset (s := φ.toLRSHom.base ⁻¹' S) hy
  have := interior_maximal hsub hopen ⟨z, hz, rfl⟩
  rw [hS] at this
  exact this

end ZeroSet

end

end ComplexAnalytic
