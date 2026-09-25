/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.ES.NormalHartogsDomain
import Oka.RingTheory.FiniteNormalization

/-!
# Hartogs extension on normal affine schemes

Let `X` be an affine scheme of finite type over `ℂ` whose ring of functions is a finite product of
integrally closed domains, and `U ⊆ X` an open whose complement has codimension at least two. Then
`X^an` has Hartogs extension across the complement of `U^an`
(`ComplexAnalytic.normalHartogs`). The factors of `Γ(X, 𝒪_X)` are the rings of functions of the
basic opens of the corresponding idempotents, which cover `X`; on each of them this is
`ComplexAnalytic.hasHartogsExtension_of_isDomain`, and Hartogs extension descends along open
immersions (`ComplexAnalytic.AnalyticSpace.bijective_res_of_isOpenImmersion`). Hence
`ComplexAnalytic.mem_essImage_of_restrict` only needs `ComplexAnalytic.NormalizationInCover`
(`ComplexAnalytic.mem_essImage_of_restrict_of_normalizationInCover`).
-/

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

universe u

namespace ComplexAnalytic

namespace AnalyticSpace

/-- **Hartogs extension descends along open immersions**: if `W` has Hartogs extension across
`j⁻¹ O`, restriction `𝒪(Ω) → 𝒪(Ω ∩ O)` is bijective for opens `Ω` inside the image of `j`. -/
theorem bijective_res_of_isOpenImmersion {W Z : AnalyticSpace.{u}} (j : W ⟶ Z)
    [LocallyRingedSpace.IsOpenImmersion j.toLRSHom] (O : Z.Opens)
    (hW : HasHartogsExtension W ((Opens.map j.toLRSHom.base).obj O)) (Ω : Z.Opens)
    (hΩ : (Ω : Set Z) ⊆ Set.range j.toLRSHom.base) :
    Function.Bijective (Z.res (inf_le_left : Ω ⊓ O ≤ Ω)) := by
  haveI := PresheafedSpace.IsOpenImmersion.isIso_of_subset j.toLRSHom.toHom Ω hΩ
  haveI := PresheafedSpace.IsOpenImmersion.isIso_of_subset j.toLRSHom.toHom (Ω ⊓ O)
    fun _ hx ↦ hΩ hx.1
  have hb₁ := ConcreteCategory.bijective_of_isIso (j.toLRSHom.c.app (op Ω))
  have hb₂ := ConcreteCategory.bijective_of_isIso (j.toLRSHom.c.app (op (Ω ⊓ O)))
  have e : ⇑(j.toLRSHom.c.app (op (Ω ⊓ O))) ∘ Z.res (inf_le_left : Ω ⊓ O ≤ Ω) =
      W.res (inf_le_left : (Opens.map j.toLRSHom.base).obj Ω ⊓
        (Opens.map j.toLRSHom.base).obj O ≤ (Opens.map j.toLRSHom.base).obj Ω) ∘
        j.toLRSHom.c.app (op Ω) :=
    funext fun s ↦ ConcreteCategory.congr_hom
      (j.toLRSHom.c.naturality (homOfLE (inf_le_left : Ω ⊓ O ≤ Ω)).op) s
  refine (Function.Bijective.of_comp_iff' hb₂ _).1 ?_
  rw [e]
  exact (hW _).comp hb₁

end AnalyticSpace

open AnalyticSpace

/-- **The factors of a finite product of normal domains as basic opens**: every point of an affine
scheme whose ring of functions is a finite product of integrally closed domains lies in a basic
open whose ring of functions is an integrally closed domain. -/
lemma exists_basicOpen_isDomain {X : Scheme.{u}} [IsAffine X]
    (hX : IsFiniteProductOfNormalDomains Γ(X, ⊤)) (x : X) :
    ∃ f : Γ(X, ⊤), x ∈ X.basicOpen f ∧ IsDomain Γ(X.basicOpen f, ⊤) ∧
      IsIntegrallyClosed Γ(X.basicOpen f, ⊤) := by
  classical
  obtain ⟨ι, hι, D, _, _, _, ⟨e⟩⟩ := hX
  haveI := Fintype.ofFinite ι
  obtain ⟨i, hi⟩ : ∃ i, e.symm (Pi.single i 1) ∉ pointIdeal x := by
    by_contra! h
    have h1 : (1 : Γ(X, ⊤)) ∈ pointIdeal x := by
      have : (1 : Γ(X, ⊤)) = ∑ i, e.symm (Pi.single i 1) := by
        rw [← map_sum, Finset.univ_sum_single]
        exact (map_one e.symm).symm
      rw [this]
      exact Ideal.sum_mem _ fun i _ ↦ h i
    exact (pointIdeal x).ne_top_iff_one.1 Ideal.IsPrime.ne_top' h1
  set f := e.symm (Pi.single i 1) with hf
  have hx : x ∈ X.basicOpen f := by
    by_contra h
    exact hi ((mem_pointIdeal_iff x f).2 h)
  letI : Algebra Γ(X, ⊤) (D i) := ((Pi.evalRingHom D i).comp e.toRingHom).toAlgebra
  have hsingle : ∀ a : Γ(X, ⊤), e (f * a) = Pi.single i (e a i) := fun a ↦ by
    rw [map_mul, hf, RingEquiv.apply_symm_apply]
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj]
  have hloc : IsLocalization.Away f (D i) := by
    refine IsLocalization.away_of_isIdempotentElem_of_mul (S := D i) ?_ (fun a b ↦ ?_) ?_
    · change f * f = f
      refine e.injective ?_
      rw [hsingle, hf, RingEquiv.apply_symm_apply, Pi.single_eq_same]
    · change e a i = e b i ↔ _
      rw [← e.injective.eq_iff, hsingle, hsingle]
      exact ⟨fun h ↦ by rw [h], fun h ↦ by simpa using congrFun h i⟩
    · intro d
      exact ⟨e.symm (Pi.single i d), by
        change e (e.symm _) i = d
        rw [RingEquiv.apply_symm_apply, Pi.single_eq_same]⟩
  let φ : Γ(X.basicOpen f, ⊤) ≃+* D i :=
    (X.basicOpen f).topIso.commRingCatIsoToRingEquiv.trans
      (IsLocalization.algEquiv (Submonoid.powers f) Γ(X, X.basicOpen f) (D i)).toRingEquiv
  exact ⟨f, hx, φ.toMulEquiv.isDomain (D i), IsIntegrallyClosed.of_equiv φ.symm⟩

/-- A complement of codimension at least two stays so in an open subscheme. -/
lemma HasCodimTwoComplement.preimage_ι {X : Scheme.{u}} {U : X.Opens}
    (hU : HasCodimTwoComplement U) (V : X.Opens) : HasCodimTwoComplement (V.ι ⁻¹ᵁ U) := by
  intro y hy
  rw [ringKrullDim_eq_of_ringEquiv (V.stalkIso y).commRingCatIsoToRingEquiv]
  exact hU y.1 hy

/-- **Hartogs extension on normal affine schemes.** Let `X` be an affine scheme of finite type
over `ℂ` whose ring of functions is a finite product of integrally closed domains and `U ⊆ X` an
open whose complement has codimension at least two. Then `X^an` has Hartogs extension across the
complement of `U^an`. -/
theorem hasHartogsExtension_of_isFiniteProductOfNormalDomains (X : SchemeLFTℂ.{u})
    [IsAffine X.obj.left] (hX : IsFiniteProductOfNormalDomains Γ(X.obj.left, ⊤))
    (U : X.obj.left.Opens) (hU : HasCodimTwoComplement U) :
    HasHartogsExtension (analytification.obj X)
      (analytificationOpenImmersionPreimage (X.restrictι U)) := by
  refine hasHartogsExtension_of_local fun Ω x hx ↦ ?_
  obtain ⟨f, hxf, hdom, hnorm⟩ := exists_basicOpen_isDomain hX ((analytificationπLRS X).base x)
  let V := X.obj.left.basicOpen f
  haveI : IsAffine (X.restrict V).obj.left := (isAffineOpen_top X.obj.left).basicOpen f
  haveI : IsDomain Γ((X.restrict V).obj.left, ⊤) := hdom
  haveI : IsIntegrallyClosed Γ((X.restrict V).obj.left, ⊤) := hnorm
  refine ⟨Ω ⊓ analytificationOpenImmersionPreimage (X.restrictι V), inf_le_left, ⟨hx, ?_⟩, ?_⟩
  · change (analytificationπLRS X).base x ∈ Set.range V.ι.base
    rw [mem_range_opens_ι_base]
    exact hxf
  refine bijective_res_of_isOpenImmersion (analytification.map (X.restrictι V)) _ ?_ _ ?_
  · rw [← analytificationOpenImmersionPreimage_restrictι_preimage]
    exact hasHartogsExtension_of_isDomain _ _ (hU.preimage_ι V)
  · rw [range_analytification_map]
    exact fun _ h ↦ h.2

/-- **`ComplexAnalytic.NormalHartogs` holds.** -/
theorem normalHartogs : NormalHartogs.{u} :=
  fun X _ hX U hU ↦ hasHartogsExtension_of_isFiniteProductOfNormalDomains X hX U hU

/-- **Essential surjectivity from a big open of a normal affine scheme**, assuming
`ComplexAnalytic.NormalizationInCover`: if the restriction of a Hausdorff finite étale cover `W`
of `X^an` to `U^an` is algebraic, so is `W`. -/
theorem mem_essImage_of_restrict_of_normalizationInCover (hN : NormalizationInCover.{u})
    (X : SchemeLFTℂ.{u}) [IsAffine X.obj.left]
    (hX : IsFiniteProductOfNormalDomains Γ(X.obj.left, ⊤))
    (U : X.obj.left.Opens) (hU : HasCodimTwoComplement U)
    (W : AnalyticSpace.FiniteEtaleOver (analytification.obj X)) [T2Space W.left]
    (hW : (analytificationFiniteEtaleOver (X.restrict U)).essImage (restrictFiniteEtaleOver W U)) :
    (analytificationFiniteEtaleOver X).essImage W :=
  mem_essImage_of_restrict normalHartogs hN X hX U hU W hW

end ComplexAnalytic
