/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.ES.CodimTwoAlgebra
import Oka.Analytification.RET.ES.FinitePushforwardStalk
import Oka.Analytification.RET.ES.AffineSpaceHartogs
import Mathlib.RingTheory.NoetherNormalization

/-!
# Hartogs extension on normal affine varieties

Let `X` be an affine scheme of finite type over `ℂ` whose ring of functions `A` is an integrally
closed domain, and `U ⊆ X` an open whose complement has codimension at least two. Then `X^an` has
Hartogs extension across the complement of `U^an`
(`ComplexAnalytic.hasHartogsExtension_of_isDomain`).

## Proof

Choose a Noether normalisation `P = ℂ[x₁, …, x_N] ⊆ A`, giving a finite morphism `q : X ⟶ 𝔸^N`.
Every prime of `P` containing the contraction of the ideal of `X ∖ U` has height at least two,
so this contraction contains `p₁, p₂` with no common prime of height at most one
(`exists_pair_of_forall_two_le_height`). Then `[p₁, p₂]` is weakly regular on `P` and, by going
down, on `A` (`isWeaklyRegular_pair_of_forall_height_le_one`). On `(𝔸^N)^an`, the coherent sheaf
`q^an_* 𝒪_{X^an}` has separating functionals from the trace embedding of `A` into `P^r`, and depth
two along `{p₁ = p₂ = 0}` by flatness; functions extend across `{p₁ = p₂ = 0}`
(`ComplexAnalytic.hasHartogsExtension_analytification_affineSpace`). Hartogs extension for
modules (`ComplexAnalytic.AnalyticSpace.bijective_restrict_of_separatingFunctionals`) extends
sections of `q^an_* 𝒪_{X^an}`, and since `q^an` is finite this gives Hartogs extension on `X^an`
across the complement of `q⁻¹{p₁ = p₂ = 0}`, which contains the complement of `U^an`.
-/

open CategoryTheory Opposite AlgebraicGeometry RingTheory.Sequence

universe u

namespace ComplexAnalytic

open AnalyticSpace

noncomputable section

/-- **Noether normalisation of an affine scheme of finite type over `ℂ`**, compatibly with the
structure map from `ℂ`. -/
lemma SchemeLFTℂ.exists_noetherNormalization (X : SchemeLFTℂ.{u}) [IsAffine X.obj.left]
    [Nontrivial Γ(X.obj.left, ⊤)] :
    ∃ (N : ℕ) (g : MvPolynomial (Fin N) (ULift.{u} ℂ) →+* Γ(X.obj.left, ⊤)),
      Function.Injective g ∧ g.Finite ∧ g.comp MvPolynomial.C = X.constMap := by
  obtain ⟨n, s, hsurj, hs⟩ := X.exists_surjective
  letI := X.constMap.toAlgebra
  let s' : MvPolynomial (Fin n) (ULift.{u} ℂ) →ₐ[ULift.{u} ℂ] Γ(X.obj.left, ⊤) :=
    { s with commutes' := fun c ↦ congrArg (fun φ : ULift.{u} ℂ →+* _ ↦ φ c) hs }
  haveI : Algebra.FiniteType (ULift.{u} ℂ) Γ(X.obj.left, ⊤) :=
    Algebra.FiniteType.iff_quotient_mvPolynomial''.2 ⟨n, s', hsurj⟩
  obtain ⟨N, g, hginj, hgfin⟩ := exists_finite_inj_algHom_of_fg (ULift.{u} ℂ) Γ(X.obj.left, ⊤)
  exact ⟨N, g.toRingHom, hginj, hgfin, RingHom.ext fun c ↦ g.commutes c⟩

/-- The value of `(p ∘ q)^an` at `x ∈ X^an` for a polynomial `p` and `q : X ⟶ 𝔸^N`. -/
lemma eval_toAffineSpace {X : SchemeLFTℂ.{u}} {N : ℕ}
    {g : MvPolynomial (Fin N) (ULift.{u} ℂ) →+* Γ(X.obj.left, ⊤)}
    (hg : g.comp MvPolynomial.C = X.constMap)
    (p : MvPolynomial (Fin N) (ULift.{u} ℂ)) (x : analytification.obj X) :
    (analytification.obj (affineSpace.{u} N)).eval (U := ⊤)
        ((analytification.map (SchemeLFTℂ.toAffineSpace g hg)).toLRSHom.base x) trivial
        (analytificationΓ (affineSpace.{u} N) ((Scheme.ΓSpecIso (.of _)).inv p)) =
      evalPoint X x (g p) := by
  refine (eval_c_app (analytification.map (SchemeLFTℂ.toAffineSpace g hg)).toLRSHom
    (analytification.map (SchemeLFTℂ.toAffineSpace g hg)).isCLinear (U := ⊤) x trivial _).symm.trans
    ?_
  refine (congrArg (fun s ↦ (analytification.obj X).eval (U := ⊤) x trivial s)
    ((analytificationΓ_naturality (SchemeLFTℂ.toAffineSpace g hg) _).symm.trans
      (congrArg _ (SchemeLFTℂ.toAffineSpace_appTop g hg p)))).trans ?_
  rfl

/-- **Hartogs extension on normal affine varieties.** Let `X` be an affine scheme of finite type
over `ℂ` whose ring of functions is an integrally closed domain and `U ⊆ X` an open whose
complement has codimension at least two. Then `X^an` has Hartogs extension across the complement
of `U^an`. -/
theorem hasHartogsExtension_of_isDomain (X : SchemeLFTℂ.{u}) [IsAffine X.obj.left]
    [IsDomain Γ(X.obj.left, ⊤)] [IsIntegrallyClosed Γ(X.obj.left, ⊤)]
    (U : X.obj.left.Opens) (hU : HasCodimTwoComplement U) :
    HasHartogsExtension (analytification.obj X)
      (analytificationOpenImmersionPreimage (X.restrictι U)) := by
  haveI := isNoetherianRing_of_isAffine X
  haveI : CharZero (ULift.{u} ℂ) := (ULift.ringEquiv (R := ℂ)).toRingHom.charZero
  obtain ⟨N, g, hginj, hgfin, hg⟩ := X.exists_noetherNormalization
  letI : Algebra (MvPolynomial (Fin N) (ULift.{u} ℂ)) Γ(X.obj.left, ⊤) := g.toAlgebra
  haveI : Module.Finite (MvPolynomial (Fin N) (ULift.{u} ℂ)) Γ(X.obj.left, ⊤) := hgfin
  obtain ⟨p₁, hp₁, p₂, hp₂, hP, hA⟩ := exists_isWeaklyRegular_pair_of_isIntegral
    (R := MvPolynomial (Fin N) (ULift.{u} ℂ)) hginj
    (complIdeal U) (fun P _ hP ↦ two_le_height_of_complIdeal_le hU P hP)
  let q := SchemeLFTℂ.toAffineSpace g hg
  haveI : AlgebraicGeometry.IsFinite q.hom.left := by
    haveI : AlgebraicGeometry.IsFinite (Spec.map (CommRingCat.ofHom g)) := by
      rw [AlgebraicGeometry.IsFinite.SpecMap_iff]
      exact hgfin
    change AlgebraicGeometry.IsFinite (X.obj.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom g))
    infer_instance
  haveI : IsAffine (affineSpace.{u} N).obj.left :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of (MvPolynomial (Fin N) (ULift.{u} ℂ)))))
  let ι : MvPolynomial (Fin N) (ULift.{u} ℂ) ≃+* Γ((affineSpace.{u} N).obj.left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin N) (ULift.{u} ℂ)))
      ).commRingCatIsoToRingEquiv.symm
  have happ : ∀ p, q.hom.left.appTop (ι p) = g p := SchemeLFTℂ.toAffineSpace_appTop g hg
  letI := q.hom.left.appTop.hom.toAlgebra
  -- the pair is weakly regular on `A` over `Γ(𝔸^N)`
  have hA' : IsWeaklyRegular Γ(X.obj.left, ⊤) [ι p₁, ι p₂] := by
    refine (isWeaklyRegular_map_algebraMap_iff (R := Γ((affineSpace.{u} N).obj.left, ⊤))
      (S := Γ(X.obj.left, ⊤)) (M := Γ(X.obj.left, ⊤)) [ι p₁, ι p₂]).1 ?_
    simp only [List.map_cons, List.map_nil]
    exact (congrArg₂ (fun a b ↦ IsWeaklyRegular Γ(X.obj.left, ⊤) [a, b]) (happ p₁)
      (happ p₂)).mpr hA
  -- generators and the trace embedding over `Γ(𝔸^N)`
  obtain ⟨m, b, hb⟩ := Module.Finite.exists_fin (R := MvPolynomial (Fin N) (ULift.{u} ℂ))
    (M := Γ(X.obj.left, ⊤))
  have hb' : Submodule.span Γ((affineSpace.{u} N).obj.left, ⊤) (Set.range b) = ⊤ := by
    refine eq_top_iff.2 fun x _ ↦ ?_
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1
      (hb ▸ Submodule.mem_top : x ∈ Submodule.span (MvPolynomial (Fin N) (ULift.{u} ℂ))
        (Set.range b))
    refine (Submodule.mem_span_range_iff_exists_fun _).2 ⟨fun i ↦ ι (c i), ?_⟩
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    change q.hom.left.appTop (ι (c i)) * b i = g (c i) * b i
    rw [happ]
  obtain ⟨r, ℓ₀, hℓ₀⟩ := exists_injective_linearMap_pi_of_finite
    (MvPolynomial (Fin N) (ULift.{u} ℂ)) Γ(X.obj.left, ⊤) hginj
  let ℓ : Γ(X.obj.left, ⊤) →ₗ[Γ((affineSpace.{u} N).obj.left, ⊤)]
      (Fin r → Γ((affineSpace.{u} N).obj.left, ⊤)) :=
    { toFun := fun x k ↦ ι (ℓ₀ x k)
      map_add' := fun x y ↦ funext fun k ↦ by simp
      map_smul' := fun a x ↦ funext fun k ↦ by
        have e : a • x = ι.symm a • x := by
          change q.hom.left.appTop a * x = g (ι.symm a) * x
          rw [← happ, RingEquiv.apply_symm_apply]
        simp only [e, LinearMap.map_smul, Pi.smul_apply, smul_eq_mul, map_mul,
          RingEquiv.apply_symm_apply, RingHom.id_apply] }
  have hℓ : Function.Injective ℓ := fun x y hxy ↦ hℓ₀ (funext fun k ↦
    ι.injective (congrFun hxy k))
  -- Hartogs extension for `q^an_* 𝒪` on `(𝔸^N)^an`
  let G := analytificationΓ (affineSpace.{u} N) (ι p₁)
  let H := analytificationΓ (affineSpace.{u} N) (ι p₂)
  have hstalk := fun z ↦ isWeaklyRegular_analytificationStalk (affineSpace.{u} N) z
    (hP.map_ringEquiv ι)
  haveI := isCoherent_pushUnit_analytification_map q
  have hmod := bijective_restrict_of_separatingFunctionals
    (M := LocallyRingedSpace.Hom.pushUnit (analytification.map q).toLRSHom)
    (separatingFunctionalsAnalytificationMap q b hb' ℓ hℓ)
    (T := {z | (analytification.obj (affineSpace.{u} N)).eval (U := ⊤) z trivial G = 0 ∧
      (analytification.obj (affineSpace.{u} N)).eval (U := ⊤) z trivial H = 0})
    (fun _ _ ↦ trivial) (nonvanishingOpens _ G H) rfl G H (fun _ _ hz ↦ hz.1)
    (fun _ _ hz ↦ hz.2)
    (fun z _ ↦ ((isWeaklyRegular_cons_iff _ _ _).1 (hstalk z)).1)
    (fun z _ ↦ isWeaklyRegular_stalk_pushUnit_analytification_map q z hA')
    (fun V _ ↦ (hasHartogsExtension_analytification_affineSpace hP V).2)
  haveI := t2Space_analytification_of_isAffine X
  haveI := isFinite_analytification_map_of_isFinite q
  refine (hasHartogsExtension_of_isFinite (analytification.map q) (nonvanishingOpens _ G H) fun V ↦
    bijective_presheaf_map_of_eq _ (by ext; rfl) _ _ (hmod V)).mono ?_
  -- `q⁻¹{p₁ = p₂ = 0}` contains the complement of `U^an`
  intro x hx
  by_contra hxU
  have hxU' : (analytificationπLRS X).base x ∉ U := fun h ↦ hxU (by
    change (analytificationπLRS X).base x ∈ Set.range U.ι.base
    rw [mem_range_opens_ι_base]
    exact h)
  have key : ∀ p ∈ (complIdeal U).comap (algebraMap (MvPolynomial (Fin N) (ULift.{u} ℂ))
      Γ(X.obj.left, ⊤)), (analytification.obj (affineSpace.{u} N)).eval (U := ⊤)
        ((analytification.map q).toLRSHom.base x) trivial
        (analytificationΓ (affineSpace.{u} N) (ι p)) = 0 := fun p hp ↦ by
    refine (eval_toAffineSpace hg p x).trans ?_
    have h1 := (mem_complIdeal_iff U _).1 (Ideal.mem_comap.1 hp) _ hxU'
    rw [← idealOfPoint_eq_pointIdeal, ← ker_evalPoint] at h1
    exact h1
  exact hx ⟨key p₁ hp₁, key p₂ hp₂⟩

end

end ComplexAnalytic
