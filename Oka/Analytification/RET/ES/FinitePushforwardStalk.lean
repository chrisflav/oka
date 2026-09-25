/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.ES.FiniteCoherent
import Oka.Analytification.RET.ES.AnalyticStalkFlat
import Oka.AnalyticSpace.PushUnitFunctionals
import Oka.RingTheory.TraceEmbedding
import Oka.RingTheory.NormalDepthTwo

/-!
# Stalks of `q^an_* 𝒪` for finite morphisms of affine schemes

Let `q : Y ⟶ S` be a finite morphism of affine schemes of finite type over `ℂ`, `A = Γ(S, 𝒪_S)`
and `B = Γ(Y, 𝒪_Y)`. The stalk of `q^an_* 𝒪_{Y^an}` at `s` is `𝒪_{S^an,s} ⊗[A] B`
(`ComplexAnalytic.bijective_pushforwardStalkTensorMap_of_isFinite`), and `𝒪_{S^an,s}` is flat
over `A`. Hence:

* a weakly regular sequence of `A` on `B` is weakly regular on the stalks of the sheaf of modules
  `q^an_* 𝒪_{Y^an}` (`ComplexAnalytic.isWeaklyRegular_stalk_pushUnit_analytification_map`);
* an injective `A`-linear map `B → A^r` gives separating functionals on `q^an_* 𝒪_{Y^an}`
  (`ComplexAnalytic.separatingFunctionalsAnalytificationMap`).
-/

open CategoryTheory Opposite AlgebraicGeometry TensorProduct RingTheory.Sequence

universe u

namespace ComplexAnalytic

open AnalyticSpace

noncomputable section

variable {Y S : SchemeLFTℂ.{u}} [IsAffine Y.obj.left] [IsAffine S.obj.left] (q : Y ⟶ S)
  [AlgebraicGeometry.IsFinite q.hom.left]

/-- **The stalks of `q^an_* 𝒪`**: `𝒪_{S^an,s} ⊗[A] B → (q^an_* 𝒪)_s` is bijective. -/
theorem bijective_pushforwardStalkTensorMap_of_isFinite (s : analytification.obj S) :
    letI := q.hom.left.appTop.hom.toAlgebra
    Function.Bijective (pushforwardStalkTensorMap (analytification.map q)
      (analytificationΓ Y) (analytificationΓ_naturality q) s) := by
  letI := q.hom.left.appTop.hom.toAlgebra
  haveI := t2Space_analytification_of_isAffine Y
  haveI := isFinite_analytification_map_of_isFinite q
  have h1 := finiteAnalyticSplitting.{u} Y S q s
  have h2 := AnalyticSpace.bijective_pushforwardStalkToPi (analytification.map q) s
  have e : ⇑(stalkTensorMap (analytification.map q) (analytificationΓ Y)
      (analytificationΓ_naturality q) s) =
      TopCat.Presheaf.pushforwardStalkToPi (analytification.map q).toLRSHom.base
        (analytification.obj Y).presheaf s ∘ pushforwardStalkTensorMap (analytification.map q)
          (analytificationΓ Y) (analytificationΓ_naturality q) s :=
    funext fun x ↦ (pushforwardStalkToPi_pushforwardStalkTensorMap _ _ _ s x).symm
  rw [e] at h1
  exact (Function.Bijective.of_comp_iff' h2 _).1 h1

omit [IsAffine Y.obj.left] [IsAffine S.obj.left] [AlgebraicGeometry.IsFinite q.hom.left] in
/-- The value of `𝒪_{S^an,s} ⊗[A] B → (q^an_* 𝒪)_s` on `∑ⱼ cⱼ ⊗ bⱼ`. -/
lemma pushforwardStalkTensorMap_sum_tmul (s : analytification.obj S) {m : ℕ}
    (c : Fin m → (analytification.obj S).presheaf.stalk s) (b : Fin m → Γ(Y.obj.left, ⊤)) :
    letI := q.hom.left.appTop.hom.toAlgebra
    pushforwardStalkTensorMap (analytification.map q) (analytificationΓ Y)
      (analytificationΓ_naturality q) s (∑ j, c j ⊗ₜ b j) =
      ∑ j, (analytification.map q).toLRSHom.stalkAlgMap s (c j) *
        (analytification.map q).toLRSHom.pgerm ⊤ trivial (analytificationΓ Y (b j)) := by
  letI := q.hom.left.appTop.hom.toAlgebra
  rw [map_sum]
  rfl

/-- **Weak regularity on the stalks of `q^an_* 𝒪`**: a pair of functions on `S` weakly regular on
`Γ(Y, 𝒪_Y)` stays weakly regular on the stalks of the pushforward presheaf of rings. -/
theorem isWeaklyRegular_pushforwardStalk (s : analytification.obj S)
    {a₁ a₂ : Γ(S.obj.left, ⊤)}
    (h : letI := q.hom.left.appTop.hom.toAlgebra
      IsWeaklyRegular Γ(Y.obj.left, ⊤) [a₁, a₂]) :
    IsWeaklyRegular (((analytification.map q).toLRSHom.base _*
        (analytification.obj Y).presheaf).stalk s)
      [(analytification.map q).toLRSHom.stalkAlgMap s
          ((analytification.obj S).presheaf.Γgerm s (analytificationΓ S a₁)),
        (analytification.map q).toLRSHom.stalkAlgMap s
          ((analytification.obj S).presheaf.Γgerm s (analytificationΓ S a₂))] := by
  letI := q.hom.left.appTop.hom.toAlgebra
  haveI := flat_analytificationStalk S s
  let Φ := RingEquiv.ofBijective _ (bijective_pushforwardStalkTensorMap_of_isFinite q s)
  have h1 := h.isWeaklyRegular_lTensor (M₂ := (analytification.obj S).presheaf.stalk s)
  have h2 := (isWeaklyRegular_map_algebraMap_iff (R := Γ(S.obj.left, ⊤))
    (S := (analytification.obj S).presheaf.stalk s ⊗[Γ(S.obj.left, ⊤)] Γ(Y.obj.left, ⊤))
    (M := (analytification.obj S).presheaf.stalk s ⊗[Γ(S.obj.left, ⊤)] Γ(Y.obj.left, ⊤))
    [a₁, a₂]).2 h1
  have h3 := h2.map_ringEquiv Φ
  have key : ∀ a : Γ(S.obj.left, ⊤), Φ (algebraMap Γ(S.obj.left, ⊤)
      ((analytification.obj S).presheaf.stalk s ⊗[Γ(S.obj.left, ⊤)] Γ(Y.obj.left, ⊤)) a) =
      (analytification.map q).toLRSHom.stalkAlgMap s
        ((analytification.obj S).presheaf.Γgerm s (analytificationΓ S a)) := fun a ↦ by
    rw [Algebra.TensorProduct.algebraMap_apply]
    refine (pushforwardStalkTensorMap_tmul (analytification.map q) (analytificationΓ Y)
      (analytificationΓ_naturality q) s _ 1).trans ?_
    exact (congrArg (_ * ·) ((congrArg _ (map_one _)).trans (map_one _))).trans
      ((mul_one _).trans rfl)
  simp only [List.map_cons, List.map_nil, key] at h3
  exact h3

/-- **Weak regularity on the stalks of the sheaf of modules `q^an_* 𝒪`.** -/
theorem isWeaklyRegular_stalk_pushUnit_analytification_map (s : analytification.obj S)
    {a₁ a₂ : Γ(S.obj.left, ⊤)}
    (h : letI := q.hom.left.appTop.hom.toAlgebra
      IsWeaklyRegular Γ(Y.obj.left, ⊤) [a₁, a₂]) :
    IsWeaklyRegular (((analytification.obj S).stalkFunctor s).obj
        (LocallyRingedSpace.Hom.pushUnit (analytification.map q).toLRSHom))
      [(analytification.obj S).presheaf.germ ⊤ s trivial (analytificationΓ S a₁),
        (analytification.obj S).presheaf.germ ⊤ s trivial (analytificationΓ S a₂)] :=
  LocallyRingedSpace.Hom.isWeaklyRegular_stalk_pushUnit (analytification.map q).toLRSHom (y := s)
    (U := ⊤) trivial _ _
    (isWeaklyRegular_pushforwardStalk q s h)

variable {m r : ℕ}

/-- **Separating functionals on `q^an_* 𝒪`** from generators `b` of `B = Γ(Y, 𝒪_Y)` over
`A = Γ(S, 𝒪_S)` and an injective `A`-linear map `ℓ : B → A^r`: `τ_k (∑ⱼ cⱼ bⱼ) = ∑ⱼ cⱼ ℓ(bⱼ)_k`. -/
def separatingFunctionalsAnalytificationMap (b : Fin m → Γ(Y.obj.left, ⊤))
    (hb : letI := q.hom.left.appTop.hom.toAlgebra
      Submodule.span Γ(S.obj.left, ⊤) (Set.range b) = ⊤)
    (ℓ : letI := q.hom.left.appTop.hom.toAlgebra
      Γ(Y.obj.left, ⊤) →ₗ[Γ(S.obj.left, ⊤)] (Fin r → Γ(S.obj.left, ⊤)))
    (hℓ : Function.Injective ℓ) :
    LocallyRingedSpace.SeparatingFunctionals
      (LocallyRingedSpace.Hom.pushUnit (analytification.map q).toLRSHom) ⊤ :=
  letI := q.hom.left.appTop.hom.toAlgebra
  haveI := flat_analytificationStalk S
  LocallyRingedSpace.Hom.separatingFunctionalsOfStalks (f := (analytification.map q).toLRSHom)
    (b := fun j ↦ analytificationΓ Y (b j)) (fun k j ↦ analytificationΓ S (ℓ (b j) k))
    (fun y c hc k ↦ by
      have h0 := (bijective_pushforwardStalkTensorMap_of_isFinite q y).1
        (((pushforwardStalkTensorMap_sum_tmul q y c b).trans hc).trans (map_zero _).symm)
      exact (TensorProduct.sum_tmul_eq_zero_iff_of_injective ℓ hℓ b c).1 h0 k)
    (fun y hy z ↦ by
      obtain ⟨x, rfl⟩ := (bijective_pushforwardStalkTensorMap_of_isFinite q y).2 z
      obtain ⟨c, rfl⟩ := TensorProduct.exists_eq_sum_tmul_of_span_eq_top hb x
      exact ⟨c, pushforwardStalkTensorMap_sum_tmul q y c b⟩)
    (fun y c hc ↦ by
      rw [← pushforwardStalkTensorMap_sum_tmul q y c b,
        (TensorProduct.sum_tmul_eq_zero_iff_of_injective ℓ hℓ b c).2 hc, map_zero])

end

end ComplexAnalytic
