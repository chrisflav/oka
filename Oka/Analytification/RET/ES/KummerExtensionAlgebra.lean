/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.ES.KummerExtensionSheaf

/-!
# The canonical extension as an `𝒪_S`-algebra

Keep the notation of `Oka/Analytification/RET/ES/KummerExtensionSheaf.lean`. Pulling back
holomorphic functions on `V ⊆ S` along `p : W → S°` makes `𝒞̄(V)` an `𝒪_S(V)`-algebra
(`ComplexAnalytic.KummerModel.extensionAlgebraMap`), compatibly with restriction. Off `t = 0`
every section is bounded, so `𝒞̄` restricts to `p_* 𝒪_W` there
(`ComplexAnalytic.KummerModel.boundedSubring_eq_top`).

## Main definitions

- `ComplexAnalytic.KummerModel.pullbackHom W V`: pulling back sections of `𝒪_S` over `V` to
  sections of `𝒪_W` over `p⁻¹(V ∩ S°)`.
- `ComplexAnalytic.KummerModel.extensionAlgebraMap W V`: the structure map `𝒪_S(V) → 𝒞̄(V)`.
- `ComplexAnalytic.KummerModel.extensionAlgebraHom`: the same, as a morphism of presheaves.

## Main results

- `ComplexAnalytic.KummerModel.boundedSubring_eq_top`: off `t = 0`, `𝒞̄ = p_* 𝒪_W`.
- `ComplexAnalytic.KummerModel.mem_boundedSubring_of_isIntegralElem`: integral sections are
  bounded.
-/

open CategoryTheory Opposite AlgebraicGeometry Topology TopologicalSpace Filter

universe u

namespace ComplexAnalytic.KummerModel

open AnalyticSpace

noncomputable section

variable {m : ℕ} {B : Set (ULift.{u} (Fin m) → ℂ)} {hB : IsOpen B}

/-- The open subset of `ℂ^{m+1}` underlying an open subset of `S`, as an open. -/
abbrev tOpens (V : (disc hB).Opens) : Opens (ULift.{u} (Fin (m + 1)) → ℂ) :=
  (discOpens B hB).isOpenEmbedding.isOpenMap.functor.obj V

/-- A section of `𝒪_S` over `V`, as a function on `ℂ^{m+1}` (extended by zero). -/
def holFun {V : (disc hB).Opens} (g : (disc hB).presheaf.obj (op V)) :
    (ULift.{u} (Fin (m + 1)) → ℂ) → ℂ :=
  OkaRing.toGlobalFun (tOpens V) g

lemma eval_disc {V : (disc hB).Opens} (g : (disc hB).presheaf.obj (op V)) (x : disc hB)
    (hx : x ∈ V) : (disc hB).eval x hx g = holFun g x.1 := by
  rw [eval_restrict_complexAffineSpace_of]
  exact (OkaRing.toGlobalFun_apply (U := tOpens V) g ⟨x, hx, rfl⟩).symm

lemma differentiableOn_holFun {V : (disc hB).Opens} (g : (disc hB).presheaf.obj (op V)) :
    DifferentiableOn ℂ (holFun g) (coeOpens V) :=
  OkaRing.differentiableOn_toGlobalFun (U := tOpens V) g

variable (W : FiniteEtaleOver (punctured hB))

lemma tOpens_punctured_le (V : (disc hB).Opens) :
    (puncturedOpens B hB).isOpenEmbedding.isOpenMap.functor.obj
      (puncturedPreimage hB (isOpen_coeOpens V)) ≤ tOpens V := by
  rintro _ ⟨y, hy, rfl⟩
  exact hy

/-- Pulling back a section of `𝒪_S` over `V` to a section of `𝒪_W` over `p⁻¹(V ∩ S°)`. -/
def pullbackHom (V : (disc hB).Opens) :
    (disc hB).presheaf.obj (op V) →+* W.left.presheaf.obj (op (preim W V)) :=
  (W.hom.toLRSHom.c.app (op (puncturedPreimage hB (isOpen_coeOpens V)))).hom.comp
    (OkaRing.restrict (tOpens_punctured_le V)).toRingHom

lemma eval_pullbackHom (V : (disc hB).Opens) (g : (disc hB).presheaf.obj (op V)) (w : W.left)
    (hw : w ∈ preim W V) :
    W.left.eval w hw (pullbackHom W V g) =
      holFun g ((W.hom.toLRSHom.base w : punctured hB).1 : ULift.{u} (Fin (m + 1)) → ℂ) := by
  refine (eval_c_app _ W.hom.isCLinear w hw _).trans
    ((eval_restrict_complexAffineSpace_of (puncturedOpens B hB) _ hw _).trans ?_)
  exact (OkaRing.toGlobalFun_apply (U := tOpens V) g (tOpens_punctured_le V ⟨_, hw, rfl⟩)).symm

lemma pullbackHom_mem_boundedSubring (V : (disc hB).Opens) (g : (disc hB).presheaf.obj (op V)) :
    pullbackHom W V g ∈ boundedSubring W V := by
  intro x hx _
  have hc : ContinuousAt (holFun g) x :=
    (differentiableOn_holFun g).continuousOn.continuousAt ((isOpen_coeOpens V).mem_nhds hx)
  refine ⟨_, hc.norm.eventually (gt_mem_nhds (lt_add_one ‖holFun g x‖)), ‖holFun g x‖ + 1,
    fun w hw hwN ↦ ?_⟩
  rw [eval_pullbackHom]
  exact le_of_lt hwN

/-- The structure map `𝒪_S(V) → 𝒞̄(V)`: pulling back holomorphic functions along `p`. -/
def extensionAlgebraMap (V : (disc hB).Opens) :
    (disc hB).presheaf.obj (op V) →+* boundedSubring W V :=
  (pullbackHom W V).codRestrict _ (pullbackHom_mem_boundedSubring W V)

instance (V : (disc hB).Opens) : Algebra ((disc hB).presheaf.obj (op V)) (boundedSubring W V) :=
  (extensionAlgebraMap W V).toAlgebra

lemma algebraMap_val (V : (disc hB).Opens) (g : (disc hB).presheaf.obj (op V)) :
    (algebraMap ((disc hB).presheaf.obj (op V)) (boundedSubring W V) g).1 = pullbackHom W V g :=
  rfl

/-- The structure maps commute with restriction. -/
lemma pullbackHom_map (hW : IsLocallyOpenInAffine W.left) {V V' : (disc hB).Opens} (h : V' ≤ V)
    (g : (disc hB).presheaf.obj (op V)) :
    W.left.presheaf.map (homOfLE (preim_mono W h)).op (pullbackHom W V g) =
      pullbackHom W V' ((disc hB).presheaf.map (homOfLE h).op g) := by
  refine eq_of_forall_eval_eq hW fun w hw ↦ ?_
  refine (eval_presheaf_map W.left _ w hw _).trans ?_
  rw [eval_pullbackHom, eval_pullbackHom]
  obtain ⟨y, hy, hyw⟩ := hw
  have h₁ := eval_disc g y (h hy)
  have h₂ := eval_disc ((disc hB).presheaf.map (homOfLE h).op g) y hy
  rw [eval_presheaf_map] at h₂
  rw [← hyw, ← h₁, ← h₂]

/-- **Off `t = 0` the canonical extension is `p_* 𝒪_W`**: over an open avoiding `t = 0` every
section is bounded. -/
theorem boundedSubring_eq_top {V : (disc hB).Opens}
    (hV : ∀ x ∈ coeOpens V, x zero ≠ 0) : boundedSubring W V = ⊤ :=
  eq_top_iff.2 fun _ _ x hx hx0 ↦ absurd hx0 (hV x hx)

variable {W} in
/-- The structure morphism `𝒪_S ⟶ 𝒞̄` of presheaves of rings. -/
def extensionAlgebraHom (hW : IsLocallyOpenInAffine W.left) :
    (disc hB).presheaf ⟶ extensionPresheaf W where
  app V := CommRingCat.ofHom (extensionAlgebraMap W V.unop)
  naturality V V' f := by
    ext g
    exact Subtype.ext (pullbackHom_map W hW f.unop.le g).symm

/-- **Integral sections are bounded**: a section of `𝒪_W` over `p⁻¹(V ∩ S°)` which is integral
over `𝒪_S(V)` is bounded near `t = 0`. -/
theorem mem_boundedSubring_of_isIntegralElem (V : (disc hB).Opens)
    {s : W.left.presheaf.obj (op (preim W V))} (hs : (pullbackHom W V).IsIntegralElem s) :
    s ∈ boundedSubring W V := by
  classical
  obtain ⟨P, hP, hPs⟩ := hs
  intro x hx _
  set n := P.natDegree
  have hev : ∀ᶠ z in 𝓝 x, ∀ i ∈ Finset.range n,
      ‖holFun (P.coeff i) z‖ ≤ ‖holFun (P.coeff i) x‖ + 1 := by
    refine (Filter.eventually_all_finset _).2 fun i _ ↦ ?_
    have hc := ((differentiableOn_holFun (P.coeff i)).continuousOn.continuousAt
      ((isOpen_coeOpens V).mem_nhds hx)).norm
    filter_upwards [hc.eventually (gt_mem_nhds (lt_add_one _))] with z hz using hz.le
  set A := ∑ i ∈ Finset.range n, (‖holFun (P.coeff i) x‖ + 1)
  refine ⟨_, hev, max 1 (n * A), fun w hw hwN ↦ ?_⟩
  refine Kummer.norm_le_of_pow_add_sum_eq_zero (a := fun i ↦ holFun (P.coeff i)
    ((W.hom.toLRSHom.base w : punctured hB).1 : ULift.{u} (Fin (m + 1)) → ℂ))
    (fun i hi ↦ (hwN i (Finset.mem_range.2 hi)).trans (Finset.single_le_sum
      (f := fun i ↦ ‖holFun (P.coeff i) x‖ + 1) (fun _ _ ↦ by positivity)
      (Finset.mem_range.2 hi))) ?_
  have h₁ := congrArg (W.left.eval w hw) hPs
  rw [map_zero, Polynomial.hom_eval₂, hP.as_sum] at h₁
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum,
    Polynomial.eval₂_mul, Polynomial.eval₂_C, RingHom.coe_comp, Function.comp_apply,
    eval_pullbackHom] at h₁
  exact h₁

end

end ComplexAnalytic.KummerModel
