/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.ES.Codim2.DescentSections
import Oka.AnalyticSpace.FiniteEtaleBaseChange
import Oka.AnalyticSpace.HolomorphicMap

/-!
# The Puiseux base change of a finite étale cover

Let `α = Kummer.coordPow i₀ s : ℂⁿ → ℂⁿ` be the Puiseux map `t ↦ tˢ` in the coordinate `i₀`, let
`N₀' = α⁻¹(N₀)` and let `W` be a finite étale cover of `N₀`. The fibre product
`W' = W ×_{N₀} N₀'` along `α|_{N₀'}` (`ComplexAnalytic.AnalyticSpace.baseChange`) is a finite étale
cover of `N₀'` (`ComplexAnalytic.BoundedSections.puiseuxCover`), Hausdorff if `W` is, and together
with its first projection it satisfies `ComplexAnalytic.BoundedSections.IsPuiseuxPullback`
(`ComplexAnalytic.BoundedSections.isPuiseuxPullback_puiseuxCover`).

## Main definitions

- `ComplexAnalytic.BoundedSections.puiseuxMap i₀ s`: `α` as a morphism `ℂⁿ ⟶ ℂⁿ`.
- `ComplexAnalytic.BoundedSections.puiseuxRestrict`: `α` as a morphism `N₀' ⟶ N₀`.
- `ComplexAnalytic.BoundedSections.puiseuxCover`: the base change `W'` of `W` along `α`.
- `ComplexAnalytic.BoundedSections.puiseuxProj`: the projection `W' → W`, as a map of points.

## Main results

- `ComplexAnalytic.BoundedSections.isPuiseuxPullback_puiseuxCover`: `W'` is the base change of `W`
  along `α` in the sense of `ComplexAnalytic.BoundedSections.IsPuiseuxPullback`.
-/

open CategoryTheory Opposite AlgebraicGeometry Topology TopologicalSpace Kummer

universe u

namespace ComplexAnalytic.BoundedSections

open AnalyticSpace

noncomputable section

variable {n : ℕ} (i₀ : ULift.{u} (Fin n)) (s : ℕ)

/-- The Puiseux map `α` as a morphism of complex analytic spaces `ℂⁿ ⟶ ℂⁿ`. -/
def puiseuxMap : AnalyticSpace.complexAffineSpace.{u} n ⟶ AnalyticSpace.complexAffineSpace.{u} n :=
  AnalyticSpace.okaMap fun j ↦ OkaRing.ofDifferentiableOn (fun x ↦ coordPow i₀ s x j)
    (differentiable_pi.1 (differentiable_coordPow (i₀ := i₀) s) j).differentiableOn

lemma base_puiseuxMap (x : Cn.{u} n) : (puiseuxMap i₀ s).toLRSHom.base x = coordPow i₀ s x := by
  funext j
  exact (congrFun (base_okaMapHom _ x) j).trans (okaMapFun_apply _ x j)

variable {i₀ s} {N₀ N₀' : (AnalyticSpace.complexAffineSpace.{u} n).Opens}

lemma range_puiseuxMap_subset (hN₀ : ∀ x, x ∈ N₀' ↔ coordPow i₀ s x ∈ N₀) :
    Set.range ((AnalyticSpace.complexAffineSpace.{u} n).ofRestrict N₀' ≫
      puiseuxMap i₀ s).toLRSHom.base ⊆ (N₀ : Set _) := by
  rintro _ ⟨x, rfl⟩
  change (puiseuxMap i₀ s).toLRSHom.base x.1 ∈ N₀
  rw [base_puiseuxMap]
  exact (hN₀ x.1).1 x.2

/-- The Puiseux map as a morphism `N₀' ⟶ N₀`. -/
def puiseuxRestrict (hN₀ : ∀ x, x ∈ N₀' ↔ coordPow i₀ s x ∈ N₀) : space N₀' ⟶ space N₀ :=
  liftRestrict ((AnalyticSpace.complexAffineSpace.{u} n).ofRestrict N₀' ≫ puiseuxMap i₀ s) N₀
    (range_puiseuxMap_subset hN₀)

lemma coe_base_puiseuxRestrict (hN₀ : ∀ x, x ∈ N₀' ↔ coordPow i₀ s x ∈ N₀) (x : space N₀') :
    ((puiseuxRestrict hN₀).toLRSHom.base x).1 = coordPow i₀ s x.1 := by
  have := congrArg (fun φ ↦ φ.toLRSHom.base x) (liftRestrict_fac
    ((AnalyticSpace.complexAffineSpace.{u} n).ofRestrict N₀' ≫ puiseuxMap i₀ s) N₀
    (range_puiseuxMap_subset hN₀))
  exact this.trans (base_puiseuxMap i₀ s x.1)

variable (hN₀ : ∀ x, x ∈ N₀' ↔ coordPow i₀ s x ∈ N₀) (W : FiniteEtaleOver (space N₀))

/-- **The Puiseux base change** `W ×_{N₀} N₀'` of a finite étale cover `W` of `N₀`. -/
def puiseuxCover : FiniteEtaleOver (space N₀') :=
  MorphismProperty.Over.mk ⊤ (baseChangeSnd (cov W) (puiseuxRestrict hN₀))
    (isFiniteEtale_baseChangeSnd _ _)

/-- The projection `W' → W` of the Puiseux base change, on points. -/
def puiseuxProj : (puiseuxCover hN₀ W).left → W.left :=
  (baseChangeFst (cov W) (puiseuxRestrict hN₀)).toLRSHom.base

/-- The points of the Puiseux base change: pairs `(w, x')` with `p(w) = α(x')`. -/
abbrev PuiseuxPoint : Type u :=
  Function.Pullback (cov W).toLRSHom.base (puiseuxRestrict hN₀).toLRSHom.base

lemma pt_puiseuxCover (w : PuiseuxPoint hN₀ W) : pt (puiseuxCover hN₀ W) w = w.1.2.1 :=
  rfl

lemma puiseuxProj_apply (w : PuiseuxPoint hN₀ W) : puiseuxProj hN₀ W w = w.1.1 := by
  unfold puiseuxProj
  rw [base_baseChangeFst]
  rfl

instance [T2Space W.left] : T2Space (puiseuxCover hN₀ W).left := by
  haveI : T2Space (AnalyticSpace.complexAffineSpace.{u} n) := by
    change T2Space (Cn.{u} n)
    infer_instance
  haveI : T2Space (space N₀') := by
    change T2Space N₀'
    infer_instance
  change T2Space (Function.Pullback (cov W).toLRSHom.base (puiseuxRestrict hN₀).toLRSHom.base)
  infer_instance

/-- **The Puiseux base change is the base change along `α`.** -/
theorem isPuiseuxPullback_puiseuxCover (hs : 0 < s) :
    IsPuiseuxPullback i₀ s W (puiseuxCover hN₀ W) (puiseuxProj hN₀ W) where
  pos := hs
  mem_iff := hN₀
  continuous := (baseChangeFst (cov W) (puiseuxRestrict hN₀)).toLRSHom.base.hom.continuous
  pt_eq w := by
    rw [puiseuxProj_apply, pt_puiseuxCover, ← coe_base_puiseuxRestrict hN₀]
    exact congrArg Subtype.val w.2
  ext w₁ w₂ h₁ h₂ := by
    rw [pt_puiseuxCover, pt_puiseuxCover] at h₁
    rw [puiseuxProj_apply, puiseuxProj_apply] at h₂
    exact Subtype.ext (Prod.ext h₂ (Subtype.ext h₁))
  exists_lift w x h := by
    have hx : x ∈ N₀' := (hN₀ x).2 (h ▸ pt_mem W w)
    refine ⟨(⟨(w, ⟨x, hx⟩), Subtype.ext ?_⟩ : PuiseuxPoint hN₀ W), rfl, puiseuxProj_apply _ _ _⟩
    exact h.trans (coe_base_puiseuxRestrict hN₀ ⟨x, hx⟩).symm

end

end ComplexAnalytic.BoundedSections
