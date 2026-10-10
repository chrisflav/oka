/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analysis.Normed.LocallyContractibleRetract
import Oka.Analytification.LocallyContractible
import Oka.Analytification.Pi1.Comparison
import Oka.Analytification.RET.ES.SmoothLocus
import Oka.Topology.Homotopy.LocallyContractible

/-!
# The comparison theorem for smooth schemes, and given the Łojasiewicz inequality

`ComplexAnalytic.etaleFundamentalGroupContinuousMulEquiv` asks `X^an` to be locally contractible.
This file discharges that hypothesis

- for `X` smooth over `ℂ`, where `X^an` is locally isomorphic to opens of `ℂⁿ`
  (`ComplexAnalytic.isLocallyOpenInAffine_analytification`), giving the unconditional
  `ComplexAnalytic.etaleFundamentalGroupContinuousMulEquivOfSmooth`;
- for arbitrary `X`, from the Łojasiewicz gradient inequality for real polynomials
  (`MvPolynomial.LojasiewiczGradient`, through
  `ComplexAnalytic.locallyContractibleSpace_analytification_of_lojasiewicz`), giving
  `ComplexAnalytic.etaleFundamentalGroupContinuousMulEquivOfLojasiewicz`.

Local contractibility passes along local homeomorphisms
(`LocallyContractibleAt.image_of_isLocalHomeomorph`), which is not in Mathlib.
-/

universe u

open CategoryTheory AlgebraicGeometry ProfiniteGrp.ProfiniteCompletion Topology

/-- **A local homeomorphism carries local contractibility at `y` to local contractibility at
`f y`.** -/
theorem LocallyContractibleAt.image_of_isLocalHomeomorph {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : Y → X} (hf : IsLocalHomeomorph f) {y : Y}
    (hy : LocallyContractibleAt y) : LocallyContractibleAt (f y) := by
  obtain ⟨φ, hyφ, rfl⟩ := hf y
  have h₁ : LocallyContractibleAt (⟨y, hyφ⟩ : φ.source) :=
    LocallyContractibleAt.of_isOpenEmbedding φ.open_source.isOpenEmbedding_subtypeVal hy
  exact LocallyContractibleAt.image_of_isOpenEmbedding φ.isOpenEmbedding_restrict h₁

/-- An open subset of a real normed space is locally contractible. -/
theorem IsOpen.locallyContractibleSpace_of_normedSpace {E : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] {Z : Set E} (hZ : IsOpen Z) : LocallyContractibleSpace Z :=
  locallyContractibleSpace_of_forall_retraction fun p hp ↦ by
    obtain ⟨ρ, hρ, hρZ⟩ := Metric.isOpen_iff.1 hZ p hp
    exact ⟨ρ, hρ, id, continuousOn_id, fun y hy ↦ hρZ hy, fun _ _ _ ↦ rfl⟩

namespace ComplexAnalytic

/-- **An analytic space locally isomorphic to opens of `ℂⁿ` is locally contractible.** -/
theorem locallyContractibleSpace_of_isLocallyOpenInAffine {Y : AnalyticSpace.{u}}
    (hY : AnalyticSpace.IsLocallyOpenInAffine Y) : LocallyContractibleSpace Y := by
  intro y
  obtain ⟨n, U, φ, z, hφ, rfl⟩ := hY y
  have hUo : IsOpen (X := ULift.{u} (Fin n) → ℂ) U.1 := U.2
  have hU' := IsOpen.locallyContractibleSpace_of_normedSpace (E := ULift.{u} (Fin n) → ℂ) hUo
  have hU : LocallyContractibleSpace
      ((AnalyticSpace.complexAffineSpace.{u} n).restrict U : Type u) := hU'
  exact LocallyContractibleAt.image_of_isLocalHomeomorph hφ.isLocalHomeomorph (hU z)

/-- **The analytification of a smooth scheme over `ℂ` is locally contractible.** -/
theorem locallyContractibleSpace_analytification_of_smooth (X : SchemeLFTℂ.{u})
    [Smooth X.obj.hom] : LocallyContractibleSpace (analytification.obj X) :=
  locallyContractibleSpace_of_isLocallyOpenInAffine
    (isLocallyOpenInAffine_analytification (SchemeLFTℂ.isLocallyEtaleOverAffineSpace_of_smooth X))

variable {X : SchemeLFTℂ.{u}} [ConnectedSpace X.obj.left] (x : analytification.obj X)

/-- **The comparison theorem for smooth schemes**: for `X` connected and smooth over `ℂ` and
`x : X^an`, `π₁ᵉᵗ(X, ξₓ)` is the profinite completion of `π₁(X^an, x)`, as topological groups. -/
noncomputable def etaleFundamentalGroupContinuousMulEquivOfSmooth [Smooth X.obj.hom] :
    Aut (FiniteEtale.fiber (geometricPoint X x)) ≃ₜ*
      completion (GrpCat.of (FundamentalGroup (analytification.obj X) x)) :=
  etaleFundamentalGroupContinuousMulEquiv x (locallyContractibleSpace_analytification_of_smooth X)

/-- **The comparison theorem, given the Łojasiewicz gradient inequality** for real polynomials:
for every connected `X` locally of finite type over `ℂ`. -/
noncomputable def etaleFundamentalGroupContinuousMulEquivOfLojasiewicz
    (h : ∀ (n : ℕ) (f : MvPolynomial (Fin n) ℝ), f.LojasiewiczGradient) :
    Aut (FiniteEtale.fiber (geometricPoint X x)) ≃ₜ*
      completion (GrpCat.of (FundamentalGroup (analytification.obj X) x)) :=
  etaleFundamentalGroupContinuousMulEquiv x
    (locallyContractibleSpace_analytification_of_lojasiewicz h X)

end ComplexAnalytic
