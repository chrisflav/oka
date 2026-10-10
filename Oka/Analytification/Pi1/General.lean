/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.Pi1.Smooth
import Oka.Geometry.RealAlgebraic.Lojasiewicz

/-!
# The comparison theorem for every connected scheme locally of finite type over `ℂ`

The Łojasiewicz gradient inequality for real polynomials
(`MvPolynomial.exists_lojasiewicz_gradient`, `Oka/Geometry/RealAlgebraic/Lojasiewicz.lean`)
discharges the hypothesis of
`ComplexAnalytic.locallyContractibleSpace_analytification_of_lojasiewicz`, so the analytification
of **every** scheme locally of finite type over `ℂ` is locally contractible
(`ComplexAnalytic.locallyContractibleSpace_analytification`), and the comparison theorem holds
unconditionally (`ComplexAnalytic.etaleFundamentalGroupEquivCompletion`). Nothing else is proved
here.
-/

universe u

open CategoryTheory AlgebraicGeometry ProfiniteGrp.ProfiniteCompletion

/-- **Every real polynomial satisfies the Łojasiewicz gradient inequality** at each of its
zeros. -/
theorem MvPolynomial.lojasiewiczGradient {n : ℕ} (f : MvPolynomial (Fin n) ℝ) :
    f.LojasiewiczGradient :=
  fun p hp ↦ MvPolynomial.exists_lojasiewicz_gradient f p hp

namespace ComplexAnalytic

/-- **The analytification of a scheme locally of finite type over `ℂ` is locally contractible.** -/
theorem locallyContractibleSpace_analytification (X : SchemeLFTℂ.{u}) :
    LocallyContractibleSpace (analytification.obj X) :=
  locallyContractibleSpace_analytification_of_lojasiewicz
    (fun _ f ↦ MvPolynomial.lojasiewiczGradient f) X

/-- **The comparison theorem `π₁ᵉᵗ(X, ξₓ) ≅ π₁(X^an, x)^`**: for every connected scheme `X` locally
of finite type over `ℂ` (possibly singular, non-reduced or non-separated) and every point `x` of
`X^an`, the étale fundamental group of `X` at the geometric point `ξₓ` is isomorphic, as a
topological group, to the profinite completion of the topological fundamental group of `X^an` at
`x`. -/
noncomputable def etaleFundamentalGroupEquivCompletion {X : SchemeLFTℂ.{u}}
    [ConnectedSpace X.obj.left] (x : analytification.obj X) :
    Aut (FiniteEtale.fiber (geometricPoint X x)) ≃ₜ*
      completion (GrpCat.of (FundamentalGroup (analytification.obj X) x)) :=
  etaleFundamentalGroupContinuousMulEquiv x (locallyContractibleSpace_analytification X)

end ComplexAnalytic
