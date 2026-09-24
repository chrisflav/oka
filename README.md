# oka

A formalization in Lean 4 / Mathlib of **Oka's coherence theorem** and of **Serre's GAGA**.

Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten.

## Main results

* **Complex analytic spaces** (`ComplexAnalytic.AnalyticSpace`, `Oka/AnalyticSpace/Basic.lean`):
  locally ringed spaces locally isomorphic to closed analytic subspaces of open subsets of `ℂⁿ`.
* **Oka's coherence theorem** (`ComplexAnalytic.AnalyticSpace.isCoherentStructureSheaf`,
  `Oka/AnalyticSpace/Coherent.lean`): the structure sheaf of any complex analytic space is
  coherent.
* **Analytification** (`ComplexAnalytic.analytification`, `Oka/Analytification/Scheme.lean`):
  the functor `X ↦ X^an` from schemes locally of finite type over `ℂ` to complex analytic spaces.
* **Serre's GAGA** (`ComplexAnalytic.gagaFull`, `Oka/Analytification/GAGA/ProjectiveGAGA3.lean`):
  for a projective scheme `X` over `ℂ`, `Hᵠ(X, F) ≅ Hᵠ(X^an, F^an)` for coherent `F`, and
  analytification is an equivalence between coherent sheaves on `X` and coherent analytic
  sheaves on `X^an` (`ComplexAnalytic.gagaEquivalence`,
  `Oka/Analytification/GAGA/Equivalence.lean`).
* **Towards the Riemann existence theorem** (`Oka/Analytification/RET/`): analytification sends
  finite étale morphisms to finite étale maps and is faithful on finite étale covers.
