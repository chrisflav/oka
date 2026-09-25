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
* **Serre's GAGA for proper schemes** (`ComplexAnalytic.gagaFull_proper`,
  `Oka/Analytification/GAGA/Proper/Equivalence.lean`): for a proper scheme `X` over `ℂ`,
  `Hᵠ(X, F) ≅ Hᵠ(X^an, F^an)` for coherent `F`, and analytification is an equivalence between
  coherent sheaves on `X` and coherent analytic sheaves on `X^an`
  (`ComplexAnalytic.gagaEquivalenceOfIsProperℂ`). The proof reduces to the projective case via
  Chow's lemma and uses Rückert's Nullstellensatz.
* **The Riemann existence theorem** (`ComplexAnalytic.riemannExistenceTheoremEquiv`,
  `Oka/Analytification/RET/RiemannExistence.lean`): for every scheme `X` locally of finite type
  over `ℂ`, analytification is an equivalence between finite étale covers of `X` and finite étale
  covers of `X^an` with separated structure map. The proof extends covers across boundary divisors
  by a formalisation of the Grauert–Remmert extension theorem and algebraises them with GAGA.
