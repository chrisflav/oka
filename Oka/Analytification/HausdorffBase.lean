/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Analytification.Hausdorff
import Oka.Analytification.StandardEtaleFiniteEtaleBase

/-!
# The standard étale cover of a presented base is a covering map over an open

`Oka/Analytification/Hausdorff.lean` makes the analytification of a tuple of polynomials Hausdorff
and applies the covering-map rung at an **empty** base presentation, to the composite to `ℂ^n`.
`Oka/Analytification/StandardEtaleFiniteEtaleBase.lean` proves the finite-étale half at **every**
`k`, and about the **structure map to `X^an`**. This file is the rung applied to that half, and it
is **one `haveI` and an application**, exactly as the `k = 0` pair is.

**The two morphisms are the whole subtlety of this neighbourhood.** What is stated here is about
`ComplexAnalytic.analytificationMap (ComplexAnalytic.etalePresHom g F G)`, the structure map to
`X^an`, which is the morphism a cover is; the theorems in `Oka/Analytification/Hausdorff.lean` are
about that map composed with `ComplexAnalytic.analytificationInclHom`, down to `ℂ^n`. This is not
a generalisation of those, and **at `k ≥ 1` their statement is not merely unstated but false**:
the unrestricted composite is not a local isomorphism as soon as some `g j` is nonzero and the
source has a point — `ComplexAnalytic.not_isLocalIso_analytificationMap_etalePresHom_comp`
(`Oka/Analytification/StandardEtaleNotLocalIso.lean`) — hence not finite étale, by
`ComplexAnalytic.AnalyticSpace.IsFiniteEtale.isLocalIso`.

**The open subset is the preimage in `X^an` of an open subset of `ℂ^n` avoiding the bad set**, and
not that open subset itself: the finiteness half is stated over
`(Opens.map (ComplexAnalytic.analytificationInclHom g).toLRSHom.base).obj V`, since the source of
the morphism restricted lives over `X^an` and not over `ℂ^n`. That is the whole of the difference
between the statements below and `Oka/Analytification/Hausdorff.lean`'s.

## No Hausdorff statement is added here, and that was worth measuring

`ComplexAnalytic.t2Space_analytification` (`Oka/Analytification/Hausdorff.lean`) binds `{n k : ℕ}`
and its `k` does not occur in its conclusion — it is declared above that file's `noncomputable
section` and so outside its `g : Fin 0 → …` block, and no morphism occurs in it at all. It is the
only `T2Space` instance about `ComplexAnalytic.AnalyticSpace.analytification` anywhere under
`Oka/`. So the separation hypothesis of
`ComplexAnalytic.AnalyticSpace.isCoveringMap_base_of_isFiniteEtale` is discharged **by instance
search at `k ≥ 1` exactly as it is at `k = 0`**, through that instance and
`ComplexAnalytic.t2Space_restrict`; there is no `haveI` for it below and none is needed.
`Oka/Analytification/Hausdorff.lean` is titled *The analytification is Hausdorff, and the standard
étale cover is a covering map*, and its `## Main results` lists that instance beside the two
corollaries; **only the second half of that title has a `k ≥ 1` counterpart to state, because the
Hausdorff half was never `k`-restricted.**

## Why this is a sibling module and not an append

`Oka/Analytification/Hausdorff.lean`'s import closure is **5240** modules and does not contain
`Oka.Analytification.StandardEtaleFiniteEtaleBase`; the union is **5246**, so appending these two
theorems there would put **six** modules onto that file —
`Oka.AnalyticSpace.CutOutCancel`, `Oka.AnalyticSpace.CutOutLocalIso`,
`Oka.AnalyticSpace.PullbackOpen`, `Oka.Analytification.StandardEtaleFiniteEtaleBase`,
`Oka.Analytification.StandardEtaleFinitenessBase` and
`Oka.Analytification.StandardEtaleLocalIsoBase`, **no Mathlib module among them**, by a set
difference over `Lean.Environment.allImportedModuleNames` at `d34b436`.

**At `d34b436` nothing under `Oka/` imported `Oka/Analytification/Hausdorff.lean`** —
`scripts/module_graph.py --importers` gave **0**, and this file is now its only importer — so
those six would have cost no other module of this repository anything. **That is the argument for
the sibling and not against it**: the reason to split is the neighbourhood's
own convention, under which the `…Base` file is the presented-base, `k ≥ 1` version of the file
whose name it extends (`StandardEtaleFiniteness` → `StandardEtaleFinitenessBase`,
`StandardEtaleFiniteEtale` → `StandardEtaleFiniteEtaleBase`, `StandardEtaleLocalIso` →
`StandardEtaleLocalIsoBase`), and the import figure is what says the split costs nothing rather
than what forces it.

## Main results

- `ComplexAnalytic.isCoveringMap_base_restrictHom_analytificationMap_etalePresHom`: **the
  analytification of a standard étale morphism over a presented base is a covering map over the
  part of `X^an` lying above an open subset of `ℂ^n` avoiding the bad set.**
- `ComplexAnalytic.isCoveringMap_base_restrictHom_analytificationMap_etalePresHom_compl`: the same
  at the complement of the bad set.

## What is not here

* **No degree, and no number of sheets.**
  `ComplexAnalytic.AnalyticSpace.card_fiber_eq_of_isFiniteEtale` applies to the same morphism — its
  `[T2Space]` on the source is discharged here — but it also asks `[PreconnectedSpace]` of the
  base, and nothing here shows that the preimage in `X^an` of an arbitrary open subset of `ℂ^n`
  avoiding the bad set is preconnected, or even nonempty. That is the same second deliverable
  `Oka/Analytification/Hausdorff.lean` records at `k = 0`, and **at `F = G = X` the open subset is
  empty**, so neither theorem below is on its own evidence that anything is covered.
* **Nothing about the unrestricted structure map**, whose finiteness is false for the reason
  `Oka/Analytification/StandardEtaleFiniteEtaleBase.lean` gives, so the restriction is not an
  artefact of this file.
* **Nothing about the composite to `ℂ^n` at `k ≥ 1`**, which is false and not merely unstated, for
  the reason given above. The `k = 0` case of that composite is
  `Oka/Analytification/Hausdorff.lean`'s and stays there.
* **No claim that the morphism is not an isomorphism**, and so no claim that the rung is
  non-vacuous at it: this file adds an application, not a witness of non-triviality.
* **Nothing at a specific pair.** These are the general `k ≥ 1` statements; instantiating them at
  a specific pair is a separate deliverable and a different statement again.
* **No comparison functor and no Riemann existence theorem.** Taxis #1113's functor is not here.
-/

open CategoryTheory MvPolynomial AlgebraicGeometry TopologicalSpace Opposite Topology

universe u

namespace ComplexAnalytic

noncomputable section

variable {n k : ℕ} (g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ)
  (F G : Polynomial (MvPolynomial (ULift.{u} (Fin n)) ℂ))

/-- **The analytification of a standard étale morphism over a presented base is a covering map
over the part of `X^an` lying above an open subset of `ℂ^n` avoiding the bad set.**

`ComplexAnalytic.isFiniteEtale_restrictHom_analytificationMap_etalePresHom` is the whole of the
input, and the separation hypothesis of
`ComplexAnalytic.AnalyticSpace.isCoveringMap_base_of_isFiniteEtale` is found by instance search:
the source is an open subspace of `ComplexAnalytic.AnalyticSpace.analytification`, which
`ComplexAnalytic.t2Space_analytification` — an instance at every `k` — and
`ComplexAnalytic.t2Space_restrict` reach.

The hypotheses are the finite-étale theorem's and they are not redistributed here: `hF` and `hV`
buy finiteness, `P`, `hFP` and `hGP` buy the local isomorphism, and the covering-map rung reads
both fields and no separation of the base. -/
theorem isCoveringMap_base_restrictHom_analytificationMap_etalePresHom (hF : F.Monic)
    (P : StandardEtalePair (PresentedAlgebra.{u} n k g))
    (hFP : polyPresentedAlgebraEquiv.{u} g
      (Ideal.Quotient.mk _ ((lastVarPolyEquiv.{u} n).symm F)) = P.f)
    (hGP : polyPresentedAlgebraEquiv.{u} g
      (Ideal.Quotient.mk _ ((lastVarPolyEquiv.{u} n).symm G)) = P.g)
    (V : Opens (ULift.{u} (Fin n) → ℂ))
    (hV : (V : Set (ULift.{u} (Fin n) → ℂ)) ⊆ (hypersurfaceCommonZeroImage.{u} F G)ᶜ) :
    IsCoveringMap (AnalyticSpace.restrictHom
      (analytificationMap.{u} (etalePresHom.{u} g ((lastVarPolyEquiv.{u} n).symm F)
        ((lastVarPolyEquiv.{u} n).symm G)))
      ((Opens.map (analytificationInclHom.{u} g).toLRSHom.base).obj V)).toLRSHom.base :=
  haveI := isFiniteEtale_restrictHom_analytificationMap_etalePresHom.{u} g F G hF P hFP hGP V hV
  AnalyticSpace.isCoveringMap_base_of_isFiniteEtale _

/-- **The same at the largest open subset of `ℂ^n` there is**, the complement of the bad set,
matching `ComplexAnalytic.isFiniteEtale_restrictHom_analytificationMap_etalePresHom_compl`.

The theorem above at `subset_rfl`, with
`ComplexAnalytic.isClosed_hypersurfaceCommonZeroImage` for the openness: **a corollary of that
theorem and not a second application of the rung**, exactly as
`ComplexAnalytic.isCoveringMap_base_restrictHom_analytificationMap_etalePresHom_comp_compl` is of
its own predecessor. **It says nothing about whether that complement, or its preimage in `X^an`,
is nonempty**, and at `F = G = X` it is empty. -/
theorem isCoveringMap_base_restrictHom_analytificationMap_etalePresHom_compl (hF : F.Monic)
    (P : StandardEtalePair (PresentedAlgebra.{u} n k g))
    (hFP : polyPresentedAlgebraEquiv.{u} g
      (Ideal.Quotient.mk _ ((lastVarPolyEquiv.{u} n).symm F)) = P.f)
    (hGP : polyPresentedAlgebraEquiv.{u} g
      (Ideal.Quotient.mk _ ((lastVarPolyEquiv.{u} n).symm G)) = P.g) :
    IsCoveringMap (AnalyticSpace.restrictHom
      (analytificationMap.{u} (etalePresHom.{u} g ((lastVarPolyEquiv.{u} n).symm F)
        ((lastVarPolyEquiv.{u} n).symm G)))
      ((Opens.map (analytificationInclHom.{u} g).toLRSHom.base).obj
        ⟨(hypersurfaceCommonZeroImage.{u} F G)ᶜ,
          (isClosed_hypersurfaceCommonZeroImage.{u} F G hF).isOpen_compl⟩)).toLRSHom.base :=
  isCoveringMap_base_restrictHom_analytificationMap_etalePresHom.{u} g F G hF P hFP hGP _ subset_rfl

end

end ComplexAnalytic
