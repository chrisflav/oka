/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.AnalyticSpace.CoveringMap
import Oka.AnalyticSpace.Hausdorff
import Oka.Analytification.StandardEtaleFiniteEtale

/-!
# The analytification is Hausdorff, and the standard étale cover is a covering map

`Oka/AnalyticSpace/Hausdorff.lean` makes the zero locus of holomorphic functions on an open subset
of `ℂ^n` Hausdorff. `ComplexAnalytic.AnalyticSpace.analytification` is such a zero locus — at
`V = ⊤`, with the polynomials read as holomorphic functions by `ComplexAnalytic.polySection` — so
it is one more `inferInstanceAs`, and that is the whole of the first declaration here.

**The second and third are what the first is for.**
`Oka/Analytification/StandardEtaleFiniteEtale.lean` proves that the analytification of a standard
étale morphism is finite étale over an open subset of the base, and its `## What is not here` ends
with a bullet saying that the covering-map rung is out of reach because
`ComplexAnalytic.AnalyticSpace.isCoveringMap_base_of_isFiniteEtale` *"needs a Hausdorff source and
it is not checked here"*. The source is
`(ComplexAnalytic.AnalyticSpace.analytification …).restrict …`, which the instance below and
`ComplexAnalytic.t2Space_restrict` reach, so the bullet closes and the corollary is a `haveI` and
an application.

## Why this is the second application of the third rung and the first outside a test file

The first is the squaring map of the punctured line, written by hand, with its separation
hypothesis supplied by a bespoke instance about that one space;
`Oka/Analytification/HausdorffBase.lean` later stated the `k ≥ 1` counterpart over `X^an` and
became the third application of the rung, which leaves where *this* file stands in that order
unchanged. The theorems below are about a morphism
the analytification machinery produces from a Mathlib `StandardEtalePair`, and their separation
hypothesis is found by instance search at a family rather than at a point — which is the
difference `Oka/AnalyticSpace/Hausdorff.lean` is for.

**Nothing about the covering is computed.** `IsCoveringMap` is a statement about the underlying
continuous map, so these say nothing about structure sheaves, nothing about how many sheets there
are, and nothing about whether the base is nonempty; the last of those is a live question about
`V`, and `Oka/Analytification/OpenBaseFiniteness.lean` is where it is discussed.

## What is not here

* **No degree, and no number of sheets.**
  `ComplexAnalytic.AnalyticSpace.card_fiber_eq_of_isFiniteEtale` would apply to the same morphism —
  its `[T2Space]` on the source is now discharged — but it also asks `[PreconnectedSpace]` of the
  base, and `V` is an arbitrary open subset of `ℂ^n` avoiding the bad set, which nothing here shows
  is preconnected or even nonempty. That is a second hypothesis and a second deliverable.
* **Nothing at `k ≥ 1`.** These are corollaries of
  `ComplexAnalytic.isFiniteEtale_restrictHom_analytificationMap_etalePresHom_comp` and inherit its
  `g : Fin 0 → …`, and nothing below is stated at a presented base. **The reason given for that
  read *the finiteness half over a presented base does not exist, so neither does this* until
  2026-09-21**, and it had been false since 2026-09-20, when `5888ddb` wrote that half and
  `ComplexAnalytic.isFiniteEtale_restrictHom_analytificationMap_etalePresHom`
  (`Oka/Analytification/StandardEtaleFiniteEtaleBase.lean`) with it. **The absence is unchanged
  and the ingredient the retired reason named is not.** What that half and that class are about is
  the structure map to `X^an`, and the two corollaries below are about the composite to `ℂ^n` —
  **two morphisms and not one**, in `Oka/Analytification/StandardEtaleFiniteness.lean`'s words,
  with `Oka/Analytification/StandardEtaleFiniteEtale.lean` saying the same of the same two
  morphisms. So what was reachable and unstated was the `k ≥ 1` counterpart **over `X^an`**,
  which is a different statement from the two below rather than their generalisation. **That
  clause ended *and stating it is a deliverable* until 2026-09-21**, when
  `Oka/Analytification/HausdorffBase.lean` stated it —
  `ComplexAnalytic.isCoveringMap_base_restrictHom_analytificationMap_etalePresHom` and its
  `_compl` companion, a sibling module rather than an append because appending would put six
  modules onto this file's closure, which that file measures. **The absence this bullet records is
  unchanged**: nothing *below* is stated at a presented base, and that is still what it says.
  **Over `ℂ^n` at `k ≥ 1` the statement is not merely unstated**: the
  *unrestricted* composite is not a local isomorphism — and so, by
  `ComplexAnalytic.AnalyticSpace.IsFiniteEtale.isLocalIso`, not finite étale — as soon as some
  `g j` is nonzero and the source has a point, by
  `ComplexAnalytic.not_isLocalIso_analytificationMap_etalePresHom_comp`
  (`Oka/Analytification/StandardEtaleNotLocalIso.lean`).
* **Nothing about the unrestricted morphism.** It is not finite étale, so there is no covering-map
  statement to make about it, and the restriction to `V` is not an artefact of this file.
* **No comparison functor and no Riemann existence theorem**, and no covering-map statement about
  the analytification of a finite étale morphism of schemes: everything here is one standard étale
  presentation over `ℂ^n`.

## Main results

- `ComplexAnalytic.t2Space_analytification`: **the analytification of a tuple of polynomials is
  Hausdorff.**
- `ComplexAnalytic.isCoveringMap_base_restrictHom_analytificationMap_etalePresHom_comp` and
  `ComplexAnalytic.isCoveringMap_base_restrictHom_analytificationMap_etalePresHom_comp_compl`:
  **the analytification of a standard étale morphism over `ℂ^n` is a covering map over an open
  subset of the base avoiding the bad set**, and at the complement of the bad set itself.
-/

open CategoryTheory MvPolynomial AlgebraicGeometry TopologicalSpace Opposite Topology

universe u

namespace ComplexAnalytic

/-- **The analytification of a tuple of polynomials is Hausdorff.**

`ComplexAnalytic.AnalyticSpace.analytification` is `ComplexAnalytic.AnalyticSpace.zeroLocus ⊤`
of the tuple read as holomorphic functions, so this is `ComplexAnalytic.t2Space_zeroLocus` at that
spelling; the `def` in between is what stops instance search from getting there on its own. -/
instance t2Space_analytification {n k : ℕ} (g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ) :
    T2Space (AnalyticSpace.analytification.{u} g : Type u) :=
  inferInstanceAs (T2Space (AnalyticSpace.zeroLocus.{u} ⊤ (polySection.{u} g)))

noncomputable section

variable {n : ℕ} (g : Fin 0 → MvPolynomial (ULift.{u} (Fin n)) ℂ)
  (F G : Polynomial (MvPolynomial (ULift.{u} (Fin n)) ℂ))

/-- **The analytification of a standard étale morphism over `ℂ^n` is a covering map over an open
subset of the base avoiding the bad set.**

`ComplexAnalytic.isFiniteEtale_restrictHom_analytificationMap_etalePresHom_comp` is the whole of
the input, and the separation hypothesis of
`ComplexAnalytic.AnalyticSpace.isCoveringMap_base_of_isFiniteEtale` is found by instance search:
the source is an open subspace of `ComplexAnalytic.AnalyticSpace.analytification`, which
`ComplexAnalytic.t2Space_analytification` and `ComplexAnalytic.t2Space_restrict` reach.

The hypotheses are the finite-étale theorem's and they are not redistributed here: `hF` and `hV`
buy finiteness, `P`, `hFP` and `hGP` buy the local isomorphism, and the covering-map rung reads
both fields and no separation of the base. -/
theorem isCoveringMap_base_restrictHom_analytificationMap_etalePresHom_comp (hF : F.Monic)
    (P : StandardEtalePair (PresentedAlgebra.{u} n 0 g))
    (hFP : polyPresentedAlgebraEquiv.{u} g
      (Ideal.Quotient.mk _ ((lastVarPolyEquiv.{u} n).symm F)) = P.f)
    (hGP : polyPresentedAlgebraEquiv.{u} g
      (Ideal.Quotient.mk _ ((lastVarPolyEquiv.{u} n).symm G)) = P.g)
    (V : Opens (ULift.{u} (Fin n) → ℂ))
    (hV : (V : Set (ULift.{u} (Fin n) → ℂ)) ⊆ (hypersurfaceCommonZeroImage.{u} F G)ᶜ) :
    IsCoveringMap (AnalyticSpace.restrictHom
      (analytificationMap.{u} (etalePresHom.{u} g ((lastVarPolyEquiv.{u} n).symm F)
        ((lastVarPolyEquiv.{u} n).symm G)) ≫ analytificationInclHom.{u} g)
      V).toLRSHom.base :=
  haveI := isFiniteEtale_restrictHom_analytificationMap_etalePresHom_comp.{u} g F G hF P hFP hGP
    V hV
  AnalyticSpace.isCoveringMap_base_of_isFiniteEtale _

/-- **The same at the largest open subset there is**, the complement of the bad set, matching
`ComplexAnalytic.isFiniteEtale_restrictHom_analytificationMap_etalePresHom_comp_compl`.

**It says nothing about whether that open subset is nonempty**, and at `F = G = X` it is empty, so
this is not on its own evidence that anything is covered; see
`Oka/Analytification/OpenBaseFiniteness.lean`. -/
theorem isCoveringMap_base_restrictHom_analytificationMap_etalePresHom_comp_compl (hF : F.Monic)
    (P : StandardEtalePair (PresentedAlgebra.{u} n 0 g))
    (hFP : polyPresentedAlgebraEquiv.{u} g
      (Ideal.Quotient.mk _ ((lastVarPolyEquiv.{u} n).symm F)) = P.f)
    (hGP : polyPresentedAlgebraEquiv.{u} g
      (Ideal.Quotient.mk _ ((lastVarPolyEquiv.{u} n).symm G)) = P.g) :
    IsCoveringMap (AnalyticSpace.restrictHom
      (analytificationMap.{u} (etalePresHom.{u} g ((lastVarPolyEquiv.{u} n).symm F)
        ((lastVarPolyEquiv.{u} n).symm G)) ≫ analytificationInclHom.{u} g)
      ⟨(hypersurfaceCommonZeroImage.{u} F G)ᶜ,
        (isClosed_hypersurfaceCommonZeroImage.{u} F G hF).isOpen_compl⟩).toLRSHom.base :=
  isCoveringMap_base_restrictHom_analytificationMap_etalePresHom_comp.{u} g F G hF P hFP hGP _
    subset_rfl

end

end ComplexAnalytic
