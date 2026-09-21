/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Analytification.StandardEtaleFinitenessBase

/-!
# The analytification of a standard étale morphism over a presented base is finite étale over an
open

`ComplexAnalytic.AnalyticSpace.IsFiniteEtale` is two fields, and at a presented base this
repository now has both:

* `ComplexAnalytic.isFinite_restrictHom_analytificationMap_etalePresHom`
  (`Oka/Analytification/StandardEtaleFinitenessBase.lean`) is the finiteness, **of the morphism
  restricted over the part of `X^an` lying above an open subset of `ℂ^n` avoiding the bad set**;
* `ComplexAnalytic.isLocalIso_analytificationMap_etalePresHom`
  (`Oka/Analytification/StandardEtaleLocalIsoBase.lean`) is the local isomorphism, **of the
  unrestricted morphism**, at every `k`.

This file puts them together. `Oka/Analytification/StandardEtaleFiniteEtale.lean` is the same
assembly at an empty base presentation, where the morphism is the composite to `ℂ^n`; **that file
and this one are two theorems and not one, because the two halves they assemble are about two
different morphisms** — the composite to `ℂ^n` there and the structure map to `X^an` here — and
the first is false at `k ≥ 1`.

## Why the assembly is a file of its own, which is the `k = 0` argument said again

`Oka/Analytification/StandardEtaleFiniteEtale.lean`'s header gives the reason and it applies
unchanged: the finiteness half reads no `StandardEtalePair` and therefore holds at
every pair `(F, G)` with `F` monic, which is what makes it reusable at pairs that are not étale;
the assembly reads one. Keeping the weaker statement's file weak is what a separate module buys,
and the cost is one import edge that adds nothing — this file's only import is
`Oka.Analytification.StandardEtaleFinitenessBase`, whose closure carries the local-isomorphism
half already.

## Which hypothesis buys which field

`hF` and `hV` are the first field's and are not read by the second; `P`, `hFP` and `hGP` are the
second field's and are not read by the first. **The restriction is asked for by the first field
alone** — the second holds of the unrestricted morphism — and it is not removable, since
unrestricted finiteness is false at `k = 0` already.

## Main results

- `ComplexAnalytic.isFiniteEtale_restrictHom_analytificationMap_etalePresHom`: **the
  analytification of a standard étale morphism over a presented base is finite étale over the part
  of `X^an` lying above an open subset of `ℂ^n` avoiding the bad set.**
- `ComplexAnalytic.isFiniteEtale_restrictHom_analytificationMap_etalePresHom_compl`: the same at
  the complement of the bad set.

## What is not here

* **No unrestricted `ComplexAnalytic.AnalyticSpace.IsFiniteEtale`**, and there never will be: it
  is false, `Oka/Analytification/MonicHypersurface.lean` carries the witness and
  `ComplexAnalytic.not_isFiniteEtale_condEtaleProj` (`OkaTest/StandardEtaleNotFinite.lean`)
  compiles it.
* **No instance of the class below *here*, and the absence this bullet recorded is retired.**
  Nothing in this file instantiates anything — the second hypothesis of the finiteness half, an
  open subset of `ℂ^n` avoiding the bad set, is a condition on the pair that nothing below bounds
  — but `OkaTest/StandardEtaleFiniteEtaleBase.lean` now instantiates the conjunction at `k = 1`,
  over the node and at `ComplexAnalytic.sqSubOneTwoPair`. **This bullet closed on *Whether that
  open subset is non-empty at any `k ≥ 1` pair is proved nowhere* until 2026-09-20**, when
  `ComplexAnalytic.hypersurfaceCommonZeroImage_sqSubOneTwoPair` made the bad set of that pair
  **empty**, so that the open subset is not merely non-empty but everything and the restriction
  comes off by `ComplexAnalytic.AnalyticSpace.isFiniteEtale_of_restrictHom_top`. **That is not an
  exception to the bullet above**: `g = 2` inverts nothing over a `ℂ`-algebra, so there is no
  localisation at that pair for the restriction to be necessary for, and the unrestricted class
  quantified over pairs is still false. What is still proved nowhere is a `k ≥ 1` pair at which
  the open subset is **proper** and non-empty, which is the only case in which the restriction
  both removes something and leaves something.
* **No comparison functor and no Riemann existence theorem.** Taxis #1113's functor consumes the
  statement below and is not here.
* **Nothing about a general étale morphism**, for the reason
  `Oka/Analytification/StandardEtaleFinitenessBase.lean` gives.
-/

open CategoryTheory MvPolynomial AlgebraicGeometry TopologicalSpace Opposite Topology

universe u

namespace ComplexAnalytic

noncomputable section

variable {n k : ℕ} (g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ)
  (F G : Polynomial (MvPolynomial (ULift.{u} (Fin n)) ℂ))

/-- **The analytification of a standard étale morphism over a presented base is finite étale over
the part of `X^an` lying above an open subset of `ℂ^n` avoiding the bad set.**

The two fields are the two halves and nothing is done between them: `isFinite` is
`ComplexAnalytic.isFinite_restrictHom_analytificationMap_etalePresHom` verbatim, and `isLocalIso`
is `ComplexAnalytic.isLocalIso_analytificationMap_etalePresHom` carried across the restriction by
`ComplexAnalytic.AnalyticSpace.isLocalIso_restrictHom`.

**The morphism is passed to `ComplexAnalytic.AnalyticSpace.isLocalIso_restrictHom` explicitly**,
for the reason `Oka/Analytification/StandardEtaleFiniteEtale.lean` records of its own assembly:
with a `_` there, elaboration has to unify `restrictHom ?f V` against a goal whose source is
spelled through `Opens.map`. -/
theorem isFiniteEtale_restrictHom_analytificationMap_etalePresHom (hF : F.Monic)
    (P : StandardEtalePair (PresentedAlgebra.{u} n k g))
    (hFP : polyPresentedAlgebraEquiv.{u} g
      (Ideal.Quotient.mk _ ((lastVarPolyEquiv.{u} n).symm F)) = P.f)
    (hGP : polyPresentedAlgebraEquiv.{u} g
      (Ideal.Quotient.mk _ ((lastVarPolyEquiv.{u} n).symm G)) = P.g)
    (V : Opens (ULift.{u} (Fin n) → ℂ))
    (hV : (V : Set (ULift.{u} (Fin n) → ℂ)) ⊆ (hypersurfaceCommonZeroImage.{u} F G)ᶜ) :
    AnalyticSpace.IsFiniteEtale (AnalyticSpace.restrictHom
      (analytificationMap.{u} (etalePresHom.{u} g ((lastVarPolyEquiv.{u} n).symm F)
        ((lastVarPolyEquiv.{u} n).symm G)))
      ((Opens.map (analytificationInclHom.{u} g).toLRSHom.base).obj V)) where
  isFinite := isFinite_restrictHom_analytificationMap_etalePresHom.{u} g F G hF V hV
  isLocalIso :=
    haveI := isLocalIso_analytificationMap_etalePresHom.{u} g ((lastVarPolyEquiv.{u} n).symm F)
      ((lastVarPolyEquiv.{u} n).symm G) P hFP hGP
    AnalyticSpace.isLocalIso_restrictHom.{u}
      (analytificationMap.{u} (etalePresHom.{u} g ((lastVarPolyEquiv.{u} n).symm F)
        ((lastVarPolyEquiv.{u} n).symm G)))
      ((Opens.map (analytificationInclHom.{u} g).toLRSHom.base).obj V)

/-- **The same over the largest open subset of `ℂ^n` there is**, the complement of the bad set.

The theorem above at `subset_rfl`, with
`ComplexAnalytic.isClosed_hypersurfaceCommonZeroImage` for the openness. **It says nothing about
whether that complement, or its preimage in `X^an`, is non-empty.** -/
theorem isFiniteEtale_restrictHom_analytificationMap_etalePresHom_compl (hF : F.Monic)
    (P : StandardEtalePair (PresentedAlgebra.{u} n k g))
    (hFP : polyPresentedAlgebraEquiv.{u} g
      (Ideal.Quotient.mk _ ((lastVarPolyEquiv.{u} n).symm F)) = P.f)
    (hGP : polyPresentedAlgebraEquiv.{u} g
      (Ideal.Quotient.mk _ ((lastVarPolyEquiv.{u} n).symm G)) = P.g) :
    AnalyticSpace.IsFiniteEtale (AnalyticSpace.restrictHom
      (analytificationMap.{u} (etalePresHom.{u} g ((lastVarPolyEquiv.{u} n).symm F)
        ((lastVarPolyEquiv.{u} n).symm G)))
      ((Opens.map (analytificationInclHom.{u} g).toLRSHom.base).obj
        ⟨(hypersurfaceCommonZeroImage.{u} F G)ᶜ,
          (isClosed_hypersurfaceCommonZeroImage.{u} F G hF).isOpen_compl⟩)) :=
  isFiniteEtale_restrictHom_analytificationMap_etalePresHom.{u} g F G hF P hFP hGP _ subset_rfl

end

end ComplexAnalytic
