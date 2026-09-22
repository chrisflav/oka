/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Analytification.StandardEtaleFiniteness
import Oka.Analytification.StandardEtaleLocalIso

/-!
# The analytification of a standard étale morphism is finite étale over an open subset of the base

`ComplexAnalytic.AnalyticSpace.IsFiniteEtale` is two fields and nothing else, and at an empty base
presentation this repository has had both for two files without ever putting them together:

* `ComplexAnalytic.isFinite_restrictHom_analytificationMap_etalePresHom_comp`
  (`Oka/Analytification/StandardEtaleFiniteness.lean`) is the finiteness, **of the morphism
  restricted over `V`**;
* `ComplexAnalytic.isLocalIso_analytificationMap_etalePresHom_comp`
  (`Oka/Analytification/StandardEtaleLocalIso.lean`) is the local isomorphism, **of the
  unrestricted morphism**.

The two are stated about different morphisms, and that is not an oversight in either file:
unrestricted finiteness is **false**, and
`Oka/Analytification/MonicHypersurface.lean` carries the counterexample in terms — compiled since
2026-09-02 as `ComplexAnalytic.not_isFinite_condEtaleProj`
(`OkaTest/StandardEtaleNotFinite.lean`), which is what makes *"stated about different morphisms"*
a measurement rather than a reading. So the class can only be
claimed for the restricted morphism, and what was missing was the second field *at the
restriction* — which is `ComplexAnalytic.AnalyticSpace.isLocalIso_restrictHom`
(`Oka/AnalyticSpace/OpenSubspace.lean`), a general fact about open subspaces with nothing étale in
it. Both files record the absence of that transport, in terms, and this file is what retires it.

## The asymmetry is the content, and a reader of the theorem alone cannot see it

The two fields are bought by two different hypotheses, and neither buys the other:

* **`IsFinite` needs `V`**, and needs only that `F` is monic. It is false without the restriction
  and it reads nothing about `G` beyond the bad set.
  `Oka/Analytification/StandardEtaleFiniteness.lean` is explicit that it holds for *every*
  monic `F` and *every* `G`.
* **`IsLocalIso` needs the pair to be étale**, through
  `Mathlib.RingTheory.Etale.StandardEtale`'s `StandardEtalePair` and its `cond` field, and needs
  no restriction at all — it is true of the unrestricted morphism, and
  `ComplexAnalytic.AnalyticSpace.isLocalIso_restrictHom` carries it down to `V` for free.

So this theorem's hypotheses are the *union* of the two halves' and its conclusion is about the
restricted morphism only. **Neither hypothesis is removable**: dropping `V` makes the first field
false, and dropping the `StandardEtalePair` leaves a morphism this development says nothing about
on stalks.

## Main results

- `ComplexAnalytic.isFiniteEtale_restrictHom_analytificationMap_etalePresHom_comp`: **the
  analytification of a standard étale morphism over affine space, restricted over an open subset
  of the base avoiding the bad set, is finite étale.** This is the whole of taxis #1112's §1 at an
  empty base presentation.
- `ComplexAnalytic.isFiniteEtale_restrictHom_analytificationMap_etalePresHom_comp_compl`: the same
  at the largest such open subset, the complement of
  `ComplexAnalytic.hypersurfaceCommonZeroImage`, which is open by
  `ComplexAnalytic.isClosed_hypersurfaceCommonZeroImage`.

## Placement, and it was priced against appending to the finiteness file

`Oka/Analytification/StandardEtaleFiniteness.lean` is where the issue that asked for this expected
it, and the cost was measured both ways with `lake env lean` on the environment's own
`getEnv.header.moduleNames`, counting modules under `Oka/` and `Mathlib/` — the convention
`Oka/AnalyticSpace/OpenSubspace.lean` states and `scripts/import_cost.py` documents:

* appending there and adding the `Oka.Analytification.StandardEtaleLocalIso` edge takes that
  file's closure from **3473 to 3480**, and the seven are named:
  `Oka.Analytification.StandardEtaleLocalIso`, `Oka.AnalyticSpace.SimpleZeroTopology`,
  `Oka.AnalyticSpace.SimpleZeroPolynomial`, `Oka.GermDerivative`, `Oka.Analysis.Calculus.Implicit`,
  `Mathlib.Analysis.Calculus.Implicit`, `Mathlib.Analysis.Normed.Module.Complemented`;
* this file's own closure is **3481**, which is the same seven plus itself.

Each figure counts the module **and** its transitive imports, so the edge is `+7` either way.
They are **environment** counts and the distinction is not pedantry: a text-based walk over the
header lines, even one using `scripts/import_cost.py`'s comment-stripped extractor, comes out
about twenty low on a closure this size while reproducing the delta and the named set exactly.
Quote the delta from either instrument; quote an absolute only from the environment.

**So cost decides nothing** — both are leaves, imported by `Oka.lean` alone and by no module under
`OkaTest/`, so neither shape adds a build to the library and the seven modules are already built
for `Oka.lean` in either case.

**What decided it is a sentence in the other file that this theorem would falsify.**
`Oka/Analytification/StandardEtaleFiniteness.lean`'s `## What is not here` says *"No
`StandardEtalePair`, and no `StandardEtalePair.cond` is read. The theorems below hold for **every**
monic `F` and **every** `G`"*. That is a stance and not merely an absence: it says what that file's
theorems cost, and it is the reason its finiteness is reusable at pairs that are not étale. This
theorem reads a `StandardEtalePair`, so appending it there would have turned that paragraph into
*"every theorem below except one"*. A separate module keeps the weaker statement's file weak.

## What is not here

* **No `IsFiniteEtale` of the unrestricted morphism**, and there never will be: it is **false**,
  `Oka/Analytification/MonicHypersurface.lean` carries the witness and
  `ComplexAnalytic.not_isFiniteEtale_condEtaleProj` (`OkaTest/StandardEtaleNotFinite.lean`)
  compiles it, and nothing in this file narrows that. The restriction is in the statement because
  the first field needs it.
* **Nothing at `k ≥ 1`.** Both halves are at an empty base presentation, for the reasons their own
  files give, and a presented base is a different theorem rather than a missing hypothesis. **The
  local-isomorphism half of that different theorem now exists** —
  `ComplexAnalytic.isLocalIso_analytificationMap_etalePresHom`
  (`Oka/Analytification/StandardEtaleLocalIsoBase.lean`), at every `k`, and about the structure
  map to `X^an` rather than the projection to `ℂ^n`. **So does the finiteness half** —
  `ComplexAnalytic.isFinite_restrictHom_analytificationMap_etalePresHom`
  (`Oka/Analytification/StandardEtaleFinitenessBase.lean`) — and so does the class, as
  `ComplexAnalytic.isFiniteEtale_restrictHom_analytificationMap_etalePresHom`
  (`Oka/Analytification/StandardEtaleFiniteEtaleBase.lean`), which is this theorem's counterpart
  and not its generalisation: the morphism there is the structure map to `X^an` and the morphism
  here is the composite to `ℂ^n`, which is false at `k ≥ 1`. **This bullet closed on *The
  finiteness half at `k ≥ 1` is untouched, so this bullet stands for the class as a whole* until
  2026-09-20**, when that half and that class were written. What it says about *this* file is
  unchanged: nothing below is at `k ≥ 1`.
* **Nothing about how large `V` is *here*, and the class is now instantiated elsewhere at a `V`
  that is proper and nonempty.** This bullet said no pair `(F, G)` was exhibited anywhere for
  which `V` is proper *and* nonempty; one is —
  `ComplexAnalytic.hypersurfaceCommonZeroImage_parabola`
  (`Oka/Analytification/OpenBaseFiniteness.lean`), instantiated for the finiteness half as
  `ComplexAnalytic.isFinite_restrictHom_analytificationMap_etalePresHom_comp_parabola`.

  **It then said the parabola is *not* instantiated for this class, *"because the second field
  needs a `StandardEtalePair` and nothing exhibits the parabola as one"*, and that reason was
  false when it was written.** `ComplexAnalytic.condPair` (`OkaTest/StandardEtaleCond.lean`) *is*
  the parabola, at `n = 1` and `i = 0`, in the multivariate vocabulary rather than the polynomial
  one; `ComplexAnalytic.condPair` predates this bullet by 1d 22h and the parabola by 1d 23h, and
  nobody read them against each other. **This bullet is 1h 14m older than the parabola**, so the
  two intervals are not the same one: the pair is `5ae9ed5`, this bullet was first written at
  `868ed5f`, and the parabola and the clause just quoted arrived together at `028808f`.
  `ComplexAnalytic.isFiniteEtale_restrictHom_condEtaleProj`
  (`OkaTest/CondFiniteEtale.lean`) is the theorem below at that pair, and the `V` it holds over is
  the punctured line — proper and nonempty, by
  `ComplexAnalytic.condGoodOpen_nonempty` and `ComplexAnalytic.condGoodOpen_ne_univ`. **The same
  morphism unrestricted is not finite étale**, which is
  `ComplexAnalytic.not_isFiniteEtale_condEtaleProj` (`OkaTest/StandardEtaleNotFinite.lean`), and
  neither is its restriction over `⊤`, which is
  `ComplexAnalytic.not_isFiniteEtale_restrictHom_condEtaleProj_top` in the same file as the
  positive half — so the two sides of the comparison are the restriction below at two opens, and
  the hypothesis on `V` is doing visible work at one compiled instance.

  **What stays true is the last clause and it is the one that matters here**: the size of `V`
  remains a hypothesis on the pair rather than a theorem, nothing below bounds it, and the
  instance is in the test library rather than in this one — a reader of the theorem below alone
  still cannot conclude that the morphism is finite étale over anything in particular.
* **No comparison functor and no Riemann existence theorem.** A *different and broader* absence —
  the analytification of a finite étale morphism of **schemes** — is what
  `Oka/AnalyticSpace/LocalIso.lean`, `Oka/AnalyticSpace/CoveringMap.lean` and
  `Oka/AnalyticSpace/SigmaFiniteEtale.lean` record, and nothing here touches it: everything on
  this line is one standard étale presentation — over `ℂ^n` here, and over a presented base in
  `Oka/Analytification/StandardEtaleLocalIsoBase.lean`,
  `Oka/Analytification/StandardEtaleFinitenessBase.lean` and
  `Oka/Analytification/StandardEtaleFiniteEtaleBase.lean` — and the general morphism is a
  Zariski-local gluing that nothing starts. **The base is not what separates the two absences**:
  the broader one asks about a finite étale morphism of schemes where this line asks about a
  standard étale pair, and it stays absent at every base. **This clause read *everything on this
  line is one standard étale presentation over `ℂ^n`* until 2026-09-22**, which was true at
  `868ed5f` and was falsified by `5888ddb` on 2026-09-20 — the landing dated by the bullet headed
  *Nothing at `k ≥ 1`* above, which put the local-isomorphism half, the finiteness half and the
  class at a presented base;
  `git show cb5a40e:Oka/Analytification/StandardEtaleFiniteEtale.lean` carries the retired wording
  at `:149–150`, wrapped after *everything on*.
* **No `IsCoveringMap` *here*, and it is no longer absent.** This bullet said
  `ComplexAnalytic.AnalyticSpace.isCoveringMap_base_of_isFiniteEtale` *"needs a Hausdorff source
  and it is not checked here"*. The source of the theorem below is an open subspace of
  `ComplexAnalytic.AnalyticSpace.analytification`, and `Oka/AnalyticSpace/Hausdorff.lean` and
  `Oka/Analytification/Hausdorff.lean` between them make that an instance rather than a check, so
  `ComplexAnalytic.isCoveringMap_base_restrictHom_analytificationMap_etalePresHom_comp` is the
  theorem below plus that rung and costs a `haveI`. It is stated in
  `Oka/Analytification/Hausdorff.lean` and not appended here, because the instances it consumes
  are what it is a corollary of and this file imports neither of them.
-/

open CategoryTheory MvPolynomial AlgebraicGeometry TopologicalSpace Opposite Topology

universe u

namespace ComplexAnalytic

noncomputable section

variable {n : ℕ} (g : Fin 0 → MvPolynomial (ULift.{u} (Fin n)) ℂ)
  (F G : Polynomial (MvPolynomial (ULift.{u} (Fin n)) ℂ))

/-- **The analytification of a standard étale morphism over `ℂ^n` is finite étale over an open
subset of the base avoiding the bad set.**

The two fields are the two halves and nothing is done between them: `isFinite` is
`ComplexAnalytic.isFinite_restrictHom_analytificationMap_etalePresHom_comp` verbatim, and
`isLocalIso` is `ComplexAnalytic.isLocalIso_analytificationMap_etalePresHom_comp` carried across
the restriction by `ComplexAnalytic.AnalyticSpace.isLocalIso_restrictHom`.

**Which hypothesis buys which field is the whole content and is worth reading off the proof.**
`hF` and `hV` are the first field's and are not read by the second; `P`, `hFP` and `hGP` are the
second field's and are not read by the first. The restriction is asked for by the first field
alone — the second holds of the unrestricted morphism — and it is not removable, since
unrestricted finiteness is false.

**The morphism is passed to `ComplexAnalytic.AnalyticSpace.isLocalIso_restrictHom` explicitly, and
that is forced.** Written with a `_` there the declaration fails with *"(deterministic) timeout at
`isDefEq`"* at the default budget, measured: elaboration has to unify `restrictHom ?f V` against a
goal whose source is spelled through `Opens.map`, which is the same `Opens`-spelling seam
`Oka/Analytification/StandardEtaleFiniteness.lean` records twice and
`ComplexAnalytic.AnalyticSpace.isLocalIso_restrictHom` a third time. **It is the `_` that costs and
not the structure syntax** — with the morphism named, both the `where` form and an anonymous
constructor compile. -/
theorem isFiniteEtale_restrictHom_analytificationMap_etalePresHom_comp (hF : F.Monic)
    (P : StandardEtalePair (PresentedAlgebra.{u} n 0 g))
    (hFP : polyPresentedAlgebraEquiv.{u} g
      (Ideal.Quotient.mk _ ((lastVarPolyEquiv.{u} n).symm F)) = P.f)
    (hGP : polyPresentedAlgebraEquiv.{u} g
      (Ideal.Quotient.mk _ ((lastVarPolyEquiv.{u} n).symm G)) = P.g)
    (V : Opens (ULift.{u} (Fin n) → ℂ))
    (hV : (V : Set (ULift.{u} (Fin n) → ℂ)) ⊆ (hypersurfaceCommonZeroImage.{u} F G)ᶜ) :
    AnalyticSpace.IsFiniteEtale (AnalyticSpace.restrictHom
      (analytificationMap.{u} (etalePresHom.{u} g ((lastVarPolyEquiv.{u} n).symm F)
        ((lastVarPolyEquiv.{u} n).symm G)) ≫ analytificationInclHom.{u} g) V) where
  isFinite := isFinite_restrictHom_analytificationMap_etalePresHom_comp.{u} g F G hF V hV
  isLocalIso :=
    haveI := isLocalIso_analytificationMap_etalePresHom_comp.{u} g
      ((lastVarPolyEquiv.{u} n).symm F) ((lastVarPolyEquiv.{u} n).symm G) P hFP hGP
    AnalyticSpace.isLocalIso_restrictHom.{u}
      (analytificationMap.{u} (etalePresHom.{u} g ((lastVarPolyEquiv.{u} n).symm F)
        ((lastVarPolyEquiv.{u} n).symm G)) ≫ analytificationInclHom.{u} g) V

/-- **The same at the largest open subset there is**, the complement of the bad set.

`ComplexAnalytic.isFinite_restrictHom_analytificationMap_etalePresHom_comp_compl` is the finiteness
half at this `V` and this is its finite-étale strengthening; monicity is what makes the complement
open, through `ComplexAnalytic.isClosed_hypersurfaceCommonZeroImage`.

**It says nothing about whether that open subset is nonempty**, and at `F = G = X` it is empty;
see this file's `## What is not here` and `Oka/Analytification/OpenBaseFiniteness.lean`. -/
theorem isFiniteEtale_restrictHom_analytificationMap_etalePresHom_comp_compl (hF : F.Monic)
    (P : StandardEtalePair (PresentedAlgebra.{u} n 0 g))
    (hFP : polyPresentedAlgebraEquiv.{u} g
      (Ideal.Quotient.mk _ ((lastVarPolyEquiv.{u} n).symm F)) = P.f)
    (hGP : polyPresentedAlgebraEquiv.{u} g
      (Ideal.Quotient.mk _ ((lastVarPolyEquiv.{u} n).symm G)) = P.g) :
    AnalyticSpace.IsFiniteEtale (AnalyticSpace.restrictHom
      (analytificationMap.{u} (etalePresHom.{u} g ((lastVarPolyEquiv.{u} n).symm F)
        ((lastVarPolyEquiv.{u} n).symm G)) ≫ analytificationInclHom.{u} g)
      ⟨(hypersurfaceCommonZeroImage.{u} F G)ᶜ,
        (isClosed_hypersurfaceCommonZeroImage.{u} F G hF).isOpen_compl⟩) :=
  isFiniteEtale_restrictHom_analytificationMap_etalePresHom_comp.{u} g F G hF P hFP hGP _ subset_rfl

end

end ComplexAnalytic
