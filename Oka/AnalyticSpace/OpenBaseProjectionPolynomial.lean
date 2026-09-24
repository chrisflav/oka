/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.AnalyticSpace.OpenBaseProjection
import Oka.Polynomial.Germ

/-!
# Over an open base, from a derivative: the projection of a polynomial hypersurface of a cylinder

`Oka/AnalyticSpace/OpenBaseProjection.lean` carries the stalk half of *the analytification of a
standard étale morphism is finite étale* across a restriction of the base, and states it in two
hypotheses: an order condition on a germ, and — since this file's companion increment — one Taylor
coefficient of the entire function the hypersurface is cut out by. Neither is what a caller on the
standard étale line holds. That caller has a **polynomial**, because
`ComplexAnalytic.etalePresentation` cuts with polynomials and
`ComplexAnalytic.eval_pderiv_ne_zero` delivers exactly

```
MvPolynomial.eval y (MvPolynomial.pderiv (localisationVar n) F) ≠ 0
```

— a derivative at a point, with no germ in it. This file is the last rewrite: the same four
theorems at the same hypothesis, over an open subset of the base.

It is to `Oka/AnalyticSpace/OpenBaseProjection.lean` exactly what
`Oka/AnalyticSpace/SimpleZeroPolynomial.lean` is to `Oka/AnalyticSpace/SimpleZeroStalk.lean`, and
for the same reason: the content is `LocalOkaRing.coeff_single_one_ofMvPolynomial`, the statement
that the coefficient of `xᵢ` in the germ at `y` of a polynomial is `∂p/∂xᵢ` evaluated at `y`, and
that lemma is about polynomials and germs and knows nothing about a cylinder. The restriction
costs nothing here — it is absorbed once, in the coefficient form this file rewrites — which is
why the two proofs below are two lines each.

## Which point the derivative is evaluated at

At the **ambient** point. A point of the hypersurface is an `x : X`; `i.base x` is a point of the
cylinder subspace, a subtype; and the derivative is a polynomial function on the whole of
`ℂ^(n+1)`, so what it is evaluated at is
`((AnalyticSpace.complexAffineSpace (n + 1)).ofRestrict (cylinder V)).toLRSHom.base (i.base x)`,
the underlying tuple. That spelling is not decoration: it is the same one
`ComplexAnalytic.evalHom_eq_zero_of_isCutOutBy_resΓ` and
`ComplexAnalytic.cylinderStalkEquiv_Γgerm_resΓ` use, so a caller who has discharged the
non-vanishing at a tuple has it at exactly this term and not at one `rw` away from it.

## Main results

- `ComplexAnalytic.bijective_stalkMap_comp_projRestrict_of_pderiv` and
  `ComplexAnalytic.isIso_stalkMap_comp_projRestrict_of_pderiv`: **the projection to `V` of a
  polynomial hypersurface of the cylinder over `V` is an isomorphism on stalks at a point where
  the last partial derivative does not vanish.**

## What is not here

**No `IsLocalIso` and no `IsFiniteEtale`, and this file moves neither any closer than its imports
did.** `Oka/AnalyticSpace/SimpleZeroStalk.lean` says of its own conclusion that *"nothing below
says anything about the underlying map of `i ≫ p`, not even that it is open"*, and that is still
true here: the two results below are about stalks and the third field a local isomorphism needs is
topological. `Oka/AnalyticSpace/OpenBaseProjection.lean` says the same in its own
`## What is not here`, and adds why joining the two halves is not an argument of the same kind — a
monic family with repeated roots gives a composite that is not a local homeomorphism.

**Nothing about `D(G)`, and the open set is a hypothesis.** `V` is an arbitrary open subset of
`ℂ^n` here, exactly as in the file this one rewrites. The standard étale line inverts a polynomial
`G` in the **fibre** variable, which cuts an open set out of the *source* and not out of the base;
`Oka/Analytification/StandardEtaleAnalytification.lean` records that difference, and nothing below
produces a `V` from a `G` or claims that the two restrictions are the same one. What this file
settles is the part that was said to be unpriced — restating the transport at the derivative
hypothesis — and it is two rewrites; the choice of `V` is untouched by that and is still the open
question.

**No `ComplexAnalytic.IsCutOutBy` datum for a presentation.** Both results take a cut-out by a
**single** section, as all four of their unrestricted ancestors do, while
`ComplexAnalytic.hypersurfacePresentation` has `k + 1` relations.
**This bullet said `Oka/Analytification/StandardEtaleAnalytification.lean` *"records that as the
absence"* standing between `ComplexAnalytic.eval_pderiv_ne_zero`'s conclusion at a tuple and this
hypothesis at `i.base x`; that file now records it as a misdiagnosis instead** — the count is
right and the reading of it was wrong, the conclusion in question being about the projection to
`ℂ^n`, so `k + 1` against one is the signature of a statement whose base is the whole of `ℂ^n`.
At `k = 0` the datum is `ComplexAnalytic.isCutOutBy_analytificationInclHom_hypersurface`
(`Oka/Analytification/StandardEtaleLocalIso.lean`), stated there for `g : Fin 0 → _`; at `k ≥ 1`
what is missing is a statement and not a datum, since the conclusion those results reach is over
`ℂ^n`. **What has not changed is this file's own part in it**: this file does not supply that
datum, and it changes which hypothesis is asked for, not who supplies the datum.

**No second generality.** Every statement here is an instance of one in
`Oka/AnalyticSpace/OpenBaseProjection.lean`, so a consumer holding a general holomorphic cutting
section should use that file directly.
-/

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry Topology

universe u

noncomputable section

namespace ComplexAnalytic

variable {n : ℕ} (V : TopologicalSpace.Opens (ULift.{u} (Fin n) → ℂ))
  {X : LocallyRingedSpace.{u}}
  {i : X ⟶ ((AnalyticSpace.complexAffineSpace.{u} (n + 1)).restrict
    (cylinder V)).toLocallyRingedSpace}
  {P : MvPolynomial (ULift.{u} (Fin (n + 1))) ℂ}

/-- **The projection to `V` of a polynomial hypersurface of the cylinder over `V` is bijective on
stalks at a point where the last partial derivative does not vanish.**

`ComplexAnalytic.bijective_stalkMap_comp_projRestrict_of_coeff` with its Taylor coefficient read
as a derivative by `LocalOkaRing.coeff_single_one_ofMvPolynomial`; the step from the cutting
section to the germ is `LocalOkaRing.ofMvPolynomial_eq`, which is `rfl`. The vanishing of `P` at
the point is not a hypothesis: it comes from `hcut` through
`ComplexAnalytic.evalHom_eq_zero_of_isCutOutBy_resΓ`, inside the theorem this one calls.

The derivative is read at `ComplexAnalytic.localisationVar n`'s spelling of the last index —
`ULift.up (Fin.last n)` — so nothing has to be relabelled between here and
`ComplexAnalytic.eval_pderiv_ne_zero`. -/
theorem bijective_stalkMap_comp_projRestrict_of_pderiv
    (hcut : IsCutOutBy i ![(AnalyticSpace.complexAffineSpace.{u} (n + 1)).resΓ (cylinder V)
      (OkaRing.ofMvPolynomial ⊤ P)])
    (x : X)
    (hlin : MvPolynomial.eval
        (((AnalyticSpace.complexAffineSpace.{u} (n + 1)).ofRestrict
          (cylinder V)).toLRSHom.base (i.base x))
        (MvPolynomial.pderiv (ULift.up.{u} (Fin.last n)) P) ≠ 0) :
    Function.Bijective ((i ≫ (AnalyticSpace.projRestrict V).toLRSHom).stalkMap x).hom := by
  refine bijective_stalkMap_comp_projRestrict_of_coeff V hcut x ?_
  rw [← LocalOkaRing.ofMvPolynomial_eq, LocalOkaRing.coeff_single_one_ofMvPolynomial]
  exact hlin

/-- **The same as an isomorphism.** This is the form the Riemann-existence line consumes over an
open base: `ComplexAnalytic.AnalyticSpace` indexes its coordinates by `ULift (Fin _)`, and a
standard étale presentation is given by polynomials. -/
theorem isIso_stalkMap_comp_projRestrict_of_pderiv
    (hcut : IsCutOutBy i ![(AnalyticSpace.complexAffineSpace.{u} (n + 1)).resΓ (cylinder V)
      (OkaRing.ofMvPolynomial ⊤ P)])
    (x : X)
    (hlin : MvPolynomial.eval
        (((AnalyticSpace.complexAffineSpace.{u} (n + 1)).ofRestrict
          (cylinder V)).toLRSHom.base (i.base x))
        (MvPolynomial.pderiv (ULift.up.{u} (Fin.last n)) P) ≠ 0) :
    IsIso ((i ≫ (AnalyticSpace.projRestrict V).toLRSHom).stalkMap x) :=
  (ConcreteCategory.isIso_iff_bijective _).2
    (bijective_stalkMap_comp_projRestrict_of_pderiv V hcut x hlin)

end ComplexAnalytic

end
