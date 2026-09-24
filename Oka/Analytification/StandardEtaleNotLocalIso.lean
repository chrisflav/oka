/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Analytification.StandardEtale
import Oka.AnalyticSpace.LocalIso
import Oka.Algebra.MvPolynomial.Funext

/-!
# The standard étale projection to `ℂ^n` is not a local isomorphism over a presented base

`Oka/Analytification/StandardEtaleLocalIso.lean` proves
`ComplexAnalytic.isLocalIso_analytificationMap_etalePresHom_comp`: at `k = 0` the analytification
of a standard étale morphism, followed by the inclusion of the base into `ℂ^n`, is a local
isomorphism onto `ℂ^n`. That file's own header says what happens at `k ≥ 1`, and says it as an
argument rather than as a theorem:

> The conclusion of that theorem is about the projection to `ℂ^n`, and for `k ≥ 1` it fails —
> **whenever the base's analytification `X^an` is a proper closed subset of `ℂ^n`** — unless the
> hypersurface's analytification is empty. … What closes it is that the image is **open**.

`Oka/Analytification/StandardEtaleAnalytification.lean` carries a second copy of that argument, on
purpose, and `Oka/Analytification/StandardEtaleLocalIsoBase.lean` states its conclusion in
passing. **This file compiles it.** Nothing else here; the positive `k ≥ 1` statement — that the
analytification of a standard étale morphism over a presented base is a local isomorphism onto
**that base** — is `ComplexAnalytic.isLocalIso_analytificationMap_etalePresHom`
(`Oka/Analytification/StandardEtaleLocalIsoBase.lean`) and is untouched.

## The two hypotheses are the prose's, restated so they are checkable

* **Proper** becomes `∃ j, g j ≠ 0`. The zero locus of `g` is a proper subset of `ℂ^n` exactly
  when some relation is a non-zero polynomial, and that is what the argument consumes: the last
  step produces `g j = 0` for the `j` chosen and contradicts it. *Proper* is a hypothesis at
  `k ≥ 1` and not a consequence of it — `Oka/Analytification/StandardEtaleLocalIso.lean` says so
  in terms, and at `g = 0` the conclusion below is **false**, since the base's analytification is
  then the whole of `ℂ^n` and the composite is a local isomorphism.
* **Unless empty** becomes a `Nonempty` on the source. Both fields of
  `ComplexAnalytic.AnalyticSpace.IsLocalIso` quantify over the points of the source, so a morphism
  out of an empty space satisfies them and no argument about its image can refute it.

**At `k = 0` the first hypothesis is unsatisfiable**, `Fin 0` being empty, so this theorem says
nothing there and does not contradict
`ComplexAnalytic.isLocalIso_analytificationMap_etalePresHom_comp` — which is a theorem about
exactly that case. The two are stated at the same composite and their hypotheses are disjoint.

## The argument, and where each step comes from

1. A local isomorphism is a local homeomorphism —
   `ComplexAnalytic.AnalyticSpace.IsLocalIso.isLocalHomeomorph` — hence an open map, hence its
   range is **open**. `IsLocalHomeomorph.isOpenMap` and `IsOpenMap.isOpen_range` are Mathlib's.
2. The range is contained in the zero locus of `g`, because the composite ends in
   `ComplexAnalytic.analytificationInclHom g` and
   `ComplexAnalytic.range_base_analytificationIncl` says that morphism's range **is** that zero
   locus. Containment is `⟨_, rfl⟩` and no image of a range is computed.
3. The source is non-empty, so the range is a non-empty open subset of `ℂ^n` on which every `g j`
   vanishes.
4. `MvPolynomial.eq_zero_of_eval_eq_zero_of_isOpen` (`Oka/Algebra/MvPolynomial/Funext.lean`) makes
   each `g j` zero. **That is the only new ingredient and it has no complex-analytic content**: it
   is `MvPolynomial.funext_set` at a box neighbourhood, so the mirror tree is where it lives and
   this file imports it.
5. Which contradicts the hypothesis.

**The prose's own route is not this one, and the difference is worth a line.** It argues that the
zero locus, being a proper closed subset of `ℂ^n`, has empty interior, so an open subset of it is
empty — and then rules that out with a point. The route below reaches the same contradiction
without naming the interior: a polynomial vanishing on the range is zero directly. The two are the
same three facts in a different order and neither is deeper.

## Why a module of its own

`Oka/Analytification/StandardEtaleLocalIso.lean` is where the fuller of the two prose copies sits
and would be the natural home, but its whole `noncomputable section` is opened at
`g : Fin 0 → MvPolynomial (ULift (Fin n)) ℂ` — the `k = 0` configuration its theorem is about — so
the statement here would need a second variable block in a file whose subject is the other case.
It would also carry `Oka/Algebra/MvPolynomial/Funext.lean` into that file's imports, and this
file's three imports are what the proof reads and nothing else: `Oka.Analytification.StandardEtale`
for the presentation and the morphism, `Oka.AnalyticSpace.LocalIso` for the class, and the mirror
lemma.

## Main results

- `ComplexAnalytic.not_isLocalIso_analytificationMap_etalePresHom_comp`: **the analytification of
  a standard étale morphism over a presented base, followed by the inclusion of the base into
  `ℂ^n`, is not a local isomorphism** — as soon as one of the base's relations is a non-zero
  polynomial and the source is not empty.

## What is not here

* **No converse.** That the composite *is* a local isomorphism when every `g j` is zero is a
  different theorem and nothing here supplies it. `Oka/Analytification/StandardEtaleLocalIso.lean`
  argues it in prose — at `g = 0` the inclusion of the base is a local isomorphism rather than a
  closed immersion — and that argument is still uncompiled.
* **Nothing about finiteness.** `ComplexAnalytic.AnalyticSpace.IsFinite` and
  `ComplexAnalytic.AnalyticSpace.IsFiniteEtale` at `k ≥ 1` are what
  `Oka/Analytification/StandardEtaleFiniteEtale.lean` and
  `Oka/Analytification/StandardEtaleFiniteness.lean` record as absent, and this file bears on
  neither: it refutes the local-isomorphism field of a composite, which is the field those files
  say is the *available* one at `k = 0`.
* **No claim that the hypotheses are irredundant**, beyond the two sentences above. That `g = 0`
  makes the conclusion false is argued from another file's prose and is not compiled; that an
  empty source satisfies `ComplexAnalytic.AnalyticSpace.IsLocalIso` is a reading of that
  structure's two fields, both of which quantify over the source, and is not a theorem here.
* **No statement about the base's own analytification** — that it is a proper closed subset of
  `ℂ^n`, or that it has empty interior. The proof does not need either and does not prove either;
  step 4 replaces them.
* **Nothing at all about `StandardEtalePair`.** No pair, no `cond`, no
  derivative: the hypotheses are about `g`, and `F` and `G` are unconstrained. That is why this is
  shorter than the positive statements on this line, which all read a pair.
-/

open CategoryTheory MvPolynomial

universe u

namespace ComplexAnalytic

noncomputable section

variable {n k : ℕ} (g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ)
  (F G : MvPolynomial (ULift.{u} (Fin (n + 1))) ℂ)

/-! ### The projection to `ℂ^n` at a proper base -/

/-- **The standard étale analytification, followed by the inclusion of the base into `ℂ^n`, is not
a local isomorphism** as soon as one of the base's relations is a non-zero polynomial and the
source is not empty.

The four steps are in the module docstring. In the proof they read backwards from the goal:
`MvPolynomial.eq_zero_of_eval_eq_zero_of_isOpen` is applied at the range of the composite, which
is open because the composite would be a local homeomorphism, and contains the image of the point
`hne` supplies; what remains is that every point of the range kills `g j`, which is
`ComplexAnalytic.range_base_analytificationIncl` at the containment `⟨_, rfl⟩`.

**`h` is used as an instance and not applied.** `ComplexAnalytic.AnalyticSpace.IsLocalIso` is a
class, so the hypothesis introduced by `intro` is found by instance search inside
`ComplexAnalytic.AnalyticSpace.IsLocalIso.isLocalHomeomorph`; the `(f := …)` is there because the
morphism cannot be inferred from the field's own type. -/
theorem not_isLocalIso_analytificationMap_etalePresHom_comp
    (hg : ∃ j, g j ≠ 0)
    (hne : Nonempty (AnalyticSpace.analytification.{u} (etalePresentation.{u} g F G))) :
    ¬ AnalyticSpace.IsLocalIso
      (analytificationMap.{u} (etalePresHom.{u} g F G) ≫ analytificationInclHom.{u} g) := by
  intro h
  obtain ⟨j, hj⟩ := hg
  obtain ⟨y⟩ := hne
  refine hj (MvPolynomial.eq_zero_of_eval_eq_zero_of_isOpen
    (AnalyticSpace.IsLocalIso.isLocalHomeomorph (f := analytificationMap.{u}
      (etalePresHom.{u} g F G) ≫ analytificationInclHom.{u} g)).isOpenMap.isOpen_range
    (Set.mem_range_self y) ?_)
  rintro x ⟨z, rfl⟩
  have hz : (analytificationMap.{u} (etalePresHom.{u} g F G) ≫
      analytificationInclHom.{u} g).toLRSHom.base z ∈
      Set.range ⇑(analytificationIncl.{u} g).base :=
    ⟨(analytificationMap.{u} (etalePresHom.{u} g F G)).toLRSHom.base z, rfl⟩
  rw [range_base_analytificationIncl] at hz
  exact hz j

end

end ComplexAnalytic
