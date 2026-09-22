/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.AnalyticSpace.LocalAtSource
import Oka.Analytification.DistinguishedOpen

/-!
# A unit-ideal family is a cover of the analytification, and local isomorphism descends along it

For `A = ℂ[x₁, …, x_n] ⧸ (g₁, …, g_k)` and a family `(fᵢ)` of polynomials whose classes in `A`
generate the unit ideal, the distinguished opens `D(fᵢ) ⊆ X^an` cover `X^an`; and a morphism out
of `X^an` is a local isomorphism as soon as each composite `(A_{fᵢ})^an ⟶ X^an ⟶ Y` is one.

**The algebraic hypothesis is the only one there is.** No finiteness of the family is asked for
and no topological condition is asked for: the covering is read off from the fact that a point of
`X^an` is a `ℂ`-algebra map out of `A` — `ComplexAnalytic.quotientEval` — and a `ℂ`-algebra map
cannot kill a family that generates the unit ideal.

## Why this file exists, which is a consumer and not a symmetry

taxis #2178 maps a Zariski-local route to *the analytification of an étale morphism of affine
`ℂ`-schemes is a local isomorphism*, in four rungs. Two of them meet here.

* **Rung 3**, `Oka/Analytification/DistinguishedOpen.lean`, says the analytification of `A ⟶ A_f`
  is the open immersion onto `D(f)`, and says it *over `X^an`*
  (`ComplexAnalytic.localisationIso_hom_ofRestrict`,
  `ComplexAnalytic.localisationIso_inv_localisationProj`).
* **Rung 4**, `Oka/AnalyticSpace/LocalAtSource.lean`, says being a local isomorphism descends
  along an open cover of the **source**.

What the route then needs, and what neither file has, is the step from an *algebraic* covering
condition — the `fᵢ` generate the unit ideal, which is the form Stacks 00UE's conclusion is used
in — to a `TopologicalSpace.IsOpenCover` of `X^an` whose members are the spaces rung 3 produces.
That step is the first theorem below and the second is the two rungs composed through it.

**This file supplies those two and stops there.** It says nothing about étale algebras, nothing
about standard étale pairs and nothing about `Spec`; the covering condition is a hypothesis here
and producing it from étaleness is a different rung of that route, not started in this
repository.

## The proof of the covering, which is three quotations and one contradiction

A point `y` of `X^an` gives the ring map `ComplexAnalytic.quotientEval g y : A →+* ℂ`, whose
value on a class is the value of the polynomial (`ComplexAnalytic.quotientEval_mk`); membership
in `D(f)` is that value being nonzero (`ComplexAnalytic.mem_localisationOpen_iff`). If `y` were
in no member, every `fᵢ` would lie in the kernel, so the whole span would
(`Ideal.span_le`), so `1` would, and `ℂ` is not the zero ring. **The hypothesis is used exactly
once**, at the rewrite that turns the span into `⊤`.

**`ComplexAnalytic.quotientEval` is what makes this short, and it is not a convenience.** Without
it the same argument has to carry the side condition that evaluation kills the `gⱼ` through every
step; that is `ComplexAnalytic.eval_eq_zero_of_mem`, discharged once in the construction of that
ring map in `Oka/Analytification/Presentation.lean` and never again here.

## Why a module of its own, measured rather than argued

Both of the files this one sits between are candidate homes, and both are reachable — neither
import would be a cycle, since `scripts/module_graph.py` reports
`Oka.Analytification.DistinguishedOpen` and `Oka.AnalyticSpace.LocalAtSource` **incomparable**.
So the argument is cost and framing, and the figures are closures of the comment-stripped import
graph, each counting the module itself.

| module | its `Oka` closure | its Mathlib closure |
| --- | --- | --- |
| `Oka/Analytification/DistinguishedOpen.lean` | 72 | 3287 |
| `Oka/AnalyticSpace/LocalAtSource.lean` | 45 | 3037 |
| this file | 74 | 3287 |

* **Appending to `Oka/AnalyticSpace/LocalAtSource.lean` is the expensive direction and the
  dishonest one.** It would add **250** Mathlib modules and **28** `Oka` modules to that file's
  closure, and it would falsify the last bullet of that file's `## What is not here` — *Nothing
  about analytification and nothing étale* — which is the sentence a reader of a file named
  *local on the source* is entitled to.
* **Appending to `Oka/Analytification/DistinguishedOpen.lean` is cheap at that file and not at
  its consumers.** It adds **0** Mathlib modules and exactly **1** `Oka` module,
  `Oka.AnalyticSpace.LocalAtSource`, whose entire closure is already inside that file's. But
  `scripts/module_graph.py --downstream` counts **157** modules downstream of it against **101**
  downstream of `Oka/AnalyticSpace/LocalAtSource.lean`, and what the append charges is the
  difference: **56** modules, every one of them under `Oka/`, would acquire the import. **The
  other 101 have it already** — the 100 under `OkaTest/`, each of which has the root `Oka` in its
  import closure and takes the import from that root's own `import Oka.AnalyticSpace.LocalAtSource`
  line, and this module, which imports it directly. **This file is downstream of no module under
  `Oka/`**: the 100 the same command reports downstream of *it* are all under `OkaTest/` and all
  reach it through the root, and its own two imports are paid by nobody else.

**Which fence these numbers are on, since the instrument has two.** Every one of them is
`scripts/module_graph.py` as printed — the two aggregator roots conduct and are subtracted from
the tally, which is that script's default — and its docstring's other fence, both roots deleted
from the graph, returns different ones. **On this fence the 56 is the figure the argument rests
on and it does not move with this push**: at the parent commit the same two commands return
**155** and **99**, the difference is **56** again, and it is the same 56 modules. What the push
moves is the two raw counts, by its own two modules — this one, which imports `DistinguishedOpen`
directly, and `OkaTest.DistinguishedOpenCover`, which reaches it through `import Oka`. **The
closures in the table are records of the commit this file is added at**, moving whenever either
file gains an import, and the raw downstream counts move whenever anything imports either file;
the acquisition count is the one that survives both, which is why the bullet argues from it. A
later reader should re-run all of them rather than quote them.

## Main results

- `ComplexAnalytic.isOpenCover_localisationOpen`: **a family of polynomials whose classes
  generate the unit ideal of `A` cuts out an open cover of `X^an` by distinguished opens.**
- `ComplexAnalytic.isLocalIso_of_localisationProj_comp`: **being a local isomorphism descends
  along such a family** — if every `ComplexAnalytic.localisationProj` composed with `φ` is a
  local isomorphism, so is `φ`.
- `ComplexAnalytic.isLocalIso_iff_localisationProj_comp`: **the two directions together.** The
  forward one asks nothing of the family: `ComplexAnalytic.localisationProj` factors through the
  open subspace by an isomorphism (`ComplexAnalytic.localisationIso_hom_ofRestrict`), and
  `ComplexAnalytic.AnalyticSpace.isLocalIso_ofRestrict` and
  `ComplexAnalytic.AnalyticSpace.isLocalIso_comp` are instances. It is here because
  `Oka/AnalyticSpace/LocalAtSource.lean` and `Oka/AnalyticSpace/LocalAtTarget.lean` pair each
  descent theorem with an `iff` and a reader who knows those files will look for this one.

## What is not here

* **No converse of the covering statement.** That the `D(fᵢ)` cover `X^an` does *not* give back
  that the classes of the `fᵢ` generate the unit ideal: `X^an` sees only the `ℂ`-points, so a
  family generating an ideal whose zero locus over `ℂ` is empty covers `X^an` without generating
  `⊤` unless a Nullstellensatz is invoked. **Nothing here proves that and nothing here needs it**
  — the theorems below take the algebraic condition as a hypothesis and never produce it.
* **No finiteness and no quasi-compactness.** The index type is arbitrary. A consumer that wants
  a finite subfamily has to get it from the algebra — `1` is a finite combination — and
  `TopologicalSpace.IsOpenCover.exists_finite_of_compactSpace` is not available, since `X^an` is
  not compact.
* **Nothing about `ComplexAnalytic.AnalyticSpace.IsFinite` or
  `ComplexAnalytic.AnalyticSpace.IsFiniteEtale`.** `Oka/AnalyticSpace/LocalAtSource.lean`
  declines both for the source, so the second theorem here cannot be stated for either, and this
  file makes no attempt at a replacement.
* **No producer of the hypothesis.** Every statement below is conditional on a family that
  generates the unit ideal, and the whole point of the route in taxis #2178 is that étaleness
  supplies one; **that step is absent from this repository and this file does not narrow it.**
* **And the covering theorem is the first declaration under `Oka/` whose conclusion is a
  `TopologicalSpace.IsOpenCover`.** `git grep -nE "IsOpenCover" -- 'Oka/**.lean'` returns, at the
  commit this file is added at and outside this file, **26** lines in **three** —
  `Oka/AnalyticSpace/LocalAtTarget.lean`, `Oka/AnalyticSpace/LocalAtSource.lean` and
  `Oka/Topology/IsLocalHomeomorph.lean` — and in every one of them the class is a hypothesis or
  prose about one. That figure is a record of this commit; the property it is evidence for is
  what a later reader should re-run.
-/

open CategoryTheory TopologicalSpace AlgebraicGeometry Topology

universe u

namespace ComplexAnalytic

variable {n k : ℕ} (g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ)
  {ι : Type u} (f : ι → MvPolynomial (ULift.{u} (Fin n)) ℂ)

/-- **A unit-ideal family cuts out an open cover of the analytification.**

If the classes of the `fᵢ` in `A = ℂ[x] ⧸ (g)` generate the unit ideal then every point of `X^an`
lies in some `D(fᵢ)`. No finiteness of the family is asked for.

The contradiction is at `ℂ`: were a point in no member, evaluation at it would kill every `fᵢ`,
hence the span they generate, hence `1`. -/
theorem isOpenCover_localisationOpen
    (hf : Ideal.span (Set.range fun i ↦ Ideal.Quotient.mk (presentationIdeal.{u} g) (f i)) = ⊤) :
    IsOpenCover fun i ↦ localisationOpen.{u} g (f i) := by
  refine eq_top_iff.2 fun y _ ↦ ?_
  rw [Opens.mem_iSup]
  by_contra hcon
  have hzero (i : ι) :
      quotientEval.{u} g y (Ideal.Quotient.mk (presentationIdeal.{u} g) (f i)) = 0 :=
    (quotientEval_mk.{u} g y (f i)).trans
      (not_not.1 fun h ↦ hcon ⟨i, (mem_localisationOpen_iff.{u} g (f i)).2 h⟩)
  have hker : Ideal.span (Set.range fun i ↦ Ideal.Quotient.mk (presentationIdeal.{u} g) (f i))
      ≤ RingHom.ker (quotientEval.{u} g y) :=
    Ideal.span_le.2 (Set.range_subset_iff.2 fun i ↦ RingHom.mem_ker.2 (hzero i))
  rw [hf] at hker
  exact one_ne_zero ((map_one (quotientEval.{u} g y)).symm.trans
    (RingHom.mem_ker.1 (hker Submodule.mem_top)))

variable {Y : AnalyticSpace.{u}} (φ : AnalyticSpace.analytification.{u} g ⟶ Y)

/-- **Being a local isomorphism descends along a unit-ideal family.**

`ComplexAnalytic.isOpenCover_localisationOpen` turns the algebraic hypothesis into a cover of the
**source**, which is what `ComplexAnalytic.AnalyticSpace.isLocalIso_of_isOpenCover_source`
consumes; the only work left is that the inclusion of `D(fᵢ)` and the projection out of
`(A_{fᵢ})^an` differ by the isomorphism `ComplexAnalytic.localisationIso`, which is
`ComplexAnalytic.localisationIso_inv_localisationProj`. -/
theorem isLocalIso_of_localisationProj_comp
    (hf : Ideal.span (Set.range fun i ↦ Ideal.Quotient.mk (presentationIdeal.{u} g) (f i)) = ⊤)
    (hloc : ∀ i, AnalyticSpace.IsLocalIso (localisationProj.{u} g (f i) ≫ φ)) :
    AnalyticSpace.IsLocalIso φ := by
  refine AnalyticSpace.isLocalIso_of_isOpenCover_source φ _
    (isOpenCover_localisationOpen.{u} g f hf) fun i ↦ ?_
  haveI := hloc i
  haveI : AnalyticSpace.IsLocalIso (localisationIso.{u} g (f i)).inv :=
    AnalyticSpace.isLocalIso_of_isIso _
  have he : (AnalyticSpace.analytification.{u} g).ofRestrict (localisationOpen.{u} g (f i)) ≫ φ =
      (localisationIso.{u} g (f i)).inv ≫ (localisationProj.{u} g (f i) ≫ φ) := by
    rw [← Category.assoc, localisationIso_inv_localisationProj]
  rw [he]
  infer_instance

/-- **Being a local isomorphism is local along a unit-ideal family.**

The forward direction asks nothing of the family and is the same two instances the source-local
`iff` in `Oka/AnalyticSpace/LocalAtSource.lean` uses, read through
`ComplexAnalytic.localisationIso_hom_ofRestrict`. The hypothesis on the family is there for the
other direction, which is `ComplexAnalytic.isLocalIso_of_localisationProj_comp` above. -/
theorem isLocalIso_iff_localisationProj_comp
    (hf : Ideal.span (Set.range fun i ↦ Ideal.Quotient.mk (presentationIdeal.{u} g) (f i)) = ⊤) :
    AnalyticSpace.IsLocalIso φ ↔
      ∀ i, AnalyticSpace.IsLocalIso (localisationProj.{u} g (f i) ≫ φ) := by
  refine ⟨fun _ i ↦ ?_, isLocalIso_of_localisationProj_comp.{u} g f φ hf⟩
  haveI : AnalyticSpace.IsLocalIso (localisationIso.{u} g (f i)).hom :=
    AnalyticSpace.isLocalIso_of_isIso _
  rw [← localisationIso_hom_ofRestrict.{u} g (f i), Category.assoc]
  infer_instance

end ComplexAnalytic
