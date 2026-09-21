/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Complex.Polynomial.Basic
import OkaTest.HolomorphicMap
import OkaTest.HolomorphicMapOpen

/-!
# Non-vacuity of finiteness for morphisms of complex analytic spaces

`ComplexAnalytic.AnalyticSpace.IsFinite` says a morphism is closed with finite fibres. Two things
could be wrong with it and neither is visible from its type: it could hold only for the
isomorphisms, and it could hold for everything. This file rules both out on the same pair of
spaces, with the two morphisms between `ℂ` and `ℂ²` that everyone draws first.

* **`ComplexAnalytic.axisIncl`, `z ↦ (z, 0)`, is finite** and is not an isomorphism — its image is
  the first axis, a proper closed subset. It is finite because its underlying map is a closed
  embedding (`ComplexAnalytic.isClosedEmbedding_base_axisIncl`), which is proved here rather than
  quoted, because `ComplexAnalytic.AnalyticSpace.isFinite_of_isCutOutBy` has no instance to be
  applied at. `ComplexAnalytic.IsCutOutBy` is a condition on a morphism of *locally ringed
  spaces*, and cut-out data is produced — that is what
  `AlgebraicGeometry.LocallyRingedSpace.isCutOutBy_zeroLocusSubspaceι` does. **For a morphism of
  *analytic* spaces there is now exactly one producer, and it does not reach
  `ComplexAnalytic.axisIncl`**: `ComplexAnalytic.isCutOutBy_analytificationInclHom` is about the
  inclusion of an *analytification* into `ℂ^n`, and `ComplexAnalytic.axisIncl` is built by hand
  and is not one. So the witness here still has to be built by hand, for the reason it always
  did — the morphism, not the category.

  **Two sentences that stood here are retired and they were wrong in different ways.** The first
  said that cut-out data for a morphism of analytic spaces is produced *"never"*, which is what
  the producer above falsifies. The second was an instrument reading that had gone stale without
  anybody noticing: *"`git grep 'IsCutOutBy.*toLRSHom'` over the whole repository returns two
  hits, `ComplexAnalytic.AnalyticSpace.mono_of_isCutOutBy` and `isFinite_of_isCutOutBy` itself,
  and both take it as a hypothesis."* By the time it was reread that grep returned **thirteen**
  lines — eleven hypothesis binders across six files, plus two occurrences in prose — and the
  conclusion drawn from it was nevertheless still correct, since all eleven were binders. **A
  count quoted in prose is a measurement with no check on it**, and this one survived four merges
  that added nine hits to it; the sentence that replaces it names no number for that reason.
* **`ComplexAnalytic.proj`, `(z, w) ↦ z`, is not finite, and fails *both* conditions.** Its fibre
  over the origin is the second axis, which is infinite; and its underlying map is not closed,
  because the hyperbola `z w = 1` is closed in `ℂ²` and its image is `ℂ ∖ {0}`, which is not
  closed in `ℂ`. So the example does not separate the two halves of the definition — it fails at
  both — and `ComplexAnalytic.not_isClosedMap_base_proj` is what says so.

## The third statement, which is the reason both are here

**`ComplexAnalytic.isFinite_axisIncl_comp_proj`: the composite `ℂ ⟶ ℂ² ⟶ ℂ` is finite although
the second factor is not.** So the finite morphisms are *not* closed under right cancellation, and
`ComplexAnalytic.AnalyticSpace.isFinite_comp` is not an iff in disguise. Without this the two
statements above would only say that the class is somewhere between empty and everything; this
says the composition lemma has the strength it claims and no more.

## The composite is the identity *morphism*, and that is what makes cancellation testable here

**`ComplexAnalytic.axisIncl_comp_proj`.** `ComplexAnalytic.base_axisIncl_comp_proj` says the
composite's base map is `id`, which is all the finiteness statements above need; a morphism of
analytic spaces is more than its base map, and the upgrade is
`ComplexAnalytic.AnalyticSpace.hom_ext_complexAffineSpace` plus three pullback computations. With
it the composite satisfies every hypothesis of a cancellation lemma for free, and the two halves
of finite étale cancellation that hold — `ComplexAnalytic.AnalyticSpace.isLocalIso_of_comp` and
`ComplexAnalytic.AnalyticSpace.finite_fiber_of_comp` — can be run against a second factor that is
this file's non-example.

**The one new fact it produces is `ComplexAnalytic.not_isLocalIso_proj`**, and it is the third
thing the projection is shown to fail. Unlike the other two it is not proved from a set one can
name: it is the cancellation lemma read contrapositively, and it doubles as the check that that
lemma's hypothesis on its second factor cannot be dropped.

## The stalk half of `IsLocalIso`, which is the other reason this file exists

**`ComplexAnalytic.isIso_stalkMap_sq`: every stalk map of the squaring map of `ℂ ∖ {0}` is an
isomorphism.** `ComplexAnalytic.AnalyticSpace.IsLocalIso` has two fields, and until this statement
no declaration anywhere had had to check the second one: the only positive witness was the
identity, and the non-example `ComplexAnalytic.axisIncl` fails the *topological* field alone. So
the class had a field nothing exercised.

`ComplexAnalytic.sq` is the map that exercises it, and it is **not** an isomorphism
(`ComplexAnalytic.not_isIso_sq`), so the field is doing work rather than coming along for free.
The content is `ComplexAnalytic.isIso_stalkMap_okaMapHom` in
`Oka/AnalyticSpace/StalkLocalInverse.lean` — the stalk map of a holomorphic map is precomposition
of germs, so an analytic local inverse makes it bijective — applied at Mathlib's local inverse of
`z ↦ z²`. Nothing here builds a branch of the square root, and the *only* use of the puncture is
that `2z ≠ 0`.

**With the topological field — `ComplexAnalytic.isLocalHomeomorph_base_sq`, from Mathlib's
`isCoveringMap_npow` — and finiteness, this assembles into
`ComplexAnalytic.isFiniteEtale_sq`.** That is the statement the two rungs were for: a finite étale
morphism which is **not** an isomorphism, so `ComplexAnalytic.AnalyticSpace.IsFiniteEtale` is
strictly larger than the isomorphisms and neither rung is idle.

**And it is where the third rung is exercised.**
`ComplexAnalytic.AnalyticSpace.isCoveringMap_base_of_isFiniteEtale`
(`Oka/AnalyticSpace/CoveringMap.lean`) says a finite étale morphism out of a Hausdorff analytic
space has a covering map for its underlying map; `ComplexAnalytic.isCoveringMap_base_sq` is the
only place at which its hypotheses are shown to be satisfiable by anything other than an
isomorphism. **This sentence also said *"is the only place it is applied"*, and that clause is now
false**: `ComplexAnalytic.isCoveringMap_base_restrictHom_analytificationMap_etalePresHom_comp`
(`Oka/Analytification/Hausdorff.lean`) is a second application, at a morphism the analytification
machinery produces rather than one written here by hand, and
`ComplexAnalytic.isCoveringMap_base_restrictHom_analytificationMap_etalePresHom`
(`Oka/Analytification/HausdorffBase.lean`) is a third since 2026-09-21, the same rung over a
presented base. **The two clauses are not the same claim
and only one of them moved**, which is why the other is narrowed rather than deleted:
`ComplexAnalytic.not_isIso_sq` shows `ComplexAnalytic.sq` is not an isomorphism, and nothing shows
that of either later application's morphism. **It proves nothing new about `z ↦ z²`** — Mathlib's
`isCoveringMap_npow` already covers that, and is what the local-homeomorphism field above is
derived from — so read it as a test of the rung and not as a fact about the map.

## Why this file imports `OkaTest/HolomorphicMapOpen.lean`

`OkaTest/` wrote the punctured `z`-line **twice**: `ComplexAnalytic.punctured` below, as
`ComplexAnalytic.AnalyticSpace.nonvanishing` of the coordinate, and `punctured` in
`OkaTest/HolomorphicMapOpen.lean`, as `{z | z (ULift.up 0) ≠ 0}` with its openness proved by
hand. **They are not a name clash** — the full names differ, so both can be in scope at once —
but they are one open set written twice, and until this import nothing in the tree said so.
`ComplexAnalytic.punctured_eq_punctured` below is that statement; it is `Opens.ext` and `Set.ext`
over the two `mem_punctured_iff`s and nothing else.

**The edge runs in this direction because the two closures are one-sided.** Transitive closure of
each file's import list, counting modules under `Oka/`, `OkaTest/` and `Mathlib/`, read off
`(← getEnv).header.moduleNames` in a `lake env lean` scratch whose imports are that list:

* **this file, 3690 → 3691**, and the one is `OkaTest.HolomorphicMapOpen` itself: `import Oka` is
  that file's entire import list and this file already has it, so the edge adds no third-party
  module at all;
* **`OkaTest/HolomorphicMapOpen.lean`, 3639 → 3691** for the reverse edge, since it would acquire
  `OkaTest.FiniteMorphism` itself together with `OkaTest.HolomorphicMap`,
  `Mathlib.Analysis.Normed.Module.Connected`, `Mathlib.Analysis.Complex.Polynomial.Basic` and
  their closures. **It is the one figure of the four that a build of this branch cannot produce**:
  measured there it reads 3692, because this file's olean now carries the edge and
  `OkaTest.HolomorphicMapOpen` joins its own closure. It was taken on `master`'s oleans, before
  the edge existed.

**One against fifty-two.** Neither figure is a *build* cost: `lakefile.toml`'s
`globs = ["OkaTest", "OkaTest.+"]` builds every module under `OkaTest/` already — the second
entry does that on its own, and the first is there so that the root module is built too, for the
reason the comment above it gives — so `lake build` runs the same 4041 jobs on both sides and the
edge buys ordering rather than work. **What it does cost is incremental rebuilds**: this file is
now behind `OkaTest/HolomorphicMapOpen.lean` in the order, and an edit to that file invalidates
this one.

**Two alternatives were priced and lost.** A third file importing both would cost one new module
and one line in `OkaTest.lean`, and would put the equality where neither consumer is; and
*retiring* one definition is not reachable in the cheap direction, since
`OkaTest/HolomorphicMapOpen.lean` would have to take the fifty-two-module edge to use
`ComplexAnalytic.punctured`. Retiring `ComplexAnalytic.punctured` instead *is* reachable once the
edge above exists, and it is a rename across four files. **What decides against it is the test a
retirement has to pass**, not its size: the surviving definition must discharge every use of the
one that goes, and both definitions have a use the other does not. Both therefore stand, and both
earn their keep: this one composes with
`ComplexAnalytic.AnalyticSpace.mem_nonvanishing_iff` and
`ComplexAnalytic.AnalyticSpace.liftRestrict`, and the other's `mem_punctured_iff` is `Iff.rfl`,
which `punctured_ne_top` uses definitionally.

**What the edge is for.** `OkaTest/HolomorphicFamily.lean` reaches this file through
`OkaTest/OpenBaseProjection.lean`, so it now sees `invCoord` and `not_restrict_eq_invCoord` —
*no entire function restricts to `1/z₀`* — with no import of its own, and with the two
`punctured`s reconciled. That file's `## What is not checked here` says what is still missing
around them, which is a parametrisation and a lemma and not bookkeeping.

## What is not checked here

* **Nothing about structure sheaves.** `ComplexAnalytic.AnalyticSpace.IsFinite` is a condition on
  the underlying map, and the theorem that makes it a condition on sheaves — that `f_*𝒪_X` is
  coherent for finite `f` — is not in this repository. So no statement here is about coherence and
  none should be read that way.
* **`ComplexAnalytic.axisIncl` is not shown to be a closed immersion**, only a closed embedding on
  points. Whether it cuts `ℂ` out of `ℂ²` by the second coordinate — the `IsCutOutBy` statement —
  is not proved, and only the topological half is used.
* **No compactness, and no properness beyond what finiteness gives.** The bullet that used to
  stand here said neither map was shown proper. It was written when this file's two maps were
  `ComplexAnalytic.axisIncl` and `ComplexAnalytic.proj`, so name them rather than counting them:
  **`ComplexAnalytic.axisIncl` and `ComplexAnalytic.sq` are proper** — by
  `ComplexAnalytic.AnalyticSpace.isProperMap_base_of_isFinite`, as
  `ComplexAnalytic.isProperMap_base_axisIncl` and `ComplexAnalytic.isProperMap_base_sq` — **and
  `ComplexAnalytic.proj` is not** (`ComplexAnalytic.not_isProperMap_base_proj`). What is still not
  here is any properness argument that does not go through finiteness: no source is shown compact,
  and no fibre is shown compact other than by being finite. The one fibre this file says anything
  else about is `ComplexAnalytic.proj`'s over the origin, and what it says is that it is **not**
  compact (`ComplexAnalytic.not_isCompact_fiber_proj`). There is still no `IsProper` class for a
  morphism of analytic spaces to be an instance of.
* **No finite étale morphism other than an isomorphism.** `ComplexAnalytic.axisIncl` is finite and
  is *not* a local isomorphism (`ComplexAnalytic.not_isLocalIso_axisIncl`), which is what says the
  second rung restricts the first; but the only positive witness for
  `ComplexAnalytic.AnalyticSpace.IsFiniteEtale` here is **no longer** the identity, and the two
  bullets that used to stand here are retired rather than weakened. `ComplexAnalytic.sq`, the
  squaring map of the punctured line, is proved finite (`ComplexAnalytic.isFinite_sq`), a local
  homeomorphism (`ComplexAnalytic.isLocalHomeomorph_base_sq`), an isomorphism on every stalk
  (`ComplexAnalytic.isIso_stalkMap_sq`) and **not** an isomorphism
  (`ComplexAnalytic.not_isIso_sq`) — hence `ComplexAnalytic.isFiniteEtale_sq`, a finite étale
  morphism which is not an isomorphism. **The stalk half of
  `ComplexAnalytic.AnalyticSpace.IsLocalIso` is exercised by it**, and within this file by
  nothing else: the non-example `ComplexAnalytic.axisIncl` fails the topological field alone.
  This bullet used to say *"and by nothing else"* without the qualification, and that stopped
  being true when `OkaTest/StandardEtaleAnalytification.lean` began exercising it through
  `ComplexAnalytic.isLocalIso_hypersurface_ofRestrict_comp_proj`; the two witnesses are
  independent — that one is an open immersion and this one is not injective. (The third,
  `ComplexAnalytic.isLocalIso_puncturedInclCoveringSpaceHom` in `OkaTest/CoveringSpace.lean`,
  goes through `ComplexAnalytic.AnalyticSpace.isLocalIso_coveringSpaceHom` and so exercises the
  stalk field only as that instance's own conclusion, which is why this bullet did not count
  it.)
* **A `degree` function on morphisms — this is no longer absent, and this file is where it is
  checked.** The bullet that used to stand here said two things, and **both are now retired**:
  that the constancy of the number of sheets over a connected base was not proved anywhere — it
  is, `ComplexAnalytic.AnalyticSpace.card_fiber_eq_of_isFiniteEtale`, applied here as
  `ComplexAnalytic.card_fiber_sq_eq` — and that nothing showed `ComplexAnalytic.sq` two-sheeted,
  which `ComplexAnalytic.card_fiber_base_sq` now does. So the constancy statement has a witness
  whose common value is **2** rather than something a one-sheeted map would also satisfy, and the
  bullet's complaint that it was a weak test is answered.
  **The `Nat`-valued `degree` function this bullet said was not wanted now exists** and is
  exercised here: `ComplexAnalytic.degree_sq` reads `ComplexAnalytic.card_fiber_base_sq` as
  `ComplexAnalytic.AnalyticSpace.degree ComplexAnalytic.sq = 2`, and
  `ComplexAnalytic.not_bijective_base_sq` is the one application of
  `ComplexAnalytic.AnalyticSpace.bijective_base_iff_degree_eq_one`. What answered the objection was
  not the computation but the pair of statements in `Oka/AnalyticSpace/Degree.lean` — the
  well-definedness theorem and a consumer of the number — and the computation here is what stops
  that pair from being exercised at nothing.
  **The distinction the bullet before that one drew still holds**: `IsCoveringMap` is a condition
  on a map of topological spaces, so neither `ComplexAnalytic.isCoveringMap_base_sq` nor Mathlib's
  `isCoveringMap_npow` is about a covering *of analytic spaces*, a notion this repository does not
  have.
-/

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry Topology Filter

universe u

namespace ComplexAnalytic

noncomputable section

/-! ### The inclusion of the first axis, `z ↦ (z, 0)` -/

/-- The pair of entire functions `(z, 0)` on `ℂ`, as a family indexed by the coordinates of `ℂ²`.
The `ULift` wrapping is what `ComplexAnalytic.AnalyticSpace.okaMap` indexes by. -/
def axisFamily : ULift.{u} (Fin 2) → OkaRing (⊤ : Opens (ULift.{u} (Fin 1) → ℂ)) :=
  fun j ↦ if j = ULift.up 0 then coord (ULift.up 0) else 0

/-- **The inclusion of the first axis, `ℂ ⟶ ℂ²`.** -/
def axisIncl : AnalyticSpace.complexAffineSpace.{u} 1 ⟶ AnalyticSpace.complexAffineSpace.{u} 2 :=
  AnalyticSpace.okaMap axisFamily.{u}

/-- **Its underlying map is `z ↦ (z, 0)`**, named on the nose rather than exhibited at a point.
Everything below is a computation with this equation. -/
theorem base_axisIncl (p : AnalyticSpace.complexAffineSpace.{u} 1) :
    ((axisIncl.{u}).toLRSHom.base p : ULift.{u} (Fin 2) → ℂ) =
      fun j ↦ if j = ULift.up 0 then (p : ULift.{u} (Fin 1) → ℂ) (ULift.up 0) else 0 := by
  refine funext fun j ↦ ?_
  change okaMapFun axisFamily.{u} _ j = _
  rw [okaMapFun_apply, axisFamily]
  by_cases h : j = ULift.up 0
  · rw [if_pos h, if_pos h, evalHom_coord]
  · rw [if_neg h, if_neg h, map_zero]

/-- The first coordinate, as a continuous retraction of `ComplexAnalytic.axisIncl`. Its existence
is what makes the inclusion an embedding without any computation of neighbourhoods. -/
def axisRetract : AnalyticSpace.complexAffineSpace.{u} 2 →
    AnalyticSpace.complexAffineSpace.{u} 1 :=
  fun q _ ↦ (q : ULift.{u} (Fin 2) → ℂ) (ULift.up 0)

/-- **The image of the inclusion is exactly the first axis.** The inclusion `⊆` is the second
component of `ComplexAnalytic.base_axisIncl`; the reverse is the retraction, and the case `j ≠ 0`
is where the hypothesis is used. -/
theorem range_base_axisIncl :
    Set.range ((axisIncl.{u}).toLRSHom.base :
        AnalyticSpace.complexAffineSpace.{u} 1 → AnalyticSpace.complexAffineSpace.{u} 2) =
      {q : AnalyticSpace.complexAffineSpace.{u} 2 |
        (q : ULift.{u} (Fin 2) → ℂ) (ULift.up 1) = 0} := by
  refine Set.ext fun q ↦ ⟨?_, fun hq ↦ ?_⟩
  · rintro ⟨p, rfl⟩
    change ((axisIncl.{u}).toLRSHom.base p : ULift.{u} (Fin 2) → ℂ) (ULift.up 1) = 0
    rw [base_axisIncl]
    exact if_neg (by simp)
  · refine ⟨fun _ ↦ (q : ULift.{u} (Fin 2) → ℂ) (ULift.up 0), funext fun j ↦ ?_⟩
    rw [show ((axisIncl.{u}).toLRSHom.base _ : ULift.{u} (Fin 2) → ℂ) = _ from base_axisIncl _]
    dsimp only
    by_cases h : j = ULift.up 0
    · rw [if_pos h, h]
    · rw [if_neg h]
      obtain ⟨j⟩ := j
      fin_cases j
      · exact absurd rfl h
      · exact hq.symm

/-- **The inclusion is a closed embedding.**

Embedding by `Function.LeftInverse.isEmbedding` at `ComplexAnalytic.axisRetract` — a continuous
injection with a continuous left inverse is an embedding, and that is cheaper than identifying the
subspace topology. Closed because, by `ComplexAnalytic.range_base_axisIncl`, the image is the zero
set of a coordinate, and evaluation at a coordinate is continuous.

The continuity of the inclusion itself is free: it is the underlying map of a morphism of locally
ringed spaces. -/
theorem isClosedEmbedding_base_axisIncl :
    IsClosedEmbedding ((axisIncl.{u}).toLRSHom.base :
      AnalyticSpace.complexAffineSpace.{u} 1 → AnalyticSpace.complexAffineSpace.{u} 2) where
  toIsEmbedding := by
    refine Function.LeftInverse.isEmbedding (f := axisRetract.{u}) ?_
      (continuous_pi fun _ ↦ continuous_apply (ULift.up 0))
      (axisIncl.{u}).toLRSHom.base.hom.continuous
    intro p
    refine funext fun l ↦ ?_
    change ((axisIncl.{u}).toLRSHom.base p : ULift.{u} (Fin 2) → ℂ) (ULift.up 0) = _
    rw [base_axisIncl]
    change p (ULift.up 0) = p l
    exact congrArg p (Subsingleton.elim _ _)
  isClosed_range := by
    have hcont : Continuous fun q : AnalyticSpace.complexAffineSpace.{u} 2 ↦
        (q : ULift.{u} (Fin 2) → ℂ) (ULift.up 1) := continuous_apply _
    rw [range_base_axisIncl]
    exact isClosed_eq hcont continuous_const

/-- **The inclusion of the first axis is a finite morphism**, and it is not an isomorphism, since
its image is a proper subset of `ℂ²` — `ComplexAnalytic.range_base_axisIncl` and the point
`(0, 1)`. -/
theorem isFinite_axisIncl : AnalyticSpace.IsFinite axisIncl.{u} :=
  AnalyticSpace.isFinite_of_isClosedEmbedding _ isClosedEmbedding_base_axisIncl.{u}

/-- **And it is proper**, by `ComplexAnalytic.AnalyticSpace.isProperMap_base_of_isFinite` off the
line above.

Nothing about `ComplexAnalytic.axisIncl` is used beyond its finiteness, and no separation
hypothesis is supplied, because that theorem asks for none — see its docstring. This and
`ComplexAnalytic.not_isProperMap_base_proj` are what make properness a condition that separates
the two morphisms of this file rather than one that holds of everything. -/
theorem isProperMap_base_axisIncl :
    IsProperMap ((axisIncl.{u}).toLRSHom.base :
      AnalyticSpace.complexAffineSpace.{u} 1 → AnalyticSpace.complexAffineSpace.{u} 2) :=
  haveI := isFinite_axisIncl.{u}
  AnalyticSpace.isProperMap_base_of_isFinite axisIncl.{u}

/-- **The inclusion is not surjective**, so `ComplexAnalytic.isFinite_axisIncl` is not a statement
about an isomorphism. -/
theorem not_surjective_base_axisIncl :
    ¬ Function.Surjective ((axisIncl.{u}).toLRSHom.base :
      AnalyticSpace.complexAffineSpace.{u} 1 → AnalyticSpace.complexAffineSpace.{u} 2) := by
  intro hsurj
  obtain ⟨p, hp⟩ := hsurj (fun _ ↦ (1 : ℂ))
  have h : ((axisIncl.{u}).toLRSHom.base p : ULift.{u} (Fin 2) → ℂ) (ULift.up 1) = 1 :=
    congrFun hp (ULift.up 1)
  rw [base_axisIncl] at h
  dsimp only at h
  rw [if_neg (by simp)] at h
  exact zero_ne_one h

/-! ### The projection `(z, w) ↦ z` -/

/-- The first coordinate of `ℂ²`, as a one-element family of entire functions. -/
def projFamily : ULift.{u} (Fin 1) → OkaRing (⊤ : Opens (ULift.{u} (Fin 2) → ℂ)) :=
  fun _ ↦ coord (ULift.up 0)

/-- **The projection `ℂ² ⟶ ℂ`.** -/
def proj : AnalyticSpace.complexAffineSpace.{u} 2 ⟶ AnalyticSpace.complexAffineSpace.{u} 1 :=
  AnalyticSpace.okaMap projFamily.{u}

/-- **Its underlying map is `(z, w) ↦ z`.** -/
theorem base_proj (q : AnalyticSpace.complexAffineSpace.{u} 2) :
    ((proj.{u}).toLRSHom.base q : ULift.{u} (Fin 1) → ℂ) =
      fun _ ↦ (q : ULift.{u} (Fin 2) → ℂ) (ULift.up 0) := by
  refine funext fun l ↦ ?_
  change okaMapFun projFamily.{u} _ l = _
  rw [okaMapFun_apply, projFamily, evalHom_coord]

/-- **The fibre of the projection over the origin is infinite**: it is the second axis, and
`t ↦ (0, t)` injects `ℂ` into it. -/
theorem infinite_fiber_proj : Infinite
    (((proj.{u}).toLRSHom.base : AnalyticSpace.complexAffineSpace.{u} 2 →
        AnalyticSpace.complexAffineSpace.{u} 1) ⁻¹'
      {(fun _ ↦ (0 : ℂ) : AnalyticSpace.complexAffineSpace.{u} 1)}) := by
  refine Set.infinite_coe_iff.2 (Set.infinite_of_injective_forall_mem
    (f := fun t : ℂ ↦ (fun l ↦ if l = ULift.up 1 then t else 0 :
      AnalyticSpace.complexAffineSpace.{u} 2)) ?_ ?_)
  · intro a b hab
    have h := congrFun hab (ULift.up 1)
    simpa using h
  · intro t
    refine Set.mem_preimage.2 (Set.mem_singleton_iff.2 (funext fun l ↦ ?_))
    rw [show ((proj.{u}).toLRSHom.base _ : ULift.{u} (Fin 1) → ℂ) = _ from base_proj _]
    simp

/-- **The projection is not finite**, by the fibre condition. Its underlying map fails the
*closed* condition as well — `ComplexAnalytic.not_isClosedMap_base_proj` — so this is not an
example separating the two halves of `ComplexAnalytic.AnalyticSpace.IsFinite`; it is one at which
both fail, and each failure is exhibited at a set one can name. -/
theorem not_isFinite_proj : ¬ AnalyticSpace.IsFinite proj.{u} :=
  AnalyticSpace.not_isFinite_of_infinite_fiber _ _ infinite_fiber_proj.{u}

/-! ### And its underlying map is not closed either

The half of `ComplexAnalytic.AnalyticSpace.IsFinite` that `ComplexAnalytic.not_isFinite_proj` does
not touch. A projection along a *compact* factor is closed; along `ℂ` it is not, and the classical
witness is the hyperbola. -/

/-- **The hyperbola `z w = 1` in `ℂ²`**, the standard closed set whose image under the projection
is not closed. -/
def hyperbola : Set (AnalyticSpace.complexAffineSpace.{u} 2) :=
  {p | (p : ULift.{u} (Fin 2) → ℂ) (ULift.up 0) * (p : ULift.{u} (Fin 2) → ℂ) (ULift.up 1) = 1}

/-- It is closed, being the level set of a continuous function. -/
theorem isClosed_hyperbola : IsClosed hyperbola.{u} := by
  have h0 : Continuous fun p : AnalyticSpace.complexAffineSpace.{u} 2 ↦
      (p : ULift.{u} (Fin 2) → ℂ) (ULift.up 0) := continuous_apply _
  have h1 : Continuous fun p : AnalyticSpace.complexAffineSpace.{u} 2 ↦
      (p : ULift.{u} (Fin 2) → ℂ) (ULift.up 1) := continuous_apply _
  exact isClosed_eq (h0.mul h1) continuous_const

/-- **Its image is `ℂ ∖ {0}`**: `z w = 1` forces `z ≠ 0`, and every nonzero `z` is hit, at
`w = z⁻¹`. -/
theorem image_hyperbola :
    ((proj.{u}).toLRSHom.base : AnalyticSpace.complexAffineSpace.{u} 2 →
        AnalyticSpace.complexAffineSpace.{u} 1) '' hyperbola.{u} =
      {q : AnalyticSpace.complexAffineSpace.{u} 1 |
        (q : ULift.{u} (Fin 1) → ℂ) (ULift.up 0) ≠ 0} := by
  refine Set.ext fun q ↦ ⟨?_, fun hq ↦ ?_⟩
  · rintro ⟨p, hp, rfl⟩
    intro hzero
    rw [show ((proj.{u}).toLRSHom.base p : ULift.{u} (Fin 1) → ℂ) = _ from base_proj _] at hzero
    exact one_ne_zero (hp.symm.trans
      (by rw [show (p : ULift.{u} (Fin 2) → ℂ) (ULift.up 0) = 0 from hzero, zero_mul]))
  · refine ⟨fun l ↦ if l = ULift.up 0 then (q : ULift.{u} (Fin 1) → ℂ) (ULift.up 0)
      else ((q : ULift.{u} (Fin 1) → ℂ) (ULift.up 0))⁻¹, ?_, ?_⟩
    · change _ * _ = 1
      simpa using mul_inv_cancel₀ hq
    · refine funext fun l ↦ ?_
      rw [show ((proj.{u}).toLRSHom.base _ : ULift.{u} (Fin 1) → ℂ) = _ from base_proj _]
      dsimp only
      rw [if_pos rfl]
      exact congrArg _ (Subsingleton.elim _ _)

/-- **The projection is not a closed map.**

If it were, `ℂ ∖ {0}` would be closed in `ℂ`, so `{0}` would be open there — and `{0}` is not
open in `ℂ`, since the punctured neighbourhood filter at `0` is not `⊥`. The passage from the
one-variable affine space to `ℂ` is the continuous map `c ↦ (fun _ ↦ c)`, whose preimage of the
zero set of the coordinate is exactly `{0}`. -/
theorem not_isClosedMap_base_proj :
    ¬ IsClosedMap ((proj.{u}).toLRSHom.base : AnalyticSpace.complexAffineSpace.{u} 2 →
      AnalyticSpace.complexAffineSpace.{u} 1) := by
  intro hclosed
  have himg := hclosed _ isClosed_hyperbola.{u}
  rw [image_hyperbola] at himg
  have hopen : IsOpen {q : AnalyticSpace.complexAffineSpace.{u} 1 |
      (q : ULift.{u} (Fin 1) → ℂ) (ULift.up 0) = 0} := by
    have hc := himg.isOpen_compl
    convert hc using 1
    exact Set.ext fun _ ↦ (not_not).symm
  have hdiag : Continuous fun c : ℂ ↦ (fun _ ↦ c : AnalyticSpace.complexAffineSpace.{u} 1) :=
    continuous_pi fun _ ↦ continuous_id
  have hzero : IsOpen ({0} : Set ℂ) := by
    have hp := hopen.preimage hdiag
    convert hp using 1
    exact Set.ext fun _ ↦ Iff.rfl
  have hb : (𝓝[≠] (0 : ℂ)) = ⊥ := by rwa [← isOpen_singleton_iff_punctured_nhds]
  exact (inferInstance : (𝓝[≠] (0 : ℂ)).NeBot).ne hb

/-- **The fibre over the origin is not compact either.**

`ComplexAnalytic.infinite_fiber_proj` says that fibre is infinite, and infiniteness by itself
refutes nothing about properness: `IsProperMap` asks that fibres be *compact*, and an infinite
set can be compact. This is the sharper statement, and it is what makes the docstring below
checkable rather than asserted. The fibre is the second axis; the second coordinate maps it
continuously **onto** `ℂ`, a continuous image of a compact set is compact, and `ℂ` is not. -/
theorem not_isCompact_fiber_proj : ¬ IsCompact
    (((proj.{u}).toLRSHom.base : AnalyticSpace.complexAffineSpace.{u} 2 →
        AnalyticSpace.complexAffineSpace.{u} 1) ⁻¹'
      {(fun _ ↦ (0 : ℂ) : AnalyticSpace.complexAffineSpace.{u} 1)}) := by
  intro h
  have hc : Continuous fun p : AnalyticSpace.complexAffineSpace.{u} 2 ↦
      (p : ULift.{u} (Fin 2) → ℂ) (ULift.up 1) := continuous_apply _
  have himg := h.image hc
  have huniv : (fun p : AnalyticSpace.complexAffineSpace.{u} 2 ↦
      (p : ULift.{u} (Fin 2) → ℂ) (ULift.up 1)) ''
        (((proj.{u}).toLRSHom.base : AnalyticSpace.complexAffineSpace.{u} 2 →
            AnalyticSpace.complexAffineSpace.{u} 1) ⁻¹'
          {(fun _ ↦ (0 : ℂ) : AnalyticSpace.complexAffineSpace.{u} 1)}) = Set.univ := by
    refine Set.eq_univ_of_forall fun t ↦
      ⟨(fun l ↦ if l = ULift.up 1 then t else 0 :
        AnalyticSpace.complexAffineSpace.{u} 2), ?_, by simp⟩
    refine Set.mem_preimage.2 (Set.mem_singleton_iff.2 (funext fun l ↦ ?_))
    rw [show ((proj.{u}).toLRSHom.base _ : ULift.{u} (Fin 1) → ℂ) = _ from base_proj _]
    simp
  rw [huniv] at himg
  exact NoncompactSpace.noncompact_univ (X := ℂ) himg

/-- **And so it is not proper**, since a proper map is closed (`IsProperMap.isClosedMap`).

`ComplexAnalytic.proj` fails `ComplexAnalytic.AnalyticSpace.IsFinite` for two independent
reasons — an infinite fibre and a non-closed underlying map — and **`IsProperMap` sees both**.
The fibre over the origin is not compact (`ComplexAnalytic.not_isCompact_fiber_proj`) and the
underlying map is not closed (`ComplexAnalytic.not_isClosedMap_base_proj`), and either failure
on its own refutes properness.

What is *not* the case is that properness tests the finiteness of a fibre. It asks for
compactness, so `ComplexAnalytic.infinite_fiber_proj` — a statement about cardinality — does not
refute it, which is why the fibre route needs the theorem above and not that one. The proof
shipped here takes the closedness route because it is one line. -/
theorem not_isProperMap_base_proj :
    ¬ IsProperMap ((proj.{u}).toLRSHom.base : AnalyticSpace.complexAffineSpace.{u} 2 →
      AnalyticSpace.complexAffineSpace.{u} 1) := fun h ↦
  not_isClosedMap_base_proj.{u} h.isClosedMap

/-! ### The composite, and what it says about the composition lemma -/

/-- **The composite `ℂ ⟶ ℂ² ⟶ ℂ` is the identity on points.**

Composition of morphisms of analytic spaces is composition of the underlying morphisms of locally
ringed spaces by definition, so the left-hand side is `base_proj` after `base_axisIncl`, and a
point of `ℂ` is determined by its one coordinate. -/
theorem base_axisIncl_comp_proj :
    ((axisIncl.{u} ≫ proj.{u}).toLRSHom.base :
      AnalyticSpace.complexAffineSpace.{u} 1 → AnalyticSpace.complexAffineSpace.{u} 1) = id := by
  refine funext fun p ↦ funext fun l ↦ ?_
  change ((proj.{u}).toLRSHom.base ((axisIncl.{u}).toLRSHom.base p) :
    ULift.{u} (Fin 1) → ℂ) l = _
  rw [show ((proj.{u}).toLRSHom.base _ : ULift.{u} (Fin 1) → ℂ) = _ from base_proj _,
    base_axisIncl]
  dsimp only
  rw [if_pos rfl]
  exact congrArg p (Subsingleton.elim _ _)

/-- **The composite is finite although the second factor is not.**

So `ComplexAnalytic.AnalyticSpace.isFinite_comp` cannot be strengthened to an equivalence, and
finiteness is not right-cancellable: with `ComplexAnalytic.not_isFinite_proj` this is a pair
`f`, `g` with `f ≫ g` finite and `g` not. -/
theorem isFinite_axisIncl_comp_proj : AnalyticSpace.IsFinite (axisIncl.{u} ≫ proj.{u}) :=
  AnalyticSpace.isFinite_of_isClosedEmbedding _
    (base_axisIncl_comp_proj.{u} ▸ IsClosedEmbedding.id)

/-- And the identity is finite, so the two together are not a statement about the empty class. -/
example : AnalyticSpace.IsFinite (𝟙 (AnalyticSpace.complexAffineSpace.{u} 1)) :=
  inferInstance

/-- Composing two finite morphisms stays finite, at the witness above. -/
example : AnalyticSpace.IsFinite (axisIncl.{u} ≫ 𝟙 (AnalyticSpace.complexAffineSpace.{u} 2)) :=
  haveI := isFinite_axisIncl.{u}
  inferInstance

/-- **And the composite in the other order is not finite**, which is
`ComplexAnalytic.AnalyticSpace.isFinite_of_isFinite_comp` read contrapositively at a second
factor that is injective and is not the identity.

The pair is `ComplexAnalytic.proj`, which `ComplexAnalytic.not_isFinite_proj` says is not finite,
and `ComplexAnalytic.axisIncl`, which `ComplexAnalytic.isClosedEmbedding_base_axisIncl` makes
injective — so the cancellation lemma forbids the composite from being finite. **Together with
`ComplexAnalytic.isFinite_axisIncl_comp_proj` this pins down which order matters**: the same two
morphisms compose to a finite map one way round and to a non-finite one the other, and the
difference is exactly that `ComplexAnalytic.proj` is the *first* factor here and the second one
there. Nothing about the fibres or the topology is computed below; the whole proof is the lemma. -/
theorem not_isFinite_proj_comp_axisIncl :
    ¬ AnalyticSpace.IsFinite (proj.{u} ≫ axisIncl.{u}) := fun h ↦
  not_isFinite_proj.{u} (AnalyticSpace.isFinite_of_isFinite_comp proj.{u} axisIncl.{u}
    isClosedEmbedding_base_axisIncl.{u}.injective h)

/-! ### Finite is not finite étale

`ComplexAnalytic.AnalyticSpace.IsFiniteEtale` is `IsFinite` together with
`ComplexAnalytic.AnalyticSpace.IsLocalIso`, and the second is a real restriction: the witness this
file already has is finite and is **not** a local isomorphism. -/

/-- **The inclusion of the first axis is not a local isomorphism.**

A local homeomorphism is an open map, so its range would be open; the range is also closed, since
the inclusion is a closed embedding. `ℂ²` is connected, so a clopen subset is `∅` or everything —
and the range is neither, being nonempty and not all of `ℂ²`
(`ComplexAnalytic.not_surjective_base_axisIncl`).

**Nothing about stalks is used**: the topological field alone fails. That is worth saying, because
it means the example does not exercise
`ComplexAnalytic.AnalyticSpace.IsLocalIso.isIso_stalkMap` — `ComplexAnalytic.isIso_stalkMap_sq`
is what does, and it is a different map. -/
theorem not_isLocalIso_axisIncl : ¬ AnalyticSpace.IsLocalIso axisIncl.{u} := by
  intro h
  haveI : PreconnectedSpace (AnalyticSpace.complexAffineSpace.{u} 2) :=
    inferInstanceAs (PreconnectedSpace (ULift.{u} (Fin 2) → ℂ))
  have hopen : IsOpen (Set.range ((axisIncl.{u}).toLRSHom.base :
      AnalyticSpace.complexAffineSpace.{u} 1 → AnalyticSpace.complexAffineSpace.{u} 2)) :=
    h.isLocalHomeomorph.isOpenMap.isOpen_range
  have hclosed : IsClosed (Set.range ((axisIncl.{u}).toLRSHom.base :
      AnalyticSpace.complexAffineSpace.{u} 1 → AnalyticSpace.complexAffineSpace.{u} 2)) :=
    isClosedEmbedding_base_axisIncl.{u}.isClosed_range
  rcases isClopen_iff.1 ⟨hclosed, hopen⟩ with hbot | htop
  · exact absurd (Set.mem_range_self (f := ((axisIncl.{u}).toLRSHom.base :
      AnalyticSpace.complexAffineSpace.{u} 1 → AnalyticSpace.complexAffineSpace.{u} 2))
      (fun _ ↦ (0 : ℂ))) (by rw [hbot]; exact fun hc ↦ hc)
  · exact not_surjective_base_axisIncl.{u} (Set.range_eq_univ.1 htop)

/-- **So it is finite and not finite étale**, which is what says the second rung is a restriction
on the first rather than a restatement of it. -/
theorem not_isFiniteEtale_axisIncl : ¬ AnalyticSpace.IsFiniteEtale axisIncl.{u} := fun h ↦
  not_isLocalIso_axisIncl.{u} h.isLocalIso

/-- **And the class is not empty**: the identity is finite étale.

This is the degenerate witness. It is kept because it is the cheapest possible check that
`ComplexAnalytic.AnalyticSpace.IsFiniteEtale` is inhabited at all, and because it was for a while
the *only* one: the non-degenerate witness is `ComplexAnalytic.isFiniteEtale_sq` below, `z ↦ z²`
from `ℂ ∖ {0}` to itself, which needed `ComplexAnalytic.AnalyticSpace.liftRestrict`, a
covering-map statement from Mathlib and a germ dictionary to state. **Neither witness makes the
other redundant**: this one says the class is nonempty at zero cost, and that one says it is
larger than the isomorphisms. -/
example : AnalyticSpace.IsFiniteEtale (𝟙 (AnalyticSpace.complexAffineSpace.{u} 1)) :=
  inferInstance

/-! ### Cancellation at this pair, and what it says about the projection

`ComplexAnalytic.AnalyticSpace.isLocalIso_of_comp` and
`ComplexAnalytic.AnalyticSpace.finite_fiber_of_comp` are the two halves of a cancellation
statement for the finite étale rung that do hold, and the pair `ComplexAnalytic.axisIncl`,
`ComplexAnalytic.proj` is where this file can see them. It composes to the **identity** — not
merely to a morphism with the identity as its base map, which is
`ComplexAnalytic.base_axisIncl_comp_proj` and is all the finiteness statements above needed — so
the composite satisfies every hypothesis at zero cost, and each of the two lemmas can be run
against a second factor that is as badly behaved as this file's non-example is. -/

/-- **The identity's coordinate pullbacks are the coordinates.**

The companion of `ComplexAnalytic.AnalyticSpace.coordPullback_comp` at the identity, and the only
step of `ComplexAnalytic.axisIncl_comp_proj` below that is about neither of the two morphisms.
`AnalyticSpace.Hom.toLRSHom (𝟙 _)` is the identity of the underlying locally ringed space by `rfl`,
after which this is functoriality of global sections.

**This is a general statement and its home would be `Oka/AnalyticSpace/HomToComplex.lean`**, beside
the composition lemma it is the companion of. It is here because this file is its only consumer;
a second one is what should move it. -/
theorem coordPullback_id {n : ℕ} (j : ULift.{u} (Fin n)) :
    AnalyticSpace.coordPullback (𝟙 (AnalyticSpace.complexAffineSpace.{u} n)) j = coord j := by
  have h : AnalyticSpace.Hom.toLRSHom (𝟙 (AnalyticSpace.complexAffineSpace.{u} n)) =
      𝟙 (AnalyticSpace.complexAffineSpace.{u} n).toLocallyRingedSpace := rfl
  change (LocallyRingedSpace.Γ.map (AnalyticSpace.Hom.toLRSHom
    (𝟙 (AnalyticSpace.complexAffineSpace.{u} n))).op).hom (coord j) = _
  rw [h, op_id, LocallyRingedSpace.Γ.map_id]
  rfl

/-- **The composite `ℂ ⟶ ℂ² ⟶ ℂ` is the identity morphism**, and not only the identity on points.

`ComplexAnalytic.base_axisIncl_comp_proj` is the statement about base maps and is what the
finiteness results above consume; it does not give this, because a morphism of analytic spaces is
its base map together with a map of structure sheaves. The upgrade is
`ComplexAnalytic.AnalyticSpace.hom_ext_complexAffineSpace` — a morphism into `ℂ^m` is determined by
the pullbacks of the coordinates — and then three computations of a pullback:
`ComplexAnalytic.AnalyticSpace.coordPullback_comp` for the composite, `Γ_map_okaMapHom_coord`
twice for the two factors, which are both `ComplexAnalytic.AnalyticSpace.okaMap` of an explicit
family, and `ComplexAnalytic.coordPullback_id` for the identity. The last rewrite is
`Subsingleton.elim` on `ULift (Fin 1)`, which is where "the first coordinate" and "the coordinate"
are identified. -/
theorem axisIncl_comp_proj :
    axisIncl.{u} ≫ proj.{u} = 𝟙 (AnalyticSpace.complexAffineSpace.{u} 1) := by
  refine AnalyticSpace.hom_ext_complexAffineSpace _ _ fun j ↦ ?_
  change AnalyticSpace.coordPullback (axisIncl.{u} ≫ proj.{u}) j =
    AnalyticSpace.coordPullback (𝟙 (AnalyticSpace.complexAffineSpace.{u} 1)) j
  rw [AnalyticSpace.coordPullback_comp,
    show AnalyticSpace.coordPullback proj.{u} j = coord (ULift.up 0) from
      Γ_map_okaMapHom_coord projFamily.{u} j]
  change AnalyticSpace.coordPullback axisIncl.{u} (ULift.up 0) = _
  rw [show AnalyticSpace.coordPullback axisIncl.{u} (ULift.up 0) = axisFamily.{u} (ULift.up 0) from
      Γ_map_okaMapHom_coord axisFamily.{u} _,
    coordPullback_id, axisFamily, if_pos rfl,
    Subsingleton.elim (ULift.up 0 : ULift.{u} (Fin 1)) j]

/-- **The projection is not a local isomorphism**, and no property of it is computed to say so.

The whole proof is `ComplexAnalytic.AnalyticSpace.isLocalIso_of_comp` read contrapositively at
`ComplexAnalytic.axisIncl_comp_proj`: the composite is the identity, hence a local isomorphism, so
if `ComplexAnalytic.proj` were one then `ComplexAnalytic.axisIncl` would be one too — and
`ComplexAnalytic.not_isLocalIso_axisIncl` says it is not.

**So this pair is also the check that the hypothesis on the second factor is not removable.** Drop
`[IsLocalIso g]` from that lemma and it proves `ComplexAnalytic.axisIncl` is a local isomorphism,
which is false here. Together with `ComplexAnalytic.not_isFinite_proj` and
`ComplexAnalytic.not_isClosedMap_base_proj` this is the third thing the projection fails, and the
only one of the three obtained from a general lemma rather than from a set one can name. -/
theorem not_isLocalIso_proj : ¬ AnalyticSpace.IsLocalIso proj.{u} := by
  intro h
  haveI : AnalyticSpace.IsLocalIso (axisIncl.{u} ≫ proj.{u}) := by
    rw [axisIncl_comp_proj]
    infer_instance
  exact not_isLocalIso_axisIncl.{u} (AnalyticSpace.isLocalIso_of_comp axisIncl.{u} proj.{u})

/-- **And the fibre half cancels against a second factor that is not finite at all.**

`ComplexAnalytic.AnalyticSpace.finite_fiber_of_comp` asks nothing of `g`, and this is the check
that the sentence means what it says: `ComplexAnalytic.proj` is the standard non-finite morphism of
this file (`ComplexAnalytic.not_isFinite_proj`), and the fibres of
`ComplexAnalytic.axisIncl` come out finite from `ComplexAnalytic.isFinite_axisIncl_comp_proj`
alone. The conclusion is not new — `ComplexAnalytic.isFinite_axisIncl` has it, with more — so this
is a statement about the lemma's hypotheses and is kept as an `example`. -/
example (y : AnalyticSpace.complexAffineSpace.{u} 2) :
    Finite ((axisIncl.{u}).toLRSHom.base ⁻¹' {y}) :=
  haveI := isFinite_axisIncl_comp_proj.{u}
  AnalyticSpace.finite_fiber_of_comp axisIncl.{u} proj.{u} y

/-! ### The squaring map of the punctured line, and its stalk maps

The limitation this file used to record — that the only positive witness for
`ComplexAnalytic.AnalyticSpace.IsFiniteEtale` was the identity — was about `ℂ ∖ {0}` and `z ↦ z²`,
and **this section builds that map**; the two after it prove everything the witness needs, and
`ComplexAnalytic.isFiniteEtale_sq` at the end retires the limitation. It is
here because the construction was the part nobody had priced: a morphism whose *target* is an open
subspace needed `ComplexAnalytic.AnalyticSpace.liftRestrict`, which did not exist.

This section proves that the map exists, what its underlying map is, and that it is **not
injective** and hence not an isomorphism. The next proves it **finite** and a **local
homeomorphism**; the one after that proves every one of its **stalk maps is an isomorphism**; and
`ComplexAnalytic.isFiniteEtale_sq` at the end assembles them. -/

/-- **The squaring map `ℂ ⟶ ℂ`**, before restricting to the punctured line: the morphism
`OkaTest/HolomorphicMap.lean` builds from `sqFamily` and proves is not the identity
(`okaMap_sq_ne_id`). -/
def sqAll : AnalyticSpace.complexAffineSpace.{u} 1 ⟶ AnalyticSpace.complexAffineSpace.{u} 1 :=
  AnalyticSpace.okaMap _root_.sqFamily.{u}

/-- **Its underlying map is `z ↦ z²`**, from `eq_sq_okaMapFun`. -/
theorem base_sqAll (p : AnalyticSpace.complexAffineSpace.{u} 1) :
    ((sqAll.{u}).toLRSHom.base p : ULift.{u} (Fin 1) → ℂ) =
      fun _ ↦ (p : ULift.{u} (Fin 1) → ℂ) (ULift.up 0) *
        (p : ULift.{u} (Fin 1) → ℂ) (ULift.up 0) := by
  change okaMapFun _root_.sqFamily.{u} (p : ULift.{u} (Fin 1) → ℂ) = _
  rw [eq_sq_okaMapFun]
  exact funext fun _ ↦ _root_.sq _

/-- **`ℂ ∖ {0}`**, as an open subspace of the affine line: the non-vanishing locus of `z`. -/
def punctured : (AnalyticSpace.complexAffineSpace.{u} 1).Opens :=
  (AnalyticSpace.complexAffineSpace.{u} 1).nonvanishing (coord (ULift.up 0))

/-- **A point of the affine line lies in it exactly when its coordinate is nonzero.**
`ComplexAnalytic.AnalyticSpace.mem_nonvanishing_iff` turns membership into non-vanishing of the
*value*, and `ComplexAnalytic.eval_complexAffineSpace` computes that value on `ℂ^n`. -/
theorem mem_punctured_iff (p : AnalyticSpace.complexAffineSpace.{u} 1) :
    p ∈ punctured.{u} ↔ (p : ULift.{u} (Fin 1) → ℂ) (ULift.up 0) ≠ 0 := by
  rw [punctured, AnalyticSpace.mem_nonvanishing_iff]
  rw [eval_complexAffineSpace, evalHom_coord]

/-- **The two `punctured`s of `OkaTest/` are the same open set.** `punctured` of
`OkaTest/HolomorphicMapOpen.lean` is `{z | z (ULift.up 0) ≠ 0}` with its openness proved by hand;
`ComplexAnalytic.punctured` above is the non-vanishing locus of the coordinate. Nothing before
this said they agree, and the two files did not see each other; see the module docstring for what
the import cost and for why neither definition is retired. -/
theorem punctured_eq_punctured : punctured.{u} = _root_.punctured.{u} :=
  TopologicalSpace.Opens.ext (Set.ext fun p ↦
    (mem_punctured_iff.{u} p).trans (_root_.mem_punctured_iff.{u} p).symm)

/-- **The square of a nonzero number is nonzero**, in the form
`ComplexAnalytic.AnalyticSpace.liftRestrict` asks for. -/
theorem range_subset_punctured :
    Set.range ((((AnalyticSpace.complexAffineSpace.{u} 1).ofRestrict punctured.{u} ≫
        sqAll.{u}).toLRSHom.base) :
      (AnalyticSpace.complexAffineSpace.{u} 1).restrict punctured.{u} →
        AnalyticSpace.complexAffineSpace.{u} 1) ⊆ (punctured.{u} : Set _) := by
  rintro _ ⟨p, rfl⟩
  have hp : (p.1 : ULift.{u} (Fin 1) → ℂ) (ULift.up 0) ≠ 0 :=
    (mem_punctured_iff.{u} p.1).1 p.2
  have hcomp : (((AnalyticSpace.complexAffineSpace.{u} 1).ofRestrict punctured.{u} ≫
      sqAll.{u}).toLRSHom.base p) = (sqAll.{u}).toLRSHom.base p.1 := rfl
  rw [hcomp]
  refine (mem_punctured_iff.{u} _).2 ?_
  rw [show (((sqAll.{u}).toLRSHom.base p.1 : AnalyticSpace.complexAffineSpace.{u} 1) :
      ULift.{u} (Fin 1) → ℂ) = _ from base_sqAll.{u} p.1]
  exact mul_ne_zero hp hp

/-- **The squaring map of the punctured line, `ℂ ∖ {0} ⟶ ℂ ∖ {0}`.**

The target is an open subspace, which is why this needs
`ComplexAnalytic.AnalyticSpace.liftRestrict`: `ComplexAnalytic.AnalyticSpace.okaMap` produces
morphisms into `ℂ^n` and nothing before produced one into a restriction of it. -/
def sq : (AnalyticSpace.complexAffineSpace.{u} 1).restrict punctured.{u} ⟶
    (AnalyticSpace.complexAffineSpace.{u} 1).restrict punctured.{u} :=
  AnalyticSpace.liftRestrict
    ((AnalyticSpace.complexAffineSpace.{u} 1).ofRestrict punctured.{u} ≫ sqAll.{u})
    punctured.{u} range_subset_punctured.{u}

/-- **Its underlying map is `z ↦ z²`.**

Computed through `ComplexAnalytic.AnalyticSpace.liftRestrict_fac` rather than by unfolding: the
lift is opaque and the composite it factors is not. -/
theorem base_sq (p : (AnalyticSpace.complexAffineSpace.{u} 1).restrict punctured.{u}) :
    (((sq.{u}).toLRSHom.base p).1 : ULift.{u} (Fin 1) → ℂ) =
      fun _ ↦ (p.1 : ULift.{u} (Fin 1) → ℂ) (ULift.up 0) *
        (p.1 : ULift.{u} (Fin 1) → ℂ) (ULift.up 0) := by
  have h := congrArg (fun m : _ ⟶ AnalyticSpace.complexAffineSpace.{u} 1 ↦ m.toLRSHom.base p)
    (AnalyticSpace.liftRestrict_fac
      ((AnalyticSpace.complexAffineSpace.{u} 1).ofRestrict punctured.{u} ≫ sqAll.{u})
      punctured.{u} range_subset_punctured.{u})
  rw [show (((sq.{u}).toLRSHom.base p).1 : AnalyticSpace.complexAffineSpace.{u} 1) = _ from h]
  exact base_sqAll.{u} p.1

/-- **It is not injective**: `1` and `-1` are two points of `ℂ ∖ {0}` with the same square.

`ComplexAnalytic.not_isIso_sq` below is the consequence, and it is a separate statement because
non-injectivity of the underlying map is not by itself non-invertibility of the morphism.
**Nothing here shows it finite étale**, and no statement below should be read as saying so. -/
theorem not_injective_base_sq :
    ¬ Function.Injective ((sq.{u}).toLRSHom.base :
      (AnalyticSpace.complexAffineSpace.{u} 1).restrict punctured.{u} →
        (AnalyticSpace.complexAffineSpace.{u} 1).restrict punctured.{u}) := by
  have h1 : ((fun _ ↦ (1 : ℂ)) : ULift.{u} (Fin 1) → ℂ) ∈ punctured.{u} :=
    (mem_punctured_iff.{u} _).2 one_ne_zero
  have h2 : ((fun _ ↦ (-1 : ℂ)) : ULift.{u} (Fin 1) → ℂ) ∈ punctured.{u} :=
    (mem_punctured_iff.{u} _).2 (neg_ne_zero.2 one_ne_zero)
  intro hinj
  have hne : (⟨(fun _ ↦ (1 : ℂ) : ULift.{u} (Fin 1) → ℂ), h1⟩ :
      (AnalyticSpace.complexAffineSpace.{u} 1).restrict punctured.{u}) ≠
    ⟨(fun _ ↦ (-1 : ℂ) : ULift.{u} (Fin 1) → ℂ), h2⟩ := by
    intro h
    have := congrFun (congrArg Subtype.val h) (ULift.up 0)
    norm_num at this
  refine hne (hinj ?_)
  refine Subtype.ext (funext fun l ↦ ?_)
  rw [show (((sq.{u}).toLRSHom.base ⟨(fun _ ↦ (1 : ℂ) : ULift.{u} (Fin 1) → ℂ), h1⟩).1 :
      ULift.{u} (Fin 1) → ℂ) = _ from base_sq.{u} _,
    show (((sq.{u}).toLRSHom.base ⟨(fun _ ↦ (-1 : ℂ) : ULift.{u} (Fin 1) → ℂ), h2⟩).1 :
      ULift.{u} (Fin 1) → ℂ) = _ from base_sq.{u} _]
  norm_num

/-- **So it is not an isomorphism**, which is what makes the map worth building: with
`ComplexAnalytic.isFiniteEtale_sq` below, `ComplexAnalytic.AnalyticSpace.IsFiniteEtale` contains
something the identity does not.

An isomorphism of analytic spaces gives a homeomorphism of the underlying spaces through
`ComplexAnalytic.AnalyticSpace.forgetToLocallyRingedSpace` and
`AlgebraicGeometry.LocallyRingedSpace.homeoOfIso`, and a homeomorphism is injective. Note that the
functor is applied to the *iso* rather than the morphism, so no instance has to be re-ascribed at
`ComplexAnalytic.AnalyticSpace.Hom.toLRSHom` — the seam
`ComplexAnalytic.AnalyticSpace.isLocalIso_of_isIso` documents does not arise on this route.

**This is not itself a statement that it is finite étale**; that is
`ComplexAnalytic.isFiniteEtale_sq`, which needs the three sections below. -/
theorem not_isIso_sq : ¬ IsIso sq.{u} := fun _ ↦
  not_injective_base_sq.{u}
    (LocallyRingedSpace.homeoOfIso
      (AnalyticSpace.forgetToLocallyRingedSpace.{u}.mapIso (asIso sq.{u}))).injective

/-! ### `sq` is finite, and a local homeomorphism

The two topological halves of the witness. **Neither of them is about stalks**; the stalk field of
`ComplexAnalytic.AnalyticSpace.IsLocalIso` is the section after this one, and
`ComplexAnalytic.isLocalIso_sq` puts them together.

Both halves go through one bridge — `ComplexAnalytic.puncturedHomeo`, which identifies the
underlying space of the punctured line with `{z : ℂ // z ≠ 0}` — and then quote Mathlib about
`x ↦ x ^ 2` on the nonzero elements of `ℂ`. **The analysis is not done here and was not written
here**: `isCoveringMap_npow` is Mathlib's, and `isClosedMap_npow` and `finite_fiber_npow` are in
`Oka/Analysis/Complex/CoveringMap.lean`, stated for an arbitrary proper normed field because
nothing in them is complex-analytic. -/

/-- **`z ↦ z ^ 2` on the nonzero complex numbers**, in the exact form Mathlib's
`isCoveringMap_npow`, `isClosedMap_npow` and `finite_fiber_npow` are stated in. Named so that the
three quotations below need no `convert`. -/
def npowPunctured : {z : ℂ // z ≠ 0} → {z : ℂ // z ≠ 0} :=
  fun z ↦ ⟨z ^ 2, pow_ne_zero 2 z.2⟩

/-- **The underlying space of the punctured line is `ℂ ∖ {0}`.**

`ComplexAnalytic.punctured` is an open of `ℂ¹ = ULift (Fin 1) → ℂ`, so the underlying space of
the restriction is a subtype of a one-element function type rather than of `ℂ`.
`Homeomorph.funUnique` removes the function type and `Homeomorph.subtype` carries the membership
condition across, using `ComplexAnalytic.mem_punctured_iff`.

**This is the whole of the plumbing**, and both statements below are Mathlib's theorems conjugated
by it. -/
def puncturedHomeo :
    ((AnalyticSpace.complexAffineSpace.{u} 1).restrict punctured.{u} : Type u) ≃ₜ
      {z : ℂ // z ≠ 0} :=
  (Homeomorph.funUnique.{u} (ULift.{u} (Fin 1)) ℂ).subtype fun p ↦
    (mem_punctured_iff.{u} p).trans (by
      simp only [Homeomorph.funUnique_apply, Subsingleton.elim (ULift.up (0 : Fin 1)) default]
      exact Iff.rfl)

/-- **Its underlying map is `z ↦ z ^ 2` read through that bridge.** -/
theorem puncturedHomeo_base_sq
    (p : ((AnalyticSpace.complexAffineSpace.{u} 1).restrict punctured.{u} : Type u)) :
    puncturedHomeo.{u} ((ComplexAnalytic.sq.{u}).toLRSHom.base p) =
      npowPunctured (puncturedHomeo.{u} p) := by
  refine Subtype.ext ?_
  change ((ComplexAnalytic.sq.{u}).toLRSHom.base p).1 (ULift.up 0) = _
  rw [show (((ComplexAnalytic.sq.{u}).toLRSHom.base p).1 : ULift.{u} (Fin 1) → ℂ) = _
    from base_sq.{u} p]
  exact (_root_.sq _).symm

/-- **The same, as an equality of maps.**

The composite form, rather than the pointwise one above, is what lets `IsClosedMap` and
`IsLocalHomeomorph` transfer by composing with a homeomorphism. -/
theorem base_sq_eq_conj :
    ((ComplexAnalytic.sq.{u}).toLRSHom.base :
        ((AnalyticSpace.complexAffineSpace.{u} 1).restrict punctured.{u} : Type u) → _) =
      puncturedHomeo.{u}.symm ∘ npowPunctured ∘ puncturedHomeo.{u} := by
  refine funext fun p ↦ ?_
  rw [Function.comp_apply, Function.comp_apply, ← puncturedHomeo_base_sq.{u} p]
  exact (puncturedHomeo.{u}.symm_apply_apply _).symm

/-- **The underlying map of `ComplexAnalytic.sq` is closed.**

`isClosedMap_npow` on `ℂ`, conjugated by `ComplexAnalytic.puncturedHomeo`.

**This is the half of `IsFinite` that `OkaTest/FiniteMorphism.lean` warns about.**
`ComplexAnalytic.not_isClosedMap_base_proj` above is a map whose underlying function is not
closed, and `ℂ ∖ {0}` is not compact, so no properness shortcut is available at this level; what
does the work is that `x ↦ x ^ n` is closed on all of a proper normed field and that the nonzero
elements are exactly the preimage of themselves. -/
theorem isClosedMap_base_sq :
    IsClosedMap ((ComplexAnalytic.sq.{u}).toLRSHom.base :
      ((AnalyticSpace.complexAffineSpace.{u} 1).restrict punctured.{u} : Type u) → _) := by
  rw [base_sq_eq_conj]
  exact (puncturedHomeo.{u}.symm.isClosedMap.comp (isClosedMap_npow 2 two_ne_zero)).comp
    puncturedHomeo.{u}.isClosedMap

/-- **Its fibres are finite.** `finite_fiber_npow` at `n = 2`, carried across the bridge; the
fibre over `w` is the two square roots of `w`. -/
theorem finite_fiber_base_sq
    (y : ((AnalyticSpace.complexAffineSpace.{u} 1).restrict punctured.{u} : Type u)) :
    Finite (((ComplexAnalytic.sq.{u}).toLRSHom.base :
      ((AnalyticSpace.complexAffineSpace.{u} 1).restrict punctured.{u} : Type u) → _) ⁻¹' {y}) := by
  rw [base_sq_eq_conj]
  have h : ((puncturedHomeo.{u}.symm ∘ npowPunctured ∘ puncturedHomeo.{u}) ⁻¹' {y}) =
      puncturedHomeo.{u} ⁻¹' (npowPunctured ⁻¹' {puncturedHomeo.{u} y}) := by
    ext p
    simp [Homeomorph.symm_apply_eq]
  rw [h]
  haveI : Finite (npowPunctured ⁻¹' {puncturedHomeo.{u} y}) :=
    finite_fiber_npow 2 two_ne_zero (puncturedHomeo.{u} y)
  exact Finite.of_injective
    (fun p ↦ (⟨puncturedHomeo.{u} p.1, p.2⟩ : (npowPunctured ⁻¹' {puncturedHomeo.{u} y})))
    fun a b hab ↦ Subtype.ext (puncturedHomeo.{u}.injective (congrArg Subtype.val hab))

/-- **`ComplexAnalytic.sq` is finite**: closed with finite fibres.

Together with `ComplexAnalytic.not_isIso_sq` this is a finite morphism which is not an
isomorphism, on a source which is *not* a closed subspace of the target — unlike
`ComplexAnalytic.axisIncl`, which is finite because it is a closed embedding. **This one field is
not by itself finite étale**: `ComplexAnalytic.isFiniteEtale_sq` needs it together with the two
fields of `ComplexAnalytic.AnalyticSpace.IsLocalIso`. -/
theorem isFinite_sq : AnalyticSpace.IsFinite (ComplexAnalytic.sq.{u}) where
  isClosedMap := isClosedMap_base_sq.{u}
  finite_fiber y := finite_fiber_base_sq.{u} y

/-- **And so it is proper**, off `ComplexAnalytic.isFinite_sq` alone.

This is the witness that carries the point of
`ComplexAnalytic.AnalyticSpace.isProperMap_base_of_isFinite`: `ℂ ∖ {0}` is **not compact**, so
none of Mathlib's compactness routes to properness is available and what supplies compactness of
the fibres is their finiteness. Compare `ComplexAnalytic.isCoveringMap_base_sq` below, which does
need the source to be Hausdorff; properness does not, and no `T2Space` instance is used here. -/
theorem isProperMap_base_sq :
    IsProperMap ((ComplexAnalytic.sq.{u}).toLRSHom.base :
      ((AnalyticSpace.complexAffineSpace.{u} 1).restrict punctured.{u} : Type u) → _) :=
  haveI := isFinite_sq.{u}
  AnalyticSpace.isProperMap_base_of_isFinite ComplexAnalytic.sq.{u}

/-- **The underlying map of `ComplexAnalytic.sq` is a local homeomorphism.**

`isCoveringMap_npow` — Mathlib's, and it is *the* statement that `z ↦ zⁿ` is a covering map of
`ℂ ∖ {0}` — conjugated by `ComplexAnalytic.puncturedHomeo`. Nothing about the inverse function
theorem is used here directly; the covering-map statement already contains it.

**This is one of the two fields of `ComplexAnalytic.AnalyticSpace.IsLocalIso`**; the other, that
every stalk map of `sq` is an isomorphism, is `ComplexAnalytic.isIso_stalkMap_sq` below, and the
two are assembled in `ComplexAnalytic.isLocalIso_sq`. -/
theorem isLocalHomeomorph_base_sq :
    IsLocalHomeomorph ((ComplexAnalytic.sq.{u}).toLRSHom.base :
      ((AnalyticSpace.complexAffineSpace.{u} 1).restrict punctured.{u} : Type u) → _) := by
  rw [base_sq_eq_conj]
  exact (puncturedHomeo.{u}.symm.isLocalHomeomorph.comp
    (isCoveringMap_npow (𝕜 := ℂ) 2 (by norm_num)).isLocalHomeomorph).comp
      puncturedHomeo.{u}.isLocalHomeomorph
/-! ### The stalk maps of the squaring map are isomorphisms

This is the field of `ComplexAnalytic.AnalyticSpace.IsLocalIso` that nothing in this repository
had ever had to check. The mathematics is Mathlib's — `AnalyticAt.analyticAt_localInverse` says
the local inverse of an analytic function with nonvanishing derivative is analytic — and the work
is the germ dictionary in `Oka/AnalyticSpace/StalkLocalInverse.lean`, which turns such a local
inverse into an isomorphism of stalks.

**The other field is the section above**, and the two are assembled in
`ComplexAnalytic.isLocalIso_sq` at the end of the file. -/

/-- `z ↦ z²` is analytic at every point of `ℂ`. -/
theorem analyticAt_sqFun (x : ℂ) : AnalyticAt ℂ (fun w : ℂ ↦ w ^ 2) x :=
  (analyticAt_id (𝕜 := ℂ) (z := x)).pow 2

/-- **Its derivative is `2z`, hence nonzero away from the origin.** This is the *only* place the
puncture is used: everything else about `ComplexAnalytic.sq` holds on all of `ℂ`. -/
theorem deriv_sqFun_ne_zero {x : ℂ} (hx : x ≠ 0) : deriv (fun w : ℂ ↦ w ^ 2) x ≠ 0 := by
  have h : deriv (fun w : ℂ ↦ w ^ 2) x = 2 * x := by simp [(hasDerivAt_pow 2 x).deriv]
  rw [h]
  exact mul_ne_zero two_ne_zero hx

/-- **A holomorphic square root near `x²`**, for `x ≠ 0`: Mathlib's local inverse of `z ↦ z²` at
`x`.

This is what `#853` predicted would have to be built by hand and what
`Mathlib/Analysis/Calculus/InverseFunctionTheorem/Deriv.lean` already provides. Nothing about
branches, `log` or `exp` appears anywhere below. -/
def sqRoot {x : ℂ} (hx : x ≠ 0) : ℂ → ℂ :=
  (analyticAt_sqFun x).hasStrictDerivAt.localInverse _ _ _ (deriv_sqFun_ne_zero hx)

/-- **It is analytic at `x²`**, which is the whole reason the germ dictionary applies. -/
theorem analyticAt_sqRoot {x : ℂ} (hx : x ≠ 0) : AnalyticAt ℂ (sqRoot hx) (x ^ 2) :=
  (analyticAt_sqFun x).analyticAt_localInverse (deriv_sqFun_ne_zero hx)

/-- **It is a left inverse of `z ↦ z²` near `x`.** -/
theorem eventually_sqRoot_sq {x : ℂ} (hx : x ≠ 0) : ∀ᶠ w in 𝓝 x, sqRoot hx (w ^ 2) = w :=
  HasStrictDerivAt.eventually_left_inverse (analyticAt_sqFun x).hasStrictDerivAt
    (deriv_sqFun_ne_zero hx)

/-- **It is a right inverse of `z ↦ z²` near `x²`.** -/
theorem eventually_sq_sqRoot {x : ℂ} (hx : x ≠ 0) : ∀ᶠ w in 𝓝 (x ^ 2), sqRoot hx w ^ 2 = w :=
  HasStrictDerivAt.eventually_right_inverse (analyticAt_sqFun x).hasStrictDerivAt
    (deriv_sqFun_ne_zero hx)

/-- **The local square root read on `ℂ¹`**, which is where `ComplexAnalytic.okaMapFun` lives.

`ULift (Fin 1)` is a subsingleton, so a function on it is determined by its value at
`ULift.up 0`; that is used in both directions below and is why no `Equiv` with `ℂ` is needed. -/
def sqRootPi {c : ℂ} (hc : c ≠ 0) :
    (ULift.{u} (Fin 1) → ℂ) → (ULift.{u} (Fin 1) → ℂ) :=
  fun w _ ↦ sqRoot hc (w (ULift.up 0))

/-- **The stalk maps of `z ↦ z²` on all of `ℂ` are isomorphisms away from the origin.**

`ComplexAnalytic.AnalyticSpace.isIso_stalkMap_okaMap` at `σ = sqRootPi`. Analyticity of `sqRootPi`
is `analyticAt_pi_iff` together with analyticity of `sqRoot` and of evaluation at a coordinate
(which is a continuous linear map); the two inverse conditions are `eventually_sqRoot_sq` and
`eventually_sq_sqRoot` transported along evaluation, which is continuous.

Stated at the *whole* line rather than at the punctured one because that is where `sqAll` is
defined; `ComplexAnalytic.isIso_stalkMap_sq` is this statement carried across
`ComplexAnalytic.AnalyticSpace.liftRestrict`. -/
theorem isIso_stalkMap_sqAll {p : ULift.{u} (Fin 1) → ℂ} (hp : p (ULift.up 0) ≠ 0) :
    IsIso ((sqAll.{u}).toLRSHom.stalkMap p) := by
  have hval : okaMapFun _root_.sqFamily.{u} p = fun _ ↦ (p (ULift.up 0)) ^ 2 := by
    rw [eq_sq_okaMapFun]
  have heval : AnalyticAt ℂ (fun w : ULift.{u} (Fin 1) → ℂ ↦ w (ULift.up 0))
      (okaMapFun _root_.sqFamily.{u} p) :=
    (ContinuousLinearMap.proj (ULift.up 0) :
      (ULift.{u} (Fin 1) → ℂ) →L[ℂ] ℂ).analyticAt _
  refine AnalyticSpace.isIso_stalkMap_okaMap (τ := sqRootPi hp) ?_ ?_ ?_
  · rw [analyticAt_pi_iff]
    intro _
    refine AnalyticAt.comp ?_ heval
    rw [hval]
    exact analyticAt_sqRoot hp
  · have h := (continuous_apply (ULift.up 0)).continuousAt (x := p) |>.eventually
      (eventually_sqRoot_sq hp)
    filter_upwards [h] with y hy
    refine funext fun _ ↦ ?_
    change sqRoot hp ((okaMapFun _root_.sqFamily.{u} y) (ULift.up 0)) = y _
    rw [eq_sq_okaMapFun, hy]
    exact congrArg y (Subsingleton.elim _ _)
  · have h := (continuous_apply (ULift.up 0)).continuousAt
      (x := okaMapFun _root_.sqFamily.{u} p) |>.eventually
      (by rw [hval]; exact eventually_sq_sqRoot hp)
    filter_upwards [h] with w hw
    refine funext fun _ ↦ ?_
    rw [eq_sq_okaMapFun]
    change sqRoot hp (w (ULift.up 0)) ^ 2 = w _
    rw [hw]
    exact congrArg w (Subsingleton.elim _ _)

/-- **The stalk maps of `ComplexAnalytic.sq` are isomorphisms**, at every point of `ℂ ∖ {0}`.

This is the stalk field of `ComplexAnalytic.AnalyticSpace.IsLocalIso` for a map that is **not** an
isomorphism (`ComplexAnalytic.not_isIso_sq`), which is what the field had never been made to do.

It is `isIso_stalkMap_sqAll` transported across the factorisation
`ComplexAnalytic.AnalyticSpace.liftRestrict_fac`, by
`AlgebraicGeometry.LocallyRingedSpace.isIso_stalkMap_liftRestrict`: the target is an open
subspace, whose inclusion is an isomorphism on stalks, so the lift and the morphism it factors
have the same stalk maps up to isomorphism. Nothing about the *subtype* topology of `ℂ ∖ {0}` is
used — the only role of the puncture is `deriv_sqFun_ne_zero`.

**Three things are written out rather than left to be inferred, and each one is load-bearing.**
`AlgebraicGeometry.LocallyRingedSpace.isIso_stalkMap_liftRestrict` is applied positionally,
because leaving its instance to search leaves the range hypothesis undetermined. The other two are
about the *spelling* of a point and of a composite, and each was measured by deleting it:

* the `haveI` states `isIso_stalkMap_sqAll` at
  `((… ).ofRestrict punctured).toLRSHom.base x` and **not** at `x.1`. The two are `rfl`-equal —
  `ComplexAnalytic.AnalyticSpace.base_ofRestrict` is `rfl` — and with the `haveI` left to infer
  its type from the `x.1` form, the `hcomp` below fails with `failed to synthesize`;
* `hcomp`'s type is written out rather than left to `inferInstance` under the `▸`: with the
  `haveI` at the right spelling but `hcomp` replaced by `he ▸ inferInstance`, the same
  `failed to synthesize` comes back at the same composite.

Why is not established here and **no explanation should be read into this note**; what reproduces
is the two deletions above. The general shape is the one that recurs across this repository — two
`rfl`-equal terms are different discrimination-tree keys, and writing out *the right one of the
two* is the fix rather than writing out a type at all.

The `▸` transports a `IsIso`, which is a `Prop`, so it moves a proof and no data and nothing
downstream can meet a stuck `Eq.mpr`. -/
theorem isIso_stalkMap_sq (x : (AnalyticSpace.complexAffineSpace.{u} 1).restrict punctured.{u}) :
    IsIso (sq.{u}.toLRSHom.stalkMap x) := by
  haveI : IsIso ((sqAll.{u}).toLRSHom.stalkMap
      (((AnalyticSpace.complexAffineSpace.{u} 1).ofRestrict punctured.{u}).toLRSHom.base x)) :=
    isIso_stalkMap_sqAll.{u} ((mem_punctured_iff.{u} x.1).1 x.2)
  have he : (((AnalyticSpace.complexAffineSpace.{u} 1).ofRestrict punctured.{u} ≫
        sqAll.{u}).toLRSHom).stalkMap x =
      (sqAll.{u}).toLRSHom.stalkMap
          (((AnalyticSpace.complexAffineSpace.{u} 1).ofRestrict punctured.{u}).toLRSHom.base x) ≫
        ((AnalyticSpace.complexAffineSpace.{u} 1).ofRestrict punctured.{u}).toLRSHom.stalkMap x :=
    LocallyRingedSpace.stalkMap_comp _ _ _
  have hcomp : IsIso ((sqAll.{u}).toLRSHom.stalkMap
        (((AnalyticSpace.complexAffineSpace.{u} 1).ofRestrict punctured.{u}).toLRSHom.base x) ≫
      ((AnalyticSpace.complexAffineSpace.{u} 1).ofRestrict punctured.{u}).toLRSHom.stalkMap x) :=
    inferInstance
  have hc : IsIso ((((AnalyticSpace.complexAffineSpace.{u} 1).ofRestrict punctured.{u} ≫
      sqAll.{u}).toLRSHom).stalkMap x) := he ▸ hcomp
  exact @LocallyRingedSpace.isIso_stalkMap_liftRestrict _ _ _ _ range_subset_punctured.{u} x hc

/-! ### The witness, assembled

Everything above is a separate statement about `ComplexAnalytic.sq`; this is the one sentence they
were for. **`ComplexAnalytic.AnalyticSpace.IsFiniteEtale` now has a positive witness other than
the identity**, and `ComplexAnalytic.not_isIso_sq` says it is not an isomorphism, so the class is
strictly larger than the isomorphisms.

Neither field is proved here — `IsLocalIso`'s two fields are
`ComplexAnalytic.isLocalHomeomorph_base_sq` and `ComplexAnalytic.isIso_stalkMap_sq`, and
`IsFiniteEtale`'s other field is `ComplexAnalytic.isFinite_sq`. -/

/-- **`ComplexAnalytic.sq` is a local isomorphism.** Its two fields are the two preceding
sections. -/
theorem isLocalIso_sq : AnalyticSpace.IsLocalIso (ComplexAnalytic.sq.{u}) where
  isLocalHomeomorph := isLocalHomeomorph_base_sq.{u}
  isIso_stalkMap x := isIso_stalkMap_sq.{u} x

/-- **`ComplexAnalytic.sq` is finite étale, and it is not an isomorphism.**

This is what `OkaTest/FiniteMorphism.lean` existed to be unable to say. With
`ComplexAnalytic.not_isIso_sq`, `ComplexAnalytic.AnalyticSpace.IsFiniteEtale` is now known to
contain something the isomorphisms do not — which is the whole claim `ComplexAnalytic.axisIncl`
could not make, since it fails the local-isomorphism condition rather than satisfying it.

**Its underlying map is a covering map**, which is the section below: the third rung,
`ComplexAnalytic.AnalyticSpace.isCoveringMap_base_of_isFiniteEtale`, consumes exactly this
theorem. That was the clause this docstring used to have to withhold. It remains a statement about
the underlying map and not about the structure sheaves. -/
theorem isFiniteEtale_sq : AnalyticSpace.IsFiniteEtale (ComplexAnalytic.sq.{u}) where
  isFinite := isFinite_sq.{u}
  isLocalIso := isLocalIso_sq.{u}

/-! ### The witness is a covering map: the third rung, exercised

`ComplexAnalytic.AnalyticSpace.isCoveringMap_base_of_isFiniteEtale` in
`Oka/AnalyticSpace/CoveringMap.lean` says the underlying map of a finite étale morphism out of a
Hausdorff analytic space is a covering map. **This was the only place it is applied until
`ComplexAnalytic.isCoveringMap_base_restrictHom_analytificationMap_etalePresHom_comp`
(`Oka/Analytification/Hausdorff.lean`) landed**, and the sentence is narrowed rather than deleted
because what it recorded — that the rung had exactly one consumer — is what stopped being true.
**There have been three since 2026-09-21**, the third being
`ComplexAnalytic.isCoveringMap_base_restrictHom_analytificationMap_etalePresHom`
(`Oka/Analytification/HausdorffBase.lean`), over a presented base and about the structure map to
`X^an`. It is still the only application at a morphism this repository proves is not an
isomorphism (`ComplexAnalytic.not_isIso_sq`).

**Nothing here is new about `ComplexAnalytic.sq`, and the section would be misread if that were
not said.** That `z ↦ z²` is a covering map of `ℂ ∖ {0}` is Mathlib's `isCoveringMap_npow`, which
is already what `ComplexAnalytic.isLocalHomeomorph_base_sq` above is derived from; conjugating it
with `ComplexAnalytic.puncturedHomeo` would give the conclusion below in two lines and without the
rung. What is tested here is the **rung** — that its hypotheses are the ones a witness in this
repository actually has, and that its conclusion follows from `ComplexAnalytic.isFiniteEtale_sq`
with no further input about `sq` beyond the separation of its source.

**Only the underlying map is a covering map.** `IsCoveringMap` is a condition on a map of
topological spaces, so `ComplexAnalytic.isCoveringMap_base_sq` says nothing about structure
sheaves; there is no notion of a covering *of analytic spaces* in this repository, and the stalk
field of `ComplexAnalytic.AnalyticSpace.IsLocalIso` plays no part in the third rung. -/

/-- **The punctured line is Hausdorff.** `ComplexAnalytic.puncturedHomeo` again: `{z : ℂ // z ≠ 0}`
is a subspace of `ℂ`.

An analytic space carries no separation axiom — `Oka/AnalyticSpace/Basic.lean` declines to impose
one, as `AlgebraicGeometry.Scheme` does — so this is a hypothesis of
`ComplexAnalytic.AnalyticSpace.isCoveringMap_base_of_isFiniteEtale` that has to be supplied here.

Declared as an instance rather than a theorem so that the application below is one line. Its head
is a particular restriction of a particular space, both defined in this file, so it cannot fire
anywhere it is not wanted.

**It is subsumed and it is kept, and both halves are measured.** This paragraph used to end
*"and there is no competing `T2Space` instance for an analytic space to disagree with"*, which
`Oka/AnalyticSpace/Hausdorff.lean` makes false: `ComplexAnalytic.t2Space_complexAffineSpace` and
`ComplexAnalytic.t2Space_restrict` prove this statement, which is the `example` below, so the two
heads now overlap. `#synth` at this type still returns **this** instance, being declared later
than the library's, which is what keeps the sentences below saying that a named theorem's
`[T2Space]` hypothesis is *supplied by* it true. Retiring it is editorial, has no mathematical
content, and costs re-verifying six citations — `Oka/AnalyticSpace/Finite.lean`,
`OkaTest/FiniteEtaleCancel.lean` and four more in this file — so it is not done here. -/
instance t2Space_restrict_punctured :
    T2Space ((AnalyticSpace.complexAffineSpace.{u} 1).restrict punctured.{u} : Type u) :=
  puncturedHomeo.{u}.symm.t2Space

/-- **The general instances subsume the bespoke one**, which is the half of
`ComplexAnalytic.t2Space_restrict_punctured`'s docstring that a reader cannot check by reading.
`ComplexAnalytic.t2Space_complexAffineSpace` makes `ℂ¹` a Hausdorff analytic space and
`ComplexAnalytic.t2Space_restrict` carries that to an open subspace;
`ComplexAnalytic.puncturedHomeo` is not used. It is an `example` and not a `theorem` because
nothing should cite it — its only job is to fail the build if the subsumption stops holding. -/
example : T2Space ((AnalyticSpace.complexAffineSpace.{u} 1).restrict punctured.{u} : Type u) :=
  ComplexAnalytic.t2Space_restrict _ _

/-- **The underlying map of `ComplexAnalytic.sq` is a covering map**, from
`ComplexAnalytic.isFiniteEtale_sq` and the third rung.

This is the **first** application of
`ComplexAnalytic.AnalyticSpace.isCoveringMap_base_of_isFiniteEtale`, and still the only one at a
morphism this repository proves is not an isomorphism — that is `ComplexAnalytic.not_isIso_sq`,
and it is what says the rung is not vacuous. **The *"so far only"* this sentence carried is gone**:
`ComplexAnalytic.isCoveringMap_base_restrictHom_analytificationMap_etalePresHom_comp`
(`Oka/Analytification/Hausdorff.lean`) is a second application, and nothing shows *its* morphism is
not an isomorphism — which is exactly where the two readings of the old clause part company, and
why the surviving one is spelled out rather than left to a reader. It is *not* independent
evidence that `z ↦ z²` covers the punctured line: see the section docstring. -/
theorem isCoveringMap_base_sq :
    IsCoveringMap ((ComplexAnalytic.sq.{u}).toLRSHom.base :
      ((AnalyticSpace.complexAffineSpace.{u} 1).restrict punctured.{u} : Type u) → _) :=
  haveI := isFiniteEtale_sq.{u}
  AnalyticSpace.isCoveringMap_base_of_isFiniteEtale ComplexAnalytic.sq.{u}

/-- **The punctured line is preconnected.** `ComplexAnalytic.puncturedHomeo` again: the statement
is about `{z : ℂ // z ≠ 0}` and the bridge carries it.

`ℂ ∖ {0}` is connected because `ℂ` has real rank `2 > 1`
(`isConnected_compl_singleton_of_one_lt_rank`, with `Complex.rank_real_complex`), which is the
only place in this file where a *dimension* of `ℂ` is used at all — everything else about
`z ↦ z²` goes through `Oka/Analysis/Complex/CoveringMap.lean` and is stated over an arbitrary
proper normed field. **That is why the statement is false for the punctured line over `ℝ`** and
why no attempt is made to state it there.

Declared as an instance for the same reason `ComplexAnalytic.t2Space_restrict_punctured` is: its
head is a particular restriction of a particular space, both defined in this file, so it cannot
fire anywhere it is not wanted. `PreconnectedSpace` rather than `ConnectedSpace` because that is
what `ComplexAnalytic.AnalyticSpace.card_fiber_eq_of_isFiniteEtale` asks for; the space is of
course also nonempty, and nothing needs that.

**The transport is `Homeomorph.connectedSpace_iff`, which is a transport of `ConnectedSpace` and
not of `PreconnectedSpace`.** The `Homeomorph` namespace has no `PreconnectedSpace` transport to
match the `Homeomorph.t2Space` that `ComplexAnalytic.t2Space_restrict_punctured` just above uses,
and that is a real gap; it costs nothing here, because the connectedness of `ℂ ∖ {0}` arrives as
`ConnectedSpace` in the first place and only becomes `PreconnectedSpace` at the last step, on this
side of the bridge. Naming the absent `PreconnectedSpace` transport in backticks would fail this
repository's docstring-name check, which is the check working: a declaration that does not exist
should not be spelled as though it did. -/
instance preconnectedSpace_restrict_punctured :
    PreconnectedSpace ((AnalyticSpace.complexAffineSpace.{u} 1).restrict punctured.{u} : Type u) :=
  haveI : ConnectedSpace {z : ℂ // z ≠ 0} := by
    have h : IsConnected ({(0 : ℂ)}ᶜ : Set ℂ) :=
      isConnected_compl_singleton_of_one_lt_rank
        (by rw [Complex.rank_real_complex]; norm_num) 0
    have he : ({(0 : ℂ)}ᶜ : Set ℂ) = {z : ℂ | z ≠ 0} := by ext z; simp
    rw [he] at h
    exact isConnected_iff_connectedSpace.mp h
  (puncturedHomeo.{u}.connectedSpace_iff.mpr ‹_›).toPreconnectedSpace

/-- **All fibres of `ComplexAnalytic.sq` have the same number of points.**

`ComplexAnalytic.AnalyticSpace.card_fiber_eq_of_isFiniteEtale` at the witness, and the only place
that theorem is applied. Its three hypotheses are all supplied in this file:
`ComplexAnalytic.isFiniteEtale_sq`, `ComplexAnalytic.t2Space_restrict_punctured` and
`ComplexAnalytic.preconnectedSpace_restrict_punctured`.

**This used to be a weak statement and the paragraph here said so**, because the common value was
not computed and nothing ruled out its being `1`. `ComplexAnalytic.card_fiber_base_sq` below
computes it, and it is `2`, so the hypotheses of the constancy statement are now satisfied at a
morphism where the conclusion is not what an isomorphism would give. **This theorem is kept and is
not made redundant by that one**: what it exercises is
`ComplexAnalytic.AnalyticSpace.card_fiber_eq_of_isFiniteEtale`, and a witness for a general theorem
is not retired by a stronger fact about the witness. It remains the only place that theorem is
applied.

`Nat.card` is not a junk value, because `ComplexAnalytic.finite_fiber_base_sq` gives finiteness —
see `ComplexAnalytic.AnalyticSpace.card_fiber_eq_of_isFiniteEtale`'s docstring, where that is the
reason the homeomorphism form is stated alongside. -/
theorem card_fiber_sq_eq (y₁ y₂ : (AnalyticSpace.complexAffineSpace.{u} 1).restrict
    punctured.{u}) :
    Nat.card ((ComplexAnalytic.sq.{u}).toLRSHom.base ⁻¹' {y₁}) =
      Nat.card ((ComplexAnalytic.sq.{u}).toLRSHom.base ⁻¹' {y₂}) :=
  haveI := isFiniteEtale_sq.{u}
  AnalyticSpace.card_fiber_eq_of_isFiniteEtale ComplexAnalytic.sq.{u} y₁ y₂

/-- **Every fibre of `ComplexAnalytic.sq` has exactly two points**, so the squaring map of the
punctured line is a genuinely two-sheeted cover.

This is what `ComplexAnalytic.card_fiber_sq_eq` above does *not* say. That theorem says all fibres
have the same cardinality; this one computes it, and the value is not `1`, so the constancy
statement now has a witness at which it is not the statement an isomorphism would satisfy.

**No covering-space theory is used.** The content is `IsAlgClosed.card_setOf_pow_eq` — over an
algebraically closed field `x ^ n = a` has exactly `n` solutions when `(n : F) ≠ 0` and `a ≠ 0` —
carried across `ComplexAnalytic.base_sq_eq_conj` exactly as
`ComplexAnalytic.finite_fiber_base_sq` carries `finite_fiber_npow`. The two shuffles are the same
one and `Equiv.subtypeEquiv` does the second half, because a homeomorphism's preimage of a set is
in bijection with that set by the underlying equivalence and nothing topological is wanted.

`Mathlib.Analysis.Complex.Polynomial.Basic` is imported by this file for `Complex.isAlgClosed`
alone, and `Oka` does not bring it in. **The way that was established is worth recording, because
the obvious instrument gets it wrong.** A breadth-first search over `import` lines that does not
mask comments reports that module as reachable from `Mathlib/Analysis/Complex/CoveringMap.lean` —
through `Mathlib.Tactic.FunProp`, whose *documentation* shows an example `import` line, which is
not an import. Masked, it is not reachable; and the compiler agrees, since without this import
`IsAlgClosed ℂ` fails to synthesize with `failed to synthesize instance of type class
IsAlgClosed ℂ`. See `Oka/FieldTheory/IsAlgClosed/Basic.lean` for the measurement.

**This did not retire the `degree` clauses, and something else has.** The sentence that used to
stand here said all four places recording the absence of a `Nat`-valued degree function still
recorded it, and that was right at the time: one theorem about one map is not an invariant. What
retired them is `Oka/AnalyticSpace/Degree.lean`, which supplies the well-definedness theorem
`ComplexAnalytic.AnalyticSpace.degree_eq_card_fiber` and a consumer,
`ComplexAnalytic.AnalyticSpace.isHomeomorph_base_of_degree_eq_one`; this theorem is what
`ComplexAnalytic.degree_sq` reads, and it is unchanged by that. -/
theorem card_fiber_base_sq (y : ((AnalyticSpace.complexAffineSpace.{u} 1).restrict
    punctured.{u} : Type u)) :
    Nat.card (((ComplexAnalytic.sq.{u}).toLRSHom.base :
      ((AnalyticSpace.complexAffineSpace.{u} 1).restrict punctured.{u} : Type u) → _) ⁻¹'
      {y}) = 2 := by
  rw [base_sq_eq_conj]
  have h : ((puncturedHomeo.{u}.symm ∘ npowPunctured ∘ puncturedHomeo.{u}) ⁻¹' {y}) =
      puncturedHomeo.{u} ⁻¹' (npowPunctured ⁻¹' {puncturedHomeo.{u} y}) := by
    ext p
    simp [Homeomorph.symm_apply_eq]
  rw [h]
  have key : Nat.card (npowPunctured ⁻¹' {puncturedHomeo.{u} y}) = 2 := by
    refine Eq.trans (Nat.card_congr ?_)
      (IsAlgClosed.card_setOf_pow_eq (n := 2) (by norm_num) (puncturedHomeo.{u} y).2)
    exact Equiv.mk (fun p ↦ ⟨(p.1 : ℂ), congrArg Subtype.val p.2⟩)
      (fun x ↦ ⟨⟨(x : ℂ), fun hz ↦ (puncturedHomeo.{u} y).2 (by rw [← x.2, hz]; norm_num)⟩,
        Subtype.ext x.2⟩)
      (fun _ ↦ rfl) (fun _ ↦ rfl)
  rw [← key]
  exact Nat.card_congr (Equiv.subtypeEquiv puncturedHomeo.{u}.toEquiv fun _ ↦ Iff.rfl)

/-- **The punctured line is not empty.**

Declared as an instance for the same reason `ComplexAnalytic.t2Space_restrict_punctured` and
`ComplexAnalytic.preconnectedSpace_restrict_punctured` are: the head is a particular restriction
of a particular space, both defined in this file, so it cannot fire anywhere it is not wanted.

Nothing needed it until `ComplexAnalytic.AnalyticSpace.degree` did, and the reason it needs it is
worth stating: the degree is an `iSup` over the target, so over an empty target it is `0` whatever
the fibres are. The paragraph above
`ComplexAnalytic.preconnectedSpace_restrict_punctured` says the space "is of course also nonempty,
and nothing needs that"; something does now.

The witness is `1`, carried back across `ComplexAnalytic.puncturedHomeo`. -/
instance nonempty_restrict_punctured :
    Nonempty ((AnalyticSpace.complexAffineSpace.{u} 1).restrict punctured.{u} : Type u) :=
  ⟨puncturedHomeo.{u}.symm ⟨1, one_ne_zero⟩⟩

/-- **The squaring map of the punctured line has degree two.**

`ComplexAnalytic.AnalyticSpace.degree_eq_of_forall_card_fiber_eq` at
`ComplexAnalytic.card_fiber_base_sq`, so the only thing this adds to that theorem is the passage
from "every fibre has two points" to a number attached to the morphism — and the only hypothesis
it costs is `ComplexAnalytic.nonempty_restrict_punctured`. In particular no covering-space theory
is used here, exactly as none is used in `ComplexAnalytic.card_fiber_base_sq`.

**This is the witness the trivial covers cannot supply.**
`ComplexAnalytic.AnalyticSpace.degree_sigmaFold` realises every value too, but always with a
disconnected source; here the source is the punctured line, which is connected
(`ComplexAnalytic.preconnectedSpace_restrict_punctured` transports its connectedness), so this is
the only morphism in this repository with a computed degree greater than one and a connected
source. -/
theorem degree_sq : AnalyticSpace.degree ComplexAnalytic.sq.{u} = 2 :=
  AnalyticSpace.degree_eq_of_forall_card_fiber_eq _ card_fiber_base_sq.{u}

/-- **The underlying map of the squaring map is not bijective**, because its degree is not one.

`ComplexAnalytic.AnalyticSpace.bijective_base_iff_degree_eq_one` at
`ComplexAnalytic.degree_sq`, and it is the one place that equivalence is applied. Its four
instance hypotheses are all in this file: `ComplexAnalytic.isFiniteEtale_sq`,
`ComplexAnalytic.t2Space_restrict_punctured`,
`ComplexAnalytic.preconnectedSpace_restrict_punctured` and
`ComplexAnalytic.nonempty_restrict_punctured`.

**This is weaker than `ComplexAnalytic.not_isIso_sq` and is proved by a different route.** That
theorem rules out an isomorphism of analytic spaces and its proof is the failure of injectivity at
a pair of points; this one reads the same failure off a *number*, and is the statement
`ComplexAnalytic.AnalyticSpace.isHomeomorph_base_of_degree_eq_one` is the converse half of. It is
here because a degree function whose only consumer is a theorem about a general morphism has not
been exercised at anything. -/
theorem not_bijective_base_sq :
    ¬ Function.Bijective ((ComplexAnalytic.sq.{u}).toLRSHom.base :
      ((AnalyticSpace.complexAffineSpace.{u} 1).restrict punctured.{u} : Type u) → _) := by
  haveI := isFiniteEtale_sq.{u}
  rw [AnalyticSpace.bijective_base_iff_degree_eq_one, degree_sq]
  norm_num

end

end ComplexAnalytic
