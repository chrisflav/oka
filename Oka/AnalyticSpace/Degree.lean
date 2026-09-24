/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.AnalyticSpace.SigmaFiniteEtale
import Oka.SetTheory.Cardinal.Finite

/-!
# The degree of a morphism of complex analytic spaces

`ComplexAnalytic.AnalyticSpace.degree` is the number of sheets of a finite étale morphism, as a
single natural number attached to the morphism rather than a theorem about a pair of points.

## Why this was declined before, and what discharges the objection

Four docstrings in this development used to record the absence of a `degree` function, with the
same two-part reason: a `Nat`-valued definition carries a **well-definedness obligation**, and
**nothing consumed one**. Both parts are answered here and neither is answered by fiat.

* The obligation is discharged by `ComplexAnalytic.AnalyticSpace.degree_eq_card_fiber`, which is
  `ComplexAnalytic.AnalyticSpace.card_fiber_eq_of_isFiniteEtale` — constancy of the fibre over a
  preconnected base — read at the definition. Note the direction of the dependency: the definition
  below is made for *every* morphism and is well-behaved only under the hypotheses of that
  theorem, exactly as `Nat.card` is defined for every type and is informative only on a finite
  one.
* The consumer is `ComplexAnalytic.AnalyticSpace.isHomeomorph_base_of_degree_eq_one`: a finite
  étale morphism of degree one has a homeomorphism for its underlying map. That statement cannot
  be phrased at all without a degree — "all fibres have the same size" does not say what the size
  is, and "this particular fibre is a singleton" is a statement about a point.

## The definition is an `iSup` and not a value at a chosen point

`⨆ y, Nat.card (f ⁻¹' {y})` needs no point of the target and no `[Nonempty Y]`, where
`Nat.card (f ⁻¹' {Classical.arbitrary Y})` would need one in the *definition* and thereby in the
statement of every lemma about it. The cost is that the two facts a reader wants are separate:

* over the empty target the value is `0`, since an `iSup` over an empty index type is `⊥`;
* over a non-empty target on which the fibre count is constant the value is that constant, which
  is `ComplexAnalytic.AnalyticSpace.degree_eq_of_forall_card_fiber_eq` and is `ciSup_const`.

Everything below goes through the second of those, including the two computations. **No covering
map theory enters any of them except `ComplexAnalytic.AnalyticSpace.degree_eq_card_fiber`**, which
is the only statement here that needs the fibres to be *related* to each other rather than
computed one at a time.

## What was recorded as not proved, and the reason given for it was not the obstruction

`ComplexAnalytic.AnalyticSpace.isHomeomorph_base_of_degree_eq_one` concludes a homeomorphism of
the **underlying spaces** and not an isomorphism of analytic spaces, although
`ComplexAnalytic.AnalyticSpace.IsLocalIso` also carries an isomorphism on every stalk. This
section used to say that the two together ought to give an isomorphism and that **the step from
them to one is a comparison of sheaves across a homeomorphism which this development does not
have**. That step is now `ComplexAnalytic.AnalyticSpace.isIso_of_degree_eq_one`, and **the reason
recorded for its absence was wrong rather than out of date**.

* The comparison of sheaves is
  `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.of_stalk_iso` — an open embedding whose
  stalk maps are isomorphisms is an open immersion — which has been in Mathlib, at exactly the
  generality wanted, the whole time. Nothing had to be written by hand and nothing was.
* What *is* repository-side is a single obligation and it is not about sheaves: the inverse has to
  be shown `ℂ`-linear before an isomorphism of locally ringed spaces is one of analytic spaces.
  That is `ComplexAnalytic.AnalyticSpace.forgetToLocallyRingedSpace_reflectsIsomorphisms`
  (`Oka/AnalyticSpace/Basic.lean`), whose proof is one application of
  `ComplexAnalytic.IsCLinearHom.of_comp`.

**This section also said that `Oka/AnalyticSpace/LocalIso.lean` records the same gap from the
other side, and that file records no such thing** — its `## What is not here` names the Riemann
existence theorem, the analytification of a finite étale morphism, Grauert's finite mapping
theorem, and two absences it records as since retired, a `degree` function and cancellation for
finite étale morphisms; none of them is this gap. The nearest sentence there is
`ComplexAnalytic.AnalyticSpace.surjective_base_of_isLocalIso_of_isFinite`'s *the same gap from
opposite sides*, which is about surjectivity and the empty index type and is a different sentence
about a different gap. The pointer is dropped rather than repaired.

What is retired is the clause that **the degree of a morphism is at present a topological invariant
of it** — degree one now decides an isomorphism of analytic spaces and not only of the underlying
spaces.

## Multiplicativity in a composite, and what the count actually costs

The paragraph that stood here said multiplicativity was *not proved either*, that it is true, and
that *the proof is a fibrewise count over the intermediate space that has nothing to do with the
material below*. **The prediction was right and `ComplexAnalytic.AnalyticSpace.degree_comp` is
it.** The count is `Nat.card_preimage_singleton_comp` (`Oka/SetTheory/Cardinal/Finite.lean`), a
statement about three bare functions with no topology and no analytic content in it, and it does
have nothing to do with the material above.

**What the count does not supply is the hypotheses, and they all come from one place.** The fibre
of the composite over a point of the target has to be counted as the fibres of the first map over
the fibre of the second, so *both* of those counts have to be known to be independent of the point
they are taken at, and that is `ComplexAnalytic.AnalyticSpace.degree_eq_card_fiber` applied twice
— once at each factor. Its `[T2Space]` and `[PreconnectedSpace]` are why `degree_comp` asks for a
Hausdorff source, a Hausdorff *and* preconnected intermediate space and a preconnected target,
where the count itself asks for nothing but finiteness. **Whether the separation axioms can be
weakened is not measured here.**

**Preconnectedness of the intermediate space is the hypothesis a reader should look at twice.** It
is not a hypothesis about the composite at all: it says the *middle* of the factorisation is
connected, and the trivial cover of a connected base already fails it at more than one sheet. So
`degree_comp` is not a statement about arbitrary factorisations of a finite étale morphism, and
the consumer it was written for —
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.degree_eq_mul`
(`Oka/AnalyticSpace/FiniteEtaleOver.lean`) — carries it as a hypothesis on the target cover rather
than discharging it.

## Main definitions

- `ComplexAnalytic.AnalyticSpace.degree`: **the number of sheets**, as a natural number.

## Main results

- `ComplexAnalytic.AnalyticSpace.degree_eq_card_fiber`: it is the size of the fibre over any
  point, for a finite étale morphism over a preconnected base — the well-definedness statement.
- `ComplexAnalytic.AnalyticSpace.degree_id` and
  `ComplexAnalytic.AnalyticSpace.degree_sigmaFold`: the degree of an identity is `1`, and the
  degree of the trivial `ι`-sheeted cover is `Nat.card ι`, so **every value is realised**.
- `ComplexAnalytic.AnalyticSpace.bijective_base_iff_degree_eq_one` and
  `ComplexAnalytic.AnalyticSpace.isHomeomorph_base_of_degree_eq_one`: **degree one means the
  underlying map is a homeomorphism.**
- `ComplexAnalytic.AnalyticSpace.isIso_of_degree_eq_one`: **degree one means the morphism is an
  isomorphism of analytic spaces**, at the same hypotheses as the homeomorphism. The step from
  the one to the other is `ComplexAnalytic.AnalyticSpace.isIso_of_isLocalIso_of_bijective`
  (`Oka/AnalyticSpace/LocalIso.lean`), and this file supplies it the bijectivity.
- `ComplexAnalytic.AnalyticSpace.degree_comp`: **the degree is multiplicative in a composite**,
  over a preconnected target and a Hausdorff, preconnected intermediate space. The empty target is
  not excluded: both sides are `0` there and the case is closed separately rather than by a
  `[Nonempty _]` on the statement.
- `ComplexAnalytic.AnalyticSpace.degree_comp_of_bijective_base` and
  `ComplexAnalytic.AnalyticSpace.degree_isIso_comp`: **the degree does not see a change of source**
  — precomposing with a morphism that is bijective on points, in particular with an isomorphism,
  leaves it alone. This is what makes the degree an invariant of an *object* of the category of
  covers rather than of a morphism, which is where
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.degree`
  (`Oka/AnalyticSpace/FiniteEtaleOver.lean`) reads it.

## References

- [Hans Grauert and Reinhold Remmert, *Coherent analytic sheaves*][grauert-remmert1984]
-/

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry Topology

universe u

namespace ComplexAnalytic.AnalyticSpace

variable {ι : Type u} {X Y : AnalyticSpace.{u}}

/-- **The degree, or number of sheets, of a morphism of complex analytic spaces**: the supremum
over the target of the number of points of a fibre.

The definition is made for an arbitrary morphism, with no hypothesis at all, and is informative
exactly when the fibre count is constant and finite —
`ComplexAnalytic.AnalyticSpace.degree_eq_card_fiber` is that statement for a finite étale morphism
over a preconnected base, and is the well-definedness obligation the module docstring is about.

**Two junk values are folded into the one expression and they are different junk.** `Nat.card` of
an infinite fibre is `0`, and an `iSup` over an empty target — or over a family of fibre counts
that is unbounded — is `0` as well, since `ℕ` is a `ConditionallyCompleteLinearOrderBot`. Neither
is reachable under the hypotheses of the theorems below, and neither is repaired by choosing a
point of the target instead: that choice merely moves the empty case into the *statement* of every
lemma, as a `[Nonempty Y]` the definition would then need. -/
noncomputable def degree (f : X ⟶ Y) : ℕ :=
  ⨆ y : Y, Nat.card (f.toLRSHom.base ⁻¹' {y})

/-- **A morphism all of whose fibres have `n` points, over a non-empty target, has degree `n`.**

This is `ciSup_const` and nothing else; it is stated because every computation of a degree below
is an instance of it, and because it is where the `[Nonempty Y]` that
`ComplexAnalytic.AnalyticSpace.degree` deliberately does not carry has to be supplied.

The hypothesis is about each fibre separately, so no covering-space theory is involved and no
finiteness is asked of anything. -/
theorem degree_eq_of_forall_card_fiber_eq (f : X ⟶ Y) [Nonempty Y] {n : ℕ}
    (h : ∀ y : Y, Nat.card (f.toLRSHom.base ⁻¹' {y}) = n) : degree f = n := by
  rw [degree]
  simp_rw [h]
  exact ciSup_const

/-- **The degree of a finite étale morphism over a preconnected base is the number of points of
the fibre over any point**, which is the well-definedness statement for
`ComplexAnalytic.AnalyticSpace.degree`.

`ComplexAnalytic.AnalyticSpace.card_fiber_eq_of_isFiniteEtale` says the fibre count is constant;
this says the constant is the degree. The point `y` supplies the `[Nonempty Y]` that
`ComplexAnalytic.AnalyticSpace.degree_eq_of_forall_card_fiber_eq` needs, so no separate
non-emptiness hypothesis appears.

This is the only statement in this file that uses the covering-map theory; the two computations
below reach their fibre counts one point at a time and use none of it. -/
theorem degree_eq_card_fiber (f : X ⟶ Y) [IsFiniteEtale f] [T2Space X] [PreconnectedSpace Y]
    (y : Y) : degree f = Nat.card (f.toLRSHom.base ⁻¹' {y}) :=
  haveI : Nonempty Y := ⟨y⟩
  degree_eq_of_forall_card_fiber_eq f fun y' ↦ card_fiber_eq_of_isFiniteEtale f y' y

/-- **The identity has degree one**, on a non-empty space.

The anchor for the scale: every fibre of `𝟙 X` is a singleton, so
`ComplexAnalytic.AnalyticSpace.degree_eq_of_forall_card_fiber_eq` applies with no hypothesis
beyond `[Nonempty X]`, and in particular without `[T2Space X]` or preconnectedness. On the empty
space the degree is `0` instead, which is the `iSup` convention and not a defect. -/
theorem degree_id (X : AnalyticSpace.{u}) [Nonempty X] : degree (𝟙 X) = 1 := by
  refine degree_eq_of_forall_card_fiber_eq _ fun x ↦ ?_
  have h : ((𝟙 X : X ⟶ X).toLRSHom.base : X → X) = _root_.id := rfl
  rw [h, Set.preimage_id]
  exact Nat.card_unique

/-- **The trivial `ι`-sheeted cover has degree `Nat.card ι`.**

`ComplexAnalytic.AnalyticSpace.card_fiber_sigmaFold` computes each fibre separately, so this is
`ComplexAnalytic.AnalyticSpace.degree_eq_of_forall_card_fiber_eq` applied to it and there is no
analysis and no covering-space theory in it. `[Finite ι]` is not needed, for the same reason it is
not needed there — and for the same reason the statement says nothing for an infinite `ι`, both
sides being `0`.

`[Nonempty X]` is needed and is not decorative: over the empty space the coproduct is empty too
and the degree is `0`, while `Nat.card ι` need not be.

**Together with `ComplexAnalytic.AnalyticSpace.degree_id` this realises every value**: at
`ι = ULift (Fin n)` the degree is `n`, for every `n`, and the morphism is finite étale by
`ComplexAnalytic.AnalyticSpace.isFiniteEtale_sigmaFold`. What it does not give is a *connected*
source, so the trivial covers say nothing about the degree of a cover that is not a disjoint union
of copies of its base, such as the squaring map of the punctured line. -/
theorem degree_sigmaFold (ι : Type u) (X : AnalyticSpace.{u}) [Nonempty X] :
    degree (sigmaFold ι X) = Nat.card ι :=
  degree_eq_of_forall_card_fiber_eq _ (card_fiber_sigmaFold X)

/-! ### Invariance under a change of source -/

/-- **Precomposing with a morphism that is bijective on points does not change the degree.**

Each fibre of `e ≫ f` over `y` is the `e`-preimage of the fibre of `f` over `y`, and a bijection
preserves `Nat.card` of a preimage (`Nat.card_preimage_of_injective`, whose second hypothesis
`s ⊆ Set.range _` is what surjectivity discharges); the two suprema are then equal term by term,
by `iSup_congr`, with no case split on finiteness and no `[Nonempty _]` anywhere.

**Bijectivity is not weakenable to either half.** Injectivity alone leaves a fibre of `f` that `e`
misses, whose points the left-hand count does not see; surjectivity alone lets two points of the
source lie over one, and the left-hand count is then too large. So this is one of the few places
in this development where `ComplexAnalytic.AnalyticSpace.bijective_base_of_isIso` is wanted and
`ComplexAnalytic.AnalyticSpace.surjective_base_of_isIso` is not enough.

**The hypothesis is on the base map alone and nothing sheaf-theoretic enters**, which is why this
is stated for an arbitrary morphism with a bijective base rather than for an isomorphism: the
isomorphism case is `ComplexAnalytic.AnalyticSpace.degree_isIso_comp` below and is the corollary
every consumer wants.

**The `rw [degree, degree]` names a definition and costs nothing here**, which is worth saying
because `Oka/Analytification/RefineDatumToBase.lean` states the opposite rule and it is the same
rule: naming a definition as a rewrite rule generates its equation lemma **once per definition,
not once per proof**, and `ComplexAnalytic.AnalyticSpace.degree.eq_1` is already in
`scripts/DumpOkaDecls.lean`'s output on this branch's base — generated by
`ComplexAnalytic.AnalyticSpace.degree_eq_of_forall_card_fiber_eq` above, which spells its proof
the same way. Measured on both refs. Where the same spelling *would* have cost a row is
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.degree_eq_of_iso`
(`Oka/AnalyticSpace/FiniteEtaleOver.lean`), whose definition no other proof names, and that
docstring records the measurement. -/
theorem degree_comp_of_bijective_base {W X Y : AnalyticSpace.{u}} (e : W ⟶ X) (f : X ⟶ Y)
    (he : Function.Bijective (e.toLRSHom.base : W → X)) :
    degree (e ≫ f) = degree f := by
  rw [degree, degree]
  refine iSup_congr fun y ↦ ?_
  have hb : ((e ≫ f).toLRSHom.base : W → Y) = f.toLRSHom.base ∘ e.toLRSHom.base := rfl
  rw [hb, Set.preimage_comp]
  exact Nat.card_preimage_of_injective he.injective (by simp [he.surjective.range_eq])

/-- **Precomposing with an isomorphism does not change the degree.**

`ComplexAnalytic.AnalyticSpace.degree_comp_of_bijective_base` at
`ComplexAnalytic.AnalyticSpace.bijective_base_of_isIso`, and nothing else. It asks nothing of `f`
— not finite, not étale, not a preconnected base — because the fibrewise argument above asks
nothing of it either.

**This is the statement that makes the degree an invariant of an object of
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver`**: a morphism of covers over `X` is a triangle, so
an isomorphism of covers exhibits one structure map as an isomorphism precomposed with the other,
and this says the two structure maps then have the same degree. That consumer is
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.degree_eq_of_iso`
(`Oka/AnalyticSpace/FiniteEtaleOver.lean`).

**Postcomposition is a different statement and is not here, in either direction.**
`degree (f ≫ e) = degree f` for an isomorphism `e` relabels the *target*, so its proof would be a
reindexing of the supremum rather than the fibrewise argument above; **this file neither states
nor proves it**, and nothing below or downstream asks for it — a triangle over a fixed base
produces the precomposition and not this. -/
theorem degree_isIso_comp {W X Y : AnalyticSpace.{u}} (e : W ⟶ X) [IsIso e] (f : X ⟶ Y) :
    degree (e ≫ f) = degree f :=
  degree_comp_of_bijective_base e f (bijective_base_of_isIso e)

/-- **A finite étale morphism over a preconnected base has degree one exactly when its underlying
map is bijective.**

The consumer the earlier refusals of a `degree` function said did not exist. Both directions are
`Function.bijective_iff_forall_card_preimage_eq_one` — bijectivity of a map is precisely every
fibre having one point — together with
`ComplexAnalytic.AnalyticSpace.degree_eq_card_fiber` to move between "every fibre" and "the
degree". The forward direction is the one that needs the constancy: from a single fibre of size
one it concludes the degree, and that step is the well-definedness theorem.

`[Nonempty Y]` is genuine on the right and invisible on the left: over the empty target every map
is bijective while the degree is `0`. -/
theorem bijective_base_iff_degree_eq_one (f : X ⟶ Y) [IsFiniteEtale f] [T2Space X]
    [PreconnectedSpace Y] [Nonempty Y] :
    Function.Bijective (f.toLRSHom.base : X → Y) ↔ degree f = 1 := by
  rw [Function.bijective_iff_forall_card_preimage_eq_one]
  refine ⟨fun h ↦ degree_eq_of_forall_card_fiber_eq f h, fun h y ↦ ?_⟩
  rw [← degree_eq_card_fiber f y, h]

/-- **A finite étale morphism of degree one is a homeomorphism on the underlying spaces.**

The three inputs to `isHomeomorph_iff_continuous_isClosedMap_bijective` are, in order, the
continuity a `TopCat` morphism carries with it, the closedness field of
`ComplexAnalytic.AnalyticSpace.IsFinite`, and
`ComplexAnalytic.AnalyticSpace.bijective_base_iff_degree_eq_one`. **The local-homeomorphism field
of `ComplexAnalytic.AnalyticSpace.IsLocalIso` is not used**, and neither is the covering-map
theorem: a closed continuous bijection is a homeomorphism whether or not it is a local one.

**The conclusion is topological and is weaker than the statement with the same hypotheses.**
`IsLocalIso` also gives an isomorphism on every stalk, and the two together do give an isomorphism
of analytic spaces: that is `ComplexAnalytic.AnalyticSpace.isIso_of_degree_eq_one`, at the same
hypotheses as this. **This paragraph used to say the step was a comparison of the two structure
sheaves across the homeomorphism which this development does not have**, and the module docstring
records why that was the wrong reason. This statement is kept because a caller wanting a
homeomorphism should not have to build an isomorphism and forget it, and because its proof reads
no stalk: it does not use the local-homeomorphism field either, so it is a statement about a
closed continuous bijection and nothing more.

It still says nothing about the squaring map of the punctured line, whose degree is not one, and
it is still not the converse of anything stated here.

**One morphism of degree one was known to be an isomorphism before any of this, and it is still
not got this way.** The trivial cover at one sheet is, by
`ComplexAnalytic.AnalyticSpace.isIso_sigmaFold`
(`Oka/AnalyticSpace/SigmaFiniteEtale.lean`), whose proof is the universal property of the disjoint
union and reads no sheaf and no fibre — and it needs neither `[T2Space]` nor `[PreconnectedSpace]`
nor a degree. **That is still worth its paragraph**: it is a fact about that one morphism, got
with no hypothesis at all, where `ComplexAnalytic.AnalyticSpace.isIso_of_degree_eq_one` asks for
all three. -/
theorem isHomeomorph_base_of_degree_eq_one (f : X ⟶ Y) [IsFiniteEtale f] [T2Space X]
    [PreconnectedSpace Y] [Nonempty Y] (h : degree f = 1) :
    IsHomeomorph (f.toLRSHom.base : X → Y) :=
  isHomeomorph_iff_continuous_isClosedMap_bijective.mpr
    ⟨f.toLRSHom.base.hom.continuous, IsFinite.isClosedMap,
      (bijective_base_iff_degree_eq_one f).mpr h⟩

/-- **A finite étale morphism of degree one is an isomorphism of analytic spaces.**

This is `ComplexAnalytic.AnalyticSpace.bijective_base_iff_degree_eq_one` fed to
`ComplexAnalytic.AnalyticSpace.isIso_of_isLocalIso_of_bijective`
(`Oka/AnalyticSpace/LocalIso.lean`). **The bijectivity was already here and only its topological
consequence had a consumer**: `ComplexAnalytic.AnalyticSpace.isHomeomorph_base_of_degree_eq_one`
reads the same equivalence and stops at the underlying spaces.

**The hypotheses are exactly the ones the degree needs**, and none of them is spent by the step to
an isomorphism. `[T2Space X]` and `[PreconnectedSpace Y]` are what make the fibre count constant,
`[Nonempty Y]` is what
`ComplexAnalytic.AnalyticSpace.bijective_base_iff_degree_eq_one` needs to read a degree off it,
and `ComplexAnalytic.AnalyticSpace.isIso_of_isLocalIso_of_bijective` asks for no separation axiom
and no connectedness. The hypothesis-free form is
`ComplexAnalytic.AnalyticSpace.isIso_of_isFiniteEtale_of_injective`, which takes injectivity
instead of a degree and asks nothing of `X` beyond being non-empty.

**This refutes no `IsIso`.** Refuting an `IsIso` is a different shape and its general form is
`ComplexAnalytic.AnalyticSpace.surjective_base_of_isIso` (`Oka/AnalyticSpace/Basic.lean`). -/
theorem isIso_of_degree_eq_one (f : X ⟶ Y) [IsFiniteEtale f] [T2Space X] [PreconnectedSpace Y]
    [Nonempty Y] (h : degree f = 1) : IsIso f :=
  isIso_of_isLocalIso_of_bijective f ((bijective_base_iff_degree_eq_one f).mpr h)

/-! ### Multiplicativity in a composite -/

/-- **The degree is multiplicative in a composite.**

The fibre of `f ≫ g` over a point `z` of the target is the union of the fibres of `f` over the
points of the fibre of `g` over `z`, and `Nat.card_preimage_singleton_comp`
(`Oka/SetTheory/Cardinal/Finite.lean`) is that as a count. The two applications of
`ComplexAnalytic.AnalyticSpace.degree_eq_card_fiber` around it are what make the two counts
independent of the points they are taken at, and they are where every hypothesis comes from: the
`[T2Space X]` and `[PreconnectedSpace Y]` of the first, the `[T2Space Y]` and
`[PreconnectedSpace Z]` of the second.

**The empty target is handled and not excluded.** `ComplexAnalytic.AnalyticSpace.degree` is an
`iSup`, so over an empty target it is `0` on the left and `degree g` is `0` on the right; the case
split is `isEmpty_or_nonempty` and it is what lets this statement avoid the `[Nonempty Z]` that
`ComplexAnalytic.AnalyticSpace.degree_eq_of_forall_card_fiber_eq` needs.

**`[PreconnectedSpace Y]` is a hypothesis about the middle of the factorisation** and is not
implied by anything about `f ≫ g`; the module docstring says what that costs a caller. The
finiteness of the fibres is not a hypothesis: it is a field of
`ComplexAnalytic.AnalyticSpace.IsFinite`, reached through
`ComplexAnalytic.AnalyticSpace.IsFiniteEtale.isFinite`, and the two `haveI`s below are that
projection at the two maps rather than an assumption.

**The `rw [hb, …]` names the base map of the composite as a composite of base maps and the proof
of that is `rfl`**, which is the step
`ComplexAnalytic.AnalyticSpace.degree_comp_of_bijective_base` above takes and the one
`ComplexAnalytic.AnalyticSpace.isFinite_comp` (`Oka/AnalyticSpace/Finite.lean`) takes in each of
its fields. -/
theorem degree_comp {X Y Z : AnalyticSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsFiniteEtale f] [IsFiniteEtale g] [T2Space X] [T2Space Y]
    [PreconnectedSpace Y] [PreconnectedSpace Z] :
    degree (f ≫ g) = degree f * degree g := by
  rcases isEmpty_or_nonempty Z with hZ | hZ
  · simp [degree, ciSup_of_empty]
  · refine degree_eq_of_forall_card_fiber_eq _ fun z ↦ ?_
    have hb : ((f ≫ g).toLRSHom.base : X → Z)
        = (g.toLRSHom.base : Y → Z) ∘ (f.toLRSHom.base : X → Y) := rfl
    haveI : Finite (((g.toLRSHom.base : Y → Z) ⁻¹' {z}) : Set Y) := IsFinite.finite_fiber z
    haveI : ∀ y : Y, Finite (((f.toLRSHom.base : X → Y) ⁻¹' {y}) : Set X) :=
      fun y ↦ IsFinite.finite_fiber y
    rw [hb, Nat.card_preimage_singleton_comp _ _ _ (d := degree f)
      (fun y ↦ (degree_eq_card_fiber f y).symm), ← degree_eq_card_fiber g z, mul_comm]

end ComplexAnalytic.AnalyticSpace
