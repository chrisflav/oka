/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.AnalyticSpace.Basic

/-!
# Finite morphisms of complex analytic spaces

A holomorphic map is **finite** when it is closed and has finite fibres. That is the classical
definition — Grauert–Remmert take it, and so does Fischer — and it is what this file gives to
`ComplexAnalytic.AnalyticSpace.Hom`, together with the stability properties that make it usable
and the two implications that make it non-vacuous.

## Why this definition and not the algebraic-geometry one

`AlgebraicGeometry.IsFinite` for schemes is `IsAffineHom f` together with `RingHom.Finite` on the
sections over every affine open, and its whole API — `HasAffineProperty`, `affineAnd`, stability
under composition and base change — is derived from affine-locality. **There are no affines in the
analytic category**, and the reason is that the machinery affine-locality is built out of does not
exist here: there is no `Spec`–`Γ` adjunction for analytic spaces, so no class of objects on which
a morphism's behaviour determines it globally, and no `HasAffineProperty` to state a property
against. `ComplexAnalytic.AnalyticSpace` is defined by local models, and a local model is a closed
subspace of an open subset of `ℂ^n` — a chart, not an affine. So none of that transfers and there
is no `IsAffineHom` to extend.

The two conditions are also not the same notion, so this is not a choice between spellings of one
thing. For schemes, `Spec` of an infinite algebraic field extension `k ⟶ K` is a homeomorphism
between one-point spaces, hence closed with finite fibres, while `k ⟶ K` is not module-finite; so
`AlgebraicGeometry.IsFinite` fails there and the condition below holds. **That example is not
formalised here** and nothing in this file depends on it; it is recorded because it is the reason
the class is stated in the `ComplexAnalytic` namespace rather than for
`AlgebraicGeometry.LocallyRingedSpace` in the mirror tree, where its name would read as the
scheme-theoretic condition and would specialise to a different one.

## Properness, and exactly what agrees with what

A finite morphism is proper: `ComplexAnalytic.AnalyticSpace.isProperMap_base_of_isFinite`. That
is a theorem rather than part of the definition, and it needs **no separation hypothesis** — a
finite set is compact in any topological space, unlike the covering-map statement in
`Oka/AnalyticSpace/CoveringMap.lean`, which does need one on the source.

**The converse is false, and this file used to say "proper and finite-with-finite-fibres agree"
in a way that invited the false reading.** Properness gives *compact* fibres, and a compact fibre
is finite only when it is also discrete, so properness alone does not imply finiteness. What is
true is the agreement with finiteness of the fibres carried on **both** sides: `IsFinite f` iff
the underlying map is proper and has finite fibres, which is
`ComplexAnalytic.AnalyticSpace.isFinite_iff_isProperMap_base_and_finite_fiber`. Read that way the
content of the agreement is exactly `IsProperMap ↔ IsClosedMap` **given** finite fibres, which is
where the two directions sit: one is `IsProperMap.isClosedMap`, the other is the compactness of a
finite set.

There is deliberately no `IsProper` class. `IsProperMap` on `f.toLRSHom.base` already is the
statement; a class would have to carry its own identity, composition and non-vacuity API to earn
its place, and nothing here or downstream consumes one.

## Cancellation, and which hypothesis each half needs

The two fields cancel differently, and saying which is which is what keeps the finite étale rung's
gap legible. **The fibre half cancels outright**:
`ComplexAnalytic.AnalyticSpace.finite_fiber_of_comp` deduces finite fibres for `f` from finite
fibres for `f ≫ g`, and asks nothing whatever of `g` — not finiteness, not closedness, not
injectivity — because the fibre of `f` over `y` sits inside the fibre of `f ≫ g` over `g y`.

**The closed half does not, and it does not even given that `g` is finite.** Take the real line
with two origins over the real line, with `f` the inclusion of one of the two branches: then
`f ≫ g` is the identity, hence closed with finite fibres, and `g` is closed with fibres of at most
two points, while the complement of the image of `f` is the other origin alone, which is not open
— so `f` is not closed. **That is a statement about topological spaces, and one of that shape is
now compiled**: `TwoIndiscrete.not_isClosedMap_pt_of_isClosedMap_comp`
(`OkaTest/FiniteEtaleCancel.lean`) exhibits a `g` that is continuous, closed and has finite
fibres, an `f` that is continuous, a
closed `f ≫ g` and a non-closed `f`. It is a two-point indiscrete space and not the line with two
origins, so it is the weaker witness — its `g` is not a local homeomorphism and its middle space
is not T1. **The line with two origins itself is compiled beside it**, as
`LineTwoOrigins.not_isClosedMap_inc_of_isClosedMap_comp`, with a `g` that *is* a local
homeomorphism, so the paragraph above is now a theorem at the space it argues with.

That paragraph does not collide with `ComplexAnalytic.AnalyticSpace.isFinite_of_isFinite_comp`,
which is this file's older cancellation lemma and asks the second factor to be injective: the `g`
above is exactly not that, at the two origins.

**What the two witnesses have in common is not their second factor, and that is what the closed
half actually needs.** In both, the middle space carries two topologically indistinguishable
points — the two origins, and the two points of the indiscrete pair — and that is the whole of
what keeps the image of `f` from being closed. **A separation axiom on the middle space, and
nothing about `g`, is therefore the hypothesis**:
`ComplexAnalytic.AnalyticSpace.isFinite_of_comp_of_t2Space` asks `[T2Space Y]` and asks of `g`
exactly what the fibre half asks, which is nothing. **So both halves cancel**, and the whole cost
of the pair is one separation axiom on `Y`.

**The classical repair is not needed, and this file used to imply that it was the only route.**
Factoring `f` through its graph and asking `Y` to be separated over the base needs a separatedness
notion and a fibre product `Y ×_S Y` at an arbitrary analytic space `Y`, and neither of those is
here — that absence is real and is recorded in the base-change paragraph
below. **This sentence read *needs a separatedness notion and fibre products, and
neither exists here* until `Oka/AnalyticSpace/PullbackOpen.lean` landed**, which builds the one
shape the graph construction cannot use. It is not what was obstructing this:
`isProperMap_of_comp_of_t2` is Mathlib's cancellation for proper maps at `[T2Space Y]` and asks
nothing of the second factor beyond continuity, and a finite morphism is proper
(`ComplexAnalytic.AnalyticSpace.isProperMap_base_of_isFinite`), so the closed half is those two
lemmas and no new topology at all. **`[T2Space Y]` is a genuine hypothesis and not an instance
that will be found** — `Oka/AnalyticSpace/Basic.lean` imposes no separation axiom, as
`AlgebraicGeometry.Scheme` does not — and the counterexample above is exactly the witness that it
cannot be dropped.

**The clause repaired above read *a fibre product over a cospan neither of whose legs is the
inclusion of an open subspace* until 2026-09-07**, when
`Oka/AnalyticSpace/CutOutFibreProduct.lean` built a fibre product over exactly such a cospan:
`ComplexAnalytic.AnalyticSpace.hasPullback_ofCutOut` is a `CategoryTheory.Limits.HasPullback`
instance at a cospan of two *local models* over a third, and neither of its legs is the inclusion
of an open subspace or is finite étale. **What that file does not reach is the cospan the graph
construction forms**, whose two legs are the same morphism out of an arbitrary analytic space `Y`
— and an arbitrary `Y` need not be a local model, which is why the repaired clause names the
object it wants rather than the shape of the legs. `CategoryTheory.Limits.HasPullbacks
ComplexAnalytic.AnalyticSpace` still does not synthesise, on a run at the commit carrying this
record, so the absence is narrowed and not struck.

**The absence is struck now.** `Oka/AnalyticSpace/PullbackReduction.lean` made that class a
theorem on 2026-09-08, `ComplexAnalytic.AnalyticSpace.hasPullbacks`, so the cospan the graph
construction forms has a fibre product like every other. **The clause repaired twice above is
retired outright and nothing above is struck**: each of its three readings was exact at the run
recorded beside it, and the last of them — *`CategoryTheory.Limits.HasPullbacks
ComplexAnalytic.AnalyticSpace` still does not synthesise* — is pinned to the commit carrying the
record and stays where it is. **What does not follow is that the classical route is now the one
this file takes**: `ComplexAnalytic.AnalyticSpace.isFinite_of_comp_of_t2Space` proves the
cancellation at `[T2Space Y]` with no fibre product at all, and that proof is unchanged.

## What is not here, and it is the whole of the subject

**Grauert's finite mapping theorem** — that `f_*𝒪_X` is a coherent `𝒪_Y`-module for finite `f` —
is what makes this definition useful, and it is not proved here or anywhere in this repository.
Nothing below mentions a pushforward. That absence stands; the properness clause that used to
stand beside it does not, and is now the section above.

**Finite covers are a further condition and are not defined here.** The Riemann existence theorem
is about finite *étale* covers — finite together with being a local isomorphism — and that is a
second notion resting on this one.

**Base change along a general morphism is absent, and along two particular shapes of leg it is
elsewhere in this repository.** `AlgebraicGeometry.IsFinite`'s `IsStableUnderBaseChange`
quantifies over every cospan and has no analogue below, because nothing here carries finiteness
across a square whose base is arbitrary. **The reason clause read *because a fibre product over a
general cospan is what `Oka/AnalyticSpace/PullbackOpen.lean`'s header prices and does not build*
until 2026-09-08**, when `Oka/AnalyticSpace/PullbackReduction.lean` built one
(`ComplexAnalytic.AnalyticSpace.hasPullbacks`); the absence stated here is unchanged and only its
reason is, the missing thing being the transfer of the class and no longer the limit. What
`Oka/AnalyticSpace/PullbackOpen.lean` does build is the pullback along the inclusion of an open
subspace, and
`ComplexAnalytic.AnalyticSpace.isFinite_restrictHom` there is finiteness carried across it, with
no hypothesis on the open subset. **The words `and along the inclusion of an open subspace it is
here` closed the sentence above until 2026-09-07**, when
`Oka/AnalyticSpace/FiniteEtaleBaseChange.lean` gave a second shape:
`ComplexAnalytic.AnalyticSpace.baseChangeSnd` is the projection of a fibre product over a cospan
whose other leg is finite étale, and it is finite étale — hence finite — with no hypothesis on the
leg it is a base change of. **That clause read *whose other leg is finite étale with Hausdorff
source* until 2026-09-14**, when the separation axiom came out of that file; the shape is wider
and the record it sits in is unmoved. Neither shape is a general morphism and
neither is below.

**This paragraph said flatly that there is no base change and that this repository has no fibre
products of analytic spaces.** Both were exact at `e8c5f03`, the commit
`Oka/AnalyticSpace/PullbackOpen.lean`'s header pins its `#synth` failures to, and the push that
added that file falsified them. The absence that is left is stated here rather than left to be
discovered.

## Main definitions

- `ComplexAnalytic.AnalyticSpace.IsFinite`: **a morphism of complex analytic spaces is finite when
  its underlying map is closed and has finite fibres.**

## Main results

- `ComplexAnalytic.AnalyticSpace.isFinite_id` and
  `ComplexAnalytic.AnalyticSpace.isFinite_comp`: the finite morphisms contain the identities and
  are closed under composition.
- `ComplexAnalytic.AnalyticSpace.isFinite_of_isIso`: an isomorphism is finite.
- `ComplexAnalytic.AnalyticSpace.isFinite_of_isClosedEmbedding` and
  `ComplexAnalytic.AnalyticSpace.isFinite_of_isCutOutBy`: **a closed embedding is finite, and
  hence so is every morphism cutting its source out of its target by global sections** — which is
  every local model this development builds.
- `ComplexAnalytic.AnalyticSpace.isFinite_comp_of_isClosedEmbedding`: **a closed embedding
  followed by a map that is closed and has finite fibres *over the image of that embedding* is
  finite**, even when the second factor is not.
- `ComplexAnalytic.AnalyticSpace.isFinite_of_isFinite_comp`: **finiteness cancels along an
  injective second factor** — if `f ≫ i` is finite and the underlying map of `i` is injective,
  then `f` is finite. This is what carries a finiteness statement proved over an ambient `ℂ^n`
  back to one over a closed analytic subspace of it, which is the shape the standard-étale line
  needs: `Oka/Analytification/MonicHypersurface.lean` proves the projection of a hypersurface to
  `ℂ^n` finite, and `Oka/Analytification/HypersurfaceFinite.lean` cancels
  `ComplexAnalytic.isClosedEmbedding_base_analytificationIncl` against it to get finiteness over
  the analytification of the base algebra — `A ⟶ A[X] ⧸ (F)` for `F` monic, which is this
  theorem's first consumer that is not about `ℂ^n`.
- `ComplexAnalytic.AnalyticSpace.finite_fiber_of_comp`: **the fibre half of finiteness cancels
  with no hypothesis at all** — if `f ≫ g` has finite fibres then so does `f`, and the second
  factor is not asked to be finite, closed or injective.
- `ComplexAnalytic.AnalyticSpace.isFinite_of_comp_of_t2Space`: **the closed half cancels too, and
  the only thing it costs is a separation axiom on the middle space** — if `f ≫ g` is finite and
  the target of `f` is Hausdorff then `f` is finite, with nothing asked of the second factor
  either. See the cancellation section above for the counterexample that says the separation
  axiom cannot be dropped.
- `ComplexAnalytic.AnalyticSpace.not_isFinite_of_infinite_fiber`: the criterion a non-example is
  exhibited by.
- `ComplexAnalytic.AnalyticSpace.isProperMap_base_of_isFinite`: **a finite morphism is proper**,
  and `ComplexAnalytic.AnalyticSpace.isFinite_iff_isProperMap_base_and_finite_fiber` is the
  agreement in both directions.

## References

- [Hans Grauert and Reinhold Remmert, *Coherent analytic sheaves*][grauert-remmert1984]
-/

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry Topology

universe u

namespace ComplexAnalytic.AnalyticSpace

/-- **A morphism of complex analytic spaces is finite when its underlying map is closed and has
finite fibres.**

Both fields are conditions on `f.toLRSHom.base` and neither mentions the structure sheaves; the
content of finiteness for the sheaves is Grauert's finite mapping theorem, which is a theorem
about this definition and is not in this repository.

The underlying map is spelled `f.toLRSHom.base` rather than `f.base`, as everywhere else here:
`ComplexAnalytic.AnalyticSpace.Hom` is a `AlgebraicGeometry.LocallyRingedSpace.Hom` together with
a `ℂ`-linearity condition, and its category structure is defined through `toLRSHom`. -/
@[mk_iff]
class IsFinite {X Y : AnalyticSpace.{u}} (f : X ⟶ Y) : Prop where
  /-- The underlying map is closed. -/
  isClosedMap : IsClosedMap f.toLRSHom.base
  /-- Every fibre is finite. -/
  finite_fiber (y : Y) : Finite (f.toLRSHom.base ⁻¹' {y})

/-- **The identity is finite.** -/
instance isFinite_id (X : AnalyticSpace.{u}) : IsFinite (𝟙 X) where
  isClosedMap := by
    have h : ((𝟙 X : X ⟶ X).toLRSHom.base : X → X) = id := rfl
    rw [h]
    exact IsClosedMap.id
  finite_fiber y := by
    have h : ((𝟙 X : X ⟶ X).toLRSHom.base : X → X) = id := rfl
    rw [h, Set.preimage_id]
    infer_instance

/-- **A composite of finite morphisms is finite.**

The closed half is `IsClosedMap.comp`. The fibre half is `Set.Finite.preimage'` — *a set with
finite fibres has finite preimage over a finite set* — applied to the fibre of the second map;
`Set.Finite.preimage` is the wrong lemma here, since it asks for injectivity, which a finite
morphism does not have. -/
instance isFinite_comp {X Y Z : AnalyticSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsFinite f] [IsFinite g] : IsFinite (f ≫ g) where
  isClosedMap := by
    have h : ((f ≫ g).toLRSHom.base : X → Z) = (g.toLRSHom.base : Y → Z) ∘ f.toLRSHom.base := rfl
    rw [h]
    exact (IsFinite.isClosedMap (f := g)).comp (IsFinite.isClosedMap (f := f))
  finite_fiber z := by
    have h : ((f ≫ g).toLRSHom.base : X → Z) = (g.toLRSHom.base : Y → Z) ∘ f.toLRSHom.base := rfl
    rw [h, Set.preimage_comp]
    haveI : Finite ((g.toLRSHom.base : Y → Z) ⁻¹' {z}) := IsFinite.finite_fiber z
    refine (Set.Finite.preimage' (Set.toFinite _) fun y _ ↦ ?_).to_subtype
    haveI : Finite ((f.toLRSHom.base : X → Y) ⁻¹' {y}) := IsFinite.finite_fiber y
    exact Set.toFinite _

/-- **A closed embedding is finite**: it is closed, and injective, so its fibres are subsingletons.

This is the source of every finite morphism below. Note that only the *topological* half of a
closed immersion is used — nothing is asked of the map on structure sheaves. -/
theorem isFinite_of_isClosedEmbedding {X Y : AnalyticSpace.{u}} (f : X ⟶ Y)
    (h : IsClosedEmbedding (f.toLRSHom.base : X → Y)) : IsFinite f where
  isClosedMap := h.isClosedMap
  finite_fiber y :=
    Set.Finite.to_subtype (Set.Finite.preimage h.injective.injOn (Set.finite_singleton y))

/-- **An isomorphism is finite**, being a homeomorphism and hence a closed embedding. -/
theorem isFinite_of_isIso {X Y : AnalyticSpace.{u}} (f : X ⟶ Y) [IsIso f] : IsFinite f :=
  isFinite_of_isClosedEmbedding f
    (LocallyRingedSpace.homeoOfIso
      (forgetToLocallyRingedSpace.{u}.mapIso (asIso f))).isClosedEmbedding

/-- **A morphism cutting its source out of its target by global sections is finite.**

`ComplexAnalytic.IsCutOutBy` carries `isClosedEmbedding` as a field, so this is that field read
through `ComplexAnalytic.AnalyticSpace.isFinite_of_isClosedEmbedding`. It is the statement that
makes the class non-vacuous in general rather than at one example: every closed analytic subspace
this development cuts out — every local model, in particular — is finite over its ambient space.

Like `ComplexAnalytic.AnalyticSpace.mono_of_isCutOutBy`, this takes the cut-out data as a
hypothesis about `f.toLRSHom` rather than producing it, because most analytic-level morphisms
carrying such data are built by the caller; see `OkaTest/FiniteMorphism.lean` for a closed
embedding exhibited directly instead. **One class of them is not**: an analytification carries
its own datum, `ComplexAnalytic.isCutOutBy_analytificationInclHom`, and a caller holding one of
those has this theorem for free. -/
theorem isFinite_of_isCutOutBy {X Y : AnalyticSpace.{u}} (f : X ⟶ Y) {k : ℕ}
    {s : Fin k → Y.presheaf.obj (op ⊤)} (h : IsCutOutBy f.toLRSHom s) : IsFinite f :=
  isFinite_of_isClosedEmbedding f h.isClosedEmbedding

/-- **A closed embedding followed by a map that is closed and has finite fibres over the image of
that embedding is finite.**

This is the shape every finite morphism onto a *non-closed* image in this development has, and
`ComplexAnalytic.AnalyticSpace.isFinite_comp` does not cover it: there `p` itself has to be
finite, and the projection `ℂ^(n+1) ⟶ ℂ^n` is not — `ComplexAnalytic.not_isFinite_proj` in
`OkaTest/FiniteMorphism.lean` is that non-example. What is asked here instead is that `p` be
closed and finite-fibred **only along `Set.range i.base`**, which for a hypersurface is a
statement about the roots of one family of polynomials and is exactly what
`Polynomial.isClosed_fst_image_of_monic` and `Polynomial.finite_inter_fst_preimage_of_monic`
supply. `Oka/AnalyticSpace/MonicProjection.lean` is the consumer.

Both hypotheses are stated for **sets** rather than for the restriction of `p` to a subtype. The
closedness one is then literally what `IsClosedMap` gives after the embedding has been applied,
so no subtype topology has to be reconciled with anything, and the fibre one is a `Set.Finite`
rather than a `Finite` instance for the same reason.

Nothing is asked of `i` beyond its underlying map being a closed embedding; in particular this
does not go through `ComplexAnalytic.IsCutOutBy`, which is how it applies to a morphism built by
hand. -/
theorem isFinite_comp_of_isClosedEmbedding {X Y S : AnalyticSpace.{u}} (i : X ⟶ Y) (p : Y ⟶ S)
    (hi : IsClosedEmbedding (i.toLRSHom.base : X → Y))
    (hclosed : ∀ t : Set Y, IsClosed t → t ⊆ Set.range (i.toLRSHom.base : X → Y) →
      IsClosed ((p.toLRSHom.base : Y → S) '' t))
    (hfin : ∀ s : S, (Set.range (i.toLRSHom.base : X → Y) ∩
      (p.toLRSHom.base : Y → S) ⁻¹' {s}).Finite) :
    IsFinite (i ≫ p) where
  isClosedMap t ht := by
    have h : ((i ≫ p).toLRSHom.base : X → S) '' t =
        (p.toLRSHom.base : Y → S) '' ((i.toLRSHom.base : X → Y) '' t) := by
      rw [Set.image_image]
      rfl
    rw [h]
    exact hclosed _ (hi.isClosedMap t ht) (Set.image_subset_range _ _)
  finite_fiber s := by
    refine Set.Finite.to_subtype (Set.Finite.of_finite_image (f := (i.toLRSHom.base : X → Y))
      ?_ hi.injective.injOn)
    refine (hfin s).subset ?_
    rintro _ ⟨x, hx, rfl⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx
    exact ⟨⟨x, rfl⟩, hx⟩

/-- **The fibre half of finiteness cancels, with no hypothesis at all**: if `f ≫ g` has finite
fibres then so does `f`, whatever `g` is.

The fibre of `f` over `y` is contained in the fibre of `f ≫ g` over `g y`, and a subset of a finite
set is finite. **There is no hypothesis on `g` at all** — no `[IsFinite g]`, no injectivity — and
`g` is in the binders only because the composite mentions it.

**This is one of the two halves of a cancellation statement for
`ComplexAnalytic.AnalyticSpace.IsFinite`, and it is the half that needs no hypothesis at all**; the
other is `ComplexAnalytic.AnalyticSpace.isFinite_of_comp_of_t2Space` at the foot of this file,
which asks nothing of `g` either and one separation axiom of `Y`.
It is also the fibre half of
`ComplexAnalytic.AnalyticSpace.isFinite_of_isFinite_comp` below, which is where this containment
used to be written out inline: that lemma's injectivity hypothesis is consumed entirely in its
closed half, and factoring this out is what makes that visible in the statements rather than only
in the prose.

**A `theorem` and not an `instance`**, for the reason
`ComplexAnalytic.AnalyticSpace.isLocalIso_of_comp` gives in `Oka/AnalyticSpace/LocalIso.lean`:
instance search would have to invent `Z` and `g`, which the goal determines in no way. -/
theorem finite_fiber_of_comp {X Y Z : AnalyticSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsFinite (f ≫ g)] (y : Y) : Finite (f.toLRSHom.base ⁻¹' {y}) := by
  have hsub : (f.toLRSHom.base : X → Y) ⁻¹' {y} ⊆
      ((f ≫ g).toLRSHom.base : X → Z) ⁻¹' {(g.toLRSHom.base : Y → Z) y} := by
    intro x hx
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx ⊢
    exact congrArg _ hx
  haveI := IsFinite.finite_fiber (f := f ≫ g) ((g.toLRSHom.base : Y → Z) y)
  exact Finite.Set.subset _ hsub

/-- **Finiteness cancels along an injective second factor**: if `f ≫ i` is finite and the
underlying map of `i` is injective, then `f` is finite.

**Do not read this as a converse of
`ComplexAnalytic.AnalyticSpace.isFinite_comp_of_isClosedEmbedding`**, whose name is one word away
and whose statement is the other direction — that one *builds* a finite composite out of a closed
embedding and a map well behaved along its image, while this one takes a finite composite apart.
Nor of `ComplexAnalytic.AnalyticSpace.isFinite_comp`, which needs both factors finite; here the
second factor need not be finite at all, only injective.

**Injectivity is asked for and nothing more, and the proof below consumes it in exactly one of
the two fields.** The fibre half is free, and it is now a theorem of its own that says so:
`ComplexAnalytic.AnalyticSpace.finite_fiber_of_comp`, directly above, asks nothing at all of the
second factor. Injectivity would upgrade its containment to an equality; staying with the
containment is what keeps the one place the hypothesis is used visible. The closed half is that
place, and it uses the continuity of `i` rather than any closedness of it: for `C` closed,
`f.toLRSHom.base '' C` is the **preimage** under `i.toLRSHom.base` of
`(f ≫ i).toLRSHom.base '' C`, which is closed by hypothesis. So `IsClosedEmbedding` would be the
wrong hypothesis — it asks for closedness that is never consumed — and this file's style is to ask
for no more than is used, as
`ComplexAnalytic.AnalyticSpace.isFinite_of_isClosedEmbedding`'s docstring says of the structure
sheaves.

**Injectivity can be dropped if `Y` is Hausdorff, and the shape any counterexample must have
says why.** Since the fibre half consumes nothing, a `f` that is not finite while `f ≫ i` is must
have finite fibres and a base map that is not closed; so the `i` beside it has to identify a limit
point of some image `f.toLRSHom.base '' C` with a point of that image — which is a point of `Y`
not separated from that image, and is impossible in a Hausdorff space.
`ComplexAnalytic.AnalyticSpace.isFinite_of_comp_of_t2Space` at the foot of this file is that
statement, and the two are incomparable rather than one subsuming the other: this one holds for a
non-Hausdorff `Y` and that one for a non-injective `i`. -/
theorem isFinite_of_isFinite_comp {X Y S : AnalyticSpace.{u}} (f : X ⟶ Y) (i : Y ⟶ S)
    (hi : Function.Injective (i.toLRSHom.base : Y → S)) (h : IsFinite (f ≫ i)) :
    IsFinite f where
  isClosedMap C hC := by
    have himg : (f.toLRSHom.base : X → Y) '' C =
        (i.toLRSHom.base : Y → S) ⁻¹' (((f ≫ i).toLRSHom.base : X → S) '' C) := by
      ext y
      refine ⟨?_, ?_⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x, hx, rfl⟩
      · rintro ⟨x, hx, hxy⟩
        exact ⟨x, hx, hi hxy⟩
    rw [himg]
    exact (h.isClosedMap C hC).preimage i.toLRSHom.base.hom.continuous
  finite_fiber y := haveI := h; finite_fiber_of_comp f i y

/-- **A morphism with an infinite fibre is not finite**, which is how a non-example is exhibited:
the fibre condition is the one that fails for a projection, and it fails for a reason one can
point at a set for. -/
theorem not_isFinite_of_infinite_fiber {X Y : AnalyticSpace.{u}} (f : X ⟶ Y) (y : Y)
    (h : Infinite (f.toLRSHom.base ⁻¹' {y})) : ¬ IsFinite f := fun hf ↦
  (not_finite_iff_infinite.2 h) (hf.finite_fiber y)

/-- **A finite morphism is proper**, in the sense that its underlying map is an `IsProperMap`.

`isProperMap_iff_isClosedMap_and_compact_fibers` asks for three things and the class supplies two
of them directly; the third, continuity, is not a field of
`ComplexAnalytic.AnalyticSpace.IsFinite` and does not need to be, since the underlying map is a
`TopCat` morphism and carries its continuity with it.

**No separation hypothesis is used and none is available.** A finite set is compact in an
arbitrary topological space (`Set.Finite.isCompact`), so compactness of the fibres falls out of
`ComplexAnalytic.AnalyticSpace.IsFinite.finite_fiber` alone. That is not true of the covering-map
statement in `Oka/AnalyticSpace/CoveringMap.lean`, which genuinely needs `[T2Space X]`; the
hypothesis should not be carried over here out of symmetry with it.

**The converse fails**: properness gives compact fibres, not finite ones. See
`ComplexAnalytic.AnalyticSpace.isFinite_iff_isProperMap_base_and_finite_fiber` for the agreement
that does hold, and the module docstring for why the weaker-sounding statement is the honest
one. -/
theorem isProperMap_base_of_isFinite {X Y : AnalyticSpace.{u}} (f : X ⟶ Y) [IsFinite f] :
    IsProperMap (f.toLRSHom.base : X → Y) :=
  isProperMap_iff_isClosedMap_and_compact_fibers.2
    ⟨f.toLRSHom.base.hom.continuous, IsFinite.isClosedMap,
      fun y ↦ have := IsFinite.finite_fiber (f := f) y; (Set.toFinite _).isCompact⟩

/-- **A morphism is finite exactly when its underlying map is proper and has finite fibres.**

This is the agreement the module docstring is careful about: finiteness of the fibres appears on
*both* sides, because properness does not imply it. With it assumed, the whole content is that a
proper map is closed (`IsProperMap.isClosedMap`) and that a closed map with finite — hence
compact — fibres is proper.

`ComplexAnalytic.AnalyticSpace.isFinite_iff`, generated by `@[mk_iff]` on the class, is the
same statement with `IsClosedMap` in place of `IsProperMap`. -/
theorem isFinite_iff_isProperMap_base_and_finite_fiber {X Y : AnalyticSpace.{u}} (f : X ⟶ Y) :
    IsFinite f ↔ IsProperMap (f.toLRSHom.base : X → Y) ∧
      ∀ y : Y, Finite (f.toLRSHom.base ⁻¹' {y}) :=
  ⟨fun _ ↦ ⟨isProperMap_base_of_isFinite f, fun y ↦ IsFinite.finite_fiber y⟩,
    fun h ↦ ⟨h.1.isClosedMap, h.2⟩⟩

/-- **Finiteness cancels along a second factor whose source is Hausdorff**: if `f ≫ g` is finite
and `Y` is Hausdorff, then `f` is finite. **Nothing is asked of `g`** — not finiteness, not
closedness, not injectivity, not that it be a local isomorphism — exactly as in
`ComplexAnalytic.AnalyticSpace.finite_fiber_of_comp`, of which this is the other half.

Both fields are one lemma. The fibre half *is* `finite_fiber_of_comp`. The closed half is
`isProperMap_of_comp_of_t2` — Mathlib's cancellation for proper maps, whose `[T2Space]` is on the
**middle** space, which is `Y` here — applied to
`ComplexAnalytic.AnalyticSpace.isProperMap_base_of_isFinite`, and then `IsProperMap.isClosedMap`.
The `rfl` identifying the underlying map of `f ≫ g` with the composite of the two underlying maps
is the one `ComplexAnalytic.AnalyticSpace.isFinite_comp` uses; it is stated rather than left to
unification because the `▸` below needs it in that direction.

**`[T2Space Y]` is a hypothesis and not an instance that will be found *at an arbitrary middle
space*.** `Oka/AnalyticSpace/Basic.lean` imposes no separation axiom on an analytic space, for the
reason `AlgebraicGeometry.Scheme` does not, so with `Y` a variable there is nothing to synthesise.
A caller whose middle space is one this development *constructs* is in a different position:
`Oka/AnalyticSpace/Hausdorff.lean` makes every zero locus inside an open subset of `ℂ^n`, and
every open subspace of a Hausdorff analytic space, carry the instance. **This paragraph used to
say that the only `T2Space` instance for an analytic space in this repository was
`ComplexAnalytic.t2Space_restrict_punctured`, about a single restriction of a single space**; that
was exact until that file was written and both halves of it are now false. And the hypothesis
cannot be dropped: `TwoIndiscrete.not_isClosedMap_pt_of_isClosedMap_comp`
(`OkaTest/FiniteEtaleCancel.lean`) is a compiled witness with a two-point indiscrete middle space,
whose second factor is closed with finite fibres — so no strengthening of `g` short of one that
forces `Y` to be Hausdorff can replace it.

**It is on the *middle* space and not on the source or the target**, which is where the module
docstring's counterexamples put the failure and is the position `isProperMap_of_comp_of_t2` asks
for. `X` and `Z` are unconstrained.

**A `theorem` and not an `instance`**, for the reason
`ComplexAnalytic.AnalyticSpace.finite_fiber_of_comp` gives: instance search would have to invent
`Z` and `g`, which the goal determines in no way.

Placed here rather than beside `ComplexAnalytic.AnalyticSpace.finite_fiber_of_comp`, where it
belongs thematically, only because it consumes
`ComplexAnalytic.AnalyticSpace.isProperMap_base_of_isFinite` and that is declared above. -/
theorem isFinite_of_comp_of_t2Space {X Y Z : AnalyticSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [T2Space Y] [IsFinite (f ≫ g)] : IsFinite f where
  isClosedMap := by
    have h : ((f ≫ g).toLRSHom.base : X → Z) = (g.toLRSHom.base : Y → Z) ∘ f.toLRSHom.base := rfl
    exact (isProperMap_of_comp_of_t2 f.toLRSHom.base.hom.continuous
      g.toLRSHom.base.hom.continuous (h ▸ isProperMap_base_of_isFinite (f ≫ g))).isClosedMap
  finite_fiber y := finite_fiber_of_comp f g y

end ComplexAnalytic.AnalyticSpace
