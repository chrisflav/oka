/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Mathlib.Topology.Covering.Basic

/-!
# Covering maps: a criterion and its converse, a cancellation, constant fibres, and a base change

Material for `Mathlib/Topology/Covering/Basic.lean`; see `README.md` on the mirror tree. The
statements below are independent of one another, sharing only their destination.

**Until 2026-09-07 the heading above read *Four statements about covering maps: two criteria, a
cancellation, and constancy of the fibre*, and the sentence beside it read *Four independent
statements, sharing only their destination*.** The section appended below moves whichever set
those two numerals were of, so they are replaced by the enumeration rather than raised by one: a
count of a file's own contents goes false on the next append and an enumeration does not.

## A closed local homeomorphism with finite fibres is a covering map

Mathlib proves this for `IsCoveringMapOn` — `IsClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn`,
which takes a set `s`, finiteness of the fibres over `s`, and a local homeomorphism on `f ⁻¹' s`.
The statement below is that theorem at `s = Set.univ`, packaged as `IsCoveringMap`; Mathlib has
the relative form and not this one. The companion global statement it does have,
`isLocalHomeomorph_iff_isCoveringMap`, assumes the source **compact** instead of the map closed,
and is therefore not applicable to a non-compact source such as the punctured line.

The Hausdorff hypothesis on the source is Mathlib's and is used to separate the finitely many
points of a fibre; it is not removable, and
`LineTwoOrigins.not_isCoveringMap_fold_of_not_t2Space` (`OkaTest/FiniteEtaleCancel.lean`) is a
compiled witness that it is not. It is the line with two origins folded onto `ℝ`: a closed local
homeomorphism with finite fibres onto a Hausdorff space, which is every hypothesis of
`IsClosedMap.isCoveringMap_of_isLocalHomeomorph` except the separation axiom, and not a covering
map. The route to that last conjunct is `IsCoveringMap.isSeparatedMap`, which is Mathlib's, and
`IsSeparatedMap.t2Space` in `Oka/Topology/SeparatedMap.lean`, which is not.

**That clause ended at *it is not removable* until 2026-09-07**, asserting the non-removability
and citing nothing — where the paragraph on `IsCoveringMap.pullback_snd` cites
`TwoIndiscrete.not_isCoveringMap_pullback_snd` for its own hypothesis, and has since `24e9179`,
the push that added both. **The assertion was true and this
repair adds the citation rather than changing the claim**; the clause is retired as a dated
record because the sentence around it is rewritten, not because it was wrong.

The same non-removability is asserted a second time, in
`## A covering map with finite fibres is a closed map`, and **that clause is deliberately
left as it stands**: its subject is *the criterion above*, so it reaches the witness by naming the
statement this paragraph is about, and a citation copied to a second site is a second thing to
keep true.

## A covering map with finite fibres is a closed map

The converse of the criterion above, and the direction Mathlib does not have. **At `v4.32.0` — the
revision `lakefile.toml` pins, resolved by `lake-manifest.json` to
`81a5d257c8e410db227a6665ed08f64fea08e997` — no declaration of Mathlib concludes `IsClosedMap`
from `IsCoveringMap`**, and the population that has to be read to say so is small enough to name:
such a declaration has to write `IsCoveringMap` in its statement, so `grep -rl IsCoveringMap
Mathlib/` is the whole of it and it returns **seven** files. In those seven the only statements
naming `IsClosedMap` are `IsClosedMap.isEvenlyCovered_of_openPartialHomeomorph`
(`Mathlib/Topology/Covering/Basic.lean:509`), `IsClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn`
(`:558`) and the `alias` beside it (`:568`) — **all three with `IsClosedMap` as a hypothesis**,
which is the criterion above and not this. **The predicate is what that clause quantifies over and
not the word *closed***: `IsCoveringMap.mk'` (`:322`) asks `IsClosed (Set.range f)`, which is
closedness of a set rather than of a map, and it concludes `IsCoveringMap` rather than starting
from one, so it is neither a counterexample nor a member of the three.

**Until 2026-09-20 that clause read *the direction Mathlib does not have in any form: across
`Mathlib/Topology/Covering/`, `isClosedMap` occurs only inside proofs*, and the scan in it could
not decide what it was offered for.** The exact token `isClosedMap` does occur only inside a proof
in that directory — once, at `Mathlib/Topology/Covering/Basic.lean:578` — so the clause was true of
the spelling it wrote; `IsClosedMap`, which is the predicate it meant, stands in the *statements* of
the two theorems named above and in the `alias`. A capital letter is the whole of the difference,
and the headline is true for a reason the scan never touched. **The claim is unchanged and only its
warrant is**, which is why the retired wording is kept here rather than struck;
`OkaTest/Axioms.lean`'s seventh census object is the rule and taxis #2108 is the filing.

`IsCoveringMap.isClosedMap` below is what makes a finite covering space *finite* in the sense a
morphism of complex analytic spaces is asked to be: it supplies the closed base map that
`ComplexAnalytic.AnalyticSpace.IsFinite` asks for and that finite fibres do not give.

**That half is what it is the only input for, and not the construction.**
`Oka/AnalyticSpace/CoveringSpace.lean` takes its cover from `IsLocalHomeomorph.sSup_sheetOpens` in
`Oka/Topology/IsLocalHomeomorph.lean`, which Mathlib also does not have, and more of this mirror
tree reaches it through the inverse image sheaf — `TopCat.Presheaf.stalkPushforward_naturality` in
`Oka/Topology/Sheaves/Stalks.lean` is used to prove the stalk isomorphism that construction's local
isomorphism rests on. No number is given here because it is not one this file could keep true.

The proof reads the evenly covered neighbourhood as what the definition literally is — an open
`U ∋ x`, and a homeomorphism `H : f ⁻¹' U ≃ₜ U × I` over `U` — and pushes the closed set across
it. Given `C` closed and `x ∉ f '' C`, the image `H '' C` is closed in `U × I`, and it misses the
slice `{x} × I` because a point of that slice lies over `x`. So each of the finitely many `i : I`
gives an open set of `U` around `x` avoiding the `i`-th sheet of `C`, and their intersection is
the neighbourhood wanted.

**Finiteness of the fibre is used once, for that intersection to be open**, and it is used at the
index type `I = f ⁻¹' {x}`, which is why the hypothesis is about fibres and not about `E`. **No
separation axiom is used at all** — unlike the criterion above, whose `T2Space E` is Mathlib's and
is not removable. And **the empty fibre is not a special case**: the intersection over an empty
index type is `U` itself, which is the right answer, since `f ⁻¹' U` is then empty and `U` misses
`f '' C` outright.

## Closedness cancels along a covering map, with no separation axiom

`IsCoveringMap.isClosedMap_of_comp`: if `f` is a covering map and `f ∘ u` is closed then `u` is
closed, for a `u` asked only to be continuous. **What Mathlib transports along a composite at
`v4.32.0` is a homeomorphism and nothing weaker; what it cancels a covering map out of is an
equality of composites, and the conclusion there is uniqueness of the companion and not a property
of it.** The instrument is a namespace and a count, and **both halves of it are printed, because a
figure whose counting rule is unstated is not reproducible**. The namespace is cut with
`sed -n '/^namespace IsCoveringMap$/,/^end IsCoveringMap$/p'` over
`Mathlib/Topology/Covering/Basic.lean`, and the count is

`grep -cE '^(@\[[^]]*\] *)?(private |protected |noncomputable )*(theorem|lemma|def|alias)'`

whose alternation is the declaration keywords that file uses and whose modifiers are the ones it
writes before them. **Both optional branches of it are load-bearing, and which one carries the
figure differs by namespace**, which is why the pattern is printed whole rather than simplified.
Over the three namespaces this docstring counts it gives **18 / 12 / 18** at `IsEvenlyCovered`
(`:44–193`), `IsCoveringMapOn` (`:200–283`) and `IsCoveringMap` (`:308–408`); dropping the
attribute branch gives **16 / 10 / 18**, and dropping the modifiers with it gives **12 / 7 / 14**.
So what a count anchored on `^theorem` loses first is the one-line `@[simp] theorem`, of which that
file carries exactly four — **two in `IsEvenlyCovered` (`:176`, `:188`), two in `IsCoveringMapOn`
(`:269`, `:278`), and none at all in `IsCoveringMap`**, where the eighteen below is unchanged by
dropping that branch and it is the `protected ` modifier that buys the four instead
(`IsCoveringMap.continuous` at `:336`, `IsCoveringMap.isLocalHomeomorph` at `:339`,
`IsCoveringMap.isOpenMap` at `:342` and `IsCoveringMap.isSeparatedMap` at `:348`).

Of those **eighteen** in `namespace IsCoveringMap`, **eight** write a composite, and they are two
different things:

* **Four conclude `IsCoveringMap` of a composite, and every one of the four is at a
  homeomorphism.** `IsCoveringMap.comp_homeomorph` (`:388`) and `IsCoveringMap.homeomorph_comp`
  (`:392`) build one, and `IsCoveringMap.comp_homeomorph_iff` (`:398`) and
  `IsCoveringMap.homeomorph_comp_iff` (`:403`) are their two-way forms, whose forward directions
  cancel one. **This is the half the headline above is about.**
* **Four cancel `f` itself out of an equality of composites**, at companions asked only to be
  continuous over a preconnected source: `IsCoveringMap.eq_of_comp_eq` (`:367`),
  `IsCoveringMap.const_of_comp` (`:371`), `IsCoveringMap.eqOn_of_comp_eqOn` (`:375`) and
  `IsCoveringMap.constOn_of_comp` (`:379`). **These are lifting-uniqueness statements**: what they
  conclude is that two companions agree, not that a companion inherits a property of the composite,
  and two of the four spell the composite by application (`f (g a)`) rather than with `∘`, which is
  itself the *can it be spelled another way?* question `OkaTest/Axioms.lean`'s seventh census object
  asks of a scan.

**Neither half is the statement below**, which carries a property of `f ∘ u` — closedness — back to
`u`, and no declaration of that namespace carries any property of a composite back to a factor.
The same instrument at `namespace IsCoveringMapOn` (`:200–283`) gives **twelve**: the same two
builders, and two `_iff` lemmas as well, `IsCoveringMapOn.comp_homeomorph_iff` (`:269`) and
`IsCoveringMapOn.homeomorph_comp_iff` (`:278`), both `@[simp] theorem …` on one line.

**Until 2026-09-20 this read *Mathlib has no cancellation lemma for `IsCoveringMap` at all —
`comp_homeomorph` and `homeomorph_comp` conjugate by a homeomorphism, and there is no composition
lemma either*, and it was false at that same `v4.32.0`.** `IsCoveringMap.comp_homeomorph_iff` is
`IsCoveringMap (f ∘ g) ↔ IsCoveringMap f` at a homeomorphism `g`, which is a cancellation lemma for
`IsCoveringMap`; the enumeration offered in support named the two lemmas without the `_iff` and not
the two with it, which stand ten and eleven lines below them in the same namespace. **What the
statement below is, and what the retired clause was reaching for, is the cancellation of a
*property* along a `u` asked only to be continuous** — not the cancellation of `f` out of an
equality, which the four `_of_comp` lemmas above do — and that is what the count says Mathlib does
not have.

The classical statement of this shape asks the second map to be **separated** and factors the
first through its graph in a fibre product. Neither is used below. A covering map instead
decomposes `f ⁻¹' U` over an evenly covered `U` into open sheets, and **`f` is injective on each
one**; that injectivity is the whole content, and the rest of the proof is that a sheet is open
with open complement in `f ⁻¹' U`, so that a closed set of the source stays closed after being cut
down to one sheet.

**What earns this its place is the separation axiom it does not ask for, and it is worth being
exact about what that is worth.** Mathlib's three cancellations for proper maps are in
`Mathlib/Topology/Maps/Proper/Basic.lean` and none of them applies: two ask the composite's second
factor to be injective or its first to be surjective, and the third, `isProperMap_of_comp_of_t2`,
asks the **middle space to be Hausdorff**. Where a Hausdorff middle space is available that third
one is both shorter and more general than this — it asks nothing whatever of the second map —
and it is what `Oka/AnalyticSpace/Finite.lean` uses for the analytic statement of this shape.
`IsCoveringMap.isClosedMap_of_comp` is what is left when no separation axiom is available at all,
and **at `v4.32.0` `IsSeparatedMap` does not reach that case either**, which is worth saying
because a covering map satisfies it (`IsCoveringMap.isSeparatedMap`) and so it is the first place
to look. `grep -rl IsSeparatedMap Mathlib/` returns **three** files, and the other two consume the
predicate rather than adding to it — `Mathlib/Topology/Homotopy/Lifting.lean` binds it on one
`variable` line and `Mathlib/Topology/Covering/Basic.lean` declares `IsCoveringMap.isSeparatedMap`
and nothing else about it. That leaves `Mathlib/Topology/SeparatedMap.lean`, whose **seventeen**
declarations about the predicate are the definition, six characterisations,
`T2Space.isSeparatedMap`, `Function.Injective.isSeparatedMap`, `IsSeparatedMap.pullback`,
`IsSeparatedMap.comp_left`, `IsSeparatedMap.comp_right`, `IsSeparatedMap.isClosed_eqLocus` and
the four lifting-uniqueness
statements in its own namespace. **`comp_left` and `comp_right` conclude `IsSeparatedMap` of a
composite rather than cancelling anything, and none of the seventeen concludes that a factor of a
closed composite is closed**, which is the statement below.

**Until 2026-09-20 the second half of that sentence read *and Mathlib has nothing there, not even
at `IsSeparatedMap`, which a covering map satisfies*.** It was true and it was bare: a universal
over a library this repository does not commit to, with no instrument and no version beside it, of
the class `OkaTest/Axioms.lean`'s seventh census object is the rule for. The enumeration replacing
it is the same claim bounded to what can be read, and the neighbouring sentence about proper maps —
three cancellations, in one named file — is the form it is copied from.

**Nothing in this repository consumes it**, and that is said rather than left to be discovered: it
is mirror-tree material stated for its own sake, in a file whose other statements about closedness
and covering maps are its natural neighbours.

## The fibres of a covering map over a preconnected base

`IsCoveringMap.nonempty_homeomorph_fiber`: over a preconnected base any two fibres of a covering
map are homeomorphic. This is what connectedness of the base buys — the *number of sheets* — and
it is the statement that a covering map itself does not give: `IsCoveringMap` says every point has
an evenly covered neighbourhood, with the fibre over that point as the index type, and says
nothing at all relating the index types at two different points.

The argument is the usual clopen one and the whole of its content is **local constancy**, which in
turn rests on one observation. **At `v4.32.0` the whole of `IsEvenlyCovered`'s Mathlib API is one
file and twenty declarations, and none of them has, for the same `f`, an `IsEvenlyCovered`
hypothesis at one point and an `IsEvenlyCovered` conclusion at another**: `grep -rl IsEvenlyCovered
Mathlib/` returns `Mathlib/Topology/Covering/Basic.lean` alone, whose `IsEvenlyCovered` namespace
(`:44–193`) holds **eighteen** by the count printed in
`## Closedness cancels along a covering map, with no separation axiom` above, with
`IsClosedMap.isEvenlyCovered_of_openPartialHomeomorph` (`:509`) and
`IsEvenlyCovered.of_openPartialHomeomorph` (`:574`) declared outside it — twenty-one if the
definition (`:40`) is counted, which this sentence does not. That list fits on a screen and reading
it is the instrument; a grep for a *word* would not have been one, since what is being denied here
is a shape and not a spelling.

**The *same `f`* is what the claim rests on and it is not a hedge.** Two of the eighteen do move
the point: `IsEvenlyCovered.homeomorph_comp` (`:181`) takes a hypothesis at `x` to a conclusion at
`g x`, and `IsEvenlyCovered.homeomorph_comp_iff` (`:188`) is its two-way form. **Both move the map
with it**, from `f` to `g ∘ f` at a homeomorphism `g` of the base, so the point they conclude at is
the same point transported and not a second point of one base. The statement below holds `f` fixed
and moves `y` inside `𝓝 x`, and nothing in those twenty does that.

**Until 2026-09-20 that sentence ended *which in turn rests on one observation Mathlib does not
state*, with nothing beside it.** It was true and it was bare — a universal over a library this
repository does not commit to, with no version and no instrument, of the class
`OkaTest/Axioms.lean`'s seventh census object is the rule for — and the enumeration above is the
same claim bounded to what can be read.

**`IsEvenlyCovered f x I` mentions `x` only through `x ∈ U`.** Unfolded it is a `U`, its openness,
the openness of `f ⁻¹' U`, a homeomorphism `f ⁻¹' U ≃ₜ U × I` and a compatibility, and none of the
last four depends on `x`. So the *same witness* serves every point of `U`, which is
`IsEvenlyCovered.eventually`. Everything below is that fact plus `IsEvenlyCovered.fiberHomeomorph`,
which is Mathlib's.

Two details of the clopen step are worth stating because each cost a failed attempt:

* **both** halves are the same local-constancy fact. `Sᶜ` is open because `Nonempty (· ≃ₜ ·)` is
  symmetric and transitive, not by a second argument;
* `IsClosed S` is the structure constructor applied to openness of the complement,
  `⟨hclosed⟩`. `isClosed_compl_iff` is about `IsClosed Sᶜ` and is the wrong lemma here.

**`PreconnectedSpace`, not `ConnectedSpace`.** Nonemptiness of the base plays no part, and asking
for it would make the statement fail on the empty space for no reason.

## A covering map stays one under base change along a continuous map

`Function.Pullback f g` is Mathlib's set-theoretic fibre product (`Mathlib/Data/Set/Prod.lean`), a
subtype of `E × Y`, so it carries the subspace topology of the product and
`IsCoveringMap.pullback_snd` constructs no type and no instance: it is a statement about
`Function.Pullback.snd` at the topology that is already there.

Being evenly covered is a condition on the base and the witness transports unchanged. Over an open
`U ∋ g y` with `H : f ⁻¹' U ≃ₜ U × I`, the set `g ⁻¹' U` is an open neighbourhood of `y`, and the
part of the pullback lying over it goes to `(g ⁻¹' U) × I` by `(e, y') ↦ (y', (H e).2)`. **The index
type is the same `I`**, which is what leaves the fibre of the base change one application of
`IsEvenlyCovered.to_isEvenlyCovered_preimage` away and what makes the companion statement about
fibres independent of the trivialisation.

**`Continuous g` is a hypothesis of `IsCoveringMap.pullback_snd` and it cannot be dropped.** The
underlying map of sets needs nothing — that is why `Function.Pullback.finite_fiber_snd` below asks
for no topology at all — but `g ⁻¹' U` being open is what makes the trivialisation above a
trivialisation, and the conclusion is false without it:
`TwoIndiscrete.not_isCoveringMap_pullback_snd` (`OkaTest/CoveringBaseChange.lean`) compiles a
witness, at the identity of a two-element discrete space base-changed along the identity out of the
same two points carrying the indiscrete topology, where `Function.Pullback.snd` is a continuous
bijection and not an open map.

`Function.Pullback.finite_fiber_snd` is the fibre half and carries neither a covering hypothesis
nor a topology: `Function.Pullback.fst` is injective on the fibre of `Function.Pullback.snd` over
`y` and lands it inside `f ⁻¹' {g y}`. It is stated apart from `IsCoveringMap.pullback_snd` rather
than conjoined with it because `ComplexAnalytic.AnalyticSpace.isFinite_coveringSpaceHom`
(`Oka/AnalyticSpace/CoveringSpace.lean`) asks for a covering map and for finite fibres as two
hypotheses.

**Both are statements about continuous maps of topological spaces, and the word *topological* is
doing work in that sentence.** The `ComplexAnalytic.AnalyticSpace.isFinite_coveringSpaceHom` just
cited reads a covering map of underlying spaces as a finiteness statement about a morphism of
complex analytic spaces, and neither statement below is composed with it in this file. Both are
guarded in `OkaTest/Axioms/Morphisms.lean` rather than beside a consumer, which is where
`IsCoveringMap.isClosedMap_of_comp` is guarded and for the reason that section gives; what consumes
`Function.Pullback.finite_fiber_snd` at the commit that adds it is
`TwoIndiscrete.not_isCoveringMap_pullback_snd_of_not_continuous`, a declaration of a test file,
which the guards of this repository's library do not reach.

## Main results

- `IsClosedMap.isCoveringMap_of_isLocalHomeomorph`: a closed local homeomorphism with finite
  fibres out of a Hausdorff space is a covering map.
- `IsCoveringMap.isClosedMap`: **a covering map with finite fibres is closed**, which is the
  converse of the previous item with the Hausdorff hypothesis dropped.
- `IsCoveringMap.isClosedMap_of_comp`: **closedness cancels along a covering map** — if `f` is a
  covering map and `f ∘ u` is closed then so is `u`, with no hypothesis on `u` beyond continuity
  and no separation axiom anywhere.
- `IsEvenlyCovered.eventually`: an evenly covered point is evenly covered on a neighbourhood, with
  the same index type.
- `IsCoveringMap.eventually_nonempty_homeomorph`: the fibres of a covering map are locally
  constant up to homeomorphism.
- `IsCoveringMap.nonempty_homeomorph_fiber`: **over a preconnected base, any two fibres of a
  covering map are homeomorphic.**
- `IsCoveringMap.pullback_snd`: **a covering map stays a covering map under base change along a
  continuous map**, at Mathlib's `Function.Pullback`.
- `Function.Pullback.finite_fiber_snd`: the fibres of `Function.Pullback.snd` are finite when the
  fibres of the map being base-changed are, with no covering hypothesis and no topology.
-/

open Topology

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {f : E → X}
  {I : Type*} [TopologicalSpace I]

/-- **A closed local homeomorphism with finite fibres out of a Hausdorff space is a covering
map.**

This is `IsClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn` at `Set.univ`. No connectedness of
the target is needed: a point outside the range is evenly covered by the empty index type, which
is how that proof treats it.

**`[T2Space E]` cannot be dropped**, and the witness is
`LineTwoOrigins.not_isCoveringMap_fold_of_not_t2Space` (`OkaTest/FiniteEtaleCancel.lean`): the
line with two origins folded onto `ℝ` is closed, has finite fibres and is a local homeomorphism —
`hf`, `hfin` and `h` here — onto a Hausdorff target, and is not a covering map. **The separation
axiom is on the *source* and there is none on the target beyond what the witness happens to
have** — `ℝ` is Hausdorff there because
that is the space the witness is built over, not because this statement asks it. -/
theorem IsClosedMap.isCoveringMap_of_isLocalHomeomorph [T2Space E] (hf : IsClosedMap f)
    (hfin : ∀ x, (f ⁻¹' {x}).Finite) (h : IsLocalHomeomorph f) : IsCoveringMap f := by
  rw [isCoveringMap_iff_isCoveringMapOn_univ]
  exact hf.isCoveringMapOn_of_isLocalHomeomorphOn (fun x _ ↦ hfin x)
    ((isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mp h).mono (Set.subset_univ _))

/-- **A covering map with finite fibres is a closed map.**

The converse of `IsClosedMap.isCoveringMap_of_isLocalHomeomorph`, with the Hausdorff hypothesis
dropped: nothing below separates two points of a fibre, it only counts them.

Given a closed `C` and a point `x` outside `f '' C`, the evenly covered neighbourhood of `x` is an
open `U` and a homeomorphism `H : f ⁻¹' U ≃ₜ U × (f ⁻¹' {x})` over `U`. The image of `C` under `H`
is closed, and misses every point of the slice over `x`, because such a point is a preimage of `x`
and `x ∉ f '' C`. Intersecting the finitely many slices of the complement gives the neighbourhood.

**Finiteness of the fibre is used exactly once**, for that intersection to be open; the empty
fibre is not a special case, since the empty intersection is `U`, which is then disjoint from
`f '' C` because `f ⁻¹' U` is empty. -/
theorem IsCoveringMap.isClosedMap (hf : IsCoveringMap f) (hfin : ∀ x, (f ⁻¹' {x}).Finite) :
    IsClosedMap f := by
  intro C hC
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨_, U, hxU, hU, hfU, H, hH⟩ := hf x
  have : Finite (f ⁻¹' {x}) := (hfin x).to_subtype
  -- The image of `C` in the trivialisation, a closed subset of `U × (f ⁻¹' {x})`.
  set D : Set (U × (f ⁻¹' {x})) := H '' (Subtype.val ⁻¹' C) with hD
  have hDclosed : IsClosed D := H.isClosedMap _ (hC.preimage continuous_subtype_val)
  -- The points of `U` no sheet of which meets `C`.
  set W : Set U := ⋂ i : (f ⁻¹' {x}), (fun u ↦ (u, i)) ⁻¹' Dᶜ with hW
  have hWopen : IsOpen W :=
    isOpen_iInter_of_finite fun i ↦ hDclosed.isOpen_compl.preimage (by fun_prop)
  have hxW : (⟨x, hxU⟩ : U) ∈ W := by
    refine Set.mem_iInter.2 fun i hmem ↦ ?_
    obtain ⟨e, heC, hey⟩ := hmem
    refine hx ⟨(e : E), heC, ?_⟩
    have := hH e
    rw [hey] at this
    exact this.symm
  refine Filter.mem_of_superset (hU.isOpenMap_subtype_val W hWopen |>.mem_nhds
    ⟨⟨x, hxU⟩, hxW, rfl⟩) ?_
  rintro _ ⟨u, huW, rfl⟩ ⟨c, hcC, hfc⟩
  have hcU : c ∈ f ⁻¹' U := by rw [Set.mem_preimage, hfc]; exact u.2
  have hfst : (H ⟨c, hcU⟩).1 = u := Subtype.ext ((hH ⟨c, hcU⟩).trans hfc)
  exact (Set.mem_iInter.1 huW (H ⟨c, hcU⟩).2) ⟨⟨c, hcU⟩, hcC, by rw [← hfst]⟩

/-- **Closedness cancels along a covering map**: if `f` is a covering map and `f ∘ u` is a closed
map, then `u` is closed.

Nothing is asked of `u` beyond continuity — not that it be closed, injective, surjective or a local
homeomorphism — and **no separation axiom is used**, on any of the three spaces.

The classical statement of this shape is *a map whose composite with a separated map is proper is
proper*, proved by factoring `u` through its graph in a fibre product. **Neither ingredient is used
here.** What a covering map supplies instead is a *sheet*: for `y : E` there is an evenly covered
`U ∋ f y` and a decomposition of `f ⁻¹' U` into open pieces on each of which `f` is injective. The
proof is that decomposition and nothing else:

* the sheet `V ∋ y` and the union `V'` of the other sheets are **both open**, because the sheet
  index is `Prod.snd ∘ H` into a discrete type, so `A := C ∩ u ⁻¹' V` is closed *in*
  `u ⁻¹' (f ⁻¹' U)` — which is what `hAcl` says, and is where `V'` is used;
* therefore `closure A` is a closed set on which the hypothesis can be spent, and
  `T := (f ∘ u) '' closure A` is closed;
* `f y ∉ T`: a witness would lie in `A` by the previous point, so its image under `u` lies in `V`
  alongside `y` and has the same image under `f`, and **`f` is injective on `V`** — so it *is* `y`,
  contradicting `y ∉ u '' C`;
* `V ∩ f ⁻¹' Tᶜ` is then an open neighbourhood of `y` missing `u '' C`.

**Injectivity on a sheet is the whole of what the hypothesis buys**, and it is what fails for a
closed local homeomorphism with finite fibres that is not a covering map — the line with two
origins over the line, whose two origins have no disjoint neighbourhoods and hence no sheet
containing exactly one of them. `Oka/AnalyticSpace/Finite.lean` records that example as the reason
this statement is false with `IsCoveringMap f` weakened to *`f` closed with finite fibres*, and
`TwoIndiscrete.not_isClosedMap_pt_of_isClosedMap_comp` (`OkaTest/FiniteEtaleCancel.lean`)
compiles a witness for the weakening — a weaker one, since its second map is not a local
homeomorphism.

**Note what those two witnesses have in common besides failing to be covering maps: their `E` is
not Hausdorff.** That is not an accident, and it means this lemma is *not* the cheapest route to
any statement in which `E` is known to be Hausdorff. There `isProperMap_of_comp_of_t2` applies —
Mathlib's proper-map cancellation, whose separation hypothesis is on `E` and which asks nothing at
all of the first map — and it is both shorter and more general. **This lemma is what remains when
no separation axiom is available at all, and the module docstring is where that case is measured
against Mathlib** — `## Closedness cancels along a covering map, with no separation axiom` counts
the `IsCoveringMap` and `IsSeparatedMap` APIs at `v4.32.0` and names the version, and this
paragraph points at it rather than restating it, a claim about a library nobody here commits to
being worth one site and not two.

**Until 2026-09-20 this ended *which is the case Mathlib does not cover, at `IsCoveringMap` or at
`IsSeparatedMap`; `IsCoveringMap.comp_homeomorph` and `IsCoveringMap.homeomorph_comp` are
conjugation by a homeomorphism and there is no composition lemma either*.** That was the module
docstring's clause said a second time, and it inherited its defect: `IsCoveringMap`'s namespace has
four lemmas concluding `IsCoveringMap` of a composite at that version and not two, the other two
being `IsCoveringMap.comp_homeomorph_iff` and `IsCoveringMap.homeomorph_comp_iff` — and four more
cancelling `f` out of an equality of composites, which conclude that two companions agree and say
nothing about the covering property of a factor. **A claim whose
evidence lives in another paragraph is not bare, but it owes the pointer**, which is what replaces
it here.

**Nothing in this repository consumes this**; see the module docstring. -/
theorem IsCoveringMap.isClosedMap_of_comp {W : Type*} [TopologicalSpace W] {u : W → E}
    (hf : IsCoveringMap f) (hu : Continuous u) (h : IsClosedMap (f ∘ u)) :
    IsClosedMap u := by
  intro C hC
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro y hy
  obtain ⟨inst, U, hyU, hU, hfU, H, hH⟩ := hf (f y)
  have hymem : y ∈ f ⁻¹' U := hyU
  -- The sheet index of a point of `f ⁻¹' U`, a continuous map to a discrete type.
  set p : (f ⁻¹' U) → (f ⁻¹' {f y}) := fun e ↦ (H e).2 with hp
  have hpcont : Continuous p := continuous_snd.comp H.continuous
  set i₀ := p ⟨y, hymem⟩ with hi₀
  -- The sheet through `y`, and the union of all the other sheets.
  set V : Set E := Subtype.val '' (p ⁻¹' {i₀}) with hV
  set V' : Set E := Subtype.val '' (p ⁻¹' {i₀}ᶜ) with hV'
  have hVopen : IsOpen V :=
    hfU.isOpenMap_subtype_val _ (hpcont.isOpen_preimage _ (isOpen_discrete _))
  have hV'open : IsOpen V' :=
    hfU.isOpenMap_subtype_val _ (hpcont.isOpen_preimage _ (isOpen_discrete _))
  have hyV : y ∈ V := ⟨⟨y, hymem⟩, rfl, rfl⟩
  have hcover : ∀ e ∈ f ⁻¹' U, e ∈ V ∨ e ∈ V' := by
    intro e he
    by_cases hcase : p ⟨e, he⟩ = i₀
    · exact Or.inl ⟨⟨e, he⟩, hcase, rfl⟩
    · exact Or.inr ⟨⟨e, he⟩, hcase, rfl⟩
  have hdisj : ∀ e ∈ V, e ∉ V' := by
    rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hba⟩
    exact hb (by rw [show b = a from Subtype.ext hba]; exact ha)
  -- `f` is injective on a single sheet: two points of it have the same index, and equal images
  -- under `f` make their two `H`-components agree.
  have hinj : ∀ a ∈ V, ∀ b ∈ V, f a = f b → a = b := by
    rintro _ ⟨ea, hea, rfl⟩ _ ⟨eb, heb, rfl⟩ hab
    refine congrArg Subtype.val (H.injective (Prod.ext (Subtype.ext ?_) ?_))
    · rw [hH ea, hH eb]; exact hab
    · exact hea.trans heb.symm
  set A : Set W := C ∩ u ⁻¹' V with hA
  -- `A` is closed in `u ⁻¹' (f ⁻¹' U)`, which is what the other sheets being open gives.
  have hAcl : ∀ w ∈ closure A, u w ∈ f ⁻¹' U → w ∈ A := by
    intro w hw hwU
    refine ⟨hC.closure_subset (closure_mono Set.inter_subset_left hw), ?_⟩
    by_contra hnot
    obtain ⟨z, hz1, hz2⟩ :=
      mem_closure_iff.1 hw _ (hV'open.preimage hu) ((hcover _ hwU).resolve_left hnot)
    exact hdisj _ hz2.2 hz1
  set T : Set X := (f ∘ u) '' (closure A) with hT
  have hfyT : f y ∉ T := by
    rintro ⟨w, hw, hwy⟩
    have hwA : w ∈ A :=
      hAcl w hw (by rw [Set.mem_preimage, show f (u w) = f y from hwy]; exact hyU)
    exact hy ⟨w, hwA.1, hinj _ hwA.2 _ hyV hwy⟩
  refine Filter.mem_of_superset
    ((hVopen.inter (((h _ isClosed_closure).isOpen_compl).preimage hf.continuous)).mem_nhds
      ⟨hyV, hfyT⟩) ?_
  rintro y' ⟨hy'V, hy'T⟩ ⟨c, hcC, rfl⟩
  exact hy'T (Set.mem_image_of_mem _ (subset_closure ⟨hcC, hy'V⟩))

/-- **An evenly covered point is evenly covered on a whole neighbourhood, with the same index
type.**

`IsEvenlyCovered f x I` is a `U` containing `x` together with data over `U` — its openness, the
openness of `f ⁻¹' U`, a homeomorphism `f ⁻¹' U ≃ₜ U × I` and its compatibility with `f` — and
**`x` occurs in none of that data except through `x ∈ U`.** So the witness for `x` is verbatim a
witness for every `y ∈ U`, and the proof destructures it and puts it back together.

Note that the index type is the *same* `I`, which is what makes this usable: applied to
`IsCoveringMap f` at `x`, whose index type is `f ⁻¹' {x}`, it says every nearby point has fibre
`f ⁻¹' {x}` — not merely that every nearby point is evenly covered by something.

Its Mathlib destination is beside `IsEvenlyCovered.of_fiber_homeomorph`, and the module docstring's
`## The fibres of a covering map over a preconnected base` is where the absence it fills is
measured — twenty declarations at `v4.32.0`, none of them evenly covered at one point and
concluding it at another **for the same `f`**.

**Until 2026-09-20 this read *Mathlib does not have this; it sits with
`IsEvenlyCovered.of_fiber_homeomorph`*.** It was true and it was bare, and it was the module
docstring's claim said a second time; a claim about a library nobody here commits to is worth one
instrumented site and a pointer, not two assertions. -/
theorem IsEvenlyCovered.eventually {x : X} (h : IsEvenlyCovered f x I) :
    ∀ᶠ y in 𝓝 x, IsEvenlyCovered f y I := by
  obtain ⟨inst, U, hxU, hU, hfU, H, hH⟩ := h
  filter_upwards [hU.mem_nhds hxU] with y hyU
  exact ⟨inst, U, hyU, hU, hfU, H, hH⟩

/-- **The fibres of a covering map are locally constant up to homeomorphism.**

`IsCoveringMap f` is by definition `∀ x, IsEvenlyCovered f x (f ⁻¹' {x})`, so
`IsEvenlyCovered.eventually` at `x` says that every nearby `y` is evenly covered **with index type
`f ⁻¹' {x}`**; `IsEvenlyCovered.fiberHomeomorph` then identifies that index type with `f ⁻¹' {y}`.

The conclusion is `Nonempty (… ≃ₜ …)` rather than a homeomorphism, because there is no canonical
choice: the identification depends on the evenly covered neighbourhood, and a different one gives
a different homeomorphism. Nothing below needs a canonical one. -/
theorem IsCoveringMap.eventually_nonempty_homeomorph (hf : IsCoveringMap f) (x : X) :
    ∀ᶠ y in 𝓝 x, Nonempty ((f ⁻¹' {y}) ≃ₜ (f ⁻¹' {x})) := by
  filter_upwards [(hf x).eventually] with y hy
  exact ⟨hy.fiberHomeomorph.symm⟩

/-- **Over a preconnected base, any two fibres of a covering map are homeomorphic.**

This is what connectedness of the base is for, and `IsCoveringMap` on its own does not give it:
being evenly covered relates the points *near* `x` to `x`, and nothing in the definition relates
two points that are far apart.

The proof is the clopen argument on `S = {z | Nonempty ((f ⁻¹' {z}) ≃ₜ (f ⁻¹' {x}))}`. Both halves
are `IsCoveringMap.eventually_nonempty_homeomorph` and nothing else — `Sᶜ` is open because
`Nonempty (· ≃ₜ ·)` is symmetric and transitive, so a point near a point *not* in `S` cannot be in
`S` either. `S` is nonempty because `x ∈ S` by `Homeomorph.refl`.

`PreconnectedSpace` and not `ConnectedSpace`: the base being nonempty is never used, and over the
empty space the statement is vacuous rather than false. -/
theorem IsCoveringMap.nonempty_homeomorph_fiber [PreconnectedSpace X] (hf : IsCoveringMap f)
    (x y : X) : Nonempty ((f ⁻¹' {x}) ≃ₜ (f ⁻¹' {y})) := by
  set S : Set X := {z | Nonempty ((f ⁻¹' {z}) ≃ₜ (f ⁻¹' {x}))} with hS
  have hopen : IsOpen S := by
    refine isOpen_iff_mem_nhds.2 fun z hz ↦ ?_
    filter_upwards [hf.eventually_nonempty_homeomorph z] with w hw
    exact ⟨hw.some.trans hz.some⟩
  have hcompl : IsOpen Sᶜ := by
    refine isOpen_iff_mem_nhds.2 fun z hz ↦ ?_
    filter_upwards [hf.eventually_nonempty_homeomorph z] with w hw hw'
    exact hz ⟨hw.some.symm.trans hw'.some⟩
  have huniv : S = Set.univ :=
    IsClopen.eq_univ ⟨⟨hcompl⟩, hopen⟩ ⟨x, ⟨Homeomorph.refl _⟩⟩
  exact ⟨(Set.eq_univ_iff_forall.mp huniv y).some.symm⟩

section BaseChange

variable {Y : Type*} [TopologicalSpace Y] {g : Y → X}

/-- **A covering map stays a covering map under base change along a continuous map.**

`Function.Pullback f g` is Mathlib's set-theoretic fibre product, a subtype of `E × Y`; the
topology on it is the subspace topology of the product, so nothing is constructed here beyond the
trivialisation itself.

Being evenly covered is a condition on the base and the witness for `g y` transports to `y`
unchanged: over an open `U ∋ g y` with `H : f ⁻¹' U ≃ₜ U × I`, the set `g ⁻¹' U` is an open
neighbourhood of `y`, and the part of the pullback lying over it goes to `(g ⁻¹' U) × I` by
`(e, y') ↦ (y', (H e).2)`. **The index type is the same `I`**, so
`IsEvenlyCovered.to_isEvenlyCovered_preimage` is all that is left to do.

**`Continuous g` cannot be dropped.** It is used on two facts — for `g ⁻¹' U` to be open, and for
the continuity of `z ↦ (g z.1 : U)`, which is what `continuous_invFun` composes with `H.symm` — and
it is not removable: `TwoIndiscrete.not_isCoveringMap_pullback_snd`
(`OkaTest/CoveringBaseChange.lean`) compiles a witness with `f` the identity of a two-element
discrete space and `g` the identity out of the same two points carrying the indiscrete topology,
where `Function.Pullback.snd` is a continuous bijection and not an open map. **The clause read *It
is used once, for `g ⁻¹' U` to be open, and that one use is not removable* until 2026-09-14**, when
the second fact was read off `IsCoveringMap.pullback_snd`'s own proof; the same numeral was in
`OkaTest/CoveringBaseChange.lean`'s module docstring and is repaired there by the same push. -/
theorem IsCoveringMap.pullback_snd (hf : IsCoveringMap f) (hg : Continuous g) :
    IsCoveringMap (Function.Pullback.snd : f.Pullback g → Y) := by
  intro y
  obtain ⟨inst, U, hyU, hU, hfU, H, hH⟩ := hf (g y)
  refine IsEvenlyCovered.to_isEvenlyCovered_preimage (I := f ⁻¹' {g y}) ?_
  have hsnd : Continuous (Function.Pullback.snd : f.Pullback g → Y) :=
    continuous_snd.comp continuous_subtype_val
  have hmemU : ∀ v : (g ⁻¹' U : Set Y), g (v : Y) ∈ U := fun v ↦ v.2
  have hmemV : ∀ p : (Function.Pullback.snd : f.Pullback g → Y) ⁻¹' (g ⁻¹' U),
      (p : f.Pullback g).1.2 ∈ g ⁻¹' U := fun p ↦ p.2
  -- the first component of a point of the pullback lying over `g ⁻¹' U` lies over `U`
  have hfst : ∀ p : (Function.Pullback.snd : f.Pullback g → Y) ⁻¹' (g ⁻¹' U),
      (p : f.Pullback g).1.1 ∈ f ⁻¹' U := fun p ↦ by
    change f (p : f.Pullback g).1.1 ∈ U
    rw [(p : f.Pullback g).2]; exact hmemV p
  -- the point of `E` the trivialisation produces lies over the right point of `X`
  have key : ∀ (v : (g ⁻¹' U : Set Y)) (i : (f ⁻¹' {g y} : Set E)),
      f ((H.symm (⟨g (v : Y), hmemU v⟩, i) : (f ⁻¹' U : Set E)) : E) = g (v : Y) := by
    intro v i
    have h := hH (H.symm (⟨g (v : Y), hmemU v⟩, i))
    rw [H.apply_symm_apply] at h
    exact h.symm
  have hleft : ∀ p : (Function.Pullback.snd : f.Pullback g → Y) ⁻¹' (g ⁻¹' U),
      ((H.symm (⟨g (p : f.Pullback g).1.2, hmemU ⟨_, hmemV p⟩⟩,
        (H ⟨(p : f.Pullback g).1.1, hfst p⟩).2) : (f ⁻¹' U : Set E)) : E)
        = (p : f.Pullback g).1.1 := by
    intro p
    have h : H ⟨(p : f.Pullback g).1.1, hfst p⟩
        = (⟨g (p : f.Pullback g).1.2, hmemU ⟨_, hmemV p⟩⟩,
          (H ⟨(p : f.Pullback g).1.1, hfst p⟩).2) := by
      refine Prod.ext (Subtype.ext ?_) rfl
      rw [hH]; exact (p : f.Pullback g).2
    rw [← h, H.symm_apply_apply]
  have hright : ∀ (v : (g ⁻¹' U : Set Y)) (i : (f ⁻¹' {g y} : Set E))
      (hw : ((H.symm (⟨g (v : Y), hmemU v⟩, i) : (f ⁻¹' U : Set E)) : E) ∈ f ⁻¹' U),
      (H ⟨((H.symm (⟨g (v : Y), hmemU v⟩, i) : (f ⁻¹' U : Set E)) : E), hw⟩).2 = i :=
    fun v i _ ↦ congrArg Prod.snd (H.apply_symm_apply (⟨g (v : Y), hmemU v⟩, i))
  exact ⟨inst, g ⁻¹' U, hyU, hU.preimage hg, hsnd.isOpen_preimage _ (hU.preimage hg),
    { toFun p := (⟨(p : f.Pullback g).1.2, hmemV p⟩, (H ⟨(p : f.Pullback g).1.1, hfst p⟩).2)
      invFun z := ⟨⟨⟨((H.symm (⟨g (z.1 : Y), hmemU z.1⟩, z.2) : (f ⁻¹' U : Set E)) : E),
        (z.1 : Y)⟩, key z.1 z.2⟩, z.1.2⟩
      left_inv p := Subtype.ext (Subtype.ext (Prod.ext (hleft p) rfl))
      right_inv z := Prod.ext rfl (hright z.1 z.2 _)
      continuous_toFun := Continuous.prodMk
        (Continuous.subtype_mk (continuous_snd.comp (continuous_subtype_val.comp
          continuous_subtype_val)) _)
        (continuous_snd.comp (H.continuous.comp (Continuous.subtype_mk (continuous_fst.comp
          (continuous_subtype_val.comp continuous_subtype_val)) _)))
      continuous_invFun := Continuous.subtype_mk (Continuous.subtype_mk (Continuous.prodMk
        (continuous_subtype_val.comp (H.symm.continuous.comp (Continuous.prodMk
          (Continuous.subtype_mk (hg.comp (continuous_subtype_val.comp continuous_fst)) _)
          continuous_snd)))
        (continuous_subtype_val.comp continuous_fst)) _) _ }, fun _ ↦ rfl⟩

omit [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace Y] in
/-- **Finite fibres base-change**: if every fibre of `f` is finite then so is every fibre of
`Function.Pullback.snd`.

`Function.Pullback.fst` sends the fibre of `Function.Pullback.snd` over `y` into `f ⁻¹' {g y}`, and
it is injective there because the second components agree by assumption. **Neither a covering
hypothesis nor a topology is used**, which is why the `TopologicalSpace` instances of this file are
omitted rather than left to be included and unused; and it is stated apart from
`IsCoveringMap.pullback_snd` because `ComplexAnalytic.AnalyticSpace.isFinite_coveringSpaceHom` asks
for a covering map and for finite fibres as two hypotheses rather than one. -/
theorem Function.Pullback.finite_fiber_snd (hfin : ∀ x, (f ⁻¹' {x}).Finite) (y : Y) :
    ((Function.Pullback.snd : f.Pullback g → Y) ⁻¹' {y}).Finite := by
  refine Set.Finite.of_finite_image (f := Function.Pullback.fst) ?_ ?_
  · refine (hfin (g y)).subset ?_
    rintro _ ⟨p, hp, rfl⟩
    change f (p : E × Y).1 ∈ ({g y} : Set X)
    rw [p.2]
    exact congrArg g hp
  · rintro p hp p' hp' h
    exact Subtype.ext (Prod.ext h (hp.trans hp'.symm))

end BaseChange
