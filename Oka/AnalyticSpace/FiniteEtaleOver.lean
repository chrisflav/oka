/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Mathlib.CategoryTheory.FintypeCat
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Oka.AnalyticSpace.Clopen
import Oka.AnalyticSpace.Degree

/-!
# The finite étale covers of an analytic space, as a category

`ComplexAnalytic.AnalyticSpace.IsFiniteEtale` is a property of a *morphism*. The Riemann existence
theorem is a statement about the *category* of such morphisms into a fixed base, and nothing in
this repository had made that category — `Oka/AnalyticSpace/CoveringSpace.lean` builds covering
spaces and compares them one at a time, and its `## What is not here` says nothing about morphisms
of covers because there was nothing to say it about. This file makes the category and says what a
morphism of covers is.

## The property is already a `MorphismProperty`, and the `def` below buys dot notation

`CategoryTheory.MorphismProperty C` is `∀ ⦃X Y : C⦄, (X ⟶ Y) → Prop`, and
`ComplexAnalytic.AnalyticSpace.IsFiniteEtale` is declared over the same telescope — `{X Y}` where
that is `⦃X Y⦄`, and **a binder annotation is not part of the type**, which is what the `@` below
discharges — so `@ComplexAnalytic.AnalyticSpace.IsFiniteEtale` **is** a morphism property with no
repackaging:
`example : MorphismProperty AnalyticSpace.{u} := @IsFiniteEtale.{u}` elaborates on the nose. This
is the same arrangement `Mathlib/AlgebraicGeometry/Morphisms/Finite.lean` relies on, where
`@AlgebraicGeometry.IsFinite` — a class with the same `{X Y}` binders — is used as a morphism
property while remaining a class.

**What does not work is dot notation.** `(@IsFiniteEtale).Over ⊤ X` fails, because the elaborator
sees a function type and goes looking for a field of `Function`; the message names a declaration
under that namespace which does not exist. So `ComplexAnalytic.AnalyticSpace.isFiniteEtale` below
is a name for something that already existed, and it is worth being precise about that: it is not
a second notion, it is `@IsFiniteEtale` with a head symbol, and
`ComplexAnalytic.AnalyticSpace.isFiniteEtale_iff` is `Iff.rfl`.

## Why the morphisms are all morphisms over the base

`CategoryTheory.MorphismProperty.Over P Q X` takes two properties: `P` cuts out the objects by
their structure map, and `Q` cuts out the morphisms. **`Q` is `⊤` here**, so a morphism of covers
is any morphism of analytic spaces commuting with the two structure maps, and nothing more. That
is the definition the Riemann existence theorem needs, and it is *not* the same as asking the
morphism to be finite étale itself. The two agree in extension —
`ComplexAnalytic.AnalyticSpace.isFiniteEtale_of_comp` (`Oka/AnalyticSpace/LocalIso.lean`) says the
underlying morphism of a morphism of covers is finite étale whenever the *target* cover's total
space is Hausdorff — but `Q` is still `⊤`, and that is what makes the category cheap to form: an
object of it carries no condition to discharge on its morphisms. See `## What is not here`.

## The four instances, and none of them is needed to form the category

`CategoryTheory.MorphismProperty.Over P Q X` asks its conditions of `Q`, and `Q` is `⊤` here, so
the category below would exist with no instance on `P` at all. **The one consumption of any of the
four in this repository is in this file**:
`ComplexAnalytic.AnalyticSpace.isFiniteEtale_of_restrictHom_top` applies
`CategoryTheory.MorphismProperty.comp_mem` twice, and that is
`CategoryTheory.MorphismProperty.IsStableUnderComposition`'s field — which
`CategoryTheory.MorphismProperty.IsMultiplicative` would supply as well, since it extends it, so
that use does not say which of the four is the one being consumed. The rest are stated in
anticipation, and because *finite étale morphisms compose and contain the identities* is a single
statement worth having under one name rather than as two instances elaborated separately.

**That sentence read *The four are stated because the downstream uses of the property — a
Galois-category structure, the comparison functor taxis #1113 wants — ask for them*, until
2026-09-08**, when it was measured rather than read, and **neither use it named existed at that
commit.** No `PreGaloisCategory` instance was in this repository, and the measurement was immune
to being written down: the name occurred in the **comment-stripped code** of no module of this
repository, so no declaration could mention it, while a plain grep for it was matched by this
sentence. `Oka/AnalyticSpace/MonoDirectSummand.lean`, `Oka/AnalyticSpace/SeparatedOver.lean` and
`Oka/AnalyticSpace/SeparatedFiniteEtale.lean` each say so of themselves in those words, and
`Oka/AnalyticSpace/SeparatedFiniteEtale.lean` adds that the namespace is not in that file's
import closure at all.

**The first of the two uses that sentence named exists from 2026-09-15 and the second is still
open**, which is why the paragraph above is written at its commit and not in the present tense:
`Oka/AnalyticSpace/GaloisCategory.lean` declares `CategoryTheory.PreGaloisCategory` at
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver`, so the name occurs in the
comment-stripped code of **two** modules of this repository from that commit — that one and
`OkaTest/GaloisCategory.lean` — with `scripts/import_cost.py`'s `strip_comments` the instrument;
the comparison functor is taxis #1113 and is open. **Whether the structure that now exists
consumes any of the four is not decided here**, and the paragraph below is what says which
instrument would decide it. **Neither a grep nor a guard can decide who consumes these four**, and
not because they are nameless — Lean generates a name for an anonymous instance and
`scripts/DumpOkaDecls.lean` emits all four, so
`#print axioms ComplexAnalytic.AnalyticSpace.instRespectsIsoIsFiniteEtale` elaborates. It is that
**no use site of an instance names it**, synthesis having put the term there, which is as true of a
named instance as of these. **The build decides it.** Declared `local instance` instead, so that no
module but this one sees them, the library still reaches `lake build` exit 0 over **4153** jobs at
`7a99bfc` and **4154** at `2cf6efa`, which is a proof that nothing outside this file consumes one;
removed outright they leave exactly **two** synthesis failures, both at
`ComplexAnalytic.AnalyticSpace.isFiniteEtale_of_restrictHom_top`'s two `comp_mem` applications.
Each run alters nothing but those four declarations, and the instrument is recorded as the sixth
object of `OkaTest/Axioms.lean`. **This paragraph said `attribute [local instance]` until
2026-09-12**, which is a different command and not this instrument: on a declaration that is
already a global `instance` it adds a local attribute and removes nothing, so the build stays green
whatever consumes it. The retired wording is kept here as a dated record.

**That numeral read 2026-09-08 from the commit that wrote this record, which is the day the
retired wording was *written* and not the day it was retired.** `0c370e5` put
`attribute [local instance]` into this paragraph at `2026-09-08T17:20:17Z`; `0eed5cd` replaced it
with `local instance` and wrote this record at `2026-09-12T16:45:34Z`. The paragraph said it
**from** the first of those days **until** the second, so the record named the day its wording
began. **This is a correction and not one of this repository's dated records**: a dated record
says what a clause read until some day, which presupposes it read true before that day, and the
numeral this repair replaces never did. **The instrument is `git log -G` or the removed side of
`git show 0eed5cd`, and not `git log -S`** — `-S` reports a commit only when the count of a string
changes, and a retirement quotes the wording it retires into the record that replaces it, so the
count does not move; run here it returns `0c370e5` alone, which is the commit whose date the wrong
numeral was, and so reads as though the record were dated correctly.
`OkaTest/Axioms.lean`'s paragraph on the same experiment took the same numeral from the same push
and is corrected in the same way and for the same reason.

Each is a quotation of a declaration that was already on `master`; nothing is proved here. (Those
three are named in the instances' own vicinity rather than in this docstring, because
`scripts/guard_coverage.py` reads every backticked repository name under a `## Main results`
heading as a result this file advertises, and they are another file's.)

**An earlier form of that list named a fibre functor, and that is now measurably wrong.**
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fiberFunctor` below reads the structure map of an
object and the triangle of a morphism, and **none of the four instances**;
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fintypeFiberFunctor` reads one thing more — the
object's `prop` field — and reads it only for the finiteness of the values. That is why a fibre
would make sense at every `CategoryTheory.MorphismProperty.Over` and not only at this one.

## Main definitions

- `ComplexAnalytic.AnalyticSpace.isFiniteEtale`: **finite étale as a
  `CategoryTheory.MorphismProperty`**, which is the class with a head symbol.
- `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver`: **the category of finite étale covers of a
  fixed analytic space**, with all morphisms over it.
- `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.id` and
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.trivial`: **two objects of it** — the base over
  itself, and the trivial `ι`-sheeted cover for a finite `ι`.
- `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.degree`: **the degree of a cover**, which is
  `ComplexAnalytic.AnalyticSpace.degree` of its structure map.
- `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.trivialIsoId`: **the trivial cover at one sheet
  is the base over itself**, as an isomorphism of objects.
- `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fiber`: **the fibre of a cover over a point of
  the base**, as the preimage type.
- `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fiberFunctor` and
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fintypeFiberFunctor`: **the fibre functor at a
  point**, into `Type u` and into `FintypeCat` — the first functors out of this category declared
  here, and the second is the shape a Galois category asks for.
- `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isPreconnectedT2`: **the covers whose total space
  is preconnected and Hausdorff**, as a `CategoryTheory.ObjectProperty` and hence as a full
  subcategory — the one the fibre functor is `CategoryTheory.Functor.Faithful` on.
- `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.sigma`: **the disjoint union of a finite family
  of covers**, as an object of the same category, with
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.sigmaι` for the inclusion of a member and
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.cofanSigma` for the cocone they make.
- `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fiberSigmaEquiv`: **the fibre of a disjoint union
  of covers is the disjoint union of the fibres**, as an equivalence of types, with
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fiberSigmaEquiv_apply` and
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fiberSigmaEquiv_apply_fintypeFiberFunctor` saying
  that its forward map is what each fibre functor does to the inclusion of a member.
- `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.restrictClopen`: **a cover restricted to a clopen
  subset of its total space**, as an object of the same category, with
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.restrictClopen_left` and
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.restrictClopen_hom` for its total space and its
  structure map, both by `rfl`. No hypothesis on the base, on the cover or on the subset beyond
  that its carrier is closed, and **no `[T2Space]` anywhere**: the structure map is built by
  composition, and it is cancellation and not composition that costs a separation axiom here.
- `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.restrictClopenι`: **its inclusion into the cover
  it came from**, as a morphism of covers, with
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.restrictClopenι_left` for the underlying morphism
  of analytic spaces. The triangle over the base holds by `rfl`.
- `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.restrictClopenCompl`: **the complementary clopen
  part**, which is `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.restrictClopen` at
  `ComplexAnalytic.AnalyticSpace.clopenCompl`.
- `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.restrictClopenComplι`: **the complementary part's
  own inclusion**, which is
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.restrictClopenι` at the complementary open and
  exists so that the cocone below can name it without unfolding.
- `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.binaryCofanRestrictClopen`: **the two inclusions
  read as a `CategoryTheory.Limits.BinaryCofan` on the cover they came from**, which is the shape
  the direct-summand axiom asks its coproduct in.

## Main results

- `ComplexAnalytic.AnalyticSpace.isFiniteEtale_iff`: membership is the class, by `Iff.rfl`.
- `ComplexAnalytic.AnalyticSpace.isIso_hom_of_iso_id`: **an object isomorphic to the base over
  itself has an invertible structure map.** This is what turns a `¬ IsIso` statement about one
  cover into the statement that the category has an object the identity is not, and it is how the
  non-vacuity in `OkaTest/FiniteEtaleOver.lean` is stated.
- `ComplexAnalytic.AnalyticSpace.isFiniteEtale_of_restrictHom_top`: **a morphism whose restriction
  over `⊤` is finite étale is finite étale** — the step that lets a `V` hypothesis be refuted
  rather than only left unproved, and the only place in this file where the property is read
  through an isomorphism rather than stated.
- `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.degree_eq_of_iso`: **the degree is an invariant of
  an object**, so `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isEmpty_iso_of_degree_ne`
  separates isomorphism classes by a number.
- `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.degree_id` and
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.degree_trivial`: the two objects above have
  degrees `1` and `Nat.card ι`, over a non-empty base.
- `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.degree_eq_mul`: **the degree of a cover is the
  degree of a morphism out of it times the degree of that morphism's target**, over a preconnected
  base with both total spaces Hausdorff and the target's preconnected. This is
  `ComplexAnalytic.AnalyticSpace.degree_comp` (`Oka/AnalyticSpace/Degree.lean`) read at the
  triangle, and it is what makes the degree of a morphism *of covers* a quantity rather than a
  spelling.
- `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.degree_dvd_degree`: **the degree of the target of
  a morphism of covers divides the degree of its source** — the first statement here that relates
  the degrees of two objects the category does not identify.
- `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.degree_left_eq_one`: **a morphism between covers
  of equal, non-zero degree has degree one**. **This bullet used to say that what it does not give
  is that the morphism is an isomorphism, and that the reader should see `## What is not here` for
  why**; it is still what *this* theorem does not give, and
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isIso_of_bijective_fiberMap` gives it.
- `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isEmpty_iso_trivial_id` and
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.card_eq_of_iso_trivial`: **the trivial covers of a
  non-empty base are pairwise non-isomorphic**, indexed by `Nat.card`, so the category there has
  as many isomorphism classes as there are values of that.
- `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.nonempty_iso_trivial_id_iff`: **and the first of
  those is sharp** — over a non-empty base the trivial cover is the base over itself exactly when
  its index type has one point. The two directions are proved by different means and neither is
  the other read backwards: the degree separates and never produces an isomorphism.
- `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.preconnectedSpace_of_iso` and
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isEmpty_iso_of_preconnectedSpace`:
  **preconnectedness of the total space is an invariant of an object**, and separates objects the
  degree cannot.
- `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.not_preconnectedSpace_trivial` and
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isEmpty_iso_trivial_of_preconnectedSpace`: **the
  total space of a trivial cover with two distinct sheets is disconnected**, so **a cover with a
  preconnected total space is not a trivial one with two distinct sheets** — the separation that
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.degree` is too coarse to make.
- `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.finite_fiber`: **a fibre is finite, with no
  hypothesis at all** — not a separation axiom, not connectedness, nothing about the base. This is
  what the fibre functor into `FintypeCat` needs, and the `## What is not here` bullet that priced
  it at a `[T2Space]` was reading the hypothesis of a different theorem.
- `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.card_fiber`: **the fibre counts the degree**, over
  a preconnected base and a Hausdorff total space, which is where that `[T2Space]` does belong.
- `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.uniqueFiberId` and
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fiberTrivialEquiv`: **the two values of the fibre
  functor this file can compute** — a point over the base over itself, and `ι` over the trivial
  `ι`-sheeted cover, both as equivalences rather than as counts.
- `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fiberEquivOfIso`: **isomorphic covers have
  equinumerous fibres**, which is `CategoryTheory.Functor.mapIso` at that functor.
- `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.base_eq_of_apply_eq`: **unique lifting** — two
  morphisms of covers that agree at one point of a preconnected source have the same map on
  points, over a Hausdorff total space of the target.
- `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.base_eq_of_fiberMap_eq` and
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.base_eq_of_fiberFunctor_map_eq`: **what the fibre
  functor's action determines is the base map**, at a point whose fibre is inhabited. The
  conclusion is an equality of maps on points; the extensionality statements below are the same
  hypotheses with an equality of *morphisms* as conclusion.
- `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.base_eq_id_of_apply_eq`: **an endomorphism of a
  connected cover that fixes a point is the identity on points** — the rigidity a deck
  transformation has, in the form that speaks of maps;
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.eq_id_of_apply_eq` is the same for the morphism.
- `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.hom_ext_of_base_eq`: **two morphisms of covers
  with the same base map are equal**, with no hypothesis on either object beyond their being
  objects. This is what separates the base-map statements above from faithfulness, and it says
  that a morphism of covers has no freedom in its map of structure sheaves beyond its map on
  points. `AlgebraicGeometry.LocallyRingedSpace.hom_ext_of_comp_eq` is the general fact it runs
  on.
- `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.hom_ext_of_apply_eq`,
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.hom_ext_of_fiberMap_eq` and
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.hom_ext_of_fiberFunctor_map_eq`: **the base-map
  statements above, with equality of morphisms as their conclusion.** The last is faithfulness
  of the fibre functor wherever its hypotheses hold — a preconnected source, a Hausdorff total
  space of the target, and a point of the fibre. **The third of those is dischargeable and the
  other two are not**: over a preconnected base
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.hom_ext_of_forall_fiberMap_eq` below asks for no
  point, and `CategoryTheory.Functor.Faithful` follows on the subcategory the first two cut out.
- `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.eq_id_of_apply_eq`: **an endomorphism of a
  connected cover that fixes a point is the identity morphism**, so the automorphisms of such a
  cover act freely on each fibre as automorphisms and not only as self-maps.
- `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.nonempty_fiber`: **over a preconnected base a
  cover with a non-empty total space has a non-empty fibre at every point** — the structure map is
  surjective there, by `ComplexAnalytic.AnalyticSpace.surjective_base_of_isFiniteEtale`.
- `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.hom_ext_of_forall_fiberMap_eq`: **two morphisms
  of covers agreeing on the whole fibre over a point of a preconnected base are equal, with no
  point of that fibre assumed.** This is the statement that removes the third hypothesis of
  faithfulness, and the empty case closes through
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.hom_ext_of_base_eq` rather than through a fibre.
- `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fiberFunctor_map_injective` and
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fintypeFiberFunctor_map_injective`: **the two
  fibre functors are injective on morphisms** out of a preconnected cover into a Hausdorff one,
  over a preconnected base.
- `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.faithful_fiberFunctor` and
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.faithful_fintypeFiberFunctor`:
  **`CategoryTheory.Functor.Faithful` for both fibre functors**, on the full subcategory
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isPreconnectedT2` and over a preconnected base.
  This is the class rather than a statement quantified by hand, and it is what `## What is not
  here` used to say no subcategory had been exhibited for.
- `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isIso_of_bijective_fiberMap`: **a morphism of
  covers whose fibre map at one point of the base is bijective is an isomorphism** — the
  statement `## What is not here` recorded as the thing nothing supplied, with no hypothesis of
  non-emptiness on either object.
- `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.reflectsIsomorphisms_fiberFunctor` and
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.reflectsIsomorphisms_fintypeFiberFunctor`:
  **`CategoryTheory.Functor.ReflectsIsomorphisms` for both fibre functors** — conservativity — on
  the same full subcategory and over the same preconnected base as the faithfulness above, so the
  two are read as a pair.
- `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isIso_of_isIso_left` and
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isEmpty_left_of_isEmpty_fiber`: **what
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isIso_of_bijective_fiberMap` is built out of**,
  and neither is about covers in particular —
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isIso_of_isIso_left` reflects an isomorphism
  along the two forgetful functors of the comma category, and
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isEmpty_left_of_isEmpty_fiber` reads
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.nonempty_fiber` backwards.
- `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isTerminalId` and
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.hasTerminal`: **the base over itself is a terminal
  object of the category, and so the category has one** — with no hypothesis on the base, the
  unique morphism out of a cover being its own structure map.
- `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isTerminalIdSubcategory`,
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.hasTerminalSubcategory` and
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.preservesLimitsOfShape_pempty_ι`: **the same
  object is terminal in the subcategory
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isPreconnectedT2` too**, over a preconnected and
  Hausdorff base, and the inclusion carries the one to the other.
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.preservesLimitsOfShape_pempty_ι` is what makes
  the preservation statements below hold of the *restricted* fibre functors by instance search, so
  neither of them is stated twice.
- `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isTerminalFintypeFiberId`: **the value of the
  `FintypeCat`-valued fibre functor at the base over itself is terminal**, which is
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.uniqueFiberId` read in that category.
- `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.preservesLimitsOfShape_pempty_fiberFunctor` and
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.preservesLimitsOfShape_pempty_fintypeFiberFunctor`:
  **both fibre functors preserve the terminal object**, with no hypothesis on the base or on the
  point. **This is a Galois-category axiom on the fibre functor**, as
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.hasTerminal` is one on the category;
  `## What is not here` says which of the others are absent, and base change of the class over a
  cospan of morphisms of covers is still among them. **This clause said *base change over a general
  cospan* until 2026-09-08**, when `Oka/AnalyticSpace/PullbackReduction.lean` gave the category the
  *limit* over a general cospan; what was absent then is the class being carried across it. **And
  it said *base change of the class over a general cospan* until 2026-09-15**, when
  `Oka/AnalyticSpace/FiniteEtaleStableUnderBaseChange.lean` carried the class across every cospan
  of `ComplexAnalytic.AnalyticSpace`; what a Galois category quantifies over is cospans of
  morphisms of this category, and that is what is absent now.
- `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isPreconnectedT2_id`,
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isPreconnectedT2_trivial_of_isEmpty` and
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isPreconnectedT2_trivial_of_isEmpty_base`:
  **objects of that subcategory** — the base over itself, when the base is preconnected and
  Hausdorff; the trivial cover at an empty index type, with no hypothesis at all; and the trivial
  cover over an empty base, at any finite index type at all.
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isPreconnectedT2_trivial_of_isEmpty` is the
  object whose empty fibre the `## What is not here` paragraph gave as its reason for keeping the
  point hypothesis, and it is inside the subcategory rather than outside it;
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isPreconnectedT2_trivial_of_isEmpty_base` is the
  witness that the `[Nonempty X]` of
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.not_preconnectedSpace_trivial` is doing work.
  `OkaTest/FiniteEtaleOver.lean` exhibits one that is not isomorphic to the base over itself.
- `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isColimitCofanSigma` and
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.hasFiniteCoproducts`: **the disjoint union of
  finitely many covers is their coproduct, so the category has finite coproducts** — with no
  hypothesis on the base, exactly as for the terminal object. **This is another Galois-category
  axiom on the category**, as
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.hasTerminal` is. The mathematics is
  `Oka/AnalyticSpace/Sigma.lean`'s and `Oka/AnalyticSpace/SigmaFiniteEtale.lean`'s, and what is
  done here is the transport of it across the comma category;
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.hasColimitsOfShape_discrete` is the statement at
  an index type of this category's own universe that the class is deduced from, and
  `## What is not here` says which axioms remain absent.
- `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isColimitFiberCofanSigma` and
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isColimitFintypeFiberCofanSigma`: **each fibre
  functor carries the cofan of the inclusions to a colimit cofan**, in `Type u` and in
  `FintypeCat` — the fibre of a disjoint union is the disjoint union of the fibres, read as a
  statement about cocones.
- `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.preservesColimitsOfShape_fiberFunctor` and
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.preservesColimitsOfShape_fintypeFiberFunctor`:
  **the same at every functor out of a discrete category on a finite index type of this category's
  own universe**, which is what the statements above become once the family a discrete diagram is
  determined by is put back. The shape is `CategoryTheory.Discrete` and the names do not say so,
  which is forced: a fully qualified name here is forty-five characters before its own, and a
  citation of it in prose has to fit on a line.
- `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.preservesFiniteCoproducts_fiberFunctor` and
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.preservesFiniteCoproducts_fintypeFiberFunctor`:
  **both fibre functors preserve finite coproducts**, with no hypothesis on the base and none on
  the point. **This is a Galois-category axiom on the fibre functor**, as
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.preservesLimitsOfShape_pempty_fiberFunctor` is,
  and it stands to
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.hasFiniteCoproducts` as that one stands to
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.hasTerminal`.
- `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isColimitBinaryCofanRestrictClopen`: **a cover is
  the coproduct of a clopen part of its total space and the complementary part.** No hypothesis on
  the base, on the cover or on the subset beyond that its carrier is closed. **This is the
  right-hand side of the direct-summand axiom and not the axiom**: what it does not supply is that
  a monomorphism's image is one of these subsets, which needs an injectivity statement.
  **That clause ended *"which needs an injectivity statement that this repository does not have"*
  until 2026-09-07**, when
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.injective_base_left_of_mono`
  (`Oka/AnalyticSpace/MonoDirectSummand.lean`) proved one, for a monomorphism of covers both of
  whose total spaces are Hausdorff. **What is still absent is the axiom**, which asks under no
  hypothesis at all. `## What is not here` says which obstructions are left.

## What is not here

* **The clopen parts of a cover do decompose it, and that still is not the direct-summand
  axiom.** `Mathlib/CategoryTheory/Galois/Basic.lean`'s axiom asks, of a monomorphism
  `i : A ⟶ B`, for an object and a morphism exhibiting `B` as the binary coproduct of `A` and it.
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isColimitBinaryCofanRestrictClopen` supplies that
  coproduct **once the monomorphism's image is known to be a clopen subset of `B`'s total space**,
  and this bullet used to say the coproduct itself was what was absent. It is not, and what is
  absent is the hypothesis it runs on.

  **What it runs on is that a monomorphism of covers has injective underlying map, and that is not
  proved or claimed here**: without it a monomorphism's image is not known to be among the clopen
  subsets in the first place — and the cancellation that makes a morphism of covers finite étale
  asks `[T2Space]` of the target's total space while the axiom asks nothing at all. taxis #1772 is
  the filing that measures both, and `OkaTest/FiniteEtaleCancel.lean` compiles the counterexample
  that makes the separation axiom a theorem rather than an artefact of a proof.

  **It is proved elsewhere as of 2026-09-07, and under two hypotheses rather than none.**
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.injective_base_left_of_mono`
  (`Oka/AnalyticSpace/MonoDirectSummand.lean`) is the injectivity, for a monomorphism of covers
  both of whose total spaces are Hausdorff, and
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.inducesIsoOnDirectSummand_of_mono` is the
  direct-summand statement it yields. **The sentence opening *What it runs on is that a monomorphism
  of covers has injective underlying map* stays true of this file**, which proves neither and
  states neither; what changes is that the obligation is no longer the repository's.

* **Cancellation — this is no longer absent, and it is not in this file.** *"If `g` and `f ≫ g`
  are finite étale then `f` is"* is `ComplexAnalytic.AnalyticSpace.isFiniteEtale_of_comp` in
  `Oka/AnalyticSpace/LocalIso.lean`, for a `[T2Space]` middle space. **This is what a
  Galois-category structure on the category below needs first**, and taxis #1114's report
  identifies the same statement as the difficulty of essential surjectivity; what that structure
  still lacks is in the two bullets below, and cancellation is no longer among it.

  **What it does not do is make a morphism of `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver X`
  carry a condition.** `Q` is `⊤` in the definition above and stays `⊤`; the cancellation says
  that the underlying morphism of every such morphism *is* finite étale, not that the category
  asks it to be. Nothing below reads it that way, and nothing below needs to.

  **The bullet was retired in three steps and the last one is the interesting one.** It first said
  the two classes are stated as stability under composition only and that Mathlib is in the same
  position one level down; both halves of that were wrong, and taxis #1312 measured how. It then
  said one topological statement was left, to be got at by a covering-map argument. That statement
  is proved, and it turned out not to be about covering maps: what was missing was a separation
  axiom on the middle space and nothing else — see the third sub-bullet.

  * `ComplexAnalytic.AnalyticSpace.IsFinite` **does** have a cancellation lemma —
    `ComplexAnalytic.AnalyticSpace.isFinite_of_isFinite_comp`, which concludes `IsFinite f` from
    `IsFinite (f ≫ i)`. What it asks in place of `IsFinite i` is
    `Function.Injective i.toLRSHom.base`, and the `i` here is the structure map of a cover, which
    is exactly what is not injective: `OkaTest/FiniteEtaleOver.lean`'s separating object is
    `ComplexAnalytic.sq`, whose `ComplexAnalytic.not_isIso_sq` is proved *from*
    non-injectivity. So the lemma exists and its hypothesis is the one a cover cannot supply,
    which is a route where "nothing exists" offered none.
  * `ComplexAnalytic.AnalyticSpace.IsLocalIso` **cancels outright** —
    `ComplexAnalytic.AnalyticSpace.isLocalIso_of_comp`, in `Oka/AnalyticSpace/LocalIso.lean` beside
    the `ComplexAnalytic.AnalyticSpace.isLocalIso_comp` it is the companion of — and it was free
    from Mathlib rather than hard: `IsLocalHomeomorph.of_comp` is its topological half and asks
    only that `f` be continuous, which a morphism's base map is, and
    `AlgebraicGeometry.LocallyRingedSpace.stalkMap_comp` with two-out-of-three is the stalk half.
    Those are the two steps that proof takes and it takes no others; the sentence was written here
    before the theorem existed, and what changed is that it now describes something.
    `Mathlib/Topology/Covering/Basic.lean` really does have no composition or cancellation lemma
    for `IsCoveringMap`, only conjugation by a homeomorphism — but that is the wrong file for this
    class, and the earlier version of this bullet carried that negative across from taxis #1114's
    report without noticing.
  * **Closedness of `f` was the last one, and the recorded obstruction to it named the wrong
    thing.** `Oka/AnalyticSpace/Finite.lean`'s cancellation section and
    `Oka/AnalyticSpace/LocalIso.lean`'s `## What is not here` both gave the real line with two
    origins as the shape, and both said the classical repair needs a separatedness notion and
    fibre products — neither of which this category has at the cospan that repair forms, for the
    same reason as the base-change bullet below. **That clause read *which this category cannot
    state* until `Oka/AnalyticSpace/PullbackOpen.lean` landed the pullback along the inclusion of
    an open subspace**, which is not the cospan the graph construction forms, so the absence is
    narrowed rather than struck. **What that example exhibits is a middle space with two points no
    open set separates, and the second factor is not what makes it work**: at a Hausdorff middle
    space the closed half cancels along an arbitrary second factor, by Mathlib's
    `isProperMap_of_comp_of_t2` and the properness of a finite morphism, which is
    `ComplexAnalytic.AnalyticSpace.isFinite_of_comp_of_t2Space` in
    `Oka/AnalyticSpace/Finite.lean`. So no separatedness notion and no fibre product was ever
    needed, and the hypothesis that was missing is a separation axiom rather than a construction.
    The counterexample is now compiled as
    `TwoIndiscrete.not_isClosedMap_pt_of_isClosedMap_comp` in `OkaTest/FiniteEtaleCancel.lean`,
    where it is the witness that the separation axiom cannot be dropped.
* **The fibre functor is here and the Galois category is not.**
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fiberFunctor` and
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fintypeFiberFunctor` below are the fibre at a
  point of the base, into `Type u` and into `FintypeCat`; the second is the shape a Galois category
  asks for, that definition being in `Mathlib/CategoryTheory/Galois/Basic.lean`, whose namespace is
  not in this file's import closure and so cannot be cited by name here.

  **The reason this bullet gave for their absence was wrong, and saying how is the point.** It said
  the fibre of a finite étale morphism is finite by
  `ComplexAnalytic.AnalyticSpace.card_fiber_eq_of_isFiniteEtale`, which asks `[T2Space]` of the
  source — a hypothesis lana-agents/oka#222's review measured is not free for a constructed cover.
  That theorem says two fibres have the **same** `Nat.card`, which a morphism all of whose fibres
  are infinite satisfies; finiteness is a *field* of `ComplexAnalytic.AnalyticSpace.IsFinite` and
  costs nothing, which is `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.finite_fiber` below. The
  `[T2Space]` buys **constancy** of the count, and constancy is what
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.card_fiber` needs and what a `FintypeCat`-valued
  functor does not.

  **What is absent is the Galois category itself.** Its axioms need the base change the
  **No base change of the class over a cospan of morphisms of covers** bullet below says this
  category has
  not — **and this
  sentence used to stop there, which read as though base change were the whole of what they
  need.** It is not. **The terminal object is one of the axioms and it is here now:**
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.hasTerminal` puts the base over itself at the top
  of the category with no hypothesis on the base at all,
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.hasTerminalSubcategory` does the same for the
  subcategory below over a preconnected and Hausdorff base, and
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.preservesLimitsOfShape_pempty_fiberFunctor` and
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.preservesLimitsOfShape_pempty_fintypeFiberFunctor`
  say the two fibre functors preserve it. **Finite coproducts are another axiom and are here
  now too:** `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.hasFiniteCoproducts` puts the disjoint
  union of finitely many covers in the category as their coproduct, again with no hypothesis on
  the base at all, and
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.preservesFiniteCoproducts_fiberFunctor` and
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.preservesFiniteCoproducts_fintypeFiberFunctor`
  say the two fibre functors preserve that as well. **What the terminal object and the finite
  coproducts discharge is the obligations named in this paragraph and no other**: base change of
  the class over a cospan of morphisms of covers is untouched by all of it, and so are quotients by
  finite group
  actions, the axiom that a monomorphism induces an isomorphism onto a direct summand, and the
  preservation of epimorphisms by a fibre functor. **This sentence said *base change over a
  general cospan* until 2026-09-08 and *base change of the class over a general cospan* until
  2026-09-15**, for the reason the bullet headed
  *No base change of the class over a cospan of morphisms of covers*
  gives under that heading, which is where each of the two moves is dated.

  **And none of the coproduct statements has a version on the subcategory
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isPreconnectedT2`, which is a fact about that
  subcategory rather than an omission.** The disjoint union of covers whose total spaces are
  preconnected is not one:
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.not_preconnectedSpace_trivial` is that at the
  trivial cover, whose total space is the disjoint union of copies of the base. So the subcategory
  is not closed under the coproduct and there is nothing there to restrict —
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.preservesLimitsOfShape_pempty_ι` has no analogue
  here, and the reason it exists at all is that the terminal object *is* an object of the
  subcategory by
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isPreconnectedT2_id`.

  **Faithfulness is
  no longer among the absences, and this paragraph used to be mostly about it.**
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.hom_ext_of_fiberFunctor_map_eq` says that two
  morphisms of covers whose images under the functor agree at one point of a fibre are **equal**,
  over a preconnected source and a Hausdorff total space of the target. **Conservativity is no
  longer among the absences either** —
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.reflectsIsomorphisms_fiberFunctor` is it, on the
  same subcategory and at the same hypothesis on the base, and
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.reflectsIsomorphisms_fintypeFiberFunctor` says it
  of the functor a Galois category asks for. **Reflecting isomorphisms is one of that definition's
  axioms and faithfulness is not**, which is why the two sit differently here although they hold
  on the same subcategory — but **the functor is not exhibited as an equivalence onto
  anything, or claimed to be**, and that clause of this bullet is untouched by any of it.

  **This bullet said that nothing turns an equivalence of fibres into an isomorphism of covers,
  and what made that false arrived in pieces, each from a different push.**
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.card_fiber` turns an equivalence of fibres at one
  point of a preconnected base into an equality of the two objects' degrees;
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.degree_left_eq_one` turns that equality — when
  the common degree is not `0` — into `AnalyticSpace.degree f.left = 1`; and
  `ComplexAnalytic.AnalyticSpace.isIso_of_degree_eq_one` (`Oka/AnalyticSpace/Degree.lean`) turns
  *that* into an isomorphism of analytic spaces, where
  `ComplexAnalytic.AnalyticSpace.isHomeomorph_base_of_degree_eq_one` stops at a homeomorphism of
  the underlying spaces.

  **Two obligations were recorded here as separating that chain from conservativity, and both
  turned out to be cheap.** The first is that `isIso_of_degree_eq_one` asks its target to be
  non-empty and nothing in the chain supplies it: that is not paid but **removed**, by
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isEmpty_left_of_isEmpty_fiber`, which closes the
  empty branch without a degree in it. The second is that the conclusion is an invertibility of
  `f.left` where conservativity wants one of `f`: that is
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isIso_of_isIso_left`, and it was two Mathlib
  reflections composed rather than a statement anybody had to prove about this category.
  **What made the first look like a price is that it is one for the theorem and not for the
  statement**: a `[Nonempty]` hypothesis would have been discharged by no object of
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isPreconnectedT2`, so paying it would have cost
  the `CategoryTheory.Functor.ReflectsIsomorphisms` instance and not only a line.

  **`CategoryTheory.Functor.Faithful` is here now, on a full subcategory** —
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.faithful_fiberFunctor` and
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.faithful_fintypeFiberFunctor`, on
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isPreconnectedT2` and over a preconnected base.
  **What this paragraph used to say, and got wrong, is which of the three hypotheses was the
  obstruction.** It said the point of the fibre was *not a technicality*, on the ground that the
  trivial cover at an empty index type has an empty fibre and the functor's value there determines
  nothing. **That much is true** —
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fiberTrivialEquiv` puts that fibre in bijection
  with the index type — **and it is not a counterexample to faithfulness**: over a **preconnected
  base** an empty fibre forces the total space itself to be empty, by
  `ComplexAnalytic.AnalyticSpace.surjective_base_or_isEmpty_of_isFiniteEtale`, and a morphism out
  of an empty cover is determined by
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.hom_ext_of_base_eq` with no fibre read at all.
  **That object is inside the subcategory and not outside it**, by
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isPreconnectedT2_trivial_of_isEmpty`.
  **The point is the hypothesis that drops; the other two are the ones that stay**, and they stay
  as the conditions the subcategory is cut out by rather than as quantifiers written by hand.

  **What preconnectedness of the base costs is a hypothesis on the statement and not on an
  object**, so it does not enter the subcategory; and the subcategory is not empty —
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isPreconnectedT2_id` puts the base over itself in
  it, `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isPreconnectedT2_trivial_of_isEmpty` puts the
  trivial cover at an empty index type in it,
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isPreconnectedT2_trivial_of_isEmpty_base` puts
  the trivial cover over an empty base in it at any finite index type at all, and
  `OkaTest/FiniteEtaleOver.lean`'s `sqOver` is in it as well, not isomorphic to the base over
  itself.

  **What closed the gap was one general lemma, and the statements the previous version of this
  paragraph named — `AlgebraicGeometry.LocallyRingedSpace.stalkMap_comp` and
  `AlgebraicGeometry.LocallyRingedSpace.hom_stalk_ext` — were the ingredients rather than the
  composition.**
  `AlgebraicGeometry.LocallyRingedSpace.hom_ext_of_comp_eq`
  (`Oka/Geometry/RingedSpace/LocallyRingedSpace.lean`) is the step nobody had taken: a morphism
  all of whose stalk maps are isomorphisms cancels on the right against two morphisms with the
  same base map. Applied at `B.hom` — whose stalk maps are isomorphisms by
  `ComplexAnalytic.AnalyticSpace.IsLocalIso.isIso_stalkMap`, which an object of this category
  carries in its `prop` field — against the composites
  `CategoryTheory.MorphismProperty.Over.w` supplies at `f` and at `g`, it is
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.hom_ext_of_base_eq`. It runs on
  `AlgebraicGeometry.LocallyRingedSpace.hom_stalk_ext` and discharges that statement's
  `TopCat.Presheaf.stalkCongr` residue with
  `AlgebraicGeometry.LocallyRingedSpace.stalkMap_congr_point` and
  `AlgebraicGeometry.LocallyRingedSpace.stalkMap_congr_hom`, which were in Mathlib all along and
  make the residue a rewrite rather than a `subst` argument.

  **Two earlier versions of this paragraph were wrong about that, in opposite directions, and
  saying so is the point.** The first said `hom_stalk_ext` was in neither this repository nor
  Mathlib; both halves were false, the search behind it having asked for `stalk` before `hom_ext`
  when the name has them the other way round. The second, having found it, said that nothing
  composes them here — which was true — and **declined to say what composing them would cost**.
  Declining was right, and the answer was one lemma about locally ringed spaces that mentions
  neither covers nor analytic spaces.
* **No base change of the class over a cospan of morphisms of covers.**
  `CategoryTheory.MorphismProperty.IsStableUnderBaseChange` for `isFiniteEtale` quantifies over
  cospans of `ComplexAnalytic.AnalyticSpace`, and it is a theorem of this repository:
  `ComplexAnalytic.AnalyticSpace.isStableUnderBaseChange_isFiniteEtale`, in
  `Oka/AnalyticSpace/FiniteEtaleStableUnderBaseChange.lean`. What is absent is the same statement
  at **this** category — nothing here carries `isFiniteEtale` across a cospan of morphisms of
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver X`, which is what a Galois category's axioms
  quantify over, and a morphism of that category is not known to be finite étale without
  `[T2Space]` of its target.

  **The heading read *No base change of the class over a general cospan*, and the sentence under
  it read *`CategoryTheory.MorphismProperty.IsStableUnderBaseChange` — which quantifies over every
  cospan — is not statable for `isFiniteEtale`: nothing in this repository carries that class
  across a square whose finite étale leg has an arbitrary source*, until 2026-09-15**, when
  `Oka/AnalyticSpace/FiniteEtaleStableUnderBaseChange.lean` stated it. **The heading had to move
  and not only the sentence under it**, because *the class* there is `isFiniteEtale` and *a general
  cospan* is a cospan of `ComplexAnalytic.AnalyticSpace`, so the statement that landed carries both
  of its words; what this bullet is *about* did not move, and the paragraph below beginning **What
  that still does not reach** had already said what that is.

  **The heading read *No pullback over a general cospan, so no base change* and the sentence under
  it began *`CategoryTheory.Limits.HasPullbacks ComplexAnalytic.AnalyticSpace` does not
  synthesise, so*, until 2026-09-08**, when `Oka/AnalyticSpace/PullbackReduction.lean` made
  `ComplexAnalytic.AnalyticSpace.hasPullbacks` a theorem of this repository. **The limit existing
  is not the class being carried**, which is what this bullet was always about and is why it is
  narrowed rather than struck: `Oka/AnalyticSpace/FiniteEtaleBaseChange.lean` carries
  `isFiniteEtale` across the square it builds itself, at a finite étale leg — **that clause read
  *at a finite étale leg with Hausdorff source* until 2026-09-14**, when the separation axiom came
  out of that file, and what this bullet is about is unmoved by it — and nothing carries it across
  the square
  `ComplexAnalytic.AnalyticSpace.hasPullback` now supplies at an arbitrary one. Every place that
  cites this bullet by its heading was rewritten in the same push — the ones in this file that the
  paragraph opening *The four sentences in this file that cite this bullet by its heading are
  unaffected* names, and one in `Oka/AnalyticSpace/FiniteEtaleBaseChange.lean` — and each says
  which half of the old heading it was citing.

  **The last clause of the sentence above read `"and the pullback of a cover along an arbitrary
  morphism of the base, which is how a Galois category's fibre functor is usually built, is not
  available to it"` until 2026-09-07**, when `Oka/AnalyticSpace/FiniteEtaleBaseChange.lean`
  supplied exactly that: `ComplexAnalytic.AnalyticSpace.hasPullback_of_isFiniteEtale` is a
  `CategoryTheory.Limits.HasPullback` instance at every cospan whose first leg is finite étale,
  and `ComplexAnalytic.AnalyticSpace.isFiniteEtale_pullback_snd_of_isFiniteEtale` carries the
  class across it. **That sentence read *at every cospan whose first leg is finite étale with
  Hausdorff source* until 2026-09-14**, when the separation axiom came out of that file. **What
  that still does not reach is this bullet's subject**: this bullet is about a base change over a
  cospan of morphisms **of covers**, and a
  morphism of `FiniteEtaleOver X` is not known to be finite étale without `[T2Space]` of its
  target — which is taxis #1772's remaining half and is not this bullet's. **That sentence closed
  *and the heading is unchanged because of it* until 2026-09-15**, when the heading did move: the
  clause was exact while the heading read *over a general cospan* and no statement in the tree
  carried the class over one, and what retires it is that statement landing rather than any change
  in what this bullet is about. **The sentence that
  distinguished the two read *`IsStableUnderBaseChange` quantifies over cospans whose finite étale
  leg has an arbitrary source*, until 2026-09-14**: that reading of the gap was exact while
  `Oka/AnalyticSpace/FiniteEtaleBaseChange.lean` asked for a Hausdorff source, and it is not what
  separates them now.
  **Every sentence in this file that cites this bullet by its heading was rewritten with it, and
  there are five of them.** Three
  are elsewhere in this module docstring — the one opening *"What is absent is the Galois category
  itself"*, the one saying that what separates two connected covers is the monodromy *action*, and
  the one **closing the paragraph the first of these opens**, whose two earlier wordings are dated
  in the same breath as its citation —
  and two are in the docstrings of
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.faithful_fintypeFiberFunctor` and of
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.preservesLimitsOfShape_pempty_fiberFunctor`.
  Four of the five cite it for the absence at the cospans a Galois category quantifies over, which
  is what it still asserts; the third of the three cites it for the *reason*, which is where the
  bullet dates its own moves. Each named the old heading and now names this one.

  **The count of four was exact when it was written, and the sentence that was false when written
  is the one saying the count had not moved.** `git blame` separates the two, and they are not one
  push: the sentence *The four sentences in this file that cite this bullet by its heading are
  unaffected* and its naming of the four are `69a54dd`'s, of 2026-09-07, and at that commit the
  wrapped-and-joined scan of this file returns **five** occurrences of the then-heading
  *No pullback over a general cospan, so no base change* — the bullet itself and **four**
  citations, which are the four it named. `2cf6efa`, of 2026-09-08, moved the heading to
  *No base change of the class over a general cospan* and **added a fifth citation in the same
  diff**: the clause that closes the paragraph opening *What is absent is the Galois category
  itself*, dating *base change over a general cospan* to that day and naming the new heading as it
  does so. At `2cf6efa` the same scan returns **six** — the bullet and five citations.

  **So the sentence `2cf6efa` wrote beside it — *All four were rewritten on 2026-09-08 to cite it
  under its new heading and to say `of the class`, and the count of four is unchanged by that* —
  stood until 2026-09-15 and was false in the push that wrote it**, the count having moved from
  four to five in that very diff. **That one is a correction and not one of this repository's dated
  records, and `69a54dd`'s sentence is the opposite case and is dated rather than corrected**: it
  was exact when it was written and was falsified by a later push, which is what a dated record
  presupposes and a correction denies. **Two retirements in one push, one date, and only one of
  them a correction.**

  **What hid the fifth citation is the register and not the reading**: it wraps after *of the
  class*, so `git grep` for the heading reached four of the five in this file, which is the
  blindness `README.md`'s census section is about, and the wrapped-and-joined scan reaches all
  five. **Both registers now return 12 over `Oka/` and `OkaTest/` and agree file by file**, this
  push having re-wrapped the two citations of this file that straddled a line break — that fifth
  one and the one in
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.preservesLimitsOfShape_pempty_fiberFunctor` — and
  rewritten outright the one outside it that did, so
  that a later seat renaming this heading again is not told four where there are five.

  **This sentence read *The four sentences in this file that cite this bullet by its heading are
  unaffected* until 2026-09-15**, when the heading moved a second time and the count was written
  upward with it. **The date is the push that retires the wording and not the day it stopped being
  true**, which is `README.md`'s rule and is why it is 2026-09-15 and not 2026-09-08: the count
  went to five at `2cf6efa`, for the reason the two paragraphs above give, and no push between that
  one and this one read the sentence against the file.

  **One further citation of the old heading
  stood in `Oka/AnalyticSpace/FiniteEtaleBaseChange.lean` and was rewritten in the same push, and
  it is not among them because that file is not this one.** That was the whole of the outside
  on 2026-09-08. **It is not now, and this clause named only that file until 2026-09-15**: the
  wrapped-and-joined scan over `Oka/` and `OkaTest/` returns **four** citations
  outside this file at the commit this push is cut from — that one, together with
  `Oka/AnalyticSpace/LocalAtTarget.lean`, `Oka/AnalyticSpace/LocalIso.lean` and
  `Oka/AnalyticSpace/PullbackOpen.lean` — and all four are rewritten in this push. **A line-wise
  `git grep` returns three of those four**, the one in `Oka/AnalyticSpace/LocalAtTarget.lean`
  wrapping after *general*: the same blindness as inside this file, in a second population, so
  the two registers stand at 4 / 6 in this file and 7 / 10 over the tree at that commit.
  **The clause was
  exact when written**: `git blame` puts the two in `Oka/AnalyticSpace/LocalIso.lean` and
  `Oka/AnalyticSpace/PullbackOpen.lean` at `2cf6efa`, the push that wrote this paragraph, and its
  diff shows both as additions citing the *new* heading rather than rewrites of the old one, and
  the one in `Oka/AnalyticSpace/LocalAtTarget.lean` at `b79ab9b`, six days later.
  **This paragraph named
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.preservesLimitsOfShape_pempty_fintypeFiberFunctor`
  where it now names
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.preservesLimitsOfShape_pempty_fiberFunctor`,
  until 2026-09-07, and was false when written, so this is a correction and not one of this
  repository's dated records**: the citation sits in the docstring that ends at the `Type u`-valued
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.preservesLimitsOfShape_pempty_fiberFunctor`, and
  the docstring of
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.preservesLimitsOfShape_pempty_fintypeFiberFunctor`
  cites this bullet by no heading — it cites the `Type u`-valued instance instead, for the
  spelling of its conclusion. Both are declarations, so `scripts/check_docstring_names.py`
  resolves either name and only a read of the two docstrings separates them; **the count is
  unaffected whatever it stands at**, since the citation is the same sentence under either name.
  That clause named the count as *four* while four is what the paragraph above it said; it is not
  re-dated here, because what it asserts — that a renaming inside one citation moves no count —
  was true at four and is true at five.
  The heading is unchanged for the same reason.

  **This bullet read *No pullbacks, so no base change* and said that no `HasPullback` instance for
  analytic spaces is available and that none is exhibited or claimed.** That was exact until
  `Oka/AnalyticSpace/PullbackOpen.lean`, which exhibits
  `ComplexAnalytic.AnalyticSpace.hasPullback_ofRestrict` — the pullback along the inclusion of an
  open subspace — and carries `isFiniteEtale` across it at
  `ComplexAnalytic.AnalyticSpace.isFiniteEtale_pullback_snd_ofRestrict`. **What that buys for a
  Galois category is nothing**, since the axioms quantify over cospans whose legs are arbitrary
  morphisms of covers, and it is named here so that the absence is stated at the strength it
  actually has.

  **The functor above is not built that way and is not evidence that this absence is harmless**:
  it reads the structure map at one point of the base directly, which is enough to *have* a fibre
  and is not enough to say anything about how it varies.
* **The degree on objects is here, it is coarse, and the second invariant that repairs that is
  here too.** This bullet said `ComplexAnalytic.AnalyticSpace.degree` is a function of a morphism
  and nothing below reads it off an object;
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.degree` does, and
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.degree_eq_of_iso` is what makes that well defined
  on isomorphism classes. It said next that the invariant is coarse and that **nothing below can
  tell apart** the two degree-`2` covers of the punctured line — `OkaTest/FiniteEtaleOver.lean`'s
  `z ↦ z²` and the trivial two-sheeted cover — and that the classical separation, connectedness of
  the total space, was half present in this repository.

  **Both halves are present now and the separation is below.**
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isEmpty_iso_trivial_of_preconnectedSpace` is the
  statement, and what it needed was not a construction: the missing half was
  `ComplexAnalytic.AnalyticSpace.not_preconnectedSpace_sigma`
  (`Oka/AnalyticSpace/SigmaFiniteEtale.lean`), which is the clopen image of a member read as a
  separation, and the transport
  `ComplexAnalytic.AnalyticSpace.preconnectedSpace_of_surjective_base`
  (`Oka/AnalyticSpace/Basic.lean`), which is `DenseRange.preconnectedSpace` at a surjection.
  **The degree bullet's own claim is unchanged and is the point**: the degree still cannot
  separate those two objects, and it is a second invariant rather than a sharper first one that
  does.

  **What is still not here is any invariant that separates two *connected* covers, and the fibre
  functor above is not one.** As a bare finite set a fibre carries nothing the degree does not
  already carry — over a preconnected base and a Hausdorff total space its size *is* the degree,
  by `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.card_fiber` — and what separates is the
  monodromy *action* on it, which needs a fundamental group nothing here connects to a cover and
  the base change the **No base change of the class over a cospan of morphisms of covers** bullet
  above says this category has not.

  **What the witness in `OkaTest/FiniteEtaleOver.lean` settles is that the functor's values are
  not a complete invariant.** `OkaTest.FiniteEtaleOver.nonempty_fiber_equiv_trivial_sqOver` puts
  the fibres of `z ↦ z²` and of the trivial two-sheeted cover of the punctured line in bijection
  at every point of the base — the same pair that
  `OkaTest.FiniteEtaleOver.not_iso_trivial_sqOver` proves non-isomorphic. So two objects this
  category distinguishes have fibres it does not, at a base this repository exhibits, and that
  much is compiled rather than argued. **It needs neither `[T2Space]` nor `[PreconnectedSpace]`**,
  the finiteness of a fibre being unconditional.

  **What it does not settle is the connected-covers sentence above, and the reason is the second
  member of its pair.** The trivial two-sheeted cover's total space is disconnected —
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.not_preconnectedSpace_trivial`, which is what
  `OkaTest.FiniteEtaleOver.not_iso_trivial_sqOver` reads and not what it proves — so the pair is a
  connected cover and a disconnected one, and a claim quantified over pairs of *connected* covers
  is untouched by it. **At a pair of connected covers this repository does exhibit, the values do
  separate**: `OkaTest.FiniteEtaleOver.sqOver` and the base over itself at the punctured line are
  both preconnected (`OkaTest.FiniteEtaleOver.preconnectedSpace_left_sqOver` and
  `ComplexAnalytic.preconnectedSpace_restrict_punctured`) and non-isomorphic
  (`OkaTest.FiniteEtaleOver.not_iso_id_sqOver`), and their fibres have two points and one —
  `OkaTest.FiniteEtaleOver.card_fiber_sqOver` and
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.uniqueFiberId`. **That separation is the degree
  again** and is no evidence that the fibre sees more, which is the paragraph above read at an
  instance. So the connected-covers sentence above stays an argument, and what would
  compile it is a pair of *non-isomorphic* connected covers of the same degree — which is what
  the missing monodromy action would be needed to tell apart.
* **No scheme side and no comparison functor.** Taxis #1113 wants a functor from finite étale
  covers of a presented affine `ℂ`-scheme to these; the source of that functor is
  `(@AlgebraicGeometry.IsFinite ⊓ @AlgebraicGeometry.IsEtale).Over ⊤ X` and is available in
  Mathlib immediately, but it mentions `AlgebraicGeometry.Scheme`. **The reason given here until
  2026-09-02 was that "this line of files does not have" one, "three of them argue in titled
  sections that its absence is a result", and both halves of that have moved.** The appositive
  names the `Oka/Analytification/` line, since that is where those sections are, and
  `Oka/Analytification/SpecScheme.lean` put `ComplexAnalytic.specScheme` on it; and there are
  **two** of them, not three — `Oka/Analytification/Comparison.lean`'s, which is about that file's
  own statements, and `Oka/Analytification/AffineCover.lean`'s, which is about its input. At
  `3e6e87d` no file under `Oka/AnalyticSpace/`, where this one lives, had such a section.
  **What survives is the shape of the obstruction and not its price**: `ComplexAnalytic.specScheme`
  is glued *from* a cover datum and is an output of one, where the functor above wants a scheme as
  its *input*, and no passage in that direction is exhibited or claimed here.
  `Oka/AnalyticSpace/Glue.lean`'s first bullet makes the same distinction for the same reason.
  **Nothing below mentions a scheme.**
## The `Mathlib/CategoryTheory/Galois/Basic.lean` scoping, and the record for it

**Every sentence of this file that scopes that namespace read *this repository's import closure*,
until 2026-09-15**, when `Oka/AnalyticSpace/GaloisCategory.lean` imported that file and declared
`CategoryTheory.PreGaloisCategory` at
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver` together with
`CategoryTheory.PreGaloisCategory.FiberFunctor` at its `FintypeCat`-valued fibre functor. **From
that commit the class is in this repository's import closure and is still not in this file's**,
which is why those sentences now say *this file's* — **all but one**: the clause reporting what
`Oka/AnalyticSpace/SeparatedFiniteEtale.lean` says of its own closure says *that file's*, a
demonstrative in a reported claim pointing at the file reported on and not at this one. No import
of this module reaches the one that pays for the class, so nothing here can name it and every
clause of this file that says so stays exact. **The rescoping is not this file's whole share of
that push**: the paragraph recording the measurement of 2026-09-08 asserted that no
`PreGaloisCategory` instance is in this repository, which the same push falsifies, and it is
rewritten at its commit rather than left in the present tense. `git diff` against the commit this
file is cut from shows both.
-/

open CategoryTheory

universe u

namespace ComplexAnalytic.AnalyticSpace

/-- **Finite étale, as a `CategoryTheory.MorphismProperty`.**

This is `ComplexAnalytic.AnalyticSpace.IsFiniteEtale` and not a second notion —
`ComplexAnalytic.AnalyticSpace.isFiniteEtale_iff` is `Iff.rfl` — declared so that the dot notation
`isFiniteEtale.Over` resolves; the class itself has the binders of a morphism property but the
elaborator will not project a field from a function type. -/
def isFiniteEtale : MorphismProperty AnalyticSpace.{u} := @IsFiniteEtale.{u}

/-- **Membership in the property is the class**, by definition. -/
theorem isFiniteEtale_iff {X Y : AnalyticSpace.{u}} (f : X ⟶ Y) :
    isFiniteEtale.{u} f ↔ IsFiniteEtale f :=
  Iff.rfl

instance : (isFiniteEtale.{u}).IsStableUnderComposition where
  comp_mem f g hf hg := @isFiniteEtale_comp.{u} _ _ _ f g hf hg

instance : (isFiniteEtale.{u}).ContainsIdentities where
  id_mem X := isFiniteEtale_id X

instance : (isFiniteEtale.{u}).IsMultiplicative where

instance : (isFiniteEtale.{u}).RespectsIso :=
  MorphismProperty.respectsIso_of_isStableUnderComposition
    fun _ _ f (_ : IsIso f) ↦ isFiniteEtale_of_isIso f

/-- **The finite étale covers of `X`**, as a category: the objects are the finite étale morphisms
into `X` and the morphisms are all the morphisms of analytic spaces over `X`.

The second `⊤` is the property asked of the morphisms, and it is deliberate: a morphism of covers
commutes with the two structure maps and is asked for nothing else. -/
abbrev FiniteEtaleOver (X : AnalyticSpace.{u}) : Type _ :=
  (isFiniteEtale.{u}).Over ⊤ X

/-- **The base over itself**, which is an object because the identity is finite étale. -/
def FiniteEtaleOver.id (X : AnalyticSpace.{u}) : FiniteEtaleOver.{u} X :=
  MorphismProperty.Over.mk _ (𝟙 X) (isFiniteEtale_id X)

/-- **The trivial `ι`-sheeted cover**, for a finite index type: `∐_{i : ι} X ⟶ X`.

`ComplexAnalytic.AnalyticSpace.isFiniteEtale_sigmaFold` is what makes it an object, and it asks
nothing of `X` — not Hausdorff, not connected, not non-empty. At an inhabited subsingleton `ι`
this is `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.id` up to the isomorphism
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.trivialIsoId` below, and over a non-empty base
those are the only index types at which it is
(`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.nonempty_iso_trivial_id_iff`). -/
noncomputable def FiniteEtaleOver.trivial (ι : Type u) [Finite ι] (X : AnalyticSpace.{u}) :
    FiniteEtaleOver.{u} X :=
  MorphismProperty.Over.mk _ (sigmaFold ι X) (isFiniteEtale_sigmaFold (ι := ι) X)

/-- **An object isomorphic to the base over itself has an invertible structure map.**

This is the lemma that lets a `¬ IsIso` statement about one cover — of which this repository has
one, for `z ↦ z²` on the punctured line — say that the category has an object the identity is
not. The proof is that the two forgetful functors carry the isomorphism to one of analytic spaces
whose morphism is `e.hom.left`, and that the triangle over `X` identifies `e.hom.left` with the
structure map, the other side of it being the identity.

**The last step is a term and not a `rw [Category.comp_id]`**: the composite displays as
`e.hom.left ≫ (FiniteEtaleOver.id X).hom` and `rw` works at `instances` transparency, which does
not unfold the `def` to reach the `𝟙 X` inside. `(Category.comp_id _).symm.trans` is the same
step at default transparency and is one line. -/
theorem isIso_hom_of_iso_id {X : AnalyticSpace.{u}} {A : FiniteEtaleOver.{u} X}
    (e : A ≅ FiniteEtaleOver.id.{u} X) : IsIso A.hom := by
  have h1 : IsIso e.hom.left :=
    ((MorphismProperty.Over.forget _ ⊤ X ⋙ CategoryTheory.Over.forget X).mapIso e).isIso_hom
  have h2 : e.hom.left = A.hom := by
    have hw : e.hom.left ≫ 𝟙 X = A.hom :=
      CategoryTheory.Over.w ((MorphismProperty.Over.forget _ ⊤ X).map e.hom)
    exact (Category.comp_id _).symm.trans hw
  rwa [h2] at h1

/-- **A morphism of covers whose underlying morphism is invertible is invertible.**

The category is `CategoryTheory.MorphismProperty.Over isFiniteEtale ⊤ X`, whose morphisms carry
no condition, so this ought to be free — and it is, twice over, but **neither reflection alone
has `f.left` as its `map` and that is why the composite has to be written out**.
`CategoryTheory.MorphismProperty.Comma.forget` reflects isomorphisms at
`[Q.RespectsIso] [W.RespectsIso]`, which `⊤` supplies, and it lands in
`CategoryTheory.Over X`; `CategoryTheory.Over.forget` reflects them too and lands in
`ComplexAnalytic.AnalyticSpace`. `CategoryTheory.MorphismProperty.Over.forget_comp_forget_map`
says the composite's action on a morphism **is** `f.left`, by `rfl`, and that is the functor
`CategoryTheory.isIso_of_reflects_iso` has to be handed.

**The same composite is what `ComplexAnalytic.AnalyticSpace.isIso_hom_of_iso_id`
above transports an isomorphism along**, in the preservation direction where every functor works;
this is the reflection, and it needs the two `ReflectsIsomorphisms` instances that direction does
not. -/
theorem FiniteEtaleOver.isIso_of_isIso_left {X : AnalyticSpace.{u}}
    {A B : FiniteEtaleOver.{u} X} (f : A ⟶ B) (h : IsIso f.left) : IsIso f := by
  haveI : IsIso ((MorphismProperty.Over.forget isFiniteEtale.{u} ⊤ X ⋙
      CategoryTheory.Over.forget X).map f) := h
  exact isIso_of_reflects_iso f
    (MorphismProperty.Over.forget isFiniteEtale.{u} ⊤ X ⋙ CategoryTheory.Over.forget X)

/-! ### The terminal object -/

/-- **The base over itself is a terminal object of the category of finite étale covers.**

The unique morphism out of a cover `A` is its own structure map, read as a morphism over `X`: a
morphism of this category is a morphism of analytic spaces commuting with the two structure maps
and nothing more — `Q` is `⊤`, as the docstring of
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver` says — and the triangle asked of `A.hom` here is
`A.hom ≫ 𝟙 X = A.hom`. Uniqueness is the same equation run backwards at an arbitrary `f`.

**Both halves are terms and neither is a `rw [Category.comp_id]`, for the reason
`ComplexAnalytic.AnalyticSpace.isIso_hom_of_iso_id` gives.** The identity in
`(ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.id X).hom` is `𝟙 X` only after the `def` is
unfolded, which `rw` will not do at `instances` transparency — it reports the target as not
type-correct there — and `simpa` reports the two sides as equalities in different types.
`(Category.comp_id _).symm.trans` is the same step at default transparency.

**This asks nothing of `X`.** Not Hausdorff, not connected, not non-empty; the object exists
because `ComplexAnalytic.AnalyticSpace.isFiniteEtale_id` does. -/
def FiniteEtaleOver.isTerminalId (X : AnalyticSpace.{u}) :
    Limits.IsTerminal (FiniteEtaleOver.id.{u} X) :=
  Limits.IsTerminal.ofUniqueHom
    (fun A ↦ MorphismProperty.Over.homMk (B := FiniteEtaleOver.id.{u} X) A.hom
      (Category.comp_id A.hom))
    fun _ f ↦ MorphismProperty.Over.Hom.ext
      ((Category.comp_id f.left).symm.trans (MorphismProperty.Over.w f))

/-- **The category of finite étale covers has a terminal object**, with no hypothesis on the base.

Stated as the class and not only as the witness above, because that is the form a
`CategoryTheory.Limits.HasTerminal` consumer asks for — `⊤_ (FiniteEtaleOver X)` is notation for
it — and because the Galois-category definition in `Mathlib/CategoryTheory/Galois/Basic.lean`,
whose namespace is not in this file's import closure and so cannot be cited by name here,
carries this field as an instance.

**It is an `instance` deliberately, and the choice was not free.** *Measured at `59f0ba2`, and
recorded rather than left live*: scanning the `instance` declarations under `Oka/AnalyticSpace/`
with block comments stripped, no statement among them mentioned the `Limits` namespace, a `Has…`
class or a `Preserves…` class.
`AlgebraicGeometry.LocallyRingedSpace.Hom.preservesFiniteLimits_pullbackModules`
(`Oka/AnalyticSpace/PullbackModulesStalk.lean`) is the nearest thing there and it is a `theorem`
about locally ringed spaces. So declaring this an instance changes what instance search can do in
a directory where nothing had yet asked for a limit, and the alternative — leaving
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isTerminalId` unbundled and making each caller
bundle it — was real. It was rejected because the terminal object here is canonical rather than a
choice, it being the base over itself; because `CategoryTheory.Limits.HasTerminal` is `Prop`-valued
and so carries no data a second instance could disagree with; and because the Galois-category
field it answers to is itself an instance field. -/
instance FiniteEtaleOver.hasTerminal (X : AnalyticSpace.{u}) :
    Limits.HasTerminal (FiniteEtaleOver.{u} X) :=
  (FiniteEtaleOver.isTerminalId.{u} X).hasTerminal

/-! ### The degree of a cover -/

/-- **The degree of a cover**: `ComplexAnalytic.AnalyticSpace.degree` of its structure map.

`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.degree_eq_of_iso` below is what makes this a
function of the isomorphism class and not only of the object, which is the property the word
"invariant" is doing work for and the one a degree-preserving functor would be stated against.

**Dot notation does reach this name through the `abbrev`, and that was measured rather than
assumed.** `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver` is an `abbrev` for
`CategoryTheory.MorphismProperty.Over`, so the expectation is that `A.degree` looks for a field of
the latter and fails; it does not — generalized field notation resolves against the head of the
type as the binder writes it, and `A.degree` elaborates. The statements below nevertheless spell
the name in full, because every declaration in this file carries an explicit universe annotation
and dot notation has nowhere to put one. -/
noncomputable def FiniteEtaleOver.degree {X : AnalyticSpace.{u}} (A : FiniteEtaleOver.{u} X) : ℕ :=
  AnalyticSpace.degree A.hom

/-- **Isomorphic covers have the same degree.**

An isomorphism `e` of covers is a triangle over `X`: `CategoryTheory.Over.w` says
`e.hom.left ≫ B.hom = A.hom`, and the two forgetful functors make `e.hom.left` an isomorphism of
analytic spaces, so `ComplexAnalytic.AnalyticSpace.degree_isIso_comp`
(`Oka/AnalyticSpace/Degree.lean`) applies. **Nothing finite étale is read**: the property appears
in the proof below only as the `_` of `CategoryTheory.MorphismProperty.Over.forget`, and neither
object's membership in it is ever opened — the degree of a cover is a fact about its structure map
and not about why that map is an object.

**The morphism is supplied by name rather than as a `_`, and that is a choice and not a
constraint.** `(e := e.hom.left)` says what the theorem is being applied at, which is worth the
two words in a proof whose whole content is that one application. It is not required:
`degree_isIso_comp _ _` compiles here — measured, by substituting that spelling into a copy of
this file and running `lake env lean` on the copy, which prints nothing.

**This paragraph said the `_` spelling was *forced*, and the failure it quoted belongs to the
draft below rather than to this proof.** With `rw [FiniteEtaleOver.degree,
FiniteEtaleOver.degree, ← hw]` in place of the `congrArg`, `exact degree_isIso_comp _ _` does
fail with *"failed to synthesize instance of type class `IsIso e.hom.left`"*, `haveI`
notwithstanding — both spellings were re-measured here, on copies of this file, and what changed
under the paragraph was the proof. **What distinguishes the two is not settled by that
measurement and nothing here claims it**; what is settled is that the constraint is the draft's
and the name here is a reader's convenience.

**No `rw` here names the definition, and the cost of the obvious one is a dump row.**
`rw [FiniteEtaleOver.degree, FiniteEtaleOver.degree, ← hw]` is the spelling this proof was written
in first, and naming a definition as a rewrite rule asks Lean to generate its equation lemma:
`scripts/DumpOkaDecls.lean` on that draft reports one extra row, the `.eq_1` of
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.degree`, measured rather than expected — and it is
one row however many proofs name it. (The cost is per definition and not per proof:
`Oka/AnalyticSpace/Degree.lean`'s `ComplexAnalytic.AnalyticSpace.degree_comp_of_bijective_base`
does write `rw [degree, degree]` and adds nothing,
`ComplexAnalytic.AnalyticSpace.degree.eq_1` having been generated by that file already.) What
replaces it is `congrArg` and `Eq.trans` at the definition's own unfolding, which go through
definitional unfolding and generate nothing — the same cure, for the same defect, that
`Oka/Analytification/RefineDatumToBase.lean` states as a rule for its own file, and the reason
`Δdump` for this branch is the number of declarations it adds and no more. **A `show` reaches the
same goal and is equally free of the equation lemma, and is not what is written**: Mathlib's
`linter.style.show` warns on a `show` that **changed** the goal and asks for `change` in its
place, and a `show` unfolding this definition changes it. It is in `linter.mathlibStandardSet`,
which `lakefile.toml` enables weakly, so `lake build --wfail` — which `.orchestra/validation.sh`
runs — turns the warning into a failure. **This sentence described the rule as one about the
*first* tactic of a proof**, which is not what the linter does: a copy of this file carrying that
`show` as the proof's **third** tactic draws the warning all the same, *"this tactic invocation
changed the goal"*, measured here. The conclusion was right and the rule under it was not. -/
theorem FiniteEtaleOver.degree_eq_of_iso {X : AnalyticSpace.{u}}
    {A B : FiniteEtaleOver.{u} X} (e : A ≅ B) :
    FiniteEtaleOver.degree.{u} A = FiniteEtaleOver.degree.{u} B := by
  haveI : IsIso e.hom.left :=
    ((MorphismProperty.Over.forget _ ⊤ X ⋙ CategoryTheory.Over.forget X).mapIso e).isIso_hom
  have hw : e.hom.left ≫ B.hom = A.hom :=
    CategoryTheory.Over.w ((MorphismProperty.Over.forget _ ⊤ X).map e.hom)
  exact (congrArg (fun f : A.left ⟶ X ↦ AnalyticSpace.degree f) hw).symm.trans
    (degree_isIso_comp (e := e.hom.left) _)

/-- **Two covers of different degrees are not isomorphic.**

The contrapositive of `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.degree_eq_of_iso`, stated as
`IsEmpty` of the type of isomorphisms because that is the shape
`OkaTest/FiniteEtaleOver.lean`'s separations are written in. **This is the first invariant on this
category that separates objects by a computation** rather than by refuting an `IsIso` of one
particular morphism, and the two are genuinely different: a `¬ IsIso f` says nothing about the
existence of some *other* isomorphism, and this says there is none. -/
theorem FiniteEtaleOver.isEmpty_iso_of_degree_ne {X : AnalyticSpace.{u}}
    {A B : FiniteEtaleOver.{u} X}
    (h : FiniteEtaleOver.degree.{u} A ≠ FiniteEtaleOver.degree.{u} B) : IsEmpty (A ≅ B) :=
  ⟨fun e ↦ h (FiniteEtaleOver.degree_eq_of_iso.{u} e)⟩

/-- **The base over itself has degree one**, over a non-empty base.

`ComplexAnalytic.AnalyticSpace.degree_id` read through the definition; the `[Nonempty X]` is that
theorem's and is not decorative, the degree of any morphism out of or into the empty space being
`0` by the `iSup` convention `ComplexAnalytic.AnalyticSpace.degree` documents. -/
theorem FiniteEtaleOver.degree_id (X : AnalyticSpace.{u}) [Nonempty X] :
    FiniteEtaleOver.degree.{u} (FiniteEtaleOver.id.{u} X) = 1 :=
  AnalyticSpace.degree_id X

/-- **The trivial `ι`-sheeted cover has degree `Nat.card ι`**, over a non-empty base.

`ComplexAnalytic.AnalyticSpace.degree_sigmaFold` read through the definition. `[Finite ι]` is
asked here because `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.trivial` asks it, not because
the degree computation needs it — that theorem holds at every `ι`, with both sides `0` when `ι` is
infinite. -/
theorem FiniteEtaleOver.degree_trivial (ι : Type u) [Finite ι] (X : AnalyticSpace.{u})
    [Nonempty X] :
    FiniteEtaleOver.degree.{u} (FiniteEtaleOver.trivial.{u} ι X) = Nat.card ι :=
  AnalyticSpace.degree_sigmaFold ι X

/-- **The trivial `ι`-sheeted cover is not the base over itself unless `ι` has one point.**

The separation `OkaTest/FiniteEtaleOver.lean` records as missing: it says that separating the
trivial cover from the identity *"needs a statement that `X ⨿ X ⟶ X` is not an isomorphism, which
this repository does not have"*. It does not need one. The degree is `Nat.card ι` on one side and
`1` on the other, and
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isEmpty_iso_of_degree_ne` closes it — no `¬ IsIso`
of any morphism is proved on the way, which is exactly why the route the absence was priced at is
not the route taken.

`Nat.card ι ≠ 1` is the honest hypothesis and is weaker than `1 < Nat.card ι`: it also covers the
empty `ι`, where the cover is the empty space and the degree is `0`. **And it is sharp** —
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.nonempty_iso_trivial_id_iff` at the end of this
file is this statement and its converse together. -/
theorem FiniteEtaleOver.isEmpty_iso_trivial_id (ι : Type u) [Finite ι] (X : AnalyticSpace.{u})
    [Nonempty X] (h : Nat.card ι ≠ 1) :
    IsEmpty (FiniteEtaleOver.trivial.{u} ι X ≅ FiniteEtaleOver.id.{u} X) :=
  FiniteEtaleOver.isEmpty_iso_of_degree_ne.{u} <| by
    rw [FiniteEtaleOver.degree_trivial, FiniteEtaleOver.degree_id]
    exact h

/-- **Two trivial covers of a non-empty base are isomorphic only if their index types have the same
cardinality.**

So the category over a non-empty base has an object of every degree in the range of `Nat.card` and
they are pairwise non-isomorphic — at `ι = ULift (Fin n)` that is one class for every `n`, which
is what turns *"at least two isomorphism classes"* into *"infinitely many"*.
`OkaTest/FiniteEtaleOver.lean` instantiates it.

Stated as an implication from an isomorphism rather than as an `IsEmpty`, because the two index
types are the data a caller has and the cardinality is what it wants back; the `IsEmpty` form is
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isEmpty_iso_of_degree_ne` at the same two
objects. -/
theorem FiniteEtaleOver.card_eq_of_iso_trivial {ι κ : Type u} [Finite ι] [Finite κ]
    {X : AnalyticSpace.{u}} [Nonempty X]
    (e : FiniteEtaleOver.trivial.{u} ι X ≅ FiniteEtaleOver.trivial.{u} κ X) :
    Nat.card ι = Nat.card κ := by
  rw [← FiniteEtaleOver.degree_trivial ι X, ← FiniteEtaleOver.degree_trivial κ X]
  exact FiniteEtaleOver.degree_eq_of_iso.{u} e

/-! ### Connectedness of the total space, which the degree does not see -/

/-- **Isomorphic covers have homeomorphic total spaces, so preconnectedness passes between
them.**

The same triangle `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.degree_eq_of_iso` reads, and the
same first step: the two forgetful functors carry `e` to an isomorphism of analytic spaces whose
morphism is `e.hom.left`, so it is surjective on points and
`ComplexAnalytic.AnalyticSpace.preconnectedSpace_of_surjective_base`
(`Oka/AnalyticSpace/Basic.lean`) applies. **The triangle itself is not used here**, unlike in the
degree statement — nothing about the structure maps is read, only that the total spaces are
isomorphic, so this would hold in `CategoryTheory.Over X` with no property at all.

**Stated in one direction and used in both.** An isomorphism has a symm, so a caller wanting the
other direction applies this at `e.symm`;
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isEmpty_iso_of_preconnectedSpace` below is the
contrapositive and is the form the separations are written in. -/
theorem FiniteEtaleOver.preconnectedSpace_of_iso {X : AnalyticSpace.{u}}
    {A B : FiniteEtaleOver.{u} X} (e : A ≅ B) [PreconnectedSpace A.left] :
    PreconnectedSpace B.left := by
  haveI : IsIso e.hom.left :=
    ((MorphismProperty.Over.forget _ ⊤ X ⋙ CategoryTheory.Over.forget X).mapIso e).isIso_hom
  exact preconnectedSpace_of_surjective_base e.hom.left (surjective_base_of_isIso _)

/-- **A cover with a preconnected total space is not isomorphic to one without.**

The contrapositive of `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.preconnectedSpace_of_iso`, in
the `IsEmpty` shape `OkaTest/FiniteEtaleOver.lean`'s separations are written in. **This is the
second invariant on this category**, and the first that is not a number:
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isEmpty_iso_of_degree_ne` separates by a
computation and is blind to any two objects of equal degree, which the punctured line supplies at
degree `2`.

**The hypothesis is instance-implicit on `A` and explicit on `B`**, which is not a symmetry the
statement has to break and is where the two sides are actually used: the connected side is the one
a caller has an instance for — `ComplexAnalytic.preconnectedSpace_restrict_punctured` is one — and
the disconnected side is the one a caller has a *theorem* for, since `¬ PreconnectedSpace` is not
a class. -/
theorem FiniteEtaleOver.isEmpty_iso_of_preconnectedSpace {X : AnalyticSpace.{u}}
    {A B : FiniteEtaleOver.{u} X} [PreconnectedSpace A.left] (h : ¬ PreconnectedSpace B.left) :
    IsEmpty (A ≅ B) :=
  ⟨fun e ↦ h (FiniteEtaleOver.preconnectedSpace_of_iso.{u} e)⟩

/-- **The total space of a trivial cover with two distinct sheets is not preconnected.**

`ComplexAnalytic.AnalyticSpace.not_preconnectedSpace_sigma`
(`Oka/AnalyticSpace/SigmaFiniteEtale.lean`) at the constant family, whose members are all `X`, so
the two points it asks for are both `Classical.arbitrary X` and `[Nonempty X]` supplies them.
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.trivial`'s total space is that disjoint union by
definition, and no lemma is needed to say so.

**`i ≠ j` and not `1 < Nat.card ι`.** The two are equivalent at a finite `ι`, and the numeral
version is what a degree statement would be phrased in — but the proof consumes two indices, and
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.degree_trivial` is the place where this file turns
an index type into a number. Asking for the indices keeps the cardinality arithmetic out of a
statement that does no counting. -/
theorem FiniteEtaleOver.not_preconnectedSpace_trivial (ι : Type u) [Finite ι]
    (X : AnalyticSpace.{u}) [Nonempty X] {i j : ι} (hij : i ≠ j) :
    ¬ PreconnectedSpace (FiniteEtaleOver.trivial.{u} ι X).left :=
  not_preconnectedSpace_sigma (fun _ : ι ↦ X) hij (Classical.arbitrary X) (Classical.arbitrary X)

/-- **A cover with a preconnected total space is not a trivial cover with two distinct sheets.**

The two statements above composed, and **the separation
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.degree` cannot make**: at the punctured line
`OkaTest/FiniteEtaleOver.lean`'s `z ↦ z²` and
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.trivial` at a two-element index type both have
degree `2` — `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.degree_trivial` and that file's
`degree_sqOver` — so `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isEmpty_iso_of_degree_ne` says
nothing about the pair. `OkaTest/FiniteEtaleOver.lean` instantiates this at exactly that pair.

**Nothing here is finite étale and nothing here is analytic.** Every step is topology — a clopen
image, a continuous surjection, and `isClopen_iff` — which is why the statement holds of any two
objects of `CategoryTheory.Over X` of these shapes and asks the property for nothing but the right
to say "cover".

**What it does not say.** A trivial cover with `Nat.card ι ≤ 1` is not covered, and correctly so:
at one sheet the fold map is an isomorphism
(`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.trivialIsoId`) and the total space is `X` itself,
which may perfectly well be preconnected. The hypothesis is two *distinct* indices and there is no
weaker one. -/
theorem FiniteEtaleOver.isEmpty_iso_trivial_of_preconnectedSpace {X : AnalyticSpace.{u}}
    (A : FiniteEtaleOver.{u} X) [PreconnectedSpace A.left] (ι : Type u) [Finite ι] [Nonempty X]
    {i j : ι} (hij : i ≠ j) :
    IsEmpty (A ≅ FiniteEtaleOver.trivial.{u} ι X) :=
  FiniteEtaleOver.isEmpty_iso_of_preconnectedSpace.{u}
    (FiniteEtaleOver.not_preconnectedSpace_trivial.{u} ι X hij)

/-! ### The restriction over `⊤` -/

/-- **A morphism whose restriction over `⊤` is finite étale is finite étale.**

`ComplexAnalytic.AnalyticSpace.restrictHom f V` has source `X|f⁻¹V` and target `Y|V`, so it is a
morphism between two *other* spaces and a property of it is not on its face a property of `f`. At
`V = ⊤` the two inclusions are isomorphisms
(`ComplexAnalytic.AnalyticSpace.isIso_ofRestrict_of_eq_univ`) and
`ComplexAnalytic.AnalyticSpace.liftTop_comp_restrictHom_top` exhibits `f` as the conjugate, so the
property transfers by `ComplexAnalytic.AnalyticSpace.isFiniteEtale`'s `RespectsIso` and
`IsMultiplicative` instances above. **Nothing is proved about finite étale morphisms here**: the
content is entirely in `Oka/AnalyticSpace/OpenSubspace.lean`, and this file supplies only the two
instances that make the conjugation a transfer.

**This is what makes a `V` hypothesis refutable rather than merely unproved.** A theorem of the
form *"restricted over `V` the morphism is finite étale"* says nothing on its own about whether
`V` can be `⊤`; with this, a morphism that is not finite étale gives
`¬ IsFiniteEtale (restrictHom f ⊤)` by contraposition, so such a theorem at `V = ⊤` would be
false. `OkaTest/StandardEtaleNotFinite.lean`'s `## What is not checked here` recorded the absence of
exactly this step — **at `IsFinite`, not here**; see the paragraph below.

**Nothing is said about `ComplexAnalytic.AnalyticSpace.IsLocalIso`.** The same conjugation would
run and no prose site asks for it, so it is declined rather than overlooked.

**The finiteness half of this is `ComplexAnalytic.AnalyticSpace.isFinite_of_restrictHom_top`**, in
the file that owns the vocabulary, and it is the one two `## What is not here` bullets elsewhere
were actually about — both name a *finiteness* theorem. It is not derived from this one and does
not derive it: `IsFinite` is not a `CategoryTheory.MorphismProperty` here, so it runs through
`ComplexAnalytic.AnalyticSpace.isFinite_comp` twice instead of through `RespectsIso`.

**What is not here is the converse.** `IsFiniteEtale f → IsFiniteEtale (restrictHom f ⊤)` follows
from the same conjugation read the other way and is not stated, because nothing here asks for it;
it is the same three lines. Nor is anything said about `restrictHom f V` at a proper `V` — the whole
argument is that `⊤` makes the inclusions invertible, and at a proper `V` neither is. -/
theorem isFiniteEtale_of_restrictHom_top {A B : AnalyticSpace.{u}} (f : A ⟶ B)
    (hfe : IsFiniteEtale (restrictHom f (⊤ : B.Opens))) : IsFiniteEtale f := by
  set U : A.Opens := (TopologicalSpace.Opens.map f.toLRSHom.base).obj (⊤ : B.Opens) with hUdef
  have h : (U : Set A) = Set.univ := rfl
  have hB : ((⊤ : B.Opens) : Set B) = Set.univ := rfl
  haveI : IsIso (B.ofRestrict (⊤ : B.Opens)) := isIso_ofRestrict_of_eq_univ B ⊤ hB
  haveI : IsIso (liftTop A U h) := isIso_liftTop A U h
  have hp : isFiniteEtale.{u} (liftTop A U h ≫ restrictHom f ⊤ ≫ B.ofRestrict ⊤) :=
    (isFiniteEtale.{u}).comp_mem _ _ (isFiniteEtale_of_isIso _)
      ((isFiniteEtale.{u}).comp_mem _ _ hfe (isFiniteEtale_of_isIso _))
  rwa [liftTop_comp_restrictHom_top] at hp

/-! ### The fibre functor -/

/-- **The fibre of a cover over a point of the base**, as a type.

Spelled as the preimage set and not as the subtype `{a // A.hom.toLRSHom.base a = x}`. The two are
definitionally the same type — membership in `{x}` *is* that equation — and the preimage is the
spelling `Oka/AnalyticSpace/Degree.lean` states every fibre count in, which is what makes
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.card_fiber` below the symmetric form of a theorem
there rather than a transport across an equivalence.

**Nothing finite étale is read here.** The definition mentions the structure map and nothing else,
so it would make sense at every object of `CategoryTheory.MorphismProperty.Over` whatever the
property is; what the property buys is the instance below and not the type. -/
def FiniteEtaleOver.fiber {X : AnalyticSpace.{u}} (x : X) (A : FiniteEtaleOver.{u} X) : Type u :=
  (A.hom.toLRSHom.base ⁻¹' {x} : Set A.left)

/-- **The fibre of a cover is finite, and nothing has to be assumed for that.**

Not a separation axiom, not connectedness, nothing about the base and nothing about the point.
`finite_fiber` is a *field* of `ComplexAnalytic.AnalyticSpace.IsFinite`
(`Oka/AnalyticSpace/Finite.lean`), `ComplexAnalytic.AnalyticSpace.IsFiniteEtale` carries it through
`ComplexAnalytic.AnalyticSpace.IsFiniteEtale.isFinite`, and an object of this category carries the
class in its `prop` field, so this is three projections and no proof.

**This corrects the pricing that stood in this file's `## What is not here` and is why the functor
below was not built earlier.** That bullet said the fibre of a finite étale morphism is finite *by*
`ComplexAnalytic.AnalyticSpace.card_fiber_eq_of_isFiniteEtale`, which asks `[T2Space]` of the
source. It is not: that theorem says two fibres have the **same** `Nat.card`, and `Nat.card` of an
infinite type is `0`, so it is satisfied by a morphism all of whose fibres are infinite and cannot
be where finiteness comes from — its own docstring says *"it does **not** say what that size is"*.
`[T2Space]` is the price of **constancy** of the count, through
`ComplexAnalytic.AnalyticSpace.nonempty_homeomorph_fiber_of_isFiniteEtale` and the covering-space
theory behind it, and constancy is not what a `FintypeCat`-valued functor asks of a fibre. -/
instance FiniteEtaleOver.finite_fiber {X : AnalyticSpace.{u}} (x : X) (A : FiniteEtaleOver.{u} X) :
    Finite (FiniteEtaleOver.fiber.{u} x A) :=
  (A.prop : IsFiniteEtale A.hom).isFinite.finite_fiber x

/-- **A morphism of covers carries the fibre over `x` into the fibre over `x`.**

The whole content is `CategoryTheory.MorphismProperty.Over.w f` — the triangle
`f.left ≫ B.hom = A.hom` — read at one point: if `a` lies over `x` for `A` then `f.left a` lies
over `x` for `B`, because the two structure maps agree along `f`.

**No property of `f` is used and none is available**, the category's second `⊤` being exactly the
statement that a morphism of covers carries no condition; the base map of a composite is the
composite of the base maps by `rfl`, which is what makes the two functor laws below `rfl` too. -/
def FiniteEtaleOver.fiberMap {X : AnalyticSpace.{u}} (x : X) {A B : FiniteEtaleOver.{u} X}
    (f : A ⟶ B) (a : FiniteEtaleOver.fiber.{u} x A) : FiniteEtaleOver.fiber.{u} x B :=
  ⟨f.left.toLRSHom.base a.1, by
    have hw : f.left ≫ B.hom = A.hom := MorphismProperty.Over.w f
    have h := congrArg (fun g ↦ (g.toLRSHom.base : A.left → X) a.1) hw
    exact h.trans a.2⟩

/-- **The fibre functor at a point of the base**, into `Type u`.

**The first functor out of `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver` declared in this
repository** — `CategoryTheory.MorphismProperty.Over.forget`, which the proofs above compose with,
is Mathlib's — and the first invariant here that is read on morphisms as well as on objects:
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.degree` is a number attached to an object and
preconnectedness of the total space is a proposition about one, while this carries every morphism
of covers to a map of finite sets.

**Both functor laws are `rfl`.** The underlying map of an identity of the comma category is the
identity and the underlying map of a composite is the composite, so there is nothing to prove and
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fiberMap` is definitionally functorial.

**`TypeCat.ofHom` is not decoration.** A morphism of `Type u` in this Mathlib is a one-field
structure and not a function — `CategoryTheory.types` has `Hom := TypeCat.Hom` — so a bare
`fun a ↦ …` does not elaborate against `⟶` and the `map` field has to wrap it. -/
def FiniteEtaleOver.fiberFunctor {X : AnalyticSpace.{u}} (x : X) :
    FiniteEtaleOver.{u} X ⥤ Type u where
  obj A := FiniteEtaleOver.fiber.{u} x A
  map f := TypeCat.ofHom (FiniteEtaleOver.fiberMap.{u} x f)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- **The fibre functor into `FintypeCat`**, which is the shape a Galois category asks for.

The same functor as
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fiberFunctor` with its values bundled with the
finiteness above; `Mathlib/CategoryTheory/Galois/Basic.lean` — whose namespace is not in this
file's import closure and so cannot be cited by name here — asks for a functor into
`FintypeCat`, and this is one.

**It is computable, which is worth recording because the obvious expectation is otherwise.**
`FintypeCat.of` takes `[Finite X]` in this Mathlib and not `[Fintype X]`, so the instance above is
what it wants and no `Fintype.ofFinite` and no `noncomputable` appears.
**`Mathlib.CategoryTheory.FintypeCat` is the one import this file gains for it, and it costs one
module**: the transitive closure of this file was 3463 modules before and is 3464 after, the new
module being that one and nothing it depends on.

**What this does not make is a Galois category.** The axioms need base change of `isFiniteEtale`
over an arbitrary cospan and nothing carries the class across one; see `## What is not here`,
whose bullet on this now says which cospans it *is* carried across and what each buys.
**This sentence added *and `CategoryTheory.Limits.HasPullbacks ComplexAnalytic.AnalyticSpace` does
not synthesise* until 2026-09-08**, when `Oka/AnalyticSpace/PullbackReduction.lean` made it
synthesise; the axioms still are not met, and the reason is now only the class and no longer also
the limit. **That sentence said `across that one` while the
bullet named a single family of cospans, the pullback along the inclusion of an open subspace, and
was rewritten on 2026-09-07 when `Oka/AnalyticSpace/FiniteEtaleBaseChange.lean` gave the bullet a
second.** **This sentence said that no
`CategoryTheory.Limits.HasPullback` instance for analytic spaces is available here at all**, and
`Oka/AnalyticSpace/PullbackOpen.lean` falsified it. **Base change is not the only axiom they need,
and the reader who meets this sentence first should not infer that it is** — the terminal-object
axiom is separately in hand, at
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.preservesLimitsOfShape_pempty_fintypeFiberFunctor`
for this functor. -/
def FiniteEtaleOver.fintypeFiberFunctor {X : AnalyticSpace.{u}} (x : X) :
    FiniteEtaleOver.{u} X ⥤ FintypeCat.{u} where
  obj A := FintypeCat.of (FiniteEtaleOver.fiber.{u} x A)
  map f := FintypeCat.homMk (FiniteEtaleOver.fiberMap.{u} x f)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- **Isomorphic covers have equinumerous fibres**, by an explicit equivalence.

`CategoryTheory.Functor.mapIso` at the fibre functor, read through `CategoryTheory.Iso.toEquiv`.
This is the equivalence behind the count in
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.degree_eq_of_iso`, which reaches the same
conclusion for `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.degree` through
`ComplexAnalytic.AnalyticSpace.degree_isIso_comp` and without a fibre in sight; neither is derived
from the other and this one asks nothing of the total spaces. -/
def FiniteEtaleOver.fiberEquivOfIso {X : AnalyticSpace.{u}} (x : X) {A B : FiniteEtaleOver.{u} X}
    (e : A ≅ B) : FiniteEtaleOver.fiber.{u} x A ≃ FiniteEtaleOver.fiber.{u} x B :=
  ((FiniteEtaleOver.fiberFunctor.{u} x).mapIso e).toEquiv

/-- **The fibre functor computes the degree**, over a preconnected base and a Hausdorff total
space.

`ComplexAnalytic.AnalyticSpace.degree_eq_card_fiber` (`Oka/AnalyticSpace/Degree.lean`) read at the
structure map of an object, which is why
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fiber` is spelled as a preimage: the two sides are
the same type on the nose and the proof is one `Eq.symm`.

**This is where `[T2Space]` genuinely enters**, and the contrast with
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.finite_fiber` above is the point: the fibre is
finite for free, and it is the statement that its size does not depend on the point that costs a
separation axiom on the source and preconnectedness of the base.

**The two `inferInstanceAs` lines are the comma category's and not this statement's.** In the type
of an object's structure map the total space appears through `CategoryTheory.Functor.id` and the
base through `CategoryTheory.Functor.fromPUnit`, applied to the two components of the object; both
are the space itself by `rfl` but **not reducibly so**, and instance search works up to reducible
unfolding, so the `[T2Space]` and `[PreconnectedSpace]` written above are not the instances
`ComplexAnalytic.AnalyticSpace.degree_eq_card_fiber` asks for until they are restated. That is
what the two `haveI`s do and there is no mathematical content in either. -/
theorem FiniteEtaleOver.card_fiber {X : AnalyticSpace.{u}} (A : FiniteEtaleOver.{u} X)
    [T2Space A.left] [PreconnectedSpace X] (x : X) :
    Nat.card (FiniteEtaleOver.fiber.{u} x A) = A.degree :=
  haveI : IsFiniteEtale A.hom := A.prop
  haveI : T2Space (((𝟭 AnalyticSpace.{u}).obj A.left : AnalyticSpace.{u}) : Type u) :=
    inferInstanceAs (T2Space (A.left : Type u))
  haveI : PreconnectedSpace
      (((Functor.fromPUnit.{0} X).obj A.right : AnalyticSpace.{u}) : Type u) :=
    inferInstanceAs (PreconnectedSpace (X : Type u))
  (degree_eq_card_fiber A.hom x).symm

/-- **The fibre of the base over itself is a point.**

Stated as `Unique` rather than as a cardinality, so that it is the fibre functor's value and not a
count of it; `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.degree_id` is the same fact read
through `Nat.card`, and it needs `[Nonempty X]` where this needs nothing — the point `x` is the
one that is there. -/
instance FiniteEtaleOver.uniqueFiberId {X : AnalyticSpace.{u}} (x : X) :
    Unique (FiniteEtaleOver.fiber.{u} x (FiniteEtaleOver.id.{u} X)) := by
  change Unique (((𝟙 X : X ⟶ X).toLRSHom.base : X → X) ⁻¹' {x} : Set X)
  have h : ((𝟙 X : X ⟶ X).toLRSHom.base : X → X) = _root_.id := rfl
  rw [h, Set.preimage_id]
  infer_instance

/-- **The fibre of the trivial `ι`-sheeted cover is `ι`**, as an equivalence.

`AlgebraicGeometry.LocallyRingedSpace.fiberSigmaDescEquiv` presents the fibre of a descent map as
`Σ i, (fibre of the i-th piece)` and every piece here is the identity, whose fibre is a point, so
`Equiv.sigmaUnique` collapses the sum. That is exactly the proof of
`ComplexAnalytic.AnalyticSpace.card_fiber_sigmaFold` (`Oka/AnalyticSpace/SigmaFiniteEtale.lean`)
with the counting removed — **the equivalence is what that proof already had**, and that file's
`## The fibre is an equivalence and not a cardinality` section says so of itself.

`[Finite ι]` is here because `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.trivial` asks it in
order to be an object, and for no reason of this statement's own. -/
noncomputable def FiniteEtaleOver.fiberTrivialEquiv (ι : Type u) [Finite ι]
    (X : AnalyticSpace.{u}) (x : X) :
    FiniteEtaleOver.fiber.{u} x (FiniteEtaleOver.trivial.{u} ι X) ≃ ι :=
  haveI hu : ∀ _ : ι, Unique (((𝟙 X : X ⟶ X).toLRSHom.base ⁻¹' {x} : Set X)) := by
    intro _
    have h : ((𝟙 X : X ⟶ X).toLRSHom.base : X → X) = _root_.id := rfl
    rw [h, Set.preimage_id]
    infer_instance
  (AlgebraicGeometry.LocallyRingedSpace.fiberSigmaDescEquiv (fun _ : ι ↦ X.toLocallyRingedSpace)
      (fun _ ↦ (𝟙 X : X ⟶ X).toLRSHom) x).symm.trans (@Equiv.sigmaUnique ι _ hu)

/-! ### The trivial cover at one sheet, where it is the base -/

/-- **The trivial cover at one sheet is the base over itself.**

The isomorphism the docstring of `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.trivial` said was
not stated. It is `ComplexAnalytic.AnalyticSpace.sigmaFoldIso`
(`Oka/AnalyticSpace/SigmaFiniteEtale.lean`) put over `X`: a morphism of this category is a
morphism of analytic spaces commuting with the two structure maps and nothing more — `Q` is `⊤`,
as the docstring above says — so the triangle is all there is to check, and it is
`Category.comp_id` at the identity structure map of
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.id`.

**The triangle is a term and not a `simp`, for the reason
`ComplexAnalytic.AnalyticSpace.isIso_hom_of_iso_id` gives above.** The goal displays as
`(sigmaFoldIso ι X).hom ≫ (FiniteEtaleOver.id X).hom = (FiniteEtaleOver.trivial ι X).hom`; both
`def`s have to be unfolded to see a `𝟙 X` and a `sigmaFold ι X`, which `rw` and `simp` do not do
at `instances` transparency, and `Category.comp_id _` is the same step at default transparency in
one line.

**`[Nonempty ι]` and `[Subsingleton ι]` and not `Nat.card ι = 1`**, which
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.nonempty_iso_trivial_id_iff` below converts for a
caller holding the numeral. The instances are what the construction consumes; a hypothesis it
would have to destructure is the wrong shape for a `def`, whose value would then depend on a
proof. -/
noncomputable def FiniteEtaleOver.trivialIsoId (ι : Type u) [Finite ι] [Nonempty ι]
    [Subsingleton ι] (X : AnalyticSpace.{u}) :
    FiniteEtaleOver.trivial.{u} ι X ≅ FiniteEtaleOver.id.{u} X :=
  MorphismProperty.Over.isoMk (sigmaFoldIso ι X) (Category.comp_id _)

/-- **So over a non-empty base the trivial cover is the base over itself exactly when its index
type has one point.**

The two directions are the two halves this file already had, joined:
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isEmpty_iso_trivial_id` is the forward one and is
proved through the degree, and
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.trivialIsoId` is the backward one and is proved
through the universal property of the disjoint union. **Neither direction is the other read
backwards**, and the degree cannot supply the backward one: it separates isomorphism classes and
never produces an isomorphism.

`[Nonempty X]` is where it is needed and not decorative — it is what
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.degree_id` and
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.degree_trivial` ask for, the degree of a morphism
out of or into the empty space being `0` whatever the index type is. The backward direction needs
nothing of `X`.

**This is a classification of one isomorphism class and not of the category.** It says which
trivial covers are the identity; it says nothing about a non-trivial cover of degree `1`, and
`## What is not here` still records that no invariant here separates two *connected* covers. -/
theorem FiniteEtaleOver.nonempty_iso_trivial_id_iff (ι : Type u) [Finite ι]
    (X : AnalyticSpace.{u}) [Nonempty X] :
    Nonempty (FiniteEtaleOver.trivial.{u} ι X ≅ FiniteEtaleOver.id.{u} X) ↔ Nat.card ι = 1 := by
  refine ⟨fun he ↦ by_contra fun h ↦
    not_nonempty_iff.mpr (FiniteEtaleOver.isEmpty_iso_trivial_id ι X h) he, fun h ↦ ?_⟩
  obtain ⟨j, hj⟩ := Nat.card_eq_one_iff_exists.mp h
  haveI : Nonempty ι := ⟨j⟩
  haveI : Subsingleton ι := ⟨fun a b ↦ (hj a).trans (hj b).symm⟩
  exact ⟨FiniteEtaleOver.trivialIsoId ι X⟩

/-! ### Unique lifting, and what the fibre functor's action determines -/

/-- **Two morphisms of covers that agree at one point of a preconnected source agree on points.**

Hatcher's Proposition 1.34 — `IsCoveringMap.eq_of_comp_eq` — at the covering map
`ComplexAnalytic.AnalyticSpace.isCoveringMap_base_of_isFiniteEtale` gives of the target's
structure map. The hypothesis that theorem asks for, that the two maps agree after composing with
the covering map, is `CategoryTheory.MorphismProperty.Over.w` read at each point: both composites
are the source's own structure map.

**Neither hypothesis is free and they come from different places.** `[PreconnectedSpace A.left]`
is what the lifting argument consumes and is a hypothesis on the *source*; `[T2Space B.left]` is
what `ComplexAnalytic.AnalyticSpace.isCoveringMap_base_of_isFiniteEtale` asks in order to be a
covering map at all, and `Oka/AnalyticSpace/CoveringMap.lean` says in terms that it is Mathlib's
hypothesis and not free here, this development imposing no separation axiom on an analytic space.

**The conclusion is an equality of maps on points and not of morphisms**, which is the whole of
what separates this from faithfulness of the fibre functor; see `## What is not here`.

The `haveI` restating `[T2Space]` carries no content: in the type of an object's structure map the
total space appears through `CategoryTheory.Functor.id`, which is the space by `rfl` but not
reducibly so, so instance search does not reach the hypothesis written above. That is the same
seam `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.card_fiber` documents. -/
theorem FiniteEtaleOver.base_eq_of_apply_eq {X : AnalyticSpace.{u}} {A B : FiniteEtaleOver.{u} X}
    [PreconnectedSpace (A.left : Type u)] [T2Space (B.left : Type u)] (f g : A ⟶ B)
    (a : (A.left : Type u)) (h : f.left.toLRSHom.base a = g.left.toLRSHom.base a) :
    (f.left.toLRSHom.base : A.left → B.left) = g.left.toLRSHom.base := by
  haveI : IsFiniteEtale B.hom := B.prop
  haveI : T2Space (((𝟭 AnalyticSpace.{u}).obj B.left : AnalyticSpace.{u}) : Type u) :=
    inferInstanceAs (T2Space (B.left : Type u))
  refine (isCoveringMap_base_of_isFiniteEtale.{u} B.hom).eq_of_comp_eq
    f.left.toLRSHom.base.hom.continuous g.left.toLRSHom.base.hom.continuous ?_ a h
  funext b
  exact (congrArg (fun k ↦ (k.toLRSHom.base : A.left → X) b) (MorphismProperty.Over.w f)).trans
    (congrArg (fun k ↦ (k.toLRSHom.base : A.left → X) b) (MorphismProperty.Over.w g)).symm

/-- **The same, from a point of a fibre.**

`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fiber` is a set of the total space, so a point of it
is a point of the source with a proof attached, and
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fiberMap` is the base map on the underlying point by
definition. So the hypothesis here is the one above with a `Subtype.val` in front of it, and the
statement is worth having only because it is the shape the fibre functor produces. -/
theorem FiniteEtaleOver.base_eq_of_fiberMap_eq {X : AnalyticSpace.{u}}
    {A B : FiniteEtaleOver.{u} X} [PreconnectedSpace (A.left : Type u)]
    [T2Space (B.left : Type u)] {x : X} (f g : A ⟶ B) (a : FiniteEtaleOver.fiber.{u} x A)
    (h : FiniteEtaleOver.fiberMap.{u} x f a = FiniteEtaleOver.fiberMap.{u} x g a) :
    (f.left.toLRSHom.base : A.left → B.left) = g.left.toLRSHom.base :=
  FiniteEtaleOver.base_eq_of_apply_eq.{u} f g a.1 (congrArg Subtype.val h)

/-- **What the fibre functor's action determines is the base map**: two morphisms of covers whose
images under `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fiberFunctor` at a point are equal have
the same map on points, provided the fibre there has a point.

**A fibre is asked for and is not free.** The equality of maps of fibres says nothing whatever when
the fibre is empty, and a cover with an empty fibre over a point exists here — the trivial cover at
an empty index type. So the point `a` is a hypothesis and not an artefact of the proof.

**The `congrArg` lands in the functor's value and is carried across by a defeq check**, which is
worth a sentence because one obvious tactic will not do it. `congrArg (fun k ↦ TypeCat.Hom.hom k a)`
produces an equation in `(fiberFunctor x).obj B`, and reaching
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fiber x B` from there is definitional: an argument
position performs that check, so the term needs no `by` at all, and `exact` performs it too.
**`simpa using` the same term fails**, reporting the two sides as equalities in different types.

**Pointwise and not at the map.** `congrArg TypeCat.Hom.hom h` — the same step without the point —
does *not* ascribe to an equation between the two
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fiberMap`s, so a proof that goes through the map and
applies it afterwards does not elaborate. All four spellings were run before this one was
chosen. -/
theorem FiniteEtaleOver.base_eq_of_fiberFunctor_map_eq {X : AnalyticSpace.{u}}
    {A B : FiniteEtaleOver.{u} X} [PreconnectedSpace (A.left : Type u)]
    [T2Space (B.left : Type u)] {x : X} (f g : A ⟶ B) (a : FiniteEtaleOver.fiber.{u} x A)
    (h : (FiniteEtaleOver.fiberFunctor.{u} x).map f = (FiniteEtaleOver.fiberFunctor.{u} x).map g) :
    (f.left.toLRSHom.base : A.left → B.left) = g.left.toLRSHom.base :=
  FiniteEtaleOver.base_eq_of_fiberMap_eq.{u} f g a (congrArg (fun k ↦ TypeCat.Hom.hom k a) h)

/-- **An endomorphism of a connected cover that fixes a point is the identity on points.**

The theorem above at `g = 𝟙 A`, whose base map is `id` by `rfl` — the same `rfl` that
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.uniqueFiberId` and
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fiberTrivialEquiv` are built on.

**This is the rigidity a deck transformation has**, at the one place this category can state it:
the automorphisms of a connected cover act freely on each fibre, so far as points are concerned.
What it is not is a statement that `f` **is** the identity morphism, for the reason the theorem
above stops where it does. -/
theorem FiniteEtaleOver.base_eq_id_of_apply_eq {X : AnalyticSpace.{u}} {A : FiniteEtaleOver.{u} X}
    [PreconnectedSpace (A.left : Type u)] [T2Space (A.left : Type u)] (f : A ⟶ A)
    (a : (A.left : Type u)) (h : f.left.toLRSHom.base a = a) :
    (f.left.toLRSHom.base : A.left → A.left) = _root_.id :=
  FiniteEtaleOver.base_eq_of_apply_eq.{u} f (𝟙 A) a h

/-- **Two morphisms of covers with the same base map are equal.**

This is what separates the theorems above from faithfulness, and it asks for **neither**
`[PreconnectedSpace]` **nor** `[T2Space]`: those two hypotheses buy the *base maps* being equal,
and once they are, nothing further is needed. The only thing consumed here is that the target is
a cover — `ComplexAnalytic.AnalyticSpace.IsLocalIso.isIso_stalkMap`, which `B` carries in its
`prop` field.

**Why the structure sheaves are then forced.**
`AlgebraicGeometry.LocallyRingedSpace.hom_ext_of_comp_eq` is the general statement: a morphism
whose stalk maps are all isomorphisms cancels on the right against two morphisms with the same
base map. Here it is applied at `B.hom`, whose stalk maps are
isomorphisms because `B` is finite étale, and the composites agree because both are `A`'s own
structure map — `CategoryTheory.MorphismProperty.Over.w` at `f` and at `g`. So a morphism of
covers has no freedom in its map of structure sheaves beyond its map on points, and the
`## What is not here` bullet that said it might is retired.

**The two reductions above the general lemma cost one term each.**
`CategoryTheory.MorphismProperty.Over.Hom.ext` reduces an equality of morphisms of covers to
their `.left`s, and `ComplexAnalytic.AnalyticSpace.forgetToLocallyRingedSpace` is faithful, which
reduces an equality of morphisms of analytic spaces to the underlying locally ringed spaces —
the `ℂ`-linearity field is a `Prop` and carries nothing.

**The hypothesis is an equality of functions and the general lemma wants one of bundled maps**,
which is the `ext` in the proof and is the only step with no content. -/
theorem FiniteEtaleOver.hom_ext_of_base_eq {X : AnalyticSpace.{u}} {A B : FiniteEtaleOver.{u} X}
    (f g : A ⟶ B)
    (h : (f.left.toLRSHom.base : A.left → B.left) = g.left.toLRSHom.base) : f = g := by
  haveI : IsFiniteEtale B.hom := B.prop
  have hb : f.left.toLRSHom.base = g.left.toLRSHom.base := by
    ext a
    exact congrFun h a
  exact MorphismProperty.Over.Hom.ext (forgetToLocallyRingedSpace.map_injective
    (AlgebraicGeometry.LocallyRingedSpace.hom_ext_of_comp_eq B.hom.toLRSHom _ _ hb
      ((congrArg Hom.toLRSHom (MorphismProperty.Over.w f)).trans
        (congrArg Hom.toLRSHom (MorphismProperty.Over.w g)).symm)))

/-- **Unique lifting for morphisms of covers, as an equality of morphisms**: two morphisms of
covers agreeing at one point of a preconnected source, over a Hausdorff total space of the
target, are equal.

`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.base_eq_of_apply_eq` followed by
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.hom_ext_of_base_eq`. The hypotheses are the first
one's and are discussed there; the second asks nothing. -/
theorem FiniteEtaleOver.hom_ext_of_apply_eq {X : AnalyticSpace.{u}} {A B : FiniteEtaleOver.{u} X}
    [PreconnectedSpace (A.left : Type u)] [T2Space (B.left : Type u)] (f g : A ⟶ B)
    (a : (A.left : Type u)) (h : f.left.toLRSHom.base a = g.left.toLRSHom.base a) : f = g :=
  FiniteEtaleOver.hom_ext_of_base_eq.{u} f g (FiniteEtaleOver.base_eq_of_apply_eq.{u} f g a h)

/-- **The same, from a point of a fibre.** -/
theorem FiniteEtaleOver.hom_ext_of_fiberMap_eq {X : AnalyticSpace.{u}}
    {A B : FiniteEtaleOver.{u} X} [PreconnectedSpace (A.left : Type u)]
    [T2Space (B.left : Type u)] {x : X} (f g : A ⟶ B) (a : FiniteEtaleOver.fiber.{u} x A)
    (h : FiniteEtaleOver.fiberMap.{u} x f a = FiniteEtaleOver.fiberMap.{u} x g a) : f = g :=
  FiniteEtaleOver.hom_ext_of_base_eq.{u} f g (FiniteEtaleOver.base_eq_of_fiberMap_eq.{u} f g a h)

/-- **The fibre functor is faithful where its hypotheses hold**: two morphisms of covers whose
images under `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fiberFunctor` at a point are equal
are themselves equal, over a preconnected source and a Hausdorff total space of the target,
provided the fibre there has a point.

**This is the statement `## What is not here` said was missing**, and what was missing was one
lemma rather than a theory:
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.base_eq_of_fiberFunctor_map_eq` was already here
and gives the base maps;
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.hom_ext_of_base_eq` turns that into an equality of
morphisms.

**It is not itself `CategoryTheory.Functor.Faithful`**, which would quantify over *all* objects
of `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver X` and ask for no point; each of
`[PreconnectedSpace A.left]`, `[T2Space B.left]` and the point `a` restricts which pairs this
reaches. **Of the three it is the point that comes off**, and it comes off at the cost of a
hypothesis on the base:
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.hom_ext_of_forall_fiberMap_eq` below asks for the
whole fibre and no point of it, over a preconnected base, and the class then holds on the full
subcategory the other two hypotheses cut out. **Neither of those two theorems bears on
conservativity**, which is a statement about one morphism and not about a pair of them; what does
is `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.reflectsIsomorphisms_fiberFunctor` at the foot
of this file, and it holds on that same full subcategory.

**The empty fibre is not the obstruction it was read as.** This docstring used to give the trivial
cover at an empty index type as the reason the point is *not a technicality*; the fibre there is
indeed empty and the functor's value determines nothing, but over a preconnected base that case
forces the total space to be empty and closes through
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.hom_ext_of_base_eq` instead. -/
theorem FiniteEtaleOver.hom_ext_of_fiberFunctor_map_eq {X : AnalyticSpace.{u}}
    {A B : FiniteEtaleOver.{u} X} [PreconnectedSpace (A.left : Type u)]
    [T2Space (B.left : Type u)] {x : X} (f g : A ⟶ B) (a : FiniteEtaleOver.fiber.{u} x A)
    (h : (FiniteEtaleOver.fiberFunctor.{u} x).map f = (FiniteEtaleOver.fiberFunctor.{u} x).map g) :
    f = g :=
  FiniteEtaleOver.hom_ext_of_base_eq.{u} f g
    (FiniteEtaleOver.base_eq_of_fiberFunctor_map_eq.{u} f g a h)

/-- **An endomorphism of a connected cover that fixes a point is the identity morphism.**

`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.base_eq_id_of_apply_eq` said this of the map on
points; this says it of the morphism, which is the form the rigidity of deck transformations is
usually stated in. The automorphism group of a connected cover acts freely on each fibre — as a
group of automorphisms and not only as a group of self-maps. -/
theorem FiniteEtaleOver.eq_id_of_apply_eq {X : AnalyticSpace.{u}} {A : FiniteEtaleOver.{u} X}
    [PreconnectedSpace (A.left : Type u)] [T2Space (A.left : Type u)] (f : A ⟶ A)
    (a : (A.left : Type u)) (h : f.left.toLRSHom.base a = a) : f = 𝟙 A :=
  FiniteEtaleOver.hom_ext_of_apply_eq.{u} f (𝟙 A) a h

/-! ### Faithfulness of the fibre functor, on the covers whose total space is connected and
Hausdorff -/

/-- **Over a preconnected base, a cover with a non-empty total space has a non-empty fibre at
every point.**

`ComplexAnalytic.AnalyticSpace.surjective_base_of_isFiniteEtale` at the structure map, which is
finite étale because the object carries the class in its `prop` field. **This is where
preconnectedness of the *base* is spent, and it is the only place below that spends it.**

**The two `inferInstanceAs` lines are the comma category's and not this statement's**, exactly as
in `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.card_fiber` above and for the same reason: an
object's structure map has its total space behind `CategoryTheory.Functor.id` and its base behind
`CategoryTheory.Functor.fromPUnit`, both the space itself by `rfl` but not reducibly so, and
instance search unfolds only at reducible transparency. Neither line has mathematical content. -/
theorem FiniteEtaleOver.nonempty_fiber {X : AnalyticSpace.{u}} [PreconnectedSpace (X : Type u)]
    (A : FiniteEtaleOver.{u} X) [Nonempty (A.left : Type u)] (x : X) :
    Nonempty (FiniteEtaleOver.fiber.{u} x A) :=
  haveI : IsFiniteEtale A.hom := A.prop
  haveI : Nonempty (((𝟭 AnalyticSpace.{u}).obj A.left : AnalyticSpace.{u}) : Type u) :=
    inferInstanceAs (Nonempty (A.left : Type u))
  haveI : PreconnectedSpace
      (((Functor.fromPUnit.{0} X).obj A.right : AnalyticSpace.{u}) : Type u) :=
    inferInstanceAs (PreconnectedSpace (X : Type u))
  ⟨⟨_, (surjective_base_of_isFiniteEtale A.hom x).choose_spec⟩⟩

/-- **An empty fibre over a preconnected base forces the total space to be empty.**

`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.nonempty_fiber` above read backwards, and it is
the direction a caller wants when it has a fibre in hand and no point of the total space:
over a preconnected base a cover with a point has a point over *every* point of the base, so a
fibre that is empty anywhere leaves nothing in the total space at all.

**No hypothesis on the point and none on the total space.** The `[Nonempty A.left]` that
`nonempty_fiber` asks for is what this concludes the negation of, so it cannot be assumed here;
the instance is introduced inside the proof, in the branch where it is being refuted. -/
theorem FiniteEtaleOver.isEmpty_left_of_isEmpty_fiber {X : AnalyticSpace.{u}}
    [PreconnectedSpace (X : Type u)] (A : FiniteEtaleOver.{u} X) (x : X)
    (h : IsEmpty (FiniteEtaleOver.fiber.{u} x A)) : IsEmpty (A.left : Type u) := by
  by_contra hc
  haveI : Nonempty (A.left : Type u) := not_isEmpty_iff.mp hc
  exact (FiniteEtaleOver.nonempty_fiber.{u} A x).elim h.elim

/-- **Two morphisms of covers that agree on the whole fibre over a point of a preconnected base
are equal — and no point of that fibre is assumed.**

This is `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.hom_ext_of_fiberMap_eq` with its point
hypothesis discharged rather than weakened, and `[PreconnectedSpace X]` on the **base** is what
pays for it. The proof is the dichotomy
`ComplexAnalytic.AnalyticSpace.surjective_base_or_isEmpty_of_isFiniteEtale`
(`Oka/AnalyticSpace/LocalIso.lean`) read at the structure map, in two cases:

* the total space is non-empty, and then
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.nonempty_fiber` above produces a point of the
  fibre and the hypothesis is applied at it;
* the total space is empty, and then the two base maps are equal because there is nothing to
  compare, and `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.hom_ext_of_base_eq` closes it with
  no fibre in sight.

**The empty case is why the `## What is not here` paragraph that priced the point hypothesis as
*not a technicality* was reading it the wrong way round.** That paragraph's witness was the
trivial cover at an empty index type, whose fibre is empty by
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fiberTrivialEquiv` and over which the functor's
value determines nothing; but over a *preconnected* base an empty fibre forces the total space
itself to be empty, and there a morphism of covers is determined with no information about fibres
at all.
**The empty fibre is not a counterexample to faithfulness; it is a case that closes for a
different reason.**

**The three hypotheses that remain are not shown necessary here.** `[PreconnectedSpace A.left]`
and `[T2Space B.left]` are what
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.base_eq_of_apply_eq` reads and buy exactly the base
maps, which is lana-agents/oka#436's finding and is unchanged;
`[PreconnectedSpace X]` is what the dichotomy reads. No witness against dropping any of the three
is exhibited or claimed. -/
theorem FiniteEtaleOver.hom_ext_of_forall_fiberMap_eq {X : AnalyticSpace.{u}}
    [PreconnectedSpace (X : Type u)] {A B : FiniteEtaleOver.{u} X}
    [PreconnectedSpace (A.left : Type u)] [T2Space (B.left : Type u)] {x : X} (f g : A ⟶ B)
    (h : ∀ a : FiniteEtaleOver.fiber.{u} x A,
      FiniteEtaleOver.fiberMap.{u} x f a = FiniteEtaleOver.fiberMap.{u} x g a) : f = g := by
  rcases isEmpty_or_nonempty (A.left : Type u) with hA | hA
  · exact FiniteEtaleOver.hom_ext_of_base_eq.{u} f g (funext fun a ↦ isEmptyElim a)
  · obtain ⟨a⟩ := FiniteEtaleOver.nonempty_fiber.{u} A x
    exact FiniteEtaleOver.hom_ext_of_fiberMap_eq.{u} f g a (h a)

/-- **The fibre functor is injective on morphisms out of a connected cover into a Hausdorff one,
over a preconnected base**, with no point of the fibre assumed.

The theorem above with the hypothesis read off an equality of the functor's values. The step from
that equality to a pointwise one is the `congrArg` that
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.base_eq_of_fiberFunctor_map_eq` documents, and it
is taken pointwise for the reason recorded there. -/
theorem FiniteEtaleOver.fiberFunctor_map_injective {X : AnalyticSpace.{u}}
    [PreconnectedSpace (X : Type u)] (x : X) {A B : FiniteEtaleOver.{u} X}
    [PreconnectedSpace (A.left : Type u)] [T2Space (B.left : Type u)] :
    Function.Injective ((FiniteEtaleOver.fiberFunctor.{u} x).map (X := A) (Y := B)) :=
  fun _ _ h ↦ FiniteEtaleOver.hom_ext_of_forall_fiberMap_eq.{u} _ _
    fun a ↦ congrArg (fun k ↦ TypeCat.Hom.hom k a) h

/-- **The same for the `FintypeCat`-valued fibre functor**, which is the shape a Galois category
asks for.

The two functors have the same `map` field up to the bundling their targets ask for —
`TypeCat.ofHom` there and `FintypeCat.homMk` here — so the only difference from the theorem above
is which projection the `congrArg` takes. **Neither is derived from the other**, because the
bundling is not the same map. -/
theorem FiniteEtaleOver.fintypeFiberFunctor_map_injective {X : AnalyticSpace.{u}}
    [PreconnectedSpace (X : Type u)] (x : X) {A B : FiniteEtaleOver.{u} X}
    [PreconnectedSpace (A.left : Type u)] [T2Space (B.left : Type u)] :
    Function.Injective ((FiniteEtaleOver.fintypeFiberFunctor.{u} x).map (X := A) (Y := B)) :=
  fun _ _ h ↦ FiniteEtaleOver.hom_ext_of_forall_fiberMap_eq.{u} _ _
    fun a ↦ congrArg (fun k ↦ k a) h

/-- **The covers whose total space is preconnected and Hausdorff**, as an
`CategoryTheory.ObjectProperty` and hence as a full subcategory.

Both conditions are on the **total space of the object itself**, and that is forced rather than
chosen: the injectivity statements above ask `[PreconnectedSpace A.left]` of the source and
`[T2Space B.left]` of the target, so a property that a full subcategory can be cut out by has to
carry both of them at every object.

**A cover with an empty total space satisfies this**, and that is not an accident of spelling:
`PreconnectedSpace` is preconnectedness of `Set.univ` and does not ask for a point, `Nonempty`
being `ConnectedSpace`'s extra field.
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isPreconnectedT2_trivial_of_isEmpty` and
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isPreconnectedT2_trivial_of_isEmpty_base` below are
that case, at an empty index type and over an empty base, **and each of them is an object at which
the point-of-the-fibre hypothesis could say nothing.**

**Over a non-empty base**, what the subcategory does **not** contain is a trivial cover with two
distinct sheets, by
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.not_preconnectedSpace_trivial`, which reads
`[Nonempty X]`. **That hypothesis is this property's blind spot and not decoration**: the property
puts no condition on the base at all, so over an *empty* base the trivial cover at **any** index
type has an empty total space, and the paragraph above then puts it inside.
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isPreconnectedT2_trivial_of_isEmpty_base` below is
that, with the index type left free: give it two distinct elements and the very cover
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.not_preconnectedSpace_trivial` excludes is an
object here. **What that took was the other emptiness lemma**, the one asking that the **members**
of the disjoint union be empty rather than its index type —
`ComplexAnalytic.AnalyticSpace.isEmpty_sigma_of_members` and not
`ComplexAnalytic.AnalyticSpace.isEmpty_sigma`, which is what the cover at an empty index type
uses. -/
def FiniteEtaleOver.isPreconnectedT2 (X : AnalyticSpace.{u}) :
    ObjectProperty (FiniteEtaleOver.{u} X) :=
  fun A ↦ PreconnectedSpace (A.left : Type u) ∧ T2Space (A.left : Type u)

/-- **The base over itself is an object of that subcategory**, when the base is preconnected and
Hausdorff.

`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.id`'s total space is the base on the nose, so this
is two `inferInstanceAs` and no proof. It is here so that the subcategory is known to be non-empty
from inside this file; `OkaTest/FiniteEtaleOver.lean` exhibits an object of it that is **not**
isomorphic to this one. -/
theorem FiniteEtaleOver.isPreconnectedT2_id (X : AnalyticSpace.{u})
    [PreconnectedSpace (X : Type u)] [T2Space (X : Type u)] :
    FiniteEtaleOver.isPreconnectedT2.{u} X (FiniteEtaleOver.id.{u} X) :=
  ⟨inferInstanceAs (PreconnectedSpace (X : Type u)), inferInstanceAs (T2Space (X : Type u))⟩

/-- **And so is the trivial cover at an empty index type**, with no hypothesis on the base at all.

Its total space is empty by `ComplexAnalytic.AnalyticSpace.isEmpty_sigma`, and an empty space is
both preconnected and Hausdorff because a subsingleton is.

**This is the object the `## What is not here` paragraph used as its reason for keeping the point
of the fibre**, and it is an object of the subcategory the fibre functor is faithful on. Its
fibre at every point of the base is empty —
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fiberTrivialEquiv` puts that fibre in bijection
with the index type — so the functor's value there really does determine nothing, and
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.hom_ext_of_forall_fiberMap_eq` reaches it anyway,
by the branch that reads no fibre. **The witness against the hypothesis is an object of the
statement that drops it.** -/
theorem FiniteEtaleOver.isPreconnectedT2_trivial_of_isEmpty (ι : Type u) [Finite ι] [IsEmpty ι]
    (X : AnalyticSpace.{u}) :
    FiniteEtaleOver.isPreconnectedT2.{u} X (FiniteEtaleOver.trivial.{u} ι X) :=
  haveI : IsEmpty ((FiniteEtaleOver.trivial.{u} ι X).left : Type u) :=
    isEmpty_sigma (F := fun _ : ι ↦ X)
  ⟨inferInstance, inferInstance⟩

/-- **And so is the trivial cover over an empty base**, at any finite index type at all.

Its total space is empty by `ComplexAnalytic.AnalyticSpace.isEmpty_sigma_of_members`, the members
of the disjoint union being the base itself. That is the theorem above at the other quantifier:
there the emptiness is discharged at the index type, here at a point of a member, and here the
index type is left free.

**Leaving it free is what this is for.**
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.not_preconnectedSpace_trivial` says a trivial cover
with two distinct sheets is *outside* the subcategory, and it reads `[Nonempty X]`; give `ι` two
distinct elements here and the same cover is inside it. **So that hypothesis is doing work rather
than decorating the statement**, which is a thing the docstring of
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isPreconnectedT2` argued in prose and nothing in
the tree witnessed. -/
theorem FiniteEtaleOver.isPreconnectedT2_trivial_of_isEmpty_base (ι : Type u) [Finite ι]
    (X : AnalyticSpace.{u}) [IsEmpty (X : Type u)] :
    FiniteEtaleOver.isPreconnectedT2.{u} X (FiniteEtaleOver.trivial.{u} ι X) :=
  haveI : IsEmpty ((FiniteEtaleOver.trivial.{u} ι X).left : Type u) :=
    isEmpty_sigma_of_members (F := fun _ : ι ↦ X)
  ⟨inferInstance, inferInstance⟩

/-- **`CategoryTheory.Functor.Faithful` for the fibre functor**, on the full subcategory of covers
whose total space is preconnected and Hausdorff, over a preconnected base.

**This is the class, and the statement `## What is not here` said was missing.** What the
paragraph there said was missing was a *full subcategory on which the instance holds*; the
`## What is not here` reading that the point of the fibre is the obstruction is what turned out to
be wrong, and `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.hom_ext_of_forall_fiberMap_eq` above
says why. **The other two hypotheses do not drop out and are not meant to**: they are what the
covering-map rung is for, and they are exactly the two conditions the subcategory is cut out by.

**`[PreconnectedSpace X]` on the base stays a hypothesis of the statement rather than joining the
subcategory**, because it is a condition on the base and not on an object.

**The explicit instance arguments are the comma category's seam again.** `A.property.1` is
`PreconnectedSpace A.obj.left` and the goal wants it at
`((FiniteEtaleOver.isPreconnectedT2 X).ι.obj A).left`, which is the same by `rfl` and not
reducibly so; passing the two fields positionally is what avoids restating them. -/
instance FiniteEtaleOver.faithful_fiberFunctor {X : AnalyticSpace.{u}}
    [PreconnectedSpace (X : Type u)] (x : X) :
    ((FiniteEtaleOver.isPreconnectedT2.{u} X).ι
      ⋙ FiniteEtaleOver.fiberFunctor.{u} x).Faithful where
  map_injective {A B} {f g} h :=
    ObjectProperty.hom_ext _
      (@FiniteEtaleOver.fiberFunctor_map_injective X ‹_› x A.obj B.obj
        A.property.1 B.property.2 _ _ h)

/-- **The same for the `FintypeCat`-valued fibre functor.**

This is the one a Galois category would want, that definition asking for a functor into
`FintypeCat`. **It is not a Galois category**, and the reason this docstring used to give was
wrong: it said that *faithfulness is one of the axioms and base change is another*.
**`CategoryTheory.Functor.Faithful` is not one of the axioms.** At the Mathlib revision
`lakefile.toml` pins, `Mathlib/CategoryTheory/Galois/Basic.lean` — whose namespace is not in this
file's import closure and so cannot be cited by name here — carries faithfulness of a fibre
functor as an `instance` *derived* from the axioms rather than as a field of the class asking for
them. So this instance proves something such a structure would hand back for free, and it
discharges none of that structure's obligations.

**What does discharge one is
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.preservesLimitsOfShape_pempty_fintypeFiberFunctor`
below**, composed with
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.preservesLimitsOfShape_pempty_ι` to reach this same
restricted functor, **and so does
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.reflectsIsomorphisms_fintypeFiberFunctor` below**,
which is conservativity — the axiom that class asks of a fibre functor where faithfulness is the
thing it hands back. **Base change of the class over a cospan of morphisms of covers is still
absent** — the
sentence read *Base change over a general cospan is still absent* until 2026-09-08 and
*Base change of the class over a general cospan is still absent* until 2026-09-15 — for the
reason the
`## No base change of the class over a cospan of morphisms of covers` bullet gives, and nothing
here bears on it. -/
instance FiniteEtaleOver.faithful_fintypeFiberFunctor {X : AnalyticSpace.{u}}
    [PreconnectedSpace (X : Type u)] (x : X) :
    ((FiniteEtaleOver.isPreconnectedT2.{u} X).ι
      ⋙ FiniteEtaleOver.fintypeFiberFunctor.{u} x).Faithful where
  map_injective {A B} {f g} h :=
    ObjectProperty.hom_ext _
      (@FiniteEtaleOver.fintypeFiberFunctor_map_injective X ‹_› x A.obj B.obj
        A.property.1 B.property.2 _ _ h)

/-! ### The terminal object of that subcategory, and the two fibre functors preserve it -/

/-- **The base over itself is terminal in the preconnected–Hausdorff subcategory too**, when the
base is preconnected and Hausdorff.

`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isPreconnectedT2_id` is the membership proof, and
it was written so that the subcategory is known to be non-empty from inside this file; it turns
out to be the terminal object's admission ticket as well, which is why `[PreconnectedSpace X]` and
`[T2Space X]` are hypotheses of this statement rather than conditions on an object.

**A full subcategory's morphisms are the ambient category's, and they are so by a definitional
equality that instance search and unification do not cross on their own.**
`CategoryTheory.ObjectProperty.homMk` and `CategoryTheory.ObjectProperty.hom_ext` are the two
functions that cross it, and they are the same pair
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.faithful_fiberFunctor` already uses. **Going
through them keeps this computable**: the other route across the seam is
`CategoryTheory.Functor.preimage` at `CategoryTheory.ObjectProperty.ι`, which is data extracted
from a `CategoryTheory.Functor.Full` instance and would force a `noncomputable` here for no
mathematical reason. -/
def FiniteEtaleOver.isTerminalIdSubcategory (X : AnalyticSpace.{u})
    [PreconnectedSpace (X : Type u)] [T2Space (X : Type u)] :
    Limits.IsTerminal (⟨FiniteEtaleOver.id.{u} X, FiniteEtaleOver.isPreconnectedT2_id.{u} X⟩ :
      (FiniteEtaleOver.isPreconnectedT2.{u} X).FullSubcategory) :=
  Limits.IsTerminal.ofUniqueHom
    (fun A ↦ ObjectProperty.homMk ((FiniteEtaleOver.isTerminalId.{u} X).from A.obj))
    fun _ _ ↦ ObjectProperty.hom_ext _ ((FiniteEtaleOver.isTerminalId.{u} X).hom_ext _ _)

/-- **And so that subcategory has a terminal object.**

The class, for the same reason
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.hasTerminal` gives above. **This is the one a
Galois category would consume**, the fibre functor's faithfulness and the conservativity question
both being stated on this subcategory and not on the whole of
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver`. -/
instance FiniteEtaleOver.hasTerminalSubcategory (X : AnalyticSpace.{u})
    [PreconnectedSpace (X : Type u)] [T2Space (X : Type u)] :
    Limits.HasTerminal (FiniteEtaleOver.isPreconnectedT2.{u} X).FullSubcategory :=
  (FiniteEtaleOver.isTerminalIdSubcategory.{u} X).hasTerminal

/-- **The inclusion of that subcategory preserves the terminal object.**

Both categories have a terminal object and the inclusion carries the subcategory's to the ambient
one, which is the whole content:
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isTerminalIdSubcategory` is the cone and
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isTerminalId` is its image, and the two are the
same object of `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver X` by `rfl`.

**This is what makes preservation hold of the *restricted* fibre functors and not only of the
unrestricted ones, and it is why neither is stated twice.**
`CategoryTheory.Limits.comp_preservesLimitsOfShape` composes this with
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.preservesLimitsOfShape_pempty_fiberFunctor` or with
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.preservesLimitsOfShape_pempty_fintypeFiberFunctor`
to give the restricted functor's preservation by instance search, and `infer_instance` closes both
composite goals — measured.
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.faithful_fiberFunctor` and
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.faithful_fintypeFiberFunctor` are stated for the
composite and not for the functor on the whole category, so the composite is the shape a
Galois-category structure would consume.

**A subcategory inclusion does not preserve limits in general** — a full subcategory closed under
nothing need not contain the ambient limit — and what makes it do so here is that the ambient
terminal object lies in the subcategory, which is
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isPreconnectedT2_id` and is where `[T2Space X]`
enters. -/
instance FiniteEtaleOver.preservesLimitsOfShape_pempty_ι (X : AnalyticSpace.{u})
    [PreconnectedSpace (X : Type u)] [T2Space (X : Type u)] :
    Limits.PreservesLimitsOfShape (Discrete PEmpty.{1})
      (FiniteEtaleOver.isPreconnectedT2.{u} X).ι :=
  haveI : Limits.PreservesLimit
      (Functor.empty.{0} (FiniteEtaleOver.isPreconnectedT2.{u} X).FullSubcategory)
      (FiniteEtaleOver.isPreconnectedT2.{u} X).ι :=
    Limits.preservesLimit_of_preserves_limit_cone
      (FiniteEtaleOver.isTerminalIdSubcategory.{u} X)
      ((Limits.isLimitMapConeEmptyConeEquiv _ _).symm (FiniteEtaleOver.isTerminalId.{u} X))
  Limits.preservesLimitsOfShape_pempty_of_preservesTerminal _

/-- **The value of the `FintypeCat`-valued fibre functor at the base over itself is a terminal
object of `FintypeCat`.**

The mathematical content is
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.uniqueFiberId` and nothing else: the fibre of the
base over itself at `x` is the one-point set `{x}`, so a map into it from anywhere exists and is
unique.

**The `Type u`-valued functor needs no companion to this**, because
`CategoryTheory.Limits.Types.isTerminalEquivUnique` converts a `Unique` into a
`CategoryTheory.Limits.IsTerminal` in `Type u` directly, and
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.preservesLimitsOfShape_pempty_fiberFunctor` uses it
inline. `FintypeCat` has no such equivalence, which is why this one is written out — the same
asymmetry between the two functors that
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fintypeFiberFunctor_map_injective` records, and for
the same reason: the two categories' morphisms are different structures.

**The `haveI` is the `FintypeCat` bundling seam and not a mathematical step.** `FintypeCat.of`
wraps the fibre, and the `Unique` instance above is not found through that wrapper by instance
search, which works up to reducible unfolding; `inferInstanceAs` restates it at the wrapped type
and there is no content in the restatement. -/
def FiniteEtaleOver.isTerminalFintypeFiberId {X : AnalyticSpace.{u}} (x : X) :
    Limits.IsTerminal
      ((FiniteEtaleOver.fintypeFiberFunctor.{u} x).obj (FiniteEtaleOver.id.{u} X)) :=
  haveI : Unique (((FiniteEtaleOver.fintypeFiberFunctor.{u} x).obj
      (FiniteEtaleOver.id.{u} X) : FintypeCat.{u}) : Type u) :=
    inferInstanceAs (Unique (FiniteEtaleOver.fiber.{u} x (FiniteEtaleOver.id.{u} X)))
  Limits.IsTerminal.ofUniqueHom (fun _ ↦ FintypeCat.homMk fun _ ↦ default)
    fun _ _ ↦ FintypeCat.hom_ext _ _ fun _ ↦ Subsingleton.elim _ _

/-- **The `Type u`-valued fibre functor preserves the terminal object**, with no hypothesis on the
base or on the point.

`CategoryTheory.Limits.preservesLimit_of_preserves_limit_cone` at the cone
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isTerminalId` is, with
`CategoryTheory.Limits.isLimitMapConeEmptyConeEquiv` turning *the image cone is a limit* into
*the image object is terminal*. The image object is the fibre of the base over itself, which is a
point by `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.uniqueFiberId`, and
`CategoryTheory.Limits.Types.isTerminalEquivUnique` is the conversion.

**Preservation of the terminal object is a Galois-category axiom on the fibre functor**, in
`Mathlib/CategoryTheory/Galois/Basic.lean`, whose namespace is not in this file's import
closure and so cannot be cited by name here. **It is one field of that structure and this instance
does not supply the others**; the `## What is not here` bullet
**No base change of the class over a cospan of morphisms of covers**
is still exactly true of the cospans a Galois category quantifies
over, and
this instance bears on neither quotients by finite group actions nor the axiom that a monomorphism
induces an isomorphism onto a direct summand. **That bullet was titled *No pullbacks, so no base
change* and this sentence called it exactly true**, which stopped being so when
`Oka/AnalyticSpace/PullbackOpen.lean` exhibited the pullback along the inclusion of an open
subspace; the bullet is narrowed and so is this citation of it. **It was titled *No pullback over
a general cospan, so no base change* until 2026-09-08**, when
`Oka/AnalyticSpace/PullbackReduction.lean` made
`CategoryTheory.Limits.HasPullbacks ComplexAnalytic.AnalyticSpace` a theorem and left the class
where it was; that is a second narrowing of the same bullet and this citation follows it again.
**And it was titled *No base change of the class over a general cospan* until 2026-09-15**, when
`Oka/AnalyticSpace/FiniteEtaleStableUnderBaseChange.lean` carried the class over every cospan of
`ComplexAnalytic.AnalyticSpace` and left the cospans of morphisms of covers where they were; that
is a third narrowing and this citation follows it a third time. **What this sentence asserts of
the bullet has not moved across any of the three**: it is exactly true of the cospans a Galois
category quantifies over, which are cospans of that category and were so under every title.

**The conclusion is `CategoryTheory.Limits.PreservesLimitsOfShape` at the empty shape and not
`CategoryTheory.Limits.PreservesLimit` at
`CategoryTheory.Functor.empty`, and the choice is load-bearing.** The two say the same thing:
`CategoryTheory.Limits.PreservesLimitsOfShape` at the empty shape is the spelling that structure's
field is written in, `CategoryTheory.Limits.PreservesLimit` at `CategoryTheory.Functor.empty` is
the spelling the proof is naturally in, and
`CategoryTheory.Limits.preservesLimitsOfShape_pempty_of_preservesTerminal` converts the second into
the first. **That converter is a `lemma` and not an instance**, so a consumer holding only
`CategoryTheory.Limits.PreservesLimit` would have to apply it by hand — while
`CategoryTheory.Limits.PreservesLimitsOfShape` hands back
`CategoryTheory.Limits.PreservesLimit` through
`CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`, which *is* an instance. Stating the
stronger one costs one line here and saves the conversion at every use. -/
instance FiniteEtaleOver.preservesLimitsOfShape_pempty_fiberFunctor {X : AnalyticSpace.{u}}
    (x : X) :
    Limits.PreservesLimitsOfShape (Discrete PEmpty.{1}) (FiniteEtaleOver.fiberFunctor.{u} x) :=
  haveI : Limits.PreservesLimit (Functor.empty.{0} (FiniteEtaleOver.{u} X))
      (FiniteEtaleOver.fiberFunctor.{u} x) :=
    Limits.preservesLimit_of_preserves_limit_cone (FiniteEtaleOver.isTerminalId.{u} X)
      ((Limits.isLimitMapConeEmptyConeEquiv _ _).symm
        ((Limits.Types.isTerminalEquivUnique _).symm (FiniteEtaleOver.uniqueFiberId.{u} x)))
  Limits.preservesLimitsOfShape_pempty_of_preservesTerminal _

/-- **The same for the `FintypeCat`-valued fibre functor**, which is the shape a Galois category
asks for.

The same proof with
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isTerminalFintypeFiberId` in place of the inline
conversion, for the reason that declaration's docstring gives, and in the same
`CategoryTheory.Limits.PreservesLimitsOfShape` spelling, for the reason
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.preservesLimitsOfShape_pempty_fiberFunctor` gives.
**Composed with
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.preservesLimitsOfShape_pempty_ι` this is the
instance a Galois-category structure would consume**, that structure asking for a functor into
`FintypeCat`. -/
instance FiniteEtaleOver.preservesLimitsOfShape_pempty_fintypeFiberFunctor {X : AnalyticSpace.{u}}
    (x : X) :
    Limits.PreservesLimitsOfShape (Discrete PEmpty.{1})
      (FiniteEtaleOver.fintypeFiberFunctor.{u} x) :=
  haveI : Limits.PreservesLimit (Functor.empty.{0} (FiniteEtaleOver.{u} X))
      (FiniteEtaleOver.fintypeFiberFunctor.{u} x) :=
    Limits.preservesLimit_of_preserves_limit_cone (FiniteEtaleOver.isTerminalId.{u} X)
      ((Limits.isLimitMapConeEmptyConeEquiv _ _).symm
        (FiniteEtaleOver.isTerminalFintypeFiberId.{u} x))
  Limits.preservesLimitsOfShape_pempty_of_preservesTerminal _

/-! ### The degree of a morphism of covers, and the divisibility it gives -/

/-- **The degree of a cover factors through the degree of any morphism out of it.**

A morphism `f : A ⟶ B` of covers is a triangle over the base:
`CategoryTheory.MorphismProperty.Over.w` says `f.left ≫ B.hom = A.hom`, so the structure map of
`A` *is* a composite, and
`ComplexAnalytic.AnalyticSpace.degree_comp` (`Oka/AnalyticSpace/Degree.lean`) reads it.

**Where the hypotheses go.** `[T2Space A.left]` and `[PreconnectedSpace B.left]` are what
`degree_comp` needs of its first factor, `[T2Space B.left]` and `[PreconnectedSpace X]` are what
it needs of its second, and there is nothing else. In particular `[PreconnectedSpace A.left]` is
**not** asked for and would be the wrong hypothesis: the cover upstairs may be disconnected and
the statement still holds, which is what the trivial cover exhibits.

**`ComplexAnalytic.AnalyticSpace.IsFiniteEtale f.left` is not a hypothesis and is not free
either.** It is `ComplexAnalytic.AnalyticSpace.isFiniteEtale_of_comp`
(`Oka/AnalyticSpace/LocalIso.lean`) at the triangle — the cancellation whose `[T2Space]` on the
middle space is `[T2Space B.left]` here — and it is the reason that hypothesis appears twice over
in the discussion of this file's `## What is not here`: a morphism of covers is finite étale
because the *target* cover's total space is separated, not because the category asks it to be.

**The instance seam bites in the direction opposite to
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.card_fiber`'s, and both directions are now needed
in this file.** There, `[T2Space]` and `[PreconnectedSpace]` are restated at the comma category's
spelling of a space, because `ComplexAnalytic.AnalyticSpace.degree_eq_card_fiber` asks for them at
the bare one. Here it is the other way round: `f.left` has target `B.left` on the nose, so
`ComplexAnalytic.AnalyticSpace.isFiniteEtale_of_comp` asks for `IsLocalIso B.hom` with `B.left`
as its source, while the instance an object carries in its `prop` field has
`(CategoryTheory.Functor.id _).obj B.left` there. The two are `rfl`-equal and are different
discrimination-tree keys, so `B.prop` is in context and the synthesis still fails — with a goal
that prints identically to the hypothesis, which is what makes it expensive to read. The named
argument `(X := B.left)` on the two `haveI`s below is the whole of the repair; taxis #1681 is the
filing about this seam. -/
theorem FiniteEtaleOver.degree_eq_mul {X : AnalyticSpace.{u}} {A B : FiniteEtaleOver.{u} X}
    (f : A ⟶ B) [T2Space A.left] [T2Space B.left] [PreconnectedSpace B.left]
    [PreconnectedSpace (X : Type u)] :
    A.degree = AnalyticSpace.degree f.left * B.degree := by
  have hw : f.left ≫ B.hom = A.hom := MorphismProperty.Over.w f
  haveI : IsFiniteEtale (X := B.left) B.hom := B.prop
  haveI : IsLocalIso (X := B.left) B.hom := IsFiniteEtale.isLocalIso
  haveI : IsFiniteEtale (f.left ≫ B.hom) := hw ▸ (A.prop : IsFiniteEtale A.hom)
  haveI : IsFiniteEtale f.left := isFiniteEtale_of_comp f.left B.hom
  haveI : PreconnectedSpace
      (((Functor.fromPUnit.{0} X).obj B.right : AnalyticSpace.{u}) : Type u) :=
    inferInstanceAs (PreconnectedSpace (X : Type u))
  calc A.degree = AnalyticSpace.degree (f.left ≫ B.hom) := by rw [hw]; rfl
    _ = AnalyticSpace.degree f.left * B.degree := degree_comp f.left B.hom

/-- **The degree of the target of a morphism of covers divides the degree of its source.**

`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.degree_eq_mul` with the witness read off, and the
witness is the degree of the morphism itself rather than an anonymous natural number.

**This is the first statement in this file relating the degrees of two objects that are not
isomorphic.** `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.degree_eq_of_iso` says isomorphic
covers have equal degrees and says nothing about anything else; a bare morphism is much weaker
than an isomorphism and still constrains the two numbers.

**It is not vacuous and it is not sharp.** Over an empty base every degree is `0` and every
divisibility holds, which is the degenerate reading; over a non-empty base the trivial cover at
`ι` maps to the base over itself, and `Nat.card ι` is divisible by `1` — the statement in that
instance says exactly that the base over itself has degree one. What it does not do is produce a
morphism from a divisibility, and nothing here does. -/
theorem FiniteEtaleOver.degree_dvd_degree {X : AnalyticSpace.{u}} {A B : FiniteEtaleOver.{u} X}
    (f : A ⟶ B) [T2Space A.left] [T2Space B.left] [PreconnectedSpace B.left]
    [PreconnectedSpace (X : Type u)] :
    B.degree ∣ A.degree :=
  ⟨AnalyticSpace.degree f.left, by rw [FiniteEtaleOver.degree_eq_mul.{u} f, mul_comm]⟩

/-- **A morphism between covers of the same non-zero degree has degree one.**

`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.degree_eq_mul` gives
`B.degree = AnalyticSpace.degree f.left * B.degree` once the two degrees are identified, and
`Nat.mul_eq_right` cancels the non-zero factor.

**The non-vanishing hypothesis is not decoration.** Over an empty base both degrees are `0` and
`f.left` may have any degree at all; `0 = d * 0` says nothing. Stating it as `B.degree ≠ 0` rather
than as `[Nonempty X]` is deliberate — non-emptiness of the base does not by itself make a
cover's degree non-zero, since the empty cover of a non-empty base is finite étale and has degree
`0`, and it is the cover being non-empty over each point that the hypothesis really wants.

**What this does not say is that `f` is an isomorphism**, and that is now a fact about this
statement rather than about the tree:
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isIso_of_bijective_fiberMap` below says it, from a
bijection of fibres rather than from an equality of degrees, and this theorem is the middle step
of its proof. Degree one is a statement about the fibres of `f.left`; getting from it to
invertibility is `ComplexAnalytic.AnalyticSpace.isIso_of_degree_eq_one`
(`Oka/AnalyticSpace/Degree.lean`) followed by
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isIso_of_isIso_left`. -/
theorem FiniteEtaleOver.degree_left_eq_one {X : AnalyticSpace.{u}} {A B : FiniteEtaleOver.{u} X}
    (f : A ⟶ B) [T2Space A.left] [T2Space B.left] [PreconnectedSpace B.left]
    [PreconnectedSpace (X : Type u)] (h : A.degree = B.degree) (hB : B.degree ≠ 0) :
    AnalyticSpace.degree f.left = 1 :=
  (Nat.mul_eq_right hB).mp ((FiniteEtaleOver.degree_eq_mul.{u} f).symm.trans h)

/-! ### Conservativity of the fibre functor -/

/-- **A morphism of covers whose fibre map at one point of the base is bijective is an
isomorphism.**

This is the chain the `## What is not here` bullet describes, closed. `card_fiber` turns the
bijection into an equality of the two degrees, `degree_left_eq_one` turns that equality into
`AnalyticSpace.degree f.left = 1`, `ComplexAnalytic.AnalyticSpace.isIso_of_degree_eq_one`
(`Oka/AnalyticSpace/Degree.lean`) turns *that* into an isomorphism of analytic spaces, and
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isIso_of_isIso_left` carries it back to this
category. **The bijection is used at one point of the base and nothing is assumed at any other.**

**There is no `[Nonempty]` hypothesis, and its absence is the whole reason the instances below
are instances.** `isIso_of_degree_eq_one` asks its target to be non-empty and nothing in the
chain supplies that; `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isPreconnectedT2` does not
carry it either, since `PreconnectedSpace` is preconnectedness of `Set.univ` and does not ask for
a point. **So the empty case is closed rather than assumed away**, and it closes without a
degree: a bijective fibre map into an empty total space empties the source's fibre,
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isEmpty_left_of_isEmpty_fiber` empties the source,
and a morphism between two empty spaces is bijective on points for want of points, so
`ComplexAnalytic.AnalyticSpace.isIso_of_isLocalIso_of_bijective`
(`Oka/AnalyticSpace/LocalIso.lean`) applies directly. **A `[Nonempty B.left]` hypothesis would
have made this a theorem the subcategory below cannot discharge.**

**Where the hypotheses go.** `[T2Space A.left]` and `[PreconnectedSpace B.left]` are what
`degree_left_eq_one` needs of the first factor of the triangle, `[T2Space B.left]` and
`[PreconnectedSpace X]` are what it needs of the second, and `[PreconnectedSpace X]` is also what
`isEmpty_left_of_isEmpty_fiber` spends. In particular `[PreconnectedSpace A.left]` is **not**
asked for, so this is not a statement about the connected covers only.

**`IsFiniteEtale f.left` is derived and not assumed.** A morphism of this category carries no
condition — the second `⊤` in its definition says so — and the class comes back from
`ComplexAnalytic.AnalyticSpace.isFiniteEtale_of_comp` at the triangle, which is the same
opening `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.degree_eq_mul` above has, and it needs
the named binder `(X := B.left)` for the same reason. -/
theorem FiniteEtaleOver.isIso_of_bijective_fiberMap {X : AnalyticSpace.{u}}
    {A B : FiniteEtaleOver.{u} X} (f : A ⟶ B)
    [T2Space (A.left : Type u)] [T2Space (B.left : Type u)]
    [PreconnectedSpace (B.left : Type u)] [PreconnectedSpace (X : Type u)] (x : X)
    (hf : Function.Bijective (FiniteEtaleOver.fiberMap.{u} x f)) : IsIso f := by
  have hw : f.left ≫ B.hom = A.hom := MorphismProperty.Over.w f
  haveI : IsFiniteEtale (X := B.left) B.hom := B.prop
  haveI : IsLocalIso (X := B.left) B.hom := IsFiniteEtale.isLocalIso
  haveI : IsFiniteEtale (f.left ≫ B.hom) := hw ▸ (A.prop : IsFiniteEtale A.hom)
  haveI : IsFiniteEtale f.left := isFiniteEtale_of_comp f.left B.hom
  refine FiniteEtaleOver.isIso_of_isIso_left f ?_
  rcases isEmpty_or_nonempty (B.left : Type u) with hB | hB
  · haveI : IsEmpty (FiniteEtaleOver.fiber.{u} x B) := ⟨fun a ↦ isEmptyElim a.1⟩
    haveI : IsEmpty (FiniteEtaleOver.fiber.{u} x A) :=
      Function.isEmpty (FiniteEtaleOver.fiberMap.{u} x f)
    haveI := FiniteEtaleOver.isEmpty_left_of_isEmpty_fiber.{u} A x this
    exact isIso_of_isLocalIso_of_bijective f.left
      ⟨fun a _ _ ↦ isEmptyElim a, fun b ↦ isEmptyElim b⟩
  · have hdeg : A.degree = B.degree := by
      rw [← FiniteEtaleOver.card_fiber A x, ← FiniteEtaleOver.card_fiber B x]
      exact Nat.card_eq_of_bijective _ hf
    have hne : B.degree ≠ 0 := by
      rw [← FiniteEtaleOver.card_fiber B x]
      haveI := FiniteEtaleOver.nonempty_fiber.{u} B x
      exact Nat.card_pos.ne'
    exact isIso_of_degree_eq_one f.left (FiniteEtaleOver.degree_left_eq_one.{u} f hdeg hne)

/-- **The fibre functor is conservative** on the covers whose total space is preconnected and
Hausdorff, over a preconnected base.

`CategoryTheory.Functor.ReflectsIsomorphisms` on exactly the subcategory and at exactly the
hypothesis on the base that
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.faithful_fiberFunctor` asks for, so the two read
as a pair. What it says is that a morphism of covers carried to a bijection of fibres over one
point **is** an isomorphism, where faithfulness says only that two morphisms agreeing there are
equal.

**Being an isomorphism in `Type u` is bijectivity of the underlying map**, by
`CategoryTheory.isIso_iff_bijective`, which is what connects the functor's conclusion to
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isIso_of_bijective_fiberMap` above.

**The explicit instance arguments are the comma category's seam**, exactly as
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.faithful_fiberFunctor`'s docstring records:
`A.property.2` is `T2Space A.obj.left` and the goal wants it at
`((FiniteEtaleOver.isPreconnectedT2 X).ι.obj A).left`, the same by `rfl` and not reducibly so, so
instance search does not cross between them. **A `haveI` does not repair it and passing the
fields positionally does.** -/
instance FiniteEtaleOver.reflectsIsomorphisms_fiberFunctor {X : AnalyticSpace.{u}}
    [PreconnectedSpace (X : Type u)] (x : X) :
    ((FiniteEtaleOver.isPreconnectedT2.{u} X).ι
      ⋙ FiniteEtaleOver.fiberFunctor.{u} x).ReflectsIsomorphisms where
  reflects {A B} f h := by
    haveI : IsIso ((FiniteEtaleOver.fiberFunctor.{u} x).map
      ((FiniteEtaleOver.isPreconnectedT2 X).ι.map f)) := h
    have hb : Function.Bijective (FiniteEtaleOver.fiberMap.{u} x
        ((FiniteEtaleOver.isPreconnectedT2 X).ι.map f)) :=
      (isIso_iff_bijective (X := FiniteEtaleOver.fiber.{u} x A.obj) _).mp this
    haveI : IsIso ((FiniteEtaleOver.isPreconnectedT2.{u} X).ι.map f) :=
      @FiniteEtaleOver.isIso_of_bijective_fiberMap X A.obj B.obj _
        A.property.2 B.property.2 B.property.1 ‹_› x hb
    exact isIso_of_reflects_iso f (FiniteEtaleOver.isPreconnectedT2.{u} X).ι

/-- **The same for the `FintypeCat`-valued fibre functor**, which is the one a Galois category
asks for.

**Not derived from the `Type u`-valued instance above and not a restatement of it**, for the
reason `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fintypeFiberFunctor_map_injective` gives
about its own pair: the two functors have the same `map` up to the bundling their targets ask for
— `TypeCat.ofHom` there and `FintypeCat.homMk` here — so `IsIso` of one is not `IsIso` of the
other, and the bijectivity has to be read off through the concrete-category forgetful functor,
`CategoryTheory.ConcreteCategory.isIso_iff_bijective`, rather than through
`CategoryTheory.isIso_iff_bijective`. **The forgetful functor that reads it off and
`FintypeCat.incl` are the same functor and not two**: at the Mathlib revision `lakefile.toml`
pins, `FintypeCat.incl` is `CategoryTheory.forget FintypeCat` by `rfl` at every universe, which
is why `Mathlib/CategoryTheory/FintypeCat.lean` can hand the forgetful functor its
`CategoryTheory.Functor.Full` instance by `inferInstanceAs` from `FintypeCat.incl`'s. **What
those two spellings do not make interchangeable is
`CategoryTheory.ConcreteCategory.isIso_iff_bijective` and `CategoryTheory.isIso_iff_bijective`**,
which differ in which category's `CategoryTheory.IsIso` they read and not in which functor
forgets. -/
instance FiniteEtaleOver.reflectsIsomorphisms_fintypeFiberFunctor {X : AnalyticSpace.{u}}
    [PreconnectedSpace (X : Type u)] (x : X) :
    ((FiniteEtaleOver.isPreconnectedT2.{u} X).ι
      ⋙ FiniteEtaleOver.fintypeFiberFunctor.{u} x).ReflectsIsomorphisms where
  reflects {A B} f h := by
    haveI : IsIso ((FiniteEtaleOver.fintypeFiberFunctor.{u} x).map
        ((FiniteEtaleOver.isPreconnectedT2 X).ι.map f)) := h
    have hb : Function.Bijective (FiniteEtaleOver.fiberMap.{u} x
        ((FiniteEtaleOver.isPreconnectedT2 X).ι.map f)) :=
      (ConcreteCategory.isIso_iff_bijective ((FiniteEtaleOver.fintypeFiberFunctor.{u} x).map
        ((FiniteEtaleOver.isPreconnectedT2 X).ι.map f))).mp this
    haveI : IsIso ((FiniteEtaleOver.isPreconnectedT2.{u} X).ι.map f) :=
      @FiniteEtaleOver.isIso_of_bijective_fiberMap X A.obj B.obj _
        A.property.2 B.property.2 B.property.1 ‹_› x hb
    exact isIso_of_reflects_iso f (FiniteEtaleOver.isPreconnectedT2.{u} X).ι

/-! ### Finite coproducts of covers -/

/-- **The disjoint union of a finite family of covers, as a cover of the same base.**

`ComplexAnalytic.AnalyticSpace.sigmaDesc` of the members' structure maps, which is finite étale by
`ComplexAnalytic.AnalyticSpace.isFiniteEtale_sigmaDesc`. That instance asks the index type to be
finite, and asks each member's structure map to be finite étale — which is what an object of this
category carries in its `prop` field.

**The `prop` fields are passed positionally with `@`, and that is not decoration.** Introducing
them as `haveI : ∀ i, IsFiniteEtale (A i).hom := fun i ↦ (A i).prop` and then leaving
`ComplexAnalytic.AnalyticSpace.isFiniteEtale_sigmaDesc`'s instance argument to be synthesised
fails with *"failed to synthesize instance of type class `∀ (i : ι), IsFiniteEtale (A i).hom`"* —
on the hypothesis introduced one line above it. That is the seam
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.faithful_fiberFunctor` records, cured the same way.

**And `inferInstance` cannot be asked for the `prop` field either**, for an independent reason:
the object property of this comma category is `ComplexAnalytic.AnalyticSpace.isFiniteEtale`, the
`def` that exists to carry a head symbol, so what the field states is not a class application at
all — the elaborator answers `type class instance expected` — however much
`ComplexAnalytic.AnalyticSpace.isFiniteEtale_iff` makes it `Iff.rfl` to one. -/
noncomputable def FiniteEtaleOver.sigma {X : AnalyticSpace.{u}} {ι : Type u} [Finite ι]
    (A : ι → FiniteEtaleOver.{u} X) : FiniteEtaleOver.{u} X :=
  MorphismProperty.Over.mk _
    (AnalyticSpace.sigmaDesc (fun i ↦ (A i).left) fun i ↦ (A i).hom)
    (@isFiniteEtale_sigmaDesc ι (fun i ↦ (A i).left) X (fun i ↦ (A i).hom) ‹_›
      fun i ↦ (A i).prop)

/-- **The inclusion of a member into the disjoint union**, as a morphism of covers.

`ComplexAnalytic.AnalyticSpace.sigmaι` underneath, and the triangle over the base is
`ComplexAnalytic.AnalyticSpace.sigmaι_sigmaDesc`: what the descent map restricts to on a member is
that member's structure map. A morphism of this category is asked for nothing beyond the triangle,
`Q` being `⊤`, so `ComplexAnalytic.AnalyticSpace.isFiniteEtale_sigmaι` is **not** read here — that
lemma is what would make an inclusion an object of a comma category over the disjoint union, which
is a different statement about a different base.

**The `⊤` argument is left to its autoParam rather than written out.** Spelling it `trivial` does
not compile: inside a declaration whose name begins
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver`, that identifier resolves to
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.trivial`, and the error message names that
declaration's type rather than `True`. -/
noncomputable def FiniteEtaleOver.sigmaι {X : AnalyticSpace.{u}} {ι : Type u} [Finite ι]
    (A : ι → FiniteEtaleOver.{u} X) (j : ι) : A j ⟶ FiniteEtaleOver.sigma A :=
  MorphismProperty.Over.homMk (AnalyticSpace.sigmaι (fun i ↦ (A i).left) j)
    (AnalyticSpace.sigmaι_sigmaDesc _ _ j)

/-- **The inclusions of the members, read as a cofan on the disjoint union of covers.**

There is no content: the declaration exists because
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isColimitCofanSigma` has to name the cocone it says
is a colimit, and because `CategoryTheory.Limits.Cofan.inj` is how that statement presents the
inclusions. It is `ComplexAnalytic.AnalyticSpace.cofanSigma` one level up. -/
noncomputable def FiniteEtaleOver.cofanSigma {X : AnalyticSpace.{u}} {ι : Type u} [Finite ι]
    (A : ι → FiniteEtaleOver.{u} X) : Limits.Cofan A :=
  Limits.Cofan.mk (FiniteEtaleOver.sigma A) (FiniteEtaleOver.sigmaι A)

/-- **The disjoint union of finitely many covers is their coproduct in the category of covers.**

**The mathematics is `Oka/AnalyticSpace/Sigma.lean`'s and this adds none of it.**
`ComplexAnalytic.AnalyticSpace.sigmaDesc` supplies the descent map,
`ComplexAnalytic.AnalyticSpace.sigmaι_sigmaDesc` is the factorisation field and
`ComplexAnalytic.AnalyticSpace.hom_ext_sigma` is the uniqueness field. What is done here is
re-reading each of those as a statement about morphisms **over the base**, which is
`CategoryTheory.MorphismProperty.Over.homMk` for the descent map,
`CategoryTheory.MorphismProperty.Over.Hom.ext` for an equality of morphisms of covers and
`CategoryTheory.MorphismProperty.Over.w` for the triangle a morphism of covers commutes.

**`ComplexAnalytic.AnalyticSpace.isColimitCofanSigma` is not read here**, although it is this
statement one level down. The descent map has to be re-wrapped as a morphism over the base in any
case, and once it is there is nothing left for that bundle to carry;
`ComplexAnalytic.AnalyticSpace.sigmaι_sigmaDesc` and
`ComplexAnalytic.AnalyticSpace.hom_ext_sigma` are what this proof reads instead.

**Every field is a term and none is a tactic**, and some citations of
`ComplexAnalytic.AnalyticSpace.sigmaι_sigmaDesc` have their arguments written out where the rest
leave them to unification. Where they are written out, the unifier would otherwise have to see
through `CategoryTheory.MorphismProperty.Over.homMk`'s underlying morphism, or through the cofan's
apex, to a `ComplexAnalytic.AnalyticSpace.sigmaDesc`, and it reports the mismatch with its
metavariables still in it. This is the seam `Oka/AnalyticSpace/Sigma.lean`'s
`## One seam, and it is not the one it looks like` describes, at one more layer of wrapping. -/
noncomputable def FiniteEtaleOver.isColimitCofanSigma {X : AnalyticSpace.{u}} {ι : Type u}
    [Finite ι] (A : ι → FiniteEtaleOver.{u} X) :
    Limits.IsColimit (FiniteEtaleOver.cofanSigma A) :=
  Limits.Cofan.IsColimit.mk _
    (fun t ↦ MorphismProperty.Over.homMk
      (AnalyticSpace.sigmaDesc (fun i ↦ (A i).left) fun i ↦ (t.inj i).left)
      (AnalyticSpace.hom_ext_sigma _ fun i ↦
        (Category.assoc _ _ _).symm.trans
          (((congrArg (· ≫ t.pt.hom) (AnalyticSpace.sigmaι_sigmaDesc _ _ i)).trans
            (MorphismProperty.Over.w (t.inj i))).trans
            (AnalyticSpace.sigmaι_sigmaDesc (fun i ↦ (A i).left)
              (fun i ↦ (A i).hom) i).symm)))
    (fun _ i ↦ MorphismProperty.Over.Hom.ext (AnalyticSpace.sigmaι_sigmaDesc _ _ i))
    (fun t _ h ↦ MorphismProperty.Over.Hom.ext <|
      AnalyticSpace.hom_ext_sigma _ fun i ↦
        (congrArg (fun f : A i ⟶ t.pt ↦ f.left) (h i)).trans
          (AnalyticSpace.sigmaι_sigmaDesc (fun i ↦ (A i).left)
            (fun i ↦ (t.inj i).left) i).symm)

/-- **So the category of covers has colimits of every discrete shape indexed by a finite type of
its own universe.**

`CategoryTheory.Limits.hasCoproducts_of_colimit_cofans` is what does this at
`ComplexAnalytic.AnalyticSpace`, and it is unavailable here: it asks for a cofan and a colimit
proof at **every** index type of a universe, and a disjoint union of covers is a cover only at a
finite one. What is written out instead is that converter's own body at one index type —
`CategoryTheory.Limits.Cocone.precompose` at `CategoryTheory.Discrete.natIsoFunctor`, which is
what turns an arbitrary functor out of a discrete category into the family of objects it is
determined by.

**A `theorem` and not an `instance`, and that was measured rather than argued.**
`Mathlib/CategoryTheory/Limits/Shapes/FiniteProducts.lean` derives
`CategoryTheory.Limits.HasColimitsOfShape` at a discrete shape on a finite index type from
`CategoryTheory.Limits.HasFiniteCoproducts`, at every universe rather than only at this
category's own, so declaring this an instance too would add nothing that instance search cannot
already do once
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.hasFiniteCoproducts` is in scope. Checked by
elaborating `inferInstance` at that statement with this declaration left a `theorem`, rather than
read off the shapes. -/
theorem FiniteEtaleOver.hasColimitsOfShape_discrete (ι : Type u) [Finite ι]
    (X : AnalyticSpace.{u}) :
    Limits.HasColimitsOfShape (Discrete ι) (FiniteEtaleOver.{u} X) where
  has_colimit F := Limits.HasColimit.mk
    ⟨(Limits.Cocone.precompose Discrete.natIsoFunctor.hom).obj
      (FiniteEtaleOver.cofanSigma fun j ↦ F.obj ⟨j⟩),
      (Limits.IsColimit.precomposeHomEquiv _ _).symm (FiniteEtaleOver.isColimitCofanSigma _)⟩

/-- **The category of finite étale covers has finite coproducts**, with no hypothesis on the base.

**This is a Galois-category axiom on the category**, as
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.hasTerminal` is: the definition in
`Mathlib/CategoryTheory/Galois/Basic.lean`, whose namespace is not in this file's import
closure and so cannot be cited by name here, carries a field of exactly this class at exactly this
category. `Oka/AnalyticSpace/Sigma.lean` states the same class of
`ComplexAnalytic.AnalyticSpace` itself and says there that what it holds is the ingredient the
axiom would be built from; this is where that ingredient is built into one.

**The universe crossing is the whole of the step and it is not free.**
`CategoryTheory.Limits.HasFiniteCoproducts` quantifies over `Fin n`, which lives in `Type 0`,
while `ComplexAnalytic.AnalyticSpace.sigma` takes its index type from `Type u`.
`CategoryTheory.Discrete.equivalence` at `Equiv.ulift` is what crosses between them, and it is the
step `CategoryTheory.Limits.hasFiniteCoproducts_of_hasCoproducts` also takes — that converter
itself being unusable here for the reason
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.hasColimitsOfShape_discrete` gives.

**What this does not say is that the category is a Galois category.** Base change of the class
over a general cospan is absent, and so are quotients by finite group actions and the axiom that a
monomorphism induces an isomorphism onto a direct summand; `## What is not here` says so, and this
instance shortens that list by a member rather than emptying it. **This sentence read *Base change
is absent* until `Oka/AnalyticSpace/PullbackOpen.lean` exhibited the pullback along the inclusion
of an open subspace and carried `isFiniteEtale` across it**; that is not a cospan a Galois category
quantifies over, so the bullet cited here is narrowed rather than struck, and so is this. **And it
read *Base change over a general cospan is absent* until 2026-09-08**, when
`Oka/AnalyticSpace/PullbackReduction.lean` supplied the fibre product over exactly such a cospan
and not the class across it. Both narrowings are the ones the bullet took. -/
instance FiniteEtaleOver.hasFiniteCoproducts (X : AnalyticSpace.{u}) :
    Limits.HasFiniteCoproducts (FiniteEtaleOver.{u} X) :=
  ⟨fun n ↦
    haveI := FiniteEtaleOver.hasColimitsOfShape_discrete (ULift.{u} (Fin n)) X
    Limits.hasColimitsOfShape_of_equivalence (Discrete.equivalence Equiv.ulift.{u})⟩

/-! ### The fibre functors preserve finite coproducts -/

/-- **The fibre of a disjoint union of covers is the disjoint union of the fibres**, as an
equivalence of types.

**This is where the mathematics of the section is, and none of it is written here.**
`AlgebraicGeometry.LocallyRingedSpace.fiberSigmaDescEquiv`
(`Oka/Geometry/RingedSpace/LocallyRingedSpace/HasColimits.lean`) is the statement for a descent map
of locally ringed spaces, and `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.sigma`'s structure map
is `ComplexAnalytic.AnalyticSpace.sigmaDesc`, whose underlying morphism is that descent map. So the
declaration is that equivalence read at this comma category, and the finite étale property is not
consulted: the equivalence holds at every object of `CategoryTheory.MorphismProperty.Over` whatever
the property is, exactly as `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fiber` does.

**The target of the family has to be written as `(Y := X.toLocallyRingedSpace)`.** Left to
unification the elaborator has no way to see through
`ComplexAnalytic.AnalyticSpace.Hom.toLRSHom` to a target before it has the family, and reports a
type mismatch with the family's own metavariable still standing in the statement it prints. -/
noncomputable def FiniteEtaleOver.fiberSigmaEquiv {X : AnalyticSpace.{u}} {ι : Type u} [Finite ι]
    (A : ι → FiniteEtaleOver.{u} X) (x : X) :
    (Σ i, FiniteEtaleOver.fiber.{u} x (A i)) ≃
      FiniteEtaleOver.fiber.{u} x (FiniteEtaleOver.sigma A) :=
  AlgebraicGeometry.LocallyRingedSpace.fiberSigmaDescEquiv
    (fun i ↦ (A i).left.toLocallyRingedSpace)
    (Y := X.toLocallyRingedSpace) (fun i ↦ (A i).hom.toLRSHom) x

/-- **What the equivalence does to a point of a member's fibre is what the fibre functor does to
it along the inclusion of that member.**

`rfl`, and it is the compatibility the colimit statement below is made of: the forward map of
`AlgebraicGeometry.LocallyRingedSpace.fiberSigmaDescEquiv` is composition with the coproduct
inclusion, `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.sigmaι`'s underlying morphism is that
inclusion, and `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fiberMap` is composition with the
underlying morphism.

**Stated at the functor rather than at
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fiberMap`**, because that is the spelling the
colimit fields present: `CategoryTheory.Limits.Cofan.inj` of the mapped cofan is
`CategoryTheory.Functor.map` and a lemma about the underlying map does not rewrite there. -/
theorem FiniteEtaleOver.fiberSigmaEquiv_apply {X : AnalyticSpace.{u}} {ι : Type u} [Finite ι]
    (A : ι → FiniteEtaleOver.{u} X) (x : X) (i : ι) (a : FiniteEtaleOver.fiber.{u} x (A i)) :
    FiniteEtaleOver.fiberSigmaEquiv A x ⟨i, a⟩
      = (FiniteEtaleOver.fiberFunctor.{u} x).map (FiniteEtaleOver.sigmaι A i) a := rfl

/-- **The same compatibility for the `FintypeCat`-valued fibre functor.**

`rfl` again, and it is a separate declaration rather than a corollary because the two statements
are equalities in types that are the same only up to `FintypeCat.of`: the value of
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fintypeFiberFunctor` is a bundled finite type and
the value of `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fiberFunctor` is the type itself, so a
rewrite by one of them inside a cofan over the other does not fire. -/
theorem FiniteEtaleOver.fiberSigmaEquiv_apply_fintypeFiberFunctor {X : AnalyticSpace.{u}}
    {ι : Type u} [Finite ι] (A : ι → FiniteEtaleOver.{u} X) (x : X) (i : ι)
    (a : FiniteEtaleOver.fiber.{u} x (A i)) :
    FiniteEtaleOver.fiberSigmaEquiv A x ⟨i, a⟩
      = (FiniteEtaleOver.fintypeFiberFunctor.{u} x).map (FiniteEtaleOver.sigmaι A i) a := rfl

/-- **The fibre functor carries the cofan of the inclusions to a colimit cofan in `Type u`.**

The apex is the fibre of the disjoint union, the inclusions are the fibre functor's action on
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.sigmaι`, and the content is that
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fiberSigmaEquiv` is a bijection whose forward map is
that action.

**Both fields other than the descent map are `congrArg` at
`fun q ↦ t.inj q.1 q.2`, and that is not a stylistic choice.** The obvious proof rewrites by the
equivalence in the goal, and **the redex is not in the goal to rewrite**: it sits inside
`ConcreteCategory.hom (↾fun p ↦ …)`, and in the factorisation field under a `≫` as well, so `rw`
reports *did not find an occurrence of the pattern* and prints the goal back with the coercion
still around it. **Unfolding the coercion does not expose it either** — after
`dsimp only [TypeCat.ofHom, ConcreteCategory.hom]` the target is no longer type-correct at
instance transparency and `simp` then makes no progress. `congrArg` builds the equality where the
redex is, in the argument, and then the whole of each field is one term.

**What is not the obstruction is that `q.2`'s type depends on `q.1`, and this paragraph used to
say it was.** Written out at the field's own shape, with both projections taken of one subterm,
`rw [Equiv.symm_apply_apply]` closes the goal and reports nothing: `rw` generalises the whole
subterm, so the motive is `fun z ↦ t.inj z.1 z.2 = …` and is perfectly constructible. The
dependency is real and it is not what stops the tactic; the coercion is. -/
noncomputable def FiniteEtaleOver.isColimitFiberCofanSigma {X : AnalyticSpace.{u}} {ι : Type u}
    [Finite ι] (A : ι → FiniteEtaleOver.{u} X) (x : X) :
    Limits.IsColimit
      (Limits.Cofan.mk ((FiniteEtaleOver.fiberFunctor.{u} x).obj (FiniteEtaleOver.sigma A))
        (fun i ↦ (FiniteEtaleOver.fiberFunctor.{u} x).map (FiniteEtaleOver.sigmaι A i)) :
          Limits.Cofan fun i ↦ (FiniteEtaleOver.fiberFunctor.{u} x).obj (A i)) := by
  refine Limits.Cofan.IsColimit.mk _
    (fun t ↦ TypeCat.ofHom fun p ↦ t.inj ((FiniteEtaleOver.fiberSigmaEquiv A x).symm p).1
      ((FiniteEtaleOver.fiberSigmaEquiv A x).symm p).2) (fun t i ↦ ?_) (fun t m hm ↦ ?_)
  · ext a
    exact congrArg (fun q : Σ i, FiniteEtaleOver.fiber.{u} x (A i) ↦ t.inj q.1 q.2)
      ((Equiv.symm_apply_eq _).2 (FiniteEtaleOver.fiberSigmaEquiv_apply A x i a).symm)
  · ext p
    obtain ⟨⟨i, a⟩, rfl⟩ := (FiniteEtaleOver.fiberSigmaEquiv A x).surjective p
    refine Eq.trans ?_ (congrArg (fun q : Σ i, FiniteEtaleOver.fiber.{u} x (A i) ↦ t.inj q.1 q.2)
      ((FiniteEtaleOver.fiberSigmaEquiv A x).symm_apply_apply ⟨i, a⟩)).symm
    exact congrArg (fun f : (FiniteEtaleOver.fiberFunctor.{u} x).obj (A i) ⟶ t.pt ↦ f a) (hm i)

/-- **The same statement for the `FintypeCat`-valued fibre functor.**

`FintypeCat.homMk` in place of `TypeCat.ofHom` and
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fiberSigmaEquiv_apply_fintypeFiberFunctor` in place
of `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fiberSigmaEquiv_apply`; the rest of the proof is
the same term, since `FintypeCat.homMk_apply` and `TypeCat.ofHom`'s application are both `rfl` and
neither field ever looks at the bundling.

**No finiteness is checked and none has to be.** The cofan's apex is
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fintypeFiberFunctor`'s value, whose finiteness is
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.finite_fiber` and is already discharged in the
functor. -/
noncomputable def FiniteEtaleOver.isColimitFintypeFiberCofanSigma {X : AnalyticSpace.{u}}
    {ι : Type u} [Finite ι] (A : ι → FiniteEtaleOver.{u} X) (x : X) :
    Limits.IsColimit
      (Limits.Cofan.mk ((FiniteEtaleOver.fintypeFiberFunctor.{u} x).obj (FiniteEtaleOver.sigma A))
        (fun i ↦ (FiniteEtaleOver.fintypeFiberFunctor.{u} x).map (FiniteEtaleOver.sigmaι A i)) :
          Limits.Cofan fun i ↦ (FiniteEtaleOver.fintypeFiberFunctor.{u} x).obj (A i)) := by
  refine Limits.Cofan.IsColimit.mk _
    (fun t ↦ FintypeCat.homMk fun p ↦ t.inj ((FiniteEtaleOver.fiberSigmaEquiv A x).symm p).1
      ((FiniteEtaleOver.fiberSigmaEquiv A x).symm p).2) (fun t i ↦ ?_) (fun t m hm ↦ ?_)
  · ext a
    exact congrArg (fun q : Σ i, FiniteEtaleOver.fiber.{u} x (A i) ↦ t.inj q.1 q.2)
      ((Equiv.symm_apply_eq _).2
        (FiniteEtaleOver.fiberSigmaEquiv_apply_fintypeFiberFunctor A x i a).symm)
  · ext p
    obtain ⟨⟨i, a⟩, rfl⟩ := (FiniteEtaleOver.fiberSigmaEquiv A x).surjective p
    refine Eq.trans ?_ (congrArg (fun q : Σ i, FiniteEtaleOver.fiber.{u} x (A i) ↦ t.inj q.1 q.2)
      ((FiniteEtaleOver.fiberSigmaEquiv A x).symm_apply_apply ⟨i, a⟩)).symm
    exact congrArg (fun f : (FiniteEtaleOver.fintypeFiberFunctor.{u} x).obj (A i) ⟶ t.pt ↦ f a)
      (hm i)

/-- **So the fibre functor preserves colimits of every discrete shape indexed by a finite type of
this category's own universe.**

The colimit statement above is about one cocone on one family, and
`CategoryTheory.Limits.PreservesColimitsOfShape` is about every functor out of the discrete
category. `CategoryTheory.Limits.preservesColimit_of_preserves_colimit_cocone` at
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isColimitCofanSigma` is the first step, with
`CategoryTheory.Limits.isColimitMapCoconeCofanMkEquiv` the bridge between a mapped cocone and a
cofan on the mapped family; `CategoryTheory.Discrete.natIsoFunctor` and
`CategoryTheory.Limits.preservesColimit_of_iso_diagram` are the second, carrying it from the family
`K` is determined by to `K` itself. -/
instance FiniteEtaleOver.preservesColimitsOfShape_fiberFunctor (ι : Type u) [Finite ι]
    {X : AnalyticSpace.{u}} (x : X) :
    Limits.PreservesColimitsOfShape (Discrete ι) (FiniteEtaleOver.fiberFunctor.{u} x) where
  preservesColimit {K} := by
    haveI : Limits.PreservesColimit (Discrete.functor (K.obj ∘ Discrete.mk))
        (FiniteEtaleOver.fiberFunctor.{u} x) :=
      Limits.preservesColimit_of_preserves_colimit_cocone
        (FiniteEtaleOver.isColimitCofanSigma (K.obj ∘ Discrete.mk))
        ((Limits.isColimitMapCoconeCofanMkEquiv _ _ _).symm
          (FiniteEtaleOver.isColimitFiberCofanSigma (K.obj ∘ Discrete.mk) x))
    exact Limits.preservesColimit_of_iso_diagram _ Discrete.natIsoFunctor.symm

/-- **The same for the `FintypeCat`-valued fibre functor**, by the same two steps at
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isColimitFintypeFiberCofanSigma`. -/
instance FiniteEtaleOver.preservesColimitsOfShape_fintypeFiberFunctor (ι : Type u)
    [Finite ι] {X : AnalyticSpace.{u}} (x : X) :
    Limits.PreservesColimitsOfShape (Discrete ι) (FiniteEtaleOver.fintypeFiberFunctor.{u} x) where
  preservesColimit {K} := by
    haveI : Limits.PreservesColimit (Discrete.functor (K.obj ∘ Discrete.mk))
        (FiniteEtaleOver.fintypeFiberFunctor.{u} x) :=
      Limits.preservesColimit_of_preserves_colimit_cocone
        (FiniteEtaleOver.isColimitCofanSigma (K.obj ∘ Discrete.mk))
        ((Limits.isColimitMapCoconeCofanMkEquiv _ _ _).symm
          (FiniteEtaleOver.isColimitFintypeFiberCofanSigma (K.obj ∘ Discrete.mk) x))
    exact Limits.preservesColimit_of_iso_diagram _ Discrete.natIsoFunctor.symm

/-- **The fibre functor preserves finite coproducts**, with no hypothesis on the base and none on
the point.

**This is a Galois-category axiom on the fibre functor**, as
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.preservesLimitsOfShape_pempty_fiberFunctor` is: the
class of a fibre functor in `Mathlib/CategoryTheory/Galois/Basic.lean`, whose namespace is not in
this file's import closure and so cannot be cited by name here, carries a field of exactly
this class.

**The universe crossing is the same one
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.hasFiniteCoproducts` takes and it is there for the
same reason.** `CategoryTheory.Limits.PreservesFiniteCoproducts` quantifies over `Fin n`, which
lives in `Type 0`, and the instance above is at an index type of this category's own universe;
`CategoryTheory.Discrete.equivalence` at `Equiv.ulift` and
`CategoryTheory.Limits.preservesColimitsOfShape_of_equiv` cross between them. -/
instance FiniteEtaleOver.preservesFiniteCoproducts_fiberFunctor {X : AnalyticSpace.{u}} (x : X) :
    Limits.PreservesFiniteCoproducts (FiniteEtaleOver.fiberFunctor.{u} x) where
  preserves n :=
    haveI := FiniteEtaleOver.preservesColimitsOfShape_fiberFunctor (ULift.{u} (Fin n)) x
    Limits.preservesColimitsOfShape_of_equiv (Discrete.equivalence Equiv.ulift.{u}) _

/-- **And the `FintypeCat`-valued fibre functor preserves finite coproducts**, which is the axiom
at the functor a Galois category asks for.

**What this does not say is that the category is a Galois category and this functor a fibre
functor for it.** Base change of the class over a general cospan is absent, and so are quotients by
finite group actions, the axiom that a monomorphism induces an isomorphism onto a direct summand,
and the preservation of epimorphisms; `## What is not here` says so, and what this instance takes
out of the set of absent axioms is the preservation of finite coproducts. **This sentence read
*Base change is absent* until `Oka/AnalyticSpace/PullbackOpen.lean` exhibited the pullback along
the inclusion of an open subspace**, which is not a cospan a Galois category quantifies over; and
it read *Base change over a general cospan is absent* until 2026-09-08, when
`Oka/AnalyticSpace/PullbackReduction.lean` supplied the fibre product over exactly such a cospan
and not the class across it. Both narrowings are the ones the bullet took. -/
instance FiniteEtaleOver.preservesFiniteCoproducts_fintypeFiberFunctor {X : AnalyticSpace.{u}}
    (x : X) : Limits.PreservesFiniteCoproducts (FiniteEtaleOver.fintypeFiberFunctor.{u} x) where
  preserves n :=
    haveI := FiniteEtaleOver.preservesColimitsOfShape_fintypeFiberFunctor
      (ULift.{u} (Fin n)) x
    Limits.preservesColimitsOfShape_of_equiv (Discrete.equivalence Equiv.ulift.{u}) _

/-- **A cover restricted to a clopen subset of its total space is again a cover**, with no
hypothesis on the base, on the cover, or on the subset beyond that its carrier is closed.

The structure map is the inclusion of the open subspace followed by the cover's own, and
`ComplexAnalytic.AnalyticSpace.isFiniteEtale_ofRestrict_comp` is what makes the composite finite
étale. **Nothing is cancelled anywhere**, which is why no `[T2Space]` appears: the Hausdorff
hypothesis in this development belongs to
`ComplexAnalytic.AnalyticSpace.isFiniteEtale_of_comp`, and going the composition way never asks
for it.

**Why the property is passed as an explicit argument rather than found.** `A.hom`'s type is
spelled `(CategoryTheory.Functor.id _).obj A.left ⟶ (CategoryTheory.Functor.fromPUnit X).obj
A.right`, so the `ComplexAnalytic.AnalyticSpace.IsFiniteEtale` in `A.prop` carries those terms in
its implicit arguments; they are `rfl`-equal to the readable spellings and are different
discrimination-tree keys. Instance search therefore cannot use a hypothesis that prints exactly
like the goal, and the cited lemma exists in the shape it does so that `A.prop` can be handed to
it by unification instead. -/
noncomputable def FiniteEtaleOver.restrictClopen {X : AnalyticSpace.{u}}
    (A : FiniteEtaleOver.{u} X) (U : A.left.Opens) (hU : IsClosed (U : Set A.left)) :
    FiniteEtaleOver.{u} X :=
  MorphismProperty.Over.mk _ (A.left.ofRestrict U ≫ A.hom)
    (isFiniteEtale_ofRestrict_comp U hU A.hom A.prop)

/-- The total space of `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.restrictClopen` is the open
subspace itself. -/
@[simp]
lemma FiniteEtaleOver.restrictClopen_left {X : AnalyticSpace.{u}} (A : FiniteEtaleOver.{u} X)
    (U : A.left.Opens) (hU : IsClosed (U : Set A.left)) :
    (A.restrictClopen U hU).left = A.left.restrict U :=
  rfl

/-- The structure map of `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.restrictClopen` is the
inclusion followed by the original structure map. -/
lemma FiniteEtaleOver.restrictClopen_hom {X : AnalyticSpace.{u}} (A : FiniteEtaleOver.{u} X)
    (U : A.left.Opens) (hU : IsClosed (U : Set A.left)) :
    (A.restrictClopen U hU).hom = A.left.ofRestrict U ≫ A.hom :=
  rfl

/-- **The inclusion of a clopen part of a cover, as a morphism of covers.**

The triangle over the base is `rfl`, and that is the whole reason
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.restrictClopen`'s structure map was written as
that composite in that order rather than assembled any other way: a morphism of covers is a
morphism of total spaces together with the commuting triangle, and here the triangle is the
definition of the target's structure map read backwards. -/
noncomputable def FiniteEtaleOver.restrictClopenι {X : AnalyticSpace.{u}}
    (A : FiniteEtaleOver.{u} X) (U : A.left.Opens) (hU : IsClosed (U : Set A.left)) :
    A.restrictClopen U hU ⟶ A :=
  MorphismProperty.Over.homMk (A.left.ofRestrict U) rfl

/-- The underlying morphism of
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.restrictClopenι` is the open-subspace inclusion. -/
@[simp]
lemma FiniteEtaleOver.restrictClopenι_left {X : AnalyticSpace.{u}} (A : FiniteEtaleOver.{u} X)
    (U : A.left.Opens) (hU : IsClosed (U : Set A.left)) :
    (A.restrictClopenι U hU).left = A.left.ofRestrict U :=
  rfl

/-- **The complementary clopen part of a cover**, which is
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.restrictClopen` at
`ComplexAnalytic.AnalyticSpace.clopenCompl`.

**This is the object a direct-summand statement would need as its complement.** The Galois-category
definition in `Mathlib/CategoryTheory/Galois/Basic.lean` asks, of a monomorphism `i : A ⟶ B`, for an
object `Z` and a morphism `Z ⟶ B` exhibiting `B` as the binary coproduct of the two; when `i`'s
image is a clopen subset of `B`'s total space, this is that `Z`. **That definition cannot be cited
by name here**, being outside this file's import closure, which is the spelling this file already
uses for it.

**That the two together are that coproduct is
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isColimitBinaryCofanRestrictClopen`**, below. This
paragraph used to say the statement was absent, and `## What is not here` records which of the
axiom's obligations are still open once it is there. -/
noncomputable def FiniteEtaleOver.restrictClopenCompl {X : AnalyticSpace.{u}}
    (A : FiniteEtaleOver.{u} X) (U : A.left.Opens) (hU : IsClosed (U : Set A.left)) :
    FiniteEtaleOver.{u} X :=
  A.restrictClopen (clopenCompl U hU) (isClosed_clopenCompl U hU)

/-- **The inclusion of the complementary clopen part of a cover.**

`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.restrictClopenι` at
`ComplexAnalytic.AnalyticSpace.clopenCompl`, exactly as
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.restrictClopenCompl` is
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.restrictClopen` there. It carries no content and
exists so that `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.binaryCofanRestrictClopen` can name
its second injection, and so that a caller can cite it without writing out the closedness of the
complement each time. -/
noncomputable def FiniteEtaleOver.restrictClopenComplι {X : AnalyticSpace.{u}}
    (A : FiniteEtaleOver.{u} X) (U : A.left.Opens) (hU : IsClosed (U : Set A.left)) :
    A.restrictClopenCompl U hU ⟶ A :=
  A.restrictClopenι (clopenCompl U hU) (isClosed_clopenCompl U hU)

/-- **The two inclusions, read as a cocone on the pair of clopen parts.**

There is no content: the declaration exists because
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isColimitBinaryCofanRestrictClopen` has to name the
cocone it says is a colimit, and because `CategoryTheory.Limits.BinaryCofan.inl` and
`CategoryTheory.Limits.BinaryCofan.inr` are how that statement presents the two injections. It
stands to that theorem as `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.cofanSigma` stands to
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isColimitCofanSigma`. -/
noncomputable def FiniteEtaleOver.binaryCofanRestrictClopen {X : AnalyticSpace.{u}}
    (A : FiniteEtaleOver.{u} X) (U : A.left.Opens) (hU : IsClosed (U : Set A.left)) :
    Limits.BinaryCofan (A.restrictClopen U hU) (A.restrictClopenCompl U hU) :=
  Limits.BinaryCofan.mk (A.restrictClopenι U hU) (A.restrictClopenComplι U hU)

/-- **A cover is the coproduct of a clopen part of its total space and the complementary part.**

**The mathematics is `Oka/AnalyticSpace/Clopen.lean`'s and this adds none of it.**
`ComplexAnalytic.AnalyticSpace.descClopen` supplies the descent map,
`ComplexAnalytic.AnalyticSpace.ofRestrict_descClopen` and
`ComplexAnalytic.AnalyticSpace.ofRestrict_clopenCompl_descClopen` are the two factorisation fields
and `ComplexAnalytic.AnalyticSpace.hom_ext_of_clopen` is the uniqueness field. What is done here is
re-reading each of those as a statement about morphisms **over the base**, which is
`CategoryTheory.MorphismProperty.Over.homMk` for the descent map,
`CategoryTheory.MorphismProperty.Over.Hom.ext` for an equality of morphisms of covers and
`CategoryTheory.MorphismProperty.Over.w` for the triangle a morphism of covers commutes.

**The triangle the descent map has to commute is itself an instance of the gluing**, and that is
the one step here that is not transcription: `ComplexAnalytic.AnalyticSpace.hom_ext_of_clopen`
compares the descent map followed by the target's structure map against this cover's own structure
map, and each half of that comparison reduces to
`CategoryTheory.MorphismProperty.Over.w` at the corresponding injection of the cocone.

**The remaining side of each half is closed by `exact` and not by `rw`, and that was measured.**
After `rw [← Category.assoc, ofRestrict_descClopen]` the goal is
`s.inl.left ≫ s.pt.hom = A.left.ofRestrict U ≫ A.hom`, while
`CategoryTheory.MorphismProperty.Over.w` at that injection proves
`s.inl.left ≫ s.pt.hom = (A.restrictClopen U hU).hom`. **The two right-hand sides are `rfl`-equal
and that equation is `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.restrictClopen_hom`**, so
`exact` at default transparency crosses the gap.

**Continuing the `rw` with that lemma rather than closing with `exact` fails**, and the failure is
worth recording because it is not about the mathematics. Planted at this declaration and read
back, replacing the first half's `exact` by a third rewrite step —
`rw [← Category.assoc, ofRestrict_descClopen, MorphismProperty.Over.w s.inl]` — reports

```
Did not find an occurrence of the pattern
  s.inl.left ≫ (((Functor.const (Discrete Limits.WalkingPair)).obj s.pt).obj
    { as := Limits.WalkingPair.left }).hom
in the target expression
  s.inl.left ≫ s.pt.hom = A.left.ofRestrict U ≫ A.hom
```

with the pattern on one line in the real message and wrapped here to fit. **The two sides of that
report are the same morphism spelled two ways**: `CategoryTheory.MorphismProperty.Over.w` states
its source through the diagram `CategoryTheory.Limits.pair` read at
`CategoryTheory.Limits.WalkingPair` and its target through `CategoryTheory.Functor.const` at the
cocone's point, while the goal states both through the projections of `s`. Under the failure Lean
adds that the target is not type-correct at `instances` transparency, and prints the application
type mismatch those two spellings make. `exact` at default transparency crosses that gap; `rw`,
which matches its pattern at `instances` transparency, does not.

**No hypothesis on the base, on the cover or on the subset beyond that its carrier is closed**, and
**no `[T2Space]` anywhere**: the gluing this reads is about open subspaces of an analytic space and
knows nothing about covers, and the separation axiom in this development belongs to
`ComplexAnalytic.AnalyticSpace.isFiniteEtale_of_comp`, which nothing here reaches. -/
noncomputable def FiniteEtaleOver.isColimitBinaryCofanRestrictClopen {X : AnalyticSpace.{u}}
    (A : FiniteEtaleOver.{u} X) (U : A.left.Opens) (hU : IsClosed (U : Set A.left)) :
    Limits.IsColimit (A.binaryCofanRestrictClopen U hU) :=
  Limits.BinaryCofan.isColimitMk
    (fun s ↦ MorphismProperty.Over.homMk
      (descClopen U hU s.inl.left s.inr.left)
      (hom_ext_of_clopen U hU
        (by
          rw [← Category.assoc, ofRestrict_descClopen]
          exact MorphismProperty.Over.w s.inl)
        (by
          rw [← Category.assoc, ofRestrict_clopenCompl_descClopen]
          exact MorphismProperty.Over.w s.inr)))
    (fun _ ↦ MorphismProperty.Over.Hom.ext (ofRestrict_descClopen U hU _ _))
    (fun _ ↦ MorphismProperty.Over.Hom.ext (ofRestrict_clopenCompl_descClopen U hU _ _))
    (fun s _ h₁ h₂ ↦ MorphismProperty.Over.Hom.ext
      (hom_ext_of_clopen U hU
        ((congrArg (fun f : A.restrictClopen U hU ⟶ s.pt ↦ f.left) h₁).trans
          (ofRestrict_descClopen U hU _ _).symm)
        ((congrArg (fun f : A.restrictClopenCompl U hU ⟶ s.pt ↦ f.left) h₂).trans
          (ofRestrict_clopenCompl_descClopen U hU _ _).symm)))

end ComplexAnalytic.AnalyticSpace
