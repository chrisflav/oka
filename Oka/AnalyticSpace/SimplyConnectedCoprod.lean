/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.AnalyticSpace.SimplyConnectedCriterion

/-!
# The coproduct form of the criterion, and the index type is never counted

`Oka/AnalyticSpace/SimplyConnected.lean` proves that a trivial fundamental group makes **every**
cover separated over the base a finite coproduct of copies of the base over itself
(`…SeparatedFiniteEtaleOver.exists_iso_coprod_id`), and
`Oka/AnalyticSpace/SimplyConnectedCriterion.lean` makes the *connected-cover* form of that
statement a criterion. **This file is the coproduct form run backwards**, which neither of them
has: from every cover being such a coproduct to the group being trivial, and so to a second
criterion whose right-hand side mentions no connectedness at all.

## Which condition each criterion asks of a consumer

The two `Iff`s differ in their right-hand side and in nothing else.

* `…SeparatedFiniteEtaleOver.subsingleton_fundamentalGroup_iff` asks for an isomorphism
  `A ≅ …SeparatedFiniteEtaleOver.id X` **for every `A` carrying
  `CategoryTheory.PreGaloisCategory.IsConnected`**, and so a consumer has to produce that instance
  before the condition is even stated at an object.
* `…SeparatedFiniteEtaleOver.subsingleton_fundamentalGroup_coprod_iff` below asks for a finite
  index type and an isomorphism with a coproduct **for every `A` whatever**, with no instance to
  discharge and no connected object to find.

**Neither implies the other by composition**, which is what makes this a file and not a corollary:
the first is about connected covers one at a time and the second quantifies over all of them, and
going from the second to the first is the whole of the middle theorem below.

## The prescription the sibling published for this, and why it is not what the proof needs

`Oka/AnalyticSpace/SimplyConnectedCriterion.lean`'s `## What is not here` priced this file, until
2026-09-21, at one statement: *what it needs and this file does not have is that a connected
object isomorphic to a finite coproduct of copies of a terminal object has a one-element index
type.*
**That statement is true and is not needed, and nothing below counts the index type.** What is used
instead is that a *coprojection* is a monomorphism: `CategoryTheory.Limits.MonoCoprod.mono_ι` at
the `CategoryTheory.Limits.MonoCoprod` instance `Mathlib/CategoryTheory/Galois/Basic.lean` declares
for every `CategoryTheory.GaloisCategory`, which makes
`CategoryTheory.Limits.Sigma.ι _ i ≫ e.inv` a mono into the connected object, after which
`CategoryTheory.PreGaloisCategory.IsConnected.noTrivialComponent` makes it an isomorphism outright.
The index type **is** a singleton whenever the hypothesis holds at a connected object, and that is
a consequence of the conclusion rather than a step towards it; it is not stated below because
nothing needs it.

**The retired clause is kept in that file as a dated record rather than struck**, which is this
repository's practice, and the repair there is to the prescription alone — *not here* is still true
of that file.

## The three steps, and only one of them takes a coproduct apart

1. **The index type is non-empty.** `…SeparatedFiniteEtaleOver.isInitialCoprodId` below says a
   coproduct over an empty index type is initial — `CategoryTheory.Limits.IsInitial.ofUniqueHom` at
   `CategoryTheory.Limits.Sigma.desc` and `CategoryTheory.Limits.Sigma.hom_ext`, **both of which
   quantify over the index type and so are discharged by `isEmptyElim` with no object of this
   repository in them** — and `CategoryTheory.PreGaloisCategory.IsConnected.notInitial` refuses
   that for a connected cover, through `CategoryTheory.Limits.IsInitial.ofIso`.
2. **The base over itself is not initial.** `…SeparatedFiniteEtaleOver.not_isInitial_id` below.
   `…SeparatedFiniteEtaleOver.isTerminalFintypeFiberId` gives a terminal object of `FintypeCat`,
   its `CategoryTheory.Limits.IsTerminal.from` out of `FintypeCat.of PUnit` applied to `PUnit.unit`
   is a point of the fibre, and `CategoryTheory.PreGaloisCategory.not_initial_of_inhabited` is the
   step. **This is the only one of the five statements below with no coproduct in it.**
3. **One coprojection is enough.** Composed with the given isomorphism it is a mono into `A`, and
   (2) is the hypothesis `…IsConnected.noTrivialComponent` asks of its source.

**Step 3 is where the finiteness of the index type is spent inside the proof, and it is spent by
instance search and not by a proof step**: `CategoryTheory.Limits.MonoCoprod.mono_ι` asks for the
coproduct of the family restricted to the complement of a point of the index type, which exists
here because that complement is finite and a `CategoryTheory.GaloisCategory` has finite coproducts.
Nothing below mentions that coproduct. **Step 1 spends no finiteness at all** —
`…SeparatedFiniteEtaleOver.isInitialCoprodId` binds `[IsEmpty ι]` and nothing else — and step 2 has
no index type in it.

**`[Finite ι]` is also what makes the statement it appears in a statement**, before any of the
three runs: the `∐` of `…SeparatedFiniteEtaleOver.nonempty_iso_id_of_iso_coprod_id` needs
`CategoryTheory.Limits.HasCoproduct` of the family, which a `CategoryTheory.GaloisCategory` gives
for a finite index type. **So the hypothesis does not come off**, and a reader asking whether it
can should read this paragraph and not the numbered list, in which it appears nowhere.

## What the import costs, measured in the environment and not by a scan

This file's only `import` is `Oka.AnalyticSpace.SimplyConnectedCriterion`, which is in `import
Oka`'s closure already, so **the cost is zero and it is a run and not a diff**: at the commit this
file is cut from `import Oka` brings **5541** modules and at the commit that adds it **5542**, by a
set difference over `Lean.Environment.allImportedModuleNames`, and the one module the difference
contains is this one. **No Mathlib module enters the closure**, and in particular the
`CategoryTheory.Limits.MonoCoprod` instance used below costs nothing:
`Mathlib/CategoryTheory/Limits/MonoCoprod.lean` is already there, brought in by
`Mathlib/CategoryTheory/Galois/Basic.lean`, which `Oka/AnalyticSpace/GaloisCategory.lean` needs for
the `CategoryTheory.GaloisCategory` instance itself. The base figure is taken by elaborating the
base `Oka.lean` at this checkout, which imports 5540 modules and is one short of `import Oka` there
by the root module itself. **A marginal import cost is a figure about the importer at a commit and
is meaningless without one**, which is why both are pinned here and neither is in the present
tense.

## What the census scripts return

**Both columns of every row below are pinned to a commit**: the before-column is `6e0c610`, the
commit this file is cut from, and the after-column is the commit that adds it. The reason is the one
the section above gives of the marginal import cost — *a figure about the importer at a commit is
meaningless without one* — and it is as true of a tree-wide total as of a closure. **Every row below
stood unpinned until 2026-09-21, and five of them were false at the head that carried them**: the
two dump totals read *4998 → 5003* and *338274 → 338280*, and the three
`scripts/check_docstring_names.py` rows read *18097 → 18150*, *350 → 383* and *240 (120) → 244
(124)*. **Their before-columns are `a414f61`'s, and this branch has been cut from `ae732d9`, from
`66cf643` and now from `6e0c610`**: at `ae732d9`, its first base, the backticked figure is **18142
(4419)** and not **18097 (4406)**, so **that** row was wrong at the before-column before any replay
and has been wrong at every base since. **The other two were not, and the difference is the
argument**: at `ae732d9` the elided row's before-column **350 (164)** and the dotless row's **240
(120)** were both correct, and the dotless one is correct at `6e0c610` too — what falsified those
two **before-columns** is the replays and this module's own prose growing under them, and not the
commit they were taken at. **The elided row's after-column is a third failure mode and neither of
those**: it was wrong when it was written, at a head this branch has since replaced, so one end of
that row was falsified by no replay and no later prose at all. **That is what the pin is for** — an
unpinned pair can be wrong at both ends at once, or right at both and falsified later by a landing
nobody editing this file touched, and a reader cannot tell which — and the five rows are re-taken
here at `6e0c610` and at this head, each column a run. **What no replay has moved is a delta**: the
five rows this module adds to the declaration dump, the six it adds to the environment dump and the
`5 = 4 + 1` below are properties of this push and are stated without a pin, and that division is
what the pin is for. **The `scripts/guard_coverage.py` rows came through every replay unmoved, and
that is a fact about what landed in between rather than a property of that script**: **all eight
rows of that report's table** are byte-identical at `a3d656d`, `57e5a1a`, `d34b436`, `66cf643` and
`6e0c610` — the whole report is not, differing from the first by **8** lines at `57e5a1a` and by
**10** at the other three, **with `--env-dump` given and one dump pair held fixed across the
five**, every one of them a skipped-token line number moved by prose landing above it — and the
module `lana-agents/oka#601` adds carries no `#print axioms` of its own, so the guard row had
nothing to miss there. **Both of those conditions are load-bearing, and the run a reader reaches
for first satisfies neither.** Without `--env-dump` the skipped-token row prints counts and no
per-token site, so **no line number appears anywhere in the report**, and the differences this
sentence reports — every one of them a skipped-token line number — cannot appear in it at all:
that run answers a different question, and its silence reads as a refutation of this sentence
rather than as a missing flag. And with each tree's own dumps the reconciliation in that row
moves with the dump as well as with the prose — the `scripts/DumpOkaDecls.lean` and
`scripts/DumpEnvNames.lean` figures this section gives for one of these very landings,
**5003 → 5008** and **338280 → 338286**, are that motion — so the differences stop being *every
one of them a skipped-token line number*. **A row that happens to be flat is not a row that
cannot move**, and they are pinned with the rest.

`scripts/DumpOkaDecls.lean` writes **5** rows at this module — the five declarations, with **no**
equation lemma, match lemma or congruence lemma — and the dump total moves **5003 → 5008**.
`scripts/DumpEnvNames.lean` moves **338280 → 338286**, which is those five declarations and this
one module and nothing else.

`scripts/guard_coverage.py` moves guards under `OkaTest/Axioms/` **2021 → 2026**, all five in
`OkaTest/Axioms/Morphisms.lean`; advertised in a `## Main results` **1517 → 1521**, in **233 →
234** files; and *in both lists* **1375 → 1379**. **`Δguards = Δ(in both) + Δ(nowhere)` closes at
`5 = 4 + 1`**, and the one is `…SeparatedFiniteEtaleOver.isInitialCoprodId`: it is guarded and it
is advertised under `## Main definitions`, which that script does not read, so it lands in the
*guarded and advertised nowhere* row, which goes **646 → 647**. The *unguarded* row is flat at
**142, in 60 files** — this file opens no gap — *advertised from another file* is flat at **89**,
*abbreviated citations, not counted* at **30, four of them dotted**, and *backticked tokens that
resolve to nothing* at **719** with `--env-dump` given at both ends.

`scripts/check_docstring_names.py` goes **18263 → 18317** backticked names (**4432 → 4445**
distinct) and **367 → 408** elided citations (**169 → 175** distinct), with **0** unresolved at
both ends, **6** resolving under more than one namespace at both, and dotless **240 (120) → 245
(124)**.

**Both ends of every figure in this section are runs**, with the base column taken in a
`git worktree` at the base commit against dumps synthesised from the head ones by deleting this
module's five declaration rows and its six environment rows. **The worktree's own copy of
`scripts/guard_coverage.py` is what has to be run there**: that script sets its repository root
from `os.path.abspath(__file__)`, so invoking the *head* checkout's copy with the worktree as the
working directory reads the head's guard files and silently reports the head's guard count while
reporting the base's advertised count — a base column that is neither commit's.

## Main definitions

- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.isInitialCoprodId`: **a coproduct of
  copies of the base over itself, over an empty index type, is initial.**

## Main results

- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.not_isInitial_id`: **the base over itself
  is not an initial object.**
- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.nonempty_iso_id_of_iso_coprod_id`: **a
  connected cover isomorphic to a finite coproduct of copies of the base over itself is isomorphic
  to the base over itself.**
- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.subsingleton_fundamentalGroup_of_coprod`:
  **a base over which every cover is a finite coproduct of copies of the base over itself has
  trivial fundamental group**, at every point of it.
- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.subsingleton_fundamentalGroup_coprod_iff`:
  **and that is a criterion** — the two conditions are equivalent.

## Why one name below is shorter than its sibling's, and the constraint is the column limit

`…SeparatedFiniteEtaleOver.subsingleton_fundamentalGroup_of_coprod` is the name the sibling's
`…subsingleton_fundamentalGroup_of_iso_id` would suggest spelling `…_of_iso_coprod_id`, and that
spelling is **unwritable in a `## Main results` list**: `scripts/guard_coverage.py` reads a
backticked token with `` `([^`\s]+)` ``, so a name broken across two lines is not a token at all
and resolves to nothing, and the whole name plus the list's `- ` and `:` is 106 columns against a
limit of 100. **Fifty-five of those columns are the namespace**
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.`, which leaves forty for the head;
`…_of_coprod` is thirty-nine and `…_coprod_iff` is forty exactly.
The list below is written in full for the reason the sibling's heading gives, and this is the other
half of that constraint: an elided head resolves to nothing, and so does a wrapped one.

## What is not here

* **No base is exhibited whose fundamental group is trivial, and none is claimed to exist.** That
  is the first bullet of both siblings' `## What is not here` and this file does not move it; what
  it changes is the shape of hypothesis that suffices and not whether any base satisfies one.
* **No count of the index type.** Nothing below says that the `ι` of the hypothesis is a singleton,
  a subsingleton or non-empty in any statement's conclusion; the non-emptiness is a step inside one
  proof and is not named. **A consumer wanting the count has to state and prove it**, and the
  section above says why the criterion does not.
* **Nothing is said about a coproduct over a non-empty index type that is not a singleton.** The
  criterion's hypothesis is satisfied by every `A` at once, so no statement below is about a
  particular decomposition, and the `∐` in it is never taken apart except at one coprojection.
* **No transport between points.** `…SeparatedFiniteEtaleOver.subsingleton_fundamentalGroup_congr`
  is the sibling's and applies to the left-hand side of this criterion unchanged, that being the
  same proposition; nothing is restated here.
* **Nothing about the topologist's fundamental group, nothing about analytification and nothing
  about a scheme.** This is the analytic side alone, for the reasons the two siblings give.
-/

universe u

open CategoryTheory CategoryTheory.Limits
open scoped FintypeCatDiscrete

namespace ComplexAnalytic.AnalyticSpace

/-- **A coproduct of copies of the base over itself over an empty index type is initial.**

`CategoryTheory.Limits.IsInitial.ofUniqueHom`: the morphism out of it is
`CategoryTheory.Limits.Sigma.desc` of an empty family of morphisms and two morphisms out of it
agree by `CategoryTheory.Limits.Sigma.hom_ext`, both obligations being a `∀` over the index type
and so discharged by `isEmptyElim`.

**It is a `def` and not a theorem** because `CategoryTheory.Limits.IsInitial` is a
`CategoryTheory.Limits.IsColimit` and so is data, and it is `noncomputable` because the coproduct
it is about is.

**Nothing here is about the base**, which is why it takes one and asks nothing of it: the same
argument would prove it of an empty coproduct of any family in any category that has the
coproduct, and it is stated at this family because that is the only place it is used. -/
noncomputable def SeparatedFiniteEtaleOver.isInitialCoprodId (X : AnalyticSpace.{u})
    {ι : Type} [IsEmpty ι] :
    IsInitial (∐ fun _ : ι ↦ SeparatedFiniteEtaleOver.id.{u} X) :=
  IsInitial.ofUniqueHom (fun _ ↦ Sigma.desc fun i ↦ isEmptyElim i)
    fun _ _ ↦ Sigma.hom_ext _ _ fun i ↦ isEmptyElim i

variable {X : AnalyticSpace.{u}} [T2Space (X : Type u)] [PreconnectedSpace (X : Type u)]
  [Nonempty (X : Type u)]

omit [Nonempty (X : Type u)] in
/-- **The base over itself is not an initial object of the category of covers separated over it.**

`CategoryTheory.PreGaloisCategory.not_initial_of_inhabited` asks for a point of the fibre, and
`…SeparatedFiniteEtaleOver.isTerminalFintypeFiberId` supplies one: it is a terminal object of
`FintypeCat`, so `CategoryTheory.Limits.IsTerminal.from` out of `FintypeCat.of PUnit` is a morphism
into it and `PUnit.unit` is what that morphism is applied to.

**The point of the base is a hypothesis of a statement that does not mention it**, and it is not
removable: the conclusion is about the category, the only route to it is through a fibre functor
and this repository's fibre functors are indexed by a point. `[Nonempty (X : Type u)]` is omitted
above because `x` gives it.

**A terminal object is not in general non-initial**, and what rules it out here is the fibre and
not the terminality: in the category of covers separated over an *empty* base the two coincide,
which is what `Oka/AnalyticSpace/EmptyBase.lean` is about, and there is no point to name. -/
theorem SeparatedFiniteEtaleOver.not_isInitial_id (x : X) :
    IsInitial (SeparatedFiniteEtaleOver.id.{u} X) → False := fun h ↦
  PreGaloisCategory.not_initial_of_inhabited
    (F := SeparatedFiniteEtaleOver.fintypeFiberFunctor.{u} x)
    ((SeparatedFiniteEtaleOver.isTerminalFintypeFiberId.{u} x).from
      (FintypeCat.of PUnit) PUnit.unit) h

/-- **A connected cover isomorphic to a finite coproduct of copies of the base over itself is
isomorphic to the base over itself.**

The index type is non-empty, since otherwise
`…SeparatedFiniteEtaleOver.isInitialCoprodId` and `CategoryTheory.Limits.IsInitial.ofIso` would
make the cover initial and `CategoryTheory.PreGaloisCategory.IsConnected.notInitial` refuses that.
At a point of it, `CategoryTheory.Limits.Sigma.ι` is a monomorphism —
`CategoryTheory.Limits.MonoCoprod.mono_ι`, at the `CategoryTheory.Limits.MonoCoprod` instance every
`CategoryTheory.GaloisCategory` carries — so composing with the inverse of the given isomorphism
gives a mono `…SeparatedFiniteEtaleOver.id X ⟶ A`, and
`CategoryTheory.PreGaloisCategory.IsConnected.noTrivialComponent` at
`…SeparatedFiniteEtaleOver.not_isInitial_id` makes it an isomorphism.

**The index type is never counted**, and the sibling module's `## What is not here` says why that
is worth pointing out.

**The conclusion is `Nonempty` of an isomorphism rather than the isomorphism**, matching
`…SeparatedFiniteEtaleOver.nonempty_iso_id`, whose place in the next proof this takes: the
isomorphism produced is `CategoryTheory.asIso` of a morphism that depends on a choice of point of
the index type, and forgetting it is what makes the statement a proposition. -/
theorem SeparatedFiniteEtaleOver.nonempty_iso_id_of_iso_coprod_id (x : X)
    (A : SeparatedFiniteEtaleOver.{u} X) [PreGaloisCategory.IsConnected A]
    {ι : Type} [Finite ι] (e : A ≅ ∐ fun _ : ι ↦ SeparatedFiniteEtaleOver.id.{u} X) :
    Nonempty (A ≅ SeparatedFiniteEtaleOver.id.{u} X) := by
  have hne : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    exact PreGaloisCategory.IsConnected.notInitial (X := A)
      (IsInitial.ofIso (SeparatedFiniteEtaleOver.isInitialCoprodId.{u} X) e.symm)
  obtain ⟨i⟩ := hne
  set f : SeparatedFiniteEtaleOver.id.{u} X ⟶ A :=
    Sigma.ι (fun _ : ι ↦ SeparatedFiniteEtaleOver.id.{u} X) i ≫ e.inv with hf
  haveI : Mono f := mono_comp _ _
  haveI : IsIso f := PreGaloisCategory.IsConnected.noTrivialComponent _ f
    (SeparatedFiniteEtaleOver.not_isInitial_id.{u} x)
  exact ⟨(asIso f).symm⟩

/-- **A base over which every cover is a finite coproduct of copies of the base over itself has
trivial fundamental group**, at every point of it.

`…SeparatedFiniteEtaleOver.subsingleton_fundamentalGroup_of_iso_id` asks for an isomorphism with
the base over itself at every *connected* cover, and
`…SeparatedFiniteEtaleOver.nonempty_iso_id_of_iso_coprod_id` above turns the hypothesis into one
there. **Nothing else is done here**, and in particular the hypothesis is used at connected covers
only, though it is stated at all of them — which is how it has to be stated, since the class it
would otherwise be restricted to is what this criterion exists to avoid mentioning.

**The hypothesis is a plain `∀` with an `∃` under it and not an instance argument**, for the
sibling's reason: the cover it speaks of is quantified over, and so is the index type. -/
theorem SeparatedFiniteEtaleOver.subsingleton_fundamentalGroup_of_coprod (x : X)
    (h : ∀ A : SeparatedFiniteEtaleOver.{u} X, ∃ (ι : Type) (_ : Finite ι),
      Nonempty (A ≅ ∐ fun _ : ι ↦ SeparatedFiniteEtaleOver.id.{u} X)) :
    Subsingleton (SeparatedFiniteEtaleOver.fundamentalGroup.{u} x) := by
  refine SeparatedFiniteEtaleOver.subsingleton_fundamentalGroup_of_iso_id.{u} x fun A hA ↦ ?_
  obtain ⟨ι, hι, e⟩ := h A
  exact SeparatedFiniteEtaleOver.nonempty_iso_id_of_iso_coprod_id.{u} x A e.some

/-- **The fundamental group at a point is trivial exactly when every cover separated over the base
is a finite coproduct of copies of the base over itself.**

The two directions are `…SeparatedFiniteEtaleOver.exists_iso_coprod_id` and
`…SeparatedFiniteEtaleOver.subsingleton_fundamentalGroup_of_coprod` above and nothing is
added to either.

**What this has that `…SeparatedFiniteEtaleOver.subsingleton_fundamentalGroup_iff` does not is a
right-hand side with no `CategoryTheory.PreGaloisCategory.IsConnected` in it**: it names no point,
as that one does not, and it also names no class a consumer has to discharge at an object before
the condition can be applied to it. -/
theorem SeparatedFiniteEtaleOver.subsingleton_fundamentalGroup_coprod_iff (x : X) :
    Subsingleton (SeparatedFiniteEtaleOver.fundamentalGroup.{u} x) ↔
      ∀ A : SeparatedFiniteEtaleOver.{u} X, ∃ (ι : Type) (_ : Finite ι),
        Nonempty (A ≅ ∐ fun _ : ι ↦ SeparatedFiniteEtaleOver.id.{u} X) :=
  ⟨fun _ A ↦ SeparatedFiniteEtaleOver.exists_iso_coprod_id.{u} x A,
    SeparatedFiniteEtaleOver.subsingleton_fundamentalGroup_of_coprod.{u} x⟩

end ComplexAnalytic.AnalyticSpace
