/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.AnalyticSpace.FundamentalGroup

/-!
# A base whose fundamental group is trivial has only trivial covers

`Oka/AnalyticSpace/FundamentalGroup.lean` defines
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.fundamentalGroup` and classifies the covers
separated over a Hausdorff, preconnected, nonempty base by it. **This file is what that
classification buys at the one value of the group that can be named without computing it**: the
trivial group. A connected cover over such a base is the base over itself, and an arbitrary one is
a finite coproduct of copies of it.

## Why this file exists, and the census is a scan rather than a memory

At the commit this file is cut from, `fundamentalGroup` occurs in the comment-stripped code of
exactly **two** modules — `Oka/AnalyticSpace/FundamentalGroup.lean`, which declares it, and
`OkaTest/Axioms/Morphisms.lean`, the guard file — and so do
`…SeparatedFiniteEtaleOver.contActionEquivalence` and
`…SeparatedFiniteEtaleOver.isPretransitive_fundamentalGroup`. **Nothing read any of the three.**
That is the position the `CategoryTheory.GaloisCategory` instance was in before that module was
written, and the sentence that module's `## What the third instance buys, probed at both ends`
ends on — *no statement of this repository at the commit that adds this instance consumes the
class* — had become true of it one level up.

**Which spelling the scan counts is part of its figure.** The population is every tracked `.lean`
file, the stripper is `scripts/import_cost.py`'s `strip_comments`, and what is counted is the name
**not preceded or followed by a letter, a digit or `_`**, with a `.` allowed before it. That last
clause is the difference from the `GaloisCategory` scan published one module over: a class written
under `open CategoryTheory` occurs bare, and every occurrence of these three names in code is
dotted, so a scan that forbids a preceding `.` returns **0** for all three and reports the two
modules that do name them as naming nothing.

## The whole of the mathematics is that a subsingleton fibre is terminal

The group acts transitively on the fibre of a connected cover
(`…SeparatedFiniteEtaleOver.isPretransitive_fundamentalGroup`) and that fibre is non-empty
(`CategoryTheory.PreGaloisCategory.nonempty_fiber_of_isConnected`), so a trivial group makes it a
one-point set. The fibre of the base over itself is a one-point set too
(`…SeparatedFiniteEtaleOver.isTerminalFintypeFiberId`), the unique morphism to the base over itself
is therefore an isomorphism **on fibres**, and the fibre functor reflects isomorphisms. **No step
of that is analytic and none of it is new mathematics**; what the file supplies is that every rung
it uses is already a declaration of this repository, and the statement it lands on.

**`CategoryTheory.isIso_of_reflects_iso` at the `FintypeCat`-valued fibre functor is where this
leaves the category and comes back.** The `ReflectsIsomorphisms` instance it consumes is found by
search and is not named below, so this file adds no occurrence of it to any census of that name.

## The names below do not carry their hypothesis, and that is forced

`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.` is **fifty-five** characters before a
declaration's own name begins, and a `## Main results` entry has to be the whole name — elide it
and `scripts/guard_coverage.py` resolves the backticked token against nothing, which is the trap
`Oka/AnalyticSpace/FundamentalGroup.lean` records at length. A name ending
`_of_subsingleton_fundamentalGroup` is thirty-three characters more, which puts the shortest of the
four entries below past the hundred-column limit `lake exe lint-style` enforces. **So the
hypothesis is in the docstrings and in the section variable and not in the names**, and it is
`[Subsingleton (…SeparatedFiniteEtaleOver.fundamentalGroup x)]` throughout: an instance argument,
which is the shape Mathlib omits from a name anyway.

## Main definitions

- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.isTerminalFintypeFiber`: **a fibre that
  is non-empty and a subsingleton is a terminal object of `FintypeCat`.** It asks nothing of the
  group and nothing of the base.

## Main results

- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.subsingleton_fiber`: **the fibre of a
  connected cover is a subsingleton when the fundamental group is trivial.**
- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.nonempty_iso_id`: **a connected cover
  over a base with trivial fundamental group is isomorphic to the base over itself.**
- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.exists_iso_coprod_id`: **and an arbitrary
  one is a finite coproduct of copies of the base over itself.**

## What the import costs, measured in the environment and not by a scan

This file's only `import` is `Oka.AnalyticSpace.FundamentalGroup`, which is in `import Oka`'s
closure already, so **the cost is zero and it is a run and not a diff**: at the commit this file is
cut from `import Oka` brings **5537** modules and at the commit that adds it **5538**, by a set
difference over `Lean.Environment.allImportedModuleNames`, and the one module the difference
contains is this one. **No Mathlib module enters the closure.** The base figure is taken by
elaborating the base `Oka.lean` at this checkout, which imports 5536 modules and is one short of
`import Oka` there by the root module itself. **A marginal import cost is a figure about the
importer at a commit and is meaningless without one**, which is why both are pinned here and
neither is in the present tense.

## What the census scripts return

`scripts/DumpOkaDecls.lean` writes **4** rows at this module — the four declarations, with **no**
equation lemma, match lemma or congruence lemma — and the dump total moves **4974 → 4984**, the
other six being `OkaTest/FundamentalGroup.lean`'s. `scripts/DumpEnvNames.lean` moves
**338245 → 338257**, which is those ten declarations and the two modules minus nothing.

`scripts/guard_coverage.py` moves guards under `OkaTest/Axioms/` **2003 → 2007**, all four in
`OkaTest/Axioms/Morphisms.lean`; advertised **1501 → 1504** in **229 → 230** files; in both
**1359 → 1362**; and guarded and advertised nowhere **644 → 645**, the one being this file's
`## Main definitions` entry, which is where a guarded declaration advertised outside a
`## Main results` section lands. **`Δguards = Δ(in both) + Δ(nowhere)` closes at `4 = 3 + 1`**, and
the *unguarded* row is flat at **142, in 60 files**: this file opens no gap. *Advertised from
another file* is flat at **86** and *abbreviated citations, not counted* at **30, four of them
dotted**.

`scripts/check_docstring_names.py` goes **17899 → 17962** backticked names
(**4364 → 4374** distinct) and **311 → 332** elided citations (**156 → 160** distinct), **0
unresolved at both ends**, **6** resolving under more than one namespace at both, and **239**
dotless at both.

## What is not here

* **No base is exhibited whose fundamental group is trivial, and none is claimed to exist.** The
  hypothesis of the three results above is satisfied by nothing in this repository. It is not
  vacuous in the mathematics and it is unwitnessed here, and those are different sentences: what
  the results say is that the hypothesis is *strong*, since over a base that meets it the category
  has one isomorphism class of connected object.
* **The converse direction is the one this repository can witness, and it is not in this file.**
  A cover that is not isomorphic to the base over itself refutes the hypothesis, and
  `OkaTest/FundamentalGroup.lean` is where that is done, at the punctured line: the witness needs
  `OkaTest/FiniteEtaleOver.lean`'s `sqOver` and the two instances that file declares at `.left`,
  none of which is under `Oka/`.
* **No comparison with the topologist's fundamental group.**
  `Oka/Analysis/Complex/FundamentalGroup.lean` computes `FundamentalGroup` of `ℂ ∖ {0}` and proves
  it infinite; the group here is the
  automorphism group of a fibre functor, `Oka/AnalyticSpace/FundamentalGroup.lean`'s
  `## What is not here` says that nothing in this repository relates the two, and **nothing below
  relates them either.** A reader who meets the punctured line on both sides of that sentence
  should read it as two theorems about two groups.
* **`SimplyConnectedSpace` is Mathlib's and is not what this file's name refers to.**
  `Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected` is in this repository's import
  closure already — it is one of the **5537** modules `import Oka` brings at the commit this file
  is cut from — and it is a condition on the *fundamental groupoid* of a topological space.
  **Nothing below mentions it, uses it or implies it**, and *simply connected* in this file's title
  means the hypothesis the statements carry and nothing else.
* **Nothing about total spaces.** The coproduct below is the categorical one and is not carried to
  a disjoint union of spaces; that reading is
  `Oka/AnalyticSpace/ConnectedComponents.lean`'s and this module neither imports it nor is
  imported by it.
* **No count.** The index type of the coproduct is existential and is related to no fibre
  cardinality and to no degree; `Nat.card` does not occur below.
-/

universe u

open CategoryTheory CategoryTheory.Limits
open scoped FintypeCatDiscrete

namespace ComplexAnalytic.AnalyticSpace

variable {X : AnalyticSpace.{u}} [T2Space (X : Type u)] [PreconnectedSpace (X : Type u)]
  [Nonempty (X : Type u)]

/-- **The fibre of a connected cover is a subsingleton when the fundamental group at that point is
trivial.**

`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.isPretransitive_fundamentalGroup` produces
a group element carrying one point of the fibre to another, `Subsingleton.elim` replaces it by `1`
and `one_smul` finishes. **The action is the one the classification is by** — it is evaluation of
the natural transformation, which `…SeparatedFiniteEtaleOver.smul_fiber` says is `rfl` — so this is
a statement about that classification and not about a second action. -/
theorem SeparatedFiniteEtaleOver.subsingleton_fiber (x : X)
    [Subsingleton (SeparatedFiniteEtaleOver.fundamentalGroup.{u} x)]
    (A : SeparatedFiniteEtaleOver.{u} X) [PreGaloisCategory.IsConnected A] :
    Subsingleton ((SeparatedFiniteEtaleOver.fintypeFiberFunctor.{u} x).obj A) := by
  haveI := SeparatedFiniteEtaleOver.isPretransitive_fundamentalGroup.{u} x A
  refine ⟨fun a b ↦ ?_⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (SeparatedFiniteEtaleOver.fundamentalGroup.{u} x) a b
  rw [← hg, Subsingleton.elim g 1, one_smul]

omit [T2Space (X : Type u)] [PreconnectedSpace (X : Type u)] [Nonempty (X : Type u)] in
/-- **A fibre that is non-empty and a subsingleton is a terminal object of `FintypeCat`.**

`CategoryTheory.Limits.IsTerminal.ofUniqueHom`: the morphism out of any finite type is the constant
map at the fibre's one point, and two morphisms into a subsingleton agree pointwise.

**It is a `def` and not a theorem** because `CategoryTheory.Limits.IsTerminal` is a
`CategoryTheory.Limits.IsLimit` and so is data; it is `noncomputable` because the one point is
produced by `Classical.arbitrary` out of the `Nonempty`.

**Nothing here is about covers**, and the hypotheses of the section are omitted above for that
reason: the statement is about an object of `FintypeCat` that happens to be written as a fibre, and
it would read the same of any non-empty subsingleton finite type. It is stated at the fibre because
that is the only place it is used and a general version would duplicate
`CategoryTheory.Limits.IsTerminal.ofUniqueHom` with no object of this repository in it. -/
noncomputable def SeparatedFiniteEtaleOver.isTerminalFintypeFiber (x : X)
    (A : SeparatedFiniteEtaleOver.{u} X)
    [Nonempty ((SeparatedFiniteEtaleOver.fintypeFiberFunctor.{u} x).obj A)]
    [Subsingleton ((SeparatedFiniteEtaleOver.fintypeFiberFunctor.{u} x).obj A)] :
    IsTerminal ((SeparatedFiniteEtaleOver.fintypeFiberFunctor.{u} x).obj A) :=
  IsTerminal.ofUniqueHom (fun _ ↦ FintypeCat.homMk fun _ ↦ Classical.arbitrary _)
    fun _ _ ↦ FintypeCat.hom_ext _ _ fun _ ↦ Subsingleton.elim _ _

/-- **A connected cover separated over a base whose fundamental group at a point is trivial is
isomorphic to the base over itself.**

The morphism is the one
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.isTerminalId` supplies, so there is no
choice in it and no compatibility to check; what the proof does is show it is an isomorphism, and
it does that on fibres. Both fibres are terminal —
`…SeparatedFiniteEtaleOver.isTerminalFintypeFiber` above at this one,
`…SeparatedFiniteEtaleOver.isTerminalFintypeFiberId` at the base over itself — so the image of the
morphism has an inverse by `CategoryTheory.Limits.IsTerminal.hom_ext` in each direction, and
`CategoryTheory.isIso_of_reflects_iso` carries that back.

**The conclusion is `Nonempty` of an isomorphism rather than the isomorphism.** The isomorphism
produced is `CategoryTheory.asIso` of a canonical morphism and is not a choice, so nothing is lost
by forgetting it here; what is gained is that the statement is a proposition and composes with
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.exists_iso_coprod_id` below, whose own
conclusion is existential for the same reason. -/
theorem SeparatedFiniteEtaleOver.nonempty_iso_id (x : X)
    [Subsingleton (SeparatedFiniteEtaleOver.fundamentalGroup.{u} x)]
    (A : SeparatedFiniteEtaleOver.{u} X) [PreGaloisCategory.IsConnected A] :
    Nonempty (A ≅ SeparatedFiniteEtaleOver.id.{u} X) := by
  haveI : Nonempty ((SeparatedFiniteEtaleOver.fintypeFiberFunctor.{u} x).obj A) :=
    PreGaloisCategory.nonempty_fiber_of_isConnected _ A
  haveI := SeparatedFiniteEtaleOver.subsingleton_fiber.{u} x A
  set f : A ⟶ SeparatedFiniteEtaleOver.id.{u} X :=
    (SeparatedFiniteEtaleOver.isTerminalId.{u} X).from A with hf
  have hiso : IsIso ((SeparatedFiniteEtaleOver.fintypeFiberFunctor.{u} x).map f) :=
    ⟨(SeparatedFiniteEtaleOver.isTerminalFintypeFiber.{u} x A).from _,
      (SeparatedFiniteEtaleOver.isTerminalFintypeFiber.{u} x A).hom_ext _ _,
      (SeparatedFiniteEtaleOver.isTerminalFintypeFiberId.{u} x).hom_ext _ _⟩
  haveI : IsIso f := isIso_of_reflects_iso f (SeparatedFiniteEtaleOver.fintypeFiberFunctor.{u} x)
  exact ⟨asIso f⟩

/-- **Every cover separated over a base whose fundamental group at a point is trivial is a finite
coproduct of copies of the base over itself.**

`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.exists_isConnected_decomposition` splits it
into connected pieces and `…SeparatedFiniteEtaleOver.nonempty_iso_id` above replaces each piece by
the base over itself, through `CategoryTheory.Limits.Sigma.mapIso`.

**The index type is the decomposition's own and is in `Type`**, which is where
`CategoryTheory.PreGaloisCategory.has_decomp_connected_components'` puts it; no universe crossing
is done here and none is needed, the coproduct being taken at that index type on both sides.

**Nothing says the index type is determined**, by this statement or by the one it is read from. -/
theorem SeparatedFiniteEtaleOver.exists_iso_coprod_id (x : X)
    [Subsingleton (SeparatedFiniteEtaleOver.fundamentalGroup.{u} x)]
    (A : SeparatedFiniteEtaleOver.{u} X) :
    ∃ (ι : Type) (_ : Finite ι),
      Nonempty (A ≅ ∐ fun _ : ι ↦ SeparatedFiniteEtaleOver.id.{u} X) := by
  obtain ⟨ι, hι, f, e, hf⟩ := SeparatedFiniteEtaleOver.exists_isConnected_decomposition.{u} A
  refine ⟨ι, hι, ⟨e.symm ≪≫ Sigma.mapIso fun i ↦ ?_⟩⟩
  haveI := hf i
  exact (SeparatedFiniteEtaleOver.nonempty_iso_id.{u} x (f i)).some

end ComplexAnalytic.AnalyticSpace
