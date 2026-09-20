/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.AnalyticSpace.GaloisCategory
import Mathlib.CategoryTheory.Galois.Equivalence

/-!
# The fundamental group, and the covers separated over a connected Hausdorff base classified by it

`Oka/AnalyticSpace/GaloisCategory.lean` makes
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver` a `CategoryTheory.GaloisCategory` over a
Hausdorff, preconnected, nonempty base, and closes by saying that **no statement of this repository
at the commit that adds that instance consumes the class**. **This file is the consumer**, and what
the class buys is the classification theorem: the covers separated over such a base are equivalent
to the finite discrete continuous actions of a single profinite group, the automorphism group of
the fibre functor.

## What is new here is the instantiation and not the mathematics

`CategoryTheory.PreGaloisCategory.functorToContAction`
(`Mathlib/CategoryTheory/Galois/Equivalence.lean`) is a functor from any Galois category to the
continuous actions of `CategoryTheory.Aut` at its fibre functor, and Mathlib declares it an
equivalence. **Both of its hypotheses are instances of this repository already** —
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.galoisCategory` and
`…SeparatedFiniteEtaleOver.fintypeFiberFunctor_isFiberFunctor` — so every declaration below is
that theorem read at this category, and none proves anything Mathlib does not. **What this file
supplies is a statement of it in this repository's vocabulary**, together with the two `rfl`
identities that say the classifying action is carried by the fibre.

## The census behind *the consumer*, which is a scan and not a memory

At the commit this file is cut from, the class occurs in the comment-stripped code of exactly
**three** modules: `Oka/AnalyticSpace/GaloisCategory.lean`, which declares the instance,
`Oka/AnalyticSpace/EmptyBase.lean`, whose only occurrence is under a `¬`, and
`OkaTest/GaloisCategory.lean`, the control. **In none of the three is the class a hypothesis of a
declaration**, which is the claim the opening paragraph quotes, checked rather than carried over.

**Which spelling a scan counts is part of its figure, so this one says which.** The population is
every tracked `.lean` file under `Oka/` and `OkaTest/` together with the two root modules, the
stripper is `scripts/import_cost.py`'s `strip_comments`, and what is counted is *GaloisCategory*
**as a token** — not preceded by a letter, a digit, `_` or `.`, and not followed by one — which is
how the class is written in code under `open CategoryTheory`, and how it is written in all six
occurrences the three modules between them have. So *PreGaloisCategory* is not an occurrence,
`…SeparatedFiniteEtaleOver.preGaloisCategory` is not one, and a module path in an `import` line is
not one either. **The fully-qualified `CategoryTheory.GaloisCategory` is written nowhere in the
code of this repository** under that population and stripper — it occurs in **0** modules — and the
bare substring occurs in **6** modules and **28** places, the three extra modules being the two
root ones and `OkaTest/Axioms/Morphisms.lean`. **The figure three belongs to the token reading and
to neither of the other two**, which is why naming the token here is not a formality.

## What the import costs, measured in the environment and not by a scan

**At the commit this file is cut from**, `import Oka` brings **5512** modules and `import Oka`
together with `import Mathlib.CategoryTheory.Galois.Equivalence` brings **5532**: **the cost is
20**, by a set difference over `Lean.Environment.allImportedModuleNames` in a `run_cmd`, which is
exact where a transitive walk of `import` lines is an estimate. Fourteen of the twenty are
`Mathlib.CategoryTheory.Galois.Action`, `…Galois.Decomposition`, `…Galois.Equivalence`,
`…Galois.EssSurj`, `…Galois.Examples`, `…Galois.Full`, `…Galois.GaloisObjects`,
`…Galois.Prorepresentability`, `…Galois.Topology`, `Mathlib.CategoryTheory.Action.Basic`,
`…Action.Concrete`, `…Action.Continuous`, `…Action.Limits` and
`Mathlib.Topology.Category.FinTopCat`; the other six are
`Mathlib.CategoryTheory.CofilteredSystem`, `Mathlib.CategoryTheory.Limits.IndYoneda`,
`Mathlib.CategoryTheory.Limits.Shapes.CombinedProducts`,
`Mathlib.CategoryTheory.Limits.Shapes.SingleObj`,
`Mathlib.CategoryTheory.Linear.FunctorCategory` and
`Mathlib.Topology.Category.TopCat.Limits.Konig`.

**At the commit that adds this file the same pair of runs gives 5533 and 5533, and the cost is
zero**, this file having paid it: 5512 plus the twenty plus this module. **A marginal import cost
is a figure about the importer at a commit and is meaningless without one**, which is why both are
pinned here and neither is written in the present tense.

## Two things a caller has to know, and neither of them announces itself

**`open scoped FintypeCatDiscrete` is load-bearing in the *statements* below and not only in their
proofs.** Without it the type `ContAction FintypeCat G` does not
elaborate — both of those names are at the root namespace and not under `CategoryTheory` — and
what is reported is

```
failed to synthesize instance of type class
  HasForget₂ FintypeCat TopCat
```

a message about a pair of categories that names neither the scoped namespace nor anything in this
file. **Any module that states a declaration below has to open it too**, which is why this
paragraph is here rather than in a comment beside the `open`.

**The fundamental group is declared without a type ascription and that is forced.** Writing
`: Type u` on the `abbrev` below fails with

```
failed to synthesize instance of type class
  Category.{u, u + 1} (X.SeparatedFiniteEtaleOver ⥤ FintypeCat)
```

because `CategoryTheory.Aut` is taken in the **functor** category and that category's universes
are not the base's. `#check` reports the inferred result type as `Type (u + 1)`.

**Both are quoted in the shape Lean prints them**: two lines, the class indented under a first
line that names no type at all, and the standard *Type class instance resolution failures can be
inspected with the `set_option trace.Meta.synthInstance true` command* hint below them, which is
the one part elided above. That is the shape `OkaTest/GaloisCategory.lean`'s own synthesis-failure
`#guard_msgs` record, and a quotation that folds the two lines into one — dropping *instance of
type class* — is a message no run of either probe produces.

## Main definitions

- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.fundamentalGroup`: **the fundamental
  group of the base at a point**, as the automorphism group of the `FintypeCat`-valued fibre
  functor there.
- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.contActionEquivalence`: **the covers
  separated over a Hausdorff, preconnected, nonempty base are equivalent to the finite discrete
  continuous actions of that group.**

## Main results

- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.contActionEquivalence_comp_forget₂`: the
  finite set underlying the action classifying a cover **is** its fibre, as an equality of
  functors, and it is `rfl`.
- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.smul_fiber`: the action is evaluation of
  the natural transformation, also `rfl`.
- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.nonempty_iso_iff` and
  `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.exists_iso_functor_obj`: the two halves
  of the equivalence spelled out — two covers are isomorphic exactly when the actions classifying
  them are, and every such action classifies a cover.
- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.isPretransitive_fundamentalGroup`: **the
  group acts transitively on the fibre of a connected cover.**
- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.exists_isConnected_decomposition`:
  **every cover separated over such a base is a finite coproduct of connected ones**, connected in
  the sense of `CategoryTheory.PreGaloisCategory.IsConnected`.
- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.exists_isGalois_hom`: **every connected
  such cover is dominated by a Galois one.**

## The two lists above are written in full, and what reads them

**Every head in the two lists above is the whole name**, with the house `…` elision kept for the
prose below them — which is the shape `Oka/AnalyticSpace/EmptyBase.lean` uses — **because
`scripts/guard_coverage.py` resolves a backticked token of a `## Main results` section against the
declaration dump and an elided one resolves to nothing.** **The list as written gives that tool ten
backticked tokens and seven of them resolve**, the other three being `rfl` twice and
`CategoryTheory.PreGaloisCategory.IsConnected`, none of which this repository declares. **Elide
the seven heads — which is what the first draft of this file did — and the same ten tokens
resolve to nothing at all**: every result here is then outside the population that tool checks,
and *no gap for this module* means *nothing read* rather than *nothing wrong*, two reports that
look identical from the outside.

Its four figures that this file moves, at the commit this file is cut from and at the one that
adds it, each end a run of `python3 scripts/guard_coverage.py --dump …` against a declaration dump
built there:

| `scripts/guard_coverage.py` | cut from | adds this file |
|---|---|---|
| advertised in a `## Main results` | **1474**, in 224 files | **1481**, in 225 files |
| of those, unguarded | **142** | **142** |
| in both lists | **1332** | **1339** |
| guarded and advertised nowhere | **637** | **639** |

**Seven of the nine declarations here are in that list and two are not**, which is the whole of the
seven in the first and third rows and of the two in the last:
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.fundamentalGroup` and
`…SeparatedFiniteEtaleOver.contActionEquivalence` are under `## Main definitions`, a heading that
tool does not read at all, so they count as guarded and advertised nowhere however they are
spelled. **All nine are guarded**, in `OkaTest/Axioms/Morphisms.lean`, and *unguarded* is unmoved
in both its figures — this file opens no gap, and now that is a reading and not a silence.

## What is not here

* **No comparison between `CategoryTheory.PreGaloisCategory.IsConnected` and `ConnectedSpace` of a
  cover's total space is made in this module, and since 2026-09-20 one is made in the tree.** The
  three results above whose statement carries that condition are about the **categorical** one,
  which is a condition on an object of this category — not initial, and every monomorphism into it
  either initial or an isomorphism. **At the commit this file is cut from no declaration under
  `Oka/` states an implication either way**: that clause is pinned to a commit that has passed and
  stays exact where it stands. **What the tree does past that commit is another matter, and this
  bullet is narrowed rather than retired.**
  `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.isConnected_iff_connectedSpace`
  (`Oka/AnalyticSpace/ConnectedCover.lean`, taxis #2082) proves the two conditions **equivalent**
  over a Hausdorff preconnected base, which is a pair of hypotheses every statement here already
  carries — so **every piece `…SeparatedFiniteEtaleOver.exists_isConnected_decomposition` produces
  has connected total space**, which is that equivalence read at each `f i` and is the whole of
  what this narrowing buys. **It does not make the pieces the topological connected components of
  the total space**: that reading needs the categorical coproduct's total space to be the
  topological disjoint union of the pieces' and needs an isomorphism of this category to be a
  homeomorphism on total spaces, and **neither is stated in this repository** — that module's
  `## What is not here` names the three steps and says which of their instruments are already in
  the tree. **So the misreading this bullet exists to stop is still a misreading, and what has
  changed is that the true statement one step short of it is now a theorem.** **The clause this
  bullet carried until 2026-09-20 was *nothing in this repository relates it to connectedness of
  the space*, in the present tense, and the push that adds that module is what falsified it**; the
  dated record is here rather than at the pinned sentence beside it, which needed none. **What is
  still not proved is the comparison over a base that is not Hausdorff or not preconnected**, and
  that module's own `## What is not here` says so and says that neither hypothesis is shown to be
  needed. **That module neither imports
  this one nor is imported by it** — both are cut from `Oka/AnalyticSpace/GaloisCategory.lean` —
  so nothing above depends on it and no statement here is restated there.
* **No comparison with the topologist's fundamental group.** The group below is the automorphism
  group of a fibre functor, which is profinite — `Mathlib/CategoryTheory/Galois/Topology.lean`
  declares `CompactSpace`, `T2Space`, `TotallyDisconnectedSpace` and `IsTopologicalGroup` at
  `CategoryTheory.Aut` of one, all four anonymously and none of them here — and `FundamentalGroup`
  of `Mathlib/Topology/Homotopy/FundamentalGroup.lean` is not. **No statement here relates the
  two**, in Lean or in prose, and the two are not isomorphic in general. **And the in-tree module
  a reader is likeliest to confuse this one with is the other file of this name**,
  `Oka/Analysis/Complex/FundamentalGroup.lean`, which computes that `FundamentalGroup` for the
  punctured plane and is mirror-tree material for Mathlib. Nothing below bears on it, it imports
  nothing of this development, and a reader who came here for it wants that path.
* **Nothing about analytification and nothing about a scheme.** This is the analytic side alone.
  The comparison functor and the Riemann existence theorem are elsewhere and nothing below bears
  on either.
* **No instance.** This file declares none: every class instance the declarations below consume
  is Mathlib's or `Oka/AnalyticSpace/GaloisCategory.lean`'s.
* **Nothing at `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver`.** Neither
  `CategoryTheory.PreGaloisCategory` nor `CategoryTheory.GaloisCategory` is stated at the ambient
  covers anywhere in this repository, and `#synth` for the first of them there fails:
  `Oka/AnalyticSpace/GaloisCategory.lean` gives the reason its own instance does not reach them —
  those covers are not separated, and the `monoInducesIsoOnDirectSummand` field is stated at the
  separated category — and `OkaTest/GaloisCategory.lean` records the failure as a `#guard_msgs`
  probe. So none of this transports to them. **That either class is *false* there is neither
  proved here nor claimed.** A failing synthesis probe cannot tell *the class does not hold* from
  *this context does not reach it*, which is the distinction `OkaTest/GaloisCategory.lean`'s own
  correction to its canary paragraph draws; settling the question in the other direction, at the
  separated covers over a base with no points, took a refutation and a module of its own,
  `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.not_galoisCategory_of_isEmpty` in
  `Oka/AnalyticSpace/EmptyBase.lean`, and nothing of that kind is done here.
-/

universe u

open CategoryTheory CategoryTheory.Limits
open scoped FintypeCatDiscrete

namespace ComplexAnalytic.AnalyticSpace

variable {X : AnalyticSpace.{u}} [T2Space (X : Type u)] [PreconnectedSpace (X : Type u)]
  [Nonempty (X : Type u)]

/-- **The fundamental group of `X` at `x`**: the automorphism group of the `FintypeCat`-valued
fibre functor at that point.

**This is a reducible abbreviation of `CategoryTheory.Aut` at that functor and nothing more.**
Every instance stated for the latter — in particular the profinite topological group structure of
`Mathlib/CategoryTheory/Galois/Topology.lean` — applies at this name unchanged, and **nothing is
stated here that is not stated at what it abbreviates.** It is written because the statements
below are about a group, and reading `CategoryTheory.Aut` of a functor as one takes a step every
time.

**It carries no type ascription**, for the reason the module docstring gives: the automorphism
group is taken in the functor category, whose universes are not the base's. -/
abbrev SeparatedFiniteEtaleOver.fundamentalGroup (x : X) :=
  Aut (SeparatedFiniteEtaleOver.fintypeFiberFunctor.{u} x)

/-- **The covers separated over a Hausdorff, preconnected, nonempty analytic space are equivalent
to the finite discrete continuous actions of the fundamental group at any point of the base.**

This is `CategoryTheory.PreGaloisCategory.functorToContAction` at this category, promoted along
Mathlib's own `IsEquivalence` instance for it. **The whole content is that the two hypotheses of
that instance are instances here**, which is what `Oka/AnalyticSpace/GaloisCategory.lean` supplies;
nothing is proved below that Mathlib does not prove for a general Galois category. -/
noncomputable def SeparatedFiniteEtaleOver.contActionEquivalence (x : X) :
    SeparatedFiniteEtaleOver.{u} X ≌
      ContAction FintypeCat (SeparatedFiniteEtaleOver.fundamentalGroup x) :=
  (PreGaloisCategory.functorToContAction
    (SeparatedFiniteEtaleOver.fintypeFiberFunctor.{u} x)).asEquivalence

/-- **The finite set underlying the action that classifies a cover is that cover's fibre**, as an
equality of functors rather than an isomorphism, and it is `rfl`.

This is what makes the equivalence above a statement about fibres: it says the classification does
not replace the fibre by something isomorphic to it, so a reader may compute with the action on
`…SeparatedFiniteEtaleOver.fintypeFiberFunctor` directly. -/
theorem SeparatedFiniteEtaleOver.contActionEquivalence_comp_forget₂ (x : X) :
    (SeparatedFiniteEtaleOver.contActionEquivalence x).functor ⋙
        forget₂ (ContAction FintypeCat (SeparatedFiniteEtaleOver.fundamentalGroup x)) FintypeCat =
      SeparatedFiniteEtaleOver.fintypeFiberFunctor.{u} x :=
  rfl

omit [T2Space (X : Type u)] [PreconnectedSpace (X : Type u)] [Nonempty (X : Type u)] in
/-- **The action of the fundamental group on a fibre is evaluation of the natural transformation**,
and it is `rfl`. Together with the equality of functors above this pins down the classifying object
completely: both its carrier and its action are the fibre functor's.

**It is the one statement in this file that asks nothing of the base**, and the `omit` is how that
is visible rather than a matter of reading: the scalar action is Mathlib's, at the automorphism
group of an arbitrary `FintypeCat`-valued functor, and none of `[T2Space]`,
`[PreconnectedSpace]` and `[Nonempty]` is reached by it. The `variable` line above binds all three,
so without the `omit` they would be arguments of this theorem that no reader could spend. -/
theorem SeparatedFiniteEtaleOver.smul_fiber (x : X) (A : SeparatedFiniteEtaleOver.{u} X)
    (g : SeparatedFiniteEtaleOver.fundamentalGroup x)
    (a : (SeparatedFiniteEtaleOver.fintypeFiberFunctor.{u} x).obj A) :
    g • a = g.hom.app A a :=
  rfl

/-- **Two covers are isomorphic exactly when the actions classifying them are.** This is full
faithfulness of the classifying functor spelled out, and it adds no mathematics to the equivalence
above. -/
theorem SeparatedFiniteEtaleOver.nonempty_iso_iff (x : X)
    (A B : SeparatedFiniteEtaleOver.{u} X) :
    Nonempty (A ≅ B) ↔
      Nonempty ((SeparatedFiniteEtaleOver.contActionEquivalence x).functor.obj A ≅
        (SeparatedFiniteEtaleOver.contActionEquivalence x).functor.obj B) :=
  ⟨Nonempty.map (SeparatedFiniteEtaleOver.contActionEquivalence x).functor.mapIso,
    Nonempty.map (SeparatedFiniteEtaleOver.contActionEquivalence x).functor.preimageIso⟩

/-- **Every finite discrete continuous action of the fundamental group classifies a cover.** This
is essential surjectivity of the classifying functor spelled out, and it too adds no mathematics to
the equivalence above. -/
theorem SeparatedFiniteEtaleOver.exists_iso_functor_obj (x : X)
    (M : ContAction FintypeCat (SeparatedFiniteEtaleOver.fundamentalGroup x)) :
    ∃ A : SeparatedFiniteEtaleOver.{u} X,
      Nonempty ((SeparatedFiniteEtaleOver.contActionEquivalence x).functor.obj A ≅ M) :=
  ⟨_, ⟨(SeparatedFiniteEtaleOver.contActionEquivalence x).counitIso.app M⟩⟩

/-- **The fundamental group acts transitively on the fibre of a connected cover.**

This is `inferInstance`, and what search finds is
`CategoryTheory.PreGaloisCategory.FiberFunctor.isPretransitive_of_isConnected`
(`Mathlib/CategoryTheory/Galois/Prorepresentability.lean`), which asks the fibre-functor class of
the functor and `CategoryTheory.PreGaloisCategory.IsConnected` of the object and nothing else. It
is written out because it is the statement a reader of the classification wants named, and because
the instance it is found by is reached only under the classes
`Oka/AnalyticSpace/GaloisCategory.lean` declares. -/
theorem SeparatedFiniteEtaleOver.isPretransitive_fundamentalGroup (x : X)
    (A : SeparatedFiniteEtaleOver.{u} X) [PreGaloisCategory.IsConnected A] :
    MulAction.IsPretransitive (SeparatedFiniteEtaleOver.fundamentalGroup x)
      ((SeparatedFiniteEtaleOver.fintypeFiberFunctor.{u} x).obj A) :=
  inferInstance

/-- **Every cover separated over a Hausdorff, preconnected, nonempty base is a finite coproduct of
connected ones.**

*Connected* is `CategoryTheory.PreGaloisCategory.IsConnected`, a condition on an **object of this
category**, and over this statement's own hypotheses it is equivalent to `ConnectedSpace` of the
cover's total space —
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.isConnected_iff_connectedSpace` of
`Oka/AnalyticSpace/ConnectedCover.lean`, a module this one neither imports nor is imported by. **So
every piece this theorem produces has connected total space.** **It does not follow that the pieces
are the topological connected components of `A.left`**, and that step is not taken anywhere in this
repository: it asks for the total space of `∐ f` to be the topological disjoint union of the
`(f i).left` and for the isomorphism above to be a homeomorphism, which are two further statements
— the second cheap and the first not — and that module's `## What is not here` prices both. This
sentence read *the module docstring's `## What is not here` records that nothing in this repository
relates it to connectedness of the cover's total space* until 2026-09-20, when that comparison
landed; the bullet it named carries the dated record and the pin beside it.

**No point of the base appears in the statement.** Mathlib's
`CategoryTheory.PreGaloisCategory.has_decomp_connected_components'` takes the Galois category and
not a fibre functor, so there is nothing to choose here. -/
theorem SeparatedFiniteEtaleOver.exists_isConnected_decomposition
    (A : SeparatedFiniteEtaleOver.{u} X) :
    ∃ (ι : Type) (_ : Finite ι) (f : ι → SeparatedFiniteEtaleOver.{u} X) (_ : ∐ f ≅ A),
      ∀ i, PreGaloisCategory.IsConnected (f i) :=
  PreGaloisCategory.has_decomp_connected_components' A

/-- **Every connected cover separated over such a base is dominated by a Galois one**: there is a
Galois cover with a morphism to it.

**No point of the base appears in the statement either, and here that takes an argument.**
`CategoryTheory.PreGaloisCategory.exists_hom_from_galois_of_connected` takes the fibre functor
explicitly, and every fibre functor this repository has is taken at a point of the base;
`CategoryTheory.PreGaloisCategory.GaloisCategory.getFiberFunctor` is the one the class carries and
it takes none, so it is what this proof feeds the lemma. -/
theorem SeparatedFiniteEtaleOver.exists_isGalois_hom (A : SeparatedFiniteEtaleOver.{u} X)
    [PreGaloisCategory.IsConnected A] :
    ∃ (B : SeparatedFiniteEtaleOver.{u} X) (_ : B ⟶ A), PreGaloisCategory.IsGalois B :=
  PreGaloisCategory.exists_hom_from_galois_of_connected
    (PreGaloisCategory.GaloisCategory.getFiberFunctor _) A

end ComplexAnalytic.AnalyticSpace
