/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.AnalyticSpace.SeparatedFiniteEtale

/-!
# The fibre functor at the separated covers, and the two axioms of it that are reachable

`Oka/AnalyticSpace/FiniteEtaleOver.lean` builds the fibre at a point of the base as a functor out
of `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver X`, into `Type u` and into `FintypeCat`, and
proves of it everything this repository knows about a fibre functor: that it preserves the terminal
object, that it is faithful, and that it is conservative. **All of that is stated one category out
from where the Galois-category axioms are being assembled.**

`Mathlib/CategoryTheory/Galois/Basic.lean` — whose namespace is not in this repository's import
closure and so cannot be cited by name here — asks for two things at once: a `PreGaloisCategory`
structure on a category, and a `FiberFunctor` structure on a functor out of **that same category**
into `FintypeCat`. The first of those is being built at
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver X`, where
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.hasTerminal` and
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.inducesIsoOnDirectSummand_of_mono'` already
are. **This file is the fibre functor at that category**, and the two of its six obligations that
are reachable without a new import.

**That sentence read *the two of its six obligations that are reachable with what is in the tree*,
until 2026-09-15**, when `Oka/AnalyticSpace/SeparatedFiberFunctorCoproducts.lean` — the only
module under `Oka/` whose own `import` lines name both this one and
`Oka/AnalyticSpace/SeparatedFiniteEtaleCoproducts.lean`, the aggregator `Oka.lean` naming both as
it names every module — landed a third at these two functors, the
preservation of finite coproducts. **The numeral in the repaired sentence is not three, and that is
deliberate**: a second branch was in review at the time of writing which states the preservation of
pullbacks at these same two functors in a module of its own, and it moves the same count
independently of this one, so *two of its six obligations that are reachable without a new import*
is the claim that is true whichever of the two lands and in whichever order.
**What the wording had wrong is its scope and not its numeral**: two is still what is reachable
here, and the bullet below opening *Not the preservation of finite
coproducts* is where the one that moved is recorded. **The numeral in this file's `#` heading and in
the heading of the section of `OkaTest/Axioms/Morphisms.lean` that guards this module counts what
this module carries, which is unmoved at two**, and neither heading is touched.

## The `[T2Space]` that stops being a hypothesis, which is the one thing here that is not transport

At the covers, faithfulness and conservativity of the fibre functor hold on the full subcategory
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isPreconnectedT2`, whose objects satisfy **two**
conditions on their total space — preconnected *and* Hausdorff. Over a Hausdorff base the second is
free here: `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.t2Space_left` is an instance, so
every `[T2Space (B.left)]` an ambient lemma asks for is discharged by the object that carries it.

**So the subcategory this file cuts,
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.isPreconnected`, is one condition and not
two**, and that is the form that matters for a Galois category: the conservativity axiom is about
the category the other axioms are stated over, so every condition that has to be cut away from it
is a gap between what is proved and what the axiom asks. This file closes one of the two and
leaves the other.

**Where the hypothesis is spent instead** is the variable block: `[T2Space (X : Type u)]` on the
base, which is what `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.t2Space_left` consumes.
The terminal-object statements below are outside that block and ask for nothing at all.

## What is transported, and how

The two functors are composites with
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.toFiniteEtaleOver`, which is full and
faithful, and every statement below is that functor's ambient counterpart read across it:

* **faithfulness** is `CategoryTheory.Functor.map_injective` of the inclusion composed with the
  ambient injectivity — the inclusion contributes the outer injection and the ambient lemma the
  inner one;
* **conservativity** is `CategoryTheory.isIso_of_reflects_iso` twice, once along the inclusion and
  once along the subcategory's;
* **the terminal object** is *not* transported, and could not be: a fully faithful functor does not
  carry terminal objects without an argument about its essential image.
  `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.isTerminalId` is the cone, proved in its
  own category for that reason, and what the inclusion contributes is one `rfl` —
  `(…toFiniteEtaleOver X).obj (…SeparatedFiniteEtaleOver.id X)` **is**
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.id X`, so the ambient fibre computation applies to
  it unchanged.

**The instance arguments are passed positionally and that is deliberate.**
`Oka/AnalyticSpace/FiniteEtaleOver.lean`'s `faithful_fiberFunctor` docstring records the seam: the
comma category's `A.left` and `((…toFiniteEtaleOver X).obj A).left` are the same by `rfl` and not
reducibly so, so instance search does not cross between them and a `haveI` does not repair it.
Every `@`-application below is that, and none of them is a mathematical step.

## Main results

- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.fiberFunctor` and
  `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.fintypeFiberFunctor`: **the fibre at a
  point of the base, as a functor out of the separated covers**, into `Type u` and into
  `FintypeCat`; the second is the shape a Galois category asks for.
- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.preservesTerminal_fiberFunctor` and
  `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.preservesTerminal_fintypeFiberFunctor`:
  **both preserve the terminal object**, with no hypothesis on the base and none on the point.
- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.isPreconnected`: **the separated covers
  whose total space is preconnected**, as a full subcategory, with its terminal object
  `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.hasTerminalSubcategory` and the
  preservation
  `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.preservesTerminal_ι`.
- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.fiberFunctor_map_injective` and
  `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.fintypeFiberFunctor_map_injective`:
  **both are injective on morphisms out of a preconnected object**, with nothing asked of the
  target.
- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.faithful_fiberFunctor` and
  `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.faithful_fintypeFiberFunctor`: **both are
  faithful on that subcategory.**
- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.isIso_of_bijective_fiberMap`: **a
  morphism whose fibre map at one point is bijective is an isomorphism**, over a preconnected
  target.
- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.reflectsIsomorphisms_fiberFunctor` and
  `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.reflectsIsomorphisms_fintypeFiberFunctor`:
  **both are conservative on that subcategory** — the sixth Galois-category obligation on a fibre
  functor.

## What is not here

* **No `FiberFunctor` instance, and no `PreGaloisCategory` instance to hang one on.** It is
  `FiberFunctor` that has **six** fields — preservation of terminal objects, of pullbacks, of
  finite coproducts, of epimorphisms and of quotients by finite group actions, and reflection of
  isomorphisms — and this file supplies the **first and the last** and says nothing about the other
  four. It is not a partial instance and no `PreGaloisCategory` instance is declared anywhere in
  this repository; at the commit that adds this file, `PreGaloisCategory` occurs in the
  comment-stripped code of no module of it at all.
* **Not the preservation of pullbacks, and the obstruction is not a missing instance.**
  `Oka/AnalyticSpace/SeparatedFiniteEtaleLimits.lean` gives the fibre product of separated covers
  over a Hausdorff base, so the limit whose image would have to be computed exists; what is missing
  is an identification of the **fibre** of that limit with the set-theoretic pullback of the two
  fibres. That file is **a sibling of this module which neither imports it nor is imported by it,
  both importing `Oka/AnalyticSpace/SeparatedFiniteEtale.lean`**, so
  `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.fibreProd` is not in scope below and
  nothing here could consume it without a new import — the relation, and the consequence, that the
  bullet opening *Not the preservation of finite coproducts* records for
  `Oka/AnalyticSpace/SeparatedFiniteEtaleCoproducts.lean`. **That relation is measured and not
  asserted**: by a transitive walk of the `Oka`-prefixed `import` lines of the comment-stripped
  code of every tracked `.lean`, each of the two modules has a closure of **75** modules counting
  itself at the commit that adds this clause, neither closure holds the other module, and
  `Oka/AnalyticSpace/SeparatedFiniteEtale.lean` is the only `import` line either file has.
  **Measured rather than asserted**: `Function.Pullback`, which is how this repository
  spells such an identification, occurs in the comment-stripped code of **six** modules at the
  commit that adds this file — `Oka/AnalyticSpace/FiniteEtaleBaseChange.lean`,
  `Oka/Topology/Covering/Basic.lean`, `Oka/Topology/IsLocalHomeomorph.lean`,
  `Oka/Topology/Maps/Proper/Basic.lean`, `OkaTest/Axioms/Morphisms.lean` and
  `OkaTest/CoveringBaseChange.lean` — the first two being the base change of a finite étale
  morphism over its own cospan and the topological statement it rests on, and the two after them
  the mirror-tree base change of a local homeomorphism and of a proper map at that same fibre
  product. **`OkaTest/Axioms/Morphisms.lean` is in that list for its single occurrence, the guard
  `#print axioms Function.Pullback.finite_fiber_snd`, and not for being about a fibre product of
  covers**: at the commit that adds this clause that file guards **twelve** declarations of
  `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver` whose names carry `fibreProd`,
  `…fibreProd` itself among them. **None of the six's `Function.Pullback` occurrences is about
  `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.fibreProd`**, and nothing carries
  the identification to it.

  **What this bullet says is not in *this* module is unchanged, and what it is supplied by
  elsewhere is `Oka/AnalyticSpace/SeparatedFiberPullback.lean` since 2026-09-15** — the module that
  imports this one and `Oka/AnalyticSpace/SeparatedFiniteEtaleLimits.lean` and states what neither
  could. **So the bullet's opening sentence is neither retired nor dated**: `README.md`'s test for
  a record is that the wording read true before the day the record gives and *stopped*, and no
  declaration below mentions a fibre product now any more than it did. **One clause of this bullet
  did stop, and it is the clause *and nothing carries the identification to it* that closes the
  sentence above.**

  **That clause read so until 2026-09-15**, when
  `Oka/AnalyticSpace/SeparatedFiberPullback.lean` carried it:
  `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.fibreProdFiberEquiv` is the
  identification, and the fibre functor's preservation of pullbacks is what it was wanted for.
  **The rest of this bullet is untouched and none of its figures moves**, which is a reading of
  them and not a re-run: *the obstruction is not a missing instance* and the sibling relation are
  claims about this module and its two neighbours, and that module imports both of them rather
  than changing either; the **six** `Function.Pullback` modules and the two closures of **75** are
  pinned *at the commit that adds this file* and *at the commit that adds this clause*, and a
  pinned figure survives a push that moves it. **The live count is seven**, that module being the
  seventh, and it is given here rather than written over the pinned one.

  **One thing about the instrument, found by getting it wrong.** *A transitive walk of the
  `Oka`-prefixed `import` lines* is exact only if `public import` lines are followed as well: 29 of
  the 240 tracked `.lean` files under `Oka/` open with `module` and write their imports that way,
  13 of them carrying a `public import Oka…` line, and a walk anchored on `^import Oka` alone
  returns **61** for this module where the closure is **75**, silently and with no unparsed line to
  report. The figures above are right; what is under-specified is the phrase, and the check that
  needs no walk is `env.allImportedModuleNames` filtered to the `Oka` prefix in a file importing
  the module.
  **That sentence read *None of the six is about* that name, until 2026-09-14, and under the
  reading its own enumeration invites it was false when written rather than falsified later, so
  this is a correction and not one of this repository's dated records**: taken as a claim about the
  six modules, the guard file refutes it, and that file has carried those twelve guards since
  `4d40d05` on 2026-09-12, two days before the push that wrote the sentence. Taken as a claim about
  the occurrences the enumeration counts — which is the reading the bullet's argument needs — it is
  true, and that is what it now says. `OkaTest/Axioms/Morphisms.lean` records the neighbouring
  rule, *A sentence in a guard file that enumerates where a name occurs must count the guard
  file*, and that one is scoped to sentences **in** a guard file, which this is not; what the two
  share is a guard file inside the population being enumerated, and the cost of naming it without
  saying what it is doing there. The bullet opening *Not the preservation of finite coproducts*
  names that same file as the one *which guards it* and this one did not.
* **Not the preservation of finite coproducts, and what is absent is the statement and not the
  colimit.** Finite coproducts of this category are in the tree —
  `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.hasFiniteCoproducts`, with no hypothesis
  on the base — but they are in `Oka/AnalyticSpace/SeparatedFiniteEtaleCoproducts.lean`, **a
  sibling of this module which neither imports it nor is imported by it, both importing
  `Oka/AnalyticSpace/SeparatedFiniteEtale.lean`**, so that instance is not in scope below and
  nothing here could consume it without a new import. The ambient preservation statement
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.preservesFiniteCoproducts_fintypeFiberFunctor` is
  in this module's closure; what is not here is either that read across the inclusion or an
  identification of the fibre of a disjoint union of separated covers with the disjoint union of
  the fibres. **Measured rather than asserted**: `preservesFiniteCoproducts` occurs in the
  comment-stripped code of exactly **two** modules at the commit that adds this file —
  `Oka/AnalyticSpace/FiniteEtaleOver.lean`, which declares it, and `OkaTest/Axioms/Morphisms.lean`,
  which guards it — and neither is about a functor out of
  `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver`.
  **Everything in this bullet is still true of this file and the statement it says is absent is no
  longer absent from the tree, since 2026-09-15**: it is
  `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.preservesFiniteCoproducts_fiberFunctor`
  and
  `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.preservesFiniteCoproducts_fintypeFiber`
  in `Oka/AnalyticSpace/SeparatedFiberFunctorCoproducts.lean`, which imports this module and that
  sibling and takes the first of the two routes this bullet names — the ambient preservation read
  across the inclusion, the inclusion itself being shown to preserve finite coproducts there.
  **The two pinned figures above are not retired by that push and are not restated by it**: both
  are read at the commit that adds this file, and a scan of the same token at any later commit is a
  different measurement — at the commit that adds that module the count is **three**, the third
  being the module itself.
  **This paragraph is a pointer and not one of this repository's dated records**, which is why it
  does not use the `until <date>` spelling and why neither census of those records moves for it:
  a record says what a clause read *until* some day and presupposes that it stopped reading true,
  and every sentence of this bullet is as true at the commit that adds that module as at the
  commit that wrote it. What changed is the tree the bullet sits in, not the bullet.
* **Not the preservation of epimorphisms and not quotients by finite group actions**, and the two
  absences are not the same shape. `CategoryTheory.SingleObj`, which is the shape the quotients
  field is stated over, occurs in the comment-stripped code of exactly **one** module of this
  repository at the commit that adds this file — `Oka/CategoryTheory/Limits/Shapes/SingleObj.lean`,
  a mirror-tree module which neither imports this one nor is imported by it and which nothing under
  `Oka/` imports, and whose one declaration gives colimits of that shape at any category with
  `CategoryTheory.Limits.HasFiniteColimits`. **Neither category of covers has that class at that
  commit**, so what is absent for quotients is a colimit and not a statement about the shape.
  **Two modules of this repository declare an instance of
  `CategoryTheory.Functor.PreservesEpimorphisms`** — `Oka/Algebra/Category/Grp/EpiMono.lean` and
  `Oka/Algebra/Category/ModuleCat/Sheaf/Colimits.lean` — and **neither is about a cover or about a
  fibre functor**, so what is absent there is the statement at these functors and not the class.
  **That count is of instances and not of occurrences of a name**, which the
  `CategoryTheory.SingleObj` count in this bullet is, and the two registers do not agree here: both
  modules spell the class by dot notation on the functor, so the literal
  `CategoryTheory.Functor.PreservesEpimorphisms` occurs in the comment-stripped code of **no**
  module of this repository.
* **Nothing at `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver` is superseded or restated.**
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isPreconnectedT2` and every statement over it are
  unchanged and stay the right ones for a caller working in the covers, which is the reason
  `Oka/AnalyticSpace/SeparatedDirectSummand.lean` gives for the same asymmetry at the direct
  summand.
* **The subcategory's preconnectedness condition is not removed and this file does not argue that
  it could be.** It is the hypothesis
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isIso_of_bijective_fiberMap` asks of its target
  and `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fiberFunctor_map_injective` asks of its
  source; what this file removes is the **Hausdorff** half of the ambient subcategory's condition
  and nothing else.
-/

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

universe u

namespace ComplexAnalytic.AnalyticSpace

variable {X : AnalyticSpace.{u}}

/-! ### The two fibre functors -/

/-- **The fibre at a point of the base, as a functor out of the separated covers.**

`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fiberFunctor` composed with the inclusion
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.toFiniteEtaleOver`, which is all it is: an
object of this category is an object of the covers carrying one extra proof, and the fibre does not
see the proof.

**It is stated as a composite rather than restated with its own `obj` and `map` fields**, so that
`CategoryTheory.Functor.comp` is what the two functor laws come from and no `rfl` is re-proved
here. The cost is that every statement below has to unfold one composite to reach the ambient
lemma, and the benefit is that `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fiberMap` is
literally the map. -/
def SeparatedFiniteEtaleOver.fiberFunctor (x : X) :
    SeparatedFiniteEtaleOver.{u} X ⥤ Type u :=
  SeparatedFiniteEtaleOver.toFiniteEtaleOver X ⋙ FiniteEtaleOver.fiberFunctor.{u} x

/-- **The same into `FintypeCat`**, which is the shape a Galois category asks for.

`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fintypeFiberFunctor` composed with the same
inclusion. **This is the functor a `FiberFunctor` structure would be asked of**, that structure
living in `Mathlib/CategoryTheory/Galois/Basic.lean`, whose namespace is not in this repository's
import closure and so cannot be cited by name here.

**No import is added for it**: `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fintypeFiberFunctor`
already pays for `Mathlib.CategoryTheory.FintypeCat` and this file imports
`Oka/AnalyticSpace/SeparatedFiniteEtale.lean`, which is downstream of it. -/
def SeparatedFiniteEtaleOver.fintypeFiberFunctor (x : X) :
    SeparatedFiniteEtaleOver.{u} X ⥤ FintypeCat.{u} :=
  SeparatedFiniteEtaleOver.toFiniteEtaleOver X ⋙ FiniteEtaleOver.fintypeFiberFunctor.{u} x

/-! ### Both preserve the terminal object -/

/-- **The value of the `FintypeCat`-valued fibre functor at the base over itself is terminal.**

`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isTerminalFintypeFiberId` **applies to this
statement unchanged**, and the reason is one `rfl`:
`(…SeparatedFiniteEtaleOver.toFiniteEtaleOver X).obj (…SeparatedFiniteEtaleOver.id X)` is
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.id X` on the nose, both being
`CategoryTheory.MorphismProperty.Over.mk` at the identity with a proof, and the proofs are
propositions. So the two sides of this `def` are the same type and the ambient declaration is the
term.

**Nothing about the terminal object of this category is transported along the inclusion.** That is
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.isTerminalId`, proved in its own category
for the reason its docstring gives — a terminal object does not cross a fully faithful functor
without an argument about the essential image — and what is shared is only the *fibre* of the one
object the two categories name the same way. -/
def SeparatedFiniteEtaleOver.isTerminalFintypeFiberId (x : X) :
    Limits.IsTerminal ((SeparatedFiniteEtaleOver.fintypeFiberFunctor.{u} x).obj
      (SeparatedFiniteEtaleOver.id.{u} X)) :=
  FiniteEtaleOver.isTerminalFintypeFiberId.{u} x

/-- **The `Type u`-valued fibre functor preserves the terminal object**, with no hypothesis on the
base and none on the point.

`CategoryTheory.Limits.preservesLimit_of_preserves_limit_cone` at
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.isTerminalId`, with
`CategoryTheory.Limits.isLimitMapConeEmptyConeEquiv` turning *the image cone is a limit* into *the
image object is terminal* and `CategoryTheory.Limits.Types.isTerminalEquivUnique` reading the
latter off `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.uniqueFiberId`, the fibre of the base
over itself being a point.

**This is the `preservesTerminalObjects` field of a `FiberFunctor` structure, at this category.**
It is one field of six and this instance supplies none of the other five; the module docstring's
`## What is not here` says which they are and why each is out of reach.

**The conclusion is `CategoryTheory.Limits.PreservesLimitsOfShape` at the empty shape and not
`CategoryTheory.Limits.PreservesLimit` at `CategoryTheory.Functor.empty`**, for the reason
`…FiniteEtaleOver.preservesLimitsOfShape_pempty_fiberFunctor`'s
docstring gives at length: the converter between them is a `lemma` in one direction and an instance
in the other, so the stronger spelling costs a line here and saves it at every use.

**The name says `preservesTerminal` where the ambient one says `preservesLimitsOfShape_pempty`, and
the reason is arithmetic and not taste.** `OkaTest/Axioms/Morphisms.lean` guards every declaration
of this module with a `#print axioms` command, and that command's name has to fit a line: this
namespace is nine characters longer than
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver`, and
`preservesLimitsOfShape_pempty_fintypeFiberFunctor` under it does not fit even wrapped onto its own
indented line. **The three instances of this shape are named for what they preserve instead**, which
is `CategoryTheory.Limits.preservesLimitsOfShape_pempty_of_preservesTerminal`'s own word for it, and
the statements are unchanged and are the ambient spelling. -/
instance SeparatedFiniteEtaleOver.preservesTerminal_fiberFunctor (x : X) :
    Limits.PreservesLimitsOfShape (Discrete PEmpty.{1})
      (SeparatedFiniteEtaleOver.fiberFunctor.{u} x) :=
  haveI : Limits.PreservesLimit (Functor.empty.{0} (SeparatedFiniteEtaleOver.{u} X))
      (SeparatedFiniteEtaleOver.fiberFunctor.{u} x) :=
    Limits.preservesLimit_of_preserves_limit_cone (SeparatedFiniteEtaleOver.isTerminalId.{u} X)
      ((Limits.isLimitMapConeEmptyConeEquiv _ _).symm
        ((Limits.Types.isTerminalEquivUnique _).symm (FiniteEtaleOver.uniqueFiberId.{u} x)))
  Limits.preservesLimitsOfShape_pempty_of_preservesTerminal _

/-- **The same for the `FintypeCat`-valued fibre functor**, which is the one a Galois category asks
for.

The same proof with
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.isTerminalFintypeFiberId` in place of the
inline conversion, for the reason that declaration's docstring gives about the bundling, and in the
same `CategoryTheory.Limits.PreservesLimitsOfShape` spelling. **Neither of the two is derived from
the other**: the two functors have the same underlying map and different bundlings of it, so
`CategoryTheory.Limits.IsTerminal` of one value is not `CategoryTheory.Limits.IsTerminal` of the
other, which is the distinction
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fintypeFiberFunctor_map_injective`'s docstring draws
for its own pair. -/
instance SeparatedFiniteEtaleOver.preservesTerminal_fintypeFiberFunctor (x : X) :
    Limits.PreservesLimitsOfShape (Discrete PEmpty.{1})
      (SeparatedFiniteEtaleOver.fintypeFiberFunctor.{u} x) :=
  haveI : Limits.PreservesLimit (Functor.empty.{0} (SeparatedFiniteEtaleOver.{u} X))
      (SeparatedFiniteEtaleOver.fintypeFiberFunctor.{u} x) :=
    Limits.preservesLimit_of_preserves_limit_cone (SeparatedFiniteEtaleOver.isTerminalId.{u} X)
      ((Limits.isLimitMapConeEmptyConeEquiv _ _).symm
        (SeparatedFiniteEtaleOver.isTerminalFintypeFiberId.{u} x))
  Limits.preservesLimitsOfShape_pempty_of_preservesTerminal _

/-! ### The preconnected subcategory, which is one condition and not two -/

variable (X) in
/-- **The separated covers whose total space is preconnected**, as an
`CategoryTheory.ObjectProperty` and hence as a full subcategory.

**One condition, where the ambient subcategory
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isPreconnectedT2` has two.** The Hausdorff half of
that conjunction is carried by every object of this category over a Hausdorff base —
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.t2Space_left` is an instance — so cutting
it out here would be cutting out nothing. The module docstring's section *The `[T2Space]` that
stops being a hypothesis* is what this is about and says why the difference is not cosmetic.

**The condition is on the total space of the object and not on the base**, exactly as the ambient
one is; the base's own preconnectedness is a separate hypothesis and appears in the variable block
of the statements that need it. -/
def SeparatedFiniteEtaleOver.isPreconnected : ObjectProperty (SeparatedFiniteEtaleOver.{u} X) :=
  fun A ↦ PreconnectedSpace (A.left : Type u)

/-- **The base over itself is an object of that subcategory**, when the base is preconnected.

`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.id`'s total space is the base on the nose,
so this is one `inferInstanceAs` and no proof. **It asks no `[T2Space]`**, which
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isPreconnectedT2_id` does, and the difference is the
subcategory's condition and not a different argument. -/
theorem SeparatedFiniteEtaleOver.isPreconnected_id (X : AnalyticSpace.{u})
    [PreconnectedSpace (X : Type u)] :
    SeparatedFiniteEtaleOver.isPreconnected.{u} X (SeparatedFiniteEtaleOver.id.{u} X) :=
  inferInstanceAs (PreconnectedSpace (X : Type u))

/-- **The base over itself is terminal in that subcategory too**, when the base is preconnected.

`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.isTerminalId` read in the full subcategory:
the unique morphism into it is the ambient one, which lies in the subcategory because the
subcategory is full, and uniqueness is `CategoryTheory.ObjectProperty.hom_ext`.

**`CategoryTheory.ObjectProperty.homMk` and `CategoryTheory.ObjectProperty.hom_ext` are the two
functions that cross the seam**, and going through them keeps this computable, for the reason
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isTerminalIdSubcategory`'s docstring gives: the
other route is `CategoryTheory.Functor.preimage` at `CategoryTheory.ObjectProperty.ι`, which is
data extracted from a `CategoryTheory.Functor.Full` instance. -/
def SeparatedFiniteEtaleOver.isTerminalIdSubcategory (X : AnalyticSpace.{u})
    [PreconnectedSpace (X : Type u)] :
    Limits.IsTerminal
      (⟨SeparatedFiniteEtaleOver.id.{u} X, SeparatedFiniteEtaleOver.isPreconnected_id.{u} X⟩ :
        (SeparatedFiniteEtaleOver.isPreconnected.{u} X).FullSubcategory) :=
  Limits.IsTerminal.ofUniqueHom
    (fun A ↦ ObjectProperty.homMk ((SeparatedFiniteEtaleOver.isTerminalId.{u} X).from A.obj))
    fun _ _ ↦ ObjectProperty.hom_ext _
      ((SeparatedFiniteEtaleOver.isTerminalId.{u} X).hom_ext _ _)

/-- **That subcategory has a terminal object**, as the class rather than as the witness, for the
reason `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.hasTerminal`'s docstring gives. -/
instance SeparatedFiniteEtaleOver.hasTerminalSubcategory (X : AnalyticSpace.{u})
    [PreconnectedSpace (X : Type u)] :
    Limits.HasTerminal (SeparatedFiniteEtaleOver.isPreconnected.{u} X).FullSubcategory :=
  (SeparatedFiniteEtaleOver.isTerminalIdSubcategory.{u} X).hasTerminal

/-- **The subcategory inclusion preserves the terminal object.**

**A subcategory inclusion does not preserve limits in general** — a full subcategory closed under
nothing need not contain the ambient limit — and what makes it do so here is that the ambient
terminal object lies in the subcategory, which is
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.isPreconnected_id`. **This is where
`[PreconnectedSpace X]` enters**, and it is the only hypothesis this statement has; the ambient
counterpart `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.preservesLimitsOfShape_pempty_ι` also
asks `[T2Space X]`, and that is the difference the module docstring is about.

**Composed with
`…SeparatedFiniteEtaleOver.preservesTerminal_fintypeFiberFunctor` this is the instance
a fibre-functor structure over the subcategory would consume.** -/
instance SeparatedFiniteEtaleOver.preservesTerminal_ι (X : AnalyticSpace.{u})
    [PreconnectedSpace (X : Type u)] :
    Limits.PreservesLimitsOfShape (Discrete PEmpty.{1})
      (SeparatedFiniteEtaleOver.isPreconnected.{u} X).ι :=
  haveI : Limits.PreservesLimit
      (Functor.empty.{0} (SeparatedFiniteEtaleOver.isPreconnected.{u} X).FullSubcategory)
      (SeparatedFiniteEtaleOver.isPreconnected.{u} X).ι :=
    Limits.preservesLimit_of_preserves_limit_cone
      (SeparatedFiniteEtaleOver.isTerminalIdSubcategory.{u} X)
      ((Limits.isLimitMapConeEmptyConeEquiv _ _).symm (SeparatedFiniteEtaleOver.isTerminalId.{u} X))
  Limits.preservesLimitsOfShape_pempty_of_preservesTerminal _

variable [T2Space (X : Type u)]

/-! ### Faithfulness -/

/-- **The `Type u`-valued fibre functor is injective on morphisms out of a preconnected object**,
over a preconnected Hausdorff base, **with nothing asked of the target**.

Two injections composed. `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.toFiniteEtaleOver`
is faithful, so `CategoryTheory.Functor.map_injective` is the outer one; the inner one is
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fiberFunctor_map_injective` at the images of the two
objects.

**The target's `[T2Space]` is supplied and not assumed**, which is the whole point of stating this
here: that lemma asks `[T2Space (B.left)]`, and
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.t2Space_left` is what hands it over. It is
**passed positionally**, for the seam
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.faithful_fiberFunctor`'s docstring records: `B.left`
and `((…toFiniteEtaleOver X).obj B).left` are the same by `rfl` and not reducibly so, so instance
search does not cross between them and a `haveI` does not repair it. -/
theorem SeparatedFiniteEtaleOver.fiberFunctor_map_injective
    [PreconnectedSpace (X : Type u)] (x : X) {A B : SeparatedFiniteEtaleOver.{u} X}
    [PreconnectedSpace (A.left : Type u)] :
    Function.Injective ((SeparatedFiniteEtaleOver.fiberFunctor.{u} x).map (X := A) (Y := B)) :=
  fun _ _ h ↦ (SeparatedFiniteEtaleOver.toFiniteEtaleOver X).map_injective
    (@FiniteEtaleOver.fiberFunctor_map_injective X ‹_› x
      ((SeparatedFiniteEtaleOver.toFiniteEtaleOver X).obj A)
      ((SeparatedFiniteEtaleOver.toFiniteEtaleOver X).obj B) ‹_›
      (SeparatedFiniteEtaleOver.t2Space_left B) _ _ h)

/-- **The same for the `FintypeCat`-valued fibre functor.**

`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fintypeFiberFunctor_map_injective` in place of its
`Type u`-valued partner, and **neither is derived from the other** for the reason that pair's
docstrings give: the two functors have the same map field up to the bundling their targets ask for,
`TypeCat.ofHom` there and `FintypeCat.homMk` here, and the bundling is not the same map. -/
theorem SeparatedFiniteEtaleOver.fintypeFiberFunctor_map_injective
    [PreconnectedSpace (X : Type u)] (x : X) {A B : SeparatedFiniteEtaleOver.{u} X}
    [PreconnectedSpace (A.left : Type u)] :
    Function.Injective
      ((SeparatedFiniteEtaleOver.fintypeFiberFunctor.{u} x).map (X := A) (Y := B)) :=
  fun _ _ h ↦ (SeparatedFiniteEtaleOver.toFiniteEtaleOver X).map_injective
    (@FiniteEtaleOver.fintypeFiberFunctor_map_injective X ‹_› x
      ((SeparatedFiniteEtaleOver.toFiniteEtaleOver X).obj A)
      ((SeparatedFiniteEtaleOver.toFiniteEtaleOver X).obj B) ‹_›
      (SeparatedFiniteEtaleOver.t2Space_left B) _ _ h)

/-- **The `Type u`-valued fibre functor is faithful on the preconnected subcategory**, over a
preconnected Hausdorff base.

The theorem above at an object of the subcategory, whose membership proof `A.property` **is** the
`[PreconnectedSpace (A.left)]` it asks for, with `CategoryTheory.ObjectProperty.hom_ext` putting the
resulting equality back in the subcategory.

**Faithfulness is not one of the Galois-category axioms** — at the Mathlib revision `lakefile.toml`
pins it is an `instance` *derived* from them — so this discharges none of that structure's
obligations, exactly as
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.faithful_fintypeFiberFunctor`'s docstring records of
the ambient statement. **What does discharge one is
`…SeparatedFiniteEtaleOver.reflectsIsomorphisms_fintypeFiberFunctor` below**, and so does
`…SeparatedFiniteEtaleOver.preservesTerminal_fintypeFiberFunctor` above. -/
instance SeparatedFiniteEtaleOver.faithful_fiberFunctor [PreconnectedSpace (X : Type u)] (x : X) :
    ((SeparatedFiniteEtaleOver.isPreconnected.{u} X).ι
      ⋙ SeparatedFiniteEtaleOver.fiberFunctor.{u} x).Faithful where
  map_injective {A B} {_ _} h :=
    ObjectProperty.hom_ext _
      (@SeparatedFiniteEtaleOver.fiberFunctor_map_injective X _ ‹_› x A.obj B.obj A.property _ _ h)

/-- **The same for the `FintypeCat`-valued fibre functor**, which is the one a Galois category asks
for. -/
instance SeparatedFiniteEtaleOver.faithful_fintypeFiberFunctor [PreconnectedSpace (X : Type u)]
    (x : X) :
    ((SeparatedFiniteEtaleOver.isPreconnected.{u} X).ι
      ⋙ SeparatedFiniteEtaleOver.fintypeFiberFunctor.{u} x).Faithful where
  map_injective {A B} {_ _} h :=
    ObjectProperty.hom_ext _
      (@SeparatedFiniteEtaleOver.fintypeFiberFunctor_map_injective X _ ‹_› x A.obj B.obj A.property
        _ _ h)

/-! ### Conservativity, which is the Galois-category axiom -/

variable [PreconnectedSpace (X : Type u)]

/-- **A morphism of separated covers whose fibre map at one point is bijective is an
isomorphism**, over a preconnected Hausdorff base and a preconnected target.

`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isIso_of_bijective_fiberMap` at the image of the
morphism, then `CategoryTheory.isIso_of_reflects_iso` along
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.toFiniteEtaleOver`, which reflects
isomorphisms because it is fully faithful.

**Both of the ambient lemma's `[T2Space]` hypotheses are supplied here**, on the source *and* on
the target, by `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.t2Space_left`; what is left
to the caller is the target's preconnectedness, which is exactly the subcategory's condition below.
Both are passed positionally, for the seam recorded on
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.fiberFunctor_map_injective`. -/
theorem SeparatedFiniteEtaleOver.isIso_of_bijective_fiberMap
    {A B : SeparatedFiniteEtaleOver.{u} X} (f : A ⟶ B)
    [PreconnectedSpace (B.left : Type u)] (x : X)
    (hf : Function.Bijective (FiniteEtaleOver.fiberMap.{u} x
      ((SeparatedFiniteEtaleOver.toFiniteEtaleOver X).map f))) : IsIso f := by
  haveI : IsIso ((SeparatedFiniteEtaleOver.toFiniteEtaleOver X).map f) :=
    @FiniteEtaleOver.isIso_of_bijective_fiberMap X
      ((SeparatedFiniteEtaleOver.toFiniteEtaleOver X).obj A)
      ((SeparatedFiniteEtaleOver.toFiniteEtaleOver X).obj B) _
      (SeparatedFiniteEtaleOver.t2Space_left A) (SeparatedFiniteEtaleOver.t2Space_left B) ‹_› ‹_›
      x hf
  exact isIso_of_reflects_iso f (SeparatedFiniteEtaleOver.toFiniteEtaleOver X)

/-- **The `Type u`-valued fibre functor is conservative on the preconnected subcategory**, over a
preconnected Hausdorff base.

`CategoryTheory.isIso_iff_bijective` reads the hypothesis as bijectivity of the fibre map,
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.isIso_of_bijective_fiberMap` turns that into
an isomorphism of the ambient category, and `CategoryTheory.isIso_of_reflects_iso` along the
subcategory inclusion puts it back. The target's preconnectedness is `B.property` and is passed
positionally, for the seam recorded above.

**Conservativity is one of the six Galois-category obligations on a fibre functor**, and it is one
of the two this file supplies; the module docstring's `## What is not here` says which four it does
not. -/
instance SeparatedFiniteEtaleOver.reflectsIsomorphisms_fiberFunctor (x : X) :
    ((SeparatedFiniteEtaleOver.isPreconnected.{u} X).ι
      ⋙ SeparatedFiniteEtaleOver.fiberFunctor.{u} x).ReflectsIsomorphisms where
  reflects {A B} f h := by
    haveI : IsIso ((SeparatedFiniteEtaleOver.fiberFunctor.{u} x).map
      ((SeparatedFiniteEtaleOver.isPreconnected.{u} X).ι.map f)) := h
    have hb : Function.Bijective (FiniteEtaleOver.fiberMap.{u} x
        ((SeparatedFiniteEtaleOver.toFiniteEtaleOver X).map
          ((SeparatedFiniteEtaleOver.isPreconnected.{u} X).ι.map f))) :=
      (isIso_iff_bijective (X := FiniteEtaleOver.fiber.{u} x
        ((SeparatedFiniteEtaleOver.toFiniteEtaleOver X).obj A.obj)) _).mp this
    haveI : IsIso ((SeparatedFiniteEtaleOver.isPreconnected.{u} X).ι.map f) :=
      @SeparatedFiniteEtaleOver.isIso_of_bijective_fiberMap X _ _ A.obj B.obj _ B.property x hb
    exact isIso_of_reflects_iso f (SeparatedFiniteEtaleOver.isPreconnected.{u} X).ι

/-- **The same for the `FintypeCat`-valued fibre functor**, which is the one a Galois category asks
for.

**Not derived from the instance above and not a restatement of it**, for the reason
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.reflectsIsomorphisms_fintypeFiberFunctor`'s docstring
gives about its own pair: the two functors have the same `map` up to the bundling their targets ask
for, so `CategoryTheory.IsIso` of one is not `CategoryTheory.IsIso` of the other, and the
bijectivity has to be read off through the concrete-category forgetful functor,
`CategoryTheory.ConcreteCategory.isIso_iff_bijective`, rather than through
`CategoryTheory.isIso_iff_bijective`. -/
instance SeparatedFiniteEtaleOver.reflectsIsomorphisms_fintypeFiberFunctor (x : X) :
    ((SeparatedFiniteEtaleOver.isPreconnected.{u} X).ι
      ⋙ SeparatedFiniteEtaleOver.fintypeFiberFunctor.{u} x).ReflectsIsomorphisms where
  reflects {A B} f h := by
    haveI : IsIso ((SeparatedFiniteEtaleOver.fintypeFiberFunctor.{u} x).map
      ((SeparatedFiniteEtaleOver.isPreconnected.{u} X).ι.map f)) := h
    have hb : Function.Bijective (FiniteEtaleOver.fiberMap.{u} x
        ((SeparatedFiniteEtaleOver.toFiniteEtaleOver X).map
          ((SeparatedFiniteEtaleOver.isPreconnected.{u} X).ι.map f))) :=
      (ConcreteCategory.isIso_iff_bijective
        ((SeparatedFiniteEtaleOver.fintypeFiberFunctor.{u} x).map
          ((SeparatedFiniteEtaleOver.isPreconnected.{u} X).ι.map f))).mp this
    haveI : IsIso ((SeparatedFiniteEtaleOver.isPreconnected.{u} X).ι.map f) :=
      @SeparatedFiniteEtaleOver.isIso_of_bijective_fiberMap X _ _ A.obj B.obj _ B.property x hb
    exact isIso_of_reflects_iso f (SeparatedFiniteEtaleOver.isPreconnected.{u} X).ι

end ComplexAnalytic.AnalyticSpace
