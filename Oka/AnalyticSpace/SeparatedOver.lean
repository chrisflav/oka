/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.AnalyticSpace.Double
import Oka.AnalyticSpace.MonoDirectSummand
import Oka.Topology.SeparatedMap

/-!
# A cover whose structure morphism is separated, and the direct summand it makes free

`Oka/AnalyticSpace/MonoDirectSummand.lean` proves that a monomorphism of covers exhibits its
source as a direct summand of its target, and it asks `[T2Space B.left]` — a separation axiom on
the *total space* of the **target**. That file's own header says what that hypothesis stands
between: the statement it proves and the `monoInducesIsoOnDirectSummand` field of
`Mathlib/CategoryTheory/Galois/Basic.lean`'s `PreGaloisCategory`, which asks the
same under no hypothesis at all. `ComplexAnalytic.AnalyticSpace.exists_finiteEtaleOver_not_t2Space`
then closed the obvious escape: a cover of a Hausdorff analytic space can have a non-Hausdorff
total space, so it does not follow from separation of the base.

**This paragraph said that file asks `[T2Space A.left]` and `[T2Space B.left]` — a separation
axiom on each of the two total spaces — and closed *so neither hypothesis follows from separation
of the base*, until 2026-09-14**, when `[T2Space E]` came out of
`Oka/AnalyticSpace/FiniteEtaleBaseChange.lean` and the source's became unused. **Everything this
file states is unchanged**: it supplies both conditions object by object, and the one that is now
surplus is supplied by a hypothesis this file still carries.

**This file takes the remaining route. Ask the cover's structure morphism to be a separated map,
and over a Hausdorff base both hypotheses are consequences rather than assumptions.**
`IsSeparatedMap f` — `Mathlib/Topology/SeparatedMap.lean` — says two *distinct* points with the
same image are separated by opens, and `Oka/Topology/SeparatedMap.lean`'s `IsSeparatedMap.t2Space`
turns that plus a Hausdorff target into a Hausdorff source. Composed with the structure morphism
of a cover, that is the whole of the implication this file spends.

**This is the relative form of a convention this repository declined to impose.**
`Oka/AnalyticSpace/Basic.lean` says that no separation axiom is imposed on
`ComplexAnalytic.AnalyticSpace`, where the classical definition of a complex analytic space
builds one in. Asking the *structure morphism* of an object to be separated is weaker than asking
the total space to be Hausdorff outright — the two agree exactly over a Hausdorff base — and it is
what a cover of a Hausdorff base has to satisfy for the Galois-category axiom to be reachable.

## What this file does not do, and it is a decision rather than an omission

**No definition changes.** `ComplexAnalytic.AnalyticSpace.IsFiniteEtale` gains no field,
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver` is not redefined, and no full subcategory is cut
out. Separatedness enters as a hypothesis on the statements below and nowhere else.

That is deliberate. Whether the condition belongs as a field of
`ComplexAnalytic.AnalyticSpace.IsFiniteEtale`, as a second conjunct in the morphism property
`FiniteEtaleOver` is built from, or as a class of its own is a choice that has to be made against
a measurement of what it costs the existing statements, and this file is the thing that makes the
measurement possible rather than the thing that makes the choice. **What it does supply is the
evidence such a choice would rest on**: the direct-summand statement holds with no hypothesis
beyond the condition, and the constructions a Galois category needs — the terminal object, finite
coproducts, and the clopen restriction the summand decomposition produces — all stay inside it.

**No `PreGaloisCategory` instance and no claim of one.** The field quantifies over
every monomorphism of `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver X`, and
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.inducesIsoOnDirectSummand_of_mono_of_isSeparatedMap`
quantifies over the ones whose source and target are separated over `X`, with `[T2Space X]` besides.

## Where each hypothesis is spent

* **`[T2Space X]`, on the base**, is spent only through
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.t2Space_left_of_isSeparatedMap`, which is
  `IsSeparatedMap.t2Space` at the structure morphism. The statements about the terminal object,
  about coproducts and about clopen restrictions do not use it and say so with `omit`.
* **Separatedness of the *target*'s structure morphism** is what makes a morphism of covers
  finite étale, through
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isFiniteEtale_left_of_isSeparatedMap`; that is
  the cancellation `ComplexAnalytic.AnalyticSpace.isFiniteEtale_of_comp` with its `[T2Space]`
  supplied rather than assumed.
* **Separatedness of the *source*'s** is what makes the fibre product of a monomorphism with
  itself available, which is where `Oka/AnalyticSpace/FiniteEtaleBaseChange.lean` spends its own
  `[T2Space E]`.

## Where these declarations live, and why here

`ComplexAnalytic.AnalyticSpace.isSeparatedMap_sigmaDesc` reads
`AlgebraicGeometry.LocallyRingedSpace.isSeparatedMap_base_sigmaDesc` — the mirror-tree statement
that a descent map out of a coproduct inherits separatedness from its pieces — at an analytic
space, in the way `ComplexAnalytic.AnalyticSpace.isFinite_sigmaDesc` and
`ComplexAnalytic.AnalyticSpace.isLocalIso_sigmaDesc` read that lemma's two siblings.

**The two it is named beside are in `Oka/AnalyticSpace/SigmaFiniteEtale.lean` and it is not, and
that is a choice rather than an accident.** It is not the import that decides it: that file's
`Oka`-side import closure already contains
`Oka/Geometry/RingedSpace/LocallyRingedSpace/HasColimits.lean`, where that lemma sits beside
`AlgebraicGeometry.LocallyRingedSpace.isClosedMap_base_sigmaDesc` and
`AlgebraicGeometry.LocallyRingedSpace.isLocalHomeomorph_base_sigmaDesc`, so hosting this one would
cost it no import — **52** modules at `f59e304` and still 52 — and this file has that module in its
own closure, so the edge would run the way the existing ones already run. **What decides it is the
subject.** `Oka/AnalyticSpace/SigmaFiniteEtale.lean` says that being finite and being a local
isomorphism pass from the members of a disjoint union to the descent map, and those two are the two
fields of `ComplexAnalytic.AnalyticSpace.IsFiniteEtale` in `Oka/AnalyticSpace/LocalIso.lean`.
`IsSeparatedMap` is no field of it, and a morphism can be finite étale without it — which is what
`ComplexAnalytic.AnalyticSpace.not_isSeparatedMap_doubledLineOver` below says — so the parallel with
`ComplexAnalytic.AnalyticSpace.isFinite_sigmaDesc` and
`ComplexAnalytic.AnalyticSpace.isLocalIso_sigmaDesc` is one of proof and not one of subject. **A
reader who thinks the parallel should win can move it**: it is one theorem, it costs that file no
import, and the only proof that consumes it is
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isSeparatedMap_sigma`'s below.

The rest is a **new file rather than an addition to
`Oka/AnalyticSpace/MonoDirectSummand.lean`**, and the reason is the subject rather than the
import: that file is about one theorem — a monomorphism of covers is injective on points — and
its header is an argument about the `[T2Space]` hypotheses of that theorem —
**two of them until 2026-09-14 and one since**, when the source's became unused. Everything below
is a statement about a *condition on objects*, consumes that theorem without touching it, and
carries the design argument this header makes, which is not that file's. The import this file
needs and that file does not is `Oka/Topology/SeparatedMap.lean`: at `07b6670` the only file naming
`import Oka.Topology.SeparatedMap` is the root `Oka.lean`, measured with
`git grep -l 'import Oka.Topology.SeparatedMap' -- '*.lean'`, so this is that module's first
consumer under `Oka/`.

**`Oka/AnalyticSpace/DirectSummand.lean` is the sharper competitor, and for two of the statements
below the answer there is not a preference but a cycle.** That file holds
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isFiniteEtale_left`, which
`…FiniteEtaleOver.isFiniteEtale_left_of_isSeparatedMap` wraps, and
`…FiniteEtaleOver.inducesIsoOnDirectSummand_of_injective`, which
`…FiniteEtaleOver.isSeparatedMap_restrictClopenCompl` cites for the complement it is about; and its
own header argues about the hypotheses of the direct-summand statement, which is the subject this
header argues about too. So the reason given for `Oka/AnalyticSpace/MonoDirectSummand.lean`
transfers — everything below is about a condition on objects and consumes those theorems without
touching them — but it is not the whole answer.

**`…FiniteEtaleOver.injective_base_left_of_mono_of_isSeparatedMap` and
`…FiniteEtaleOver.inducesIsoOnDirectSummand_of_mono_of_isSeparatedMap` cannot be in that file at
all**, and that is unaffected by either of them having lost a hypothesis on
2026-09-14. They consume `…FiniteEtaleOver.injective_base_left_of_mono` and
`…FiniteEtaleOver.inducesIsoOnDirectSummand_of_mono`, which are in
`Oka/AnalyticSpace/MonoDirectSummand.lean`, and that file imports
`Oka/AnalyticSpace/DirectSummand.lean` directly — the line `import Oka.AnalyticSpace.DirectSummand`
is in it. The edge those two would need is the reverse of one that is already there.

For the rest it is a measurement rather than a cycle, and it is given with its instrument because a
dependency relation asserted between two named files is a claim that has to be measured. Over the
tracked `.lean` files under `Oka/` together with `Oka.lean` at `f59e304`, walked with
`scripts/import_cost.py`'s `IMPORT` pattern over its
nesting-aware `strip_comments` and closed transitively, the `Oka`-side import closure of
`Oka/AnalyticSpace/DirectSummand.lean` is **58** modules and this file's is **71**. Neither
`Oka/AnalyticSpace/Double.lean`, which
`ComplexAnalytic.AnalyticSpace.not_isSeparatedMap_doubledLineOver` needs, nor
`Oka/Topology/SeparatedMap.lean`, which `ComplexAnalytic.AnalyticSpace.t2Space_of_isSeparatedMap`
needs, is in that closure, and neither of those two files and `Oka/AnalyticSpace/DirectSummand.lean`
has the other in its closure either way. Adding the two would take that file from 58 to **63**, to
carry statements nothing in it uses. **Note that the `IMPORT` pattern matches `public import` and a
walk of `^import` alone does not**: at `f59e304` the two disagree on this file's closure by fourteen
modules, and the figures here are the former's.

## Main results

- `ComplexAnalytic.AnalyticSpace.t2Space_of_isSeparatedMap`: **a separated morphism into a
  Hausdorff analytic space has Hausdorff source**, which is the transfer of the separation axiom
  in `Oka/Topology/SeparatedMap.lean` read at the base map of a morphism of analytic spaces.
- `ComplexAnalytic.AnalyticSpace.isSeparatedMap_sigmaDesc`: **a descent map out of a disjoint
  union of analytic spaces is separated as soon as each of its restrictions is.**
- `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.t2Space_left_of_isSeparatedMap`: **the total
  space of a cover separated over a Hausdorff base is Hausdorff.**
- `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isFiniteEtale_left_of_isSeparatedMap` and
  `…FiniteEtaleOver.injective_base_left_of_mono_of_isSeparatedMap`: **the two consequences of
  `Oka/AnalyticSpace/MonoDirectSummand.lean` with their separation axioms supplied** — the
  underlying morphism of a morphism of covers is finite étale, and a monomorphism of covers is
  injective on points. **Each asks separatedness of the target and of nothing else; the second
  asked it of the source as well, until 2026-09-14**, when that hypothesis became unused.
- `…FiniteEtaleOver.inducesIsoOnDirectSummand_of_mono_of_isSeparatedMap`: **a monomorphism of
  covers separated over a Hausdorff base exhibits its source as a direct summand of its target**,
  which is the shape of the `monoInducesIsoOnDirectSummand` field with the total-space hypothesis
  replaced by a condition on the target object. **This read *the two total-space hypotheses
  replaced by one condition on each object* until 2026-09-14**, when the source's became unused.
- `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isSeparatedMap_id`,
  `…FiniteEtaleOver.isSeparatedMap_sigma`, `…FiniteEtaleOver.isSeparatedMap_restrictClopen` and
  `…FiniteEtaleOver.isSeparatedMap_restrictClopenCompl`: **the terminal object, a finite
  coproduct, and a clopen restriction of a separated cover are separated** — so the complementary
  clopen part the direct-summand statement produces is separated whenever the cover it is cut out
  of is, and the decomposition stays inside the condition.
- `ComplexAnalytic.AnalyticSpace.not_isSeparatedMap_doubledLineOver`: **the condition is a real
  restriction on objects**, and the object it throws out is the line with two origins over `ℂ¹` —
  the cover `Oka/AnalyticSpace/Double.lean` built to show that those `[T2Space]` hypotheses
  cannot be dropped. **This read *the two `[T2Space]` hypotheses* until 2026-09-14**, when the
  source's became unused; the witness settles the one that is left and settled both.

## What is not here

* **No base change.** That a base change of a separated morphism is separated is Mathlib's
  `IsSeparatedMap.pullback`, at the level of maps of topological spaces, and nothing below reads
  it at an analytic space because nothing below needs to.
* **No converse.** Nothing below says that a cover with Hausdorff total space is separated over
  its base; that direction is Mathlib's `T2Space.isSeparatedMap`, needs no hypothesis on the base
  at all, and would be stated where a caller wants it.
* **Nothing about the fibre functor, the degree, or connectedness**, and no statement about
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isPreconnectedT2`, which is a different
  restriction of the same category made for a different reason.
* **No statement below that the covers this development is ultimately about are separated.**
  Whether the analytification of a finite étale morphism of schemes satisfies the condition is a
  question for the analytification thread, and nothing below touches it.
-/

open CategoryTheory

namespace ComplexAnalytic.AnalyticSpace

universe u

/-! ### Separatedness at a morphism of analytic spaces -/

/-- **A separated morphism into a Hausdorff analytic space has Hausdorff source.**

`IsSeparatedMap.t2Space` at the base map, whose continuity is the one thing a morphism of analytic
spaces supplies here that a bare map of spaces does not. -/
theorem t2Space_of_isSeparatedMap {E Y : AnalyticSpace.{u}} [T2Space (Y : Type u)] {f : E ⟶ Y}
    (h : IsSeparatedMap ⇑(f.toLRSHom.base)) : T2Space (E : Type u) :=
  h.t2Space f.toLRSHom.base.hom.continuous

/-- **A descent map out of a disjoint union is separated as soon as each of its restrictions is.**

`AlgebraicGeometry.LocallyRingedSpace.isSeparatedMap_base_sigmaDesc` read at an analytic space:
the base map of `ComplexAnalytic.AnalyticSpace.sigmaDesc` is the base map of the locally ringed
descent map, which is what `ComplexAnalytic.AnalyticSpace.toLRSHom_sigmaDesc` says. The index type
is not asked to be finite. -/
theorem isSeparatedMap_sigmaDesc {ι : Type u} (F : ι → AnalyticSpace.{u}) {Y : AnalyticSpace.{u}}
    (g : ∀ i, F i ⟶ Y) (h : ∀ i, IsSeparatedMap ⇑((g i).toLRSHom.base)) :
    IsSeparatedMap ⇑((sigmaDesc F g).toLRSHom.base) :=
  AlgebraicGeometry.LocallyRingedSpace.isSeparatedMap_base_sigmaDesc _
    (fun i ↦ (g i).toLRSHom) h

/-! ### A cover separated over its base -/

variable {X : AnalyticSpace.{u}} [T2Space (X : Type u)]

/-- **The total space of a cover separated over a Hausdorff base is Hausdorff.**

`ComplexAnalytic.AnalyticSpace.t2Space_of_isSeparatedMap` at the structure morphism.

**The `haveI` is the comma category's and not this statement's.** In the type of an object's
structure map the base appears through `CategoryTheory.Functor.fromPUnit` applied to the object's
second component; that is the space itself by `rfl` but not reducibly so, and instance search
works up to reducible unfolding, so `[T2Space X]` is not the instance
`ComplexAnalytic.AnalyticSpace.t2Space_of_isSeparatedMap` asks for until it is restated. This is
the idiom `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.card_fiber` uses and there is no
mathematical content in it. -/
theorem FiniteEtaleOver.t2Space_left_of_isSeparatedMap (A : FiniteEtaleOver.{u} X)
    (h : IsSeparatedMap ⇑(A.hom.toLRSHom.base)) : T2Space (A.left : Type u) :=
  haveI : T2Space (((Functor.fromPUnit.{0} X).obj A.right : AnalyticSpace.{u}) : Type u) :=
    inferInstanceAs (T2Space (X : Type u))
  t2Space_of_isSeparatedMap h

/-- **The underlying morphism of a morphism of covers is finite étale**, when the target is
separated over a Hausdorff base.

`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isFiniteEtale_left` with its `[T2Space B.left]`
supplied rather than assumed. Nothing is asked of the source. -/
theorem FiniteEtaleOver.isFiniteEtale_left_of_isSeparatedMap {A B : FiniteEtaleOver.{u} X}
    (hB : IsSeparatedMap ⇑(B.hom.toLRSHom.base)) (i : A ⟶ B) : IsFiniteEtale i.left :=
  haveI := FiniteEtaleOver.t2Space_left_of_isSeparatedMap B hB
  FiniteEtaleOver.isFiniteEtale_left i

/-- **A monomorphism of covers is injective on points**, when the **target** is separated over a
Hausdorff base.

`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.injective_base_left_of_mono` with its one
separation axiom supplied. It is spent making the underlying morphism finite étale, and nothing
is asked of the source.

**This statement took a separatedness hypothesis on the source as well, until 2026-09-14**, when
`[T2Space E]` came out of `Oka/AnalyticSpace/FiniteEtaleBaseChange.lean`: the hypothesis was
there to make the fibre product of the underlying morphism with itself available, that base
change stopped asking for it, and the tree's `unusedArguments` linter is what said so. -/
theorem FiniteEtaleOver.injective_base_left_of_mono_of_isSeparatedMap
    {A B : FiniteEtaleOver.{u} X}
    (hB : IsSeparatedMap ⇑(B.hom.toLRSHom.base)) (i : A ⟶ B) [Mono i] :
    Function.Injective (i.left.toLRSHom.base : A.left → B.left) :=
  haveI := FiniteEtaleOver.t2Space_left_of_isSeparatedMap B hB
  FiniteEtaleOver.injective_base_left_of_mono i

/-- **A monomorphism of covers separated over a Hausdorff base exhibits its source as a direct
summand of its target**: there is a cover `Z` and a morphism `Z ⟶ B` whose binary cofan with `i`
is a colimit.

**This is the shape of the `monoInducesIsoOnDirectSummand` field and it is not that field.** The
field asks the same of every monomorphism and under no hypothesis at all; this asks `[T2Space X]`
of the base and separatedness of the **target**, which is what
`Oka/AnalyticSpace/MonoDirectSummand.lean`'s one remaining `[T2Space]` hypothesis costs when it
is paid for at the object instead of at its total space.

**This paragraph said *separatedness of the two objects* and *two `[T2Space]`
hypotheses*, until 2026-09-14**, when the source's came out along with `[T2Space E]` in
`Oka/AnalyticSpace/FiniteEtaleBaseChange.lean`. -/
theorem FiniteEtaleOver.inducesIsoOnDirectSummand_of_mono_of_isSeparatedMap
    {A B : FiniteEtaleOver.{u} X}
    (hB : IsSeparatedMap ⇑(B.hom.toLRSHom.base)) (i : A ⟶ B) [Mono i] :
    ∃ (Z : FiniteEtaleOver.{u} X) (u : Z ⟶ B),
      Nonempty (Limits.IsColimit (Limits.BinaryCofan.mk i u)) :=
  haveI := FiniteEtaleOver.t2Space_left_of_isSeparatedMap B hB
  FiniteEtaleOver.inducesIsoOnDirectSummand_of_mono i

/-! ### The condition against the constructions the category has -/

omit [T2Space (X : Type u)] in
/-- **The terminal object is separated over the base.** Its structure morphism is the identity,
which is injective, and `Function.Injective.isSeparatedMap` asks nothing else — not continuity,
not a hypothesis on the base. -/
theorem FiniteEtaleOver.isSeparatedMap_id :
    IsSeparatedMap ⇑((FiniteEtaleOver.id.{u} X).hom.toLRSHom.base) :=
  Function.Injective.isSeparatedMap fun _ _ h ↦ h

omit [T2Space (X : Type u)] in
/-- **A finite disjoint union of covers separated over the base is separated over the base.**

`ComplexAnalytic.AnalyticSpace.isSeparatedMap_sigmaDesc`, because the structure morphism of
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.sigma` is the descent map of the structure
morphisms by definition. The finiteness of the index is the one the coproduct of covers carries
and is not used by the separatedness. -/
theorem FiniteEtaleOver.isSeparatedMap_sigma {ι : Type u} [Finite ι] (A : ι → FiniteEtaleOver.{u} X)
    (h : ∀ i, IsSeparatedMap ⇑((A i).hom.toLRSHom.base)) :
    IsSeparatedMap ⇑((FiniteEtaleOver.sigma A).hom.toLRSHom.base) :=
  isSeparatedMap_sigmaDesc _ _ h

omit [T2Space (X : Type u)] in
/-- **A clopen part of a cover separated over the base is separated over the base.**

`IsSeparatedMap.comp_right`, Mathlib's, which asks the map composed on the right to be continuous
and injective: the inclusion of an open subspace is both, its injectivity being
`ComplexAnalytic.AnalyticSpace.base_ofRestrict` read as `Subtype.ext`. Neither the closedness of
the part nor the finite étale structure enters — this is true of a restriction to any open. -/
theorem FiniteEtaleOver.isSeparatedMap_restrictClopen (A : FiniteEtaleOver.{u} X)
    (U : A.left.Opens) (hU : IsClosed (U : Set A.left))
    (h : IsSeparatedMap ⇑(A.hom.toLRSHom.base)) :
    IsSeparatedMap ⇑((A.restrictClopen U hU).hom.toLRSHom.base) :=
  h.comp_right (A.left.ofRestrict U).toLRSHom.base.hom.continuous fun _ _ hxy ↦ Subtype.ext hxy

omit [T2Space (X : Type u)] in
/-- **And so is the complementary part**, which is the statement the direct-summand decomposition
needs: `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.restrictClopenCompl` is
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.restrictClopen` at
`ComplexAnalytic.AnalyticSpace.clopenCompl`, so the complement produced by
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.inducesIsoOnDirectSummand_of_injective` is
separated over the base whenever the cover it is cut out of is. -/
theorem FiniteEtaleOver.isSeparatedMap_restrictClopenCompl (A : FiniteEtaleOver.{u} X)
    (U : A.left.Opens) (hU : IsClosed (U : Set A.left))
    (h : IsSeparatedMap ⇑(A.hom.toLRSHom.base)) :
    IsSeparatedMap ⇑((A.restrictClopenCompl U hU).hom.toLRSHom.base) :=
  A.isSeparatedMap_restrictClopen _ _ h

/-! ### The condition is a restriction -/

/-- **The line with two origins is not separated over `ℂ¹`.**

`ComplexAnalytic.AnalyticSpace.doubledLineOver` is a cover of `ℂ¹` whose total space is not
Hausdorff, and `ℂ¹` is Hausdorff, so
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.t2Space_left_of_isSeparatedMap` would make it
Hausdorff if its structure morphism were separated.

**This is what stops everything above from being about the empty condition.** Every statement in
this file is conditional on separatedness of an object, and a condition no object of this
repository is known to fail is a condition those statements say nothing about. -/
theorem not_isSeparatedMap_doubledLineOver :
    ¬ IsSeparatedMap ⇑((doubledLineOver.{u}).hom.toLRSHom.base) := fun h ↦
  not_t2Space_left_doubledLineOver.{u}
    (FiniteEtaleOver.t2Space_left_of_isSeparatedMap doubledLineOver.{u} h)

end ComplexAnalytic.AnalyticSpace
