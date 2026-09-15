/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.AnalyticSpace.SeparatedFiniteEtale

/-!
# The direct summand of a monomorphism, landed inside the separated covers

`Oka/AnalyticSpace/SeparatedFiniteEtale.lean` proves that a monomorphism of covers separated over a
Hausdorff base exhibits its source as a direct summand of its target, and **produces the summand
and the colimit one category out**, in `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver X`. Its
`## What is not here` says in terms why, and names the repair:

> The obstruction is that the summand is existentially quantified where it is produced […] but the
> existential hides which object was taken, so this file cannot reach that lemma from the
> statement. **Landing the summand in this category needs the ambient statement restated with its
> witness named, and that is a push on `Oka/AnalyticSpace/DirectSummand.lean` and not on this one.**

**This file is the second half of that repair and it adds no mathematics.**
`Oka/AnalyticSpace/DirectSummand.lean` now states the decomposition with the summand named
(`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.directSummandCompl`); what is done here is to give
that object the second component an object of this category needs, and to reflect the colimit back
along an inclusion that is fully faithful.

## What the statement is, and what it is not

`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.inducesIsoOnDirectSummand_of_mono'` is the
`monoInducesIsoOnDirectSummand` field of `Mathlib/CategoryTheory/Galois/Basic.lean`'s
`PreGaloisCategory`, at this category, **with `[T2Space X]` added on the base and nothing else
changed**. The field is written for every monomorphism under no hypothesis; the class asks five
things of a category and this is one of them, so what is here is one field and not the class.
**That namespace is not in this repository's import closure** — `#check` on it reports an unknown
identifier from a file importing `Oka/AnalyticSpace/SeparatedFiniteEtale.lean` — which is the
spelling `Oka/AnalyticSpace/SeparatedFiniteEtale.lean` and `Oka/AnalyticSpace/DirectSummand.lean`
already use for it, and the reason no instance is declared anywhere below.

## The two steps, and neither is deep

* **The object.** `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.directSummandCompl` at the image
  of `i`, given its second component by
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isSeparatedMap_restrictClopenCompl`
  (`Oka/AnalyticSpace/SeparatedOver.lean`), which says a complementary clopen part is separated
  over the base whenever the cover it is cut out of is. **That lemma was already in the tree and
  already about exactly this object**; what was missing was a name to apply it to, which is the
  whole of the obstruction the file above recorded.
* **The colimit.** `CategoryTheory.Limits.isColimitOfReflectsOfMapIsColimit` along
  `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.toFiniteEtaleOver`, whose
  `CategoryTheory.Limits.ReflectsColimit` is
  `CategoryTheory.Limits.fullyFaithful_reflectsColimits` at a functor
  `Oka/AnalyticSpace/SeparatedFiniteEtale.lean` already argues is full and faithful. **The
  mathematical content is Mathlib's — a fully faithful functor reflects colimits — and nothing
  here reproves it**: no `CategoryTheory.Limits.BinaryCofan.IsColimit.mk` appears below and no
  universal property is checked by hand.

**Both seams close by `rfl` and that is a measurement rather than a hope.** The inclusion carries
the object and the morphism this file builds to the ones
`Oka/AnalyticSpace/DirectSummand.lean` builds **on the nose**, which is why the reflection lemma
applies with no `CategoryTheory.eqToHom` and no `CategoryTheory.Limits.Cocones.ext`. **Both were
written out as `example … := rfl` in a scratch file importing this module and elaborated, before
this paragraph was written** — at the head that adds this module, since neither statement can be
made at any earlier commit. That is a consequence of
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.directSummandCompl` being **written out
rather than transported**, in the idiom
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.selfProd` uses and for the reason its
docstring gives.

## Main definitions

- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.directSummandCompl`: **the summand
  complementary to a morphism of separated covers, as an object of this category**, and
  `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.directSummandComplι`: **its inclusion
  into the target**. Neither asks for `CategoryTheory.Mono`.

## Main results

- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.isColimitBinaryCofanDirectSummandCompl`:
  **the target is the coproduct of the source and that summand, in this category**, at a
  monomorphism of this category.
- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.inducesIsoOnDirectSummand_of_mono'`:
  **its existential closure**, which is the shape the Galois-category field is written in.

## What is not here

* **No `PreGaloisCategory` instance, and what is here is one of that class's five obligations and
  not the class.** The other four are a terminal object, which
  `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.hasTerminal` gives and with no hypothesis
  on the base; pullbacks, which taxis #1918 is the filing for and which is not on `master` at the
  commit that writes this; finite coproducts, which the bullet opening *No coproducts and no cofan*
  is about; and quotients by finite group actions, about which this repository states nothing.

  **Measured rather than read**: at `0eed5cd`, the base of this push, the string
  `SeparatedFiniteEtaleOver` occurs in the comment-stripped code of exactly two modules,
  `Oka/AnalyticSpace/SeparatedFiniteEtale.lean` and `OkaTest/Axioms/Morphisms.lean`,
  and the only limits instance either declares for the category is that terminal object; and
  `PreGaloisCategory` and `SingleObj` occur in the comment-stripped code of no module of this
  repository at all. **`HasFiniteCoproducts` does occur, in two** —
  `Oka/AnalyticSpace/FiniteEtaleOver.lean` and `Oka/AnalyticSpace/Sigma.lean` — but of the covers
  and not of this category, which is the distinction the bullet opening *No coproducts and no
  cofan* draws.
* **`[T2Space X]` is not removed and nothing below tries to.** It is spent through
  `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.t2Space_left`, which is what supplies the
  `[T2Space B.left]` that `Oka/AnalyticSpace/DirectSummand.lean` asks of the target cover, and that
  hypothesis is in turn the cancellation's — `Oka/AnalyticSpace/DirectSummand.lean`'s own
  `## What is not here` argues at length that it cannot be dropped and compiles the witness.
* **Nothing about base change in `ComplexAnalytic.AnalyticSpace` is narrowed.**
  `CategoryTheory.MorphismProperty.IsStableUnderBaseChange` for
  `ComplexAnalytic.AnalyticSpace.isFiniteEtale` quantifies over cospans whose finite étale leg may
  have a non-Hausdorff source, and `ComplexAnalytic.AnalyticSpace.doubledLineOver` is the standing
  witness against it. That class is
  `ComplexAnalytic.AnalyticSpace.isStableUnderBaseChange_isFiniteEtale`, in
  `Oka/AnalyticSpace/FiniteEtaleStableUnderBaseChange.lean`, which is untouched by this file and is
  not made weaker by it; so are the bullets about it in
  `Oka/AnalyticSpace/FiniteEtaleBaseChange.lean` and `Oka/AnalyticSpace/FiniteEtaleOver.lean`.

  **The second sentence of this bullet ended *The bullets recording that in
  `Oka/AnalyticSpace/FiniteEtaleBaseChange.lean` and `Oka/AnalyticSpace/FiniteEtaleOver.lean` are
  untouched by this file and are not made weaker by it*, until 2026-09-15**, when the class was
  stated and *the bullets recording that* stopped naming what records it. What this bullet claims
  of this file is unchanged.
* **No coproducts and no cofan.**
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isSeparatedMap_sigma` makes a finite disjoint
  union of separated covers separated, so the objects of that cofan are available; the cofan
  itself, its colimit and the `CategoryTheory.Limits.HasFiniteCoproducts` instance they would give
  are not here and are a rung of their own. **This is
  `Oka/AnalyticSpace/SeparatedFiniteEtale.lean`'s bullet of the same subject, unchanged** — this
  file is about the summand of a monomorphism and produces no coproduct of two objects chosen
  freely.

  **That rung landed on 2026-09-13**, and the sentences above are kept rather than rewritten
  because two clauses of this docstring cite this bullet by its opening words.
  `Oka/AnalyticSpace/SeparatedFiniteEtaleCoproducts.lean` — **a sibling of this module, which
  neither imports it nor is imported by it, both importing
  `Oka/AnalyticSpace/SeparatedFiniteEtale.lean`** — gives the cofan
  `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.cofanSigma`, its colimit
  `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.isColimitCofanSigma` and the instance
  `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.hasFiniteCoproducts`, out of that same
  lemma and **with no hypothesis on the base**. **Nothing in this file moved**: it gains no import
  and no declaration, and what is still true of it is the last sentence — it is about the summand
  of a monomorphism and produces no coproduct of two objects chosen freely.

  **The *does occur, in two* figure in this docstring's first bullet is pinned to `0eed5cd` and is
  exact there.** At the commit that adds the coproducts the string `HasFiniteCoproducts` occurs in
  the comment-stripped code of **three** modules, and the third is of this category — so the
  distinction that figure draws is still the right one to draw and the count beside it is a record
  of a commit and not a claim about the tree.
* **The isomorphism onto the clopen part is still not exposed**, for the reason
  `Oka/AnalyticSpace/DirectSummand.lean`'s `## What is not here` gives; nothing below unfolds that
  proof.
-/

open CategoryTheory

universe u

namespace ComplexAnalytic.AnalyticSpace

variable {X : AnalyticSpace.{u}} [T2Space (X : Type u)]
variable {A B : SeparatedFiniteEtaleOver.{u} X}

/-! ### The summand, as an object of the separated covers -/

/-- **The summand complementary to a morphism of separated covers, as an object of this
category.**

`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.directSummandCompl` at the image of `i`, **written
out rather than transported**, so that the inclusion into the covers carries it to that object on
the nose and the colimit below needs no `CategoryTheory.eqToHom`. This is the idiom
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.selfProd` uses and its docstring is where
the reason is argued.

**The second component is the whole of what is new**, and it is
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isSeparatedMap_restrictClopenCompl` at `B`'s own
separatedness: a complementary clopen part is separated over the base whenever the cover it is cut
out of is. **That lemma asks nothing of the base** — its statement carries an `omit` of the
Hausdorff hypothesis — so the `[T2Space X]` of this section is spent only on the `[T2Space B.left]`
the ambient object needs, through
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.t2Space_left`.

**The `haveI` is the comma category's and not this definition's**: the inclusion's action on an
object leaves `left` alone by `rfl` but not reducibly so, which is the seam
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.t2Space_left_of_isSeparatedMap`'s docstring
describes and which
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.inducesIsoOnDirectSummand_of_mono` already
carries one of.

**No injectivity and no `CategoryTheory.Mono` is asked**, exactly as in the ambient definition: the
object exists at every morphism of this category and the hypothesis is what makes the cofan below
a colimit. -/
noncomputable def SeparatedFiniteEtaleOver.directSummandCompl (i : A ⟶ B) :
    SeparatedFiniteEtaleOver.{u} X :=
  haveI : T2Space
      ((((SeparatedFiniteEtaleOver.toFiniteEtaleOver X).obj B).left : AnalyticSpace.{u}) :
        Type u) :=
    inferInstanceAs (T2Space (B.left : Type u))
  MorphismProperty.Over.mk _
    (FiniteEtaleOver.directSummandCompl
      ((SeparatedFiniteEtaleOver.toFiniteEtaleOver X).map i)).hom
    ⟨(FiniteEtaleOver.directSummandCompl
        ((SeparatedFiniteEtaleOver.toFiniteEtaleOver X).map i)).prop,
      FiniteEtaleOver.isSeparatedMap_restrictClopenCompl
        ((SeparatedFiniteEtaleOver.toFiniteEtaleOver X).obj B)
        (FiniteEtaleOver.rangeOpens ((SeparatedFiniteEtaleOver.toFiniteEtaleOver X).map i))
        (FiniteEtaleOver.isClosed_rangeOpens
          ((SeparatedFiniteEtaleOver.toFiniteEtaleOver X).map i))
        B.isSeparatedMap_hom⟩

/-- **Its inclusion into the target, as a morphism of this category.**

The underlying morphism is
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.directSummandComplι`'s and the triangle over `X` is
that morphism's own, read through `CategoryTheory.MorphismProperty.Over.w`. **Nothing is proved
here**: a morphism of this category is a morphism of covers between objects of it, which is what
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.toFiniteEtaleOver` being full says, and
this is that statement used in the direction that builds rather than the direction that reads. -/
noncomputable def SeparatedFiniteEtaleOver.directSummandComplι (i : A ⟶ B) :
    SeparatedFiniteEtaleOver.directSummandCompl i ⟶ B :=
  haveI : T2Space
      ((((SeparatedFiniteEtaleOver.toFiniteEtaleOver X).obj B).left : AnalyticSpace.{u}) :
        Type u) :=
    inferInstanceAs (T2Space (B.left : Type u))
  MorphismProperty.Over.homMk
    (FiniteEtaleOver.directSummandComplι
      ((SeparatedFiniteEtaleOver.toFiniteEtaleOver X).map i)).left
    (MorphismProperty.Over.w
      (FiniteEtaleOver.directSummandComplι
        ((SeparatedFiniteEtaleOver.toFiniteEtaleOver X).map i)))

/-! ### The decomposition, in the separated covers -/

/-- **The target is the coproduct of the source and that summand, in this category.**

`CategoryTheory.Limits.isColimitOfReflectsOfMapIsColimit` along
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.toFiniteEtaleOver`, at
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isColimitBinaryCofanDirectSummandCompl` and with
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.injective_base_left_of_mono` discharging
the injectivity. **The `CategoryTheory.Limits.ReflectsColimit` instance is
`CategoryTheory.Limits.fullyFaithful_reflectsColimits`** and it is the only mathematical content of
this declaration: a fully faithful functor reflects colimits, because a competing cocone in the
source is carried to one in the target and the descent map comes back by fullness and is unique by
faithfulness.

**The hypothesis is `CategoryTheory.Mono` in this category and not in the covers**, which is the
whole reason `Oka/AnalyticSpace/SeparatedFiniteEtale.lean` introduced the category: a monomorphism
here is tested against fewer objects than one there, and
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.injective_base_left_of_mono` is where that
weaker hypothesis is shown to be enough.

**Neither `CategoryTheory.Functor.mapCocone` seam needed repair.** The lemma asks for the ambient
colimit at `G.map i` and `G.map u`, and what is available is the one at `G.map i` and the ambient
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.directSummandComplι` of `G.map i`; both the object
and the morphism agree with what the inclusion produces by `rfl`, which the module docstring
records as an elaborated statement and not as an expectation.

It is a `def` and not a `theorem` because `CategoryTheory.Limits.IsColimit` is data. -/
noncomputable def SeparatedFiniteEtaleOver.isColimitBinaryCofanDirectSummandCompl
    (i : A ⟶ B) [Mono i] :
    Limits.IsColimit
      (Limits.BinaryCofan.mk i (SeparatedFiniteEtaleOver.directSummandComplι i)) :=
  haveI : T2Space
      ((((SeparatedFiniteEtaleOver.toFiniteEtaleOver X).obj B).left : AnalyticSpace.{u}) :
        Type u) :=
    inferInstanceAs (T2Space (B.left : Type u))
  Limits.isColimitOfReflectsOfMapIsColimit (SeparatedFiniteEtaleOver.toFiniteEtaleOver X)
    i (SeparatedFiniteEtaleOver.directSummandComplι i)
    (FiniteEtaleOver.isColimitBinaryCofanDirectSummandCompl
      ((SeparatedFiniteEtaleOver.toFiniteEtaleOver X).map i)
      (SeparatedFiniteEtaleOver.injective_base_left_of_mono i))

/-- **A monomorphism of this category exhibits its source as a direct summand of its target, with
the summand and the colimit both in this category.**

**This is the Galois-category field's shape and, over a Hausdorff base, its content.**
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.inducesIsoOnDirectSummand_of_mono`
(`Oka/AnalyticSpace/SeparatedFiniteEtale.lean`) is the same statement with `Z` and the colimit in
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver X`; **it is not superseded and is not restated**,
since a caller working in the covers wants it in the covers. The prime is against that name and
marks which category the witness lands in.

**What separates this from the field is `[T2Space X]` and nothing else.** The module docstring says
which of the five obligations of `Mathlib/CategoryTheory/Galois/Basic.lean`'s class this is and
which four it is not, and no instance of that class is declared anywhere in this repository. -/
theorem SeparatedFiniteEtaleOver.inducesIsoOnDirectSummand_of_mono' (i : A ⟶ B) [Mono i] :
    ∃ (Z : SeparatedFiniteEtaleOver.{u} X) (u : Z ⟶ B),
      Nonempty (Limits.IsColimit (Limits.BinaryCofan.mk i u)) :=
  ⟨SeparatedFiniteEtaleOver.directSummandCompl i, SeparatedFiniteEtaleOver.directSummandComplι i,
    ⟨SeparatedFiniteEtaleOver.isColimitBinaryCofanDirectSummandCompl i⟩⟩

end ComplexAnalytic.AnalyticSpace
