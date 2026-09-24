/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.AnalyticSpace.CoveringSpace

/-!
# Morphisms between the covering spaces of a complex analytic space

`Oka/AnalyticSpace/CoveringSpace.lean` builds, from a local homeomorphism `p : E → X` of
topological spaces into a complex analytic space, an analytic structure on `E` and a morphism
`ComplexAnalytic.AnalyticSpace.coveringSpaceHom` from it to `X` whose underlying map is `p`. That
is the action on **objects**. This file is the action on **maps**: a continuous `h : E' ⟶ E` with
`p' = h ≫ p` gives a morphism of analytic spaces `p'⁻¹X ⟶ p⁻¹X` over `X` whose underlying map is
`h`, and two morphisms into `p⁻¹X` which agree on underlying maps and over `X` are equal.

## This is not a functor, and the absence bullet it looks like it closes is about another file

`Oka/AnalyticSpace/CoveringSpace.lean`'s `## What is not here` says of **that file** that what is
missing is *the round trip as an equivalence: no functor either way, no naturality, and nothing
about morphisms of covers*. **Every word of that is still true of that file**: nothing below is
added to it, and the sentence is scoped to the file it stands in.

**It is also not what this file supplies.** `ComplexAnalytic.AnalyticSpace.coveringSpaceMap` is
the value of that action at one map and nothing more: there is no identity law below, no
composition law, no `CategoryTheory.Functor` built, and no category of covers of `X` for such a
functor to go out of. `CategoryTheory.Functor` occurs below only through
`ComplexAnalytic.AnalyticSpace.forgetToLocallyRingedSpace`, in the two declarations where an
equation between morphisms of analytic spaces is obtained from the equation between their
underlying morphisms of locally ringed spaces, and in no other way.

## Nothing is proved here, and the docstrings say what each half is

The locally-ringed-space half is `AlgebraicGeometry.LocallyRingedSpace.inverseImageMapOfEq` with
its base computation and its triangle over `X`, all three already in the tree at
`Oka/Geometry/RingedSpace/LocallyRingedSpace/InverseImage.lean`; the uniqueness half is that
file's `AlgebraicGeometry.LocallyRingedSpace.inverseImage_hom_ext`. What is added is the
`ℂ`-linearity of the morphism, which is `ComplexAnalytic.IsCLinearHom.of_comp` at that triangle —
the same one-application argument `ComplexAnalytic.AnalyticSpace.toCoveringSpace` makes at its
own factorisation, and for the same reason: both structures are the structure of `X` pulled back,
so neither is transported and neither is glued.

**The factorisation is taken as a hypothesis `p' = h ≫ p` rather than read off the shape of the
type**, which is the shape `AlgebraicGeometry.LocallyRingedSpace.inverseImageMapOfEq` has and
whose docstring gives the reason: a caller arrives holding two maps into `X` and a commuting
triangle, not a term whose head is `≫`.

## Main definitions

- `ComplexAnalytic.AnalyticSpace.coveringSpaceMap`: **a continuous map over `X` between the
  sources of two local homeomorphisms into `X` is a morphism of analytic spaces over `X`**, for
  the structures `ComplexAnalytic.AnalyticSpace.coveringSpace` puts on them.

## Main results

- `ComplexAnalytic.AnalyticSpace.base_coveringSpaceMap`: its underlying map is `h`, on the nose.
- `ComplexAnalytic.AnalyticSpace.coveringSpaceMap_comp`: it is a morphism over `X`.
- `ComplexAnalytic.AnalyticSpace.coveringSpace_hom_ext`: **two morphisms into a covering space
  which agree on underlying maps and over `X` are equal.**

## What is not here

* **Nothing about `h`.** It is asked to be continuous and to commute, and nothing below concludes
  that it is a local homeomorphism, injective, surjective, finite, or in any class of morphisms of
  analytic spaces — nor that the morphism it carries is a local isomorphism or an isomorphism.
  Both `p` and `p'` are local homeomorphisms below, which does make `h` one; that implication is
  not stated here and is not used here.
* **No functor and no naturality**, as above.
* **No hypothesis is put on `X` beyond its being an analytic space** — no separation axiom, no
  connectedness — and none is put on `p` or `p'` beyond being local homeomorphisms. In particular
  neither is assumed to be a covering map and neither is assumed to have finite fibres, which is
  what `Oka/AnalyticSpace/CoveringSpace.lean` needs for its finite-étale conclusions and does not
  need for the construction itself.
* **Nothing about the existence of `h`.** Given `p` and `p'`, this file says what a map over `X`
  between them gives; it does not lift, extend or construct one.
-/

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry TopCat Topology

universe u

noncomputable section

namespace ComplexAnalytic

variable (X : AnalyticSpace.{u}) {E E' : TopCat.{u}}
  (p : E ⟶ X.toLocallyRingedSpace.toTopCat) (hp : IsLocalHomeomorph ⇑p)
  (p' : E' ⟶ X.toLocallyRingedSpace.toTopCat) (hp' : IsLocalHomeomorph ⇑p')
  (h : E' ⟶ E) (hcomm : p' = h ≫ p)

/-- **A continuous map over `X` carries a morphism of the two covering spaces it is a map of.**

`AlgebraicGeometry.LocallyRingedSpace.inverseImageMapOfEq` together with a proof of
`ComplexAnalytic.IsCLinearHom`, and that proof is `ComplexAnalytic.IsCLinearHom.of_comp` at the
triangle `AlgebraicGeometry.LocallyRingedSpace.inverseImageMapOfEq_comp`: both algebra structures
are `X`'s pulled back along the two `AlgebraicGeometry.LocallyRingedSpace.inverseImageHom`s, so
the two inputs are `ComplexAnalytic.isCLinearHom_comapAlgMap` twice and nothing else.

Nothing is transported. The underlying locally ringed space of
`ComplexAnalytic.AnalyticSpace.coveringSpace X p hp` is
`X.toLocallyRingedSpace.inverseImage p` by `rfl`
(`ComplexAnalytic.AnalyticSpace.coveringSpace_toLocallyRingedSpace`), so the field is literally a
morphism between the two inverse images. -/
def AnalyticSpace.coveringSpaceMap :
    AnalyticSpace.coveringSpace X p' hp' ⟶ AnalyticSpace.coveringSpace X p hp :=
  ⟨LocallyRingedSpace.inverseImageMapOfEq p h p' hcomm,
    IsCLinearHom.of_comp (LocallyRingedSpace.inverseImageMapOfEq_comp p h p' hcomm)
      (isCLinearHom_comapAlgMap _ _) (isCLinearHom_comapAlgMap _ _)⟩

/-- **Its underlying morphism of locally ringed spaces** is
`AlgebraicGeometry.LocallyRingedSpace.inverseImageMapOfEq`, on the nose.

**Not `@[simp]`, and the reason was reported rather than chosen**: with it,
`simpNF` rejects the base computation below, which this together with
`AlgebraicGeometry.LocallyRingedSpace.inverseImageMapOfEq_base` already proves. The base
computation is the one a caller reaches for, so it is the one that keeps the attribute. -/
theorem AnalyticSpace.toLRSHom_coveringSpaceMap :
    (AnalyticSpace.coveringSpaceMap X p hp p' hp' h hcomm).toLRSHom =
      LocallyRingedSpace.inverseImageMapOfEq p h p' hcomm :=
  rfl

/-- **And its underlying map is `h`**, which is what makes the two statements below statements
about `h` and not about a homeomorphic copy of it. -/
@[simp]
theorem AnalyticSpace.base_coveringSpaceMap :
    (AnalyticSpace.coveringSpaceMap X p hp p' hp' h hcomm).toLRSHom.base = h :=
  LocallyRingedSpace.inverseImageMapOfEq_base p h p' hcomm

/-- **It is a morphism over `X`.**

`AlgebraicGeometry.LocallyRingedSpace.inverseImageMapOfEq_comp` pushed across the faithful
`ComplexAnalytic.AnalyticSpace.forgetToLocallyRingedSpace`: an equation between morphisms of
analytic spaces is an equation between their underlying morphisms, the `ℂ`-linearity fields being
proofs. -/
theorem AnalyticSpace.coveringSpaceMap_comp :
    AnalyticSpace.coveringSpaceMap X p hp p' hp' h hcomm ≫
        AnalyticSpace.coveringSpaceHom X p hp = AnalyticSpace.coveringSpaceHom X p' hp' :=
  AnalyticSpace.forgetToLocallyRingedSpace.map_injective
    (LocallyRingedSpace.inverseImageMapOfEq_comp p h p' hcomm)

/-- **Two morphisms into a covering space which agree on underlying maps and over `X` are equal.**

`AlgebraicGeometry.LocallyRingedSpace.inverseImage_hom_ext` read through the faithful
`ComplexAnalytic.AnalyticSpace.forgetToLocallyRingedSpace` in both directions: the hypothesis
`huv` is carried down to the locally ringed spaces by applying the functor, and the conclusion is
carried back up by its faithfulness.

**The base hypothesis is not implied by the other one.** `p` is asked to be a local
homeomorphism and not to be injective, so two morphisms into `p⁻¹X` can agree over `X` and differ
on points; nothing below states a witness. The sheaf-level content is in the statement this is
read from, and none of it is re-argued here. -/
theorem AnalyticSpace.coveringSpace_hom_ext {Z : AnalyticSpace.{u}}
    {u v : Z ⟶ AnalyticSpace.coveringSpace X p hp}
    (hbase : u.toLRSHom.base = v.toLRSHom.base)
    (huv : u ≫ AnalyticSpace.coveringSpaceHom X p hp =
      v ≫ AnalyticSpace.coveringSpaceHom X p hp) : u = v :=
  AnalyticSpace.forgetToLocallyRingedSpace.map_injective
    (LocallyRingedSpace.inverseImage_hom_ext _ _ hbase
      (congrArg AnalyticSpace.forgetToLocallyRingedSpace.map huv))

end ComplexAnalytic
