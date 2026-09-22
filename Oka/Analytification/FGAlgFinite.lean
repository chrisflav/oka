/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Analytification.Functor
import Oka.Analytification.SpecFiniteAnalytification

/-!
# The finite half, read at the functor on finitely generated `ℂ`-algebras

`Oka/Analytification/ModuleFiniteAnalytification.lean` and
`Oka/Analytification/SpecFiniteAnalytification.lean` state that a module-finite map of presented
algebras analytifies to a finite morphism, at a `ComplexAnalytic.PresHom` the caller holds.
**This file states the same thing with the morphism produced by the functor instead of by the
presentation-level construction**, which is the form a consumer working in
`ComplexAnalytic.analytificationFGAlg` can use without ever naming a tuple of polynomials.

## The two readings, and this file is the first of them

There are two statements a reader can mean by *read it at the functor*, and they are not the same
job.

1. **The presentation still indexes the objects.** The morphism is
   `(toFGAlg ⋙ analytificationFGAlg).map ψ` for `ψ` a morphism of presentations, and the
   hypothesis is the one the theorem above already takes. **That is this file**, and its whole
   content is that the functor's morphism is the presentation-level one conjugated by the
   comparison isomorphism — `ComplexAnalytic.toFGAlg_comp_analytificationFGAlg_map` — together
   with the fact that a composite of finite morphisms is finite and an isomorphism is finite.
2. **The presentation is gone altogether.** The morphism is `analytificationFGAlg.map f` for an
   arbitrary `f` between finitely generated `ℂ`-algebras. `ComplexAnalytic.analytificationFGAlg`
   *is* `toFGAlg.asEquivalence.inverse ⋙ analytificationFunctor` by definition, so there is no
   work in the conclusion at all and all of it is in the hypothesis: carrying `RingHom.Finite`
   of `f` across the equivalence's counit, which is built from
   `ComplexAnalytic.exists_presentation` and so from `Classical.choice`.
   `RingHom.finite_respectsIso` is the Mathlib side of that. **Nothing here is evidence about its
   size and it is not started.**

**The ingredient the first reading needs is the naturality of the comparison and not the
comparison itself.** `ComplexAnalytic.analytificationFGAlgObjIso` is an isomorphism of objects; a
statement about a *morphism* needs the square, which is
`ComplexAnalytic.analytificationFGAlgObjIso_naturality`. That distinction is why this file is
short and why a clause pointing a reader at the object isomorphism alone was pointing at
something that cannot prove it.

## What the import costs, measured

This file is the first module to import both `Oka/Analytification/Functor.lean` and
`Oka/Analytification/SpecFiniteAnalytification.lean`: at the commit this file is added to, neither
is in the other's import closure. **Against the closure of
`Oka/Analytification/SpecFiniteAnalytification.lean` the `Functor` edge adds exactly one `Oka`
module — that file itself — and zero Mathlib modules**, taking the closure from 85 `Oka` modules
to 86 with the Mathlib closure flat at 3320. The reason is that
`Mathlib/Algebra/Category/CommAlgCat/Basic.lean`, the one Mathlib import
`Oka/Analytification/Functor.lean` adds by hand, is already reachable from the finiteness side.

## Main results

- `ComplexAnalytic.isFinite_toFGAlg_comp_analytificationFGAlg_map_of_finite`: **a module-finite
  map of presented algebras is sent by the functor on finitely generated `ℂ`-algebras to a finite
  morphism of analytic spaces.**
- `ComplexAnalytic.isFinite_toFGAlg_comp_analytificationFGAlg_map_of_isFinite_specMap`: **and the
  same with the hypothesis read as finiteness of the morphism of spectra**, which is the
  vocabulary the prose sites about finite morphisms of schemes use.

## What is not here

* **The second reading above**, at an arbitrary morphism of finitely generated `ℂ`-algebras with
  no presentation in the statement. It is a transport across the equivalence's counit and is
  untouched.
* **Nothing étale, and nothing non-affine.** `Oka/Analytification/SpecFiniteAnalytification.lean`
  enumerates the eight prose sites that record the analytification of a finite *étale* morphism
  as absent; this file is the finite half again, in a second vocabulary, and narrows none of
  them. The Zariski-local gluing that would take an affine statement to a general morphism of
  schemes is not started either.
* **No naturality and no functoriality statement of its own.** What is proved is a property of
  each morphism in the image, not a statement about the functor.
-/

open CategoryTheory AlgebraicGeometry

universe u

namespace ComplexAnalytic

/-- **A module-finite map of presented algebras is sent by the functor on finitely generated
`ℂ`-algebras to a finite morphism.**

`ComplexAnalytic.isFinite_analytificationMap_of_finite` is the same statement for the morphism
built from the presentation in hand, and this is that statement transported along
`ComplexAnalytic.toFGAlg_comp_analytificationFGAlg_map`: the functor's morphism is the
presentation-level one with an isomorphism on each side, an isomorphism is finite, and a composite
of finite morphisms is finite.

**The two `@`-applications at the end are not a stylistic choice.** `rw` leaves the goal's object
indices as the ones the statement was written with, so after rewriting, the composite's source is
still spelled `(toFGAlg ⋙ analytificationFGAlg).obj P` while each hypothesis above is at
`analytificationFGAlg.obj (toFGAlg.obj P)`. Those are definitionally equal and
`instance` search, which runs at `instances` transparency, unfolds neither to the other — so
`infer_instance` fails on a goal every ingredient of which is in scope, naming an instance that
has just been proved. `exact` elaborates at default transparency and closes it, and passing the
two instance arguments by hand is what keeps it out of instance search. -/
theorem isFinite_toFGAlg_comp_analytificationFGAlg_map_of_finite {P Q : Presentation.{u}}
    (ψ : P ⟶ Q) (hψ : ψ.toRingHom.Finite) :
    AnalyticSpace.IsFinite ((toFGAlg.{u} ⋙ analytificationFGAlg.{u}).map ψ) := by
  have hmap : AnalyticSpace.IsFinite (analytificationMap.{u} ψ) :=
    isFinite_analytificationMap_of_finite.{u} ψ hψ
  have hP : AnalyticSpace.IsFinite (analytificationFGAlgObjIso.{u} P).hom :=
    AnalyticSpace.isFinite_of_isIso _
  have hQ : AnalyticSpace.IsFinite (analytificationFGAlgObjIso.{u} Q).inv :=
    AnalyticSpace.isFinite_of_isIso _
  rw [toFGAlg_comp_analytificationFGAlg_map.{u} ψ]
  exact @AnalyticSpace.isFinite_comp _ _ _ _ _
    (@AnalyticSpace.isFinite_comp _ _ _ _ _ hP hmap) hQ

/-- **And the same with the hypothesis read as finiteness of the morphism of spectra.**

This stands to the theorem above exactly as
`ComplexAnalytic.isFinite_analytificationMap_of_isFinite_specMap` stands to
`ComplexAnalytic.isFinite_analytificationMap_of_finite`: it is that theorem composed with
`AlgebraicGeometry.IsFinite.SpecMap_iff`, the affine criterion for `AlgebraicGeometry.IsFinite`,
and there is no analysis in it. `ComplexAnalytic.PresHom.toRingHom` runs `B ⟶ A` where the
analytified morphism runs `A^an ⟶ B^an` and `AlgebraicGeometry.Spec.map` reverses it again, so the
morphism of spectra runs in the same direction as the one produced by the functor. -/
theorem isFinite_toFGAlg_comp_analytificationFGAlg_map_of_isFinite_specMap
    {P Q : Presentation.{u}} (ψ : P ⟶ Q)
    (h : IsFinite (Spec.map (CommRingCat.ofHom ψ.toRingHom))) :
    AnalyticSpace.IsFinite ((toFGAlg.{u} ⋙ analytificationFGAlg.{u}).map ψ) :=
  isFinite_toFGAlg_comp_analytificationFGAlg_map_of_finite.{u} ψ
    ((IsFinite.SpecMap_iff _).mp h)

end ComplexAnalytic
