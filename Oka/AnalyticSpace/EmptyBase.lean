/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.AnalyticSpace.GaloisCategory

/-!
# Over an empty base the Galois-category class is false

`Oka/AnalyticSpace/GaloisCategory.lean` states `CategoryTheory.GaloisCategory` at the covers
separated over a base that is Hausdorff, preconnected **and nonempty**, and the paragraph of its
module docstring that justifies the third hypothesis argues in prose that it is a hypothesis of the
mathematics and not of the search: `IsPreconnected` holds of the empty set, so a preconnected base
may be empty, and over an empty base the class looks false rather than merely unreachable. **That
paragraph marked itself as an argument and not a run.** This file is the run, and the paragraph now
says so.

## The route, which is not the one that paragraph sketches

The sketch routes through the initial object: *every cover of an empty base is empty, so the initial
object of the category — the empty coproduct — is isomorphic to its terminal object*. **No statement
or proof below writes a coproduct or `CategoryTheory.Limits.HasInitial`.** That is a grep over this
file's code and not a claim about what its proof terms unfold to: Mathlib's
`CategoryTheory.PreGaloisCategory.initial_iff_fiber_empty`, which the two refutations reach by name,
is itself proved through the colimit over the empty diagram. What is proved here is that the
terminal object this repository already has — `…SeparatedFiniteEtaleOver.id`, terminal with no
hypothesis at all by `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.isTerminalId` — **is
itself initial** over an empty base. That is the stronger statement: it needs neither the empty
coproduct nor an isomorphism between two objects, and the contradiction it feeds is two lines rather
than a transport. A fibre functor sends that one object to a `FintypeCat` which is empty because the
object is initial and has a point because the object is terminal.

**Which fields of `CategoryTheory.PreGaloisCategory.FiberFunctor` the route spends is read out of
Mathlib's source and is not a run of this file.**
`CategoryTheory.PreGaloisCategory.initial_iff_fiber_empty` is proved through
`CategoryTheory.Limits.IsInitial.isInitialIffObj`, whose two instance arguments are
`CategoryTheory.Limits.PreservesColimit` and `CategoryTheory.Limits.ReflectsColimit` at the empty
diagram — the class's `preservesFiniteCoproducts` and, through
`CategoryTheory.Limits.reflectsColimitsOfShape_of_reflectsIsomorphisms`, its `reflectsIsos`; and
`CategoryTheory.Limits.IsTerminal.isTerminalObj` asks for `CategoryTheory.Limits.PreservesLimit` at
the empty diagram, which is `preservesTerminalObjects`. **The remaining three fields are not named
on the route**, and that is a reading of those two files and not a measurement of the proof terms
below.

## Main results

- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.isIso_hom_of_isEmpty`: **the structure
  morphism of a cover of an empty base is an isomorphism**, and
  `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.isoIdOfIsEmpty`: **so every object is
  isomorphic to the terminal one**, stated as a definition because it is one.
- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.isInitialIdOfIsEmpty`: **that terminal
  object is initial**, over an empty base.
- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.not_isFiberFunctor_of_isEmpty`: **so no
  `FintypeCat`-valued functor out of that category is a fibre functor**, in any universe.
- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.not_galoisCategory_of_isEmpty`: **and the
  category is not a `CategoryTheory.GaloisCategory`.** The class is the two
  `CategoryTheory.PreGaloisCategory` ingredients together with the **existence** of a fibre
  functor, and it is that existential `…SeparatedFiniteEtaleOver.not_isFiberFunctor_of_isEmpty`
  refutes.

**The general ingredient is in `Oka/AnalyticSpace/LocalIso.lean` and not here.**
`ComplexAnalytic.AnalyticSpace.isIso_of_isEmpty` — a morphism of analytic spaces whose target is
empty is an isomorphism — has no Galois content and is stated beside
`ComplexAnalytic.AnalyticSpace.isIso_of_isLocalIso_of_bijective`, which is its only ingredient.

## What is not here

* **Nothing about `[PreconnectedSpace X]`.** That hypothesis of
  `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.galoisCategory` is spent by the fibre
  functor's `reflectsIsos` field, this file touches neither it nor the fibre functor, and no
  statement below says an empty base is or is not preconnected.
* **No change to any of the three instances that module declares, and none to their hypotheses.**
  `[Nonempty X]` stays exactly where it is; what this file settles is *why* it is there.
* **Nothing about `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver`**, the covers that are not
  separated. `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.isTerminalId` is a statement
  of the separated category and the `CategoryTheory.PreGaloisCategory` instance is declared there;
  whether the same argument runs at the ambient covers is **not measured here** and no sentence of
  this file bears on it.
* **No claim that the category over an empty base is trivial, equivalent to a point, or a
  zero-object category.** What is compiled is that one named object is initial and terminal and
  that every object is isomorphic to it; the hom sets are not described and nothing below is an
  equivalence of categories.
* **No object.** Every statement here is under `[IsEmpty (X : Type u)]` at a variable base;
  `OkaTest/GaloisCategory.lean` is where the refutation is read at a named analytic space, which is
  what keeps the hypothesis from being one nothing satisfies.
-/

open CategoryTheory CategoryTheory.Limits

universe w u

namespace ComplexAnalytic.AnalyticSpace

variable {X : AnalyticSpace.{u}} [IsEmpty (X : Type u)]

/-- **The structure morphism of a cover of an empty base is an isomorphism.**

`ComplexAnalytic.AnalyticSpace.isIso_of_isEmpty` at `A.hom`, and the emptiness has to be passed by
name: the target of `A.hom` elaborates as `(CategoryTheory.Functor.fromPUnit X).obj A.right` rather
than as `X`, and instance search does not find `IsEmpty` of it. That is the reason that theorem
takes its hypothesis explicitly and the paragraph there gives it in full. -/
theorem SeparatedFiniteEtaleOver.isIso_hom_of_isEmpty (A : SeparatedFiniteEtaleOver.{u} X) :
    IsIso A.hom :=
  isIso_of_isEmpty A.hom ‹IsEmpty (X : Type u)›

/-- **So every object is isomorphic to the terminal one**, over an empty base.

`CategoryTheory.MorphismProperty.Over.isoMk` at `…SeparatedFiniteEtaleOver.isIso_hom_of_isEmpty`,
whose compatibility is
`A.hom ≫ 𝟙 X = A.hom`. **The instance is supplied by name rather than found**, which is what the
`@` is doing: instance search declines in every shape this `CategoryTheory.IsIso` fact can be
offered in, and the shapes are named below because they do not all print the same thing.

**As a global `instance` of `IsIso A.hom`, or as a quantified binder `[∀ B, IsIso B.hom]`, the
unifier is asked for `IsIso A.hom ≟ IsIso (CategoryTheory.MorphismProperty.Comma.toComma ?m).hom`
and declines.** The metavariable is the universally quantified object of those two statements,
which is exactly what the `@` supplies by hand.

**With the specialised statement in context the two sides pretty-print alike and search declines
anyway, and that is the reason for the `@`.** `haveI := A.isIso_hom_of_isEmpty` gives
`IsIso A.hom ≟ IsIso A.hom`, with `toComma` occurring nowhere in that trace, and the term fails
with `failed to synthesize instance of type class IsIso A.hom` at a goal that has it in context.
**It is the stronger of the two facts**: a reader holding only the first would conclude that
naming the specialised statement in a `haveI` would have done, and it does not. All three are runs
and none is a reading.

**The clause this replaces gave the `≟` line under the hypothesis shape, which prints the other
one, and it is corrected rather than dated.** A hypothesis about a fixed `A` carries no
metavariable, so the pairing was already wrong at the commit that wrote it — and a dated record
says what a clause read *until* some day, which presupposes it read true before that day, the
distinction `README.md`'s *The `until <date>` record* draws in the paragraph opening *The wording
this section repairs here is corrected and not dated*. **Argued at taxis #2075.**

**This is the statement the module docstring's `## What is not here` declines to make in a
stronger form.** It says every object is isomorphic to `…SeparatedFiniteEtaleOver.id X`; it does
not say the category is equivalent to a point, and nothing below reads it that way. -/
noncomputable def SeparatedFiniteEtaleOver.isoIdOfIsEmpty (A : SeparatedFiniteEtaleOver.{u} X) :
    A ≅ SeparatedFiniteEtaleOver.id.{u} X :=
  MorphismProperty.Over.isoMk (@asIso _ _ _ _ A.hom A.isIso_hom_of_isEmpty)
    (Category.comp_id A.hom)

/-- **Over an empty base the terminal object is initial.**

`CategoryTheory.Limits.IsInitial.ofUniqueHom` at the inverse of
`…SeparatedFiniteEtaleOver.isoIdOfIsEmpty`. Uniqueness
is the terminality this category already has and not a second argument: two morphisms out of
`…SeparatedFiniteEtaleOver.id X` composed with that isomorphism are two morphisms **into** it, so
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.isTerminalId` identifies them and
`CategoryTheory.Iso.cancel_iso_hom_right` cancels.

**`…SeparatedFiniteEtaleOver.isTerminalId` asks nothing of the base**, so the object is terminal
with or without this file's hypothesis and the content here is the initial half alone. -/
noncomputable def SeparatedFiniteEtaleOver.isInitialIdOfIsEmpty (X : AnalyticSpace.{u})
    [IsEmpty (X : Type u)] : IsInitial (SeparatedFiniteEtaleOver.id.{u} X) :=
  IsInitial.ofUniqueHom (fun A ↦ A.isoIdOfIsEmpty.inv) fun A f ↦ by
    rw [← Iso.cancel_iso_hom_right f A.isoIdOfIsEmpty.inv A.isoIdOfIsEmpty]
    exact (SeparatedFiniteEtaleOver.isTerminalId.{u} X).hom_ext _ _

/-- **So no `FintypeCat`-valued functor out of that category is a fibre functor**, over an empty
base.

The one object is initial and terminal at once, so its image is empty by
`CategoryTheory.PreGaloisCategory.initial_iff_fiber_empty` and has a point by
`CategoryTheory.Limits.IsTerminal.isTerminalObj`: the point is the value at `PUnit.unit` of the
morphism a terminal object of `FintypeCat` receives from the one-point object.

**The target universe is free.** `CategoryTheory.PreGaloisCategory.FiberFunctor` is stated at
`FintypeCat.{w}` for an arbitrary `w`, and nothing in the argument constrains it to the hom
universe of this category, which is the one `CategoryTheory.GaloisCategory`'s own field quantifies
over. -/
theorem SeparatedFiniteEtaleOver.not_isFiberFunctor_of_isEmpty
    (F : SeparatedFiniteEtaleOver.{u} X ⥤ FintypeCat.{w}) :
    ¬ PreGaloisCategory.FiberFunctor F := by
  intro hF
  haveI := hF
  have hempty : IsEmpty (F.obj (SeparatedFiniteEtaleOver.id.{u} X)) :=
    (PreGaloisCategory.initial_iff_fiber_empty F _).1
      ⟨SeparatedFiniteEtaleOver.isInitialIdOfIsEmpty X⟩
  have hterm : IsTerminal (F.obj (SeparatedFiniteEtaleOver.id.{u} X)) :=
    IsTerminal.isTerminalObj F _ (SeparatedFiniteEtaleOver.isTerminalId.{u} X)
  exact hempty.false (hterm.from (FintypeCat.of.{w} PUnit) PUnit.unit)

/-- **And the covers separated over an empty base are not a `CategoryTheory.GaloisCategory`.**

The class is `CategoryTheory.PreGaloisCategory` — which this category has over `[T2Space X]`, and an
empty space is Hausdorff — together with the **existence** of a `FintypeCat`-valued fibre functor,
and it is that existential
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.not_isFiberFunctor_of_isEmpty` refutes. **So
`[Nonempty X]` on `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.galoisCategory` is a
hypothesis of the mathematics**: it is not an artefact of this repository's fibre functors being
taken at a point.

The `CategoryTheory.PreGaloisCategory` instance the field's fibre functors are stated over is the
one carried by the hypothesis being refuted rather than the one instance search finds, and the two
are interchangeable because that class is a `Prop`. -/
theorem SeparatedFiniteEtaleOver.not_galoisCategory_of_isEmpty :
    ¬ GaloisCategory (SeparatedFiniteEtaleOver.{u} X) := by
  intro h
  obtain ⟨F, ⟨hF⟩⟩ := h.hasFiberFunctor
  exact SeparatedFiniteEtaleOver.not_isFiberFunctor_of_isEmpty F hF

end ComplexAnalytic.AnalyticSpace
