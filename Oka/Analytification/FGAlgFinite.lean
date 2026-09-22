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

## The two readings, and this file carries both

There are two statements a reader can mean by *read it at the functor*, and they are not the same
job.

1. **The presentation still indexes the objects.** The morphism is
   `(toFGAlg ⋙ analytificationFGAlg).map ψ` for `ψ` a morphism of presentations, and the
   hypothesis is the one the theorem above already takes. **That is the first theorem below**, and
   its whole content is that the functor's morphism is the presentation-level one conjugated by the
   comparison isomorphism — `ComplexAnalytic.toFGAlg_comp_analytificationFGAlg_map` — together
   with the fact that a composite of finite morphisms is finite and an isomorphism is finite.
2. **The presentation is gone altogether.** The morphism is `analytificationFGAlg.map f` for an
   arbitrary `f` between finitely generated `ℂ`-algebras. `ComplexAnalytic.analytificationFGAlg`
   *is* `toFGAlg.asEquivalence.inverse ⋙ analytificationFunctor` by definition, so there is no
   work in the conclusion at all and all of it is in the hypothesis: carrying `RingHom.Finite`
   of `f` across the equivalence's counit, which is built from
   `ComplexAnalytic.exists_presentation` and so from `Classical.choice`. **That is the second
   theorem below**, and what the transport costs is two applications of `RingHom.Finite.comp`
   against `RingHom.Finite.of_surjective` at each end — the ends being the two chosen
   presentations' comparison isomorphisms, read as algebra equivalences.

**Three wordings of this section are retired by the second reading and are recorded here rather
than struck.** Until 2026-09-22 the heading read *The two readings, and this file is the first of
them*; item 1 read *That is this file, and its whole content is…*, whose *this file* is now the
first theorem; and item 2 ended *`RingHom.finite_respectsIso` is the Mathlib side of that. Nothing
here is evidence about its size and it is not started.* **All three were exact at `da252a7`, the
commit that wrote this file, and all three are retired by a push of the same day** — one day is the
shortest interval any record in this file spans. **`RingHom.finite_respectsIso` is usable here and
is not what the proof takes**: Mathlib proves it *from* `RingHom.Finite.of_surjective` and
composition, and a three-fold composite of algebra maps wants those two directly rather than a
two-sided `RingHom.RespectsIso` matched against it twice. That is a pointer one step too abstract
and not a false one, so it is retired as part of the item and not corrected.

**The ingredient the first reading needs is the naturality of the comparison and not the
comparison itself.** `ComplexAnalytic.analytificationFGAlgObjIso` is an isomorphism of objects; a
statement about a *morphism* needs the square, which is
`ComplexAnalytic.analytificationFGAlgObjIso_naturality`. That distinction is why this file is
short and why a clause pointing a reader at the object isomorphism alone was pointing at
something that cannot prove it.

## What the import costs, measured

This file is the first module **under `Oka/`** to import both
`Oka/Analytification/Functor.lean` and `Oka/Analytification/SpecFiniteAnalytification.lean`: at
the commit this file is added to, neither is in the other's import closure. **`Oka.lean`, the
aggregator `mk_all` generates, imports both as it imports every module of the library, and is
excluded from that claim**, as `OkaTest/Axioms.lean` excludes it from the same kind of grep; so
are the 99 modules under `OkaTest/` that reach both through it. At `73176e1` the modules with
both in import closure are **102** — those 99, the two aggregators, and this file, which is the
only one under `Oka/`. **That clause read *"the first module to import
both"* and was false at `da252a7`, the commit that wrote it, for the reason just given; it is
corrected here and not dated**, on `README.md`'s rule that a clause false when it was written is
corrected rather than recorded. **Against the closure of
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
- `ComplexAnalytic.isFinite_analytificationFGAlg_map_of_finite`: **and the same with the
  presentations quantified away** — a module-finite map of finitely generated `ℂ`-algebras is sent
  by `ComplexAnalytic.analytificationFGAlg` to a finite morphism, with no presentation in the
  statement at all.
- `ComplexAnalytic.isFinite_analytificationFGAlg_map_of_isFinite_specMap`: **and that one with the
  hypothesis on the spectra as well**, so the two vocabularies are crossed with the two readings.

## What is not here

* **This bullet read *The second reading above, at an arbitrary morphism of finitely generated
  `ℂ`-algebras with no presentation in the statement. It is a transport across the equivalence's
  counit and is untouched.* until 2026-09-22.** That transport is the last two theorems below;
  nothing of the *finite* half is left unread at this functor, in either vocabulary.
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

/-- **A module-finite map of finitely generated `ℂ`-algebras is sent to a finite morphism, with no
presentation anywhere in the statement.**

The theorem above is the same statement at a morphism `ComplexAnalytic.toFGAlg` produces, where a
presentation still indexes each object; this is it with the presentations quantified away, which is
the form a statement about `ComplexAnalytic.analytificationFGAlg` alone can have.

**The transport is on the ring map and not on the morphism of spaces**, and that is the whole of
the proof. `ComplexAnalytic.toFGAlgFullyFaithful.preimage` turns `φ.hom ≫ f ≫ χ.inv` into a
`ComplexAnalytic.PresHom` whose `toRingHom` is **definitionally** the composite of the three
underlying algebra maps, so the hypothesis below is stated as that composite and applied where the
`preimage`'s own is expected, and the hypothesis travels by
`RingHom.Finite.comp` twice, against `RingHom.Finite.of_surjective` at each end. The two ends are
surjective because they are isomorphisms in a full subcategory of `CommAlgCat ℂ`, and
`CommAlgCat.algEquivOfIso` of the inclusion's image is what says so. The conclusion
is then carried back across the images of those two isomorphisms, in `AnalyticSpace`.

**`RingHom.finite_respectsIso` is not the ingredient this needs**, and
`Oka/Analytification/SpecFiniteAnalytification.lean` named it as the Mathlib side of exactly this
transport. It is the right fact and one step too abstract: Mathlib proves it *from*
`RingHom.Finite.of_surjective` and composition, and using it here would mean producing a
`RingEquiv` from each end's `AlgEquiv` and then matching `RingHom.RespectsIso`'s two-sided shape
against a three-fold composite. The two lines below are what the prediction was reaching for.

**The presentations are chosen and nothing depends on the choice**, which is what makes this a
statement about the algebra: `CategoryTheory.Functor.objObjPreimageIso` is
`ComplexAnalytic.toFGAlg.EssSurj`, and that instance is `ComplexAnalytic.exists_presentation` and
so `Classical.choice`. -/
theorem isFinite_analytificationFGAlg_map_of_finite
    {X Y : (isFiniteType.{u}.FullSubcategory)ᵒᵖ} (f : X ⟶ Y)
    (hf : (f.unop.hom.hom).toRingHom.Finite) :
    AnalyticSpace.IsFinite (analytificationFGAlg.{u}.map f) := by
  obtain ⟨P, ⟨φ⟩⟩ : ∃ P : Presentation.{u}, Nonempty (toFGAlg.{u}.obj P ≅ X) :=
    ⟨_, ⟨toFGAlg.{u}.objObjPreimageIso X⟩⟩
  obtain ⟨Q, ⟨χ⟩⟩ : ∃ Q : Presentation.{u}, Nonempty (toFGAlg.{u}.obj Q ≅ Y) :=
    ⟨_, ⟨toFGAlg.{u}.objObjPreimageIso Y⟩⟩
  have hψ : RingHom.Finite ((φ.hom.unop.hom.hom).toRingHom.comp
      ((f.unop.hom.hom).toRingHom.comp (χ.inv.unop.hom.hom).toRingHom)) :=
    (RingHom.Finite.of_surjective _
        (CommAlgCat.algEquivOfIso ((isFiniteType.{u}).ι.mapIso φ.unop)).surjective).comp
      (hf.comp (RingHom.Finite.of_surjective _
        (CommAlgCat.algEquivOfIso ((isFiniteType.{u}).ι.mapIso χ.symm.unop)).surjective))
  have key := isFinite_toFGAlg_comp_analytificationFGAlg_map_of_finite.{u}
    (toFGAlgFullyFaithful.{u}.preimage (φ.hom ≫ f ≫ χ.inv)) hψ
  rw [Functor.comp_map, toFGAlgFullyFaithful.{u}.map_preimage, Functor.map_comp,
    Functor.map_comp] at key
  have e : analytificationFGAlg.{u}.map f =
      inv (analytificationFGAlg.{u}.map φ.hom) ≫
        (analytificationFGAlg.{u}.map φ.hom ≫ analytificationFGAlg.{u}.map f ≫
          analytificationFGAlg.{u}.map χ.inv) ≫ inv (analytificationFGAlg.{u}.map χ.inv) := by
    simp
  rw [e]
  exact @AnalyticSpace.isFinite_comp _ _ _ _ _ (AnalyticSpace.isFinite_of_isIso _)
    (@AnalyticSpace.isFinite_comp _ _ _ _ _ key (AnalyticSpace.isFinite_of_isIso _))

/-- **And the same with the hypothesis read as finiteness of the morphism of spectra**, which is
the vocabulary the prose sites about finite morphisms of schemes use.

This stands to the theorem above as
`ComplexAnalytic.isFinite_toFGAlg_comp_analytificationFGAlg_map_of_isFinite_specMap` stands to
`ComplexAnalytic.isFinite_toFGAlg_comp_analytificationFGAlg_map_of_finite`: it is that theorem
composed with `AlgebraicGeometry.IsFinite.SpecMap_iff`, and there is no analysis in it. -/
theorem isFinite_analytificationFGAlg_map_of_isFinite_specMap
    {X Y : (isFiniteType.{u}.FullSubcategory)ᵒᵖ} (f : X ⟶ Y)
    (h : IsFinite (Spec.map (CommRingCat.ofHom (f.unop.hom.hom).toRingHom))) :
    AnalyticSpace.IsFinite (analytificationFGAlg.{u}.map f) :=
  isFinite_analytificationFGAlg_map_of_finite.{u} f ((IsFinite.SpecMap_iff _).mp h)

end ComplexAnalytic
