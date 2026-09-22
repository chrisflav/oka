/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Analytification.ModuleFiniteAnalytification

/-!
# A finite morphism of affine `ℂ`-schemes analytifies to a finite morphism

`Oka/Analytification/ModuleFiniteAnalytification.lean` proves that a `ComplexAnalytic.PresHom`
whose ring map is module-finite analytifies to an `ComplexAnalytic.AnalyticSpace.IsFinite`
morphism. **This file states the same thing with the hypothesis read on the algebraic side
instead**, as `AlgebraicGeometry.IsFinite` of the morphism of spectra, which is the vocabulary the
eight prose sites recording *the analytification of a finite étale morphism of schemes* use.

## The whole content is one `iff` of Mathlib's, and the import is free

`AlgebraicGeometry.IsFinite.SpecMap_iff` (`Mathlib/AlgebraicGeometry/Morphisms/Finite.lean`) says
that `AlgebraicGeometry.IsFinite` of `AlgebraicGeometry.Spec.map f` is `RingHom.Finite` of `f`,
supplied by the `AlgebraicGeometry.HasAffineProperty` instance for that class, which is
`AlgebraicGeometry.affineAnd RingHom.Finite`. So the theorem below is that `iff` composed with the
theorem above, and there is no analysis in it at all.

**The import is free and that was measured rather than assumed.** `AlgebraicGeometry.IsFinite` and
its affine criterion are already in the closure of the one `Oka` module this file imports: a
scratch file importing `Oka.Analytification.ModuleFiniteAnalytification` and **nothing else**
elaborates `AlgebraicGeometry.IsFinite.SpecMap_iff` at exit 0. So this file adds **one** `Oka`
module and **zero** Mathlib modules, which is why it is a file of its own rather than a hypothesis
change to the theorem it wraps.

## Main results

- `ComplexAnalytic.isFinite_analytificationMap_of_isFinite_specMap`: **a `ℂ`-algebra map of
  presented algebras whose spectrum morphism is finite analytifies to a finite morphism of
  analytic spaces.**

## What is not here, and the first bullet is the one that matters

* **Nothing about `ComplexAnalytic.AnalyticSpace.IsFiniteEtale`, and this narrows none of the
  eight sentences that record the analytification of a finite *étale* morphism as absent.**
  `Oka/AnalyticSpace/LocalIso.lean`, `Oka/AnalyticSpace/CoveringMap.lean`,
  `Oka/AnalyticSpace/SigmaFiniteEtale.lean`, `Oka/AnalyticSpace/Degree.lean`,
  `Oka/AnalyticSpace/SeparatedOver.lean`, `Oka/Analytification/Hausdorff.lean`,
  `Oka/Analytification/StandardEtaleFiniteness.lean` and
  `Oka/Analytification/StandardEtaleFiniteEtale.lean` are the eight, and **every one of them is
  about the étale half and none of them is touched.** This is the *finite* half, and only over an
  affine base: étaleness enters nowhere below and the Zariski-local gluing that would take an
  affine statement to a general morphism of schemes is not started.
* **No converse.** Nothing says a finite analytification comes from a finite morphism of spectra,
  which is the direction a comparison functor's essential surjectivity would want.
* **No `AlgebraicGeometry.Scheme`-valued analytification.** The morphism analytified below is
  `ComplexAnalytic.analytificationMap` of a presentation-level map, and the algebraic side enters
  only as a hypothesis about `AlgebraicGeometry.Spec.map`. Building
  `Oka/Analytification/AffineCover.lean`'s `analytificationOfScheme` is the different and
  `{u}`-collapsing job `Oka/Analytification/ModuleFiniteAnalytification.lean` names, and it is
  untouched — that file's *No `AlgebraicGeometry.Scheme`* bullet is about its own statement and
  stays true of it.
* **No choice of presentation.** The theorem is read at a `ComplexAnalytic.PresHom` in hand.
  Reading it at `ComplexAnalytic.analytificationFGAlg`, where the presentation is gone from the
  statement, needs `ComplexAnalytic.analytificationFGAlgObjIso` and is not done below.
-/

open CategoryTheory AlgebraicGeometry

universe u

namespace ComplexAnalytic

variable {n n' k k' : ℕ} {g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ}
  {g' : Fin k' → MvPolynomial (ULift.{u} (Fin n')) ℂ}

/-- **A `ℂ`-algebra map of presented algebras whose morphism of spectra is finite analytifies to a
finite morphism of analytic spaces.**

`ComplexAnalytic.PresHom.toRingHom` goes `B ⟶ A` where the analytified morphism goes
`A^an ⟶ B^an`, and `AlgebraicGeometry.Spec.map` reverses it again, so the morphism of spectra runs
in the same direction as the analytified one and the hypothesis is about the arrow a reader
expects.

The proof is `AlgebraicGeometry.IsFinite.SpecMap_iff` followed by
`ComplexAnalytic.isFinite_analytificationMap_of_finite`: the `iff` is the affine criterion for
`AlgebraicGeometry.IsFinite`, which is `AlgebraicGeometry.affineAnd RingHom.Finite` through the
`AlgebraicGeometry.HasAffineProperty` instance, and the second is where all the work is. -/
theorem isFinite_analytificationMap_of_isFinite_specMap (ψ : PresHom.{u} g g')
    (h : IsFinite (Spec.map (CommRingCat.ofHom ψ.toRingHom))) :
    AnalyticSpace.IsFinite (analytificationMap.{u} ψ) :=
  isFinite_analytificationMap_of_finite ψ ((IsFinite.SpecMap_iff _).mp h)

end ComplexAnalytic
