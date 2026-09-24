/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Analytification.ChangeOfVariables
import Oka.AnalyticSpace.Finite

/-!
# A surjection of presented algebras analytifies to a finite morphism

`Oka/Analytification/HypersurfaceFinite.lean` decomposes *the analytification of a module-finite
map of presented `ℂ`-algebras is finite* into three obstructions, discharges two of them, and
prices the third:

> **The quotient is the wall, and it is not an induction at all.** A module-finite `A`-algebra is
> a *quotient* of an iterated hypersurface: adjoin one root per module generator, then kill the
> kernel. The surjection is finite on the algebraic side because it is a closed immersion, and
> what that needs analytically is that **a surjection of presented algebras has closed-embedding
> base map**.

**This file is that statement.** A surjection of presented `ℂ`-algebras adds relations and no
variables, so it is `ComplexAnalytic.PresHom.ofRename` at the identity between two presentations
in the *same* `n` variables whose ideals are nested, and its analytification is the inclusion of
one zero locus into a larger one inside a single `ℂ^n`.

## The proof, and there is no analytic content in it

The triangle `ComplexAnalytic.analytificationMap_ofRename_id_comp` — the induced morphism followed
by the inclusion of the larger zero locus into `ℂ^n` is the inclusion of the smaller one — is
`ComplexAnalytic.AnalyticSpace.hom_ext_complexAffineSpace` and one computation of the transported
tuple: a rename at the identity sends the class of a variable to the class of the same variable,
so the transported tuple is the source's own coordinates. Then
`ComplexAnalytic.isClosedEmbedding_base_analytificationIncl` is used **twice**, on the two sides of
that triangle, and `Topology.IsClosedEmbedding.of_comp_iff` cancels the outer one. **No new
topology and no Nullstellensatz.**

`ComplexAnalytic.AnalyticSpace.isFinite_of_isClosedEmbedding` turns the embedding into
`ComplexAnalytic.AnalyticSpace.IsFinite`, which is what the general theorem composes with the
tower's finiteness — this sentence said *"would compose"*, and
`ComplexAnalytic.isFinite_analytificationMap_ofRename_id_comp_towerPresHom`
(`Oka/Analytification/ModuleFiniteAnalytification.lean`) is the composition. That step asks
nothing of the map on structure sheaves, so a surjection being finite here is a topological fact
and not a coherence one.

## Why the two theorems are stated at `ComplexAnalytic.PresHom.ofRename` and not at a wrapper

A `def` naming *the* surjection attached to a pair of nested ideals would read better at a call
site and would cost a reader the identification with `ComplexAnalytic.PresHom.ofRename`, which is
where every lemma about the construction lives — `ComplexAnalytic.PresHom.ofRename_comp` in
particular, which is what a tower consumes. The hypothesis is written
`MvPolynomial.rename id (g' j) ∈ presentationIdeal g` rather than `g' j ∈ presentationIdeal g` for
the same reason: it is `ComplexAnalytic.PresHom.ofRename`'s own hypothesis at `σ = id` and needs no
translation to be passed on. `MvPolynomial.rename_id` is a `simp` lemma, so a caller holding the
second form supplies the first with `simpa using h`, which is compiled in a spike against this
file and not inferred from the lemma's attribute.

`ComplexAnalytic.PresHom.ofRename_id_toRingHom_surjective` is what entitles the word *surjection*
in the title: nothing else here checks that the map is onto, and the two geometric statements would
be true of a `ComplexAnalytic.PresHom.ofRename` at a non-surjective renaming as well — with the
containment of ideals doing the work either way.

## Main results

- `ComplexAnalytic.PresHom.ofRename_id_toRingHom_surjective`: **a rename at the identity between
  presentations in the same variables is a surjection of algebras**, the quotient map of the two
  nested ideals.
- `ComplexAnalytic.analytificationMap_ofRename_id_comp`: **the induced morphism lies over `ℂ^n`** —
  followed by the inclusion of the larger zero locus it is the inclusion of the smaller one.
- `ComplexAnalytic.isClosedEmbedding_base_analytificationMap_ofRename_id`: **the induced morphism
  is a closed embedding on points**, which is the statement
  `Oka/Analytification/HypersurfaceFinite.lean` priced and left unstated.
- `ComplexAnalytic.isFinite_analytificationMap_ofRename_id`: **the analytification of a surjection
  of presented algebras is finite.**

## What is not here

* **The general module-finite theorem, which is not here and is no longer missing.** This bullet
  used to read *"What is missing between here and it is a **construction**: from a module-finite
  `ψ : ComplexAnalytic.PresHom g g'`, pick module generators, adjoin one root per generator with
  `ComplexAnalytic.towerPresHom`, and exhibit the target as the quotient of that tower by the
  kernel."* That construction is `Oka/Analytification/ModuleFiniteAnalytification.lean` and it is
  the construction this bullet describes, step for step;
  `ComplexAnalytic.isFinite_analytificationMap_of_finite` is the theorem and it reads this file's
  `ComplexAnalytic.isFinite_analytificationMap_ofRename_id`. **This file is still one of its
  inputs and not the theorem**, which is what the bullet's first clause says and what stays true.
* **The different-numbers-of-variables surjection.** A surjection between presentations in
  different numbers of variables is not a `ComplexAnalytic.PresHom.ofRename` at the identity and
  **nothing here is evidence about it.** The same-variables case is the one the module-finite
  argument produces, because the quotient there is taken inside the tower's own polynomial ring —
  which `ComplexAnalytic.isFinite_analytificationMap_of_finite` now confirms by construction
  rather than by prediction, at the cost of the source presentation it produces not being the one
  it is handed.
* **No converse.** Nothing says a finite analytification comes from a module-finite map, and
  nothing here relates the fibres to anything.
* **Nothing about `ComplexAnalytic.AnalyticSpace.IsFinite`'s sheaf-theoretic strength.** The class
  is closed with finite fibres and no coherence is asked or supplied, which is why a closed
  embedding is finite in one line.
-/

open CategoryTheory Opposite AlgebraicGeometry Topology

universe u

namespace ComplexAnalytic

variable {n k k' : ℕ} {g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ}
  {g' : Fin k' → MvPolynomial (ULift.{u} (Fin n)) ℂ}

/-! ### The surjection -/

/-- **A rename at the identity between two presentations in the same variables is surjective.**

Its value on a class is the class of the same polynomial — `ComplexAnalytic.PresHom.ofRename` at
`σ = id`, with `MvPolynomial.rename_id_apply` — so it is the quotient map of the larger ideal by the
smaller and `Ideal.Quotient.mk_surjective` is the whole proof. This is what makes *surjection* the
right word for the two theorems below; neither of them uses it. -/
theorem PresHom.ofRename_id_toRingHom_surjective
    (h : ∀ j, MvPolynomial.rename (_root_.id : ULift.{u} (Fin n) → ULift.{u} (Fin n)) (g' j) ∈
      presentationIdeal.{u} g) :
    Function.Surjective (PresHom.ofRename.{u} _root_.id h).toRingHom := by
  intro x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨Ideal.Quotient.mk (presentationIdeal.{u} g') p,
    (PresHom.ofRename_toRingHom_mk.{u} _root_.id h p).trans
      (congrArg (Ideal.Quotient.mk (presentationIdeal.{u} g)) (MvPolynomial.rename_id_apply p))⟩

/-! ### The triangle over `ℂ^n` -/

/-- **The induced morphism lies over `ℂ^n`**: followed by the inclusion of the larger zero locus
into `ℂ^n`, it is the inclusion of the smaller one.

`ComplexAnalytic.AnalyticSpace.hom_ext_complexAffineSpace` reduces this to the pullbacks of the
`n` coordinates, and there
`ComplexAnalytic.coordPullback_analytificationMap_comp` says the left-hand side is the transported
tuple. **The transported tuple of a rename at the identity is the source's own coordinates**: it is
`quotientToGlobal g` of the class of `MvPolynomial.rename id (X j)`, and that is
`ComplexAnalytic.quotientToGlobal_mk_X`, whose value is `ComplexAnalytic.analytificationCoord g j`
— which is the right-hand side by definition.

**Both steps are `change` and not `show`, and that is measured rather than stylistic**: each does
alter the goal — the first folds the coordinate pullbacks back into
`ComplexAnalytic.AnalyticSpace.coordPullback`, the second unfolds
`ComplexAnalytic.transported` — and `Mathlib`'s style linter fails a `show` that changes anything.
`ComplexAnalytic.isFinite_analytificationMap_towerPresHom` records the same rule at two sites. -/
theorem analytificationMap_ofRename_id_comp
    (h : ∀ j, MvPolynomial.rename (id : ULift.{u} (Fin n) → ULift.{u} (Fin n)) (g' j) ∈
      presentationIdeal.{u} g) :
    analytificationMap.{u} (PresHom.ofRename.{u} id h) ≫ analytificationInclHom.{u} g' =
      analytificationInclHom.{u} g := by
  refine AnalyticSpace.hom_ext_complexAffineSpace _ _ fun j ↦ ?_
  change AnalyticSpace.coordPullback (analytificationMap.{u} (PresHom.ofRename.{u} id h) ≫
      analytificationInclHom.{u} g') j =
    AnalyticSpace.coordPullback (analytificationInclHom.{u} g) j
  rw [coordPullback_analytificationMap_comp]
  change quotientToGlobal.{u} g ((PresHom.ofRename.{u} id h).toRingHom
    (Ideal.Quotient.mk (presentationIdeal.{u} g') (MvPolynomial.X j))) = _
  rw [PresHom.ofRename_toRingHom_mk, MvPolynomial.rename_X, id_eq, quotientToGlobal_mk_X]
  rfl

/-! ### The closed embedding, and finiteness -/

/-- **The analytification of a surjection of presented algebras is a closed embedding on points.**

This is the statement `Oka/Analytification/HypersurfaceFinite.lean` priced from a spike and did not
state, and its proof is that spike's:
`ComplexAnalytic.isClosedEmbedding_base_analytificationIncl` twice, on the two sides of the
triangle above, with `Topology.IsClosedEmbedding.of_comp_iff` cancelling the outer factor.

The triangle is transported to locally ringed spaces by `congrArg` at
`ComplexAnalytic.AnalyticSpace.Hom.toLRSHom` rather than by rewriting under a functor, and the
composite is then handed to `Topology.IsClosedEmbedding.of_comp_iff` unnormalised: the base map of
a composite **is** the composite of the base maps, so no `simp only` has to traverse a goal in
which `ComplexAnalytic.analytificationMap` and `ComplexAnalytic.PresHom.ofRename` occur with proof
arguments. That is `Oka/Analytification/RefineDatumTransition.lean`'s recorded route to a planted
congruence lemma, and avoiding it here is why this file's declaration count equals what it
declares. -/
theorem isClosedEmbedding_base_analytificationMap_ofRename_id
    (h : ∀ j, MvPolynomial.rename (id : ULift.{u} (Fin n) → ULift.{u} (Fin n)) (g' j) ∈
      presentationIdeal.{u} g) :
    IsClosedEmbedding ⇑(analytificationMap.{u} (PresHom.ofRename.{u} id h)).base := by
  have hcomp : (analytificationMap.{u} (PresHom.ofRename.{u} id h)).toLRSHom ≫
      analytificationIncl.{u} g' = analytificationIncl.{u} g :=
    congrArg AnalyticSpace.Hom.toLRSHom (analytificationMap_ofRename_id_comp.{u} h)
  have hce : IsClosedEmbedding
      ⇑((analytificationMap.{u} (PresHom.ofRename.{u} id h)).toLRSHom ≫
        analytificationIncl.{u} g').base :=
    hcomp ▸ isClosedEmbedding_base_analytificationIncl.{u} g
  exact (isClosedEmbedding_base_analytificationIncl.{u} g').of_comp_iff.1 hce

/-- **The analytification of a surjection of presented algebras is finite.**

`ComplexAnalytic.AnalyticSpace.isFinite_of_isClosedEmbedding` and the theorem above, and that is
the whole of it: the class asks for a closed map with finite fibres and a closed embedding is both,
so **nothing about the map on structure sheaves enters**.

This is the input `Oka/Analytification/HypersurfaceFinite.lean`'s third obstruction needs, and it
is the half of that obstruction which is analytic. The other half is the construction — the
generators and the kernel — and it is not here: it is
`ComplexAnalytic.isFinite_analytificationMap_of_finite`
(`Oka/Analytification/ModuleFiniteAnalytification.lean`). This theorem's only consumer is that
file's `ComplexAnalytic.isFinite_analytificationMap_ofRename_id_comp_towerPresHom`, which composes
it with the tower. -/
theorem isFinite_analytificationMap_ofRename_id
    (h : ∀ j, MvPolynomial.rename (id : ULift.{u} (Fin n) → ULift.{u} (Fin n)) (g' j) ∈
      presentationIdeal.{u} g) :
    AnalyticSpace.IsFinite (analytificationMap.{u} (PresHom.ofRename.{u} id h)) :=
  AnalyticSpace.isFinite_of_isClosedEmbedding _
    (isClosedEmbedding_base_analytificationMap_ofRename_id.{u} h)

end ComplexAnalytic
