/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.AnalyticSpace.CoveringMap
import Oka.AnalyticSpace.Glue
import Oka.AnalyticSpace.InverseImageSheet
import Oka.Topology.IsLocalHomeomorph

/-!
# A covering space of a complex analytic space is a complex analytic space

Let `X` be a complex analytic space and `p : E → X` a local homeomorphism of topological spaces.
Then `E` carries a complex analytic structure — the inverse image `p⁻¹𝒪_X` of the structure sheaf
— for which `p` is a morphism of analytic spaces, and that morphism is a local isomorphism. If `p`
is moreover **closed** and has finite fibres it is **finite étale**, and a covering map with
finite fibres is such a `p`.

This is the Riemann existence theorem's topological input: it is what turns a topological covering
of an analytic space into an object of the category the theorem compares with finite étale
algebras.

## The `ℂ`-algebra structure is not glued, and that is the design

`ComplexAnalytic.HasLocalModels` is a *property* and is local on the space
(`ComplexAnalytic.HasLocalModels.of_iSup_eq_top`), but the `ℂ`-algebra structure is *data* landing
in **global** sections, so it does not restrict from a cover for free —
`Oka/AnalyticSpace/Local.lean`'s docstring is explicit about the difference, and
`ComplexAnalytic.AnalyticSpace.ofOpensCompatible` is the constructor that glues one from
structures on the members.

**Nothing here glues anything.** `AlgebraicGeometry.LocallyRingedSpace.inverseImageHom` is a
morphism `p⁻¹X ⟶ X` defined on the whole of `p⁻¹X`, so `X`'s structure pulled back along it is
already a structure on the global sections of `p⁻¹X`
(`ComplexAnalytic.inverseImageAlgMap`), and `ComplexAnalytic.AnalyticSpace.ofHasLocalModels` is
all that is needed. The cover is used for the *property* and for nothing else.

That is what sidesteps the gap
`Oka/Geometry/RingedSpace/LocallyRingedSpace/InverseImageSheet.lean` records under its
`## What is not here`: *"No cocycle and no gluing. Two sheets `V₀`, `V₁` meeting give two
isomorphisms over `p '' (V₀ ∩ V₁)` and nothing here compares them."* Two sheets are never
compared below, so the naive `p '' (V₀ ∩ V₁) = p '' V₀ ∩ p '' V₁` — **false** for a covering map,
as that file's counterexample shows — is never needed.

## The cover, and what each member costs

The members are the **sheets**: `sheetOpens ⇑p`, the opens of `E` on which `p` is an open
embedding, which cover by `IsLocalHomeomorph.sSup_sheetOpens`. Over one sheet `V` the three
inputs compose with nothing left over:

* `AlgebraicGeometry.LocallyRingedSpace.sheetIso` identifies `(p⁻¹X)|V` with `X|(p '' V)` as
  locally ringed spaces;
* `ComplexAnalytic.isCLinearHom_sheetHom` makes that identification `ℂ`-linear — an isomorphism
  of locally ringed spaces between analytic spaces can be antiholomorphic, so this half is not
  decoration. It is not, however, what `ComplexAnalytic.HasLocalModels.of_iso` is handed below:
  after `AlgebraicGeometry.LocallyRingedSpace.sheetIso_hom` that obligation is the by-definition
  `ComplexAnalytic.isCLinearHom_comapAlgMap`, and the sheet linearity reaches the assembly one
  level down, through the next bullet;
* `ComplexAnalytic.comapAlgMap_sheetHom` says the structure the sheet inherits *is* the ambient
  one restricted, which is the side of the seam `of_iSup_eq_top` states its hypothesis on. **This
  is the lemma `ComplexAnalytic.isCLinearHom_sheetHom` is consumed by**: the sheet linearity is
  what makes that equality of structures true.

So the member obligation is `ComplexAnalytic.HasLocalModels.restrict` on `X` and two rewrites.

## Finiteness is the only thing that is not already here

`ComplexAnalytic.AnalyticSpace.IsLocalIso` costs nothing: its topological field is the hypothesis
itself, and its stalk field is the instance
`AlgebraicGeometry.LocallyRingedSpace.isIso_stalkMap_inverseImageHom` — *every* stalk map of the
inverse image is an isomorphism, for an arbitrary continuous map.

`ComplexAnalytic.AnalyticSpace.IsFinite` is *closed base map* and *finite fibres*, and
`ComplexAnalytic.AnalyticSpace.base_coveringSpaceHom` says the base map is `p` on the nose, so
**both fields are hypotheses of
`ComplexAnalytic.AnalyticSpace.isFinite_coveringSpaceHom_of_isClosedMap` and neither is proved**:
the closed field is the hypothesis, and the fibre field is the hypothesis at
`Set.Finite.to_subtype`, which changes a spelling and not the content. Closedness is not implied
by finite fibres — an open embedding has fibres of at most one point and need not be closed — so it
has to be asked for, and asking for it is the whole of what the general form spends on finiteness.

**Where a covering map enters is the corollary and not the statement.**
`ComplexAnalytic.AnalyticSpace.isFinite_coveringSpaceHom` is the covering-map form, and the one
lemma it adds on top of the general one is `IsCoveringMap.isClosedMap` in
`Oka/Topology/Covering/Basic.lean`, added for this file. It is the one new piece of mathematics
in this line and it is topology, not analysis; the finite-étale corollary
`ComplexAnalytic.AnalyticSpace.isFiniteEtale_coveringSpaceHom` is the same statement at the same
lemma. **The token `IsCoveringMap` occurs in exactly two statements of this file — those two
corollaries — and in no proof of it.**

`Oka/AnalyticSpace/CoveringMap.lean` goes the other way — finite étale implies covering map — and
needs `[T2Space]`, because Mathlib's criterion separates the points of a fibre. **This direction
needs no separation axiom**, and none is assumed below.

## Uniqueness, and the reading of it that carries no transport

**A local isomorphism over `X` is this construction, at its own base map.** For `q : E' ⟶ X`
*any* morphism of complex analytic spaces with `ComplexAnalytic.AnalyticSpace.IsLocalIso q`, its
source is isomorphic **over `X`** to the space built below on `q`'s own base map. That is the
reading of *"the structure is unique"* delivered here, and it is a choice among several.

That shape is also what makes the statement cheap. The literal reading — *given an analytic
structure on the topological space `E`, and a morphism whose base map is equal to `p`* — needs an
equality of `TopCat` objects and an equality of morphisms across it, and every statement about it
then carries a transport. `ComplexAnalytic.AnalyticSpace.coveringSpace` takes the local
homeomorphism as an argument, so the comparison space is built out of `q`'s own base map: `p` and
the hypothesis on it are then not hypotheses of the uniqueness statement at all, being read off
`q`. It is also *stronger* than the literal reading, because it pins the morphism and not only the
space.

**The `ℂ`-linearity of the inverse is where the work is, and it is not decoration.**
`AlgebraicGeometry.LocallyRingedSpace.isIso_toInverseImage` gives an isomorphism of *locally
ringed* spaces out of the stalk field of `ComplexAnalytic.AnalyticSpace.IsLocalIso` and nothing
else. That is **not** an isomorphism of analytic spaces: `ComplexAnalytic.AnalyticSpace` is a
**non-full** subcategory of `AlgebraicGeometry.LocallyRingedSpace` — a
`ComplexAnalytic.AnalyticSpace.Hom` is a `AlgebraicGeometry.LocallyRingedSpace.Hom` *plus* a proof
of `ComplexAnalytic.IsCLinearHom` — so an isomorphism downstairs hands back an inverse about whose
`ℂ`-linearity nothing has been said, and complex conjugation is a ring automorphism of the sheaf
of holomorphic functions. That is the same fact `Oka/AnalyticSpace/InverseImageSheet.lean` states
for a sheet. `ComplexAnalytic.IsCLinearHom.of_comp` read at `CategoryTheory.IsIso.inv_hom_id` is
the one line that closes it, and `ComplexAnalytic.AnalyticSpace.forgetToLocallyRingedSpace` being
faithful is what closes the two triangle identities.

**Agreement on stalks alone would not have been this statement**, which is worth saying because it
is the cheap thing a reader may expect to find here.
`AlgebraicGeometry.LocallyRingedSpace.stalkInverseImageIso` makes the stalk of `p⁻¹X` at `e` the
stalk of `X` at `p e`, and `IsLocalIso q` makes `q`'s stalk map an isomorphism, so *both* stalks
are canonically `X`'s stalk at the image point and any stalkwise agreement between them is
`IsLocalIso`'s own content restated. It says nothing whatever about the structure sheaves away
from a point, which is the entire question.

## Main definitions

- `ComplexAnalytic.inverseImageAlgMap`: the `ℂ`-algebra structure on `p⁻¹X`, pulled back from `X`
  along the whole of `AlgebraicGeometry.LocallyRingedSpace.inverseImageHom`.
- `ComplexAnalytic.AnalyticSpace.coveringSpace`: **the complex analytic space on the source of a
  local homeomorphism into a complex analytic space.**
- `ComplexAnalytic.AnalyticSpace.coveringSpaceHom`: the morphism of complex analytic spaces it
  carries, whose underlying map is `p`.
- `ComplexAnalytic.AnalyticSpace.toCoveringSpace`: **the comparison morphism** from the source of
  a local isomorphism `q` to the covering space built on `q`'s own base map. It is the identity on
  carriers.
- `ComplexAnalytic.AnalyticSpace.coveringSpaceIso`: the isomorphism of complex analytic spaces
  that comparison morphism is.

## Main results

- `ComplexAnalytic.hasLocalModels_inverseImage`: **the inverse image of a complex analytic space
  along a local homeomorphism has local models**, which is the whole of the object-level content.
- `ComplexAnalytic.AnalyticSpace.base_coveringSpaceHom`: the underlying map is `p` on the nose.
- `ComplexAnalytic.AnalyticSpace.isLocalIso_coveringSpaceHom`: **a local homeomorphism into a
  complex analytic space is a local isomorphism** for this structure.
- `ComplexAnalytic.AnalyticSpace.isFinite_coveringSpaceHom_of_isClosedMap` and
  `ComplexAnalytic.AnalyticSpace.isFiniteEtale_coveringSpaceHom_of_isClosedMap`: **a closed local
  homeomorphism with finite fibres is finite étale** for this structure.
- `ComplexAnalytic.AnalyticSpace.isFinite_coveringSpaceHom` and
  `ComplexAnalytic.AnalyticSpace.isFiniteEtale_coveringSpaceHom`: **a covering map with finite
  fibres is finite étale** for this structure —
  `ComplexAnalytic.AnalyticSpace.isFinite_coveringSpaceHom_of_isClosedMap` and
  `ComplexAnalytic.AnalyticSpace.isFiniteEtale_coveringSpaceHom_of_isClosedMap` at a covering
  map's closedness, with their statements unchanged.
- `ComplexAnalytic.AnalyticSpace.toCoveringSpace_comp`: the comparison morphism is a morphism
  over `X`.
- `ComplexAnalytic.AnalyticSpace.isIso_toCoveringSpace`: **it is an isomorphism of complex
  analytic spaces**, its inverse's `ℂ`-linearity included.
- `ComplexAnalytic.AnalyticSpace.exists_iso_coveringSpace`: **uniqueness** — every local
  isomorphism of complex analytic spaces over `X` is this construction at its own base map, and
  compatibly with the two maps to `X`.

## What is not here

* **No uniqueness of the comparison morphism stated *here*, though it is available.**
  `ComplexAnalytic.AnalyticSpace.exists_iso_coveringSpace` says an isomorphism over `X` exists and
  exhibits one; nothing below says it is the *only* morphism over `X` whose base map is the
  identity. **That is now an absence in this file alone and not in the tree**:
  `AlgebraicGeometry.LocallyRingedSpace.inverseImage_hom_ext` says a morphism into an inverse
  image is determined by its base map together with its composite to the base, of which the
  statement above is the case where the base map is the identity, and
  `Oka/AnalyticSpace/FiniteEtaleBaseChange.lean` is what consumes it. **Until 2026-09-07 this
  bullet ended with a sentence saying that `CategoryTheory.sheafifyLift_unique` was where the
  uniqueness *would* come from and that
  `Oka/Geometry/RingedSpace/LocallyRingedSpace/InverseImage.lean`'s own section of absences said
  so at the rung the argument would be run on**, and both halves stopped being true at once: that
  file now records the uniqueness as present, and the lemma it is proved from is
  `CategoryTheory.sheafify_hom_ext` rather than `CategoryTheory.sheafifyLift_unique`. Naturality
  in `q` is still missing and is still not stated here, and
  `Oka/Geometry/RingedSpace/LocallyRingedSpace/InverseImage.lean` does not state it either.
* **No statement for a `q` whose base map is *equal to* a given `p`.** The uniqueness above is
  read at `q`'s own base map, which is exactly what frees it of transport — see the module
  docstring. A consumer who arrives holding `p`, a proof that `q`'s base map equals it, and a
  structure on the carrier has to cross that equality, and nothing here does it for them.
* **The comparison with `ComplexAnalytic.AnalyticSpace.sigma` is not stated, and it is one
  application away.** The trivial `ι`-sheeted cover `ComplexAnalytic.AnalyticSpace.sigmaFold` is
  finite étale, hence a local isomorphism, so
  `ComplexAnalytic.AnalyticSpace.exists_iso_coveringSpace` applies to it and says that `sigma`'s
  own structure **is** the one this file puts on its source, over `X`.
* **Nothing about the number of sheets.**
  `ComplexAnalytic.AnalyticSpace.card_fiber_eq_of_isFiniteEtale` in
  `Oka/AnalyticSpace/CoveringMap.lean` is that statement, over a preconnected base — but it is
  **not** free for the morphism below, and two things stand in the way. It asks `[T2Space]` of the
  *source*, which is Mathlib's hypothesis, used to separate the finitely many points of a fibre,
  and is exactly the separation axiom this direction otherwise does without; `E` is arbitrary
  here, so there is nothing to synthesise. And
  `ComplexAnalytic.AnalyticSpace.isFiniteEtale_coveringSpaceHom` is a theorem rather than an
  instance, so it has to be supplied by hand. A caller holding `[T2Space E]` gets the statement by
  carrying that instance across the carrier seam with `inferInstanceAs` and supplying the
  finite-étale one; a caller without one does not get it at all. The same barrier stands one file
  further on: `ComplexAnalytic.AnalyticSpace.degree_eq_card_fiber` in
  `Oka/AnalyticSpace/Degree.lean`, which is where a reader looking for the number of sheets *as a
  number* will land, asks `[T2Space]` of the source for the same reason and through the same
  lemma. Nothing below states either.
* **No sections of `p⁻¹𝒪_X`.** No formula is proved for the sections over an open set, here or in
  either file below — over a sheet the *space* is identified with the base and that is strictly
  weaker than a formula, which is all a chart needs.
* **The converse is no longer absent either, and the same bullet says what still is.** A morphism
  of analytic spaces that is finite étale has a covering map for its underlying map
  (`Oka/AnalyticSpace/CoveringMap.lean`, which needs `[T2Space]`), and the structure its source
  carries is now identified with the one built here by
  `ComplexAnalytic.AnalyticSpace.exists_iso_coveringSpace` — which needs no separation axiom,
  since it reads only `ComplexAnalytic.AnalyticSpace.IsLocalIso`. What is **not** here is the
  round trip as an equivalence: no functor either way, no naturality, and nothing about morphisms
  of covers.

## References

- [Hans Grauert and Reinhold Remmert, *Coherent analytic sheaves*][grauert-remmert1984]
-/

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry TopCat Topology

universe u

noncomputable section

namespace ComplexAnalytic

variable (X : AnalyticSpace.{u}) {E : TopCat.{u}} (p : E ⟶ X.toLocallyRingedSpace.toTopCat)

/-- **The `ℂ`-algebra structure on the inverse image**: `X`'s structure pulled back along
`AlgebraicGeometry.LocallyRingedSpace.inverseImageHom`.

There is no choice in it and nothing to glue. `inverseImageHom` is defined on the whole of
`p⁻¹X`, so pulling back along it lands in **global** sections, which is where a
`ComplexAnalytic.AnalyticSpace`'s structure lives; the sheet-by-sheet structures of
`ComplexAnalytic.comapAlgMap_sheetHom` are this one restricted, and not the other way round. See
the module docstring on why that ordering is what makes the construction short. -/
def inverseImageAlgMap :
    ℂ →+* (X.toLocallyRingedSpace.inverseImage p).presheaf.obj (op ⊤) :=
  LocallyRingedSpace.comapAlgMap (X.toLocallyRingedSpace.inverseImageHom p) X.algebraMap

/-- **The inverse image of a complex analytic space along a local homeomorphism has local
models.**

`ComplexAnalytic.HasLocalModels.of_iSup_eq_top` over the sheets of `p`, which cover by
`IsLocalHomeomorph.sSup_sheetOpens`. On one sheet the chart is `X`'s own chart on the image open
`p '' V`, carried back by `ComplexAnalytic.HasLocalModels.of_iso` along
`AlgebraicGeometry.LocallyRingedSpace.sheetIso`, whose `ℂ`-linearity is
`ComplexAnalytic.isCLinearHom_comapAlgMap` — true by definition once
`AlgebraicGeometry.LocallyRingedSpace.sheetIso_hom` has rewritten the goal.
`ComplexAnalytic.comapAlgMap_sheetHom` is what turns the structure that produces into the
restriction of `ComplexAnalytic.inverseImageAlgMap`, which is the spelling the hypothesis of
`of_iSup_eq_top` is written in, and it is the step that consumes
`ComplexAnalytic.isCLinearHom_sheetHom`.

Only a local homeomorphism is needed — not a covering map, and no finiteness. -/
theorem hasLocalModels_inverseImage (hp : IsLocalHomeomorph ⇑p) :
    HasLocalModels (X.toLocallyRingedSpace.inverseImage p) (inverseImageAlgMap X p) := by
  refine HasLocalModels.of_iSup_eq_top
    (U := fun V : ↥(sheetOpens ⇑p) ↦ (V : Opens E)) ?_ ?_
  · -- The carrier of `p⁻¹X` is `E` on the nose, but the two spellings of `Opens` are not
    -- syntactically equal, so the supremum is taken at the `E` one and `change` crosses the seam.
    -- `change` and not `show`: `linter.style.show` together with `--wfail` makes `show` a build
    -- error whenever it moves the goal, which is the whole job here.
    change (⨆ V : ↥(sheetOpens ⇑p), (V : Opens E)) = ⊤
    rw [← sSup_eq_iSup']
    exact hp.sSup_sheetOpens
  · rintro ⟨V, hV⟩
    have hV' : IsOpenEmbedding fun x : V ↦ p x := hV
    have key : HasLocalModels
        ((X.toLocallyRingedSpace.inverseImage p).restrict V.isOpenEmbedding)
        (LocallyRingedSpace.comapAlgMap
          (LocallyRingedSpace.sheetHom X.toLocallyRingedSpace p V hV')
          (X.toLocallyRingedSpace.resAlgMap X.algebraMap
            (LocallyRingedSpace.sheetImage X.toLocallyRingedSpace p V hV'))) := by
      refine HasLocalModels.of_iso
        (LocallyRingedSpace.sheetIso X.toLocallyRingedSpace p V hV') ?_
        (X.hasLocalModels.restrict _)
      rw [LocallyRingedSpace.sheetIso_hom]
      exact isCLinearHom_comapAlgMap _ _
    rwa [comapAlgMap_sheetHom] at key

/-- **The complex analytic space on the source of a local homeomorphism into a complex analytic
space.**

The underlying topological space is `E` on the nose
(`AlgebraicGeometry.LocallyRingedSpace.inverseImage_toTopCat`), the structure sheaf is `p⁻¹𝒪_X`,
and the `ℂ`-algebra structure is `ComplexAnalytic.inverseImageAlgMap`. The hypothesis is a local
homeomorphism and nothing more; a covering map and finite fibres are what make the morphism below
*finite étale* and are not needed for the space to exist. -/
def AnalyticSpace.coveringSpace (hp : IsLocalHomeomorph ⇑p) : AnalyticSpace.{u} :=
  AnalyticSpace.ofHasLocalModels _ _ (hasLocalModels_inverseImage X p hp)

@[simp]
theorem AnalyticSpace.coveringSpace_toLocallyRingedSpace (hp : IsLocalHomeomorph ⇑p) :
    (AnalyticSpace.coveringSpace X p hp).toLocallyRingedSpace =
      X.toLocallyRingedSpace.inverseImage p :=
  rfl

/-- **The morphism of complex analytic spaces carrying a local homeomorphism.**

`AlgebraicGeometry.LocallyRingedSpace.inverseImageHom` with its `ℂ`-linearity, which is
`ComplexAnalytic.isCLinearHom_comapAlgMap` and holds **by definition**: the structure on the
source is the pullback of the structure on the target along this very morphism. -/
def AnalyticSpace.coveringSpaceHom (hp : IsLocalHomeomorph ⇑p) :
    AnalyticSpace.coveringSpace X p hp ⟶ X :=
  ⟨X.toLocallyRingedSpace.inverseImageHom p, isCLinearHom_comapAlgMap _ _⟩

/-- **The underlying map of `ComplexAnalytic.AnalyticSpace.coveringSpaceHom` is `p`**, on the
nose. -/
@[simp]
theorem AnalyticSpace.base_coveringSpaceHom (hp : IsLocalHomeomorph ⇑p) :
    (AnalyticSpace.coveringSpaceHom X p hp).toLRSHom.base = p :=
  rfl

/-- **A local homeomorphism into a complex analytic space is a local isomorphism** for the
structure `ComplexAnalytic.AnalyticSpace.coveringSpace` puts on its source.

Both fields are free. The topological one is the hypothesis, since the underlying map is `p`; the
stalk one is `AlgebraicGeometry.LocallyRingedSpace.isIso_stalkMap_inverseImageHom`, which holds
for an **arbitrary** continuous map — the stalk of the inverse image at `e` is the stalk of `X` at
`p e` and the stalk map is that identification. So no hypothesis on `p` is used for the stalk
half, and in particular this is not where a covering map would be needed. -/
instance AnalyticSpace.isLocalIso_coveringSpaceHom (hp : IsLocalHomeomorph ⇑p) :
    IsLocalIso (AnalyticSpace.coveringSpaceHom X p hp) where
  isLocalHomeomorph := hp
  isIso_stalkMap _ := LocallyRingedSpace.isIso_stalkMap_inverseImageHom _ _ _

/-- **A closed local homeomorphism with finite fibres into a complex analytic space is finite**
for this structure.

Both fields are handed over: `ComplexAnalytic.AnalyticSpace.IsFinite` is *closed base map* and
*finite fibres*, the base map is `p` on the nose, and the fibre hypothesis is transported to the
class `Finite` by `Set.Finite.to_subtype`. **Nothing is proved here.** -/
theorem AnalyticSpace.isFinite_coveringSpaceHom_of_isClosedMap (hp : IsLocalHomeomorph ⇑p)
    (hcl : IsClosedMap ⇑p) (hfin : ∀ x : X, (⇑p ⁻¹' {x}).Finite) :
    IsFinite (AnalyticSpace.coveringSpaceHom X p hp) where
  isClosedMap := hcl
  finite_fiber y := (hfin y).to_subtype

/-- **A covering map with finite fibres into a complex analytic space is finite** for this
structure.

`IsCoveringMap.isClosedMap` is the whole of the difference from
`ComplexAnalytic.AnalyticSpace.isFinite_coveringSpaceHom_of_isClosedMap`, and this declaration
together with `ComplexAnalytic.AnalyticSpace.isFiniteEtale_coveringSpaceHom` are the only two in
this file whose statement mentions a covering map. -/
theorem AnalyticSpace.isFinite_coveringSpaceHom (hcov : IsCoveringMap ⇑p)
    (hfin : ∀ x : X, (⇑p ⁻¹' {x}).Finite) :
    IsFinite (AnalyticSpace.coveringSpaceHom X p hcov.isLocalHomeomorph) :=
  AnalyticSpace.isFinite_coveringSpaceHom_of_isClosedMap X p _ (hcov.isClosedMap hfin) hfin

/-- **A closed local homeomorphism with finite fibres into a complex analytic space is finite
étale** for the structure `ComplexAnalytic.AnalyticSpace.coveringSpace` puts on its source.

Neither field needs the map to be a covering map: the local-isomorphism half is
`ComplexAnalytic.AnalyticSpace.isLocalIso_coveringSpaceHom`, which reads the hypothesis and an
instance holding for an arbitrary continuous map, and the finite half is the closedness
hypothesis together with the fibres. `Oka/AnalyticSpace/CoveringMap.lean` is the converse at the
level of the underlying map, and needs a separation axiom that this direction does not. -/
theorem AnalyticSpace.isFiniteEtale_coveringSpaceHom_of_isClosedMap (hp : IsLocalHomeomorph ⇑p)
    (hcl : IsClosedMap ⇑p) (hfin : ∀ x : X, (⇑p ⁻¹' {x}).Finite) :
    IsFiniteEtale (AnalyticSpace.coveringSpaceHom X p hp) where
  isFinite := AnalyticSpace.isFinite_coveringSpaceHom_of_isClosedMap X p hp hcl hfin
  isLocalIso := inferInstance

/-- **A covering map with finite fibres into a complex analytic space is finite étale** for the
structure `ComplexAnalytic.AnalyticSpace.coveringSpace` puts on its source.

This is the statement the Riemann existence theorem's analytic side needs: a topological covering
of an analytic space, with finite fibres, *is* an object of the category of finite étale covers. -/
theorem AnalyticSpace.isFiniteEtale_coveringSpaceHom (hcov : IsCoveringMap ⇑p)
    (hfin : ∀ x : X, (⇑p ⁻¹' {x}).Finite) :
    IsFiniteEtale (AnalyticSpace.coveringSpaceHom X p hcov.isLocalHomeomorph) :=
  AnalyticSpace.isFiniteEtale_coveringSpaceHom_of_isClosedMap X p _ (hcov.isClosedMap hfin) hfin

/-! ### Uniqueness: a local isomorphism is this construction at its own base map -/

section Uniqueness

variable {X E' : AnalyticSpace.{u}} (q : E' ⟶ X) [hq : AnalyticSpace.IsLocalIso q]

/-- **The comparison morphism** from the source of a local isomorphism `q` to the covering space
built on `q`'s own base map.

It is `AlgebraicGeometry.LocallyRingedSpace.toInverseImage` together with a proof of
`ComplexAnalytic.IsCLinearHom`, and that proof is `ComplexAnalytic.IsCLinearHom.of_comp` at the
factorisation `AlgebraicGeometry.LocallyRingedSpace.toInverseImage_comp`: the structure on the
target is the pullback of `X`'s along `ComplexAnalytic.AnalyticSpace.coveringSpaceHom`, so the two
inputs are `q`'s own linearity and `ComplexAnalytic.isCLinearHom_comapAlgMap`, which holds by
definition.

Nothing here is transported. The target's underlying locally ringed space is
`X.toLocallyRingedSpace.inverseImage q.toLRSHom.base` by `rfl`
(`ComplexAnalytic.AnalyticSpace.coveringSpace_toLocallyRingedSpace`), so the field is literally a
morphism into it. -/
def AnalyticSpace.toCoveringSpace :
    E' ⟶ AnalyticSpace.coveringSpace X q.toLRSHom.base hq.isLocalHomeomorph :=
  ⟨LocallyRingedSpace.toInverseImage q.toLRSHom,
    IsCLinearHom.of_comp (LocallyRingedSpace.toInverseImage_comp q.toLRSHom) q.isCLinear
      (isCLinearHom_comapAlgMap _ _)⟩

/-- **The underlying morphism of locally ringed spaces of the comparison morphism** is
`AlgebraicGeometry.LocallyRingedSpace.toInverseImage`, on the nose. -/
@[simp]
theorem AnalyticSpace.toLRSHom_toCoveringSpace :
    (AnalyticSpace.toCoveringSpace q).toLRSHom = LocallyRingedSpace.toInverseImage q.toLRSHom :=
  rfl

/-- **The underlying map of the comparison morphism is the identity**, on the nose — which is what
makes the uniqueness statement below an identification of `E'` itself and not of a homeomorphic
copy of it. -/
@[simp]
theorem AnalyticSpace.base_toCoveringSpace :
    (AnalyticSpace.toCoveringSpace q).toLRSHom.base = 𝟙 E'.toLocallyRingedSpace.toTopCat :=
  rfl

/-- **The comparison morphism is a morphism over `X`.**

`AlgebraicGeometry.LocallyRingedSpace.toInverseImage_comp` verbatim, pushed across the faithful
`ComplexAnalytic.AnalyticSpace.forgetToLocallyRingedSpace`: an equation between morphisms of
analytic spaces is an equation between their underlying morphisms, and the `ℂ`-linearity fields
are proofs. -/
theorem AnalyticSpace.toCoveringSpace_comp :
    AnalyticSpace.toCoveringSpace q ≫
        AnalyticSpace.coveringSpaceHom X q.toLRSHom.base hq.isLocalHomeomorph = q :=
  AnalyticSpace.forgetToLocallyRingedSpace.map_injective
    (LocallyRingedSpace.toInverseImage_comp q.toLRSHom)

set_option backward.isDefEq.respectTransparency false in
/-- **The comparison morphism is an isomorphism of complex analytic spaces.**

`AlgebraicGeometry.LocallyRingedSpace.isIso_toInverseImage` is the locally-ringed-space half and
consumes only the stalk field of `ComplexAnalytic.AnalyticSpace.IsLocalIso`; the topological field
is not used here at all, being spent instead on naming the target — see the module docstring.

**The inverse's `ℂ`-linearity is a separate obligation and is the content of this instance.** The
subcategory is not full, so the inverse handed back downstairs is a morphism of locally ringed
spaces and nothing more; `ComplexAnalytic.IsCLinearHom.of_comp` applied at
`CategoryTheory.IsIso.inv_hom_id` supplies it, with
`ComplexAnalytic.IsCLinearHom.id` for the composite. The two triangle identities are then their
locally-ringed-space counterparts, by faithfulness.

**The `set_option` is load-bearing and was tested by deletion.** Without it the `inv` in the term
below fails to find its `IsIso` instance: the expected type spells the source as
`(ComplexAnalytic.AnalyticSpace.coveringSpace …).toLocallyRingedSpace` while the hypothesis spells
it as `AlgebraicGeometry.LocallyRingedSpace.inverseImage …`, and
`ComplexAnalytic.AnalyticSpace.coveringSpace_toLocallyRingedSpace` bridging them is `rfl` at
default transparency only, where instance search runs at reducible.
`AlgebraicGeometry.LocallyRingedSpace.isIso_toInverseImage` itself needs no such option, because
no term in it crosses that seam. -/
instance AnalyticSpace.isIso_toCoveringSpace : IsIso (AnalyticSpace.toCoveringSpace q) := by
  haveI : IsIso (LocallyRingedSpace.toInverseImage q.toLRSHom) :=
    LocallyRingedSpace.isIso_toInverseImage q.toLRSHom fun z ↦
      AnalyticSpace.IsLocalIso.isIso_stalkMap z
  refine ⟨⟨CategoryTheory.inv (LocallyRingedSpace.toInverseImage q.toLRSHom), ?_⟩, ?_, ?_⟩
  · exact IsCLinearHom.of_comp (CategoryTheory.IsIso.inv_hom_id _) (IsCLinearHom.id _)
      (AnalyticSpace.toCoveringSpace q).isCLinear
  · exact AnalyticSpace.forgetToLocallyRingedSpace.map_injective
      (CategoryTheory.IsIso.hom_inv_id (LocallyRingedSpace.toInverseImage q.toLRSHom))
  · exact AnalyticSpace.forgetToLocallyRingedSpace.map_injective
      (CategoryTheory.IsIso.inv_hom_id (LocallyRingedSpace.toInverseImage q.toLRSHom))

/-- **The isomorphism the comparison morphism is**, as a `CategoryTheory.Iso`.

`CategoryTheory.asIso` of the instance above, so its `hom` field is
`ComplexAnalytic.AnalyticSpace.toCoveringSpace` by definition and
`ComplexAnalytic.AnalyticSpace.toCoveringSpace_comp` applies to it unchanged. -/
def AnalyticSpace.coveringSpaceIso :
    E' ≅ AnalyticSpace.coveringSpace X q.toLRSHom.base hq.isLocalHomeomorph :=
  asIso (AnalyticSpace.toCoveringSpace q)

/-- **Uniqueness of the analytic structure on a covering space**: a morphism of complex analytic
spaces which is a local isomorphism is *this file's construction*, at its own base map, over its
own target.

Neither `p` nor a hypothesis on it appears: both are read off `q`, which is what removes the
transport a statement quantified over structures on a fixed carrier would carry. The second
component is what makes it a statement over `X` and not merely about the two spaces; without it
the isomorphism would say nothing about the maps. -/
theorem AnalyticSpace.exists_iso_coveringSpace :
    ∃ e : E' ≅ AnalyticSpace.coveringSpace X q.toLRSHom.base hq.isLocalHomeomorph,
      e.hom ≫ AnalyticSpace.coveringSpaceHom X q.toLRSHom.base hq.isLocalHomeomorph = q :=
  ⟨AnalyticSpace.coveringSpaceIso q, AnalyticSpace.toCoveringSpace_comp q⟩

end Uniqueness

end ComplexAnalytic

end
