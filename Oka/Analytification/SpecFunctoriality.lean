/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Analytification.SpecAffineCover

/-!
# A morphism of covered schemes on the `Spec` side

`Oka/Analytification/SpecAffineCover.lean` glues the members' `Spec`s into `X`, and
`Oka/Analytification/CoverFunctoriality.lean` builds `X^an ⟶ Y^an` from a map of index types and
a morphism of presentations over it. **This file is the same construction on the other side**:
the same input gives `X ⟶ Y`, with the identity and composition laws.

## It is the analytic file with the promotion step removed

**Every declaration here that has a counterpart in `Oka/Analytification/CoverFunctoriality.lean`**
is that counterpart with `ComplexAnalytic.specFunctor` where that file has
`ComplexAnalytic.analytificationFunctor`, and every difference between a pair is a *subtraction*:

* **No `ComplexAnalytic.AnalyticSpace.Hom.toLRSHom` anywhere.** The analytic file states its
  compatibility hypothesis at the locally-ringed-space level because
  `ComplexAnalytic.coverGlueMorphisms` does, and then has to push its family through the
  forgetful functor. `X` is a locally ringed space to begin with, so the whole file works at one
  level — the same saving `Oka/Analytification/SpecAffineCover.lean` records about itself.
* **No wrapper around `AlgebraicGeometry.LocallyRingedSpace.GlueData.glueMorphisms`.**
  `ComplexAnalytic.coverGlueMorphisms` exists because a glued locally ringed space has to be
  promoted into an analytic space and the glued morphism has to be shown `ℂ`-linear;
  `ComplexAnalytic.specGlued` **is** the glue datum's gluing, so `glueMorphisms` and
  `AlgebraicGeometry.LocallyRingedSpace.GlueData.hom_ext` apply to it directly and
  `ComplexAnalytic.specMap_unique` is one line.

**The qualification is carrying exactly one declaration, and the count says so: nine here against
eight there.** The extra is `ComplexAnalytic.comm_specGlueData`, which is an addition and not a
mirror, and the next section is about where its counterpart does live.

## `ComplexAnalytic.comm_specGlueData` is here and not in `Oka/Analytification/SpecAffineCover.lean`

Its analytic mirror `ComplexAnalytic.comm_coverGlueData` lives in
`Oka/Analytification/AffineCover.lean`, under that file's `### Morphisms out of \`X^an\`` heading —
and `Oka/Analytification/SpecAffineCover.lean` deliberately mirrors only the *first* half of that
file, saying in terms that the second half exists to promote a gluing into an analytic space and
so does not transfer. Nothing there needed a family out of the members. **This file is the first
thing that does**, so the bridge from the compatibility a caller can state to the one a glue
datum's `glue_condition` has belongs here, beside its only consumer.

## The input, and why the compatibility is a hypothesis

Unchanged from the analytic side, and for the same reason: nothing in a map of index types and a
family of morphisms of presentations implies that the members agree over the overlaps of `X`. A
morphism of schemes need not carry one cover into the other, and even when it does, which member
of the target's cover an overlap of the source lands in is a choice `σ` does not record.
`ComplexAnalytic.comm_specMapPart_id` discharges the hypothesis for the identity data, so it is
meetable; `ComplexAnalytic.comm_specMapPart_comp` discharges it for a composite, so the
composition law asks a caller for nothing beyond the two hypotheses its two morphisms carry.

## Main definitions

- `ComplexAnalytic.specMapPart`: the `i`-th member's contribution, `Spec A_i ⟶ Y`.
- `ComplexAnalytic.specMap`: **the induced morphism `X ⟶ Y`.**

## Main results

- `ComplexAnalytic.comm_specGlueData`: **agreement over the chosen overlaps is the glue datum's
  compatibility condition**, which is what makes everything below statable.
- `ComplexAnalytic.specIota_comp_specMap`: **it restricts to `Spec` of the member morphism on each
  member.** It is the only statement here *about `ComplexAnalytic.specMap`* with independent
  content: `ComplexAnalytic.specMap_unique` is it plus
  `AlgebraicGeometry.LocallyRingedSpace.GlueData.hom_ext`, and both laws below are derived from
  that. **The claim is about the statements and not about a hypothetical definition ignoring `ψ`**,
  which is a counterfactual nobody on this line of work has exhibited a member of.
- `ComplexAnalytic.specMap_unique`: **and it is the only morphism that does.**
- `ComplexAnalytic.comm_specMapPart_id` and `ComplexAnalytic.comm_specMapPart_comp`: the
  compatibility hypothesis, discharged for the identity data and for a composite.
- `ComplexAnalytic.specMap_id` and `ComplexAnalytic.specMap_comp`: **the two functor laws.**

## What is not here

* **No functor.** As in `Oka/Analytification/CoverFunctoriality.lean`: there is no category of
  covered schemes in this repository to be a functor out of, since two covers of the same scheme
  are different inputs with no morphism between them until cover independence exists. The two
  laws below are the content a functor instance would carry.
* **No non-identity instance.** Nothing below exhibits a `σ` and a `ψ` other than the identity.
  The identity law is the only control here — the same gap the analytic file records, and for the
  same reason.
* **No square against the comparison morphism.** That
  `ComplexAnalytic.analytificationToSpecGlued` intertwines `ComplexAnalytic.coverMap` with
  `ComplexAnalytic.specMap` is `Oka/Analytification/ComparisonSquare.lean`, which imports this
  file and both of the others. It is not here because it needs the analytic morphism as well, and
  nothing in this file mentions an analytic space — **and keeping the two apart is what makes
  `ComplexAnalytic.specMap` cheap to consume**. Measured from `env.header.moduleNames` under
  `lake env lean`: this file costs `5137` modules, `84` of them `Oka`'s and `3303` `Mathlib`'s,
  which is `Oka/Analytification/SpecAffineCover.lean` plus itself and no `Mathlib` module at all.
  The square costs `5140 / 87 / 3303`. A reader who wants `X ⟶ Y` and not the comparison would
  pay those three extra modules if the two lived together, and one of them is the whole analytic
  comparison.
* **Nothing about `AlgebraicGeometry.Scheme`.** `ComplexAnalytic.specFunctor` lands in
  `AlgebraicGeometry.LocallyRingedSpace` and so does everything below. **The referent of the
  second half moved on 2026-09-02**: `Oka/Analytification/SpecAffineCover.lean` no longer argues
  that the absence is a result, because `Oka/Analytification/SpecScheme.lean` promotes its gluing
  to a scheme; what that file's bullet now says is where the scheme is and that it is not in
  either of these two modules. `Oka/Analytification/Comparison.lean`'s titled section is the
  argument both bullets ultimately point at, and it is about *its* statements and is untouched.
-/

open CategoryTheory TopologicalSpace AlgebraicGeometry

universe u

namespace ComplexAnalytic

noncomputable section

variable {J K : Type u} (obj : J → Presentation.{u})
  (poly : ∀ i : J, J → MvPolynomial (ULift.{u} (Fin (obj i).n)) ℂ)
  (glue : ∀ i j : J, coverOverlap.{u} obj poly i j ≅ coverOverlap.{u} obj poly j i)
  (hrange : ∀ i j k : J, i ≠ j → i ≠ k → j ≠ k →
    Set.range (specTripleIncl.{u} obj poly i j k ≫
        specTransitionHom.{u} obj poly glue i j).base ⊆
      (specOpen.{u} obj poly j k : Set (specSpace.{u} obj j)))
  (hsymm : ∀ i j : J, glue j i = (glue i j).symm)
  (hcocycle : ∀ i j k : J, ∀ hij : i ≠ j, ∀ hik : i ≠ k, ∀ hjk : j ≠ k,
    specTriple.{u} obj poly glue hrange i j k hij hik hjk ≫
      specTriple.{u} obj poly glue hrange j k i hjk hij.symm hik.symm ≫
      specTriple.{u} obj poly glue hrange k i j hik.symm hjk.symm hij = 𝟙 _)

/-! ### The compatibility condition -/

/-- **A family of morphisms out of the members which agrees over the chosen overlaps satisfies the
glue datum's compatibility condition.**

`CategoryTheory.GlueData.ofGlueData'_comm` at `ComplexAnalytic.specGlueData'`, and the mirror of
`ComplexAnalytic.comm_coverGlueData`. The hypothesis is at `i ≠ j` and the conclusion at every
pair: `ComplexAnalytic.specGlueData`'s diagonal is `CategoryTheory.GlueData.ofGlueData'`'s
`eqToHom`s and not `ComplexAnalytic.specTransition i i`, so there is nothing there for a caller to
check.

Do not try to derive this from `CategoryTheory.GlueData.glue_condition` by hand.
`Oka/CategoryTheory/GlueData.lean`'s module docstring is about why that fails, and
`ComplexAnalytic.specIncl_comp_specIota` — which reads it back the other way — was written after
four such derivations across two sessions had run into it. -/
theorem comm_specGlueData {Y : LocallyRingedSpace.{u}} (f : ∀ i, specSpace.{u} obj i ⟶ Y)
    (h : ∀ i j : J, i ≠ j → specIncl.{u} obj poly i j ≫ f i =
      (specTransition.{u} obj poly glue i j).hom ≫ specIncl.{u} obj poly j i ≫ f j) (i j : J) :
    (specGlueData.{u} obj poly glue hrange hsymm hcocycle).f i j ≫ f i =
      (specGlueData.{u} obj poly glue hrange hsymm hcocycle).t i j ≫
        (specGlueData.{u} obj poly glue hrange hsymm hcocycle).f j i ≫ f j :=
  CategoryTheory.GlueData.ofGlueData'_comm
    (specGlueData'.{u} obj poly glue hrange hsymm hcocycle) f (fun i j hij ↦ h i j hij) i j

/-! ### The morphism -/

variable (obj' : K → Presentation.{u})
  (poly' : ∀ i : K, K → MvPolynomial (ULift.{u} (Fin (obj' i).n)) ℂ)
  (glue' : ∀ i j : K, coverOverlap.{u} obj' poly' i j ≅ coverOverlap.{u} obj' poly' j i)
  (hrange' : ∀ i j k : K, i ≠ j → i ≠ k → j ≠ k →
    Set.range (specTripleIncl.{u} obj' poly' i j k ≫
        specTransitionHom.{u} obj' poly' glue' i j).base ⊆
      (specOpen.{u} obj' poly' j k : Set (specSpace.{u} obj' j)))
  (hsymm' : ∀ i j : K, glue' j i = (glue' i j).symm)
  (hcocycle' : ∀ i j k : K, ∀ hij : i ≠ j, ∀ hik : i ≠ k, ∀ hjk : j ≠ k,
    specTriple.{u} obj' poly' glue' hrange' i j k hij hik hjk ≫
      specTriple.{u} obj' poly' glue' hrange' j k i hjk hij.symm hik.symm ≫
      specTriple.{u} obj' poly' glue' hrange' k i j hik.symm hjk.symm hij = 𝟙 _)
  (σ : J → K) (ψ : ∀ i : J, obj i ⟶ obj' (σ i))

/-- **The `i`-th member's contribution**, `Spec A_i ⟶ Y`: `Spec` of the member morphism followed
by the inclusion of the member of `Y` it lands in.

The mirror of `ComplexAnalytic.coverMapPart`. Note the direction: a `ComplexAnalytic.PresHom`'s
ring map runs backwards, so `ψ i` is a morphism of presented algebras `A'_{σ i} ⟶ A_i` and
`ComplexAnalytic.specFunctor.map (ψ i)` runs `Spec A_i ⟶ Spec A'_{σ i}`, which is the geometric
direction. -/
abbrev specMapPart (i : J) :
    specSpace.{u} obj i ⟶ specGlued.{u} obj' poly' glue' hrange' hsymm' hcocycle' :=
  specFunctor.{u}.map (ψ i) ≫ specIota.{u} obj' poly' glue' hrange' hsymm' hcocycle' (σ i)

variable (hcomm : ∀ i j : J, i ≠ j →
  specIncl.{u} obj poly i j ≫
      specMapPart.{u} obj obj' poly' glue' hrange' hsymm' hcocycle' σ ψ i =
    (specTransition.{u} obj poly glue i j).hom ≫ specIncl.{u} obj poly j i ≫
      specMapPart.{u} obj obj' poly' glue' hrange' hsymm' hcocycle' σ ψ j)

/-- **The induced morphism `X ⟶ Y`.**

`AlgebraicGeometry.LocallyRingedSpace.GlueData.glueMorphisms` at the family above, whose overlap
hypothesis is `ComplexAnalytic.comm_specGlueData`. There is no analogue here of
`ComplexAnalytic.coverGlueMorphisms`: that declaration exists to promote a glued locally ringed
space into an analytic space and to carry a `ℂ`-linearity proof, and `ComplexAnalytic.specGlued`
needs neither. -/
def specMap :
    specGlued.{u} obj poly glue hrange hsymm hcocycle ⟶
      specGlued.{u} obj' poly' glue' hrange' hsymm' hcocycle' :=
  LocallyRingedSpace.GlueData.glueMorphisms
    (specGlueData.{u} obj poly glue hrange hsymm hcocycle)
    (specMapPart.{u} obj obj' poly' glue' hrange' hsymm' hcocycle' σ ψ)
    (comm_specGlueData.{u} obj poly glue hrange hsymm hcocycle _ hcomm)

/-- **It restricts to `Spec` of the member morphism on each member.**

`AlgebraicGeometry.LocallyRingedSpace.GlueData.ι_glueMorphisms`, stated at
`ComplexAnalytic.specIota` — which is that `ι`, by `rfl`, so no transport is needed and the
`ComplexAnalytic.toLRSHom_coverIota` step the analytic mirror takes has no counterpart here.

**This is the statement about `ComplexAnalytic.specMap` with independent content**, and the claim
is meant no wider than it says: `ComplexAnalytic.specMap_unique` is this lemma plus
`AlgebraicGeometry.LocallyRingedSpace.GlueData.hom_ext`, and both laws below are that, so a reader
who wants to know that `ComplexAnalytic.specMap` is built out of `ψ` at all need read only this
one. `ComplexAnalytic.comm_specMapPart_id` is *not* covered by that claim — it is about
`ComplexAnalytic.specMapPart` at the identity data and never mentions
`ComplexAnalytic.specMap`. -/
@[reassoc (attr := simp)]
theorem specIota_comp_specMap (i : J) :
    specIota.{u} obj poly glue hrange hsymm hcocycle i ≫
        specMap.{u} obj poly glue hrange hsymm hcocycle obj' poly' glue' hrange' hsymm'
          hcocycle' σ ψ hcomm =
      specFunctor.{u}.map (ψ i) ≫
        specIota.{u} obj' poly' glue' hrange' hsymm' hcocycle' (σ i) :=
  LocallyRingedSpace.GlueData.ι_glueMorphisms
    (specGlueData.{u} obj poly glue hrange hsymm hcocycle) _ _ i

/-- **And it is the only morphism that restricts that way**, by
`AlgebraicGeometry.LocallyRingedSpace.GlueData.hom_ext`.

Both laws below are corollaries of this: the identity and the composite are *exhibited* as
morphisms with the right restrictions, so neither proof touches a glue datum. That is the analytic
file's design and it survives the substitution unchanged. -/
theorem specMap_unique
    (φ : specGlued.{u} obj poly glue hrange hsymm hcocycle ⟶
      specGlued.{u} obj' poly' glue' hrange' hsymm' hcocycle')
    (h : ∀ i, specIota.{u} obj poly glue hrange hsymm hcocycle i ≫ φ =
      specFunctor.{u}.map (ψ i) ≫
        specIota.{u} obj' poly' glue' hrange' hsymm' hcocycle' (σ i)) :
    φ = specMap.{u} obj poly glue hrange hsymm hcocycle obj' poly' glue' hrange' hsymm'
      hcocycle' σ ψ hcomm :=
  LocallyRingedSpace.GlueData.hom_ext
    (specGlueData.{u} obj poly glue hrange hsymm hcocycle) _ _ fun i ↦
      (h i).trans (specIota_comp_specMap.{u} obj poly glue hrange hsymm hcocycle obj' poly'
        glue' hrange' hsymm' hcocycle' σ ψ hcomm i).symm

/-! ### The identity -/

/-- **The compatibility hypothesis, discharged for the identity data** — `σ = id` and `ψ = 𝟙`.

It is `ComplexAnalytic.specIncl_comp_specIota`, the glue datum's own `glue_condition` read back
into this file's vocabulary, after the functor law kills the identity. Its existence is what says
the hypothesis of `ComplexAnalytic.specMap` is meetable at all. -/
theorem comm_specMapPart_id (i j : J) (hij : i ≠ j) :
    specIncl.{u} obj poly i j ≫
        specMapPart.{u} obj obj poly glue hrange hsymm hcocycle id (fun i ↦ 𝟙 (obj i)) i =
      (specTransition.{u} obj poly glue i j).hom ≫ specIncl.{u} obj poly j i ≫
        specMapPart.{u} obj obj poly glue hrange hsymm hcocycle id (fun i ↦ 𝟙 (obj i)) j := by
  simpa [specMapPart] using
    specIncl_comp_specIota.{u} obj poly glue hrange hsymm hcocycle i j hij

/-- **The identity law**: the identity data induces the identity of `X`. -/
theorem specMap_id :
    specMap.{u} obj poly glue hrange hsymm hcocycle obj poly glue hrange hsymm hcocycle id
        (fun i ↦ 𝟙 (obj i)) (comm_specMapPart_id.{u} obj poly glue hrange hsymm hcocycle) =
      𝟙 _ :=
  (specMap_unique.{u} obj poly glue hrange hsymm hcocycle obj poly glue hrange hsymm hcocycle
    id (fun i ↦ 𝟙 (obj i)) _ (𝟙 _) (by simp)).symm

/-! ### Composition -/

variable {L : Type u} (obj'' : L → Presentation.{u})
  (poly'' : ∀ i : L, L → MvPolynomial (ULift.{u} (Fin (obj'' i).n)) ℂ)
  (glue'' : ∀ i j : L, coverOverlap.{u} obj'' poly'' i j ≅ coverOverlap.{u} obj'' poly'' j i)
  (hrange'' : ∀ i j k : L, i ≠ j → i ≠ k → j ≠ k →
    Set.range (specTripleIncl.{u} obj'' poly'' i j k ≫
        specTransitionHom.{u} obj'' poly'' glue'' i j).base ⊆
      (specOpen.{u} obj'' poly'' j k : Set (specSpace.{u} obj'' j)))
  (hsymm'' : ∀ i j : L, glue'' j i = (glue'' i j).symm)
  (hcocycle'' : ∀ i j k : L, ∀ hij : i ≠ j, ∀ hik : i ≠ k, ∀ hjk : j ≠ k,
    specTriple.{u} obj'' poly'' glue'' hrange'' i j k hij hik hjk ≫
      specTriple.{u} obj'' poly'' glue'' hrange'' j k i hjk hij.symm hik.symm ≫
      specTriple.{u} obj'' poly'' glue'' hrange'' k i j hik.symm hjk.symm hij = 𝟙 _)
  (τ : K → L) (χ : ∀ i : K, obj' i ⟶ obj'' (τ i))

variable (hcomm' : ∀ i j : K, i ≠ j →
  specIncl.{u} obj' poly' i j ≫
      specMapPart.{u} obj' obj'' poly'' glue'' hrange'' hsymm'' hcocycle'' τ χ i =
    (specTransition.{u} obj' poly' glue' i j).hom ≫ specIncl.{u} obj' poly' j i ≫
      specMapPart.{u} obj' obj'' poly'' glue'' hrange'' hsymm'' hcocycle'' τ χ j)

include hcomm hcomm' hrange' hsymm' hcocycle' in
/-- **The compatibility hypothesis, discharged for the composite data** — `τ ∘ σ` and
`fun i ↦ ψ i ≫ χ (σ i)`. So the composition law below asks a caller for nothing beyond the two
hypotheses its two morphisms already carry.

**The whole of it is that the composite's `i`-th part is the first map's `i`-th part followed by
the second morphism**, at every `i` and with no hypothesis at all:
`ComplexAnalytic.specMapPart` at the composite data is `specFunctor.map (ψ i ≫ χ (σ i))` followed
by the inclusion of the `τ (σ i)`-th member, the functor law splits the first factor, and
`ComplexAnalytic.specIota_comp_specMap` — which is `@[simp]` — folds the tail back into
`ComplexAnalytic.specMap`. Given that, the statement is `hcomm` postcomposed with one morphism,
which is what `reassoc_of%` does to it.

**The obstruction one expects here is not there, and it is worth naming which one.** `hcomm'` is
an equation at pairs `i ≠ j` of `K`, so a derivation that fed it the pair `(σ i, σ j)` would say
nothing whenever `σ i = σ j` — and nothing in the input forbids a cover map carrying two distinct
members of `X` into the same member of `Y`. **No such pair is ever formed.** `hcomm'` enters only
through `ComplexAnalytic.specMap`, which holds it whole, so nothing here splits on whether `σ` is
injective. The analytic mirror `ComplexAnalytic.comm_coverMapPart_comp` says the same, and the
first delivery of that file argued the opposite before it was measured. -/
theorem comm_specMapPart_comp (i j : J) (hij : i ≠ j) :
    specIncl.{u} obj poly i j ≫
        specMapPart.{u} obj obj'' poly'' glue'' hrange'' hsymm'' hcocycle'' (τ ∘ σ)
          (fun i ↦ ψ i ≫ χ (σ i)) i =
      (specTransition.{u} obj poly glue i j).hom ≫ specIncl.{u} obj poly j i ≫
        specMapPart.{u} obj obj'' poly'' glue'' hrange'' hsymm'' hcocycle'' (τ ∘ σ)
          (fun i ↦ ψ i ≫ χ (σ i)) j := by
  have key : ∀ a : J,
      specMapPart.{u} obj obj'' poly'' glue'' hrange'' hsymm'' hcocycle'' (τ ∘ σ)
          (fun i ↦ ψ i ≫ χ (σ i)) a =
        specMapPart.{u} obj obj' poly' glue' hrange' hsymm' hcocycle' σ ψ a ≫
          specMap.{u} obj' poly' glue' hrange' hsymm' hcocycle' obj'' poly'' glue'' hrange''
            hsymm'' hcocycle'' τ χ hcomm' := fun a ↦ by
    simp only [specMapPart, Functor.map_comp, Category.assoc, specIota_comp_specMap,
      Function.comp_apply]
  calc specIncl.{u} obj poly i j ≫
        specMapPart.{u} obj obj'' poly'' glue'' hrange'' hsymm'' hcocycle'' (τ ∘ σ)
          (fun i ↦ ψ i ≫ χ (σ i)) i
      = specIncl.{u} obj poly i j ≫
          specMapPart.{u} obj obj' poly' glue' hrange' hsymm' hcocycle' σ ψ i ≫
            specMap.{u} obj' poly' glue' hrange' hsymm' hcocycle' obj'' poly'' glue'' hrange''
              hsymm'' hcocycle'' τ χ hcomm' :=
        congrArg (specIncl.{u} obj poly i j ≫ ·) (key i)
    _ = (specIncl.{u} obj poly i j ≫
          specMapPart.{u} obj obj' poly' glue' hrange' hsymm' hcocycle' σ ψ i) ≫
            specMap.{u} obj' poly' glue' hrange' hsymm' hcocycle' obj'' poly'' glue'' hrange''
              hsymm'' hcocycle'' τ χ hcomm' := (Category.assoc _ _ _).symm
    _ = ((specTransition.{u} obj poly glue i j).hom ≫ specIncl.{u} obj poly j i ≫
          specMapPart.{u} obj obj' poly' glue' hrange' hsymm' hcocycle' σ ψ j) ≫
            specMap.{u} obj' poly' glue' hrange' hsymm' hcocycle' obj'' poly'' glue'' hrange''
              hsymm'' hcocycle'' τ χ hcomm' := congrArg (· ≫ _) (hcomm i j hij)
    _ = (specTransition.{u} obj poly glue i j).hom ≫ (specIncl.{u} obj poly j i ≫
          specMapPart.{u} obj obj' poly' glue' hrange' hsymm' hcocycle' σ ψ j) ≫
            specMap.{u} obj' poly' glue' hrange' hsymm' hcocycle' obj'' poly'' glue'' hrange''
              hsymm'' hcocycle'' τ χ hcomm' := Category.assoc _ _ _
    _ = (specTransition.{u} obj poly glue i j).hom ≫ specIncl.{u} obj poly j i ≫
          specMapPart.{u} obj obj' poly' glue' hrange' hsymm' hcocycle' σ ψ j ≫
            specMap.{u} obj' poly' glue' hrange' hsymm' hcocycle' obj'' poly'' glue'' hrange''
              hsymm'' hcocycle'' τ χ hcomm' :=
        congrArg ((specTransition.{u} obj poly glue i j).hom ≫ ·) (Category.assoc _ _ _)
    _ = (specTransition.{u} obj poly glue i j).hom ≫ specIncl.{u} obj poly j i ≫
          specMapPart.{u} obj obj'' poly'' glue'' hrange'' hsymm'' hcocycle'' (τ ∘ σ)
            (fun i ↦ ψ i ≫ χ (σ i)) j :=
        congrArg ((specTransition.{u} obj poly glue i j).hom ≫ specIncl.{u} obj poly j i ≫ ·)
          (key j).symm

/-- **The composition law.**

`ComplexAnalytic.specMap_unique` at the composite, whose own compatibility is
`ComplexAnalytic.comm_specMapPart_comp` rather than a hypothesis a caller has to supply.

**A caller holding some other proof of that compatibility loses nothing**: the two are proofs of
one `Prop`, so `ComplexAnalytic.specMap` cannot tell them apart and the equation stated here is
the equation they wanted. That is what makes naming a particular proof in the statement free. -/
theorem specMap_comp :
    specMap.{u} obj poly glue hrange hsymm hcocycle obj' poly' glue' hrange' hsymm' hcocycle'
        σ ψ hcomm ≫
      specMap.{u} obj' poly' glue' hrange' hsymm' hcocycle' obj'' poly'' glue'' hrange'' hsymm''
        hcocycle'' τ χ hcomm' =
    specMap.{u} obj poly glue hrange hsymm hcocycle obj'' poly'' glue'' hrange'' hsymm''
      hcocycle'' (τ ∘ σ) (fun i ↦ ψ i ≫ χ (σ i))
      (comm_specMapPart_comp.{u} obj poly glue obj' poly' glue' hrange' hsymm' hcocycle' σ ψ
        hcomm obj'' poly'' glue'' hrange'' hsymm'' hcocycle'' τ χ hcomm') :=
  specMap_unique.{u} obj poly glue hrange hsymm hcocycle obj'' poly'' glue'' hrange'' hsymm''
    hcocycle'' (τ ∘ σ) (fun i ↦ ψ i ≫ χ (σ i)) _ _ (by simp)

end

end ComplexAnalytic
