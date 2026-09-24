/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Analytification.AffineCover

/-!
# A morphism of covered schemes analytifies

`Oka/Analytification/AffineCover.lean` builds `X^an` from a cover as data — an index type, a
presentation for each index, a polynomial cutting out each overlap, and an isomorphism of the two
descriptions of each overlap — and gives it a morphism *out* of `X^an` glued from morphisms out of
the members. This file is the morphism *between* two of them: a map of index types, a morphism of
presentations over it, and the compatibility over overlaps, glued into `X^an ⟶ Y^an`, with the
identity and composition laws.

## The input, and why the compatibility is a hypothesis

The member-wise data is a map of index types `σ : J → K` and, for each `i`, a morphism of
presentations `ψ i : obj i ⟶ obj' (σ i)`. Note the direction: a `ComplexAnalytic.PresHom`'s ring
map runs backwards, so `ψ i` is a morphism of presented algebras `A'_{σ i} ⟶ A_i` and
`ComplexAnalytic.analytificationFunctor.map (ψ i)` runs `A_i^an ⟶ A'^an_{σ i}`, which is the
geometric direction a cover of `X` mapping into a cover of `Y` has.

**What the caller also has to supply is that the members agree over the overlaps of `X`, and that
is a hypothesis here rather than a consequence.** `ComplexAnalytic.coverGlueMorphisms` asks for
exactly it, at `i ≠ j`, and nothing in the input implies it: a morphism of schemes need not carry
one cover into the other at all, and even when it does, which member of the target's cover an
overlap of the source lands in is a choice `σ` does not record. This is the "state it as a
hypothesis and leave removing it to the cover-independence issue" that this construction's
specification asks for, and the honest price is that the hypothesis is *geometric* — an equation
between morphisms of locally ringed spaces — where the rest of the input is algebraic.

Two things make that price visible rather than hidden, and both are below:

* `ComplexAnalytic.comm_coverMapPart_id` **discharges it for the identity**, and the proof is
  `ComplexAnalytic.coverIncl_comp_coverIota` — the glue datum's own `glue_condition`, read back
  into this vocabulary. So the hypothesis is not vacuous and not unmeetable.
* `ComplexAnalytic.comm_coverMapPart_comp` **discharges it for the composite**, so
  `ComplexAnalytic.coverMap_comp` asks for nothing beyond the two hypotheses its two morphisms
  already carry. The obstruction one expects is absent and it is worth naming: the second map's
  hypothesis is an equation at pairs of `K`, so feeding it `(σ i, σ j)` would say nothing when
  `σ i = σ j`, and nothing forbids a cover map that identifies two members. **The derivation never
  forms that pair** — it goes through `ComplexAnalytic.coverIota_comp_coverMap`, which holds at
  every index unconditionally, so the second hypothesis is only ever used whole.

## The shape of the proofs

Everything after `ComplexAnalytic.coverMap` goes through
`ComplexAnalytic.coverAnalytification_hom_ext`: a morphism out of `X^an` is determined by its
restrictions to the members. So `ComplexAnalytic.coverMap_unique` is proved once, and both laws are
corollaries of it — the identity and the composite are exhibited as morphisms with the right
restrictions rather than computed. **That is why neither law needs a glue datum at all**, and why
this file is short where the construction it rests on is not.

The restriction statement carries `@[reassoc (attr := simp)]`, and the `_assoc` form is what
`ComplexAnalytic.coverMap_comp` uses. Without it, `rw [Category.assoc]` on the composite fails
against a goal that displays as `(f ≫ g) ≫ h` — the pathology `Oka/CategoryTheory/GlueData.lean`'s
module docstring describes, arising here because the objects carry unreduced
`ComplexAnalytic.coverAnalytification` projections. Generating the associated form is the cure and
it costs one attribute.

## Main definitions

- `ComplexAnalytic.coverMapPart`: the `i`-th member's contribution, `A_i^an ⟶ Y^an` — the
  analytified member morphism followed by the inclusion of the `σ i`-th member of `Y`.
- `ComplexAnalytic.coverMap`: **the induced morphism `X^an ⟶ Y^an`.**

## Main results

- `ComplexAnalytic.coverIota_comp_coverMap`: **it restricts to the analytified member morphism on
  each member**, which is the statement that says the construction is the intended one; every
  other statement here *about* `ComplexAnalytic.coverMap` rests on it, and
  `ComplexAnalytic.comm_coverMapPart_id`, which does not, is not about it.
- `ComplexAnalytic.coverMap_unique`: **and it is the only morphism that does.**
- `ComplexAnalytic.comm_coverMapPart_id` and `ComplexAnalytic.comm_coverMapPart_comp`: the
  compatibility hypothesis, discharged for the identity data and for a composite.
- `ComplexAnalytic.coverMap_id` and `ComplexAnalytic.coverMap_comp`: **the two functor laws.**

## What is not here

* **No functor.** There is no category of covered schemes in this repository to be a functor *out
  of*: the input is a cover as data, and two covers of the same scheme are different inputs with
  no morphism between them until cover independence exists. The two laws below are the content a
  functor instance would carry, stated where they can be stated.
* **No non-identity instance *below*, and there is one elsewhere now.**
  `ComplexAnalytic.refineDatumToBase` (`Oka/Analytification/RefineDatumToBase.lean`) is
  `ComplexAnalytic.coverMap` from a cross-member refined cover datum down to the datum it refines,
  at an arbitrary map of index types, at a `ψ` that is `ComplexAnalytic.localisationHom`, and with
  `hcomm` **proved**. So the identity law is no longer the only control on this definition: the
  hypothesis is now met with a `ψ` this repository constructs and a proof that comes from the
  refinement's geometry. `ComplexAnalytic.comm_coverMapPart_id` and
  `ComplexAnalytic.comm_coverMapPart_comp` below discharge it too — at the identity data, and at a
  composite whose two factors already carry it — so what is new elsewhere is the data and where
  the proof comes from, not the fact of a discharge.
* **Nothing algebraic about the compatibility.** The hypothesis is an equation of morphisms of
  locally ringed spaces; deriving it from a compatibility of the `ψ i` with the two glue data would
  need the overlaps of `X` to map into the overlaps of `Y`, which is a refinement condition on the
  input and belongs with cover independence.
* **No comparison with `Spec`.** `Oka/Analytification/CoverComparison.lean` builds the comparison
  morphism `X^an ⟶ X`; that the square against it commutes needs this file's
  `ComplexAnalytic.coverMap` and that file's morphism at once, so it is in neither and is
  `Oka/Analytification/ComparisonSquare.lean`, which imports both. **This bullet has twice
  recorded an absence a later file retired**: it said the morphism did not exist until
  `Oka/Analytification/CoverComparison.lean` arrived, and that the square was stated nowhere
  until `Oka/Analytification/ComparisonSquare.lean` did.
-/

open CategoryTheory TopologicalSpace AlgebraicGeometry

universe u

namespace ComplexAnalytic

noncomputable section

variable {J K : Type u} (obj : J → Presentation.{u})
  (poly : ∀ i : J, J → MvPolynomial (ULift.{u} (Fin (obj i).n)) ℂ)
  (glue : ∀ i j : J, coverOverlap.{u} obj poly i j ≅ coverOverlap.{u} obj poly j i)
  (hrange : ∀ i j k : J, i ≠ j → i ≠ k → j ≠ k →
    Set.range (coverTripleIncl.{u} obj poly i j k ≫
        coverTransitionHom.{u} obj poly glue i j).base ⊆
      (coverOpen.{u} obj poly j k : Set (coverSpace.{u} obj j)))
  (hsymm : ∀ i j : J, glue j i = (glue i j).symm)
  (hcocycle : ∀ i j k : J, ∀ hij : i ≠ j, ∀ hik : i ≠ k, ∀ hjk : j ≠ k,
    coverTriple.{u} obj poly glue hrange i j k hij hik hjk ≫
      coverTriple.{u} obj poly glue hrange j k i hjk hij.symm hik.symm ≫
      coverTriple.{u} obj poly glue hrange k i j hik.symm hjk.symm hij = 𝟙 _)
  (obj' : K → Presentation.{u})
  (poly' : ∀ i : K, K → MvPolynomial (ULift.{u} (Fin (obj' i).n)) ℂ)
  (glue' : ∀ i j : K, coverOverlap.{u} obj' poly' i j ≅ coverOverlap.{u} obj' poly' j i)
  (hrange' : ∀ i j k : K, i ≠ j → i ≠ k → j ≠ k →
    Set.range (coverTripleIncl.{u} obj' poly' i j k ≫
        coverTransitionHom.{u} obj' poly' glue' i j).base ⊆
      (coverOpen.{u} obj' poly' j k : Set (coverSpace.{u} obj' j)))
  (hsymm' : ∀ i j : K, glue' j i = (glue' i j).symm)
  (hcocycle' : ∀ i j k : K, ∀ hij : i ≠ j, ∀ hik : i ≠ k, ∀ hjk : j ≠ k,
    coverTriple.{u} obj' poly' glue' hrange' i j k hij hik hjk ≫
      coverTriple.{u} obj' poly' glue' hrange' j k i hjk hij.symm hik.symm ≫
      coverTriple.{u} obj' poly' glue' hrange' k i j hik.symm hjk.symm hij = 𝟙 _)
  (σ : J → K) (ψ : ∀ i : J, obj i ⟶ obj' (σ i))

/-! ### The morphism -/

/-- **The `i`-th member's contribution**, `A_i^an ⟶ Y^an`: the analytified member morphism
followed by the inclusion of the member of `Y` it lands in.

This is what `ComplexAnalytic.coverGlueMorphisms` is applied to, and naming it is what makes the
compatibility hypothesis below statable in one line rather than two composites. -/
abbrev coverMapPart (i : J) :
    AnalyticSpace.analytification.{u} (obj i).g ⟶
      coverAnalytification.{u} obj' poly' glue' hrange' hsymm' hcocycle' :=
  analytificationFunctor.{u}.map (ψ i) ≫
    coverIota.{u} obj' poly' glue' hrange' hsymm' hcocycle' (σ i)

variable (hcomm : ∀ i j : J, i ≠ j →
  coverIncl.{u} obj poly i j ≫
      (coverMapPart.{u} obj obj' poly' glue' hrange' hsymm' hcocycle' σ ψ i).toLRSHom =
    (coverTransition.{u} obj poly glue i j).hom ≫ coverIncl.{u} obj poly j i ≫
      (coverMapPart.{u} obj obj' poly' glue' hrange' hsymm' hcocycle' σ ψ j).toLRSHom)

/-- **The induced morphism `X^an ⟶ Y^an`.**

`ComplexAnalytic.coverGlueMorphisms` at the family above. Everything that makes it usable — that
the pieces satisfy the glue datum's compatibility condition, that the result is `ℂ`-linear, and
that a glue datum has no pullbacks to state agreement over — is settled there; what this file adds
is the family, and the two laws below. -/
def coverMap :
    coverAnalytification.{u} obj poly glue hrange hsymm hcocycle ⟶
      coverAnalytification.{u} obj' poly' glue' hrange' hsymm' hcocycle' :=
  coverGlueMorphisms.{u} obj poly glue hrange hsymm hcocycle
    (coverMapPart.{u} obj obj' poly' glue' hrange' hsymm' hcocycle' σ ψ) hcomm

/-- **It restricts to the analytified member morphism on each member.**

`ComplexAnalytic.coverIota_comp_coverGlueMorphisms`, and **the statement that says this
construction is the intended one rather than a well-typed one**.

**Every statement in this file about `ComplexAnalytic.coverMap` rests on this one**:
`ComplexAnalytic.coverMap_unique` rewrites by it, and both laws are corollaries of that. So a
reader who wants to know that `ComplexAnalytic.coverMap` is built out of `ψ` has to read this one
and need read no other.

**The declarations that depend on it are a larger set than that**, and the difference is what the
next paragraph turns on. `ComplexAnalytic.comm_coverMapPart_comp` needs this lemma too, and its
statement mentions `ComplexAnalytic.coverMapPart` and not `ComplexAnalytic.coverMap` — so
*aboutness* and *dependence* are two criteria here and not one, and only the second separates the
two `ComplexAnalytic.comm_coverMapPart_*` lemmas.

**`ComplexAnalytic.comm_coverMapPart_id` is the exception — the one statement in this file that
does not rest on this lemma — and it is worth naming rather than qualifying around.** It is not
about `ComplexAnalytic.coverMap` either: it says that the identity data meets the compatibility,
its proof is `ComplexAnalytic.coverIncl_comp_coverIota`, and it would hold if that morphism had
never been defined. **Until 2026-08-30 this docstring claimed that
`ComplexAnalytic.coverIota_comp_coverMap` was the only statement here with independent content,
and added that the claim was meant literally — which denied
`ComplexAnalytic.comm_coverMapPart_id` exactly the independence recorded here.**

**Two probes measure different things and only one of them is cheap.** Dropping `(attr := simp)`
from this lemma breaks exactly `ComplexAnalytic.comm_coverMapPart_comp` and
`ComplexAnalytic.coverMap_comp` — that is `simp` dependence, and it does **not** see
`ComplexAnalytic.coverMap_unique`, whose proof names the lemma in a `rw`. Logical dependence is
the list in the first paragraph and is longer; a sentence that reports the erasure count as if it
were that list is measuring the wrong thing.

It is not free either — `by first | rfl | simp` leaves the goal open, because
`ComplexAnalytic.coverMap` is a `ComplexAnalytic.coverGlueMorphisms`, whose own defining property
is stated at the glue datum's `ι` and not at `ComplexAnalytic.coverIota`. -/
@[reassoc (attr := simp)]
theorem coverIota_comp_coverMap (i : J) :
    coverIota.{u} obj poly glue hrange hsymm hcocycle i ≫
        coverMap.{u} obj poly glue hrange hsymm hcocycle obj' poly' glue' hrange' hsymm'
          hcocycle' σ ψ hcomm =
      analytificationFunctor.{u}.map (ψ i) ≫
        coverIota.{u} obj' poly' glue' hrange' hsymm' hcocycle' (σ i) :=
  coverIota_comp_coverGlueMorphisms.{u} obj poly glue hrange hsymm hcocycle _ hcomm i

/-- **And it is the only morphism that restricts that way**, by
`ComplexAnalytic.coverAnalytification_hom_ext`.

Both laws below are corollaries of this: the identity and the composite are *exhibited* as
morphisms with the right restrictions, so neither proof touches a glue datum. -/
theorem coverMap_unique
    (φ : coverAnalytification.{u} obj poly glue hrange hsymm hcocycle ⟶
      coverAnalytification.{u} obj' poly' glue' hrange' hsymm' hcocycle')
    (h : ∀ i, coverIota.{u} obj poly glue hrange hsymm hcocycle i ≫ φ =
      analytificationFunctor.{u}.map (ψ i) ≫
        coverIota.{u} obj' poly' glue' hrange' hsymm' hcocycle' (σ i)) :
    φ = coverMap.{u} obj poly glue hrange hsymm hcocycle obj' poly' glue' hrange' hsymm'
      hcocycle' σ ψ hcomm :=
  coverAnalytification_hom_ext.{u} obj poly glue hrange hsymm hcocycle _ _ fun i ↦ by
    rw [h i, coverIota_comp_coverMap]

/-! ### The identity -/

/-- **The compatibility hypothesis, discharged for the identity data** — `σ = id` and `ψ = 𝟙`.

It is `ComplexAnalytic.coverIncl_comp_coverIota`, the glue datum's own `glue_condition` read back
into this file's vocabulary, after the functor law kills the identity. Its existence is what says
the hypothesis of `ComplexAnalytic.coverMap` is meetable at all. -/
theorem comm_coverMapPart_id (i j : J) (hij : i ≠ j) :
    coverIncl.{u} obj poly i j ≫
        (coverMapPart.{u} obj obj poly glue hrange hsymm hcocycle id
          (fun i ↦ 𝟙 (obj i)) i).toLRSHom =
      (coverTransition.{u} obj poly glue i j).hom ≫ coverIncl.{u} obj poly j i ≫
        (coverMapPart.{u} obj obj poly glue hrange hsymm hcocycle id
          (fun i ↦ 𝟙 (obj i)) j).toLRSHom := by
  simpa [coverMapPart] using
    coverIncl_comp_coverIota.{u} obj poly glue hrange hsymm hcocycle i j hij

/-- **The identity law**: the identity data induces the identity of `X^an`. -/
theorem coverMap_id :
    coverMap.{u} obj poly glue hrange hsymm hcocycle obj poly glue hrange hsymm hcocycle id
        (fun i ↦ 𝟙 (obj i)) (comm_coverMapPart_id.{u} obj poly glue hrange hsymm hcocycle) =
      𝟙 _ :=
  (coverMap_unique.{u} obj poly glue hrange hsymm hcocycle obj poly glue hrange hsymm hcocycle
    id (fun i ↦ 𝟙 (obj i)) _ (𝟙 _) (by simp)).symm

/-! ### Composition -/

variable {L : Type u} (obj'' : L → Presentation.{u})
  (poly'' : ∀ i : L, L → MvPolynomial (ULift.{u} (Fin (obj'' i).n)) ℂ)
  (glue'' : ∀ i j : L, coverOverlap.{u} obj'' poly'' i j ≅ coverOverlap.{u} obj'' poly'' j i)
  (hrange'' : ∀ i j k : L, i ≠ j → i ≠ k → j ≠ k →
    Set.range (coverTripleIncl.{u} obj'' poly'' i j k ≫
        coverTransitionHom.{u} obj'' poly'' glue'' i j).base ⊆
      (coverOpen.{u} obj'' poly'' j k : Set (coverSpace.{u} obj'' j)))
  (hsymm'' : ∀ i j : L, glue'' j i = (glue'' i j).symm)
  (hcocycle'' : ∀ i j k : L, ∀ hij : i ≠ j, ∀ hik : i ≠ k, ∀ hjk : j ≠ k,
    coverTriple.{u} obj'' poly'' glue'' hrange'' i j k hij hik hjk ≫
      coverTriple.{u} obj'' poly'' glue'' hrange'' j k i hjk hij.symm hik.symm ≫
      coverTriple.{u} obj'' poly'' glue'' hrange'' k i j hik.symm hjk.symm hij = 𝟙 _)
  (τ : K → L) (χ : ∀ i : K, obj' i ⟶ obj'' (τ i))

variable (hcomm' : ∀ i j : K, i ≠ j →
  coverIncl.{u} obj' poly' i j ≫
      (coverMapPart.{u} obj' obj'' poly'' glue'' hrange'' hsymm'' hcocycle'' τ χ i).toLRSHom =
    (coverTransition.{u} obj' poly' glue' i j).hom ≫ coverIncl.{u} obj' poly' j i ≫
      (coverMapPart.{u} obj' obj'' poly'' glue'' hrange'' hsymm'' hcocycle'' τ χ j).toLRSHom)

include hcomm hcomm' hrange' hsymm' hcocycle' in
/-- **The compatibility hypothesis, discharged for the composite data** — `τ ∘ σ` and
`fun i ↦ ψ i ≫ χ (σ i)`. So the composition law below asks a caller for nothing beyond the two
hypotheses the two morphisms already carry.

**The whole of it is that the composite's `i`-th part is the first map's `i`-th part followed by
the second morphism**, at every `i` and with no hypothesis at all: `ComplexAnalytic.coverMapPart`
at the composite data is `analytificationFunctor.map (ψ i ≫ χ (σ i)) ≫ coverIota'' (τ (σ i))`, the
functor law splits it, and `ComplexAnalytic.coverIota_comp_coverMap` — which is `@[simp]` — folds
the tail back into `ComplexAnalytic.coverMap`. Given that, this statement is `hcomm` postcomposed
with one morphism, which is what `reassoc_of%` does to it.

**The obstruction one expects here is not there, and it is worth naming which one.** `hcomm'` is
an equation at pairs `i ≠ j` of `K`, so a derivation that fed it the pair `(σ i, σ j)` would say
nothing whenever `σ i = σ j` — and nothing in the input forbids a cover map carrying two distinct
members of `X` into the same member of `Y`. **No such pair is ever formed.** `hcomm'` enters only
through `ComplexAnalytic.coverMap`, which holds it whole, so nothing here splits on whether `σ` is
injective, and `key` above holds at every index with no hypothesis at all. -/
theorem comm_coverMapPart_comp (i j : J) (hij : i ≠ j) :
    coverIncl.{u} obj poly i j ≫
        (coverMapPart.{u} obj obj'' poly'' glue'' hrange'' hsymm'' hcocycle'' (τ ∘ σ)
          (fun i ↦ ψ i ≫ χ (σ i)) i).toLRSHom =
      (coverTransition.{u} obj poly glue i j).hom ≫ coverIncl.{u} obj poly j i ≫
        (coverMapPart.{u} obj obj'' poly'' glue'' hrange'' hsymm'' hcocycle'' (τ ∘ σ)
          (fun i ↦ ψ i ≫ χ (σ i)) j).toLRSHom := by
  have key : ∀ a : J,
      coverMapPart.{u} obj obj'' poly'' glue'' hrange'' hsymm'' hcocycle'' (τ ∘ σ)
          (fun i ↦ ψ i ≫ χ (σ i)) a =
        coverMapPart.{u} obj obj' poly' glue' hrange' hsymm' hcocycle' σ ψ a ≫
          coverMap.{u} obj' poly' glue' hrange' hsymm' hcocycle' obj'' poly'' glue'' hrange''
            hsymm'' hcocycle'' τ χ hcomm' := fun a ↦ by
    simp [coverMapPart]
  rw [key i, key j]
  exact (reassoc_of% (hcomm i j hij)) _

/-- **The composition law.**

`ComplexAnalytic.coverMap_unique` at the composite, whose own compatibility is
`ComplexAnalytic.comm_coverMapPart_comp` rather than a hypothesis a caller has to supply.

**A caller holding some other proof of that compatibility loses nothing**: the two are proofs of
one `Prop`, so `ComplexAnalytic.coverMap` cannot tell them apart and the equation stated here is
the equation they wanted. That is what makes naming a particular proof in the statement free. -/
theorem coverMap_comp :
    coverMap.{u} obj poly glue hrange hsymm hcocycle obj' poly' glue' hrange' hsymm' hcocycle'
        σ ψ hcomm ≫
      coverMap.{u} obj' poly' glue' hrange' hsymm' hcocycle' obj'' poly'' glue'' hrange'' hsymm''
        hcocycle'' τ χ hcomm' =
    coverMap.{u} obj poly glue hrange hsymm hcocycle obj'' poly'' glue'' hrange'' hsymm''
      hcocycle'' (τ ∘ σ) (fun i ↦ ψ i ≫ χ (σ i))
      (comm_coverMapPart_comp.{u} obj poly glue obj' poly' glue' hrange' hsymm' hcocycle' σ ψ
        hcomm obj'' poly'' glue'' hrange'' hsymm'' hcocycle'' τ χ hcomm') :=
  coverMap_unique.{u} obj poly glue hrange hsymm hcocycle obj'' poly'' glue'' hrange'' hsymm''
    hcocycle'' (τ ∘ σ) (fun i ↦ ψ i ≫ χ (σ i)) _ _ (by simp)

end

end ComplexAnalytic
