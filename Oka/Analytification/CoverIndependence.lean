/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Analytification.CoverFunctoriality

/-!
# Two cover data with isomorphic members give the same `X^an`

`Oka/Analytification/AffineCover.lean` builds `X^an` from a cover as *data* — an index type, a
presentation for each index, a polynomial cutting out each overlap, and an isomorphism of the two
descriptions of each overlap — and the construction depends on all of it. **Nothing so far says
that two data describing the same geometry give the same space.** This file is the first two
instalments of that.

## The two increments, and what each varies

* **Member-wise presentation independence**, the smaller one. The two data share an **index
  type**, so the members correspond one to one and the overlaps sit at the same pairs. What varies
  is the *presentation* of each member — an isomorphism `ψ i : obj i ≅ obj' i` in
  `ComplexAnalytic.Presentation` — and, with it, everything downstream of a presentation: the
  polynomials cutting out the overlaps, the identifications of the overlaps, and the two
  triple-overlap hypotheses.
* **Reindexing.** The index types differ by an equivalence `e : J ≃ K` and the members are
  isomorphic *along it*, `χ i : obj i ≅ objK (e i)`.

In both, `hrange` and `hcocycle` are asked for on each side separately.

## The first increment is literally the second at `Equiv.refl`, and that is measured

`ComplexAnalytic.coverMap_hom_inv`'s statement is `ComplexAnalytic.coverMap_reindex_hom_inv`'s at
`e = Equiv.refl J`, **and the proof term typechecks as it stands** — no coercion, no
`CategoryTheory.eqToHom`, no congruence step. What makes that work is that
`ComplexAnalytic.coverReindexInv` at `Equiv.refl` reduces to `fun i ↦ (ψ i).inv` *definitionally*,
which was not obvious in advance: it is `CategoryTheory.eqToHom rfl ≫ (ψ i).inv`, and the
reduction needs `𝟙 ≫ f` to be `f` by `rfl` in this category rather than by `Category.id_comp`.

**The same-index statements are kept anyway.** That is the choice
`Oka/Analytification/AffineCover.lean` and `Oka/Analytification/CoverFunctoriality.lean` both
settled on for a readable instance of a general statement: a caller with one index type should not
have to supply an `Equiv` and read past a transport to find the statement they want. What the
general one adds is not content at that instance — it is the two index types.

## What the reindexing costs, and it is one transport in each direction

`ComplexAnalytic.coverReindexInv` — the family the backward morphism is glued from — cannot be
written without a `CategoryTheory.eqToHom`: `χ` is indexed by `J` and the family by `K`, so its
inverse at `e.symm k` has source `objK (e (e.symm k))` where `objK k` is wanted. **That single
`eqToHom` is the whole difference between the two increments**, and it is why reindexing is not a
corollary of member-wise independence in the other direction.

It surfaces twice, asymmetrically, and the asymmetry is worth naming because it looks like an
accident and is not. The **backward** round trip meets `χ` at one index and the isomorphism
cancels before anything has to move, so only `ComplexAnalytic.coverIota`'s index is transported.
The **forward** one meets `χ` at `i` and at `e.symm (e i)`, so both `coverIota` and `χ` are.

**`CategoryTheory.dcongr_arg` does both**, and no lemma had to be written for either. It is
Mathlib's transport for a family `α : ∀ i, F i ⟶ G i` along `h : i = j`, and its content is the
`subst` that the proofs themselves cannot do — there the index is `e.symm (e i)`, which is not a
variable, which is why `simp [Equiv.symm_apply_apply]`, `rw [e.symm_apply_apply i]`, `obtain` and
`cases` on the equivalence all leave the goal open. **That was measured as this increment's
obstruction before the file was written, and the obstruction turned out to be already bridged.**

## Each increment takes two compatibility hypotheses and they do not reduce to one

`ComplexAnalytic.coverMap` asks for agreement over the overlaps, and each increment here asks for
it twice — once for the forward family and once for the backward one. **That is not redundancy and
it is worth saying why, since it is the first question a reader has.** The two hypotheses are
equations over *different spaces*: the first is about `ComplexAnalytic.coverPart obj poly i j` and
the second about `ComplexAnalytic.coverPart obj' poly' i j`. Those are open subspaces cut out by
`poly i j` and `poly' i j`, which do not even live in the same type — `poly i j` is a polynomial
in `(obj i).n` variables and `poly' i j` in `(obj' i).n` — so neither hypothesis is a statement
the other could imply. In the reindexed increment the second is indexed by `K` rather than by `J`,
which is the same argument one step further along.

## The proof, and it does not touch a glue datum

Both round trips go through `ComplexAnalytic.coverAnalytification_hom_ext` and
`ComplexAnalytic.coverIota_comp_coverMap`, which is what
`Oka/Analytification/CoverFunctoriality.lean` set up for exactly this: a morphism out of `X^an` is
determined by its restrictions, so the composite is identified by restricting it. Neither
`ComplexAnalytic.coverMap_id` nor `ComplexAnalytic.coverMap_comp` is used — the composite's family
is `fun i ↦ (ψ i).hom ≫ (ψ i).inv` rather than `fun i ↦ 𝟙`, so going through the two laws would
need a congruence step that going through uniqueness directly does not.

**One trap, recorded because four rewrites fail on it.** After `simp` the residual goal *displays*
as `F.map h ≫ F.map h⁻¹ ≫ ι`, and `rw [← Functor.map_comp]`, `rw [← Functor.map_comp_assoc]`,
`simp [← Functor.map_comp]` and `simp [← Functor.map_comp_assoc]` all fail with *"did not find an
occurrence of the pattern"*. This is the pathology `Oka/CategoryTheory/GlueData.lean`'s module
docstring predicts by name — the objects carry unreduced `ComplexAnalytic.coverAnalytification`
projections — and it is the fifth file on this line of work to hit it.
`CategoryTheory.Iso.hom_inv_id_assoc` at `ComplexAnalytic.analytificationFunctor.mapIso` names the
fact instead of asking `simp` to find it, and that is what the proofs below use.

**The same pathology reaches `Category.assoc` itself in the reindexed backward round trip**, and
there it is the sixth instance rather than the fifth. Unfolding
`ComplexAnalytic.coverReindexInv` puts a composite in the *first* factor, so the goal acquires the
shape `(f ≫ g) ≫ h ≫ k` — and `rw [Category.assoc]` and `simp only [Category.assoc]` both decline
it, the first reporting *"did not find an occurrence of the pattern"* with a note that the target
is not type-correct at `instances` transparency. `(Category.assoc _ _ _).trans` as a **term**
never consults the unifier and closes it in one line; the congruence after it is written as
`congrArg (_ ≫ ·)` for the same reason. The forward round trip needs neither, because there the
composite is unfolded in the second factor and the chain is already right-nested.

**And they normalise with `simp only` and an explicit list rather than with `simp`**, which is not
a style preference: `lake build --wfail` runs the `flexible` linter, and a bare `simp` followed by
an `exact` that modifies the same goal is a **build failure** on this project rather than a
warning. The list the linter itself suggests is the one below, and
`ComplexAnalytic.analytificationFunctor_obj` is in it — the fourth consumer of a lemma whose own
docstring predicts that every consumer of the functor spells its object the other way.

## Main definitions

- `ComplexAnalytic.coverAnalytificationIso`: **the isomorphism `X^an ≅ X'^an`**, at one index type.
- `ComplexAnalytic.coverReindexInv`: the backward family when the index types differ, and the one
  `CategoryTheory.eqToHom` the difference costs.
- `ComplexAnalytic.coverAnalytificationReindexIso`: **the isomorphism when the index types differ
  by an equivalence.**

## Main results

- `ComplexAnalytic.coverMap_hom_inv` and `ComplexAnalytic.coverMap_inv_hom`: the two round trips,
  stated as theorems beside the isomorphism rather than inlined into its fields, so that a caller
  who wants one of them need not project.
- `ComplexAnalytic.coverMap_reindex_hom_inv` and `ComplexAnalytic.coverMap_reindex_inv_hom`: the
  same two when the index types differ, and the pair the two above are an instance of.

## What is not here

* **No refinement.** An equivalence of index types matches the members one to one; nothing here
  allows one cover to have more members than the other, or a member of one to be covered by
  several of the other. **Both increments here take `σ` and `ψ` from the caller**, which is the
  difference. That is taxis #1107's third increment, and
  `Oka/Analytification/CoverRefinement.lean` is where it is done: for members refined by
  distinguished opens of **one** fixed member it now builds the whole cover datum — the members,
  the polynomials, the glue isomorphism, its coherence triangle and both geometric laws — and
  with it `ComplexAnalytic.refineAnalytification` and the morphism
  `ComplexAnalytic.refineToBase` down to the fixed member. **That morphism is not an
  isomorphism**, which is proved there rather than left open, so a refinement is not an instance
  of what this file does.

  **This sentence read *"Still absent there, and so still absent everywhere: … a literal
  `ComplexAnalytic.coverMap` out of a refinement, which needs `A^an` presented as a one-member
  cover datum and that gluing identified with `A^an` — an identification nothing in this
  repository states"*, and the price it quotes is the *one-member* case's and is not owed by the
  cross-member one.** `coverMap` runs between two cover **data**. What blocks it at
  `Oka/Analytification/CoverRefinement.lean` is that the *target* there is a single
  `ComplexAnalytic.Presentation`; a cross-member refinement's target is
  `ComplexAnalytic.coverAnalytification` of the original datum, which is already a cover datum, so
  neither the one-member presentation nor the identification exists to be paid.
  `ComplexAnalytic.refineDatumToBase` (`Oka/Analytification/RefineDatumToBase.lean`) is that
  `coverMap`, and it is the first one **outside `Oka/Analytification/CoverFunctoriality.lean`**
  whose compatibility hypothesis is discharged rather than taken from a caller — inside that file
  the two functor laws already discharge it, `ComplexAnalytic.comm_coverMapPart_id` at the
  identity data and `ComplexAnalytic.comm_coverMapPart_comp` at a composite, the latter from the
  two hypotheses of the morphisms being composed. The identification is still not stated and is
  still what a *one-member* `coverMap` would need.

  **What is absent in the cross-member case is the datum and no longer the transport.** This
  bullet used to say that the case is absent because the original cover's own `glue` has to be
  transported; `Oka/Analytification/CrossMemberGlue.lean` transports it —
  `ComplexAnalytic.refineCrossGlue` with its coherence triangle
  `ComplexAnalytic.refineCrossGlue_hom_comp`, over the *original overlap* rather than over either
  member, since the data relates no two members. What no file has is a refined cover datum whose
  members cross, and what is missing has gone from four things to two and a half. Its `poly`
  field is `ComplexAnalytic.refineDatumPoly` (`Oka/Analytification/CrossMemberDatum.lean`), one
  formula per ordered pair with the two cases read back off it; its `glue` is
  `ComplexAnalytic.refineDatumGlue` (`Oka/Analytification/CrossMemberDatumGlue.lean`), the equal
  branch and the cross-member one under a case split, each with its coherence triangle — the
  transport between two objects of `ComplexAnalytic.Presentation` that the one-member case never
  meets cost one `subst`, and the case split itself cost nothing, both branches being isomorphisms
  between the same two objects. **So the count is one rather than two and a half, and this
  sentence gave two until two later increments landed.** It read *"the count is two rather than
  two and a half, and the half that moved did not become nothing: the unequal branch takes the
  caller's `r`, `u` and two equations, and the existentials that would produce them are the same
  ones `hsymm` is blocked on. What is left is that choice, an `hsymm` quantified over every
  ordered pair, and the two geometric laws"*. **The half went first**:
  `ComplexAnalytic.exists_refineDatumCross` (`Oka/Analytification/CrossMemberChoice.lean`)
  produces `q`, `r`, `u` and both obligations at every ordered pair from the *input* datum's
  symmetry law, algebraically. **This sentence said it did so *"using none of the three
  existentials that sentence had in mind"*, and it spends one of them**: three existentials did
  not have to be instantiated, one did, and it is `ComplexAnalytic.exists_mk_rename_eq` — that is
  `Oka/Analytification/CrossMemberDatumGlue.lean`'s own wording for the correction — and
  `ComplexAnalytic.exists_refineDatumCrossFactor` is where it is spent. The two it does **not**
  spend are the two that produce an equality of *opens*, which is exactly why it says nothing
  about what the overlap so refined cuts out: an equality of opens does not give an associate.
  **Then the `hsymm` went**:
  `ComplexAnalytic.refineDatumGlue_symm` (`Oka/Analytification/RefineDatumSymm.lean`) is that law
  at every ordered pair, for two arbitrary independent choices, so the compatibility this bullet
  expected to be needed is not needed at all. **What is left is the two geometric laws**, and the
  count above stays at one — but the two no longer stand or fall together. This sentence read
  *"which have no cross-member analogue at all"* until
  `ComplexAnalytic.refineDatumTransitionHom_localisationProj_of_ne`
  (`Oka/Analytification/RefineDatumTransition.lean`) gave `hrange` one: the refined transition
  lies over the original datum's own `ComplexAnalytic.coverTransitionHom`, there being no morphism
  between two members of a cover datum for it to lie over instead. It leaves `hrange` a single
  containment, in the caller's own `D(q b c)`, at a triple whose three members are pairwise
  different — `ComplexAnalytic.range_refineDatumTransitionHom_subset_iff` states that as an
  *equivalence* and not as a sufficient condition. **This sentence went on to say "and nothing at
  all at the mixed triples, where `ComplexAnalytic.refineDatumGlue` takes its equal branch and the
  triangle is over a member", and a triangle over a member is what settles them**:
  `Oka/Analytification/RefineDatumRange.lean` reads all four remaining shapes off it — `hrange`
  outright where the three members are equal, that same containment at two more, and a
  containment in the caller's own `D(fam c)` at the fourth. **This sentence said `hcocycle` "keeps
  the clause" and that it "cannot be stated before `hrange` is proved in any case"**, which was
  right about `ComplexAnalytic.coverTriple` taking the range law as an argument and is no longer a
  bar: `Oka/Analytification/RefineDatumGlueData.lean` joins the five shapes into one proof and
  states the cocycle law off it, as `ComplexAnalytic.RefineDatumCocycle`, and
  `ComplexAnalytic.refineDatumHcocycle` (`Oka/Analytification/RefineDatumCocycle.lean`) proves it
  from the original datum's own three laws. **The count is still not moved, and now the whole of
  the reason is the range law**: `ComplexAnalytic.refineDatumHrange_iff` says the two conditions
  the assembled law is proved from are *equivalent* to it, so what a caller carries is the range
  law under another name and not a discharge of it. It counts what a refined datum still owes,
  which is those two conditions and no law at all. Those nine files' `## What is not here` state
  all of it.

  **This bullet also said refinement is where `σ` and `ψ` "have to be built", with the implication
  that building them is the work; the second half is false and was measured so on 2026-08-30.**
  `ψ` is `ComplexAnalytic.localisationHom`, whose direction convention is already the one
  `ComplexAnalytic.coverMap` wants, and `σ` is constant in the case that file treats — neither
  costs a line. The work is the refined cover *datum*, which is what that file is mostly about.
* **No scheme.** Nothing here says the two data describe the same scheme. **The clause that used
  to follow — *"there is no scheme in this line of files at all"* — was retired on 2026-09-02**:
  `Oka/Analytification/SpecScheme.lean` promotes `ComplexAnalytic.specGlued` to
  `ComplexAnalytic.specScheme`, and it is the only scheme on this line.
  `Oka/Analytification/Comparison.lean` and `Oka/Analytification/AffineCover.lean` each
  argue in a titled section why nothing *here* is one — **this sentence named
  `Oka/Analytification/CoverFunctoriality.lean` for the first until 2026-09-02, and that file has
  no such section**; its `## What is not here` argues there is no category of covered schemes to
  be a functor out of, which is a different absence. Neither is weakened by that module:
  what they are about is the absence of a scheme from the **input**, which is still a cover datum
  and is still not produced from a scheme. taxis #1107's headline speaks of two *admissible covers
  of a scheme*, and there is still no predicate of that name — but **defining one is not what that
  issue's fourth increment is blocked on, and this bullet said until 2026-08-31 that it was.**
  Every part admissibility asserts of a member already held of a cover datum, and each was already
  a declaration: `ComplexAnalytic.finiteType_presentationAlg` for finite type over `ℂ`,
  `ComplexAnalytic.isOpenImmersion_specIota` for openness, and
  `AlgebraicGeometry.LocallyRingedSpace.GlueData.ι_jointly_surjective` for the covering, the three
  packaged as `ComplexAnalytic.specGluedOpenCover`. What a common refinement of two data has to
  reproduce is a **stronger**
  condition the data already carries and nobody had named — every pairwise overlap is a
  *distinguished* open of each of the two members it lies in —
  and `Oka/Analytification/SpecAffineCover.lean`'s admissibility section is where it is written
  down. taxis #1329 has the measurement. **Its *local* form turned out to be a Mathlib lemma
  nobody had connected to it**: any two affine opens of a scheme have, at each point of their
  overlap, an open distinguished in both, which is
  `AlgebraicGeometry.exists_basicOpen_le_affine_inter` and is stated at the members of a cover
  datum by `ComplexAnalytic.exists_basicOpen_specSchemeIota_inter`. **That is strictly weaker than
  the condition above** — a datum's overlap *is* a distinguished open of each member, where the
  lemma gives only a distinguished neighbourhood of each point of it — and it is the local
  statement a common refinement would be assembled from rather than a step of one. Nothing builds
  such a refinement.
* **No naturality.** That the isomorphism commutes with `ComplexAnalytic.coverMap` out of either
  side, or with the comparison morphisms of `Oka/Analytification/CoverComparison.lean`, is not
  stated. Nothing consumes it yet.
-/

open CategoryTheory TopologicalSpace AlgebraicGeometry

universe u

namespace ComplexAnalytic

noncomputable section

variable {J : Type u} (obj : J → Presentation.{u})
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
  (obj' : J → Presentation.{u})
  (poly' : ∀ i : J, J → MvPolynomial (ULift.{u} (Fin (obj' i).n)) ℂ)
  (glue' : ∀ i j : J, coverOverlap.{u} obj' poly' i j ≅ coverOverlap.{u} obj' poly' j i)
  (hrange' : ∀ i j k : J, i ≠ j → i ≠ k → j ≠ k →
    Set.range (coverTripleIncl.{u} obj' poly' i j k ≫
        coverTransitionHom.{u} obj' poly' glue' i j).base ⊆
      (coverOpen.{u} obj' poly' j k : Set (coverSpace.{u} obj' j)))
  (hsymm' : ∀ i j : J, glue' j i = (glue' i j).symm)
  (hcocycle' : ∀ i j k : J, ∀ hij : i ≠ j, ∀ hik : i ≠ k, ∀ hjk : j ≠ k,
    coverTriple.{u} obj' poly' glue' hrange' i j k hij hik hjk ≫
      coverTriple.{u} obj' poly' glue' hrange' j k i hjk hij.symm hik.symm ≫
      coverTriple.{u} obj' poly' glue' hrange' k i j hik.symm hjk.symm hij = 𝟙 _)
  (ψ : ∀ i : J, obj i ≅ obj' i)

/-! ### The two compatibility hypotheses -/

variable (hcomm : ∀ i j : J, i ≠ j →
  coverIncl.{u} obj poly i j ≫
      (coverMapPart.{u} obj obj' poly' glue' hrange' hsymm' hcocycle' id
        (fun i ↦ (ψ i).hom) i).toLRSHom =
    (coverTransition.{u} obj poly glue i j).hom ≫ coverIncl.{u} obj poly j i ≫
      (coverMapPart.{u} obj obj' poly' glue' hrange' hsymm' hcocycle' id
        (fun i ↦ (ψ i).hom) j).toLRSHom)
  (hcomm' : ∀ i j : J, i ≠ j →
    coverIncl.{u} obj' poly' i j ≫
        (coverMapPart.{u} obj' obj poly glue hrange hsymm hcocycle id
          (fun i ↦ (ψ i).inv) i).toLRSHom =
      (coverTransition.{u} obj' poly' glue' i j).hom ≫ coverIncl.{u} obj' poly' j i ≫
        (coverMapPart.{u} obj' obj poly glue hrange hsymm hcocycle id
          (fun i ↦ (ψ i).inv) j).toLRSHom)

/-! ### The isomorphism -/

/-- **The two induced morphisms compose to the identity of `X^an`.**

`ComplexAnalytic.coverAnalytification_hom_ext` and `ComplexAnalytic.coverIota_comp_coverMap`: the
composite restricts on the `i`-th member to `analytificationFunctor.map ((ψ i).hom ≫ (ψ i).inv)`
followed by the inclusion, and that functor sends an isomorphism's round trip to the identity. -/
theorem coverMap_hom_inv :
    coverMap.{u} obj poly glue hrange hsymm hcocycle obj' poly' glue' hrange' hsymm' hcocycle'
        id (fun i ↦ (ψ i).hom) hcomm ≫
      coverMap.{u} obj' poly' glue' hrange' hsymm' hcocycle' obj poly glue hrange hsymm hcocycle
        id (fun i ↦ (ψ i).inv) hcomm' = 𝟙 _ :=
  coverAnalytification_hom_ext.{u} obj poly glue hrange hsymm hcocycle _ _ fun i ↦ by
    simp only [coverIota_comp_coverMap_assoc, analytificationFunctor_obj, id_eq, Category.assoc,
      coverIota_comp_coverMap, Category.comp_id]
    exact (analytificationFunctor.{u}.mapIso (ψ i)).hom_inv_id_assoc _

/-- **And the other way round**, on `X'^an`. -/
theorem coverMap_inv_hom :
    coverMap.{u} obj' poly' glue' hrange' hsymm' hcocycle' obj poly glue hrange hsymm hcocycle
        id (fun i ↦ (ψ i).inv) hcomm' ≫
      coverMap.{u} obj poly glue hrange hsymm hcocycle obj' poly' glue' hrange' hsymm' hcocycle'
        id (fun i ↦ (ψ i).hom) hcomm = 𝟙 _ :=
  coverAnalytification_hom_ext.{u} obj' poly' glue' hrange' hsymm' hcocycle' _ _ fun i ↦ by
    simp only [coverIota_comp_coverMap_assoc, analytificationFunctor_obj, id_eq, Category.assoc,
      coverIota_comp_coverMap, Category.comp_id]
    exact (analytificationFunctor.{u}.mapIso (ψ i)).inv_hom_id_assoc _

/-- **Two presentations of each member give canonically isomorphic analytifications.**

Both morphisms are `ComplexAnalytic.coverMap`, so the isomorphism restricts on each member to the
analytified isomorphism of presentations — which is what says it is the intended one and not
merely one of the right type, and is `ComplexAnalytic.coverIota_comp_coverMap` at each of them. -/
def coverAnalytificationIso :
    coverAnalytification.{u} obj poly glue hrange hsymm hcocycle ≅
      coverAnalytification.{u} obj' poly' glue' hrange' hsymm' hcocycle' where
  hom := coverMap.{u} obj poly glue hrange hsymm hcocycle obj' poly' glue' hrange' hsymm'
    hcocycle' id (fun i ↦ (ψ i).hom) hcomm
  inv := coverMap.{u} obj' poly' glue' hrange' hsymm' hcocycle' obj poly glue hrange hsymm
    hcocycle id (fun i ↦ (ψ i).inv) hcomm'
  hom_inv_id := coverMap_hom_inv.{u} obj poly glue hrange hsymm hcocycle obj' poly' glue'
    hrange' hsymm' hcocycle' ψ hcomm hcomm'
  inv_hom_id := coverMap_inv_hom.{u} obj poly glue hrange hsymm hcocycle obj' poly' glue'
    hrange' hsymm' hcocycle' ψ hcomm hcomm'

/-! ### Reindexing along an equivalence of index types -/

variable {K : Type u} (objK : K → Presentation.{u})
  (polyK : ∀ i : K, K → MvPolynomial (ULift.{u} (Fin (objK i).n)) ℂ)
  (glueK : ∀ i j : K, coverOverlap.{u} objK polyK i j ≅ coverOverlap.{u} objK polyK j i)
  (hrangeK : ∀ i j k : K, i ≠ j → i ≠ k → j ≠ k →
    Set.range (coverTripleIncl.{u} objK polyK i j k ≫
        coverTransitionHom.{u} objK polyK glueK i j).base ⊆
      (coverOpen.{u} objK polyK j k : Set (coverSpace.{u} objK j)))
  (hsymmK : ∀ i j : K, glueK j i = (glueK i j).symm)
  (hcocycleK : ∀ i j k : K, ∀ hij : i ≠ j, ∀ hik : i ≠ k, ∀ hjk : j ≠ k,
    coverTriple.{u} objK polyK glueK hrangeK i j k hij hik hjk ≫
      coverTriple.{u} objK polyK glueK hrangeK j k i hjk hij.symm hik.symm ≫
      coverTriple.{u} objK polyK glueK hrangeK k i j hik.symm hjk.symm hij = 𝟙 _)
  (e : J ≃ K) (χ : ∀ i : J, obj i ≅ objK (e i))

/-- **The backward family**, `A'_k ⟶ A_{e⁻¹ k}` as a morphism of presentations.

`χ` runs `obj i ≅ objK (e i)`, so its inverse at `e.symm k` runs
`objK (e (e.symm k)) ⟶ obj (e.symm k)` and the source is the wrong spelling of `objK k` by one
application of `Equiv.apply_symm_apply`. **The `CategoryTheory.eqToHom` in front is that spelling
and is the whole cost of allowing the index types to differ**; there is no way to state the
backward family without it, since `χ` is indexed by `J` and this family by `K`. -/
def coverReindexInv (k : K) : objK k ⟶ obj (e.symm k) :=
  eqToHom (congrArg objK (e.apply_symm_apply k)).symm ≫ (χ (e.symm k)).inv

variable (hcommK : ∀ i j : J, i ≠ j →
  coverIncl.{u} obj poly i j ≫
      (coverMapPart.{u} obj objK polyK glueK hrangeK hsymmK hcocycleK e
        (fun i ↦ (χ i).hom) i).toLRSHom =
    (coverTransition.{u} obj poly glue i j).hom ≫ coverIncl.{u} obj poly j i ≫
      (coverMapPart.{u} obj objK polyK glueK hrangeK hsymmK hcocycleK e
        (fun i ↦ (χ i).hom) j).toLRSHom)
  (hcommK' : ∀ i j : K, i ≠ j →
    coverIncl.{u} objK polyK i j ≫
        (coverMapPart.{u} objK obj poly glue hrange hsymm hcocycle e.symm
          (coverReindexInv.{u} obj objK e χ) i).toLRSHom =
      (coverTransition.{u} objK polyK glueK i j).hom ≫ coverIncl.{u} objK polyK j i ≫
        (coverMapPart.{u} objK obj poly glue hrange hsymm hcocycle e.symm
          (coverReindexInv.{u} obj objK e χ) j).toLRSHom)

/-- **The two induced morphisms compose to the identity of `X^an`**, when the index types differ
by an equivalence.

`ComplexAnalytic.coverAnalytification_hom_ext` and `ComplexAnalytic.coverIota_comp_coverMap`, as
in the same-index case above, and then **two transports rather than none**:
`ComplexAnalytic.coverIota` is left at the index `e.symm (e i)` and `χ` at the same index, and
`CategoryTheory.dcongr_arg` moves both to `i`. -/
theorem coverMap_reindex_hom_inv :
    coverMap.{u} obj poly glue hrange hsymm hcocycle objK polyK glueK hrangeK hsymmK hcocycleK
        e (fun i ↦ (χ i).hom) hcommK ≫
      coverMap.{u} objK polyK glueK hrangeK hsymmK hcocycleK obj poly glue hrange hsymm hcocycle
        e.symm (coverReindexInv.{u} obj objK e χ) hcommK' = 𝟙 _ :=
  coverAnalytification_hom_ext.{u} obj poly glue hrange hsymm hcocycle _ _ fun i ↦ by
    simp only [coverIota_comp_coverMap_assoc, analytificationFunctor_obj, Category.assoc,
      coverIota_comp_coverMap, Category.comp_id]
    rw [dcongr_arg (coverIota.{u} obj poly glue hrange hsymm hcocycle) (e.symm_apply_apply i),
      coverReindexInv, dcongr_arg (fun i ↦ (χ i).inv) (e.symm_apply_apply i)]
    simp only [Functor.map_comp, eqToHom_map, Category.assoc, Category.id_comp,
      analytificationFunctor_obj, eqToHom_trans_assoc, eqToHom_refl]
    exact (analytificationFunctor.{u}.mapIso (χ i)).hom_inv_id_assoc _

/-- **And the other way round**, on `Y^an`.

**One transport, not two.** The composite restricts on the `k`-th member to the round trip of `χ`
at the single index `e.symm k`, so the isomorphism cancels before any index has to be moved and
only `ComplexAnalytic.coverIota`'s is left. That asymmetry is not a defect of the proof: the
backward family is the one carrying the `CategoryTheory.eqToHom`, so it is the forward round trip
that meets `χ` at two different indices. -/
theorem coverMap_reindex_inv_hom :
    coverMap.{u} objK polyK glueK hrangeK hsymmK hcocycleK obj poly glue hrange hsymm hcocycle
        e.symm (coverReindexInv.{u} obj objK e χ) hcommK' ≫
      coverMap.{u} obj poly glue hrange hsymm hcocycle objK polyK glueK hrangeK hsymmK hcocycleK
        e (fun i ↦ (χ i).hom) hcommK = 𝟙 _ :=
  coverAnalytification_hom_ext.{u} objK polyK glueK hrangeK hsymmK hcocycleK _ _ fun k ↦ by
    simp only [coverIota_comp_coverMap_assoc, analytificationFunctor_obj, Category.assoc,
      coverIota_comp_coverMap, Category.comp_id]
    rw [dcongr_arg (coverIota.{u} objK polyK glueK hrangeK hsymmK hcocycleK)
        (e.apply_symm_apply k).symm, coverReindexInv]
    simp only [Functor.map_comp, eqToHom_map]
    refine (Category.assoc _ _ _).trans ?_
    exact congrArg (_ ≫ ·) ((analytificationFunctor.{u}.mapIso (χ (e.symm k))).inv_hom_id_assoc _)

/-- **Two cover data whose index types differ by an equivalence, and whose members are isomorphic
as presentations along it, give canonically isomorphic analytifications.**

Both morphisms are `ComplexAnalytic.coverMap`, so the isomorphism restricts on the `i`-th member
of `X` to the analytified `χ i` followed by the inclusion of the `e i`-th member of `Y` — which is
`ComplexAnalytic.coverIota_comp_coverMap` and is what says it is the intended isomorphism rather
than one of the right type. -/
def coverAnalytificationReindexIso :
    coverAnalytification.{u} obj poly glue hrange hsymm hcocycle ≅
      coverAnalytification.{u} objK polyK glueK hrangeK hsymmK hcocycleK where
  hom := coverMap.{u} obj poly glue hrange hsymm hcocycle objK polyK glueK hrangeK hsymmK
    hcocycleK e (fun i ↦ (χ i).hom) hcommK
  inv := coverMap.{u} objK polyK glueK hrangeK hsymmK hcocycleK obj poly glue hrange hsymm
    hcocycle e.symm (coverReindexInv.{u} obj objK e χ) hcommK'
  hom_inv_id := coverMap_reindex_hom_inv.{u} obj poly glue hrange hsymm hcocycle objK polyK
    glueK hrangeK hsymmK hcocycleK e χ hcommK hcommK'
  inv_hom_id := coverMap_reindex_inv_hom.{u} obj poly glue hrange hsymm hcocycle objK polyK
    glueK hrangeK hsymmK hcocycleK e χ hcommK hcommK'

end

end ComplexAnalytic
