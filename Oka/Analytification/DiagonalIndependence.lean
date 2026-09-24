/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Analytification.CrossMemberDatum

/-!
# A cover datum's diagonal is unread, and the space it glues to says so

`Oka/Analytification/AffineCover.lean`'s `## The diagonal` section records that the diagonal data
of a cover datum — `poly i i` and `glue i i` — is asked for and never consumed, and that
`poly i i = 1` with `glue i i = Iso.refl` *"is the natural choice, satisfies it, and is checked by
nothing"*. `Oka/Analytification/CrossMemberDatum.lean` then **uses** that: its
`ComplexAnalytic.polyDiagOne` normalises the diagonal to `1` so that one product serves the two
cases of a cross-member refined `poly`, and until this file existed it gave the half it could not
prove a section of its own:

> **What is not proved here is that normalising leaves the glued space unchanged.** It is a
> statement about `ComplexAnalytic.coverAnalytification` of two data that differ on the diagonal,
> nothing below states it, and the paragraph above is an argument and not a citation of one.

**That sentence is no longer in that file.** The same branch that added this one replaced it with
a citation of what is below, so the quotation is of what stood there until 2026-08-31 and is here
to say what this file is for and not to describe the file as it is now.

This file is that statement, and it comes out stronger than the diagonal:
`ComplexAnalytic.coverAnalytification_congr` says the glued analytic space depends on `poly` and
`glue` **only through their values off the diagonal**, for any two data that agree there.
`ComplexAnalytic.coverAnalytification_polyDiagOne` is the instance
`Oka/Analytification/CrossMemberDatum.lean` asks for.

## Why the two data are not two values of one type, which is the whole cost

`glue i j` is an isomorphism of `ComplexAnalytic.coverOverlap obj poly i j` with
`ComplexAnalytic.coverOverlap obj poly j i`, so `poly i i` occurs in the **type** of `glue`. Two
data differing on the diagonal therefore have `glue`s of different types, their overlaps
`ComplexAnalytic.coverPart` are equal only propositionally, and every field below inherits that:
`f`'s type mentions `V`, `t`'s mentions `V` twice. So the comparison is `HEq` from `f` down and
there is no `Eq` anywhere to `rw` with. **That, and not the geometry, is what this file costs.**

Each transport is the same two lines — abstract the polynomial (or the open, or the morphism) as a
*variable*, `rintro … rfl`, and the two sides become one — and they are named rather than inlined
because the next author to compare two cover data will want them and they are not discoverable
from the goal.

## `t'` is not among them, and that is a fact about `CategoryTheory.GlueData'`

The field that would have been worst is `t'`, whose type mentions four pullbacks of the `f`s.
`CategoryTheory.GlueData'.ext_of_heq` does not ask for it: `t_fac` factorises `t'` through
`CategoryTheory.Limits.pullback.snd`, which is a pullback of the monomorphism `f j k`, so `t'` is
determined by `t` and `CategoryTheory.cancel_mono` supplies it. That lemma is in
`Oka/CategoryTheory/GlueData.lean` because it is about Mathlib's structure and not about a cover.

## One place where the elaborator has to be told the type, and one where it was thought to be

* **`ComplexAnalytic.AnalyticSpace.ofGlueDataCLinear_congr`'s `HEq` argument.** The two
  `ℂ`-algebra families here are the *same expression* — the members' own algebra maps — but their
  types read `(D.U i).presheaf.obj (op ⊤)` at two different glue data. Passing `HEq.rfl` against an
  inferred type exceeds the default heartbeat budget; a `have` at the spelled-out family is
  immediate, and the difference is that the second never asks the elaborator to reduce
  `CategoryTheory.GlueData.ofGlueData'` inside a metavariable. **The failure is machine-dependent
  and the workaround is not**: measured three times on 2026-08-31, the inline form gives
  `(kernel) deterministic timeout` after 2m32s and after 154s on two machines and is killed after
  150s on a third, where the hoisted form costs about a minute for the whole file. The `have hα`
  inside `ComplexAnalytic.coverAnalytification_congr` is that, and it is not style.

  **It is a cost and not a non-termination**, and until 2026-08-31 the first sentence above said
  *"does not elaborate at all"*, which is stronger than any of those three runs shows. Under
  `set_option maxHeartbeats 0` this module **builds** with the inline form, in 489s against 60s as
  shipped — so what the `have` buys is about eight times the file. `lakefile.toml` sets no
  `maxHeartbeats`, so the budget all three failures met is Lean's default 200000, and the figure
  of a million that `Oka/AnalyticSpace/Glue.lean` gave for the same seam named a budget nobody
  set. See that file for the same correction from the other side.
* **`ComplexAnalytic.coverAnalytification_polyDiagOne` needs no such thing, and this section said
  it did.** Until 2026-08-31 the bullet here read *"with the six `Prop` arguments left to
  unification the application times out, and with all of `poly`, `poly'`, `glue`, `glue'` and the
  six named it is immediate"*. It does not: deleting **every** named argument from that proof,
  leaving `coverAnalytification_congr` applied to its two explicit hypotheses, builds the module
  under `lake build --wfail` in 55s against 61s with them, which is noise. The named arguments
  have gone with the claim. The timeout is real one level up — it is the bullet above — and
  fixing it there is what made this workaround unnecessary; nothing re-tested it until the branch
  was reviewed. **A measured claim that no longer reproduces is worse than no claim**, which is
  why the retraction is here rather than a silent deletion.

## Main definitions

- `ComplexAnalytic.glueDiagOne`: **a cover datum's `glue` carried to its diagonal-normalised
  form.** Off the diagonal it is a `cast` of the original — `cast` rather than a conjugation by
  `CategoryTheory.eqToIso`, because `cast_heq` is then the whole of
  `ComplexAnalytic.heq_glueDiagOne` — and on the diagonal it is `CategoryTheory.eqToIso`, which
  nothing below reads.

## Main results

- `ComplexAnalytic.coverGlueData'_congr`, `ComplexAnalytic.coverGlueData_congr` and
  `ComplexAnalytic.coverAnalytification_congr`: **two cover data that agree off the diagonal have
  the same glue datum, and glue to the same analytic space.** The hypotheses are exactly
  `poly i j = poly' i j` and `HEq (glue i j) (glue' i j)` at `i ≠ j`; nothing is asked at `i = i`.
- `ComplexAnalytic.hrange_congr` and `ComplexAnalytic.hcocycle_congr`: **the two geometric
  hypotheses transport**, so the second datum is a datum whenever the first is. Both are stated
  only at distinct indices, which is why they transport at all.
- `ComplexAnalytic.hsymm_glueDiagOne`: and so does the symmetry hypothesis, including at the
  diagonal, where `CategoryTheory.eqToIso` of a proof of `X = X` is its own inverse.
- `ComplexAnalytic.coverAnalytification_polyDiagOne`: **a cover datum and its diagonal-normalised
  form glue to the same analytic space**, with the normalised datum's three hypotheses supplied
  rather than assumed. This is the statement `Oka/Analytification/CrossMemberDatum.lean` names as
  what a consumer of `ComplexAnalytic.refineDatumPoly` will need.

## What is not here

* **No claim that `ComplexAnalytic.refineDatumPoly`'s correctness depends on this.** It does not,
  as far as anything compiled says: a refined datum's overlaps are built from
  `ComplexAnalytic.polyDiagOne` directly, and `ComplexAnalytic.refineDatumPoly_of_eq` lands on
  `ComplexAnalytic.refinePoly`, which `Oka/Analytification/CoverRefinement.lean` already works
  with. What the statement above buys is a *route*: a proof that a refined cover refines the same
  space may factor through the normalised datum, and if it does, this is the step it needs. **No
  such proof exists and this file is not evidence that one will take that route.**
* **Nothing about `ComplexAnalytic.refineDatumPoly` itself**, and no refined datum: `glue`,
  `hrange`, `hsymm` and `hcocycle` for a cross-member refinement are taxis #1287's and are
  untouched *here*. **This bullet said they were untouched, without the last word, and three of
  the four have since been built or proved on that thread** — `ComplexAnalytic.refineDatumGlue`,
  `ComplexAnalytic.refineDatumGlue_symm` and `ComplexAnalytic.refineDatumHrange`, the last from
  two conditions `Oka/Analytification/RefineDatumGlueData.lean` adopts and shows equivalent to
  it. **The count is now four of four**: `hcocycle` is stated in that file and proved in
  `Oka/Analytification/RefineDatumCocycle.lean`. Nothing in *this* file moved.
* **No converse.** Nothing here says two data whose glued spaces agree must agree off the
  diagonal, and nothing needs it.
* **No `Iso`.** The conclusions are equalities of `ComplexAnalytic.AnalyticSpace`, which is what
  the `HEq` route gives and is stronger than an isomorphism; a caller who wants a morphism gets it
  from `CategoryTheory.eqToHom`.
-/

open CategoryTheory AlgebraicGeometry

universe u

namespace ComplexAnalytic

variable {J : Type u} {obj : J → Presentation.{u}}
  {poly poly' : ∀ i : J, J → MvPolynomial (ULift.{u} (Fin (obj i).n)) ℂ}

/-! ### The pieces cut out by one polynomial

Each of these says that a construction of `Oka/Analytification/AffineCover.lean` reads `poly` only
at the pair it is indexed by. The proofs are all the same: abstract that value as a variable, and
`rintro … rfl`.
-/

/-- **The overlap presentation depends on `poly` only at its own pair.** -/
theorem coverOverlap_congr {i j : J} (h : poly i j = poly' i j) :
    coverOverlap.{u} obj poly i j = coverOverlap.{u} obj poly' i j :=
  congrArg (fun p ↦ (⟨(obj i).n + 1, (obj i).k + 1,
    localisationPresentation.{u} (obj i).g p⟩ : Presentation.{u})) h

/-- **So does its analytification.** -/
theorem coverOverlapSpace_congr {i j : J} (h : poly i j = poly' i j) :
    coverOverlapSpace.{u} obj poly i j = coverOverlapSpace.{u} obj poly' i j :=
  congrArg (fun p ↦ (AnalyticSpace.analytification.{u}
    (localisationPresentation.{u} (obj i).g p)).toLocallyRingedSpace) h

/-- **So does the open subset `D(f_ij)` of the `i`-th member.** -/
theorem coverOpen_congr {i j : J} (h : poly i j = poly' i j) :
    coverOpen.{u} obj poly i j = coverOpen.{u} obj poly' i j :=
  congrArg (localisationOpen.{u} (obj i).g) h

/-- **So does that open as a space**, which is a glue datum's `V (i, j)`. -/
theorem coverPart_congr {i j : J} (h : poly i j = poly' i j) :
    coverPart.{u} obj poly i j = coverPart.{u} obj poly' i j :=
  congrArg (fun p ↦ (coverSpace.{u} obj i).restrict
    (localisationOpen.{u} (obj i).g p).isOpenEmbedding) h

/-- **The triple overlap depends on `poly` at the two pairs it is cut out by.** -/
theorem coverTriplePart_congr {i j k : J} (hij : poly i j = poly' i j)
    (hik : poly i k = poly' i k) :
    coverTriplePart.{u} obj poly i j k = coverTriplePart.{u} obj poly' i j k := by
  have key : ∀ U U' V V' : TopologicalSpace.Opens (coverSpace.{u} obj i), U = U' → V = V' →
      (coverSpace.{u} obj i).restrict (U ⊓ V).isOpenEmbedding =
        (coverSpace.{u} obj i).restrict (U' ⊓ V').isOpenEmbedding := by
    rintro U U' V V' rfl rfl; rfl
  exact key _ _ _ _ (coverOpen_congr hij) (coverOpen_congr hik)

/-- **The inclusion of the overlap into the ambient member**, a glue datum's `f i j`.

`HEq` and not `Eq` from here on: the source moves with `poly`. -/
theorem heq_coverIncl {i j : J} (h : poly i j = poly' i j) :
    HEq (coverIncl.{u} obj poly i j) (coverIncl.{u} obj poly' i j) := by
  have key : ∀ p q : MvPolynomial (ULift.{u} (Fin (obj i).n)) ℂ, p = q →
      HEq ((coverSpace.{u} obj i).ofRestrict (localisationOpen.{u} (obj i).g p).isOpenEmbedding)
        ((coverSpace.{u} obj i).ofRestrict
          (localisationOpen.{u} (obj i).g q).isOpenEmbedding) := by
    rintro p q rfl; rfl
  exact key _ _ h

/-- **The comparison of the two spellings of the overlap.** -/
theorem heq_coverOverlapIso {i j : J} (h : poly i j = poly' i j) :
    HEq (coverOverlapIso.{u} obj poly i j) (coverOverlapIso.{u} obj poly' i j) := by
  have key : ∀ p q : MvPolynomial (ULift.{u} (Fin (obj i).n)) ℂ, p = q →
      HEq (AnalyticSpace.forgetToLocallyRingedSpace.{u}.mapIso (localisationIso.{u} (obj i).g p))
        (AnalyticSpace.forgetToLocallyRingedSpace.{u}.mapIso
          (localisationIso.{u} (obj i).g q)) := by
    rintro p q rfl; rfl
  exact key _ _ h

/-- **The inclusion of a triple overlap into a double one.** -/
theorem heq_coverTripleIncl {i j k : J} (hij : poly i j = poly' i j)
    (hik : poly i k = poly' i k) :
    HEq (coverTripleIncl.{u} obj poly i j k) (coverTripleIncl.{u} obj poly' i j k) := by
  have key : ∀ U U' V V' : TopologicalSpace.Opens (coverSpace.{u} obj i), U = U' → V = V' →
      ∀ (h : U ⊓ V ≤ U) (h' : U' ⊓ V' ≤ U'),
      HEq ((coverSpace.{u} obj i).restrictLE h) ((coverSpace.{u} obj i).restrictLE h') := by
    rintro U U' V V' rfl rfl h h'; rfl
  exact key _ _ _ _ (coverOpen_congr hij) (coverOpen_congr hik) _ _

/-! ### The pieces that read `glue` -/

variable {glue : ∀ i j : J, coverOverlap.{u} obj poly i j ≅ coverOverlap.{u} obj poly j i}
  {glue' : ∀ i j : J, coverOverlap.{u} obj poly' i j ≅ coverOverlap.{u} obj poly' j i}

/-- **The given algebra isomorphism, analytified.**

The two presentations are abstracted as variables, so that `HEq (glue i j) (glue' i j)` becomes an
`Eq` before `MvPolynomial.rename` or the analytification functor is looked at. -/
theorem heq_coverGlueIso {i j : J} (hij : poly i j = poly' i j) (hji : poly j i = poly' j i)
    (hg : HEq (glue i j) (glue' i j)) :
    HEq (coverGlueIso.{u} obj poly glue i j) (coverGlueIso.{u} obj poly' glue' i j) := by
  have key : ∀ P P' Q Q' : Presentation.{u}, P = P' → Q = Q' →
      ∀ (g : P ≅ Q) (g' : P' ≅ Q'), HEq g g' →
      HEq (AnalyticSpace.forgetToLocallyRingedSpace.{u}.mapIso
            (analytificationFunctor.{u}.mapIso g))
        (AnalyticSpace.forgetToLocallyRingedSpace.{u}.mapIso
          (analytificationFunctor.{u}.mapIso g')) := by
    rintro P P' Q Q' rfl rfl g g' hg
    rw [eq_of_heq hg]
  exact key _ _ _ _ (coverOverlap_congr hij) (coverOverlap_congr hji) _ _ hg

/-- **The transition isomorphism of the glue datum.**

The three-term `CategoryTheory.Iso.trans` is abstracted whole. Spelling its factors out instead —
`AnalyticSpace.forgetToLocallyRingedSpace.mapIso` of a `ComplexAnalytic.localisationIso` at each
end — exhausts the heartbeat budget at `isDefEq`, which is the same cost
`Oka/Analytification/AffineCover.lean`'s docstring names as the reason
`ComplexAnalytic.coverOverlapIso` is a definition of its own. -/
theorem heq_coverTransition {i j : J} (hij : poly i j = poly' i j) (hji : poly j i = poly' j i)
    (hg : HEq (glue i j) (glue' i j)) :
    HEq (coverTransition.{u} obj poly glue i j) (coverTransition.{u} obj poly' glue' i j) := by
  have key : ∀ A A' B B' C C' D D' : LocallyRingedSpace.{u}, A = A' → B = B' → C = C' → D = D' →
      ∀ (e₁ : A ≅ B) (e₁' : A' ≅ B'), HEq e₁ e₁' → ∀ (e₂ : A ≅ C) (e₂' : A' ≅ C'), HEq e₂ e₂' →
      ∀ (e₃ : C ≅ D) (e₃' : C' ≅ D'), HEq e₃ e₃' →
      HEq (e₁.symm ≪≫ e₂ ≪≫ e₃) (e₁'.symm ≪≫ e₂' ≪≫ e₃') := by
    rintro A A' B B' C C' D D' rfl rfl rfl rfl e₁ e₁' h₁ e₂ e₂' h₂ e₃ e₃' h₃
    rw [eq_of_heq h₁, eq_of_heq h₂, eq_of_heq h₃]
  exact key _ _ _ _ _ _ _ _ (coverOverlapSpace_congr hij) (coverPart_congr hij)
    (coverOverlapSpace_congr hji) (coverPart_congr hji) _ _ (heq_coverOverlapIso hij) _ _
    (heq_coverGlueIso hij hji hg) _ _ (heq_coverOverlapIso hji)

/-- **The transition followed into the ambient member**, which is what `hrange` is about. -/
theorem heq_coverTransitionHom {i j : J} (hij : poly i j = poly' i j)
    (hji : poly j i = poly' j i) (hg : HEq (glue i j) (glue' i j)) :
    HEq (coverTransitionHom.{u} obj poly glue i j)
      (coverTransitionHom.{u} obj poly' glue' i j) := by
  have key : ∀ A A' B B' C C' : LocallyRingedSpace.{u}, A = A' → B = B' → C = C' →
      ∀ (e : A ≅ B) (e' : A' ≅ B'), HEq e e' → ∀ (m : B ⟶ C) (m' : B' ⟶ C'), HEq m m' →
      HEq (e.hom ≫ m) (e'.hom ≫ m') := by
    rintro A A' B B' C C' rfl rfl rfl e e' he m m' hm
    rw [eq_of_heq he, eq_of_heq hm]
  exact key _ _ _ _ _ _ (coverPart_congr hij) (coverPart_congr hji) rfl _ _
    (heq_coverTransition hij hji hg) _ _ (heq_coverIncl hji)

/-- **The transition on triple overlaps.**

`AlgebraicGeometry.LocallyRingedSpace.liftRestrict`'s third argument is a `Prop`, so it needs no
hypothesis: once the source, the morphism and the target open are matched, proof irrelevance
closes the goal. That is also why `hrange` and `hrange'` are unnamed here. -/
theorem heq_coverTriple {hrange hrange'} {i j k : J} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (eij : poly i j = poly' i j) (eik : poly i k = poly' i k) (eji : poly j i = poly' j i)
    (ejk : poly j k = poly' j k) (hg : HEq (glue i j) (glue' i j)) :
    HEq (coverTriple.{u} obj poly glue hrange i j k hij hik hjk)
      (coverTriple.{u} obj poly' glue' hrange' i j k hij hik hjk) := by
  have keyc : ∀ A A' B B' C : LocallyRingedSpace.{u}, A = A' → B = B' →
      ∀ (f : A ⟶ B) (f' : A' ⟶ B'), HEq f f' → ∀ (m : B ⟶ C) (m' : B' ⟶ C), HEq m m' →
      HEq (f ≫ m) (f' ≫ m') := by
    rintro A A' B B' C rfl rfl f f' hf m m' hm
    rw [eq_of_heq hf, eq_of_heq hm]
  have key : ∀ Z Z' X : LocallyRingedSpace.{u}, Z = Z' →
      ∀ (φ : Z ⟶ X) (φ' : Z' ⟶ X), HEq φ φ' →
      ∀ U U' : TopologicalSpace.Opens X, U = U' →
      ∀ (h : Set.range φ.base ⊆ (U : Set X)) (h' : Set.range φ'.base ⊆ (U' : Set X)),
      HEq (LocallyRingedSpace.liftRestrict φ U h) (LocallyRingedSpace.liftRestrict φ' U' h') := by
    rintro Z Z' X rfl φ φ' hφ U U' rfl h h'
    obtain rfl := eq_of_heq hφ
    rfl
  refine key _ _ _ (coverTriplePart_congr eij eik) _ _
    (keyc _ _ _ _ _ (coverTriplePart_congr eij eik) (coverPart_congr eij) _ _
      (heq_coverTripleIncl eij eik) _ _ (heq_coverTransitionHom eij eji hg)) _ _ ?_ _ _
  exact congrArg₂ (· ⊓ ·) (coverOpen_congr ejk) (coverOpen_congr eji)

/-! ### The two geometric hypotheses transport -/

/-- **`hrange` transports**: it is stated only at distinct triples, and there the two data agree.

Without that restriction there would be nothing to transport, since `poly i i` is exactly what the
two data are allowed to differ in. -/
theorem hrange_congr (hoff : ∀ i j : J, i ≠ j → poly i j = poly' i j)
    (hg : ∀ i j : J, i ≠ j → HEq (glue i j) (glue' i j))
    (hrange : ∀ i j k : J, i ≠ j → i ≠ k → j ≠ k →
      Set.range (coverTripleIncl.{u} obj poly i j k ≫
          coverTransitionHom.{u} obj poly glue i j).base ⊆
        (coverOpen.{u} obj poly j k : Set (coverSpace.{u} obj j))) :
    ∀ i j k : J, i ≠ j → i ≠ k → j ≠ k →
      Set.range (coverTripleIncl.{u} obj poly' i j k ≫
          coverTransitionHom.{u} obj poly' glue' i j).base ⊆
        (coverOpen.{u} obj poly' j k : Set (coverSpace.{u} obj j)) := by
  intro i j k hij hik hjk
  have keyc : ∀ A A' B B' C : LocallyRingedSpace.{u}, A = A' → B = B' →
      ∀ (f : A ⟶ B) (f' : A' ⟶ B'), HEq f f' → ∀ (m : B ⟶ C) (m' : B' ⟶ C), HEq m m' →
      HEq (f ≫ m) (f' ≫ m') := by
    rintro A A' B B' C rfl rfl f f' hf m m' hm
    rw [eq_of_heq hf, eq_of_heq hm]
  have key : ∀ A A' : LocallyRingedSpace.{u}, A = A' →
      ∀ (m : A ⟶ coverSpace.{u} obj j) (m' : A' ⟶ coverSpace.{u} obj j), HEq m m' →
      ∀ U U' : TopologicalSpace.Opens (coverSpace.{u} obj j), U = U' →
      Set.range m.base ⊆ (U : Set (coverSpace.{u} obj j)) →
      Set.range m'.base ⊆ (U' : Set (coverSpace.{u} obj j)) := by
    rintro A A' rfl m m' hm U U' rfl h
    rwa [← eq_of_heq hm]
  exact key _ _ (coverTriplePart_congr (hoff i j hij) (hoff i k hik)) _ _
    (keyc _ _ _ _ _ (coverTriplePart_congr (hoff i j hij) (hoff i k hik))
      (coverPart_congr (hoff i j hij)) _ _
      (heq_coverTripleIncl (hoff i j hij) (hoff i k hik)) _ _
      (heq_coverTransitionHom (hoff i j hij) (hoff j i hij.symm) (hg i j hij))) _ _
    (coverOpen_congr (hoff j k hjk)) (hrange i j k hij hik hjk)

/-- **`hcocycle` transports too**, and for the same reason: three distinct indices. -/
theorem hcocycle_congr (hoff : ∀ i j : J, i ≠ j → poly i j = poly' i j)
    (hg : ∀ i j : J, i ≠ j → HEq (glue i j) (glue' i j)) {hrange hrange'}
    (hcocycle : ∀ i j k : J, ∀ hij : i ≠ j, ∀ hik : i ≠ k, ∀ hjk : j ≠ k,
      coverTriple.{u} obj poly glue hrange i j k hij hik hjk ≫
        coverTriple.{u} obj poly glue hrange j k i hjk hij.symm hik.symm ≫
        coverTriple.{u} obj poly glue hrange k i j hik.symm hjk.symm hij = 𝟙 _) :
    ∀ i j k : J, ∀ hij : i ≠ j, ∀ hik : i ≠ k, ∀ hjk : j ≠ k,
      coverTriple.{u} obj poly' glue' hrange' i j k hij hik hjk ≫
        coverTriple.{u} obj poly' glue' hrange' j k i hjk hij.symm hik.symm ≫
        coverTriple.{u} obj poly' glue' hrange' k i j hik.symm hjk.symm hij = 𝟙 _ := by
  intro i j k hij hik hjk
  have keyc : ∀ A A' B B' C C' : LocallyRingedSpace.{u}, A = A' → B = B' → C = C' →
      ∀ (f : A ⟶ B) (f' : A' ⟶ B'), HEq f f' → ∀ (m : B ⟶ C) (m' : B' ⟶ C'), HEq m m' →
      HEq (f ≫ m) (f' ≫ m') := by
    rintro A A' B B' C C' rfl rfl rfl f f' hf m m' hm
    rw [eq_of_heq hf, eq_of_heq hm]
  have key : ∀ A A' : LocallyRingedSpace.{u}, A = A' → ∀ (m : A ⟶ A) (m' : A' ⟶ A'), HEq m m' →
      m = 𝟙 A → m' = 𝟙 A' := by
    rintro A A' rfl m m' hm h
    rwa [← eq_of_heq hm]
  refine key _ _ (coverTriplePart_congr (hoff i j hij) (hoff i k hik)) _ _ ?_
    (hcocycle i j k hij hik hjk)
  refine keyc _ _ _ _ _ _ (coverTriplePart_congr (hoff i j hij) (hoff i k hik))
    (coverTriplePart_congr (hoff j k hjk) (hoff j i hij.symm))
    (coverTriplePart_congr (hoff i j hij) (hoff i k hik)) _ _
    (heq_coverTriple hij hik hjk (hoff i j hij) (hoff i k hik) (hoff j i hij.symm)
      (hoff j k hjk) (hg i j hij)) _ _ ?_
  exact keyc _ _ _ _ _ _ (coverTriplePart_congr (hoff j k hjk) (hoff j i hij.symm))
    (coverTriplePart_congr (hoff k i hik.symm) (hoff k j hjk.symm))
    (coverTriplePart_congr (hoff i j hij) (hoff i k hik)) _ _
    (heq_coverTriple hjk hij.symm hik.symm (hoff j k hjk) (hoff j i hij.symm)
      (hoff k j hjk.symm) (hoff k i hik.symm) (hg j k hjk)) _ _
    (heq_coverTriple hik.symm hjk.symm hij (hoff k i hik.symm) (hoff k j hjk.symm)
      (hoff i k hik) (hoff i j hij) (hg k i hik.symm))

/-! ### The glue datum, and the space -/

/-- **Two cover data that agree off the diagonal have the same glue datum.**

`CategoryTheory.GlueData'.ext_of_heq` at five fields, of which `J` and `U` do not move at all —
the members are `ComplexAnalytic.coverSpace obj`, which never mentions `poly`. `V` is the only
one that comes out as an `Eq`, and only because `CategoryTheory.GlueData'.V` takes `i ≠ j` as an
argument, so the hypothesis is in scope at the point where it is needed. -/
theorem coverGlueData'_congr (hoff : ∀ i j : J, i ≠ j → poly i j = poly' i j)
    (hg : ∀ i j : J, i ≠ j → HEq (glue i j) (glue' i j))
    {hrange hrange' hsymm hsymm' hcocycle hcocycle'} :
    coverGlueData'.{u} obj poly glue hrange hsymm hcocycle =
      coverGlueData'.{u} obj poly' glue' hrange' hsymm' hcocycle' := by
  refine GlueData'.ext_of_heq rfl HEq.rfl ?_ ?_ ?_
  · exact heq_of_eq (funext fun i ↦ funext fun j ↦ funext fun hij ↦ coverPart_congr (hoff i j hij))
  · refine Function.hfunext rfl fun i i' hi ↦ ?_
    obtain rfl := eq_of_heq hi
    refine Function.hfunext rfl fun j j' hj ↦ ?_
    obtain rfl := eq_of_heq hj
    refine Function.hfunext rfl fun hij hij' _ ↦ ?_
    exact heq_coverIncl (hoff i j hij)
  · refine Function.hfunext rfl fun i i' hi ↦ ?_
    obtain rfl := eq_of_heq hi
    refine Function.hfunext rfl fun j j' hj ↦ ?_
    obtain rfl := eq_of_heq hj
    refine Function.hfunext rfl fun hij hij' _ ↦ ?_
    have key : ∀ A A' B B' : LocallyRingedSpace.{u}, A = A' → B = B' →
        ∀ (e : A ≅ B) (e' : A' ≅ B'), HEq e e' → HEq e.hom e'.hom := by
      rintro A A' B B' rfl rfl e e' he
      rw [eq_of_heq he]
    exact key _ _ _ _ (coverPart_congr (hoff i j hij)) (coverPart_congr (hoff j i hij.symm)) _ _
      (heq_coverTransition (hoff i j hij) (hoff j i hij.symm) (hg i j hij))

/-- **And the same glue datum of locally ringed spaces.** -/
theorem coverGlueData_congr (hoff : ∀ i j : J, i ≠ j → poly i j = poly' i j)
    (hg : ∀ i j : J, i ≠ j → HEq (glue i j) (glue' i j))
    {hrange hrange' hsymm hsymm' hcocycle hcocycle'} :
    coverGlueData.{u} obj poly glue hrange hsymm hcocycle =
      coverGlueData.{u} obj poly' glue' hrange' hsymm' hcocycle' :=
  LocallyRingedSpace.GlueData.ext_of_toGlueData
    (congrArg GlueData.ofGlueData' (coverGlueData'_congr hoff hg))

/-- **Two cover data that agree off the diagonal glue to the same analytic space.**

The headline of this file. Nothing is asked at `i = i`: `poly i i` and `glue i i` may be anything
at all, on either side. -/
theorem coverAnalytification_congr (hoff : ∀ i j : J, i ≠ j → poly i j = poly' i j)
    (hg : ∀ i j : J, i ≠ j → HEq (glue i j) (glue' i j))
    {hrange hrange' hsymm hsymm' hcocycle hcocycle'} :
    coverAnalytification.{u} obj poly glue hrange hsymm hcocycle =
      coverAnalytification.{u} obj poly' glue' hrange' hsymm' hcocycle' := by
  have hd := coverGlueData_congr hoff hg (hrange := hrange) (hrange' := hrange')
    (hsymm := hsymm) (hsymm' := hsymm') (hcocycle := hcocycle) (hcocycle' := hcocycle')
  have hα : HEq (fun i : J ↦ (AnalyticSpace.analytification.{u} (obj i).g).algebraMap)
      (fun i : J ↦ (AnalyticSpace.analytification.{u} (obj i).g).algebraMap) := HEq.rfl
  exact AnalyticSpace.ofGlueDataCLinear_congr hd hα

end ComplexAnalytic

namespace ComplexAnalytic

variable {J : Type u} {obj : J → Presentation.{u}}
  {poly : ∀ i : J, J → MvPolynomial (ULift.{u} (Fin (obj i).n)) ℂ}

/-! ### The diagonal-normalised datum -/

open Classical in
/-- **A cover datum's `glue`, carried to its diagonal-normalised form.**

Off the diagonal `ComplexAnalytic.polyDiagOne` changes nothing, so the two overlap presentations
are equal and the original isomorphism is carried by a `cast`. On the diagonal there is no
original to carry — `poly i i` has been replaced — and `CategoryTheory.eqToIso` of the equality
`i = j` forces is the choice; `ComplexAnalytic.hsymm_glueDiagOne` is the only thing that reads it,
and the glue datum reads it not at all.

**A `cast` and not a conjugation by two `CategoryTheory.eqToIso`s.** The two are the same
isomorphism, but `cast_heq` is a one-line proof of `ComplexAnalytic.heq_glueDiagOne`, which is the
hypothesis everything below consumes, where the conjugated form would need the transport unwound
at each end. -/
noncomputable def glueDiagOne
    (glue : ∀ i j : J, coverOverlap.{u} obj poly i j ≅ coverOverlap.{u} obj poly j i) (i j : J) :
    coverOverlap.{u} obj (polyDiagOne.{u} obj poly) i j ≅
      coverOverlap.{u} obj (polyDiagOne.{u} obj poly) j i :=
  if h : i = j then eqToIso (by cases h; rfl)
  else cast (by
    rw [coverOverlap_congr (poly' := polyDiagOne.{u} obj poly)
        (polyDiagOne_of_ne.{u} obj poly h).symm,
      coverOverlap_congr (poly' := polyDiagOne.{u} obj poly)
        (polyDiagOne_of_ne.{u} obj poly (Ne.symm h)).symm]) (glue i j)

/-- **Off the diagonal it is the original isomorphism**, which is the whole of what the
congruence above asks for. -/
theorem heq_glueDiagOne
    (glue : ∀ i j : J, coverOverlap.{u} obj poly i j ≅ coverOverlap.{u} obj poly j i)
    {i j : J} (h : i ≠ j) : HEq (glueDiagOne.{u} glue i j) (glue i j) := by
  have hne : glueDiagOne.{u} glue i j = cast _ (glue i j) := dif_neg h
  rw [hne]
  exact cast_heq _ _

/-- **On the diagonal it is `CategoryTheory.eqToIso` of a proof that `i = j` forces.** -/
theorem glueDiagOne_of_eq
    (glue : ∀ i j : J, coverOverlap.{u} obj poly i j ≅ coverOverlap.{u} obj poly j i)
    {i j : J} (h : i = j) :
    glueDiagOne.{u} glue i j = eqToIso (by cases h; rfl) :=
  dif_pos h

/-- **The symmetry hypothesis transports**, including at the diagonal.

The two cases are different arguments and neither covers the other. Off the diagonal the
transported isomorphism is the original one, so the original hypothesis is all that is used. On
the diagonal both sides are `CategoryTheory.eqToIso` of a proof of an equality of one object with
itself, and a proof of `X = X` is `rfl` by proof irrelevance — so the value is
`CategoryTheory.Iso.refl` and is its own inverse. This is the one place in the file where the
diagonal is looked at, and it is looked at because `hsymm` is the one hypothesis of a cover datum
that is quantified over every pair. -/
theorem hsymm_glueDiagOne
    (glue : ∀ i j : J, coverOverlap.{u} obj poly i j ≅ coverOverlap.{u} obj poly j i)
    (hsymm : ∀ i j : J, glue j i = (glue i j).symm) (i j : J) :
    glueDiagOne.{u} glue j i = (glueDiagOne.{u} glue i j).symm := by
  by_cases h : i = j
  · cases h
    rw [glueDiagOne_of_eq glue (rfl : i = i)]
    rfl
  · have key : ∀ A A' B B' : Presentation.{u}, A = A' → B = B' →
        ∀ (e : A ≅ B) (e' : A' ≅ B'), HEq e e' → HEq e.symm e'.symm := by
      rintro A A' B B' rfl rfl e e' he
      rw [eq_of_heq he]
    refine eq_of_heq (((heq_glueDiagOne glue (Ne.symm h)).trans
      (heq_of_eq (hsymm i j))).trans ?_)
    exact (key _ _ _ _ (coverOverlap_congr (poly' := polyDiagOne.{u} obj poly)
      (polyDiagOne_of_ne.{u} obj poly h).symm)
      (coverOverlap_congr (poly' := polyDiagOne.{u} obj poly)
        (polyDiagOne_of_ne.{u} obj poly (Ne.symm h)).symm) _ _
      (heq_glueDiagOne glue h).symm)

/-- **A cover datum and its diagonal-normalised form glue to the same analytic space.**

The statement `Oka/Analytification/CrossMemberDatum.lean` recorded as argued and not compiled,
in its section *Why normalising the diagonal is allowed, and it is not a new hypothesis on the
caller*, which now cites this declaration instead. The normalised datum's three hypotheses are
supplied and not assumed: `ComplexAnalytic.hrange_congr` and `ComplexAnalytic.hcocycle_congr`
transport because they are stated at distinct indices, and `ComplexAnalytic.hsymm_glueDiagOne`
covers the diagonal separately.

Nothing here is named against an elaborator budget: an earlier version of this proof named
`poly`, `poly'`, `glue`, `glue'` and all six `Prop` arguments against a timeout that does not
reproduce, and this file's module docstring records what was measured. -/
theorem coverAnalytification_polyDiagOne
    (glue : ∀ i j : J, coverOverlap.{u} obj poly i j ≅ coverOverlap.{u} obj poly j i)
    {hrange hsymm hcocycle} :
    coverAnalytification.{u} obj poly glue hrange hsymm hcocycle =
      coverAnalytification.{u} obj (polyDiagOne.{u} obj poly) (glueDiagOne.{u} glue)
        (hrange_congr (fun _ _ h ↦ (polyDiagOne_of_ne.{u} obj poly h).symm)
          (fun _ _ h ↦ (heq_glueDiagOne.{u} glue h).symm) hrange)
        (hsymm_glueDiagOne.{u} glue hsymm)
        (hcocycle_congr (fun _ _ h ↦ (polyDiagOne_of_ne.{u} obj poly h).symm)
          (fun _ _ h ↦ (heq_glueDiagOne.{u} glue h).symm) hcocycle) :=
  coverAnalytification_congr (fun _ _ h ↦ (polyDiagOne_of_ne.{u} obj poly h).symm)
    (fun _ _ h ↦ (heq_glueDiagOne.{u} glue h).symm)

end ComplexAnalytic
