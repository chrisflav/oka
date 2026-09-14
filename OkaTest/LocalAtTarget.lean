/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka
import OkaTest.CoveringSpace

/-!
# The three classes are local on the target: what the criteria reach, and what they cost

`Oka/AnalyticSpace/LocalAtTarget.lean` says that `ComplexAnalytic.AnalyticSpace.IsFinite`,
`ComplexAnalytic.AnalyticSpace.IsLocalIso` and `ComplexAnalytic.AnalyticSpace.IsFiniteEtale`
descend along an open cover of the target. **A criterion quantified over open covers says nothing
until a cover is exhibited that the statements it generalises cannot reach**, and that is what this
file is for. Four things are checked and they are different things:

* **that the criteria are a generalisation** —
  `ComplexAnalytic.AnalyticSpace.isFinite_of_restrictHom_top` and
  `ComplexAnalytic.AnalyticSpace.isFiniteEtale_of_restrictHom_top` are *derived* from them at the
  one-member cover, rather than said in a docstring to follow from them;
* **that the class of covers reached is not exhausted by the one-member one** — two proper opens
  of the affine line, each non-empty and neither `⊤`, whose supremum is `⊤`;
* **that the empty index is admitted** — at `ι = Empty` the cover hypothesis forces the target's
  carrier to be empty and the restriction hypothesis is `fun i ↦ i.elim`, which is the decision
  `Oka/AnalyticSpace/LocalAtTarget.lean` records, compiled rather than asserted;
* **that the criteria have content in the negative direction** — the inclusion of the punctured
  line into the line is not finite, so *no* open cover of the line has all its restrictions
  finite, which is a statement about every cover and is not available from the `V = ⊤` theorems.

## Main results

- `ComplexAnalytic.isOpenCover_punctureCover`: **two proper non-empty opens cover the affine
  line.**
- `ComplexAnalytic.ne_top_punctureCover`: **neither member is `⊤`**, which is the whole point of
  exhibiting the pair.
- `ComplexAnalytic.exists_not_isFinite_restrictHom_puncturedInclCoveringSpaceHom`: **every open
  cover of the line has a member over which the punctured inclusion's restriction is not finite.**

## What is not here

* **No new library statement.** Everything below is an `example` or a consequence of one theorem
  of `Oka/AnalyticSpace/LocalAtTarget.lean` and one of `OkaTest/CoveringSpace.lean`; nothing here
  is cited from `Oka/`.
* **No `#synth` control, and the reason is that there is nothing to synthesise.** Taxis #1970's
  definition of done asks for one at both ends, on the model of the `HasPullbacks` control in
  `Oka/AnalyticSpace/FiniteEtaleBaseChange.lean`. **That model does not transfer**: **no
  declaration this push adds is an `instance`, none carries `@[instance]` and none declares a
  `class`**, so a planted `#synth` would have nothing to fail at and nothing to succeed at. The
  two `def`s below are `Opens`-valued and no instance search reaches either; every other
  declaration this push adds is a theorem, and some of those do *state* one of the three classes
  this file is about — `ComplexAnalytic.AnalyticSpace.IsFinite`,
  `ComplexAnalytic.AnalyticSpace.IsLocalIso` and `ComplexAnalytic.AnalyticSpace.IsFiniteEtale`
  are declared with `class` — which is why the clause above is about what a declaration *is* and
  not about what it concludes. **The control at the base end is
  `scripts/DumpOkaDecls.lean` instead** — the nine names are absent from its output at the
  branch's base and present at its head, which is a run and not a plant. This bullet is here
  because a definition-of-done item silently dropped reads exactly like one silently missed.
* **No cover over which a class is established that was not already known.** The positive
  instances below conclude things the tree has by other routes — `ComplexAnalytic.AnalyticSpace`'s
  identity is finite étale, and the two `…_of_restrictHom_top` theorems are already theorems.
  **A witness whose conclusion is *not* independently available needs a morphism whose finite
  étaleness is visible over the members of a cover and not globally**, and building one is a push
  of its own rather than a line of this file; the negative statement below is the one that is not
  available otherwise, and it is why it is here.
* **Nothing about the punctured line's second member.** The cover exhibited below is of
  `ℂ¹` by `{z ≠ 0}` and `{z ≠ 1}` and is unrelated to the punctured inclusion; the two live in
  the same file because they witness two different things about the same criteria.
-/

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry Topology

universe u

namespace ComplexAnalytic

noncomputable section

/-! ### The two `…_of_restrictHom_top` theorems are the one-member case -/

/-- **`ComplexAnalytic.AnalyticSpace.isFinite_of_restrictHom_top` follows from the cover
criterion**, at the family constantly `⊤` over `Unit`. Stated as an `example` because the library
statement exists with its own proof and is not replaced. -/
example {X Y : AnalyticSpace.{u}} (f : X ⟶ Y)
    (hfin : AnalyticSpace.IsFinite (AnalyticSpace.restrictHom f (⊤ : Y.Opens))) :
    AnalyticSpace.IsFinite f :=
  AnalyticSpace.isFinite_of_isOpenCover f
    (U := fun _ : Unit ↦ (⊤ : Y.Opens)) (by simp [IsOpenCover]) fun _ ↦ hfin

/-- **`ComplexAnalytic.AnalyticSpace.isFiniteEtale_of_restrictHom_top` follows the same way**, and
for the same reason is an `example`. -/
example {X Y : AnalyticSpace.{u}} (f : X ⟶ Y)
    (hfe : AnalyticSpace.IsFiniteEtale (AnalyticSpace.restrictHom f (⊤ : Y.Opens))) :
    AnalyticSpace.IsFiniteEtale f :=
  AnalyticSpace.isFiniteEtale_of_isOpenCover f
    (U := fun _ : Unit ↦ (⊤ : Y.Opens)) (by simp [IsOpenCover]) fun _ ↦ hfe

/-! ### A cover of the affine line by two proper opens -/

/-- **The complement of a point of the affine line**, as an open subspace: the locus where the one
coordinate differs from `c`. At `c = 0` this is the `punctured` of `OkaTest/HolomorphicMapOpen.lean`
and of `OkaTest/FiniteMorphism.lean`, and it is written again here rather than imported because the
point is the *pair* of them at two different `c` and neither of those files offers the family. -/
def punctureAt (c : ℂ) : (AnalyticSpace.complexAffineSpace.{u} 1).Opens where
  carrier := {z : ULift.{u} (Fin 1) → ℂ | z (ULift.up 0) ≠ c}
  is_open' := isOpen_compl_singleton.preimage (continuous_apply (ULift.up 0))

theorem mem_punctureAt_iff (c : ℂ) (z : ULift.{u} (Fin 1) → ℂ) :
    z ∈ punctureAt.{u} c ↔ z (ULift.up 0) ≠ c := Iff.rfl

/-- **The two opens `{z ≠ 0}` and `{z ≠ 1}`**, indexed so that they are a family and not a pair:
`TopologicalSpace.IsOpenCover` is a statement about an indexed family and the criteria of
`Oka/AnalyticSpace/LocalAtTarget.lean` quantify over one. -/
def punctureCover : Bool → (AnalyticSpace.complexAffineSpace.{u} 1).Opens :=
  fun b ↦ punctureAt.{u} (if b then 0 else 1)

theorem mem_punctureCover_iff (b : Bool) (z : ULift.{u} (Fin 1) → ℂ) :
    z ∈ punctureCover.{u} b ↔ z (ULift.up 0) ≠ (if b then 0 else 1) := Iff.rfl

/-- **They cover**: a point of the line has its coordinate different from `0` or different from
`1`, there being no complex number equal to both. -/
theorem isOpenCover_punctureCover : IsOpenCover punctureCover.{u} := by
  refine IsOpenCover.mk (le_antisymm le_top fun z _ ↦ ?_)
  by_cases h : (z : ULift.{u} (Fin 1) → ℂ) (ULift.up 0) = 0
  · refine Opens.mem_iSup.2 ⟨false, (mem_punctureCover_iff.{u} false z).2 ?_⟩
    rw [h]
    norm_num
  · exact Opens.mem_iSup.2 ⟨true, (mem_punctureCover_iff.{u} true z).2 (by simpa using h)⟩

/-- **Neither member is `⊤`**, which is what makes the pair a witness rather than a restatement:
the point whose coordinate is the punctured value is missing from it. -/
theorem ne_top_punctureCover (b : Bool) : punctureCover.{u} b ≠ ⊤ := by
  intro h
  have hmem : (fun _ ↦ if b then (0 : ℂ) else 1) ∈ punctureCover.{u} b := h ▸ trivial
  exact (mem_punctureCover_iff.{u} b _).1 hmem rfl

/-- **And neither is empty**, so the cover is by two proper non-empty opens: `1` avoids `{z ≠ 0}`'s
missing point and `0` avoids `{z ≠ 1}`'s. -/
theorem nonempty_punctureCover (b : Bool) :
    ((punctureCover.{u} b : (AnalyticSpace.complexAffineSpace.{u} 1).Opens) :
      Set (AnalyticSpace.complexAffineSpace.{u} 1)).Nonempty := by
  refine ⟨fun _ ↦ if b then 1 else 0, (mem_punctureCover_iff.{u} b _).2 ?_⟩
  cases b <;> norm_num

/-- **The criterion applies at that cover**, which is the instance the `V = ⊤` theorems cannot
reach: the identity is finite étale over each of two proper opens and therefore finite étale.

**Its conclusion is independently available** — the identity is an isomorphism and every
isomorphism is finite étale — and that is said here rather than left for a reader to notice: what
this checks is that the hypotheses of
`ComplexAnalytic.AnalyticSpace.isFiniteEtale_of_isOpenCover` are satisfiable at a cover no member
of which is `⊤`, not that its conclusion is new. -/
example : AnalyticSpace.IsFiniteEtale (𝟙 (AnalyticSpace.complexAffineSpace.{u} 1)) :=
  AnalyticSpace.isFiniteEtale_of_isOpenCover _ isOpenCover_punctureCover.{u} fun _ ↦ inferInstance

/-! ### The empty index, which the criteria admit and which the `V = ⊤` theorems cannot express -/

/-- **The criteria apply at an empty index, with no restriction hypothesis at all.**

`TopologicalSpace.IsOpenCover` at `ι = Empty` says `⊥ = ⊤` in `Y.Opens`, so the hypothesis is
available exactly when `Y`'s carrier is empty — and then every morphism into `Y` is finite étale,
because both classes are conditions at points and there are none. **`fun i ↦ i.elim` is the whole
of the restriction hypothesis**, which is what makes this the sharpest statement of the decision
`Oka/AnalyticSpace/LocalAtTarget.lean`'s `## What is not here` records: the empty index is admitted
rather than ruled out, and no proof there special-cases it.

**It is a real case and not a degenerate one.** The `V = ⊤` theorems cannot say it: `⊤` is a
one-member cover and its hypothesis is a statement about `restrictHom f ⊤`, which at an empty `Y`
is a morphism of empty spaces that a caller still has to supply. Here the caller supplies
nothing. -/
example {X Y : AnalyticSpace.{u}} (f : X ⟶ Y)
    (hU : IsOpenCover (fun _ : Empty ↦ (⊥ : Y.Opens))) : AnalyticSpace.IsFiniteEtale f :=
  AnalyticSpace.isFiniteEtale_of_isOpenCover f hU fun i ↦ i.elim

/-! ### The negative direction, which is the half the `V = ⊤` theorems do not give -/

/-- **No open cover of the affine line has every restriction of the punctured inclusion finite.**

`ComplexAnalytic.not_isFinite_puncturedInclCoveringSpaceHom` says that morphism is not finite, and
`ComplexAnalytic.AnalyticSpace.isFinite_of_isOpenCover` says it would be if every restriction
were. **This is a statement about every cover of the line**, including the ones with no member
equal to `⊤`, and nothing in this repository before the criterion could say it: the `V = ⊤`
theorems contrapose to a statement about the single open `⊤` and about no other. -/
theorem exists_not_isFinite_restrictHom_puncturedInclCoveringSpaceHom {ι : Type*}
    (U : ι → (AnalyticSpace.complexAffineSpace.{u} 1).Opens) (hU : IsOpenCover U) :
    ∃ i, ¬ AnalyticSpace.IsFinite (AnalyticSpace.restrictHom
      (AnalyticSpace.coveringSpaceHom (AnalyticSpace.complexAffineSpace.{u} 1)
        puncturedIncl.{u} isLocalHomeomorph_puncturedIncl.{u}) (U i)) := by
  by_contra hcon
  push Not at hcon
  exact not_isFinite_puncturedInclCoveringSpaceHom.{u}
    (AnalyticSpace.isFinite_of_isOpenCover _ hU hcon)

end

end ComplexAnalytic
