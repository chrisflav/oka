/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.AnalyticSpace.DirectSummand
import Oka.AnalyticSpace.FiniteEtaleBaseChange

/-!
# A monomorphism of covers is injective on points, and the direct summand it cuts out

`Oka/AnalyticSpace/DirectSummand.lean` proves that a morphism of covers which is **injective on
points** exhibits its source as a direct summand of its target, and its `## What is not here`
named the missing half in terms until the push that added this file: *"A proof that a monomorphism
of covers is injective on points. That is the remaining obligation, and it is a theorem rather
than a formality — the classical argument makes the diagonal `A ⟶ A ×_B A` an isomorphism and
needs the fibre product."* That bullet now records the repair and keeps the retired wording as a
dated record. **The fibre product arrived in
`Oka/AnalyticSpace/FiniteEtaleBaseChange.lean`** — the base change of a finite étale morphism
along an arbitrary one — and this file spends it on that obligation.

## The argument, and it is shorter than the classical one

`A ×_B A` is the base change of `i` along itself. The two projections `p₁` and `p₂` satisfy
`p₁ ≫ i = p₂ ≫ i` because the square commutes, so a monomorphism `i` forces `p₁ = p₂`. **That is
already the whole of it**, because the carrier of the fibre product is
`Function.Pullback i.base i.base` on the nose: a pair of points of `A` with the same image, whose
two projections are its two components. Two points with the same image give a point of the fibre
product at which `p₁` reads off the first and `p₂` the second, so they are equal.

**The diagonal is never built and no isomorphism is proved.** The classical route makes
`A ⟶ A ×_B A` an isomorphism and reads injectivity off that; what injectivity actually needs is
one equation between two morphisms, evaluated at one point.

## Where each hypothesis is spent

* **`[T2Space A.left]`, the source cover's total space**, is spent once, in
  `ComplexAnalytic.AnalyticSpace.baseChange`: the fibre product of `i` with itself is a base
  change *along* `i`, so it is `ComplexAnalytic.AnalyticSpace.isCoveringMap_baseChangeSndBase`
  that asks for it, and that lemma is where `Oka/AnalyticSpace/FiniteEtaleBaseChange.lean` says
  its own `[T2Space E]` goes.
* **`[T2Space B.left]`, the target cover's total space**, is spent once, in
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isFiniteEtale_left`, which is the cancellation
  that makes the underlying morphism of a morphism of covers finite étale.
  `Oka/AnalyticSpace/Finite.lean` records why that separation axiom is not an artefact of its
  proof.
* **Nothing is assumed of the base `X`** — not Hausdorff, not connected, not non-empty — and
  nothing is assumed of `i` beyond `Mono`.

**Neither hypothesis is derived from the other here, and neither is derived from a hypothesis on
the base — and at this file's meaning of *cover* neither can be.** The classical sentence *a cover
of a Hausdorff space has Hausdorff total space* is about `IsCoveringMap`, and a cover here is an
object of `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver`, whose structure morphism is
`ComplexAnalytic.AnalyticSpace.IsFiniteEtale`. **That class is not `IsCoveringMap`** and its own
docstring says so: unfolded it is `ComplexAnalytic.AnalyticSpace.IsFinite` — a closed underlying
map with finite fibres — together with `ComplexAnalytic.AnalyticSpace.IsLocalIso` — a local
homeomorphism whose stalk maps are isomorphisms — and the first three of those four conditions
are the whole of its topological content, the fourth saying nothing about points.
The fold of the real line with two origins onto `ℝ` has all three, and `ℝ` is Hausdorff while
the total space is not. **So no argument from the
topological content of `IsFiniteEtale` reaches `[T2Space A.left]` from a hypothesis on `X`**, and
both hypotheses below are asked for because at this reading they have to be.

**Under `IsCoveringMap` the classical sentence is true, and every route to `IsCoveringMap` from
finite étale data here asks the hypothesis it would discharge.** Its ingredient is Mathlib's
`IsCoveringMap.isSeparatedMap`, and its home would be `Oka/Topology/Covering/Basic.lean` beside
`IsCoveringMap.isClosedMap` rather than a file about analytic spaces. But of the declarations
under `Oka/` whose conclusion is `IsCoveringMap` — a comment-stripping walk over every one of
them, not a `grep` — the two that take an arbitrary finite étale morphism are
`ComplexAnalytic.AnalyticSpace.isCoveringMap_base_of_isFiniteEtale`, which asks `[T2Space X]` of
its source, and `ComplexAnalytic.AnalyticSpace.isCoveringMap_baseChangeSndBase`, which asks
`[T2Space E]` of its; both are proved from `IsClosedMap.isCoveringMap_of_isLocalHomeomorph`, whose
own `[T2Space E]` is the hypothesis that fold shows cannot be dropped. **So that
lemma's separation hypothesis has a witness too**, and its docstring — which reads *A closed local
homeomorphism with finite fibres out of a Hausdorff space is a covering map* and gives the reason
no connectedness of the target is needed — names none.

`Oka/AnalyticSpace/Hausdorff.lean` declares seven `T2Space` instances — `ℂ^ι` and `ℂ^n`, an open
subspace of `ℂ^n` and an open subspace of an arbitrary Hausdorff analytic space, a zero locus in
each of the two spellings, and the node — **and it is not the only file that declares one.**
Walking every tracked `.lean` with the same comment stripper, taking each `instance` head whose
conclusion is `T2Space` and reading the declaring module off `scripts/DumpOkaDecls.lean`'s rows
rather than off a path, one more turns up: `ComplexAnalytic.t2Space_analytification`
(`Oka/Analytification/Hausdorff.lean`).
**So none of the eight — the seven of that file and this one — removes either hypothesis
below**, and an instance that did would have to state at `IsFiniteEtale` what the fold refutes.

**This paragraph read *A cover of a Hausdorff space has Hausdorff total space; that is a
topological statement, and this repository's `T2Space` instances for analytic spaces are the seven
of `Oka/AnalyticSpace/Hausdorff.lean`*, said of those seven *none of which concludes anything
about the total space of a cover*, and ended *So both hypotheses are asked for, and
`Oka/AnalyticSpace/Hausdorff.lean` is where a later seat would put the instance that removes one*,
until 2026-09-07. Each of those three was false when written rather than falsified later, so this
is a correction and not one of this repository's dated records**: the first is false at
`IsFiniteEtale` and true at `IsCoveringMap`, which are not the same class; three of the instances
are declared outside the file named; and one of those three is a cover's total space.

## Main definitions

- `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.selfProd`: **the fibre product `A ×_B A` as an
  object of the category of covers of `X`**, structured over `X` through its *second* projection.
- `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.selfProdFst` and
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.selfProdSnd`: its two projections, as morphisms
  of covers.

## Main results

- `ComplexAnalytic.AnalyticSpace.injective_base_of_baseChangeFst_eq`: **the two projections
  agreeing is what injectivity is**, for a finite étale morphism of analytic spaces. This is the
  step that reads points off the carrier and the only one that does.
- `ComplexAnalytic.AnalyticSpace.injective_base_of_mono`: **a monomorphism of complex analytic
  spaces which is finite étale is injective on points.**
- `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.injective_base_left_of_mono`: **a monomorphism of
  covers is injective on points**, when the **target**'s total space is Hausdorff.

  **The first two of these read *with Hausdorff source* and the third read *when both total spaces
  are Hausdorff*, until 2026-09-14**, when `[T2Space E]` came out of
  `Oka/AnalyticSpace/FiniteEtaleBaseChange.lean`: the base change of `i` with itself stopped
  asking for it, the hypotheses became unused, and this repository's `unusedArguments` linter is
  what said so. The source's separation was never spent on anything else.
- `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.inducesIsoOnDirectSummand_of_mono`: **a
  monomorphism of covers exhibits its source as a direct summand of its target**, which is
  `Oka/AnalyticSpace/DirectSummand.lean`'s statement with its injectivity hypothesis discharged.

## What is not here

* **This is still not the `monoInducesIsoOnDirectSummand` field of
  `Mathlib/CategoryTheory/Galois/Basic.lean`'s `PreGaloisCategory`.** That field asks for the
  summand at every monomorphism and under **no** hypothesis whatever; the last result below asks
  for `[T2Space B.left]`. What this file removes from the gap is the injectivity hypothesis and
  nothing else, and that one separation hypothesis is what is left.

  **This bullet named `[T2Space A.left]` and `[T2Space B.left]` and closed *the two separation
  hypotheses are what is left*, until 2026-09-14**, when the source's became unused; the gap is
  one hypothesis narrower and is still a gap.
* **No `PreGaloisCategory` instance**, and nothing here bears on the other fields: base change
  over a general cospan of morphisms *of covers*, quotients by finite group actions, and the
  preservation of epimorphisms by a fibre functor are each untouched.
* **Nothing about Hausdorffness.** That a cover of a Hausdorff analytic space has Hausdorff total
  space is a topological statement this repository does not make, and deriving either hypothesis
  below from a hypothesis on `X` would need it. **Nothing is added here because at this file's
  meaning of *cover* that statement is false**, as `## Where each hypothesis is spent` argues from
  the fold of the real line with two origins onto `ℝ`; what is true is its `IsCoveringMap` form,
  and that is a statement about topological spaces whose home is
  `Oka/Topology/Covering/Basic.lean` and which this file does not prove either. **This sentence
  is unchanged and nothing in it is retired** — the clause added is the one that says why the gap
  will not be closed in the shape the sentence suggests.
* **The refutation is now inside the category, and the *Nothing about Hausdorffness* bullet is
  still exact.**
  `ComplexAnalytic.AnalyticSpace.exists_finiteEtaleOver_not_t2Space` exhibits an object of
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver` over
  `ComplexAnalytic.AnalyticSpace.complexAffineSpace 1` whose total space is not Hausdorff, over a
  base that is; it is the complex line with two origins, glued from two copies of `ℂ¹` along the
  complement of the origin. **Nothing in that bullet is retired and nothing here weakens it**:
  this repository still does not *make* the statement it names, and what changes is
  only the evidence against it — the argument from the fold of the real line with two origins is
  about a topological space that is not an analytic space, and this one is about an object of the
  category the two hypotheses below quantify over. **Neither hypothesis below is removed or
  weakened by it**, and no declaration of this file is touched.
* **No diagonal and no isomorphism `A ≅ A ×_B A`.** The classical argument's object is not built,
  so nothing below says the fibre product of a monomorphism with itself is its source.
* **Nothing about a general mono of analytic spaces.**
  `ComplexAnalytic.AnalyticSpace.injective_base_of_mono` asks its morphism to be finite étale; a
  monomorphism of analytic spaces which is not is not reached.

  **That clause read *finite étale with Hausdorff source, because that is what makes the base
  change exist*, until 2026-09-14**, when `[T2Space E]` came out of
  `Oka/AnalyticSpace/FiniteEtaleBaseChange.lean`. The reason it gave was exact: the separation
  axiom was there for the base change and for nothing else, so when the base change stopped
  asking for it the hypothesis became unused and the tree's `unusedArguments` linter refused the
  file until it was dropped.
-/

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

universe u

namespace ComplexAnalytic.AnalyticSpace

/-- **The two projections of `A ×_B A` agreeing is injectivity on points.**

The carrier of `ComplexAnalytic.AnalyticSpace.baseChange` is `Function.Pullback` of the two base
maps, so a pair of points with the same image *is* a point of it, and the two projections read off
its two components — `ComplexAnalytic.AnalyticSpace.base_baseChangeFst` and
`ComplexAnalytic.AnalyticSpace.base_baseChangeSnd` say so and the two `rfl`s below are the
subtype and product projections. **The hypothesis is an equation between morphisms and the
conclusion is about points**, which is the only place in this file where the two levels meet. -/
theorem injective_base_of_baseChangeFst_eq {A B : AnalyticSpace.{u}} (i : A ⟶ B)
    [IsFiniteEtale i] (h : baseChangeFst i i = baseChangeSnd i i) :
    Function.Injective i.toLRSHom.base := by
  intro a₁ a₂ hEq
  set z : baseChange i i := ⟨(a₁, a₂), hEq⟩ with hz
  have h1 : (baseChangeFst i i).toLRSHom.base z = a₁ := by rw [base_baseChangeFst]; rfl
  have h2 : (baseChangeSnd i i).toLRSHom.base z = a₂ := by rw [base_baseChangeSnd]; rfl
  rw [← h1, ← h2, h]

/-- **A monomorphism of complex analytic spaces which is finite étale is injective on points.**

`ComplexAnalytic.AnalyticSpace.baseChange_square` is the commuting square of the fibre product of
`i` with itself, and `CategoryTheory.cancel_mono` turns it into an equality of the two
projections.

**This statement asked `[T2Space A]` as well, until 2026-09-14**, when `[T2Space E]` came out of
`Oka/AnalyticSpace/FiniteEtaleBaseChange.lean`: the fibre product of `i` with itself stopped
asking for it and the hypothesis became unused. -/
theorem injective_base_of_mono {A B : AnalyticSpace.{u}} (i : A ⟶ B)
    [IsFiniteEtale i] [Mono i] :
    Function.Injective i.toLRSHom.base :=
  injective_base_of_baseChangeFst_eq i ((cancel_mono i).1 (baseChange_square i i))

variable {X : AnalyticSpace.{u}} {A B : FiniteEtaleOver.{u} X}

/-- **The fibre product `A ×_B A`, as an object of the category of covers of `X`.**

**It is structured over `X` through its second projection**, which is the one
`ComplexAnalytic.AnalyticSpace.isFiniteEtale_baseChangeSnd` makes finite étale; the first
projection is finite étale too, by the symmetry of this particular base change, but that is not
proved in this repository and is not needed. Composing with `A.hom` and
`ComplexAnalytic.AnalyticSpace.isFiniteEtale_comp` is the whole of the object's proof
obligation. -/
noncomputable def FiniteEtaleOver.selfProd (i : A ⟶ B) [T2Space (B.left : Type u)] :
    FiniteEtaleOver.{u} X :=
  haveI : IsFiniteEtale i.left := FiniteEtaleOver.isFiniteEtale_left i
  haveI : IsFiniteEtale (X := A.left) A.hom := A.prop
  haveI : IsFiniteEtale (baseChangeSnd i.left i.left) := isFiniteEtale_baseChangeSnd i.left i.left
  MorphismProperty.Over.mk _ (baseChangeSnd i.left i.left ≫ A.hom)
    (isFiniteEtale_comp (baseChangeSnd i.left i.left) A.hom)

variable (i : A ⟶ B) [T2Space (B.left : Type u)]

/-- **The second projection of `A ×_B A`, as a morphism of covers.** Its triangle over `X` is
`rfl`, because that projection is what the object was structured by. -/
noncomputable def FiniteEtaleOver.selfProdSnd : FiniteEtaleOver.selfProd i ⟶ A :=
  haveI : IsFiniteEtale i.left := FiniteEtaleOver.isFiniteEtale_left i
  MorphismProperty.Over.homMk (baseChangeSnd i.left i.left) rfl

/-- **The first projection of `A ×_B A`, as a morphism of covers.**

Its triangle over `X` is not `rfl` and is the one place the square is used at the level of
morphisms rather than of points: `A.hom` is `i.left ≫ B.hom` because `i` is a morphism over `X`,
and the two composites to `B.left` agree by
`ComplexAnalytic.AnalyticSpace.baseChange_square`. **The two `rfl`s after the rewrites are the
comma-category seam** — `A.hom`'s source is `(𝟭 ComplexAnalytic.AnalyticSpace).obj A.left` and not
`A.left`, and a rewrite leaves the goal in the second spelling. **The step before them is a
`change` and not a `show`**, for the reason `ComplexAnalytic.AnalyticSpace.mono_ofRestrict`'s
docstring gives: the two spellings are `rfl`-equal and not syntactically equal, so
`linter.style.show` fires and `lake build --wfail` turns the warning into an error, which
`lake env lean` on a scratch file does not. -/
noncomputable def FiniteEtaleOver.selfProdFst : FiniteEtaleOver.selfProd i ⟶ A :=
  haveI : IsFiniteEtale i.left := FiniteEtaleOver.isFiniteEtale_left i
  MorphismProperty.Over.homMk (baseChangeFst i.left i.left) (by
    have hw : i.left ≫ B.hom = A.hom := MorphismProperty.Over.w i
    change baseChangeFst i.left i.left ≫ A.hom = baseChangeSnd i.left i.left ≫ A.hom
    have e1 : baseChangeFst i.left i.left ≫ A.hom
        = (baseChangeFst i.left i.left ≫ i.left) ≫ B.hom := by rw [Category.assoc, hw]; rfl
    have e2 : baseChangeSnd i.left i.left ≫ A.hom
        = (baseChangeSnd i.left i.left ≫ i.left) ≫ B.hom := by rw [Category.assoc, hw]; rfl
    rw [e1, e2, baseChange_square])

/-- **A monomorphism of covers is injective on points**, when the target's total space is
Hausdorff.

**It asked both total spaces to be Hausdorff, until 2026-09-14**, when `[T2Space E]` came out of
`Oka/AnalyticSpace/FiniteEtaleBaseChange.lean` and the source's became unused. The target's is
what makes the underlying morphism of a morphism of covers finite étale, which is taxis #1772's
remaining half and is untouched.

This is the obligation `Oka/AnalyticSpace/DirectSummand.lean`'s `## What is not here` names.
`CategoryTheory.MorphismProperty.Over.Hom.ext` reduces the equality the monomorphism gives to the
equality of the underlying morphisms of analytic spaces, which is what
`ComplexAnalytic.AnalyticSpace.injective_base_of_baseChangeFst_eq` consumes. **The monomorphism is
in the category of covers and not in `ComplexAnalytic.AnalyticSpace`**, which is the hypothesis a
Galois-category axiom offers; both projections are morphisms over `X`, so the cancellation happens
where the axiom would use it. -/
theorem FiniteEtaleOver.injective_base_left_of_mono [Mono i] :
    Function.Injective (i.left.toLRSHom.base : A.left → B.left) := by
  haveI : IsFiniteEtale i.left := FiniteEtaleOver.isFiniteEtale_left i
  have h : FiniteEtaleOver.selfProdFst i = FiniteEtaleOver.selfProdSnd i :=
    (cancel_mono i).1 (MorphismProperty.Over.Hom.ext (baseChange_square i.left i.left))
  exact injective_base_of_baseChangeFst_eq i.left
    (congrArg (fun m : FiniteEtaleOver.selfProd i ⟶ A => m.left) h)

/-- **A monomorphism of covers exhibits its source as a direct summand of its target**: there is a
cover `Z` and a morphism `Z ⟶ B` whose binary cofan with `i` is a colimit.

`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.inducesIsoOnDirectSummand_of_injective` with its
injectivity hypothesis discharged by the theorem above. **This is the shape of the
`monoInducesIsoOnDirectSummand` field and it is not that field**: the field asks the same under no
hypothesis at all, and the one `T2Space` hypothesis here is what stands between them.

**This read *the two `T2Space` hypotheses here*, until 2026-09-14**, when the source's became
unused. -/
theorem FiniteEtaleOver.inducesIsoOnDirectSummand_of_mono [Mono i] :
    ∃ (Z : FiniteEtaleOver.{u} X) (u : Z ⟶ B),
      Nonempty (Limits.IsColimit (Limits.BinaryCofan.mk i u)) :=
  FiniteEtaleOver.inducesIsoOnDirectSummand_of_injective i
    (FiniteEtaleOver.injective_base_left_of_mono i)

end ComplexAnalytic.AnalyticSpace
