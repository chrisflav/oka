/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.AnalyticSpace.FiniteEtaleOver
import Oka.AnalyticSpace.Glue
import Oka.AnalyticSpace.Hausdorff
import Oka.Geometry.RingedSpace.PresheafedSpace.Double

/-!
# The complex line with two origins, and a finite étale cover with non-Hausdorff total space

`Oka/AnalyticSpace/Basic.lean` says twice that no separation axiom is imposed on
`ComplexAnalytic.AnalyticSpace`, and `Oka/AnalyticSpace/Hausdorff.lean` says that an analytic
space is not Hausdorff in general. **Until this file no declaration of this repository concluded
`¬ T2Space` of an analytic space.** At `d2ae161` five declarations concluded `¬ T2Space` of
anything, all five in `OkaTest/FiniteEtaleCancel.lean`: `TwoIndiscrete.not_t2Space` and
`LineTwoOrigins.not_t2Space`, whose whole conclusion it is, and
`TwoIndiscrete.not_isClosedMap_pt_of_isClosedMap_comp`,
`LineTwoOrigins.not_isClosedMap_inc_of_isClosedMap_comp` and
`LineTwoOrigins.not_isCoveringMap_fold_of_not_t2Space`, which conclude it as one conjunct of a
conjunction. Each of the five is about `TwoIndiscrete` or `LineTwoOrigins`, bare topological
spaces which no declaration of this repository makes an analytic space. Two instruments:
`git grep -nE '¬ *T2Space' -- Oka/ OkaTest/`, which returns six lines at that commit — those five
conclusions and one line of docstring prose, and not one of them a hypothesis — and
`git grep -n LineTwoOrigins -- '*.lean'`, whose hits outside the file that declares it are
all prose.

This file supplies the witness, and it supplies it in the form the question is actually asked in.
`ComplexAnalytic.AnalyticSpace.double X V` glues two copies of an analytic space `X` along an open
`V` — the locally ringed space is
`AlgebraicGeometry.LocallyRingedSpace.double`, promoted by
`ComplexAnalytic.AnalyticSpace.ofGlueDataCLinear` — and the fold down to `X` is **finite étale**.
At `X = ℂ¹` and `V = ℂ ∖ {0}` the double is the line with two origins, it is not Hausdorff, and
`ℂ¹` is.

## What that settles, and it is a hypothesis two theorems carry

`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.inducesIsoOnDirectSummand_of_mono` and
`…inducesIsoOnDirectSummand_of_injective` (`Oka/AnalyticSpace/MonoDirectSummand.lean`,
`Oka/AnalyticSpace/DirectSummand.lean`) each carry `[T2Space B.left]` — separation of the
**total space** of the target — where the `PreGaloisCategory` field of
`Mathlib/CategoryTheory/Galois/Basic.lean` they are modelled on asks for nothing.

**This paragraph said both carry `[T2Space A.left]` and `[T2Space B.left]`, until 2026-09-14.**
It was exact of neither: `…inducesIsoOnDirectSummand_of_injective` has asked only for the
target's since it was written, and `…inducesIsoOnDirectSummand_of_mono` lost the source's on
2026-09-14 when `[T2Space E]` came out of `Oka/AnalyticSpace/FiniteEtaleBaseChange.lean` and the
`unusedArguments` linter refused it. **Neither half of the correction touches what this file
settles**, which is about the target's and is stated at one object.

`ComplexAnalytic.AnalyticSpace.exists_finiteEtaleOver_not_t2Space` below says that hypothesis
cannot be discharged from a hypothesis on the base: **there is an
object of `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver (ℂ¹)` whose total space is not
Hausdorff**, and `ℂ¹` is Hausdorff by `ComplexAnalytic.t2Space_complexAffineSpace`.

That is an improvement on the argument the tree already had.
`OkaTest/FiniteEtaleCancel.lean`'s `LineTwoOrigins.fold` has the closed-map, finite-fibre
and local-homeomorphism halves of `ComplexAnalytic.AnalyticSpace.IsFiniteEtale` over a Hausdorff
base with a non-Hausdorff total space, but it is a map of topological spaces and so is evidence
about the *topological content of the definition* rather than about analytic spaces. This file's
witness is an object of the category.

## What is not settled

* **Nothing about whether the two hypotheses could be replaced by weaker ones.** What is ruled out
  is deriving them from separation of the base; a different hypothesis on the total space, or a
  connectedness assumption, is untouched.
* **No claim that the doubled line is a counterexample to anything else.** In particular nothing
  here says that
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.inducesIsoOnDirectSummand_of_mono`'s conclusion
  fails for it — only that its hypotheses are not free.
* **No `[T2Space]` instance is added or removed**, and
  `Oka/AnalyticSpace/Hausdorff.lean` is not opened by this file.

## Main definitions

- `ComplexAnalytic.AnalyticSpace.double`: two copies of `X` glued along `V`, as a complex analytic
  space.
- `ComplexAnalytic.AnalyticSpace.doubleFold`: the morphism of analytic spaces down to `X`.
- `ComplexAnalytic.AnalyticSpace.origin`, `…doubledLine`, `…doubledLineFold` and
  `…doubledLineOver`: the concrete witness — `ℂ¹`, its origin, the line with two origins, and the
  fold read as an object of `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver (ℂ¹)`.

## Main results

- `ComplexAnalytic.AnalyticSpace.glueDataCLinear_double`: **the transitions of the double are
  `ℂ`-linear**, which is what promotes the gluing to an analytic space. It costs one `congrArg`,
  because the two legs into a member are the same morphism — the lemma that says so is one
  category down and this bullet names it nowhere, for the reason
  `Oka/Geometry/RingedSpace/PresheafedSpace/Gluing.lean` does not name its consumers here either.
- `ComplexAnalytic.AnalyticSpace.isFiniteEtale_doubleFold`: **the fold is finite étale**, for any
  `X` and any `V`. All four conditions are proved one category down, in
  `Oka/Geometry/RingedSpace/PresheafedSpace/Double.lean`, because none of them mentions the
  analytic structure.
- `ComplexAnalytic.AnalyticSpace.not_t2Space_double` and
  `…not_t2Space_double_compl_singleton`: **the double is not Hausdorff** when a point outside `V`
  is in the closure of `V`, and in particular when `V` is the complement of a non-isolated point.
- `ComplexAnalytic.AnalyticSpace.exists_finiteEtaleOver_not_t2Space`: **a finite étale cover of a
  Hausdorff complex analytic space can have non-Hausdorff total space.**
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace Topology Opposite
open AlgebraicGeometry AlgebraicGeometry.LocallyRingedSpace

universe u

namespace ComplexAnalytic.AnalyticSpace

noncomputable section

variable (X : AnalyticSpace.{u}) (V : X.Opens)

/-! ### The double of an analytic space along an open -/

/-- **The transitions of the double are `ℂ`-linear.**

`ComplexAnalytic.GlueDataCLinear` asks that the two structures an overlap inherits agree, and here
the two morphisms it compares — `f i j` and `t i j ≫ f j i` — are *the same morphism*
(`AlgebraicGeometry.LocallyRingedSpace.doubleGlueData_f_eq_t_comp_f`), because the gluing is along
the identity of `V`. So the condition is a `congrArg` and no analytic input is needed; every
member carries the structure of `X` itself. -/
theorem glueDataCLinear_double :
    ComplexAnalytic.GlueDataCLinear (X.toLocallyRingedSpace.doubleGlueData V)
      (fun _ ↦ X.algebraMap) := fun i j ↦
  congrArg (fun m ↦ AlgebraicGeometry.LocallyRingedSpace.comapAlgMap m X.algebraMap)
    (doubleGlueData_f_eq_t_comp_f X.toLocallyRingedSpace V i j)

/-- **Two copies of `X` glued along `V`, as a complex analytic space.** -/
def double : AnalyticSpace.{u} :=
  ofGlueDataCLinear (X.toLocallyRingedSpace.doubleGlueData V) (fun _ ↦ X.algebraMap)
    (glueDataCLinear_double X V) (fun _ ↦ X.hasLocalModels)

/-- **Its underlying locally ringed space is the one glued one category down**, so every statement
of `Oka/Geometry/RingedSpace/PresheafedSpace/Double.lean` is a statement about this space. -/
@[simp]
theorem double_toLocallyRingedSpace :
    (double X V).toLocallyRingedSpace = X.toLocallyRingedSpace.double V := rfl

/-- **The fold, as a morphism of analytic spaces.**

`ComplexAnalytic.AnalyticSpace.glueMorphismsOfGlueData` at the identity of each copy; its two
hypotheses are `AlgebraicGeometry.LocallyRingedSpace.doubleGlueData_comm` and
`ComplexAnalytic.IsCLinearHom.id`. -/
def doubleFold : double X V ⟶ X :=
  glueMorphismsOfGlueData (X.toLocallyRingedSpace.doubleGlueData V) (fun _ ↦ X.algebraMap)
    (glueDataCLinear_double X V) (fun _ ↦ X.hasLocalModels) (fun _ ↦ 𝟙 _)
    (doubleGlueData_comm X.toLocallyRingedSpace V (𝟙 _)) (fun _ ↦ IsCLinearHom.id _)

/-- **Its underlying morphism is the fold of the glued locally ringed space**, which is what lets
the four conditions below be discharged one category down.

It is also where the universal property comes from: the fold's restriction to each copy is
`AlgebraicGeometry.LocallyRingedSpace.ι_doubleFold` read through this equation, and there is no
second statement of it here because `simpNF` rejects one — this lemma rewrites its left-hand
side. The inclusions are morphisms of locally ringed spaces and not of analytic spaces anyway,
which is the reason `ComplexAnalytic.AnalyticSpace.ι_glueMorphismsOfGlueData` gives for its own
spelling. -/
@[simp]
theorem toLRSHom_doubleFold :
    (doubleFold X V).toLRSHom = X.toLocallyRingedSpace.doubleFold V := rfl

/-! ### The fold is finite étale -/

/-- **The fold is a local isomorphism**, both fields from
`Oka/Geometry/RingedSpace/PresheafedSpace/Double.lean`. -/
instance isLocalIso_doubleFold : IsLocalIso (doubleFold X V) where
  isLocalHomeomorph := isLocalHomeomorph_base_doubleFold X.toLocallyRingedSpace V
  isIso_stalkMap x := isIso_stalkMap_doubleFold X.toLocallyRingedSpace V x

/-- **The fold is finite**: it is closed because the image of a set is the union of its two
preimages, and its fibres have at most two points. -/
instance isFinite_doubleFold : IsFinite (doubleFold X V) where
  isClosedMap := isClosedMap_base_doubleFold X.toLocallyRingedSpace V
  finite_fiber y := finite_preimage_base_doubleFold X.toLocallyRingedSpace V y

/-- **The fold is finite étale, for every `X` and every `V`.**

No hypothesis on `V` enters: when `V` is clopen the double is a disjoint union and the fold is the
codiagonal, and when it is not the double is not Hausdorff. Both are finite étale, which is the
point — finite étaleness says nothing about separation of the total space. -/
instance isFiniteEtale_doubleFold : IsFiniteEtale (doubleFold X V) where
  isFinite := inferInstance
  isLocalIso := inferInstance

/-! ### The double is not Hausdorff -/

/-- **The double is not Hausdorff when a point outside `V` is in the closure of `V`**, which is
`AlgebraicGeometry.LocallyRingedSpace.not_t2Space_double` read at the analytic space. -/
theorem not_t2Space_double (x₀ : X) (hx₀ : x₀ ∉ V) (hcl : x₀ ∈ closure (V : Set X)) :
    ¬ T2Space (double X V : Type u) :=
  AlgebraicGeometry.LocallyRingedSpace.not_t2Space_double X.toLocallyRingedSpace V x₀ hx₀ hcl

variable {X}

/-- **In particular the double along the complement of a non-isolated point is not Hausdorff.**

`isOpen_compl_singleton` needs `[T1Space X]` and `Dense.closure_eq` needs
`[Filter.NeBot (𝓝[≠] x₀)]`, which together are exactly *`x₀` is a point of a `T1` space that is
not isolated*. -/
theorem not_t2Space_double_compl_singleton [T1Space X] (x₀ : X) [Filter.NeBot (𝓝[≠] x₀)] :
    ¬ T2Space (double X ⟨{x₀}ᶜ, isOpen_compl_singleton⟩ : Type u) :=
  not_t2Space_double X ⟨{x₀}ᶜ, isOpen_compl_singleton⟩ x₀ (by simp)
    ((dense_compl_singleton x₀).closure_eq ▸ Set.mem_univ _)

/-! ### The complex line with two origins -/

/-- **The origin of `ℂ¹`.**

Written as the constant function rather than as `0` because the carrier of
`ComplexAnalytic.AnalyticSpace.complexAffineSpace 1` is `ULift (Fin 1) → ℂ` only up to unfolding,
and instance search does not unfold it: `(0 : complexAffineSpace 1)` fails to synthesize `OfNat`,
while a lambda elaborates against the unfolded expected type. -/
def origin : (complexAffineSpace.{u} 1 : Type u) := fun _ ↦ 0

/-- **The origin is not isolated in `ℂ¹`**, which is the hypothesis
`ComplexAnalytic.AnalyticSpace.not_t2Space_double_compl_singleton` asks for. Instance search finds
this for `(0 : ULift (Fin 1) → ℂ)` and not at the spelling above, which is why it is restated. -/
instance neBot_nhdsWithin_compl_origin : Filter.NeBot (𝓝[≠] (origin.{u})) :=
  inferInstanceAs (Filter.NeBot (𝓝[≠] (0 : ULift.{u} (Fin 1) → ℂ)))

/-- **The complex line with two origins**: two copies of `ℂ¹` glued along `ℂ ∖ {0}`. -/
def doubledLine : AnalyticSpace.{u} :=
  double (complexAffineSpace.{u} 1) ⟨{origin.{u}}ᶜ, isOpen_compl_singleton⟩

/-- **It is not Hausdorff**, and it is a complex analytic space — which is what
`Oka/AnalyticSpace/Basic.lean`'s two sentences about the absence of a separation axiom, and
`Oka/AnalyticSpace/Hausdorff.lean`'s, had no witness for. -/
theorem not_t2Space_doubledLine : ¬ T2Space (doubledLine.{u} : Type u) :=
  not_t2Space_double_compl_singleton origin.{u}

/-- **The fold of the line with two origins onto `ℂ¹`.** -/
def doubledLineFold : doubledLine.{u} ⟶ complexAffineSpace.{u} 1 :=
  doubleFold (complexAffineSpace.{u} 1) ⟨{origin.{u}}ᶜ, isOpen_compl_singleton⟩

/-- **It is finite étale.** -/
instance isFiniteEtale_doubledLineFold : IsFiniteEtale doubledLineFold.{u} :=
  isFiniteEtale_doubleFold _ _

/-- **The line with two origins, as a finite étale cover of `ℂ¹`.** -/
def doubledLineOver : FiniteEtaleOver (complexAffineSpace.{u} 1) :=
  MorphismProperty.Over.mk _ doubledLineFold.{u} isFiniteEtale_doubledLineFold.{u}

/-- **Its total space is not Hausdorff.** -/
theorem not_t2Space_left_doubledLineOver :
    ¬ T2Space ((doubledLineOver.{u}).left : Type u) :=
  not_t2Space_doubledLine.{u}

/-- **A finite étale cover of a Hausdorff complex analytic space can have non-Hausdorff total
space.**

The base is `ℂ¹`, which is Hausdorff by `ComplexAnalytic.t2Space_complexAffineSpace`; the cover is
the line with two origins. So a `[T2Space]` hypothesis on a cover's total space is not derivable
from separation of the base, which is what
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.inducesIsoOnDirectSummand_of_mono` and
`…inducesIsoOnDirectSummand_of_injective` carry one for.

**This read *So `[T2Space A.left]` is not derivable* until 2026-09-14**, when the source's
hypothesis came out of the first of those two; the statement is at a single object and settles
the target's as readily as the source's. -/
theorem exists_finiteEtaleOver_not_t2Space :
    ∃ A : FiniteEtaleOver (complexAffineSpace.{u} 1), ¬ T2Space (A.left : Type u) :=
  ⟨doubledLineOver.{u}, not_t2Space_left_doubledLineOver.{u}⟩

end

end ComplexAnalytic.AnalyticSpace
