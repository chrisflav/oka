/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.AnalyticSpace.SeparatedFiberFunctor
import Oka.AnalyticSpace.SeparatedFiniteEtaleCoproducts

/-!
# Both fibre functors at the separated covers preserve finite coproducts

`Oka/AnalyticSpace/SeparatedFiberFunctor.lean` builds the fibre at a point of the base as a functor
out of `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver`, into `Type u` and into
`FintypeCat`, and proves two of the six obligations a fibre functor of a Galois category carries —
the terminal object at the two functors themselves, and the reflection of isomorphisms at their
restrictions along the inclusion of the subcategory of objects with preconnected total space.
Its `## What is not here` records a third as absent and says exactly what stands in the way:

> **Not the preservation of finite coproducts, and what is absent is the statement and not the
> colimit.** Finite coproducts of this category are in the tree —
> `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.hasFiniteCoproducts`, with no hypothesis
> on the base — but they are in `Oka/AnalyticSpace/SeparatedFiniteEtaleCoproducts.lean`, **a
> sibling of this module which neither imports it nor is imported by it** […] so that instance is
> not in scope below and nothing here could consume it without a new import.

**This file is that import.** It imports both siblings, and everything below is the ambient
statement read across an inclusion that turns out to carry the cofan on the nose.

## The route, and the one step that is not bookkeeping

`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.fiberFunctor` **is** defined as
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.toFiniteEtaleOver` composed with
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fiberFunctor`, and the `FintypeCat`-valued one
likewise. So the only thing owed at the two functors is **the inclusion**, after which
`CategoryTheory.Limits.comp_preservesColimitsOfShape` is the whole of the step —
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.preservesFiniteCoproducts_fiberFunctor` and
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.preservesFiniteCoproducts_fintypeFiberFunctor`
supply the other half and are in this file's import closure through either sibling — both
siblings' `Oka`-prefixed transitive import closures contain
`Oka/AnalyticSpace/FiniteEtaleOver.lean`, which is a walk of the `import Oka…` lines of the
comment-stripped code of each module reached, `scripts/import_cost.py`'s `strip_comments` and its
`IMPORT` pattern being the instrument.

**And the inclusion costs one `def` whose body is the ambient declaration unchanged.**
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.sigma` is the ambient disjoint union
**written out rather than transported** — the decision
`Oka/AnalyticSpace/SeparatedFiniteEtaleCoproducts.lean`'s docstring argues for at length, and the
reason it gives is that the inclusion then carries the object to the ambient one on the nose — so
the image of the cofan of `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.sigmaι` under
that inclusion **is** the ambient cofan, and
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isColimitCofanSigma` elaborates against the image
statement with no `CategoryTheory.eqToHom` and no conversion. That is
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.isColimitMapCofanSigma`, and it is the one
place where the two categories are compared; everything after it is Mathlib's colimit API.

**Nothing here reflects a colimit and nothing asks the inclusion to be full.** The statement proved
of the inclusion is preservation, in the direction the composite needs, and
`CategoryTheory.Limits.isColimitOfReflectsOfMapIsColimit` is not read — which is the same decision
`Oka/AnalyticSpace/SeparatedFiniteEtaleCoproducts.lean` took for its own colimit and for the same
reason.

## Where the hypotheses are spent, which is nowhere

**No hypothesis on the base and none on the point**, exactly as at the ambient pair.
`Oka/AnalyticSpace/SeparatedFiberFunctor.lean`'s terminal-object statements sit outside its
`[T2Space (X : Type u)]` block and these sit outside one too:
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.t2Space_left` is read by nothing below, the
disjoint union of separated covers asks nothing of the base —
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isSeparatedMap_sigma` carries an `omit` of the
Hausdorff hypothesis — and a colimit statement about morphisms over `X` does not see the topology
of `X`. The only class hypotheses below are `[Finite ι]` and the universe of the index, both of
which `ComplexAnalytic.AnalyticSpace.sigma` already asks.

## Two names that are not the ambient ones, and the reason is arithmetic

`OkaTest/Axioms/Morphisms.lean` guards every declaration of this module with a `#print axioms`
command, and that command's name has to fit a line: `#print axioms` and a space are fourteen
characters, `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.` is fifty-five, and a guard
whose name is wrapped onto an indented line of its own has two more, so a name of more than
**forty-three** characters after that namespace cannot be guarded in either layout.
`preservesFiniteCoproducts_fintypeFiberFunctor`, which is the ambient spelling one category out, is
**forty-five**. So the `FintypeCat`-valued instance below is
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.preservesFiniteCoproducts_fintypeFiber`,
whose statement is at `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.fintypeFiberFunctor`
and is the ambient statement unchanged, and the `Type u`-valued one keeps the ambient spelling
because it fits. **This is the same arithmetic
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.preservesTerminal_fintypeFiberFunctor`'s
docstring records for its own name**, and the asymmetry between the two names below is that
arithmetic and nothing else: a name is shortened here when and only when it does not fit.

## Main results

- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.isColimitMapCofanSigma`: **the inclusion
  into the covers carries the cofan of the inclusions of a finite family to a colimit cofan**, and
  its proof term is the ambient colimit itself.
- **So the inclusion preserves colimits of every discrete shape indexed by a finite type of this
category's own universe** —
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.preservesColimitsOfShape_toFiniteEtaleOver`
— and **it preserves finite coproducts** —
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.preservesFiniteCoproducts_toFiniteEtaleOver`
— which is the class the two instances below consume.
- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.preservesFiniteCoproducts_fiberFunctor`
  and
  `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.preservesFiniteCoproducts_fintypeFiber`:
  **both fibre functors preserve finite coproducts**, with no hypothesis on the base and none on
  the point. The second is the Galois-category obligation at the functor a fibre functor is asked
  to be.

## What is not here

* **No `FiberFunctor` instance and no `PreGaloisCategory` instance, and the class cannot be cited
  by name here.** `Mathlib/CategoryTheory/Galois/Basic.lean`'s namespace is not in this
  repository's import closure, which is the spelling
  `Oka/AnalyticSpace/SeparatedFiberFunctor.lean` and
  `Oka/AnalyticSpace/SeparatedFiniteEtaleCoproducts.lean` already use for it and the reason no
  instance of it is declared anywhere below. **What this file moves is one field of a structure
  nothing in this repository can name**, and that is measured rather than said:
  `PreGaloisCategory` occurs in the comment-stripped code of **no** module of this repository at
  the commit that adds this file, by a scan of every tracked `.lean` with
  `scripts/import_cost.py`'s `strip_comments`. **The bare token `FiberFunctor` is not the
  instrument for the other class and this file does not use it as one**: it occurs in five
  modules at that commit, every hit a substring of a declaration name of this repository such as
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fintypeFiberFunctor`, and none of them
  Mathlib's structure. Of the six obligations that structure carries — the terminal object,
  pullbacks, finite coproducts, epimorphisms, quotients by finite group actions and the reflection
  of isomorphisms — `Oka/AnalyticSpace/SeparatedFiberFunctor.lean` supplies the first at these two
  functors and the last **at their restrictions along
  `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.isPreconnected`'s inclusion**, which is a
  weaker statement than the field asks for and is that file's own reading of what is reachable, and
  this file supplies the third at the two functors themselves.
* **Not the preservation of pullbacks**, and this file does not narrow that absence.
  `Oka/AnalyticSpace/SeparatedFiberFunctor.lean`'s bullet on it is untouched and stands as written:
  fibre products of this category exist, and what is missing is an identification of the **fibre**
  of that limit with the set-theoretic pullback of the two fibres. **Nothing below is that
  identification for a limit**, and the coproduct case is no evidence about it: the identification
  this file rests on is `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fiberSigmaEquiv`, which is a
  statement about a disjoint union and is already in the ambient file.
* **Not the preservation of epimorphisms and not quotients by finite group actions.** Both are
  where `Oka/AnalyticSpace/SeparatedFiberFunctor.lean` left them and nothing here moves either;
  the quotients field is stated over `CategoryTheory.SingleObj`, which no declaration below names.
* **Nothing at `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver` is superseded or restated.**
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.preservesFiniteCoproducts_fiberFunctor` and its
  `FintypeCat` counterpart are what a caller working in the covers wants and are unchanged; this
  file consumes them and adds no second proof of either. **Nor is anything at
  `Oka/AnalyticSpace/SeparatedFiniteEtaleCoproducts.lean` restated**: the object, the cofan and the
  colimit of this category are that file's, and what is added here is the comparison of its cofan
  with the ambient one.
* **No statement about coproducts of the preconnected subcategory.**
  `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.isPreconnected` is the full subcategory
  `Oka/AnalyticSpace/SeparatedFiberFunctor.lean` cuts for faithfulness and conservativity, and the
  disjoint union of two objects of it whose total spaces are both non-empty is not one: each
  summand is clopen in the union and neither is empty, so the union is not preconnected. **The
  qualification is not decoration** — a disjoint union with an empty member is homeomorphic to the
  other member and stays in the subcategory, so the unqualified sentence would be false — and
  nothing below states either half. Nothing below is about that subcategory or about the functor
  `CategoryTheory.ObjectProperty.ι` at it.
-/

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

universe u

namespace ComplexAnalytic.AnalyticSpace

variable {X : AnalyticSpace.{u}}

/-! ### The inclusion into the covers carries the cofan to a colimit -/

/-- **The image under the inclusion of the cofan of the inclusions of a finite family of separated
covers is a coproduct cofan in the covers.**

**The proof term is `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isColimitCofanSigma` at the
family of images, unchanged**, and that is what the statement is for: it records that the two
cofans are the same and not merely isomorphic. **The reason is
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.sigma`'s own construction** — the object is
`CategoryTheory.MorphismProperty.Over.mk` at the ambient disjoint union's structure map rather than
a transport of it, and
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.toFiniteEtaleOver` is
`CategoryTheory.MorphismProperty.Over.changeProp`, which rewrites an object's proof and nothing
else — so the apex, the legs and the family of the image cofan are the ambient ones and the two
statements are the same type. That the two proofs an object carries differ is invisible here
because both are propositions.

**No `CategoryTheory.eqToHom` and no `CategoryTheory.Limits.IsColimit.ofIsoColimit`**, which is
what the sibling's decision to write the object out rather than transport it was taken to buy, and
this declaration is where that purchase is collected. -/
noncomputable def SeparatedFiniteEtaleOver.isColimitMapCofanSigma {ι : Type u} [Finite ι]
    (A : ι → SeparatedFiniteEtaleOver.{u} X) :
    Limits.IsColimit
      (Limits.Cofan.mk ((SeparatedFiniteEtaleOver.toFiniteEtaleOver X).obj
          (SeparatedFiniteEtaleOver.sigma A))
        (fun i ↦ (SeparatedFiniteEtaleOver.toFiniteEtaleOver X).map
          (SeparatedFiniteEtaleOver.sigmaι A i)) :
          Limits.Cofan fun i ↦ (SeparatedFiniteEtaleOver.toFiniteEtaleOver X).obj (A i)) :=
  FiniteEtaleOver.isColimitCofanSigma.{u}
    (fun i ↦ (SeparatedFiniteEtaleOver.toFiniteEtaleOver X).obj (A i))

/-! ### So the inclusion preserves finite coproducts -/

/-- **The inclusion preserves colimits of every discrete shape indexed by a finite type of this
category's own universe.**

`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.preservesColimitsOfShape_fiberFunctor`'s body at
this functor: `CategoryTheory.Limits.preservesColimit_of_preserves_colimit_cocone` at
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.isColimitCofanSigma`, with
`CategoryTheory.Limits.isColimitMapCoconeCofanMkEquiv` the bridge between a mapped cocone and a
cofan on the mapped family, and `CategoryTheory.Discrete.natIsoFunctor` together with
`CategoryTheory.Limits.preservesColimit_of_iso_diagram` carrying it from the family a functor out
of a discrete category is determined by to that functor itself. **The two steps are the ambient
ones and neither is re-argued here.**

**What makes this cheap is the declaration above and not the shape argument**: the colimit of the
image cofan is the ambient colimit, so nothing has to be transported across an isomorphism of
cocones. -/
instance SeparatedFiniteEtaleOver.preservesColimitsOfShape_toFiniteEtaleOver (ι : Type u)
    [Finite ι] (X : AnalyticSpace.{u}) :
    Limits.PreservesColimitsOfShape (Discrete ι)
      (SeparatedFiniteEtaleOver.toFiniteEtaleOver.{u} X) where
  preservesColimit {K} := by
    haveI : Limits.PreservesColimit (Discrete.functor (K.obj ∘ Discrete.mk))
        (SeparatedFiniteEtaleOver.toFiniteEtaleOver.{u} X) :=
      Limits.preservesColimit_of_preserves_colimit_cocone
        (SeparatedFiniteEtaleOver.isColimitCofanSigma (K.obj ∘ Discrete.mk))
        ((Limits.isColimitMapCoconeCofanMkEquiv _ _ _).symm
          (SeparatedFiniteEtaleOver.isColimitMapCofanSigma (K.obj ∘ Discrete.mk)))
    exact Limits.preservesColimit_of_iso_diagram _ Discrete.natIsoFunctor.symm

/-- **The inclusion preserves finite coproducts.**

**The universe crossing is the whole of the step**, as at
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.hasFiniteCoproducts` and at the ambient
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.preservesFiniteCoproducts_fiberFunctor`:
`CategoryTheory.Limits.PreservesFiniteCoproducts` quantifies over `Fin n`, which lives in `Type 0`,
the instance above is at an index type of this category's own universe, and
`CategoryTheory.Discrete.equivalence` at `Equiv.ulift` with
`CategoryTheory.Limits.preservesColimitsOfShape_of_equiv` is what crosses between them.

**This is not a statement that the inclusion creates or reflects coproducts**, neither of which is
below; what a consumer gets from it is the image of a coproduct cocone, which is the direction the
two instances after it need. -/
instance SeparatedFiniteEtaleOver.preservesFiniteCoproducts_toFiniteEtaleOver
    (X : AnalyticSpace.{u}) :
    Limits.PreservesFiniteCoproducts (SeparatedFiniteEtaleOver.toFiniteEtaleOver.{u} X) where
  preserves n :=
    haveI := SeparatedFiniteEtaleOver.preservesColimitsOfShape_toFiniteEtaleOver
      (ULift.{u} (Fin n)) X
    Limits.preservesColimitsOfShape_of_equiv (Discrete.equivalence Equiv.ulift.{u}) _

/-! ### And so do both fibre functors -/

/-- **The `Type u`-valued fibre functor at the separated covers preserves finite coproducts**, with
no hypothesis on the base and none on the point.

`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.fiberFunctor` is by definition
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.toFiniteEtaleOver` composed with
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fiberFunctor`, so the instance above and
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.preservesFiniteCoproducts_fiberFunctor` compose.

**The composite is spelled out in an `inferInstanceAs` rather than left to instance search**, and
that is not decoration but a run: with the two instances above in scope, `infer_instance` at
`CategoryTheory.Limits.PreservesColimitsOfShape (CategoryTheory.Discrete (Fin n))` of this functor
reports *failed to synthesize*. The fibre functor is a `def` and not an `abbrev`, so the goal's
head is that constant rather than a `CategoryTheory.Functor.comp` and
`CategoryTheory.Limits.comp_preservesColimitsOfShape` is not reached; naming the composite puts
the unfolding in the elaborator's hands, where it is one `def`. -/
instance SeparatedFiniteEtaleOver.preservesFiniteCoproducts_fiberFunctor {X : AnalyticSpace.{u}}
    (x : X) :
    Limits.PreservesFiniteCoproducts (SeparatedFiniteEtaleOver.fiberFunctor.{u} x) where
  preserves n :=
    inferInstanceAs (Limits.PreservesColimitsOfShape (Discrete (Fin n))
      (SeparatedFiniteEtaleOver.toFiniteEtaleOver.{u} X ⋙ FiniteEtaleOver.fiberFunctor.{u} x))

/-- **The `FintypeCat`-valued fibre functor preserves finite coproducts**, which is the obligation
a fibre functor of a Galois category carries at the functor it is asked of.

The same composition at
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.preservesFiniteCoproducts_fintypeFiberFunctor`.
**Neither of the two below is derived from the other, and that is a choice and not an
obstruction.** The two functors have the same underlying map and different bundlings of it, so a
colimit of one family of values is not literally a colimit of the other — which is the distinction
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.preservesTerminal_fintypeFiberFunctor`'s
docstring draws for its own pair. **A derivation is nevertheless available and is not taken**:
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.fintypeFiberFunctor` composed with
`FintypeCat.incl` **is**
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.fiberFunctor` by `rfl`, which I ran, so a
reflection argument along that faithful functor would give one from the other. Composing two
instances that are already in scope is shorter than that argument and asks nothing of
`FintypeCat.incl`.

**The name is seven characters short of the ambient one and the module docstring's section *Two
names that are not the ambient ones* is why**; the statement is the ambient statement and the
functor is `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.fintypeFiberFunctor`.

**What this does not say is that this category is a Galois category and this functor a fibre
functor for it.** Of the six obligations, two are stated at this functor at the commit that adds
this module — the terminal object and this one — and a third, the reflection of isomorphisms, is
stated at its restriction along the preconnected subcategory's inclusion and not at it.
**The other three are stated at neither fibre functor, and that is a scan and not an impression**,
taken over the comment-stripped code of every tracked `.lean` at the commit that adds this module
with `scripts/import_cost.py`'s `strip_comments`: `PreservesLimitsOfShape` occurs in **two**
modules, `Oka/AnalyticSpace/FiniteEtaleOver.lean` and
`Oka/AnalyticSpace/SeparatedFiberFunctor.lean`, and in both of them only at `Discrete PEmpty`,
which is the terminal-object obligation and not the pullback one — **this file adds no occurrence
of that spelling**, its own statements being at `CategoryTheory.Limits.PreservesColimitsOfShape`,
and a branch in review at the time of writing states the pullback obligation and moves this row,
so re-take it rather than carrying it; `PreservesFiniteLimits` occurs
in **five**, none of them about a cover or a fibre functor; `PreservesEpimorphisms` in **two**,
which is the pair `Oka/AnalyticSpace/SeparatedFiberFunctor.lean`'s own bullet names and neither is
about these functors; and `CategoryTheory.SingleObj`, the shape the quotients obligation is stated
over, in **one**, the mirror-tree module that declares colimits of that shape. **The bare token
`SingleObj` occurs in two and the second is the aggregator `Oka.lean`'s `import` line**, which is
why the qualified spelling is the one counted here. `Mathlib/CategoryTheory/Galois/Basic.lean`'s
class is not citable by name from here in any case. -/
instance SeparatedFiniteEtaleOver.preservesFiniteCoproducts_fintypeFiber {X : AnalyticSpace.{u}}
    (x : X) :
    Limits.PreservesFiniteCoproducts (SeparatedFiniteEtaleOver.fintypeFiberFunctor.{u} x) where
  preserves n :=
    inferInstanceAs (Limits.PreservesColimitsOfShape (Discrete (Fin n))
      (SeparatedFiniteEtaleOver.toFiniteEtaleOver.{u} X ⋙
        FiniteEtaleOver.fintypeFiberFunctor.{u} x))

end ComplexAnalytic.AnalyticSpace
