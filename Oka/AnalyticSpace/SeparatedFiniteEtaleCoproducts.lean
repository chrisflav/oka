/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.AnalyticSpace.SeparatedFiniteEtale

/-!
# Finite coproducts in the category of covers separated over the base

`Oka/AnalyticSpace/SeparatedFiniteEtale.lean` cuts the covers separated over the base out of
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver` and gives that category a terminal object. Its
`## What is not here` says in terms what was missing next, and names the ingredient that was
already there:

> **No coproducts and no terminal-object-and-coproducts package.**
> `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isSeparatedMap_sigma` says a finite disjoint
> union of separated covers is separated, so the objects are available; what is not here is the
> cofan […]

**This file is the cofan, its colimit and the class, and it adds no mathematics.**
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.hasFiniteCoproducts` is the same statement one
category out and every step of its construction is reread here at objects carrying a second
component.

## What the statement is, and what it is not

`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.hasFiniteCoproducts` is the
`hasFiniteCoproducts` field of `Mathlib/CategoryTheory/Galois/Basic.lean`'s `PreGaloisCategory` at
this category, **with nothing added**. That class asks five things of a category — a terminal
object, pullbacks, finite coproducts, quotients by finite group actions, and that a monomorphism
induce an isomorphism onto a direct summand — and this is one of them, so what is here is one
field and not the class. **That namespace is not in this repository's import closure**: `#check` on
it reports an unknown identifier from a file importing this module, which is the spelling
`Oka/AnalyticSpace/SeparatedFiniteEtale.lean` and `Oka/AnalyticSpace/FiniteEtaleOver.lean` already
use for it and the reason no instance of it is declared anywhere below.

**And nothing is added on the base either, which is the one thing this rung was expected to cost
and does not.** `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isSeparatedMap_sigma` carries an
`omit` of `[T2Space (X : Type u)]` (`Oka/AnalyticSpace/SeparatedOver.lean`) and says in its own
docstring that the finiteness of the index is the coproduct's and not the separatedness's; the
disjoint union of covers asks nothing of the base; and the colimit statement is about morphisms
over `X` and not about the topology of `X`. **So this file has no hypothesis on the base at all**,
as `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.hasTerminal` has none.
`Oka/AnalyticSpace/SeparatedFiniteEtale.lean` asks it of the statements that read a topological
consequence off a monomorphism, and its own
*Where each hypothesis is spent* says it is spent there through
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.t2Space_left` and through nothing else;
this file cites neither that instance nor any statement that needs it.

## The two steps, and what each one is a copy of

* **The object, the inclusion, the cofan and the colimit** are
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.sigma`,
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.sigmaι`,
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.cofanSigma` and
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isColimitCofanSigma` reread at this category. The
  object is **written out rather than transported** — its underlying cover is the ambient disjoint
  union of the underlying covers, not an isomorphic copy — which is the idiom
  `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.selfProd` uses and its docstring argues.
  **The colimit's proof term is the ambient one character for character**, which is a `diff` of the
  two proof bodies and not an impression: that proof reads
  `CategoryTheory.MorphismProperty.Over.homMk`,
  `CategoryTheory.MorphismProperty.Over.Hom.ext`, `CategoryTheory.MorphismProperty.Over.w` and the
  three statements `ComplexAnalytic.AnalyticSpace.sigmaDesc`,
  `ComplexAnalytic.AnalyticSpace.sigmaι_sigmaDesc` and
  `ComplexAnalytic.AnalyticSpace.hom_ext_sigma`, and **not one of those mentions which morphism
  property the comma category was cut out by**. That is why nothing had to be adapted.
* **The class** is `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.hasColimitsOfShape_discrete` and
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.hasFiniteCoproducts` reread the same way, and
  those two bodies differ from the ambient ones **only in the name of the category and in the
  names of the declarations of this file they cite — two in the first and one in the second — plus
  one line break the hundred-column limit forces**, which is a `diff` of the four bodies. The two
  steps they take are argued at length in the ambient pair's
  docstrings and are not re-argued here: `CategoryTheory.Limits.Cocone.precompose` at
  `CategoryTheory.Discrete.natIsoFunctor` for the discrete shape, because
  `CategoryTheory.Limits.hasCoproducts_of_colimit_cofans` asks for a cofan at every index type of a
  universe and a disjoint union of covers is a cover only at a finite one; and
  `CategoryTheory.Discrete.equivalence` at `Equiv.ulift` to cross from the `Fin n` of
  `CategoryTheory.Limits.HasFiniteCoproducts`, which lives in `Type 0`, to the `Type u` that
  `ComplexAnalytic.AnalyticSpace.sigma` takes its index from.

**Reflection along the inclusion is the route this file does not take.**
`CategoryTheory.Limits.isColimitOfReflectsOfMapIsColimit` is for a binary cofan; at a general
discrete shape what would have to be reconciled is
`CategoryTheory.Functor.mapCocone` of a `CategoryTheory.Limits.Cofan.mk` against
`CategoryTheory.Discrete.functor` of the family of images, which is bookkeeping this rung does not
need when the ambient proof transfers with no edit at all.
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.isTerminalId` took the same decision and
its docstring gives the same reason.

**Binary coproducts come free, and they are Mathlib's instance and not this file's.** At the commit
that adds this module `#synth CategoryTheory.Limits.HasBinaryCoproducts` at this category resolves
to `CategoryTheory.Limits.hasColimitsOfShape_discrete` at
`CategoryTheory.Limits.WalkingPair` — that is
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.hasFiniteCoproducts` read at a two-element
shape — and at the commit before it fails to synthesise. Nothing below states binary coproducts and
no declaration of
this file is about them.

## Main definitions

- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.sigma`: **the disjoint union of a finite
  family of separated covers, as an object of this category**, and
  `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.sigmaι`: **the inclusion of a member**.
- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.cofanSigma`: **those inclusions as a
  cofan**, which carries no content and exists so that the colimit statement can name its cocone.

## Main results

- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.isColimitCofanSigma`: **that cofan is a
  coproduct in this category**.
- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.hasColimitsOfShape_discrete`: **so the
  category has colimits of every finite discrete shape of its own universe**, and
  `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.hasFiniteCoproducts`: **it has finite
  coproducts**, which is the Galois-category field.

## What is not here

* **No `CategoryTheory.Limits.HasFiniteColimits`, and what is missing is named rather than
  gestured at.** The two converters into that class that a category with finite coproducts would
  reach for are
  `CategoryTheory.Limits.hasFiniteColimits_of_hasCoequalizers_and_finite_coproducts`, which asks
  for coequalisers beside the finite coproducts below, and
  `CategoryTheory.Limits.hasFiniteColimits_of_hasInitial_and_pushouts`, which asks for an initial
  object and pushouts. **Neither a coequaliser nor a pushout is stated for this category or for
  the covers anywhere in this repository**, and that is a measurement at `077f6d5` over the
  comment-stripped code of every tracked module: `Coequalizer` occurs in none, `HasPushouts` in
  none, `pushout` in none, and the two modules whose code carries `coequalizer` —
  `Oka/Geometry/RingedSpace/PresheafedSpace/Gluing.lean` and `OkaTest/AffineSections.lean` — are
  about mapping out of a glued presheafed space and about a cokernel of a map of modules, neither
  of which is a colimit of either category. `#synth` on `CategoryTheory.Limits.HasFiniteColimits`
  at this category fails at the commit that adds this module, which measures the instance graph
  and is not an argument that the class is unprovable.
* **No `PreGaloisCategory` instance and no claim of one, and every count of how many of the five
  hold is pinned to a commit, because it moves — three times while this module was being written,
  once between its first delivery and this one.** At **`077f6d5`**, the commit this module is
  written on top of, **three** of the five hold at this category: a terminal object, by
  `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.hasTerminal` and with no hypothesis on
  the base; the direct summand at a monomorphism, by
  `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.inducesIsoOnDirectSummand_of_mono'` and
  over a Hausdorff base; and fibre products, by
  `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.hasPullbacks` and over a Hausdorff base
  as well. **At the commit that adds this module, four do**: those three and
  `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.hasFiniteCoproducts`. **The one that
  remains at that commit is quotients by finite group actions**, and that it is stated nowhere is a
  measurement and not an impression: the name `CategoryTheory.SingleObj` occurs in the
  comment-stripped code of no module of this repository at `077f6d5`.

  **At the commit that adds `Oka/CategoryTheory/Limits/Shapes/SingleObj.lean` that count is one,
  and the one is that module**, which is not the field: it says a category with
  `CategoryTheory.Limits.HasFiniteColimits` has colimits of that shape for every finite group at
  every universe, and this category is not known to have finite colimits — coequalisers and
  pushouts are stated nowhere for it, which is what the bullet opening *No
  `CategoryTheory.Limits.HasFiniteColimits`* measures. That
  module is in the mirror tree and **imports nothing of this repository**, and this one does not
  import it, so nothing here consumes it and nothing here is changed by it.

  **This bullet said *two* and *three* and put pullbacks among the remaining two, naming taxis
  #1918 as a pull request in review, until that request merged** as `4d40d05` while this branch was
  in review. Both figures were exact at `26dc715`, the commit the first delivery of this module was
  written on top of, and neither is exact at this one — which is the reason the bullet opens by
  saying that the count moves and is pinned.
* **Nothing about the ambient category is restated, narrowed or deleted.**
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.hasFiniteCoproducts` is landed and is what a
  caller working in the covers wants; `Oka/AnalyticSpace/Sigma.lean`'s statements about
  `ComplexAnalytic.AnalyticSpace` itself are what both constructions rest on and are untouched.
  **In particular the fibre-functor statements are not extended**: that a fibre functor preserves
  finite coproducts is proved in `Oka/AnalyticSpace/FiniteEtaleOver.lean` for the covers, this file
  declares no functor out of this category, and preservation along the inclusion composed with
  such a functor is not stated.
* **Nothing about base change in `ComplexAnalytic.AnalyticSpace` is narrowed.**
  `CategoryTheory.MorphismProperty.IsStableUnderBaseChange` for
  `ComplexAnalytic.AnalyticSpace.isFiniteEtale` quantifies over cospans whose finite étale leg may
  have a non-Hausdorff source, and `ComplexAnalytic.AnalyticSpace.doubledLineOver` is the standing
  witness against it. The bullets recording that in `Oka/AnalyticSpace/FiniteEtaleBaseChange.lean`
  and `Oka/AnalyticSpace/FiniteEtaleOver.lean` are untouched by this file and are not made weaker
  by it.
-/

open CategoryTheory

universe u

namespace ComplexAnalytic.AnalyticSpace

variable {X : AnalyticSpace.{u}}

/-! ### The disjoint union of a finite family of separated covers -/

/-- **The disjoint union of a finite family of separated covers, as an object of this category.**

`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.sigma` at the family of underlying covers,
**written out rather than transported**, so that the inclusion into the covers carries this object
to that one on the nose and
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.isColimitCofanSigma` inherits the ambient
proof with no `CategoryTheory.eqToHom`. This is the idiom
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.selfProd` uses and its docstring is where
the reason is argued.

**The second component is the whole of what is new**, and it is
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isSeparatedMap_sigma` at each member's own
separatedness: the structure morphism of a disjoint union of covers is the descent map of the
structure morphisms by definition, and a descent map out of a finite disjoint union is separated
when every member's map is. **That lemma asks nothing of the base** — its statement carries an
`omit` of the Hausdorff hypothesis — which is why no declaration of this file has a hypothesis on
the base.

**No hypothesis beyond `[Finite ι]` and `ι : Type u`**, both of which the ambient construction
already asks: the finiteness is what makes a disjoint union of covers a cover, and the universe is
the one `ComplexAnalytic.AnalyticSpace.sigma` takes its index from. -/
noncomputable def SeparatedFiniteEtaleOver.sigma {ι : Type u} [Finite ι]
    (A : ι → SeparatedFiniteEtaleOver.{u} X) : SeparatedFiniteEtaleOver.{u} X :=
  MorphismProperty.Over.mk _
    (FiniteEtaleOver.sigma fun i ↦ (SeparatedFiniteEtaleOver.toFiniteEtaleOver X).obj (A i)).hom
    ⟨(FiniteEtaleOver.sigma fun i ↦
        (SeparatedFiniteEtaleOver.toFiniteEtaleOver X).obj (A i)).prop,
      FiniteEtaleOver.isSeparatedMap_sigma _ fun i ↦ (A i).isSeparatedMap_hom⟩

/-- **The inclusion of a member into the disjoint union**, as a morphism of this category.

`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.sigmaι`'s body unchanged:
`ComplexAnalytic.AnalyticSpace.sigmaι` underneath and
`ComplexAnalytic.AnalyticSpace.sigmaι_sigmaDesc` for the triangle over the base, which is what the
descent map restricts to on a member. **A morphism of this category is asked for nothing beyond
that triangle**, the second morphism property being `⊤` here as it is in the covers, so the second
component of neither object enters and `ComplexAnalytic.AnalyticSpace.isFiniteEtale_sigmaι` is not
read — that statement is about a different base, as the ambient docstring says of its own use.

**The `⊤` argument is left to its autoParam rather than written out**, for the reason the ambient
declaration's docstring records: inside a declaration whose name begins
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver` the identifier `trivial` resolves to a
declaration of that namespace and the error names its type rather than `True`. -/
noncomputable def SeparatedFiniteEtaleOver.sigmaι {ι : Type u} [Finite ι]
    (A : ι → SeparatedFiniteEtaleOver.{u} X) (j : ι) : A j ⟶ SeparatedFiniteEtaleOver.sigma A :=
  MorphismProperty.Over.homMk (AnalyticSpace.sigmaι (fun i ↦ (A i).left) j)
    (AnalyticSpace.sigmaι_sigmaDesc _ _ j)

/-- **The inclusions of the members, read as a cofan on the disjoint union.**

There is no content, for the reason
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.cofanSigma`'s docstring gives of itself: the
declaration exists because
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.isColimitCofanSigma` has to name the
cocone it says is a colimit, and because `CategoryTheory.Limits.Cofan.inj` is how that statement
presents the inclusions. -/
noncomputable def SeparatedFiniteEtaleOver.cofanSigma {ι : Type u} [Finite ι]
    (A : ι → SeparatedFiniteEtaleOver.{u} X) : Limits.Cofan A :=
  Limits.Cofan.mk (SeparatedFiniteEtaleOver.sigma A) (SeparatedFiniteEtaleOver.sigmaι A)

/-- **The disjoint union of finitely many separated covers is their coproduct in this category.**

**The proof term is
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isColimitCofanSigma`'s character for character**,
and that is a `diff` of the two bodies rather than a way of putting it. It is possible because
that proof names no morphism property: `CategoryTheory.Limits.Cofan.IsColimit.mk` takes a descent
map, a factorisation and a uniqueness field, and all three are built out of
`ComplexAnalytic.AnalyticSpace.sigmaDesc`,
`ComplexAnalytic.AnalyticSpace.sigmaι_sigmaDesc` and
`ComplexAnalytic.AnalyticSpace.hom_ext_sigma` wrapped in
`CategoryTheory.MorphismProperty.Over.homMk`,
`CategoryTheory.MorphismProperty.Over.w` and
`CategoryTheory.MorphismProperty.Over.Hom.ext`, which are the comma category's own API at any
property whatever. **What the objects of this category carry beyond a cover is never inspected**;
it is discharged once, in
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.sigma`, and the colimit cannot see it.

**The descent map is built and not reflected**, so nothing here asks the inclusion into the covers
to be full: the map out of the disjoint union is
`ComplexAnalytic.AnalyticSpace.sigmaDesc` of the competing cocone's legs, read as a morphism over
the base. The module docstring says what the alternative would have cost.

**Some citations of `ComplexAnalytic.AnalyticSpace.sigmaι_sigmaDesc` have their arguments written
out and some leave them to unification**, exactly as in the ambient proof and for the reason its
docstring gives: where they are written out the unifier would otherwise have to see through
`CategoryTheory.MorphismProperty.Over.homMk`'s underlying morphism, or through the cofan's apex, to
a `ComplexAnalytic.AnalyticSpace.sigmaDesc`. -/
noncomputable def SeparatedFiniteEtaleOver.isColimitCofanSigma {ι : Type u} [Finite ι]
    (A : ι → SeparatedFiniteEtaleOver.{u} X) :
    Limits.IsColimit (SeparatedFiniteEtaleOver.cofanSigma A) :=
  Limits.Cofan.IsColimit.mk _
    (fun t ↦ MorphismProperty.Over.homMk
      (AnalyticSpace.sigmaDesc (fun i ↦ (A i).left) fun i ↦ (t.inj i).left)
      (AnalyticSpace.hom_ext_sigma _ fun i ↦
        (Category.assoc _ _ _).symm.trans
          (((congrArg (· ≫ t.pt.hom) (AnalyticSpace.sigmaι_sigmaDesc _ _ i)).trans
            (MorphismProperty.Over.w (t.inj i))).trans
            (AnalyticSpace.sigmaι_sigmaDesc (fun i ↦ (A i).left)
              (fun i ↦ (A i).hom) i).symm)))
    (fun _ i ↦ MorphismProperty.Over.Hom.ext (AnalyticSpace.sigmaι_sigmaDesc _ _ i))
    (fun t _ h ↦ MorphismProperty.Over.Hom.ext <|
      AnalyticSpace.hom_ext_sigma _ fun i ↦
        (congrArg (fun f : A i ⟶ t.pt ↦ f.left) (h i)).trans
          (AnalyticSpace.sigmaι_sigmaDesc (fun i ↦ (A i).left)
            (fun i ↦ (t.inj i).left) i).symm)

/-! ### The class -/

/-- **The category has colimits of every finite discrete shape of its own universe.**

`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.hasColimitsOfShape_discrete`'s body at this
category, which is `CategoryTheory.Limits.Cocone.precompose` at
`CategoryTheory.Discrete.natIsoFunctor` — the step that turns an arbitrary functor out of a
discrete category into the family of objects it is determined by — applied to
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.cofanSigma`. The
ambient docstring says why `CategoryTheory.Limits.hasCoproducts_of_colimit_cofans` cannot be used
instead and that argument is not repeated here.

**A `theorem` and not an `instance`, and the reason was rechecked rather than copied.**
`Mathlib/CategoryTheory/Limits/Shapes/FiniteProducts.lean` derives this class at a discrete shape
on a finite index type from `CategoryTheory.Limits.HasFiniteCoproducts`, so once
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.hasFiniteCoproducts` is in scope instance
search answers this statement without it. Checked by elaborating `inferInstance` at this statement
with this declaration left a `theorem`, at the commit that adds this module. -/
theorem SeparatedFiniteEtaleOver.hasColimitsOfShape_discrete (ι : Type u) [Finite ι]
    (X : AnalyticSpace.{u}) :
    Limits.HasColimitsOfShape (Discrete ι) (SeparatedFiniteEtaleOver.{u} X) where
  has_colimit F := Limits.HasColimit.mk
    ⟨(Limits.Cocone.precompose Discrete.natIsoFunctor.hom).obj
      (SeparatedFiniteEtaleOver.cofanSigma fun j ↦ F.obj ⟨j⟩),
      (Limits.IsColimit.precomposeHomEquiv _ _).symm
        (SeparatedFiniteEtaleOver.isColimitCofanSigma _)⟩

/-- **The category of covers separated over the base has finite coproducts**, with no hypothesis on
the base.

**This is a Galois-category field at this category**, as
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.hasTerminal` is: the class in
`Mathlib/CategoryTheory/Galois/Basic.lean`, whose namespace is not in this repository's import
closure and so cannot be cited by name here, carries a field of exactly this class at exactly the
category the monomorphism field is stated over. **It is one field and not the class**, and the
module docstring says which of the five it is, which three else hold at the commit this is written
at, and where the remaining one stands.

**The universe crossing is the whole of the step**, as in the ambient declaration:
`CategoryTheory.Limits.HasFiniteCoproducts` quantifies over `Fin n`, which lives in `Type 0`, while
`ComplexAnalytic.AnalyticSpace.sigma` takes its index type from `Type u`, and
`CategoryTheory.Discrete.equivalence` at `Equiv.ulift` is what crosses between them. That
declaration's docstring argues the step and this one does not repeat the argument.

**An `instance` and not a `theorem`, for the reason its ambient counterpart is one**: it is the
form a `CategoryTheory.Limits.HasFiniteCoproducts` consumer asks for, and the Galois-category
definition carries this field as an instance. -/
instance SeparatedFiniteEtaleOver.hasFiniteCoproducts (X : AnalyticSpace.{u}) :
    Limits.HasFiniteCoproducts (SeparatedFiniteEtaleOver.{u} X) :=
  ⟨fun n ↦
    haveI := SeparatedFiniteEtaleOver.hasColimitsOfShape_discrete (ULift.{u} (Fin n)) X
    Limits.hasColimitsOfShape_of_equivalence (Discrete.equivalence Equiv.ulift.{u})⟩

end ComplexAnalytic.AnalyticSpace
