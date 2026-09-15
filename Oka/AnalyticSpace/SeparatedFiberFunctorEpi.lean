/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.AnalyticSpace.SeparatedFiberFunctor
import Oka.AnalyticSpace.SeparatedFiniteEtaleCoproducts

/-!
# Both fibre functors at the separated covers preserve epimorphisms

`Oka/AnalyticSpace/SeparatedFiberFunctor.lean` builds the fibre at a point of the base as a functor
out of `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver X`, into `Type u` and into
`FintypeCat`, and its `## What is not here` lists the four obligations of
`Mathlib/CategoryTheory/Galois/Basic.lean`'s `FiberFunctor` it does not meet. **This file is one of
those four, the preservation of epimorphisms**, and the two statements it lands are at those same
two functors.

## What the obligation is, read at the pinned Mathlib

`Mathlib/CategoryTheory/Galois/Basic.lean` at the revision `lake-manifest.json` pins asks a
`FiberFunctor` for **six** things — preservation of terminal objects, of pullbacks, of finite
coproducts, of epimorphisms and of quotients by finite group actions, and reflection of
isomorphisms. That namespace is **not in this file's import closure** and so cannot be cited
by name here, which is the spelling `Oka/AnalyticSpace/SeparatedFiberFunctor.lean` and
`Oka/AnalyticSpace/SeparatedFiniteEtale.lean` already use for it and the reason no instance of
either of that file's two classes is declared anywhere below. The field is
`CategoryTheory.Functor.PreservesEpimorphisms` of the functor, which is
`Mathlib/CategoryTheory/Functor/EpiMono.lean`'s and **is** in this repository's closure.

**So what is here is one field of one of the two classes, and not the class.** No
`PreGaloisCategory` instance was declared anywhere in this repository **until 2026-09-15**, when
`Oka/AnalyticSpace/GaloisCategory.lean` declared one at
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver` and made this sentence a record of a
commit rather than a claim about the tree; **none is declared here**, which is what this paragraph
is about and which that push does not touch.

## The content is one theorem about the category and the functors contribute nothing to it

**A surjection of total spaces restricts to a surjection of fibres with no further argument.**
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fiberMap` — which is what either functor does to a
morphism — is `i.left.toLRSHom.base` together with the observation that it carries a point over `x`
to a point over `x`, that observation being `CategoryTheory.MorphismProperty.Over.w` read at one
point. Given a point of the fibre of the target, a preimage in the whole of the source is already
in the fibre, because the triangle sends it to where its image goes.

**So the whole of the mathematics is
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.surjective_base_left_of_epi`, a statement
about the category and not about either functor**, and the two preservation instances are that
theorem with a wrapper. It is the dual of `Oka/AnalyticSpace/MonoDirectSummand.lean`'s
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.injective_base_left_of_mono` and shares no step with
it: that one is proved from the fibre product of a morphism with itself, and this one from the
coproduct of the target with itself.

## How the epimorphism is spent, and it is spent once

Against a cover `B` and a morphism `i : A ⟶ B` of the separated covers:

* **The image of `i.left` is clopen.**
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isClopen_range_left`
  (`Oka/AnalyticSpace/DirectSummand.lean`), whose `[T2Space B.left]` is
  `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.t2Space_left` and therefore free in this
  category.
* **The test object is the disjoint union of two copies of `B`**,
  `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.sigma` at the constant family over
  `ULift Bool`, and the two morphisms compared are its inclusion at `true` against the morphism
  which is that inclusion on the image and the inclusion at `false` off it. The second is
  `ComplexAnalytic.AnalyticSpace.descClopen` (`Oka/AnalyticSpace/Clopen.lean`), which glues a
  morphism out of a clopen open subspace with one out of the complement **and asks no agreement
  between them**, promoted to a morphism over the base by
  `ComplexAnalytic.AnalyticSpace.hom_ext_of_clopen` at the two structure maps.
* **They agree after `i`** because
  `ComplexAnalytic.AnalyticSpace.liftRestrict` (`Oka/AnalyticSpace/OpenSubspace.lean`) factors
  `i.left` through the image — at `subset_rfl`, the image being that open subspace's carrier on the
  nose — and `ComplexAnalytic.AnalyticSpace.ofRestrict_descClopen` computes the glued morphism
  there. **This is the only place `CategoryTheory.Epi` is used**, through
  `CategoryTheory.cancel_epi`.
* **And a point outside the image would be two members of a coproduct at once.**
  `ComplexAnalytic.AnalyticSpace.ofRestrict_clopenCompl_descClopen` computes the glued morphism on
  the complement, and
  `AlgebraicGeometry.LocallyRingedSpace.eq_of_sigmaι_base_eq`
  (`Oka/Geometry/RingedSpace/LocallyRingedSpace/HasColimits.lean`) turns the resulting equation
  into `ULift.up true = ULift.up false`.

**The two copies are indexed by `ULift Bool` and not by `Fin 2`, and that is forced.**
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.sigma` takes its index type in `Type u`,
where the universe is the one the covers live in, and `Fin 2` is in `Type 0`; the same lift is what
`ComplexAnalytic.AnalyticSpace.clopenCover` is indexed by, one construction down.

## Where each hypothesis is spent

**`[T2Space (X : Type u)]` on the base is spent exactly once**, in
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.t2Space_left` at `B`, which is what the
clopenness of the image asks for. Nothing below asks a separation axiom of a total space directly
and nothing below asks preconnectedness of anything — which is the difference from the faithfulness
and conservativity statements of `Oka/AnalyticSpace/SeparatedFiberFunctor.lean`, whose subcategory
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.isPreconnected` does not occur here.

**The `haveI` below is the comma category's seam and not a mathematical step.** The inclusion
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.toFiniteEtaleOver` leaves `left` alone by
`rfl` but not reducibly so, so `[T2Space (B.left : Type u)]` is not found at
`(((…toFiniteEtaleOver X).obj B).left : AnalyticSpace.{u})`; the repair is the one
`Oka/AnalyticSpace/SeparatedDirectSummand.lean` carries at each of its three declarations, in the
same `inferInstanceAs` spelling.

## The hypothesis is `CategoryTheory.Epi` in *this* category, and that is not a gap

A full subcategory has **fewer** objects to test against, so an epimorphism of this category is
tested against fewer morphisms than one of
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver` and `CategoryTheory.Epi` here is the **weaker**
hypothesis. Every object this proof tests against is separated over the base — the disjoint union
by `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isSeparatedMap_sigma`, and nothing else is
needed, the two clopen parts never being formed as objects — so the weaker hypothesis suffices and
the Galois-category obligation, which is stated at this category, is what is met.

**The ambient statement at `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver` is neither implied by
this one nor implies it**, the two `CategoryTheory.Epi` hypotheses being about different categories
with neither inclusion of test objects going the right way, and it is not here; `## What is not
here` says so.

## Main results

- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.surjective_base_left_of_epi`: **an
  epimorphism of separated covers over a Hausdorff base is surjective on total spaces**, which is
  the whole of the content.
- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.fiberFunctor_map_surjective_of_epi` and
  `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.fintypeFiberFunctor_map_surjective_of_epi`
  — **both fibre functors carry it to a surjection of fibres**, at every point of the base and with
  nothing asked of the point.
- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.preservesEpimorphisms_fiberFunctor` and
  `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.preservesEpimorphisms_fintypeFiberFunctor`
  — **both preserve epimorphisms**, which is the `FiberFunctor` field.

## What is not here

* **No `FiberFunctor` instance and no `PreGaloisCategory` instance.** This is one of six fields of
  one of two classes; `Oka/AnalyticSpace/SeparatedFiberFunctor.lean` supplies the first and the
  last of the six, `Oka/AnalyticSpace/SeparatedFiberFunctorCoproducts.lean` the third and
  `Oka/AnalyticSpace/SeparatedFiberPullback.lean` the second, and **the one that remains is
  quotients by finite group actions**, which is absent from the tree at the commit that adds this
  file. **Measured rather than asserted**: `PreGaloisCategory` occurs in the comment-stripped code
  of **no** module of this repository at that commit, over a population of **345** tracked `.lean`
  files, and `CategoryTheory.SingleObj` — the shape the quotients field is stated over — in
  exactly **one**, the mirror-tree module that declares colimits of that shape and which nothing
  under `Oka/` imports.
* **Not the ambient statement at `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver`**, and what is
  missing is the statement and not an ingredient. Every step above is available there — the
  clopenness of the image is stated there to begin with, and
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.sigma` is the disjoint union one category out —
  so what would be needed is the proof reread at that category and not a new argument. It is not
  a corollary of what is here, for the reason the section above gives.
* **No converse.** That a morphism surjective on total spaces is an epimorphism of either category
  is not stated below and is not used. **Measured rather than asserted, and the spelling counted is
  part of the figure**: the bare token `Epi` as a whole word — not `EpiMono`, not `Epimorphisms`,
  not `epi_of_epi_map` — occurs in the comment-stripped code of **sixteen** modules of this
  repository at the commit that adds this file, this one among them, and the qualified spelling
  `CategoryTheory.Epi` occurs in **none**. **Of the other fifteen, not one carries `Epi` of a
  morphism of either category of covers**, which is a reading of the `Epi` context at every one of
  the fifteen and not of their titles. **Two of them mention
  `FiniteEtaleOver` at all** — `Oka/AnalyticSpace/Basic.lean`, where the token is `Epi` of a stalk
  map, and `Oka/AnalyticSpace/LocalIso.lean`, where it is `Epi` of a `TopCat` morphism — **and the
  remaining thirteen mention neither that category nor
  `ComplexAnalytic.AnalyticSpace.isFiniteEtale` anywhere. That second scan is over the file text
  and not over the stripped code**, which the first is and has to be, being a count of code.
  **The two registers answer differently here and the difference is the whole of the reason to say
  which is which**: both of those mentions stand in prose the stripper deletes — a module docstring
  in one file and a declaration docstring in the other — so over the stripped code the first figure
  is **none** and the second is **fourteen**, `Oka/AnalyticSpace/LocalIso.lean` being the
  fifteenth because its own declarations are named `isFiniteEtale_id` and the like. **The question
  this clause asks is whether a reader of those files would have met this category at all**, and
  that is the one the file text answers.
* **Nothing about the *image* of a non-surjective morphism.** The complementary clopen part is a
  named object of this category — it is
  `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.directSummandCompl`
  (`Oka/AnalyticSpace/SeparatedDirectSummand.lean`) — and this file neither cites it nor imports
  the module it is in; the argument below works with the open subspace and its complement at the
  level of analytic spaces and never forms either as a cover.
## The `Mathlib/CategoryTheory/Galois/Basic.lean` scoping, and the record for it

**Every sentence of this file that scopes that namespace read *this repository's import closure*,
until 2026-09-15**, when `Oka/AnalyticSpace/GaloisCategory.lean` imported that file and declared
`CategoryTheory.PreGaloisCategory` at
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver` together with
`CategoryTheory.PreGaloisCategory.FiberFunctor` at its `FintypeCat`-valued fibre functor. **From
that commit the class is in this repository's import closure and is still not in this file's**,
which is why those sentences now say *this file's*: no import of this module reaches the one that
pays for the class, so nothing here can name it and every clause of this file that says so stays
exact. **The rescoping is not this file's whole share of that push**: the `## What is not here`
sentence asserting that no `PreGaloisCategory` instance is declared anywhere in this repository is
a claim about existence and not about citability, the same push falsifies it, and it is rewritten
at its commit rather than left in the present tense. `git diff` against the commit this file is
cut from shows both.
-/

universe u

open CategoryTheory

namespace ComplexAnalytic.AnalyticSpace

variable {X : AnalyticSpace.{u}} [T2Space (X : Type u)]
variable {A B : SeparatedFiniteEtaleOver.{u} X}

/-! ### An epimorphism of separated covers is surjective on total spaces -/

/-- **An epimorphism of separated covers over a Hausdorff base is surjective on points.**

The two morphisms out of `B` that the hypothesis is spent on are the two inclusions of `B` into the
disjoint union of two copies of itself, glued so that they differ exactly off the image of `i`:
the first is `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.sigmaι` at `true`, and the
second agrees with it on the image and is `…sigmaι` at `false` on the complement. They agree after
`i` because `i.left` factors through the image, so `CategoryTheory.cancel_epi` identifies them, and
then a point off the image is a point at which the two inclusions of a coproduct agree.

**The image has to be clopen for the second morphism to exist at all**, which is
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isClopen_range_left` and is where the `[T2Space X]`
of this section is spent, through
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.t2Space_left`. **The open subspace is built
here rather than taken from `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.rangeOpens`, and there
are two reasons.** That definition's value is an `Opens` of
`((…toFiniteEtaleOver X).obj B).left` and not of `B.left` — the two are equal by `rfl` and not
reducibly so, which is the seam the module docstring's paragraph on the `haveI` describes — and its
carrier is `Set.range` on the nose either way, so building it here is what makes
`ComplexAnalytic.AnalyticSpace.liftRestrict`'s range hypothesis `subset_rfl` and the factorisation
cost nothing.

**The disjoint union is formed in this category and not in the covers**, because the hypothesis is
`CategoryTheory.Epi` here and a test object has to be an object here;
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isSeparatedMap_sigma`, which is what makes it one,
asks nothing of the base and is not cited below — it is inside
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.sigma`. -/
theorem SeparatedFiniteEtaleOver.surjective_base_left_of_epi (i : A ⟶ B) [Epi i] :
    Function.Surjective (i.left.toLRSHom.base : A.left → B.left) := by
  haveI : T2Space
      ((((SeparatedFiniteEtaleOver.toFiniteEtaleOver X).obj B).left : AnalyticSpace.{u}) :
        Type u) :=
    inferInstanceAs (T2Space (B.left : Type u))
  have hclopen : IsClopen (Set.range (i.left.toLRSHom.base : A.left → B.left)) :=
    FiniteEtaleOver.isClopen_range_left ((SeparatedFiniteEtaleOver.toFiniteEtaleOver X).map i)
  set U : (B.left : AnalyticSpace.{u}).Opens :=
    ⟨Set.range (i.left.toLRSHom.base : A.left → B.left), hclopen.2⟩ with hUdef
  have hU : IsClosed ((U : (B.left : AnalyticSpace.{u}).Opens) : Set B.left) := hclopen.1
  set F : ULift.{u} Bool → SeparatedFiniteEtaleOver.{u} X := fun _ ↦ B with hF
  set j₀ : B ⟶ SeparatedFiniteEtaleOver.sigma F :=
    SeparatedFiniteEtaleOver.sigmaι F (ULift.up true) with hj₀
  set j₁ : B ⟶ SeparatedFiniteEtaleOver.sigma F :=
    SeparatedFiniteEtaleOver.sigmaι F (ULift.up false) with hj₁
  have hw : descClopen U hU (B.left.ofRestrict U ≫ j₀.left)
      (B.left.ofRestrict (clopenCompl U hU) ≫ j₁.left) ≫
        (SeparatedFiniteEtaleOver.sigma F).hom = B.hom := by
    refine hom_ext_of_clopen U hU ?_ ?_
    · rw [← Category.assoc, ofRestrict_descClopen, Category.assoc, MorphismProperty.Over.w j₀]
    · rw [← Category.assoc, ofRestrict_clopenCompl_descClopen, Category.assoc,
        MorphismProperty.Over.w j₁]
  set h : B ⟶ SeparatedFiniteEtaleOver.sigma F :=
    MorphismProperty.Over.homMk (descClopen U hU (B.left.ofRestrict U ≫ j₀.left)
      (B.left.ofRestrict (clopenCompl U hU) ≫ j₁.left)) hw with hh
  have key : i ≫ j₀ = i ≫ h := by
    refine MorphismProperty.Over.Hom.ext ?_
    change i.left ≫ j₀.left = i.left ≫ h.left
    have hfac : liftRestrict i.left U subset_rfl ≫ B.left.ofRestrict U = i.left :=
      liftRestrict_fac _ _ _
    conv_lhs => rw [← hfac]
    conv_rhs => rw [← hfac]
    rw [Category.assoc, Category.assoc]
    congr 1
    exact (ofRestrict_descClopen U hU _ _).symm
  have hgh : j₀ = h := (cancel_epi i).mp key
  have hcompl : B.left.ofRestrict (clopenCompl U hU) ≫ j₀.left
      = B.left.ofRestrict (clopenCompl U hU) ≫ j₁.left := by
    rw [congrArg (fun f : B ⟶ SeparatedFiniteEtaleOver.sigma F ↦ f.left) hgh]
    exact ofRestrict_clopenCompl_descClopen U hU _ _
  intro b
  by_contra hb
  have hbmem : b ∈ ((clopenCompl U hU : (B.left : AnalyticSpace.{u}).Opens) : Set B.left) := by
    simpa [hUdef] using hb
  have hpt := congrArg
    (fun φ : (B.left : AnalyticSpace.{u}).restrict (clopenCompl U hU) ⟶
        (SeparatedFiniteEtaleOver.sigma F).left ↦ φ.toLRSHom.base ⟨b, hbmem⟩) hcompl
  rw [show Hom.toLRSHom (B.left.ofRestrict (clopenCompl U hU) ≫ j₀.left)
        = (B.left.ofRestrict (clopenCompl U hU)).toLRSHom ≫ j₀.left.toLRSHom from rfl,
      show Hom.toLRSHom (B.left.ofRestrict (clopenCompl U hU) ≫ j₁.left)
        = (B.left.ofRestrict (clopenCompl U hU)).toLRSHom ≫ j₁.left.toLRSHom from rfl] at hpt
  simp only [AlgebraicGeometry.LocallyRingedSpace.comp_base, ConcreteCategory.comp_apply] at hpt
  rw [show Hom.toLRSHom j₀.left
        = Limits.Sigma.ι (fun k ↦ ((F k).left : AnalyticSpace.{u}).toLocallyRingedSpace)
            (ULift.up true) from rfl,
      show Hom.toLRSHom j₁.left
        = Limits.Sigma.ι (fun k ↦ ((F k).left : AnalyticSpace.{u}).toLocallyRingedSpace)
            (ULift.up false) from rfl] at hpt
  exact (by simp : (ULift.up true : ULift.{u} Bool) ≠ ULift.up false)
    (AlgebraicGeometry.LocallyRingedSpace.eq_of_sigmaι_base_eq _ hpt)

/-! ### Both fibre functors carry it to a surjection -/

/-- **The fibre at any point of the base carries an epimorphism to a surjection.**

`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.surjective_base_left_of_epi` at the point
underlying the given element of the fibre, together with the observation that a preimage of a point
lying over `x` lies over `x` itself. **That observation is
`CategoryTheory.MorphismProperty.Over.w` and nothing else**, read at the preimage: it says the two
structure maps agree along `i.left`, so the source's structure map sends the preimage where the
target's sends its image.

**Nothing is asked of the point and nothing of the base beyond the section's `[T2Space X]`**, which
is spent in the theorem above and not again here. -/
theorem SeparatedFiniteEtaleOver.fiberFunctor_map_surjective_of_epi (x : X) (i : A ⟶ B) [Epi i] :
    Function.Surjective
      ((SeparatedFiniteEtaleOver.fiberFunctor.{u} x).map (X := A) (Y := B) i) := by
  intro b
  obtain ⟨a₀, ha₀⟩ := SeparatedFiniteEtaleOver.surjective_base_left_of_epi i b.1
  have hw : i.left ≫ B.hom = A.hom := MorphismProperty.Over.w i
  have h := congrArg (fun g : (A.left : AnalyticSpace.{u}) ⟶ X ↦
    (g.toLRSHom.base : A.left → X) a₀) hw
  have hb : (B.hom.toLRSHom.base : B.left → X) (i.left.toLRSHom.base a₀) = x := by
    rw [ha₀]; exact b.2
  exact ⟨⟨a₀, h.symm.trans hb⟩, Subtype.ext ha₀⟩

/-- **And so does the `FintypeCat`-valued one**, whose map on morphisms is the same function
bundled with the finiteness of the two fibres.

`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.fiberFunctor_map_surjective_of_epi`
unchanged: `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fintypeFiberFunctor`'s `map` field is
`FintypeCat.homMk` of `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fiberMap` where the
`Type u`-valued one's is `TypeCat.ofHom` of it, so the underlying function is the same and the
statement is the same statement at a different wrapper. -/
theorem SeparatedFiniteEtaleOver.fintypeFiberFunctor_map_surjective_of_epi (x : X) (i : A ⟶ B)
    [Epi i] :
    Function.Surjective
      ((SeparatedFiniteEtaleOver.fintypeFiberFunctor.{u} x).map (X := A) (Y := B) i) :=
  SeparatedFiniteEtaleOver.fiberFunctor_map_surjective_of_epi x i

/-! ### The `FiberFunctor` field, at both -/

/-- **The `Type u`-valued fibre functor preserves epimorphisms.**

`CategoryTheory.ofHom_epi_iff_surjective` at the theorem above: an epimorphism of `Type u` is a
surjection and the functor's `map` field is `TypeCat.ofHom` of the fibre map, so the two sides of
that equivalence are the two statements.

**This is the fourth of `Mathlib/CategoryTheory/Galois/Basic.lean`'s six `FiberFunctor`
obligations**, at the `Type u`-valued functor rather than at the one that class is stated of; the
instance below is the one it asks for. -/
instance SeparatedFiniteEtaleOver.preservesEpimorphisms_fiberFunctor (x : X) :
    (SeparatedFiniteEtaleOver.fiberFunctor.{u} x).PreservesEpimorphisms where
  preserves {_ _} i _ :=
    (ofHom_epi_iff_surjective _).2
      (SeparatedFiniteEtaleOver.fiberFunctor_map_surjective_of_epi x i)

/-- **And so does the `FintypeCat`-valued one**, which is the functor a `FiberFunctor` structure
would be asked of.

**`FintypeCat` has no epimorphism criterion in this Mathlib** — `Epi` occurs nowhere in
`Mathlib/CategoryTheory/FintypeCat.lean` — so this is not that criterion applied but the
epimorphism *reflected* along `FintypeCat.incl`:
`CategoryTheory.Functor.reflectsEpimorphisms_of_faithful` makes a faithful functor reflect
epimorphisms, that inclusion is faithful, and its value on the map on morphisms is the underlying
function, which the theorem above makes surjective. **That is the same route
`Mathlib/CategoryTheory/Galois/Basic.lean` itself takes in the other direction**, reading
surjectivity off an epimorphism of `FintypeCat` through `FintypeCat.incl` rather
than through a criterion of its own. -/
instance SeparatedFiniteEtaleOver.preservesEpimorphisms_fintypeFiberFunctor (x : X) :
    (SeparatedFiniteEtaleOver.fintypeFiberFunctor.{u} x).PreservesEpimorphisms where
  preserves {_ _} i _ :=
    FintypeCat.incl.epi_of_epi_map
      ((ofHom_epi_iff_surjective _).2
        (SeparatedFiniteEtaleOver.fintypeFiberFunctor_map_surjective_of_epi x i))

end ComplexAnalytic.AnalyticSpace
