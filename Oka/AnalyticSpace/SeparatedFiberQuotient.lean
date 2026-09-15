/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.AnalyticSpace.QuotientColimit
import Oka.AnalyticSpace.SeparatedFiberFunctor

/-!
# Both fibre functors at the separated covers preserve quotients by finite group actions

`Oka/AnalyticSpace/QuotientColimit.lean` gives
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver` colimits of shape
`CategoryTheory.SingleObj G` for every finite group `G`, by building the quotient of the acted-on
cover and showing its cocone universal. **This file is the statement that the two fibre functors
carry that colimit to a colimit**, which is the sixth and last of the obligations
`Mathlib/CategoryTheory/Galois/Basic.lean`'s `FiberFunctor` carries.

## What the obligation is, read at the pinned Mathlib

At the revision `lake-manifest.json` pins, the fifth field of that class in the order it lists them
is

```lean
  /-- `F` preserves quotients by finite groups (G5). -/
  preservesQuotientsByFiniteGroups (G : Type u₂) [Group G] [Finite G] :
    PreservesColimitsOfShape (SingleObj G) F := by infer_instance
```

with `u₂` the hom universe of the category. That namespace is **not in this file's import
closure** and so cannot be cited by name here, which is the spelling the whole of this
neighbourhood uses and the reason no instance of either of that file's two classes is declared
anywhere below. **The two instances below ask nothing of the universe of `G`**, so they cover that
field's `u₂` whatever the hom universe of this category is.

## The content is one identification and the rest is `Quotient.lift`

**The fibre of the quotient is the orbit set of the fibre**, and that is the whole of the
mathematics. The action is over the base, so every orbit lies in a single fibre; the quotient map
is surjective on each fibre because `ComplexAnalytic.AnalyticSpace.orbitMk` is surjective and the
descended structure map computes on a representative by `rfl`; and two points of one fibre have the
same image exactly when one is a translate of the other, which is the orbit relation of the
restricted action.
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.singleObjFiberQuotientEquiv` is that
identification, named so that a caller can have it without going through a colimit — the
reason `Oka/AnalyticSpace/DirectSummand.lean` gives for naming its summand.

**The colimit statement is then `Quotient.lift` through that equivalence.** A cocone under the
composite functor is a `G`-invariant map out of the fibre; the factor is its lift, the
factorisation is `Equiv.symm_apply_eq` at one point, and uniqueness is the surjectivity above. **No
finiteness of the fibre and no finiteness of `G` is spent below** — both are spent in the module
this one imports, in making the orbit space a cover at all.

## The action on the fibre is written from the automorphism and not restricted from the total space

`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.singleObjFiberSMul` defines `g • a` as the
underlying map of `…singleObjAut F g` at `a`, with the membership crossed by
`…singleObjAut_base_over`. **Restricting the total-space action instead does not elaborate**: the
fibre is taken at `(…toFiniteEtaleOver X).obj (F.obj …)` and the action is on `(F.obj …).left`, and
those two spellings of one type are `rfl`-equal without being syntactically equal, so neither
instance search nor `inferInstanceAs` crosses between them and the hypothesis of a restriction
lemma arrives at the wrong spelling. **That is the same seam
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.quotient` records for its own `@`-passed
instances**, met one functor further out.

## Main definitions

- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.singleObjFiber`: the fibre of the object a
  functor out of `CategoryTheory.SingleObj G` names, and
  `…SeparatedFiniteEtaleOver.singleObjFiberSMul` the action of `G` on it.
- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.singleObjFiberMk`: the quotient map read
  at that fibre, which is the cocone leg the two instances are about.
- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.singleObjFiberQuotientEquiv`: **the fibre
  of the quotient is the orbit set of the fibre.**

## Main results

- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.singleObjFiberMk_surjective` and
  `…SeparatedFiniteEtaleOver.singleObjFiberMk_eq_iff`: the two halves that identification is built
  from, each usable on its own.
- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.singleObjFiberIsColimit`: **the image of
  the quotient cocone under the `Type u`-valued fibre functor is a colimit.**
- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.preservesQuotients_fiber` and
  `…SeparatedFiniteEtaleOver.preservesQuotients_fintypeFiber`: **both fibre functors preserve
  colimits of shape `CategoryTheory.SingleObj G` for every finite group `G`.**

## What is not here

* **No `FiberFunctor` instance and no `PreGaloisCategory` instance.** This is one field of one of
  those two classes and not the class; `PreGaloisCategory` occurs in the comment-stripped code of
  **no** module of this repository at the commit that adds this file. **With this file all six
  `FiberFunctor` obligations are stated at both functors** — the terminal object, pullbacks, finite
  coproducts, epimorphisms, conservativity and this one — and assembling them is not done below.
* **Nothing at `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver`.** The ambient covers have no
  statement about `CategoryTheory.SingleObj` at all, so there is no ambient statement to transport
  and none is made: the quotient this is about is the separated category's, and it is the one
  `Oka/AnalyticSpace/QuotientColimit.lean` builds.
* **No second colimit and no coequaliser.** The cocone below is the one that module lands and the
  colimit property of the cocone in the covers is cited rather than reproved; nothing here bears on
  `CategoryTheory.Limits.HasFiniteColimits` at either category, which is still not available.
* **Nothing about the action beyond its being over the base** — no freeness, no stabilisers, and no
  statement counting orbits or comparing the degree of the quotient with the degree of the cover.
  `Oka/AnalyticSpace/Degree.lean` is where such a statement would go and this file adds none.
* **The `FintypeCat`-valued instance is not derived by re-proving anything.** It is the `Type u` one
  reflected along `FintypeCat.incl`, which reflects colimits by instance search, and
  the two functors differ by that inclusion by `rfl` — the derivation
  `Oka/AnalyticSpace/SeparatedFiberFunctorCoproducts.lean` names as available and does not take for
  its own pair, because there it had two ambient instances to compose instead and here there are
  none.
## The `Mathlib/CategoryTheory/Galois/Basic.lean` scoping, and the record for it

**Every sentence of this file that scopes that namespace read *this repository's import closure*,
until 2026-09-15**, when `Oka/AnalyticSpace/GaloisCategory.lean` imported that file and declared
`CategoryTheory.PreGaloisCategory` at
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver` together with
`CategoryTheory.PreGaloisCategory.FiberFunctor` at its `FintypeCat`-valued fibre functor. **From
that commit the class is in this repository's import closure and is still not in this file's**,
which is why those sentences now say *this file's*: no import of this module reaches the one that
pays for the class, so nothing here can name it and every clause of this file that says so stays
exact. The rescoping is this file's whole share of that push, and `git diff` against the commit it
is cut from shows it.
-/

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry TopCat Topology

universe u

noncomputable section

namespace ComplexAnalytic.AnalyticSpace

variable {X : AnalyticSpace.{u}} [T2Space (X : Type u)]
variable {G : Type*} [Group G] [Finite G] (F : SingleObj G ⥤ SeparatedFiniteEtaleOver.{u} X)
variable (x : X)

/-- **The fibre over `x` of the object a functor out of `CategoryTheory.SingleObj G` names.**

An `abbrev`, so that the two instances below are found at the spelling a caller meets them in: the
fibre functor's value at that object is this type by `rfl`, and instance search runs at reducible
transparency. -/
abbrev SeparatedFiniteEtaleOver.singleObjFiber : Type u :=
  FiniteEtaleOver.fiber.{u} x
    ((SeparatedFiniteEtaleOver.toFiniteEtaleOver X).obj (F.obj (SingleObj.star G)))

/-- **The action of `G` on that fibre.**

`g • a` is the underlying map of
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.singleObjAut` at `a`, and the point stays
in the fibre because the action is over the base — which is
`…SeparatedFiniteEtaleOver.singleObjAut_base_over` and the only place that statement is spent here.
The two laws are the two laws of that automorphism read at a point, through `Subtype.ext`.

**Reducible and not an instance**, for the reason
`…SeparatedFiniteEtaleOver.singleObjSMul` gives of the action on the total space: it depends on the
functor, so a global instance would have nothing to key on, and every declaration below introduces
it with `letI`. -/
@[reducible] def SeparatedFiniteEtaleOver.singleObjFiberSMul :
    MulAction G (SeparatedFiniteEtaleOver.singleObjFiber F x) where
  smul g a := ⟨(SeparatedFiniteEtaleOver.singleObjAut F g).left.toLRSHom.base a.1, by
    change (F.obj (SingleObj.star G)).hom.toLRSHom.base
        ((SeparatedFiniteEtaleOver.singleObjAut F g).left.toLRSHom.base a.1) ∈ ({x} : Set X)
    rw [SeparatedFiniteEtaleOver.singleObjAut_base_over F g a.1]
    exact a.2⟩
  one_smul a := by
    apply Subtype.ext
    change (SeparatedFiniteEtaleOver.singleObjAut F 1).left.toLRSHom.base a.1 = a.1
    rw [SeparatedFiniteEtaleOver.singleObjAut_one]
    rfl
  mul_smul g₁ g₂ a := by
    apply Subtype.ext
    change (SeparatedFiniteEtaleOver.singleObjAut F (g₁ * g₂)).left.toLRSHom.base a.1
      = (SeparatedFiniteEtaleOver.singleObjAut F g₁).left.toLRSHom.base
        ((SeparatedFiniteEtaleOver.singleObjAut F g₂).left.toLRSHom.base a.1)
    rw [SeparatedFiniteEtaleOver.singleObjAut_mul]
    rfl

/-- **The quotient map read at the fibre**, which is the leg of the image cocone and the map the two
instances below are statements about.

`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fiberMap` at the quotient map of
`Oka/AnalyticSpace/QuotientColimit.lean`. An `abbrev` because it is the value of the fibre functor
at that morphism and a caller should see it as such. -/
abbrev SeparatedFiniteEtaleOver.singleObjFiberMk
    (a : SeparatedFiniteEtaleOver.singleObjFiber F x) :
    FiniteEtaleOver.fiber.{u} x ((SeparatedFiniteEtaleOver.toFiniteEtaleOver X).obj
      (SeparatedFiniteEtaleOver.singleObjQuotient F)) :=
  FiniteEtaleOver.fiberMap.{u} x
    ((SeparatedFiniteEtaleOver.toFiniteEtaleOver X).map
      (SeparatedFiniteEtaleOver.singleObjToQuotient F)) a

/-- **Its value is the orbit of the point**, which is what makes every statement below a statement
about `Quotient (MulAction.orbitRel G …)`.

`ComplexAnalytic.AnalyticSpace.base_toQuotientCover` says the underlying map of the quotient
morphism is `ComplexAnalytic.AnalyticSpace.orbitMk`, and the fibre map is that map on
representatives. **The three instances are passed positionally with `@`**, for the seam
`…SeparatedFiniteEtaleOver.quotient` records: `A.hom`'s source is spelled `(𝟭 _).obj A.left`, so a
`haveI` at the other spelling is not found. -/
theorem SeparatedFiniteEtaleOver.singleObjFiberMk_val
    (a : SeparatedFiniteEtaleOver.singleObjFiber F x) :
    letI := SeparatedFiniteEtaleOver.singleObjSMul F
    (SeparatedFiniteEtaleOver.singleObjFiberMk F x a).1
      = Quotient.mk (MulAction.orbitRel G ↥(F.obj (SingleObj.star G)).left) a.1 := by
  letI := SeparatedFiniteEtaleOver.singleObjSMul F
  haveI : ContinuousConstSMul G ↥(F.obj (SingleObj.star G)).left :=
    ⟨SeparatedFiniteEtaleOver.continuous_singleObjAut_base F⟩
  haveI := (F.obj (SingleObj.star G)).isFiniteEtale_hom
  change (SeparatedFiniteEtaleOver.singleObjToQuotient F).left.toLRSHom.base a.1 = _
  change ((F.obj (SingleObj.star G)).toQuotient
    (SeparatedFiniteEtaleOver.singleObjAut_base_over F)).left.toLRSHom.base a.1 = _
  rw [show ((F.obj (SingleObj.star G)).toQuotient
      (SeparatedFiniteEtaleOver.singleObjAut_base_over F)).left
      = @toQuotientCover X (F.obj (SingleObj.star G)).left (F.obj (SingleObj.star G)).hom G _ _ _
        (SeparatedFiniteEtaleOver.singleObjAut_base_over F) _ _
        (F.obj (SingleObj.star G)).isFiniteEtale_hom from rfl,
    @base_toQuotientCover X (F.obj (SingleObj.star G)).left (F.obj (SingleObj.star G)).hom G _ _ _
      (SeparatedFiniteEtaleOver.singleObjAut_base_over F) _ _
      (F.obj (SingleObj.star G)).isFiniteEtale_hom]
  rfl

/-- **The quotient map is surjective on the fibre.**

`Quotient.mk` is surjective, and a representative of a point of the quotient's fibre lies over `x`
because `ComplexAnalytic.AnalyticSpace.orbitDesc_apply` is `rfl`: the descended structure map at an
orbit **is** the structure map at the representative, so the fibre condition transfers with no
argument. **This is where the fibre being a fibre is used and it is the only place.** -/
theorem SeparatedFiniteEtaleOver.singleObjFiberMk_surjective :
    Function.Surjective (SeparatedFiniteEtaleOver.singleObjFiberMk F x) := by
  letI := SeparatedFiniteEtaleOver.singleObjSMul F
  haveI : ContinuousConstSMul G ↥(F.obj (SingleObj.star G)).left :=
    ⟨SeparatedFiniteEtaleOver.continuous_singleObjAut_base F⟩
  rintro ⟨p, hp⟩
  obtain ⟨y, rfl⟩ := Quotient.mk_surjective
    (s := MulAction.orbitRel G ↥(F.obj (SingleObj.star G)).left) p
  have hy : (F.obj (SingleObj.star G)).hom.toLRSHom.base y ∈ ({x} : Set X) := hp
  refine ⟨⟨y, hy⟩, ?_⟩
  apply Subtype.ext
  exact SeparatedFiniteEtaleOver.singleObjFiberMk_val F x ⟨y, hy⟩

/-- **And two points of the fibre have the same image exactly when one is a translate of the
other.**

`Quotient.exact` and `Quotient.sound` at the orbit relation of the **total space**, carried to the
fibre by `Subtype.ext` in both directions — which is what says that the orbit relation of the
restricted action is the restriction of the orbit relation, and is the only thing the two relations
need from each other. -/
theorem SeparatedFiniteEtaleOver.singleObjFiberMk_eq_iff
    (a b : SeparatedFiniteEtaleOver.singleObjFiber F x) :
    letI := SeparatedFiniteEtaleOver.singleObjFiberSMul F x
    SeparatedFiniteEtaleOver.singleObjFiberMk F x a
        = SeparatedFiniteEtaleOver.singleObjFiberMk F x b ↔ ∃ g : G, g • b = a := by
  letI := SeparatedFiniteEtaleOver.singleObjSMul F
  letI := SeparatedFiniteEtaleOver.singleObjFiberSMul F x
  constructor
  · intro h
    have h1 : Quotient.mk (MulAction.orbitRel G ↥(F.obj (SingleObj.star G)).left) a.1
        = Quotient.mk _ b.1 :=
      (SeparatedFiniteEtaleOver.singleObjFiberMk_val F x a).symm.trans
        ((congrArg Subtype.val h).trans (SeparatedFiniteEtaleOver.singleObjFiberMk_val F x b))
    obtain ⟨g, hg⟩ := Quotient.exact h1
    exact ⟨g, Subtype.ext hg⟩
  · rintro ⟨g, rfl⟩
    refine Subtype.ext
      ((SeparatedFiniteEtaleOver.singleObjFiberMk_val F x _).trans (?_ : _ = _))
    exact (Quotient.sound (s := MulAction.orbitRel G ↥(F.obj (SingleObj.star G)).left)
      ⟨g, rfl⟩).trans (SeparatedFiniteEtaleOver.singleObjFiberMk_val F x b).symm

/-- **The fibre of the quotient is the orbit set of the fibre**, which is the whole of the
mathematics of this file.

`Equiv.ofBijective` at the lift of the quotient map: injectivity is the criterion above read
through `Quotient.inductionOn₂`, and surjectivity is the surjectivity above. **Named rather than
left inside the colimit**, so that a caller who wants the set and not the universal property has
it — which is the reason `Oka/AnalyticSpace/DirectSummand.lean` gives for naming its summand
beside the existential. -/
def SeparatedFiniteEtaleOver.singleObjFiberQuotientEquiv :
    letI := SeparatedFiniteEtaleOver.singleObjFiberSMul F x
    Quotient (MulAction.orbitRel G (SeparatedFiniteEtaleOver.singleObjFiber F x))
      ≃ FiniteEtaleOver.fiber.{u} x ((SeparatedFiniteEtaleOver.toFiniteEtaleOver X).obj
          (SeparatedFiniteEtaleOver.singleObjQuotient F)) :=
  letI := SeparatedFiniteEtaleOver.singleObjFiberSMul F x
  Equiv.ofBijective
    (Quotient.lift (SeparatedFiniteEtaleOver.singleObjFiberMk F x)
      (fun a b h ↦ (SeparatedFiniteEtaleOver.singleObjFiberMk_eq_iff F x a b).2 h))
    ⟨by
      refine fun p q ↦ Quotient.inductionOn₂ p q (fun a b h ↦ ?_)
      exact Quotient.sound ((SeparatedFiniteEtaleOver.singleObjFiberMk_eq_iff F x a b).1 h),
     fun p ↦ by
      obtain ⟨a, ha⟩ := SeparatedFiniteEtaleOver.singleObjFiberMk_surjective F x p
      exact ⟨Quotient.mk _ a, ha⟩⟩

/-- **The image of the quotient cocone under the `Type u`-valued fibre functor is a colimit.**

The factor is `Quotient.lift` of the competing cocone's leg through the equivalence above, its
invariance being that cocone's own equation at `g` read at a point; the factorisation is
`Equiv.symm_apply_eq` at one point and `rfl`; and uniqueness is the surjectivity of the leg.

**Two shapes of this Mathlib are worth naming, because neither is guessable from the goal.**
A morphism of `Type u` is bundled, so the factor is built with `↾` and an equation of two of them
is applied at a point with `CategoryTheory.ConcreteCategory.congr_hom` and not with `congrFun`. -/
def SeparatedFiniteEtaleOver.singleObjFiberIsColimit :
    Limits.IsColimit ((SeparatedFiniteEtaleOver.fiberFunctor.{u} x).mapCocone
      (SeparatedFiniteEtaleOver.singleObjCocone F)) :=
  letI := SeparatedFiniteEtaleOver.singleObjFiberSMul F x
  { desc := fun s ↦ ↾(fun p ↦ Quotient.lift (fun a ↦ s.ι.app (SingleObj.star G) a)
      (fun a b h ↦ by
        obtain ⟨g, rfl⟩ := h
        have hw := ConcreteCategory.congr_hom
          (s.w (j := SingleObj.star G) (j' := SingleObj.star G) g) b
        rw [ConcreteCategory.comp_apply] at hw
        exact hw)
      ((SeparatedFiniteEtaleOver.singleObjFiberQuotientEquiv F x).symm p))
    fac := fun s j ↦ by
      ext a
      change Quotient.lift _ _ ((SeparatedFiniteEtaleOver.singleObjFiberQuotientEquiv F x).symm
          (SeparatedFiniteEtaleOver.singleObjFiberMk F x a))
        = s.ι.app (SingleObj.star G) a
      rw [show (SeparatedFiniteEtaleOver.singleObjFiberQuotientEquiv F x).symm
            (SeparatedFiniteEtaleOver.singleObjFiberMk F x a)
          = Quotient.mk _ a from (Equiv.symm_apply_eq _).2 rfl]
      rfl
    uniq := fun s m h ↦ by
      ext p
      obtain ⟨a, rfl⟩ := SeparatedFiniteEtaleOver.singleObjFiberMk_surjective F x p
      have hm : (ConcreteCategory.hom m).toFun
            (SeparatedFiniteEtaleOver.singleObjFiberMk F x a)
          = s.ι.app (SingleObj.star G) a :=
        ConcreteCategory.congr_hom (h (SingleObj.star G)) a
      rw [hm]
      change _ = Quotient.lift _ _
        ((SeparatedFiniteEtaleOver.singleObjFiberQuotientEquiv F x).symm
          (SeparatedFiniteEtaleOver.singleObjFiberMk F x a))
      rw [show (SeparatedFiniteEtaleOver.singleObjFiberQuotientEquiv F x).symm
            (SeparatedFiniteEtaleOver.singleObjFiberMk F x a)
          = Quotient.mk _ a from (Equiv.symm_apply_eq _).2 rfl]
      rfl }

/-- **The `Type u`-valued fibre functor preserves colimits of shape `CategoryTheory.SingleObj G`.**

`CategoryTheory.Limits.preservesColimit_of_preserves_colimit_cocone` at the two colimits: the
cocone `Oka/AnalyticSpace/QuotientColimit.lean` builds for the functor, and its image above.
**Every functor out of that shape gets the same pair**, the quotient being built from the functor
rather than chosen, which is why this is an instance at every `G` and not a statement about one.

**An `instance` and not a `theorem`**: the field of
`Mathlib/CategoryTheory/Galois/Basic.lean`'s `FiberFunctor` it answers is discharged by
`infer_instance`, and `#synth` at this statement fails at the base and succeeds here. -/
instance SeparatedFiniteEtaleOver.preservesQuotients_fiber :
    Limits.PreservesColimitsOfShape (SingleObj G)
      (SeparatedFiniteEtaleOver.fiberFunctor.{u} x) where
  preservesColimit {K} :=
    Limits.preservesColimit_of_preserves_colimit_cocone
      (SeparatedFiniteEtaleOver.singleObjIsColimit K)
      (SeparatedFiniteEtaleOver.singleObjFiberIsColimit K x)

/-- **And so does the `FintypeCat`-valued one**, which is the functor the class asks it of.

The same pair with the image colimit reflected along `FintypeCat.incl`, which
reflects colimits by instance search and along which the two fibre functors differ by `rfl`.
**This is the derivation
`Oka/AnalyticSpace/SeparatedFiberFunctorCoproducts.lean` names as available and does not take**:
there the `FintypeCat` statement had an ambient instance to compose with, and here there is none —
nothing at `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver` says anything about this shape — so the
reflection is the short route rather than the long one. -/
instance SeparatedFiniteEtaleOver.preservesQuotients_fintypeFiber :
    Limits.PreservesColimitsOfShape (SingleObj G)
      (SeparatedFiniteEtaleOver.fintypeFiberFunctor.{u} x) where
  preservesColimit {K} :=
    Limits.preservesColimit_of_preserves_colimit_cocone
      (SeparatedFiniteEtaleOver.singleObjIsColimit K)
      (Limits.isColimitOfReflects FintypeCat.incl
        (SeparatedFiniteEtaleOver.singleObjFiberIsColimit K x))

end ComplexAnalytic.AnalyticSpace
