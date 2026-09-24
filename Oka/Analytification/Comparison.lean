/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.AlgebraicGeometry.GammaSpecAdjunction
import Oka.Analytification.Functor

/-!
# The comparison morphism `X^an ⟶ X` is natural

`Oka/Analytification/Presentation.lean` builds, for each presentation `g`, a morphism of locally
ringed spaces `ComplexAnalytic.analytificationToSpec g : X^an_g ⟶ Spec (ℂ[x] ⧸ (g))`, and
`Oka/Analytification/Functor.lean` makes `X^an_g` functorial in `g`. Neither says the two fit
together. This file does:

```
ComplexAnalytic.analytificationToSpecNatTrans :
  analytificationFunctor ⋙ AnalyticSpace.forgetToLocallyRingedSpace ⟶ specFunctor

ComplexAnalytic.analytificationFGAlgToSpec :
  analytificationFGAlg ⋙ AnalyticSpace.forgetToLocallyRingedSpace ⟶
    toCommRingCatOp ⋙ Spec.toLocallyRingedSpace
```

The first is naturality in the *presentation*; the second is the same statement with the
presentation removed, transported along the equivalence of `Oka/Analytification/Functor.lean`.
**The second is the analytification of a finitely generated `ℂ`-algebra together with its
comparison morphism, as a single piece of structure** — `X^an ⟶ X` is no longer a construction
performed once per presentation.

## The content is `Spec` of a square that was already proved

Naturality of `analytificationToSpec` needs exactly two things, both on `master` before this file:

* `AlgebraicGeometry.LocallyRingedSpace.toΓSpec_naturality`, in the mirror tree — the canonical
  map to the spectrum of the global sections is natural;
* `ComplexAnalytic.Γ_map_analytificationMap_comp_quotientToGlobal` — pulling a section back along
  the induced morphism is applying the `ℂ`-algebra map, i.e. `ComplexAnalytic.quotientToGlobal`
  is natural.

The second is the ring-level square, proved in `Oka/Analytification/ChangeOfVariables.lean` for
functoriality of `ComplexAnalytic.analytificationMap` rather than for this, and the geometric
statement is `Spec` of it. Three module docstrings called this "the next step" without estimating
it; the estimate is one `rw` and a `congrArg`.

## `Scheme` does not appear, and that is a result rather than an omission

Both functors land in `LocallyRingedSpace`: `AnalyticSpace.forgetToLocallyRingedSpace` on one
side, `Spec.locallyRingedSpaceObj` on the other. `AlgebraicGeometry.Scheme` and
`AlgebraicGeometry.AffineScheme` appear in no statement in this file — only, as here, in prose.

That settles a question left open on `Oka/Analytification/Functor.lean`, whose source category is
the full subcategory of `CommAlgCat ℂ` on `Algebra.FiniteType`, opposite, rather than affine
`ℂ`-schemes. The reason given there for not passing to schemes was that `AffineScheme` is itself
defined as an essential image, so its inverse is a second choice-opaque object map. This file is
the evidence that the second one is never needed: the comparison is natural without it.

## `specFunctor` is not a new functor

`ComplexAnalytic.specFunctor` is stated directly — `P ↦ Spec (ℂ[x] ⧸ (g))` — so that the
naturality above is about the objects the rest of the development already names. It would be
useless if it were unrelated to `Oka/Analytification/Functor.lean`'s equivalence, so:

```
ComplexAnalytic.specFunctor_eq :
  toFGAlg ⋙ toCommRingCatOp ⋙ Spec.toLocallyRingedSpace = specFunctor
```

and it is `rfl`. That is what lets `ComplexAnalytic.analytificationFGAlgToSpec` be built by
whiskering rather than by transporting along an isomorphism, and it is why the algebra-level
statement costs four lines rather than a comparison of two composites.

## Main definitions

- `ComplexAnalytic.specFunctor`: `Spec` of the presented algebra, as a functor on presentations.
- `ComplexAnalytic.toCommRingCatOp`: a finitely generated `ℂ`-algebra, read as a commutative ring,
  opposite.
- `ComplexAnalytic.analytificationToSpecNatTrans`: **the comparison morphism is natural in the
  presentation.**
- `ComplexAnalytic.analytificationFGAlgToSpec`: **the comparison morphism is natural in the
  finitely generated `ℂ`-algebra**, with no presentation in the statement.

## Main results

- `ComplexAnalytic.analytificationToSpec_naturality`: the square itself.
- `ComplexAnalytic.specFunctor_eq`: `ComplexAnalytic.specFunctor` is `Spec` after
  `ComplexAnalytic.toFGAlg`, definitionally.
- `ComplexAnalytic.analytificationToSpecNatTrans_app` and
  `ComplexAnalytic.analytificationFGAlgToSpec_app`: the components of the two natural
  transformations. The first is `rfl`; the second is what keeps the algebra-level one from being
  a definition nothing can be computed from.
- `ComplexAnalytic.analytificationFGAlgToSpec_app_toFGAlg_obj`: **the algebra-level component at
  a presentation one has**, rather than at the one `Classical.choice` produced. A triangle
  identity of the equivalence, and the analogue for the transformation of what
  `ComplexAnalytic.analytificationFGAlgObjIso` is for the functor.

## What is not here

* **Anything non-affine.** #550's eventual goal is a functor on schemes locally of finite type,
  by gluing; nothing here glues.
* **Anything analytic.** As with `Oka/Analytification/ChangeOfVariables.lean` and
  `Oka/Analytification/Functor.lean`, every proof here is formal. The analytic content is
  upstream, in the universal property.
* **`Spec` as a functor to `Scheme`.** See above: it is not needed, not that it is missing.

## References

- [Hans Grauert and Reinhold Remmert, *Coherent analytic sheaves*][grauert-remmert1984], §A
-/

open CategoryTheory Opposite AlgebraicGeometry

universe u

noncomputable section

namespace ComplexAnalytic

variable {n k n' k' : ℕ} {g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ}
  {g' : Fin k' → MvPolynomial (ULift.{u} (Fin n')) ℂ}

/-! ### Naturality in the presentation -/

/-- **The comparison morphism `X^an ⟶ X` is natural in the presentation.**

Both sides of `ComplexAnalytic.analytificationToSpec` are `toΓSpec` followed by `Spec` of
`ComplexAnalytic.quotientToGlobal`, so the square is naturality of `toΓSpec` followed by `Spec`
of the ring-level square `ComplexAnalytic.Γ_map_analytificationMap_comp_quotientToGlobal`. -/
theorem analytificationToSpec_naturality (ψ : PresHom.{u} g g') :
    (analytificationMap.{u} ψ).toLRSHom ≫ analytificationToSpec.{u} g' =
      analytificationToSpec.{u} g ≫
        Spec.locallyRingedSpaceMap (CommRingCat.ofHom ψ.toRingHom) := by
  rw [analytificationToSpec, analytificationToSpec, ← Category.assoc,
    LocallyRingedSpace.toΓSpec_naturality (analytificationMap.{u} ψ).toLRSHom,
    Category.assoc, Category.assoc, ← Spec.locallyRingedSpaceMap_comp,
    ← Spec.locallyRingedSpaceMap_comp]
  have h : CommRingCat.ofHom (quotientToGlobal.{u} g') ≫
      LocallyRingedSpace.Γ.map (analytificationMap.{u} ψ).toLRSHom.op =
      CommRingCat.ofHom ψ.toRingHom ≫ CommRingCat.ofHom (quotientToGlobal.{u} g) :=
    CommRingCat.hom_ext (Γ_map_analytificationMap_comp_quotientToGlobal.{u} ψ)
  exact congrArg
    (fun m ↦ (AnalyticSpace.analytification.{u} g).toΓSpec ≫ Spec.locallyRingedSpaceMap m) h

/-- **`Spec` of the presented algebra, as a functor on presentations.**

Stated directly rather than as a composite so that the naturality below is about the object
`Oka/Analytification/Presentation.lean` already names; `ComplexAnalytic.specFunctor_eq` says the
two agree. Both functor laws are `Spec`'s own, after a `rfl` identifying the ring maps. -/
def specFunctor : Presentation.{u} ⥤ LocallyRingedSpace.{u} where
  obj P := Spec.locallyRingedSpaceObj (CommRingCat.of P.alg)
  map ψ := Spec.locallyRingedSpaceMap (CommRingCat.ofHom ψ.toRingHom)
  map_id P := by
    refine Eq.trans ?_ (Spec.locallyRingedSpaceMap_id (CommRingCat.of P.alg))
    rfl
  map_comp ψ χ := by
    refine Eq.trans ?_ (Spec.locallyRingedSpaceMap_comp
      (CommRingCat.ofHom χ.toRingHom) (CommRingCat.ofHom ψ.toRingHom))
    rfl

/-- **The comparison morphism, as a natural transformation on presentations.** -/
def analytificationToSpecNatTrans :
    analytificationFunctor.{u} ⋙ AnalyticSpace.forgetToLocallyRingedSpace.{u} ⟶
      specFunctor.{u} where
  app P := analytificationToSpec.{u} P.g
  naturality _ _ ψ := analytificationToSpec_naturality.{u} ψ

@[simp]
theorem analytificationToSpecNatTrans_app (P : Presentation.{u}) :
    analytificationToSpecNatTrans.{u}.app P = analytificationToSpec.{u} P.g :=
  rfl

/-! ### Naturality in the algebra -/

/-- A finitely generated `ℂ`-algebra, read as a commutative ring; opposite, because
`ComplexAnalytic.toFGAlg` lands in an opposite category. -/
def toCommRingCatOp : (isFiniteType.{u}.FullSubcategory)ᵒᵖ ⥤ CommRingCat.{u}ᵒᵖ :=
  (isFiniteType.{u}.ι ⋙ forget₂ (CommAlgCat.{u} ℂ) CommRingCat.{u}).op

/-- **`ComplexAnalytic.specFunctor` is `Spec` after `ComplexAnalytic.toFGAlg`**, definitionally:
the ring underlying the `ℂ`-algebra a presentation presents is the quotient it is defined to be,
and `ComplexAnalytic.PresHom.toAlgHom` is its own ring map.

This is what keeps `specFunctor` from being a second, unrelated functor to `LocallyRingedSpace`,
and it is what makes `ComplexAnalytic.analytificationFGAlgToSpec` a whiskering rather than a
transport. -/
theorem specFunctor_eq :
    toFGAlg.{u} ⋙ toCommRingCatOp.{u} ⋙ Spec.toLocallyRingedSpace.{u} = specFunctor.{u} :=
  rfl

/-- `ComplexAnalytic.specFunctor_eq` on morphisms. -/
theorem specFunctor_map {P Q : Presentation.{u}} (ψ : P ⟶ Q) :
    specFunctor.{u}.map ψ =
      (toCommRingCatOp.{u} ⋙ Spec.toLocallyRingedSpace.{u}).map (toFGAlg.{u}.map ψ) :=
  rfl

/-- **The comparison morphism `X^an ⟶ X` is natural in the finitely generated `ℂ`-algebra**, with
no presentation anywhere in the statement.

The presentation-level transformation whiskered by the inverse of the equivalence
`ComplexAnalytic.toFGAlg`, then the counit. This is the sense in which the analytification of an
affine `ℂ`-scheme of finite type comes with its comparison morphism as *structure*: the source is
`ComplexAnalytic.analytificationFGAlg`, whose statement mentions no tuple of polynomials, and the
target is `Spec` of the algebra itself. -/
def analytificationFGAlgToSpec :
    analytificationFGAlg.{u} ⋙ AnalyticSpace.forgetToLocallyRingedSpace.{u} ⟶
      toCommRingCatOp.{u} ⋙ Spec.toLocallyRingedSpace.{u} :=
  (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft toFGAlg.{u}.asEquivalence.inverse analytificationToSpecNatTrans.{u} ≫
      Functor.whiskerRight toFGAlg.{u}.asEquivalence.counitIso.hom
        (toCommRingCatOp.{u} ⋙ Spec.toLocallyRingedSpace.{u}) ≫
        (toCommRingCatOp.{u} ⋙ Spec.toLocallyRingedSpace.{u}).leftUnitor.hom

/-- **The component of `ComplexAnalytic.analytificationFGAlgToSpec` at an algebra**: the
comparison morphism of whichever presentation essential surjectivity chose, followed by `Spec` of
the counit that identifies the algebra it presents with the algebra itself.

Without this the transformation would be a definition nothing can be computed from — the same
obligation `ComplexAnalytic.analytificationFGAlgObjIso` discharges for
`ComplexAnalytic.analytificationFGAlg`. The two identities are dropped by hand rather than by
`simp` because the two spellings of the objects are definitionally but not syntactically equal,
and `Category.id_comp` has to be told which category it is in. -/
theorem analytificationFGAlgToSpec_app (X : (isFiniteType.{u}.FullSubcategory)ᵒᵖ) :
    analytificationFGAlgToSpec.{u}.app X =
      analytificationToSpec.{u} (toFGAlg.{u}.asEquivalence.inverse.obj X).g ≫
        (toCommRingCatOp.{u} ⋙ Spec.toLocallyRingedSpace.{u}).map
          (toFGAlg.{u}.asEquivalence.counitIso.hom.app X) := by
  simp only [analytificationFGAlgToSpec, analytificationToSpecNatTrans, Functor.id_obj,
    Functor.comp_map, Spec.toLocallyRingedSpace_map]
  refine (Category.id_comp (obj := LocallyRingedSpace.{u}) _).trans
    (congrArg (fun m ↦ analytificationToSpec.{u}
      (toFGAlg.{u}.asEquivalence.inverse.obj X).g ≫ m)
      (Category.comp_id (obj := LocallyRingedSpace.{u}) _))

/-- **The algebra-level comparison morphism, at a presentation one has.**

`ComplexAnalytic.analytificationFGAlgToSpec_app` computes the component in terms of the
presentation `Classical.choice` produced, which is the thing one cannot see past. This computes it
in terms of a presentation in hand, through the comparison isomorphism — the exact analogue of
what `ComplexAnalytic.analytificationFGAlgObjIso` does for
`ComplexAnalytic.analytificationFGAlg`, and required for the same reason: without it the
transformation is a definition nothing can be evaluated at.

It is a triangle identity of the equivalence. Naturality of
`ComplexAnalytic.analytificationToSpecNatTrans` at the inverse of the unit turns the right-hand
side into the component at the chosen presentation followed by `Spec` of the unit's inverse, and
`CategoryTheory.Equivalence.counit_app_functor` identifies that with the counit. -/
theorem analytificationFGAlgToSpec_app_toFGAlg_obj (P : Presentation.{u}) :
    analytificationFGAlgToSpec.{u}.app (toFGAlg.{u}.obj P) =
      AnalyticSpace.forgetToLocallyRingedSpace.{u}.map (analytificationFGAlgObjIso.{u} P).hom ≫
        analytificationToSpec.{u} P.g := by
  have hnat := analytificationToSpecNatTrans.{u}.naturality
    (toFGAlg.{u}.asEquivalence.unitIso.inv.app P)
  simp only [Functor.comp_map, Functor.id_obj, analytificationToSpecNatTrans_app] at hnat
  rw [analytificationFGAlgToSpec_app, analytificationFGAlgObjIso_hom]
  refine Eq.trans ?_ hnat.symm
  have hc : toFGAlg.{u}.asEquivalence.counitIso.hom.app (toFGAlg.{u}.obj P) =
      toFGAlg.{u}.map (toFGAlg.{u}.asEquivalence.unitIso.inv.app P) :=
    toFGAlg.{u}.asEquivalence.counit_app_functor P
  rw [specFunctor_map, hc]
  rfl

end ComplexAnalytic
