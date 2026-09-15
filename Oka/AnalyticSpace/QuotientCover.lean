/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.AnalyticSpace.CoveringSpaceMap
import Oka.AnalyticSpace.SeparatedFiniteEtale
import Oka.Topology.Covering.Quotient

/-!
# The quotient of a cover by a finite group acting over the base

Let `X` be a complex analytic space, `f : Y ⟶ X` a finite étale morphism with `Y` Hausdorff, and
let a finite group `G` act on the topological space underlying `Y` by homeomorphisms **over `X`**.
Then the orbit space carries a complex analytic structure for which the descended map is finite
étale and separated, and the quotient map is a morphism of analytic spaces over `X`. At an object
of `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver` over a Hausdorff base, both
hypotheses on the total space are free and the quotient is again an object of that category, with
the quotient map a morphism of it.

## The analytic content is zero, and that is the whole design

Every step is a statement already in the tree, and this file is the composite:

1. **Down.** `ComplexAnalytic.AnalyticSpace.isCoveringMap_base_of_isFiniteEtale` turns `f` into a
   topological covering map. That is where `[T2Space Y]` is spent and the only place; it is
   Mathlib's hypothesis, used to separate the finitely many points of a fibre, and it is asked of
   the **source** and not of the base.
2. **Across.** `IsCoveringMap.of_comp_quotientMk` of `Oka/Topology/Covering/Quotient.lean` is the
   descent: the orbit space of a finite group acting continuously over the base is again a
   covering map, with `MulAction.finite_fiber_of_comp_quotientMk` for its fibres. **The action is
   not assumed free and nothing whatever is assumed of the base there.**
3. **Up.** `ComplexAnalytic.AnalyticSpace.isFiniteEtale_coveringSpaceHom` puts the analytic
   structure back on: a covering map with finite fibres into an analytic space is finite étale for
   it, with **no separation axiom of any kind**.
4. **Separated.** `IsCoveringMap.isSeparatedMap` is the second half of an object of
   `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver`, read at the same covering map and
   asking nothing at all.

**So the base carries no separation axiom in the first section of this file.** `[T2Space X]`
appears only in the section that packages the result into the category, where it is what supplies
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.t2Space_left` and so discharges step 1's
hypothesis on the total space.

## The descended map is constructed here, and the module it comes from says why it was not there

`Oka/Topology/Covering/Quotient.lean` takes the descended map as a variable together with
`∀ e, q (Quotient.mk _ e) = p e`, and its docstring gives the reason: any such `q` is
`Quotient.lift p` at the proof that `p` is constant on orbits, so nothing is lost and no
definition is introduced for a term `Quotient.lift` already names.
**An analytic structure has to be put on something**, so a term is what this file needs, and
`ComplexAnalytic.AnalyticSpace.orbitDesc` is exactly that `Quotient.lift`, with the constancy
supplied by the hypothesis that the action is over the base. Its defining equation
`ComplexAnalytic.AnalyticSpace.orbitDesc_apply` is `rfl`, which is what makes it an instance of
that module's hypothesis with no work.

## The action is on the topological space and not by automorphisms of the cover

The hypotheses are `MulAction G ↥Y`, `ContinuousConstSMul G ↥Y` and that each `g` commutes with
the structure map. **A group acting by automorphisms of the cover gives all three**, and that
implication is not made below — nothing here turns a `CategoryTheory.Aut` or a functor out of
`CategoryTheory.SingleObj` into an action on points, and nothing here is stated for such a group.
Taking the action topologically is what keeps every statement in this file free of the category
and is why step 2 above can be Mathlib-shaped; supplying the bridge is what the colimit statement
below is said not to be.

## Main definitions

- `ComplexAnalytic.AnalyticSpace.orbitSpace`, `ComplexAnalytic.AnalyticSpace.orbitMk` and
  `ComplexAnalytic.AnalyticSpace.orbitDesc`: the orbit space as an object of `TopCat`, the
  quotient map onto it, and the descent of the structure map along that quotient map.
- `ComplexAnalytic.AnalyticSpace.quotientCover` and
  `ComplexAnalytic.AnalyticSpace.quotientCoverHom`: the orbit space as a complex analytic space,
  and its structure morphism to `X`.
- `ComplexAnalytic.AnalyticSpace.toQuotientCover`: the quotient map as a morphism of analytic
  spaces.
- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.quotient` and
  `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.toQuotient`: both of those read at an
  object of the category of covers separated over a Hausdorff base.

## Main results

- `ComplexAnalytic.AnalyticSpace.isCoveringMap_orbitDesc`: **the descended map is a covering map**,
  and `ComplexAnalytic.AnalyticSpace.finite_fiber_orbitDesc` that its fibres are finite.
- `ComplexAnalytic.AnalyticSpace.isFiniteEtale_quotientCoverHom` and
  `ComplexAnalytic.AnalyticSpace.isSeparatedMap_quotientCoverHom`: **the structure morphism of the
  quotient is finite étale, and its base map is separated.**
- `ComplexAnalytic.AnalyticSpace.toQuotientCover_comp`: **the quotient map is a morphism over
  `X`**, and `ComplexAnalytic.AnalyticSpace.base_toQuotientCover` that its underlying map is the
  quotient map of the orbit space.

## What is not here

* **Not the `PreGaloisCategory` field of `Mathlib/CategoryTheory/Galois/Basic.lean`, and not
  a colimit of any shape.** Nothing
  below says that `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.toQuotient` is a colimit
  cocone, that a `G`-invariant morphism out of the cover factors through the quotient, or that
  such a factorisation is unique. **`CategoryTheory.SingleObj` occurs in the comment-stripped code
  of exactly one module of this repository at the commit that adds this file** —
  `Oka/CategoryTheory/Limits/Shapes/SingleObj.lean`, the mirror-tree module that reduces colimits
  of that shape to finite colimits, which is not about this category, which this file does not
  import and which nothing below cites. **The bare `SingleObj` is a second register and it returns
  two**: the other module is `Oka.lean`, the aggregator `mk_all` generates, whose only hit is its
  `import Oka.CategoryTheory.Limits.Shapes.SingleObj` line — a module path, which does not contain
  the token this bullet is measured at. `README.md` puts that difference in terms in its account of
  what a re-cut owes, *which spelling a token scan uses is part of the figure*, and the two
  spellings answer differently here; the count above is the qualified one, which is the spelling
  `Oka/AnalyticSpace/SeparatedFiberFunctor.lean` and `OkaTest/Axioms/Morphisms.lean` measure the
  same absence at, and it agrees with both.
* **No bridge from a group of automorphisms of the cover to the action taken here**, as the
  paragraph above says at length. A caller holding a homomorphism into
  `CategoryTheory.Aut` of an object has to build the three hypotheses itself, and no declaration
  below helps.
* **Nothing about freeness, fixed points or stabilisers**, and nothing about the degree of the
  quotient — not that it divides the degree of the cover, not that it is the number of orbits in a
  fibre. `Oka/AnalyticSpace/Degree.lean` is where such a statement would go and this file adds
  nothing to it.
* **Nothing about the quotient map `Y ⟶ Y⧸G` as a morphism in a class.** It is built, its
  underlying map is identified, and it is shown to be a morphism over `X`; it is not shown to be a
  local isomorphism, finite, finite étale, an epimorphism, or a quotient in any categorical sense.
* **Nothing about the orbit space as a topological space in its own right** — not Hausdorff, not
  locally compact, nothing about the quotient map being closed. The orbit space is Hausdorff here
  as a consequence of `ComplexAnalytic.AnalyticSpace.isSeparatedMap_quotientCoverHom` only over a
  Hausdorff base, and that consequence is not drawn below.
* **Nothing about `IsQuotientCoveringMap`**, the structure of Mathlib's
  `Mathlib/Topology/Covering/Quotient.lean`, which is about the other map and asks the action to
  be free. `Oka/Topology/Covering/Quotient.lean`'s docstring is where that comparison is made and
  it is not repeated here.
* **Not stated at `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver`.** The category-level
  declarations below are at the separated covers and at no other category; the general-purpose
  section above them asks for no category at all and is the form a caller at a different one
  should use.
-/

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry TopCat Topology

universe u

noncomputable section

namespace ComplexAnalytic.AnalyticSpace

section Orbits

variable {X Y : AnalyticSpace.{u}} (f : Y ⟶ X)
variable (G : Type*) [Group G] [MulAction G ↥Y] [ContinuousConstSMul G ↥Y]

/-- **The orbit space of the action, as an object of `TopCat`.**

`Quotient` at `MulAction.orbitRel` with the quotient topology, bundled. The structure map plays
no part in it and is not an argument; what the structure map is for is
`ComplexAnalytic.AnalyticSpace.orbitDesc` below. -/
def orbitSpace : TopCat.{u} := TopCat.of (Quotient (MulAction.orbitRel G ↥Y))

/-- **The quotient map onto the orbit space**, as a morphism of `TopCat`.

`Quotient.mk` with `continuous_quotient_mk'`, which is the quotient topology's own continuity and
not a fact about the action. -/
def orbitMk : Y.toLocallyRingedSpace.toTopCat ⟶ orbitSpace (Y := Y) G :=
  TopCat.ofHom ⟨Quotient.mk (MulAction.orbitRel G ↥Y), continuous_quotient_mk'⟩

variable {G}
variable (hover : ∀ (g : G) (y : ↥Y), f.toLRSHom.base (g • y) = f.toLRSHom.base y)

/-- **The descent of the structure map to the orbit space.**

`Quotient.lift` of the base map at the constancy on orbits that the hypothesis `hover` is, with
`continuous_quot_lift` for continuity. **This is the term
`Oka/Topology/Covering/Quotient.lean` declines to introduce** — that module takes the descended
map as a variable, on the ground that any such map is this one — and it is introduced here
because an analytic structure has to be put on a term. See the module docstring. -/
def orbitDesc : orbitSpace (Y := Y) G ⟶ X.toLocallyRingedSpace.toTopCat :=
  TopCat.ofHom ⟨Quotient.lift ⇑f.toLRSHom.base (by
      rintro a b ⟨g, rfl⟩
      exact hover g b),
    continuous_quot_lift _ f.toLRSHom.base.hom.continuous⟩

omit [ContinuousConstSMul G ↥Y] in
/-- **Its defining equation**, which is `rfl`: the descent of the structure map along the quotient
map is the structure map. This is the hypothesis `Oka/Topology/Covering/Quotient.lean` asks of a
descended map, so every statement of that module applies here with no work. -/
@[simp]
theorem orbitDesc_apply (y : ↥Y) :
    orbitDesc f hover (Quotient.mk (MulAction.orbitRel G ↥Y) y) = f.toLRSHom.base y :=
  rfl

omit [ContinuousConstSMul G ↥Y] in
/-- **The same equation as an equation of `TopCat` morphisms**, and it is `rfl` too. It is what
`ComplexAnalytic.AnalyticSpace.coveringSpaceMap` is fed to build the quotient morphism below. -/
theorem orbitMk_comp_orbitDesc :
    orbitMk (Y := Y) G ≫ orbitDesc f hover = f.toLRSHom.base := rfl

section Covering

variable [Finite G] [T2Space Y] [IsFiniteEtale f]

/-- **The descended map is a covering map.**

`IsCoveringMap.of_comp_quotientMk` of `Oka/Topology/Covering/Quotient.lean` at the covering map
`ComplexAnalytic.AnalyticSpace.isCoveringMap_base_of_isFiniteEtale` reads off `f`, with the
fibres of `f` finite because `ComplexAnalytic.AnalyticSpace.IsFinite.finite_fiber` is a field of
`ComplexAnalytic.AnalyticSpace.IsFiniteEtale`.

**`[T2Space Y]` is spent here and nowhere else below**, and it is spent on the first step and not
on the descent: the descent asks nothing of any space. **No hypothesis is placed on `X`.** -/
theorem isCoveringMap_orbitDesc : IsCoveringMap ⇑(orbitDesc f hover) :=
  IsCoveringMap.of_comp_quotientMk (p := ⇑f.toLRSHom.base) (fun _ => rfl)
    (isCoveringMap_base_of_isFiniteEtale f)
    (fun x => have := IsFinite.finite_fiber (f := f) x; Set.toFinite _)

omit [ContinuousConstSMul G ↥Y] [Finite G] [T2Space Y] in
/-- **And its fibres are finite.**

`MulAction.finite_fiber_of_comp_quotientMk`, whose fibre of the descent is the image of the fibre
of `f` under the quotient map. **The three `omit`s are the statement and not an economy**: this
uses no finiteness of the group, no continuity of the action and no separation axiom, exactly as
the module it comes from says of itself. -/
theorem finite_fiber_orbitDesc (x : ↥X) : (⇑(orbitDesc f hover) ⁻¹' {x}).Finite :=
  MulAction.finite_fiber_of_comp_quotientMk (p := ⇑f.toLRSHom.base) (fun _ => rfl)
    (fun x => have := IsFinite.finite_fiber (f := f) x; Set.toFinite _) x

/-- **The quotient of the cover, as a complex analytic space.**

`ComplexAnalytic.AnalyticSpace.coveringSpace` at the descended map, which is a local
homeomorphism because it is a covering map. The underlying topological space is the orbit space
on the nose and the structure sheaf is the inverse image of `X`'s along the descent; nothing is
glued, for the reason `Oka/AnalyticSpace/CoveringSpace.lean`'s docstring gives at length. -/
def quotientCover : AnalyticSpace.{u} :=
  coveringSpace X (orbitDesc f hover) (isCoveringMap_orbitDesc f hover).isLocalHomeomorph

/-- **Its structure morphism to the base**, which is
`ComplexAnalytic.AnalyticSpace.coveringSpaceHom` at the same map. -/
def quotientCoverHom : quotientCover f hover ⟶ X :=
  coveringSpaceHom X (orbitDesc f hover) (isCoveringMap_orbitDesc f hover).isLocalHomeomorph

/-- **Its underlying map is the descent**, by `rfl`. -/
@[simp]
theorem base_quotientCoverHom :
    (quotientCoverHom f hover).toLRSHom.base = orbitDesc f hover := rfl

/-- **The structure morphism of the quotient is finite étale.**

`ComplexAnalytic.AnalyticSpace.isFiniteEtale_coveringSpaceHom` at the covering map and the finite
fibres above. **That statement asks no separation axiom**, so the hypotheses of this one are the
hypotheses of `ComplexAnalytic.AnalyticSpace.isCoveringMap_orbitDesc` and nothing further.

A theorem rather than an instance, following the declaration it reads: a caller who wants it by
instance search supplies it by name, which is what the category-level definitions below do. -/
theorem isFiniteEtale_quotientCoverHom : IsFiniteEtale (quotientCoverHom f hover) :=
  isFiniteEtale_coveringSpaceHom X _ (isCoveringMap_orbitDesc f hover)
    (finite_fiber_orbitDesc f hover)

/-- **And its base map is a separated map.**

`IsCoveringMap.isSeparatedMap` at the same covering map — Mathlib's, asking nothing of either
space. This is the second half of what an object of
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver` carries, and the half that
`ComplexAnalytic.AnalyticSpace.not_isSeparatedMap_doubledLineOver` shows does not come free with
the first. -/
theorem isSeparatedMap_quotientCoverHom :
    _root_.IsSeparatedMap ⇑((quotientCoverHom f hover).toLRSHom.base) :=
  (isCoveringMap_orbitDesc f hover).isSeparatedMap

/-- **The quotient map, as a morphism of analytic spaces.**

`ComplexAnalytic.AnalyticSpace.toCoveringSpace` identifies `Y` with the covering space built on
its own base map — an isomorphism, by
`ComplexAnalytic.AnalyticSpace.isIso_toCoveringSpace` — and
`ComplexAnalytic.AnalyticSpace.coveringSpaceMap` carries the topological quotient map across the
triangle `ComplexAnalytic.AnalyticSpace.orbitMk_comp_orbitDesc`. **Nothing is glued and no sheaf
map is written down**: both structures are `X`'s pulled back, and the `ℂ`-linearity is the one
application of `ComplexAnalytic.IsCLinearHom.of_comp` that
`Oka/AnalyticSpace/CoveringSpaceMap.lean` makes. -/
def toQuotientCover : Y ⟶ quotientCover f hover :=
  toCoveringSpace f ≫
    coveringSpaceMap X (orbitDesc f hover) (isCoveringMap_orbitDesc f hover).isLocalHomeomorph
      f.toLRSHom.base IsLocalIso.isLocalHomeomorph (orbitMk G)
      (orbitMk_comp_orbitDesc f hover).symm

/-- **Its underlying map is the quotient map of the orbit space.**

The comparison morphism has identity base
(`ComplexAnalytic.AnalyticSpace.base_toCoveringSpace`) and
`ComplexAnalytic.AnalyticSpace.coveringSpaceMap` has base the map it was built from, so the
composite has base that map. -/
@[simp]
theorem base_toQuotientCover : (toQuotientCover f hover).toLRSHom.base = orbitMk G := by
  change (toCoveringSpace f).toLRSHom.base ≫ _ = _
  rw [base_toCoveringSpace, base_coveringSpaceMap]
  exact Category.id_comp _

/-- **And it is a morphism over `X`.**

The two triangles of the two factors, composed:
`ComplexAnalytic.AnalyticSpace.coveringSpaceMap_comp` and then
`ComplexAnalytic.AnalyticSpace.toCoveringSpace_comp`. -/
theorem toQuotientCover_comp : toQuotientCover f hover ≫ quotientCoverHom f hover = f :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun m ↦ toCoveringSpace f ≫ m)
        (coveringSpaceMap_comp X (orbitDesc f hover)
          (isCoveringMap_orbitDesc f hover).isLocalHomeomorph f.toLRSHom.base
          IsLocalIso.isLocalHomeomorph (orbitMk G)
          (orbitMk_comp_orbitDesc f hover).symm)).trans (toCoveringSpace_comp f))

end Covering

end Orbits

section Category

variable {X : AnalyticSpace.{u}} [T2Space (X : Type u)] (A : SeparatedFiniteEtaleOver.{u} X)
variable {G : Type*} [Group G] [Finite G] [MulAction G ↥A.left] [ContinuousConstSMul G ↥A.left]
variable (hover : ∀ (g : G) (y : ↥A.left), A.hom.toLRSHom.base (g • y) = A.hom.toLRSHom.base y)

/-- **The quotient of a cover separated over a Hausdorff base by a finite group acting over that
base is again one.**

The pair an object of this category carries is
`ComplexAnalytic.AnalyticSpace.isFiniteEtale_quotientCoverHom` and
`ComplexAnalytic.AnalyticSpace.isSeparatedMap_quotientCoverHom`, and both hypotheses of the
section above are discharged here rather than asked for: the total space is Hausdorff by
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.t2Space_left`, which is what `[T2Space X]`
buys, and the structure morphism is finite étale because the object says so.

**The three instances are passed positionally with `@` and that is not decoration.** The object
of this comma category spells its total space as `(𝟭 _).obj A.left` and its base as
`(Functor.fromPUnit X).obj A.right`, neither reducibly the thing it is, so a hypothesis introduced
by `haveI` at the spelling `A.left ⟶ X` is not found by instance search at the spelling the
elaborated application asks for. `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.sigma` records
the same seam and is cured the same way. -/
def SeparatedFiniteEtaleOver.quotient : SeparatedFiniteEtaleOver.{u} X :=
  MorphismProperty.Over.mk _
    (@quotientCoverHom X A.left A.hom G _ _ _ hover _ _ A.isFiniteEtale_hom)
    ⟨@isFiniteEtale_quotientCoverHom X A.left A.hom G _ _ _ hover _ _ A.isFiniteEtale_hom,
      @isSeparatedMap_quotientCoverHom X A.left A.hom G _ _ _ hover _ _ A.isFiniteEtale_hom⟩

/-- **The quotient map, as a morphism of that category.**

`ComplexAnalytic.AnalyticSpace.toQuotientCover` with its triangle over `X`, which is the whole of
what a morphism of this category is: the property on morphisms is `⊤` on both sides, so nothing
is asked of the underlying morphism beyond commuting. -/
def SeparatedFiniteEtaleOver.toQuotient : A ⟶ A.quotient hover :=
  MorphismProperty.Over.homMk
    (@toQuotientCover X A.left A.hom G _ _ _ hover _ _ A.isFiniteEtale_hom)
    (@toQuotientCover_comp X A.left A.hom G _ _ _ hover _ _ A.isFiniteEtale_hom)

end Category

end ComplexAnalytic.AnalyticSpace
