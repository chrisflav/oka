/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Mathlib.Geometry.RingedSpace.LocallyRingedSpace.HasColimits
import Mathlib.Topology.IsLocalHomeomorph
import Oka.Geometry.RingedSpace.PresheafedSpace.Gluing

/-!
# The coproduct of locally ringed spaces is covered by its inclusions, and is their disjoint union

Material for two Mathlib files and not one; see `README.md` on the mirror tree, which asks for the
split by destination.

**The cover goes to `Mathlib/Geometry/RingedSpace/PresheafedSpace/Gluing.lean`**, because it is
stated in terms of `AlgebraicGeometry.LocallyRingedSpace.OpenCover`, and Mathlib has no such
structure: this repository's is in `Oka/Geometry/RingedSpace/PresheafedSpace/Gluing.lean`, proposed
for the Mathlib file of that name, and that file is *not* in the closure of the one below.
`scripts/import_cost.py` prices it at **3** modules against that target
(`Mathlib.CategoryTheory.GlueData`, `Mathlib.Geometry.RingedSpace.PresheafedSpace.Gluing`,
`Mathlib.Topology.Gluing`), while the dependency in the other direction costs **0** — so upstream
the cover sits beside `OpenCover` and nothing pays anything. It is in this file rather than in the
gluing one only because that file is an import of this one.

**What decides is the statement**, which is `README.md`'s *split by destination, not by subject*:
a declaration travels with the cover exactly when its own statement mentions `OpenCover`, because
that is what the gluing import buys. As this file stands two do —
`AlgebraicGeometry.LocallyRingedSpace.sigmaOpenCover` and
`AlgebraicGeometry.LocallyRingedSpace.disjoint_opensRange_sigmaOpenCover`, which `## Main results`
below lists as two separate entries — and both go to the gluing file at that same **3**. The
disjointness is not *forced* there, and that is worth knowing before the split is read as a cost:
`AlgebraicGeometry.LocallyRingedSpace.disjoint_range_sigmaι` is the same fact stated with
`Set.range (Sigma.ι f i).base` and no `OpenCover` in it, and it goes to the cost-0 target with
everything else.

**Everything else goes to `Mathlib/Geometry/RingedSpace/LocallyRingedSpace/HasColimits.lean`, and
all of it but one declaration at cost 0**: it is this file's own import, and the `SheafedSpace`
results the proofs run through are already in its closure.

**The one exception is `AlgebraicGeometry.LocallyRingedSpace.isLocalHomeomorph_base_sigmaDesc`,
which costs that target 9.** It is the only statement here that names `IsLocalHomeomorph`, and
`scripts/import_cost.py --target Mathlib.Geometry.RingedSpace.LocallyRingedSpace.HasColimits
Mathlib.Topology.IsLocalHomeomorph` prices the edge at **9** on a closure of **1694** — the whole
of `Mathlib.Topology.OpenPartialHomeomorph.{Basic, Composition, Continuity, Defs, IsImage}`,
`Mathlib.Topology.PartialHomeomorph.Defs`, `Mathlib.Logic.Equiv.PartialEquiv` and
`Mathlib.Topology.SeparatedMap`, plus the module itself. It is kept here rather than split out
because **it goes to the same destination as its four siblings**, which is what `README.md` asks
the split to be made on; 9 is the price that destination pays for it, and it is stated so that a
Mathlib reviewer who would rather not pay it can move one declaration knowing what it costs.

Mathlib builds the coproduct of locally ringed spaces in that file and never says that the
inclusions are open immersions. It says it one level below, for `SheafedSpace` over a category
with strict terminal objects
(`AlgebraicGeometry.SheafedSpace.IsOpenImmersion.sigma_ι_isOpenImmersion`), and one level above,
for `AlgebraicGeometry.Scheme` — where `Mathlib/AlgebraicGeometry/Limits.lean` has the whole
sigma API: `AlgebraicGeometry.sigmaOpenCover`, `AlgebraicGeometry.sigmaι_eq_iff`,
`AlgebraicGeometry.disjoint_opensRange_sigmaι`, `AlgebraicGeometry.sigmaMk`. Only the middle level
is missing, and

    example (i : Discrete ι) : LocallyRingedSpace.IsOpenImmersion (colimit.ι F i) := by
      infer_instance

fails to synthesise. Everything here is the transport across
`AlgebraicGeometry.LocallyRingedSpace.forgetToSheafedSpace`, which preserves these colimits.

## Main results

- `AlgebraicGeometry.LocallyRingedSpace.sigma_ι_isOpenImmersion`: **the inclusion of a member of
  a coproduct is an open immersion.**
- `AlgebraicGeometry.LocallyRingedSpace.exists_colimit_ι_base_eq`: **every point of a coproduct
  is in the image of some inclusion.**
- `AlgebraicGeometry.LocallyRingedSpace.sigmaOpenCover`: the two together, as an
  `AlgebraicGeometry.LocallyRingedSpace.OpenCover`.
- `AlgebraicGeometry.LocallyRingedSpace.disjoint_opensRange_sigmaOpenCover`: **the images of two
  distinct members are disjoint**, so the index of a point of the coproduct is unique.
- `AlgebraicGeometry.LocallyRingedSpace.sigmaι_base_eq_iff`: the two together — two points of the
  members have the same image exactly when they are the same point of the same member.
- `AlgebraicGeometry.LocallyRingedSpace.image_base_sigmaDesc`: **the image of a set under a
  descent map is the union of the images of its traces on the members**, which is the shape every
  statement in the section below is proved from.
- `AlgebraicGeometry.LocallyRingedSpace.isClosedMap_base_sigmaDesc`: **a descent map out of a
  coproduct of finitely many members is closed as soon as each of them is.** Finiteness of the
  index is used exactly once, to make the union above a finite one.
- `AlgebraicGeometry.LocallyRingedSpace.isSeparatedMap_base_sigmaDesc`: **a descent map out of a
  coproduct is separated as soon as each of its restrictions is**, for any index type — two points
  of one member are separated by that member's hypothesis, and two points of different members by
  the ranges of their inclusions.
- `AlgebraicGeometry.LocallyRingedSpace.fiberSigmaDescEquiv`: **the fibre of a descent map is the
  disjoint union of the fibres of the pieces**, as an equivalence rather than as a cardinality —
  so that both finiteness and the count follow from one object.
- `AlgebraicGeometry.LocallyRingedSpace.isLocalHomeomorph_base_sigmaDesc` and
  `AlgebraicGeometry.LocallyRingedSpace.isIso_stalkMap_sigmaDesc`: **a descent map is a local
  homeomorphism, and an isomorphism on stalks, as soon as each of its restrictions is.** Neither
  needs the index type finite.
- `AlgebraicGeometry.LocallyRingedSpace.sigmaEquivSigma`: **the points of a coproduct are the
  pairs (index, point of that member)**, as an equivalence of types.
- `AlgebraicGeometry.LocallyRingedSpace.sigmaHomeoSigma`: **and that equivalence is a
  homeomorphism** — the space underlying a coproduct is the topological disjoint union of the
  spaces underlying its members. `AlgebraicGeometry.LocallyRingedSpace.sigmaHomeoSigma_symm_apply`
  and `AlgebraicGeometry.LocallyRingedSpace.sigmaHomeoSigma_sigmaι_base` say it is the
  identification made by the inclusions and not some other bijection.

## How the index of a point is recovered, and the route this file does not take

The disjointness is the half that looks hard, and it is hard along the obvious route. Mathlib's
`AlgebraicGeometry.SheafedSpace.IsOpenImmersion.image_preimage_is_empty` gets it one level down by
pushing a point through `CategoryTheory.preservesColimitIso`, then
`CategoryTheory.Limits.HasColimit.isoOfNatIso` at `CategoryTheory.Discrete.natIsoFunctor`, then
`TopCat.sigmaIsoSigma`, landing in a `Sigma` type where the index is a projection. Transporting
that here **does not go through by `rw` or by `simp`**: the middle step is blocked on
`(F ⋙ G).obj k` against `G.obj (F.obj k)`, which is definitional and not syntactic, and `simp`
unfolds the composite functor's action into `CategoryTheory.InducedCategory.homMk` before the
rewrite can fire. Mathlib runs that chain under
`set_option backward.isDefEq.respectTransparency false`, and no such `set_option` appears here.

**It is not needed, because that route computes more than the statement does.**
`TopCat.sigmaIsoSigma` identifies the whole coproduct space with a `Sigma` type; disjointness
needs only that the index of a point is well defined, and a *map* to the index type suffices for
that — it never has to be a homeomorphism. So `AlgebraicGeometry.LocallyRingedSpace.indexCocone`
gives the index type the discrete topology and descends the constant-index maps through the
universal property, and `AlgebraicGeometry.LocallyRingedSpace.eq_of_colimit_ι_base_eq` reads two
of its factorisations against each other. Nothing is inverted, so nothing has to be rewritten
across `CategoryTheory.Discrete.natIsoFunctor`.

## What is not here

**Nothing about a descent map being *injective*, *surjective* or an open map**, and no statement
that it is an isomorphism when the pieces are. The section below has exactly the four properties a
finite étale morphism is built from, because those are what has a consumer; each of the missing
ones is a separate small argument from
`AlgebraicGeometry.LocallyRingedSpace.fiberSigmaDescEquiv` or from the cover.

**This section read *No analogue of `AlgebraicGeometry.sigmaMk`: the index map built below is not
shown to be part of a homeomorphism onto a `Sigma` type, only to exist* until 2026-09-20**, when
`AlgebraicGeometry.LocallyRingedSpace.sigmaHomeoSigma` was added; taxis #2091 is what asked for it,
and the whole of what asked was a statement one level up about the connected components of a cover.
**That sentence went on to say the statement *would need exactly the `TopCat.sigmaIsoSigma` chain
described above*, and that half was wrong**: the homeomorphism below is built from
`AlgebraicGeometry.LocallyRingedSpace.sigmaι_base_eq_iff`,
`AlgebraicGeometry.LocallyRingedSpace.exists_sigma_ι_base_eq` and the open-embedding half of
`AlgebraicGeometry.LocallyRingedSpace.sigmaι_isOpenImmersion` — this file's own three statements,
the same three the index map is built from — and inverts nothing. **What the paragraph *How the
index of a point is recovered* says about that chain is unaffected and was re-run**: with the
composite spelled out, `rw [ι_preservesColimitIso_hom_assoc]` still reports *did not find an
occurrence of the pattern* against a goal that displays as that pattern, which is the
definitional-versus-syntactic seam it describes.

## Implementation notes

The index type is taken in `Type u` throughout rather than in a general universe with `Small`,
because `AlgebraicGeometry.LocallyRingedSpace.OpenCover.J` is a `Type u` and the cover is the
point of the file. The two lemmas are stated for a `CategoryTheory.Limits.colimit` of a functor
out of `CategoryTheory.Discrete`, which is what the `SheafedSpace` results are stated for, and the
cover is built for a family, which is the shape `Mathlib/AlgebraicGeometry/Limits.lean` states
its `AlgebraicGeometry.Scheme` version in, and what a consumer has.

Two seams, both recorded because neither is visible from the statements.

**The composition instance has to be handed over positionally.** After rewriting the goal along
`CategoryTheory.ι_preservesColimitIso_inv`, the `colimit.ι` appearing in it carries a
different `CategoryTheory.Limits.HasColimit` instance path from the one a freshly elaborated
`inferInstance` produces. The two terms are definitionally equal and not syntactically equal, and
instance synthesis is syntactic — so `AlgebraicGeometry.SheafedSpace.IsOpenImmersion.comp` is not
found even with the first factor's instance in context, and is supplied with `@`.

**`AlgebraicGeometry.SheafedSpace` is itself an induced category.** A `SheafedSpace` morphism
needs one `CategoryTheory.InducedCategory.Hom.hom` more than a `LocallyRingedSpace` one before
its `base` can be projected, so the underlying map of the comparison isomorphism is `.hom.hom.base`
where the underlying map of `colimit.ι` at this level is `.base`.

**Those `AlgebraicGeometry` names are in the root namespace, not under
`AlgebraicGeometry.Scheme`.** This file's docstring previously said the sigma API could not be
named here because the repository does not import `Mathlib/AlgebraicGeometry/Limits.lean`. That
is false — it is in the `Oka` closure and `scripts/check_docstring_names.py` resolves all four
names above. What had failed was the spelling: those declarations were being cited under
`AlgebraicGeometry.Scheme`, where none of them lives. The name cannot be repeated here to show
what was wrong with it, because a name that resolves to nothing is what the checker rejects.

**The composite forgetful functor is not found by `infer_instance` at its own spelling, and the
reason is not that the instance is missing.**
`AlgebraicGeometry.LocallyRingedSpace.forgetToTop` is *by definition*
`AlgebraicGeometry.LocallyRingedSpace.forgetToSheafedSpace` followed by
`AlgebraicGeometry.SheafedSpace.forget`; both factors preserve these colimits, and
`CategoryTheory.Limits.comp_preservesColimitsOfShape` covers the composite and **is** an instance.
What blocks it is that `forgetToTop` is a `def` rather than an `abbrev`, so at the reducible
transparency instance search runs at the goal is never seen as a composite and that instance is
never tried. Two controls settle it, both against
`Mathlib.Geometry.RingedSpace.LocallyRingedSpace.HasColimits` alone: `inferInstanceAs` at the
spelled-out composite succeeds where bare `infer_instance` fails, and an `abbrev` whose body is
the same composite is found by bare `infer_instance`. Handing the instance over is one line, and
is the move `Mathlib/AlgebraicGeometry/Limits.lean` makes for the `AlgebraicGeometry.Scheme`
version, there by `inferInstanceAs` at the unfolded type.
-/

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.LocallyRingedSpace

universe u

variable {ι : Type u} (F : Discrete ι ⥤ LocallyRingedSpace.{u})

/-- **The inclusion of a member of a coproduct of locally ringed spaces is an open immersion.**

`AlgebraicGeometry.SheafedSpace.IsOpenImmersion.sigma_ι_isOpenImmersion` transported along
`AlgebraicGeometry.LocallyRingedSpace.forgetToSheafedSpace`, which preserves coproducts. -/
instance sigma_ι_isOpenImmersion (i : Discrete ι) :
    LocallyRingedSpace.IsOpenImmersion (colimit.ι F i) := by
  have h := ι_preservesColimitIso_inv forgetToSheafedSpace.{u} F i
  change SheafedSpace.IsOpenImmersion (forgetToSheafedSpace.map (colimit.ι F i))
  rw [← h]
  have h1 : SheafedSpace.IsOpenImmersion (colimit.ι (F ⋙ forgetToSheafedSpace.{u}) i) :=
    inferInstance
  exact @SheafedSpace.IsOpenImmersion.comp _ _ _ _ _ _ _ h1 _

/-- **Every point of a coproduct of locally ringed spaces is in the image of some inclusion.**

`AlgebraicGeometry.SheafedSpace.colimit_exists_rep` for the coproduct of the underlying sheafed
spaces, moved across the comparison isomorphism — which is an isomorphism, hence injective on
points, which is what turns a representative there into one here. -/
theorem exists_colimit_ι_base_eq (x : (colimit F : LocallyRingedSpace.{u})) :
    ∃ (i : Discrete ι) (y : F.obj i), (colimit.ι F i).base y = x := by
  set e := preservesColimitIso forgetToSheafedSpace.{u} F with he
  obtain ⟨i, y, hy⟩ := SheafedSpace.colimit_exists_rep (F ⋙ forgetToSheafedSpace.{u})
    (e.hom.hom.base x)
  refine ⟨i, y, ?_⟩
  have hcomp := ι_preservesColimitIso_hom forgetToSheafedSpace.{u} F i
  have key : e.hom.hom.base ((colimit.ι F i).base y) = e.hom.hom.base x := by
    rw [← hy, ← hcomp]
    rfl
  have : IsIso ((SheafedSpace.forget CommRingCat.{u}).map e.hom) := inferInstance
  exact (TopCat.homeoOfIso (asIso ((SheafedSpace.forget CommRingCat.{u}).map e.hom))).injective key

variable (f : ι → LocallyRingedSpace.{u})

/-- **The inclusion of a member of a coproduct is an open immersion**, for a family rather than
for a functor out of `CategoryTheory.Discrete`.

Stated separately because instance search does not see through
`CategoryTheory.Limits.Sigma.ι` to `CategoryTheory.Limits.colimit.ι`, so the cover below cannot
find its `isOpen` field from the functor-indexed instance. -/
instance sigmaι_isOpenImmersion (i : ι) :
    LocallyRingedSpace.IsOpenImmersion (Sigma.ι f i) :=
  sigma_ι_isOpenImmersion (Discrete.functor f) ⟨i⟩

/-- **Every point of a coproduct of locally ringed spaces is in the image of some inclusion**, for
a family rather than for a functor out of `CategoryTheory.Discrete`. -/
theorem exists_sigma_ι_base_eq (x : (∐ f : LocallyRingedSpace.{u})) :
    ∃ (i : ι) (y : f i), (Sigma.ι f i).base y = x := by
  obtain ⟨i, y, hy⟩ := exists_colimit_ι_base_eq (Discrete.functor f) x
  exact ⟨i.as, y, hy⟩

/-- **The members of a coproduct of locally ringed spaces are an open cover of it.**

The analogue of `AlgebraicGeometry.sigmaOpenCover`, in `Mathlib/AlgebraicGeometry/Limits.lean`.
The index of a point is chosen by `Exists.choose` from
`AlgebraicGeometry.LocallyRingedSpace.exists_sigma_ι_base_eq`. That choice is in fact forced,
because the members are disjoint — `AlgebraicGeometry.LocallyRingedSpace.disjoint_range_sigmaι`,
in the section below — but nothing in this definition depends on it. -/
noncomputable def sigmaOpenCover : (∐ f : LocallyRingedSpace.{u}).OpenCover where
  J := ι
  obj := f
  map := Sigma.ι f
  idx x := (exists_sigma_ι_base_eq f x).choose
  covers x := (exists_sigma_ι_base_eq f x).choose_spec

/-! ### The index of a point is unique

The members of a coproduct do not overlap, so the index that
`AlgebraicGeometry.LocallyRingedSpace.OpenCover.idx` chooses above is in fact forced. The proof is
the one described in the header: descend a map to the index type, do not build an isomorphism
with a `Sigma` type. -/

/-- **The underlying space of a coproduct of locally ringed spaces is the coproduct of the
underlying spaces**, in the only form used below: that
`AlgebraicGeometry.LocallyRingedSpace.forgetToTop` preserves these colimits.

Both factors of it do, and `CategoryTheory.Limits.comp_preservesColimitsOfShape` is an instance
that covers the composite — but `AlgebraicGeometry.LocallyRingedSpace.forgetToTop` is a `def`, so
the goal does not present as a composite at reducible transparency and that instance is never
tried. Hence the explicit term rather than `inferInstance`; see the implementation notes in the
header. -/
noncomputable instance preservesColimitsOfShape_discrete_forgetToTop :
    PreservesColimitsOfShape (Discrete ι) forgetToTop.{u} :=
  Limits.comp_preservesColimitsOfShape _ _

/-- **The cocone that remembers which member a point came from**: the index type carried by the
*discrete* topology, with the `i`-th member mapping to the constant `i`.

This is the whole of the disjointness argument. A cocone under `F ⋙ forgetToTop` factors uniquely
through the coproduct, so the factorisation is a continuous map assigning an index to every point
of the coproduct, and two members whose images met would force their indices equal.

**Nothing below uses discreteness, and the topology is not forced.** A constant map is continuous
into any space, so `continuous_const` discharges the whole obligation whatever topology `ι`
carries, and the argument reads off an equality of *points* of `ι` and never names an open set of
it: substituting `⊤` for `⊥` here leaves
`AlgebraicGeometry.LocallyRingedSpace.eq_of_colimit_ι_base_eq` and the disjointness below it
compiling word for word, and `⊤` is provably not discrete. `⊥` is chosen because it is the
canonical topology on an index type. Note also that "every map into it is continuous" is the
property of the *indiscrete* topology, not of this one — into a discrete codomain continuity is
local constancy, which is a real condition. What *is* forced is that some topology be supplied,
and that it be supplied by `letI` rather than by a `TopologicalSpace` instance, because
`TopCat.ofHom` resolves the codomain's instance by search and would not see through a definition
that fixed it. -/
noncomputable def indexCocone : Cocone (F ⋙ forgetToTop.{u}) :=
  letI : TopologicalSpace ι := ⊥
  { pt := TopCat.of ι
    ι := Discrete.natTrans fun i ↦ TopCat.ofHom ⟨fun _ ↦ i.as, continuous_const⟩ }

/-- **Two members of a coproduct whose images meet are the same member.**

The two factorisations of `AlgebraicGeometry.LocallyRingedSpace.indexCocone` through the colimit,
read against each other at the two points: each says that the descended map takes the value of the
index there, and the hypothesis says the two points have the same image. -/
theorem eq_of_colimit_ι_base_eq {i j : Discrete ι} {x : F.obj i} {y : F.obj j}
    (h : (colimit.ι F i).base x = (colimit.ι F j).base y) : i = j := by
  have hc := isColimitOfPreserves forgetToTop.{u} (colimit.isColimit F)
  have hi := ConcreteCategory.congr_hom (hc.fac (indexCocone F) i) x
  have hj := ConcreteCategory.congr_hom (hc.fac (indexCocone F) j) y
  simp only [Functor.mapCocone_ι_app, ConcreteCategory.comp_apply] at hi hj
  exact Discrete.ext (hi.symm.trans
    ((congrArg (ConcreteCategory.hom (hc.desc (indexCocone F))) h).trans hj))

/-- **Two members of a coproduct whose images meet are the same member**, for a family rather than
for a functor out of `CategoryTheory.Discrete`. -/
theorem eq_of_sigmaι_base_eq {i j : ι} {x : f i} {y : f j}
    (h : (Sigma.ι f i).base x = (Sigma.ι f j).base y) : i = j :=
  congrArg Discrete.as (eq_of_colimit_ι_base_eq (Discrete.functor f) h)

/-- **The inclusion of a member of a coproduct is injective on points**, which is its being an
open immersion and hence an open embedding. -/
theorem sigmaι_base_injective (i : ι) : Function.Injective (Sigma.ι f i).base :=
  (sigmaι_isOpenImmersion f i).base_open.injective

/-- **Two points of the members of a coproduct have the same image exactly when they are the same
point of the same member.**

The analogue of `AlgebraicGeometry.sigmaι_eq_iff`, in `Mathlib/AlgebraicGeometry/Limits.lean` —
whose proof is no guide, running as it does through a locally directed cover, which does not
exist at this level. Here the two directions are the two lemmas above:
`AlgebraicGeometry.LocallyRingedSpace.eq_of_sigmaι_base_eq` for the index and
`AlgebraicGeometry.LocallyRingedSpace.sigmaι_base_injective` for the point. -/
theorem sigmaι_base_eq_iff (i j : ι) (x : f i) (y : f j) :
    (Sigma.ι f i).base x = (Sigma.ι f j).base y ↔
      (Sigma.mk i x : (i : ι) × (f i).toTopCat) = Sigma.mk j y := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain rfl := eq_of_sigmaι_base_eq f h
    exact congrArg _ (sigmaι_base_injective f i h)
  · rintro ⟨⟩
    rfl

/-- **The images of two distinct members of a coproduct are disjoint.** -/
theorem disjoint_range_sigmaι {i j : ι} (h : i ≠ j) :
    Disjoint (Set.range (Sigma.ι f i).base) (Set.range (Sigma.ι f j).base) := by
  rw [Set.disjoint_left]
  rintro _ ⟨x, rfl⟩ ⟨y, hy⟩
  exact h (eq_of_sigmaι_base_eq f hy).symm

/-- **Two distinct members of the open cover of a coproduct have disjoint images**, as open
subsets of the coproduct.

The analogue of `AlgebraicGeometry.disjoint_opensRange_sigmaι`, and the form a gluing argument
consumes: `Disjoint` unfolds by `disjoint_iff` to the meet being `⊥`, which is what makes a
compatibility hypothesis on the pairwise intersections of the members vacuous for `i ≠ j`. -/
theorem disjoint_opensRange_sigmaOpenCover {i j : ι} (h : i ≠ j) :
    Disjoint ((sigmaOpenCover f).opensRange i) ((sigmaOpenCover f).opensRange j) := by
  rw [disjoint_iff, ← SetLike.coe_set_eq, TopologicalSpace.Opens.coe_inf,
    TopologicalSpace.Opens.coe_bot, OpenCover.coe_opensRange, OpenCover.coe_opensRange]
  exact Set.disjoint_iff_inter_eq_empty.mp (disjoint_range_sigmaι f h)


/-! ### Descent maps out of a coproduct

`CategoryTheory.Limits.Sigma.desc` builds a morphism out of a coproduct from a morphism out of
each member. Everything below says that a property of the pieces passes to it, and every proof
runs through the same two facts: every point of the coproduct is in the image of exactly one
member (`AlgebraicGeometry.LocallyRingedSpace.exists_sigma_ι_base_eq` and
`AlgebraicGeometry.LocallyRingedSpace.eq_of_sigmaι_base_eq`), and the descent map agrees with the
`i`-th piece there.

**Only the closedness statement asks the index type to be finite**, and it is worth seeing where:
the image of a set is a union indexed by `ι`, and a union of closed sets is closed only when it is
finite. Nothing else here is a statement about all the members at once.
-/

variable {ι : Type u} (f : ι → LocallyRingedSpace.{u}) {Y : LocallyRingedSpace.{u}}
  (g : ∀ i, f i ⟶ Y)

/-- **A descent map agrees with the `i`-th piece on the image of the `i`-th member.**

`CategoryTheory.Limits.Sigma.ι_desc` read at a point. It is stated separately because every proof
below uses it and because the two sides are *not* definitionally equal — the colimit's universal
property is a theorem, not a computation — so `rfl` does not close it. -/
theorem base_sigmaι_sigmaDesc (i : ι) (x : f i) :
    (Sigma.desc g).base ((Sigma.ι f i).base x) = (g i).base x :=
  congrArg (fun m : f i ⟶ Y ↦ m.base x) (Sigma.ι_desc g i)

/-- **The image of a set under a descent map is the union of the images of its traces on the
members.**

Both inclusions are the two facts named in the section header: `⊆` needs that the point of the
coproduct came from some member, and `⊇` needs only that the descent map agrees with the piece
there. Disjointness of the members is *not* used — the statement is true for any cocone — and
that is why it is stated for `Set.iUnion` and not as a partition. -/
theorem image_base_sigmaDesc (C : Set (∐ f : LocallyRingedSpace.{u})) :
    (Sigma.desc g).base '' C = ⋃ i, (g i).base '' ((Sigma.ι f i).base ⁻¹' C) := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨i, y, rfl⟩ := exists_sigma_ι_base_eq f x
    exact Set.mem_iUnion.2 ⟨i, ⟨y, hx, (base_sigmaι_sigmaDesc f g i y).symm⟩⟩
  · intro hz
    obtain ⟨i, y, hy, rfl⟩ := Set.mem_iUnion.1 hz
    exact ⟨(Sigma.ι f i).base y, hy, base_sigmaι_sigmaDesc f g i y⟩

/-- **A descent map out of a coproduct of finitely many members is closed as soon as each of them
is.**

`AlgebraicGeometry.LocallyRingedSpace.image_base_sigmaDesc`, then `isClosed_iUnion_of_finite`.
The trace of a closed set on a member is closed because the inclusion is continuous — being an
open immersion is not needed for this one.

**`[Finite ι]` is used once and cannot be dropped**: a union of closed sets over an infinite index
need not be closed, and the coproduct of infinitely many copies of a point maps onto a point by a
map which is closed for a different reason. What fails without it is this proof, not necessarily
the statement. -/
theorem isClosedMap_base_sigmaDesc [Finite ι] (h : ∀ i, IsClosedMap (g i).base) :
    IsClosedMap (Sigma.desc g).base := by
  intro C hC
  rw [image_base_sigmaDesc]
  exact isClosed_iUnion_of_finite fun i ↦ h i _ (hC.preimage (Sigma.ι f i).base.hom.continuous)

/-- **A descent map out of a coproduct is separated as soon as each of its restrictions is.**

`IsSeparatedMap` asks that two *distinct* points with the same image be separated by opens, so the
proof is the case split on whether the two points come from the same member. Within one member the
member's own hypothesis separates them downstairs and the inclusion carries the separation up: it
is an open map and it is injective, which is what keeps the two images open and disjoint. Across
two members nothing has to be separated at all — the ranges of the two inclusions are already open
and already disjoint, and that is
`AlgebraicGeometry.LocallyRingedSpace.eq_of_sigmaι_base_eq`.

**The index type is not asked to be finite**, and neither point of the statement is about all the
members at once.

`IsSeparatedMap` is available here without a new import: `Mathlib/Topology/IsLocalHomeomorph.lean`,
which this file already imports, publicly imports `Mathlib/Topology/SeparatedMap.lean`. Upstreaming
this statement to `Mathlib/Geometry/RingedSpace/LocallyRingedSpace/HasColimits.lean` would cost
that file **one** module, measured with `scripts/import_cost.py`'s `--target` at that Mathlib
module and `Mathlib.Topology.SeparatedMap`. -/
theorem isSeparatedMap_base_sigmaDesc (h : ∀ i, IsSeparatedMap ⇑(g i).base) :
    IsSeparatedMap ⇑(Sigma.desc g).base := by
  intro x y hxy hne
  obtain ⟨i, a, rfl⟩ := exists_sigma_ι_base_eq f x
  obtain ⟨j, b, rfl⟩ := exists_sigma_ι_base_eq f y
  by_cases hij : i = j
  · subst hij
    have hab : (g i).base a = (g i).base b := by
      rw [← base_sigmaι_sigmaDesc f g i a, ← base_sigmaι_sigmaDesc f g i b]
      exact hxy
    obtain ⟨u, v, hu, hv, hau, hbv, huv⟩ := h i a b hab fun hab' ↦ hne (by rw [hab'])
    refine ⟨(Sigma.ι f i).base '' u, (Sigma.ι f i).base '' v,
      (sigmaι_isOpenImmersion f i).base_open.isOpenMap _ hu,
      (sigmaι_isOpenImmersion f i).base_open.isOpenMap _ hv,
      ⟨a, hau, rfl⟩, ⟨b, hbv, rfl⟩, ?_⟩
    rw [Set.disjoint_left]
    rintro _ ⟨p, hp, rfl⟩ ⟨q, hq, hqp⟩
    obtain rfl := sigmaι_base_injective f i hqp
    exact Set.disjoint_left.1 huv hp hq
  · refine ⟨Set.range ⇑(Sigma.ι f i).base, Set.range ⇑(Sigma.ι f j).base,
      (sigmaι_isOpenImmersion f i).base_open.isOpen_range,
      (sigmaι_isOpenImmersion f j).base_open.isOpen_range, ⟨a, rfl⟩, ⟨b, rfl⟩, ?_⟩
    rw [Set.disjoint_left]
    rintro _ ⟨p, rfl⟩ ⟨q, hq⟩
    exact hij (eq_of_sigmaι_base_eq f hq).symm

/-- **The fibre of a descent map is the disjoint union of the fibres of the pieces.**

Stated as an equivalence rather than as a statement about cardinalities, so that both finiteness
of the fibre and its size follow from one object; the map is `⟨i, x⟩ ↦ (Sigma.ι f i).base x` and
its bijectivity is the uniqueness of the index
(`AlgebraicGeometry.LocallyRingedSpace.eq_of_sigmaι_base_eq`) together with the injectivity of a
single inclusion (`AlgebraicGeometry.LocallyRingedSpace.sigmaι_base_injective`).

`noncomputable` only because `Equiv.ofBijective` is: the underlying map is explicit and the
inverse is not needed anywhere. -/
noncomputable def fiberSigmaDescEquiv (y : Y) :
    (Σ i : ι, ((g i).base ⁻¹' {y} : Set (f i))) ≃
      ((Sigma.desc g).base ⁻¹' {y} : Set (∐ f : LocallyRingedSpace.{u})) := by
  refine Equiv.ofBijective (fun p ↦ ⟨(Sigma.ι f p.1).base p.2.1, ?_⟩) ⟨?_, ?_⟩
  · change (Sigma.desc g).base _ ∈ ({y} : Set Y)
    rw [base_sigmaι_sigmaDesc]
    exact p.2.2
  · rintro ⟨i, x, hx⟩ ⟨j, z, hz⟩ hij
    simp only [Subtype.mk.injEq] at hij
    obtain rfl := eq_of_sigmaι_base_eq f hij
    obtain rfl := sigmaι_base_injective f i hij
    rfl
  · rintro ⟨x, hx⟩
    obtain ⟨i, z, rfl⟩ := exists_sigma_ι_base_eq f x
    refine ⟨⟨i, z, ?_⟩, rfl⟩
    change (g i).base z ∈ ({y} : Set Y)
    rw [← base_sigmaι_sigmaDesc f g i z]
    exact hx

/-- **A descent map is a local homeomorphism as soon as each of its restrictions is.**

`IsLocalHomeomorphOn.of_comp_right` at the `i`-th member: the composite with the inclusion *is*
the `i`-th piece, the inclusion is an open embedding and hence a local homeomorphism, so the
descent map is a local homeomorphism **on the image of the member** — and every point of the
coproduct is in one such image.

The index type is not asked to be finite, and `of_comp_right` is the direction that needs the
inclusion to be a local homeomorphism rather than the descent map: it concludes about `g` on
`f '' s` from the composite and from `f`, which is exactly the shape here. -/
theorem isLocalHomeomorph_base_sigmaDesc (h : ∀ i, IsLocalHomeomorph (g i).base) :
    IsLocalHomeomorph (Sigma.desc g).base := by
  intro x
  obtain ⟨i, z, rfl⟩ := exists_sigma_ι_base_eq f x
  have hcomp : IsLocalHomeomorphOn ((Sigma.desc g).base ∘ (Sigma.ι f i).base) Set.univ := by
    have he : (Sigma.desc g).base ∘ ((Sigma.ι f i).base : f i → (∐ f : LocallyRingedSpace.{u}))
        = (g i).base := funext fun y ↦ base_sigmaι_sigmaDesc f g i y
    rw [he]
    exact (h i).isLocalHomeomorphOn
  exact hcomp.of_comp_right
    (sigmaι_isOpenImmersion f i).base_open.isLocalHomeomorph.isLocalHomeomorphOn _
      ⟨z, trivial, rfl⟩

/-- **A descent map is an isomorphism on every stalk as soon as each of its restrictions is.**

`AlgebraicGeometry.LocallyRingedSpace.isIso_stalkMap_of_comp` at the factorisation
`Sigma.ι f i ≫ Sigma.desc g = g i`, whose other hypothesis — that the inclusion is an isomorphism
on stalks — is `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.stalk_iso` and is found by
instance search.

The point of the coproduct has to be exhibited as coming from a member before the factorisation
can be used, and that is the whole of the proof: the statement quantifies over points of `∐ f`,
where the hypothesis quantifies over points of the members. -/
theorem isIso_stalkMap_sigmaDesc (h : ∀ i (x : f i), IsIso ((g i).stalkMap x))
    (x : (∐ f : LocallyRingedSpace.{u})) : IsIso ((Sigma.desc g).stalkMap x) := by
  obtain ⟨i, z, rfl⟩ := exists_sigma_ι_base_eq f x
  exact isIso_stalkMap_of_comp (Sigma.ι f i) (Sigma.desc g) (g i) (Sigma.ι_desc g i) z (h i z)

/-! ### The coproduct's space is the disjoint union of the members' spaces

The index map of the section above says a point of `∐ f` has a well-defined index; this section
says the pair (index, point of that member) determines it and exhausts it, as a `Homeomorph`. It
is the conclusion the three statements above are the hypotheses of, and it is stated at the level
of spaces because that is the only level at which a `Sigma` type is available.
-/

/-- **The points of a coproduct of locally ringed spaces are the pairs (index, point of that
member)**, as an equivalence of types.

Injectivity is `AlgebraicGeometry.LocallyRingedSpace.sigmaι_base_eq_iff`, read as the statement
that the pair is recovered from the point, and surjectivity is
`AlgebraicGeometry.LocallyRingedSpace.exists_sigma_ι_base_eq`. **Neither half asks the index type
to be finite** and neither goes through `CategoryTheory.preservesColimitIso`. -/
noncomputable def sigmaEquivSigma :
    (Σ i, (f i : Type u)) ≃ ((∐ f : LocallyRingedSpace.{u}) : Type u) :=
  Equiv.ofBijective (fun p ↦ (Sigma.ι f p.1).base p.2)
    ⟨fun p q h ↦ by
        simpa [Sigma.ext_iff] using (sigmaι_base_eq_iff f p.1 q.1 p.2 q.2).mp h,
      fun x ↦ by
        obtain ⟨i, y, hy⟩ := exists_sigma_ι_base_eq f x
        exact ⟨⟨i, y⟩, hy⟩⟩

/-- **And that equivalence is a homeomorphism**: the space underlying a coproduct of locally
ringed spaces is the topological disjoint union of the spaces underlying its members.

The map out of the `Sigma` type is continuous because each inclusion is (`continuous_sigma`) and
open because each inclusion is an open embedding (`isOpenMap_sigma` at
`AlgebraicGeometry.LocallyRingedSpace.sigmaι_isOpenImmersion`), so
`Equiv.toHomeomorphOfContinuousOpen` upgrades
`AlgebraicGeometry.LocallyRingedSpace.sigmaEquivSigma` and this is its inverse. **The direction is
chosen so that the statement reads as an identification of `∐ f`**; it is the inverse that is
`rfl` on a pair, which is what
`AlgebraicGeometry.LocallyRingedSpace.sigmaHomeoSigma_symm_apply` records.

**This is `AlgebraicGeometry.sigmaMk`'s analogue at this level**, and the paragraph *How the index
of a point is recovered* above is why it is not built the way that one is: nothing here inverts
`TopCat.sigmaIsoSigma` or rewrites across `CategoryTheory.Discrete.natIsoFunctor`. -/
noncomputable def sigmaHomeoSigma :
    ((∐ f : LocallyRingedSpace.{u}) : Type u) ≃ₜ Σ i, (f i : Type u) :=
  ((sigmaEquivSigma f).toHomeomorphOfContinuousOpen
    (continuous_sigma fun i ↦ (Sigma.ι f i).base.hom.continuous)
    (isOpenMap_sigma.mpr fun i ↦ (sigmaι_isOpenImmersion f i).base_open.isOpenMap)).symm

/-- **The inverse sends a pair to the image of its second component under the inclusion**, by
`rfl`: it is `AlgebraicGeometry.LocallyRingedSpace.sigmaEquivSigma`'s own map. -/
@[simp]
theorem sigmaHomeoSigma_symm_apply (i : ι) (y : f i) :
    (sigmaHomeoSigma f).symm ⟨i, y⟩ = (Sigma.ι f i).base y := rfl

/-- **So the homeomorphism sends a point of a member to its own index and itself.**

This is the form a consumer uses: it says that the identification is the one made by the
inclusions and not some other bijection with the same source and target. -/
@[simp]
theorem sigmaHomeoSigma_sigmaι_base (i : ι) (y : f i) :
    sigmaHomeoSigma f ((Sigma.ι f i).base y) = ⟨i, y⟩ :=
  (sigmaHomeoSigma f).apply_eq_iff_eq_symm_apply.mpr rfl

end AlgebraicGeometry.LocallyRingedSpace
