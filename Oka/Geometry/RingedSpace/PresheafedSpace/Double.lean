/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Mathlib.Topology.IsLocalHomeomorph
import Oka.CategoryTheory.GlueData
import Oka.Geometry.RingedSpace.PresheafedSpace.Gluing

/-!
# Two copies of a locally ringed space glued along an open subspace

Given a locally ringed space `X` and an open `V ⊆ X`, this file glues two copies of `X` along
`V` and reads off the result: `AlgebraicGeometry.LocallyRingedSpace.double X V`, the two
inclusions, the fold map back to `X`, and when the double fails to be Hausdorff. At `X = ℂ` and
`V = ℂ ∖ {0}` it is the *line with two origins*, and the complex analytic development this mirror
file serves is what wanted it. Nothing below mentions that development, and the reason these
results are here rather than there is that none of them mentions an analytic structure.

## Why the glue datum costs nothing, and it is a fact about the index type

`CategoryTheory.GlueData'` asks for `t'` and `cocycle` **only at triples `i, j, k` that are
pairwise distinct**. The index type here is `ULift Bool`, which has no such triple, so all three
of `t'`, `t_fac` and `cocycle` are discharged by `False.elim` and the datum is nine lines. That is
the whole reason this construction is short: building the same object as a
`CategoryTheory.GlueData` directly would ask for `t'` at every triple, and the two `pullback`s it
lands between are the objects `AlgebraicGeometry.LocallyRingedSpace.restrictInfIsoPullback`
exists to get rid of.

**The price is paid at the diagonal instead**, and it is paid once.
`CategoryTheory.GlueData.ofGlueData'` fills `V (i, i)` with a `dite`, so the overlap, the
inclusion and the transition of the resulting datum are all `dite`s off which an `eqToHom` has to
be peeled. `Oka/CategoryTheory/GlueData.lean` is where that peeling lives, and
`AlgebraicGeometry.LocallyRingedSpace.doubleGlueData_f_of_ne` and
`…doubleGlueData_t_comp_f_of_ne` are its two instances here — after them nothing below mentions a
`dite`.

## What the two points over a point of `X ∖ V` cost

`AlgebraicGeometry.LocallyRingedSpace.doubleGlueData_ι_base_eq_iff` is the whole topological
content: `ι i x = ι j y` exactly when `x = y` and either `i = j` or `x ∈ V`. Off the diagonal it
is `AlgebraicGeometry.LocallyRingedSpace.GlueData.ι_eq_iff` with the two `eqToHom`s peeled; on
the diagonal it is injectivity of an open immersion, which is a shorter proof than unfolding the
relation at `V (i, i)` would be.

Everything else about the underlying space follows from it and from
`AlgebraicGeometry.LocallyRingedSpace.GlueData.ι_jointly_surjective`: the fold is a closed map
because the image of a set is the union of its two preimages, its fibres have at most two points,
and it is a local homeomorphism because each copy of `X` is an open set on which it inverts the
inclusion.

## Placement

This file is mirror-tree material for `Mathlib/Geometry/RingedSpace/PresheafedSpace/`: every
declaration is in `AlgebraicGeometry.LocallyRingedSpace`, nothing here mentions complex analysis,
and the statements would make sense to a reader who had never heard of Oka's theorem.

**Upstream it would go into `Mathlib/Geometry/RingedSpace/PresheafedSpace/Gluing.lean` or into a
new file beside it, and this file's imports argue for the second.**
`python3 scripts/import_cost.py --target Mathlib.Geometry.RingedSpace.PresheafedSpace.Gluing
Mathlib.CategoryTheory.GlueData Mathlib.Topology.IsLocalHomeomorph` reports **cost 9**: the
category-theory module is already in that target's closure of 1697 and
`Mathlib/Topology/IsLocalHomeomorph.lean` is not, bringing nine modules with it —
`Mathlib.Logic.Equiv.PartialEquiv`, `Mathlib.Topology.SeparatedMap`, the five under
`Mathlib/Topology/OpenPartialHomeomorph/` (`Basic`, `Composition`, `Continuity`, `Defs`,
`IsImage`), `Mathlib.Topology.PartialHomeomorph.Defs` and `Mathlib.Topology.IsLocalHomeomorph`
itself. That is what
`AlgebraicGeometry.LocallyRingedSpace.isLocalHomeomorph_base_doubleFold` costs, and it is a real
argument for keeping the construction out of the API file rather than a bookkeeping figure.

The same split is what this repository wants for a second reason: this file needs
`Oka/CategoryTheory/GlueData.lean`, which `Oka/Geometry/RingedSpace/PresheafedSpace/Gluing.lean`
neither imports nor reaches — that file's `Oka`-internal import closure has four modules and this
is not one of them — so putting the material there would put it into the import closure of the
**167** repository modules downstream of that file (measured at `d2ae161`, with
`public import` counted).

## Main definitions

- `AlgebraicGeometry.LocallyRingedSpace.doubleGlueData'`: two copies of `X`, glued along `V`, as a
  `CategoryTheory.GlueData'` — the variant that asks for the overlaps only off the diagonal.
- `AlgebraicGeometry.LocallyRingedSpace.doubleGlueData`: the same as a
  `AlgebraicGeometry.LocallyRingedSpace.GlueData`.
- `AlgebraicGeometry.LocallyRingedSpace.double`: the glued space itself.
- `AlgebraicGeometry.LocallyRingedSpace.doubleFold`: the morphism down to `X` which restricts to
  the identity on each copy.
- `AlgebraicGeometry.LocallyRingedSpace.doubleFoldPartialHomeomorph`: the fold read as an open
  partial homeomorphism on one copy of `X`, which is what exhibits it as a local homeomorphism.

## Main results

- `AlgebraicGeometry.LocallyRingedSpace.doubleGlueData_ι_base_eq_iff`: **two points of the double
  are equal exactly when they come from the same point of `X` and either from the same copy or
  from inside `V`.**
- `AlgebraicGeometry.LocallyRingedSpace.ι_doubleFold`: the fold is a retraction of each copy.
- `AlgebraicGeometry.LocallyRingedSpace.isClosedMap_base_doubleFold`,
  `…finite_preimage_base_doubleFold`, `…isLocalHomeomorph_base_doubleFold` and
  `…isIso_stalkMap_doubleFold`: **the fold is closed, has finite fibres, is a local homeomorphism
  and is an isomorphism on every stalk.** Four separate statements, because they are what a
  consumer that has to check a morphism against a four-field condition asks for one at a time.
- `AlgebraicGeometry.LocallyRingedSpace.not_t2Space_double`: **the double is not Hausdorff as soon
  as some point outside `V` is in the closure of `V`** — the two copies of that point cannot be
  separated, because any two neighbourhoods of them meet inside `V`.

## What is not here

* **No claim that the double is not Hausdorff for every `V`.** If `V` is clopen the double is the
  disjoint union of `X` and `X`, which is Hausdorff whenever `X` is; the hypothesis of
  `AlgebraicGeometry.LocallyRingedSpace.not_t2Space_double` is what rules that case out and it is
  not weakened here.
* **No converse**, and no statement about the double when `V = ⊤`. That case is `X` itself up to
  isomorphism and nothing below says so.
* **Nothing about `n` copies rather than two.** The construction generalises to any index type,
  but `t'` and `cocycle` stop being vacuous the moment three pairwise distinct indices exist, and
  nothing here is evidence about what they cost then.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace Topology

universe u

namespace AlgebraicGeometry.LocallyRingedSpace

noncomputable section

variable (X : LocallyRingedSpace.{u}) (V : Opens X)

/-! ### The glue datum -/

/-- **Two copies of `X` glued along `V`, as a `CategoryTheory.GlueData'`.**

Both members are `X`, both overlaps are the open subspace `V`, both inclusions are
`AlgebraicGeometry.LocallyRingedSpace.ofRestrict` and both transitions are the identity — the two
copies are glued along `V` by the identity of `V` and by nothing else.

`t'`, `t_fac` and `cocycle` are `False.elim`: they are asked for only at triples of **pairwise
distinct** indices and `ULift Bool` has none. The `have` is stated before the structure instance
rather than three times inside it, and `decide` closes it. -/
def doubleGlueData' : CategoryTheory.GlueData' LocallyRingedSpace.{u} :=
  have hJ : ∀ i j k : ULift.{u} Bool, i ≠ j → i ≠ k → j ≠ k → False := by decide
  { J := ULift.{u} Bool
    U _ := X
    V _ _ _ := X.restrict V.isOpenEmbedding
    f _ _ _ := X.ofRestrict V.isOpenEmbedding
    t _ _ _ := 𝟙 _
    t' i j k hij hik hjk := (hJ i j k hij hik hjk).elim
    t_fac i j k hij hik hjk := (hJ i j k hij hik hjk).elim
    t_inv _ _ _ := Category.comp_id _
    cocycle i j k hij hik hjk := (hJ i j k hij hik hjk).elim }

/-- **Two copies of `X` glued along `V`, as a
`AlgebraicGeometry.LocallyRingedSpace.GlueData`.**

`CategoryTheory.GlueData.ofGlueData'` of the datum above, with `f_open` from
`AlgebraicGeometry.LocallyRingedSpace.isOpenImmersion_f'` — the same route
`ComplexAnalytic.specGlueData` takes, and for the same reason: building a
`AlgebraicGeometry.LocallyRingedSpace.GlueData` directly means producing `t'` at every triple. -/
def doubleGlueData : LocallyRingedSpace.GlueData.{u} where
  toGlueData := CategoryTheory.GlueData.ofGlueData' (doubleGlueData'.{u} X V)
  f_open i j :=
    isOpenImmersion_f' (doubleGlueData'.{u} X V)
      (fun _ _ _ ↦ isOpenImmersion_ofRestrict _ _) i j

/-- **The members are the two copies of `X` one put in.**

`rfl`, and stated for the reason `ComplexAnalytic.specGlueData_U` is stated: without it the glue
datum is a well-typed object with no recorded relation to its input, since
`CategoryTheory.GlueData.ofGlueData'` has no projection lemmas in Mathlib —
`Oka/CategoryTheory/GlueData.lean` is where that is measured, with the version and the command.
**This docstring already named a sibling for the reason and restated the absence anyway, and it
did so until 2026-09-21**, when taxis #2118 gave it the anchor for the evidence. -/
@[simp]
theorem doubleGlueData_U (i : ULift.{u} Bool) : (doubleGlueData.{u} X V).U i = X := rfl

/-- **Off the diagonal the overlap is the open subspace on `V`.**

`dif_neg`, named because it is the equality every `eqToHom` below is taken along and because a
caller that writes `dif_neg` inline has to write the `dite`'s motive out. -/
theorem doubleGlueData_V_of_ne {i j : ULift.{u} Bool} (h : i ≠ j) :
    (doubleGlueData.{u} X V).V (i, j) = X.restrict V.isOpenEmbedding := dif_neg h

variable {X V}

/-- **Off the diagonal the inclusion is the inclusion of `V`, after the `eqToHom`.** -/
theorem doubleGlueData_f_of_ne {i j : ULift.{u} Bool} (h : i ≠ j) :
    (doubleGlueData.{u} X V).f i j =
      eqToHom (doubleGlueData_V_of_ne X V h) ≫ X.ofRestrict V.isOpenEmbedding :=
  CategoryTheory.GlueData.ofGlueData'_f_of_ne (doubleGlueData'.{u} X V) h

/-- **And so is the transition followed by the other inclusion**, because the transition is the
identity.

The two statements are not one: `f i j` and `t i j ≫ f j i` are the two legs the relation of
`AlgebraicGeometry.LocallyRingedSpace.GlueData.ι_eq_iff` is phrased through, and it is *because*
they are the same morphism here that a point of the overlap is glued to itself. -/
theorem doubleGlueData_t_comp_f_of_ne {i j : ULift.{u} Bool} (h : i ≠ j) :
    (doubleGlueData.{u} X V).t i j ≫ (doubleGlueData.{u} X V).f j i =
      eqToHom (doubleGlueData_V_of_ne X V h) ≫ X.ofRestrict V.isOpenEmbedding := by
  refine (CategoryTheory.GlueData.ofGlueData'_t_comp_f_of_ne (doubleGlueData'.{u} X V) h).trans ?_
  dsimp only [doubleGlueData']
  rw [Category.id_comp]
  rfl

variable (X V)

/-! ### The doubled space and its two points over each point of `X ∖ V` -/

/-- **The double of `X` along `V`.** -/
abbrev double : LocallyRingedSpace.{u} := (doubleGlueData.{u} X V).toGlueData.glued

variable {X V}

/-- **Two points of the double coming from different copies are equal exactly when they are the
same point of `V`.**

`AlgebraicGeometry.LocallyRingedSpace.GlueData.ι_eq_iff` at this datum, with the `eqToHom` of
`AlgebraicGeometry.LocallyRingedSpace.doubleGlueData_V_of_ne` peeled off both legs. The backward
direction has to produce a point of `(doubleGlueData X V).V (i, j)`, which is a `dite`; it is
produced by transporting `⟨x, hx⟩` along that same `eqToHom`, and the local `have` below is the
one computation that says the transport cancels. -/
theorem doubleGlueData_ι_base_eq_iff_of_ne {i j : ULift.{u} Bool} (hij : i ≠ j) (x y : X) :
    ((doubleGlueData.{u} X V).toGlueData.ι i).base x =
      ((doubleGlueData.{u} X V).toGlueData.ι j).base y ↔ x = y ∧ x ∈ V := by
  refine ((doubleGlueData.{u} X V).ι_eq_iff i j x y).trans ?_
  have hf := doubleGlueData_f_of_ne (X := X) (V := V) hij
  have ht := doubleGlueData_t_comp_f_of_ne (X := X) (V := V) hij
  constructor
  · rintro ⟨z, hz1, hz2⟩
    rw [hf] at hz1
    rw [ht] at hz2
    simp only [LocallyRingedSpace.comp_base] at hz1 hz2
    refine ⟨hz1.symm.trans hz2, ?_⟩
    have hx : x ∈ Set.range ⇑(X.ofRestrict V.isOpenEmbedding).base := ⟨_, hz1⟩
    rwa [X.range_ofRestrict] at hx
  · rintro ⟨rfl, hx⟩
    have main : ∀ g : (doubleGlueData.{u} X V).V (i, j) ⟶ X,
        eqToHom (doubleGlueData_V_of_ne X V hij).symm ≫ g = X.ofRestrict V.isOpenEmbedding →
        g.base ((eqToHom (doubleGlueData_V_of_ne X V hij).symm).base ⟨x, hx⟩) = x := by
      intro g hg
      have h1 := congrArg (fun m : X.restrict V.isOpenEmbedding ⟶ X ↦ m.base ⟨x, hx⟩) hg
      simp only [LocallyRingedSpace.comp_base] at h1
      exact h1
    refine ⟨(eqToHom (doubleGlueData_V_of_ne X V hij).symm).base ⟨x, hx⟩, main _ ?_, main _ ?_⟩
    · rw [hf, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    · rw [ht, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

/-- **Each copy of `X` sits injectively in the double**, since its inclusion is an open
immersion. -/
theorem injective_base_doubleGlueData_ι (i : ULift.{u} Bool) :
    Function.Injective ⇑((doubleGlueData.{u} X V).toGlueData.ι i).base :=
  ((doubleGlueData.{u} X V).ι_isOpenImmersion i).base_open.injective

/-- **When two points of the double are equal.**

The diagonal case is injectivity above and not the relation at `V (i, i)`: that overlap is the
`dite`'s positive branch and reading the relation there would mean peeling a different `eqToHom`
for no gain. -/
theorem doubleGlueData_ι_base_eq_iff (i j : ULift.{u} Bool) (x y : X) :
    ((doubleGlueData.{u} X V).toGlueData.ι i).base x =
      ((doubleGlueData.{u} X V).toGlueData.ι j).base y ↔ x = y ∧ (i = j ∨ x ∈ V) := by
  rcases eq_or_ne i j with rfl | hij
  · exact ⟨fun h ↦ ⟨injective_base_doubleGlueData_ι i h, Or.inl rfl⟩, fun h ↦ congrArg _ h.1⟩
  · rw [doubleGlueData_ι_base_eq_iff_of_ne hij]
    simp [hij]

/-! ### The fold -/

variable (X V)

/-- **A family of copies of one morphism out of `X` agrees over the datum's overlaps.**

The hypothesis `AlgebraicGeometry.LocallyRingedSpace.GlueData.glueMorphisms` asks for, at every
pair — `CategoryTheory.GlueData.ofGlueData'_comm` from the off-diagonal statement, which here is
`ofRestrict ≫ g = 𝟙 ≫ ofRestrict ≫ g`. -/
theorem doubleGlueData_comm {Y : LocallyRingedSpace.{u}} (g : X ⟶ Y) (i j : ULift.{u} Bool) :
    (doubleGlueData.{u} X V).f i j ≫ g =
      (doubleGlueData.{u} X V).t i j ≫ (doubleGlueData.{u} X V).f j i ≫ g :=
  CategoryTheory.GlueData.ofGlueData'_comm (doubleGlueData'.{u} X V) (fun _ ↦ g)
    (fun _ _ _ ↦ by dsimp only [doubleGlueData']; simp) i j

/-- **The two legs into a member are the same morphism.**

`AlgebraicGeometry.LocallyRingedSpace.doubleGlueData_comm` at `g = 𝟙`. It is what says the gluing
is along the identity of `V` and nothing else, and it is the form a consumer needs when it has to
compare the two structures an overlap inherits — one through each leg. -/
theorem doubleGlueData_f_eq_t_comp_f (i j : ULift.{u} Bool) :
    (doubleGlueData.{u} X V).f i j =
      (doubleGlueData.{u} X V).t i j ≫ (doubleGlueData.{u} X V).f j i := by
  simpa using doubleGlueData_comm X V (𝟙 X) i j

/-- **The fold**, glued from the identity on each of the two copies. -/
def doubleFold : double.{u} X V ⟶ X :=
  (doubleGlueData.{u} X V).glueMorphisms (fun _ ↦ 𝟙 X) (doubleGlueData_comm X V (𝟙 X))

/-- **The fold restricts to the identity on each copy**, which is the universal property in the
form every proof below uses. -/
@[reassoc (attr := simp)]
theorem ι_doubleFold (i : ULift.{u} Bool) :
    (doubleGlueData.{u} X V).toGlueData.ι i ≫ doubleFold.{u} X V = 𝟙 X :=
  (doubleGlueData.{u} X V).ι_glueMorphisms _ _ i

/-- The same, on underlying maps. -/
theorem doubleFold_base_comp_ι_base (i : ULift.{u} Bool) :
    ⇑(doubleFold.{u} X V).base ∘ ⇑((doubleGlueData.{u} X V).toGlueData.ι i).base = _root_.id :=
  congrArg (fun m : X ⟶ X ↦ ⇑m.base) (ι_doubleFold X V i)

/-- The same, at a point.

**Not a `simp` lemma**, and that is measured rather than a preference: with the attribute the
`simpNF` linter rejects it, because
`AlgebraicGeometry.LocallyRingedSpace.doubleGlueData_U` rewrites its left-hand side inside the
instance arguments of the `TopCat` coercion. Every use below names it. -/
theorem doubleFold_base_ι_base (i : ULift.{u} Bool) (y : X) :
    (doubleFold.{u} X V).base (((doubleGlueData.{u} X V).toGlueData.ι i).base y) = y :=
  congrFun (doubleFold_base_comp_ι_base X V i) y

/-! ### The fold is closed, finite, and a local isomorphism -/

/-- **The image of a set under the fold is the union of its two preimages.**

Every point of the double is `ι i y` for some `i` and `y`, and the fold sends it to `y`; so a
point of `X` is in the image of `C` exactly when one of the two copies of it lies in `C`. This one
equation is what makes the fold a closed map, and the same computation at a singleton is what
bounds its fibres. -/
theorem image_base_doubleFold (C : Set (double.{u} X V)) :
    ⇑(doubleFold.{u} X V).base '' C =
      ⋃ i : ULift.{u} Bool, ⇑((doubleGlueData.{u} X V).toGlueData.ι i).base ⁻¹' C := by
  ext y
  simp only [Set.mem_image, Set.mem_iUnion, Set.mem_preimage]
  constructor
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨i, a, rfl⟩ := (doubleGlueData.{u} X V).ι_jointly_surjective c
    exact ⟨i, by rwa [doubleFold_base_ι_base]⟩
  · rintro ⟨i, hi⟩
    exact ⟨_, hi, doubleFold_base_ι_base X V i y⟩

/-- **The fold is a closed map**: a union of two closed sets. -/
theorem isClosedMap_base_doubleFold : IsClosedMap ⇑(doubleFold.{u} X V).base := by
  intro C hC
  rw [image_base_doubleFold]
  exact isClosed_iUnion_of_finite fun i ↦
    hC.preimage (((doubleGlueData.{u} X V).ι_isOpenImmersion i).base_open.continuous)

/-- **The fibre of the fold over a point is its two copies.** -/
theorem preimage_base_doubleFold_singleton (y : X) :
    ⇑(doubleFold.{u} X V).base ⁻¹' {y} =
      Set.range fun i : ULift.{u} Bool ↦ ((doubleGlueData.{u} X V).toGlueData.ι i).base y := by
  ext c
  simp only [Set.mem_preimage, Set.mem_range]
  constructor
  · rintro rfl
    obtain ⟨i, a, rfl⟩ := (doubleGlueData.{u} X V).ι_jointly_surjective c
    exact ⟨i, by rw [doubleFold_base_ι_base]⟩
  · rintro ⟨i, rfl⟩
    exact doubleFold_base_ι_base X V i y

/-- **So the fibres of the fold are finite.** -/
theorem finite_preimage_base_doubleFold (y : X) :
    Finite (⇑(doubleFold.{u} X V).base ⁻¹' {y}) := by
  rw [preimage_base_doubleFold_singleton]
  exact Set.Finite.to_subtype (Set.finite_range _)

/-- **The fold, read on the `i`-th copy of `X`.**

`Topology.IsLocalHomeomorph` asks for an `OpenPartialHomeomorph` whose coercion is the map
itself, so this is built with the fold as its `toFun` rather than obtained from the inclusion's
`Topology.IsOpenEmbedding`; the inverse is the inclusion and the source is its range. -/
def doubleFoldPartialHomeomorph (i : ULift.{u} Bool) :
    OpenPartialHomeomorph (double.{u} X V) X where
  toFun := ⇑(doubleFold.{u} X V).base
  invFun := ⇑((doubleGlueData.{u} X V).toGlueData.ι i).base
  source := Set.range ⇑((doubleGlueData.{u} X V).toGlueData.ι i).base
  target := Set.univ
  map_source' _ _ := Set.mem_univ _
  map_target' y _ := Set.mem_range_self y
  left_inv' := by rintro _ ⟨y, rfl⟩; rw [doubleFold_base_ι_base]
  right_inv' y _ := doubleFold_base_ι_base X V i y
  open_source := ((doubleGlueData.{u} X V).ι_isOpenImmersion i).base_open.isOpen_range
  open_target := isOpen_univ
  continuousOn_toFun := (doubleFold.{u} X V).base.hom.continuous.continuousOn
  continuousOn_invFun :=
    ((doubleGlueData.{u} X V).ι_isOpenImmersion i).base_open.continuous.continuousOn

/-- **The fold is a local homeomorphism.** -/
theorem isLocalHomeomorph_base_doubleFold :
    IsLocalHomeomorph ⇑(doubleFold.{u} X V).base := by
  intro x
  obtain ⟨i, y, rfl⟩ := (doubleGlueData.{u} X V).ι_jointly_surjective x
  exact ⟨doubleFoldPartialHomeomorph X V i, Set.mem_range_self y, rfl⟩

set_option backward.isDefEq.respectTransparency false in
/-- **The fold is an isomorphism on every stalk.**

The proof is `AlgebraicGeometry.LocallyRingedSpace.OpenCover.isIso_stalkMap_fromGlued`'s with the
member's inclusion into `X` replaced by the identity: at a point `ι i y` the composite
`ι i ≫ doubleFold` is `𝟙 X`, whose stalk map is an isomorphism, and the inclusion's stalk map is
an isomorphism because it is an open immersion.

The `set_option` is that proof's too: without it the rewrite by
`CategoryTheory.IsIso.eq_comp_inv` fails, reporting that the hypothesis is not type-correct at
`instances` transparency because the two stalks are indexed at the same point spelled two ways. -/
instance isIso_stalkMap_doubleFold (x : double.{u} X V) :
    IsIso ((doubleFold.{u} X V).stalkMap x) := by
  obtain ⟨i, y, rfl⟩ := (doubleGlueData.{u} X V).ι_jointly_surjective x
  haveI := (doubleGlueData.{u} X V).ι_isOpenImmersion i
  have h := LocallyRingedSpace.stalkMap_congr_hom _ _ (ι_doubleFold X V i) y
  rw [LocallyRingedSpace.stalkMap_comp, ← IsIso.eq_comp_inv] at h
  have heq : (((doubleGlueData.{u} X V).toGlueData.ι i ≫ doubleFold.{u} X V).base) y =
      ((𝟙 X : X ⟶ X).base) y := by
    rw [ι_doubleFold]
    rfl
  haveI := TopCat.Presheaf.isIso_stalkSpecializes_of_eq X.presheaf
    (specializes_of_eq heq.symm) heq
  haveI : IsIso ((𝟙 X : X ⟶ X).stalkMap y) := by
    rw [LocallyRingedSpace.stalkMap_id]
    exact CategoryTheory.IsIso.id _
  rw [h]
  infer_instance

/-! ### The double is not Hausdorff -/

/-- **The double is not Hausdorff as soon as a point outside `V` is in the closure of `V`.**

The two copies of such a point are distinct by
`AlgebraicGeometry.LocallyRingedSpace.doubleGlueData_ι_base_eq_iff`, and they cannot be separated:
neighbourhoods of them pull back to neighbourhoods of `x₀` in `X`, whose intersection meets `V`,
and a point of `V` has only one copy — so it lies in both neighbourhoods at once.

**The hypothesis is not decoration.** If `V` is clopen no point outside it is in its closure, the
double is the disjoint union of two copies of `X`, and it is Hausdorff whenever `X` is. -/
theorem not_t2Space_double (x₀ : X) (hx₀ : x₀ ∉ V) (hcl : x₀ ∈ closure (V : Set X)) :
    ¬ T2Space (double.{u} X V) := by
  intro h
  have hne : ((doubleGlueData.{u} X V).toGlueData.ι ⟨false⟩).base x₀ ≠
      ((doubleGlueData.{u} X V).toGlueData.ι ⟨true⟩).base x₀ := by
    rw [Ne, doubleGlueData_ι_base_eq_iff]
    simp [hx₀]
  obtain ⟨W₁, W₂, hW₁, hW₂, hx₁, hx₂, hd⟩ := h.t2 hne
  have hc : ∀ i : ULift.{u} Bool,
      Continuous ⇑((doubleGlueData.{u} X V).toGlueData.ι i).base :=
    fun i ↦ ((doubleGlueData.{u} X V).ι_isOpenImmersion i).base_open.continuous
  have hA : IsOpen (⇑((doubleGlueData.{u} X V).toGlueData.ι ⟨false⟩).base ⁻¹' W₁ ∩
      ⇑((doubleGlueData.{u} X V).toGlueData.ι ⟨true⟩).base ⁻¹' W₂) :=
    ((hW₁.preimage (hc _)).inter (hW₂.preimage (hc _)))
  obtain ⟨z, hzA, hzV⟩ := mem_closure_iff.mp hcl _ hA ⟨hx₁, hx₂⟩
  refine Set.disjoint_left.mp hd hzA.1 ?_
  have : ((doubleGlueData.{u} X V).toGlueData.ι ⟨false⟩).base z =
      ((doubleGlueData.{u} X V).toGlueData.ι ⟨true⟩).base z := by
    rw [doubleGlueData_ι_base_eq_iff]
    exact ⟨rfl, Or.inr hzV⟩
  rw [this]
  exact hzA.2

end

end AlgebraicGeometry.LocallyRingedSpace
