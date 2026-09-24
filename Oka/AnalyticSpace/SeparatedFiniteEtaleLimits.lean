/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.AnalyticSpace.SeparatedFiniteEtale

/-!
# Fibre products of separated covers, and `HasFiniteLimits` over a Hausdorff base

`Oka/AnalyticSpace/SeparatedFiniteEtale.lean` builds the category
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver` of covers separated over the base, gives
it a terminal object with no hypothesis whatever, and lists in its `## What is not here` the
absences that stand between it and a Galois category — the first being *"base change over a
general cospan of morphisms of this category"*. **This file closes that one**, over a Hausdorff
base, and assembles it with the terminal object into

    CategoryTheory.Limits.HasFiniteLimits
      (ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver X)   for `[T2Space X]`

## Which field this is, measured rather than repeated

**`HasFiniteLimits` is not a field of `PreGaloisCategory`, and saying so is the point of this
section**: the filing this module was written from called it one, and a reader who takes that on
trust will look for a field that does not exist. `Mathlib/CategoryTheory/Galois/Basic.lean`
declares `PreGaloisCategory` with **five** fields and no `hasFiniteLimits` among them — the two
limit fields are separate — and the run that settles it is `Lean.getStructureInfo?` at that class,
which returns `hasTerminal`, `hasPullbacks`, `hasFiniteCoproducts`,
`hasQuotientsByFiniteGroups` and `monoInducesIsoOnDirectSummand`.

**So what this file closes is the `hasPullbacks` field**, and
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.hasFiniteLimits` below is the standard
consequence of that field together with `hasTerminal`, which the category already had.

**How many of the five hold is pinned to a commit, because it moves — it moved while this module
was in review.** At **`26dc715`**, the commit this module is written on top of, **two** hold at
this category: `hasTerminal`, by
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.hasTerminal` and with no hypothesis on the
base, and `monoInducesIsoOnDirectSummand`, by
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.inducesIsoOnDirectSummand_of_mono'` and
over a Hausdorff base. **At the commit that adds this module, three do**: those two and
`hasPullbacks`. The remaining two are `hasFiniteCoproducts` and `hasQuotientsByFiniteGroups`, and
the `## What is not here` section below says where each of them stands.

That namespace is not in this file's import closure, so every name in the paragraph above is
prose and not a citation. **That is a measurement and not a convention**, and what it measures is
this file's closure: no import of this module reaches `Oka/AnalyticSpace/GaloisCategory.lean`,
which is the only module of this repository whose `import` lines name anything under
`Mathlib/CategoryTheory/Galois/` at the commit that adds it. **This paragraph measured the whole
tree instead — no module reachable from `Oka.lean` importing anything under that directory, and
`scripts/check_docstring_names.py` reporting the class's dotted form as resolving to nothing in
the environment of `import Oka` — until 2026-09-15**, when that module made `Oka.lean` reach it
and so put the class in that environment. **Both halves were exact when they were written and
neither was ever a claim about this file**, which is why the bare form is still used above: that
is the spelling `Oka/AnalyticSpace/SeparatedFiniteEtale.lean` and `Oka/AnalyticSpace/Sigma.lean`
already use, and the reason for it here is this file's closure and not the tree's.

## The construction costs no new mathematics, and that is a claim with a check behind it

**Every input is a landed declaration and none of them is edited.** The object is
`ComplexAnalytic.AnalyticSpace.baseChange` of `Oka/AnalyticSpace/FiniteEtaleBaseChange.lean`, its
universal property is that file's `ComplexAnalytic.AnalyticSpace.baseChangeLift` with
`ComplexAnalytic.AnalyticSpace.baseChangeLift_fst`,
`ComplexAnalytic.AnalyticSpace.baseChangeLift_snd` and
`ComplexAnalytic.AnalyticSpace.baseChange_hom_ext` around it, and the two conditions that make the
result an object of this category are the two `Oka/AnalyticSpace/SeparatedFiniteEtale.lean`
already discharges for
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.selfProd`, with the second leg of the
cospan put where that construction repeats the first. **That is literal and not a resemblance**:
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.fibreProd_self` below says
`fibreProd i i = selfProd i`, and it is `rfl`, as are the two statements beside it about the
projections. So the earlier construction is this one at a repeated leg and no second idea entered
between them.

**What this file adds over the ambient fibre product is the comma category and nothing else.** The
underlying analytic space, the two projections and the lift are `baseChange`'s; what is proved
here is that each of them is a morphism *over* `X`, and that the object carries the pair an object
of this category is. The universal property is then
`CategoryTheory.Limits.PullbackCone.IsLimit.mk` at
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.fibreProdLift` and four statements of this
file — the square, the two triangles and the extensionality — **each of which is one ambient lemma
read through `CategoryTheory.MorphismProperty.Over.Hom.ext` and nothing else**:
`ComplexAnalytic.AnalyticSpace.baseChange_square`,
`ComplexAnalytic.AnalyticSpace.baseChangeLift_fst`,
`ComplexAnalytic.AnalyticSpace.baseChangeLift_snd` and
`ComplexAnalytic.AnalyticSpace.baseChange_hom_ext` in that order. That extensionality is what
reduces equality of morphisms of this category to equality of their underlying morphisms.

## Where the Hausdorff hypothesis is spent, and where the asymmetry comes from

**The construction spends `[T2Space X]` through exactly two declarations of
`Oka/AnalyticSpace/SeparatedFiniteEtale.lean`:**

* **`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.t2Space_left`**, which gives
  `[T2Space A.left]`. It is spent on the **objects** of this category being separated over their
  base and not on the base change: `ComplexAnalytic.AnalyticSpace.baseChange` asks no separation
  axiom of anything.

  **That bullet closed *`ComplexAnalytic.AnalyticSpace.baseChange` asks that of the source of its
  finite étale leg and `Oka/AnalyticSpace/CoveringMap.lean` records why it is not removable
  there*, until 2026-09-14**, when `[T2Space E]` came out of
  `Oka/AnalyticSpace/FiniteEtaleBaseChange.lean`. The named reason was that file's and was exact
  while it stood; what this file spends `[T2Space X]` on is unchanged, and the instance is still
  one of the two that spend it.
* **`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.isFiniteEtale_left`**, which makes the
  underlying morphism of `i` finite étale. That statement spends the **target**'s separatedness
  and the target of `i` is `C`.

**Three more of that file's `[T2Space X]` declarations are named at the foot of this one** —
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.selfProd`, `…selfProdFst` and
`…selfProdSnd`, on the right-hand side of the three `rfl`s. They carry the hypothesis for the same
reason the construction does and add no use of it that `…t2Space_left` and `…isFiniteEtale_left`
do not already account for, but *exactly two* would be false of the file as a whole and is not
what is claimed.

**The construction is not symmetric in the two legs and the asymmetry is in the inputs, not in a
choice made here.** `i` is the leg that is base-changed: its underlying morphism has to be finite
étale, by `…isFiniteEtale_left i`, and separated, by
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.isSeparatedMap_left i` — which reads
separatedness off `A`'s structure morphism and asks nothing of `C`. `j` is asked for nothing
beyond being a morphism of this category; what is used of `B` is its own structure morphism's
finite étaleness and separatedness, which the object carries. **The symmetric statement holds by
symmetry of the limit and not by rerunning this**, and no statement below says so.

## Main definitions

- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.fibreProd`: **the fibre product of two
  morphisms of this category, as an object of it** — `baseChange` of the underlying morphisms,
  structured over `X` by the second projection followed by `B`'s structure morphism.
- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.fibreProdFst` and
  `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.fibreProdSnd`: **its two projections**,
  as morphisms of this category.
- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.fibreProdLift`: **the morphism a
  commuting square induces into it**, at a hypothesis stated on the underlying morphisms.

## Main results

- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.isPullback_fibreProd`: **the square is a
  pullback in this category**.
- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.hasPullback` and
  `…SeparatedFiniteEtaleOver.hasPullbacks`: **so every cospan of this category has a fibre
  product**, over a Hausdorff base.
- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.hasFiniteLimits`: **and the category has
  all finite limits**, which is the consequence of two fields and is itself none, as the head of
  this file measures.
- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.fibreProd_self`, with
  `…fibreProdFst_self` and `…fibreProdSnd_self`: **the self-product this category already had is
  this construction at a repeated leg**, on the nose.

## What is not here

* **No `PreGaloisCategory` instance, and no claim that one is close.** That class is not in this
  file's import closure — measured at the head of this file rather than assumed — so it
  cannot be cited by name in a statement here, and **two of its five fields are untouched at the
  commit that adds this module**: `hasFiniteCoproducts`, which the bullet of this section opening
  *No finite coproducts* is about, and `hasQuotientsByFiniteGroups`, which is stated nowhere in
  this repository — a measurement and not
  an impression, since the name `CategoryTheory.SingleObj` occurs in the comment-stripped code of
  no module of this repository at `26dc715`.

  **This bullet said *three* until 2026-09-12**, naming `monoInducesIsoOnDirectSummand` as the
  third and as the one this repository was nearest to, and it was right when written. What it said
  stood between that statement and the field was *the existential that hides which object the
  summand is*, quoting `Oka/AnalyticSpace/SeparatedFiniteEtale.lean`'s own `## What is not here`;
  **that diagnosis was the right one, and naming the witness is exactly what closed it**.
  `Oka/AnalyticSpace/SeparatedDirectSummand.lean` now lands the summand in this category as
  `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.inducesIsoOnDirectSummand_of_mono'`,
  over a Hausdorff base as this file's own statements are. **That module and this one are
  siblings** — neither imports the other and both import
  `Oka/AnalyticSpace/SeparatedFiniteEtale.lean` — so nothing of this file's Lean reads it and the
  two rungs are independent.
* **Nothing here bears on a fibre functor**, which is a different class — `FiberFunctor` in the
  `PreGaloisCategory` namespace, with fields of its own — and not a field of the one above.
  **`Oka/AnalyticSpace/SeparatedFiniteEtale.lean`'s bullet lists the preservation of epimorphisms
  by a fibre functor among *the other fields* of `PreGaloisCategory`, and that is a slip**: it is a
  field of `FiberFunctor`. **This push does not repair it**, because the sentence carrying it is
  scoped to that file and stays true of it, and widening into a second module's
  `## What is not here` for one word is not what this push is. The measurement is recorded so a
  later seat does not have to make it again.
* **This is not `CategoryTheory.MorphismProperty.IsStableUnderBaseChange` for
  `ComplexAnalytic.AnalyticSpace.isFiniteEtale`, and nothing below is stated from that class or
  bears on it.** That class quantifies over cospans in `ComplexAnalytic.AnalyticSpace` whose finite
  étale leg may have a non-Hausdorff source, and
  `ComplexAnalytic.AnalyticSpace.doubledLineOver` is the standing witness that such a cospan
  exists. Every cospan below is a cospan of **objects of this category**, whose total spaces are
  Hausdorff by `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.t2Space_left`. The bullets
  in `Oka/AnalyticSpace/FiniteEtaleBaseChange.lean` and `Oka/AnalyticSpace/FiniteEtaleOver.lean`
  say what they said before this file existed.

  **This bullet read *…, and the bullets recording that absence are not narrowed* until
  2026-09-15**, when
  `Oka/AnalyticSpace/FiniteEtaleStableUnderBaseChange.lean` stated the class and there ceased to be
  an absence for a bullet to record. Nothing else in the bullet moves: what is here is still not
  that class, for the reason the sentence after the heading gives, and the two bullets named are
  still untouched by this file.
* **`[T2Space X]` is not removed and nothing here tries.** The construction spends it through
  `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.t2Space_left` and
  `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.isFiniteEtale_left`, which are the two
  `## Where the Hausdorff hypothesis is spent, and where the asymmetry comes from` names, and the
  first of those two spends it through a statement whose own hypothesis is Mathlib's in the
  criterion that turns a proper local homeomorphism into a covering map.
* **No finite coproducts and no `CategoryTheory.Limits.HasFiniteColimits`.**
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isSeparatedMap_sigma` makes the objects
  available, as `Oka/AnalyticSpace/SeparatedFiniteEtale.lean` records; the cofan and the colimit
  are not built here and this file does not touch that line. **That rung is not on `master` at
  `26dc715`** and this file cites no declaration of it; finite limits and finite colimits are
  separate questions and nothing below bears on the second.
* **Nothing is said about the fibres or the degree of the fibre product.** The construction is the
  set-level pullback with an analytic structure and its fibres correspond, by
  `Function.Pullback.fst`; no statement below mentions
  `ComplexAnalytic.AnalyticSpace.degree_eq_card_fiber`.
* **No comparison with `CategoryTheory.Limits.pullback` in the ambient category.** The forgetful
  functor `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.toFiniteEtaleOver` and the
  functor to `ComplexAnalytic.AnalyticSpace` are not shown to preserve these limits, although the
  underlying object is `ComplexAnalytic.AnalyticSpace.baseChange` on the nose and
  `ComplexAnalytic.AnalyticSpace.isPullback_baseChange` is the ambient square. **What is missing
  is the statement and not the mathematics**, and a push that wants it should say which of the two
  functors it means.
## The `Mathlib/CategoryTheory/Galois/Basic.lean` scoping, and the record for it

**Every sentence of this file that scopes that namespace read *this repository's import closure*,
until 2026-09-15**, when `Oka/AnalyticSpace/GaloisCategory.lean` imported that file and declared
`CategoryTheory.PreGaloisCategory` at
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver` together with
`CategoryTheory.PreGaloisCategory.FiberFunctor` at its `FintypeCat`-valued fibre functor. **From
that commit the class is in this repository's import closure and is still not in this file's**,
which is why those sentences now say *this file's*: no import of this module reaches the one that
pays for the class, so nothing here can name it and every clause of this file that says so stays
exact. **The rescoping is not this file's whole share of that push**: the paragraph opening *That
namespace is not in this file's import closure* measured the whole tree rather than this file, the
same push falsifies that measurement, and it is retired at its commit above rather than left in
the present tense. `git diff` against the commit this file is cut from shows both halves.
-/

open CategoryTheory Topology TopologicalSpace AlgebraicGeometry

universe u

noncomputable section

namespace ComplexAnalytic.AnalyticSpace

variable {X : AnalyticSpace.{u}}

namespace SeparatedFiniteEtaleOver

section

variable [T2Space (X : Type u)] {A B C : SeparatedFiniteEtaleOver.{u} X}

/-! ### The object and its two projections -/

/-- **The fibre product of two morphisms of this category, as an object of it.**

The underlying analytic space is `ComplexAnalytic.AnalyticSpace.baseChange` of the two underlying
morphisms, written out rather than transported, so that the projections below can be stated with
no `eqToHom`; it is structured over `X` by the second projection followed by `B`'s structure
morphism. **The two components of the object's pair are
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.selfProd`'s with `j.left` in the slot that
construction repeats `i.left` in**, and the file's header says so with a `rfl`.

`ComplexAnalytic.AnalyticSpace.baseChange` asks `[IsFiniteEtale i.left]` and nothing else; it is
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.isFiniteEtale_left`, which spends the
separatedness of the **target** `C`. **This sentence read *asks `[IsFiniteEtale i.left]` and
`[T2Space A.left]`* and named both, until 2026-09-14**, when the second came out of
`Oka/AnalyticSpace/FiniteEtaleBaseChange.lean`; the instance it named,
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.t2Space_left`, is still where `[T2Space X]`
enters. **Separatedness of the structure morphism is two steps**: `IsSeparatedMap.pullback` makes
the projection to `B.left` separated because
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.isSeparatedMap_left` makes `i` separated,
and `IsSeparatedMap.comp` composes that with `B`'s own structure morphism. **Nothing is asked of
`j` beyond its being a morphism of this category**, which is the asymmetry the header describes. -/
def fibreProd (i : A ⟶ C) (j : B ⟶ C) : SeparatedFiniteEtaleOver.{u} X :=
  haveI : IsFiniteEtale i.left := isFiniteEtale_left i
  haveI : IsFiniteEtale (X := B.left) B.hom := B.prop.1
  haveI : IsFiniteEtale (baseChangeSnd i.left j.left) := isFiniteEtale_baseChangeSnd i.left j.left
  MorphismProperty.Over.mk _ (baseChangeSnd i.left j.left ≫ B.hom)
    ⟨isFiniteEtale_comp (baseChangeSnd i.left j.left) B.hom,
      ((isSeparatedMap_left i).pullback _).comp B.isSeparatedMap_hom
        (baseChangeSnd i.left j.left).toLRSHom.base.hom.continuous⟩

/-- **Its second projection, as a morphism of this category.** Its triangle over `X` is `rfl`,
because that projection is what the object was structured by. -/
def fibreProdSnd (i : A ⟶ C) (j : B ⟶ C) : fibreProd i j ⟶ B :=
  haveI : IsFiniteEtale i.left := isFiniteEtale_left i
  MorphismProperty.Over.homMk (baseChangeSnd i.left j.left) rfl

/-- **Its first projection, as a morphism of this category.**

The triangle over `X` is where `ComplexAnalytic.AnalyticSpace.baseChange_square` is spent: `A.hom`
is `i.left ≫ C.hom` and `B.hom` is `j.left ≫ C.hom`, both because a morphism of this category
commutes with the structure maps, and the two composites into `C.left` agree by that square.
**The `change` is not a `show` and the two `rfl`s at the ends of `e1` and `e2` are the comma
category's seam**, for the reason
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.selfProdFst`'s docstring gives of the same
two lines: `CategoryTheory.MorphismProperty.Over` is a comma category over
`CategoryTheory.Functor.id`, so a structure morphism's source is `(𝟭 _).obj A.left` rather than
`A.left`, and a `rw` whose motive crosses that unifier fails on an instance argument rather than
on the equation. -/
def fibreProdFst (i : A ⟶ C) (j : B ⟶ C) : fibreProd i j ⟶ A :=
  haveI : IsFiniteEtale i.left := isFiniteEtale_left i
  MorphismProperty.Over.homMk (baseChangeFst i.left j.left) (by
    have hi : i.left ≫ C.hom = A.hom := MorphismProperty.Over.w i
    have hj : j.left ≫ C.hom = B.hom := MorphismProperty.Over.w j
    change baseChangeFst i.left j.left ≫ A.hom = baseChangeSnd i.left j.left ≫ B.hom
    have e1 : baseChangeFst i.left j.left ≫ A.hom
        = (baseChangeFst i.left j.left ≫ i.left) ≫ C.hom := by rw [Category.assoc, hi]; rfl
    have e2 : baseChangeSnd i.left j.left ≫ B.hom
        = (baseChangeSnd i.left j.left ≫ j.left) ≫ C.hom := by rw [Category.assoc, hj]; rfl
    rw [e1, e2, baseChange_square])

/-- **The square commutes in this category.**
`CategoryTheory.MorphismProperty.Over.Hom.ext` at
`ComplexAnalytic.AnalyticSpace.baseChange_square`, which is the whole of it: the comma category
contributes the extensionality and nothing else, and the triangles over `X` are already carried by
the two projections. -/
theorem fibreProd_square (i : A ⟶ C) (j : B ⟶ C) :
    fibreProdFst i j ≫ i = fibreProdSnd i j ≫ j :=
  haveI : IsFiniteEtale i.left := isFiniteEtale_left i
  MorphismProperty.Over.Hom.ext (baseChange_square i.left j.left)

/-! ### The universal property -/

/-- **The morphism a commuting square induces into the fibre product.**

`ComplexAnalytic.AnalyticSpace.baseChangeLift` at the underlying morphisms, made a morphism over
`X` by `ComplexAnalytic.AnalyticSpace.baseChangeLift_snd`: the composite to the structure morphism
of the fibre product is the lift followed by the second projection followed by `B.hom`, which is
`b.left ≫ B.hom` and so is `Z.hom`.

**The hypothesis is stated on the underlying morphisms and not as `a ≫ i = b ≫ j`**, which is the
form a caller holding a `CategoryTheory.Limits.PullbackCone` has to convert to anyway — the
conversion is `congrArg` at `left` and is `rfl`-thin because
`CategoryTheory.MorphismProperty.Comma.comp_left` is `rfl`. Stating it this way keeps the `rfl`
at the one call site in this file rather than inside the definition, where a later reader would
have to unfold it to see what was proved. -/
def fibreProdLift (i : A ⟶ C) (j : B ⟶ C) {Z : SeparatedFiniteEtaleOver.{u} X}
    (a : Z ⟶ A) (b : Z ⟶ B) (hab : a.left ≫ i.left = b.left ≫ j.left) : Z ⟶ fibreProd i j :=
  haveI : IsFiniteEtale i.left := isFiniteEtale_left i
  MorphismProperty.Over.homMk (baseChangeLift i.left j.left a.left b.left hab) (by
    change baseChangeLift i.left j.left a.left b.left hab ≫
      baseChangeSnd i.left j.left ≫ B.hom = Z.hom
    rw [← Category.assoc, baseChangeLift_snd, MorphismProperty.Over.w b])

/-- **The lift is over `A`.** `ComplexAnalytic.AnalyticSpace.baseChangeLift_fst` read through the
comma category's extensionality. -/
theorem fibreProdLift_fst (i : A ⟶ C) (j : B ⟶ C) {Z : SeparatedFiniteEtaleOver.{u} X}
    (a : Z ⟶ A) (b : Z ⟶ B) (hab : a.left ≫ i.left = b.left ≫ j.left) :
    fibreProdLift i j a b hab ≫ fibreProdFst i j = a :=
  haveI : IsFiniteEtale i.left := isFiniteEtale_left i
  MorphismProperty.Over.Hom.ext (baseChangeLift_fst i.left j.left a.left b.left hab)

/-- **And over `B`.** `ComplexAnalytic.AnalyticSpace.baseChangeLift_snd` read the same way — the
same lemma the triangle over `X` in
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.fibreProdLift` is proved from, and spent
here at its own statement rather than under a composite. -/
theorem fibreProdLift_snd (i : A ⟶ C) (j : B ⟶ C) {Z : SeparatedFiniteEtaleOver.{u} X}
    (a : Z ⟶ A) (b : Z ⟶ B) (hab : a.left ≫ i.left = b.left ≫ j.left) :
    fibreProdLift i j a b hab ≫ fibreProdSnd i j = b :=
  haveI : IsFiniteEtale i.left := isFiniteEtale_left i
  MorphismProperty.Over.Hom.ext (baseChangeLift_snd i.left j.left a.left b.left hab)

/-- **Two morphisms of this category into the fibre product agreeing on both projections are
equal.** `ComplexAnalytic.AnalyticSpace.baseChange_hom_ext` under
`CategoryTheory.MorphismProperty.Over.Hom.ext`, whose two hypotheses are the given ones read at
`left`. **Faithfulness is what makes this cheap and it is not assumed**: the extensionality lemma
of a `CategoryTheory.MorphismProperty.Over` is an equality of underlying morphisms, so no
cancellation in this category is needed and the ambient statement transfers with no side
condition. -/
theorem fibreProd_hom_ext (i : A ⟶ C) (j : B ⟶ C) {Z : SeparatedFiniteEtaleOver.{u} X}
    {u v : Z ⟶ fibreProd i j} (h1 : u ≫ fibreProdFst i j = v ≫ fibreProdFst i j)
    (h2 : u ≫ fibreProdSnd i j = v ≫ fibreProdSnd i j) : u = v :=
  haveI : IsFiniteEtale i.left := isFiniteEtale_left i
  MorphismProperty.Over.Hom.ext
    (baseChange_hom_ext i.left j.left
      (congrArg (fun m : Z ⟶ A ↦ m.left) h1) (congrArg (fun m : Z ⟶ B ↦ m.left) h2))

/-- **The square is a pullback in this category.**

`CategoryTheory.Limits.PullbackCone.IsLimit.mk` at
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.fibreProd_square`,
`…SeparatedFiniteEtaleOver.fibreProdLift`, `…SeparatedFiniteEtaleOver.fibreProdLift_fst`,
`…SeparatedFiniteEtaleOver.fibreProdLift_snd` and
`…SeparatedFiniteEtaleOver.fibreProd_hom_ext`, named rather than reached by position; the cone's
condition is read at `left` by `congrArg` — which typechecks because
`CategoryTheory.MorphismProperty.Comma.comp_left` is `rfl`.

**It is stated in the `CategoryTheory.IsPullback` form and the `CategoryTheory.Limits.IsLimit` is
not named**, which is the shape
`ComplexAnalytic.AnalyticSpace.isPullback_baseChange` has in the file the object comes from; a
consumer that wants the cone gets it from `CategoryTheory.IsPullback.isLimit`. -/
theorem isPullback_fibreProd (i : A ⟶ C) (j : B ⟶ C) :
    IsPullback (fibreProdFst i j) (fibreProdSnd i j) i j :=
  IsPullback.of_isLimit (Limits.PullbackCone.IsLimit.mk (fibreProd_square i j)
    (fun s ↦ fibreProdLift i j s.fst s.snd (congrArg (fun m : s.pt ⟶ C ↦ m.left) s.condition))
    (fun s ↦ fibreProdLift_fst i j s.fst s.snd _)
    (fun s ↦ fibreProdLift_snd i j s.fst s.snd _)
    (fun s _ hm1 hm2 ↦ fibreProd_hom_ext i j
      (hm1.trans (fibreProdLift_fst i j s.fst s.snd _).symm)
      (hm2.trans (fibreProdLift_snd i j s.fst s.snd _).symm)))

/-- **So a cospan of this category has a fibre product.** An instance, so that
`CategoryTheory.Limits.pullback i j` elaborates in this category. -/
instance hasPullback (i : A ⟶ C) (j : B ⟶ C) : Limits.HasPullback i j :=
  (isPullback_fibreProd i j).hasPullback

/-! ### The self-product this category already had -/

/-- **`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.selfProd` is this construction at a
repeated leg**, on the nose and not up to isomorphism.

`rfl`. The two objects are `CategoryTheory.MorphismProperty.Over.mk` at the same morphism and the
pairs they carry are propositions, so nothing but the structure morphism has to agree — and it is
`baseChangeSnd i.left i.left ≫ A.hom` on both sides. **This is the file header's claim that no
second idea entered**, stated as a theorem so that it cannot go stale silently: if either
construction is rewritten, this line stops compiling. -/
theorem fibreProd_self (i : A ⟶ B) : fibreProd i i = selfProd i := rfl

/-- **And so are its two projections**, first one. `rfl`, for the same reason. -/
theorem fibreProdFst_self (i : A ⟶ B) : fibreProdFst i i = selfProdFst i := rfl

/-- **And so are its two projections**, second one. `rfl`, for the same reason. -/
theorem fibreProdSnd_self (i : A ⟶ B) : fibreProdSnd i i = selfProdSnd i := rfl

end

/-! ### The category has all finite limits -/

/-- **Every cospan of this category has a fibre product**, over a Hausdorff base, as the class
rather than at a named cospan.

`CategoryTheory.Limits.hasPullbacks_of_hasLimit_cospan` at
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.hasPullback`. Stated for the reason
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.hasTerminal`'s docstring gives of itself:
that is the form a `CategoryTheory.Limits.HasPullbacks` consumer asks for, and
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.hasFiniteLimits` is one of them. -/
instance hasPullbacks (X : AnalyticSpace.{u}) [T2Space (X : Type u)] :
    Limits.HasPullbacks (SeparatedFiniteEtaleOver.{u} X) :=
  Limits.hasPullbacks_of_hasLimit_cospan _

/-- **The category of covers separated over a Hausdorff base has all finite limits.**

`CategoryTheory.Limits.hasFiniteLimits_of_hasTerminal_and_pullbacks` at
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.hasTerminal`, which asks nothing of the
base, and at `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.hasPullbacks`, which asks
`[T2Space X]`. **This is not a field of `PreGaloisCategory` and the head of this file measures
that** — that class's five fields are `hasTerminal`, `hasPullbacks`, `hasFiniteCoproducts`,
`hasQuotientsByFiniteGroups` and `monoInducesIsoOnDirectSummand`, and it carries no
`hasFiniteLimits`. What this module closes is `hasPullbacks`; this statement is what that field
and `hasTerminal` give together, and it is stated because it is the form a general limit consumer
asks for. **The fields this module does not close are named in the `## What is not here` section
of this file rather than counted here**, since how many of the five hold moves with `master` and
that section pins it to a commit; in particular nothing here bears on a fibre functor, which is a
different class again. -/
instance hasFiniteLimits (X : AnalyticSpace.{u}) [T2Space (X : Type u)] :
    Limits.HasFiniteLimits (SeparatedFiniteEtaleOver.{u} X) :=
  Limits.hasFiniteLimits_of_hasTerminal_and_pullbacks

end SeparatedFiniteEtaleOver

end ComplexAnalytic.AnalyticSpace
