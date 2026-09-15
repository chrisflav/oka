/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.AnalyticSpace.SeparatedOver

/-!
# Separatedness as a second conjunct, and the category of covers separated over the base

`Oka/AnalyticSpace/SeparatedOver.lean` proves that a monomorphism of covers separated over a
Hausdorff base exhibits its source as a direct summand of its target, and it says in terms that it
does not make the choice its own statements raise: *"Whether the condition belongs as a field of
`ComplexAnalytic.AnalyticSpace.IsFiniteEtale`, as a second conjunct in the morphism property
`FiniteEtaleOver` is built from, or as a class of its own is a choice that has to be made against
a measurement of what it costs the existing statements, and this file is the thing that makes the
measurement possible rather than the thing that makes the choice."*

**This file makes that choice, and it is the second of the three.** Separatedness becomes a
`CategoryTheory.MorphismProperty` in its own right, `ComplexAnalytic.AnalyticSpace.isSeparatedMap`
below, and the category is the one that property cuts out of the covers by intersection:

    SeparatedFiniteEtaleOver X = (isFiniteEtale ⊓ isSeparatedMap).Over ⊤ X

against `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver`'s `isFiniteEtale.Over ⊤ X`. The second `⊤`
is unchanged and deliberate for the reason that file gives of its own: a morphism of separated
covers commutes with the two structure maps and is asked for nothing else.

## What the choice costs, measured rather than asserted

**No declaration that existed before this module is edited**, and that is the measurement rather
than a way of putting it: `ComplexAnalytic.AnalyticSpace.IsFiniteEtale` gains no field,
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver` is not redefined, no landed statement acquires a
hypothesis and no landed proof is touched. **The push that adds this module touches four files and
the instrument is `git diff --numstat` against its base**: this one, which is new;
`Oka/Topology/SeparatedMap.lean`, which gains two general-topology statements; the root
`Oka.lean`, which gains one import line; and `OkaTest/Axioms/Morphisms.lean`, which gains a guard
section and the module-docstring clause that section owes. **Five lines are removed anywhere in
it, all five in `Oka/Topology/SeparatedMap.lean`'s header and all five prose** — its title, the
sentence retired there with a dated record, and a bullet restated to cover three statements
instead of one. **That is the whole of the measurement
`Oka/AnalyticSpace/SeparatedOver.lean` asked for**, and it is the argument for this branch of the
three rather than a remark about it: a field of `ComplexAnalytic.AnalyticSpace.IsFiniteEtale`
would put the condition into every statement that class appears in, and this puts it into none of
them.

**What it does not do is argue that the other two branches are wrong.** A field would make the
condition part of what *finite étale* means in this repository, which is a claim about the
definition and not about a category, and a class of its own would give the condition a home
independent of the covers. Neither is refuted here; what is shown is that the conjunct is
available at no cost to anything already proved, and a branch with that property is worth taking
before one without it.

## The result that is new, and it is not a restatement

`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.injective_base_left_of_mono_of_isSeparatedMap`
asks its morphism to be a monomorphism **in the category of covers**. The
`monoInducesIsoOnDirectSummand` field of `Mathlib/CategoryTheory/Galois/Basic.lean`'s
`PreGaloisCategory` — whose namespace is not in this file's import closure and so cannot be
cited by name here — offers a monomorphism **in the category the axiom is stated over**, which
under this choice is the separated one. Those are different hypotheses, and the second is a priori
the weaker: a monomorphism of covers is one here, because every test object of this category is a
cover, while the converse asks a cancellation against test objects this category does not contain.
**Whether they coincide is not settled here and nothing below claims it.**

`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.injective_base_left_of_mono` is the
statement at the weaker hypothesis, and **the reason it goes through is that `A ×_B A` is itself
separated over the base**. The cancellation in the ambient proof happens against that object and
against nothing else, so it is enough that the object be in this category —
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.selfProd` is where that is discharged, and
it is discharged in two steps: `IsSeparatedMap.pullback`, Mathlib's, makes the projection
`A ×_B A ⟶ A` separated because `i` is, and `IsSeparatedMap.comp` composes that with `A`'s own
structure morphism. **`i` is separated because `A` is** — its structure morphism factors through
`i`, and `IsSeparatedMap.of_comp` reads separatedness off a composite for its first factor.
Neither of those two topological statements was in Mathlib; both are added by this push, in
`Oka/Topology/SeparatedMap.lean`, whose header says what Mathlib has of that shape and why it does
not give either.

## Where each hypothesis is spent

* **`[T2Space X]`, on the base**, is spent only through
  `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.t2Space_left`, which is
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.t2Space_left_of_isSeparatedMap` at an object of
  this category. The category itself, its inclusion, its terminal object and the statement that
  the doubled line is not one of its objects are all stated without it.
* **Separatedness of an object** is spent three times and in three different places: on the total
  space being Hausdorff, on the underlying morphism of a morphism of this category being finite
  étale, and on `A ×_B A` being an object. The first two are
  `Oka/AnalyticSpace/SeparatedOver.lean`'s and are read here at objects of this category; the
  third is this file's.
* **Nothing is assumed of the base beyond `[T2Space X]`** — not connected, not non-empty — and
  nothing is assumed of a morphism beyond `CategoryTheory.Mono` where that is asked.

## Main definitions

- `ComplexAnalytic.AnalyticSpace.isSeparatedMap`: **separatedness of the underlying map, as a
  `CategoryTheory.MorphismProperty`** on complex analytic spaces.
- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver`: **the covers of `X` separated over
  `X`**, as a category.
- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.toFiniteEtaleOver`: **its inclusion into
  the covers**, which is full and faithful.
- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.id`: **the base over itself**, and
  `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.isTerminalId`: it is terminal.
- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.selfProd`: **the fibre product
  `A ×_B A`, as an object of this category**, with its two projections
  `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.selfProdFst` and
  `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.selfProdSnd`.

## Main results

- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.injective_base_left_of_mono`: **a
  monomorphism of this category is injective on points**, over a Hausdorff base and with no
  further hypothesis.
- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.inducesIsoOnDirectSummand_of_mono`: **and
  it exhibits its source as a direct summand of its target**.
- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.t2Space_left`: **the total space of an
  object is Hausdorff**, over a Hausdorff base.
- `ComplexAnalytic.AnalyticSpace.not_inf_isSeparatedMap_doubledLineOver`: **the line with two
  origins is not an object of this category**, so the choice is a restriction and not a renaming.

## What is not here

* **No `PreGaloisCategory` instance and no claim of one.** The field
  `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.inducesIsoOnDirectSummand_of_mono`
  answers to still asks `[T2Space X]` of the base, which the axiom does not; and nothing here
  bears on the other fields — base change over a general cospan of morphisms of this category, or
  quotients by finite group actions — nor on the preservation of epimorphisms by a fibre functor,
  **which is a field of `FiberFunctor` and not one of the other fields of the class this bullet is
  headed by**. **That is a correction and not one of this repository's dated records**: the
  sentence listed that preservation among *the other fields* of `PreGaloisCategory` from the commit
  that wrote it, so it was false when written rather than falsified later.
  `Oka/AnalyticSpace/SeparatedFiniteEtaleLimits.lean` is where the slip was measured and recorded,
  in a bullet saying in terms that the push which made the measurement was not the one to repair
  it; the repair is made here by the push that lands that preservation, in
  `Oka/AnalyticSpace/SeparatedFiberFunctorEpi.lean`.
* **The summand is produced in the covers and not inside this category, and a file this one does
  not import now also produces it inside.**
  `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.inducesIsoOnDirectSummand_of_mono`
  below gives a `Z` in `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver X` and a colimit there, and
  that is still what it gives; **nothing in this file moved**.

  **This bullet read as an open obstruction until 2026-09-12** and the diagnosis it gave was
  right, so it is kept: *"the summand is existentially quantified where it is produced —
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.inducesIsoOnDirectSummand_of_injective` constructs
  it as the complementary clopen part at the range of the monomorphism, and
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isSeparatedMap_restrictClopenCompl` says exactly
  that object is separated over the base whenever the one it is cut out of is — but the existential
  hides which object was taken, so this file cannot reach that lemma from the statement. Landing
  the summand in this category needs the ambient statement restated with its witness named, and
  that is a push on `Oka/AnalyticSpace/DirectSummand.lean` and not on this one."* That push
  happened: `Oka/AnalyticSpace/DirectSummand.lean` now names the witness as
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.directSummandCompl`, and
  `Oka/AnalyticSpace/SeparatedDirectSummand.lean` — **downstream of this file, so nothing here can
  cite its declarations** — gives that object the second component and reflects the colimit back
  along the fully faithful inclusion. **The statement below is unchanged and this file gains no
  import**; what a reader should take from this bullet now is which file to look in.
* **No coproducts, and a file this one does not import now has them.**

  **This bullet read as an open absence until 2026-09-13** and what it said was right, so it is
  kept: *"No coproducts and no terminal-object-and-coproducts package.
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isSeparatedMap_sigma` says a finite disjoint
  union of separated covers is separated, so the objects are available; what is not here is the
  cofan, the colimit, and the `CategoryTheory.Limits.HasFiniteCoproducts` instance they would
  give."* All three arrived in `Oka/AnalyticSpace/SeparatedFiniteEtaleCoproducts.lean` — which
  imports this file directly, so nothing here can cite its declarations — out of that same lemma
  and with no hypothesis on the base. **Nothing in this file moved**: it gains no import, no
  declaration and no statement, and what a reader should take from this bullet now is which file
  to look in.
  **The package this bullet's first sentence also named is not claimed there either**: that file
  declares the coproducts and nothing that bundles them with the terminal object, and its
  `## What is not here` names two of `Mathlib`'s converters into
  `CategoryTheory.Limits.HasFiniteColimits` and measures, for each, what this repository does not
  state.
* **No `#print axioms` guards for the four instances below that carry no name.** They are the
  `CategoryTheory.MorphismProperty.IsStableUnderComposition`,
  `CategoryTheory.MorphismProperty.ContainsIdentities`,
  `CategoryTheory.MorphismProperty.IsMultiplicative` and
  `CategoryTheory.MorphismProperty.RespectsIso` instances of
  `ComplexAnalytic.AnalyticSpace.isSeparatedMap`, and
  `Oka/AnalyticSpace/FiniteEtaleOver.lean` declares the same four for
  `ComplexAnalytic.AnalyticSpace.isFiniteEtale`, equally anonymous and equally unguarded. The
  guard section that carries this module says so and names them.
* **Nothing about a separated morphism that is not the structure morphism of a cover.**
  `ComplexAnalytic.AnalyticSpace.isSeparatedMap` is a property of every morphism of analytic
  spaces and the four instances are about all of them, but every statement below that mentions an
  object mentions a cover.
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

open CategoryTheory Topology TopologicalSpace AlgebraicGeometry

universe u

namespace ComplexAnalytic.AnalyticSpace

/-! ### Separatedness as a morphism property -/

/-- **Separatedness of the underlying map, as a `CategoryTheory.MorphismProperty`.**

`IsSeparatedMap` is `Mathlib/Topology/SeparatedMap.lean`'s and is a property of a bare function;
this reads it at the base map of a morphism of analytic spaces. It is a `def` and not an `abbrev`
for the reason `ComplexAnalytic.AnalyticSpace.isFiniteEtale`'s docstring gives of itself — the
dot notation `isSeparatedMap.Over` has to resolve — and unlike that one it wraps no class, so
`ComplexAnalytic.AnalyticSpace.isSeparatedMap_iff` below is the only unfolding lemma it needs. -/
def isSeparatedMap : MorphismProperty AnalyticSpace.{u} :=
  fun _ _ f ↦ _root_.IsSeparatedMap ⇑(f.toLRSHom.base)

/-- **Membership in the property is separatedness of the base map**, by definition.

`Iff.rfl`, and stated for the same reason
`ComplexAnalytic.AnalyticSpace.isFiniteEtale_iff` is: a caller holding one spelling should not
have to know that the other is definitionally it. -/
theorem isSeparatedMap_iff {X Y : AnalyticSpace.{u}} (f : X ⟶ Y) :
    isSeparatedMap.{u} f ↔ _root_.IsSeparatedMap ⇑(f.toLRSHom.base) :=
  Iff.rfl

instance : (isSeparatedMap.{u}).IsStableUnderComposition where
  comp_mem f _ hf hg := hf.comp hg f.toLRSHom.base.hom.continuous

instance : (isSeparatedMap.{u}).ContainsIdentities where
  id_mem _ := Function.Injective.isSeparatedMap fun _ _ h ↦ h

instance : (isSeparatedMap.{u}).IsMultiplicative where

instance : (isSeparatedMap.{u}).RespectsIso :=
  MorphismProperty.respectsIso_of_isStableUnderComposition
    fun _ _ f (_ : IsIso f) ↦ (bijective_base_of_isIso f).injective.isSeparatedMap

/-- **The first factor of a separated composite is separated.**

`IsSeparatedMap.of_comp` at the base maps, whose composite is the base map of the composite by
`rfl`. **`g` is explicit because it occurs in neither the conclusion nor the hypothesis's binder**
in a position elaboration could read it from — the hypothesis names `f ≫ g` and the conclusion
names `f`, so unification sees `g` only inside the hypothesis's type, which is not enough when the
hypothesis is supplied by a tactic. This is the analytic form of a statement that asks nothing
whatever of `g`: not continuity, not injectivity, not separatedness. -/
theorem isSeparatedMap_of_comp {X Y Z : AnalyticSpace.{u}} {f : X ⟶ Y} (g : Y ⟶ Z)
    (h : isSeparatedMap.{u} (f ≫ g)) : isSeparatedMap.{u} f :=
  IsSeparatedMap.of_comp _ h

/-! ### The category -/

/-- **The covers of `X` separated over `X`**, as a category: the objects are the finite étale
morphisms into `X` whose base map is a separated map, and the morphisms are all the morphisms of
analytic spaces over `X`.

The property is the intersection of two morphism properties and the object condition is their
conjunction, which `CategoryTheory.MorphismProperty` being a complete lattice makes literal: the
proof obligation of an object is a pair. **The second `⊤` is unchanged from
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver` and is deliberate for the same reason** — a
morphism of separated covers commutes with the two structure maps and is asked for nothing else —
and it is what makes
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.toFiniteEtaleOver` full. -/
abbrev SeparatedFiniteEtaleOver (X : AnalyticSpace.{u}) : Type _ :=
  (isFiniteEtale.{u} ⊓ isSeparatedMap.{u}).Over ⊤ X

variable {X : AnalyticSpace.{u}}

/-- **The structure morphism of an object is finite étale.** The first component of the pair the
object carries. -/
theorem SeparatedFiniteEtaleOver.isFiniteEtale_hom (A : SeparatedFiniteEtaleOver.{u} X) :
    IsFiniteEtale A.hom :=
  A.prop.1

/-- **And its base map is separated.** The second component of that pair, and the whole of what
this category asks over `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver`. -/
theorem SeparatedFiniteEtaleOver.isSeparatedMap_hom (A : SeparatedFiniteEtaleOver.{u} X) :
    _root_.IsSeparatedMap ⇑(A.hom.toLRSHom.base) :=
  A.prop.2

variable (X) in
/-- **The inclusion into the covers of `X`.**

`CategoryTheory.MorphismProperty.Over.changeProp` at `inf_le_left`, which forgets the second
component of an object's pair and nothing else. **It is full as well as faithful**, both by
instance search: faithful because every functor of that shape is, and full because the morphism
property is `⊤` on both sides and the implication between them is `le_rfl`. So a morphism of this
category is exactly a morphism of covers between objects of it, which is what the monomorphism
statements below turn on. -/
abbrev SeparatedFiniteEtaleOver.toFiniteEtaleOver :
    SeparatedFiniteEtaleOver.{u} X ⥤ FiniteEtaleOver.{u} X :=
  MorphismProperty.Over.changeProp X inf_le_left le_rfl

/-- **The base over itself**, which is an object because the identity is finite étale and
injective. `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isSeparatedMap_id` is the second half
and asks nothing of `X`. -/
def SeparatedFiniteEtaleOver.id (X : AnalyticSpace.{u}) : SeparatedFiniteEtaleOver.{u} X :=
  MorphismProperty.Over.mk _ (𝟙 X) ⟨isFiniteEtale_id X, FiniteEtaleOver.isSeparatedMap_id⟩

/-- **It is terminal**, with no hypothesis on the base.

The proof is `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isTerminalId`'s read in this category
and it transfers unchanged, because the two categories have the same morphisms between the objects
they share: the unique morphism into it is an object's own structure map, and uniqueness is the
triangle over `X`. **Nothing here goes through
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.toFiniteEtaleOver`** — a terminal object
does not transport along a fully faithful functor without an argument that its image is in the
image of the functor, and rerunning two lines is cheaper than making that argument. -/
def SeparatedFiniteEtaleOver.isTerminalId (X : AnalyticSpace.{u}) :
    Limits.IsTerminal (SeparatedFiniteEtaleOver.id.{u} X) :=
  Limits.IsTerminal.ofUniqueHom
    (fun A ↦ MorphismProperty.Over.homMk (B := SeparatedFiniteEtaleOver.id.{u} X) A.hom
      (Category.comp_id A.hom))
    fun _ f ↦ MorphismProperty.Over.Hom.ext
      ((Category.comp_id f.left).symm.trans (MorphismProperty.Over.w f))

/-- **The category has a terminal object**, as the class rather than as the witness.

Stated for the reason `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.hasTerminal`'s docstring
gives at length: that is the form a `CategoryTheory.Limits.HasTerminal` consumer asks for, and the
Galois-category definition carries this field as an instance. That docstring's argument for
declaring it an `instance` rather than leaving the witness unbundled applies here word for word
and is not repeated. -/
instance SeparatedFiniteEtaleOver.hasTerminal (X : AnalyticSpace.{u}) :
    Limits.HasTerminal (SeparatedFiniteEtaleOver.{u} X) :=
  (SeparatedFiniteEtaleOver.isTerminalId.{u} X).hasTerminal

/-- **The line with two origins is not an object of this category**, although it is a cover of a
Hausdorff base.

`ComplexAnalytic.AnalyticSpace.not_isSeparatedMap_doubledLineOver` at the second component. **This
is what stops the choice this file makes from being a renaming**: the condition is a restriction,
and an object of `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver` that fails it is what says so.
Note the shape of the statement — it negates the conjunction, so it also says the pair cannot be
supplied, which is what an object of this category is. -/
theorem not_inf_isSeparatedMap_doubledLineOver :
    ¬ (isFiniteEtale.{u} ⊓ isSeparatedMap.{u}) (doubledLineOver.{u}).hom :=
  fun h ↦ not_isSeparatedMap_doubledLineOver.{u} h.2

/-! ### Over a Hausdorff base -/

section

variable [T2Space (X : Type u)]

/-- **The total space of an object is Hausdorff**, over a Hausdorff base.

`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.t2Space_left_of_isSeparatedMap` at the image of the
object under the inclusion. **It is an `instance` here and a theorem there**, and the difference is
that there the separatedness is an explicit hypothesis that instance search cannot supply, while
here it is carried by the object; so this is the statement that makes every `[T2Space A.left]`
below unnecessary, and every use of it in this file is by instance search rather than by name. -/
instance SeparatedFiniteEtaleOver.t2Space_left (A : SeparatedFiniteEtaleOver.{u} X) :
    T2Space (A.left : Type u) :=
  FiniteEtaleOver.t2Space_left_of_isSeparatedMap
    ((SeparatedFiniteEtaleOver.toFiniteEtaleOver X).obj A) A.isSeparatedMap_hom

variable {A B : SeparatedFiniteEtaleOver.{u} X}

/-- **The underlying morphism of a morphism of this category is finite étale.**

`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isFiniteEtale_left_of_isSeparatedMap` at the image
of the morphism under the inclusion. The separatedness spent is the **target**'s and the source is
asked for nothing, which is the shape that lemma has and not an artefact of reading it here. -/
theorem SeparatedFiniteEtaleOver.isFiniteEtale_left (i : A ⟶ B) : IsFiniteEtale i.left :=
  FiniteEtaleOver.isFiniteEtale_left_of_isSeparatedMap B.isSeparatedMap_hom
    ((SeparatedFiniteEtaleOver.toFiniteEtaleOver X).map i)

omit [T2Space (X : Type u)] in
/-- **And its base map is separated**, with no hypothesis on the base.

The source's structure morphism factors through it — that is what a morphism over `X` is — so
`ComplexAnalytic.AnalyticSpace.isSeparatedMap_of_comp` reads separatedness off the **source** and
nothing is asked of the target. This is the step that makes the fibre product below an object of
this category, and it is the one place the first-factor statement is spent. -/
theorem SeparatedFiniteEtaleOver.isSeparatedMap_left (i : A ⟶ B) :
    _root_.IsSeparatedMap ⇑(i.left.toLRSHom.base) :=
  isSeparatedMap_of_comp B.hom (by rw [MorphismProperty.Over.w i]; exact A.isSeparatedMap_hom)

/-- **The fibre product `A ×_B A`, as an object of this category.**

The object is `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.selfProd`'s and is written out rather
than transported, so that its underlying space is `ComplexAnalytic.AnalyticSpace.baseChange` on
the nose and the two projections below can be stated with no `eqToHom`. **What is new is the
second component**, and it is two steps: `IsSeparatedMap.pullback` makes the projection to `A`
separated because
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.isSeparatedMap_left` makes `i` separated,
and `IsSeparatedMap.comp` composes that with `A`'s structure morphism, spending the continuity of
the projection. **This is the whole reason a monomorphism of this category is enough below**: the
cancellation is against this object, so it has to be in this category. -/
noncomputable def SeparatedFiniteEtaleOver.selfProd (i : A ⟶ B) :
    SeparatedFiniteEtaleOver.{u} X :=
  haveI : IsFiniteEtale i.left := SeparatedFiniteEtaleOver.isFiniteEtale_left i
  haveI : IsFiniteEtale (X := A.left) A.hom := A.prop.1
  haveI : IsFiniteEtale (baseChangeSnd i.left i.left) := isFiniteEtale_baseChangeSnd i.left i.left
  MorphismProperty.Over.mk _ (baseChangeSnd i.left i.left ≫ A.hom)
    ⟨isFiniteEtale_comp (baseChangeSnd i.left i.left) A.hom,
      ((SeparatedFiniteEtaleOver.isSeparatedMap_left i).pullback _).comp A.isSeparatedMap_hom
        (baseChangeSnd i.left i.left).toLRSHom.base.hom.continuous⟩

/-- **Its second projection, as a morphism of this category.** Its triangle over `X` is `rfl`,
because that projection is what the object was structured by. -/
noncomputable def SeparatedFiniteEtaleOver.selfProdSnd (i : A ⟶ B) :
    SeparatedFiniteEtaleOver.selfProd i ⟶ A :=
  haveI : IsFiniteEtale i.left := SeparatedFiniteEtaleOver.isFiniteEtale_left i
  MorphismProperty.Over.homMk (baseChangeSnd i.left i.left) rfl

/-- **Its first projection, as a morphism of this category.**

The triangle is `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.selfProdFst`'s and the proof is
that one read here: `A.hom` is `i.left ≫ B.hom` because `i` is a morphism over `X`, and the two
composites to `B.left` agree by `ComplexAnalytic.AnalyticSpace.baseChange_square`. **The `change`
is not a `show` and the two `rfl`s are the comma-category seam**, both for the reasons that
docstring gives; neither is a stylistic choice and `lake build --wfail` turns the second into an
error. -/
noncomputable def SeparatedFiniteEtaleOver.selfProdFst (i : A ⟶ B) :
    SeparatedFiniteEtaleOver.selfProd i ⟶ A :=
  haveI : IsFiniteEtale i.left := SeparatedFiniteEtaleOver.isFiniteEtale_left i
  MorphismProperty.Over.homMk (baseChangeFst i.left i.left) (by
    have hw : i.left ≫ B.hom = A.hom := MorphismProperty.Over.w i
    change baseChangeFst i.left i.left ≫ A.hom = baseChangeSnd i.left i.left ≫ A.hom
    have e1 : baseChangeFst i.left i.left ≫ A.hom
        = (baseChangeFst i.left i.left ≫ i.left) ≫ B.hom := by rw [Category.assoc, hw]; rfl
    have e2 : baseChangeSnd i.left i.left ≫ A.hom
        = (baseChangeSnd i.left i.left ≫ i.left) ≫ B.hom := by rw [Category.assoc, hw]; rfl
    rw [e1, e2, baseChange_square])

/-- **A monomorphism of this category is injective on points**, over a Hausdorff base.

**The hypothesis is `CategoryTheory.Mono` in this category and not in the covers**, which is what
this statement is for:
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.injective_base_left_of_mono_of_isSeparatedMap`
proves the same conclusion from a monomorphism of covers, and that is a priori the stronger
hypothesis, since a cancellation there is tested against objects this category does not contain.
The proof is the ambient one with every object replaced by an object of this category: the two
projections of `A ×_B A` are equalised by `i`, the monomorphism makes them equal, and
`ComplexAnalytic.AnalyticSpace.injective_base_of_baseChangeFst_eq` reads injectivity off that one
equation at one point. **Nothing is transported and no isomorphism is built**; what the choice of
category buys is that `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.selfProd` is a legal
test object. -/
theorem SeparatedFiniteEtaleOver.injective_base_left_of_mono (i : A ⟶ B) [Mono i] :
    Function.Injective (i.left.toLRSHom.base : A.left → B.left) := by
  haveI : IsFiniteEtale i.left := SeparatedFiniteEtaleOver.isFiniteEtale_left i
  have h : SeparatedFiniteEtaleOver.selfProdFst i = SeparatedFiniteEtaleOver.selfProdSnd i :=
    (cancel_mono i).1 (MorphismProperty.Over.Hom.ext (baseChange_square i.left i.left))
  exact injective_base_of_baseChangeFst_eq i.left
    (congrArg (fun m : SeparatedFiniteEtaleOver.selfProd i ⟶ A => m.left) h)

/-- **A monomorphism of this category exhibits its source as a direct summand of its target**:
there is a cover `Z` and a morphism `Z ⟶ B` whose binary cofan with `i` is a colimit.

`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.inducesIsoOnDirectSummand_of_injective` with its
injectivity hypothesis discharged by the theorem above and its `[T2Space]` by the object's own
separatedness. **The summand and the colimit are in the covers and not in this category**, and they
stay there: the ambient statement quantifies its witness existentially, so the lemma that would
make that witness separated cannot be reached from *this* statement. **That is a fact about this
theorem and no longer a gap in the repository** — `Oka/AnalyticSpace/SeparatedDirectSummand.lean`,
which this file does not import, produces the summand and the colimit inside this category from the
named witness `Oka/AnalyticSpace/DirectSummand.lean` now carries, and the
`## What is not here` bullet of the same subject records what changed and when.

**The `haveI` is the comma category's and not this statement's** — the
inclusion's action on an object leaves `left` alone by `rfl` but not reducibly so, which is the
seam `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.t2Space_left_of_isSeparatedMap`'s docstring
describes. -/
theorem SeparatedFiniteEtaleOver.inducesIsoOnDirectSummand_of_mono (i : A ⟶ B) [Mono i] :
    ∃ (Z : FiniteEtaleOver.{u} X)
      (u : Z ⟶ (SeparatedFiniteEtaleOver.toFiniteEtaleOver X).obj B),
      Nonempty (Limits.IsColimit (Limits.BinaryCofan.mk
        ((SeparatedFiniteEtaleOver.toFiniteEtaleOver X).map i) u)) :=
  haveI : T2Space
      ((((SeparatedFiniteEtaleOver.toFiniteEtaleOver X).obj B).left : AnalyticSpace.{u}) :
        Type u) :=
    inferInstanceAs (T2Space (B.left : Type u))
  FiniteEtaleOver.inducesIsoOnDirectSummand_of_injective
    ((SeparatedFiniteEtaleOver.toFiniteEtaleOver X).map i)
    (SeparatedFiniteEtaleOver.injective_base_left_of_mono i)

end

end ComplexAnalytic.AnalyticSpace
