/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.AnalyticSpace.SeparatedFiberFunctor
import Oka.AnalyticSpace.SeparatedFiniteEtaleLimits

/-!
# The fibre functor at the separated covers preserves pullbacks

`Oka/AnalyticSpace/SeparatedFiberFunctor.lean` builds the fibre at a point of the base as a functor
out of `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver X`, into `Type u` and into
`FintypeCat`, and proves two of the six obligations a fibre functor of a Galois category carries —
the terminal object at the two functors themselves, and the reflection of isomorphisms at their
restrictions along the inclusion of the subcategory of objects with preconnected total space.
`Oka/AnalyticSpace/SeparatedFiniteEtaleLimits.lean` builds the fibre product of two morphisms of
that category over a Hausdorff base. **Neither file can see the other, and the instrument is one
walk**: the transitive `Oka`-prefixed import closure of each — `import` **and** `public import`
lines alike, for the reason `## The instrument the closure figures are taken with` gives — holds
seventy-five modules **counting itself** at the commit that adds this file, and neither closure
holds the other module,
`Oka/AnalyticSpace/SeparatedFiniteEtale.lean` being the only `Oka` import line either file has.
This is the module that imports both and says the one thing that needs both:

    CategoryTheory.Limits.PreservesLimitsOfShape CategoryTheory.Limits.WalkingCospan
      (ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.fintypeFiberFunctor x)

for `[T2Space X]`, and the same for the `Type u`-valued functor. **That is the second of the six
obligations in the order the class lists them, and the third this repository states at the two
fibre functors themselves** — after the terminal object and finite coproducts — **which brings to
four the number of the six it states anywhere**, the reflection of isomorphisms being stated at the
restrictions of the two functors along the preconnected subcategory's inclusion and not at them.
**The second and third of those three counts are pinned to the commit that adds this file and the
first is not** — the first is a fact about the order of the fields of Mathlib's class and does not
move with this tree, and `## What is not here`'s first bullet is where the other two are
enumerated and where the reason for their pin is given.

## What the obstruction was, and it was an identification and not an instance

`Oka/AnalyticSpace/SeparatedFiberFunctor.lean`'s `## What is not here` says of this field that the
limit whose image would have to be computed exists and that what is missing is *an identification
of the fibre of that limit with the set-theoretic pullback of the two fibres*. **That diagnosis is
right, and the identification costs nothing**: the fibre of the fibre product **is** the
set-theoretic pullback of the two fibres, definitionally, and
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.fibreProdFiberEquiv` below is an `Equiv`
whose two round trips are the only content.

The chain that makes it definitional is three constructions deep and is written out here because a
reader meeting the statement will want it and the three constructions it runs through document
their own step and not the composite:
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.fibreProd` is
`CategoryTheory.MorphismProperty.Over.mk` at
`ComplexAnalytic.AnalyticSpace.baseChangeSnd i.left j.left ≫ B.hom`;
`ComplexAnalytic.AnalyticSpace.baseChange` is `ComplexAnalytic.AnalyticSpace.coveringSpace` at
`ComplexAnalytic.AnalyticSpace.baseChangeSndBase`; that space is built from an
`AlgebraicGeometry.LocallyRingedSpace.inverseImage`, **whose topological space is the source on the
nose**, and the source is `ComplexAnalytic.AnalyticSpace.baseChangeCarrier`, which is `TopCat.of`
of Mathlib's `Function.Pullback`. `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fiber` is spelled
as a preimage of a singleton, so the outer subtype falls out with no coercion either.

**One of the two projections is not `rfl` on points and the other is**, which is why there are two
value lemmas below rather than none. `ComplexAnalytic.AnalyticSpace.base_baseChangeFst` is proved
by `ext` in `Oka/AnalyticSpace/FiniteEtaleBaseChange.lean` — the projection to the finite étale
leg's source is built as three factors through inverse images, and only the middle one moves a
point — while the projection the space is structured by is the identity on points. **That
asymmetry is that file's and not this one's**, and it is the same asymmetry
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.fibreProdFst`'s docstring describes from
the other side.

## This is the first preservation statement here that is not a transport

At the commit that adds this file, every statement about these two functors that either of this
file's two imports carries is an ambient one read across
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.toFiniteEtaleOver`: faithfulness,
conservativity and — with one `rfl` in place of a transport — the terminal object.
**This one cannot be, and the reason is that the ambient category has no such limit.**
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver` has no fibre products in this repository at the
commit that adds this file — `git grep -l 'AnalyticSpace\.FiniteEtaleOver\.fibreProd'` over `Oka/`
and `OkaTest/` is **empty**, and the anchor is not decoration: without it the pattern matches every
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.fibreProd…` name, of which the tree has
many, because the shorter namespace is a substring of the longer one. **The other family of
`fibreProd` names, and it is not a counterexample**: `ComplexAnalytic.AnalyticSpace.fibreProdCutOut`
and the fifteen names beside it — sixteen rows of `scripts/DumpOkaDecls.lean`'s output at the
commit that adds this file — are a fibre product of **analytic spaces** presented by cut-out data,
not of covers, and they are the whole of what a `fibreProd` scan of that dump returns outside
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver` there. The fibre
product is what `Oka/AnalyticSpace/SeparatedFiniteEtaleLimits.lean` supplies one category in, over
a Hausdorff base, out of hypotheses that only an object of the separated category carries. So the
cone whose image is computed below exists only here, the limit is proved here, and
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fiberFunctor` gains nothing from this file.

## The instrument the closure figures are taken with

**A closure walk over this tree has to follow `public import` and not only `import`.** Twenty-nine
of the two hundred and forty tracked `.lean` files under `Oka/` open with `module` and
write their imports as `public import`, thirteen of them carrying a `public import Oka…` line; a
walk anchored on `^import Oka` alone returns **sixty-one** modules for
`Oka/AnalyticSpace/SeparatedFiberFunctor.lean` where its closure is **seventy-five**, and it does
so silently, with no missing file and no unparsed line to report. **The check that needs no walk
at all** is `env.allImportedModuleNames` filtered to the `Oka` prefix, in a `run_cmd` in a file
importing the root, and it is what every closure figure in this docstring was taken with. All of
them are pinned to the commit that adds this file.

## The two functors, and which relation between them is used

`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.fintypeFiberFunctor` composed with
`FintypeCat.incl` **is**
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.fiberFunctor`, by `rfl`: the two are the
same composite with the same inclusion, differing in whether the value is bundled with its
finiteness, and `FintypeCat.incl` forgets exactly that bundling. So the
`FintypeCat`-valued statement is the `Type u`-valued one read back through a fully faithful functor
— `CategoryTheory.Limits.preservesLimit_of_reflects_of_preserves` — and is four lines.

**That is a different relation from the one the terminal-object pair uses**, and the difference is
worth stating rather than inheriting: `Oka/AnalyticSpace/SeparatedFiberFunctor.lean` says of its
two terminal-object instances that neither is derived from the other, because
`CategoryTheory.Limits.IsTerminal` of one *value* is not `CategoryTheory.Limits.IsTerminal` of the
other. Here the two statements are about the *functors* and not about values, and one functor is
the other composed with a fully faithful one, so the derivation is available and is taken.

## Main definitions

- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.fibreProdFiberEquiv`: **the fibre of the
  fibre product is the set-theoretic pullback of the two fibres**, as an `Equiv` — the
  identification `Oka/AnalyticSpace/SeparatedFiberFunctor.lean` names as the missing thing.
- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.isLimitFiberFunctorMapFibreProd`: **the
  image of the fibre-product square under the fibre functor is a limit cone**, in
  `CategoryTheory.Limits.PullbackCone` form.

## Main results

- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.val_fiberFunctor_map_fibreProdFst` and
  `…SeparatedFiniteEtaleOver.val_fiberFunctor_map_fibreProdSnd`: **what the two projections do to
  a point of the fibre**, which is the whole computational content of this file.
- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.preservesPullbacks_fiberFunctor` and
  `…SeparatedFiniteEtaleOver.preservesPullbacks_fintypeFiberFunctor`: **both fibre functors
  preserve pullbacks**, over a Hausdorff base and with nothing asked of the point.

## What is not here

* **No `FiberFunctor` instance, and no `PreGaloisCategory` instance to hang one on.** That
  namespace is not in this repository's import closure — the measurement is
  `Oka/AnalyticSpace/SeparatedFiberFunctor.lean`'s and is not retaken here — so the class cannot
  be cited by name in a statement below and the count in this file's heading is prose. **Of the six
  fields of that fibre-functor class, this repository states four at the commit that adds this
  file, and three of the four at the two fibre functors themselves**: preservation of the terminal
  object, in that module; preservation of finite coproducts, in
  `Oka/AnalyticSpace/SeparatedFiberFunctorCoproducts.lean`; and preservation of pullbacks, here.
  **The fourth is the reflection of isomorphisms, and it is stated at the restrictions of the two
  functors along the preconnected subcategory's inclusion and not at them** — which is the
  distinction `Oka/AnalyticSpace/SeparatedFiberFunctorCoproducts.lean` draws in terms for its own
  count, and the reason a bare numeral will not do here. The two this repository does not state at
  all are preservation of epimorphisms and of quotients by finite group actions. **Both counts are
  pinned to the commit that adds this file, and the reason is that they move under pushes this file
  cannot see**: the count at the two functors stood at one and the count anywhere at two until
  `Oka/AnalyticSpace/SeparatedFiberFunctorCoproducts.lean` landed on 2026-09-15, and this file
  moves each of them by one again.
* **Nothing about the other three fields, and *other* is read against this file and not against
  the tree.** No epimorphism is mapped below, no group acts on anything, and the coproduct of this
  category is not mentioned here — **finite coproducts are nevertheless stated at both fibre
  functors**, in `Oka/AnalyticSpace/SeparatedFiberFunctorCoproducts.lean`, which is why the bullet
  above counts four fields stated and this one counts three fields untouched. The bullets of
  `Oka/AnalyticSpace/SeparatedFiberFunctor.lean` recording those three fields as absent **from
  that module** come out of this push unweakened — its finite-coproducts bullet already carries the
  pointer the push that landed that module wrote — and only the clause about pullbacks is retired.
* **No `CategoryTheory.Limits.PreservesFiniteLimits`.** The terminal object and pullbacks are two
  of the three generators and the third — that the category has the limits to preserve — is
  `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.hasFiniteLimits`, which is in the sibling
  this file imports. **What is missing is the assembly and not an input**, and it is left out
  deliberately: the class a Galois category asks for is the two shapes separately, and a statement
  in the stronger form would have to be re-read against that class by anyone checking the field.
* **Nothing at `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver`.** The ambient fibre functor gains
  no preservation statement here, for the reason `## This is the first preservation statement here
  that is not a transport` gives: there is no ambient limit to preserve.
* **Nothing is said about the degree of a fibre product**, although the equivalence below computes
  its fibre. `ComplexAnalytic.AnalyticSpace.degree_eq_card_fiber` would turn that into a count over
  a preconnected base, and no statement below mentions it —
  `Oka/AnalyticSpace/SeparatedFiniteEtaleLimits.lean`'s own `## What is not here` records the same
  absence from the other side and is not retired by this file.
* **No comparison with the ambient fibre product.** The underlying object of
  `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.fibreProd` is
  `ComplexAnalytic.AnalyticSpace.baseChange` on the nose, and nothing below says that the forgetful
  functor to `ComplexAnalytic.AnalyticSpace` carries the square to
  `ComplexAnalytic.AnalyticSpace.isPullback_baseChange`.
-/

open CategoryTheory CategoryTheory.Limits

universe u

noncomputable section

namespace ComplexAnalytic.AnalyticSpace

namespace SeparatedFiniteEtaleOver

variable {X : AnalyticSpace.{u}} [T2Space (X : Type u)]
variable {A B C : SeparatedFiniteEtaleOver.{u} X}

/-! ### What the two projections do to a point of the fibre -/

/-- **The image of the fibre-product square under the fibre functor commutes.**

`CategoryTheory.Functor.map_comp` twice at
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.fibreProd_square`, which is the whole of
it: a functor carries a commuting square to a commuting square and nothing about this square or
this functor enters. It is stated rather than inlined because
`CategoryTheory.Limits.PullbackCone.mk` needs it as a term in two places below and because the
`CategoryTheory.Limits.IsLimit` it is the condition of has to name it to be re-used. -/
theorem fiberFunctor_map_fibreProd_square (i : A ⟶ C) (j : B ⟶ C) (x : X) :
    (fiberFunctor.{u} x).map (fibreProdFst i j) ≫ (fiberFunctor.{u} x).map i =
      (fiberFunctor.{u} x).map (fibreProdSnd i j) ≫ (fiberFunctor.{u} x).map j := by
  rw [← Functor.map_comp, ← Functor.map_comp, fibreProd_square]

/-- **The first projection sends a point of the fibre to the first component of its carrier.**

A point of the fibre of `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.fibreProd` is a
point of `Function.Pullback` of the two underlying base maps together with a proof that it lies
over `x`, and a point of that is a pair together with a proof that the two legs agree; this says
the first projection reads off the first component of the pair.

**The `change` is not decoration and the `rw` is the one step with content, and `change` is what
this file uses rather than `show` because the goal it produces is not the one it was given —
which is the distinction `linter.style.show` enforces and which cost this file one build.** The
underlying
morphism of `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.fibreProdFst` is
`ComplexAnalytic.AnalyticSpace.baseChangeFst`, whose base map is the carrier's first projection
only by `ComplexAnalytic.AnalyticSpace.base_baseChangeFst` and not definitionally — that morphism
is three factors through inverse images. The `haveI` restates the instance that morphism asks for,
which `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.fibreProdFst` restates for itself and
which is not in scope at a bare statement. -/
theorem val_fiberFunctor_map_fibreProdFst (i : A ⟶ C) (j : B ⟶ C) (x : X)
    (z : (fiberFunctor.{u} x).obj (fibreProd i j)) :
    (((fiberFunctor.{u} x).map (fibreProdFst i j)).hom z).1 = z.1.1.1 := by
  haveI : IsFiniteEtale i.left := isFiniteEtale_left i
  change (baseChangeFst i.left j.left).toLRSHom.base z.1 = _
  rw [base_baseChangeFst]
  rfl

/-- **The second projection reads off the second component, and this one is `rfl`.**

The asymmetry with
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.val_fiberFunctor_map_fibreProdFst` is the
construction's: the analytic structure on the fibre product is the inverse image **along the second
projection of the carrier**, so that projection's base map is that projection on the nose, while
the first has to be factored through an inverse image. -/
theorem val_fiberFunctor_map_fibreProdSnd (i : A ⟶ C) (j : B ⟶ C) (x : X)
    (z : (fiberFunctor.{u} x).obj (fibreProd i j)) :
    (((fiberFunctor.{u} x).map (fibreProdSnd i j)).hom z).1 = z.1.1.2 := rfl

/-! ### The identification of the fibre -/

/-- **The fibre of the fibre product is the set-theoretic pullback of the two fibres.**

This is the identification `Oka/AnalyticSpace/SeparatedFiberFunctor.lean`'s `## What is not here`
names as the thing standing between that module and this field, and it is an `Equiv` rather than an
`Iso` because what it identifies is the *value* of the functor at one object and not the functor.

**Both round trips are
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.val_fiberFunctor_map_fibreProdFst` and
`…SeparatedFiniteEtaleOver.val_fiberFunctor_map_fibreProdSnd` and nothing else.** The forward map
is the pair
of the two projections, its side condition being the commuting square read at the point; the
backward map is the pair of the two underlying points, its side condition being the pullback
condition of the two fibre elements read at `Subtype.val`. **The proof that the backward map lands
in the fibre is the second component's and not a conjunction**, because a point of the carrier over
`x` for the second leg is over `x` for the first by the square, so nothing has to be supplied
twice.

**The limit below does not go through this**, and that is deliberate: a cone's lift is a map out of
an arbitrary object and an `Equiv` would have to be composed with it, which costs more than the
four lines the lift takes directly. What this declaration is for is the reader, and a consumer that
wants the fibre as a set. -/
def fibreProdFiberEquiv (i : A ⟶ C) (j : B ⟶ C) (x : X) :
    (fiberFunctor.{u} x).obj (fibreProd i j) ≃
      Function.Pullback (FiniteEtaleOver.fiberMap.{u} x ((toFiniteEtaleOver X).map i))
        (FiniteEtaleOver.fiberMap.{u} x ((toFiniteEtaleOver X).map j)) where
  toFun z :=
    ⟨(((fiberFunctor.{u} x).map (fibreProdFst i j)).hom z,
        ((fiberFunctor.{u} x).map (fibreProdSnd i j)).hom z),
      congrArg (fun m : (fiberFunctor.{u} x).obj (fibreProd i j) ⟶
        (fiberFunctor.{u} x).obj C ↦ m.hom z) (fiberFunctor_map_fibreProd_square i j x)⟩
  invFun p := ⟨⟨(p.1.1.1, p.1.2.1), congrArg Subtype.val p.2⟩, p.1.2.2⟩
  left_inv z := Subtype.ext (Subtype.ext (Prod.ext
    (val_fiberFunctor_map_fibreProdFst i j x z) (val_fiberFunctor_map_fibreProdSnd i j x z)))
  right_inv _ := Subtype.ext (Prod.ext
    (Subtype.ext (val_fiberFunctor_map_fibreProdFst i j x _))
    (Subtype.ext (val_fiberFunctor_map_fibreProdSnd i j x _)))

/-! ### The limit, and the two instances -/

/-- **The image of the fibre-product square under the fibre functor is a limit cone.**

`CategoryTheory.Limits.PullbackCone.IsLimit.mk` at the square above, with the four data given
directly rather than transported across
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.fibreProdFiberEquiv`.

**The lift is asymmetric and the asymmetry is the object's.** A competing cone gives, at each point
of its vertex, a point of the fibre of `A` and a point of the fibre of `B` whose images in the
fibre of `C` agree; the carrier of the fibre product wants the pair and that agreement, and the
proof that the pair lies over `x` is the *second* component's proof and not a conjunction — the
first component's would do as well and is not asked for, because the structure morphism of the
fibre product is the second projection followed by `B`'s.

**The condition on the competing cone is read at a point by `congrArg` and not by `simp`.** A
morphism of `Type u` in this Mathlib is a one-field structure, so `s.condition` is an equality of
structures and the function it carries is reached by `CategoryTheory.Functor` composition being
`rfl` on the underlying map; `congrArg` at `fun m ↦ (m.hom t).1` is that read-off, and it is the
same move the equivalence above makes.

**Uniqueness is the two value lemmas and `Subtype.ext` twice.** Two points of the fibre with the
same two components are equal, the pullback condition and the proof of lying over `x` both being
propositions. -/
def isLimitFiberFunctorMapFibreProd (i : A ⟶ C) (j : B ⟶ C) (x : X) :
    IsLimit (PullbackCone.mk ((fiberFunctor.{u} x).map (fibreProdFst i j))
      ((fiberFunctor.{u} x).map (fibreProdSnd i j))
      (fiberFunctor_map_fibreProd_square i j x)) :=
  PullbackCone.IsLimit.mk _
    (fun s ↦ TypeCat.ofHom fun t ↦
      ⟨⟨((s.fst.hom t).1, (s.snd.hom t).1),
        congrArg (fun m : s.pt ⟶ (fiberFunctor.{u} x).obj C ↦ (m.hom t).1) s.condition⟩,
        (s.snd.hom t).2⟩)
    (fun _ ↦ by
      ext t
      exact Subtype.ext (val_fiberFunctor_map_fibreProdFst i j x _))
    (fun _ ↦ by
      ext t
      exact Subtype.ext (val_fiberFunctor_map_fibreProdSnd i j x _))
    (fun s m h1 h2 ↦ by
      ext t
      exact Subtype.ext (Subtype.ext (Prod.ext
        ((val_fiberFunctor_map_fibreProdFst i j x (m.hom t)).symm.trans
          (congrArg (fun n : s.pt ⟶ (fiberFunctor.{u} x).obj A ↦ (n.hom t).1) h1))
        ((val_fiberFunctor_map_fibreProdSnd i j x (m.hom t)).symm.trans
          (congrArg (fun n : s.pt ⟶ (fiberFunctor.{u} x).obj B ↦ (n.hom t).1) h2)))))

/-- **So the fibre functor preserves the fibre product of one cospan.**

`CategoryTheory.Limits.preservesLimit_of_preserves_limit_cone` at
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.isPullback_fibreProd`, which is the limit
in this category, and the cone above, which is its image.

**`CategoryTheory.Limits.isLimitMapConePullbackConeEquiv` is what crosses between
`CategoryTheory.Functor.mapCone` of a `CategoryTheory.Limits.PullbackCone.mk` and the
`CategoryTheory.Limits.PullbackCone.mk` of the mapped morphisms**, and its `comm` argument is
passed explicitly. Left as a placeholder it has no way to solve the two type arguments of the
equivalence and the failure names neither the functor nor the cone. -/
instance preservesLimit_cospan_fiberFunctor (i : A ⟶ C) (j : B ⟶ C) (x : X) :
    PreservesLimit (cospan i j) (fiberFunctor.{u} x) :=
  preservesLimit_of_preserves_limit_cone (isPullback_fibreProd i j).isLimit
    ((isLimitMapConePullbackConeEquiv (fiberFunctor.{u} x)
      (fibreProd_square i j)).symm (isLimitFiberFunctorMapFibreProd i j x))

/-- **The fibre functor preserves pullbacks**, over a Hausdorff base and with nothing asked of the
point.

The instance above is at a cospan `cospan i j`; this is at an arbitrary
`CategoryTheory.Limits.WalkingCospan`-shaped diagram, and the bridge is
`CategoryTheory.Limits.diagramIsoCospan`, which says every such diagram is isomorphic to one of
that form. **That is the one step of this file that quantifies over a diagram rather than over a
cospan**, and it is Mathlib's idiom for the shape rather than anything about covers. -/
instance preservesPullbacks_fiberFunctor (x : X) :
    PreservesLimitsOfShape WalkingCospan (fiberFunctor.{u} x) where
  preservesLimit {K} :=
    preservesLimit_of_iso_diagram (fiberFunctor.{u} x) (diagramIsoCospan K).symm

/-- **And so does the `FintypeCat`-valued fibre functor, at one cospan.**

`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.fintypeFiberFunctor` composed with
`FintypeCat.incl` is
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.fiberFunctor` by `rfl`, so the instance
above is already the hypothesis
`CategoryTheory.Limits.preservesLimit_of_reflects_of_preserves` asks for; what that lemma
contributes is the reflection, and `FintypeCat.incl` reflects limits because it is
fully faithful.

**This is a derivation and the terminal-object pair is not**, which
`## The two functors, and which relation between them is used` at the head of this file is about:
there the two statements are about *values* of the two functors and neither is the other's, here
they are about the functors themselves and one functor is the other composed with a fully faithful
one. -/
instance preservesLimit_cospan_fintypeFiberFunctor (i : A ⟶ C) (j : B ⟶ C) (x : X) :
    PreservesLimit (cospan i j) (fintypeFiberFunctor.{u} x) :=
  haveI : PreservesLimit (cospan i j) (fintypeFiberFunctor.{u} x ⋙ FintypeCat.incl.{u}) :=
    preservesLimit_cospan_fiberFunctor i j x
  preservesLimit_of_reflects_of_preserves _ FintypeCat.incl.{u}

/-- **The `FintypeCat`-valued fibre functor preserves pullbacks**, which is the shape a Galois
category asks the field in.

`CategoryTheory.Limits.diagramIsoCospan` again, at the instance above; the two functors are handled
separately at this last step rather than transported, because
`CategoryTheory.Limits.PreservesLimitsOfShape` is a statement about a functor and the transport
would be the same two lines with a composite in the way. -/
instance preservesPullbacks_fintypeFiberFunctor (x : X) :
    PreservesLimitsOfShape WalkingCospan (fintypeFiberFunctor.{u} x) where
  preservesLimit {K} :=
    preservesLimit_of_iso_diagram (fintypeFiberFunctor.{u} x) (diagramIsoCospan K).symm

end SeparatedFiniteEtaleOver

end ComplexAnalytic.AnalyticSpace

end
