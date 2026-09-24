/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.AnalyticSpace.FiniteEtaleOver

/-!
# A morphism of covers that is injective on points exhibits its source as a direct summand

`Mathlib/CategoryTheory/Galois/Basic.lean`'s `PreGaloisCategory` asks, of every monomorphism
`i : A ⟶ B`, for an object `Z` and a morphism `Z ⟶ B` making `B` the binary coproduct of `A` and
`Z`. This file proves that statement at
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver X` **with the monomorphism hypothesis replaced by
injectivity of the underlying map, and with a Hausdorff hypothesis on the target cover's total
space added**. Both replacements are discussed under `## What is not here`, and neither is
cosmetic: what is proved here is not that field.

The geometry is the one a reader would guess. A morphism of covers over a Hausdorff total space is
itself finite étale, so its image is open because it is a local isomorphism and closed because it
is finite; an injective map onto its own image is a bijection onto it, and a bijective local
isomorphism is an isomorphism. So the source is isomorphic to the target restricted to a clopen
subset, and `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isColimitBinaryCofanRestrictClopen`
already says a cover is the coproduct of a clopen part and its complement.

## Main definitions

- `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.rangeOpens`: **the image of a morphism of covers,
  as an open subset of the target's total space**, which is the shape
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.restrictClopen` and its complement are indexed by.
- `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.directSummandCompl`: **the summand complementary
  to a morphism of covers**, and
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.directSummandComplι`: **its inclusion into the
  target**. Neither asks for injectivity.

## Main results

- `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isFiniteEtale_left`: **the underlying morphism of
  a morphism of covers is finite étale when the target cover's total space is Hausdorff**, which is
  `ComplexAnalytic.AnalyticSpace.isFiniteEtale_of_comp` at the triangle a morphism of covers
  commutes.
- `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isClopen_range_left`: **and so its image is
  clopen**, which is where the decomposition comes from.
- `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isColimitBinaryCofanDirectSummandCompl`: **the
  target is the coproduct of the source and that summand**, at an injective morphism and with both
  objects named.
- `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.inducesIsoOnDirectSummand_of_injective`: **the
  direct-summand statement itself**, in the shape `PreGaloisCategory`'s field is written in — an
  object and a morphism to `B` whose binary cofan with `i` is a colimit.
- `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isIso_of_bijective_fiberMap_of_t2`: **a morphism
  of covers bijective on the fibre over one point of a preconnected base is an isomorphism**, with
  nothing asked of either cover beyond Hausdorffness. It is here and not in
  `Oka/AnalyticSpace/FiniteEtaleOver.lean` because the summand above is what empties and that file
  cannot cite it — this module's only `Oka` import line names it, so the direction is read off the
  head of this file; taxis #2025 is the filing and the docstring below compares the two routes.

**The named witness and the existential are both here on purpose.** The existential is the shape
the field asks for and is what the two modules of `Oka/` that apply it cite; the named one is what
a caller needing a *property* of the summand has to have, and
`Oka/AnalyticSpace/SeparatedDirectSummand.lean` is the first such caller. **The witnesses were
added on 2026-09-12 and nothing else in this file moved**: the existential's statement is character
for character what it was.

## What is not here

* **The `PreGaloisCategory` field.** That field asks for the summand at every monomorphism and
  under no hypothesis on the base, on the source or on the target. This statement asks for
  `[T2Space B.left]` and for injectivity, and **nothing below derives either of them from
  `Mono i`**. **Saying so is the point of this paragraph**: the gap is named rather than hidden
  behind a statement that reads like the field.
* **A proof that a monomorphism of covers is injective on points, which is not below and is no
  longer absent from the repository.** **This bullet opened *"A proof that a monomorphism of
  covers is injective on points. That is the remaining obligation"* until 2026-09-07**, when
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.injective_base_left_of_mono`
  (`Oka/AnalyticSpace/MonoDirectSummand.lean`) proved it for a monomorphism of covers both of
  whose total spaces are Hausdorff — **it has asked only the target's since 2026-09-14**, when
  `[T2Space E]` came out of `Oka/AnalyticSpace/FiniteEtaleBaseChange.lean` — and
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.inducesIsoOnDirectSummand_of_mono` fed it to the
  theorem below. **Nothing below moved and nothing below derives injectivity from `Mono i`**;
  what changed is that a file this one does not import does.

  **The route was not the one this bullet predicted, and the prediction is kept because the
  correction is the interesting part.** It read: *"it is a theorem rather than a formality — the
  classical argument makes the diagonal `A ⟶ A ×_B A` an isomorphism and needs the fibre
  product."* The fibre product is what it needed and is now
  `ComplexAnalytic.AnalyticSpace.baseChange`, at a cospan whose legs are both `i`; **the diagonal
  is not built and no isomorphism is proved**, because the two projections being equal — which is
  what `CategoryTheory.cancel_mono` gives directly — already reads off as injectivity at a point
  of the carrier. At `c48bf8a`,
  **`#synth CategoryTheory.Limits.HasPullbacks ComplexAnalytic.AnalyticSpace` fails** — a record
  pinned to that commit and elaborated rather than grepped, not a claim about what the tree will
  hold, and it is still not what supplies the fibre product above. The monomorphism results this
  file could have reached for run the other way, from an immersion to a monomorphism:
  `ComplexAnalytic.AnalyticSpace.mono_ofRestrict`
  (`Oka/AnalyticSpace/OpenSubspace.lean`) makes the inclusion of an open subspace a monomorphism,
  and `ComplexAnalytic.IsCutOutBy.mono` together with
  `ComplexAnalytic.AnalyticSpace.mono_of_isCutOutBy` (`Oka/AnalyticSpace/Basic.lean`) do the same
  for a morphism that cuts out a subspace.
* **Any claim that `[T2Space B.left]` can be dropped.** It is the cost of
  `ComplexAnalytic.AnalyticSpace.isFiniteEtale_of_comp`, which is where a morphism of covers gets
  its own finite étale property from, and `Oka/AnalyticSpace/Finite.lean` argues in its module
  docstring that a separation axiom on the middle space is what the closed half of the finite rung
  actually needs.
* **The isomorphism onto the clopen part, as a named declaration.** It is built inside the proof
  below and is not exposed. Exposing it would put the source of
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isFiniteEtale_left` — a theorem and not an
  instance — into the *type* of a declaration, since the clopen part is
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.restrictClopen` at an open built from a
  local-isomorphism hypothesis. A caller that wants it should ask for it here rather than unfold
  this proof.
-/

open CategoryTheory

universe u

namespace ComplexAnalytic.AnalyticSpace

/-! ### The underlying morphism of a morphism of covers -/

/-- **The underlying morphism of a morphism of covers is finite étale**, when the total space of
the target cover is Hausdorff.

This is `ComplexAnalytic.AnalyticSpace.isFiniteEtale_of_comp` at the triangle a morphism of covers
commutes: `f.left ≫ B.hom` is `A.hom`, which is finite étale because `A` is an object of the
category, and `B.hom` is a local isomorphism for the same reason about `B`. **The separation
axiom is that cancellation's and none of it is spent here** — a morphism of covers is finite étale
*because the target cover's total space is separated*, not because the category asks it to be, and
`Oka/AnalyticSpace/FiniteEtaleOver.lean`'s module docstring makes the same point from the side of
what that file does not assume.

**The named arguments `(X := B.left)` on the two `haveI`s are load-bearing** and the reason is
recorded at `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.degree_eq_mul`, whose proof opens by
running this one inline: `f.left` has target `B.left` on the nose, while the instance an object
carries in its `prop` field has `(CategoryTheory.Functor.id _).obj B.left` there, and the two are
`rfl`-equal with different discrimination-tree keys. taxis #1681 is the filing about that seam.

**`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.degree_eq_mul` and
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isIso_of_bijective_fiberMap` cannot cite this**,
since they are in the file this one imports; extracting their copies would have to happen there.
That pair is `Oka/AnalyticSpace/FiniteEtaleOver.lean`'s own reading and not this file's: the
docstring above the second of them already says *"the class comes back from
`…isFiniteEtale_of_comp` at the triangle, which is the same opening `…degree_eq_mul` above has"*.
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.degree_left_eq_one` is not one of them and has no
copy to extract — its proof is a single term handing its hypotheses to `degree_eq_mul`. -/
theorem FiniteEtaleOver.isFiniteEtale_left {X : AnalyticSpace.{u}} {A B : FiniteEtaleOver.{u} X}
    (f : A ⟶ B) [T2Space (B.left : Type u)] : IsFiniteEtale f.left := by
  have hw : f.left ≫ B.hom = A.hom := MorphismProperty.Over.w f
  haveI : IsFiniteEtale (X := B.left) B.hom := B.prop
  haveI : IsLocalIso (X := B.left) B.hom := IsFiniteEtale.isLocalIso
  haveI : IsFiniteEtale (f.left ≫ B.hom) := hw ▸ (A.prop : IsFiniteEtale A.hom)
  exact isFiniteEtale_of_comp f.left B.hom

/-! ### The direct summand at an injective morphism of covers -/

/-- **The image of a morphism of covers is clopen**, when the total space of the target cover is
Hausdorff.

`ComplexAnalytic.AnalyticSpace.isClopen_range_of_isLocalIso_of_isFinite` at `i.left`, whose two
instances come from `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isFiniteEtale_left`. **That
statement asks no separation axiom of anything** — it is open because a local isomorphism is an
open map and closed because a finite morphism is a closed map — so the `[T2Space B.left]` here is
spent entirely on the cancellation above and not on the topology of the image. -/
theorem FiniteEtaleOver.isClopen_range_left {X : AnalyticSpace.{u}} {A B : FiniteEtaleOver.{u} X}
    (i : A ⟶ B) [T2Space (B.left : Type u)] :
    IsClopen (Set.range (i.left.toLRSHom.base : A.left → B.left)) :=
  haveI : IsFiniteEtale i.left := FiniteEtaleOver.isFiniteEtale_left i
  isClopen_range_of_isLocalIso_of_isFinite i.left

/-- **The image of a morphism of covers, as an open subset of the target's total space.**

`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.restrictClopen` and its complement are indexed by a
`TopologicalSpace.Opens` together with a proof that it is closed, so the image has to be presented
in that shape before it can be handed to them. The underlying set is `Set.range` on the nose, which
is what makes `ComplexAnalytic.AnalyticSpace.liftRestrict` apply below at `subset_rfl`. -/
def FiniteEtaleOver.rangeOpens {X : AnalyticSpace.{u}} {A B : FiniteEtaleOver.{u} X}
    (i : A ⟶ B) [T2Space (B.left : Type u)] : B.left.Opens :=
  ⟨Set.range (i.left.toLRSHom.base : A.left → B.left), (FiniteEtaleOver.isClopen_range_left i).2⟩

/-- **And it is closed**, which is the second argument
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.restrictClopenCompl` takes. -/
theorem FiniteEtaleOver.isClosed_rangeOpens {X : AnalyticSpace.{u}} {A B : FiniteEtaleOver.{u} X}
    (i : A ⟶ B) [T2Space (B.left : Type u)] :
    IsClosed ((FiniteEtaleOver.rangeOpens i : B.left.Opens) : Set B.left) :=
  (FiniteEtaleOver.isClopen_range_left i).1

/-- **The direct summand complementary to a morphism of covers**, named.

`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.restrictClopenCompl` at the image of `i`. **It is
defined at every morphism of covers and asks no injectivity**, because injectivity is what makes
the cofan below a colimit and not what makes this object exist;
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isColimitBinaryCofanDirectSummandCompl` is where it
is spent.

**Naming it is the whole point of this declaration and it is not a convenience.**
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.inducesIsoOnDirectSummand_of_injective` below
quantifies its witness existentially, and a caller that needs a *property* of the summand — that it
is separated over the base, say, which
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isSeparatedMap_restrictClopenCompl`
(`Oka/AnalyticSpace/SeparatedOver.lean`) gives of exactly this object — cannot reach it through the
existential. **That is the obstruction
`Oka/AnalyticSpace/SeparatedFiniteEtale.lean`'s `## What is not here` states in terms**, and this
declaration, `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.directSummandComplι` and
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isColimitBinaryCofanDirectSummandCompl` are what
close it. -/
noncomputable def FiniteEtaleOver.directSummandCompl {X : AnalyticSpace.{u}}
    {A B : FiniteEtaleOver.{u} X} (i : A ⟶ B) [T2Space (B.left : Type u)] :
    FiniteEtaleOver.{u} X :=
  B.restrictClopenCompl (FiniteEtaleOver.rangeOpens i) (FiniteEtaleOver.isClosed_rangeOpens i)

/-- **Its inclusion into the target**,
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.restrictClopenComplι` at the same open. It carries
no content and exists so that the colimit below can name the second injection of its cofan. -/
noncomputable def FiniteEtaleOver.directSummandComplι {X : AnalyticSpace.{u}}
    {A B : FiniteEtaleOver.{u} X} (i : A ⟶ B) [T2Space (B.left : Type u)] :
    FiniteEtaleOver.directSummandCompl i ⟶ B :=
  B.restrictClopenComplι (FiniteEtaleOver.rangeOpens i) (FiniteEtaleOver.isClosed_rangeOpens i)

/-- **The target is the coproduct of the source and that summand**, at an injective morphism of
covers and with both of them named.

**`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.inducesIsoOnDirectSummand_of_injective` below is
the existential closure of this**, and the proof is that theorem's former tactic block with **two
hunks** changed and the **twenty-four** lines between them unaltered: the two lines that introduce
`U` and `hU`, which now cite the two declarations above instead of spelling the image out, and the
closing five lines, which become six. It is a `def` and not a `theorem` because
`CategoryTheory.Limits.IsColimit` is data — it carries the descent map — and a consumer that has to
transport it along a functor, as `Oka/AnalyticSpace/SeparatedDirectSummand.lean` does, needs the
witness and not its `Nonempty`.

**The closing hunk is the one thing naming the witness cost, and the reason is worth recording.**
The former body closed with `rw [← hei]` on a goal whose second injection was written out as
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.restrictClopenComplι` at the image. Here that
injection is `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.directSummandComplι` **at `i` itself**,
so rewriting `i` backwards inside the goal rewrites it there too and the result is a cofan whose
second leg is indexed by `e ≫ …restrictClopenι` rather than by `i`. Rewriting **forwards in the
hypothesis** — `rw [hei] at key` — moves only the occurrence that has to move, because the pattern
being rewritten does not occur inside the second leg at all.

**The proof, in the order the steps are taken.**
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isClopen_range_left` makes the image clopen.
`ComplexAnalytic.AnalyticSpace.liftRestrict` factors `i.left` through the open subspace at that
image, and the factor is a local isomorphism by
`ComplexAnalytic.AnalyticSpace.isLocalIso_of_comp` and a bijection because `hinj` gives the
injective half and the image is the target by construction, so
`ComplexAnalytic.AnalyticSpace.isIso_of_isLocalIso_of_bijective` makes it an isomorphism.
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isIso_of_isIso_left` reads that as an isomorphism
of covers, and
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isColimitBinaryCofanRestrictClopen` together with
`CategoryTheory.Limits.BinaryCofan.isColimitCompLeftIso` transports the decomposition along it.

**`hinj` is stated about `i.left.toLRSHom.base` and not about a fibre map**, because that is the
map the topology of the argument is about: `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fiber`
enters nowhere below and no fibre is counted.

**The last step is an `exact` and not a `simp only`, and that is a measured choice rather than a
style one.** `CategoryTheory.Limits.BinaryCofan.isColimitCompLeftIso` returns its conclusion at
`(B.binaryCofanRestrictClopen U hU).inl` and `.inr`, which are the two inclusions by definition;
a `simp only` naming
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.binaryCofanRestrictClopen` closes the gap and
**generates that definition's equation lemma, which then lands in
`scripts/DumpOkaDecls.lean`'s output as a row this file did not write**. `exact` crosses the same
gap at default transparency and plants nothing, so this proof's contribution to that dump is the
declarations it states and no more. -/
noncomputable def FiniteEtaleOver.isColimitBinaryCofanDirectSummandCompl {X : AnalyticSpace.{u}}
    {A B : FiniteEtaleOver.{u} X} (i : A ⟶ B) [T2Space (B.left : Type u)]
    (hinj : Function.Injective (i.left.toLRSHom.base : A.left → B.left)) :
    Limits.IsColimit
      (Limits.BinaryCofan.mk i (FiniteEtaleOver.directSummandComplι i)) := by
  haveI hfe : IsFiniteEtale i.left := FiniteEtaleOver.isFiniteEtale_left i
  set U : B.left.Opens := FiniteEtaleOver.rangeOpens i with hUdef
  have hU : IsClosed (U : Set B.left) := FiniteEtaleOver.isClosed_rangeOpens i
  have hsub : Set.range (i.left.toLRSHom.base : A.left → B.left) ⊆ (U : Set B.left) := subset_rfl
  set j : A.left ⟶ B.left.restrict U := liftRestrict i.left U hsub with hjdef
  have hfac : j ≫ B.left.ofRestrict U = i.left := liftRestrict_fac _ _ _
  have hbase : ∀ a : A.left, (B.left.ofRestrict U).toLRSHom.base (j.toLRSHom.base a)
      = i.left.toLRSHom.base a := fun a =>
    congrArg (fun m : A.left ⟶ B.left => m.toLRSHom.base a) hfac
  have hbij : Function.Bijective (j.toLRSHom.base : A.left → B.left.restrict U) := by
    constructor
    · intro a a' h
      exact hinj (by rw [← hbase a, ← hbase a', h])
    · intro y
      obtain ⟨a, ha⟩ : y.1 ∈ Set.range (i.left.toLRSHom.base : A.left → B.left) := y.2
      exact ⟨a, Subtype.ext (by rw [← hbase a] at ha; exact ha)⟩
  haveI : IsLocalIso (j ≫ B.left.ofRestrict U) := hfac ▸ hfe.isLocalIso
  haveI : IsLocalIso j := isLocalIso_of_comp j (B.left.ofRestrict U)
  haveI : IsIso j := isIso_of_isLocalIso_of_bijective j hbij
  let e : A ⟶ B.restrictClopen U hU :=
    MorphismProperty.Over.homMk j (by
      have h1 : j ≫ B.left.ofRestrict U ≫ B.hom = A.hom := by
        rw [← Category.assoc, hfac]; exact MorphismProperty.Over.w i
      exact h1)
  haveI : IsIso e := FiniteEtaleOver.isIso_of_isIso_left e (by simpa [e] using ‹IsIso j›)
  have hei : e ≫ B.restrictClopenι U hU = i :=
    MorphismProperty.Over.Hom.ext (by simpa [e] using hfac)
  have key : Limits.IsColimit (Limits.BinaryCofan.mk (e ≫ B.restrictClopenι U hU)
      (FiniteEtaleOver.directSummandComplι i)) :=
    Limits.BinaryCofan.isColimitCompLeftIso
      (B.binaryCofanRestrictClopen U hU) e (B.isColimitBinaryCofanRestrictClopen U hU)
  rw [hei] at key
  exact key


/-- **A morphism of covers that is injective on points exhibits its source as a direct summand of
its target**: there is a cover `Z` and a morphism `Z ⟶ B` whose binary cofan with `i` is a
colimit.

**This is the shape the `monoInducesIsoOnDirectSummand` field of
`Mathlib/CategoryTheory/Galois/Basic.lean`'s pre-Galois-category class is written in, and it is not
that field.** That field asks the same of every monomorphism and under
no hypothesis at all; this asks for `[T2Space B.left]` and for `hinj`. The module docstring's
`## What is not here` says what stands between the two and why nothing below derives either of
them from `Mono i`.

**The whole of the content is
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isColimitBinaryCofanDirectSummandCompl` above, and
this is its existential closure.** The statement is unchanged — it is what the field's shape asks
for and what the two modules of `Oka/` that apply it cite — but the witness it hides is now
available under a name, which is what a caller needing a property of the summand has to have.

**The complement is
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.restrictClopenCompl` at the image**, as it always
was; `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.directSummandCompl` is that composite under one
name and its docstring says why the name is load-bearing.

**This proof was the block now above until 2026-09-12**, when it was moved out under a name; the
statement of this theorem is character for character what it was, which is the measurement that
says the modules that apply it are untouched by the move. **In the comment-stripped code of `Oka/`
the name occurs in three modules**: this one, which declares it, and
`Oka/AnalyticSpace/MonoDirectSummand.lean` and `Oka/AnalyticSpace/SeparatedFiniteEtale.lean`, which
apply it. -/
theorem FiniteEtaleOver.inducesIsoOnDirectSummand_of_injective {X : AnalyticSpace.{u}}
    {A B : FiniteEtaleOver.{u} X} (i : A ⟶ B) [T2Space (B.left : Type u)]
    (hinj : Function.Injective (i.left.toLRSHom.base : A.left → B.left)) :
    ∃ (Z : FiniteEtaleOver.{u} X) (u : Z ⟶ B),
      Nonempty (Limits.IsColimit (Limits.BinaryCofan.mk i u)) :=
  ⟨FiniteEtaleOver.directSummandCompl i, FiniteEtaleOver.directSummandComplι i,
    ⟨FiniteEtaleOver.isColimitBinaryCofanDirectSummandCompl i hinj⟩⟩

/-! ### Conservativity, with nothing asked of the target cover beyond Hausdorffness -/

/-- **A morphism of covers whose fibre map at one point of the base is bijective is an
isomorphism** — over a preconnected base, with both total spaces Hausdorff and **nothing asked of
either of them beyond that**.

**This is `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isIso_of_bijective_fiberMap` with
`[PreconnectedSpace B.left]` gone, and the suffix names what is left**: Hausdorffness of the two
total spaces, which is the whole of what this statement asks of the two covers. That hypothesis was
the *route's* and not the statement's — that proof reads the degree of `f.left` off
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.degree_eq_mul`, and a degree is one number only over
a connected space — and the route here never forms it.

**It is in this file and not in that one because the summand is**, which is the same reason the
paragraph opening *`…degree_eq_mul` and `…isIso_of_bijective_fiberMap` cannot cite this* gives
above: `Oka/AnalyticSpace/FiniteEtaleOver.lean` is imported by this module and cannot cite
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.directSummandCompl`. **The direction is one line of
this file and not a reading of it** — `import Oka.AnalyticSpace.FiniteEtaleOver` is the only
`Oka` import line this module has, so nothing of this file is in that file's closure.
**Both statements stand**: the
one above is the one a caller inside
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isPreconnectedT2` already has and the two
conservativity instances of that file are stated from it, and this one is what a caller outside
that subcategory needs.

**Two halves, and neither forms a degree of `f.left`.** *Surjectivity*: the image of `f.left` is
clopen by `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isClopen_range_left` above, which is where
`[T2Space B.left]` goes, so `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.directSummandCompl` is
an object of the category; its fibre over `x` is empty because the fibre map there is onto, and
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isEmpty_left_of_isEmpty_fiber` — which asks
`[PreconnectedSpace X]` and nothing of the cover — empties the whole of it. *Injectivity*: a
surjection of total spaces makes **every** fibre map onto, by
`CategoryTheory.MorphismProperty.Over.w` read at a preimage; each fibre is finite and
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.card_fiber` reads the two cardinalities as the two
degrees, which the hypothesis at `x` makes equal; and a surjection between finite types of equal
`Nat.card` is injective, which is `Nat.bijective_iff_surjective_and_card`. Two points with one
image lie over one point of the base, so injectivity of that one fibre map is injectivity of
`f.left`.

**The empty case is not a case here**, where the proof above splits on it: nothing in the route
asks for a point, so a cover with empty total space is carried by the same two steps as any other.

**Neither membership in the complement is crossed by a `simp` naming
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.rangeOpens`, and that is the same measured choice
the paragraph above makes for `isColimitBinaryCofanDirectSummandCompl`.** Membership in that open
is the range condition definitionally, so a type ascription crosses it; `simpa [rangeOpens]` also
crosses it and **generates that definition's equation lemma**, which then stands in
`scripts/DumpOkaDecls.lean`'s output as a row this file did not write — measured, not expected:
the draft that spelled it that way reported **one** extra row,
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.rangeOpens.eq_1`, and `Δdump` for the push that
adds this theorem was `+4` against three declarations. **Both crossings here are ascriptions**, so
that push's `Δdump` is the three declarations it states and no more.

**Where the hypotheses go.** `[T2Space B.left]` is spent three times, on
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isFiniteEtale_left` at `f.left`, on the image being
clopen and on `card_fiber` of the target; `[T2Space A.left]` once, on `card_fiber` of the source;
and `[PreconnectedSpace X]` twice, on emptying the complementary summand and on `card_fiber` at
each point of the base. **Neither total space is asked to be preconnected.** -/
theorem FiniteEtaleOver.isIso_of_bijective_fiberMap_of_t2 {X : AnalyticSpace.{u}}
    {A B : FiniteEtaleOver.{u} X} (f : A ⟶ B)
    [T2Space (A.left : Type u)] [T2Space (B.left : Type u)]
    [PreconnectedSpace (X : Type u)] (x : X)
    (hf : Function.Bijective (FiniteEtaleOver.fiberMap.{u} x f)) : IsIso f := by
  have hw : f.left ≫ B.hom = A.hom := MorphismProperty.Over.w f
  haveI : IsFiniteEtale f.left := FiniteEtaleOver.isFiniteEtale_left f
  refine FiniteEtaleOver.isIso_of_isIso_left f ?_
  have hCempty : IsEmpty (FiniteEtaleOver.fiber.{u} x (FiniteEtaleOver.directSummandCompl f)) := by
    constructor
    rintro ⟨b, hb⟩
    have hx : (B.hom.toLRSHom.base : B.left → X) b.1 = x := hb
    obtain ⟨a, ha⟩ := hf.2 ⟨b.1, hx⟩
    have hmem : (b.1 : B.left) ∈ Set.range (f.left.toLRSHom.base : A.left → B.left) :=
      ⟨a.1, congrArg Subtype.val ha⟩
    exact (b.2 : (b.1 : B.left) ∈ (FiniteEtaleOver.rangeOpens f : Set B.left)ᶜ) hmem
  have hCleft := FiniteEtaleOver.isEmpty_left_of_isEmpty_fiber.{u}
    (FiniteEtaleOver.directSummandCompl f) x hCempty
  have hsurj : Function.Surjective (f.left.toLRSHom.base : A.left → B.left) := by
    intro b
    by_contra hb
    exact hCleft.elim
      (⟨b, fun hmem ↦ hb (hmem : (b : B.left) ∈
          Set.range (f.left.toLRSHom.base : A.left → B.left))⟩ :
        ((FiniteEtaleOver.directSummandCompl f).left : Type u))
  have hAB : ∀ a : (A.left : Type u),
      (B.hom.toLRSHom.base : B.left → X) ((f.left.toLRSHom.base : A.left → B.left) a)
        = (A.hom.toLRSHom.base : A.left → X) a :=
    fun a ↦ congrArg (fun g : A.left ⟶ X ↦ (g.toLRSHom.base : A.left → X) a) hw
  have hdeg : A.degree = B.degree := by
    rw [← FiniteEtaleOver.card_fiber A x, ← FiniteEtaleOver.card_fiber B x]
    exact Nat.card_eq_of_bijective _ hf
  have hinj : Function.Injective (f.left.toLRSHom.base : A.left → B.left) := by
    intro a₁ a₂ h
    set y : X := (A.hom.toLRSHom.base : A.left → X) a₁ with hy
    have hy₂ : (A.hom.toLRSHom.base : A.left → X) a₂ = y := by
      rw [← hAB a₂, ← h, hAB a₁]
    have hfibsurj : Function.Surjective (FiniteEtaleOver.fiberMap.{u} y f) := by
      rintro ⟨b, hb⟩
      obtain ⟨a, ha⟩ := hsurj b
      refine ⟨⟨a, ?_⟩, Subtype.ext ha⟩
      change (A.hom.toLRSHom.base : A.left → X) a = y
      rw [← hAB a, ha]
      exact hb
    have hcard : Nat.card (FiniteEtaleOver.fiber.{u} y A)
        = Nat.card (FiniteEtaleOver.fiber.{u} y B) := by
      rw [FiniteEtaleOver.card_fiber A y, FiniteEtaleOver.card_fiber B y, hdeg]
    have hbij : Function.Bijective (FiniteEtaleOver.fiberMap.{u} y f) :=
      (Nat.bijective_iff_surjective_and_card _).2 ⟨hfibsurj, hcard⟩
    exact congrArg Subtype.val
      (hbij.1 (a₁ := ⟨a₁, rfl⟩) (a₂ := ⟨a₂, hy₂⟩) (Subtype.ext h))
  exact isIso_of_isLocalIso_of_bijective f.left ⟨hinj, hsurj⟩

end ComplexAnalytic.AnalyticSpace
