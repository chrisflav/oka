/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.AnalyticSpace.EmptyBase

/-!
# Connected as an object and connected as a space are the same condition

`CategoryTheory.PreGaloisCategory.IsConnected` is a condition on an **object of a category** — not
initial, and every monomorphism into it either initial or an isomorphism — and `ConnectedSpace` is
a condition on a **topological space**. For a cover `A` separated over `X`, *`A` is connected* can
mean either, and until this file **no declaration of this repository stated an implication in
either direction**. `Oka/AnalyticSpace/FundamentalGroup.lean`'s `## What is not here` records that
absence in a bullet pinned to the commit that adds that file, and this file is what narrows it:
over a Hausdorff preconnected base the two conditions **agree**, so every piece of the
decomposition theorem there has **connected total space**. **That is one step short of the pieces
being the topological connected components of that total space**, which is a further statement;
`## What is not here` prices the three steps between and says which of their instruments are
already in the tree. taxis #2082 is the filing.

**That sentence ended *and is proved nowhere in this repository*, in the present tense, until
2026-09-20**, when `Oka/AnalyticSpace/ConnectedComponents.lean` proved it as
`…SeparatedFiniteEtaleOver.exists_connectedComponent_decomposition`; the dated record is here and
the bullet below carries what the pricing got wrong. **Nothing else in this file moves with it**:
the statements here are about an object and the one there is about a space, and that module
imports this one rather than the other way round.

**The base hypotheses are exactly the ones under which the fibre functor is a fibre functor** —
`[T2Space X]` and `[PreconnectedSpace X]`, which is what
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.fintypeFiberFunctor_isFiberFunctor` asks —
and `[Nonempty X]` is **not** among them in either direction; the paragraph *The empty base is
inside both directions and not excluded from them* below says how the second direction survives
without it.

## Main definitions

- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.restrictClopen`: **a clopen part of a
  separated cover's total space is again a separated cover of the base.**
- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.restrictClopenι`: **its inclusion**, as a
  morphism of separated covers.

## Main results

- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.mono_restrictClopenι`: **that inclusion
  is a monomorphism**, which is what makes a clopen part a legal test object for the categorical
  condition.
- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.surjective_base_left_of_isIso`: **an
  isomorphism of separated covers is surjective on total spaces.**
- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.isConnected_of_connectedSpace`: **a cover
  whose total space is connected is connected as an object.**
- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.connectedSpace_of_isConnected`: **and
  conversely**, which is the direction taxis #2082 §3 calls the trap and prices at the clopen
  restriction above.
- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.isConnected_iff_connectedSpace`: **the
  two together**, as the equivalence.
- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.isPreconnected_of_isConnected`: **a
  connected object lies in the preconnected full subcategory of
  `Oka/AnalyticSpace/SeparatedFiberFunctor.lean`**, which is the one statement here relating the
  categorical condition to an object property this repository already had. **The converse is not
  proved and is not claimed**; `## What is not here` says why.

## Neither direction is a rewriting, and where each hypothesis goes

**The plausible direction spends the clopenness of an image and nothing about the base beyond the
two hypotheses.** A monomorphism of separated covers is injective on total spaces
(`…SeparatedFiniteEtaleOver.injective_base_left_of_mono`) and its image is clopen
(`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isClopen_range_left`), so a clopen nonempty subset
of a connected space being everything makes the morphism bijective on total spaces, hence bijective
on the fibre over any point, hence an isomorphism of covers by
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isIso_of_bijective_fiberMap_of_t2`, and an
isomorphism of separated covers because `…SeparatedFiniteEtaleOver.toFiniteEtaleOver` is fully
faithful and so reflects isomorphisms. **Non-initiality is the other half and it is the one that
needs the fibre**: `CategoryTheory.PreGaloisCategory.initial_iff_fiber_empty` turns it into
emptiness of a fibre, and the point of the base at which the fibre is read is **the image of a
point of the total space**, which a connected space has. That is why the statement takes no
basepoint.

**Where the two base hypotheses go, and neither goes to one place.** `[T2Space X]` is asked by
`…SeparatedFiniteEtaleOver.injective_base_left_of_mono` directly, and again by
`…FiniteEtaleOver.isClopen_range_left`, which wants Hausdorffness of the target's **total** space —
carried over a Hausdorff base by `…SeparatedFiniteEtaleOver.t2Space_left`. `[PreconnectedSpace X]`
is asked by `…FiniteEtaleOver.isIso_of_bijective_fiberMap_of_t2`, and again by
`…SeparatedFiniteEtaleOver.fintypeFiberFunctor_isFiberFunctor`, without which the Mathlib lemma
about initiality has no fibre functor to be read at. **So neither hypothesis has a single site**,
and a delivery that removed one of the two uses would not have removed the hypothesis.

**The converse needs a clopen part of the total space to be a cover again, and that is a
construction and not a reading.** taxis #2082 §3 is right that this is the harder direction. What
discharges it is already in the tree: `ComplexAnalytic.AnalyticSpace.isFiniteEtale_ofRestrict_comp`
makes the restriction finite étale and
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isSeparatedMap_restrictClopen` makes it separated,
so `…SeparatedFiniteEtaleOver.restrictClopen` is an object of **this** category and not only of the
ambient one. The inclusion is a monomorphism because `ComplexAnalytic.AnalyticSpace.ofRestrict` is
one and a morphism of this category is determined by its underlying morphism, and a nonempty clopen
part is a non-initial subobject, so `CategoryTheory.PreGaloisCategory.IsConnected` forces it to be
everything. **`Mathlib/Topology/Connected/Clopen.lean`'s `connectedSpace_iff_clopen` is the shape
the conclusion is assembled in**, its nonemptiness half coming from
`CategoryTheory.PreGaloisCategory.nonempty_fiber_of_isConnected`.

**`…SeparatedFiniteEtaleOver.restrictClopen` is built from
`ComplexAnalytic.AnalyticSpace.ofRestrict` directly and not from
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.restrictClopen`, and that is a measurement and not
a preference.** The object whose structure morphism is the ambient
construction's `hom` elaborates, at the default `maxHeartbeats`, into a
`(deterministic) timeout at isDefEq`; the same object written as
`CategoryTheory.MorphismProperty.Over.mk` at `A.left.ofRestrict U ≫ A.hom` — which is the ambient
construction's structure morphism unfolded by one step — elaborates in seconds. Both were run.
The separatedness half is still the ambient lemma, read at the functor image of `A`, because that
statement is about the composite and not about the packaging.

## The empty base is inside both directions and not excluded from them

`[Nonempty X]` appears in neither statement, and only one of the two directions had to argue for
that. The first takes its point of the base from a point of the total space, which
`ConnectedSpace` supplies. The second cannot, and splits: over a **nonempty** base it reads the
fibre at any point, and over an **empty** one every object is initial —
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.isoIdOfIsEmpty` and
`…SeparatedFiniteEtaleOver.isInitialIdOfIsEmpty` of `Oka/AnalyticSpace/EmptyBase.lean` are the two
halves — so `CategoryTheory.PreGaloisCategory.IsConnected` is false of every object and the
implication is vacuous. **That is the whole of what this file's one import buys**, and it is the
reason the import is `Oka/AnalyticSpace/EmptyBase.lean` and not
`Oka/AnalyticSpace/GaloisCategory.lean`, which is the module the mathematics otherwise reads from.

## What the import costs, measured in the environment and not by a scan

At the commit this file is cut from, `import Oka` brings **5533** modules; at the commit that adds
it, **5534**. **The cost is one module and the one is this file**: by a set difference over
`Lean.Environment.allImportedModuleNames` in a `run_cmd`, the only names in the second closure and
not the first are `Oka` itself and `Oka.AnalyticSpace.ConnectedCover`, so **no Mathlib module
enters and the marginal Mathlib cost is zero**. This file's only `import` line names
`Oka/AnalyticSpace/EmptyBase.lean`, which `Oka.lean` already imported, and every Mathlib name used
below — `CategoryTheory.PreGaloisCategory.IsConnected` and the three lemmas about fibres and
initiality, and `connectedSpace_iff_clopen` — is in that module's closure already.

**A marginal import cost is a figure about the importer at a commit**, so both ends are dated here
rather than written in the present tense, exactly as `Oka/AnalyticSpace/GaloisCategory.lean` and
`Oka/AnalyticSpace/FundamentalGroup.lean` do for their own.

**What the census script returns, at the commit this file is cut from and at the commit that adds
it.** `scripts/check_docstring_names.py` goes **17680 → 17761** backticked names (4314 → 4327
distinct) and **229 → 273** elided citations (138 → 150), **0 unresolved at both ends**, **6**
resolving under more than one namespace at both, and **232** dotless at both, against a
`scripts/DumpEnvNames.lean` dump that moves **338216 → 338225** — **332537 → 332545** declarations
and **5679 → 5680** modules, which is this module's eight declarations and this module.

**Eight declarations, and eight is the whole of the module.** `scripts/DumpOkaDecls.lean` writes
**8** rows at `Oka.AnalyticSpace.ConnectedCover` at the commit that adds this file — no equation
lemma, no match lemma, no congruence lemma — and the dump total moves **4949 → 4957**.

## What is not here

* **Nothing about a base that is not Hausdorff, or not preconnected.**
  `CategoryTheory.PreGaloisCategory.IsConnected` is defined at any category and so is a meaningful
  condition on an object of `…SeparatedFiniteEtaleOver X` for any `X`; **both statements below ask
  both hypotheses and neither is shown to be needed.** What is true is that both proofs spend
  both — the paragraph *Where the two base hypotheses go* says where — and that without them the
  fibre functor is not known to be one, which is what the three Mathlib lemmas named above
  consume.
* **The converse of `…SeparatedFiniteEtaleOver.isPreconnected_of_isConnected` is neither proved
  nor claimed.** `…SeparatedFiniteEtaleOver.isPreconnected` is `PreconnectedSpace` of the total
  space, which does **not** exclude an object whose total space is empty; such an object is
  initial and so is never `CategoryTheory.PreGaloisCategory.IsConnected`, so the converse looks
  false. **That is an argument and not a run, and a census is what says so.** At the commit that
  adds this file the token `IsInitial` occurs in the comment-stripped code of **two** modules
  under `Oka/` — `Oka/AnalyticSpace/EmptyBase.lean` and this one — in **three** places, and only
  one of the three is in a *statement*:
  `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.isInitialIdOfIsEmpty`'s, which identifies
  an initial object **only over an empty base**; this file's is a `have` inside a proof. So no
  object with empty total space over a nonempty base is exhibited anywhere, the converse has no
  witness to be refuted by, and it is left open rather than settled.
* **No comparison with the topologist's fundamental group.**
  `Oka/AnalyticSpace/FundamentalGroup.lean`'s `## What is not here` records that absence and
  nothing here bears on it: this file relates two notions of *connected*, not two groups.
* **Nothing at `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver`.** The ambient covers carry no
  `CategoryTheory.PreGaloisCategory` instance in this repository —
  `Oka/AnalyticSpace/GaloisCategory.lean` gives the reason — so the categorical condition has no
  fibre-functor theory there and neither proof below transports. **Both statements are at the
  separated covers and only there.**
* **This bullet opened *Nothing that makes the pieces of the decomposition the topological
  connected components of the total space* until 2026-09-20**, when
  `…SeparatedFiniteEtaleOver.exists_connectedComponent_decomposition`
  (`Oka/AnalyticSpace/ConnectedComponents.lean`, taxis #2091) made that statement; **the three
  steps below are left as they stood, because they are what the absence was priced at and two of
  the judgements in them were repaired by the push that closed it** — the paragraph after the
  census says which. What is proved **here** is
  `…SeparatedFiniteEtaleOver.isConnected_iff_connectedSpace` read at each piece: *every
  `f i` has connected total space*. `Oka/AnalyticSpace/FundamentalGroup.lean`'s
  `…SeparatedFiniteEtaleOver.exists_isConnected_decomposition` gives an isomorphism `∐ f ≅ A` **in
  the category** and nothing about `A.left` as a space, so *the pieces are the components* needs
  all three of:
  1. **`∐ f ≅ …SeparatedFiniteEtaleOver.sigma f`.**
     `…SeparatedFiniteEtaleOver.isColimitCofanSigma` and
     `CategoryTheory.Limits.IsColimit.coconePointUniqueUpToIso` would close it **at a matching
     index universe, and the universes do not match**: `…SeparatedFiniteEtaleOver.sigma` takes
     `{ι : Type u}` and that theorem's `ι` is `Type`, so `SeparatedFiniteEtaleOver.sigma f` at it
     is *Application type mismatch: The argument `f` has type `ι → X.SeparatedFiniteEtaleOver` but
     is expected to have type `?m.4 → SeparatedFiniteEtaleOver ?m.3`*, which is a run of mine and
     not a reading; with `ι : Type u` the same term elaborates. **The crossing is the one
     `…SeparatedFiniteEtaleOver.hasFiniteCoproducts` already makes** —
     `CategoryTheory.Discrete.equivalence` at `Equiv.ulift`, there for `Fin n` — and it would have
     to be made again for an arbitrary finite `ι`. **This is the expensive step of the three.**
  2. **The total space of `…SeparatedFiniteEtaleOver.sigma f` is the topological disjoint union of
     the `(f i).left`.** Every instrument for this is in the tree and only the conclusion is
     missing: `ComplexAnalytic.AnalyticSpace.sigma_toLocallyRingedSpace` is `rfl`, so the carrier
     is the coproduct's on the nose, and there
     `AlgebraicGeometry.LocallyRingedSpace.sigmaι_isOpenImmersion`,
     `AlgebraicGeometry.LocallyRingedSpace.disjoint_range_sigmaι` and
     `AlgebraicGeometry.LocallyRingedSpace.exists_sigma_ι_base_eq` are the open embedding, the
     disjointness and the covering, with
     `AlgebraicGeometry.LocallyRingedSpace.preservesColimitsOfShape_discrete_forgetToTop` saying
     the same thing in one line at the level of spaces and
     `ComplexAnalytic.AnalyticSpace.isClopen_range_sigmaι_base` carrying the clopenness one level
     up. **What no declaration does is conclude from them**, and a `Homeomorph` onto
     `Σ i, (f i).left` is the shape that conclusion would take.
  3. **An isomorphism of this category is a homeomorphism on total spaces.**
     `AlgebraicGeometry.LocallyRingedSpace.homeoOfIso`
     (`Oka/Geometry/RingedSpace/LocallyRingedSpace.lean`) is that statement one level down, so this
     step is the forgetful functor's image of the isomorphism and one application of it — **the
     cheap step of the three**. `…SeparatedFiniteEtaleOver.surjective_base_left_of_isIso` above is
     the surjectivity half only and `ComplexAnalytic.AnalyticSpace.bijective_base_of_isIso` the
     bijectivity, and **a bijection of spaces does not carry connected components**, which is why
     neither is enough.

  **The census that says this is an absence and not an oversight**: at the commit that adds this
  file the token `connectedComponent` occurs **0 times** in the comment-stripped code of the tree —
  so the notion the reading above concludes about is in **no** statement and **no** proof of this
  repository — and `≃ₜ` occurs **12** times in **10** files, **none of them about the total space of
  an object of this category**: they are fibres, charts of `ℂ^n`, a cylinder, a sheet, and the
  locally ringed space statement of step 3.

  **What the push that closed this absence found, recorded here because this bullet priced it
  wrongly.** *This is the expensive step of the three* was said of step 1 and is the judgement
  that was wrong: the crossing is four lines —
  `CategoryTheory.Limits.HasColimit.isoOfEquivalence` at
  `CategoryTheory.Discrete.equivalence Equiv.ulift.symm` and an identity natural isomorphism,
  which is `…SeparatedFiniteEtaleOver.coprodIsoULift` — and it is the cheapest of the three to
  write. **Step 2 is where the work was**, exactly as *what no declaration does is conclude from
  them* says: the conclusion is
  `AlgebraicGeometry.LocallyRingedSpace.sigmaHomeoSigma`, added by that push to
  `Oka/Geometry/RingedSpace/LocallyRingedSpace/HasColimits.lean`, and it is **not** built from the
  four instruments this bullet names but from that file's own
  `…sigmaι_base_eq_iff`, `…exists_sigma_ι_base_eq` and the open-embedding half of
  `…sigmaι_isOpenImmersion`. **Step 3 is as priced**, one application of
  `AlgebraicGeometry.LocallyRingedSpace.homeoOfIso`. **The `≃ₜ` census above is pinned to the
  commit that adds this file and stays exact there**; past it the count moves, and the module that
  moves it is the one named above.
* **No restatement of the decomposition theorem.**
  `…SeparatedFiniteEtaleOver.exists_isConnected_decomposition` is
  `Oka/AnalyticSpace/FundamentalGroup.lean`'s and stays there; what this file changes is what a
  reader may conclude from it, and that change is recorded beside the bullet it narrows rather
  than by editing the theorem.
* **No instance for the equivalence.** `…SeparatedFiniteEtaleOver.isConnected_of_connectedSpace`
  is a theorem and not an `instance`: it would fire on every goal of the form
  `CategoryTheory.PreGaloisCategory.IsConnected _` and send search after a `ConnectedSpace` of a
  total space, which is not a class this tree's objects carry. The one `instance` here is the
  monomorphism, which is the shape the categorical condition's own field asks for.
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace ComplexAnalytic.AnalyticSpace

variable {X : AnalyticSpace.{u}} [T2Space (X : Type u)] [PreconnectedSpace (X : Type u)]

omit [T2Space (X : Type u)] [PreconnectedSpace (X : Type u)] in
/-- **An isomorphism of separated covers is surjective on total spaces.**

The inverse's underlying map is the section: `CategoryTheory.IsIso.inv_hom_id` is an equation
between two morphisms of this category, and reading both sides at a point of the target's total
space is one `congrArg`, the underlying map of a composite being the composite of the underlying
maps and the underlying map of an identity being the identity — both on the nose.

**Nothing is asked of the base**, which is why the two section hypotheses are omitted: the
statement is about a morphism that already has an inverse, and no covering-space theory is used to
produce one.

**One level down this is `ComplexAnalytic.AnalyticSpace.surjective_base_of_isIso`
(`Oka/AnalyticSpace/Basic.lean`), and that statement carries the argument for why nothing is asked
of the base, together with `ComplexAnalytic.AnalyticSpace.bijective_base_of_isIso` beside it.** The
proof here is self-contained rather than a transport along the two forgetful functors, which is one
`haveI` plus that lemma; both are a `congrArg` at `CategoryTheory.IsIso.inv_hom_id` and neither is
shorter. -/
theorem SeparatedFiniteEtaleOver.surjective_base_left_of_isIso
    {A B : SeparatedFiniteEtaleOver.{u} X} (i : A ⟶ B) [IsIso i] :
    Function.Surjective (i.left.toLRSHom.base : A.left → B.left) := fun b ↦
  ⟨((inv i).left.toLRSHom.base : B.left → A.left) b,
    congrArg (fun m : B ⟶ B ↦ (m.left.toLRSHom.base : B.left → B.left) b) (IsIso.inv_hom_id i)⟩

variable (A : SeparatedFiniteEtaleOver.{u} X)

/-- **A clopen part of a separated cover's total space is again a separated cover of the base.**

The structure morphism is `ComplexAnalytic.AnalyticSpace.ofRestrict` followed by the cover's own,
finite étale by `ComplexAnalytic.AnalyticSpace.isFiniteEtale_ofRestrict_comp` — which is where the
closedness is spent, an open part alone being finite étale over nothing — and separated by
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isSeparatedMap_restrictClopen`, read at the image of
`A` under `…SeparatedFiniteEtaleOver.toFiniteEtaleOver`.

**This is `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.restrictClopen` with the second component
supplied, and it is written out rather than built from that object.** The module docstring's
paragraph beginning *`…SeparatedFiniteEtaleOver.restrictClopen` is built from* gives the
measurement: the version whose structure morphism is the ambient object's `hom` does not elaborate
inside the default heartbeat budget and this one elaborates in seconds. The two structure morphisms
are the same term up to one unfolding. -/
noncomputable def SeparatedFiniteEtaleOver.restrictClopen (U : (A.left : AnalyticSpace.{u}).Opens)
    (hU : IsClosed (U : Set (A.left : AnalyticSpace.{u}))) : SeparatedFiniteEtaleOver.{u} X :=
  MorphismProperty.Over.mk _ ((A.left : AnalyticSpace.{u}).ofRestrict U ≫ A.hom)
    ⟨isFiniteEtale_ofRestrict_comp U hU A.hom A.isFiniteEtale_hom,
      FiniteEtaleOver.isSeparatedMap_restrictClopen
        ((SeparatedFiniteEtaleOver.toFiniteEtaleOver X).obj A) U hU A.isSeparatedMap_hom⟩

/-- **Its inclusion into the cover**, as a morphism of separated covers.

The underlying morphism is `ComplexAnalytic.AnalyticSpace.ofRestrict` and the triangle over the
base is the definition of the source's structure morphism read backwards, which is why the
compatibility is `rfl` — the same `rfl` that
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.restrictClopenι` gives for the ambient statement. -/
noncomputable def SeparatedFiniteEtaleOver.restrictClopenι (U : (A.left : AnalyticSpace.{u}).Opens)
    (hU : IsClosed (U : Set (A.left : AnalyticSpace.{u}))) :
    SeparatedFiniteEtaleOver.restrictClopen A U hU ⟶ A :=
  MorphismProperty.Over.homMk ((A.left : AnalyticSpace.{u}).ofRestrict U) rfl

/-- **And it is a monomorphism.**

A morphism of this category is determined by its underlying morphism of analytic spaces —
`CategoryTheory.MorphismProperty.Over.Hom.ext` — and the underlying morphism here is
`ComplexAnalytic.AnalyticSpace.ofRestrict`, which is a monomorphism by instance search. So
cancelling is `CategoryTheory.cancel_mono` at that morphism and nothing about covers is used.

**This is what makes a clopen part a legal test object.**
`CategoryTheory.PreGaloisCategory.IsConnected`'s second field quantifies over monomorphisms into
the object, so without this instance the clopen part is a subobject of the total space and not a
subobject in the category. -/
instance SeparatedFiniteEtaleOver.mono_restrictClopenι (U : (A.left : AnalyticSpace.{u}).Opens)
    (hU : IsClosed (U : Set (A.left : AnalyticSpace.{u}))) :
    Mono (SeparatedFiniteEtaleOver.restrictClopenι A U hU) :=
  ⟨fun {Z} _ _ hfg ↦ MorphismProperty.Over.Hom.ext
    ((cancel_mono ((A.left : AnalyticSpace.{u}).ofRestrict U)).mp
      (congrArg (fun m : Z ⟶ A ↦ m.left) hfg))⟩

/-- **A separated cover whose total space is connected is connected as an object of the category.**

The two fields of `CategoryTheory.PreGaloisCategory.IsConnected`, in the order the class declares
them; the module docstring's paragraph *The plausible direction spends the clopenness of an image*
names the route and where each hypothesis goes.

**No point of the base appears in the statement**, and that is what `[ConnectedSpace A.left]` buys
over `[PreconnectedSpace A.left]`: the point at which the fibre is read is the image of a point of
the total space, so the nonemptiness half of the class is what keeps this basepoint-free. -/
theorem SeparatedFiniteEtaleOver.isConnected_of_connectedSpace
    [ConnectedSpace (A.left : Type u)] : PreGaloisCategory.IsConnected A where
  notInitial h := by
    obtain ⟨a⟩ := (inferInstance : Nonempty (A.left : Type u))
    set x : X := (A.hom.toLRSHom.base : A.left → X) a with hx
    exact ((PreGaloisCategory.initial_iff_fiber_empty
      (SeparatedFiniteEtaleOver.fintypeFiberFunctor.{u} x) A).mp ⟨h⟩).false ⟨a, rfl⟩
  noTrivialComponent Y i hmono hY := by
    haveI := hmono
    haveI : T2Space
        ((((SeparatedFiniteEtaleOver.toFiniteEtaleOver X).obj A).left : AnalyticSpace.{u}) :
          Type u) :=
      SeparatedFiniteEtaleOver.t2Space_left A
    haveI : T2Space
        ((((SeparatedFiniteEtaleOver.toFiniteEtaleOver X).obj Y).left : AnalyticSpace.{u}) :
          Type u) :=
      SeparatedFiniteEtaleOver.t2Space_left Y
    haveI : PreconnectedSpace
        ((((SeparatedFiniteEtaleOver.toFiniteEtaleOver X).obj A).left : AnalyticSpace.{u}) :
          Type u) :=
      inferInstanceAs (PreconnectedSpace (A.left : Type u))
    obtain ⟨a₀⟩ := (inferInstance : Nonempty (A.left : Type u))
    set x : X := (A.hom.toLRSHom.base : A.left → X) a₀ with hx
    obtain ⟨y₀⟩ : Nonempty ((SeparatedFiniteEtaleOver.fintypeFiberFunctor.{u} x).obj Y) :=
      (PreGaloisCategory.not_initial_iff_fiber_nonempty
        (SeparatedFiniteEtaleOver.fintypeFiberFunctor.{u} x) Y).mp hY
    have hw : ∀ y : (Y.left : Type u),
        (A.hom.toLRSHom.base : A.left → X) ((i.left.toLRSHom.base : Y.left → A.left) y)
          = (Y.hom.toLRSHom.base : Y.left → X) y :=
      fun y ↦ congrArg (fun g : Y.left ⟶ X ↦ (g.toLRSHom.base : Y.left → X) y)
        (MorphismProperty.Over.w i)
    have hinj : Function.Injective (i.left.toLRSHom.base : Y.left → A.left) :=
      SeparatedFiniteEtaleOver.injective_base_left_of_mono i
    have hsurj : Function.Surjective (i.left.toLRSHom.base : Y.left → A.left) :=
      Set.range_eq_univ.mp
        ((FiniteEtaleOver.isClopen_range_left
          ((SeparatedFiniteEtaleOver.toFiniteEtaleOver X).map i)).eq_univ
            ⟨_, Set.mem_range_self y₀.1⟩)
    have hbij : Function.Bijective (FiniteEtaleOver.fiberMap.{u} x
        ((SeparatedFiniteEtaleOver.toFiniteEtaleOver X).map i)) := by
      refine ⟨fun p q hpq ↦ Subtype.ext (hinj (congrArg Subtype.val hpq)), ?_⟩
      rintro ⟨b, hb⟩
      obtain ⟨y, hy⟩ := hsurj b
      have hyx : (Y.hom.toLRSHom.base : Y.left → X) y = x := by rw [← hw y, hy]; exact hb
      exact ⟨⟨y, hyx⟩, Subtype.ext hy⟩
    haveI : IsIso ((SeparatedFiniteEtaleOver.toFiniteEtaleOver X).map i) :=
      FiniteEtaleOver.isIso_of_bijective_fiberMap_of_t2 _ x hbij
    exact isIso_of_reflects_iso i (SeparatedFiniteEtaleOver.toFiniteEtaleOver X)

/-- **And conversely**: a separated cover connected as an object has connected total space.

`connectedSpace_iff_clopen` is the shape the conclusion is assembled in. Nonemptiness is
`CategoryTheory.PreGaloisCategory.nonempty_fiber_of_isConnected` and a point of the total space is
the first component of a point of a fibre; for a nonempty clopen part, the subobject is
`…SeparatedFiniteEtaleOver.restrictClopenι` and the class's second field makes it an isomorphism,
whose image is the whole total space by
`…SeparatedFiniteEtaleOver.surjective_base_left_of_isIso` and is the clopen part by
`ComplexAnalytic.AnalyticSpace.range_base_ofRestrict`.

**The empty base is a case of the proof and not an excluded hypothesis**; the module docstring's
section *The empty base is inside both directions* says what settles it and why the import that
settles it is this file's only one. -/
theorem SeparatedFiniteEtaleOver.connectedSpace_of_isConnected
    [h : PreGaloisCategory.IsConnected A] : ConnectedSpace (A.left : Type u) := by
  rcases isEmpty_or_nonempty (X : Type u) with hX | hX
  · exact (h.notInitial ((SeparatedFiniteEtaleOver.isInitialIdOfIsEmpty.{u} X).ofIso
      A.isoIdOfIsEmpty.symm)).elim
  obtain ⟨x⟩ := hX
  haveI hfib : Nonempty ((SeparatedFiniteEtaleOver.fintypeFiberFunctor.{u} x).obj A) :=
    PreGaloisCategory.nonempty_fiber_of_isConnected _ A
  rw [connectedSpace_iff_clopen]
  refine ⟨⟨hfib.some.1⟩, fun s hs ↦ ?_⟩
  rcases Set.eq_empty_or_nonempty s with rfl | ⟨a, ha⟩
  · exact Or.inl rfl
  refine Or.inr ?_
  set U : (A.left : AnalyticSpace.{u}).Opens := ⟨s, hs.2⟩ with hUdef
  have hU : IsClosed (U : Set (A.left : AnalyticSpace.{u})) := hs.1
  set y : X := (A.hom.toLRSHom.base : A.left → X) a with hy
  have hni : IsInitial (SeparatedFiniteEtaleOver.restrictClopen A U hU) → False := fun hin ↦
    ((PreGaloisCategory.initial_iff_fiber_empty
      (SeparatedFiniteEtaleOver.fintypeFiberFunctor.{u} y)
      (SeparatedFiniteEtaleOver.restrictClopen A U hU)).mp ⟨hin⟩).false ⟨⟨a, ha⟩, rfl⟩
  haveI : IsIso (SeparatedFiniteEtaleOver.restrictClopenι A U hU) :=
    h.noTrivialComponent _ (SeparatedFiniteEtaleOver.restrictClopenι A U hU) hni
  have hrange : Set.range ((SeparatedFiniteEtaleOver.restrictClopenι A U hU).left.toLRSHom.base :
      (SeparatedFiniteEtaleOver.restrictClopen A U hU).left → A.left) = s :=
    AnalyticSpace.range_base_ofRestrict _ _
  rw [← hrange]
  exact Set.range_eq_univ.mpr
    (SeparatedFiniteEtaleOver.surjective_base_left_of_isIso
      (SeparatedFiniteEtaleOver.restrictClopenι A U hU))

/-- **So the two conditions are the same condition**, over a Hausdorff preconnected base.

This is the statement taxis #2082's fourth section asks for, in both directions rather than one,
and it is what its third bullet's *or a proof that they cannot* names: there is no separated cover
over such a base on which the two readings of *connected* differ, so no witness separating them
exists to be exhibited. -/
theorem SeparatedFiniteEtaleOver.isConnected_iff_connectedSpace :
    PreGaloisCategory.IsConnected A ↔ ConnectedSpace (A.left : Type u) :=
  ⟨fun _ ↦ SeparatedFiniteEtaleOver.connectedSpace_of_isConnected A,
    fun _ ↦ SeparatedFiniteEtaleOver.isConnected_of_connectedSpace A⟩

/-- **A connected object lies in the preconnected subcategory.**

`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.isPreconnected`
(`Oka/AnalyticSpace/SeparatedFiberFunctor.lean`) is `PreconnectedSpace` of the total space as a
`CategoryTheory.ObjectProperty`, and this is the equivalence above followed by
`ConnectedSpace.toPreconnectedSpace`. **It is the one statement in this repository relating the
categorical condition to an object property the tree already had.**

**The converse is not proved here and is not claimed**; the module docstring's `## What is not
here` gives the reason and marks it as an argument rather than a run. -/
theorem SeparatedFiniteEtaleOver.isPreconnected_of_isConnected
    [PreGaloisCategory.IsConnected A] : SeparatedFiniteEtaleOver.isPreconnected.{u} X A :=
  haveI := SeparatedFiniteEtaleOver.connectedSpace_of_isConnected A
  inferInstanceAs (PreconnectedSpace (A.left : Type u))

end ComplexAnalytic.AnalyticSpace
