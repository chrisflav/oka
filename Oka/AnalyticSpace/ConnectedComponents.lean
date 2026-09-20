/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.AnalyticSpace.ConnectedCover
import Oka.AnalyticSpace.FundamentalGroup
import Oka.Topology.Connected.Clopen

/-!
# The pieces of the decomposition are the connected components of the total space

`Oka/AnalyticSpace/FundamentalGroup.lean`'s
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.exists_isConnected_decomposition` writes a
cover separated over a Hausdorff preconnected nonempty base as a finite coproduct `∐ f ≅ A` **in
the category**, with every `f i` connected as an *object*;
`Oka/AnalyticSpace/ConnectedCover.lean`'s
`…SeparatedFiniteEtaleOver.isConnected_iff_connectedSpace` upgrades that third conjunct to
`ConnectedSpace (f i).left`. **Neither says anything about `A.left` as a space**, and both of those
modules say so in a `## What is not here` bullet. This file is what closes the gap: the
decomposition is carried to a **homeomorphism** `A.left ≃ₜ Σ i, (f i).left`, and the components of
the total space are then the pieces. taxis #2091 is the filing.

**The three steps that bullet priced are one universe crossing, one identification of a space and
one functor image, and the pricing is reversed by the first of them.** The bullet called the
coproduct-to-`sigma` step *the expensive step of the three* and the disjoint-union step the one
whose instruments were all in the tree:

* **The universe crossing is four lines and is `…SeparatedFiniteEtaleOver.coprodIsoULift` below.**
  `…SeparatedFiniteEtaleOver.sigma` takes `{ι : Type u}` and the decomposition theorem's `ι` is
  `Type`, because it is `CategoryTheory.PreGaloisCategory.has_decomp_connected_components'`'s.
  `CategoryTheory.Limits.HasColimit.isoOfEquivalence` at
  `CategoryTheory.Discrete.equivalence Equiv.ulift.symm` crosses it for an arbitrary index, which
  is the crossing `…SeparatedFiniteEtaleOver.hasFiniteCoproducts` makes for `Fin n` only.
* **The disjoint-union step is where the work was**, and it is
  `AlgebraicGeometry.LocallyRingedSpace.sigmaHomeoSigma` of
  `Oka/Geometry/RingedSpace/LocallyRingedSpace/HasColimits.lean`, added by the same push as this
  file: that file had the open embedding, the disjointness and the covering and drew no conclusion
  from them, and said so in a bullet which this push retires.
* **The functor image is one application** of `AlgebraicGeometry.LocallyRingedSpace.homeoOfIso`
  and is `…SeparatedFiniteEtaleOver.homeoLeftOfIso` below.

**Nothing in the middle step is analytic.**
`ComplexAnalytic.AnalyticSpace.sigma_toLocallyRingedSpace` is `rfl`, so the carrier of a disjoint
union of analytic spaces *is* the carrier of the locally-ringed-space coproduct, and
`ComplexAnalytic.AnalyticSpace.sigmaHomeoSigma` below is the mirror-tree statement read at that
`rfl` and nothing else. The same `rfl` carries it to the
covers, which is why no statement here has to know what `…SeparatedFiniteEtaleOver.sigma` does to
the structure morphism.

## Main definitions

- `ComplexAnalytic.AnalyticSpace.sigmaHomeoSigma`: **the space underlying a disjoint union of
  analytic spaces is the topological disjoint union of theirs.**
- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.homeoLeftOfIso`: **an isomorphism of
  separated covers is a homeomorphism on total spaces.**
- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.coprodIsoSigma`: **the categorical
  coproduct of finitely many separated covers is their disjoint union**, as an isomorphism of
  covers.
- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.coprodIsoULift`: **and a coproduct over
  an index type in `Type` is a coproduct over one in `Type u`**, which is the universe crossing.
- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.coprodLeftHomeoSigma`: **the three
  together** — the total space of a coproduct of separated covers is the topological disjoint
  union of the members' total spaces.

## Main results

- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.exists_connectedComponent_decomposition`:
  **a cover separated over a Hausdorff preconnected nonempty base is homeomorphic to a finite
  disjoint union of connected spaces, and the pieces of that disjoint union are the connected
  components of its total space.** This is
  `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.exists_isConnected_decomposition` read
  on spaces.

## What the statement says and what it does not

**The homeomorphism is data and the component statement is about it.** The theorem produces an
`e : A.left ≃ₜ Σ i, (g i).left` and says
`connectedComponent a = e ⁻¹' Set.range (Sigma.mk (e a).1)` for every point `a` — so the
components of `A.left` are exactly the preimages of the members, one for each index. **It does not
assert that the index type is the set of components**: over an index `i` whose piece has empty
total space the two would differ, and no piece here is empty, because `ConnectedSpace` is
nonemptiness plus preconnectedness and every `g i` carries it. The statement is left set-level for
that reason; `ConnectedComponents`, the quotient type, appears nowhere.

**The index type is `ULift ι` and that is visible in the statement**, which quantifies it
existentially in `Type u`. The theorem it is read from quantifies its own index in `Type`, and
`…SeparatedFiniteEtaleOver.sigma` cannot be applied there; nothing is lost, because the index type
is existential at both ends.

**No hypothesis is added to and nothing is restated from
`…SeparatedFiniteEtaleOver.exists_isConnected_decomposition`.** `[T2Space X]`,
`[PreconnectedSpace X]` and `[Nonempty X]` are that theorem's own, and the first two are also what
`…SeparatedFiniteEtaleOver.isConnected_iff_connectedSpace` asks; this file adds none of its own.

## What the import costs and what the census scripts return

**The import cost is measured in the environment and not by a scan.** At the commit this file is
cut from, `import Oka` brings **5534** modules; at the commit that adds it, **5536**. The
set difference over `Lean.Environment.allImportedModuleNames` is exactly `Oka` itself, this module
and `Oka.Topology.Connected.Clopen`, so **no Mathlib module enters the closure**: two of this
file's three imports were in it already and the third is the mirror file this push also adds,
whose own two imports — `Mathlib.Topology.Connected.Clopen` and `Mathlib.Topology.Constructions` —
were in it already as well.

**`scripts/DumpOkaDecls.lean`** writes **6** rows at this module, **1** at
`Oka.Topology.Connected.Clopen` and **20 → 24** at
`Oka.Geometry.RingedSpace.LocallyRingedSpace.HasColimits` — no equation lemma, no match lemma and
no congruence lemma in any of the three — and the dump total moves **4957 → 4968**.
`scripts/DumpEnvNames.lean` moves **338225 → 338238**, being **332545 → 332556**
declarations and **5680 → 5682** modules, which is this push's eleven declarations and
its two modules.

**`scripts/guard_coverage.py`** moves guards **1986 → 1997** under `OkaTest/Axioms/`, which is
**6** added to `OkaTest/Axioms/Morphisms.lean` (**721 → 727** in that file) and **5** to
`OkaTest/Axioms/Sheaves.lean` (**111 → 116**); advertised **1487 → 1493** declarations in
**226 → 228** files, in both **1345 → 1351**, and guarded and advertised nowhere
**641 → 646** — the five being this file's `## Main definitions` entries, that row being where a
guarded declaration advertised outside a `## Main results` section lands. **Its *unguarded* row
is flat at 142, in 60 files** — every
declaration this push advertises is guarded — *abbreviated citations, not counted* is flat at
**30, four of them dotted**, and the *backticked tokens skipped* line is flat at **700**
in its *resolve to nothing* column.

**One row moves that the list above does not name.** *Advertised from another file* goes
**85 → 86**, and the one is
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.exists_isConnected_decomposition`: this
file's `## Main results` entry names it, because the entry says what the theorem is read from, and
the script attributes every name in that section to the file it is declared in.

**`scripts/check_docstring_names.py`** goes **17761 → 17845** backticked names
(**4327 → 4348** distinct) and **273 → 306** elided citations
(**150 → 155** distinct), **0 unresolved at both ends**, **6** resolving under more than
one namespace at both, and **232 → 237** dotless.

**The census the module this one is cut beside published is what this push moves.**
`Oka/AnalyticSpace/ConnectedCover.lean`'s `## What is not here` records that `connectedComponent`
occurred **0** times in the comment-stripped code of `Oka/` and `OkaTest/` at the commit that adds
that file; at the commit that adds this one the token occurs **14** times in **4** files,
**2** of them inside `connectedComponentIn`, and `≃ₜ` goes **12 → 17** occurrences in
**10 → 12** files. That sentence is pinned to its own commit and stays exact there;
the record that the tree has moved past it is in the bullet this push narrows.

**The published check on the statements of a pullback square is unmoved in both halves**: over
`OkaTest/Axioms/Morphisms.lean`'s `#print axioms` names, *isPullback* returns **9** unfiltered
and **8** dropping the ones over `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver`, and
*hasPullback* returns **8** and **6**, at both ends alike; no name of the six this push adds
there carries either token.

## What is not here

* **No statement that the decomposition is unique, and none that the index type is determined.**
  The connected components of `A.left` are determined, and the theorem says the pieces are them;
  what is not said is that two decompositions have the same index type, which would be the
  statement that the map `i ↦ e ⁻¹' Set.range (Sigma.mk i)` is injective. It is — the pieces are
  nonempty and disjoint — and it has no consumer.
* **Nothing about the fibre functor or the fundamental group.** The decomposition theorem is read
  as a statement about a space and nothing here touches
  `…SeparatedFiniteEtaleOver.fintypeFiberFunctor` or the group
  `Oka/AnalyticSpace/FundamentalGroup.lean` builds from it; in particular **the number of pieces
  is not related to anything**, and the degree of the cover does not appear.
* **No `Homeomorph` compatible with the covers' own inclusions at this level.**
  `AlgebraicGeometry.LocallyRingedSpace.sigmaHomeoSigma_sigmaι_base` pins the mirror-tree
  homeomorphism against `CategoryTheory.Limits.Sigma.ι`, and
  `ComplexAnalytic.AnalyticSpace.sigmaHomeoSigma` inherits it up to the `rfl` above; what is not
  stated is the corresponding equation for `…SeparatedFiniteEtaleOver.sigmaι`, whose underlying
  morphism is the same one *not reducibly* — `Oka/AnalyticSpace/Sigma.lean` says so of the ambient
  construction. Nothing below needs it: the component statement is about the homeomorphism and
  reads no inclusion.
* **Nothing over a base that is not Hausdorff, preconnected and nonempty.** Those are the
  hypotheses of the theorem this is read from, and this file does not ask whether the conclusion
  survives without them.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace ComplexAnalytic.AnalyticSpace

/-- **The space underlying a disjoint union of analytic spaces is the topological disjoint union
of the spaces underlying its members.**

`AlgebraicGeometry.LocallyRingedSpace.sigmaHomeoSigma` read at
`ComplexAnalytic.AnalyticSpace.sigma_toLocallyRingedSpace`, which is `rfl`: the carrier of
`ComplexAnalytic.AnalyticSpace.sigma` *is* the carrier of the locally-ringed-space coproduct, so
there is nothing to transport and the definition is that statement applied to the members'
locally ringed spaces.

**No finiteness is asked**, here or by `ComplexAnalytic.AnalyticSpace.sigma`, which takes an
arbitrary family; the mirror-tree statement holds for any index type too, and it is the covers —
where a disjoint union has to be finite étale again — that ask for one. -/
noncomputable def sigmaHomeoSigma {ι : Type u} (F : ι → AnalyticSpace.{u}) :
    ((AnalyticSpace.sigma F : AnalyticSpace.{u}) : Type u) ≃ₜ
      Σ i, ((F i : AnalyticSpace.{u}) : Type u) :=
  LocallyRingedSpace.sigmaHomeoSigma fun i ↦ (F i).toLocallyRingedSpace

variable {X : AnalyticSpace.{u}} [T2Space (X : Type u)] [PreconnectedSpace (X : Type u)]

/-- **An isomorphism of separated covers is a homeomorphism on total spaces.**

`AlgebraicGeometry.LocallyRingedSpace.homeoOfIso` at the image of the isomorphism under the two
forgetful functors of the comma category and
`ComplexAnalytic.AnalyticSpace.forgetToLocallyRingedSpace`. **This is the step
`Oka/AnalyticSpace/ConnectedCover.lean`'s `## What is not here` called the cheap one**, and it is:
one functor application, where `…SeparatedFiniteEtaleOver.surjective_base_left_of_isIso` and
`ComplexAnalytic.AnalyticSpace.bijective_base_of_isIso` give the surjectivity and the bijectivity
of the underlying map and neither gives continuity of the inverse.

**Nothing is asked of the base**, as for the two lemmas just named; the section's hypotheses are
inherited and unused here. -/
noncomputable def SeparatedFiniteEtaleOver.homeoLeftOfIso {A B : SeparatedFiniteEtaleOver.{u} X}
    (e : A ≅ B) :
    ((A.left : AnalyticSpace.{u}) : Type u) ≃ₜ ((B.left : AnalyticSpace.{u}) : Type u) :=
  LocallyRingedSpace.homeoOfIso
    (((MorphismProperty.Over.forget _ _ _ ⋙ Over.forget _) ⋙
      AnalyticSpace.forgetToLocallyRingedSpace).mapIso e)

/-- **The categorical coproduct of finitely many separated covers is their disjoint union.**

`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.isColimitCofanSigma` says the cofan built
on `…SeparatedFiniteEtaleOver.sigma` is a colimit;
`CategoryTheory.Limits.IsColimit.coconePointUniqueUpToIso` against the colimit cocone is the
isomorphism. **`∐ A` is `CategoryTheory.Limits.colimit` and is not `…sigma A` on the nose**, which
is why this is a declaration and not a rewriting. -/
noncomputable def SeparatedFiniteEtaleOver.coprodIsoSigma {ι : Type u} [Finite ι]
    (A : ι → SeparatedFiniteEtaleOver.{u} X) : (∐ A) ≅ SeparatedFiniteEtaleOver.sigma A :=
  (colimit.isColimit (Discrete.functor A)).coconePointUniqueUpToIso
    (SeparatedFiniteEtaleOver.isColimitCofanSigma A)

/-- **A coproduct over an index type in `Type` is a coproduct over one in `Type u`.**

`CategoryTheory.Limits.HasColimit.isoOfEquivalence` at
`CategoryTheory.Discrete.equivalence Equiv.ulift.symm`, with the natural isomorphism the identity
componentwise.

**This is the universe crossing, and it is the step the filing this file closes was told would be
the expensive one.** It is expensive only in the sense that it exists: `…sigma` takes its index in
`Type u` because `ComplexAnalytic.AnalyticSpace.sigma` does, and
`CategoryTheory.PreGaloisCategory.has_decomp_connected_components'` produces one in `Type`, so
without this nothing downstream elaborates at all. The crossing itself is
`…SeparatedFiniteEtaleOver.hasFiniteCoproducts`'s, made for an arbitrary index type instead of for
`Fin n`. -/
noncomputable def SeparatedFiniteEtaleOver.coprodIsoULift {ι : Type} [Finite ι]
    (A : ι → SeparatedFiniteEtaleOver.{u} X) :
    (∐ A) ≅ ∐ (fun i : ULift.{u} ι ↦ A i.down) :=
  HasColimit.isoOfEquivalence (Discrete.equivalence Equiv.ulift.symm)
    (Discrete.natIso fun _ ↦ Iso.refl _)

/-- **The total space of a coproduct of separated covers is the topological disjoint union of the
members' total spaces.**

The two steps above composed: the coproduct is the disjoint union as an object
(`…SeparatedFiniteEtaleOver.coprodIsoSigma`), an isomorphism of covers is a homeomorphism
(`…SeparatedFiniteEtaleOver.homeoLeftOfIso`), and the disjoint union's total space is the `Sigma`
type (`ComplexAnalytic.AnalyticSpace.sigmaHomeoSigma`). -/
noncomputable def SeparatedFiniteEtaleOver.coprodLeftHomeoSigma {ι : Type u} [Finite ι]
    (A : ι → SeparatedFiniteEtaleOver.{u} X) :
    (((∐ A).left : AnalyticSpace.{u}) : Type u) ≃ₜ
      Σ i, (((A i).left : AnalyticSpace.{u}) : Type u) :=
  (SeparatedFiniteEtaleOver.homeoLeftOfIso (SeparatedFiniteEtaleOver.coprodIsoSigma A)).trans
    (AnalyticSpace.sigmaHomeoSigma fun i ↦ ((A i).left : AnalyticSpace.{u}))

variable [Nonempty (X : Type u)]

/-- **A cover separated over a Hausdorff preconnected nonempty base is a finite disjoint union of
connected spaces, and the pieces are the connected components of its total space.**

`…SeparatedFiniteEtaleOver.exists_isConnected_decomposition` read on spaces. The pieces are that
theorem's own, re-indexed by `ULift`; their total spaces are connected by
`…SeparatedFiniteEtaleOver.connectedSpace_of_isConnected`, and the homeomorphism is
`…SeparatedFiniteEtaleOver.coprodLeftHomeoSigma` after the isomorphism `∐ f ≅ A` is inverted and
crossed.

**The last conjunct is the statement that the pieces are the components**, and it is
`connectedComponent_sigmaMk` (`Oka/Topology/Connected/Clopen.lean`) transported along the
homeomorphism: a homeomorphism carries connected components to connected components, which is
`Homeomorph.image_connectedComponentIn` read at `Set.univ`, and the component of a point of a
disjoint union of connected spaces is the member it lies in.

**Read at a fixed `i` the last conjunct says the `i`-th piece is a component**: `e ⁻¹' Set.range
(Sigma.mk i)` is the `i`-th piece's image in `A.left`, and every point `a` of it has
`(e a).1 = i`. -/
theorem SeparatedFiniteEtaleOver.exists_connectedComponent_decomposition
    (A : SeparatedFiniteEtaleOver.{u} X) :
    ∃ (ι : Type u) (_ : Finite ι) (g : ι → SeparatedFiniteEtaleOver.{u} X)
      (e : ((A.left : AnalyticSpace.{u}) : Type u) ≃ₜ
        Σ i, (((g i).left : AnalyticSpace.{u}) : Type u)),
      (∀ i, ConnectedSpace (((g i).left : AnalyticSpace.{u}) : Type u)) ∧
        ∀ a, connectedComponent a = e ⁻¹' Set.range (Sigma.mk (e a).1) := by
  obtain ⟨ι, hι, f, e, hf⟩ := SeparatedFiniteEtaleOver.exists_isConnected_decomposition A
  haveI : ∀ i : ULift.{u} ι, ConnectedSpace ((((f i.down).left : AnalyticSpace.{u})) : Type u) :=
    fun i ↦ haveI := hf i.down
      SeparatedFiniteEtaleOver.connectedSpace_of_isConnected _
  refine ⟨ULift.{u} ι, inferInstance, fun i ↦ f i.down,
    (SeparatedFiniteEtaleOver.homeoLeftOfIso
        (e.symm ≪≫ SeparatedFiniteEtaleOver.coprodIsoULift f)).trans
      (SeparatedFiniteEtaleOver.coprodLeftHomeoSigma fun i : ULift.{u} ι ↦ f i.down),
    inferInstance, fun a ↦ ?_⟩
  set h := (SeparatedFiniteEtaleOver.homeoLeftOfIso
      (e.symm ≪≫ SeparatedFiniteEtaleOver.coprodIsoULift f)).trans
    (SeparatedFiniteEtaleOver.coprodLeftHomeoSigma fun i : ULift.{u} ι ↦ f i.down) with hh
  have himg : h '' connectedComponent a = connectedComponent (h a) := by
    simpa [connectedComponentIn_univ, Set.image_univ, h.surjective.range_eq] using
      h.image_connectedComponentIn (s := (Set.univ : Set _)) (Set.mem_univ a)
  rw [← h.injective.preimage_image (connectedComponent a), himg]
  rcases hb : h a with ⟨i, y⟩
  simp only [connectedComponent_sigmaMk]

end ComplexAnalytic.AnalyticSpace
