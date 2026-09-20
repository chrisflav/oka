/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.AnalyticSpace.ConnectedCover
import Oka.AnalyticSpace.FundamentalGroup
import Oka.Topology.Homeomorph.Lemmas

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
`ComplexAnalytic.AnalyticSpace.sigmaHomeoSigma` is the mirror-tree statement read at that
`rfl` and nothing else. The same `rfl` carries it to the
covers, which is why no statement here has to know what `…SeparatedFiniteEtaleOver.sigma` does to
the structure morphism.

**That declaration was in this file, and said *below*, until 2026-09-20**, when taxis #2094 moved
it to `Oka/AnalyticSpace/Sigma.lean`, beside the construction it is about and with the two lemmas
pinning it against the inclusions. **The argument for moving it is this file's own guard section**:
`OkaTest/Axioms/Morphisms.lean` said of the six names it guarded for this module that *one of the
six does not mention the covers at all*, and says that the split between guard files is *by what
the statement is about and not by which push wrote it* — which is an argument that the declaration
was in the wrong module and not merely in the wrong guard file. Both clauses are dated there.
Nothing about it changed but its home: the statement, its name and its proof are the ones
that landed.

## Main definitions

- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.homeoLeftOfIso`: **an isomorphism of
  separated covers is a homeomorphism on total spaces.**
- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.coprodIsoSigma`: **the categorical
  coproduct of finitely many separated covers is their disjoint union**, as an isomorphism of
  covers.
- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.coprodIsoULift`: **and a coproduct over
  an index type in `Type` is a coproduct over one in `Type u`**, which is the universe crossing.
- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.coprodLeftHomeoSigma`: **the two above
  together with the disjoint union's own space** — the total space of a coproduct of separated
  covers is the topological disjoint union of the members' total spaces.

## Main results

- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.exists_connectedComponent_decomposition`:
  **a cover separated over a Hausdorff preconnected nonempty base is homeomorphic to a finite
  disjoint union of connected spaces, and the pieces of that disjoint union are the connected
  components of its total space.** This is
  `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.exists_isConnected_decomposition` read
  on spaces.
- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.finite_connectedComponents_left`: **so
  such a cover has finitely many connected components**, as a statement about
  `ConnectedComponents`, the quotient type. It is the statement above with the homeomorphism and
  the pieces forgotten; the census at the foot of this docstring says where else in the tree that
  quotient type is named.

## What the statement says and what it does not

**The homeomorphism is data and the component statement is about it.** The theorem produces an
`e : A.left ≃ₜ Σ i, (g i).left` and says
`connectedComponent a = e ⁻¹' Set.range (Sigma.mk (e a).1)` for every point `a` — so the
components of `A.left` are exactly the preimages of the members, one for each index. **It does not
assert that the index type is the set of components**: over an index `i` whose piece has empty
total space the two would differ, and no piece here is empty, because `ConnectedSpace` is
nonemptiness plus preconnectedness and every `g i` carries it. The statement is left set-level for
that reason.

**This paragraph ended *`ConnectedComponents`, the quotient type, appears nowhere*, in the present
tense, until 2026-09-20**, when taxis #2094 added
`…SeparatedFiniteEtaleOver.finite_connectedComponents_left` here; **what that statement says is
still not what this one is read as saying**. It says the components are finite in number, which
follows from the index type being finite and the map index-to-component being onto; it does not
say the two are in bijection, and the clause about the index type above is why. The dated record
is here because it is this paragraph's own sentence that moved.

**The index type is `ULift ι` and that is visible in the statement**, which quantifies it
existentially in `Type u`. The theorem it is read from quantifies its own index in `Type`, and
`…SeparatedFiniteEtaleOver.sigma` cannot be applied there; nothing is lost, because the index type
is existential at both ends.

**No hypothesis is added to and nothing is restated from
`…SeparatedFiniteEtaleOver.exists_isConnected_decomposition`.** `[T2Space X]`,
`[PreconnectedSpace X]` and `[Nonempty X]` are that theorem's own, and the first two are also what
`…SeparatedFiniteEtaleOver.isConnected_iff_connectedSpace` asks; this file adds none of its own.

## What the import costs and what the census scripts return

**Every figure in this section down to the pullback paragraph is a figure of the push that added
this file, pinned to it, and none of them is a claim about the tree as it stands**; what the push
of 2026-09-20 moved is the paragraph after them. **Two sentences below were written in the present
tense and are dated in place** rather than rewritten, because a record of what a push measured is
worth more than a figure that tracks the head.

**The import cost is measured in the environment and not by a scan.** At the commit this file is
cut from, `import Oka` brings **5534** modules; at the commit that adds it, **5536**. The
set difference over `Lean.Environment.allImportedModuleNames` is exactly `Oka` itself, this module
and `Oka.Topology.Connected.Clopen`, so **no Mathlib module enters the closure**: at that commit
two of this file's three imports were in it already and the third was
`Oka.Topology.Connected.Clopen`, the mirror file that push also added, whose own two imports —
`Mathlib.Topology.Connected.Clopen` and `Mathlib.Topology.Constructions` — were in it already as
well. **The third import read `Oka.Topology.Connected.Clopen` until 2026-09-20**, when taxis #2094
replaced it by `Oka.Topology.Homeomorph.Lemmas`, which imports it; the sentence above is that
push's measurement and the one at the end of this section is this one's.

**`scripts/DumpOkaDecls.lean`** wrote, at that commit, **6** rows at this module, **1** at
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

**The published check on the statements of a pullback square was unmoved in both halves**: over
`OkaTest/Axioms/Morphisms.lean`'s `#print axioms` names, *isPullback* returned **9** unfiltered
and **8** dropping the ones over `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver`, and
*hasPullback* returned **8** and **6**, at both ends alike; no name of the six that push added
there carries either token.

## What the push of 2026-09-20 moved

**taxis #2094 is the filing.** It adds three declarations in a new mirror module
(`Oka/Topology/Homeomorph/Lemmas.lean`), two in `Oka/AnalyticSpace/Sigma.lean`, and one theorem
here; it moves one declaration out of this file into that one and moves nothing else. The base
column below is `upstream/master` at the commit that merged the push this section's other figures
are of; every figure is a run in a checkout built at each end.

**The import closure grows by one module and it is not a Mathlib one.** `import Oka` brings
**5536 → 5537** modules and the set difference over `Lean.Environment.allImportedModuleNames` is
exactly `Oka.Topology.Homeomorph.Lemmas`, the mirror file this push adds; its two imports are
`Mathlib.Topology.Homeomorph.Lemmas`, already in the closure, and
`Oka.Topology.Connected.Clopen`, which this file imported directly before and now reaches through
it. **Upstreaming that file costs its Mathlib target nothing** — `python3
scripts/import_cost.py Oka/Topology/Homeomorph/Lemmas.lean` reports a closure of **624** and a
cost of **0**, the one Mathlib import beyond the target being already in it.

**`scripts/DumpOkaDecls.lean`** moves **4968 → 4974**: **0 → 3** rows at
`Oka.Topology.Homeomorph.Lemmas`, **21 → 24** at `Oka.AnalyticSpace.Sigma`, **flat at 1** at
`Oka.Topology.Connected.Clopen`, and **flat at 6** at this module, which is the one declaration
that left and the one that arrived. **No equation lemma, no match lemma and no congruence lemma
at any of them.** `scripts/DumpEnvNames.lean` moves **338238 → 338245**, being
**332556 → 332562** declarations and **5682 → 5683** modules.

**`scripts/guard_coverage.py`** moves guards **1997 → 2003** under `OkaTest/Axioms/`:
`OkaTest/Axioms/AnalyticSpace.lean` **254 → 257**, `OkaTest/Axioms/Sheaves.lean` **116 → 119**,
and `OkaTest/Axioms/Morphisms.lean` **flat at 727**, where one guard was removed and one added.
Advertised goes **1493 → 1501** in **228 → 229** files and *in both lists* **1351 → 1359**.
**The eight are not the eight a reader would guess**: the three of the new mirror file, the three
added to `Oka/AnalyticSpace/Sigma.lean`'s `## Main results`, this file's new theorem — and
`ComplexAnalytic.AnalyticSpace.sigma` itself, which that file's `## Main results` names for the
first time in the sentence saying what the new entry adds, and which was a `## Main definitions`
entry there and so counted in no advertised row before. *Guarded and advertised nowhere* goes
**646 → 644**, the two being that name and
`ComplexAnalytic.AnalyticSpace.sigmaHomeoSigma`, which moved the same way out of this file's
`## Main definitions`. **The *unguarded* row is flat at 142, in 60 files**, *abbreviated
citations, not counted* is flat at **30, four of them dotted**, and *advertised from another
file* is **flat at 86** — this file's citation of
`…SeparatedFiniteEtaleOver.exists_isConnected_decomposition` is still the same one entry and the
new `## Main results` bullets name no declaration owned by another module. **The *resolve to
nothing* column is the one row of this push that is not flat and not accounted for by a
declaration**: **700 → 702**, the two being the `simpNF` output quoted in the two declaration
docstrings added to `Oka/AnalyticSpace/Sigma.lean`, which contains dotted tokens that are terms
and not names.

**`scripts/check_docstring_names.py`** goes **17845 → 17899** backticked names
(**4348 → 4364** distinct) and **306 → 311** elided citations (**155 → 156** distinct), with
**0 unresolved at both ends** and **6** resolving under more than one namespace at both;
**237 → 239** dotless occurrences are not checked.

**The two censuses this line publishes, re-taken.** In the comment-stripped code of `Oka/` and
`OkaTest/`, `connectedComponent` goes **14 → 29** occurrences in **4 → 5** files and `≃ₜ`
goes **17 → 20** in **12 → 14**; the **2** occurrences inside `connectedComponentIn` are unmoved in
number and have changed file, being in the mirror module's proof rather than in this one's.
**`ConnectedComponents`, the quotient type, goes 0 → 5 occurrences in 2 files** — this module
and `Oka/Topology/Homeomorph/Lemmas.lean` — and **the sentence that dates it is the one in
`## What the statement says and what it does not` above**, the paragraph that ended *appears
nowhere* in the present tense until 2026-09-20. It is named by its section and not reached by
counting paragraphs, so the pointer survives the next push into this docstring.

## What is not here

* **No statement that the decomposition is unique, and none that the index type is determined.**
  The connected components of `A.left` are determined, and the theorem says the pieces are them;
  what is not said is that two decompositions have the same index type, which would be the
  statement that the map `i ↦ e ⁻¹' Set.range (Sigma.mk i)` is injective. It is — the pieces are
  nonempty and disjoint — and it has no consumer. **This bullet went on to be the reason
  `…SeparatedFiniteEtaleOver.finite_connectedComponents_left` is a `Finite` and not a
  cardinality**: that statement is the surjectivity of the same map, which is all a finiteness
  claim needs, and the injectivity it does not prove is what an equality of counts would need.
* **Nothing about the fibre functor or the fundamental group.** The decomposition theorem is read
  as a statement about a space and nothing here touches
  `…SeparatedFiniteEtaleOver.fintypeFiberFunctor` or the group
  `Oka/AnalyticSpace/FundamentalGroup.lean` builds from it; in particular **the number of pieces
  is not related to anything**, and the degree of the cover does not appear.
* **No `Homeomorph` compatible with the covers' own inclusions at this level.**
  `AlgebraicGeometry.LocallyRingedSpace.sigmaHomeoSigma_sigmaι_base` pins the mirror-tree
  homeomorphism against `CategoryTheory.Limits.Sigma.ι`, and
  `ComplexAnalytic.AnalyticSpace.sigmaHomeoSigma` inherits it up to the `rfl` named at the head of
  this docstring, and `ComplexAnalytic.AnalyticSpace.sigmaHomeoSigma_preimage_range` — added
  beside it in `Oka/AnalyticSpace/Sigma.lean` on 2026-09-20 — states the same compatibility one
  level down, against `ComplexAnalytic.AnalyticSpace.sigmaι`. **That is a level below the one this
  bullet is about.** What is still not stated is the corresponding equation for
  `…SeparatedFiniteEtaleOver.sigmaι`, whose underlying
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

**The last conjunct is one application of `Homeomorph.connectedComponent_sigma`**
(`Oka/Topology/Homeomorph/Lemmas.lean`), which is that statement at an arbitrary space
homeomorphic to a disjoint union of connected ones: the component of a point of such a disjoint
union is the member it lies in, `connectedComponent_sigmaMk`
(`Oka/Topology/Connected/Clopen.lean`), carried across by `Homeomorph.image_connectedComponent`,
which is in turn `Homeomorph.image_connectedComponentIn` read at `Set.univ`. **Nothing of that is
done here**: both steps are named lemmas of the mirror tree and this proof spends the first of
them and no Mathlib lemma at all.

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
  exact ⟨ULift.{u} ι, inferInstance, fun i ↦ f i.down,
    (SeparatedFiniteEtaleOver.homeoLeftOfIso
        (e.symm ≪≫ SeparatedFiniteEtaleOver.coprodIsoULift f)).trans
      (SeparatedFiniteEtaleOver.coprodLeftHomeoSigma fun i : ULift.{u} ι ↦ f i.down),
    inferInstance, fun a ↦ Homeomorph.connectedComponent_sigma _ a⟩

/-- **Such a cover has finitely many connected components.**

`Homeomorph.finite_connectedComponents_of_sigma` at the homeomorphism above: the index type is
finite and every piece is connected, so the map sending an index to the component of a point of
that piece is onto.

**This is a statement about `ConnectedComponents`, the quotient type, and the statement above is
not.** What is not said here is that the index type *is* the type of components — the pieces of a
decomposition may repeat as subsets in principle, and the module docstring's `## What is not here`
says what ruling that out would need. -/
theorem SeparatedFiniteEtaleOver.finite_connectedComponents_left
    (A : SeparatedFiniteEtaleOver.{u} X) :
    Finite (ConnectedComponents ((A.left : AnalyticSpace.{u}) : Type u)) := by
  obtain ⟨ι, hfin, g, e, hg, -⟩ :=
    SeparatedFiniteEtaleOver.exists_connectedComponent_decomposition A
  haveI := hfin
  haveI := hg
  exact e.finite_connectedComponents_of_sigma

end ComplexAnalytic.AnalyticSpace
