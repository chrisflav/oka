/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Analytification.StandardEtaleLocalIsoBase
import Oka.Analytification.StandardEtaleFiniteness
import Oka.AnalyticSpace.PullbackOpen

/-!
# The analytification of a standard étale morphism over a presented base is finite over an open

`Oka/Analytification/StandardEtaleFiniteness.lean` is this statement at an **empty** base
presentation, where the target is `ℂ^n`; `Oka/Analytification/StandardEtaleLocalIsoBase.lean` is
the **local-isomorphism** half at every `k`, where the target is `X^an`. This file is the
finiteness half at every `k`, and its target is `X^an` for the reason that file gives: composed
with `ComplexAnalytic.analytificationInclHom` the statement is about `ℂ^n` and is false at `k ≥ 1`
for every base with a proper non-empty zero locus.

## Why this is not the transport across a cut-down that was predicted for it

The `k ≥ 1` finiteness half was expected to be the `k = 0` one carried across the square of
`ComplexAnalytic.ofRestrict_comp_analytificationMap_comp_analytificationInclHom`, restricted on
both sides, by a finiteness counterpart of
`ComplexAnalytic.AnalyticSpace.isLocalIso_of_isCutOutBy_pullbackΓ`. **That route exists and is not
the one below, because the `X^an`-level input the split needs is already a theorem at every `k`**:
`ComplexAnalytic.isFinite_analytificationMap_hypersurfacePresHom`
(`Oka/Analytification/HypersurfaceFinite.lean`) says the analytification of `A ⟶ A[X] ⧸ (F)` is
finite for `F` monic, and that file's section variable is `(g : Fin k → _)` with `k` free. Nothing
below carries a class across a square and nothing below reads a cut-out datum.

## The route, which is the `k = 0` file's three steps with one of them free

* **The factorisation.** `ComplexAnalytic.etaleAnalytificationIso_hom_comp`, which is general in
  `k`, writes the étale cover as the isomorphism, the open immersion of `D(G)`, and the
  hypersurface's structure map **to `X^an`**;
  `ComplexAnalytic.AnalyticSpace.restrictHom_comp` splits the restriction of that composite in
  two.
* **The second factor is free.** `ComplexAnalytic.AnalyticSpace.isFinite_restrictHom` is an
  instance, so the restriction of the theorem quoted above needs nothing. **At `k = 0` this step
  is not free**: there the statement being restricted is about the composite to `ℂ^n`, so
  `Oka/Analytification/StandardEtaleFiniteness.lean` has to go through
  `ComplexAnalytic.isFinite_restrictHom_hypersurface_comp_proj` and
  `ComplexAnalytic.hypersurfacePresentation_empty` first. This half of the `k ≥ 1` proof is
  shorter than the `k = 0` one.
* **The first factor is the geometry**, and it is
  `ComplexAnalytic.AnalyticSpace.isFinite_restrictHom_of_subset_range` at the containment below —
  the same two hypotheses, discharged the same way, as at `k = 0`.

## The containment is the `k = 0` one read through the comparison

`ComplexAnalytic.hypersurfaceCommonZeroImage` is defined at the hypersurface of `F` **alone**, a
`k = 0` object, so the `k ≥ 1` containment cannot be stated at a new bad set without defining one.
It is not stated at a new one: `ComplexAnalytic.hypersurfaceCompare` maps the `k ≥ 1` hypersurface
into `{F = 0}` and `ComplexAnalytic.hypersurfaceCompare_comp` says it is a morphism over
`ℂ^(n + 1)`, so a point of the first has the same underlying point of `ℂ^(n + 1)` as its image in
the second — hence the same value of `G` and the same image in `ℂ^n`. **The `k = 0` containment
therefore applies to that image verbatim**, and
`ComplexAnalytic.map_le_localisationOpen_of_subset_compl_base` is
`ComplexAnalytic.map_le_localisationOpen_of_subset_compl` at the empty base plus that transport.
`ComplexAnalytic.hypersurfaceOnly` is *defined* as
`ComplexAnalytic.hypersurfacePresentation` over the empty base, so no spelling is crossed between
the two statements.

## What the import costs, measured rather than asserted

`Oka.Analytification.StandardEtaleLocalIsoBase` and `Oka.Analytification.StandardEtaleFiniteness`
are the two halves this file joins and neither is avoidable. The third import,
`Oka.AnalyticSpace.PullbackOpen`, is the one that carries
`ComplexAnalytic.AnalyticSpace.isFinite_restrictHom`, and **over the other two it costs exactly
one module, which is itself.** At the commit that adds this file, the transitive closure of the
first two — walked over the `import` lines of this repository **and of Mathlib**, through
`scripts/import_cost.py`'s comment stripper — is **3557** modules, and **3558** with the third
edge added; this file's own closure is **3559** and
`Oka/Analytification/StandardEtaleFiniteEtaleBase.lean`'s is **3560**, each adding only itself.
`Mathlib/Topology/LocalAtTarget.lean` is the only Mathlib module
`Oka/AnalyticSpace/PullbackOpen.lean` names, and it is in the closure of **each** of the other two
already — nine edges from `Oka/Analytification/StandardEtaleFiniteness.lean`, through
`Oka/Regular.lean` and `Mathlib/RingTheory/Ideal/KrullsHeightTheorem.lean`.

**A closure walked over this repository's edges alone answers a different question and gets this
one wrong.** It counts a Mathlib module named by the new import as new without asking whether a
module already in the closure reaches it, and here that is exactly what happens: over repository
edges alone the third import appears to cost two modules rather than one. **The figure a marginal
import cost states is a fact about the baseline**, so the baseline is named here and the walk is
said to cross into Mathlib.

**The pair adds nothing to `import Oka` but the two of them**: by
`Lean.Environment.allImportedModuleNames`, `import Oka` is **5538** modules at the commit this
file is cut from and **5540** at the commit that adds it.

## Main results

- `ComplexAnalytic.map_le_localisationOpen_of_subset_compl_base`: **above an open subset of `ℂ^n`
  avoiding the bad set, the hypersurface over a presented base lies inside `D(G)`** — the `k = 0`
  containment at every `k`.
- `ComplexAnalytic.isFinite_restrictHom_analytificationMap_etalePresHom`: **the analytification of
  a standard étale morphism over a presented base, restricted over the part of `X^an` lying above
  such an open subset, is finite over that part.**
- `ComplexAnalytic.isFinite_restrictHom_analytificationMap_etalePresHom_compl`: the same at the
  largest such open subset there is, the complement of the bad set.

## What is not here

* **No unrestricted finiteness**, and there never will be: it is **false**, at `k = 0` already.
  `Oka/Analytification/MonicHypersurface.lean` carries the witness and
  `ComplexAnalytic.not_isFiniteEtale_condEtaleProj` (`OkaTest/StandardEtaleNotFinite.lean`)
  compiles it. The restriction below is in the statement because the conclusion needs it and not
  because the proof is weak.
* **Nothing about the composite to `ℂ^n` at `k ≥ 1`.** That is a different statement and
  `Oka/Analytification/StandardEtaleLocalIso.lean` proves its local-isomorphism half false for a
  base with a proper non-empty zero locus; this file does not touch it. The open subset below is
  an open subset of `X^an` for that reason, and it is the preimage of an open subset of `ℂ^n`
  because the bad set lives in `ℂ^n` and nothing here defines a subset of `X^an` directly.
* **No `ComplexAnalytic.AnalyticSpace.IsFiniteEtale`**, which is
  `Oka/Analytification/StandardEtaleFiniteEtaleBase.lean`'s. Nothing below reads a
  `StandardEtalePair`, and the theorems below therefore hold at every pair
  `(F, G)` with `F` monic and not only at étale ones — which is the same reason
  `Oka/Analytification/StandardEtaleFiniteness.lean` gives for the `k = 0` split, said of the
  file and not of one theorem.
* **No claim about how large the open subset is.** `Oka/Analytification/OpenBaseFiniteness.lean`
  exhibits a pair at which the bad set is all of `ℂ^n` and one at which it is proper; neither is a
  statement about `k ≥ 1` and neither is restated here.
* **Nothing about a general étale morphism.** Zariski-local standardness and the gluing are a
  separate construction that nothing starts.
-/

open CategoryTheory MvPolynomial AlgebraicGeometry TopologicalSpace Opposite Topology

universe u

namespace ComplexAnalytic

noncomputable section

variable {n k : ℕ} (g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ)
  (F G : Polynomial (MvPolynomial (ULift.{u} (Fin n)) ℂ))

/-! ### The containment, read through the comparison with the hypersurface of `F` alone -/

/-- **Above an open subset of `ℂ^n` avoiding the bad set, the hypersurface over a presented base
lies inside `D(G)`.**

`ComplexAnalytic.map_le_localisationOpen_of_subset_compl` is this statement at the empty base
presentation, and `ComplexAnalytic.hypersurfaceOnly` is *defined* as
`ComplexAnalytic.hypersurfacePresentation` there, so what has to be crossed is the comparison and
not a spelling. `ComplexAnalytic.hypersurfaceCompare_comp` says the comparison is a morphism over
`ℂ^(n + 1)`, which gives both halves of the crossing at once: the point upstairs and its image
have the same underlying point of `ℂ^(n + 1)`, so they have the same image in `ℂ^n` — which is
what puts the image in the `k = 0` statement's open — and the same value of `G`, which is what
carries the conclusion back.

**`G` is read only through that value and `F` only through the space**, exactly as at `k = 0`; no
hypothesis is placed on either polynomial here. -/
theorem map_le_localisationOpen_of_subset_compl_base {V : Opens (ULift.{u} (Fin n) → ℂ)}
    (hV : (V : Set (ULift.{u} (Fin n) → ℂ)) ⊆ (hypersurfaceCommonZeroImage.{u} F G)ᶜ) :
    (Opens.map (analytificationInclHom.{u} (hypersurfacePresentation.{u} g
          ((lastVarPolyEquiv.{u} n).symm F)) ≫
        AnalyticSpace.proj.{u} n).toLRSHom.base).obj V ≤
      localisationOpen.{u} (hypersurfacePresentation.{u} g ((lastVarPolyEquiv.{u} n).symm F))
        ((lastVarPolyEquiv.{u} n).symm G) := by
  intro y hy
  have hbase : (analytificationInclHom.{u} (hypersurfaceOnly.{u} (n := n)
        ((lastVarPolyEquiv.{u} n).symm F))).toLRSHom.base
        ((hypersurfaceCompare.{u} g ((lastVarPolyEquiv.{u} n).symm F)).toLRSHom.base y)
      = (analytificationInclHom.{u} (hypersurfacePresentation.{u} g
          ((lastVarPolyEquiv.{u} n).symm F))).toLRSHom.base y := by
    conv_rhs => rw [← hypersurfaceCompare_comp.{u} g ((lastVarPolyEquiv.{u} n).symm F)]
    rfl
  have hy' : (hypersurfaceCompare.{u} g ((lastVarPolyEquiv.{u} n).symm F)).toLRSHom.base y ∈
      (Opens.map (analytificationInclHom.{u} (hypersurfaceOnly.{u} (n := n)
          ((lastVarPolyEquiv.{u} n).symm F)) ≫
        AnalyticSpace.proj.{u} n).toLRSHom.base).obj V := by
    have hcomp : ((analytificationInclHom.{u} (hypersurfaceOnly.{u} (n := n)
          ((lastVarPolyEquiv.{u} n).symm F)) ≫
        AnalyticSpace.proj.{u} n).toLRSHom.base)
        ((hypersurfaceCompare.{u} g ((lastVarPolyEquiv.{u} n).symm F)).toLRSHom.base y)
        = ((analytificationInclHom.{u} (hypersurfacePresentation.{u} g
            ((lastVarPolyEquiv.{u} n).symm F)) ≫ AnalyticSpace.proj.{u} n).toLRSHom.base) y := by
      conv_rhs => rw [← hypersurfaceCompare_comp.{u} g ((lastVarPolyEquiv.{u} n).symm F)]
      rfl
    change ((analytificationInclHom.{u} (hypersurfaceOnly.{u} (n := n)
        ((lastVarPolyEquiv.{u} n).symm F)) ≫ AnalyticSpace.proj.{u} n).toLRSHom.base)
        ((hypersurfaceCompare.{u} g ((lastVarPolyEquiv.{u} n).symm F)).toLRSHom.base y) ∈ V
    rw [hcomp]
    exact hy
  have h0 := map_le_localisationOpen_of_subset_compl.{u}
    (![] : Fin 0 → MvPolynomial (ULift.{u} (Fin n)) ℂ) F G hV hy'
  rw [mem_localisationOpen_iff] at h0 ⊢
  have hpt : ((hypersurfaceCompare.{u} g ((lastVarPolyEquiv.{u} n).symm F)).toLRSHom.base y).1.1
      = (y.1.1 : ULift.{u} (Fin (n + 1)) → ℂ) := hbase
  exact hpt ▸ h0

/-! ### The finiteness of the standard étale analytification over a presented base -/

/-- **The analytification of a standard étale morphism over a presented base, restricted over the
part of `X^an` lying above an open subset of `ℂ^n` on which the inversion is vacuous, is finite
over that part.**

The remaining half of the `k ≥ 1` line, whose local-isomorphism half is
`ComplexAnalytic.isLocalIso_analytificationMap_etalePresHom`
(`Oka/Analytification/StandardEtaleLocalIsoBase.lean`).

`ComplexAnalytic.etaleAnalytificationIso_hom_comp` writes the cover as the isomorphism, the open
immersion of `D(G)`, and the structure map of the hypersurface to `X^an`;
`ComplexAnalytic.AnalyticSpace.restrictHom_comp` splits the restriction of that composite.
`ComplexAnalytic.isFinite_analytificationMap_hypersurfacePresHom` — **which is already stated at
every `k`** — and the instance `ComplexAnalytic.AnalyticSpace.isFinite_restrictHom` give the
second factor with nothing to do, and
`ComplexAnalytic.AnalyticSpace.isFinite_restrictHom_of_subset_range` gives the first from the
embedding and the containment above.

**The open subset is the preimage of `V` and not `V`**, because at `k ≥ 1` the morphism's target
is `X^an`; `ComplexAnalytic.analytificationMap_hypersurfacePresHom_comp` is what identifies the
preimage of that preimage with the open the containment is stated at, and it is an equality of
opens rather than a rewriting of a morphism.

**`ComplexAnalytic.AnalyticSpace.isFinite_comp` and
`ComplexAnalytic.AnalyticSpace.isFinite_restrictHom` are both applied by name**, for the reason
`Oka/Analytification/StandardEtaleFiniteness.lean` records of the first: the facts are about
`ComplexAnalytic.AnalyticSpace.restrictHom` at opens the goal spells through `Opens.map`, and
instance search does not close the goal from them — measured here too, *"failed to synthesize
instance"* on the second factor when it is left to `inferInstance`. -/
theorem isFinite_restrictHom_analytificationMap_etalePresHom (hF : F.Monic)
    (V : Opens (ULift.{u} (Fin n) → ℂ))
    (hV : (V : Set (ULift.{u} (Fin n) → ℂ)) ⊆ (hypersurfaceCommonZeroImage.{u} F G)ᶜ) :
    AnalyticSpace.IsFinite (AnalyticSpace.restrictHom
      (analytificationMap.{u} (etalePresHom.{u} g ((lastVarPolyEquiv.{u} n).symm F)
        ((lastVarPolyEquiv.{u} n).symm G)))
      ((Opens.map (analytificationInclHom.{u} g).toLRSHom.base).obj V)) := by
  rw [← etaleAnalytificationIso_hom_comp.{u} g ((lastVarPolyEquiv.{u} n).symm F)
      ((lastVarPolyEquiv.{u} n).symm G), ← Category.assoc, AnalyticSpace.restrictHom_comp]
  haveI := isFinite_analytificationMap_hypersurfacePresHom.{u} g F hF
  have hW : (Opens.map (AnalyticSpace.Hom.toLRSHom
        (analytificationMap.{u} (hypersurfacePresHom.{u} g
          ((lastVarPolyEquiv.{u} n).symm F)))).base).obj
      ((Opens.map (analytificationInclHom.{u} g).toLRSHom.base).obj V)
      = (Opens.map (analytificationInclHom.{u} (hypersurfacePresentation.{u} g
          ((lastVarPolyEquiv.{u} n).symm F)) ≫ AnalyticSpace.proj.{u} n).toLRSHom.base).obj V := by
    rw [← analytificationMap_hypersurfacePresHom_comp.{u} g ((lastVarPolyEquiv.{u} n).symm F)]
    rfl
  have hopen : AnalyticSpace.IsFinite (AnalyticSpace.restrictHom
      ((etaleAnalytificationIso.{u} g ((lastVarPolyEquiv.{u} n).symm F)
            ((lastVarPolyEquiv.{u} n).symm G)).hom ≫
        (AnalyticSpace.analytification.{u} (hypersurfacePresentation.{u} g
          ((lastVarPolyEquiv.{u} n).symm F))).ofRestrict
          (localisationOpen.{u} (hypersurfacePresentation.{u} g ((lastVarPolyEquiv.{u} n).symm F))
            ((lastVarPolyEquiv.{u} n).symm G)))
      ((Opens.map (AnalyticSpace.Hom.toLRSHom
          (analytificationMap.{u} (hypersurfacePresHom.{u} g
            ((lastVarPolyEquiv.{u} n).symm F)))).base).obj
        ((Opens.map (analytificationInclHom.{u} g).toLRSHom.base).obj V))) := by
    refine AnalyticSpace.isFinite_restrictHom_of_subset_range ?_ ?_
    · exact (localisationOpen.{u} (hypersurfacePresentation.{u} g
        ((lastVarPolyEquiv.{u} n).symm F))
          ((lastVarPolyEquiv.{u} n).symm G)).isOpenEmbedding.isEmbedding.comp
        (LocallyRingedSpace.homeoOfIso (AnalyticSpace.forgetToLocallyRingedSpace.{u}.mapIso
          (etaleAnalytificationIso.{u} g ((lastVarPolyEquiv.{u} n).symm F)
            ((lastVarPolyEquiv.{u} n).symm G)))).isEmbedding
    · intro y hy
      rw [hW] at hy
      obtain ⟨z, hz⟩ := (LocallyRingedSpace.homeoOfIso
        (AnalyticSpace.forgetToLocallyRingedSpace.{u}.mapIso
          (etaleAnalytificationIso.{u} g ((lastVarPolyEquiv.{u} n).symm F)
            ((lastVarPolyEquiv.{u} n).symm G)))).surjective
        ⟨y, map_le_localisationOpen_of_subset_compl_base.{u} g F G hV hy⟩
      exact ⟨z, congrArg Subtype.val hz⟩
  haveI hbase := AnalyticSpace.isFinite_restrictHom
    (analytificationMap.{u} (hypersurfacePresHom.{u} g ((lastVarPolyEquiv.{u} n).symm F)))
    ((Opens.map (analytificationInclHom.{u} g).toLRSHom.base).obj V)
  exact @AnalyticSpace.isFinite_comp _ _ _ _ _ hopen hbase

/-- **The same over the largest open subset of `ℂ^n` there is**, the complement of the bad set.

`ComplexAnalytic.isClosed_hypersurfaceCommonZeroImage` is what makes that complement open, and the
theorem above at `subset_rfl` is the whole proof. Stated for the reason the `k = 0` file gives of
its own: the theorem above quantifies over `V` and a reader wants to know the quantification is
not empty of content. **It says nothing about whether the complement is non-empty**, and nothing
below does. -/
theorem isFinite_restrictHom_analytificationMap_etalePresHom_compl (hF : F.Monic) :
    AnalyticSpace.IsFinite (AnalyticSpace.restrictHom
      (analytificationMap.{u} (etalePresHom.{u} g ((lastVarPolyEquiv.{u} n).symm F)
        ((lastVarPolyEquiv.{u} n).symm G)))
      ((Opens.map (analytificationInclHom.{u} g).toLRSHom.base).obj
        ⟨(hypersurfaceCommonZeroImage.{u} F G)ᶜ,
          (isClosed_hypersurfaceCommonZeroImage.{u} F G hF).isOpen_compl⟩)) :=
  isFinite_restrictHom_analytificationMap_etalePresHom.{u} g F G hF _ subset_rfl

end

end ComplexAnalytic
