/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka
import OkaTest.FiniteMorphism

/-!
# Non-vacuity and sharpness of the analytic structure on a covering space

`Oka/AnalyticSpace/CoveringSpace.lean` builds a complex analytic structure on the source of a
local homeomorphism into a complex analytic space, and says the resulting morphism is finite étale
when the map is closed with finite fibres — a covering map with finite fibres being one such.
Neither statement says the hypotheses can hold at anything, and the second could be the first in
disguise if finiteness were free. This file measures both.

## The three things checked

* **`ComplexAnalytic.isFiniteEtale_sqCoveringSpaceHom`** — the hypotheses hold at the squaring map
  `z ↦ z²` of the punctured line, which `OkaTest/FiniteMorphism.lean` already knows is a covering
  map (`ComplexAnalytic.isCoveringMap_base_sq`) with fibres of exactly two points
  (`ComplexAnalytic.card_fiber_base_sq`). `ComplexAnalytic.card_fiber_sqCoveringSpaceHom` carries
  that count to the constructed morphism, so **the witness is a genuine two-sheeted cover** and
  not a bijection dressed up as one.
* **`ComplexAnalytic.isFiniteEtale_emptyCoveringSpaceHom`** — the empty space over the punctured
  line is finite étale here, which is the convention `Oka/AnalyticSpace/SigmaFiniteEtale.lean`
  argues for and this development is already committed to. It is checked rather than assumed
  because it is the case a reader expecting a surjectivity hypothesis will look for.
* **`ComplexAnalytic.not_isFinite_puncturedInclCoveringSpaceHom`** — **the hypothesis cannot be
  weakened to a local homeomorphism with finite fibres.** The inclusion `ℂ ∖ {0} ↪ ℂ` is an open
  embedding, hence a local homeomorphism, and its fibres have at most one point; the construction
  applies to it and `ComplexAnalytic.isLocalIso_puncturedInclCoveringSpaceHom` holds — but the
  morphism is not finite, because the inclusion is not a closed map. Without this the closedness
  hypothesis of `ComplexAnalytic.AnalyticSpace.isFinite_coveringSpaceHom_of_isClosedMap` could be
  redundant and nothing would say so. **The witness fails at closedness and at nothing else**, so
  it also says what the covering hypothesis of
  `ComplexAnalytic.AnalyticSpace.isFinite_coveringSpaceHom` was buying: that one field, and no
  other.

## One question that used to be asked three ways, and is now answered three ways

This section used to say that **nothing below compares the constructed structure with a structure
the source already had**, and listed three instances of that one question. All three are now
answered, by `ComplexAnalytic.AnalyticSpace.exists_iso_coveringSpace` and one hypothesis each:

* **the squaring map** — `ComplexAnalytic.exists_iso_sqCoveringSpace`, on
  `ComplexAnalytic.isLocalIso_sq` from `OkaTest/FiniteMorphism.lean`. The punctured line's own
  structure *is* `ComplexAnalytic.sqCoveringSpace`, over the punctured line;
* **the trivial `ι`-sheeted cover** — `ComplexAnalytic.exists_iso_sigmaFoldCoveringSpace`, on the
  instance `ComplexAnalytic.AnalyticSpace.isFiniteEtale_sigmaFold`, so
  `ComplexAnalytic.AnalyticSpace.sigma`'s own structure is the constructed one;
* **the open subspace** — `ComplexAnalytic.exists_iso_puncturedInclCoveringSpace`, on
  `ComplexAnalytic.AnalyticSpace.isLocalIso_ofRestrict`. The structure the third section puts on
  `ℂ ∖ {0}` is the open subspace's own.

**These are non-vacuity checks and not three theorems.** Each is one application of a statement
proved in `Oka/AnalyticSpace/CoveringSpace.lean`; what they establish is that its hypothesis
holds somewhere, and in particular at a morphism that is not an isomorphism — without which a
uniqueness theorem is indistinguishable from one whose hypotheses cannot be met. The first is the
sharp one: the squaring map is two-to-one, by `ComplexAnalytic.card_fiber_sqCoveringSpaceHom`
above, so the isomorphism there is not a repackaging of a bijection.

**What is still not compared is a structure arriving from outside `IsLocalIso`.** Every witness
above hands the uniqueness statement a morphism that is *already* a local isomorphism of analytic
spaces. A consumer holding only a topological covering map, a structure on its source and a
proof that the *base maps* agree still has an equality of carriers to cross, and
`Oka/AnalyticSpace/CoveringSpace.lean`'s `## What is not here` records that gap on its own side.

**No second finite étale example.** The squaring map is the only covering map with finite fibres
in this repository that is not a disjoint union, so there is one non-trivial witness and not two.
-/

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry TopCat Topology

universe u

noncomputable section

namespace ComplexAnalytic

/-! ### The squaring map of the punctured line, through the construction -/

/-- The punctured line, which is the analytic space both sides of `ComplexAnalytic.sq` live on. -/
abbrev puncturedLine : AnalyticSpace.{u} :=
  (AnalyticSpace.complexAffineSpace.{u} 1).restrict punctured.{u}

/-- **Every fibre of the squaring map is a finite set**, which is the half of
`ComplexAnalytic.AnalyticSpace.isFiniteEtale_coveringSpaceHom`'s hypothesis that
`ComplexAnalytic.isCoveringMap_base_sq` does not supply.

`ComplexAnalytic.finite_fiber_base_sq` in `OkaTest/FiniteMorphism.lean` is the same statement as
the class `Finite`, which is the spelling `ComplexAnalytic.AnalyticSpace.IsFinite` asks for;
`ComplexAnalytic.AnalyticSpace.isFinite_coveringSpaceHom` asks for the `Set.Finite` one, because
`IsCoveringMap.isClosedMap` does. `Set.toFinite` is the whole difference. -/
theorem setFinite_fiber_base_sq (y : puncturedLine.{u}) :
    (((ComplexAnalytic.sq.{u}).toLRSHom.base : puncturedLine.{u} → puncturedLine.{u}) ⁻¹'
      {y}).Finite :=
  haveI := finite_fiber_base_sq.{u} y
  Set.toFinite _

/-- **The complex analytic space the construction puts on the source of the squaring map.**

The underlying topological space is the punctured line's, and the structure sheaf is the inverse
image of the punctured line's along `z ↦ z²`. It is the source of the morphism the rest of this
section is about, by definition and not by a lemma: the arguments are the same three.

That it **is** the punctured line's own analytic structure, over the punctured line, is
`ComplexAnalytic.exists_iso_sqCoveringSpace` at the end of this file — a statement about this
`def` and not part of it. -/
def sqCoveringSpace : AnalyticSpace.{u} :=
  AnalyticSpace.coveringSpace puncturedLine.{u} (ComplexAnalytic.sq.{u}).toLRSHom.base
    isCoveringMap_base_sq.{u}.isLocalHomeomorph

/-- **The construction's morphism at the squaring map is finite étale** — the hypotheses of
`ComplexAnalytic.AnalyticSpace.isFiniteEtale_coveringSpaceHom` are jointly satisfiable, at a
covering map that is not a homeomorphism. -/
theorem isFiniteEtale_sqCoveringSpaceHom :
    AnalyticSpace.IsFiniteEtale
      (AnalyticSpace.coveringSpaceHom puncturedLine.{u} (ComplexAnalytic.sq.{u}).toLRSHom.base
        isCoveringMap_base_sq.{u}.isLocalHomeomorph) :=
  AnalyticSpace.isFiniteEtale_coveringSpaceHom _ _ isCoveringMap_base_sq.{u}
    setFinite_fiber_base_sq.{u}

/-- **Every fibre of the constructed morphism has two points**, so the witness above is a genuine
two-sheeted cover.

`ComplexAnalytic.card_fiber_base_sq` verbatim: the underlying map of
`ComplexAnalytic.AnalyticSpace.coveringSpaceHom` is the map it was built from, on the nose
(`ComplexAnalytic.AnalyticSpace.base_coveringSpaceHom`), so there is nothing to transport. Without
this the section above would be compatible with a one-sheeted cover, where finite étale is no
stronger than an isomorphism on carriers. -/
theorem card_fiber_sqCoveringSpaceHom (y : puncturedLine.{u}) :
    Nat.card ((AnalyticSpace.coveringSpaceHom puncturedLine.{u}
      (ComplexAnalytic.sq.{u}).toLRSHom.base
        isCoveringMap_base_sq.{u}.isLocalHomeomorph).toLRSHom.base ⁻¹' {y}) = 2 :=
  card_fiber_base_sq.{u} y

/-! ### The empty cover, which is finite étale here by a convention this file inherits -/

/-- The empty topological space, as the source of a cover of the punctured line. -/
def emptySpace : TopCat.{u} := TopCat.of (ULift.{u} Empty)

instance : IsEmpty emptySpace.{u} := inferInstanceAs (IsEmpty (ULift.{u} Empty))

/-- **The empty cover of the punctured line.** -/
def emptyToPuncturedLine :
    emptySpace.{u} ⟶ puncturedLine.{u}.toLocallyRingedSpace.toTopCat :=
  TopCat.ofHom ⟨fun e ↦ e.down.elim, continuous_of_discreteTopology⟩

/-- **The empty space over the punctured line is finite étale.**

`Oka/AnalyticSpace/SigmaFiniteEtale.lean` argues for this convention in terms — *"the empty space
over a non-empty one is finite étale here"* — and Mathlib agrees, since
`IsCoveringMap.of_isEmpty` is a theorem. It is checked here rather than assumed because a reader
who expects a surjectivity hypothesis on `p` will look for it, and the answer is that there is
none and that the construction is total. -/
theorem isFiniteEtale_emptyCoveringSpaceHom :
    AnalyticSpace.IsFiniteEtale
      (AnalyticSpace.coveringSpaceHom puncturedLine.{u} emptyToPuncturedLine.{u}
        (IsCoveringMap.of_isEmpty ⇑emptyToPuncturedLine.{u}).isLocalHomeomorph) :=
  AnalyticSpace.isFiniteEtale_coveringSpaceHom _ _
    (IsCoveringMap.of_isEmpty ⇑emptyToPuncturedLine.{u}) fun _ ↦ Set.toFinite _

/-! ### Sharpness: a local homeomorphism with finite fibres that is not finite -/

/-- The inclusion of the punctured line into the line, as a map of topological spaces. -/
def puncturedIncl :
    TopCat.of ↥(punctured.{u}) ⟶
      (AnalyticSpace.complexAffineSpace.{u} 1).toLocallyRingedSpace.toTopCat :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

theorem isOpenEmbedding_puncturedIncl : IsOpenEmbedding ⇑puncturedIncl.{u} :=
  punctured.{u}.isOpenEmbedding

theorem isLocalHomeomorph_puncturedIncl : IsLocalHomeomorph ⇑puncturedIncl.{u} :=
  isOpenEmbedding_puncturedIncl.{u}.isLocalHomeomorph

/-- **Every fibre of the inclusion has at most one point**, hence is finite: the inclusion is
injective. So the fibre half of `ComplexAnalytic.AnalyticSpace.IsFinite` holds and is not what
fails below. -/
theorem finite_fiber_puncturedIncl (y : AnalyticSpace.complexAffineSpace.{u} 1) :
    (⇑puncturedIncl.{u} ⁻¹' {y}).Finite :=
  Set.Subsingleton.finite fun _ ha _ hb ↦ Subtype.ext (ha.trans hb.symm)

/-- **The construction applies to the inclusion**: it is a local homeomorphism, which is all
`ComplexAnalytic.AnalyticSpace.coveringSpace` asks for, and the resulting morphism is a local
isomorphism.

The instance is `ComplexAnalytic.AnalyticSpace.isLocalIso_coveringSpaceHom`, stated here so that
the failure of finiteness below is measured against a morphism that has everything else. -/
theorem isLocalIso_puncturedInclCoveringSpaceHom :
    AnalyticSpace.IsLocalIso
      (AnalyticSpace.coveringSpaceHom (AnalyticSpace.complexAffineSpace.{u} 1)
        puncturedIncl.{u} isLocalHomeomorph_puncturedIncl.{u}) :=
  inferInstance

/-- **The punctured line is not a closed subset of the line.**

`{0}` is not open in `ℂ`, since the punctured neighbourhood filter at `0` is not `⊥`; the passage
from the one-variable affine space to `ℂ` is the continuous map `c ↦ (fun _ ↦ c)`. This is
`ComplexAnalytic.not_isClosedMap_base_proj`'s argument, which reaches the same three steps from a
hyperbola instead of from an inclusion. -/
theorem not_isClosed_punctured :
    ¬ IsClosed ({q | (q : ULift.{u} (Fin 1) → ℂ) (ULift.up 0) ≠ 0} :
      Set (AnalyticSpace.complexAffineSpace.{u} 1)) := by
  intro hcl
  have hcompl : ({q | (q : ULift.{u} (Fin 1) → ℂ) (ULift.up 0) ≠ 0} :
      Set (AnalyticSpace.complexAffineSpace.{u} 1))ᶜ =
      {q | (q : ULift.{u} (Fin 1) → ℂ) (ULift.up 0) = 0} :=
    Set.ext fun _ ↦ not_not
  have hopen : IsOpen ({q | (q : ULift.{u} (Fin 1) → ℂ) (ULift.up 0) = 0} :
      Set (AnalyticSpace.complexAffineSpace.{u} 1)) := hcompl ▸ hcl.isOpen_compl
  have hdiag : Continuous fun c : ℂ ↦ (fun _ ↦ c : AnalyticSpace.complexAffineSpace.{u} 1) :=
    continuous_pi fun _ ↦ continuous_id
  have hzero : IsOpen ({0} : Set ℂ) := hopen.preimage hdiag
  have hb : (𝓝[≠] (0 : ℂ)) = ⊥ := by rwa [← isOpen_singleton_iff_punctured_nhds]
  exact (inferInstance : (𝓝[≠] (0 : ℂ)).NeBot).ne hb

/-- **The inclusion of the punctured line is not a closed map**: the image of the whole space is
the punctured line, which `ComplexAnalytic.not_isClosed_punctured` says is not closed. -/
theorem not_isClosedMap_puncturedIncl : ¬ IsClosedMap ⇑puncturedIncl.{u} := by
  intro hclosed
  have h := hclosed _ isClosed_univ
  have hrange : Set.range ⇑puncturedIncl.{u} =
      ({q | (q : ULift.{u} (Fin 1) → ℂ) (ULift.up 0) ≠ 0} :
        Set (AnalyticSpace.complexAffineSpace.{u} 1)) :=
    Set.ext fun q ↦ ⟨fun ⟨z, hz⟩ ↦ hz ▸ (mem_punctured_iff.{u} _).1 z.2,
      fun hq ↦ ⟨⟨q, (mem_punctured_iff.{u} _).2 hq⟩, rfl⟩⟩
  rw [Set.image_univ, hrange] at h
  exact not_isClosed_punctured.{u} h

/-- **The construction's morphism at the inclusion is not finite**, though it is a local
isomorphism with finite fibres.

So the closedness hypothesis of
`ComplexAnalytic.AnalyticSpace.isFinite_coveringSpaceHom_of_isClosedMap` is not redundant:
`IsLocalHomeomorph` together with finite fibres does **not** give
`ComplexAnalytic.AnalyticSpace.IsFinite`. The underlying map of
`ComplexAnalytic.AnalyticSpace.coveringSpaceHom` is the inclusion on the nose, so the closed half
fails for the reason above — **and that is the only half that fails**, which is the same fact read
as a statement about the covering-map form: what `IsCoveringMap.isClosedMap` supplies to
`ComplexAnalytic.AnalyticSpace.isFinite_coveringSpaceHom` is closedness, and closedness is what
this space does not have. -/
theorem not_isFinite_puncturedInclCoveringSpaceHom :
    ¬ AnalyticSpace.IsFinite
      (AnalyticSpace.coveringSpaceHom (AnalyticSpace.complexAffineSpace.{u} 1)
        puncturedIncl.{u} isLocalHomeomorph_puncturedIncl.{u}) := fun h ↦
  not_isClosedMap_puncturedIncl.{u} h.isClosedMap

/-- **And so the inclusion is not a covering map**, which is the same fact read as a statement
about the map rather than about the morphism: a covering map with finite fibres is closed
(`IsCoveringMap.isClosedMap`) and this one is not. -/
theorem not_isCoveringMap_puncturedIncl : ¬ IsCoveringMap ⇑puncturedIncl.{u} := fun h ↦
  not_isClosedMap_puncturedIncl.{u} (h.isClosedMap finite_fiber_puncturedIncl.{u})

/-! ### Non-vacuity of uniqueness: three structures that were already there -/

/-- **The punctured line's own structure is the one the construction puts on the source of the
squaring map**, and compatibly with the two maps to the punctured line.

`ComplexAnalytic.isLocalIso_sq` in `OkaTest/FiniteMorphism.lean` is the only input;
`ComplexAnalytic.AnalyticSpace.exists_iso_coveringSpace` is the whole proof. This is the sharp
witness of the three, because `ComplexAnalytic.card_fiber_sqCoveringSpaceHom` above puts every
fibre at **2**: the isomorphism produced here is not a bijection dressed up as a cover.

Note which space is on the left. `ComplexAnalytic.sqCoveringSpace` is the *constructed* space and
`ComplexAnalytic.puncturedLine` is the source of `ComplexAnalytic.sq`; that they are isomorphic
over the punctured line is exactly what the module docstring used to record as unchecked. -/
theorem exists_iso_sqCoveringSpace :
    ∃ e : puncturedLine.{u} ≅ sqCoveringSpace.{u},
      e.hom ≫ AnalyticSpace.coveringSpaceHom puncturedLine.{u} (sq.{u}).toLRSHom.base
        isCoveringMap_base_sq.{u}.isLocalHomeomorph = sq.{u} :=
  haveI := isLocalIso_sq.{u}
  AnalyticSpace.exists_iso_coveringSpace sq.{u}

/-- **The structure the construction puts on the source of the trivial `ι`-sheeted cover is
`ComplexAnalytic.AnalyticSpace.sigma`'s own**, over `X`.

The hypothesis is found by instance search from
`ComplexAnalytic.AnalyticSpace.isFiniteEtale_sigmaFold`, whose `isLocalIso` field carries
`attribute [instance]`. It holds for every base and every finite index type, so — unlike the
squaring map — this witness is a family and not a point, and at `ι` empty it is the empty cover
of the second section read through uniqueness. -/
theorem exists_iso_sigmaFoldCoveringSpace (ι : Type u) [Finite ι] (X : AnalyticSpace.{u}) :
    ∃ e : AnalyticSpace.sigma (fun _ : ι ↦ X) ≅
        AnalyticSpace.coveringSpace X (AnalyticSpace.sigmaFold ι X).toLRSHom.base
          (AnalyticSpace.IsLocalIso.isLocalHomeomorph (f := AnalyticSpace.sigmaFold ι X)),
      e.hom ≫ AnalyticSpace.coveringSpaceHom X (AnalyticSpace.sigmaFold ι X).toLRSHom.base
          (AnalyticSpace.IsLocalIso.isLocalHomeomorph (f := AnalyticSpace.sigmaFold ι X)) =
        AnalyticSpace.sigmaFold ι X :=
  AnalyticSpace.exists_iso_coveringSpace _

/-- **The underlying map of the open-subspace inclusion is
`ComplexAnalytic.puncturedIncl`**, on the nose — which is what makes the statement below about
the same map as the sharpness section above it. -/
theorem base_ofRestrict_punctured :
    ((AnalyticSpace.complexAffineSpace.{u} 1).ofRestrict punctured.{u}).toLRSHom.base =
      puncturedIncl.{u} :=
  rfl

/-- **The structure the construction puts on `ℂ ∖ {0}` over `ℂ` is the open subspace's own**, over
the line.

The hypothesis is `ComplexAnalytic.AnalyticSpace.isLocalIso_ofRestrict`, found by instance search.
Together with `ComplexAnalytic.not_isFinite_puncturedInclCoveringSpaceHom` above this says
something the other two witnesses cannot: the uniqueness statement asks
`ComplexAnalytic.AnalyticSpace.IsLocalIso` and **not** finiteness, and here is a morphism that
satisfies the first and fails the second while the identification still holds.

The covering space is spelled at the inclusion's own base map rather than at
`ComplexAnalytic.puncturedIncl`; `ComplexAnalytic.base_ofRestrict_punctured` is that they are the
same map, and stating it that way is what keeps the elaboration cheap — asking Lean to unify the
two spellings inside the statement of the existential runs it into a deterministic heartbeat
timeout — reported at `whnf` or at `isDefEq` depending on how the unification is phrased, and
measured in both shapes rather than feared. -/
theorem exists_iso_puncturedInclCoveringSpace :
    ∃ e : puncturedLine.{u} ≅
        AnalyticSpace.coveringSpace (AnalyticSpace.complexAffineSpace.{u} 1)
          ((AnalyticSpace.complexAffineSpace.{u} 1).ofRestrict punctured.{u}).toLRSHom.base
          (AnalyticSpace.IsLocalIso.isLocalHomeomorph
            (f := (AnalyticSpace.complexAffineSpace.{u} 1).ofRestrict punctured.{u})),
      e.hom ≫ AnalyticSpace.coveringSpaceHom (AnalyticSpace.complexAffineSpace.{u} 1)
          ((AnalyticSpace.complexAffineSpace.{u} 1).ofRestrict punctured.{u}).toLRSHom.base
          (AnalyticSpace.IsLocalIso.isLocalHomeomorph
            (f := (AnalyticSpace.complexAffineSpace.{u} 1).ofRestrict punctured.{u})) =
        (AnalyticSpace.complexAffineSpace.{u} 1).ofRestrict punctured.{u} :=
  AnalyticSpace.exists_iso_coveringSpace _

end ComplexAnalytic

end
