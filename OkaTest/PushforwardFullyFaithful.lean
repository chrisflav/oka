/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka

/-!
# Non-vacuity of full faithfulness of the pushforward

`TopCat.Presheaf.pushforwardFullyFaithful` is stated for a variable inducing map. This file
elaborates it at the embedding the development actually needs — the inclusion
`AlgebraicGeometry.LocallyRingedSpace.zeroLocusι` of the zero locus of a family of global
sections, whose `IsClosedEmbedding` is `isClosedEmbedding_zeroLocusι` — and at the node
`{z ∈ ℂ² | z₀ z₁ = 0}`, where the sheaves involved are the structure sheaves of a genuine
singular complex analytic space rather than variables.

The `simp` lemma `TopCat.Presheaf.pushforwardHomEquiv_apply` in the library already rules out the
other way this could be vacuous: the equivalence's forward map is the pushforward itself, not some
unrelated bijection between hom-sets that happen to have the same cardinality.
-/

open CategoryTheory Limits TopologicalSpace Opposite AlgebraicGeometry ComplexAnalytic

universe u

noncomputable section

variable {Y : LocallyRingedSpace.{u}} {κ : Type u} (g : κ → Y.presheaf.obj (op ⊤))

/-- At the inclusion of a zero locus: morphisms of presheaves on the zero locus are the same as
morphisms of their pushforwards to the ambient space. -/
example (F G : (Y.zeroLocusSpace g).Presheaf CommRingCat.{u}) :
    (F ⟶ G) ≃ ((Y.zeroLocusι g) _* F ⟶ (Y.zeroLocusι g) _* G) :=
  TopCat.Presheaf.pushforwardHomEquiv _ (Y.isClosedEmbedding_zeroLocusι g).isInducing F G

/-- The same for sheaves, at the same embedding. -/
example (F G : (Y.zeroLocusSpace g).Sheaf CommRingCat.{u}) :
    (F ⟶ G) ≃
      ((TopCat.Sheaf.pushforward CommRingCat.{u} (Y.zeroLocusι g)).obj F ⟶
        (TopCat.Sheaf.pushforward CommRingCat.{u} (Y.zeroLocusι g)).obj G) :=
  TopCat.Sheaf.pushforwardHomEquiv _ (Y.isClosedEmbedding_zeroLocusι g).isInducing F G

/-- **The structure sheaf of the node determines its endomorphisms downstairs.** At the node
`{z ∈ ℂ² | z₀ z₁ = 0}`, endomorphisms of the structure sheaf are the same as endomorphisms of
its pushforward to `ℂ²`. This is the instance the mapping property of
`ComplexAnalytic.IsCutOutBy` consumes. -/
example :
    (nodeAmbient.{u}.zeroLocusPresheaf nodeSection.{u} ⟶
        nodeAmbient.{u}.zeroLocusPresheaf nodeSection.{u}) ≃
      ((nodeAmbient.{u}.zeroLocusι nodeSection.{u}) _*
          nodeAmbient.{u}.zeroLocusPresheaf nodeSection.{u} ⟶
        (nodeAmbient.{u}.zeroLocusι nodeSection.{u}) _*
          nodeAmbient.{u}.zeroLocusPresheaf nodeSection.{u}) :=
  TopCat.Presheaf.pushforwardHomEquiv _
    (nodeAmbient.{u}.isClosedEmbedding_zeroLocusι nodeSection.{u}).isInducing _ _

/-- The forward map is the pushforward, checked at the concrete embedding rather than only in
the abstract statement. -/
example (F G : (Y.zeroLocusSpace g).Presheaf CommRingCat.{u}) (σ : F ⟶ G) :
    TopCat.Presheaf.pushforwardHomEquiv _ (Y.isClosedEmbedding_zeroLocusι g).isInducing F G σ =
      (TopCat.Presheaf.pushforward CommRingCat.{u} (Y.zeroLocusι g)).map σ :=
  rfl
