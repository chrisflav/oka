/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka
import OkaTest.AnalytificationDistinguishedOpen

/-!
# Non-vacuity of the distinguished-open cover

`ComplexAnalytic.isOpenCover_localisationOpen` is satisfied by the one-member family `f = 1`:
`ComplexAnalytic.localisationOpen_one` says `D(1) = ⊤`, and `Ideal.span {1} = ⊤`. Read at that
family every statement in `Oka/Analytification/DistinguishedOpenCover.lean` is about the identity
cover, and `ComplexAnalytic.isLocalIso_of_localisationProj_comp` says nothing at all. **What
rules that reading out is a cover with more than one member, every member of which is a proper
open subset**, and that is what is built here.

The space is the node `z₀ z₁ = 0` that `OkaTest/AnalytificationDistinguishedOpen.lean` and
`OkaTest/OpenSubspace.lean` already work over, and the family is `z₀` and `1 - z₀`. They sum to
`1`, so their classes generate the unit ideal over any base at all — **the node plays no part in
the covering condition and is there to make the members proper**, which is the half that needs a
point:

* `D(z₀)` misses the origin, which is `localisationOpen_nodePres_ne_top` in the file this one
  imports; it is the punctured first axis, by `localisationOpen_nodePres_eq_nodeAxis`.
* `D(1 - z₀)` misses `axisPoint 0`, the point `(1, 0)`, where `z₀` is `1`.

So `isOpenCover_nodeCover` is a two-member cover of the node by two proper opens, neither of
which is the whole space, and the cover is not the trivial one.

**What is not checked here.** No morphism is run through
`ComplexAnalytic.isLocalIso_of_localisationProj_comp`: nothing below exhibits a `φ` out of the
node that is a local isomorphism on each member and is then concluded to be one, and the
repository has no such `φ` to hand. What is checked is that the hypothesis the descent theorem
takes is satisfiable by something other than the trivial cover — which is the reading that would
make the theorem vacuous — and not that the conclusion has ever been drawn.
-/

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry ComplexAnalytic

universe u

noncomputable section

/-- The two-member family `z₀`, `1 - z₀` on the node. Indexed by `ULift (Fin 2)` because the
index type of `ComplexAnalytic.isOpenCover_localisationOpen` lives in the universe of the
presented algebra. -/
abbrev nodeCoverFamily : ULift.{u} (Fin 2) → MvPolynomial (ULift.{u} (Fin 2)) ℂ :=
  fun i ↦ ![nodeX.{u}, 1 - nodeX.{u}] i.down

/-- **The two classes generate the unit ideal**, because the two polynomials sum to `1`. Nothing
about the node enters: the same proof works over any presentation. -/
theorem span_nodeCoverFamily_eq_top :
    Ideal.span (Set.range fun i ↦ Ideal.Quotient.mk (presentationIdeal.{u} nodePres.{u})
      (nodeCoverFamily.{u} i)) = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  have h := Ideal.add_mem
    (Ideal.span (Set.range fun i ↦ Ideal.Quotient.mk (presentationIdeal.{u} nodePres.{u})
      (nodeCoverFamily.{u} i)))
    (Ideal.subset_span (Set.mem_range_self (ULift.up (0 : Fin 2))))
    (Ideal.subset_span (Set.mem_range_self (ULift.up (1 : Fin 2))))
  rwa [← map_add, show nodeCoverFamily.{u} (ULift.up (0 : Fin 2))
    + nodeCoverFamily.{u} (ULift.up (1 : Fin 2)) = 1 by simp [nodeCoverFamily], map_one] at h

/-- **The node is covered by `D(z₀)` and `D(1 - z₀)`.** -/
theorem isOpenCover_nodeCover :
    IsOpenCover fun i ↦ localisationOpen.{u} nodePres.{u} (nodeCoverFamily.{u} i) :=
  isOpenCover_localisationOpen.{u} nodePres.{u} nodeCoverFamily.{u} span_nodeCoverFamily_eq_top.{u}

/-- **`D(1 - z₀)` is a proper open subset**: `z₀` takes the value `1` at `axisPoint 0`, so
`1 - z₀` vanishes there. -/
theorem localisationOpen_one_sub_nodeX_ne_top :
    localisationOpen.{u} nodePres.{u} (1 - nodeX.{u}) ≠ ⊤ :=
  localisationOpen_ne_top.{u} nodePres.{u} _ (axisPoint.{u} (ULift.up 0)) (by
    rw [map_sub, map_one, MvPolynomial.eval_X, axisPoint_coord, if_pos rfl, sub_self])

/-- **Every member of the cover is a proper open subset**, so `isOpenCover_nodeCover` is not the
one-member cover by `⊤` that `ComplexAnalytic.localisationOpen_one` supplies over any base. This
is the statement that makes the cover evidence. -/
theorem localisationOpen_nodeCoverFamily_ne_top (i : ULift.{u} (Fin 2)) :
    localisationOpen.{u} nodePres.{u} (nodeCoverFamily.{u} i) ≠ ⊤ := by
  rcases i with ⟨i⟩
  fin_cases i
  · exact localisationOpen_nodePres_ne_top.{u}
  · exact localisationOpen_one_sub_nodeX_ne_top.{u}

end
