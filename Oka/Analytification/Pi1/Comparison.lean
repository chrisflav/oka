/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.Pi1.ConnectedCover
import Oka.Analytification.Pi1.Fiber
import Oka.Analytification.RET.Connected
import Oka.AnalyticSpace.Monodromy
import Oka.CategoryTheory.Galois.Transport

/-!
# The comparison theorem `π₁ᵉᵗ(X, ξₓ) ≅ π₁(X^an, x)^`

For a connected scheme `X` locally of finite type over `ℂ` and a point `x` of `X^an` whose
analytification is locally contractible, the étale fundamental group of `X` at the geometric point
`ξₓ` (`ComplexAnalytic.geometricPoint`) is isomorphic, as a topological group, to the profinite
completion of the topological fundamental group `π₁(X^an, x)`
(`ComplexAnalytic.etaleFundamentalGroupContinuousMulEquiv`).

`X` need not be separated, reduced or smooth. The local contractibility hypothesis is the only
input about the topology of `X^an`; it holds for every `X` (`Plans/Pi1Comparison.md`, §4).

## The proof

`π₁(X^an, x)` acts on the fibre over `x` of every finite cover of `X^an` by monodromy
(`Oka/AnalyticSpace/Monodromy.lean`), hence, through the Riemann existence theorem and the
identification of fibre functors `ComplexAnalytic.fiberGeometricPointIso`, on the fibres of pi1's
fibre functor `AlgebraicGeometry.FiniteEtale.fiber ξₓ`
(`CategoryTheory.PreGaloisCategory.transportMulAction`). This action is natural, transitive on
connected objects (a connected finite étale cover has connected total space,
`AlgebraicGeometry.FiniteEtale.connectedSpace_left_of_isConnected`, hence connected
analytification, `ComplexAnalytic.connectedSpace_analytification`), and every finite-index normal
subgroup contains the kernel on some fibre (the covering space of the subgroup,
`Oka/Topology/Covering/PathCover.lean`).
`CategoryTheory.PreGaloisCategory.isFundamentalGroup_completion` then identifies the profinite
completion with `Aut (FiniteEtale.fiber ξₓ) = π₁ᵉᵗ(ξₓ)`.
-/

universe u

open CategoryTheory PreGaloisCategory AlgebraicGeometry ProfiniteGrp.ProfiniteCompletion

namespace ComplexAnalytic

noncomputable section

variable {X : SchemeLFTℂ.{u}} (x : analytification.obj X)

/-- The monodromy action of `π₁(X^an, x)` on the étale fibres at `ξₓ`. -/
abbrev etaleMonodromyMulAction :
    ∀ A : FiniteEtale X.obj.left, MulAction (FundamentalGroup (analytification.obj X) x)
      ((FiniteEtale.fiber (geometricPoint X x)).obj A) :=
  letI := AnalyticSpace.SeparatedFiniteEtaleOver.monodromyMulAction x
  transportMulAction (analytificationFiniteEtale X) (fiberGeometricPointIso x) _

variable [ConnectedSpace X.obj.left]

/-- **The comparison theorem**: for a connected scheme `X` locally of finite type over `ℂ` whose
analytification is locally contractible, and `x : X^an`, the étale fundamental group of `X` at the
geometric point `ξₓ` is the profinite completion of the topological fundamental group of `X^an` at
`x`, as topological groups. -/
def etaleFundamentalGroupContinuousMulEquiv
    (hX : LocallyContractibleSpace (analytification.obj X)) :
    Aut (FiniteEtale.fiber (geometricPoint X x)) ≃ₜ*
      completion (GrpCat.of (FundamentalGroup (analytification.obj X) x)) := by
  haveI := hX.locallyPathConnectedSpace
  letI := AnalyticSpace.SeparatedFiniteEtaleOver.monodromyMulAction x
  letI := etaleMonodromyMulAction x
  haveI : IsNaturalSMul (FiniteEtale.fiber (geometricPoint X x))
      (FundamentalGroup (analytification.obj X) x) :=
    isNaturalSMul_transport (analytificationFiniteEtale X) (fiberGeometricPointIso x) _
  refine (profiniteCompletionContinuousMulEquiv (FiniteEtale.fiber (geometricPoint X x))
    (FundamentalGroup (analytification.obj X) x) (fun A _ ↦ ?_) (fun N ↦ ?_)).symm
  · haveI : ConnectedSpace A.left :=
      FiniteEtale.connectedSpace_left_of_isConnected (geometricPoint X x) A
    haveI : ConnectedSpace (SchemeLFTℂ.ofFiniteEtale X A).obj.left := ‹ConnectedSpace A.left›
    haveI : ConnectedSpace (((analytificationFiniteEtale X).obj A).left : Type u) :=
      connectedSpace_analytification (SchemeLFTℂ.ofFiniteEtale X A)
    exact isPretransitive_transport_obj (analytificationFiniteEtale X) (fiberGeometricPointIso x)
      _ A (AnalyticSpace.SeparatedFiniteEtaleOver.isPretransitive_monodromy_of_connectedSpace x _)
  · exact exists_ker_le_transport (analytificationFiniteEtale X) (fiberGeometricPointIso x) _
      (AnalyticSpace.SeparatedFiniteEtaleOver.exists_ker_le x hX.semilocallySimplyConnected
        N.toSubgroup)

end

end ComplexAnalytic
