/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.AnalyticSpace.ConnectedCover
import Oka.AnalyticSpace.CoveringMap
import Oka.AnalyticSpace.CoveringSpace
import Oka.AnalyticSpace.FundamentalGroup
import Oka.CategoryTheory.Galois.ProfiniteCompletion
import Oka.Topology.Covering.LocallyContractible
import Oka.Topology.Covering.Monodromy
import Oka.Topology.Covering.Separated

/-!
# The topological fundamental group acts on the fibres of analytic covers

Let `X` be a complex analytic space and `x : X`. The underlying map of a cover separated
over `X` is a covering map (`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.isCoveringMap`;
no separation axiom on `X` is needed),
so the topological fundamental group `π₁(X, x)` (Mathlib's `FundamentalGroup`) acts on its fibre
over `x` by monodromy (`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.monodromyMulAction`).
If `X` is moreover locally contractible (Mathlib's classical `LocallyContractibleSpace`), the
action satisfies the three hypotheses of
`CategoryTheory.PreGaloisCategory.isFundamentalGroup_completion`:

- it is natural in the cover (`…SeparatedFiniteEtaleOver.isNaturalSMul_monodromy`);
- it is transitive on the fibre of a cover with connected total space
  (`…SeparatedFiniteEtaleOver.isPretransitive_monodromy_of_connectedSpace`), which is then path
  connected;
- every finite-index normal subgroup `N` contains the kernel of the action on the fibre of the
  cover `PathCover N` of `Oka/Topology/Covering/PathCover.lean`, made analytic by
  `ComplexAnalytic.AnalyticSpace.coveringSpace` (`…SeparatedFiniteEtaleOver.exists_ker_le`).

Hence the analytic fundamental group `…SeparatedFiniteEtaleOver.fundamentalGroup x` (the
automorphism group of the fibre functor) is the profinite completion of `π₁(X, x)`
(`…SeparatedFiniteEtaleOver.fundamentalGroupContinuousMulEquiv`).
-/

universe u

open CategoryTheory PreGaloisCategory ProfiniteGrp.ProfiniteCompletion

namespace ComplexAnalytic.AnalyticSpace

variable {X : AnalyticSpace.{u}}

/-- **The underlying map of a separated cover is a covering map**, over an arbitrary base: it is
closed, separated, a local homeomorphism and has finite fibres
(`IsClosedMap.isCoveringMap_of_isLocalHomeomorph_of_isSeparatedMap`). -/
theorem SeparatedFiniteEtaleOver.isCoveringMap (A : SeparatedFiniteEtaleOver.{u} X) :
    IsCoveringMap A.hom.toLRSHom.base :=
  haveI := A.isFiniteEtale_hom
  (IsFinite.isClosedMap (f := A.hom)).isCoveringMap_of_isLocalHomeomorph_of_isSeparatedMap
    A.isSeparatedMap_hom
    (fun y ↦ have := IsFinite.finite_fiber (f := A.hom) y; Set.toFinite _)
    IsLocalIso.isLocalHomeomorph

variable (x : X)

/-- **The monodromy action of `π₁(X, x)` on the fibre over `x`.** -/
@[reducible] noncomputable def SeparatedFiniteEtaleOver.monodromyMulAction
    (A : SeparatedFiniteEtaleOver.{u} X) :
    MulAction (FundamentalGroup (X : Type u) x)
      ((SeparatedFiniteEtaleOver.fintypeFiberFunctor.{u} x).obj A) :=
  A.isCoveringMap.fundamentalGroupMulAction x

attribute [local instance] SeparatedFiniteEtaleOver.monodromyMulAction

lemma SeparatedFiniteEtaleOver.monodromy_smul_def (A : SeparatedFiniteEtaleOver.{u} X)
    (g : FundamentalGroup (X : Type u) x)
    (a : (SeparatedFiniteEtaleOver.fintypeFiberFunctor.{u} x).obj A) :
    g • a = A.isCoveringMap.monodromy g a :=
  rfl

/-- **Monodromy is natural in the cover.** -/
instance SeparatedFiniteEtaleOver.isNaturalSMul_monodromy :
    IsNaturalSMul (SeparatedFiniteEtaleOver.fintypeFiberFunctor.{u} x)
      (FundamentalGroup (X : Type u) x) where
  naturality g A B f a := by
    have hw : B.hom.toLRSHom.base ∘ f.left.toLRSHom.base = A.hom.toLRSHom.base := by
      have := MorphismProperty.Over.w f
      ext y
      exact congr_arg (fun φ ↦ φ.toLRSHom.base y) this
    exact Subtype.ext (A.isCoveringMap.monodromy_comp B.isCoveringMap
      f.left.toLRSHom.base.hom.continuous hw g a)

/-- **Monodromy is transitive on the fibre of a cover with connected total space**, over a
locally path-connected base. -/
theorem SeparatedFiniteEtaleOver.isPretransitive_monodromy_of_connectedSpace
    [LocallyPathConnectedSpace (X : Type u)] (A : SeparatedFiniteEtaleOver.{u} X)
    [ConnectedSpace (A.left : Type u)] :
    MulAction.IsPretransitive (FundamentalGroup (X : Type u) x)
      ((SeparatedFiniteEtaleOver.fintypeFiberFunctor.{u} x).obj A) := by
  haveI : LocallyPathConnectedSpace ((Functor.fromPUnit X).obj A.right : Type u) :=
    ‹LocallyPathConnectedSpace (X : Type u)›
  haveI : LocallyPathConnectedSpace (A.left : Type u) :=
    A.isCoveringMap.isLocalHomeomorph.locallyPathConnectedSpace
  haveI : PathConnectedSpace (A.left : Type u) := PathConnectedSpace.of_locallyPathConnectedSpace
  haveI : PathConnectedSpace ((𝟭 AnalyticSpace.{u}).obj A.left : Type u) := this
  exact ⟨fun a b ↦ A.isCoveringMap.exists_monodromy_eq a b⟩

/-- The cover of `X` attached to a finite-index subgroup `N ≤ π₁(X, x)`, as an object of the
category of covers separated over `X`. -/
noncomputable def SeparatedFiniteEtaleOver.pathCover [LocallyPathConnectedSpace (X : Type u)]
    (hX : SemilocallySimplyConnected (X : Type u)) (N : Subgroup (FundamentalGroup (X : Type u) x))
    [N.FiniteIndex] : SeparatedFiniteEtaleOver.{u} X :=
  have hcov : IsCoveringMap (PathCover.proj N) := PathCover.isCoveringMap (B := (X : Type u)) hX
  let p : TopCat.of (PathCover N) ⟶ X.toLocallyRingedSpace.toTopCat :=
    TopCat.ofHom ⟨PathCover.proj N, hcov.continuous⟩
  MorphismProperty.Over.mk ⊤ (AnalyticSpace.coveringSpaceHom X p hcov.isLocalHomeomorph)
    ⟨AnalyticSpace.isFiniteEtale_coveringSpaceHom X p hcov PathCover.finite_proj_preimage,
      hcov.isSeparatedMap⟩

/-- **Every finite-index subgroup of `π₁(X, x)` contains the kernel of the monodromy action on
some fibre**, for `X` locally path connected and semilocally simply connected. -/
theorem SeparatedFiniteEtaleOver.exists_ker_le [LocallyPathConnectedSpace (X : Type u)]
    (hX : SemilocallySimplyConnected (X : Type u)) (N : Subgroup (FundamentalGroup (X : Type u) x))
    [N.FiniteIndex] :
    ∃ A : SeparatedFiniteEtaleOver.{u} X, ∀ h : FundamentalGroup (X : Type u) x,
      (∀ a : (SeparatedFiniteEtaleOver.fintypeFiberFunctor.{u} x).obj A, h • a = a) → h ∈ N := by
  refine ⟨SeparatedFiniteEtaleOver.pathCover x hX N, fun h hh ↦ ?_⟩
  exact PathCover.mem_of_monodromy_eq hX h (hh ⟨⟨x, PathCover.Fiber.mk (𝟙 _)⟩, rfl⟩)

variable [T2Space (X : Type u)] [PreconnectedSpace (X : Type u)]

/-- **Monodromy is transitive on the fibre of a connected cover** of a Hausdorff, preconnected,
locally path-connected base. -/
theorem SeparatedFiniteEtaleOver.isPretransitive_monodromy [LocallyPathConnectedSpace (X : Type u)]
    (A : SeparatedFiniteEtaleOver.{u} X) [PreGaloisCategory.IsConnected A] :
    MulAction.IsPretransitive (FundamentalGroup (X : Type u) x)
      ((SeparatedFiniteEtaleOver.fintypeFiberFunctor.{u} x).obj A) :=
  haveI : ConnectedSpace (A.left : Type u) :=
    SeparatedFiniteEtaleOver.connectedSpace_of_isConnected A
  SeparatedFiniteEtaleOver.isPretransitive_monodromy_of_connectedSpace x A

/-- **The analytic fundamental group is the profinite completion of the topological one**, for a
Hausdorff, connected, locally contractible complex analytic space (Hausdorff because the analytic
Galois category `…SeparatedFiniteEtaleOver.galoisCategory` asks it). -/
noncomputable def SeparatedFiniteEtaleOver.fundamentalGroupContinuousMulEquiv
    [Nonempty (X : Type u)]
    (hX : LocallyContractibleSpace (X : Type u)) :
    SeparatedFiniteEtaleOver.fundamentalGroup x ≃ₜ*
      completion (GrpCat.of (FundamentalGroup (X : Type u) x)) :=
  haveI := hX.locallyPathConnectedSpace
  (profiniteCompletionContinuousMulEquiv (SeparatedFiniteEtaleOver.fintypeFiberFunctor.{u} x)
    (FundamentalGroup (X : Type u) x)
    (fun A _ ↦ SeparatedFiniteEtaleOver.isPretransitive_monodromy x A)
    (fun N ↦ SeparatedFiniteEtaleOver.exists_ker_le x hX.semilocallySimplyConnected
      N.toSubgroup)).symm

end ComplexAnalytic.AnalyticSpace
