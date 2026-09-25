/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.ES.CapExtension.ProjChartInf
import Oka.Analytification.RET.ES.CapExtension.ChartReverse
import Oka.Analytification.GAGA.ProjectiveLineCoherentDirectImage
import Oka.Geometry.RingedSpace.LocallyRingedSpace.FreeResolutionAcyclic

/-!
# Coherence of the sheaf of the cap over the good part of the base

A sheaf of modules satisfying the local conditions for coherence at every point of an open `N` is
coherent on `N` (`AlgebraicGeometry.LocallyRingedSpace.isCoherent_restrictModules_of_forall`).

Keep the notation of `Oka/Analytification/RET/ES/CapExtension/ProjSheaf.lean`. If `U ⊆ G` is open
and `𝒜` satisfies the local conditions for coherence at the points of `N` over `U`, then the sheaf
of the cap `𝒞` is coherent over `U × ℙ¹`
(`ComplexAnalytic.Cap.AnnulusDecomposition.isCoherent_restrictModules_capModule`): points of
`U × ℙ¹` lie in the chart `w` over `N` or in the disc at infinity.
-/

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.LocallyRingedSpace

variable {X : LocallyRingedSpace.{u}} (N : Opens X.toPresheafedSpace)
  (M : SheafOfModules.{u} X.ringSheaf)

/-- The chart identifying the restriction of `M` to the open subspace `N` with `M`. -/
noncomputable def restrictModuleChart :
    ModuleChart M ((restrictOverEquiv X N).functor.obj (M.over N)) where
  g := (X.ofRestrict N.isOpenEmbedding).base
  isOpenEmbedding := N.isOpenEmbedding
  ψ _ := RingHom.id _
  bijective_ψ _ := Function.bijective_id
  ψ_res _ _ := rfl
  φ O := (restrictSectionsEquiv N M O).symm.toAddMonoidHom
  bijective_φ O := (restrictSectionsEquiv N M O).symm.bijective
  φ_res _ _ := rfl
  φ_smul _ _ _ := rfl

/-- **Coherence on an open from the local conditions at its points.** -/
theorem isCoherent_restrictModules_of_forall
    (h : ∀ x ∈ N, IsLocallyFinitelyGeneratedModuleAt M x ∧ HasLocalModuleRelationsAt M x) :
    ((X.restrictModules N).obj M).IsCoherent := by
  have hK : ((restrictOverEquiv X N).functor.obj (M.over N)).IsCoherent :=
    isCoherent_of_hasLocalModuleRelations _
      (fun y ↦ (restrictModuleChart N M).isLocallyFinitelyGeneratedModuleAt_of (h y.1 y.2).1)
      ((hasLocalModuleRelations_iff _).2 fun y ↦
        (restrictModuleChart N M).hasLocalModuleRelationsAt_of (h y.1 y.2).2)
  exact @SheafOfModules.IsCoherent.of_iso.{u} _ _ _ _ _ _ _ _ _ _
    (restrictModulesObjIso X N M).symm hK

end AlgebraicGeometry.LocallyRingedSpace

namespace ComplexAnalytic.Cap.AnnulusDecomposition

open AnalyticSpace BoundedSections relProjectiveSpaceAn relProjectiveLine
open AlgebraicGeometry AlgebraicGeometry.LocallyRingedSpace

noncomputable section

variable {m : ℕ} {N N₀ : (AnalyticSpace.complexAffineSpace.{u} (m + 1)).Opens}
  {W : FiniteEtaleOver (space N₀)} {F : WeierstrassForm N N₀}
  (D : AnnulusDecomposition W F.G F.ρ) (h₀ : N₀ ≤ N)

/-- **The local conditions for coherence of `𝒞`** at a point `chartPt i q` with `‖q.2‖ < ρ`. -/
lemma capModule_isCoherentAt_chartPt {i : Fin 2} {q : (Fin m → ℂ) × ℂ}
    (hqG : ofBase q.1 ∈ F.G) (hq : ‖q.2‖ < F.ρ)
    (hcoh : i = 0 → ∀ x : space N, x.1 = chartCoordHomeo.symm q → IsCoherentAt h₀ W x) :
    IsLocallyFinitelyGeneratedModuleAt D.capModule (chartPt.{u} i q) ∧
      HasLocalModuleRelationsAt D.capModule (chartPt.{u} i q) := by
  set x : Cn.{u} (m + 1) := chartCoordHomeo.symm q
  have hxq : chartCoordHomeo x = q := chartCoordHomeo.apply_symm_apply q
  have hb : baseOf x ∈ F.G ∧ ‖fibOf x‖ < F.ρ := by
    have h1 := congrArg Prod.fst hxq
    have h2 := congrArg Prod.snd hxq
    change baseCoord (baseOf x) = q.1 at h1
    change fibOf x = q.2 at h2
    refine ⟨?_, h2 ▸ hq⟩
    rw [← ofBase_baseCoord (baseOf x), h1]
    exact hqG
  fin_cases i
  · have hxN : x ∈ N := (F.mem_N x).2 hb
    have := D.capModule_isCoherentAt_chart0 h₀ (hcoh rfl ⟨x, hxN⟩ rfl)
    rwa [chart0Pt_eq, hxq] at this
  · have := D.capModule_isCoherentAt_chartInf h₀ (⟨x, hb⟩ : space (infOpens F))
    change IsLocallyFinitelyGeneratedModuleAt D.capModule (chartPt 1 (chartCoordHomeo x)) ∧
      HasLocalModuleRelationsAt D.capModule (chartPt 1 (chartCoordHomeo x)) at this
    rwa [hxq] at this

/-- **Coherence of the sheaf of the cap over `U × ℙ¹`** if `U ⊆ G` and `𝒜` satisfies the local
conditions for coherence at the points of `N` over `U`. -/
theorem isCoherent_restrictModules_capModule {U : Opens (Fin m → ℂ)}
    (hUG : ∀ b ∈ U, ofBase b ∈ F.G)
    (hU : ∀ x : space N, baseCoord (baseOf x.1) ∈ U → IsCoherentAt h₀ W x) :
    (((relProjectiveSpaceAn.{u} m 1).toLocallyRingedSpace.restrictModules
      (tube.{u} (N := 1) U)).obj D.capModule).IsCoherent := by
  refine isCoherent_restrictModules_of_forall _ _ fun p hp ↦ ?_
  obtain ⟨q, hqU, hq1, hq⟩ := exists_chartPt_norm_le_one hp
  have hqρ : ‖q.2‖ < F.ρ := hq1.trans_lt F.one_lt_ρ
  have hcoh : ∀ x : space N, x.1 = chartCoordHomeo.symm q → IsCoherentAt h₀ W x :=
    fun x hx ↦ hU x (by
      have : chartCoordHomeo x.1 = q := by rw [hx]; exact chartCoordHomeo.apply_symm_apply q
      have h1 : baseCoord (baseOf x.1) = q.1 := congrArg Prod.fst this
      exact h1 ▸ hqU)
  rcases hq with hq | hq
  · rw [← hq]
    exact D.capModule_isCoherentAt_chartPt h₀ (hUG _ hqU) hqρ fun _ ↦ hcoh
  · rw [← hq]
    exact D.capModule_isCoherentAt_chartPt h₀ (hUG _ hqU) hqρ fun h ↦ absurd h (by decide)

end

end ComplexAnalytic.Cap.AnnulusDecomposition
