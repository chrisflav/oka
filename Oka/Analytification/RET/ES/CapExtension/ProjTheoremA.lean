/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.ES.CapExtension.ProjTwist
import Oka.Analytification.RET.ES.CapExtension.Combine

/-!
# Relative Theorem A for the cap

Keep the notation of `Oka/Analytification/RET/ES/CapExtension/ProjSheaf.lean`. If the sheaf of the
cap `𝒞` is coherent over `U × ℙ¹`, then by relative Theorem A on `U × ℙ¹`
(`ComplexAnalytic.relProjectiveLine.exists_generates_twistMod`) for `n ≫ 0` finitely many sections
of `𝒞(n)` over `B × ℙ¹` generate `𝒞(n)` near a point `(y, [1 : w])`. In the chart `w`, `𝒞(n)` is
`𝒞 = 𝒜`, so the corresponding sections of the cap with a pole of order `≤ n`
(`ComplexAnalytic.Cap.AnnulusDecomposition.capPoleOf`) generate `𝒜` near `y`
(`ComplexAnalytic.Cap.AnnulusDecomposition.capTheoremA_of_isCoherent`).
-/

open CategoryTheory Opposite Topology TopologicalSpace Set Filter Metric

universe u

namespace ComplexAnalytic.Cap.AnnulusDecomposition

open AnalyticSpace BoundedSections relProjectiveSpaceAn relProjectiveLine
open AlgebraicGeometry AlgebraicGeometry.LocallyRingedSpace

noncomputable section

variable {m : ℕ}

lemma mem_closedBox_self_iff' {a y : Fin m → ℂ} : y ∈ Complex.closedBox a a ↔ y = a := by
  simp only [Complex.closedBox, Set.mem_univ_pi, Complex.mem_reProdIm, Set.Icc_self,
    Set.mem_singleton_iff]
  exact ⟨fun h ↦ funext fun j ↦ Complex.ext (h j).1 (h j).2, fun h j ↦ by simp [h]⟩

variable {N N₀ : (AnalyticSpace.complexAffineSpace.{u} (m + 1)).Opens} (h₀ : N₀ ≤ N)
  {W : FiniteEtaleOver (space N₀)} {F : WeierstrassForm N N₀}
  (D : AnnulusDecomposition W F.G F.ρ)

/-- In the chart `w`, the component `σ₀` is the section of `𝒜` underlying the section of the cap
given by `σ`. -/
lemma phi0_twComp_eq {n : ℕ} {B : Opens (Fin m → ℂ)}
    (σ : (twistMod D.capModule (n : ℤ)).val.obj (op (tube.{u} (N := 1) B)))
    {V₂ : (space N).Opens} (hV₂ : V₂ ≤ tubeN N (baseSet B) isOpen_baseSet)
    (hle : img0 N V₂ ≤ tube.{u} (N := 1) B ⊓ stdOpen.{u} m 1 0) :
    phi0 h₀ V₂ (sectRes D.capModule hle (twComp σ 0)) =
      sectRes (boundedModule h₀ W) hV₂ (capSec h₀ D (D.capPoleOf h₀ σ)) := by
  refine secVal_ext h₀ W fun w hw ↦ ?_
  rw [evalFun_phi0 h₀ _ hw, evalFun_secVal_sectRes _ _ hw, secVal_mkSec,
    evalFun_capPoleOf h₀ _ (preim_mono h₀ W hV₂ hw),
    capWVal_res _ _ ((mem_preimW_img0_iff h₀).2 hw)]

omit h₀ in
lemma modRes_eq_sectRes {O O' : (relProjectiveSpaceAn.{u} m 1).Opens} (h : O' ≤ O)
    (s : D.capModule.val.obj (op O)) : modRes s O' h = sectRes D.capModule h s :=
  rfl

/-- **Relative Theorem A for the cap**, from the coherence of the sheaf of the cap over `U × ℙ¹`,
at the points of `N` over `U`. -/
theorem capTheoremA_of_isCoherent {U : Opens (Fin m → ℂ)} (hUG : ∀ y ∈ U, ofBase.{u} y ∈ F.G)
    (hcoh : (((relProjectiveSpaceAn.{u} m 1).toLocallyRingedSpace.restrictModules
      (tube.{u} (N := 1) U)).obj D.capModule).IsCoherent)
    {y : space N} (hy : baseCoord (baseOf y.1) ∈ U) : D.CapTheoremA h₀ y := by
  classical
  set a := baseCoord (baseOf y.1)
  have hK : Complex.closedBox a a ⊆ U := fun y' hy' ↦ (mem_closedBox_self_iff'.1 hy') ▸ hy
  have hne : (Complex.closedBox a a).Nonempty := ⟨a, mem_closedBox_self_iff'.2 rfl⟩
  obtain ⟨a', b', hab', hBU, n₀, hgen⟩ := exists_generates_twistMod D.capModule hcoh hK hne
  have haB : a ∈ boxOpens a' b' := hab' (mem_closedBox_self_iff'.2 rfl)
  have hB : ∀ y ∈ boxOpens a' b', ofBase.{u} y ∈ F.G := fun y hy ↦ hUG y (hBU hy)
  refine ⟨baseSet (boxOpens a' b'), isOpen_baseSet, baseSet_subset hB, haB, n₀.toNat,
    fun n hn ↦ ?_⟩
  have hn' : n₀ ≤ (n : ℤ) := (Int.self_le_toNat n₀).trans (by exact_mod_cast hn)
  have hyT : chart0Pt y.1 ∈ tube.{u} (N := 1) (boxOpens a' b') := by
    change baseY (chartPt.{u} 0 _) ∈ boxOpens a' b'
    rw [baseY_chartPt]
    exact haB
  obtain ⟨I, _, σ, W₁, hW₁, hyW₁, hgenW⟩ := hgen n hn' _ hyT
  set e := Fintype.equivFin I
  refine ⟨Fintype.card I, fun k ↦ D.capPoleOf h₀ (σ (e.symm k)),
    fun k ↦ capPoleOf_mem h₀ hB _, ?_⟩
  set C := D.chart0ModuleChart h₀
  let V' : (space N).Opens := C.pre W₁ ⊓ tubeN N (baseSet (boxOpens a' b')) isOpen_baseSet
  have hyV' : y ∈ V' := by
    refine ⟨?_, haB⟩
    change C.g y ∈ W₁
    change (chart0Map N).toLRSHom.base y ∈ W₁
    rw [chart0Map_base]
    exact hyW₁
  refine ⟨V', inf_le_right, hyV', fun V'' hV'' b z hz ↦ ?_⟩
  have hV''T : C.img V'' ≤ tube.{u} (N := 1) (boxOpens a' b') ⊓ stdOpen.{u} m 1 0 :=
    (C.img_mono (hV''.trans inf_le_right)).trans img0_tubeN_le
  have hV''W : C.img V'' ≤ W₁ := (C.img_mono (hV''.trans inf_le_left)).trans (C.img_pre_le W₁)
  set s' := C.φInv V'' b
  set c := twistModCocycle.{u} m 1 (n : ℤ)
  set τ := (modTwistSectionsEquiv (N := D.capModule) c 0 (hV''T.trans inf_le_right)).symm s'
  obtain ⟨W₂, hW₂, hzW₂, d, hd⟩ := hgenW (C.img V'') hV''W τ (C.g z) ((C.mem_img z V'').2 hz)
  have hd' := congrArg (modTwistSectionsEquiv (N := D.capModule) c 0
    (hW₂.trans (hV''T.trans inf_le_right))) hd
  rw [modTwistSectionsEquiv_res _ 0 (hV''T.trans inf_le_right) hW₂,
    LinearEquiv.apply_symm_apply, map_sum] at hd'
  simp only [LinearEquiv.map_smul] at hd'
  have e2 (k : I) : modTwistSectionsEquiv (N := D.capModule) c 0
      (hW₂.trans (hV''T.trans inf_le_right)) (modRes (modRes (σ k) W₁ hW₁) W₂
        (hW₂.trans hV''W)) = modRes (twComp (σ k) 0) W₂ (hW₂.trans hV''T) := by
    rw [modRes_res, twComp, ← modTwistSectionsEquiv_res, modRes_res]
  simp only [e2] at hd'
  have hW''V'' : C.pre W₂ ≤ V'' := C.pre_le_of_le_img hW₂
  have hW''e : C.img (C.pre W₂) ≤ W₂ := C.img_pre_le W₂
  refine ⟨C.pre W₂, hW''V'', hzW₂, fun k ↦ C.ψ (C.pre W₂)
    ((relProjectiveSpaceAn.{u} m 1).res hW''e (d (e.symm k))), ?_⟩
  have e1 : sectRes (boundedModule h₀ W) hW''V'' b =
      C.φ (C.pre W₂) (sectRes D.capModule hW''e (modRes s' W₂ hW₂)) := by
    rw [← C.φ_φInv V'' b, ← C.φ_res hW''V'']
    congr 1
    exact (sectRes_sectRes _ _ _ _).symm
  rw [e1, hd', sectRes_sum, C.φ_sum]
  refine (Fintype.sum_equiv e _ _ fun k ↦ ?_)
  simp only [Equiv.symm_apply_apply]
  rw [sectRes_smul, C.φ_smul, modRes_eq_sectRes, sectRes_sectRes]
  exact congrArg _ (phi0_twComp_eq h₀ D (σ k) _ _)

end

end ComplexAnalytic.Cap.AnnulusDecomposition
