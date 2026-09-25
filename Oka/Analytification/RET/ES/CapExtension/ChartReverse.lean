/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Geometry.RingedSpace.LocallyRingedSpace.CoherentModuleOpenEmbedding

/-!
# Transporting local generators and relations backwards along charts

Let `C : ModuleChart M K` be a chart for sheaves of modules along an open embedding `g : Z → Y`
(`AlgebraicGeometry.LocallyRingedSpace.ModuleChart`). Then the local conditions for coherence of
`M` at `g z` imply those of `K` at `z`
(`AlgebraicGeometry.LocallyRingedSpace.ModuleChart.isLocallyFinitelyGeneratedModuleAt_of`,
`AlgebraicGeometry.LocallyRingedSpace.ModuleChart.hasLocalModuleRelationsAt_of`); this is the
converse of `AlgebraicGeometry.LocallyRingedSpace.ModuleChart.isLocallyFinitelyGeneratedModuleAt`.
-/

open CategoryTheory TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.LocallyRingedSpace.ModuleChart

variable {Y Z : LocallyRingedSpace.{u}} {M : SheafOfModules.{u} Y.ringSheaf}
  {K : SheafOfModules.{u} Z.ringSheaf} (C : ModuleChart M K)

/-- **Local generators transport backwards along a chart.** -/
theorem isLocallyFinitelyGeneratedModuleAt_of {z : Z}
    (hM : IsLocallyFinitelyGeneratedModuleAt M (C.g z)) :
    IsLocallyFinitelyGeneratedModuleAt K z := by
  obtain ⟨W, k, s, hzW, hgen⟩ := hM
  set W₀ : Opens Y.toPresheafedSpace := W ⊓ C.img ⊤
  have hW₀e : C.img (C.pre W₀) = W₀ := C.img_pre inf_le_right
  have hW₀W : C.img (C.pre W₀) ≤ W := hW₀e.le.trans inf_le_left
  refine ⟨C.pre W₀, k, fun l ↦ C.φ (C.pre W₀) (sectRes M hW₀W (s l)),
    ⟨hzW, (C.mem_img z ⊤).2 trivial⟩, fun O₁ hO₁ t y hy ↦ ?_⟩
  have h₁ : C.img O₁ ≤ W := (C.img_mono hO₁).trans hW₀W
  obtain ⟨W'', hW'', hyW'', c, hc⟩ := hgen (C.img O₁) h₁ (C.φInv O₁ t) (C.g y)
    ((C.mem_img y O₁).2 hy)
  have hW''r : W'' ≤ C.img ⊤ := hW''.trans (C.img_mono le_top)
  have hW''e : C.img (C.pre W'') = W'' := C.img_pre hW''r
  have hpre : C.pre W'' ≤ O₁ := C.pre_le_of_le_img hW''
  refine ⟨C.pre W'', hpre, hyW'', fun l ↦ C.ψ (C.pre W'') (Y.res hW''e.le (c l)), ?_⟩
  have e₁ : sectRes K hpre t = C.φ (C.pre W'') (sectRes M (C.img_mono hpre) (C.φInv O₁ t)) := by
    rw [C.φ_res hpre, φ_φInv]
  rw [e₁]
  have e₂ : sectRes M (C.img_mono hpre) (C.φInv O₁ t) =
      sectRes M hW''e.le (sectRes M hW'' (C.φInv O₁ t)) := by
    rw [sectRes_sectRes]
  rw [e₂, hc, sectRes_sum, C.φ_sum]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [sectRes_smul, C.φ_smul, sectRes_sectRes]
  beta_reduce
  congr 1
  exact C.φ_sectRes_sectRes _ (hpre.trans hO₁) hW₀W _

/-- **Local relations transport backwards along a chart.** -/
theorem hasLocalModuleRelationsAt_of {z : Z} (hM : HasLocalModuleRelationsAt M (C.g z)) :
    HasLocalModuleRelationsAt K z := by
  intro V m f hzV
  obtain ⟨W, hWV, k, g, hzW, hrel, hcompl⟩ :=
    hM (C.img V) m (fun i ↦ C.φInv V (f i)) ((C.mem_img z V).2 hzV)
  have hWr : W ≤ C.img ⊤ := hWV.trans (C.img_mono le_top)
  have hWe : C.img (C.pre W) = W := C.img_pre hWr
  have hpreV : C.pre W ≤ V := C.pre_le_of_le_img hWV
  refine ⟨C.pre W, hpreV, k, fun l i ↦ C.ψ (C.pre W) (Y.res hWe.le (g l i)), hzW,
    fun l ↦ ?_, fun W' hW' a ha y hy ↦ ?_⟩
  · have := congrArg (fun s ↦ C.φ (C.pre W) (sectRes M hWe.le s)) (hrel l)
    simp only [sectRes_sum, sectRes_smul, C.φ_sum, sectRes_zero, map_zero] at this
    rw [← this]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [C.φ_smul, sectRes_sectRes, C.φ_res hpreV, φ_φInv]
  · -- transport the relation to `Y`
    have hW'e : C.img W' ≤ W := (C.img_mono hW').trans hWe.le
    let a' : Fin m → Y.presheaf.obj (op (C.img W')) := fun i ↦ C.ψInv W' (a i)
    have ha' : ∑ i, a' i • sectRes M (hW'e.trans hWV) (C.φInv V (f i)) = 0 := by
      refine C.φ_injective W' ?_
      rw [C.φ_sum, map_zero, ← ha]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [C.φ_smul, ψ_ψInv, C.φ_res (hW'.trans hpreV), φ_φInv]
    obtain ⟨W'', hW'', hyW'', c, hc⟩ := hcompl (C.img W') hW'e a' ha' (C.g y)
      ((C.mem_img y W').2 hy)
    have hW''r : W'' ≤ C.img ⊤ := hW''.trans (C.img_mono le_top)
    have hW''e : C.img (C.pre W'') = W'' := C.img_pre hW''r
    have hpre : C.pre W'' ≤ W' := C.pre_le_of_le_img hW''
    refine ⟨C.pre W'', hpre, hyW'', fun l ↦ C.ψ (C.pre W'') (Y.res hW''e.le (c l)),
      fun i ↦ ?_⟩
    have := congrArg (fun r ↦ C.ψ (C.pre W'') (Y.res hW''e.le r)) (hc i)
    simp only [res_sum, map_sum] at this
    have e₁ : Z.res hpre (a i) = C.ψ (C.pre W'') (Y.res (C.img_mono hpre) (a' i)) := by
      rw [C.ψ_res hpre, ψ_ψInv]
    rw [e₁, ← Y.res_res hW''e.le hW'', this]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [res_mul, map_mul, Y.res_res, C.ψ_res_res _ (hpre.trans hW') hWe.le]

end AlgebraicGeometry.LocallyRingedSpace.ModuleChart
