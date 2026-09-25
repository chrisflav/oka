/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.AnalyticSpace.LocalFreeResolution
import Oka.Analytification.GAGA.CartanTheoremA
import Oka.Analytification.GAGA.ProjectiveLineCoherentCover
import Oka.Geometry.RingedSpace.LocallyRingedSpace.PullbackCoherent

/-!
# Cartan's theorems on chart boxes of `U × ℙ¹`

Let `X` be a locally ringed space, `j : ℂⁿ ⟶ X` an open immersion and `𝒢` a sheaf of
`𝒪_X`-modules which is coherent on an open `O ⊆ j(ℂⁿ)`. By Cartan's theorems for closed boxes,
applied on the open subspace `X|_O`, every closed box `K ⊆ j⁻¹(O)` has an open neighbourhood `N`
with finitely many sections of `𝒢` over `N` which generate the sections of `𝒢` over every open
`W ⊆ N` on which `𝒪_X` is acyclic, and `𝒢` is acyclic on such `W`
(`ComplexAnalytic.exists_generators_acyclic_of_openImmersion`).

For `P^an = ℂᵐ × ℙ¹` and `𝒢` coherent over `U × ℙ¹` we apply this in both charts
(`ComplexAnalytic.relProjectiveLine.exists_chartGenerators`). The opens on which `𝒪` is acyclic
include the chart boxes over open boxes and their intersections
(`ComplexAnalytic.relProjectiveLine.subsingleton_H_chartBox`,
`ComplexAnalytic.relProjectiveLine.subsingleton_H_chartBox_inf`).
-/

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry Limits
open AlgebraicGeometry.LocallyRingedSpace

universe u

noncomputable section

namespace ComplexAnalytic

section OpenImmersion

variable {X : LocallyRingedSpace.{u}} {n : ℕ} (j : complexAffineSpace.{u} n ⟶ X)
  [LocallyRingedSpace.IsOpenImmersion j]

set_option maxHeartbeats 400000 in
-- identifying sections over opens of `X|_O` with sections over their images in `X` is slow
/-- **Cartan's theorems near a closed box in a chart.** Let `j : ℂⁿ ⟶ X` be an open immersion,
`O ⊆ j(ℂⁿ)` open with `𝒪_{X|_O}` having locally finitely generated relations, and `𝒢` a sheaf of
`𝒪_X`-modules whose restriction to `O` is coherent. For a nonempty closed box `K ⊆ j⁻¹(O)` there
are an open `N ⊆ O` with `K ⊆ j⁻¹(N)` and finitely many sections `g` of `𝒢` over `N` such that
on every open `W ⊆ N` on which `𝒪_X` is acyclic, `𝒢` is acyclic and the `g|_W` generate the
sections of `𝒢` over `W`. -/
theorem exists_generators_acyclic_of_openImmersion (O : Opens X.toPresheafedSpace)
    (hOj : ∀ x ∈ O, x ∈ Set.range j.base) (hX : (X.restrict O.isOpenEmbedding).HasLocalRelations)
    (𝒢 : SheafOfModules.{u} X.ringSheaf) (h𝒢 : ((X.restrictModules O).obj 𝒢).IsCoherent)
    {a b : ULift.{u} (Fin n) → ℂ} (hK : Complex.closedBox a b ⊆ j.base ⁻¹' O)
    (hne : (Complex.closedBox a b).Nonempty) :
    ∃ (N : Opens X.toPresheafedSpace), N ≤ O ∧ Complex.closedBox a b ⊆ j.base ⁻¹' N ∧
      ∃ (I : Type u) (_ : Fintype I) (g : I → 𝒢.val.obj (op N)),
        ∀ (W : Opens X.toPresheafedSpace) (hW : W ≤ N),
          (∀ q, 0 < q → Subsingleton (TopCat.Sheaf.H
            ((TopCat.Sheaf.restrictOpen W).obj X.structureSheafAb) q)) →
          (∀ q, 0 < q → Subsingleton (TopCat.Sheaf.H
            ((TopCat.Sheaf.restrictOpen W).obj 𝒢.toAb) q)) ∧
          ∀ s : 𝒢.val.obj (op W), ∃ c : I → X.ringSheaf.obj.obj (op W),
            s = ∑ i, c i • 𝒢.val.map (homOfLE hW).op (g i) := by
  classical
  have hrange : Set.range (X.ofRestrict O.isOpenEmbedding).base ⊆ Set.range j.base := by
    rintro _ ⟨y, rfl⟩
    exact hOj _ y.2
  let f : X.restrict O.isOpenEmbedding ⟶ complexAffineSpace.{u} n :=
    LocallyRingedSpace.IsOpenImmersion.lift j (X.ofRestrict O.isOpenEmbedding) hrange
  have hf : f ≫ j = X.ofRestrict O.isOpenEmbedding :=
    LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ _
  haveI := LocallyRingedSpace.IsOpenImmersion.pullback_snd_isIso_of_range_subset j _ hrange
  haveI : LocallyRingedSpace.IsOpenImmersion f := by
    change LocallyRingedSpace.IsOpenImmersion
      (inv (pullback.snd j (X.ofRestrict O.isOpenEmbedding)) ≫ pullback.fst _ _)
    infer_instance
  haveI : ((restrictOverEquiv X O).functor.obj (𝒢.over O)).IsCoherent :=
    @SheafOfModules.IsCoherent.of_iso.{u} _ _ _ _ _ _ _ _ _ _ (restrictModulesObjIso X O 𝒢) h𝒢
  have hpd : ∀ y, HasProjectiveDimensionLE
      (((X.restrict O.isOpenEmbedding).stalkFunctor y).obj
        ((restrictOverEquiv X O).functor.obj (𝒢.over O))) n := fun y ↦ by
    haveI := finite_stalk_of_isFiniteType ((restrictOverEquiv X O).functor.obj (𝒢.over O)) y
    exact hasFGGlobalDimensionLE_stalk_of_isIso f y
      (hasFGGlobalDimensionLE_stalk_complexAffineSpace n _)
      (((X.restrict O.isOpenEmbedding).stalkFunctor y).obj
        ((restrictOverEquiv X O).functor.obj (𝒢.over O)))
  have hKf : Complex.closedBox a b ⊆ Set.range f.base := by
    intro x hx
    have hr := LocallyRingedSpace.IsOpenImmersion.lift_range j
      (X.ofRestrict O.isOpenEmbedding) hrange
    have hx' : x ∈ j.base ⁻¹' Set.range (X.ofRestrict O.isOpenEmbedding).base :=
      ⟨⟨j.base x, hK hx⟩, rfl⟩
    rw [← hr] at hx'
    exact hx'
  obtain ⟨W', hKW', hres⟩ := exists_hasFreeResolutionLE_closedBox f hX _ hpd hKf hne
  obtain ⟨I, I', _, _, g, A, -, H⟩ := exists_generators_acyclic W' _ hres
  let N : Opens X.toPresheafedSpace := O.isOpenEmbedding.isOpenMap.functor.obj W'
  have hNO : N ≤ O := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  refine ⟨N, hNO, fun x hx ↦ ?_, I, inferInstance,
    fun i ↦ restrictSectionsEquiv O 𝒢 W' (g i), fun W hW hWa ↦ ?_⟩
  · obtain ⟨y, hy, hyx⟩ := hKW' hx
    refine ⟨y, hy, ?_⟩
    change (X.ofRestrict O.isOpenEmbedding).base y = j.base x
    rw [← hyx]
    exact (congrArg (fun φ : X.restrict O.isOpenEmbedding ⟶ X ↦ φ.base y) hf).symm
  obtain ⟨W'', hφW⟩ : ∃ W'' : Opens (X.restrict O.isOpenEmbedding).toPresheafedSpace,
      O.isOpenEmbedding.isOpenMap.functor.obj W'' = W :=
    ⟨preimageOpen O W, functor_obj_preimageOpen (hW.trans hNO)⟩
  have hW''W' : W'' ≤ W' := by
    intro y hy
    have hy' : (X.ofRestrict O.isOpenEmbedding).base y ∈ N := hW (hφW ▸ ⟨y, hy, rfl⟩)
    obtain ⟨y', hy', hyy'⟩ := hy'
    rwa [← O.isOpenEmbedding.injective hyy']
  have r₁ : W ≤ O.isOpenEmbedding.isOpenMap.functor.obj W'' := hφW.ge
  have r₂ : O.isOpenEmbedding.isOpenMap.functor.obj W'' ≤ W := hφW.le
  have hW''a : ∀ q, 0 < q → Subsingleton (TopCat.Sheaf.H
      ((TopCat.Sheaf.restrictOpen W'').obj (X.restrict O.isOpenEmbedding).structureSheafAb) q) :=
    fun q hq ↦ @Equiv.subsingleton _ _
      (structureSheafAbAddEquivOfEq (X.ofRestrict O.isOpenEmbedding) O.isOpenEmbedding W'' hφW
        q).symm.toEquiv (hWa q hq)
  obtain ⟨hMa, hsurj, -⟩ := H W'' hW''W' hW''a
  refine ⟨fun q hq ↦ subsingleton_H_restrictOpen_of_restrict hφW (hMa q hq), fun s ↦ ?_⟩
  let s' : 𝒢.val.obj (op (O.isOpenEmbedding.isOpenMap.functor.obj W'')) :=
    𝒢.val.map (homOfLE r₂).op s
  obtain ⟨c, hc⟩ := hsurj ((restrictSectionsEquiv O 𝒢 W'').symm s')
  refine ⟨fun i ↦ X.ringSheaf.obj.map (homOfLE r₁).op (c i), ?_⟩
  have e1 : 𝒢.val.map (homOfLE r₁).op s' = s := by
    rw [sheafOfModules_map_map, sheafOfModules_map_self]
  have e3 : s' = restrictSectionsEquiv O 𝒢 W'' (∑ i, c i •
      ((restrictOverEquiv X O).functor.obj (𝒢.over O)).val.map (homOfLE hW''W').op (g i)) := by
    have h := congrArg (restrictSectionsEquiv O 𝒢 W'') hc
    rw [AddEquiv.apply_symm_apply] at h
    exact h
  rw [← e1, e3]
  erw [map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  erw [PresheafOfModules.map_smul]
  congr 1
  change 𝒢.val.map (homOfLE r₁).op (𝒢.val.map
    (homOfLE (O.isOpenEmbedding.isOpenMap.functor.monotone hW''W')).op
      (restrictSectionsEquiv O 𝒢 W' (g i))) = _
  rw [sheafOfModules_map_map]

/-- The restriction of a sheaf of modules which is coherent on `W` to an open `V ≤ W` is
coherent, if `𝒪_X` has locally finitely generated relations. -/
lemma isCoherent_restrictModules_of_le {X : LocallyRingedSpace.{u}} (hX : X.HasLocalRelations)
    {V W : Opens X.toPresheafedSpace} (h : V ≤ W) (𝒢 : SheafOfModules.{u} X.ringSheaf)
    (h𝒢 : ((X.restrictModules W).obj 𝒢).IsCoherent) :
    ((X.restrictModules V).obj 𝒢).IsCoherent := by
  haveI := h𝒢
  have := isCoherent_pullbackModules_of_isCoherentStructureSheaf
    (isCoherentStructureSheaf_of_hasLocalRelations (hX.restrict V)) (X.restrictLE h)
    ((X.restrictModules W).obj 𝒢)
  exact @SheafOfModules.IsCoherent.of_iso.{u} _ _ _ _ _ _ _ _ _ _ (restrictModulesLEIso h 𝒢).symm
    this

end OpenImmersion

namespace relProjectiveLine

open relProjectiveSpaceAn

variable {m : ℕ}

/-! ### Boxes in chart coordinates -/

/-- The index of the fibre coordinate of `ℂ^{1+m}`. -/
abbrev fibIdx : ULift.{u} (Fin (1 + m)) := ⟨Fin.castAdd m 0⟩

/-- The index of the `j`-th base coordinate of `ℂ^{1+m}`. -/
abbrev baseIdx (j : Fin m) : ULift.{u} (Fin (1 + m)) := ⟨Fin.natAdd 1 j⟩

@[simp]
lemma cpt_fibIdx (p : (Fin m → ℂ) × ℂ) :
    (cpt.{u} p : ULift.{u} (Fin (1 + m)) → ℂ) fibIdx = p.2 := by
  simp [cpt, joinPt]

@[simp]
lemma cpt_baseIdx (p : (Fin m → ℂ) × ℂ) (j : Fin m) :
    (cpt.{u} p : ULift.{u} (Fin (1 + m)) → ℂ) (baseIdx j) = p.1 j := by
  simp [cpt, joinPt]

lemma cpt_mem_openBox_iff {α β : ULift.{u} (Fin (1 + m)) → ℂ} {p : (Fin m → ℂ) × ℂ} :
    (cpt.{u} p : ULift.{u} (Fin (1 + m)) → ℂ) ∈ Complex.openBox α β ↔
      p.2 ∈ Set.Ioo (α fibIdx).re (β fibIdx).re ×ℂ Set.Ioo (α fibIdx).im (β fibIdx).im ∧
      p.1 ∈ Complex.openBox (fun j ↦ α (baseIdx j)) (fun j ↦ β (baseIdx j)) := by
  simp only [Complex.openBox, Set.mem_univ_pi]
  refine ⟨fun h ↦ ⟨by simpa using h fibIdx, fun j ↦ by simpa using h (baseIdx j)⟩, ?_⟩
  rintro ⟨h1, h2⟩ ⟨k⟩
  induction k using Fin.addCases with
  | left l =>
    rw [Subsingleton.elim l 0]
    simpa using h1
  | right j => simpa using h2 j

lemma cpt_mem_closedBox_iff {α β : ULift.{u} (Fin (1 + m)) → ℂ} {p : (Fin m → ℂ) × ℂ} :
    (cpt.{u} p : ULift.{u} (Fin (1 + m)) → ℂ) ∈ Complex.closedBox α β ↔
      p.2 ∈ Set.Icc (α fibIdx).re (β fibIdx).re ×ℂ Set.Icc (α fibIdx).im (β fibIdx).im ∧
      p.1 ∈ Complex.closedBox (fun j ↦ α (baseIdx j)) (fun j ↦ β (baseIdx j)) := by
  simp only [Complex.closedBox, Set.mem_univ_pi]
  refine ⟨fun h ↦ ⟨by simpa using h fibIdx, fun j ↦ by simpa using h (baseIdx j)⟩, ?_⟩
  rintro ⟨h1, h2⟩ ⟨k⟩
  induction k using Fin.addCases with
  | left l =>
    rw [Subsingleton.elim l 0]
    simpa using h1
  | right j => simpa using h2 j

lemma mem_closedBox_yPart {α β : ULift.{u} (Fin (1 + m)) → ℂ}
    {w : AnalyticSpace.complexAffineSpace.{u} (1 + m)}
    (hw : (w : ULift.{u} (Fin (1 + m)) → ℂ) ∈ Complex.closedBox α β) :
    yPart w ∈ Complex.closedBox (fun j ↦ α (baseIdx j)) (fun j ↦ β (baseIdx j)) := by
  rw [← cpt_yPart_zPart w] at hw
  exact (cpt_mem_closedBox_iff.1 hw).2

/-! ### Generators on the chart boxes -/

/-- **Cartan's theorems in a chart of `U × ℙ¹`.** Let `𝒢` be coherent over `U × ℙ¹`, `K ⊆ U` a
nonempty closed box and `S > 0`. For each chart `i` there are an open `B ⊆ U` containing `K`, an
open `N ⊇ chartBox i (B × (-S, S)²)` and finitely many sections `g` of `𝒢` over `N` which generate
the sections of `𝒢` over every open `W ⊆ N` on which `𝒪` is acyclic; `𝒢` is acyclic on such
`W`. -/
theorem exists_chartGenerators {U : Opens (Fin m → ℂ)}
    (𝒢 : SheafOfModules.{u} (relProjectiveSpaceAn.{u} m 1).toLocallyRingedSpace.ringSheaf)
    (h𝒢 : (((relProjectiveSpaceAn.{u} m 1).toLocallyRingedSpace.restrictModules
      (tube.{u} (N := 1) U)).obj 𝒢).IsCoherent)
    {a b : Fin m → ℂ} (hK : Complex.closedBox a b ⊆ U) (hne : (Complex.closedBox a b).Nonempty)
    {S : ℝ} (hS : 0 < S) (i : Fin 2) :
    ∃ (B : Opens (Fin m → ℂ)), Complex.closedBox a b ⊆ B ∧ B ≤ U ∧
      ∃ (N : (relProjectiveSpaceAn.{u} m 1).Opens),
        chartBox.{u} i (prodOpens B (squareOpens S)) ≤ N ∧
        ∃ (I : Type u) (_ : Fintype I) (g : I → 𝒢.val.obj (op N)),
          ∀ (W : (relProjectiveSpaceAn.{u} m 1).Opens) (hW : W ≤ N),
            (∀ q, 0 < q → Subsingleton (TopCat.Sheaf.H ((TopCat.Sheaf.restrictOpen W).obj
              (relProjectiveSpaceAn.{u} m 1).toLocallyRingedSpace.structureSheafAb) q)) →
            (∀ q, 0 < q → Subsingleton (TopCat.Sheaf.H
              ((TopCat.Sheaf.restrictOpen W).obj 𝒢.toAb) q)) ∧
            ∀ s : 𝒢.val.obj (op W), ∃ c : I →
              (relProjectiveSpaceAn.{u} m 1).toLocallyRingedSpace.ringSheaf.obj.obj (op W),
              s = ∑ k, c k • 𝒢.val.map (homOfLE hW).op (g k) := by
  obtain ⟨S', hS'⟩ : ∃ S' : ℝ, S' = S + 1 := ⟨_, rfl⟩
  have hS'0 : 0 < S' := by rw [hS']; positivity
  let α : ULift.{u} (Fin (1 + m)) → ℂ := fun k ↦ Fin.append ![⟨-S', -S'⟩] a k.down
  let β : ULift.{u} (Fin (1 + m)) → ℂ := fun k ↦ Fin.append ![⟨S', S'⟩] b k.down
  have hαf : α fibIdx = ⟨-S', -S'⟩ := by simp [α]
  have hβf : β fibIdx = ⟨S', S'⟩ := by simp [β]
  have hαb : (fun j ↦ α (baseIdx j)) = a := by funext j; simp [α]
  have hβb : (fun j ↦ β (baseIdx j)) = b := by funext j; simp [β]
  have hcpt : ∀ y ∈ Complex.closedBox a b, ∀ z : ℂ, |z.re| ≤ S' → |z.im| ≤ S' →
      (cpt.{u} (y, z) : ULift.{u} (Fin (1 + m)) → ℂ) ∈ Complex.closedBox α β := by
    intro y hy z hre him
    rw [cpt_mem_closedBox_iff, hαf, hβf, hαb, hβb]
    refine ⟨?_, hy⟩
    simp only [Complex.mem_reProdIm, Set.mem_Icc]
    exact ⟨abs_le.1 hre, abs_le.1 him⟩
  obtain ⟨y₀, hy₀⟩ := hne
  let O : (relProjectiveSpaceAn.{u} m 1).Opens := tube.{u} (N := 1) U ⊓ chartOpens i
  have hX : O ≤ tube.{u} (N := 1) U := inf_le_left
  have hK' : Complex.closedBox α β ⊆ (chartLRS.{u} (m := m) i).base ⁻¹' O := fun w hw ↦
    ⟨by
      change baseY _ ∈ U
      rw [baseY_chart]
      rw [← hαb, ← hβb] at hK
      exact hK (mem_closedBox_yPart hw), ⟨w, rfl⟩⟩
  obtain ⟨N, hNO, hKN, I, _, g, H⟩ := @exists_generators_acyclic_of_openImmersion _ (1 + m)
    (chartLRS.{u} (m := m) (N := 1) i) (isOpenImmersion_chart i) O (fun x hx ↦ hx.2)
    ((AnalyticSpace.hasLocalRelations (relProjectiveSpaceAn.{u} m 1)).restrict O) 𝒢
    (isCoherent_restrictModules_of_le (AnalyticSpace.hasLocalRelations _) hX 𝒢 h𝒢) α β hK'
    ⟨_, hcpt y₀ hy₀ 0 (by simp only [Complex.zero_re, abs_zero]; positivity)
      (by simp only [Complex.zero_im, abs_zero]; positivity)⟩
  obtain ⟨α', β', hαβ, hsub⟩ := exists_openBox_between
    (N.isOpen.preimage (chartLRS.{u} (m := m) i).base.hom.continuous) hKN
  have hfib : ∀ z ∈ squareOpens S,
      z ∈ Set.Ioo (α' fibIdx).re (β' fibIdx).re ×ℂ Set.Ioo (α' fibIdx).im (β' fibIdx).im := by
    intro z hz
    rw [mem_squareOpens_iff, abs_lt, abs_lt] at hz
    have h1 := (cpt_mem_openBox_iff.1 (hαβ (hcpt y₀ hy₀ ⟨-S', -S'⟩ (by simp [abs_of_pos hS'0])
      (by simp [abs_of_pos hS'0])))).1
    have h2 := (cpt_mem_openBox_iff.1 (hαβ (hcpt y₀ hy₀ ⟨S', S'⟩ (by simp [abs_of_pos hS'0])
      (by simp [abs_of_pos hS'0])))).1
    simp only [Complex.mem_reProdIm, Set.mem_Ioo] at h1 h2 ⊢
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith [h1.1.1, h1.2.1, h2.1.2, h2.2.2]
  let B : Opens (Fin m → ℂ) := boxOpens (fun j ↦ α' (baseIdx j)) (fun j ↦ β' (baseIdx j))
  have hBN : chartBox.{u} i (prodOpens B (squareOpens S)) ≤ N := by
    rintro _ ⟨p, ⟨hp1, hp2⟩, rfl⟩
    exact hsub (cpt_mem_openBox_iff.2 ⟨hfib _ hp2, hp1⟩)
  refine ⟨B, fun y hy ↦ ?_, fun y hy ↦ ?_, N, hBN, I, inferInstance, g, H⟩
  · exact (cpt_mem_openBox_iff.1 (hαβ (hcpt y hy 0
      (by simp only [Complex.zero_re, abs_zero]; positivity)
      (by simp only [Complex.zero_im, abs_zero]; positivity)))).2
  · have h0 : chartPt.{u} i (y, 0) ∈ N := hBN ⟨(y, 0), ⟨hy, zero_mem_squareOpens hS⟩, rfl⟩
    have := (hNO h0).1
    change baseY _ ∈ U at this
    rwa [baseY_chartPt] at this

end relProjectiveLine

end ComplexAnalytic

end
