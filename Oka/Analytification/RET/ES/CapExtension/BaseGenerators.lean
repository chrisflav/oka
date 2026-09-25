/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.ES.CapExtension.BaseSheaf
import Oka.AnalyticSpace.NoetherProperty

/-!
# Uniform generators of the sections of the cap

Keep the notation of `Oka/Analytification/RET/ES/CapExtension/BaseSheaf.lean`. If the sections of
the cap with a pole of order `≤ n` at infinity are locally finitely generated at every point of
`G`, the sheaf `𝒮ₙ` of their evaluations is coherent
(`ComplexAnalytic.Cap.AnnulusDecomposition.isCoherent_evalSubmodule`): it is a subsheaf of a
free sheaf, so its relations are relations of tuples of holomorphic functions. By Cartan's Theorem A
on a closed box `K ⊆ G`, finitely many sections of `𝒮ₙ` near `K` generate `𝒮ₙ` near every point of
`K`; they glue to sections of the cap over the interior of `K`
(`ComplexAnalytic.Cap.AnnulusDecomposition.exists_isCapGenAt_openBox`). Since the interior of `K`
does not depend on `n`, this gives uniform generators
(`ComplexAnalytic.Cap.AnnulusDecomposition.capGenerators_of_capLocallyFinite`).
-/

open CategoryTheory Opposite Topology Set Filter Metric

universe u

namespace ComplexAnalytic.Cap.AnnulusDecomposition

open AnalyticSpace BoundedSections Complex.ProjectiveLineBundle AlgebraicGeometry.LocallyRingedSpace
open KummerModel (splitEquiv)

noncomputable section

variable {m : ℕ} {N N₀ : (AnalyticSpace.complexAffineSpace.{u} (m + 1)).Opens} (h₀ : N₀ ≤ N)
  {W : FiniteEtaleOver (space N₀)} {F : WeierstrassForm N N₀}
  (D : AnnulusDecomposition W F.G F.ρ) {n : ℕ} {M : ℕ} {w : Fin M → ℂ}

/-- **`𝒮ₙ` is coherent** if the sections of the cap are locally finitely generated. -/
theorem isCoherent_evalSubmodule (hwρ : ∀ ν, w ν ∈ overlap F.ρ)
    (hloc : ∀ b ∈ F.G, D.CapLocallyFinite h₀ n b) :
    (D.evalSubmodule h₀ n hwρ).toSheafOfModules.IsCoherent := by
  classical
  haveI := AnalyticSpace.isCoherent_free (space F.baseOpens) (D.EvIdx M)
  exact isCoherent_of_hasLocalModuleRelations _
    (D.isLocallyFinitelyGeneratedModule_evalSubmodule h₀ hwρ hloc)
    ((D.evalSubmodule h₀ n hwρ).hasLocalModuleRelations
      (hasLocalModuleRelations_of_isCoherent _))

/-- **Cartan's Theorem A for `𝒮ₙ`** near a closed box `K ⊆ G`. -/
theorem exists_generatesLocally_evalSubmodule (hwρ : ∀ ν, w ν ∈ overlap F.ρ)
    (hcoh : (D.evalSubmodule h₀ n hwρ).toSheafOfModules.IsCoherent) {a b : Cm.{u} m}
    (hK : Complex.closedBox a b ⊆ F.G) (hne : (Complex.closedBox a b).Nonempty) :
    ∃ W' : (space F.baseOpens).Opens, (∀ z ∈ Complex.closedBox a b, z ∈ img W') ∧
      ∃ (I : Type u) (_ : Fintype I)
        (g : I → (D.evalSubmodule h₀ n hwρ).toSheafOfModules.val.obj (op W')),
        ∀ (V : (space F.baseOpens).Opens) (hV : V ≤ W')
          (σ : (D.evalSubmodule h₀ n hwρ).toSheafOfModules.val.obj (op V))
          (y : space F.baseOpens), y ∈ V →
          ∃ (W₃ : (space F.baseOpens).Opens) (h : W₃ ≤ V), y ∈ W₃ ∧
            ∃ c : I → (space F.baseOpens).presheaf.obj (op W₃),
              modRes σ W₃ h = ∑ i, c i • modRes (g i) W₃ (h.trans hV) := by
  let S' : SheafOfModules.{u}
      ((_root_.complexAffineSpace.{u} m).restrict F.baseOpens.isOpenEmbedding).ringSheaf :=
    (D.evalSubmodule h₀ n hwρ).toSheafOfModules
  obtain ⟨W', hKW', I, hI, g, hg, -⟩ := @ComplexAnalytic.exists_sections_closedBox _ _ _
    ((_root_.complexAffineSpace.{u} m).ofRestrict F.baseOpens.isOpenEmbedding) _
    ((hasLocalRelations_complexSpace _).restrict F.baseOpens) S' hcoh _
    (fun y ↦ @ComplexAnalytic.hasProjectiveDimensionLE_stalk_restrict_complexAffineSpace _
      F.baseOpens S' hcoh y)
    _ _ (fun x hx ↦ ⟨⟨x, hK hx⟩, rfl⟩) hne
  refine ⟨W', fun z hz ↦ ?_, I, hI, g, fun V hV σ y hy ↦ hg V hV σ y hy⟩
  obtain ⟨y, hy, rfl⟩ := hKW' hz
  exact mem_img_iff.2 ⟨y.2, hy⟩


variable [T2Space W.left]

/-- **Generators of the sections of the cap over an open box**, from Cartan's Theorem A for `𝒮ₙ`
on the closure of the box. -/
theorem exists_isCapGenAt_openBox (hwρ : ∀ ν, w ν ∈ overlap F.ρ) (hw : Function.Injective w)
    (hM : (∑ i, (D.deg i : ℕ)) * n < M)
    (hcoh : (D.evalSubmodule h₀ n hwρ).toSheafOfModules.IsCoherent) {a b : Cm.{u} m}
    (hK : Complex.closedBox a b ⊆ F.G) (hne : (Complex.closedBox a b).Nonempty) :
    ∃ (L : ℕ) (σ : Fin L → boundedSubring h₀ W (tubeN N (Complex.openBox a b)
      (isOpen_openBox a b)) × (D.ι → Cm.{u} m × ℂ → ℂ)),
      (∀ l, σ l ∈ D.capPole h₀ n (tubeN N (Complex.openBox a b) (isOpen_openBox a b))
        (Complex.openBox a b ×ˢ ball 0 F.ρ)) ∧
      ∀ z ∈ Complex.openBox a b, D.IsCapGenAt h₀ n σ z := by
  classical
  set O := Complex.openBox a b
  have hO : IsOpen O := isOpen_openBox a b
  have hOK : O ⊆ Complex.closedBox a b := fun x hx j _ ↦
    ⟨Ioo_subset_Icc_self (hx j trivial).1, Ioo_subset_Icc_self (hx j trivial).2⟩
  have hOG : O ⊆ F.G := hOK.trans hK
  set S := (D.evalSubmodule h₀ n hwρ).toSheafOfModules
  obtain ⟨W', hKW', I, hI, g, hg⟩ :=
    D.exists_generatesLocally_evalSubmodule h₀ hwρ hcoh hK hne
  have hOW' : ∀ z ∈ O, z ∈ img W' := fun z hz ↦ hKW' z (hOK hz)
  -- the generators, as sections of the cap over `O`
  have hglue : ∀ i, ∃ t ∈ D.capPole h₀ n (tubeN N O hO) (O ×ˢ ball 0 F.ρ), ∀ z ∈ O, ∀ x,
      D.evalVec w t.1.1 z x = holFun (V := W') (SheafOfModules.freeEval _ (g i).1 x) z := by
    intro i
    have hτ : D.IsCapEval h₀ n w (SheafOfModules.freeEval (op W') (g i).1) := (g i).2
    refine D.exists_capPole_of_locally h₀ hOG hM hw hwρ fun z hz ↦ ?_
    obtain ⟨B, hB, hBW, hzB, t, ht, htv⟩ := hτ z (hOW' z hz)
    have hBO : IsOpen (B ∩ O) := hB.inter hO
    have hle : tubeN N (B ∩ O) hBO ≤ tubeN N B hB := tubeN_mono inter_subset_left
    refine ⟨B ∩ O, hBO, inter_subset_right, ⟨hzB, hz⟩, D.capRestrict h₀ hle t,
      D.capRestrict_mem_capPole h₀ hle (prod_mono inter_subset_left subset_rfl) ht,
      fun z' hz' x ↦ ?_⟩
    rw [D.evalVec_capRestrict h₀ hwρ (inter_subset_right.trans hOG) inter_subset_left _ hz']
    exact htv z' hz'.1 x
  choose t ht htv using hglue
  set e := Fintype.equivFin I
  refine ⟨Fintype.card I, fun l ↦ t (e.symm l), fun l ↦ ht _, fun z hz V hV hVO hzV t' ht' ↦ ?_⟩
  have hVG : V ⊆ F.G := hVO.trans hOG
  have hle : F.baseOpen V hV ≤ W' := fun y hy ↦ (mem_img_iff.1 (hOW' y.1 (hVO hy))).2
  obtain ⟨W₃, h₃, hzW₃, c, hc⟩ := hg (F.baseOpen V hV) hle (D.evalSec h₀ hwρ hVG ht') ⟨z, hVG hzV⟩
    hzV
  have hW₃V : ∀ z' ∈ img W₃, z' ∈ V := fun z' hz' ↦
    (F.mem_img_baseOpen hVG).1 (img_mono h₃ hz')
  refine ⟨img W₃, hW₃V, (img W₃).isOpen, mem_img_iff.2 ⟨_, hzW₃⟩,
    fun l ↦ holFun (c (e.symm l)), fun l ↦ (differentiableOn_holFun _), ?_⟩
  refine D.evalFun_eq_sum_of_evalVec h₀ (img W₃).isOpen hVG hW₃V hVO ht' (fun l ↦ ht _) hM hw hwρ
    (fun l ↦ differentiableOn_holFun _) fun z' hz' x ↦ ?_
  have := congrArg (fun s : S.val.obj (op W₃) ↦
    holFun (V := W₃) (SheafOfModules.freeEval _ s.1 x) z') hc
  rw [D.holFun_freeEval_modRes h₀ hwρ h₃ _ x hz', D.holFun_freeEval_sum_smul h₀ hwρ _ _ x hz',
    D.holFun_evalSec h₀ hwρ hVG ht' x (hW₃V z' hz')] at this
  rw [this, ← e.sum_comp]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [D.holFun_freeEval_modRes h₀ hwρ _ _ x hz', Equiv.symm_apply_apply,
    htv _ z' (hVO (hW₃V z' hz')) x]

omit [T2Space W.left] in
lemma convex_openBox (a b : Cm.{u} m) : Convex ℝ (Complex.openBox a b) :=
  convex_pi fun _ _ ↦ ((convex_Ioo _ _).linear_preimage Complex.reLm).inter
    ((convex_Ioo _ _).linear_preimage Complex.imLm)

/-- **Uniform generators of the sections of the cap** near every point of `G`, if the sections
of the cap with a pole of order `≤ n` are locally finitely generated for every `n`. -/
theorem capGenerators_of_capLocallyFinite
    (hloc : ∀ n, ∀ b ∈ F.G, D.CapLocallyFinite h₀ n b) {z₀ : Cm.{u} m} (hz₀ : z₀ ∈ F.G) :
    D.CapGenerators h₀ z₀ := by
  obtain ⟨ε, hε, hεG⟩ := Metric.isOpen_iff.1 F.isOpen_G z₀ hz₀
  set δ : ℝ := ε / 4
  have hδ : 0 < δ := by positivity
  set a : Cm.{u} m := z₀ - fun _ ↦ ⟨δ, δ⟩
  set b : Cm.{u} m := z₀ + fun _ ↦ ⟨δ, δ⟩
  have hK : Complex.closedBox a b ⊆ F.G := fun x hx ↦ hεG (by
    have := closedBox_subset_closedBall z₀ hδ.le hx
    rw [mem_closedBall] at this
    rw [mem_ball]
    have : δ = ε / 4 := rfl
    linarith)
  have hz₀O : z₀ ∈ Complex.openBox a b := fun j _ ↦ by
    refine Complex.mem_reProdIm.2 ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> simp [a, b] <;> linarith
  have hne : (Complex.closedBox a b).Nonempty :=
    ⟨z₀, fun j _ ↦ ⟨Ioo_subset_Icc_self (hz₀O j trivial).1,
      Ioo_subset_Icc_self (hz₀O j trivial).2⟩⟩
  refine ⟨Complex.openBox a b, isOpen_openBox a b, fun x hx ↦ hK fun j _ ↦
    ⟨Ioo_subset_Icc_self (hx j trivial).1, Ioo_subset_Icc_self (hx j trivial).2⟩,
    convex_openBox a b, hz₀O, fun n ↦ ?_⟩
  obtain ⟨w, hw, hwρ⟩ := exists_nodes F.one_lt_ρ ((∑ i, (D.deg i : ℕ)) * n + 1)
  exact D.exists_isCapGenAt_openBox h₀ hwρ hw (Nat.lt_succ_self _)
    (D.isCoherent_evalSubmodule h₀ hwρ (hloc n)) hK hne

end

end ComplexAnalytic.Cap.AnnulusDecomposition
