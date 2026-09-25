/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.ES.CapExtension.Chain
import Oka.Analytification.RET.ES.CapExtension.CapHartogs

/-!
# Coherence at the zero set from generators of the cap sections

Keep the notation of `Oka/Analytification/RET/ES/CapExtension/Setup.lean`: `(N, N°)` is in
Weierstrass form over `G`, `D` is a decomposition of `W` over the annulus and `R` is a family of
regular pairs on `G` with zero set `Z`. We show that `𝒜` satisfies the local conditions for
coherence at a point `x` over `z₀ ∈ G` given the following two inputs:

* **relative Theorem A** at the points `y` not over `Z`
  (`ComplexAnalytic.Cap.AnnulusDecomposition.CapTheoremA`): for `n ≫ 0` the sections of the cap
  with a pole of order `≤ n` at infinity over `B × ℙ¹`, `B` a neighbourhood of the base point of
  `y`, generate `𝒜` near `y`;
* **uniform generators** near `z₀` (`ComplexAnalytic.Cap.AnnulusDecomposition.CapGenerators`):
  over a fixed convex neighbourhood `O` of `z₀`, for every `n` finitely many sections `σₙ` of the
  cap with a pole of order `≤ n` generate these sections as a module over the holomorphic functions
  on the base, locally at every point of `O`.

Then near every point `y` over `O ∖ Z` the `σₙ` generate `𝒜` for `n ≫ 0`, so by the chain
argument (`ComplexAnalytic.BoundedSections.exists_generatesNear_of_chain`) a single finite family
generates `𝒜` off `Z` near `x`, and the gap criterion
(`ComplexAnalytic.BoundedSections.isCoherentAt_of_generates`) concludes
(`ComplexAnalytic.Cap.AnnulusDecomposition.isCoherentAt_of_capGenerators`).
-/

open CategoryTheory Opposite Topology Set Filter Metric

universe u

namespace ComplexAnalytic.Cap.AnnulusDecomposition

open AnalyticSpace BoundedSections Complex.ProjectiveLineBundle AlgebraicGeometry.LocallyRingedSpace
open KummerModel (splitEquiv)

noncomputable section

variable {m : ℕ} {N N₀ : (AnalyticSpace.complexAffineSpace.{u} (m + 1)).Opens} (h₀ : N₀ ≤ N)
  {W : FiniteEtaleOver (space N₀)} {F : WeierstrassForm N N₀}
  (D : AnnulusDecomposition W F.G F.ρ)

/-- The section of `𝒜` underlying a section of the cap. -/
abbrev capSec {V : (space N).Opens} (t : boundedSubring h₀ W V × (D.ι → Cm.{u} m × ℂ → ℂ)) :
    (boundedModule h₀ W).val.obj (op V) :=
  mkSec h₀ W t.1.1 t.1.2

/-- **Relative Theorem A for the cap** at `y`: for `n ≫ 0`, finitely many sections of the cap with
a pole of order `≤ n` at infinity over `B × ℙ¹`, `B` a neighbourhood of the base point of `y`,
generate `𝒜` near `y`. -/
def CapTheoremA (y : space N) : Prop :=
  ∃ (B : Set (Cm.{u} m)) (hB : IsOpen B), B ⊆ F.G ∧ baseOf y.1 ∈ B ∧ ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
    ∃ (K : ℕ) (s : Fin K → boundedSubring h₀ W (tubeN N B hB) × (D.ι → Cm.{u} m × ℂ → ℂ)),
      (∀ k, s k ∈ D.capPole h₀ n (tubeN N B hB) (B ×ˢ ball 0 F.ρ)) ∧
        GeneratesNear h₀ W (fun k ↦ D.capSec h₀ (s k)) y

/-- **The sections `s` of the cap generate the sections of the cap at `b`**: every section `t` of
the cap with a pole of order `≤ n` over `V × ℙ¹`, `b ∈ V ⊆ B`, is near `b` a combination of the
`sₖ` with coefficients holomorphic functions on the base. -/
def IsCapGenAt (n : ℕ) {B : Set (Cm.{u} m)} {hB : IsOpen B} {K : ℕ}
    (s : Fin K → boundedSubring h₀ W (tubeN N B hB) × (D.ι → Cm.{u} m × ℂ → ℂ))
    (b : Cm.{u} m) : Prop :=
  ∀ (V : Set (Cm.{u} m)) (hV : IsOpen V), V ⊆ B → b ∈ V →
    ∀ t ∈ D.capPole h₀ n (tubeN N V hV) (V ×ˢ ball 0 F.ρ),
      ∃ V' ⊆ V, IsOpen V' ∧ b ∈ V' ∧ ∃ e : Fin K → Cm.{u} m → ℂ,
        (∀ k, DifferentiableOn ℂ (e k) V') ∧ ∀ y ∈ preim h₀ W (tubeN N V hV),
          baseOf (pt W y) ∈ V' →
            evalFun t.1.1 y = ∑ k, e k (baseOf (pt W y)) * evalFun (s k).1.1 y

/-- **The sections of the cap are locally finitely generated at `b`**: over a neighbourhood `B`
of `b`, finitely many sections of the cap with a pole of order `≤ n` generate these sections at
every point of `B`. -/
def CapLocallyFinite (n : ℕ) (b : Cm.{u} m) : Prop :=
  ∃ (B : Set (Cm.{u} m)) (hB : IsOpen B), B ⊆ F.G ∧ b ∈ B ∧ ∃ (K : ℕ)
    (s : Fin K → boundedSubring h₀ W (tubeN N B hB) × (D.ι → Cm.{u} m × ℂ → ℂ)),
    (∀ k, s k ∈ D.capPole h₀ n (tubeN N B hB) (B ×ˢ ball 0 F.ρ)) ∧
      ∀ b' ∈ B, D.IsCapGenAt h₀ n s b'

/-- **Uniform generators of the sections of the cap** near `z₀`: over a convex open neighbourhood
`O ⊆ G` of `z₀`, for every `n` finitely many sections of the cap with a pole of order `≤ n` over
`O × ℙ¹` generate these sections at every point of `O`. -/
def CapGenerators (z₀ : Cm.{u} m) : Prop :=
  ∃ (O : Set (Cm.{u} m)) (hO : IsOpen O), O ⊆ F.G ∧ Convex ℝ O ∧ z₀ ∈ O ∧ ∀ n : ℕ,
    ∃ (L : ℕ) (σ : Fin L → boundedSubring h₀ W (tubeN N O hO) × (D.ι → Cm.{u} m × ℂ → ℂ)),
      (∀ l, σ l ∈ D.capPole h₀ n (tubeN N O hO) (O ×ˢ ball 0 F.ρ)) ∧
        ∀ b ∈ O, D.IsCapGenAt h₀ n σ b

lemma evalFun_secVal_sectRes_capSec {V V' : (space N).Opens} (h : V' ≤ V)
    (t : boundedSubring h₀ W V × (D.ι → Cm.{u} m × ℂ → ℂ)) {y : W.left}
    (hy : y ∈ preim h₀ W V') :
    evalFun (secVal h₀ W (sectRes (boundedModule h₀ W) h (D.capSec h₀ t))) y =
      evalFun t.1.1 y := by
  rw [secVal_map, evalFun_map W _ _ hy, secVal_mkSec]

/-- **Generators of `𝒜` from generators of the cap sections**: if sections `s` of the cap over
`B × ℙ¹` generate `𝒜` near `y`, and near the base point of `y` every `sₖ` is a combination of the
`σₗ` with holomorphic coefficients on the base, then the `σₗ` generate `𝒜` near `y`. -/
theorem generatesNear_of_combination {B O V' : Set (Cm.{u} m)} {hB : IsOpen B} {hO : IsOpen O}
    (hV' : IsOpen V') (hV'O : V' ⊆ O) {y : space N} (hyV' : baseOf y.1 ∈ V') {K L : ℕ}
    {s : Fin K → boundedSubring h₀ W (tubeN N B hB) × (D.ι → Cm.{u} m × ℂ → ℂ)}
    (hs : GeneratesNear h₀ W (fun k ↦ D.capSec h₀ (s k)) y)
    (σ : Fin L → boundedSubring h₀ W (tubeN N O hO) × (D.ι → Cm.{u} m × ℂ → ℂ))
    {e : Fin K → Fin L → Cm.{u} m → ℂ} (he : ∀ k l, DifferentiableOn ℂ (e k l) V')
    (hse : ∀ k, ∀ w ∈ preim h₀ W (tubeN N B hB), baseOf (pt W w) ∈ V' →
      evalFun (s k).1.1 w = ∑ l, e k l (baseOf (pt W w)) * evalFun (σ l).1.1 w) :
    GeneratesNear h₀ W (fun l ↦ D.capSec h₀ (σ l)) y := by
  classical
  obtain ⟨V₁, hV₁B, hyV₁, hgen⟩ := hs
  refine ⟨V₁ ⊓ tubeN N V' hV', fun z hz ↦ hV'O hz.2, ⟨hyV₁, hyV'⟩,
    fun V₃ h₃ a z hz ↦ ?_⟩
  obtain ⟨W₄, h₄, hzW₄, f, hf⟩ := hgen V₃ (h₃.trans inf_le_left) a z hz
  have hW₄V' : ∀ x ∈ img W₄, baseOf x ∈ V' := fun x hx ↦ by
    obtain ⟨hxN, hx4⟩ := mem_img_iff.1 hx
    exact (h₃ (h₄ hx4)).2
  have hd : ∀ l, DifferentiableOn ℂ
      (fun x ↦ ∑ k, holFun (f k) x * e k l (baseOf x)) (img W₄) := fun l ↦
    DifferentiableOn.fun_sum fun k _ ↦ (differentiableOn_holFun (f k)).mul
      ((he k l).comp differentiable_baseOf.differentiableOn fun x hx ↦ hW₄V' x hx)
  refine ⟨W₄, h₄, hzW₄, fun l ↦ OkaRing.ofDifferentiableOn _ (hd l), ?_⟩
  refine secVal_ext h₀ W fun w hw ↦ ?_
  have hwimg : pt W w ∈ img W₄ := (mem_preim_iff h₀ W).1 hw
  have hwB : w ∈ preim h₀ W (tubeN N B hB) :=
    preim_mono h₀ W (h₄.trans ((h₃.trans inf_le_left).trans hV₁B)) hw
  rw [hf, evalFun_sum_smul h₀ W _ _ hw, evalFun_sum_smul h₀ W _ _ hw]
  simp_rw [evalFun_secVal_sectRes_capSec h₀ D _ _ hw, holFun_ofDifferentiableOn _ hwimg,
    hse _ w hwB (hW₄V' _ hwimg), Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun l _ ↦ by ring

/-- An open subset of `G` meeting the zero set of `R` is not contained in it. -/
lemma exists_mem_sdiff_zeroSet (R : RegularPairFamily F.G) {O : Set (Cm.{u} m)} (hO : IsOpen O)
    (hOG : O ⊆ F.G) {z₀ : Cm.{u} m} (hz₀ : z₀ ∈ O) : ∃ b ∈ O, b ∉ R.zeroSet := by
  by_contra! h
  have := R.eqOn_of_eqOn_diff hO hOG (F₁ := fun _ ↦ (0 : ℂ)) (F₂ := fun _ ↦ 1)
    continuousOn_const continuousOn_const (fun b hb ↦ absurd (h b hb.1) hb.2) hz₀
  exact zero_ne_one this

variable [T2Space W.left]

/-- **Coherence from generators of the cap sections.** If relative Theorem A holds at the points
not over the zero set `Z` of `R` and the sections of the cap have uniform generators near `z₀`, then
`𝒜` satisfies the local conditions for coherence at every point over `z₀`. -/
theorem isCoherentAt_of_capGenerators (R : RegularPairFamily F.G)
    (hRT : ∀ y : space N, baseOf y.1 ∉ R.zeroSet → D.CapTheoremA h₀ y) {x : space N}
    (hx : D.CapGenerators h₀ (baseOf x.1)) : IsCoherentAt h₀ W x := by
  classical
  obtain ⟨O, hO, hOG, hOc, hxO, hσ⟩ := hx
  choose L σ hσmem hσgen using hσ
  -- generation off `Z`
  have hgen : ∀ y ∈ tubeN N O hO, y.1 ∉ baseOf ⁻¹' R.zeroSet → ∃ j₁, ∀ j, j₁ ≤ j →
      GeneratesNear h₀ W (fun l ↦ D.capSec h₀ (σ j l)) y := by
    intro y hyU hyZ
    obtain ⟨B, hB, hBG, hyB, n₀, hs⟩ := hRT y hyZ
    refine ⟨n₀, fun j hj ↦ ?_⟩
    obtain ⟨K, s, hsmem, hsgen⟩ := hs j hj
    have hBO : IsOpen (B ∩ O) := hB.inter hO
    have hle : tubeN N (B ∩ O) hBO ≤ tubeN N B hB := tubeN_mono inter_subset_left
    choose V' hV'sub hV'o hbV' e he hrel using fun k ↦
      hσgen j (baseOf y.1) hyU (B ∩ O) hBO inter_subset_right ⟨hyB, hyU⟩
        (D.capRestrict h₀ hle (s k))
        (D.capRestrict_mem_capPole h₀ hle (prod_mono inter_subset_left subset_rfl) (hsmem k))
    set V'' : Set (Cm.{u} m) := (⋂ k, V' k) ∩ (B ∩ O)
    have hV''o : IsOpen V'' := (isOpen_iInter_of_finite hV'o).inter hBO
    refine D.generatesNear_of_combination h₀ hV''o (inter_subset_right.trans inter_subset_right)
      ⟨mem_iInter.2 hbV', hyB, hyU⟩ hsgen (σ j) (e := e)
      (fun k l ↦ (he k l).mono fun b hb ↦ mem_iInter.1 hb.1 k) fun k w hw hwV ↦ ?_
    have hw' : w ∈ preim h₀ W (tubeN N (B ∩ O) hBO) := by
      obtain ⟨hwN, -⟩ := mem_img_iff.1 ((mem_preim_iff h₀ W).1 hw)
      exact (mem_preim_iff h₀ W).2 (mem_img_iff.2 ⟨hwN, hwV.2⟩)
    have := hrel k w hw' (mem_iInter.1 hwV.1 k)
    simp only [capRestrict] at this
    rwa [evalFun_map W _ _ hw'] at this
  -- a point of `N°` off `Z`
  obtain ⟨b₁, hb₁O, hb₁Z⟩ := exists_mem_sdiff_zeroSet R hO hOG hxO
  have hann : mkPt b₁ 1 ∈ annulusRegion F.G F.ρ := by
    change splitEquiv m (mkPt b₁ 1) ∈ F.G ×ˢ overlap F.ρ
    rw [mkPt, Homeomorph.apply_symm_apply]
    exact ⟨hOG hb₁O, mem_overlap_of_norm_eq_one F.one_lt_ρ norm_one⟩
  have hy₀N : mkPt b₁ 1 ∈ N :=
    (F.mem_N _).2 ⟨by rw [baseOf_mkPt]; exact hOG hb₁O, by
      rw [fibOf_mkPt, norm_one]; exact F.one_lt_ρ⟩
  set y₀ : space N := ⟨mkPt b₁ 1, hy₀N⟩
  have hy₀U : y₀ ∈ tubeN N O hO := by
    change baseOf (mkPt b₁ 1) ∈ O
    rw [baseOf_mkPt]
    exact hb₁O
  have hy₀Z : y₀.1 ∉ baseOf ⁻¹' R.zeroSet := by
    change baseOf (mkPt b₁ 1) ∉ R.zeroSet
    rw [baseOf_mkPt]
    exact hb₁Z
  obtain ⟨j₀, hj₀⟩ := hgen y₀ hy₀U hy₀Z
  -- the chain argument and the gap criterion
  obtain ⟨U', hU'U, hxU', r, s, hs⟩ := exists_generatesNear_of_chain h₀ W F.hasThinComplement
    (F.isPreconnected_img_tubeN hOG hOc) (fun j l ↦ D.capSec h₀ (σ j l))
    (F.annulusRegion_subset _ hann) (hj₀ j₀ le_rfl) hgen hxO
  have hU'G : ∀ z ∈ (img U' : Set (Cn.{u} (m + 1))), baseOf z ∈ F.G := fun z hz ↦ by
    obtain ⟨hzN, hzU'⟩ := mem_img_iff.1 hz
    exact hOG (hU'U hzU')
  refine isCoherentAt_of_generates h₀ W F.hasThinComplement s (R.pullBase hU'G)
    (fun y hy hyZ ↦ hs y hy ?_) hxU'
  rwa [RegularPairFamily.zeroSet_pullBase] at hyZ

end

end ComplexAnalytic.Cap.AnnulusDecomposition
