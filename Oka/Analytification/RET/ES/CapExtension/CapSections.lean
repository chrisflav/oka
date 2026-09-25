/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.ES.CapExtension.Saturation

/-!
# Sections of the cap over opens of the base: combinations, uniqueness, gluing

Keep the notation of `Oka/Analytification/RET/ES/CapExtension/Setup.lean`. The sections of the cap
with a pole of order `≤ n` at infinity over opens `V × ℙ¹` of `G × ℙ¹` form a sheaf of modules over
the holomorphic functions on the base: they can be multiplied by functions of `b`
(`ComplexAnalytic.Cap.AnnulusDecomposition.exists_capPole_sum`), are determined by their evaluation
`λ` at more than `n ∑ kᵢ` points of the annulus
(`ComplexAnalytic.Cap.AnnulusDecomposition.capPole_ext`), and a tuple which is locally the
evaluation of sections is the evaluation of a section
(`ComplexAnalytic.Cap.AnnulusDecomposition.exists_capPole_of_locally`).
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

/-- The evaluation at `(b, wᵥ)` is the value at a point `y` over it, for all sections at once. -/
lemma exists_evalVec_eq_tube {M : ℕ} {w : Fin M → ℂ} (hwρ : ∀ ν, w ν ∈ overlap F.ρ)
    {V : Set (Cm.{u} m)} {hV : IsOpen V} (hVG : V ⊆ F.G) {b : Cm.{u} m} (hb : b ∈ V)
    (x : Fin M × (Σ i, Fin (D.deg i))) :
    ∃ y ∈ preim h₀ W (tubeN N V hV), baseOf (pt W y) = b ∧
      ∀ a : W.left.presheaf.obj (op (preim h₀ W (tubeN N V hV))),
        D.evalVec w a b x = evalFun a y := by
  have hbV : (splitEquiv m).symm (b, w x.1) ∈ img (tubeN N V hV) := by
    rw [F.mem_img_tubeN hVG, Homeomorph.apply_symm_apply]
    exact ⟨hb, mem_ball_zero_iff.2 (hwρ x.1).2⟩
  obtain ⟨y, hy, hpt, h⟩ := D.exists_evalVec_eq (h₀ := h₀) hwρ (hVG hb) x hbV
  refine ⟨y, hy, ?_, fun a ↦ by rw [h, evalFun_of_mem _ hy]⟩
  rw [hpt]
  simp [baseOf]

/-- **Combinations of sections of the cap** with coefficients holomorphic functions of `b`. -/
theorem exists_capPole_sum {n : ℕ} {V : Set (Cm.{u} m)} {hV : IsOpen V} (hVG : V ⊆ F.G)
    {K : ℕ} {s : Fin K → boundedSubring h₀ W (tubeN N V hV) × (D.ι → Cm.{u} m × ℂ → ℂ)}
    (hs : ∀ k, s k ∈ D.capPole h₀ n (tubeN N V hV) (V ×ˢ ball 0 F.ρ))
    {e : Fin K → Cm.{u} m → ℂ} (he : ∀ k, DifferentiableOn ℂ (e k) V) :
    ∃ t ∈ D.capPole h₀ n (tubeN N V hV) (V ×ˢ ball 0 F.ρ),
      (∀ y ∈ preim h₀ W (tubeN N V hV),
        evalFun t.1.1 y = ∑ k, e k (baseOf (pt W y)) * evalFun (s k).1.1 y) ∧
      ∀ i x, t.2 i x = ∑ k, e k x.1 * (s k).2 i x := by
  classical
  choose c hc hce hc2 using fun k ↦ D.exists_const_mem_capSubring (h₀ := h₀)
    (V := tubeN N V hV) (U := V) (F.mem_img_tubeN hVG) (he k)
  refine ⟨∑ k, c k * s k, AddSubgroup.sum_mem _ fun k _ ↦
    D.mul_mem_capPole_of_mem_capSubring (hc k) (hs k), fun y hy ↦ ?_, fun i x ↦ ?_⟩
  · have hsum : (∑ k, c k * s k).1.1 = ∑ k, (c k).1.1 * (s k).1.1 := by
      simp only [Prod.fst_sum, Prod.fst_mul, AddSubmonoidClass.coe_finsetSum,
        MulMemClass.coe_mul]
    rw [hsum, evalFun_of_mem _ hy, map_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [map_mul, ← evalFun_of_mem _ hy, ← evalFun_of_mem _ hy, hce k y hy]
  · simp only [Prod.snd_sum, Prod.snd_mul, Finset.sum_apply, Pi.mul_apply, hc2]

variable [T2Space W.left]

/-- **Sections of the cap are determined by their evaluation.** -/
theorem capPole_ext {n : ℕ} {V : Set (Cm.{u} m)} {hV : IsOpen V} (hVG : V ⊆ F.G)
    {t t' : boundedSubring h₀ W (tubeN N V hV) × (D.ι → Cm.{u} m × ℂ → ℂ)}
    (ht : t ∈ D.capPole h₀ n (tubeN N V hV) (V ×ˢ ball 0 F.ρ))
    (ht' : t' ∈ D.capPole h₀ n (tubeN N V hV) (V ×ˢ ball 0 F.ρ)) {M : ℕ}
    (hM : (∑ i, (D.deg i : ℕ)) * n < M) {w : Fin M → ℂ} (hw : Function.Injective w)
    (hwρ : ∀ ν, w ν ∈ overlap F.ρ) (h : ∀ b ∈ V, D.evalVec w t.1.1 b = D.evalVec w t'.1.1 b) :
    t.1 = t'.1 ∧ ∀ i, EqOn (t.2 i) (t'.2 i) (Kummer.powMap (D.deg i) ⁻¹' (V ×ˢ ball 0 F.ρ)) := by
  obtain ⟨h1, h2⟩ := D.eq_zero_of_forall_evalVec_eq_zero F.hasThinComplement
    F.annulusRegion_subset F.one_lt_ρ hVG (F.mem_img_tubeN hVG) hM hw hwρ (sub_mem ht ht')
    fun b hb ↦ funext fun x ↦ by
      obtain ⟨y, hyO, -, hy⟩ := D.exists_evalVec_eq_tube h₀ hwρ hVG hb x
      have := congrFun (h b hb) x
      rw [hy, hy] at this
      rw [hy]
      change evalFun (t.1.1 - t'.1.1) y = 0
      rw [evalFun_of_mem _ hyO, map_sub, ← evalFun_of_mem _ hyO, ← evalFun_of_mem _ hyO, this,
        sub_self]
  refine ⟨sub_eq_zero.1 h1, fun i z hz ↦ sub_eq_zero.1 (h2 i hz)⟩

omit [T2Space W.left] in
lemma evalVec_capRestrict {M : ℕ} {w : Fin M → ℂ} (hwρ : ∀ ν, w ν ∈ overlap F.ρ)
    {V V' : Set (Cm.{u} m)} {hV : IsOpen V} {hV' : IsOpen V'} (hV'G : V' ⊆ F.G) (h : V' ⊆ V)
    (t : boundedSubring h₀ W (tubeN N V hV) × (D.ι → Cm.{u} m × ℂ → ℂ)) {b : Cm.{u} m}
    (hb : b ∈ V') :
    D.evalVec w (D.capRestrict h₀ (tubeN_mono (hV := hV) (hV' := hV') h) t).1.1 b =
      D.evalVec w t.1.1 b := by
  funext x
  refine D.evalVec_map (tubeN_mono h) hwρ (hV'G hb) x ?_ t.1.1
  rw [F.mem_img_tubeN hV'G, Homeomorph.apply_symm_apply]
  exact ⟨hb, mem_ball_zero_iff.2 (hwρ x.1).2⟩

/-- **Gluing sections of the cap**: a tuple which is locally the evaluation of sections of the cap
is the evaluation of a section. -/
theorem exists_capPole_of_locally {n : ℕ} {U : Set (Cm.{u} m)} {hU : IsOpen U} (hUG : U ⊆ F.G)
    {M : ℕ} (hM : (∑ i, (D.deg i : ℕ)) * n < M) {w : Fin M → ℂ} (hw : Function.Injective w)
    (hwρ : ∀ ν, w ν ∈ overlap F.ρ) {v : Fin M × (Σ i, Fin (D.deg i)) → Cm.{u} m → ℂ}
    (hloc : ∀ b ∈ U, ∃ (B : Set (Cm.{u} m)) (hB : IsOpen B), B ⊆ U ∧ b ∈ B ∧
      ∃ t ∈ D.capPole h₀ n (tubeN N B hB) (B ×ˢ ball 0 F.ρ),
        ∀ b' ∈ B, ∀ x, D.evalVec w t.1.1 b' x = v x b') :
    ∃ t ∈ D.capPole h₀ n (tubeN N U hU) (U ×ˢ ball 0 F.ρ),
      ∀ b ∈ U, ∀ x, D.evalVec w t.1.1 b x = v x b := by
  classical
  choose B hB hBU hbB t ht htv using fun p : U ↦ hloc p.1 p.2
  have hBG : ∀ p, B p ⊆ F.G := fun p ↦ (hBU p).trans hUG
  -- the sections agree on overlaps
  have hagree : ∀ p q : U, (∀ y ∈ preim h₀ W (tubeN N (B p ∩ B q) ((hB p).inter (hB q))),
      evalFun (t p).1.1 y = evalFun (t q).1.1 y) ∧ ∀ i, EqOn ((t p).2 i) ((t q).2 i)
        (Kummer.powMap (D.deg i) ⁻¹' ((B p ∩ B q) ×ˢ ball 0 F.ρ)) := by
    intro p q
    have hpq : B p ∩ B q ⊆ F.G := inter_subset_left.trans (hBG p)
    have hp := D.capRestrict_mem_capPole h₀ (tubeN_mono (hV := hB p)
      (hV' := (hB p).inter (hB q)) inter_subset_left)
      (prod_mono (inter_subset_left : B p ∩ B q ⊆ B p) subset_rfl) (ht p)
    have hq := D.capRestrict_mem_capPole h₀ (tubeN_mono (hV := hB q)
      (hV' := (hB p).inter (hB q)) inter_subset_right)
      (prod_mono (inter_subset_right : B p ∩ B q ⊆ B q) subset_rfl) (ht q)
    obtain ⟨h1, h2⟩ := D.capPole_ext h₀ hpq hp hq hM hw hwρ fun b hb ↦ by
      rw [D.evalVec_capRestrict h₀ hwρ hpq inter_subset_left _ hb,
        D.evalVec_capRestrict h₀ hwρ hpq inter_subset_right _ hb]
      funext x
      rw [htv p b hb.1, htv q b hb.2]
    refine ⟨fun y hy ↦ ?_, fun i z hz ↦ h2 i hz⟩
    have := congrArg (fun a : boundedSubring h₀ W _ ↦ evalFun a.1 y) h1
    simp only [capRestrict] at this
    rwa [evalFun_map W _ _ hy, evalFun_map W _ _ hy] at this
  -- gluing the parts over `N`
  set O : U → (space N).Opens := fun p ↦ tubeN N (B p) (hB p)
  have hOU : ∀ p, O p ≤ tubeN N U hU := fun p ↦ tubeN_mono (hBU p)
  have hcov : tubeN N U hU ≤ iSup O := fun y hy ↦
    TopologicalSpace.Opens.mem_iSup.2 ⟨⟨baseOf y.1, hy⟩, hbB ⟨baseOf y.1, hy⟩⟩
  obtain ⟨a₀, ha₀, -⟩ := AlgebraicGeometry.LocallyRingedSpace.modRes_existsUnique_gluing
    (boundedModule h₀ W) O hcov hOU (fun p ↦ mkSec h₀ W (t p).1.1 (t p).1.2) fun p q ↦ by
      refine secVal_ext h₀ W fun y hy ↦ ?_
      have hy' : y ∈ preim h₀ W (tubeN N (B p ∩ B q) ((hB p).inter (hB q))) := by
        rw [mem_preim_iff] at hy ⊢
        obtain ⟨hyN, hyV⟩ := mem_img_iff.1 hy
        exact mem_img_iff.2 ⟨hyN, hyV.1, hyV.2⟩
      change evalFun (secVal h₀ W (sectRes (boundedModule h₀ W) _ _)) y =
        evalFun (secVal h₀ W (sectRes (boundedModule h₀ W) _ _)) y
      rw [secVal_map, secVal_map, evalFun_map W _ _ hy, evalFun_map W _ _ hy, secVal_mkSec,
        secVal_mkSec]
      exact (hagree p q).1 y hy'
  have ha₀val : ∀ p : U, ∀ y ∈ preim h₀ W (O p), evalFun (secVal h₀ W a₀) y =
      evalFun (t p).1.1 y := by
    intro p y hy
    have := congrArg (fun a ↦ evalFun (secVal h₀ W a) y) (ha₀ p)
    rw [show modRes a₀ (O p) (hOU p) = sectRes (boundedModule h₀ W) (hOU p) a₀ from rfl,
      secVal_map, evalFun_map W _ _ hy, secVal_mkSec] at this
    exact this
  -- the functions at infinity
  set f : D.ι → Cm.{u} m × ℂ → ℂ := fun i z ↦
    if hz : z.1 ∈ U then (t ⟨z.1, hz⟩).2 i z else 0
  have hf : ∀ i (p : U) z, z.1 ∈ B p → ‖z.2 ^ (D.deg i : ℕ)‖ < F.ρ → f i z = (t p).2 i z := by
    intro i p z hzp hzρ
    have hzU : z.1 ∈ U := hBU p hzp
    simp only [f, dif_pos hzU]
    exact (hagree ⟨z.1, hzU⟩ p).2 i ⟨⟨hbB ⟨z.1, hzU⟩, hzp⟩, mem_ball_zero_iff.2 hzρ⟩
  refine ⟨(⟨secVal h₀ W a₀, secVal_mem h₀ W a₀⟩, f), ⟨fun i z hz ↦ ?_, fun i z hz hz' ↦ ?_⟩,
    fun b hb x ↦ ?_⟩
  · -- holomorphy at infinity
    have hzU : z.1 ∈ U := hz.1
    set p : U := ⟨z.1, hzU⟩
    have hopen : IsOpen (Kummer.powMap (D.deg i) ⁻¹' (B p ×ˢ ball (0 : ℂ) F.ρ)) :=
      ((hB p).prod isOpen_ball).preimage (Kummer.continuous_powMap _)
    have hzB : z ∈ Kummer.powMap (D.deg i) ⁻¹' (B p ×ˢ ball (0 : ℂ) F.ρ) := ⟨hbB p, hz.2⟩
    refine (((ht p).1 i).differentiableAt (hopen.mem_nhds hzB)).congr_of_eventuallyEq
      ?_ |>.differentiableWithinAt
    filter_upwards [hopen.mem_nhds hzB] with z' hz'
    exact hf i p z' hz'.1 (mem_ball_zero_iff.1 hz'.2)
  · -- the relation at infinity
    have hzU : z.1 ∈ U := hz'.1
    set p : U := ⟨z.1, hzU⟩
    obtain ⟨hzb, hzO⟩ := hz
    have hzOp : D.toFun ⟨i, ⟨z, hzb⟩⟩ ∈ preim h₀ W (O p) := by
      obtain ⟨hN, -⟩ := mem_img_iff.1 ((mem_preim_iff h₀ W).1 hzO)
      refine (mem_preim_iff h₀ W).2 (mem_img_iff.2 ⟨hN, ?_⟩)
      change baseOf (pt W (D.toFun ⟨i, ⟨z, hzb⟩⟩)) ∈ B p
      rw [D.pt_toFun]
      simpa [baseOf] using hbB p
    have hzpiece : z ∈ D.pieceSet (preim h₀ W (O p)) i := ⟨hzb, hzOp⟩
    have hrel := (ht p).2 i z hzpiece ⟨hbB p, hz'.2⟩
    change D.kummerVal (secVal h₀ W a₀) i z = z.2 ^ (n * D.deg i) * f i (invCoord z)
    rw [D.kummerVal_of_mem _ _ hzb, ha₀val p _ hzOp, ← D.kummerVal_of_mem _ _ hzb, hrel,
      hf i p (invCoord z) (hbB p) (mem_ball_zero_iff.1 hz'.2)]
  · -- the evaluation
    set p : U := ⟨b, hb⟩
    have hres : D.capRestrict h₀ (hOU p) (⟨secVal h₀ W a₀, secVal_mem h₀ W a₀⟩, f) =
        (⟨(t p).1.1, (t p).1.2⟩, f) := by
      refine Prod.ext (Subtype.ext ?_) rfl
      have := congrArg (secVal h₀ W) (ha₀ p)
      exact this
    have := D.evalVec_capRestrict h₀ hwρ (hBG p) (hBU p) (hV := hU) (hV' := hB p)
      (⟨secVal h₀ W a₀, secVal_mem h₀ W a₀⟩, f) (hbB p)
    rw [hres] at this
    change D.evalVec w (secVal h₀ W a₀) b x = v x b
    rw [← this]
    exact htv p b (hbB p) x

end

end ComplexAnalytic.Cap.AnnulusDecomposition
