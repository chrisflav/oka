/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.ES.CapExtension.Liouville
import Oka.Analytification.RET.ES.CapExtension.RegularPull
import Oka.Analytification.RET.ES.EvaluationCramer

/-!
# Sections of the cap over opens of the base

Keep the notation of `Oka/Analytification/RET/ES/GrauertRemmert/WeierstrassForm.lean`: `(N, N°)` is
in Weierstrass form `N = G × {‖w‖ < ρ}`, `N° = {P(b)(w) ≠ 0}`. For an open `V ⊆ G`,
`V × {‖w‖ < ρ}` is an open of `N` (`ComplexAnalytic.BoundedSections.tubeN`), and the sections of the
cap over `V × ℙ¹` with a pole of order `≤ n` at infinity are
`ComplexAnalytic.Cap.AnnulusDecomposition.capPole` over it. This file collects the basic facts:
`N ∖ N°` is thin (`ComplexAnalytic.BoundedSections.WeierstrassForm.hasThinComplement`), and
there are evaluation points in the annulus (`ComplexAnalytic.Cap.exists_nodes`).
-/

open CategoryTheory Opposite Topology Set Filter Polynomial Metric

universe u

namespace ComplexAnalytic.Cap

open Complex.ProjectiveLineBundle

/-- **Evaluation points**: `M` distinct points in the annulus `{ρ⁻¹ < ‖w‖ < ρ}`. -/
lemma exists_nodes {ρ : ℝ} (hρ : 1 < ρ) (M : ℕ) :
    ∃ w : Fin M → ℂ, Function.Injective w ∧ ∀ ν, w ν ∈ overlap ρ := by
  set ε : ℝ := (ρ - 1) / (M + 1)
  have hε : 0 < ε := div_pos (by linarith) (by positivity)
  refine ⟨fun ν ↦ ((1 + (ν : ℕ) * ε : ℝ) : ℂ), fun ν ν' h ↦ ?_, fun ν ↦ ?_⟩
  · have h' : (1 + (ν : ℕ) * ε : ℝ) = 1 + (ν' : ℕ) * ε := Complex.ofReal_injective h
    have : ((ν : ℕ) : ℝ) = (ν' : ℕ) := by
      have := mul_right_cancel₀ hε.ne' (add_left_cancel h')
      exact this
    exact Fin.ext (by exact_mod_cast this)
  · have hν : ((ν : ℕ) : ℝ) < M + 1 := by
      have := ν.2
      exact_mod_cast Nat.lt_succ_of_lt this
    have h0 : 0 ≤ (ν : ℕ) * ε := by positivity
    have h1 : (ν : ℕ) * ε < ρ - 1 := by
      calc (ν : ℕ) * ε < (M + 1) * ε := mul_lt_mul_of_pos_right hν hε
        _ = ρ - 1 := by rw [mul_div_cancel₀]; positivity
    have hn : ‖((1 + (ν : ℕ) * ε : ℝ) : ℂ)‖ = 1 + (ν : ℕ) * ε := by
      rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    refine ⟨?_, ?_⟩
    · rw [hn]
      exact (inv_lt_one_of_one_lt₀ hρ).trans_le (by linarith)
    · rw [hn]
      linarith

end ComplexAnalytic.Cap

namespace ComplexAnalytic.BoundedSections

open AnalyticSpace KummerModel Cap

noncomputable section

variable {m : ℕ} {N N₀ : (AnalyticSpace.complexAffineSpace.{u} (m + 1)).Opens}

variable (N) in
/-- The open `V × {‖w‖ < ρ}` of `N`: the points of `N` over an open `V` of the base. -/
def tubeN (V : Set (Cm.{u} m)) (hV : IsOpen V) : (space N).Opens :=
  ⟨{x | baseOf x.1 ∈ V}, hV.preimage (continuous_baseOf.comp continuous_subtype_val)⟩

lemma tubeN_mono {V V' : Set (Cm.{u} m)} {hV : IsOpen V} {hV' : IsOpen V'} (h : V' ⊆ V) :
    tubeN N V' hV' ≤ tubeN N V hV :=
  fun _ hx ↦ h hx

namespace WeierstrassForm

variable (F : WeierstrassForm N N₀)

lemma mem_img_tubeN {V : Set (Cm.{u} m)} {hV : IsOpen V} (hVG : V ⊆ F.G) (x : Cn.{u} (m + 1)) :
    x ∈ img (tubeN N V hV) ↔ splitEquiv m x ∈ V ×ˢ ball (0 : ℂ) F.ρ := by
  rw [mem_img_iff]
  constructor
  · rintro ⟨hxN, hxV⟩
    exact ⟨hxV, mem_ball_zero_iff.2 ((F.mem_N x).1 hxN).2⟩
  · rintro ⟨hxV, hxρ⟩
    exact ⟨(F.mem_N x).2 ⟨hVG hxV, mem_ball_zero_iff.1 hxρ⟩, hxV⟩

lemma img_tubeN_eq {V : Set (Cm.{u} m)} {hV : IsOpen V} (hVG : V ⊆ F.G) :
    (img (tubeN N V hV) : Set (Cn.{u} (m + 1))) = splitEquiv m ⁻¹' (V ×ˢ ball (0 : ℂ) F.ρ) :=
  Set.ext fun x ↦ F.mem_img_tubeN hVG x

/-- Over a convex open `V ⊆ G`, `V × {‖w‖ < ρ}` is preconnected. -/
lemma isPreconnected_img_tubeN {V : Set (Cm.{u} m)} {hV : IsOpen V} (hVG : V ⊆ F.G)
    (hVc : Convex ℝ V) : IsPreconnected (img (tubeN N V hV) : Set (Cn.{u} (m + 1))) := by
  rw [F.img_tubeN_eq hVG]
  have hc : Convex ℝ (V ×ˢ ball (0 : ℂ) F.ρ) := hVc.prod (convex_ball 0 F.ρ)
  have : splitEquiv m ⁻¹' (V ×ˢ ball (0 : ℂ) F.ρ) =
      (splitEquiv m).symm '' (V ×ˢ ball (0 : ℂ) F.ρ) :=
    (congrFun (splitEquiv m).image_symm _).symm
  rw [this]
  exact hc.isPreconnected.image _ (splitEquiv m).symm.continuous.continuousOn

include F in
/-- **The complement of `N°` in `N` is thin**: it is the zero set of `(b, w) ↦ P(b)(w)`. -/
theorem hasThinComplement : HasThinComplement N N₀ := by
  refine ⟨polyFun F.P, (differentiableOn_polyFun F.differentiableOn_coeff).mono
    fun x hx ↦ ((F.mem_N x).1 hx).1, ?_, fun x hx hx₀ ↦ ?_⟩
  · refine eq_empty_iff_forall_notMem.2 fun x hx ↦ ?_
    have hxN : x ∈ N := (interior_subset hx).1
    have hev : ∀ᶠ y in 𝓝 x, polyFun F.P y = 0 :=
      Filter.mem_of_superset (isOpen_interior.mem_nhds hx) fun y hy ↦ (interior_subset hy).2
    have ht : Tendsto (fun t : ℂ ↦ mkPt (baseOf x) (fibOf x + t)) (𝓝 0) (𝓝 x) := by
      have hc : Continuous fun t : ℂ ↦ mkPt (baseOf x) (fibOf x + t) :=
        differentiable_mkPt.continuous.comp (continuous_const.prodMk
          (continuous_const.add continuous_id))
      simpa [mkPt_baseOf_fibOf] using hc.tendsto 0
    refine BPointData.not_eventually_eval_eq_zero (F.monic.map
      (Pi.evalRingHom (fun _ ↦ ℂ) (baseOf x))).ne_zero (fibOf x) ?_
    filter_upwards [ht.eventually hev] with t ht
    simpa [polyFun] using ht
  · by_contra h
    exact hx₀ ((F.mem_N₀ x hx).2 h)

end WeierstrassForm

end

end ComplexAnalytic.BoundedSections
