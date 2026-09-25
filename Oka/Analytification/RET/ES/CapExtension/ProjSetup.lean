/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.ES.CapExtension.LocalGen
import Oka.Analytification.RET.ES.Codim2.BlowupSheaf

/-!
# The cap as a cover of `ℂᵐ × ℙ¹`

Keep the notation of `Oka/Analytification/RET/ES/CapExtension/Setup.lean`. The cap over `G × ℙ¹`
is glued from `W`, which lies over the chart `w` of `P^an = ℂᵐ × ℙ¹`
(`ComplexAnalytic.relProjectiveSpaceAn`), and the Kummer covers `u' ↦ u'^{kᵢ}` of the discs
`{‖w'‖ < ρ}` of the chart `w' = w⁻¹` at infinity. We realise the Kummer covers as the disjoint open
pieces `{‖(t - cᵢ)^{kᵢ}‖ < ρ}` of `ℂ^{m+1}` (`ComplexAnalytic.Cap.AnnulusDecomposition.kPiece`),
translated in the fibre coordinate `t` by `cᵢ` so that they do not meet, with Kummer coordinate
`u' = t - cᵢ` (`ComplexAnalytic.Cap.AnnulusDecomposition.kCoord`).

This file defines the maps `W ⟶ P^an` (`ComplexAnalytic.Cap.AnnulusDecomposition.projW`) and
`K ⟶ P^an` (`ComplexAnalytic.Cap.AnnulusDecomposition.kMap`) from `W` and from the union `K` of the
pieces, and the point of `K` corresponding to a point of `W` over the annulus
(`ComplexAnalytic.Cap.AnnulusDecomposition.projW_toFun`).
-/

open CategoryTheory Opposite Topology Set Filter Metric

universe u

namespace ComplexAnalytic.Cap.AnnulusDecomposition

open AnalyticSpace BoundedSections relProjectiveSpaceAn relProjectiveLine
open KummerModel (splitEquiv)

noncomputable section

variable {m : ℕ}

/-! ### The chart `w` -/

/-- The point of `P^an` with base coordinates `b` and fibre coordinate `w` in the chart `0`, for
`x = (b, w) ∈ ℂ^{m+1}`. -/
def chart0Pt (x : Cn.{u} (m + 1)) : relProjectiveSpaceAn.{u} m 1 :=
  chartPt 0 (baseCoord (baseOf x), fibOf x)

lemma differentiable_baseCoord_baseOf :
    Differentiable ℂ fun x : Cn.{u} (m + 1) ↦ baseCoord (baseOf x) := fun x ↦
  (differentiable_baseCoord (baseOf x)).comp x (differentiable_baseOf x)

lemma differentiable_chart0Fun :
    Differentiable ℂ fun x : Cn.{u} (m + 1) ↦ cptFun.{u} (baseCoord (baseOf x), fibOf x) :=
  differentiable_cptFun.comp (differentiable_baseCoord_baseOf.prodMk differentiable_fibOf)

variable (N₀ : (AnalyticSpace.complexAffineSpace.{u} (m + 1)).Opens)

/-- The coordinates of the chart `0` of `P^an`, as holomorphic functions on `N°`. -/
def chart0Coord (k : ULift.{u} (Fin (1 + m))) : (space N₀).presheaf.obj (op ⊤) :=
  OkaRing.ofDifferentiableOn (fun x ↦ cptFun.{u} (baseCoord (baseOf x), fibOf x) k)
    ((differentiable_pi.1 differentiable_chart0Fun k).differentiableOn)

/-- The map `N° ⟶ P^an`, `(b, w) ↦ (b, [1 : w])`. -/
def chart0Map : space N₀ ⟶ relProjectiveSpaceAn.{u} m 1 :=
  okaMapOpen (chart0Coord N₀) ≫ relProjectiveSpaceAnChart.{u} 0

lemma chart0Map_base (x : space N₀) : (chart0Map N₀).toLRSHom.base x = chart0Pt x.1 := by
  change (chartLRS.{u} 0).base ((okaMapOpenHom (chart0Coord N₀)).base x) = _
  rw [base_okaMapOpenHom, chart0Pt, chartPt]
  congr 1
  funext k
  exact OkaRing.toGlobalFun_apply (U := img (⊤ : (space N₀).Opens)) _
    ((mem_functor_obj_top_iff N₀ x.1).2 x.2)

variable {N₀} (W : FiniteEtaleOver (space N₀))

/-- **The map `W ⟶ P^an`**, the composite of `p : W ⟶ N°` and `N° ⟶ P^an`. -/
def projW : W.left ⟶ relProjectiveSpaceAn.{u} m 1 :=
  cov W ≫ chart0Map N₀

lemma projW_base (w : W.left) : (projW W).toLRSHom.base w = chart0Pt (pt W w) :=
  chart0Map_base N₀ _

/-! ### The Kummer pieces at infinity -/

variable {N : (AnalyticSpace.complexAffineSpace.{u} (m + 1)).Opens} {W} {F : WeierstrassForm N N₀}
  (D : AnnulusDecomposition W F.G F.ρ)

/-- The translation `cᵢ` of the `i`-th Kummer piece. -/
def kShift (i : D.ι) : ℂ :=
  ((3 * (F.ρ + 1) : ℝ) : ℂ) * ((Fintype.equivFin D.ι i : ℕ) : ℂ)

/-- The `i`-th Kummer piece `{b ∈ G, ‖(t - cᵢ)^{kᵢ}‖ < ρ}`. -/
def kPiece (i : D.ι) : Set (Cn.{u} (m + 1)) :=
  {x | baseOf x ∈ F.G ∧ ‖(fibOf x - D.kShift i) ^ (D.deg i : ℕ)‖ < F.ρ}

lemma isOpen_kPiece (i : D.ι) : IsOpen (D.kPiece i) :=
  (F.isOpen_G.preimage continuous_baseOf).inter (isOpen_lt
    (continuous_norm.comp ((continuous_fibOf.sub continuous_const).pow _)) continuous_const)

lemma norm_lt_of_mem_kPiece {i : D.ι} {x : Cn.{u} (m + 1)} (hx : x ∈ D.kPiece i) :
    ‖fibOf x - D.kShift i‖ < F.ρ := by
  by_contra h
  push Not at h
  have h1 : 1 ≤ ‖fibOf x - D.kShift i‖ := F.one_lt_ρ.le.trans h
  have := hx.2
  rw [norm_pow] at this
  have h2 : ‖fibOf x - D.kShift i‖ ≤ ‖fibOf x - D.kShift i‖ ^ (D.deg i : ℕ) :=
    le_self_pow₀ h1 (D.deg i).ne_zero
  linarith

lemma eq_of_mem_kPiece {i j : D.ι} {x : Cn.{u} (m + 1)} (hi : x ∈ D.kPiece i)
    (hj : x ∈ D.kPiece j) : i = j := by
  by_contra hij
  have hρ := F.one_lt_ρ
  have h1 := D.norm_lt_of_mem_kPiece hi
  have h2 := D.norm_lt_of_mem_kPiece hj
  set a : ℕ := (Fintype.equivFin D.ι i : ℕ)
  set b : ℕ := (Fintype.equivFin D.ι j : ℕ)
  have hne : a ≠ b := fun h ↦ hij ((Fintype.equivFin D.ι).injective (Fin.ext h))
  have hd : (1 : ℝ) ≤ ‖(a : ℂ) - (b : ℂ)‖ := by
    rw [show (a : ℂ) - (b : ℂ) = ((a : ℝ) - (b : ℝ) : ℝ) by push_cast; rfl,
      Complex.norm_real, Real.norm_eq_abs]
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have : ((Fintype.equivFin D.ι i : ℕ) : ℝ) + 1 ≤ (Fintype.equivFin D.ι j : ℕ) := by
        exact_mod_cast h
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]
      linarith
    · have : ((Fintype.equivFin D.ι j : ℕ) : ℝ) + 1 ≤ (Fintype.equivFin D.ι i : ℕ) := by
        exact_mod_cast h
      rw [abs_of_nonneg (by linarith)]
      linarith
  have hsh : ‖D.kShift i - D.kShift j‖ = 3 * (F.ρ + 1) *
      ‖((Fintype.equivFin D.ι i : ℕ) : ℂ) - ((Fintype.equivFin D.ι j : ℕ) : ℂ)‖ := by
    rw [kShift, kShift, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have htri : ‖D.kShift i - D.kShift j‖ ≤ ‖fibOf x - D.kShift j‖ + ‖fibOf x - D.kShift i‖ := by
    calc ‖D.kShift i - D.kShift j‖ = ‖(fibOf x - D.kShift j) - (fibOf x - D.kShift i)‖ := by
          ring_nf
      _ ≤ _ := norm_sub_le _ _
  nlinarith

/-- The union `K` of the Kummer pieces, an open of `ℂ^{m+1}`. -/
def kOpens : (AnalyticSpace.complexAffineSpace.{u} (m + 1)).Opens :=
  ⟨⋃ i, D.kPiece i, isOpen_iUnion D.isOpen_kPiece⟩

lemma mem_kOpens {x : Cn.{u} (m + 1)} : x ∈ D.kOpens ↔ ∃ i, x ∈ D.kPiece i :=
  mem_iUnion

open Classical in
/-- The Kummer coordinate `u' = t - cᵢ` on the `i`-th piece. -/
def kCoord (x : Cn.{u} (m + 1)) : ℂ :=
  ∑ i, if x ∈ D.kPiece i then fibOf x - D.kShift i else 0

open Classical in
/-- The coordinate `w' = u'^{kᵢ}` of the chart at infinity, on the `i`-th piece. -/
def kVal (x : Cn.{u} (m + 1)) : ℂ :=
  ∑ i, if x ∈ D.kPiece i then (fibOf x - D.kShift i) ^ (D.deg i : ℕ) else 0

lemma kCoord_of_mem {i : D.ι} {x : Cn.{u} (m + 1)} (hx : x ∈ D.kPiece i) :
    D.kCoord x = fibOf x - D.kShift i := by
  classical
  rw [kCoord, Finset.sum_eq_single i (fun j _ hji ↦ if_neg fun hj ↦ hji (D.eq_of_mem_kPiece hj hx))
    (fun h ↦ absurd (Finset.mem_univ i) h), if_pos hx]

lemma kVal_of_mem {i : D.ι} {x : Cn.{u} (m + 1)} (hx : x ∈ D.kPiece i) :
    D.kVal x = (fibOf x - D.kShift i) ^ (D.deg i : ℕ) := by
  classical
  rw [kVal, Finset.sum_eq_single i (fun j _ hji ↦ if_neg fun hj ↦ hji (D.eq_of_mem_kPiece hj hx))
    (fun h ↦ absurd (Finset.mem_univ i) h), if_pos hx]

lemma kVal_eq_kCoord_pow {i : D.ι} {x : Cn.{u} (m + 1)} (hx : x ∈ D.kPiece i) :
    D.kVal x = D.kCoord x ^ (D.deg i : ℕ) := by
  rw [D.kVal_of_mem hx, D.kCoord_of_mem hx]

lemma differentiableOn_kCoord : DifferentiableOn ℂ D.kCoord {x | x ∈ D.kOpens} := by
  intro x hx
  obtain ⟨i, hi⟩ := D.mem_kOpens.1 hx
  have hd := (differentiable_fibOf.sub_const (D.kShift i)).differentiableAt (x := x)
  refine (hd.congr_of_eventuallyEq ?_).differentiableWithinAt
  filter_upwards [(D.isOpen_kPiece i).mem_nhds hi] with y hy using D.kCoord_of_mem hy

lemma differentiableOn_kVal : DifferentiableOn ℂ D.kVal {x | x ∈ D.kOpens} := by
  intro x hx
  obtain ⟨i, hi⟩ := D.mem_kOpens.1 hx
  refine ((((differentiable_fibOf.sub_const (D.kShift i)).pow (D.deg i : ℕ)).differentiableAt
    (x := x)).congr_of_eventuallyEq ?_)
    |>.differentiableWithinAt
  filter_upwards [(D.isOpen_kPiece i).mem_nhds hi] with y hy using D.kVal_of_mem hy

/-- The point of the `i`-th piece with Kummer coordinates `(b, u')`. -/
def kPt (i : D.ι) (z : Cm.{u} m × ℂ) : Cn.{u} (m + 1) :=
  mkPt z.1 (z.2 + D.kShift i)

lemma kPt_mem {i : D.ι} {z : Cm.{u} m × ℂ} (hz : z.1 ∈ F.G) (hz' : ‖z.2 ^ (D.deg i : ℕ)‖ < F.ρ) :
    D.kPt i z ∈ D.kPiece i := by
  refine ⟨by rw [kPt, baseOf_mkPt]; exact hz, ?_⟩
  rw [kPt, fibOf_mkPt, add_sub_cancel_right]
  exact hz'

@[simp]
lemma baseOf_kPt (i : D.ι) (z : Cm.{u} m × ℂ) : baseOf (D.kPt i z) = z.1 :=
  baseOf_mkPt _ _

lemma kCoord_kPt {i : D.ι} {z : Cm.{u} m × ℂ} (hz : D.kPt i z ∈ D.kPiece i) :
    D.kCoord (D.kPt i z) = z.2 := by
  rw [D.kCoord_of_mem hz, kPt, fibOf_mkPt, add_sub_cancel_right]

lemma kVal_kPt {i : D.ι} {z : Cm.{u} m × ℂ} (hz : D.kPt i z ∈ D.kPiece i) :
    D.kVal (D.kPt i z) = z.2 ^ (D.deg i : ℕ) := by
  rw [D.kVal_eq_kCoord_pow hz, D.kCoord_kPt hz]

/-- A point of the `i`-th piece is the point with its Kummer coordinates. -/
lemma kPt_kCoord {i : D.ι} {x : Cn.{u} (m + 1)} (hx : x ∈ D.kPiece i) :
    D.kPt i (baseOf x, D.kCoord x) = x := by
  rw [kPt, D.kCoord_of_mem hx, sub_add_cancel, mkPt_baseOf_fibOf]

/-- The coordinates of the chart `1` of `P^an` on `K`. -/
def kMapCoord (k : ULift.{u} (Fin (1 + m))) : (space D.kOpens).presheaf.obj (op ⊤) :=
  OkaRing.ofDifferentiableOn (fun x ↦ cptFun.{u} (baseCoord (baseOf x), D.kVal x) k) (by
    have hd : DifferentiableOn ℂ (fun x ↦ cptFun.{u} (baseCoord (baseOf x), D.kVal x))
        {x | x ∈ D.kOpens} :=
      differentiable_cptFun.comp_differentiableOn
        (differentiable_baseCoord_baseOf.differentiableOn.prodMk D.differentiableOn_kVal)
    exact ((differentiableOn_pi.1 hd) k).mono fun x hx ↦ (mem_functor_obj_top_iff _ x).1 hx)

/-- **The map `K ⟶ P^an`**, `x ↦ (b, [w' : 1])` with `w' = u'^{kᵢ}` on the `i`-th piece. -/
def kMap : space D.kOpens ⟶ relProjectiveSpaceAn.{u} m 1 :=
  okaMapOpen D.kMapCoord ≫ relProjectiveSpaceAnChart.{u} 1

lemma kMap_base (x : space D.kOpens) :
    D.kMap.toLRSHom.base x = chartPt 1 (baseCoord (baseOf x.1), D.kVal x.1) := by
  change (chartLRS.{u} 1).base ((okaMapOpenHom D.kMapCoord).base x) = _
  rw [base_okaMapOpenHom, chartPt]
  congr 1
  funext k
  exact OkaRing.toGlobalFun_apply (U := img (⊤ : (space D.kOpens).Opens)) _
    ((mem_functor_obj_top_iff _ x.1).2 x.2)

/-- The point of `K` corresponding to the point of `W` with Kummer coordinates `z` over the
annulus. -/
lemma kPt_invCoord_mem {i : D.ι} {z : Cm.{u} m × ℂ}
    (hz : z ∈ KummerAnnulus.base F.G F.ρ⁻¹ F.ρ (D.deg i)) :
    D.kPt i (invCoord z) ∈ D.kPiece i := by
  refine D.kPt_mem hz.1 ?_
  have h0 : 0 < ‖z.2‖ := KummerAnnulus.pos_of_mem_base F.G
    (inv_nonneg.2 F.pos_ρ.le) (D.deg i).ne_zero hz
  change ‖(z.2⁻¹) ^ (D.deg i : ℕ)‖ < F.ρ
  rw [inv_pow, norm_inv, norm_pow]
  exact inv_lt_of_inv_lt₀ F.pos_ρ hz.2.1

/-- **The gluing of `W` and `K`**: the point of `W` with Kummer coordinates `z = (b, u)` over the
annulus and the point of `K` with Kummer coordinates `(b, u⁻¹)` have the same image in `P^an`. -/
lemma projW_toFun (i : D.ι) (z : KummerAnnulus.base F.G F.ρ⁻¹ F.ρ (D.deg i)) :
    (projW W).toLRSHom.base (D.toFun ⟨i, z⟩) =
      D.kMap.toLRSHom.base ⟨D.kPt i (invCoord z.1),
        D.mem_kOpens.2 ⟨i, D.kPt_invCoord_mem z.2⟩⟩ := by
  have h0 : z.1.2 ≠ 0 := norm_pos_iff.1 (KummerAnnulus.pos_of_mem_base F.G
    (inv_nonneg.2 F.pos_ρ.le) (D.deg i).ne_zero z.2)
  rw [projW_base, D.pt_toFun, D.kMap_base, D.kVal_kPt (D.kPt_invCoord_mem z.2), chart0Pt,
    baseOf_kPt]
  simp only [baseOf_mkPt, fibOf_mkPt, invCoord]
  rw [chartPt_zero_eq_chartPt_one (pow_ne_zero _ h0), inv_pow]

end

end ComplexAnalytic.Cap.AnnulusDecomposition
