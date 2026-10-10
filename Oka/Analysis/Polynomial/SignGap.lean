/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Order.IntermediateValue

/-!
# Signs of a real polynomial between the roots of its derivative

Let `Z ⊆ ℝ` be a finite set containing every root of `p'` (the derivative of a real polynomial
`p`). On every *gap* of `Z` — a maximal interval of `ℝ ∖ Z`; two points lie in the same gap when
`Polynomial.SameGap Z y y'` — the derivative has constant sign, so `p` is strictly monotone. This
file reads off the sign of `p` at a point `y ∉ Z` from the signs of `p` at the two neighbours of
`y` in `Z` and from the sign of `p'(y)`:

* `Polynomial.sign_eval_of_not_leftAnchor`: if `a` is the left neighbour of `y` in `Z` and
  `sign p(a) ≠ -sign p'(y)`, then `sign p(y) = sign p'(y)`;
* `Polynomial.sign_eval_of_not_rightAnchor`: symmetrically on the right;
* `Polynomial.exists_root_of_anchor`: otherwise (`Polynomial.LeftAnchor` and
  `Polynomial.RightAnchor`, where a missing neighbour counts as an anchor because `|p| → ∞`),
  `p` has a unique root `r` in the gap of `y`, and `sign p(y') = sign p'(y) * sign (y' - r)`
  throughout that gap.

Together with `Polynomial.sign_eval_eq_of_forall_ne_zero` (a polynomial without roots on a
segment has constant sign there) this is the analytic input of Hörmander's proof of the
Tarski–Seidenberg theorem: the sign diagram of a family of polynomials is determined by the sign
diagram of the family obtained by replacing a polynomial of maximal degree by its derivative and
its remainders. Nothing here is in Mathlib.
-/

open Set Filter

namespace Polynomial

/-- `y` and `y'` lie in the same gap of the finite set `Z`: no point of `Z` separates them. -/
def SameGap (Z : Finset ℝ) (y y' : ℝ) : Prop := ∀ z ∈ Z, z < y ↔ z < y'

namespace SameGap

variable {Z : Finset ℝ} {y y' y'' : ℝ}

/-- Every point lies in its own gap. -/
@[refl] lemma refl (Z : Finset ℝ) (y : ℝ) : SameGap Z y y := fun _ _ => Iff.rfl

/-- `SameGap Z` is symmetric. -/
lemma symm (h : SameGap Z y y') : SameGap Z y' y := fun z hz => (h z hz).symm

/-- `SameGap Z` is transitive. -/
lemma trans (h : SameGap Z y y') (h' : SameGap Z y' y'') : SameGap Z y y'' :=
  fun z hz => (h z hz).trans (h' z hz)

/-- Two points of the same gap of `Z`, both outside `Z`, span a segment disjoint from `Z`. -/
lemma not_mem_uIcc (h : SameGap Z y y') (hy : y ∉ Z) (hy' : y' ∉ Z) :
    ∀ z ∈ Z, z ∉ uIcc y y' := by
  intro z hz hzI
  have h1 : z ≠ y := fun e => hy (e ▸ hz)
  have h2 : z ≠ y' := fun e => hy' (e ▸ hz)
  rcases le_total y y' with hle | hle
  · rw [uIcc_of_le hle] at hzI
    exact not_lt.2 hzI.1 ((h z hz).2 (lt_of_le_of_ne hzI.2 h2))
  · rw [uIcc_of_ge hle] at hzI
    exact not_lt.2 hzI.1 ((h z hz).1 (lt_of_le_of_ne hzI.2 h1))

end SameGap

/-- A real polynomial without roots on a segment has the same sign at both ends. -/
theorem sign_eval_eq_of_forall_ne_zero (w : ℝ[X]) {a b : ℝ} (h : ∀ y ∈ uIcc a b, w.eval y ≠ 0) :
    SignType.sign (w.eval a) = SignType.sign (w.eval b) := by
  have ha := h a left_mem_uIcc
  have hb := h b right_mem_uIcc
  by_contra hne
  have h0 : (0 : ℝ) ∈ uIcc (w.eval a) (w.eval b) := by
    rcases lt_or_gt_of_ne ha with ha' | ha' <;> rcases lt_or_gt_of_ne hb with hb' | hb'
    · exact absurd (by rw [sign_neg ha', sign_neg hb']) hne
    · exact mem_uIcc.2 (Or.inl ⟨ha'.le, hb'.le⟩)
    · exact mem_uIcc.2 (Or.inr ⟨hb'.le, ha'.le⟩)
    · exact absurd (by rw [sign_pos ha', sign_pos hb']) hne
  obtain ⟨c, hc, hc0⟩ := intermediate_value_uIcc w.continuous.continuousOn h0
  exact h c hc hc0

/-- A real polynomial with positive derivative on the interior of a convex set is strictly
monotone on it. -/
theorem strictMonoOn_eval (p : ℝ[X]) {D : Set ℝ} (hD : Convex ℝ D)
    (h : ∀ t ∈ interior D, 0 < (derivative p).eval t) : StrictMonoOn (fun x => p.eval x) D :=
  strictMonoOn_of_deriv_pos hD p.continuous.continuousOn
    (fun t ht => by rw [Polynomial.deriv]; exact h t ht)

section Gap

variable {Z : Finset ℝ} {p : ℝ[X]}

/-- `y` has a *left anchor* for `p` in `Z`: if `y` has a left neighbour `a` in `Z`, then `p(a)`
has sign opposite to `p'(y)`. -/
def LeftAnchor (Z : Finset ℝ) (p : ℝ[X]) (y : ℝ) : Prop :=
  ∀ a ∈ Z, a < y → (∀ z ∈ Z, z < y → z ≤ a) →
    SignType.sign (p.eval a) = -SignType.sign ((derivative p).eval y)

/-- `y` has a *right anchor* for `p` in `Z`: if `y` has a right neighbour `b` in `Z`, then `p(b)`
has the sign of `p'(y)`. -/
def RightAnchor (Z : Finset ℝ) (p : ℝ[X]) (y : ℝ) : Prop :=
  ∀ b ∈ Z, y < b → (∀ z ∈ Z, y < z → b ≤ z) →
    SignType.sign (p.eval b) = SignType.sign ((derivative p).eval y)

private lemma pos_of_free (hZ : ∀ t, (derivative p).eval t = 0 → t ∈ Z) {y t : ℝ}
    (hy : 0 < (derivative p).eval y) (hfree : ∀ s ∈ uIcc y t, s ∉ Z) :
    0 < (derivative p).eval t := by
  have := sign_eval_eq_of_forall_ne_zero (derivative p) (a := y) (b := t)
    (fun s hs h0 => hfree s hs (hZ s h0))
  rw [sign_pos hy] at this
  exact sign_eq_one_iff.1 this.symm

private lemma derivative_ne_zero_of_pos {y : ℝ} (hy : 0 < (derivative p).eval y) :
    0 < p.degree := by
  by_contra h
  rw [eq_C_of_degree_le_zero (not_lt.1 h)] at hy
  simp at hy

private lemma lt_of_leftNbr (hZ : ∀ t, (derivative p).eval t = 0 → t ∈ Z) {y a : ℝ}
    (hyZ : y ∉ Z) (hy : 0 < (derivative p).eval y) (ha : a < y)
    (hmax : ∀ z ∈ Z, z < y → z ≤ a) : p.eval a < p.eval y := by
  refine strictMonoOn_eval p (convex_Icc a y) (fun t ht => ?_) ⟨le_rfl, ha.le⟩
    ⟨ha.le, le_rfl⟩ ha
  rw [interior_Icc] at ht
  refine pos_of_free hZ hy fun s hs hsZ => ?_
  rw [uIcc_of_ge ht.2.le] at hs
  rcases hs.2.lt_or_eq with hs' | rfl
  · exact absurd (hmax s hsZ hs') (not_le.2 (ht.1.trans_le hs.1))
  · exact hyZ hsZ

private lemma lt_of_rightNbr (hZ : ∀ t, (derivative p).eval t = 0 → t ∈ Z) {y b : ℝ}
    (hyZ : y ∉ Z) (hy : 0 < (derivative p).eval y) (hb : y < b)
    (hmin : ∀ z ∈ Z, y < z → b ≤ z) : p.eval y < p.eval b := by
  refine strictMonoOn_eval p (convex_Icc y b) (fun t ht => ?_) ⟨le_rfl, hb.le⟩
    ⟨hb.le, le_rfl⟩ hb
  rw [interior_Icc] at ht
  refine pos_of_free hZ hy fun s hs hsZ => ?_
  rw [uIcc_of_le ht.1.le] at hs
  rcases hs.1.lt_or_eq with hs' | rfl
  · exact absurd (hmin s hsZ hs') (not_le.2 (hs.2.trans_lt ht.2))
  · exact hyZ hsZ

private lemma exists_left (hZ : ∀ t, (derivative p).eval t = 0 → t ∈ Z) {y : ℝ} (hyZ : y ∉ Z)
    (hy : 0 < (derivative p).eval y) (hL : LeftAnchor Z p y) :
    ∃ α < y, p.eval α < 0 ∧ ∀ z ∈ Z, z < y → z ≤ α := by
  by_cases hex : ∃ z ∈ Z, z < y
  · have hne : (Z.filter (· < y)).Nonempty := by
      obtain ⟨z, hz, hzy⟩ := hex
      exact ⟨z, Finset.mem_filter.2 ⟨hz, hzy⟩⟩
    set a := (Z.filter (· < y)).max' hne
    have ha := Finset.mem_filter.1 ((Z.filter (· < y)).max'_mem hne)
    have hmax : ∀ z ∈ Z, z < y → z ≤ a :=
      fun z hz hzy => (Z.filter (· < y)).le_max' z (Finset.mem_filter.2 ⟨hz, hzy⟩)
    have := hL a ha.1 ha.2 hmax
    rw [sign_pos hy] at this
    exact ⟨a, ha.2, sign_eq_neg_one_iff.1 this, hmax⟩
  · push Not at hex
    have hmono : StrictMonoOn (fun x => p.eval x) (Iic y) := by
      refine strictMonoOn_eval p (convex_Iic y) (fun t ht => ?_)
      rw [interior_Iic] at ht
      refine pos_of_free hZ hy fun s hs hsZ => ?_
      rw [uIcc_of_ge ht.le] at hs
      exact hyZ (le_antisymm hs.2 (hex s hsZ) ▸ hsZ)
    have hev := (abs_tendsto_atBot (P := p) (derivative_ne_zero_of_pos hy)).eventually
      (eventually_gt_atTop |p.eval y|)
    obtain ⟨t, ht1, ht2⟩ := (hev.and (eventually_lt_atBot y)).exists
    refine ⟨t, ht2, ?_, fun z hz hzy => absurd (hex z hz) (not_le.2 hzy)⟩
    have hlt := hmono (mem_Iic.2 ht2.le) (mem_Iic.2 le_rfl) ht2
    by_contra hnn
    rw [abs_of_nonneg (not_lt.1 hnn)] at ht1
    exact absurd (ht1.trans hlt) (not_lt.2 (le_abs_self _))

private lemma exists_right (hZ : ∀ t, (derivative p).eval t = 0 → t ∈ Z) {y : ℝ} (hyZ : y ∉ Z)
    (hy : 0 < (derivative p).eval y) (hR : RightAnchor Z p y) :
    ∃ β > y, 0 < p.eval β ∧ ∀ z ∈ Z, y < z → β ≤ z := by
  by_cases hex : ∃ z ∈ Z, y < z
  · have hne : (Z.filter (y < ·)).Nonempty := by
      obtain ⟨z, hz, hzy⟩ := hex
      exact ⟨z, Finset.mem_filter.2 ⟨hz, hzy⟩⟩
    set b := (Z.filter (y < ·)).min' hne
    have hb := Finset.mem_filter.1 ((Z.filter (y < ·)).min'_mem hne)
    have hmin : ∀ z ∈ Z, y < z → b ≤ z :=
      fun z hz hzy => (Z.filter (y < ·)).min'_le z (Finset.mem_filter.2 ⟨hz, hzy⟩)
    have := hR b hb.1 hb.2 hmin
    rw [sign_pos hy] at this
    exact ⟨b, hb.2, sign_eq_one_iff.1 this, hmin⟩
  · push Not at hex
    have hmono : StrictMonoOn (fun x => p.eval x) (Ici y) := by
      refine strictMonoOn_eval p (convex_Ici y) (fun t ht => ?_)
      rw [interior_Ici] at ht
      refine pos_of_free hZ hy fun s hs hsZ => ?_
      rw [uIcc_of_le ht.le] at hs
      exact hyZ (le_antisymm (hex s hsZ) hs.1 ▸ hsZ)
    have hev := (abs_tendsto_atTop (P := p) (derivative_ne_zero_of_pos hy)).eventually
      (eventually_gt_atTop |p.eval y|)
    obtain ⟨t, ht1, ht2⟩ := (hev.and (eventually_gt_atTop y)).exists
    refine ⟨t, ht2, ?_, fun z hz hzy => absurd (hex z hz) (not_le.2 hzy)⟩
    have hlt := hmono (mem_Ici.2 le_rfl) (mem_Ici.2 ht2.le) ht2
    by_contra hnn
    have h0 : 0 ≤ -p.eval t := by linarith [not_lt.1 hnn]
    rw [abs_of_nonpos (not_lt.1 hnn)] at ht1
    linarith [neg_abs_le (p.eval y)]

private lemma exists_root_of_anchor_pos (hZ : ∀ t, (derivative p).eval t = 0 → t ∈ Z) {y : ℝ}
    (hyZ : y ∉ Z) (hy : 0 < (derivative p).eval y) (hL : LeftAnchor Z p y)
    (hR : RightAnchor Z p y) :
    ∃ r, r ∉ Z ∧ p.eval r = 0 ∧ SameGap Z y r ∧
      ∀ y', y' ∉ Z → SameGap Z y y' → SignType.sign (p.eval y') = SignType.sign (y' - r) := by
  obtain ⟨α, hαy, hpα, hα⟩ := exists_left hZ hyZ hy hL
  obtain ⟨β, hβy, hpβ, hβ⟩ := exists_right hZ hyZ hy hR
  have hfree : ∀ z ∈ Z, z ∉ Ioo α β := by
    intro z hz hzI
    rcases lt_trichotomy z y with h | rfl | h
    · exact absurd (hα z hz h) (not_le.2 hzI.1)
    · exact hyZ hz
    · exact absurd (hβ z hz h) (not_le.2 hzI.2)
  have hposI : ∀ t ∈ Ioo α β, 0 < (derivative p).eval t := by
    intro t ht
    refine pos_of_free hZ hy fun s hs hsZ => hfree s hsZ ?_
    exact (ordConnected_Ioo.uIcc_subset ⟨hαy, hβy⟩ ht) hs
  have hmono : StrictMonoOn (fun x => p.eval x) (Icc α β) :=
    strictMonoOn_eval p (convex_Icc α β) (fun t ht => hposI t (by rwa [interior_Icc] at ht))
  have h0 : (0 : ℝ) ∈ Icc (p.eval α) (p.eval β) := ⟨hpα.le, hpβ.le⟩
  obtain ⟨r, hr, hr0⟩ := intermediate_value_Icc (hαy.trans hβy).le
    p.continuous.continuousOn h0
  have hrα : r ≠ α := by rintro rfl; simp [hr0] at hpα
  have hrβ : r ≠ β := by rintro rfl; simp [hr0] at hpβ
  have hrI : r ∈ Ioo α β := ⟨lt_of_le_of_ne hr.1 hrα.symm, lt_of_le_of_ne hr.2 hrβ⟩
  have hrZ : r ∉ Z := fun h => hfree r h hrI
  have hgap : SameGap Z y r := by
    intro z hz
    constructor
    · intro h
      exact (hα z hz h).trans_lt hrI.1
    · intro h
      by_contra h'
      rcases (not_lt.1 h').lt_or_eq with h'' | rfl
      · exact absurd (hβ z hz h'') (not_le.2 (h.trans hrI.2))
      · exact hyZ hz
  refine ⟨r, hrZ, hr0, hgap, fun y' hy'Z hy' => ?_⟩
  have hgap' : SameGap Z r y' := hgap.symm.trans hy'
  have hfree' := hgap'.not_mem_uIcc hrZ hy'Z
  have hmono' : StrictMonoOn (fun x => p.eval x) (uIcc r y') := by
    refine strictMonoOn_eval p (convex_uIcc r y') (fun t ht => ?_)
    refine pos_of_free hZ (hposI r hrI) fun s hs hsZ => hfree' s hsZ ?_
    exact (ordConnected_uIcc.uIcc_subset left_mem_uIcc (interior_subset ht)) hs
  rcases lt_trichotomy y' r with h | rfl | h
  · have := hmono' right_mem_uIcc left_mem_uIcc h
    simp only [hr0] at this
    rw [sign_neg this, sign_neg (sub_neg.2 h)]
  · simp [hr0]
  · have := hmono' left_mem_uIcc right_mem_uIcc h
    simp only [hr0] at this
    rw [sign_pos this, sign_pos (sub_pos.2 h)]

private lemma hZ_neg (hZ : ∀ t, (derivative p).eval t = 0 → t ∈ Z) :
    ∀ t, (derivative (-p)).eval t = 0 → t ∈ Z :=
  fun t ht => hZ t (by simpa using ht)

private lemma leftAnchor_neg {y : ℝ} : LeftAnchor Z (-p) y ↔ LeftAnchor Z p y := by
  simp [LeftAnchor, Left.sign_neg, neg_eq_iff_eq_neg]

private lemma rightAnchor_neg {y : ℝ} : RightAnchor Z (-p) y ↔ RightAnchor Z p y := by
  simp [RightAnchor, Left.sign_neg]

/-- If `y ∉ Z` has a left neighbour `a` in `Z` at which `p` does not have the sign opposite to
`p'(y)`, then `p(y)` has the sign of `p'(y)`. -/
theorem sign_eval_of_not_leftAnchor (hZ : ∀ t, (derivative p).eval t = 0 → t ∈ Z) {y : ℝ}
    (hyZ : y ∉ Z) (hL : ¬ LeftAnchor Z p y) :
    SignType.sign (p.eval y) = SignType.sign ((derivative p).eval y) := by
  have hne : (derivative p).eval y ≠ 0 := fun h => hyZ (hZ y h)
  unfold LeftAnchor at hL
  push Not at hL
  obtain ⟨a, ha, hay, hmax, hsa⟩ := hL
  rcases hne.lt_or_gt with hneg | hpos
  · have hpos' : 0 < (derivative (-p)).eval y := by simpa using hneg
    have hlt := lt_of_leftNbr (hZ_neg hZ) hyZ hpos' hay hmax
    rw [sign_neg hneg] at hsa ⊢
    have hpa : p.eval a ≤ 0 := by
      by_contra h
      exact hsa (by rw [sign_pos (not_le.1 h)]; rfl)
    simp only [eval_neg] at hlt
    exact sign_neg (by linarith)
  · have hlt := lt_of_leftNbr hZ hyZ hpos hay hmax
    rw [sign_pos hpos] at hsa ⊢
    have hpa : 0 ≤ p.eval a := by
      by_contra h
      exact hsa (sign_neg (not_le.1 h))
    exact sign_pos (by linarith)

/-- If `y ∉ Z` has a right neighbour `b` in `Z` at which `p` does not have the sign of `p'(y)`,
then `p(y)` has the sign opposite to `p'(y)`. -/
theorem sign_eval_of_not_rightAnchor (hZ : ∀ t, (derivative p).eval t = 0 → t ∈ Z) {y : ℝ}
    (hyZ : y ∉ Z) (hR : ¬ RightAnchor Z p y) :
    SignType.sign (p.eval y) = -SignType.sign ((derivative p).eval y) := by
  have hne : (derivative p).eval y ≠ 0 := fun h => hyZ (hZ y h)
  unfold RightAnchor at hR
  push Not at hR
  obtain ⟨b, hb, hyb, hmin, hsb⟩ := hR
  rcases hne.lt_or_gt with hneg | hpos
  · have hpos' : 0 < (derivative (-p)).eval y := by simpa using hneg
    have hlt := lt_of_rightNbr (hZ_neg hZ) hyZ hpos' hyb hmin
    rw [sign_neg hneg] at hsb ⊢
    have hpb : 0 ≤ p.eval b := by
      by_contra h
      exact hsb (sign_neg (not_le.1 h))
    simp only [eval_neg] at hlt
    rw [sign_pos (by linarith)]
    rfl
  · have hlt := lt_of_rightNbr hZ hyZ hpos hyb hmin
    rw [sign_pos hpos] at hsb ⊢
    have hpb : p.eval b ≤ 0 := by
      by_contra h
      exact hsb (sign_pos (not_le.1 h))
    rw [sign_neg (by linarith)]

/-- If `y ∉ Z` is anchored on both sides, then `p` has a root `r` in the gap of `y`, and on that
gap `p` has the sign of `p'(y) * (y' - r)`. -/
theorem exists_root_of_anchor (hZ : ∀ t, (derivative p).eval t = 0 → t ∈ Z) {y : ℝ}
    (hyZ : y ∉ Z) (hL : LeftAnchor Z p y) (hR : RightAnchor Z p y) :
    ∃ r, r ∉ Z ∧ p.eval r = 0 ∧ SameGap Z y r ∧
      ∀ y', y' ∉ Z → SameGap Z y y' → SignType.sign (p.eval y') =
        SignType.sign ((derivative p).eval y) * SignType.sign (y' - r) := by
  have hne : (derivative p).eval y ≠ 0 := fun h => hyZ (hZ y h)
  rcases hne.lt_or_gt with hneg | hpos
  · have hpos' : 0 < (derivative (-p)).eval y := by simpa using hneg
    obtain ⟨r, hrZ, hr0, hgap, hsign⟩ := exists_root_of_anchor_pos (hZ_neg hZ) hyZ hpos'
      (leftAnchor_neg.2 hL) (rightAnchor_neg.2 hR)
    refine ⟨r, hrZ, by simpa using hr0, hgap, fun y' hy'Z hy' => ?_⟩
    have := hsign y' hy'Z hy'
    rw [eval_neg, Left.sign_neg] at this
    rw [sign_neg hneg, ← this]
    simp
  · obtain ⟨r, hrZ, hr0, hgap, hsign⟩ := exists_root_of_anchor_pos hZ hyZ hpos hL hR
    refine ⟨r, hrZ, hr0, hgap, fun y' hy'Z hy' => ?_⟩
    rw [hsign y' hy'Z hy', sign_pos hpos, one_mul]

/-- A root of `p` outside `Z` is anchored on both sides. -/
theorem anchor_of_root (hZ : ∀ t, (derivative p).eval t = 0 → t ∈ Z) {r : ℝ} (hrZ : r ∉ Z)
    (hr0 : p.eval r = 0) : LeftAnchor Z p r ∧ RightAnchor Z p r := by
  have hpr' : (derivative p).eval r ≠ 0 := fun h => hrZ (hZ r h)
  refine ⟨?_, ?_⟩
  · by_contra hL
    have := sign_eval_of_not_leftAnchor hZ hrZ hL
    rw [hr0, sign_zero, eq_comm, sign_eq_zero_iff] at this
    exact hpr' this
  · by_contra hR
    have := sign_eval_of_not_rightAnchor hZ hrZ hR
    rw [hr0, sign_zero, eq_comm] at this
    exact hpr' (by simpa using this)

/-- Each gap of `Z` contains at most one root of `p`. -/
theorem eq_of_sameGap_of_root (hZ : ∀ t, (derivative p).eval t = 0 → t ∈ Z) {r r' : ℝ}
    (hrZ : r ∉ Z) (hr'Z : r' ∉ Z) (hr0 : p.eval r = 0) (hr'0 : p.eval r' = 0)
    (hgap : SameGap Z r r') : r = r' := by
  have hpr' : (derivative p).eval r ≠ 0 := fun h => hrZ (hZ r h)
  obtain ⟨hL, hR⟩ := anchor_of_root hZ hrZ hr0
  obtain ⟨s, -, -, -, hsign⟩ := exists_root_of_anchor hZ hrZ hL hR
  have h1 := hsign r hrZ (SameGap.refl Z r)
  have h2 := hsign r' hr'Z hgap
  rw [hr0, sign_zero, eq_comm, mul_eq_zero, sign_eq_zero_iff, sign_eq_zero_iff] at h1
  rw [hr'0, sign_zero, eq_comm, mul_eq_zero, sign_eq_zero_iff, sign_eq_zero_iff] at h2
  rcases h1 with h1 | h1
  · exact absurd h1 hpr'
  rcases h2 with h2 | h2
  · exact absurd h2 hpr'
  linarith

end Gap

end Polynomial
