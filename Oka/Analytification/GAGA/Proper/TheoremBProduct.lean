/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.GAGA.TheoremBBox

/-!
# Theorem B for the structure sheaf on products of boxes, punctured planes and planes

Let `ι` be finite, split into box coordinates `S`, punctured coordinates `P` (disjoint from
`S`) and full coordinates. The *mixed domain* `Complex.mixedSet S P a b ⊆ ℂ^ι` is the product
of the open rectangles `(a_i.re, b_i.re) × (a_i.im, b_i.im)` for `i ∈ S`, of `ℂ^×` for `i ∈ P`
and of `ℂ` for the other coordinates. We show `Hᵠ(D, 𝒪) = 0` for `q ≥ 1`, by
`Complex.TheoremB.eq_zero_of_exhaustion`: `D` is exhausted by products of holed rectangles
(shrunk boxes in `S`, the exhaustion of `Complex.exhaustion` elsewhere), and one-variable Runge
approximation in each coordinate gives `lim¹ 𝒪 = 0`.

## Main definitions

- `Complex.mixedSet S P a b`: the domain `∏_{i ∈ S} (box) × (ℂ^×)^P × ℂ^{ι \ (S ∪ P)}`.
- `Complex.mixedExhaustion S P a b n`: its exhaustion by products of holed rectangles.

## Main results

- `Complex.exists_approx_boxExhaustion_coord`, `Complex.exists_approx_exhaustion_coord`: Runge
  approximation with holomorphic parameters in a single coordinate of the exhaustions of
  boxes, resp. of `(ℂ^×)^P × ℂ^{ι \ P}`.
- `Complex.iUnion_prod_mixedExhaustion`, `Complex.exists_approx_mixedExhaustion`.
- `Complex.TheoremB.H'_structureSheafAb_eq_zero_of_mixedSet`,
  `Complex.TheoremB.subsingleton_H_restrictOpen_structureSheafAb_mixedSet`: **Theorem B** on
  mixed domains.
-/

universe u

open CategoryTheory TopologicalSpace Opposite Set Filter
open scoped Topology

namespace Complex

open HoledRect

variable {ι : Type*}

section Coord

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- Runge approximation in one coordinate of the box exhaustion: functions holomorphic on the
`(n + 1)`-st shrunk rectangle (with holomorphic parameters) are uniform limits on the closure of
the `n`-th one of functions holomorphic on `ℂ` (with the same parameters). -/
theorem exists_approx_boxExhaustion_coord (a b : ι → ℂ) (n : ℕ) (j : ι) {Q : Set E}
    (hQ : IsOpen Q) {f : ℂ × E → ℂ}
    (hf : DifferentiableOn ℂ f ((boxExhaustion a b (n + 1) j).set ×ˢ Q)) {L : Set E}
    (hL : IsCompact L) (hLQ : L ⊆ Q) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℂ × E → ℂ, DifferentiableOn ℂ g (univ ×ˢ Q) ∧
      ∀ z ∈ closure (boxExhaustion a b n j).set, ∀ w ∈ L, ‖f (z, w) - g (z, w)‖ ≤ ε := by
  rcases (closure (boxExhaustion a b n j).set).eq_empty_or_nonempty with hK0 | ⟨z₀, hz₀⟩
  · exact ⟨0, differentiableOn_const 0, fun z hz ↦ by simp [hK0] at hz⟩
  obtain ⟨m, hm1, hm2⟩ := exists_between (one_div_succ_lt_one_div n)
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := mem_closure_boxExhaustion_set hz₀
  have hre : (a j).re + m < (b j).re - m := by linarith
  have him : (a j).im + m < (b j).im - m := by linarith
  refine exists_approx_entire_of_rect (a := ⟨(a j).re + m, (a j).im + m⟩)
    (b := ⟨(b j).re - m, (b j).im - m⟩) hre him ?_ hQ hf (isCompact_closure_set _) ?_ hL hLQ hε
  · rintro z ⟨⟨e1, e2⟩, e3, e4⟩
    exact mem_boxExhaustion_set_iff.2 ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  · intro z hz
    obtain ⟨⟨e1, e2⟩, e3, e4⟩ := mem_closure_boxExhaustion_set hz
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

variable [DecidableEq ι]

/-- Runge approximation in one coordinate of the exhaustion of `(ℂ^×)^P × ℂ^{ι \ P}`: functions
holomorphic on the `j`-th factor of the `(n + 1)`-st member (with holomorphic parameters) are
uniform limits on the closure of the `j`-th factor of the `n`-th member of functions holomorphic
on `ℂ^×` (if `j ∈ P`), resp. on `ℂ` (with the same parameters). -/
theorem exists_approx_exhaustion_coord (P : Finset ι) (n : ℕ) (j : ι) {Q : Set E}
    (hQ : IsOpen Q) {f : ℂ × E → ℂ}
    (hf : DifferentiableOn ℂ f ((exhaustion P (n + 1) j).set ×ˢ Q)) {L : Set E}
    (hL : IsCompact L) (hLQ : L ⊆ Q) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℂ × E → ℂ, DifferentiableOn ℂ g ((if j ∈ P then {0}ᶜ else univ) ×ˢ Q) ∧
      ∀ z ∈ closure (exhaustion P n j).set, ∀ w ∈ L, ‖f (z, w) - g (z, w)‖ ≤ ε := by
  have hr : ∀ m : ℕ, (0 : ℝ) < (1 / 4) ^ (m + 1) := fun m ↦ by positivity
  have hr' : ((1 : ℝ) / 4) ^ (n + 1) = 4 * (1 / 4) ^ (n + 1 + 1) := by ring
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = n + 3 / 2 := ⟨_, rfl⟩
  have hn0 : (0 : ℝ) ≤ n := n.cast_nonneg
  by_cases hj : j ∈ P
  · rw [if_pos hj]
    set ρ : ℝ := 2 * (1 / 4) ^ (n + 1 + 1)
    have hρ : 0 < ρ := by positivity
    have hρ1 : ρ < 1 := by
      have : ((1 : ℝ) / 4) ^ (n + 1 + 1) ≤ 1 / 4 := pow_le_of_le_one (by norm_num)
        (by norm_num) (by omega) |>.trans (by norm_num)
      linarith
    have hR : 1 < R := by linarith
    refine exists_approx_punctured_of_frame (X₀ := -R) (X₁ := R) (Y₀ := -R) (Y₁ := R)
      hρ (by linarith) (by linarith) (by linarith) (by linarith) ?_ hQ hf
      ((exhaustion P n j).isCompact_closure_set) ?_ ?_ hL hLQ hε
    · rintro z ⟨⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩, h5⟩
      refine mem_set_iff'.2 ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
      all_goals simp only [exhaustion, hj, if_true]
      · push_cast; linarith
      · push_cast; linarith
      · push_cast; linarith
      · push_cast; linarith
      by_contra hle
      push Not at hle
      refine h5 ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
        linarith [abs_le.1 ((le_max_left _ _).trans hle), abs_le.1 ((le_max_right _ _).trans hle)]
    · intro z hz
      obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5⟩ := mem_closure_set hz
      simp only [exhaustion, hj, if_true] at h1 h2 h3 h4 h5
      refine ⟨⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩, fun h ↦ ?_⟩
      have : max |z.re| |z.im| ≤ ρ := max_le (abs_le.2 ⟨h.1.1, h.1.2⟩) (abs_le.2 ⟨h.2.1, h.2.2⟩)
      rw [hr'] at h5
      linarith [hr (n + 1)]
    · intro z hz
      obtain ⟨-, -, h5⟩ := mem_closure_set hz
      simp only [exhaustion, hj, if_true] at h5
      rw [hr'] at h5
      refine le_trans ?_ (max_le (Complex.abs_re_le_norm z) (Complex.abs_im_le_norm z))
      linarith [hr (n + 1)]
  · rw [if_neg hj]
    refine exists_approx_entire_of_rect (a := ⟨-R, -R⟩) (b := ⟨R, R⟩) (by simp; linarith)
      (by simp; linarith) ?_ hQ hf ((exhaustion P n j).isCompact_closure_set) ?_ hL hLQ hε
    · rintro z ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
      refine mem_set_iff'.2 ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
      all_goals simp only [exhaustion, hj, if_false]
      · push_cast; linarith
      · push_cast; linarith
      · push_cast; linarith
      · push_cast; linarith
      · linarith [(abs_nonneg z.re).trans (le_max_left |z.re| |z.im|)]
    · intro z hz
      obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩, -⟩ := mem_closure_set hz
      simp only [exhaustion] at h1 h2 h3 h4
      exact ⟨⟨by simp; linarith, by simp; linarith⟩, ⟨by simp; linarith, by simp; linarith⟩⟩

end Coord

/-! ### Eventual membership in the exhaustions -/

lemma eventually_mem_boxExhaustion_set {a b : ι → ℂ} {i : ι} {z : ℂ}
    (hz : z ∈ Ioo (a i).re (b i).re ×ℂ Ioo (a i).im (b i).im) :
    ∀ᶠ n : ℕ in atTop, z ∈ (boxExhaustion a b n i).set := by
  have hev : ∀ c : ℝ, 0 < c → ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) < c := fun c hc ↦
    tendsto_one_div_add_atTop_nhds_zero_nat.eventually (gt_mem_nhds hc)
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hz
  filter_upwards [hev _ (sub_pos.2 h1), hev _ (sub_pos.2 h2), hev _ (sub_pos.2 h3),
    hev _ (sub_pos.2 h4)] with n e1 e2 e3 e4
  exact mem_boxExhaustion_set_iff.2 ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

lemma mem_rect_of_mem_boxExhaustion_set {a b : ι → ℂ} {n : ℕ} {i : ι} {z : ℂ}
    (hz : z ∈ (boxExhaustion a b n i).set) :
    z ∈ Ioo (a i).re (b i).re ×ℂ Ioo (a i).im (b i).im := by
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := mem_boxExhaustion_set_iff.1 hz
  have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

variable [DecidableEq ι]

lemma eventually_mem_exhaustion_set {P : Finset ι} {i : ι} {z : ℂ} (hz : i ∈ P → z ≠ 0) :
    ∀ᶠ n : ℕ in atTop, z ∈ (exhaustion P n i).set := by
  have hev1 : ∀ᶠ n : ℕ in atTop, ‖z‖ < n + 1 := by
    obtain ⟨N, hN⟩ := exists_nat_gt ‖z‖
    filter_upwards [eventually_ge_atTop N] with n hn
    have : (N : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hev2 : ∀ᶠ n : ℕ in atTop, i ∈ P → (1 / 4 : ℝ) ^ (n + 1) < max |z.re| |z.im| := by
    by_cases hi : i ∈ P
    · have hpos : 0 < max |z.re| |z.im| := by
        by_contra h
        push Not at h
        have h1 : |z.re| = 0 := le_antisymm ((le_max_left _ _).trans h) (abs_nonneg _)
        have h2 : |z.im| = 0 := le_antisymm ((le_max_right _ _).trans h) (abs_nonneg _)
        exact hz hi (Complex.ext (abs_eq_zero.1 h1) (abs_eq_zero.1 h2))
      obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hpos (show (1 / 4 : ℝ) < 1 by norm_num)
      filter_upwards [eventually_ge_atTop N] with n hn _
      exact lt_of_le_of_lt (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)) hN
    · exact .of_forall fun _ h ↦ absurd h hi
  filter_upwards [hev1, hev2] with n hn1 hn2
  have h1 := abs_lt.1 (lt_of_le_of_lt (Complex.abs_re_le_norm z) hn1)
  have h2 := abs_lt.1 (lt_of_le_of_lt (Complex.abs_im_le_norm z) hn1)
  refine mem_set_iff'.2 ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  all_goals simp only [exhaustion]
  · linarith [h1.1]
  · linarith [h1.2]
  · linarith [h2.1]
  · linarith [h2.2]
  split_ifs with hi
  · exact hn2 hi
  · exact lt_of_lt_of_le (by norm_num) (le_max_of_le_left (abs_nonneg _))

lemma ne_zero_of_mem_exhaustion_set {P : Finset ι} {n : ℕ} {i : ι} (hi : i ∈ P) {z : ℂ}
    (hz : z ∈ (exhaustion P n i).set) : z ≠ 0 := by
  rintro rfl
  have := (mem_set_iff'.1 hz).2.2
  simp only [exhaustion, hi, if_true, zero_re, zero_im, abs_zero, max_self] at this
  have : (0 : ℝ) < (1 / 4) ^ (n + 1) := by positivity
  linarith

/-! ### Mixed domains -/

omit [DecidableEq ι] in
/-- The mixed domain: the product of the open rectangles `(a_i.re, b_i.re) × (a_i.im, b_i.im)`
for `i ∈ S`, of `ℂ^×` for `i ∈ P` and of `ℂ` for the other coordinates. -/
def mixedSet (S P : Set ι) (a b : ι → ℂ) : Set (ι → ℂ) :=
  {x | ∀ i, (i ∈ S → x i ∈ Ioo (a i).re (b i).re ×ℂ Ioo (a i).im (b i).im) ∧ (i ∈ P → x i ≠ 0)}

omit [DecidableEq ι] in
lemma mixedSet_empty_left (P : Set ι) (a b : ι → ℂ) : mixedSet ∅ P a b = puncturedSet P := by
  ext x
  simp [mixedSet, puncturedSet]

omit [DecidableEq ι] in
lemma mixedSet_univ_empty (a b : ι → ℂ) : mixedSet univ ∅ a b = openBox a b := by
  ext x
  simp [mixedSet, openBox]

/-- The exhaustion of the mixed domain: shrunk rectangles in the coordinates in `S`, and the
members of `Complex.exhaustion P` in the others. -/
noncomputable def mixedExhaustion (S P : Finset ι) (a b : ι → ℂ) (n : ℕ) : ι → HoledRect :=
  fun i ↦ if i ∈ S then boxExhaustion a b n i else exhaustion P n i

lemma closure_mixedExhaustion_set_subset (S P : Finset ι) (a b : ι → ℂ) (n : ℕ) (i : ι) :
    closure (mixedExhaustion S P a b n i).set ⊆ (mixedExhaustion S P a b (n + 1) i).set := by
  simp only [mixedExhaustion]
  split_ifs
  · exact closure_boxExhaustion_set_subset a b n i
  · exact closure_exhaustion_set_subset P n i

lemma closure_prod_mixedExhaustion_subset (S P : Finset ι) (a b : ι → ℂ) (n : ℕ) :
    closure (prod (mixedExhaustion S P a b n)) ⊆ prod (mixedExhaustion S P a b (n + 1)) := by
  rw [closure_prod]
  exact pi_mono fun i _ ↦ closure_mixedExhaustion_set_subset S P a b n i

lemma prod_mixedExhaustion_subset (S P : Finset ι) (a b : ι → ℂ) (n : ℕ) :
    prod (mixedExhaustion S P a b n) ⊆ prod (mixedExhaustion S P a b (n + 1)) :=
  subset_closure.trans (closure_prod_mixedExhaustion_subset S P a b n)

lemma prod_mixedExhaustion_subset_mixedSet {S P : Finset ι} (hSP : Disjoint S P) (a b : ι → ℂ)
    (n : ℕ) : prod (mixedExhaustion S P a b n) ⊆ mixedSet (S : Set ι) (P : Set ι) a b := by
  intro x hx i
  have hxi := mem_prod_iff.1 hx i
  refine ⟨fun hi ↦ ?_, fun hi ↦ ?_⟩
  · simp only [mixedExhaustion, Finset.mem_coe.1 hi, if_true] at hxi
    exact mem_rect_of_mem_boxExhaustion_set hxi
  · have hiS : i ∉ S := Finset.disjoint_right.1 hSP hi
    simp only [mixedExhaustion, hiS, if_false] at hxi
    exact ne_zero_of_mem_exhaustion_set hi hxi

lemma iUnion_prod_mixedExhaustion [Finite ι] {S P : Finset ι} (hSP : Disjoint S P)
    (a b : ι → ℂ) :
    ⋃ n, prod (mixedExhaustion S P a b n) = mixedSet (S : Set ι) (P : Set ι) a b := by
  refine subset_antisymm (iUnion_subset (prod_mixedExhaustion_subset_mixedSet hSP a b))
    fun x hx ↦ ?_
  have h : ∀ᶠ n : ℕ in atTop, ∀ i, x i ∈ (mixedExhaustion S P a b n i).set := by
    rw [Filter.eventually_all]
    intro i
    simp only [mixedExhaustion]
    by_cases hi : i ∈ S
    · simp only [hi, if_true]
      exact eventually_mem_boxExhaustion_set ((hx i).1 hi)
    · simp only [hi, if_false]
      exact eventually_mem_exhaustion_set (hx i).2
  obtain ⟨n, hn⟩ := h.exists
  exact mem_iUnion.2 ⟨n, mem_prod_iff.2 hn⟩

/-- The target of the coordinatewise approximation on the mixed domain: `ℂ^×` for `j ∈ P \ S`,
`ℂ` otherwise. -/
def mixedTarget (S P : Finset ι) (j : ι) : Set ℂ :=
  if j ∈ S then univ else if j ∈ P then {0}ᶜ else univ

lemma isOpen_mixedTarget (S P : Finset ι) (j : ι) : IsOpen (mixedTarget S P j) := by
  unfold mixedTarget
  split_ifs
  exacts [isOpen_univ, isOpen_compl_singleton, isOpen_univ]

lemma mixedExhaustion_set_subset_mixedTarget (S P : Finset ι) (a b : ι → ℂ) (n : ℕ) (j : ι) :
    (mixedExhaustion S P a b n j).set ⊆ mixedTarget S P j := by
  intro z hz
  unfold mixedTarget
  by_cases hS : j ∈ S
  · rw [if_pos hS]; exact mem_univ _
  · rw [if_neg hS]
    by_cases hP : j ∈ P
    · rw [if_pos hP]
      have e : mixedExhaustion S P a b n j = exhaustion P n j := if_neg hS
      rw [e] at hz
      exact ne_zero_of_mem_exhaustion_set hP hz
    · rw [if_neg hP]; exact mem_univ _

lemma mixedSet_subset_pi_mixedTarget (S P : Finset ι) (a b : ι → ℂ) :
    mixedSet (S : Set ι) (P : Set ι) a b ⊆ univ.pi (mixedTarget S P) := by
  intro x hx j _
  unfold mixedTarget
  by_cases hS : j ∈ S
  · rw [if_pos hS]; exact mem_univ _
  · rw [if_neg hS]
    by_cases hP : j ∈ P
    · rw [if_pos hP]; exact (hx j).2 hP
    · rw [if_neg hP]; exact mem_univ _

/-- Runge approximation with holomorphic parameters in one coordinate of the exhaustion of the
mixed domain. -/
theorem exists_approx_mixedExhaustion_coord {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] (S P : Finset ι) (a b : ι → ℂ) (n : ℕ) (j : ι) {Q : Set E}
    (hQ : IsOpen Q) {f : ℂ × E → ℂ}
    (hf : DifferentiableOn ℂ f ((mixedExhaustion S P a b (n + 1) j).set ×ˢ Q)) {L : Set E}
    (hL : IsCompact L) (hLQ : L ⊆ Q) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℂ × E → ℂ, DifferentiableOn ℂ g (mixedTarget S P j ×ˢ Q) ∧
      ∀ z ∈ closure (mixedExhaustion S P a b n j).set, ∀ w ∈ L,
        ‖f (z, w) - g (z, w)‖ ≤ ε := by
  by_cases hj : j ∈ S
  · have e1 : mixedExhaustion S P a b (n + 1) j = boxExhaustion a b (n + 1) j := if_pos hj
    have e2 : mixedExhaustion S P a b n j = boxExhaustion a b n j := if_pos hj
    have e3 : mixedTarget S P j = univ := if_pos hj
    rw [e1] at hf
    rw [e2, e3]
    exact exists_approx_boxExhaustion_coord a b n j hQ hf hL hLQ hε
  · have e1 : mixedExhaustion S P a b (n + 1) j = exhaustion P (n + 1) j := if_neg hj
    have e2 : mixedExhaustion S P a b n j = exhaustion P n j := if_neg hj
    have e3 : mixedTarget S P j = if j ∈ P then {0}ᶜ else univ := if_neg hj
    rw [e1] at hf
    rw [e2, e3]
    exact exists_approx_exhaustion_coord P n j hQ hf hL hLQ hε

/-- Functions holomorphic on the `(n + 1)`-st member of the exhaustion of the mixed domain are
uniform limits on the `n`-th member of functions holomorphic on the mixed domain. -/
theorem exists_approx_mixedExhaustion [Finite ι] (S P : Finset ι) (a b : ι → ℂ) (n : ℕ)
    {g : (ι → ℂ) → ℂ} (hg : DifferentiableOn ℂ g (prod (mixedExhaustion S P a b (n + 1))))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ G : (ι → ℂ) → ℂ, DifferentiableOn ℂ G (mixedSet (S : Set ι) (P : Set ι) a b) ∧
      ∀ x ∈ prod (mixedExhaustion S P a b n), ‖g x - G x‖ ≤ ε := by
  cases nonempty_fintype ι
  have hrunge : ∀ j (Q : Set ({k // k ≠ j} → ℂ)), IsOpen Q → ∀ f : ℂ × ({k // k ≠ j} → ℂ) → ℂ,
      DifferentiableOn ℂ f ((mixedExhaustion S P a b (n + 1) j).set ×ˢ Q) → ∀ L, IsCompact L →
      L ⊆ Q → ∀ ε' > 0, ∃ g : ℂ × ({k // k ≠ j} → ℂ) → ℂ,
        DifferentiableOn ℂ g (mixedTarget S P j ×ˢ Q) ∧
        ∀ z ∈ closure (mixedExhaustion S P a b n j).set, ∀ w ∈ L,
          ‖f (z, w) - g (z, w)‖ ≤ ε' :=
    fun j _ hQ _ hf _ hL hLQ _ hε' ↦
      exists_approx_mixedExhaustion_coord S P a b n j hQ hf hL hLQ hε'
  obtain ⟨G, hG, hGe⟩ := exists_approx_pi (fun j ↦ (mixedExhaustion S P a b (n + 1) j).set)
    (mixedTarget S P) (fun j ↦ closure (mixedExhaustion S P a b n j).set)
    (fun j ↦ (mixedExhaustion S P a b (n + 1) j).isOpen_set) (isOpen_mixedTarget S P)
    (mixedExhaustion_set_subset_mixedTarget S P a b (n + 1))
    (fun j ↦ (mixedExhaustion S P a b n j).isCompact_closure_set)
    (fun j ↦ closure_mixedExhaustion_set_subset S P a b n j) hrunge hg hε
  exact ⟨G, hG.mono (mixedSet_subset_pi_mixedTarget S P a b), fun x hx ↦ hGe x fun j _ ↦
    subset_closure (mem_prod_iff.1 hx j)⟩

namespace TheoremB

variable {ι : Type u} [Fintype ι]

set_option hygiene false in
/-- The space `ℂ^ι` as an object of `TopCat`. -/
local notation "𝕏" => TopCat.of (ι → ℂ)

/-- The members of the exhaustion of the mixed domain, as opens. -/
noncomputable def mixedExhaustionOpens [DecidableEq ι] (S P : Finset ι) (a b : ι → ℂ) (n : ℕ) :
    Opens 𝕏 :=
  ⟨prod (mixedExhaustion S P a b n), isOpen_prod _⟩

/-- **Theorem B on mixed domains**, for Mathlib's cohomology of opens: every class of positive
degree of the structure sheaf on `D = ∏_{i ∈ S} (box) × (ℂ^×)^P × ℂ^{ι \ (S ∪ P)}` vanishes. -/
theorem H'_structureSheafAb_eq_zero_of_mixedSet {S P : Set ι} (hSP : Disjoint S P)
    (a b : ι → ℂ) {D : Opens 𝕏} (hD : (D : Set (ι → ℂ)) = mixedSet S P a b) {q : ℕ}
    (c : CategoryTheory.Sheaf.H'.{u} (complexSpaceStructureSheafAb ι) (q + 1) D) : c = 0 := by
  classical
  set S' := (Set.toFinite S).toFinset
  set P' := (Set.toFinite P).toFinset
  have hS' : (S' : Set ι) = S := Set.Finite.coe_toFinset _
  have hP' : (P' : Set ι) = P := Set.Finite.coe_toFinset _
  have hSP' : Disjoint S' P' := by
    rw [← Finset.disjoint_coe, hS', hP']
    exact hSP
  have hU : Monotone (mixedExhaustionOpens S' P' a b) :=
    monotone_nat_of_le_succ fun n ↦ prod_mixedExhaustion_subset S' P' a b n
  have hUnion : ⋃ j, (mixedExhaustionOpens S' P' a b j : Set (ι → ℂ)) = mixedSet S P a b := by
    rw [← hS', ← hP']
    exact iUnion_prod_mixedExhaustion hSP' a b
  refine eq_zero_of_exhaustion cousinSplitting_structureSheafAb (mixedExhaustion S' P' a b) hU
    (fun _ ↦ rfl) (closure_prod_mixedExhaustion_subset S' P' a b)
    (limOneVanishesOn_structureSheafAb hU fun k g hg ε hε ↦ ?_)
    (Opens.ext ((Opens.coe_iSup _).trans (hUnion.trans hD.symm))) c
  obtain ⟨G, hG, hGe⟩ := exists_approx_mixedExhaustion S' P' a b k hg hε
  refine ⟨G, ?_, hGe⟩
  rw [hUnion, ← hS', ← hP']
  exact hG

/-- **Theorem B on mixed domains**: `Hᵠ(D, 𝒪|_D) = 0` for `q ≥ 1` and
`D = ∏_{i ∈ S} (box) × (ℂ^×)^P × ℂ^{ι \ (S ∪ P)}`, `S ∩ P = ∅`. -/
theorem subsingleton_H_restrictOpen_structureSheafAb_mixedSet {S P : Set ι} (hSP : Disjoint S P)
    (a b : ι → ℂ) {D : Opens 𝕏} (hD : (D : Set (ι → ℂ)) = mixedSet S P a b) {q : ℕ}
    (hq : 0 < q) :
    Subsingleton (TopCat.Sheaf.H
      ((TopCat.Sheaf.restrictOpen D).obj (complexSpaceStructureSheafAb ι)) q) := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_lt hq
  rw [zero_add]
  have : Subsingleton (CategoryTheory.Sheaf.H'.{u} (complexSpaceStructureSheafAb ι) (q + 1) D) :=
    subsingleton_of_forall_eq 0 (H'_structureSheafAb_eq_zero_of_mixedSet hSP a b hD)
  exact (TopCat.Sheaf.H'AddEquiv D _ (q + 1)).symm.toEquiv.subsingleton

end TheoremB

end Complex
