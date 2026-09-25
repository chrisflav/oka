/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.GAGA.CartanBundle

/-!
# Induction over closed boxes

Let `Q` be a property of subsets of `ℂ^ι` which passes to subsets, holds for all sets near every
point of a closed box `K`, and is stable under merging adjacent closed boxes: if `K₁` and `K₂` are
obtained from a closed box by moving its left and right real edge (or its lower and upper
imaginary edge) in one coordinate outwards, then `Q K₁` and `Q K₂` imply `Q (K₁ ∪ K₂)`. Then
`Q K` holds. This is the shape of the proofs of Cartan's Theorems A and B for closed boxes; the
subdivision argument is `Complex.HoledRect.mem_of_merge`.

## Main results

- `Complex.closedBox_induction`: the induction principle.
-/

open Set Topology

namespace Complex

variable {ι : Type*} [Finite ι] [DecidableEq ι]

/-- The merge hypothesis of `Complex.closedBox_induction` for cuts in the real direction. -/
def BoxMergeRe (Q : Set (ι → ℂ) → Prop) : Prop :=
  ∀ (i : ι) (a b : ι → ℂ), (∀ j, (a j).re ≤ (b j).re ∧ (a j).im ≤ (b j).im) →
    ∀ x₀ x₁ : ℝ, x₀ ≤ (a i).re → (b i).re ≤ x₁ →
    Q (closedBox (Function.update a i ⟨x₀, (a i).im⟩) b) →
    Q (closedBox a (Function.update b i ⟨x₁, (b i).im⟩)) →
    Q (closedBox (Function.update a i ⟨x₀, (a i).im⟩) b ∪
      closedBox a (Function.update b i ⟨x₁, (b i).im⟩))

/-- The merge hypothesis of `Complex.closedBox_induction` for cuts in the imaginary
direction. -/
def BoxMergeIm (Q : Set (ι → ℂ) → Prop) : Prop :=
  ∀ (i : ι) (a b : ι → ℂ), (∀ j, (a j).re ≤ (b j).re ∧ (a j).im ≤ (b j).im) →
    ∀ y₀ y₁ : ℝ, y₀ ≤ (a i).im → (b i).im ≤ y₁ →
    Q (closedBox (Function.update a i ⟨(a i).re, y₀⟩) b) →
    Q (closedBox a (Function.update b i ⟨(b i).re, y₁⟩)) →
    Q (closedBox (Function.update a i ⟨(a i).re, y₀⟩) b ∪
      closedBox a (Function.update b i ⟨(b i).re, y₁⟩))

/-- The family of sets all of whose closed boxes satisfy `Q`. -/
private def boxFamily (Q : Set (ι → ℂ) → Prop) : Set (Set (ι → ℂ)) :=
  {W | ∀ a b, closedBox a b ⊆ W → Q (closedBox a b)}

omit [Finite ι] in
private lemma mem_prod_update_withX₁ {s : ι → HoledRect} {i : ι} {x : ι → ℂ} {c : ℝ}
    (hx : x ∈ HoledRect.prod s) (hxi : (x i).re < c) :
    x ∈ HoledRect.prod (Function.update s i ((s i).withX₁ c)) := by
  refine HoledRect.mem_prod_iff.2 fun j ↦ ?_
  have := HoledRect.mem_prod_iff.1 hx j
  by_cases hj : j = i
  · subst hj
    rw [Function.update_self]
    rw [HoledRect.mem_set_iff'] at this ⊢
    exact ⟨⟨this.1.1, hxi⟩, this.2⟩
  · rwa [Function.update_of_ne hj]

omit [Finite ι] in
private lemma mem_prod_update_withX₀ {s : ι → HoledRect} {i : ι} {x : ι → ℂ} {c : ℝ}
    (hx : x ∈ HoledRect.prod s) (hxi : c < (x i).re) :
    x ∈ HoledRect.prod (Function.update s i ((s i).withX₀ c)) := by
  refine HoledRect.mem_prod_iff.2 fun j ↦ ?_
  have := HoledRect.mem_prod_iff.1 hx j
  by_cases hj : j = i
  · subst hj
    rw [Function.update_self]
    rw [HoledRect.mem_set_iff'] at this ⊢
    exact ⟨⟨hxi, this.1.2⟩, this.2⟩
  · rwa [Function.update_of_ne hj]

omit [Finite ι] in
private lemma mem_prod_update_withY₁ {s : ι → HoledRect} {i : ι} {x : ι → ℂ} {c : ℝ}
    (hx : x ∈ HoledRect.prod s) (hxi : (x i).im < c) :
    x ∈ HoledRect.prod (Function.update s i ((s i).withY₁ c)) := by
  refine HoledRect.mem_prod_iff.2 fun j ↦ ?_
  have := HoledRect.mem_prod_iff.1 hx j
  by_cases hj : j = i
  · subst hj
    rw [Function.update_self]
    rw [HoledRect.mem_set_iff'] at this ⊢
    exact ⟨this.1, ⟨this.2.1.1, hxi⟩, this.2.2⟩
  · rwa [Function.update_of_ne hj]

omit [Finite ι] in
private lemma mem_prod_update_withY₀ {s : ι → HoledRect} {i : ι} {x : ι → ℂ} {c : ℝ}
    (hx : x ∈ HoledRect.prod s) (hxi : c < (x i).im) :
    x ∈ HoledRect.prod (Function.update s i ((s i).withY₀ c)) := by
  refine HoledRect.mem_prod_iff.2 fun j ↦ ?_
  have := HoledRect.mem_prod_iff.1 hx j
  by_cases hj : j = i
  · subst hj
    rw [Function.update_self]
    rw [HoledRect.mem_set_iff'] at this ⊢
    exact ⟨this.1, ⟨hxi, this.2.1.2⟩, this.2.2⟩
  · rwa [Function.update_of_ne hj]

omit [Finite ι] in
private lemma mergeRe_boxFamily {Q : Set (ι → ℂ) → Prop} (hmono : ∀ K K', K' ⊆ K → Q K → Q K')
    (hempty : Q ∅) (hre : BoxMergeRe Q) : HoledRect.MergeRe (boxFamily Q) := by
  intro s i t δ hδ _ _ _ hA hB a b hK
  by_cases hord : ∀ j, (a j).re ≤ (b j).re ∧ (a j).im ≤ (b j).im
  swap
  · rw [closedBox_eq_empty_of_not_le hord]
    exact hempty
  rcases lt_or_ge (b i).re (t + δ) with hb | hb
  · exact hA a b fun x hx ↦ mem_prod_update_withX₁ (hK hx)
      ((hx i (mem_univ _)).1.2.trans_lt hb)
  rcases lt_or_ge (t - δ) (a i).re with ha | ha
  · exact hB a b fun x hx ↦ mem_prod_update_withX₀ (hK hx)
      (ha.trans_le (hx i (mem_univ _)).1.1)
  obtain ⟨a', ha'i, ha'j⟩ : ∃ a' : ι → ℂ,
      a' i = ⟨t - δ / 2, (a i).im⟩ ∧ ∀ j, j ≠ i → a' j = a j :=
    ⟨Function.update a i _, Function.update_self _ _ _, fun j hj ↦ Function.update_of_ne hj _ _⟩
  obtain ⟨b', hb'i, hb'j⟩ : ∃ b' : ι → ℂ,
      b' i = ⟨t + δ / 2, (b i).im⟩ ∧ ∀ j, j ≠ i → b' j = b j :=
    ⟨Function.update b i _, Function.update_self _ _ _, fun j hj ↦ Function.update_of_ne hj _ _⟩
  set K₁ := closedBox (Function.update a' i ⟨(a i).re, (a' i).im⟩) b'
  set K₂ := closedBox a' (Function.update b' i ⟨(b i).re, (b' i).im⟩)
  have hK₁K : K₁ ⊆ closedBox a b := by
    intro x hx j _
    have := hx j (mem_univ _)
    by_cases hj : j = i
    · rw [hj] at this ⊢
      simp only [Function.update_self, ha'i, hb'i, mem_reProdIm, mem_Icc] at this ⊢
      obtain ⟨⟨h1, h2⟩, h3, h4⟩ := this
      exact ⟨⟨h1, by linarith⟩, h3, h4⟩
    · simpa [Function.update_of_ne hj, ha'j j hj, hb'j j hj] using this
  have hK₂K : K₂ ⊆ closedBox a b := by
    intro x hx j _
    have := hx j (mem_univ _)
    by_cases hj : j = i
    · rw [hj] at this ⊢
      simp only [Function.update_self, ha'i, hb'i, mem_reProdIm, mem_Icc] at this ⊢
      obtain ⟨⟨h1, h2⟩, h3, h4⟩ := this
      exact ⟨⟨by linarith, h2⟩, h3, h4⟩
    · simpa [Function.update_of_ne hj, ha'j j hj, hb'j j hj] using this
  have hQ₁ : Q K₁ := hA _ _ fun x hx ↦ by
    refine mem_prod_update_withX₁ (hK (hK₁K hx)) ?_
    have := (hx i (mem_univ _)).1.2
    rw [hb'i] at this
    change (x i).re ≤ t + δ / 2 at this
    linarith
  have hQ₂ : Q K₂ := hB _ _ fun x hx ↦ by
    refine mem_prod_update_withX₀ (hK (hK₂K hx)) ?_
    have := (hx i (mem_univ _)).1.1
    rw [ha'i] at this
    change t - δ / 2 ≤ (x i).re at this
    linarith
  have hord' : ∀ j, (a' j).re ≤ (b' j).re ∧ (a' j).im ≤ (b' j).im := fun j ↦ by
    by_cases hj : j = i
    · rw [hj, ha'i, hb'i]
      exact ⟨show t - δ / 2 ≤ t + δ / 2 by linarith, (hord i).2⟩
    · rw [ha'j j hj, hb'j j hj]
      exact hord j
  have hQ := hre i a' b' hord' (a i).re (b i).re
    (by rw [ha'i]; change (a i).re ≤ t - δ / 2; linarith)
    (by rw [hb'i]; change t + δ / 2 ≤ (b i).re; linarith) hQ₁ hQ₂
  refine hmono _ _ (fun x hx ↦ ?_) hQ
  rcases le_or_gt (x i).re (t + δ / 2) with hxi | hxi
  · refine Or.inl fun j _ ↦ ?_
    have := hx j (mem_univ _)
    by_cases hj : j = i
    · rw [hj] at this ⊢
      simp only [Function.update_self, ha'i, hb'i, mem_reProdIm, mem_Icc] at this ⊢
      exact ⟨⟨this.1.1, hxi⟩, this.2⟩
    · simpa [Function.update_of_ne hj, ha'j j hj, hb'j j hj] using this
  · refine Or.inr fun j _ ↦ ?_
    have := hx j (mem_univ _)
    by_cases hj : j = i
    · rw [hj] at this ⊢
      simp only [Function.update_self, ha'i, hb'i, mem_reProdIm, mem_Icc] at this ⊢
      exact ⟨⟨by linarith, this.1.2⟩, this.2⟩
    · simpa [Function.update_of_ne hj, ha'j j hj, hb'j j hj] using this

omit [Finite ι] in
private lemma mergeIm_boxFamily {Q : Set (ι → ℂ) → Prop} (hmono : ∀ K K', K' ⊆ K → Q K → Q K')
    (hempty : Q ∅) (him : BoxMergeIm Q) : HoledRect.MergeIm (boxFamily Q) := by
  intro s i t δ hδ _ _ _ hA hB a b hK
  by_cases hord : ∀ j, (a j).re ≤ (b j).re ∧ (a j).im ≤ (b j).im
  swap
  · rw [closedBox_eq_empty_of_not_le hord]
    exact hempty
  rcases lt_or_ge (b i).im (t + δ) with hb | hb
  · exact hA a b fun x hx ↦ mem_prod_update_withY₁ (hK hx)
      ((hx i (mem_univ _)).2.2.trans_lt hb)
  rcases lt_or_ge (t - δ) (a i).im with ha | ha
  · exact hB a b fun x hx ↦ mem_prod_update_withY₀ (hK hx)
      (ha.trans_le (hx i (mem_univ _)).2.1)
  obtain ⟨a', ha'i, ha'j⟩ : ∃ a' : ι → ℂ,
      a' i = ⟨(a i).re, t - δ / 2⟩ ∧ ∀ j, j ≠ i → a' j = a j :=
    ⟨Function.update a i _, Function.update_self _ _ _, fun j hj ↦ Function.update_of_ne hj _ _⟩
  obtain ⟨b', hb'i, hb'j⟩ : ∃ b' : ι → ℂ,
      b' i = ⟨(b i).re, t + δ / 2⟩ ∧ ∀ j, j ≠ i → b' j = b j :=
    ⟨Function.update b i _, Function.update_self _ _ _, fun j hj ↦ Function.update_of_ne hj _ _⟩
  set K₁ := closedBox (Function.update a' i ⟨(a' i).re, (a i).im⟩) b'
  set K₂ := closedBox a' (Function.update b' i ⟨(b' i).re, (b i).im⟩)
  have hK₁K : K₁ ⊆ closedBox a b := by
    intro x hx j _
    have := hx j (mem_univ _)
    by_cases hj : j = i
    · rw [hj] at this ⊢
      simp only [Function.update_self, ha'i, hb'i, mem_reProdIm, mem_Icc] at this ⊢
      obtain ⟨⟨h1, h2⟩, h3, h4⟩ := this
      exact ⟨⟨h1, h2⟩, h3, by linarith⟩
    · simpa [Function.update_of_ne hj, ha'j j hj, hb'j j hj] using this
  have hK₂K : K₂ ⊆ closedBox a b := by
    intro x hx j _
    have := hx j (mem_univ _)
    by_cases hj : j = i
    · rw [hj] at this ⊢
      simp only [Function.update_self, ha'i, hb'i, mem_reProdIm, mem_Icc] at this ⊢
      obtain ⟨⟨h1, h2⟩, h3, h4⟩ := this
      exact ⟨⟨h1, h2⟩, by linarith, h4⟩
    · simpa [Function.update_of_ne hj, ha'j j hj, hb'j j hj] using this
  have hQ₁ : Q K₁ := hA _ _ fun x hx ↦ by
    refine mem_prod_update_withY₁ (hK (hK₁K hx)) ?_
    have := (hx i (mem_univ _)).2.2
    rw [hb'i] at this
    change (x i).im ≤ t + δ / 2 at this
    linarith
  have hQ₂ : Q K₂ := hB _ _ fun x hx ↦ by
    refine mem_prod_update_withY₀ (hK (hK₂K hx)) ?_
    have := (hx i (mem_univ _)).2.1
    rw [ha'i] at this
    change t - δ / 2 ≤ (x i).im at this
    linarith
  have hord' : ∀ j, (a' j).re ≤ (b' j).re ∧ (a' j).im ≤ (b' j).im := fun j ↦ by
    by_cases hj : j = i
    · rw [hj, ha'i, hb'i]
      exact ⟨(hord i).1, show t - δ / 2 ≤ t + δ / 2 by linarith⟩
    · rw [ha'j j hj, hb'j j hj]
      exact hord j
  have hQ := him i a' b' hord' (a i).im (b i).im
    (by rw [ha'i]; change (a i).im ≤ t - δ / 2; linarith)
    (by rw [hb'i]; change t + δ / 2 ≤ (b i).im; linarith) hQ₁ hQ₂
  refine hmono _ _ (fun x hx ↦ ?_) hQ
  rcases le_or_gt (x i).im (t + δ / 2) with hxi | hxi
  · refine Or.inl fun j _ ↦ ?_
    have := hx j (mem_univ _)
    by_cases hj : j = i
    · rw [hj] at this ⊢
      simp only [Function.update_self, ha'i, hb'i, mem_reProdIm, mem_Icc] at this ⊢
      exact ⟨this.1, this.2.1, hxi⟩
    · simpa [Function.update_of_ne hj, ha'j j hj, hb'j j hj] using this
  · refine Or.inr fun j _ ↦ ?_
    have := hx j (mem_univ _)
    by_cases hj : j = i
    · rw [hj] at this ⊢
      simp only [Function.update_self, ha'i, hb'i, mem_reProdIm, mem_Icc] at this ⊢
      exact ⟨this.1, by linarith, this.2.2⟩
    · simpa [Function.update_of_ne hj, ha'j j hj, hb'j j hj] using this

/-- **Induction over closed boxes.** Let `Q` be a property of subsets of `ℂ^ι` which passes to
subsets, holds for `∅`, holds for every set inside some neighbourhood of each point of the closed
box `K = closedBox a b`, and is stable under merging adjacent closed boxes in the real and in the
imaginary directions. Then `Q K`. -/
theorem closedBox_induction (Q : Set (ι → ℂ) → Prop) (hmono : ∀ K K', K' ⊆ K → Q K → Q K')
    (hempty : Q ∅) (hre : BoxMergeRe Q) (him : BoxMergeIm Q) {a b : ι → ℂ}
    (hloc : ∀ x ∈ closedBox a b, ∃ U ∈ 𝓝 x, ∀ K ⊆ U, Q K) : Q (closedBox a b) := by
  cases nonempty_fintype ι
  by_cases hord : ∀ j, (a j).re ≤ (b j).re ∧ (a j).im ≤ (b j).im
  swap
  · rw [closedBox_eq_empty_of_not_le hord]
    exact hempty
  set O : Set (ι → ℂ) := {x | ∃ U ∈ 𝓝 x, ∀ K ⊆ U, Q K} with hOdef
  have hO : IsOpen O := by
    refine isOpen_iff_mem_nhds.2 fun x ⟨U, hU, hQU⟩ ↦ ?_
    filter_upwards [eventually_mem_nhds_iff.2 hU] with y hy using ⟨U, hy, hQU⟩
  obtain ⟨δ, hδ, hδO⟩ := (isCompact_closedBox a b).exists_thickening_subset_open hO hloc
  set s₀ : ι → HoledRect := fun j ↦
    ⟨(a j).re - δ / 4, (b j).re + δ / 4, (a j).im - δ / 4, (b j).im + δ / 4, -1⟩ with hs₀
  have hloc' : ∀ x ∈ closure (HoledRect.prod s₀), ∃ W ∈ boxFamily Q, W ∈ 𝓝 x := by
    intro x hx
    rw [HoledRect.closure_prod] at hx
    have hxj : ∀ j, x j ∈ closedRectNhd (a j) (b j) (δ / 4) := fun j ↦
      closure_minimal (HoledRect.set_subset_rect (s₀ j)) isCompact_closedRectNhd.isClosed
        (hx j (mem_univ _))
    have hxO : x ∈ O := by
      refine hδO (Metric.mem_thickening_iff.2 ?_)
      choose y hy hdist using fun j ↦ Metric.mem_thickening_iff.1
        (closedRectNhd_subset_thickening (s := δ / 4) (δ := δ) (hord j).1 (hord j).2
          (by positivity) (by linarith) (hxj j))
      refine ⟨y, fun j _ ↦ ?_, (dist_pi_lt_iff hδ).2 hdist⟩
      simpa [closedRectNhd] using hy j
    obtain ⟨U, hU, hQU⟩ := hxO
    exact ⟨U, fun a b h ↦ hQU _ h, hU⟩
  have hmem := HoledRect.mem_of_merge (boxFamily Q) (fun a b h ↦ by rwa [subset_empty_iff.1 h])
    (fun W hW W' hW' a b h ↦ hW a b (h.trans hW')) (mergeRe_boxFamily hmono hempty hre)
    (mergeIm_boxFamily hmono hempty him) s₀ hloc'
  refine hmem a b fun x hx ↦ HoledRect.mem_prod_iff.2 fun j ↦ ?_
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hx j (mem_univ _)
  refine HoledRect.mem_set_iff'.2 ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · change (a j).re - δ / 4 < (x j).re; linarith
  · change (x j).re < (b j).re + δ / 4; linarith
  · change (a j).im - δ / 4 < (x j).im; linarith
  · change (x j).im < (b j).im + δ / 4; linarith
  · exact lt_of_lt_of_le (by norm_num) (le_max_of_le_left (abs_nonneg _))

section Update

omit [Finite ι]

omit [DecidableEq ι] in
lemma closedBox_nonempty {a b : ι → ℂ} (h : ∀ j, (a j).re ≤ (b j).re ∧ (a j).im ≤ (b j).im) :
    (closedBox a b).Nonempty :=
  ⟨a, fun j _ ↦ ⟨⟨le_rfl, (h j).1⟩, le_rfl, (h j).2⟩⟩

/-- Two boxes adjacent in the real direction form a closed box. -/
lemma closedBox_union_re (i : ι) {a b : ι → ℂ} (hre : (a i).re ≤ (b i).re) {x₀ x₁ : ℝ}
    (hx₀ : x₀ ≤ (a i).re) (hx₁ : (b i).re ≤ x₁) :
    closedBox (Function.update a i ⟨x₀, (a i).im⟩) b ∪
        closedBox a (Function.update b i ⟨x₁, (b i).im⟩) =
      closedBox (Function.update a i ⟨x₀, (a i).im⟩) (Function.update b i ⟨x₁, (b i).im⟩) := by
  ext x
  constructor
  · rintro (hx | hx) j _ <;> have := hx j (mem_univ _) <;> by_cases hj : j = i
    · subst hj
      simp only [Function.update_self, mem_reProdIm, mem_Icc] at this ⊢
      exact ⟨⟨this.1.1, by linarith [this.1.2]⟩, this.2⟩
    · simpa [Function.update_of_ne hj] using this
    · subst hj
      simp only [Function.update_self, mem_reProdIm, mem_Icc] at this ⊢
      exact ⟨⟨by linarith [this.1.1], this.1.2⟩, this.2⟩
    · simpa [Function.update_of_ne hj] using this
  · intro hx
    have hxi := hx i (mem_univ _)
    simp only [Function.update_self, mem_reProdIm, mem_Icc] at hxi
    rcases le_or_gt (x i).re (b i).re with h | h
    · refine Or.inl fun j _ ↦ ?_
      have := hx j (mem_univ _)
      by_cases hj : j = i
      · subst hj
        simp only [Function.update_self, mem_reProdIm, mem_Icc]
        exact ⟨⟨hxi.1.1, h⟩, hxi.2⟩
      · simpa [Function.update_of_ne hj] using this
    · refine Or.inr fun j _ ↦ ?_
      have := hx j (mem_univ _)
      by_cases hj : j = i
      · subst hj
        simp only [Function.update_self, mem_reProdIm, mem_Icc]
        exact ⟨⟨by linarith, hxi.1.2⟩, hxi.2⟩
      · simpa [Function.update_of_ne hj] using this

/-- Two boxes adjacent in the imaginary direction form a closed box. -/
lemma closedBox_union_im (i : ι) {a b : ι → ℂ} (him : (a i).im ≤ (b i).im) {y₀ y₁ : ℝ}
    (hy₀ : y₀ ≤ (a i).im) (hy₁ : (b i).im ≤ y₁) :
    closedBox (Function.update a i ⟨(a i).re, y₀⟩) b ∪
        closedBox a (Function.update b i ⟨(b i).re, y₁⟩) =
      closedBox (Function.update a i ⟨(a i).re, y₀⟩) (Function.update b i ⟨(b i).re, y₁⟩) := by
  ext x
  constructor
  · rintro (hx | hx) j _ <;> have := hx j (mem_univ _) <;> by_cases hj : j = i
    · subst hj
      simp only [Function.update_self, mem_reProdIm, mem_Icc] at this ⊢
      exact ⟨this.1, this.2.1, by linarith [this.2.2]⟩
    · simpa [Function.update_of_ne hj] using this
    · subst hj
      simp only [Function.update_self, mem_reProdIm, mem_Icc] at this ⊢
      exact ⟨this.1, by linarith [this.2.1], this.2.2⟩
    · simpa [Function.update_of_ne hj] using this
  · intro hx
    have hxi := hx i (mem_univ _)
    simp only [Function.update_self, mem_reProdIm, mem_Icc] at hxi
    rcases le_or_gt (x i).im (b i).im with h | h
    · refine Or.inl fun j _ ↦ ?_
      have := hx j (mem_univ _)
      by_cases hj : j = i
      · subst hj
        simp only [Function.update_self, mem_reProdIm, mem_Icc]
        exact ⟨hxi.1, hxi.2.1, h⟩
      · simpa [Function.update_of_ne hj] using this
    · refine Or.inr fun j _ ↦ ?_
      have := hx j (mem_univ _)
      by_cases hj : j = i
      · subst hj
        simp only [Function.update_self, mem_reProdIm, mem_Icc]
        exact ⟨hxi.1, by linarith, hxi.2.2⟩
      · simpa [Function.update_of_ne hj] using this

lemma closedBox_subset_update_left_im (i : ι) {a b : ι → ℂ} {y₀ : ℝ} (hy₀ : y₀ ≤ (a i).im) :
    closedBox a b ⊆ closedBox (Function.update a i ⟨(a i).re, y₀⟩) b := by
  intro x hx j _
  by_cases hj : j = i
  · subst hj
    obtain ⟨h1, h2, h3⟩ := hx j (mem_univ _)
    simp only [Function.update_self]
    exact ⟨h1, hy₀.trans h2, h3⟩
  · simpa [Function.update_of_ne hj] using hx j (mem_univ _)

lemma closedBox_subset_update_right_im (i : ι) {a b : ι → ℂ} {y₁ : ℝ} (hy₁ : (b i).im ≤ y₁) :
    closedBox a b ⊆ closedBox a (Function.update b i ⟨(b i).re, y₁⟩) := by
  intro x hx j _
  by_cases hj : j = i
  · subst hj
    obtain ⟨h1, h2, h3⟩ := hx j (mem_univ _)
    simp only [Function.update_self]
    exact ⟨h1, h2, h3.trans hy₁⟩
  · simpa [Function.update_of_ne hj] using hx j (mem_univ _)

lemma closedBox_update_inter_subset_im (i : ι) {a b : ι → ℂ} (y₀ y₁ : ℝ) :
    closedBox (Function.update a i ⟨(a i).re, y₀⟩) b ∩
      closedBox a (Function.update b i ⟨(b i).re, y₁⟩) ⊆ closedBox a b := by
  rintro x ⟨h₁, h₂⟩ j _
  by_cases hj : j = i
  · subst hj
    obtain ⟨e1, -, e3⟩ := h₁ j (mem_univ _)
    obtain ⟨-, e2, -⟩ := h₂ j (mem_univ _)
    simp only [Function.update_self] at e1 e2 e3 ⊢
    exact ⟨e1, e2, e3⟩
  · simpa [Function.update_of_ne hj] using h₁ j (mem_univ _)

end Update

end Complex
