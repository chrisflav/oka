/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Geometry.RealAlgebraic.Semialgebraic.OneVariable
import Oka.Topology.Order.LocalMonotone

/-!
# The monotonicity theorem for semialgebraic functions of one variable

A semialgebraic function `h : ℝ → ℝ` is, to the right of every point `a`, continuous and monotone
(increasing or decreasing) on some interval `(a, b)`:
`IsSemialgebraicFun.exists_continuousOn_monotoneOn`.

The proof is van den Dries' (*Tame topology and o-minimal structures*, Ch. 3, Thm. 1.2), and uses
only that semialgebraic subsets of `ℝ` are finite unions of points and intervals
(`IsSemialgebraic₁.exists_Ioo_subset_of_infinite`, `IsSemialgebraic₁.eventually_nhdsGT`) and that
sets defined by first-order formulas are semialgebraic (Tarski–Seidenberg):

* `exists_Ioo_const_or_injOn`: on a subinterval of any interval, `h` is constant or injective;
* `exists_Ioo_strictMonoOn_of_injOn`: an injective `h` is strictly monotone on a subinterval;
* `exists_Ioo_continuousOn_monotoneOn`: on a subinterval of any interval, `h` is continuous and
  monotone;
* the set of points near which `h` is continuous and monotone is semialgebraic and meets every
  interval, hence contains an interval `(a, b)` to the right of every point.

None of this is in Mathlib.
-/

open Set Filter Topology

namespace IsSemialgebraicFun

variable {h : ℝ → ℝ} {a b : ℝ}

/-- The negative of a semialgebraic function is semialgebraic. -/
theorem neg (hh : IsSemialgebraicFun h) : IsSemialgebraicFun (fun t => -h t) := by
  have : IsSemialgebraic {w : Fin 2 → ℝ | ∃ v, h (w 0) = v ∧ -v = w 1} := by
    semialg using hh.setOf_graph
  exact this.congr (by ext w; simp)

/-- The image of an open interval by a semialgebraic function is semialgebraic. -/
theorem isSemialgebraic₁_image (hh : IsSemialgebraicFun h) (a b : ℝ) :
    IsSemialgebraic₁ (h '' Ioo a b) := by
  have : IsSemialgebraic {x : Unit → ℝ | ∃ t, (a < t ∧ t < b) ∧ h t = x ()} := by
    semialg using hh.setOf_graph
  exact this.congr (by ext x; simp [and_assoc])

/-- The set of points of `(a, b)` where `h` takes a given value is semialgebraic. -/
theorem isSemialgebraic₁_fiber (hh : IsSemialgebraicFun h) (a b y : ℝ) :
    IsSemialgebraic₁ {t | t ∈ Ioo a b ∧ h t = y} := by
  have : IsSemialgebraic {x : Unit → ℝ | (a < x () ∧ x () < b) ∧ ∃ v, h (x ()) = v ∧ v = y} := by
    semialg using hh.setOf_graph
  exact this.congr (by ext x; simp)

/-- **Constant or injective.** On some open subinterval of a given interval, a semialgebraic
function is constant or injective. -/
theorem exists_Ioo_const_or_injOn (hh : IsSemialgebraicFun h) (hab : a < b) :
    ∃ a' b', a' < b' ∧ Ioo a' b' ⊆ Ioo a b ∧
      ((∃ y, ∀ t ∈ Ioo a' b', h t = y) ∨ InjOn h (Ioo a' b')) := by
  by_cases hfib : ∃ y, {t | t ∈ Ioo a b ∧ h t = y}.Infinite
  · obtain ⟨y, hy⟩ := hfib
    obtain ⟨a', b', hab', hsub⟩ :=
      (hh.isSemialgebraic₁_fiber a b y).exists_Ioo_subset_of_infinite hy
    exact ⟨a', b', hab', fun t ht => (hsub ht).1, Or.inl ⟨y, fun t ht => (hsub ht).2⟩⟩
  simp only [not_exists, Set.not_infinite] at hfib
  -- the image is infinite
  have himg : (h '' Ioo a b).Infinite := by
    intro hfin
    refine Ioo_infinite hab ((hfin.biUnion fun y _ => hfib y).subset fun t ht => ?_)
    exact mem_biUnion (mem_image_of_mem h ht) ⟨ht, rfl⟩
  obtain ⟨c, d, hcd, hsubcd⟩ := (hh.isSemialgebraic₁_image a b).exists_Ioo_subset_of_infinite himg
  -- the smallest point of each fibre
  have hmin : ∀ y ∈ Ioo c d, ∃ m, (m ∈ Ioo a b ∧ h m = y) ∧
      ∀ s, s ∈ Ioo a b ∧ h s = y → m ≤ s := by
    intro y hy
    obtain ⟨t, ht, rfl⟩ := hsubcd hy
    obtain ⟨m, hm, hm'⟩ := exists_min_image _ id (hfib (h t)) ⟨t, ht, rfl⟩
    exact ⟨m, hm, hm'⟩
  choose! g hg hg' using hmin
  set T := {t | t ∈ Ioo a b ∧ h t ∈ Ioo c d ∧ ∀ s ∈ Ioo a b, s < t → h s ≠ h t} with hTdef
  have hT : IsSemialgebraic₁ T := by
    have : IsSemialgebraic {x : Unit → ℝ | (a < x () ∧ x () < b) ∧
        (∃ v, h (x ()) = v ∧ c < v ∧ v < d) ∧
        ∀ s, a < s → s < b → s < x () → ∀ u, h s = u → ∀ v, h (x ()) = v → u ≠ v} := by
      semialg using hh.setOf_graph
    refine this.congr (by ext x; simp [hTdef, and_assoc])
  have hTinf : T.Infinite := by
    refine infinite_of_injOn_mapsTo (f := g) (s := Ioo c d) (fun y hy y' hy' hyy' => ?_)
      (fun y hy => ⟨(hg y hy).1, ?_, fun s hs hsy hsy' => ?_⟩) (Ioo_infinite hcd)
    · rw [← (hg y hy).2, ← (hg y' hy').2, hyy']
    · rw [(hg y hy).2]
      exact hy
    · rw [(hg y hy).2] at hsy'
      exact absurd (hg' y hy s ⟨hs, hsy'⟩) (not_le.2 hsy)
  obtain ⟨a', b', hab', hsub⟩ := hT.exists_Ioo_subset_of_infinite hTinf
  refine ⟨a', b', hab', fun t ht => (hsub ht).1, Or.inr fun t ht t' ht' htt' => ?_⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact (hsub ht').2.2 t (hsub ht).1 hlt htt'
  · exact (hsub ht).2.2 t' (hsub ht').1 hlt htt'.symm

/-- A union of four sets, one of which is infinite and semialgebraic; this is used to find the
"type" of a semialgebraic function near the points of an interval. -/
private lemma exists_Ioo_of_cover {A₁ A₂ A₃ A₄ : Set ℝ} (hab : a < b)
    (h₁ : IsSemialgebraic₁ A₁) (h₂ : IsSemialgebraic₁ A₂) (h₃ : IsSemialgebraic₁ A₃)
    (h₄ : IsSemialgebraic₁ A₄) (hcov : Ioo a b ⊆ A₁ ∪ A₂ ∪ A₃ ∪ A₄) :
    ∃ a' b', a' < b' ∧ (Ioo a' b' ⊆ A₁ ∨ Ioo a' b' ⊆ A₂ ∨ Ioo a' b' ⊆ A₃ ∨ Ioo a' b' ⊆ A₄) := by
  by_cases f₁ : A₁.Infinite
  · obtain ⟨a', b', h, hs⟩ := h₁.exists_Ioo_subset_of_infinite f₁
    exact ⟨a', b', h, Or.inl hs⟩
  by_cases f₂ : A₂.Infinite
  · obtain ⟨a', b', h, hs⟩ := h₂.exists_Ioo_subset_of_infinite f₂
    exact ⟨a', b', h, Or.inr (Or.inl hs)⟩
  by_cases f₃ : A₃.Infinite
  · obtain ⟨a', b', h, hs⟩ := h₃.exists_Ioo_subset_of_infinite f₃
    exact ⟨a', b', h, Or.inr (Or.inr (Or.inl hs))⟩
  by_cases f₄ : A₄.Infinite
  · obtain ⟨a', b', h, hs⟩ := h₄.exists_Ioo_subset_of_infinite f₄
    exact ⟨a', b', h, Or.inr (Or.inr (Or.inr hs))⟩
  simp only [Set.not_infinite] at f₁ f₂ f₃ f₄
  exact absurd ((((f₁.union f₂).union f₃).union f₄).subset hcov) (Ioo_infinite hab)

/-- At each point `t`, a semialgebraic `h` is, just to the right of `t`, either everywhere
`> h t` or everywhere `≤ h t`. -/
private lemma right_dichotomy (hh : IsSemialgebraicFun h) (t : ℝ) :
    (∃ u > t, ∀ s ∈ Ioo t u, h t < h s) ∨ ∃ u > t, ∀ s ∈ Ioo t u, ¬ h t < h s := by
  have hS : IsSemialgebraic₁ {s | h t < h s} := by
    have : IsSemialgebraic {x : Unit → ℝ | ∃ v, h (x ()) = v ∧ h t < v} := by
      semialg using hh.setOf_graph
    exact this.congr (by ext x; simp)
  rcases hS.eventually_nhdsGT t with h1 | h1
  · obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 h1
    exact Or.inl ⟨u, hu, fun s hs => hsub hs⟩
  · obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 h1
    exact Or.inr ⟨u, hu, fun s hs => hsub hs⟩

/-- At each point `t`, a semialgebraic `h` is, just to the left of `t`, either everywhere
`> h t` or everywhere `≤ h t`. -/
private lemma left_dichotomy (hh : IsSemialgebraicFun h) (t : ℝ) :
    (∃ u < t, ∀ s ∈ Ioo u t, h t < h s) ∨ ∃ u < t, ∀ s ∈ Ioo u t, ¬ h t < h s := by
  have hS : IsSemialgebraic₁ {s | h t < h s} := by
    have : IsSemialgebraic {x : Unit → ℝ | ∃ v, h (x ()) = v ∧ h t < v} := by
      semialg using hh.setOf_graph
    exact this.congr (by ext x; simp)
  rcases hS.eventually_nhdsLT t with h1 | h1
  · obtain ⟨u, hu, hsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1 h1
    exact Or.inl ⟨u, hu, fun s hs => hsub hs⟩
  · obtain ⟨u, hu, hsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1 h1
    exact Or.inr ⟨u, hu, fun s hs => hsub hs⟩

private lemma setOf_rel {R : ℝ → ℝ → Prop} (hR : IsSemialgebraic {w : Fin 2 → ℝ | R (w 0) (w 1)})
    {ι : Type*} {i j : ι} : IsSemialgebraic {x : ι → ℝ | R (x i) (x j)} :=
  (IsSemialgebraic.preimage_comp ![i, j] hR).congr (by ext x; simp)

/-- The set of points `t` such that `R (h s) (h t)` for all `s` just to the left of `t` is
semialgebraic. -/
private lemma isSemialgebraic₁_left (hh : IsSemialgebraicFun h) {R : ℝ → ℝ → Prop}
    (hR : IsSemialgebraic {w : Fin 2 → ℝ | R (w 0) (w 1)}) :
    IsSemialgebraic₁ {t | ∃ u < t, ∀ s ∈ Ioo u t, R (h s) (h t)} := by
  have : IsSemialgebraic {x : Unit → ℝ | ∃ u, u < x () ∧
      ∀ s, u < s → s < x () → ∀ v w, h s = v → h (x ()) = w → R v w} := by
    semialg using hh.setOf_graph, setOf_rel hR
  exact this.congr (by ext x; simp)

/-- The set of points `t` such that `R (h s) (h t)` for all `s` just to the right of `t` is
semialgebraic. -/
private lemma isSemialgebraic₁_right (hh : IsSemialgebraicFun h) {R : ℝ → ℝ → Prop}
    (hR : IsSemialgebraic {w : Fin 2 → ℝ | R (w 0) (w 1)}) :
    IsSemialgebraic₁ {t | ∃ u > t, ∀ s ∈ Ioo t u, R (h s) (h t)} := by
  have : IsSemialgebraic {x : Unit → ℝ | ∃ u, x () < u ∧
      ∀ s, x () < s → s < u → ∀ v w, h s = v → h (x ()) = w → R v w} := by
    semialg using hh.setOf_graph, setOf_rel hR
  exact this.congr (by ext x; simp)

private lemma isSemialgebraic_lt : IsSemialgebraic {w : Fin 2 → ℝ | w 0 < w 1} := by semialg

private lemma isSemialgebraic_gt : IsSemialgebraic {w : Fin 2 → ℝ | w 1 < w 0} := by semialg

/-- **Injective implies strictly monotone.** An injective semialgebraic function on an open
interval is strictly increasing or strictly decreasing on some open subinterval. -/
theorem exists_Ioo_strictMonoOn_of_injOn (hh : IsSemialgebraicFun h) (hab : a < b)
    (hinj : InjOn h (Ioo a b)) : ∃ a' b', a' < b' ∧ Ioo a' b' ⊆ Ioo a b ∧
      (StrictMonoOn h (Ioo a' b') ∨ StrictAntiOn h (Ioo a' b')) := by
  have hI : IsSemialgebraic₁ (Ioo a b) := by
    have : IsSemialgebraic {x : Unit → ℝ | a < x () ∧ x () < b} := by semialg
    exact this
  set Ll := {t | ∃ u < t, ∀ s ∈ Ioo u t, h s < h t}
  set Lg := {t | ∃ u < t, ∀ s ∈ Ioo u t, h t < h s}
  set Rl := {t | ∃ u > t, ∀ s ∈ Ioo t u, h s < h t}
  set Rg := {t | ∃ u > t, ∀ s ∈ Ioo t u, h t < h s}
  have hLl : IsSemialgebraic₁ Ll :=
    isSemialgebraic₁_left (R := fun v w => v < w) hh isSemialgebraic_lt
  have hLg : IsSemialgebraic₁ Lg :=
    isSemialgebraic₁_left (R := fun v w => w < v) hh isSemialgebraic_gt
  have hRl : IsSemialgebraic₁ Rl :=
    isSemialgebraic₁_right (R := fun v w => v < w) hh isSemialgebraic_lt
  have hRg : IsSemialgebraic₁ Rg :=
    isSemialgebraic₁_right (R := fun v w => w < v) hh isSemialgebraic_gt
  have inter3 : ∀ {A B : Set ℝ}, IsSemialgebraic₁ A → IsSemialgebraic₁ B →
      IsSemialgebraic₁ (Ioo a b ∩ A ∩ B) := fun hA hB => (hI.inter hA).inter hB
  -- every point of `(a, b)` has one of four types
  have hcov : Ioo a b ⊆ (Ioo a b ∩ Ll ∩ Rg) ∪ (Ioo a b ∩ Lg ∩ Rl) ∪ (Ioo a b ∩ Ll ∩ Rl) ∪
      (Ioo a b ∩ Lg ∩ Rg) := by
    intro t ht
    have hL : t ∈ Ll ∨ t ∈ Lg := by
      rcases left_dichotomy hh t with ⟨u, hu, h1⟩ | ⟨u, hu, h1⟩
      · exact Or.inr ⟨u, hu, h1⟩
      · refine Or.inl ⟨max u a, max_lt hu ht.1, fun s hs => ?_⟩
        have hs' : s ∈ Ioo u t := ⟨(le_max_left _ _).trans_lt hs.1, hs.2⟩
        have hsI : s ∈ Ioo a b := ⟨(le_max_right _ _).trans_lt hs.1, hs.2.trans ht.2⟩
        exact lt_of_le_of_ne (not_lt.1 (h1 s hs')) (fun e => hs.2.ne (hinj hsI ht e))
    have hR : t ∈ Rl ∨ t ∈ Rg := by
      rcases right_dichotomy hh t with ⟨u, hu, h1⟩ | ⟨u, hu, h1⟩
      · exact Or.inr ⟨u, hu, h1⟩
      · refine Or.inl ⟨min u b, lt_min hu ht.2, fun s hs => ?_⟩
        have hs' : s ∈ Ioo t u := ⟨hs.1, hs.2.trans_le (min_le_left _ _)⟩
        have hsI : s ∈ Ioo a b := ⟨ht.1.trans hs.1, hs.2.trans_le (min_le_right _ _)⟩
        exact lt_of_le_of_ne (not_lt.1 (h1 s hs')) (fun e => hs.1.ne' (hinj hsI ht e))
    rcases hL with hL | hL <;> rcases hR with hR | hR
    · exact Or.inl (Or.inr ⟨⟨ht, hL⟩, hR⟩)
    · exact Or.inl (Or.inl (Or.inl ⟨⟨ht, hL⟩, hR⟩))
    · exact Or.inl (Or.inl (Or.inr ⟨⟨ht, hL⟩, hR⟩))
    · exact Or.inr ⟨⟨ht, hL⟩, hR⟩
  obtain ⟨a', b', hab', hsub⟩ := exists_Ioo_of_cover hab (inter3 hLl hRg) (inter3 hLg hRl)
    (inter3 hLl hRl) (inter3 hLg hRg) hcov
  have hcount : ∀ {A : Set ℝ}, A.Countable → ¬ Ioo a' b' ⊆ A := fun hA hs =>
    (not_le.2 hab') (Cardinal.Real.Ioo_countable_iff.1 (hA.mono hs))
  rcases hsub with hs | hs | hs | hs
  · refine ⟨a', b', hab', fun t ht => (hs ht).1.1, Or.inl (StrictMonoOn.of_local fun t ht => ?_)⟩
    exact ⟨(hs ht).1.2, (hs ht).2⟩
  · refine ⟨a', b', hab', fun t ht => (hs ht).1.1, Or.inr ?_⟩
    have := StrictMonoOn.of_local (h := fun t => -h t) (a := a') (b := b') fun t ht => by
      obtain ⟨⟨_, u, hu, h1⟩, u', hu', h2⟩ := hs ht
      exact ⟨⟨u, hu, fun s hs => neg_lt_neg (h1 s hs)⟩, u', hu', fun s hs => neg_lt_neg (h2 s hs)⟩
    exact fun s hs t ht hst => neg_lt_neg_iff.1 (this hs ht hst)
  · exfalso
    refine hcount (Set.Countable.of_isStrictLocalMax (h := h)) fun t ht => ?_
    obtain ⟨⟨_, u, hu, h1⟩, u', hu', h2⟩ := hs ht
    exact ⟨u, hu, u', hu', fun s hs hst => (lt_or_gt_of_ne hst).elim
      (fun h3 => h1 s ⟨hs.1, h3⟩) (fun h3 => h2 s ⟨h3, hs.2⟩)⟩
  · exfalso
    refine hcount (Set.Countable.of_isStrictLocalMax (h := fun t => -h t)) fun t ht => ?_
    obtain ⟨⟨_, u, hu, h1⟩, u', hu', h2⟩ := hs ht
    exact ⟨u, hu, u', hu', fun s hs hst => (lt_or_gt_of_ne hst).elim
      (fun h3 => neg_lt_neg (h1 s ⟨hs.1, h3⟩)) (fun h3 => neg_lt_neg (h2 s ⟨h3, hs.2⟩))⟩

/-- On some open subinterval of any open interval, a semialgebraic function is continuous and
monotone (increasing or decreasing). -/
theorem exists_Ioo_continuousOn_monotoneOn (hh : IsSemialgebraicFun h) (hab : a < b) :
    ∃ a' b', a' < b' ∧ Ioo a' b' ⊆ Ioo a b ∧ ContinuousOn h (Ioo a' b') ∧
      (MonotoneOn h (Ioo a' b') ∨ AntitoneOn h (Ioo a' b')) := by
  obtain ⟨a₁, b₁, h₁, hs₁, hc⟩ := exists_Ioo_const_or_injOn hh hab
  rcases hc with ⟨y, hy⟩ | hinj
  · refine ⟨a₁, b₁, h₁, hs₁, continuousOn_const.congr fun t ht => hy t ht,
      Or.inl fun s hs t ht _ => ?_⟩
    rw [hy s hs, hy t ht]
  obtain ⟨a₂, b₂, h₂, hs₂, hm⟩ := exists_Ioo_strictMonoOn_of_injOn hh h₁ hinj
  rcases hm with hm | hm
  · obtain ⟨c, d, hcd, hsub⟩ := (hh.isSemialgebraic₁_image a₂ b₂).exists_Ioo_subset_of_infinite
      ((Ioo_infinite h₂).image hm.injOn)
    obtain ⟨a₃, b₃, h₃, hs₃, hc₃⟩ := exists_Ioo_continuousOn_of_strictMonoOn hm hcd hsub
    exact ⟨a₃, b₃, h₃, hs₃.trans (hs₂.trans hs₁), hc₃, Or.inl (hm.mono hs₃).monotoneOn⟩
  · have hm' : StrictMonoOn (fun t => -h t) (Ioo a₂ b₂) :=
      fun s hs t ht hst => neg_lt_neg (hm hs ht hst)
    obtain ⟨c, d, hcd, hsub⟩ := (hh.neg.isSemialgebraic₁_image a₂ b₂).exists_Ioo_subset_of_infinite
      ((Ioo_infinite h₂).image hm'.injOn)
    obtain ⟨a₃, b₃, h₃, hs₃, hc₃⟩ := exists_Ioo_continuousOn_of_strictMonoOn hm' hcd hsub
    refine ⟨a₃, b₃, h₃, hs₃.trans (hs₂.trans hs₁), hc₃.neg.congr fun t _ => by simp,
      Or.inr (hm.mono hs₃).antitoneOn⟩

/-- Points near which `h` is monotone form a semialgebraic set. -/
private lemma isSemialgebraic₁_localMono (hh : IsSemialgebraicFun h) :
    IsSemialgebraic₁ {t | ∃ δ > 0, MonotoneOn h (Ioo (t - δ) (t + δ))} := by
  have : IsSemialgebraic {x : Unit → ℝ | ∃ δ, 0 < δ ∧ ∀ s, x () - δ < s → s < x () + δ →
      ∀ s', x () - δ < s' → s' < x () + δ → s ≤ s' → ∀ v w, h s = v → h s' = w → v ≤ w} := by
    semialg using hh.setOf_graph
  exact this.congr (by ext x; simp [MonotoneOn])

/-- Points near which `h` is continuous and monotone or antitone form a semialgebraic set. -/
private lemma isSemialgebraic₁_good (hh : IsSemialgebraicFun h) :
    IsSemialgebraic₁ {t | ∃ δ > 0, ContinuousOn h (Ioo (t - δ) (t + δ)) ∧
      (MonotoneOn h (Ioo (t - δ) (t + δ)) ∨ AntitoneOn h (Ioo (t - δ) (t + δ)))} := by
  have : IsSemialgebraic {x : Unit → ℝ | ∃ δ, 0 < δ ∧
      (∀ s, x () - δ < s → s < x () + δ → ∀ e, 0 < e → ∃ d, 0 < d ∧
        ∀ s', x () - δ < s' → s' < x () + δ → -d < s' - s → s' - s < d →
          ∀ v w, h s' = v → h s = w → -e < v - w ∧ v - w < e) ∧
      ((∀ s, x () - δ < s → s < x () + δ → ∀ s', x () - δ < s' → s' < x () + δ → s ≤ s' →
          ∀ v w, h s = v → h s' = w → v ≤ w) ∨
        (∀ s, x () - δ < s → s < x () + δ → ∀ s', x () - δ < s' → s' < x () + δ → s ≤ s' →
          ∀ v w, h s = v → h s' = w → w ≤ v))} := by
    semialg using hh.setOf_graph
  exact this.congr (by
    ext x
    simp [Metric.continuousOn_iff, Real.dist_eq, abs_lt, MonotoneOn, AntitoneOn])

/-- **Monotonicity theorem** (at a point, from the right). A semialgebraic function `ℝ → ℝ` is
continuous and monotone or antitone on some interval `(a, b)`, for every `a`. -/
theorem exists_continuousOn_monotoneOn (hh : IsSemialgebraicFun h) (a : ℝ) :
    ∃ b > a, ContinuousOn h (Ioo a b) ∧ (MonotoneOn h (Ioo a b) ∨ AntitoneOn h (Ioo a b)) := by
  set Good := {t | ∃ δ > 0, ContinuousOn h (Ioo (t - δ) (t + δ)) ∧
      (MonotoneOn h (Ioo (t - δ) (t + δ)) ∨ AntitoneOn h (Ioo (t - δ) (t + δ)))}
  have hdense : ∀ c d, c < d → ∃ t ∈ Ioo c d, t ∈ Good := by
    intro c d hcd
    obtain ⟨a', b', hab', hsub, hcont, hmono⟩ := exists_Ioo_continuousOn_monotoneOn hh hcd
    have heq : Ioo ((a' + b') / 2 - (b' - a') / 2) ((a' + b') / 2 + (b' - a') / 2) =
        Ioo a' b' := by
      congr 1 <;> ring
    refine ⟨(a' + b') / 2, hsub ⟨by linarith, by linarith⟩, (b' - a') / 2, by linarith, ?_⟩
    rw [heq]
    exact ⟨hcont, hmono⟩
  obtain ⟨u, hu, hgood⟩ : ∃ u > a, ∀ s ∈ Ioo a u, s ∈ Good := by
    rcases (isSemialgebraic₁_good hh).eventually_nhdsGT a with h1 | h1
    · obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 h1
      exact ⟨u, hu, fun s hs => hsub hs⟩
    · obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 h1
      obtain ⟨t, ht, htG⟩ := hdense a u hu
      exact absurd htG (hsub ht)
  have hcont : ∀ v ≤ u, ContinuousOn h (Ioo a v) := by
    intro v hv t ht
    obtain ⟨δ, hδ, hc, -⟩ := hgood t ⟨ht.1, ht.2.trans_le hv⟩
    exact ((hc t ⟨by linarith, by linarith⟩).continuousAt
      (Ioo_mem_nhds (by linarith) (by linarith))).continuousWithinAt
  rcases (isSemialgebraic₁_localMono hh).eventually_nhdsGT a with h1 | h1
  · obtain ⟨u', hu', hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 h1
    refine ⟨min u u', lt_min hu hu', hcont _ (min_le_left _ _), Or.inl ?_⟩
    exact MonotoneOn.of_local (hcont _ (min_le_left _ _)) fun t ht =>
      hsub ⟨ht.1, ht.2.trans_le (min_le_right _ _)⟩
  · obtain ⟨u', hu', hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 h1
    refine ⟨min u u', lt_min hu hu', hcont _ (min_le_left _ _), Or.inr ?_⟩
    have := MonotoneOn.of_local (h := fun t => -h t) (hcont _ (min_le_left _ _)).neg
      fun t ht => by
        obtain ⟨δ, hδ, -, hm⟩ := hgood t ⟨ht.1, ht.2.trans_le (min_le_left _ _)⟩
        rcases hm with hm | hm
        · exact absurd ⟨δ, hδ, hm⟩ (hsub ⟨ht.1, ht.2.trans_le (min_le_right _ _)⟩)
        · exact ⟨δ, hδ, fun s hs t ht hst => neg_le_neg (hm hs ht hst)⟩
    exact fun s hs t ht hst => neg_le_neg_iff.1 (this hs ht hst)

end IsSemialgebraicFun
