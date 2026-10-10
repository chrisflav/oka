/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Topology.Algebra.Order.Field

/-!
# Local and global monotonicity of real functions

Elementary facts about functions `h : ℝ → ℝ` used in the proof of the monotonicity theorem for
semialgebraic functions:

* `StrictMonoOn.of_local`: if at every point `t` of an open interval, `h` is smaller than `h t`
  just to the left of `t` and larger just to the right, then `h` is strictly increasing on the
  interval (no continuity is assumed);
* `MonotoneOn.of_local`: a continuous function which is monotone near every point of an open
  interval is monotone on it;
* `Set.Countable.of_isStrictLocalMax`: the set of strict local maxima of any function `ℝ → ℝ`
  is countable;
* `exists_Ioo_continuousOn_of_strictMonoOn`: a strictly increasing function on an open interval
  whose image contains an open interval is continuous on some open subinterval.

These are standard (e.g. van den Dries, *Tame topology and o-minimal structures*, Ch. 3 §1);
Mathlib does not have them in this form.
-/

open Set Filter Topology

variable {h : ℝ → ℝ} {a b : ℝ}

/-- A function which, at every point of an open interval, is smaller to the immediate left and
larger to the immediate right, is strictly increasing on the interval. -/
theorem StrictMonoOn.of_local
    (hloc : ∀ t ∈ Ioo a b,
      (∃ u < t, ∀ s ∈ Ioo u t, h s < h t) ∧ ∃ u > t, ∀ s ∈ Ioo t u, h t < h s) :
    StrictMonoOn h (Ioo a b) := by
  intro s hs s' hs' hss'
  set T := {w | w ∈ Icc s s' ∧ ∀ u ∈ Ioc s w, h s < h u} with hTdef
  have hsT : s ∈ T := ⟨⟨le_rfl, hss'.le⟩, fun u hu => absurd hu.2 (not_le.2 hu.1)⟩
  have hbdd : BddAbove T := ⟨s', fun w hw => hw.1.2⟩
  set m := sSup T
  have hsm : s ≤ m := le_csSup hbdd hsT
  have hms' : m ≤ s' := csSup_le ⟨s, hsT⟩ fun w hw => hw.1.2
  have hmI : m ∈ Ioo a b := ⟨hs.1.trans_le hsm, hms'.trans_lt hs'.2⟩
  have claim1 : ∀ u, s < u → u < m → h s < h u := by
    intro u hsu hum
    obtain ⟨w, hwT, huw⟩ := exists_lt_of_lt_csSup ⟨s, hsT⟩ hum
    exact hwT.2 u ⟨hsu, huw.le⟩
  have claim3 : h s < h m := by
    obtain ⟨u₁, hu₁, hu₁'⟩ := (hloc m hmI).1
    have claim2 : s < m := by
      obtain ⟨u₀, hu₀, hu₀'⟩ := (hloc s hs).2
      set w := min ((s + u₀) / 2) s'
      have hsw : s < w := lt_min (by linarith) hss'
      have hwT : w ∈ T := by
        refine ⟨⟨hsw.le, min_le_right _ _⟩, fun u hu => hu₀' u ⟨hu.1, ?_⟩⟩
        exact hu.2.trans_lt ((min_le_left _ _).trans_lt (by linarith))
      exact hsw.trans_le (le_csSup hbdd hwT)
    set x := max ((u₁ + m) / 2) ((s + m) / 2)
    have hx1 : u₁ < x := (by linarith : u₁ < (u₁ + m) / 2).trans_le (le_max_left _ _)
    have hx2 : x < m := max_lt (by linarith) (by linarith)
    have hx3 : s < x := (by linarith : s < (s + m) / 2).trans_le (le_max_right _ _)
    exact (claim1 x hx3 hx2).trans (hu₁' x ⟨hx1, hx2⟩)
  have claim4 : m = s' := by
    by_contra hne
    have hlt : m < s' := lt_of_le_of_ne hms' hne
    obtain ⟨u₂, hu₂, hu₂'⟩ := (hloc m hmI).2
    set w := min ((m + u₂) / 2) s'
    have hmw : m < w := lt_min (by linarith) hlt
    have hwT : w ∈ T := by
      refine ⟨⟨hsm.trans hmw.le, min_le_right _ _⟩, fun u hu => ?_⟩
      rcases lt_trichotomy u m with h1 | rfl | h1
      · exact claim1 u hu.1 h1
      · exact claim3
      · exact claim3.trans (hu₂' u ⟨h1, hu.2.trans_lt ((min_le_left _ _).trans_lt
          (by linarith))⟩)
    exact absurd (le_csSup hbdd hwT) (not_le.2 hmw)
  rw [← claim4]
  exact claim3

/-- A function which is continuous on an open interval and monotone near each of its points is
monotone on the interval. -/
theorem MonotoneOn.of_local (hc : ContinuousOn h (Ioo a b))
    (hloc : ∀ t ∈ Ioo a b, ∃ δ > 0, MonotoneOn h (Ioo (t - δ) (t + δ))) :
    MonotoneOn h (Ioo a b) := by
  intro s hs s' hs' hss'
  have hsub : Icc s s' ⊆ Ioo a b := Icc_subset_Ioo hs.1 hs'.2
  have hcl : IsClosed (h ⁻¹' Ici (h s) ∩ Icc s s') := by
    rw [inter_comm]
    exact (hc.mono hsub).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have := hcl.Icc_subset_of_forall_mem_nhdsWithin (a := s) (b := s') (le_refl (h s)) ?_
  · exact this ⟨hss', le_rfl⟩
  intro u ⟨hu, huI⟩
  obtain ⟨δ, hδ, hmono⟩ := hloc u (hsub (Ico_subset_Icc_self huI))
  filter_upwards [Ioo_mem_nhdsGT (show u < u + δ by linarith)] with x hx
  exact (mem_Ici.1 hu).trans (hmono ⟨by linarith, by linarith⟩ ⟨by linarith [hx.1], hx.2⟩ hx.1.le)

/-- The strict local maxima of any function `ℝ → ℝ` form a countable set. -/
theorem Set.Countable.of_isStrictLocalMax :
    {t : ℝ | ∃ u < t, ∃ u' > t, ∀ s ∈ Ioo u u', s ≠ t → h s < h t}.Countable := by
  set M := {t : ℝ | ∃ u < t, ∃ u' > t, ∀ s ∈ Ioo u u', s ≠ t → h s < h t}
  have key : ∀ t ∈ M, ∃ q : ℚ × ℚ, (q.1 : ℝ) < t ∧ t < q.2 ∧
      ∀ s ∈ Ioo (q.1 : ℝ) q.2, s ≠ t → h s < h t := by
    rintro t ⟨u, hu, u', hu', hM⟩
    obtain ⟨q₁, hq₁, hq₁'⟩ := exists_rat_btwn hu
    obtain ⟨q₂, hq₂, hq₂'⟩ := exists_rat_btwn hu'
    exact ⟨(q₁, q₂), hq₁', hq₂, fun s hs hst => hM s ⟨hq₁.trans hs.1, hs.2.trans hq₂'⟩ hst⟩
  choose! q hq using key
  refine (mapsTo_univ q M).countable_of_injOn (fun t ht t' ht' htt' => ?_) countable_univ
  by_contra hne
  obtain ⟨h1, h2, h3⟩ := hq t ht
  obtain ⟨h1', h2', h3'⟩ := hq t' ht'
  rw [htt'] at h1 h2 h3
  exact lt_asymm (h3 t' ⟨h1', h2'⟩ (Ne.symm hne)) (h3' t ⟨h1, h2⟩ hne)

/-- A strictly increasing function on an open interval whose image contains an open interval is
continuous on some open subinterval. -/
theorem exists_Ioo_continuousOn_of_strictMonoOn (hmono : StrictMonoOn h (Ioo a b)) {c d : ℝ}
    (hcd : c < d) (hsub : Ioo c d ⊆ h '' Ioo a b) :
    ∃ a' b', a' < b' ∧ Ioo a' b' ⊆ Ioo a b ∧ ContinuousOn h (Ioo a' b') := by
  set c' := (2 * c + d) / 3 with hc'v
  set d' := (c + 2 * d) / 3 with hd'v
  have hcc' : c < c' := by linarith
  have hc'd' : c' < d' := by linarith
  have hd'd : d' < d := by linarith
  obtain ⟨t₁, ht₁, hc'⟩ := hsub (show c' ∈ Ioo c d from ⟨hcc', hc'd'.trans hd'd⟩)
  obtain ⟨t₂, ht₂, hd'⟩ := hsub (show d' ∈ Ioo c d from ⟨hcc'.trans hc'd', hd'd⟩)
  have ht : t₁ < t₂ := by
    by_contra hle
    have := hmono.le_iff_le ht₂ ht₁ |>.2 (not_lt.1 hle)
    rw [hc', hd'] at this
    linarith
  have hsubI : Ioo t₁ t₂ ⊆ Ioo a b := Ioo_subset_Ioo ht₁.1.le ht₂.2.le
  refine ⟨t₁, t₂, ht, hsubI, fun t htI => ?_⟩
  refine (continuousAt_of_monotoneOn_of_image_mem_nhds ((hmono.mono hsubI).monotoneOn)
    (Ioo_mem_nhds htI.1 htI.2) ?_).continuousWithinAt
  have hval : h t ∈ Ioo c' d' := by
    rw [← hc', ← hd']
    exact ⟨hmono ht₁ (hsubI htI) htI.1, hmono (hsubI htI) ht₂ htI.2⟩
  refine Filter.mem_of_superset (Ioo_mem_nhds hval.1 hval.2) fun v hv => ?_
  obtain ⟨u, hu, rfl⟩ := hsub (show v ∈ Ioo c d from ⟨hcc'.trans hv.1, hv.2.trans hd'd⟩)
  refine ⟨u, ⟨?_, ?_⟩, rfl⟩
  · rw [← hc'] at hv
    exact (hmono.lt_iff_lt ht₁ hu).1 hv.1
  · rw [← hd'] at hv
    exact (hmono.lt_iff_lt hu ht₂).1 hv.2
