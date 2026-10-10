/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Mathlib.Topology.Algebra.MvPolynomial
import Oka.Geometry.RealAlgebraic.Semialgebraic.OneVariable

/-!
# Hölder continuity of semialgebraic functions at a point

A semialgebraic function `h : ℝ → ℝ` with `h t → 0` as `t → 0⁺` tends to `0` at least like a
power of `t`: `|h t| ^ N ≤ t` for some `N ≥ 1` and all small `t > 0`
(`IsSemialgebraicFun.exists_pow_le`). This is the part of the Puiseux-type growth lemma for
semialgebraic functions (Bochnak–Coste–Roy, *Real algebraic geometry*, §2.6) that is needed for
the Łojasiewicz inequality.

The proof does not use Puiseux series:

* `IsSemialgebraicFun.exists_poly`: the graph of `h` lies on an algebraic curve `Q(t, y) = 0`
  with `Q ≠ 0`: at every `t`, `h t` is a root of some nonzero polynomial of the finite family
  defining the graph, since otherwise all members keep their signs near `(t, h t)` and the graph
  would contain a segment;
* if `|h t| ^ N ≤ t` failed for `N` larger than the `y`-degree of `Q`, then by o-minimality
  `t < |h t| ^ N` for all small `t`, and the monomial of `Q` that is minimal in the
  lexicographic order (first in `t`, then in `y`) would dominate all others in
  `Q(t, h t) = 0`, a contradiction (a one-step Newton polygon argument).

Not in Mathlib.
-/

open Set Filter Topology MvPolynomial

namespace IsSemialgebraicFun

variable {h : ℝ → ℝ}

/-- The graph of a semialgebraic function lies on a plane algebraic curve. -/
theorem exists_poly (hh : IsSemialgebraicFun h) :
    ∃ Q : MvPolynomial (Fin 2) ℝ, Q ≠ 0 ∧ ∀ t, eval ![t, h t] Q = 0 := by
  classical
  obtain ⟨F, hF⟩ := hh
  refine ⟨∏ P ∈ F.filter (· ≠ 0), P, ?_, fun t => ?_⟩
  · rw [Finset.prod_ne_zero_iff]
    intro P hP
    exact (Finset.mem_filter.1 hP).2
  by_contra hne
  rw [map_prod] at hne
  replace hne := Finset.prod_ne_zero_iff.1 hne
  have hev : ∀ P ∈ F, ∀ᶠ y in 𝓝[≠] (h t),
      SignType.sign (eval ![t, y] P) = SignType.sign (eval ![t, h t] P) := by
    intro P hP
    by_cases hP0 : P = 0
    · simp [hP0]
    have hne' := hne P (Finset.mem_filter.2 ⟨hP, hP0⟩)
    have hc : Continuous fun y : ℝ => eval ![t, y] P :=
      (MvPolynomial.continuous_eval P).comp (continuous_pi fun i => by
        fin_cases i
        · exact continuous_const
        · exact continuous_id)
    apply eventually_nhdsWithin_of_eventually_nhds
    rcases hne'.lt_or_gt with hlt | hlt
    · filter_upwards [hc.continuousAt.eventually_lt continuousAt_const hlt] with y hy
      rw [sign_neg hy, sign_neg hlt]
    · filter_upwards [continuousAt_const.eventually_lt hc.continuousAt hlt] with y hy
      rw [sign_pos hy, sign_pos hlt]
  obtain ⟨y, hy, hyne⟩ :=
    (((Filter.eventually_all_finset F).2 hev).and self_mem_nhdsWithin).exists
  have := hF ![t, h t] ![t, y] (fun P hP => (hy P hP).symm) (by simp)
  simp only [Set.mem_setOf_eq, Matrix.cons_val_zero, Matrix.cons_val_one] at this
  exact hyne this.symm

/-- Each non-dominant monomial is small compared to the dominant one. -/
private lemma term_le {t v : ℝ} {j₀ k₀ N : ℕ} (m : Fin 2 →₀ ℕ) (ht : 0 < t) (ht1 : t ≤ 1)
    (hv1 : |v| ≤ 1) (htv : t ≤ |v| ^ N) (hN : k₀ + 1 ≤ N + m 1)
    (hm : m 0 = j₀ ∧ k₀ + 1 ≤ m 1 ∨ j₀ < m 0) :
    |t ^ m 0 * v ^ m 1| ≤ |v| * (t ^ j₀ * |v| ^ k₀) := by
  rw [abs_mul, abs_pow, abs_pow, abs_of_pos ht]
  have hv0 := abs_nonneg v
  rcases hm with ⟨h0, h1⟩ | h0
  · rw [h0]
    calc t ^ j₀ * |v| ^ m 1 ≤ t ^ j₀ * |v| ^ (k₀ + 1) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hv0 hv1 h1) (pow_nonneg ht.le _)
      _ = |v| * (t ^ j₀ * |v| ^ k₀) := by ring
  · have h2 : t ^ m 0 ≤ t ^ j₀ * |v| ^ N := by
      calc t ^ m 0 = t ^ j₀ * t ^ (m 0 - j₀) := by rw [← pow_add, Nat.add_sub_cancel' h0.le]
        _ ≤ t ^ j₀ * t := by
          refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg ht.le _)
          simpa using pow_le_pow_of_le_one ht.le ht1
            (Nat.le_sub_of_add_le (by omega : 1 + j₀ ≤ m 0))
        _ ≤ t ^ j₀ * |v| ^ N := mul_le_mul_of_nonneg_left htv (pow_nonneg ht.le _)
    calc t ^ m 0 * |v| ^ m 1 ≤ t ^ j₀ * |v| ^ N * |v| ^ m 1 :=
          mul_le_mul_of_nonneg_right h2 (pow_nonneg hv0 _)
      _ = t ^ j₀ * |v| ^ (N + m 1) := by ring
      _ ≤ t ^ j₀ * |v| ^ (k₀ + 1) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hv0 hv1 hN) (pow_nonneg ht.le _)
      _ = |v| * (t ^ j₀ * |v| ^ k₀) := by ring

/-- **Hölder estimate at a point.** A semialgebraic function tending to `0` at `0⁺` is bounded
by a power `t ^ (1 / N)` near `0⁺`. -/
theorem exists_pow_le (hh : IsSemialgebraicFun h) (h0 : Tendsto h (𝓝[>] 0) (𝓝 0)) :
    ∃ N : ℕ, 0 < N ∧ ∀ᶠ t in 𝓝[>] 0, |h t| ^ N ≤ t := by
  classical
  obtain ⟨Q, hQ0, hQ⟩ := hh.exists_poly
  set S := Q.support with hSdef
  have hS : S.Nonempty := Finset.nonempty_of_ne_empty (by simpa [S] using hQ0)
  set K := S.sup (fun m => m 1)
  set N := 2 * (K + 1)
  have hNeven : Even N := even_two_mul _
  refine ⟨N, by omega, ?_⟩
  have hset : IsSemialgebraic₁ {t | h t ^ N ≤ t} := by
    have : IsSemialgebraic {x : Unit → ℝ | ∃ v, h (x ()) = v ∧ v ^ N ≤ x ()} := by
      semialg using hh.setOf_graph
    exact this.congr (by ext x; simp)
  rcases hset.eventually_nhdsGT 0 with hgood | hbad
  · filter_upwards [hgood] with t ht
    rwa [hNeven.pow_abs]
  exfalso
  -- the dominant monomial
  set j₀ := S.inf' hS (fun m => m 0)
  obtain ⟨m₁, hm₁S, hm₁⟩ := Finset.exists_mem_eq_inf' hS (fun m => m 0)
  set S₀ := S.filter (fun m => m 0 = j₀)
  have hS₀ : S₀.Nonempty := ⟨m₁, Finset.mem_filter.2 ⟨hm₁S, hm₁.symm⟩⟩
  obtain ⟨m₀, hm₀S₀, hm₀⟩ := Finset.exists_mem_eq_inf' hS₀ (fun m => m 1)
  set k₀ := m₀ 1
  have hm₀S : m₀ ∈ S := (Finset.mem_filter.1 hm₀S₀).1
  have hm₀0 : m₀ 0 = j₀ := (Finset.mem_filter.1 hm₀S₀).2
  set a₀ := coeff m₀ Q
  have ha₀ : a₀ ≠ 0 := mem_support_iff.1 hm₀S
  set A := ∑ m ∈ S, |coeff m Q|
  have hA : |a₀| ≤ A := Finset.single_le_sum (f := fun m => |coeff m Q|)
    (fun m _ => abs_nonneg _) hm₀S
  have hApos : 0 < A := (abs_pos.2 ha₀).trans_le hA
  -- choose a good small `t`
  have ev1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < 1 :=
    Filter.mem_of_superset (Ioo_mem_nhdsGT one_pos) fun t ht => ht.2
  have ev2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), |h t| < min 1 (|a₀| / A) := by
    have := h0.abs
    rw [abs_zero] at this
    exact this.eventually (gt_mem_nhds (lt_min one_pos (div_pos (abs_pos.2 ha₀) hApos)))
  obtain ⟨t, ht1, ht2, ht3, ht4⟩ :=
    (ev1.and (ev2.and ((eventually_mem_nhdsWithin : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Ioi 0).and
      hbad))).exists
  simp only [mem_Ioi, mem_setOf_eq, not_le] at ht3 ht4
  rw [← hNeven.pow_abs] at ht4
  set v := h t
  have hv1 : |v| ≤ 1 := (ht2.trans_le (min_le_left _ _)).le
  have hvA : |v| * A < |a₀| := by
    have := ht2.trans_le (min_le_right _ _)
    rwa [lt_div_iff₀ hApos] at this
  have hvpos : 0 < |v| := by
    by_contra hv
    have : |v| = 0 := le_antisymm (not_lt.1 hv) (abs_nonneg v)
    rw [this, zero_pow (by omega)] at ht4
    linarith
  have hK : k₀ ≤ K := Finset.le_sup (f := fun m => m 1) hm₀S
  -- the relation `Q(t, h t) = 0` as a sum of monomials
  have key := hQ t
  rw [eval_eq'] at key
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at key
  rw [← Finset.add_sum_erase S _ hm₀S] at key
  set B := t ^ j₀ * |v| ^ k₀
  have hBpos : 0 < B := mul_pos (pow_pos ht3 _) (pow_pos hvpos _)
  have hrest : |∑ m ∈ S.erase m₀, coeff m Q * (t ^ m 0 * v ^ m 1)| ≤ A * |v| * B := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ m ∈ S.erase m₀, |coeff m Q * (t ^ m 0 * v ^ m 1)|
        ≤ ∑ m ∈ S.erase m₀, |coeff m Q| * (|v| * B) := by
          refine Finset.sum_le_sum fun m hm => ?_
          rw [abs_mul]
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          have hmS := Finset.mem_of_mem_erase hm
          have hmne := Finset.ne_of_mem_erase hm
          refine term_le m ht3 ht1.le hv1 ht4.le ?_ ?_
          · have : m 1 ≤ K := Finset.le_sup (f := fun m => m 1) hmS
            omega
          · have hj : j₀ ≤ m 0 := Finset.inf'_le _ hmS
            rcases hj.lt_or_eq with hj | hj
            · exact Or.inr hj
            · refine Or.inl ⟨hj.symm, ?_⟩
              have hk : k₀ ≤ m 1 := by
                rw [← hm₀]
                exact Finset.inf'_le _ (Finset.mem_filter.2 ⟨hmS, hj.symm⟩)
              rcases hk.lt_or_eq with hk | hk
              · omega
              · exfalso
                apply hmne
                ext i
                fin_cases i
                · simp [← hj, hm₀0]
                · simp [← hk, k₀]
      _ ≤ ∑ m ∈ S, |coeff m Q| * (|v| * B) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
            (fun _ _ _ => mul_nonneg (abs_nonneg _) (mul_nonneg (abs_nonneg _) hBpos.le))
      _ = A * |v| * B := by rw [← Finset.sum_mul]; ring
  have hlead : |coeff m₀ Q * (t ^ m₀ 0 * v ^ m₀ 1)| = |a₀| * B := by
    rw [abs_mul, abs_mul, abs_pow, abs_pow, abs_of_pos ht3, hm₀0]
  have hT := congrArg abs (eq_neg_of_add_eq_zero_left key)
  rw [abs_neg, hlead] at hT
  nlinarith [hrest, mul_lt_mul_of_pos_right hvA hBpos]

end IsSemialgebraicFun
