/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Mathlib.Algebra.Order.Group.OrderIso
import Mathlib.Data.Finset.Max
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Extending finite order embeddings of `ℝ` to order automorphisms

Every strictly monotone map from a finite subset of `ℝ` to `ℝ` is the restriction of an order
automorphism of `ℝ` (`Real.exists_orderIso_extend`). The automorphism is built one point at a
time, from the left: `Real.exists_orderIso_fix_Iic` produces a piecewise affine automorphism that
fixes `(-∞, c]` pointwise and moves a given point `u > c` to a given point `v > c`.

This is used to compare *sign diagrams* of families of real polynomials: two families have the
same sign diagram when an order automorphism of `ℝ` carries the sign function of one onto that of
the other, and such automorphisms are produced by extending a matching of finitely many roots.

Nothing here is in Mathlib; Mathlib has the analogous statement for countable dense orders
(`Order.iso_of_countable_dense`) but not this finite extension property of `ℝ`.
-/

namespace Real

/-- The piecewise affine map fixing `(-∞, c]`, sending `u` to `v` (for `c < u`, `c < v`) and
translating `[u, ∞)`. -/
private noncomputable def fixIicFun (c u v : ℝ) (y : ℝ) : ℝ :=
  if y ≤ c then y else if y ≤ u then c + (y - c) * ((v - c) / (u - c)) else y - u + v

private lemma fixIicFun_strictMono {c u v : ℝ} (hu : c < u) (hv : c < v) :
    StrictMono (fixIicFun c u v) := by
  have hk : 0 < (v - c) / (u - c) := div_pos (by linarith) (by linarith)
  have hku : (u - c) * ((v - c) / (u - c)) = v - c := by
    field_simp [(by linarith : u - c ≠ 0)]
  intro y₁ y₂ h
  have hm : ∀ y, c < y → y ≤ u → c < c + (y - c) * ((v - c) / (u - c)) ∧
      c + (y - c) * ((v - c) / (u - c)) ≤ v := by
    intro y hy hyu
    refine ⟨by nlinarith [mul_pos (show 0 < y - c by linarith) hk], ?_⟩
    nlinarith [mul_le_mul_of_nonneg_right (show y - c ≤ u - c by linarith) hk.le]
  unfold fixIicFun
  split_ifs with h1 h2 h3 h4 h3 h4 h5 h6
  · exact h
  · linarith [(hm y₂ (by linarith) (by assumption)).1]
  · linarith
  · linarith
  · nlinarith [mul_lt_mul_of_pos_right h hk]
  · linarith [(hm y₁ (by linarith) (by assumption)).2]
  · linarith
  · linarith
  · linarith

private lemma fixIicFun_surjective {c u v : ℝ} (hu : c < u) (hv : c < v) :
    Function.Surjective (fixIicFun c u v) := by
  intro w
  have huc : u - c ≠ 0 := by linarith
  have hvc : v - c ≠ 0 := by linarith
  by_cases hw : w ≤ c
  · exact ⟨w, by simp [fixIicFun, hw]⟩
  by_cases hw' : w ≤ v
  · refine ⟨c + (w - c) * ((u - c) / (v - c)), ?_⟩
    have h1 : 0 < (w - c) * ((u - c) / (v - c)) :=
      mul_pos (by linarith) (div_pos (by linarith) (by linarith))
    have h2 : (w - c) * ((u - c) / (v - c)) ≤ u - c := by
      rw [mul_div_assoc', div_le_iff₀ (by linarith)]
      nlinarith
    have h3 : ¬ c + (w - c) * ((u - c) / (v - c)) ≤ c := by linarith
    have h4 : c + (w - c) * ((u - c) / (v - c)) ≤ u := by linarith
    simp only [fixIicFun, h3, h4, if_false, if_true]
    field_simp
    ring
  · refine ⟨w - v + u, ?_⟩
    have h3 : ¬ w - v + u ≤ c := by linarith
    have h4 : ¬ w - v + u ≤ u := by linarith
    simp only [fixIicFun, h3, h4, if_false]
    ring

/-- For `c < u` and `c < v` there is an order automorphism of `ℝ` fixing `(-∞, c]` pointwise and
sending `u` to `v`. -/
theorem exists_orderIso_fix_Iic {c u v : ℝ} (hu : c < u) (hv : c < v) :
    ∃ χ : ℝ ≃o ℝ, (∀ y ≤ c, χ y = y) ∧ χ u = v := by
  refine ⟨StrictMono.orderIsoOfSurjective _ (fixIicFun_strictMono hu hv)
    (fixIicFun_surjective hu hv), fun y hy => by simp [fixIicFun, hy], ?_⟩
  have h3 : ¬ u ≤ c := by linarith
  simp only [StrictMono.coe_orderIsoOfSurjective, fixIicFun, h3, le_refl, if_true, if_false]
  field_simp [(by linarith : u - c ≠ 0)]
  ring

/-- **Finite extension property of `ℝ`.** A map that is strictly monotone on a finite set `A`
agrees on `A` with some order automorphism of `ℝ`. -/
theorem exists_orderIso_extend (A : Finset ℝ) (e : ℝ → ℝ) (he : StrictMonoOn e A) :
    ∃ ψ : ℝ ≃o ℝ, ∀ a ∈ A, ψ a = e a := by
  induction A using Finset.induction_on_max generalizing e with
  | empty => exact ⟨OrderIso.refl ℝ, by simp⟩
  | insert m s hm ih =>
    obtain ⟨ψ', hψ'⟩ := ih e (he.mono (by simp))
    rcases s.eq_empty_or_nonempty with rfl | hs
    · refine ⟨OrderIso.addRight (e m - m), ?_⟩
      simp
    · set c := s.max' hs
      have hcs : c ∈ s := s.max'_mem hs
      have hcm : c < m := hm c hcs
      have h1 : ψ' c < ψ' m := ψ'.strictMono hcm
      have h2 : ψ' c < e m := by
        rw [hψ' c hcs]
        exact he (by simp [hcs]) (by simp) hcm
      obtain ⟨χ, hχ, hχm⟩ := exists_orderIso_fix_Iic h1 h2
      refine ⟨ψ'.trans χ, ?_⟩
      intro a ha
      rcases Finset.mem_insert.1 ha with rfl | ha
      · simpa using hχm
      · simp only [OrderIso.trans_apply]
        rw [hχ _ (ψ'.monotone (s.le_max' a ha)), hψ' a ha]

end Real
