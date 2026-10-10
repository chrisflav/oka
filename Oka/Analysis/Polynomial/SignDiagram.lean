/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Analysis.Polynomial.SignGap
import Oka.Data.Real.OrderIsoExtend

/-!
# Transporting sign diagrams of real polynomials (Hörmander's step)

Two families `u`, `v` of real polynomials, indexed by the same finite set `G`, *have the same sign
diagram* when some order automorphism `φ` of `ℝ` satisfies
`sign (v i (φ y)) = sign (u i y)` for all `i ∈ G` and `y ∈ ℝ`.

The main result, `Polynomial.exists_orderIso_signTransport`, is the inductive step of Hörmander's
proof of the Tarski–Seidenberg theorem (Hörmander, *The analysis of linear partial differential
operators II*, Appendix A.2; Bochnak–Coste–Roy, *Real algebraic geometry*, §1.4). Suppose `φ`
matches the sign diagrams of `u` and `v` on `G`, all members are nonzero, `p' = u d` and
`q' = v d` for some `d ∈ G`, and `φ` matches the signs of `p` and `q` at every root of every
`u i`. Then a (possibly different) automorphism `ψ` matches the sign diagrams of
`G ∪ {p}` and `G ∪ {q}`.

The automorphism `ψ` agrees with `φ` on the roots `Z` of the family and sends each root of `p`
outside `Z` to the root of `q` in the corresponding gap (`Real.exists_orderIso_extend`); the
signs of `p` on each gap are then read off from `Polynomial.sign_eval_of_not_leftAnchor`,
`Polynomial.sign_eval_of_not_rightAnchor` and `Polynomial.exists_root_of_anchor`.

Nothing here is in Mathlib.
-/

open Set

namespace Polynomial

section Transport

variable {Z : Finset ℝ} (ψ : ℝ ≃o ℝ) {p q : ℝ[X]} {y : ℝ}

/-- Left anchors are transported by an order automorphism `ψ` that preserves the signs of
`p` on `Z` and of `p'` at `y`. -/
lemma leftAnchor_image_iff (hZ : ∀ z ∈ Z, SignType.sign (q.eval (ψ z)) = SignType.sign (p.eval z))
    (hd : SignType.sign ((derivative q).eval (ψ y)) = SignType.sign ((derivative p).eval y)) :
    LeftAnchor (Z.image ψ) q (ψ y) ↔ LeftAnchor Z p y := by
  constructor
  · intro h a ha hay hmax
    have := h (ψ a) (Finset.mem_image_of_mem ψ ha) (ψ.lt_iff_lt.2 hay) (by
      intro z' hz' hlt
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hz'
      exact ψ.le_iff_le.2 (hmax z hz (ψ.lt_iff_lt.1 hlt)))
    rwa [hZ a ha, hd] at this
  · intro h a' ha' hay hmax
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 ha'
    rw [hZ a ha, hd]
    exact h a ha (ψ.lt_iff_lt.1 hay) (fun z hz hzy =>
      ψ.le_iff_le.1 (hmax (ψ z) (Finset.mem_image_of_mem ψ hz) (ψ.lt_iff_lt.2 hzy)))

/-- Right anchors are transported by an order automorphism `ψ` that preserves the signs of
`p` on `Z` and of `p'` at `y`. -/
lemma rightAnchor_image_iff (hZ : ∀ z ∈ Z, SignType.sign (q.eval (ψ z)) = SignType.sign (p.eval z))
    (hd : SignType.sign ((derivative q).eval (ψ y)) = SignType.sign ((derivative p).eval y)) :
    RightAnchor (Z.image ψ) q (ψ y) ↔ RightAnchor Z p y := by
  constructor
  · intro h b hb hyb hmin
    have := h (ψ b) (Finset.mem_image_of_mem ψ hb) (ψ.lt_iff_lt.2 hyb) (by
      intro z' hz' hlt
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hz'
      exact ψ.le_iff_le.2 (hmin z hz (ψ.lt_iff_lt.1 hlt)))
    rwa [hZ b hb, hd] at this
  · intro h b' hb' hyb hmin
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hb'
    rw [hZ b hb, hd]
    exact h b hb (ψ.lt_iff_lt.1 hyb) (fun z hz hzy =>
      ψ.le_iff_le.1 (hmin (ψ z) (Finset.mem_image_of_mem ψ hz) (ψ.lt_iff_lt.2 hzy)))

/-- An order automorphism carries gaps of `Z` to gaps of `ψ '' Z`. -/
lemma sameGap_image_iff {y' : ℝ} : SameGap (Z.image ψ) (ψ y) (ψ y') ↔ SameGap Z y y' := by
  constructor
  · intro h z hz
    simpa only [ψ.lt_iff_lt] using h (ψ z) (Finset.mem_image_of_mem ψ hz)
  · intro h z' hz'
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hz'
    simpa only [ψ.lt_iff_lt] using h z hz

/-- An order automorphism preserves the sign of differences. -/
lemma sign_sub_orderIso (a b : ℝ) : SignType.sign (ψ a - ψ b) = SignType.sign (a - b) := by
  rcases lt_trichotomy a b with h | rfl | h
  · rw [sign_neg (sub_neg.2 (ψ.lt_iff_lt.2 h)), sign_neg (sub_neg.2 h)]
  · simp
  · rw [sign_pos (sub_pos.2 (ψ.lt_iff_lt.2 h)), sign_pos (sub_pos.2 h)]

end Transport

/-- **Hörmander's step.** Let `φ` match the sign diagrams of two families `u`, `v` of nonzero
real polynomials indexed by `G`. Suppose `p' = u d` and `q' = v d` for some `d ∈ G`, and that `φ`
matches the signs of `p` and `q` at the roots of the members of `u`. Then some order automorphism
`ψ` matches the sign diagrams of the families enlarged by `p` and by `q`. -/
theorem exists_orderIso_signTransport {I : Type*} (u v : I → ℝ[X]) (G : Finset I)
    (φ : ℝ ≃o ℝ)
    (hφ : ∀ i ∈ G, ∀ y, SignType.sign ((v i).eval (φ y)) = SignType.sign ((u i).eval y))
    (hu : ∀ i ∈ G, u i ≠ 0) {p q : ℝ[X]} {d : I} (hd : d ∈ G)
    (hpd : derivative p = u d) (hqd : derivative q = v d)
    (hroot : ∀ i ∈ G, ∀ z, (u i).eval z = 0 →
      SignType.sign (q.eval (φ z)) = SignType.sign (p.eval z)) :
    ∃ ψ : ℝ ≃o ℝ,
      (∀ i ∈ G, ∀ y, SignType.sign ((v i).eval (ψ y)) = SignType.sign ((u i).eval y)) ∧
      ∀ y, SignType.sign (q.eval (ψ y)) = SignType.sign (p.eval y) := by
  classical
  set Z : Finset ℝ := G.biUnion fun i => (u i).roots.toFinset with hZdef
  have memZ : ∀ y, y ∈ Z ↔ ∃ i ∈ G, (u i).eval y = 0 := by
    intro y
    simp only [Z, Finset.mem_biUnion, Multiset.mem_toFinset]
    constructor
    · rintro ⟨i, hi, h⟩
      exact ⟨i, hi, (mem_roots (hu i hi)).1 h⟩
    · rintro ⟨i, hi, h⟩
      exact ⟨i, hi, (mem_roots (hu i hi)).2 h⟩
  have memZφ : ∀ y, y ∈ Z.image φ ↔ ∃ i ∈ G, (v i).eval y = 0 := by
    intro y
    rw [Finset.mem_image]
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨i, hi, h⟩ := (memZ z).1 hz
      refine ⟨i, hi, ?_⟩
      have := hφ i hi z
      rwa [h, sign_zero, sign_eq_zero_iff] at this
    · rintro ⟨i, hi, h⟩
      refine ⟨φ.symm y, (memZ _).2 ⟨i, hi, ?_⟩, φ.apply_symm_apply y⟩
      have := hφ i hi (φ.symm y)
      rwa [φ.apply_symm_apply, h, sign_zero, eq_comm, sign_eq_zero_iff] at this
  have hZp : ∀ t, (derivative p).eval t = 0 → t ∈ Z :=
    fun t ht => (memZ t).2 ⟨d, hd, hpd ▸ ht⟩
  have hp0 : p ≠ 0 := by
    rintro rfl
    exact hu d hd (by rw [← hpd]; simp)
  have hZφ : ∀ z ∈ Z, SignType.sign (q.eval (φ z)) = SignType.sign (p.eval z) := by
    intro z hz
    obtain ⟨i, hi, h⟩ := (memZ z).1 hz
    exact hroot i hi z h
  have hdφ : ∀ y, SignType.sign ((derivative q).eval (φ y)) =
      SignType.sign ((derivative p).eval y) := by
    intro y
    rw [hpd, hqd]
    exact hφ d hd y
  have hZq : ∀ (χ : ℝ ≃o ℝ), Z.image χ = Z.image φ →
      ∀ t, (derivative q).eval t = 0 → t ∈ Z.image χ := by
    intro χ hχ t ht
    rw [hχ]
    exact (memZφ t).2 ⟨d, hd, hqd ▸ ht⟩
  have hnotZ : ∀ (χ : ℝ ≃o ℝ) y, y ∉ Z → χ y ∉ Z.image χ := by
    intro χ y hy h
    obtain ⟨z, hz, hzy⟩ := Finset.mem_image.1 h
    exact hy (χ.injective hzy ▸ hz)
  -- the roots of `p` off `Z`, and the matching roots of `q`
  set Rp := p.roots.toFinset.filter (· ∉ Z) with hRpdef
  have memRp : ∀ r, r ∈ Rp ↔ p.eval r = 0 ∧ r ∉ Z := by
    intro r
    simp [Rp, mem_roots hp0]
  have hρ : ∀ r ∈ Rp, ∃ ρ, ρ ∉ Z.image φ ∧ q.eval ρ = 0 ∧ SameGap (Z.image φ) (φ r) ρ := by
    intro r hr
    obtain ⟨hr0, hrZ⟩ := (memRp r).1 hr
    obtain ⟨hL, hR⟩ := anchor_of_root hZp hrZ hr0
    obtain ⟨ρ, hρZ, hρ0, hgap, -⟩ := exists_root_of_anchor (hZq φ rfl) (hnotZ φ r hrZ)
      ((leftAnchor_image_iff φ hZφ (hdφ r)).2 hL) ((rightAnchor_image_iff φ hZφ (hdφ r)).2 hR)
    exact ⟨ρ, hρZ, hρ0, hgap⟩
  choose! ρ hρZ hρ0 hρgap using hρ
  have key1 : ∀ z ∈ Z, ∀ r ∈ Rp, z < r → φ z < ρ r := fun z hz r hr h =>
    (hρgap r hr (φ z) (Finset.mem_image_of_mem φ hz)).1 (φ.lt_iff_lt.2 h)
  have key2 : ∀ z ∈ Z, ∀ r ∈ Rp, r < z → ρ r < φ z := by
    intro z hz r hr h
    have h1 : ¬ φ z < ρ r := fun h' =>
      (not_lt.2 h.le) (φ.lt_iff_lt.1 ((hρgap r hr (φ z) (Finset.mem_image_of_mem φ hz)).2 h'))
    exact lt_of_le_of_ne (not_lt.1 h1) (fun e => hρZ r hr (e ▸ Finset.mem_image_of_mem φ hz))
  have key3 : ∀ r ∈ Rp, ∀ r' ∈ Rp, r < r' → ∃ z ∈ Z, r < z ∧ z < r' := by
    intro r hr r' hr' h
    by_contra hcon
    push Not at hcon
    obtain ⟨hr0, hrZ⟩ := (memRp r).1 hr
    obtain ⟨hr'0, hr'Z⟩ := (memRp r').1 hr'
    have hgap : SameGap Z r r' := by
      intro z hz
      refine ⟨fun h' => h'.trans h, fun h' => ?_⟩
      by_contra h''
      have hrz : r < z := lt_of_le_of_ne (not_lt.1 h'') (fun e => hrZ (e ▸ hz))
      exact (not_lt.2 (hcon z hz hrz)) h'
    exact absurd (eq_of_sameGap_of_root hZp hrZ hr'Z hr0 hr'0 hgap) h.ne
  -- the finite matching and its extension `ψ`
  set E : ℝ → ℝ := fun y => if y ∈ Z then φ y else ρ y with hEdef
  have hEmono : StrictMonoOn E ↑(Z ∪ Rp) := by
    intro a ha b hb hab
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe] at ha hb
    have hRZ : ∀ r ∈ Rp, r ∉ Z := fun r hr => ((memRp r).1 hr).2
    by_cases haZ : a ∈ Z <;> by_cases hbZ : b ∈ Z <;> simp only [E, haZ, hbZ, if_true, if_false]
    · exact φ.lt_iff_lt.2 hab
    · exact key1 a haZ b (hb.resolve_left hbZ) hab
    · exact key2 b hbZ a (ha.resolve_left haZ) hab
    · obtain ⟨z, hz, h1, h2⟩ := key3 a (ha.resolve_left haZ) b (hb.resolve_left hbZ) hab
      exact (key2 z hz a (ha.resolve_left haZ) h1).trans (key1 z hz b (hb.resolve_left hbZ) h2)
  obtain ⟨ψ, hψ⟩ := Real.exists_orderIso_extend (Z ∪ Rp) E hEmono
  have hψZ : ∀ z ∈ Z, ψ z = φ z := fun z hz => by
    rw [hψ z (Finset.mem_union_left _ hz)]
    simp [E, hz]
  have hψR : ∀ r ∈ Rp, ψ r = ρ r := fun r hr => by
    rw [hψ r (Finset.mem_union_right _ hr)]
    simp [E, ((memRp r).1 hr).2]
  have himg : Z.image ψ = Z.image φ := Finset.image_congr (fun z hz => hψZ z hz)
  have hZψ : ∀ z ∈ Z, SignType.sign (q.eval (ψ z)) = SignType.sign (p.eval z) :=
    fun z hz => by rw [hψZ z hz]; exact hZφ z hz
  have hgapψφ : ∀ y, SameGap (Z.image ψ) (ψ y) (φ y) := by
    intro y z' hz'
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hz'
    rw [ψ.lt_iff_lt, hψZ z hz, φ.lt_iff_lt]
  -- the members of `G`
  have hG : ∀ i ∈ G, ∀ y, SignType.sign ((v i).eval (ψ y)) = SignType.sign ((u i).eval y) := by
    intro i hi y
    by_cases hy : y ∈ Z
    · rw [hψZ y hy]
      exact hφ i hi y
    · rw [← hφ i hi y]
      have hφy : φ y ∉ Z.image ψ := by rw [himg]; exact hnotZ φ y hy
      refine sign_eval_eq_of_forall_ne_zero _ (fun t ht h0 => ?_)
      have htZ : t ∈ Z.image ψ := by rw [himg]; exact (memZφ t).2 ⟨i, hi, h0⟩
      exact (hgapψφ y).not_mem_uIcc (hnotZ ψ y hy) hφy t htZ ht
  refine ⟨ψ, hG, fun y => ?_⟩
  by_cases hyZ : y ∈ Z
  · exact hZψ y hyZ
  have hdψ : SignType.sign ((derivative q).eval (ψ y)) =
      SignType.sign ((derivative p).eval y) := by
    rw [hpd, hqd]
    exact hG d hd y
  have hZqψ := hZq ψ himg
  have hψy := hnotZ ψ y hyZ
  by_cases hL : LeftAnchor Z p y
  · by_cases hR : RightAnchor Z p y
    · obtain ⟨r, hrZ, hr0, hgap, hsign⟩ := exists_root_of_anchor hZp hyZ hL hR
      have hrRp : r ∈ Rp := (memRp r).2 ⟨hr0, hrZ⟩
      obtain ⟨r', -, -, -, hsign'⟩ := exists_root_of_anchor hZqψ hψy
        ((leftAnchor_image_iff ψ hZψ hdψ).2 hL) ((rightAnchor_image_iff ψ hZψ hdψ).2 hR)
      have hq'ne : SignType.sign ((derivative q).eval (ψ y)) ≠ 0 := by
        rw [hdψ, Ne, sign_eq_zero_iff]
        exact fun h => hyZ (hZp y h)
      have h1 := hsign' (ψ r) (hnotZ ψ r hrZ) ((sameGap_image_iff ψ).2 hgap)
      rw [hψR r hrRp, hρ0 r hrRp, sign_zero, eq_comm, mul_eq_zero] at h1
      have hrr' : ρ r = r' := by
        rcases h1 with h1 | h1
        · exact absurd h1 hq'ne
        · linarith [sign_eq_zero_iff.1 h1]
      rw [hsign' (ψ y) hψy (SameGap.refl _ _), hsign y hyZ (SameGap.refl _ _), hdψ, ← hrr',
        ← hψR r hrRp, sign_sub_orderIso]
    · rw [sign_eval_of_not_rightAnchor hZqψ hψy (mt (rightAnchor_image_iff ψ hZψ hdψ).1 hR),
        sign_eval_of_not_rightAnchor hZp hyZ hR, hdψ]
  · rw [sign_eval_of_not_leftAnchor hZqψ hψy (mt (leftAnchor_image_iff ψ hZψ hdψ).1 hL),
      sign_eval_of_not_leftAnchor hZp hyZ hL, hdψ]

end Polynomial
