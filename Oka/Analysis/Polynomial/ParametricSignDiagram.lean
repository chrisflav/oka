/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Mathlib.Data.Multiset.DershowitzManna
import Oka.Algebra.Polynomial.PseudoDivision
import Oka.Analysis.Polynomial.SignDiagram

/-!
# Sign diagrams of polynomials with parameters (Cohen–Hörmander)

Let `A` be an integral domain and `F` a finite family (a multiset) of polynomials in `A[X]`.
Every ring homomorphism `f : A →+* ℝ` (a *point*: for `A = MvPolynomial ι ℝ` these are the
evaluations at points of `ℝ^ι`) specialises `F` to a family of real polynomials
`P.map f`. The *sign diagram* of this family is its sign function `y ↦ (sign (P.map f).eval y)_P`
up to order automorphisms of `ℝ`; `Polynomial.SignMatch f g F φ` says that `φ : ℝ ≃o ℝ`
carries the sign diagram at `f` onto the one at `g`.

The main theorem, `Polynomial.exists_signMatch_of_signsAgree`, says that the sign diagram is
determined by finitely many signs of parameters: there is a finite `Q ⊆ A` such that whenever
`f` and `g` give the same sign to every element of `Q`, the sign diagrams at `f` and `g` agree.
This is the heart of the Tarski–Seidenberg theorem; it is proved by Hörmander's induction on the
multiset of degrees (Dershowitz–Manna order, `Multiset.wellFounded_isDershowitzMannaLT`):

* a member whose leading coefficient vanishes at the point is replaced by `eraseLead`
  (`controlsOn_split`);
* when all leading coefficients are nonzero at the point, a member `p` of maximal degree is
  replaced by `p'` and by the pseudo-remainders of `p` modulo the other nonconstant members and
  `p'` (`Polynomial.exists_pseudoDivision`); the sign diagram of the old family is recovered
  from that of the new one by `Polynomial.exists_orderIso_signTransport`.

Nothing here is in Mathlib.
-/

namespace Polynomial

variable {A : Type*} [CommRing A]

/-- `φ` carries the sign diagram of the specialisation of `F` at `f` onto the one at `g`. -/
def SignMatch (f g : A →+* ℝ) (F : Multiset A[X]) (φ : ℝ ≃o ℝ) : Prop :=
  ∀ P ∈ F, ∀ y, SignType.sign ((P.map g).eval (φ y)) = SignType.sign ((P.map f).eval y)

/-- The points `f` and `g` give the same sign to every element of `Q`. -/
def SignsAgree (Q : Finset A) (f g : A →+* ℝ) : Prop :=
  ∀ a ∈ Q, SignType.sign (f a) = SignType.sign (g a)

/-- On the region where no element of `H` vanishes, the signs of the elements of `Q` determine
the sign diagram of `F`. -/
def ControlsOn (Q : Finset A) (F : Multiset A[X]) (H : Finset A) : Prop :=
  ∀ f g : A →+* ℝ, (∀ h ∈ H, f h ≠ 0) → (∀ h ∈ H, g h ≠ 0) → SignsAgree Q f g →
    ∃ φ, SignMatch f g F φ

/-- Agreement of signs on `Q'` implies agreement on any `Q ⊆ Q'`. -/
lemma SignsAgree.mono {Q Q' : Finset A} {f g : A →+* ℝ} (h : Q ⊆ Q') (hQ : SignsAgree Q' f g) :
    SignsAgree Q f g :=
  fun a ha => hQ a (h ha)

/-- Control persists when the controlling set or the region conditions are enlarged. -/
lemma ControlsOn.mono {Q Q' : Finset A} {F : Multiset A[X]} {H H' : Finset A} (hQ : Q ⊆ Q')
    (hH : H ⊆ H') (h : ControlsOn Q F H) : ControlsOn Q' F H' :=
  fun f g hf hg hQ' => h f g (fun x hx => hf x (hH hx)) (fun x hx => hg x (hH hx)) (hQ'.mono hQ)

private lemma sign_cancel {s a b : SignType} (hs : s ≠ 0) (h : s * a = s * b) : a = b := by
  rcases s with _ | _ | _ <;> rcases a with _ | _ | _ <;> rcases b with _ | _ | _ <;>
    first | rfl | exact absurd rfl hs | exact absurd h (by decide)

private lemma dm_lt (F₀ G : Multiset A[X]) (p : A[X])
    (hG : ∀ g ∈ G, natDegree g < natDegree p) :
    Multiset.IsDershowitzMannaLT ((G + F₀).map natDegree) ((p ::ₘ F₀).map natDegree) := by
  refine ⟨F₀.map natDegree, G.map natDegree, {natDegree p}, by simp, by simp [add_comm], ?_, ?_⟩
  · rw [Multiset.map_cons, add_comm, Multiset.singleton_add]
  · intro y hy
    obtain ⟨g, hg, rfl⟩ := Multiset.mem_map.1 hy
    exact ⟨natDegree p, by simp, hG g hg⟩

/-- Splitting on whether the leading coefficient of a member vanishes. -/
private lemma controlsOn_split [DecidableEq A] [DecidableEq A[X]] {Q₁ Q₂ : Finset A}
    {F : Multiset A[X]} {H : Finset A} {P : A[X]}
    (h₁ : ControlsOn Q₁ (eraseLead P ::ₘ F.erase P) ∅)
    (h₂ : ControlsOn Q₂ F (insert P.leadingCoeff H)) :
    ControlsOn (insert P.leadingCoeff (Q₁ ∪ Q₂)) F H := by
  intro f g hf hg hQ
  have hsign := hQ P.leadingCoeff (Finset.mem_insert_self _ _)
  by_cases hfP : f P.leadingCoeff = 0
  · have hgP : g P.leadingCoeff = 0 := by
      rw [hfP, sign_zero, eq_comm, sign_eq_zero_iff] at hsign
      exact hsign
    obtain ⟨φ, hφ⟩ := h₁ f g (by simp) (by simp)
      (hQ.mono (fun a ha => Finset.mem_insert_of_mem (Finset.mem_union_left _ ha)))
    refine ⟨φ, fun R hR y => ?_⟩
    by_cases hRP : R = P
    · subst hRP
      have hmap : ∀ k : A →+* ℝ, k R.leadingCoeff = 0 → R.map k = (eraseLead R).map k := by
        intro k hk
        conv_lhs => rw [← eraseLead_add_monomial_natDegree_leadingCoeff R]
        rw [Polynomial.map_add, Polynomial.map_monomial, hk, monomial_zero_right, add_zero]
      rw [hmap f hfP, hmap g hgP]
      exact hφ _ (Multiset.mem_cons_self _ _) y
    · exact hφ R (Multiset.mem_cons_of_mem ((Multiset.mem_erase_of_ne hRP).2 hR)) y
  · have hgP : g P.leadingCoeff ≠ 0 := fun h => hfP (by
      rw [h, sign_zero, sign_eq_zero_iff] at hsign
      exact hsign)
    exact h₂ f g (Finset.forall_mem_insert _ _ _ |>.2 ⟨hfP, hf⟩)
      (Finset.forall_mem_insert _ _ _ |>.2 ⟨hgP, hg⟩)
      (hQ.mono (fun a ha => Finset.mem_insert_of_mem (Finset.mem_union_right _ ha)))

variable [IsDomain A] [CharZero A]

/-- Hörmander's step: if all leading coefficients of the nonconstant members of `F` are among the
elements of `H` (so nonzero on the region), the sign diagram of `F` is controlled, given control
of all families of smaller degree multiset. -/
private lemma controlsOn_of_leadingCoeff (F : Multiset A[X])
    (ih : ∀ F' : Multiset A[X], Multiset.IsDershowitzMannaLT (F'.map natDegree)
      (F.map natDegree) → ∃ Q, ControlsOn Q F' ∅)
    (H : Finset A) (hH : ∀ P ∈ F, 1 ≤ natDegree P → P.leadingCoeff ∈ H) :
    ∃ Q, ControlsOn Q F H := by
  classical
  by_cases hc : ∀ P ∈ F, natDegree P = 0
  · refine ⟨F.toFinset.image (fun P => P.coeff 0), fun f g _ _ hQ => ⟨OrderIso.refl ℝ, ?_⟩⟩
    intro P hP y
    rw [eq_C_of_natDegree_eq_zero (hc P hP)]
    simpa using (hQ _ (Finset.mem_image_of_mem _ (Multiset.mem_toFinset.2 hP))).symm
  push Not at hc
  obtain ⟨P₀, hP₀, hP₀d⟩ := hc
  have hF0 : F ≠ 0 := by rintro rfl; exact Multiset.notMem_zero _ hP₀
  obtain ⟨p, hpF, hpmax⟩ := Multiset.exists_max_image natDegree hF0
  have hpd : 1 ≤ natDegree p := by
    have := hpmax P₀ hP₀
    omega
  set F₀ := F.erase p with hF₀
  have hF : F = p ::ₘ F₀ := (Multiset.cons_erase hpF).symm
  have hdiv : ∀ g : A[X], 1 ≤ natDegree g → ∃ (k : ℕ) (a r : A[X]),
      C g.leadingCoeff ^ k * p = a * g + r ∧ r.natDegree < g.natDegree :=
    fun g hg => exists_pseudoDivision p g hg
  choose! k a r hrel hrdeg using hdiv
  set G : Multiset A[X] := derivative p ::ₘ F₀.filter (1 ≤ natDegree ·) with hG
  set Rs : Multiset A[X] := (G.filter (1 ≤ natDegree ·)).map r with hRs
  set W : Multiset A[X] := (derivative p ::ₘ Rs) + F₀ with hW
  have hGdeg : ∀ g ∈ G, natDegree g ≤ natDegree p := by
    intro g hg
    rcases Multiset.mem_cons.1 hg with rfl | hg
    · exact natDegree_derivative_le p |>.trans (Nat.sub_le _ _)
    · exact hpmax g (Multiset.mem_of_mem_erase (Multiset.mem_filter.1 hg).1)
  have hWlt : Multiset.IsDershowitzMannaLT (W.map natDegree) (F.map natDegree) := by
    rw [hF, hW]
    refine dm_lt F₀ _ p (fun g hg => ?_)
    rcases Multiset.mem_cons.1 hg with rfl | hg
    · exact natDegree_derivative_lt (by omega)
    · obtain ⟨g', hg', rfl⟩ := Multiset.mem_map.1 hg
      obtain ⟨hg'G, hg'd⟩ := Multiset.mem_filter.1 hg'
      exact (hrdeg g' hg'd).trans_le (hGdeg g' hg'G)
  obtain ⟨QW, hQW⟩ := ih W hWlt
  refine ⟨QW ∪ G.toFinset.image leadingCoeff, fun f g hf hg hQ => ?_⟩
  obtain ⟨φ, hφ⟩ := hQW f g (by simp) (by simp) (hQ.mono Finset.subset_union_left)
  have hlc : ∀ i ∈ G, SignType.sign (f i.leadingCoeff) = SignType.sign (g i.leadingCoeff) :=
    fun i hi => hQ _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _
      (Multiset.mem_toFinset.2 hi)))
  have hlcp : ∀ k : A →+* ℝ, (∀ h ∈ H, k h ≠ 0) → k p.leadingCoeff ≠ 0 :=
    fun k hk => hk _ (hH p hpF hpd)
  have hlcG : ∀ k : A →+* ℝ, (∀ h ∈ H, k h ≠ 0) → ∀ i ∈ G, k i.leadingCoeff ≠ 0 := by
    intro k hk i hi
    rcases Multiset.mem_cons.1 hi with rfl | hi
    · rw [leadingCoeff_derivative, map_mul, map_natCast]
      exact mul_ne_zero (hlcp k hk) (Nat.cast_ne_zero.2 (by omega))
    · obtain ⟨hiF, hid⟩ := Multiset.mem_filter.1 hi
      exact hk _ (hH i (Multiset.mem_of_mem_erase hiF) hid)
  have hu : ∀ k : A →+* ℝ, (∀ h ∈ H, k h ≠ 0) → ∀ i ∈ G, i.map k ≠ 0 := by
    intro k hk i hi h0
    have := hlcG k hk i hi
    rw [← leadingCoeff_map_of_leadingCoeff_ne_zero _ this, h0, leadingCoeff_zero] at this
    exact this rfl
  have hGW : ∀ i ∈ G, i ∈ W := by
    intro i hi
    rcases Multiset.mem_cons.1 hi with rfl | hi
    · exact Multiset.mem_add.2 (Or.inl (Multiset.mem_cons_self _ _))
    · exact Multiset.mem_add.2 (Or.inr (Multiset.mem_filter.1 hi).1)
  have hRW : ∀ i ∈ G, 1 ≤ natDegree i → r i ∈ W := fun i hi hid =>
    Multiset.mem_add.2 (Or.inl (Multiset.mem_cons_of_mem
      (Multiset.mem_map_of_mem _ (Multiset.mem_filter.2 ⟨hi, hid⟩))))
  -- the remainder relation evaluated at a root
  have hremeval : ∀ (k' : A →+* ℝ) (i : A[X]), 1 ≤ natDegree i → ∀ z, (i.map k').eval z = 0 →
      k' i.leadingCoeff ^ k i * (p.map k').eval z = ((r i).map k').eval z := by
    intro k' i hid z hz
    have := congrArg (fun P => (P.map k').eval z) (hrel i hid)
    simpa [Polynomial.map_mul, Polynomial.map_add, hz] using this
  obtain ⟨ψ, hψG, hψp⟩ := exists_orderIso_signTransport (fun i => i.map f) (fun i => i.map g)
    G.toFinset φ (fun i hi y => hφ i (hGW i (Multiset.mem_toFinset.1 hi)) y)
    (fun i hi => hu f hf i (Multiset.mem_toFinset.1 hi))
    (d := derivative p) (Multiset.mem_toFinset.2 (Multiset.mem_cons_self _ _))
    (derivative_map p f) (derivative_map p g) (by
      intro i hi z hz
      have hi := Multiset.mem_toFinset.1 hi
      by_cases hid : 1 ≤ natDegree i
      · have hz' : (i.map g).eval (φ z) = 0 := by
          have := hφ i (hGW i hi) z
          rwa [hz, sign_zero, sign_eq_zero_iff] at this
        have e₁ := hremeval f i hid z hz
        have e₂ := hremeval g i hid (φ z) hz'
        have hs := hφ (r i) (hRW i hi hid) z
        rw [← e₁, ← e₂, sign_mul, sign_mul, sign_pow, sign_pow, hlc i hi] at hs
        refine sign_cancel ?_ hs
        rw [← sign_pow, Ne, sign_eq_zero_iff]
        exact pow_ne_zero _ (hlcG g hg i hi)
      · have hi0 : natDegree i = 0 := by omega
        exfalso
        rw [eq_C_of_natDegree_eq_zero hi0] at hz
        have := hu f hf i hi
        rw [eq_C_of_natDegree_eq_zero hi0] at this
        simp only [map_C, eval_C] at hz this
        exact this (by rw [hz, C_0]))
  refine ⟨ψ, fun R hR y => ?_⟩
  rw [hF] at hR
  rcases Multiset.mem_cons.1 hR with rfl | hR
  · exact hψp y
  by_cases hRd : 1 ≤ natDegree R
  · exact hψG R (Multiset.mem_toFinset.2 (Multiset.mem_cons_of_mem
      (Multiset.mem_filter.2 ⟨hR, hRd⟩))) y
  · have hR0 : natDegree R = 0 := by omega
    have := hφ R (Multiset.mem_add.2 (Or.inr hR)) y
    rw [eq_C_of_natDegree_eq_zero hR0] at this ⊢
    simpa using this

/-- **Cohen–Hörmander.** For every finite family `F` of polynomials over a domain `A` of
characteristic zero, finitely many elements of `A` control the sign diagram of `F` at all real
points: there is a finite `Q ⊆ A` such that points giving the same signs to `Q` give the same
sign diagram to `F`. -/
theorem exists_controlsOn (F : Multiset A[X]) : ∃ Q : Finset A, ControlsOn Q F ∅ := by
  classical
  induction F using (InvImage.wf (fun F : Multiset A[X] => F.map natDegree)
    Multiset.wellFounded_isDershowitzMannaLT).induction with
  | _ F ih =>
  set L := (F.filter (1 ≤ natDegree ·)).toFinset with hL
  suffices h : ∀ n, ∀ S ⊆ L, (L \ S).card = n → ∃ Q, ControlsOn Q F (S.image leadingCoeff) by
    simpa using h _ ∅ (Finset.empty_subset _) rfl
  intro n
  induction n with
  | zero =>
    intro S _ hcard
    rw [Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset] at hcard
    exact controlsOn_of_leadingCoeff F ih _ (fun P hP hPd =>
      Finset.mem_image_of_mem _ (hcard (by simp [L, hP, hPd])))
  | succ n ihn =>
    intro S hS hcard
    obtain ⟨P, hP⟩ : (L \ S).Nonempty := by
      rw [← Finset.card_pos, hcard]
      omega
    obtain ⟨hPL, hPS⟩ := Finset.mem_sdiff.1 hP
    have hPF : P ∈ F := (Multiset.mem_filter.1 (Multiset.mem_toFinset.1 hPL)).1
    have hPd : 1 ≤ natDegree P := (Multiset.mem_filter.1 (Multiset.mem_toFinset.1 hPL)).2
    obtain ⟨Q₁, hQ₁⟩ := ih (eraseLead P ::ₘ F.erase P) (by
      have := dm_lt (F.erase P) {eraseLead P} P (by
        intro g hg
        rw [Multiset.mem_singleton] at hg
        subst hg
        rcases eraseLead_natDegree_lt_or_eraseLead_eq_zero P with h | h
        · exact h
        · rw [h, natDegree_zero]
          omega)
      rwa [Multiset.singleton_add, Multiset.cons_erase hPF] at this)
    obtain ⟨Q₂, hQ₂⟩ := ihn (insert P S) (Finset.insert_subset hPL hS) (by
      rw [Finset.sdiff_insert, Finset.card_erase_of_mem hP, hcard]
      rfl)
    rw [Finset.image_insert] at hQ₂
    exact ⟨_, controlsOn_split hQ₁ hQ₂⟩

/-- **Cohen–Hörmander**, unconditional form: points of `A` (ring homomorphisms to `ℝ`) that give
the same signs to the finitely many elements of `Q` have the same sign diagram for `F`. -/
theorem exists_signMatch_of_signsAgree (F : Multiset A[X]) :
    ∃ Q : Finset A, ∀ f g : A →+* ℝ, SignsAgree Q f g → ∃ φ : ℝ ≃o ℝ, SignMatch f g F φ := by
  obtain ⟨Q, hQ⟩ := exists_controlsOn F
  exact ⟨Q, fun f g h => hQ f g (by simp) (by simp) h⟩

end Polynomial
