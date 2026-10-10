/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Uniformization.FEtCovering
import Mathlib.Analysis.Polynomial.CauchyBound

/-!
# The deck group acts transitively on the lifts

In the setting of `FEtCovering`, suppose the base functions `ι₀ a` are invariant under a group
`Γ ≤ SL(2, ℝ)`, polynomially bounded in a fixed function `h₀`, and that every `Γ`-invariant
holomorphic function polynomially bounded in `h₀` lies in `ι₀(A)`. If `B` is a domain integral
over `A` and `ι₀` is injective, then `Γ` acts transitively on the lifts (`FEt.exists_smul_eq`):
the symmetric functions of the values `f(τ)(b₀)` over a `Γ`-orbit `S` of lifts are
`Γ`-invariant, hence lie in `ι₀(A)`, so `b₀` satisfies a monic equation of degree `|S|` over `A`;
at a point where `b₀` separates the `n` points over `χ_τ`, this forces `|S| ≥ n`.
-/

open Complex Metric Set Filter Topology Polynomial
open UpperHalfPlane hiding I I_re I_im
open scoped MatrixGroups

namespace Uniformization

namespace FEt

variable {A B : Type*} [CommRing A] [Algebra ℂ A] [CommRing B] [Algebra ℂ B] [Algebra A B]
  {ι₀ : A →ₐ[ℂ] (ℍ → ℂ)}

/-- `u` is bounded by a polynomial in `‖h₀‖`. -/
def PolyBdd (h₀ : ℍ → ℂ) (u : ℍ → ℝ) : Prop := ∃ C : ℝ, ∃ N : ℕ, ∀ τ, u τ ≤ C * (2 + ‖h₀ τ‖) ^ N

namespace PolyBdd

variable {h₀ : ℍ → ℂ}

theorem const (c : ℝ) : PolyBdd h₀ fun _ ↦ c := ⟨c, 0, fun τ ↦ by simp⟩

theorem mono {u v : ℍ → ℝ} (hv : PolyBdd h₀ v) (h : ∀ τ, u τ ≤ v τ) : PolyBdd h₀ u := by
  obtain ⟨C, N, hC⟩ := hv
  exact ⟨C, N, fun τ ↦ (h τ).trans (hC τ)⟩

theorem add {u v : ℍ → ℝ} (hu : PolyBdd h₀ u) (hv : PolyBdd h₀ v) : PolyBdd h₀ (u + v) := by
  obtain ⟨C, N, hC⟩ := hu
  obtain ⟨D, M, hD⟩ := hv
  refine ⟨|C| + |D|, N + M, fun τ ↦ ?_⟩
  have h1 : 1 ≤ 2 + ‖h₀ τ‖ := by linarith [norm_nonneg (h₀ τ)]
  have hN : (2 + ‖h₀ τ‖) ^ N ≤ (2 + ‖h₀ τ‖) ^ (N + M) := pow_le_pow_right₀ h1 (by omega)
  have hM : (2 + ‖h₀ τ‖) ^ M ≤ (2 + ‖h₀ τ‖) ^ (N + M) := pow_le_pow_right₀ h1 (by omega)
  have hp : 0 ≤ (2 + ‖h₀ τ‖) ^ N := by positivity
  have hq : 0 ≤ (2 + ‖h₀ τ‖) ^ M := by positivity
  have := hC τ
  have := hD τ
  simp only [Pi.add_apply]
  nlinarith [le_abs_self C, le_abs_self D, abs_nonneg C, abs_nonneg D]

theorem mul {u v : ℍ → ℝ} (hu : PolyBdd h₀ u) (hv : PolyBdd h₀ v) (hu0 : ∀ τ, 0 ≤ u τ)
    (hv0 : ∀ τ, 0 ≤ v τ) : PolyBdd h₀ (u * v) := by
  obtain ⟨C, N, hC⟩ := hu
  obtain ⟨D, M, hD⟩ := hv
  refine ⟨C * D, N + M, fun τ ↦ ?_⟩
  simp only [Pi.mul_apply, pow_add]
  have := mul_le_mul (hC τ) (hD τ) (hv0 τ) ((hu0 τ).trans (hC τ))
  linarith

theorem prod {ι : Type*} (s : Finset ι) {u : ι → ℍ → ℝ} (hu : ∀ i ∈ s, PolyBdd h₀ (u i))
    (hu0 : ∀ i ∈ s, ∀ τ, 0 ≤ u i τ) : PolyBdd h₀ fun τ ↦ ∏ i ∈ s, u i τ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using const 1
  | insert j s hj ih =>
    simp_rw [Finset.prod_insert hj]
    exact mul (hu j (Finset.mem_insert_self _ _))
      (ih (fun i hi ↦ hu i (Finset.mem_insert_of_mem hi))
        fun i hi ↦ hu0 i (Finset.mem_insert_of_mem hi))
      (hu0 j (Finset.mem_insert_self _ _))
      fun τ ↦ Finset.prod_nonneg fun i hi ↦ hu0 i (Finset.mem_insert_of_mem hi) τ

theorem sum {ι : Type*} (s : Finset ι) {u : ι → ℍ → ℝ} (hu : ∀ i ∈ s, PolyBdd h₀ (u i)) :
    PolyBdd h₀ fun τ ↦ ∑ i ∈ s, u i τ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using const 0
  | insert j s hj ih =>
    simp_rw [Finset.sum_insert hj]
    exact add (hu j (Finset.mem_insert_self _ _))
      (ih fun i hi ↦ hu i (Finset.mem_insert_of_mem hi))

end PolyBdd

/-- Invariance transports points. -/
def Over.transport {χ χ' : A →ₐ[ℂ] ℂ} (h : χ = χ') (ψ : Over B χ) : Over B χ' := h ▸ ψ

theorem Over.transport_coe {χ χ' : A →ₐ[ℂ] ℂ} (h : χ = χ') (ψ : Over B χ) :
    ⇑(ψ.transport h).1 = ⇑ψ.1 := by subst h; rfl

theorem IsLift.smul {Γ : Subgroup SL(2, ℝ)} (hΓ : ∀ γ ∈ Γ, ∀ a τ, ι₀ a (γ • τ) = ι₀ a τ)
    {ι : ℍ → B → ℂ} (h : IsLift ι₀ ι) {γ : SL(2, ℝ)} (hγ : γ ∈ Γ) :
    IsLift ι₀ fun τ ↦ ι (γ • τ) := by
  refine ⟨fun τ ↦ ?_, fun b ↦ (h.cont b).comp (continuous_const_smul γ)⟩
  obtain ⟨ψ, hψ⟩ := h.pt (γ • τ)
  have hpt : FEt.pt ι₀ (γ • τ) = FEt.pt ι₀ τ := AlgHom.ext fun a ↦ hΓ γ hγ a τ
  exact ⟨ψ.transport hpt, by rw [Over.transport_coe, hψ]⟩

/-- A lift of an injective `ι₀` to a domain integral over `A` is injective. -/
theorem IsLift.eq_zero [IsDomain B] [Algebra.IsIntegral A B] (hinj : Function.Injective ι₀)
    {ι : ℍ → B → ℂ} (h : IsLift ι₀ ι) {b : B} (hb : ∀ τ, ι τ b = 0) : b = 0 := by
  classical
  by_contra hb0
  haveI : Nontrivial A := ⟨⟨1, 0, fun h ↦ by
    have := congrFun (congrArg ι₀ h) UpperHalfPlane.I; simp at this⟩⟩
  have hint : IsIntegral A b := Algebra.IsIntegral.isIntegral b
  have hGm : (minpoly A b).Monic := minpoly.monic hint
  have hG : aeval b (minpoly A b) = 0 := minpoly.aeval A b
  have hG0 : (minpoly A b).coeff 0 ≠ 0 := by
    intro h0
    obtain ⟨H, hH⟩ := X_dvd_iff.mpr h0
    have hHm : H.Monic := Monic.of_mul_monic_left monic_X (hH ▸ hGm)
    have hHb : aeval b H = 0 := by
      rw [hH, map_mul, aeval_X] at hG
      exact (mul_eq_zero.mp hG).resolve_left hb0
    have hmin := minpoly.min A b hHm hHb
    rw [hH, mul_comm, degree_mul_X, degree_eq_natDegree hHm.ne_zero] at hmin
    have : ((H.natDegree + 1 : ℕ) : WithBot ℕ) ≤ (H.natDegree : WithBot ℕ) := by
      push_cast; exact hmin
    norm_cast at this
    omega
  apply hG0
  apply hinj
  funext τ
  obtain ⟨ψ, hψ⟩ := h.pt τ
  have hdec := divX_mul_X_add (minpoly A b)
  have h1 : aeval b (minpoly A b) = aeval b (divX (minpoly A b)) * b +
      algebraMap A B ((minpoly A b).coeff 0) := by
    conv_lhs => rw [← hdec]
    simp [map_add, map_mul]
  rw [hG] at h1
  have h2 := congrArg ψ.1 h1
  rw [map_zero, map_add, map_mul, ψ.2, hψ, hb τ, mul_zero, zero_add, pt_apply] at h2
  rw [← h2]
  simp

/-- Cauchy's bound for a root of a monic polynomial. -/
theorem norm_le_of_isRoot_monic {p : ℂ[X]} (hp : p.Monic) {r : ℂ} (hr : p.IsRoot r) :
    ‖r‖ ≤ 1 + ∑ i ∈ Finset.range p.natDegree, ‖p.coeff i‖ := by
  have h := hr.norm_lt_cauchyBound hp.ne_zero
  have hc : cauchyBound p ≤ (∑ i ∈ Finset.range p.natDegree, ‖p.coeff i‖₊) + 1 := by
    rw [cauchyBound, hp.leadingCoeff, nnnorm_one, div_one]
    gcongr
    exact Finset.sup_le fun i hi ↦
      Finset.single_le_sum (f := fun i ↦ ‖p.coeff i‖₊) (fun _ _ ↦ zero_le) hi
  have h2 : (‖r‖₊ : ℝ) ≤ ((∑ i ∈ Finset.range p.natDegree, ‖p.coeff i‖₊) + 1 : NNReal) :=
    NNReal.coe_le_coe.mpr (h.le.trans hc)
  push_cast at h2
  linarith

variable [IsDomain B] [Algebra.IsIntegral A B]

/-- **Transitivity**: every lift is a `Γ`-translate of a given holomorphic lift. -/
theorem exists_smul_eq (hhol : ∀ a, Unif.HolH (ι₀ a)) {n : ℕ}
    (hcount : ∀ τ, Nat.card (Over B (FEt.pt ι₀ τ)) = n) (hloc : ∀ τ, LocPres ι₀ (B := B) n τ)
    {Γ : Subgroup SL(2, ℝ)} (hΓ : ∀ γ ∈ Γ, ∀ a τ, ι₀ a (γ • τ) = ι₀ a τ) {h₀ : ℍ → ℂ}
    (hgrowth : ∀ a, PolyBdd h₀ fun τ ↦ ‖ι₀ a τ‖)
    (hpoly : ∀ g : ℍ → ℂ, Unif.HolH g → (∀ γ ∈ Γ, ∀ τ, g (γ • τ) = g τ) →
      PolyBdd h₀ (fun τ ↦ ‖g τ‖) → ∃ a, ∀ τ, ι₀ a τ = g τ)
    (hinj : Function.Injective ι₀) {ι ι' : ℍ → B → ℂ} (hι : IsLift ι₀ ι)
    (hιh : ∀ b, Unif.HolH fun τ ↦ ι τ b) (hι' : IsLift ι₀ ι') :
    ∃ γ ∈ Γ, ι' = fun τ ↦ ι (γ • τ) := by
  classical
  haveI : Nontrivial A := ⟨⟨1, 0, fun h ↦ by
    have := congrFun (congrArg ι₀ h) UpperHalfPlane.I; simp at this⟩⟩
  have hcov := isCoveringMap_proj hhol hcount hloc
  set τ₀ := UpperHalfPlane.I
  obtain ⟨b₀, F, δ, hFm, hFn, hF, hδ, hpres⟩ := hloc τ₀
  -- the orbit
  set O : Set (ℍ → B → ℂ) := {f | ∃ γ ∈ Γ, f = fun τ ↦ ι (γ • τ)}
  have hOlift : ∀ f ∈ O, IsLift ι₀ f := by
    rintro f ⟨γ, hγ, rfl⟩; exact hι.smul hΓ hγ
  have hOhol : ∀ f ∈ O, ∀ b, Unif.HolH fun τ ↦ f τ b := by
    rintro f ⟨γ, hγ, rfl⟩ b; exact (hιh b).comp_smul γ
  have hιO : ι ∈ O := ⟨1, Γ.one_mem, by simp⟩
  -- the points over `τ₀`
  have hOverinj : Function.Injective fun ψ : Over B (FEt.pt ι₀ τ₀) ↦ ψ.1 b₀ :=
    fun ψ ψ' h ↦ Over.ext_of_apply_eq hδ hpres h
  haveI hOverfin : Finite (Over B (FEt.pt ι₀ τ₀)) := by
    have hmaps : ∀ ψ : Over B (FEt.pt ι₀ τ₀),
        ψ.1 b₀ ∈ (F.map (FEt.pt ι₀ τ₀ : A →+* ℂ)).roots.toFinset := fun ψ ↦ by
      rw [Multiset.mem_toFinset, mem_roots ((hFm.map _).ne_zero)]; exact ψ.isRoot hF
    exact Finite.of_injective (fun ψ ↦ (⟨ψ.1 b₀, hmaps ψ⟩ :
      (F.map (FEt.pt ι₀ τ₀ : A →+* ℂ)).roots.toFinset))
      fun ψ ψ' h ↦ hOverinj (congrArg Subtype.val h)
  -- the orbit is finite
  choose ψf hψf using fun f : {f // f ∈ O} ↦ (hOlift f.1 f.2).pt τ₀
  have hψfinj : Function.Injective ψf := fun f g h ↦ Subtype.ext
    ((hOlift f.1 f.2).eq hcov (hOlift g.1 g.2) (by rw [← hψf, ← hψf, h]))
  haveI : Finite {f // f ∈ O} := Finite.of_injective ψf hψfinj
  have hOfin : O.Finite := Set.toFinite O
  set S := hOfin.toFinset
  have hS : ∀ f, f ∈ S ↔ f ∈ O := fun f ↦ Set.Finite.mem_toFinset hOfin
  set m := S.card
  -- the polynomial
  set P : ℍ → ℂ[X] := fun τ ↦ ∏ f ∈ S, (X - C (f τ b₀))
  have hPinv : ∀ γ ∈ Γ, ∀ τ, P (γ • τ) = P τ := by
    intro γ hγ τ
    refine Finset.prod_nbij' (fun f τ ↦ f (γ • τ)) (fun f τ ↦ f (γ⁻¹ • τ)) ?_ ?_ ?_ ?_ ?_
    · intro f hf
      obtain ⟨γ', hγ', rfl⟩ := (hS f).mp hf
      exact (hS _).mpr ⟨γ' * γ, Γ.mul_mem hγ' hγ, by funext τ; simp [mul_smul]⟩
    · intro f hf
      obtain ⟨γ', hγ', rfl⟩ := (hS f).mp hf
      exact (hS _).mpr ⟨γ' * γ⁻¹, Γ.mul_mem hγ' (Γ.inv_mem hγ), by funext τ; simp [mul_smul]⟩
    · intro f _; funext τ; simp
    · intro f _; funext τ; simp
    · intro f _; rfl
  have hPm : ∀ τ, (P τ).Monic := fun τ ↦ monic_prod_X_sub_C _ _
  have hPdeg : ∀ τ, (P τ).natDegree = m := fun τ ↦ natDegree_finsetProd_X_sub_C_eq_card _ _
  -- the root bound
  set R : ℍ → ℝ := fun τ ↦ 1 + ∑ i ∈ Finset.range n, ‖ι₀ (F.coeff i) τ‖
  have hR : PolyBdd h₀ R := (PolyBdd.const 1).add (PolyBdd.sum _ fun i _ ↦ hgrowth _)
  have hfR : ∀ f ∈ S, ∀ τ, ‖f τ b₀‖ ≤ R τ := by
    intro f hf τ
    obtain ⟨ψ, hψ⟩ := (hOlift f ((hS f).mp hf)).pt τ
    have := norm_le_of_isRoot_monic (hFm.map (FEt.pt ι₀ τ : A →+* ℂ)) (ψ.isRoot hF)
    rw [(hFm.natDegree_map _), hFn] at this
    simp only [coeff_map, RingHom.coe_coe, pt_apply] at this
    rw [← hψ]; exact this
  -- the coefficients lie in `ι₀(A)`
  have hcoeff : ∀ k, ∃ a : A, ∀ τ, ι₀ a τ = (P τ).coeff k := by
    intro k
    refine hpoly _ ?_ (fun γ hγ τ ↦ by rw [hPinv γ hγ τ]) ?_
    · exact differentiableOn_coeff_prod_X_sub_C S (a := fun f z ↦ f (ofComplex z) b₀)
        (fun f hf ↦ hOhol f ((hS f).mp hf) b₀) k
    · refine (PolyBdd.prod S (u := fun _ τ ↦ 1 + R τ) (fun _ _ ↦ (PolyBdd.const 1).add hR)
        fun _ _ τ ↦ by positivity).mono fun τ ↦ ?_
      refine (norm_coeff_prod_X_sub_C_le _ _ k).trans ?_
      exact Finset.prod_le_prod (fun _ _ ↦ by positivity) fun f hf ↦ by linarith [hfR f hf τ]
  choose a ha using hcoeff
  set Q : A[X] := X ^ m + ∑ i : Fin m, C (a i) * X ^ (i : ℕ)
  have hQm : Q.Monic := monic_X_pow_add (degree_sum_fin_lt _)
  have hQmap : ∀ τ, Q.map (FEt.pt ι₀ τ : A →+* ℂ) = P τ := by
    intro τ
    conv_rhs => rw [(hPm τ).as_sum, hPdeg τ, Finset.sum_range]
    simp only [Q, Polynomial.map_add, Polynomial.map_pow, map_X, Polynomial.map_sum,
      Polynomial.map_mul, map_C, RingHom.coe_coe, pt_apply, ha]
  have hQb : aeval b₀ Q = 0 := by
    refine hι.eq_zero hinj fun τ ↦ ?_
    obtain ⟨ψ, hψ⟩ := hι.pt τ
    rw [← hψ, Over.apply_aeval, hQmap]
    simp only [P, eval_prod, eval_sub, eval_X, eval_C]
    exact Finset.prod_eq_zero ((hS ι).mpr hιO) (by rw [hψ, sub_self])
  -- counting at `τ₀`
  have hnm : n ≤ m := by
    have hroots : ∀ ψ : Over B (FEt.pt ι₀ τ₀),
        ψ.1 b₀ ∈ (Q.map (FEt.pt ι₀ τ₀ : A →+* ℂ)).roots.toFinset := fun ψ ↦ by
      rw [Multiset.mem_toFinset, mem_roots ((hQm.map _).ne_zero), IsRoot, ← Over.apply_aeval,
        hQb, map_zero]
    have h1 := Nat.card_le_card_of_injective (fun ψ : Over B (FEt.pt ι₀ τ₀) ↦
      (⟨ψ.1 b₀, hroots ψ⟩ : (Q.map (FEt.pt ι₀ τ₀ : A →+* ℂ)).roots.toFinset))
      fun ψ ψ' h ↦ hOverinj (congrArg Subtype.val h)
    rw [hcount, Nat.card_eq_fintype_card, Fintype.card_coe] at h1
    calc n ≤ _ := h1
      _ ≤ Multiset.card (Q.map (FEt.pt ι₀ τ₀ : A →+* ℂ)).roots := Multiset.toFinset_card_le _
      _ ≤ (Q.map (FEt.pt ι₀ τ₀ : A →+* ℂ)).natDegree := card_roots' _
      _ = m := by
        rw [hQm.natDegree_map]
        change (X ^ m + ∑ i : Fin m, C (a i) * X ^ (i : ℕ)).natDegree = m
        rw [natDegree_add_eq_left_of_degree_lt, natDegree_X_pow]
        exact (degree_sum_fin_lt _).trans_eq (degree_X_pow m).symm
  have hmO : m = Nat.card {f // f ∈ O} := by
    rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card O hOfin]
  have hbij := hψfinj.bijective_of_nat_card_le (by rw [hcount, ← hmO]; exact hnm)
  obtain ⟨ψ', hψ'⟩ := hι'.pt τ₀
  obtain ⟨f, hf⟩ := hbij.2 ψ'
  have hfeq : f.1 = ι' := (hOlift f.1 f.2).eq hcov hι' (by rw [← hψf, hf, hψ'])
  obtain ⟨γ, hγ, hfγ⟩ := f.2
  exact ⟨γ, hγ, hfeq.symm.trans hfγ⟩

end FEt

end Uniformization
