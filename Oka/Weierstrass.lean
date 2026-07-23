/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.OkaRing
import Oka.LocalOkaRing
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.RingTheory.PowerSeries.WeierstrassPreparation
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.MvPowerSeries.Inverse
/-!
# The Weierstrass preparation theorem

We state the Weierstrass preparation theorem: a holomorphic function on a neighbourhood of the
origin in `ℂ^{n+1}` which does not vanish identically on the last coordinate axis factors, near
the origin, as a unit times a Weierstrass polynomial.

## Main definitions

- `IsWeierstrassPolynomial`: a monic polynomial whose lower coefficients vanish at the origin.
-/

open Finsupp in
theorem MvPowerSeries.mem_span_X_of_constantCoeff_eq_zero
    {σ : Type*} [Finite σ] [LinearOrder σ] {φ : MvPowerSeries σ ℂ}
    (hφ : MvPowerSeries.constantCoeff φ = 0) :
    φ ∈ Ideal.span (Set.range (X : σ → MvPowerSeries σ ℂ)) := by
  classical
  haveI := Fintype.ofFinite σ
  rw [Ideal.mem_span_range_iff_exists_fun]
  set g : σ → MvPowerSeries σ ℂ :=
    fun i ↦ (fun e ↦ if ∀ j, j < i → e j = 0 then coeff (e + single i 1) φ else 0) with hg
  refine ⟨g, ?_⟩
  ext d
  rw [map_sum]
  have key : ∀ i : σ, coeff d (g i * X i)
      = if single i 1 ≤ d then (if ∀ j, j < i → d j = 0 then coeff d φ else 0) else 0 := by
    intro i
    rw [X_def, coeff_mul_monomial, mul_one]
    by_cases hle : single i 1 ≤ d
    · rw [if_pos hle, if_pos hle, hg, MvPowerSeries.coeff_apply]
      dsimp only
      rw [tsub_add_cancel_of_le hle]
      refine if_congr (forall_congr' fun j ↦ imp_congr_right fun hj ↦ ?_) rfl rfl
      simp [Finsupp.tsub_apply, ne_of_gt hj]
    · rw [if_neg hle, if_neg hle]
  rw [Finset.sum_congr rfl fun i _ ↦ key i]
  simp_rw [← ite_and]
  by_cases hd : d = 0
  · subst hd
    rw [coeff_zero_eq_constantCoeff, hφ]
    refine Finset.sum_eq_zero fun i _ ↦ if_neg fun h ↦ ?_
    have h1 := Finsupp.single_le_iff.mp h.1
    simp only [Finsupp.coe_zero, Pi.zero_apply] at h1
    omega
  · have hne : d.support.Nonempty := Finsupp.support_nonempty_iff.mpr hd
    have hmem : d.support.min' hne ∈ d.support := Finset.min'_mem _ hne
    have hpos : 1 ≤ d (d.support.min' hne) :=
      Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hmem)
    rw [Finset.sum_eq_single (d.support.min' hne)]
    · have hcond : single (d.support.min' hne) 1 ≤ d ∧
          (∀ j, j < d.support.min' hne → d j = 0) := by
        refine ⟨Finsupp.single_le_iff.mpr hpos, fun j hj ↦ ?_⟩
        by_contra hdj
        exact absurd (Finset.min'_le _ j (Finsupp.mem_support_iff.mpr hdj)) (not_le.mpr hj)
      rw [if_pos hcond]
    · intro i _ hi
      refine if_neg fun h ↦ ?_
      have hisupp : i ∈ d.support :=
        Finsupp.mem_support_iff.mpr (by have := Finsupp.single_le_iff.mp h.1; omega)
      have hlt : d.support.min' hne < i :=
        lt_of_le_of_ne (Finset.min'_le _ i hisupp) (Ne.symm hi)
      exact absurd (h.2 _ hlt) (Nat.one_le_iff_ne_zero.mp hpos)
    · intro h; exact absurd (Finset.mem_univ _) h

open MvPowerSeries in
theorem MvPowerSeries.maximalIdeal_eq_span_X {σ : Type*} [Finite σ] [LinearOrder σ] :
    IsLocalRing.maximalIdeal (MvPowerSeries σ ℂ)
      = Ideal.span (Set.range (X : σ → MvPowerSeries σ ℂ)) := by
  apply le_antisymm
  · intro x hx
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx
    refine mem_span_X_of_constantCoeff_eq_zero ?_
    by_contra hc
    exact hx (isUnit_iff_constantCoeff.mpr (isUnit_iff_ne_zero.mpr hc))
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have h0 := isUnit_iff_constantCoeff.mp hu
    rw [constantCoeff_X] at h0
    exact not_isUnit_zero h0

instance instIsAdicCompleteMaximalIdealMvPowerSeries
    {σ : Type*} [Finite σ] [LinearOrder σ] :
    IsAdicComplete (IsLocalRing.maximalIdeal (MvPowerSeries σ ℂ)) (MvPowerSeries σ ℂ) := by
  rw [MvPowerSeries.maximalIdeal_eq_span_X]
  infer_instance

open Polynomial in
theorem exists_diffQuotient
    {R : Type*} [CommRing R] [Nontrivial R]
    (q : R[X]) (hq : q ≠ 0) (c : R) :
    ∃ Q : R[X], Q.degree < q.degree ∧ q - C (q.eval c) = (X - C c) * Q := by
  refine ⟨q /ₘ (X - C c), ?_, ?_⟩
  · refine degree_divByMonic_lt q (X - C c) hq ?_
    rw [degree_X_sub_C]
    exact_mod_cast Nat.zero_lt_one
  · have h := modByMonic_add_div q (X - C c)
    rw [modByMonic_X_sub_C_eq_C_eval] at h
    exact (eq_sub_of_add_eq' h).symm

namespace MvPowerSeries
section Curry

variable {σ τ R : Type*} [CommSemiring R]

noncomputable def curry (f : MvPowerSeries (σ ⊕ τ) R) : MvPowerSeries σ (MvPowerSeries τ R) :=
  fun dσ dτ ↦ coeff (Finsupp.sumFinsuppEquivProdFinsupp.symm (dσ, dτ)) f

noncomputable def uncurry (g : MvPowerSeries σ (MvPowerSeries τ R)) : MvPowerSeries (σ ⊕ τ) R :=
  fun d ↦ coeff (Finsupp.sumFinsuppEquivProdFinsupp d).2
              (coeff (Finsupp.sumFinsuppEquivProdFinsupp d).1 g)

@[simp] lemma coeff_curry (f : MvPowerSeries (σ ⊕ τ) R) (dσ : σ →₀ ℕ) (dτ : τ →₀ ℕ) :
    coeff dτ (coeff dσ (curry f)) =
      coeff (Finsupp.sumFinsuppEquivProdFinsupp.symm (dσ, dτ)) f := rfl

@[simp] lemma coeff_uncurry (g : MvPowerSeries σ (MvPowerSeries τ R)) (d : σ ⊕ τ →₀ ℕ) :
    coeff d (uncurry g) =
      coeff (Finsupp.sumFinsuppEquivProdFinsupp d).2
        (coeff (Finsupp.sumFinsuppEquivProdFinsupp d).1 g) := rfl

lemma uncurry_curry (f : MvPowerSeries (σ ⊕ τ) R) : uncurry (curry f) = f := by
  ext d
  rw [coeff_uncurry, coeff_curry, Prod.mk.eta, Equiv.symm_apply_apply]

lemma curry_uncurry (g : MvPowerSeries σ (MvPowerSeries τ R)) : curry (uncurry g) = g := by
  ext dσ dτ
  rw [coeff_curry, coeff_uncurry, Equiv.apply_symm_apply]

@[simp] lemma curry_add (f g : MvPowerSeries (σ ⊕ τ) R) :
    curry (f + g) = curry f + curry g := by
  ext dσ dτ
  simp [map_add]

@[simp] lemma curry_zero : curry (0 : MvPowerSeries (σ ⊕ τ) R) = 0 := by
  ext dσ dτ
  simp

lemma curry_one : curry (1 : MvPowerSeries (σ ⊕ τ) R) = 1 := by
  classical
  have he0 : Finsupp.sumFinsuppEquivProdFinsupp (0 : σ ⊕ τ →₀ ℕ) = (0, 0) := by
    apply Prod.ext <;> ext x <;> simp
  ext dσ dτ
  rw [coeff_curry, coeff_one]
  have key : (Finsupp.sumFinsuppEquivProdFinsupp.symm (dσ, dτ) = (0 : σ ⊕ τ →₀ ℕ))
      ↔ (dσ = 0 ∧ dτ = 0) := by
    rw [Equiv.symm_apply_eq, he0, Prod.mk.injEq]
  simp only [key]
  by_cases h : dσ = 0 ∧ dτ = 0
  · obtain ⟨h1, h2⟩ := h; subst h1; subst h2; simp
  · rw [if_neg h]
    rcases not_and_or.mp h with h' | h'
    · simp [coeff_one, if_neg h']
    · by_cases hσ : dσ = 0
      · subst hσ; simp [coeff_one, if_neg h']
      · simp [coeff_one, if_neg hσ]

lemma symm_prod_eq_sumElim (a : σ →₀ ℕ) (b : τ →₀ ℕ) :
    Finsupp.sumFinsuppEquivProdFinsupp.symm (a, b) = Finsupp.sumElim a b := by
  ext x
  cases x with
  | inl x => simp
  | inr x => simp

lemma curry_mul (f g : MvPowerSeries (σ ⊕ τ) R) : curry (f * g) = curry f * curry g := by
  classical
  ext dσ dτ
  have hL : coeff dτ (coeff dσ (curry (f * g)))
      = ∑ q ∈ (Finset.antidiagonal dσ) ×ˢ (Finset.antidiagonal dτ),
          coeff (Finsupp.sumElim q.1.1 q.2.1) f * coeff (Finsupp.sumElim q.1.2 q.2.2) g := by
    rw [coeff_curry, symm_prod_eq_sumElim, coeff_mul,
      ← Finsupp.image_sumElim_product_antidiagonal,
      Finset.sum_image (by
        rintro ⟨⟨x, y⟩, z, w⟩ _ ⟨⟨x', y'⟩, z', w'⟩ _ hEq
        simp only [Prod.mk.injEq] at hEq
        obtain ⟨h1, h2⟩ := hEq
        have hx : x = x' := by ext a; simpa using DFunLike.congr_fun h1 (Sum.inl a)
        have hz : z = z' := by ext a; simpa using DFunLike.congr_fun h1 (Sum.inr a)
        have hy : y = y' := by ext a; simpa using DFunLike.congr_fun h2 (Sum.inl a)
        have hw : w = w' := by ext a; simpa using DFunLike.congr_fun h2 (Sum.inr a)
        subst hx; subst hy; subst hz; subst hw; rfl)]
  have hR : coeff dτ (coeff dσ (curry f * curry g))
      = ∑ q ∈ (Finset.antidiagonal dσ) ×ˢ (Finset.antidiagonal dτ),
          coeff (Finsupp.sumElim q.1.1 q.2.1) f * coeff (Finsupp.sumElim q.1.2 q.2.2) g := by
    rw [coeff_mul, map_sum, Finset.sum_product]
    refine Finset.sum_congr rfl fun pσ _ ↦ ?_
    rw [coeff_mul]
    refine Finset.sum_congr rfl fun pτ _ ↦ ?_
    rw [coeff_curry, coeff_curry, symm_prod_eq_sumElim, symm_prod_eq_sumElim]
  rw [hL, hR]

noncomputable def curryEquiv : MvPowerSeries (σ ⊕ τ) R ≃+* MvPowerSeries σ (MvPowerSeries τ R) where
  toFun := curry
  invFun := uncurry
  left_inv := uncurry_curry
  right_inv := curry_uncurry
  map_add' := curry_add
  map_mul' := curry_mul

def finLastEquivSum (n : ℕ) : Fin (n + 1) ≃ Unit ⊕ Fin n where
  toFun i := Fin.lastCases (Sum.inl ()) Sum.inr i
  invFun x := Sum.elim (fun _ ↦ Fin.last n) Fin.castSucc x
  left_inv i := by
    induction i using Fin.lastCases with
    | last => simp
    | cast j => simp
  right_inv x := by
    cases x with
    | inl u => simp
    | inr j => simp

noncomputable def finSuccRingEquiv (n : ℕ) :
    MvPowerSeries (Fin (n + 1)) ℂ ≃+* PowerSeries (MvPowerSeries (Fin n) ℂ) :=
  (MvPowerSeries.renameEquiv (R := ℂ) (finLastEquivSum n)).toRingEquiv.trans
    (curryEquiv (σ := Unit) (τ := Fin n) (R := ℂ))

end Curry
end MvPowerSeries

namespace MvPowerSeries

lemma summableAt_X {ι : Type*} (i : ι) (x : ι → ℂ) :
    (X i : MvPowerSeries ι ℂ).SummableAt x := by
  classical
  refine summable_of_ne_finset_zero (s := {Finsupp.single i 1}) fun d hd ↦ ?_
  rw [Finset.mem_singleton] at hd
  rw [term, coeff_X, if_neg hd, zero_mul, norm_zero]

lemma locallyConvergent_X {ι : Type*} (i : ι) :
    (X i : MvPowerSeries ι ℂ).LocallyConvergent :=
  .of_forall fun x ↦ summableAt_X i x

lemma eval_X {ι : Type*} (i : ι) (x : ι → ℂ) :
    (X i : MvPowerSeries ι ℂ).eval x = x i := by
  classical
  rw [eval, tsum_eq_single (Finsupp.single i 1) ?_]
  · rw [term, coeff_X, if_pos rfl, one_mul, evalMonomial, Finsupp.prod_single_index] <;> simp
  · intro d hd
    rw [term, coeff_X, if_neg hd, zero_mul]

lemma eval_add_of_summableAt {ι : Type*} {P Q : MvPowerSeries ι ℂ} {x : ι → ℂ}
    (hP : P.SummableAt x) (hQ : Q.SummableAt x) :
    (P + Q).eval x = P.eval x + Q.eval x := by
  have hfun : (P + Q).term x = fun d ↦ P.term x d + Q.term x d :=
    funext fun d ↦ term_add P Q x d
  refine (hP.add hQ).hasSum.unique ?_
  rw [hfun]
  exact hP.hasSum.add hQ.hasSum

lemma eval_mul_of_summableAt {ι : Type*} {P Q : MvPowerSeries ι ℂ} {x : ι → ℂ}
    (hP : P.SummableAt x) (hQ : Q.SummableAt x) :
    (P * Q).eval x = P.eval x * Q.eval x := by
  classical
  have hFsum : Summable fun p : (ι →₀ ℕ) × (ι →₀ ℕ) ↦ P.term x p.1 * Q.term x p.2 := by
    refine Summable.of_norm ?_
    simpa [norm_mul] using
      Summable.mul_of_nonneg hP hQ (fun _ ↦ norm_nonneg _) (fun _ ↦ norm_nonneg _)
  have hF : HasSum (fun p : (ι →₀ ℕ) × (ι →₀ ℕ) ↦ P.term x p.1 * Q.term x p.2)
      (P.eval x * Q.eval x) := hP.hasSum.mul hQ.hasSum hFsum
  have hσ := (antidiagonalSigmaEquiv ι).hasSum_iff.mpr hF
  have hfib : ∀ d : ι →₀ ℕ,
      HasSum (fun c : {p : (ι →₀ ℕ) × (ι →₀ ℕ) //
          p ∈ Finset.HasAntidiagonal.antidiagonal d} ↦ P.term x c.1.1 * Q.term x c.1.2)
        ((P * Q).term x d) := by
    intro d
    rw [term_mul, ← Finset.sum_attach (Finset.HasAntidiagonal.antidiagonal d)
      (fun p ↦ P.term x p.1 * Q.term x p.2)]
    exact hasSum_fintype _
  exact ((hσ.sigma hfib).unique (hP.mul hQ).hasSum).symm

lemma summableAt_zero {ι : Type*} (x : ι → ℂ) : (0 : MvPowerSeries ι ℂ).SummableAt x := by
  simpa using summableAt_algebraMap 0 x

lemma summableAt_one {ι : Type*} (x : ι → ℂ) : (1 : MvPowerSeries ι ℂ).SummableAt x := by
  simpa using summableAt_algebraMap 1 x

lemma eval_algebraMap {ι : Type*} (c : ℂ) (x : ι → ℂ) :
    (algebraMap ℂ (MvPowerSeries ι ℂ) c).eval x = c := by
  classical
  rw [eval, tsum_eq_single 0 (fun d hd ↦ term_algebraMap_of_ne_zero c x hd),
    term_algebraMap_zero]

lemma eval_of_zero {ι : Type*} (x : ι → ℂ) : (0 : MvPowerSeries ι ℂ).eval x = 0 := by
  simpa using eval_algebraMap 0 x

lemma eval_one {ι : Type*} (x : ι → ℂ) : (1 : MvPowerSeries ι ℂ).eval x = 1 := by
  simpa using eval_algebraMap 1 x

lemma SummableAt.sum {ι κ : Type*} {x : ι → ℂ} {s : Finset κ} {P : κ → MvPowerSeries ι ℂ} :
    (∀ k ∈ s, (P k).SummableAt x) → (∑ k ∈ s, P k).SummableAt x := by
  classical
  induction s using Finset.induction with
  | empty => intro _; simpa using summableAt_zero x
  | insert k s hk ih =>
      intro h
      rw [Finset.sum_insert hk]
      exact (h k (by simp)).add (ih fun j hj ↦ h j (Finset.mem_insert_of_mem hj))

lemma eval_sum_of_summableAt {ι κ : Type*} {x : ι → ℂ} {s : Finset κ}
    {P : κ → MvPowerSeries ι ℂ} :
    (∀ k ∈ s, (P k).SummableAt x) → (∑ k ∈ s, P k).eval x = ∑ k ∈ s, (P k).eval x := by
  classical
  induction s using Finset.induction with
  | empty => intro _; simp [eval_of_zero]
  | insert k s hk ih =>
      intro h
      have hs : ∀ j ∈ s, (P j).SummableAt x := fun j hj ↦ h j (Finset.mem_insert_of_mem hj)
      rw [Finset.sum_insert hk, Finset.sum_insert hk,
        eval_add_of_summableAt (h k (by simp)) (SummableAt.sum hs), ih hs]

lemma SummableAt.pow {ι : Type*} {P : MvPowerSeries ι ℂ} {x : ι → ℂ} (h : P.SummableAt x) :
    ∀ m : ℕ, (P ^ m).SummableAt x
  | 0 => by simpa using summableAt_one x
  | m + 1 => by rw [pow_succ]; exact (SummableAt.pow h m).mul h

lemma eval_pow_of_summableAt {ι : Type*} {P : MvPowerSeries ι ℂ} {x : ι → ℂ}
    (h : P.SummableAt x) :
    ∀ m : ℕ, (P ^ m).eval x = P.eval x ^ m
  | 0 => by simpa using eval_one x
  | m + 1 => by
      rw [pow_succ, pow_succ, eval_mul_of_summableAt (h.pow m) h, eval_pow_of_summableAt h m]

lemma summableAt_zero_pt {ι : Type*} (P : MvPowerSeries ι ℂ) :
    P.SummableAt (0 : ι → ℂ) := by
  classical
  refine summable_of_ne_finset_zero (s := {0}) fun d hd ↦ ?_
  rw [Finset.mem_singleton] at hd
  rw [term, evalMonomial_eq_zero hd, mul_zero, norm_zero]

end MvPowerSeries

variable {n : ℕ}

noncomputable def LocalOkaRing.lastVar : LocalOkaRing (Fin (n + 1)) :=
  ⟨MvPowerSeries.X (Fin.last n), MvPowerSeries.locallyConvergent_X _⟩

namespace MvPowerSeries
open Filter Topology

variable {σ τ : Type*}

lemma evalMonomial_mapDomain (e : σ ↪ τ) (d : σ →₀ ℕ) (x : τ → ℂ) :
    evalMonomial (Finsupp.mapDomain e d) x = evalMonomial d (x ∘ e) :=
  Finsupp.prod_mapDomain_index_inj e.injective

lemma term_rename (e : σ ↪ τ) [TendstoCofinite (e : σ → τ)]
    (P : MvPowerSeries σ ℂ) (x : τ → ℂ) (d : σ →₀ ℕ) :
    (rename (e : σ → τ) P).term x (Finsupp.mapDomain e d) = P.term (x ∘ e) d := by
  rw [term, term, ← Finsupp.embDomain_eq_mapDomain, coeff_embDomain_rename,
    Finsupp.embDomain_eq_mapDomain, evalMonomial_mapDomain]

lemma eval_rename (e : σ ↪ τ) [TendstoCofinite (e : σ → τ)]
    (P : MvPowerSeries σ ℂ) (x : τ → ℂ) :
    (rename (e : σ → τ) P).eval x = P.eval (x ∘ e) := by
  have hzero : Function.support (fun d' ↦ (rename (e : σ → τ) P).term x d') ⊆
      Set.range (Finsupp.mapDomain (e : σ → τ)) := by
    intro d' hd'
    by_contra h
    apply hd'
    change (rename (e : σ → τ) P).term x d' = 0
    rw [term, coeff_rename_eq_zero _ _ h, zero_mul]
  rw [eval, eval, ← Function.Injective.tsum_eq
    (Finsupp.mapDomain_injective e.injective) hzero]
  exact tsum_congr fun d ↦ term_rename e P x d

lemma SummableAt.rename (e : σ ↪ τ) [TendstoCofinite (e : σ → τ)]
    {P : MvPowerSeries σ ℂ} {x : τ → ℂ} (h : P.SummableAt (x ∘ e)) :
    (rename (e : σ → τ) P).SummableAt x := by
  refine (Function.Injective.summable_iff
    (g := fun d : σ →₀ ℕ ↦ Finsupp.mapDomain (e : σ → τ) d)
    (Finsupp.mapDomain_injective e.injective) ?_).mp ?_
  · intro d' hd'
    rw [term, coeff_rename_eq_zero _ _ hd', zero_mul, norm_zero]
  · simpa [SummableAt, Function.comp_def, term_rename] using h

lemma LocallyConvergent.rename (e : σ ↪ τ) [TendstoCofinite (e : σ → τ)]
    {P : MvPowerSeries σ ℂ} (hP : P.LocallyConvergent) :
    (rename (e : σ → τ) P).LocallyConvergent := by
  have hc : Tendsto (fun x : τ → ℂ ↦ x ∘ (e : σ → τ)) (𝓝 0) (𝓝 0) :=
    (continuous_pi fun i ↦ continuous_apply (e i)).tendsto' 0 0 rfl
  filter_upwards [hc.eventually hP] with x hx using SummableAt.rename e hx

end MvPowerSeries

instance : Filter.TendstoCofinite (Fin.castSuccEmb : Fin n → Fin (n + 1)) :=
  Filter.tendstoCofinite_of_finite _

noncomputable def LocalOkaRing.incl :
    LocalOkaRing (Fin n) →ₐ[ℂ] LocalOkaRing (Fin (n + 1)) :=
  ((MvPowerSeries.rename (Fin.castSuccEmb : Fin n → Fin (n + 1))).comp
      (localOkaSubring (Fin n)).val).codRestrict _
    (fun P ↦ MvPowerSeries.LocallyConvergent.rename _ P.2)

open Polynomial TopologicalSpace

variable {n : ℕ}

/-- A local Weierstrass polynomial is a monic polynomial whose coefficients below the leading
one vanish at the origin. -/
structure IsLocalWeierstrassPolynomial
  (P : (MvPowerSeries (Fin n) ℂ)[X]) : Prop where
  monic : P.Monic
  apply_zero (i : ℕ) (hi : i < P.degree) :
  MvPowerSeries.constantCoeff (P.coeff i) = 0

noncomputable def LocalOkaRing.fromPolynomial :
    (LocalOkaRing (Fin n))[X] →ₐ[ℂ] LocalOkaRing (Fin (n + 1)) :=
  Polynomial.aevalTower LocalOkaRing.incl LocalOkaRing.lastVar

lemma LocalOkaRing.eval_incl (a : LocalOkaRing (Fin n)) (z : Fin (n + 1) → ℂ) :
    ((incl a : LocalOkaRing (Fin (n + 1))) : MvPowerSeries (Fin (n + 1)) ℂ).eval z
      = (a : MvPowerSeries (Fin n) ℂ).eval (fun j ↦ z j.castSucc) := by
  change (MvPowerSeries.rename (Fin.castSuccEmb : Fin n → Fin (n + 1))
      (a : MvPowerSeries (Fin n) ℂ)).eval z = _
  rw [MvPowerSeries.eval_rename]
  rfl

lemma LocalOkaRing.eval_lastVar (z : Fin (n + 1) → ℂ) :
    ((lastVar : LocalOkaRing (Fin (n + 1))) : MvPowerSeries (Fin (n + 1)) ℂ).eval z
      = z (Fin.last n) :=
  MvPowerSeries.eval_X _ _

lemma LocalOkaRing.fromPolynomial_eq_sum (q : (LocalOkaRing (Fin n))[X]) :
    fromPolynomial q
      = ∑ i ∈ Finset.range (q.natDegree + 1), incl (q.coeff i) * lastVar ^ i := by
  rw [fromPolynomial]
  exact Polynomial.eval₂_eq_sum_range _ _

lemma LocalOkaRing.summableAt_incl (a : LocalOkaRing (Fin n)) (z : Fin (n + 1) → ℂ)
    (ha : (a : MvPowerSeries (Fin n) ℂ).SummableAt (fun j ↦ z j.castSucc)) :
    ((incl a : LocalOkaRing (Fin (n + 1))) : MvPowerSeries (Fin (n + 1)) ℂ).SummableAt z := by
  change (MvPowerSeries.rename (Fin.castSuccEmb : Fin n → Fin (n + 1))
      (a : MvPowerSeries (Fin n) ℂ)).SummableAt z
  exact MvPowerSeries.SummableAt.rename _ ha

lemma LocalOkaRing.eval_fromPolynomial (q : (LocalOkaRing (Fin n))[X]) (z : Fin (n + 1) → ℂ)
    (hz : ∀ i, ((q.coeff i : LocalOkaRing (Fin n)) : MvPowerSeries (Fin n) ℂ).SummableAt
      (fun j ↦ z j.castSucc)) :
    ((fromPolynomial q : LocalOkaRing (Fin (n + 1))) : MvPowerSeries (Fin (n + 1)) ℂ).eval z
      = ∑ i ∈ Finset.range (q.natDegree + 1),
          ((q.coeff i : MvPowerSeries (Fin n) ℂ).eval (fun j ↦ z j.castSucc))
            * z (Fin.last n) ^ i := by
  classical
  have hX : (MvPowerSeries.X (Fin.last n) : MvPowerSeries (Fin (n + 1)) ℂ).SummableAt z :=
    MvPowerSeries.summableAt_X _ z
  have hcast : ((∑ i ∈ Finset.range (q.natDegree + 1),
        incl (q.coeff i) * lastVar ^ i : LocalOkaRing (Fin (n + 1))) :
        MvPowerSeries (Fin (n + 1)) ℂ)
      = ∑ i ∈ Finset.range (q.natDegree + 1),
          ((incl (q.coeff i) : LocalOkaRing (Fin (n + 1))) : MvPowerSeries (Fin (n + 1)) ℂ)
            * (MvPowerSeries.X (Fin.last n) : MvPowerSeries (Fin (n + 1)) ℂ) ^ i := by
    push_cast
    rfl
  have hsum : ∀ i ∈ Finset.range (q.natDegree + 1),
      (((incl (q.coeff i) : LocalOkaRing (Fin (n + 1))) : MvPowerSeries (Fin (n + 1)) ℂ)
        * (MvPowerSeries.X (Fin.last n) : MvPowerSeries (Fin (n + 1)) ℂ) ^ i).SummableAt z :=
    fun i _ ↦ (summableAt_incl _ z (hz i)).mul (hX.pow i)
  rw [fromPolynomial_eq_sum, hcast, MvPowerSeries.eval_sum_of_summableAt hsum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [MvPowerSeries.eval_mul_of_summableAt (summableAt_incl _ z (hz i)) (hX.pow i),
    MvPowerSeries.eval_pow_of_summableAt hX, eval_incl, MvPowerSeries.eval_X]

lemma LocalOkaRing.eval_fromPolynomial_axis (q : (LocalOkaRing (Fin n))[X]) (w : ℂ) :
    ((fromPolynomial q : LocalOkaRing (Fin (n + 1))) : MvPowerSeries (Fin (n + 1)) ℂ).eval
        (Fin.snoc (0 : Fin n → ℂ) w : Fin (n + 1) → ℂ)
      = ∑ i ∈ Finset.range (q.natDegree + 1),
          MvPowerSeries.constantCoeff (q.coeff i : MvPowerSeries (Fin n) ℂ) * w ^ i := by
  have hpt : (fun j : Fin n ↦ (Fin.snoc (0 : Fin n → ℂ) w : Fin (n + 1) → ℂ) j.castSucc) = 0 := by
    funext j; simp [Fin.snoc_castSucc]
  rw [eval_fromPolynomial q (Fin.snoc (0 : Fin n → ℂ) w : Fin (n + 1) → ℂ)
    (fun i ↦ by rw [hpt]; exact MvPowerSeries.summableAt_zero_pt _)]
  simp only [Fin.snoc_last]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [hpt, MvPowerSeries.eval_zero]

lemma LocalOkaRing.eval_fromPolynomial_axis_weierstrass
    (q : (LocalOkaRing (Fin n))[X])
    (hq : IsLocalWeierstrassPolynomial
      (Polynomial.map (localOkaSubring (Fin n)).val.toRingHom q)) (w : ℂ) :
    ((fromPolynomial q : LocalOkaRing (Fin (n + 1))) : MvPowerSeries (Fin (n + 1)) ℂ).eval
        (Fin.snoc (0 : Fin n → ℂ) w : Fin (n + 1) → ℂ)
      = w ^ q.natDegree := by
  classical
  have hinj : Function.Injective (localOkaSubring (Fin n)).val.toRingHom :=
    Subtype.val_injective
  set Q := Polynomial.map (localOkaSubring (Fin n)).val.toRingHom q with hQ
  have hqne : q ≠ 0 := fun h ↦ hq.monic.ne_zero (by rw [hQ, h, Polynomial.map_zero])
  have hdeg : Q.natDegree = q.natDegree := natDegree_map_eq_of_injective hinj q
  have hcoeff : ∀ i, MvPowerSeries.constantCoeff (q.coeff i : MvPowerSeries (Fin n) ℂ)
      = MvPowerSeries.constantCoeff (Q.coeff i) := fun i ↦ by rw [hQ, Polynomial.coeff_map]; rfl
  rw [eval_fromPolynomial_axis,
    Finset.sum_eq_single_of_mem q.natDegree (Finset.self_mem_range_succ q.natDegree)]
  · have hlead :
        MvPowerSeries.constantCoeff (q.coeff q.natDegree : MvPowerSeries (Fin n) ℂ) = 1 := by
      rw [hcoeff, ← hdeg, hq.monic.coeff_natDegree, map_one]
    rw [hlead, one_mul]
  · intro i hi hine
    have hilt : i < q.natDegree := by
      have := Finset.mem_range.mp hi; omega
    have hidQ : (i : WithBot ℕ) < Q.degree := by
      rw [hQ, degree_map_eq_of_injective hinj, Polynomial.degree_eq_natDegree hqne]
      exact_mod_cast hilt
    rw [hcoeff, hq.apply_zero i hidQ, zero_mul]

lemma LocalOkaRing.eventually_summableAt_coeffs (q : (LocalOkaRing (Fin n))[X]) :
    ∀ᶠ z' : Fin n → ℂ in nhds 0,
      ∀ i ∈ Finset.range (q.natDegree + 1),
        ((q.coeff i : LocalOkaRing (Fin n)) : MvPowerSeries (Fin n) ℂ).SummableAt z' := by
  rw [Filter.eventually_all_finset]
  intro i _
  exact (q.coeff i).locallyConvergent

lemma LocalOkaRing.eval_coeff_natDegree
    (q : (LocalOkaRing (Fin n))[X])
    (hq : IsLocalWeierstrassPolynomial
      (Polynomial.map (localOkaSubring (Fin n)).val.toRingHom q)) (z' : Fin n → ℂ) :
    ((q.coeff q.natDegree : LocalOkaRing (Fin n)) : MvPowerSeries (Fin n) ℂ).eval z' = 1 := by
  have hinj : Function.Injective (localOkaSubring (Fin n)).val.toRingHom :=
    Subtype.val_injective
  have hcoeff1 : q.coeff q.natDegree = 1 := by
    apply hinj
    have h1 : (Polynomial.map (localOkaSubring (Fin n)).val.toRingHom q).coeff q.natDegree = 1 := by
      rw [← natDegree_map_eq_of_injective hinj q]
      exact hq.monic.coeff_natDegree
    rw [map_one, ← Polynomial.coeff_map]
    exact h1
  rw [hcoeff1, show ((1 : LocalOkaRing (Fin n)) : MvPowerSeries (Fin n) ℂ) = 1 by simp]
  exact MvPowerSeries.eval_one z'

lemma LocalOkaRing.eventually_error_lt
    (q : (LocalOkaRing (Fin n))[X])
    (hq : IsLocalWeierstrassPolynomial
      (Polynomial.map (localOkaSubring (Fin n)).val.toRingHom q))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ z' : Fin n → ℂ in nhds 0,
      ∑ i ∈ Finset.range q.natDegree,
          ‖((q.coeff i : LocalOkaRing (Fin n)) : MvPowerSeries (Fin n) ℂ).eval z'‖ * ε ^ i
        < ε ^ q.natDegree := by
  have hinj : Function.Injective (localOkaSubring (Fin n)).val.toRingHom :=
    Subtype.val_injective
  have hqne : q ≠ 0 := fun h ↦ hq.monic.ne_zero (by rw [h, Polynomial.map_zero])
  have hci0 : ∀ i ∈ Finset.range q.natDegree,
      ((q.coeff i : LocalOkaRing (Fin n)) : MvPowerSeries (Fin n) ℂ).eval 0 = 0 := by
    intro i hi
    have hilt : i < q.natDegree := Finset.mem_range.mp hi
    have hidQ : (i : WithBot ℕ)
        < (Polynomial.map (localOkaSubring (Fin n)).val.toRingHom q).degree := by
      rw [degree_map_eq_of_injective hinj, Polynomial.degree_eq_natDegree hqne]
      exact_mod_cast hilt
    rw [MvPowerSeries.eval_zero]
    have hthis := hq.apply_zero i hidQ
    rwa [Polynomial.coeff_map] at hthis
  have htend : Filter.Tendsto
      (fun z' : Fin n → ℂ ↦ ∑ i ∈ Finset.range q.natDegree,
          ‖((q.coeff i : LocalOkaRing (Fin n)) : MvPowerSeries (Fin n) ℂ).eval z'‖ * ε ^ i)
      (nhds 0) (nhds 0) := by
    have hsum0 : (0 : ℝ) = ∑ i ∈ Finset.range q.natDegree,
        ‖((q.coeff i : LocalOkaRing (Fin n)) : MvPowerSeries (Fin n) ℂ).eval (0 : Fin n → ℂ)‖
          * ε ^ i := by
      refine (Finset.sum_eq_zero fun i hi ↦ ?_).symm
      rw [hci0 i hi, norm_zero, zero_mul]
    rw [hsum0]
    refine tendsto_finsetSum _ fun i _ ↦ ?_
    exact Filter.Tendsto.mul_const _
      ((q.coeff i).locallyConvergent.analyticAt.continuousAt.norm)
  exact htend.eventually (gt_mem_nhds (pow_pos hε _))

lemma LocalOkaRing.eventually_fromPolynomial_ne_zero
    (q : (LocalOkaRing (Fin n))[X])
    (hq : IsLocalWeierstrassPolynomial
      (Polynomial.map (localOkaSubring (Fin n)).val.toRingHom q))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ z' : Fin n → ℂ in nhds 0,
      ∀ w : ℂ, ‖w‖ = ε →
        ((fromPolynomial q : LocalOkaRing (Fin (n + 1))) : MvPowerSeries (Fin (n + 1)) ℂ).eval
            (Fin.snoc z' w : Fin (n + 1) → ℂ) ≠ 0 := by
  filter_upwards [eventually_summableAt_coeffs q, eventually_error_lt q hq hε]
    with z' hsummable herror w hw
  have hpt : (fun j : Fin n ↦ (Fin.snoc z' w : Fin (n + 1) → ℂ) j.castSucc) = z' := by
    funext j; simp [Fin.snoc_castSucc]
  have hz : ∀ i, ((q.coeff i : LocalOkaRing (Fin n)) : MvPowerSeries (Fin n) ℂ).SummableAt
      (fun j : Fin n ↦ (Fin.snoc z' w : Fin (n + 1) → ℂ) j.castSucc) := by
    intro i
    rw [hpt]
    by_cases hi : i ≤ q.natDegree
    · exact hsummable i (Finset.mem_range.mpr (by omega))
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
      simpa using MvPowerSeries.summableAt_zero z'
  have hval : ((fromPolynomial q : LocalOkaRing (Fin (n + 1))) :
        MvPowerSeries (Fin (n + 1)) ℂ).eval (Fin.snoc z' w : Fin (n + 1) → ℂ)
      = ∑ i ∈ Finset.range (q.natDegree + 1),
          ((q.coeff i : LocalOkaRing (Fin n)) : MvPowerSeries (Fin n) ℂ).eval z' * w ^ i := by
    rw [eval_fromPolynomial q (Fin.snoc z' w : Fin (n + 1) → ℂ) hz]
    simp only [Fin.snoc_last, hpt]
  set S := ((fromPolynomial q : LocalOkaRing (Fin (n + 1))) :
      MvPowerSeries (Fin (n + 1)) ℂ).eval (Fin.snoc z' w : Fin (n + 1) → ℂ) with hS
  have hSdecomp : S = w ^ q.natDegree + ∑ i ∈ Finset.range q.natDegree,
      ((q.coeff i : LocalOkaRing (Fin n)) : MvPowerSeries (Fin n) ℂ).eval z' * w ^ i := by
    rw [hval, Finset.sum_range_succ, eval_coeff_natDegree q hq z', one_mul, add_comm]
  set T := ∑ i ∈ Finset.range q.natDegree,
      ((q.coeff i : LocalOkaRing (Fin n)) : MvPowerSeries (Fin n) ℂ).eval z' * w ^ i with hT
  have hTbound : ‖T‖ ≤ ∑ i ∈ Finset.range q.natDegree,
      ‖((q.coeff i : LocalOkaRing (Fin n)) : MvPowerSeries (Fin n) ℂ).eval z'‖ * ε ^ i := by
    rw [hT]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ le_of_eq ?_)
    rw [norm_mul, norm_pow, hw]
  have hlow : (0 : ℝ) < ‖S‖ := by
    have h2 : ‖(w : ℂ) ^ q.natDegree‖ ≤ ‖S‖ + ‖T‖ := by
      have he : (w : ℂ) ^ q.natDegree = S - T := by rw [hSdecomp]; ring
      rw [he]; exact norm_sub_le S T
    have h1 : ‖(w : ℂ) ^ q.natDegree‖ = ε ^ q.natDegree := by rw [norm_pow, hw]
    have hTlt : ‖T‖ < ε ^ q.natDegree := lt_of_le_of_lt hTbound herror
    rw [h1] at h2
    linarith
  intro hzero
  rw [hzero, norm_zero] at hlow
  exact lt_irrefl 0 hlow

lemma localweierstrass_division_lemma_one
      (q : (LocalOkaRing (Fin n))[X])
      (hq : IsLocalWeierstrassPolynomial (Polynomial.map (localOkaSubring _).val.toRingHom q))
      (f : LocalOkaRing (Fin (n + 1))) :
      ∃ (δ : ℝ) (hd : δ > 0) (ε : ℝ) (he : ε > 0),
      ∀ (z : Fin (n+1) → ℂ)
          (hz₁ : ∀ i : Fin n, ‖z i.castSucc‖ ≤ δ)
          (hz₂ : ‖z (Fin.last n)‖ = ε),
          ((f : MvPowerSeries (Fin (n+1)) ℂ)).SummableAt z ∧
          ((LocalOkaRing.fromPolynomial q : LocalOkaRing (Fin (n+1))) :
            MvPowerSeries (Fin (n+1)) ℂ).eval z ≠ 0 := by
  obtain ⟨ρ, hρ, hsum⟩ := f.locallyConvergent.exists_summableAt_const
  have hne := LocalOkaRing.eventually_fromPolynomial_ne_zero q hq hρ
  rw [Metric.eventually_nhds_iff] at hne
  obtain ⟨δ₀, hδ₀, hprop⟩ := hne
  refine ⟨min (δ₀ / 2) ρ, lt_min (by linarith) hρ, ρ, hρ, ?_⟩
  intro z hz₁ hz₂
  have hzeq : (Fin.snoc (fun i : Fin n ↦ z i.castSucc) (z (Fin.last n)) : Fin (n + 1) → ℂ) = z := by
    funext k
    induction k using Fin.lastCases with
    | last => simp
    | cast j => simp
  refine ⟨?_, ?_⟩
  · refine hsum.mono ?_
    intro i
    induction i using Fin.lastCases with
    | last => simp [hz₂, Complex.norm_real, abs_of_nonneg hρ.le]
    | cast j =>
        have hle : ‖z j.castSucc‖ ≤ ρ := le_trans (hz₁ j) (min_le_right _ _)
        simpa [Complex.norm_real, abs_of_nonneg hρ.le] using hle
  · have hz'dist : dist (fun i : Fin n ↦ z i.castSucc) (0 : Fin n → ℂ) < δ₀ := by
      rw [dist_pi_lt_iff hδ₀]
      intro i
      simp only [Pi.zero_apply, dist_zero_right]
      have h2 : ‖z i.castSucc‖ ≤ δ₀ / 2 := le_trans (hz₁ i) (min_le_left _ _)
      linarith
    have hprop2 := hprop hz'dist (z (Fin.last n)) hz₂
    rwa [hzeq] at hprop2

lemma localweierstrass_division_lemma_two
    (q : (LocalOkaRing (Fin n))[X])
    (hq : IsLocalWeierstrassPolynomial (Polynomial.map (localOkaSubring _).val.toRingHom q))
    (f : LocalOkaRing (Fin (n + 1)))
    (δ : ℝ) (hd : δ > 0) (ε : ℝ) (he : ε > 0)
    (hf : ∀ z : Fin (n+1) → ℂ, (∀ i : Fin n, ‖z i.castSucc‖ ≤ δ) → ‖z (Fin.last n)‖ = ε →
      (f : MvPowerSeries (Fin (n+1)) ℂ).SummableAt z)
    (hq0 : ∀ z : Fin (n+1) → ℂ, (∀ i : Fin n, ‖z i.castSucc‖ ≤ δ) → ‖z (Fin.last n)‖ = ε →
      ((LocalOkaRing.fromPolynomial q : LocalOkaRing (Fin (n+1))) :
        MvPowerSeries (Fin (n+1)) ℂ).eval z ≠ 0) :
      ∃ a : LocalOkaRing (Fin (n+1)),
       (a : MvPowerSeries (Fin (n+1)) ℂ).Represents (fun x =>
            (2 * Real.pi * Complex.I : ℂ)⁻¹ *
              ∮ ζ in C(0, ε),
                (f : MvPowerSeries (Fin (n+1)) ℂ).eval (Fin.snoc (Fin.init x) ζ) /
                  (((LocalOkaRing.fromPolynomial q : LocalOkaRing (Fin (n+1))) :
                      MvPowerSeries (Fin (n+1)) ℂ).eval (Fin.snoc (Fin.init x) ζ)
                    * (ζ - x (Fin.last n)))) := by
  have hF : AnalyticAt ℂ (fun (x : Fin (n+1) → ℂ) =>
      (2 * Real.pi * Complex.I : ℂ)⁻¹ *
        ∮ ζ in C(0, ε),
          (f : MvPowerSeries (Fin (n+1)) ℂ).eval (Fin.snoc (Fin.init x) ζ) /
            (((LocalOkaRing.fromPolynomial q : LocalOkaRing (Fin (n+1))) :
                MvPowerSeries (Fin (n+1)) ℂ).eval (Fin.snoc (Fin.init x) ζ)
              * (ζ - x (Fin.last n)))) 0 := by
    sorry
  obtain ⟨P, hconv, hrep⟩ := MvPowerSeries.exists_represents hF
  exact ⟨⟨P, hconv⟩, hrep⟩
















/-- uniqueness is omitted ---/
theorem localweierstrass_division
      (q : (LocalOkaRing (Fin n))[X])
      (hq : IsLocalWeierstrassPolynomial
           (Polynomial.map (Subring.subtype (localOkaSubring _).toSubring) q))
      (f : LocalOkaRing (Fin (n + 1))) :
      ∃ (a : LocalOkaRing (Fin (n + 1)))
        (b : (LocalOkaRing (Fin (n)))[X]) (hd : b.degree < q.degree),
      f = a * (LocalOkaRing.fromPolynomial q) + (LocalOkaRing.fromPolynomial b) :=
  sorry








/-- The Weierstrass preparation theorem for germs; uniqueness is omitted. -/
theorem localweierstrass_preparation
    (f : LocalOkaRing (Fin (n + 1)))
    (hf : (f : MvPowerSeries (Fin (n + 1)) ℂ).IsGeneralIn (.last _)) :
    ∃ (u : LocalOkaRing (Fin (n + 1))) (hu : IsUnit u)
      (g : (LocalOkaRing (Fin (n)))[X])
      (hg : IsLocalWeierstrassPolynomial
           (Polynomial.map (Subring.subtype (localOkaSubring _).toSubring) g)),
      f = LocalOkaRing.fromPolynomial g * u :=
  sorry



















variable {n : ℕ} (U : Opens (Fin n → ℂ))

/-- A Weierstrass polynomial is a monic polynomial whose coefficients below the leading one
vanish at the origin. -/
structure IsWeierstrassPolynomial (P : (OkaRing U)[X]) : Prop where
  monic : P.Monic
  apply_zero (i : ℕ) (hi : i < P.degree) : (P.coeff i).toGlobalFun _ 0 = 0

variable (U : Opens (Fin (n + 1) → ℂ))

/-- The Weierstrass preparation theorem; uniqueness is omitted. -/
theorem weierstrass_preparation
    (f : OkaRing U) (h : 0 ∈ U)
    (hf : ∃ (w : ℂ) (hw : Fin.snoc 0 w ∈ U),
      f.toFun _ ⟨Fin.snoc 0 w, hw⟩ ≠ 0) :
    ∃ (V : Opens (Fin n → ℂ)) (hx : 0 ∈ V)
      (W : Opens (Fin (n + 1) → ℂ)) (hxW : 0 ∈ W)
      (hWV : W ≤ V.extend')
      (hWU : W ≤ U)
      (h : OkaRing W) (g : (OkaRing V)[X])
          (hi : h.toFun _ ⟨0, hxW⟩ ≠ 0)
          (hg : IsWeierstrassPolynomial _ g),
      f.restrict hWU =
        (Polynomial.toOkaRing _ g).restrict hWV *
          h :=
  sorry

/-- The Weierstrass division theorem; uniqueness is omitted. -/
theorem weierstrass_division
      (S : Opens (Fin n → ℂ))
      (g : (OkaRing S)[X]) (hx : 0 ∈ U) (hg : IsWeierstrassPolynomial _ g)
      (V : Opens (Fin (n + 1) → ℂ)) (hy : 0 ∈ V)
      (f : OkaRing V) :
    ∃ (W : Opens (Fin (n+1) → ℂ))
          (hWV : W ≤ V) (hWS : W ≤ S.extend')
      (h : OkaRing W)
      (r : (OkaRing S)[X]) (hd : r.degree < g.degree),
      f.restrict hWV =
          (Polynomial.toOkaRing _ g).restrict hWS * h +
              (Polynomial.toOkaRing _ r).restrict hWS :=
  sorry
