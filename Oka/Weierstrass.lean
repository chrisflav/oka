/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.OkaRing
import Oka.LocalOkaRing
import Mathlib.MeasureTheory.Integral.CircleIntegral
/-!
# The Weierstrass preparation theorem

We state the Weierstrass preparation theorem: a holomorphic function on a neighbourhood of the
origin in `ℂ^{n+1}` which does not vanish identically on the last coordinate axis factors, near
the origin, as a unit times a Weierstrass polynomial.

## Main definitions

- `IsWeierstrassPolynomial`: a monic polynomial whose lower coefficients vanish at the origin.
-/

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

structure IsLocalWeierstrassPolynomial
  (P : (MvPowerSeries (Fin n) ℂ)[X]) : Prop where
  monic : P.Monic
  apply_zero (i : ℕ) (hi : i < P.degree) :
  MvPowerSeries.constantCoeff (P.coeff i)  = 0

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











lemma localweierstrass_division_lemma_one
      (q : (LocalOkaRing (Fin n))[X])
      (hq : IsLocalWeierstrassPolynomial (Polynomial.map (localOkaSubring _).val.toRingHom q))
      (f : LocalOkaRing (Fin (n + 1))) :
      ∃ (δ : ℝ) (hd : δ > 0) (ε : ℝ) (he : ε > 0),
      ∀ (z : Fin (n+1) → ℂ)
          (hz₁ : ∀ i : Fin n, ‖z i.castSucc‖ ≤ δ)
          (hz₂ : ‖z (Fin.last n)‖ = ε),
          ((f : MvPowerSeries (Fin (n+1)) ℂ)).SummableAt z ∧
          ((LocalOkaRing.fromPolynomial q : LocalOkaRing (Fin (n+1))) : MvPowerSeries (Fin (n+1)) ℂ).eval z ≠ 0
       := by
  obtain ⟨ρ, hρ, hsum⟩ := (f.locallyConvergent).exists_summableAt_const
  refine ⟨ρ, hρ, ρ, hρ, ?_⟩
  intro z hz₁ hz₂
  constructor
  · refine hsum.mono ?_
    intro i
    induction i using Fin.lastCases with
    | last => simp [hz₂, Complex.norm_real, abs_of_nonneg hρ.le]
    | cast j => simpa [Complex.norm_real, abs_of_nonneg hρ.le] using hz₁ j
  · sorry

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

open Polynomial in
theorem exists_diffQuotient {R : Type*} [CommRing R] [Nontrivial R]
    (q : R[X]) (hq : q ≠ 0) (c : R) :
    ∃ Q : R[X], Q.degree < q.degree ∧ q - C (q.eval c) = (X - C c) * Q := by
  refine ⟨q /ₘ (X - C c), ?_, ?_⟩
  · refine degree_divByMonic_lt q (X - C c) hq ?_
    rw [degree_X_sub_C]
    exact_mod_cast Nat.zero_lt_one
  · have h := modByMonic_add_div q (X - C c)
    rw [modByMonic_X_sub_C_eq_C_eval] at h
    exact (eq_sub_of_add_eq' h).symm














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








/-- uniqueness is omitted ---/
theorem localweierstrass_preparation
    (f : LocalOkaRing (Fin (n+1)))
    (hf : (f : MvPowerSeries (Fin (n+1)) ℂ).IsGeneralIn  (.last _) ) :
    ∃ (u : LocalOkaRing (Fin (n+1))) (hu : IsUnit u)
      (g : (LocalOkaRing (Fin (n)))[X])
      (hg : IsLocalWeierstrassPolynomial
           (Polynomial.map (Subring.subtype (localOkaSubring _).toSubring) g)),
      f = LocalOkaRing.fromPolynomial g * u :=
  sorry



















variable {n : ℕ} (U : Opens (Fin n → ℂ))

structure IsWeierstrassPolynomial (P : (OkaRing U)[X]) : Prop where
  monic : P.Monic
  apply_zero (i : ℕ) (hi : i < P.degree) : (P.coeff i).toGlobalFun _ 0 = 0

variable (U : Opens (Fin (n + 1) → ℂ))

/-- uniqueness is omitted ---/
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

/-- uniqueness is omitted ---/
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
