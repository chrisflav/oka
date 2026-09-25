/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.Analysis.Complex.Polynomial.Basic
import Oka.OkaLemma
import Oka.MaximalIdeal
import Oka.RenameIndex
import Oka.Regular

/-!
# Splitting monic polynomials over germ rings

Let `R = ℂ{x₁, …, x_n}` be the ring of germs at the origin of holomorphic functions and
`P ∈ R[t]` a monic polynomial whose reduction `P(0, t) ∈ ℂ[t]` has the roots `c₁, …, c_k`. Then

  `R[t] ⧸ (P) ≅ ∏ⱼ ℂ{x, t - cⱼ} ⧸ (P)`,

the map sending a polynomial to its germs at the points `(0, cⱼ)`
(`LocalOkaRing.isPiQuotient_shiftPoly`). The proof factors `P` at every `(0, cⱼ)` as a
Weierstrass polynomial times a unit (`exists_weierstrass_factor`), identifies each factor of the
product with `R[t] ⧸ (Gⱼ)` by Weierstrass division, and concludes with the Chinese remainder
theorem, the `Gⱼ` being pairwise coprime with product `P`.

Iterating over several variables gives, for monic `P₁, …, P_m ∈ R[t]`,

  `R[t₁, …, t_m] ⧸ (P₁(t₁), …, P_m(t_m)) ≅ ∏_c ℂ{x, t - c} ⧸ (P₁(t₁), …, P_m(t_m))`,

the product running over the tuples `c` of roots (`LocalOkaRing.isPiQuotient_germMap`).

Such statements are phrased with `Ideal.IsPiQuotient`: a family of ring maps `κ i : T → Q i`
together with ideals `I i` of `Q i` such that `T → ∏ i, Q i ⧸ I i` is surjective with a given
kernel.

## Main definitions

- `Ideal.IsPiQuotient`: `T ⧸ K ≅ ∏ i, Q i ⧸ I i` through a family of ring maps.
- `LocalOkaRing.shiftPoly`: the germ at `(0, c)` of a polynomial over `ℂ{x}`.
- `LocalOkaRing.germMap`: the germ at `(0, c)` of a polynomial in several variables over `ℂ{x}`.

## Main results

- `LocalOkaRing.isPiQuotient_shiftPoly`: the splitting in one variable.
- `LocalOkaRing.isPiQuotient_germMap`: the splitting in several variables.
-/

open Polynomial

namespace Ideal

variable {T : Type*} [CommRing T] {ι : Type*} {Q : ι → Type*} [∀ i, CommRing (Q i)]

/-- A family of ring maps `κ i : T → Q i` and ideals `I i` of `Q i` **present `T ⧸ K` as
`∏ i, Q i ⧸ I i`**: the induced map `T → ∏ i, Q i ⧸ I i` is surjective with kernel `K`. -/
structure IsPiQuotient (κ : ∀ i, T →+* Q i) (I : ∀ i, Ideal (Q i)) (K : Ideal T) : Prop where
  exists_sub_mem (q : ∀ i, Q i) : ∃ f : T, ∀ i, κ i f - q i ∈ I i
  forall_mem_iff (f : T) : (∀ i, κ i f ∈ I i) ↔ f ∈ K

namespace IsPiQuotient

variable {κ : ∀ i, T →+* Q i} {I : ∀ i, Ideal (Q i)} {K : Ideal T}

lemma map_mem (h : IsPiQuotient κ I K) {f : T} (hf : f ∈ K) (i : ι) : κ i f ∈ I i :=
  (h.forall_mem_iff f).2 hf i

lemma exists_single (h : IsPiQuotient κ I K) (i : ι) (q : Q i) :
    ∃ f : T, κ i f - q ∈ I i ∧ ∀ j ≠ i, κ j f ∈ I j := by
  classical
  obtain ⟨f, hf⟩ := h.exists_sub_mem (Pi.single i q)
  refine ⟨f, by simpa using hf i, fun j hj ↦ ?_⟩
  simpa [Pi.single_eq_of_ne hj] using hf j

/-- Elements of `𝔞.map (κ i)` lift, modulo the `I j`, to elements of `𝔞` concentrated at `i`. -/
lemma exists_mem_of_mem_map (h : IsPiQuotient κ I K) (𝔞 : Ideal T) (i : ι)
    {x : Q i} (hx : x ∈ 𝔞.map (κ i)) :
    ∃ g ∈ 𝔞, κ i g - x ∈ I i ∧ ∀ j ≠ i, κ j g ∈ I j := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨e, he, he'⟩ := h.exists_single i 1
    refine ⟨e * a, 𝔞.mul_mem_left e ha, ?_, fun j hj ↦ ?_⟩
    · rw [map_mul, ← sub_one_mul]
      exact (I i).mul_mem_right _ he
    · rw [map_mul]
      exact (I j).mul_mem_right _ (he' j hj)
  | zero => exact ⟨0, 𝔞.zero_mem, by simp, fun j _ ↦ by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨g, hg, hgi, hgj⟩ := hx
    obtain ⟨g', hg', hgi', hgj'⟩ := hy
    refine ⟨g + g', 𝔞.add_mem hg hg', ?_, fun j hj ↦ ?_⟩
    · rw [map_add, add_sub_add_comm]
      exact (I i).add_mem hgi hgi'
    · rw [map_add]
      exact (I j).add_mem (hgj j hj) (hgj' j hj)
  | smul y x _ hx =>
    obtain ⟨g, hg, hgi, hgj⟩ := hx
    obtain ⟨w, hw, -⟩ := h.exists_single i y
    refine ⟨w * g, 𝔞.mul_mem_left w hg, ?_, fun j hj ↦ ?_⟩
    · have e : κ i (w * g) - y • x = κ i w * (κ i g - x) + (κ i w - y) * x := by
        rw [smul_eq_mul, map_mul]
        ring
      rw [e]
      exact (I i).add_mem ((I i).mul_mem_left _ hgi) ((I i).mul_mem_right _ hw)
    · rw [map_mul]
      exact (I j).mul_mem_left _ (hgj j hj)

/-- **Quotienting both sides by an ideal `𝔞` of `T`.** -/
theorem sup [Finite ι] (h : IsPiQuotient κ I K) (𝔞 : Ideal T) :
    IsPiQuotient κ (fun i ↦ I i ⊔ 𝔞.map (κ i)) (K ⊔ 𝔞) where
  exists_sub_mem q := by
    obtain ⟨f, hf⟩ := h.exists_sub_mem q
    exact ⟨f, fun i ↦ Ideal.mem_sup_left (hf i)⟩
  forall_mem_iff f := by
    classical
    have := Fintype.ofFinite ι
    constructor
    · intro hf
      have hx : ∀ i, ∃ g ∈ 𝔞, κ i f - κ i g ∈ I i ∧ ∀ j ≠ i, κ j g ∈ I j := fun i ↦ by
        obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 (hf i)
        obtain ⟨g, hg, hgi, hgj⟩ := h.exists_mem_of_mem_map 𝔞 i hz
        refine ⟨g, hg, ?_, hgj⟩
        have e : κ i f - κ i g = y - (κ i g - z) := by
          rw [← hyz]
          ring
        rw [e]
        exact (I i).sub_mem hy hgi
      choose g hg hgi hgj using hx
      have hK : f - ∑ i, g i ∈ K := by
        rw [← h.forall_mem_iff]
        intro j
        rw [map_sub, map_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ j),
          sub_add_eq_sub_sub]
        exact (I j).sub_mem (hgi j) (Ideal.sum_mem _ fun i hi ↦
          hgj i j (Finset.ne_of_mem_erase hi).symm)
      have := Submodule.add_mem_sup hK (Ideal.sum_mem 𝔞 (t := Finset.univ) fun i _ ↦ hg i)
      rwa [sub_add_cancel] at this
    · intro hf i
      obtain ⟨k, hk, a, ha, rfl⟩ := Submodule.mem_sup.1 hf
      rw [map_add]
      exact Submodule.add_mem_sup (h.map_mem hk i) (Ideal.mem_map_of_mem _ ha)

/-- **Composition**: presenting each `Q i ⧸ I i` as a product presents `T ⧸ K` as the product of
all factors. -/
theorem comp {δ : Type*} {R : ι → δ → Type*} [∀ i d, CommRing (R i d)]
    (h : IsPiQuotient κ I K) {ψ : ∀ i d, Q i →+* R i d} {J : ∀ i d, Ideal (R i d)}
    (hψ : ∀ i, IsPiQuotient (ψ i) (J i) (I i)) :
    IsPiQuotient (fun p : ι × δ ↦ (ψ p.1 p.2).comp (κ p.1)) (fun p ↦ J p.1 p.2) K where
  exists_sub_mem r := by
    choose q hq using fun i ↦ (hψ i).exists_sub_mem (fun d ↦ r (i, d))
    obtain ⟨f, hf⟩ := h.exists_sub_mem q
    refine ⟨f, fun p ↦ ?_⟩
    have := (J p.1 p.2).add_mem ((hψ p.1).map_mem (hf p.1) p.2) (hq p.1 p.2)
    rwa [map_sub, sub_add_sub_cancel] at this
  forall_mem_iff f := by
    rw [← h.forall_mem_iff]
    exact ⟨fun hf i ↦ ((hψ i).forall_mem_iff _).1 fun d ↦ hf (i, d),
      fun hf p ↦ ((hψ p.1).forall_mem_iff _).2 (hf p.1) p.2⟩

/-- **Adjoining a root of a monic polynomial** `P` on both sides. -/
theorem polynomial [Finite ι] (h : IsPiQuotient κ I K) {P : T[X]} (hP : P.Monic) :
    IsPiQuotient (fun i ↦ mapRingHom (κ i)) (fun i ↦ span {P.map (κ i)} ⊔ (I i).map C)
      (span {P} ⊔ K.map C) where
  exists_sub_mem q := by
    classical
    have := Fintype.ofFinite ι
    choose α hα using fun j : ℕ ↦ h.exists_sub_mem (fun i ↦ (q i).coeff j)
    let N := Finset.univ.sup fun i ↦ (q i).natDegree
    refine ⟨∑ j ∈ Finset.range (N + 1), C (α j) * X ^ j, fun i ↦ Ideal.mem_sup_right ?_⟩
    rw [Ideal.mem_map_C_iff]
    intro k
    simp only [coe_mapRingHom, coeff_sub, coeff_map, finsetSum_coeff, coeff_C_mul_X_pow,
      map_sum]
    by_cases hk : k ≤ N
    · rw [Finset.sum_eq_single k (fun j _ hj ↦ by rw [if_neg (Ne.symm hj), map_zero])
        (fun hk' ↦ absurd (Finset.mem_range.2 (Nat.lt_succ_of_le hk)) hk'), if_pos rfl]
      exact hα k i
    · have hq : (q i).coeff k = 0 := coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt (Finset.le_sup (f := fun i ↦ (q i).natDegree) (Finset.mem_univ i))
          (not_le.1 hk))
      rw [hq, sub_zero, Finset.sum_eq_zero fun j hj ↦ ?_]
      · exact zero_mem _
      rw [if_neg, map_zero]
      rintro rfl
      exact hk (Nat.le_of_lt_succ (Finset.mem_range.1 hj))
  forall_mem_iff f := by
    constructor
    · intro hf
      rcases subsingleton_or_nontrivial T with hT | hT
      · exact Ideal.mem_sup_left (by simp [Subsingleton.elim f 0])
      have hr : f %ₘ P ∈ K.map C := by
        rw [Ideal.mem_map_C_iff]
        intro k
        rw [← h.forall_mem_iff]
        intro i
        by_cases hI : I i = ⊤
        · rw [hI]
          trivial
        haveI : Nontrivial (Q i ⧸ I i) := Ideal.Quotient.nontrivial_iff.2 hI
        haveI : Nontrivial (Q i) := by
          by_contra h'
          rw [not_nontrivial_iff_subsingleton] at h'
          exact hI (Subsingleton.elim _ _)
        obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 (hf i)
        obtain ⟨v, rfl⟩ := Ideal.mem_span_singleton'.1 hy
        let π := Ideal.Quotient.mk (I i)
        have hz0 : z.map π = 0 := by
          ext l
          rw [coeff_map, coeff_zero, Ideal.Quotient.eq_zero_iff_mem]
          exact Ideal.mem_map_C_iff.1 hz l
        have hrf : (f %ₘ P).map (κ i) = (v - (f /ₘ P).map (κ i)) * P.map (κ i) + z := by
          have e1 := congrArg (Polynomial.map (κ i)) (modByMonic_add_div f P)
          simp only [coe_mapRingHom] at hyz
          rw [Polynomial.map_add, Polynomial.map_mul, ← hyz] at e1
          linear_combination e1
        have hkey : ((f %ₘ P).map (κ i)).map π =
            (v - (f /ₘ P).map (κ i)).map π * (P.map (κ i)).map π := by
          rw [hrf, Polynomial.map_add, hz0, add_zero, Polynomial.map_mul]
        have hPm : ((P.map (κ i)).map π).Monic := (hP.map _).map _
        have hdeg : (((f %ₘ P).map (κ i)).map π).degree < ((P.map (κ i)).map π).degree := by
          rw [(hP.map (κ i)).degree_map π, hP.degree_map]
          exact lt_of_le_of_lt (degree_map_le.trans degree_map_le) (degree_modByMonic_lt f hP)
        have h0 : ((f %ₘ P).map (κ i)).map π = 0 := by
          rw [← (modByMonic_eq_self_iff hPm).2 hdeg, modByMonic_eq_zero_iff_dvd hPm, hkey]
          exact dvd_mul_left _ _
        have := congrArg (fun p ↦ p.coeff k) h0
        simp only [coeff_map, coeff_zero, π, Ideal.Quotient.eq_zero_iff_mem] at this
        exact this
      rw [← modByMonic_add_div f P]
      exact Ideal.add_mem _ (Ideal.mem_sup_right hr)
        (Ideal.mem_sup_left (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self P)))
    · intro hf i
      obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hf
      obtain ⟨v, rfl⟩ := Ideal.mem_span_singleton'.1 hy
      rw [map_add, map_mul]
      refine Submodule.add_mem_sup (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)) ?_
      rw [Ideal.mem_map_C_iff] at hz ⊢
      intro l
      rw [coe_mapRingHom, coeff_map]
      exact h.map_mem (hz l) i

/-- Reindexing along an equivalence. -/
theorem reindex {ι' : Type*} (h : IsPiQuotient κ I K) (e : ι' ≃ ι) :
    IsPiQuotient (fun i' ↦ κ (e i')) (fun i' ↦ I (e i')) K where
  exists_sub_mem q := by
    obtain ⟨f, hf⟩ := h.exists_sub_mem (Equiv.piCongrLeft Q e q)
    refine ⟨f, fun i' ↦ ?_⟩
    have := hf (e i')
    rwa [Equiv.piCongrLeft_apply_apply] at this
  forall_mem_iff f := by
    rw [← h.forall_mem_iff]
    refine ⟨fun hf i ↦ ?_, fun hf i' ↦ hf (e i')⟩
    have := hf (e.symm i)
    rwa [e.apply_symm_apply] at this

/-- Precomposing with a ring isomorphism. -/
theorem comp_ringEquiv {T' : Type*} [CommRing T'] (h : IsPiQuotient κ I K) (e : T' ≃+* T) :
    IsPiQuotient (fun i ↦ (κ i).comp e.toRingHom) I (K.comap e.toRingHom) where
  exists_sub_mem q := by
    obtain ⟨f, hf⟩ := h.exists_sub_mem q
    exact ⟨e.symm f, fun i ↦ by simpa using hf i⟩
  forall_mem_iff f := h.forall_mem_iff (e f)

lemma congr {κ' : ∀ i, T →+* Q i} {I' : ∀ i, Ideal (Q i)} {K' : Ideal T}
    (h : IsPiQuotient κ I K) (hκ : ∀ i, κ i = κ' i) (hI : ∀ i, I i = I' i) (hK : K = K') :
    IsPiQuotient κ' I' K' := by
  obtain rfl : κ = κ' := funext hκ
  obtain rfl : I = I' := funext hI
  exact hK ▸ h

/-- **Restricting to the factors not killed by the ideals**: if `I i = ⊤` outside the range of
an injection `j`, only the factors indexed by `j` are needed. -/
theorem restrict {Q₀ : Type*} [CommRing Q₀] {κ : ι → T →+* Q₀} {I : ι → Ideal Q₀}
    (h : IsPiQuotient κ I K) {F : Type*} (j : F → ι) (hj : Function.Injective j)
    (htop : ∀ i ∉ Set.range j, I i = ⊤) :
    IsPiQuotient (fun y ↦ κ (j y)) (fun y ↦ I (j y)) K where
  exists_sub_mem q := by
    obtain ⟨f, hf⟩ := h.exists_sub_mem (Function.extend j q 0)
    exact ⟨f, fun y ↦ by simpa [hj.extend_apply] using hf (j y)⟩
  forall_mem_iff f := by
    rw [← h.forall_mem_iff]
    refine ⟨fun hf i ↦ ?_, fun hf y ↦ hf (j y)⟩
    by_cases hi : i ∈ Set.range j
    · obtain ⟨y, rfl⟩ := hi
      exact hf y
    · rw [htop i hi]
      trivial

/-- With a surjection `σ i : Q i → O i` with kernel `I i` for every `i`, the map
`T → ∏ i, O i` is surjective with kernel `K`. -/
theorem surjective_and_ker_eq {O : ι → Type*} [∀ i, CommRing (O i)] (h : IsPiQuotient κ I K)
    (σ : ∀ i, Q i →+* O i) (hσ : ∀ i, Function.Surjective (σ i))
    (hker : ∀ i, RingHom.ker (σ i) = I i) :
    Function.Surjective (RingHom.pi fun i ↦ (σ i).comp (κ i)) ∧
      RingHom.ker (RingHom.pi fun i ↦ (σ i).comp (κ i)) = K := by
  refine ⟨fun o ↦ ?_, Ideal.ext fun f ↦ ?_⟩
  · choose q hq using fun i ↦ hσ i (o i)
    obtain ⟨f, hf⟩ := h.exists_sub_mem q
    refine ⟨f, funext fun i ↦ ?_⟩
    have := hf i
    rw [← hker i, RingHom.mem_ker, map_sub, hq i, sub_eq_zero] at this
    exact this
  · rw [← h.forall_mem_iff, RingHom.mem_ker]
    simp only [funext_iff, RingHom.pi_apply, RingHom.comp_apply, Pi.zero_apply, ← hker,
      RingHom.mem_ker]

end IsPiQuotient

end Ideal

lemma Polynomial.Monic.taylor {R : Type*} [CommRing R] {p : R[X]} (hp : p.Monic) (r : R) :
    (taylor r p).Monic := by
  rw [Monic, leadingCoeff_taylor]
  exact hp

namespace LocalOkaRing

variable {n : ℕ}

/-! ### Germs of polynomials at the points `(0, c)` -/

lemma constantCoeff_renameEmb {ι κ : Type*} [Fintype ι] (e : ι ↪ κ) (P : LocalOkaRing ι) :
    LocalOkaRing.constantCoeff (renameEmb e P) = LocalOkaRing.constantCoeff P := by
  haveI : Filter.TendstoCofinite (e : ι → κ) := Filter.tendstoCofinite_of_finite _
  rw [constantCoeff_apply, constantCoeff_apply, coe_renameEmb,
    MvPowerSeries.constantCoeff_rename]

lemma renameEmb_coord {ι κ : Type*} [Fintype ι] (e : ι ↪ κ) (i : ι) :
    renameEmb e (coord i) = coord (e i) := by
  haveI : Filter.TendstoCofinite (e : ι → κ) := Filter.tendstoCofinite_of_finite _
  ext1
  rw [coe_renameEmb, coe_coord, coe_coord, MvPowerSeries.rename_X]

lemma constantCoeff_fromPolynomial_eq_eval (f : (LocalOkaRing (Fin n))[X]) :
    LocalOkaRing.constantCoeff (fromPolynomial f) =
      (f.map LocalOkaRing.constantCoeff).eval 0 := by
  have h : LocalOkaRing.constantCoeff.comp (fromPolynomial (n := n)).toRingHom =
      (evalRingHom 0).comp (mapRingHom LocalOkaRing.constantCoeff) := by
    refine Polynomial.ringHom_ext (fun a ↦ ?_) ?_
    · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe, fromPolynomial_C, coe_mapRingHom, map_C, coe_evalRingHom, eval_C]
      rw [incl_eq_renameEmb, constantCoeff_renameEmb]
    · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe, fromPolynomial_X, coe_mapRingHom, map_X, coe_evalRingHom, eval_X]
      rw [lastVar_eq_coord, constantCoeff_coord]
  exact RingHom.congr_fun h f

lemma taylor_neg_taylor {R : Type*} [CommRing R] [Algebra ℂ R] (c : ℂ) (f : R[X]) :
    taylor (algebraMap ℂ R (-c)) (taylor (algebraMap ℂ R c) f) = f := by
  rw [taylor_taylor, ← map_add, neg_add_cancel, map_zero, taylor_zero]

lemma taylor_taylor_neg {R : Type*} [CommRing R] [Algebra ℂ R] (c : ℂ) (f : R[X]) :
    taylor (algebraMap ℂ R c) (taylor (algebraMap ℂ R (-c)) f) = f := by
  rw [taylor_taylor, ← map_add, add_neg_cancel, map_zero, taylor_zero]

/-- **The germ at `(0, c)` of a polynomial `f(x, t)` with coefficients in `ℂ{x}`**, as the germ at
the origin of `f(x, t + c)`. -/
noncomputable def shiftPoly (c : ℂ) :
    (LocalOkaRing (Fin n))[X] →+* LocalOkaRing (Fin (n + 1)) :=
  (fromPolynomial (n := n)).toRingHom.comp
    (taylorAlgHom (algebraMap ℂ (LocalOkaRing (Fin n)) c)).toRingHom

lemma shiftPoly_apply (c : ℂ) (f : (LocalOkaRing (Fin n))[X]) :
    shiftPoly c f = fromPolynomial (taylor (algebraMap ℂ (LocalOkaRing (Fin n)) c) f) :=
  rfl

@[simp]
lemma shiftPoly_C (c : ℂ) (a : LocalOkaRing (Fin n)) : shiftPoly c (C a) = incl a := by
  rw [shiftPoly_apply, taylor_C, fromPolynomial_C]

@[simp]
lemma shiftPoly_X (c : ℂ) :
    shiftPoly (n := n) c X = coord (Fin.last n) + algebraMap ℂ _ c := by
  rw [shiftPoly_apply, taylor_X, map_add, fromPolynomial_X, fromPolynomial_C, AlgHom.commutes,
    lastVar_eq_coord]

lemma constantCoeff_shiftPoly (c : ℂ) (f : (LocalOkaRing (Fin n))[X]) :
    LocalOkaRing.constantCoeff (shiftPoly c f) = (f.map LocalOkaRing.constantCoeff).eval c := by
  rw [shiftPoly_apply, constantCoeff_fromPolynomial_eq_eval, map_taylor, constantCoeff_algebraMap,
    taylor_eval, zero_add]

/-! ### Weierstrass factors at the points `(0, c)` -/

lemma _root_.IsLocalWeierstrassPolynomial.monic' {g : (LocalOkaRing (Fin n))[X]}
    (hg : IsLocalWeierstrassPolynomial (g.map (localOkaSubring (Fin n)).toSubring.subtype)) :
    g.Monic :=
  Polynomial.monic_of_injective Subtype.val_injective hg.monic

/-- The reduction of a local Weierstrass polynomial of degree `d` is `X ^ d`. -/
lemma _root_.IsLocalWeierstrassPolynomial.map_constantCoeff {g : (LocalOkaRing (Fin n))[X]}
    (hg : IsLocalWeierstrassPolynomial (g.map (localOkaSubring (Fin n)).toSubring.subtype)) :
    g.map LocalOkaRing.constantCoeff = X ^ g.natDegree := by
  ext k
  rw [coeff_map, coeff_X_pow]
  rcases lt_trichotomy k g.natDegree with hk | rfl | hk
  · rw [if_neg hk.ne]
    have := hg.apply_zero k (by
      rw [degree_map_eq_of_injective Subtype.val_injective, degree_eq_natDegree hg.monic'.ne_zero]
      exact_mod_cast hk)
    rw [coeff_map] at this
    rw [constantCoeff_apply]
    exact this
  · rw [if_pos rfl, hg.monic'.coeff_natDegree, map_one]
  · rw [if_neg hk.ne', coeff_eq_zero_of_natDegree_lt hk, map_zero]

section Factor

variable {P g u : (LocalOkaRing (Fin n))[X]} {c : ℂ}
  (hg : IsLocalWeierstrassPolynomial (g.map (localOkaSubring (Fin n)).toSubring.subtype))
  (hPgu : taylor (algebraMap ℂ (LocalOkaRing (Fin n)) c) P = g * u)
  (hu : IsUnit (fromPolynomial u))

include hPgu hu in
lemma span_shiftPoly_eq : Ideal.span {shiftPoly c P} = Ideal.span {fromPolynomial g} := by
  rw [shiftPoly_apply, hPgu, map_mul]
  exact Ideal.span_singleton_mul_right_unit hu _

include hg hPgu hu in
/-- The germ at `(0, c)` of `f` is a multiple of the germ of `P` if and only if `f` is divisible
by the Weierstrass factor of `P` at `(0, c)`. -/
lemma shiftPoly_mem_span_iff (f : (LocalOkaRing (Fin n))[X]) :
    shiftPoly c f ∈ Ideal.span {shiftPoly c P} ↔
      taylor (algebraMap ℂ (LocalOkaRing (Fin n)) (-c)) g ∣ f := by
  rw [span_shiftPoly_eq hPgu hu, Ideal.mem_span_singleton', shiftPoly_apply]
  have hgm := hg.monic'
  constructor
  · rintro ⟨a, ha⟩
    have h0 := (fromPolynomial_eq_divByMonic hg (taylor _ f) (a := a) (b := 0)
      (by rw [degree_zero]; exact bot_lt_iff_ne_bot.2 (degree_ne_bot.2 hgm.ne_zero))
      (by rw [map_zero, add_zero, ha])).2
    obtain ⟨w, hw⟩ := (modByMonic_eq_zero_iff_dvd hgm).1 h0.symm
    refine ⟨taylor (algebraMap ℂ _ (-c)) w, ?_⟩
    rw [← taylor_mul, ← hw, taylor_neg_taylor]
  · rintro ⟨v, rfl⟩
    refine ⟨fromPolynomial (taylor (algebraMap ℂ _ c) v), ?_⟩
    rw [taylor_mul, taylor_taylor_neg, map_mul, mul_comm]

include hg hPgu hu in
/-- **Weierstrass division at `(0, c)`**: every germ at `(0, c)` is, modulo the germ of `P`, the
germ of a polynomial. -/
lemma exists_shiftPoly_sub_mem (h : LocalOkaRing (Fin (n + 1))) :
    ∃ f, shiftPoly c f - h ∈ Ideal.span {shiftPoly c P} := by
  obtain ⟨a, b, -, hab⟩ := localweierstrass_division g hg h
  refine ⟨taylor (algebraMap ℂ _ (-c)) b, ?_⟩
  rw [span_shiftPoly_eq hPgu hu, shiftPoly_apply, taylor_taylor_neg, hab,
    show fromPolynomial b - (a * fromPolynomial g + fromPolynomial b) =
      -a * fromPolynomial g by ring]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

include hg hPgu hu in
/-- The degree of the Weierstrass factor at `(0, c)` is the multiplicity of `c` as a root of
`P(0, t)`. -/
lemma rootMultiplicity_map_constantCoeff :
    rootMultiplicity c (P.map LocalOkaRing.constantCoeff) = g.natDegree := by
  have h1 : taylor c (P.map LocalOkaRing.constantCoeff) =
      X ^ g.natDegree * u.map LocalOkaRing.constantCoeff := by
    conv_lhs => rw [← constantCoeff_algebraMap (ι := Fin n) c]
    rw [← map_taylor, hPgu, Polynomial.map_mul, hg.map_constantCoeff]
  have hu0 : (u.map LocalOkaRing.constantCoeff).eval 0 ≠ 0 := by
    rw [← constantCoeff_fromPolynomial_eq_eval]
    exact isUnit_iff.1 hu
  have hne : (u.map LocalOkaRing.constantCoeff) ≠ 0 := fun h ↦ hu0 (by rw [h, eval_zero])
  rw [rootMultiplicity_eq_rootMultiplicity, ← taylor_apply, h1,
    rootMultiplicity_mul (mul_ne_zero (pow_ne_zero _ X_ne_zero) hne),
    rootMultiplicity_eq_zero (p := u.map _) hu0, add_zero]
  simpa using rootMultiplicity_X_sub_C_pow (0 : ℂ) g.natDegree

end Factor

lemma isUnit_shiftPoly_taylor {g : (LocalOkaRing (Fin n))[X]} {c c' : ℂ}
    (hg : IsLocalWeierstrassPolynomial (g.map (localOkaSubring (Fin n)).toSubring.subtype))
    (hc : c' ≠ c) :
    IsUnit (shiftPoly c' (taylor (algebraMap ℂ (LocalOkaRing (Fin n)) (-c)) g)) := by
  rw [isUnit_iff, constantCoeff_shiftPoly, map_taylor, constantCoeff_algebraMap,
    hg.map_constantCoeff, taylor_eval, eval_pow, eval_X]
  exact pow_ne_zero _ (by rw [← sub_eq_add_neg]; exact sub_ne_zero.2 hc)

/-- **Splitting of a monic polynomial over `ℂ{x}` at the roots of its reduction**: for monic
`P ∈ ℂ{x}[t]` and a finite set `D ⊆ ℂ` containing the roots of `P(0, t)`, the germs at the points
`(0, c)`, `c ∈ D`, induce `ℂ{x}[t] ⧸ (P) ≅ ∏_{c ∈ D} ℂ{x, t - c} ⧸ (P)`. -/
theorem isPiQuotient_shiftPoly {P : (LocalOkaRing (Fin n))[X]} (hP : P.Monic) (D : Finset ℂ)
    (hD : ∀ c, (P.map LocalOkaRing.constantCoeff).IsRoot c → c ∈ D) :
    Ideal.IsPiQuotient (fun c : D ↦ shiftPoly (n := n) (c : ℂ))
      (fun c ↦ Ideal.span {shiftPoly (c : ℂ) P}) (Ideal.span {P}) := by
  classical
  choose g u hg hgu hu using fun c : ℂ ↦
    exists_weierstrass_factor (hP.taylor (algebraMap ℂ (LocalOkaRing (Fin n)) c))
  have hker (c : ℂ) := shiftPoly_mem_span_iff (hg c) (hgu c) (hu c)
  set G : ℂ → (LocalOkaRing (Fin n))[X] := fun c ↦ taylor (algebraMap ℂ _ (-c)) (g c) with hG
  have hGm : ∀ c, (G c).Monic := fun c ↦ (hg c).monic'.taylor _
  have hcop : ∀ c c', c ≠ c' → IsCoprime (G c) (G c') := by
    intro c c' hcc'
    obtain ⟨v, hv⟩ := (isUnit_shiftPoly_taylor (hg c') hcc').exists_left_inv
    obtain ⟨b, hb⟩ := exists_shiftPoly_sub_mem (hg c) (hgu c) (hu c) v
    have hmem : shiftPoly c (b * G c' - 1) ∈ Ideal.span {shiftPoly c P} := by
      have e : shiftPoly c (b * G c' - 1) =
          (shiftPoly c b - v) * shiftPoly c (G c') + (v * shiftPoly c (G c') - 1) := by
        rw [map_sub, map_mul, map_one]
        ring
      rw [e, hv, sub_self, add_zero]
      exact Ideal.mul_mem_right _ _ hb
    obtain ⟨a, ha⟩ := (hker c _).1 hmem
    rw [show taylor (algebraMap ℂ (LocalOkaRing (Fin n)) (-c)) (g c) = G c from rfl] at ha
    exact ⟨-a, b, by linear_combination ha⟩
  have hdvd : ∀ c, G c ∣ P := fun c ↦ by
    refine ⟨taylor (algebraMap ℂ _ (-c)) (u c), ?_⟩
    rw [hG, ← taylor_mul, ← hgu c, taylor_neg_taylor]
  have hprod : ∏ c ∈ D, G c = P := by
    refine (eq_of_monic_of_dvd_of_natDegree_le (monic_prod_of_monic _ _ fun c _ ↦ hGm c) hP
      (Finset.prod_dvd_of_coprime (fun c _ c' _ h ↦ hcop c c' h) fun c _ ↦ hdvd c) ?_).symm
    rw [natDegree_prod_of_monic _ _ fun c _ ↦ hGm c]
    have e : ∀ c, (G c).natDegree = Multiset.count c (P.map LocalOkaRing.constantCoeff).roots :=
      fun c ↦ by
        rw [hG, natDegree_taylor, count_roots,
          rootMultiplicity_map_constantCoeff (hg c) (hgu c) (hu c)]
    simp only [e]
    rw [Multiset.sum_count_eq_card, IsAlgClosed.card_roots_eq_natDegree, hP.natDegree_map]
    intro a ha
    exact hD a ((mem_roots (hP.map _).ne_zero).1 ha)
  refine ⟨fun q ↦ ?_, fun f ↦ ?_⟩
  · choose f hf using fun c : D ↦ exists_shiftPoly_sub_mem (hg c) (hgu c) (hu c) (q c)
    obtain ⟨r, hr⟩ := Ideal.exists_forall_sub_mem_ideal (I := fun c : D ↦ Ideal.span {G c})
      (fun c c' h ↦ (Ideal.isCoprime_span_singleton_iff _ _).2
        (hcop c c' (Subtype.coe_injective.ne h))) f
    refine ⟨r, fun c ↦ ?_⟩
    have h1 := (hker c (r - f c)).2 (Ideal.mem_span_singleton.1 (hr c))
    rw [map_sub] at h1
    have := Ideal.add_mem _ h1 (hf c)
    rwa [sub_add_sub_cancel] at this
  · rw [Ideal.mem_span_singleton]
    constructor
    · intro h
      rw [← hprod]
      exact Finset.prod_dvd_of_coprime (fun c _ c' _ h' ↦ hcop c c' h')
        fun c hc ↦ (hker c f).1 (h ⟨c, hc⟩)
    · intro h c
      rw [← hprod] at h
      exact (hker c f).2 ((Finset.dvd_prod_of_mem G c.2).trans h)

/-! ### Several variables -/

/-- Germs in `n` variables, as germs in `n + m` variables not involving the last `m`. -/
noncomputable def inclAdd (n m : ℕ) : LocalOkaRing (Fin n) →ₐ[ℂ] LocalOkaRing (Fin (n + m)) :=
  renameEmb (Fin.castAddEmb m)

lemma incl_inclAdd (m : ℕ) (a : LocalOkaRing (Fin n)) :
    incl (inclAdd n m a) = inclAdd n (m + 1) a := by
  rw [inclAdd, inclAdd, incl_eq_renameEmb, renameEmb_trans]
  exact renameEmb_congr (fun i ↦ Fin.castSucc_castAdd i) a

lemma constantCoeff_inclAdd (m : ℕ) (a : LocalOkaRing (Fin n)) :
    LocalOkaRing.constantCoeff (inclAdd n m a) = LocalOkaRing.constantCoeff a :=
  constantCoeff_renameEmb _ a

/-- **The germ at `(0, c)` of a polynomial in `t₁, …, t_m` with coefficients in `ℂ{x}`**, as the
germ at the origin of `f(x, t + c)`. -/
noncomputable def germMap (n m : ℕ) (c : Fin m → ℂ) :
    MvPolynomial (Fin m) (LocalOkaRing (Fin n)) →+* LocalOkaRing (Fin (n + m)) :=
  MvPolynomial.eval₂Hom (inclAdd n m).toRingHom
    fun k ↦ coord (Fin.natAdd n k) + algebraMap ℂ _ (c k)

@[simp]
lemma germMap_C {m : ℕ} (c : Fin m → ℂ) (a : LocalOkaRing (Fin n)) :
    germMap n m c (MvPolynomial.C a) = inclAdd n m a :=
  MvPolynomial.eval₂Hom_C _ _ _

@[simp]
lemma germMap_X {m : ℕ} (c : Fin m → ℂ) (k : Fin m) :
    germMap n m c (MvPolynomial.X k) = coord (Fin.natAdd n k) + algebraMap ℂ _ (c k) :=
  MvPolynomial.eval₂Hom_X' _ _ _

lemma germMap_comp_C {m : ℕ} (c : Fin m → ℂ) :
    (germMap n m c).comp MvPolynomial.C = (inclAdd n m).toRingHom :=
  RingHom.ext fun a ↦ germMap_C c a

/-- The polynomial `P k` in the variable `t_k`. -/
noncomputable def polyVar {m : ℕ} (P : Fin m → (LocalOkaRing (Fin n))[X]) (k : Fin m) :
    MvPolynomial (Fin m) (LocalOkaRing (Fin n)) :=
  (P k).eval₂ MvPolynomial.C (MvPolynomial.X k)

/-- The roots of the reduction `p(0, t)` of a polynomial over `ℂ{x}`. -/
noncomputable def rootsFinset (p : (LocalOkaRing (Fin n))[X]) : Finset ℂ :=
  (p.map LocalOkaRing.constantCoeff).roots.toFinset

lemma mem_rootsFinset {p : (LocalOkaRing (Fin n))[X]} (hp : p.Monic) {c : ℂ} :
    c ∈ rootsFinset p ↔ (p.map LocalOkaRing.constantCoeff).IsRoot c := by
  rw [rootsFinset, Multiset.mem_toFinset, mem_roots (hp.map _).ne_zero]

/-- `R[t₁, …, t_{m+1}] ≃ R[t₁, …, t_m][t_{m+1}]`. -/
noncomputable def lastVarEquiv (m : ℕ) (R : Type*) [CommRing R] :
    MvPolynomial (Fin (m + 1)) R ≃+* (MvPolynomial (Fin m) R)[X] :=
  ((MvPolynomial.renameEquiv R (finSuccEquiv' (Fin.last m))).trans
    (MvPolynomial.optionEquivLeft R (Fin m))).toRingEquiv

section LastVarEquiv

variable {m : ℕ} {R : Type*} [CommRing R]

@[simp]
lemma lastVarEquiv_C (r : R) :
    lastVarEquiv m R (MvPolynomial.C r) = C (MvPolynomial.C r) := by
  simp [lastVarEquiv]

@[simp]
lemma lastVarEquiv_X_last : lastVarEquiv m R (MvPolynomial.X (Fin.last m)) = X := by
  simp [lastVarEquiv, finSuccEquiv'_at]

@[simp]
lemma lastVarEquiv_X_castSucc (j : Fin m) :
    lastVarEquiv m R (MvPolynomial.X j.castSucc) = C (MvPolynomial.X j) := by
  simp [lastVarEquiv, finSuccEquiv'_below (Fin.castSucc_lt_last j)]

lemma lastVarEquiv_eval₂ (p : R[X]) (x : MvPolynomial (Fin (m + 1)) R) :
    lastVarEquiv m R (p.eval₂ MvPolynomial.C x) =
      p.eval₂ (C.comp MvPolynomial.C) (lastVarEquiv m R x) := by
  rw [← RingEquiv.coe_toRingHom, hom_eval₂]
  congr 1
  exact RingHom.ext fun r ↦ lastVarEquiv_C r

lemma lastVarEquiv_polyVar_last (P : Fin (m + 1) → (LocalOkaRing (Fin n))[X]) :
    lastVarEquiv m _ (polyVar P (Fin.last m)) = (P (Fin.last m)).map MvPolynomial.C := by
  rw [polyVar, lastVarEquiv_eval₂, lastVarEquiv_X_last,
    ← eval₂_C_X (p := (P (Fin.last m)).map _), eval₂_map]

lemma lastVarEquiv_polyVar_castSucc (P : Fin (m + 1) → (LocalOkaRing (Fin n))[X])
    (j : Fin m) :
    lastVarEquiv m _ (polyVar P j.castSucc) = C (polyVar (fun k ↦ P k.castSucc) j) := by
  rw [polyVar, polyVar, lastVarEquiv_eval₂, lastVarEquiv_X_castSucc, hom_eval₂]

end LastVarEquiv

lemma germMap_succ {m : ℕ} (c : Fin (m + 1) → ℂ) :
    ((shiftPoly (n := n + m) (c (Fin.last m))).comp
      (mapRingHom (germMap n m fun k ↦ c k.castSucc))).comp (lastVarEquiv m _).toRingHom =
      germMap n (m + 1) c := by
  refine MvPolynomial.ringHom_ext (fun a ↦ ?_) (fun k ↦ ?_)
  · simp [incl_inclAdd]
  · induction k using Fin.lastCases with
    | last =>
      simp [Fin.natAdd_last]
      rfl
    | cast j =>
      simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
        RingEquiv.coe_toRingHom, lastVarEquiv_X_castSucc, coe_mapRingHom, map_C, germMap_X,
        shiftPoly_C, map_add, AlgHom.commutes, incl_eq_renameEmb, renameEmb_coord]
      rw [Fin.natAdd_castSucc]
      rfl

lemma isPiQuotient_germMap_zero (P : Fin 0 → (LocalOkaRing (Fin n))[X]) :
    Ideal.IsPiQuotient (fun c : (∀ k, rootsFinset (P k)) ↦ germMap n 0 fun k ↦ (c k : ℂ))
      (fun c ↦ Ideal.span (Set.range fun k ↦ germMap n 0 (fun k ↦ (c k : ℂ)) (polyVar P k)))
      (Ideal.span (Set.range (polyVar P))) := by
  let e : Fin (n + 0) ↪ Fin n := ⟨Fin.cast (Nat.add_zero n), Fin.cast_injective _⟩
  have h1 : ∀ a, inclAdd n 0 (renameEmb e a) = a := fun a ↦ by
    rw [inclAdd, renameEmb_trans]
    exact (renameEmb_congr (e := e.trans (Fin.castAddEmb 0))
      (e' := Function.Embedding.refl _) (fun i ↦ Fin.ext rfl) a).trans (renameEmb_refl a)
  have h2 : ∀ a, renameEmb e (inclAdd n 0 a) = a := fun a ↦ by
    rw [inclAdd, renameEmb_trans]
    exact (renameEmb_congr (e := (Fin.castAddEmb 0).trans e)
      (e' := Function.Embedding.refl _) (fun i ↦ Fin.ext rfl) a).trans (renameEmb_refl a)
  simp only [Set.range_eq_empty, Ideal.span_empty]
  refine ⟨fun q ↦ ⟨MvPolynomial.C (renameEmb e (q default)), fun c ↦ ?_⟩, fun f ↦ ?_⟩
  · rw [Subsingleton.elim c default, germMap_C, h1, sub_self]
    exact Ideal.zero_mem _
  · rw [MvPolynomial.eq_C_of_isEmpty f]
    simp only [germMap_C, Ideal.mem_bot, MvPolynomial.C_eq_zero]
    exact ⟨fun h ↦ by rw [← h2 (MvPolynomial.coeff 0 f), h default, map_zero],
      fun h _ ↦ by rw [h, map_zero]⟩

/-- **Splitting in several variables**: for monic `P₁, …, P_m ∈ ℂ{x}[t]`, the germs at the
points `(0, c)`, `c` running over the tuples of roots of the reductions `P_k(0, t)`, induce
`ℂ{x}[t₁, …, t_m] ⧸ (P_k(t_k))_k ≅ ∏_c ℂ{x, t - c} ⧸ (P_k(t_k))_k`. -/
theorem isPiQuotient_germMap (m : ℕ) (P : Fin m → (LocalOkaRing (Fin n))[X])
    (hP : ∀ k, (P k).Monic) :
    Ideal.IsPiQuotient (fun c : (∀ k, rootsFinset (P k)) ↦ germMap n m fun k ↦ (c k : ℂ))
      (fun c ↦ Ideal.span (Set.range fun k ↦ germMap n m (fun k ↦ (c k : ℂ)) (polyVar P k)))
      (Ideal.span (Set.range (polyVar P))) := by
  induction m with
  | zero => exact isPiQuotient_germMap_zero P
  | succ m ih =>
    classical
    set P' : Fin m → (LocalOkaRing (Fin n))[X] := fun k ↦ P k.castSucc with hP'
    have h' := ih P' fun k ↦ hP k.castSucc
    set Pl : (MvPolynomial (Fin m) (LocalOkaRing (Fin n)))[X] :=
      (P (Fin.last m)).map MvPolynomial.C with hPl
    have hPlm : Pl.Monic := (hP _).map _
    have hmap : ∀ c' : Fin m → ℂ, Pl.map (germMap n m c') = (P (Fin.last m)).map (inclAdd n m) :=
      fun c' ↦ by rw [hPl, Polynomial.map_map, germMap_comp_C]; rfl
    have hcc : ∀ p : (LocalOkaRing (Fin n))[X],
        (p.map (inclAdd n m)).map LocalOkaRing.constantCoeff = p.map LocalOkaRing.constantCoeff :=
      fun p ↦ by
        ext k
        simp only [coeff_map]
        exact constantCoeff_inclAdd m _
    have hW : ∀ i : (∀ k, rootsFinset (P' k)), Ideal.IsPiQuotient
        (fun d : rootsFinset (P (Fin.last m)) ↦ shiftPoly (n := n + m) (d : ℂ))
        (fun d ↦ Ideal.span {shiftPoly (d : ℂ) (Pl.map (germMap n m fun k ↦ (i k : ℂ)))} ⊔
          ((Ideal.span (Set.range fun k ↦ germMap n m (fun k ↦ (i k : ℂ)) (polyVar P' k))).map
            C).map (shiftPoly (d : ℂ)))
        (Ideal.span {Pl.map (germMap n m fun k ↦ (i k : ℂ))} ⊔
          (Ideal.span (Set.range fun k ↦ germMap n m (fun k ↦ (i k : ℂ)) (polyVar P' k))).map
            C) := fun i ↦ by
      refine (isPiQuotient_shiftPoly ?_ _ fun d hd ↦ ?_).sup _
      · rw [hmap]
        exact (hP _).map _
      · rw [mem_rootsFinset (hP _)]
        rwa [hmap, hcc] at hd
    have hc := ((h'.polynomial hPlm).comp hW).comp_ringEquiv (lastVarEquiv m _)
    let ε : (∀ k, rootsFinset (P k)) ≃
        (∀ k, rootsFinset (P' k)) × rootsFinset (P (Fin.last m)) :=
      (Fin.snocEquiv fun k ↦ rootsFinset (P k)).symm.trans (Equiv.prodComm _ _)
    have hκ : ∀ c : (∀ k, rootsFinset (P k)),
        ((shiftPoly ((ε c).2 : ℂ)).comp (mapRingHom (germMap n m fun k ↦ ((ε c).1 k : ℂ)))).comp
          (lastVarEquiv m _).toRingHom = germMap n (m + 1) fun k ↦ (c k : ℂ) :=
      fun c ↦ germMap_succ fun k ↦ (c k : ℂ)
    have hlast : ∀ c : (∀ k, rootsFinset (P k)),
        germMap n (m + 1) (fun k ↦ (c k : ℂ)) (polyVar P (Fin.last m)) =
          shiftPoly ((ε c).2 : ℂ) (Pl.map (germMap n m fun k ↦ ((ε c).1 k : ℂ))) := fun c ↦ by
      rw [← hκ c]
      simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
        RingEquiv.coe_toRingHom, lastVarEquiv_polyVar_last, coe_mapRingHom]
      rfl
    have hcs : ∀ (c : ∀ k, rootsFinset (P k)) (j : Fin m),
        germMap n (m + 1) (fun k ↦ (c k : ℂ)) (polyVar P j.castSucc) =
          shiftPoly ((ε c).2 : ℂ) (C (germMap n m (fun k ↦ ((ε c).1 k : ℂ)) (polyVar P' j))) :=
      fun c j ↦ by
        rw [← hκ c]
        simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
          RingEquiv.coe_toRingHom, lastVarEquiv_polyVar_castSucc, coe_mapRingHom, map_C]
        rfl
    refine (hc.reindex ε).congr hκ (fun c ↦ ?_) ?_
    · refine le_antisymm (sup_le ?_ ?_) (Ideal.span_le.2 ?_)
      · rw [Ideal.span_le, Set.singleton_subset_iff]
        exact Ideal.subset_span ⟨Fin.last m, hlast c⟩
      · rw [Ideal.map_span, Ideal.map_span, Ideal.span_le]
        rintro _ ⟨_, ⟨_, ⟨j, rfl⟩, rfl⟩, rfl⟩
        exact Ideal.subset_span ⟨j.castSucc, hcs c j⟩
      · rintro _ ⟨k, rfl⟩
        dsimp only
        induction k using Fin.lastCases with
        | last => exact Ideal.mem_sup_left (by rw [hlast]; exact Ideal.mem_span_singleton_self _)
        | cast j =>
          refine Ideal.mem_sup_right ?_
          rw [hcs]
          exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨j, rfl⟩))
    · have hJ : Ideal.span {Pl} ⊔ (Ideal.span (Set.range (polyVar P'))).map C =
          (Ideal.span (Set.range (polyVar P))).map (lastVarEquiv m _).toRingHom := by
        refine le_antisymm (sup_le ?_ ?_) ?_
        · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, hPl,
            ← lastVarEquiv_polyVar_last P]
          exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨Fin.last m, rfl⟩)
        · rw [Ideal.map_le_iff_le_comap, Ideal.span_le]
          rintro _ ⟨j, rfl⟩
          rw [SetLike.mem_coe, Ideal.mem_comap, hP', ← lastVarEquiv_polyVar_castSucc P j]
          exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨j.castSucc, rfl⟩)
        · rw [Ideal.map_le_iff_le_comap, Ideal.span_le]
          rintro _ ⟨k, rfl⟩
          rw [SetLike.mem_coe, Ideal.mem_comap]
          change lastVarEquiv m _ (polyVar P k) ∈ _
          induction k using Fin.lastCases with
          | last =>
            rw [lastVarEquiv_polyVar_last]
            exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
          | cast j =>
            rw [lastVarEquiv_polyVar_castSucc]
            exact Ideal.mem_sup_right (Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨j, rfl⟩))
      rw [hJ]
      exact Ideal.comap_map_of_bijective _ (lastVarEquiv m _).bijective

end LocalOkaRing
