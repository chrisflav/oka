import Oka.LocalOkaRing
import Oka.Weierstrass

open Polynomial

variable {n : ℕ}

noncomputable instance : Algebra (LocalOkaRing (Fin n))
    (LocalOkaRing (Fin (n + 1))) :=
  ((LocalOkaRing.fromPolynomial (n := n)).toRingHom.comp
    (Polynomial.C : LocalOkaRing (Fin n) →+*
      (LocalOkaRing (Fin n))[X])).toAlgebra

def LocalOkaRing.fromPolynomialAlg :
    (LocalOkaRing (Fin n))[X] →ₐ[LocalOkaRing (Fin n)] LocalOkaRing (Fin (n + 1)) where
  toRingHom := LocalOkaRing.fromPolynomial.toRingHom
  commutes' _ := rfl

noncomputable def polyIncl {d : ℕ} :
    (LocalOkaRing (Fin n))[X]_d →ₗ[LocalOkaRing (Fin n)]
        (LocalOkaRing (Fin (n + 1))) :=
  LocalOkaRing.fromPolynomialAlg (n := n) ∘ₗ (Submodule.subtype _)

noncomputable def polyInclPi {p : ℕ} {d : ℕ} :
    ((Fin p) → (LocalOkaRing (Fin n))[X]_d) →ₗ[LocalOkaRing (Fin n)]
        ((Fin p) → (LocalOkaRing (Fin (n + 1)))) :=
  LinearMap.piMap (fun _ : Fin p ↦ polyIncl)

noncomputable def K_deg {p : ℕ} (d : ℕ) (F : Fin p → LocalOkaRing (Fin (n + 1))) :
    Submodule (LocalOkaRing (Fin n)) (Fin p → (LocalOkaRing (Fin n))[X]_d) :=
  LinearMap.ker ((linOfFun F).restrictScalars _ ∘ₗ
    polyInclPi)

noncomputable def KK_deg {p : ℕ} (d : ℕ) (F : Fin p → LocalOkaRing (Fin (n + 1))) :
    Submodule (LocalOkaRing (Fin (n + 1))) (Fin p → LocalOkaRing (Fin (n + 1))) :=
  Submodule.span (LocalOkaRing (Fin (n + 1)))
    (Submodule.map polyInclPi (K_deg d F)).carrier

theorem oka_lemma_weierstrass_rhs_containedIn_lhs (p : ℕ) (d : ℕ)
    (F : Fin p → (LocalOkaRing (Fin n))[X]) :
    letI F' (j : Fin p) : LocalOkaRing (Fin (n + 1)) :=
      LocalOkaRing.fromPolynomial (F j)
    Submodule.span _ (Submodule.map polyInclPi (K_deg d F')).carrier ≤
      LinearMap.ker (linOfFun F') := by
  rw [Submodule.span_le]
  intro G hG
  rcases hG with ⟨g, hg, rfl⟩
  simp only [SetLike.mem_coe, LinearMap.mem_ker, Module.Basis.constr_apply_fintype,
    Pi.basisFun_equivFun, LinearEquiv.refl_apply, smul_eq_mul]
  simp only [K_deg, SetLike.mem_coe, LinearMap.mem_ker, LinearMap.coe_comp,
    LinearMap.coe_restrictScalars, Function.comp_apply, Module.Basis.constr_apply_fintype,
    Pi.basisFun_equivFun, LinearEquiv.refl_apply, smul_eq_mul] at hg
  exact hg

theorem oka_lemma_weierstrass_lhs_containedIn_rhs (p : ℕ) (d : ℕ)
    (hp : 0 < p)
    (F : Fin p → (LocalOkaRing (Fin n))[X])
    (hF : ∀ j, (F j).degree < d)
    (hF' : ∀ j, (F j).Monic)
    (hF₁ : IsLocalWeierstrassPolynomial (Polynomial.map
      (Subring.subtype (localOkaSubring _).toSubring) (F ⟨0, hp⟩))) :
    letI F' (j : Fin p) : LocalOkaRing (Fin (n + 1)) :=
      LocalOkaRing.fromPolynomial (F j)
    LinearMap.ker (linOfFun F') ≤ KK_deg (2 * d) F' := by
  let F' (j : Fin p) : LocalOkaRing (Fin (n + 1)) :=
      LocalOkaRing.fromPolynomial (F j)
  let zero : Fin p := ⟨0, hp⟩
  let Fd (i : Fin p) : (LocalOkaRing (Fin n))[X]_d := ⟨F i, by
    simpa [Polynomial.mem_degreeLT] using hF i⟩
  let E : Fin p → (Fin p → (LocalOkaRing (Fin n))[X]_d) :=
    fun j ↦ - Pi.single zero (Fd j) + Pi.single j (Fd zero)
  intro G hG
  rw [LinearMap.mem_ker] at hG
  simp only [Module.Basis.constr_apply_fintype, Pi.basisFun_equivFun, LinearEquiv.refl_apply,
    smul_eq_mul] at hG
  choose A R hAR hAR' using fun (j : Fin p) ↦ localweierstrass_division (F zero) hF₁ (G j)
  let S := ∑ (i : Fin p), (A i) * (F' i)
  let R' := fun (j : Fin p) ↦ LocalOkaRing.fromPolynomial (R j)
  let E' := fun (j : Fin p) (i : Fin p) ↦
    LocalOkaRing.fromPolynomial (E j i).val
  let H := R' + Pi.single zero S
  have hG' : G = H + ∑ (j : Fin p), (A j) • (E' j) := by
    funext i
    simp only [Pi.add_apply, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, H, hAR', R', Pi.add_apply]
    rw [add_comm (A i * (F' zero)) (R' i)]
    simp only [R', add_assoc]
    congr
    by_cases h : i = zero
    · simp only [h, Pi.single_eq_same, Pi.add_apply, Pi.neg_apply,
      Submodule.coe_add, NegMemClass.coe_neg, map_add, map_neg, S, E', E, Fd, F']
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
      simp only [mul_neg, Finset.sum_neg_distrib, add_neg_cancel_left]
      rw [Fintype.sum_eq_single zero]
      · simp only [Pi.single_eq_same]
      · intro x hx
        rw [Pi.single_eq_of_ne (Ne.symm hx)]
        simp only [ZeroMemClass.coe_zero, map_zero, mul_zero]
    · simp only [ne_eq, h, not_false_eq_true, Pi.single_eq_of_ne, Pi.add_apply, Pi.neg_apply,
      Submodule.coe_add, NegMemClass.coe_neg, map_add, map_neg, ZeroMemClass.coe_zero, map_zero,
      neg_zero, zero_add, E', E]
      let ff' (x : Fin p) :=
        (A ↑x) * LocalOkaRing.fromPolynomial
          ↑(Pi.single (M := fun _ ↦ (LocalOkaRing (Fin n))[X]_d) x (Fd zero) i)
      have hh (x : Fin p) (hx : x ≠ i) : (ff' x) = 0 := by
        simp only [mul_eq_zero, ff']
        right
        rw [Pi.single_eq_of_ne _ _]
        · simp only [ZeroMemClass.coe_zero, map_zero]
        · exact hx.symm
      rw [Fintype.sum_eq_single i]
      · simp only [Pi.single_eq_same, F', Fd]
      · intro x hx
        rw [Pi.single_eq_of_ne (Ne.symm hx)]
        simp only [ZeroMemClass.coe_zero, map_zero, mul_zero]
  have hH : (H ∈ KK_deg (2 * d) F') := by
    sorry
  have hE' : ∀ (j : Fin p), (E' j ∈ KK_deg (2 * d) F') := by
    intro j
    simp only [KK_deg, E']
    refine Submodule.subset_span (R := LocalOkaRing (Fin (n + 1))) ?_
    simp only [Submodule.carrier_eq_coe, Submodule.map_coe, Set.mem_image, SetLike.mem_coe]
    let Ej : Fin p → (LocalOkaRing (Fin n))[X]_(2 * d) :=
      fun i ↦
        ⟨(E j i: (LocalOkaRing (Fin n))[X]),
        Polynomial.degreeLT_mono (R := LocalOkaRing (Fin n)) (by omega) (E j i).property⟩
    use Ej
    constructor
    · simp only [K_deg, LinearMap.mem_ker, LinearMap.coe_comp, LinearMap.coe_restrictScalars,
      Function.comp_apply, Module.Basis.constr_apply_fintype, Pi.basisFun_equivFun,
      LinearEquiv.refl_apply, smul_eq_mul, polyInclPi, Ej]
      simp only [LinearMap.coe_piMap, Pi.map_apply]
      simp only [polyIncl, LocalOkaRing.fromPolynomialAlg, AlgHom.toRingHom_eq_coe,
        LinearMap.coe_comp, LinearMap.coe_coe, AlgHom.coe_mk, RingHom.coe_coe,
        Submodule.coe_subtype, Function.comp_apply, F']
      have hpoly : ∑ x, ↑(E j x) * (F x) = 0 := by
        simp only [E]
        have hres : ∑ x, ↑(E j x) * (F x) =
            ∑ x ∈ {zero, j}, ↑(E j x) * (F x) := by
          symm
          apply Fintype.sum_subset
          intro i hi
          by_contra hc
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
          simp only [Pi.add_apply, Pi.neg_apply, Submodule.coe_add, NegMemClass.coe_neg, ne_eq,
            mul_eq_zero, not_or, E] at hi
          rw [Pi.single_eq_of_ne hc.2, Pi.single_eq_of_ne hc.1] at hi
          simp only [ZeroMemClass.coe_zero, neg_zero, add_zero, not_true_eq_false, false_and] at hi
        rw [hres]
        by_cases hj : j = zero
        · simp only [hj]
          have hE : E zero = (fun _ ↦ 0) := by
            simp only [neg_add_cancel, E]
            trivial
          rw [hE]
          simp only [Finset.mem_singleton, Finset.insert_eq_of_mem, ZeroMemClass.coe_zero, zero_mul,
            Finset.sum_const_zero]
        · rw [Finset.sum_pair (Ne.symm hj)]
          simp only [Pi.add_apply, Pi.neg_apply, Pi.single_eq_same, Submodule.coe_add,
            NegMemClass.coe_neg, E, Fd]
          rw [Pi.single_eq_of_ne hj]
          rw [Pi.single_eq_of_ne (Ne.symm hj)]
          simp only [ZeroMemClass.coe_zero, add_zero, neg_mul, neg_zero, zero_add, mul_comm,
            neg_add_cancel]
      have hpoly' := congrArg LocalOkaRing.fromPolynomial hpoly
      simp only [map_sum, map_mul, map_zero] at hpoly'
      exact hpoly'
    · simp only [polyInclPi, LinearMap.coe_piMap]
      funext i
      simp only [polyIncl, LinearMap.coe_comp, LinearMap.coe_coe, Submodule.coe_subtype,
        Pi.map_apply, Function.comp_apply]
      rfl
  rw [hG']
  refine Submodule.add_mem (KK_deg (2 * d) F') hH ?_
  apply Submodule.sum_mem (KK_deg (2 * d) F')
  intro i hi
  exact Submodule.smul_mem _ _ (hE' i)



theorem oka_lemma_weierstrass (p : ℕ) (d : ℕ)
    (hp : 0 < p)
    (F : Fin p → (LocalOkaRing (Fin n))[X])
    (hF : ∀ j, (F j).degree < d)
    (hF' : ∀ j, (F j).Monic)
    (hF₁ : IsLocalWeierstrassPolynomial (Polynomial.map
      (Subring.subtype (localOkaSubring _).toSubring) (F ⟨0, hp⟩))) :
    letI F' (j : Fin p) : LocalOkaRing (Fin (n + 1)) :=
      LocalOkaRing.fromPolynomial (F j)
    LinearMap.ker (linOfFun F') = KK_deg (2 * d) F' := by
  apply le_antisymm
  · exact oka_lemma_weierstrass_lhs_containedIn_rhs p d hp F hF hF' hF₁
  · exact oka_lemma_weierstrass_rhs_containedIn_lhs _ _ _
