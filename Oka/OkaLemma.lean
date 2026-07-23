import Oka.LocalOkaRing
import Oka.Weierstrass

open Polynomial

variable {n : ℕ}

noncomputable instance : Algebra (LocalOkaRing (Fin n))
    (LocalOkaRing (Fin (n + 1))) :=
  ((LocalOkaRing.fromPolynomial (n := n)).toRingHom.comp
    (Polynomial.C : LocalOkaRing (Fin n) →+*
      (LocalOkaRing (Fin n))[X])).toAlgebra

noncomputable def LocalOkaRing.fromPolynomialAlg :
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

theorem oka_lemma (p : ℕ) (d : ℕ)
    (F : Fin p → (LocalOkaRing (Fin n))[X]_d)
    (hF' : ∀ j, (F j).val.Monic) :
    letI F' (j : Fin p) : LocalOkaRing (Fin (n + 1)) :=
      polyIncl (F j)
    LinearMap.ker (linOfFun F') =
      Submodule.span (LocalOkaRing (Fin (n + 1)))
        (Submodule.map polyInclPi (K_deg d F')).carrier :=
  sorry

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

theorem oka_lemma_weierstrass_lhs_containedIn_rhs (n : ℕ) (p : ℕ) (d : ℕ)
    (hp : 0 < p)
    (F : Fin p → (LocalOkaRing (Fin n))[X])
    (hF : ∀ j, (F j).degree < d)
    (hF' : ∀ j, (F j).Monic)
    (hF₁ : IsLocalWeierstrassPolynomial (Polynomial.map
      (Subring.subtype (localOkaSubring _).toSubring) (F ⟨0, hp⟩))) :
    letI F' (j : Fin p) : LocalOkaRing (Fin (n + 1)) :=
      LocalOkaRing.fromPolynomial (F j)
    LinearMap.ker (linOfFun F') ≤ KK_deg d F' := by
  let F' (j : Fin p) : LocalOkaRing (Fin (n + 1)) :=
      LocalOkaRing.fromPolynomial (F j)
  let zero : Fin p := ⟨0, hp⟩
  let nonzero := {z : Fin p // z ≠ zero}
  let Fd (i : Fin p) : (LocalOkaRing (Fin n))[X]_d := ⟨F i, by
    simpa [Polynomial.mem_degreeLT] using hF i⟩
  let E : nonzero → (Fin p → (LocalOkaRing (Fin n))[X]_d) :=
    fun j ↦ - Pi.single zero (Fd j.1) + Pi.single j.1 (Fd zero)
  intro G hG
  rw [LinearMap.mem_ker] at hG
  simp only [Module.Basis.constr_apply_fintype, Pi.basisFun_equivFun, LinearEquiv.refl_apply,
    smul_eq_mul] at hG
  choose A R hAR hAR' using fun (j : Fin p) ↦ localweierstrass_division (F zero) hF₁ (G j)
  let S := ∑ (i : Fin p), (A i) * (F' i)
  let R' := fun (j : Fin p) ↦ LocalOkaRing.fromPolynomial (R j)
  let E' := fun (j : nonzero) (i : Fin p) ↦
    LocalOkaRing.fromPolynomial (E j i).val
  let H := R' + Pi.single zero S
  have hG' : G = H + ∑ (j : nonzero), (A j) • (E' j) := by
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
      let ff (x : Fin p) := A x * LocalOkaRing.fromPolynomial (F x)
      have hsplit : (∑ x, ff x) = ff zero + ∑ x : {x : Fin p // x ≠ zero}, ff ↑x := by
        calc
        (∑ x, ff x)
          = (ff zero) +  ∑ x ∈ ({zero}ᶜ : Finset _), ff ↑x :=
            Fintype.sum_eq_add_sum_compl zero ff
        _ = (ff zero) + ∑ x : {x : Fin p // x ≠ zero}, ff ↑x := by
            congr 1
            rw [Finset.sum_subtype ({zero}ᶜ : Finset _) _ ff]
            intro x
            simp only [Finset.mem_compl, Finset.mem_singleton, ne_eq]
      simp only [ne_eq, ff] at hsplit
      rw [hsplit, add_assoc]
      simp
      rw [←add_assoc]
      rw [add_neg_cancel]
      rw [Fintype.sum_eq_zero]
      simp
      intro j
      have j' := Ne.symm j.property
      simp only [Pi.single_eq_of_ne j' _, ZeroMemClass.coe_zero, map_zero, mul_zero]
    · simp [h, E', E]
      let ff' (x : Fin p) :=
        (A ↑x) * LocalOkaRing.fromPolynomial
          (Pi.single (M := fun _ ↦ (LocalOkaRing (Fin n))[X]) x (Fd zero) i)
      have hh (x : {y : nonzero // y ≠ i}) : (ff' x) = 0 := by
        simp only [ne_eq, mul_eq_zero, ff']
        rw [Pi.single_eq_of_ne _ _]
        simp only [map_zero, or_true]
        have hx := x.property
        exact hx.symm
      have hsplit : (∑ x : nonzero, ff' x) = ff' i + ∑ x : {y : nonzero // y ≠ i}, ff' x := by
        sorry
      simp [ff'] at hsplit
      sorry
  have hH : (H ∈ KK_deg d F') := by
    sorry
  have hE' : ∀ (j : nonzero), (E' j ∈ KK_deg d F') := by
    sorry
  rw [hG']
  refine Submodule.add_mem (KK_deg d F') hH ?_
  simp only [ne_eq, Set.mem_setOf_eq, nonzero]
  apply Submodule.sum_mem (KK_deg d F')
  intro i hi
  exact Submodule.smul_mem _ _ (hE' i)
