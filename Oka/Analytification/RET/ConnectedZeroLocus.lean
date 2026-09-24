/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Oka.Analytification.RET.RootCover

/-!
# The zero locus of a prime ideal is connected

For a prime ideal `I` of `ℂ[z₁, …, z_n]`, the zero locus `Z(I) ⊆ ℂ^n` is connected in the
Euclidean topology, provided that `Z(I) ∖ {f = 0}` is dense in `Z(I)` for every `f ∉ I`
(`ComplexAnalytic.isPreconnected_zeroLocus_of_isPrime`).

Let `A = ℂ[z] ⧸ I`. By Noether normalisation `A` is finite over a polynomial ring
`R = ℂ[x₁, …, x_d]`. A primitive element `t ∈ A` of `Frac A` over `Frac R` has an irreducible
monic minimal polynomial `P ∈ R[T]`, and there are nonzero `c, δ ∈ R` such that `c A ⊆ R[t]` and
`δ ∈ (P, P')` (`ComplexAnalytic.exists_primitive_presentation`). Off `cδ = 0` the points of
`Z(I)` are parametrised continuously by the root cover `{(w, τ) | c(w)δ(w) ≠ 0, P(w, τ) = 0}`,
which is connected by `ComplexAnalytic.isPreconnected_rootCover`, and the part of `Z(I)` off
`cδ = 0` is dense.

## Main results

- `ComplexAnalytic.exists_primitive_presentation`: a primitive element of a finite extension of
  domains over a polynomial ring.
- `ComplexAnalytic.isPreconnected_zeroLocus_of_isPrime`: the zero locus of a prime ideal is
  connected.

## References

- David Mumford, *Algebraic Geometry I: Complex Projective Varieties*, (4.16)
-/

open Polynomial Filter Topology IntermediateField

namespace ComplexAnalytic

noncomputable section

/-! ### Algebra -/

section Algebra

variable {d : ℕ} {A : Type*} [CommRing A] [IsDomain A] [Algebra (MvPolynomial (Fin d) ℂ) A]
  [Module.Finite (MvPolynomial (Fin d) ℂ) A] [FaithfulSMul (MvPolynomial (Fin d) ℂ) A]

attribute [local instance] FractionRing.liftAlgebra

/-- **A primitive element of a finite extension of domains of a polynomial ring over `ℂ`.** There
is `t ∈ A` with an irreducible monic minimal polynomial `P` over `R = ℂ[x₁, …, x_d]` generating
the kernel of `R[T] → A`, a nonzero `c ∈ R` with `c A ⊆ R[t]` and a nonzero `δ ∈ R ∩ (P, P')`. -/
theorem exists_primitive_presentation :
    ∃ (t : A) (P : (MvPolynomial (Fin d) ℂ)[X]) (c δ : MvPolynomial (Fin d) ℂ),
      P.Monic ∧ Irreducible P ∧ aeval t P = 0 ∧
      (∀ H : (MvPolynomial (Fin d) ℂ)[X], aeval t H = 0 → P ∣ H) ∧
      c ≠ 0 ∧ (∀ a : A, ∃ H : (MvPolynomial (Fin d) ℂ)[X], aeval t H = c • a) ∧
      δ ≠ 0 ∧ ∃ U V : (MvPolynomial (Fin d) ℂ)[X], U * P + V * derivative P = C δ := by
  classical
  set R := MvPolynomial (Fin d) ℂ
  set L := FractionRing R
  set K := FractionRing A
  -- a primitive element in `A`
  obtain ⟨α, hα⟩ := Field.exists_primitive_element L K
  obtain ⟨a, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := A) α
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  obtain ⟨r, hr, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (Ideal.comap_ne_bot_of_integral_mem hs0 (Ideal.mem_span_singleton_self s)
      (Algebra.IsIntegral.isIntegral (R := R) s))
  obtain ⟨s', hs'⟩ := Ideal.mem_span_singleton'.1 (Ideal.mem_comap.1 hr)
  set t := a * s'
  have hsK : algebraMap A K s ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective A K)).2 hs0
  have hrL : algebraMap R L r ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R L)).2 hr0
  have ht : algebraMap A K t * algebraMap A K s = algebraMap L K (algebraMap R L r) *
      algebraMap A K a := by
    rw [← map_mul, mul_assoc, hs', map_mul, mul_comm, ← IsScalarTower.algebraMap_apply R A K,
      IsScalarTower.algebraMap_apply R L K]
  have hprim : L⟮algebraMap A K t⟯ = ⊤ := by
    refine eq_top_iff.2 (hα ▸ IntermediateField.adjoin_simple_le_iff.2 ?_)
    have : algebraMap A K a / algebraMap A K s =
        (algebraMap L K (algebraMap R L r))⁻¹ * algebraMap A K t := by
      rw [div_eq_iff hsK, mul_assoc, ht, ← mul_assoc,
        inv_mul_cancel₀ ((_root_.map_ne_zero _).2 hrL), one_mul]
    rw [this, ← map_inv₀]
    exact IntermediateField.mul_mem _ (IntermediateField.algebraMap_mem _ _)
      (IntermediateField.mem_adjoin_simple_self _ _)
  -- the minimal polynomial
  have hti : IsIntegral R t := Algebra.IsIntegral.isIntegral t
  set P := minpoly R t
  have hPL : minpoly L (algebraMap A K t) = P.map (algebraMap R L) :=
    minpoly.isIntegrallyClosed_eq_field_fractions L K hti
  -- `c A ⊆ R[t]`
  have hmul (a : A) : ∃ b : R, b ≠ 0 ∧ ∃ H : R[X], aeval t H = b • a := by
    have hmem : algebraMap A K a ∈ (L⟮algebraMap A K t⟯).toSubalgebra := by
      rw [hprim]
      trivial
    rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic _), Algebra.adjoin_singleton_eq_range_aeval] at hmem
    obtain ⟨q, hq⟩ := hmem
    change aeval _ q = _ at hq
    obtain ⟨b, hb, hbq⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors R) q
    refine ⟨b, nonZeroDivisors.ne_zero hb,
      IsLocalization.integerNormalization (nonZeroDivisors R) q, IsFractionRing.injective A K ?_⟩
    rw [← aeval_algebraMap_apply, ← aeval_map_algebraMap L, hbq, ← algebraMap_smul L b q,
      map_smul, hq, Algebra.smul_def, Algebra.smul_def, map_mul,
      ← IsScalarTower.algebraMap_apply R L K, ← IsScalarTower.algebraMap_apply R A K]
  choose b hb H hH using hmul
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := R) (M := A)
  set c := ∏ a ∈ S, b a
  have hc0 : c ≠ 0 := Finset.prod_ne_zero_iff.2 fun a _ ↦ hb a
  let N : Submodule R A :=
    { carrier := {a | ∃ H : R[X], aeval t H = c • a}
      add_mem' := by
        rintro _ _ ⟨H₁, h₁⟩ ⟨H₂, h₂⟩
        exact ⟨H₁ + H₂, by rw [map_add, h₁, h₂, smul_add]⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro r' _ ⟨H₁, h₁⟩
        refine ⟨C r' * H₁, ?_⟩
        rw [map_mul, aeval_C, h₁, ← Algebra.smul_def, smul_comm] }
  have hN : N = ⊤ := by
    refine eq_top_iff.2 (hS ▸ Submodule.span_le.2 fun a ha ↦ ?_)
    refine ⟨C (∏ x ∈ S.erase a, b x) * H a, ?_⟩
    rw [map_mul, aeval_C, hH, ← Algebra.smul_def, smul_smul, Finset.prod_erase_mul S b ha]
  -- `δ ∈ (P, P')`
  have hsepL : (P.map (algebraMap R L)).Separable := by
    rw [← hPL]
    exact Algebra.IsSeparable.isSeparable L _
  obtain ⟨U, V, hUV⟩ := hsepL
  obtain ⟨bU, hbU, hU⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors R) U
  obtain ⟨bV, hbV, hV⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors R) V
  refine ⟨t, P, c, bU * bV, minpoly.monic hti, minpoly.irreducible hti, minpoly.aeval R t,
    fun H hH ↦ minpoly.isIntegrallyClosed_dvd hti hH, hc0, fun a ↦ ?_,
    mul_ne_zero (nonZeroDivisors.ne_zero hbU) (nonZeroDivisors.ne_zero hbV),
    C bV * IsLocalization.integerNormalization (nonZeroDivisors R) U,
    C bU * IsLocalization.integerNormalization (nonZeroDivisors R) V, ?_⟩
  · have : a ∈ N := hN ▸ Submodule.mem_top
    exact this
  · refine map_injective _ (IsFractionRing.injective R L) ?_
    simp only [Polynomial.map_add, Polynomial.map_mul, map_C, hU, hV, map_mul]
    rw [← algebraMap_smul L bU U, ← algebraMap_smul L bV V, smul_eq_C_mul, smul_eq_C_mul,
      ← derivative_map]
    linear_combination (C (algebraMap R L bU) * C (algebraMap R L bV)) * hUV

end Algebra

/-- Let `P` generate the kernel of `R[T] → A`, `T ↦ t`, and let `c A ⊆ R[t]`. If a ring map
`ev : R[T] → F` to a domain kills `P` and the `G i` but not `c`, then the ideal of `A` generated by
the images `G i (t)` is proper. -/
theorem one_notMem_span_aeval {R A F : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [CommRing F] [IsDomain F] {t : A} {P : R[X]} (hdvd : ∀ H : R[X], aeval t H = 0 → P ∣ H)
    {c : R} (hc : ∀ a : A, ∃ H : R[X], aeval t H = c • a) (ev : R[X] →+* F) (hP : ev P = 0)
    (hc0 : ev (C c) ≠ 0) {ι : Type*} (G : ι → R[X]) (hG : ∀ i, ev (G i) = 0) :
    (1 : A) ∉ Ideal.span (Set.range fun i ↦ aeval t (G i)) := by
  have hker (H H' : R[X]) (h : aeval t H = aeval t H') : ev H = ev H' := by
    obtain ⟨Q, hQ⟩ := hdvd (H - H') (by rw [map_sub, h, sub_self])
    rw [← sub_eq_zero, ← map_sub, hQ, map_mul, hP, zero_mul]
  let J : Ideal A :=
    { carrier := {a | ∀ H : R[X], aeval t H = c • a → ev H = 0}
      add_mem' := by
        intro a b ha hb H hH
        obtain ⟨Ha, hHa⟩ := hc a
        obtain ⟨Hb, hHb⟩ := hc b
        rw [hker H (Ha + Hb) (by rw [hH, map_add, hHa, hHb, smul_add]), map_add, ha Ha hHa,
          hb Hb hHb, add_zero]
      zero_mem' := fun H hH ↦ by rw [hker H 0 (by rw [hH, smul_zero, map_zero]), map_zero]
      smul_mem' := by
        intro b a ha H hH
        obtain ⟨Ha, hHa⟩ := hc a
        obtain ⟨Hb, hHb⟩ := hc b
        have := hker (C c * H) (Hb * Ha) (by
          rw [map_mul, map_mul, aeval_C, hH, hHb, hHa, smul_eq_mul, Algebra.smul_def,
            Algebra.smul_def, Algebra.smul_def]
          ring)
        rw [map_mul, map_mul, ha Ha hHa, mul_zero] at this
        exact (mul_eq_zero.1 this).resolve_left hc0 }
  have hle : Ideal.span (Set.range fun i ↦ aeval t (G i)) ≤ J := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨i, rfl⟩ H hH
    rw [hker H (C c * G i) (by rw [hH, map_mul, aeval_C, Algebra.smul_def]), map_mul, hG,
      mul_zero]
  exact fun h ↦ hc0 (hle h (C c) (by rw [aeval_C, Algebra.smul_def, mul_one]))

/-! ### The zero locus -/

/-- **The zero locus of a prime ideal of `ℂ[z₁, …, z_n]` is connected**, provided that for every
`f ∉ I` the part of the zero locus where `f` does not vanish is dense in it. -/
theorem isPreconnected_zeroLocus_of_isPrime {σ : Type*} [Finite σ]
    (I : Ideal (MvPolynomial σ ℂ)) [I.IsPrime]
    (hdense : ∀ f ∉ I, {z : σ → ℂ | ∀ g ∈ I, MvPolynomial.eval z g = 0} ⊆
      closure {z : σ → ℂ | (∀ g ∈ I, MvPolynomial.eval z g = 0) ∧ MvPolynomial.eval z f ≠ 0}) :
    IsPreconnected {z : σ → ℂ | ∀ g ∈ I, MvPolynomial.eval z g = 0} := by
  classical
  set Y := {z : σ → ℂ | ∀ g ∈ I, MvPolynomial.eval z g = 0}
  obtain ⟨d, φ, hφ, hfin⟩ := exists_finite_inj_algHom_of_fg ℂ (MvPolynomial σ ℂ ⧸ I)
  letI : Algebra (MvPolynomial (Fin d) ℂ) (MvPolynomial σ ℂ ⧸ I) := φ.toRingHom.toAlgebra
  haveI : Module.Finite (MvPolynomial (Fin d) ℂ) (MvPolynomial σ ℂ ⧸ I) := hfin
  haveI : FaithfulSMul (MvPolynomial (Fin d) ℂ) (MvPolynomial σ ℂ ⧸ I) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 hφ
  obtain ⟨t, P, c, δ, hPm, hPirr, hPt, hPdvd, hc0, hc, hδ0, U, V, hUV⟩ :=
    exists_primitive_presentation (d := d) (A := MvPolynomial σ ℂ ⧸ I)
  have hφa (r : MvPolynomial (Fin d) ℂ) :
      algebraMap (MvPolynomial (Fin d) ℂ) (MvPolynomial σ ℂ ⧸ I) r = φ r := rfl
  -- evaluation at the points of the zero locus
  let lift : MvPolynomial σ ℂ ⧸ I → MvPolynomial σ ℂ := fun a ↦
    (Ideal.Quotient.mk_surjective a).choose
  have hlift (a : MvPolynomial σ ℂ ⧸ I) : Ideal.Quotient.mk I (lift a) = a :=
    (Ideal.Quotient.mk_surjective a).choose_spec
  let ev (z : σ → ℂ) (hz : z ∈ Y) : (MvPolynomial σ ℂ ⧸ I) →ₐ[ℂ] ℂ :=
    Ideal.Quotient.liftₐ I (MvPolynomial.aeval z) fun g hg ↦ by
      exact hz g hg
  have hevmk (z : σ → ℂ) (hz : z ∈ Y) (g : MvPolynomial σ ℂ) :
      ev z hz (Ideal.Quotient.mk I g) = MvPolynomial.eval z g := by
    simp [ev, MvPolynomial.coe_aeval_eq_eval]
  have hev (z : σ → ℂ) (hz : z ∈ Y) (a : MvPolynomial σ ℂ ⧸ I) :
      ev z hz a = MvPolynomial.eval z (lift a) := by
    conv_lhs => rw [← hlift a]
    exact hevmk z hz _
  let xz : (σ → ℂ) → Fin d → ℂ := fun z i ↦ MvPolynomial.eval z (lift (φ (MvPolynomial.X i)))
  let tz : (σ → ℂ) → ℂ := fun z ↦ MvPolynomial.eval z (lift t)
  have hevφ (z : σ → ℂ) (hz : z ∈ Y) (r : MvPolynomial (Fin d) ℂ) :
      ev z hz (φ r) = MvPolynomial.eval (xz z) r := by
    have : (ev z hz).comp φ = MvPolynomial.aeval (xz z) :=
      MvPolynomial.algHom_ext fun i ↦ by simp [hev, xz]
    rw [← MvPolynomial.coe_aeval_eq_eval, ← this]
    rfl
  have hkey (z : σ → ℂ) (hz : z ∈ Y) (H : (MvPolynomial (Fin d) ℂ)[X]) :
      ev z hz (aeval t H) = (H.map (MvPolynomial.eval (xz z))).eval (tz z) := by
    have h₁ : (ev z hz : (MvPolynomial σ ℂ ⧸ I) →+* ℂ).comp
        (algebraMap (MvPolynomial (Fin d) ℂ) _) = MvPolynomial.eval (xz z) :=
      RingHom.ext fun r ↦ hevφ z hz r
    rw [aeval_def, eval_map, ← h₁]
    exact (hom_eval₂ H _ (ev z hz : (MvPolynomial σ ℂ ⧸ I) →+* ℂ) t).trans
      (congrArg (fun x ↦ eval₂ _ x H) (hev z hz t))
  -- the root cover
  have hsep (w : Fin d → ℂ) (hw : MvPolynomial.eval w (c * δ) ≠ 0) :
      (P.map (MvPolynomial.eval w)).Separable := by
    rw [map_mul] at hw
    have hδw : MvPolynomial.eval w δ ≠ 0 := right_ne_zero_of_mul hw
    have := congrArg (Polynomial.map (MvPolynomial.eval w)) hUV
    simp only [Polynomial.map_add, Polynomial.map_mul, map_C, ← derivative_map] at this
    refine ⟨C (MvPolynomial.eval w δ)⁻¹ * U.map (MvPolynomial.eval w),
      C (MvPolynomial.eval w δ)⁻¹ * V.map (MvPolynomial.eval w), ?_⟩
    calc _ = C (MvPolynomial.eval w δ)⁻¹ * (U.map (MvPolynomial.eval w) *
          P.map (MvPolynomial.eval w) + V.map (MvPolynomial.eval w) *
            derivative (P.map (MvPolynomial.eval w))) := by ring
      _ = 1 := by rw [this, ← C_mul, inv_mul_cancel₀ hδw, C_1]
  have hE := isPreconnected_rootCover hPm hPirr (mul_ne_zero hc0 hδ0) hsep
  have hcw (w : Fin d → ℂ) (hw : MvPolynomial.eval w (c * δ) ≠ 0) : MvPolynomial.eval w c ≠ 0 := by
    rw [map_mul] at hw
    exact left_ne_zero_of_mul hw
  choose Hs hHs using fun s : σ ↦ hc (Ideal.Quotient.mk I (MvPolynomial.X s))
  let Φ : (Fin d → ℂ) × ℂ → σ → ℂ := fun q s ↦
    ((Hs s).map (MvPolynomial.eval q.1)).eval q.2 / MvPolynomial.eval q.1 c
  have hΦc : ContinuousOn Φ {q : (Fin d → ℂ) × ℂ | MvPolynomial.eval q.1 (c * δ) ≠ 0 ∧
      (P.map (MvPolynomial.eval q.1)).IsRoot q.2} :=
    continuousOn_pi.2 fun s ↦ (continuous_eval_map_eval (Hs s)).continuousOn.div
      ((MvPolynomial.continuous_eval c).comp continuous_fst).continuousOn
      fun q hq ↦ hcw q.1 hq.1
  have hΦz (z : σ → ℂ) (hz : z ∈ Y) (hc' : MvPolynomial.eval (xz z) c ≠ 0) :
      Φ (xz z, tz z) = z := by
    funext s
    have := hkey z hz (Hs s)
    rw [hHs s, Algebra.smul_def, map_mul, hφa, hevφ, hevmk, MvPolynomial.eval_X] at this
    change ((Hs s).map (MvPolynomial.eval (xz z))).eval (tz z) / _ = _
    rw [← this]
    field_simp
  -- every point of the root cover comes from the zero locus
  have hexists (w : Fin d → ℂ) (τ : ℂ) (hw : MvPolynomial.eval w c ≠ 0)
      (hτ : (P.map (MvPolynomial.eval w)).IsRoot τ) :
      ∃ z, ∃ hz : z ∈ Y, xz z = w ∧ tz z = τ := by
    let G : Option (Fin d) → (MvPolynomial (Fin d) ℂ)[X] := fun o ↦
      o.elim (X - C (MvPolynomial.C τ)) fun i ↦ C (MvPolynomial.X i) - C (MvPolynomial.C (w i))
    let evw : (MvPolynomial (Fin d) ℂ)[X] →+* ℂ :=
      (Polynomial.evalRingHom τ).comp (Polynomial.mapRingHom (MvPolynomial.eval w))
    have h1 := one_notMem_span_aeval hPdvd hc evw (by simpa [evw] using hτ.eq_zero)
      (by simpa [evw] using hw) G (by rintro (_ | i) <;> simp [G, evw])
    obtain ⟨M, hM, hJM⟩ := Ideal.exists_le_maximal _ ((Ideal.ne_top_iff_one _).2 h1)
    have hM' : (M.comap (Ideal.Quotient.mk I)).IsMaximal :=
      Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
    obtain ⟨z, hz⟩ := MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton.1 hM'
    have hmemM (g : MvPolynomial σ ℂ) :
        Ideal.Quotient.mk I g ∈ M ↔ MvPolynomial.eval z g = 0 := by
      rw [← Ideal.mem_comap, hz, MvPolynomial.mem_vanishingIdeal_singleton_iff]
      rfl
    have hzY : z ∈ Y := fun g hg ↦ (hmemM g).1 (by
      rw [Ideal.Quotient.eq_zero_iff_mem.2 hg]
      exact M.zero_mem)
    have hMG (o : Option (Fin d)) : aeval t (G o) ∈ M := hJM (Ideal.subset_span ⟨o, rfl⟩)
    have hC (x : ℂ) : aeval t (C (MvPolynomial.C x) : (MvPolynomial (Fin d) ℂ)[X]) =
        Ideal.Quotient.mk I (MvPolynomial.C x) := by
      rw [aeval_C, hφa, ← MvPolynomial.algebraMap_eq, φ.commutes]
      rfl
    refine ⟨z, hzY, funext fun i ↦ ?_, ?_⟩
    · have h := hMG (some i)
      have e : aeval t (G (some i)) =
          Ideal.Quotient.mk I (lift (φ (MvPolynomial.X i)) - MvPolynomial.C (w i)) := by
        simp only [G, Option.elim_some, map_sub, aeval_C, hφa, hlift]
        rw [← hC (w i), aeval_C, hφa]
      rw [e, hmemM, map_sub, MvPolynomial.eval_C, sub_eq_zero] at h
      exact h
    · have h := hMG none
      have e : aeval t (G none) = Ideal.Quotient.mk I (lift t - MvPolynomial.C τ) := by
        simp only [G, Option.elim_none, map_sub, aeval_X, hlift]
        rw [← hC τ]
      rw [e, hmemM, map_sub, MvPolynomial.eval_C, sub_eq_zero] at h
      exact h
  -- the part of the zero locus off `cδ = 0` is connected
  have himage : Φ '' {q : (Fin d → ℂ) × ℂ | MvPolynomial.eval q.1 (c * δ) ≠ 0 ∧
      (P.map (MvPolynomial.eval q.1)).IsRoot q.2} =
        {z | z ∈ Y ∧ MvPolynomial.eval (xz z) (c * δ) ≠ 0} := by
    ext z
    constructor
    · rintro ⟨⟨w, τ⟩, ⟨hw, hτ⟩, rfl⟩
      obtain ⟨z, hz, rfl, rfl⟩ := hexists w τ (hcw w hw) hτ
      rw [hΦz z hz (hcw _ hw)]
      exact ⟨hz, hw⟩
    · rintro ⟨hz, hw⟩
      refine ⟨(xz z, tz z), ⟨hw, ?_⟩, hΦz z hz (hcw _ hw)⟩
      change eval (tz z) (P.map (MvPolynomial.eval (xz z))) = 0
      rw [← hkey z hz P, hPt, map_zero]
  have hYW := himage ▸ hE.image Φ hΦc
  -- density
  have hf : lift (φ (c * δ)) ∉ I := fun h ↦ by
    have := Ideal.Quotient.eq_zero_iff_mem.2 h
    rw [hlift] at this
    exact mul_ne_zero hc0 hδ0 (hφ (this.trans (map_zero φ).symm))
  have hset : {z : σ → ℂ | (∀ g ∈ I, MvPolynomial.eval z g = 0) ∧
      MvPolynomial.eval z (lift (φ (c * δ))) ≠ 0} =
        {z | z ∈ Y ∧ MvPolynomial.eval (xz z) (c * δ) ≠ 0} := by
    ext z
    refine and_congr_right fun hz ↦ ?_
    rw [← hev z hz, hevφ]
  exact hYW.subset_closure (fun z hz ↦ hz.1) (hset ▸ hdense _ hf)

end

end ComplexAnalytic
