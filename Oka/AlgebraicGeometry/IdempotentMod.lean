/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
# Idempotents modulo `Tⁿ` attached to a splitting of the zero locus of `T`

Let `X` be a scheme, `T : Γ(X, ⊤)` a global function with zero locus `Z = X ∖ D(T)`, and
`Z = Z₁ ⊔ Z₂` a splitting into disjoint closed subsets. On an open `V`, a section `e ∈ Γ(X, V)` is
a **`Tⁿ`-idempotent for `Z₁`** (`Scheme.IsIdemMod`) if `e² - e ∈ (Tⁿ)` and, at points of `Z ∩ V`,
`e` is a unit exactly on `Z₁`.

* Such sections restrict to smaller opens (`Scheme.IsIdemMod.res`).
* On an affine `V` they exist for every `n` (`Scheme.exists_isIdemMod`): `Spec Γ(X, V) ⧸ (Tⁿ)` is
  homeomorphic to `Z ∩ V`, where `Z₁` is clopen.
* On an affine `V` they are unique modulo `Tⁿ` (`Scheme.IsIdemMod.sub_mem`), for `n ≥ 1`.
-/

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} (Z₁ : Set X)

/-- `e ∈ Γ(X, V)` is a `τⁿ`-idempotent for `Z₁`, where `τ ∈ Γ(X, V)`: `e² - e ∈ (τⁿ)`, and at the
points of `V` where `τ` vanishes, `e` is a unit exactly on `Z₁`. -/
def IsIdemMod {V : X.Opens} (τ : Γ(X, V)) (n : ℕ) (e : Γ(X, V)) : Prop :=
  e * e - e ∈ Ideal.span {τ ^ n} ∧
    ∀ x ∈ V, x ∉ X.basicOpen τ → (x ∈ X.basicOpen e ↔ x ∈ Z₁)

variable {Z₁}

lemma mem_basicOpen_restrict_iff {T : Γ(X, ⊤)} {V : X.Opens} {x : X} (hx : x ∈ V) :
    x ∈ X.basicOpen (T |_ V) ↔ x ∈ X.basicOpen T := by
  rw [TopCat.Presheaf.restrictOpen, TopCat.Presheaf.restrict, Scheme.basicOpen_res]
  exact ⟨fun h => h.2, fun h => ⟨hx, h⟩⟩

lemma IsIdemMod.mono {V : X.Opens} {τ : Γ(X, V)} {m n : ℕ} (hmn : n ≤ m) {e : Γ(X, V)}
    (he : IsIdemMod Z₁ τ m e) : IsIdemMod Z₁ τ n e := by
  refine ⟨?_, he.2⟩
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp he.1
  refine Ideal.mem_span_singleton'.mpr ⟨c * τ ^ (m - n), ?_⟩
  rw [← hc, mul_assoc, ← pow_add, Nat.sub_add_cancel hmn]

/-- Restriction of a `τⁿ`-idempotent along a ring map `r : Γ(X, V) → Γ(X, W)` which is a
restriction map. -/
lemma IsIdemMod.res {V W : X.Opens} (hWV : W ≤ V) {τ : Γ(X, V)} {n : ℕ} {e : Γ(X, V)}
    (he : IsIdemMod Z₁ τ n e) :
    IsIdemMod Z₁ (X.presheaf.map (homOfLE hWV).op τ) n (X.presheaf.map (homOfLE hWV).op e) := by
  set r := (X.presheaf.map (homOfLE hWV).op).hom
  refine ⟨?_, fun x hxW hxT => ?_⟩
  · obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp he.1
    refine Ideal.mem_span_singleton'.mpr ⟨r c, ?_⟩
    rw [← map_pow, ← map_mul, hc, map_sub, map_mul]
  · have hxT' : x ∉ X.basicOpen τ := by
      intro h
      apply hxT
      rw [Scheme.basicOpen_res]
      exact ⟨hxW, h⟩
    rw [← he.2 x (hWV hxW) hxT', Scheme.basicOpen_res]
    exact ⟨fun h => h.2, fun h => ⟨hxW, h⟩⟩

/-- In a ring, `u² - u ∈ J` implies `uᵐ - u ∈ J` for `m ≥ 1`. -/
lemma pow_sub_self_mem {A : Type*} [CommRing A] {J : Ideal A} {u : A} (hu : u * u - u ∈ J)
    (m : ℕ) : u ^ (m + 1) - u ∈ J := by
  induction m with
  | zero => simp
  | succ m ih =>
    have : u ^ (m + 2) - u = u * (u ^ (m + 1) - u) + (u * u - u) := by ring
    rw [this]
    exact J.add_mem (J.mul_mem_left _ ih) hu

/-- **Uniqueness of `τⁿ`-idempotents on affine opens**: two `τⁿ`-idempotents for `Z₁` on an
affine `V` agree modulo `τⁿ`, for `n ≥ 1`. -/
theorem IsIdemMod.sub_mem {V : X.Opens} (hV : IsAffineOpen V) {τ : Γ(X, V)} {n : ℕ}
    (hn : 1 ≤ n) {e e' : Γ(X, V)} (he : IsIdemMod Z₁ τ n e) (he' : IsIdemMod Z₁ τ n e') :
    e - e' ∈ Ideal.span {τ ^ n} := by
  set J := Ideal.span {τ ^ n}
  have key : ∀ {e e' : Γ(X, V)}, IsIdemMod Z₁ τ n e → IsIdemMod Z₁ τ n e' →
      e * (1 - e') ∈ J := by
    intro e e' he he'
    set u := e * (1 - e')
    have hu : u * u - u ∈ J := by
      have : u * u - u = (e * e - e) * (1 - e') ^ 2 + e * (e' * e' - e') := by
        simp only [u]
        ring
      rw [this]
      exact J.add_mem (J.mul_mem_right _ he.1) (J.mul_mem_left _ he'.1)
    have hle : X.basicOpen u ≤ X.basicOpen τ := by
      intro x hx
      have hxV : x ∈ V := X.basicOpen_le u hx
      rw [Scheme.basicOpen_mul] at hx
      by_contra hxT
      have hx1 : x ∈ Z₁ := (he.2 x hxV hxT).1 hx.1
      have hx2 : x ∈ X.basicOpen e' := (he'.2 x hxV hxT).2 hx1
      have hmul : x ∈ X.basicOpen (e' * (1 - e')) := by
        rw [Scheme.basicOpen_mul]
        exact ⟨hx2, hx.2⟩
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp he'.1
      have heq : e' * (1 - e') = τ ^ n * (-c) := by
        linear_combination hc
      rw [heq, Scheme.basicOpen_mul, Scheme.basicOpen_pow _ _ (by omega)] at hmul
      exact hxT hmul.1
    have hle' : PrimeSpectrum.basicOpen u ≤ PrimeSpectrum.basicOpen τ := by
      rw [← hV.fromSpec_preimage_basicOpen, ← hV.fromSpec_preimage_basicOpen]
      exact fun x hx => hle hx
    rw [PrimeSpectrum.basicOpen_le_basicOpen_iff] at hle'
    obtain ⟨k, hk⟩ := hle'
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp ((Ideal.span {τ}).mul_mem_left u hk)
    have hpow : u ^ ((k + 1) * n) ∈ J := by
      refine Ideal.mem_span_singleton'.mpr ⟨c ^ n, ?_⟩
      rw [pow_mul, ← mul_pow, hc, pow_succ']
    obtain ⟨m, hm⟩ : ∃ m, (k + 1) * n = m + 1 := ⟨(k + 1) * n - 1, by
      have : 1 ≤ (k + 1) * n := Nat.one_le_iff_ne_zero.mpr (by positivity)
      omega⟩
    rw [hm] at hpow
    have := J.sub_mem hpow (pow_sub_self_mem hu m)
    simpa using this
  have h1 := key he he'
  have h2 := key he' he
  have : e - e' = e * (1 - e') - e' * (1 - e) := by ring
  rw [this]
  exact J.sub_mem h1 h2

/-- **Existence of `τⁿ`-idempotents on affine opens.** Let `Z₁, Z₂` be disjoint closed subsets
covering the zero locus of `τ` in `V`. -/
theorem exists_isIdemMod {Z₂ : Set X} (hZ₁ : IsClosed Z₁) (hZ₂ : IsClosed Z₂)
    (hdisj : Disjoint Z₁ Z₂) {V : X.Opens} (hV : IsAffineOpen V) (τ : Γ(X, V))
    (hcov : ∀ x ∈ V, x ∉ X.basicOpen τ → x ∈ Z₁ ∨ x ∈ Z₂) {n : ℕ} (hn : 1 ≤ n) :
    ∃ e : Γ(X, V), IsIdemMod Z₁ τ n e := by
  set J := Ideal.span {τ ^ n}
  let q := Ideal.Quotient.mk J
  let φ : PrimeSpectrum (Γ(X, V) ⧸ J) → X := fun P => hV.fromSpec (PrimeSpectrum.comap q P)
  have hφc : Continuous φ :=
    hV.fromSpec.continuous.comp (PrimeSpectrum.continuous_comap q)
  have hφV (P : PrimeSpectrum (Γ(X, V) ⧸ J)) : φ P ∈ V := by
    rw [← SetLike.mem_coe, ← hV.range_fromSpec]
    exact ⟨_, rfl⟩
  -- the points `φ P` lie in the zero locus of `τ`
  have hφT (P : PrimeSpectrum (Γ(X, V) ⧸ J)) : φ P ∉ X.basicOpen τ := by
    intro h
    have h' : PrimeSpectrum.comap q P ∈ hV.fromSpec ⁻¹ᵁ X.basicOpen τ := h
    rw [hV.fromSpec_preimage_basicOpen] at h'
    apply h'
    change q τ ∈ P.asIdeal
    refine P.isPrime.mem_of_pow_mem n ?_
    have : q (τ ^ n) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
    rw [map_pow] at this
    rw [this]
    exact P.asIdeal.zero_mem
  have hS : IsClopen (φ ⁻¹' Z₁) := by
    refine ⟨hZ₁.preimage hφc, ?_⟩
    have : φ ⁻¹' Z₁ = (φ ⁻¹' Z₂)ᶜ := by
      ext P
      simp only [Set.mem_preimage, Set.mem_compl_iff]
      rcases hcov _ (hφV P) (hφT P) with h | h
      · exact ⟨fun _ h2 => hdisj.ne_of_mem h h2 rfl, fun _ => h⟩
      · exact ⟨fun h1 => absurd rfl (hdisj.ne_of_mem h1 h), fun h' => absurd h h'⟩
    rw [this]
    exact (hZ₂.preimage hφc).isOpen_compl
  obtain ⟨ē, hē, hSē⟩ := PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isClopen hS
  obtain ⟨e, rfl⟩ := Ideal.Quotient.mk_surjective ē
  refine ⟨e, ?_, fun x hxV hxT => ?_⟩
  · rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hē.eq, sub_self]
  · obtain ⟨P₀, rfl⟩ : x ∈ Set.range hV.fromSpec := by
      rw [hV.range_fromSpec]
      exact hxV
    have hT₀ : τ ∈ P₀.asIdeal := by
      by_contra h
      have h' : P₀ ∈ hV.fromSpec ⁻¹ᵁ X.basicOpen τ := by
        rw [hV.fromSpec_preimage_basicOpen]
        exact h
      exact hxT h'
    have hJ : J ≤ P₀.asIdeal := by
      rw [Ideal.span_le, Set.singleton_subset_iff]
      exact P₀.asIdeal.pow_mem_of_mem hT₀ n (by omega)
    obtain ⟨P, hP⟩ : P₀ ∈ Set.range (PrimeSpectrum.comap q) := by
      rw [range_comap_of_surjective _ q Ideal.Quotient.mk_surjective,
        Ideal.mk_ker]
      exact hJ
    have h1 : hV.fromSpec P₀ ∈ X.basicOpen e ↔ P₀ ∈ PrimeSpectrum.basicOpen e := by
      rw [← hV.fromSpec_preimage_basicOpen]
      rfl
    rw [h1, ← hP]
    change e ∉ (PrimeSpectrum.comap q P).asIdeal ↔ _
    rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
    change P ∈ PrimeSpectrum.basicOpen (q e) ↔ φ P ∈ Z₁
    rw [← SetLike.mem_coe, ← hSē]
    rfl

end AlgebraicGeometry.Scheme
