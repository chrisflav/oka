/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.RingTheory.MvPolynomial.CechProjective
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Interval

/-!
# The top Čech cohomology of `O(k)` on projective space is finitely generated: Laurent model

Let `ι` be a finite type with `card ι = n + 1`. The Laurent model of the Čech complex of `O(k)`
(`MvPolynomial.exists_eq_d_of_laurentPart`) is exact in degree `q ≥ 1`, except in degree `q = n`
for `k ≤ -n - 1`. In that degree, a cocycle `x` splits as `x = u + (x - u)` where `u` is its
component `proj univ` (the monomials `Xᵃ` with all `aⱼ < 0`). The rest `x - u` is a cocycle with
vanishing `univ`-component, hence a coboundary, and `u` takes values in the `R`-span of the
finitely many monomials `Xᵃ` with all `aⱼ < 0` and `deg a = k` (`MvPolynomial.topExponents`).
Since cochains are functions on the finite set `Fin (p + 2) → ι`, the cohomology is spanned by
finitely many cochains.

We state this uniformly in `p` and `k` (in all other cases the cohomology vanishes, and the
statement holds already with the given generators).

## Main results

- `MvPolynomial.exists_eq_sum_add_d_of_laurentPart`: there are finitely many cochains
  `s₀, …, s_{N-1}` with values in `laurentPart (im i) k` such that every cocycle `x` of degree
  `p + 1` with values in `laurentPart (im i) k` is `x = ∑ⱼ rⱼ • sⱼ + d p y`, with `y` again
  with values in `laurentPart (im i) k`.
- `MvPolynomial.exists_eq_sum_add_of_laurentPart`: the transfer to a complex `V` embedded into
  the Laurent model as in `MvPolynomial.exact_of_laurentPart`, with an `R`-action on `V (p + 1)`
  (given as a function `smul`) compatible with the embedding.
-/

open SimplexCochain

namespace MvPolynomial

variable {ι : Type*} {R : Type*} [CommRing R] [DecidableEq ι] [Fintype ι]

variable (ι) in
/-- A finite set of exponents containing all `a` with all `aⱼ < 0` and `deg a = k`: the
exponents with `k ≤ aⱼ ≤ -1` for all `j`. -/
noncomputable def topExponents (k : ℤ) : Finset (ι →₀ ℤ) :=
  (Fintype.piFinset fun _ : ι ↦ Finset.Icc k (-1)).map
    Finsupp.equivFunOnFinite.symm.toEmbedding

lemma mem_topExponents {k : ℤ} {a : ι →₀ ℤ} (ha : negSupp a = Finset.univ)
    (hk : a.degree = k) : a ∈ topExponents ι k := by
  rw [topExponents, Finset.mem_map_equiv, Equiv.symm_symm, Fintype.mem_piFinset]
  intro j
  have hneg : ∀ l, a l < 0 := fun l ↦ mem_negSupp.mp (ha ▸ Finset.mem_univ l)
  rw [Finsupp.equivFunOnFinite_apply, Finset.mem_Icc]
  refine ⟨?_, by have := hneg j; omega⟩
  rw [Finsupp.degree_eq_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ j)] at hk
  have : ∑ l ∈ Finset.univ.erase j, a l ≤ 0 :=
    Finset.sum_nonpos fun l _ ↦ (hneg l).le
  omega

lemma negSupp_eq_univ_of_mem_topExponents {k : ℤ} {a : ι →₀ ℤ} (ha : a ∈ topExponents ι k) :
    negSupp a = Finset.univ := by
  rw [topExponents, Finset.mem_map_equiv, Equiv.symm_symm, Fintype.mem_piFinset] at ha
  refine Finset.eq_univ_of_forall fun j ↦ mem_negSupp.mpr ?_
  have := Finset.mem_Icc.mp (ha j)
  rw [Finsupp.equivFunOnFinite_apply] at this
  omega

variable (ι R) in
/-- The index set of the generators of the top cohomology in degree `p + 1`: pairs `(i, a)` of a
simplex `i` and an exponent `a ∈ topExponents k` with `negSupp a ⊆ im i` and `deg a = k`. -/
noncomputable def topIndex (k : ℤ) (p : ℕ) : Finset ((Fin (p + 1) → ι) × (ι →₀ ℤ)) :=
  (Finset.univ ×ˢ topExponents ι k).filter fun ia ↦ negSupp ia.2 ⊆ im ia.1 ∧ ia.2.degree = k

variable (R) in
/-- The generator `Xᵃ` placed at the simplex `i`. -/
noncomputable def topGen {p : ℕ} (ia : (Fin (p + 1) → ι) × (ι →₀ ℤ)) :
    Cochain ι ((ι →₀ ℤ) →₀ R) p :=
  Pi.single ia.1 (Finsupp.single ia.2 1)

lemma topGen_mem {k : ℤ} {p : ℕ} {ia : (Fin (p + 1) → ι) × (ι →₀ ℤ)}
    (hia : ia ∈ topIndex ι k p) (i : Fin (p + 1) → ι) :
    topGen R ia i ∈ laurentPart R (im i) k := by
  obtain ⟨-, h⟩ := Finset.mem_filter.mp hia
  rw [topGen]
  by_cases hi : i = ia.1
  · subst hi
    rw [Pi.single_eq_same, mem_laurentPart]
    intro a ha
    rw [Finsupp.single_apply] at ha
    split_ifs at ha with hEq
    · exact hEq ▸ h
    · exact absurd rfl ha
  · rw [Pi.single_eq_of_ne hi]
    exact zero_mem _

omit [Fintype ι] in
lemma topGen_apply {p : ℕ} (ia : (Fin (p + 1) → ι) × (ι →₀ ℤ)) (i : Fin (p + 1) → ι)
    (a : ι →₀ ℤ) : topGen R ia i a = if ia = (i, a) then 1 else 0 := by
  obtain ⟨i', a'⟩ := ia
  by_cases hi : i = i'
  · subst hi
    by_cases ha : a = a' <;> simp [topGen, ha, eq_comm]
  · simp [topGen, Ne.symm hi]

/-- **The `univ`-component of a cochain** with values in `laurentPart (im i) k` is the
`R`-linear combination of the generators `topGen` indexed by `topIndex`. -/
lemma map_proj_univ_eq_sum {k : ℤ} {p : ℕ} (x : Cochain ι ((ι →₀ ℤ) →₀ R) p)
    (hx : ∀ i, x i ∈ laurentPart R (im i) k) :
    map ((laurentGrading ι R).proj Finset.univ) p x =
      ∑ ia ∈ topIndex ι k p, x ia.1 ia.2 • topGen R ia := by
  ext i a
  rw [Finset.sum_apply, Finsupp.finsetSum_apply, map_apply, laurentGrading_proj_apply]
  simp only [Pi.smul_apply, Finsupp.smul_apply, topGen_apply, smul_eq_mul, mul_ite, mul_one,
    mul_zero]
  rw [Finset.sum_ite_eq']
  by_cases hN : negSupp a = Finset.univ
  · rw [if_pos hN]
    split_ifs with hia
    · rfl
    · by_contra hxa
      obtain ⟨h₁, h₂⟩ := mem_laurentPart.mp (hx i) a hxa
      exact hia (Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, mem_topExponents hN h₂⟩, h₁, h₂⟩)
  · have hia : (i, a) ∉ topIndex ι k p := fun hia ↦ hN
      (negSupp_eq_univ_of_mem_topExponents (Finset.mem_product.mp (Finset.mem_filter.mp hia).1).2)
    rw [if_neg hN, if_neg hia]

section Finite

omit [Fintype ι]
variable [Finite ι]

/-- **The top Čech cohomology of `O(k)` is finitely generated** (Laurent model): there are
finitely many cochains `s₀, …, s_{N-1}` of degree `p + 1` with values in `laurentPart (im i) k`
such that every `(p + 1)`-cocycle `x` with values in `laurentPart (im i) k` is
`x = ∑ⱼ rⱼ • sⱼ + d p y` for some `rⱼ ∈ R` and a cochain `y` with values in
`laurentPart (im i) k`. This holds for all `k` and `p`; it has content only for
`p + 2 = card ι` and `k ≤ -card ι`, where the generators are the monomials `Xᵃ` with all
`aⱼ < 0` and `deg a = k`, placed at the simplices `i` with `im i = univ`. -/
theorem exists_eq_sum_add_d_of_laurentPart (k : ℤ) (p : ℕ) :
    ∃ (N : ℕ) (s : Fin N → Cochain ι ((ι →₀ ℤ) →₀ R) (p + 1)),
      (∀ j i, s j i ∈ laurentPart R (im i) k) ∧
      ∀ x : Cochain ι ((ι →₀ ℤ) →₀ R) (p + 1), (∀ i, x i ∈ laurentPart R (im i) k) →
        d (p + 1) x = 0 → ∃ (r : Fin N → R) (y : Cochain ι ((ι →₀ ℤ) →₀ R) p),
          (∀ i, y i ∈ laurentPart R (im i) k) ∧ x = ∑ j, r j • s j + d p y := by
  have := Fintype.ofFinite ι
  let T := topIndex ι k (p + 1)
  let e := T.equivFin
  refine ⟨T.card, fun j ↦ topGen R (e.symm j).1, fun j i ↦ topGen_mem (e.symm j).2 i,
    fun x hx hdx ↦ ?_⟩
  let π := laurentGrading ι R
  set u := map (π.proj Finset.univ) (p + 1) x with hu_def
  have hu : ∀ i, u i ∈ laurentPart R (im i) k := fun i ↦ by
    refine mem_laurentPart.mpr fun a ha ↦ mem_laurentPart.mp (hx i) a ?_
    simp only [hu_def, map_apply, π, laurentGrading_proj_apply] at ha
    split_ifs at ha
    · exact ha
    · exact absurd rfl ha
  have hxu : ∀ i, (x - u) i ∈ laurentPart R (im i) k := fun i ↦ sub_mem (hx i) (hu i)
  obtain ⟨hadm, hdeg⟩ := forall_mem_laurentPart_iff.mp hxu
  obtain ⟨y, hy, hyS, hdy⟩ := π.exists_eq_d (degreePart R k)
    (fun N m hm ↦ laurentGrading_proj_mem_degreePart N m hm) (x - u) hadm hdeg
    (by rw [map_sub, hu_def, d_map, hdx, map_zero, sub_zero])
    (Or.inr fun i ↦ by
      rw [Pi.sub_apply, map_sub, hu_def, map_apply, π.proj_proj, if_pos rfl, sub_self])
  refine ⟨fun j ↦ x (e.symm j).1.1 (e.symm j).1.2, y,
    forall_mem_laurentPart_iff.mpr ⟨hy, hyS⟩, ?_⟩
  have hS : u = ∑ j, x (e.symm j).1.1 (e.symm j).1.2 • topGen R (e.symm j).1 := by
    rw [hu_def, map_proj_univ_eq_sum x hx, ← Finset.sum_coe_sort T]
    exact (e.symm.sum_comp fun t : T ↦ x t.1.1 t.1.2 • topGen R t.1).symm
  beta_reduce
  rw [hdy, ← hS]
  abel

/-- **The top Čech cohomology of `O(k)` is finitely generated**, transferred to a complex `V`
which embeds into the Laurent model as in `exact_of_laurentPart` (`Φ` injective, compatible with
the differentials, with image the cochains with values in `laurentPart (im i) k`). The
`R`-action on `V (p + 1)` is an arbitrary function `smul` with `Φ (smul r v) = r • Φ v`: there are
finitely many `s₀, …, s_{N-1} : V (p + 1)` such that every cocycle `v` is
`v = ∑ⱼ smul rⱼ sⱼ + D p w`. This holds for all `k` and `p`. -/
theorem exists_eq_sum_add_of_laurentPart {k : ℤ} {V : ℕ → Type*} [∀ p, AddCommGroup (V p)]
    (D : ∀ p, V p →+ V (p + 1)) (Φ : ∀ p, V p →+ Cochain ι ((ι →₀ ℤ) →₀ R) p)
    (hΦ : ∀ p, Function.Injective (Φ p)) (hΦD : ∀ p v, Φ (p + 1) (D p v) = d p (Φ p v))
    (hΦmem : ∀ p v i, Φ p v i ∈ laurentPart R (im i) k)
    (hΦsurj : ∀ p x, (∀ i, x i ∈ laurentPart R (im i) k) → ∃ v, Φ p v = x)
    (p : ℕ) (smul : R → V (p + 1) → V (p + 1))
    (hΦsmul : ∀ r v, Φ (p + 1) (smul r v) = r • Φ (p + 1) v) :
    ∃ (N : ℕ) (s : Fin N → V (p + 1)), ∀ v, D (p + 1) v = 0 →
      ∃ (r : Fin N → R) (w : V p), v = ∑ j, smul (r j) (s j) + D p w := by
  obtain ⟨N, s, hs, H⟩ := exists_eq_sum_add_d_of_laurentPart (R := R) (ι := ι) k p
  choose s' hs' using fun j ↦ hΦsurj (p + 1) (s j) (hs j)
  refine ⟨N, s', fun v hv ↦ ?_⟩
  obtain ⟨r, y, hy, hxy⟩ := H (Φ (p + 1) v) (hΦmem _ v) (by rw [← hΦD, hv, map_zero])
  obtain ⟨w, rfl⟩ := hΦsurj p y hy
  refine ⟨r, w, hΦ _ ?_⟩
  rw [hxy, map_add, map_sum, hΦD]
  simp only [hΦsmul, hs']

end Finite

end MvPolynomial
