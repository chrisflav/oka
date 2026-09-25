/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.Analysis.Matrix.Normed
import Oka.Analytification.GAGA.CartanApprox
import Oka.Analytification.GAGA.CousinShrink

/-!
# Cartan's matrix lemma

Let `R ⊆ ℂ` be the closed rectangle with corners `p` and `q`, and `L ⊆ E` a compact set of
parameters (`E` finite-dimensional, e.g. `L` a closed box in `ℂ^{n-1}`). Let `F` be holomorphic
near `R × L` with values in the invertible elements of a finite-dimensional normed `ℂ`-algebra
`𝔸` (e.g. invertible matrices). Then `F = F₁ F₂` near `R × L`, where `F₁` is holomorphic and
invertible on a neighbourhood of `{Re z ≤ q.re} × L` and `F₂` on a neighbourhood of
`{Re z ≥ p.re, p.im ≤ Im z ≤ q.im} × L`.

In particular, for adjacent closed boxes `K₁ = [x₀, q.re] × [p.im, q.im] × L` and
`K₂ = [p.re, x₁] × [p.im, q.im] × L` with `K₁ ∩ K₂ = R × L`, every invertible holomorphic matrix
near `K₁ ∩ K₂` is a product of invertible holomorphic matrices near `K₁` and near `K₂`.

The proof combines the approximation of `F` by functions `G` which are holomorphic and invertible
on `ℂ × P` (`Complex.exists_approx_isUnit`) with the splitting of `F G⁻¹`, which is close to `1`
(`Complex.exists_mul_split_of_norm_sub_one_le`): `F = F₁ (F₂ G)`.

## Main results

- `Complex.exists_mul_split_of_isUnit`: **Cartan's lemma** for `𝔸`-valued functions.
- `Complex.exists_matrix_mul_split`: **Cartan's matrix lemma.**
- `Complex.exists_mul_split_closedBox`: Cartan's lemma for adjacent closed boxes
  `Complex.closedBox` in `ℂ^ι`, cut in the real direction of a coordinate.
- `Complex.exists_mul_split_closedBox_of_isOpen`: the version for given open neighbourhoods of
  the two boxes, i.e. merging of trivialisations over adjacent boxes.
-/

open Set
open scoped Ring

namespace Complex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

section Algebra

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [NormOneClass 𝔸]
  [FiniteDimensional ℂ 𝔸]

/-- **Cartan's lemma.** Let `F` be holomorphic with invertible values on an open `U ⊇ R × L`, where
`R = closedRectNhd p q 0` is the closed rectangle with corners `p`, `q` and `L` is compact. Then
there are `ε > 0` and an open `P ⊇ L` such that `F = F₁ F₂` on `rectNhd p q ε × P`, with `F₁`
holomorphic and invertible on `leftPlane q ε × P` and `F₂` on `rightStrip p q ε × P`. -/
theorem exists_mul_split_of_isUnit {p q : ℂ} (hre : p.re ≤ q.re) (him : p.im ≤ q.im)
    {L : Set E} (hL : IsCompact L) {U : Set (ℂ × E)} (hU : IsOpen U)
    (hRL : closedRectNhd p q 0 ×ˢ L ⊆ U) {F : ℂ × E → 𝔸} (hF : DifferentiableOn ℂ F U)
    (hFu : ∀ x ∈ U, IsUnit (F x)) :
    ∃ ε > 0, ∃ P : Set E, IsOpen P ∧ L ⊆ P ∧ ∃ F₁ F₂ : ℂ × E → 𝔸,
      DifferentiableOn ℂ F₁ (leftPlane q ε ×ˢ P) ∧ (∀ x ∈ leftPlane q ε ×ˢ P, IsUnit (F₁ x)) ∧
      DifferentiableOn ℂ F₂ (rightStrip p q ε ×ˢ P) ∧
      (∀ x ∈ rightStrip p q ε ×ˢ P, IsUnit (F₂ x)) ∧
      ∀ x ∈ rectNhd p q ε ×ˢ P, F x = F₁ x * F₂ x := by
  haveI : CompleteSpace 𝔸 := FiniteDimensional.complete ℂ 𝔸
  obtain ⟨ρ, hρ, P, hP, hLP, hPU, happrox⟩ := exists_approx_isUnit hre him hL hU hRL hF hFu
  obtain ⟨θ, hθ, hsplit⟩ := exists_mul_split_of_norm_sub_one_le (E := E) (𝔸 := 𝔸) hre him hρ
  obtain ⟨G, hG, hGu, hFG⟩ := happrox θ hθ
  have hsub : rectNhd p q ρ ×ˢ P ⊆ univ ×ˢ P := prod_mono (subset_univ _) subset_rfl
  obtain ⟨F₁, F₂, hF₁, hF₁u, hF₂, hF₂u, hH⟩ := hsplit hP (H := fun x ↦ F x * (G x)⁻¹ʳ)
    ((hF.mono hPU).mul ((hG.mono hsub).inverse fun x hx ↦ hGu x (hsub hx))) hFG
  refine ⟨ρ / 2, by positivity, P, hP, hLP, F₁, fun x ↦ F₂ x * G x, hF₁, hF₁u,
    hF₂.mul (hG.mono (prod_mono (subset_univ _) subset_rfl)),
    fun x hx ↦ (hF₂u x hx).mul (hGu x ⟨mem_univ _, hx.2⟩), fun x hx ↦ ?_⟩
  have hGx : IsUnit (G x) := hGu x ⟨mem_univ _, hx.2⟩
  rw [← mul_assoc, ← hH x hx, Ring.inverse_mul_cancel_right _ _ hGx]

end Algebra

section Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Cartan's matrix lemma.** Let `F` be a matrix of holomorphic functions on an open
`U ⊇ R × L` with invertible values, where `R = closedRectNhd p q 0` is the closed rectangle with
corners `p`, `q` and `L` is compact. Then there are `ε > 0`, an open `P ⊇ L` and matrices `F₁`,
`F₂` of holomorphic functions, invertible on `leftPlane q ε × P` resp. `rightStrip p q ε × P`,
with `F = F₁ F₂` on `rectNhd p q ε × P`. -/
theorem exists_matrix_mul_split {p q : ℂ} (hre : p.re ≤ q.re) (him : p.im ≤ q.im)
    {L : Set E} (hL : IsCompact L) {U : Set (ℂ × E)} (hU : IsOpen U)
    (hRL : closedRectNhd p q 0 ×ˢ L ⊆ U) {F : ℂ × E → Matrix n n ℂ}
    (hF : DifferentiableOn ℂ F U) (hFu : ∀ x ∈ U, IsUnit (F x)) :
    ∃ ε > 0, ∃ P : Set E, IsOpen P ∧ L ⊆ P ∧ ∃ F₁ F₂ : ℂ × E → Matrix n n ℂ,
      DifferentiableOn ℂ F₁ (leftPlane q ε ×ˢ P) ∧
      (∀ x ∈ leftPlane q ε ×ˢ P, IsUnit (F₁ x)) ∧
      DifferentiableOn ℂ F₂ (rightStrip p q ε ×ˢ P) ∧
      (∀ x ∈ rightStrip p q ε ×ˢ P, IsUnit (F₂ x)) ∧
      ∀ x ∈ rectNhd p q ε ×ˢ P, F x = F₁ x * F₂ x := by
  cases isEmpty_or_nonempty n
  · refine ⟨1, one_pos, univ, isOpen_univ, subset_univ _, 1, 1, differentiableOn_const 1,
      fun _ _ ↦ isUnit_one, differentiableOn_const 1, fun _ _ ↦ isUnit_one,
      fun _ _ ↦ Subsingleton.elim _ _⟩
  open scoped Matrix.Norms.Operator in
  exact exists_mul_split_of_isUnit (𝔸 := Matrix n n ℂ) hre him hL hU hRL hF hFu

end Matrix

section Box

variable {ι : Type*} [Finite ι] [DecidableEq ι]
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [NormOneClass 𝔸]
  [FiniteDimensional ℂ 𝔸]

/-- The closed box `∏ j, [(a j).re, (b j).re] × [(a j).im, (b j).im] ⊆ ℂ^ι`. -/
def closedBox (a b : ι → ℂ) : Set (ι → ℂ) :=
  univ.pi fun j ↦ Icc (a j).re (b j).re ×ℂ Icc (a j).im (b j).im

omit [Finite ι] [DecidableEq ι] in
lemma isCompact_closedBox (a b : ι → ℂ) : IsCompact (closedBox a b) :=
  isCompact_univ_pi fun _ ↦ isCompact_Icc.reProdIm isCompact_Icc

/-- **Cartan's lemma for adjacent closed boxes.** Let `K = closedBox a b ⊆ ℂ^ι` and let
`K₁ = closedBox a' b`, `K₂ = closedBox a b'` be the boxes obtained by moving the left, resp.
right, real edge of `K` in the coordinate `i` to `x₀`, resp. `x₁`; for `x₀ ≤ (a i).re` and
`(b i).re ≤ x₁` they are adjacent boxes with `K₁ ∩ K₂ = K`. Let `F` be holomorphic with invertible
values on an open `U ⊇ K`. Then there are open `U₁ ⊇ K₁`, `U₂ ⊇ K₂`, `W ⊇ K` with
`W ⊆ U ∩ U₁ ∩ U₂`, and `F₁`, `F₂` holomorphic with invertible values on `U₁`, resp. `U₂`, with
`F = F₁ F₂` on `W`. -/
theorem exists_mul_split_closedBox (i : ι) {a b : ι → ℂ} (hre : (a i).re ≤ (b i).re)
    (him : (a i).im ≤ (b i).im) (x₀ x₁ : ℝ) {U : Set (ι → ℂ)} (hU : IsOpen U)
    (hKU : closedBox a b ⊆ U) {F : (ι → ℂ) → 𝔸} (hF : DifferentiableOn ℂ F U)
    (hFu : ∀ x ∈ U, IsUnit (F x)) :
    ∃ U₁ U₂ W : Set (ι → ℂ), IsOpen U₁ ∧ IsOpen U₂ ∧ IsOpen W ∧
      closedBox (Function.update a i ⟨x₀, (a i).im⟩) b ⊆ U₁ ∧
      closedBox a (Function.update b i ⟨x₁, (b i).im⟩) ⊆ U₂ ∧
      closedBox a b ⊆ W ∧ W ⊆ U ∩ U₁ ∩ U₂ ∧
      ∃ F₁ F₂ : (ι → ℂ) → 𝔸, DifferentiableOn ℂ F₁ U₁ ∧ (∀ x ∈ U₁, IsUnit (F₁ x)) ∧
        DifferentiableOn ℂ F₂ U₂ ∧ (∀ x ∈ U₂, IsUnit (F₂ x)) ∧ ∀ x ∈ W, F x = F₁ x * F₂ x := by
  cases nonempty_fintype ι
  set e := splitAt i
  set L : Set ({j // j ≠ i} → ℂ) := univ.pi fun j ↦ Icc (a j).re (b j).re ×ℂ Icc (a j).im (b j).im
  have hL : IsCompact L := isCompact_univ_pi fun _ ↦ isCompact_Icc.reProdIm isCompact_Icc
  have hU' : IsOpen (e.symm ⁻¹' U) := hU.preimage e.symm.continuous
  have hRL : closedRectNhd (a i) (b i) 0 ×ˢ L ⊆ e.symm ⁻¹' U := by
    rintro ⟨z, w⟩ ⟨hz, hw⟩
    refine hKU fun j _ ↦ ?_
    rcases eq_or_ne j i with rfl | hj
    · rw [splitAt_symm_apply_self]
      simpa [closedRectNhd] using hz
    · rw [splitAt_symm_apply_of_ne _ _ hj]
      exact hw ⟨j, hj⟩ (mem_univ _)
  obtain ⟨ε, hε, P, hP, hLP, F₁, F₂, hF₁, hF₁u, hF₂, hF₂u, hFF⟩ :=
    exists_mul_split_of_isUnit hre him hL hU' hRL
      (hF.comp e.symm.differentiableOn (mapsTo_preimage _ _)) fun x hx ↦ hFu _ hx
  have hLx : ∀ {a' b' : ι → ℂ}, (∀ j, j ≠ i → a' j = a j) → (∀ j, j ≠ i → b' j = b j) →
      ∀ x ∈ closedBox a' b', (fun j : {j // j ≠ i} ↦ x j) ∈ P := by
    intro a' b' ha' hb' x hx
    refine hLP fun j _ ↦ ?_
    have := hx j (mem_univ _)
    simp only at this
    rwa [ha' j j.2, hb' j j.2] at this
  refine ⟨e ⁻¹' (leftPlane (b i) ε ×ˢ P), e ⁻¹' (rightStrip (a i) (b i) ε ×ˢ P),
    U ∩ e ⁻¹' (rectNhd (a i) (b i) ε ×ˢ P),
    (isOpen_leftPlane.prod hP).preimage e.continuous,
    (isOpen_rightStrip.prod hP).preimage e.continuous,
    hU.inter ((isOpen_rectNhd.prod hP).preimage e.continuous), fun x hx ↦ ?_, fun x hx ↦ ?_,
    fun x hx ↦ ?_, fun x hx ↦ ?_, F₁ ∘ e, F₂ ∘ e,
    hF₁.comp e.differentiableOn (mapsTo_preimage _ _), fun x hx ↦ hF₁u _ hx,
    hF₂.comp e.differentiableOn (mapsTo_preimage _ _), fun x hx ↦ hF₂u _ hx, fun x hx ↦ ?_⟩
  · refine ⟨?_, hLx (fun j hj ↦ Function.update_of_ne hj _ _) (fun _ _ ↦ rfl) x hx⟩
    have := (hx i (mem_univ _)).1.2
    change (x i).re < (b i).re + ε
    linarith
  · refine ⟨?_, hLx (fun _ _ ↦ rfl) (fun j hj ↦ Function.update_of_ne hj _ _) x hx⟩
    have h1 := (hx i (mem_univ _)).1.1
    have h2 := (hx i (mem_univ _)).2
    simp only [Function.update_self] at h2
    refine ⟨?_, ?_, ?_⟩
    · change (a i).re - ε < (x i).re; linarith
    · change (a i).im - ε < (x i).im; linarith [h2.1]
    · change (x i).im < (b i).im + ε; linarith [h2.2]
  · refine ⟨hKU hx, show x i ∈ rectNhd (a i) (b i) ε from ?_,
      hLx (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) x hx⟩
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hx i (mem_univ _)
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  · exact ⟨⟨hx.1, prod_mono rectNhd_subset_leftPlane subset_rfl hx.2⟩,
      prod_mono rectNhd_subset_rightStrip subset_rfl hx.2⟩
  · have := hFF (e x) hx.2
    simp only [Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply] at this ⊢
    exact this

omit [Finite ι] in
lemma closedBox_subset_update_left (i : ι) {a b : ι → ℂ} {x₀ : ℝ} (hx₀ : x₀ ≤ (a i).re) :
    closedBox a b ⊆ closedBox (Function.update a i ⟨x₀, (a i).im⟩) b := by
  intro x hx j _
  rcases eq_or_ne j i with rfl | hj
  · obtain ⟨⟨h1, h2⟩, h3⟩ := hx j (mem_univ _)
    simp only [Function.update_self]
    exact ⟨⟨hx₀.trans h1, h2⟩, h3⟩
  · simp only [Function.update_of_ne hj]
    exact hx j (mem_univ _)

omit [Finite ι] in
lemma closedBox_subset_update_right (i : ι) {a b : ι → ℂ} {x₁ : ℝ} (hx₁ : (b i).re ≤ x₁) :
    closedBox a b ⊆ closedBox a (Function.update b i ⟨x₁, (b i).im⟩) := by
  intro x hx j _
  rcases eq_or_ne j i with rfl | hj
  · obtain ⟨⟨h1, h2⟩, h3⟩ := hx j (mem_univ _)
    simp only [Function.update_self]
    exact ⟨⟨h1, h2.trans hx₁⟩, h3⟩
  · simp only [Function.update_of_ne hj]
    exact hx j (mem_univ _)

omit [Finite ι] in
lemma closedBox_update_inter_subset (i : ι) {a b : ι → ℂ} (x₀ x₁ : ℝ) :
    closedBox (Function.update a i ⟨x₀, (a i).im⟩) b ∩
      closedBox a (Function.update b i ⟨x₁, (b i).im⟩) ⊆ closedBox a b := by
  rintro x ⟨h₁, h₂⟩ j _
  rcases eq_or_ne j i with rfl | hj
  · obtain ⟨⟨-, e2⟩, e3⟩ := h₁ j (mem_univ _)
    obtain ⟨⟨e1, -⟩, -⟩ := h₂ j (mem_univ _)
    simp only [Function.update_self] at e1 e2 e3 ⊢
    exact ⟨⟨e1, e2⟩, e3⟩
  · simpa [Function.update_of_ne hj] using h₁ j (mem_univ _)

end Box

/-- Two compact sets `A`, `B` of a Hausdorff space have open neighbourhoods `N₁`, `N₂` with
`N₁ ∩ N₂` inside a given open neighbourhood `W` of `A ∩ B`. -/
lemma exists_isOpen_inter_subset {X : Type*} [TopologicalSpace X] [T2Space X] {A B W : Set X}
    (hA : IsCompact A) (hB : IsCompact B) (hW : IsOpen W) (hAB : A ∩ B ⊆ W) :
    ∃ N₁ N₂ : Set X, IsOpen N₁ ∧ IsOpen N₂ ∧ A ⊆ N₁ ∧ B ⊆ N₂ ∧ N₁ ∩ N₂ ⊆ W := by
  obtain ⟨O₁, O₂, h₁, h₂, hA', hB', hdisj⟩ := SeparatedNhds.of_isCompact_isCompact
    (hA.diff hW) (hB.diff hW)
    (Set.disjoint_left.2 fun x hxA hxB ↦ hxA.2 (hAB ⟨hxA.1, hxB.1⟩))
  refine ⟨W ∪ O₁, W ∪ O₂, hW.union h₁, hW.union h₂, fun x hx ↦ ?_, fun x hx ↦ ?_, ?_⟩
  · by_cases hxW : x ∈ W
    · exact Or.inl hxW
    · exact Or.inr (hA' ⟨hx, hxW⟩)
  · by_cases hxW : x ∈ W
    · exact Or.inl hxW
    · exact Or.inr (hB' ⟨hx, hxW⟩)
  · rintro x ⟨hx₁ | hx₁, hx₂ | hx₂⟩
    · exact hx₁
    · exact hx₁
    · exact hx₂
    · exact absurd hx₂ (Set.disjoint_left.1 hdisj hx₁)

section Merge

variable {ι : Type*} [Finite ι] [DecidableEq ι]
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [NormOneClass 𝔸]
  [FiniteDimensional ℂ 𝔸]

/-- **Merging trivialisations over adjacent closed boxes.** Let `K₁`, `K₂` be adjacent closed
boxes as in `Complex.exists_mul_split_closedBox`, with `K₁ ∩ K₂ = closedBox a b`, let
`V₁ ⊇ K₁`, `V₂ ⊇ K₂` be open, and let `g` be holomorphic with invertible values on `V₁ ∩ V₂`. Then
there are open `V₁' ⊇ K₁`, `V₂' ⊇ K₂` inside `V₁`, resp. `V₂`, and `h₁`, `h₂` holomorphic with
invertible values on `V₁'`, resp. `V₂'`, with `g = h₁ h₂` on `V₁' ∩ V₂'`. In particular, a
holomorphic vector bundle which is trivial over `V₁` and over `V₂` (transition function `g`) is
trivial over the neighbourhood `V₁' ∪ V₂'` of `K₁ ∪ K₂`. -/
theorem exists_mul_split_closedBox_of_isOpen (i : ι) {a b : ι → ℂ} (hre : (a i).re ≤ (b i).re)
    (him : (a i).im ≤ (b i).im) {x₀ x₁ : ℝ} (hx₀ : x₀ ≤ (a i).re) (hx₁ : (b i).re ≤ x₁)
    {V₁ V₂ : Set (ι → ℂ)} (hV₁ : IsOpen V₁) (hV₂ : IsOpen V₂)
    (hK₁ : closedBox (Function.update a i ⟨x₀, (a i).im⟩) b ⊆ V₁)
    (hK₂ : closedBox a (Function.update b i ⟨x₁, (b i).im⟩) ⊆ V₂) {g : (ι → ℂ) → 𝔸}
    (hg : DifferentiableOn ℂ g (V₁ ∩ V₂)) (hgu : ∀ x ∈ V₁ ∩ V₂, IsUnit (g x)) :
    ∃ V₁' V₂' : Set (ι → ℂ), IsOpen V₁' ∧ IsOpen V₂' ∧
      closedBox (Function.update a i ⟨x₀, (a i).im⟩) b ⊆ V₁' ∧
      closedBox a (Function.update b i ⟨x₁, (b i).im⟩) ⊆ V₂' ∧ V₁' ⊆ V₁ ∧ V₂' ⊆ V₂ ∧
      ∃ h₁ h₂ : (ι → ℂ) → 𝔸, DifferentiableOn ℂ h₁ V₁' ∧ (∀ x ∈ V₁', IsUnit (h₁ x)) ∧
        DifferentiableOn ℂ h₂ V₂' ∧ (∀ x ∈ V₂', IsUnit (h₂ x)) ∧
        ∀ x ∈ V₁' ∩ V₂', g x = h₁ x * h₂ x := by
  have hK : closedBox a b ⊆ V₁ ∩ V₂ := fun x hx ↦
    ⟨hK₁ (closedBox_subset_update_left i hx₀ hx), hK₂ (closedBox_subset_update_right i hx₁ hx)⟩
  obtain ⟨U₁, U₂, W, hU₁, hU₂, hW, hKU₁, hKU₂, hKW, hWsub, F₁, F₂, hF₁, hF₁u, hF₂, hF₂u, hFF⟩ :=
    exists_mul_split_closedBox i hre him x₀ x₁ (hV₁.inter hV₂) hK hg hgu
  obtain ⟨N₁, N₂, hN₁, hN₂, hKN₁, hKN₂, hN⟩ := exists_isOpen_inter_subset
    (isCompact_closedBox _ _) (isCompact_closedBox _ _) hW
    ((closedBox_update_inter_subset i x₀ x₁).trans hKW)
  refine ⟨V₁ ∩ U₁ ∩ N₁, V₂ ∩ U₂ ∩ N₂, (hV₁.inter hU₁).inter hN₁, (hV₂.inter hU₂).inter hN₂,
    fun x hx ↦ ⟨⟨hK₁ hx, hKU₁ hx⟩, hKN₁ hx⟩, fun x hx ↦ ⟨⟨hK₂ hx, hKU₂ hx⟩, hKN₂ hx⟩,
    fun x hx ↦ hx.1.1, fun x hx ↦ hx.1.1, F₁, F₂, hF₁.mono fun x hx ↦ hx.1.2,
    fun x hx ↦ hF₁u x hx.1.2, hF₂.mono fun x hx ↦ hx.1.2, fun x hx ↦ hF₂u x hx.1.2,
    fun x hx ↦ hFF x (hN ⟨hx.1.2, hx.2.2⟩)⟩

end Merge

end Complex
