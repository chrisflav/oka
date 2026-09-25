/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.GAGA.CartanMatrixLemma
import Oka.Analytification.GAGA.GridMerge

/-!
# Holomorphic cocycles are trivial near closed boxes

Let `D : κ → Set (ℂ^ι)` be a family of open sets and `g` a holomorphic cocycle with values in the
invertible elements of a finite-dimensional normed `ℂ`-algebra `𝔸` (e.g. the transition functions
of a holomorphic vector bundle, `𝔸 = Matrix (Fin r) (Fin r) ℂ`): `g k l` is holomorphic and
invertible on `D k ∩ D l` and `g k l * g l m = g k m` on `D k ∩ D l ∩ D m`. Then `g` is trivial
near every closed box `K ⊆ ⋃ k, D k`: there are `h k`, holomorphic and invertible on `D k ∩ V` for
an open `V ⊇ K`, with `g k l * h l = h k`.

The proof merges trivialisations along the grid of `Complex.HoledRect.mem_of_merge`; a merging
step is Cartan's lemma for adjacent boxes, `Complex.exists_mul_split_closedBox_of_isOpen`, in the
real direction, and its rotated version `Complex.exists_mul_split_closedBox_of_isOpen_im` in the
imaginary direction.

## Main definitions

- `Complex.rotI i`: multiplication of the `i`-th coordinate by `-I`.
- `Complex.IsCocycleTrivialOn D g W`: the cocycle `g` is trivial on `W`.

## Main results

- `Complex.exists_mul_split_closedBox_of_isOpen_im`: Cartan's lemma for boxes adjacent in the
  imaginary direction.
- `Complex.IsCocycleTrivialOn.union`: merging two trivialisations along a splitting of their
  comparison function.
- `Complex.exists_isCocycleTrivialOn_of_closedBox`: holomorphic cocycles are trivial near closed
  boxes; `Complex.exists_matrix_cocycle_trivial`: the version for matrix-valued cocycles, i.e.
  holomorphic vector bundles are trivial near closed boxes.
-/

open Set
open scoped Ring Topology

namespace Complex

section Rotation

variable {ι : Type*} [DecidableEq ι] (i : ι)

/-- Multiplication of the `i`-th coordinate by `-I`; it exchanges the real and the imaginary
direction of the `i`-th coordinate. -/
noncomputable def rotI : (ι → ℂ) ≃L[ℂ] (ι → ℂ) :=
  ContinuousLinearEquiv.piCongrRight fun j ↦ if j = i then
    ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 (-I) (by simp))
  else ContinuousLinearEquiv.refl ℂ ℂ

@[simp]
lemma rotI_apply_self (x : ι → ℂ) : rotI i x i = x i * (-I) := by
  simp [rotI]

@[simp]
lemma rotI_apply_of_ne (x : ι → ℂ) {j : ι} (hj : j ≠ i) : rotI i x j = x j := by
  simp [rotI, hj]

@[simp]
lemma rotI_symm_apply_self (x : ι → ℂ) : (rotI i).symm x i = x i * I := by
  simp [rotI]

@[simp]
lemma rotI_symm_apply_of_ne (x : ι → ℂ) {j : ι} (hj : j ≠ i) : (rotI i).symm x j = x j := by
  simp [rotI, hj]

end Rotation

section MergeIm

variable {ι : Type*} [Finite ι] [DecidableEq ι]
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [NormOneClass 𝔸]
  [FiniteDimensional ℂ 𝔸]

/-- **Merging trivialisations over boxes adjacent in the imaginary direction**: the version of
`Complex.exists_mul_split_closedBox_of_isOpen` for `K₁`, `K₂` obtained from `K = closedBox a b` by
moving the lower, resp. upper, imaginary edge in the coordinate `i` to `y₀`, resp. `y₁`. -/
theorem exists_mul_split_closedBox_of_isOpen_im (i : ι) {a b : ι → ℂ}
    (hre : (a i).re ≤ (b i).re) (him : (a i).im ≤ (b i).im) {y₀ y₁ : ℝ} (hy₀ : y₀ ≤ (a i).im)
    (hy₁ : (b i).im ≤ y₁) {V₁ V₂ : Set (ι → ℂ)} (hV₁ : IsOpen V₁) (hV₂ : IsOpen V₂)
    (hK₁ : closedBox (Function.update a i ⟨(a i).re, y₀⟩) b ⊆ V₁)
    (hK₂ : closedBox a (Function.update b i ⟨(b i).re, y₁⟩) ⊆ V₂) {g : (ι → ℂ) → 𝔸}
    (hg : DifferentiableOn ℂ g (V₁ ∩ V₂)) (hgu : ∀ x ∈ V₁ ∩ V₂, IsUnit (g x)) :
    ∃ V₁' V₂' : Set (ι → ℂ), IsOpen V₁' ∧ IsOpen V₂' ∧
      closedBox (Function.update a i ⟨(a i).re, y₀⟩) b ⊆ V₁' ∧
      closedBox a (Function.update b i ⟨(b i).re, y₁⟩) ⊆ V₂' ∧ V₁' ⊆ V₁ ∧ V₂' ⊆ V₂ ∧
      ∃ h₁ h₂ : (ι → ℂ) → 𝔸, DifferentiableOn ℂ h₁ V₁' ∧ (∀ x ∈ V₁', IsUnit (h₁ x)) ∧
        DifferentiableOn ℂ h₂ V₂' ∧ (∀ x ∈ V₂', IsUnit (h₂ x)) ∧
        ∀ x ∈ V₁' ∩ V₂', g x = h₁ x * h₂ x := by
  cases nonempty_fintype ι
  set R := rotI (ι := ι) i
  obtain ⟨a', ha'i, ha'j⟩ : ∃ a' : ι → ℂ,
      a' i = ⟨(a i).im, -(b i).re⟩ ∧ ∀ j, j ≠ i → a' j = a j :=
    ⟨Function.update a i _, Function.update_self _ _ _, fun j hj ↦ Function.update_of_ne hj _ _⟩
  obtain ⟨b', hb'i, hb'j⟩ : ∃ b' : ι → ℂ,
      b' i = ⟨(b i).im, -(a i).re⟩ ∧ ∀ j, j ≠ i → b' j = b j :=
    ⟨Function.update b i _, Function.update_self _ _ _, fun j hj ↦ Function.update_of_ne hj _ _⟩
  have hV₁' : IsOpen (R.symm ⁻¹' V₁) := hV₁.preimage R.symm.continuous
  have hV₂' : IsOpen (R.symm ⁻¹' V₂) := hV₂.preimage R.symm.continuous
  have hK₁' : closedBox (Function.update a' i ⟨y₀, (a' i).im⟩) b' ⊆ R.symm ⁻¹' V₁ := by
    intro y hy
    refine hK₁ fun j _ ↦ ?_
    by_cases hj : j = i
    · rw [hj]
      have hyi := hy i (mem_univ _)
      simp only [Function.update_self, ha'i, hb'i, R, rotI_symm_apply_self, mem_reProdIm, mem_Icc,
        mul_re, mul_im, I_re, I_im] at hyi ⊢
      obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hyi
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
    · simpa [R, Function.update_of_ne hj, rotI_symm_apply_of_ne _ _ hj, ha'j j hj, hb'j j hj]
        using hy j (mem_univ _)
  have hK₂' : closedBox a' (Function.update b' i ⟨y₁, (b' i).im⟩) ⊆ R.symm ⁻¹' V₂ := by
    intro y hy
    refine hK₂ fun j _ ↦ ?_
    by_cases hj : j = i
    · rw [hj]
      have hyi := hy i (mem_univ _)
      simp only [Function.update_self, ha'i, hb'i, R, rotI_symm_apply_self, mem_reProdIm, mem_Icc,
        mul_re, mul_im, I_re, I_im] at hyi ⊢
      obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hyi
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
    · simpa [R, Function.update_of_ne hj, rotI_symm_apply_of_ne _ _ hj, ha'j j hj, hb'j j hj]
        using hy j (mem_univ _)
  obtain ⟨W₁, W₂, hW₁, hW₂, hKW₁, hKW₂, hW₁V, hW₂V, h₁, h₂, hh₁, hh₁u, hh₂, hh₂u, hgh⟩ :=
    exists_mul_split_closedBox_of_isOpen (g := g ∘ R.symm) i (a := a') (b := b')
      (by rw [ha'i, hb'i]; exact him) (by rw [ha'i, hb'i]; simp only; linarith)
      (by rw [ha'i]; exact hy₀) (by rw [hb'i]; exact hy₁) hV₁' hV₂' hK₁' hK₂'
      (hg.comp (s := R.symm ⁻¹' V₁ ∩ R.symm ⁻¹' V₂) R.symm.differentiableOn fun x hx ↦ hx)
      (fun x hx ↦ hgu _ hx)
  refine ⟨R ⁻¹' W₁, R ⁻¹' W₂, hW₁.preimage R.continuous, hW₂.preimage R.continuous,
    fun x hx ↦ hKW₁ ?_, fun x hx ↦ hKW₂ ?_, fun x hx ↦ ?_, fun x hx ↦ ?_, h₁ ∘ R, h₂ ∘ R,
    hh₁.comp R.differentiableOn (fun x hx ↦ hx), fun x hx ↦ hh₁u _ hx,
    hh₂.comp R.differentiableOn (fun x hx ↦ hx), fun x hx ↦ hh₂u _ hx, fun x hx ↦ ?_⟩
  · intro j _
    by_cases hj : j = i
    · rw [hj]
      have hxi := hx i (mem_univ _)
      simp only [Function.update_self, ha'i, hb'i, R, rotI_apply_self, mem_reProdIm, mem_Icc,
        mul_re, mul_im, neg_re, neg_im, I_re, I_im] at hxi ⊢
      obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hxi
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
    · simpa [R, Function.update_of_ne hj, rotI_apply_of_ne _ _ hj, ha'j j hj, hb'j j hj]
        using hx j (mem_univ _)
  · intro j _
    by_cases hj : j = i
    · rw [hj]
      have hxi := hx i (mem_univ _)
      simp only [Function.update_self, ha'i, hb'i, R, rotI_apply_self, mem_reProdIm, mem_Icc,
        mul_re, mul_im, neg_re, neg_im, I_re, I_im] at hxi ⊢
      obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hxi
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
    · simpa [R, Function.update_of_ne hj, rotI_apply_of_ne _ _ hj, ha'j j hj, hb'j j hj]
        using hx j (mem_univ _)
  · simpa using hW₁V hx
  · simpa using hW₂V hx
  · simpa using hgh (R x) hx

end MergeIm

section Cocycle

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] {κ : Type*}
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸]

/-- The cocycle `g` on the family of open sets `D` is trivial on `W`: there are `h k`,
holomorphic with invertible values on `D k ∩ W`, with `g k l * h l = h k` on `D k ∩ D l ∩ W`. -/
def IsCocycleTrivialOn (D : κ → Set X) (g : κ → κ → X → 𝔸) (W : Set X) : Prop :=
  ∃ h : κ → X → 𝔸, (∀ k, DifferentiableOn ℂ (h k) (D k ∩ W)) ∧
    (∀ k, ∀ x ∈ D k ∩ W, IsUnit (h k x)) ∧ ∀ k l, ∀ x ∈ D k ∩ D l ∩ W, g k l x * h l x = h k x

variable {D : κ → Set X} {g : κ → κ → X → 𝔸}

lemma IsCocycleTrivialOn.mono {W W' : Set X} (h : IsCocycleTrivialOn D g W) (hW : W' ⊆ W) :
    IsCocycleTrivialOn D g W' := by
  obtain ⟨h, hd, hu, hrel⟩ := h
  exact ⟨h, fun k ↦ (hd k).mono (inter_subset_inter_right _ hW),
    fun k x hx ↦ hu k x ⟨hx.1, hW hx.2⟩, fun k l x hx ↦ hrel k l x ⟨hx.1, hW hx.2⟩⟩

lemma isCocycleTrivialOn_empty : IsCocycleTrivialOn D g ∅ :=
  ⟨fun _ _ ↦ 1, fun _ ↦ by simp, fun _ _ hx ↦ hx.2.elim, fun _ _ _ hx ↦ hx.2.elim⟩

/-- A cocycle is trivial on every subset of a member of the cover. -/
lemma isCocycleTrivialOn_of_subset (hg : ∀ k l, DifferentiableOn ℂ (g k l) (D k ∩ D l))
    (hgu : ∀ k l, ∀ x ∈ D k ∩ D l, IsUnit (g k l x))
    (hcoc : ∀ k l m, ∀ x ∈ D k ∩ D l ∩ D m, g k l x * g l m x = g k m x) {W : Set X} {k₀ : κ}
    (hW : W ⊆ D k₀) : IsCocycleTrivialOn D g W :=
  ⟨fun l ↦ g l k₀, fun l ↦ (hg l k₀).mono fun _ hx ↦ ⟨hx.1, hW hx.2⟩,
    fun l x hx ↦ hgu l k₀ x ⟨hx.1, hW hx.2⟩, fun k l x hx ↦ hcoc k l k₀ x ⟨hx.1, hW hx.2⟩⟩

variable [CompleteSpace 𝔸]

/-- **Merging trivialisations.** Let the cocycle `g` be trivial on the open sets `W₁` and `W₂`.
Their comparison is a holomorphic invertible function `G` on `W₁ ∩ W₂`; if every such `G` splits as
`G = G₁ G₂` on `V₁ ∩ V₂` for some open `V₁ ⊆ W₁`, `V₂ ⊆ W₂` with property `P` and holomorphic
invertible `G₁`, `G₂` on `V₁`, `V₂`, then `g` is trivial on `V₁ ∪ V₂` for such `V₁`, `V₂`. -/
theorem IsCocycleTrivialOn.union (hD : ∀ k, IsOpen (D k))
    (hgu : ∀ k l, ∀ x ∈ D k ∩ D l, IsUnit (g k l x)) {W₁ W₂ : Set X} (hW₁ : IsOpen W₁)
    (hW₂ : IsOpen W₂) (hcov : W₁ ∩ W₂ ⊆ ⋃ k, D k) (h₁ : IsCocycleTrivialOn D g W₁)
    (h₂ : IsCocycleTrivialOn D g W₂) {P : Set X → Set X → Prop}
    (hsplit : ∀ G : X → 𝔸, DifferentiableOn ℂ G (W₁ ∩ W₂) → (∀ x ∈ W₁ ∩ W₂, IsUnit (G x)) →
      ∃ V₁ V₂ : Set X, IsOpen V₁ ∧ IsOpen V₂ ∧ V₁ ⊆ W₁ ∧ V₂ ⊆ W₂ ∧ P V₁ V₂ ∧
        ∃ G₁ G₂ : X → 𝔸, DifferentiableOn ℂ G₁ V₁ ∧ (∀ x ∈ V₁, IsUnit (G₁ x)) ∧
          DifferentiableOn ℂ G₂ V₂ ∧ (∀ x ∈ V₂, IsUnit (G₂ x)) ∧
          ∀ x ∈ V₁ ∩ V₂, G x = G₁ x * G₂ x) :
    ∃ V₁ V₂ : Set X, IsOpen V₁ ∧ IsOpen V₂ ∧ V₁ ⊆ W₁ ∧ V₂ ⊆ W₂ ∧ P V₁ V₂ ∧
      IsCocycleTrivialOn D g (V₁ ∪ V₂) := by
  classical
  rcases isEmpty_or_nonempty κ with hκ | hκ
  · obtain ⟨V₁, V₂, hV₁, hV₂, hV₁W, hV₂W, hP, -⟩ :=
      hsplit 1 (differentiableOn_const 1) fun _ _ ↦ isUnit_one
    exact ⟨V₁, V₂, hV₁, hV₂, hV₁W, hV₂W, hP, fun k ↦ isEmptyElim k, fun k ↦ isEmptyElim k,
      fun k ↦ isEmptyElim k, fun k ↦ isEmptyElim k⟩
  obtain ⟨h, hd, hu, hrel⟩ := h₁
  obtain ⟨h', hd', hu', hrel'⟩ := h₂
  choose! kx hkx using fun x (hx : x ∈ W₁ ∩ W₂) ↦ mem_iUnion.1 (hcov hx)
  -- the comparison of the two trivialisations
  set G : X → 𝔸 := fun x ↦ (h (kx x) x)⁻¹ʳ * h' (kx x) x
  have hGk : ∀ k, ∀ x ∈ D k ∩ W₁ ∩ W₂, G x = (h k x)⁻¹ʳ * h' k x := by
    intro k x hx
    have hl : x ∈ D (kx x) := hkx x ⟨hx.1.2, hx.2⟩
    have e1 := hrel (kx x) k x ⟨⟨hl, hx.1.1⟩, hx.1.2⟩
    have e2 := hrel' (kx x) k x ⟨⟨hl, hx.1.1⟩, hx.2⟩
    have hgx := hgu (kx x) k x ⟨hl, hx.1.1⟩
    change (h (kx x) x)⁻¹ʳ * h' (kx x) x = _
    rw [← e1, ← e2, Ring.inverse_mul (Or.inl hgx), mul_assoc,
      Ring.inverse_mul_cancel_left _ _ hgx]
  have hloc : ∀ k, DifferentiableOn ℂ (fun x ↦ (h k x)⁻¹ʳ * h' k x) (D k ∩ W₁ ∩ W₂) := fun k ↦
    ((hd k).mono fun x hx ↦ ⟨hx.1.1, hx.1.2⟩).inverse (fun x hx ↦ hu k x ⟨hx.1.1, hx.1.2⟩)
      |>.mul ((hd' k).mono fun x hx ↦ ⟨hx.1.1, hx.2⟩)
  have hGd : DifferentiableOn ℂ G (W₁ ∩ W₂) := by
    intro x hx
    have hO : IsOpen (D (kx x) ∩ W₁ ∩ W₂) := ((hD _).inter hW₁).inter hW₂
    have hxO : x ∈ D (kx x) ∩ W₁ ∩ W₂ := ⟨⟨hkx x hx, hx.1⟩, hx.2⟩
    refine (((hloc (kx x)).differentiableAt (hO.mem_nhds hxO)).congr_of_eventuallyEq ?_)
      |>.differentiableWithinAt
    filter_upwards [hO.mem_nhds hxO] with y hy using hGk _ y hy
  have hGu : ∀ x ∈ W₁ ∩ W₂, IsUnit (G x) := fun x hx ↦
    (hu _ x ⟨hkx x hx, hx.1⟩).ringInverse.mul (hu' _ x ⟨hkx x hx, hx.2⟩)
  obtain ⟨V₁, V₂, hV₁, hV₂, hV₁W, hV₂W, hP, G₁, G₂, hG₁, hG₁u, hG₂, hG₂u, hGG⟩ :=
    hsplit G hGd hGu
  refine ⟨V₁, V₂, hV₁, hV₂, hV₁W, hV₂W, hP, ?_⟩
  -- the new trivialisation
  set h'' : κ → X → 𝔸 := fun k x ↦ if x ∈ V₁ then h k x * G₁ x else h' k x * (G₂ x)⁻¹ʳ
  have e₁ : ∀ k, ∀ x ∈ D k ∩ V₁, h'' k x = h k x * G₁ x := fun k x hx ↦ by
    simp only [h'', if_pos hx.2]
  have e₂ : ∀ k, ∀ x ∈ D k ∩ V₂, h'' k x = h' k x * (G₂ x)⁻¹ʳ := by
    intro k x hx
    by_cases hx₁ : x ∈ V₁
    · simp only [h'', if_pos hx₁]
      have hG := hGk k x ⟨⟨hx.1, hV₁W hx₁⟩, hV₂W hx.2⟩
      have hGs := hGG x ⟨hx₁, hx.2⟩
      have : h' k x = h k x * (G₁ x * G₂ x) := by
        rw [← hGs, hG, Ring.mul_inverse_cancel_left _ _ (hu k x ⟨hx.1, hV₁W hx₁⟩)]
      rw [this, ← mul_assoc, Ring.mul_inverse_cancel_right _ _ (hG₂u x hx.2)]
    · simp only [h'', if_neg hx₁]
  have hd₁ : ∀ k, DifferentiableOn ℂ (fun x ↦ h k x * G₁ x) (D k ∩ V₁) := fun k ↦
    ((hd k).mono fun x hx ↦ ⟨hx.1, hV₁W hx.2⟩).mul (hG₁.mono fun _ hx ↦ hx.2)
  have hd₂ : ∀ k, DifferentiableOn ℂ (fun x ↦ h' k x * (G₂ x)⁻¹ʳ) (D k ∩ V₂) := fun k ↦
    ((hd' k).mono fun x hx ↦ ⟨hx.1, hV₂W hx.2⟩).mul
      ((hG₂.mono fun _ hx ↦ hx.2).inverse fun x hx ↦ hG₂u x hx.2)
  refine ⟨h'', fun k x hx ↦ ?_, fun k x hx ↦ ?_, fun k l x hx ↦ ?_⟩
  · rcases hx.2 with hx₁ | hx₂
    · have hO : IsOpen (D k ∩ V₁) := (hD k).inter hV₁
      refine (((hd₁ k).differentiableAt (hO.mem_nhds ⟨hx.1, hx₁⟩)).congr_of_eventuallyEq
        ?_).differentiableWithinAt
      filter_upwards [hO.mem_nhds ⟨hx.1, hx₁⟩] with y hy using e₁ k y hy
    · have hO : IsOpen (D k ∩ V₂) := (hD k).inter hV₂
      refine (((hd₂ k).differentiableAt (hO.mem_nhds ⟨hx.1, hx₂⟩)).congr_of_eventuallyEq
        ?_).differentiableWithinAt
      filter_upwards [hO.mem_nhds ⟨hx.1, hx₂⟩] with y hy using e₂ k y hy
  · rcases hx.2 with hx₁ | hx₂
    · rw [e₁ k x ⟨hx.1, hx₁⟩]
      exact (hu k x ⟨hx.1, hV₁W hx₁⟩).mul (hG₁u x hx₁)
    · rw [e₂ k x ⟨hx.1, hx₂⟩]
      exact (hu' k x ⟨hx.1, hV₂W hx₂⟩).mul (hG₂u x hx₂).ringInverse
  · rcases hx.2 with hx₁ | hx₂
    · rw [e₁ l x ⟨hx.1.2, hx₁⟩, e₁ k x ⟨hx.1.1, hx₁⟩, ← mul_assoc,
        hrel k l x ⟨hx.1, hV₁W hx₁⟩]
    · rw [e₂ l x ⟨hx.1.2, hx₂⟩, e₂ k x ⟨hx.1.1, hx₂⟩, ← mul_assoc,
        hrel' k l x ⟨hx.1, hV₂W hx₂⟩]

end Cocycle

section Box

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*}
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [NormOneClass 𝔸]
  [FiniteDimensional ℂ 𝔸]

omit [Fintype ι] [DecidableEq ι] in
lemma closedBox_eq_empty_of_not_le {a b : ι → ℂ}
    (h : ¬ ∀ j, (a j).re ≤ (b j).re ∧ (a j).im ≤ (b j).im) : closedBox a b = ∅ := by
  refine eq_empty_iff_forall_notMem.2 fun x hx ↦ h fun j ↦ ?_
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hx j (mem_univ _)
  exact ⟨h1.trans h2, h3.trans h4⟩

/-- The family of sets `W` such that the cocycle is trivial near every closed box inside `W`. -/
private def trivialNearBoxes (D : κ → Set (ι → ℂ)) (g : κ → κ → (ι → ℂ) → 𝔸) :
    Set (Set (ι → ℂ)) :=
  {W | ∀ a b, closedBox a b ⊆ W → ∃ V, IsOpen V ∧ closedBox a b ⊆ V ∧ V ⊆ ⋃ k, D k ∧
    IsCocycleTrivialOn D g V}

variable {D : κ → Set (ι → ℂ)} {g : κ → κ → (ι → ℂ) → 𝔸}

private lemma mergeRe_trivialNearBoxes (hD : ∀ k, IsOpen (D k))
    (hgu : ∀ k l, ∀ x ∈ D k ∩ D l, IsUnit (g k l x)) :
    HoledRect.MergeRe (trivialNearBoxes D g) := by
  haveI : CompleteSpace 𝔸 := FiniteDimensional.complete ℂ 𝔸
  intro s i t δ hδ _ _ _ hA hB a b hK
  by_cases hord : ∀ j, (a j).re ≤ (b j).re ∧ (a j).im ≤ (b j).im
  swap
  · rw [closedBox_eq_empty_of_not_le hord]
    exact ⟨∅, isOpen_empty, subset_rfl, empty_subset _, isCocycleTrivialOn_empty⟩
  have hmemA : ∀ x ∈ HoledRect.prod s, (x i).re < t + δ →
      x ∈ HoledRect.prod (Function.update s i ((s i).withX₁ (t + δ))) := by
    intro x hx hxi
    refine HoledRect.mem_prod_iff.2 fun j ↦ ?_
    have := HoledRect.mem_prod_iff.1 hx j
    by_cases hj : j = i
    · subst hj
      rw [Function.update_self]
      rw [HoledRect.mem_set_iff'] at this ⊢
      exact ⟨⟨this.1.1, hxi⟩, this.2⟩
    · rwa [Function.update_of_ne hj]
  have hmemB : ∀ x ∈ HoledRect.prod s, t - δ < (x i).re →
      x ∈ HoledRect.prod (Function.update s i ((s i).withX₀ (t - δ))) := by
    intro x hx hxi
    refine HoledRect.mem_prod_iff.2 fun j ↦ ?_
    have := HoledRect.mem_prod_iff.1 hx j
    by_cases hj : j = i
    · subst hj
      rw [Function.update_self]
      rw [HoledRect.mem_set_iff'] at this ⊢
      exact ⟨⟨hxi, this.1.2⟩, this.2⟩
    · rwa [Function.update_of_ne hj]
  rcases lt_or_ge (b i).re (t + δ) with hb | hb
  · exact hA a b fun x hx ↦ hmemA x (hK hx) ((hx i (mem_univ _)).1.2.trans_lt hb)
  rcases lt_or_ge (t - δ) (a i).re with ha | ha
  · exact hB a b fun x hx ↦ hmemB x (hK hx) (ha.trans_le (hx i (mem_univ _)).1.1)
  obtain ⟨a', ha'i, ha'j⟩ : ∃ a' : ι → ℂ,
      a' i = ⟨t - δ / 2, (a i).im⟩ ∧ ∀ j, j ≠ i → a' j = a j :=
    ⟨Function.update a i _, Function.update_self _ _ _, fun j hj ↦ Function.update_of_ne hj _ _⟩
  obtain ⟨b', hb'i, hb'j⟩ : ∃ b' : ι → ℂ,
      b' i = ⟨t + δ / 2, (b i).im⟩ ∧ ∀ j, j ≠ i → b' j = b j :=
    ⟨Function.update b i _, Function.update_self _ _ _, fun j hj ↦ Function.update_of_ne hj _ _⟩
  set K₁ := closedBox (Function.update a' i ⟨(a i).re, (a' i).im⟩) b'
  set K₂ := closedBox a' (Function.update b' i ⟨(b i).re, (b' i).im⟩)
  have hK₁K : K₁ ⊆ closedBox a b := by
    intro x hx j _
    have := hx j (mem_univ _)
    by_cases hj : j = i
    · rw [hj] at this ⊢
      simp only [Function.update_self, ha'i, hb'i, mem_reProdIm, mem_Icc] at this ⊢
      obtain ⟨⟨h1, h2⟩, h3, h4⟩ := this
      exact ⟨⟨h1, by linarith⟩, h3, h4⟩
    · simpa [Function.update_of_ne hj, ha'j j hj, hb'j j hj] using this
  have hK₂K : K₂ ⊆ closedBox a b := by
    intro x hx j _
    have := hx j (mem_univ _)
    by_cases hj : j = i
    · rw [hj] at this ⊢
      simp only [Function.update_self, ha'i, hb'i, mem_reProdIm, mem_Icc] at this ⊢
      obtain ⟨⟨h1, h2⟩, h3, h4⟩ := this
      exact ⟨⟨by linarith, h2⟩, h3, h4⟩
    · simpa [Function.update_of_ne hj, ha'j j hj, hb'j j hj] using this
  have hK₁A : K₁ ⊆ HoledRect.prod (Function.update s i ((s i).withX₁ (t + δ))) := by
    intro x hx
    refine hmemA x (hK (hK₁K hx)) ?_
    have := (hx i (mem_univ _)).1.2
    rw [hb'i] at this
    change (x i).re ≤ t + δ / 2 at this
    linarith
  have hK₂B : K₂ ⊆ HoledRect.prod (Function.update s i ((s i).withX₀ (t - δ))) := by
    intro x hx
    refine hmemB x (hK (hK₂K hx)) ?_
    have := (hx i (mem_univ _)).1.1
    rw [ha'i] at this
    change t - δ / 2 ≤ (x i).re at this
    linarith
  obtain ⟨W₁, hW₁, hK₁W₁, hW₁Ω, htriv₁⟩ := hA _ _ hK₁A
  obtain ⟨W₂, hW₂, hK₂W₂, hW₂Ω, htriv₂⟩ := hB _ _ hK₂B
  obtain ⟨V₁, V₂, hV₁, hV₂, hV₁W, hV₂W, ⟨hK₁V₁, hK₂V₂⟩, htriv⟩ :=
    IsCocycleTrivialOn.union (P := fun V₁ V₂ ↦ K₁ ⊆ V₁ ∧ K₂ ⊆ V₂) hD hgu hW₁ hW₂
      (fun x hx ↦ hW₁Ω hx.1) htriv₁ htriv₂ fun G hG hGu ↦ by
        obtain ⟨V₁, V₂, o₁, o₂, k₁, k₂, s₁, s₂, rest⟩ :=
          exists_mul_split_closedBox_of_isOpen i (a := a') (b := b')
            (by rw [ha'i, hb'i]; change t - δ / 2 ≤ t + δ / 2; linarith)
            (by rw [ha'i, hb'i]; exact (hord i).2)
            (by rw [ha'i]; change (a i).re ≤ t - δ / 2; linarith)
            (by rw [hb'i]; change t + δ / 2 ≤ (b i).re; linarith) hW₁ hW₂ hK₁W₁ hK₂W₂ hG hGu
        exact ⟨V₁, V₂, o₁, o₂, s₁, s₂, ⟨k₁, k₂⟩, rest⟩
  refine ⟨V₁ ∪ V₂, hV₁.union hV₂, fun x hx ↦ ?_,
    union_subset (hV₁W.trans hW₁Ω) (hV₂W.trans hW₂Ω), htriv⟩
  rcases le_or_gt (x i).re (t + δ / 2) with hxi | hxi
  · refine Or.inl (hK₁V₁ fun j _ ↦ ?_)
    have := hx j (mem_univ _)
    by_cases hj : j = i
    · rw [hj] at this ⊢
      simp only [Function.update_self, ha'i, hb'i, mem_reProdIm, mem_Icc] at this ⊢
      exact ⟨⟨this.1.1, hxi⟩, this.2⟩
    · simpa [Function.update_of_ne hj, ha'j j hj, hb'j j hj] using this
  · refine Or.inr (hK₂V₂ fun j _ ↦ ?_)
    have := hx j (mem_univ _)
    by_cases hj : j = i
    · rw [hj] at this ⊢
      simp only [Function.update_self, ha'i, hb'i, mem_reProdIm, mem_Icc] at this ⊢
      exact ⟨⟨by linarith, this.1.2⟩, this.2⟩
    · simpa [Function.update_of_ne hj, ha'j j hj, hb'j j hj] using this

private lemma mergeIm_trivialNearBoxes (hD : ∀ k, IsOpen (D k))
    (hgu : ∀ k l, ∀ x ∈ D k ∩ D l, IsUnit (g k l x)) :
    HoledRect.MergeIm (trivialNearBoxes D g) := by
  haveI : CompleteSpace 𝔸 := FiniteDimensional.complete ℂ 𝔸
  intro s i t δ hδ _ _ _ hA hB a b hK
  by_cases hord : ∀ j, (a j).re ≤ (b j).re ∧ (a j).im ≤ (b j).im
  swap
  · rw [closedBox_eq_empty_of_not_le hord]
    exact ⟨∅, isOpen_empty, subset_rfl, empty_subset _, isCocycleTrivialOn_empty⟩
  have hmemA : ∀ x ∈ HoledRect.prod s, (x i).im < t + δ →
      x ∈ HoledRect.prod (Function.update s i ((s i).withY₁ (t + δ))) := by
    intro x hx hxi
    refine HoledRect.mem_prod_iff.2 fun j ↦ ?_
    have := HoledRect.mem_prod_iff.1 hx j
    by_cases hj : j = i
    · subst hj
      rw [Function.update_self]
      rw [HoledRect.mem_set_iff'] at this ⊢
      exact ⟨this.1, ⟨this.2.1.1, hxi⟩, this.2.2⟩
    · rwa [Function.update_of_ne hj]
  have hmemB : ∀ x ∈ HoledRect.prod s, t - δ < (x i).im →
      x ∈ HoledRect.prod (Function.update s i ((s i).withY₀ (t - δ))) := by
    intro x hx hxi
    refine HoledRect.mem_prod_iff.2 fun j ↦ ?_
    have := HoledRect.mem_prod_iff.1 hx j
    by_cases hj : j = i
    · subst hj
      rw [Function.update_self]
      rw [HoledRect.mem_set_iff'] at this ⊢
      exact ⟨this.1, ⟨hxi, this.2.1.2⟩, this.2.2⟩
    · rwa [Function.update_of_ne hj]
  rcases lt_or_ge (b i).im (t + δ) with hb | hb
  · exact hA a b fun x hx ↦ hmemA x (hK hx) ((hx i (mem_univ _)).2.2.trans_lt hb)
  rcases lt_or_ge (t - δ) (a i).im with ha | ha
  · exact hB a b fun x hx ↦ hmemB x (hK hx) (ha.trans_le (hx i (mem_univ _)).2.1)
  obtain ⟨a', ha'i, ha'j⟩ : ∃ a' : ι → ℂ,
      a' i = ⟨(a i).re, t - δ / 2⟩ ∧ ∀ j, j ≠ i → a' j = a j :=
    ⟨Function.update a i _, Function.update_self _ _ _, fun j hj ↦ Function.update_of_ne hj _ _⟩
  obtain ⟨b', hb'i, hb'j⟩ : ∃ b' : ι → ℂ,
      b' i = ⟨(b i).re, t + δ / 2⟩ ∧ ∀ j, j ≠ i → b' j = b j :=
    ⟨Function.update b i _, Function.update_self _ _ _, fun j hj ↦ Function.update_of_ne hj _ _⟩
  set K₁ := closedBox (Function.update a' i ⟨(a' i).re, (a i).im⟩) b'
  set K₂ := closedBox a' (Function.update b' i ⟨(b' i).re, (b i).im⟩)
  have hK₁K : K₁ ⊆ closedBox a b := by
    intro x hx j _
    have := hx j (mem_univ _)
    by_cases hj : j = i
    · rw [hj] at this ⊢
      simp only [Function.update_self, ha'i, hb'i, mem_reProdIm, mem_Icc] at this ⊢
      obtain ⟨⟨h1, h2⟩, h3, h4⟩ := this
      exact ⟨⟨h1, h2⟩, h3, by linarith⟩
    · simpa [Function.update_of_ne hj, ha'j j hj, hb'j j hj] using this
  have hK₂K : K₂ ⊆ closedBox a b := by
    intro x hx j _
    have := hx j (mem_univ _)
    by_cases hj : j = i
    · rw [hj] at this ⊢
      simp only [Function.update_self, ha'i, hb'i, mem_reProdIm, mem_Icc] at this ⊢
      obtain ⟨⟨h1, h2⟩, h3, h4⟩ := this
      exact ⟨⟨h1, h2⟩, by linarith, h4⟩
    · simpa [Function.update_of_ne hj, ha'j j hj, hb'j j hj] using this
  have hK₁A : K₁ ⊆ HoledRect.prod (Function.update s i ((s i).withY₁ (t + δ))) := by
    intro x hx
    refine hmemA x (hK (hK₁K hx)) ?_
    have := (hx i (mem_univ _)).2.2
    rw [hb'i] at this
    change (x i).im ≤ t + δ / 2 at this
    linarith
  have hK₂B : K₂ ⊆ HoledRect.prod (Function.update s i ((s i).withY₀ (t - δ))) := by
    intro x hx
    refine hmemB x (hK (hK₂K hx)) ?_
    have := (hx i (mem_univ _)).2.1
    rw [ha'i] at this
    change t - δ / 2 ≤ (x i).im at this
    linarith
  obtain ⟨W₁, hW₁, hK₁W₁, hW₁Ω, htriv₁⟩ := hA _ _ hK₁A
  obtain ⟨W₂, hW₂, hK₂W₂, hW₂Ω, htriv₂⟩ := hB _ _ hK₂B
  obtain ⟨V₁, V₂, hV₁, hV₂, hV₁W, hV₂W, ⟨hK₁V₁, hK₂V₂⟩, htriv⟩ :=
    IsCocycleTrivialOn.union (P := fun V₁ V₂ ↦ K₁ ⊆ V₁ ∧ K₂ ⊆ V₂) hD hgu hW₁ hW₂
      (fun x hx ↦ hW₁Ω hx.1) htriv₁ htriv₂ fun G hG hGu ↦ by
        obtain ⟨V₁, V₂, o₁, o₂, k₁, k₂, s₁, s₂, rest⟩ :=
          exists_mul_split_closedBox_of_isOpen_im i (a := a') (b := b')
            (by rw [ha'i, hb'i]; exact (hord i).1)
            (by rw [ha'i, hb'i]; change t - δ / 2 ≤ t + δ / 2; linarith)
            (by rw [ha'i]; change (a i).im ≤ t - δ / 2; linarith)
            (by rw [hb'i]; change t + δ / 2 ≤ (b i).im; linarith) hW₁ hW₂ hK₁W₁ hK₂W₂ hG hGu
        exact ⟨V₁, V₂, o₁, o₂, s₁, s₂, ⟨k₁, k₂⟩, rest⟩
  refine ⟨V₁ ∪ V₂, hV₁.union hV₂, fun x hx ↦ ?_,
    union_subset (hV₁W.trans hW₁Ω) (hV₂W.trans hW₂Ω), htriv⟩
  rcases le_or_gt (x i).im (t + δ / 2) with hxi | hxi
  · refine Or.inl (hK₁V₁ fun j _ ↦ ?_)
    have := hx j (mem_univ _)
    by_cases hj : j = i
    · rw [hj] at this ⊢
      simp only [Function.update_self, ha'i, hb'i, mem_reProdIm, mem_Icc] at this ⊢
      exact ⟨this.1, this.2.1, hxi⟩
    · simpa [Function.update_of_ne hj, ha'j j hj, hb'j j hj] using this
  · refine Or.inr (hK₂V₂ fun j _ ↦ ?_)
    have := hx j (mem_univ _)
    by_cases hj : j = i
    · rw [hj] at this ⊢
      simp only [Function.update_self, ha'i, hb'i, mem_reProdIm, mem_Icc] at this ⊢
      exact ⟨this.1, by linarith, this.2.2⟩
    · simpa [Function.update_of_ne hj, ha'j j hj, hb'j j hj] using this

omit [DecidableEq ι] in
/-- **Holomorphic cocycles are trivial near closed boxes.** Let `g` be a holomorphic cocycle on the
family of open sets `D` with values in the invertible elements of `𝔸` (e.g. the transition
functions of a holomorphic vector bundle). Then `g` is trivial on an open neighbourhood of every
closed box `K ⊆ ⋃ k, D k`. -/
theorem exists_isCocycleTrivialOn_of_closedBox (hD : ∀ k, IsOpen (D k))
    (hg : ∀ k l, DifferentiableOn ℂ (g k l) (D k ∩ D l))
    (hgu : ∀ k l, ∀ x ∈ D k ∩ D l, IsUnit (g k l x))
    (hcoc : ∀ k l m, ∀ x ∈ D k ∩ D l ∩ D m, g k l x * g l m x = g k m x) {a b : ι → ℂ}
    (hK : closedBox a b ⊆ ⋃ k, D k) :
    ∃ V : Set (ι → ℂ), IsOpen V ∧ closedBox a b ⊆ V ∧ IsCocycleTrivialOn D g V := by
  classical
  by_cases hord : ∀ j, (a j).re ≤ (b j).re ∧ (a j).im ≤ (b j).im
  swap
  · rw [closedBox_eq_empty_of_not_le hord]
    exact ⟨∅, isOpen_empty, subset_rfl, isCocycleTrivialOn_empty⟩
  have hΩ : IsOpen (⋃ k, D k) := isOpen_iUnion hD
  obtain ⟨δ, hδ, hδΩ⟩ := (isCompact_closedBox a b).exists_thickening_subset_open hΩ hK
  set s₀ : ι → HoledRect := fun j ↦
    ⟨(a j).re - δ / 4, (b j).re + δ / 4, (a j).im - δ / 4, (b j).im + δ / 4, -1⟩ with hs₀
  have hloc : ∀ x ∈ closure (HoledRect.prod s₀), ∃ W ∈ trivialNearBoxes D g, W ∈ 𝓝 x := by
    intro x hx
    rw [HoledRect.closure_prod] at hx
    have hxj : ∀ j, x j ∈ closedRectNhd (a j) (b j) (δ / 4) := fun j ↦
      closure_minimal (HoledRect.set_subset_rect (s₀ j)) isCompact_closedRectNhd.isClosed
        (hx j (mem_univ _))
    have hxΩ : x ∈ ⋃ k, D k := by
      refine hδΩ (Metric.mem_thickening_iff.2 ?_)
      choose y hy hdist using fun j ↦ Metric.mem_thickening_iff.1
        (closedRectNhd_subset_thickening (s := δ / 4) (δ := δ) (hord j).1 (hord j).2
          (by positivity) (by linarith) (hxj j))
      refine ⟨y, fun j _ ↦ ?_, (dist_pi_lt_iff hδ).2 hdist⟩
      simpa [closedRectNhd] using hy j
    obtain ⟨k, hk⟩ := mem_iUnion.1 hxΩ
    exact ⟨D k, fun a b h ↦ ⟨D k, hD k, h, subset_iUnion D k,
      isCocycleTrivialOn_of_subset hg hgu hcoc subset_rfl⟩, (hD k).mem_nhds hk⟩
  have hmem := HoledRect.mem_of_merge (trivialNearBoxes D g)
    (fun a b h ↦ ⟨∅, isOpen_empty, h, empty_subset _, isCocycleTrivialOn_empty⟩)
    (fun W hW W' hW' a b h ↦ hW a b (h.trans hW')) (mergeRe_trivialNearBoxes hD hgu)
    (mergeIm_trivialNearBoxes hD hgu) s₀ hloc
  obtain ⟨V, hV, hKV, -, hVt⟩ := hmem a b fun x hx ↦ HoledRect.mem_prod_iff.2 fun j ↦ by
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hx j (mem_univ _)
    refine HoledRect.mem_set_iff'.2 ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
    · change (a j).re - δ / 4 < (x j).re; linarith
    · change (x j).re < (b j).re + δ / 4; linarith
    · change (a j).im - δ / 4 < (x j).im; linarith
    · change (x j).im < (b j).im + δ / 4; linarith
    · exact lt_of_lt_of_le (by norm_num) (le_max_of_le_left (abs_nonneg _))
  exact ⟨V, hV, hKV, hVt⟩

omit [Fintype ι] [DecidableEq ι] in
/-- **Holomorphic matrix cocycles are trivial near closed boxes**: for the transition functions
`g k l` of a holomorphic vector bundle on `⋃ k, D k` and a closed box `K ⊆ ⋃ k, D k`, there are
`h k`, holomorphic with invertible values on `D k ∩ V` for an open `V ⊇ K`, with
`g k l * h l = h k`. -/
theorem exists_matrix_cocycle_trivial [Finite ι] {n : Type*} [Fintype n] [DecidableEq n]
    {D : κ → Set (ι → ℂ)} (hD : ∀ k, IsOpen (D k)) {g : κ → κ → (ι → ℂ) → Matrix n n ℂ}
    (hg : ∀ k l, DifferentiableOn ℂ (g k l) (D k ∩ D l))
    (hgu : ∀ k l, ∀ x ∈ D k ∩ D l, IsUnit (g k l x))
    (hcoc : ∀ k l m, ∀ x ∈ D k ∩ D l ∩ D m, g k l x * g l m x = g k m x) {a b : ι → ℂ}
    (hK : closedBox a b ⊆ ⋃ k, D k) :
    ∃ V : Set (ι → ℂ), IsOpen V ∧ closedBox a b ⊆ V ∧
      ∃ h : κ → (ι → ℂ) → Matrix n n ℂ, (∀ k, DifferentiableOn ℂ (h k) (D k ∩ V)) ∧
        (∀ k, ∀ x ∈ D k ∩ V, IsUnit (h k x)) ∧
        ∀ k l, ∀ x ∈ D k ∩ D l ∩ V, g k l x * h l x = h k x := by
  cases nonempty_fintype ι
  cases isEmpty_or_nonempty n
  · exact ⟨univ, isOpen_univ, subset_univ _, fun _ _ ↦ 1, fun _ ↦ differentiableOn_const 1,
      fun _ _ _ ↦ isUnit_one, fun _ _ _ _ ↦ Subsingleton.elim _ _⟩
  open scoped Matrix.Norms.Operator in
  exact exists_isCocycleTrivialOn_of_closedBox (𝔸 := Matrix n n ℂ) hD hg hgu hcoc hK

end Box

end Complex
