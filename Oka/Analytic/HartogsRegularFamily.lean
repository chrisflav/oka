/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytic.HartogsRegular

/-!
# Hartogs extension across finitely many zero sets of regular pairs

Let `U ⊆ ℂ^ι` be open and `(gᵢ, hᵢ)`, `i < k`, finitely many pairs of functions continuous on
`U` whose germs form a regular sequence at every common zero in `U`
(`RegularPairFamily U`), and let `Z = ⋃ᵢ {gᵢ = hᵢ = 0}`. For every open `G ⊆ U`, every
holomorphic function on `G \ Z` extends to a holomorphic function on `G`
(`RegularPairFamily.exists_differentiableOn_eqOn`), and `G \ Z` is dense in `G`
(`RegularPairFamily.eqOn_of_eqOn_diff`). This iterates
`exists_differentiableOn_eqOn_of_isWeaklyRegular` over the pairs.

## Main definitions

- `RegularPairFamily U`: finitely many regular pairs on `U`.
- `RegularPairFamily.zeroSet`: the union of their common zero sets.
-/

open Set Filter
open scoped Topology

variable {ι : Type*} [Finite ι]

/-- **A finite family of regular pairs on `U`**: pairs `(gᵢ, hᵢ)` of functions continuous on `U`
such that at every common zero `z ∈ U` of `gᵢ` and `hᵢ` some germs representing `gᵢ` and `hᵢ` at
`z` form a regular sequence. -/
structure RegularPairFamily (U : Set (ι → ℂ)) where
  /-- The number of pairs. -/
  k : ℕ
  /-- The first functions. -/
  g : Fin k → (ι → ℂ) → ℂ
  /-- The second functions. -/
  h : Fin k → (ι → ℂ) → ℂ
  /-- The first functions are continuous on `U`. -/
  continuousOn_g : ∀ i, ContinuousOn (g i) U
  /-- The second functions are continuous on `U`. -/
  continuousOn_h : ∀ i, ContinuousOn (h i) U
  /-- At common zeros in `U`, the germs form a regular sequence. -/
  isWeaklyRegular : ∀ i, ∀ z ∈ U, g i z = 0 → h i z = 0 → ∃ G H : LocalOkaRing ι,
    (G : MvPowerSeries ι ℂ).Represents (fun w ↦ g i (w + z)) ∧
    (H : MvPowerSeries ι ℂ).Represents (fun w ↦ h i (w + z)) ∧
    RingTheory.Sequence.IsWeaklyRegular (LocalOkaRing ι) [G, H]

namespace RegularPairFamily

variable {U : Set (ι → ℂ)} (P : RegularPairFamily U)

/-- The common zero set of the `i`-th pair. -/
def zeroSetOf (i : Fin P.k) : Set (ι → ℂ) :=
  {z | P.g i z = 0 ∧ P.h i z = 0}

/-- The union of the common zero sets of the pairs. -/
def zeroSet : Set (ι → ℂ) :=
  ⋃ i, P.zeroSetOf i

omit [Finite ι] in
lemma isOpen_diff_biUnion {G : Set (ι → ℂ)} (hG : IsOpen G) (hGU : G ⊆ U)
    (s : Finset (Fin P.k)) :
    IsOpen (G \ ⋃ i ∈ s, P.zeroSetOf i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hG
  | insert j s hj ih =>
    rw [Finset.set_biUnion_insert, ← sdiff_sdiff, sdiff_sdiff_comm]
    exact isOpen_diff_setOf_eq_zero_and_eq_zero ih ((P.continuousOn_g j).mono
      (sdiff_subset.trans hGU)) ((P.continuousOn_h j).mono (sdiff_subset.trans hGU))

omit [Finite ι] in
lemma isOpen_diff_zeroSet {G : Set (ι → ℂ)} (hG : IsOpen G) (hGU : G ⊆ U) :
    IsOpen (G \ P.zeroSet) := by
  simpa [zeroSet] using P.isOpen_diff_biUnion hG hGU Finset.univ

/-- Two functions continuous on an open `G ⊆ U` which agree off the zero set agree on `G`. -/
theorem eqOn_of_eqOn_diff {Y : Type*} [TopologicalSpace Y] [T2Space Y] {G : Set (ι → ℂ)}
    (hG : IsOpen G) (hGU : G ⊆ U) {F₁ F₂ : (ι → ℂ) → Y} (h₁ : ContinuousOn F₁ G)
    (h₂ : ContinuousOn F₂ G) (h : EqOn F₁ F₂ (G \ P.zeroSet)) : EqOn F₁ F₂ G := by
  classical
  suffices ∀ (s : Finset (Fin P.k)) (G : Set (ι → ℂ)), IsOpen G → G ⊆ U → ContinuousOn F₁ G →
      ContinuousOn F₂ G → EqOn F₁ F₂ (G \ ⋃ i ∈ s, P.zeroSetOf i) → EqOn F₁ F₂ G from
    this Finset.univ G hG hGU h₁ h₂ (by simpa [zeroSet] using h)
  intro s
  induction s using Finset.induction_on with
  | empty => intro G _ _ _ _ h; simpa using h
  | insert j s hj ih =>
    intro G hG hGU h₁ h₂ h
    have hGj : IsOpen (G \ P.zeroSetOf j) := isOpen_diff_setOf_eq_zero_and_eq_zero hG
      ((P.continuousOn_g j).mono hGU) ((P.continuousOn_h j).mono hGU)
    have h' : EqOn F₁ F₂ (G \ P.zeroSetOf j) := ih _ hGj (sdiff_subset.trans hGU)
      (h₁.mono sdiff_subset) (h₂.mono sdiff_subset) (by
        rw [sdiff_sdiff, ← Finset.set_biUnion_insert]
        exact h)
    have hint : interior (G ∩ P.zeroSetOf j) = ∅ :=
      interior_inter_setOf_eq_zero_and_eq_zero_eq_empty hG ((P.continuousOn_g j).mono hGU)
        ((P.continuousOn_h j).mono hGU) fun z hz ↦ P.isWeaklyRegular j z (hGU hz)
    exact EqOn.of_eqOn_diff_of_interior_eq_empty hG hint h₁ h₂ fun z hz ↦
      h' ⟨hz.1, fun hzj ↦ hz.2 ⟨hz.1, hzj⟩⟩

/-- **Hartogs extension across finitely many zero sets of regular pairs**: every holomorphic
function on `G \ Z`, for an open `G ⊆ U`, extends to a holomorphic function on `G`. -/
theorem exists_differentiableOn_eqOn {G : Set (ι → ℂ)} (hG : IsOpen G) (hGU : G ⊆ U)
    {f : (ι → ℂ) → ℂ} (hf : DifferentiableOn ℂ f (G \ P.zeroSet)) :
    ∃ F : (ι → ℂ) → ℂ, DifferentiableOn ℂ F G ∧ EqOn F f (G \ P.zeroSet) := by
  classical
  suffices ∀ (s : Finset (Fin P.k)) (G : Set (ι → ℂ)), IsOpen G → G ⊆ U →
      DifferentiableOn ℂ f (G \ ⋃ i ∈ s, P.zeroSetOf i) →
      ∃ F : (ι → ℂ) → ℂ, DifferentiableOn ℂ F G ∧ EqOn F f (G \ ⋃ i ∈ s, P.zeroSetOf i) by
    simpa [zeroSet] using this Finset.univ G hG hGU (by simpa [zeroSet] using hf)
  intro s
  induction s using Finset.induction_on with
  | empty => intro G _ _ hf; exact ⟨f, by simpa using hf, fun _ _ ↦ rfl⟩
  | insert j s hj ih =>
    intro G hG hGU hf
    have hGj : IsOpen (G \ P.zeroSetOf j) := isOpen_diff_setOf_eq_zero_and_eq_zero hG
      ((P.continuousOn_g j).mono hGU) ((P.continuousOn_h j).mono hGU)
    obtain ⟨F₁, hF₁, hF₁f⟩ := ih _ hGj (sdiff_subset.trans hGU) (by
      rw [sdiff_sdiff, ← Finset.set_biUnion_insert]
      exact hf)
    obtain ⟨F, hF, hFF₁⟩ := exists_differentiableOn_eqOn_of_isWeaklyRegular hG
      ((P.continuousOn_g j).mono hGU) ((P.continuousOn_h j).mono hGU)
      (fun z hz ↦ P.isWeaklyRegular j z (hGU hz)) hF₁
    refine ⟨F, hF, fun z hz ↦ ?_⟩
    rw [Finset.set_biUnion_insert] at hz
    have hzj : z ∈ G \ P.zeroSetOf j := ⟨hz.1, fun h ↦ hz.2 (Or.inl h)⟩
    exact (hFF₁ hzj).trans (hF₁f ⟨hzj, fun h ↦ hz.2 (Or.inr h)⟩)

end RegularPairFamily
