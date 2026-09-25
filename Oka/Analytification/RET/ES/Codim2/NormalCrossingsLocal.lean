/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.ES.Codim2.NormalCrossingsBasis

/-!
# Normal crossings charts from local coordinates

Keep the notation of `Oka/Analytification/RET/ES/Codim2/NormalCrossingsCover.lean`. Suppose that
near a point `x₀ ∈ N` there are holomorphic coordinates `Φ : O ≅ O' ⊆ E × ℂʳ` with `Φ(x₀) ∈ E × {0}`
in which `N°` is the complement of the coordinate hyperplanes of the last `r` coordinates, i.e.
`N ∖ N°` is a normal crossings divisor near `x₀` in the coordinates `Φ`. Then a polydisc
neighbourhood of `x₀`, rescaled to `B × Δʳ`, is a normal crossings chart
(`ComplexAnalytic.BoundedSections.exists_ncChart`). Consequently `𝒜` is free near `x₀`, with a
basis of monomial sections (`ComplexAnalytic.BoundedSections.exists_isFreeSpanAt_of_local`).

This covers the points off `N ∖ N°` (`r = 0`), the smooth points of `N ∖ N°` (`r = 1`), and the
points where two smooth branches of `N ∖ N°` cross transversally (`r = 2`).

## Main results

- `ComplexAnalytic.BoundedSections.exists_ncChart`: a normal crossings chart near `x₀`.
- `ComplexAnalytic.BoundedSections.exists_isFreeSpanAt_of_local`: `𝒜` is free near `x₀`.
-/

open CategoryTheory Opposite AlgebraicGeometry Topology TopologicalSpace Filter Set Metric

universe u

namespace ComplexAnalytic.BoundedSections

open AnalyticSpace

noncomputable section

variable {n : ℕ} {N N₀ : (AnalyticSpace.complexAffineSpace.{u} n).Opens}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {r : ℕ}

/-- The open of `N` whose points lie in `V ⊆ N`. -/
def opensOf (N : (AnalyticSpace.complexAffineSpace.{u} n).Opens) {V : Set (Cn.{u} n)}
    (hV : IsOpen V) : (space N).Opens :=
  ⟨Subtype.val ⁻¹' V, hV.preimage continuous_subtype_val⟩

lemma img_opensOf {V : Set (Cn.{u} n)} (hV : IsOpen V) (hVN : ∀ x ∈ V, x ∈ N) :
    (img (opensOf N hV) : Set (Cn.{u} n)) = V := by
  ext x
  rw [SetLike.mem_coe, mem_img_iff]
  exact ⟨fun ⟨_, hx⟩ ↦ hx, fun hx ↦ ⟨hVN x hx, hx⟩⟩

/-- **A normal crossings chart from local coordinates.** Let `Φ` be holomorphic on an open
`O ⊆ N` with holomorphic inverse `Φ'` on an open `O'`, such that `x ∈ N°` if and only if the last
`r` coordinates of `Φ(x)` are nonzero, and let `x₀ ∈ O` with `Φ(x₀) ∈ E × {0}`. Then some open
neighbourhood `U` of `x₀` in `N` carries a normal crossings chart. -/
theorem exists_ncChart {O : Set (Cn.{u} n)} (hO : IsOpen O) (hON : ∀ x ∈ O, x ∈ N)
    {O' : Set (E × (Fin r → ℂ))} (hO' : IsOpen O') {Φ : Cn.{u} n → E × (Fin r → ℂ)}
    {Φ' : E × (Fin r → ℂ) → Cn.{u} n} (hΦ : DifferentiableOn ℂ Φ O)
    (hΦ' : DifferentiableOn ℂ Φ' O') (hmaps : MapsTo Φ O O') (hmaps' : MapsTo Φ' O' O)
    (hleft : ∀ x ∈ O, Φ' (Φ x) = x) (hright : ∀ z ∈ O', Φ (Φ' z) = z)
    (hmem : ∀ x ∈ O, x ∈ N₀ ↔ ∀ i, (Φ x).2 i ≠ 0) {x₀ : Cn.{u} n} (hx₀ : x₀ ∈ O)
    (hx₀0 : ∀ i, (Φ x₀).2 i = 0) :
    ∃ U : (space N).Opens, x₀ ∈ img U ∧ Nonempty (NCChart N₀ (img U : Set (Cn.{u} n)) E r) := by
  obtain ⟨δ, hδ, hδO'⟩ := Metric.isOpen_iff.1 hO' _ (hmaps hx₀)
  set b₀ := (Φ x₀).1
  have hball : ball (Φ x₀) δ = ball b₀ δ ×ˢ univ.pi fun _ : Fin r ↦ ball (0 : ℂ) δ := by
    rw [← ball_prod_same, ball_pi _ hδ]
    congr
    funext i
    rw [hx₀0 i]
  set V := O ∩ Φ ⁻¹' ball (Φ x₀) δ
  have hV : IsOpen V := hΦ.continuousOn.isOpen_inter_preimage hO isOpen_ball
  have hVN : ∀ x ∈ V, x ∈ N := fun x hx ↦ hON x hx.1
  have hδ' : (δ : ℂ) ≠ 0 := by exact_mod_cast hδ.ne'
  have hsc : Differentiable ℂ fun z : E × (Fin r → ℂ) ↦ ((z.1, fun i ↦ (δ : ℂ) * z.2 i) :
      E × (Fin r → ℂ)) := by fun_prop
  have hscmem (z : E × (Fin r → ℂ)) (hz : z ∈ ball b₀ δ ×ˢ univ.pi fun _ ↦ ball (0 : ℂ) 1) :
      ((z.1, fun i ↦ (δ : ℂ) * z.2 i) : E × (Fin r → ℂ)) ∈ ball (Φ x₀) δ := by
    rw [hball]
    refine ⟨hz.1, fun i _ ↦ ?_⟩
    have := mem_ball_zero_iff.1 (hz.2 i (mem_univ i))
    rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_of_nonneg hδ.le]
    exact mul_lt_of_lt_one_right hδ this
  have χ : NCChart N₀ V E r :=
    { B := ball b₀ δ
      convex := convex_ball _ _
      isOpen := isOpen_ball
      Ψ := fun x ↦ ((Φ x).1, fun i ↦ (Φ x).2 i / δ)
      Ψ' := fun z ↦ Φ' (z.1, fun i ↦ (δ : ℂ) * z.2 i)
      differentiableOn := by
        have hΦV := hΦ.mono (inter_subset_left (t := Φ ⁻¹' ball (Φ x₀) δ))
        fun_prop
      differentiableOn' := hΦ'.comp hsc.differentiableOn fun z hz ↦ hδO' (hscmem z hz)
      mapsTo := fun x hx ↦ by
        have h₁ : Φ x ∈ ball b₀ δ ×ˢ univ.pi fun _ : Fin r ↦ ball (0 : ℂ) δ := hball ▸ hx.2
        refine ⟨h₁.1, fun i _ ↦ ?_⟩
        have := mem_ball_zero_iff.1 (h₁.2 i (mem_univ i))
        rw [mem_ball_zero_iff, norm_div, Complex.norm_real, Real.norm_of_nonneg hδ.le,
          div_lt_one hδ]
        exact this
      mapsTo' := fun z hz ↦ by
        have h₁ := hδO' (hscmem z hz)
        refine ⟨hmaps' h₁, ?_⟩
        rw [mem_preimage, hright _ h₁]
        exact hscmem z hz
      left_inv := fun x hx ↦ by
        have : ((((Φ x).1, fun i ↦ (δ : ℂ) * ((Φ x).2 i / δ))) : E × (Fin r → ℂ)) = Φ x :=
          Prod.ext rfl (funext fun i ↦ mul_div_cancel₀ _ hδ')
        simp only [this, hleft x hx.1]
      right_inv := fun z hz ↦ by
        have h₁ := hδO' (hscmem z hz)
        simp only [hright _ h₁]
        exact Prod.ext rfl (funext fun i ↦ mul_div_cancel_left₀ _ hδ')
      mem_iff := fun x hx ↦ by
        rw [hmem x hx.1]
        exact forall_congr' fun i ↦ by simp [div_eq_zero_iff, hδ'] }
  refine ⟨opensOf N hV, ?_, ?_⟩
  · rw [← SetLike.mem_coe, img_opensOf hV hVN]
    exact ⟨hx₀, mem_ball_self hδ⟩
  · rw [img_opensOf hV hVN]
    exact ⟨χ⟩

/-- **`𝒜` is free near a normal crossings point.** In the situation of
`ComplexAnalytic.BoundedSections.exists_ncChart`, there are an open neighbourhood `U` of `x₀` in
`N` and sections `e₁, …, e_k` of `𝒜` over `U` such that near every point of `U`, `𝒜` is free
with a basis in their span. -/
theorem exists_isFreeSpanAt_of_local [FiniteDimensional ℂ E] (h₀ : N₀ ≤ N)
    (W : FiniteEtaleOver (space N₀)) [T2Space W.left] {O : Set (Cn.{u} n)} (hO : IsOpen O)
    (hON : ∀ x ∈ O, x ∈ N) {O' : Set (E × (Fin r → ℂ))} (hO' : IsOpen O')
    {Φ : Cn.{u} n → E × (Fin r → ℂ)} {Φ' : E × (Fin r → ℂ) → Cn.{u} n}
    (hΦ : DifferentiableOn ℂ Φ O) (hΦ' : DifferentiableOn ℂ Φ' O') (hmaps : MapsTo Φ O O')
    (hmaps' : MapsTo Φ' O' O) (hleft : ∀ x ∈ O, Φ' (Φ x) = x)
    (hright : ∀ z ∈ O', Φ (Φ' z) = z) (hmem : ∀ x ∈ O, x ∈ N₀ ↔ ∀ i, (Φ x).2 i ≠ 0)
    {x₀ : Cn.{u} n} (hx₀ : x₀ ∈ O) (hx₀0 : ∀ i, (Φ x₀).2 i = 0) :
    ∃ (U : (space N).Opens) (k : ℕ) (e : Fin k → (boundedModule h₀ W).val.obj (op U)),
      x₀ ∈ img U ∧ ∀ y ∈ U, IsFreeSpanAt h₀ W e y := by
  obtain ⟨U, hx₀U, ⟨χ⟩⟩ := exists_ncChart hO hON hO' hΦ hΦ' hmaps hmaps' hleft hright hmem hx₀
    hx₀0
  obtain ⟨k, e, he⟩ := NCChart.exists_isFreeSpanAt (W := W) h₀ χ
  exact ⟨U, k, e, hx₀U, he⟩

end

end ComplexAnalytic.BoundedSections
