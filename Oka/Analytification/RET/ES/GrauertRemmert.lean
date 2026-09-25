/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.ES.GrauertRemmert.LocalForm

/-!
# Coherence of bounded sections: reduction to the extension across codimension two

Let `N ⊆ ℂⁿ` be open, `N° ⊆ N` with thin complement (the complement lies in the zero set of a
holomorphic `g` which does not vanish identically on any open set) and `W` a Hausdorff finite étale
cover of `N°`. We reduce the coherence of the sheaf `𝒜` of bounded sections
(`ComplexAnalytic.BoundedSections.boundedModule`) to the following extension statement across a
set of codimension two in Weierstrass form, `ComplexAnalytic.BoundedSections.CapExtension m` for
`m = n - 1`:

> Let `(N, N°)` be in Weierstrass form `N = G × {‖w‖ < ρ}`, `N° = {P(b)(w) ≠ 0}`, `G ⊆ ℂ^m`
> (`ComplexAnalytic.BoundedSections.WeierstrassForm`), and let `R` be a family of regular pairs on
> `G`. If `𝒜` satisfies the local conditions for coherence at every point not lying over the zero
> set of `R`, then it satisfies them everywhere.

This is the step of Grauert–Remmert (*Komplexe Räume*, 1958, §12–13) which uses the extension of
`W` over `G × ℙ¹` (`Oka/Analytification/RET/ES/Cap.lean`) and the evaluation embedding
(`Oka/Analytification/RET/ES/Evaluation.lean`). It is only needed for `n ≥ 3`: for `n ≤ 2` the
zero set of `R` is empty, and `𝒜` is coherent
(`ComplexAnalytic.BoundedSections.isCoherent_boundedModule_of_le_two`).

## Proof of the reduction

At points of `N°` the sheaf `𝒜` is free. Replacing `N°` by `{g ≠ 0}` does not change `𝒜`
(`ComplexAnalytic.BoundedSections.isCoherentAt_of_restrict`). Near a zero `x₀` of `g`, in an
affine chart, `(N, N°)` is in Weierstrass form, and `𝒜` satisfies the local conditions at all
points off the zero set of a family of regular pairs on the base: over points where the reduced
Weierstrass polynomial is separable `𝒜` is free, and over the remaining points off a codimension
two set the discriminant locus is a smooth graph, so they are b-points
(`ComplexAnalytic.BoundedSections.exists_localForm`). The extension statement gives the local
conditions at `x₀` in the chart, and they transfer back along the chart
(`ComplexAnalytic.BoundedSections.LocalBiholo.isCoherentAt_of_forall`).

## Main definitions

- `ComplexAnalytic.BoundedSections.CapExtension m`: the extension statement over a base of
  dimension `m`.

## Main results

- `ComplexAnalytic.BoundedSections.isCoherent_boundedModule_of_capExtension`: `𝒜` is coherent,
  assuming `ComplexAnalytic.BoundedSections.CapExtension (n - 1)` if `n ≥ 3`.
- `ComplexAnalytic.BoundedSections.isCoherent_boundedModule_of_le_two`: `𝒜` is coherent if
  `n ≤ 2`.
-/

open CategoryTheory Opposite AlgebraicGeometry Topology TopologicalSpace Filter Set

universe u

namespace ComplexAnalytic.BoundedSections

open AnalyticSpace KummerModel

noncomputable section

/-- **The extension of coherence across a codimension two set in Weierstrass form**, over a base
of dimension `m`: if `(N, N°)` is in Weierstrass form over a base `G ⊆ ℂ^m` and `R` is a family of
regular pairs on `G`, then the local conditions for coherence of the bounded sections of a
Hausdorff finite étale cover of `N°` at the points not lying over the zero set of `R` imply them at
all points. -/
def CapExtension (m : ℕ) : Prop :=
  ∀ (N N₀ : (AnalyticSpace.complexAffineSpace.{u} (m + 1)).Opens) (h₀ : N₀ ≤ N)
    (W : FiniteEtaleOver (space N₀)) [T2Space W.left] (F : WeierstrassForm N N₀)
    (R : RegularPairFamily F.G),
    (∀ x : space N, baseOf x.1 ∉ R.zeroSet → IsCoherentAt h₀ W x) →
      ∀ x : space N, IsCoherentAt h₀ W x

variable {n : ℕ} {N N₀ : (AnalyticSpace.complexAffineSpace.{u} n).Opens} (h₀ : N₀ ≤ N)
  (W : FiniteEtaleOver (space N₀)) [T2Space W.left]

/-- The bounded sections are free near the points of `N°`. -/
theorem isCoherentAt_of_mem {x : space N} (hx : x.1 ∈ N₀) : IsCoherentAt h₀ W x := by
  obtain ⟨U, k, e, hxU, hfree⟩ := exists_isFreeSpanAt_of_coords h₀ W
    (isOpen_setOf_mem N₀) (fun _ hy ↦ h₀ hy) (isOpen_setOf_mem N₀) (Φ := id) (Φ' := id)
    differentiableOn_id differentiableOn_id (fun _ h ↦ h) (fun _ h ↦ h) (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) ∅ (fun y hy ↦ by simpa using hy) (x₀ := x.1) hx (by simp)
  exact isCoherentAt_of_isFreeSpanAt _ _ (hfree x (mem_img_iff.1 hxU).2)

/-- **Coherence at the zeros of `g`**, if `N° = {g ≠ 0}`, assuming the extension statement in
dimension `n - 1` if `n ≥ 3`. -/
theorem isCoherentAt_of_eq_zero (hext : ∀ m, n = m + 1 → 2 ≤ m → CapExtension.{u} m)
    {g : Cn.{u} n → ℂ} (hg : DifferentiableOn ℂ g {x | x ∈ N}) (hne : ∀ x ∈ N, ¬ g =ᶠ[𝓝 x] 0)
    (hN₀ : ∀ x ∈ N, x ∈ N₀ ↔ g x ≠ 0) (x₀ : space N) (hgx₀ : g x₀.1 = 0) :
    IsCoherentAt h₀ W x₀ := by
  cases n with
  | zero =>
    exfalso
    refine hne x₀.1 x₀.2 (Eventually.of_forall fun y ↦ ?_)
    rw [Subsingleton.elim (α := Cn.{u} 0) y x₀.1]
    exact hgx₀
  | succ m =>
    obtain ⟨B, F, R, hx₀E, hR, hcoh⟩ := exists_localForm hg hne hN₀ x₀.2 hgx₀
    have hp : x₀.1 ∉ N₀ := fun h ↦ (hN₀ _ x₀.2).1 h hgx₀
    refine B.isCoherentAt_of_forall hp h₀ W (fun W' _ x ↦ ?_) hx₀E
    by_cases hm : m ≤ 1
    · exact hcoh W' x (by rw [hR hm]; exact notMem_empty _)
    · exact hext m rfl (by omega) B.A (B.A₀ N₀) (B.A₀_le N₀) W' F R (hcoh W') x

/-- **Coherence of the bounded sections, assuming the extension statement.** Let `N ∖ N°` be
thin, and suppose `ComplexAnalytic.BoundedSections.CapExtension (n - 1)` if `n ≥ 3`. Then the
sheaf of bounded sections of every Hausdorff finite étale cover of `N°` is a coherent sheaf of
`𝒪_N`-modules. -/
theorem isCoherent_boundedModule_of_capExtension
    (hext : ∀ m, n = m + 1 → 2 ≤ m → CapExtension.{u} m) (hD : HasThinComplement N N₀) :
    (boundedModule h₀ W).IsCoherent := by
  obtain ⟨g, hg, hgZ, hgD⟩ := hD
  refine isCoherent_of_forall_isCoherentAt h₀ W fun x₀ ↦ ?_
  by_cases hx₀ : x₀.1 ∈ N₀
  · exact isCoherentAt_of_mem h₀ W hx₀
  -- remove the zero set of `g` from `N°`
  set N₀' : (AnalyticSpace.complexAffineSpace.{u} n).Opens :=
    ⟨{x | x ∈ N₀ ∧ g x ≠ 0}, by
      change IsOpen ({x : Cn.{u} n | x ∈ N₀} ∩ g ⁻¹' {0}ᶜ)
      exact (hg.mono fun _ h ↦ h₀ h).continuousOn.isOpen_inter_preimage (isOpen_setOf_mem N₀)
        isOpen_compl_singleton⟩
  have h₀' : N₀' ≤ N₀ := fun _ h ↦ h.1
  have hβ := isMapPullback_mapCover (restrictMap h₀' hx₀) W
  have hgZ' : interior ({x : Cn.{u} n | x ∈ N₀} ∩ g ⁻¹' {0}) = ∅ :=
    subset_empty_iff.1 (hgZ ▸ interior_mono fun x hx ↦ ⟨h₀ hx.1, hx.2⟩)
  refine isCoherentAt_of_restrict (h₀ := h₀) h₀' hβ (fun _ hx ↦ restrictMap_χ h₀' hx₀ hx)
    (g := g) (hg.mono fun _ h ↦ h₀ h) hgZ'
    (fun x hx ↦ ⟨fun h ↦ h.2, fun h ↦ ⟨hx, h⟩⟩) ?_
  have hne : ∀ x ∈ N, ¬ g =ᶠ[𝓝 x] 0 := fun (x : Cn.{u} n) hx h ↦ by
    have hmem : x ∈ interior ({x : Cn.{u} n | x ∈ N} ∩ g ⁻¹' {0}) :=
      mem_interior_iff_mem_nhds.2 (inter_mem ((isOpen_setOf_mem N).mem_nhds hx)
        (Filter.mem_of_superset h fun y hy ↦ hy))
    exact hgZ.le hmem
  refine isCoherentAt_of_eq_zero (h₀'.trans h₀) _ hext hg hne (fun x hx ↦ ⟨fun h ↦ h.2,
    fun h ↦ ⟨by_contra fun h' ↦ h (hgD x hx h'), h⟩⟩) x₀ (hgD _ x₀.2 hx₀)

/-- **Coherence of the bounded sections in dimension at most two**: if `N ⊆ ℂⁿ`, `n ≤ 2`, and
`N ∖ N°` is thin, then the sheaf of bounded sections of every Hausdorff finite étale cover of `N°`
is a coherent sheaf of `𝒪_N`-modules. -/
theorem isCoherent_boundedModule_of_le_two (hn : n ≤ 2) (hD : HasThinComplement N N₀) :
    (boundedModule h₀ W).IsCoherent :=
  isCoherent_boundedModule_of_capExtension h₀ W (fun m hm h2 ↦ absurd hn (by omega)) hD

end

end ComplexAnalytic.BoundedSections
