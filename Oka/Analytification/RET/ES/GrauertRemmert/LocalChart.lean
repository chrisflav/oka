/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.ES.Codim2.GraphInduction

/-!
# Bounded sections along a local biholomorphism

Keep the notation of `Oka/Analytification/RET/ES/Codim2/ChartModule.lean`. Let `Φ` be a
biholomorphism from an open `A ⊆ ℂⁿ` onto an open `E ⊆ N`, with inverse `Ψ`
(`ComplexAnalytic.BoundedSections.LocalBiholo`). Then `A° = Φ⁻¹(N°) ∩ A` is open, and `Φ`
extended by a point `p ∉ N°` off `A` is a `ComplexAnalytic.BoundedSections.ChartMap A° N°`
(`ComplexAnalytic.BoundedSections.LocalBiholo.chartMap`) which is biholomorphic on all of `A`
(`ComplexAnalytic.BoundedSections.LocalBiholo.chartBiholo`). Hence the local conditions for
coherence of the bounded sections transfer from the pullback of `W` to `A°` at `x ∈ A` to `W` at
`Φ(x)` (`ComplexAnalytic.BoundedSections.LocalBiholo.isCoherentAt`).

This covers both shrinking `N` to a small open `A ⊆ N` (`Φ = id`) and holomorphic changes of
coordinates.

## Main definitions

- `ComplexAnalytic.BoundedSections.LocalBiholo N`: a biholomorphism of an open of `ℂⁿ` onto an
  open of `N`.
- `ComplexAnalytic.BoundedSections.LocalBiholo.A₀`: the open `Φ⁻¹(N°) ∩ A`.

## Main results

- `ComplexAnalytic.BoundedSections.LocalBiholo.isCoherentAt`: transfer of the local conditions.
- `ComplexAnalytic.BoundedSections.LocalBiholo.isCoherentAt_of_forall`: the same, if the bounded
  sections of every Hausdorff finite étale cover of `A°` satisfy them.
-/

open CategoryTheory Opposite AlgebraicGeometry Topology TopologicalSpace Filter Set

universe u

namespace ComplexAnalytic.BoundedSections

open AnalyticSpace

noncomputable section

variable {n : ℕ}

/-- **A biholomorphism `Φ : A → E`** of an open `A ⊆ ℂⁿ` onto an open `E ⊆ N`, with inverse
`Ψ`. -/
structure LocalBiholo (N : (AnalyticSpace.complexAffineSpace.{u} n).Opens) where
  /-- The domain. -/
  A : (AnalyticSpace.complexAffineSpace.{u} n).Opens
  /-- The image. -/
  E : Set (Cn.{u} n)
  isOpen_E : IsOpen E
  E_sub : ∀ y ∈ E, y ∈ N
  /-- The biholomorphism. -/
  Φ : Cn.{u} n → Cn.{u} n
  /-- Its inverse. -/
  Ψ : Cn.{u} n → Cn.{u} n
  differentiableOn_Φ : DifferentiableOn ℂ Φ {x | x ∈ A}
  differentiableOn_Ψ : DifferentiableOn ℂ Ψ E
  mapsTo_Φ : ∀ x ∈ A, Φ x ∈ E
  mapsTo_Ψ : ∀ y ∈ E, Ψ y ∈ A
  Ψ_Φ : ∀ x ∈ A, Ψ (Φ x) = x
  Φ_Ψ : ∀ y ∈ E, Φ (Ψ y) = y

namespace LocalBiholo

variable {N : (AnalyticSpace.complexAffineSpace.{u} n).Opens} (B : LocalBiholo N)

/-- The open `A° = Φ⁻¹(N°) ∩ A`. -/
def A₀ (N₀ : (AnalyticSpace.complexAffineSpace.{u} n).Opens) :
    (AnalyticSpace.complexAffineSpace.{u} n).Opens :=
  ⟨{x | x ∈ B.A ∧ B.Φ x ∈ N₀}, by
    change IsOpen ({x : Cn.{u} n | x ∈ B.A} ∩ B.Φ ⁻¹' {y | y ∈ N₀})
    exact B.differentiableOn_Φ.continuousOn.isOpen_inter_preimage (isOpen_setOf_mem B.A)
      (isOpen_setOf_mem N₀)⟩

lemma mem_A₀ {N₀ : (AnalyticSpace.complexAffineSpace.{u} n).Opens} {x : Cn.{u} n} :
    x ∈ B.A₀ N₀ ↔ x ∈ B.A ∧ B.Φ x ∈ N₀ :=
  Iff.rfl

lemma A₀_le (N₀ : (AnalyticSpace.complexAffineSpace.{u} n).Opens) : B.A₀ N₀ ≤ B.A :=
  fun _ hx ↦ hx.1

variable {N₀ : (AnalyticSpace.complexAffineSpace.{u} n).Opens} {p : Cn.{u} n}

open Classical in
/-- The extension of `Φ` by `p` off `A`. -/
def extend (p x : Cn.{u} n) : Cn.{u} n :=
  if x ∈ B.A then B.Φ x else p

lemma extend_of_mem {x : Cn.{u} n} (hx : x ∈ B.A) : B.extend p x = B.Φ x := by
  classical
  unfold extend
  exact if_pos hx

lemma extend_of_not_mem {x : Cn.{u} n} (hx : x ∉ B.A) : B.extend p x = p := by
  classical
  unfold extend
  exact if_neg hx

/-- The map `Φ` on `A`, extended by `p ∉ N°`, as a `ComplexAnalytic.BoundedSections.ChartMap`. -/
def chartMap (hp : p ∉ N₀) : ChartMap (B.A₀ N₀) N₀ where
  χ := B.extend p
  χInv := B.Ψ
  R := B.E
  isOpen_R := B.isOpen_E
  differentiableOn_χ := B.differentiableOn_Φ.mono (fun x hx ↦ hx.1) |>.congr
    fun x hx ↦ B.extend_of_mem hx.1
  differentiableOn_χInv := B.differentiableOn_Ψ
  mem_iff x := by
    by_cases hx : x ∈ B.A
    · rw [B.extend_of_mem hx]
      exact ⟨fun h ↦ h.2, fun h ↦ ⟨hx, h⟩⟩
    · rw [B.extend_of_not_mem hx]
      exact ⟨fun h ↦ absurd h.1 hx, fun h ↦ absurd h hp⟩
  χ_mem_R x hx := by
    rw [B.extend_of_mem hx.1]
    exact B.mapsTo_Φ x hx.1
  χInv_χ x hx := by
    rw [B.extend_of_mem hx.1]
    exact B.Ψ_Φ x hx.1
  χ_χInv y hy _ := by
    rw [B.extend_of_mem (B.mapsTo_Ψ y hy)]
    exact B.Φ_Ψ y hy

variable (hp : p ∉ N₀)

lemma chartMap_χ {x : Cn.{u} n} (hx : x ∈ B.A) : (B.chartMap hp).χ x = B.Φ x :=
  B.extend_of_mem hx

/-- `Φ` is biholomorphic on all of `A`. -/
def chartBiholo : ChartBiholo (B.chartMap hp) B.A N where
  D := {x | x ∈ B.A}
  E := B.E
  isOpen_D := isOpen_setOf_mem B.A
  isOpen_E := B.isOpen_E
  D_sub _ hx := hx
  E_sub := B.E_sub
  E_sub_R _ hy := hy
  mapsTo x hx := by
    rw [B.chartMap_χ hp hx]
    exact B.mapsTo_Φ x hx
  inv_mem := B.mapsTo_Ψ
  inv_χ x hx := by
    change B.Ψ ((B.chartMap hp).χ x) = x
    rw [B.chartMap_χ hp hx]
    exact B.Ψ_Φ x hx
  χ_inv y hy := by
    change (B.chartMap hp).χ (B.Ψ y) = y
    rw [B.chartMap_χ hp (B.mapsTo_Ψ y hy)]
    exact B.Φ_Ψ y hy
  differentiableOn_χ := B.differentiableOn_Φ.congr fun x hx ↦ B.chartMap_χ hp hx
  differentiableOn_χInv := B.differentiableOn_Ψ

lemma Φ_mem {x : Cn.{u} n} (hx : x ∈ B.A) : B.Φ x ∈ N :=
  B.E_sub _ (B.mapsTo_Φ x hx)

/-- **The local conditions for coherence transfer along `Φ`**: if the bounded sections of the
pullback of `W` to `A°` satisfy them at `x ∈ A`, then those of `W` satisfy them at `Φ(x)`. -/
theorem isCoherentAt (h₀ : N₀ ≤ N) (W : FiniteEtaleOver (space N₀)) {x : Cn.{u} n}
    (hx : x ∈ B.A)
    (hc : IsCoherentAt (B.A₀_le N₀) (mapCover (B.chartMap hp) W) ⟨x, hx⟩) :
    IsCoherentAt h₀ W ⟨B.Φ x, B.Φ_mem hx⟩ := by
  have := (B.chartBiholo hp).isCoherentAt (h₀ := h₀) (fun _ hy ↦ hy)
    (isMapPullback_mapCover (B.chartMap hp) W) hc
  convert this using 2
  exact Subtype.ext (B.chartMap_χ hp hx).symm

include hp in
/-- **Transfer of the local conditions for coherence**, if they hold for the bounded sections of
every Hausdorff finite étale cover of `A°` at the points of `A`: then they hold for `W` at every
point of `E`. -/
theorem isCoherentAt_of_forall (h₀ : N₀ ≤ N) (W : FiniteEtaleOver (space N₀)) [T2Space W.left]
    (hc : ∀ (W' : FiniteEtaleOver (space (B.A₀ N₀))) [T2Space W'.left] (x : space B.A),
      IsCoherentAt (B.A₀_le N₀) W' x)
    {y : Cn.{u} n} (hy : y ∈ B.E) : IsCoherentAt h₀ W ⟨y, B.E_sub y hy⟩ := by
  have := B.isCoherentAt hp h₀ W (B.mapsTo_Ψ y hy) (hc _ _)
  convert this using 2
  exact Subtype.ext (B.Φ_Ψ y hy).symm

end LocalBiholo

end

end ComplexAnalytic.BoundedSections
