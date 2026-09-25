/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.ES.CapExtension.BaseGenerators
import Oka.Analytification.RET.ES.CapExtension.Graph
import Oka.Analytification.RET.ES.GrauertRemmert

/-!
# The extension statement from relative Theorem A and finiteness of the cap sections

Keep the notation of `Oka/Analytification/RET/ES/CapExtension/Setup.lean`. We deduce the
extension statement `ComplexAnalytic.BoundedSections.CapExtension m` from two inputs about the
sections of the cap with a pole of order `≤ n` at infinity, for every Weierstrass form, regular
pair family and annulus decomposition such that `𝒜` is coherent off the zero set `Z` of the pairs:

* `ComplexAnalytic.BoundedSections.CapTheoremAInput m`: relative Theorem A at the points not over
  `Z` (`ComplexAnalytic.Cap.AnnulusDecomposition.CapTheoremA`);
* `ComplexAnalytic.BoundedSections.CapFinitenessInput m`: the sections of the cap are locally
  finitely generated over the holomorphic functions on the base, at every point of `G`
  (`ComplexAnalytic.Cap.AnnulusDecomposition.CapLocallyFinite`).

The second input gives uniform generators near every point of `G`
(`ComplexAnalytic.Cap.AnnulusDecomposition.capGenerators_of_capLocallyFinite`), and with the first
one this gives coherence over `Z`
(`ComplexAnalytic.Cap.AnnulusDecomposition.isCoherentAt_of_capGenerators`).
-/

universe u

namespace ComplexAnalytic.BoundedSections

open AnalyticSpace Cap

/-- **Relative Theorem A for the cap** in dimension `m`: for every Weierstrass form over a base of
dimension `m`, regular pair family `R` and annulus decomposition `D` such that `𝒜` satisfies the
local conditions for coherence off the zero set of `R`, relative Theorem A holds at every point
not over the zero set of `R`. -/
def CapTheoremAInput (m : ℕ) : Prop :=
  ∀ (N N₀ : (AnalyticSpace.complexAffineSpace.{u} (m + 1)).Opens) (h₀ : N₀ ≤ N)
    (W : FiniteEtaleOver (space N₀)) [T2Space W.left] (F : WeierstrassForm N N₀)
    (R : RegularPairFamily F.G) (D : AnnulusDecomposition W F.G F.ρ),
    (∀ x : space N, baseOf x.1 ∉ R.zeroSet → IsCoherentAt h₀ W x) →
      ∀ y : space N, baseOf y.1 ∉ R.zeroSet → D.CapTheoremA h₀ y

/-- **Local finiteness of the sections of the cap** in dimension `m`: under the hypotheses of
`ComplexAnalytic.BoundedSections.CapTheoremAInput`, for every `n` the sections of the cap with a
pole of order `≤ n` at infinity are locally finitely generated at every point of the base off
the zero set of the regular pairs. -/
def CapFinitenessInput (m : ℕ) : Prop :=
  ∀ (N N₀ : (AnalyticSpace.complexAffineSpace.{u} (m + 1)).Opens) (h₀ : N₀ ≤ N)
    (W : FiniteEtaleOver (space N₀)) [T2Space W.left] (F : WeierstrassForm N N₀)
    (R : RegularPairFamily F.G) (D : AnnulusDecomposition W F.G F.ρ),
    (∀ x : space N, baseOf x.1 ∉ R.zeroSet → IsCoherentAt h₀ W x) →
      ∀ n, ∀ b ∈ F.G, b ∉ R.zeroSet → D.CapLocallyFinite h₀ n b

/-- **The extension statement** from relative Theorem A and the local finiteness of the sections
of the cap. -/
theorem capExtension_of_input {m : ℕ} (hA : CapTheoremAInput.{u} m)
    (hfin : CapFinitenessInput.{u} m) : CapExtension.{u} m := by
  intro N N₀ h₀ W _ F R hcoh x
  obtain ⟨D⟩ := AnnulusDecomposition.nonempty (W := W) F.convex_G F.isOpen_G F.one_lt_ρ
    F.annulusRegion_subset
  have hxG : baseOf x.1 ∈ F.G := ((F.mem_N x.1).1 x.2).1
  exact D.isCoherentAt_of_capGenerators h₀ R (hA N N₀ h₀ W F R D hcoh)
    (D.capGenerators_of_capLocallyFinite h₀ (fun n _ hb ↦
      AnnulusDecomposition.capLocallyFinite_of_forall_not_mem (hfin N N₀ h₀ W F R D hcoh n) hb) hxG)

/-- **Coherence of bounded sections in every dimension**, from relative Theorem A and the local
finiteness of the sections of the cap in all dimensions `≥ 2`. -/
theorem isCoherent_boundedModule_of_input
    (hA : ∀ m, 2 ≤ m → CapTheoremAInput.{u} m) (hfin : ∀ m, 2 ≤ m → CapFinitenessInput.{u} m)
    {n : ℕ} {N N₀ : (AnalyticSpace.complexAffineSpace.{u} n).Opens} (h₀ : N₀ ≤ N)
    (W : FiniteEtaleOver (space N₀)) [T2Space W.left] (hD : HasThinComplement N N₀) :
    (boundedModule h₀ W).IsCoherent :=
  isCoherent_boundedModule_of_capExtension h₀ W
    (fun m _ hm ↦ capExtension_of_input (hA m hm) (hfin m hm)) hD

end ComplexAnalytic.BoundedSections
