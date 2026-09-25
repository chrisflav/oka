/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.ES.CapExtension.Assembly
import Oka.Analytification.RET.ES.CapExtension.ProjFinite
import Oka.Analytification.RET.ES.CapExtension.StepDown

/-!
# The extension statement for the cap

We prove the extension statement `ComplexAnalytic.BoundedSections.CapExtension m` in every dimension
(`ComplexAnalytic.BoundedSections.capExtension`), and hence the coherence of the sheaf of bounded
sections `𝒜` of a finite étale cover of `N° ⊆ N` whose complement is thin, in every dimension
(`ComplexAnalytic.BoundedSections.isCoherent_boundedModule_of_hasThinComplement`).

By `ComplexAnalytic.BoundedSections.capExtension_of_input` it suffices to prove the two inputs
about the sections of the cap, over the open `U = G ∖ Z` of the base over which `𝒜` satisfies
the local conditions for coherence. There the sheaf of the cap `𝒞` on `ℂᵐ × ℙ¹` is coherent
(`ComplexAnalytic.Cap.AnnulusDecomposition.isCoherent_restrictModules_capModule`), so:

* relative Theorem A on `U × ℙ¹` gives relative Theorem A for the cap
  (`ComplexAnalytic.Cap.AnnulusDecomposition.capTheoremA_of_isCoherent`);
* the surjectivity of `𝒪(e)^I → 𝒞(n₁ + e)` on sections for `e ≫ 0` gives the local finiteness of
  the sections of the cap with a pole of high order
  (`ComplexAnalytic.Cap.AnnulusDecomposition.exists_capLocallyFinite_of_isCoherent`), and by
  descending induction with Oka's theorem that of the sections with a pole of any order
  (`ComplexAnalytic.Cap.AnnulusDecomposition.capLocallyFinite_of_succ`).
-/

universe u

namespace ComplexAnalytic.BoundedSections

open AnalyticSpace Cap relProjectiveSpaceAn

section

variable {m : ℕ} {N N₀ : (AnalyticSpace.complexAffineSpace.{u} (m + 1)).Opens}
  {W : FiniteEtaleOver (space N₀)} {F : WeierstrassForm N N₀} (R : RegularPairFamily F.G)

/-- The open `G ∖ Z` of the base, in the coordinates `Fin m → ℂ`. -/
def goodBase : TopologicalSpace.Opens (Fin m → ℂ) :=
  ⟨{y | ofBase.{u} y ∈ F.G \ R.zeroSet},
    (R.isOpen_diff_zeroSet F.isOpen_G subset_rfl).preimage continuous_ofBase⟩

lemma mem_goodBase {b : Cm.{u} m} : baseCoord b ∈ goodBase R ↔ b ∈ F.G ∧ b ∉ R.zeroSet := by
  change ofBase (baseCoord b) ∈ F.G \ R.zeroSet ↔ _
  rw [ofBase_baseCoord]
  rfl

lemma ofBase_mem_of_mem_goodBase {y : Fin m → ℂ} (hy : y ∈ goodBase R) : ofBase.{u} y ∈ F.G :=
  hy.1

lemma isCoherentAt_of_mem_goodBase {h₀ : N₀ ≤ N}
    (hcoh : ∀ x : space N, baseOf x.1 ∉ R.zeroSet → IsCoherentAt h₀ W x) (x : space N)
    (hx : baseCoord (baseOf x.1) ∈ goodBase R) : IsCoherentAt h₀ W x :=
  hcoh x ((mem_goodBase R).1 hx).2

end

/-- **Relative Theorem A for the cap** holds in every dimension. -/
theorem capTheoremAInput (m : ℕ) : CapTheoremAInput.{u} m := by
  intro N N₀ h₀ W _ F R D hcoh y hy
  have hyG : baseOf y.1 ∈ F.G := ((F.mem_N y.1).1 y.2).1
  exact D.capTheoremA_of_isCoherent h₀ (fun _ hy ↦ ofBase_mem_of_mem_goodBase R hy)
    (D.isCoherent_restrictModules_capModule h₀ (fun _ hy ↦ ofBase_mem_of_mem_goodBase R hy)
      (isCoherentAt_of_mem_goodBase R hcoh)) ((mem_goodBase R).2 ⟨hyG, hy⟩)

/-- **The sections of the cap are locally finitely generated** in every dimension. -/
theorem capFinitenessInput (m : ℕ) : CapFinitenessInput.{u} m := by
  intro N N₀ h₀ W _ F R D hcoh n b hbG hbZ
  obtain ⟨N₁, hN₁⟩ := D.exists_capLocallyFinite_of_isCoherent h₀
    (fun _ hy ↦ ofBase_mem_of_mem_goodBase R hy) (isCoherentAt_of_mem_goodBase R hcoh)
    ((mem_goodBase R).2 ⟨hbG, hbZ⟩)
  have hdown : ∀ k, D.CapLocallyFinite h₀ (n + k) b → D.CapLocallyFinite h₀ n b := by
    intro k
    induction k with
    | zero => exact id
    | succ k ih => exact fun h ↦ ih (D.capLocallyFinite_of_succ h₀ h)
  exact hdown N₁ (hN₁ _ (Nat.le_add_left _ _))

/-- **The extension statement** `ComplexAnalytic.BoundedSections.CapExtension m` holds in every
dimension. -/
theorem capExtension (m : ℕ) : CapExtension.{u} m :=
  capExtension_of_input (capTheoremAInput m) (capFinitenessInput m)

/-- **Coherence of bounded sections**: the sheaf of bounded sections of a finite étale cover of
`N° ⊆ N`, where `N ∖ N°` is thin, is coherent. -/
theorem isCoherent_boundedModule_of_hasThinComplement {n : ℕ}
    {N N₀ : (AnalyticSpace.complexAffineSpace.{u} n).Opens}
    (h₀ : N₀ ≤ N) (W : FiniteEtaleOver (space N₀)) [T2Space W.left]
    (hD : HasThinComplement N N₀) : (boundedModule h₀ W).IsCoherent :=
  isCoherent_boundedModule_of_capExtension h₀ W (fun m _ _ ↦ capExtension m) hD

end ComplexAnalytic.BoundedSections
