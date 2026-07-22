/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Statement
import Oka.StructureSheaf
import Oka.Algebra.Category.ModuleCat.Sheaf.Coherent.Criterion

/-!
# Auxiliary lemmas for Oka's coherence theorem

This file collects the lemmas used to deduce coherence of a structure sheaf from finitely
generated relations. The deduction itself is carried out over an arbitrary locally ringed space
in `Oka.AnalyticSpace.Relations`, and specialized to `ℂ^ι` in `isCoherent_unit_okaSheaf`.
-/

open CategoryTheory Limits TopologicalSpace Opposite SheafOfModules

universe u

section OpensSite

variable {T : Type u} [TopologicalSpace T]

/-- A family of open subsets of `X` covering `X` covers the terminal object of the slice site
over `X`. -/
lemma coversTop_over (X : Opens T) {A : Type u} (V : A → Opens T) (hle : ∀ a, V a ≤ X)
    (hcov : ∀ x ∈ X, ∃ a, x ∈ V a) :
    ((Opens.grothendieckTopology T).over X).CoversTop (fun a ↦ Over.mk (homOfLE (hle a))) := by
  intro Z
  let S : Sieve Z.left :=
    ⟨fun W _ ↦ ∃ a, W ≤ V a, by rintro W₁ W₂ f ⟨a, ha⟩ g; exact ⟨a, (leOfHom g).trans ha⟩⟩
  have hS : S ∈ Opens.grothendieckTopology T Z.left := by
    intro x hx
    obtain ⟨a, ha⟩ := hcov x (leOfHom Z.hom hx)
    exact ⟨Z.left ⊓ V a, homOfLE inf_le_left, ⟨a, inf_le_right⟩, ⟨hx, ha⟩⟩
  refine GrothendieckTopology.superset_covering _ ?_
    (GrothendieckTopology.overEquiv_symm_mem_over _ Z S hS)
  rintro W g ⟨a, ha⟩
  exact ⟨a, ⟨Over.homMk (homOfLE ha)⟩⟩

end OpensSite

section LinOfFun

variable {A : Type*} [CommRing A] {n : ℕ}

lemma linOfFun_apply (f : Fin n → A) (a : Fin n → A) :
    linOfFun f a = ∑ i, a i * f i := by
  simp [linOfFun, Module.Basis.constr_apply_fintype, mul_comm]

end LinOfFun
