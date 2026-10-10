/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.Topology.Homotopy.Lifting

/-!
# Monodromy: naturality in maps of covers, and transitivity

Material for `Mathlib/Topology/Homotopy/Lifting.lean`, where `IsCoveringMap.monodromy` and the
monodromy action `IsCoveringMap.fundamentalGroupMulAction` are defined. Mathlib does not state how
monodromy interacts with a map between two covers of the same base, nor that the action is
transitive on the fibre of a path-connected cover; this file adds both.

## Main results

- `IsCoveringMap.monodromy_comp`: a continuous map `f : E → E'` over `X` between covering spaces
  intertwines monodromy.
- `IsCoveringMap.exists_monodromy_eq`: if `E` is path connected, any two points of a fibre are
  related by the monodromy of a loop in the base.
-/

open Function

namespace IsCoveringMap

variable {E E' X : Type*} [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace X]
  {p : E → X} {q : E' → X}

/-- **Monodromy is natural in maps of covers**: if `f : E → E'` is continuous with `q ∘ f = p`,
then `f` carries the monodromy of `p` along `γ` to the monodromy of `q` along `γ`. -/
theorem monodromy_comp (cp : IsCoveringMap p) (cq : IsCoveringMap q) {f : E → E'}
    (hf : Continuous f) (hfq : q ∘ f = p) {x y : X} (γ : Path.Homotopic.Quotient x y)
    (e : p ⁻¹' {x}) :
    f (cp.monodromy γ e) = cq.monodromy γ ⟨f e, by simpa [← hfq] using e.2⟩ := by
  induction γ using Path.Homotopic.Quotient.ind with | mk γ =>
  change f (cp.liftPath γ e _ 1) = cq.liftPath γ (f e) _ 1
  have h : f ∘ cp.liftPath γ e (γ.source.trans e.2.symm) =
      cq.liftPath γ (f e) (γ.source.trans (by simpa [← hfq] using e.2.symm)) :=
    (cq.eq_liftPath_iff _).2 ⟨hf.comp (ContinuousMap.continuous _),
      by rw [← comp_assoc, hfq, cp.liftPath_lifts], by simp [cp.liftPath_zero]⟩
  exact congr_fun h 1

/-- **The monodromy action on the fibre of a path-connected cover is transitive**: any two points
of a fibre are related by the monodromy of a loop. -/
theorem exists_monodromy_eq [PathConnectedSpace E] (cp : IsCoveringMap p) {x : X}
    (e e' : p ⁻¹' {x}) : ∃ γ : Path.Homotopic.Quotient x x, cp.monodromy γ e = e' := by
  let Γ : Path.Homotopic.Quotient e.1 e'.1 :=
    Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath e.1 e'.1)
  refine ⟨(Γ.map ⟨p, cp.continuous⟩).cast e.2.symm e'.2.symm,
    cp.monodromy_eq_of_map_eq Γ ?_⟩
  simp

end IsCoveringMap
