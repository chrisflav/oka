import Oka.OkaRing

open TopologicalSpace

variable {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (U : Opens (ι → ℂ))

-- `U ⊆ ℂⁿ`
theorem oka {m : ℕ}
    -- (L : (Fin m → OkaRing U) →ₗ[OkaRing U] OkaRing U)
    (f : Fin m → OkaRing U) (x : ι → ℂ) (hx : x ∈ U) :
    ∃ (V : Opens (ι → ℂ)) (hV : V ≤ U) (k : ℕ)
      (g : Fin k → (Fin m → OkaRing V)), x ∈ V ∧
      ∀ (W : Opens (ι → ℂ)) (hWV : W ≤ V), W ≤ V →
        LinearMap.ker (linOfFun <| fun i : Fin m ↦
          OkaRing.restrict (le_trans hWV hV) (f i)) =
        Submodule.span (OkaRing W)
          (Set.range fun j : Fin k ↦
            (fun a : Fin m ↦ OkaRing.restrict hWV (g j a))) :=
  sorry
