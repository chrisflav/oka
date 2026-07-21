import Oka.OkaRing

open Polynomial TopologicalSpace

variable {n : ℕ} (U : Opens (Fin n → ℂ))

structure IsWeierstrassPolynomial (P : (OkaRing U)[X]) : Prop where
  monic : P.Monic
  apply_zero (i : ℕ) (hi : i < P.degree) : (P.coeff i).toGlobalFun _ 0 = 0

variable (U : Opens (Fin (n + 1) → ℂ))

theorem weierstrass_preparation (f : OkaRing U) (h : 0 ∈ U)
    (hf : ∃ (w : ℂ) (hw : Fin.snoc 0 w ∈ U),
      f.toFun _ ⟨Fin.snoc 0 w, hw⟩ ≠ 0) :
    ∃ (V : Opens (Fin n → ℂ)) (hx : 0 ∈ V)
      (W : Opens (Fin (n + 1) → ℂ)) (hxW : 0 ∈ W)
      (hWV : W ≤ V.extend')
      (hWU : W ≤ U)
      (h : OkaRing W) (g : (OkaRing V)[X]) (hg : IsWeierstrassPolynomial _ g),
      f.restrict hWU =
        (Polynomial.toOkaRing _ g).restrict hWV *
          h :=
  sorry
