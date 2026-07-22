/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.OkaRing

/-!
# The Weierstrass preparation theorem

We state the Weierstrass preparation theorem: a holomorphic function on a neighbourhood of the
origin in `ℂ^{n+1}` which does not vanish identically on the last coordinate axis factors, near
the origin, as a unit times a Weierstrass polynomial.

## Main definitions

- `IsWeierstrassPolynomial`: a monic polynomial whose lower coefficients vanish at the origin.
-/

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
