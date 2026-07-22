/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.OkaRing
import Oka.LocalOkaRing

/-!
# The Weierstrass preparation theorem

We state the Weierstrass preparation theorem: a holomorphic function on a neighbourhood of the
origin in `ℂ^{n+1}` which does not vanish identically on the last coordinate axis factors, near
the origin, as a unit times a Weierstrass polynomial.

## Main definitions

- `IsWeierstrassPolynomial`: a monic polynomial whose lower coefficients vanish at the origin.
-/

open Polynomial TopologicalSpace

variable {n : ℕ}

/-- A local Weierstrass polynomial is a monic polynomial whose coefficients below the leading
one vanish at the origin. -/
structure IsLocalWeierstrassPolynomial
  (P : (MvPowerSeries (Fin n) ℂ)[X]) : Prop where
  monic : P.Monic
  apply_zero (i : ℕ) (hi : i < P.degree) :
  MvPowerSeries.constantCoeff (P.coeff i) = 0

/-- A polynomial over the germs in `n` variables, viewed as a germ in `n + 1` variables. -/
def LocalOkaRing.fromPolynomial :
    (LocalOkaRing (Fin n))[X] →ₐ[ℂ] LocalOkaRing (Fin (n + 1)) := sorry

/-- The Weierstrass preparation theorem for germs; uniqueness is omitted. -/
theorem localweierstrass_preparation
    (f : LocalOkaRing (Fin (n + 1)))
    (hf : (f : MvPowerSeries (Fin (n + 1)) ℂ).IsGeneralIn (.last _)) :
    ∃ (u : LocalOkaRing (Fin (n + 1))) (hu : IsUnit u)
      (g : (LocalOkaRing (Fin (n)))[X])
      (hg : IsLocalWeierstrassPolynomial
           (Polynomial.map (Subring.subtype (localOkaSubring _).toSubring) g)),
      f = LocalOkaRing.fromPolynomial g * u :=
  sorry







/-- The Weierstrass division theorem for germs; uniqueness is omitted. -/
theorem localweierstrass_division
      (q : (LocalOkaRing (Fin (n)))[X])
      (hq : IsLocalWeierstrassPolynomial
           (Polynomial.map (Subring.subtype (localOkaSubring _).toSubring) q))
      (f : LocalOkaRing (Fin (n + 1))) :
      ∃ (a : LocalOkaRing (Fin (n + 1)))
        (b : (LocalOkaRing (Fin (n)))[X]) (hd : b.degree < q.degree),
      f = a * (LocalOkaRing.fromPolynomial q) + (LocalOkaRing.fromPolynomial b) :=
  sorry















variable {n : ℕ} (U : Opens (Fin n → ℂ))

/-- A Weierstrass polynomial is a monic polynomial whose coefficients below the leading one
vanish at the origin. -/
structure IsWeierstrassPolynomial (P : (OkaRing U)[X]) : Prop where
  monic : P.Monic
  apply_zero (i : ℕ) (hi : i < P.degree) : (P.coeff i).toGlobalFun _ 0 = 0

variable (U : Opens (Fin (n + 1) → ℂ))

/-- The Weierstrass preparation theorem; uniqueness is omitted. -/
theorem weierstrass_preparation
    (f : OkaRing U) (h : 0 ∈ U)
    (hf : ∃ (w : ℂ) (hw : Fin.snoc 0 w ∈ U),
      f.toFun _ ⟨Fin.snoc 0 w, hw⟩ ≠ 0) :
    ∃ (V : Opens (Fin n → ℂ)) (hx : 0 ∈ V)
      (W : Opens (Fin (n + 1) → ℂ)) (hxW : 0 ∈ W)
      (hWV : W ≤ V.extend')
      (hWU : W ≤ U)
      (h : OkaRing W) (g : (OkaRing V)[X])
          (hi : h.toFun _ ⟨0, hxW⟩ ≠ 0)
          (hg : IsWeierstrassPolynomial _ g),
      f.restrict hWU =
        (Polynomial.toOkaRing _ g).restrict hWV *
          h :=
  sorry

/-- The Weierstrass division theorem; uniqueness is omitted. -/
theorem weierstrass_division
      (S : Opens (Fin n → ℂ))
      (g : (OkaRing S)[X]) (hx : 0 ∈ U) (hg : IsWeierstrassPolynomial _ g)
      (V : Opens (Fin (n + 1) → ℂ)) (hy : 0 ∈ V)
      (f : OkaRing V) :
    ∃ (W : Opens (Fin (n+1) → ℂ))
          (hWV : W ≤ V) (hWS : W ≤ S.extend')
      (h : OkaRing W)
      (r : (OkaRing S)[X]) (hd : r.degree < g.degree),
      f.restrict hWV =
          (Polynomial.toOkaRing _ g).restrict hWS * h +
              (Polynomial.toOkaRing _ r).restrict hWS :=
  sorry
