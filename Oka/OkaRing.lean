/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Complex.Basic

/-!
# The ring of holomorphic functions on an open subset of `ℂ^ι`

## Main definitions

- `OkaAnalytic`: a function on an open set `U` of `ℂ^ι` is holomorphic if its extension by zero
  is analytic on `U`.
- `okaSubring` and `OkaRing`: the `ℂ`-algebra of holomorphic functions on `U`.
- `OkaRing.restrict`: restriction of holomorphic functions along an inclusion of opens.
- `TopologicalSpace.Opens.extend'`: the cylinder `U × ℂ` over an open set `U` of `ℂ^n`.
- `Polynomial.toOkaRing`: a polynomial over `OkaRing U` viewed as a holomorphic function on the
  cylinder over `U`.
-/

/-- The `R`-linear form `x ↦ ∑ i, x i • f i` attached to a family `f` of elements of `R`. -/
noncomputable
abbrev linOfFun {R : Type*} [CommRing R]
    {ι : Type*} [Finite ι] (f : ι → R) :
    (ι → R) →ₗ[R] R :=
  Module.Basis.constr (S := R)
    (Pi.basisFun _ _) f

open TopologicalSpace

variable {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A function on an open set `U` of `ℂ^ι` is holomorphic if its extension by zero is
analytic on `U`. -/
def OkaAnalytic {U : Opens (ι → ℂ)} (f : U → ℂ) :
    Prop :=
  AnalyticOn ℂ (Function.extend Subtype.val f 0) U

/-- The `ℂ`-subalgebra of holomorphic functions inside all functions on `U`. -/
def okaSubring (U : Opens (ι → ℂ)) :
    Subalgebra ℂ (U → ℂ) where
  carrier := { f | OkaAnalytic f }
  mul_mem' := sorry
  one_mem' := sorry
  add_mem' := sorry
  zero_mem' := sorry
  algebraMap_mem' := sorry

/-- The `ℂ`-algebra of holomorphic functions on an open set `U` of `ℂ^ι`. -/
def OkaRing (U : Opens (ι → ℂ)) : Type _ :=
  okaSubring U

variable (U : Opens (ι → ℂ))

variable {U} in
/-- Bundle a holomorphic function on `U` as an element of `OkaRing U`. -/
def OkaRing.mk (f : U → ℂ) (hf : OkaAnalytic f) :
    OkaRing U :=
  ⟨_, hf⟩

-- instance : CoeFun (OkaRing U) U ℂ where

/-- The function underlying an element of `OkaRing U`. -/
def OkaRing.toFun (f : OkaRing U) :
    U → ℂ := f.val

/-- The extension by zero of `f : OkaRing U` to a function on all of `ℂ^ι`. -/
noncomputable
def OkaRing.toGlobalFun (f : OkaRing U) :
    (ι → ℂ) → ℂ :=
  Function.extend Subtype.val f.toFun 0

instance : CommRing (OkaRing U) :=
  inferInstanceAs <| CommRing (okaSubring U)

instance : Algebra ℂ (OkaRing U) :=
  inferInstanceAs <| Algebra ℂ (okaSubring U)

/-- Restriction of holomorphic functions along an inclusion `U ≤ V` of open sets. -/
noncomputable
def OkaRing.restrict {U V : Opens (ι → ℂ)}
    (h : U ≤ V) :
    OkaRing V →ₐ[ℂ] OkaRing U where
  toFun f := .mk (f.toFun ∘ U.inclusion h) sorry
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry
  commutes' := sorry

/-- The product of an open set of `X` and an open set of `Y`, as an open set of `X × Y`. -/
def TopologicalSpace.Opens.prod {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (U : Opens X) (V : Opens Y) :
    Opens (X × Y) :=
  ⟨_, U.2.prod V.2⟩

/-- The cylinder `U × ℂ` over an open set `U` of `ℂ^n`, as an open set of `ℂ^{n + 1}`. -/
noncomputable
def TopologicalSpace.Opens.extend' (U : Opens (Fin n → ℂ)) :
    Opens (Fin (n + 1) → ℂ) :=
  let homeo : ((Fin n → ℂ) × ℂ) ≃ₜ (Fin (n + 1) → ℂ) :=
    .trans
      ((.prodCongr (.refl _) (.symm <|
          .piUnique fun _ : Fin 1 ↦ ℂ)))
      (Fin.appendHomeomorph n 1)
  Homeomorph.opensCongr homeo (Opens.prod U ⊤)

open Polynomial

/-- A polynomial with coefficients holomorphic functions on `U`, viewed as the holomorphic
function `(z, w) ↦ ∑ i, (P.coeff i) z * w ^ i` on the cylinder over `U`. -/
noncomputable
def Polynomial.toOkaRing (U : Opens (Fin n → ℂ)) :
    (OkaRing U)[X] →ₐ[ℂ] OkaRing U.extend' where
  toFun P :=
    OkaRing.mk sorry sorry
  map_one' := sorry
  map_mul' := sorry
  map_add' := sorry
  map_zero' := sorry
  commutes' := sorry
