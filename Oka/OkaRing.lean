import Mathlib

noncomputable
abbrev linOfFun {R : Type*} [CommRing R]
    {ι : Type*} [Finite ι] (f : ι → R) :
    (ι → R) →ₗ[R] R :=
  Module.Basis.constr (S := R)
    (Pi.basisFun _ _) f

open TopologicalSpace

variable {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

def OkaAnalytic {U : Opens (ι → ℂ)} (f : U → ℂ) :
    Prop :=
  AnalyticOn ℂ (Function.extend Subtype.val f 0) U

def okaSubring (U : Opens (ι → ℂ)) :
    Subalgebra ℂ (U → ℂ) where
  carrier := { f | OkaAnalytic f }
  mul_mem' := sorry
  one_mem' := sorry
  add_mem' := sorry
  zero_mem' := sorry
  algebraMap_mem' := sorry

def OkaRing (U : Opens (ι → ℂ)) : Type _ :=
  okaSubring U

variable (U : Opens (ι → ℂ))

variable {U} in
def OkaRing.mk (f : U → ℂ) (hf : OkaAnalytic f) :
    OkaRing U :=
  ⟨_, hf⟩

-- instance : CoeFun (OkaRing U) U ℂ where

def OkaRing.toFun (f : OkaRing U) :
    U → ℂ := f.val

noncomputable
def OkaRing.toGlobalFun (f : OkaRing U) :
    (ι → ℂ) → ℂ :=
  Function.extend Subtype.val f.toFun 0

instance : CommRing (OkaRing U) :=
  inferInstanceAs <| CommRing (okaSubring U)

instance : Algebra ℂ (OkaRing U) :=
  inferInstanceAs <| Algebra ℂ (okaSubring U)

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

def TopologicalSpace.Opens.prod {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (U : Opens X) (V : Opens Y) :
    Opens (X × Y) :=
  ⟨_, U.2.prod V.2⟩

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
