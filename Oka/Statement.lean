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


open Polynomial

structure IsWeierstrassPolynomial (P : (OkaRing U)[X]) : Prop where
  monic : P.Monic
  apply_zero (i : ℕ) (hi : i < P.degree) : (P.coeff i).toGlobalFun _ 0 = 0

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
