/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Oka.AlgebraicGeometry.AlgClosed.Basic

/-!
# Finite étale morphisms bijective on closed points are isomorphisms

Let `K` be an algebraically closed field, `Y` a scheme locally of finite type over `K` and
`f : X ⟶ Y` a finite étale morphism which is injective and surjective on closed points. Then `f`
is an isomorphism.

Proof: the two projections `X ×_Y X ⟶ X` agree on closed points (closed points map to closed
points between Jacobson schemes locally of finite type, and `f` is injective on them), hence are
equal because `f` is unramified (`AlgebraicGeometry.ext_of_apply_eq_of_formallyUnramified`).
Thus `f` is a monomorphism. Its image is closed (`f` is finite) and contains all closed points,
hence is everything (`Y` is Jacobson). A flat, quasi-compact, surjective monomorphism is an
isomorphism (`AlgebraicGeometry.Flat.isIso_of_surjective_of_mono`).

## Main results

- `AlgebraicGeometry.mono_of_injOn_closedPoints`: a formally unramified morphism locally of finite
  type between schemes locally of finite type over `K` which is injective on closed points is a
  monomorphism.
- `AlgebraicGeometry.isIso_of_isFinite_of_etale_of_bijOn_closedPoints`: a finite étale morphism
  which is injective and surjective on closed points is an isomorphism.
-/

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} {K : Type u} [Field K] [IsAlgClosed K]

/-- A formally unramified morphism `f : X ⟶ Y` locally of finite type, where `Y` is locally of
finite type over an algebraically closed field, which is injective on closed points is a
monomorphism. -/
theorem mono_of_injOn_closedPoints (f : X ⟶ Y) [FormallyUnramified f] [LocallyOfFiniteType f]
    (i : Y ⟶ Spec (.of K)) [LocallyOfFiniteType i]
    (hinj : ∀ x x' : X, IsClosed {x} → IsClosed {x'} → f x = f x' → x = x') : Mono f := by
  have hXJ : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace (f ≫ i)
  have hYJ : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace i
  have : pullback.fst f f = pullback.snd f f := by
    refine ext_of_apply_eq_of_formallyUnramified f i pullback.condition fun w hw ↦ ?_
    have h₁ : IsClosed {pullback.fst f f w} :=
      (pullback.fst f f).closePoints_subset_preimage_closedPoints hw
    have h₂ : IsClosed {pullback.snd f f w} :=
      (pullback.snd f f).closePoints_subset_preimage_closedPoints hw
    refine hinj _ _ h₁ h₂ ?_
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
  refine ⟨fun a b hab ↦ ?_⟩
  have ha : pullback.lift a b hab ≫ pullback.fst f f = a := pullback.lift_fst _ _ _
  have hb : pullback.lift a b hab ≫ pullback.snd f f = b := pullback.lift_snd _ _ _
  rw [← ha, this, hb]

/-- A closed morphism `f : X ⟶ Y` into a Jacobson scheme whose image contains all closed points
of `Y` is surjective. -/
theorem surjective_of_isClosedMap_of_closedPoints_subset [JacobsonSpace Y] (f : X ⟶ Y)
    (hf : IsClosedMap f) (hsurj : ∀ y : Y, IsClosed {y} → ∃ x, f x = y) : Surjective f := by
  refine ⟨fun y ↦ ?_⟩
  have hcl : IsClosed (Set.range f) := hf.isClosed_range
  have hsub : closedPoints Y ⊆ Set.range f := fun y hy ↦ hsurj y hy
  have : Set.range f = Set.univ := by
    rw [← hcl.closure_eq, ← Set.univ_subset_iff]
    exact (closure_closedPoints (X := Y)).symm.subset.trans (closure_mono hsub)
  exact this.symm.subset (Set.mem_univ y)

/-- **A finite étale morphism which is bijective on closed points is an isomorphism.** Let `Y`
be locally of finite type over an algebraically closed field `K` and `f : X ⟶ Y` finite and
étale. If `f` is injective on closed points and every closed point of `Y` lies in the image of
`f`, then `f` is an isomorphism. -/
theorem isIso_of_isFinite_of_etale_of_bijOn_closedPoints (f : X ⟶ Y) [IsFinite f] [Etale f]
    (i : Y ⟶ Spec (.of K)) [LocallyOfFiniteType i]
    (hinj : ∀ x x' : X, IsClosed {x} → IsClosed {x'} → f x = f x' → x = x')
    (hsurj : ∀ y : Y, IsClosed {y} → ∃ x, f x = y) : IsIso f := by
  have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace i
  have : Mono f := mono_of_injOn_closedPoints f i hinj
  have : Surjective f := surjective_of_isClosedMap_of_closedPoints_subset f f.isClosedMap hsurj
  exact Flat.isIso_of_surjective_of_mono f

end AlgebraicGeometry
