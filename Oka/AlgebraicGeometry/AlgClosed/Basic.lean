/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Oka.AlgebraicGeometry.Morphisms.FormallyUnramified

/-!
# Morphisms into unramified schemes over an algebraically closed field

Let `K` be an algebraically closed field and `X` locally of finite type over `K`. Closed points of
`X` have residue field `K` (`AlgebraicGeometry.residueFieldIsoBase`), so a `K`-morphism out of
`Spec κ(x)` is determined by its image point. Combined with
`AlgebraicGeometry.ext_of_fromSpecResidueField_eq_of_formallyUnramified`, two morphisms into a
scheme which is unramified over some base are equal as soon as they agree on the closed points.
No reducedness of `X` and no separatedness is needed.

## Main results

- `AlgebraicGeometry.ext_of_apply_eq_of_formallyUnramified`: if `s : Y ⟶ Z` is formally
  unramified and locally of finite type, `Z` is locally of finite type over `K`, and `f g : X ⟶ Y`
  agree over `Z` and on all closed points of `X`, then `f = g`.
-/

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **Morphisms into an unramified scheme over an algebraically closed field are determined by
their values on closed points.** Let `K` be algebraically closed, `i : Z ⟶ Spec K` locally of
finite type, `s : Y ⟶ Z` formally unramified and locally of finite type, and `f g : X ⟶ Y` with
`f ≫ s = g ≫ s` and `X` locally of finite type over `K`. If `f x = g x` for every closed point
`x` of `X`, then `f = g`. -/
theorem ext_of_apply_eq_of_formallyUnramified {X Y Z : Scheme.{u}} {K : Type u} [Field K]
    [IsAlgClosed K] {f g : X ⟶ Y} (s : Y ⟶ Z) [FormallyUnramified s] [LocallyOfFiniteType s]
    (i : Z ⟶ Spec (.of K)) [LocallyOfFiniteType i] [LocallyOfFiniteType (f ≫ s ≫ i)]
    (h : f ≫ s = g ≫ s) (H : ∀ x, IsClosed {x} → f x = g x) : f = g := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace (f ≫ s ≫ i)
  refine ext_of_fromSpecResidueField_eq_of_formallyUnramified s h fun x hx ↦ ?_
  rw [← cancel_epi (Spec.map (residueFieldIsoBase (f ≫ s ≫ i) x hx).hom)]
  refine ext_of_apply_closedPoint_eq (s ≫ i) ?_ ?_ (by simpa using H x hx)
  · simp only [Category.assoc, ← SpecMap_residueFieldIsoBase_inv (f ≫ s ≫ i) x hx,
      ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id]
  · simp only [Category.assoc, ← reassoc_of% h, ← SpecMap_residueFieldIsoBase_inv (f ≫ s ≫ i) x hx,
      ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id]

end AlgebraicGeometry
