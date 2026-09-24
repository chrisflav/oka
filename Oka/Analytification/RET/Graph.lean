/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.AnalyticSpace.ClopenEqLocus
import Oka.Analytification.RET.EtaleLocalIso
import Oka.Analytification.RET.Pullback
import Oka.Analytification.RET.Separated

/-!
# The graph of a morphism between analytifications

Let `a : A ⟶ X` and `b : B ⟶ X` be morphisms of schemes locally of finite type over `ℂ` and let
`g : A^an ⟶ B^an` be a morphism over `X^an`. With `Z = A ×_X B` and projections `p₁ : Z ⟶ A`,
`p₂ : Z ⟶ B`, the **graph** of `g` is the set of points `z` of `Z^an` with
`g (p₁^an z) = p₂^an z`.

If `b` is finite and étale, the graph is open and closed in `Z^an`: it is the locus where two
morphisms into `B^an` over `X^an` agree, and `b^an` is a local isomorphism (so the locus is open)
and a separated map (so the locus is closed, `b` being affine). In general `p₁^an` restricts to a
bijection from the graph onto `A^an`, computed on the closed points of `Z`.

## Main definitions

- `ComplexAnalytic.analytificationGraph g a b`: the graph of `g` in `(A ×_X B)^an`.

## Main results

- `ComplexAnalytic.isClopen_analytificationGraph`: the graph is open and closed.
- `ComplexAnalytic.exists_mem_analytificationGraph`: every point of `A^an` is the image of a
  point of the graph.
- `ComplexAnalytic.eq_of_mem_analytificationGraph`: two points of the graph with the same image
  in `A^an` are equal.
-/

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace ComplexAnalytic

open AnalyticSpace SchemeLFTℂ

variable {X A B : SchemeLFTℂ.{u}} {a : A ⟶ X} {b : B ⟶ X}
  (g : analytification.obj A ⟶ analytification.obj B)

/-- **The graph of `g : A^an ⟶ B^an`** in `(A ×_X B)^an`: the points `z` with
`g (p₁^an z) = p₂^an z`. -/
def analytificationGraph (a : A ⟶ X) (b : B ⟶ X) :
    Set (analytification.obj (fibreProd a b)) :=
  {z | g.toLRSHom.base ((analytification.map (fibreProdFst a b)).toLRSHom.base z) =
    (analytification.map (fibreProdSnd a b)).toLRSHom.base z}

variable (hg : g ≫ analytification.map b = analytification.map a)
include hg

/-- **The graph is open and closed**, if `b` is finite and étale. -/
theorem isClopen_analytificationGraph [IsFinite b.hom.left] [Etale b.hom.left] :
    IsClopen (analytificationGraph g a b) := by
  haveI : IsLocalIso (analytification.map b) := isLocalIso_analytification_map_of_etale _
  refine isClopen_eqLocus_base_of_isLocalIso (analytification.map b)
    (isSeparatedMap_analytification_map b)
    (g₁ := analytification.map (fibreProdFst a b) ≫ g)
    (g₂ := analytification.map (fibreProdSnd a b)) ?_
  rw [Category.assoc, hg, ← Functor.map_comp, ← Functor.map_comp, fibreProd_condition]

/-- **Every point of `A^an` lies under a point of the graph.** -/
theorem exists_mem_analytificationGraph (y : analytification.obj A) :
    ∃ z ∈ analytificationGraph g a b,
      (analytification.map (fibreProdFst a b)).toLRSHom.base z = y := by
  have hy := (mem_range_analytificationπ_base_iff A _).1 ⟨y, rfl⟩
  have hy' := (mem_range_analytificationπ_base_iff B _).1 ⟨g.toLRSHom.base y, rfl⟩
  obtain ⟨c, hc, hc₁, hc₂⟩ := exists_isClosed_fibreProd a b hy hy' (by
    rw [← analytificationπ_base_map_apply, ← analytificationπ_base_map_apply]
    exact congrArg (fun φ ↦ (analytificationπ X).left.base (φ.toLRSHom.base y)) hg.symm)
  obtain ⟨z, rfl⟩ := (mem_range_analytificationπ_base_iff _ c).2 hc
  have h₁ : (analytification.map (fibreProdFst a b)).toLRSHom.base z = y :=
    analytificationπ_base_injective A ((analytificationπ_base_map_apply _ z).trans hc₁)
  refine ⟨z, ?_, h₁⟩
  change g.toLRSHom.base _ = _
  rw [h₁]
  exact (analytificationπ_base_injective B
    ((analytificationπ_base_map_apply _ z).trans hc₂)).symm

omit hg in
/-- **Two points of the graph with the same image in `A^an` are equal.** -/
theorem eq_of_mem_analytificationGraph {z z' : analytification.obj (fibreProd a b)}
    (hz : z ∈ analytificationGraph g a b) (hz' : z' ∈ analytificationGraph g a b)
    (h : (analytification.map (fibreProdFst a b)).toLRSHom.base z =
      (analytification.map (fibreProdFst a b)).toLRSHom.base z') : z = z' := by
  refine analytificationπ_base_injective _ (fibreProd_ext_of_isClosed a b
    ((mem_range_analytificationπ_base_iff _ _).1 ⟨z, rfl⟩)
    ((mem_range_analytificationπ_base_iff _ _).1 ⟨z', rfl⟩) ?_ ?_)
  · change (fibreProdFst a b).hom.left.base _ = (fibreProdFst a b).hom.left.base _
    rw [← analytificationπ_base_map_apply, ← analytificationπ_base_map_apply, h]
  · change (fibreProdSnd a b).hom.left.base _ = (fibreProdSnd a b).hom.left.base _
    rw [← analytificationπ_base_map_apply, ← analytificationπ_base_map_apply]
    change (analytificationπ B).left.base _ = (analytificationπ B).left.base _
    rw [← show _ = _ from hz, ← show _ = _ from hz', h]

end ComplexAnalytic
