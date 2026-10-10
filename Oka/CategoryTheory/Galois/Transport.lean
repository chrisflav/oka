/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.CategoryTheory.Galois.IsFundamentalgroup
import Mathlib.Algebra.Group.Action.TransferInstance

/-!
# Transporting a group action on fibres along an equivalence

Let `e : C ⥤ D` be an equivalence of categories, `F : C ⥤ FintypeCat`, `F' : D ⥤ FintypeCat` and
`φ : F ≅ e ⋙ F'`. A group `π` acting on the fibres of `F'` acts on the fibres of `F` through `φ`
(`CategoryTheory.PreGaloisCategory.transportMulAction`), and the three conditions of
`CategoryTheory.PreGaloisCategory.isFundamentalGroup_completion` (naturality, transitivity on
connected objects, every finite-index normal subgroup containing the kernel on some fibre) move
from `F'` to `F`. Equivalences preserve connected objects
(`CategoryTheory.PreGaloisCategory.isConnected_obj_of_isEquivalence`); Mathlib states this only for
the specific functor `functorToAction`.
-/

universe u u₁ u₂ v₁ v₂ w

open CategoryTheory Limits

namespace CategoryTheory.PreGaloisCategory

variable {C : Type u₁} [Category.{u₂} C] {D : Type v₁} [Category.{v₂} D]

/-- **Equivalences preserve connected objects.** -/
lemma isConnected_obj_of_isEquivalence (e : C ⥤ D) [e.IsEquivalence] (X : C) [IsConnected X] :
    IsConnected (e.obj X) where
  notInitial h := IsConnected.notInitial (X := X)
    ((h.isInitialObj e.inv).ofIso (e.asEquivalence.unitIso.app X).symm)
  noTrivialComponent Y i _ hY := by
    let E := e.asEquivalence
    let i' : E.inverse.obj Y ⟶ X := E.inverse.map i ≫ (E.unitIso.app X).inv
    haveI : Mono (E.inverse.map i) := inferInstance
    have : IsIso (E.inverse.map i ≫ (E.unitIso.app X).inv) :=
      IsConnected.noTrivialComponent _ i' fun h ↦
        hY ((h.isInitialObj E.functor).ofIso (E.counitIso.app Y))
    haveI : IsIso (E.inverse.map i) :=
      IsIso.of_isIso_comp_right (E.inverse.map i) (E.unitIso.app X).inv
    exact isIso_of_reflects_iso i E.inverse

variable (e : C ⥤ D) {F : C ⥤ FintypeCat.{w}} {F' : D ⥤ FintypeCat.{w}} (φ : F ≅ e ⋙ F')

/-- The bijection `F.obj X ≃ F'.obj (e.obj X)` given by `φ`. -/
def fiberEquivOfIso (X : C) : F.obj X ≃ F'.obj (e.obj X) :=
  FintypeCat.equivEquivIso.symm (φ.app X)

variable {e φ} in
lemma fiberEquivOfIso_naturality {X Y : C} (f : X ⟶ Y) (x : F.obj X) :
    fiberEquivOfIso e φ Y (F.map f x) = F'.map (e.map f) (fiberEquivOfIso e φ X x) :=
  ConcreteCategory.congr_hom (φ.hom.naturality f) x

variable (π : Type u) [Group π] [∀ Y, MulAction π (F'.obj Y)]

/-- The action of `π` on the fibres of `F` transported from `F'` along `φ`. -/
abbrev transportMulAction : ∀ X : C, MulAction π (F.obj X) :=
  fun X ↦ (fiberEquivOfIso e φ X).mulAction π

variable {e φ π}

lemma fiberEquivOfIso_smul {X : C} (g : π) (x : F.obj X) :
    letI := transportMulAction e φ π
    fiberEquivOfIso e φ X (g • x) = g • fiberEquivOfIso e φ X x := by
  letI := transportMulAction e φ π
  change fiberEquivOfIso e φ X ((fiberEquivOfIso e φ X).symm _) = _
  simp

variable (e φ π)

lemma isNaturalSMul_transport [IsNaturalSMul F' π] :
    letI := transportMulAction e φ π
    IsNaturalSMul F π := by
  letI := transportMulAction e φ π
  exact ⟨fun g X Y f x ↦ (fiberEquivOfIso e φ Y).injective <| by
    rw [fiberEquivOfIso_naturality, fiberEquivOfIso_smul, fiberEquivOfIso_smul,
      fiberEquivOfIso_naturality, IsNaturalSMul.naturality]⟩

lemma isPretransitive_transport_obj (X : C)
    (h : MulAction.IsPretransitive π (F'.obj (e.obj X))) :
    letI := transportMulAction e φ π
    MulAction.IsPretransitive π (F.obj X) := by
  letI := transportMulAction e φ π
  refine ⟨fun x y ↦ ?_⟩
  obtain ⟨g, hg⟩ := h.exists_smul_eq (fiberEquivOfIso e φ X x) (fiberEquivOfIso e φ X y)
  exact ⟨g, (fiberEquivOfIso e φ X).injective (by rw [fiberEquivOfIso_smul, hg])⟩

lemma isPretransitive_transport [e.IsEquivalence]
    (htrans : ∀ (Y : D) [IsConnected Y], MulAction.IsPretransitive π (F'.obj Y)) (X : C)
    [IsConnected X] :
    letI := transportMulAction e φ π
    MulAction.IsPretransitive π (F.obj X) := by
  haveI := isConnected_obj_of_isEquivalence e X
  exact isPretransitive_transport_obj e φ π X (htrans (e.obj X))

lemma exists_ker_le_transport [e.IsEquivalence] [IsNaturalSMul F' π] {N : Subgroup π}
    (hN : ∃ Y : D, ∀ h : π, (∀ y : F'.obj Y, h • y = y) → h ∈ N) :
    letI := transportMulAction e φ π
    ∃ X : C, ∀ h : π, (∀ x : F.obj X, h • x = x) → h ∈ N := by
  letI := transportMulAction e φ π
  obtain ⟨Y, hY⟩ := hN
  let E := e.asEquivalence
  refine ⟨E.inverse.obj Y, fun h hh ↦ hY h fun y ↦ ?_⟩
  let c : e.obj (E.inverse.obj Y) ≅ Y := E.counitIso.app Y
  obtain ⟨x, hx⟩ := (fiberEquivOfIso e φ (E.inverse.obj Y)).surjective (F'.map c.inv y)
  have hcy : F'.map c.hom (fiberEquivOfIso e φ _ x) = y := by
    rw [hx]
    exact ConcreteCategory.congr_hom (F'.mapIso c).inv_hom_id y
  rw [← hcy, ← IsNaturalSMul.naturality, ← fiberEquivOfIso_smul, hh]

end CategoryTheory.PreGaloisCategory
