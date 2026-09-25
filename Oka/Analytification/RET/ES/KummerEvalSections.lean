/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.ES.KummerSections

/-!
# Sections of the structure sheaf which are determined by their values

On an open subspace of `ℂⁿ` a section of the structure sheaf is determined by its values. If a
complex analytic space `Y` is covered by local isomorphisms from such spaces, the same holds on
`Y` (`ComplexAnalytic.AnalyticSpace.eq_of_forall_eval_eq`). Then sections of `𝒪_Y` can be glued
from local sections with prescribed values
(`ComplexAnalytic.AnalyticSpace.exists_eval_eq_of_local`),
and sections can be transported along injective local isomorphisms
(`ComplexAnalytic.AnalyticSpace.exists_eval_eq_image`).

## Main definitions

- `ComplexAnalytic.AnalyticSpace.IsLocallyOpenInAffine Y`: every point of `Y` is in the image of a
  local isomorphism from an open subspace of some `ℂⁿ`.

## Main results

- `ComplexAnalytic.AnalyticSpace.eq_of_forall_eval_eq`: sections are determined by their values.
- `ComplexAnalytic.AnalyticSpace.exists_eval_eq_of_local`: gluing sections from their values.
- `ComplexAnalytic.AnalyticSpace.exists_eval_eq_image`: transport along injective local
  isomorphisms.
-/

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

universe u

namespace ComplexAnalytic.AnalyticSpace

/-- The value of a restricted section is the value of the section. -/
lemma eval_presheaf_map (Z : AnalyticSpace.{u}) {U V : Z.Opens} (i : op U ⟶ op V) (z : Z)
    (hz : z ∈ V)
    (t : Z.presheaf.obj (op U)) :
    Z.eval z hz (Z.presheaf.map i t) = Z.eval z (i.unop.le hz) t := by
  rw [eval_apply, eval_apply]
  exact congrArg _ (Z.presheaf.germ_res_apply i.unop z hz t)

/-- On an open subspace of `ℂⁿ`, a section is determined by its values. -/
theorem eq_of_forall_eval_eq_restrict {n : ℕ} (U : (AnalyticSpace.complexAffineSpace.{u} n).Opens)
    {O : ((AnalyticSpace.complexAffineSpace.{u} n).restrict U).Opens}
    {σ σ' : ((AnalyticSpace.complexAffineSpace.{u} n).restrict U).presheaf.obj (op O)}
    (h : ∀ z (hz : z ∈ O), ((AnalyticSpace.complexAffineSpace.{u} n).restrict U).eval z hz σ =
      ((AnalyticSpace.complexAffineSpace.{u} n).restrict U).eval z hz σ') : σ = σ' := by
  refine OkaRing.ext (funext fun ⟨x, hx⟩ ↦ ?_)
  obtain ⟨z, hz, rfl⟩ := hx
  have := h z hz
  rw [eval_restrict_complexAffineSpace_of, eval_restrict_complexAffineSpace_of] at this
  exact this

/-- Every point of `Y` is in the image of a local isomorphism from an open subspace of some
`ℂⁿ`. -/
def IsLocallyOpenInAffine (Y : AnalyticSpace.{u}) : Prop :=
  ∀ y : Y, ∃ (n : ℕ) (U : (AnalyticSpace.complexAffineSpace.{u} n).Opens)
    (φ : (AnalyticSpace.complexAffineSpace.{u} n).restrict U ⟶ Y)
    (z : (AnalyticSpace.complexAffineSpace.{u} n).restrict U), IsLocalIso φ ∧
      φ.toLRSHom.base z = y

/-- **On a space locally isomorphic to opens of `ℂⁿ`, sections are determined by their
values.** -/
theorem eq_of_forall_eval_eq {Y : AnalyticSpace.{u}} (hY : IsLocallyOpenInAffine Y) {O : Y.Opens}
    {s s' : Y.presheaf.obj (op O)} (h : ∀ y (hy : y ∈ O), Y.eval y hy s = Y.eval y hy s') :
    s = s' := by
  refine TopCat.Presheaf.section_ext Y.toSheafedSpace.sheaf O s s' fun y hy ↦ ?_
  obtain ⟨n, U, φ, z, hφ, rfl⟩ := hY y
  have hinj : Function.Injective (φ.toLRSHom.stalkMap z) :=
    (ConcreteCategory.bijective_of_isIso _).1
  apply hinj
  change φ.toLRSHom.stalkMap z (Y.presheaf.germ O _ hy s) =
    φ.toLRSHom.stalkMap z (Y.presheaf.germ O _ hy s')
  rw [LocallyRingedSpace.stalkMap_germ_apply, LocallyRingedSpace.stalkMap_germ_apply]
  congr 1
  refine eq_of_forall_eval_eq_restrict U fun w hw ↦ ?_
  rw [eval_c_app _ φ.isCLinear w hw s, eval_c_app _ φ.isCLinear w hw s']
  exact h _ hw

/-- **Gluing sections from their values.** On a space locally isomorphic to opens of `ℂⁿ`, a
function which is locally the value of a section is the value of a section. -/
theorem exists_eval_eq_of_local {Y : AnalyticSpace.{u}} (hY : IsLocallyOpenInAffine Y)
    {O : Y.Opens} (f : Y → ℂ)
    (hf : ∀ y ∈ O, ∃ (N : Y.Opens) (_ : y ∈ N) (_ : N ≤ O) (σ : Y.presheaf.obj (op N)),
      ∀ w (hw : w ∈ N), Y.eval w hw σ = f w) :
    ∃ s : Y.presheaf.obj (op O), ∀ w (hw : w ∈ O), Y.eval w hw s = f w := by
  choose N hyN hNO σ hσ using fun y : O ↦ hf y.1 y.2
  obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' Y.toSheafedSpace.sheaf N O
    (fun y ↦ homOfLE (hNO y)) (fun y hy ↦ Opens.mem_iSup.2 ⟨⟨y, hy⟩, hyN ⟨y, hy⟩⟩) σ
    fun i j ↦ eq_of_forall_eval_eq hY fun w hw ↦ by
      change Y.eval w hw (Y.presheaf.map _ (σ i)) = Y.eval w hw (Y.presheaf.map _ (σ j))
      rw [eval_presheaf_map, eval_presheaf_map, hσ, hσ]
  refine ⟨s, fun w hw ↦ ?_⟩
  have := congrArg (Y.eval w (hyN ⟨w, hw⟩)) (hs ⟨w, hw⟩)
  change Y.eval w _ (Y.presheaf.map _ s) = _ at this
  rw [eval_presheaf_map, hσ] at this
  exact this

/-- **Transporting a section along an injective local isomorphism**: a section of `𝒪_Z` over `U`
gives a section of `𝒪_Y` over the image of `U` with the same values. -/
theorem exists_eval_eq_image {Z Y : AnalyticSpace.{u}} (φ : Z ⟶ Y) [IsLocalIso φ]
    (hinj : Function.Injective φ.toLRSHom.base) {U : Z.Opens} (t : Z.presheaf.obj (op U)) :
    ∃ σ : Y.presheaf.obj (op ⟨φ.toLRSHom.base '' U,
        (IsLocalIso.isLocalHomeomorph (f := φ)).isOpenMap _ U.isOpen⟩),
      ∀ z (hz : z ∈ U),
        Y.eval (φ.toLRSHom.base z) (Set.mem_image_of_mem _ hz) σ = Z.eval z hz t := by
  haveI : LocallyRingedSpace.IsOpenImmersion φ.toLRSHom :=
    LocallyRingedSpace.IsOpenImmersion.of_stalk_iso _
      ((IsLocalIso.isLocalHomeomorph (f := φ)).isOpenEmbedding_of_injective hinj)
  refine ⟨LocallyRingedSpace.IsOpenImmersion.invApp φ.toLRSHom U t, fun z hz ↦ ?_⟩
  rw [← eval_c_app _ φ.isCLinear z (Set.mem_image_of_mem _ hz)]
  erw [LocallyRingedSpace.IsOpenImmersion.invApp_app_apply]
  exact eval_presheaf_map Z _ z _ t

end ComplexAnalytic.AnalyticSpace
