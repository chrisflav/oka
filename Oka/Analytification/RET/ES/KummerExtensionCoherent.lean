/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.ES.KummerExtensionFree
import Oka.AnalyticSpace.Coherent
import Oka.Algebra.Category.ModuleCat.Sheaf.Free

/-!
# The canonical extension is a coherent sheaf of `𝒪_S`-modules

Keep the notation of `Oka/Analytification/RET/ES/KummerExtensionSheaf.lean`. Restricting scalars
along `𝒪_S ⟶ 𝒞̄` makes the canonical extension a sheaf of `𝒪_S`-modules
(`ComplexAnalytic.KummerModel.extensionModule`). For a decomposition `e` of `W` into Kummer covers
of degrees `kᵢ`, the monomials `uʲ`, `j < kᵢ`, on the Kummer covers form a basis: the induced
morphism from the free sheaf of rank `∑ kᵢ` is an isomorphism
(`ComplexAnalytic.KummerModel.isIso_extensionFreeHom`). Hence `𝒞̄` is coherent
(`ComplexAnalytic.KummerModel.isCoherent_extensionModule`).

## Main definitions

- `ComplexAnalytic.KummerModel.extensionRingSheaf hW`: `𝒞̄` as a sheaf of rings on the site of `S`.
- `ComplexAnalytic.KummerModel.extensionModule hW`: `𝒞̄` as a sheaf of `𝒪_S`-modules.
- `ComplexAnalytic.KummerModel.extensionFreeHom e hW`: the morphism `𝒪_S^{∑ kᵢ} ⟶ 𝒞̄`.

## Main results

- `ComplexAnalytic.KummerModel.isIso_extensionFreeHom`,
  `ComplexAnalytic.KummerModel.extensionModuleIsoFree`: `𝒞̄ ≅ 𝒪_S^{∑ kᵢ}`.
- `ComplexAnalytic.KummerModel.isCoherent_extensionModule`: `𝒞̄` is coherent.
-/

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace Polynomial

universe u

namespace ComplexAnalytic.KummerModel

open AnalyticSpace

noncomputable section

variable {m : ℕ} {B : Set (ULift.{u} (Fin m) → ℂ)} {hB : IsOpen B}
  {W : FiniteEtaleOver (punctured hB)}

/-- The canonical extension as a sheaf of rings on the site of `S`. -/
def extensionRingSheaf (hW : IsLocallyOpenInAffine W.left) :
    Sheaf (Opens.grothendieckTopology ↑(disc hB).toPresheafedSpace) RingCat.{u} :=
  ⟨extensionPresheaf W ⋙ forget₂ CommRingCat.{u} RingCat.{u},
    (TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget₂ CommRingCat.{u} RingCat.{u})
      (extensionPresheaf W)).1 (isSheaf_extensionPresheaf hW)⟩

/-- The structure morphism `𝒪_S ⟶ 𝒞̄` of sheaves of rings. -/
def extensionRingHom (hW : IsLocallyOpenInAffine W.left) :
    (disc hB).toLocallyRingedSpace.ringSheaf ⟶ extensionRingSheaf hW :=
  ⟨Functor.whiskerRight (extensionAlgebraHom hW) (forget₂ CommRingCat.{u} RingCat.{u})⟩

/-- **The canonical extension as a sheaf of `𝒪_S`-modules.** -/
def extensionModule (hW : IsLocallyOpenInAffine W.left) :
    SheafOfModules.{u} (disc hB).toLocallyRingedSpace.ringSheaf :=
  (SheafOfModules.restrictScalars (extensionRingHom hW)).obj (SheafOfModules.unit _)

variable {ι : Type u} {k : ι → ℕ+} [Finite ι]
  (e : W ≅ FiniteEtaleOver.sigma fun i ↦ cover hB (k i)) (hW : IsLocallyOpenInAffine W.left)

open Classical in
/-- The basis section `uʲ` on the `i`-th Kummer cover, over all of `S`. -/
def basisSection (p : Σ i, Fin (k i)) : boundedSubring W ⊤ :=
  coeffEquiv e ⊤ (Pi.single p.1 (Pi.single p.2 1))

/-- The morphism `𝒪_S^{∑ kᵢ} ⟶ 𝒞̄` given by the monomials `uʲ` on the Kummer covers. -/
def extensionFreeHom :
    SheafOfModules.free (Σ i, Fin (k i)) ⟶ extensionModule hW :=
  (extensionModule hW).freeHomEquiv.symm fun p ↦
    SheafOfModules.sectionOfTerminal Limits.isTerminalTop (extensionModule hW)
      (basisSection e p)

open Classical in
lemma extensionFreeHom_app (V : (disc hB).Opens)
    (b : (SheafOfModules.free (R := (disc hB).toLocallyRingedSpace.ringSheaf)
      (Σ i, Fin (k i))).val.obj (op V)) :
    (extensionFreeHom e hW).val.app (op V) b =
      coeffEquiv e V fun i j ↦ SheafOfModules.freeEval (op V) b ⟨i, j⟩ := by
  haveI := Fintype.ofFinite ι
  rw [SheafOfModules.val_app_eq_sum]
  simp only [extensionFreeHom, Equiv.apply_symm_apply, SheafOfModules.sectionOfTerminal_val]
  let c : (Σ i, Fin (k i)) → (disc hB).presheaf.obj (op V) :=
    fun p ↦ SheafOfModules.freeEval (op V) b p
  change _ = coeffEquiv e V fun i j ↦ c ⟨i, j⟩
  have hfam : (fun i j ↦ c ⟨i, j⟩) =
      ∑ p : Σ i, Fin (k i), c p •
        (Pi.single p.1 (Pi.single p.2 1) : ∀ i, Fin (k i) → (disc hB).presheaf.obj (op V)) := by
    funext i j
    rw [Finset.sum_apply, Finset.sum_apply, Finset.sum_eq_single ⟨i, j⟩]
    · simp
    · rintro ⟨i', j'⟩ - hne
      by_cases hi : i' = i
      · subst hi
        have hj : j' ≠ j := fun h ↦ hne (by rw [h])
        simp [hj]
      · simp [hi]
    · simp
  rw [hfam, map_sum]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [map_smul]
  congr 1
  refine (extensionPresheaf_map_coeffEquiv (e := e) le_top _).trans (congrArg (coeffEquiv e V) ?_)
  funext i j
  by_cases hi : p.1 = i
  · subst hi
    by_cases hj : p.2 = j
    · subst hj
      simp
    · simp [Ne.symm hj]
  · simp [Ne.symm hi]

/-- **The monomials `uʲ` on the Kummer covers form a basis of `𝒞̄`.** -/
theorem isIso_extensionFreeHom : IsIso (extensionFreeHom e hW) := by
  classical
  haveI := Fintype.ofFinite ι
  have hbij (V : (disc hB).Opens) :
      Function.Bijective ((extensionFreeHom e hW).val.app (op V)) := by
    have : ⇑((extensionFreeHom e hW).val.app (op V)) = ⇑(coeffEquiv e V) ∘
        (fun b i j ↦ SheafOfModules.freeEval (op V) b ⟨i, j⟩) :=
      funext (extensionFreeHom_app e hW V)
    rw [this]
    refine (coeffEquiv e V).bijective.comp ?_
    exact (Equiv.piCurry fun (i : ι) (_ : Fin (k i)) ↦ (disc hB).presheaf.obj (op V)).bijective.comp
      (SheafOfModules.freeEvalEquiv (R := (disc hB).toLocallyRingedSpace.ringSheaf)
        (I := Σ i, Fin (k i)) (op V)).bijective
  haveI : ∀ V : (Opens ↑(disc hB).toPresheafedSpace)ᵒᵖ,
      IsIso (((SheafOfModules.toSheaf _).map (extensionFreeHom e hW)).hom.app V) :=
    fun V ↦ (ConcreteCategory.isIso_iff_bijective _).2 (hbij V.unop)
  have h₁ : IsIso ((SheafOfModules.toSheaf _).map (extensionFreeHom e hW)).hom :=
    NatIso.isIso_of_isIso_app _
  haveI : IsIso ((sheafToPresheaf _ _).map
      ((SheafOfModules.toSheaf _).map (extensionFreeHom e hW))) := h₁
  haveI : IsIso ((SheafOfModules.toSheaf _).map (extensionFreeHom e hW)) :=
    isIso_of_reflects_iso _ (sheafToPresheaf _ _)
  exact isIso_of_reflects_iso _ (SheafOfModules.toSheaf _)

/-- **The canonical extension is free of rank `∑ kᵢ`**, as a sheaf of `𝒪_S`-modules. -/
def extensionModuleIsoFree :
    SheafOfModules.free (Σ i, Fin (k i)) ≅ extensionModule hW :=
  haveI := isIso_extensionFreeHom e hW
  asIso (extensionFreeHom e hW)

include e in
/-- **The canonical extension is a coherent sheaf of `𝒪_S`-modules.** -/
theorem isCoherent_extensionModule : (extensionModule hW).IsCoherent :=
  haveI : (SheafOfModules.free (R := (disc hB).toLocallyRingedSpace.ringSheaf)
      (Σ i, Fin (k i))).IsCoherent := (disc hB).isCoherent_free _
  SheafOfModules.IsCoherent.of_iso.{u} (extensionModuleIsoFree e hW)

end

end ComplexAnalytic.KummerModel
