/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.AnalyticSpace.PushforwardStalkCoherent
import Oka.Geometry.RingedSpace.LocallyRingedSpace.HomSheafStalk
import Mathlib.RingTheory.Regular.RegularSequence

/-!
# Regular sequences on the stalks of `f_* 𝒪_X`

For a morphism `f : X ⟶ Y` of locally ringed spaces, the stalk at `y` of the sheaf of
`𝒪_Y`-modules `f_* 𝒪_X` (`AlgebraicGeometry.LocallyRingedSpace.Hom.pushUnit`) is described by
the stalk `(f_* 𝒪_X)_y` of the pushforward presheaf of rings. A pair of germs is weakly regular on
the former if its image under `𝒪_{Y,y} → (f_* 𝒪_X)_y` is weakly regular on the latter
(`AlgebraicGeometry.LocallyRingedSpace.Hom.isWeaklyRegular_stalk_pushUnit`).
-/

open CategoryTheory TopologicalSpace Opposite RingTheory.Sequence Pointwise

universe u

section Algebra

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {g h : R}

/-- **Weak regularity of a pair, elementwise**: `[g, h]` is weakly regular on `M` iff `g` is
a nonzerodivisor on `M` and `h m ∈ g M` implies `m ∈ g M`. -/
theorem RingTheory.Sequence.isWeaklyRegular_pair_iff :
    IsWeaklyRegular M [g, h] ↔
      IsSMulRegular M g ∧ ∀ m m' : M, h • m = g • m' → ∃ m'', m = g • m'' := by
  rw [isWeaklyRegular_cons_iff, isWeaklyRegular_cons_iff]
  have hmem : ∀ x : M, Submodule.Quotient.mk (p := g • (⊤ : Submodule R M)) x = 0 ↔
      ∃ m'', x = g • m'' := fun x ↦ by
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_pointwise_iff_exists]
    simp [eq_comm]
  refine and_congr_right fun _ ↦ ⟨fun ⟨H, _⟩ m m' e ↦ ?_, fun H ↦ ⟨?_, IsWeaklyRegular.nil _ _⟩⟩
  · refine (hmem m).1 (H.right_eq_zero_of_smul ?_)
    rw [← Submodule.Quotient.mk_smul, e]
    exact (hmem _).2 ⟨m', rfl⟩
  · refine isSMulRegular_iff_right_eq_zero_of_smul.2 fun x hx ↦ ?_
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [← Submodule.Quotient.mk_smul, hmem] at hx
    obtain ⟨m', hm'⟩ := hx
    exact (hmem m).2 (H m m' hm')

end Algebra

noncomputable section

namespace AlgebraicGeometry.LocallyRingedSpace.Hom

variable {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y)

/-- The germ in `(f_* 𝒪_X)_y` of a section of `𝒪_X` over `f⁻¹ V`. -/
abbrev pgerm (V : Opens Y) {y : Y} (hy : y ∈ V)
    (s : X.presheaf.obj (op ((Opens.map f.base).obj V))) : (f.base _* X.presheaf).stalk y :=
  (f.base _* X.presheaf).germ V y hy s

lemma pgerm_eq_zero_iff (V : Opens Y) {y : Y} (hy : y ∈ V)
    (s : X.presheaf.obj (op ((Opens.map f.base).obj V))) :
    f.pgerm V hy s = 0 ↔ ∃ (W : Opens Y) (hW : W ≤ V), y ∈ W ∧
      X.res ((Opens.map f.base).monotone hW) s = 0 := by
  constructor
  · intro h
    obtain ⟨W, hW, hyW, e⟩ := f.exists_res_eq_of_pushforward_germ_eq hy s 0
      (h.trans (map_zero _).symm)
    exact ⟨W, hW, hyW, e.trans (res_zero _ _)⟩
  · rintro ⟨W, hW, hyW, e⟩
    exact (germ_res_pushforward f hW hyW s).symm.trans ((congrArg _ e).trans (map_zero _))

lemma mgerm_pushUnit_eq_zero_iff (V : Opens Y) {y : Y} (hy : y ∈ V)
    (s : (pushUnit f).val.obj (op V)) :
    mgerm (pushUnit f) V y hy s = 0 ↔ f.pgerm V hy s = 0 := by
  rw [pgerm_eq_zero_iff]
  constructor
  · intro h
    obtain ⟨W, hW, hyW, e⟩ := exists_modRes_eq_zero_of_mgerm_eq_zero y hy s h
    exact ⟨W, hW, hyW, e⟩
  · rintro ⟨W, hW, hyW, e⟩
    rw [← mgerm_modRes hW y hyW s]
    change mgerm (pushUnit f) W y hyW (X.res ((Opens.map f.base).monotone hW) s) = 0
    rw [e]
    exact mgerm_zero _ _ _

lemma mgerm_pushUnit_eq_iff (V : Opens Y) {y : Y} (hy : y ∈ V)
    (s t : (pushUnit f).val.obj (op V)) :
    mgerm (pushUnit f) V y hy s = mgerm (pushUnit f) V y hy t ↔
      f.pgerm V hy s = f.pgerm V hy t := by
  have e₁ : mgerm (pushUnit f) V y hy (s - t) =
      mgerm (pushUnit f) V y hy s - mgerm (pushUnit f) V y hy t := map_sub _ s t
  have e₂ : f.pgerm V hy (s - t) = f.pgerm V hy s - f.pgerm V hy t := map_sub _ s t
  rw [← sub_eq_zero, ← e₁, mgerm_pushUnit_eq_zero_iff, e₂, sub_eq_zero]

lemma pgerm_mul_cApp (V : Opens Y) {y : Y} (hy : y ∈ V) (r : Y.presheaf.obj (op V))
    (s : X.presheaf.obj (op ((Opens.map f.base).obj V))) :
    f.pgerm V hy (f.cApp V r * s) =
      f.stalkAlgMap y (Y.presheaf.germ V y hy r) * f.pgerm V hy s :=
  (map_mul _ _ _).trans (congrArg (· * _) (stalkAlgMap_germ f hy r).symm)

/-- Every element of the stalk of `f_* 𝒪_X` at `y` is the germ of a section over an open inside
a given neighbourhood of `y`. -/
lemma exists_mgerm_pushUnit_eq {y : Y} {U : Opens Y} (hy : y ∈ U)
    (m : (Y.stalkFunctor y).obj (pushUnit f)) :
    ∃ (V : Opens Y) (_ : V ≤ U) (hyV : y ∈ V)
      (s : X.presheaf.obj (op ((Opens.map f.base).obj V))),
      m = mgerm (pushUnit f) V y hyV s := by
  obtain ⟨V, hyV, s, rfl⟩ := exists_mgerm_eq y m
  refine ⟨V ⊓ U, inf_le_right, ⟨hyV, hy⟩, sectRes (pushUnit f) inf_le_left s, ?_⟩
  exact (mgerm_modRes inf_le_left y ⟨hyV, hy⟩ s).symm

lemma germ_smul_mgerm_pushUnit {y : Y} {U V : Opens Y} (hVU : V ≤ U) (hyV : y ∈ V)
    (g : Y.presheaf.obj (op U)) (s : X.presheaf.obj (op ((Opens.map f.base).obj V))) :
    Y.presheaf.germ U y (hVU hyV) g • mgerm (pushUnit f) V y hyV s =
      mgerm (pushUnit f) V y hyV (show (pushUnit f).val.obj (op V) from
        f.cApp V (Y.res hVU g) * s) := by
  rw [← germ_res hVU y hyV g]
  exact (mgerm_smul V y hyV _ _).symm

/-- **Weak regularity on the stalks of `f_* 𝒪_X`**: a pair of germs is weakly regular on the
stalk of the sheaf of modules `f_* 𝒪_X` if its image in the stalk of the pushforward presheaf of
rings is weakly regular there. -/
theorem isWeaklyRegular_stalk_pushUnit {y : Y} {U : Opens Y} (hy : y ∈ U)
    (g h : Y.presheaf.obj (op U))
    (hreg : IsWeaklyRegular ((f.base _* X.presheaf).stalk y)
      [f.stalkAlgMap y (Y.presheaf.germ U y hy g), f.stalkAlgMap y (Y.presheaf.germ U y hy h)]) :
    IsWeaklyRegular ((Y.stalkFunctor y).obj (pushUnit f))
      [Y.presheaf.germ U y hy g, Y.presheaf.germ U y hy h] := by
  rw [isWeaklyRegular_pair_iff] at hreg ⊢
  obtain ⟨hg, hh⟩ := hreg
  have hgerm : ∀ {V : Opens Y} (hVU : V ≤ U) (hyV : y ∈ V) (a : Y.presheaf.obj (op U)),
      Y.presheaf.germ V y hyV (Y.res hVU a) = Y.presheaf.germ U y hy a :=
    fun hVU hyV a ↦ germ_res hVU y hyV a
  refine ⟨isSMulRegular_iff_right_eq_zero_of_smul.2 fun m hm ↦ ?_, fun m m' e ↦ ?_⟩
  · obtain ⟨V, hVU, hyV, s, rfl⟩ := exists_mgerm_pushUnit_eq f hy m
    rw [germ_smul_mgerm_pushUnit f hVU hyV, mgerm_pushUnit_eq_zero_iff, pgerm_mul_cApp,
      hgerm hVU hyV] at hm
    rw [mgerm_pushUnit_eq_zero_iff]
    exact hg.right_eq_zero_of_smul hm
  · obtain ⟨V₁, h₁, hy₁, s₁, rfl⟩ := exists_mgerm_pushUnit_eq f hy m
    obtain ⟨V, h₂, hyV, s₂, rfl⟩ := exists_mgerm_pushUnit_eq f hy₁ m'
    have hVU : V ≤ U := h₂.trans h₁
    let s : X.presheaf.obj (op ((Opens.map f.base).obj V)) :=
      X.res ((Opens.map f.base).monotone h₂) s₁
    have hs : mgerm (pushUnit f) V₁ y hy₁ s₁ = mgerm (pushUnit f) V y hyV s :=
      (mgerm_modRes (N := pushUnit f) h₂ y hyV s₁).symm
    rw [hs, germ_smul_mgerm_pushUnit f hVU hyV, germ_smul_mgerm_pushUnit f hVU hyV,
      mgerm_pushUnit_eq_iff, pgerm_mul_cApp, pgerm_mul_cApp, hgerm hVU hyV, hgerm hVU hyV] at e
    obtain ⟨z, hz⟩ := hh _ _ e
    obtain ⟨W₀, hyW₀, s₀, rfl⟩ := (f.base _* X.presheaf).exists_germ_eq z
    let W := W₀ ⊓ V
    have hyW : y ∈ W := ⟨hyW₀, hyV⟩
    have hWV : W ≤ V := inf_le_right
    let s'' : X.presheaf.obj (op ((Opens.map f.base).obj W)) :=
      X.res ((Opens.map f.base).monotone (inf_le_left : W ≤ W₀)) s₀
    have hz' : f.pgerm W hyW (X.res ((Opens.map f.base).monotone hWV) s) =
        f.pgerm W hyW (f.cApp W (Y.res (hWV.trans hVU) g) * s'') := by
      rw [pgerm_mul_cApp, hgerm (hWV.trans hVU) hyW]
      exact (germ_res_pushforward f hWV hyW s).trans (hz.trans (congrArg _
        (germ_res_pushforward f inf_le_left hyW s₀).symm))
    refine ⟨mgerm (pushUnit f) W y hyW s'', ?_⟩
    rw [hs, germ_smul_mgerm_pushUnit f (hWV.trans hVU) hyW]
    refine (mgerm_modRes (N := pushUnit f) hWV y hyW s).symm.trans ?_
    exact (mgerm_pushUnit_eq_iff f W hyW _ _).2 hz'

end AlgebraicGeometry.LocallyRingedSpace.Hom

end
