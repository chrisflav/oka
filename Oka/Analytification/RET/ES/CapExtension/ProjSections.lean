/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.ES.CapExtension.ProjKummer
import Oka.Analytification.RET.ES.CapExtension.BaseSheaf

/-!
# Sections of the sheaf of the cap

Keep the notation of `Oka/Analytification/RET/ES/CapExtension/ProjSheaf.lean`. A section of the
sheaf of the cap `𝒞` over an open `O` of `P^an` is given by its values on `W` and on `K` over `O`
(`ComplexAnalytic.Cap.AnnulusDecomposition.capModule_ext`), and a compatible pair of a bounded
section of `𝒪_W` and a section of `𝒪_K` is a section of `𝒞`
(`ComplexAnalytic.Cap.AnnulusDecomposition.mkCap`).
-/

open CategoryTheory Opposite Topology TopologicalSpace Set Filter Metric Limits

universe u

namespace ComplexAnalytic.Cap.AnnulusDecomposition

open AnalyticSpace BoundedSections relProjectiveSpaceAn relProjectiveLine
open AlgebraicGeometry AlgebraicGeometry.LocallyRingedSpace
open KummerModel (splitEquiv)

noncomputable section

variable {m : ℕ} {N N₀ : (AnalyticSpace.complexAffineSpace.{u} (m + 1)).Opens}
  {W : FiniteEtaleOver (space N₀)} {F : WeierstrassForm N N₀}
  {D : AnnulusDecomposition W F.G F.ρ} {O : (relProjectiveSpaceAn.{u} m 1).Opens}

/-- The values on `W` of a section of `𝒞`. -/
def capWVal (s : D.capModule.val.obj (op O)) (w : W.left) : ℂ :=
  evalFun (wPart s.1) w

/-- The values on `K` of a section of `𝒞`. -/
def capKVal (s : D.capModule.val.obj (op O)) (x : Cn.{u} (m + 1)) : ℂ :=
  holFun (kPart s.1) x

lemma capWVal_compat (s : D.capModule.val.obj (op O)) (i : D.ι)
    (z : KummerAnnulus.base F.G F.ρ⁻¹ F.ρ (D.deg i))
    (hz : D.toFun ⟨i, z⟩ ∈ (Opens.map (projW W).toLRSHom.base).obj O) :
    capWVal s (D.toFun ⟨i, z⟩) = capKVal s (D.kPt i (invCoord z.1)) :=
  s.2 i z hz

variable (D) in
/-- A pair of a bounded section of `𝒪_W` and a section of `𝒪_K`, as a section of the ambient
sheaf. -/
def mkAmb (a : W.left.presheaf.obj (op ((Opens.map (projW W).toLRSHom.base).obj O)))
    (ha : IsBoundedNear (projW W) (removedW N N₀) a)
    (g : (space D.kOpens).presheaf.obj (op ((Opens.map D.kMap.toLRSHom.base).obj O))) :
    D.capAmb.val.obj (op O) :=
  (biprod.inl : capW W ⟶ D.capAmb).val.app (op O) (show (capW W).val.obj (op O) from ⟨a, ha⟩) +
    (biprod.inr : D.capK ⟶ D.capAmb).val.app (op O) g

lemma wPart_mkAmb (a) (ha) (g) : wPart (D.mkAmb (O := O) a ha g) = a := by
  change wPart (_ + _) = a
  rw [wPart_add]
  simp only [wPart]
  rw [SheafOfModules.biprod_fst_inl_apply, SheafOfModules.biprod_fst_inr_apply]
  exact add_zero a

lemma kPart_mkAmb (a) (ha) (g) : kPart (D.mkAmb (O := O) a ha g) = g := by
  change kPart (_ + _) = g
  rw [kPart_add]
  simp only [kPart]
  rw [SheafOfModules.biprod_snd_inl_apply, SheafOfModules.biprod_snd_inr_apply]
  exact zero_add g

variable (D) in
/-- A compatible pair of a bounded section of `𝒪_W` and a section of `𝒪_K`, as a section of `𝒞`. -/
def mkCap (a : W.left.presheaf.obj (op ((Opens.map (projW W).toLRSHom.base).obj O)))
    (ha : IsBoundedNear (projW W) (removedW N N₀) a)
    (g : (space D.kOpens).presheaf.obj (op ((Opens.map D.kMap.toLRSHom.base).obj O)))
    (hc : ∀ (i : D.ι) (z : KummerAnnulus.base F.G F.ρ⁻¹ F.ρ (D.deg i)),
      D.toFun ⟨i, z⟩ ∈ (Opens.map (projW W).toLRSHom.base).obj O →
        evalFun a (D.toFun ⟨i, z⟩) = holFun g (D.kPt i (invCoord z.1))) :
    D.capModule.val.obj (op O) :=
  ⟨D.mkAmb a ha g, fun i z hz ↦ by
    change evalFun (wPart (D.mkAmb a ha g)) _ = holFun (kPart (D.mkAmb a ha g)) _
    rw [wPart_mkAmb, kPart_mkAmb]
    exact hc i z hz⟩

lemma wPart_mkCap (a) (ha) (g) (hc) :
    wPart (D.mkCap (O := O) a ha g hc).1 = a :=
  wPart_mkAmb a ha g

lemma kPart_mkCap (a) (ha) (g) (hc) :
    kPart (D.mkCap (O := O) a ha g hc).1 = g :=
  kPart_mkAmb a ha g

/-- **Sections of `𝒞` are determined by their values.** -/
theorem capModule_ext {s t : D.capModule.val.obj (op O)}
    (hW : ∀ w ∈ (Opens.map (projW W).toLRSHom.base).obj O, capWVal s w = capWVal t w)
    (hK : ∀ x ∈ img ((Opens.map D.kMap.toLRSHom.base).obj O), capKVal s x = capKVal t x) :
    s = t := by
  refine Subtype.ext (SheafOfModules.biprod_ext ?_ ?_)
  · refine Subtype.ext (eq_of_forall_eval_eq (isLocallyOpenInAffine_left W) fun w hw ↦ ?_)
    have := hW w hw
    rwa [capWVal, capWVal, evalFun_of_mem _ hw, evalFun_of_mem _ hw] at this
  · exact eq_of_holFun_eq fun x hx ↦ hK x hx

lemma capWVal_add (s t : D.capModule.val.obj (op O)) {w : W.left}
    (hw : w ∈ (Opens.map (projW W).toLRSHom.base).obj O) :
    capWVal (s + t) w = capWVal s w + capWVal t w := by
  change evalFun (wPart (s.1 + t.1)) w = _
  rw [wPart_add, evalFun_add W _ _ hw]
  rfl

lemma capKVal_add (s t : D.capModule.val.obj (op O)) {x : Cn.{u} (m + 1)}
    (hx : x ∈ img ((Opens.map D.kMap.toLRSHom.base).obj O)) :
    capKVal (s + t) x = capKVal s x + capKVal t x := by
  change holFun (kPart (s.1 + t.1)) x = _
  rw [kPart_add, holFun_add _ _ hx]
  rfl

lemma capWVal_smul (r : (relProjectiveSpaceAn.{u} m 1).presheaf.obj (op O))
    (s : D.capModule.val.obj (op O)) {w : W.left}
    (hw : w ∈ (Opens.map (projW W).toLRSHom.base).obj O) :
    capWVal (r • s) w =
      (relProjectiveSpaceAn.{u} m 1).eval ((projW W).toLRSHom.base w) hw r * capWVal s w := by
  change evalFun (wPart (r • s.1)) w = _
  rw [wPart_smul, evalFun_mul W _ _ hw, evalFun_c_app_projW r hw]
  rfl

lemma capKVal_smul (r : (relProjectiveSpaceAn.{u} m 1).presheaf.obj (op O))
    (s : D.capModule.val.obj (op O)) {x : Cn.{u} (m + 1)}
    (hx : x ∈ img ((Opens.map D.kMap.toLRSHom.base).obj O)) :
    capKVal (r • s) x = (relProjectiveSpaceAn.{u} m 1).eval
      (D.kMap.toLRSHom.base ⟨x, img_le _ x hx⟩) (mem_img_iff.1 hx).2 r * capKVal s x := by
  change holFun (kPart (r • s.1)) x = _
  rw [kPart_smul, holFun_mul _ _ hx, holFun_c_app_kMap r hx]
  rfl

lemma capWVal_res {O' : (relProjectiveSpaceAn.{u} m 1).Opens} (h : O' ≤ O)
    (s : D.capModule.val.obj (op O)) {w : W.left}
    (hw : w ∈ (Opens.map (projW W).toLRSHom.base).obj O') :
    capWVal (sectRes D.capModule h s) w = capWVal s w := by
  change evalFun (wPart (sectRes D.capAmb h s.1)) w = _
  rw [wPart_res, evalFun_map W _ _ hw]
  rfl

lemma capKVal_res {O' : (relProjectiveSpaceAn.{u} m 1).Opens} (h : O' ≤ O)
    (s : D.capModule.val.obj (op O)) {x : Cn.{u} (m + 1)}
    (hx : x ∈ img ((Opens.map D.kMap.toLRSHom.base).obj O')) :
    capKVal (sectRes D.capModule h s) x = capKVal s x := by
  change holFun (kPart (sectRes D.capAmb h s.1)) x = _
  rw [kPart_res, holFun_map _ _ hx]
  rfl

lemma capWVal_sum_smul {κ : Type*} [Fintype κ]
    (r : κ → (relProjectiveSpaceAn.{u} m 1).presheaf.obj (op O))
    (s : κ → D.capModule.val.obj (op O)) {w : W.left}
    (hw : w ∈ (Opens.map (projW W).toLRSHom.base).obj O) :
    capWVal (∑ k, r k • s k) w = ∑ k,
      (relProjectiveSpaceAn.{u} m 1).eval ((projW W).toLRSHom.base w) hw (r k) *
        capWVal (s k) w := by
  classical
  have : ∀ t : Finset κ, capWVal (∑ k ∈ t, r k • s k) w = ∑ k ∈ t,
      (relProjectiveSpaceAn.{u} m 1).eval ((projW W).toLRSHom.base w) hw (r k) *
        capWVal (s k) w := fun t ↦ by
    induction t using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      change evalFun (wPart (0 : D.capAmb.val.obj (op O))) w = 0
      rw [wPart_zero, evalFun_of_mem _ hw, map_zero]
    | insert k t hk ih =>
      rw [Finset.sum_insert hk, Finset.sum_insert hk, capWVal_add _ _ hw, capWVal_smul _ _ hw, ih]
  exact this Finset.univ

lemma capKVal_sum_smul {κ : Type*} [Fintype κ]
    (r : κ → (relProjectiveSpaceAn.{u} m 1).presheaf.obj (op O))
    (s : κ → D.capModule.val.obj (op O)) {x : Cn.{u} (m + 1)}
    (hx : x ∈ img ((Opens.map D.kMap.toLRSHom.base).obj O)) :
    capKVal (∑ k, r k • s k) x = ∑ k, (relProjectiveSpaceAn.{u} m 1).eval
      (D.kMap.toLRSHom.base ⟨x, img_le _ x hx⟩) (mem_img_iff.1 hx).2 (r k) * capKVal (s k) x := by
  classical
  have : ∀ t : Finset κ, capKVal (∑ k ∈ t, r k • s k) x = ∑ k ∈ t,
      (relProjectiveSpaceAn.{u} m 1).eval (D.kMap.toLRSHom.base ⟨x, img_le _ x hx⟩)
        (mem_img_iff.1 hx).2 (r k) * capKVal (s k) x := fun t ↦ by
    induction t using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      change holFun (kPart (0 : D.capAmb.val.obj (op O))) x = 0
      rw [kPart_zero, holFun_zero hx]
    | insert k t hk ih =>
      rw [Finset.sum_insert hk, Finset.sum_insert hk, capKVal_add _ _ hx, capKVal_smul _ _ hx, ih]
  exact this Finset.univ

lemma capWVal_mkCap (a) (ha) (g) (hc) (w : W.left) :
    capWVal (D.mkCap (O := O) a ha g hc) w = evalFun a w := by
  rw [capWVal, wPart_mkCap]

lemma capKVal_mkCap (a) (ha) (g) (hc) (x : Cn.{u} (m + 1)) :
    capKVal (D.mkCap (O := O) a ha g hc) x = holFun g x := by
  rw [capKVal, kPart_mkCap]

end

end ComplexAnalytic.Cap.AnnulusDecomposition
