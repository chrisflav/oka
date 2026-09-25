/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.ES.CapExtension.ProjSetup

/-!
# The sheaf of the cap on `ℂᵐ × ℙ¹`

Keep the notation of `Oka/Analytification/RET/ES/CapExtension/ProjSetup.lean`. The **sheaf of the
cap** `𝒞` on `P^an = ℂᵐ × ℙ¹` (`ComplexAnalytic.Cap.AnnulusDecomposition.capModule`) has as
sections over `O` the pairs `(a, g)` of a section `a` of `𝒪_W` over the preimage of `O`, bounded
near the points over `N ∖ N°`, and a section `g` of `𝒪_K` over the preimage of `O`, such that
`a` and `g` agree at the corresponding points of `W` and `K` over the annulus
(`ComplexAnalytic.Cap.AnnulusDecomposition.IsCapCompat`). It is a sheaf of submodules of the
biproduct of the bounded pushforward of `𝒪_W` and the pushforward of `𝒪_K`.
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
  (D : AnnulusDecomposition W F.G F.ρ)

variable (N N₀) in
/-- The points of `P^an` over `N ∖ N°`. -/
def removedW : Set (relProjectiveSpaceAn.{u} m 1) :=
  chart0Pt '' {x | x ∈ N ∧ x ∉ N₀}

variable (W) in
/-- The sections of `𝒪_W` over the preimages of opens of `P^an`, bounded near the points over
`N ∖ N°`. -/
abbrev capW : SheafOfModules.{u} (relProjectiveSpaceAn.{u} m 1).ringSheaf :=
  boundedPushforward (projW W) (removedW N N₀)

/-- The pushforward of `𝒪_K` to `P^an`. -/
abbrev capK : SheafOfModules.{u} (relProjectiveSpaceAn.{u} m 1).ringSheaf :=
  LocallyRingedSpace.Hom.pushUnit D.kMap.toLRSHom

/-- The ambient sheaf of the cap. -/
abbrev capAmb : SheafOfModules.{u} (relProjectiveSpaceAn.{u} m 1).ringSheaf :=
  capW (N := N) W ⊞ D.capK

variable {D}

/-- The component on `W` of a section of the ambient sheaf. -/
def wPart {O : (relProjectiveSpaceAn.{u} m 1).Opens} (s : D.capAmb.val.obj (op O)) :
    W.left.presheaf.obj (op ((Opens.map (projW W).toLRSHom.base).obj O)) :=
  ((biprod.fst : D.capAmb ⟶ capW W).val.app (op O) s).1

/-- The component on `K` of a section of the ambient sheaf. -/
def kPart {O : (relProjectiveSpaceAn.{u} m 1).Opens} (s : D.capAmb.val.obj (op O)) :
    (space D.kOpens).presheaf.obj (op ((Opens.map D.kMap.toLRSHom.base).obj O)) :=
  (biprod.snd : D.capAmb ⟶ D.capK).val.app (op O) s

lemma wPart_add {O : (relProjectiveSpaceAn.{u} m 1).Opens} (s t : D.capAmb.val.obj (op O)) :
    wPart (s + t) = wPart s + wPart t := by
  simp only [wPart, map_add]
  rfl

lemma kPart_add {O : (relProjectiveSpaceAn.{u} m 1).Opens} (s t : D.capAmb.val.obj (op O)) :
    kPart (s + t) = kPart s + kPart t := by
  simp only [kPart, map_add]
  rfl

lemma wPart_zero {O : (relProjectiveSpaceAn.{u} m 1).Opens} :
    wPart (0 : D.capAmb.val.obj (op O)) = 0 := by
  simp only [wPart, map_zero]
  rfl

lemma kPart_zero {O : (relProjectiveSpaceAn.{u} m 1).Opens} :
    kPart (0 : D.capAmb.val.obj (op O)) = 0 := by
  simp only [kPart, map_zero]
  rfl

variable (W) in
/-- Pulling back sections of `𝒪_{P^an}` along `W ⟶ P^an`. -/
def pullW (O : (relProjectiveSpaceAn.{u} m 1).Opens) :
    (relProjectiveSpaceAn.{u} m 1).presheaf.obj (op O) →+*
      W.left.presheaf.obj (op ((Opens.map (projW W).toLRSHom.base).obj O)) :=
  ((projW W).toLRSHom.c.app (op O)).hom

variable (D) in
/-- Pulling back sections of `𝒪_{P^an}` along `K ⟶ P^an`. -/
def pullK (O : (relProjectiveSpaceAn.{u} m 1).Opens) :
    (relProjectiveSpaceAn.{u} m 1).presheaf.obj (op O) →+*
      (space D.kOpens).presheaf.obj (op ((Opens.map D.kMap.toLRSHom.base).obj O)) :=
  (D.kMap.toLRSHom.c.app (op O)).hom

lemma wPart_smul {O : (relProjectiveSpaceAn.{u} m 1).Opens}
    (r : (relProjectiveSpaceAn.{u} m 1).presheaf.obj (op O)) (s : D.capAmb.val.obj (op O)) :
    wPart (r • s) = pullW W O r * wPart s := by
  simp only [wPart, map_smul]
  rfl

lemma kPart_smul {O : (relProjectiveSpaceAn.{u} m 1).Opens}
    (r : (relProjectiveSpaceAn.{u} m 1).presheaf.obj (op O)) (s : D.capAmb.val.obj (op O)) :
    kPart (r • s) = D.pullK O r * kPart s := by
  simp only [kPart, map_smul]
  rfl

lemma wPart_res {O O' : (relProjectiveSpaceAn.{u} m 1).Opens} (h : O' ≤ O)
    (s : D.capAmb.val.obj (op O)) :
    wPart (sectRes D.capAmb h s) =
      W.left.presheaf.map (homOfLE ((Opens.map (projW W).toLRSHom.base).monotone h)).op
        (wPart s) := by
  simp only [wPart, sectRes]
  erw [PresheafOfModules.naturality_apply]
  rfl

lemma kPart_res {O O' : (relProjectiveSpaceAn.{u} m 1).Opens} (h : O' ≤ O)
    (s : D.capAmb.val.obj (op O)) :
    kPart (sectRes D.capAmb h s) =
      (space D.kOpens).presheaf.map
        (homOfLE ((Opens.map D.kMap.toLRSHom.base).monotone h)).op (kPart s) := by
  simp only [kPart, sectRes]
  erw [PresheafOfModules.naturality_apply]
  rfl

/-- The point of `K` corresponding to a point of `W` over the annulus lies over the same open. -/
lemma kPt_mem_img {O : (relProjectiveSpaceAn.{u} m 1).Opens} {i : D.ι}
    {z : KummerAnnulus.base F.G F.ρ⁻¹ F.ρ (D.deg i)}
    (hz : D.toFun ⟨i, z⟩ ∈ (Opens.map (projW W).toLRSHom.base).obj O) :
    D.kPt i (invCoord z.1) ∈ img ((Opens.map D.kMap.toLRSHom.base).obj O) :=
  mem_img_iff.2 ⟨D.mem_kOpens.2 ⟨i, D.kPt_invCoord_mem z.2⟩, by
    change D.kMap.toLRSHom.base _ ∈ O
    rw [← D.projW_toFun i z]
    exact hz⟩

variable (D) in
/-- **The compatibility of the two components** of a section of the ambient sheaf: at the
corresponding points of `W` and `K` over the annulus, the values agree. -/
def IsCapCompat {O : (relProjectiveSpaceAn.{u} m 1).Opens} (s : D.capAmb.val.obj (op O)) : Prop :=
  ∀ (i : D.ι) (z : KummerAnnulus.base F.G F.ρ⁻¹ F.ρ (D.deg i)),
    D.toFun ⟨i, z⟩ ∈ (Opens.map (projW W).toLRSHom.base).obj O →
      evalFun (wPart s) (D.toFun ⟨i, z⟩) = holFun (kPart s) (D.kPt i (invCoord z.1))

lemma evalFun_c_app_projW {O : (relProjectiveSpaceAn.{u} m 1).Opens}
    (r : (relProjectiveSpaceAn.{u} m 1).presheaf.obj (op O)) {w : W.left}
    (hw : w ∈ (Opens.map (projW W).toLRSHom.base).obj O) :
    evalFun (pullW W O r) w =
      (relProjectiveSpaceAn.{u} m 1).eval ((projW W).toLRSHom.base w) hw r := by
  rw [evalFun_of_mem _ hw]
  exact eval_c_app (projW W).toLRSHom (projW W).isCLinear w hw r

lemma holFun_c_app_kMap {O : (relProjectiveSpaceAn.{u} m 1).Opens}
    (r : (relProjectiveSpaceAn.{u} m 1).presheaf.obj (op O)) {x : Cn.{u} (m + 1)}
    (hx : x ∈ img ((Opens.map D.kMap.toLRSHom.base).obj O)) :
    holFun (D.pullK O r) x = (relProjectiveSpaceAn.{u} m 1).eval
      (D.kMap.toLRSHom.base ⟨x, img_le _ x hx⟩) (mem_img_iff.1 hx).2 r := by
  rw [holFun_eq_eval _ hx]
  exact eval_c_app D.kMap.toLRSHom D.kMap.isCLinear _ _ r

variable (D) in
/-- **The sheaf of the cap** as a sheaf of submodules of the ambient sheaf. -/
def capSubmodule : D.capAmb.Submodule where
  obj O :=
    { carrier := {s | D.IsCapCompat (O := O.unop) s}
      add_mem' := fun {s t} hs ht i z hz ↦ by
        change evalFun (wPart (s + t)) _ = holFun (kPart (s + t)) _
        rw [wPart_add, kPart_add, evalFun_add W _ _ hz, holFun_add _ _ (kPt_mem_img hz),
          hs i z hz, ht i z hz]
      zero_mem' := fun i z hz ↦ by
        change evalFun (wPart (0 : D.capAmb.val.obj O)) _ =
          holFun (kPart (0 : D.capAmb.val.obj O)) _
        rw [wPart_zero, kPart_zero, holFun_zero (kPt_mem_img hz), evalFun_of_mem _ hz, map_zero]
      smul_mem' := fun r s hs i z hz ↦ by
        change evalFun (wPart (r • s)) _ = holFun (kPart (r • s)) _
        have e1 : wPart (r • s) = pullW W O.unop r * wPart s := wPart_smul (O := O.unop) r s
        have e2 : kPart (r • s) = D.pullK O.unop r * kPart s := kPart_smul (O := O.unop) r s
        rw [e1, e2, evalFun_mul W _ _ hz, holFun_mul _ _ (kPt_mem_img hz),
          hs i z hz, evalFun_c_app_projW r hz, holFun_c_app_kMap r (kPt_mem_img hz)]
        congr 1
        exact eval_congr_point (D.projW_toFun i z) _ _ r }
  map {O O'} f s hs i z hz := by
    change evalFun (wPart (sectRes D.capAmb (leOfHom f.unop) s)) _ =
      holFun (kPart (sectRes D.capAmb (leOfHom f.unop) s)) _
    rw [wPart_res, kPart_res, evalFun_map W _ _ hz, holFun_map _ _ (kPt_mem_img hz)]
    exact hs i z ((Opens.map (projW W).toLRSHom.base).monotone (leOfHom f.unop) hz)
  isSheaf {O} s hs i z hz := by
    obtain ⟨O', f, hO', hzO'⟩ := hs ((projW W).toLRSHom.base (D.toFun ⟨i, z⟩)) hz
    have := hO' i z hzO'
    change evalFun (wPart (sectRes D.capAmb (leOfHom f) s)) _ =
      holFun (kPart (sectRes D.capAmb (leOfHom f) s)) _ at this
    rwa [wPart_res, kPart_res, evalFun_map W _ _ hzO', holFun_map _ _ (kPt_mem_img hzO')] at this

variable (D) in
/-- **The sheaf of the cap** `𝒞` on `P^an`. -/
abbrev capModule : SheafOfModules.{u} (relProjectiveSpaceAn.{u} m 1).ringSheaf :=
  D.capSubmodule.toSheafOfModules

end

end ComplexAnalytic.Cap.AnnulusDecomposition

namespace SheafOfModules

variable {Y : AlgebraicGeometry.LocallyRingedSpace.{u}} {A B : SheafOfModules.{u} Y.ringSheaf}
  {X : (TopologicalSpace.Opens Y.toPresheafedSpace)ᵒᵖ}

lemma biprod_fst_inl_apply (a : A.val.obj X) :
    (biprod.fst : A ⊞ B ⟶ A).val.app X ((biprod.inl : A ⟶ A ⊞ B).val.app X a) = a := by
  change (biprod.inl ≫ biprod.fst : A ⟶ A).val.app X a = a
  rw [biprod.inl_fst]
  rfl

lemma biprod_snd_inl_apply (a : A.val.obj X) :
    (biprod.snd : A ⊞ B ⟶ B).val.app X ((biprod.inl : A ⟶ A ⊞ B).val.app X a) = 0 := by
  change (biprod.inl ≫ biprod.snd : A ⟶ B).val.app X a = 0
  rw [biprod.inl_snd]
  rfl

lemma biprod_fst_inr_apply (b : B.val.obj X) :
    (biprod.fst : A ⊞ B ⟶ A).val.app X ((biprod.inr : B ⟶ A ⊞ B).val.app X b) = 0 := by
  change (biprod.inr ≫ biprod.fst : B ⟶ A).val.app X b = 0
  rw [biprod.inr_fst]
  rfl

lemma biprod_snd_inr_apply (b : B.val.obj X) :
    (biprod.snd : A ⊞ B ⟶ B).val.app X ((biprod.inr : B ⟶ A ⊞ B).val.app X b) = b := by
  change (biprod.inr ≫ biprod.snd : B ⟶ B).val.app X b = b
  rw [biprod.inr_snd]
  rfl

lemma biprod_eq_inl_add_inr (x : (A ⊞ B).val.obj X) :
    x = (biprod.inl : A ⟶ A ⊞ B).val.app X ((biprod.fst : A ⊞ B ⟶ A).val.app X x) +
      (biprod.inr : B ⟶ A ⊞ B).val.app X ((biprod.snd : A ⊞ B ⟶ B).val.app X x) := by
  have := congrArg (fun f : A ⊞ B ⟶ A ⊞ B ↦ f.val.app X x) (biprod.total (X := A) (Y := B))
  exact this.symm

lemma biprod_ext {x y : (A ⊞ B).val.obj X}
    (h₁ : (biprod.fst : A ⊞ B ⟶ A).val.app X x = (biprod.fst : A ⊞ B ⟶ A).val.app X y)
    (h₂ : (biprod.snd : A ⊞ B ⟶ B).val.app X x = (biprod.snd : A ⊞ B ⟶ B).val.app X y) :
    x = y := by
  rw [biprod_eq_inl_add_inr x, biprod_eq_inl_add_inr y, h₁, h₂]

end SheafOfModules
