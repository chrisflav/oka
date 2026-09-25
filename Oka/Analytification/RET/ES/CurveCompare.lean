/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.ES.CurveSetup
import Oka.Analytification.RET.ES.CurveStalk
import Oka.Analytification.RET.ES.CurveTensor

/-!
# Comparing the chart of `ℙ¹` with a coordinate on a curve

Let `q : V ⟶ 𝔸¹` be given by a global function of an affine scheme `V` and let `p : W ⟶ V^an`.
With `ρ₀ = q^an ∘ p : W ⟶ ℂ¹` and `ρ : W ⟶ ℙ¹_an` its composite with the chart `0`, the
functions on `W` pulled back from `Γ(ℙ¹, U₀)` along `ρ` are those pulled back from `Γ(V, 𝒪_V)`
along `p`, through `Γ(ℙ¹, U₀) ≅ Γ(𝔸¹, 𝒪) → Γ(V, 𝒪_V)`
(`ComplexAnalytic.ProjectiveLine.toSections_eq`).
-/

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry Topology

universe u

namespace ComplexAnalytic.ProjectiveLine

open AnalyticSpace projectiveSpaceAn

noncomputable section

section Congr

variable {X Y : LocallyRingedSpace.{u}} {φ ψ : X ⟶ Y}

lemma map_c_app_congr (e : φ = ψ) {U : Opens Y} {O : Opens X}
    (h₁ : O ≤ (Opens.map φ.base).obj U) (h₂ : O ≤ (Opens.map ψ.base).obj U)
    (r : Y.presheaf.obj (op U)) :
    X.presheaf.map (homOfLE h₁).op (φ.c.app (op U) r) =
      X.presheaf.map (homOfLE h₂).op (ψ.c.app (op U) r) := by
  subst e
  rfl

lemma germ_c_app_congr (e : φ = ψ) {U : Opens Y} (r : Y.presheaf.obj (op U)) (x : X)
    (h₁ : x ∈ (Opens.map φ.base).obj U) (h₂ : x ∈ (Opens.map ψ.base).obj U) :
    X.presheaf.germ _ x h₁ (φ.c.app (op U) r) = X.presheaf.germ _ x h₂ (ψ.c.app (op U) r) := by
  subst e
  rfl

lemma c_app_map_apply {X Y : LocallyRingedSpace.{u}} (F : X ⟶ Y) {O O' : Opens Y} (h : O' ≤ O)
    (y : Y.presheaf.obj (op O)) :
    F.c.app (op O') (Y.presheaf.map (homOfLE h).op y) =
      X.presheaf.map (homOfLE ((Opens.map F.base).monotone h)).op (F.c.app (op O) y) :=
  NatTrans.naturality_apply F.c (homOfLE h).op y

end Congr

/-- The scheme chart `𝔸¹ ⟶ ℙ¹` onto `U₀`. -/
abbrev chartSch : (affineSpace.{u} 1).obj.left ⟶ (projectiveSpace.{u} 1).obj.left :=
  (projectiveSpaceChart.{u} (n := 1) 0).hom.left

lemma opensRange_chartSch : chartSch.{u}.opensRange = stdU 0 :=
  ProjectiveSpace.opensRange_chart 0

lemma top_le_preimage_stdU : ⊤ ≤ chartSch.{u} ⁻¹ᵁ stdU 0 := fun x _ ↦ by
  change chartSch.base x ∈ stdU 0
  rw [← opensRange_chartSch]
  exact ⟨x, rfl⟩

/-- **The chart `0` on sections**: `Γ(ℙ¹, U₀) → Γ(𝔸¹, 𝒪)`. -/
def chartΓ : ringU₀.{u} →+* Γ((affineSpace.{u} 1).obj.left, ⊤) :=
  ((affineSpace.{u} 1).obj.left.presheaf.map (homOfLE top_le_preimage_stdU).op).hom.comp
    (chartSch.app (stdU 0)).hom

lemma bijective_chartΓ : Function.Bijective chartΓ.{u} := by
  haveI : IsIso (chartSch.{u}.app (stdU 0)) := Scheme.Hom.isIso_app _ _ (by
    rw [opensRange_chartSch])
  haveI : IsIso (homOfLE top_le_preimage_stdU.{u}) :=
    homOfLE_isIso_of_eq _ (le_antisymm top_le_preimage_stdU le_top)
  exact (ConcreteCategory.bijective_of_isIso
    ((affineSpace.{u} 1).obj.left.presheaf.map (homOfLE top_le_preimage_stdU).op)).comp
    (ConcreteCategory.bijective_of_isIso (chartSch.app (stdU 0)))

/-- `Γ(ℙ¹, U₀) ≅ Γ(𝔸¹, 𝒪)` through the chart `0`. -/
def chartΓEquiv : ringU₀.{u} ≃+* Γ((affineSpace.{u} 1).obj.left, ⊤) :=
  RingEquiv.ofBijective chartΓ bijective_chartΓ

lemma chartΓ_chartΓEquiv_symm (r : Γ((affineSpace.{u} 1).obj.left, ⊤)) :
    chartΓ (chartΓEquiv.symm r) = r :=
  chartΓEquiv.apply_symm_apply r

variable {V : SchemeLFTℂ.{u}} {s : MvPolynomial (Fin 1) (ULift.{u} ℂ) →+* Γ(V.obj.left, ⊤)}
  (hs : s.comp MvPolynomial.C = V.constMap) {W : AnalyticSpace.{u}}
  (p : W ⟶ analytification.obj V)

lemma toProjectiveLine_eq :
    toProjectiveLine (p ≫ SchemeLFTℂ.anToAffine s hs) =
      p ≫ analytification.map (SchemeLFTℂ.toAffineSpace s hs ≫ projectiveSpaceChart 0) := by
  simp only [toProjectiveLine, projectiveSpaceAnChart, SchemeLFTℂ.anToAffine, Functor.map_comp,
    Category.assoc, Iso.hom_inv_id_assoc]

lemma toProjectiveLine_comp_πP :
    (toProjectiveLine (p ≫ SchemeLFTℂ.anToAffine s hs)).toLRSHom ≫ πP =
      ((p ≫ analytification.map (SchemeLFTℂ.toAffineSpace s hs)).toLRSHom ≫
        analytificationπLRS (affineSpace.{u} 1)) ≫ chartSch.toLRSHom := by
  have e1 : (toProjectiveLine (p ≫ SchemeLFTℂ.anToAffine s hs)).toLRSHom =
      p.toLRSHom ≫ (analytification.map
        (SchemeLFTℂ.toAffineSpace s hs ≫ projectiveSpaceChart 0)).toLRSHom := by
    rw [toProjectiveLine_eq]
    rfl
  have e2 : (p ≫ analytification.map (SchemeLFTℂ.toAffineSpace s hs)).toLRSHom =
      p.toLRSHom ≫ (analytification.map (SchemeLFTℂ.toAffineSpace s hs)).toLRSHom := rfl
  rw [e1, e2, Category.assoc, analytificationπLRS_naturality, Category.assoc, Category.assoc,
    analytificationπLRS_naturality_assoc]
  rfl

/-- **Functions pulled back from `U₀ ⊆ ℙ¹` are functions pulled back from `V`.** -/
theorem toSections_eq (r : ringU₀.{u}) :
    toSections (p ≫ SchemeLFTℂ.anToAffine s hs) r =
      p.pullbackΓ (analytificationΓ V
        ((SchemeLFTℂ.toAffineSpace s hs).hom.left.appTop (chartΓ r))) := by
  have hA : toSections (p ≫ SchemeLFTℂ.anToAffine s hs) r =
      W.presheaf.map (homOfLE (preimOpen_stdU_zero (p ≫ SchemeLFTℂ.anToAffine s hs)).ge).op
        (((toProjectiveLine (p ≫ SchemeLFTℂ.anToAffine s hs)).toLRSHom ≫ πP).c.app
          (op (stdU 0)) r) := rfl
  rw [hA]
  refine (map_c_app_congr (toProjectiveLine_comp_πP hs p)
    (preimOpen_stdU_zero (p ≫ SchemeLFTℂ.anToAffine s hs)).ge
    (fun _ _ ↦ top_le_preimage_stdU trivial) r).trans ?_
  rw [analytificationΓ_naturality, ← Hom.pullbackΓ_comp]
  have hC := c_app_map_apply ((p ≫ analytification.map (SchemeLFTℂ.toAffineSpace s hs)).toLRSHom ≫
    analytificationπLRS (affineSpace.{u} 1)) top_le_preimage_stdU (chartSch.app (stdU 0) r)
  exact hC.symm


/-- The analytic chart `𝔸¹^an ⟶ ℙ¹_an`. -/
abbrev chartAn : analytification.obj (affineSpace.{u} 1) ⟶ projectiveSpaceAn.{u} 1 :=
  analytification.map (projectiveSpaceChart.{u} (n := 1) 0)

lemma chartAn_mem (c : analytification.obj (affineSpace.{u} 1)) :
    chartAn.toLRSHom.base c ∈ analytificationPreimage (projectiveSpace.{u} 1) (stdU 0) := by
  change (chartAn.toLRSHom ≫ analytificationπLRS (projectiveSpace.{u} 1)).base c ∈ stdU 0
  rw [analytificationπLRS_naturality]
  exact top_le_preimage_stdU trivial

/-- The point `chart c` of `π⁻¹ U₀ ⊆ ℙ¹_an`. -/
abbrev chartPt (c : analytification.obj (affineSpace.{u} 1)) :
    analytificationPreimage (projectiveSpace.{u} 1) (stdU 0) :=
  ⟨_, chartAn_mem c⟩


/-- The stalk isomorphism `𝒪_{ℙ¹_an, chart c} ≅ 𝒪_{𝔸¹^an, c}` of the chart. -/
def chartStalkEquiv (c : analytification.obj (affineSpace.{u} 1)) :
    (projectiveSpaceAn.{u} 1).presheaf.stalk (chartPt c).1 ≃+*
      (analytification.obj (affineSpace.{u} 1)).presheaf.stalk c :=
  haveI : IsLocalIso chartAn.{u} :=
    isLocalIso_analytification_map_of_etale (projectiveSpaceChart.{u} (n := 1) 0)
  RingEquiv.ofBijective (chartAn.toLRSHom.stalkMap c).hom
    (ConcreteCategory.bijective_of_isIso (chartAn.toLRSHom.stalkMap c))

lemma chartStalkEquiv_apply (c : analytification.obj (affineSpace.{u} 1))
    (t : (projectiveSpaceAn.{u} 1).presheaf.stalk (chartPt c).1) :
    chartStalkEquiv c t = chartAn.toLRSHom.stalkMap c t :=
  rfl

/-- **The analytic chart on stalks is compatible with the chart on sections.** -/
lemma stalkMap_chartAn_algebraMap (c : analytification.obj (affineSpace.{u} 1))
    (r : ringU₀.{u}) :
    chartAn.toLRSHom.stalkMap c (@algebraMap ringU₀.{u}
      ((projectiveSpaceAn.{u} 1).presheaf.stalk (chartPt c).1) _ _
        (analytificationStalkSectionsAlgebra (chartPt c)) r) =
      algebraMap Γ((affineSpace.{u} 1).obj.left, ⊤)
        ((analytification.obj (affineSpace.{u} 1)).presheaf.stalk c) (chartΓ r) := by
  change chartAn.toLRSHom.stalkMap c (πP.stalkMap _ ((projectiveSpace.{u} 1).obj.left.presheaf.germ
    (stdU 0) _ (chartAn_mem c) r)) = _
  erw [LocallyRingedSpace.stalkMap_germ_apply, LocallyRingedSpace.stalkMap_germ_apply]
  refine (germ_c_app_congr (analytificationπLRS_naturality (projectiveSpaceChart.{u} (n := 1) 0))
    r c _ (top_le_preimage_stdU trivial)).trans ?_
  change _ = (analytification.obj (affineSpace.{u} 1)).presheaf.germ ⊤ c trivial
    ((analytificationπLRS (affineSpace.{u} 1)).c.app (op ⊤)
      ((affineSpace.{u} 1).obj.left.presheaf.map (homOfLE top_le_preimage_stdU).op
        (chartSch.app (stdU 0) r)))
  erw [c_app_map_apply (analytificationπLRS (affineSpace.{u} 1)) top_le_preimage_stdU,
    TopCat.Presheaf.germ_res_apply]
  rfl

/-- **Stalk maps along `W ⟶ V^an ⟶ 𝔸¹^an ⟶ ℙ¹_an`**: the stalk map of `ρ` at a point over
`chart c` is the composite of the stalk maps of the chart, of `q^an` and of `p`. -/
lemma fibreStalkMap_comp_chartAn (c : analytification.obj (affineSpace.{u} 1)) (w : W)
    (hw : (toProjectiveLine (p ≫ SchemeLFTℂ.anToAffine s hs)).toLRSHom.base w = (chartPt c).1)
    (hv : (analytification.map (SchemeLFTℂ.toAffineSpace s hs)).toLRSHom.base
      (p.toLRSHom.base w) = c)
    (t : (projectiveSpaceAn.{u} 1).presheaf.stalk (chartPt c).1) :
    fibreStalkMap p (p.toLRSHom.base w) ⟨w, rfl⟩
        (fibreStalkMap (analytification.map (SchemeLFTℂ.toAffineSpace s hs)) c
          ⟨p.toLRSHom.base w, hv⟩ (chartAn.toLRSHom.stalkMap c t)) =
      fibreStalkMap (toProjectiveLine (p ≫ SchemeLFTℂ.anToAffine s hs)) (chartPt c).1
        ⟨w, hw⟩ t := by
  obtain ⟨U, hxU, r, rfl⟩ := TopCat.Presheaf.exists_germ_eq _ t
  erw [LocallyRingedSpace.stalkMap_germ_apply]
  rw [fibreStalkMap_germ, fibreStalkMap_germ, fibreStalkMap_germ]
  have e : (p ≫ analytification.map (SchemeLFTℂ.toAffineSpace s hs) ≫ chartAn).toLRSHom =
      (toProjectiveLine (p ≫ SchemeLFTℂ.anToAffine s hs)).toLRSHom := by
    rw [toProjectiveLine_eq, Functor.map_comp]
  exact germ_c_app_congr e r w _ _

/-! ### Growth of algebraic functions -/

/-- A polynomial in the coordinate grows at most polynomially. -/
lemma exists_norm_affineEval_le (c : MvPolynomial (Fin 1) (ULift.{u} ℂ)) :
    ∃ (k : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ z : AnalyticSpace.complexAffineSpace.{u} 1, 1 ≤ ‖coord z‖ →
      ‖affineEval 1 z c‖ ≤ C * ‖coord z‖ ^ k := by
  induction c using MvPolynomial.induction_on with
  | C a =>
    refine ⟨0, ‖a.down‖, norm_nonneg _, fun z _ ↦ ?_⟩
    simp only [affineEval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C, pow_zero, mul_one]
    exact le_of_eq rfl
  | add c d hc hd =>
    obtain ⟨k, C, hC0, hC⟩ := hc
    obtain ⟨k', C', hC0', hC'⟩ := hd
    refine ⟨max k k', C + C', add_nonneg hC0 hC0', fun z hz ↦ ?_⟩
    rw [map_add, add_mul]
    refine (norm_add_le _ _).trans (add_le_add ((hC z hz).trans ?_) ((hC' z hz).trans ?_))
    · exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hz (le_max_left _ _)) hC0
    · exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hz (le_max_right _ _)) hC0'
  | mul_X c i hc =>
    obtain ⟨k, C, hC0, hC⟩ := hc
    refine ⟨k + 1, C, hC0, fun z hz ↦ ?_⟩
    rw [map_mul, norm_mul, pow_succ, ← mul_assoc]
    have hX : affineEval 1 z (MvPolynomial.X i) = coord z := by
      rw [Subsingleton.elim i 0]
      simp [affineEval, coord]
    rw [hX]
    exact mul_le_mul_of_nonneg_right (hC z hz) (norm_nonneg _)

variable {V : SchemeLFTℂ.{u}} {s : MvPolynomial (Fin 1) (ULift.{u} ℂ) →+* Γ(V.obj.left, ⊤)}
  (hs : s.comp MvPolynomial.C = V.constMap) {W : AnalyticSpace.{u}}
  (p : W ⟶ analytification.obj V)

/-- **Functions on `V` have polynomial growth** on `W`, if `Γ(V, 𝒪_V)` is finite over the
coordinate ring `ℂ[z]`. -/
theorem hasPolyGrowth_pullbackΓ (hsfin : s.Finite) (a : Γ(V.obj.left, ⊤)) :
    HasPolyGrowth (p ≫ SchemeLFTℂ.anToAffine s hs) (p.pullbackΓ (analytificationΓ V a)) := by
  classical
  letI := s.toAlgebra
  haveI : Module.Finite (MvPolynomial (Fin 1) (ULift.{u} ℂ)) Γ(V.obj.left, ⊤) := hsfin
  obtain ⟨P, hPm, hP⟩ := Algebra.IsIntegral.isIntegral (R := MvPolynomial (Fin 1) (ULift.{u} ℂ)) a
  set n := P.natDegree
  choose k C hC0 hC using fun i ↦ exists_norm_affineEval_le.{u} (P.coeff i)
  set K := (Finset.range n).sup k
  set Cm := ∑ i ∈ Finset.range n, C i
  have hCm : 0 ≤ Cm := Finset.sum_nonneg fun i _ ↦ hC0 i
  refine ⟨K, max 1 (n * Cm), 1, fun w hw ↦ ?_⟩
  set v := p.toLRSHom.base w
  set z := coord ((SchemeLFTℂ.anToAffine s hs).toLRSHom.base v)
  change 1 < ‖z‖ at hw
  change ‖W.eval (U := ⊤) w trivial (p.pullbackΓ (analytificationΓ V a))‖ ≤ _ * ‖z‖ ^ K
  have hval : W.eval (U := ⊤) w trivial (p.pullbackΓ (analytificationΓ V a)) =
      evalPoint V v a :=
    eval_c_app _ p.isCLinear (U := ⊤) w trivial _
  rw [hval]
  have hcoeff : ∀ i, evalPoint V v (s (P.coeff i)) =
      affineEval 1 ((SchemeLFTℂ.anToAffine s hs).toLRSHom.base v) (P.coeff i) :=
    fun i ↦ evalPoint_eq_affineEval s hs v _
  have heq : evalPoint V v a ^ n + ∑ i ∈ Finset.range n,
      affineEval 1 ((SchemeLFTℂ.anToAffine s hs).toLRSHom.base v) (P.coeff i) *
        evalPoint V v a ^ i = 0 := by
    have h0 := congrArg (evalPoint V v) hP
    rw [map_zero, Polynomial.hom_eval₂, hPm.as_sum] at h0
    simpa [Polynomial.eval₂_finsetSum, hcoeff, RingHom.algebraMap_toAlgebra] using h0
  have hz1 : 1 ≤ ‖z‖ := hw.le
  have hA : ∀ i < n, ‖affineEval 1 ((SchemeLFTℂ.anToAffine s hs).toLRSHom.base v)
      (P.coeff i)‖ ≤ Cm * ‖z‖ ^ K := fun i hi ↦ by
    refine (hC i _ hz1).trans (mul_le_mul ?_ (pow_le_pow_right₀ hz1
      (Finset.le_sup (Finset.mem_range.2 hi))) (by positivity) hCm)
    exact Finset.single_le_sum (fun j _ ↦ hC0 j) (Finset.mem_range.2 hi)
  refine (Kummer.norm_le_of_pow_add_sum_eq_zero hA heq).trans ?_
  have hzK : 1 ≤ ‖z‖ ^ K := one_le_pow₀ hz1
  rw [max_mul_of_nonneg _ _ (by positivity), one_mul, ← mul_assoc]
  exact max_le_max hzK le_rfl

end

end ComplexAnalytic.ProjectiveLine
