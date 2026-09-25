/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.ES.SmoothStalk
import Oka.Analytification.RET.ES.CurveCompare

/-!
# Comparing the chart of `ℙⁿ` with a finite map to `𝔸ⁿ`

Let `q : V ⟶ 𝔸ⁿ` be given by `n` global functions of an affine scheme `V` and let
`p : W ⟶ V^an`. With `ρ₀ = q^an ∘ p : W ⟶ ℂⁿ` and `ρ : W ⟶ ℙⁿ_an` its composite with the chart `0`,
the functions on `W` pulled back from `Γ(ℙⁿ, U₀)` along `ρ` are those pulled back from
`Γ(V, 𝒪_V)` along `p`, through `Γ(ℙⁿ, U₀) ≅ Γ(𝔸ⁿ, 𝒪) → Γ(V, 𝒪_V)`
(`ComplexAnalytic.ProjectiveCompletion.toSections_eq`). If `q` is finite, the functions pulled
back from `V` have polynomial growth
(`ComplexAnalytic.ProjectiveCompletion.hasPolyGrowth_pullbackΓ`).
-/

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry Topology

universe u

namespace ComplexAnalytic.ProjectiveCompletion

open AnalyticSpace projectiveSpaceAn

noncomputable section

variable {n : ℕ}

/-- The scheme chart `𝔸ⁿ ⟶ ℙⁿ` onto `U₀`. -/
abbrev chartSch (n : ℕ) : (affineSpace.{u} n).obj.left ⟶ (projectiveSpace.{u} n).obj.left :=
  (projectiveSpaceChart.{u} (n := n) 0).hom.left

lemma opensRange_chartSch (n : ℕ) : (chartSch.{u} n).opensRange = stdU 0 :=
  ProjectiveSpace.opensRange_chart 0

lemma top_le_preimage_stdU (n : ℕ) : ⊤ ≤ (chartSch.{u} n) ⁻¹ᵁ stdU 0 := fun x _ ↦ by
  change (chartSch n).base x ∈ stdU 0
  rw [← (opensRange_chartSch n)]
  exact ⟨x, rfl⟩

/-- **The chart `0` on sections**: `Γ(ℙⁿ, U₀) → Γ(𝔸ⁿ, 𝒪)`. -/
def chartΓ (n : ℕ) : (ringU₀.{u} n) →+* Γ((affineSpace.{u} n).obj.left, ⊤) :=
  ((affineSpace.{u} n).obj.left.presheaf.map (homOfLE (top_le_preimage_stdU n)).op).hom.comp
    ((chartSch n).app (stdU 0)).hom

lemma bijective_chartΓ (n : ℕ) : Function.Bijective (chartΓ.{u} n) := by
  haveI : IsIso ((chartSch.{u} n).app (stdU 0)) := Scheme.Hom.isIso_app _ _ (by
    rw [(opensRange_chartSch n)])
  haveI : IsIso (homOfLE (top_le_preimage_stdU.{u} n)) :=
    homOfLE_isIso_of_eq _ (le_antisymm (top_le_preimage_stdU n) le_top)
  exact (ConcreteCategory.bijective_of_isIso
    ((affineSpace.{u} n).obj.left.presheaf.map (homOfLE (top_le_preimage_stdU n)).op)).comp
    (ConcreteCategory.bijective_of_isIso ((chartSch n).app (stdU 0)))

/-- `Γ(ℙⁿ, U₀) ≅ Γ(𝔸ⁿ, 𝒪)` through the chart `0`. -/
def chartΓEquiv (n : ℕ) : (ringU₀.{u} n) ≃+* Γ((affineSpace.{u} n).obj.left, ⊤) :=
  RingEquiv.ofBijective (chartΓ n) (bijective_chartΓ n)

lemma chartΓ_chartΓEquiv_symm (r : Γ((affineSpace.{u} n).obj.left, ⊤)) :
    chartΓ n ((chartΓEquiv n).symm r) = r :=
  (chartΓEquiv n).apply_symm_apply r

variable {V : SchemeLFTℂ.{u}} {s : MvPolynomial (Fin n) (ULift.{u} ℂ) →+* Γ(V.obj.left, ⊤)}
  (hs : s.comp MvPolynomial.C = V.constMap) {W : AnalyticSpace.{u}}
  (p : W ⟶ analytification.obj V)

lemma toProj_eq :
    toProj (p ≫ SchemeLFTℂ.anToAffine s hs) =
      p ≫ analytification.map (SchemeLFTℂ.toAffineSpace s hs ≫ projectiveSpaceChart 0) := by
  simp only [toProj, projectiveSpaceAnChart, SchemeLFTℂ.anToAffine, Functor.map_comp,
    Category.assoc, Iso.hom_inv_id_assoc]

lemma toProj_comp_πP :
    (toProj (p ≫ SchemeLFTℂ.anToAffine s hs)).toLRSHom ≫ πP =
      ((p ≫ analytification.map (SchemeLFTℂ.toAffineSpace s hs)).toLRSHom ≫
        analytificationπLRS (affineSpace.{u} n)) ≫ (chartSch n).toLRSHom := by
  have e1 : (toProj (p ≫ SchemeLFTℂ.anToAffine s hs)).toLRSHom =
      p.toLRSHom ≫ (analytification.map
        (SchemeLFTℂ.toAffineSpace s hs ≫ projectiveSpaceChart 0)).toLRSHom := by
    rw [toProj_eq]
    rfl
  have e2 : (p ≫ analytification.map (SchemeLFTℂ.toAffineSpace s hs)).toLRSHom =
      p.toLRSHom ≫ (analytification.map (SchemeLFTℂ.toAffineSpace s hs)).toLRSHom := rfl
  rw [e1, e2, Category.assoc, analytificationπLRS_naturality, Category.assoc, Category.assoc,
    analytificationπLRS_naturality_assoc]
  rfl

/-- **Functions pulled back from `U₀ ⊆ ℙⁿ` are functions pulled back from `V`.** -/
theorem toSections_eq (r : (ringU₀.{u} n)) :
    toSections (p ≫ SchemeLFTℂ.anToAffine s hs) r =
      p.pullbackΓ (analytificationΓ V
        ((SchemeLFTℂ.toAffineSpace s hs).hom.left.appTop (chartΓ n r))) := by
  have hA : toSections (p ≫ SchemeLFTℂ.anToAffine s hs) r =
      W.presheaf.map (homOfLE (preimOpen_stdU_zero (p ≫ SchemeLFTℂ.anToAffine s hs)).ge).op
        (((toProj (p ≫ SchemeLFTℂ.anToAffine s hs)).toLRSHom ≫ πP).c.app
          (op (stdU 0)) r) := rfl
  rw [hA]
  refine (ProjectiveLine.map_c_app_congr (toProj_comp_πP hs p)
    (preimOpen_stdU_zero (p ≫ SchemeLFTℂ.anToAffine s hs)).ge
    (fun _ _ ↦ (top_le_preimage_stdU n) trivial) r).trans ?_
  rw [analytificationΓ_naturality, ← Hom.pullbackΓ_comp]
  have hC := ProjectiveLine.c_app_map_apply
    ((p ≫ analytification.map (SchemeLFTℂ.toAffineSpace s hs)).toLRSHom ≫
      analytificationπLRS (affineSpace.{u} n)) (top_le_preimage_stdU n)
    ((chartSch n).app (stdU 0) r)
  exact hC.symm


/-- The analytic chart `𝔸ⁿ^an ⟶ ℙⁿ_an`. -/
abbrev chartAn : analytification.obj (affineSpace.{u} n) ⟶ projectiveSpaceAn.{u} n :=
  analytification.map (projectiveSpaceChart.{u} (n := n) 0)

lemma chartAn_mem (c : analytification.obj (affineSpace.{u} n)) :
    chartAn.toLRSHom.base c ∈ analytificationPreimage (projectiveSpace.{u} n) (stdU 0) := by
  change (chartAn.toLRSHom ≫ analytificationπLRS (projectiveSpace.{u} n)).base c ∈ stdU 0
  rw [analytificationπLRS_naturality]
  exact (top_le_preimage_stdU n) trivial

/-- The point `chart c` of `π⁻¹ U₀ ⊆ ℙⁿ_an`. -/
abbrev chartPt (c : analytification.obj (affineSpace.{u} n)) :
    analytificationPreimage (projectiveSpace.{u} n) (stdU 0) :=
  ⟨_, chartAn_mem c⟩


/-- The stalk isomorphism `𝒪_{ℙⁿ_an, chart c} ≅ 𝒪_{𝔸ⁿ^an, c}` of the chart. -/
def chartStalkEquiv (c : analytification.obj (affineSpace.{u} n)) :
    (projectiveSpaceAn.{u} n).presheaf.stalk (chartPt c).1 ≃+*
      (analytification.obj (affineSpace.{u} n)).presheaf.stalk c :=
  haveI : IsLocalIso chartAn.{u} :=
    isLocalIso_analytification_map_of_etale (projectiveSpaceChart.{u} (n := n) 0)
  RingEquiv.ofBijective (chartAn.toLRSHom.stalkMap c).hom
    (ConcreteCategory.bijective_of_isIso (chartAn.toLRSHom.stalkMap c))

lemma chartStalkEquiv_apply (c : analytification.obj (affineSpace.{u} n))
    (t : (projectiveSpaceAn.{u} n).presheaf.stalk (chartPt c).1) :
    chartStalkEquiv c t = chartAn.toLRSHom.stalkMap c t :=
  rfl

/-- **The analytic chart on stalks is compatible with the chart on sections.** -/
lemma stalkMap_chartAn_algebraMap (c : analytification.obj (affineSpace.{u} n))
    (r : (ringU₀.{u} n)) :
    chartAn.toLRSHom.stalkMap c (@algebraMap (ringU₀.{u} n)
      ((projectiveSpaceAn.{u} n).presheaf.stalk (chartPt c).1) _ _
        (analytificationStalkSectionsAlgebra (chartPt c)) r) =
      algebraMap Γ((affineSpace.{u} n).obj.left, ⊤)
        ((analytification.obj (affineSpace.{u} n)).presheaf.stalk c) (chartΓ n r) := by
  change chartAn.toLRSHom.stalkMap c (πP.stalkMap _ ((projectiveSpace.{u} n).obj.left.presheaf.germ
    (stdU 0) _ (chartAn_mem c) r)) = _
  erw [LocallyRingedSpace.stalkMap_germ_apply, LocallyRingedSpace.stalkMap_germ_apply]
  refine (ProjectiveLine.germ_c_app_congr
    (analytificationπLRS_naturality (projectiveSpaceChart.{u} (n := n) 0)) r c _
    (top_le_preimage_stdU n trivial)).trans ?_
  change _ = (analytification.obj (affineSpace.{u} n)).presheaf.germ ⊤ c trivial
    ((analytificationπLRS (affineSpace.{u} n)).c.app (op ⊤)
      ((affineSpace.{u} n).obj.left.presheaf.map (homOfLE (top_le_preimage_stdU n)).op
        ((chartSch n).app (stdU 0) r)))
  erw [ProjectiveLine.c_app_map_apply (analytificationπLRS (affineSpace.{u} n))
      (top_le_preimage_stdU n),
    TopCat.Presheaf.germ_res_apply]
  rfl

/-- **Stalk maps along `W ⟶ V^an ⟶ 𝔸ⁿ^an ⟶ ℙⁿ_an`**: the stalk map of `ρ` at a point over
`chart c` is the composite of the stalk maps of the chart, of `q^an` and of `p`. -/
lemma fibreStalkMap_comp_chartAn (c : analytification.obj (affineSpace.{u} n)) (w : W)
    (hw : (toProj (p ≫ SchemeLFTℂ.anToAffine s hs)).toLRSHom.base w = (chartPt c).1)
    (hv : (analytification.map (SchemeLFTℂ.toAffineSpace s hs)).toLRSHom.base
      (p.toLRSHom.base w) = c)
    (t : (projectiveSpaceAn.{u} n).presheaf.stalk (chartPt c).1) :
    fibreStalkMap p (p.toLRSHom.base w) ⟨w, rfl⟩
        (fibreStalkMap (analytification.map (SchemeLFTℂ.toAffineSpace s hs)) c
          ⟨p.toLRSHom.base w, hv⟩ (chartAn.toLRSHom.stalkMap c t)) =
      fibreStalkMap (toProj (p ≫ SchemeLFTℂ.anToAffine s hs)) (chartPt c).1
        ⟨w, hw⟩ t := by
  obtain ⟨U, hxU, r, rfl⟩ := TopCat.Presheaf.exists_germ_eq _ t
  erw [LocallyRingedSpace.stalkMap_germ_apply]
  rw [fibreStalkMap_germ, fibreStalkMap_germ, fibreStalkMap_germ]
  have e : (p ≫ analytification.map (SchemeLFTℂ.toAffineSpace s hs) ≫ chartAn).toLRSHom =
      (toProj (p ≫ SchemeLFTℂ.anToAffine s hs)).toLRSHom := by
    rw [toProj_eq, Functor.map_comp]
  exact ProjectiveLine.germ_c_app_congr e r w _ _

/-! ### Growth of algebraic functions -/

/-- A polynomial in the coordinates grows at most polynomially. -/
lemma exists_norm_affineEval_le (c : MvPolynomial (Fin n) (ULift.{u} ℂ)) :
    ∃ (k : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ z : AnalyticSpace.complexAffineSpace.{u} n, 1 ≤ vnorm z →
      ‖affineEval n z c‖ ≤ C * vnorm z ^ k := by
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
    have hX : affineEval n z (MvPolynomial.X i) = toFin z i := by
      simp [affineEval, toFin]
    rw [hX]
    exact mul_le_mul (hC z hz) (norm_apply_le_vnorm z i) (norm_nonneg _)
      (mul_nonneg hC0 (pow_nonneg (vnorm_nonneg _) _))

variable {V : SchemeLFTℂ.{u}} {s : MvPolynomial (Fin n) (ULift.{u} ℂ) →+* Γ(V.obj.left, ⊤)}
  (hs : s.comp MvPolynomial.C = V.constMap) {W : AnalyticSpace.{u}}
  (p : W ⟶ analytification.obj V)

/-- **Functions on `V` have polynomial growth** on `W`, if `Γ(V, 𝒪_V)` is finite over the
coordinate ring `ℂ[z₁, …, zₙ]`. -/
theorem hasPolyGrowth_pullbackΓ (hsfin : s.Finite) (a : Γ(V.obj.left, ⊤)) :
    HasPolyGrowth (p ≫ SchemeLFTℂ.anToAffine s hs) (p.pullbackΓ (analytificationΓ V a)) := by
  classical
  letI := s.toAlgebra
  haveI : Module.Finite (MvPolynomial (Fin n) (ULift.{u} ℂ)) Γ(V.obj.left, ⊤) := hsfin
  obtain ⟨P, hPm, hP⟩ := Algebra.IsIntegral.isIntegral (R := MvPolynomial (Fin n) (ULift.{u} ℂ)) a
  set d := P.natDegree
  choose k C hC0 hC using fun i ↦ exists_norm_affineEval_le.{u} (n := n) (P.coeff i)
  set K := (Finset.range d).sup k
  set Cm := ∑ i ∈ Finset.range d, C i
  have hCm : 0 ≤ Cm := Finset.sum_nonneg fun i _ ↦ hC0 i
  refine ⟨K, max 1 (d * Cm), 1, fun w hw ↦ ?_⟩
  set v := p.toLRSHom.base w
  set z := vnorm ((SchemeLFTℂ.anToAffine s hs).toLRSHom.base v)
  change 1 < z at hw
  change ‖W.eval (U := ⊤) w trivial (p.pullbackΓ (analytificationΓ V a))‖ ≤ _ * z ^ K
  have hval : W.eval (U := ⊤) w trivial (p.pullbackΓ (analytificationΓ V a)) =
      evalPoint V v a :=
    eval_c_app _ p.isCLinear (U := ⊤) w trivial _
  rw [hval]
  have hcoeff : ∀ i, evalPoint V v (s (P.coeff i)) =
      affineEval n ((SchemeLFTℂ.anToAffine s hs).toLRSHom.base v) (P.coeff i) :=
    fun i ↦ evalPoint_eq_affineEval s hs v _
  have heq : evalPoint V v a ^ d + ∑ i ∈ Finset.range d,
      affineEval n ((SchemeLFTℂ.anToAffine s hs).toLRSHom.base v) (P.coeff i) *
        evalPoint V v a ^ i = 0 := by
    have h0 := congrArg (evalPoint V v) hP
    rw [map_zero, Polynomial.hom_eval₂, hPm.as_sum] at h0
    simpa [Polynomial.eval₂_finsetSum, hcoeff, RingHom.algebraMap_toAlgebra] using h0
  have hz1 : 1 ≤ z := hw.le
  have hA : ∀ i < d, ‖affineEval n ((SchemeLFTℂ.anToAffine s hs).toLRSHom.base v)
      (P.coeff i)‖ ≤ Cm * z ^ K := fun i hi ↦ by
    refine (hC i _ hz1).trans (mul_le_mul ?_ (pow_le_pow_right₀ hz1
      (Finset.le_sup (Finset.mem_range.2 hi))) (pow_nonneg (vnorm_nonneg _) _) hCm)
    exact Finset.single_le_sum (fun j _ ↦ hC0 j) (Finset.mem_range.2 hi)
  refine (Kummer.norm_le_of_pow_add_sum_eq_zero hA heq).trans ?_
  have hzK : 1 ≤ z ^ K := one_le_pow₀ hz1
  rw [max_mul_of_nonneg _ _ (pow_nonneg (vnorm_nonneg _) _), one_mul, ← mul_assoc]
  exact max_le_max hzK le_rfl

end

end ComplexAnalytic.ProjectiveCompletion
