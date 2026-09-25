/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.ES.Kummer
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Oka.AnalyticSpace.StalkLocalInverse

/-!
# Kummer covers of `B × Δ*` inside `ℂ^{m+1}`

Write the points of `ℂ^{m+1}` as `(t, b)` with `t` the coordinate `0` and `b ∈ ℂ^m` the others,
let `B ⊆ ℂ^m` be open and let `S° ⊆ ℂ^{m+1}` be the open subspace `{b ∈ B, 0 < ‖t‖ < 1}`. For
`k > 0` the polynomial map `(t, b) ↦ (tᵏ, b)` restricts to a finite étale endomorphism of `S°`,
the Kummer cover `ComplexAnalytic.KummerModel.cover B k`. Every finite étale cover of `S°` with
Hausdorff total space is isomorphic to a finite disjoint union of these, for `B` convex
(`ComplexAnalytic.KummerModel.exists_iso_sigma_cover`).

## Main definitions

- `ComplexAnalytic.KummerModel.splitEquiv m`: `ℂ^{m+1} ≃ ℂ^m × ℂ`, `(t, b) ↦ (b, t)`.
- `ComplexAnalytic.KummerModel.punctured B`: the open subspace `S°` of `ℂ^{m+1}`.
- `ComplexAnalytic.KummerModel.kummerHom B k`: the morphism `S° ⟶ S°`, `(t, b) ↦ (tᵏ, b)`.
- `ComplexAnalytic.KummerModel.cover B k`: the Kummer cover of degree `k`, as a finite étale cover
  of `S°`.

## Main results

- `ComplexAnalytic.KummerModel.isLocalIso_kummerHom`,
  `ComplexAnalytic.KummerModel.isFinite_kummerHom`: the Kummer map is finite étale.
- `ComplexAnalytic.KummerModel.exists_iso_sigma_cover`: a finite étale cover of `S°` with
  Hausdorff total space is a finite disjoint union of Kummer covers.
-/

open CategoryTheory Opposite AlgebraicGeometry Topology Filter

universe u

namespace ComplexAnalytic.KummerModel

open AnalyticSpace

noncomputable section

variable {m : ℕ}

/-- The coordinate `t` of `ℂ^{m+1}`. -/
abbrev zero : ULift.{u} (Fin (m + 1)) := ⟨0⟩

/-- The splitting `ℂ^{m+1} ≃ ℂ^m × ℂ`, `(t, b) ↦ (b, t)`. -/
def splitEquiv (m : ℕ) : (ULift.{u} (Fin (m + 1)) → ℂ) ≃ₜ (ULift.{u} (Fin m) → ℂ) × ℂ where
  toFun x := (fun i ↦ x ⟨i.down.succ⟩, x zero)
  invFun p j := Fin.cases p.2 (fun i ↦ p.1 ⟨i⟩) j.down
  left_inv x := by
    funext ⟨j⟩
    cases j using Fin.cases <;> rfl
  right_inv p := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by
    refine continuous_pi fun ⟨j⟩ ↦ ?_
    cases j using Fin.cases
    · exact continuous_snd
    · exact (continuous_apply (⟨_⟩ : ULift.{u} (Fin m))).comp continuous_fst

@[simp]
lemma splitEquiv_apply (x : ULift.{u} (Fin (m + 1)) → ℂ) :
    splitEquiv m x = (fun i ↦ x ⟨i.down.succ⟩, x zero) :=
  rfl

variable (B : Set (ULift.{u} (Fin m) → ℂ))

/-- The open subset `{b ∈ B, 0 < ‖t‖ < 1}` of `ℂ^{m+1}`. -/
def puncturedOpens (hB : IsOpen B) : (AnalyticSpace.complexAffineSpace.{u} (m + 1)).Opens :=
  ⟨splitEquiv m ⁻¹' Kummer.base B, (Kummer.isOpen_base hB).preimage (splitEquiv m).continuous⟩

variable {B}

/-- The open subspace `S° = {b ∈ B, 0 < ‖t‖ < 1}` of `ℂ^{m+1}`. -/
abbrev punctured (hB : IsOpen B) : AnalyticSpace.{u} :=
  (AnalyticSpace.complexAffineSpace.{u} (m + 1)).restrict (puncturedOpens B hB)

/-- The identification of `S°` with `B × Δ*`. -/
def homeomorph (hB : IsOpen B) : (punctured hB : Type u) ≃ₜ Kummer.base B :=
  (splitEquiv m).sets rfl

@[simp]
lemma homeomorph_apply (hB : IsOpen B) (x : punctured hB) :
    (homeomorph hB x : (ULift.{u} (Fin m) → ℂ) × ℂ) = splitEquiv m x.1 :=
  rfl

/-- The polynomial map `(t, b) ↦ (tᵏ, b)` of `ℂ^{m+1}`, as a tuple of entire functions. -/
def kummerPoly (k : ℕ+) :
    ULift.{u} (Fin (m + 1)) →
      OkaRing (⊤ : TopologicalSpace.Opens (ULift.{u} (Fin (m + 1)) → ℂ)) :=
  fun j ↦ if j = zero then coord j ^ (k : ℕ) else coord j

lemma okaMapFun_kummerPoly (k : ℕ+) (x : ULift.{u} (Fin (m + 1)) → ℂ) :
    okaMapFun (kummerPoly k) x = Function.update x zero (x zero ^ (k : ℕ)) := by
  funext j
  rw [okaMapFun_apply, kummerPoly]
  by_cases hj : j = zero
  · subst hj
    rw [if_pos rfl, map_pow, evalHom_coord, Function.update_self]
  · rw [if_neg hj, evalHom_coord, Function.update_of_ne hj]

lemma splitEquiv_update (k : ℕ+) (x : ULift.{u} (Fin (m + 1)) → ℂ) :
    splitEquiv m (Function.update x zero (x zero ^ (k : ℕ))) =
      ((splitEquiv m x).1, (splitEquiv m x).2 ^ (k : ℕ)) := by
  refine Prod.ext (funext fun i ↦ ?_) ?_
  · exact Function.update_of_ne (fun h ↦ Fin.succ_ne_zero _ (congrArg ULift.down h))
      (x zero ^ (k : ℕ)) x
  · exact Function.update_self zero (x zero ^ (k : ℕ)) x

/-! ### A local analytic inverse -/

/-- The inverse of `(t, b) ↦ (tᵏ, b)` near a point with `t = c ≠ 0`:
`(s, b) ↦ (c · exp(log(s / cᵏ) / k), b)`. -/
def localInverse (k : ℕ+) (c : ℂ) (w : ULift.{u} (Fin (m + 1)) → ℂ) :
    ULift.{u} (Fin (m + 1)) → ℂ :=
  fun j ↦ if j = zero then c * Complex.exp (Complex.log (w zero / c ^ (k : ℕ)) / k) else w j

lemma localInverse_zero (k : ℕ+) (c : ℂ) (w : ULift.{u} (Fin (m + 1)) → ℂ) :
    localInverse k c w zero = c * Complex.exp (Complex.log (w zero / c ^ (k : ℕ)) / k) :=
  if_pos rfl

lemma localInverse_of_ne (k : ℕ+) (c : ℂ) (w : ULift.{u} (Fin (m + 1)) → ℂ)
    {j : ULift.{u} (Fin (m + 1))} (hj : j ≠ zero) : localInverse k c w j = w j :=
  if_neg hj

lemma analyticAt_localInverse (k : ℕ+) (c : ℂ) {w : ULift.{u} (Fin (m + 1)) → ℂ}
    (hw : w zero / c ^ (k : ℕ) ∈ Complex.slitPlane) :
    AnalyticAt ℂ (localInverse k c) w := by
  refine AnalyticAt.pi fun j ↦ ?_
  by_cases hj : j = zero
  · simp only [localInverse, if_pos hj]
    have h₀ : AnalyticAt ℂ (fun w : ULift.{u} (Fin (m + 1)) → ℂ ↦ w zero) w :=
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ULift.{u} (Fin (m + 1)) ↦ ℂ)
        zero).analyticAt w
    exact analyticAt_const.mul
      (AnalyticAt.div_const (AnalyticAt.clog (h₀.div_const (c := c ^ (k : ℕ))) hw)).cexp'
  · simp only [localInverse, if_neg hj]
    exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ULift.{u} (Fin (m + 1)) ↦ ℂ)
      j).analyticAt w

lemma okaMapFun_localInverse (k : ℕ+) {c : ℂ} (hc : c ≠ 0) {w : ULift.{u} (Fin (m + 1)) → ℂ}
    (hw : w zero / c ^ (k : ℕ) ∈ Complex.slitPlane) :
    okaMapFun (kummerPoly k) (localInverse k c w) = w := by
  rw [okaMapFun_kummerPoly]
  funext j
  by_cases hj : j = zero
  · subst hj
    rw [Function.update_self, localInverse_zero, mul_pow, ← Complex.exp_nat_mul,
      mul_div_cancel₀ _ (by exact_mod_cast k.ne_zero),
      Complex.exp_log (Complex.slitPlane_ne_zero hw), mul_div_cancel₀ _ (pow_ne_zero _ hc)]
  · rw [Function.update_of_ne hj, localInverse_of_ne k c _ hj]

lemma localInverse_okaMapFun (k : ℕ+) {c : ℂ} (hc : c ≠ 0) {p : ULift.{u} (Fin (m + 1)) → ℂ}
    (hp : p zero / c ∈ Complex.slitPlane)
    (harg : |Complex.arg (p zero / c)| < Real.pi / k) :
    localInverse k c (okaMapFun (kummerPoly k) p) = p := by
  rw [okaMapFun_kummerPoly]
  funext j
  by_cases hj : j = zero
  · subst hj
    rw [localInverse_zero, Function.update_self]
    set q := p zero / c
    have hq0 : q ≠ 0 := Complex.slitPlane_ne_zero hp
    have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast k.ne_zero
    have hkpos : (0 : ℝ) < k := by exact_mod_cast k.pos
    have hpow : p zero ^ (k : ℕ) / c ^ (k : ℕ) = Complex.exp (k * Complex.log q) := by
      rw [← div_pow, Complex.exp_nat_mul, Complex.exp_log hq0]
    have him : (k * Complex.log q).im = k * Complex.arg q := by
      simp [Complex.log_im]
    have hlog : Complex.log (Complex.exp (k * Complex.log q)) = k * Complex.log q := by
      refine Complex.log_exp ?_ ?_
      · rw [him]
        have := (abs_lt.1 harg).1
        rw [← neg_div, div_lt_iff₀ hkpos] at this
        linarith [mul_comm (k : ℝ) q.arg]
      · rw [him]
        have := (abs_lt.1 harg).2
        rw [lt_div_iff₀ hkpos] at this
        linarith [mul_comm (k : ℝ) q.arg]
    rw [hpow, hlog, mul_div_cancel_left₀ _ hk0, Complex.exp_log hq0, mul_div_cancel₀ _ hc]
  · rw [localInverse_of_ne k c _ hj, Function.update_of_ne hj]

/-- The Kummer map is an isomorphism on stalks at the points with `t ≠ 0`. -/
theorem isIso_stalkMap_okaMap_kummerPoly (k : ℕ+) {y : ULift.{u} (Fin (m + 1)) → ℂ}
    (hy : y zero ≠ 0) :
    IsIso ((AnalyticSpace.okaMap (kummerPoly k)).toLRSHom.stalkMap y) := by
  have hy' : okaMapFun (kummerPoly k) y zero = y zero ^ (k : ℕ) := by
    rw [okaMapFun_kummerPoly, Function.update_self]
  have hcont : Continuous fun w : ULift.{u} (Fin (m + 1)) → ℂ ↦ w zero / y zero ^ (k : ℕ) :=
    (continuous_apply zero).div_const _
  refine AnalyticSpace.isIso_stalkMap_okaMap (τ := localInverse k (y zero))
    (analyticAt_localInverse k _ (by
      rw [hy', div_self (pow_ne_zero _ hy)]; exact Complex.one_mem_slitPlane)) ?_ ?_
  · have h₁ : Tendsto (fun p : ULift.{u} (Fin (m + 1)) → ℂ ↦ p zero / y zero) (𝓝 y) (𝓝 1) := by
      rw [← div_self hy]
      exact ((continuous_apply zero).div_const _).continuousAt.tendsto
    have h₂ : ∀ᶠ q : ℂ in 𝓝 1, q ∈ Complex.slitPlane ∧ |Complex.arg q| < Real.pi / k := by
      have h₀ : ∀ᶠ q : ℂ in 𝓝 1, q ∈ Complex.slitPlane :=
        Complex.isOpen_slitPlane.mem_nhds Complex.one_mem_slitPlane
      refine h₀.and ?_
      have := (Complex.continuousAt_arg Complex.one_mem_slitPlane).tendsto
      rw [Complex.arg_one] at this
      exact this.eventually (eventually_abs_sub_lt 0
        (div_pos Real.pi_pos (Nat.cast_pos.2 k.pos : (0 : ℝ) < (k : ℕ)))) |>.mono
        fun q hq ↦ by simpa using hq
    filter_upwards [h₁.eventually h₂] with p hp
    exact localInverse_okaMapFun k hy hp.1 hp.2
  · have h₁ : Tendsto (fun w : ULift.{u} (Fin (m + 1)) → ℂ ↦ w zero / y zero ^ (k : ℕ))
        (𝓝 (okaMapFun (kummerPoly k) y)) (𝓝 1) := by
      have := hcont.continuousAt (x := okaMapFun (kummerPoly k) y)
      rwa [ContinuousAt, hy', div_self (pow_ne_zero _ hy)] at this
    filter_upwards [h₁.eventually (Complex.isOpen_slitPlane.mem_nhds Complex.one_mem_slitPlane)]
      with w hw
    exact okaMapFun_localInverse k hy hw

/-! ### The Kummer cover -/

variable (hB : IsOpen B)

lemma range_subset_puncturedOpens (k : ℕ+) :
    Set.range (((AnalyticSpace.complexAffineSpace.{u} (m + 1)).ofRestrict
      (puncturedOpens B hB) ≫ AnalyticSpace.okaMap (kummerPoly k)).toLRSHom.base) ⊆
      (puncturedOpens B hB : Set (AnalyticSpace.complexAffineSpace.{u} (m + 1))) := by
  rintro _ ⟨x, rfl⟩
  change splitEquiv m (okaMapFun (kummerPoly k) x.1) ∈ Kummer.base B
  rw [okaMapFun_kummerPoly, splitEquiv_update]
  exact (Kummer.cover B k ⟨_, x.2⟩).2

/-- The Kummer map `(t, b) ↦ (tᵏ, b)` of `S°`, as a morphism of complex analytic spaces. -/
def kummerHom (k : ℕ+) : punctured hB ⟶ punctured hB :=
  liftRestrict (AnalyticSpace.ofRestrict _ (puncturedOpens B hB) ≫
    AnalyticSpace.okaMap (kummerPoly k)) (puncturedOpens B hB) (range_subset_puncturedOpens hB k)

lemma kummerHom_comp_ofRestrict (k : ℕ+) :
    kummerHom hB k ≫ AnalyticSpace.ofRestrict _ (puncturedOpens B hB) =
      AnalyticSpace.ofRestrict _ (puncturedOpens B hB) ≫ AnalyticSpace.okaMap (kummerPoly k) :=
  liftRestrict_fac _ _ _

lemma coe_kummerHom_base (k : ℕ+) (x : punctured hB) :
    ((kummerHom hB k).toLRSHom.base x).1 = Function.update x.1 zero (x.1 zero ^ (k : ℕ)) :=
  (congrArg (fun φ ↦ φ.toLRSHom.base x) (kummerHom_comp_ofRestrict hB k)).trans
    (okaMapFun_kummerPoly k x.1)

lemma kummerHom_base (k : ℕ+) (x : punctured hB) :
    (kummerHom hB k).toLRSHom.base x = kummerMap (homeomorph hB) k x := by
  refine Subtype.ext ?_
  rw [coe_kummerHom_base, kummerMap_apply]
  apply (splitEquiv m).injective
  rw [splitEquiv_update]
  change _ = splitEquiv m ((splitEquiv m).symm (Kummer.cover B k (homeomorph hB x)).1)
  rw [Homeomorph.apply_symm_apply]
  rfl

lemma coe_kummerHom_base_eq (k : ℕ+) :
    ⇑(kummerHom hB k).toLRSHom.base = ⇑(kummerMap (homeomorph hB) k) :=
  funext (kummerHom_base hB k)

instance isLocalIso_kummerHom (k : ℕ+) : IsLocalIso (kummerHom hB k) where
  isLocalHomeomorph := by
    rw [coe_kummerHom_base_eq]
    exact (isCoveringMap_kummerMap (homeomorph hB) k).isLocalHomeomorph
  isIso_stalkMap x := by
    set i := AnalyticSpace.ofRestrict _ (puncturedOpens B hB)
    have h₁ : IsIso ((i ≫ AnalyticSpace.okaMap (kummerPoly k)).toLRSHom.stalkMap x) := by
      have h : (i ≫ AnalyticSpace.okaMap (kummerPoly k)).toLRSHom =
          i.toLRSHom ≫ (AnalyticSpace.okaMap (kummerPoly k)).toLRSHom := rfl
      rw [h, LocallyRingedSpace.stalkMap_comp]
      have h₂ : IsIso ((AnalyticSpace.okaMap (kummerPoly k)).toLRSHom.stalkMap
          (i.toLRSHom.base x)) :=
        isIso_stalkMap_okaMap_kummerPoly k (y := x.1) (x.2.2.1)
      exact CategoryTheory.IsIso.comp_isIso' h₂ inferInstance
    rw [← kummerHom_comp_ofRestrict] at h₁
    have h : (kummerHom hB k ≫ i).toLRSHom = (kummerHom hB k).toLRSHom ≫ i.toLRSHom := rfl
    rw [h, LocallyRingedSpace.stalkMap_comp] at h₁
    exact @IsIso.of_isIso_comp_left _ _ _ _ _
      (i.toLRSHom.stalkMap ((kummerHom hB k).toLRSHom.base x))
      ((kummerHom hB k).toLRSHom.stalkMap x) inferInstance h₁

instance isFinite_kummerHom (k : ℕ+) : IsFinite (kummerHom hB k) where
  isClosedMap := by
    rw [coe_kummerHom_base_eq]
    exact (isCoveringMap_kummerMap (homeomorph hB) k).isClosedMap
      (finite_preimage_kummerMap (homeomorph hB) k)
  finite_fiber y := by
    rw [coe_kummerHom_base_eq]
    exact (finite_preimage_kummerMap (homeomorph hB) k y).to_subtype

/-- The **Kummer cover** `(t, b) ↦ (tᵏ, b)` of `S° = {b ∈ B, 0 < ‖t‖ < 1}`. -/
def cover (k : ℕ+) : FiniteEtaleOver (punctured hB) :=
  MorphismProperty.Over.mk ⊤ (kummerHom hB k) ⟨inferInstance, inferInstance⟩

/-- **A finite étale cover of `S° = {b ∈ B, 0 < ‖t‖ < 1}` is a finite disjoint union of Kummer
covers**, for `B` convex and open. -/
theorem exists_iso_sigma_cover (hBc : Convex ℝ B) (W : FiniteEtaleOver (punctured hB))
    [T2Space W.left] :
    ∃ (ι : Type u) (_ : Finite ι) (k : ι → ℕ+),
      Nonempty (W ≅ FiniteEtaleOver.sigma fun i ↦ cover hB (k i)) :=
  FiniteEtaleOver.exists_iso_sigma_of_forall_eq_kummerMap (homeomorph hB) hBc hB (cover hB)
    (fun _ ↦ Homeomorph.refl _) (fun k x ↦ kummerHom_base hB k x) W

end

end ComplexAnalytic.KummerModel
