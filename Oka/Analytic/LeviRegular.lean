/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytic.HartogsRegular
import Oka.Analytic.LeviDirection

/-!
# Extension of meromorphic functions across the zero set of a regular sequence

Let `U ⊆ ℂ^ι` be open and `g, h` holomorphic on `U` such that at every common zero the germs of
`g` and `h` form a regular sequence, and let `f` be meromorphic on `U \ {g = h = 0}` in the sense
that near every point it is a quotient of holomorphic functions whose denominator does not vanish
on any open set (`IsLocallyQuotientAt`). Then near every point of `U` there is a holomorphic
function `c`, not vanishing on any open set, such that `c * f` extends holomorphically
(`hasDenominatorAt_of_isWeaklyRegular`); for finitely many such functions `c` can be chosen in
common (`exists_common_denominator_of_isWeaklyRegular`).

## Proof

Near a common zero we choose, by `exists_direction_forall_analyticAt`, a direction `v` in which
the germ of `g` is general, such that `f` is holomorphic near arbitrarily small circles in the
line spanned by `v`. In the coordinates in which `v` is the last coordinate direction, the
Weierstrass preparation theorem slices the common zero set of `g` and `h` as in
`LocalOkaRing.exists_slices` (`LocalOkaRing.exists_slices_of_isGeneralIn`), and by compactness `f`
is holomorphic on a neighbourhood of the product of a small ball with one of these circles. This
is the situation of `exists_mul_eq_of_prod`.

## Main results

- `LocalOkaRing.exists_slices_of_isGeneralIn`: the slicing of the common zero set of a regular
  sequence in prescribed coordinates, for all small radii.
- `hasDenominatorAt_fin`, `hasDenominatorAt_of_isWeaklyRegular`: **Levi's extension theorem**
  across the common zero set of a regular sequence.
- `exists_common_denominator_of_isWeaklyRegular`: a common denominator for finitely many
  functions.
-/

open Set Filter Metric Polynomial
open scoped Topology

/-- The linear isomorphism `ℂⁿ × ℂ ≃ ℂⁿ⁺¹`, `(a, t) ↦ Fin.snoc a t`. -/
noncomputable def finSnocCLE (n : ℕ) : ((Fin n → ℂ) × ℂ) ≃L[ℂ] (Fin (n + 1) → ℂ) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun p ↦ Fin.snoc p.1 p.2
      invFun := fun y ↦ (Fin.init y, y (Fin.last n))
      map_add' := fun p q ↦ by
        funext i
        induction i using Fin.lastCases <;> simp
      map_smul' := fun c p ↦ by
        funext i
        induction i using Fin.lastCases <;> simp
      left_inv := fun p ↦ by simp
      right_inv := fun y ↦ by simp }

@[simp]
lemma finSnocCLE_apply {n : ℕ} (p : (Fin n → ℂ) × ℂ) :
    finSnocCLE n p = Fin.snoc p.1 p.2 :=
  rfl

namespace LocalOkaRing

variable {n : ℕ}

/-- **Slicing the common zero set of a regular sequence in prescribed coordinates.** Let `H` be
a nonzerodivisor modulo `G`, where `G` and `H` are germs at the origin representing `g` and `h`,
and let `φ` be a linear change of coordinates in which `G` is general in the last variable. Then
there is `ρ > 0` such that for every `0 < ε ≤ ρ` there is `δ > 0` with the following properties:
in the coordinates `(a, t) ∈ ℂⁿ × ℂ`, for all `a` in the ball of radius `δ` and `‖t‖ ≤ 3ε`, the
point lies in `N` and `g` does not vanish there if `ε ≤ ‖t‖`, and the set of `a` over which `g`
and `h` have a common zero with `‖t‖ ≤ 3ε` has empty interior. -/
theorem exists_slices_of_isGeneralIn {G H : LocalOkaRing (Fin (n + 1))}
    (hreg : ∀ y, G ∣ H * y → G ∣ y)
    {g h : (Fin (n + 1) → ℂ) → ℂ} (hg : (G : MvPowerSeries (Fin (n + 1)) ℂ).Represents g)
    (hh : (H : MvPowerSeries (Fin (n + 1)) ℂ).Represents h) {N : Set (Fin (n + 1) → ℂ)}
    (hN : N ∈ 𝓝 0) (φ : (Fin (n + 1) → ℂ) ≃L[ℂ] (Fin (n + 1) → ℂ))
    (hφ : ((congr φ G : LocalOkaRing (Fin (n + 1))) :
      MvPowerSeries (Fin (n + 1)) ℂ).IsGeneralIn (Fin.last n)) :
    ∃ ρ > 0, ∀ ε : ℝ, 0 < ε → ε ≤ ρ → ∃ δ > 0,
      (∀ a ∈ ball (0 : Fin n → ℂ) δ, ∀ t : ℂ, ‖t‖ ≤ 3 * ε →
        φ.symm (Fin.snoc a t) ∈ N ∧ (ε ≤ ‖t‖ → g (φ.symm (Fin.snoc a t)) ≠ 0)) ∧
      interior {a ∈ ball (0 : Fin n → ℂ) δ | ∃ t : ℂ, ‖t‖ ≤ 3 * ε ∧
        g (φ.symm (Fin.snoc a t)) = 0 ∧ h (φ.symm (Fin.snoc a t)) = 0} = ∅ := by
  obtain ⟨u, hu, W, hW, heq⟩ := localweierstrass_preparation _ hφ
  set e := congr φ
  have hreg' : ∀ y, e G ∣ e H * y → e G ∣ y := fun y hy ↦ by
    have := hreg (e.symm y) (by simpa using map_dvd e.symm hy)
    simpa using map_dvd e this
  obtain ⟨c, hc0, hc⟩ := exists_ne_zero_incl_mem_span_pair hW hu heq hreg'
  obtain ⟨α, β, hαβ⟩ := Ideal.mem_span_pair.mp hc
  set v : LocalOkaRing (Fin (n + 1)) := ↑hu.unit⁻¹
  have hWG : fromPolynomial W = e G * v := by
    rw [heq, mul_assoc, IsUnit.mul_val_inv, mul_one]
  -- the identities between the germs hold as identities of functions near the origin
  have hφ0 : Tendsto φ.symm (𝓝 0) (𝓝 0) := by
    simpa using φ.symm.continuous.tendsto (0 : Fin (n + 1) → ℂ)
  have hE : ∀ᶠ y in 𝓝 (0 : Fin (n + 1) → ℂ), φ.symm y ∈ N ∧
      ((e G : LocalOkaRing (Fin (n + 1))) : MvPowerSeries (Fin (n + 1)) ℂ).eval y =
        g (φ.symm y) ∧
      ((e H : LocalOkaRing (Fin (n + 1))) : MvPowerSeries (Fin (n + 1)) ℂ).eval y =
        h (φ.symm y) ∧
      ((fromPolynomial W : LocalOkaRing (Fin (n + 1))) : MvPowerSeries (Fin (n + 1)) ℂ).eval y =
        ((e G : LocalOkaRing (Fin (n + 1))) : MvPowerSeries (Fin (n + 1)) ℂ).eval y *
          (v : MvPowerSeries (Fin (n + 1)) ℂ).eval y ∧
      ((incl c : LocalOkaRing (Fin (n + 1))) : MvPowerSeries (Fin (n + 1)) ℂ).eval y =
        (α : MvPowerSeries (Fin (n + 1)) ℂ).eval y *
          ((e G : LocalOkaRing (Fin (n + 1))) : MvPowerSeries (Fin (n + 1)) ℂ).eval y +
        (β : MvPowerSeries (Fin (n + 1)) ℂ).eval y *
          ((e H : LocalOkaRing (Fin (n + 1))) : MvPowerSeries (Fin (n + 1)) ℂ).eval y := by
    filter_upwards [hφ0.eventually hN, (congr_represents (φ := φ) hg).eval_eq,
      (congr_represents (φ := φ) hh).eval_eq, eventually_eval_mul (e G) v,
      eventually_eval_add (α * e G) (β * e H), eventually_eval_mul α (e G),
      eventually_eval_mul β (e H)] with y hN hg hh hmul hadd hmα hmβ
    refine ⟨hN, hg, hh, by rw [hWG, hmul], ?_⟩
    rw [← hαβ, hadd, hmα, hmβ]
  obtain ⟨ρ, hρ, hρE⟩ := Metric.eventually_nhds_iff.mp hE
  refine ⟨ρ / 4, by positivity, fun ε hε0 hερ ↦ ?_⟩
  obtain ⟨δ₁, hδ₁, hroot⟩ := Metric.eventually_nhds_iff.mp
    (eventually_fromPolynomial_ne_zero_of_le W hW hε0)
  obtain ⟨ρc, hρc, hcball⟩ := c.locallyConvergent.hasFPowerSeriesOnBall
  set δ := min δ₁ (min ρ ρc)
  have hδ : 0 < δ := lt_min hδ₁ (lt_min hρ hρc)
  have hpt : ∀ a ∈ ball (0 : Fin n → ℂ) δ, ∀ t : ℂ, ‖t‖ ≤ 3 * ε →
      dist (Fin.snoc a t : Fin (n + 1) → ℂ) 0 < ρ := fun a ha t ht ↦ by
    rw [dist_zero_right]
    refine norm_snoc_lt hρ ((mem_ball_zero_iff.mp ha).trans_le
      ((min_le_right _ _).trans (min_le_left _ _))) (by linarith)
  refine ⟨δ, hδ, fun a ha t ht ↦ ⟨(hρE (hpt a ha t ht)).1, fun hεt hzero ↦ ?_⟩, ?_⟩
  · obtain ⟨-, hg, -, hW', -⟩ := hρE (hpt a ha t ht)
    have ha₁ : dist a 0 < δ₁ := by
      rw [dist_zero_right]
      exact (mem_ball_zero_iff.mp ha).trans_le (min_le_left _ _)
    refine hroot ha₁ t hεt ?_
    rw [hW', hg, hzero, zero_mul]
  -- the common zeros lie over the zero set of `c`
  have hsub : {a ∈ ball (0 : Fin n → ℂ) δ | ∃ t : ℂ, ‖t‖ ≤ 3 * ε ∧
      g (φ.symm (Fin.snoc a t)) = 0 ∧ h (φ.symm (Fin.snoc a t)) = 0} ⊆
        ball (0 : Fin n → ℂ) δ ∩ (c : MvPowerSeries (Fin n) ℂ).eval ⁻¹' {0} := by
    rintro a ⟨ha, t, ht, hgz, hhz⟩
    obtain ⟨-, hg, hh, -, hcE⟩ := hρE (hpt a ha t ht)
    refine ⟨ha, ?_⟩
    have := hcE
    rw [hg, hh, hgz, hhz, mul_zero, mul_zero, add_zero, eval_incl] at this
    simpa [Fin.snoc_castSucc] using this
  refine subset_empty_iff.mp (le_of_le_of_eq (interior_mono hsub) ?_)
  have hana : AnalyticOnNhd ℂ (c : MvPowerSeries (Fin n) ℂ).eval (ball 0 δ) := fun a ha ↦
    hcball.analyticAt_of_mem (by
      rw [Metric.eball_ofReal]
      exact ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _)) ha)
  obtain ⟨a₀, ha₀, hca₀⟩ :
      ∃ a ∈ ball (0 : Fin n → ℂ) δ, (c : MvPowerSeries (Fin n) ℂ).eval a ≠ 0 := by
    by_contra! H
    exact hc0 (eq_zero_of_eventually_eval_eq_zero
      (Filter.mem_of_superset (ball_mem_nhds 0 hδ) H))
  exact hana.interior_inter_preimage_zero_eq_empty (convex_ball 0 δ).isPreconnected ha₀ hca₀

end LocalOkaRing

/-- If `g` does not vanish identically near the origin on the line spanned by `v`, then after the
change of coordinates `lineEquiv v` a germ representing `g` is general in the last variable. -/
theorem LocalOkaRing.isGeneralIn_congr_lineEquiv {n : ℕ} {G : LocalOkaRing (Fin (n + 1))}
    {g : (Fin (n + 1) → ℂ) → ℂ} (hG : (G : MvPowerSeries (Fin (n + 1)) ℂ).Represents g)
    (v : Fin (n + 1) → ℂ) (hv : v (Fin.last n) ≠ 0)
    (hfreq : ∃ᶠ t in 𝓝 (0 : ℂ), g (t • v) ≠ 0) :
    ((LocalOkaRing.congr (lineEquiv v hv) G : LocalOkaRing (Fin (n + 1))) :
      MvPowerSeries (Fin (n + 1)) ℂ).IsGeneralIn (Fin.last n) := by
  classical
  intro hgen
  have hax := (LocalOkaRing.congr_represents (φ := lineEquiv v hv) hG).eventually_axis_eq_zero
    (Fin.last n) hgen
  refine hfreq (hax.mono fun t ht ↦ ?_)
  rw [Function.comp_apply, lineEquiv_symm_smul_single v hv t] at ht
  exact not_not.mpr ht

/-- `Fin.snoc 0 t` is `t` times the last standard basis vector. -/
lemma Fin.snoc_zero_eq_smul_single {n : ℕ} (t : ℂ) :
    (Fin.snoc (0 : Fin n → ℂ) t : Fin (n + 1) → ℂ) = t • Pi.single (Fin.last n) 1 := by
  funext i
  induction i using Fin.lastCases with
  | last => simp
  | cast j => simp [(Fin.castSucc_lt_last j).ne]

/-- **Levi's extension theorem** across the common zero set of a regular sequence, in
`ℂⁿ⁺¹`. Let `z₀ ∈ U` and let `G ≠ 0` and `H` be germs representing `g` and `h` at `z₀`, with `H`
a nonzerodivisor modulo `G`. If `f` is locally a quotient of holomorphic functions at every point
of `U` outside `{g = h = 0}`, then `f` has a holomorphic denominator near `z₀`. -/
theorem hasDenominatorAt_fin {n : ℕ} {U : Set (Fin (n + 1) → ℂ)} (hU : IsOpen U)
    {g h : (Fin (n + 1) → ℂ) → ℂ} {z₀ : Fin (n + 1) → ℂ} (hz₀ : z₀ ∈ U)
    {G H : LocalOkaRing (Fin (n + 1))} (hG0 : G ≠ 0) (hreg : ∀ y, G ∣ H * y → G ∣ y)
    (hG : (G : MvPowerSeries (Fin (n + 1)) ℂ).Represents fun w ↦ g (w + z₀))
    (hH : (H : MvPowerSeries (Fin (n + 1)) ℂ).Represents fun w ↦ h (w + z₀))
    {f : (Fin (n + 1) → ℂ) → ℂ}
    (hf : ∀ z ∈ U, ¬(g z = 0 ∧ h z = 0) → IsLocallyQuotientAt f z) :
    HasDenominatorAt {z | g z = 0 ∧ h z = 0} f z₀ := by
  classical
  set g₀ : (Fin (n + 1) → ℂ) → ℂ := fun w ↦ g (w + z₀)
  set f₀ : (Fin (n + 1) → ℂ) → ℂ := fun w ↦ f (w + z₀)
  -- `g₀` is analytic near the origin and does not vanish identically there
  obtain ⟨ρ₁, hρ₁, hga⟩ := (analyticAt_of_represents G.2 hG).exists_ball_analyticOnNhd
  obtain ⟨ρ₂, hρ₂, hρ₂U⟩ := Metric.isOpen_iff.mp (hU.preimage (continuous_add_const z₀)) 0
    (by simpa using hz₀)
  set ρ := min ρ₁ ρ₂
  have hρ : 0 < ρ := lt_min hρ₁ hρ₂
  have hρU : ∀ w ∈ ball (0 : Fin (n + 1) → ℂ) ρ, w + z₀ ∈ U := fun w hw ↦
    hρ₂U (ball_subset_ball (min_le_right _ _) hw)
  have hg0 : ∃ᶠ w in 𝓝 (0 : Fin (n + 1) → ℂ), g₀ w ≠ 0 := fun hev ↦
    hG0 (Subtype.ext (MvPowerSeries.eq_zero_of_represents_zero
      (hG.congr (hev.mono fun w hw ↦ not_not.mp hw))))
  have hq : ∀ w ∈ ball (0 : Fin (n + 1) → ℂ) ρ, g₀ w ≠ 0 → IsLocallyQuotientAt f₀ w :=
    fun w hw hgw ↦ by
      simpa using (hf (w + z₀) (hρU w hw) fun h ↦ hgw h.1).comp_continuousLinearEquiv
        (ContinuousLinearEquiv.refl ℂ _) z₀
  -- a direction avoiding the poles of `f`
  obtain ⟨v, hv, hfreq, hcirc⟩ := exists_direction_forall_analyticAt hρ
    (hga.mono (ball_subset_ball (min_le_left _ _))) hg0 hq
    (V := {v : Fin (n + 1) → ℂ | v (Fin.last n) ≠ 0})
    (isOpen_ne_fun (continuous_apply _) continuous_const)
    ⟨Pi.single (Fin.last n) 1, by simp⟩ (by simp)
  set φ := lineEquiv v hv
  obtain ⟨ρ₀, hρ₀, hsl⟩ := LocalOkaRing.exists_slices_of_isGeneralIn hreg hG hH
    (ball_mem_nhds 0 hρ) φ (LocalOkaRing.isGeneralIn_congr_lineEquiv hG v hv hfreq)
  obtain ⟨r, ⟨hr0, hrρ₀⟩, hrc⟩ := hcirc ρ₀ hρ₀
  obtain ⟨δ, hδ, hgood, hbad⟩ := hsl (r / 2) (half_pos hr0) (by linarith)
  -- the coordinates
  set Ψ : ((Fin n → ℂ) × ℂ) ≃L[ℂ] (Fin (n + 1) → ℂ) := (finSnocCLE n).trans φ.symm
  have hΨ : ∀ p, Ψ p = φ.symm (Fin.snoc p.1 p.2) := fun p ↦ rfl
  have hΨt : ∀ t : ℂ, Ψ (0, t) = t • v := fun t ↦ by
    rw [hΨ, Fin.snoc_zero_eq_smul_single, lineEquiv_symm_smul_single]
  -- by compactness, `f` is holomorphic near the product of a small ball with the circle
  set A : Set ((Fin n → ℂ) × ℂ) := {p | AnalyticAt ℂ f₀ (Ψ p)}
  have hAo : IsOpen A := (isOpen_analyticAt ℂ f₀).preimage Ψ.continuous
  have hKA : ({(0 : Fin n → ℂ)} ×ˢ sphere (0 : ℂ) r) ⊆ A := by
    rintro ⟨a, t⟩ ⟨ha, ht⟩
    rw [mem_singleton_iff] at ha
    subst ha
    change AnalyticAt ℂ f₀ (Ψ (0, t))
    rw [hΨt]
    exact hrc t (mem_sphere_zero_iff_norm.mp ht)
  obtain ⟨η, hη, hηA⟩ := (isCompact_singleton.prod
    (isCompact_sphere (0 : ℂ) r)).exists_thickening_subset_open hAo hKA
  set η' := min η (r / 2)
  have hη' : 0 < η' := lt_min hη (half_pos hr0)
  have htube : ∀ a : Fin n → ℂ, ‖a‖ < η' → ∀ t : ℂ, r - η' < ‖t‖ → ‖t‖ < r + η' →
      AnalyticAt ℂ f₀ (Ψ (a, t)) := by
    intro a ha t ht₁ ht₂
    have htpos : 0 < ‖t‖ := by linarith [min_le_right η (r / 2)]
    refine hηA (Metric.mem_thickening_iff.mpr ⟨(0, ((r / ‖t‖ : ℝ) : ℂ) * t),
      ⟨rfl, ?_⟩, ?_⟩)
    · rw [mem_sphere_zero_iff_norm, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (div_pos hr0 htpos), div_mul_cancel₀ _ htpos.ne']
    · have htc : (‖t‖ : ℂ) ≠ 0 := by exact_mod_cast htpos.ne'
      have heq : t - ((r / ‖t‖ : ℝ) : ℂ) * t = (((‖t‖ - r) / ‖t‖ : ℝ) : ℂ) * t := by
        push_cast
        field_simp
      rw [Prod.dist_eq, max_lt_iff, dist_zero_right, dist_eq_norm, heq, norm_mul,
        Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos htpos,
        div_mul_cancel₀ _ htpos.ne', abs_lt]
      have := min_le_left η (r / 2)
      exact ⟨by linarith, by constructor <;> linarith⟩
  -- the extension in the coordinates
  set D := ball (0 : Fin n → ℂ) (min δ η')
  have hDδ : ∀ a ∈ D, a ∈ ball (0 : Fin n → ℂ) δ := fun a ha ↦
    ball_subset_ball (min_le_left _ _) ha
  set S' : Set ((Fin n → ℂ) × ℂ) := (fun p ↦ Ψ p + z₀) ⁻¹' {z | g z = 0 ∧ h z = 0}
  have hbad' : interior {a ∈ D | ∃ t : ℂ, ‖t‖ ≤ r ∧ (a, t) ∈ S'} = ∅ :=
    subset_empty_iff.mp (hbad ▸ interior_mono fun a ⟨ha, t, ht, hS⟩ ↦
      ⟨hDδ a ha, t, by linarith, hS⟩)
  have hmer' : ∀ a ∈ D, ∀ t : ℂ, ‖t‖ ≤ r → (a, t) ∉ S' →
      IsLocallyQuotientAt (fun p ↦ f (Ψ p + z₀)) (a, t) := fun a ha t ht hS ↦ by
    have hmem := (hgood a (hDδ a ha) t (by linarith)).1
    exact (hf _ (hρU _ hmem) hS).comp_continuousLinearEquiv Ψ z₀
  have hann' : DifferentiableOn ℂ (fun p ↦ f (Ψ p + z₀))
      (D ×ˢ {t : ℂ | r - η' < ‖t‖ ∧ ‖t‖ < r + η'}) := by
    rintro ⟨a, t⟩ ⟨ha, ht₁, ht₂⟩
    have ha' : ‖a‖ < η' := (mem_ball_zero_iff.mp ha).trans_le (min_le_right _ _)
    exact ((htube a ha' t ht₁ ht₂).differentiableAt.comp (a, t)
      Ψ.differentiableAt).differentiableWithinAt
  obtain ⟨c, F, hc, hF, hc0, hcF⟩ := exists_mul_eq_of_prod isOpen_ball
    (convex_ball _ _).isPreconnected ⟨0, mem_ball_self (lt_min hδ hη')⟩ hr0
    (by linarith : r - η' < r) (by linarith : r < r + η') hbad' hmer' hann'
  have h' : HasDenominatorAt S' (fun p ↦ f (Ψ p + z₀)) (0, 0) :=
    ⟨D ×ˢ ball 0 r, isOpen_ball.prod isOpen_ball,
      ⟨mem_ball_self (lt_min hδ hη'), mem_ball_self hr0⟩, c, F, hc, hF, hc0, hcF⟩
  have h'' := h'.of_continuousLinearEquiv Ψ z₀
  rwa [Prod.mk_zero_zero, map_zero, zero_add] at h''

section Regular

variable {ι : Type*} [Fintype ι] {U : Set (ι → ℂ)} {g h : (ι → ℂ) → ℂ}

/-- **Levi's extension theorem** across the common zero set of a regular sequence. Let
`z₀ ∈ U` and suppose that, if `z₀` is a common zero of `g` and `h`, some germs representing `g`
and `h` at `z₀` form a regular sequence. If `f` is locally a quotient of holomorphic functions
at every point of `U` outside `{g = h = 0}`, then near `z₀` there is a holomorphic function `c`
whose zero set has empty interior such that `c * f` extends holomorphically. -/
theorem hasDenominatorAt_of_isWeaklyRegular (hU : IsOpen U) {z₀ : ι → ℂ} (hz₀ : z₀ ∈ U)
    (hreg : g z₀ = 0 → h z₀ = 0 → ∃ G H : LocalOkaRing ι,
      (G : MvPowerSeries ι ℂ).Represents (fun w ↦ g (w + z₀)) ∧
      (H : MvPowerSeries ι ℂ).Represents (fun w ↦ h (w + z₀)) ∧
      RingTheory.Sequence.IsWeaklyRegular (LocalOkaRing ι) [G, H])
    {f : (ι → ℂ) → ℂ} (hf : ∀ z ∈ U, ¬(g z = 0 ∧ h z = 0) → IsLocallyQuotientAt f z) :
    HasDenominatorAt {z | g z = 0 ∧ h z = 0} f z₀ := by
  by_cases hS : g z₀ = 0 ∧ h z₀ = 0
  · obtain ⟨G, H, hG, hH, hGH⟩ := hreg hS.1 hS.2
    have hG0 := hGH.ne_zero_of_cons
    cases hn : Fintype.card ι with
    | zero =>
      -- in no variables, a nonzero germ is a unit and so does not vanish at the origin
      haveI : IsEmpty ι := Fintype.card_eq_zero_iff.mp hn
      have hu := LocalOkaRing.isUnit_iff_ne_zero.mpr hG0
      rw [LocalOkaRing.isUnit_iff, LocalOkaRing.constantCoeff_apply, ← hG.apply_zero] at hu
      exact (hu (by rw [zero_add]; exact hS.1)).elim
    | succ m =>
      set φ : (ι → ℂ) ≃L[ℂ] (Fin (m + 1) → ℂ) :=
        (LinearEquiv.funCongrLeft ℂ ℂ (Fintype.equivFinOfCardEq hn).symm).toContinuousLinearEquiv
      set e := LocalOkaRing.congr φ
      have hrep : ∀ {P : LocalOkaRing ι} {F : (ι → ℂ) → ℂ},
          (P : MvPowerSeries ι ℂ).Represents (fun w ↦ F (w + z₀)) →
          ((e P : LocalOkaRing (Fin (m + 1))) : MvPowerSeries (Fin (m + 1)) ℂ).Represents
            (fun w ↦ (F ∘ φ.symm) (w + φ z₀)) := fun hP ↦
        (LocalOkaRing.congr_represents hP).congr (Eventually.of_forall fun w ↦ by
          simp [map_add])
      have hf' : ∀ z ∈ φ.symm ⁻¹' U, ¬((g ∘ φ.symm) z = 0 ∧ (h ∘ φ.symm) z = 0) →
          IsLocallyQuotientAt (f ∘ φ.symm) z := fun z hz hzS ↦ by
        have h' := hf _ hz hzS
        rw [← add_zero (φ.symm z)] at h'
        simpa [Function.comp_def] using h'.comp_continuousLinearEquiv φ.symm 0
      have := hasDenominatorAt_fin (hU.preimage φ.symm.continuous) (by simpa using hz₀)
        (G := e G) (H := e H) ((map_ne_zero_iff e e.injective).mpr hG0) (fun y hy ↦ ?_)
        (hrep hG) (hrep hH) hf'
      · have h₂ : HasDenominatorAt ((fun x ↦ φ.symm x + 0) ⁻¹' {z | g z = 0 ∧ h z = 0})
            (fun x ↦ f (φ.symm x + 0)) (φ z₀) := by simpa [Function.comp_def] using this
        simpa using h₂.of_continuousLinearEquiv φ.symm 0
      · have := hGH.dvd_of_dvd_mul (y := e.symm y) (by simpa using map_dvd e.symm hy)
        simpa using map_dvd e this
  · exact (hf z₀ hz₀ hS).hasDenominatorAt

/-- **A common denominator** for finitely many functions which are locally quotients of
holomorphic functions outside the common zero set of a regular sequence. -/
theorem exists_common_denominator_of_isWeaklyRegular (hU : IsOpen U)
    (hreg : ∀ z ∈ U, g z = 0 → h z = 0 → ∃ G H : LocalOkaRing ι,
      (G : MvPowerSeries ι ℂ).Represents (fun w ↦ g (w + z)) ∧
      (H : MvPowerSeries ι ℂ).Represents (fun w ↦ h (w + z)) ∧
      RingTheory.Sequence.IsWeaklyRegular (LocalOkaRing ι) [G, H])
    {κ : Type*} (T : Finset κ) {f : κ → (ι → ℂ) → ℂ}
    (hf : ∀ i ∈ T, ∀ z ∈ U, ¬(g z = 0 ∧ h z = 0) → IsLocallyQuotientAt (f i) z)
    {z₀ : ι → ℂ} (hz₀ : z₀ ∈ U) :
    ∃ W : Set (ι → ℂ), IsOpen W ∧ z₀ ∈ W ∧ ∃ c : (ι → ℂ) → ℂ, DifferentiableOn ℂ c W ∧
      interior (W ∩ c ⁻¹' {0}) = ∅ ∧ ∀ i ∈ T, ∃ F : (ι → ℂ) → ℂ, DifferentiableOn ℂ F W ∧
        ∀ z ∈ W, ¬(g z = 0 ∧ h z = 0) → ContinuousAt (f i) z → F z = c z * f i z :=
  exists_common_denominator T fun i hi ↦
    hasDenominatorAt_of_isWeaklyRegular hU hz₀ (hreg z₀ hz₀) (hf i hi)

end Regular
