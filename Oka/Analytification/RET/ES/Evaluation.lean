/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analysis.Complex.LiouvillePolynomial
import Oka.Analytification.RET.ES.BoundedSectionsTrace
import Oka.Analytification.RET.ES.Cap

/-!
# The evaluation embedding

Keep the notation of `Oka/Analytification/RET/ES/Cap.lean`: `p : W → N°` is a finite étale cover
decomposed over the annulus `G × {ρ⁻¹ < ‖w‖ < ρ}` into Kummer covers of degrees `kᵢ`, and the cap
is its extension over `G × ℙ¹` (Grauert–Remmert 1958, Hilfssatz 9–10, Satz 41).

* **Poles at infinity** (`ComplexAnalytic.Cap.AnnulusDecomposition.capPole`): a section of the cap
  with a pole of order `≤ k` at `w = ∞` is a section `s` of `𝒜` in the chart `w` together with
  holomorphic functions `fᵢ` on the Kummer covers at infinity such that `s = wᵏ fᵢ` on the
  overlap. These form an additive group, stable under multiplication by sections of the cap.
* **The evaluation** (`ComplexAnalytic.Cap.AnnulusDecomposition.evalVec`): for points `wᵥ`,
  `ν < M`, of the annulus, `λ(s)(b)` is the family of values of `s` on the sheets `(i, j)`,
  `j < kᵢ`, over the points `(b, wᵥ)`, a vector in `ℂ^{M ∑ kᵢ}`. It is additive, multiplicative,
  `𝒪`-linear (`ComplexAnalytic.Cap.AnnulusDecomposition.evalVec_pullback`), compatible with
  restriction and holomorphic in `b`
  (`ComplexAnalytic.Cap.AnnulusDecomposition.differentiableOn_evalVec`).
* **Injectivity** (`ComplexAnalytic.Cap.AnnulusDecomposition.eq_zero_of_forall_evalVec_eq_zero`):
  if the `wᵥ` are distinct and `M > k ∑ kᵢ`, a section with a pole of order `≤ k` at infinity
  whose evaluation vanishes is zero. For fixed `b`, the coefficients of the characteristic
  polynomial of `s` are holomorphic in `w` on `{‖w‖ < ρ}` (Riemann extension,
  `ComplexAnalytic.BoundedSections.exists_coeff_charPolyFun`) and are, on the overlap, the
  coefficients of `∏ (T - wᵏ fᵢ(u'))` over the Kummer roots `u'` of `w⁻¹`
  (`ComplexAnalytic.Cap.infCoeff`), which continue them to entire functions of growth
  `O(‖w‖^{k ∑ kᵢ})`. By Liouville they are polynomials of degree `≤ k ∑ kᵢ`
  (`ComplexAnalytic.Cap.eqOn_zero_of_infCoeff`); vanishing at the `wᵥ`, the characteristic
  polynomial is `T^{∑ kᵢ}`, so `s` vanishes, and then so do the `fᵢ` by the identity theorem.
-/

open CategoryTheory Opposite Topology Set Filter Polynomial Metric

universe u

namespace ComplexAnalytic.Cap

open AnalyticSpace BoundedSections KummerModel Complex.ProjectiveLineBundle AnnulusDecomposition

noncomputable section

/-! ### Products over the `k`-th roots -/

lemma zeta_pow_mul_pow {k : ℕ} (hk : 0 < k) (j : ℕ) (r : ℂ) :
    (Kummer.zeta k ^ j * r) ^ k = r ^ k := by
  rw [mul_pow, ← pow_mul, mul_comm j k, pow_mul, (Kummer.isPrimitiveRoot_zeta hk).pow_eq_one,
    one_pow, one_mul]

/-- The product `∏_{j < k} g(ζʲ r)` over the `k`-th roots of `rᵏ` depends only on `rᵏ`. -/
lemma prod_zeta_pow_mul_eq {R : Type*} [CommMonoid R] {k : ℕ} (hk : 0 < k) (g : ℂ → R)
    {r r' : ℂ} (h : r ^ k = r' ^ k) :
    ∏ j : Fin k, g (Kummer.zeta k ^ (j : ℕ) * r) =
      ∏ j : Fin k, g (Kummer.zeta k ^ (j : ℕ) * r') := by
  have key : ∀ α : ℂ, ∏ j : Fin k, g (Kummer.zeta k ^ (j : ℕ) * α) =
      ((nthRoots k (α ^ k)).map g).prod := fun α ↦ by
    rw [(Kummer.isPrimitiveRoot_zeta hk).nthRoots_eq rfl, Multiset.map_map,
      Fin.prod_univ_eq_prod_range (fun j ↦ g (Kummer.zeta k ^ j * α)) k,
      Finset.prod_eq_multiset_prod]
    rfl
  rw [key, key, h]

lemma zeta_pow_mul_kroot_pow {n : ℕ} (hn : n ≠ 0) (j : ℕ) {w₁ w : ℂ} (hw₁ : w₁ ≠ 0) (hw : w ≠ 0) :
    (Kummer.zeta n ^ j * kroot n w₁ w) ^ n = w := by
  rw [zeta_pow_mul_pow (Nat.pos_of_ne_zero hn), kroot_pow hn hw₁ hw]

lemma zeta_pow_mul_kroot_ne_zero {n : ℕ} (hn : n ≠ 0) (j : ℕ) {w₁ w : ℂ} (hw₁ : w₁ ≠ 0)
    (hw : w ≠ 0) : Kummer.zeta n ^ j * kroot n w₁ w ≠ 0 := fun h ↦
  hw (by rw [← zeta_pow_mul_kroot_pow hn j hw₁ hw, h, zero_pow hn])

/-! ### Liouville on the Kummer cap -/

section Liouville

variable {ι : Type*} [Fintype ι] (deg : ι → ℕ+) (k : ℕ) (φ : ι → ℂ → ℂ) (l : ℕ)

/-- The `l`-th coefficient of `∏_{i, j < kᵢ} (T - wᵏ φᵢ((ζʲ w^{1/kᵢ})⁻¹))`: the characteristic
polynomial of the functions `φᵢ` on the Kummer covers `u'^{kᵢ} = w⁻¹`, twisted by `wᵏ`. The
`kᵢ`-th root of `w` is the branch `kroot kᵢ w₁`; the result does not depend on `w₁`
(`ComplexAnalytic.Cap.infCoeff_eq`). -/
def infCoeff (w₁ w : ℂ) : ℂ :=
  (∏ ij : Σ i, Fin (deg i), (X - C (w ^ k * φ ij.1
    (Kummer.zeta (deg ij.1) ^ (ij.2 : ℕ) * kroot (deg ij.1) w₁ w)⁻¹))).coeff l

/-- `infCoeff` does not depend on the branch of the roots. -/
lemma infCoeff_eq {w₁ w₂ w : ℂ} (hw₁ : w₁ ≠ 0) (hw₂ : w₂ ≠ 0) (hw : w ≠ 0) :
    infCoeff deg k φ l w₁ w = infCoeff deg k φ l w₂ w := by
  have key (w₃ : ℂ) : ∏ ij : Σ i, Fin (deg i), (X - C (w ^ k * φ ij.1
      (Kummer.zeta (deg ij.1) ^ (ij.2 : ℕ) * kroot (deg ij.1) w₃ w)⁻¹)) =
      ∏ i, ∏ j : Fin (deg i), (fun u ↦ X - C (w ^ k * φ i u⁻¹))
        (Kummer.zeta (deg i) ^ (j : ℕ) * kroot (deg i) w₃ w) :=
    Fintype.prod_sigma _
  unfold infCoeff
  rw [key, key]
  refine congrArg (fun P : ℂ[X] ↦ P.coeff l) (Finset.prod_congr rfl fun i _ ↦ ?_)
  exact prod_zeta_pow_mul_eq (deg i).pos (fun u ↦ X - C (w ^ k * φ i u⁻¹))
    ((kroot_pow (deg i).ne_zero hw₁ hw).trans (kroot_pow (deg i).ne_zero hw₂ hw).symm)

variable {ρ : ℝ} {deg k φ l}

lemma norm_pow_inv_zeta_pow_mul_kroot {n : ℕ} (hn : n ≠ 0) (j : ℕ) {w₁ w : ℂ} (hw₁ : w₁ ≠ 0)
    (hw : w ≠ 0) : ‖((Kummer.zeta n ^ j * kroot n w₁ w)⁻¹) ^ n‖ = ‖w‖⁻¹ := by
  rw [inv_pow, zeta_pow_mul_kroot_pow hn j hw₁ hw, norm_inv]

/-- **Liouville on the cap**: let `A` be holomorphic on `{‖w‖ < ρ}` and equal on the overlap
`{ρ⁻¹ < ‖w‖ < ρ}` to the `l`-th coefficient of the characteristic polynomial of functions `φᵢ`,
holomorphic on the Kummer covers `{‖u'^{kᵢ}‖ < ρ}` of the chart at infinity, twisted by `wᵏ`.
Then `A` extends to an entire function of growth `O(‖w‖^{k ∑ kᵢ})`, a polynomial of degree
`≤ k ∑ kᵢ`; if `A` vanishes at more than `k ∑ kᵢ` points, it vanishes. -/
theorem eqOn_zero_of_infCoeff (hρ : 1 < ρ)
    (hφ : ∀ i, DifferentiableOn ℂ (φ i) {u | ‖u ^ (deg i : ℕ)‖ < ρ})
    {A : ℂ → ℂ} (hA : DifferentiableOn ℂ A (ball 0 ρ))
    (hAB : ∀ w ∈ overlap ρ, A w = infCoeff deg k φ l w w)
    {M : ℕ} (hM : (∑ i, (deg i : ℕ)) * k < M) {w : Fin M → ℂ} (hw : Function.Injective w)
    (hwρ : ∀ ν, w ν ∈ ball (0 : ℂ) ρ) (h0 : ∀ ν, A (w ν) = 0) : EqOn A 0 (ball 0 ρ) := by
  classical
  have hρ0 : 0 < ρ := zero_lt_one.trans hρ
  have hρi : ρ⁻¹ < 1 := inv_lt_one_of_one_lt₀ hρ
  set d := ∑ i, (deg i : ℕ)
  set B : ℂ → ℂ := fun w ↦ infCoeff deg k φ l w w
  have hS (i : ι) : IsOpen {u : ℂ | ‖u ^ (deg i : ℕ)‖ < ρ} :=
    isOpen_lt (continuous_norm.comp (continuous_pow _)) continuous_const
  have hB (w₀ : ℂ) (hw₀ : ρ⁻¹ < ‖w₀‖) : DifferentiableAt ℂ B w₀ := by
    have hw₀0 : w₀ ≠ 0 := norm_pos_iff.1 ((inv_pos.2 hρ0).trans hw₀)
    have heq : (fun w ↦ infCoeff deg k φ l w₀ w) =ᶠ[𝓝 w₀] B := by
      filter_upwards [isOpen_ne.mem_nhds hw₀0] with w hw
      exact infCoeff_eq deg k φ l hw₀0 hw hw
    refine DifferentiableAt.congr_of_eventuallyEq ?_ heq.symm
    refine differentiableAt_coeff_prod_X_sub_C _ _ (fun ij _ ↦ ?_) l
    have hk := differentiableAt_kroot (deg ij.1) (w₁ := w₀) (w := w₀)
      (by rw [div_self hw₀0]; exact Complex.one_mem_slitPlane)
    have hne := zeta_pow_mul_kroot_ne_zero (deg ij.1).ne_zero ij.2 hw₀0 hw₀0
    have hφd : DifferentiableAt ℂ (φ ij.1)
        (Kummer.zeta (deg ij.1) ^ (ij.2 : ℕ) * kroot (deg ij.1) w₀ w₀)⁻¹ := by
      refine (hφ ij.1).differentiableAt ((hS ij.1).mem_nhds ?_)
      change ‖_‖ < ρ
      rw [norm_pow_inv_zeta_pow_mul_kroot (deg ij.1).ne_zero ij.2 hw₀0 hw₀0]
      exact inv_lt_of_inv_lt₀ hρ0 hw₀
    exact (differentiableAt_pow k).mul (hφd.comp w₀ ((hk.const_mul _).inv hne))
  set E : ℂ → ℂ := fun w ↦ if ‖w‖ < ρ then A w else B w
  have hEA (w : ℂ) (h : ‖w‖ < ρ) : E w = A w := if_pos h
  have hEB (w : ℂ) (h : ρ⁻¹ < ‖w‖) : E w = B w := by
    by_cases h' : ‖w‖ < ρ
    · rw [hEA w h']
      exact hAB w ⟨h, h'⟩
    · exact if_neg h'
  have hE : Differentiable ℂ E := by
    intro w₀
    by_cases h : ‖w₀‖ < ρ
    · have hn : ball (0 : ℂ) ρ ∈ 𝓝 w₀ := isOpen_ball.mem_nhds (mem_ball_zero_iff.2 h)
      refine (hA.differentiableAt hn).congr_of_eventuallyEq ?_
      filter_upwards [hn] with w hw using hEA w (mem_ball_zero_iff.1 hw)
    · have h' : ρ⁻¹ < ‖w₀‖ := hρi.trans (hρ.trans_le (not_lt.1 h))
      refine (hB w₀ h').congr_of_eventuallyEq ?_
      filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds h'] with w hw
        using hEB w hw
  -- the bound on the `φᵢ` on the closed unit disc
  have hφb (i : ι) : ∃ c, ∀ u ∈ closedBall (0 : ℂ) 1, ‖φ i u‖ ≤ c :=
    (isCompact_closedBall 0 1).exists_bound_of_continuousOn ((hφ i).continuousOn.mono
      fun u hu ↦ by
        change ‖u ^ (deg i : ℕ)‖ < ρ
        rw [norm_pow]
        exact (pow_le_one₀ (norm_nonneg u) (mem_closedBall_zero_iff.1 hu)).trans_lt hρ)
  choose c hc using hφb
  set C₀ := ∑ i, |c i|
  have hC₀ : 0 ≤ C₀ := Finset.sum_nonneg fun i _ ↦ abs_nonneg _
  have hφC (i : ι) (u : ℂ) (hu : ‖u‖ ≤ 1) : ‖φ i u‖ ≤ C₀ :=
    (hc i u (mem_closedBall_zero_iff.2 hu)).trans ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun i ↦ |c i|) (fun j _ ↦ abs_nonneg _) (Finset.mem_univ i)))
  have hBb (w : ℂ) (hw : 1 ≤ ‖w‖) : ‖B w‖ ≤ (1 + C₀) ^ d * (1 + ‖w‖) ^ (d * k) := by
    have hw0 : w ≠ 0 := norm_pos_iff.1 (zero_lt_one.trans_le hw)
    have hcard : (Finset.univ : Finset (Σ i, Fin (deg i))).card = d := by
      simp [d]
    have h₁ := norm_coeff_prod_X_sub_C_le (Finset.univ : Finset (Σ i, Fin (deg i)))
      (fun ij ↦ w ^ k * φ ij.1
        (Kummer.zeta (deg ij.1) ^ (ij.2 : ℕ) * kroot (deg ij.1) w w)⁻¹)
      (M := ‖w‖ ^ k * C₀) (by positivity) (fun ij _ ↦ ?_) l
    · rw [hcard] at h₁
      refine h₁.trans ?_
      rw [pow_mul', ← mul_pow]
      refine pow_le_pow_left₀ (by positivity) ?_ d
      have t₁ : 1 ≤ (1 + ‖w‖) ^ k := one_le_pow₀ (by linarith [norm_nonneg w])
      have t₂ : ‖w‖ ^ k ≤ (1 + ‖w‖) ^ k :=
        pow_le_pow_left₀ (norm_nonneg w) (by linarith) k
      nlinarith [mul_le_mul_of_nonneg_left t₂ hC₀]
    · rw [norm_mul, norm_pow]
      refine mul_le_mul_of_nonneg_left (hφC _ _ ?_) (by positivity)
      have h₂ := norm_pow_inv_zeta_pow_mul_kroot (deg ij.1).ne_zero ij.2 hw0 hw0
      rw [norm_pow] at h₂
      refine (pow_le_one_iff_of_nonneg (norm_nonneg _) (deg ij.1).ne_zero).1 ?_
      rw [h₂]
      exact inv_le_one_of_one_le₀ hw
  obtain ⟨C₂, hC₂⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn
    hE.continuous.continuousOn
  set C := max ((1 + C₀) ^ d) C₂
  have hbound (t : ℂ) : ‖E t‖ ≤ C * (1 + ‖t‖) ^ (d * k) := by
    have h₁ : 1 ≤ (1 + ‖t‖) ^ (d * k) := one_le_pow₀ (by linarith [norm_nonneg t])
    have hC : 0 ≤ C := (by positivity : (0 : ℝ) ≤ (1 + C₀) ^ d).trans (le_max_left _ _)
    by_cases ht : ‖t‖ ≤ 1
    · exact (hC₂ t (mem_closedBall_zero_iff.2 ht)).trans ((le_max_right _ _).trans
        (le_mul_of_one_le_right hC h₁))
    · rw [hEB t (hρi.trans (not_le.1 ht))]
      exact (hBb t (not_le.1 ht).le).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (by positivity))
  obtain ⟨p, hpdeg, hp⟩ := Differentiable.exists_polynomial_eq_of_norm_le_pow hE hbound
  have hp0 : p = 0 := by
    by_contra hp0
    have hlt := (natDegree_lt_iff_degree_lt hp0).2 hpdeg
    refine hp0 (eq_zero_of_natDegree_lt_card_of_eval_eq_zero p hw (fun ν ↦ ?_) ?_)
    · rw [← hp, hEA _ (mem_ball_zero_iff.1 (hwρ ν)), h0]
    · rw [Fintype.card_fin]
      omega
  intro w hw
  rw [← hEA w (mem_ball_zero_iff.1 hw), hp, hp0, eval_zero, Pi.zero_apply]

end Liouville

/-- A monic polynomial whose coefficients vanish except in degree `d` is `Xᵈ`. -/
lemma eq_X_pow_of_coeff_eq_zero {P : ℂ[X]} (hP : P.Monic) {d : ℕ}
    (h : ∀ l, l ≠ d → P.coeff l = 0) : P = X ^ d := by
  have hd : P.natDegree = d := by
    by_contra hne
    have := hP.coeff_natDegree
    rw [h _ hne] at this
    exact zero_ne_one this
  ext l
  rw [coeff_X_pow]
  split_ifs with hl
  · rw [hl, ← hd]
    exact hP.coeff_natDegree
  · exact h l hl

/-! ### Sections of the cap with a pole at infinity -/

namespace AnnulusDecomposition

variable {m : ℕ} {N₀ : (AnalyticSpace.complexAffineSpace.{u} (m + 1)).Opens}
  {W : FiniteEtaleOver (space N₀)} {G : Set (Cm.{u} m)} {ρ : ℝ}
  (D : AnnulusDecomposition W G ρ)

/-- Over a point of a disc in the annulus, the characteristic polynomial of a function on `W` is
the product over the sheets. -/
lemma charPolyFun_eq_prod_sheet {w₁ : ℂ} {ε : ℝ} (hε : ball w₁ ε ⊆ overlap ρ)
    {z : Cm.{u} m × ℂ} (hz : z ∈ discRegion G w₁ ε) (f : W.left → ℂ) :
    charPolyFun W f ((splitEquiv m).symm z) =
      ∏ ij : Σ i, Fin (D.deg i), (X - C (f (D.sheet hε ij.1 ij.2 z hz))) := by
  classical
  let e : (Σ i, Fin (D.deg i)) ≃ {w // w ∈ fiberFinset W ((splitEquiv m).symm z)} :=
    (D.sheetEquiv hε hz).trans (Equiv.subtypeEquivRight fun w ↦ by
      rw [mem_fiberFinset]; exact (splitEquiv m).eq_symm_apply.symm)
  rw [charPolyFun, ← Finset.prod_coe_sort]
  exact (Fintype.prod_equiv e _ _ fun ij ↦ rfl).symm

variable {N : (AnalyticSpace.complexAffineSpace.{u} (m + 1)).Opens} (h₀ : N₀ ≤ N)

/-- **Sections of the cap with a pole of order `≤ k` at infinity** over the open of `G × ℙ¹`
which is `V` in the chart `w` and `V'` in the chart `w' = w⁻¹`: pairs of a section `s` of `𝒜`
over `V` and functions `fᵢ`, holomorphic on `{(b, u') | (b, u'^{kᵢ}) ∈ V'}`, such that on the
`i`-th Kummer piece over the overlap `s(b, u) = u^{k kᵢ} fᵢ(b, u⁻¹)`, i.e. `s = wᵏ fᵢ`. For `k = 0`
these are the sections of the cap (`ComplexAnalytic.Cap.AnnulusDecomposition.mem_capPole_zero`).
-/
def capPole (k : ℕ) (V : (space N).Opens) (V' : Set (Cm.{u} m × ℂ)) :
    AddSubgroup (boundedSubring h₀ W V × (D.ι → Cm.{u} m × ℂ → ℂ)) where
  carrier := {s | (∀ i, DifferentiableOn ℂ (s.2 i) (Kummer.powMap (D.deg i) ⁻¹' V')) ∧
    ∀ i, ∀ z ∈ D.pieceSet (preim h₀ W V) i, invCoord z ∈ Kummer.powMap (D.deg i) ⁻¹' V' →
      D.kummerVal s.1.1 i z = z.2 ^ (k * D.deg i) * s.2 i (invCoord z)}
  add_mem' {s t} hs ht := ⟨fun i ↦ (hs.1 i).add (ht.1 i), fun i z hz hz' ↦ by
    change D.kummerVal (s.1.1 + t.1.1) i z = _ * (s.2 i _ + t.2 i _)
    rw [D.kummerVal_add hz, hs.2 i z hz hz', ht.2 i z hz hz', mul_add]⟩
  zero_mem' := ⟨fun _ ↦ differentiableOn_const 0, fun i z _ _ ↦ by
    change D.kummerVal (0 : W.left.presheaf.obj (op (preim h₀ W V))) i z = _ * 0
    rw [D.kummerVal_zero, mul_zero]⟩
  neg_mem' {s} hs := ⟨fun i ↦ (hs.1 i).neg, fun i z hz hz' ↦ by
    change D.kummerVal (-s.1.1) i z = _ * -s.2 i _
    rw [D.kummerVal_neg hz, hs.2 i z hz hz', mul_neg]⟩

variable {h₀} {k : ℕ} {V : (space N).Opens} {V' : Set (Cm.{u} m × ℂ)}
  {s : boundedSubring h₀ W V × (D.ι → Cm.{u} m × ℂ → ℂ)}

lemma mem_capPole_iff :
    s ∈ D.capPole h₀ k V V' ↔ (∀ i, DifferentiableOn ℂ (s.2 i) (Kummer.powMap (D.deg i) ⁻¹' V')) ∧
      ∀ i, ∀ z ∈ D.pieceSet (preim h₀ W V) i, invCoord z ∈ Kummer.powMap (D.deg i) ⁻¹' V' →
        D.kummerVal s.1.1 i z = z.2 ^ (k * D.deg i) * s.2 i (invCoord z) :=
  Iff.rfl

/-- Sections of the cap with a pole of order `≤ 0` are sections of the cap. -/
lemma mem_capPole_zero : s ∈ D.capPole h₀ 0 V V' ↔ s ∈ D.capSubring h₀ V V' := by
  simp only [mem_capPole_iff, mem_capSubring_iff, zero_mul, pow_zero, one_mul]

/-- The product of sections with poles of order `≤ k` and `≤ k'` has a pole of order
`≤ k + k'`. -/
lemma mul_mem_capPole {k' : ℕ} {t : boundedSubring h₀ W V × (D.ι → Cm.{u} m × ℂ → ℂ)}
    (hs : s ∈ D.capPole h₀ k V V') (ht : t ∈ D.capPole h₀ k' V V') :
    s * t ∈ D.capPole h₀ (k + k') V V' :=
  ⟨fun i ↦ (hs.1 i).mul (ht.1 i), fun i z hz hz' ↦ by
    change D.kummerVal (s.1.1 * t.1.1) i z = _ * (s.2 i _ * t.2 i _)
    rw [D.kummerVal_mul hz, hs.2 i z hz hz', ht.2 i z hz hz', add_mul, pow_add]
    ring⟩

/-- Sections of the cap act on the sections with a pole of order `≤ k`. -/
lemma mul_mem_capPole_of_mem_capSubring {t : boundedSubring h₀ W V × (D.ι → Cm.{u} m × ℂ → ℂ)}
    (ht : t ∈ D.capSubring h₀ V V') (hs : s ∈ D.capPole h₀ k V V') :
    t * s ∈ D.capPole h₀ k V V' := by
  simpa using D.mul_mem_capPole ((D.mem_capPole_zero).2 ht) hs

/-! ### The evaluation -/

variable {M : ℕ} (w : Fin M → ℂ)

/-- **The evaluation** at the points `(b, wᵥ)` of the annulus: the values of a section `a` of `𝒪_W`
on the sheets `(i, j)` over `(b, wᵥ)`, indexed by `(ν, i, j)`. -/
def evalVec {O : W.left.Opens} (a : W.left.presheaf.obj (op O)) (b : Cm.{u} m) :
    Fin M × (Σ i, Fin (D.deg i)) → ℂ :=
  fun x ↦ D.sheetVal (w₁ := w x.1) a x.2.1 x.2.2 (b, w x.1)

/-- The evaluation takes values in `ℂ^{M ∑ kᵢ}`. -/
lemma card_evalIndex : Fintype.card (Fin M × (Σ i, Fin (D.deg i))) = M * ∑ i, (D.deg i : ℕ) := by
  simp

variable {w}

/-- The value of the evaluation is the value of the section at a point over `(b, wᵥ)`. -/
lemma exists_evalVec_eq (hw : ∀ ν, w ν ∈ overlap ρ) {b : Cm.{u} m} (hb : b ∈ G)
    (x : Fin M × (Σ i, Fin (D.deg i))) (hbV : (splitEquiv m).symm (b, w x.1) ∈ img V) :
    ∃ (y : W.left) (hy : y ∈ preim h₀ W V), pt W y = (splitEquiv m).symm (b, w x.1) ∧
      ∀ a : W.left.presheaf.obj (op (preim h₀ W V)), D.evalVec w a b x = W.left.eval y hy a := by
  obtain ⟨ε, hε0, hε⟩ := Metric.isOpen_iff.1 (isOpen_overlap ρ) _ (hw x.1)
  have hz : (b, w x.1) ∈ discRegion G (w x.1) ε := ⟨hb, mem_ball_self hε0⟩
  have hy : D.sheet hε x.2.1 x.2.2 _ hz ∈ preim h₀ W V := by
    rw [mem_preim_iff, D.pt_sheet]
    exact hbV
  refine ⟨_, hy, D.pt_sheet hε _ _ hz, fun a ↦ ?_⟩
  rw [← evalFun_of_mem _ hy, D.evalFun_sheet hε a _ _ hz]
  rfl

/-- **The evaluation is additive.** -/
lemma evalVec_add (hw : ∀ ν, w ν ∈ overlap ρ) {b : Cm.{u} m} (hb : b ∈ G)
    (x : Fin M × (Σ i, Fin (D.deg i))) (hbV : (splitEquiv m).symm (b, w x.1) ∈ img V)
    (a a' : W.left.presheaf.obj (op (preim h₀ W V))) :
    D.evalVec w (a + a') b x = D.evalVec w a b x + D.evalVec w a' b x := by
  obtain ⟨y, hy, -, h⟩ := D.exists_evalVec_eq hw hb x hbV
  rw [h, h, h, map_add]

/-- **The evaluation is multiplicative.** -/
lemma evalVec_mul (hw : ∀ ν, w ν ∈ overlap ρ) {b : Cm.{u} m} (hb : b ∈ G)
    (x : Fin M × (Σ i, Fin (D.deg i))) (hbV : (splitEquiv m).symm (b, w x.1) ∈ img V)
    (a a' : W.left.presheaf.obj (op (preim h₀ W V))) :
    D.evalVec w (a * a') b x = D.evalVec w a b x * D.evalVec w a' b x := by
  obtain ⟨y, hy, -, h⟩ := D.exists_evalVec_eq hw hb x hbV
  rw [h, h, h, map_mul]

/-- **The evaluation is `𝒪`-linear**: the evaluation of the pullback of a section `r` of `𝒪_N` is
the value of `r`. For `r` independent of `w` the evaluation is thus `𝒪_G`-linear. -/
lemma evalVec_pullback (hw : ∀ ν, w ν ∈ overlap ρ) {b : Cm.{u} m} (hb : b ∈ G)
    (x : Fin M × (Σ i, Fin (D.deg i))) (hbV : (splitEquiv m).symm (b, w x.1) ∈ img V)
    (r : (space N).presheaf.obj (op V)) :
    D.evalVec w (pullback h₀ W V r) b x = holFun r ((splitEquiv m).symm (b, w x.1)) := by
  obtain ⟨y, hy, hpt, h⟩ := D.exists_evalVec_eq hw hb x hbV
  rw [h, eval_pullback, hpt]

/-- The Kummer coordinates of the sheets over a point `(b, w₁)` of the overlap lying in `V`. -/
lemma sheetCoord_mem_pieceSet {w₁ : ℂ} (hw₁ : w₁ ∈ overlap ρ) {b : Cm.{u} m} (hb : b ∈ G)
    (hbV : (splitEquiv m).symm (b, w₁) ∈ img V) (i : D.ι) (j : ℕ) :
    sheetCoord (D.deg i) j w₁ (b, w₁) ∈ D.pieceSet (preim h₀ W V) i := by
  obtain ⟨ε, hε0, hε⟩ := Metric.isOpen_iff.1 (isOpen_overlap ρ) _ hw₁
  have hz : (b, w₁) ∈ discRegion G w₁ ε := ⟨hb, mem_ball_self hε0⟩
  refine ⟨sheetCoord_mem_base hε (D.deg i) j hz, ?_⟩
  change D.sheet hε i j _ hz ∈ preim h₀ W V
  rw [mem_preim_iff, D.pt_sheet]
  exact hbV

/-- **The evaluation commutes with restriction.** -/
lemma evalVec_map {V₂ : (space N).Opens} (h : V₂ ≤ V) (hw : ∀ ν, w ν ∈ overlap ρ)
    {b : Cm.{u} m} (hb : b ∈ G) (x : Fin M × (Σ i, Fin (D.deg i)))
    (hbV : (splitEquiv m).symm (b, w x.1) ∈ img V₂) (a : W.left.presheaf.obj (op (preim h₀ W V))) :
    D.evalVec w (W.left.presheaf.map (homOfLE (preim_mono h₀ W h)).op a) b x =
      D.evalVec w a b x :=
  D.kummerVal_map _ (D.sheetCoord_mem_pieceSet (hw x.1) hb hbV x.2.1 x.2.2)

/-- **The evaluation is holomorphic** in `b`. -/
theorem differentiableOn_evalVec (hGo : IsOpen G) (hw : ∀ ν, w ν ∈ overlap ρ)
    (a : W.left.presheaf.obj (op (preim h₀ W V))) (x : Fin M × (Σ i, Fin (D.deg i))) :
    DifferentiableOn ℂ (fun b ↦ D.evalVec w a b x)
      {b | b ∈ G ∧ (splitEquiv m).symm (b, w x.1) ∈ img V} := by
  obtain ⟨ε, hε0, hε⟩ := Metric.isOpen_iff.1 (isOpen_overlap ρ) _ (hw x.1)
  exact (D.differentiableOn_sheetVal_preim hε h₀ hGo a x.2.1 x.2.2).comp
    ((differentiable_id.prodMk (differentiable_const _)).differentiableOn)
    fun b hb ↦ ⟨⟨hb.1, mem_ball_self hε0⟩, hb.2⟩

/-! ### Injectivity of the evaluation -/

/-- The value of a section of the cap with a pole of order `≤ k` on the `(i, j)`-th sheet over a
point `(b, w₁)` of the overlap, in terms of the chart at infinity. -/
lemma sheetVal_eq_of_mem_capPole {U : Set (Cm.{u} m)} (hUG : U ⊆ G)
    (hV : ∀ x, x ∈ img V ↔ splitEquiv m x ∈ U ×ˢ ball (0 : ℂ) ρ)
    (hs : s ∈ D.capPole h₀ k V (U ×ˢ ball 0 ρ)) {b : Cm.{u} m} (hb : b ∈ U) {w₁ : ℂ}
    (hw₁ : w₁ ∈ overlap ρ) (i : D.ι) (j : ℕ) :
    D.sheetVal (w₁ := w₁) s.1.1 i j (b, w₁) =
      w₁ ^ k * s.2 i (b, (Kummer.zeta (D.deg i) ^ j * kroot (D.deg i) w₁ w₁)⁻¹) := by
  have hρ0 : 0 < ρ := pos_of_mem_overlap hw₁
  have hw0 : w₁ ≠ 0 := ne_zero_of_mem_overlap hρ0 hw₁
  have hmem := D.sheetCoord_mem_pieceSet (h₀ := h₀) hw₁ (hUG hb) (by
    rw [hV, Homeomorph.apply_symm_apply]
    exact ⟨hb, mem_ball_zero_iff.2 hw₁.2⟩) i j
  have hmem' : invCoord (sheetCoord (D.deg i) j w₁ (b, w₁)) ∈
      Kummer.powMap (D.deg i) ⁻¹' (U ×ˢ ball 0 ρ) := by
    refine ⟨hb, mem_ball_zero_iff.2 ?_⟩
    change ‖((Kummer.zeta (D.deg i) ^ j * kroot (D.deg i) w₁ w₁)⁻¹) ^ (D.deg i : ℕ)‖ < ρ
    rw [norm_pow_inv_zeta_pow_mul_kroot (D.deg i).ne_zero j hw0 hw0]
    exact inv_lt_of_inv_lt₀ hρ0 hw₁.1
  refine (hs.2 i _ hmem hmem').trans ?_
  change (Kummer.zeta (D.deg i) ^ j * kroot (D.deg i) w₁ w₁) ^ (k * D.deg i) * _ = _
  rw [mul_comm k, pow_mul, zeta_pow_mul_kroot_pow (D.deg i).ne_zero j hw0 hw0]
  rfl

/-- **Injectivity of the evaluation**, pointwise: let `s` be a section of the cap with a pole of
order `≤ k` at infinity over `U × ℙ¹`, and let `w₀, …, w_{M-1}` be distinct points of the annulus
with `M > k ∑ kᵢ`. If the values of `s` on all sheets over the points `(b, wᵥ)` vanish, then `s`
vanishes over `{b} × ℙ¹`.

For fixed `b`, the coefficients of the characteristic polynomial of `s` are holomorphic in `w`,
and have a pole of order `≤ k ∑ kᵢ` at infinity; so they are polynomials of degree `≤ k ∑ kᵢ` in
`w` vanishing at the `M` points `wᵥ`, and the characteristic polynomial is `T^{∑ kᵢ}`. -/
theorem eq_zero_of_evalVec_eq_zero [T2Space W.left] (hD : HasThinComplement N N₀)
    (hA : ∀ x ∈ annulusRegion G ρ, x ∈ N₀) (hρ : 1 < ρ) {U : Set (Cm.{u} m)} (hUG : U ⊆ G)
    (hV : ∀ x, x ∈ img V ↔ splitEquiv m x ∈ U ×ˢ ball (0 : ℂ) ρ)
    (hM : (∑ i, (D.deg i : ℕ)) * k < M) (hw : Function.Injective w)
    (hwρ : ∀ ν, w ν ∈ overlap ρ) (hs : s ∈ D.capPole h₀ k V (U ×ˢ ball 0 ρ)) {b : Cm.{u} m}
    (hb : b ∈ U) (h0 : D.evalVec w s.1.1 b = 0) :
    (∀ y ∈ preim h₀ W V, (splitEquiv m (pt W y)).1 = b → evalFun s.1.1 y = 0) ∧
      ∀ i u, ‖u ^ (D.deg i : ℕ)‖ < ρ → s.2 i (b, u) = 0 := by
  classical
  have hρ0 : 0 < ρ := zero_lt_one.trans hρ
  set d := ∑ i, (D.deg i : ℕ)
  have hmemV (w' : ℂ) (hw' : ‖w'‖ < ρ) : (splitEquiv m).symm (b, w') ∈ img V := by
    rw [hV, Homeomorph.apply_symm_apply]
    exact ⟨hb, mem_ball_zero_iff.2 hw'⟩
  have hmemN (w' : ℂ) (hw' : w' ∈ overlap ρ) : (splitEquiv m).symm (b, w') ∈ N₀ :=
    hA _ (by
      rw [annulusRegion, mem_preimage, Homeomorph.apply_symm_apply]
      exact ⟨hUG hb, hw'⟩)
  have hchar (w' : ℂ) (hw' : w' ∈ overlap ρ) :
      charPolyFun W (evalFun s.1.1) ((splitEquiv m).symm (b, w')) =
        ∏ ij : Σ i, Fin (D.deg i), (X - C (D.sheetVal (w₁ := w') s.1.1 ij.1 ij.2 (b, w'))) := by
    obtain ⟨ε, hε0, hε⟩ := Metric.isOpen_iff.1 (isOpen_overlap ρ) _ hw'
    have hz : (b, w') ∈ discRegion G w' ε := ⟨hUG hb, mem_ball_self hε0⟩
    rw [D.charPolyFun_eq_prod_sheet hε hz]
    exact Finset.prod_congr rfl fun ij _ ↦ by rw [D.evalFun_sheet hε]
  choose r hr using fun l ↦ exists_coeff_charPolyFun hD s.1.2 l
  set φ : D.ι → ℂ → ℂ := fun i u ↦ s.2 i (b, u)
  have hφ (i : D.ι) : DifferentiableOn ℂ (φ i) {u | ‖u ^ (D.deg i : ℕ)‖ < ρ} :=
    (hs.1 i).comp ((differentiable_const b).prodMk differentiable_id).differentiableOn
      fun u hu ↦ ⟨hb, mem_ball_zero_iff.2 hu⟩
  have hvan (l : ℕ) (hl : l ≠ d) :
      EqOn (fun w' ↦ holFun (r l) ((splitEquiv m).symm (b, w'))) 0 (ball 0 ρ) := by
    refine eqOn_zero_of_infCoeff (φ := φ) (l := l) hρ hφ ?_ (fun w' hw' ↦ ?_) hM hw
      (fun ν ↦ mem_ball_zero_iff.2 (hwρ ν).2) fun ν ↦ ?_
    · exact (differentiableOn_holFun (r l)).comp (differentiable_splitEquiv_symm.comp
        ((differentiable_const b).prodMk differentiable_id)).differentiableOn
        fun w' hw' ↦ hmemV w' (mem_ball_zero_iff.1 hw')
    · rw [hr l _ (hmemV w' hw'.2) (hmemN w' hw'), hchar w' hw', infCoeff]
      refine congrArg (fun P : ℂ[X] ↦ P.coeff l) (Finset.prod_congr rfl fun ij _ ↦ ?_)
      rw [D.sheetVal_eq_of_mem_capPole hUG hV hs hb hw' ij.1 ij.2]
    · rw [hr l _ (hmemV _ (hwρ ν).2) (hmemN _ (hwρ ν)), hchar _ (hwρ ν)]
      have h₁ (ij : Σ i, Fin (D.deg i)) :
          D.sheetVal (w₁ := w ν) s.1.1 ij.1 ij.2 (b, w ν) = 0 :=
        congrFun h0 (ν, ij)
      simp only [h₁, map_zero, sub_zero, Finset.prod_const, Finset.card_univ,
        Fintype.card_sigma, Fintype.card_fin, coeff_X_pow]
      exact if_neg hl
  have part₁ (y : W.left) (hy : y ∈ preim h₀ W V) (hyb : (splitEquiv m (pt W y)).1 = b) :
      evalFun s.1.1 y = 0 := by
    have hyV : pt W y ∈ img V := (mem_preim_iff h₀ W).1 hy
    set w' := (splitEquiv m (pt W y)).2
    have hx : pt W y = (splitEquiv m).symm (b, w') :=
      (splitEquiv m).eq_symm_apply.2 (Prod.ext hyb rfl)
    have hw' : w' ∈ ball (0 : ℂ) ρ := (((hV _).1 hyV).2)
    have hP : charPolyFun W (evalFun s.1.1) (pt W y) = X ^ d := by
      refine eq_X_pow_of_coeff_eq_zero (monic_charPolyFun W (evalFun s.1.1) _) fun l hl ↦ ?_
      rw [← hr l _ hyV (pt_mem W y), hx]
      exact hvan l hl hw'
    have := eval_charPolyFun W (evalFun s.1.1) (rfl : pt W y = pt W y)
    rw [hP, eval_pow, eval_X] at this
    exact pow_eq_zero_iff'.1 this |>.1
  refine ⟨part₁, fun i u hu ↦ ?_⟩
  -- the component at infinity vanishes near `u = 1`, hence everywhere
  have hS : IsOpen {u : ℂ | ‖u ^ (D.deg i : ℕ)‖ < ρ} :=
    isOpen_lt (continuous_norm.comp (continuous_pow _)) continuous_const
  have hconn : IsPreconnected {u : ℂ | ‖u ^ (D.deg i : ℕ)‖ < ρ} := by
    refine (StarConvex.isPathConnected (a := 0) (fun y hy a c ha hc _ ↦ ?_) ?_).isConnected
      |>.isPreconnected
    · change ‖(a • (0 : ℂ) + c • y) ^ (D.deg i : ℕ)‖ < ρ
      change ‖y ^ (D.deg i : ℕ)‖ < ρ at hy
      rw [smul_zero, zero_add, norm_pow, norm_smul, mul_pow]
      rw [norm_pow] at hy
      have h₁ : ‖c‖ ^ (D.deg i : ℕ) ≤ 1 := pow_le_one₀ (norm_nonneg _) (by
        rw [Real.norm_of_nonneg hc]
        linarith)
      calc ‖c‖ ^ (D.deg i : ℕ) * ‖y‖ ^ (D.deg i : ℕ) ≤ 1 * ‖y‖ ^ (D.deg i : ℕ) :=
            mul_le_mul_of_nonneg_right h₁ (by positivity)
        _ < ρ := by rwa [one_mul]
    · change ‖(0 : ℂ) ^ (D.deg i : ℕ)‖ < ρ
      rw [zero_pow (D.deg i).ne_zero, norm_zero]
      exact hρ0
  have hT : IsOpen {u : ℂ | u ^ (D.deg i : ℕ) ∈ overlap ρ} :=
    (isOpen_overlap ρ).preimage (continuous_pow _)
  have h1T : (1 : ℂ) ∈ {u : ℂ | u ^ (D.deg i : ℕ) ∈ overlap ρ} := by
    change 1 ^ (D.deg i : ℕ) ∈ overlap ρ
    rw [one_pow]
    exact ⟨by rw [norm_one]; exact inv_lt_one_of_one_lt₀ hρ, by rw [norm_one]; exact hρ⟩
  have hT0 : ∀ v ∈ {u : ℂ | u ^ (D.deg i : ℕ) ∈ overlap ρ}, φ i v = 0 := by
    intro v hv
    have hv0 : v ≠ 0 := by
      rintro rfl
      exact ne_zero_of_mem_overlap hρ0 hv (zero_pow (D.deg i).ne_zero)
    have hvi : (v⁻¹) ^ (D.deg i : ℕ) ∈ overlap ρ := by
      rw [inv_pow]
      exact inv_mem_overlap hρ0 hv
    have hzbase : (b, v⁻¹) ∈ KummerAnnulus.base G ρ⁻¹ ρ (D.deg i) := by
      refine ⟨hUG hb, ?_⟩
      change ρ⁻¹ < ‖v⁻¹‖ ^ (D.deg i : ℕ) ∧ ‖v⁻¹‖ ^ (D.deg i : ℕ) < ρ
      rw [← norm_pow]
      exact hvi
    have hzO : D.toFun ⟨i, ⟨(b, v⁻¹), hzbase⟩⟩ ∈ preim h₀ W V := by
      rw [mem_preim_iff, D.pt_toFun]
      exact hmemV _ hvi.2
    have h₁ := hs.2 i (b, v⁻¹) ⟨hzbase, hzO⟩ ⟨hb, by
      change (v⁻¹)⁻¹ ^ (D.deg i : ℕ) ∈ ball (0 : ℂ) ρ
      rw [inv_inv, mem_ball_zero_iff]
      exact hv.2⟩
    rw [D.kummerVal_of_mem _ _ hzbase, part₁ _ hzO (by
      rw [D.pt_toFun, Homeomorph.apply_symm_apply])] at h₁
    change 0 = (v⁻¹) ^ (k * D.deg i) * s.2 i (b, v⁻¹⁻¹) at h₁
    rw [inv_inv] at h₁
    exact (mul_eq_zero.1 h₁.symm).resolve_left (pow_ne_zero _ (inv_ne_zero hv0))
  have := ((hφ i).analyticOnNhd hS).eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn
    (by
      change ‖(1 : ℂ) ^ (D.deg i : ℕ)‖ < ρ
      rw [one_pow, norm_one]
      exact hρ)
    (Filter.eventually_of_mem (hT.mem_nhds h1T) hT0)
  exact this hu

/-- **Injectivity of the evaluation**: a section `s` of the cap with a pole of order `≤ k` at
infinity over `U × ℙ¹` whose values on the sheets over the points `(b, wᵥ)`, for `b ∈ U`,
vanish is zero, provided the `M` points `wᵥ` of the annulus are distinct and `M > k ∑ kᵢ`. -/
theorem eq_zero_of_forall_evalVec_eq_zero [T2Space W.left] (hD : HasThinComplement N N₀)
    (hA : ∀ x ∈ annulusRegion G ρ, x ∈ N₀) (hρ : 1 < ρ) {U : Set (Cm.{u} m)} (hUG : U ⊆ G)
    (hV : ∀ x, x ∈ img V ↔ splitEquiv m x ∈ U ×ˢ ball (0 : ℂ) ρ)
    (hM : (∑ i, (D.deg i : ℕ)) * k < M) (hw : Function.Injective w)
    (hwρ : ∀ ν, w ν ∈ overlap ρ) (hs : s ∈ D.capPole h₀ k V (U ×ˢ ball 0 ρ))
    (h0 : ∀ b ∈ U, D.evalVec w s.1.1 b = 0) :
    s.1 = 0 ∧ ∀ i, EqOn (s.2 i) 0 (Kummer.powMap (D.deg i) ⁻¹' (U ×ˢ ball 0 ρ)) := by
  refine ⟨Subtype.ext (eq_of_forall_eval_eq (isLocallyOpenInAffine_left W) fun y hy ↦ ?_),
    fun i x hx ↦ ?_⟩
  · have hb := ((hV _).1 ((mem_preim_iff h₀ W).1 hy)).1
    have := (D.eq_zero_of_evalVec_eq_zero hD hA hρ hUG hV hM hw hwρ hs hb (h0 _ hb)).1 y hy rfl
    rw [evalFun_of_mem _ hy] at this
    rw [this]
    exact (map_zero _).symm
  · exact (D.eq_zero_of_evalVec_eq_zero hD hA hρ hUG hV hM hw hwρ hs hx.1 (h0 _ hx.1)).2 i x.2
      (mem_ball_zero_iff.1 hx.2)

end AnnulusDecomposition

end

end ComplexAnalytic.Cap
