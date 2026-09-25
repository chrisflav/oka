/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.ES.CapExtension.Combine
import Oka.Statement

/-!
# Lowering the order of the pole of the sections of the cap

Keep the notation of `Oka/Analytification/RET/ES/CapExtension/Setup.lean`. A section `t` of the cap
with a pole of order `≤ n + 1` at infinity has a pole of order `≤ n` iff its functions at infinity
`fᵢ(b, u') = ∑_{j < kᵢ} u'ʲ cᵢⱼ(b, u'^{kᵢ})` are divisible by `u'^{kᵢ}`, i.e. iff the holomorphic
functions `b ↦ cᵢⱼ(b, 0)` on the base vanish. So the sections with a pole of order `≤ n` are the
kernel of an `𝒪`-linear map from the sections with a pole of order `≤ n + 1` to `𝒪^{∑ kᵢ}`, and
local finiteness passes from `n + 1` to `n` by Oka's theorem
(`ComplexAnalytic.Cap.AnnulusDecomposition.capLocallyFinite_of_succ`).

The division by `w'` is `ComplexAnalytic.Cap.exists_eq_snd_mul`: a holomorphic function on an
open subset of `E × ℂ` vanishing on `{w' = 0}` is `w'` times a holomorphic function, by the Schwarz
lemma and the Riemann extension theorem.
-/

open CategoryTheory Opposite Topology TopologicalSpace Set Filter Metric

universe u

namespace ComplexAnalytic.Cap

noncomputable section

/-! ### Division by the last coordinate -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- **Division by `w`**: a holomorphic function on an open `V ⊆ E × ℂ` vanishing on `{w = 0}` is
`w` times a holomorphic function on `V`. -/
theorem exists_eq_snd_mul {V : Set (E × ℂ)} (hV : IsOpen V) {f : E × ℂ → ℂ}
    (hf : DifferentiableOn ℂ f V) (h0 : ∀ x ∈ V, x.2 = 0 → f x = 0) :
    ∃ g : E × ℂ → ℂ, DifferentiableOn ℂ g V ∧ ∀ x ∈ V, f x = x.2 * g x := by
  have hpre : Kummer.powMap 1 ⁻¹' V = V := by
    ext x
    simp [Kummer.powMap]
  have hd : DifferentiableOn ℂ (fun x : E × ℂ ↦ f x / x.2)
      (Kummer.powMap 1 ⁻¹' V \ Prod.snd ⁻¹' {0}) := by
    rw [hpre]
    exact ((hf.mono sdiff_subset).mul (differentiable_snd.differentiableOn.inv
      fun x hx ↦ hx.2)).congr fun x _ ↦ div_eq_mul_inv _ _
  have hb : ∀ x ∈ V, x.2 = 0 → IsBoundedUnder (· ≤ ·)
      (𝓝[Kummer.powMap 1 ⁻¹' V \ Prod.snd ⁻¹' {0}] x) (fun x ↦ ‖f x / x.2‖) := by
    intro x₀ hx₀ hx₀0
    rw [hpre]
    have hc : ContinuousAt f x₀ := hf.continuousOn.continuousAt (hV.mem_nhds hx₀)
    have hf0 : f x₀ = 0 := h0 x₀ hx₀ hx₀0
    have hS : {x | ‖f x‖ < 1} ∩ V ∈ 𝓝 x₀ :=
      inter_mem (hc.norm.preimage_mem_nhds (Iio_mem_nhds (by rw [hf0, norm_zero]; exact one_pos)))
        (hV.mem_nhds hx₀)
    rw [← Prod.mk.eta (p := x₀), mem_nhds_prod_iff] at hS
    obtain ⟨U₀, hU₀, v, hv, hUv⟩ := hS
    obtain ⟨r, hr, hrv⟩ := Metric.mem_nhds_iff.1 hv
    rw [hx₀0] at hrv
    refine isBoundedUnder_of_eventually_le (a := 1 / r) ?_
    rw [eventually_nhdsWithin_iff]
    have hprod : U₀ ×ˢ ball (0 : ℂ) r ∈ 𝓝 x₀ := by
      rw [← Prod.mk.eta (p := x₀), hx₀0]
      exact prod_mem_nhds hU₀ (ball_mem_nhds 0 hr)
    filter_upwards [hprod] with x hx hxV
    obtain ⟨hx1, hx2⟩ := hx
    have hmem : ∀ w ∈ ball (0 : ℂ) r, (x.1, w) ∈ {x | ‖f x‖ < 1} ∩ V := fun w hw ↦
      hUv ⟨hx1, hrv hw⟩
    have hφ : DifferentiableOn ℂ (fun w ↦ f (x.1, w)) (ball 0 r) := fun w hw ↦
      ((hf _ (hmem w hw).2).differentiableAt (hV.mem_nhds (hmem w hw).2)).comp w
        ((differentiableAt_const _).prodMk differentiableAt_id) |>.differentiableWithinAt
    have hφ0 : f (x.1, 0) = 0 := h0 _ (hmem 0 (mem_ball_self hr)).2 rfl
    have hmaps : MapsTo (fun w ↦ f (x.1, w)) (ball 0 r) (closedBall (f (x.1, 0)) 1) :=
      fun w hw ↦ by
        rw [hφ0, mem_closedBall_zero_iff]
        exact (hmem w hw).1.le
    have hsch := Complex.dist_le_div_mul_dist_of_mapsTo_ball hφ hmaps hx2
    rw [hφ0, dist_zero_right, dist_zero_right] at hsch
    have hx20 : x.2 ≠ 0 := hxV.2
    change ‖f x / x.2‖ ≤ 1 / r
    rw [norm_div, div_le_iff₀ (norm_pos_iff.2 hx20)]
    exact hsch
  obtain ⟨F, hF, hFeq⟩ := Kummer.exists_differentiableOn_powMap_eqOn (k := 1) one_pos hV hd hb
  rw [hpre] at hF hFeq
  refine ⟨F, hF, fun x hx ↦ ?_⟩
  by_cases hx0 : x.2 = 0
  · rw [h0 x hx hx0, hx0, zero_mul]
  · rw [hFeq ⟨hx, hx0⟩]
    field_simp

/-- **The identity theorem on a disc**: holomorphic functions on `{‖w‖ < ρ}`, `ρ > 1`, which
agree on the annulus `{ρ⁻¹ < ‖w‖ < ρ}` agree at `0`. -/
theorem eq_at_zero_of_eqOn_annulus {ρ : ℝ} (hρ : 1 < ρ) {F G : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (ball 0 ρ)) (hG : DifferentiableOn ℂ G (ball 0 ρ))
    (h : ∀ w : ℂ, ρ⁻¹ < ‖w‖ → ‖w‖ < ρ → F w = G w) : F 0 = G 0 := by
  have hρ0 : 0 < ρ := zero_lt_one.trans hρ
  have h1 : (1 : ℂ) ∈ ball (0 : ℂ) ρ := by rw [mem_ball_zero_iff, norm_one]; exact hρ
  have hann : IsOpen {w : ℂ | ρ⁻¹ < ‖w‖ ∧ ‖w‖ < ρ} :=
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  have hmem : (1 : ℂ) ∈ {w : ℂ | ρ⁻¹ < ‖w‖ ∧ ‖w‖ < ρ} := by
    rw [mem_setOf_eq, norm_one]
    exact ⟨inv_lt_one_of_one_lt₀ hρ, hρ⟩
  refine (hF.analyticOnNhd isOpen_ball).eqOn_of_preconnected_of_eventuallyEq
    (hG.analyticOnNhd isOpen_ball) (convex_ball 0 ρ).isPreconnected h1 ?_
    (mem_ball_self hρ0)
  filter_upwards [hann.mem_nhds hmem] with w hw using h w hw.1 hw.2

namespace AnnulusDecomposition

open AnalyticSpace BoundedSections Complex.ProjectiveLineBundle
open KummerModel (splitEquiv)

variable {m : ℕ} {N N₀ : (AnalyticSpace.complexAffineSpace.{u} (m + 1)).Opens} (h₀ : N₀ ≤ N)
  {W : FiniteEtaleOver (space N₀)} {F : WeierstrassForm N N₀}
  (D : AnnulusDecomposition W F.G F.ρ) {n : ℕ}

/-! ### Multiplication by functions on the base -/

/-- A holomorphic function `r` on the base `B`, as a section of the cap over `B × ℙ¹`. -/
def baseCap {B : Set (Cm.{u} m)} (hB : IsOpen B) (r : Cm.{u} m → ℂ)
    (hr : DifferentiableOn ℂ r B) :
    boundedSubring h₀ W (tubeN N B hB) × (D.ι → Cm.{u} m × ℂ → ℂ) :=
  (algebraMapBounded h₀ W _ (OkaRing.ofDifferentiableOn (fun x ↦ r (baseOf x))
      (hr.comp differentiable_baseOf.differentiableOn fun _ hx ↦ (mem_img_iff.1 hx).2)),
    fun _ z ↦ r z.1)

lemma baseCap_mem {B : Set (Cm.{u} m)} (hB : IsOpen B) {r : Cm.{u} m → ℂ}
    (hr : DifferentiableOn ℂ r B) :
    D.baseCap h₀ hB r hr ∈ D.capSubring h₀ (tubeN N B hB) (B ×ˢ ball 0 F.ρ) :=
  D.algebraMap_mem_capSubring h₀ _ (g := fun z ↦ r z.1)
    (hr.comp differentiableOn_fst fun _ hz ↦ hz.1) fun b _ w _ hx _ ↦ by
      rw [holFun_ofDifferentiableOn _ hx]
      simp [baseOf]

lemma evalFun_baseCap_mul {B : Set (Cm.{u} m)} (hB : IsOpen B) {r : Cm.{u} m → ℂ}
    (hr : DifferentiableOn ℂ r B) (t : boundedSubring h₀ W (tubeN N B hB) ×
      (D.ι → Cm.{u} m × ℂ → ℂ)) {w : W.left} (hw : w ∈ preim h₀ W (tubeN N B hB)) :
    evalFun (D.baseCap h₀ hB r hr * t).1.1 w = r (baseOf (pt W w)) * evalFun t.1.1 w := by
  change evalFun (pullback h₀ W _ _ * t.1.1) w = _
  rw [evalFun_mul W _ _ hw, evalFun_pullback h₀ W _ hw,
    holFun_ofDifferentiableOn _ ((mem_preim_iff h₀ W).1 hw)]

/-! ### Raising and lowering the order of the pole -/

variable {V : (space N).Opens} {V' : Set (Cm.{u} m × ℂ)}

lemma ne_zero_of_mem_pieceSet {O : W.left.Opens} {i : D.ι} {z : Cm.{u} m × ℂ}
    (hz : z ∈ D.pieceSet O i) : z.2 ≠ 0 :=
  norm_pos_iff.1 (KummerAnnulus.pos_of_mem_base F.G (inv_nonneg.2 F.pos_ρ.le)
    (D.deg i).ne_zero hz.1)

/-- **Multiplying the functions at infinity by `u'^{kᵢ}`** raises the order of the pole by one. -/
lemma raise_mem {t : boundedSubring h₀ W V × (D.ι → Cm.{u} m × ℂ → ℂ)}
    (ht : t ∈ D.capPole h₀ n V V') :
    (t.1, fun i z ↦ z.2 ^ (D.deg i : ℕ) * t.2 i z) ∈ D.capPole h₀ (n + 1) V V' := by
  refine ⟨fun i ↦ ((differentiable_snd.pow _).differentiableOn).mul (ht.1 i),
    fun i z hz hz' ↦ ?_⟩
  have hz0 := D.ne_zero_of_mem_pieceSet hz
  change D.kummerVal t.1.1 i z = _
  rw [ht.2 i z hz hz']
  simp only [invCoord, inv_pow]
  rw [add_mul, one_mul, pow_add, mul_assoc, ← mul_assoc (z.2 ^ (D.deg i : ℕ)),
    mul_inv_cancel₀ (pow_ne_zero _ hz0), one_mul]

/-- **Dividing the functions at infinity by `u'^{kᵢ}`** lowers the order of the pole by one. -/
lemma lower_mem {t : boundedSubring h₀ W V × (D.ι → Cm.{u} m × ℂ → ℂ)}
    (ht : t ∈ D.capPole h₀ (n + 1) V V') (G : D.ι → Cm.{u} m × ℂ → ℂ)
    (hG : ∀ i, DifferentiableOn ℂ (G i) (Kummer.powMap (D.deg i) ⁻¹' V'))
    (htG : ∀ i, ∀ z ∈ Kummer.powMap (D.deg i) ⁻¹' V', t.2 i z = z.2 ^ (D.deg i : ℕ) * G i z) :
    (t.1, G) ∈ D.capPole h₀ n V V' := by
  refine ⟨hG, fun i z hz hz' ↦ ?_⟩
  have hz0 := D.ne_zero_of_mem_pieceSet hz
  change D.kummerVal t.1.1 i z = _
  rw [ht.2 i z hz hz', htG i _ hz']
  simp only [invCoord, inv_pow]
  rw [add_mul, one_mul, pow_add, mul_assoc, ← mul_assoc (z.2 ^ (D.deg i : ℕ)),
    mul_inv_cancel₀ (pow_ne_zero _ hz0), one_mul]

/-! ### Functions at infinity from values on `W` -/

/-- If the values on `W` of a section `t` of the cap are a combination of those of sections `sₗ`
over `V''`, then so are its functions at infinity over the annulus. -/
lemma snd_eq_sum_of_evalFun_eq {k : ℕ} {B V V'' : Set (Cm.{u} m)} (hB : IsOpen B)
    (hV : IsOpen V) {t : boundedSubring h₀ W (tubeN N V hV) × (D.ι → Cm.{u} m × ℂ → ℂ)}
    (ht : t ∈ D.capPole h₀ k (tubeN N V hV) (V ×ˢ ball 0 F.ρ)) {K : ℕ}
    {s : Fin K → boundedSubring h₀ W (tubeN N B hB) × (D.ι → Cm.{u} m × ℂ → ℂ)}
    (hs : ∀ l, s l ∈ D.capPole h₀ k (tubeN N B hB) (B ×ˢ ball 0 F.ρ))
    (e : Fin K → Cm.{u} m → ℂ) (hV''V : V'' ⊆ V) (hV''B : V'' ⊆ B)
    (hte : ∀ y ∈ preim h₀ W (tubeN N V hV), baseOf (pt W y) ∈ V'' →
      evalFun t.1.1 y = ∑ l, e l (baseOf (pt W y)) * evalFun (s l).1.1 y)
    (i : D.ι) {z : Cm.{u} m × ℂ} (hzG : z.1 ∈ F.G) (hz1 : z.1 ∈ V'')
    (hz2 : F.ρ⁻¹ < ‖z.2‖ ^ (D.deg i : ℕ)) (hz3 : ‖z.2‖ ^ (D.deg i : ℕ) < F.ρ) :
    t.2 i z = ∑ l, e l z.1 * (s l).2 i z := by
  have hpos : 0 < ‖z.2‖ ^ (D.deg i : ℕ) := (inv_pos.2 F.pos_ρ).trans hz2
  have hz0 : z.2 ≠ 0 := fun h ↦ by
    rw [h, norm_zero, zero_pow (D.deg i).ne_zero] at hpos
    exact lt_irrefl 0 hpos
  have hz'b : invCoord z ∈ KummerAnnulus.base F.G F.ρ⁻¹ F.ρ (D.deg i) := by
    refine KummerAnnulus.mem_base.2 ⟨hzG, ?_, ?_⟩
    · change F.ρ⁻¹ < ‖z.2⁻¹‖ ^ (D.deg i : ℕ)
      rw [norm_inv, inv_pow]
      exact (inv_lt_inv₀ F.pos_ρ hpos).2 hz3
    · change ‖z.2⁻¹‖ ^ (D.deg i : ℕ) < F.ρ
      rw [norm_inv, inv_pow]
      exact inv_lt_of_inv_lt₀ F.pos_ρ hz2
  have hbase : baseOf (pt W (D.toFun ⟨i, ⟨invCoord z, hz'b⟩⟩)) = z.1 := by
    change (splitEquiv m (pt W (D.toFun ⟨i, ⟨invCoord z, hz'b⟩⟩))).1 = z.1
    rw [D.splitEquiv_pt]
    rfl
  have hpre (O : Set (Cm.{u} m)) (hO : IsOpen O) (hzO : z.1 ∈ O) :
      D.toFun ⟨i, ⟨invCoord z, hz'b⟩⟩ ∈ preim h₀ W (tubeN N O hO) :=
    (mem_preim_iff h₀ W).2 (mem_img_iff.2 ⟨h₀ (pt_mem W _), by
      change baseOf _ ∈ O
      rw [hbase]
      exact hzO⟩)
  have hinv : invCoord (invCoord z) = z := by
    simp [invCoord]
  have hzV : invCoord (invCoord z) ∈ Kummer.powMap (D.deg i) ⁻¹' (V ×ˢ ball 0 F.ρ) := by
    rw [hinv]
    exact ⟨hV''V hz1, mem_ball_zero_iff.2 (by
      change ‖z.2 ^ (D.deg i : ℕ)‖ < F.ρ; rw [norm_pow]; exact hz3)⟩
  have hzB : invCoord (invCoord z) ∈ Kummer.powMap (D.deg i) ⁻¹' (B ×ˢ ball 0 F.ρ) := by
    rw [hinv]
    exact ⟨hV''B hz1, mem_ball_zero_iff.2 (by
      change ‖z.2 ^ (D.deg i : ℕ)‖ < F.ρ; rw [norm_pow]; exact hz3)⟩
  have h1 := ht.2 i (invCoord z) ⟨hz'b, hpre V hV (hV''V hz1)⟩ hzV
  have h3 := hte _ (hpre V hV (hV''V hz1)) (by rw [hbase]; exact hz1)
  rw [← D.kummerVal_of_mem t.1.1 i hz'b, h1, hbase] at h3
  have h4 : ∀ l, evalFun (s l).1.1 (D.toFun ⟨i, ⟨invCoord z, hz'b⟩⟩) =
      (invCoord z).2 ^ (k * D.deg i) * (s l).2 i (invCoord (invCoord z)) := fun l ↦ by
    rw [← D.kummerVal_of_mem _ i hz'b]
    exact (hs l).2 i (invCoord z) ⟨hz'b, hpre B hB (hV''B hz1)⟩ hzB
  simp only [h4, hinv] at h3
  have hc : (invCoord z).2 ^ (k * D.deg i) ≠ 0 := pow_ne_zero _ (inv_ne_zero hz0)
  refine mul_left_cancel₀ hc (h3.trans ?_)
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ ↦ by ring

lemma evalFun_sum_baseCap_mul {B : Set (Cm.{u} m)} (hB : IsOpen B) {K : ℕ}
    {r : Fin K → Cm.{u} m → ℂ} (hr : ∀ k, DifferentiableOn ℂ (r k) B)
    (t : Fin K → boundedSubring h₀ W (tubeN N B hB) × (D.ι → Cm.{u} m × ℂ → ℂ)) {w : W.left}
    (hw : w ∈ preim h₀ W (tubeN N B hB)) :
    evalFun (∑ k, D.baseCap h₀ hB (r k) (hr k) * t k).1.1 w =
      ∑ k, r k (baseOf (pt W w)) * evalFun (t k).1.1 w := by
  rw [Prod.fst_sum, AddSubmonoidClass.coe_finsetSum, evalFun_of_mem _ hw, map_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [← evalFun_of_mem _ hw, D.evalFun_baseCap_mul h₀ hB (hr k) (t k) hw]

/-- **Local finiteness of the sections of the cap passes from `n + 1` to `n`.** -/
theorem capLocallyFinite_of_succ {b : Cm.{u} m} (hn : D.CapLocallyFinite h₀ (n + 1) b) :
    D.CapLocallyFinite h₀ n b := by
  classical
  obtain ⟨B, hB, hBG, hbB, K, s, hs, hgen⟩ := hn
  have hV'o : IsOpen (B ×ˢ ball (0 : ℂ) F.ρ) := hB.prod isOpen_ball
  choose c hcd hceq using fun k i ↦ exists_coeff_eqOn (D.deg i).pos hV'o ((hs k).1 i)
  let eX := Fintype.equivFin (Σ i, Fin (D.deg i))
  let U₀ : TopologicalSpace.Opens (Cm.{u} m) := ⟨B, hB⟩
  have hB0 : ∀ y ∈ B, (y, (0 : ℂ)) ∈ B ×ˢ ball (0 : ℂ) F.ρ := fun y hy ↦
    ⟨hy, mem_ball_self F.pos_ρ⟩
  have hcol : ∀ k (q : Fin (Fintype.card (Σ i, Fin (D.deg i)))), DifferentiableOn ℂ
      (fun y ↦ c k (eX.symm q).1 (eX.symm q).2 (y, 0)) U₀ := fun k q ↦
    (hcd k _ _).comp (differentiableOn_id.prodMk (differentiableOn_const 0)) hB0
  let col : Fin K → Fin (Fintype.card (Σ i, Fin (D.deg i))) → OkaRing U₀ := fun k q ↦
    OkaRing.ofDifferentiableOn _ (hcol k q)
  obtain ⟨V₀, hV₀U₀, L, g, hbV₀, hrel, hgen'⟩ := oka' U₀ col b hbB
  have hV₀B : (V₀ : Set (Cm.{u} m)) ⊆ B := hV₀U₀
  have hV₀G : (V₀ : Set (Cm.{u} m)) ⊆ F.G := fun y hy ↦ hBG (hV₀B hy)
  let gf : Fin L → Fin K → Cm.{u} m → ℂ := fun l k ↦ (g l k).toGlobalFun _
  have hgf : ∀ l k, DifferentiableOn ℂ (gf l k) V₀ := fun l k ↦
    (g l k).differentiableOn_toGlobalFun
  have hrelp : ∀ l, ∀ y ∈ (V₀ : Set (Cm.{u} m)), ∀ i (j : Fin (D.deg i)),
      ∑ k, gf l k y * c k i j (y, 0) = 0 := by
    intro l y hy i j
    have := congrArg (OkaRing.evalHom hy) (hrel l (eX ⟨i, j⟩))
    simp only [map_sum, map_mul, map_zero, OkaRing.evalHom_restrict] at this
    refine (Finset.sum_congr rfl fun k _ ↦ ?_).trans this
    simp only [gf, col, OkaRing.evalHom_apply, OkaRing.ofDifferentiableOn_toFun,
      OkaRing.toGlobalFun_apply _ hy]
    rw [Equiv.symm_apply_apply]
  -- the restricted generators and the combinations given by the relations
  let sV : Fin K → boundedSubring h₀ W (tubeN N V₀ V₀.isOpen) × (D.ι → Cm.{u} m × ℂ → ℂ) :=
    fun k ↦ D.capRestrict h₀ (tubeN_mono hV₀B) (s k)
  have hsV : ∀ k, sV k ∈ D.capPole h₀ (n + 1) (tubeN N V₀ V₀.isOpen) (V₀ ×ˢ ball 0 F.ρ) :=
    fun k ↦ D.capRestrict_mem_capPole h₀ _ (prod_mono hV₀B subset_rfl) (hs k)
  let T : Fin L → boundedSubring h₀ W (tubeN N V₀ V₀.isOpen) × (D.ι → Cm.{u} m × ℂ → ℂ) :=
    fun l ↦ ∑ k, D.baseCap h₀ V₀.isOpen (gf l k) (hgf l k) * sV k
  have hT : ∀ l, T l ∈ D.capPole h₀ (n + 1) (tubeN N V₀ V₀.isOpen) (V₀ ×ˢ ball 0 F.ρ) :=
    fun l ↦ AddSubgroup.sum_mem _ fun k _ ↦
      D.mul_mem_capPole_of_mem_capSubring (D.baseCap_mem h₀ _ _) (hsV k)
  have hT2 : ∀ l i z, (T l).2 i z = ∑ k, gf l k z.1 * (s k).2 i z := fun l i z ↦ by
    simp only [T, Prod.snd_sum, Finset.sum_apply]
    rfl
  -- division by `w'`
  have hdiv : ∀ l i (j : Fin (D.deg i)), ∃ d : Cm.{u} m × ℂ → ℂ,
      DifferentiableOn ℂ d ((V₀ : Set (Cm.{u} m)) ×ˢ ball (0 : ℂ) F.ρ) ∧
      ∀ x ∈ (V₀ : Set (Cm.{u} m)) ×ˢ ball (0 : ℂ) F.ρ,
        ∑ k, gf l k x.1 * c k i j x = x.2 * d x := fun l i j ↦
    exists_eq_snd_mul (V₀.isOpen.prod isOpen_ball)
      (DifferentiableOn.fun_sum fun k _ ↦ ((hgf l k).comp differentiableOn_fst
        fun _ hx ↦ hx.1).mul ((hcd k i j).mono (prod_mono hV₀B subset_rfl)))
      fun x hx hx0 ↦ by
        have hx' : x = (x.1, 0) := Prod.ext rfl hx0
        rw [hx']
        exact hrelp l x.1 hx.1 i j
  choose d hdd hdeq using hdiv
  let Gl : Fin L → D.ι → Cm.{u} m × ℂ → ℂ := fun l i z ↦
    ∑ j : Fin (D.deg i), z.2 ^ (j : ℕ) * d l i j (Kummer.powMap (D.deg i) z)
  have hTG : ∀ l i, ∀ z ∈ Kummer.powMap (D.deg i) ⁻¹' ((V₀ : Set (Cm.{u} m)) ×ˢ ball 0 F.ρ),
      (T l).2 i z = z.2 ^ (D.deg i : ℕ) * Gl l i z := by
    intro l i z hz
    have hzB : z ∈ Kummer.powMap (D.deg i) ⁻¹' (B ×ˢ ball (0 : ℂ) F.ρ) := ⟨hV₀B hz.1, hz.2⟩
    rw [hT2]
    have e3 : ∀ k, gf l k z.1 * (s k).2 i z = ∑ j : Fin (D.deg i), z.2 ^ (j : ℕ) *
        (gf l k z.1 * c k i j (Kummer.powMap (D.deg i) z)) := fun k ↦ by
      rw [hceq k i hzB, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ ↦ by ring
    rw [Finset.sum_congr rfl fun k _ ↦ e3 k, Finset.sum_comm]
    simp only [Gl, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    have h := hdeq l i j _ hz
    simp only [Kummer.powMap_apply] at h ⊢
    rw [← Finset.mul_sum, h]
    ring
  let T' : Fin L → boundedSubring h₀ W (tubeN N V₀ V₀.isOpen) × (D.ι → Cm.{u} m × ℂ → ℂ) :=
    fun l ↦ ((T l).1, Gl l)
  have hT' : ∀ l, T' l ∈ D.capPole h₀ n (tubeN N V₀ V₀.isOpen) (V₀ ×ˢ ball 0 F.ρ) :=
    fun l ↦ D.lower_mem h₀ (hT l) (Gl l)
      (fun i ↦ Kummer.differentiableOn_sum_pow_mul_comp_powMap (hdd l i)) (hTG l)
  refine ⟨V₀, V₀.isOpen, hV₀G, hbV₀, L, T', hT', fun b' hb' V hV hVV₀ hb'V t ht ↦ ?_⟩
  have htr := D.raise_mem h₀ ht
  obtain ⟨V'', hV''V, hV''o, hb'V'', e, he, hte⟩ :=
    hgen b' (hV₀B hb') V hV (hVV₀.trans hV₀B) hb'V _ htr
  have hV''B : V'' ⊆ B := hV''V.trans (hVV₀.trans hV₀B)
  choose ct hctd hcteq using fun i ↦ exists_coeff_eqOn (D.deg i).pos
    (hV.prod isOpen_ball) (ht.1 i)
  -- the values at `w' = 0` of the coefficients of the combination vanish
  have hΦ : ∀ y ∈ V'', ∀ i (j : Fin (D.deg i)), ∑ k, e k y * c k i j (y, 0) = 0 := by
    intro y hy i j
    have hann : IsOpen {w : ℂ | F.ρ⁻¹ < ‖w‖ ∧ ‖w‖ < F.ρ} :=
      (isOpen_lt continuous_const continuous_norm).inter
        (isOpen_lt continuous_norm continuous_const)
    have hAB : ∀ x ∈ V'' ×ˢ {w : ℂ | F.ρ⁻¹ < ‖w‖ ∧ ‖w‖ < F.ρ}, x ∈ B ×ˢ ball (0 : ℂ) F.ρ :=
      fun x hx ↦ ⟨hV''B hx.1, mem_ball_zero_iff.2 hx.2.2⟩
    have hAV : ∀ x ∈ V'' ×ˢ {w : ℂ | F.ρ⁻¹ < ‖w‖ ∧ ‖w‖ < F.ρ}, x ∈ V ×ˢ ball (0 : ℂ) F.ρ :=
      fun x hx ↦ ⟨hV''V hx.1, mem_ball_zero_iff.2 hx.2.2⟩
    have key := eqOn_of_coeff (D.deg i).pos (hV''o.prod hann)
      (g := fun j x ↦ ∑ k, e k x.1 * c k i j x) (g' := fun j x ↦ x.2 * ct i j x)
      (fun j ↦ (DifferentiableOn.fun_sum fun k _ ↦ ((he k).comp differentiableOn_fst
        fun _ hx ↦ hx.1).mul ((hcd k i j).mono hAB)).continuousOn)
      (fun j ↦ (differentiableOn_snd.mul ((hctd i j).mono hAV)).continuousOn)
      (fun z hz ↦ ?_) j
    · have hF : DifferentiableOn ℂ (fun w ↦ ∑ k, e k y * c k i j (y, w)) (ball 0 F.ρ) :=
        DifferentiableOn.fun_sum fun k _ ↦ (differentiableOn_const _).mul ((hcd k i j).comp
          ((differentiableOn_const y).prodMk differentiableOn_id) fun w hw ↦ ⟨hV''B hy, hw⟩)
      have hG : DifferentiableOn ℂ (fun w ↦ w * ct i j (y, w)) (ball 0 F.ρ) :=
        differentiableOn_id.mul ((hctd i j).comp
          ((differentiableOn_const y).prodMk differentiableOn_id) fun w hw ↦ ⟨hV''V hy, hw⟩)
      have := eq_at_zero_of_eqOn_annulus F.one_lt_ρ hF hG fun w h1 h2 ↦
        key (show (y, w) ∈ V'' ×ˢ {w : ℂ | F.ρ⁻¹ < ‖w‖ ∧ ‖w‖ < F.ρ} from ⟨hy, h1, h2⟩)
      simpa using this
    · have hzB : z ∈ Kummer.powMap (D.deg i) ⁻¹' (B ×ˢ ball (0 : ℂ) F.ρ) := hAB _ hz
      have hzV : z ∈ Kummer.powMap (D.deg i) ⁻¹' (V ×ˢ ball (0 : ℂ) F.ρ) := hAV _ hz
      have hz1 : z.1 ∈ V'' := hz.1
      have hz2 : F.ρ⁻¹ < ‖z.2‖ ^ (D.deg i : ℕ) := by
        have := hz.2.1
        change F.ρ⁻¹ < ‖z.2 ^ (D.deg i : ℕ)‖ at this
        rwa [norm_pow] at this
      have hz3 : ‖z.2‖ ^ (D.deg i : ℕ) < F.ρ := by
        have := hz.2.2
        change ‖z.2 ^ (D.deg i : ℕ)‖ < F.ρ at this
        rwa [norm_pow] at this
      have hsum := D.snd_eq_sum_of_evalFun_eq h₀ hB hV htr hs e hV''V hV''B hte i
        (hBG (hV''B hz1)) hz1 hz2 hz3
      simp only at hsum ⊢
      have e1 : ∑ j : Fin (D.deg i), z.2 ^ (j : ℕ) *
          ∑ k, e k (Kummer.powMap (D.deg i) z).1 * c k i j (Kummer.powMap (D.deg i) z) =
          ∑ k, e k z.1 * (s k).2 i z := by
        simp only [fun k ↦ hceq k i hzB, Finset.mul_sum, Kummer.powMap_apply]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring
      rw [e1, ← hsum, hcteq i hzV, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ ↦ by simp only [Kummer.powMap_apply]; ring
  -- Oka's theorem
  let UV : TopologicalSpace.Opens (Cm.{u} m) := ⟨V'', hV''o⟩
  have hUV : UV ≤ V₀ := fun y hy ↦ hVV₀ (hV''V hy)
  let a : Fin K → OkaRing UV := fun k ↦ OkaRing.ofDifferentiableOn (e k) (he k)
  have hzero : ∀ f : OkaRing UV, (∀ y (hy : y ∈ UV), OkaRing.evalHom hy f = 0) → f = 0 :=
    fun f h ↦ OkaRing.ext (funext fun y ↦ h y.1 y.2)
  have hrel' : ∀ q, ∑ k, a k * OkaRing.restrict (hUV.trans hV₀U₀) (col k q) = 0 := fun q ↦
    hzero _ fun y hy ↦ by
      simp only [map_sum, map_mul, a, col, OkaRing.evalHom_apply,
        OkaRing.ofDifferentiableOn_toFun]
      exact hΦ y hy _ _
  obtain ⟨W', hW'UV, hb'W', c', hc'⟩ := hgen' UV hUV a hrel' b' hb'V''
  refine ⟨W', fun y hy ↦ hV''V (hW'UV hy), W'.isOpen, hb'W', fun l ↦ (c' l).toGlobalFun _,
    fun l ↦ (c' l).differentiableOn_toGlobalFun, fun y hy hyW ↦ ?_⟩
  have hyV'' : baseOf (pt W y) ∈ V'' := hW'UV hyW
  have hyN := (mem_img_iff.1 ((mem_preim_iff h₀ W).1 hy)).1
  have hyV₀ : y ∈ preim h₀ W (tubeN N V₀ V₀.isOpen) :=
    (mem_preim_iff h₀ W).2 (mem_img_iff.2 ⟨hyN, hUV hyV''⟩)
  have hek : ∀ k, e k (baseOf (pt W y)) = ∑ l, (c' l).toGlobalFun _ (baseOf (pt W y)) *
      gf l k (baseOf (pt W y)) := fun k ↦ by
    have := congrArg (OkaRing.evalHom hyW) (hc' k)
    simp only [map_sum, map_mul, OkaRing.evalHom_restrict] at this
    have h2 : OkaRing.evalHom (hW'UV hyW) (a k) = e k (baseOf (pt W y)) := rfl
    rw [h2] at this
    rw [this]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [OkaRing.toGlobalFun_apply _ hyW]
    exact congrArg _ (OkaRing.toGlobalFun_apply _ (hUV (hW'UV hyW))).symm
  have hTl : ∀ l, evalFun (T' l).1.1 y =
      ∑ k, gf l k (baseOf (pt W y)) * evalFun (s k).1.1 y := fun l ↦ by
    change evalFun (T l).1.1 y = _
    rw [D.evalFun_sum_baseCap_mul h₀ V₀.isOpen (hgf l) sV hyV₀]
    exact Finset.sum_congr rfl fun k _ ↦ congrArg _ (evalFun_map W _ _ hyV₀)
  rw [hte y hy hyV'']
  simp only [hTl, hek, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun l _ ↦ by ring

end AnnulusDecomposition

end

end ComplexAnalytic.Cap
