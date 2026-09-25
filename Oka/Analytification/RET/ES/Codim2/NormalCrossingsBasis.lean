/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.ES.ReflexiveHull
import Oka.Analytification.RET.ES.Codim2.NormalCrossingsCover

/-!
# Bounded sections near a normal crossings divisor

Keep the notation of `Oka/Analytification/RET/ES/Codim2/NormalCrossingsCover.lean`: `χ` is a
normal crossings chart for `N ∖ N°` on `img U`, with coordinates `Ψ : img U ≅ B × Δʳ`, and `K`
describes `W` over `U` as a union of quotients `Φ_c` of Kummer covers of degrees `M_c` by groups of
rotations `Γ_c`.

For every Kummer piece `c` and every exponent `j ∈ {0, …, M_c - 1}ʳ` invariant under `Γ_c`, the
function which is `uʲ` at `Φ_c(u)` and `0` on the other pieces is the value of a bounded section
`K.basis h₀ ⟨c, j⟩` of `𝒜` over `U`. These sections form a basis of `𝒜` over every open inside
`U` (`ComplexAnalytic.BoundedSections.NCChart.KummerData.exists_eq_sum_smul_basis`,
`ComplexAnalytic.BoundedSections.NCChart.KummerData.eq_zero_of_sum_smul_basis_eq_zero`): a
bounded section `a` gives on the piece `c` a bounded holomorphic function of `u ∈ B × (Δ*)ʳ`
invariant under `Γ_c`, which extends holomorphically across the divisor
(`KummerPi.exists_differentiableOn_powMap_eqOn`) and is then `∑_j uʲ gⱼ(κ(u))` with only
invariant `j` occurring (`KummerPi.exists_eqOn_sum_monomial_mul_comp_powMap`,
`KummerPi.eqOn_zero_of_comp_rotMap_eq`). In particular `𝒜` is locally free near every point of
a normal crossings chart (`ComplexAnalytic.BoundedSections.NCChart.exists_basis`,
`ComplexAnalytic.BoundedSections.NCChart.exists_isFreeSpanAt`).

## Main definitions

- `ComplexAnalytic.BoundedSections.NCChart.KummerData.ι`: the invariant monomials on the pieces.
- `ComplexAnalytic.BoundedSections.NCChart.KummerData.basis`: the corresponding sections of `𝒜`.

## Main results

- `ComplexAnalytic.BoundedSections.NCChart.exists_basis`: `𝒜` is free over `U`, with a basis of
  monomial sections.
-/

open CategoryTheory Opposite AlgebraicGeometry Topology TopologicalSpace Filter Set Metric
  LocallyRingedSpace

universe u

namespace ComplexAnalytic.BoundedSections

open AnalyticSpace

noncomputable section

variable {n : ℕ} {N N₀ : (AnalyticSpace.complexAffineSpace.{u} n).Opens} (h₀ : N₀ ≤ N)
  {W : FiniteEtaleOver (space N₀)} {U : (space N).Opens} {E : Type*} [NormedAddCommGroup E]
  [NormedSpace ℂ E] {r : ℕ} {χ : NCChart N₀ (img U : Set (Cn.{u} n)) E r}


/-! ### Sections of `𝒪_N` and of `𝒜` -/

lemma eq_of_holFun_eq {V : (space N).Opens} {q q' : (space N).presheaf.obj (op V)}
    (h : ∀ x ∈ img V, holFun q x = holFun q' x) : q = q' :=
  OkaRing.ext (funext fun x ↦ (OkaRing.toGlobalFun_apply (U := img V) _ x.2).symm.trans
    ((h x x.2).trans (OkaRing.toGlobalFun_apply (U := img V) _ x.2)))

lemma holFun_ofDifferentiableOn {V : (space N).Opens} {F : Cn.{u} n → ℂ}
    (hF : DifferentiableOn ℂ F (img V)) {x : Cn.{u} n} (hx : x ∈ img V) :
    holFun (N := N) (V := V) (OkaRing.ofDifferentiableOn F hF) x = F x :=
  OkaRing.toGlobalFun_apply (U := img V) _ hx

lemma secVal_sum {V : (space N).Opens} {κ : Type*} (s : Finset κ)
    (f : κ → (boundedModule h₀ W).val.obj (op V)) :
    secVal h₀ W (∑ i ∈ s, f i) = ∑ i ∈ s, secVal h₀ W (f i) :=
  map_sum (AddMonoidHom.mk' (secVal h₀ W) (secVal_add h₀ W)) f s

namespace NCChart.KummerData

variable (K : χ.KummerData W)

/-- The exponents `j ∈ {0, …, M_c - 1}ʳ` whose monomial `uʲ` is invariant under `Γ_c`. -/
abbrev J (c : K.C) : Type :=
  {j : Fin r → Fin (K.M c) // ∀ a ∈ K.Γ c, KummerPi.rotChar (K.M c) a (fun i ↦ (j i : ℕ)) = 1}

instance (c : K.C) : Fintype (K.J c) :=
  Fintype.ofFinite _

/-- The invariant monomials on the Kummer pieces. -/
abbrev ι : Type u :=
  Σ c : K.C, ULift.{u} (K.J c)

/-- The exponent of an invariant monomial, as a natural-number vector. -/
def exponent (i : K.ι) : Fin r → ℕ :=
  fun k ↦ (i.2.down.1 k : ℕ)

lemma monomial_rot (c : K.C) (j : K.J c) {a : Fin r → ℤ} (ha : a ∈ K.Γ c)
    (u : KummerPi.base χ.B r) :
    KummerPi.monomial (fun k ↦ (j.1 k : ℕ)) (KummerPi.rot χ.B r (K.M c) a u).1 =
      KummerPi.monomial (fun k ↦ (j.1 k : ℕ)) u.1 := by
  change KummerPi.monomial _ (KummerPi.rotMap (K.M c : ℕ) a u.1) = _
  rw [KummerPi.monomial_rotMap, j.2 a ha, one_mul]

open Classical in
/-- The value of the monomial section `i = ⟨c, j⟩`: `uʲ` at `Φ_c(u)` and `0` off the piece `c`. -/
def val (i : K.ι) (w : W.left) : ℂ :=
  if h : ∃ u, K.Φ i.1 u = w then KummerPi.monomial (K.exponent i) h.choose.1 else 0

lemma val_eq (i : K.ι) {u : KummerPi.base χ.B r} {w : W.left} (hu : K.Φ i.1 u = w) :
    K.val i w = KummerPi.monomial (K.exponent i) u.1 := by
  have h : ∃ u, K.Φ i.1 u = w := ⟨u, hu⟩
  rw [val, dif_pos h]
  obtain ⟨a, ha, hau⟩ := (K.fib i.1 _ _).1 (h.choose_spec.trans hu.symm)
  rw [hau]
  exact (K.monomial_rot i.1 i.2.down ha _).symm

lemma val_eq_zero (i : K.ι) {w : W.left} (hw : ∀ u, K.Φ i.1 u ≠ w) : K.val i w = 0 := by
  rw [val, dif_neg fun ⟨u, hu⟩ ↦ hw u hu]

lemma val_eq_zero_of_ne (i : K.ι) {c : K.C} (hc : c ≠ i.1) {u : KummerPi.base χ.B r}
    {w : W.left} (hu : K.Φ c u = w) : K.val i w = 0 :=
  K.val_eq_zero i fun u' hu' ↦ hc (K.sep c i.1 u u' (hu.trans hu'.symm))

lemma norm_val_le (i : K.ι) (w : W.left) : ‖K.val i w‖ ≤ 1 := by
  by_cases h : ∃ u, K.Φ i.1 u = w
  · obtain ⟨u, hu⟩ := h
    rw [K.val_eq i hu, KummerPi.monomial, norm_prod]
    refine Finset.prod_le_one (fun _ _ ↦ norm_nonneg _) fun k _ ↦ ?_
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) ((KummerPi.mem_base.1 u.2).2 k).2.le
  · rw [K.val_eq_zero i fun u hu ↦ h ⟨u, hu⟩, norm_zero]
    exact zero_le_one

/-- The point below `Φ_c(u)` is `Ψ'(κ(u))`. -/
lemma pt_Φ (c : K.C) (u : KummerPi.base χ.B r) :
    pt W (K.Φ c u) = χ.Ψ' (KummerPi.powMap (K.M c) u.1) := by
  rw [← K.Ψ_pt c u, χ.left_inv _ (K.pt_mem c u)]


/-! ### The monomial sections -/

/-- The monomial function `K.val i` is the value of a section of `𝒪_W` over `p⁻¹(U)`: near a
point of the piece `c`, the coordinate `u` is a holomorphic function of the point below, via a
local inverse of `κ`. -/
theorem exists_eval_eq_val (i : K.ι) :
    ∃ s : W.left.presheaf.obj (op (preim h₀ W U)), ∀ w (hw : w ∈ preim h₀ W U),
      W.left.eval w hw s = K.val i w := by
  classical
  refine exists_eval_eq_of_local (isLocallyOpenInAffine_left W) (K.val i) fun w hw ↦ ?_
  have hwU : pt W w ∈ img U := (mem_preim_iff h₀ W).1 hw
  obtain ⟨c, u₀, hu₀⟩ := K.surj w hwU
  by_cases hc : c = i.1
  swap
  · let O : W.left.Opens := ⟨K.Φ c '' univ, K.isOpenMap c _ isOpen_univ⟩
    refine ⟨O ⊓ preim h₀ W U, ⟨⟨u₀, trivial, hu₀⟩, hw⟩, inf_le_right, 0, fun w' hw' ↦ ?_⟩
    obtain ⟨u', -, hu'⟩ := hw'.1
    rw [map_zero, K.val_eq_zero_of_ne i hc hu']
  have hu₀nz : ∀ k, u₀.1.2 k ≠ 0 := fun k ↦ ((KummerPi.mem_base.1 u₀.2).2 k).1
  set L := KummerPi.localInv (K.M c : ℕ) u₀.1
  have hΨx₀ : χ.Ψ (pt W w) = KummerPi.powMap (K.M c) u₀.1 := by
    rw [← hu₀]
    exact K.Ψ_pt c u₀
  have hbo : IsOpen (KummerPi.base χ.B r) := KummerPi.isOpen_base r χ.isOpen
  -- `Φ_c`, extended to all of `E × ℂʳ`
  let Φ' : E × (Fin r → ℂ) → W.left := fun z ↦
    if hz : z ∈ KummerPi.base χ.B r then K.Φ c ⟨z, hz⟩ else w
  have hΦ' (z : E × (Fin r → ℂ)) (hz : z ∈ KummerPi.base χ.B r) : Φ' z = K.Φ c ⟨z, hz⟩ :=
    dif_pos hz
  have hΦ'c : ContinuousOn Φ' (KummerPi.base χ.B r) := by
    rw [continuousOn_iff_continuous_restrict]
    have : (KummerPi.base χ.B r).restrict Φ' = K.Φ c := funext fun z ↦ hΦ' z.1 z.2
    rw [this]
    exact K.continuous c
  obtain ⟨O₁, hwO₁, hinj, -⟩ := exists_sheet W w
  have hΨc : ContinuousAt χ.Ψ (pt W w) :=
    χ.differentiableOn.continuousOn.continuousAt ((img U).isOpen.mem_nhds hwU)
  have h₂ : ∀ᶠ x in 𝓝 (pt W w), DifferentiableAt ℂ L (χ.Ψ x) ∧ ∀ k, (χ.Ψ x).2 k ≠ 0 :=
    hΨc.eventually (by rw [hΨx₀]; exact KummerPi.eventually_differentiableAt_localInv _ hu₀nz)
  have hLx₀ : L (χ.Ψ (pt W w)) = u₀.1 := by
    rw [hΨx₀]
    exact KummerPi.localInv_powMap_self _ _
  have hgc : ContinuousAt (fun x ↦ L (χ.Ψ x)) (pt W w) :=
    h₂.self_of_nhds.1.continuousAt.comp hΨc
  have h₃ : ∀ᶠ x in 𝓝 (pt W w), L (χ.Ψ x) ∈ KummerPi.base χ.B r :=
    hgc.preimage_mem_nhds (by rw [hLx₀]; exact hbo.mem_nhds u₀.2)
  have h₄ : ∀ᶠ x in 𝓝 (pt W w), Φ' (L (χ.Ψ x)) ∈ O₁ := by
    have hc' : ContinuousAt (fun x ↦ Φ' (L (χ.Ψ x))) (pt W w) :=
      ContinuousAt.comp (g := Φ') (by rw [hLx₀]; exact hΦ'c.continuousAt (hbo.mem_nhds u₀.2))
        hgc
    refine hc'.preimage_mem_nhds (O₁.isOpen.mem_nhds ?_)
    change Φ' (L (χ.Ψ (pt W w))) ∈ O₁
    have e : K.Φ c ⟨u₀.1, u₀.2⟩ = w := hu₀
    rw [hLx₀, hΦ' _ u₀.2, e]
    exact hwO₁
  obtain ⟨G, hG, hGo, hx₀G⟩ := _root_.eventually_nhds_iff.1
    (((show ∀ᶠ x in 𝓝 (pt W w), x ∈ img U from (img U).isOpen.mem_nhds hwU).and h₂).and
      (h₃.and h₄))
  let O₂ : W.left.Opens := ⟨pt W ⁻¹' G, hGo.preimage (continuous_pt W)⟩
  obtain ⟨σ, hσ⟩ := exists_eval_eq_of_differentiableAt W (O := O₁ ⊓ preim h₀ W U ⊓ O₂)
    (fun x ↦ KummerPi.monomial (K.exponent i) (L (χ.Ψ x))) fun w' hw' ↦ by
      obtain ⟨⟨hGU, hL, -⟩, -⟩ := hG _ hw'.2
      exact DifferentiableAt.comp (g := KummerPi.monomial (K.exponent i)) _
        (KummerPi.differentiable_monomial _).differentiableAt
        (hL.comp _ (χ.differentiableOn.differentiableAt ((img U).isOpen.mem_nhds hGU)))
  refine ⟨O₁ ⊓ preim h₀ W U ⊓ O₂, ⟨⟨hwO₁, hw⟩, hx₀G⟩, inf_le_left.trans inf_le_right, σ,
    fun w' hw' ↦ ?_⟩
  rw [hσ w' hw']
  obtain ⟨⟨hGU, -, hnz⟩, hbase, hO₁⟩ := hG _ hw'.2
  have hw'' : K.Φ c ⟨_, hbase⟩ = w' := by
    refine hinj (by rw [← hΦ' _ hbase]; exact hO₁) hw'.1.1 ?_
    rw [K.pt_Φ, KummerPi.powMap_localInv (K.M c).ne_zero _ hu₀nz hnz, χ.left_inv _ hGU]
  subst hc
  exact (K.val_eq i hw'').symm

/-- The monomial section `i`, as a section of `𝒪_W` over `p⁻¹(U)`. -/
def sec (i : K.ι) : W.left.presheaf.obj (op (preim h₀ W U)) :=
  (K.exists_eval_eq_val h₀ i).choose

lemma eval_sec (i : K.ι) (w : W.left) (hw : w ∈ preim h₀ W U) :
    W.left.eval w hw (K.sec h₀ i) = K.val i w :=
  (K.exists_eval_eq_val h₀ i).choose_spec w hw

lemma sec_mem (i : K.ι) : K.sec h₀ i ∈ boundedSubring h₀ W U := fun _ _ _ ↦
  ⟨univ, univ_mem, 1, fun w hw _ ↦ by rw [K.eval_sec h₀ i w hw]; exact K.norm_val_le i w⟩

/-- The **monomial section** `i = ⟨c, j⟩` of `𝒜` over `U`: `uʲ` at `Φ_c(u)`, `0` off the piece
`c`. -/
def basis (i : K.ι) : (boundedModule h₀ W).val.obj (op U) :=
  mkSec h₀ W (K.sec h₀ i) (K.sec_mem h₀ i)

lemma evalFun_basis {V : (space N).Opens} (h : V ≤ U) (i : K.ι) {w : W.left}
    (hw : w ∈ preim h₀ W V) :
    evalFun (secVal h₀ W (sectRes (boundedModule h₀ W) h (K.basis h₀ i))) w = K.val i w := by
  rw [secVal_map, evalFun_of_mem _ hw, eval_presheaf_map]
  exact K.eval_sec h₀ i w _


/-- Near a point of the piece `c` lying in an open `O`, the piece stays in `O`. -/
lemma eventually_mem (c : K.C) (u : KummerPi.base χ.B r) {O : W.left.Opens}
    (hO : K.Φ c u ∈ O) :
    ∀ᶠ z in 𝓝 u.1, ∃ hz : z ∈ KummerPi.base χ.B r, K.Φ c ⟨z, hz⟩ ∈ O := by
  have hbo : IsOpen (KummerPi.base χ.B r) := KummerPi.isOpen_base r χ.isOpen
  filter_upwards [(hbo.isOpenMap_subtype_val _
    ((K.continuous c).isOpen_preimage _ O.isOpen)).mem_nhds ⟨u, hO, rfl⟩] with z hz
  obtain ⟨u', hu', rfl⟩ := hz
  exact ⟨u'.2, hu'⟩

variable [FiniteDimensional ℂ E]

/-- **A bounded section on a Kummer piece.** On the piece `c`, a section `a` of `𝒜` over
`V ⊆ U` is `∑_j uʲ gⱼ(κ(u))` with `gⱼ` holomorphic on `Ψ(img V)`, and `gⱼ = 0` unless `uʲ` is
invariant under `Γ_c`. -/
theorem exists_decomposition {V : (space N).Opens} (h : V ≤ U)
    (a : (boundedModule h₀ W).val.obj (op V)) (c : K.C) :
    ∃ g : (Fin r → Fin (K.M c)) → E × (Fin r → ℂ) → ℂ,
      (∀ j, DifferentiableOn ℂ (g j) (χ.chartSet (img V))) ∧
      (∀ j, ¬ (∀ b ∈ K.Γ c, KummerPi.rotChar (K.M c) b (fun k ↦ (j k : ℕ)) = 1) →
        EqOn (g j) 0 (χ.chartSet (img V))) ∧
      ∀ u : KummerPi.base χ.B r, KummerPi.powMap (K.M c) u.1 ∈ χ.chartSet (img V) →
        evalFun (secVal h₀ W a) (K.Φ c u) =
          ∑ j, KummerPi.monomial (fun k ↦ (j k : ℕ)) u.1 * g j (KummerPi.powMap (K.M c) u.1) := by
  classical
  set M : ℕ := (K.M c : ℕ)
  have hM : 0 < M := (K.M c).pos
  set Vc := χ.chartSet (img V)
  have hVc : IsOpen Vc := χ.isOpen_chartSet (img V).isOpen
  have hD : IsOpen (χ.B ×ˢ univ.pi fun _ : Fin r ↦ ball (0 : ℂ) 1) :=
    χ.isOpen.prod (isOpen_set_pi finite_univ fun _ _ ↦ isOpen_ball)
  set Z := KummerPi.prodCoord (E := E) (r := r) ⁻¹' {0}
  have hbase (z : E × (Fin r → ℂ)) (hz : z ∈ KummerPi.powMap M ⁻¹' Vc \ Z) :
      z ∈ KummerPi.base χ.B r :=
    χ.mem_base_of_mem_chartSet hM.ne' hz.1 hz.2
  have hpre (u : KummerPi.base χ.B r) (hu : KummerPi.powMap M u.1 ∈ Vc) :
      K.Φ c u ∈ preim h₀ W V := by
    rw [mem_preim_iff, K.pt_Φ]
    exact hu.2
  let F : E × (Fin r → ℂ) → ℂ := fun z ↦
    if hz : z ∈ KummerPi.base χ.B r then evalFun (secVal h₀ W a) (K.Φ c ⟨z, hz⟩) else 0
  have hF (u : KummerPi.base χ.B r) : F u.1 = evalFun (secVal h₀ W a) (K.Φ c u) := dif_pos u.2
  -- `F` is holomorphic off the divisor
  have hFd : DifferentiableOn ℂ F (KummerPi.powMap M ⁻¹' Vc \ Z) := by
    intro z hz
    refine DifferentiableAt.differentiableWithinAt ?_
    set u : KummerPi.base χ.B r := ⟨z, hbase z hz⟩
    have hw₀ := hpre u hz.1
    obtain ⟨O₁, hwO₁, -, hsheet⟩ := exists_sheet W (K.Φ c u)
    obtain ⟨Fs, hFsd, hFs⟩ := hsheet (O' := O₁ ⊓ preim h₀ W V) inf_le_left
      (W.left.presheaf.map (homOfLE inf_le_right).op (secVal h₀ W a))
    have hκ : KummerPi.powMap M z ∈ χ.B ×ˢ univ.pi fun _ : Fin r ↦ ball (0 : ℂ) 1 := hz.1.1
    have hd : DifferentiableAt ℂ (fun z ↦ Fs (χ.Ψ' (KummerPi.powMap M z))) z := by
      have h₁ := hFsd (K.Φ c u) ⟨hwO₁, hw₀⟩
      rw [K.pt_Φ] at h₁
      exact h₁.comp z ((χ.differentiableOn'.differentiableAt (hD.mem_nhds hκ)).comp z
        ((KummerPi.differentiable_powMap M).differentiableAt))
    refine hd.congr_of_eventuallyEq ?_
    filter_upwards [K.eventually_mem c u (O := O₁ ⊓ preim h₀ W V) ⟨hwO₁, hw₀⟩] with z' hz'
    obtain ⟨hz'b, hz'O⟩ := hz'
    rw [hF ⟨z', hz'b⟩, evalFun_of_mem _ hz'O.2, ← eval_presheaf_map W.left
      (homOfLE inf_le_right).op _ hz'O, hFs _ hz'O, K.pt_Φ]
  -- `F` is bounded near the divisor
  have hbdd : ∀ z ∈ KummerPi.powMap M ⁻¹' Vc, IsBoundedUnder (· ≤ ·)
      (𝓝[KummerPi.powMap M ⁻¹' Vc \ Z] z) (‖F ·‖) := by
    intro z hz
    by_cases hz0 : KummerPi.prodCoord z = 0
    swap
    · have hVo : IsOpen (KummerPi.powMap M ⁻¹' Vc \ Z) :=
        (hVc.preimage (KummerPi.differentiable_powMap M).continuous).sdiff
          (isClosed_singleton.preimage (KummerPi.differentiable_prodCoord).continuous)
      exact ((hFd.differentiableAt (hVo.mem_nhds ⟨hz, hz0⟩)).continuousAt.norm.tendsto
        |>.isBoundedUnder_le).mono nhdsWithin_le_nhds
    set y := χ.Ψ' (KummerPi.powMap M z)
    have hyV : y ∈ img V := hz.2
    have hyN : y ∉ N₀ := by
      rw [χ.mem_iff y (img_mono h hyV), χ.right_inv _ hz.1]
      intro hne
      obtain ⟨k, -, hk⟩ := Finset.prod_eq_zero_iff.1 hz0
      exact hne k (by simp [KummerPi.powMap, hk, hM.ne'])
    obtain ⟨hyN', hyV'⟩ := mem_img_iff.1 hyV
    obtain ⟨Nb, hNb, C, hC⟩ := secVal_mem h₀ W a ⟨y, hyN'⟩ hyV' hyN
    obtain ⟨t, ht, hts⟩ := (mem_nhds_subtype _ _ _).1 hNb
    have hc : ContinuousAt (fun z ↦ χ.Ψ' (KummerPi.powMap M z)) z :=
      (χ.differentiableOn'.continuousOn.continuousAt (hD.mem_nhds hz.1)).comp
        (KummerPi.differentiable_powMap M).continuous.continuousAt
    refine isBoundedUnder_of_eventually_le (a := C) ?_
    filter_upwards [nhdsWithin_le_nhds (hc.preimage_mem_nhds ht), self_mem_nhdsWithin]
      with z' hz't hz'
    set u : KummerPi.base χ.B r := ⟨z', hbase z' hz'⟩
    have hw := hpre u hz'.1
    have hNbw : (proj h₀ W).toLRSHom.base (K.Φ c u) ∈ Nb := by
      refine hts ?_
      change ((proj h₀ W).toLRSHom.base (K.Φ c u)).1 ∈ t
      rw [coe_proj_base, K.pt_Φ]
      exact hz't
    change ‖F u.1‖ ≤ C
    rw [hF u, evalFun_of_mem _ hw]
    exact hC _ hw hNbw
  obtain ⟨G, hG, hGF⟩ := KummerPi.exists_differentiableOn_powMap_eqOn M hVc hFd hbdd
  -- `G` is invariant under `Γ_c`
  have hrot (b : Fin r → ℤ) (hb : b ∈ K.Γ c) :
      EqOn (G ∘ KummerPi.rotMap M b) G (KummerPi.powMap M ⁻¹' Vc) := by
    refine KummerPi.eqOn_comp_rotMap hM.ne' b hVc hG.continuousOn fun z hz ↦ ?_
    have hz' : KummerPi.rotMap M b z ∈ KummerPi.powMap M ⁻¹' Vc \ Z := by
      refine ⟨by rw [mem_preimage, KummerPi.powMap_rotMap hM.ne']; exact hz.1, ?_⟩
      simp only [Z, mem_preimage, mem_singleton_iff, KummerPi.prodCoord, KummerPi.rotMap,
        Finset.prod_mul_distrib]
      exact mul_ne_zero (Finset.prod_ne_zero_iff.2 fun _ _ ↦ Complex.exp_ne_zero _) hz.2
    set u : KummerPi.base χ.B r := ⟨z, hbase z hz⟩
    have hu' : (⟨KummerPi.rotMap M b z, hbase _ hz'⟩ : KummerPi.base χ.B r) =
        KummerPi.rot χ.B r (K.M c) b u := rfl
    change G (KummerPi.rotMap M b z) = G z
    rw [hGF hz', hGF hz, hF ⟨_, hbase _ hz'⟩, hF u, hu', (K.fib c u _).2 ⟨b, hb, rfl⟩]
  obtain ⟨g, hgd, hGg⟩ := KummerPi.exists_eqOn_sum_monomial_mul_comp_powMap hM hVc hG
  refine ⟨g, hgd, fun j hj ↦ ?_, fun u hu ↦ ?_⟩
  · push Not at hj
    obtain ⟨b, hb, hbj⟩ := hj
    refine KummerPi.eqOn_zero_of_comp_rotMap_eq hM hVc (fun j ↦ (hgd j).continuousOn) b
      (fun x hx ↦ ?_) hbj
    have hx' : KummerPi.rotMap M b x ∈ KummerPi.powMap M ⁻¹' Vc := by
      rw [mem_preimage, KummerPi.powMap_rotMap hM.ne']
      exact hx
    have e₁ := hGg hx'
    have e₂ := hGg hx
    simp only at e₁ e₂
    rw [← e₁, ← e₂]
    exact hrot b hb hx
  · have hu0 : u.1 ∈ KummerPi.powMap M ⁻¹' Vc \ Z := by
      refine ⟨hu, ?_⟩
      simp only [Z, mem_preimage, mem_singleton_iff, KummerPi.prodCoord]
      exact Finset.prod_ne_zero_iff.2 fun k _ ↦ ((KummerPi.mem_base.1 u.2).2 k).1
    rw [← hF u, ← hGF hu0]
    exact hGg hu


/-! ### The monomial sections form a basis -/

omit [FiniteDimensional ℂ E] in
/-- The values of a combination of monomial sections at a point of the piece `c`. -/
lemma evalFun_sum_smul_basis {V : (space N).Opens} (h : V ≤ U)
    (q : K.ι → (space N).presheaf.obj (op V)) {c : K.C} {u : KummerPi.base χ.B r}
    (hw : K.Φ c u ∈ preim h₀ W V) :
    evalFun (secVal h₀ W (∑ i, q i • sectRes (boundedModule h₀ W) h (K.basis h₀ i)))
        (K.Φ c u) =
      ∑ j : ULift.{u} (K.J c), holFun (q ⟨c, j⟩) (pt W (K.Φ c u)) *
        KummerPi.monomial (K.exponent ⟨c, j⟩) u.1 := by
  classical
  have hterm (i : K.ι) : evalFun (secVal h₀ W (q i • sectRes (boundedModule h₀ W) h
      (K.basis h₀ i))) (K.Φ c u) = holFun (q i) (pt W (K.Φ c u)) * K.val i (K.Φ c u) := by
    rw [secVal_smul, evalFun_mul W _ _ hw, evalFun_pullback h₀ W _ hw, K.evalFun_basis h₀ h i hw]
  rw [secVal_sum, evalFun_of_mem _ hw, map_sum]
  simp_rw [← evalFun_of_mem _ hw, hterm]
  rw [Fintype.sum_sigma, Finset.sum_eq_single c]
  · exact Finset.sum_congr rfl fun j _ ↦ by rw [K.val_eq ⟨c, j⟩ rfl]
  · intro c' _ hc'
    exact Finset.sum_eq_zero fun j _ ↦ by rw [K.val_eq_zero_of_ne ⟨c', j⟩ (Ne.symm hc') rfl,
      mul_zero]
  · exact fun h ↦ absurd (Finset.mem_univ c) h

/-- **The monomial sections span `𝒜`.** Every section of `𝒜` over `V ⊆ U` is a combination of the
monomial sections with holomorphic coefficients. -/
theorem exists_eq_sum_smul_basis {V : (space N).Opens} (h : V ≤ U)
    (a : (boundedModule h₀ W).val.obj (op V)) :
    ∃ q : K.ι → (space N).presheaf.obj (op V),
      a = ∑ i, q i • sectRes (boundedModule h₀ W) h (K.basis h₀ i) := by
  classical
  choose g hgd hg0 hga using K.exists_decomposition h₀ h a
  have hmaps (x : Cn.{u} n) (hx : x ∈ img V) : χ.Ψ x ∈ χ.chartSet (img V) :=
    χ.Ψ_mem_chartSet (img_mono h) hx
  have hq (i : K.ι) : DifferentiableOn ℂ (fun x ↦ g i.1 i.2.down.1 (χ.Ψ x)) (img V) :=
    (hgd i.1 i.2.down.1).comp (χ.differentiableOn.mono (img_mono h)) hmaps
  refine ⟨fun i ↦ OkaRing.ofDifferentiableOn _ (hq i), ?_⟩
  refine secVal_injective h₀ W (eq_of_forall_eval_eq (isLocallyOpenInAffine_left W)
    fun w hw ↦ ?_)
  have hwV := (mem_preim_iff h₀ W).1 hw
  obtain ⟨c, u, rfl⟩ := K.surj w (img_mono h hwV)
  rw [← evalFun_of_mem _ hw, ← evalFun_of_mem _ hw, K.evalFun_sum_smul_basis h₀ h _ hw]
  have hκ : KummerPi.powMap (K.M c) u.1 ∈ χ.chartSet (img V) := by
    have := hmaps _ hwV
    rwa [K.Ψ_pt] at this
  rw [hga c u hκ]
  have hcoef (j : ULift.{u} (K.J c)) :
      holFun (N := N) (V := V) (OkaRing.ofDifferentiableOn _ (hq ⟨c, j⟩)) (pt W (K.Φ c u)) =
        g c j.down.1 (KummerPi.powMap (K.M c) u.1) := by
    rw [holFun_ofDifferentiableOn _ hwV, K.Ψ_pt]
  simp_rw [hcoef]
  set P : (Fin r → Fin (K.M c)) → Prop := fun j ↦
    ∀ b ∈ K.Γ c, KummerPi.rotChar (K.M c) b (fun k ↦ (j k : ℕ)) = 1
  symm
  refine Fintype.sum_of_injective (fun j : ULift.{u} (K.J c) ↦ j.down.1)
    (fun j j' hjj' ↦ ULift.ext _ _ (Subtype.ext hjj')) _ _ (fun j hj ↦ ?_) fun j ↦ mul_comm _ _
  have hPj : ¬ P j := fun hPj ↦ hj ⟨⟨⟨j, hPj⟩⟩, rfl⟩
  rw [hg0 c j hPj hκ, Pi.zero_apply, mul_zero]

omit [FiniteDimensional ℂ E] in
/-- **The monomial sections are linearly independent** over every open inside `U`. -/
theorem eq_zero_of_sum_smul_basis_eq_zero {V : (space N).Opens} (h : V ≤ U)
    (q : K.ι → (space N).presheaf.obj (op V))
    (hq : ∑ i, q i • sectRes (boundedModule h₀ W) h (K.basis h₀ i) = 0) (i : K.ι) : q i = 0 := by
  classical
  obtain ⟨c, ⟨j₀⟩⟩ := i
  set M : ℕ := (K.M c : ℕ)
  set Vc := χ.chartSet (img V)
  have hVc : IsOpen Vc := χ.isOpen_chartSet (img V).isOpen
  let P : (Fin r → Fin M) → Prop := fun j ↦
    ∀ b ∈ K.Γ c, KummerPi.rotChar (K.M c) b (fun k ↦ (j k : ℕ)) = 1
  let g : (Fin r → Fin M) → E × (Fin r → ℂ) → ℂ := fun j z ↦
    if hj : P j then holFun (q ⟨c, ⟨⟨j, hj⟩⟩⟩) (χ.Ψ' z) else 0
  have hgc (j : Fin r → Fin M) : ContinuousOn (g j) Vc := by
    by_cases hj : P j
    · simp only [g, dif_pos hj]
      exact (differentiableOn_holFun _).continuousOn.comp
        (χ.differentiableOn'.continuousOn.mono inter_subset_left) fun z hz ↦ hz.2
    · simp only [g, dif_neg hj]
      exact continuousOn_const
  have hpow : Continuous (KummerPi.powMap (E := E) (r := r) M) :=
    (KummerPi.differentiable_powMap M).continuous
  have hsum : EqOn (fun z ↦ ∑ j, KummerPi.monomial (fun k ↦ (j k : ℕ)) z *
      g j (KummerPi.powMap M z)) 0 (KummerPi.powMap M ⁻¹' Vc) := by
    refine EqOn.of_eqOn_diff_zero (g := KummerPi.prodCoord) (hVc.preimage hpow)
      (KummerPi.interior_inter_preimage_prod_eq_empty _) ?_ continuousOn_const fun z hz ↦ ?_
    · refine continuousOn_finsetSum _ fun j _ ↦ ?_
      exact (KummerPi.differentiable_monomial _).continuous.continuousOn.mul
        ((hgc j).comp hpow.continuousOn fun _ hz ↦ hz)
    have hzb := χ.mem_base_of_mem_chartSet (K.M c).ne_zero hz.1 hz.2
    set u : KummerPi.base χ.B r := ⟨z, hzb⟩
    have hw : K.Φ c u ∈ preim h₀ W V := by
      rw [mem_preim_iff, K.pt_Φ]
      exact hz.1.2
    have h₀' := congrArg (fun s ↦ evalFun (secVal h₀ W s) (K.Φ c u)) hq
    rw [K.evalFun_sum_smul_basis h₀ h q hw, secVal_zero, evalFun_of_mem _ hw, map_zero] at h₀'
    simp only [Pi.zero_apply]
    rw [← h₀']
    symm
    refine Fintype.sum_of_injective (fun j : ULift.{u} (K.J c) ↦ j.down.1)
      (fun j j' hjj' ↦ ULift.ext _ _ (Subtype.ext hjj')) _ _ (fun j hj ↦ ?_) fun j ↦ ?_
    · have hPj : ¬ P j := fun hPj ↦ hj ⟨⟨⟨j, hPj⟩⟩, rfl⟩
      simp only [g, dif_neg hPj, mul_zero]
    · simp only [g, K.pt_Φ]
      rw [dif_pos (show P j.down.1 from j.down.2)]
      exact mul_comm _ _
  have hg := KummerPi.eqOn_zero_of_sum_monomial_mul_comp_powMap (K.M c).pos hVc hgc hsum j₀.1
  refine eq_of_holFun_eq fun x hx ↦ ?_
  rw [holFun_zero hx]
  have hx' := hg (χ.Ψ_mem_chartSet (img_mono h) hx)
  simp only [g, χ.left_inv _ (img_mono h hx), Pi.zero_apply] at hx'
  rw [dif_pos (show P j₀.1 from j₀.2)] at hx'
  exact hx'

end NCChart.KummerData

/-- **`𝒜` is free near a normal crossings divisor.** Over a normal crossings chart on `U`, the
sheaf `𝒜` has a finite basis of sections over `U`, the monomial sections: every section of `𝒜`
over an open `V ⊆ U` is a unique combination of their restrictions with holomorphic
coefficients. -/
theorem NCChart.exists_basis [T2Space W.left] [FiniteDimensional ℂ E]
    (χ : NCChart N₀ (img U : Set (Cn.{u} n)) E r) :
    ∃ (k : ℕ) (e : Fin k → (boundedModule h₀ W).val.obj (op U)),
      (∀ (V : (space N).Opens) (h : V ≤ U) (a : (boundedModule h₀ W).val.obj (op V)),
        ∃ q : Fin k → (space N).presheaf.obj (op V),
          a = ∑ i, q i • sectRes (boundedModule h₀ W) h (e i)) ∧
      ∀ (V : (space N).Opens) (h : V ≤ U) (q : Fin k → (space N).presheaf.obj (op V)),
        ∑ i, q i • sectRes (boundedModule h₀ W) h (e i) = 0 → ∀ i, q i = 0 := by
  obtain ⟨K⟩ := χ.nonempty_kummerData W (img U).isOpen
  set e := Fintype.equivFin K.ι
  refine ⟨Fintype.card K.ι, fun i ↦ K.basis h₀ (e.symm i), fun V h a ↦ ?_, fun V h q hq i ↦ ?_⟩
  · obtain ⟨q, hq⟩ := K.exists_eq_sum_smul_basis h₀ h a
    refine ⟨fun i ↦ q (e.symm i), ?_⟩
    rw [hq]
    exact (e.symm.sum_comp fun i ↦ q i • sectRes (boundedModule h₀ W) h (K.basis h₀ i)).symm
  · have := K.eq_zero_of_sum_smul_basis_eq_zero h₀ h (fun i ↦ q (e i)) (by
      rw [← hq, ← e.sum_comp]
      exact Finset.sum_congr rfl fun x _ ↦ by simp only [Equiv.symm_apply_apply]) (e.symm i)
    simpa using this

/-- **`𝒜` is free near a normal crossings divisor**, in the form of
`ComplexAnalytic.BoundedSections.IsFreeSpanAt`: there are sections `e₁, …, e_k` of `𝒜` over `U`
such that near every point of `U`, `𝒜` is free with a basis in their span. -/
theorem NCChart.exists_isFreeSpanAt [T2Space W.left] [FiniteDimensional ℂ E]
    (χ : NCChart N₀ (img U : Set (Cn.{u} n)) E r) :
    ∃ (k : ℕ) (e : Fin k → (boundedModule h₀ W).val.obj (op U)),
      ∀ y ∈ U, IsFreeSpanAt h₀ W e y := by
  classical
  obtain ⟨k, e, hspan, hindep⟩ := NCChart.exists_basis (W := W) h₀ χ
  refine ⟨k, e, fun y hy ↦ isFreeSpanAt_of_basis le_rfl e hspan hindep le_rfl hy
    (fun i j ↦ if i = j then 1 else 0) fun i ↦ ?_⟩
  simp only [ReflexiveHullData.sectRes_refl, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

end

end ComplexAnalytic.BoundedSections
