/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analysis.Complex.KummerCoverPi
import Oka.Analytification.RET.ES.BoundedSections
import Oka.Analytification.RET.ES.Codim2.KummerMonomial

/-!
# Finite étale covers near a normal crossings divisor

Keep the notation of `Oka/Analytification/RET/ES/BoundedSections.lean`: `p : W ⟶ N°` is a finite
étale cover with `W` Hausdorff and `N° ⊆ N ⊆ ℂⁿ`. A *normal crossings chart*
(`ComplexAnalytic.BoundedSections.NCChart`) on an open `V ⊆ N` is a biholomorphism `Ψ` of `V`
onto `B × Δʳ`, `B` convex, under which `V ∩ N°` corresponds to `B × (Δ*)ʳ`; i.e. `N ∖ N°` is a
normal crossings divisor on `V` in the coordinates `Ψ`.

Over such a chart, `W` is a finite disjoint union of quotients of Kummer covers
(`ComplexAnalytic.BoundedSections.NCChart.exists_kummer`): there are finitely many continuous
open maps `Φ_c : B × (Δ*)ʳ → W` with disjoint images covering `p⁻¹(V)`, with
`Ψ(p(Φ_c(u))) = (b, u₁^{M_c}, …, uᵣ^{M_c})`, whose fibres are the orbits of a group `Γ_c` of
rotations of the coordinates by `M_c`-th roots of unity. This is
`IsCoveringMap.exists_sigma_kummerPi` applied to the covering `Ψ ∘ p` of `B × (Δ*)ʳ`.

Holomorphic local inverses of `κ = KummerPi.powMap M` (`KummerPi.localInv`) express the
coordinates `u` on the Kummer pieces as holomorphic functions of the point below.

## Main definitions

- `KummerPi.localInv M u₀`: a holomorphic local inverse of `κ` near `κ(u₀)`.
- `ComplexAnalytic.BoundedSections.NCChart`: a normal crossings chart for `N ∖ N°`.

## Main results

- `ComplexAnalytic.BoundedSections.NCChart.exists_kummer`: the Kummer structure of `W` over a
  normal crossings chart.
-/

open CategoryTheory Opposite AlgebraicGeometry Topology TopologicalSpace Filter Set Metric

universe u

namespace KummerPi

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {r : ℕ}

/-- The local inverse `(b, v) ↦ (b, u₀ᵢ exp(log(vᵢ / u₀ᵢᴹ) / M))` of `κ = KummerPi.powMap M`
near `κ(u₀)`. -/
noncomputable def localInv (M : ℕ) (u₀ z : E × (Fin r → ℂ)) : E × (Fin r → ℂ) :=
  (z.1, fun i ↦ u₀.2 i * Complex.exp (Complex.log (z.2 i / u₀.2 i ^ M) / M))

omit [NormedAddCommGroup E] [NormedSpace ℂ E] in
lemma localInv_powMap_self (M : ℕ) (u₀ : E × (Fin r → ℂ)) : localInv M u₀ (powMap M u₀) = u₀ := by
  refine Prod.ext rfl (funext fun i ↦ ?_)
  simp [localInv, powMap]

omit [NormedAddCommGroup E] [NormedSpace ℂ E] in
lemma powMap_localInv {M : ℕ} (hM : M ≠ 0) (u₀ : E × (Fin r → ℂ)) (hu₀ : ∀ i, u₀.2 i ≠ 0)
    {z : E × (Fin r → ℂ)} (hz : ∀ i, z.2 i ≠ 0) : powMap M (localInv M u₀ z) = z := by
  refine Prod.ext rfl (funext fun i ↦ ?_)
  simp only [localInv, powMap]
  rw [mul_pow, ← Complex.exp_nat_mul, mul_div_cancel₀ _ (by exact_mod_cast hM),
    Complex.exp_log (div_ne_zero (hz i) (pow_ne_zero _ (hu₀ i))),
    mul_div_cancel₀ _ (pow_ne_zero _ (hu₀ i))]

lemma differentiableAt_localInv (M : ℕ) (u₀ : E × (Fin r → ℂ)) {z : E × (Fin r → ℂ)}
    (hz : ∀ i, z.2 i / u₀.2 i ^ M ∈ Complex.slitPlane) :
    DifferentiableAt ℂ (localInv M u₀) z := by
  refine differentiableAt_fst.prodMk (differentiableAt_pi.2 fun i ↦ ?_)
  have h₀ : DifferentiableAt ℂ (fun z : E × (Fin r → ℂ) ↦ z.2 i / u₀.2 i ^ M) z := by fun_prop
  have h₁ : DifferentiableAt ℂ (fun z : E × (Fin r → ℂ) ↦ Complex.log (z.2 i / u₀.2 i ^ M)) z :=
    h₀.clog (hz i)
  simpa only [div_eq_mul_inv] using (h₁.mul_const ((M : ℂ)⁻¹)).cexp.const_mul (u₀.2 i)

/-- Near `κ(u₀)`, the local inverse is holomorphic and the coordinates are nonzero. -/
lemma eventually_differentiableAt_localInv (M : ℕ) {u₀ : E × (Fin r → ℂ)}
    (hu₀ : ∀ i, u₀.2 i ≠ 0) : ∀ᶠ z in 𝓝 (powMap M u₀),
      DifferentiableAt ℂ (localInv M u₀) z ∧ ∀ i, z.2 i ≠ 0 := by
  have hc (i : Fin r) : ContinuousAt (fun z : E × (Fin r → ℂ) ↦ z.2 i / u₀.2 i ^ M)
      (powMap M u₀) := by fun_prop
  have hmem (i : Fin r) : ∀ᶠ z in 𝓝 (powMap M u₀), z.2 i / u₀.2 i ^ M ∈ Complex.slitPlane := by
    refine (hc i).preimage_mem_nhds (Complex.isOpen_slitPlane.mem_nhds ?_)
    simp [powMap, div_self (pow_ne_zero M (hu₀ i)), Complex.one_mem_slitPlane]
  filter_upwards [eventually_all.2 hmem] with z hz
  exact ⟨differentiableAt_localInv M u₀ hz, fun i h ↦ by
    have := hz i
    rw [h, zero_div] at this
    exact Complex.slitPlane_ne_zero this rfl⟩

end KummerPi

namespace ComplexAnalytic.BoundedSections

open AnalyticSpace

noncomputable section

variable {n : ℕ} {N N₀ : (AnalyticSpace.complexAffineSpace.{u} n).Opens}

/-- A **normal crossings chart** for `N ∖ N°` on `V ⊆ ℂⁿ`: a biholomorphism `Ψ` of `V` onto
`B × Δʳ`, `B ⊆ E` convex and open, with inverse `Ψ'`, under which `V ∩ N°` corresponds to
`B × (Δ*)ʳ`. -/
structure NCChart (N₀ : (AnalyticSpace.complexAffineSpace.{u} n).Opens) (V : Set (Cn.{u} n))
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] (r : ℕ) where
  /-- The parameter domain. -/
  B : Set E
  convex : Convex ℝ B
  isOpen : IsOpen B
  /-- The chart. -/
  Ψ : Cn.{u} n → E × (Fin r → ℂ)
  /-- The inverse of the chart. -/
  Ψ' : E × (Fin r → ℂ) → Cn.{u} n
  differentiableOn : DifferentiableOn ℂ Ψ V
  differentiableOn' : DifferentiableOn ℂ Ψ' (B ×ˢ univ.pi fun _ ↦ ball 0 1)
  mapsTo : MapsTo Ψ V (B ×ˢ univ.pi fun _ ↦ ball 0 1)
  mapsTo' : MapsTo Ψ' (B ×ˢ univ.pi fun _ ↦ ball 0 1) V
  left_inv : ∀ x ∈ V, Ψ' (Ψ x) = x
  right_inv : ∀ z ∈ B ×ˢ univ.pi (fun _ ↦ ball (0 : ℂ) 1), Ψ (Ψ' z) = z
  mem_iff : ∀ x ∈ V, x ∈ N₀ ↔ ∀ i, (Ψ x).2 i ≠ 0

namespace NCChart

variable {V : Set (Cn.{u} n)} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {r : ℕ}
  (χ : NCChart N₀ V E r)

lemma base_subset : KummerPi.base χ.B r ⊆ χ.B ×ˢ univ.pi fun _ ↦ ball (0 : ℂ) 1 :=
  fun _ hz ↦ ⟨(KummerPi.mem_base.1 hz).1, fun i _ ↦
    mem_ball_zero_iff.2 ((KummerPi.mem_base.1 hz).2 i).2⟩

lemma Ψ_mem_base {x : Cn.{u} n} (hxV : x ∈ V) (hx : x ∈ N₀) : χ.Ψ x ∈ KummerPi.base χ.B r := by
  obtain ⟨h₁, h₂⟩ := χ.mapsTo hxV
  exact KummerPi.mem_base.2 ⟨h₁, fun i ↦ ⟨(χ.mem_iff x hxV).1 hx i,
    mem_ball_zero_iff.1 (h₂ i (mem_univ i))⟩⟩

lemma Ψ'_mem_N₀ {z : E × (Fin r → ℂ)} (hz : z ∈ KummerPi.base χ.B r) : χ.Ψ' z ∈ N₀ := by
  have hzD := χ.base_subset hz
  refine (χ.mem_iff _ (χ.mapsTo' hzD)).2 fun i ↦ ?_
  rw [χ.right_inv z hzD]
  exact ((KummerPi.mem_base.1 hz).2 i).1

/-- The points of `N°` over `V`, as a subset of `N°`. -/
def punctured (N₀ : (AnalyticSpace.complexAffineSpace.{u} n).Opens) (V : Set (Cn.{u} n)) :
    Set (space N₀) :=
  {y | y.1 ∈ V}

/-- `V ∩ N°` is homeomorphic to `B × (Δ*)ʳ` through `Ψ`. -/
def homeomorph : punctured N₀ V ≃ₜ KummerPi.base χ.B r where
  toFun y := ⟨χ.Ψ y.1.1, χ.Ψ_mem_base y.2 y.1.2⟩
  invFun z := ⟨⟨χ.Ψ' z.1, χ.Ψ'_mem_N₀ z.2⟩, χ.mapsTo' (χ.base_subset z.2)⟩
  left_inv y := Subtype.ext (Subtype.ext (χ.left_inv _ y.2))
  right_inv z := Subtype.ext (χ.right_inv _ (χ.base_subset z.2))
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact χ.differentiableOn.continuousOn.comp_continuous
      (continuous_subtype_val.comp continuous_subtype_val) fun y ↦ y.2
  continuous_invFun := by
    refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
    exact χ.differentiableOn'.continuousOn.comp_continuous continuous_subtype_val
      fun z ↦ χ.base_subset z.2

lemma coe_homeomorph_apply (y : punctured N₀ V) :
    (χ.homeomorph y : E × (Fin r → ℂ)) = χ.Ψ y.1.1 :=
  rfl


/-- The part `B × Δʳ ∩ Ψ'⁻¹(V')` of the chart corresponding to `V' ⊆ V`. -/
def chartSet (V' : Set (Cn.{u} n)) : Set (E × (Fin r → ℂ)) :=
  (χ.B ×ˢ univ.pi fun _ ↦ ball (0 : ℂ) 1) ∩ χ.Ψ' ⁻¹' V'

lemma isOpen_chartSet {V' : Set (Cn.{u} n)} (hV' : IsOpen V') : IsOpen (χ.chartSet V') :=
  χ.differentiableOn'.continuousOn.isOpen_inter_preimage
    (χ.isOpen.prod (isOpen_set_pi finite_univ fun _ _ ↦ isOpen_ball)) hV'

lemma Ψ_mem_chartSet {V' : Set (Cn.{u} n)} (hV' : V' ⊆ V) {x : Cn.{u} n} (hx : x ∈ V') :
    χ.Ψ x ∈ χ.chartSet V' :=
  ⟨χ.mapsTo (hV' hx), by rw [mem_preimage, χ.left_inv _ (hV' hx)]; exact hx⟩

lemma mem_base_of_mem_chartSet {M : ℕ} (hM : M ≠ 0) {V' : Set (Cn.{u} n)}
    {z : E × (Fin r → ℂ)} (hz : KummerPi.powMap M z ∈ χ.chartSet V')
    (hz0 : KummerPi.prodCoord z ≠ 0) : z ∈ KummerPi.base χ.B r := by
  obtain ⟨⟨h₁, h₂⟩, -⟩ := hz
  refine KummerPi.mem_base.2 ⟨h₁, fun k ↦ ⟨Finset.prod_ne_zero_iff.1 hz0 k (Finset.mem_univ k),
    ?_⟩⟩
  have := mem_ball_zero_iff.1 (h₂ k (mem_univ k))
  simp only [KummerPi.powMap, norm_pow] at this
  exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) hM).1 this

variable (W : FiniteEtaleOver (space N₀))

/-- **The Kummer structure of `W` over a normal crossings chart.** There are finitely many
continuous open maps `Φ_c : B × (Δ*)ʳ → W` with disjoint images covering `p⁻¹(V)`, such that
`Ψ(p(Φ_c(u))) = κ_{M_c}(u)` and whose fibres are the orbits of a subgroup `Γ_c ≤ ℤʳ` containing
`M_c ℤʳ`, acting through `KummerPi.rot`. -/
theorem exists_kummer [T2Space W.left] (hV : IsOpen V) :
    ∃ (C : Type u) (_ : Finite C) (M : C → ℕ+) (Γ : C → AddSubgroup (Fin r → ℤ))
      (Φ : C → KummerPi.base χ.B r → W.left), (∀ c a, (M c : ℤ) • a ∈ Γ c) ∧
      (∀ c, Continuous (Φ c)) ∧ (∀ c, IsOpenMap (Φ c)) ∧
      (∀ c u, pt W (Φ c u) ∈ V ∧ χ.Ψ (pt W (Φ c u)) = KummerPi.powMap (M c) u.1) ∧
      (∀ w, pt W w ∈ V → ∃ c u, Φ c u = w) ∧ (∀ c c' u u', Φ c u = Φ c' u' → c = c') ∧
      ∀ c u u', Φ c u = Φ c u' ↔ ∃ a ∈ Γ c, u' = KummerPi.rot χ.B r (M c) a u := by
  set f := (cov W).toLRSHom.base
  have hf : IsCoveringMap f := isCoveringMap_base_of_isFiniteEtale (cov W)
  have hS : IsOpen (punctured N₀ V) := hV.preimage continuous_subtype_val
  set X := f ⁻¹' (punctured N₀ V)
  set p : X → KummerPi.base χ.B r := χ.homeomorph ∘ (punctured N₀ V).restrictPreimage f
  have hp : IsCoveringMap p := (hf.restrictPreimage _).homeomorph_comp _
  have hpx (w : X) : (p w : E × (Fin r → ℂ)) = χ.Ψ (pt W w.1) := rfl
  have hfin (y : KummerPi.base χ.B r) : (p ⁻¹' {y}).Finite := by
    refine ((finite_fiber W (χ.Ψ' y.1)).preimage Subtype.val_injective.injOn).subset ?_
    intro w hw
    change pt W w.1 = χ.Ψ' y.1
    have h₁ : χ.Ψ (pt W w.1) = y.1 := by rw [← hpx]; exact congrArg Subtype.val hw
    rw [← h₁]
    exact (χ.left_inv _ w.2).symm
  obtain ⟨hC, M, Γ, Φ, hM, hcont, hopen, hpΦ, hsurj, hsep, hfib⟩ :=
    hp.exists_sigma_kummerPi χ.convex χ.isOpen hfin
  have hXo : IsOpen (X : Set W.left) := hS.preimage f.hom.continuous
  refine ⟨ZerothHomotopy X, hC, M, Γ, fun c u ↦ (Φ c u).1, hM,
    fun c ↦ continuous_subtype_val.comp (hcont c),
    fun c ↦ hXo.isOpenMap_subtype_val.comp (hopen c), fun c u ↦ ⟨(Φ c u).2, ?_⟩,
    fun w hw ↦ ?_, fun c c' u u' h ↦ hsep c c' u u' (Subtype.ext h),
    fun c u u' ↦ ⟨fun h ↦ (hfib c u u').1 (Subtype.ext h),
      fun h ↦ congrArg Subtype.val ((hfib c u u').2 h)⟩⟩
  · rw [← hpx, hpΦ, KummerPi.cover_apply]
    rfl
  · obtain ⟨c, u, hu⟩ := hsurj ⟨w, hw⟩
    exact ⟨c, u, congrArg Subtype.val hu⟩

/-- **Kummer data** for `W` over a normal crossings chart: finitely many continuous open maps
`Φ_c : B × (Δ*)ʳ → W` with disjoint images covering `p⁻¹(V)`, with `Ψ(p(Φ_c(u))) = κ_{M_c}(u)`,
whose fibres are the orbits of a subgroup `Γ_c ≤ ℤʳ` acting through `KummerPi.rot`. -/
structure KummerData where
  /-- The index set of the Kummer pieces. -/
  C : Type u
  [fintype : Fintype C]
  /-- The degrees of the Kummer pieces. -/
  M : C → ℕ+
  /-- The groups of rotations identifying points of the Kummer pieces. -/
  Γ : C → AddSubgroup (Fin r → ℤ)
  /-- The Kummer pieces. -/
  Φ : C → KummerPi.base χ.B r → W.left
  continuous (c : C) : Continuous (Φ c)
  isOpenMap (c : C) : IsOpenMap (Φ c)
  pt_mem (c : C) (u : KummerPi.base χ.B r) : pt W (Φ c u) ∈ V
  Ψ_pt (c : C) (u : KummerPi.base χ.B r) : χ.Ψ (pt W (Φ c u)) = KummerPi.powMap (M c) u.1
  surj (w : W.left) : pt W w ∈ V → ∃ c u, Φ c u = w
  sep (c c' : C) (u u' : KummerPi.base χ.B r) : Φ c u = Φ c' u' → c = c'
  fib (c : C) (u u' : KummerPi.base χ.B r) :
    Φ c u = Φ c u' ↔ ∃ a ∈ Γ c, u' = KummerPi.rot χ.B r (M c) a u

attribute [instance] KummerData.fintype

theorem nonempty_kummerData [T2Space W.left] (hV : IsOpen V) : Nonempty (χ.KummerData W) := by
  obtain ⟨C, hC, M, Γ, Φ, -, hcont, hopen, hpt, hsurj, hsep, hfib⟩ := χ.exists_kummer W hV
  haveI := Fintype.ofFinite C
  exact ⟨⟨C, M, Γ, Φ, hcont, hopen, fun c u ↦ (hpt c u).1, fun c u ↦ (hpt c u).2, hsurj,
    hsep, hfib⟩⟩

end NCChart

end

end ComplexAnalytic.BoundedSections
