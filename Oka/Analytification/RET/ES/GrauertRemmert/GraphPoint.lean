/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.ES.Codim2.BPoint
import Oka.Analytification.RET.ES.GrauertRemmert.WeierstrassForm

/-!
# Weierstrass forms near smooth points of the discriminant locus

Keep the notation of `Oka/Analytification/RET/ES/GrauertRemmert/WeierstrassForm.lean`, with
`m = m' + 1`, and write the points of the base `ℂ^{m'+1}` as `(y, v)`, `y ∈ ℂ^{m'}`. Suppose that
near a point `b₀ = (y₀, v₀)` of `G` the polynomial `P(b)` is separable off the graph of a
holomorphic function `v = φ(y)` through `b₀`. In the coordinates `(y, t, w)`, `t = v - φ(y)`, the
polynomial `P` is separable for `t ≠ 0`: `b₀` is a b-point
(`ComplexAnalytic.BoundedSections.BPointData`). Hence the bounded sections satisfy the local
conditions for coherence at every point over `b₀`
(`ComplexAnalytic.BoundedSections.WeierstrassForm.isCoherentAt_of_graph`), by
`ComplexAnalytic.BoundedSections.BPointData.isCoherent` and the transfer along the change of
coordinates `ComplexAnalytic.BoundedSections.LocalBiholo.isCoherentAt_of_forall`.
-/

open CategoryTheory Opposite AlgebraicGeometry Topology TopologicalSpace Filter Set Metric
  Polynomial

universe u

namespace ComplexAnalytic.BoundedSections

open AnalyticSpace KummerModel Cap

noncomputable section

variable {m : ℕ}

/-! ### The coordinates `(y, v, w)` of `ℂ^{m+2}` -/

section Coords

/-- The coordinates `y` of `(y, v, w) ∈ ℂ^{m+2}`. -/
abbrev yOf (x : Cn.{u} (m + 2)) : Cm.{u} m := baseOf (baseOf x)

/-- The coordinate `v` of `(y, v, w) ∈ ℂ^{m+2}`. -/
abbrev vOf (x : Cn.{u} (m + 2)) : ℂ := fibOf (baseOf x)

/-- The point `(y, v, w)` of `ℂ^{m+2}`. -/
abbrev mkPt₃ (y : Cm.{u} m) (v w : ℂ) : Cn.{u} (m + 2) := mkPt (mkPt y v) w

/-- The index of the coordinate `v`. -/
abbrev vIdx : ULift.{u} (Fin (m + 2)) := ⟨Fin.succ 0⟩

@[simp]
lemma yOf_mkPt₃ (y : Cm.{u} m) (v w : ℂ) : yOf (mkPt₃ y v w) = y := by
  simp [yOf, mkPt₃]

@[simp]
lemma vOf_mkPt₃ (y : Cm.{u} m) (v w : ℂ) : vOf (mkPt₃ y v w) = v := by
  simp [vOf, mkPt₃]

lemma fibOf_mkPt₃ (y : Cm.{u} m) (v w : ℂ) : fibOf (mkPt₃ y v w) = w := by
  simp [mkPt₃]

lemma mkPt₃_yOf (x : Cn.{u} (m + 2)) : mkPt₃ (yOf x) (vOf x) (fibOf x) = x := by
  rw [mkPt₃, mkPt_baseOf_fibOf, mkPt_baseOf_fibOf]

lemma vOf_eq (x : Cn.{u} (m + 2)) : vOf x = x vIdx :=
  rfl

lemma fibOf_eq (x : Cn.{u} (m + 2)) : fibOf x = x zero :=
  rfl

lemma baseOf_update_zero (x : Cn.{u} (m + 1)) (a : ℂ) :
    baseOf (Function.update x zero a) = baseOf x := by
  funext i
  change Function.update x zero a ⟨i.down.succ⟩ = x ⟨i.down.succ⟩
  exact Function.update_of_ne (fun h ↦ Fin.succ_ne_zero _ (congrArg ULift.down h)) a x

lemma yOf_update_vIdx (x : Cn.{u} (m + 2)) (a : ℂ) :
    yOf (Function.update x vIdx a) = yOf x := by
  funext i
  change Function.update x vIdx a ⟨i.down.succ.succ⟩ = x ⟨i.down.succ.succ⟩
  exact Function.update_of_ne (fun h ↦ Fin.succ_ne_zero _
    (Fin.succ_injective _ (congrArg ULift.down h))) a x

lemma yOf_baseProj (x : Cn.{u} (m + 2)) : yOf (baseProj vIdx zero x) = yOf x := by
  rw [baseProj, yOf, baseOf_update_zero, ← yOf, yOf_update_vIdx]

lemma differentiable_yOf : Differentiable ℂ (yOf.{u} (m := m)) :=
  (differentiable_baseOf.{u} (m := m)).comp (differentiable_baseOf.{u} (m := m + 1))

lemma differentiable_vOf : Differentiable ℂ (vOf.{u} (m := m)) :=
  (differentiable_fibOf.{u} (m := m)).comp (differentiable_baseOf.{u} (m := m + 1))

lemma differentiable_mkPt₃ :
    Differentiable ℂ fun p : Cm.{u} m × ℂ × ℂ ↦ mkPt₃ p.1 p.2.1 p.2.2 :=
  differentiable_mkPt.comp
    ((differentiable_mkPt.comp (differentiable_fst.prodMk differentiable_snd.fst)).prodMk
      differentiable_snd.snd)

lemma yOf_add_smul (a b : ℝ) (x z : Cn.{u} (m + 2)) :
    yOf (a • x + b • z) = a • yOf x + b • yOf z :=
  rfl

lemma convex_preimage_yOf {s : Set (Cm.{u} m)} (hs : Convex ℝ s) :
    Convex ℝ (yOf ⁻¹' s) := fun x hx z hz a b ha hb hab ↦ by
  rw [mem_preimage, yOf_add_smul]
  exact hs hx hz ha hb hab

end Coords

namespace WeierstrassForm

variable {m' : ℕ} {N N₀ : (AnalyticSpace.complexAffineSpace.{u} (m' + 2)).Opens}
  (F : WeierstrassForm N N₀)

/-- **Coherence over a b-point.** Let `b₀ = (y₀, v₀) ∈ G` and let `φ` be holomorphic near `y₀`
with `φ(y₀) = v₀`, such that `P(y, v)` is separable for `(y, v)` near `b₀` off the graph
`v = φ(y)`. Then the bounded sections of every Hausdorff finite étale cover of `N°` satisfy the
local conditions for coherence at every point over `b₀`. -/
theorem isCoherentAt_of_graph (h₀ : N₀ ≤ N) (W : FiniteEtaleOver (space N₀)) [T2Space W.left]
    {b₀ : Cm.{u} (m' + 1)} (hb₀ : b₀ ∈ F.G) {φ : Cm.{u} m' → ℂ} {r ε : ℝ} (hr : 0 < r)
    (hε : 0 < ε) (hφd : DifferentiableOn ℂ φ (ball (baseOf b₀) r))
    (hφb : φ (baseOf b₀) = fibOf b₀)
    (hgraph : ∀ b ∈ F.G, baseOf b ∈ ball (baseOf b₀) r → ‖fibOf b - fibOf b₀‖ < ε →
      fibOf b ≠ φ (baseOf b) → (evalPoly F.P b).Separable)
    (x : space N) (hx : baseOf x.1 = b₀) : IsCoherentAt h₀ W x := by
  set c := baseOf b₀
  set d := fibOf b₀
  -- a product neighbourhood of `b₀` in `G`
  have hmk : Continuous fun p : Cm.{u} m' × ℂ ↦ mkPt p.1 p.2 := differentiable_mkPt.continuous
  obtain ⟨δ, hδ, hδG⟩ := Metric.isOpen_iff.1 (F.isOpen_G.preimage hmk) (c, d) (by
    change mkPt c d ∈ F.G
    rw [mkPt_baseOf_fibOf]
    exact hb₀)
  set ε₁ := min (ε / 2) (δ / 2)
  have hε₁ : 0 < ε₁ := lt_min (half_pos hε) (half_pos hδ)
  have hφc : ContinuousAt φ c := (hφd.continuousOn.continuousAt (isOpen_ball.mem_nhds
    (mem_ball_self hr)))
  obtain ⟨r₁', hr₁', hφr₁⟩ := Metric.continuousAt_iff.1 hφc ε₁ hε₁
  set r₁ := min (min r δ) r₁'
  have hr₁ : 0 < r₁ := lt_min (lt_min hr hδ) hr₁'
  have hr₁r : ball c r₁ ⊆ ball c r := ball_subset_ball ((min_le_left _ _).trans (min_le_left _ _))
  have hφnear : ∀ y ∈ ball c r₁, ‖φ y - d‖ < ε₁ := fun y hy ↦ by
    have := hφr₁ (hy.trans_le (min_le_right _ _))
    rwa [dist_eq_norm, hφb] at this
  have hinG : ∀ y ∈ ball c r₁, ∀ v : ℂ, ‖v - d‖ < 2 * ε₁ → mkPt y v ∈ F.G := fun y hy v hv ↦ by
    have h : (y, v) ∈ ball (c, d) δ := by
      rw [mem_ball, Prod.dist_eq, max_lt_iff]
      refine ⟨hy.trans_le ((min_le_left _ _).trans (min_le_right _ _)), ?_⟩
      rw [dist_eq_norm]
      linarith [min_le_right (ε / 2) (δ / 2)]
    exact hδG h
  -- the change of coordinates `t = v - φ(y)`
  set Φ : Cn.{u} (m' + 2) → Cn.{u} (m' + 2) := fun x ↦ mkPt₃ (yOf x) (vOf x + φ (yOf x)) (fibOf x)
  set Ψ : Cn.{u} (m' + 2) → Cn.{u} (m' + 2) := fun z ↦ mkPt₃ (yOf z) (vOf z - φ (yOf z)) (fibOf z)
  have hφy : DifferentiableOn ℂ (fun x ↦ φ (yOf x)) (yOf ⁻¹' ball c r₁) :=
    (hφd.mono hr₁r).comp differentiable_yOf.differentiableOn fun _ h ↦ h
  have hΦd : DifferentiableOn ℂ Φ (yOf ⁻¹' ball c r₁) := fun x hx ↦
    (differentiable_mkPt₃ (yOf x, vOf x + φ (yOf x), fibOf x)).comp_differentiableWithinAt
      (f := fun x ↦ (yOf x, vOf x + φ (yOf x), fibOf x)) x
      (differentiable_yOf.differentiableAt.differentiableWithinAt.prodMk
        ((differentiable_vOf.differentiableAt.differentiableWithinAt.add (hφy x hx)).prodMk
          differentiable_fibOf.differentiableAt.differentiableWithinAt))
  have hΨd : DifferentiableOn ℂ Ψ (yOf ⁻¹' ball c r₁) := fun x hx ↦
    (differentiable_mkPt₃ (yOf x, vOf x - φ (yOf x), fibOf x)).comp_differentiableWithinAt
      (f := fun x ↦ (yOf x, vOf x - φ (yOf x), fibOf x)) x
      (differentiable_yOf.differentiableAt.differentiableWithinAt.prodMk
        ((differentiable_vOf.differentiableAt.differentiableWithinAt.sub (hφy x hx)).prodMk
          differentiable_fibOf.differentiableAt.differentiableWithinAt))
  set A : (AnalyticSpace.complexAffineSpace.{u} (m' + 2)).Opens :=
    ⟨{x | yOf x ∈ ball c r₁ ∧ ‖vOf x‖ < ε₁ ∧ ‖fibOf x‖ < F.ρ}, by
      change IsOpen (yOf ⁻¹' ball c r₁ ∩ ({x | ‖vOf x‖ < ε₁} ∩ {x | ‖fibOf x‖ < F.ρ}))
      exact (isOpen_ball.preimage differentiable_yOf.continuous).inter
        ((isOpen_lt differentiable_vOf.continuous.norm continuous_const).inter
          (isOpen_lt continuous_fibOf.norm continuous_const))⟩
  set E : Set (Cn.{u} (m' + 2)) :=
    {z | yOf z ∈ ball c r₁ ∧ ‖vOf z - φ (yOf z)‖ < ε₁ ∧ ‖fibOf z‖ < F.ρ}
  have hE : IsOpen E := by
    have h := ((differentiable_vOf.continuous.continuousOn.sub hφy.continuousOn).norm)
      |>.isOpen_inter_preimage
      (isOpen_ball.preimage differentiable_yOf.continuous) (isOpen_Iio (a := ε₁))
    have hEeq : E = (yOf ⁻¹' ball c r₁ ∩ (fun z ↦ ‖vOf z - φ (yOf z)‖) ⁻¹' Iio ε₁) ∩
        {z | ‖fibOf z‖ < F.ρ} := by
      ext z
      simp only [E, mem_setOf_eq, mem_inter_iff, mem_preimage, mem_Iio, and_assoc]
    rw [hEeq]
    exact h.inter (isOpen_lt continuous_fibOf.norm continuous_const)
  have hyΦ : ∀ x, yOf (Φ x) = yOf x := fun x ↦ yOf_mkPt₃ _ _ _
  have hvΦ : ∀ x, vOf (Φ x) = vOf x + φ (yOf x) := fun x ↦ vOf_mkPt₃ _ _ _
  have hwΦ : ∀ x, fibOf (Φ x) = fibOf x := fun x ↦ fibOf_mkPt₃ _ _ _
  have hyΨ : ∀ z, yOf (Ψ z) = yOf z := fun z ↦ yOf_mkPt₃ _ _ _
  have hvΨ : ∀ z, vOf (Ψ z) = vOf z - φ (yOf z) := fun z ↦ vOf_mkPt₃ _ _ _
  have hwΨ : ∀ z, fibOf (Ψ z) = fibOf z := fun z ↦ fibOf_mkPt₃ _ _ _
  have hbaseΦ : ∀ x, baseOf (Φ x) = mkPt (yOf x) (vOf x + φ (yOf x)) := fun x ↦ baseOf_mkPt _ _
  have hnear : ∀ x, yOf x ∈ ball c r₁ → ‖vOf x‖ < ε₁ → ‖vOf x + φ (yOf x) - d‖ < 2 * ε₁ :=
    fun x hy hv ↦ by
      calc ‖vOf x + φ (yOf x) - d‖ = ‖vOf x + (φ (yOf x) - d)‖ := by ring_nf
        _ ≤ ‖vOf x‖ + ‖φ (yOf x) - d‖ := norm_add_le _ _
        _ < ε₁ + ε₁ := add_lt_add hv (hφnear _ hy)
        _ = 2 * ε₁ := by ring
  have hEN : ∀ z ∈ E, z ∈ N := fun z hz ↦ (F.mem_N z).2 ⟨by
    rw [← mkPt_baseOf_fibOf (baseOf z)]
    refine hinG _ hz.1 _ ?_
    calc ‖vOf z - d‖ = ‖(vOf z - φ (yOf z)) + (φ (yOf z) - d)‖ := by ring_nf
      _ ≤ ‖vOf z - φ (yOf z)‖ + ‖φ (yOf z) - d‖ := norm_add_le _ _
      _ < ε₁ + ε₁ := add_lt_add hz.2.1 (hφnear _ hz.1)
      _ = 2 * ε₁ := by ring, hz.2.2⟩
  have hmapsΦ : ∀ x : Cn.{u} (m' + 2), x ∈ A → Φ x ∈ E := fun x hx ↦
    ⟨by rw [hyΦ]; exact hx.1, by rw [hvΦ, hyΦ, add_sub_cancel_right]; exact hx.2.1,
      by rw [hwΦ]; exact hx.2.2⟩
  have hmapsΨ : ∀ z : Cn.{u} (m' + 2), z ∈ E → Ψ z ∈ A := fun z hz ↦
    ⟨by rw [hyΨ]; exact hz.1, by rw [hvΨ]; exact hz.2.1, by rw [hwΨ]; exact hz.2.2⟩
  have hΨΦ : ∀ x : Cn.{u} (m' + 2), Ψ (Φ x) = x := fun x ↦ by
    change mkPt₃ (yOf (Φ x)) (vOf (Φ x) - φ (yOf (Φ x))) (fibOf (Φ x)) = x
    rw [hyΦ, hvΦ, hwΦ, add_sub_cancel_right, mkPt₃_yOf]
  have hΦΨ : ∀ z : Cn.{u} (m' + 2), Φ (Ψ z) = z := fun z ↦ by
    change mkPt₃ (yOf (Ψ z)) (vOf (Ψ z) + φ (yOf (Ψ z))) (fibOf (Ψ z)) = z
    rw [hyΨ, hvΨ, hwΨ, sub_add_cancel, mkPt₃_yOf]
  let B : LocalBiholo N :=
    { A := A
      E := E
      isOpen_E := hE
      E_sub := hEN
      Φ := Φ
      Ψ := Ψ
      differentiableOn_Φ := hΦd.mono fun x hx ↦ hx.1
      differentiableOn_Ψ := hΨd.mono fun z hz ↦ hz.1
      mapsTo_Φ := hmapsΦ
      mapsTo_Ψ := hmapsΨ
      Ψ_Φ := fun x _ ↦ hΨΦ x
      Φ_Ψ := fun z _ ↦ hΦΨ z }
  -- the data at the b-point
  have hΦbase : ∀ x, yOf x ∈ ball c r₁ →
      DifferentiableAt ℂ (fun x ↦ baseOf (Φ x)) x := fun x hx ↦
    DifferentiableAt.comp (g := baseOf.{u} (m := m' + 1)) (f := Φ) x (differentiable_baseOf _)
      ((hΦd x hx).differentiableAt ((isOpen_ball.preimage differentiable_yOf.continuous).mem_nhds
        hx))
  have hupd : ∀ x a, Φ (Function.update x zero a) = Function.update (Φ x) zero a := fun x a ↦ by
    have h₁ : yOf (Function.update x zero a) = yOf x := by
      rw [yOf, baseOf_update_zero]
    have h₂ : vOf (Function.update x zero a) = vOf x := by
      rw [vOf, baseOf_update_zero]
    have h₃ : fibOf (Function.update x zero a) = a := by
      change Function.update x zero a zero = a
      exact Function.update_self _ _ _
    change mkPt₃ (yOf (Function.update x zero a)) (vOf (Function.update x zero a) +
      φ (yOf (Function.update x zero a))) (fibOf (Function.update x zero a)) = _
    rw [h₁, h₂, h₃]
    rw [← mkPt_baseOf_fibOf (Function.update (Φ x) zero a), baseOf_update_zero, hbaseΦ]
    rfl
  have dB : BPointData B.A (B.A₀ N₀) :=
    { it := vIdx
      iw := zero
      it_ne_iw := fun h ↦ Fin.succ_ne_zero (0 : Fin (m' + 1)) (congrArg ULift.down h)
      P := F.P.map (precompHom fun x ↦ baseOf (Φ x))
      monic := F.monic.map _
      coeff_update := fun k x a ↦ by
        rw [coeff_map_precompHom, Function.comp_apply, Function.comp_apply, hupd,
          baseOf_update_zero]
      G := yOf ⁻¹' ball c r₁
      convex := convex_preimage_yOf (convex_ball _ _)
      isOpen := isOpen_ball.preimage differentiable_yOf.continuous
      r := ε₁
      pos := hε₁
      mem_region := fun x hx ↦ ⟨by rw [mem_preimage, yOf_baseProj]; exact hx.1, hx.2.1⟩
      differentiableOn_coeff := fun k x hx ↦ by
        have hy : yOf x ∈ ball c r₁ := by
          have := hx.1
          rwa [mem_preimage, yOf_baseProj] at this
        rw [coeff_map_precompHom]
        refine (((F.differentiableOn_coeff k).differentiableAt (F.isOpen_G.mem_nhds ?_)).comp x
          (hΦbase x hy)).differentiableWithinAt
        rw [hbaseΦ]
        exact hinG _ hy _ (hnear x hy hx.2)
      separable := fun x hxG hxr ht ↦ by
        have hy : yOf x ∈ ball c r₁ := by rwa [mem_preimage, yOf_baseProj] at hxG
        change (evalPoly (F.P.map (precompHom fun x ↦ baseOf (Φ x))) x).Separable
        rw [evalPoly_map_precompHom, hbaseΦ]
        have hv := hnear x hy hxr
        refine hgraph _ (hinG _ hy _ hv) (by rw [baseOf_mkPt]; exact hr₁r hy) ?_ ?_
        · rw [fibOf_mkPt]
          linarith [min_le_left (ε / 2) (δ / 2)]
        · rw [fibOf_mkPt, baseOf_mkPt]
          intro h
          exact ht (by rw [← vOf_eq x]; simpa using h)
      mem_iff := fun x hx ↦ by
        change x ∈ B.A ∧ Φ x ∈ N₀ ↔ _
        rw [and_iff_right hx]
        refine (F.mem_N₀ (Φ x) (hEN _ (B.mapsTo_Φ x hx))).trans ?_
        change _ ↔ (evalPoly (F.P.map (precompHom fun x ↦ baseOf (Φ x))) x).eval (fibOf x) ≠ 0
        rw [evalPoly_map_precompHom, hwΦ] }
  have hxE : x.1 ∈ E := by
    obtain ⟨-, hxρ⟩ := (F.mem_N x.1).1 x.2
    have hyx : yOf x.1 = c := by rw [yOf, hx]
    have hvx : vOf x.1 = d := by rw [vOf, hx]
    refine ⟨by rw [hyx]; exact mem_ball_self hr₁, ?_, hxρ⟩
    rw [hyx, hvx, ← hφb, sub_self, norm_zero]
    exact hε₁
  exact B.isCoherentAt_of_forall (F.outPt_not_mem h₀) h₀ W
    (fun W' _ y ↦ IsCoherentAt.of_isCoherent _ _ (dB.isCoherent (B.A₀_le N₀) W') y) hxE

end WeierstrassForm

end

end ComplexAnalytic.BoundedSections
