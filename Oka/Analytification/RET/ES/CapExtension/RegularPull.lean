/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.ES.GrauertRemmert.RegularPair

/-!
# Regular pairs pulled back along the projection `ℂ^{m+1} → ℂ^m`

Write the points of `ℂ^{m+1}` as `(b, w)`. If the germs of `g` and `h` at `b₀ ∈ ℂ^m` form a
regular sequence, then so do the germs of `(b, w) ↦ g(b)` and `(b, w) ↦ h(b)` at every point
`(b₀, w₀)` (`ComplexAnalytic.BoundedSections.isWeaklyRegular_pullBase`). Hence a family of regular
pairs on `G ⊆ ℂ^m` pulls back to a family of regular pairs on every set lying over `G`, with zero
set the preimage of the zero set (`RegularPairFamily.pullBase`).

## Proof

In the coordinates in which `w` is the last one, the germs are `incl G`, `incl H` for germs `G`,
`H` in the first variables (`LocalOkaRing.isWeaklyRegular_incl`). If `incl G ∣ incl H · y`,
write `y = a w + incl c` by Weierstrass division by `w`; restricting to `w = 0` gives `G ∣ H c`,
hence `G ∣ c`, and `incl G ∣ incl H · a` since `w` is a nonzerodivisor modulo `incl G`. Iterating,
`y ∈ (incl G) + (wᵏ)` for all `k`, so `y ∈ (incl G)` by Krull's intersection theorem.
-/

open Filter Topology Set RingTheory.Sequence

universe u

namespace LocalOkaRing

variable {n : ℕ}

/-- The last coordinate is a nonzerodivisor modulo `incl G` for `G ≠ 0`. -/
lemma incl_dvd_of_dvd_lastVar_mul {G : LocalOkaRing (Fin n)} (hG : G ≠ 0)
    {z : LocalOkaRing (Fin (n + 1))} (h : incl G ∣ lastVar * z) : incl G ∣ z := by
  obtain ⟨t, ht⟩ := h
  obtain ⟨a, c, rfl⟩ := exists_eq_mul_lastVar_add_incl t
  have hmem : incl (G * c) ∈ Ideal.span {(lastVar : LocalOkaRing (Fin (n + 1)))} := by
    rw [Ideal.mem_span_singleton]
    refine ⟨z - incl G * a, ?_⟩
    rw [map_mul]
    linear_combination (-1 : LocalOkaRing (Fin (n + 1))) * ht
  have hc : c = 0 := (mul_eq_zero.1 (incl_eq_zero_of_mem_span_lastVar hmem)).resolve_left hG
  subst hc
  rw [map_zero, add_zero] at ht
  refine ⟨a, mul_left_cancel₀ (show (lastVar : LocalOkaRing (Fin (n + 1))) ≠ 0 by
    rw [lastVar_eq_coord]; exact coord_ne_zero _) ?_⟩
  rw [ht]
  ring

/-- The last coordinate lies in the maximal ideal. -/
lemma lastVar_mem_maximalIdeal :
    (lastVar : LocalOkaRing (Fin (n + 1))) ∈ IsLocalRing.maximalIdeal _ := by
  rw [mem_maximalIdeal_iff, lastVar_eq_coord]
  exact constantCoeff_coord _

/-- **Regular pairs stay regular after adding a variable.** -/
theorem isWeaklyRegular_incl {G H : LocalOkaRing (Fin n)}
    (hGH : IsWeaklyRegular (LocalOkaRing (Fin n)) [G, H]) :
    IsWeaklyRegular (LocalOkaRing (Fin (n + 1))) [incl G, incl H] := by
  have hG : G ≠ 0 := hGH.ne_zero_of_cons
  have hG' : (incl G : LocalOkaRing (Fin (n + 1))) ≠ 0 := by
    intro h0
    refine hG (incl_eq_zero_of_mem_span_lastVar ?_)
    rw [h0]
    exact Ideal.zero_mem _
  refine isWeaklyRegular_pair (fun a b hab ↦ mul_left_cancel₀ hG' hab) fun y hy ↦ ?_
  -- `y ∈ (incl G) + (wᵏ)` for all `k`
  have key : ∀ k : ℕ, ∃ q r : LocalOkaRing (Fin (n + 1)),
      y = incl G * q + lastVar ^ k * r ∧ incl G ∣ incl H * r := by
    intro k
    induction k with
    | zero => exact ⟨0, y, by ring, hy⟩
    | succ k ih =>
      obtain ⟨q, r, hyr, e, he⟩ := ih
      obtain ⟨a, c, rfl⟩ := exists_eq_mul_lastVar_add_incl r
      obtain ⟨e₁, e₀, rfl⟩ := exists_eq_mul_lastVar_add_incl e
      have hmem : incl (H * c - G * e₀) ∈
          Ideal.span {(lastVar : LocalOkaRing (Fin (n + 1)))} := by
        rw [Ideal.mem_span_singleton]
        refine ⟨incl G * e₁ - incl H * a, ?_⟩
        rw [map_sub, map_mul, map_mul]
        linear_combination he
      have hc : G ∣ H * c := ⟨e₀, sub_eq_zero.1 (incl_eq_zero_of_mem_span_lastVar hmem)⟩
      obtain ⟨c', rfl⟩ := hGH.dvd_of_dvd_mul hc
      have hdvd : incl G ∣ lastVar * (incl H * a) := by
        refine ⟨e₁ * lastVar + incl e₀ - incl H * incl c', ?_⟩
        rw [map_mul] at he
        linear_combination he
      refine ⟨q + lastVar ^ k * incl c', a, ?_, incl_dvd_of_dvd_lastVar_mul hG hdvd⟩
      rw [hyr, map_mul]
      ring
  -- Krull's intersection theorem in `B ⧸ (incl G)`
  set I : Ideal (LocalOkaRing (Fin (n + 1))) := Ideal.span {incl G}
  have hbot := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing
    (M := LocalOkaRing (Fin (n + 1)) ⧸ I) (IsLocalRing.maximalIdeal (LocalOkaRing (Fin (n + 1))))
    (IsLocalRing.maximalIdeal.isMaximal (LocalOkaRing (Fin (n + 1)))).ne_top
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem]
  change Submodule.Quotient.mk (p := I) y = 0
  rw [← Submodule.mem_bot (LocalOkaRing (Fin (n + 1))), ← hbot, Submodule.mem_iInf]
  intro k
  obtain ⟨q, r, hyr, -⟩ := key k
  rw [hyr, Submodule.Quotient.mk_add, (Submodule.Quotient.mk_eq_zero I).2
    (Ideal.mem_span_singleton.2 (dvd_mul_right _ _)), zero_add]
  have hmem : lastVar ^ k * r ∈ (IsLocalRing.maximalIdeal (LocalOkaRing (Fin (n + 1)))) ^ k •
      (⊤ : Submodule (LocalOkaRing (Fin (n + 1))) (LocalOkaRing (Fin (n + 1)))) := by
    rw [smul_eq_mul, Ideal.mul_top]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow lastVar_mem_maximalIdeal k)
  have hb' := Submodule.mem_map_of_mem (f := I.mkQ) hmem
  rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ] at hb'
  exact hb'

end LocalOkaRing

namespace ComplexAnalytic.BoundedSections

open LocalOkaRing Cap

noncomputable section

variable {m : ℕ}

/-- Weakly regular pairs are transported by ring isomorphisms. -/
lemma isWeaklyRegular_pair_map {R S : Type*} [CommRing R] [CommRing S] (φ : R ≃+* S) {g h : R}
    (H : IsWeaklyRegular R [g, h]) : IsWeaklyRegular S [φ g, φ h] :=
  (AddEquiv.isWeaklyRegular_congr (e := φ.toAddEquiv) (as := [g, h]) (bs := [g, h].map φ)
    (List.forall₂_map_right_iff.2 (List.forall₂_same.2 fun r _ x ↦ map_mul φ r x))).1 H

/-- The germ at `z` of `(b, w) ↦ g(b)`, for a germ `G` of `g` at `baseOf z`. -/
def pullBaseGerm (G : LocalOkaRing (ULift.{u} (Fin m))) : LocalOkaRing (ULift.{u} (Fin (m + 1))) :=
  LocalOkaRing.congr (rotCoord.{u} m)
    (incl (LocalOkaRing.congr (LocalOkaRing.uliftCoord.{u} (Fin m)).symm G))

lemma isWeaklyRegular_pullBaseGerm {G H : LocalOkaRing (ULift.{u} (Fin m))}
    (hGH : IsWeaklyRegular (LocalOkaRing (ULift.{u} (Fin m))) [G, H]) :
    IsWeaklyRegular (LocalOkaRing (ULift.{u} (Fin (m + 1)))) [pullBaseGerm G, pullBaseGerm H] :=
  isWeaklyRegular_pair_map (LocalOkaRing.congr (rotCoord.{u} m)).toRingEquiv
    (isWeaklyRegular_incl (isWeaklyRegular_pair_map
      (LocalOkaRing.congr (LocalOkaRing.uliftCoord.{u} (Fin m)).symm).toRingEquiv hGH))

lemma represents_pullBaseGerm {G : LocalOkaRing (ULift.{u} (Fin m))} {g : Cm.{u} m → ℂ}
    {z : Cn.{u} (m + 1)} (hG : (G : MvPowerSeries _ ℂ).Represents (fun v ↦ g (v + baseOf z))) :
    ((pullBaseGerm G : LocalOkaRing (ULift.{u} (Fin (m + 1)))) : MvPowerSeries _ ℂ).Represents
      (fun v ↦ g (baseOf (v + z))) := by
  set e := rotCoord.{u} m
  set ι := LocalOkaRing.uliftCoord.{u} (Fin m)
  have h₀ := congr_represents (φ := ι.symm) hG
  have h₁ : ((incl (LocalOkaRing.congr ι.symm G) : LocalOkaRing (Fin (m + 1))) :
      MvPowerSeries (Fin (m + 1)) ℂ).Represents (fun y ↦ g (ι (Fin.init y) + baseOf z)) :=
    MvPowerSeries.Represents.rename_castSucc h₀
  refine (congr_represents (φ := e) h₁).congr (Eventually.of_forall fun v ↦ ?_)
  have hs := (Prod.ext_iff.1 (splitEquiv_rotCoord.{u} (e.symm v))).1
  rw [ContinuousLinearEquiv.apply_symm_apply] at hs
  change g (ι (Fin.init (e.symm v)) + baseOf z) = g (baseOf (v + z))
  rw [baseOf_add]
  exact congrArg (fun b ↦ g (b + baseOf z)) hs.symm

/-- **Regular pairs pulled back to `ℂ^{m+1}`**: if some germs of `g` and `h` at `baseOf z` form a
regular sequence, then so do some germs of `(b, w) ↦ g(b)` and `(b, w) ↦ h(b)` at `z`. -/
theorem isWeaklyRegular_pullBase {g h : Cm.{u} m → ℂ} {z : Cn.{u} (m + 1)}
    (H : ∃ G H : LocalOkaRing (ULift.{u} (Fin m)),
      (G : MvPowerSeries _ ℂ).Represents (fun v ↦ g (v + baseOf z)) ∧
      (H : MvPowerSeries _ ℂ).Represents (fun v ↦ h (v + baseOf z)) ∧
      IsWeaklyRegular (LocalOkaRing (ULift.{u} (Fin m))) [G, H]) :
    ∃ G H : LocalOkaRing (ULift.{u} (Fin (m + 1))),
      (G : MvPowerSeries _ ℂ).Represents (fun v ↦ (g ∘ baseOf) (v + z)) ∧
      (H : MvPowerSeries _ ℂ).Represents (fun v ↦ (h ∘ baseOf) (v + z)) ∧
      IsWeaklyRegular (LocalOkaRing (ULift.{u} (Fin (m + 1)))) [G, H] := by
  obtain ⟨G, H, hG, hH, hGH⟩ := H
  exact ⟨pullBaseGerm G, pullBaseGerm H, represents_pullBaseGerm hG, represents_pullBaseGerm hH,
    isWeaklyRegular_pullBaseGerm hGH⟩

end

end ComplexAnalytic.BoundedSections

namespace RegularPairFamily

open ComplexAnalytic.BoundedSections ComplexAnalytic.Cap

variable {m : ℕ} {G : Set (Cm.{u} m)} (R : RegularPairFamily G)

/-- **A family of regular pairs pulled back to `ℂ^{m+1}`**: the pairs `(gᵢ(b), hᵢ(b))` on a set
`U` of points `(b, w)` with `b ∈ G`. -/
noncomputable def pullBase {U : Set (Cn.{u} (m + 1))} (hU : ∀ x ∈ U, baseOf x ∈ G) :
    RegularPairFamily U where
  k := R.k
  g i := R.g i ∘ baseOf
  h i := R.h i ∘ baseOf
  continuousOn_g i := (R.continuousOn_g i).comp continuous_baseOf.continuousOn hU
  continuousOn_h i := (R.continuousOn_h i).comp continuous_baseOf.continuousOn hU
  isWeaklyRegular i z hz hg hh := isWeaklyRegular_pullBase (R.isWeaklyRegular i _ (hU z hz) hg hh)

lemma zeroSet_pullBase {U : Set (Cn.{u} (m + 1))} (hU : ∀ x ∈ U, baseOf x ∈ G) :
    (R.pullBase hU).zeroSet = baseOf ⁻¹' R.zeroSet := by
  ext x
  simp [zeroSet, zeroSetOf, pullBase]

/-- A family of regular pairs restricts to subsets. -/
def restrict {U : Set (Cm.{u} m)} (hU : U ⊆ G) : RegularPairFamily U where
  k := R.k
  g := R.g
  h := R.h
  continuousOn_g i := (R.continuousOn_g i).mono hU
  continuousOn_h i := (R.continuousOn_h i).mono hU
  isWeaklyRegular i z hz := R.isWeaklyRegular i z (hU hz)

@[simp]
lemma zeroSet_restrict {U : Set (Cm.{u} m)} (hU : U ⊆ G) : (R.restrict hU).zeroSet = R.zeroSet :=
  rfl

end RegularPairFamily
