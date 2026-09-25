/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.ES.Codim2.CoverFunctions
import Oka.Analytification.RET.ES.Codim2.PuiseuxCoord

/-!
# Bounded sections under Puiseux base change

Keep the notation of `Oka/Analytification/RET/ES/BoundedSections.lean`. Let `i₀` be a coordinate
`t` of `ℂⁿ`, `s > 0` and `α = Kummer.coordPow i₀ s : (…, t, …) ↦ (…, tˢ, …)`. Let
`N' = α⁻¹(N)`, `N₀' = α⁻¹(N₀)`, and let `p' : W' ⟶ N₀'` be a finite étale cover with a continuous
map `β : W' → W` over `α` which identifies `W'` with the fibre product `W ×_{N₀} N₀'` at the level
of points (`ComplexAnalytic.BoundedSections.IsPuiseuxPullback`). Write `𝒜` and `𝒜'` for the
sheaves of bounded sections of `W` and of `W'`, and `V' = α⁻¹(V)` for `V ⊆ N`
(`ComplexAnalytic.BoundedSections.pullOpens`).

The group of `s`-th roots of unity acts on `W'` over `t ↦ ζ t` (`…IsPuiseuxPullback.rotW`), and:

1. Pulling back along `β` identifies `𝒜(V)` with the invariant sections of `𝒜'(V')`
   (`…IsPuiseuxPullback.pullSec`, `…IsPuiseuxPullback.descend`,
   `…IsPuiseuxPullback.descend_pullSec`, `…IsPuiseuxPullback.pullSec_descend`). An invariant section
   `b` descends to a function `f` on `W`; near a point of `W` choose a continuous local section `σ`
   of `p`, so that `f ∘ σ ∘ α = b ∘ τ` for a continuous local section `τ` of `p'`; hence
   `f ∘ σ ∘ α` is holomorphic, and so is `f ∘ σ` by `Kummer.differentiableOn_of_comp_coordPow`.
   Boundedness descends because the roots of `tˢ` depend continuously on `t`.
2. The Reynolds operator `R(b) = s⁻¹ ∑_ζ ζ · b` (`…IsPuiseuxPullback.reynolds`) maps `𝒜'(V')` onto
   the invariant sections and is linear over the holomorphic functions pulled back from `V`
   (`…IsPuiseuxPullback.reynolds_pullFun_smul`).

## Main definitions

- `ComplexAnalytic.BoundedSections.IsPuiseuxPullback i₀ s W W' β`: `W'` is the base change of `W`
  along `α`.
- `…IsPuiseuxPullback.rotW`: the action of the `s`-th roots of unity on `W'`.
- `…IsPuiseuxPullback.pullSec`, `…IsPuiseuxPullback.descend`, `…IsPuiseuxPullback.reynolds`.

## Main results

- `…IsPuiseuxPullback.continuousAt_of_lift`: lifts to `W'` of continuous data are continuous.
- `…IsPuiseuxPullback.descend_pullSec`, `…IsPuiseuxPullback.pullSec_descend`: `𝒜(V)` is the
  invariant part of `𝒜'(V')`.
- `…IsPuiseuxPullback.isInvariant_reynolds`, `…IsPuiseuxPullback.reynolds_of_isInvariant`: the
  Reynolds operator is a projection onto the invariant sections.
-/

open CategoryTheory Opposite AlgebraicGeometry Topology TopologicalSpace Filter Kummer

universe u

namespace ComplexAnalytic.BoundedSections

open AnalyticSpace

noncomputable section

variable {n : ℕ} (i₀ : ULift.{u} (Fin n)) (s : ℕ)
  {N N₀ N' N₀' : (AnalyticSpace.complexAffineSpace.{u} n).Opens}

/-- **`W'` is the base change of `W` along the Puiseux map** `α = Kummer.coordPow i₀ s`, at the
level of points: `N₀' = α⁻¹(N₀)`, and `β : W' → W` is a continuous map over `α` such that every
pair of a point `w ∈ W` and a point `x'` with `α(x') = p(w)` comes from exactly one point of
`W'`. -/
structure IsPuiseuxPullback (W : FiniteEtaleOver (space N₀)) (W' : FiniteEtaleOver (space N₀'))
    (β : W'.left → W.left) : Prop where
  pos : 0 < s
  mem_iff : ∀ x, x ∈ N₀' ↔ coordPow i₀ s x ∈ N₀
  continuous : Continuous β
  pt_eq : ∀ w, pt W (β w) = coordPow i₀ s (pt W' w)
  ext : ∀ w₁ w₂, pt W' w₁ = pt W' w₂ → β w₁ = β w₂ → w₁ = w₂
  exists_lift : ∀ w x, pt W w = coordPow i₀ s x → ∃ w', pt W' w' = x ∧ β w' = w

variable (N') in
/-- The open `α⁻¹(V)` of `N'`. -/
def pullOpens (V : (space N).Opens) : (space N').Opens :=
  ⟨{y | coordPow i₀ s y.1 ∈ img V},
    (img V).isOpen.preimage ((continuous_coordPow s).comp continuous_subtype_val)⟩

variable {i₀ s}

lemma mem_img_pullOpens (hN : ∀ x, x ∈ N' ↔ coordPow i₀ s x ∈ N) {V : (space N).Opens}
    {x : Cn.{u} n} : x ∈ img (pullOpens i₀ s N' V) ↔ coordPow i₀ s x ∈ img V := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨_, hx⟩ := mem_img_iff.1 h
    exact hx
  · exact mem_img_iff.2 ⟨(hN x).2 (img_le V _ h), h⟩

lemma pullOpens_mono {V V' : (space N).Opens} (h : V' ≤ V) :
    pullOpens i₀ s N' V' ≤ pullOpens i₀ s N' V :=
  fun _ hy ↦ img_mono h hy

namespace IsPuiseuxPullback

variable {W : FiniteEtaleOver (space N₀)} {W' : FiniteEtaleOver (space N₀')}
  {β : W'.left → W.left} (P : IsPuiseuxPullback i₀ s W W' β)
include P

/-! ### Lifts -/

/-- **Lifts are continuous**: if `λ` lifts continuous data `(φ, g)` to `W'`, i.e.
`p'(λ x) = g x` and `β(λ x) = φ x` near `x₀`, then `λ` is continuous at `x₀`. -/
theorem continuousAt_of_lift [T2Space W'.left] {X : Type*} [TopologicalSpace X]
    {φ : X → W.left} {g : X → Cn.{u} n} {l : X → W'.left} {x₀ : X} (hφ : ContinuousAt φ x₀)
    (hg : ContinuousAt g x₀) (hl : ∀ᶠ x in 𝓝 x₀, pt W' (l x) = g x ∧ β (l x) = φ x) :
    ContinuousAt l x₀ := by
  have hx₀ := hl.self_of_nhds
  have hgN : g x₀ ∈ N₀' := hx₀.1 ▸ pt_mem W' (l x₀)
  obtain ⟨B, I, _, σ, hBo, hB, -, hσ, hσc, huniq, -⟩ := exists_local_sheets W' hgN
  obtain ⟨i, hi, -⟩ := huniq (l x₀) (hx₀.1.symm ▸ hB)
  rw [hx₀.1] at hi
  obtain ⟨O, hwO, hinj, -⟩ := exists_sheet W (φ x₀)
  have hσg : ContinuousAt (fun x ↦ σ i (g x)) x₀ :=
    ((hσc i).continuousAt (hBo.mem_nhds hB)).comp hg
  have hβσg : ContinuousAt (fun x ↦ β (σ i (g x))) x₀ := P.continuous.continuousAt.comp hσg
  have hval : β (σ i (g x₀)) = φ x₀ := by rw [hi, hx₀.2]
  have hev : ∀ᶠ x in 𝓝 x₀, σ i (g x) = l x := by
    filter_upwards [hl, hg.preimage_mem_nhds (hBo.mem_nhds hB),
      hφ.preimage_mem_nhds (O.isOpen.mem_nhds hwO),
      hβσg.preimage_mem_nhds (O.isOpen.mem_nhds (hval ▸ hwO))] with x hx hxB hxO hxO'
    have h₁ : β (σ i (g x)) = φ x := hinj hxO' hxO (by
      rw [P.pt_eq, hσ i _ hxB, ← hx.1, ← P.pt_eq, hx.2])
    exact P.ext _ _ (by rw [hx.1, hσ i _ hxB]) (by rw [hx.2, h₁])
  exact hσg.congr hev

lemma coordPow_coordRot_zeta (k : Fin s) (x : Cn.{u} n) :
    coordPow i₀ s (coordRot i₀ (zeta s ^ (k : ℕ)) x) = coordPow i₀ s x :=
  coordPow_coordRot (zeta_pow_pow P.pos k) x

lemma pt_apply_eq_coordPow_coordRot (k : Fin s) (w : W'.left) :
    pt W (β w) = coordPow i₀ s (coordRot i₀ (zeta s ^ (k : ℕ)) (pt W' w)) := by
  rw [P.pt_eq, P.coordPow_coordRot_zeta]

/-- **The action of the `s`-th roots of unity on `W'`**: `ζᵏ` acts over `t ↦ ζᵏ t`. -/
def rotW (k : Fin s) (w : W'.left) : W'.left :=
  (P.exists_lift _ _ (P.pt_apply_eq_coordPow_coordRot k w)).choose

lemma pt_rotW (k : Fin s) (w : W'.left) :
    pt W' (P.rotW k w) = coordRot i₀ (zeta s ^ (k : ℕ)) (pt W' w) :=
  (P.exists_lift _ _ (P.pt_apply_eq_coordPow_coordRot k w)).choose_spec.1

lemma apply_rotW (k : Fin s) (w : W'.left) : β (P.rotW k w) = β w :=
  (P.exists_lift _ _ (P.pt_apply_eq_coordPow_coordRot k w)).choose_spec.2

lemma continuous_rotW [T2Space W'.left] (k : Fin s) : Continuous (P.rotW k) :=
  continuous_iff_continuousAt.2 fun _ ↦ P.continuousAt_of_lift P.continuous.continuousAt
    ((continuous_coordRot _).comp (continuous_pt W')).continuousAt
    (Eventually.of_forall fun w ↦ ⟨P.pt_rotW k w, P.apply_rotW k w⟩)

lemma rotW_rotW (k l : Fin s) (w : W'.left) : P.rotW k (P.rotW l w) = P.rotW (k + l) w :=
  P.ext _ _ (by rw [P.pt_rotW, P.pt_rotW, P.pt_rotW, coordRot_coordRot, zeta_pow_add P.pos])
    (by rw [P.apply_rotW, P.apply_rotW, P.apply_rotW])

lemma rotW_zero (w : W'.left) : P.rotW ⟨0, P.pos⟩ w = w :=
  P.ext _ _ (by rw [P.pt_rotW]; simp) (P.apply_rotW _ w)

/-- Two points of `W'` with the same image in `W` differ by a rotation. -/
lemma exists_rotW_eq {w₁ w₂ : W'.left} (h : β w₁ = β w₂) : ∃ k, P.rotW k w₁ = w₂ := by
  have h' : coordPow i₀ s (pt W' w₁) = coordPow i₀ s (pt W' w₂) := by
    rw [← P.pt_eq, ← P.pt_eq, h]
  obtain ⟨k, hk⟩ := exists_coordRot_eq P.pos h'
  exact ⟨k, P.ext _ _ (by rw [P.pt_rotW, hk]) (by rw [P.apply_rotW, h])⟩

lemma nonempty_of_mem (w : W.left) : Nonempty W'.left :=
  ⟨(P.exists_lift w (coordRoot i₀ s (pt W w))
    (coordPow_coordRoot P.pos.ne' _).symm).choose⟩

/-! ### Opens -/

variable (hN : ∀ x, x ∈ N' ↔ coordPow i₀ s x ∈ N) {h₀ : N₀ ≤ N} {h₀' : N₀' ≤ N'}
include hN

omit P in
lemma mem_preim_pullOpens {V : (space N).Opens} {w : W'.left} :
    w ∈ preim h₀' W' (pullOpens i₀ s N' V) ↔ coordPow i₀ s (pt W' w) ∈ img V := by
  rw [mem_preim_iff, mem_img_pullOpens hN]

lemma apply_mem_preim {V : (space N).Opens} {w : W'.left}
    (hw : w ∈ preim h₀' W' (pullOpens i₀ s N' V)) : β w ∈ preim h₀ W V := by
  rw [mem_preim_iff, P.pt_eq]
  exact (mem_preim_pullOpens hN).1 hw

lemma rotW_mem_preim {V : (space N).Opens} (k : Fin s) {w : W'.left}
    (hw : w ∈ preim h₀' W' (pullOpens i₀ s N' V)) :
    P.rotW k w ∈ preim h₀' W' (pullOpens i₀ s N' V) := by
  rw [mem_preim_pullOpens hN, P.pt_rotW, P.coordPow_coordRot_zeta]
  exact (mem_preim_pullOpens hN).1 hw

lemma exists_lift_mem {V : (space N).Opens} {w : W.left} (hw : w ∈ preim h₀ W V) :
    ∃ w', w' ∈ preim h₀' W' (pullOpens i₀ s N' V) ∧ β w' = w := by
  obtain ⟨w', hw', hβ⟩ := P.exists_lift w (coordRoot i₀ s (pt W w))
    (coordPow_coordRoot P.pos.ne' _).symm
  refine ⟨w', ?_, hβ⟩
  rw [mem_preim_pullOpens hN, hw', coordPow_coordRoot P.pos.ne']
  exact (mem_preim_iff h₀ W).1 hw

/-! ### Functions -/

omit P in
/-- Bounded functions pull back to bounded functions. -/
lemma isBddOn_comp {V : (space N).Opens} {f : W.left → ℂ} (hf : IsBddOn W V f)
    (hmem : ∀ x, x ∈ N₀' ↔ coordPow i₀ s x ∈ N₀) (hpt : ∀ w, pt W (β w) = coordPow i₀ s (pt W' w)) :
    IsBddOn W' (pullOpens i₀ s N' V) (fun w ↦ f (β w)) := by
  intro x hx hxN
  rw [mem_img_pullOpens hN] at hx
  obtain ⟨M, hM, C, hC⟩ := hf _ hx (fun h ↦ hxN ((hmem x).2 h))
  refine ⟨coordPow i₀ s ⁻¹' M, (continuous_coordPow s).continuousAt.preimage_mem_nhds hM, C,
    fun w hw hwV ↦ ?_⟩
  rw [mem_img_pullOpens hN] at hwV
  exact hC (β w) (by rw [hpt]; exact hw) (by rw [hpt]; exact hwV)

lemma isBddOn_comp_rotW {V : (space N).Opens} {f : W'.left → ℂ}
    (hf : IsBddOn W' (pullOpens i₀ s N' V) f) (k : Fin s) :
    IsBddOn W' (pullOpens i₀ s N' V) (fun w ↦ f (P.rotW k w)) := by
  intro x hx hxN
  have hx' : coordRot i₀ (zeta s ^ (k : ℕ)) x ∈ img (pullOpens i₀ s N' V) := by
    rw [mem_img_pullOpens hN, P.coordPow_coordRot_zeta]
    exact (mem_img_pullOpens hN).1 hx
  have hxN' : coordRot i₀ (zeta s ^ (k : ℕ)) x ∉ N₀' := by
    exact fun h ↦ hxN ((P.mem_iff x).2 (P.coordPow_coordRot_zeta k x ▸ (P.mem_iff _).1 h))
  obtain ⟨M, hM, C, hC⟩ := hf _ hx' hxN'
  refine ⟨coordRot i₀ (zeta s ^ (k : ℕ)) ⁻¹' M,
    (continuous_coordRot _).continuousAt.preimage_mem_nhds hM, C, fun w hw hwV ↦ ?_⟩
  refine hC _ (by rw [P.pt_rotW]; exact hw) ?_
  rw [P.pt_rotW, mem_img_pullOpens hN, P.coordPow_coordRot_zeta]
  exact (mem_img_pullOpens hN).1 hwV

lemma isHolOn_comp_rotW [T2Space W'.left] {V : (space N).Opens} {f : W'.left → ℂ}
    (hf : IsHolOn W' f (preim h₀' W' (pullOpens i₀ s N' V))) (k : Fin s) :
    IsHolOn W' (fun w ↦ f (P.rotW k w)) (preim h₀' W' (pullOpens i₀ s N' V)) :=
  hf.comp (differentiable_coordRot _) (P.pt_rotW k) (fun _ _ ↦ (P.continuous_rotW k).continuousAt)
    fun _ hw ↦ P.rotW_mem_preim hN k hw

/-! ### Pulling back sections -/

variable (h₀') in
lemma exists_pullSec {V : (space N).Opens} (a : (boundedModule h₀ W).val.obj (op V)) :
    ∃ b : (boundedModule h₀' W').val.obj (op (pullOpens i₀ s N' V)),
      ∀ w ∈ preim h₀' W' (pullOpens i₀ s N' V),
        evalFun (secVal h₀' W' b) w = evalFun (secVal h₀ W a) (β w) :=
  exists_secVal_eq h₀' W'
    ((isHolOn_secVal h₀ W a).comp (differentiable_coordPow s) P.pt_eq
      (fun _ _ ↦ P.continuous.continuousAt) fun _ hw ↦ P.apply_mem_preim hN hw)
    (isBddOn_comp hN (isBddOn_secVal h₀ W a) P.mem_iff P.pt_eq)

variable (h₀') in
/-- **The pullback `𝒜(V) → 𝒜'(α⁻¹(V))`** along `β`. -/
def pullSec {V : (space N).Opens} (a : (boundedModule h₀ W).val.obj (op V)) :
    (boundedModule h₀' W').val.obj (op (pullOpens i₀ s N' V)) :=
  (P.exists_pullSec hN h₀' a).choose

lemma evalFun_pullSec {V : (space N).Opens} (a : (boundedModule h₀ W).val.obj (op V))
    {w : W'.left} (hw : w ∈ preim h₀' W' (pullOpens i₀ s N' V)) :
    evalFun (secVal h₀' W' (P.pullSec hN h₀' a)) w = evalFun (secVal h₀ W a) (β w) :=
  (P.exists_pullSec hN h₀' a).choose_spec w hw

/-- A section of `𝒜'(α⁻¹(V))` is **invariant** if its values are invariant under the rotations. -/
def IsInvariant {V : (space N).Opens}
    (b : (boundedModule h₀' W').val.obj (op (pullOpens i₀ s N' V))) : Prop :=
  ∀ k, ∀ w ∈ preim h₀' W' (pullOpens i₀ s N' V),
    evalFun (secVal h₀' W' b) (P.rotW k w) = evalFun (secVal h₀' W' b) w

lemma isInvariant_pullSec {V : (space N).Opens} (a : (boundedModule h₀ W).val.obj (op V)) :
    P.IsInvariant (P.pullSec hN h₀' a) := fun k w hw ↦ by
  rw [P.evalFun_pullSec hN a (P.rotW_mem_preim hN k hw), P.evalFun_pullSec hN a hw,
    P.apply_rotW]

/-! ### Descent of invariant sections -/


omit hN in
lemma evalFun_eq_of_apply_eq {V : (space N).Opens}
    {b : (boundedModule h₀' W').val.obj (op (pullOpens i₀ s N' V))} (hb : P.IsInvariant b)
    {w₁ w₂ : W'.left} (hw₁ : w₁ ∈ preim h₀' W' (pullOpens i₀ s N' V)) (h : β w₁ = β w₂) :
    evalFun (secVal h₀' W' b) w₁ = evalFun (secVal h₀' W' b) w₂ := by
  obtain ⟨k, rfl⟩ := P.exists_rotW_eq h
  exact (hb k w₁ hw₁).symm

variable (β) in
open Classical in
/-- The function on `W` induced by an invariant section. -/
def descFun {V : (space N).Opens} (b : (boundedModule h₀' W').val.obj (op (pullOpens i₀ s N' V)))
    (w : W.left) : ℂ :=
  if h : ∃ w', w' ∈ preim h₀' W' (pullOpens i₀ s N' V) ∧ β w' = w then
    evalFun (secVal h₀' W' b) h.choose else 0

omit hN in
lemma descFun_apply {V : (space N).Opens}
    {b : (boundedModule h₀' W').val.obj (op (pullOpens i₀ s N' V))} (hb : P.IsInvariant b)
    {w : W'.left} (hw : w ∈ preim h₀' W' (pullOpens i₀ s N' V)) :
    descFun β b (β w) = evalFun (secVal h₀' W' b) w := by
  have h : ∃ w', w' ∈ preim h₀' W' (pullOpens i₀ s N' V) ∧ β w' = β w := ⟨w, hw, rfl⟩
  rw [descFun, dif_pos h]
  exact P.evalFun_eq_of_apply_eq hb h.choose_spec.1 h.choose_spec.2

lemma isHolOn_descFun [T2Space W.left] [T2Space W'.left] {V : (space N).Opens}
    {b : (boundedModule h₀' W').val.obj (op (pullOpens i₀ s N' V))} (hb : P.IsInvariant b) :
    IsHolOn W (descFun β b) (preim h₀ W V) := by
  classical
  intro w hw
  haveI := P.nonempty_of_mem w
  obtain ⟨B, I, _, σ, hBo, hB, -, hσ, hσc, huniq, hopen⟩ := exists_local_sheets W (pt_mem W w)
  obtain ⟨i, hi, -⟩ := huniq w hB
  set G : Set (Cn.{u} n) := B ∩ img V
  have hGo : IsOpen G := hBo.inter (img V).isOpen
  have hαG : IsOpen (coordPow i₀ s ⁻¹' G) := hGo.preimage (continuous_coordPow s)
  have hlift : ∀ x ∈ coordPow i₀ s ⁻¹' G, ∃ w', pt W' w' = x ∧ β w' = σ i (coordPow i₀ s x) :=
    fun x hx ↦ P.exists_lift _ _ (hσ i _ hx.1)
  let τ : Cn.{u} n → W'.left := fun x ↦
    if hx : x ∈ coordPow i₀ s ⁻¹' G then (hlift x hx).choose else Classical.arbitrary _
  have hτ : ∀ x ∈ coordPow i₀ s ⁻¹' G, pt W' (τ x) = x ∧ β (τ x) = σ i (coordPow i₀ s x) :=
    fun x hx ↦ by simp only [τ, dif_pos hx]; exact (hlift x hx).choose_spec
  have hτc : ContinuousOn τ (coordPow i₀ s ⁻¹' G) := fun x hx ↦
    (P.continuousAt_of_lift (((hσc i).continuousAt (hBo.mem_nhds hx.1)).comp
      (continuous_coordPow s).continuousAt) continuousAt_id
      (eventually_of_mem (hαG.mem_nhds hx) fun y hy ↦ hτ y hy)).continuousWithinAt
  have hτV : ∀ x ∈ coordPow i₀ s ⁻¹' G, τ x ∈ preim h₀' W' (pullOpens i₀ s N' V) := fun x hx ↦ by
    rw [mem_preim_pullOpens hN, (hτ x hx).1]
    exact hx.2
  set h : Cn.{u} n → ℂ := fun x ↦ descFun β b (σ i x)
  have hh : DifferentiableOn ℂ h G := by
    refine differentiableOn_of_comp_coordPow (i₀ := i₀) P.pos hGo fun x hx ↦ ?_
    have heq : (fun y ↦ evalFun (secVal h₀' W' b) (τ y)) =ᶠ[𝓝 x] h ∘ coordPow i₀ s := by
      filter_upwards [hαG.mem_nhds hx] with y hy
      simp only [Function.comp_apply, h, ← (hτ y hy).2]
      exact (P.descFun_apply hb (hτV y hy)).symm
    exact ((differentiableAt_evalFun_comp W' hαG (fun y hy ↦ (hτ y hy).1) hτc _ hx
      (hτV x hx)).congr_of_eventuallyEq heq.symm).differentiableWithinAt
  refine ⟨h, ?_⟩
  filter_upwards [(hopen i).mem_nhds ⟨hB, hi⟩, (preim h₀ W V).isOpen.mem_nhds hw] with w' hw' hw'V
  refine ⟨hh.differentiableAt (hGo.mem_nhds ⟨hw'.1, (mem_preim_iff h₀ W).1 hw'V⟩), ?_⟩
  simp only [h, hw'.2]

lemma isBddOn_descFun {V : (space N).Opens}
    {b : (boundedModule h₀' W').val.obj (op (pullOpens i₀ s N' V))} (hb : P.IsInvariant b) :
    IsBddOn W V (descFun β b) := by
  intro x hx hxN
  set x' := coordRoot i₀ s x
  have hx'x : coordPow i₀ s x' = x := coordPow_coordRoot P.pos.ne' x
  have hk : ∀ k : Fin s, coordRot i₀ (zeta s ^ (k : ℕ)) x' ∈ img (pullOpens i₀ s N' V) ∧
      coordRot i₀ (zeta s ^ (k : ℕ)) x' ∉ N₀' := fun k ↦ by
    refine ⟨by rw [mem_img_pullOpens hN, P.coordPow_coordRot_zeta, hx'x]; exact hx, fun h ↦ hxN ?_⟩
    have := (P.mem_iff _).1 h
    rwa [P.coordPow_coordRot_zeta, hx'x] at this
  choose M hM C hC using fun k ↦ isBddOn_secVal h₀' W' b _ (hk k).1 (hk k).2
  choose r hr hrM using fun k ↦ Metric.mem_nhds_iff.1 (hM k)
  haveI : Nonempty (Fin s) := ⟨⟨0, P.pos⟩⟩
  set ρ := Finset.univ.inf' Finset.univ_nonempty r
  have hρ : 0 < ρ := (Finset.lt_inf'_iff _).2 fun k _ ↦ hr k
  refine ⟨Metric.ball x (min ρ (ρ ^ s)), Metric.ball_mem_nhds _ (lt_min hρ (pow_pos hρ s)),
    ∑ k, |C k|, fun w hw hwV ↦ ?_⟩
  obtain ⟨w', hpt', rfl⟩ := P.exists_lift w (coordRoot i₀ s (pt W w))
    (coordPow_coordRoot P.pos.ne' _).symm
  have hw' : w' ∈ preim h₀' W' (pullOpens i₀ s N' V) := by
    rw [mem_preim_pullOpens hN, hpt', coordPow_coordRoot P.pos.ne']
    exact hwV
  rw [P.descFun_apply hb hw']
  have hdist : ‖coordPow i₀ s (pt W' w') - coordPow i₀ s x'‖ < min ρ (ρ ^ s) := by
    rw [← P.pt_eq, hx'x, ← dist_eq_norm]
    exact hw
  obtain ⟨k, hk'⟩ := exists_coordRot_norm_sub_lt P.pos hρ hdist
  have hmem : pt W' w' ∈ M k := hrM k (by
    rw [Metric.mem_ball, dist_eq_norm]
    exact hk'.trans_le (Finset.inf'_le _ (Finset.mem_univ k)))
  exact (hC k w' hmem ((mem_preim_iff h₀' W').1 hw')).trans
    ((le_abs_self _).trans (Finset.single_le_sum (fun j _ ↦ abs_nonneg (C j)) (Finset.mem_univ k)))

omit P in
/-- The pullback `r ∘ α` of a holomorphic function on `V`, as a function on `α⁻¹(V)`. -/
def pullFun {V : (space N).Opens} (r : (space N).presheaf.obj (op V)) :
    (space N').presheaf.obj (op (pullOpens i₀ s N' V)) :=
  OkaRing.ofDifferentiableOn (fun x ↦ holFun r (coordPow i₀ s x)) fun x hx ↦
    ((differentiableOn_holFun r).differentiableAt ((img V).isOpen.mem_nhds
      ((mem_img_pullOpens hN).1 hx))).comp x
      (differentiable_coordPow s x) |>.differentiableWithinAt

omit P in
lemma holFun_pullFun {V : (space N).Opens} (r : (space N).presheaf.obj (op V)) {x : Cn.{u} n}
    (hx : x ∈ img (pullOpens i₀ s N' V)) :
    holFun (pullFun hN r) x = holFun r (coordPow i₀ s x) :=
  holFun_ofDifferentiableOn _ hx

lemma pullSec_smul {V : (space N).Opens} (r : (space N).presheaf.obj (op V))
    (a : (boundedModule h₀ W).val.obj (op V)) :
    P.pullSec hN h₀' (r • a) = pullFun hN r • P.pullSec hN h₀' a :=
  secVal_ext h₀' W' fun w hw ↦ by
    rw [evalFun_secVal_smul _ _ hw, P.evalFun_pullSec hN _ hw,
      P.evalFun_pullSec hN _ hw, evalFun_secVal_smul _ _ (P.apply_mem_preim hN hw),
      holFun_pullFun hN r ((mem_preim_iff h₀' W').1 hw), P.pt_eq]

lemma pullSec_add {V : (space N).Opens} (a a' : (boundedModule h₀ W).val.obj (op V)) :
    P.pullSec hN h₀' (a + a') = P.pullSec hN h₀' a + P.pullSec hN h₀' a' :=
  secVal_ext h₀' W' fun w hw ↦ by
    rw [evalFun_secVal_add _ _ hw, P.evalFun_pullSec hN _ hw,
      P.evalFun_pullSec hN _ hw, P.evalFun_pullSec hN _ hw,
      evalFun_secVal_add _ _ (P.apply_mem_preim hN hw)]

lemma pullSec_sum {V : (space N).Opens} {ι : Type*} (t : Finset ι)
    (a : ι → (boundedModule h₀ W).val.obj (op V)) :
    P.pullSec hN h₀' (∑ i ∈ t, a i) = ∑ i ∈ t, P.pullSec hN h₀' (a i) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    refine secVal_ext h₀' W' fun w hw ↦ ?_
    simp only [Finset.sum_empty]
    rw [P.evalFun_pullSec hN _ hw, evalFun_secVal_zero hw,
      evalFun_secVal_zero (P.apply_mem_preim hN hw)]
  | insert j t hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, P.pullSec_add, ih]

variable [T2Space W'.left]

/-! ### The Reynolds operator -/

lemma exists_reynolds {V : (space N).Opens}
    (b : (boundedModule h₀' W').val.obj (op (pullOpens i₀ s N' V))) :
    ∃ c : (boundedModule h₀' W').val.obj (op (pullOpens i₀ s N' V)),
      ∀ w ∈ preim h₀' W' (pullOpens i₀ s N' V), evalFun (secVal h₀' W' c) w =
        (s : ℂ)⁻¹ * ∑ k, evalFun (secVal h₀' W' b) (P.rotW k w) :=
  exists_secVal_eq h₀' W'
    ((isHolOn_const (s : ℂ)⁻¹ _).mul (IsHolOn.sum Finset.univ fun k _ ↦
      P.isHolOn_comp_rotW hN (isHolOn_secVal h₀' W' b) k))
    ((isBddOn_const _ (s : ℂ)⁻¹).mul (IsBddOn.sum Finset.univ fun k _ ↦
      P.isBddOn_comp_rotW hN (isBddOn_secVal h₀' W' b) k))

/-- **The Reynolds operator** `R(b) = s⁻¹ ∑_ζ ζ · b` on `𝒜'(α⁻¹(V))`. -/
def reynolds {V : (space N).Opens}
    (b : (boundedModule h₀' W').val.obj (op (pullOpens i₀ s N' V))) :
    (boundedModule h₀' W').val.obj (op (pullOpens i₀ s N' V)) :=
  (P.exists_reynolds hN b).choose

lemma evalFun_reynolds {V : (space N).Opens}
    (b : (boundedModule h₀' W').val.obj (op (pullOpens i₀ s N' V))) {w : W'.left}
    (hw : w ∈ preim h₀' W' (pullOpens i₀ s N' V)) :
    evalFun (secVal h₀' W' (P.reynolds hN b)) w =
      (s : ℂ)⁻¹ * ∑ k, evalFun (secVal h₀' W' b) (P.rotW k w) :=
  (P.exists_reynolds hN b).choose_spec w hw

/-- The Reynolds operator takes values in the invariant sections. -/
theorem isInvariant_reynolds {V : (space N).Opens}
    (b : (boundedModule h₀' W').val.obj (op (pullOpens i₀ s N' V))) :
    P.IsInvariant (P.reynolds hN b) := fun j w hw ↦ by
  haveI : NeZero s := ⟨P.pos.ne'⟩
  rw [P.evalFun_reynolds hN b (P.rotW_mem_preim hN j hw), P.evalFun_reynolds hN b hw]
  simp_rw [P.rotW_rotW]
  congr 1
  exact Fintype.sum_equiv (Equiv.addRight j) _ _ fun _ ↦ rfl

/-- The Reynolds operator is the identity on invariant sections. -/
theorem reynolds_of_isInvariant {V : (space N).Opens}
    {b : (boundedModule h₀' W').val.obj (op (pullOpens i₀ s N' V))} (hb : P.IsInvariant b) :
    P.reynolds hN b = b :=
  secVal_ext h₀' W' fun w hw ↦ by
    rw [P.evalFun_reynolds hN b hw]
    simp_rw [hb _ w hw]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc,
      inv_mul_cancel₀ (Nat.cast_ne_zero.2 P.pos.ne'), one_mul]

lemma reynolds_add {V : (space N).Opens}
    (b c : (boundedModule h₀' W').val.obj (op (pullOpens i₀ s N' V))) :
    P.reynolds hN (b + c) = P.reynolds hN b + P.reynolds hN c :=
  secVal_ext h₀' W' fun w hw ↦ by
    rw [evalFun_secVal_add _ _ hw, P.evalFun_reynolds hN _ hw, P.evalFun_reynolds hN _ hw,
      P.evalFun_reynolds hN _ hw, ← mul_add, ← Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_congr rfl fun k _ ↦ evalFun_secVal_add _ _ (P.rotW_mem_preim hN k hw)

lemma reynolds_sum {V : (space N).Opens} {ι : Type*} (t : Finset ι)
    (b : ι → (boundedModule h₀' W').val.obj (op (pullOpens i₀ s N' V))) :
    P.reynolds hN (∑ i ∈ t, b i) = ∑ i ∈ t, P.reynolds hN (b i) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    refine secVal_ext h₀' W' fun w hw ↦ ?_
    simp only [Finset.sum_empty]
    rw [P.evalFun_reynolds hN _ hw, evalFun_secVal_zero hw]
    simp_rw [evalFun_secVal_zero (P.rotW_mem_preim hN _ hw)]
    simp
  | insert j t hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, P.reynolds_add, ih]

/-- **The Reynolds operator is linear over the functions pulled back from `V`.** -/
theorem reynolds_pullFun_smul {V : (space N).Opens} (r : (space N).presheaf.obj (op V))
    (b : (boundedModule h₀' W').val.obj (op (pullOpens i₀ s N' V))) :
    P.reynolds hN (pullFun hN r • b) = pullFun hN r • P.reynolds hN b :=
  secVal_ext h₀' W' fun w hw ↦ by
    rw [evalFun_secVal_smul _ _ hw, P.evalFun_reynolds hN _ hw, P.evalFun_reynolds hN _ hw,
      Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    have hk := P.rotW_mem_preim hN k hw
    rw [evalFun_secVal_smul _ _ hk, holFun_pullFun hN r ((mem_preim_iff h₀' W').1 hk),
      holFun_pullFun hN r ((mem_preim_iff h₀' W').1 hw), P.pt_rotW, P.coordPow_coordRot_zeta]
    ring

variable [T2Space W.left]


/-- **Descent of an invariant section** of `𝒜'(α⁻¹(V))` to a section of `𝒜(V)`. -/
def descend {V : (space N).Opens} (b : (boundedModule h₀' W').val.obj (op (pullOpens i₀ s N' V)))
    (hb : P.IsInvariant b) : (boundedModule h₀ W).val.obj (op V) :=
  (exists_secVal_eq h₀ W (P.isHolOn_descFun hN hb) (P.isBddOn_descFun hN hb)).choose

lemma evalFun_descend {V : (space N).Opens}
    {b : (boundedModule h₀' W').val.obj (op (pullOpens i₀ s N' V))} (hb : P.IsInvariant b)
    {w : W'.left} (hw : w ∈ preim h₀' W' (pullOpens i₀ s N' V)) :
    evalFun (secVal h₀ W (P.descend hN b hb)) (β w) = evalFun (secVal h₀' W' b) w :=
  ((exists_secVal_eq h₀ W (P.isHolOn_descFun hN hb) (P.isBddOn_descFun hN hb)).choose_spec _
    (P.apply_mem_preim hN hw)).trans (P.descFun_apply hb hw)

/-- Pulling back a descended section gives it back. -/
theorem pullSec_descend {V : (space N).Opens}
    {b : (boundedModule h₀' W').val.obj (op (pullOpens i₀ s N' V))} (hb : P.IsInvariant b) :
    P.pullSec hN h₀' (P.descend hN (h₀ := h₀) b hb) = b :=
  secVal_ext h₀' W' fun w hw ↦ by
    rw [P.evalFun_pullSec hN _ hw, P.evalFun_descend hN hb hw]

/-- Descending a pulled back section gives it back. -/
theorem descend_pullSec {V : (space N).Opens} (a : (boundedModule h₀ W).val.obj (op V)) :
    P.descend hN (P.pullSec hN h₀' a) (P.isInvariant_pullSec hN a) = a :=
  secVal_ext h₀ W fun w hw ↦ by
    obtain ⟨w', hw', rfl⟩ := P.exists_lift_mem hN hw
    rw [P.evalFun_descend hN _ hw', P.evalFun_pullSec hN _ hw']

/-- **`𝒜(V)` is the invariant part of `𝒜'(α⁻¹(V))`.** -/
theorem isInvariant_iff {V : (space N).Opens}
    (b : (boundedModule h₀' W').val.obj (op (pullOpens i₀ s N' V))) :
    P.IsInvariant b ↔ ∃ a : (boundedModule h₀ W).val.obj (op V),
      P.pullSec hN h₀' a = b :=
  ⟨fun hb ↦ ⟨P.descend hN b hb, P.pullSec_descend hN hb⟩, fun ⟨a, ha⟩ ↦
    ha ▸ P.isInvariant_pullSec hN a⟩

omit [T2Space W'.left] [T2Space W.left] in
lemma pullSec_injective {V : (space N).Opens} :
    Function.Injective (P.pullSec hN h₀' (h₀ := h₀) (V := V)) := by
  intro a a' h
  refine secVal_ext h₀ W fun w hw ↦ ?_
  obtain ⟨w', hw', rfl⟩ := P.exists_lift_mem (h₀' := h₀') hN hw
  rw [← P.evalFun_pullSec hN a hw', ← P.evalFun_pullSec hN a' hw', h]

end IsPuiseuxPullback

end

end ComplexAnalytic.BoundedSections
