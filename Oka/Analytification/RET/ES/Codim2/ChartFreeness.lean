/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.ES.Codim2.MapPullback

/-!
# Freeness of bounded sections along a biholomorphic chart

Keep the notation of `Oka/Analytification/RET/ES/Codim2/MapPullback.lean`: `χ : A° → N°` is a
holomorphic open embedding and `W'` is the pullback of `W` along `χ`, with `β : W' → W`. Suppose
that `χ` extends to a biholomorphism `D → E` between opens `D ⊆ A` and `E ⊆ N`
(`ComplexAnalytic.BoundedSections.ChartBiholo`); e.g. a chart of a blow-up off the exceptional
divisor. Then a section of `𝒜'` over `V ⊆ D` gives the section of `𝒜` over `χ(V)` with values
`b ∘ β⁻¹` (`…ChartBiholo.pushSec`), a section `a` of `𝒜` over `V ⊆ E` gives the section of `𝒜'`
over `χ⁻¹(V)` with values `a ∘ β` (`…ChartBiholo.pullSec`), and a local basis of `𝒜'` near `x ∈ D`
goes to a local basis of `𝒜` near `χ(x)` (`…ChartBiholo.isFreeSpanAt`).

## Main definitions

- `ComplexAnalytic.BoundedSections.ChartBiholo Φ A N`: the extension of `χ` to a biholomorphism
  `D → E`.

## Main results

- `ComplexAnalytic.BoundedSections.ChartBiholo.isFreeSpanAt`: if `𝒜'` is free near `x ∈ D`, then
  `𝒜` is free near `χ(x)`.
-/

open CategoryTheory Opposite AlgebraicGeometry Topology TopologicalSpace Filter

universe u

namespace ComplexAnalytic.BoundedSections

open AnalyticSpace AlgebraicGeometry.LocallyRingedSpace

noncomputable section

variable {n : ℕ} {N N₀ A A₀ : (AnalyticSpace.complexAffineSpace.{u} n).Opens}

/-- **An extension of `χ` to a biholomorphism** `D → E` between opens `D ⊆ A` and `E ⊆ N`. -/
structure ChartBiholo (Φ : ChartMap A₀ N₀) (A N : (AnalyticSpace.complexAffineSpace.{u} n).Opens)
    where
  /-- The domain. -/
  D : Set (Cn.{u} n)
  /-- The image. -/
  E : Set (Cn.{u} n)
  isOpen_D : IsOpen D
  isOpen_E : IsOpen E
  D_sub : ∀ x ∈ D, x ∈ A
  E_sub : ∀ y ∈ E, y ∈ N
  E_sub_R : E ⊆ Φ.R
  mapsTo : ∀ x ∈ D, Φ.χ x ∈ E
  inv_mem : ∀ y ∈ E, Φ.χInv y ∈ D
  inv_χ : ∀ x ∈ D, Φ.χInv (Φ.χ x) = x
  χ_inv : ∀ y ∈ E, Φ.χ (Φ.χInv y) = y
  differentiableOn_χ : DifferentiableOn ℂ Φ.χ D
  differentiableOn_χInv : DifferentiableOn ℂ Φ.χInv E

namespace ChartBiholo

variable {Φ : ChartMap A₀ N₀} (Z : ChartBiholo Φ A N)

/-- The open `χ⁻¹(V)` of `A` for an open `V` of `N`. -/
def pullOpen (V : (space N).Opens) : (space A).Opens :=
  ⟨{z | z.1 ∈ Z.D ∧ Φ.χ z.1 ∈ img V}, by
    have := Z.differentiableOn_χ.continuousOn.isOpen_inter_preimage Z.isOpen_D (img V).isOpen
    exact this.preimage continuous_subtype_val⟩

/-- The open `χ(V)` of `N` for an open `V` of `A`. -/
def pushOpen (V : (space A).Opens) : (space N).Opens :=
  ⟨{y | y.1 ∈ Z.E ∧ Φ.χInv y.1 ∈ img V}, by
    have := Z.differentiableOn_χInv.continuousOn.isOpen_inter_preimage Z.isOpen_E (img V).isOpen
    exact this.preimage continuous_subtype_val⟩

lemma mem_img_pullOpen {V : (space N).Opens} {x : Cn.{u} n} :
    x ∈ img (Z.pullOpen V) ↔ x ∈ Z.D ∧ Φ.χ x ∈ img V := by
  rw [mem_img_iff]
  exact ⟨fun ⟨_, h⟩ ↦ h, fun h ↦ ⟨Z.D_sub x h.1, h⟩⟩

lemma mem_img_pushOpen {V : (space A).Opens} {y : Cn.{u} n} :
    y ∈ img (Z.pushOpen V) ↔ y ∈ Z.E ∧ Φ.χInv y ∈ img V := by
  rw [mem_img_iff]
  exact ⟨fun ⟨_, h⟩ ↦ h, fun h ↦ ⟨Z.E_sub y h.1, h⟩⟩

variable {h₀ : N₀ ≤ N} {hA : A₀ ≤ A} {W : FiniteEtaleOver (space N₀)}
  {W' : FiniteEtaleOver (space A₀)} {β : W'.left → W.left} (hβ : IsMapPullback Φ W W' β)
include hβ

/-- Every point of `W` over `E` is in the image of `β`. -/
lemma exists_β {w : W.left} (hw : pt W w ∈ Z.E) : ∃ w', β w' = w :=
  hβ.mem_range_iff.2 ⟨Z.E_sub_R hw, (Φ.mem_iff _).2 (by
    rw [Z.χ_inv _ hw]
    exact pt_mem W w)⟩

lemma mem_preim_of_pushOpen {V : (space A).Opens} {w' : W'.left}
    (hw : β w' ∈ preim h₀ W (Z.pushOpen V)) : w' ∈ preim hA W' V := by
  rw [mem_preim_iff] at hw ⊢
  rw [hβ.pt_eq_χInv]
  exact (Z.mem_img_pushOpen.1 hw).2

lemma pt_mem_D (w' : W'.left) (hw : pt W (β w') ∈ Z.E) : pt W' w' ∈ Z.D := by
  rw [hβ.pt_eq_χInv]
  exact Z.inv_mem _ hw

lemma isHolOn_push {V : (space A).Opens} (b : (boundedModule hA W').val.obj (op V)) :
    IsHolOn W (IsMapPullback.liftFun β (evalFun (secVal hA W' b))) (preim h₀ W (Z.pushOpen V)) :=
  (hβ.isHolOn_liftFun (isHolOn_secVal hA W' b)).mono fun w hw ↦ by
    have hE : pt W w ∈ Z.E := (Z.mem_img_pushOpen.1 ((mem_preim_iff h₀ W).1 hw)).1
    obtain ⟨w', rfl⟩ := Z.exists_β hβ hE
    exact ⟨w', Z.mem_preim_of_pushOpen hβ hw, rfl⟩

lemma isBddOn_push {V : (space A).Opens} (b : (boundedModule hA W').val.obj (op V)) :
    IsBddOn W (Z.pushOpen V) (IsMapPullback.liftFun β (evalFun (secVal hA W' b))) := by
  intro y hy hyN
  obtain ⟨hyE, hyV⟩ := Z.mem_img_pushOpen.1 hy
  have hxA₀ : Φ.χInv y ∉ A₀ := fun h ↦ hyN (by
    rw [← Z.χ_inv y hyE]
    exact (Φ.mem_iff _).1 h)
  obtain ⟨M, hM, C, hC⟩ := isBddOn_secVal hA W' b _ hyV hxA₀
  have hc : ContinuousAt Φ.χInv y :=
    Z.differentiableOn_χInv.continuousOn.continuousAt (Z.isOpen_E.mem_nhds hyE)
  refine ⟨Φ.χInv ⁻¹' M, hc.preimage_mem_nhds hM, C, fun w hwM hwV ↦ ?_⟩
  obtain ⟨w', rfl⟩ := Z.exists_β hβ (Z.mem_img_pushOpen.1 hwV).1
  rw [hβ.liftFun_apply]
  refine hC w' ?_ ?_
  · rw [hβ.pt_eq_χInv]
    exact hwM
  · rw [hβ.pt_eq_χInv]
    exact (Z.mem_img_pushOpen.1 hwV).2

/-- The section of `𝒜` over `χ(V)` with values `b ∘ β⁻¹`. -/
def pushSec {V : (space A).Opens} (b : (boundedModule hA W').val.obj (op V)) :
    (boundedModule h₀ W).val.obj (op (Z.pushOpen V)) :=
  (exists_secVal_eq h₀ W (Z.isHolOn_push hβ b) (Z.isBddOn_push hβ b)).choose

lemma evalFun_pushSec {V : (space A).Opens} (b : (boundedModule hA W').val.obj (op V))
    {w' : W'.left} (hw : β w' ∈ preim h₀ W (Z.pushOpen V)) :
    evalFun (secVal h₀ W (Z.pushSec hβ b)) (β w') = evalFun (secVal hA W' b) w' :=
  ((exists_secVal_eq h₀ W (Z.isHolOn_push hβ b) (Z.isBddOn_push hβ b)).choose_spec _ hw).trans
    (hβ.liftFun_apply _ w')

lemma isBddOn_pull {V : (space N).Opens} (a : (boundedModule h₀ W).val.obj (op V)) :
    IsBddOn W' (Z.pullOpen V) (fun w' ↦ evalFun (secVal h₀ W a) (β w')) := by
  intro x hx hxA
  obtain ⟨hxD, hxV⟩ := Z.mem_img_pullOpen.1 hx
  obtain ⟨M, hM, C, hC⟩ := isBddOn_secVal h₀ W a _ hxV fun h ↦ hxA ((Φ.mem_iff x).2 h)
  have hc : ContinuousAt Φ.χ x :=
    Z.differentiableOn_χ.continuousOn.continuousAt (Z.isOpen_D.mem_nhds hxD)
  refine ⟨Φ.χ ⁻¹' M, hc.preimage_mem_nhds hM, C, fun w' hwM hwV ↦ ?_⟩
  refine hC (β w') ?_ ?_
  · rw [hβ.pt_eq]
    exact hwM
  · rw [hβ.pt_eq]
    exact (Z.mem_img_pullOpen.1 hwV).2

/-- The section of `𝒜'` over `χ⁻¹(V)` with values `a ∘ β`. -/
def pullSec {V : (space N).Opens} (a : (boundedModule h₀ W).val.obj (op V)) :
    (boundedModule hA W').val.obj (op (Z.pullOpen V)) :=
  (exists_secVal_eq hA W' (hβ.isHolOn_comp (isHolOn_secVal h₀ W a) fun w' hw' ↦
    (mem_preim_iff h₀ W).2 (by
      rw [hβ.pt_eq]
      exact (Z.mem_img_pullOpen.1 ((mem_preim_iff hA W').1 hw')).2))
    (Z.isBddOn_pull hβ a)).choose

lemma evalFun_pullSec {V : (space N).Opens} (a : (boundedModule h₀ W).val.obj (op V))
    {w' : W'.left} (hw' : w' ∈ preim hA W' (Z.pullOpen V)) :
    evalFun (secVal hA W' (Z.pullSec hβ a)) w' = evalFun (secVal h₀ W a) (β w') :=
  (exists_secVal_eq hA W' (hβ.isHolOn_comp (isHolOn_secVal h₀ W a) fun w' hw' ↦
    (mem_preim_iff h₀ W).2 (by
      rw [hβ.pt_eq]
      exact (Z.mem_img_pullOpen.1 ((mem_preim_iff hA W').1 hw')).2))
    (Z.isBddOn_pull hβ a)).choose_spec w' hw'


omit hβ in
lemma holFun_eq_zero {M : (AnalyticSpace.complexAffineSpace.{u} n).Opens} {V : (space M).Opens}
    {x : Cn.{u} n} (hx : x ∈ img V) : holFun (0 : (space M).presheaf.obj (op V)) x = 0 := by
  obtain ⟨hxM, hxV⟩ := mem_img_iff.1 hx
  rw [← eval_space _ ⟨x, hxM⟩ hxV, map_zero]

/-- **Freeness transfers along the biholomorphism `χ`**: if `𝒜'` is free near `x ∈ D`, then `𝒜`
is free near `χ(x)`. -/
theorem isFreeSpanAt {x : space A} (hx : x.1 ∈ Z.D) {U₂ : (space A).Opens} {m₂ : ℕ}
    {e₀ : Fin m₂ → (boundedModule hA W').val.obj (op U₂)} (he₀ : IsFreeSpanAt hA W' e₀ x) :
    ∃ (U : (space N).Opens) (r : ℕ) (e : Fin r → (boundedModule h₀ W).val.obj (op U)),
      IsFreeSpanAt h₀ W e ⟨Φ.χ x.1, Z.E_sub _ (Z.mapsTo _ hx)⟩ := by
  classical
  obtain ⟨V, -, r, e, -, hxV, -, hspan, hindep⟩ := he₀
  have hyU : (⟨Φ.χ x.1, Z.E_sub _ (Z.mapsTo _ hx)⟩ : space N) ∈ Z.pushOpen V :=
    ⟨Z.mapsTo _ hx, by
      rw [Z.inv_χ _ hx]
      exact mem_img_iff.2 ⟨x.2, hxV⟩⟩
  have hsub : ∀ V'' ≤ Z.pushOpen V, Z.pullOpen V'' ≤ V := fun V'' h z hz ↦ by
    have hz' := (Z.mem_img_pushOpen.1 (img_mono h hz.2)).2
    rw [Z.inv_χ _ hz.1] at hz'
    exact (mem_img_iff.1 hz').2
  have hβmem : ∀ (V'' : (space N).Opens) (w : W.left), w ∈ preim h₀ W V'' →
      V'' ≤ Z.pushOpen V → ∃ w', β w' = w ∧ w' ∈ preim hA W' (Z.pullOpen V'') := by
    intro V'' w hw h
    have hwE : pt W w ∈ Z.E := (Z.mem_img_pushOpen.1 (img_mono h ((mem_preim_iff h₀ W).1 hw))).1
    obtain ⟨w', rfl⟩ := Z.exists_β hβ hwE
    refine ⟨w', rfl, (mem_preim_iff hA W').2 (Z.mem_img_pullOpen.2 ⟨Z.pt_mem_D hβ w' hwE, ?_⟩)⟩
    rw [← hβ.pt_eq]
    exact (mem_preim_iff h₀ W).1 hw
  refine ⟨Z.pushOpen V, r, fun k ↦ Z.pushSec hβ (e k), Z.pushOpen V, le_rfl, r,
    fun k ↦ Z.pushSec hβ (e k), fun k i ↦ if k = i then 1 else 0, hyU, fun k ↦ ?_,
    fun V'' h a ↦ ?_, fun V'' h c hc ↦ ?_⟩
  · simp only [ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    exact secVal_ext h₀ W fun w hw ↦ (evalFun_secVal_sectRes _ _ hw).symm
  · -- generation
    obtain ⟨c', hc'⟩ := hspan (Z.pullOpen V'') (hsub V'' h) (Z.pullSec hβ a)
    have himg : ∀ y ∈ img V'', Φ.χInv y ∈ img (Z.pullOpen V'') ∧ y ∈ Z.E := fun y hy ↦ by
      have hyE := (Z.mem_img_pushOpen.1 (img_mono h hy)).1
      refine ⟨Z.mem_img_pullOpen.2 ⟨Z.inv_mem _ hyE, ?_⟩, hyE⟩
      rw [Z.χ_inv _ hyE]
      exact hy
    have hd (k : Fin r) : DifferentiableOn ℂ (fun y ↦ holFun (c' k) (Φ.χInv y)) (img V'') :=
      fun y hy ↦ ((differentiableOn_holFun (c' k) _ (himg y hy).1).differentiableAt
        ((img (Z.pullOpen V'')).isOpen.mem_nhds (himg y hy).1)).comp_differentiableWithinAt y
        ((Z.differentiableOn_χInv y (himg y hy).2).mono fun y' hy' ↦ (himg y' hy').2)
    refine ⟨fun k ↦ OkaRing.ofDifferentiableOn _ (hd k), secVal_ext h₀ W fun w hw ↦ ?_⟩
    obtain ⟨w', rfl, hw'⟩ := hβmem V'' w hw h
    rw [evalFun_secVal_sum_smul _ _ _ hw, ← Z.evalFun_pullSec hβ a hw', hc',
      evalFun_secVal_sum_smul _ _ _ hw']
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [holFun_ofDifferentiableOn (hd k) ((mem_preim_iff h₀ W).1 hw), evalFun_secVal_sectRes _ _ hw,
      evalFun_secVal_sectRes _ _ hw', Z.evalFun_pushSec hβ _
        (preim_mono h₀ W h hw), ← hβ.pt_eq_χInv]
  · -- independence
    have himg : ∀ z ∈ img (Z.pullOpen V''), Φ.χ z ∈ img V'' := fun z hz ↦
      (Z.mem_img_pullOpen.1 hz).2
    have hd (k : Fin r) :
        DifferentiableOn ℂ (fun z ↦ holFun (c k) (Φ.χ z)) (img (Z.pullOpen V'')) :=
      fun z hz ↦ ((differentiableOn_holFun (c k) _ (himg z hz)).differentiableAt
        ((img V'').isOpen.mem_nhds (himg z hz))).comp_differentiableWithinAt z
        ((Z.differentiableOn_χ z (Z.mem_img_pullOpen.1 hz).1).mono fun z' hz' ↦
          (Z.mem_img_pullOpen.1 hz').1)
    let c'' : Fin r → (space A).presheaf.obj (op (Z.pullOpen V'')) :=
      fun k ↦ OkaRing.ofDifferentiableOn _ (hd k)
    have hc' : ∑ k, c'' k • sectRes (boundedModule hA W') (hsub V'' h) (e k) = 0 := by
      refine secVal_ext hA W' fun w' hw' ↦ ?_
      have hβw : β w' ∈ preim h₀ W V'' := (mem_preim_iff h₀ W).2 (by
        rw [hβ.pt_eq]
        exact (Z.mem_img_pullOpen.1 ((mem_preim_iff hA W').1 hw')).2)
      have h0 := congrArg (fun s ↦ evalFun (secVal h₀ W s) (β w')) hc
      simp only at h0
      rw [evalFun_secVal_sum_smul _ _ _ hβw, evalFun_secVal_zero hβw] at h0
      rw [evalFun_secVal_sum_smul _ _ _ hw', evalFun_secVal_zero hw', ← h0]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [holFun_ofDifferentiableOn (hd k) ((mem_preim_iff hA W').1 hw'),
        evalFun_secVal_sectRes _ _ hw', evalFun_secVal_sectRes _ _ hβw,
        Z.evalFun_pushSec hβ _ (preim_mono h₀ W h hβw), hβ.pt_eq]
    intro k
    have hk := hindep (Z.pullOpen V'') (hsub V'' h) _ hc' k
    refine eq_of_forall_eval_eq_restrict N fun y hy ↦ ?_
    rw [eval_space, map_zero]
    have hyimg : y.1 ∈ img V'' := mem_img_iff.2 ⟨y.2, hy⟩
    have hyE := (Z.mem_img_pushOpen.1 (img_mono h hyimg)).1
    have hz : Φ.χInv y.1 ∈ img (Z.pullOpen V'') := Z.mem_img_pullOpen.2
      ⟨Z.inv_mem _ hyE, by rw [Z.χ_inv _ hyE]; exact hyimg⟩
    have : holFun (c'' k) (Φ.χInv y.1) = holFun (c k) (Φ.χ (Φ.χInv y.1)) :=
      holFun_ofDifferentiableOn (hd k) hz
    rw [hk, Z.χ_inv _ hyE, holFun_eq_zero hz] at this
    exact this.symm

end ChartBiholo

end

end ComplexAnalytic.BoundedSections
