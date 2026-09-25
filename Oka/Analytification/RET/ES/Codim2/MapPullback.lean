/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.ES.Codim2.DescentBaseChange

/-!
# Finite étale covers pulled back along holomorphic open embeddings

Let `χ : N°' → N°` be a holomorphic open embedding between opens of `ℂⁿ`, with a holomorphic
inverse `χ⁻¹` on an open `R ⊇ χ(N°')` (`ComplexAnalytic.BoundedSections.ChartMap`); e.g. a chart
of a blow-up. A finite étale cover `W'` of `N°'` with a continuous map `β : W' → W` over `χ` which
identifies `W'` with `W ×_{N°} N°'` at the level of points is recorded by
`ComplexAnalytic.BoundedSections.IsMapPullback`. The base change
`ComplexAnalytic.BoundedSections.mapCover` is an example
(`ComplexAnalytic.BoundedSections.isMapPullback_mapCover`).

Then `β` is an open embedding (`…IsMapPullback.isOpenEmbedding`), and holomorphic functions on `W`
and on `W'` correspond along `β` (`…IsMapPullback.isHolOn_comp`,
`…IsMapPullback.isHolOn_liftFun`), where `…IsMapPullback.liftFun g` is the function `g ∘ β⁻¹` on
the image of `β`, extended by `0`.

## Main definitions

- `ComplexAnalytic.BoundedSections.ChartMap N₀' N₀`: the embedding `χ` with its inverse.
- `ComplexAnalytic.BoundedSections.IsMapPullback Φ W W' β`: `W'` is the pullback of `W`.
- `ComplexAnalytic.BoundedSections.mapCover`: the base change of `W` along `χ`.
-/

open CategoryTheory Opposite AlgebraicGeometry Topology TopologicalSpace Filter

universe u

namespace ComplexAnalytic.BoundedSections

open AnalyticSpace

noncomputable section

variable {n : ℕ}

/-- **A holomorphic open embedding `χ : N°' → N°`** with a holomorphic inverse `χ⁻¹` on an open
`R ⊇ χ(N°')`, and with `N°' = χ⁻¹(N°)`. -/
structure ChartMap (N₀' N₀ : (AnalyticSpace.complexAffineSpace.{u} n).Opens) where
  /-- The embedding. -/
  χ : Cn.{u} n → Cn.{u} n
  /-- Its inverse. -/
  χInv : Cn.{u} n → Cn.{u} n
  /-- The domain of the inverse. -/
  R : Set (Cn.{u} n)
  isOpen_R : IsOpen R
  differentiableOn_χ : DifferentiableOn ℂ χ {x | x ∈ N₀'}
  differentiableOn_χInv : DifferentiableOn ℂ χInv R
  mem_iff : ∀ x, x ∈ N₀' ↔ χ x ∈ N₀
  χ_mem_R : ∀ x ∈ N₀', χ x ∈ R
  χInv_χ : ∀ x ∈ N₀', χInv (χ x) = x
  χ_χInv : ∀ y ∈ R, χInv y ∈ N₀' → χ (χInv y) = y

namespace ChartMap

variable {N₀' N₀ : (AnalyticSpace.complexAffineSpace.{u} n).Opens} (Φ : ChartMap N₀' N₀)

lemma injOn : Set.InjOn Φ.χ {x | x ∈ N₀'} := fun x hx y hy h ↦ by
  rw [← Φ.χInv_χ x hx, ← Φ.χInv_χ y hy, h]

/-- `χ` restricted to `N°'` is an open embedding. -/
lemma isOpenEmbedding : IsOpenEmbedding fun x : N₀' ↦ Φ.χ x.1 := by
  refine .of_continuous_injective_isOpenMap
    (Φ.differentiableOn_χ.continuousOn.comp_continuous continuous_subtype_val fun x ↦ x.2)
    (fun x y h ↦ Subtype.ext (Φ.injOn x.2 y.2 h)) fun U hU ↦ ?_
  have heq : (fun x : N₀' ↦ Φ.χ x.1) '' U = Φ.R ∩ Φ.χInv ⁻¹' (Subtype.val '' U) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨Φ.χ_mem_R _ x.2, x, hx, (Φ.χInv_χ _ x.2).symm⟩
    · rintro ⟨hyR, x, hx, hxy⟩
      refine ⟨x, hx, ?_⟩
      change Φ.χ x.1 = y
      have hx2 : Φ.χInv y ∈ N₀' := hxy ▸ x.2
      calc Φ.χ x.1 = Φ.χ (Φ.χInv y) := congrArg Φ.χ hxy
        _ = y := Φ.χ_χInv y hyR hx2
  rw [heq]
  exact Φ.differentiableOn_χInv.continuousOn.isOpen_inter_preimage Φ.isOpen_R
    (N₀'.isOpenEmbedding.isOpenMap _ hU)

/-- The coordinates of `χ`, as holomorphic functions on `N°'`. -/
def coord (k : ULift.{u} (Fin n)) : (space N₀').presheaf.obj (op ⊤) :=
  OkaRing.ofDifferentiableOn (fun x ↦ Φ.χ x k)
    (((differentiableOn_pi.1 Φ.differentiableOn_χ) k).mono fun x hx ↦
      (mem_functor_obj_top_iff N₀' x).1 hx)

lemma okaMapOpen_base (x : space N₀') : (okaMapOpen Φ.coord).toLRSHom.base x = Φ.χ x.1 := by
  change okaMapOpenFun Φ.coord x.1 = _
  funext k
  exact OkaRing.toGlobalFun_apply (U := img (⊤ : (space N₀').Opens)) _
    ((mem_functor_obj_top_iff N₀' x.1).2 x.2)

lemma range_subset : Set.range (okaMapOpen Φ.coord).toLRSHom.base ⊆ (N₀ : Set _) := by
  rintro _ ⟨x, rfl⟩
  rw [okaMapOpen_base]
  exact (Φ.mem_iff _).1 x.2

/-- `χ` as a morphism of analytic spaces `N°' ⟶ N°`. -/
def hom : space N₀' ⟶ space N₀ :=
  AnalyticSpace.liftRestrict (okaMapOpen Φ.coord) N₀ Φ.range_subset

lemma coe_hom_base (x : space N₀') : (Φ.hom.toLRSHom.base x).1 = Φ.χ x.1 :=
  (congrArg (fun f ↦ f.toLRSHom.base x)
    (AnalyticSpace.liftRestrict_fac _ N₀ Φ.range_subset)).trans (Φ.okaMapOpen_base x)

end ChartMap

variable {N₀' N₀ : (AnalyticSpace.complexAffineSpace.{u} n).Opens}

/-- **`W'` is the pullback of `W` along `χ`**, at the level of points: `β : W' → W` is continuous
over `χ`, and every point of `W` over `χ(x')` has a unique preimage over `x'`. -/
structure IsMapPullback (Φ : ChartMap N₀' N₀) (W : FiniteEtaleOver (space N₀))
    (W' : FiniteEtaleOver (space N₀')) (β : W'.left → W.left) : Prop where
  continuous : Continuous β
  pt_eq : ∀ w, pt W (β w) = Φ.χ (pt W' w)
  ext : ∀ w₁ w₂, pt W' w₁ = pt W' w₂ → β w₁ = β w₂ → w₁ = w₂
  exists_lift : ∀ w x, pt W w = Φ.χ x → ∃ w', pt W' w' = x ∧ β w' = w

/-- The points of `W` lying over `ℂⁿ` form a local homeomorphism `W → ℂⁿ`. -/
lemma isLocalHomeomorph_pt (W : FiniteEtaleOver (space N₀)) : IsLocalHomeomorph (pt W) :=
  N₀.isOpenEmbedding.isLocalHomeomorph.comp (IsLocalIso.isLocalHomeomorph (f := cov W))

namespace IsMapPullback

variable {Φ : ChartMap N₀' N₀} {W : FiniteEtaleOver (space N₀)} {W' : FiniteEtaleOver (space N₀')}
  {β : W'.left → W.left} (hβ : IsMapPullback Φ W W' β)
include hβ

lemma injective : Function.Injective β := fun w₁ w₂ h ↦ by
  have h' : Φ.χ (pt W' w₁) = Φ.χ (pt W' w₂) := by rw [← hβ.pt_eq, ← hβ.pt_eq, h]
  exact hβ.ext _ _ (Φ.injOn (pt_mem W' w₁) (pt_mem W' w₂) h') h

/-- **`β` is an open embedding.** -/
theorem isOpenEmbedding : IsOpenEmbedding β := by
  have h₁ : IsLocalHomeomorph fun w ↦ Φ.χ (pt W' w) :=
    Φ.isOpenEmbedding.isLocalHomeomorph.comp (IsLocalIso.isLocalHomeomorph (f := cov W'))
  have h₂ : IsLocalHomeomorph (pt W ∘ β) := by
    have : pt W ∘ β = fun w ↦ Φ.χ (pt W' w) := funext hβ.pt_eq
    rw [this]
    exact h₁
  exact (h₂.of_comp (isLocalHomeomorph_pt W) hβ.continuous).isOpenEmbedding_of_injective
    hβ.injective

lemma mem_range_iff {w : W.left} :
    w ∈ Set.range β ↔ pt W w ∈ Φ.R ∧ Φ.χInv (pt W w) ∈ N₀' := by
  constructor
  · rintro ⟨w', rfl⟩
    rw [hβ.pt_eq, Φ.χInv_χ _ (pt_mem W' w')]
    exact ⟨Φ.χ_mem_R _ (pt_mem W' w'), pt_mem W' w'⟩
  · rintro ⟨hR, hN⟩
    obtain ⟨w', -, hw'⟩ := hβ.exists_lift w _ (Φ.χ_χInv _ hR hN).symm
    exact ⟨w', hw'⟩

lemma pt_eq_χInv (w' : W'.left) : pt W' w' = Φ.χInv (pt W (β w')) := by
  rw [hβ.pt_eq, Φ.χInv_χ _ (pt_mem W' w')]

omit hβ in
variable (β) in
open Classical in
/-- The function `g ∘ β⁻¹` on the image of `β`, extended by `0`. -/
def liftFun (g : W'.left → ℂ) (w : W.left) : ℂ :=
  if h : ∃ w', β w' = w then g h.choose else 0

lemma liftFun_apply (g : W'.left → ℂ) (w' : W'.left) : liftFun β g (β w') = g w' := by
  have h : ∃ w'', β w'' = β w' := ⟨w', rfl⟩
  rw [liftFun, dif_pos h, hβ.injective h.choose_spec]

/-- **Holomorphic functions on `W` pull back to holomorphic functions on `W'`.** -/
lemma isHolOn_comp {f : W.left → ℂ} {O : Set W.left} (hf : IsHolOn W f O) {O' : Set W'.left}
    (hmaps : ∀ w ∈ O', β w ∈ O) : IsHolOn W' (fun w ↦ f (β w)) O' := by
  intro w hw
  obtain ⟨F, hF⟩ := hf (β w) (hmaps w hw)
  refine ⟨fun x ↦ F (Φ.χ x), ?_⟩
  filter_upwards [hβ.continuous.continuousAt.preimage_mem_nhds hF] with w' hw'
  have hχ : DifferentiableAt ℂ Φ.χ (pt W' w') :=
    Φ.differentiableOn_χ.differentiableAt (N₀'.isOpen.mem_nhds (pt_mem W' w'))
  refine ⟨?_, ?_⟩
  · have := hw'.1
    rw [hβ.pt_eq] at this
    exact this.comp _ hχ
  · rw [hw'.2, hβ.pt_eq]

/-- **Holomorphic functions on `W'` push forward to holomorphic functions on the image of
`β`.** -/
lemma isHolOn_liftFun {g : W'.left → ℂ} {O' : Set W'.left} (hg : IsHolOn W' g O') :
    IsHolOn W (liftFun β g) (β '' O') := by
  rintro _ ⟨w, hw, rfl⟩
  obtain ⟨G, hG⟩ := hg w hw
  refine ⟨fun x ↦ G (Φ.χInv x), ?_⟩
  rw [← hβ.isOpenEmbedding.map_nhds_eq w, Filter.eventually_map]
  filter_upwards [hG] with w' hw'
  have hR : pt W (β w') ∈ Φ.R := by
    rw [hβ.pt_eq]
    exact Φ.χ_mem_R _ (pt_mem W' w')
  have hInv : DifferentiableAt ℂ Φ.χInv (pt W (β w')) :=
    Φ.differentiableOn_χInv.differentiableAt (Φ.isOpen_R.mem_nhds hR)
  refine ⟨?_, ?_⟩
  · have := hw'.1
    rw [hβ.pt_eq_χInv] at this
    exact this.comp _ hInv
  · rw [hβ.liftFun_apply, hw'.2, hβ.pt_eq_χInv]

end IsMapPullback

/-! ### The base change -/

variable (Φ : ChartMap N₀' N₀) (W : FiniteEtaleOver (space N₀))

/-- **The pullback** `W ×_{N°} N°'` of a finite étale cover `W` of `N°` along `χ`. -/
def mapCover : FiniteEtaleOver (space N₀') :=
  MorphismProperty.Over.mk ⊤ (baseChangeSnd (cov W) Φ.hom) (isFiniteEtale_baseChangeSnd _ _)

/-- The projection `W ×_{N°} N°' → W`, as a map of points. -/
def mapProj : (mapCover Φ W).left → W.left :=
  (baseChangeFst (cov W) Φ.hom).toLRSHom.base

/-- The points of the pullback: pairs `(w, x')` with `p(w) = χ(x')`. -/
abbrev MapPoint : Type u :=
  Function.Pullback (cov W).toLRSHom.base Φ.hom.toLRSHom.base

lemma pt_mapCover (w : MapPoint Φ W) : pt (mapCover Φ W) w = w.1.2.1 :=
  rfl

lemma mapProj_apply (w : MapPoint Φ W) : mapProj Φ W w = w.1.1 := by
  unfold mapProj
  rw [base_baseChangeFst]
  rfl

instance [T2Space W.left] : T2Space (mapCover Φ W).left := by
  haveI : T2Space (AnalyticSpace.complexAffineSpace.{u} n) := by
    change T2Space (Cn.{u} n)
    infer_instance
  haveI : T2Space (space N₀') := by
    change T2Space N₀'
    infer_instance
  change T2Space (Function.Pullback (cov W).toLRSHom.base Φ.hom.toLRSHom.base)
  infer_instance

/-- **The base change along `χ` is the pullback along `χ`.** -/
theorem isMapPullback_mapCover : IsMapPullback Φ W (mapCover Φ W) (mapProj Φ W) where
  continuous := (baseChangeFst (cov W) Φ.hom).toLRSHom.base.hom.continuous
  pt_eq w := by
    rw [mapProj_apply, pt_mapCover, ← Φ.coe_hom_base]
    exact congrArg Subtype.val w.2
  ext w₁ w₂ h₁ h₂ := by
    rw [pt_mapCover, pt_mapCover] at h₁
    rw [mapProj_apply, mapProj_apply] at h₂
    exact Subtype.ext (Prod.ext h₂ (Subtype.ext h₁))
  exists_lift w x h := by
    have hx : x ∈ N₀' := (Φ.mem_iff x).2 (h ▸ pt_mem W w)
    refine ⟨(⟨(w, ⟨x, hx⟩), Subtype.ext ?_⟩ : MapPoint Φ W), rfl, mapProj_apply _ _ _⟩
    exact h.trans (Φ.coe_hom_base ⟨x, hx⟩).symm

end

end ComplexAnalytic.BoundedSections
