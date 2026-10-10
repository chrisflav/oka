/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Topology.Homotopy.Lifting

/-!
# Lifting convex sets through coverings, set-theoretic form

Throughout `Oka/Uniformization/` a covering map is a function `f : E → X` of the ambient spaces
together with `IsCoveringMapOn f V`: the domain of the covering is `f ⁻¹' V`. This file restates
Mathlib's lifting criterion (`IsCoveringMapOn.existsUnique_continuousMap_lifts`) for maps defined on
a convex subset `D` of a real normed space, in terms of `ContinuousOn` and `MapsTo` rather than
bundled maps out of subtypes, and records that homeomorphisms are covering maps.

## Main results

- `isCoveringMap_homeomorph`: a homeomorphism is a covering map.
- `IsCoveringMapOn.exists_lift_of_convex`: a continuous map `g : D → V` from a convex set lifts
  through a covering `f` on `V`, with prescribed value at one point.
- `IsCoveringMapOn.eqOn_of_lift`: two such lifts agreeing at one point of a preconnected set agree.
-/

open Set Function Topology

namespace Uniformization

/-- A homeomorphism is a covering map. -/
theorem isCoveringMap_homeomorph {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    (e : E ≃ₜ X) : IsCoveringMap e := by
  intro x
  let H : e ⁻¹' univ ≃ₜ ↥(univ : Set X) × PUnit.{1} := ((Homeomorph.Set.univ E).trans e).trans
      ((Homeomorph.Set.univ X).symm.trans (Homeomorph.prodPUnit (univ : Set X)).symm)
  have hU : IsEvenlyCovered e x PUnit.{1} :=
    ⟨inferInstance, univ, mem_univ x, isOpen_univ, isOpen_univ, H, fun y ↦ rfl⟩
  haveI : Unique (e ⁻¹' {x}) :=
    { default := ⟨e.symm x, by simp⟩
      uniq := fun y ↦ Subtype.ext (by
        have : e y = x := y.2
        simp [← this]) }
  exact hU.of_fiber_homeomorph (Homeomorph.homeomorphOfUnique _ _)

end Uniformization

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]

/-- **Lifting through a covering, convex source.** Let `f` be a covering on `V`, `D` a convex set
and `g` continuous on `D` with values in `V`. Given `a₀ ∈ D` and `e₀` over `g a₀`, there is a
continuous `σ` on `D` with `f ∘ σ = g` on `D` and `σ a₀ = e₀`. -/
theorem IsCoveringMapOn.exists_lift_of_convex {f : E → X} {V : Set X} (hf : IsCoveringMapOn f V)
    {D : Set F} (hD : Convex ℝ D) {g : F → X} (hg : ContinuousOn g D) (hgV : MapsTo g D V)
    {a₀ : F} (ha₀ : a₀ ∈ D) {e₀ : E} (he₀ : f e₀ = g a₀) :
    ∃ σ : F → E, ContinuousOn σ D ∧ (∀ a ∈ D, f (σ a) = g a) ∧ σ a₀ = e₀ := by
  haveI : Nonempty D := ⟨⟨a₀, ha₀⟩⟩
  haveI := hD.contractibleSpace ⟨a₀, ha₀⟩
  haveI := hD.locallyPathConnectedSpace
  let g' : C(D, X) := ⟨D.restrict g, hg.restrict⟩
  obtain ⟨F', ⟨hF0, hF⟩, -⟩ := hf.existsUnique_continuousMap_lifts g' (a₀ := ⟨a₀, ha₀⟩) he₀
    fun a ↦ hgV a.2
  classical
  refine ⟨fun a ↦ if h : a ∈ D then F' ⟨a, h⟩ else e₀, ?_, fun a ha ↦ ?_, by simp [ha₀, hF0]⟩
  · rw [continuousOn_iff_continuous_restrict]
    convert F'.continuous using 1
    funext a
    simp [a.2]
  · simp only [ha, dite_true]
    exact congrFun hF ⟨a, ha⟩

omit [NormedSpace ℝ F] in
/-- **Uniqueness of lifts.** Two continuous lifts through a covering on `V`, of the same map into
`V` on a preconnected set `D`, which agree at one point of `D`, agree on `D`. -/
theorem IsCoveringMapOn.eqOn_of_lift {f : E → X} {V : Set X} (hf : IsCoveringMapOn f V)
    {D : Set F} (hD : IsPreconnected D) {σ₁ σ₂ : F → E} (h₁ : ContinuousOn σ₁ D)
    (h₂ : ContinuousOn σ₂ D) (hV : ∀ a ∈ D, f (σ₁ a) ∈ V) (heq : ∀ a ∈ D, f (σ₁ a) = f (σ₂ a))
    {a₀ : F} (ha₀ : a₀ ∈ D) (h₀ : σ₁ a₀ = σ₂ a₀) : EqOn σ₁ σ₂ D := by
  classical
  have hcov := hf.isCoveringMap_restrictPreimage
  let τ₁ : F → f ⁻¹' V := fun a ↦ if h : a ∈ D then ⟨σ₁ a, hV a h⟩ else ⟨σ₁ a₀, hV a₀ ha₀⟩
  have hV₂ : ∀ a ∈ D, σ₂ a ∈ f ⁻¹' V := fun a h ↦ by
    rw [mem_preimage, ← heq a h]; exact hV a h
  let τ₂ : F → f ⁻¹' V := fun a ↦ if h : a ∈ D then ⟨σ₂ a, hV₂ a h⟩ else
    ⟨σ₁ a₀, hV a₀ ha₀⟩
  have hτ₁ : ContinuousOn τ₁ D := by
    rw [continuousOn_iff_continuous_restrict]
    have : D.restrict τ₁ = fun a : D ↦ ⟨σ₁ a, hV a a.2⟩ := by funext a; simp [τ₁, a.2]
    rw [this]
    exact (h₁.restrict).subtype_mk _
  have hτ₂ : ContinuousOn τ₂ D := by
    rw [continuousOn_iff_continuous_restrict]
    have : D.restrict τ₂ = fun a : D ↦ ⟨σ₂ a, hV₂ a a.2⟩ := by
      funext a; simp [τ₂, a.2]
    rw [this]
    exact (h₂.restrict).subtype_mk _
  have hcomp : EqOn (V.restrictPreimage f ∘ τ₁) (V.restrictPreimage f ∘ τ₂) D := by
    intro a ha
    apply Subtype.ext
    simp [τ₁, τ₂, ha, Set.restrictPreimage, heq a ha]
  have := hcov.eqOn_of_comp_eqOn hD hτ₁ hτ₂ hcomp ha₀ (by simp [τ₁, τ₂, ha₀, h₀])
  intro a ha
  have := congrArg Subtype.val (this ha)
  simpa [τ₁, τ₂, ha] using this

namespace Uniformization

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]

/-- Two continuous sections of a locally injective map over a preconnected set `V`, agreeing at
one point, agree on `V`. -/
theorem eqOn_of_sections [T2Space E] {f : E → X} {V : Set X} (hV : IsPreconnected V)
    {s₁ s₂ : X → E} (h₁ : ContinuousOn s₁ V) (h₂ : ContinuousOn s₂ V)
    (hs₁ : ∀ v ∈ V, f (s₁ v) = v) (hs₂ : ∀ v ∈ V, f (s₂ v) = v)
    (hinj : ∀ v ∈ V, ∃ W ∈ 𝓝 (s₁ v), InjOn f W) {v₀ : X} (hv₀ : v₀ ∈ V)
    (h₀ : s₁ v₀ = s₂ v₀) : EqOn s₁ s₂ V := by
  haveI : PreconnectedSpace V := Subtype.preconnectedSpace hV
  set g₁ : V → E := V.restrict s₁
  set g₂ : V → E := V.restrict s₂
  have hg₁ : Continuous g₁ := h₁.restrict
  have hg₂ : Continuous g₂ := h₂.restrict
  set A : Set V := {v | g₁ v = g₂ v}
  have hA : IsClopen A := by
    refine ⟨isClosed_eq hg₁ hg₂, isOpen_iff_mem_nhds.mpr fun v hv ↦ ?_⟩
    obtain ⟨W, hW, hWinj⟩ := hinj v v.2
    have hW₁ : g₁ ⁻¹' W ∈ 𝓝 v := hg₁.continuousAt.preimage_mem_nhds hW
    have hW₂ : g₂ ⁻¹' W ∈ 𝓝 v := hg₂.continuousAt.preimage_mem_nhds (by
      change W ∈ 𝓝 (s₂ v); rw [← show s₁ v = s₂ v from hv]; exact hW)
    filter_upwards [hW₁, hW₂] with u hu₁ hu₂
    exact hWinj hu₁ hu₂ (by simp only [g₁, g₂, restrict_apply, hs₁ u u.2, hs₂ u u.2])
  have hAu := hA.eq_univ ⟨⟨v₀, hv₀⟩, h₀⟩
  intro v hv
  have : (⟨v, hv⟩ : V) ∈ A := hAu ▸ mem_univ _
  exact this

/-- The image of a section of a locally injective continuous map over an open set is open. -/
theorem isOpen_image_of_section {f : E → X} {B V : Set X} (hVo : IsOpen V) (hVB : V ⊆ B)
    (hopen : IsOpen (f ⁻¹' B)) (hcont : ContinuousOn f (f ⁻¹' B))
    (hinj : ∀ e ∈ f ⁻¹' B, ∃ W ∈ 𝓝 e, InjOn f W) {s : X → E} (hs : ContinuousOn s V)
    (hsf : ∀ v ∈ V, f (s v) = v) : IsOpen (s '' V) := by
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨v, hv, rfl⟩
  have hB : s v ∈ f ⁻¹' B := by rw [mem_preimage, hsf v hv]; exact hVB hv
  obtain ⟨W, hW, hWinj⟩ := hinj _ hB
  have hfc : ContinuousAt f (s v) := hcont.continuousAt (hopen.mem_nhds hB)
  have hsc : ContinuousAt s v := hs.continuousAt (hVo.mem_nhds hv)
  have h1 : f ⁻¹' V ∈ 𝓝 (s v) := hfc.preimage_mem_nhds (by rw [hsf v hv]; exact hVo.mem_nhds hv)
  have h2 : f ⁻¹' (s ⁻¹' W) ∈ 𝓝 (s v) :=
    hfc.preimage_mem_nhds (by rw [hsf v hv]; exact hsc.preimage_mem_nhds hW)
  filter_upwards [h1, h2, hW] with e he1 he2 he3
  exact ⟨f e, he1, hWinj he2 he3 (hsf _ he1)⟩

/-- **Local sections give a covering.** Let `f` be continuous and locally injective on the open set
`f ⁻¹' B`. Suppose every point of `B` has an open preconnected neighbourhood `V ⊆ B` such that
through every point `e` over `V` there is a continuous section of `f` over `V`. Then `f` is a
covering map on `B`. -/
theorem isCoveringMapOn_of_sections [T2Space E] {f : E → X} {B : Set X}
    (hopen : IsOpen (f ⁻¹' B)) (hcont : ContinuousOn f (f ⁻¹' B))
    (hinj : ∀ e ∈ f ⁻¹' B, ∃ W ∈ 𝓝 e, InjOn f W)
    (hsec : ∀ x ∈ B, ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ V ⊆ B ∧ IsPreconnected V ∧
      ∀ e, f e ∈ V → ∃ s : X → E, ContinuousOn s V ∧ (∀ v ∈ V, f (s v) = v) ∧ s (f e) = e) :
    IsCoveringMapOn f B := by
  intro x hx
  obtain ⟨V, hVo, hxV, hVB, hVc, hV⟩ := hsec x hx
  have hinjV : ∀ {s : X → E}, (∀ v ∈ V, f (s v) = v) → ∀ v ∈ V, ∃ W ∈ 𝓝 (s v), InjOn f W :=
    fun hsf v hv ↦ hinj _ (by rw [mem_preimage, hsf v hv]; exact hVB hv)
  -- the fibre is discrete
  haveI hdisc : DiscreteTopology (f ⁻¹' {x}) := by
    refine discreteTopology_iff_isOpen_singleton.mpr fun e ↦ ?_
    have he : f e = x := e.2
    obtain ⟨W, hW, hWinj⟩ := hinj e (by rw [mem_preimage, he]; exact hx)
    obtain ⟨W', hW'W, hW'o, heW'⟩ := _root_.mem_nhds_iff.mp hW
    refine ⟨W', hW'o, ?_⟩
    ext e'
    simp only [mem_preimage, mem_singleton_iff]
    constructor
    · intro h
      exact Subtype.ext (hWinj (hW'W h) (hW'W heW') (by rw [e'.2, e.2]))
    · rintro rfl; exact heW'
  rcases (f ⁻¹' V).eq_empty_or_nonempty with hempty | ⟨e₀, he₀⟩
  · haveI : IsEmpty (f ⁻¹' {x}) := ⟨fun e ↦ by
      have : e.1 ∈ f ⁻¹' V := by rw [mem_preimage, e.2]; exact hxV
      rw [hempty] at this; exact this⟩
    exact IsEvenlyCovered.of_preimage_eq_empty _ (hVo.mem_nhds hxV) hempty
  haveI : Nonempty (X → E) := ⟨fun _ ↦ e₀⟩
  -- a section through each point of the fibre
  have hfib : ∀ i : f ⁻¹' {x}, f i.1 ∈ V := fun i ↦ by rw [i.2]; exact hxV
  choose s hs hsf hsi using fun i : f ⁻¹' {x} ↦ hV i.1 (hfib i)
  have hsx : ∀ i : f ⁻¹' {x}, s i x = i.1 := fun i ↦ by
    have := hsi i; rwa [show f i.1 = x from i.2] at this
  haveI : Nonempty (f ⁻¹' {x}) := by
    obtain ⟨t, ht, htf, hte⟩ := hV e₀ he₀
    exact ⟨⟨t x, htf x hxV⟩⟩
  have hopenU : ∀ i, IsOpen (s i '' V) := fun i ↦
    isOpen_image_of_section hVo hVB hopen hcont hinj (hs i) (hsf i)
  have hsame : ∀ {i : f ⁻¹' {x}} {t : X → E}, ContinuousOn t V → (∀ v ∈ V, f (t v) = v) →
      ∀ v ∈ V, s i v = t v → EqOn (s i) t V := fun {i} {t} ht htf v hv h ↦
    eqOn_of_sections hVc (hs i) ht (hsf i) htf (hinjV (hsf i)) hv h
  let T := IsOpen.trivializationDiscrete (f := f) (U := fun i ↦ s i '' V) (V := V) hVo
    (fun i W hWV ↦ by
      constructor
      · intro hW
        have := (hcont.isOpen_inter_preimage hopen hW).inter (hopenU i)
        convert this using 1
        ext e
        simp only [mem_inter_iff, mem_preimage]
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨⟨hVB (hWV h1), h1⟩, h2⟩
        · rintro ⟨⟨-, h1⟩, h2⟩; exact ⟨h1, h2⟩
      · intro hW
        have hWeq : W = V ∩ s i ⁻¹' (f ⁻¹' W ∩ s i '' V) := by
          ext w
          simp only [mem_inter_iff, mem_preimage, mem_image]
          constructor
          · intro hw
            exact ⟨hWV hw, by rw [hsf i w (hWV hw)]; exact hw, w, hWV hw, rfl⟩
          · rintro ⟨hwV, hw, -⟩
            rwa [hsf i w hwV] at hw
        rw [hWeq]
        exact (hs i).isOpen_inter_preimage hVo hW)
    (fun i ↦ by
      rintro _ ⟨v, hv, rfl⟩ _ ⟨v', hv', rfl⟩ h
      rw [hsf i v hv, hsf i v' hv'] at h
      rw [h])
    (fun i v hv ↦ ⟨s i v, ⟨v, hv, rfl⟩, hsf i v hv⟩)
    (fun i j hij ↦ by
      rw [Function.onFun, Set.disjoint_left]
      rintro _ ⟨v, hv, rfl⟩ ⟨v', hv', hvv'⟩
      apply hij
      have hvv : v' = v := by rw [← hsf j v' hv', hvv', hsf i v hv]
      rw [hvv] at hvv'
      have := hsame (hs j) (hsf j) v hv hvv'.symm hxV
      apply Subtype.ext
      rw [← hsx i, ← hsx j, this])
    (fun e he ↦ by
      obtain ⟨t, ht, htf, hte⟩ := hV e he
      let i : f ⁻¹' {x} := ⟨t x, htf x hxV⟩
      have := hsame (i := i) ht htf x hxV (hsx i)
      refine mem_iUnion.mpr ⟨i, f e, he, ?_⟩
      rw [this he, hte])
  exact .to_isEvenlyCovered_preimage (.of_trivialization (t := T) (by simpa [T] using hxV))

end Uniformization
