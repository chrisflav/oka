/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.AnalyticSpace.FinitePushforwardCoherent
import Oka.Geometry.RingedSpace.LocallyRingedSpace.ReflexiveHull
import Oka.AnalyticSpace.LocalIso
import Oka.AnalyticSpace.Continuity

/-!
# Hartogs extension across the complement of an open

A complex analytic space `Z` **has Hartogs extension across the complement of an open `O`**
(`ComplexAnalytic.AnalyticSpace.HasHartogsExtension`) if restriction `𝒪(Ω) → 𝒪(Ω ∩ O)` is
bijective for every open `Ω`. This file collects ways to obtain it:

* it is local: it suffices that every point of every open `Ω` has a neighbourhood `B ⊆ Ω` for which
  restriction is bijective (`ComplexAnalytic.AnalyticSpace.hasHartogsExtension_of_local`);
* it passes to larger opens `O' ⊇ O`
  (`ComplexAnalytic.AnalyticSpace.HasHartogsExtension.mono`);
* it passes from preimages `q⁻¹ V` of opens under a finite morphism `q` with Hausdorff source to
  all opens (`ComplexAnalytic.AnalyticSpace.hasHartogsExtension_of_isFinite`), since `q⁻¹ V`
  splits into a disjoint union of small neighbourhoods of the points of a fibre.
-/

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry LocallyRingedSpace

universe u

namespace ComplexAnalytic.AnalyticSpace

variable {Z : AnalyticSpace.{u}}

/-- `Z` **has Hartogs extension across the complement of `O`**: restriction
`𝒪(Ω) → 𝒪(Ω ∩ O)` is bijective for every open `Ω`. -/
def HasHartogsExtension (Z : AnalyticSpace.{u}) (O : Z.Opens) : Prop :=
  ∀ Ω : Z.Opens, Function.Bijective (Z.res (inf_le_left : Ω ⊓ O ≤ Ω))

/-- **Hartogs extension is local.** -/
theorem hasHartogsExtension_of_local {O : Z.Opens}
    (h : ∀ Ω : Z.Opens, ∀ x ∈ Ω, ∃ (B : Z.Opens) (_ : B ≤ Ω), x ∈ B ∧
      Function.Bijective (Z.res (inf_le_left : B ⊓ O ≤ B))) :
    HasHartogsExtension Z O := by
  -- injectivity
  have hinj : ∀ Ω : Z.Opens, Function.Injective (Z.res (inf_le_left : Ω ⊓ O ≤ Ω)) := by
    intro Ω s t hst
    refine res_eq_of_locally fun x hx ↦ ?_
    obtain ⟨B, hBΩ, hxB, hB⟩ := h Ω x hx
    refine ⟨B, hBΩ, hxB, hB.1 ?_⟩
    have hle : B ⊓ O ≤ Ω ⊓ O := inf_le_inf_right O hBΩ
    rw [res_res, res_res, ← res_res _ hle inf_le_left, ← res_res _ hle inf_le_left t, hst]
  intro Ω
  refine ⟨hinj Ω, fun s ↦ ?_⟩
  -- local extensions
  have hloc : ∀ x ∈ Ω, ∃ (B : Z.Opens) (hBΩ : B ≤ Ω), x ∈ B ∧ ∃ u : Z.presheaf.obj (op B),
      Z.res (inf_le_left : B ⊓ O ≤ B) u = Z.res (inf_le_inf_right O hBΩ) s := by
    intro x hx
    obtain ⟨B, hBΩ, hxB, hB⟩ := h Ω x hx
    obtain ⟨u, hu⟩ := hB.2 (Z.res (inf_le_inf_right O hBΩ) s)
    exact ⟨B, hBΩ, hxB, u, hu⟩
  choose B hBΩ hxB u hu using hloc
  obtain ⟨t, ht⟩ := exists_sectRes_eq_of_locally (SheafOfModules.unit Z.ringSheaf) B hBΩ hxB u
    fun x hx x' hx' ↦ by
      refine hinj (B x hx ⊓ B x' hx') ?_
      refine (res_res _ _ _ _).trans (Eq.trans ?_ (res_res _ _ _ _).symm)
      have h₁ : B x hx ⊓ B x' hx' ⊓ O ≤ B x hx ⊓ O := inf_le_inf_right _ inf_le_left
      have h₂ : B x hx ⊓ B x' hx' ⊓ O ≤ B x' hx' ⊓ O := inf_le_inf_right _ inf_le_right
      refine (res_res _ h₁ inf_le_left _).symm.trans ?_
      refine Eq.trans ?_ (res_res _ h₂ inf_le_left _)
      rw [hu, hu, res_res, res_res]
  refine ⟨t, res_eq_of_locally fun y hy ↦ ?_⟩
  refine ⟨B y hy.1 ⊓ O, inf_le_inf_right O (hBΩ y hy.1), ⟨hxB y hy.1, hy.2⟩, ?_⟩
  refine (res_res _ _ _ _).trans ?_
  have h₁ : B y hy.1 ⊓ O ≤ B y hy.1 := inf_le_left
  refine (res_res _ h₁ (hBΩ y hy.1) t).symm.trans ?_
  change Z.res h₁ (sectRes (SheafOfModules.unit Z.ringSheaf) (hBΩ y hy.1) t) = _
  rw [ht, hu]
  rfl

/-- **Hartogs extension passes to larger opens.** -/
theorem HasHartogsExtension.mono {O O' : Z.Opens} (h : HasHartogsExtension Z O) (hO : O ≤ O') :
    HasHartogsExtension Z O' := by
  intro Ω
  have hle : Ω ⊓ O ≤ Ω ⊓ O' := inf_le_inf_left Ω hO
  refine ⟨fun s t hst ↦ (h Ω).1 ?_, fun s' ↦ ?_⟩
  · rw [← res_res _ hle inf_le_left, ← res_res _ hle inf_le_left t, hst]
  · obtain ⟨t, ht⟩ := (h Ω).2 (Z.res hle s')
    refine ⟨t, (h (Ω ⊓ O')).1 ?_⟩
    have h₁ : Ω ⊓ O' ⊓ O ≤ Ω ⊓ O := inf_le_inf_right O inf_le_left
    rw [res_res, ← res_res _ h₁ inf_le_left, ht, res_res]

/-- A restriction is bijective if it becomes so after splitting off a disjoint open: if `W` is the
disjoint union of `B` and `B'` and restriction `𝒪(W) → 𝒪(W ∩ O)` is bijective, so is
`𝒪(B) → 𝒪(B ∩ O)`. -/
theorem bijective_res_of_disjoint {O W B B' : Z.Opens} (hB : B ≤ W) (hB' : B' ≤ W)
    (hW : W ≤ B ⊔ B') (hdisj : B ⊓ B' = ⊥)
    (hres : Function.Bijective (Z.res (inf_le_left : W ⊓ O ≤ W))) :
    Function.Bijective (Z.res (inf_le_left : B ⊓ O ≤ B)) := by
  let N := SheafOfModules.unit Z.ringSheaf
  let P : Bool → Z.Opens := fun i ↦ if i then B else B'
  have hP : ∀ i, P i ≤ W := fun i ↦ by cases i <;> simp [P, hB, hB']
  have hPW : W ≤ ⨆ i, P i := hW.trans (sup_le (le_iSup P true) (le_iSup P false))
  have hPdisj : ∀ i j, i ≠ j → P i ⊓ P j = ⊥ := by
    intro i j hij
    cases i <;> cases j <;> simp_all [P, inf_comm]
  let PO : Bool → Z.Opens := fun i ↦ P i ⊓ O
  have hPO : ∀ i, PO i ≤ W ⊓ O := fun i ↦ inf_le_inf_right O (hP i)
  have hPOW : W ⊓ O ≤ ⨆ i, PO i := fun x hx ↦ by
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hPW hx.1)
    exact Opens.mem_iSup.2 ⟨i, hi, hx.2⟩
  have hPOdisj : ∀ i j, i ≠ j → PO i ⊓ PO j = ⊥ := fun i j hij ↦
    eq_bot_iff.2 fun x hx ↦ (hPdisj i j hij).le ⟨hx.1.1, hx.2.1⟩
  constructor
  · suffices hker : ∀ s, Z.res (inf_le_left : B ⊓ O ≤ B) s = 0 → s = 0 from fun s s' h ↦
      sub_eq_zero.1 (hker _ ((map_sub _ _ _).trans (sub_eq_zero.2 h)))
    intro s hs
    obtain ⟨t, ht, ht'⟩ := exists_extend_zero N P hP hPW hPdisj true s
    have ht0 : Z.res (inf_le_left : W ⊓ O ≤ W) t = 0 := by
      refine sectRes_ext N PO hPO hPOW _ 0 fun i ↦ ?_
      change Z.res _ (Z.res _ t) = Z.res _ 0
      rw [res_zero, res_res]
      cases i
      · rw [← res_res _ (inf_le_left : PO false ≤ P false) (hP false)]
        change Z.res _ (sectRes N (hP false) t) = 0
        rw [ht' false Bool.false_ne_true]
        exact map_zero _
      · rw [← res_res _ (inf_le_left : PO true ≤ P true) (hP true)]
        change Z.res _ (sectRes N (hP true) t) = 0
        rw [ht]
        exact hs
    rw [← ht, (hres.1 (ht0.trans (res_zero _ _).symm) : t = 0)]
    exact res_zero _ _
  · intro s
    obtain ⟨t, ht, -⟩ := exists_extend_zero N PO hPO hPOW hPOdisj true s
    obtain ⟨w, hw⟩ := hres.2 t
    refine ⟨Z.res hB w, (res_res _ _ _ _).trans ?_⟩
    refine (res_res _ (hPO true) (inf_le_left : W ⊓ O ≤ W) w).symm.trans ?_
    rw [hw]
    exact ht

/-- **Hartogs extension from preimages under a finite morphism.** If `q : X' ⟶ S` is finite,
`X'` is Hausdorff and restriction `𝒪(q⁻¹ V) → 𝒪(q⁻¹ V ∩ q⁻¹ O)` is bijective for every open
`V ⊆ S`, then `X'` has Hartogs extension across the complement of `q⁻¹ O`. -/
theorem hasHartogsExtension_of_isFinite {X' S : AnalyticSpace.{u}} (q : X' ⟶ S) [IsFinite q]
    [T2Space X'] (O : S.Opens)
    (h : ∀ V : S.Opens, Function.Bijective (X'.res (inf_le_left :
      (Opens.map q.toLRSHom.base).obj V ⊓ (Opens.map q.toLRSHom.base).obj O ≤
        (Opens.map q.toLRSHom.base).obj V))) :
    HasHartogsExtension X' ((Opens.map q.toLRSHom.base).obj O) := by
  classical
  refine hasHartogsExtension_of_local fun Ω x hx ↦ ?_
  haveI : Finite (q.toLRSHom.base ⁻¹' {q.toLRSHom.base x}) := IsFinite.finite_fiber _
  obtain ⟨V, P, -, -, hxP, hPU, hPV, hdisj, hcov⟩ := Hom.exists_fibre_cover q.toLRSHom
    IsFinite.isClosedMap (y := q.toLRSHom.base x) (Set.toFinite _) (W := ⊤) trivial
    (fun x' ↦ if x'.1 = x then Ω else ⊤) fun x' ↦ by
      split_ifs with h
      · rw [h]
        exact hx
      · trivial
  let x₀ : q.toLRSHom.base ⁻¹' {q.toLRSHom.base x} := ⟨x, rfl⟩
  have hBΩ : P x₀ ≤ Ω := (hPU x₀).trans (by simp [x₀])
  refine ⟨P x₀, hBΩ, hxP x₀, ?_⟩
  refine bijective_res_of_disjoint (hPV x₀) (B' := ⨆ x' : {x' // x' ≠ x₀}, P x'.1)
    (iSup_le fun x' ↦ hPV x'.1) (fun z hz ↦ ?_) ?_ (h V)
  · obtain ⟨x', hx'⟩ := Opens.mem_iSup.1 (hcov hz)
    by_cases hx'₀ : x' = x₀
    · subst hx'₀
      exact Or.inl hx'
    · exact Or.inr (Opens.mem_iSup.2 ⟨⟨x', hx'₀⟩, hx'⟩)
  · refine eq_bot_iff.2 fun z hz ↦ ?_
    obtain ⟨x', hx'⟩ := Opens.mem_iSup.1 hz.2
    exact ((hdisj x₀ x'.1 (Ne.symm x'.2)).le ⟨hz.1, hx'⟩)

/-- The open where two global functions do not both vanish. -/
def nonvanishingOpens (Z : AnalyticSpace.{u}) (g h : Z.presheaf.obj (op ⊤)) : Z.Opens :=
  ⟨{z | ¬ (Z.eval (U := ⊤) z trivial g = 0 ∧ Z.eval (U := ⊤) z trivial h = 0)}, by
    refine (IsClosed.inter (isClosed_eq (Z.continuous_eval_top g) continuous_const)
      (isClosed_eq (Z.continuous_eval_top h) continuous_const)).isOpen_compl⟩

lemma mem_nonvanishingOpens_iff (Z : AnalyticSpace.{u}) (g h : Z.presheaf.obj (op ⊤)) (z : Z) :
    z ∈ nonvanishingOpens Z g h ↔
      ¬ (Z.eval (U := ⊤) z trivial g = 0 ∧ Z.eval (U := ⊤) z trivial h = 0) :=
  Iff.rfl

end ComplexAnalytic.AnalyticSpace
