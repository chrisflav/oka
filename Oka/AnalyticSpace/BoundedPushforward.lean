/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.AnalyticSpace.FinitePushforwardCoherent
import Oka.AnalyticSpace.Continuity
import Oka.Algebra.Category.ModuleCat.Sheaf.Submodule
import Oka.Analytification.RET.ES.KummerEvalSections

/-!
# Sections of a pushforward which are bounded near a subset

Let `ρ : W ⟶ Y` be a morphism of complex analytic spaces and `D ⊆ Y`. A section `s` of `ρ_* 𝒪_W`
over an open `O ⊆ Y`, i.e. a section of `𝒪_W` over `ρ⁻¹ O`, is *bounded near `D`* if every point
`y ∈ O ∩ D` has a neighbourhood `N` such that `s` is bounded on `ρ⁻¹ (O ∩ N)`
(`ComplexAnalytic.AnalyticSpace.IsBoundedNear`). These sections form a sheaf of `𝒪_Y`-submodules
of `ρ_* 𝒪_W` (`ComplexAnalytic.AnalyticSpace.boundedSubmodule`), the sheaf of modules
`ComplexAnalytic.AnalyticSpace.boundedPushforward ρ D`. Over opens not meeting `D` it agrees with
`ρ_* 𝒪_W`.
-/

open CategoryTheory Opposite TopologicalSpace Topology Filter AlgebraicGeometry

universe u

namespace ComplexAnalytic.AnalyticSpace

noncomputable section

variable {W Y : AnalyticSpace.{u}} (ρ : W ⟶ Y) (D : Set Y)

/-- A section of `𝒪_W` over `ρ⁻¹ O` is **bounded near `D`** if every point of `O ∩ D` has a
neighbourhood `N` such that the section is bounded on `ρ⁻¹ (O ∩ N)`. -/
def IsBoundedNear {O : Y.Opens}
    (s : W.presheaf.obj (op ((Opens.map ρ.toLRSHom.base).obj O))) : Prop :=
  ∀ y ∈ O, y ∈ D → ∃ N ∈ 𝓝 y, ∃ C : ℝ, ∀ (w : W) (hw : ρ.toLRSHom.base w ∈ O),
    ρ.toLRSHom.base w ∈ N → ‖W.eval w hw s‖ ≤ C

variable {ρ D}

lemma isBoundedNear_of_disjoint {O : Y.Opens} (hO : Disjoint (O : Set Y) D)
    (s : W.presheaf.obj (op ((Opens.map ρ.toLRSHom.base).obj O))) : IsBoundedNear ρ D s :=
  fun _ hy hyD ↦ absurd hyD (Set.disjoint_left.1 hO hy)

lemma IsBoundedNear.add {O : Y.Opens}
    {s t : W.presheaf.obj (op ((Opens.map ρ.toLRSHom.base).obj O))}
    (hs : IsBoundedNear ρ D s) (ht : IsBoundedNear ρ D t) : IsBoundedNear ρ D (s + t) := by
  intro y hy hyD
  obtain ⟨N, hN, C, hC⟩ := hs y hy hyD
  obtain ⟨N', hN', C', hC'⟩ := ht y hy hyD
  refine ⟨N ∩ N', inter_mem hN hN', C + C', fun w hw hwN ↦ ?_⟩
  rw [map_add]
  exact (norm_add_le _ _).trans (add_le_add (hC w hw hwN.1) (hC' w hw hwN.2))

lemma isBoundedNear_zero {O : Y.Opens} :
    IsBoundedNear ρ D (0 : W.presheaf.obj (op ((Opens.map ρ.toLRSHom.base).obj O))) :=
  fun _ _ _ ↦ ⟨Set.univ, univ_mem, 0, fun w hw _ ↦ by rw [map_zero, norm_zero]⟩

lemma IsBoundedNear.mul {O : Y.Opens}
    {s t : W.presheaf.obj (op ((Opens.map ρ.toLRSHom.base).obj O))}
    (hs : IsBoundedNear ρ D s) (ht : IsBoundedNear ρ D t) : IsBoundedNear ρ D (s * t) := by
  intro y hy hyD
  obtain ⟨N, hN, C, hC⟩ := hs y hy hyD
  obtain ⟨N', hN', C', hC'⟩ := ht y hy hyD
  refine ⟨N ∩ N', inter_mem hN hN', max C 0 * max C' 0, fun w hw hwN ↦ ?_⟩
  rw [map_mul, norm_mul]
  exact mul_le_mul ((hC w hw hwN.1).trans (le_max_left _ _))
    ((hC' w hw hwN.2).trans (le_max_left _ _)) (norm_nonneg _) (le_max_right _ _)

/-- The pullback of a section of `𝒪_Y` is bounded near every point. -/
lemma isBoundedNear_c_app {O : Y.Opens} (r : Y.presheaf.obj (op O)) :
    IsBoundedNear ρ D (ρ.toLRSHom.c.app (op O) r) := by
  intro y hy _
  have h1 : ∀ᶠ z in 𝓝 (⟨y, hy⟩ : O), ‖Y.eval z.1 z.2 r‖ < ‖Y.eval y hy r‖ + 1 :=
    (Y.continuousAt_eval r ⟨y, hy⟩).norm.eventually (gt_mem_nhds (lt_add_one _))
  rw [nhds_subtype_eq_comap, eventually_comap] at h1
  refine ⟨_, h1, ‖Y.eval y hy r‖ + 1, fun w hw hwN ↦ ?_⟩
  rw [eval_c_app _ ρ.isCLinear w hw r]
  exact (hwN ⟨_, hw⟩ rfl).le

lemma IsBoundedNear.restrict {O O' : Y.Opens} (h : O' ≤ O)
    {s : W.presheaf.obj (op ((Opens.map ρ.toLRSHom.base).obj O))} (hs : IsBoundedNear ρ D s) :
    IsBoundedNear ρ D (W.presheaf.map (homOfLE ((Opens.map ρ.toLRSHom.base).monotone h)).op s) := by
  intro y hy hyD
  obtain ⟨N, hN, C, hC⟩ := hs y (h hy) hyD
  refine ⟨N, hN, C, fun w hw hwN ↦ ?_⟩
  rw [eval_presheaf_map]
  exact hC w (h hw) hwN

variable (ρ D)

/-- The sections of `ρ_* 𝒪_W` which are bounded near `D`, as a sheaf of `𝒪_Y`-submodules. -/
def boundedSubmodule : (LocallyRingedSpace.Hom.pushUnit ρ.toLRSHom).Submodule where
  obj O :=
    { carrier := {s | IsBoundedNear ρ D (O := O.unop) s}
      add_mem' := fun hs ht ↦ hs.add ht
      zero_mem' := isBoundedNear_zero
      smul_mem' := fun r s hs ↦ (isBoundedNear_c_app (O := O.unop) r).mul hs }
  map {O O'} f s hs := hs.restrict f.unop.le
  isSheaf {O} s hs := by
    intro y hy hyD
    obtain ⟨O', i, hO', hyO'⟩ := hs y hy
    obtain ⟨N, hN, C, hC⟩ := hO' y hyO' hyD
    refine ⟨N ∩ O', inter_mem hN (O'.isOpen.mem_nhds hyO'), C, fun w hw hwN ↦ ?_⟩
    have := hC w hwN.2 hwN.1
    erw [eval_presheaf_map] at this
    exact this

/-- **The pushforward bounded near `D`**: the sheaf of `𝒪_Y`-modules of sections of `ρ_* 𝒪_W`
which are bounded near `D`. -/
def boundedPushforward : SheafOfModules.{u} Y.ringSheaf :=
  (boundedSubmodule ρ D).toSheafOfModules

lemma mem_boundedSubmodule_iff {O : Y.Opens}
    (s : W.presheaf.obj (op ((Opens.map ρ.toLRSHom.base).obj O))) :
    s ∈ (boundedSubmodule ρ D).obj (op O) ↔ IsBoundedNear ρ D s :=
  Iff.rfl

end

end ComplexAnalytic.AnalyticSpace
