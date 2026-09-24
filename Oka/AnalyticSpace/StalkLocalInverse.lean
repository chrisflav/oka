/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.AnalyticSpace.HolomorphicMap

/-!
# The germ dictionary: a local inverse makes a holomorphic map an isomorphism on stalks

`Oka/AnalyticSpace/HolomorphicMap.lean` turns a family `u : κ → OkaRing ⊤` of entire functions
on `ℂ^ι` into a morphism of locally ringed spaces `ComplexAnalytic.okaMapHom u : ℂ^ι ⟶ ℂ^κ`
whose pullback of sections is **composition with `ComplexAnalytic.okaMapFun u`**. This file reads
that off at a stalk: the map `𝒪_{ℂ^κ, F z} ⟶ 𝒪_{ℂ^ι, z}` is precomposition of germs with
`F = okaMapFun u`, and precomposition with a map that has an analytic local inverse near `z` is
bijective.

**No analysis is done here.** The local inverse is a *hypothesis*: a function `σ` analytic at
`F z`, inverse to `F` on a neighbourhood on each side. Everything below is the translation
between that hypothesis and the stalk map, which is what nothing in this repository had.
Mathlib's `AnalyticAt.analyticAt_localInverse` and `analyticAt_comp_iff_of_deriv_ne_zero`
(`Mathlib/Analysis/Calculus/InverseFunctionTheorem/Analytic.lean`) are what produce such a `σ` in
one variable.

## Why the two halves are not symmetric

**Injectivity uses only the right inverse.** A germ killed by precomposition is a section
vanishing on `F ⁻¹' W'` for some `W'`; to see that the section itself vanishes near `F z` one
writes a point `w` near `F z` as `F (σ w)` and evaluates. Analyticity of `σ` is not used, only
its continuity, so this half holds for a topological local section.

**Surjectivity uses only the left inverse, and there analyticity is the whole point.** The
preimage of a germ `t` at `z` is `t ∘ σ`, which is a *holomorphic* function near `F z` exactly
because `σ` is analytic — `OkaAnalytic.comp_analyticOn` is the statement that
composing a holomorphic function with an analytic map is holomorphic, and it is the only place
in the file where the sheaf being a sheaf of *holomorphic* functions is used.

## Main results

- `ComplexAnalytic.injective_stalkMap_okaMapHom`
- `ComplexAnalytic.surjective_stalkMap_okaMapHom`
- `ComplexAnalytic.isIso_stalkMap_okaMapHom`: **a holomorphic map with an analytic local inverse
  at a point is an isomorphism on the stalk there.**
- `ComplexAnalytic.AnalyticSpace.isIso_stalkMap_okaMap`: the same for the morphism of complex
  analytic spaces.
-/

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry Filter Topology

universe u

noncomputable section

namespace ComplexAnalytic

variable {ι κ : Type u} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable {u : κ → OkaRing (⊤ : Opens (ι → ℂ))} {z : ι → ℂ} {σ : (κ → ℂ) → (ι → ℂ)}

omit [DecidableEq ι] [DecidableEq κ] in
/-- **Precomposition with a map admitting a continuous right inverse is injective on germs.**

If a germ at `okaMapFun u z` pulls back to zero then the pulling-back function vanishes on a
neighbourhood `V` of `z`; and every `w` near `okaMapFun u z` is `okaMapFun u (σ w)` with `σ w`
in `V`, so the germ itself is the germ of a function vanishing near `okaMapFun u z`.

Only continuity of `σ` at the point is used. -/
theorem injective_stalkMap_okaMapHom (hcont : ContinuousAt σ (okaMapFun u z))
    (hσz : σ (okaMapFun u z) = z)
    (hright : ∀ᶠ w in 𝓝 (okaMapFun u z), okaMapFun u (σ w) = w) :
    Function.Injective ((okaMapHom u).stalkMap z).hom := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨W, hW, s, rfl⟩ := (complexSpace.{u} κ).presheaf.exists_germ_eq a
  rw [LocallyRingedSpace.stalkMap_germ_apply (okaMapHom u) W z hW s] at ha
  have hzP : z ∈ (Opens.map (okaMapHom u).base).obj W := hW
  obtain ⟨V, hVz, iV, i0, hres⟩ := (complexSpace.{u} ι).presheaf.germ_eq z hzP hzP
    ((okaMapHom u).c.app (op W) s) 0 (ha.trans (map_zero _).symm)
  have hzero : ∀ y : V, s.toFun _ ⟨okaMapFun u y.1, (leOfHom iV) y.2⟩ = 0 := fun y ↦
    congrArg (fun t : OkaRing V ↦ t.toFun _ y) hres
  have hWmem : ∀ᶠ w in 𝓝 (okaMapFun u z), w ∈ W := W.isOpen.mem_nhds hW
  have hVmem : ∀ᶠ w in 𝓝 (okaMapFun u z), σ w ∈ V :=
    hcont (by rw [hσz]; exact V.isOpen.mem_nhds hVz)
  have hev : ∀ᶠ w in 𝓝 (okaMapFun u z), σ w ∈ V ∧ okaMapFun u (σ w) = w ∧ w ∈ W :=
    hVmem.and (hright.and hWmem)
  obtain ⟨t, hts, htopen, ht0⟩ := mem_nhds_iff.mp hev
  set W' : Opens (κ → ℂ) := ⟨t, htopen⟩ with hW'def
  have hWle : W' ≤ W := fun w hw ↦ (hts hw).2.2
  have hres' : OkaRing.restrict hWle s = 0 := by
    refine OkaRing.ext (funext fun w ↦ ?_)
    obtain ⟨hσV, hFσ, _⟩ := hts w.2
    change s.toFun _ ⟨w.1, hWle w.2⟩ = 0
    rw [← hzero ⟨σ w.1, hσV⟩]
    exact congrArg (fun q : W ↦ s.toFun _ q) (Subtype.ext hFσ.symm)
  have hzW' : (okaMapHom u).base z ∈ W' := ht0
  rw [← TopCat.Presheaf.germ_res_apply (complexSpace.{u} κ).presheaf (homOfLE hWle)
    ((okaMapHom u).base z) hzW' s]
  change (complexSpace.{u} κ).presheaf.germ W' _ hzW' (OkaRing.restrict hWle s) = 0
  rw [hres']
  exact map_zero _

omit [DecidableEq ι] [DecidableEq κ] in
/-- **Precomposition with a map admitting an analytic left inverse is surjective on germs.**

A germ at `z` is represented by a holomorphic `t` on some `V ∋ z`; its preimage is the germ of
`t ∘ σ`, which is holomorphic on any open neighbourhood of `okaMapFun u z` where `σ` is analytic
and lands in `V` (`OkaAnalytic.comp_analyticOn`). That it *is* a preimage is the
left-inverse hypothesis, used on the neighbourhood of `z` where it holds. -/
theorem surjective_stalkMap_okaMapHom (hσ : AnalyticAt ℂ σ (okaMapFun u z))
    (hσz : σ (okaMapFun u z) = z) (hleft : ∀ᶠ y in 𝓝 z, σ (okaMapFun u y) = y) :
    Function.Surjective ((okaMapHom u).stalkMap z).hom := by
  intro b
  obtain ⟨V, hVz, t, rfl⟩ := (complexSpace.{u} ι).presheaf.exists_germ_eq b
  have hev : ∀ᶠ w in 𝓝 (okaMapFun u z), AnalyticAt ℂ σ w ∧ σ w ∈ V :=
    hσ.eventually_analyticAt.and (hσ.continuousAt (by rw [hσz]; exact V.isOpen.mem_nhds hVz))
  obtain ⟨W0, hsub, hopen, hmem⟩ := mem_nhds_iff.mp hev
  set W : Opens (κ → ℂ) := ⟨W0, hopen⟩ with hWdef
  have hAn : ∀ w ∈ W, AnalyticAt ℂ σ w := fun w hw ↦ (hsub hw).1
  have hIn : ∀ w ∈ W, σ w ∈ V := fun w hw ↦ (hsub hw).2
  have hmemW : (okaMapHom u).base z ∈ W := hmem
  refine ⟨(complexSpace.{u} κ).presheaf.germ W _ hmemW
    (OkaRing.mk (fun w : W ↦ t.toFun _ ⟨σ w.1, hIn w.1 w.2⟩)
      (t.2.comp_analyticOn σ hAn hIn)), ?_⟩
  rw [LocallyRingedSpace.stalkMap_germ_apply (okaMapHom u) W z hmemW _]
  obtain ⟨O0, hOsub, hOopen, hO0⟩ := mem_nhds_iff.mp hleft
  set O : Opens (ι → ℂ) := ⟨O0, hOopen⟩ with hOdef
  have hzP : z ∈ (Opens.map (okaMapHom u).base).obj W := hmemW
  set V0 : Opens (ι → ℂ) := V ⊓ (Opens.map (okaMapHom u).base).obj W ⊓ O with hV0def
  have hzV0 : z ∈ V0 := ⟨⟨hVz, hzP⟩, hO0⟩
  have hle1 : V0 ≤ (Opens.map (okaMapHom u).base).obj W := fun y hy ↦ hy.1.2
  have hle2 : V0 ≤ V := fun y hy ↦ hy.1.1
  rw [← TopCat.Presheaf.germ_res_apply (complexSpace.{u} ι).presheaf (homOfLE hle1) z hzV0 _,
    ← TopCat.Presheaf.germ_res_apply (complexSpace.{u} ι).presheaf (homOfLE hle2) z hzV0 t]
  congr 1
  refine OkaRing.ext (funext fun y ↦ ?_)
  exact congrArg (fun q : V ↦ t.toFun _ q) (Subtype.ext (hOsub y.2.2))

omit [DecidableEq ι] [DecidableEq κ] in
/-- **A holomorphic map with an analytic local inverse at a point is an isomorphism on the stalk
there.**

`σ` is asked to be analytic at `okaMapFun u z` and to be a two-sided inverse of `okaMapFun u`
near the two points; the value `σ (okaMapFun u z) = z` is not a separate hypothesis, since it is
`hleft` at `z`.

This is the statement `ComplexAnalytic.AnalyticSpace.IsLocalIso`'s stalk field asks for, and the
first in this repository to produce an isomorphism of stalks which is neither an identity nor a
field of an `IsCutOutBy`. -/
theorem isIso_stalkMap_okaMapHom (hσ : AnalyticAt ℂ σ (okaMapFun u z))
    (hleft : ∀ᶠ y in 𝓝 z, σ (okaMapFun u y) = y)
    (hright : ∀ᶠ w in 𝓝 (okaMapFun u z), okaMapFun u (σ w) = w) :
    IsIso ((okaMapHom u).stalkMap z) :=
  (ConcreteCategory.isIso_iff_bijective _).2
    ⟨injective_stalkMap_okaMapHom hσ.continuousAt hleft.self_of_nhds hright,
      surjective_stalkMap_okaMapHom hσ hleft.self_of_nhds hleft⟩

/-- **The same, for the morphism of complex analytic spaces.**

`(AnalyticSpace.okaMap u).toLRSHom` is `okaMapHom u`, so this is the previous statement at the
spelling a caller who built the morphism with `ComplexAnalytic.AnalyticSpace.okaMap` holds. -/
theorem AnalyticSpace.isIso_stalkMap_okaMap {n m : ℕ}
    {v : ULift.{u} (Fin m) → OkaRing (⊤ : TopologicalSpace.Opens (ULift.{u} (Fin n) → ℂ))}
    {y : ULift.{u} (Fin n) → ℂ} {τ : (ULift.{u} (Fin m) → ℂ) → (ULift.{u} (Fin n) → ℂ)}
    (hτ : AnalyticAt ℂ τ (okaMapFun v y))
    (hleft : ∀ᶠ p in 𝓝 y, τ (okaMapFun v p) = p)
    (hright : ∀ᶠ q in 𝓝 (okaMapFun v y), okaMapFun v (τ q) = q) :
    IsIso ((AnalyticSpace.okaMap v).toLRSHom.stalkMap y) :=
  isIso_stalkMap_okaMapHom hτ hleft hright

end ComplexAnalytic
