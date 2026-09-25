/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analysis.Complex.KummerCover
import Oka.AnalyticSpace.CoveringSpaceHomeomorph

/-!
# Finite étale covers of a product with a punctured disc

Let `S` be a complex analytic space whose underlying space is identified by a homeomorphism `h`
with `B × Δ*`, where `B` is a convex open subset of a real normed space and `Δ*` is the punctured
unit disc. For `k > 0`, the Kummer cover `ComplexAnalytic.AnalyticSpace.kummer h k` of `S` is the
covering space of `S` on the map `(b, u) ↦ (b, uᵏ)`.

Every finite étale cover of `S` with Hausdorff total space is isomorphic to a finite disjoint union
of Kummer covers (`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.exists_iso_sigma_kummer`). This
follows from the topological classification `IsCoveringMap.exists_homeomorph_sigma_kummer`, since
a finite étale cover is determined by its underlying covering map.

## Main definitions

- `ComplexAnalytic.AnalyticSpace.kummerMap h k`: the map `(b, u) ↦ (b, uᵏ)` on `S`.
- `ComplexAnalytic.AnalyticSpace.kummer h k`: the Kummer cover of degree `k` of `S`.

## Main results

- `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.exists_iso_sigma_kummer`: a finite étale cover
  of `S` with Hausdorff total space is a finite disjoint union of Kummer covers.
- `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.exists_iso_sigma_of_forall_eq_kummerMap`: the
  same, for any family of covers of `S` identified with the Kummer covers on underlying spaces.
-/

open CategoryTheory Topology

universe u

namespace ComplexAnalytic.AnalyticSpace

noncomputable section

variable {S : AnalyticSpace.{u}} {E : Type*} [NormedAddCommGroup E] {B : Set E}
  (h : (S : Type u) ≃ₜ Kummer.base B)

/-- The Kummer map `(b, u) ↦ (b, uᵏ)` on `S`, transported along `h`. -/
def kummerMap (k : ℕ+) : S.toLocallyRingedSpace.toTopCat ⟶ S.toLocallyRingedSpace.toTopCat :=
  TopCat.ofHom ⟨h.symm ∘ Kummer.cover B k ∘ h,
    h.symm.continuous.comp ((Kummer.isCoveringMap_cover B k).continuous.comp h.continuous)⟩

lemma kummerMap_apply (k : ℕ+) (s : S) : kummerMap h k s = h.symm (Kummer.cover B k (h s)) :=
  rfl

lemma isCoveringMap_kummerMap (k : ℕ+) : IsCoveringMap (kummerMap h k) :=
  ((Kummer.isCoveringMap_cover B k).comp_homeomorph h).homeomorph_comp h.symm

lemma finite_preimage_kummerMap (k : ℕ+) (s : S) : (kummerMap h k ⁻¹' {s}).Finite := by
  have : kummerMap h k ⁻¹' {s} = h ⁻¹' (Kummer.cover B k ⁻¹' {h s}) := by
    ext t
    exact h.symm_apply_eq
  rw [this]
  exact (Kummer.finite_preimage_cover B k (h s)).preimage h.injective.injOn

/-- The **Kummer cover** of degree `k` of `S`: the covering space of `S` on the map
`(b, u) ↦ (b, uᵏ)`. -/
def kummer (k : ℕ+) : FiniteEtaleOver S :=
  MorphismProperty.Over.mk ⊤
    (coveringSpaceHom S (kummerMap h k) (isCoveringMap_kummerMap h k).isLocalHomeomorph)
    (isFiniteEtale_coveringSpaceHom S _ (isCoveringMap_kummerMap h k)
      (finite_preimage_kummerMap h k))

lemma kummer_hom_base_apply (k : ℕ+) (s : (kummer h k).left) :
    (kummer h k).hom.toLRSHom.base s = h.symm (Kummer.cover B k (h s)) :=
  rfl

/-- **A finite étale cover of `B × Δ*` is a finite disjoint union of Kummer covers**, for any
family `K` of covers of `S` whose `k`-th member is identified with `S` so that its structure map
becomes the Kummer map of degree `k`. -/
theorem FiniteEtaleOver.exists_iso_sigma_of_forall_eq_kummerMap [NormedSpace ℝ E]
    (hB : Convex ℝ B) (hBo : IsOpen B) (K : ℕ+ → FiniteEtaleOver S)
    (eK : ∀ k, (K k).left ≃ₜ (S : Type u))
    (hK : ∀ k x, (K k).hom.toLRSHom.base x = kummerMap h k (eK k x))
    (W : FiniteEtaleOver S) [T2Space W.left] :
    ∃ (ι : Type u) (_ : Finite ι) (k : ι → ℕ+),
      Nonempty (W ≅ FiniteEtaleOver.sigma fun i ↦ K (k i)) := by
  haveI : IsFiniteEtale W.hom := W.prop
  haveI : T2Space ((𝟭 AnalyticSpace.{u}).obj W.left) := ‹T2Space W.left›
  set p := W.hom.toLRSHom.base
  have hp : IsCoveringMap (h ∘ p) :=
    (isCoveringMap_base_of_isFiniteEtale W.hom).homeomorph_comp h
  have hfin (y : Kummer.base B) : ((h ∘ p) ⁻¹' {y}).Finite := by
    have : (h ∘ p) ⁻¹' {y} = p ⁻¹' {h.symm y} := by
      ext w
      exact h.eq_symm_apply.symm
    rw [this]
    have := IsFinite.finite_fiber (f := W.hom) (h.symm y)
    exact Set.toFinite _
  obtain ⟨hι, k, Φ, hΦ⟩ := hp.exists_homeomorph_sigma_kummer hB hBo hfin
  let F : ZerothHomotopy W.left → AnalyticSpace.{u} := fun i ↦ (K (k i)).left
  let g : ∀ i, Kummer.base B ≃ₜ (F i : Type u) := fun i ↦ h.symm.trans (eK (k i)).symm
  let e : (Σ _ : ZerothHomotopy W.left, Kummer.base B) ≃ₜ Σ i, (F i : Type u) :=
    (Equiv.sigmaCongrRight fun i ↦ (g i).toEquiv)
      |>.toHomeomorphOfContinuousOpen
        (continuous_sigma fun i ↦ continuous_sigmaMk.comp (g i).continuous)
        (isOpenMap_sigma.2 fun i ↦ isOpenMap_sigmaMk.comp (g i).isOpenMap)
  refine ⟨_, hι, k, ⟨FiniteEtaleOver.isoOfHomeomorph W _
    (Φ.symm.trans (e.trans (sigmaHomeoSigma F).symm)) fun w ↦ ?_⟩⟩
  obtain ⟨⟨c, y⟩, rfl⟩ := Φ.surjective w
  have h₁ : (FiniteEtaleOver.sigma fun i ↦ K (k i)).hom.toLRSHom.base
      ((sigmaHomeoSigma F).symm ⟨c, g c y⟩) = (K (k c)).hom.toLRSHom.base (g c y) :=
    congrArg (fun φ ↦ φ.toLRSHom.base (g c y))
      (sigmaι_sigmaDesc (fun i ↦ (K (k i)).left) (fun i ↦ (K (k i)).hom) c)
  have h₀ : (Φ.symm.trans (e.trans (sigmaHomeoSigma F).symm)) (Φ ⟨c, y⟩) =
      (sigmaHomeoSigma F).symm ⟨c, g c y⟩ := by
    rw [Homeomorph.trans_apply, Homeomorph.symm_apply_apply]
    rfl
  refine Eq.trans (congrArg _ h₀) (h₁.trans ?_)
  rw [hK, kummerMap_apply]
  simp only [g, Homeomorph.trans_apply, Homeomorph.apply_symm_apply]
  rw [← hΦ c y, Function.comp_apply, Homeomorph.symm_apply_apply]

/-- **A finite étale cover of `B × Δ*` is a finite disjoint union of Kummer covers.** -/
theorem FiniteEtaleOver.exists_iso_sigma_kummer [NormedSpace ℝ E] (hB : Convex ℝ B)
    (hBo : IsOpen B) (W : FiniteEtaleOver S) [T2Space W.left] :
    ∃ (ι : Type u) (_ : Finite ι) (k : ι → ℕ+),
      Nonempty (W ≅ FiniteEtaleOver.sigma fun i ↦ kummer h (k i)) :=
  exists_iso_sigma_of_forall_eq_kummerMap h hB hBo (kummer h) (fun _ ↦ Homeomorph.refl _)
    (fun _ _ ↦ rfl) W

end

end ComplexAnalytic.AnalyticSpace
