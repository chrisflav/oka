/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analysis.Complex.KummerCoverPi
import Oka.Analytification.RET.ES.Kummer

/-!
# Finite étale covers of a product with a power of the punctured disc

Let `S` be a complex analytic space whose underlying space is identified by a homeomorphism `h`
with `B × (Δ*)ʳ`, where `B` is a convex open subset of a real normed space and `Δ*` is the
punctured unit disc; this is the local model of the complement of a normal crossings divisor. For
`M > 0` the Kummer cover `ComplexAnalytic.AnalyticSpace.kummerPi h M` of `S` is the covering space
of `S` on the map `(b, u) ↦ (b, u₁ᴹ, …, uᵣᴹ)`.

Every finite étale cover `W` of `S` with Hausdorff total space is a finite disjoint union of
quotients of Kummer covers (`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.exists_kummerPi`):
there are finitely many morphisms `φᵢ : kummerPi h Mᵢ ⟶ W` over `S` whose images are disjoint and
cover `W`, and the fibres of `φᵢ` are the orbits of a subgroup `Γᵢ ≤ ℤʳ` containing `Mᵢℤʳ`, acting
through the `Mᵢ`-th roots of unity.

## Main definitions

- `ComplexAnalytic.AnalyticSpace.kummerPiMap h M`: the map `(b, u) ↦ (b, uᴹ)` on `S`.
- `ComplexAnalytic.AnalyticSpace.kummerPi h M`: the Kummer cover of degree `M` of `S`.
- `ComplexAnalytic.AnalyticSpace.kummerPiHom`: the morphism of covers `kummerPi h M ⟶ W`
  induced by a continuous map over `S`.

## Main results

- `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.exists_kummerPi`: a finite étale cover of `S`
  with Hausdorff total space is a finite disjoint union of quotients of Kummer covers.
-/

open CategoryTheory Topology

universe u

namespace ComplexAnalytic.AnalyticSpace

noncomputable section

variable {S : AnalyticSpace.{u}} {E : Type*} [NormedAddCommGroup E] {B : Set E} {r : ℕ}
  (h : (S : Type u) ≃ₜ KummerPi.base B r)

/-- The Kummer map `(b, u) ↦ (b, u₁ᴹ, …, uᵣᴹ)` on `S`, transported along `h`. -/
def kummerPiMap (M : ℕ+) : S.toLocallyRingedSpace.toTopCat ⟶ S.toLocallyRingedSpace.toTopCat :=
  TopCat.ofHom ⟨h.symm ∘ KummerPi.cover B r M ∘ h,
    h.symm.continuous.comp ((KummerPi.isCoveringMap_cover M).continuous.comp h.continuous)⟩

lemma kummerPiMap_apply (M : ℕ+) (s : S) :
    kummerPiMap h M s = h.symm (KummerPi.cover B r M (h s)) :=
  rfl

lemma isCoveringMap_kummerPiMap (M : ℕ+) : IsCoveringMap (kummerPiMap h M) :=
  ((KummerPi.isCoveringMap_cover M).comp_homeomorph h).homeomorph_comp h.symm

lemma finite_preimage_kummerPiMap (M : ℕ+) (s : S) : (kummerPiMap h M ⁻¹' {s}).Finite := by
  have : kummerPiMap h M ⁻¹' {s} = h ⁻¹' (KummerPi.cover B r M ⁻¹' {h s}) := by
    ext t
    exact h.symm_apply_eq
  rw [this]
  exact (KummerPi.finite_preimage_cover M (h s)).preimage h.injective.injOn

/-- The **Kummer cover** of degree `M` of `S`: the covering space of `S` on the map
`(b, u) ↦ (b, u₁ᴹ, …, uᵣᴹ)`. -/
def kummerPi (M : ℕ+) : FiniteEtaleOver S :=
  MorphismProperty.Over.mk ⊤
    (coveringSpaceHom S (kummerPiMap h M) (isCoveringMap_kummerPiMap h M).isLocalHomeomorph)
    (isFiniteEtale_coveringSpaceHom S _ (isCoveringMap_kummerPiMap h M)
      (finite_preimage_kummerPiMap h M))

variable {h} in
/-- The morphism of covers `kummerPi h M ⟶ W` whose underlying map is a given continuous map
`f : S → W` over `S`. -/
def kummerPiHom {W : FiniteEtaleOver S} {M : ℕ+}
    (f : S.toLocallyRingedSpace.toTopCat ⟶ W.left.toLocallyRingedSpace.toTopCat)
    (hf : kummerPiMap h M = f ≫ W.hom.toLRSHom.base) : kummerPi h M ⟶ W := by
  haveI : IsLocalIso W.hom := W.prop.isLocalIso
  refine MorphismProperty.Over.homMk
    (coveringSpaceMap S W.hom.toLRSHom.base IsLocalIso.isLocalHomeomorph (kummerPiMap h M)
      (isCoveringMap_kummerPiMap h M).isLocalHomeomorph f hf ≫ (coveringSpaceIso W.hom).inv) ?_
  have hW : (coveringSpaceIso W.hom).inv ≫ W.hom =
      coveringSpaceHom S W.hom.toLRSHom.base IsLocalIso.isLocalHomeomorph := by
    rw [Iso.inv_comp_eq]
    exact (toCoveringSpace_comp W.hom).symm
  change (_ ≫ (coveringSpaceIso W.hom).inv) ≫ W.hom = _
  rw [Category.assoc, hW]
  exact coveringSpaceMap_comp S _ _ _ _ f hf

lemma kummerPiHom_left_base_apply {W : FiniteEtaleOver S} {M : ℕ+}
    (f : S.toLocallyRingedSpace.toTopCat ⟶ W.left.toLocallyRingedSpace.toTopCat)
    (hf : kummerPiMap h M = f ≫ W.hom.toLRSHom.base) (x : S) :
    (kummerPiHom f hf).left.toLRSHom.base x = f x := by
  haveI : IsLocalIso W.hom := W.prop.isLocalIso
  have hinv (z) : (coveringSpaceIso W.hom).inv.toLRSHom.base z = z :=
    congrArg (fun φ ↦ φ.toLRSHom.base z) (coveringSpaceIso W.hom).inv_hom_id
  change (coveringSpaceIso W.hom).inv.toLRSHom.base
    ((coveringSpaceMap S W.hom.toLRSHom.base _ (kummerPiMap h M) _ f hf).toLRSHom.base x) = f x
  rw [hinv, base_coveringSpaceMap]
  rfl

/-- **A finite étale cover of `B × (Δ*)ʳ` is a finite disjoint union of quotients of Kummer
covers.** For `W` with Hausdorff total space there are finitely many morphisms of covers
`φᵢ : kummerPi h Mᵢ ⟶ W` whose images are disjoint and cover `W`, and two points have the same
image under `φᵢ` if and only if they differ by the action of an element of a subgroup
`Γᵢ ≤ ℤʳ` containing `Mᵢℤʳ`, acting through `KummerPi.rot`. -/
theorem FiniteEtaleOver.exists_kummerPi [NormedSpace ℝ E] (hB : Convex ℝ B) (hBo : IsOpen B)
    (W : FiniteEtaleOver S) [T2Space W.left] :
    ∃ (ι : Type u) (_ : Finite ι) (M : ι → ℕ+) (Γ : ι → AddSubgroup (Fin r → ℤ))
      (φ : ∀ i, kummerPi h (M i) ⟶ W), (∀ i a, (M i : ℤ) • a ∈ Γ i) ∧
      (∀ w, ∃ i, ∃ x : S, (φ i).left.toLRSHom.base x = w) ∧
      (∀ i j (x y : S), (φ i).left.toLRSHom.base x = (φ j).left.toLRSHom.base y → i = j) ∧
      ∀ i (x y : S), (φ i).left.toLRSHom.base x = (φ i).left.toLRSHom.base y ↔
        ∃ a ∈ Γ i, h y = KummerPi.rot B r (M i) a (h x) := by
  haveI : IsFiniteEtale W.hom := W.prop
  haveI : T2Space ((𝟭 AnalyticSpace.{u}).obj W.left) := ‹T2Space W.left›
  set p := W.hom.toLRSHom.base
  have hp : IsCoveringMap (h ∘ p) :=
    (isCoveringMap_base_of_isFiniteEtale W.hom).homeomorph_comp h
  have hfin (y : KummerPi.base B r) : ((h ∘ p) ⁻¹' {y}).Finite := by
    have : (h ∘ p) ⁻¹' {y} = p ⁻¹' {h.symm y} := by
      ext w
      exact h.eq_symm_apply.symm
    rw [this]
    have := IsFinite.finite_fiber (f := W.hom) (h.symm y)
    exact Set.toFinite _
  obtain ⟨hι, M, Γ, Φ, hM, hcont, -, hpΦ, hsurj, hsep, hfib⟩ :=
    hp.exists_sigma_kummerPi hB hBo hfin
  let f (c : ZerothHomotopy W.left) :
      S.toLocallyRingedSpace.toTopCat ⟶ W.left.toLocallyRingedSpace.toTopCat :=
    TopCat.ofHom ⟨Φ c ∘ h, (hcont c).comp h.continuous⟩
  have hf (c : ZerothHomotopy W.left) : kummerPiMap h (M c) = f c ≫ W.hom.toLRSHom.base := by
    ext s
    change h.symm (KummerPi.cover B r (M c) (h s)) = p (Φ c (h s))
    rw [← hpΦ c (h s), Function.comp_apply, Homeomorph.symm_apply_apply]
  refine ⟨ZerothHomotopy W.left, hι, M, Γ, fun c ↦ kummerPiHom (f c) (hf c), hM,
    fun w ↦ ?_, fun i j x y hxy ↦ ?_, fun i x y ↦ ?_⟩
  · obtain ⟨c, y, rfl⟩ := hsurj w
    refine ⟨c, h.symm y, ?_⟩
    rw [kummerPiHom_left_base_apply]
    change Φ c (h (h.symm y)) = Φ c y
    rw [Homeomorph.apply_symm_apply]
  · rw [kummerPiHom_left_base_apply, kummerPiHom_left_base_apply] at hxy
    exact hsep i j _ _ hxy
  · rw [kummerPiHom_left_base_apply, kummerPiHom_left_base_apply]
    exact hfib i (h x) (h y)

end

end ComplexAnalytic.AnalyticSpace
