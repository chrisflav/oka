/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.AnalyticSpace.CoveringSpaceMap
import Oka.AnalyticSpace.FiniteEtaleOver

/-!
# Finite étale covers are determined by their underlying topological covers

A finite étale cover of a complex analytic space `S` is isomorphic to the covering space built on
its underlying map (`ComplexAnalytic.AnalyticSpace.coveringSpaceIso`). Consequently two finite
étale covers of `S` whose total spaces are homeomorphic over `S` are isomorphic as objects of
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver S`.

Along a morphism `g : S' ⟶ S` which is a homeomorphism on underlying spaces, a finite étale cover
`p : W → S` is transported to the finite étale cover `g⁻¹ ∘ p : W → S'` of `S'`.

## Main definitions and results

- `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isoOfHomeomorph`: a homeomorphism of total
  spaces over `S` induces an isomorphism of finite étale covers.
- `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.transport`: the transport of a finite étale
  cover along a morphism which is a homeomorphism on underlying spaces.
- `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.nonempty_iso_of_iso_transport`: a finite étale
  cover `A` of `S` is isomorphic to `W` if a cover of `S'` isomorphic to the transport of `W`
  maps homeomorphically to `A` over `g`.
-/

open CategoryTheory AlgebraicGeometry

universe u

namespace ComplexAnalytic.AnalyticSpace

noncomputable section

variable {S : AnalyticSpace.{u}}

/-- The underlying map of a morphism of analytic spaces which is an isomorphism is a
homeomorphism. -/
lemma isHomeomorph_base_of_isIso {X Y : AnalyticSpace.{u}} (f : X ⟶ Y) [IsIso f] :
    IsHomeomorph (f.toLRSHom.base : X → Y) :=
  (LocallyRingedSpace.homeoOfIso (asIso (forgetToLocallyRingedSpace.map f))).isHomeomorph

/-- The underlying map of the left component of an isomorphism of finite étale covers is a
homeomorphism. -/
lemma FiniteEtaleOver.isHomeomorph_base_hom_left {A B : FiniteEtaleOver S} (e : A ≅ B) :
    IsHomeomorph (e.hom.left.toLRSHom.base : A.left → B.left) := by
  have : IsIso e.hom.left :=
    ((MorphismProperty.Over.forget _ _ _ ⋙ CategoryTheory.Over.forget _).mapIso e).isIso_hom
  exact isHomeomorph_base_of_isIso _

/-- **A homeomorphism of total spaces over `S` induces an isomorphism of finite étale covers.** -/
def FiniteEtaleOver.isoOfHomeomorph (A B : FiniteEtaleOver S) (h : A.left ≃ₜ B.left)
    (hh : ∀ a, B.hom.toLRSHom.base (h a) = A.hom.toLRSHom.base a) : A ≅ B := by
  haveI : IsLocalIso A.hom := A.prop.isLocalIso
  haveI : IsLocalIso B.hom := B.prop.isLocalIso
  let pA := A.hom.toLRSHom.base
  let pB := B.hom.toLRSHom.base
  let hA := IsLocalIso.isLocalHomeomorph (f := A.hom)
  let hB := IsLocalIso.isLocalHomeomorph (f := B.hom)
  let f : A.left.toLocallyRingedSpace.toTopCat ⟶ B.left.toLocallyRingedSpace.toTopCat :=
    TopCat.ofHom ⟨h, h.continuous⟩
  let g : B.left.toLocallyRingedSpace.toTopCat ⟶ A.left.toLocallyRingedSpace.toTopCat :=
    TopCat.ofHom ⟨h.symm, h.symm.continuous⟩
  have hf : pA = f ≫ pB := by
    ext a
    exact (hh a).symm
  have hg : pB = g ≫ pA := by
    ext b
    change pB b = pA (h.symm b)
    rw [← hh, h.apply_symm_apply]
  let φ := coveringSpaceMap S pB hB pA hA f hf
  let ψ := coveringSpaceMap S pA hA pB hB g hg
  let e : coveringSpace S pA hA ≅ coveringSpace S pB hB :=
    { hom := φ
      inv := ψ
      hom_inv_id := by
        refine coveringSpace_hom_ext S pA hA ?_ ?_
        · change φ.toLRSHom.base ≫ ψ.toLRSHom.base = 𝟙 _
          rw [base_coveringSpaceMap, base_coveringSpaceMap]
          ext a
          exact h.symm_apply_apply a
        · simp only [Category.assoc, ψ, φ, coveringSpaceMap_comp, Category.id_comp]
      inv_hom_id := by
        refine coveringSpace_hom_ext S pB hB ?_ ?_
        · change ψ.toLRSHom.base ≫ φ.toLRSHom.base = 𝟙 _
          rw [base_coveringSpaceMap, base_coveringSpaceMap]
          ext b
          exact h.apply_symm_apply b
        · simp only [Category.assoc, ψ, φ, coveringSpaceMap_comp, Category.id_comp] }
  refine MorphismProperty.Over.isoMk (coveringSpaceIso A.hom ≪≫ e ≪≫
    (coveringSpaceIso B.hom).symm) ?_
  have hB' : (coveringSpaceIso B.hom).inv ≫ B.hom = coveringSpaceHom S pB hB := by
    rw [Iso.inv_comp_eq]
    exact (toCoveringSpace_comp B.hom).symm
  change (coveringSpaceIso A.hom).hom ≫ φ ≫ (coveringSpaceIso B.hom).inv ≫ B.hom = A.hom
  refine (congrArg ((coveringSpaceIso A.hom).hom ≫ ·) (congrArg (φ ≫ ·) hB')).trans ?_
  change (coveringSpaceIso A.hom).hom ≫ φ ≫ coveringSpaceHom S pB hB = A.hom
  exact (congrArg ((coveringSpaceIso A.hom).hom ≫ ·)
    (coveringSpaceMap_comp S pB hB pA hA f hf)).trans (toCoveringSpace_comp A.hom)

variable {S' : AnalyticSpace.{u}} (g : S' ⟶ S) (hg : IsHomeomorph (g.toLRSHom.base : S' → S))

/-- The underlying map of the transport of a cover along a homeomorphism. -/
def FiniteEtaleOver.transportMap (W : FiniteEtaleOver S) :
    W.left.toLocallyRingedSpace.toTopCat ⟶ S'.toLocallyRingedSpace.toTopCat :=
  W.hom.toLRSHom.base ≫
    TopCat.ofHom ⟨(hg.homeomorph _).symm, (hg.homeomorph _).symm.continuous⟩

/-- The underlying map of the transport is a local homeomorphism. -/
lemma FiniteEtaleOver.isLocalHomeomorph_transportMap (W : FiniteEtaleOver S) :
    IsLocalHomeomorph (transportMap g hg W) := by
  haveI : IsLocalIso W.hom := W.prop.isLocalIso
  exact (hg.homeomorph _).symm.isLocalHomeomorph.comp IsLocalIso.isLocalHomeomorph

/-- **The transport of a finite étale cover of `S` along `g : S' ⟶ S`**, a homeomorphism on
underlying spaces: the covering space of `S'` on the composite of the cover with `g⁻¹`. -/
def FiniteEtaleOver.transport (W : FiniteEtaleOver S) : FiniteEtaleOver S' :=
  MorphismProperty.Over.mk ⊤ (coveringSpaceHom S' (transportMap g hg W)
      (isLocalHomeomorph_transportMap g hg W)) <| by
    haveI : IsFinite W.hom := W.prop.isFinite
    refine isFiniteEtale_coveringSpaceHom_of_isClosedMap _ _ _ ?_ fun x ↦ ?_
    · exact (hg.homeomorph _).symm.isClosedMap.comp IsFinite.isClosedMap
    · have : ⇑(transportMap g hg W) ⁻¹' {x} = W.hom.toLRSHom.base ⁻¹' {g.toLRSHom.base x} := by
        ext w
        change (hg.homeomorph _).symm _ = x ↔ _
        rw [Homeomorph.symm_apply_eq]
        rfl
      rw [this]
      exact @Set.toFinite _ _ (IsFinite.finite_fiber _)

/-- The transport of `W` composed with `g` is the structure map of `W`, on points. -/
lemma FiniteEtaleOver.transport_hom_base_apply (W : FiniteEtaleOver S) (w : W.left) :
    g.toLRSHom.base ((transport g hg W).hom.toLRSHom.base w) = W.hom.toLRSHom.base w :=
  (hg.homeomorph _).apply_symm_apply _

/-- **Recognising a cover from its transport.** Let `g : S' ⟶ S` be a homeomorphism on underlying
spaces, `W` and `A` finite étale covers of `S` and `V` a finite étale cover of `S'` isomorphic to
the transport of `W`. If `k : V ⟶ A` is a morphism over `g` which is a homeomorphism on
underlying spaces, then `A ≅ W`. -/
theorem FiniteEtaleOver.nonempty_iso_of_iso_transport {W A : FiniteEtaleOver S}
    {V : FiniteEtaleOver S'} (e : V ≅ transport g hg W) (k : V.left ⟶ A.left)
    (hk : IsHomeomorph (k.toLRSHom.base : V.left → A.left)) (w : k ≫ A.hom = V.hom ≫ g) :
    Nonempty (A ≅ W) := by
  let h : A.left ≃ₜ W.left :=
    (hk.homeomorph _).symm.trans ((isHomeomorph_base_hom_left e).homeomorph _)
  refine ⟨isoOfHomeomorph A W h fun a ↦ ?_⟩
  obtain ⟨v, rfl⟩ := (hk.homeomorph _).surjective a
  have hv : h (hk.homeomorph _ v) = e.hom.left.toLRSHom.base v := by
    simp only [h, Homeomorph.trans_apply, Homeomorph.symm_apply_apply]
    rfl
  rw [hv, ← transport_hom_base_apply g hg W]
  have h1 : (transport g hg W).hom.toLRSHom.base (e.hom.left.toLRSHom.base v) =
      V.hom.toLRSHom.base v :=
    congrArg (fun φ ↦ φ.toLRSHom.base v) (MorphismProperty.Over.w e.hom)
  have h2 : A.hom.toLRSHom.base (k.toLRSHom.base v) = g.toLRSHom.base (V.hom.toLRSHom.base v) :=
    congrArg (fun φ ↦ φ.toLRSHom.base v) w
  rw [h1]
  exact h2.symm

end

end ComplexAnalytic.AnalyticSpace
