/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.AlgebraicGeometry.IrreducibleChain
import Oka.AlgebraicGeometry.Morphisms.FiniteEtaleIso
import Oka.Analytification.RET.Faithful
import Oka.Analytification.RET.Graph

/-!
# Fullness of the analytification on finite étale covers, given connectedness

Assume that the analytification of a connected scheme locally of finite type over `ℂ` is
connected (`ComplexAnalytic.AnalytificationPreservesConnected`). Then the analytification functor
`FEt(X) ⥤ FEt(X^an)` is full.

The connected components of a scheme `Z` locally of finite type over `ℂ` are open, since its
irreducible components form a locally finite family. Hence, under the hypothesis, every open and
closed subset of `Z^an` is the preimage of an open and closed subset of `Z` under `π : Z^an ⟶ Z`.

Let `g : A^an ⟶ B^an` be a morphism over `X^an` of analytified finite étale covers. Its graph is
an open and closed subset of `(A ×_X B)^an` (`ComplexAnalytic.isClopen_analytificationGraph`),
so it is the preimage of an open and closed subscheme `C` of `A ×_X B`. The projection `C ⟶ A`
is finite étale and bijective on closed points, hence an isomorphism
(`AlgebraicGeometry.isIso_of_isFinite_of_etale_of_bijOn_closedPoints`), and
`A ≅ C ⟶ B` is a morphism whose analytification is `g`, as both agree on points.

## Main definitions

- `ComplexAnalytic.AnalytificationPreservesConnected`: the analytification of every connected
  scheme locally of finite type over `ℂ` is connected.

## Main results

- `AlgebraicGeometry.Scheme.isOpen_connectedComponent`: connected components of a locally
  Noetherian scheme are open.
- `ComplexAnalytic.exists_isClopen_preimage_eq`: under the hypothesis, every open and closed
  subset of `Z^an` is the preimage of an open and closed subset of `Z`.
- `ComplexAnalytic.full_analytificationFiniteEtaleOver`: under the hypothesis, the
  analytification functor `FEt(X) ⥤ FEt(X^an)` is full.
-/

open CategoryTheory Limits AlgebraicGeometry Topology

universe u

/-- **The connected components of a locally Noetherian scheme are open.** -/
theorem AlgebraicGeometry.Scheme.isOpen_connectedComponent (X : Scheme.{u})
    [IsLocallyNoetherian X] (x : X) : IsOpen (connectedComponent x) := by
  classical
  rw [isOpen_iff_mem_nhds]
  intro y hy
  rw [connectedComponent_eq hy]
  let F : irreducibleComponents X → Set X := fun Z ↦ if y ∈ (Z : Set X) then ∅ else Z
  have hF : LocallyFinite F := X.locallyFinite_irreducibleComponents.subset fun Z ↦ by
    dsimp only [F]
    split_ifs
    · exact Set.empty_subset _
    · exact subset_rfl
  have hc : IsClosed (⋃ Z, F Z) := hF.isClosed_iUnion fun Z ↦ by
    dsimp only [F]
    split_ifs
    · exact isClosed_empty
    · exact isClosed_of_mem_irreducibleComponents _ Z.2
  refine Filter.mem_of_superset (hc.isOpen_compl.mem_nhds ?_) fun w hw ↦ ?_
  · simp only [Set.mem_compl_iff, Set.mem_iUnion, not_exists]
    intro Z
    dsimp only [F]
    split_ifs with h
    · exact Set.notMem_empty y
    · exact h
  · have hwy : y ∈ irreducibleComponent w := by
      by_contra h
      refine hw (Set.mem_iUnion.2 ⟨⟨_, irreducibleComponent_mem_irreducibleComponents w⟩, ?_⟩)
      dsimp only [F]
      rw [if_neg h]
      exact mem_irreducibleComponent
    exact isIrreducible_irreducibleComponent.isConnected.isPreconnected.subset_connectedComponent
      hwy mem_irreducibleComponent

namespace ComplexAnalytic

open AnalyticSpace SchemeLFTℂ

/-- **The analytification preserves connectedness**: the analytification of every connected
scheme locally of finite type over `ℂ` is connected. -/
def AnalytificationPreservesConnected : Prop :=
  ∀ Y : SchemeLFTℂ.{u}, ConnectedSpace Y.obj.left → ConnectedSpace (analytification.obj Y)

/-- A scheme locally of finite type over `ℂ` is locally Noetherian. -/
instance SchemeLFTℂ.isLocallyNoetherian (Z : SchemeLFTℂ.{u}) : IsLocallyNoetherian Z.obj.left :=
  haveI : LocallyOfFiniteType Z.obj.hom := Z.property
  LocallyOfFiniteType.isLocallyNoetherian Z.obj.hom

/-- Under `ComplexAnalytic.AnalytificationPreservesConnected`, the preimage in `Z^an` of a
connected component of `Z` is preconnected. -/
theorem isPreconnected_preimage_connectedComponent (h : AnalytificationPreservesConnected.{u})
    (Z : SchemeLFTℂ.{u}) (z : Z.obj.left) :
    IsPreconnected ((analytificationπ Z).left.base ⁻¹' connectedComponent z) := by
  let U : Z.obj.left.Opens := ⟨connectedComponent z, Z.obj.left.isOpen_connectedComponent z⟩
  haveI : ConnectedSpace (Z.restrict U).obj.left :=
    Subtype.connectedSpace isConnected_connectedComponent
  haveI := h _ this
  have hr := range_analytification_map_restrictι Z U
  change _ = (analytificationπ Z).left.base ⁻¹' connectedComponent z at hr
  rw [← hr]
  exact (isConnected_range (analytification.map (Z.restrictι U)).toLRSHom.base.hom.continuous
    ).isPreconnected

/-- **Clopen subsets of `Z^an` come from clopen subsets of `Z`**, if the analytification
preserves connectedness. -/
theorem exists_isClopen_preimage_eq (h : AnalytificationPreservesConnected.{u})
    (Z : SchemeLFTℂ.{u}) {W : Set (analytification.obj Z)} (hW : IsClopen W) :
    ∃ C : Set Z.obj.left, IsClopen C ∧ (analytificationπ Z).left.base ⁻¹' C = W := by
  let π : analytification.obj Z → Z.obj.left := (analytificationπ Z).left.base
  let C : Set Z.obj.left := {z | π ⁻¹' connectedComponent z ⊆ W}
  have hC (z : Z.obj.left) (y : Z.obj.left) (hy : y ∈ connectedComponent z) :
      y ∈ C ↔ z ∈ C := by
    change π ⁻¹' connectedComponent y ⊆ W ↔ π ⁻¹' connectedComponent z ⊆ W
    rw [connectedComponent_eq hy]
  refine ⟨C, ⟨?_, ?_⟩, ?_⟩
  · rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    exact fun z hz ↦ ⟨connectedComponent z, fun y hy ↦ (hC z y hy).not.2 hz,
      Z.obj.left.isOpen_connectedComponent z, mem_connectedComponent⟩
  · rw [isOpen_iff_forall_mem_open]
    exact fun z hz ↦ ⟨connectedComponent z, fun y hy ↦ (hC z y hy).2 hz,
      Z.obj.left.isOpen_connectedComponent z, mem_connectedComponent⟩
  · ext w
    refine ⟨fun hw ↦ hw (mem_connectedComponent (x := π w)), fun hw ↦ ?_⟩
    exact (isPreconnected_preimage_connectedComponent h Z (π w)).subset_isClopen hW
      ⟨w, mem_connectedComponent, hw⟩

/-- **Morphisms between analytified finite étale covers are algebraic**, if the analytification
preserves connectedness: for `a : A ⟶ X` and `b : B ⟶ X` finite étale, every morphism
`g : A^an ⟶ B^an` over `X^an` is the analytification of a morphism `A ⟶ B` over `X`. -/
theorem exists_analytification_map_eq (h : AnalytificationPreservesConnected.{u})
    {X A B : SchemeLFTℂ.{u}} (a : A ⟶ X) (b : B ⟶ X) [IsFinite a.hom.left] [Etale a.hom.left]
    [IsFinite b.hom.left] [Etale b.hom.left] (g : analytification.obj A ⟶ analytification.obj B)
    (hg : g ≫ analytification.map b = analytification.map a) :
    ∃ φ : A ⟶ B, φ ≫ b = a ∧ analytification.map φ = g := by
  let π : analytification.obj (fibreProd a b) → (fibreProd a b).obj.left :=
    (analytificationπ (fibreProd a b)).left.base
  obtain ⟨C, hC, hCW⟩ :=
    exists_isClopen_preimage_eq h (fibreProd a b) (isClopen_analytificationGraph g hg)
  replace hCW : π ⁻¹' C = analytificationGraph g a b := hCW
  let U : (pullback a.hom.left b.hom.left).Opens := ⟨C, hC.isOpen⟩
  haveI : IsClosedImmersion U.ι :=
    IsClosedImmersion.of_isPreimmersion _ (by rw [Scheme.Opens.range_ι]; exact hC.isClosed)
  let e : (U : Scheme.{u}) ⟶ A.obj.left := U.ι ≫ pullback.fst a.hom.left b.hom.left
  haveI : IsFinite e := inferInstanceAs (IsFinite (U.ι ≫ pullback.fst a.hom.left b.hom.left))
  haveI : Etale e := inferInstanceAs (Etale (U.ι ≫ pullback.fst a.hom.left b.hom.left))
  -- the closed points of `C` are the images of the points of the graph
  have hgr (x : (U : Scheme.{u})) (hx : IsClosed {x}) :
      ∃ z, π z = U.ι.base x ∧ z ∈ analytificationGraph g a b := by
    have hcl : IsClosed {U.ι.base x} := by
      have := U.ι.isClosedEmbedding.isClosedMap _ hx
      rwa [Set.image_singleton] at this
    obtain ⟨z, hz⟩ : ∃ z, π z = U.ι.base x :=
      (mem_range_analytificationπ_base_iff (fibreProd a b) _).2 hcl
    refine ⟨z, hz, ?_⟩
    rw [← hCW, Set.mem_preimage, hz]
    exact x.2
  -- every point of `A^an` comes from a closed point of `C` over it
  have key (y : analytification.obj A) : ∃ x : (U : Scheme.{u}), IsClosed {x} ∧
      e.base x = (analytificationπ A).left.base y ∧
      (pullback.snd a.hom.left b.hom.left).base (U.ι.base x) =
        (analytificationπ B).left.base (g.toLRSHom.base y) := by
    obtain ⟨z, hz, rfl⟩ := exists_mem_analytificationGraph g hg y
    have hzC : π z ∈ C := by
      rw [← Set.mem_preimage, hCW]
      exact hz
    have hcl : IsClosed {π z} :=
      (mem_range_analytificationπ_base_iff (fibreProd a b) _).1 ⟨z, rfl⟩
    obtain ⟨x, hx⟩ : π z ∈ Set.range U.ι.base := by
      rw [Scheme.Opens.range_ι]
      exact hzC
    refine ⟨x, ?_, ?_, ?_⟩
    · have hpre : U.ι.base ⁻¹' {π z} = {x} := by
        ext x'
        change U.ι.base x' = π z ↔ x' = x
        rw [← hx]
        exact U.ι.isOpenEmbedding.injective.eq_iff
      exact (congrArg IsClosed hpre).mp (hcl.preimage U.ι.continuous)
    · change (pullback.fst a.hom.left b.hom.left).base (U.ι.base x) = _
      rw [hx]
      exact (analytificationπ_base_map_apply (fibreProdFst a b) z).symm
    · rw [hx]
      refine (analytificationπ_base_map_apply (fibreProdSnd a b) z).symm.trans ?_
      exact congrArg (analytificationπ B).left.base hz.symm
  haveI : LocallyOfFiniteType A.obj.hom := A.property
  haveI : IsIso e := by
    refine isIso_of_isFinite_of_etale_of_bijOn_closedPoints e A.obj.hom (K := ULift.{u} ℂ)
      (fun x x' hx hx' hxx' ↦ ?_) (fun y hy ↦ ?_)
    · obtain ⟨z, hz, hzW⟩ := hgr x hx
      obtain ⟨z', hz', hzW'⟩ := hgr x' hx'
      refine U.ι.isOpenEmbedding.injective ?_
      rw [← hz, ← hz']
      refine congrArg π (eq_of_mem_analytificationGraph g hzW hzW'
        (analytificationπ_base_injective A ?_))
      rw [analytificationπ_base_map_apply, analytificationπ_base_map_apply]
      change (pullback.fst a.hom.left b.hom.left).base (π z) =
        (pullback.fst a.hom.left b.hom.left).base (π z')
      rw [hz, hz']
      exact hxx'
    · obtain ⟨y', rfl⟩ := (mem_range_analytificationπ_base_iff A y).2 hy
      obtain ⟨x, -, hx, -⟩ := key y'
      exact ⟨x, hx⟩
  let φs : A.obj.left ⟶ B.obj.left := inv e ≫ U.ι ≫ pullback.snd a.hom.left b.hom.left
  have heφ : e ≫ φs = U.ι ≫ pullback.snd a.hom.left b.hom.left := IsIso.hom_inv_id_assoc _ _
  have hφa : φs ≫ b.hom.left = a.hom.left := by
    rw [← cancel_epi e, reassoc_of% heφ]
    exact congrArg (U.ι ≫ ·) pullback.condition.symm
  have hφ : φs ≫ B.obj.hom = A.obj.hom := by
    rw [← Over.w b.hom, reassoc_of% hφa, Over.w a.hom]
  let φ : A ⟶ B := ObjectProperty.homMk (Over.homMk φs hφ)
  have hφb : φ ≫ b = a := by
    ext1
    exact Over.OverMorphism.ext hφa
  refine ⟨φ, hφb, ?_⟩
  let A' : AnalyticSpace.FiniteEtaleOver (analytification.obj X) :=
    MorphismProperty.Over.mk ⊤ _
      (isFiniteEtale_analytification_map a ⟨inferInstance, inferInstance⟩)
  let B' : AnalyticSpace.FiniteEtaleOver (analytification.obj X) :=
    MorphismProperty.Over.mk ⊤ _
      (isFiniteEtale_analytification_map b ⟨inferInstance, inferInstance⟩)
  have := AnalyticSpace.FiniteEtaleOver.hom_ext_of_base_eq (A := A') (B := B')
    (MorphismProperty.Over.homMk (analytification.map φ)
      (show analytification.map φ ≫ analytification.map b = analytification.map a by
        rw [← Functor.map_comp, hφb]))
    (MorphismProperty.Over.homMk g hg) ?_
  · exact congrArg (fun f ↦ f.left) this
  · funext y
    change (analytification.map φ).toLRSHom.base y = g.toLRSHom.base y
    obtain ⟨x, -, hx, hx'⟩ := key y
    refine analytificationπ_base_injective B ?_
    rw [analytificationπ_base_map_apply, ← hx', ← hx]
    change (e ≫ φs).base x = _
    rw [heφ]
    rfl

/-- **The analytification functor `FEt(X) ⥤ FEt(X^an)` is full**, if the analytification
preserves connectedness. -/
theorem full_analytificationFiniteEtaleOver (h : AnalytificationPreservesConnected.{u})
    (X : SchemeLFTℂ.{u}) : (analytificationFiniteEtaleOver X).Full where
  map_surjective {A B} g := by
    let a : A.left ⟶ X := A.hom
    let b : B.left ⟶ X := B.hom
    haveI : IsFinite a.hom.left := A.prop.1
    haveI : Etale a.hom.left := A.prop.2
    haveI : IsFinite b.hom.left := B.prop.1
    haveI : Etale b.hom.left := B.prop.2
    obtain ⟨φ, hφ, hφg⟩ := exists_analytification_map_eq h a b g.left (MorphismProperty.Over.w g)
    exact ⟨MorphismProperty.Over.homMk φ hφ, MorphismProperty.Over.Hom.ext hφg⟩

end ComplexAnalytic
