/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# Closures of graphs

For morphisms `sY : Y ⟶ S`, `sP : P ⟶ S`, an open `U ⊆ Y` and `g : U ⟶ P` over `S`, the graph
`U ⟶ Y ×_S P` is an immersion (`AlgebraicGeometry.graphMap`). If `U ⟶ Y` is quasi-compact and
`P` is separated over `S`, the first projection from the scheme-theoretic image `Γ̄` of the graph
restricts to an isomorphism over `U` when `Y` is reduced
(`AlgebraicGeometry.isIso_graphClosureFst_restrict`).

We also record two criteria used in the proof of Chow's lemma:

- `AlgebraicGeometry.isClosedImmersion_morphismRestrict_of_graph`: let `c : X ⟶ Y ×_S P` be a
  closed immersion with projections `π`, `q`, let `V ⊆ P` be open, `t : T ⟶ V` a closed
  immersion and `ρ : T ⟶ Y` over `S`. If `q` and `π` factor over `q⁻¹ V` as `t ∘ u` and `ρ ∘ u`,
  then `q⁻¹ V ⟶ V` is a closed immersion.
- `AlgebraicGeometry.isClosedImmersion_of_isClosed_range_of_cover`: a morphism with closed
  range which is a closed immersion over each member of a family of opens covering its range is
  a closed immersion.
-/

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

/-- A dominant morphism into a reduced scheme is injective on global sections. -/
lemma appTop_injective_of_isDominant {X Y : Scheme.{u}} [IsReduced Y] (f : X ⟶ Y)
    [IsDominant f] : Function.Injective f.appTop := by
  rw [injective_iff_map_eq_zero]
  intro s hs
  apply eq_zero_of_basicOpen_eq_bot
  have h : f ⁻¹ᵁ Y.basicOpen s = ⊥ := by
    rw [Scheme.preimage_basicOpen_top, hs, Scheme.basicOpen_zero]
  by_contra hne
  obtain ⟨y, hy⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty _).1 hne
  obtain ⟨x, hx⟩ := f.denseRange.exists_mem_open (Y.basicOpen s).isOpen ⟨y, hy⟩
  have : x ∈ f ⁻¹ᵁ Y.basicOpen s := hx
  rw [h] at this
  exact this

variable {X Y P S : Scheme.{u}} {sY : Y ⟶ S} {sP : P ⟶ S}

/-- Let `c : X ⟶ Y ×_S P` be a closed immersion, `V ⊆ P` open, `t : T ⟶ V` a closed immersion
and `ρ : T ⟶ Y` over `S`. If on `q⁻¹ V` (`q = c ≫ snd`) the projections to `V` and `Y` factor
as `u ≫ t` and `u ≫ ρ`, then `q⁻¹ V ⟶ V` is a closed immersion. -/
theorem isClosedImmersion_morphismRestrict_of_graph (c : X ⟶ pullback sY sP)
    [IsClosedImmersion c] (V : P.Opens) {T : Scheme.{u}} (t : T ⟶ V) [IsClosedImmersion t]
    (ρ : T ⟶ Y) (hρ : ρ ≫ sY = t ≫ V.ι ≫ sP)
    (u : ((c ≫ pullback.snd sY sP) ⁻¹ᵁ V).toScheme ⟶ T)
    (hu₁ : u ≫ t = (c ≫ pullback.snd sY sP) ∣_ V)
    (hu₂ : u ≫ ρ = Scheme.Opens.ι _ ≫ c ≫ pullback.fst sY sP) :
    IsClosedImmersion ((c ≫ pullback.snd sY sP) ∣_ V) := by
  rw [← hu₁]
  suffices IsClosedImmersion u from inferInstance
  let O : (pullback sY sP).Opens := pullback.snd sY sP ⁻¹ᵁ V
  let γ : T ⟶ pullback sY sP := pullback.lift ρ (t ≫ V.ι) (by rw [hρ, Category.assoc])
  have hγ : Set.range γ ⊆ (O : Set _) := by
    rintro _ ⟨x, rfl⟩
    change pullback.snd sY sP (γ x) ∈ V
    rw [← Scheme.Hom.comp_apply, pullback.lift_snd, Scheme.Hom.comp_apply]
    exact (t x).2
  let γ' : T ⟶ O := IsOpenImmersion.lift O.ι γ (by simpa using hγ)
  have hγ' : γ' ≫ O.ι = γ := IsOpenImmersion.lift_fac _ _ _
  have : Mono γ := by
    have : Mono (γ ≫ pullback.snd sY sP) := by rw [pullback.lift_snd]; infer_instance
    exact mono_of_mono γ (pullback.snd sY sP)
  have : Mono γ' := by
    have : Mono (γ' ≫ O.ι) := by rw [hγ']; infer_instance
    exact mono_of_mono γ' O.ι
  have key : u ≫ γ' = (X.isoOfEq (by rfl : c ⁻¹ᵁ O = _)).inv ≫ (c ∣_ O) := by
    rw [← cancel_mono O.ι, Category.assoc, hγ', Category.assoc, morphismRestrict_ι]
    apply pullback.hom_ext
    · simp only [γ, Category.assoc, pullback.lift_fst, hu₂, Scheme.isoOfEq_inv_ι_assoc]
    · simp only [γ, Category.assoc, pullback.lift_snd, reassoc_of% hu₁, morphismRestrict_ι,
        Scheme.isoOfEq_inv_ι_assoc]
  have : IsClosedImmersion (u ≫ γ') := key ▸ inferInstance
  exact IsClosedImmersion.of_comp u γ'

/-- A morphism with closed range is a closed immersion if it is one over each member of a family
of opens covering its range. -/
theorem isClosedImmersion_of_isClosed_range_of_cover {X P : Scheme.{u}} (q : X ⟶ P)
    (hq : IsClosed (Set.range q)) {α : Type*} (V : α → P.Opens)
    (hV : ∀ x, ∃ a, q x ∈ V a) (h : ∀ a, IsClosedImmersion (q ∣_ V a)) :
    IsClosedImmersion q := by
  let O : P.Opens := ⟨(Set.range q)ᶜ, hq.isOpen_compl⟩
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (fun o : Option α ↦ o.elim O V) ?_ ?_
  · rw [eq_top_iff]
    intro p _
    by_cases hp : p ∈ Set.range q
    · obtain ⟨x, rfl⟩ := hp
      obtain ⟨a, ha⟩ := hV x
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨some a, ha⟩
    · exact TopologicalSpace.Opens.mem_iSup.2 ⟨none, hp⟩
  · rintro (_ | a)
    · have : IsEmpty (q ⁻¹ᵁ O) := ⟨fun ⟨x, hx⟩ ↦ hx ⟨x, rfl⟩⟩
      change IsClosedImmersion (q ∣_ O)
      infer_instance
    · exact h a

/-- The scheme-theoretic image of a quasi-compact morphism from a reduced scheme is reduced. -/
lemma isReduced_image {X Z : Scheme.{u}} (f : X ⟶ Z) [QuasiCompact f] [IsReduced X] :
    IsReduced f.image := by
  let W : Z.affineOpens → f.image.Opens := fun V ↦ f.imageι ⁻¹ᵁ V.1
  have hW : TopologicalSpace.IsOpenCover W := by
    rw [TopologicalSpace.IsOpenCover, eq_top_iff]
    intro x _
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
      Z.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f.imageι x)) isOpen_univ
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨V, hV⟩, hxV⟩
  have (V : Z.affineOpens) : IsReduced (W V).toScheme := by
    have : IsAffine (W V).toScheme := V.2.preimage f.imageι
    have : _root_.IsReduced Γ((W V).toScheme, ⊤) :=
      isReduced_of_injective ((W V).topIso.hom ≫ f.toImage.app (W V)).hom
        ((f.toImage_app_injective V).comp
          (ConcreteCategory.bijective_of_isIso (W V).topIso.hom).1)
    exact isReduced_of_isAffine_isReduced _
  exact @IsReduced.of_openCover _ (f.image.openCoverOfIsOpenCover W hW) this

section graph

variable {Y P S : Scheme.{u}} (sY : Y ⟶ S) (sP : P ⟶ S) (U : Y.Opens) (g : U.toScheme ⟶ P)
  (hg : g ≫ sP = U.ι ≫ sY)

/-- The graph `U ⟶ Y ×_S P` of a morphism `g : U ⟶ P` over `S` defined on an open `U ⊆ Y`. -/
noncomputable def graphMap : U.toScheme ⟶ pullback sY sP := pullback.lift U.ι g hg.symm

@[reassoc (attr := simp)]
lemma graphMap_fst : graphMap sY sP U g hg ≫ pullback.fst sY sP = U.ι := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma graphMap_snd : graphMap sY sP U g hg ≫ pullback.snd sY sP = g := pullback.lift_snd _ _ _

instance : IsImmersion (graphMap sY sP U g hg) := by
  have : IsImmersion (graphMap sY sP U g hg ≫ pullback.fst sY sP) := by
    rw [graphMap_fst]; infer_instance
  exact IsImmersion.of_comp _ (pullback.fst sY sP)

/-- The graph of `g` is quasi-compact if `U ⟶ Y` is. -/
lemma quasiCompact_graphMap [QuasiCompact U.ι] [QuasiSeparated sP] :
    QuasiCompact (graphMap sY sP U g hg) := by
  have : QuasiCompact (graphMap sY sP U g hg ≫ pullback.fst sY sP) := by
    rw [graphMap_fst]; infer_instance
  exact QuasiCompact.of_comp _ (pullback.fst sY sP)

variable [QuasiCompact U.ι] [IsSeparated sP]

/-- The projection `Γ̄ ⟶ Y` from the scheme-theoretic image of the graph. -/
noncomputable abbrev graphClosureFst : (graphMap sY sP U g hg).image ⟶ Y :=
  (graphMap sY sP U g hg).imageι ≫ pullback.fst sY sP

/-- The projection `Γ̄ ⟶ P` from the scheme-theoretic image of the graph. -/
noncomputable abbrev graphClosureSnd : (graphMap sY sP U g hg).image ⟶ P :=
  (graphMap sY sP U g hg).imageι ≫ pullback.snd sY sP

include hg in
/-- The scheme-theoretic image of the graph is reduced if `Y` is. -/
lemma isReduced_graphClosure [IsReduced Y] : IsReduced (graphMap sY sP U g hg).image :=
  have := quasiCompact_graphMap sY sP U g hg
  isReduced_image _

/-- **The closure of the graph is isomorphic to `U` over `U`.** -/
lemma isIso_graphClosureFst_restrict [IsReduced Y] :
    IsIso (graphClosureFst sY sP U g hg ∣_ U) := by
  have := quasiCompact_graphMap sY sP U g hg
  have := isReduced_graphClosure sY sP U g hg
  set Γ := graphMap sY sP U g hg
  set π := graphClosureFst sY sP U g hg
  let V := π ⁻¹ᵁ U
  have hπ : Γ.toImage ≫ π = U.ι := by simp [π, Γ]
  have hq : Γ.toImage ≫ graphClosureSnd sY sP U g hg = g := by simp [Γ]
  have hrange : Set.range Γ.toImage ⊆ (V : Set _) := by
    rintro _ ⟨x, rfl⟩
    change π (Γ.toImage x) ∈ U
    rw [← Scheme.Hom.comp_apply, hπ]
    exact x.2
  let ι' : U.toScheme ⟶ V := IsOpenImmersion.lift V.ι Γ.toImage (by simpa using hrange)
  have hι' : ι' ≫ V.ι = Γ.toImage := IsOpenImmersion.lift_fac _ _ _
  have : IsDominant ι' := by
    have : IsDominant (ι' ≫ V.ι) := by rw [hι']; infer_instance
    exact IsDominant.of_comp_of_isOpenImmersion ι' V.ι
  have h₂ : ι' ≫ π ∣_ U = 𝟙 _ := by
    rw [← cancel_mono U.ι, Category.assoc, morphismRestrict_ι, reassoc_of% hι', hπ,
      Category.id_comp]
  refine ⟨ι', ?_, h₂⟩
  rw [← cancel_mono (V.ι ≫ Γ.imageι), Category.assoc, reassoc_of% hι', Γ.toImage_imageι,
    Category.id_comp]
  apply pullback.hom_ext
  · simp only [Category.assoc, graphMap_fst, Γ]
    exact morphismRestrict_ι π U
  · simp only [Category.assoc, graphMap_snd, Γ]
    refine ext_of_isDominant_of_isSeparated sP ?_ ι' ?_
    · simp only [Category.assoc, hg]
      rw [← Category.assoc, morphismRestrict_ι, Category.assoc, Category.assoc,
        pullback.condition]
    · simp only [reassoc_of% h₂, reassoc_of% hι']
      exact hq.symm

end graph

/-- The scheme-theoretic image of a quasi-compact morphism from an irreducible scheme is
irreducible. -/
lemma irreducibleSpace_image {X Z : Scheme.{u}} (f : X ⟶ Z) [QuasiCompact f]
    [IrreducibleSpace X] : IrreducibleSpace f.image := by
  refine (irreducibleSpace_def _).2 ?_
  have h := (IrreducibleSpace.isIrreducible_univ X).image f.toImage
    f.toImage.continuous.continuousOn
  rw [Set.image_univ] at h
  simpa [f.toImage.denseRange.closure_range] using h.closure

end AlgebraicGeometry
