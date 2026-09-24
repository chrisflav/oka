/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.AlgebraicGeometry.Chow

/-!
# Chow's lemma for irreducible schemes

Let `Y` be an irreducible scheme, proper over `Spec R`. Then there is a closed immersion
`c : Y' ⟶ Y ×_R ℙ(N; R)` from an irreducible scheme `Y'` such that the second projection
`Y' ⟶ ℙ(N; R)` is a closed immersion, the first projection `π : Y' ⟶ Y` is an isomorphism over a
nonempty open `U ⊆ Y`, and `π⁻¹ U` is scheme-theoretically dense in `Y'`
(`AlgebraicGeometry.exists_chow_of_irreducibleSpace`).

The construction is the one of `AlgebraicGeometry.exists_chow`. Reducedness is replaced by the
fact that `U` is scheme-theoretically dense in the scheme-theoretic image `Y'` of the graph:
morphisms to a separated scheme agreeing on a scheme-theoretically dense open agree
(`AlgebraicGeometry.ext_of_isSchemeTheoreticallyDominant_of_isSeparated`).
-/

open CategoryTheory Limits HomogeneousLocalization MvPolynomial

universe u

namespace AlgebraicGeometry

/-- The morphism to the scheme-theoretic image of a quasi-compact morphism is
scheme-theoretically dominant. -/
instance isSchemeTheoreticallyDominant_toImage {X Z : Scheme.{u}} (f : X ⟶ Z)
    [QuasiCompact f] : IsSchemeTheoreticallyDominant f.toImage := by
  rw [isSchemeTheoreticallyDominant_iff]
  let W : Z.affineOpens → f.image.affineOpens := fun V ↦ ⟨f.imageι ⁻¹ᵁ V.1, V.2.preimage _⟩
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top W ?_ fun V ↦ ?_
  · rw [eq_top_iff]
    intro x _
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
      Z.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f.imageι x)) isOpen_univ
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨V, hV⟩, hxV⟩
  · rw [Scheme.Hom.ker_apply, Scheme.IdealSheafData.ideal_bot, Pi.bot_apply]
    exact (RingHom.injective_iff_ker_eq_bot _).1 (f.toImage_app_injective V)

/-- The restriction of a quasi-compact scheme-theoretically dominant morphism to an open of the
target is scheme-theoretically dominant. -/
instance isSchemeTheoreticallyDominant_morphismRestrict {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsSchemeTheoreticallyDominant f] [QuasiCompact f] (V : Y.Opens) :
    IsSchemeTheoreticallyDominant (f ∣_ V) :=
  .of_isPullback (isPullback_morphismRestrict f V).flip

/-- If `g ≫ V.ι` is quasi-compact and scheme-theoretically dominant, so is `g`. -/
lemma IsSchemeTheoreticallyDominant.of_comp_ι {X Y : Scheme.{u}} {V : Y.Opens}
    (g : X ⟶ V) [IsSchemeTheoreticallyDominant (g ≫ V.ι)] [QuasiCompact (g ≫ V.ι)] :
    IsSchemeTheoreticallyDominant g := by
  refine .of_isPullback (f := g ≫ V.ι) (g := V.ι) (pX := 𝟙 X) (IsPullback.flip ?_)
  refine IsOpenImmersion.isPullback g (𝟙 X) V.ι (g ≫ V.ι) (Category.id_comp _) ?_
  ext x
  exact iff_of_true ⟨g x, rfl⟩ ⟨x, rfl⟩

/-- If the source of a scheme-theoretically dominant morphism `i` factors through an open `V`,
then `V ⟶ X` is scheme-theoretically dominant. -/
lemma IsSchemeTheoreticallyDominant.ι_of_fac {W X : Scheme.{u}} {V : X.Opens} (g : W ⟶ V)
    (i : W ⟶ X) [IsSchemeTheoreticallyDominant i] (h : g ≫ V.ι = i) :
    IsSchemeTheoreticallyDominant V.ι := by
  rw [isSchemeTheoreticallyDominant_iff, eq_bot_iff, ← i.ker_eq_bot, ← h]
  exact Scheme.Hom.le_ker_comp _ _

/-- Let `f g : X ⟶ Y` agree over some separated `s : Y ⟶ Z`. Then `f = g` if `ι ≫ f = ι ≫ g`
for some scheme-theoretically dominant `ι`. -/
lemma ext_of_isSchemeTheoreticallyDominant_of_isSeparated {W X Y Z : Scheme.{u}} {f g : X ⟶ Y}
    (s : Y ⟶ Z) [IsSeparated s] (h : f ≫ s = g ≫ s)
    (ι : W ⟶ X) [IsSchemeTheoreticallyDominant ι] (hU : ι ≫ f = ι ≫ g) : f = g := by
  let X' : Over Z := Over.mk (f ≫ s)
  let Y' : Over Z := Over.mk s
  let U' : Over Z := Over.mk (ι ≫ f ≫ s)
  let f' : X' ⟶ Y' := Over.homMk f
  let g' : X' ⟶ Y' := Over.homMk g
  let ι' : U' ⟶ X' := Over.homMk ι
  have : IsSeparated Y'.hom := ‹_›
  have hι : ι' ≫ f' = ι' ≫ g' := by ext1; exact hU
  have hfac : (equalizer.lift ι' hι).left ≫ (equalizer.ι f' g').left = ι := by
    rw [← Over.comp_left, equalizer.lift_ι]
    rfl
  have : IsIso (equalizer.ι f' g').left := by
    have : IsSchemeTheoreticallyDominant
        ((equalizer.lift ι' hι).left ≫ (equalizer.ι f' g').left) := by
      rw [hfac]; exact (inferInstance : IsSchemeTheoreticallyDominant ι)
    rw [IsClosedImmersion.isIso_iff_ker_eq_bot, eq_bot_iff,
      ← ((equalizer.lift ι' hι).left ≫ (equalizer.ι f' g').left).ker_eq_bot]
    exact Scheme.Hom.le_ker_comp _ _
  exact (cancel_epi (equalizer.ι f' g').left).1 congr($(equalizer.condition f' g').left)

section graph

variable {Y P S : Scheme.{u}} (sY : Y ⟶ S) (sP : P ⟶ S) (U : Y.Opens) (g : U.toScheme ⟶ P)
  (hg : g ≫ sP = U.ι ≫ sY) [QuasiCompact U.ι] [IsSeparated sP]

/-- The open immersion `U ⟶ π⁻¹ U` into the preimage of `U` in the closure of the graph. -/
noncomputable def graphClosureι :
    U.toScheme ⟶ (graphClosureFst sY sP U g hg ⁻¹ᵁ U).toScheme :=
  IsOpenImmersion.lift (graphClosureFst sY sP U g hg ⁻¹ᵁ U).ι (graphMap sY sP U g hg).toImage
    (by
      rintro _ ⟨x, rfl⟩
      rw [Scheme.Opens.range_ι]
      change graphClosureFst sY sP U g hg ((graphMap sY sP U g hg).toImage x) ∈ U
      rw [← Scheme.Hom.comp_apply]
      simp)

omit [QuasiCompact U.ι] [IsSeparated sP] in
@[reassoc]
lemma graphClosureι_ι : graphClosureι sY sP U g hg ≫ (graphClosureFst sY sP U g hg ⁻¹ᵁ U).ι =
    (graphMap sY sP U g hg).toImage :=
  IsOpenImmersion.lift_fac _ _ _

instance : IsSchemeTheoreticallyDominant (graphClosureι sY sP U g hg) := by
  have := quasiCompact_graphMap sY sP U g hg
  have : IsSchemeTheoreticallyDominant
      (graphClosureι sY sP U g hg ≫ (graphClosureFst sY sP U g hg ⁻¹ᵁ U).ι) := by
    rw [graphClosureι_ι]; infer_instance
  have : QuasiCompact (graphClosureι sY sP U g hg ≫ (graphClosureFst sY sP U g hg ⁻¹ᵁ U).ι) := by
    rw [graphClosureι_ι]; infer_instance
  exact .of_comp_ι _

/-- The preimage of `U` is scheme-theoretically dense in the closure of the graph. -/
instance : IsSchemeTheoreticallyDominant (graphClosureFst sY sP U g hg ⁻¹ᵁ U).ι := by
  have := quasiCompact_graphMap sY sP U g hg
  exact .ι_of_fac _ _ (graphClosureι_ι sY sP U g hg)

/-- **The closure of the graph is isomorphic to `U` over `U`.** -/
lemma isIso_graphClosureFst_restrict' : IsIso (graphClosureFst sY sP U g hg ∣_ U) := by
  set Γ := graphMap sY sP U g hg
  set π := graphClosureFst sY sP U g hg
  set ι' := graphClosureι sY sP U g hg
  have hπ : Γ.toImage ≫ π = U.ι := by simp [π, Γ]
  have hq : Γ.toImage ≫ graphClosureSnd sY sP U g hg = g := by simp [Γ]
  have hι' : ι' ≫ (π ⁻¹ᵁ U).ι = Γ.toImage := graphClosureι_ι ..
  have h₂ : ι' ≫ π ∣_ U = 𝟙 _ := by
    rw [← cancel_mono U.ι, Category.assoc, morphismRestrict_ι, reassoc_of% hι', hπ,
      Category.id_comp]
  refine ⟨ι', ?_, h₂⟩
  rw [← cancel_mono ((π ⁻¹ᵁ U).ι ≫ Γ.imageι), Category.assoc, reassoc_of% hι',
    Γ.toImage_imageι, Category.id_comp]
  apply pullback.hom_ext
  · simp only [Category.assoc, graphMap_fst, Γ]
    exact morphismRestrict_ι π U
  · simp only [Category.assoc, graphMap_snd, Γ]
    refine ext_of_isSchemeTheoreticallyDominant_of_isSeparated sP ?_ ι' ?_
    · simp only [Category.assoc, hg]
      rw [← Category.assoc, morphismRestrict_ι, Category.assoc, Category.assoc,
        pullback.condition]
    · simp only [reassoc_of% h₂, reassoc_of% hι']
      exact hq.symm

end graph

namespace Chow

open ProjectiveSpace

variable {R : Type u} [CommRing R] {Y : Scheme.{u}} {sY : Y ⟶ Spec (.of R)} (d : Data sY)

namespace Data

/-- The homogeneous coordinate ring of `ℙ(N; R)`. -/
local notation3 "𝒜" d => homogeneousSubmodule (Fin (Data.N d + 1)) R

/-- `U` is scheme-theoretically dense in `Y'`. -/
instance : IsSchemeTheoreticallyDominant (d.π ⁻¹ᵁ d.U).ι :=
  inferInstanceAs (IsSchemeTheoreticallyDominant (graphClosureFst _ _ d.U d.g d.g_toSpec ⁻¹ᵁ d.U).ι)

section closed

variable [IsSeparated sY] (i : d.I) (κ : d.K) (hκ : κ i = none)

omit [IsSeparated sY] in
include hκ in
/-- If `κ i = none`, then `ρ ∘ q` factors through the closed immersion `ε`. -/
lemma ker_ε_le' : (d.ε i).ker ≤ (d.q ∣_ d.W κ ≫ d.ρ i κ).ker :=
  calc (d.ε i).ker ≤ ((d.j ⁻¹ᵁ d.q ⁻¹ᵁ d.W κ).ι ≫ Y.homOfLE (d.U_le i) ≫ d.ε i).ker := by
        rw [← Category.assoc]; exact Scheme.Hom.le_ker_comp _ _
    _ = (d.q ∣_ d.W κ ≫ d.ρ i κ).ker := by
        rw [← d.restrict_j_q_ρ i κ hκ, Scheme.Hom.ker_comp, (d.j ∣_ _).ker_eq_bot,
          Scheme.IdealSheafData.map_bot]

/-- The morphism `q⁻¹ D₊(X_κ) ⟶ V i` which agrees with `π` (`h'_ι`), for `κ i = none`. -/
noncomputable def h' : (d.q ⁻¹ᵁ d.W κ).toScheme ⟶ (d.V i).toScheme :=
  IsClosedImmersion.lift (d.ε i) _ (d.ker_ε_le' i κ hκ)

omit [IsSeparated sY] in
/-- `h'` lifts `ρ ∘ q` along `ε`. -/
@[reassoc]
lemma h'_ε : d.h' i κ hκ ≫ d.ε i = d.q ∣_ d.W κ ≫ d.ρ i κ :=
  IsClosedImmersion.lift_fac ..

omit [IsSeparated sY] in
/-- On `U`, `h'` is the inclusion `U ⟶ V i`. -/
lemma j_restrict_h' : d.j ∣_ (d.q ⁻¹ᵁ d.W κ) ≫ d.h' i κ hκ =
    (d.j ⁻¹ᵁ d.q ⁻¹ᵁ d.W κ).ι ≫ Y.homOfLE (d.U_le i) := by
  rw [← cancel_mono (d.ε i), Category.assoc, h'_ε, restrict_j_q_ρ _ i κ hκ, Category.assoc]

/-- On `q⁻¹ D₊(X_κ)`, `π` factors through `h' : q⁻¹ D₊(X_κ) ⟶ V i`. -/
lemma h'_ι : d.h' i κ hκ ≫ (d.V i).ι = (d.q ⁻¹ᵁ d.W κ).ι ≫ d.π := by
  refine ext_of_isSchemeTheoreticallyDominant_of_isSeparated sY ?_ (d.j ∣_ (d.q ⁻¹ᵁ d.W κ)) ?_
  · rw [Category.assoc, ← ε_SpecMap_C, h'_ε_assoc, Category.assoc, ρ_SpecMap_C,
      morphismRestrict_ι_assoc]
    simp [pullback.condition]
  · rw [reassoc_of% j_restrict_h', Scheme.homOfLE_ι, morphismRestrict_ι_assoc, j_π]

include hκ in
/-- **`q` is a closed immersion over the chart `D₊(X_κ)`** when `κ i = none`. -/
theorem isClosedImmersion_q_restrict' : IsClosedImmersion (d.q ∣_ d.W κ) := by
  refine isClosedImmersion_morphismRestrict_of_graph d.c (d.W κ)
    (pullback.fst (d.ρ i κ) (d.ε i)) (pullback.snd _ _ ≫ (d.V i).ι) ?_
    (pullback.lift _ (d.h' i κ hκ) (d.h'_ε i κ hκ).symm) (pullback.lift_fst _ _ _) ?_
  · rw [Category.assoc, ← ε_SpecMap_C, ← pullback.condition_assoc, ρ_SpecMap_C]
  · rw [pullback.lift_snd_assoc, h'_ι]

end closed

/-- On `π⁻¹ V i ∩ q⁻¹ D₊(X_λ)` with `λ i = g`, the coordinate `X_{λ[i ↦ none]}` does not vanish:
its ratio with `X_λ` is inverse to the generator `a i g`. -/
lemma mem_W_update' (y : d.Y') (i : d.I) (l : d.K) (g : d.G i) (hl : l i = some g)
    (hy₁ : d.π y ∈ d.V i) (hy₂ : d.q y ∈ d.W l) :
    d.q y ∈ d.W (Function.update l i none) := by
  set l' := Function.update l i none
  let V : d.Y'.Opens := d.π ⁻¹ᵁ d.V i ⊓ d.q ⁻¹ᵁ d.W l
  have hV : V ≤ d.q ⁻¹ᵁ d.W l := inf_le_right
  let e := Proj.basicOpenIsoSpec _ _ (X_mem_homogeneousSubmodule_one (R := R) (d.e l)) one_pos
  let r : Away (𝒜 d) (X (d.e l)) := Away.isLocalizationElem
    (X_mem_homogeneousSubmodule_one (d.e l)) (X_mem_homogeneousSubmodule_one (d.e l'))
  let m : V.toScheme ⟶ Spec (.of (Away (𝒜 d) (X (d.e l)))) :=
    d.Y'.homOfLE hV ≫ d.q ∣_ d.W l ≫ e.hom
  let n : V.toScheme ⟶ Spec (.of (MvPolynomial (d.G i) R)) :=
    d.Y'.homOfLE inf_le_left ≫ d.π ∣_ d.V i ≫ d.ε i
  have hD : d.j ⁻¹ᵁ V ≤ d.D l := fun _ hx ↦ (d.j_preimage_q_preimage l).le (hV hx)
  let k := d.U.toScheme.homOfLE hD ≫ d.U.toScheme.basicOpenToSpecAway (d.φ (X (d.e l)))
  have hm : d.j ∣_ V ≫ m =
      k ≫ Spec.map (CommRingCat.ofHom (Proj.awayToLocalization (𝒜 d) d.φ (X (d.e l)))) := by
    simp only [m, k, Category.assoc]
    exact d.restrict_j_q_basicOpenIsoSpec l V hV
  have hn : d.j ∣_ V ≫ n = k ≫ Spec.map (CommRingCat.ofHom
      ((algebraMap _ (Localization.Away (d.φ (X (d.e l))))).comp (d.evalU i))) := by
    have : d.j ∣_ V ≫ d.Y'.homOfLE inf_le_left ≫ d.π ∣_ d.V i =
        (d.j ⁻¹ᵁ V).ι ≫ Y.homOfLE (d.U_le i) := by
      rw [← cancel_mono (d.V i).ι]
      simp only [Category.assoc, morphismRestrict_ι, Scheme.homOfLE_ι_assoc,
        morphismRestrict_ι_assoc, j_π, Scheme.homOfLE_ι]
    simp only [k, n, Category.assoc]
    rw [CommRingCat.ofHom_comp, Spec.map_comp, Scheme.basicOpenToSpecAway_SpecMap_assoc,
      Scheme.homOfLE_ι_assoc, reassoc_of% this, homOfLE_ε]
    rfl
  have hring : Proj.awayToLocalization (𝒜 d) d.φ (X (d.e l)) r *
      algebraMap _ (Localization.Away (d.φ (X (d.e l)))) (d.evalU i (X g)) = 1 := by
    have := d.mono_update l i none
    rw [hl, show d.A i none = 1 from rfl, one_mul] at this
    rw [Proj.awayToLocalization_mk, mul_comm, IsLocalization.mul_mk'_eq_mk'_of_mul]
    simp only [pow_one, φ_X, evalU, eval₂Hom_X']
    rw [mul_comm, this]
    exact IsLocalization.mk'_self' (Localization.Away (d.φ (X (d.e l))))
  have hs : IsUnit (m.appTop ((Scheme.ΓSpecIso _).inv r)) := by
    refine IsUnit.of_mul_eq_one (n.appTop ((Scheme.ΓSpecIso _).inv (X g))) ?_
    apply (d.j ∣_ V).app_injective ⊤
    have h₁ : (d.j ∣_ V).appTop (m.appTop ((Scheme.ΓSpecIso _).inv r)) =
        (d.j ∣_ V ≫ m).appTop ((Scheme.ΓSpecIso _).inv r) := rfl
    have h₂ : (d.j ∣_ V).appTop (n.appTop ((Scheme.ΓSpecIso _).inv (X g))) =
        (d.j ∣_ V ≫ n).appTop ((Scheme.ΓSpecIso _).inv (X g)) := rfl
    change (d.j ∣_ V).appTop _ = (d.j ∣_ V).appTop _
    rw [map_mul, map_one, h₁, h₂, hm, hn, appTop_comp_SpecMap_ΓSpecIso_inv,
      appTop_comp_SpecMap_ΓSpecIso_inv, ← map_mul, ← map_mul]
    simp only [CommRingCat.hom_ofHom, RingHom.comp_apply, hring, map_one]
  set y' : V.toScheme := ⟨y, hy₁, hy₂⟩
  have h₂ : y' ∈ m ⁻¹ᵁ (Spec _).basicOpen ((Scheme.ΓSpecIso _).inv r) := by
    rw [Scheme.preimage_basicOpen_top, Scheme.basicOpen_of_isUnit _ hs]
    trivial
  have E : Proj.awayι _ _ (X_mem_homogeneousSubmodule_one (d.e l)) one_pos ⁻¹ᵁ d.W l' =
      (Spec _).basicOpen ((Scheme.ΓSpecIso _).inv r) := by
    rw [Proj.awayι_preimage_basicOpen _ _ one_pos (X_mem_homogeneousSubmodule_one (d.e l'))
      one_pos, basicOpen_eq_of_affine]
  have h₃ : y' ∈ m ⁻¹ᵁ Proj.awayι _ _ (X_mem_homogeneousSubmodule_one (d.e l)) one_pos ⁻¹ᵁ
      d.W l' := by
    rw [E]
    exact h₂
  have hmι : m ≫ Proj.awayι _ _ (X_mem_homogeneousSubmodule_one (d.e l)) one_pos = V.ι ≫ d.q := by
    simp only [m, e, Category.assoc, ← Proj.basicOpenIsoSpec_inv_ι, Iso.hom_inv_id_assoc,
      morphismRestrict_ι, Scheme.homOfLE_ι_assoc]
  have h₄ : (m ≫ Proj.awayι _ _ (X_mem_homogeneousSubmodule_one (d.e l)) one_pos) y' ∈
      d.W l' := h₃
  rwa [hmι] at h₄

/-- Every point of `Y'` maps under `q` to a chart `D₊(X_κ)` with `κ i = none` for some `i`. -/
lemma exists_chart' (y : d.Y') : ∃ i κ, κ i = none ∧ d.q y ∈ d.W κ := by
  obtain ⟨i, hi⟩ : ∃ i, d.π y ∈ d.V i :=
    TopologicalSpace.Opens.mem_iSup.mp (d.iSup_V.ge (Set.mem_univ (d.π y)))
  obtain ⟨k, hk⟩ : ∃ k, d.q y ∈ ProjectiveSpace.U d.N R k :=
    TopologicalSpace.Opens.mem_iSup.mp ((iSup_U d.N R).ge (Set.mem_univ (d.q y)))
  have hl : d.q y ∈ d.W (d.e.symm k) := by
    simpa [W, ProjectiveSpace.U] using hk
  cases h : d.e.symm k i with
  | none => exact ⟨i, _, h, hl⟩
  | some g => exact ⟨i, _, Function.update_self .., d.mem_W_update' y i _ g h hi hl⟩

/-- **The projection `Y' ⟶ ℙ(N; R)` is a closed immersion.** -/
theorem isClosedImmersion_q' [IsProper sY] : IsClosedImmersion d.q := by
  refine isClosedImmersion_of_isClosed_range_of_cover d.q d.q.isClosedMap.isClosed_range
    (fun p : {p : d.I × d.K // p.2 p.1 = none} ↦ d.W p.1.2) (fun y ↦ ?_) ?_
  · obtain ⟨i, κ, h, hy⟩ := d.exists_chart' y
    exact ⟨⟨(i, κ), h⟩, hy⟩
  · rintro ⟨⟨i, κ⟩, h⟩
    exact d.isClosedImmersion_q_restrict' i κ h

/-- **`π : Y' ⟶ Y` is an isomorphism over `U`.** -/
theorem isIso_π_restrict' : IsIso (d.π ∣_ d.U) :=
  isIso_graphClosureFst_restrict' ..

/-- `Y'` is irreducible if `Y` is. -/
lemma irreducibleSpace_Y' [IrreducibleSpace Y] : IrreducibleSpace d.Y' := by
  have hne : (d.U : Set Y).Nonempty := d.dense_U.nonempty
  have : IrreducibleSpace d.U.toScheme :=
    Subtype.irreducibleSpace ⟨hne, (IrreducibleSpace.isIrreducible_univ Y).2.open_subset
      d.U.isOpen (Set.subset_univ _)⟩
  exact irreducibleSpace_image d.Γ

end Data

open TopologicalSpace in
/-- **Chow data exist** for an irreducible, quasi-compact, quasi-separated scheme locally of
finite type over `R`. -/
theorem Data.nonempty_of_irreducibleSpace [IrreducibleSpace Y] [CompactSpace Y]
    [QuasiSeparatedSpace Y] [LocallyOfFiniteType sY] : Nonempty (Data sY) := by
  classical
  have hx (x : Y) : ∃ V : Y.Opens, IsAffineOpen V ∧ x ∈ V := by
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact ⟨V, hV, hxV⟩
  choose V hV hxV using hx
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x ↦ (V x : Set Y))
    (fun x ↦ (V x).isOpen) (fun x _ ↦ Set.mem_iUnion.2 ⟨x, hxV x⟩)
  have hgen (x : Y) : ∃ s : Finset Γ(V x, ⊤), Function.Surjective
      (eval₂Hom ((V x).ι ≫ sY).baseHom (fun a : s ↦ (a : Γ(V x, ⊤)))) := by
    have : IsAffine (V x) := hV x
    have hft : ((V x).ι ≫ sY).baseHom.FiniteType := by
      have h := (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)
        (f := (V x).ι ≫ sY)).mp inferInstance
      exact h.comp (RingHom.FiniteType.of_surjective _
        (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.symm.surjective)
    exact exists_finset_surjective hft
  choose s hs using hgen
  let η := genericPoint Y
  have hη (x : Y) : η ∈ V x :=
    ((genericPoint_spec Y).mem_open_set_iff (V x).isOpen).mpr ⟨x, trivial, hxV x⟩
  have hS : IsOpen (⋂ x : t, (V x : Set Y)) := isOpen_iInter_of_finite fun x ↦ (V x).isOpen
  obtain ⟨_, ⟨U, hU, rfl⟩, hηU, hUS⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_iInter.2 fun (x : t) ↦ hη x) hS
  have : IsAffine U := hU
  exact ⟨{
    I := t
    V := fun x ↦ V x
    isAffineOpen_V := fun x ↦ hV x
    iSup_V := by
      rw [eq_top_iff]
      intro y _
      obtain ⟨x, hx, hy⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ y))
      exact Opens.mem_iSup.2 ⟨⟨x, hx⟩, hy⟩
    G := fun x ↦ s x
    a := fun x a ↦ a
    surjective := fun x ↦ hs x
    U := U
    U_le := fun x ↦ hUS.trans (Set.iInter_subset (fun x : t ↦ (V x : Set Y)) x)
    dense_U := U.isOpen.dense ⟨η, hηU⟩
    quasiCompact_U := inferInstance }⟩

end Chow

/-- **Chow's lemma** (EGA II 5.6.1, irreducible case). Let `Y` be an irreducible scheme, proper
over `Spec R`. There are `N`, a closed immersion `c : Y' ⟶ Y ×_R ℙ(N; R)` from an irreducible
scheme `Y'` whose second projection `Y' ⟶ ℙ(N; R)` is a closed immersion, and a nonempty open
`U ⊆ Y` over which the first projection `π : Y' ⟶ Y` restricts to an isomorphism `π⁻¹ U ≅ U`;
moreover `π⁻¹ U` is scheme-theoretically dense in `Y'`. -/
theorem exists_chow_of_irreducibleSpace {R : Type u} [CommRing R] {Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of R)) [IrreducibleSpace Y] [IsProper sY] :
    ∃ (N : ℕ) (Y' : Scheme.{u}) (c : Y' ⟶ pullback sY (ProjectiveSpace.toSpec N R))
      (U : Y.Opens), IsClosedImmersion c ∧ IsClosedImmersion (c ≫ pullback.snd _ _) ∧
      (U : Set Y).Nonempty ∧ IsIso ((c ≫ pullback.fst _ _) ∣_ U) ∧ IrreducibleSpace Y' ∧
      IsSchemeTheoreticallyDominant ((c ≫ pullback.fst _ _) ⁻¹ᵁ U).ι := by
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated sY
  obtain ⟨d⟩ := Chow.Data.nonempty_of_irreducibleSpace (sY := sY)
  exact ⟨d.N, d.Y', d.c, d.U, inferInstance, d.isClosedImmersion_q', d.dense_U.nonempty,
    d.isIso_π_restrict', d.irreducibleSpace_Y', inferInstance⟩

end AlgebraicGeometry
