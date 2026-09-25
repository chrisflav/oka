/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.AnalyticSpace.PushforwardStalkCoherent
import Oka.AnalyticSpace.Coherent

/-!
# Pushforward of the structure sheaf along finite étale morphisms

For a finite étale morphism `p : W ⟶ Z` of complex analytic spaces with `W` Hausdorff, `p_* 𝒪_W` is
locally free of finite rank: near `z ∈ Z`, the fibre `p⁻¹ z` has pairwise disjoint neighbourhoods
`O_w` on which `p` is injective, covering `p⁻¹ V` for a neighbourhood `V` of `z` contained in every
`p(O_w)`, and the indicator sections `e_w` of the `O_w ∩ p⁻¹ V` form a basis of `p_* 𝒪_W` over
`V`, on stalks as well as on sections. In particular `p_* 𝒪_W` is coherent
(`ComplexAnalytic.AnalyticSpace.isCoherent_pushUnit_of_isFiniteEtale`), and hence so is `p_* M`
for every coherent `𝒪_W`-module `M`
(`ComplexAnalytic.AnalyticSpace.isCoherent_pushforward_of_isFiniteEtale`).
-/

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open AlgebraicGeometry.LocallyRingedSpace

universe u

noncomputable section

namespace ComplexAnalytic.AnalyticSpace

/-- The structure sheaf of a complex analytic space has locally finitely generated tuple
relations. -/
lemma hasLocalTupleRelations_unit (X : AnalyticSpace.{u}) :
    HasLocalTupleRelations (SheafOfModules.unit X.toLocallyRingedSpace.ringSheaf) :=
  haveI : (SheafOfModules.unit X.toLocallyRingedSpace.ringSheaf).IsCoherent :=
    X.isCoherentStructureSheaf
  (hasLocalModuleRelations_of_isCoherent _).hasLocalTupleRelations

variable {W Z : AnalyticSpace.{u}} (p : W ⟶ Z)

/-- **`p_* 𝒪_W` is coherent** for a finite étale morphism `p` with Hausdorff source. -/
theorem isCoherent_pushUnit_of_isFiniteEtale [IsFiniteEtale p] [T2Space W] :
    (Hom.pushUnit p.toLRSHom).IsCoherent := by
  classical
  refine Hom.isCoherent_pushUnit_of_stalks _ Z.hasLocalTupleRelations_unit fun z ↦ ?_
  let f := p.toLRSHom
  haveI : Finite (f.base ⁻¹' {z}) := IsFinite.finite_fiber z
  haveI : Fintype (f.base ⁻¹' {z}) := Fintype.ofFinite _
  have hloc : ∀ x : W, ∃ U : Opens W, x ∈ U ∧ Set.InjOn f.base U := fun x ↦ by
    obtain ⟨e, hxe, he⟩ := IsLocalIso.isLocalHomeomorph (f := p) x
    refine ⟨⟨e.source, e.open_source⟩, hxe, ?_⟩
    change Set.InjOn (⇑f.base) e.source
    rw [he]
    exact e.injOn
  choose U hxU hinj using hloc
  obtain ⟨V, O, -, hzV, hxO, hOU, hOV, hdisj, hcov⟩ := Hom.exists_fibre_cover f
    IsFinite.isClosedMap (Set.toFinite _) (show z ∈ (⊤ : Opens Z) from trivial)
    (fun x ↦ U x.1) fun x ↦ hxU x.1
  have hopen : IsOpenMap f.base := (IsLocalIso.isLocalHomeomorph (f := p)).isOpenMap
  let img : f.base ⁻¹' {z} → Opens Z := fun x ↦ ⟨f.base '' (O x).carrier, hopen _ (O x).2⟩
  obtain ⟨V₁, hzV₁, hV₁⟩ := exists_open_forall Z.toLocallyRingedSpace z (fun x V' ↦ V' ≤ img x)
    (fun _ _ _ h₁ h₂ ↦ h₁.trans h₂) fun x ↦ ⟨img x, ⟨x.1, hxO x, x.2⟩, le_rfl⟩
  let V' := V₁ ⊓ V
  have hV'V : V' ≤ V := inf_le_right
  let O' : f.base ⁻¹' {z} → Opens W := fun x ↦ O x ⊓ (Opens.map f.base).obj V'
  have hO'V : ∀ x, O' x ≤ (Opens.map f.base).obj V' := fun x ↦ inf_le_right
  have hcov' : (Opens.map f.base).obj V' ≤ ⨆ x, O' x := fun w hw ↦ by
    obtain ⟨x, hx⟩ := Opens.mem_iSup.1 (hcov ((Opens.map f.base).monotone hV'V hw))
    exact Opens.mem_iSup.2 ⟨x, hx, hw⟩
  have hdisj' : ∀ x x', x ≠ x' → O' x ⊓ O' x' = ⊥ := fun x x' hxx' ↦
    eq_bot_iff.2 fun w hw ↦ (hdisj x x' hxx').le ⟨hw.1.1, hw.2.1⟩
  -- the indicator sections
  choose E hE hE0 using fun x ↦
    exists_extend_zero (SheafOfModules.unit W.toLocallyRingedSpace.ringSheaf) O' hO'V hcov' hdisj' x
      (1 : W.presheaf.obj (op (O' x)))
  let e : Fin (Fintype.card (f.base ⁻¹' {z})) ≃ f.base ⁻¹' {z} := (Fintype.equivFin _).symm
  let g : Fin (Fintype.card (f.base ⁻¹' {z})) →
      W.presheaf.obj (op ((Opens.map f.base).obj V')) := fun j ↦ E (e j)
  -- the germs of the indicator sections
  have hgerm : ∀ x x₀ (w : W) (hw : w ∈ O' x₀),
      W.presheaf.germ ((Opens.map f.base).obj V') w (hO'V x₀ hw) (E x) =
        if x = x₀ then 1 else 0 := by
    intro x x₀ w hw
    rw [← TopCat.Presheaf.germ_res_apply W.presheaf (homOfLE (hO'V x₀)) w hw]
    by_cases hx : x = x₀
    · subst hx
      rw [if_pos rfl]
      have := hE x
      change W.res (hO'V x) (E x) = 1 at this
      exact (congrArg _ this).trans (map_one _)
    · rw [if_neg hx]
      have := hE0 x x₀ (Ne.symm hx)
      change W.res (hO'V x₀) (E x) = 0 at this
      exact (congrArg _ this).trans (map_zero _)
  -- over every point of `V'`, each `O' x` contains exactly one point of the fibre
  have hex : ∀ z' ∈ V', ∀ x : f.base ⁻¹' {z}, ∃ w ∈ O' x, f.base w = z' := by
    intro z' hz' x
    obtain ⟨w, hw, hwz⟩ := hV₁ x hz'.1
    exact ⟨w, ⟨hw, show f.base w ∈ V' by rw [hwz]; exact hz'⟩, hwz⟩
  have huniq : ∀ x (w w' : W), w ∈ O' x → w' ∈ O' x → f.base w = f.base w' → w = w' :=
    fun x w w' hw hw' h ↦ hinj x.1 (hOU x hw.1) (hOU x hw'.1) h
  have hmem : ∀ w ∈ (Opens.map f.base).obj V', ∃ x, w ∈ O' x := fun w hw ↦
    Opens.mem_iSup.1 (hcov' hw)
  let π := fun z' ↦ TopCat.Presheaf.pushforwardStalkToPi f.base W.presheaf z'
  -- evaluation of combinations of the indicator sections along the fibre
  have heval : ∀ (z' : Z) (hz' : z' ∈ V') (r : Fin (Fintype.card (f.base ⁻¹' {z})) →
      Z.presheaf.stalk z') (x₀ : f.base ⁻¹' {z}) (w : f.base ⁻¹' {z'}) (hw : w.1 ∈ O' x₀),
      π z' (∑ j, Hom.stalkAlgMap f z' (r j) *
        (f.base _* W.presheaf).germ V' z' hz' (g j)) w = fibreStalkMap p z' w (r (e.symm x₀)) := by
    intro z' hz' r x₀ w hw
    simp only [π]
    rw [map_sum, Finset.sum_apply]
    simp only [map_mul, Pi.mul_apply]
    rw [Finset.sum_eq_single (e.symm x₀)]
    · erw [pushforwardStalkToPi_stalkFunctor_map]
      rw [TopCat.Presheaf.pushforwardStalkToPi_germ]
      erw [hgerm (e (e.symm x₀)) x₀ w.1 hw]
      rw [Equiv.apply_symm_apply, if_pos rfl, mul_one]
    · intro j _ hj
      rw [TopCat.Presheaf.pushforwardStalkToPi_germ]
      erw [hgerm (e j) x₀ w.1 hw]
      rw [if_neg (fun h ↦ hj (by rw [← h, Equiv.symm_apply_apply])), mul_zero]
    · simp
  refine ⟨V', Fintype.card (f.base ⁻¹' {z}), 0, g, fun l ↦ l.elim0, ⟨hzV₁, hzV⟩,
    fun l ↦ l.elim0, fun z' hz' ζ ↦ ?_, fun z' hz' r hr ↦ ?_⟩
  · -- generation
    choose w hwO hwz using hex z' hz'
    let R : f.base ⁻¹' {z} → Z.presheaf.stalk z' := fun x ↦
      (RingEquiv.ofBijective _ (bijective_fibreStalkMap p z' ⟨w x, hwz x⟩)).symm
        (π z' ζ ⟨w x, hwz x⟩)
    refine ⟨fun j ↦ R (e j), (bijective_pushforwardStalkToPi p z').1 (funext fun w' ↦ ?_)⟩
    obtain ⟨x₀, hx₀⟩ := hmem w'.1 (show f.base w'.1 ∈ V' by rw [w'.2]; exact hz')
    rw [heval z' hz' (fun j ↦ R (e j)) x₀ w' hx₀]
    obtain rfl : w' = ⟨w x₀, hwz x₀⟩ := Subtype.ext (huniq x₀ _ _ hx₀ (hwO x₀)
      (w'.2.trans (hwz x₀).symm))
    rw [Equiv.apply_symm_apply]
    exact ((RingEquiv.ofBijective _ (bijective_fibreStalkMap p z' _)).apply_symm_apply _).symm
  · -- relations: the indicator sections are a basis
    refine ⟨fun l ↦ l.elim0, fun j ↦ ?_⟩
    rw [Finset.univ_eq_empty, Finset.sum_empty]
    choose w hwO hwz using hex z' hz'
    have := congrArg (fun ζ ↦ π z' ζ ⟨w (e j), hwz (e j)⟩) hr
    simp only [map_zero, Pi.zero_apply] at this
    rw [heval z' hz' r (e j) ⟨w (e j), hwz (e j)⟩ (hwO (e j)), Equiv.symm_apply_apply] at this
    exact (injective_iff_map_eq_zero _).1 (bijective_fibreStalkMap p z' _).1 _ this

/-- **Pushforward of coherent sheaves along finite étale morphisms**: for `p : W ⟶ Z` finite étale
with `W` Hausdorff, `p_* M` is coherent for every coherent `𝒪_W`-module `M`. -/
theorem isCoherent_pushforward_of_isFiniteEtale [IsFiniteEtale p] [T2Space W]
    (M : SheafOfModules.{u} W.toLocallyRingedSpace.ringSheaf) [M.IsCoherent] :
    ((SheafOfModules.pushforward.{u} p.toLRSHom.toRingSheafHom).obj M).IsCoherent := by
  haveI := isCoherent_pushUnit_of_isFiniteEtale p
  exact Hom.isCoherent_pushforward_of_isClosedMap _ M IsFinite.isClosedMap
    fun y ↦ (haveI := IsFinite.finite_fiber (f := p) y; Set.toFinite _)

end ComplexAnalytic.AnalyticSpace
