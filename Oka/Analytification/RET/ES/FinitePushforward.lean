/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.Topology.Sheaves.Stalks
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Oka.AnalyticSpace.Evaluation
import Oka.AnalyticSpace.Finite
import Oka.AnalyticSpace.LocalIso
import Oka.AnalyticSpace.Coherent
import Oka.Geometry.RingedSpace.LocallyRingedSpace.Modules

/-!
# Stalks of pushforwards along finite maps

Let `f : X ⟶ Y` be a closed continuous map and `F` a sheaf of commutative rings on `X`. For
`y ∈ Y` the natural map
`(f_* F)_y → ∏_{x ∈ f⁻¹ y} F_x`, `germ_y s ↦ (germ_x s)_x`
(`TopCat.Presheaf.pushforwardStalkToPi`) is injective, and it is bijective when `X` is Hausdorff
and the fibre `f⁻¹ y` is finite. Every open neighbourhood of `f⁻¹ y` contains the preimage of an
open neighbourhood of `y` because `f` is closed, and finitely many points of a Hausdorff space
have pairwise disjoint neighbourhoods, over which sections glue.

For a finite morphism `p : W ⟶ Y` of complex analytic spaces with `W` Hausdorff this computes
the stalks of `p_* 𝒪_W` (`ComplexAnalytic.AnalyticSpace.bijective_pushforwardStalkToPi`),
compatibly with the stalk maps of `p` (`ComplexAnalytic.fibreStalkMap`). If `p` is moreover a
local isomorphism, `(p_* 𝒪_W)_y ≅ 𝒪_{Y,y}^{p⁻¹ y}` as `𝒪_{Y,y}`-algebras
(`ComplexAnalytic.AnalyticSpace.pushforwardStalkEquivPi`).

## Main definitions

- `TopCat.Presheaf.pushforwardStalkToPi`: the map `(f_* F)_y → ∏_{x ∈ f⁻¹ y} F_x`.
- `ComplexAnalytic.fibreStalkMap`: the stalk map `𝒪_{Y,y} → 𝒪_{X,x}` of `f` at a point `x` of
  the fibre over `y`.

## Main results

- `TopCat.Presheaf.injective_pushforwardStalkToPi`,
  `TopCat.Presheaf.surjective_pushforwardStalkToPi`.
- `ComplexAnalytic.AnalyticSpace.pushforwardStalkToPi_stalkFunctor_map`: compatibility with the
  stalk maps of `p`.

## Hypotheses recorded, not proved

- `ComplexAnalytic.AnalyticSpace.FiniteMappingTheorem`: Grauert's finite mapping theorem (the
  pushforward of a coherent sheaf along a finite morphism is coherent).
-/

open CategoryTheory Opposite TopologicalSpace Topology AlgebraicGeometry

universe u

namespace TopCat.Presheaf

variable {X Y : TopCat.{u}} (f : X ⟶ Y) (F : X.Presheaf CommRingCat.{u}) (y : Y)

/-- The map `(f_* F)_y → ∏_{x ∈ f⁻¹ y} F_x` sending the germ of a section to its germs along the
fibre. -/
noncomputable def pushforwardStalkToPi :
    (f _* F).stalk y →+* ((x : f ⁻¹' {y}) → F.stalk x.1) :=
  RingHom.pi fun x ↦ (F.stalkPushforward CommRingCat f x.1).hom.comp
    ((f _* F).stalkCongr (.of_eq (x.2 : f x.1 = y).symm)).hom.hom

lemma pushforwardStalkToPi_germ (U : Opens Y) (hy : y ∈ U) (s : (f _* F).obj (op U))
    (x : f ⁻¹' {y}) :
    pushforwardStalkToPi f F y ((f _* F).germ U y hy s) x =
      F.germ ((Opens.map f).obj U) x.1
        (by change f x.1 ∈ U; rw [show f x.1 = y from x.2]; exact hy) s := by
  obtain ⟨x, hx⟩ := x
  obtain rfl : f x = y := hx
  change (F.stalkPushforward CommRingCat f x).hom ((f _* F).stalkSpecializes (specializes_refl _)
    ((f _* F).germ U (f x) hy s)) = _
  rw [germ_stalkSpecializes_apply]
  exact stalkPushforward_germ_apply CommRingCat f F U x hy s

/-- For a closed map `f`, every open neighbourhood of a fibre `f⁻¹ y` contains the preimage of
an open neighbourhood of `y`. -/
theorem _root_.IsClosedMap.exists_preimage_le {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} (hf : IsClosedMap f) {y : Y} (U : Opens X)
    (hU : f ⁻¹' {y} ⊆ U) : ∃ V : Opens Y, y ∈ V ∧ f ⁻¹' V ⊆ U := by
  refine ⟨⟨(f '' (U : Set X)ᶜ)ᶜ, (hf _ U.isOpen.isClosed_compl).isOpen_compl⟩, ?_, ?_⟩
  · rintro ⟨x, hx, rfl⟩
    exact hx (hU rfl)
  · intro x hx
    by_contra h
    exact hx ⟨x, h, rfl⟩

variable {f F y}

/-- Two sections of a sheaf over an empty open set are equal. -/
lemma eq_of_le_bot (hF : F.IsSheaf) {V : Opens X} (hV : V ≤ ⊥) (s t : F.obj (op V)) :
    s = t :=
  TopCat.Sheaf.eq_of_locally_eq' ⟨F, hF⟩ (U := fun e : Empty ↦ e.elim) V
    (fun e ↦ e.elim) (hV.trans bot_le) s t fun e ↦ e.elim

/-- **The map `(f_* F)_y → ∏_{x ∈ f⁻¹ y} F_x` is injective** for a sheaf `F` and a closed map
`f`. -/
theorem injective_pushforwardStalkToPi (hF : F.IsSheaf) (hf : IsClosedMap f) :
    Function.Injective (pushforwardStalkToPi f F y) := by
  intro a b hab
  obtain ⟨U, hyU, s, rfl⟩ := (f _* F).exists_germ_eq a
  obtain ⟨U', hyU', t, rfl⟩ := (f _* F).exists_germ_eq b
  have hx : ∀ x : f ⁻¹' {y}, ∃ (W : Opens X) (_ : x.1 ∈ W) (iU : W ⟶ (Opens.map f).obj U)
      (iU' : W ⟶ (Opens.map f).obj U'), F.map iU.op s = F.map iU'.op t := fun x ↦ by
    have h := congrFun hab x
    rw [pushforwardStalkToPi_germ, pushforwardStalkToPi_germ] at h
    exact F.germ_eq x.1 _ _ s t h
  choose W hxW iU iU' hst using hx
  obtain ⟨V, hyV, hVW⟩ := hf.exists_preimage_le (⨆ x, W x) fun x hx ↦
    Opens.mem_iSup.2 ⟨⟨x, hx⟩, hxW _⟩
  let V' : Opens Y := V ⊓ U ⊓ U'
  have hV' : y ∈ V' := ⟨⟨hyV, hyU⟩, hyU'⟩
  have i1 : V' ⟶ U := homOfLE (inf_le_left.trans inf_le_right)
  have i2 : V' ⟶ U' := homOfLE inf_le_right
  rw [← (f _* F).germ_res_apply i1 y hV' s, ← (f _* F).germ_res_apply i2 y hV' t]
  congr 1
  refine TopCat.Sheaf.eq_of_locally_eq' ⟨F, hF⟩ (fun x ↦ W x ⊓ (Opens.map f).obj V')
    ((Opens.map f).obj V') (fun _ ↦ homOfLE inf_le_right) (fun z hz ↦ ?_) _ _ fun x ↦ ?_
  · obtain ⟨x, hx⟩ := Opens.mem_iSup.1 (hVW hz.1.1)
    exact Opens.mem_iSup.2 ⟨x, hx, hz⟩
  · have h1 : ∀ (a : W x ⊓ (Opens.map f).obj V' ⟶ (Opens.map f).obj V')
        (b : W x ⊓ (Opens.map f).obj V' ⟶ W x) (g : (Opens.map f).obj V' ⟶ (Opens.map f).obj U)
        (g' : (Opens.map f).obj V' ⟶ (Opens.map f).obj U'),
        F.map a.op (F.map g.op s) = F.map a.op (F.map g'.op t) := by
      intro a b g g'
      rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← F.map_comp,
        ← F.map_comp, show g.op ≫ a.op = (iU x).op ≫ b.op from rfl,
        show g'.op ≫ a.op = (iU' x).op ≫ b.op from rfl, F.map_comp, F.map_comp,
        ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hst x]
    exact h1 _ (homOfLE inf_le_left) ((Opens.map f).map i1) ((Opens.map f).map i2)

/-- **The map `(f_* F)_y → ∏_{x ∈ f⁻¹ y} F_x` is surjective** for a sheaf `F` on a Hausdorff
space, a closed map `f` and a finite fibre `f⁻¹ y`. -/
theorem surjective_pushforwardStalkToPi [T2Space X] (hF : F.IsSheaf) (hf : IsClosedMap f)
    (hfin : (f ⁻¹' {y}).Finite) :
    Function.Surjective (pushforwardStalkToPi f F y) := by
  intro t
  have hx : ∀ x : f ⁻¹' {y}, ∃ (W : Opens X) (_ : x.1 ∈ W) (s : F.obj (op W)),
      F.germ W x.1 ‹_› s = t x := fun x ↦ F.exists_germ_eq (t x)
  choose W hxW s hs using hx
  obtain ⟨D, hD, hdisj⟩ := hfin.t2_separation
  let D' : f ⁻¹' {y} → Opens X := fun x ↦ W x ⊓ ⟨D x.1, (hD x.1).2⟩
  have hxD' : ∀ x, x.1 ∈ D' x := fun x ↦ ⟨hxW x, (hD x.1).1⟩
  let sf : ∀ x, F.obj (op (D' x)) := fun x ↦ F.map (homOfLE inf_le_left).op (s x)
  have hcompat : TopCat.Presheaf.IsCompatible F D' sf := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rfl
    · refine eq_of_le_bot hF (fun z hz ↦ ?_) _ _
      exact (hdisj i.2 j.2 (fun h ↦ hij (Subtype.ext h))).le_bot ⟨hz.1.2, hz.2.2⟩
  obtain ⟨g, hg, -⟩ := TopCat.Sheaf.existsUnique_gluing ⟨F, hF⟩ D' sf hcompat
  obtain ⟨V, hyV, hVD⟩ := hf.exists_preimage_le (⨆ x, D' x) fun x hx ↦
    Opens.mem_iSup.2 ⟨⟨x, hx⟩, hxD' _⟩
  refine ⟨(f _* F).germ V y hyV (F.map (homOfLE hVD : (Opens.map f).obj V ⟶ _).op g),
    funext fun x ↦ ?_⟩
  rw [pushforwardStalkToPi_germ, F.germ_res_apply, ← hs x]
  calc F.germ (⨆ x, D' x) x.1 _ g
      = F.germ (D' x) x.1 (hxD' x) (F.map (Opens.leSupr D' x).op g) :=
        (F.germ_res_apply (Opens.leSupr D' x) x.1 (hxD' x) g).symm
    _ = F.germ (D' x) x.1 (hxD' x) (sf x) := by rw [hg x]
    _ = F.germ (W x) x.1 (hxW x) (s x) := F.germ_res_apply _ _ _ _
end TopCat.Presheaf

namespace ComplexAnalytic

open AnalyticSpace

noncomputable section

/-! ### Stalk maps at the points of a fibre -/

section FibreStalk

variable {X Y : AnalyticSpace.{u}} (f : X ⟶ Y) (y : Y)

/-- The stalk map `𝒪_{Y,y} → 𝒪_{X,x}` of `f` at a point `x` of the fibre over `y`. -/
def fibreStalkMap (x : f.toLRSHom.base ⁻¹' {y}) :
    Y.presheaf.stalk y →+* X.presheaf.stalk x.1 :=
  (f.toLRSHom.stalkMap x.1).hom.comp
    (Y.presheaf.stalkCongr (.of_eq (x.2 : f.toLRSHom.base x.1 = y).symm)).hom.hom

lemma fibreStalkMap_germ (x : f.toLRSHom.base ⁻¹' {y}) (U : Y.Opens) (hy : y ∈ U)
    (s : Y.presheaf.obj (op U)) :
    fibreStalkMap f y x (Y.presheaf.germ U y hy s) =
      X.presheaf.germ ((Opens.map f.toLRSHom.base).obj U) x.1
        (by change f.toLRSHom.base x.1 ∈ U; rw [show f.toLRSHom.base x.1 = y from x.2]; exact hy)
        (f.toLRSHom.c.app (op U) s) := by
  obtain ⟨x, hx⟩ := x
  obtain rfl : f.toLRSHom.base x = y := hx
  simp only [fibreStalkMap, TopCat.Presheaf.stalkCongr, TopCat.Presheaf.stalkSpecializes_refl,
    RingHom.coe_comp, Function.comp_apply]
  exact AlgebraicGeometry.LocallyRingedSpace.stalkMap_germ_apply f.toLRSHom U x hy s

lemma fibreStalkMap_Γgerm (x : f.toLRSHom.base ⁻¹' {y}) (s : Y.presheaf.obj (op ⊤)) :
    fibreStalkMap f y x (Y.presheaf.Γgerm y s) = X.presheaf.Γgerm x.1 (f.pullbackΓ s) :=
  fibreStalkMap_germ f y x ⊤ trivial s

lemma evalStalk_fibreStalkMap (x : f.toLRSHom.base ⁻¹' {y}) (t : Y.presheaf.stalk y) :
    X.evalStalk x.1 (fibreStalkMap f y x t) = Y.evalStalk y t := by
  obtain ⟨x, hx⟩ := x
  obtain rfl : f.toLRSHom.base x = y := hx
  simp only [fibreStalkMap, TopCat.Presheaf.stalkCongr, TopCat.Presheaf.stalkSpecializes_refl,
    RingHom.coe_comp, Function.comp_apply]
  exact evalStalk_stalkMap_hom f x t

lemma bijective_fibreStalkMap [IsLocalIso f] (x : f.toLRSHom.base ⁻¹' {y}) :
    Function.Bijective (fibreStalkMap f y x) :=
  (ConcreteCategory.bijective_of_isIso (f.toLRSHom.stalkMap x.1)).comp
    (ConcreteCategory.bijective_of_isIso _)

end FibreStalk

/-! ### Stalks of `p_* 𝒪_W` -/

namespace AnalyticSpace

variable {W Y : AnalyticSpace.{u}} (p : W ⟶ Y) (y : Y)

/-- The structure map `𝒪_{Y,y} → (p_* 𝒪_W)_y`. -/
abbrev pushforwardStalkAlgebraMap :
    Y.presheaf.stalk y →+* (p.toLRSHom.base _* W.presheaf).stalk y :=
  ((TopCat.Presheaf.stalkFunctor _ y).map p.toLRSHom.c).hom

/-- **`(p_* 𝒪_W)_y → ∏_{w ∈ p⁻¹ y} 𝒪_{W,w}` is compatible with the stalk maps of `p`.** -/
lemma pushforwardStalkToPi_stalkFunctor_map (t : Y.presheaf.stalk y)
    (w : p.toLRSHom.base ⁻¹' {y}) :
    TopCat.Presheaf.pushforwardStalkToPi p.toLRSHom.base W.presheaf y
        (pushforwardStalkAlgebraMap p y t) w = fibreStalkMap p y w t := by
  obtain ⟨U, hyU, s, rfl⟩ := Y.presheaf.exists_germ_eq t
  erw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  rw [TopCat.Presheaf.pushforwardStalkToPi_germ, fibreStalkMap_germ]

/-- **The stalks of `p_* 𝒪_W` for a finite morphism `p` with Hausdorff source**:
`(p_* 𝒪_W)_y → ∏_{w ∈ p⁻¹ y} 𝒪_{W,w}` is bijective. -/
theorem bijective_pushforwardStalkToPi [IsFinite p] [T2Space W] :
    Function.Bijective (TopCat.Presheaf.pushforwardStalkToPi p.toLRSHom.base W.presheaf y) :=
  ⟨TopCat.Presheaf.injective_pushforwardStalkToPi W.sheaf.2 IsFinite.isClosedMap,
    TopCat.Presheaf.surjective_pushforwardStalkToPi W.sheaf.2 IsFinite.isClosedMap
      (haveI : Finite (p.toLRSHom.base ⁻¹' {y}) := IsFinite.finite_fiber y; Set.toFinite _)⟩

/-- **The stalks of `p_* 𝒪_W` are free** for a finite étale `p` with Hausdorff source:
`(p_* 𝒪_W)_y ≅ 𝒪_{Y,y}^{p⁻¹ y}`, compatibly with the structure maps from `𝒪_{Y,y}`
(`ComplexAnalytic.AnalyticSpace.pushforwardStalkEquivPi_pushforwardStalkAlgebraMap`). -/
def pushforwardStalkEquivPi [IsFiniteEtale p] [T2Space W] :
    (p.toLRSHom.base _* W.presheaf).stalk y ≃+* (p.toLRSHom.base ⁻¹' {y} → Y.presheaf.stalk y) :=
  (RingEquiv.ofBijective _ (bijective_pushforwardStalkToPi p y)).trans
    (RingEquiv.piCongrRight fun w ↦
      (RingEquiv.ofBijective (fibreStalkMap p y w) (bijective_fibreStalkMap p y w)).symm)

lemma pushforwardStalkEquivPi_pushforwardStalkAlgebraMap [IsFiniteEtale p] [T2Space W]
    (t : Y.presheaf.stalk y) :
    pushforwardStalkEquivPi p y (pushforwardStalkAlgebraMap p y t) = fun _ ↦ t := by
  funext w
  change (RingEquiv.ofBijective (fibreStalkMap p y w) (bijective_fibreStalkMap p y w)).symm
    (TopCat.Presheaf.pushforwardStalkToPi p.toLRSHom.base W.presheaf y
      (pushforwardStalkAlgebraMap p y t) w) = t
  rw [pushforwardStalkToPi_stalkFunctor_map]
  exact (RingEquiv.ofBijective _ _).symm_apply_apply t

/-- **Grauert's finite mapping theorem**, recorded as a hypothesis: the pushforward of a coherent
sheaf of modules along a finite morphism with Hausdorff source is coherent. It is not proved in
this file. -/
def FiniteMappingTheorem : Prop :=
  ∀ ⦃X Y : AnalyticSpace.{u}⦄ (f : X ⟶ Y) [IsFinite f] [T2Space X]
    (M : SheafOfModules.{u} X.toLocallyRingedSpace.ringSheaf) [M.IsCoherent],
    ((SheafOfModules.pushforward.{u} f.toLRSHom.toRingSheafHom).obj M).IsCoherent

end AnalyticSpace

end

end ComplexAnalytic
