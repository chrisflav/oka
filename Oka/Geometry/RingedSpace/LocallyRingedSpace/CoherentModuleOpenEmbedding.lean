/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Geometry.RingedSpace.LocallyRingedSpace.CoherentModuleSections
import Mathlib.Geometry.RingedSpace.OpenImmersion

/-!
# Transporting local generators and relations along open embeddings

The conditions `AlgebraicGeometry.LocallyRingedSpace.IsLocallyFinitelyGeneratedModule` and
`AlgebraicGeometry.LocallyRingedSpace.HasLocalModuleRelations`, which together imply coherence,
are conjunctions over the points of the space of a condition at that point
(`IsLocallyFinitelyGeneratedModuleAt`, `HasLocalModuleRelationsAt`).

Let `g : Z → Y` be an open embedding of the underlying spaces of two locally ringed spaces. Suppose
the sections of `𝒪_Y` over the image `g(O)` of an open `O ⊆ Z` are identified with the sections of
`𝒪_Z` over `O`, and the sections of a sheaf of `𝒪_Y`-modules `M` over `g(O)` with the sections of
a sheaf of `𝒪_Z`-modules `K` over `O`, compatibly with restrictions and module structures
(`AlgebraicGeometry.LocallyRingedSpace.ModuleChart`). Then the conditions at a point `z` for `K`
imply those at `g z` for `M` (`ModuleChart.isLocallyFinitelyGeneratedModuleAt`,
`ModuleChart.hasLocalModuleRelationsAt`). If `Y` is covered by such charts with `K` coherent,
`M` is coherent (`AlgebraicGeometry.LocallyRingedSpace.isCoherent_of_forall_moduleChart`).
-/

open CategoryTheory TopologicalSpace Opposite Topology

universe u

noncomputable section

namespace AlgebraicGeometry.LocallyRingedSpace

section At

variable {Y : LocallyRingedSpace.{u}} (M : SheafOfModules.{u} Y.ringSheaf)

/-- The condition of `IsLocallyFinitelyGeneratedModule` at the point `x`. -/
def IsLocallyFinitelyGeneratedModuleAt (x : Y) : Prop :=
  ∃ (W : Opens Y.toPresheafedSpace) (k : ℕ) (s : Fin k → M.val.obj (op W)), x ∈ W ∧
    ∀ (W' : Opens Y.toPresheafedSpace) (hW' : W' ≤ W) (t : M.val.obj (op W')), ∀ y ∈ W',
      ∃ (W'' : Opens Y.toPresheafedSpace) (hW'' : W'' ≤ W'), y ∈ W'' ∧
        ∃ c : Fin k → Y.presheaf.obj (op W''),
        sectRes M hW'' t = ∑ l, c l • sectRes M (hW''.trans hW') (s l)

/-- The condition of `HasLocalModuleRelations` at the point `x`. -/
def HasLocalModuleRelationsAt (x : Y) : Prop :=
  ∀ (V : Opens Y.toPresheafedSpace) (m : ℕ) (f : Fin m → M.val.obj (op V)), x ∈ V →
    ∃ (W : Opens Y.toPresheafedSpace) (hWV : W ≤ V) (k : ℕ)
      (g : Fin k → (Fin m → Y.presheaf.obj (op W))),
      x ∈ W ∧ (∀ l, ∑ i, g l i • sectRes M hWV (f i) = 0) ∧
      ∀ (W' : Opens Y.toPresheafedSpace) (hW' : W' ≤ W) (a : Fin m → Y.presheaf.obj (op W')),
        (∑ i, a i • sectRes M (hW'.trans hWV) (f i) = 0) → ∀ y ∈ W',
          ∃ (W'' : Opens Y.toPresheafedSpace) (hW'' : W'' ≤ W'), y ∈ W'' ∧
            ∃ c : Fin k → Y.presheaf.obj (op W''),
              ∀ i, Y.res hW'' (a i) = ∑ l, c l * Y.res (hW''.trans hW') (g l i)

lemma isLocallyFinitelyGeneratedModule_iff :
    IsLocallyFinitelyGeneratedModule M ↔ ∀ x, IsLocallyFinitelyGeneratedModuleAt M x :=
  Iff.rfl

lemma hasLocalModuleRelations_iff :
    HasLocalModuleRelations M ↔ ∀ x, HasLocalModuleRelationsAt M x :=
  ⟨fun h x V m f hx ↦ h V m f x hx, fun h V m f x hx ↦ h x V m f hx⟩

variable {M} in
/-- `HasLocalModuleRelationsAt` may be checked on the opens inside a neighbourhood of the point. -/
lemma hasLocalModuleRelationsAt_of_le {x : Y} (N : Opens Y.toPresheafedSpace) (hxN : x ∈ N)
    (h : ∀ (V : Opens Y.toPresheafedSpace), V ≤ N → ∀ (m : ℕ) (f : Fin m → M.val.obj (op V)),
      x ∈ V → ∃ (W : Opens Y.toPresheafedSpace) (hWV : W ≤ V) (k : ℕ)
        (g : Fin k → (Fin m → Y.presheaf.obj (op W))),
        x ∈ W ∧ (∀ l, ∑ i, g l i • sectRes M hWV (f i) = 0) ∧
        ∀ (W' : Opens Y.toPresheafedSpace) (hW' : W' ≤ W) (a : Fin m → Y.presheaf.obj (op W')),
          (∑ i, a i • sectRes M (hW'.trans hWV) (f i) = 0) → ∀ y ∈ W',
            ∃ (W'' : Opens Y.toPresheafedSpace) (hW'' : W'' ≤ W'), y ∈ W'' ∧
              ∃ c : Fin k → Y.presheaf.obj (op W''),
                ∀ i, Y.res hW'' (a i) = ∑ l, c l * Y.res (hW''.trans hW') (g l i)) :
    HasLocalModuleRelationsAt M x := by
  intro V m f hx
  obtain ⟨W, hWV, k, g, hxW, hrel, hcompl⟩ :=
    h (V ⊓ N) inf_le_right m (fun i ↦ sectRes M inf_le_left (f i)) ⟨hx, hxN⟩
  refine ⟨W, hWV.trans inf_le_left, k, g, hxW, fun l ↦ ?_, fun W' hW' a ha y hy ↦ ?_⟩
  · simpa only [sectRes_sectRes] using hrel l
  · exact hcompl W' hW' a (by simpa only [sectRes_sectRes] using ha) y hy

end At

/-! ### Charts -/

variable {Y Z : LocallyRingedSpace.{u}}

/-- **A chart for a pair of sheaves of modules**: an open embedding `g : Z → Y` together with
identifications of the sections of `𝒪_Y` and of `M` over `g(O)` with the sections of `𝒪_Z` and of
`K` over `O`, compatible with restrictions and module structures. -/
structure ModuleChart (M : SheafOfModules.{u} Y.ringSheaf) (K : SheafOfModules.{u} Z.ringSheaf)
    where
  /-- The underlying map. -/
  g : Z.toPresheafedSpace.carrier ⟶ Y.toPresheafedSpace.carrier
  /-- It is an open embedding. -/
  isOpenEmbedding : IsOpenEmbedding g
  /-- The identification of the sections of the structure sheaves. -/
  ψ (O : Opens Z.toPresheafedSpace) :
    Y.presheaf.obj (op (isOpenEmbedding.isOpenMap.functor.obj O)) →+* Z.presheaf.obj (op O)
  /-- `ψ` is bijective. -/
  bijective_ψ (O : Opens Z.toPresheafedSpace) : Function.Bijective (ψ O)
  /-- `ψ` commutes with restriction. -/
  ψ_res {O₁ O₂ : Opens Z.toPresheafedSpace} (h : O₁ ≤ O₂)
    (r : Y.presheaf.obj (op (isOpenEmbedding.isOpenMap.functor.obj O₂))) :
    ψ O₁ (Y.res (isOpenEmbedding.isOpenMap.functor.monotone h) r) = Z.res h (ψ O₂ r)
  /-- The identification of the sections of the sheaves of modules. -/
  φ (O : Opens Z.toPresheafedSpace) :
    M.val.obj (op (isOpenEmbedding.isOpenMap.functor.obj O)) →+ K.val.obj (op O)
  /-- `φ` is bijective. -/
  bijective_φ (O : Opens Z.toPresheafedSpace) : Function.Bijective (φ O)
  /-- `φ` commutes with restriction. -/
  φ_res {O₁ O₂ : Opens Z.toPresheafedSpace} (h : O₁ ≤ O₂)
    (s : M.val.obj (op (isOpenEmbedding.isOpenMap.functor.obj O₂))) :
    φ O₁ (sectRes M (isOpenEmbedding.isOpenMap.functor.monotone h) s) = sectRes K h (φ O₂ s)
  /-- `φ` is semilinear over `ψ`. -/
  φ_smul (O : Opens Z.toPresheafedSpace)
    (r : Y.presheaf.obj (op (isOpenEmbedding.isOpenMap.functor.obj O)))
    (s : M.val.obj (op (isOpenEmbedding.isOpenMap.functor.obj O))) :
    φ O (r • s) = ψ O r • φ O s

namespace ModuleChart

variable {M : SheafOfModules.{u} Y.ringSheaf} {K : SheafOfModules.{u} Z.ringSheaf}
  (C : ModuleChart M K)

/-- The image of an open of `Z`. -/
abbrev img (O : Opens Z.toPresheafedSpace) : Opens Y.toPresheafedSpace :=
  C.isOpenEmbedding.isOpenMap.functor.obj O

/-- The preimage of an open of `Y`. -/
def pre (O : Opens Y.toPresheafedSpace) : Opens Z.toPresheafedSpace :=
  ⟨C.g ⁻¹' O, O.isOpen.preimage C.isOpenEmbedding.continuous⟩

lemma img_mono {O₁ O₂ : Opens Z.toPresheafedSpace} (h : O₁ ≤ O₂) : C.img O₁ ≤ C.img O₂ :=
  C.isOpenEmbedding.isOpenMap.functor.monotone h

lemma mem_img (z : Z) (O : Opens Z.toPresheafedSpace) : C.g z ∈ C.img O ↔ z ∈ O :=
  ⟨fun ⟨_, hz', h⟩ ↦ C.isOpenEmbedding.injective h ▸ hz', fun h ↦ ⟨z, h, rfl⟩⟩

lemma pre_img (O : Opens Z.toPresheafedSpace) : C.pre (C.img O) = O :=
  Opens.ext (Set.ext fun z ↦ C.mem_img z O)

lemma img_pre_le (O : Opens Y.toPresheafedSpace) : C.img (C.pre O) ≤ O := by
  rintro _ ⟨z, hz, rfl⟩
  exact hz

lemma img_pre {O : Opens Y.toPresheafedSpace} (h : O ≤ C.img ⊤) : C.img (C.pre O) = O := by
  refine le_antisymm (C.img_pre_le O) fun y hy ↦ ?_
  obtain ⟨z, -, rfl⟩ := h hy
  exact ⟨z, hy, rfl⟩

lemma pre_mono {O₁ O₂ : Opens Y.toPresheafedSpace} (h : O₁ ≤ O₂) : C.pre O₁ ≤ C.pre O₂ :=
  fun _ hz ↦ h hz

lemma pre_le_of_le_img {O : Opens Y.toPresheafedSpace} {O' : Opens Z.toPresheafedSpace}
    (h : O ≤ C.img O') : C.pre O ≤ O' := by
  intro z hz
  exact (C.mem_img z O').1 (h hz)

lemma φ_injective (O : Opens Z.toPresheafedSpace) : Function.Injective (C.φ O) :=
  (C.bijective_φ O).1

lemma ψ_injective (O : Opens Z.toPresheafedSpace) : Function.Injective (C.ψ O) :=
  (C.bijective_ψ O).1

/-- The inverse of `ψ`. -/
def ψInv (O : Opens Z.toPresheafedSpace) (r : Z.presheaf.obj (op O)) :
    Y.presheaf.obj (op (C.img O)) :=
  (Equiv.ofBijective _ (C.bijective_ψ O)).symm r

@[simp]
lemma ψ_ψInv (O : Opens Z.toPresheafedSpace) (r : Z.presheaf.obj (op O)) : C.ψ O (C.ψInv O r) = r :=
  (Equiv.ofBijective _ (C.bijective_ψ O)).apply_symm_apply r

/-- The inverse of `φ`. -/
def φInv (O : Opens Z.toPresheafedSpace) (s : K.val.obj (op O)) : M.val.obj (op (C.img O)) :=
  (Equiv.ofBijective _ (C.bijective_φ O)).symm s

@[simp]
lemma φ_φInv (O : Opens Z.toPresheafedSpace) (s : K.val.obj (op O)) : C.φ O (C.φInv O s) = s :=
  (Equiv.ofBijective _ (C.bijective_φ O)).apply_symm_apply s

lemma φ_sum (O : Opens Z.toPresheafedSpace) {κ : Type*} (t : Finset κ)
    (u : κ → M.val.obj (op (C.img O))) :
    C.φ O (∑ i ∈ t, u i) = ∑ i ∈ t, C.φ O (u i) :=
  map_sum (C.φ O) u t

lemma ψ_sum (O : Opens Z.toPresheafedSpace) {κ : Type*} (t : Finset κ)
    (u : κ → Y.presheaf.obj (op (C.img O))) :
    C.ψ O (∑ i ∈ t, u i) = ∑ i ∈ t, C.ψ O (u i) :=
  map_sum (C.ψ O) u t

/-- `φ` on restrictions of a section over an open of `Y`. -/
lemma φ_sectRes_sectRes {O : Opens Z.toPresheafedSpace} {W : Opens Y.toPresheafedSpace}
    (hW : C.img O ≤ W) {O' : Opens Z.toPresheafedSpace} (h : O ≤ O') (hW' : C.img O' ≤ W)
    (s : M.val.obj (op W)) :
    C.φ O (sectRes M hW s) = sectRes K h (C.φ O' (sectRes M hW' s)) := by
  rw [← C.φ_res h, sectRes_sectRes]

/-- `ψ` on restrictions of a section over an open of `Y`. -/
lemma ψ_res_res {O : Opens Z.toPresheafedSpace} {W : Opens Y.toPresheafedSpace}
    (hW : C.img O ≤ W) {O' : Opens Z.toPresheafedSpace} (h : O ≤ O') (hW' : C.img O' ≤ W)
    (r : Y.presheaf.obj (op W)) :
    C.ψ O (Y.res hW r) = Z.res h (C.ψ O' (Y.res hW' r)) := by
  rw [← C.ψ_res h, res_res]

/-- **Local generators transport along a chart.** -/
theorem isLocallyFinitelyGeneratedModuleAt {z : Z}
    (hK : IsLocallyFinitelyGeneratedModuleAt K z) :
    IsLocallyFinitelyGeneratedModuleAt M (C.g z) := by
  obtain ⟨W', k, s, hzW', hgen⟩ := hK
  refine ⟨C.img W', k, fun l ↦ C.φInv W' (s l), (C.mem_img z W').2 hzW',
    fun W₁ hW₁ t y hy ↦ ?_⟩
  have hW₁r : W₁ ≤ C.img ⊤ := hW₁.trans (C.img_mono le_top)
  have hW₁e : C.img (C.pre W₁) = W₁ := C.img_pre hW₁r
  obtain ⟨z', -, rfl⟩ := hW₁r hy
  have hpre : C.pre W₁ ≤ W' := C.pre_le_of_le_img hW₁
  obtain ⟨W₂', hW₂', hz'W₂', c', hc'⟩ := hgen (C.pre W₁) hpre
    (C.φ (C.pre W₁) (sectRes M hW₁e.le t)) z' hy
  have hW₂ : C.img W₂' ≤ W₁ := (C.img_mono hW₂').trans hW₁e.le
  refine ⟨C.img W₂', hW₂, (C.mem_img z' W₂').2 hz'W₂', fun l ↦ C.ψInv W₂' (c' l), ?_⟩
  apply C.φ_injective W₂'
  rw [C.φ_sectRes_sectRes hW₂ hW₂' hW₁e.le, hc', C.φ_sum]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [C.φ_smul, ψ_ψInv, C.φ_res (hW₂'.trans hpre), φ_φInv]

/-- **Local relations transport along a chart.** -/
theorem hasLocalModuleRelationsAt {z : Z} (hK : HasLocalModuleRelationsAt K z) :
    HasLocalModuleRelationsAt M (C.g z) := by
  refine hasLocalModuleRelationsAt_of_le (C.img ⊤) ((C.mem_img z ⊤).2 trivial)
    fun V hV m f hzV ↦ ?_
  have hVe : C.img (C.pre V) = V := C.img_pre hV
  let f' : Fin m → K.val.obj (op (C.pre V)) := fun i ↦ C.φ (C.pre V) (sectRes M hVe.le (f i))
  obtain ⟨W', hW'V, k, g', hzW', hrel', hcompl'⟩ := hK (C.pre V) m f' hzV
  have hWV : C.img W' ≤ V := (C.img_mono hW'V).trans hVe.le
  refine ⟨C.img W', hWV, k, fun l i ↦ C.ψInv W' (g' l i), (C.mem_img z W').2 hzW',
    fun l ↦ ?_, fun W₁ hW₁ a ha y hy ↦ ?_⟩
  · apply C.φ_injective W'
    rw [C.φ_sum, map_zero, ← hrel' l]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [C.φ_smul, ψ_ψInv, C.φ_sectRes_sectRes hWV hW'V hVe.le]
  · have hW₁r : W₁ ≤ C.img ⊤ := hW₁.trans (C.img_mono le_top)
    have hW₁e : C.img (C.pre W₁) = W₁ := C.img_pre hW₁r
    obtain ⟨z', -, rfl⟩ := hW₁r hy
    have hpre : C.pre W₁ ≤ W' := C.pre_le_of_le_img hW₁
    let a' : Fin m → Z.presheaf.obj (op (C.pre W₁)) := fun i ↦ C.ψ (C.pre W₁) (Y.res hW₁e.le (a i))
    have ha' : ∑ i, a' i • sectRes K (hpre.trans hW'V) (f' i) = 0 := by
      have := congrArg (fun s ↦ C.φ (C.pre W₁) (sectRes M hW₁e.le s)) ha
      simp only [sectRes_sum, sectRes_smul, C.φ_sum, sectRes_zero, map_zero] at this
      rw [← this]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [C.φ_smul, sectRes_sectRes, C.φ_sectRes_sectRes _ (hpre.trans hW'V) hVe.le]
    obtain ⟨W₂', hW₂', hz'W₂', c', hc'⟩ := hcompl' (C.pre W₁) hpre a' ha' z' hy
    have hW₂ : C.img W₂' ≤ W₁ := (C.img_mono hW₂').trans hW₁e.le
    refine ⟨C.img W₂', hW₂, (C.mem_img z' W₂').2 hz'W₂', fun l ↦ C.ψInv W₂' (c' l),
      fun i ↦ ?_⟩
    apply C.ψ_injective W₂'
    rw [C.ψ_res_res hW₂ hW₂' hW₁e.le, hc', C.ψ_sum]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [map_mul, ψ_ψInv, C.ψ_res (hW₂'.trans hpre), ψ_ψInv]

end ModuleChart

section OpenImmersion

variable (g : Z ⟶ Y) [IsOpenImmersion g]

/-- The image of an open under an open immersion. -/
abbrev openImmersionImg (O : Opens Z.toPresheafedSpace) : Opens Y.toPresheafedSpace :=
  (PresheafedSpace.IsOpenImmersion.base_open (f := g.toHom)).isOpenMap.functor.obj O

lemma le_preimage_openImmersionImg (O : Opens Z.toPresheafedSpace) :
    O ≤ (Opens.map g.base).obj (openImmersionImg g O) :=
  fun z hz ↦ ⟨z, hz, rfl⟩

lemma preimage_openImmersionImg_le (O : Opens Z.toPresheafedSpace) :
    (Opens.map g.base).obj (openImmersionImg g O) ≤ O := by
  rintro z ⟨z', hz', h⟩
  rwa [(PresheafedSpace.IsOpenImmersion.base_open (f := g.toHom)).injective h] at hz'

/-- The identification `𝒪_Y(g(O)) ≅ 𝒪_Z(O)` induced by an open immersion `g : Z ⟶ Y`. -/
def openImmersionψ (O : Opens Z.toPresheafedSpace) :
    Y.presheaf.obj (op (openImmersionImg g O)) →+* Z.presheaf.obj (op O) :=
  (Z.presheaf.map (homOfLE (le_preimage_openImmersionImg g O)).op).hom.comp
    (g.c.app (op (openImmersionImg g O))).hom

lemma bijective_openImmersionψ (O : Opens Z.toPresheafedSpace) :
    Function.Bijective (openImmersionψ g O) := by
  haveI : IsIso (homOfLE (le_preimage_openImmersionImg g O)) := homOfLE_isIso_of_eq _
    (le_antisymm (le_preimage_openImmersionImg g O) (preimage_openImmersionImg_le g O))
  rw [openImmersionψ, RingHom.coe_comp]
  exact (ConcreteCategory.bijective_of_isIso _).comp (ConcreteCategory.bijective_of_isIso _)

lemma openImmersionψ_res {O₁ O₂ : Opens Z.toPresheafedSpace} (h : O₁ ≤ O₂)
    (r : Y.presheaf.obj (op (openImmersionImg g O₂))) :
    openImmersionψ g O₁ (Y.res ((PresheafedSpace.IsOpenImmersion.base_open
      (f := g.toHom)).isOpenMap.functor.monotone h) r) = Z.res h (openImmersionψ g O₂ r) := by
  simp only [openImmersionψ, RingHom.coe_comp, Function.comp_apply]
  change Z.res _ (g.c.app _ (Y.res _ r)) = Z.res h (Z.res _ (g.c.app _ r))
  rw [c_app_res, res_res, res_res]

variable {M : SheafOfModules.{u} Y.ringSheaf} {K : SheafOfModules.{u} Z.ringSheaf}

/-- The chart given by an open immersion `g : Z ⟶ Y` and an identification of the sections of `M`
over `g(O)` with the sections of `K` over `O`. -/
def ModuleChart.ofIsOpenImmersion
    (φ : ∀ O : Opens Z.toPresheafedSpace, M.val.obj (op (openImmersionImg g O)) →+ K.val.obj (op O))
    (bijective_φ : ∀ O, Function.Bijective (φ O))
    (φ_res : ∀ {O₁ O₂ : Opens Z.toPresheafedSpace} (h : O₁ ≤ O₂)
      (s : M.val.obj (op (openImmersionImg g O₂))),
      φ O₁ (sectRes M ((PresheafedSpace.IsOpenImmersion.base_open
        (f := g.toHom)).isOpenMap.functor.monotone h) s) = sectRes K h (φ O₂ s))
    (φ_smul : ∀ (O : Opens Z.toPresheafedSpace) (r : Y.presheaf.obj (op (openImmersionImg g O)))
      (s : M.val.obj (op (openImmersionImg g O))), φ O (r • s) = openImmersionψ g O r • φ O s) :
    ModuleChart M K where
  g := g.base
  isOpenEmbedding := PresheafedSpace.IsOpenImmersion.base_open (f := g.toHom)
  ψ := openImmersionψ g
  bijective_ψ := bijective_openImmersionψ g
  ψ_res := openImmersionψ_res g
  φ := φ
  bijective_φ := bijective_φ
  φ_res := φ_res
  φ_smul := φ_smul

@[simp]
lemma ModuleChart.ofIsOpenImmersion_g (φ bijective_φ φ_res φ_smul) :
    (ModuleChart.ofIsOpenImmersion (M := M) (K := K) g φ bijective_φ φ_res φ_smul).g = g.base :=
  rfl

end OpenImmersion

/-- **Coherence from coherent charts**: if every point of `Y` is the image of a point under a
chart `M ↔ K` with `K` coherent, then `M` is coherent. -/
theorem isCoherent_of_forall_moduleChart (M : SheafOfModules.{u} Y.ringSheaf)
    (h : ∀ y : Y, ∃ (Z : LocallyRingedSpace.{u}) (K : SheafOfModules.{u} Z.ringSheaf)
      (_ : K.IsCoherent) (C : ModuleChart M K) (z : Z), C.g z = y) :
    M.IsCoherent := by
  refine isCoherent_of_hasLocalModuleRelations M (fun y ↦ ?_)
    ((hasLocalModuleRelations_iff M).2 fun y ↦ ?_)
  · obtain ⟨Z, K, hK, C, z, rfl⟩ := h y
    exact C.isLocallyFinitelyGeneratedModuleAt
      (isLocallyFinitelyGeneratedModule_of_isFiniteType K z)
  · obtain ⟨Z, K, hK, C, z, rfl⟩ := h y
    exact C.hasLocalModuleRelationsAt
      ((hasLocalModuleRelations_iff K).1 (hasLocalModuleRelations_of_isCoherent K) z)

/-- **Coherence is preserved by pushing forward along an isomorphism.** -/
theorem isCoherent_pushforward_of_isIso {Z : LocallyRingedSpace.{u}} (g : Z ⟶ Y) [IsIso g]
    (K : SheafOfModules.{u} Z.ringSheaf) [K.IsCoherent] :
    ((SheafOfModules.pushforward.{u} g.toRingSheafHom).obj K).IsCoherent := by
  refine isCoherent_of_forall_moduleChart _ fun y ↦ ?_
  obtain ⟨z, rfl⟩ := (homeoOfIso (asIso g)).surjective y
  have hself (O : Opens Z.toPresheafedSpace) (s : K.val.obj (op O)) : sectRes K le_rfl s = s := by
    change (K.val.presheaf.map (𝟙 (op O))).hom s = s
    simp only [CategoryTheory.Functor.map_id]
    rfl
  have hbij (O : Opens Z.toPresheafedSpace) :
      Function.Bijective (K.val.map (homOfLE (le_preimage_openImmersionImg g O)).op) := by
    refine Function.bijective_iff_has_inverse.2
      ⟨fun (s : K.val.obj (op O)) ↦ sectRes K (preimage_openImmersionImg_le g O) s,
        fun s ↦ ?_, fun s ↦ ?_⟩
    · change sectRes K _ (sectRes K _ s) = s
      rw [sectRes_sectRes, hself]
    · change sectRes K (le_preimage_openImmersionImg g O) (sectRes K
        (preimage_openImmersionImg_le g O) (show K.val.obj (op O) from s)) =
        (show K.val.obj (op O) from s)
      rw [sectRes_sectRes, hself]
  refine ⟨Z, K, inferInstance, ModuleChart.ofIsOpenImmersion g
    (fun O ↦ (K.val.map (homOfLE (le_preimage_openImmersionImg g O)).op).hom.toAddMonoidHom)
    hbij (fun {O₁ O₂} h s ↦ ?_) (fun O r s ↦ ?_), z, rfl⟩
  · change sectRes K _ (sectRes K _ s) = sectRes K h (sectRes K _ s)
    rw [sectRes_sectRes, sectRes_sectRes]
  · change sectRes K _ ((show Z.presheaf.obj (op ((Opens.map g.base).obj (openImmersionImg g O)))
        from g.c.app _ r) • (show K.val.obj (op ((Opens.map g.base).obj (openImmersionImg g O)))
        from s)) = _
    rw [sectRes_smul]
    rfl

end AlgebraicGeometry.LocallyRingedSpace
