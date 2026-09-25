/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.AnalyticSpace.BoundedPushforward
import Oka.AnalyticSpace.CoveringMap
import Oka.Analytification.RET.ES.KummerSections
import Oka.Analytification.GAGA.CousinCoordinate

/-!
# Bounded sections of a finite étale cover of the complement of a hypersurface

Let `N° ⊆ N` be opens of `ℂⁿ` and `p : W ⟶ N°` a finite étale cover. The sections of `p_* 𝒪_W`
over `V ⊆ N`, i.e. the sections of `𝒪_W` over `p⁻¹(V ∩ N°)`, which are bounded near every point
of `V ∖ N°` form a sheaf `𝒜` of `𝒪_N`-algebras on `N`
(`ComplexAnalytic.BoundedSections.boundedModule`, `ComplexAnalytic.BoundedSections.boundedSheaf`),
which is `p_* 𝒪_W` over `N°` (`ComplexAnalytic.BoundedSections.boundedSubring_eq_top`). This
generalises `Oka/Analytification/RET/ES/KummerExtensionSheaf.lean`.

This file also provides the local analysis of `W` on which the study of `𝒜` rests: `W` is
locally isomorphic to opens of `ℂⁿ`, sections of `𝒪_W` near a point are holomorphic functions of
the point below (`ComplexAnalytic.BoundedSections.exists_sheet`) and conversely
(`ComplexAnalytic.BoundedSections.exists_eval_eq_of_differentiableAt`), and if `W` is Hausdorff,
then near every point of `N°` the cover is trivial
(`ComplexAnalytic.BoundedSections.exists_local_sheets`).

## Main definitions

- `ComplexAnalytic.BoundedSections.proj h₀ W`: the composite `W ⟶ N° ⟶ N`, and
  `ComplexAnalytic.BoundedSections.pullback h₀ W V : 𝒪_N(V) → 𝒪_W(p⁻¹(V ∩ N°))`.
- `ComplexAnalytic.BoundedSections.boundedModule h₀ W`: `𝒜` as a sheaf of `𝒪_N`-modules.
- `ComplexAnalytic.BoundedSections.boundedSubring h₀ W V`: the ring `𝒜(V)`.
- `ComplexAnalytic.BoundedSections.boundedSheaf h₀ W`: `𝒜` as a sheaf of rings, with structure
  morphism `ComplexAnalytic.BoundedSections.boundedAlgebraHom h₀ W : 𝒪_N ⟶ 𝒜`.
- `ComplexAnalytic.AnalyticSpace.evalFun a`: the values of a section, as a function.

## Main results

- `ComplexAnalytic.AnalyticSpace.isLocallyOpenInAffine_of_isLocalIso`: a space with a local
  isomorphism to an open of `ℂⁿ` is locally isomorphic to opens of `ℂⁿ`.
- `ComplexAnalytic.BoundedSections.isSheaf_boundedPresheaf`: `𝒜` is a sheaf of rings.
- `ComplexAnalytic.BoundedSections.exists_local_sheets`: local triviality of `W` over `N°`.
- `ComplexAnalytic.BoundedSections.differentiableAt_evalFun_comp`: values of sections along
  continuous local sections of `p` are holomorphic.
-/

open CategoryTheory Opposite AlgebraicGeometry Topology TopologicalSpace Filter

universe u

namespace ComplexAnalytic.AnalyticSpace

noncomputable section

/-- The inclusion of a smaller open subspace of `ℂⁿ` into a larger one does not move points. -/
lemma coe_base_restrictLE {n : ℕ} {V V' : (AnalyticSpace.complexAffineSpace.{u} n).Opens}
    (h : V ≤ V') (x : (AnalyticSpace.complexAffineSpace.{u} n).restrict V) :
    (((AnalyticSpace.complexAffineSpace.{u} n).restrictLE h).toLRSHom.base x).1 = x.1 := by
  have := congrArg (fun f ↦ f.toLRSHom.base x)
    ((AnalyticSpace.complexAffineSpace.{u} n).restrictLE_fac h)
  exact this

theorem isLocallyOpenInAffine_of_isLocalIso {Z : AnalyticSpace.{u}} {n : ℕ}
    {U : (AnalyticSpace.complexAffineSpace.{u} n).Opens}
    (φ : Z ⟶ (AnalyticSpace.complexAffineSpace.{u} n).restrict U) [IsLocalIso φ] :
    IsLocallyOpenInAffine Z := by
  intro z
  obtain ⟨e, hze, he⟩ := IsLocalIso.isLocalHomeomorph (f := φ) z
  let O : Z.Opens := ⟨e.source, e.open_source⟩
  let ψ := Z.ofRestrict O ≫ φ
  have hψ : ∀ x, ψ.toLRSHom.base x = φ.toLRSHom.base x.1 := fun _ ↦ rfl
  have hinj : Function.Injective ψ.toLRSHom.base := by
    intro x y hxy
    rw [hψ, hψ, he] at hxy
    exact Subtype.ext (e.injOn x.2 y.2 hxy)
  let V : ((AnalyticSpace.complexAffineSpace.{u} n).restrict U).Opens :=
    ⟨Set.range ψ.toLRSHom.base, (IsLocalIso.isLocalHomeomorph (f := ψ)).isOpenMap.isOpen_range⟩
  let ψ' := liftRestrict ψ V subset_rfl
  have hψ' : ψ' ≫ ofRestrict _ V = ψ := liftRestrict_fac ψ V subset_rfl
  haveI : IsLocalIso (ψ' ≫ ofRestrict _ V) := by rw [hψ']; infer_instance
  haveI : IsLocalIso ψ' := isLocalIso_of_comp ψ' (ofRestrict _ V)
  have hbase : ∀ x, (ψ'.toLRSHom.base x).1 = ψ.toLRSHom.base x := fun x ↦
    congrArg (fun f ↦ f.toLRSHom.base x) hψ'
  haveI : IsIso ψ' := isIso_of_isLocalIso_of_bijective ψ' ⟨fun x y hxy ↦ hinj (by
    rw [← hbase, ← hbase, hxy]), fun y ↦ by
      obtain ⟨x, hx⟩ := y.2
      exact ⟨x, Subtype.ext ((hbase x).trans hx)⟩⟩
  let V'' : (AnalyticSpace.complexAffineSpace.{u} n).Opens :=
    U.isOpenEmbedding.isOpenMap.functor.obj V
  have hV''U : V'' ≤ U := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  let χ₀ := (AnalyticSpace.complexAffineSpace.{u} n).restrictLE hV''U
  have hχ₀ : Set.range χ₀.toLRSHom.base ⊆ (V : Set _) := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨y, hy, hyx⟩ := x.2
    have : χ₀.toLRSHom.base x = y := Subtype.ext ((coe_base_restrictLE hV''U x).trans hyx.symm)
    rw [this]
    exact hy
  let χ := liftRestrict χ₀ V hχ₀
  have hχ : χ ≫ ofRestrict _ V = χ₀ := liftRestrict_fac χ₀ V hχ₀
  haveI : IsLocalIso (χ₀ ≫ ofRestrict _ U) := by
    rw [restrictLE_fac]; infer_instance
  haveI : IsLocalIso χ₀ := isLocalIso_of_comp χ₀ (ofRestrict _ U)
  haveI : IsLocalIso (χ ≫ ofRestrict _ V) := by rw [hχ]; infer_instance
  haveI : IsLocalIso χ := isLocalIso_of_comp χ (ofRestrict _ V)
  haveI : IsLocalIso (inv ψ') := isLocalIso_of_isIso _
  have hz : ψ.toLRSHom.base ⟨z, hze⟩ ∈ V := ⟨_, rfl⟩
  refine ⟨n, V'', χ ≫ inv ψ' ≫ Z.ofRestrict O, ⟨_, ⟨_, hz, rfl⟩⟩, inferInstance, ?_⟩
  have h₁ : χ.toLRSHom.base ⟨_, ⟨_, hz, rfl⟩⟩ = ψ'.toLRSHom.base ⟨z, hze⟩ := by
    refine Subtype.ext (Subtype.ext ?_)
    rw [hbase]
    exact (congrArg (fun f ↦ (f.toLRSHom.base ⟨_, ⟨_, hz, rfl⟩⟩).1) hχ).trans
      (coe_base_restrictLE hV''U _)
  have h₂ : (inv ψ').toLRSHom.base (ψ'.toLRSHom.base ⟨z, hze⟩) = ⟨z, hze⟩ :=
    congrArg (fun f ↦ f.toLRSHom.base ⟨z, hze⟩) (IsIso.hom_inv_id ψ')
  change (Z.ofRestrict O).toLRSHom.base ((inv ψ').toLRSHom.base
    (χ.toLRSHom.base ⟨_, ⟨_, hz, rfl⟩⟩)) = z
  rw [h₁, h₂]
  rfl

/-- **Sections over an injective local isomorphism into an open of `ℂⁿ` are holomorphic
functions**: their values are the values of a function holomorphic near the image. -/
theorem exists_eval_eq_of_injective {n : ℕ} {Z : AnalyticSpace.{u}}
    {U : (AnalyticSpace.complexAffineSpace.{u} n).Opens}
    (φ : Z ⟶ (AnalyticSpace.complexAffineSpace.{u} n).restrict U) [IsLocalIso φ]
    (hinj : Function.Injective φ.toLRSHom.base) {O : Z.Opens} (t : Z.presheaf.obj (op O)) :
    ∃ F : (ULift.{u} (Fin n) → ℂ) → ℂ, (∀ z ∈ O, DifferentiableAt ℂ F (φ.toLRSHom.base z).1) ∧
      ∀ z (hz : z ∈ O), Z.eval z hz t = F (φ.toLRSHom.base z).1 := by
  obtain ⟨σ, hσ⟩ := exists_eval_eq_image φ hinj t
  let V : ((AnalyticSpace.complexAffineSpace.{u} n).restrict U).Opens :=
    ⟨φ.toLRSHom.base '' O, (IsLocalIso.isLocalHomeomorph (f := φ)).isOpenMap _ O.isOpen⟩
  let V' : TopologicalSpace.Opens (ULift.{u} (Fin n) → ℂ) :=
    U.isOpenEmbedding.isOpenMap.functor.obj V
  refine ⟨OkaRing.toGlobalFun V' σ, fun z hz ↦ ?_, fun z hz ↦ ?_⟩
  · exact (OkaRing.analyticAt_toGlobalFun (U := V') σ ⟨_, ⟨z, hz, rfl⟩, rfl⟩).differentiableAt
  · rw [← hσ z hz, eval_restrict_complexAffineSpace_of]
    exact (OkaRing.toGlobalFun_apply (U := V') σ ⟨_, ⟨z, hz, rfl⟩, rfl⟩).symm

open Classical in
/-- The values of a section of a complex analytic space, as a function on the whole space (zero
outside the domain of the section). -/
def evalFun {Z : AnalyticSpace.{u}} {O : Z.Opens} (a : Z.presheaf.obj (op O)) (z : Z) : ℂ :=
  if h : z ∈ O then Z.eval z h a else 0

open Classical in
lemma evalFun_of_mem {Z : AnalyticSpace.{u}} {O : Z.Opens} (a : Z.presheaf.obj (op O)) {z : Z}
    (h : z ∈ O) : evalFun a z = Z.eval z h a := by
  rw [evalFun, dif_pos h]

/-- The values of a section are continuous on its domain. -/
lemma continuousOn_evalFun {Z : AnalyticSpace.{u}} {O : Z.Opens} (a : Z.presheaf.obj (op O)) :
    ContinuousOn (evalFun a) O := by
  rw [continuousOn_iff_continuous_restrict]
  have : (O : Set Z).restrict (evalFun a) = fun z : O ↦ Z.eval z.1 z.2 a :=
    funext fun z ↦ evalFun_of_mem a z.2
  rw [this]
  exact Z.continuous_eval a

end

end ComplexAnalytic.AnalyticSpace

namespace ComplexAnalytic.BoundedSections

open AnalyticSpace

noncomputable section

variable {n : ℕ}


/-- The points of `ℂⁿ`. -/
abbrev Cn (n : ℕ) : Type u := ULift.{u} (Fin n) → ℂ

/-- The open subspace `N` of `ℂⁿ`. -/
abbrev space (N : (AnalyticSpace.complexAffineSpace.{u} n).Opens) : AnalyticSpace.{u} :=
  (AnalyticSpace.complexAffineSpace.{u} n).restrict N

variable {N N₀ : (AnalyticSpace.complexAffineSpace.{u} n).Opens}

/-- The open subset of `ℂⁿ` underlying an open subset of `N`. -/
def img (V : (space N).Opens) : TopologicalSpace.Opens (Cn.{u} n) :=
  N.isOpenEmbedding.isOpenMap.functor.obj V

lemma mem_img_iff {V : (space N).Opens} {x : (Cn.{u} n)} :
    x ∈ img V ↔ ∃ hx : x ∈ N, (⟨x, hx⟩ : space N) ∈ V := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, h⟩
    exact ⟨_, h, rfl⟩

lemma img_mono {V V' : (space N).Opens} (h : V' ≤ V) : img V' ≤ img V :=
  Set.image_mono h

lemma img_le (V : (space N).Opens) : ∀ x ∈ img V, x ∈ N := by
  rintro _ ⟨y, -, rfl⟩
  exact y.2

variable (h₀ : N₀ ≤ N) (W : FiniteEtaleOver (space N₀))

/-- The structure morphism `p : W ⟶ N°`. -/
def cov : W.left ⟶ space N₀ :=
  W.hom

instance : IsFiniteEtale (cov W) :=
  W.prop

/-- The composite `W ⟶ N° ⟶ N`. -/
def proj : W.left ⟶ space N :=
  cov W ≫ (AnalyticSpace.complexAffineSpace.{u} n).restrictLE h₀

/-- The point of `ℂⁿ` below a point of `W`. -/
def pt (w : W.left) : (Cn.{u} n) :=
  ((cov W).toLRSHom.base w).1

lemma pt_mem (w : W.left) : pt W w ∈ N₀ :=
  ((cov W).toLRSHom.base w).2

lemma coe_proj_base (w : W.left) : ((proj h₀ W).toLRSHom.base w).1 = pt W w :=
  congrArg (fun f ↦ f.toLRSHom.base ((cov W).toLRSHom.base w))
    ((AnalyticSpace.complexAffineSpace.{u} n).restrictLE_fac h₀)

lemma continuous_pt : Continuous (pt W) :=
  continuous_subtype_val.comp (cov W).toLRSHom.base.hom.continuous

lemma isOpenMap_pt : IsOpenMap (pt W) :=
  N₀.isOpenEmbedding.isOpenMap.comp (IsLocalIso.isLocalHomeomorph (f := cov W)).isOpenMap

/-- The open `p⁻¹(V ∩ N°)` of `W`. -/
abbrev preim (V : (space N).Opens) : W.left.Opens :=
  (Opens.map (proj h₀ W).toLRSHom.base).obj V

lemma mem_preim_iff {V : (space N).Opens} {w : W.left} :
    w ∈ preim h₀ W V ↔ pt W w ∈ img V := by
  have h : (proj h₀ W).toLRSHom.base w = ⟨pt W w, h₀ (pt_mem W w)⟩ :=
    Subtype.ext (coe_proj_base h₀ W w)
  change (proj h₀ W).toLRSHom.base w ∈ V ↔ _
  rw [h, mem_img_iff]
  exact ⟨fun hw ↦ ⟨_, hw⟩, fun ⟨_, hw⟩ ↦ hw⟩

lemma preim_mono {V V' : (space N).Opens} (h : V' ≤ V) : preim h₀ W V' ≤ preim h₀ W V :=
  (Opens.map _).monotone h

variable (N) in
/-- The complement `D = N ∖ N°`, as a subset of `N`. -/
def removedSet (N₀ : (AnalyticSpace.complexAffineSpace.{u} n).Opens) : Set (space N) :=
  {y | y.1 ∉ N₀}

/-- **The sheaf `𝒜` of bounded sections**: the sections of `p_* 𝒪_W` which are bounded near
`N ∖ N°`, as a sheaf of `𝒪_N`-modules. -/
abbrev boundedModule : SheafOfModules.{u} (space N).ringSheaf :=
  boundedPushforward (proj h₀ W) (removedSet N N₀)

/-- `W` is locally isomorphic to open subspaces of `ℂⁿ`. -/
theorem isLocallyOpenInAffine_left : IsLocallyOpenInAffine W.left :=
  isLocallyOpenInAffine_of_isLocalIso (cov W)

/-- **Sheets of `W`**: every point of `W` has a neighbourhood `O` on which `p` is injective, such
that every section of `𝒪_W` over an open inside `O` is a holomorphic function of the point
below. -/
theorem exists_sheet (w : W.left) : ∃ O : W.left.Opens, w ∈ O ∧ Set.InjOn (pt W) (O : Set W.left) ∧
    ∀ {O' : W.left.Opens} (_ : O' ≤ O) (a : W.left.presheaf.obj (op O')),
      ∃ F : Cn.{u} n → ℂ, (∀ w' ∈ O', DifferentiableAt ℂ F (pt W w')) ∧
        ∀ w' (hw' : w' ∈ O'), W.left.eval w' hw' a = F (pt W w') := by
  obtain ⟨e, hwe, he⟩ := IsLocalIso.isLocalHomeomorph (f := cov W) w
  let O : W.left.Opens := ⟨e.source, e.open_source⟩
  have hinjO : Set.InjOn (cov W).toLRSHom.base (O : Set W.left) := by
    intro x hx y hy hxy
    rw [he] at hxy
    exact e.injOn hx hy hxy
  refine ⟨O, hwe, fun x hx y hy hxy ↦ hinjO hx hy (Subtype.ext hxy), fun {O'} hO' a ↦ ?_⟩
  let φ := W.left.ofRestrict O ≫ cov W
  have hinj : Function.Injective φ.toLRSHom.base := fun x y hxy ↦
    Subtype.ext (hinjO x.2 y.2 hxy)
  obtain ⟨F, hFd, hF⟩ := exists_eval_eq_of_injective φ hinj
    ((W.left.ofRestrict O).toLRSHom.c.app (op O') a)
  refine ⟨F, fun w' hw' ↦ hFd ⟨w', hO' hw'⟩ hw', fun w' hw' ↦ ?_⟩
  exact (eval_c_app _ (W.left.ofRestrict O).isCLinear ⟨w', hO' hw'⟩ hw' a).symm.trans
    (hF ⟨w', hO' hw'⟩ hw')

/-- **Holomorphic functions give sections**: a function holomorphic at the points below an
open `O` of `W` is the value of a section of `𝒪_W` over `O`. -/
theorem exists_eval_eq_of_differentiableAt {O : W.left.Opens} (F : Cn.{u} n → ℂ)
    (hF : ∀ w ∈ O, DifferentiableAt ℂ F (pt W w)) :
    ∃ a : W.left.presheaf.obj (op O), ∀ w (hw : w ∈ O), W.left.eval w hw a = F (pt W w) := by
  let V : (space N₀).Opens := ⟨(cov W).toLRSHom.base '' (O : Set W.left),
    (IsLocalIso.isLocalHomeomorph (f := cov W)).isOpenMap _ O.isOpen⟩
  let G : TopologicalSpace.Opens (Cn.{u} n) := N₀.isOpenEmbedding.isOpenMap.functor.obj V
  have hG : DifferentiableOn ℂ F G := by
    rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    exact (hF w hw).differentiableWithinAt
  let σ : (space N₀).presheaf.obj (op V) := OkaRing.ofDifferentiableOn F hG
  have hOV : O ≤ (Opens.map (cov W).toLRSHom.base).obj V := fun w hw ↦ ⟨w, hw, rfl⟩
  refine ⟨W.left.presheaf.map (homOfLE hOV).op ((cov W).toLRSHom.c.app (op V) σ), fun w hw ↦ ?_⟩
  refine (eval_presheaf_map W.left _ w hw _).trans ?_
  refine (eval_c_app _ (cov W).isCLinear w (hOV hw) σ).trans ?_
  rw [eval_restrict_complexAffineSpace_of]
  rfl

/-- A section of `𝒪_N` over `V`, as a function on `ℂⁿ` (extended by zero). -/
def holFun {V : (space N).Opens} (r : (space N).presheaf.obj (op V)) : Cn.{u} n → ℂ :=
  OkaRing.toGlobalFun (img V) r

lemma eval_space {V : (space N).Opens} (r : (space N).presheaf.obj (op V)) (y : space N)
    (hy : y ∈ V) : (space N).eval y hy r = holFun r y.1 := by
  rw [eval_restrict_complexAffineSpace_of]
  exact (OkaRing.toGlobalFun_apply (U := img V) r ⟨y, hy, rfl⟩).symm

lemma differentiableOn_holFun {V : (space N).Opens} (r : (space N).presheaf.obj (op V)) :
    DifferentiableOn ℂ (holFun r) (img V) :=
  OkaRing.differentiableOn_toGlobalFun (U := img V) r

/-- Pulling back sections of `𝒪_N` over `V` to sections of `𝒪_W` over `p⁻¹(V ∩ N°)`. -/
def pullback (V : (space N).Opens) :
    (space N).presheaf.obj (op V) →+* W.left.presheaf.obj (op (preim h₀ W V)) :=
  ((proj h₀ W).toLRSHom.c.app (op V)).hom

/-- The value of the pullback of a section of `𝒪_N` along `p`. -/
lemma eval_pullback {V : (space N).Opens} (r : (space N).presheaf.obj (op V)) (w : W.left)
    (hw : w ∈ preim h₀ W V) : W.left.eval w hw (pullback h₀ W V r) = holFun r (pt W w) :=
  (eval_c_app _ (proj h₀ W).isCLinear w hw r).trans (by rw [eval_space, coe_proj_base])

/-- The fibres of `W` over points of `ℂⁿ` are finite. -/
lemma finite_fiber (x : Cn.{u} n) : {w : W.left | pt W w = x}.Finite := by
  by_cases hx : x ∈ N₀
  · have h : {w : W.left | pt W w = x} = (cov W).toLRSHom.base ⁻¹' {⟨x, hx⟩} := by
      ext w
      exact ⟨fun h ↦ Subtype.ext h, fun h ↦ congrArg Subtype.val h⟩
    rw [h]
    haveI := IsFinite.finite_fiber (f := cov W) ⟨x, hx⟩
    exact Set.toFinite _
  · convert Set.finite_empty
    ext w
    exact ⟨fun h ↦ hx (h ▸ pt_mem W w), fun h ↦ h.elim⟩

/-- The fibre of `W` over a point of `ℂⁿ`. -/
def fiberFinset (x : Cn.{u} n) : Finset W.left :=
  (finite_fiber W x).toFinset

lemma mem_fiberFinset {x : Cn.{u} n} {w : W.left} : w ∈ fiberFinset W x ↔ pt W w = x :=
  Set.Finite.mem_toFinset _

/-- **Local sheets of `W`**: near a point `x₀ ∈ N°`, the cover `W` is trivial. There are an open
neighbourhood `B ⊆ N°` of `x₀` and finitely many continuous sections `σᵢ` of `p` over `B` whose
values at each `x ∈ B` enumerate the fibre over `x` without repetition, and whose images are
open. -/
theorem exists_local_sheets [T2Space W.left] {x₀ : Cn.{u} n} (hx₀ : x₀ ∈ N₀) :
    ∃ (B : Set (Cn.{u} n)) (I : Type u) (_ : Fintype I) (σ : I → Cn.{u} n → W.left),
      IsOpen B ∧ x₀ ∈ B ∧ (∀ x ∈ B, x ∈ N₀) ∧ (∀ i, ∀ x ∈ B, pt W (σ i x) = x) ∧
      (∀ i, ContinuousOn (σ i) B) ∧ (∀ w, pt W w ∈ B → ∃! i, σ i (pt W w) = w) ∧
      (∀ i, IsOpen {w | pt W w ∈ B ∧ σ i (pt W w) = w}) := by
  classical
  let f := (cov W).toLRSHom.base
  obtain ⟨hdisc, U, hz₀U, hUo, hpre, H, hH⟩ :=
    isCoveringMap_base_of_isFiniteEtale (cov W) (⟨x₀, hx₀⟩ : space N₀)
  let I := f ⁻¹' {(⟨x₀, hx₀⟩ : space N₀)}
  haveI : Finite I := IsFinite.finite_fiber (f := cov W) _
  -- the sections over `U`
  let G : I → space N₀ → W.left := fun i y ↦ if hy : y ∈ U then (H.symm (⟨y, hy⟩, i)).1 else i.1
  have hG : ∀ i y (hy : y ∈ U), G i y = (H.symm (⟨y, hy⟩, i)).1 := fun i y hy ↦ dif_pos hy
  have hfG : ∀ i y (hy : y ∈ U), f (H.symm (⟨y, hy⟩, i)).1 = y := fun i y hy ↦ by
    have := hH (H.symm (⟨y, hy⟩, i))
    rw [Homeomorph.apply_symm_apply] at this
    exact this.symm
  have hHw : ∀ w (hw : f w ∈ U), (H ⟨w, hw⟩).1 = ⟨f w, hw⟩ := fun w hw ↦ Subtype.ext (hH _)
  let B : Set (Cn.{u} n) := Subtype.val '' U
  have hB : ∀ x ∈ B, ∃ hx : x ∈ N₀, (⟨x, hx⟩ : space N₀) ∈ U := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  have hptB : ∀ w, pt W w ∈ B ↔ f w ∈ U := fun w ↦
    ⟨fun h ↦ (hB _ h).2, fun h ↦ ⟨_, h, rfl⟩⟩
  let σ : I → Cn.{u} n → W.left := fun i x ↦ if hx : x ∈ N₀ then G i ⟨x, hx⟩ else i.1
  have hσ : ∀ i w (hw : f w ∈ U), σ i (pt W w) = (H.symm (⟨f w, hw⟩, i)).1 := fun i w hw ↦ by
    simp only [σ, dif_pos (pt_mem W w)]
    exact hG i _ hw
  have key : ∀ i w (hw : f w ∈ U), σ i (pt W w) = w ↔ (H ⟨w, hw⟩).2 = i := fun i w hw ↦ by
    rw [hσ i w hw]
    constructor
    · intro h
      have h' : H.symm (⟨f w, hw⟩, i) = ⟨w, hw⟩ := Subtype.ext h
      rw [← h', Homeomorph.apply_symm_apply]
    · intro h
      have h' : H ⟨w, hw⟩ = (⟨f w, hw⟩, i) := Prod.ext (hHw w hw) h
      rw [← h', Homeomorph.symm_apply_apply]
  refine ⟨B, I, Fintype.ofFinite I, σ, N₀.isOpenEmbedding.isOpenMap _ hUo, ⟨_, hz₀U, rfl⟩,
    fun x hx ↦ (hB x hx).1, fun i x hx ↦ ?_, fun i ↦ ?_, fun w hw ↦ ?_, fun i ↦ ?_⟩
  · obtain ⟨hxN, hxU⟩ := hB x hx
    simp only [σ, dif_pos hxN, hG i _ hxU]
    exact congrArg Subtype.val (hfG i _ hxU)
  · rw [continuousOn_iff_continuous_restrict]
    have : B.restrict (σ i) = fun x : B ↦
        (H.symm (⟨⟨x.1, (hB x.1 x.2).1⟩, (hB x.1 x.2).2⟩, i)).1 := by
      funext x
      simp only [Set.restrict_apply, σ, dif_pos (hB x.1 x.2).1, hG i _ (hB x.1 x.2).2]
    rw [this]
    refine continuous_subtype_val.comp (H.symm.continuous.comp (Continuous.prodMk ?_
      continuous_const))
    have hc1 : Continuous fun x : B ↦ (⟨x.1, (hB x.1 x.2).1⟩ : space N₀) :=
      continuous_subtype_val.subtype_mk _
    exact hc1.subtype_mk _
  · have hwU := (hptB w).1 hw
    exact ⟨(H ⟨w, hwU⟩).2, (key _ w hwU).2 rfl, fun j hj ↦ ((key j w hwU).1 hj).symm⟩
  · have : {w | pt W w ∈ B ∧ σ i (pt W w) = w} =
        Subtype.val '' ((fun x ↦ (H x).2) ⁻¹' {i}) := by
      ext w
      constructor
      · rintro ⟨hw, hσw⟩
        have hwU := (hptB w).1 hw
        exact ⟨⟨w, hwU⟩, (key i w hwU).1 hσw, rfl⟩
      · rintro ⟨⟨w, hwU⟩, hwi, rfl⟩
        exact ⟨(hptB w).2 hwU, (key i w hwU).2 hwi⟩
    rw [this]
    exact hpre.isOpenMap_subtype_val _
      ((isOpen_discrete {i}).preimage (continuous_snd.comp H.continuous))

/-- **Values along a continuous section of `p` are holomorphic.** -/
theorem differentiableAt_evalFun_comp {B : Set (Cn.{u} n)} {σ : Cn.{u} n → W.left}
    (hB : IsOpen B) (hσ : ∀ x ∈ B, pt W (σ x) = x) (hσc : ContinuousOn σ B) {O : W.left.Opens}
    (a : W.left.presheaf.obj (op O)) {x₁ : Cn.{u} n} (hx₁ : x₁ ∈ B) (hO : σ x₁ ∈ O) :
    DifferentiableAt ℂ (fun x ↦ evalFun a (σ x)) x₁ := by
  obtain ⟨O₁, hwO₁, -, hsheet⟩ := exists_sheet W (σ x₁)
  obtain ⟨F, hFd, hF⟩ := hsheet (O' := O₁ ⊓ O) inf_le_left
    (W.left.presheaf.map (homOfLE inf_le_right).op a)
  have hc : ContinuousAt σ x₁ := hσc.continuousAt (hB.mem_nhds hx₁)
  have hev : ∀ᶠ x in 𝓝 x₁, σ x ∈ O₁ ⊓ O ∧ x ∈ B :=
    Filter.Eventually.and (show ∀ᶠ x in 𝓝 x₁, σ x ∈ O₁ ⊓ O from
      hc.preimage_mem_nhds ((O₁ ⊓ O).isOpen.mem_nhds ⟨hwO₁, hO⟩)) (hB.mem_nhds hx₁)
  have heq : (fun x ↦ evalFun a (σ x)) =ᶠ[𝓝 x₁] F := by
    filter_upwards [hev] with x hx
    calc evalFun a (σ x) = W.left.eval (σ x) hx.1.2 a := evalFun_of_mem a hx.1.2
      _ = W.left.eval (σ x) hx.1 (W.left.presheaf.map (homOfLE inf_le_right).op a) :=
          (eval_presheaf_map W.left _ _ hx.1 a).symm
      _ = F (pt W (σ x)) := hF _ hx.1
      _ = F x := by rw [hσ x hx.2]
  have := hFd (σ x₁) ⟨hwO₁, hO⟩
  rw [hσ x₁ hx₁] at this
  exact this.congr_of_eventuallyEq heq

/-! ### The sheaf of rings `𝒜` -/

/-- The sections of `p_* 𝒪_W` over `V` which are bounded near `N ∖ N°`. -/
def boundedSubring (V : (space N).Opens) : Subring (W.left.presheaf.obj (op (preim h₀ W V))) where
  carrier := {s | IsBoundedNear (proj h₀ W) (removedSet N N₀) s}
  mul_mem' hs ht := hs.mul ht
  one_mem' := by
    have := isBoundedNear_c_app (ρ := proj h₀ W) (D := removedSet N N₀) (O := V) 1
    rwa [map_one] at this
  add_mem' hs ht := hs.add ht
  zero_mem' := isBoundedNear_zero
  neg_mem' {s} hs y hy hyD := by
    obtain ⟨M, hM, C, hC⟩ := hs y hy hyD
    exact ⟨M, hM, C, fun w hw hwM ↦ by rw [map_neg, norm_neg]; exact hC w hw hwM⟩

lemma mem_boundedSubring_iff {V : (space N).Opens} (s : W.left.presheaf.obj (op (preim h₀ W V))) :
    s ∈ boundedSubring h₀ W V ↔ s ∈ (boundedSubmodule (proj h₀ W) (removedSet N N₀)).obj (op V) :=
  Iff.rfl

/-- Restriction preserves boundedness. -/
lemma map_mem_boundedSubring {V V' : (space N).Opens} (h : V' ≤ V)
    {s : W.left.presheaf.obj (op (preim h₀ W V))} (hs : s ∈ boundedSubring h₀ W V) :
    W.left.presheaf.map (homOfLE (preim_mono h₀ W h)).op s ∈ boundedSubring h₀ W V' :=
  IsBoundedNear.restrict h hs

/-- **Off `N ∖ N°`, `𝒜` is `p_* 𝒪_W`.** -/
theorem boundedSubring_eq_top {V : (space N).Opens} (hV : ∀ y ∈ V, y.1 ∈ N₀) :
    boundedSubring h₀ W V = ⊤ :=
  eq_top_iff.2 fun s _ ↦ isBoundedNear_of_disjoint
    (Set.disjoint_left.2 fun y hy hyD ↦ absurd (hV y hy) hyD) s

/-- The presheaf of rings `V ↦ 𝒜(V)`. -/
def boundedPresheaf : TopCat.Presheaf CommRingCat.{u} (space N).toLocallyRingedSpace.toTopCat where
  obj V := CommRingCat.of (boundedSubring h₀ W V.unop)
  map {V V'} f := CommRingCat.ofHom ((W.left.presheaf.map
    (homOfLE (preim_mono h₀ W f.unop.le)).op).hom.restrict _ _
      fun _ hs ↦ map_mem_boundedSubring h₀ W f.unop.le hs)
  map_id V := by
    ext s
    change W.left.presheaf.map (homOfLE _).op s.1 = s.1
    rw [Subsingleton.elim (homOfLE _).op (𝟙 _), W.left.presheaf.map_id]
    rfl
  map_comp f g := by
    ext s
    change W.left.presheaf.map (homOfLE _).op s.1 =
      W.left.presheaf.map (homOfLE _).op (W.left.presheaf.map (homOfLE _).op s.1)
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl

lemma boundedPresheaf_map_val {V V' : (space N).Opens} (f : V' ⟶ V)
    (s : (boundedPresheaf h₀ W).obj (op V)) :
    ((boundedPresheaf h₀ W).map f.op s).1 =
      W.left.presheaf.map (homOfLE (preim_mono h₀ W f.le)).op s.1 :=
  rfl

/-- **`𝒜` is a sheaf of rings.** -/
theorem isSheaf_boundedPresheaf : (boundedPresheaf h₀ W).IsSheaf := by
  classical
  have hW := isLocallyOpenInAffine_left W
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro ι U sf hsf
  have hcomp (i j : ι) (w : W.left) (hi : w ∈ preim h₀ W (U i)) (hj : w ∈ preim h₀ W (U j)) :
      W.left.eval w hi (sf i).1 = W.left.eval w hj (sf j).1 := by
    have hij : w ∈ preim h₀ W (U i ⊓ U j) := ⟨hi, hj⟩
    have := congrArg (fun s : (boundedPresheaf h₀ W).obj (op (U i ⊓ U j)) ↦
      W.left.eval w hij s.1) (hsf i j)
    exact (eval_presheaf_map W.left _ w hij (sf i).1).symm.trans
      (this.trans (eval_presheaf_map W.left _ w hij (sf j).1))
  let f : W.left → ℂ := fun w ↦
    if h : ∃ i, w ∈ preim h₀ W (U i) then W.left.eval w h.choose_spec (sf h.choose).1 else 0
  have hf (i : ι) (w : W.left) (hw : w ∈ preim h₀ W (U i)) :
      f w = W.left.eval w hw (sf i).1 := by
    have h : ∃ i, w ∈ preim h₀ W (U i) := ⟨i, hw⟩
    simp only [f, dif_pos h]
    exact hcomp _ _ _ _ _
  have hcov (w : W.left) (hw : w ∈ preim h₀ W (iSup U)) : ∃ i, w ∈ preim h₀ W (U i) :=
    by obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (show (proj h₀ W).toLRSHom.base w ∈ iSup U from hw)
       exact ⟨i, hi⟩
  obtain ⟨s, hs⟩ := exists_eval_eq_of_local hW (O := preim h₀ W (iSup U)) f fun w hw ↦ by
    obtain ⟨i, hi⟩ := hcov w hw
    exact ⟨preim h₀ W (U i), hi, preim_mono h₀ W (le_iSup U i), (sf i).1,
      fun w' hw' ↦ (hf i w' hw').symm⟩
  have hsb : s ∈ boundedSubring h₀ W (iSup U) := by
    intro y hy hyD
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 hy
    obtain ⟨M, hM, C, hC⟩ := (sf i).2 y hi hyD
    refine ⟨M ∩ (U i).carrier, inter_mem hM ((U i).isOpen.mem_nhds hi), C,
      fun w hw hwM ↦ ?_⟩
    rw [hs w hw, hf i w hwM.2]
    exact hC w hwM.2 hwM.1
  refine ⟨⟨s, hsb⟩, fun i ↦ Subtype.ext ?_, fun s' hs' ↦ Subtype.ext ?_⟩
  · change W.left.presheaf.map _ s = _
    refine eq_of_forall_eval_eq hW fun w hw ↦ ?_
    exact (eval_presheaf_map W.left _ w hw s).trans ((hs _ _).trans (hf i w hw))
  · refine eq_of_forall_eval_eq hW fun w hw ↦ ?_
    obtain ⟨i, hi⟩ := hcov w hw
    have := congrArg (fun s : (boundedPresheaf h₀ W).obj (op (U i)) ↦ W.left.eval w hi s.1)
      (hs' i)
    exact (eval_presheaf_map W.left _ w hi s'.1).symm.trans
      (this.trans ((hf i w hi).symm.trans (hs w hw).symm))

/-- **The sheaf of rings `𝒜`** of sections of `p_* 𝒪_W` bounded near `N ∖ N°`. -/
def boundedSheaf : TopCat.Sheaf CommRingCat.{u} (space N).toLocallyRingedSpace.toTopCat :=
  ⟨boundedPresheaf h₀ W, isSheaf_boundedPresheaf h₀ W⟩

/-- Pulling back sections of `𝒪_N` along `p` lands in `𝒜`. -/
def algebraMapBounded (V : (space N).Opens) :
    (space N).presheaf.obj (op V) →+* boundedSubring h₀ W V :=
  (pullback h₀ W V).codRestrict _
    fun r ↦ isBoundedNear_c_app (ρ := proj h₀ W) (D := removedSet N N₀) (O := V) r

/-- **The structure morphism `𝒪_N ⟶ 𝒜`** of presheaves of rings. -/
def boundedAlgebraHom : (space N).presheaf ⟶ boundedPresheaf h₀ W where
  app V := CommRingCat.ofHom (algebraMapBounded h₀ W V.unop)
  naturality V V' f := by
    ext r
    refine Subtype.ext ?_
    change (proj h₀ W).toLRSHom.c.app (op V'.unop) ((space N).presheaf.map f r) =
      W.left.presheaf.map _ ((proj h₀ W).toLRSHom.c.app (op V.unop) r)
    exact ConcreteCategory.congr_hom ((proj h₀ W).toLRSHom.c.naturality f) r

end

end ComplexAnalytic.BoundedSections
