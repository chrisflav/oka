/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.ES.Codim2.ChartFreeness
import Oka.Analytification.RET.ES.Codim2.NormalCrossingsBasis
import Oka.Geometry.RingedSpace.LocallyRingedSpace.CoherentModuleOpenEmbedding

/-!
# Bounded sections along a biholomorphism

Keep the notation of `Oka/Analytification/RET/ES/Codim2/ChartFreeness.lean`: `Z` extends
`χ : A° → N°` to a biholomorphism `D → E` with `D ⊆ A`, `E ⊆ N`, and `W'` is the pullback of `W`
along `χ`. If `D` is all of `A`, then `χ` is an open embedding `A → N`, the sections of `𝒪_N` over
`χ(O)` are the sections of `𝒪_A` over `O` (composition with `χ`), and the sections of `𝒜` over
`χ(O)` are the sections of `𝒜'` over `O` (composition with `β`). This is a chart in the sense of
`AlgebraicGeometry.LocallyRingedSpace.ModuleChart`
(`ComplexAnalytic.BoundedSections.ChartBiholo.moduleChart`), so the local finiteness conditions
whose conjunction is coherence transfer from `𝒜'` at `x` to `𝒜` at `χ(x)`.

## Main definitions

- `ComplexAnalytic.BoundedSections.ChartBiholo.moduleChart`: the chart `𝒜' → 𝒜`.
- `ComplexAnalytic.BoundedSections.IsCoherentAt`: the local conditions for coherence of `𝒜` at a
  point.

## Main results

- `ComplexAnalytic.BoundedSections.ChartBiholo.isCoherentAt`: the local conditions transfer along
  `χ`.
- `ComplexAnalytic.BoundedSections.isCoherent_of_forall_isCoherentAt`: coherence from the local
  conditions at every point.
-/

open CategoryTheory Opposite AlgebraicGeometry Topology TopologicalSpace Filter

universe u

namespace ComplexAnalytic.BoundedSections

open AnalyticSpace AlgebraicGeometry.LocallyRingedSpace

noncomputable section

variable {n : ℕ}

/-! ### The local conditions for coherence -/

section At

variable {N N₀ : (AnalyticSpace.complexAffineSpace.{u} n).Opens} (h₀ : N₀ ≤ N)
  (W : FiniteEtaleOver (space N₀))

/-- The conditions at `x` whose conjunction over all points is coherence of `𝒜`: local
generation and local finite generation of relations. -/
def IsCoherentAt (x : space N) : Prop :=
  IsLocallyFinitelyGeneratedModuleAt (boundedModule h₀ W) x ∧
    HasLocalModuleRelationsAt (boundedModule h₀ W) x

/-- **Coherence from the local conditions.** -/
theorem isCoherent_of_forall_isCoherentAt (h : ∀ x, IsCoherentAt h₀ W x) :
    (boundedModule h₀ W).IsCoherent :=
  isCoherent_of_hasLocalModuleRelations _ (fun x ↦ (h x).1)
    ((hasLocalModuleRelations_iff _).2 fun x ↦ (h x).2)

/-- The local conditions hold at every point of a coherent sheaf. -/
theorem IsCoherentAt.of_isCoherent (h : (boundedModule h₀ W).IsCoherent) (x : space N) :
    IsCoherentAt h₀ W x :=
  ⟨isLocallyFinitelyGeneratedModule_of_isFiniteType _ x,
    (hasLocalModuleRelations_iff _).1 (hasLocalModuleRelations_of_isCoherent _) x⟩

end At

/-! ### Sections of `𝒪_N` by their values -/

lemma holFun_injective {N : (AnalyticSpace.complexAffineSpace.{u} n).Opens} {V : (space N).Opens}
    {r r' : (space N).presheaf.obj (op V)} (h : ∀ x ∈ img V, holFun r x = holFun r' x) :
    r = r' :=
  OkaRing.ext (funext fun x ↦ (OkaRing.toGlobalFun_apply (U := img V) r x.2).symm.trans
    ((h x.1 x.2).trans (OkaRing.toGlobalFun_apply (U := img V) r' x.2)))

namespace ChartBiholo

variable {N N₀ A A₀ : (AnalyticSpace.complexAffineSpace.{u} n).Opens} {Φ : ChartMap A₀ N₀}
  (Z : ChartBiholo Φ A N) (hDA : ∀ x ∈ A, x ∈ Z.D)

/-! ### The open embedding -/

include hDA

/-- The map `χ : A → N`. -/
def gMap (x : space A) : space N :=
  ⟨Φ.χ x.1, Z.E_sub _ (Z.mapsTo _ (hDA _ x.2))⟩

lemma continuous_gMap : Continuous (Z.gMap hDA) :=
  (Z.differentiableOn_χ.continuousOn.comp_continuous continuous_subtype_val
    fun x ↦ hDA _ x.2).subtype_mk _

lemma mem_image_gMap_iff (O : (space A).Opens) (y : space N) :
    y ∈ Z.gMap hDA '' (O : Set (space A)) ↔ y.1 ∈ Z.E ∧ Φ.χInv y.1 ∈ img O := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨Z.mapsTo _ (hDA _ x.2), ?_⟩
    change Φ.χInv (Φ.χ x.1) ∈ img O
    rw [Z.inv_χ _ (hDA _ x.2)]
    exact mem_img_iff.2 ⟨x.2, hx⟩
  · rintro ⟨hyE, hy⟩
    obtain ⟨hA, hO⟩ := mem_img_iff.1 hy
    exact ⟨⟨_, hA⟩, hO, Subtype.ext (Z.χ_inv _ hyE)⟩

lemma image_gMap_eq_pushOpen (O : (space A).Opens) :
    Z.gMap hDA '' (O : Set (space A)) = (Z.pushOpen O : Set (space N)) := by
  ext y
  rw [Z.mem_image_gMap_iff hDA O y]
  exact (Z.mem_img_pushOpen (V := O) (y := y.1)).symm.trans (by
    rw [mem_img_iff]
    exact ⟨fun ⟨_, h⟩ ↦ h, fun h ↦ ⟨y.2, h⟩⟩)

/-- `χ : A → N` is an open embedding. -/
lemma isOpenEmbedding_gMap : IsOpenEmbedding (Z.gMap hDA) := by
  refine .of_continuous_injective_isOpenMap (Z.continuous_gMap hDA)
    (fun x y h ↦ Subtype.ext ?_) fun U hU ↦ ?_
  · have h' : Φ.χ x.1 = Φ.χ y.1 := congrArg Subtype.val h
    rw [← Z.inv_χ _ (hDA _ x.2), h', Z.inv_χ _ (hDA _ y.2)]
  · have := Z.image_gMap_eq_pushOpen hDA ⟨U, hU⟩
    change IsOpen (Z.gMap hDA '' ((⟨U, hU⟩ : (space A).Opens) : Set (space A)))
    rw [this]
    exact (Z.pushOpen _).isOpen

/-- The map `χ : A → N`, as a morphism of topological spaces. -/
def gHom : (space A).toPresheafedSpace.carrier ⟶ (space N).toPresheafedSpace.carrier :=
  TopCat.ofHom ⟨Z.gMap hDA, Z.continuous_gMap hDA⟩

lemma isOpenEmbedding_gHom : IsOpenEmbedding (Z.gHom hDA) :=
  Z.isOpenEmbedding_gMap hDA

/-- The image `χ(O)` of an open `O` of `A`. -/
abbrev gImg (O : (space A).Opens) : (space N).Opens :=
  (Z.isOpenEmbedding_gHom hDA).isOpenMap.functor.obj O

lemma img_functor_obj (O : (space A).Opens) :
    (img (Z.gImg hDA O) : Set (Cn.{u} n)) =
      img (Z.pushOpen O) := by
  have : Z.gImg hDA O = Z.pushOpen O :=
    Opens.ext (Z.image_gMap_eq_pushOpen hDA O)
  rw [this]

lemma χ_mem_img {O : (space A).Opens} {x : Cn.{u} n} (hx : x ∈ img O) :
    Φ.χ x ∈ img (Z.gImg hDA O) := by
  obtain ⟨hxA, hxO⟩ := mem_img_iff.1 hx
  exact mem_img_iff.2 ⟨_, ⟨x, hxA⟩, hxO, rfl⟩

lemma χInv_mem_img {O : (space A).Opens} {y : Cn.{u} n}
    (hy : y ∈ img (Z.gImg hDA O)) :
    y ∈ Z.E ∧ Φ.χInv y ∈ img O := by
  have := hy
  rw [← SetLike.mem_coe, Z.img_functor_obj hDA O, SetLike.mem_coe] at this
  exact Z.mem_img_pushOpen.1 this

/-! ### Sections of the structure sheaves -/

lemma differentiableOn_holFun_comp (O : (space A).Opens)
    (r : (space N).presheaf.obj (op (Z.gImg hDA O))) :
    DifferentiableOn ℂ (fun x ↦ holFun r (Φ.χ x)) (img O) :=
  fun x hx ↦ ((differentiableOn_holFun r _ (Z.χ_mem_img hDA hx)).differentiableAt
    ((img _).isOpen.mem_nhds (Z.χ_mem_img hDA hx))).comp_differentiableWithinAt x
    ((Z.differentiableOn_χ x (hDA _ (img_le O x hx))).mono fun x' hx' ↦
      hDA _ (img_le O x' hx'))

/-- Sections of `𝒪_N` over `χ(O)` as sections of `𝒪_A` over `O`: composition with `χ`. -/
def ψ (O : (space A).Opens) :
    (space N).presheaf.obj (op (Z.gImg hDA O)) →+*
      (space A).presheaf.obj (op O) where
  toFun r := OkaRing.ofDifferentiableOn _ (Z.differentiableOn_holFun_comp hDA O r)
  map_one' := holFun_injective fun x hx ↦ by
    rw [holFun_ofDifferentiableOn _ hx, holFun_eq_eval _ (Z.χ_mem_img hDA hx),
      holFun_eq_eval _ hx, map_one, map_one]
  map_mul' r r' := holFun_injective fun x hx ↦ by
    rw [holFun_ofDifferentiableOn _ hx, holFun_mul _ _ hx, holFun_ofDifferentiableOn _ hx,
      holFun_ofDifferentiableOn _ hx, holFun_mul _ _ (Z.χ_mem_img hDA hx)]
  map_zero' := holFun_injective fun x hx ↦ by
    rw [holFun_ofDifferentiableOn _ hx, holFun_zero hx, holFun_zero (Z.χ_mem_img hDA hx)]
  map_add' r r' := holFun_injective fun x hx ↦ by
    rw [holFun_ofDifferentiableOn _ hx, holFun_add _ _ hx, holFun_ofDifferentiableOn _ hx,
      holFun_ofDifferentiableOn _ hx, holFun_add _ _ (Z.χ_mem_img hDA hx)]

lemma holFun_ψ {O : (space A).Opens}
    (r : (space N).presheaf.obj (op (Z.gImg hDA O)))
    {x : Cn.{u} n} (hx : x ∈ img O) : holFun (Z.ψ hDA O r) x = holFun r (Φ.χ x) :=
  holFun_ofDifferentiableOn _ hx

lemma bijective_ψ (O : (space A).Opens) : Function.Bijective (Z.ψ hDA O) := by
  refine ⟨fun r r' h ↦ holFun_injective fun y hy ↦ ?_, fun s ↦ ?_⟩
  · obtain ⟨hyE, hyO⟩ := Z.χInv_mem_img hDA hy
    have := congrArg (fun r ↦ holFun r (Φ.χInv y)) h
    simp only [Z.holFun_ψ hDA _ hyO, Z.χ_inv _ hyE] at this
    exact this
  · have hd : DifferentiableOn ℂ (fun y ↦ holFun s (Φ.χInv y))
        (img (Z.gImg hDA O)) := fun y hy ↦ by
      obtain ⟨hyE, hyO⟩ := Z.χInv_mem_img hDA hy
      exact ((differentiableOn_holFun s _ hyO).differentiableAt
        ((img O).isOpen.mem_nhds hyO)).comp_differentiableWithinAt y
        ((Z.differentiableOn_χInv y hyE).mono fun y' hy' ↦ (Z.χInv_mem_img hDA hy').1)
    refine ⟨OkaRing.ofDifferentiableOn _ hd, holFun_injective fun x hx ↦ ?_⟩
    rw [Z.holFun_ψ hDA _ hx, holFun_ofDifferentiableOn _ (Z.χ_mem_img hDA hx),
      Z.inv_χ _ (hDA _ (img_le O x hx))]

lemma ψ_res {O₁ O₂ : (space A).Opens} (h : O₁ ≤ O₂)
    (r : (space N).presheaf.obj (op (Z.gImg hDA O₂))) :
    Z.ψ hDA O₁ ((space N).res ((Z.isOpenEmbedding_gHom hDA).isOpenMap.functor.monotone h) r) =
      (space A).res h (Z.ψ hDA O₂ r) :=
  holFun_injective fun x hx ↦ by
    rw [Z.holFun_ψ hDA _ hx]
    exact (holFun_map _ r (Z.χ_mem_img hDA hx)).trans
      ((Z.holFun_ψ hDA r (img_mono h hx)).symm.trans (holFun_map h _ hx).symm)

/-! ### Sections of the bounded modules -/

variable {h₀ : N₀ ≤ N} {hA : A₀ ≤ A} {W : FiniteEtaleOver (space N₀)}
  {W' : FiniteEtaleOver (space A₀)} {β : W'.left → W.left} (hβ : IsMapPullback Φ W W' β)
include hβ

omit hβ in
lemma le_pullOpen (O : (space A).Opens) :
    O ≤ Z.pullOpen (Z.gImg hDA O) :=
  fun x hx ↦ ⟨hDA _ x.2, Z.χ_mem_img hDA (mem_img_iff.2 ⟨x.2, hx⟩)⟩

/-- Sections of `𝒜` over `χ(O)` as sections of `𝒜'` over `O`: composition with `β`. -/
def φFun (O : (space A).Opens)
    (a : (boundedModule h₀ W).val.obj (op (Z.gImg hDA O))) :
    (boundedModule hA W').val.obj (op O) :=
  sectRes (boundedModule hA W') (Z.le_pullOpen hDA O) (Z.pullSec hβ a)

lemma evalFun_φFun {O : (space A).Opens}
    (a : (boundedModule h₀ W).val.obj (op (Z.gImg hDA O)))
    {w' : W'.left} (hw' : w' ∈ preim hA W' O) :
    evalFun (secVal hA W' (Z.φFun hDA hβ O a)) w' = evalFun (secVal h₀ W a) (β w') := by
  rw [φFun, evalFun_secVal_sectRes _ _ hw', Z.evalFun_pullSec hβ a
    (preim_mono hA W' (Z.le_pullOpen hDA O) hw')]

lemma β_mem_preim {O : (space A).Opens} {w' : W'.left} (hw' : w' ∈ preim hA W' O) :
    β w' ∈ preim h₀ W (Z.gImg hDA O) := by
  rw [mem_preim_iff, hβ.pt_eq]
  exact Z.χ_mem_img hDA ((mem_preim_iff hA W').1 hw')

lemma exists_preim {O : (space A).Opens} {w : W.left}
    (hw : w ∈ preim h₀ W (Z.gImg hDA O)) :
    ∃ w', β w' = w ∧ w' ∈ preim hA W' O := by
  obtain ⟨hE, hO⟩ := Z.χInv_mem_img hDA ((mem_preim_iff h₀ W).1 hw)
  obtain ⟨w', rfl⟩ := Z.exists_β hβ hE
  refine ⟨w', rfl, (mem_preim_iff hA W').2 ?_⟩
  rw [hβ.pt_eq_χInv]
  exact hO

/-- The identification of the sections of `𝒜` over `χ(O)` with the sections of `𝒜'` over `O`. -/
def φ (O : (space A).Opens) :
    (boundedModule h₀ W).val.obj (op (Z.gImg hDA O)) →+
      (boundedModule hA W').val.obj (op O) where
  toFun := Z.φFun hDA hβ O
  map_zero' := secVal_ext hA W' fun w' hw' ↦ by
    rw [Z.evalFun_φFun hDA hβ _ hw', evalFun_secVal_zero hw',
      evalFun_secVal_zero (Z.β_mem_preim hDA hβ hw')]
  map_add' a b := secVal_ext hA W' fun w' hw' ↦ by
    rw [Z.evalFun_φFun hDA hβ _ hw', evalFun_secVal_add _ _ hw', Z.evalFun_φFun hDA hβ _ hw',
      Z.evalFun_φFun hDA hβ _ hw', evalFun_secVal_add _ _ (Z.β_mem_preim hDA hβ hw')]

lemma bijective_φ (O : (space A).Opens) :
    Function.Bijective (Z.φ (h₀ := h₀) (hA := hA) hDA hβ O) := by
  refine ⟨fun a b h ↦ secVal_ext h₀ W fun w hw ↦ ?_, fun b ↦ ?_⟩
  · obtain ⟨w', rfl, hw'⟩ := Z.exists_preim hDA hβ hw
    have := congrArg (fun a ↦ evalFun (secVal hA W' a) w') h
    simp only [φ, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at this
    rwa [Z.evalFun_φFun hDA hβ _ hw', Z.evalFun_φFun hDA hβ _ hw'] at this
  · have hle : Z.gImg hDA O ≤ Z.pushOpen O :=
      (Opens.ext (Z.image_gMap_eq_pushOpen hDA O)).le
    refine ⟨sectRes (boundedModule h₀ W) hle (Z.pushSec hβ b), secVal_ext hA W' fun w' hw' ↦ ?_⟩
    have hβw := Z.β_mem_preim (h₀ := h₀) hDA hβ hw'
    simp only [φ, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    rw [Z.evalFun_φFun hDA hβ _ hw', evalFun_secVal_sectRes _ _ hβw,
      Z.evalFun_pushSec hβ _ (preim_mono h₀ W hle hβw)]

lemma φ_res {O₁ O₂ : (space A).Opens} (h : O₁ ≤ O₂)
    (a : (boundedModule h₀ W).val.obj
      (op (Z.gImg hDA O₂))) :
    Z.φ hDA hβ O₁ (sectRes (boundedModule h₀ W)
      ((Z.isOpenEmbedding_gHom hDA).isOpenMap.functor.monotone h) a) =
      sectRes (boundedModule hA W') h (Z.φ hDA hβ O₂ a) :=
  secVal_ext hA W' fun w' hw' ↦ by
    simp only [φ, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    rw [Z.evalFun_φFun hDA hβ _ hw', evalFun_secVal_sectRes _ _ (Z.β_mem_preim hDA hβ hw'),
      evalFun_secVal_sectRes _ _ hw', Z.evalFun_φFun hDA hβ _ (preim_mono hA W' h hw')]

lemma φ_smul (O : (space A).Opens)
    (r : (space N).presheaf.obj (op (Z.gImg hDA O)))
    (a : (boundedModule h₀ W).val.obj
      (op (Z.gImg hDA O))) :
    Z.φ (hA := hA) hDA hβ O (r • a) = Z.ψ hDA O r • Z.φ hDA hβ O a :=
  secVal_ext hA W' fun w' hw' ↦ by
    simp only [φ, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    rw [Z.evalFun_φFun hDA hβ _ hw', evalFun_secVal_smul _ _ (Z.β_mem_preim hDA hβ hw'),
      evalFun_secVal_smul _ _ hw', Z.evalFun_φFun hDA hβ _ hw',
      Z.holFun_ψ hDA _ ((mem_preim_iff hA W').1 hw'), hβ.pt_eq]

/-- **The chart of `𝒜` given by a biholomorphism `χ : A → E ⊆ N`**: the sections of `𝒜` over
`χ(O)` are the sections of `𝒜'` over `O`. -/
def moduleChart : ModuleChart (boundedModule h₀ W) (boundedModule hA W') where
  g := Z.gHom hDA
  isOpenEmbedding := Z.isOpenEmbedding_gHom hDA
  ψ := Z.ψ hDA
  bijective_ψ := Z.bijective_ψ hDA
  ψ_res := Z.ψ_res hDA
  φ := Z.φ hDA hβ
  bijective_φ := Z.bijective_φ hDA hβ
  φ_res := Z.φ_res hDA hβ
  φ_smul := Z.φ_smul hDA hβ

/-- **The local conditions for coherence transfer along `χ`.** -/
theorem isCoherentAt {x : space A} (hx : IsCoherentAt hA W' x) :
    IsCoherentAt h₀ W (Z.gMap hDA x) :=
  ⟨(Z.moduleChart hDA hβ).isLocallyFinitelyGeneratedModuleAt hx.1,
    (Z.moduleChart hDA hβ).hasLocalModuleRelationsAt hx.2⟩

end ChartBiholo

end

end ComplexAnalytic.BoundedSections
