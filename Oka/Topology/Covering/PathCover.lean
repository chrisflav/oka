/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.Convex.Contractible
import Mathlib.GroupTheory.Index

/-!
# The covering space associated to a subgroup of the fundamental group

Let `B` be a locally path-connected, semilocally simply connected space, `b : B` and
`H ≤ π₁(B, b)`. The classical construction (Hatcher, *Algebraic Topology*, §1.3) gives a covering
map `PathCover.proj H : PathCover H → B` whose points over `y` are homotopy classes of paths from
`b` to `y` modulo `H` acting by precomposition, topologised by the sets of extensions of a class
by paths inside an open set. Mathlib has path lifting and monodromy for covering maps
(`Mathlib/Topology/Homotopy/Lifting.lean`) but no construction of covering spaces from subgroups;
this file adds it.

Semilocal simple connectivity is used in the "path" form `IsPathSimple`: any two paths inside the
set with the same end points are homotopic in `B`.

## Main definitions

- `IsPathSimple U`, `SemilocallySimplyConnected B`.
- `PathCover H`, `PathCover.proj H`.

## Main results

- `PathCover.isCoveringMap`: `PathCover.proj H` is a covering map.
- `PathCover.monodromy_eq`: the monodromy of the class of a path `γ : y ⟶ z` sends the class of
  `α : b ⟶ y` to the class of `α ≫ γ`.
- `PathCover.mem_of_forall_monodromy_eq`: an element of `π₁(B, b)` acting trivially on the fibre
  over `b` lies in `H`.
- `PathCover.t2Space`: the total space is Hausdorff if `B` is.
-/

universe u

open Topology Set CategoryTheory

variable {B : Type u} [TopologicalSpace B]

/-- A set `U` is **path-simple** if any two paths inside `U` with the same end points are
homotopic (in the ambient space). -/
def IsPathSimple (U : Set B) : Prop :=
  ∀ ⦃x y : B⦄ (γ γ' : Path x y), (∀ t, γ t ∈ U) → (∀ t, γ' t ∈ U) → γ.Homotopic γ'

lemma IsPathSimple.mono {U V : Set B} (hU : IsPathSimple U) (h : V ⊆ U) : IsPathSimple V :=
  fun _ _ γ γ' hγ hγ' ↦ hU γ γ' (fun t ↦ h (hγ t)) fun t ↦ h (hγ' t)

variable (B) in
/-- A space is **semilocally simply connected** if every point has a path-simple neighbourhood. -/
def SemilocallySimplyConnected : Prop :=
  ∀ x : B, ∃ U ∈ 𝓝 x, IsPathSimple U

noncomputable section

namespace PathCover

variable {b : B} (H : Subgroup (FundamentalGroup B b))

/-- The relation on arrows `b ⟶ y` of the fundamental groupoid: `α ~ β` iff `α ≫ β⁻¹ ∈ H`. -/
def setoid (y : B) : Setoid (FundamentalGroupoid.mk b ⟶ FundamentalGroupoid.mk y) where
  r α β := FundamentalGroup.fromArrow (α ≫ inv β) ∈ H
  iseqv := {
    refl α := by
      rw [IsIso.hom_inv_id]
      exact H.one_mem
    symm {α β} h := by
      have e : FundamentalGroup.fromArrow (β ≫ inv α) =
          (FundamentalGroup.fromArrow (α ≫ inv β))⁻¹ := by
        change _ = Groupoid.inv _
        simp [Groupoid.inv_eq_inv]
      change FundamentalGroup.fromArrow (β ≫ inv α) ∈ H
      rw [e]
      exact H.inv_mem h
    trans {α β γ} h h' := by
      have e : FundamentalGroup.fromArrow (α ≫ inv γ) =
          FundamentalGroup.fromArrow (β ≫ inv γ) * FundamentalGroup.fromArrow (α ≫ inv β) := by
        rw [End.mul_def]
        simp
      change FundamentalGroup.fromArrow (α ≫ inv γ) ∈ H
      rw [e]
      exact H.mul_mem h' h }

/-- The points over `y`. -/
def Fiber (y : B) : Type u := Quotient (setoid H y)

/-- The total space. -/
def _root_.PathCover : Type u := Σ y : B, Fiber H y

/-- The projection to the base. -/
def proj : PathCover H → B := Sigma.fst

variable {H}

/-- The class of an arrow. -/
def Fiber.mk {y : B} (α : FundamentalGroupoid.mk b ⟶ FundamentalGroupoid.mk y) : Fiber H y :=
  Quotient.mk _ α

lemma Fiber.mk_surjective {y : B} : Function.Surjective (Fiber.mk (H := H) (y := y)) :=
  Quotient.mk_surjective

lemma Fiber.mk_eq_mk_iff {y : B} {α β : FundamentalGroupoid.mk b ⟶ FundamentalGroupoid.mk y} :
    Fiber.mk (H := H) α = Fiber.mk β ↔ FundamentalGroup.fromArrow (α ≫ inv β) ∈ H :=
  Quotient.eq

/-- Extension of a class by an arrow of the fundamental groupoid. -/
def Fiber.extend {y z : B} (c : Fiber H y)
    (δ : FundamentalGroupoid.mk y ⟶ FundamentalGroupoid.mk z) : Fiber H z :=
  Quotient.map (· ≫ δ) (fun α β (h : FundamentalGroup.fromArrow (α ≫ inv β) ∈ H) ↦ by
    change FundamentalGroup.fromArrow ((α ≫ δ) ≫ inv (β ≫ δ)) ∈ H
    simpa using h) c

@[simp]
lemma Fiber.mk_extend {y z : B} (α : FundamentalGroupoid.mk b ⟶ FundamentalGroupoid.mk y)
    (δ : FundamentalGroupoid.mk y ⟶ FundamentalGroupoid.mk z) :
    (Fiber.mk (H := H) α).extend δ = Fiber.mk (α ≫ δ) :=
  rfl

@[simp]
lemma Fiber.extend_extend {y z w : B} (c : Fiber H y)
    (δ : FundamentalGroupoid.mk y ⟶ FundamentalGroupoid.mk z)
    (δ' : FundamentalGroupoid.mk z ⟶ FundamentalGroupoid.mk w) :
    (c.extend δ).extend δ' = c.extend (δ ≫ δ') := by
  obtain ⟨α, rfl⟩ := Fiber.mk_surjective c
  simp

@[simp]
lemma Fiber.extend_id {y : B} (c : Fiber H y) : c.extend (𝟙 _) = c := by
  obtain ⟨α, rfl⟩ := Fiber.mk_surjective c
  simp

lemma Fiber.extend_injective {y z : B} (δ : FundamentalGroupoid.mk y ⟶ FundamentalGroupoid.mk z) :
    Function.Injective fun c : Fiber H y ↦ c.extend δ := by
  intro c c' h
  have := congr_arg (fun c ↦ Fiber.extend c (inv δ)) h
  simpa using this

/-- The arrow of the fundamental groupoid given by a path. -/
abbrev hom {x y : B} (γ : Path x y) : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y :=
  Path.Homotopic.Quotient.mk γ

lemma hom_trans {x y z : B} (γ : Path x y) (γ' : Path y z) : hom (γ.trans γ') = hom γ ≫ hom γ' :=
  rfl

lemma hom_refl (x : B) : hom (Path.refl x) = 𝟙 (FundamentalGroupoid.mk x) :=
  rfl

lemma hom_eq_of_isPathSimple {U : Set B} (hU : IsPathSimple U) {x y : B} (γ γ' : Path x y)
    (hγ : ∀ t, γ t ∈ U) (hγ' : ∀ t, γ' t ∈ U) : hom γ = hom γ' :=
  Path.Homotopic.Quotient.eq.2 (hU γ γ' hγ hγ')

/-- The basic sets of the topology: the extensions of `e` by paths inside `U`. -/
def nbhd (e : PathCover H) (U : Set B) : Set (PathCover H) :=
  {e' | ∃ δ : Path e.1 e'.1, (∀ t, δ t ∈ U) ∧ e'.2 = e.2.extend (hom δ)}

instance : TopologicalSpace (PathCover H) :=
  TopologicalSpace.generateFrom {s | ∃ e U, IsOpen U ∧ s = nbhd e U}

lemma mem_nbhd_self (e : PathCover H) {U : Set B} (h : e.1 ∈ U) : e ∈ nbhd e U :=
  ⟨Path.refl _, fun _ ↦ h, (Fiber.extend_id _).symm⟩

lemma fst_mem_of_mem_nbhd {e e' : PathCover H} {U : Set B} (h : e' ∈ nbhd e U) : e'.1 ∈ U := by
  obtain ⟨δ, hδ, -⟩ := h
  simpa using hδ 1

lemma nbhd_subset {e e' : PathCover H} {U V : Set B} (h : e' ∈ nbhd e U) (hVU : V ⊆ U) :
    nbhd e' V ⊆ nbhd e U := by
  obtain ⟨δ, hδ, he'⟩ := h
  rintro e'' ⟨δ', hδ', he''⟩
  refine ⟨δ.trans δ', fun t ↦ ?_, by rw [he'', he', Fiber.extend_extend]; rfl⟩
  rw [Path.trans_apply]
  split_ifs
  exacts [hδ _, hVU (hδ' _)]

lemma isOpen_nbhd (e : PathCover H) {U : Set B} (hU : IsOpen U) : IsOpen (nbhd e U) :=
  TopologicalSpace.isOpen_generateFrom_of_mem ⟨e, U, hU, rfl⟩

lemma isTopologicalBasis :
    TopologicalSpace.IsTopologicalBasis {s : Set (PathCover H) | ∃ e U, IsOpen U ∧ s = nbhd e U}
    where
  exists_subset_inter := by
    rintro _ ⟨e₁, U₁, hU₁, rfl⟩ _ ⟨e₂, U₂, hU₂, rfl⟩ e ⟨h₁, h₂⟩
    exact ⟨nbhd e (U₁ ∩ U₂), ⟨e, _, hU₁.inter hU₂, rfl⟩,
      mem_nbhd_self e ⟨fst_mem_of_mem_nbhd h₁, fst_mem_of_mem_nbhd h₂⟩,
      subset_inter (nbhd_subset h₁ inter_subset_left) (nbhd_subset h₂ inter_subset_right)⟩
  sUnion_eq := eq_univ_of_forall fun e ↦ ⟨_, ⟨e, univ, isOpen_univ, rfl⟩, mem_nbhd_self e trivial⟩
  eq_generateFrom := rfl

lemma mem_nhds_iff {e : PathCover H} {s : Set (PathCover H)} :
    s ∈ 𝓝 e ↔ ∃ U, IsOpen U ∧ e.1 ∈ U ∧ nbhd e U ⊆ s := by
  rw [isTopologicalBasis.mem_nhds_iff]
  constructor
  · rintro ⟨_, ⟨e', U, hU, rfl⟩, he, hs⟩
    exact ⟨U, hU, fst_mem_of_mem_nbhd he, (nbhd_subset he subset_rfl).trans hs⟩
  · rintro ⟨U, hU, he, hs⟩
    exact ⟨_, ⟨e, U, hU, rfl⟩, mem_nbhd_self e he, hs⟩

lemma proj_image_nbhd (e : PathCover H) (U : Set B) :
    proj H '' nbhd e U = pathComponentIn U e.1 := by
  ext z
  constructor
  · rintro ⟨e', ⟨δ, hδ, -⟩, rfl⟩
    exact ⟨δ, hδ⟩
  · rintro ⟨δ, hδ⟩
    exact ⟨⟨z, e.2.extend (hom δ)⟩, ⟨δ, hδ, rfl⟩, rfl⟩

lemma isOpenMap_proj [LocallyPathConnectedSpace B] : IsOpenMap (proj H) := by
  rw [isTopologicalBasis.isOpenMap_iff]
  rintro _ ⟨e, U, hU, rfl⟩
  rw [proj_image_nbhd]
  exact hU.pathComponentIn _

lemma hom_symm_comp {x y : B} (γ : Path x y) : hom γ.symm ≫ hom γ = 𝟙 _ :=
  Path.Homotopic.Quotient.symm_trans _

lemma hom_comp_symm {x y : B} (γ : Path x y) : hom γ ≫ hom γ.symm = 𝟙 _ :=
  Path.Homotopic.Quotient.trans_symm _

/-! ### Sheets over a path-simple, path-connected open set -/

section Sheet

variable {y₀ : B} {V : Set B}

/-- The sheet through `c` over `V`. -/
abbrev sheet (V : Set B) (c : Fiber H y₀) : Set (PathCover H) := nbhd ⟨y₀, c⟩ V

lemma injOn_sheet (hVs : IsPathSimple V) (c : Fiber H y₀) : (sheet V c).InjOn (proj H) := by
  rintro ⟨z, d⟩ ⟨δ, hδ, hd⟩ ⟨z', d'⟩ ⟨δ', hδ', hd'⟩ (h : z = z')
  subst h
  simp only at hd hd'
  rw [hd, hd', hom_eq_of_isPathSimple hVs δ δ' hδ hδ']

lemma surjOn_sheet (hV : ∀ z ∈ V, JoinedIn V y₀ z) (c : Fiber H y₀) :
    (sheet V c).SurjOn (proj H) V := fun z hz ↦ by
  obtain ⟨δ, hδ⟩ := hV z hz
  exact ⟨⟨z, c.extend (hom δ)⟩, ⟨δ, hδ, rfl⟩, rfl⟩

lemma pairwise_disjoint_sheet (hVs : IsPathSimple V) :
    Pairwise (Function.onFun Disjoint fun c : Fiber H y₀ ↦ sheet V c) := by
  intro c c' hcc'
  refine Set.disjoint_left.2 ?_
  rintro ⟨z, d⟩ ⟨δ, hδ, hd⟩ ⟨δ', hδ', hd'⟩
  simp only at hd hd'
  rw [hom_eq_of_isPathSimple hVs δ δ' hδ hδ'] at hd
  exact hcc' (Fiber.extend_injective _ (hd.symm.trans hd'))

lemma preimage_subset_iUnion_sheet (hV : ∀ z ∈ V, JoinedIn V y₀ z) :
    proj H ⁻¹' V ⊆ ⋃ c : Fiber H y₀, sheet V c := by
  rintro ⟨z, d⟩ (hz : z ∈ V)
  obtain ⟨δ, hδ⟩ := hV z hz
  exact mem_iUnion.2 ⟨d.extend (hom δ.symm), δ, hδ, by
    rw [Fiber.extend_extend, hom_symm_comp, Fiber.extend_id]⟩

lemma isOpen_iff_sheet [LocallyPathConnectedSpace B] (hV : ∀ z ∈ V, JoinedIn V y₀ z)
    (c : Fiber H y₀) {W : Set B} (hW : W ⊆ V) :
    IsOpen W ↔ IsOpen (proj H ⁻¹' W ∩ sheet V c) := by
  constructor
  · intro hWo
    refine isOpen_iff_mem_nhds.2 fun e he ↦ mem_nhds_iff.2 ⟨W, hWo, he.1, fun e' he' ↦
      ⟨fst_mem_of_mem_nbhd he', nbhd_subset he.2 hW he'⟩⟩
  · intro h
    convert isOpenMap_proj _ h using 1
    ext z
    refine ⟨fun hz ↦ ?_, fun ⟨e, he, hez⟩ ↦ hez ▸ he.1⟩
    obtain ⟨e, he, rfl⟩ := surjOn_sheet hV c (hW hz)
    exact ⟨e, ⟨hz, he⟩, rfl⟩

end Sheet

/-- Every point of a locally path-connected, semilocally simply connected space has an open,
path-simple neighbourhood in which every point is joined to it. -/
lemma exists_isPathSimple_nhds [LocallyPathConnectedSpace B] (hB : SemilocallySimplyConnected B)
    (y₀ : B) : ∃ V : Set B, IsOpen V ∧ IsPathSimple V ∧ y₀ ∈ V ∧ ∀ z ∈ V, JoinedIn V y₀ z := by
  obtain ⟨U, hU, hUs⟩ := hB y₀
  have hy₀ : y₀ ∈ interior U := mem_interior_iff_mem_nhds.2 hU
  have hVy : y₀ ∈ pathComponentIn (interior U) y₀ := mem_pathComponentIn_self hy₀
  exact ⟨_, isOpen_interior.pathComponentIn y₀,
    hUs.mono (pathComponentIn_subset.trans interior_subset), hVy,
    fun z hz ↦ (isPathConnected_pathComponentIn hy₀).joinedIn y₀ hVy z hz⟩

/-- **`PathCover.proj H` is a covering map**: over an open, path-simple, path-connected `V` the
sheets `PathCover.sheet V c` trivialise it. -/
theorem isCoveringMap [LocallyPathConnectedSpace B] (hB : SemilocallySimplyConnected B) :
    IsCoveringMap (proj H) := by
  intro y₀
  obtain ⟨V, hVo, hVs, hVy, hVc⟩ := exists_isPathSimple_nhds hB y₀
  rcases isEmpty_or_nonempty (Fiber H y₀) with hne | hne
  · haveI : IsEmpty (proj H ⁻¹' {y₀}) := ⟨by
      rintro ⟨⟨z, d⟩, hz⟩
      obtain rfl : z = y₀ := hz
      exact hne.false d⟩
    refine IsEvenlyCovered.of_preimage_eq_empty _ (hVo.mem_nhds hVy) ?_
    refine eq_empty_of_forall_notMem ?_
    rintro ⟨z, d⟩ hz
    obtain ⟨δ, -⟩ := hVc z hz
    exact hne.false (d.extend (hom δ.symm))
  · letI : TopologicalSpace (Fiber H y₀) := ⊥
    haveI : DiscreteTopology (Fiber H y₀) := ⟨rfl⟩
    haveI : Nonempty (B → PathCover H) := ⟨fun z ↦ ⟨y₀, Classical.arbitrary _⟩⟩
    let t := hVo.trivializationDiscrete (f := proj H) (fun c : Fiber H y₀ ↦ sheet V c) V
      (fun c {_} hW ↦ isOpen_iff_sheet hVc c hW) (fun c ↦ injOn_sheet hVs c)
      (fun c ↦ surjOn_sheet hVc c) (pairwise_disjoint_sheet hVs)
      (preimage_subset_iUnion_sheet hVc)
    exact (IsEvenlyCovered.of_trivialization (t := t) hVy).to_isEvenlyCovered_preimage

/-- **The total space is Hausdorff if the base is.** -/
theorem t2Space [T2Space B] [LocallyPathConnectedSpace B] (hB : SemilocallySimplyConnected B) :
    T2Space (PathCover H) := by
  refine ⟨fun e e' hne ↦ ?_⟩
  by_cases h : e.1 = e'.1
  · obtain ⟨y, c⟩ := e
    obtain ⟨y', c'⟩ := e'
    obtain rfl : y = y' := h
    have hcc : c ≠ c' := fun h ↦ hne (h ▸ rfl)
    obtain ⟨V, hVo, hVs, hy, -⟩ := exists_isPathSimple_nhds hB y
    exact ⟨sheet V c, sheet V c', isOpen_nbhd _ hVo, isOpen_nbhd _ hVo, mem_nbhd_self _ hy,
      mem_nbhd_self _ hy, pairwise_disjoint_sheet hVs hcc⟩
  · obtain ⟨U, U', hU, hU', hyU, hyU', hUU'⟩ := t2_separation h
    have hc := (isCoveringMap (H := H) hB).continuous
    exact ⟨proj H ⁻¹' U, proj H ⁻¹' U', hU.preimage hc, hU'.preimage hc, hyU, hyU',
      hUU'.preimage _⟩

/-- **The fibres are finite when `H` has finite index.** -/
instance finite_fiber [H.FiniteIndex] (y : B) : Finite (Fiber H y) := by
  rcases isEmpty_or_nonempty (Fiber H y) with h | h
  · infer_instance
  obtain ⟨c⟩ := h
  obtain ⟨α₀, -⟩ := Fiber.mk_surjective c
  have hb : Finite (Fiber H b) := by
    refine Finite.of_surjective (fun q : FundamentalGroup B b ⧸ H ↦ Quotient.liftOn' q
      (fun g ↦ Fiber.mk (H := H) (FundamentalGroup.toArrow g)) fun g g' hgg' ↦ ?_) ?_
    · rw [QuotientGroup.leftRel_apply] at hgg'
      refine Fiber.mk_eq_mk_iff.2 ?_
      have e : FundamentalGroup.fromArrow (FundamentalGroup.toArrow g ≫
          inv (FundamentalGroup.toArrow g')) = (g⁻¹ * g')⁻¹ := by
        rw [mul_inv_rev, inv_inv, End.mul_def]
        change _ = _ ≫ Groupoid.inv _
        rw [Groupoid.inv_eq_inv]
      rw [e]
      exact H.inv_mem hgg'
    · intro d
      obtain ⟨α, rfl⟩ := Fiber.mk_surjective d
      exact ⟨QuotientGroup.mk α, rfl⟩
  refine Finite.of_surjective (fun d : Fiber H b ↦ d.extend α₀) fun d ↦ ?_
  obtain ⟨α, rfl⟩ := Fiber.mk_surjective d
  exact ⟨Fiber.mk (α ≫ inv α₀), by simp⟩

lemma finite_proj_preimage [H.FiniteIndex] (y : B) : (proj H ⁻¹' {y}).Finite := by
  have : proj H ⁻¹' {y} = Set.range (fun c : Fiber H y ↦ (⟨y, c⟩ : PathCover H)) := by
    ext ⟨z, d⟩
    constructor
    · rintro (rfl : z = y)
      exact ⟨d, rfl⟩
    · rintro ⟨c, hc⟩
      exact (congr_arg Sigma.fst hc).symm
  rw [this]
  exact Set.finite_range _

/-! ### Lifts of paths and monodromy -/

/-- The affine path in the unit interval from `s` to `t`. -/
def segPath (s t : unitInterval) : Path s t where
  toFun u := ⟨s + u * (t - s), by
    have := s.2.1; have := s.2.2; have := t.2.1; have := t.2.2; have := u.2.1; have := u.2.2
    constructor <;> nlinarith⟩
  continuous_toFun := by fun_prop
  source' := by ext; simp
  target' := by ext; simp

lemma dist_segPath_le (s t u : unitInterval) : dist (segPath s t u) s ≤ dist t s := by
  change |(s + u * (t - s) : ℝ) - s| ≤ |(t : ℝ) - s|
  rw [add_sub_cancel_left, abs_mul, abs_of_nonneg u.2.1]
  exact mul_le_of_le_one_left (abs_nonneg _) u.2.2

/-- The restriction of `f : C(I, B)` to `[0, t]`, as a path from `f 0` to `f t`. -/
abbrev segmap (f : C(unitInterval, B)) (t : unitInterval) : Path (f 0) (f t) :=
  (segPath 0 t).map f.continuous

instance : SimplyConnectedSpace unitInterval :=
  haveI : ContractibleSpace unitInterval := (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, by simp⟩
  inferInstance

lemma hom_segmap_trans (f : C(unitInterval, B)) (s t : unitInterval) :
    hom (segmap f t) = hom (segmap f s) ≫ hom ((segPath s t).map f.continuous) := by
  rw [← hom_trans, ← Path.map_trans]
  exact Path.Homotopic.Quotient.eq.2
    ((SimplyConnectedSpace.paths_homotopic _ _).map ⟨f, f.continuous⟩)

lemma hom_segmap_zero (f : C(unitInterval, B)) : hom (segmap f 0) = 𝟙 _ := by
  have : hom (segmap f 0) = hom ((Path.refl (0 : unitInterval)).map f.continuous) :=
    Path.Homotopic.Quotient.eq.2
      ((SimplyConnectedSpace.paths_homotopic _ _).map ⟨f, f.continuous⟩)
  rw [this]
  rfl

/-- The candidate lift of `f` through `PathCover.proj H` starting at the class `c`. -/
def liftFun (f : C(unitInterval, B)) (c : Fiber H (f 0)) (t : unitInterval) : PathCover H :=
  ⟨f t, c.extend (hom (segmap f t))⟩

lemma continuous_liftFun (f : C(unitInterval, B)) (c : Fiber H (f 0)) :
    Continuous (liftFun f c) := by
  refine continuous_iff_continuousAt.2 fun t₀ ↦ ?_
  intro s hs
  obtain ⟨U, hU, hU₀, hUs⟩ := mem_nhds_iff.1 hs
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.1 (f.continuous.continuousAt.preimage_mem_nhds
    (hU.mem_nhds hU₀))
  refine Filter.mem_map.2 (Filter.mem_of_superset (Metric.ball_mem_nhds t₀ hε) fun t ht ↦ hUs ?_)
  refine ⟨(segPath t₀ t).map f.continuous, fun u ↦ hεU ?_, ?_⟩
  · exact Metric.mem_ball.2 ((dist_segPath_le t₀ t u).trans_lt (Metric.mem_ball.1 ht))
  · change c.extend _ = (c.extend _).extend _
    rw [Fiber.extend_extend]
    exact congr_arg _ (hom_segmap_trans f t₀ t)

/-- **Path lifting in `PathCover H`, explicitly**: the lift of `f` starting at `⟨f 0, c⟩` is
`t ↦ ⟨f t, c.extend [f|[0,t]]⟩`. -/
lemma liftPath_eq [LocallyPathConnectedSpace B] (hB : SemilocallySimplyConnected B)
    (f : C(unitInterval, B)) (c : Fiber H (f 0)) :
    (isCoveringMap (H := H) hB).liftPath f ⟨f 0, c⟩ rfl = ⟨liftFun f c, continuous_liftFun f c⟩ :=
  (((isCoveringMap hB).eq_liftPath_iff' rfl).2 ⟨rfl, by
    change (⟨f 0, c.extend (hom (segmap f 0))⟩ : PathCover H) = ⟨f 0, c⟩
    rw [hom_segmap_zero, Fiber.extend_id]⟩).symm

/-- **Monodromy in `PathCover H`**: the monodromy of the class of `γ : Path y z` sends `⟨y, c⟩`
to `⟨z, c.extend [γ]⟩`. -/
theorem monodromy_eq [LocallyPathConnectedSpace B] (hB : SemilocallySimplyConnected B) {y z : B}
    (γ : Path y z) (c : Fiber H y) :
    ((isCoveringMap (H := H) hB).monodromy (Path.Homotopic.Quotient.mk γ) ⟨⟨y, c⟩, rfl⟩ :
      PathCover H) = ⟨z, c.extend (hom γ)⟩ := by
  obtain ⟨f, rfl, rfl⟩ := γ
  change (isCoveringMap hB).liftPath f ⟨f 0, c⟩ rfl 1 = _
  rw [liftPath_eq hB f c]
  change (⟨f 1, c.extend (hom (segmap f 1))⟩ : PathCover H) = _
  congr 3
  ext u
  change f (segPath 0 1 u) = f u
  congr 1
  ext
  simp [segPath]

/-- **The kernel of the monodromy action on the fibre over `b` is contained in `H`**: an element
of `π₁(B, b)` fixing the class of the constant path lies in `H`. -/
theorem mem_of_monodromy_eq [LocallyPathConnectedSpace B] (hB : SemilocallySimplyConnected B)
    (g : FundamentalGroup B b)
    (hg : (isCoveringMap (H := H) hB).monodromy g ⟨⟨b, Fiber.mk (𝟙 _)⟩, rfl⟩ =
      ⟨⟨b, Fiber.mk (𝟙 _)⟩, rfl⟩) : g ∈ H := by
  obtain ⟨γ, rfl⟩ := Path.Homotopic.Quotient.mk_surjective (FundamentalGroup.toPath g)
  have := congr_arg Subtype.val hg
  rw [monodromy_eq hB] at this
  have h2 := (Sigma.mk.inj_iff.1 this).2
  rw [heq_eq_eq, Fiber.mk_extend, Fiber.mk_eq_mk_iff] at h2
  simpa using h2

end PathCover

end
