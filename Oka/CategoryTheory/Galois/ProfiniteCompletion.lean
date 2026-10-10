/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.CategoryTheory.Galois.IsFundamentalgroup
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion

/-!
# The profinite completion of a group acting on fibres is a fundamental group

Let `C` be a Galois category with fibre functor `F` and let `π` be a discrete group acting naturally
on the fibres of `F`. If `π` acts transitively on the fibres of connected objects, and every
finite-index normal subgroup of `π` contains the kernel of the action on some fibre, then the
profinite completion `π^` (`ProfiniteGrp.ProfiniteCompletion.completion`) is a fundamental group
of `F` in the sense of `CategoryTheory.PreGaloisCategory.IsFundamentalGroup`, and hence
`π^ ≃ₜ* Aut F` (`CategoryTheory.PreGaloisCategory.profiniteCompletionContinuousMulEquiv`).

This is the shape of every comparison theorem of the form "the étale fundamental group is the
profinite completion of a discrete group", e.g. of the topological fundamental group. Nothing here
is in Mathlib: Mathlib has the profinite completion with its universal property and the notion of
a fundamental group of a fibre functor, but does not connect them.

## Main definitions

- `ProfiniteGrp.ProfiniteCompletion.proj`: the projection `π^ → π ⧸ N` for a finite-index normal
  subgroup `N`.
- `CategoryTheory.PreGaloisCategory.completionMulAction`: the action of `π^` on a fibre, through
  the finite quotient of `π` acting faithfully on it.

## Main results

- `CategoryTheory.PreGaloisCategory.isFundamentalGroup_completion`.
- `CategoryTheory.PreGaloisCategory.profiniteCompletionContinuousMulEquiv`.
-/

universe u u₁ u₂ w

open CategoryTheory

namespace ProfiniteGrp.ProfiniteCompletion

variable {G : Type u} [Group G]

/-- The projection from the profinite completion to the finite quotient `G ⧸ N`. -/
def proj (N : FiniteIndexNormalSubgroup G) : completion (GrpCat.of G) →* G ⧸ N.toSubgroup where
  toFun x := x.val N
  map_one' := rfl
  map_mul' _ _ := rfl

lemma proj_apply (N : FiniteIndexNormalSubgroup G) (x : completion (GrpCat.of G)) :
    proj N x = x.val N :=
  rfl

@[simp]
lemma proj_etaFn (N : FiniteIndexNormalSubgroup G) (g : G) :
    proj N (etaFn (GrpCat.of G) g) = (g : G ⧸ N.toSubgroup) :=
  rfl

/-- The projections are compatible with the transition maps. -/
lemma proj_of_le {N M : FiniteIndexNormalSubgroup G} (h : N ≤ M) (x : completion (GrpCat.of G)) :
    proj M x = QuotientGroup.map _ _ (MonoidHom.id G) h (proj N x) :=
  (x.2 (homOfLE h)).symm

/-- If `x` maps to the class of `g` in `G ⧸ N`, it maps to the class of `g` in every coarser
quotient. -/
lemma proj_eq_of_le {N M : FiniteIndexNormalSubgroup G} (h : N ≤ M) {x : completion (GrpCat.of G)}
    {g : G} (hx : proj N x = g) : proj M x = g := by
  rw [proj_of_le h, hx]
  rfl

lemma ext_proj {x y : completion (GrpCat.of G)} (h : ∀ N, proj N x = proj N y) : x = y :=
  Subtype.ext (funext h)

lemma eq_one_of_proj {x : completion (GrpCat.of G)} (h : ∀ N, proj N x = 1) : x = 1 :=
  ext_proj h

/-- The fibres of each projection are open. -/
lemma isOpen_proj_preimage (N : FiniteIndexNormalSubgroup G) (q : G ⧸ N.toSubgroup) :
    IsOpen {x : completion (GrpCat.of G) | proj N x = q} := by
  have hc : Continuous fun x : completion (GrpCat.of G) ↦ x.val N :=
    (continuous_apply N).comp continuous_subtype_val
  letI : TopologicalSpace (G ⧸ N.toSubgroup) := ⊥
  haveI : DiscreteTopology (G ⧸ N.toSubgroup) := ⟨rfl⟩
  exact (isOpen_discrete {q}).preimage hc

end ProfiniteGrp.ProfiniteCompletion

namespace CategoryTheory.PreGaloisCategory

open ProfiniteGrp.ProfiniteCompletion

variable {C : Type u₁} [Category.{u₂} C] (F : C ⥤ FintypeCat.{w})
  (π : Type u) [Group π] [∀ X, MulAction π (F.obj X)]

/-- The kernel of the action of `π` on the fibre `F.obj X`, a finite-index normal subgroup. -/
def actionKernel (X : C) : FiniteIndexNormalSubgroup π :=
  haveI : Finite (MulAction.toPermHom π (F.obj X)).range := inferInstance
  FiniteIndexNormalSubgroup.ofSubgroup (MulAction.toPermHom π (F.obj X)).ker

variable {π} in
lemma mem_actionKernel_iff {X : C} {g : π} :
    g ∈ actionKernel F π X ↔ ∀ x : F.obj X, g • x = x := by
  change g ∈ (MulAction.toPermHom π (F.obj X)).ker ↔ _
  rw [MonoidHom.mem_ker, Equiv.ext_iff]
  rfl

/-- The action of `π` on `F.obj X` as a permutation representation of the completion: it factors
through the finite quotient by the kernel of the action. -/
def completionPerm (X : C) : completion (GrpCat.of π) →* Equiv.Perm (F.obj X) :=
  (QuotientGroup.lift (actionKernel F π X).toSubgroup (MulAction.toPermHom π (F.obj X))
    (fun _ h ↦ h)).comp (proj (actionKernel F π X))

/-- The action of the profinite completion of `π` on the fibres of `F`. -/
@[reducible]
def completionMulAction (X : C) : MulAction (completion (GrpCat.of π)) (F.obj X) :=
  MulAction.compHom (F.obj X) (completionPerm F π X)

attribute [local instance] completionMulAction

variable {F π}

lemma completion_smul_def (X : C) (g : completion (GrpCat.of π)) (x : F.obj X) :
    g • x = completionPerm F π X g x :=
  rfl

/-- An element of the completion acts on `F.obj X` as any element of `π` with the same image in a
finite quotient finer than the one by the kernel of the action. -/
lemma completion_smul_eq {X : C} {N : FiniteIndexNormalSubgroup π} (hN : N ≤ actionKernel F π X)
    {g : completion (GrpCat.of π)} {h : π} (hg : proj N g = h) (x : F.obj X) : g • x = h • x := by
  rw [completion_smul_def, completionPerm, MonoidHom.comp_apply, proj_eq_of_le hN hg]
  rfl

@[simp]
lemma etaFn_smul {X : C} (h : π) (x : F.obj X) : etaFn (GrpCat.of π) h • x = h • x :=
  completion_smul_eq le_rfl (proj_etaFn _ h) x

lemma exists_proj_eq (N : FiniteIndexNormalSubgroup π) (g : completion (GrpCat.of π)) :
    ∃ h : π, proj N g = h :=
  (QuotientGroup.mk_surjective (proj N g)).imp fun _ h ↦ h.symm

instance isNaturalSMul_completion [IsNaturalSMul F π] :
    IsNaturalSMul F (completion (GrpCat.of π)) where
  naturality g X Y f x := by
    obtain ⟨h, hh⟩ := exists_proj_eq (actionKernel F π X ⊓ actionKernel F π Y) g
    rw [completion_smul_eq inf_le_left hh, completion_smul_eq inf_le_right hh,
      IsNaturalSMul.naturality]

open scoped PreGaloisCategory in
lemma continuousSMul_completion (X : C) : ContinuousSMul (completion (GrpCat.of π)) (F.obj X) := by
  constructor
  rw [continuous_prod_of_discrete_right]
  intro x
  refine continuous_discrete_rng.mpr fun y ↦ ?_
  have : (fun g : completion (GrpCat.of π) ↦ g • x) ⁻¹' {y} =
      ⋃ q ∈ {q : π ⧸ (actionKernel F π X).toSubgroup |
        QuotientGroup.lift _ (MulAction.toPermHom π (F.obj X)) (fun _ h ↦ h) q x = y},
        {g | proj (actionKernel F π X) g = q} := by
    ext g
    simp [completion_smul_def, completionPerm]
    rfl
  rw [this]
  exact isOpen_biUnion fun q _ ↦ isOpen_proj_preimage _ q

variable [GaloisCategory C]

variable (F π) in
/-- **The profinite completion of `π` is a fundamental group of `F`**, if `π` acts naturally on
the fibres of `F`, transitively on the fibres of connected objects, and every finite-index normal
subgroup of `π` contains the kernel of the action on some fibre. -/
theorem isFundamentalGroup_completion [IsNaturalSMul F π]
    (htrans : ∀ (X : C) [IsConnected X], MulAction.IsPretransitive π (F.obj X))
    (hker : ∀ N : FiniteIndexNormalSubgroup π, ∃ X : C,
      ∀ h : π, (∀ x : F.obj X, h • x = x) → h ∈ N) :
    IsFundamentalGroup F (completion (GrpCat.of π)) where
  transitive_of_isGalois X _ := ⟨fun x y ↦ by
    obtain ⟨h, rfl⟩ := (htrans X).exists_smul_eq x y
    exact ⟨etaFn _ h, etaFn_smul h x⟩⟩
  continuous_smul X := continuousSMul_completion X
  non_trivial' g hg := by
    refine eq_one_of_proj fun N ↦ ?_
    obtain ⟨X, hX⟩ := hker N
    obtain ⟨h, hh⟩ := exists_proj_eq (actionKernel F π X ⊓ N) g
    have hmem : h ∈ N := hX h fun x ↦ by
      rw [← completion_smul_eq inf_le_left hh x]
      exact hg X x
    rw [proj_eq_of_le inf_le_right hh, QuotientGroup.eq_one_iff]
    exact hmem

variable [FiberFunctor F]

variable (F π) in
/-- **The profinite completion of `π` is the automorphism group of `F`**, as topological groups,
under the hypotheses of `CategoryTheory.PreGaloisCategory.isFundamentalGroup_completion`. -/
noncomputable def profiniteCompletionContinuousMulEquiv [IsNaturalSMul F π]
    (htrans : ∀ (X : C) [IsConnected X], MulAction.IsPretransitive π (F.obj X))
    (hker : ∀ N : FiniteIndexNormalSubgroup π, ∃ X : C,
      ∀ h : π, (∀ x : F.obj X, h • x = x) → h ∈ N) :
    completion (GrpCat.of π) ≃ₜ* Aut F :=
  haveI := isFundamentalGroup_completion F π htrans hker
  { toMulEquiv := toAutMulEquiv F (completion (GrpCat.of π))
    continuous_toFun := (toAutMulEquiv_isHomeomorph F _).continuous
    continuous_invFun := (toAutMulEquiv_isHomeomorph F _).homeomorph.symm.continuous }

end CategoryTheory.PreGaloisCategory
