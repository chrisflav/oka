/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Geometry.RingedSpace.LocallyRingedSpace.FreeResolutionAcyclic
import Oka.Geometry.RingedSpace.LocallyRingedSpace.ModulesStalkNakayama
import Oka.Geometry.RingedSpace.LocallyRingedSpace.ModulesStalkSurjective

/-!
# Local generators and bases of sheaves of modules given by sections

Let `M` be a sheaf of modules on a locally ringed space `Y` and `u : κ → M(V)` a finite family of
sections over an open `V`.

- `ComplexAnalytic.GeneratesLocally u`: every section of `M` over an open `W ≤ V` is, near every
  point, a linear combination of the restrictions of `u`.
- `ComplexAnalytic.LinIndepSections u`: the restrictions of `u` to every open `W ≤ V` are linearly
  independent over `𝒪_Y(W)`.

Both properties are local on `V` and invariant under invertible changes of the family. The
morphism `𝒪^κ ⟶ M|_V` given by `u` (`ComplexAnalytic.freeHomOfSections`) is an epimorphism if `u`
generates locally, and an isomorphism if moreover `u` is linearly independent.
-/

universe u

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry Limits
open AlgebraicGeometry.LocallyRingedSpace

namespace ComplexAnalytic

variable {Y : LocallyRingedSpace.{u}} {M : SheafOfModules.{u} Y.ringSheaf} {κ κ' : Type*}
  [Fintype κ] [Fintype κ']

/-- The section `σ` over `W ≤ V` is a linear combination of the restrictions of `u` to `W`. -/
def IsSecComb {V W : Opens Y.toPresheafedSpace} (u : κ → M.val.obj (op V)) (h : W ≤ V)
    (σ : M.val.obj (op W)) : Prop :=
  ∃ c : κ → Y.presheaf.obj (op W), σ = ∑ k, c k • modRes (u k) W h

/-- The family `u` of sections over `V` generates `M` locally on `V`. -/
def GeneratesLocally {V : Opens Y.toPresheafedSpace} (u : κ → M.val.obj (op V)) : Prop :=
  ∀ (W : Opens Y.toPresheafedSpace) (hW : W ≤ V) (σ : M.val.obj (op W)) (y : Y), y ∈ W →
    ∃ (W' : Opens Y.toPresheafedSpace) (h : W' ≤ W), y ∈ W' ∧
      IsSecComb u (h.trans hW) (modRes σ W' h)

/-- The restrictions of the family `u` of sections over `V` to every open `W ≤ V` are linearly
independent. -/
def LinIndepSections {V : Opens Y.toPresheafedSpace} (u : κ → M.val.obj (op V)) : Prop :=
  ∀ (W : Opens Y.toPresheafedSpace) (hW : W ≤ V) (c : κ → Y.presheaf.obj (op W)),
    ∑ k, c k • modRes (u k) W hW = 0 → c = 0

lemma modRes_sum_smul' {V W : Opens Y.toPresheafedSpace} (h : W ≤ V)
    (c : κ → Y.presheaf.obj (op V))
    (x : κ → M.val.obj (op V)) :
    modRes (∑ k, c k • x k) W h =
      ∑ k, Y.presheaf.map (homOfLE h).op (c k) • modRes (x k) W h := by
  rw [modRes, map_sum]
  exact Finset.sum_congr rfl fun k _ ↦ modRes_smul h (c k) (x k)

lemma presheaf_map_map' {U V W : Opens Y.toPresheafedSpace} (h₁ : W ≤ V) (h₂ : V ≤ U)
    (s : Y.presheaf.obj (op U)) :
    Y.presheaf.map (homOfLE h₁).op (Y.presheaf.map (homOfLE h₂).op s) =
      Y.presheaf.map (homOfLE (h₁.trans h₂)).op s :=
  TopCat.Presheaf.restrict_restrict _ _ _

lemma IsSecComb.res {V W W' : Opens Y.toPresheafedSpace} {u : κ → M.val.obj (op V)}
    {h : W ≤ V}
    {σ : M.val.obj (op W)} (hσ : IsSecComb u h σ) (h' : W' ≤ W) :
    IsSecComb u (h'.trans h) (modRes σ W' h') := by
  obtain ⟨c, rfl⟩ := hσ
  refine ⟨fun k ↦ Y.presheaf.map (homOfLE h').op (c k), ?_⟩
  rw [modRes_sum_smul']
  simp_rw [modRes_res]

/-- If every member of `u` is a combination of `v`, combinations of `u` are combinations of
`v`. -/
lemma IsSecComb.trans {V W : Opens Y.toPresheafedSpace} {u : κ → M.val.obj (op V)}
    {v : κ' → M.val.obj (op V)}
    (huv : ∀ k, IsSecComb v le_rfl (u k)) {h : W ≤ V} {σ : M.val.obj (op W)}
    (hσ : IsSecComb u h σ) : IsSecComb v h σ := by
  classical
  choose a ha using huv
  obtain ⟨c, rfl⟩ := hσ
  refine ⟨fun l ↦ ∑ k, c k * Y.presheaf.map (homOfLE h).op (a k l), ?_⟩
  simp_rw [Finset.sum_smul, mul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [ha k, modRes_sum_smul', Finset.smul_sum]
  simp_rw [modRes_res]

/-- Generation is local: a family which generates on `W₁` and on `W₂` generates on
`W₁ ⊔ W₂`. -/
lemma GeneratesLocally.sup {W₁ W₂ : Opens Y.toPresheafedSpace}
    {w : κ → M.val.obj (op (W₁ ⊔ W₂))}
    (h₁ : GeneratesLocally fun k ↦ modRes (w k) W₁ le_sup_left)
    (h₂ : GeneratesLocally fun k ↦ modRes (w k) W₂ le_sup_right) : GeneratesLocally w := by
  intro W hW σ y hy
  have hy' : y ∈ W₁ ⊔ W₂ := hW hy
  rcases (Opens.mem_sup).1 hy' with hy₁ | hy₂
  · obtain ⟨W', hW', hyW', c, hc⟩ := h₁ (W ⊓ W₁) inf_le_right (modRes σ _ inf_le_left) y
      ⟨hy, hy₁⟩
    refine ⟨W', hW'.trans inf_le_left, hyW', c, ?_⟩
    rw [← modRes_res inf_le_left hW', hc]
    simp_rw [modRes_res]
  · obtain ⟨W', hW', hyW', c, hc⟩ := h₂ (W ⊓ W₂) inf_le_right (modRes σ _ inf_le_left) y
      ⟨hy, hy₂⟩
    refine ⟨W', hW'.trans inf_le_left, hyW', c, ?_⟩
    rw [← modRes_res inf_le_left hW', hc]
    simp_rw [modRes_res]

/-- Generation passes to smaller opens. -/
lemma GeneratesLocally.res {V V' : Opens Y.toPresheafedSpace} {u : κ → M.val.obj (op V)}
    (hu : GeneratesLocally u) (h : V' ≤ V) : GeneratesLocally fun k ↦ modRes (u k) V' h := by
  intro W hW σ y hy
  obtain ⟨W', hW', hyW', c, hc⟩ := hu W (hW.trans h) σ y hy
  exact ⟨W', hW', hyW', c, by simp_rw [modRes_res]; exact hc⟩

/-- If the members of `u` are combinations of `v` and `u` generates locally, so does `v`. -/
lemma GeneratesLocally.of_comb {V : Opens Y.toPresheafedSpace} {u : κ → M.val.obj (op V)}
    {v : κ' → M.val.obj (op V)} (hu : GeneratesLocally u)
    (huv : ∀ k, IsSecComb v le_rfl (u k)) :
    GeneratesLocally v := by
  intro W hW σ y hy
  obtain ⟨W', hW', hyW', hc⟩ := hu W hW σ y hy
  exact ⟨W', hW', hyW', hc.trans huv⟩

lemma sec_eq_of_sup {W A B : Opens Y.toPresheafedSpace} (hW : W ≤ A ⊔ B) (hA : A ≤ W)
    (hB : B ≤ W) {r r' : Y.presheaf.obj (op W)}
    (h₁ : Y.presheaf.map (homOfLE hA).op r = Y.presheaf.map (homOfLE hA).op r')
    (h₂ : Y.presheaf.map (homOfLE hB).op r = Y.presheaf.map (homOfLE hB).op r') : r = r' := by
  refine TopCat.Sheaf.eq_of_locally_eq' Y.sheaf (fun b : Bool ↦ cond b A B) W
    (fun b ↦ homOfLE (by cases b <;> assumption)) (fun y hy ↦ ?_) r r' fun b ↦ ?_
  · rcases (Opens.mem_sup).1 (hW hy) with h | h
    · exact Opens.mem_iSup.2 ⟨true, h⟩
    · exact Opens.mem_iSup.2 ⟨false, h⟩
  · cases b
    · exact h₂
    · exact h₁

/-- Linear independence is local. -/
lemma LinIndepSections.sup {W₁ W₂ : Opens Y.toPresheafedSpace}
    {w : κ → M.val.obj (op (W₁ ⊔ W₂))}
    (h₁ : LinIndepSections fun k ↦ modRes (w k) W₁ le_sup_left)
    (h₂ : LinIndepSections fun k ↦ modRes (w k) W₂ le_sup_right) : LinIndepSections w := by
  intro W hW c hc
  have key : ∀ (A : Opens Y.toPresheafedSpace) (hA : A ≤ W) (hAW : A ≤ W₁ ⊔ W₂)
      (hL : LinIndepSections fun k ↦ modRes (w k) A hAW),
      (fun k ↦ Y.presheaf.map (homOfLE hA).op (c k)) = 0 := by
    intro A hA hAW hL
    refine hL A le_rfl _ ?_
    have := congrArg (fun σ ↦ modRes σ A hA) hc
    simp only [modRes_sum_smul', modRes_zero] at this
    simp_rw [modRes_res] at this ⊢
    exact this
  have e₁ := key (W ⊓ W₁) inf_le_left (inf_le_right.trans le_sup_left)
    (fun V hV c hc ↦ h₁ V (hV.trans inf_le_right) c (by simpa [modRes_res] using hc))
  have e₂ := key (W ⊓ W₂) inf_le_left (inf_le_right.trans le_sup_right)
    (fun V hV c hc ↦ h₂ V (hV.trans inf_le_right) c (by simpa [modRes_res] using hc))
  funext k
  refine sec_eq_of_sup (A := W ⊓ W₁) (B := W ⊓ W₂) (fun y hy ↦ ?_) inf_le_left inf_le_left
    ?_ ?_
  · rcases (Opens.mem_sup).1 (hW hy) with h | h
    · exact Opens.mem_sup.2 (Or.inl ⟨hy, h⟩)
    · exact Opens.mem_sup.2 (Or.inr ⟨hy, h⟩)
  · rw [congrFun e₁ k, Pi.zero_apply, Pi.zero_apply, map_zero]
  · rw [congrFun e₂ k, Pi.zero_apply, Pi.zero_apply, map_zero]

/-- Linear independence is preserved under an invertible change of the family. -/
lemma LinIndepSections.of_mul [DecidableEq κ] {V : Opens Y.toPresheafedSpace}
    {u v : κ → M.val.obj (op V)} (hu : LinIndepSections u)
    (H H' : Matrix κ κ (Y.presheaf.obj (op V))) (hH : H * H' = 1)
    (hv : ∀ k, v k = ∑ l, H k l • u l) : LinIndepSections v := by
  intro W hW c hc
  set ρ := (Y.presheaf.map (homOfLE hW).op).hom
  have hd : Matrix.vecMul c (H.map ρ) = 0 := by
    refine hu W hW _ (Eq.trans ?_ hc)
    simp_rw [hv, modRes_sum_smul', Finset.smul_sum, smul_smul, Matrix.vecMul, dotProduct,
      Finset.sum_smul]
    rw [Finset.sum_comm]
    rfl
  have e : H.map ρ * H'.map ρ = 1 := by
    rw [← Matrix.map_mul, hH, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [← Matrix.vecMul_one c, ← e, ← Matrix.vecMul_vecMul, hd, Matrix.zero_vecMul]

/-- Two sections which agree on the intersection glue. -/
lemma exists_glue {W₁ W₂ : Opens Y.toPresheafedSpace} (σ₁ : M.val.obj (op W₁))
    (σ₂ : M.val.obj (op W₂))
    (h : modRes σ₁ (W₁ ⊓ W₂) inf_le_left = modRes σ₂ (W₁ ⊓ W₂) inf_le_right) :
    ∃ σ : M.val.obj (op (W₁ ⊔ W₂)), modRes σ W₁ le_sup_left = σ₁ ∧
      modRes σ W₂ le_sup_right = σ₂ := by
  obtain ⟨σ, hσ, -⟩ := modRes_existsUnique_gluing M (fun b : Bool ↦ cond b W₁ W₂)
    (W := W₁ ⊔ W₂) (fun y hy ↦ by
      rcases (Opens.mem_sup).1 hy with h | h
      · exact Opens.mem_iSup.2 ⟨true, h⟩
      · exact Opens.mem_iSup.2 ⟨false, h⟩)
    (fun b ↦ by cases b <;> simp)
    (fun b ↦ Bool.rec σ₂ σ₁ b) (fun a b ↦ by
      cases a <;> cases b
      · rfl
      · have := congrArg (fun σ ↦ modRes σ (W₂ ⊓ W₁) (le_inf inf_le_right inf_le_left)) h
        simp only [modRes_res] at this
        exact this.symm
      · have := congrArg (fun σ ↦ modRes σ (W₁ ⊓ W₂) le_rfl) h
        simp only [modRes_res] at this
        exact this
      · rfl)
  exact ⟨σ, hσ true, hσ false⟩

section MatAct

variable {κ'' : Type*} [Fintype κ'']

/-- A matrix of sections of `𝒪_Y` over `W` acting on a family of sections of `M` over `W`. -/
def matAct {W : Opens Y.toPresheafedSpace} (A : Matrix κ κ' (Y.presheaf.obj (op W)))
    (x : κ' → M.val.obj (op W)) : κ → M.val.obj (op W) :=
  fun k ↦ ∑ l, A k l • x l

omit [Fintype κ] in
lemma matAct_apply {W : Opens Y.toPresheafedSpace} (A : Matrix κ κ' (Y.presheaf.obj (op W)))
    (x : κ' → M.val.obj (op W)) (k : κ) : matAct A x k = ∑ l, A k l • x l :=
  rfl

omit [Fintype κ] in
lemma matAct_mul {W : Opens Y.toPresheafedSpace} (A : Matrix κ κ' (Y.presheaf.obj (op W)))
    (B : Matrix κ' κ'' (Y.presheaf.obj (op W))) (x : κ'' → M.val.obj (op W)) :
    matAct (A * B) x = matAct A (matAct B x) := by
  funext k
  simp only [matAct, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
  exact Finset.sum_comm

omit [Fintype κ] in
lemma matAct_one [DecidableEq κ'] {W : Opens Y.toPresheafedSpace}
    (x : κ' → M.val.obj (op W)) : matAct (1 : Matrix κ' κ' (Y.presheaf.obj (op W))) x = x := by
  funext k
  simp [matAct, Matrix.one_apply]

omit [Fintype κ] in
lemma modRes_matAct {W W' : Opens Y.toPresheafedSpace} (h : W' ≤ W)
    (A : Matrix κ κ' (Y.presheaf.obj (op W))) (x : κ' → M.val.obj (op W)) (k : κ) :
    modRes (matAct A x k) W' h =
      matAct (A.map (Y.presheaf.map (homOfLE h).op).hom) (fun l ↦ modRes (x l) W' h) k :=
  modRes_sum_smul' h _ _

omit [Fintype κ] in
/-- Every member of `x` is a combination of `v` if `x = A v`. -/
lemma isSecComb_matAct {W : Opens Y.toPresheafedSpace} (A : Matrix κ κ' (Y.presheaf.obj (op W)))
    {v : κ' → M.val.obj (op W)} (k : κ) : IsSecComb v le_rfl (matAct A v k) :=
  ⟨A k, by simp_rw [modRes_self]; rfl⟩

omit [Fintype κ] in
lemma matAct_sub {W : Opens Y.toPresheafedSpace} (A B : Matrix κ κ' (Y.presheaf.obj (op W)))
    (x : κ' → M.val.obj (op W)) : matAct (A - B) x = matAct A x - matAct B x := by
  funext k
  simp [matAct, sub_smul, Finset.sum_sub_distrib]

omit [Fintype κ'] in
/-- A family obtained from a locally generating family by an invertible matrix generates
locally. -/
lemma GeneratesLocally.of_matAct [DecidableEq κ] {V : Opens Y.toPresheafedSpace}
    {u w : κ → M.val.obj (op V)} (hu : GeneratesLocally u)
    {H H' : Matrix κ κ (Y.presheaf.obj (op V))} (hH : H' * H = 1) (hw : w = matAct H u) :
    GeneratesLocally w := by
  refine hu.of_comb fun k ↦ ?_
  have : u = matAct H' w := by rw [hw, ← matAct_mul, hH, matAct_one]
  rw [this]
  exact isSecComb_matAct H' k

omit [Fintype κ'] in
/-- A family obtained from a linearly independent family by an invertible matrix is linearly
independent. -/
lemma LinIndepSections.of_matAct [DecidableEq κ] {V : Opens Y.toPresheafedSpace}
    {u w : κ → M.val.obj (op V)} (hu : LinIndepSections u)
    {H H' : Matrix κ κ (Y.presheaf.obj (op V))} (hH : H * H' = 1) (hw : w = matAct H u) :
    LinIndepSections w :=
  hu.of_mul H H' hH fun k ↦ by rw [hw]; rfl

omit [Fintype κ'] in
/-- A family which generates the sections over every smaller open generates locally. -/
lemma generatesLocally_of_forall_isSecComb {V : Opens Y.toPresheafedSpace}
    {u : κ → M.val.obj (op V)}
    (hu : ∀ (W : Opens Y.toPresheafedSpace) (hW : W ≤ V) (σ : M.val.obj (op W)),
      IsSecComb u hW σ) : GeneratesLocally u :=
  fun W hW _ _ hy ↦ ⟨W, le_rfl, hy, hu W (le_rfl.trans hW) _⟩

omit [Fintype κ'] in
lemma LinIndepSections.res {V V' : Opens Y.toPresheafedSpace} {u : κ → M.val.obj (op V)}
    (hu : LinIndepSections u) (h : V' ≤ V) :
    LinIndepSections fun k ↦ modRes (u k) V' h :=
  fun W hW c hc ↦ hu W (hW.trans h) c (by simpa only [modRes_res] using hc)

/-- Linear independence is invariant under reindexing. -/
lemma LinIndepSections.comp_equiv {V : Opens Y.toPresheafedSpace} {u : κ' → M.val.obj (op V)}
    (hu : LinIndepSections u) (e : κ ≃ κ') : LinIndepSections (u ∘ e) := by
  intro W hW c hc
  have := hu W hW (c ∘ e.symm) (by
    rw [← hc, ← e.sum_comp]
    simp)
  funext k
  simpa using congrFun this (e k)

end MatAct

section Sheaf

variable (M) in
/-- The restriction of `M` to the open subspace `Y|_V`, whose sections over `W'` are the sections
of `M` over the image of `W'`. -/
noncomputable abbrev resOver (V : Opens Y.toPresheafedSpace) :
    SheafOfModules.{u} (Y.restrict V.isOpenEmbedding).ringSheaf :=
  (restrictOverEquiv Y V).functor.obj (M.over V)

variable {ι : Type u} [Fintype ι]

/-- The morphism `𝒪^ι ⟶ M|_V` sending the generators to the sections `u`. -/
noncomputable def freeHomOfSections {V : Opens Y.toPresheafedSpace}
    (u : ι → M.val.obj (op V)) : SheafOfModules.free ι ⟶ resOver M V :=
  freeMkTop (resOver M V) fun k ↦
    (restrictSectionsEquiv V M ⊤).symm (modRes (u k) _ (TopCat.Sheaf.functor_obj_top V).le)

omit [Fintype ι] in
lemma restrictGenerator_freeHomOfSections {V : Opens Y.toPresheafedSpace}
    (u : ι → M.val.obj (op V)) (k : ι) :
    restrictGenerator V M (freeHomOfSections u) k = u k := by
  rw [restrictGenerator, freeHomOfSections, generatorSection_freeMkTop]
  change modRes (modRes (u k) _ _) V _ = u k
  rw [modRes_res, modRes_self]

/-- The value of `ComplexAnalytic.freeHomOfSections u` on a section of `𝒪^ι`. -/
lemma freeHomOfSections_app [DecidableEq ι] {V : Opens Y.toPresheafedSpace}
    (u : ι → M.val.obj (op V))
    (W' : Opens (Y.restrict V.isOpenEmbedding).toPresheafedSpace)
    (t : (SheafOfModules.free (R := (Y.restrict V.isOpenEmbedding).ringSheaf) ι).val.obj
      (op W')) :
    restrictSectionsEquiv V M W' ((freeHomOfSections u).val.app (op W') t) =
      ∑ k, (show Y.presheaf.obj (op (V.isOpenEmbedding.isOpenMap.functor.obj W')) from
        SheafOfModules.freeEval (op W') t k) •
        modRes (u k) _ ((V.isOpenEmbedding.isOpenMap.functor.monotone le_top).trans
          (TopCat.Sheaf.functor_obj_top V).le) := by
  have h := map_val_app_free_eq_sum (freeHomOfSections u)
    (W := V.isOpenEmbedding.isOpenMap.functor.obj W') rfl
    ((V.isOpenEmbedding.isOpenMap.functor.monotone le_top).trans
      (TopCat.Sheaf.functor_obj_top V).le) t
  simp only [restrictGenerator_freeHomOfSections, sheafOfModules_map_self, ringSheaf_map_self] at h
  exact h

/-- A family of sections which generates locally gives an epimorphism `𝒪^ι ⟶ M|_V`. -/
theorem epi_freeHomOfSections {V : Opens Y.toPresheafedSpace} {u : ι → M.val.obj (op V)}
    (hu : GeneratesLocally u) : Epi (freeHomOfSections u) := by
  classical
  refine epi_of_forall_surjective_stalk _ fun y ↦ ?_
  rw [surjective_stalk_iff_forall]
  intro W' hy s
  set F := V.isOpenEmbedding.isOpenMap.functor
  have hFW' : F.obj W' ≤ V := (F.monotone le_top).trans (TopCat.Sheaf.functor_obj_top V).le
  obtain ⟨W'', hW'', hyW'', c, hc⟩ :=
    hu (F.obj W') hFW' (restrictSectionsEquiv V M W' s) y.1 ⟨y, hy, rfl⟩
  have e : F.obj (preimageOpen V W'') = W'' := functor_obj_preimageOpen (hW''.trans hFW')
  have h₃ : preimageOpen V W'' ≤ W' := fun z hz ↦ by
    obtain ⟨z', hz', hzz'⟩ := hW'' hz
    rwa [show z = z' from Subtype.ext hzz'.symm]
  refine ⟨preimageOpen V W'', h₃, hyW'', SheafOfModules.freeEvalSymm (op (preimageOpen V W''))
    (fun k ↦ Y.presheaf.map (homOfLE e.le).op (c k)), ?_⟩
  apply (restrictSectionsEquiv V M _).injective
  rw [freeHomOfSections_app]
  simp_rw [SheafOfModules.freeEval_freeEvalSymm]
  change _ = modRes (restrictSectionsEquiv V M W' s) (F.obj (preimageOpen V W''))
    (F.monotone h₃)
  rw [← modRes_res hW'' e.le, hc, modRes_sum_smul']
  simp_rw [modRes_res]
  rfl

/-- A linearly independent family of sections gives a monomorphism `𝒪^ι ⟶ M|_V`. -/
theorem mono_freeHomOfSections {V : Opens Y.toPresheafedSpace} {u : ι → M.val.obj (op V)}
    (hu : LinIndepSections u) : Mono (freeHomOfSections u) := by
  classical
  have : Mono ((SheafOfModules.forget _).map (freeHomOfSections u)) := by
    refine PresheafOfModules.mono_of_injective fun W' ↦ ?_
    rw [injective_iff_map_eq_zero]
    intro t ht
    have h0 := freeHomOfSections_app u W'.unop t
    change restrictSectionsEquiv V M W'.unop ((freeHomOfSections u).val.app W' t) = _ at h0
    rw [show (freeHomOfSections u).val.app W' t = 0 from ht, map_zero] at h0
    have hc := hu _ _ _ h0.symm
    refine SheafOfModules.freeEval_injective (op W'.unop) ?_
    exact hc.trans (map_zero _).symm
  exact (SheafOfModules.forget _).mono_of_mono_map this

/-- A linearly independent family of sections which generates locally gives an isomorphism
`𝒪^ι ≅ M|_V`. -/
theorem isIso_freeHomOfSections {V : Opens Y.toPresheafedSpace} {u : ι → M.val.obj (op V)}
    (hu : GeneratesLocally u) (hu' : LinIndepSections u) : IsIso (freeHomOfSections u) := by
  haveI := epi_freeHomOfSections hu
  haveI := mono_freeHomOfSections hu'
  exact isIso_of_mono_of_epi _

/-- If `p : 𝒪^ι ⟶ M|_V` is an isomorphism, its generators are a linearly independent family of
sections. -/
theorem linIndepSections_restrictGenerator {V : Opens Y.toPresheafedSpace}
    (p : SheafOfModules.free ι ⟶ resOver M V) [IsIso p] :
    LinIndepSections (restrictGenerator V M p) := by
  classical
  intro W hW c hc
  have e := functor_obj_preimageOpen (X := Y) hW
  have h0 := val_app_freeEvalSymm_eq_zero p e hW c hc
  have hinj : Function.Injective (p.val.app (op (preimageOpen V W))) :=
    PresheafOfModules.injective_of_mono ((SheafOfModules.forget _).map p) _
  rw [← map_zero (p.val.app (op (preimageOpen V W))).hom] at h0
  have h1 := congrArg (SheafOfModules.freeEval (op (preimageOpen V W))) (hinj h0)
  rw [SheafOfModules.freeEval_freeEvalSymm, map_zero] at h1
  funext k
  have h2 := congrArg (fun r ↦ Y.ringSheaf.obj.map (homOfLE e.ge).op r) (congrFun h1 k)
  simp only [Pi.zero_apply, ringSheaf_map_map, ringSheaf_map_self] at h2
  exact h2.trans (map_zero _)

/-- If `p : 𝒪^ι ⟶ M|_V` is surjective on the sections over the preimage of `W ≤ V`, every
section of `M` over `W` is a combination of the generators of `p`. -/
theorem isSecComb_restrictGenerator {V W : Opens Y.toPresheafedSpace}
    (p : SheafOfModules.free ι ⟶ resOver M V) (hW : W ≤ V)
    (hp : Function.Surjective (p.val.app (op (preimageOpen V W)))) (σ : M.val.obj (op W)) :
    IsSecComb (restrictGenerator V M p) hW σ := by
  classical
  have e := functor_obj_preimageOpen (X := Y) hW
  obtain ⟨t, ht⟩ := hp ((restrictSectionsEquiv V M _).symm (modRes σ _ e.le))
  have h := map_val_app_free_eq_sum p e hW t
  rw [ht, AddEquiv.apply_symm_apply] at h
  change modRes (modRes σ _ e.le) W e.ge = _ at h
  rw [modRes_res, modRes_self] at h
  exact ⟨_, h⟩

end Sheaf

end ComplexAnalytic
