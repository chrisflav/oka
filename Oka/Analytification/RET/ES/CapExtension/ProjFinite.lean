/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.ES.CapExtension.ProjLocal
import Oka.Analytification.RET.ES.CapExtension.ProjTheoremA

/-!
# Local finiteness of the sections of the cap with a pole of high order

Keep the notation of `Oka/Analytification/RET/ES/CapExtension/ProjSheaf.lean` and suppose that `𝒜`
satisfies the local conditions for coherence over an open `U ⊆ G`. Then for `n ≫ 0` the sections
of the cap with a pole of order `≤ n` at infinity are locally finitely generated at the points of
`U` (`ComplexAnalytic.Cap.AnnulusDecomposition.exists_capLocallyFinite_of_isCoherent`).

By relative Theorem A (`ComplexAnalytic.relProjectiveLine.exists_finite_generates_twistMod`)
finitely many sections `σᵢ` of `ℋ = 𝒞(n₁)` generate `ℋ` over `B₁ × ℙ¹`, and for `e ≫ 0` the map
`𝒪(e)^I → ℋ(e)` is surjective on sections over `V × ℙ¹`, `V` a small box
(`ComplexAnalytic.relProjectiveLine.exists_surjective_twistMod_extendFreeMap`). A section `t` of the
cap with a pole of order `≤ n₁ + e` is a section of `ℋ(e) = 𝒞(n₁ + e)`
(`ComplexAnalytic.Cap.AnnulusDecomposition.twistOfCap`), hence `∑ pᵢ σᵢ` with `pᵢ` sections of
`𝒪(e)`, i.e. polynomials of degree `≤ e` in `w` with holomorphic coefficients. By Lagrange
interpolation `t` is a combination of the `ℓₗ(w) σᵢ`, `ℓₗ` the Lagrange basis polynomials
(`ComplexAnalytic.Cap.AnnulusDecomposition.polyShift`), with holomorphic coefficients.
-/

open CategoryTheory Opposite Topology TopologicalSpace Set Filter Metric

universe u

namespace ComplexAnalytic.Cap.AnnulusDecomposition

open AnalyticSpace BoundedSections relProjectiveSpaceAn relProjectiveLine
open AlgebraicGeometry AlgebraicGeometry.LocallyRingedSpace

noncomputable section

variable {m : ℕ} {N N₀ : (AnalyticSpace.complexAffineSpace.{u} (m + 1)).Opens} (h₀ : N₀ ≤ N)
  {W : FiniteEtaleOver (space N₀)} {F : WeierstrassForm N N₀}
  (D : AnnulusDecomposition W F.G F.ρ)

lemma capWVal_twComp_eq {n : ℕ} {B : Opens (Fin m → ℂ)}
    (σ : (twistMod D.capModule (n : ℤ)).val.obj (op (tube.{u} (N := 1) B))) {w : W.left}
    (hw : w ∈ (Opens.map (projW W).toLRSHom.base).obj
      (tube.{u} (N := 1) B ⊓ stdOpen.{u} m 1 0)) :
    capWVal (twComp σ 0) w = capWVal (modTwistComp σ 0) w := by
  rw [twComp, modTwistSectionsEquiv_apply, modTwistComp_res]
  have hw2 : w ∈ (Opens.map (projW W).toLRSHom.base).obj
      (tube.{u} (N := 1) B ⊓ stdOpen.{u} m 1 0 ⊓ stdOpen.{u} m 1 0) := ⟨hw, hw.2⟩
  erw [capWVal_res _ _ hw, capWVal_res _ _ hw2]

lemma baseSet_mono {B B' : Opens (Fin m → ℂ)} (h : B ≤ B') : baseSet.{u} B ⊆ baseSet.{u} B' :=
  fun _ hb ↦ h hb

lemma mem_preim_tubeN_of {V V' : Set (Cm.{u} m)} {hV : IsOpen V} {hV' : IsOpen V'} {y : W.left}
    (hy : y ∈ preim h₀ W (tubeN N V hV)) (hy' : baseOf (pt W y) ∈ V') :
    y ∈ preim h₀ W (tubeN N V' hV') :=
  (mem_preim_iff h₀ W).2 (mem_img_iff.2 ⟨(mem_img_iff.1 ((mem_preim_iff h₀ W).1 hy)).1, hy'⟩)

/-- **The values on `W` of a section of `ℋ(e)` in the image of `𝒪(e)^I`**, `ℋ = 𝒞(n₁)`, in the
chart `w`: `∑ᵢ pᵢ(w) σᵢ`. -/
lemma capWVal_eq_sum_of_map_eq {n₁ e : ℕ} {B₁ Bv : Opens (Fin m → ℂ)} (hBv : Bv ≤ B₁)
    {I : Type u} [Fintype I] [DecidableEq I]
    (σ : I → (twistMod D.capModule (n₁ : ℤ)).val.obj (op (tube.{u} (N := 1) B₁)))
    (S' : (twistMod (twistMod D.capModule (n₁ : ℤ)) (e : ℤ)).val.obj
      (op (tube.{u} (N := 1) Bv)))
    (P : (twistMod (SheafOfModules.free
      (R := (relProjectiveSpaceAn.{u} m 1).toLocallyRingedSpace.ringSheaf) I) (e : ℤ)).val.obj
        (op (tube.{u} (N := 1) Bv)))
    (hP : ((twistModFunctor m 1 (e : ℤ)).map (extendFreeMap σ)).val.app
        (op (tube.{u} (N := 1) Bv)) P =
      ((twistModFunctor m 1 (e : ℤ)).map (toModTwistOne (twistMod D.capModule (n₁ : ℤ))
        (V := fun _ : Unit ↦ tube.{u} (N := 1) B₁))).val.app (op (tube.{u} (N := 1) Bv)) S')
    {w : W.left} (hw : w ∈ (Opens.map (projW W).toLRSHom.base).obj
      (tube.{u} (N := 1) Bv ⊓ stdOpen.{u} m 1 0)) :
    capWVal (modTwistSectionsEquiv (N := D.capModule) (twistModCocycle.{u} m 1 (n₁ : ℤ)) 0
      inf_le_right (modTwistComp S' 0)) w =
      ∑ i, freeF0 P i (baseCoord (baseOf (pt W w)), fibOf (pt W w)) *
        capWVal (twComp (σ i) 0) w := by
  set W₀ := tube.{u} (N := 1) Bv ⊓ stdOpen.{u} m 1 0
  have hW₀ : W₀ ≤ tube.{u} (N := 1) B₁ := fun p hp ↦ hBv hp.1
  have key := congrArg (fun T ↦ modTwistComp T 0) hP
  change (extendFreeMap σ).val.app _ (modTwistComp P 0) =
    (toModTwistOne (twistMod D.capModule (n₁ : ℤ))
      (V := fun _ : Unit ↦ tube.{u} (N := 1) B₁)).val.app _ (modTwistComp S' 0) at key
  have k2 := congrArg (modTwistSectionsEquiv (1 : ModCocycle fun _ : Unit ↦ tube.{u} (N := 1) B₁)
    () hW₀) key
  rw [extendFreeMap_app, modTwistSectionsEquiv_apply, modTwistComp_toModTwistOne_app,
    modRes_res, modRes_self] at k2
  set E := modTwistSectionsEquiv (N := D.capModule)
    (twistModCocycle.{u} m 1 (n₁ : ℤ)) 0 (inf_le_right : W₀ ≤ stdOpen.{u} m 1 0)
  have k3 : ∑ i, SheafOfModules.freeEval (op W₀) (modTwistComp P 0) i •
      E (modRes (σ i) W₀ hW₀) = E (modTwistComp S' 0) := by
    rw [← k2, map_sum]
    exact Finset.sum_congr rfl fun i _ ↦ (E.map_smul _ _).symm
  have e2 (i : I) : E (modRes (σ i) W₀ hW₀) =
      modRes (twComp (σ i) 0) W₀ (le_inf hW₀ inf_le_right) := by
    rw [twComp, ← modTwistSectionsEquiv_res, modRes_res]
  rw [← k3]
  erw [capWVal_sum_smul _ _ hw]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [e2 i]
  erw [capWVal_res _ _ hw]
  congr 1
  have hp : chartPt.{u} 0 (baseCoord (baseOf (pt W w)), fibOf (pt W w)) ∈ W₀ :=
    projW_eq_chartPt w ▸ hw
  rw [freeF0, f0_eq_eval _ hp]
  exact eval_congr_point (projW_eq_chartPt w) hw hp _

/-- **The sections of the cap with a pole of high order are locally finitely generated** at the
points over an open `U ⊆ G` over which `𝒜` satisfies the local conditions for coherence. -/
theorem exists_capLocallyFinite_of_isCoherent {U : Opens (Fin m → ℂ)}
    (hUG : ∀ y ∈ U, ofBase.{u} y ∈ F.G)
    (hU : ∀ x : space N, baseCoord (baseOf x.1) ∈ U → IsCoherentAt h₀ W x) {b : Cm.{u} m}
    (hb : baseCoord b ∈ U) : ∃ N₁ : ℕ, ∀ n, N₁ ≤ n → D.CapLocallyFinite h₀ n b := by
  classical
  set a := baseCoord b
  have hK : Complex.closedBox a a ⊆ U := fun y' hy' ↦ (mem_closedBox_self_iff'.1 hy') ▸ hb
  have hne : (Complex.closedBox a a).Nonempty := ⟨a, mem_closedBox_self_iff'.2 rfl⟩
  have hcoh := D.isCoherent_restrictModules_capModule h₀ hUG hU
  obtain ⟨n₀, hgen⟩ := exists_finite_generates_twistMod D.capModule hcoh hK hne
  obtain ⟨n₁, hn₁⟩ : ∃ n₁ : ℕ, n₀ ≤ n₁ := ⟨n₀.toNat, Int.self_le_toNat n₀⟩
  obtain ⟨a₁, b₁, hab₁, hB₁U, I, hI, σ, hσ⟩ := hgen n₁ hn₁
  letI := hI
  let B₁ := boxOpens a₁ b₁
  have hB₁G : ∀ y ∈ B₁, ofBase.{u} y ∈ F.G := fun y hy ↦ hUG y (hB₁U hy)
  have hℋ := D.isCoherent_restrictModules_twistMod_capModule h₀ hB₁G
    (fun x hx ↦ hU x (hB₁U hx)) (n₁ : ℤ)
  obtain ⟨a₂, b₂, hab₂, hB'B₁, e₀, hsurj⟩ :=
    exists_surjective_twistMod_extendFreeMap (twistMod D.capModule (n₁ : ℤ)) hℋ hab₁ hne hσ
  refine ⟨n₁ + e₀.toNat, fun n hn ↦ ?_⟩
  obtain ⟨e, rfl⟩ : ∃ e, n = n₁ + e := ⟨n - n₁, by omega⟩
  have he : e₀ ≤ (e : ℤ) := (Int.self_le_toNat e₀).trans (by exact_mod_cast (by omega))
  let B' := boxOpens a₂ b₂
  have hB'le : B' ≤ B₁ := fun y hy ↦ hB'B₁ hy
  have hB'G : ∀ y ∈ B', ofBase.{u} y ∈ F.G := fun y hy ↦ hB₁G y (hB'le hy)
  let x : Fin (e + 1) → ℂ := fun l ↦ ((l : ℕ) : ℂ)
  have hx : Function.Injective x := fun l l' h ↦
    Fin.ext (Nat.cast_injective (R := ℂ) h)
  let s₀ : I → boundedSubring h₀ W (tubeN N (baseSet.{u} B') isOpen_baseSet) ×
      (D.ι → Cm.{u} m × ℂ → ℂ) := fun i ↦
    D.capRestrict h₀ (tubeN_mono (baseSet_mono hB'le)) (D.capPoleOf h₀ (σ i))
  have hs₀ (i : I) : s₀ i ∈ D.capPole h₀ n₁ (tubeN N (baseSet.{u} B') isOpen_baseSet)
      (baseSet.{u} B' ×ˢ ball 0 F.ρ) :=
    D.capRestrict_mem_capPole h₀ _ (prod_mono (baseSet_mono hB'le) subset_rfl)
      (capPoleOf_mem h₀ hB₁G (σ i))
  let s : I × Fin (e + 1) → boundedSubring h₀ W (tubeN N (baseSet.{u} B') isOpen_baseSet) ×
      (D.ι → Cm.{u} m × ℂ → ℂ) := fun il ↦
    D.polyShift h₀ (Lagrange.basis Finset.univ x il.2) e (s₀ il.1)
  have hs (il : I × Fin (e + 1)) : s il ∈ D.capPole h₀ (n₁ + e)
      (tubeN N (baseSet.{u} B') isOpen_baseSet) (baseSet.{u} B' ×ˢ ball 0 F.ρ) :=
    D.polyShift_mem h₀ (natDegree_lagrange_basis_le hx il.2) (hs₀ il.1)
  let eq := Fintype.equivFin (I × Fin (e + 1))
  refine ⟨baseSet.{u} B', isOpen_baseSet, baseSet_subset hB'G,
    hab₂ (mem_closedBox_self_iff'.2 rfl), Fintype.card (I × Fin (e + 1)),
    fun k ↦ s (eq.symm k), fun k ↦ hs _, fun b' hb' V hV hVB hb'V t ht ↦ ?_⟩
  -- a box around `b'`
  have hVf : IsOpen ({y : Fin m → ℂ | ofBase.{u} y ∈ V} ∩ B') :=
    (hV.preimage continuous_ofBase).inter B'.isOpen
  obtain ⟨a₃, b₃, hmem, hsub⟩ := relProjectiveSpaceAn.exists_openBox_subset hVf
    (show baseCoord b' ∈ {y : Fin m → ℂ | ofBase.{u} y ∈ V} ∩ B' from
      ⟨by rw [Set.mem_setOf_eq, ofBase_baseCoord]; exact hb'V, hb'⟩)
  let Bv := boxOpens a₃ b₃
  have hBvB' : Complex.openBox a₃ b₃ ⊆ Complex.openBox a₂ b₂ := fun y hy ↦ (hsub hy).2
  have hBvB₁ : Bv ≤ B₁ := fun y hy ↦ hB'le (hBvB' hy)
  have hBvV : baseSet.{u} Bv ⊆ V := fun c hc ↦ by
    have := (hsub hc).1
    rwa [Set.mem_setOf_eq, ofBase_baseCoord] at this
  let t' := D.capRestrict h₀ (tubeN_mono (hV := hV) (hV' := isOpen_baseSet) hBvV) t
  have ht' : t' ∈ D.capPole h₀ (n₁ + e) (tubeN N (baseSet.{u} Bv) isOpen_baseSet)
      (baseSet.{u} Bv ×ˢ ball 0 F.ρ) :=
    D.capRestrict_mem_capPole h₀ _ (prod_mono hBvV subset_rfl) ht
  -- the section of `𝒞(n₁ + e)` and of `ℋ(e)`
  let S := twistOfCap h₀ ht'
  have hc : twistModCocycle.{u} m 1 ((n₁ + e : ℕ) : ℤ) =
      twistModCocycle.{u} m 1 (n₁ : ℤ) * twistModCocycle.{u} m 1 (e : ℤ) := by
    rw [← twistModCocycle_add]
    push_cast
    rfl
  obtain ⟨S', hS'⟩ := (modTwistTwistHom_bijective (N := D.capModule)
    (twistModCocycle.{u} m 1 (n₁ : ℤ)) (twistModCocycle.{u} m 1 (e : ℤ))
      (tube.{u} (N := 1) Bv)).2 ((modTwistCongrHom D.capModule hc).val.app _ S)
  obtain ⟨P, hP⟩ := hsurj (e : ℤ) he a₃ b₃ hBvB'
    (((twistModFunctor m 1 (e : ℤ)).map (toModTwistOne (twistMod D.capModule (n₁ : ℤ))
      (V := fun _ : Unit ↦ tube.{u} (N := 1) B₁))).val.app (op (tube.{u} (N := 1) Bv)) S')
  refine ⟨baseSet.{u} Bv, hBvV, isOpen_baseSet, hmem,
    fun k c ↦ freeF0 P (eq.symm k).1 (baseCoord c, x (eq.symm k).2), fun k ↦ ?_,
    fun y hy hyV ↦ ?_⟩
  · exact (differentiableOn_freeF0 P _).comp
      (differentiable_baseCoord.differentiableOn.prodMk (differentiableOn_const _))
      fun c hc ↦ mem_prodOpens.2 ⟨hc, trivial⟩
  · have hyv : y ∈ preim h₀ W (tubeN N (baseSet.{u} Bv) isOpen_baseSet) :=
      mem_preim_tubeN_of h₀ hy hyV
    have hw0 := mem_preimW_of_mem_preim (B := Bv) h₀ hyv
    have hyB₁ : y ∈ preim h₀ W (tubeN N (baseSet.{u} B₁) isOpen_baseSet) :=
      mem_preim_tubeN_of h₀ hy (baseSet_mono hBvB₁ hyV)
    have hyB' : y ∈ preim h₀ W (tubeN N (baseSet.{u} B') isOpen_baseSet) :=
      mem_preim_tubeN_of h₀ hy (baseSet_mono (fun z hz ↦ hBvB' hz) hyV)
    have h1 : evalFun t.1.1 y = capWVal (twComp S 0) y := by
      rw [capWVal_twComp_twistOfCap h₀ ht' hw0]
      exact (evalFun_map W _ _ hyv).symm
    have h2 : capWVal (twComp S 0) y = capWVal (modTwistSectionsEquiv (N := D.capModule)
        (twistModCocycle.{u} m 1 (n₁ : ℤ)) 0 inf_le_right (modTwistComp S' 0)) y := by
      rw [capWVal_twComp_eq D S hw0]
      have := congrArg (fun T ↦ modTwistComp T 0) hS'
      exact congrArg (capWVal · y) this.symm
    rw [h1, h2, capWVal_eq_sum_of_map_eq D hBvB₁ σ S' P hP hw0]
    refine Eq.trans ?_ (Fintype.sum_equiv eq.symm _ (fun il ↦ freeF0 P il.1
      (baseCoord (baseOf (pt W y)), x il.2) * evalFun (s il).1.1 y) fun _ ↦ rfl).symm
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hyBv : baseCoord (baseOf (pt W y)) ∈ Bv := hyV
    rw [freeF0_eq_sum_lagrange P i hyBv hx, Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    have hs₀v : evalFun (s₀ i).1.1 y = evalFun (D.capPoleOf h₀ (σ i)).1.1 y :=
      evalFun_map W _ _ hyB'
    rw [D.evalFun_polyShift h₀ _ _ _ hyB']
    simp only
    rw [hs₀v, evalFun_capPoleOf h₀ _ hyB₁]
    ring

end

end ComplexAnalytic.Cap.AnnulusDecomposition
