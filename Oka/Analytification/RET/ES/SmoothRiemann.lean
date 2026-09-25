/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.ES.SmoothSetup
import Oka.Analytic.RiemannExtension

/-!
# The Riemann extension theorem on spaces locally isomorphic to opens of affine spaces

Let `X` be a complex analytic space which is locally isomorphic to opens of affine spaces and `h`
a global function on `X` whose zero set `Z` has empty interior. A section of `𝒪_X` over an open
`O'` containing `O ∖ Z` which is locally bounded near every point of `O` extends to a section over
`O` (`ComplexAnalytic.AnalyticSpace.exists_extension_of_isBounded`). Sections over `O` agreeing
off `Z` agree (`ComplexAnalytic.AnalyticSpace.eq_of_eval_eq_off`), and a bound off `Z` is a bound
on `O` (`ComplexAnalytic.AnalyticSpace.norm_eval_le_of_le_off`).
-/

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry Topology Filter

universe u

namespace ComplexAnalytic.AnalyticSpace

open BoundedSections

noncomputable section

variable {X : AnalyticSpace.{u}}

/-- **Injective charts**: a space locally isomorphic to opens of affine spaces has, around every
point and inside every neighbourhood of it, an injective local isomorphism from an open of an
affine space. -/
theorem IsLocallyOpenInAffine.exists_injective_chart (hX : IsLocallyOpenInAffine X) {x : X}
    {M : Set X} (hM : M ∈ 𝓝 x) :
    ∃ (m : ℕ) (U : (AnalyticSpace.complexAffineSpace.{u} m).Opens)
      (ψ : (AnalyticSpace.complexAffineSpace.{u} m).restrict U ⟶ X),
      IsLocalIso ψ ∧ Function.Injective ψ.toLRSHom.base ∧ Set.range ψ.toLRSHom.base ⊆ M ∧
        x ∈ Set.range ψ.toLRSHom.base := by
  obtain ⟨m, U, φ, z₀, hφ, rfl⟩ := hX x
  haveI := hφ
  obtain ⟨E, hzE, hE⟩ := IsLocalIso.isLocalHomeomorph (f := φ) z₀
  obtain ⟨M', hM'M, hM'o, hxM'⟩ := mem_nhds_iff.1 hM
  let D : ((AnalyticSpace.complexAffineSpace.{u} m).restrict U).Opens :=
    ⟨E.source ∩ φ.toLRSHom.base ⁻¹' M',
      E.open_source.inter (hM'o.preimage φ.toLRSHom.base.hom.continuous)⟩
  have hzD : z₀ ∈ D := ⟨hzE, hxM'⟩
  let U' : (AnalyticSpace.complexAffineSpace.{u} m).Opens :=
    U.isOpenEmbedding.isOpenMap.functor.obj D
  have hU' : U' ≤ U := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  let r := (AnalyticSpace.complexAffineSpace.{u} m).restrictLE hU'
  have hr : ∀ y, (r.toLRSHom.base y).1 = y.1 := coe_base_restrictLE hU'
  have hrD : ∀ y, r.toLRSHom.base y ∈ D := by
    intro y
    obtain ⟨y', hy', hyy'⟩ := y.2
    have : r.toLRSHom.base y = y' := Subtype.ext ((hr y).trans hyy'.symm)
    rw [this]
    exact hy'
  haveI : IsLocalIso (r ≫ (AnalyticSpace.complexAffineSpace.{u} m).ofRestrict U) := by
    rw [restrictLE_fac]
    infer_instance
  haveI : IsLocalIso r :=
    isLocalIso_of_comp r ((AnalyticSpace.complexAffineSpace.{u} m).ofRestrict U)
  have hzU' : z₀.1 ∈ U' := ⟨z₀, hzD, rfl⟩
  refine ⟨m, U', r ≫ φ, inferInstance, fun y y' hyy' ↦ ?_, ?_, ⟨⟨z₀.1, hzU'⟩, ?_⟩⟩
  · change φ.toLRSHom.base (r.toLRSHom.base y) = φ.toLRSHom.base (r.toLRSHom.base y') at hyy'
    rw [hE] at hyy'
    have := E.injOn (hrD y).1 (hrD y').1 hyy'
    exact Subtype.ext ((hr y).symm.trans ((congrArg Subtype.val this).trans (hr y')))
  · rintro _ ⟨y, rfl⟩
    exact hM'M (hrD y).2
  · change φ.toLRSHom.base (r.toLRSHom.base ⟨z₀.1, hzU'⟩) = φ.toLRSHom.base z₀
    congr 1
    exact Subtype.ext (hr _)

section Riemann

variable (hX : IsLocallyOpenInAffine X) (h : X.presheaf.obj (op ⊤))
  (hZ : interior {x | X.eval (U := ⊤) x trivial h = 0} = ∅)

include hZ in
lemma subset_closure_diff_zero {G : Set X} (hG : IsOpen G) :
    G ⊆ closure (G ∩ {x | X.eval (U := ⊤) x trivial h = 0}ᶜ) :=
  (interior_eq_empty_iff_dense_compl.1 hZ).open_subset_closure_inter hG

include hZ in
/-- Two continuous functions on an open which agree off the zero set of `h` agree. -/
lemma eqOn_of_eqOn_diff_zero {G : Set X} (hG : IsOpen G) {f₁ f₂ : X → ℂ}
    (h₁ : ContinuousOn f₁ G) (h₂ : ContinuousOn f₂ G)
    (hf : ∀ x ∈ G, X.eval (U := ⊤) x trivial h ≠ 0 → f₁ x = f₂ x) : Set.EqOn f₁ f₂ G :=
  Set.EqOn.of_subset_closure (fun x hx ↦ hf x hx.1 hx.2) h₁ h₂ Set.inter_subset_left
    (subset_closure_diff_zero h hZ hG)

include hX hZ in
/-- **Sections agreeing off the zero set of `h` agree.** -/
theorem eq_of_eval_eq_off {O : X.Opens} {s s' : X.presheaf.obj (op O)}
    (hs : ∀ x (hx : x ∈ O), X.eval (U := ⊤) x trivial h ≠ 0 → X.eval x hx s = X.eval x hx s') :
    s = s' := by
  refine eq_of_forall_eval_eq hX fun x hx ↦ ?_
  have := eqOn_of_eqOn_diff_zero h hZ O.isOpen (continuousOn_evalFun s)
    (continuousOn_evalFun s') (fun y hy hy0 ↦ by
      rw [evalFun_of_mem s hy, evalFun_of_mem s' hy]
      exact hs y hy hy0) hx
  rwa [evalFun_of_mem s hx, evalFun_of_mem s' hx] at this

include hZ in
/-- **A bound off the zero set of `h` is a bound.** -/
theorem norm_eval_le_of_le_off {O : X.Opens} (s : X.presheaf.obj (op O)) {G : Set X}
    (hG : IsOpen G) {C : ℝ}
    (hs : ∀ x (hx : x ∈ O), x ∈ G → X.eval (U := ⊤) x trivial h ≠ 0 → ‖X.eval x hx s‖ ≤ C)
    (x : X) (hx : x ∈ O) (hxG : x ∈ G) : ‖X.eval x hx s‖ ≤ C := by
  have hcl := subset_closure_diff_zero h hZ (hG.inter O.isOpen) ⟨hxG, hx⟩
  have hc : ContinuousOn (fun y ↦ ‖evalFun s y‖) (G ∩ O) :=
    ((continuousOn_evalFun s).mono Set.inter_subset_right).norm
  have hle : ∀ y ∈ (G ∩ O) ∩ {x | X.eval (U := ⊤) x trivial h = 0}ᶜ, ‖evalFun s y‖ ≤ C :=
    fun y hy ↦ by
      rw [evalFun_of_mem s hy.1.2]
      exact hs y hy.1.2 hy.1.1 hy.2
  by_contra hlt
  rw [not_le] at hlt
  have hca : ContinuousAt (fun y ↦ ‖evalFun s y‖) x :=
    ((continuousOn_evalFun s).continuousAt (O.isOpen.mem_nhds hx)).norm
  have hev : ∀ᶠ y in 𝓝 x, C < ‖evalFun s y‖ :=
    hca.eventually (lt_mem_nhds (by change C < ‖evalFun s x‖; rwa [evalFun_of_mem s hx]))
  obtain ⟨y, hy1, hy2⟩ := mem_closure_iff_nhds.1 hcl _ hev
  exact absurd (hle y hy2) (not_le.2 hy1)

include hX hZ in
/-- A section over `O'` which is bounded near a point of `O` extends to a neighbourhood of the
point. -/
lemma exists_local_extension {O O' : X.Opens}
    (hO'O : ∀ x ∈ O, X.eval (U := ⊤) x trivial h ≠ 0 → x ∈ O') (t : X.presheaf.obj (op O'))
    {x : X} (hx : x ∈ O) {N : Set X} (hN : N ∈ 𝓝 x) {C : ℝ}
    (hC : ∀ y (hy : y ∈ O'), y ∈ N → ‖X.eval y hy t‖ ≤ C) :
    ∃ (N' : X.Opens) (_ : x ∈ N') (_ : N' ≤ O) (σ : X.presheaf.obj (op N')),
      ∀ y (hy : y ∈ N') (hy' : y ∈ O'), X.eval y hy σ = X.eval y hy' t := by
  obtain ⟨m, U, ψ, hψ, hinj, hrange, hxr⟩ :=
    hX.exists_injective_chart (Filter.inter_mem hN (O.isOpen.mem_nhds hx))
  haveI := hψ
  let tψ : (space U).presheaf.obj (op ((Opens.map ψ.toLRSHom.base).obj O')) :=
    ψ.toLRSHom.c.app (op O') t
  let hψ' : (space U).presheaf.obj (op ((Opens.map ψ.toLRSHom.base).obj ⊤)) :=
    ψ.toLRSHom.c.app (op ⊤) h
  set g := holFun hψ'
  set f := holFun tψ
  have hg : ∀ z : space U, g z.1 = X.eval (U := ⊤) (ψ.toLRSHom.base z) trivial h := fun z ↦
    ((eval_space hψ' z trivial).symm.trans (eval_c_app _ ψ.isCLinear (U := ⊤) z trivial h))
  have hf : ∀ (z : space U) (hz : ψ.toLRSHom.base z ∈ O'),
      f z.1 = X.eval (ψ.toLRSHom.base z) hz t := fun z hz ↦
    ((eval_space tψ z hz).symm.trans (eval_c_app _ ψ.isCLinear z hz t))
  set Us : Set (Cn.{u} m) := (img (⊤ : (space U).Opens) : Set (Cn.{u} m))
  have hUs : ∀ y ∈ Us, y ∈ U := img_le _
  have hZ' : interior (Us ∩ g ⁻¹' {0}) = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.2 fun y hy ↦ ?_
    let S' : Set (space U) := {z | z.1 ∈ interior (Us ∩ g ⁻¹' {0})}
    have hS' : IsOpen S' := isOpen_interior.preimage continuous_subtype_val
    have hsub : ψ.toLRSHom.base '' S' ⊆ {x | X.eval (U := ⊤) x trivial h = 0} := by
      rintro _ ⟨z, hz, rfl⟩
      rw [Set.mem_setOf_eq, ← hg]
      exact (interior_subset hz).2
    have := interior_maximal hsub
      ((IsLocalIso.isLocalHomeomorph (f := ψ)).isOpenMap _ hS')
      ⟨⟨y, hUs y (interior_subset hy).1⟩, hy, rfl⟩
    rw [hZ] at this
    exact this
  have hsubO' : Us \ g ⁻¹' {0} ⊆ img ((Opens.map ψ.toLRSHom.base).obj O') := by
    intro y hy
    have hyU := hUs y hy.1
    refine mem_img_iff.2 ⟨hyU, ?_⟩
    refine hO'O _ (hrange ⟨_, rfl⟩).2 ?_
    rw [← hg]
    exact hy.2
  obtain ⟨F, hFd, hFeq⟩ := exists_differentiableOn_eqOn_of_isBoundedUnder (img ⊤).isOpen
    (differentiableOn_holFun hψ') hZ' ((differentiableOn_holFun tψ).mono hsubO')
    fun z _ ↦ Filter.isBoundedUnder_of_eventually_le (a := C)
      (eventually_nhdsWithin_of_forall fun y hy ↦ by
        obtain ⟨hyU, hyO'⟩ := mem_img_iff.1 (hsubO' hy)
        change ‖f y‖ ≤ C
        rw [show y = (⟨y, hyU⟩ : space U).1 from rfl, hf _ hyO']
        exact hC _ _ (hrange ⟨_, rfl⟩).1)
  let σ₀ : (space U).presheaf.obj (op ⊤) := OkaRing.ofDifferentiableOn F hFd
  have hσ₀ : ∀ (z : space U) (hz : z ∈ (⊤ : (space U).Opens)), (space U).eval z hz σ₀ = F z.1 :=
    fun z hz ↦ by
      rw [eval_restrict_complexAffineSpace_of]
      rfl
  obtain ⟨σ, hσ⟩ := exists_eval_eq_image ψ hinj σ₀
  have hFf : Set.EqOn F f (img ((Opens.map ψ.toLRSHom.base).obj O')) := by
    refine Set.EqOn.of_eqOn_diff_zero (img _).isOpen
      (Set.eq_empty_of_subset_empty ((interior_mono (Set.inter_subset_inter_left _
        (img_mono le_top))).trans hZ'.le))
      (hFd.continuousOn.mono (img_mono le_top)) (differentiableOn_holFun tψ).continuousOn
      fun y hy ↦ hFeq ⟨img_mono le_top hy.1, hy.2⟩
  refine ⟨_, ?_, ?_, σ, ?_⟩
  · obtain ⟨z, hz⟩ := hxr
    exact ⟨z, trivial, hz⟩
  · rintro _ ⟨z, -, rfl⟩
    exact (hrange ⟨z, rfl⟩).2
  · rintro _ ⟨z, -, rfl⟩ hy'
    rw [hσ z trivial, hσ₀, hFf (mem_img_iff.2 ⟨z.2, hy'⟩), hf z hy']

include hX hZ in
/-- **The Riemann extension theorem.** Let `h` be a global function whose zero set has empty
interior, `O' ⊆ O` opens with `O ∖ O'` inside the zero set of `h`, and `t` a section over `O'`
which is bounded near every point of `O`. Then `t` extends to a section over `O`. -/
theorem exists_extension_of_isBounded {O O' : X.Opens} (hO' : O' ≤ O)
    (hO'O : ∀ x ∈ O, X.eval (U := ⊤) x trivial h ≠ 0 → x ∈ O') (t : X.presheaf.obj (op O'))
    (hb : ∀ x ∈ O, ∃ N ∈ 𝓝 x, ∃ C : ℝ, ∀ y (hy : y ∈ O'), y ∈ N → ‖X.eval y hy t‖ ≤ C) :
    ∃ s : X.presheaf.obj (op O), X.presheaf.map (homOfLE hO').op s = t := by
  classical
  have hloc : ∀ x ∈ O, ∃ (N' : X.Opens) (_ : x ∈ N') (_ : N' ≤ O)
      (σ : X.presheaf.obj (op N')),
      ∀ y (hy : y ∈ N') (hy' : y ∈ O'), X.eval y hy σ = X.eval y hy' t := fun x hx ↦ by
    obtain ⟨N, hN, C, hC⟩ := hb x hx
    exact exists_local_extension hX h hZ hO'O t hx hN hC
  choose N hxN hNO σ hσ using hloc
  let f : X → ℂ := fun y ↦ if hy : y ∈ O' then X.eval y hy t else
    if hyO : y ∈ O then X.eval y (hxN y hyO) (σ y hyO) else 0
  obtain ⟨s, hs⟩ := exists_eval_eq_of_local hX f fun y hy ↦ ⟨N y hy, hxN y hy, hNO y hy, σ y hy,
    fun w hw ↦ by
      by_cases hw' : w ∈ O'
      · simp only [f, dif_pos hw']
        exact hσ y hy w hw hw'
      · have hwO : w ∈ O := hNO y hy hw
        simp only [f, dif_neg hw', dif_pos hwO]
        have key := eqOn_of_eqOn_diff_zero h hZ ((N y hy).isOpen.inter (N w hwO).isOpen)
          ((continuousOn_evalFun (σ y hy)).mono Set.inter_subset_left)
          ((continuousOn_evalFun (σ w hwO)).mono Set.inter_subset_right)
          (fun x hx hx0 ↦ by
            have hxO' := hO'O x (hNO y hy hx.1) hx0
            rw [evalFun_of_mem _ hx.1, evalFun_of_mem _ hx.2, hσ y hy x hx.1 hxO',
              hσ w hwO x hx.2 hxO']) ⟨hw, hxN w hwO⟩
        rwa [evalFun_of_mem _ hw, evalFun_of_mem _ (hxN w hwO)] at key⟩
  refine ⟨s, eq_of_forall_eval_eq hX fun y hy ↦ ?_⟩
  rw [eval_presheaf_map, hs]
  simp only [f, dif_pos hy]

end Riemann

end

end ComplexAnalytic.AnalyticSpace
