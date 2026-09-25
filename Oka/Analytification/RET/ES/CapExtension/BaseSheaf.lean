/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.ES.CapExtension.LocalGen
import Oka.Algebra.Category.ModuleCat.Sheaf.Submodule

/-!
# The sheaf of evaluations of the sections of the cap on the base

Keep the notation of `Oka/Analytification/RET/ES/CapExtension/Setup.lean` and fix `n` and
`M > n ∑ kᵢ` distinct points `wᵥ` of the annulus. The evaluations `λ(t)` of the sections `t` of the
cap with a pole of order `≤ n` at infinity, over opens `B × ℙ¹` of `G × ℙ¹`, form a sheaf of
`𝒪_G`-submodules `𝒮ₙ` of the free sheaf `𝒪_G^{M ∑ kᵢ}`
(`ComplexAnalytic.Cap.AnnulusDecomposition.evalSubmodule`): a tuple of holomorphic functions on
an open `V ⊆ G` is a section if it is locally the evaluation of a section of the cap.
-/

open CategoryTheory Opposite Topology Set Filter Metric

universe u

namespace ComplexAnalytic.BoundedSections.WeierstrassForm

open AnalyticSpace

variable {m : ℕ} {N N₀ : (AnalyticSpace.complexAffineSpace.{u} (m + 1)).Opens}
  (F : WeierstrassForm N N₀)

/-- The base `G`, as an open of `ℂ^m`. -/
def baseOpens : (AnalyticSpace.complexAffineSpace.{u} m).Opens :=
  ⟨F.G, F.isOpen_G⟩

lemma img_subset_G (V : (space F.baseOpens).Opens) : (img V : Set (Cn.{u} m)) ⊆ F.G :=
  fun x hx ↦ img_le V x hx

end ComplexAnalytic.BoundedSections.WeierstrassForm

namespace ComplexAnalytic.Cap.AnnulusDecomposition

open AnalyticSpace BoundedSections Complex.ProjectiveLineBundle AlgebraicGeometry.LocallyRingedSpace
open KummerModel (splitEquiv)

noncomputable section

variable {m : ℕ} {N N₀ : (AnalyticSpace.complexAffineSpace.{u} (m + 1)).Opens} (h₀ : N₀ ≤ N)
  {W : FiniteEtaleOver (space N₀)} {F : WeierstrassForm N N₀}
  (D : AnnulusDecomposition W F.G F.ρ)

/-- The indices `(ν, i, j)` of the evaluation at `M` points. -/
abbrev EvIdx (M : ℕ) : Type u :=
  Fin M × (Σ i, Fin (D.deg i))

variable (n : ℕ) {M : ℕ} (w : Fin M → ℂ)

/-- A tuple `v` of holomorphic functions on an open `V ⊆ G` is **locally an evaluation** of
sections of the cap with a pole of order `≤ n` at infinity. -/
def IsCapEval {V : (space F.baseOpens).Opens}
    (v : D.EvIdx M → (space F.baseOpens).presheaf.obj (op V)) : Prop :=
  ∀ b ∈ img V, ∃ (B : Set (Cm.{u} m)) (hB : IsOpen B), B ⊆ img V ∧ b ∈ B ∧
    ∃ t ∈ D.capPole h₀ n (tubeN N B hB) (B ×ˢ ball 0 F.ρ),
      ∀ b' ∈ B, ∀ x, D.evalVec w t.1.1 b' x = holFun (v x) b'

variable {n w}

variable {h₀ D} in
lemma IsCapEval.congr {V : (space F.baseOpens).Opens}
    {v v' : D.EvIdx M → (space F.baseOpens).presheaf.obj (op V)}
    (hv : D.IsCapEval h₀ n w v) (h : ∀ x, ∀ b ∈ img V, holFun (v' x) b = holFun (v x) b) :
    D.IsCapEval h₀ n w v' := by
  intro b hb
  obtain ⟨B, hB, hBV, hbB, t, ht, htv⟩ := hv b hb
  exact ⟨B, hB, hBV, hbB, t, ht, fun b' hb' x ↦ by rw [htv b' hb' x, h x b' (hBV hb')]⟩

lemma isCapEval_zero (hwρ : ∀ ν, w ν ∈ overlap F.ρ) {V : (space F.baseOpens).Opens} :
    D.IsCapEval h₀ n w (0 : D.EvIdx M → (space F.baseOpens).presheaf.obj (op V)) := by
  intro b hb
  refine ⟨img V, (img V).isOpen, subset_rfl, hb, 0, zero_mem _, fun b' hb' x ↦ ?_⟩
  rw [Pi.zero_apply, holFun_zero hb']
  obtain ⟨y, hy, -, hval⟩ := D.exists_evalVec_eq_tube h₀ hwρ (F.img_subset_G V) hb' x
    (hV := (img V).isOpen)
  rw [hval]
  exact evalFun_of_mem _ hy |>.trans (map_zero _)

lemma isCapEval_add (hwρ : ∀ ν, w ν ∈ overlap F.ρ) {V : (space F.baseOpens).Opens}
    {v v' : D.EvIdx M → (space F.baseOpens).presheaf.obj (op V)} (hv : D.IsCapEval h₀ n w v)
    (hv' : D.IsCapEval h₀ n w v') : D.IsCapEval h₀ n w (v + v') := by
  intro b hb
  obtain ⟨B, hB, hBV, hbB, t, ht, htv⟩ := hv b hb
  obtain ⟨B', hB', hB'V, hbB', t', ht', ht'v⟩ := hv' b hb
  have hBB : IsOpen (B ∩ B') := hB.inter hB'
  have h1 : tubeN N (B ∩ B') hBB ≤ tubeN N B hB := tubeN_mono inter_subset_left
  have h2 : tubeN N (B ∩ B') hBB ≤ tubeN N B' hB' := tubeN_mono inter_subset_right
  have hG : B ∩ B' ⊆ F.G := inter_subset_left.trans (hBV.trans (F.img_subset_G V))
  refine ⟨B ∩ B', hBB, inter_subset_left.trans hBV, ⟨hbB, hbB'⟩,
    D.capRestrict h₀ h1 t + D.capRestrict h₀ h2 t',
    add_mem (D.capRestrict_mem_capPole h₀ h1 (prod_mono inter_subset_left subset_rfl) ht)
      (D.capRestrict_mem_capPole h₀ h2 (prod_mono inter_subset_right subset_rfl) ht'),
    fun b' hb' x ↦ ?_⟩
  have hbV : (splitEquiv m).symm (b', w x.1) ∈ img (tubeN N (B ∩ B') hBB) := by
    rw [F.mem_img_tubeN hG, Homeomorph.apply_symm_apply]
    exact ⟨hb', mem_ball_zero_iff.2 (hwρ x.1).2⟩
  change D.evalVec w ((D.capRestrict h₀ h1 t).1.1 + (D.capRestrict h₀ h2 t').1.1) b' x = _
  rw [D.evalVec_add hwρ (hG hb') x hbV, D.evalVec_capRestrict h₀ hwρ hG inter_subset_left _ hb',
    D.evalVec_capRestrict h₀ hwρ hG inter_subset_right _ hb', htv b' hb'.1 x, ht'v b' hb'.2 x,
    Pi.add_apply, holFun_add _ _ (hBV hb'.1)]

lemma isCapEval_smul (hwρ : ∀ ν, w ν ∈ overlap F.ρ) {V : (space F.baseOpens).Opens}
    (r : (space F.baseOpens).presheaf.obj (op V))
    {v : D.EvIdx M → (space F.baseOpens).presheaf.obj (op V)} (hv : D.IsCapEval h₀ n w v) :
    D.IsCapEval h₀ n w (fun x ↦ r * v x) := by
  intro b hb
  obtain ⟨B, hB, hBV, hbB, t, ht, htv⟩ := hv b hb
  have hG : B ⊆ F.G := hBV.trans (F.img_subset_G V)
  obtain ⟨t', ht', ht'v, -⟩ := D.exists_capPole_sum h₀ hG (s := fun _ : Fin 1 ↦ t)
    (fun _ ↦ ht) (e := fun _ ↦ holFun r) fun _ ↦ (differentiableOn_holFun r).mono hBV
  refine ⟨B, hB, hBV, hbB, t', ht', fun b' hb' x ↦ ?_⟩
  rw [D.evalVec_eq_sum_of_evalFun h₀ hG hwρ ht'v hb' x, Fin.sum_univ_one, htv b' hb' x,
    holFun_mul _ _ (hBV hb')]

lemma isCapEval_map (hwρ : ∀ ν, w ν ∈ overlap F.ρ) {V V' : (space F.baseOpens).Opens}
    (h : V' ≤ V)
    {v : D.EvIdx M → (space F.baseOpens).presheaf.obj (op V)} (hv : D.IsCapEval h₀ n w v) :
    D.IsCapEval h₀ n w (fun x ↦ (space F.baseOpens).presheaf.map (homOfLE h).op (v x)) := by
  intro b hb
  obtain ⟨B, hB, hBV, hbB, t, ht, htv⟩ := hv b (img_mono h hb)
  have hBB : IsOpen (B ∩ img V') := hB.inter (img V').isOpen
  have h1 : tubeN N (B ∩ img V') hBB ≤ tubeN N B hB := tubeN_mono inter_subset_left
  have hG : B ∩ img V' ⊆ F.G := inter_subset_right.trans (F.img_subset_G V')
  refine ⟨B ∩ img V', hBB, inter_subset_right, ⟨hbB, hb⟩, D.capRestrict h₀ h1 t,
    D.capRestrict_mem_capPole h₀ h1 (prod_mono inter_subset_left subset_rfl) ht,
    fun b' hb' x ↦ ?_⟩
  rw [D.evalVec_capRestrict h₀ hwρ hG inter_subset_left _ hb', htv b' hb'.1 x,
    holFun_map h _ hb'.2]

lemma holFun_freeEval_map {V V' : (space F.baseOpens).Opens} (f : op V ⟶ op V')
    (s : (SheafOfModules.free (R := (space F.baseOpens).ringSheaf) (D.EvIdx M)).val.obj (op V))
    [DecidableEq (D.EvIdx M)] (x : D.EvIdx M) {b : Cm.{u} m} (hb : b ∈ img V') :
    holFun (V := V') (SheafOfModules.freeEval (op V')
      ((SheafOfModules.free (D.EvIdx M)).val.map f s) x) b =
      holFun (V := V) (SheafOfModules.freeEval (op V) s x) b := by
  rw [SheafOfModules.freeEval_naturality]
  exact holFun_map (leOfHom f.unop) _ hb

variable (n) in
open Classical in
/-- **The sheaf `𝒮ₙ` of evaluations of the sections of the cap** with a pole of order `≤ n` at
infinity, as a sheaf of submodules of `𝒪_G^{M ∑ kᵢ}`. -/
def evalSubmodule (hwρ : ∀ ν, w ν ∈ overlap F.ρ) :
    (SheafOfModules.free (R := (space F.baseOpens).ringSheaf) (D.EvIdx M)).Submodule where
  obj V :=
    { carrier := {s | D.IsCapEval h₀ n w (V := V.unop) (SheafOfModules.freeEval V s)}
      add_mem' := fun {s s'} hs hs' ↦ by
        change D.IsCapEval h₀ n w (V := V.unop) (SheafOfModules.freeEval V (s + s'))
        rw [map_add]
        exact D.isCapEval_add h₀ hwρ hs hs'
      zero_mem' := by
        change D.IsCapEval h₀ n w (V := V.unop) (SheafOfModules.freeEval V
          (0 : (SheafOfModules.free (R := (space F.baseOpens).ringSheaf) (D.EvIdx M)).val.obj V))
        rw [map_zero]
        exact D.isCapEval_zero h₀ hwρ
      smul_mem' := fun r s hs ↦ by
        change D.IsCapEval h₀ n w (V := V.unop) (SheafOfModules.freeEval V (r • s))
        rw [map_smul]
        exact D.isCapEval_smul h₀ hwρ r hs }
  map {V V'} f s hs := by
    change D.IsCapEval h₀ n w (V := V'.unop)
      (SheafOfModules.freeEval V' ((SheafOfModules.free (D.EvIdx M)).val.map f s))
    exact (D.isCapEval_map h₀ hwρ (leOfHom f.unop) hs).congr fun x b hb ↦
      (D.holFun_freeEval_map f s x hb).trans (holFun_map _ _ hb).symm
  isSheaf {V} s hs := by
    intro b hb
    obtain ⟨hbG, hbV⟩ := mem_img_iff.1 hb
    obtain ⟨O', i, hO', hbO'⟩ := hs ⟨b, hbG⟩ hbV
    obtain ⟨B, hB, hBO', hbB, t, ht, htv⟩ := hO' b (mem_img_iff.2 ⟨hbG, hbO'⟩)
    refine ⟨B, hB, hBO'.trans (img_mono (leOfHom i)), hbB, t, ht, fun b' hb' x ↦ ?_⟩
    rw [htv b' hb' x]
    exact D.holFun_freeEval_map i.op s x (hBO' hb')

end

end ComplexAnalytic.Cap.AnnulusDecomposition

namespace SheafOfModules.Submodule

open AlgebraicGeometry AlgebraicGeometry.LocallyRingedSpace

variable {Y : LocallyRingedSpace.{u}} {M : SheafOfModules.{u} Y.ringSheaf} (N : M.Submodule)

lemma val_sectRes {V V' : TopologicalSpace.Opens Y} (h : V' ≤ V)
    (s : N.toSheafOfModules.val.obj (op V)) :
    (sectRes N.toSheafOfModules h s).1 = sectRes M h s.1 :=
  rfl

lemma val_sum_smul {V : TopologicalSpace.Opens Y} {κ : Type*} [Fintype κ]
    (c : κ → Y.presheaf.obj (op V)) (s : κ → N.toSheafOfModules.val.obj (op V)) :
    (∑ k, c k • s k).1 = ∑ k, c k • (s k).1 := by
  change ((∑ k, c k • s k : N.obj (op V)) : M.val.obj (op V)) = _
  rw [Submodule.coe_sum]
  rfl

/-- **Relations in a subsheaf** are relations in the ambient sheaf. -/
theorem hasLocalModuleRelations (hM : HasLocalModuleRelations M) :
    HasLocalModuleRelations N.toSheafOfModules := by
  intro V q f x hx
  obtain ⟨W, hWV, k, g, hxW, hg, hgen⟩ := hM V q (fun i ↦ (f i).1) x hx
  refine ⟨W, hWV, k, g, hxW, fun l ↦ Subtype.ext ?_, fun W' hW' a ha ↦ hgen W' hW' a ?_⟩
  · rw [val_sum_smul]
    exact hg l
  · have := congrArg Subtype.val ha
    rw [val_sum_smul] at this
    exact this

end SheafOfModules.Submodule

namespace ComplexAnalytic.BoundedSections.WeierstrassForm

open AnalyticSpace Cap

variable {m : ℕ} {N N₀ : (AnalyticSpace.complexAffineSpace.{u} (m + 1)).Opens}
  (F : WeierstrassForm N N₀)

/-- The open of the base `G` given by an open subset of `G`. -/
def baseOpen (B : Set (Cm.{u} m)) (hB : IsOpen B) : (space F.baseOpens).Opens :=
  ⟨Subtype.val ⁻¹' B, hB.preimage continuous_subtype_val⟩

lemma mem_img_baseOpen {B : Set (Cm.{u} m)} {hB : IsOpen B} (hBG : B ⊆ F.G) {b : Cm.{u} m} :
    b ∈ img (F.baseOpen B hB) ↔ b ∈ B :=
  ⟨fun h ↦ (mem_img_iff.1 h).2, fun h ↦ mem_img_iff.2 ⟨hBG h, h⟩⟩

end ComplexAnalytic.BoundedSections.WeierstrassForm

namespace ComplexAnalytic.Cap.AnnulusDecomposition

open AnalyticSpace BoundedSections Complex.ProjectiveLineBundle AlgebraicGeometry.LocallyRingedSpace
open KummerModel (splitEquiv)

noncomputable section

variable {m : ℕ} {N N₀ : (AnalyticSpace.complexAffineSpace.{u} (m + 1)).Opens} (h₀ : N₀ ≤ N)
  {W : FiniteEtaleOver (space N₀)} {F : WeierstrassForm N N₀}
  (D : AnnulusDecomposition W F.G F.ρ) {n : ℕ} {M : ℕ} {w : Fin M → ℂ}

/-- The evaluation of a combination of sections over a larger open. -/
lemma evalVec_eq_sum_of_evalFun' {V V' B : Set (Cm.{u} m)} {hV : IsOpen V} {hB : IsOpen B}
    (hVG : V ⊆ F.G) (hV'V : V' ⊆ V) (hVB : V ⊆ B) (hwρ : ∀ ν, w ν ∈ overlap F.ρ) {K : ℕ}
    {t : W.left.presheaf.obj (op (preim h₀ W (tubeN N V hV)))}
    {s : Fin K → W.left.presheaf.obj (op (preim h₀ W (tubeN N B hB)))}
    {e : Fin K → Cm.{u} m → ℂ}
    (h : ∀ y ∈ preim h₀ W (tubeN N V hV), baseOf (pt W y) ∈ V' →
      evalFun t y = ∑ k, e k (baseOf (pt W y)) * evalFun (s k) y)
    {b : Cm.{u} m} (hb : b ∈ V') (x : Fin M × (Σ i, Fin (D.deg i))) :
    D.evalVec w t b x = ∑ k, e k b * D.evalVec w (s k) b x := by
  obtain ⟨y, hy, hyb, hval⟩ := D.exists_evalVec_eq_tube h₀ hwρ hVG (hV'V hb) x
  rw [hval, h y hy (hyb ▸ hb), hyb]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  have hle : tubeN N V hV ≤ tubeN N B hB := tubeN_mono hVB
  have hbV : (splitEquiv m).symm (b, w x.1) ∈ img (tubeN N V hV) := by
    rw [F.mem_img_tubeN hVG, Homeomorph.apply_symm_apply]
    exact ⟨hV'V hb, mem_ball_zero_iff.2 (hwρ x.1).2⟩
  rw [← D.evalVec_map hle hwρ (hVG (hV'V hb)) x hbV, hval, evalFun_map W _ _ hy]

lemma differentiableOn_evalVec_baseOpen (hwρ : ∀ ν, w ν ∈ overlap F.ρ) {B : Set (Cm.{u} m)}
    {hB : IsOpen B} (hBG : B ⊆ F.G) (a : W.left.presheaf.obj (op (preim h₀ W (tubeN N B hB))))
    (x : D.EvIdx M) :
    DifferentiableOn ℂ (fun b ↦ D.evalVec w a b x) (img (F.baseOpen B hB)) :=
  (D.differentiableOn_evalVec F.isOpen_G hwρ a x).mono fun b hb ↦ by
    have hbB := (F.mem_img_baseOpen hBG).1 hb
    refine ⟨hBG hbB, ?_⟩
    rw [F.mem_img_tubeN hBG, Homeomorph.apply_symm_apply]
    exact ⟨hbB, mem_ball_zero_iff.2 (hwρ x.1).2⟩

open Classical in
/-- The evaluation of a section of the cap over `B × ℙ¹`, as a section of `𝒮ₙ` over `B`. -/
def evalSec (hwρ : ∀ ν, w ν ∈ overlap F.ρ) {B : Set (Cm.{u} m)} {hB : IsOpen B} (hBG : B ⊆ F.G)
    {t : boundedSubring h₀ W (tubeN N B hB) × (D.ι → Cm.{u} m × ℂ → ℂ)}
    (ht : t ∈ D.capPole h₀ n (tubeN N B hB) (B ×ˢ ball 0 F.ρ)) :
    (D.evalSubmodule h₀ n hwρ).toSheafOfModules.val.obj (op (F.baseOpen B hB)) :=
  ⟨SheafOfModules.freeEvalSymm _ fun x ↦
    OkaRing.ofDifferentiableOn _ (D.differentiableOn_evalVec_baseOpen h₀ hwρ hBG t.1.1 x), by
    change D.IsCapEval h₀ n w (SheafOfModules.freeEval (R := (space F.baseOpens).ringSheaf)
      (op (F.baseOpen B hB)) (SheafOfModules.freeEvalSymm (op (F.baseOpen B hB)) _))
    rw [SheafOfModules.freeEval_freeEvalSymm]
    intro b hb
    refine ⟨B, hB, fun b' hb' ↦ (F.mem_img_baseOpen hBG).2 hb', (F.mem_img_baseOpen hBG).1 hb,
      t, ht, fun b' hb' x ↦ ?_⟩
    exact (holFun_ofDifferentiableOn (N := F.baseOpens) (V := F.baseOpen B hB)
      (D.differentiableOn_evalVec_baseOpen h₀ hwρ hBG t.1.1 x)
      ((F.mem_img_baseOpen hBG).2 hb')).symm⟩

open Classical in
lemma holFun_evalSec (hwρ : ∀ ν, w ν ∈ overlap F.ρ) {B : Set (Cm.{u} m)} {hB : IsOpen B}
    (hBG : B ⊆ F.G) {t : boundedSubring h₀ W (tubeN N B hB) × (D.ι → Cm.{u} m × ℂ → ℂ)}
    (ht : t ∈ D.capPole h₀ n (tubeN N B hB) (B ×ˢ ball 0 F.ρ)) (x : D.EvIdx M) {b : Cm.{u} m}
    (hb : b ∈ B) :
    holFun (V := F.baseOpen B hB) (SheafOfModules.freeEval _ (D.evalSec h₀ hwρ hBG ht).1 x) b =
      D.evalVec w t.1.1 b x := by
  change holFun (V := F.baseOpen B hB) (SheafOfModules.freeEval (R := (space F.baseOpens).ringSheaf)
    (op (F.baseOpen B hB)) (SheafOfModules.freeEvalSymm (op (F.baseOpen B hB)) _) x) b = _
  rw [SheafOfModules.freeEval_freeEvalSymm]
  exact holFun_ofDifferentiableOn _ ((F.mem_img_baseOpen hBG).2 hb)

lemma holFun_sum {V : (space F.baseOpens).Opens} {κ : Type*} [Fintype κ]
    (r : κ → (space F.baseOpens).presheaf.obj (op V)) {b : Cm.{u} m} (hb : b ∈ img V) :
    holFun (∑ k, r k) b = ∑ k, holFun (r k) b := by
  simp only [holFun_eq_eval _ hb, map_sum]

open Classical in
lemma holFun_freeEval_modRes (hwρ : ∀ ν, w ν ∈ overlap F.ρ) {V V' : (space F.baseOpens).Opens}
    (h : V' ≤ V) (s : (D.evalSubmodule h₀ n hwρ).toSheafOfModules.val.obj (op V))
    (x : D.EvIdx M) {b : Cm.{u} m} (hb : b ∈ img V') :
    holFun (V := V') (SheafOfModules.freeEval (op V') (modRes s V' h).1 x) b =
      holFun (V := V) (SheafOfModules.freeEval (op V) s.1 x) b :=
  D.holFun_freeEval_map (homOfLE h).op s.1 x hb

open Classical in
lemma holFun_freeEval_sum_smul (hwρ : ∀ ν, w ν ∈ overlap F.ρ) {V : (space F.baseOpens).Opens}
    {κ : Type*} [Fintype κ] (c : κ → (space F.baseOpens).presheaf.obj (op V))
    (s : κ → (D.evalSubmodule h₀ n hwρ).toSheafOfModules.val.obj (op V)) (x : D.EvIdx M)
    {b : Cm.{u} m} (hb : b ∈ img V) :
    holFun (V := V) (SheafOfModules.freeEval (op V) (∑ k, c k • s k).1 x) b =
      ∑ k, holFun (c k) b * holFun (V := V) (SheafOfModules.freeEval (op V) (s k).1 x) b := by
  rw [SheafOfModules.Submodule.val_sum_smul, map_sum, Finset.sum_apply]
  erw [holFun_sum _ hb]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  exact (congrArg (fun v ↦ holFun (V := V) (v x) b)
    ((SheafOfModules.freeEval (op V)).map_smul (c k) (s k).1)).trans (holFun_mul _ _ hb)


open Classical in
/-- **`𝒮ₙ` is locally finitely generated** if the sections of the cap are. -/
theorem isLocallyFinitelyGeneratedModule_evalSubmodule (hwρ : ∀ ν, w ν ∈ overlap F.ρ)
    (hloc : ∀ b ∈ F.G, D.CapLocallyFinite h₀ n b) :
    IsLocallyFinitelyGeneratedModule (D.evalSubmodule h₀ n hwρ).toSheafOfModules := by
  intro x
  obtain ⟨B, hB, hBG, hbB, K, s, hs, hgen⟩ := hloc x.1 x.2
  refine ⟨F.baseOpen B hB, K, fun k ↦ D.evalSec h₀ hwρ hBG (hs k), hbB,
    fun W' hW' τ y hy ↦ ?_⟩
  have hyW' : y.1 ∈ img W' := mem_img_iff.2 ⟨y.2, hy⟩
  have hτ : D.IsCapEval h₀ n w (SheafOfModules.freeEval (op W') τ.1) := τ.2
  obtain ⟨B', hB', hB'W', hyB', t', ht', ht'v⟩ := hτ y.1 hyW'
  have hB'B : B' ⊆ B := fun b hb ↦ (F.mem_img_baseOpen hBG).1 (img_mono hW' (hB'W' hb))
  have hB'G : B' ⊆ F.G := hB'B.trans hBG
  obtain ⟨V', hV'B', hV', hyV', e, he, hrel⟩ := hgen y.1 (hB'B hyB') B' hB' hB'B hyB' t' ht'
  set W'' : (space F.baseOpens).Opens := W' ⊓ F.baseOpen V' hV'
  have hW''V' : ∀ b ∈ img W'', b ∈ V' := fun b hb ↦ (mem_img_iff.1 hb).2.2
  refine ⟨W'', inf_le_left, ⟨hy, hyV'⟩,
    fun k ↦ OkaRing.ofDifferentiableOn (e k) ((he k).mono hW''V'), ?_⟩
  refine Subtype.ext (SheafOfModules.freeEval_injective _ (funext fun x ↦ ?_))
  refine eq_of_holFun_eq fun b hb ↦ ?_
  have hbV' := hW''V' b hb
  erw [SheafOfModules.Submodule.val_sectRes, SheafOfModules.Submodule.val_sum_smul, map_sum]
  simp only [map_smul, Finset.sum_apply]
  erw [holFun_sum _ hb]
  erw [D.holFun_freeEval_map _ _ x hb]
  refine (ht'v b (hV'B' hbV') x).symm.trans ?_
  rw [D.evalVec_eq_sum_of_evalFun' h₀ hB'G hV'B' hB'B hwρ hrel hbV' x]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  erw [holFun_mul _ _ hb]
  erw [SheafOfModules.Submodule.val_sectRes, D.holFun_freeEval_map _ _ x hb]
  rw [D.holFun_evalSec h₀ hwρ hBG (hs k) x (hB'B (hV'B' hbV')),
    holFun_ofDifferentiableOn _ hb]

end

end ComplexAnalytic.Cap.AnnulusDecomposition
