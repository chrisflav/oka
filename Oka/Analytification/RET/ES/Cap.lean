/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analysis.Complex.KummerCoverAnnulus
import Oka.Analysis.Complex.KummerExtension
import Oka.Analytification.GAGA.ProjectiveLineBundle
import Oka.Analytification.RET.ES.BoundedSections

/-!
# The trivial `ℙ¹`-cap

Let `G ⊆ ℂ^m` be convex and open, `ρ > 1`, and let `p : W → N°` be a finite étale cover with
`N° ⊆ ℂ^{m+1}` open and containing the annulus region `G × {ρ⁻¹ < ‖w‖ < ρ}` (`w` the coordinate
`0`), the overlap of the charts `{‖w‖ < ρ}` and `{‖w'‖ < ρ}`, `w' = w⁻¹`, of `G × ℙ¹`
(`Complex.ProjectiveLineBundle.overlap`). This file constructs the extension of `W` over the chart
at infinity (Grauert–Remmert, *Komplexe Räume*, Satz 34 and Hilfssatz 5).

* **Kummer decomposition** (`ComplexAnalytic.Cap.AnnulusDecomposition.nonempty`): over the annulus,
  `W` is a finite disjoint union of Kummer covers `(b, u) ↦ (b, u^{kᵢ})` of
  `G × {ρ⁻¹ < ‖u‖^{kᵢ} < ρ}`, and `∑ᵢ kᵢ` is the degree of `W`
  (`ComplexAnalytic.Cap.AnnulusDecomposition.card_fiberFinset`). Sections of `𝒪_W` are holomorphic
  functions of the Kummer coordinates
  (`ComplexAnalytic.Cap.AnnulusDecomposition.differentiableOn_kummerVal`).
* **The cap** (`ComplexAnalytic.Cap.AnnulusDecomposition.capSubring`): in the Kummer coordinate
  `u' = u⁻¹` the `i`-th piece extends over `w' = 0` as the Kummer cover `u' ↦ u'^{kᵢ}` branched
  at `∞` only. The sections of the extended sheaf over an open of `G × ℙ¹`, given by `V` in the
  chart `w` and `V'` in the chart `w'`, are the pairs of a section `s` of the sheaf `𝒜` of bounded
  sections of `p_* 𝒪_W` over `V` and holomorphic functions `fᵢ` on `{(b, u') | (b, u'^{kᵢ}) ∈ V'}`
  with `s = fᵢ(b, u⁻¹)` on the `i`-th piece over the overlap. This is a ring, compatible with
  restriction (`ComplexAnalytic.Cap.AnnulusDecomposition.capRestrict_mem`) and receiving the
  holomorphic functions on `G × ℙ¹`
  (`ComplexAnalytic.Cap.AnnulusDecomposition.algebraMap_mem_capSubring`). At infinity it is the free
  algebra `∏ᵢ 𝒪[u']/(u'^{kᵢ} - w')` of rank `∑ᵢ kᵢ`: `fᵢ = ∑_{j < kᵢ} u'ʲ gᵢⱼ(b, u'^{kᵢ})` with
  unique holomorphic `gᵢⱼ` (`ComplexAnalytic.Cap.exists_coeff_eqOn`,
  `ComplexAnalytic.Cap.eqOn_of_coeff`).
* **Sheets over a disc** (Hilfssatz 5): over a disc `G × {‖w - w₁‖ < ε}` inside the annulus, `W`
  is trivial. The sheets `ComplexAnalytic.Cap.AnnulusDecomposition.sheet`, with Kummer coordinates
  `(b, ζʲ w^{1/kᵢ})`, enumerate the fibres (`ComplexAnalytic.Cap.AnnulusDecomposition.sheetEquiv`)
  and are open (`ComplexAnalytic.Cap.AnnulusDecomposition.isOpen_sheetSet`). The values of a
  section on the sheets (`ComplexAnalytic.Cap.AnnulusDecomposition.sheetVal`) are holomorphic
  (`ComplexAnalytic.Cap.AnnulusDecomposition.differentiableOn_sheetVal`), determine the section
  (`ComplexAnalytic.Cap.AnnulusDecomposition.eq_of_sheetVal_eq`) and can be prescribed
  arbitrarily (`ComplexAnalytic.Cap.AnnulusDecomposition.exists_sheetVal_eq`). Since the annulus
  lies in both charts, no change of the coordinate `w` is needed to place the disc in the chart
  at `0`.

## Main definitions

- `ComplexAnalytic.Cap.AnnulusDecomposition W G ρ`: a decomposition of `W` over the annulus into
  Kummer covers.
- `ComplexAnalytic.Cap.AnnulusDecomposition.kummerVal`: the values of a section in the Kummer
  coordinates.
- `ComplexAnalytic.Cap.AnnulusDecomposition.sheet`,
  `ComplexAnalytic.Cap.AnnulusDecomposition.sheetVal`:
  the sheets over a disc and the values of a section on them.
- `ComplexAnalytic.Cap.AnnulusDecomposition.capSubring h₀ V V'`: the sections of the cap.
-/

open CategoryTheory Opposite Topology Set Filter

universe u

namespace ComplexAnalytic.Cap

open AnalyticSpace BoundedSections KummerModel Complex.ProjectiveLineBundle

noncomputable section

variable {m : ℕ}

/-- The points of `ℂ^m`. -/
abbrev Cm (m : ℕ) : Type u := ULift.{u} (Fin m) → ℂ

lemma differentiable_splitEquiv_symm :
    Differentiable ℂ (splitEquiv.{u} m).symm := by
  refine differentiable_pi.2 fun ⟨j⟩ ↦ ?_
  cases j using Fin.cases
  · exact differentiable_snd
  · change Differentiable ℂ fun p : Cm.{u} m × ℂ ↦ p.1 ⟨_⟩
    fun_prop

lemma differentiable_splitEquiv : Differentiable ℂ (splitEquiv.{u} m) := by
  change Differentiable ℂ fun x : Cn.{u} (m + 1) ↦
    ((fun i : ULift.{u} (Fin m) ↦ x ⟨i.down.succ⟩), x zero)
  exact (differentiable_pi.2 fun i ↦ differentiable_apply _).prodMk (differentiable_apply _)

/-- The region `G × {ρ⁻¹ < ‖w‖ < ρ}` of `ℂ^{m+1}`, with `w` the coordinate `0`. -/
def annulusRegion (G : Set (Cm.{u} m)) (ρ : ℝ) : Set (Cn.{u} (m + 1)) :=
  splitEquiv m ⁻¹' (G ×ˢ overlap ρ)

variable {N₀ : (AnalyticSpace.complexAffineSpace.{u} (m + 1)).Opens}
  (W : FiniteEtaleOver (space N₀)) (G : Set (Cm.{u} m)) (ρ : ℝ)

/-- A **decomposition of `W` over the annulus** `G × {ρ⁻¹ < ‖w‖ < ρ}` into Kummer covers: an open
embedding `Φ` of `∐ᵢ G × {ρ⁻¹ < ‖u‖^{kᵢ} < ρ}` onto the part of `W` over the annulus, under which
the projection to `ℂ^{m+1}` becomes `(b, u) ↦ (b, u^{kᵢ})` on the `i`-th piece. -/
structure AnnulusDecomposition where
  /-- The index set of the Kummer pieces. -/
  ι : Type u
  [fintype : Fintype ι]
  /-- The degree of the `i`-th Kummer piece. -/
  deg : ι → ℕ+
  /-- The embedding of the Kummer pieces into `W`. -/
  toFun : (Σ i, KummerAnnulus.base G ρ⁻¹ ρ (deg i)) → W.left
  isOpenEmbedding : IsOpenEmbedding toFun
  range_eq : range toFun = pt W ⁻¹' annulusRegion G ρ
  splitEquiv_pt (i : ι) (y : KummerAnnulus.base G ρ⁻¹ ρ (deg i)) :
    splitEquiv m (pt W (toFun ⟨i, y⟩)) = (y.1.1, y.1.2 ^ (deg i : ℕ))

attribute [instance] AnnulusDecomposition.fintype

variable {W G ρ}

lemma overlap_eq_annulus_one {ρ : ℝ} :
    overlap ρ = KummerAnnulus.annulus ρ⁻¹ ρ 1 := by
  ext w
  simp [overlap, KummerAnnulus.annulus]

/-- **The part of a finite étale cover over the annulus is a disjoint union of Kummer covers**,
for `G` convex and open. -/
theorem AnnulusDecomposition.nonempty [T2Space W.left] (hG : Convex ℝ G) (hGo : IsOpen G)
    (hρ : 1 < ρ) (hA : ∀ x ∈ annulusRegion G ρ, x ∈ N₀) :
    Nonempty (AnnulusDecomposition W G ρ) := by
  have hρ0 : 0 < ρ := zero_lt_one.trans hρ
  have hρi : ρ⁻¹ < ρ := (inv_lt_one_of_one_lt₀ hρ).trans hρ
  set f := (cov W).toLRSHom.base
  have hf : IsCoveringMap f := isCoveringMap_base_of_isFiniteEtale (cov W)
  let s : Set (space N₀) := {y | y.1 ∈ annulusRegion G ρ}
  have hs : IsOpen s := by
    refine IsOpen.preimage continuous_subtype_val ?_
    refine IsOpen.preimage (splitEquiv m).continuous (hGo.prod (isOpen_overlap ρ))
  let e : s ≃ₜ KummerAnnulus.base G ρ⁻¹ ρ 1 :=
    { toFun y := ⟨splitEquiv m y.1.1, by
        have := y.2
        simp only [s, annulusRegion, mem_setOf_eq, overlap_eq_annulus_one] at this
        exact this⟩
      invFun x := ⟨⟨(splitEquiv m).symm x.1, hA _ (by
        rw [annulusRegion, mem_preimage, Homeomorph.apply_symm_apply, overlap_eq_annulus_one]
        exact x.2)⟩, by
        change (splitEquiv m).symm x.1 ∈ annulusRegion G ρ
        rw [annulusRegion, mem_preimage, Homeomorph.apply_symm_apply, overlap_eq_annulus_one]
        exact x.2⟩
      left_inv y := by
        apply Subtype.ext
        apply Subtype.ext
        exact (splitEquiv m).symm_apply_apply _
      right_inv x := Subtype.ext ((splitEquiv m).apply_symm_apply x.1)
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact (splitEquiv m).continuous.comp (continuous_subtype_val.comp continuous_subtype_val)
      continuous_invFun := by
        refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
        exact (splitEquiv m).symm.continuous.comp continuous_subtype_val }
  set p := e ∘ s.restrictPreimage f
  have hp : IsCoveringMap p := (hf.restrictPreimage s).homeomorph_comp e
  have hfin (y : KummerAnnulus.base G ρ⁻¹ ρ 1) : (p ⁻¹' {y}).Finite := by
    have h₁ := IsFinite.finite_fiber (f := cov W) (e.symm y).1
    refine Finite.of_finite_image (f := Subtype.val) ?_ Subtype.val_injective.injOn
    refine (Set.toFinite (f ⁻¹' {(e.symm y).1})).subset ?_
    rintro _ ⟨w, hw, rfl⟩
    change f w.1 = (e.symm y).1
    have : e.symm (p w) = e.symm y := congrArg e.symm hw
    change e.symm (e (s.restrictPreimage f w)) = _ at this
    rw [Homeomorph.symm_apply_apply] at this
    exact congrArg Subtype.val this
  obtain ⟨hι, k, Φ, hΦ⟩ := hp.exists_homeomorph_sigma_kummerAnnulus hG hGo
    (inv_nonneg.2 hρ0.le) hρi hfin
  haveI := hι
  refine ⟨{ ι := ZerothHomotopy (f ⁻¹' s)
            fintype := Fintype.ofFinite _
            deg := k
            toFun := Subtype.val ∘ Φ
            isOpenEmbedding := (hs.preimage hf.continuous).isOpenEmbedding_subtypeVal.comp
              Φ.isOpenEmbedding
            range_eq := ?_
            splitEquiv_pt := fun i y ↦ ?_ }⟩
  · rw [range_comp, Φ.range_coe, image_univ, Subtype.range_coe]
    rfl
  · have := congrArg Subtype.val (hΦ i y)
    exact this

namespace AnnulusDecomposition

variable (D : AnnulusDecomposition W G ρ)

lemma pt_toFun (i : D.ι) (y : KummerAnnulus.base G ρ⁻¹ ρ (D.deg i)) :
    pt W (D.toFun ⟨i, y⟩) = (splitEquiv m).symm (y.1.1, y.1.2 ^ (D.deg i : ℕ)) := by
  rw [← D.splitEquiv_pt, Homeomorph.symm_apply_apply]

lemma continuous_toFun_mk (i : D.ι) : Continuous fun y ↦ D.toFun ⟨i, y⟩ :=
  D.isOpenEmbedding.continuous.comp continuous_sigmaMk

lemma toFun_injective : Function.Injective D.toFun :=
  D.isOpenEmbedding.injective

open Classical in
/-- The values of a section `a` of `𝒪_W` on the `i`-th Kummer piece, as a function of the Kummer
coordinates `(b, u)` (zero outside the piece). -/
def kummerVal {O : W.left.Opens} (a : W.left.presheaf.obj (op O)) (i : D.ι) (z : Cm.{u} m × ℂ) :
    ℂ :=
  if h : z ∈ KummerAnnulus.base G ρ⁻¹ ρ (D.deg i) then evalFun a (D.toFun ⟨i, ⟨z, h⟩⟩) else 0

lemma kummerVal_of_mem {O : W.left.Opens} (a : W.left.presheaf.obj (op O)) (i : D.ι)
    {z : Cm.{u} m × ℂ} (h : z ∈ KummerAnnulus.base G ρ⁻¹ ρ (D.deg i)) :
    D.kummerVal a i z = evalFun a (D.toFun ⟨i, ⟨z, h⟩⟩) := by
  classical
  rw [kummerVal, dif_pos h]

/-- The Kummer coordinates `(b, u)` on the `i`-th piece of the points of `O`. -/
def pieceSet (O : W.left.Opens) (i : D.ι) : Set (Cm.{u} m × ℂ) :=
  {z | ∃ h : z ∈ KummerAnnulus.base G ρ⁻¹ ρ (D.deg i), D.toFun ⟨i, ⟨z, h⟩⟩ ∈ O}

lemma isOpen_pieceSet (hGo : IsOpen G) (O : W.left.Opens) (i : D.ι) :
    IsOpen (D.pieceSet O i) := by
  have : D.pieceSet O i = Subtype.val '' ((fun y ↦ D.toFun ⟨i, y⟩) ⁻¹' O) := by
    ext z
    exact ⟨fun ⟨h, hz⟩ ↦ ⟨⟨z, h⟩, hz, rfl⟩, fun ⟨y, hy, hyz⟩ ↦ hyz ▸ ⟨y.2, hy⟩⟩
  rw [this]
  exact (KummerAnnulus.isOpen_base _ _ hGo _).isOpenMap_subtype_val _
    (O.isOpen.preimage (D.continuous_toFun_mk i))

lemma pieceSet_mono {O O' : W.left.Opens} (h : O' ≤ O) (i : D.ι) :
    D.pieceSet O' i ⊆ D.pieceSet O i :=
  fun _ ⟨hz, hz'⟩ ↦ ⟨hz, h hz'⟩

/-- **Sections of `𝒪_W` are holomorphic in the Kummer coordinates.** -/
theorem differentiableOn_kummerVal (hGo : IsOpen G) {O : W.left.Opens}
    (a : W.left.presheaf.obj (op O)) (i : D.ι) :
    DifferentiableOn ℂ (D.kummerVal a i) (D.pieceSet O i) := by
  rintro z ⟨h, hz⟩
  obtain ⟨O₁, hwO₁, -, hsheet⟩ := exists_sheet W (D.toFun ⟨i, ⟨z, h⟩⟩)
  obtain ⟨F, hFd, hF⟩ := hsheet (O' := O₁ ⊓ O) inf_le_left
    (W.left.presheaf.map (homOfLE inf_le_right).op a)
  have hU : D.pieceSet (O₁ ⊓ O) i ∈ 𝓝 z :=
    (D.isOpen_pieceSet hGo _ i).mem_nhds ⟨h, hwO₁, hz⟩
  have heq : D.kummerVal a i =ᶠ[𝓝 z] fun z' ↦
      F ((splitEquiv m).symm (Kummer.powMap (D.deg i : ℕ) z')) := by
    filter_upwards [hU] with z' ⟨h', hz'⟩
    rw [D.kummerVal_of_mem a i h', evalFun_of_mem a hz'.2, ← eval_presheaf_map W.left
      (homOfLE inf_le_right).op _ hz', hF _ hz', D.pt_toFun]
    rfl
  have hd := hFd _ ⟨hwO₁, hz⟩
  rw [D.pt_toFun] at hd
  exact ((hd.comp z ((differentiable_splitEquiv_symm _).comp z
    (Kummer.differentiable_powMap _ z))).congr_of_eventuallyEq heq).differentiableWithinAt

/-! ### Sheets over a disc -/

/-- A holomorphic branch of the `k`-th root near `w₁ ≠ 0`,
`w ↦ w₁^{1/k} exp(log(w / w₁) / k)`. -/
def kroot (k : ℕ) (w₁ w : ℂ) : ℂ :=
  w₁ ^ ((k : ℂ)⁻¹) * Complex.exp (Complex.log (w / w₁) / k)

lemma kroot_pow {k : ℕ} (hk : k ≠ 0) {w₁ w : ℂ} (hw₁ : w₁ ≠ 0) (hw : w ≠ 0) :
    kroot k w₁ w ^ k = w := by
  rw [kroot, mul_pow, Complex.cpow_nat_inv_pow _ hk, ← Complex.exp_nat_mul,
    mul_div_cancel₀ _ (by exact_mod_cast hk), Complex.exp_log (div_ne_zero hw hw₁),
    mul_div_cancel₀ _ hw₁]

lemma differentiableAt_kroot (k : ℕ) {w₁ w : ℂ} (hw : w / w₁ ∈ Complex.slitPlane) :
    DifferentiableAt ℂ (kroot k w₁) w := by
  unfold kroot
  refine (differentiableAt_const _).mul (((differentiableAt_id.div_const w₁).clog hw).div_const
    _).cexp

lemma div_mem_slitPlane {w₁ w : ℂ} (hw : ‖w - w₁‖ < ‖w₁‖) : w / w₁ ∈ Complex.slitPlane := by
  have hw₁ : 0 < ‖w₁‖ := (norm_nonneg _).trans_lt hw
  have : w / w₁ = 1 + (w - w₁) / w₁ := by
    field_simp [norm_pos_iff.1 hw₁]
    ring
  rw [this]
  refine Complex.mem_slitPlane_of_norm_lt_one ?_
  rwa [norm_div, div_lt_one hw₁]

/-- The Kummer coordinates `(b, ζʲ w^{1/k})` of the `j`-th sheet over `(b, w)`. -/
def sheetCoord (k j : ℕ) (w₁ : ℂ) (z : Cm.{u} m × ℂ) : Cm.{u} m × ℂ :=
  (z.1, Kummer.zeta k ^ j * kroot k w₁ z.2)

/-- The disc region `G × {‖w - w₁‖ < ε}`. -/
def discRegion (G : Set (Cm.{u} m)) (w₁ : ℂ) (ε : ℝ) : Set (Cm.{u} m × ℂ) :=
  G ×ˢ Metric.ball w₁ ε

variable {w₁ : ℂ} {ε : ℝ}

lemma norm_sub_lt_of_mem_discRegion (hε : Metric.ball w₁ ε ⊆ overlap ρ) (hρ : 0 < ρ)
    {z : Cm.{u} m × ℂ} (hz : z ∈ discRegion G w₁ ε) : ‖z.2 - w₁‖ < ‖w₁‖ := by
  have h₁ : ε ≤ ‖w₁‖ := by
    by_contra h
    have h0 : (0 : ℂ) ∈ Metric.ball w₁ ε := by
      rw [Metric.mem_ball, dist_comm, dist_zero_right]
      exact lt_of_not_ge h
    exact ne_zero_of_mem_overlap hρ (hε h0) rfl
  exact (dist_eq_norm z.2 w₁ ▸ hz.2 : ‖z.2 - w₁‖ < ε).trans_le h₁

lemma sheetCoord_pow (hε : Metric.ball w₁ ε ⊆ overlap ρ) (hρ : 0 < ρ) {k : ℕ} (hk : k ≠ 0)
    (j : ℕ) {z : Cm.{u} m × ℂ} (hz : z ∈ discRegion G w₁ ε) :
    (sheetCoord k j w₁ z).2 ^ k = z.2 := by
  have hz0 := ne_zero_of_mem_overlap hρ (hε hz.2)
  have hw₁ : w₁ ≠ 0 :=
    norm_pos_iff.1 ((norm_nonneg _).trans_lt (norm_sub_lt_of_mem_discRegion hε hρ hz))
  rw [sheetCoord, mul_pow, ← pow_mul, mul_comm j k, pow_mul,
    (Kummer.isPrimitiveRoot_zeta (Nat.pos_of_ne_zero hk)).pow_eq_one, one_pow, one_mul,
    kroot_pow hk hw₁ hz0]

lemma pos_of_mem_overlap {w : ℂ} (hw : w ∈ overlap ρ) : 0 < ρ :=
  (norm_nonneg w).trans_lt hw.2

lemma sheetCoord_mem_base (hε : Metric.ball w₁ ε ⊆ overlap ρ) (k : ℕ+) (j : ℕ)
    {z : Cm.{u} m × ℂ} (hz : z ∈ discRegion G w₁ ε) :
    sheetCoord k j w₁ z ∈ KummerAnnulus.base G ρ⁻¹ ρ k := by
  have h := hε hz.2
  refine ⟨hz.1, ?_⟩
  rw [KummerAnnulus.annulus, mem_setOf_eq, ← norm_pow,
    sheetCoord_pow hε (pos_of_mem_overlap h) k.ne_zero j hz]
  exact h

/-- The `(i, j)`-th **sheet of `W` over the disc** `G × {‖w - w₁‖ < ε}`: the point with Kummer
coordinates `(b, ζʲ w^{1/kᵢ})` on the `i`-th piece. -/
def sheet (hε : Metric.ball w₁ ε ⊆ overlap ρ) (i : D.ι) (j : ℕ) (z : Cm.{u} m × ℂ)
    (hz : z ∈ discRegion G w₁ ε) : W.left :=
  D.toFun ⟨i, ⟨sheetCoord (D.deg i) j w₁ z, sheetCoord_mem_base hε (D.deg i) j hz⟩⟩

variable (hε : Metric.ball w₁ ε ⊆ overlap ρ)

lemma splitEquiv_pt_sheet (i : D.ι) (j : ℕ) {z : Cm.{u} m × ℂ} (hz : z ∈ discRegion G w₁ ε) :
    splitEquiv m (pt W (D.sheet hε i j z hz)) = z := by
  rw [sheet, D.splitEquiv_pt]
  exact Prod.ext rfl (sheetCoord_pow hε (pos_of_mem_overlap (hε hz.2)) (D.deg i).ne_zero j hz)

lemma pt_sheet (i : D.ι) (j : ℕ) {z : Cm.{u} m × ℂ} (hz : z ∈ discRegion G w₁ ε) :
    pt W (D.sheet hε i j z hz) = (splitEquiv m).symm z := by
  exact (splitEquiv m).eq_symm_apply.2 (D.splitEquiv_pt_sheet hε i j hz)

include hε in
lemma kroot_ne_zero {k : ℕ} (hk : k ≠ 0) {z : Cm.{u} m × ℂ} (hz : z ∈ discRegion G w₁ ε) :
    kroot k w₁ z.2 ≠ 0 := by
  have hρ := pos_of_mem_overlap (hε hz.2)
  have hw₁ : w₁ ≠ 0 :=
    norm_pos_iff.1 ((norm_nonneg _).trans_lt (norm_sub_lt_of_mem_discRegion hε hρ hz))
  intro h
  have := kroot_pow hk hw₁ (ne_zero_of_mem_overlap hρ (hε hz.2))
  rw [h, zero_pow hk] at this
  exact ne_zero_of_mem_overlap hρ (hε hz.2) this.symm

/-- **The sheets over the disc are disjoint.** -/
theorem sheet_injective {i i' : D.ι} {j j' : ℕ} (hj : j < D.deg i) (hj' : j' < D.deg i')
    {z : Cm.{u} m × ℂ} (hz : z ∈ discRegion G w₁ ε)
    (h : D.sheet hε i j z hz = D.sheet hε i' j' z hz) : i = i' ∧ j = j' := by
  have h' := Sigma.mk.inj_iff.1 (D.toFun_injective h)
  obtain ⟨rfl, h''⟩ := h'
  refine ⟨rfl, ?_⟩
  have h₂ := congrArg (fun y : KummerAnnulus.base G ρ⁻¹ ρ (D.deg i) ↦ y.1.2) (eq_of_heq h'')
  simp only [sheetCoord] at h₂
  exact (Kummer.isPrimitiveRoot_zeta (D.deg i).pos).pow_inj hj hj'
    (mul_right_cancel₀ (kroot_ne_zero hε (D.deg i).ne_zero hz) h₂)

/-- **The sheets over the disc exhaust the fibres.** -/
theorem exists_sheet_eq {z : Cm.{u} m × ℂ} (hz : z ∈ discRegion G w₁ ε) {w : W.left}
    (hw : splitEquiv m (pt W w) = z) : ∃ i, ∃ j < (D.deg i : ℕ), D.sheet hε i j z hz = w := by
  have hwA : w ∈ pt W ⁻¹' annulusRegion G ρ := by
    change splitEquiv m (pt W w) ∈ G ×ˢ overlap ρ
    rw [hw]
    exact ⟨hz.1, hε hz.2⟩
  rw [← D.range_eq] at hwA
  obtain ⟨⟨i, y⟩, rfl⟩ := hwA
  rw [D.splitEquiv_pt] at hw
  haveI : NeZero (D.deg i : ℕ) := ⟨(D.deg i).ne_zero⟩
  have hkr := kroot_ne_zero hε (D.deg i).ne_zero hz
  have hρ := pos_of_mem_overlap (hε hz.2)
  have hpow : (y.1.2 / kroot (D.deg i) w₁ z.2) ^ (D.deg i : ℕ) = 1 := by
    have h₁ : y.1.2 ^ (D.deg i : ℕ) = z.2 := congrArg Prod.snd hw
    have h₂ := sheetCoord_pow hε hρ (D.deg i).ne_zero 0 hz
    simp only [sheetCoord, pow_zero, one_mul] at h₂
    rw [div_pow, h₁, h₂, div_self (ne_zero_of_mem_overlap hρ (hε hz.2))]
  obtain ⟨j, hj, hζ⟩ := (Kummer.isPrimitiveRoot_zeta (D.deg i).pos).eq_pow_of_pow_eq_one hpow
  refine ⟨i, j, hj, congrArg D.toFun (Sigma.ext rfl (heq_of_eq (Subtype.ext ?_)))⟩
  refine Prod.ext ?_ ?_
  · exact (congrArg Prod.fst hw).symm
  · change Kummer.zeta _ ^ j * kroot _ w₁ z.2 = y.1.2
    rw [hζ, div_mul_cancel₀ _ hkr]

/-- The sheets over a point `z` of the disc, as an enumeration of the fibre over `z`. -/
def sheetEquiv {z : Cm.{u} m × ℂ} (hz : z ∈ discRegion G w₁ ε) :
    (Σ i, Fin (D.deg i)) ≃ {w : W.left // splitEquiv m (pt W w) = z} :=
  Equiv.ofBijective (fun ij ↦ ⟨D.sheet hε ij.1 ij.2 z hz, D.splitEquiv_pt_sheet hε _ _ hz⟩)
    ⟨fun ⟨i, j⟩ ⟨i', j'⟩ h ↦ by
      obtain ⟨rfl, h'⟩ := D.sheet_injective hε j.2 j'.2 hz (congrArg Subtype.val h)
      rw [Fin.ext h'],
    fun ⟨w, hw⟩ ↦ by
      obtain ⟨i, j, hj, h⟩ := D.exists_sheet_eq hε hz hw
      exact ⟨⟨i, ⟨j, hj⟩⟩, Subtype.ext h⟩⟩

lemma coe_sheetEquiv_apply {z : Cm.{u} m × ℂ} (hz : z ∈ discRegion G w₁ ε)
    (ij : Σ i, Fin (D.deg i)) :
    (D.sheetEquiv hε hz ij : W.left) = D.sheet hε ij.1 ij.2 z hz :=
  rfl

omit hε in
/-- **The degree of `W` over the annulus is `∑ᵢ kᵢ`.** -/
theorem card_fiberFinset {x : Cn.{u} (m + 1)} (hx : x ∈ annulusRegion G ρ) :
    (fiberFinset W x).card = ∑ i, (D.deg i : ℕ) := by
  obtain ⟨ε, hε0, hε⟩ := Metric.isOpen_iff.1 (isOpen_overlap ρ) _ hx.2
  have hz : splitEquiv m x ∈ discRegion G (splitEquiv m x).2 ε :=
    ⟨hx.1, Metric.mem_ball_self hε0⟩
  have e : {w | pt W w = x} ≃ Σ i, Fin (D.deg i) :=
    (Equiv.subtypeEquivRight fun w ↦ by
      simp only [mem_setOf_eq]
      exact ⟨fun h ↦ h ▸ rfl, fun h ↦ (splitEquiv m).injective h⟩).trans
      (D.sheetEquiv hε hz).symm
  rw [fiberFinset, ← Nat.card_eq_card_finite_toFinset, Nat.card_congr e,
    Nat.card_eq_fintype_card, Fintype.card_sigma]
  simp

/-- The value of a section `a` of `𝒪_W` on the `(i, j)`-th sheet over the disc, as a function of
the point `(b, w)` below. -/
def sheetVal {O : W.left.Opens} (a : W.left.presheaf.obj (op O)) (i : D.ι) (j : ℕ)
    (z : Cm.{u} m × ℂ) : ℂ :=
  D.kummerVal a i (sheetCoord (D.deg i) j w₁ z)

lemma evalFun_sheet {O : W.left.Opens} (a : W.left.presheaf.obj (op O)) (i : D.ι) (j : ℕ)
    {z : Cm.{u} m × ℂ} (hz : z ∈ discRegion G w₁ ε) :
    evalFun a (D.sheet hε i j z hz) = D.sheetVal (w₁ := w₁) a i j z :=
  (D.kummerVal_of_mem a i _).symm

include hε in
lemma differentiableAt_sheetCoord (k j : ℕ) {z : Cm.{u} m × ℂ} (hz : z ∈ discRegion G w₁ ε) :
    DifferentiableAt ℂ (sheetCoord k j w₁) z := by
  have hρ := pos_of_mem_overlap (hε hz.2)
  have hk := differentiableAt_kroot k (div_mem_slitPlane (norm_sub_lt_of_mem_discRegion hε hρ hz))
  exact differentiableAt_fst.prodMk
    ((differentiableAt_const _).mul (hk.comp z differentiableAt_snd))

/-- **Values on the sheets over the disc are holomorphic**: for a section `a` of `𝒪_W` over `O`,
the value on the `(i, j)`-th sheet is holomorphic on the points of the disc whose sheet lies in
`O`. -/
theorem differentiableOn_sheetVal (hGo : IsOpen G) {O : W.left.Opens}
    (a : W.left.presheaf.obj (op O)) (i : D.ι) (j : ℕ) :
    DifferentiableOn ℂ (D.sheetVal (w₁ := w₁) a i j)
      {z | ∃ hz : z ∈ discRegion G w₁ ε, D.sheet hε i j z hz ∈ O} := by
  rintro z ⟨hz, hzO⟩
  have hmem : sheetCoord (D.deg i) j w₁ z ∈ D.pieceSet O i :=
    ⟨sheetCoord_mem_base hε (D.deg i) j hz, hzO⟩
  have hd := (D.differentiableOn_kummerVal hGo a i).differentiableAt
    ((D.isOpen_pieceSet hGo O i).mem_nhds hmem)
  exact (hd.comp z (differentiableAt_sheetCoord hε _ j hz)).differentiableWithinAt

/-! ### Algebraic properties of the values -/

section Values

variable {O : W.left.Opens} {a b : W.left.presheaf.obj (op O)} {i : D.ι} {z : Cm.{u} m × ℂ}

lemma kummerVal_mul (hz : z ∈ D.pieceSet O i) :
    D.kummerVal (a * b) i z = D.kummerVal a i z * D.kummerVal b i z := by
  obtain ⟨h, hO⟩ := hz
  simp only [D.kummerVal_of_mem _ _ h, evalFun_of_mem _ hO, map_mul]

lemma kummerVal_add (hz : z ∈ D.pieceSet O i) :
    D.kummerVal (a + b) i z = D.kummerVal a i z + D.kummerVal b i z := by
  obtain ⟨h, hO⟩ := hz
  simp only [D.kummerVal_of_mem _ _ h, evalFun_of_mem _ hO, map_add]

lemma kummerVal_neg (hz : z ∈ D.pieceSet O i) : D.kummerVal (-a) i z = -D.kummerVal a i z := by
  obtain ⟨h, hO⟩ := hz
  simp only [D.kummerVal_of_mem _ _ h, evalFun_of_mem _ hO, map_neg]

variable (O) in
lemma kummerVal_one (hz : z ∈ D.pieceSet O i) :
    D.kummerVal (1 : W.left.presheaf.obj (op O)) i z = 1 := by
  obtain ⟨h, hO⟩ := hz
  simp only [D.kummerVal_of_mem _ _ h, evalFun_of_mem _ hO, map_one]

variable (O) in
lemma kummerVal_zero : D.kummerVal (0 : W.left.presheaf.obj (op O)) i z = 0 := by
  classical
  unfold kummerVal
  split_ifs with h
  · by_cases hO : D.toFun ⟨i, ⟨z, h⟩⟩ ∈ O
    · rw [evalFun_of_mem _ hO, map_zero]
    · rw [evalFun, dif_neg hO]
  · rfl

lemma kummerVal_map {O' : W.left.Opens} (hO : O' ≤ O) (hz : z ∈ D.pieceSet O' i) :
    D.kummerVal (W.left.presheaf.map (homOfLE hO).op a) i z = D.kummerVal a i z := by
  obtain ⟨h, hO'⟩ := hz
  rw [D.kummerVal_of_mem _ _ h, D.kummerVal_of_mem _ _ h, evalFun_of_mem _ hO',
    evalFun_of_mem _ (hO hO'), eval_presheaf_map]

end Values

/-- **Sections are determined by their values on the sheets over the disc**: two sections of
`𝒪_W` over an open lying over the disc which have the same values on all sheets are equal. -/
theorem eq_of_sheetVal_eq {O : W.left.Opens}
    (hO : ∀ w ∈ O, splitEquiv m (pt W w) ∈ discRegion G w₁ ε) {a b : W.left.presheaf.obj (op O)}
    (h : ∀ i, ∀ j < (D.deg i : ℕ), ∀ z (hz : z ∈ discRegion G w₁ ε), D.sheet hε i j z hz ∈ O →
      D.sheetVal (w₁ := w₁) a i j z = D.sheetVal (w₁ := w₁) b i j z) : a = b := by
  refine eq_of_forall_eval_eq (isLocallyOpenInAffine_left W) fun w hw ↦ ?_
  obtain ⟨i, j, hj, hij⟩ := D.exists_sheet_eq hε (hO w hw) rfl
  have hmem : D.sheet hε i j _ (hO w hw) ∈ O := by rw [hij]; exact hw
  have := h i j hj _ (hO w hw) hmem
  rw [← D.evalFun_sheet hε a i j (hO w hw), ← D.evalFun_sheet hε b i j (hO w hw), hij,
    evalFun_of_mem _ hw, evalFun_of_mem _ hw] at this
  exact this

/-! ### Sections with prescribed values on the sheets -/

include hε in
lemma continuousAt_kroot_pow {k : ℕ} {x : Cm.{u} m × ℂ}
    (hx : Kummer.powMap k x ∈ discRegion G w₁ ε) :
    ContinuousAt (fun x : Cm.{u} m × ℂ ↦ kroot k w₁ (x.2 ^ k)) x := by
  have hρ := pos_of_mem_overlap (hε hx.2)
  have h := differentiableAt_kroot k (div_mem_slitPlane (norm_sub_lt_of_mem_discRegion hε hρ hx))
  exact ContinuousAt.comp (g := kroot k w₁) (f := fun x : Cm.{u} m × ℂ ↦ x.2 ^ k) h.continuousAt
    (by fun_prop)

include hε in
/-- A point over the disc is on one of the sheets. -/
lemma exists_eq_sheetCoord {k : ℕ+} {y : Cm.{u} m × ℂ}
    (hy : Kummer.powMap k y ∈ discRegion G w₁ ε) :
    ∃ j < (k : ℕ), y = sheetCoord k j w₁ (Kummer.powMap k y) := by
  haveI : NeZero (k : ℕ) := ⟨k.ne_zero⟩
  have hkr := kroot_ne_zero hε k.ne_zero hy
  have hρ := pos_of_mem_overlap (hε hy.2)
  have h₂ := sheetCoord_pow hε hρ k.ne_zero 0 hy
  simp only [sheetCoord, pow_zero, one_mul, Kummer.powMap_apply] at h₂ hkr
  have hpow : (y.2 / kroot k w₁ (y.2 ^ (k : ℕ))) ^ (k : ℕ) = 1 := by
    rw [div_pow, h₂]
    exact div_self (ne_zero_of_mem_overlap hρ (hε hy.2))
  obtain ⟨j, hj, hζ⟩ := (Kummer.isPrimitiveRoot_zeta k.pos).eq_pow_of_pow_eq_one hpow
  refine ⟨j, hj, Prod.ext rfl ?_⟩
  change y.2 = Kummer.zeta k ^ j * kroot k w₁ (y.2 ^ (k : ℕ))
  rw [hζ, div_mul_cancel₀ _ hkr]

/-- The image of the `(i, j)`-th sheet over the disc. -/
def sheetSet (i : D.ι) (j : ℕ) : Set W.left :=
  {w | ∃ z, ∃ hz : z ∈ discRegion G w₁ ε, D.sheet hε i j z hz = w}

/-- **The sheets over the disc are open.** -/
theorem isOpen_sheetSet (hGo : IsOpen G) (i : D.ι) {j : ℕ} (hj : j < D.deg i) :
    IsOpen (D.sheetSet hε i j) := by
  set k := D.deg i
  set U := Kummer.powMap k ⁻¹' discRegion G w₁ ε
  set T : Set (Cm.{u} m × ℂ) := U ∩ ⋂ j' : Fin k, ⋂ (_ : (j' : ℕ) ≠ j), (U ∩
      (fun x : Cm.{u} m × ℂ ↦ x.2 - Kummer.zeta k ^ (j' : ℕ) * kroot k w₁ (x.2 ^ (k : ℕ))) ⁻¹'
        {0}ᶜ)
  have hU : IsOpen U := (hGo.prod Metric.isOpen_ball).preimage (Kummer.continuous_powMap _)
  have hT : IsOpen T := by
    refine hU.inter (isOpen_iInter_of_finite fun j' ↦ isOpen_iInter_of_finite fun _ ↦ ?_)
    refine ContinuousOn.isOpen_inter_preimage ?_ hU isOpen_compl_singleton
    exact fun x hx ↦ (continuous_snd.continuousAt.sub (continuousAt_const.mul
      (continuousAt_kroot_pow hε hx))).continuousWithinAt
  have hkr : ∀ {z : Cm.{u} m × ℂ}, z ∈ discRegion G w₁ ε → kroot (k : ℕ) w₁ z.2 ≠ 0 :=
    fun hz ↦ kroot_ne_zero hε k.ne_zero hz
  have heq : D.sheetSet hε i j = D.toFun '' (Sigma.mk i '' (Subtype.val ⁻¹' T)) := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hpz : Kummer.powMap k (sheetCoord k j w₁ z) = z :=
        Prod.ext rfl (sheetCoord_pow hε (pos_of_mem_overlap (hε hz.2)) k.ne_zero j hz)
      refine ⟨_, ⟨_, ⟨?_, ?_⟩, rfl⟩, rfl⟩
      · change Kummer.powMap k (sheetCoord k j w₁ z) ∈ discRegion G w₁ ε
        rw [hpz]
        exact hz
      · refine mem_iInter.2 fun j' ↦ mem_iInter.2 fun hj' ↦ ⟨?_, ?_⟩
        · change Kummer.powMap k (sheetCoord k j w₁ z) ∈ discRegion G w₁ ε
          rw [hpz]
          exact hz
        · have h₂ : (sheetCoord k j w₁ z).2 ^ (k : ℕ) = z.2 := congrArg Prod.snd hpz
          change (sheetCoord k j w₁ z).2 - _ * kroot k w₁ ((sheetCoord k j w₁ z).2 ^ (k : ℕ)) ≠ 0
          rw [h₂, sub_ne_zero]
          intro h
          exact hj' ((Kummer.isPrimitiveRoot_zeta k.pos).pow_inj j'.2 hj
            (mul_right_cancel₀ (hkr hz) h.symm))
    · rintro ⟨_, ⟨y, hyT, rfl⟩, rfl⟩
      obtain ⟨j'', hj'', hy⟩ := exists_eq_sheetCoord hε hyT.1
      have hj''j : j'' = j := by
        by_contra hne
        have := (mem_iInter.1 (mem_iInter.1 hyT.2 ⟨j'', hj''⟩) hne).2
        refine this (sub_eq_zero.2 ?_)
        exact congrArg Prod.snd hy
      subst hj''j
      exact ⟨_, hyT.1, congrArg (fun y ↦ D.toFun ⟨i, y⟩) (Subtype.ext hy.symm)⟩
  rw [heq]
  exact D.isOpenEmbedding.isOpenMap _ (isOpenMap_sigmaMk _ (hT.preimage continuous_subtype_val))

lemma sheet_congr (i : D.ι) (j : ℕ) {z z' : Cm.{u} m × ℂ} (h : z = z')
    (hz : z ∈ discRegion G w₁ ε) (hz' : z' ∈ discRegion G w₁ ε) :
    D.sheet hε i j z hz = D.sheet hε i j z' hz' := by
  subst h
  rfl

/-- **Sections with prescribed values on the sheets**: over an open `O` lying over the disc,
every family of functions `gᵢⱼ` which are holomorphic wherever the `(i, j)`-th sheet lies in `O` is
the family of values on the sheets of a section of `𝒪_W` over `O`. Together with
`ComplexAnalytic.Cap.AnnulusDecomposition.eq_of_sheetVal_eq`, `W` is trivial over the disc. -/
theorem exists_sheetVal_eq (hGo : IsOpen G) {O : W.left.Opens}
    (hO : ∀ w ∈ O, splitEquiv m (pt W w) ∈ discRegion G w₁ ε)
    (g : ∀ i, Fin (D.deg i) → Cm.{u} m × ℂ → ℂ)
    (hg : ∀ i (j : Fin (D.deg i)) z (hz : z ∈ discRegion G w₁ ε), D.sheet hε i j z hz ∈ O →
      DifferentiableAt ℂ (g i j) z) :
    ∃ a : W.left.presheaf.obj (op O), ∀ i (j : Fin (D.deg i)) z (hz : z ∈ discRegion G w₁ ε),
      D.sheet hε i j z hz ∈ O → D.sheetVal (w₁ := w₁) a i j z = g i j z := by
  classical
  let idx : ∀ w, splitEquiv m (pt W w) ∈ discRegion G w₁ ε → Σ i, Fin (D.deg i) :=
    fun w hw ↦ (D.sheetEquiv hε hw).symm ⟨w, rfl⟩
  have hidx (w : W.left) (hw) : D.sheet hε (idx w hw).1 (idx w hw).2 _ hw = w :=
    congrArg Subtype.val ((D.sheetEquiv hε hw).apply_symm_apply ⟨w, rfl⟩)
  have hidx' (i : D.ι) (j : Fin (D.deg i)) (z) (hz : z ∈ discRegion G w₁ ε) (hw) :
      idx (D.sheet hε i j z hz) hw = ⟨i, j⟩ := by
    refine (Equiv.symm_apply_eq _).2 (Subtype.ext ?_)
    exact D.sheet_congr hε i j (D.splitEquiv_pt_sheet hε i j hz).symm hz hw
  let f : W.left → ℂ := fun w ↦ if hw : splitEquiv m (pt W w) ∈ discRegion G w₁ ε then
    g (idx w hw).1 (idx w hw).2 (splitEquiv m (pt W w)) else 0
  have hf (i : D.ι) (j : Fin (D.deg i)) (z) (hz : z ∈ discRegion G w₁ ε) :
      f (D.sheet hε i j z hz) = g i j z := by
    have hmem : splitEquiv m (pt W (D.sheet hε i j z hz)) ∈ discRegion G w₁ ε := by
      rw [D.splitEquiv_pt_sheet]
      exact hz
    simp only [f, dif_pos hmem, D.splitEquiv_pt_sheet]
    rw [hidx' i j z hz hmem]
  obtain ⟨a, ha⟩ := exists_eval_eq_of_local (isLocallyOpenInAffine_left W) f fun y hy ↦ by
    set ij := idx y (hO y hy)
    let S : W.left.Opens := ⟨D.sheetSet hε ij.1 ij.2, D.isOpen_sheetSet hε hGo ij.1 ij.2.2⟩
    obtain ⟨σ, hσ⟩ := exists_eval_eq_of_differentiableAt W (O := S ⊓ O)
      (g ij.1 ij.2 ∘ splitEquiv m) fun w hw ↦ by
        obtain ⟨⟨z, hz, rfl⟩, hwO⟩ := hw
        have hd := hg ij.1 ij.2 z hz hwO
        rw [← D.splitEquiv_pt_sheet hε ij.1 ij.2 hz] at hd
        exact hd.comp _ (differentiable_splitEquiv _)
    refine ⟨S ⊓ O, ⟨⟨_, hO y hy, hidx y (hO y hy)⟩, hy⟩, inf_le_right, σ, fun w hw ↦ ?_⟩
    rw [hσ w hw]
    obtain ⟨⟨z, hz, rfl⟩, -⟩ := hw
    rw [hf, Function.comp_apply, D.splitEquiv_pt_sheet]
  exact ⟨a, fun i j z hz hzO ↦ by
    rw [← D.evalFun_sheet hε a i j hz, evalFun_of_mem _ hzO, ha _ hzO, hf]⟩

/-! ### Bounded sections -/

section Bounded

variable {N : (AnalyticSpace.complexAffineSpace.{u} (m + 1)).Opens} (h₀ : N₀ ≤ N)

lemma mem_pieceSet_preim {V : (space N).Opens} {i : D.ι} {z : Cm.{u} m × ℂ} :
    z ∈ D.pieceSet (preim h₀ W V) i ↔ z ∈ KummerAnnulus.base G ρ⁻¹ ρ (D.deg i) ∧
      (splitEquiv m).symm (Kummer.powMap (D.deg i) z) ∈ img V := by
  constructor
  · rintro ⟨h, hz⟩
    rw [mem_preim_iff, D.pt_toFun] at hz
    exact ⟨h, hz⟩
  · rintro ⟨h, hz⟩
    refine ⟨h, ?_⟩
    rw [mem_preim_iff, D.pt_toFun]
    exact hz

include hε in
/-- **Values of sections of `p_* 𝒪_W` over `V` on the sheets over the disc are holomorphic** on
the part of the disc lying in `V`. -/
theorem differentiableOn_sheetVal_preim (hGo : IsOpen G) {V : (space N).Opens}
    (s : W.left.presheaf.obj (op (preim h₀ W V))) (i : D.ι) (j : ℕ) :
    DifferentiableOn ℂ (D.sheetVal (w₁ := w₁) s i j)
      (discRegion G w₁ ε ∩ (splitEquiv m).symm ⁻¹' img V) :=
  (D.differentiableOn_sheetVal hε hGo s i j).mono fun _ ⟨hz, hzV⟩ ↦
    ⟨hz, by rw [mem_preim_iff, D.pt_sheet]; exact hzV⟩

/-! ### The cap -/

/-- The change `(b, u) ↦ (b, u⁻¹)` from the Kummer coordinates on the annulus to the Kummer
coordinates at infinity. -/
def invCoord (z : Cm.{u} m × ℂ) : Cm.{u} m × ℂ := (z.1, z.2⁻¹)

/-- **The sections of the cap** over the open of `G × ℙ¹` which is `V` in the chart `w` and `V'` in
the chart `w' = w⁻¹`: pairs of a section `s` of `𝒜` over `V` and functions `fᵢ`, holomorphic on
`{(b, u') | (b, u'^{kᵢ}) ∈ V'}` (the `i`-th Kummer cover of the chart at infinity), such that on the
`i`-th Kummer piece over the overlap `s(b, u) = fᵢ(b, u⁻¹)`. -/
def capSubring (V : (space N).Opens) (V' : Set (Cm.{u} m × ℂ)) :
    Subring (boundedSubring h₀ W V × (D.ι → Cm.{u} m × ℂ → ℂ)) where
  carrier := {s | (∀ i, DifferentiableOn ℂ (s.2 i) (Kummer.powMap (D.deg i) ⁻¹' V')) ∧
    ∀ i, ∀ z ∈ D.pieceSet (preim h₀ W V) i, invCoord z ∈ Kummer.powMap (D.deg i) ⁻¹' V' →
      D.kummerVal s.1.1 i z = s.2 i (invCoord z)}
  mul_mem' {s t} hs ht := ⟨fun i ↦ (hs.1 i).mul (ht.1 i), fun i z hz hz' ↦ by
    change D.kummerVal (s.1.1 * t.1.1) i z = s.2 i _ * t.2 i _
    rw [D.kummerVal_mul hz, hs.2 i z hz hz', ht.2 i z hz hz']⟩
  one_mem' := ⟨fun _ ↦ differentiableOn_const 1, fun i z hz _ ↦ D.kummerVal_one _ hz⟩
  add_mem' {s t} hs ht := ⟨fun i ↦ (hs.1 i).add (ht.1 i), fun i z hz hz' ↦ by
    change D.kummerVal (s.1.1 + t.1.1) i z = s.2 i _ + t.2 i _
    rw [D.kummerVal_add hz, hs.2 i z hz hz', ht.2 i z hz hz']⟩
  zero_mem' := ⟨fun _ ↦ differentiableOn_const 0, fun i z _ _ ↦ D.kummerVal_zero _⟩
  neg_mem' {s} hs := ⟨fun i ↦ (hs.1 i).neg, fun i z hz hz' ↦ by
    change D.kummerVal (-s.1.1) i z = -s.2 i _
    rw [D.kummerVal_neg hz, hs.2 i z hz hz']⟩

lemma mem_capSubring_iff {V : (space N).Opens} {V' : Set (Cm.{u} m × ℂ)}
    {s : boundedSubring h₀ W V × (D.ι → Cm.{u} m × ℂ → ℂ)} :
    s ∈ D.capSubring h₀ V V' ↔
      (∀ i, DifferentiableOn ℂ (s.2 i) (Kummer.powMap (D.deg i) ⁻¹' V')) ∧
      ∀ i, ∀ z ∈ D.pieceSet (preim h₀ W V) i, invCoord z ∈ Kummer.powMap (D.deg i) ⁻¹' V' →
        D.kummerVal s.1.1 i z = s.2 i (invCoord z) :=
  Iff.rfl

/-- The restriction of a section of the cap. -/
def capRestrict {V V₂ : (space N).Opens} (h : V₂ ≤ V)
    (s : boundedSubring h₀ W V × (D.ι → Cm.{u} m × ℂ → ℂ)) :
    boundedSubring h₀ W V₂ × (D.ι → Cm.{u} m × ℂ → ℂ) :=
  (⟨W.left.presheaf.map (homOfLE (preim_mono h₀ W h)).op s.1.1,
    map_mem_boundedSubring h₀ W h s.1.2⟩, s.2)

/-- **Restriction of sections of the cap.** -/
theorem capRestrict_mem {V V₂ : (space N).Opens} (h : V₂ ≤ V) {V' V₂' : Set (Cm.{u} m × ℂ)}
    (h' : V₂' ⊆ V') {s : boundedSubring h₀ W V × (D.ι → Cm.{u} m × ℂ → ℂ)}
    (hs : s ∈ D.capSubring h₀ V V') : D.capRestrict h₀ h s ∈ D.capSubring h₀ V₂ V₂' := by
  refine ⟨fun i ↦ (hs.1 i).mono fun _ hx ↦ h' hx, fun i z hz hz' ↦ ?_⟩
  change D.kummerVal (W.left.presheaf.map (homOfLE (preim_mono h₀ W h)).op s.1.1) i z = _
  rw [D.kummerVal_map _ hz]
  exact hs.2 i z (D.pieceSet_mono (preim_mono h₀ W h) i hz) (h' hz')

/-- **The structure map of the cap**: a pair of a section `r` of `𝒪_N` over `V` and a holomorphic
function `g` on `V'` which agree on the overlap, `r(b, w) = g(b, w⁻¹)`, gives the section
`(r, (g(b, u'^{kᵢ}))ᵢ)` of the cap. -/
theorem algebraMap_mem_capSubring {V : (space N).Opens} {V' : Set (Cm.{u} m × ℂ)}
    (r : (space N).presheaf.obj (op V)) {g : Cm.{u} m × ℂ → ℂ} (hg : DifferentiableOn ℂ g V')
    (hrg : ∀ b ∈ G, ∀ w ∈ overlap ρ, (splitEquiv m).symm (b, w) ∈ img V → (b, w⁻¹) ∈ V' →
      holFun r ((splitEquiv m).symm (b, w)) = g (b, w⁻¹)) :
    (algebraMapBounded h₀ W V r, fun i ↦ g ∘ Kummer.powMap (D.deg i)) ∈ D.capSubring h₀ V V' := by
  refine ⟨fun i ↦ hg.comp (Kummer.differentiable_powMap _).differentiableOn fun _ hx ↦ hx,
    fun i z hz hz' ↦ ?_⟩
  obtain ⟨h, hO⟩ := hz
  have hV := ((D.mem_pieceSet_preim h₀).1 ⟨h, hO⟩).2
  have hov : z.2 ^ (D.deg i : ℕ) ∈ overlap ρ := by
    rw [overlap_eq_annulus_one, KummerAnnulus.annulus, mem_setOf_eq, norm_pow, pow_one]
    exact h.2
  change D.kummerVal (pullback h₀ W V r) i z = g (Kummer.powMap (D.deg i) (invCoord z))
  rw [D.kummerVal_of_mem _ _ h, evalFun_of_mem _ hO, eval_pullback, D.pt_toFun,
    hrg z.1 h.1 _ hov hV (by simpa [invCoord, inv_pow] using hz')]
  simp [invCoord, inv_pow]

end Bounded

end AnnulusDecomposition

/-! ### Freeness at infinity -/

section Free

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- **The Kummer cover at infinity is free**: a holomorphic function on
`{(b, u') | (b, u'ᵏ) ∈ V'}` is `∑_{j < k} u'ʲ gⱼ(b, u'ᵏ)` with `gⱼ` holomorphic on `V'`. -/
theorem exists_coeff_eqOn {k : ℕ} (hk : 0 < k) {V' : Set (E × ℂ)} (hV' : IsOpen V')
    {f : E × ℂ → ℂ} (hf : DifferentiableOn ℂ f (Kummer.powMap k ⁻¹' V')) :
    ∃ g : Fin k → E × ℂ → ℂ, (∀ j, DifferentiableOn ℂ (g j) V') ∧
      EqOn f (fun x ↦ ∑ j : Fin k, x.2 ^ (j : ℕ) * g j (Kummer.powMap k x))
        (Kummer.powMap k ⁻¹' V') := by
  have hU : IsOpen (Kummer.powMap k ⁻¹' V') :=
    hV'.preimage (Kummer.continuous_powMap k)
  obtain ⟨g, hgd, hgeq⟩ := Kummer.exists_eqOn_sum_pow_mul_comp_powMap hk hV'
    (hf.mono sdiff_subset) fun x hx hx0 ↦ by
      have hxU : x ∈ Kummer.powMap k ⁻¹' V' := by
        change (x.1, x.2 ^ k) ∈ V'
        rw [hx0, zero_pow hk.ne', ← hx0]
        exact hx
      exact ((hf.continuousOn.continuousAt (hU.mem_nhds hxU)).tendsto.mono_left
        nhdsWithin_le_nhds).norm.isBoundedUnder_le
  refine ⟨g, hgd, EqOn.of_eqOn_diff_zero hU (Kummer.interior_inter_preimage_snd_eq_empty _)
    hf.continuousOn ?_ hgeq⟩
  exact (Kummer.differentiableOn_sum_pow_mul_comp_powMap hgd).continuousOn

omit [FiniteDimensional ℂ E] in
/-- The coefficients in `exists_coeff_eqOn` are unique. -/
theorem eqOn_of_coeff {k : ℕ} (hk : 0 < k) {V' : Set (E × ℂ)} (hV' : IsOpen V')
    {g g' : Fin k → E × ℂ → ℂ} (hg : ∀ j, ContinuousOn (g j) V')
    (hg' : ∀ j, ContinuousOn (g' j) V')
    (h : EqOn (fun x ↦ ∑ j : Fin k, x.2 ^ (j : ℕ) * g j (Kummer.powMap k x))
      (fun x ↦ ∑ j : Fin k, x.2 ^ (j : ℕ) * g' j (Kummer.powMap k x)) (Kummer.powMap k ⁻¹' V'))
    (j : Fin k) : EqOn (g j) (g' j) V' := by
  have := Kummer.eqOn_zero_of_sum_pow_mul_comp_powMap hk hV' (g := fun j ↦ g j - g' j)
    (fun j ↦ (hg j).sub (hg' j)) (fun x hx ↦ by
      have := h hx.1
      simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib, Pi.zero_apply]
      exact sub_eq_zero.2 this) j
  exact fun x hx ↦ sub_eq_zero.1 (this hx)

end Free

end

end ComplexAnalytic.Cap
