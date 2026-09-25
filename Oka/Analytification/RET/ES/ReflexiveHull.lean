/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.ES.BoundedSectionsHartogs
import Oka.Geometry.RingedSpace.LocallyRingedSpace.ReflexiveHull
import Oka.AnalyticSpace.FiniteEtalePushforwardCoherent

/-!
# Coherence of bounded sections via reflexive hulls

Keep the notation of `Oka/Analytification/RET/ES/BoundedSectionsHartogs.lean`: `p : W ⟶ N°` is a
finite étale cover with `W` Hausdorff, `N ∖ N°` is thin, and `𝒜` is the sheaf of sections of
`p_* 𝒪_W` bounded near `N ∖ N°`. Let `U ⊆ N` be open, `P` a family of regular pairs on `U` with
zero set `Z ⊇ S`, and `s₁, …, s_m ∈ 𝒜(U)` such that near every point of `U ∖ S` the sheaf `𝒜`
is free with a basis in the span of the `sᵢ` (`ComplexAnalytic.BoundedSections.IsFreeSpanAt`).
Then these data satisfy the reflexive hull criterion
`AlgebraicGeometry.LocallyRingedSpace.ReflexiveHullData` with functionals `a ↦ tr(a sⱼ)` and
`U₀ = U ∖ Z` (`ComplexAnalytic.BoundedSections.reflexiveHullData`); if they exist near every point
of `N`, then `𝒜` is coherent (`ComplexAnalytic.BoundedSections.isCoherent_boundedModule`).

The functionals separate sections
(`ComplexAnalytic.BoundedSections.eq_zero_of_trace_mulSec_eq_zero`): off `Z` the `sᵢ` generate
`𝒜`, so if `tr(a sⱼ) = 0` for all `j`, then `tr(a b) = 0` for the indicator section `b` of any
sheet over a small ball (`ComplexAnalytic.BoundedSections.exists_indicator`), i.e. `a` vanishes
over `N° ∖ Z`, which is dense. Hartogs extension across `Z` holds for `𝒪_N` and `𝒜` by
`ComplexAnalytic.BoundedSections.bijective_map_of_regularPairFamily` and
`ComplexAnalytic.BoundedSections.bijective_boundedModule_map`.

## Main definitions

- `ComplexAnalytic.BoundedSections.IsFreeSpanAt h₀ W s y`: near `y`, `𝒜` is free with a basis in
  the span of the `sᵢ`.
- `ComplexAnalytic.BoundedSections.reflexiveHullData`: the reflexive hull data for `𝒜` on `U`.

## Main results

- `ComplexAnalytic.BoundedSections.isCoherent_boundedModule`: `𝒜` is coherent.
- `ComplexAnalytic.BoundedSections.isFreeSpanAt_of_basis`: `IsFreeSpanAt` from a local basis whose
  elements are near `y` combinations of the `sᵢ`.
-/

open CategoryTheory Opposite AlgebraicGeometry Topology TopologicalSpace Filter

universe u

namespace ComplexAnalytic.BoundedSections

open AnalyticSpace AlgebraicGeometry.LocallyRingedSpace

noncomputable section

variable {n : ℕ} {N N₀ : (AnalyticSpace.complexAffineSpace.{u} n).Opens} (h₀ : N₀ ≤ N)
  (W : FiniteEtaleOver (space N₀))


/-- **`𝒜` is free near `y` with a basis in the span of `s₁, …, s_m`**: there are an open
`V ∋ y` inside `U` and sections `e₁, …, e_r` of `𝒜` over `V`, combinations of the `sᵢ`, such
that every section of `𝒜` over an open inside `V` is a unique combination of the `eₖ`. -/
def IsFreeSpanAt {U : (space N).Opens} {m : ℕ} (s : Fin m → (boundedModule h₀ W).val.obj (op U))
    (y : space N) : Prop :=
  ∃ (V : (space N).Opens) (hVU : V ≤ U) (r : ℕ) (e : Fin r → (boundedModule h₀ W).val.obj (op V))
    (P : Fin r → Fin m → (space N).presheaf.obj (op V)), y ∈ V ∧
    (∀ k, e k = ∑ i, P k i • sectRes (boundedModule h₀ W) hVU (s i)) ∧
    (∀ (V' : (space N).Opens) (h : V' ≤ V) (a : (boundedModule h₀ W).val.obj (op V')),
      ∃ c : Fin r → (space N).presheaf.obj (op V'),
        a = ∑ k, c k • sectRes (boundedModule h₀ W) h (e k)) ∧
    ∀ (V' : (space N).Opens) (h : V' ≤ V) (c : Fin r → (space N).presheaf.obj (op V')),
      ∑ k, c k • sectRes (boundedModule h₀ W) h (e k) = 0 → ∀ k, c k = 0
lemma mulSec_comm {V : (space N).Opens} (s t : (boundedModule h₀ W).val.obj (op V)) :
    mulSec h₀ W s t = mulSec h₀ W t s :=
  secVal_injective h₀ W (by
    change secVal h₀ W s * secVal h₀ W t = secVal h₀ W t * secVal h₀ W s
    exact mul_comm _ _)

lemma mulSec_sum_smul {V : (space N).Opens} {k : ℕ} (f : Fin k → (space N).presheaf.obj (op V))
    (t : Fin k → (boundedModule h₀ W).val.obj (op V)) (a : (boundedModule h₀ W).val.obj (op V)) :
    mulSec h₀ W a (∑ i, f i • t i) = ∑ i, f i • mulSec h₀ W a (t i) := by
  classical
  simp only [mulSec_comm h₀ W a]
  have : ∀ s : Finset (Fin k), mulSec h₀ W (∑ i ∈ s, f i • t i) a =
      ∑ i ∈ s, f i • mulSec h₀ W (t i) a := fun s ↦ by
    induction s using Finset.induction_on with
    | empty => simpa using mulSec_zero_left h₀ W a
    | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, mulSec_add,
        mulSec_smul, ih]
  exact this Finset.univ

variable [T2Space W.left] (hD : HasThinComplement N N₀)
include hD

lemma trace_sum_smul {V : (space N).Opens} {k : ℕ} (f : Fin k → (space N).presheaf.obj (op V))
    (t : Fin k → (boundedModule h₀ W).val.obj (op V)) :
    trace h₀ W hD (∑ i, f i • t i) = ∑ i, f i * trace h₀ W hD (t i) := by
  classical
  have : ∀ s : Finset (Fin k), trace h₀ W hD (∑ i ∈ s, f i • t i) =
      ∑ i ∈ s, f i * trace h₀ W hD (t i) := fun s ↦ by
    induction s using Finset.induction_on with
    | empty => simpa using trace_zero h₀ W hD
    | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, trace_add, trace_smul,
        ih]
  exact this Finset.univ

open Classical in
omit hD in
/-- **Indicator sections of sheets**: near the point below `w₀`, there is a section of `𝒪_W` over
any open lying over a small ball which is `1` at `w₀` and `0` at the other points of its
fibre. -/
lemma exists_indicator (w₀ : W.left) : ∃ B : Set (Cn.{u} n), IsOpen B ∧ pt W w₀ ∈ B ∧
    (∀ z ∈ B, z ∈ N₀) ∧ ∀ O : W.left.Opens, (∀ w ∈ O, pt W w ∈ B) →
      ∃ b : W.left.presheaf.obj (op O), ∀ w ∈ O, pt W w = pt W w₀ →
        evalFun b w = if w = w₀ then 1 else 0 := by
  classical
  obtain ⟨B, I, _, σ, hBo, hx₀B, hBN, hσ, -, huniq, hopen⟩ := exists_local_sheets W (pt_mem W w₀)
  obtain ⟨i₀, hi₀, -⟩ := huniq w₀ hx₀B
  refine ⟨B, hBo, hx₀B, hBN, fun O hOB ↦ ?_⟩
  set S : I → W.left.Opens := fun i ↦ ⟨_, hopen i⟩
  obtain ⟨b, hb⟩ := exists_eval_eq_of_local (isLocallyOpenInAffine_left W) (O := O)
    (fun w ↦ if σ i₀ (pt W w) = w then 1 else 0) fun w hw ↦ by
      obtain ⟨j, hj, hjuniq⟩ := huniq w (hOB w hw)
      by_cases hji : j = i₀
      · subst hji
        refine ⟨O ⊓ S j, ⟨hw, hOB w hw, hj⟩, inf_le_left, 1, fun w' hw' ↦ ?_⟩
        rw [map_one, if_pos hw'.2.2]
      · refine ⟨O ⊓ S j, ⟨hw, hOB w hw, hj⟩, inf_le_left, 0, fun w' hw' ↦ ?_⟩
        rw [map_zero, if_neg]
        intro h
        obtain ⟨k, -, hk⟩ := huniq w' hw'.2.1
        exact hji ((hk j hw'.2.2).trans (hk i₀ h).symm)
  refine ⟨b, fun w hw hww₀ ↦ ?_⟩
  rw [evalFun_of_mem b hw, hb w hw, hww₀, hi₀]
  by_cases h : w = w₀
  · rw [if_pos h.symm, if_pos h]
  · rw [if_neg (Ne.symm h), if_neg h]

/-- **The trace pairing against generators is non-degenerate.** Let `P` be a family of regular
pairs on `U` with zero set `Z`, and let `s₁, …, s_m ∈ 𝒜(U)` generate `𝒜` near every point of
`U ∖ Z`. A section `a` of `𝒜` over `V ⊆ U` with `tr(a sⱼ) = 0` for all `j` vanishes: at a point
`w` over `U ∖ Z`, pairing with an indicator section of the sheet through `w` gives `a(w) = 0`,
and these points are dense. -/
theorem eq_zero_of_trace_mulSec_eq_zero {U : (space N).Opens}
    (P : RegularPairFamily (img U : Set (Cn.{u} n))) {m : ℕ}
    (s : Fin m → (boundedModule h₀ W).val.obj (op U))
    (hgen : ∀ y ∈ U, y.1 ∉ P.zeroSet → ∃ (V' : (space N).Opens) (hV'U : V' ≤ U), y ∈ V' ∧
      ∀ (V'' : (space N).Opens) (h : V'' ≤ V') (b : (boundedModule h₀ W).val.obj (op V'')),
        ∃ f : Fin m → (space N).presheaf.obj (op V''),
          b = ∑ i, f i • sectRes (boundedModule h₀ W) (h.trans hV'U) (s i))
    {V : (space N).Opens} (hVU : V ≤ U) (a : (boundedModule h₀ W).val.obj (op V))
    (ha : ∀ j, trace h₀ W hD (mulSec h₀ W a (sectRes (boundedModule h₀ W) hVU (s j))) = 0) :
    a = 0 := by
  classical
  -- the values vanish over `U ∖ Z`
  have hpt : ∀ w (hw : w ∈ preim h₀ W V), pt W w ∉ P.zeroSet →
      evalFun (secVal h₀ W a) w = 0 := by
    intro w hw hwZ
    set x := pt W w
    have hxV : x ∈ img V := (mem_preim_iff h₀ W).1 hw
    obtain ⟨hxN, hyV⟩ := mem_img_iff.1 hxV
    obtain ⟨V', hV'U, hyV', hspan⟩ := hgen ⟨x, hxN⟩ (hVU hyV) hwZ
    obtain ⟨B, hBo, hxB, hBN, hind⟩ := exists_indicator W w
    let VB : (space N).Opens := ⟨Subtype.val ⁻¹' B, hBo.preimage continuous_subtype_val⟩
    let V'' : (space N).Opens := V ⊓ V' ⊓ VB
    have hV''V : V'' ≤ V := inf_le_left.trans inf_le_left
    have hV''V' : V'' ≤ V' := inf_le_left.trans inf_le_right
    have hxV'' : x ∈ img V'' := mem_img_iff.2 ⟨hxN, ⟨hyV, hyV'⟩, hxB⟩
    have hV''B : ∀ w' ∈ preim h₀ W V'', pt W w' ∈ B := fun w' hw' ↦ by
      obtain ⟨_, h⟩ := mem_img_iff.1 ((mem_preim_iff h₀ W).1 hw')
      exact h.2
    obtain ⟨b, hb⟩ := hind (preim h₀ W V'') hV''B
    have hbmem : b ∈ boundedSubring h₀ W V'' := by
      rw [boundedSubring_eq_top h₀ W fun z (hz : z ∈ V'') ↦ hBN _ hz.2]
      trivial
    obtain ⟨f, hf⟩ := hspan V'' hV''V' (mkSec h₀ W b hbmem)
    have key : trace h₀ W hD (mulSec h₀ W (sectRes (boundedModule h₀ W) hV''V a)
        (mkSec h₀ W b hbmem)) = 0 := by
      rw [hf, mulSec_sum_smul, trace_sum_smul]
      refine Finset.sum_eq_zero fun i _ ↦ ?_
      rw [← sectRes_sectRes (boundedModule h₀ W) hV''V hVU,
        ← mulSec_map, trace_map, ha i,
        map_zero, mul_zero]
    have := holFun_trace h₀ W hD (mulSec h₀ W (sectRes (boundedModule h₀ W) hV''V a)
      (mkSec h₀ W b hbmem)) hxV'' (pt_mem W w)
    rw [key, holFun_zero hxV'', traceFun, Finset.sum_eq_single w] at this
    · rw [secVal_mulSec, evalFun_mul W _ _ ((mem_preim_iff h₀ W).2 hxV''), secVal_mkSec,
        hb w ((mem_preim_iff h₀ W).2 hxV'') rfl, if_pos rfl, mul_one, secVal_map,
        evalFun_map W _ _ ((mem_preim_iff h₀ W).2 hxV'')] at this
      exact this.symm
    · intro w' hw' hw'w
      have hw'x : pt W w' = x := (mem_fiberFinset W).1 hw'
      have hw'V : w' ∈ preim h₀ W V'' := (mem_preim_iff h₀ W).2 (hw'x ▸ hxV'')
      rw [secVal_mulSec, evalFun_mul W _ _ hw'V, secVal_mkSec, hb w' hw'V hw'x, if_neg hw'w,
        mul_zero]
    · exact fun h ↦ (h ((mem_fiberFinset W).2 rfl)).elim
  -- density of the points over `U ∖ Z`
  refine secVal_injective h₀ W (eq_of_forall_eval_eq (isLocallyOpenInAffine_left W)
    fun w hw ↦ ?_)
  rw [secVal_zero, map_zero]
  obtain ⟨O, hwO, -, hsheet⟩ := exists_sheet W w
  obtain ⟨F, hFd, hF⟩ := hsheet (O' := O ⊓ preim h₀ W V) inf_le_left
    (W.left.presheaf.map (homOfLE inf_le_right).op (secVal h₀ W a))
  set G : Set (Cn.{u} n) := pt W '' ((O ⊓ preim h₀ W V : W.left.Opens) : Set W.left)
  have hGU : G ⊆ img U := (image_pt_subset h₀ W O).trans (img_mono hVU)
  have hFc : ContinuousOn F G := by
    rintro _ ⟨w', hw', rfl⟩
    exact (hFd w' hw').continuousAt.continuousWithinAt
  have h0 := P.eqOn_of_eqOn_diff (isOpen_image_pt W _) hGU hFc (continuousOn_const (c := 0))
    (fun x hx ↦ ?_) ⟨w, ⟨hwO, hw⟩, rfl⟩
  · have := hF w ⟨hwO, hw⟩
    rw [eval_presheaf_map] at this
    exact this.trans h0
  · obtain ⟨⟨w', hw', rfl⟩, hxZ⟩ := hx
    rw [← hF w' hw', eval_presheaf_map, ← evalFun_of_mem _ hw'.2]
    exact hpt w' hw'.2 hxZ

omit [T2Space W.left] hD in
variable {h₀ W} in
/-- The generators `sᵢ` of a free basis generate `𝒜`. -/
lemma exists_span_of_isFreeSpanAt {U : (space N).Opens} {m : ℕ}
    {s : Fin m → (boundedModule h₀ W).val.obj (op U)} {y : space N}
    (h : IsFreeSpanAt h₀ W s y) : ∃ (V' : (space N).Opens) (hV'U : V' ≤ U), y ∈ V' ∧
      ∀ (V'' : (space N).Opens) (h : V'' ≤ V') (b : (boundedModule h₀ W).val.obj (op V'')),
        ∃ f : Fin m → (space N).presheaf.obj (op V''),
          b = ∑ i, f i • sectRes (boundedModule h₀ W) (h.trans hV'U) (s i) := by
  obtain ⟨V, hVU, r, e, P, hyV, he, hspan, -⟩ := h
  refine ⟨V, hVU, hyV, fun V' h a ↦ ?_⟩
  obtain ⟨c, rfl⟩ := hspan V' h a
  refine ⟨fun i ↦ ∑ k, c k * (space N).res h (P k i), ?_⟩
  simp only [he, sectRes_sum_smul, sectRes_sectRes, Finset.smul_sum, Finset.sum_smul, mul_smul]
  exact Finset.sum_comm

omit [T2Space W.left] hD in
variable {h₀ W} in
/-- **A local basis whose elements are combinations of the `sᵢ` near `y`**: if `e₁, …, e_r` is a
basis of `𝒜` over `V ∋ y` and near `y` each `eₖ` is a combination of the `sᵢ` (i.e. the germs of
the `sᵢ` generate the stalk of `𝒜` at `y`), then `𝒜` is free near `y` with a basis in the span of
the `sᵢ`. -/
lemma isFreeSpanAt_of_basis {U V : (space N).Opens} (hVU : V ≤ U) {m r : ℕ}
    {s : Fin m → (boundedModule h₀ W).val.obj (op U)}
    (e : Fin r → (boundedModule h₀ W).val.obj (op V))
    (hspan : ∀ (V' : (space N).Opens) (h : V' ≤ V) (a : (boundedModule h₀ W).val.obj (op V')),
      ∃ c : Fin r → (space N).presheaf.obj (op V'),
        a = ∑ k, c k • sectRes (boundedModule h₀ W) h (e k))
    (hindep : ∀ (V' : (space N).Opens) (h : V' ≤ V) (c : Fin r → (space N).presheaf.obj (op V')),
      ∑ k, c k • sectRes (boundedModule h₀ W) h (e k) = 0 → ∀ k, c k = 0)
    {V' : (space N).Opens} (hV'V : V' ≤ V) {y : space N} (hy : y ∈ V')
    (P : Fin r → Fin m → (space N).presheaf.obj (op V'))
    (he : ∀ k, sectRes (boundedModule h₀ W) hV'V (e k) =
      ∑ i, P k i • sectRes (boundedModule h₀ W) (hV'V.trans hVU) (s i)) :
    IsFreeSpanAt h₀ W s y := by
  refine ⟨V', hV'V.trans hVU, r, fun k ↦ sectRes (boundedModule h₀ W) hV'V (e k), P, hy, he,
    fun V'' h a ↦ ?_, fun V'' h c hc ↦ hindep V'' (h.trans hV'V) c ?_⟩
  · obtain ⟨c, hc⟩ := hspan V'' (h.trans hV'V) a
    exact ⟨c, by simpa only [sectRes_sectRes] using hc⟩
  · simpa only [sectRes_sectRes] using hc

omit [T2Space W.left] hD in
variable (N) in
/-- The part `U ∖ Z` of `U` off the zero set of a family of regular pairs on `U`. -/
def diffZeroSet {U : (space N).Opens} (P : RegularPairFamily (img U : Set (Cn.{u} n))) :
    (space N).Opens :=
  ⟨Subtype.val ⁻¹' ((img U : Set (Cn.{u} n)) \ P.zeroSet),
    (P.isOpen_diff_zeroSet (img U).isOpen subset_rfl).preimage continuous_subtype_val⟩

omit [T2Space W.left] hD in
lemma diffZeroSet_le {U : (space N).Opens} (P : RegularPairFamily (img U : Set (Cn.{u} n))) :
    diffZeroSet N P ≤ U := fun y hy ↦ by
  obtain ⟨_, h⟩ := mem_img_iff.1 hy.1
  exact h

omit [T2Space W.left] hD in
lemma img_diff_subset {U : (space N).Opens} (P : RegularPairFamily (img U : Set (Cn.{u} n)))
    {V : (space N).Opens} (hVU : V ≤ U) :
    (img V : Set (Cn.{u} n)) \ P.zeroSet ⊆ img (V ⊓ diffZeroSet N P) := by
  intro x hx
  obtain ⟨hxN, hxV⟩ := mem_img_iff.1 hx.1
  exact mem_img_iff.2 ⟨hxN, hxV, img_mono hVU hx.1, hx.2⟩

/-- **The reflexive hull data for `𝒜`.** Let `P` be a family of regular pairs on `U` whose zero
set contains `S`, and let `s₁, …, s_m ∈ 𝒜(U)` be such that near every point of `U ∖ S`, `𝒜` is
free with a basis in the span of the `sᵢ`. The functionals are `a ↦ tr(a sⱼ)`, and `U₀ = U ∖ Z`
(`ComplexAnalytic.BoundedSections.diffZeroSet`). -/
def reflexiveHullData {U : (space N).Opens} (P : RegularPairFamily (img U : Set (Cn.{u} n)))
    {m : ℕ} (s : Fin m → (boundedModule h₀ W).val.obj (op U)) {S : Set (Cn.{u} n)}
    (hS : S ⊆ P.zeroSet) (hfree : ∀ y ∈ U, y.1 ∉ S → IsFreeSpanAt h₀ W s y) :
    ReflexiveHullData (boundedModule h₀ W) U where
  U₀ := diffZeroSet N P
  le := diffZeroSet_le P
  m := m
  s := s
  m' := m
  τ j V hV a := trace h₀ W hD (mulSec h₀ W a (sectRes (boundedModule h₀ W) hV (s j)))
  τ_add j V hV a b := by rw [mulSec_add, trace_add]
  τ_smul j V hV r a := by rw [mulSec_smul, trace_smul]
  τ_res j V hV V' h a := by
    rw [← sectRes_sectRes (boundedModule h₀ W) h hV, ← mulSec_map, trace_map]
    rfl
  eq_zero_of_τ V hV a ha := eq_zero_of_trace_mulSec_eq_zero h₀ W hD P s
    (fun y hy hyZ ↦ exists_span_of_isFreeSpanAt (hfree y hy fun h ↦ hyZ (hS h))) hV a ha
  injective_res V hV :=
    (bijective_map_of_regularPairFamily P hV inf_le_left (img_diff_subset P hV)).1
  surjective_res V hV :=
    (bijective_map_of_regularPairFamily P hV inf_le_left (img_diff_subset P hV)).2
  surjective_sectRes V hV :=
    (bijective_boundedModule_map P h₀ W hV inf_le_left (img_diff_subset P hV) hD).2
  exists_basis y hy := hfree y (diffZeroSet_le P hy) fun h ↦ hy.2 (hS h)

/-- **Coherence of `𝒜` from the reflexive hull criterion.** Suppose every point of `N` has an
open neighbourhood `U`, a family `P` of regular pairs on `U` whose zero set contains a set `S`,
and sections `s₁, …, s_m ∈ 𝒜(U)` such that near every point of `U ∖ S` the sheaf `𝒜` is free
with a basis in the span of the `sᵢ`. Then `𝒜` is a coherent sheaf of `𝒪_N`-modules. -/
theorem isCoherent_boundedModule
    (h : ∀ x : space N, ∃ (U : (space N).Opens) (P : RegularPairFamily (img U : Set (Cn.{u} n)))
      (S : Set (Cn.{u} n)) (m : ℕ) (s : Fin m → (boundedModule h₀ W).val.obj (op U)),
      x ∈ U ∧ S ⊆ P.zeroSet ∧ ∀ y ∈ U, y.1 ∉ S → IsFreeSpanAt h₀ W s y) :
    (boundedModule h₀ W).IsCoherent :=
  isCoherent_of_reflexiveHullData (space N).hasLocalTupleRelations_unit _ fun x ↦ by
    obtain ⟨U, P, S, m, s, hxU, hS, hfree⟩ := h x
    exact ⟨U, hxU, ⟨reflexiveHullData h₀ W hD P s hS hfree⟩⟩

end

end ComplexAnalytic.BoundedSections
