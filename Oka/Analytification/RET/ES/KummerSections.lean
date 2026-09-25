/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analysis.Complex.KummerExtension
import Oka.Analytification.GAGA.ProjectiveSpaceAnFunctions
import Oka.Analytification.RET.ES.KummerModel

/-!
# Bounded sections of a finite étale cover of `B × Δ*`

Keep the notation of `Oka/Analytification/RET/ES/KummerModel.lean`: `S° ⊆ ℂ^{m+1}` is the open
subspace `{b ∈ B, 0 < ‖t‖ < 1}`, and `p : W → S°` a finite étale cover, which is isomorphic to a
finite disjoint union of Kummer covers `(t, b) ↦ (t^{kᵢ}, b)` of `S°`. Let `V ⊆ {b ∈ B, ‖t‖ < 1}`
be open. A section `s` of `𝒪_W` over `p⁻¹(V)` is bounded near `D = {t = 0}` if every point of
`V ∩ D` has a neighbourhood `N` with `s` bounded on `p⁻¹(N)`.

The bounded sections are exactly those whose restriction to the `i`-th Kummer cover is of the form
`∑_{j < kᵢ} tʲ gᵢⱼ(b, tᵏⁱ)` with `gᵢⱼ` holomorphic on `V`
(`ComplexAnalytic.KummerModel.isBoundedNearZero_iff`), and the `gᵢⱼ` are unique
(`ComplexAnalytic.KummerModel.eqOn_of_forall_eval_eq`): on the `i`-th Kummer cover the bounded
functions form the free `𝒪(V)`-module with basis `1, t, …, t^{kᵢ - 1}`, that is
`𝒪(V)[u]/(u^{kᵢ} - t)`. Boundedness itself does not refer to the decomposition of `W`.

## Main definitions

- `ComplexAnalytic.KummerModel.puncturedPreimage hB hV`: the open `V ∩ S°` of `S°`.
- `ComplexAnalytic.KummerModel.IsBoundedNearZero`: a section of `𝒪_W` over `p⁻¹(V ∩ S°)` is
  bounded near `t = 0`.
- `ComplexAnalytic.KummerModel.piece e i`: the `i`-th Kummer cover in a decomposition `e` of `W`.

## Main results

- `ComplexAnalytic.eval_restrict_complexAffineSpace_of`: on an open subspace of `ℂⁿ`, the value
  of a section over any open is its value as a holomorphic function.
- `ComplexAnalytic.KummerModel.isBoundedNearZero_iff`: the characterisation of the bounded
  sections.
- `ComplexAnalytic.KummerModel.eqOn_of_forall_eval_eq`: uniqueness of the coefficients `gᵢⱼ`.
-/

open CategoryTheory Opposite AlgebraicGeometry Topology Filter TopologicalSpace

universe u

namespace ComplexAnalytic

open AnalyticSpace

/-- **On an open subspace of `ℂⁿ`, the value of a section over an open `O` is its value as a
holomorphic function** on the image of `O` in `ℂⁿ`. -/
theorem eval_restrict_complexAffineSpace_of {n : ℕ}
    (Uo : (AnalyticSpace.complexAffineSpace.{u} n).Opens)
    {O : ((AnalyticSpace.complexAffineSpace.{u} n).restrict Uo).Opens}
    (x : (AnalyticSpace.complexAffineSpace.{u} n).restrict Uo) (hx : x ∈ O)
    (σ : ((AnalyticSpace.complexAffineSpace.{u} n).restrict Uo).presheaf.obj (op O)) :
    ((AnalyticSpace.complexAffineSpace.{u} n).restrict Uo).eval x hx σ =
      OkaRing.evalHom (U := ((Uo.isOpenEmbedding.isOpenMap.functor.obj O :
        (AnalyticSpace.complexAffineSpace.{u} n).Opens) : Opens (ULift.{u} (Fin n) → ℂ)))
        (x := x.1) ⟨x, hx, rfl⟩ σ := by
  let i := (AnalyticSpace.complexAffineSpace.{u} n).ofRestrict Uo
  let W : (AnalyticSpace.complexAffineSpace.{u} n).Opens :=
    Uo.isOpenEmbedding.isOpenMap.functor.obj O
  have hxW : i.toLRSHom.base x ∈ W := ⟨x, hx, rfl⟩
  have hOW : O ≤ (Opens.map i.toLRSHom.base).obj W := fun y hy ↦ ⟨y, hy, rfl⟩
  have key : TopCat.Presheaf.restrictOpen
      (F := ((AnalyticSpace.complexAffineSpace.{u} n).restrict Uo).presheaf)
      (i.toLRSHom.c.app (op W) σ) O hOW = σ := by
    have h₂ : ∀ {Y : (AnalyticSpace.complexAffineSpace.{u} n).Opensᵒᵖ} (a : op W ⟶ Y)
        (b : Y ⟶ op W), (AnalyticSpace.complexAffineSpace.{u} n).presheaf.map b
          ((AnalyticSpace.complexAffineSpace.{u} n).presheaf.map a σ) = σ := fun a b ↦ by
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, Subsingleton.elim (a ≫ b) (𝟙 _),
        (AnalyticSpace.complexAffineSpace.{u} n).presheaf.map_id]
      rfl
    refine h₂ (homOfLE fun y hy ↦ ?_).op (homOfLE fun y hy ↦ ?_).op
    · obtain ⟨z, hz, rfl⟩ := hy
      exact hz
    · obtain ⟨z, hz, rfl⟩ := hy
      exact ⟨z, hOW hz, rfl⟩
  rw [← key, eval_restrictOpen, eval_c_app _ i.isCLinear x hxW σ, eval_complexAffineSpace_of]
  rfl


namespace KummerModel

noncomputable section

variable {m : ℕ} {B : Set (ULift.{u} (Fin m) → ℂ)} (hB : IsOpen B)

lemma differentiable_splitEquiv_symm :
    Differentiable ℂ ((splitEquiv.{u} m).symm :
      (ULift.{u} (Fin m) → ℂ) × ℂ → ULift.{u} (Fin (m + 1)) → ℂ) := by
  refine differentiable_pi.2 fun ⟨j⟩ ↦ ?_
  cases j using Fin.cases
  · exact differentiable_snd
  · rename_i i
    change Differentiable ℂ fun z : (ULift.{u} (Fin m) → ℂ) × ℂ ↦ z.1 ⟨i⟩
    fun_prop

lemma splitEquiv_symm_powMap (k : ℕ+) (x : ULift.{u} (Fin (m + 1)) → ℂ) :
    (splitEquiv m).symm (Kummer.powMap k (splitEquiv m x)) =
      Function.update x zero (x zero ^ (k : ℕ)) := by
  rw [Homeomorph.symm_apply_eq, splitEquiv_update]
  rfl

/-- The open `V ∩ S°` of `S°`. -/
def puncturedPreimage {V : Set (ULift.{u} (Fin (m + 1)) → ℂ)} (hV : IsOpen V) :
    (punctured hB).Opens :=
  ⟨{y | (y.1 : ULift.{u} (Fin (m + 1)) → ℂ) ∈ V}, hV.preimage continuous_subtype_val⟩

/-- The value of a section, pulled back to `S°`, is a holomorphic function. -/
theorem exists_eval_eq_of_hom {Z : AnalyticSpace.{u}} (φ : punctured hB ⟶ Z) {O : Z.Opens}
    (s : Z.presheaf.obj (op O)) :
    ∃ f : (ULift.{u} (Fin (m + 1)) → ℂ) → ℂ,
      (∀ y : punctured hB, φ.toLRSHom.base y ∈ O → DifferentiableAt ℂ f y.1) ∧
      ∀ (y : punctured hB) (hy : φ.toLRSHom.base y ∈ O), Z.eval _ hy s = f y.1 := by
  set O' : (punctured hB).Opens := (Opens.map φ.toLRSHom.base).obj O
  set σ := φ.toLRSHom.c.app (op O) s
  set U : Opens (ULift.{u} (Fin (m + 1)) → ℂ) :=
    (puncturedOpens B hB).isOpenEmbedding.isOpenMap.functor.obj O'
  refine ⟨OkaRing.toGlobalFun U σ, fun y hy ↦ ?_, fun y hy ↦ ?_⟩
  · exact (OkaRing.analyticAt_toGlobalFun (U := U) σ ⟨y, hy, rfl⟩).differentiableAt
  · rw [← eval_c_app _ φ.isCLinear y hy s, eval_restrict_complexAffineSpace_of]
    exact (OkaRing.toGlobalFun_apply (U := U) σ ⟨y, hy, rfl⟩).symm

/-- A section of `𝒪_W` over `p⁻¹(V ∩ S°)` is **bounded near `t = 0`** if every point of `V` with
`t = 0` has a neighbourhood `N` such that the section is bounded on `p⁻¹(N)`. -/
def IsBoundedNearZero (W : FiniteEtaleOver (punctured hB)) {V : Set (ULift.{u} (Fin (m + 1)) → ℂ)}
    (hV : IsOpen V)
    (s : W.left.presheaf.obj (op ((Opens.map W.hom.toLRSHom.base).obj (puncturedPreimage hB hV)))) :
    Prop :=
  ∀ x ∈ V, x zero = 0 → ∃ N ∈ 𝓝 x, ∃ M : ℝ, ∀ (w : W.left)
    (hw : W.hom.toLRSHom.base w ∈ puncturedPreimage hB hV),
    ((W.hom.toLRSHom.base w : punctured hB).1 : ULift.{u} (Fin (m + 1)) → ℂ) ∈ N →
      ‖W.left.eval w hw s‖ ≤ M

variable {hB} {W : FiniteEtaleOver (punctured hB)} {ι : Type u} {k : ι → ℕ+}
  [Finite ι] (e : W ≅ FiniteEtaleOver.sigma fun i ↦ cover hB (k i))

/-- The `i`-th Kummer cover inside `W`, for a decomposition `e` of `W`. -/
def piece (i : ι) : punctured hB ⟶ W.left :=
  AnalyticSpace.sigmaι (fun i ↦ (cover hB (k i)).left) i ≫ e.inv.left

lemma piece_comp (i : ι) : piece e i ≫ W.hom = kummerHom hB (k i) := by
  rw [piece, Category.assoc]
  refine (congrArg (AnalyticSpace.sigmaι (fun i ↦ (cover hB (k i)).left) i ≫ ·)
    (MorphismProperty.Over.w e.inv)).trans ?_
  exact sigmaι_sigmaDesc (fun i ↦ (cover hB (k i)).left) (fun i ↦ (cover hB (k i)).hom) i

lemma coe_hom_base_piece (i : ι) (y : punctured hB) :
    ((W.hom.toLRSHom.base ((piece e i).toLRSHom.base y) : punctured hB).1 :
      ULift.{u} (Fin (m + 1)) → ℂ) = Function.update y.1 zero (y.1 zero ^ (k i : ℕ)) :=
  (congrArg (fun φ ↦ ((φ.toLRSHom.base y : punctured hB).1 : ULift.{u} (Fin (m + 1)) → ℂ))
    (piece_comp e i)).trans (coe_kummerHom_base hB (k i) y)

lemma exists_piece (w : W.left) : ∃ i y, (piece e i).toLRSHom.base y = w := by
  obtain ⟨z, rfl⟩ := (FiniteEtaleOver.isHomeomorph_base_hom_left e.symm).surjective w
  obtain ⟨⟨i, y⟩, rfl⟩ :=
    (sigmaHomeoSigma fun i ↦ (cover hB (k i)).left).symm.surjective z
  exact ⟨i, y, rfl⟩


lemma coe_hom_base_piece_splitEquiv_symm (i : ι) (z : (ULift.{u} (Fin m) → ℂ) × ℂ)
    (hx : (splitEquiv m).symm z ∈ puncturedOpens B hB) :
    ((W.hom.toLRSHom.base ((piece e i).toLRSHom.base ⟨_, hx⟩) : punctured hB).1 :
      ULift.{u} (Fin (m + 1)) → ℂ) = (splitEquiv m).symm (Kummer.powMap (k i) z) := by
  rw [coe_hom_base_piece, ← splitEquiv_symm_powMap]
  change (splitEquiv m).symm (Kummer.powMap (k i) (splitEquiv m ((splitEquiv m).symm z))) = _
  rw [Homeomorph.apply_symm_apply]

/-- A point `(b, u)` with `u ≠ 0` and `(b, uᵏ) ∈ V` is a point of `S°` whose image in `W` under
the `i`-th Kummer cover lies over `V`. -/
lemma exists_mem_puncturedPreimage {V : Set (ULift.{u} (Fin (m + 1)) → ℂ)} (hV : IsOpen V)
    (hVB : ∀ x ∈ V, (splitEquiv m x).1 ∈ B ∧ ‖x zero‖ < 1) (i : ι)
    {z : (ULift.{u} (Fin m) → ℂ) × ℂ}
    (hz : z ∈ Kummer.powMap (k i) ⁻¹' ((splitEquiv m).symm ⁻¹' V) \ Prod.snd ⁻¹' {0}) :
    ∃ hx : (splitEquiv m).symm z ∈ puncturedOpens B hB,
      W.hom.toLRSHom.base ((piece e i).toLRSHom.base ⟨_, hx⟩) ∈ puncturedPreimage hB hV := by
  have h₁ := hVB _ hz.1
  have h₂ : splitEquiv m ((splitEquiv m).symm (Kummer.powMap (k i) z)) =
      Kummer.powMap (k i) z := Homeomorph.apply_symm_apply _ _
  rw [h₂] at h₁
  have hx : (splitEquiv m).symm z ∈ puncturedOpens B hB := by
    change splitEquiv m ((splitEquiv m).symm z) ∈ Kummer.base B
    rw [Homeomorph.apply_symm_apply]
    refine ⟨h₁.1, hz.2, ?_⟩
    have := h₁.2
    change ‖(splitEquiv m ((splitEquiv m).symm (Kummer.powMap (k i) z))).2‖ < 1 at this
    rw [h₂, Kummer.powMap_apply, norm_pow,
      pow_lt_one_iff_of_nonneg (norm_nonneg _) (PNat.ne_zero _)] at this
    exact this
  refine ⟨hx, ?_⟩
  change ((W.hom.toLRSHom.base ((piece e i).toLRSHom.base ⟨_, hx⟩) : punctured hB).1 :
    ULift.{u} (Fin (m + 1)) → ℂ) ∈ V
  rw [coe_hom_base_piece_splitEquiv_symm]
  exact hz.1

/-- **The bounded sections of a finite étale cover of `B × Δ*`.** Let `e` decompose `W` into
Kummer covers of degrees `kᵢ` and let `V ⊆ {b ∈ B, ‖t‖ < 1}` be open. A section `s` of `𝒪_W` over
`p⁻¹(V ∩ S°)` is bounded near `t = 0` if and only if on the `i`-th Kummer cover it is
`∑_{j < kᵢ} tʲ gᵢⱼ(b, tᵏⁱ)` with `gᵢⱼ` holomorphic on `V`. -/
theorem isBoundedNearZero_iff {V : Set (ULift.{u} (Fin (m + 1)) → ℂ)} (hV : IsOpen V)
    (hVB : ∀ x ∈ V, (splitEquiv m x).1 ∈ B ∧ ‖x zero‖ < 1)
    (s : W.left.presheaf.obj (op ((Opens.map W.hom.toLRSHom.base).obj (puncturedPreimage hB hV)))) :
    IsBoundedNearZero hB W hV s ↔ ∀ i, ∃ g : Fin (k i) → (ULift.{u} (Fin m) → ℂ) × ℂ → ℂ,
      (∀ j, DifferentiableOn ℂ (g j) ((splitEquiv m).symm ⁻¹' V)) ∧
      ∀ (y : punctured hB)
        (hy : W.hom.toLRSHom.base ((piece e i).toLRSHom.base y) ∈ puncturedPreimage hB hV),
        W.left.eval _ hy s =
          ∑ j : Fin (k i), y.1 zero ^ (j : ℕ) * g j (Kummer.powMap (k i) (splitEquiv m y.1)) := by
  set V' : Set ((ULift.{u} (Fin m) → ℂ) × ℂ) := (splitEquiv m).symm ⁻¹' V
  have hV' : IsOpen V' := hV.preimage (splitEquiv m).symm.continuous
  have hmem (i : ι) (z : (ULift.{u} (Fin m) → ℂ) × ℂ)
      (hz : z ∈ Kummer.powMap (k i) ⁻¹' V' \ Prod.snd ⁻¹' {0}) :=
    exists_mem_puncturedPreimage e hV hVB i hz
  constructor
  · intro hbd i
    obtain ⟨f, hfd, hfeval⟩ := exists_eval_eq_of_hom hB (piece e i)
      (O := (Opens.map W.hom.toLRSHom.base).obj (puncturedPreimage hB hV)) s
    have hF : DifferentiableOn ℂ (fun z ↦ f ((splitEquiv m).symm z))
        (Kummer.powMap (k i) ⁻¹' V' \ Prod.snd ⁻¹' {0}) := fun z hz ↦ by
      obtain ⟨hx, hw⟩ := hmem i z hz
      exact ((hfd ⟨_, hx⟩ hw).comp z
        (differentiable_splitEquiv_symm.differentiableAt)).differentiableWithinAt
    have hFb : ∀ x' ∈ V', x'.2 = 0 → IsBoundedUnder (· ≤ ·)
        (𝓝[Kummer.powMap (k i) ⁻¹' V' \ Prod.snd ⁻¹' {0}] x')
        (‖(fun z ↦ f ((splitEquiv m).symm z)) ·‖) := by
      intro x' hx' hx'0
      obtain ⟨N, hN, M, hM⟩ := hbd _ hx' hx'0
      have hc : ContinuousAt (fun z ↦ (splitEquiv m).symm (Kummer.powMap (k i) z)) x' :=
        ((splitEquiv m).symm.continuous.comp (Kummer.continuous_powMap _)).continuousAt
      have hx'' : (splitEquiv m).symm (Kummer.powMap (k i) x') = (splitEquiv m).symm x' := by
        congr 1
        exact Prod.ext rfl (by simp [hx'0])
      rw [ContinuousAt, hx''] at hc
      refine ⟨M, eventually_map.2 ?_⟩
      filter_upwards [nhdsWithin_le_nhds (hc hN), self_mem_nhdsWithin] with z hzN hz
      obtain ⟨hx, hw⟩ := hmem i z hz
      refine (congrArg norm (hfeval ⟨_, hx⟩ hw)).symm.trans_le (hM _ hw ?_)
      rw [coe_hom_base_piece_splitEquiv_symm]
      exact hzN
    obtain ⟨g, hgd, hgeq⟩ :=
      Kummer.exists_eqOn_sum_pow_mul_comp_powMap (k i).pos hV' hF hFb
    refine ⟨g, hgd, fun y hy ↦ ?_⟩
    have hz : splitEquiv m y.1 ∈ Kummer.powMap (k i) ⁻¹' V' \ Prod.snd ⁻¹' {0} := by
      refine ⟨?_, y.2.2.1⟩
      change (splitEquiv m).symm (Kummer.powMap (k i) (splitEquiv m y.1)) ∈ V
      rw [splitEquiv_symm_powMap, ← coe_hom_base_piece e i y]
      exact hy
    rw [hfeval y hy]
    have := hgeq hz
    simp only [Homeomorph.symm_apply_apply] at this
    exact this
  · intro hg x hx hx0
    choose g hgd hgeval using hg
    haveI := Fintype.ofFinite ι
    set x' := splitEquiv m x
    have hx' : x' ∈ V' := by
      change (splitEquiv m).symm (splitEquiv m x) ∈ V
      rw [Homeomorph.symm_apply_apply]
      exact hx
    have hev : ∀ᶠ z in 𝓝 x', ∀ i j, ‖g i j z‖ ≤ ‖g i j x'‖ + 1 := by
      refine Filter.eventually_all.2 fun i ↦ Filter.eventually_all.2 fun j ↦ ?_
      have := ((hgd i j).continuousOn.continuousAt (hV'.mem_nhds hx')).norm
      filter_upwards [this.eventually (gt_mem_nhds (lt_add_one ‖g i j x'‖))] with z hz
      exact hz.le
    refine ⟨splitEquiv m ⁻¹' {z | ∀ i j, ‖g i j z‖ ≤ ‖g i j x'‖ + 1},
      (splitEquiv m).continuous.continuousAt.preimage_mem_nhds hev,
      ∑ i, ∑ j, (‖g i j x'‖ + 1), fun w hw hwN ↦ ?_⟩
    obtain ⟨i, y, rfl⟩ := exists_piece e w
    rw [hgeval i y hw]
    have hy1 : ‖(y.1 : ULift.{u} (Fin (m + 1)) → ℂ) zero‖ < 1 := y.2.2.2
    have hN : ∀ j, ‖g i j (Kummer.powMap (k i) (splitEquiv m y.1))‖ ≤ ‖g i j x'‖ + 1 := by
      have := hwN
      rw [coe_hom_base_piece, ← splitEquiv_symm_powMap] at this
      change ∀ i j, _ at this
      simp only [Homeomorph.apply_symm_apply] at this
      exact this i
    calc ‖∑ j : Fin (k i), y.1 zero ^ (j : ℕ) * g i j (Kummer.powMap (k i) (splitEquiv m y.1))‖
        ≤ ∑ j : Fin (k i), ‖y.1 zero ^ (j : ℕ) * g i j (Kummer.powMap (k i) (splitEquiv m y.1))‖ :=
          norm_sum_le _ _
      _ ≤ ∑ j, (‖g i j x'‖ + 1) := by
          refine Finset.sum_le_sum fun j _ ↦ ?_
          rw [norm_mul, norm_pow]
          calc _ ≤ 1 * ‖g i j (Kummer.powMap (k i) (splitEquiv m y.1))‖ :=
                mul_le_mul_of_nonneg_right (pow_le_one₀ (norm_nonneg _) hy1.le) (norm_nonneg _)
            _ ≤ ‖g i j x'‖ + 1 := by rw [one_mul]; exact hN j
      _ ≤ ∑ i, ∑ j, (‖g i j x'‖ + 1) :=
          Finset.single_le_sum (f := fun i ↦ ∑ j, (‖g i j x'‖ + 1))
            (fun i _ ↦ Finset.sum_nonneg fun j _ ↦ by positivity) (Finset.mem_univ i)


/-- **Uniqueness of the coefficients**: two families `g`, `g'` of holomorphic functions on `V`
describing the same section on the `i`-th Kummer cover agree on `V`. -/
theorem eqOn_of_forall_eval_eq {V : Set (ULift.{u} (Fin (m + 1)) → ℂ)} (hV : IsOpen V)
    (hVB : ∀ x ∈ V, (splitEquiv m x).1 ∈ B ∧ ‖x zero‖ < 1) (i : ι)
    {g g' : Fin (k i) → (ULift.{u} (Fin m) → ℂ) × ℂ → ℂ}
    (hg : ∀ j, ContinuousOn (g j) ((splitEquiv m).symm ⁻¹' V))
    (hg' : ∀ j, ContinuousOn (g' j) ((splitEquiv m).symm ⁻¹' V))
    (h : ∀ (y : punctured hB)
      (_ : W.hom.toLRSHom.base ((piece e i).toLRSHom.base y) ∈ puncturedPreimage hB hV),
      ∑ j : Fin (k i), y.1 zero ^ (j : ℕ) * g j (Kummer.powMap (k i) (splitEquiv m y.1)) =
        ∑ j : Fin (k i), y.1 zero ^ (j : ℕ) * g' j (Kummer.powMap (k i) (splitEquiv m y.1)))
    (j : Fin (k i)) : Set.EqOn (g j) (g' j) ((splitEquiv m).symm ⁻¹' V) := by
  have hV' : IsOpen ((splitEquiv m).symm ⁻¹' V) := hV.preimage (splitEquiv m).symm.continuous
  have := Kummer.eqOn_zero_of_sum_pow_mul_comp_powMap (k i).pos hV'
    (g := fun j ↦ g j - g' j) (fun j ↦ (hg j).sub (hg' j)) (fun z hz ↦ ?_) j
  · exact fun x hx ↦ sub_eq_zero.1 (this hx)
  obtain ⟨hx, hw⟩ := exists_mem_puncturedPreimage e hV hVB i hz
  have := h ⟨_, hx⟩ hw
  simp only [Homeomorph.apply_symm_apply] at this
  simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib, Pi.zero_apply]
  exact sub_eq_zero.2 this

end

end KummerModel

end ComplexAnalytic
