/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.ES.Codim2.Descent
import Oka.Analytification.GAGA.ProjectiveLineCoherentGenerators
import Oka.AnalyticSpace.HolomorphicMapOpen

/-!
# Bounded sections on the blow-up of a codimension two centre

Keep the notation of `Oka/Analytification/RET/ES/BoundedSections.lean`: `p : W ⟶ N°` is a finite
étale cover, `N° ⊆ N ⊆ ℂⁿ`, and `𝒜` is the sheaf of bounded sections. Let `τ`, `ω` be holomorphic
functions on `N` with `τ ≠ 0` on `N°` (`ComplexAnalytic.BoundedSections.BlowupData`); typically
`τ = t` and `ω = w - φ(y, t)`, the centre is `C = {τ = ω = 0}` and `N ∖ N°` contains `{t = 0}`.

The blow-up `Ñ = {(x, [a : b]) | a ω(x) = b τ(x)}` of `N` along `C` lies in `P^an = ℂⁿ × ℙ¹`
(`ComplexAnalytic.relProjectiveSpaceAn n 1`), and `N°` embeds into it by
`x ↦ (x, [τ(x) : ω(x)])`, i.e. by the point with fibre coordinate `ω / τ` in the chart `0`
(`ComplexAnalytic.BoundedSections.BlowupData.map`). Composing with `p` gives
`ρ : W ⟶ P^an` (`ComplexAnalytic.BoundedSections.BlowupData.proj`), and the sections of `ρ_* 𝒪_W`
bounded near the points of `P^an` over `ℂⁿ ∖ N°` form a sheaf of `𝒪_{P^an}`-modules `𝒢`
(`ComplexAnalytic.BoundedSections.BlowupData.module`): the pushforward to `P^an` of the sheaf of
bounded sections of the pulled-back cover of `Ñ ∖ σ⁻¹(N ∖ N°)`.

This file provides the description of sections of `𝒢` by their values
(`ComplexAnalytic.BoundedSections.BlowupData.gVal`) and the values of the structure sheaf of `P^an`
along `ρ` in both charts (`ComplexAnalytic.BoundedSections.BlowupData.eval_proj_base`).

## Main definitions

- `ComplexAnalytic.BoundedSections.BlowupData N N₀`: the functions `τ`, `ω`.
- `ComplexAnalytic.BoundedSections.BlowupData.map`: the embedding `N° ⟶ P^an`.
- `ComplexAnalytic.BoundedSections.BlowupData.module`: the sheaf `𝒢` on `P^an`.
-/

open CategoryTheory Opposite AlgebraicGeometry Topology TopologicalSpace Filter

universe u

namespace ComplexAnalytic.BoundedSections

open AnalyticSpace relProjectiveSpaceAn relProjectiveLine AlgebraicGeometry.LocallyRingedSpace

noncomputable section

variable {n : ℕ}

/-! ### Coordinates -/

/-- The coordinates of a point of `ℂⁿ`, as a point of `Fin n → ℂ`. -/
def baseCoord (x : Cn.{u} n) : Fin n → ℂ :=
  fun j ↦ x (ULift.up j)

/-- A point of `Fin n → ℂ`, as a point of `ℂⁿ`. -/
def ofBase (y : Fin n → ℂ) : Cn.{u} n :=
  fun j ↦ y j.down

@[simp]
lemma baseCoord_ofBase (y : Fin n → ℂ) : baseCoord (ofBase.{u} y) = y :=
  rfl

@[simp]
lemma ofBase_baseCoord (x : Cn.{u} n) : ofBase (baseCoord x) = x :=
  rfl

lemma continuous_baseCoord : Continuous (baseCoord.{u} (n := n)) :=
  continuous_pi fun _ ↦ continuous_apply _

lemma continuous_ofBase : Continuous (ofBase.{u} (n := n)) :=
  continuous_pi fun _ ↦ continuous_apply _

lemma differentiable_baseCoord : Differentiable ℂ (baseCoord.{u} (n := n)) :=
  differentiable_pi.2 fun _ ↦ differentiable_apply _

/-- The open of `Fin n → ℂ` corresponding to an open of `ℂⁿ`. -/
def baseOpens (G : Opens (Cn.{u} n)) : Opens (Fin n → ℂ) :=
  ⟨ofBase ⁻¹' G, G.isOpen.preimage continuous_ofBase⟩

@[simp]
lemma mem_baseOpens {G : Opens (Cn.{u} n)} {y : Fin n → ℂ} : y ∈ baseOpens G ↔ ofBase y ∈ G :=
  Iff.rfl

/-- The point `cpt p` of `ℂ^{1+n}`, as a function `ULift (Fin (1 + n)) → ℂ`. -/
def cptFun (p : (Fin n → ℂ) × ℂ) : ULift.{u} (Fin (1 + n)) → ℂ :=
  cpt.{u} p

/-- The chart coordinates `ℂⁿ × ℂ → ℂ^{1+n}` of `P^an = ℂⁿ × ℙ¹` are holomorphic. -/
lemma differentiable_cptFun : Differentiable ℂ (cptFun.{u} (n := n)) := by
  refine differentiable_pi.2 fun k ↦ ?_
  change Differentiable ℂ fun p : (Fin n → ℂ) × ℂ ↦ Fin.append ![p.2] p.1 k.down
  induction k.down using Fin.addCases with
  | left l => simp [Fin.append_left, Subsingleton.elim l 0]
  | right j =>
    simp only [Fin.append_right]
    fun_prop

/-! ### The data of the blow-up -/

variable (N N₀ : (AnalyticSpace.complexAffineSpace.{u} n).Opens)

/-- **The data of a blow-up along `{τ = ω = 0}`**: holomorphic functions `τ`, `ω` on `N` with
`τ ≠ 0` on `N°`. -/
structure BlowupData where
  /-- The function `τ`, typically the coordinate `t`. -/
  τ : Cn.{u} n → ℂ
  /-- The function `ω`, typically `w - φ(y, t)`. -/
  ω : Cn.{u} n → ℂ
  differentiableOn_τ : DifferentiableOn ℂ τ {x : Cn.{u} n | x ∈ N}
  differentiableOn_ω : DifferentiableOn ℂ ω {x : Cn.{u} n | x ∈ N}
  τ_ne_zero : ∀ x ∈ N₀, τ x ≠ 0

namespace BlowupData

variable {N N₀} (h₀ : N₀ ≤ N) (c : BlowupData N N₀)

/-- The point `(x, [τ(x) : ω(x)])` of `P^an`, i.e. the point with fibre coordinate `ω / τ` in the
chart `0`. -/
def blowupPt (x : Cn.{u} n) : relProjectiveSpaceAn.{u} n 1 :=
  chartPt 0 (baseCoord x, c.ω x / c.τ x)

@[simp]
lemma baseY_blowupPt (x : Cn.{u} n) : baseY (c.blowupPt x) = baseCoord x := by
  simp [blowupPt]

include h₀ in
lemma differentiableOn_div :
    DifferentiableOn ℂ (fun x ↦ c.ω x / c.τ x) {x : Cn.{u} n | x ∈ N₀} := by
  have hs : {x : Cn.{u} n | x ∈ N₀} ⊆ {x : Cn.{u} n | x ∈ N} := fun x hx ↦ h₀ hx
  simp only [div_eq_mul_inv]
  exact fun x hx ↦ ((c.differentiableOn_ω x (hs hx)).mono hs).mul
    (((c.differentiableOn_τ x (hs hx)).mono hs).inv (c.τ_ne_zero x hx))

include h₀ in
/-- The coordinates in `ℂ^{1+n}` of the points `(x, ω(x) / τ(x))` of the chart `0`, as
holomorphic functions on `N°`. -/
def mapCoord (k : ULift.{u} (Fin (1 + n))) : (space N₀).presheaf.obj (op ⊤) :=
  OkaRing.ofDifferentiableOn (fun x ↦ cptFun.{u} (baseCoord x, c.ω x / c.τ x) k) (by
    have hd : DifferentiableOn ℂ (fun x : Cn.{u} n ↦ cptFun.{u} (baseCoord x, c.ω x / c.τ x))
        {x : Cn.{u} n | x ∈ N₀} :=
      differentiable_cptFun.comp_differentiableOn
        (differentiable_baseCoord.differentiableOn.prodMk (c.differentiableOn_div h₀))
    exact ((differentiableOn_pi.1 hd) k).mono fun x hx ↦ (mem_functor_obj_top_iff N₀ x).1 hx)

/-- **The embedding `N° ⟶ P^an`**, `x ↦ (x, [τ(x) : ω(x)])`. -/
def map : space N₀ ⟶ relProjectiveSpaceAn.{u} n 1 :=
  okaMapOpen (c.mapCoord h₀) ≫ relProjectiveSpaceAnChart.{u} 0

lemma map_base (x : space N₀) : (c.map h₀).toLRSHom.base x = c.blowupPt x.1 := by
  change (chartLRS.{u} 0).base ((okaMapOpenHom (c.mapCoord h₀)).base x) = _
  rw [base_okaMapOpenHom, blowupPt, chartPt]
  congr 1
  funext k
  exact OkaRing.toGlobalFun_apply (U := img (⊤ : (space N₀).Opens)) _
    ((mem_functor_obj_top_iff N₀ x.1).2 x.2)

variable (W : FiniteEtaleOver (space N₀))

/-- **The map `ρ : W ⟶ P^an`**, the composite of `p` and the embedding `N° ⟶ P^an`. -/
def proj : W.left ⟶ relProjectiveSpaceAn.{u} n 1 :=
  cov W ≫ c.map h₀

lemma proj_base (w : W.left) : (c.proj h₀ W).toLRSHom.base w = c.blowupPt (pt W w) :=
  c.map_base h₀ _

variable (N₀) in
/-- The points of `P^an` over `ℂⁿ ∖ N°`. -/
def removed : Set (relProjectiveSpaceAn.{u} n 1) :=
  {p | ofBase (baseY p) ∉ N₀}

/-- **The sheaf `𝒢` on `P^an`** of sections of `ρ_* 𝒪_W` bounded near the points over
`ℂⁿ ∖ N°`. -/
abbrev module : SheafOfModules.{u} (relProjectiveSpaceAn.{u} n 1).ringSheaf :=
  boundedPushforward (c.proj h₀ W) (removed N₀)

/-! ### Sections of `𝒢` by their values -/

variable {h₀ c W}

/-- A section of `𝒢` over `O`, as a section of `𝒪_W` over `ρ⁻¹(O)`. -/
def gVal {O : (relProjectiveSpaceAn.{u} n 1).Opens} (s : (c.module h₀ W).val.obj (op O)) :
    W.left.presheaf.obj (op ((Opens.map (c.proj h₀ W).toLRSHom.base).obj O)) :=
  s.1

lemma gVal_mem {O : (relProjectiveSpaceAn.{u} n 1).Opens} (s : (c.module h₀ W).val.obj (op O)) :
    IsBoundedNear (c.proj h₀ W) (removed N₀) (gVal s) :=
  s.2

lemma mem_proj_preimage {O : (relProjectiveSpaceAn.{u} n 1).Opens} {w : W.left} :
    w ∈ (Opens.map (c.proj h₀ W).toLRSHom.base).obj O ↔ c.blowupPt (pt W w) ∈ O := by
  change (c.proj h₀ W).toLRSHom.base w ∈ O ↔ _
  rw [proj_base]

variable (c h₀ W) in
/-- A section of `𝒪_W` over `ρ⁻¹(O)` bounded near the points over `ℂⁿ ∖ N°`, as a section of
`𝒢`. -/
def mkG {O : (relProjectiveSpaceAn.{u} n 1).Opens}
    (s : W.left.presheaf.obj (op ((Opens.map (c.proj h₀ W).toLRSHom.base).obj O)))
    (hs : IsBoundedNear (c.proj h₀ W) (removed N₀) s) : (c.module h₀ W).val.obj (op O) :=
  ⟨s, hs⟩

@[simp]
lemma gVal_mkG {O : (relProjectiveSpaceAn.{u} n 1).Opens}
    (s : W.left.presheaf.obj (op ((Opens.map (c.proj h₀ W).toLRSHom.base).obj O)))
    (hs : IsBoundedNear (c.proj h₀ W) (removed N₀) s) : gVal (mkG h₀ c W s hs) = s :=
  rfl

lemma gVal_injective {O : (relProjectiveSpaceAn.{u} n 1).Opens} :
    Function.Injective (gVal (h₀ := h₀) (c := c) (W := W) (O := O)) :=
  fun _ _ h ↦ Subtype.ext h

lemma gVal_add {O : (relProjectiveSpaceAn.{u} n 1).Opens} (s t : (c.module h₀ W).val.obj (op O)) :
    gVal (s + t) = gVal s + gVal t :=
  rfl

variable (h₀ c W) in
/-- Pulling back sections of `𝒪_{P^an}` over `O` to sections of `𝒪_W` over `ρ⁻¹(O)`. -/
def gPull (O : (relProjectiveSpaceAn.{u} n 1).Opens) :
    (relProjectiveSpaceAn.{u} n 1).presheaf.obj (op O) →+*
      W.left.presheaf.obj (op ((Opens.map (c.proj h₀ W).toLRSHom.base).obj O)) :=
  ((c.proj h₀ W).toLRSHom.c.app (op O)).hom

lemma evalFun_gPull {O : (relProjectiveSpaceAn.{u} n 1).Opens}
    (r : (relProjectiveSpaceAn.{u} n 1).presheaf.obj (op O)) {w : W.left}
    (hw : w ∈ (Opens.map (c.proj h₀ W).toLRSHom.base).obj O) :
    evalFun (gPull h₀ c W O r) w =
      (relProjectiveSpaceAn.{u} n 1).eval ((c.proj h₀ W).toLRSHom.base w) hw r := by
  rw [evalFun_of_mem _ hw]
  exact eval_c_app (c.proj h₀ W).toLRSHom (c.proj h₀ W).isCLinear w hw r

lemma gVal_smul {O : (relProjectiveSpaceAn.{u} n 1).Opens}
    (r : (relProjectiveSpaceAn.{u} n 1).presheaf.obj (op O))
    (s : (c.module h₀ W).val.obj (op O)) :
    gVal (r • s) = gPull h₀ c W O r * gVal s :=
  rfl

lemma gVal_modRes {O O' : (relProjectiveSpaceAn.{u} n 1).Opens} (h : O' ≤ O)
    (s : (c.module h₀ W).val.obj (op O)) :
    gVal (modRes s O' h) =
      W.left.presheaf.map (homOfLE ((Opens.map (c.proj h₀ W).toLRSHom.base).monotone h)).op
        (gVal s) :=
  rfl

lemma evalFun_gVal_add {O : (relProjectiveSpaceAn.{u} n 1).Opens}
    (s t : (c.module h₀ W).val.obj (op O)) {w : W.left}
    (hw : w ∈ (Opens.map (c.proj h₀ W).toLRSHom.base).obj O) :
    evalFun (gVal (s + t)) w = evalFun (gVal s) w + evalFun (gVal t) w := by
  rw [gVal_add, evalFun_add W _ _ hw]

lemma evalFun_gVal_smul {O : (relProjectiveSpaceAn.{u} n 1).Opens}
    (r : (relProjectiveSpaceAn.{u} n 1).presheaf.obj (op O))
    (s : (c.module h₀ W).val.obj (op O)) {w : W.left}
    (hw : w ∈ (Opens.map (c.proj h₀ W).toLRSHom.base).obj O) :
    evalFun (gVal (r • s)) w =
      (relProjectiveSpaceAn.{u} n 1).eval ((c.proj h₀ W).toLRSHom.base w) hw r *
        evalFun (gVal s) w := by
  rw [gVal_smul, evalFun_mul W _ _ hw, evalFun_gPull]

lemma evalFun_gVal_sum {O : (relProjectiveSpaceAn.{u} n 1).Opens} {ι : Type*} (t : Finset ι)
    (s : ι → (c.module h₀ W).val.obj (op O)) {w : W.left}
    (hw : w ∈ (Opens.map (c.proj h₀ W).toLRSHom.base).obj O) :
    evalFun (gVal (∑ i ∈ t, s i)) w = ∑ i ∈ t, evalFun (gVal (s i)) w := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    change evalFun (0 : W.left.presheaf.obj _) w = 0
    rw [evalFun_of_mem _ hw, map_zero]
  | insert j t hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, evalFun_gVal_add _ _ hw, ih]

lemma evalFun_gVal_modRes {O O' : (relProjectiveSpaceAn.{u} n 1).Opens} (h : O' ≤ O)
    (s : (c.module h₀ W).val.obj (op O)) {w : W.left}
    (hw : w ∈ (Opens.map (c.proj h₀ W).toLRSHom.base).obj O') :
    evalFun (gVal (modRes s O' h)) w = evalFun (gVal s) w := by
  rw [gVal_modRes, evalFun_map W _ _ hw]

/-! ### The two charts -/

variable (c) in
/-- The function which generates the ideal of the exceptional divisor in the chart `i`: `τ` in
the chart `0` and `ω` in the chart `1`. -/
def θ : Fin 2 → Cn.{u} n → ℂ
  | 0 => c.τ
  | 1 => c.ω

variable (c) in
/-- The fibre coordinate in the chart `i`: `ω / τ` in the chart `0` and `τ / ω` in the
chart `1`. -/
def ζ : Fin 2 → Cn.{u} n → ℂ
  | 0 => fun x ↦ c.ω x / c.τ x
  | 1 => fun x ↦ c.τ x / c.ω x

/-- A section of `𝒪_{P^an}` in the coordinates of the chart `i`. -/
def chartFun {O : (relProjectiveSpaceAn.{u} n 1).Opens} :
    Fin 2 → (relProjectiveSpaceAn.{u} n 1).presheaf.obj (op O) → (Fin n → ℂ) × ℂ → ℂ
  | 0 => f0
  | 1 => f1

lemma chartFun_eq_eval {O : (relProjectiveSpaceAn.{u} n 1).Opens} (i : Fin 2)
    (a : (relProjectiveSpaceAn.{u} n 1).presheaf.obj (op O)) {p : (Fin n → ℂ) × ℂ}
    (hp : chartPt.{u} i p ∈ O) :
    chartFun i a p = (relProjectiveSpaceAn.{u} n 1).eval (chartPt.{u} i p) hp a := by
  fin_cases i
  exacts [f0_eq_eval a hp, f1_eq_eval a hp]

lemma differentiableOn_chartFun (i : Fin 2) {S : Opens ((Fin n → ℂ) × ℂ)}
    (a : (relProjectiveSpaceAn.{u} n 1).presheaf.obj (op (chartBox.{u} i S))) :
    DifferentiableOn ℂ (chartFun i a) S := by
  fin_cases i
  exacts [differentiableOn_f0 a, differentiableOn_f1 a]

lemma chartFun_restrictOpen {O O' : (relProjectiveSpaceAn.{u} n 1).Opens} (i : Fin 2)
    (h : O' ≤ O) (a : (relProjectiveSpaceAn.{u} n 1).presheaf.obj (op O))
    {p : (Fin n → ℂ) × ℂ} (hp : chartPt.{u} i p ∈ O') :
    chartFun i (TopCat.Presheaf.restrictOpen a O' h) p = chartFun i a p := by
  fin_cases i
  exacts [f0_restrictOpen h a hp, f1_restrictOpen h a hp]

lemma chartPt_mem_stdOpen (i : Fin 2) (p : (Fin n → ℂ) × ℂ) :
    chartPt.{u} i p ∈ stdOpen.{u} n 1 i := by
  rw [stdOpen_eq_chartOpens]
  exact ⟨cpt p, rfl⟩

lemma blowupPt_mem_stdOpen_zero (x : Cn.{u} n) : c.blowupPt x ∈ stdOpen.{u} n 1 0 :=
  chartPt_mem_stdOpen 0 _

/-- Where `τ ≠ 0` and `θᵢ ≠ 0`, the point `(x, [τ(x) : ω(x)])` has fibre coordinate `ζᵢ(x)` in the
chart `i`. -/
lemma blowupPt_eq_chartPt (i : Fin 2) {x : Cn.{u} n} (hτ : c.τ x ≠ 0) (hθ : c.θ i x ≠ 0) :
    c.blowupPt x = chartPt i (baseCoord x, c.ζ i x) := by
  fin_cases i
  · rfl
  · change chartPt 0 (baseCoord x, c.ω x / c.τ x) = chartPt 1 (baseCoord x, c.τ x / c.ω x)
    have hθ' : c.ω x ≠ 0 := hθ
    rw [chartPt_zero_eq_chartPt_one (div_ne_zero hθ' hτ), inv_div]

/-- If `(x, [τ(x) : ω(x)])` lies in the chart `i`, then `θᵢ(x) ≠ 0`. -/
lemma θ_ne_zero_of_mem_stdOpen (i : Fin 2) {x : Cn.{u} n} (hτ : c.τ x ≠ 0)
    (h : c.blowupPt x ∈ stdOpen.{u} n 1 i) : c.θ i x ≠ 0 := by
  fin_cases i
  · exact hτ
  · change c.ω x ≠ 0
    rw [stdOpen_eq_chartOpens] at h
    have := (chartPt_zero_mem_range_chart_one_iff _).1 h
    exact fun h0 ↦ this (by simp [h0])

lemma differentiableOn_θ (i : Fin 2) : DifferentiableOn ℂ (c.θ i) {x : Cn.{u} n | x ∈ N} := by
  fin_cases i
  exacts [c.differentiableOn_τ, c.differentiableOn_ω]

lemma differentiableOn_ζ (i : Fin 2) :
    DifferentiableOn ℂ (c.ζ i) {x : Cn.{u} n | x ∈ N ∧ c.θ i x ≠ 0} := by
  have hs : {x : Cn.{u} n | x ∈ N ∧ c.θ i x ≠ 0} ⊆ {x : Cn.{u} n | x ∈ N} := fun x hx ↦ hx.1
  fin_cases i
  · change DifferentiableOn ℂ (fun x ↦ c.ω x / c.τ x) _
    simp only [div_eq_mul_inv]
    exact fun x hx ↦ ((c.differentiableOn_ω x hx.1).mono hs).mul
      (((c.differentiableOn_τ x hx.1).mono hs).inv hx.2)
  · change DifferentiableOn ℂ (fun x ↦ c.τ x / c.ω x) _
    simp only [div_eq_mul_inv]
    exact fun x hx ↦ ((c.differentiableOn_τ x hx.1).mono hs).mul
      (((c.differentiableOn_ω x hx.1).mono hs).inv hx.2)

/-- **Values of sections of `𝒪_{P^an}` along `ρ`**, in the coordinates of the chart `i`. -/
lemma eval_proj_base {O : (relProjectiveSpaceAn.{u} n 1).Opens}
    (a : (relProjectiveSpaceAn.{u} n 1).presheaf.obj (op O)) {w : W.left}
    (hw : w ∈ (Opens.map (c.proj h₀ W).toLRSHom.base).obj O) (i : Fin 2)
    (hθ : c.θ i (pt W w) ≠ 0) :
    (relProjectiveSpaceAn.{u} n 1).eval ((c.proj h₀ W).toLRSHom.base w) hw a =
      chartFun i a (baseCoord (pt W w), c.ζ i (pt W w)) := by
  have h : (c.proj h₀ W).toLRSHom.base w = chartPt i (baseCoord (pt W w), c.ζ i (pt W w)) :=
    (c.proj_base h₀ W w).trans
      (c.blowupPt_eq_chartPt i (c.τ_ne_zero _ (pt_mem W w)) hθ)
  have hp : chartPt.{u} i (baseCoord (pt W w), c.ζ i (pt W w)) ∈ O := h ▸ hw
  rw [chartFun_eq_eval i a hp]
  exact eval_congr_point h _ _ a

end BlowupData

end

end ComplexAnalytic.BoundedSections
