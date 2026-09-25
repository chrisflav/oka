/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.ES.Codim2.GraphEmbedding

/-!
# The charts of the blow-up of `{t = 0, w = φ}` inside `ℂⁿ × ℙ¹`

Let `t = x_{i_t}` and `w = x_{i_w}` be two coordinates of `ℂⁿ` and let `φ` be holomorphic and
independent of `w` (`ComplexAnalytic.BoundedSections.BlowupCentre`), with `t ≠ 0` on `N°`. The
blow-up of `N` along `C = {t = 0, w = φ}` is covered by two charts, which in coordinates are
(`Codim2.chart₁`, `Codim2.chart₂`)

* `ch₁ : (…, t, v) ↦ (…, t, φ + t v)`, embedded into the chart `0` of `ℂⁿ × ℙ¹` by
  `Γ₁ = (ch₁, v)`;
* `ch₂ : (…, s, v') ↦ (…, s v', φ + s)`, embedded into the chart `1` of `ℂⁿ × ℙ¹` by
  `Γ₂ = (ch₂, v')`.

In both cases the image of `Γᵢ` is a hypersurface `hᵢ = 0` with a holomorphic retraction, in the
sense of `ComplexAnalytic.BoundedSections.GraphEmbeddingData`
(`ComplexAnalytic.BoundedSections.BlowupCentre.graph₁`, `…BlowupCentre.graph₂`), and on the
charts over `N°` the embedding `x ↦ (x, [τ(x) : ω(x)])` of
`Oka/Analytification/RET/ES/Codim2/BlowupSheaf.lean` is `Γᵢ ∘ chᵢ⁻¹`
(`…BlowupCentre.blowupPt_ch₁`, `…BlowupCentre.blowupPt_ch₂`).

## Main definitions

- `ComplexAnalytic.BoundedSections.BlowupCentre N N₀`: the coordinates `t`, `w` and `φ`.
- `ComplexAnalytic.BoundedSections.BlowupCentre.toBlowupData`: `τ = t`, `ω = w - φ`.
- `ComplexAnalytic.BoundedSections.BlowupCentre.ch₁`, `…BlowupCentre.ch₂`: the two charts, with
  domains `…BlowupCentre.M₁`, `…BlowupCentre.M₂` and `…BlowupCentre.M₁₀`, `…BlowupCentre.M₂₀`
  over `N°`.
- `ComplexAnalytic.BoundedSections.BlowupCentre.graph₁`, `…BlowupCentre.graph₂`: the embeddings
  into the charts of `ℂⁿ × ℙ¹`.
-/

open CategoryTheory Opposite AlgebraicGeometry Topology TopologicalSpace Filter

universe u

namespace ComplexAnalytic.BoundedSections

open AnalyticSpace relProjectiveSpaceAn relProjectiveLine

noncomputable section

variable {n : ℕ}

/-! ### Coordinates on `ℂ^{1+n}` -/

/-- The base point `y ∈ ℂⁿ` of a point of `ℂ^{1+n}`. -/
def cptBase (p : Cn.{u} (1 + n)) : Cn.{u} n :=
  ofBase (yPart.{u} (N := 1) p)

/-- The fibre coordinate of a point of `ℂ^{1+n}`. -/
def cptFib (p : Cn.{u} (1 + n)) : ℂ :=
  zPart.{u} (m := n) p 0

@[simp]
lemma cptBase_cptFun (b : Fin n → ℂ) (z : ℂ) : cptBase (cptFun.{u} (b, z)) = ofBase b := by
  simp [cptBase, cptFun]

@[simp]
lemma cptFib_cptFun (b : Fin n → ℂ) (z : ℂ) : cptFib (cptFun.{u} (b, z)) = z := by
  simp [cptFib, cptFun]

lemma cptFun_cptBase_cptFib (p : Cn.{u} (1 + n)) :
    cptFun (baseCoord (cptBase p), cptFib p) = p :=
  cpt_yPart_zPart p

lemma differentiable_cptBase : Differentiable ℂ (cptBase.{u} (n := n)) :=
  differentiable_pi.2 fun _ ↦ differentiable_apply _

lemma differentiable_cptFib : Differentiable ℂ (cptFib.{u} (n := n)) :=
  differentiable_apply _

/-! ### The cylinder over `N` in the direction of `w` -/

/-- The points `x` of `ℂⁿ` such that changing the coordinate `w` lands in `N`. -/
def cyl (N : (AnalyticSpace.complexAffineSpace.{u} n).Opens) (iw : ULift.{u} (Fin n)) :
    Set (Cn.{u} n) :=
  {x | ∃ a, Function.update x iw a ∈ N}

lemma isOpen_cyl (N : (AnalyticSpace.complexAffineSpace.{u} n).Opens) (iw : ULift.{u} (Fin n)) :
    IsOpen (cyl N iw) := by
  have : cyl N iw = ⋃ a : ℂ, {x : Cn.{u} n | Function.update x iw a ∈ N} := by
    ext x
    simp [cyl]
  rw [this]
  exact isOpen_iUnion fun a ↦ N.isOpen.preimage (continuous_id.update iw continuous_const)

lemma mem_cyl_of_mem {N : (AnalyticSpace.complexAffineSpace.{u} n).Opens}
    {iw : ULift.{u} (Fin n)} {x : Cn.{u} n} (hx : x ∈ N) : x ∈ cyl N iw :=
  ⟨x iw, by rwa [Function.update_eq_self]⟩

lemma update_mem_cyl {N : (AnalyticSpace.complexAffineSpace.{u} n).Opens}
    {iw : ULift.{u} (Fin n)} {x : Cn.{u} n} (a : ℂ) :
    Function.update x iw a ∈ cyl N iw ↔ x ∈ cyl N iw := by
  simp [cyl, Function.update_idem]

lemma differentiableWithinAt_update {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {F : E → Cn.{u} n} {g : E → ℂ} {s : Set E} {e : E} (hF : DifferentiableWithinAt ℂ F s e)
    (hg : DifferentiableWithinAt ℂ g s e) (i : ULift.{u} (Fin n)) :
    DifferentiableWithinAt ℂ (fun e ↦ Function.update (F e) i (g e)) s e := by
  refine differentiableWithinAt_pi.2 fun j ↦ ?_
  by_cases hj : j = i
  · subst hj
    simpa using hg
  · simpa [Function.update_of_ne hj] using differentiableWithinAt_pi.1 hF j

lemma differentiableOn_update {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {F : E → Cn.{u} n} {g : E → ℂ} {s : Set E} (hF : DifferentiableOn ℂ F s)
    (hg : DifferentiableOn ℂ g s) (i : ULift.{u} (Fin n)) :
    DifferentiableOn ℂ (fun e ↦ Function.update (F e) i (g e)) s :=
  fun e he ↦ differentiableWithinAt_update (hF e he) (hg e he) i

/-! ### The centre -/

variable (N N₀ : (AnalyticSpace.complexAffineSpace.{u} n).Opens)

/-- **The centre `{t = 0, w = φ}` of a blow-up**: two coordinates `t = x_{i_t}` and `w = x_{i_w}`
and a function `φ` independent of `w`, holomorphic where it is determined by a point of `N`, with
`t ≠ 0` on `N°`. -/
structure BlowupCentre where
  /-- The coordinate `t`. -/
  it : ULift.{u} (Fin n)
  /-- The coordinate `w`. -/
  iw : ULift.{u} (Fin n)
  it_ne_iw : it ≠ iw
  /-- The function `φ` with `C = {t = 0, w = φ}`. -/
  φ : Cn.{u} n → ℂ
  φ_update : ∀ x a, φ (Function.update x iw a) = φ x
  differentiableOn_φ : DifferentiableOn ℂ φ (cyl N iw)
  ne_zero : ∀ x ∈ N₀, x it ≠ 0

namespace BlowupCentre

variable {N N₀} (C : BlowupCentre N N₀)

/-- The data `τ = t`, `ω = w - φ` of the blow-up. -/
def toBlowupData : BlowupData N N₀ where
  τ x := x C.it
  ω x := x C.iw - C.φ x
  differentiableOn_τ := (differentiable_apply C.it).differentiableOn
  differentiableOn_ω := (differentiable_apply C.iw).differentiableOn.sub
    (C.differentiableOn_φ.mono fun _ hx ↦ mem_cyl_of_mem hx)
  τ_ne_zero := C.ne_zero

@[simp]
lemma toBlowupData_τ (x : Cn.{u} n) : C.toBlowupData.τ x = x C.it :=
  rfl

@[simp]
lemma toBlowupData_ω (x : Cn.{u} n) : C.toBlowupData.ω x = x C.iw - C.φ x :=
  rfl

/-! ### The first chart -/

/-- **The first chart** `(…, t, v) ↦ (…, t, φ + t v)`. -/
def ch₁ (x : Cn.{u} n) : Cn.{u} n :=
  Function.update x C.iw (C.φ x + x C.it * x C.iw)

@[simp]
lemma ch₁_it (x : Cn.{u} n) : C.ch₁ x C.it = x C.it :=
  Function.update_of_ne C.it_ne_iw _ _

@[simp]
lemma ch₁_iw (x : Cn.{u} n) : C.ch₁ x C.iw = C.φ x + x C.it * x C.iw :=
  Function.update_self _ _ _

@[simp]
lemma φ_ch₁ (x : Cn.{u} n) : C.φ (C.ch₁ x) = C.φ x :=
  C.φ_update _ _

lemma differentiableOn_ch₁ : DifferentiableOn ℂ C.ch₁ (cyl N C.iw) :=
  differentiableOn_update differentiableOn_id
    (C.differentiableOn_φ.add ((differentiable_apply C.it).mul
      (differentiable_apply C.iw)).differentiableOn) C.iw

lemma mem_cyl_of_ch₁_mem {x : Cn.{u} n} (hx : C.ch₁ x ∈ N) : x ∈ cyl N C.iw :=
  ⟨_, hx⟩

/-- The domain `{x | ch₁ x ∈ N}` of the first chart. -/
def M₁ : (AnalyticSpace.complexAffineSpace.{u} n).Opens :=
  ⟨{x | C.ch₁ x ∈ N}, by
    change IsOpen {x : Cn.{u} n | C.ch₁ x ∈ N}
    have heq : {x : Cn.{u} n | C.ch₁ x ∈ N} = cyl N C.iw ∩ C.ch₁ ⁻¹' {x | x ∈ N} :=
      Set.ext fun x ↦ ⟨fun hx ↦ ⟨C.mem_cyl_of_ch₁_mem hx, hx⟩, fun hx ↦ hx.2⟩
    rw [heq]
    exact C.differentiableOn_ch₁.continuousOn.isOpen_inter_preimage (isOpen_cyl N C.iw)
      N.isOpen⟩

variable (h₀ : N₀ ≤ N)

include h₀ in
/-- The part `{x | ch₁ x ∈ N°}` of the first chart over `N°`. -/
def M₁₀ : (AnalyticSpace.complexAffineSpace.{u} n).Opens :=
  ⟨{x | C.ch₁ x ∈ N₀}, by
    change IsOpen {x : Cn.{u} n | C.ch₁ x ∈ N₀}
    have heq : {x : Cn.{u} n | C.ch₁ x ∈ N₀} = cyl N C.iw ∩ C.ch₁ ⁻¹' {x | x ∈ N₀} :=
      Set.ext fun x ↦ ⟨fun hx ↦ ⟨C.mem_cyl_of_ch₁_mem (h₀ hx), hx⟩, fun hx ↦ hx.2⟩
    rw [heq]
    exact C.differentiableOn_ch₁.continuousOn.isOpen_inter_preimage (isOpen_cyl N C.iw)
      N₀.isOpen⟩

lemma M₁₀_le : C.M₁₀ h₀ ≤ C.M₁ :=
  fun _ hx ↦ h₀ hx

/-- The retraction `(y, z) ↦ (…, t, z)` of the embedding of the first chart. -/
def L₁ (p : Cn.{u} (1 + n)) : Cn.{u} n :=
  Function.update (cptBase p) C.iw (cptFib p)

/-- The equation `w - φ - t z` of the first chart in the chart `0` of `ℂⁿ × ℙ¹`. -/
def h₁ (p : Cn.{u} (1 + n)) : ℂ :=
  cptBase p C.iw - C.φ (cptBase p) - cptBase p C.it * cptFib p

/-- The embedding `x ↦ (ch₁ x, v)` of the first chart into the chart `0` of `ℂⁿ × ℙ¹`. -/
def Γ₁ (x : Cn.{u} n) : Cn.{u} (1 + n) :=
  cptFun (baseCoord (C.ch₁ x), x C.iw)

/-- The inverse of `(L₁, h₁)`. -/
def Θ₁ (q : Cn.{u} n × ℂ) : Cn.{u} (1 + n) :=
  cptFun (baseCoord (Function.update q.1 C.iw (C.φ q.1 + q.1 C.it * q.1 C.iw + q.2)), q.1 C.iw)

lemma L₁_apply_iw (p : Cn.{u} (1 + n)) : C.L₁ p C.iw = cptFib p :=
  Function.update_self _ _ _

lemma L₁_apply_it (p : Cn.{u} (1 + n)) : C.L₁ p C.it = cptBase p C.it :=
  Function.update_of_ne C.it_ne_iw _ _

lemma φ_L₁ (p : Cn.{u} (1 + n)) : C.φ (C.L₁ p) = C.φ (cptBase p) :=
  C.φ_update _ _

/-- The part of the chart `0` of `ℂⁿ × ℙ¹` over `N` which retracts onto the first chart. -/
def B₁ : (AnalyticSpace.complexAffineSpace.{u} (1 + n)).Opens :=
  ⟨{p | cptBase p ∈ N ∧ C.L₁ p ∈ C.M₁}, by
    have hL : Continuous C.L₁ :=
      continuous_pi fun j ↦ by
        by_cases hj : j = C.iw
        · subst hj
          simpa [L₁] using differentiable_cptFib.continuous
        · simp only [L₁, Function.update_of_ne hj]
          exact
            (continuous_apply j).comp differentiable_cptBase.continuous
    have h₁ : IsOpen {p : Cn.{u} (1 + n) | cptBase p ∈ N} :=
      N.isOpen.preimage differentiable_cptBase.continuous
    have hc : ContinuousOn (fun p ↦ C.ch₁ (C.L₁ p)) {p : Cn.{u} (1 + n) | cptBase p ∈ N} :=
      C.differentiableOn_ch₁.continuousOn.comp hL.continuousOn fun p hp ↦
        ⟨cptBase p C.iw, by rw [L₁, Function.update_idem, Function.update_eq_self]; exact hp⟩
    exact hc.isOpen_inter_preimage h₁ N.isOpen⟩

lemma M₁_le_cyl {x : Cn.{u} n} (hx : x ∈ C.M₁) : x ∈ cyl N C.iw :=
  C.mem_cyl_of_ch₁_mem hx

lemma ch₁_mem_of_mem_M₁ {x : Cn.{u} n} (hx : x ∈ C.M₁) : C.ch₁ x ∈ N :=
  hx

lemma L₁_Γ₁ (x : Cn.{u} n) : C.L₁ (C.Γ₁ x) = x := by
  simp [L₁, Γ₁, ch₁, Function.update_idem]

/-- **The first chart as an embedding into the chart `0` of `ℂⁿ × ℙ¹`.** -/
def graph₁ : GraphEmbeddingData C.M₁ C.B₁ where
  Γ := C.Γ₁
  L := C.L₁
  h := C.h₁
  Θ := C.Θ₁
  domΘ := {q | q.1 ∈ cyl N C.iw}
  isOpen_domΘ := (isOpen_cyl N C.iw).preimage continuous_fst
  differentiableOn_Γ := by
    have h₁ : DifferentiableOn ℂ C.ch₁ {a : Cn.{u} n | a ∈ C.M₁} :=
      C.differentiableOn_ch₁.mono fun x hx ↦ C.M₁_le_cyl hx
    have hb := differentiable_baseCoord.{u} (n := n)
    have hc := differentiable_cptFun.{u} (n := n)
    change DifferentiableOn ℂ (fun x ↦ cptFun (baseCoord (C.ch₁ x), x C.iw)) _
    fun_prop
  differentiableOn_L := differentiableOn_update differentiable_cptBase.differentiableOn
    differentiable_cptFib.differentiableOn C.iw
  differentiableOn_h := by
    have hφ : DifferentiableOn ℂ (fun p ↦ C.φ (cptBase p)) {p : Cn.{u} (1 + n) | p ∈ C.B₁} :=
      C.differentiableOn_φ.comp differentiable_cptBase.differentiableOn fun p hp ↦
        mem_cyl_of_mem hp.1
    have hb := differentiable_cptBase.{u} (n := n)
    have hf := differentiable_cptFib.{u} (n := n)
    change DifferentiableOn ℂ
      (fun p ↦ cptBase p C.iw - C.φ (cptBase p) - cptBase p C.it * cptFib p) _
    fun_prop
  differentiableOn_Θ := by
    set S : Set (Cn.{u} n × ℂ) := {q | q.1 ∈ cyl N C.iw}
    have hφ : DifferentiableOn ℂ (fun q : Cn.{u} n × ℂ ↦ C.φ q.1) S :=
      C.differentiableOn_φ.comp differentiable_fst.differentiableOn fun q hq ↦ hq
    have hs : DifferentiableOn ℂ
        (fun q : Cn.{u} n × ℂ ↦ C.φ q.1 + q.1 C.it * q.1 C.iw + q.2) S := by
      fun_prop
    have hu : DifferentiableOn ℂ (fun q : Cn.{u} n × ℂ ↦
        Function.update q.1 C.iw (C.φ q.1 + q.1 C.it * q.1 C.iw + q.2)) S :=
      differentiableOn_update differentiable_fst.differentiableOn hs C.iw
    have hb := differentiable_baseCoord.{u} (n := n)
    have hc := differentiable_cptFun.{u} (n := n)
    change DifferentiableOn ℂ (fun q : Cn.{u} n × ℂ ↦ cptFun (baseCoord
      (Function.update q.1 C.iw (C.φ q.1 + q.1 C.it * q.1 C.iw + q.2)), q.1 C.iw)) S
    fun_prop
  Γ_mem a ha := by
    refine ⟨?_, ?_⟩
    · simpa [Γ₁] using C.ch₁_mem_of_mem_M₁ ha
    · rw [L₁_Γ₁]
      exact ha
  L_mem _ hp := hp.2
  L_Γ a _ := C.L₁_Γ₁ a
  h_Γ a _ := by
    simp only [h₁, Γ₁, cptBase_cptFun, cptFib_cptFun, ofBase_baseCoord, ch₁_iw, φ_ch₁, ch₁_it]
    ring
  mem_domΘ _ hp := C.M₁_le_cyl hp.2
  Θ_zero a _ := by
    simp [Θ₁, Γ₁, ch₁]
  Θ_L p _ := by
    have : C.φ (C.L₁ p) + C.L₁ p C.it * C.L₁ p C.iw + C.h₁ p = cptBase p C.iw := by
      rw [φ_L₁, L₁_apply_it, L₁_apply_iw, h₁]
      ring
    change cptFun (baseCoord (Function.update (C.L₁ p) C.iw
      (C.φ (C.L₁ p) + C.L₁ p C.it * C.L₁ p C.iw + C.h₁ p)), C.L₁ p C.iw) = p
    rw [this, L₁_apply_iw, L₁, Function.update_idem, Function.update_eq_self]
    exact cptFun_cptBase_cptFib p

/-! ### The second chart -/

/-- The point `(…, s v', v')` of the second chart, with `t = s v'` in the place of `s`. -/
def ta (a : Cn.{u} n) : Cn.{u} n :=
  Function.update a C.it (a C.it * a C.iw)

/-- **The second chart** `(…, s, v') ↦ (…, s v', φ + s)`. -/
def ch₂ (a : Cn.{u} n) : Cn.{u} n :=
  Function.update (C.ta a) C.iw (C.φ (C.ta a) + a C.it)

@[simp]
lemma ta_iw (a : Cn.{u} n) : C.ta a C.iw = a C.iw :=
  Function.update_of_ne C.it_ne_iw.symm _ _

@[simp]
lemma ch₂_it (a : Cn.{u} n) : C.ch₂ a C.it = a C.it * a C.iw := by
  rw [ch₂, Function.update_of_ne C.it_ne_iw, ta, Function.update_self]

@[simp]
lemma ch₂_iw (a : Cn.{u} n) : C.ch₂ a C.iw = C.φ (C.ta a) + a C.it :=
  Function.update_self _ _ _

@[simp]
lemma φ_ch₂ (a : Cn.{u} n) : C.φ (C.ch₂ a) = C.φ (C.ta a) :=
  C.φ_update _ _

lemma continuous_ta : Continuous C.ta :=
  continuous_id.update C.it ((continuous_apply C.it).mul (continuous_apply C.iw))

lemma differentiable_ta : Differentiable ℂ C.ta := by
  have h : Differentiable ℂ fun a : Cn.{u} n ↦ a C.it * a C.iw := by fun_prop
  exact fun a ↦ (differentiableWithinAt_update (s := Set.univ)
    differentiable_id.differentiableAt.differentiableWithinAt (h a).differentiableWithinAt
    C.it).differentiableAt Filter.univ_mem

/-- The points where the second chart is holomorphic. -/
def dom₂ : Set (Cn.{u} n) :=
  C.ta ⁻¹' cyl N C.iw

lemma isOpen_dom₂ : IsOpen C.dom₂ :=
  (isOpen_cyl N C.iw).preimage C.continuous_ta

lemma differentiableOn_φ_ta : DifferentiableOn ℂ (fun a ↦ C.φ (C.ta a)) C.dom₂ :=
  C.differentiableOn_φ.comp C.differentiable_ta.differentiableOn fun _ ha ↦ ha

lemma differentiableOn_ch₂ : DifferentiableOn ℂ C.ch₂ C.dom₂ :=
  differentiableOn_update C.differentiable_ta.differentiableOn
    (C.differentiableOn_φ_ta.add (differentiable_apply C.it).differentiableOn) C.iw

lemma mem_dom₂_of_ch₂_mem {a : Cn.{u} n} (ha : C.ch₂ a ∈ N) : a ∈ C.dom₂ :=
  ⟨_, ha⟩

/-- The domain `{a | ch₂ a ∈ N}` of the second chart. -/
def M₂ : (AnalyticSpace.complexAffineSpace.{u} n).Opens :=
  ⟨{a | C.ch₂ a ∈ N}, by
    change IsOpen {a : Cn.{u} n | C.ch₂ a ∈ N}
    have heq : {a : Cn.{u} n | C.ch₂ a ∈ N} = C.dom₂ ∩ C.ch₂ ⁻¹' {x | x ∈ N} :=
      Set.ext fun a ↦ ⟨fun ha ↦ ⟨C.mem_dom₂_of_ch₂_mem ha, ha⟩, fun ha ↦ ha.2⟩
    rw [heq]
    exact C.differentiableOn_ch₂.continuousOn.isOpen_inter_preimage C.isOpen_dom₂ N.isOpen⟩

include h₀ in
/-- The part `{a | ch₂ a ∈ N°}` of the second chart over `N°`. -/
def M₂₀ : (AnalyticSpace.complexAffineSpace.{u} n).Opens :=
  ⟨{a | C.ch₂ a ∈ N₀}, by
    change IsOpen {a : Cn.{u} n | C.ch₂ a ∈ N₀}
    have heq : {a : Cn.{u} n | C.ch₂ a ∈ N₀} = C.dom₂ ∩ C.ch₂ ⁻¹' {x | x ∈ N₀} :=
      Set.ext fun a ↦ ⟨fun ha ↦ ⟨C.mem_dom₂_of_ch₂_mem (h₀ ha), ha⟩, fun ha ↦ ha.2⟩
    rw [heq]
    exact C.differentiableOn_ch₂.continuousOn.isOpen_inter_preimage C.isOpen_dom₂ N₀.isOpen⟩

lemma M₂₀_le : C.M₂₀ h₀ ≤ C.M₂ :=
  fun _ ha ↦ h₀ ha

lemma M₂_le_dom₂ {a : Cn.{u} n} (ha : a ∈ C.M₂) : a ∈ C.dom₂ :=
  C.mem_dom₂_of_ch₂_mem ha

/-- The retraction `(y, z') ↦ (…, w - φ, z')` of the embedding of the second chart. -/
def L₂ (p : Cn.{u} (1 + n)) : Cn.{u} n :=
  Function.update (Function.update (cptBase p) C.it (cptBase p C.iw - C.φ (cptBase p))) C.iw
    (cptFib p)

/-- The equation `t - z' (w - φ)` of the second chart in the chart `1` of `ℂⁿ × ℙ¹`. -/
def h₂ (p : Cn.{u} (1 + n)) : ℂ :=
  cptBase p C.it - cptFib p * (cptBase p C.iw - C.φ (cptBase p))

/-- The embedding `a ↦ (ch₂ a, v')` of the second chart into the chart `1` of `ℂⁿ × ℙ¹`. -/
def Γ₂ (a : Cn.{u} n) : Cn.{u} (1 + n) :=
  cptFun (baseCoord (C.ch₂ a), a C.iw)

/-- The point `(…, η + s v', v')`. -/
def ta' (q : Cn.{u} n × ℂ) : Cn.{u} n :=
  Function.update q.1 C.it (q.2 + q.1 C.it * q.1 C.iw)

/-- The inverse of `(L₂, h₂)`. -/
def Θ₂ (q : Cn.{u} n × ℂ) : Cn.{u} (1 + n) :=
  cptFun (baseCoord (Function.update (C.ta' q) C.iw (C.φ (C.ta' q) + q.1 C.it)), q.1 C.iw)

lemma L₂_it (p : Cn.{u} (1 + n)) : C.L₂ p C.it = cptBase p C.iw - C.φ (cptBase p) := by
  rw [L₂, Function.update_of_ne C.it_ne_iw, Function.update_self]

lemma L₂_iw (p : Cn.{u} (1 + n)) : C.L₂ p C.iw = cptFib p :=
  Function.update_self _ _ _

lemma continuous_L₂_on : ContinuousOn C.L₂ {p : Cn.{u} (1 + n) | cptBase p ∈ N} := by
  have hφ : ContinuousOn (fun p ↦ C.φ (cptBase p)) {p : Cn.{u} (1 + n) | cptBase p ∈ N} :=
    C.differentiableOn_φ.continuousOn.comp differentiable_cptBase.continuous.continuousOn
      fun _ hp ↦ mem_cyl_of_mem hp
  refine continuousOn_pi.2 fun j ↦ ?_
  by_cases hj : j = C.iw
  · subst hj
    simpa [L₂] using differentiable_cptFib.continuous.continuousOn
  by_cases hj' : j = C.it
  · subst hj'
    simp only [L₂, Function.update_of_ne hj, Function.update_self]
    exact (((continuous_apply _).comp differentiable_cptBase.continuous).continuousOn.sub hφ)
  · simp only [L₂, Function.update_of_ne hj, Function.update_of_ne hj']
    exact ((continuous_apply j).comp differentiable_cptBase.continuous).continuousOn

/-- The part of the chart `1` of `ℂⁿ × ℙ¹` over `N` which retracts onto the second chart. -/
def B₂ : (AnalyticSpace.complexAffineSpace.{u} (1 + n)).Opens :=
  ⟨{p | cptBase p ∈ N ∧ C.L₂ p ∈ C.M₂}, by
    change IsOpen {p : Cn.{u} (1 + n) | cptBase p ∈ N ∧ C.ch₂ (C.L₂ p) ∈ N}
    have h₁ : IsOpen {p : Cn.{u} (1 + n) | cptBase p ∈ N} :=
      N.isOpen.preimage differentiable_cptBase.continuous
    have h₂ : IsOpen ({p : Cn.{u} (1 + n) | cptBase p ∈ N} ∩ C.L₂ ⁻¹' C.dom₂) :=
      C.continuous_L₂_on.isOpen_inter_preimage h₁ C.isOpen_dom₂
    have hc : ContinuousOn (fun p ↦ C.ch₂ (C.L₂ p))
        ({p : Cn.{u} (1 + n) | cptBase p ∈ N} ∩ C.L₂ ⁻¹' C.dom₂) :=
      C.differentiableOn_ch₂.continuousOn.comp (C.continuous_L₂_on.mono Set.inter_subset_left)
        fun _ hp ↦ hp.2
    have heq : {p : Cn.{u} (1 + n) | cptBase p ∈ N ∧ C.ch₂ (C.L₂ p) ∈ N} =
        ({p : Cn.{u} (1 + n) | cptBase p ∈ N} ∩ C.L₂ ⁻¹' C.dom₂) ∩
          (fun p ↦ C.ch₂ (C.L₂ p)) ⁻¹' {x | x ∈ N} :=
      Set.ext fun p ↦ ⟨fun hp ↦ ⟨⟨hp.1, C.mem_dom₂_of_ch₂_mem hp.2⟩, hp.2⟩,
        fun hp ↦ ⟨hp.1.1, hp.2⟩⟩
    rw [heq]
    exact hc.isOpen_inter_preimage h₂ N.isOpen⟩

lemma L₂_Γ₂ {a : Cn.{u} n} : C.L₂ (C.Γ₂ a) = a := by
  have hne := C.it_ne_iw
  funext j
  simp only [L₂, Γ₂, cptBase_cptFun, cptFib_cptFun, ofBase_baseCoord, ch₂_iw, φ_ch₂]
  by_cases hj : j = C.iw
  · subst hj
    simp
  by_cases hj' : j = C.it
  · subst hj'
    simp [Function.update_of_ne hj]
  · simp [ch₂, ta, Function.update_of_ne hj, Function.update_of_ne hj']

lemma ta'_L₂ (p : Cn.{u} (1 + n)) :
    C.ta' (C.L₂ p, C.h₂ p) = Function.update (cptBase p) C.iw (cptFib p) := by
  have hne := C.it_ne_iw
  have e : C.h₂ p + C.L₂ p C.it * C.L₂ p C.iw = cptBase p C.it := by
    rw [L₂_it, L₂_iw, h₂]
    ring
  simp only [ta']
  rw [e]
  funext j
  by_cases hj : j = C.iw
  · subst hj
    simp [Function.update_of_ne hne.symm, L₂]
  by_cases hj' : j = C.it
  · subst hj'
    simp [Function.update_of_ne hj]
  · simp [L₂, Function.update_of_ne hj, Function.update_of_ne hj']

lemma differentiable_ta' : Differentiable ℂ C.ta' := by
  have h : Differentiable ℂ fun q : Cn.{u} n × ℂ ↦ q.2 + q.1 C.it * q.1 C.iw := by fun_prop
  exact fun q ↦ (differentiableWithinAt_update (s := Set.univ)
    differentiable_fst.differentiableAt.differentiableWithinAt (h q).differentiableWithinAt
    C.it).differentiableAt Filter.univ_mem

/-- **The second chart as an embedding into the chart `1` of `ℂⁿ × ℙ¹`.** -/
def graph₂ : GraphEmbeddingData C.M₂ C.B₂ where
  Γ := C.Γ₂
  L := C.L₂
  h := C.h₂
  Θ := C.Θ₂
  domΘ := C.ta' ⁻¹' cyl N C.iw
  isOpen_domΘ := (isOpen_cyl N C.iw).preimage C.differentiable_ta'.continuous
  differentiableOn_Γ := by
    have h₁ : DifferentiableOn ℂ C.ch₂ {a : Cn.{u} n | a ∈ C.M₂} :=
      C.differentiableOn_ch₂.mono fun _ ha ↦ C.M₂_le_dom₂ ha
    have hb := differentiable_baseCoord.{u} (n := n)
    have hc := differentiable_cptFun.{u} (n := n)
    change DifferentiableOn ℂ (fun a ↦ cptFun (baseCoord (C.ch₂ a), a C.iw)) _
    fun_prop
  differentiableOn_L := by
    have hφ : DifferentiableOn ℂ (fun p ↦ C.φ (cptBase p)) {p : Cn.{u} (1 + n) | p ∈ C.B₂} :=
      C.differentiableOn_φ.comp differentiable_cptBase.differentiableOn fun p hp ↦
        mem_cyl_of_mem hp.1
    have hb := differentiable_cptBase.{u} (n := n)
    exact differentiableOn_update (differentiableOn_update hb.differentiableOn
      (by fun_prop) C.it) differentiable_cptFib.differentiableOn C.iw
  differentiableOn_h := by
    have hφ : DifferentiableOn ℂ (fun p ↦ C.φ (cptBase p)) {p : Cn.{u} (1 + n) | p ∈ C.B₂} :=
      C.differentiableOn_φ.comp differentiable_cptBase.differentiableOn fun p hp ↦
        mem_cyl_of_mem hp.1
    have hb := differentiable_cptBase.{u} (n := n)
    have hf := differentiable_cptFib.{u} (n := n)
    change DifferentiableOn ℂ
      (fun p ↦ cptBase p C.it - cptFib p * (cptBase p C.iw - C.φ (cptBase p))) _
    fun_prop
  differentiableOn_Θ := by
    set S : Set (Cn.{u} n × ℂ) := C.ta' ⁻¹' cyl N C.iw
    have ht := C.differentiable_ta'
    have hφ : DifferentiableOn ℂ (fun q ↦ C.φ (C.ta' q)) S :=
      C.differentiableOn_φ.comp ht.differentiableOn fun q hq ↦ hq
    have hs : DifferentiableOn ℂ (fun q : Cn.{u} n × ℂ ↦ C.φ (C.ta' q) + q.1 C.it) S := by
      fun_prop
    have hu : DifferentiableOn ℂ (fun q : Cn.{u} n × ℂ ↦
        Function.update (C.ta' q) C.iw (C.φ (C.ta' q) + q.1 C.it)) S :=
      differentiableOn_update ht.differentiableOn hs C.iw
    have hb := differentiable_baseCoord.{u} (n := n)
    have hc := differentiable_cptFun.{u} (n := n)
    change DifferentiableOn ℂ (fun q : Cn.{u} n × ℂ ↦ cptFun (baseCoord
      (Function.update (C.ta' q) C.iw (C.φ (C.ta' q) + q.1 C.it)), q.1 C.iw)) S
    fun_prop
  Γ_mem a ha := by
    refine ⟨?_, ?_⟩
    · simpa [Γ₂] using (show C.ch₂ a ∈ N from ha)
    · rw [L₂_Γ₂]
      exact ha
  L_mem _ hp := hp.2
  L_Γ _ _ := C.L₂_Γ₂
  h_Γ a _ := by
    simp only [h₂, Γ₂, cptBase_cptFun, cptFib_cptFun, ofBase_baseCoord, ch₂_iw, φ_ch₂, ch₂_it]
    ring
  mem_domΘ p hp := by
    change C.ta' (C.L₂ p, C.h₂ p) ∈ cyl N C.iw
    rw [ta'_L₂, update_mem_cyl]
    exact mem_cyl_of_mem hp.1
  Θ_zero a _ := by
    simp only [Θ₂, Γ₂, ch₂, ta', ta, zero_add]
  Θ_L p _ := by
    change cptFun (baseCoord (Function.update (C.ta' (C.L₂ p, C.h₂ p)) C.iw
      (C.φ (C.ta' (C.L₂ p, C.h₂ p)) + C.L₂ p C.it)), C.L₂ p C.iw) = p
    rw [ta'_L₂, C.φ_update, L₂_it, L₂_iw, add_sub_cancel, Function.update_idem,
      Function.update_eq_self]
    exact cptFun_cptBase_cptFib p

/-! ### The charts over `N°` -/

lemma it_ne_zero_of_mem_M₁₀ {x : Cn.{u} n} (hx : x ∈ C.M₁₀ h₀) : x C.it ≠ 0 := by
  have := C.ne_zero _ (show C.ch₁ x ∈ N₀ from hx)
  rwa [ch₁_it] at this

lemma ne_zero_of_mem_M₂₀ {a : Cn.{u} n} (ha : a ∈ C.M₂₀ h₀) : a C.it ≠ 0 ∧ a C.iw ≠ 0 := by
  have := C.ne_zero _ (show C.ch₂ a ∈ N₀ from ha)
  rw [ch₂_it] at this
  exact ⟨left_ne_zero_of_mul this, right_ne_zero_of_mul this⟩

/-- On the first chart over `N°`, the point `(x, [τ : ω])` of `ℂⁿ × ℙ¹` is `Γ₁`. -/
lemma blowupPt_ch₁ {x : Cn.{u} n} (hx : x C.it ≠ 0) :
    C.toBlowupData.blowupPt (C.ch₁ x) = chartPt 0 (baseCoord (C.ch₁ x), x C.iw) := by
  simp only [BlowupData.blowupPt, toBlowupData_ω, toBlowupData_τ, ch₁_iw, φ_ch₁, ch₁_it]
  congr 2
  field_simp
  ring

/-- On the second chart over `N°`, the point `(x, [τ : ω])` of `ℂⁿ × ℙ¹` is `Γ₂`. -/
lemma blowupPt_ch₂ {a : Cn.{u} n} (hs : a C.it ≠ 0) (hv : a C.iw ≠ 0) :
    C.toBlowupData.blowupPt (C.ch₂ a) = chartPt 1 (baseCoord (C.ch₂ a), a C.iw) := by
  simp only [BlowupData.blowupPt, toBlowupData_ω, toBlowupData_τ, ch₂_iw, φ_ch₂, ch₂_it]
  have e : (C.φ (C.ta a) + a C.it - C.φ (C.ta a)) / (a C.it * a C.iw) = (a C.iw)⁻¹ := by
    field_simp
    ring
  rw [e, chartPt_zero_eq_chartPt_one (by simpa using hv), inv_inv]

/-- The inverse `x ↦ (…, t, (w - φ) / t)` of the first chart off `t = 0`. -/
def ch₁Inv (x : Cn.{u} n) : Cn.{u} n :=
  Function.update x C.iw ((x C.iw - C.φ x) / x C.it)

lemma ch₁_ch₁Inv {x : Cn.{u} n} (hx : x C.it ≠ 0) : C.ch₁ (C.ch₁Inv x) = x := by
  have e : C.φ (C.ch₁Inv x) + C.ch₁Inv x C.it * C.ch₁Inv x C.iw = x C.iw := by
    simp only [ch₁Inv, C.φ_update, Function.update_of_ne C.it_ne_iw, Function.update_self]
    field_simp
    ring
  rw [ch₁, e, ch₁Inv, Function.update_idem, Function.update_eq_self]

lemma ch₁Inv_ch₁ {x : Cn.{u} n} (hx : x C.it ≠ 0) : C.ch₁Inv (C.ch₁ x) = x := by
  have e : (C.ch₁ x C.iw - C.φ (C.ch₁ x)) / C.ch₁ x C.it = x C.iw := by
    rw [ch₁_iw, φ_ch₁, ch₁_it]
    field_simp
    ring
  rw [ch₁Inv, e, ch₁, Function.update_idem, Function.update_eq_self]

lemma differentiableOn_ch₁Inv :
    DifferentiableOn ℂ C.ch₁Inv {x : Cn.{u} n | x ∈ cyl N C.iw ∧ x C.it ≠ 0} := by
  have hφ : DifferentiableOn ℂ C.φ {x : Cn.{u} n | x ∈ cyl N C.iw ∧ x C.it ≠ 0} :=
    C.differentiableOn_φ.mono fun _ hx ↦ hx.1
  refine differentiableOn_update differentiableOn_id ?_ C.iw
  simp only [div_eq_mul_inv]
  exact fun x hx ↦ (((differentiable_apply C.iw).differentiableAt.differentiableWithinAt).sub
    (hφ x hx)).mul ((differentiable_apply C.it).differentiableAt.differentiableWithinAt.inv hx.2)

/-- The inverse `x ↦ (…, w - φ, t / (w - φ))` of the second chart off `w = φ`. -/
def ch₂Inv (x : Cn.{u} n) : Cn.{u} n :=
  Function.update (Function.update x C.it (x C.iw - C.φ x)) C.iw (x C.it / (x C.iw - C.φ x))

lemma ch₂_ch₂Inv {x : Cn.{u} n} (hx : x C.iw - C.φ x ≠ 0) : C.ch₂ (C.ch₂Inv x) = x := by
  have hne := C.it_ne_iw
  have hta : C.ta (C.ch₂Inv x) = Function.update x C.iw (x C.it / (x C.iw - C.φ x)) := by
    have e : C.ch₂Inv x C.it * C.ch₂Inv x C.iw = x C.it := by
      simp only [ch₂Inv, Function.update_of_ne hne, Function.update_self]
      field_simp
    rw [ta, e]
    funext j
    by_cases hj : j = C.iw
    · subst hj
      simp [ch₂Inv, Function.update_of_ne hne.symm]
    by_cases hj' : j = C.it
    · subst hj'
      simp [Function.update_of_ne hj]
    · simp [ch₂Inv, Function.update_of_ne hj, Function.update_of_ne hj']
  have e : C.φ (C.ta (C.ch₂Inv x)) + C.ch₂Inv x C.it = x C.iw := by
    rw [hta, C.φ_update, ch₂Inv, Function.update_of_ne hne, Function.update_self]
    ring
  rw [ch₂, e, hta, Function.update_idem, Function.update_eq_self]

lemma ch₂Inv_ch₂ {a : Cn.{u} n} (hs : a C.it ≠ 0) : C.ch₂Inv (C.ch₂ a) = a := by
  have hne := C.it_ne_iw
  have e₁ : C.ch₂ a C.iw - C.φ (C.ch₂ a) = a C.it := by
    rw [ch₂_iw, φ_ch₂]
    ring
  have e₂ : C.ch₂ a C.it / a C.it = a C.iw := by
    rw [ch₂_it]
    field_simp
  rw [ch₂Inv, e₁, e₂]
  funext j
  by_cases hj : j = C.iw
  · subst hj
    simp
  by_cases hj' : j = C.it
  · subst hj'
    simp [Function.update_of_ne hj]
  · simp [ch₂, ta, Function.update_of_ne hj, Function.update_of_ne hj']

lemma differentiableOn_ch₂Inv :
    DifferentiableOn ℂ C.ch₂Inv {x : Cn.{u} n | x ∈ cyl N C.iw ∧ x C.iw - C.φ x ≠ 0} := by
  have hφ : DifferentiableOn ℂ C.φ {x : Cn.{u} n | x ∈ cyl N C.iw ∧ x C.iw - C.φ x ≠ 0} :=
    C.differentiableOn_φ.mono fun _ hx ↦ hx.1
  have hω : DifferentiableOn ℂ (fun x ↦ x C.iw - C.φ x)
      {x : Cn.{u} n | x ∈ cyl N C.iw ∧ x C.iw - C.φ x ≠ 0} :=
    (differentiable_apply C.iw).differentiableOn.sub hφ
  refine differentiableOn_update (differentiableOn_update differentiableOn_id hω C.it) ?_ C.iw
  simp only [div_eq_mul_inv]
  exact fun x hx ↦ (differentiable_apply C.it).differentiableAt.differentiableWithinAt.mul
    ((hω x hx).inv hx.2)

end BlowupCentre

end

end ComplexAnalytic.BoundedSections
