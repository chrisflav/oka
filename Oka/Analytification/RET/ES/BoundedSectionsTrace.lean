/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.ES.BoundedSections
import Oka.Analytic.RiemannExtension
import Oka.AlgebraicGeometry.Modules.CocycleTwistPullback

/-!
# Traces and characteristic polynomials of bounded sections

Keep the notation of `Oka/Analytification/RET/ES/BoundedSections.lean`: `p : W ⟶ N°` is a finite
étale cover with `W` Hausdorff, `N° ⊆ N ⊆ ℂⁿ`, and `𝒜` is the sheaf of sections of `p_* 𝒪_W`
bounded near `N ∖ N°`. Assume that `N ∖ N°` is thin, i.e. contained in the zero set of a
holomorphic function on `N` whose zero set has empty interior
(`ComplexAnalytic.BoundedSections.HasThinComplement`).

For a section `a` of `𝒜` over `V`, the trace `∑_{w ∈ p⁻¹(x)} a(w)` and the coefficients of the
characteristic polynomial `∏_{w ∈ p⁻¹(x)} (T - a(w))` are holomorphic on `V ∩ N°`, since `W` is
locally trivial over `N°`, and bounded near `V ∖ N°`; by Riemann extension they are sections of
`𝒪_N` over `V`. This gives the `𝒪_N`-linear trace `𝒜 ⟶ 𝒪_N`
(`ComplexAnalytic.BoundedSections.trace`), and shows that every section of `𝒜` over a
preconnected open is integral over `𝒪_N`
(`ComplexAnalytic.BoundedSections.isIntegralElem_of_mem_boundedSubring`); conversely integral
sections are bounded (`ComplexAnalytic.BoundedSections.mem_boundedSubring_of_isIntegralElem`).
The number of sheets is constant over preconnected opens of `N`
(`ComplexAnalytic.BoundedSections.card_fiberFinset_eq`).

## Main definitions

- `ComplexAnalytic.BoundedSections.traceFun`, `ComplexAnalytic.BoundedSections.charPolyFun`: the
  trace and characteristic polynomial of a function on `W`, fibrewise.
- `ComplexAnalytic.BoundedSections.trace hD s`: the trace of a section of `𝒜`, a section of `𝒪_N`;
  `ComplexAnalytic.BoundedSections.traceHom`: the trace as a morphism `𝒜 ⟶ 𝒪_N`.
- `ComplexAnalytic.BoundedSections.mulSec`: the product of two sections of `𝒜`.

## Main results

- `ComplexAnalytic.BoundedSections.trace_add`, `ComplexAnalytic.BoundedSections.trace_smul`,
  `ComplexAnalytic.BoundedSections.trace_map`: the trace is `𝒪_N`-linear and natural.
- `ComplexAnalytic.BoundedSections.exists_coeff_charPolyFun`: the coefficients of the
  characteristic polynomial are holomorphic on `V`.
- `ComplexAnalytic.BoundedSections.exists_holFun_eq`: Riemann extension across `N ∖ N°`.
-/

open CategoryTheory Opposite AlgebraicGeometry Topology TopologicalSpace Filter Polynomial

universe u

namespace ComplexAnalytic.BoundedSections

open AnalyticSpace

noncomputable section

variable {n : ℕ} {N N₀ : (AnalyticSpace.complexAffineSpace.{u} n).Opens}

variable (N N₀) in
/-- The complement of `N°` in `N` is **thin**: it lies in the zero set of a function holomorphic
on `N` whose zero set has empty interior. -/
def HasThinComplement : Prop :=
  ∃ g : Cn.{u} n → ℂ, DifferentiableOn ℂ g {x | x ∈ N} ∧
    interior ({x | x ∈ N} ∩ g ⁻¹' {0}) = ∅ ∧ ∀ x ∈ N, x ∉ N₀ → g x = 0

variable (h₀ : N₀ ≤ N) (W : FiniteEtaleOver (space N₀))

/-! ### Sections of `𝒜` -/

/-- A section of `𝒜 = boundedModule h₀ W` over `V`, as a section of `𝒪_W` over `p⁻¹(V ∩ N°)`. -/
def secVal {V : (space N).Opens} (s : (boundedModule h₀ W).val.obj (op V)) :
    W.left.presheaf.obj (op (preim h₀ W V)) :=
  s.1

lemma secVal_mem {V : (space N).Opens} (s : (boundedModule h₀ W).val.obj (op V)) :
    secVal h₀ W s ∈ boundedSubring h₀ W V :=
  s.2

/-- A bounded section of `𝒪_W` over `p⁻¹(V ∩ N°)`, as a section of `𝒜` over `V`. -/
def mkSec {V : (space N).Opens} (s : W.left.presheaf.obj (op (preim h₀ W V)))
    (hs : s ∈ boundedSubring h₀ W V) : (boundedModule h₀ W).val.obj (op V) :=
  ⟨s, hs⟩

@[simp]
lemma secVal_mkSec {V : (space N).Opens} (s : W.left.presheaf.obj (op (preim h₀ W V)))
    (hs : s ∈ boundedSubring h₀ W V) : secVal h₀ W (mkSec h₀ W s hs) = s :=
  rfl

lemma secVal_injective {V : (space N).Opens} :
    Function.Injective (secVal h₀ W (V := V)) :=
  fun _ _ h ↦ Subtype.ext h

@[simp]
lemma secVal_add {V : (space N).Opens} (s t : (boundedModule h₀ W).val.obj (op V)) :
    secVal h₀ W (s + t) = secVal h₀ W s + secVal h₀ W t :=
  rfl

@[simp]
lemma secVal_zero {V : (space N).Opens} :
    secVal h₀ W (0 : (boundedModule h₀ W).val.obj (op V)) = 0 :=
  rfl

@[simp]
lemma secVal_smul {V : (space N).Opens} (r : (space N).presheaf.obj (op V))
    (s : (boundedModule h₀ W).val.obj (op V)) :
    secVal h₀ W (r • s) = pullback h₀ W V r * secVal h₀ W s :=
  rfl

lemma secVal_map {V V' : (space N).Opens} (h : V' ≤ V) (s : (boundedModule h₀ W).val.obj (op V)) :
    secVal h₀ W (LocallyRingedSpace.sectRes (boundedModule h₀ W) h s) =
      W.left.presheaf.map (homOfLE (preim_mono h₀ W h)).op (secVal h₀ W s) :=
  rfl

/-! ### Fibres -/

open Classical in
/-- On the domain of local sheets, the fibre over `x` is enumerated by the sheets. -/
lemma fiberFinset_eq_image {B : Set (Cn.{u} n)} {I : Type u} [Fintype I]
    {σ : I → Cn.{u} n → W.left} (hσ : ∀ i, ∀ x ∈ B, pt W (σ i x) = x)
    (huniq : ∀ w, pt W w ∈ B → ∃! i, σ i (pt W w) = w) {x : Cn.{u} n} (hx : x ∈ B) :
    fiberFinset W x = Finset.univ.image (fun i ↦ σ i x) := by
  classical
  ext w
  rw [mem_fiberFinset, Finset.mem_image]
  constructor
  · rintro rfl
    obtain ⟨i, hi, -⟩ := huniq w hx
    exact ⟨i, Finset.mem_univ _, hi⟩
  · rintro ⟨i, -, rfl⟩
    exact hσ i x hx

lemma injective_sheets {B : Set (Cn.{u} n)} {I : Type u} {σ : I → Cn.{u} n → W.left}
    (hσ : ∀ i, ∀ x ∈ B, pt W (σ i x) = x)
    (huniq : ∀ w, pt W w ∈ B → ∃! i, σ i (pt W w) = w) {x : Cn.{u} n} (hx : x ∈ B) :
    Function.Injective (fun i ↦ σ i x) := by
  intro i j hij
  have hw : pt W (σ i x) ∈ B := by rw [hσ i x hx]; exact hx
  obtain ⟨k, -, hk⟩ := huniq (σ i x) hw
  have h₁ : σ i (pt W (σ i x)) = σ i x := by rw [hσ i x hx]
  have h₂ : σ j (pt W (σ i x)) = σ i x := by rw [hσ i x hx]; exact hij.symm
  exact (hk i h₁).trans (hk j h₂).symm

/-- The number of points in the fibre is locally constant on `N°`. -/
lemma eventually_card_fiberFinset_eq [T2Space W.left] {x₀ : Cn.{u} n} (hx₀ : x₀ ∈ N₀) :
    ∀ᶠ x in 𝓝 x₀, (fiberFinset W x).card = (fiberFinset W x₀).card := by
  classical
  obtain ⟨B, I, _, σ, hBo, hx₀B, -, hσ, -, huniq, -⟩ := exists_local_sheets W hx₀
  have hcard : ∀ x ∈ B, (fiberFinset W x).card = Fintype.card I := fun x hx ↦ by
    rw [fiberFinset_eq_image W hσ huniq hx,
      Finset.card_image_of_injective _ (injective_sheets W hσ huniq hx), Finset.card_univ]
  filter_upwards [hBo.mem_nhds hx₀B] with x hx
  rw [hcard x hx, hcard x₀ hx₀B]

/-- **The number of sheets is constant over a preconnected open subset of `N`.** -/
theorem card_fiberFinset_eq [T2Space W.left] (hD : HasThinComplement N N₀)
    {G : Set (Cn.{u} n)} (hGo : IsOpen G) (hGc : IsPreconnected G) (hGN : ∀ x ∈ G, x ∈ N)
    {x y : Cn.{u} n} (hx : x ∈ G) (hxN : x ∈ N₀) (hy : y ∈ G) (hyN : y ∈ N₀) :
    (fiberFinset W x).card = (fiberFinset W y).card := by
  obtain ⟨g, hg, hZ, hg0⟩ := hD
  have hgG : DifferentiableOn ℂ g G := hg.mono fun z hz ↦ hGN z hz
  have hZG : interior (G ∩ g ⁻¹' {0}) = ∅ :=
    Set.subset_empty_iff.1 (hZ ▸ interior_mono (Set.inter_subset_inter_left _ hGN))
  have hS : IsPreconnected (G \ g ⁻¹' {0}) := hGc.diff_zero hGo hgG hZG
  have hSN : ∀ z ∈ G \ g ⁻¹' {0}, z ∈ N₀ := fun z hz ↦ by
    by_contra h
    exact hz.2 (hg0 z (hGN z hz.1) h)
  have hcont : ContinuousOn (fun z ↦ (fiberFinset W z).card) (G \ g ⁻¹' {0}) :=
    fun z hz ↦ (continuousAt_const.congr (by
      filter_upwards [eventually_card_fiberFinset_eq W (hSN z hz)] with z' hz'
      exact hz'.symm)).continuousWithinAt
  have key : ∀ z ∈ G, z ∈ N₀ → ∃ z' ∈ G \ g ⁻¹' {0},
      (fiberFinset W z).card = (fiberFinset W z').card := fun z hz hzN ↦ by
    have hcl := subset_closure_diff_zero hGo hZG hz
    rw [mem_closure_iff_frequently] at hcl
    obtain ⟨z', hz'S, hz'⟩ := (hcl.and_eventually (eventually_card_fiberFinset_eq W hzN)).exists
    exact ⟨z', hz'S, hz'.symm⟩
  obtain ⟨x', hx'S, hx'⟩ := key x hx hxN
  obtain ⟨y', hy'S, hy'⟩ := key y hy hyN
  rw [hx', hy']
  exact hS.constant hcont hx'S hy'S

/-! ### Coefficients of `∏ (X - C rᵢ)` -/

/-- The coefficients of `∏ᵢ (X - C (gᵢ y))` are holomorphic in `y` where the `gᵢ` are. -/
lemma differentiableAt_coeff_prod_X_sub_C {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ι : Type*} (s : Finset ι) (g : ι → E → ℂ) {x : E}
    (hg : ∀ i ∈ s, DifferentiableAt ℂ (g i) x) (k : ℕ) :
    DifferentiableAt ℂ (fun y ↦ (∏ i ∈ s, (X - C (g i y))).coeff k) x := by
  classical
  induction s using Finset.induction_on generalizing k with
  | empty =>
    simp only [Finset.prod_empty, coeff_one]
    exact differentiableAt_const _
  | insert j s hj ih =>
    have ih' := fun k ↦ ih (fun i hi ↦ hg i (Finset.mem_insert_of_mem hi)) k
    have hgj := hg j (Finset.mem_insert_self j s)
    simp only [Finset.prod_insert hj, sub_mul, coeff_sub, coeff_C_mul]
    cases k with
    | zero =>
      simp only [coeff_X_mul_zero, zero_sub]
      exact (hgj.mul (ih' 0)).neg
    | succ k =>
      simp only [coeff_X_mul]
      exact (ih' k).sub (hgj.mul (ih' (k + 1)))

/-- The coefficients of `∏ᵢ (X - C rᵢ)` are bounded by `(1 + M) ^ card` if all `‖rᵢ‖ ≤ M`. -/
lemma norm_coeff_prod_X_sub_C_le {ι : Type*} (s : Finset ι) (r : ι → ℂ) {M : ℝ} (hM : 0 ≤ M)
    (hr : ∀ i ∈ s, ‖r i‖ ≤ M) (k : ℕ) :
    ‖(∏ i ∈ s, (X - C (r i))).coeff k‖ ≤ (1 + M) ^ s.card := by
  classical
  induction s using Finset.induction_on generalizing k with
  | empty =>
    simp only [Finset.prod_empty, coeff_one, Finset.card_empty, pow_zero]
    split_ifs <;> simp
  | insert j s hj ih =>
    have ih' := fun k ↦ ih (fun i hi ↦ hr i (Finset.mem_insert_of_mem hi)) k
    have hrj := hr j (Finset.mem_insert_self j s)
    have hB : 0 ≤ (1 + M) ^ s.card := pow_nonneg (by linarith) _
    rw [Finset.prod_insert hj, Finset.card_insert_of_notMem hj, pow_succ, sub_mul, coeff_sub,
      coeff_C_mul]
    have h₂ : ‖r j * (∏ i ∈ s, (X - C (r i))).coeff k‖ ≤ M * (1 + M) ^ s.card := by
      rw [norm_mul]
      exact mul_le_mul hrj (ih' k) (norm_nonneg _) hM
    cases k with
    | zero =>
      rw [coeff_X_mul_zero, zero_sub, norm_neg]
      nlinarith
    | succ k =>
      rw [coeff_X_mul]
      calc _ ≤ ‖(∏ i ∈ s, (X - C (r i))).coeff k‖ + ‖r j * (∏ i ∈ s, (X - C (r i))).coeff
            (k + 1)‖ := norm_sub_le _ _
        _ ≤ (1 + M) ^ s.card + M * (1 + M) ^ s.card := add_le_add (ih' k) h₂
        _ = (1 + M) ^ s.card * (1 + M) := by ring

/-! ### Traces and characteristic polynomials of functions on `W` -/

/-- The trace of a function on `W` at `x ∈ ℂⁿ`: the sum of its values over the fibre. -/
def traceFun (f : W.left → ℂ) (x : Cn.{u} n) : ℂ :=
  ∑ w ∈ fiberFinset W x, f w

/-- The characteristic polynomial of a function `f` on `W` at `x ∈ ℂⁿ`:
`∏_{w ∈ p⁻¹(x)} (T - f w)`. -/
def charPolyFun (f : W.left → ℂ) (x : Cn.{u} n) : ℂ[X] :=
  ∏ w ∈ fiberFinset W x, (X - C (f w))

lemma traceFun_congr {f f' : W.left → ℂ} {x : Cn.{u} n} (h : ∀ w, pt W w = x → f w = f' w) :
    traceFun W f x = traceFun W f' x :=
  Finset.sum_congr rfl fun w hw ↦ h w ((mem_fiberFinset W).1 hw)

lemma traceFun_add (f f' : W.left → ℂ) (x : Cn.{u} n) :
    traceFun W (f + f') x = traceFun W f x + traceFun W f' x :=
  Finset.sum_add_distrib

lemma traceFun_mul_comp (c : Cn.{u} n → ℂ) (f : W.left → ℂ) (x : Cn.{u} n) :
    traceFun W (fun w ↦ c (pt W w) * f w) x = c x * traceFun W f x := by
  rw [traceFun, traceFun, Finset.mul_sum]
  exact Finset.sum_congr rfl fun w hw ↦ by rw [(mem_fiberFinset W).1 hw]

lemma charPolyFun_congr {f f' : W.left → ℂ} {x : Cn.{u} n} (h : ∀ w, pt W w = x → f w = f' w) :
    charPolyFun W f x = charPolyFun W f' x :=
  Finset.prod_congr rfl fun w hw ↦ by rw [h w ((mem_fiberFinset W).1 hw)]

lemma monic_charPolyFun (f : W.left → ℂ) (x : Cn.{u} n) : (charPolyFun W f x).Monic :=
  monic_prod_of_monic _ _ fun _ _ ↦ monic_X_sub_C _

lemma natDegree_charPolyFun (f : W.left → ℂ) (x : Cn.{u} n) :
    (charPolyFun W f x).natDegree = (fiberFinset W x).card := by
  rw [charPolyFun, natDegree_prod_of_monic _ _ fun w _ ↦ monic_X_sub_C _]
  simp

lemma eval_charPolyFun (f : W.left → ℂ) {w : W.left} {x : Cn.{u} n} (hw : pt W w = x) :
    (charPolyFun W f x).eval (f w) = 0 := by
  rw [charPolyFun, eval_prod]
  exact Finset.prod_eq_zero ((mem_fiberFinset W).2 hw) (by simp)


/-- The characteristic polynomial at a point with `d` sheets, written out. -/
lemma eval_charPolyFun_eq (f : W.left → ℂ) {x : Cn.{u} n} {d : ℕ}
    (hd : (fiberFinset W x).card = d) (z : ℂ) :
    (charPolyFun W f x).eval z =
      z ^ d + ∑ k ∈ Finset.range d, (charPolyFun W f x).coeff k * z ^ k := by
  have hlead : (charPolyFun W f x).coeff d = 1 := by
    rw [← hd, ← natDegree_charPolyFun]
    exact (monic_charPolyFun W _ _).coeff_natDegree
  rw [eval_eq_sum_range, natDegree_charPolyFun, hd, Finset.sum_range_succ, hlead, one_mul,
    add_comm]
lemma norm_traceFun_le (f : W.left → ℂ) (x : Cn.{u} n) {C : ℝ}
    (hC : ∀ w, pt W w = x → ‖f w‖ ≤ C) : ‖traceFun W f x‖ ≤ (fiberFinset W x).card * C := by
  refine (norm_sum_le _ _).trans ?_
  rw [← nsmul_eq_mul]
  exact Finset.sum_le_card_nsmul _ _ _ fun w hw ↦ hC w ((mem_fiberFinset W).1 hw)

lemma norm_coeff_charPolyFun_le (f : W.left → ℂ) (x : Cn.{u} n) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ w, pt W w = x → ‖f w‖ ≤ C) (k : ℕ) :
    ‖(charPolyFun W f x).coeff k‖ ≤ (1 + C) ^ (fiberFinset W x).card :=
  norm_coeff_prod_X_sub_C_le _ _ hC0 (fun w hw ↦ hC w ((mem_fiberFinset W).1 hw)) k

/-! ### Holomorphy of traces and characteristic polynomials -/

/-- `evalFun` of a restricted section. -/
lemma evalFun_map {O O' : W.left.Opens} (h : O' ≤ O) (a : W.left.presheaf.obj (op O)) {w : W.left}
    (hw : w ∈ O') : evalFun (W.left.presheaf.map (homOfLE h).op a) w = evalFun a w := by
  rw [evalFun_of_mem _ hw, evalFun_of_mem _ (h hw), eval_presheaf_map]

/-- Near a point `x₁ ∈ N°`, the trace and the characteristic polynomial of the values of a section
defined over `p⁻¹(G)` are sums and products of holomorphic functions. -/
lemma exists_local_formula [T2Space W.left] {O : W.left.Opens} (a : W.left.presheaf.obj (op O))
    {G : Set (Cn.{u} n)} (hGO : ∀ w, pt W w ∈ G → w ∈ O) {x₁ : Cn.{u} n}
    (hx₁G : x₁ ∈ G) (hx₁N : x₁ ∈ N₀) :
    ∃ (I : Type u) (_ : Fintype I) (g : I → Cn.{u} n → ℂ), (∀ i, DifferentiableAt ℂ (g i) x₁) ∧
      ∀ᶠ x in 𝓝 x₁, traceFun W (evalFun a) x = ∑ i, g i x ∧
        charPolyFun W (evalFun a) x = ∏ i, (X - C (g i x)) := by
  classical
  obtain ⟨B, I, _, σ, hBo, hx₁B, -, hσ, hσc, huniq, -⟩ := exists_local_sheets W hx₁N
  refine ⟨I, inferInstance, fun i x ↦ evalFun a (σ i x), fun i ↦ ?_, ?_⟩
  · exact differentiableAt_evalFun_comp W hBo (hσ i) (hσc i) a hx₁B
      (hGO _ (by rw [hσ i x₁ hx₁B]; exact hx₁G))
  · filter_upwards [hBo.mem_nhds hx₁B] with x hx
    rw [traceFun, charPolyFun, fiberFinset_eq_image W hσ huniq hx,
      Finset.sum_image fun i _ j _ h ↦ injective_sheets W hσ huniq hx h,
      Finset.prod_image fun i _ j _ h ↦ injective_sheets W hσ huniq hx h]
    exact ⟨rfl, rfl⟩

/-- **The trace of a section is holomorphic.** -/
theorem differentiableOn_traceFun [T2Space W.left] {O : W.left.Opens}
    (a : W.left.presheaf.obj (op O)) {G : Set (Cn.{u} n)}
    (hGO : ∀ w, pt W w ∈ G → w ∈ O) :
    DifferentiableOn ℂ (traceFun W (evalFun a)) (G ∩ {x | x ∈ N₀}) := by
  rintro x₁ ⟨hx₁G, hx₁N⟩
  obtain ⟨I, _, g, hg, hev⟩ := exists_local_formula W a hGO hx₁G hx₁N
  refine (DifferentiableAt.congr_of_eventuallyEq ?_
    (hev.mono fun x hx ↦ hx.1)).differentiableWithinAt
  exact DifferentiableAt.fun_sum fun i _ ↦ hg i

/-- **The coefficients of the characteristic polynomial of a section are holomorphic.** -/
theorem differentiableOn_coeff_charPolyFun [T2Space W.left] {O : W.left.Opens}
    (a : W.left.presheaf.obj (op O)) {G : Set (Cn.{u} n)}
    (hGO : ∀ w, pt W w ∈ G → w ∈ O) (k : ℕ) :
    DifferentiableOn ℂ (fun x ↦ (charPolyFun W (evalFun a) x).coeff k) (G ∩ {x | x ∈ N₀}) := by
  rintro x₁ ⟨hx₁G, hx₁N⟩
  obtain ⟨I, _, g, hg, hev⟩ := exists_local_formula W a hGO hx₁G hx₁N
  refine (DifferentiableAt.congr_of_eventuallyEq ?_
    (hev.mono fun x hx ↦ by rw [hx.2])).differentiableWithinAt
  exact differentiableAt_coeff_prod_X_sub_C _ g (fun i _ ↦ hg i) k

/-! ### Bounds near `N ∖ N°` -/

lemma isOpen_setOf_mem (U : (AnalyticSpace.complexAffineSpace.{u} n).Opens) :
    IsOpen {x : Cn.{u} n | x ∈ U} :=
  U.isOpen

/-- Near a point of `N`, the number of sheets is bounded. -/
lemma exists_card_le [T2Space W.left] (hD : HasThinComplement N N₀) {x : Cn.{u} n} (hx : x ∈ N) :
    ∃ M ∈ 𝓝 x, ∃ d : ℕ, ∀ y ∈ M, y ∈ N₀ → (fiberFinset W y).card ≤ d := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (isOpen_setOf_mem N) x hx
  refine ⟨Metric.ball x ε, Metric.ball_mem_nhds x hε, ?_⟩
  by_cases h : ∃ y₁ ∈ Metric.ball x ε, y₁ ∈ N₀
  · obtain ⟨y₁, hy₁, hy₁N⟩ := h
    exact ⟨_, fun y hy hyN ↦ (card_fiberFinset_eq W hD Metric.isOpen_ball
      (convex_ball x ε).isPreconnected (fun z hz ↦ hball hz) hy hyN hy₁ hy₁N).le⟩
  · exact ⟨0, fun y hy hyN ↦ (h ⟨y, hy, hyN⟩).elim⟩

variable {h₀ W} in
/-- A bounded section is bounded on the fibres near a point of `V ∖ N°`. -/
lemma exists_bound_of_mem_boundedSubring {V : (space N).Opens}
    {a : W.left.presheaf.obj (op (preim h₀ W V))} (ha : a ∈ boundedSubring h₀ W V)
    {x : Cn.{u} n} (hx : x ∈ img V) (hxN : x ∉ N₀) :
    ∃ M ∈ 𝓝 x, ∃ C, 0 ≤ C ∧ ∀ w, pt W w ∈ M → pt W w ∈ img V → ‖evalFun a w‖ ≤ C := by
  obtain ⟨hxN', hxV⟩ := mem_img_iff.1 hx
  obtain ⟨M₀, hM₀, C, hC⟩ := ha ⟨x, hxN'⟩ hxV hxN
  refine ⟨Subtype.val '' M₀, N.isOpenEmbedding.isOpenMap.image_mem_nhds hM₀, max C 0,
    le_max_right _ _, fun w hwM hwV ↦ ?_⟩
  have hw : w ∈ preim h₀ W V := (mem_preim_iff h₀ W).2 hwV
  obtain ⟨y, hyM, hy⟩ := hwM
  have hpw : (proj h₀ W).toLRSHom.base w = y :=
    Subtype.ext ((coe_proj_base h₀ W w).trans hy.symm)
  rw [evalFun_of_mem a hw]
  exact (hC w hw (hpw ▸ hyM)).trans (le_max_left _ _)

variable {h₀ W} in
/-- **The trace of a bounded section is bounded near `N ∖ N°`.** -/
lemma exists_bound_traceFun [T2Space W.left] (hD : HasThinComplement N N₀) {V : (space N).Opens}
    {a : W.left.presheaf.obj (op (preim h₀ W V))} (ha : a ∈ boundedSubring h₀ W V)
    {x : Cn.{u} n} (hx : x ∈ img V) (hxN : x ∉ N₀) :
    ∃ M ∈ 𝓝 x, ∃ C, ∀ y ∈ M, y ∈ N₀ → ‖traceFun W (evalFun a) y‖ ≤ C := by
  obtain ⟨M, hM, C, -, hC⟩ := exists_bound_of_mem_boundedSubring ha hx hxN
  obtain ⟨M', hM', d, hd⟩ := exists_card_le W hD (img_le V x hx)
  refine ⟨M ∩ M' ∩ img V, inter_mem (inter_mem hM hM') ((img V).isOpen.mem_nhds hx),
    d * max C 0, fun y hy hyN ↦ ?_⟩
  refine (norm_traceFun_le W _ y fun w hw ↦ ?_).trans
    (mul_le_mul (by exact_mod_cast hd y hy.1.2 hyN)
    le_rfl (le_max_right _ _) (Nat.cast_nonneg _))
  exact (hC w (hw ▸ hy.1.1) (hw ▸ hy.2)).trans (le_max_left _ _)

variable {h₀ W} in
/-- **The coefficients of the characteristic polynomial of a bounded section are bounded near
`N ∖ N°`.** -/
lemma exists_bound_coeff_charPolyFun [T2Space W.left] (hD : HasThinComplement N N₀)
    {V : (space N).Opens} {a : W.left.presheaf.obj (op (preim h₀ W V))}
    (ha : a ∈ boundedSubring h₀ W V) {x : Cn.{u} n} (hx : x ∈ img V) (hxN : x ∉ N₀) (k : ℕ) :
    ∃ M ∈ 𝓝 x, ∃ C, ∀ y ∈ M, y ∈ N₀ → ‖(charPolyFun W (evalFun a) y).coeff k‖ ≤ C := by
  obtain ⟨M, hM, C, hC0, hC⟩ := exists_bound_of_mem_boundedSubring ha hx hxN
  obtain ⟨M', hM', d, hd⟩ := exists_card_le W hD (img_le V x hx)
  refine ⟨M ∩ M' ∩ img V, inter_mem (inter_mem hM hM') ((img V).isOpen.mem_nhds hx),
    (1 + C) ^ d, fun y hy hyN ↦ ?_⟩
  refine (norm_coeff_charPolyFun_le W _ y hC0 (fun w hw ↦ ?_) k).trans
    (pow_le_pow_right₀ (by linarith) (hd y hy.1.2 hyN))
  exact hC w (hw ▸ hy.1.1) (hw ▸ hy.2)

/-! ### Riemann extension across `N ∖ N°` -/

section Riemann

variable (hD : HasThinComplement N N₀)
include hD

/-- The part of `img V` inside `N°` is dense in `img V`: two continuous functions agreeing on it
agree on `img V`. -/
lemma eqOn_img_of_eqOn {V : (space N).Opens} {F₁ F₂ : Cn.{u} n → ℂ}
    (h₁ : ContinuousOn F₁ (img V)) (h₂ : ContinuousOn F₂ (img V))
    (h : ∀ x ∈ img V, x ∈ N₀ → F₁ x = F₂ x) : Set.EqOn F₁ F₂ (img V) := by
  obtain ⟨g, -, hZ, hg0⟩ := hD
  have hZV : interior ((img V : Set (Cn.{u} n)) ∩ g ⁻¹' {0}) = ∅ :=
    Set.subset_empty_iff.1 (hZ ▸ interior_mono (Set.inter_subset_inter_left _ (img_le V)))
  refine Set.EqOn.of_eqOn_diff_zero (img V).isOpen hZV h₁ h₂ fun x hx ↦ h x hx.1 ?_
  by_contra hxN
  exact hx.2 (hg0 x (img_le V x hx.1) hxN)

/-- Sections of `𝒪_N` are determined by their values on `N°`. -/
theorem holFun_ext {V : (space N).Opens} {r r' : (space N).presheaf.obj (op V)}
    (h : ∀ x ∈ img V, x ∈ N₀ → holFun r x = holFun r' x) : r = r' := by
  have := eqOn_img_of_eqOn hD (differentiableOn_holFun r).continuousOn
    (differentiableOn_holFun r').continuousOn h
  refine OkaRing.ext (funext fun x ↦ ?_)
  exact (OkaRing.toGlobalFun_apply (U := img V) r x.2).symm.trans
    ((this x.2).trans (OkaRing.toGlobalFun_apply (U := img V) r' x.2))

/-- **Riemann extension across `N ∖ N°`**: a function holomorphic on `V ∩ N°` which is bounded
near every point of `V ∖ N°` is the restriction of a section of `𝒪_N` over `V`. -/
theorem exists_holFun_eq {V : (space N).Opens} {f : Cn.{u} n → ℂ}
    (hf : DifferentiableOn ℂ f (img V ∩ {x | x ∈ N₀}))
    (hb : ∀ x ∈ img V, x ∉ N₀ → ∃ M ∈ 𝓝 x, ∃ C, ∀ y ∈ M, y ∈ N₀ → ‖f y‖ ≤ C) :
    ∃ r : (space N).presheaf.obj (op V), ∀ x ∈ img V, x ∈ N₀ → holFun r x = f x := by
  obtain ⟨g, hg, hZ, hg0⟩ := hD
  set U : Set (Cn.{u} n) := (img V : Set (Cn.{u} n))
  have hgU : DifferentiableOn ℂ g U := hg.mono (img_le V)
  have hZU : interior (U ∩ g ⁻¹' {0}) = ∅ :=
    Set.subset_empty_iff.1 (hZ ▸ interior_mono (Set.inter_subset_inter_left _ (img_le V)))
  have hN : ∀ y ∈ U \ g ⁻¹' {0}, y ∈ N₀ := fun y hy ↦ by
    by_contra h
    exact hy.2 (hg0 y (img_le V y hy.1) h)
  have hUN : IsOpen (U ∩ {x | x ∈ N₀}) := (img V).isOpen.inter (isOpen_setOf_mem N₀)
  obtain ⟨F, hFd, hFf⟩ := exists_differentiableOn_eqOn_of_isBoundedUnder (img V).isOpen hgU hZU
    (hf.mono fun y hy ↦ ⟨hy.1, hN y hy⟩) fun z hz ↦ by
      by_cases hzN : z ∈ N₀
      · have hc : ContinuousAt f z := (hf.differentiableAt (hUN.mem_nhds ⟨hz, hzN⟩)).continuousAt
        exact Filter.IsBoundedUnder.mono nhdsWithin_le_nhds hc.norm.tendsto.isBoundedUnder_le
      · obtain ⟨M, hM, C, hC⟩ := hb z hz hzN
        refine ⟨C, eventually_map.2 ?_⟩
        filter_upwards [nhdsWithin_le_nhds hM, self_mem_nhdsWithin] with y hyM hyS
        exact hC y hyM (hN y hyS)
  have hFN : ∀ x ∈ U, x ∈ N₀ → F x = f x := by
    have hZ' : interior ((U ∩ {x | x ∈ N₀}) ∩ g ⁻¹' {0}) = ∅ :=
      Set.subset_empty_iff.1 (hZU ▸ interior_mono (Set.inter_subset_inter_left _
        Set.inter_subset_left))
    have := Set.EqOn.of_eqOn_diff_zero hUN hZ' (hFd.continuousOn.mono Set.inter_subset_left)
      hf.continuousOn fun y hy ↦ hFf ⟨hy.1.1, hy.2⟩
    exact fun x hx hxN ↦ this ⟨hx, hxN⟩
  refine ⟨OkaRing.ofDifferentiableOn F hFd, fun x hx hxN ↦ ?_⟩
  rw [holFun, OkaRing.toGlobalFun_apply _ hx]
  exact hFN x hx hxN

end Riemann

/-! ### Values of sections -/

lemma holFun_eq_eval {V : (space N).Opens} (r : (space N).presheaf.obj (op V)) {x : Cn.{u} n}
    (hx : x ∈ img V) :
    holFun r x = (space N).eval ⟨x, img_le V x hx⟩ (mem_img_iff.1 hx).2 r :=
  (eval_space r ⟨x, img_le V x hx⟩ (mem_img_iff.1 hx).2).symm

lemma holFun_add {V : (space N).Opens} (r r' : (space N).presheaf.obj (op V)) {x : Cn.{u} n}
    (hx : x ∈ img V) : holFun (r + r') x = holFun r x + holFun r' x := by
  simp only [holFun_eq_eval _ hx, map_add]

lemma holFun_mul {V : (space N).Opens} (r r' : (space N).presheaf.obj (op V)) {x : Cn.{u} n}
    (hx : x ∈ img V) : holFun (r * r') x = holFun r x * holFun r' x := by
  simp only [holFun_eq_eval _ hx, map_mul]

lemma holFun_zero {V : (space N).Opens} {x : Cn.{u} n} (hx : x ∈ img V) :
    holFun (0 : (space N).presheaf.obj (op V)) x = 0 := by
  simp only [holFun_eq_eval _ hx, map_zero]

lemma holFun_map {V V' : (space N).Opens} (h : V' ≤ V) (r : (space N).presheaf.obj (op V))
    {x : Cn.{u} n} (hx : x ∈ img V') :
    holFun ((space N).presheaf.map (homOfLE h).op r) x = holFun r x := by
  rw [holFun_eq_eval _ hx, eval_presheaf_map, holFun_eq_eval _ (img_mono h hx)]

lemma evalFun_add {O : W.left.Opens} (a b : W.left.presheaf.obj (op O)) {w : W.left} (hw : w ∈ O) :
    evalFun (a + b) w = evalFun a w + evalFun b w := by
  simp only [evalFun_of_mem _ hw, map_add]

lemma evalFun_mul {O : W.left.Opens} (a b : W.left.presheaf.obj (op O)) {w : W.left} (hw : w ∈ O) :
    evalFun (a * b) w = evalFun a w * evalFun b w := by
  simp only [evalFun_of_mem _ hw, map_mul]

lemma evalFun_pullback {V : (space N).Opens} (r : (space N).presheaf.obj (op V)) {w : W.left}
    (hw : w ∈ preim h₀ W V) : evalFun (pullback h₀ W V r) w = holFun r (pt W w) := by
  rw [evalFun_of_mem _ hw]
  exact eval_pullback h₀ W r w hw

/-- The product of two sections of `𝒜`. -/
def mulSec {V : (space N).Opens} (s t : (boundedModule h₀ W).val.obj (op V)) :
    (boundedModule h₀ W).val.obj (op V) :=
  mkSec h₀ W (secVal h₀ W s * secVal h₀ W t) (mul_mem (secVal_mem h₀ W s) (secVal_mem h₀ W t))

@[simp]
lemma secVal_mulSec {V : (space N).Opens} (s t : (boundedModule h₀ W).val.obj (op V)) :
    secVal h₀ W (mulSec h₀ W s t) = secVal h₀ W s * secVal h₀ W t :=
  rfl

lemma mulSec_add {V : (space N).Opens} (s s' t : (boundedModule h₀ W).val.obj (op V)) :
    mulSec h₀ W (s + s') t = mulSec h₀ W s t + mulSec h₀ W s' t :=
  secVal_injective h₀ W (by
    change (secVal h₀ W s + secVal h₀ W s') * secVal h₀ W t =
      secVal h₀ W s * secVal h₀ W t + secVal h₀ W s' * secVal h₀ W t
    exact add_mul _ _ _)

lemma mulSec_smul {V : (space N).Opens} (r : (space N).presheaf.obj (op V))
    (s t : (boundedModule h₀ W).val.obj (op V)) :
    mulSec h₀ W (r • s) t = r • mulSec h₀ W s t :=
  secVal_injective h₀ W (mul_assoc _ _ _)

lemma mulSec_zero_left {V : (space N).Opens} (t : (boundedModule h₀ W).val.obj (op V)) :
    mulSec h₀ W 0 t = 0 :=
  secVal_injective h₀ W (zero_mul _)

lemma mulSec_map {V V' : (space N).Opens} (h : V' ≤ V) (s t : (boundedModule h₀ W).val.obj (op V)) :
    LocallyRingedSpace.sectRes (boundedModule h₀ W) h (mulSec h₀ W s t) =
      mulSec h₀ W (LocallyRingedSpace.sectRes (boundedModule h₀ W) h s)
        (LocallyRingedSpace.sectRes (boundedModule h₀ W) h t) :=
  secVal_injective h₀ W (by
    change W.left.presheaf.map _ (secVal h₀ W s * secVal h₀ W t) =
      W.left.presheaf.map _ (secVal h₀ W s) * W.left.presheaf.map _ (secVal h₀ W t)
    exact map_mul _ _ _)

/-! ### The trace `𝒜 → 𝒪_N` -/

section Trace

variable [T2Space W.left] (hD : HasThinComplement N N₀)
include hD

variable {h₀ W} in
/-- The trace of a bounded section extends holomorphically across `N ∖ N°`. -/
theorem exists_trace {V : (space N).Opens} {a : W.left.presheaf.obj (op (preim h₀ W V))}
    (ha : a ∈ boundedSubring h₀ W V) :
    ∃ r : (space N).presheaf.obj (op V),
      ∀ x ∈ img V, x ∈ N₀ → holFun r x = traceFun W (evalFun a) x :=
  exists_holFun_eq hD (differentiableOn_traceFun W a fun _ hw ↦ (mem_preim_iff h₀ W).2 hw)
    fun _ hx hxN ↦ exists_bound_traceFun hD ha hx hxN

/-- **The trace** `tr : 𝒜 ⟶ 𝒪_N`: the sum of the values over the fibres, extended across
`N ∖ N°`. -/
def trace {V : (space N).Opens} (s : (boundedModule h₀ W).val.obj (op V)) :
    (space N).presheaf.obj (op V) :=
  (exists_trace hD (secVal_mem h₀ W s)).choose

lemma holFun_trace {V : (space N).Opens} (s : (boundedModule h₀ W).val.obj (op V))
    {x : Cn.{u} n} (hx : x ∈ img V) (hxN : x ∈ N₀) :
    holFun (trace h₀ W hD s) x = traceFun W (evalFun (secVal h₀ W s)) x :=
  (exists_trace hD (secVal_mem h₀ W s)).choose_spec x hx hxN

lemma trace_add {V : (space N).Opens} (s t : (boundedModule h₀ W).val.obj (op V)) :
    trace h₀ W hD (s + t) = trace h₀ W hD s + trace h₀ W hD t := by
  refine holFun_ext hD fun x hx hxN ↦ ?_
  rw [holFun_add _ _ hx, holFun_trace _ _ _ _ hx hxN, holFun_trace _ _ _ _ hx hxN,
    holFun_trace _ _ _ _ hx hxN, ← traceFun_add]
  refine traceFun_congr W fun w hw ↦ ?_
  exact evalFun_add W _ _ ((mem_preim_iff h₀ W).2 (hw ▸ hx))

lemma trace_smul {V : (space N).Opens} (r : (space N).presheaf.obj (op V))
    (s : (boundedModule h₀ W).val.obj (op V)) :
    trace h₀ W hD (r • s) = r * trace h₀ W hD s := by
  refine holFun_ext hD fun x hx hxN ↦ ?_
  rw [holFun_mul _ _ hx, holFun_trace _ _ _ _ hx hxN, holFun_trace _ _ _ _ hx hxN,
    ← traceFun_mul_comp]
  refine traceFun_congr W fun w hw ↦ ?_
  have hw' : w ∈ preim h₀ W V := (mem_preim_iff h₀ W).2 (hw ▸ hx)
  rw [secVal_smul, evalFun_mul W _ _ hw', evalFun_pullback h₀ W r hw']

lemma trace_zero {V : (space N).Opens} :
    trace h₀ W hD (0 : (boundedModule h₀ W).val.obj (op V)) = 0 := by
  have := trace_smul h₀ W hD 0 (0 : (boundedModule h₀ W).val.obj (op V))
  rwa [zero_smul, zero_mul] at this

lemma trace_map {V V' : (space N).Opens} (h : V' ≤ V) (s : (boundedModule h₀ W).val.obj (op V)) :
    trace h₀ W hD (LocallyRingedSpace.sectRes (boundedModule h₀ W) h s) =
      (space N).presheaf.map (homOfLE h).op (trace h₀ W hD s) := by
  refine holFun_ext hD fun x hx hxN ↦ ?_
  rw [holFun_map h _ hx, holFun_trace _ _ _ _ hx hxN, holFun_trace _ _ _ _ (img_mono h hx) hxN]
  refine traceFun_congr W fun w hw ↦ ?_
  rw [secVal_map]
  exact evalFun_map W _ _ ((mem_preim_iff h₀ W).2 (hw ▸ hx))


/-- **The trace** as a morphism `𝒜 ⟶ 𝒪_N` of sheaves of `𝒪_N`-modules. -/
def traceHom : boundedModule h₀ W ⟶ SheafOfModules.unit (space N).ringSheaf :=
  LocallyRingedSpace.modHomMk
    (fun _ ↦ AddMonoidHom.mk' (trace h₀ W hD) (trace_add h₀ W hD))
    (fun _ r s ↦ trace_smul h₀ W hD r s) fun _ _ h s ↦ trace_map h₀ W hD h s

lemma traceHom_app {V : (space N).Opens} (s : (boundedModule h₀ W).val.obj (op V)) :
    (traceHom h₀ W hD).val.app (op V) s = trace h₀ W hD s :=
  rfl

end Trace

/-! ### Integrality -/

section Integral

variable [T2Space W.left] (hD : HasThinComplement N N₀)
include hD

variable {h₀ W} in
/-- The coefficients of the characteristic polynomial of a bounded section extend holomorphically
across `N ∖ N°`. -/
theorem exists_coeff_charPolyFun {V : (space N).Opens}
    {a : W.left.presheaf.obj (op (preim h₀ W V))} (ha : a ∈ boundedSubring h₀ W V) (k : ℕ) :
    ∃ r : (space N).presheaf.obj (op V),
      ∀ x ∈ img V, x ∈ N₀ → holFun r x = (charPolyFun W (evalFun a) x).coeff k :=
  exists_holFun_eq hD
    (differentiableOn_coeff_charPolyFun W a (fun _ hw ↦ (mem_preim_iff h₀ W).2 hw) k)
    fun _ hx hxN ↦ exists_bound_coeff_charPolyFun hD ha hx hxN k

variable {h₀ W} in
/-- **Bounded sections are integral**: over a preconnected `V`, a section of `𝒜` is a root of
its characteristic polynomial, a monic polynomial with coefficients in `𝒪_N(V)`. -/
theorem isIntegralElem_of_mem_boundedSubring {V : (space N).Opens}
    (hV : IsPreconnected (img V : Set (Cn.{u} n)))
    {a : W.left.presheaf.obj (op (preim h₀ W V))} (ha : a ∈ boundedSubring h₀ W V) :
    (pullback h₀ W V).IsIntegralElem a := by
  classical
  have hW := isLocallyOpenInAffine_left W
  by_cases hne : ∃ x₁ ∈ img V, x₁ ∈ N₀
  · obtain ⟨x₁, hx₁V, hx₁N⟩ := hne
    set d := (fiberFinset W x₁).card
    have hd : ∀ x ∈ img V, x ∈ N₀ → (fiberFinset W x).card = d := fun x hx hxN ↦
      card_fiberFinset_eq W hD (img V).isOpen hV (img_le V) hx hxN hx₁V hx₁N
    choose c hc using exists_coeff_charPolyFun hD ha
    refine ⟨X ^ d + ∑ k : Fin d, C (c k) * X ^ (k : ℕ), monic_X_pow_add (degree_sum_fin_lt _),
      ?_⟩
    refine eq_of_forall_eval_eq hW fun w hw ↦ ?_
    have hwV : pt W w ∈ img V := (mem_preim_iff h₀ W).1 hw
    have hdw := hd _ hwV (pt_mem W w)
    have hlead : (charPolyFun W (evalFun a) (pt W w)).coeff d = 1 := by
      rw [← hdw, ← natDegree_charPolyFun]
      exact (monic_charPolyFun W _ _).coeff_natDegree
    have hP := eval_charPolyFun W (evalFun a) (rfl : pt W w = pt W w)
    rw [eval_eq_sum_range, natDegree_charPolyFun, hdw, Finset.sum_range_succ, hlead, one_mul,
      add_comm, Finset.sum_range] at hP
    rw [map_zero, hom_eval₂]
    simp only [eval₂_add, eval₂_X_pow, eval₂_finsetSum, eval₂_mul, eval₂_C,
      RingHom.coe_comp, Function.comp_apply]
    rw [← hP, ← evalFun_of_mem a hw]
    congr 1
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [eval_pullback h₀ W (c k) w hw, hc k _ hwV (pt_mem W w)]
  · push Not at hne
    have ha0 : a = 0 := eq_of_forall_eval_eq hW fun w hw ↦
      absurd (pt_mem W w) (hne _ ((mem_preim_iff h₀ W).1 hw))
    exact ⟨X, monic_X, by rw [eval₂_X, ha0]⟩

end Integral

variable {h₀ W} in
/-- **Integral sections are bounded**: a section of `𝒪_W` over `p⁻¹(V ∩ N°)` which is integral
over `𝒪_N(V)` lies in `𝒜(V)`. -/
theorem mem_boundedSubring_of_isIntegralElem {V : (space N).Opens}
    {a : W.left.presheaf.obj (op (preim h₀ W V))} (ha : (pullback h₀ W V).IsIntegralElem a) :
    a ∈ boundedSubring h₀ W V := by
  classical
  obtain ⟨P, hP, hPa⟩ := ha
  intro y hy _
  set d := P.natDegree
  have hx : y.1 ∈ img V := mem_img_iff.2 ⟨y.2, hy⟩
  have hev : ∀ᶠ z in 𝓝 y.1, ∀ i ∈ Finset.range d,
      ‖holFun (P.coeff i) z‖ ≤ ‖holFun (P.coeff i) y.1‖ + 1 := by
    refine (Filter.eventually_all_finset _).2 fun i _ ↦ ?_
    have hc := ((differentiableOn_holFun (P.coeff i)).continuousOn.continuousAt
      ((img V).isOpen.mem_nhds hx)).norm
    filter_upwards [hc.eventually (gt_mem_nhds (lt_add_one _))] with z hz using hz.le
  set A := ∑ i ∈ Finset.range d, (‖holFun (P.coeff i) y.1‖ + 1)
  refine ⟨Subtype.val ⁻¹' {z | ∀ i ∈ Finset.range d,
      ‖holFun (P.coeff i) z‖ ≤ ‖holFun (P.coeff i) y.1‖ + 1},
    continuous_subtype_val.continuousAt.preimage_mem_nhds hev, max 1 (d * A),
    fun w hw hwM ↦ ?_⟩
  have hwM' : ∀ i ∈ Finset.range d,
      ‖holFun (P.coeff i) (pt W w)‖ ≤ ‖holFun (P.coeff i) y.1‖ + 1 := by
    rw [← coe_proj_base h₀ W w]
    exact hwM
  refine Kummer.norm_le_of_pow_add_sum_eq_zero (a := fun i ↦ holFun (P.coeff i) (pt W w))
    (fun i hi ↦ (hwM' i (Finset.mem_range.2 hi)).trans (Finset.single_le_sum
      (f := fun i ↦ ‖holFun (P.coeff i) y.1‖ + 1) (fun _ _ ↦ by positivity)
      (Finset.mem_range.2 hi))) ?_
  have h₁ := congrArg (W.left.eval w hw) hPa
  rw [map_zero, hom_eval₂, hP.as_sum] at h₁
  simp only [eval₂_add, eval₂_X_pow, eval₂_finsetSum, eval₂_mul, eval₂_C, RingHom.coe_comp,
    Function.comp_apply, eval_pullback] at h₁
  exact h₁

end

end ComplexAnalytic.BoundedSections
