/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.ES.KummerExtensionAlgebra

/-!
# The canonical extension is `∏ᵢ 𝒪_S[u]/(u^{kᵢ} - t)`

Keep the notation of `Oka/Analytification/RET/ES/KummerExtensionSheaf.lean`, and let `e`
decompose `W` into Kummer covers of degrees `kᵢ`. For an open `V ⊆ S`, a family of polynomials
`Pᵢ ∈ 𝒪_S(V)[u]` gives the section of `𝒪_W` which is `Pᵢ(t)` with coefficients evaluated at
`(b, tᵏⁱ)` on the `i`-th Kummer cover; it is bounded near `t = 0`. This is a surjective ring
homomorphism `∏ᵢ 𝒪_S(V)[u] → 𝒞̄(V)` (`ComplexAnalytic.KummerModel.evExt`) with kernel generated
by the `u^{kᵢ} - t` (`ComplexAnalytic.KummerModel.ker_evExt`). Hence `𝒞̄(V)` is a free
`𝒪_S(V)`-module with basis the monomials `uʲ`, `j < kᵢ`, on the Kummer covers
(`ComplexAnalytic.KummerModel.coeffEquiv`), and in particular every bounded section is integral
over `𝒪_S(V)`.

## Main definitions

- `ComplexAnalytic.KummerModel.polyFun k P`: the function `x ↦ P(t)` with coefficients evaluated
  at `(b, tᵏ)`.
- `ComplexAnalytic.KummerModel.evExt e V`: the ring homomorphism `∏ᵢ 𝒪_S(V)[u] → 𝒞̄(V)`.
- `ComplexAnalytic.KummerModel.coeffEquiv e V`: the `𝒪_S(V)`-linear isomorphism
  `∏ᵢ 𝒪_S(V)^{kᵢ} ≃ 𝒞̄(V)`.

## Main results

- `ComplexAnalytic.KummerModel.ker_evExt`, `ComplexAnalytic.KummerModel.surjective_evExt`.
- `ComplexAnalytic.KummerModel.extensionPresheaf_map_coeffEquiv`: the isomorphisms `coeffEquiv` are
  compatible with restriction.
- `ComplexAnalytic.KummerModel.isLocallyOpenInAffine_of_convex`: the hypothesis of
  `ComplexAnalytic.KummerModel.extensionSheaf` holds for `B` convex.
- `ComplexAnalytic.KummerModel.extensionRingEquiv`: `𝒞̄(V) ≃+* (∏ᵢ 𝒪_S(V)[u]) / (u^{kᵢ} - t)ᵢ`.
- `ComplexAnalytic.KummerModel.free_boundedSubring`,
  `ComplexAnalytic.KummerModel.finite_boundedSubring`,
  `ComplexAnalytic.KummerModel.isIntegral_boundedSubring`.
-/

open CategoryTheory Opposite AlgebraicGeometry Topology TopologicalSpace Filter Polynomial

universe u

namespace ComplexAnalytic.KummerModel

open AnalyticSpace

noncomputable section

variable {m : ℕ} {B : Set (ULift.{u} (Fin m) → ℂ)} {hB : IsOpen B}
  {W : FiniteEtaleOver (punctured hB)} {ι : Type u} {k : ι → ℕ+} [Finite ι]
  (e : W ≅ FiniteEtaleOver.sigma fun i ↦ cover hB (k i))

/-- The Kummer map `(t, b) ↦ (tᵏ, b)` of `ℂ^{m+1}`. -/
abbrev kummerPt (k : ℕ) (x : ULift.{u} (Fin (m + 1)) → ℂ) : ULift.{u} (Fin (m + 1)) → ℂ :=
  Function.update x zero (x zero ^ k)

lemma differentiable_kummerPt (k : ℕ) : Differentiable ℂ (kummerPt.{u} (m := m) k) := by
  refine differentiable_pi.2 fun j ↦ ?_
  by_cases hj : j = zero
  · subst hj
    simp only [kummerPt, Function.update_self]
    fun_prop
  · simp only [kummerPt, Function.update_of_ne hj]
    fun_prop

/-- **Sections of `𝒪_W` with prescribed holomorphic values on the Kummer pieces.** -/
theorem exists_section_eval_eq_fun {V : Set (ULift.{u} (Fin (m + 1)) → ℂ)} (hV : IsOpen V)
    (F : ι → (ULift.{u} (Fin (m + 1)) → ℂ) → ℂ)
    (hF : ∀ i, DifferentiableOn ℂ (F i) {x | kummerPt (k i) x ∈ V}) :
    ∃ s : W.left.presheaf.obj (op ((Opens.map W.hom.toLRSHom.base).obj
        (puncturedPreimage hB hV))),
      ∀ i (y : punctured hB)
        (hy : W.hom.toLRSHom.base ((piece e i).toLRSHom.base y) ∈ puncturedPreimage hB hV),
        W.left.eval _ hy s = F i y.1 := by
  choose I Y hIY using exists_piece e
  have hrep (i : ι) (y : punctured hB) :
      I ((piece e i).toLRSHom.base y) = i ∧ Y ((piece e i).toLRSHom.base y) = y := by
    have h := (piece_base_eq_iff e _ _ _ _).1 (hIY ((piece e i).toLRSHom.base y))
    exact ⟨(Sigma.mk.inj h).1, eq_of_heq (Sigma.mk.inj h).2⟩
  let f : W.left → ℂ := fun w ↦ F (I w) (Y w).1
  have hf (i : ι) (y : punctured hB) : f ((piece e i).toLRSHom.base y) = F i y.1 := by
    have key : ∀ i' (_ : i' = i) (y' : punctured hB) (_ : y' = y), F i' y'.1 = F i y.1 := by
      rintro _ rfl _ rfl
      rfl
    exact key _ (hrep i y).1 _ (hrep i y).2
  set O := (Opens.map W.hom.toLRSHom.base).obj (puncturedPreimage hB hV)
  obtain ⟨s, hs⟩ := exists_eval_eq_of_local (isLocallyOpenInAffine_left e) (O := O) f
    fun w hw ↦ by
      obtain ⟨i, y₀, rfl⟩ := exists_piece e w
      set Ui : (punctured hB).Opens := (Opens.map (piece e i).toLRSHom.base).obj O
      set T : Opens (ULift.{u} (Fin (m + 1)) → ℂ) :=
        (puncturedOpens B hB).isOpenEmbedding.isOpenMap.functor.obj Ui
      have hT : ∀ x ∈ T, kummerPt (k i) x ∈ V := by
        rintro _ ⟨y, hy, rfl⟩
        change _ ∈ V at hy
        rwa [coe_hom_base_piece e i y] at hy
      let t : (punctured hB).presheaf.obj (op Ui) :=
        OkaRing.mk (U := T) (fun x ↦ F i x.1) (okaAnalytic_restrict fun x hx ↦
          analyticAt_of_differentiableOn_of_finiteDimensional T.isOpen
            ((hF i).mono hT) hx)
      have ht (y : punctured hB) (hy : y ∈ Ui) : (punctured hB).eval y hy t = F i y.1 := by
        rw [eval_restrict_complexAffineSpace_of]
        rfl
      obtain ⟨σ, hσ⟩ := exists_eval_eq_image (piece e i) (injective_piece_base e i) t
      refine ⟨_, Set.mem_image_of_mem (piece e i).toLRSHom.base (show y₀ ∈ Ui from hw), ?_,
        σ, ?_⟩
      · rintro _ ⟨y, hy, rfl⟩
        exact hy
      · rintro _ ⟨y, hy, rfl⟩
        rw [hσ y hy, ht, hf]
  exact ⟨s, fun i y hy ↦ (hs _ hy).trans (hf i y)⟩

variable {V : (disc hB).Opens}

/-- The function `x ↦ P(t)` on `ℂ^{m+1}`, with the coefficients of `P` evaluated at `(b, tᵏ)`. -/
def polyFun (k : ℕ) (P : ((disc hB).presheaf.obj (op V))[X]) (x : ULift.{u} (Fin (m + 1)) → ℂ) :
    ℂ :=
  ∑ n ∈ Finset.range (P.natDegree + 1), holFun (P.coeff n) (kummerPt k x) * x zero ^ n

lemma differentiableOn_polyFun (k : ℕ) (P : ((disc hB).presheaf.obj (op V))[X]) :
    DifferentiableOn ℂ (polyFun k P) {x | kummerPt k x ∈ coeOpens V} :=
  DifferentiableOn.fun_sum fun n _ ↦ ((differentiableOn_holFun _).comp
    (differentiable_kummerPt k).differentiableOn fun _ hx ↦ hx).mul
      ((differentiable_apply zero).differentiableOn.pow n)

/-- Evaluation of a section of `𝒪_S` over `V` at a point of `V`. -/
def evalAt {x : ULift.{u} (Fin (m + 1)) → ℂ} (hx : x ∈ tOpens V) :
    (disc hB).presheaf.obj (op V) →+* ℂ :=
  OkaRing.evalHom hx

lemma polyFun_eq_eval₂ (k : ℕ) (P : ((disc hB).presheaf.obj (op V))[X])
    {x : ULift.{u} (Fin (m + 1)) → ℂ} (hx : kummerPt k x ∈ tOpens V) :
    polyFun k P x = P.eval₂ (evalAt hx) (x zero) := by
  rw [eval₂_eq_sum_range]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  rw [holFun, OkaRing.toGlobalFun_apply (U := tOpens V) _ hx]
  rfl

variable (V) in
/-- The coordinate `t`, as a section of `𝒪_S` over `V`. -/
def tSec : (disc hB).presheaf.obj (op V) :=
  OkaRing.restrict (U := tOpens V) le_top (coord zero)

lemma evalAt_tSec {x : ULift.{u} (Fin (m + 1)) → ℂ} (hx : x ∈ tOpens V) :
    evalAt hx (tSec V) = x zero :=
  evalHom_coord zero

variable {e}

lemma kummerPt_mem {i : ι} {y : punctured hB}
    (hy : W.hom.toLRSHom.base ((piece e i).toLRSHom.base y) ∈
      puncturedPreimage hB (isOpen_coeOpens V)) :
    kummerPt (k i) y.1 ∈ tOpens V := by
  have h : ((W.hom.toLRSHom.base ((piece e i).toLRSHom.base y) : punctured hB).1 :
    ULift.{u} (Fin (m + 1)) → ℂ) ∈ coeOpens V := hy
  rw [coe_hom_base_piece] at h
  exact h

variable (e V) in
lemma exists_secPoly (P : ι → ((disc hB).presheaf.obj (op V))[X]) :
    ∃ s : W.left.presheaf.obj (op (preim W V)),
      ∀ i (y : punctured hB)
        (hy : W.hom.toLRSHom.base ((piece e i).toLRSHom.base y) ∈
          puncturedPreimage hB (isOpen_coeOpens V)),
        W.left.eval _ hy s = polyFun (k i) (P i) y.1 :=
  exists_section_eval_eq_fun e (isOpen_coeOpens V) (fun i ↦ polyFun (k i) (P i))
    fun _ ↦ differentiableOn_polyFun _ _

variable (e V) in
/-- The section of `𝒪_W` which is `Pᵢ(t)` on the `i`-th Kummer cover. -/
def secPoly (P : ι → ((disc hB).presheaf.obj (op V))[X]) :
    W.left.presheaf.obj (op (preim W V)) :=
  (exists_secPoly e V P).choose

lemma eval_secPoly (P : ι → ((disc hB).presheaf.obj (op V))[X]) (i : ι) (y : punctured hB)
    (hy : W.hom.toLRSHom.base ((piece e i).toLRSHom.base y) ∈
      puncturedPreimage hB (isOpen_coeOpens V)) :
    W.left.eval _ hy (secPoly e V P) =
      (P i).eval₂ (evalAt (kummerPt_mem hy)) (y.1 zero) :=
  ((exists_secPoly e V P).choose_spec i y hy).trans (polyFun_eq_eval₂ _ _ _)

lemma secPoly_mem (P : ι → ((disc hB).presheaf.obj (op V))[X]) :
    secPoly e V P ∈ boundedSubring W V := by
  classical
  intro x hx _
  haveI := Fintype.ofFinite ι
  have hev : ∀ᶠ z in 𝓝 x, ∀ i, ∀ n ∈ Finset.range ((P i).natDegree + 1),
      ‖holFun ((P i).coeff n) z‖ ≤ ‖holFun ((P i).coeff n) x‖ + 1 := by
    refine Filter.eventually_all.2 fun i ↦ (Filter.eventually_all_finset _).2 fun n _ ↦ ?_
    have hc := ((differentiableOn_holFun ((P i).coeff n)).continuousOn.continuousAt
      ((isOpen_coeOpens V).mem_nhds hx)).norm
    filter_upwards [hc.eventually (gt_mem_nhds (lt_add_one _))] with z hz using hz.le
  refine ⟨_, hev, ∑ i, ∑ n ∈ Finset.range ((P i).natDegree + 1),
    (‖holFun ((P i).coeff n) x‖ + 1), fun w hw hwN ↦ ?_⟩
  obtain ⟨i, y, rfl⟩ := exists_piece e w
  refine (congrArg norm ((exists_secPoly e V P).choose_spec i y hw)).trans_le ?_
  rw [coe_hom_base_piece] at hwN
  have hy1 : ‖(y.1 : ULift.{u} (Fin (m + 1)) → ℂ) zero‖ < 1 := y.2.2.2
  calc ‖polyFun (k i) (P i) y.1‖
      ≤ ∑ n ∈ Finset.range ((P i).natDegree + 1),
          ‖holFun ((P i).coeff n) (kummerPt (k i) y.1) * y.1 zero ^ n‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.range ((P i).natDegree + 1), (‖holFun ((P i).coeff n) x‖ + 1) := by
        refine Finset.sum_le_sum fun n hn ↦ ?_
        rw [norm_mul, norm_pow]
        calc _ ≤ ‖holFun ((P i).coeff n) (kummerPt (k i) y.1)‖ * 1 :=
              mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) hy1.le) (norm_nonneg _)
          _ ≤ _ := by rw [mul_one]; exact hwN i n hn
    _ ≤ _ := Finset.single_le_sum (f := fun i ↦ ∑ n ∈ Finset.range ((P i).natDegree + 1),
          (‖holFun ((P i).coeff n) x‖ + 1))
          (fun i _ ↦ Finset.sum_nonneg fun n _ ↦ by positivity) (Finset.mem_univ i)

variable (e) in
/-- Two bounded sections with the same values on the Kummer pieces are equal. -/
lemma boundedSubring_ext {a b : boundedSubring W V}
    (h : ∀ i (y : punctured hB)
      (hy : W.hom.toLRSHom.base ((piece e i).toLRSHom.base y) ∈
        puncturedPreimage hB (isOpen_coeOpens V)),
      W.left.eval _ hy a.1 = W.left.eval _ hy b.1) : a = b := by
  refine Subtype.ext (eq_of_forall_eval_eq_piece e fun w hw ↦ ?_)
  obtain ⟨i, y, rfl⟩ := exists_piece e w
  exact h i y hw

variable (e V) in
/-- The ring homomorphism `∏ᵢ 𝒪_S(V)[u] → 𝒞̄(V)`, `(Pᵢ) ↦` the section which is `Pᵢ(t)`, with
coefficients evaluated at `(b, tᵏⁱ)`, on the `i`-th Kummer cover. -/
def evExt : (ι → ((disc hB).presheaf.obj (op V))[X]) →+* boundedSubring W V where
  toFun P := ⟨secPoly e V P, secPoly_mem P⟩
  map_one' := boundedSubring_ext e fun i y hy ↦ by
    rw [eval_secPoly, Pi.one_apply, eval₂_one, OneMemClass.coe_one, map_one]
  map_mul' P Q := boundedSubring_ext e fun i y hy ↦ by
    change _ = W.left.eval _ hy (secPoly e V P * secPoly e V Q)
    rw [map_mul, eval_secPoly, eval_secPoly, eval_secPoly]
    rw [Pi.mul_apply, eval₂_mul]
  map_zero' := boundedSubring_ext e fun i y hy ↦ by
    rw [eval_secPoly, Pi.zero_apply, eval₂_zero, ZeroMemClass.coe_zero, map_zero]
  map_add' P Q := boundedSubring_ext e fun i y hy ↦ by
    change _ = W.left.eval _ hy (secPoly e V P + secPoly e V Q)
    rw [map_add, eval_secPoly, eval_secPoly, eval_secPoly]
    rw [Pi.add_apply, eval₂_add]

lemma eval_evExt (P : ι → ((disc hB).presheaf.obj (op V))[X]) (i : ι) (y : punctured hB)
    (hy : W.hom.toLRSHom.base ((piece e i).toLRSHom.base y) ∈
      puncturedPreimage hB (isOpen_coeOpens V)) :
    W.left.eval _ hy (evExt e V P).1 =
      (P i).eval₂ (evalAt (kummerPt_mem hy)) (y.1 zero) :=
  eval_secPoly P i y hy

lemma evalAt_holFun {x : ULift.{u} (Fin (m + 1)) → ℂ} (hx : x ∈ tOpens V)
    (g : (disc hB).presheaf.obj (op V)) : holFun g x = evalAt hx g :=
  OkaRing.toGlobalFun_apply (U := tOpens V) g hx

lemma evalAt_tSec_kummerPt {i : ι} {y : punctured hB}
    (hy : W.hom.toLRSHom.base ((piece e i).toLRSHom.base y) ∈
      puncturedPreimage hB (isOpen_coeOpens V)) :
    evalAt (kummerPt_mem hy) (tSec V) = y.1 zero ^ (k i : ℕ) := by
  rw [evalAt_tSec]
  exact Function.update_self _ _ _

variable (e) in
/-- **Uniqueness of the coefficients**: a family `gⱼ ∈ 𝒪_S(V)`, `j < kᵢ`, with
`∑ gⱼ(b, tᵏⁱ) tʲ = 0` on the `i`-th Kummer cover vanishes. -/
theorem eq_zero_of_forall_sum_eq_zero {i : ι} (g : Fin (k i) → (disc hB).presheaf.obj (op V))
    (h : ∀ (y : punctured hB)
      (hy : W.hom.toLRSHom.base ((piece e i).toLRSHom.base y) ∈
        puncturedPreimage hB (isOpen_coeOpens V)),
      ∑ j, evalAt (kummerPt_mem hy) (g j) * y.1 zero ^ (j : ℕ) = 0) : g = 0 := by
  have hc (j : Fin (k i)) : ContinuousOn (fun z ↦ holFun (g j) ((splitEquiv m).symm z))
      ((splitEquiv m).symm ⁻¹' coeOpens V) :=
    (differentiableOn_holFun (g j)).continuousOn.comp (splitEquiv m).symm.continuous.continuousOn
      fun _ hz ↦ hz
  funext j
  have hEq := eqOn_of_forall_eval_eq e (isOpen_coeOpens V)
    (fun x hx ↦ mem_disc_of_mem_coeOpens V hx) i
    (g := fun j z ↦ holFun (g j) ((splitEquiv m).symm z)) (g' := fun _ _ ↦ 0) hc
    (fun _ ↦ continuousOn_const) (fun y hy ↦ by
      simp only [mul_zero, Finset.sum_const_zero]
      rw [← h y hy]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [splitEquiv_symm_powMap, evalAt_holFun (kummerPt_mem hy), mul_comm]) j
  refine OkaRing.ext (funext fun ⟨x, hx⟩ ↦ ?_)
  have := hEq (show (splitEquiv m).symm (splitEquiv m x) ∈ coeOpens V by
    rw [Homeomorph.symm_apply_apply]; exact hx)
  simp only [Homeomorph.symm_apply_apply] at this
  rw [holFun, OkaRing.toGlobalFun_apply (U := tOpens V) _ hx] at this
  exact this

/-- **The kernel of `evExt`**: `(Pᵢ)` gives the zero section if and only if every `Pᵢ` is a
multiple of `u^{kᵢ} - t`. -/
theorem evExt_eq_zero_iff (P : ι → ((disc hB).presheaf.obj (op V))[X]) :
    evExt e V P = 0 ↔ ∀ i, (X ^ (k i : ℕ) - C (tSec V)) ∣ P i := by
  constructor
  · intro h i
    set q : ((disc hB).presheaf.obj (op V))[X] := X ^ (k i : ℕ) - C (tSec V)
    have hq : q.Monic := monic_X_pow_sub_C _ (k i).ne_zero
    by_cases hq1 : q = 1
    · rw [hq1]
      exact one_dvd _
    set R := P i %ₘ q
    have hRdeg : R.natDegree < k i := by
      refine (natDegree_modByMonic_lt (P i) hq hq1).trans_le ?_
      exact natDegree_sub_le_of_le
        (natDegree_X_pow_le (R := (disc hB).presheaf.obj (op V)) (k i : ℕ))
        ((natDegree_C (tSec V)).le.trans (Nat.zero_le (k i : ℕ))) |>.trans_eq (max_self _)
    refine (modByMonic_eq_zero_iff_dvd hq).1 (Polynomial.ext fun n ↦ ?_)
    by_cases hn : n < k i
    · have hR := eq_zero_of_forall_sum_eq_zero e (i := i) (fun j ↦ R.coeff j) fun y hy ↦ by
        have h₁ := congrArg (fun s : boundedSubring W V ↦ W.left.eval _ hy s.1) h
        simp only [ZeroMemClass.coe_zero, map_zero] at h₁
        rw [eval_evExt, ← modByMonic_add_div (P i) q, eval₂_add, eval₂_mul] at h₁
        have hq0 : q.eval₂ (evalAt (kummerPt_mem hy)) (y.1 zero) = 0 := by
          rw [eval₂_sub, eval₂_X_pow, eval₂_C, evalAt_tSec_kummerPt hy, sub_self]
        rw [hq0, zero_mul, add_zero, eval₂_eq_sum_range' _ hRdeg] at h₁
        rw [Fin.sum_univ_eq_sum_range (fun n ↦ evalAt (kummerPt_mem hy) (R.coeff n) *
          y.1 zero ^ n)]
        exact h₁
      exact congrFun hR ⟨n, hn⟩
    · rw [coeff_zero, coeff_eq_zero_of_natDegree_lt (hRdeg.trans_le (not_lt.1 hn))]
  · intro h
    refine boundedSubring_ext e fun i y hy ↦ ?_
    obtain ⟨Q, hQ⟩ := h i
    rw [eval_evExt, hQ, eval₂_mul, eval₂_sub, eval₂_X_pow, eval₂_C, evalAt_tSec_kummerPt hy,
      sub_self, zero_mul, ZeroMemClass.coe_zero, map_zero]

variable (e V) in
theorem ker_evExt :
    RingHom.ker (evExt e V) = Ideal.pi fun i ↦ Ideal.span {X ^ (k i : ℕ) - C (tSec V)} := by
  ext P
  rw [RingHom.mem_ker, evExt_eq_zero_iff, Ideal.mem_pi]
  simp only [Ideal.mem_span_singleton]

/-- The family of polynomials `∑_{j < kᵢ} gᵢⱼ uʲ`. -/
def coeffPoly (g : ∀ i, Fin (k i) → (disc hB).presheaf.obj (op V)) :
    ι → ((disc hB).presheaf.obj (op V))[X] :=
  fun i ↦ ∑ j, C (g i j) * X ^ (j : ℕ)

omit [Finite ι] in
lemma eval₂_coeffPoly (g : ∀ i, Fin (k i) → (disc hB).presheaf.obj (op V)) (i : ι)
    (f : (disc hB).presheaf.obj (op V) →+* ℂ) (z : ℂ) :
    (coeffPoly g i).eval₂ f z = ∑ j, f (g i j) * z ^ (j : ℕ) := by
  simp [coeffPoly, eval₂_finsetSum]

lemma differentiable_splitEquiv :
    Differentiable ℂ (fun x : ULift.{u} (Fin (m + 1)) → ℂ ↦ splitEquiv m x) :=
  Differentiable.prodMk (differentiable_pi.2 fun _ ↦ differentiable_apply _)
    (differentiable_apply _)

variable (e) in
/-- **Every bounded section is `∑ gᵢⱼ uʲ` on the Kummer covers.** -/
theorem exists_coeffPoly_eq (s : boundedSubring W V) :
    ∃ g : ∀ i, Fin (k i) → (disc hB).presheaf.obj (op V), evExt e V (coeffPoly g) = s := by
  choose g hg heval using (isBoundedNearZero_iff e (isOpen_coeOpens V)
    (fun x hx ↦ mem_disc_of_mem_coeOpens V hx) s.1).1 s.2
  let G : ∀ i, Fin (k i) → (disc hB).presheaf.obj (op V) := fun i j ↦
    OkaRing.mk (U := tOpens V) (fun x ↦ g i j (splitEquiv m x.1)) (okaAnalytic_restrict
      fun x hx ↦ analyticAt_of_differentiableOn_of_finiteDimensional (tOpens V).isOpen
        ((hg i j).comp differentiable_splitEquiv.differentiableOn fun y hy ↦ by
          change (splitEquiv m).symm (splitEquiv m y) ∈ coeOpens V
          rw [Homeomorph.symm_apply_apply]
          exact hy) hx)
  refine ⟨G, boundedSubring_ext e fun i y hy ↦ ?_⟩
  rw [eval_evExt, eval₂_coeffPoly, heval i y hy]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [mul_comm]
  change _ * g i j (splitEquiv m (kummerPt (k i) y.1)) = _
  rw [splitEquiv_update]
  rfl

variable (e V) in
theorem surjective_evExt : Function.Surjective (evExt e V) := fun s ↦
  ⟨_, (exists_coeffPoly_eq e s).choose_spec⟩

variable (e V) in
/-- **The canonical extension is `∏ᵢ 𝒪_S(V)[u]/(u^{kᵢ} - t)`.** -/
def extensionRingEquiv :
    ((ι → ((disc hB).presheaf.obj (op V))[X]) ⧸
      Ideal.pi fun i ↦ Ideal.span {X ^ (k i : ℕ) - C (tSec V)}) ≃+* boundedSubring W V :=
  (Ideal.quotEquivOfEq (ker_evExt e V).symm).trans
    (RingHom.quotientKerEquivOfSurjective (surjective_evExt e V))

lemma evExt_C (a : (disc hB).presheaf.obj (op V)) :
    evExt e V (fun _ ↦ C a) = algebraMap ((disc hB).presheaf.obj (op V)) (boundedSubring W V) a :=
  boundedSubring_ext e fun i y hy ↦ by
    rw [eval_evExt, eval₂_C, algebraMap_val, eval_pullbackHom, coe_hom_base_piece,
      evalAt_holFun (kummerPt_mem hy)]

variable (e V) in
/-- **The canonical extension is free**: `(gᵢⱼ) ↦ ∑ gᵢⱼ uʲ` is an isomorphism of
`𝒪_S(V)`-modules `∏ᵢ 𝒪_S(V)^{kᵢ} ≃ 𝒞̄(V)`. -/
def coeffEquiv : (∀ i, Fin (k i) → (disc hB).presheaf.obj (op V)) ≃ₗ[(disc hB).presheaf.obj (op V)]
    boundedSubring W V := by
  refine LinearEquiv.ofBijective
    { toFun g := evExt e V (coeffPoly g)
      map_add' g g' := by
        rw [← map_add]
        congr 1
        funext i
        simp [coeffPoly, Finset.sum_add_distrib, add_mul]
      map_smul' a g := by
        rw [RingHom.id_apply]
        conv_rhs => rw [Algebra.smul_def, ← evExt_C (e := e), ← map_mul]
        congr 1
        funext i
        simp [coeffPoly, Finset.mul_sum, mul_assoc] } ⟨?_, fun s ↦ exists_coeffPoly_eq e s⟩
  refine (injective_iff_map_eq_zero _).2 fun g hg ↦ funext fun i ↦ ?_
  refine eq_zero_of_forall_sum_eq_zero e (g i) fun y hy ↦ ?_
  have h₁ := congrArg (fun s : boundedSubring W V ↦ W.left.eval _ hy s.1) hg
  simp only [ZeroMemClass.coe_zero, map_zero] at h₁
  change W.left.eval _ hy (evExt e V (coeffPoly g)).1 = 0 at h₁
  rwa [eval_evExt, eval₂_coeffPoly] at h₁

variable (e V) in
include e in
theorem free_boundedSubring : Module.Free ((disc hB).presheaf.obj (op V)) (boundedSubring W V) :=
  Module.Free.of_equiv (coeffEquiv e V)

variable (e V) in
include e in
theorem finite_boundedSubring :
    Module.Finite ((disc hB).presheaf.obj (op V)) (boundedSubring W V) :=
  Module.Finite.equiv (coeffEquiv e V)

variable (e V) in
include e in
/-- **Bounded sections are integral** over `𝒪_S(V)`. -/
theorem isIntegral_boundedSubring :
    Algebra.IsIntegral ((disc hB).presheaf.obj (op V)) (boundedSubring W V) :=
  haveI := finite_boundedSubring e V
  Algebra.IsIntegral.of_finite _ _

lemma coeffEquiv_apply (g : ∀ i, Fin (k i) → (disc hB).presheaf.obj (op V)) :
    coeffEquiv e V g = evExt e V (coeffPoly g) :=
  rfl

/-- **The isomorphisms `coeffEquiv` are compatible with restriction**, so that `𝒞̄` is isomorphic
to the free `𝒪_S`-module of rank `∑ kᵢ`. -/
theorem extensionPresheaf_map_coeffEquiv {V' : (disc hB).Opens} (h : V' ≤ V)
    (g : ∀ i, Fin (k i) → (disc hB).presheaf.obj (op V)) :
    (extensionPresheaf W).map (homOfLE h).op (coeffEquiv e V g) =
      coeffEquiv e V' fun i j ↦ (disc hB).presheaf.map (homOfLE h).op (g i j) := by
  refine boundedSubring_ext e fun i y hy ↦ ?_
  have hy' : W.hom.toLRSHom.base ((piece e i).toLRSHom.base y) ∈
      puncturedPreimage hB (isOpen_coeOpens V) := coeOpens_mono h hy
  refine (eval_presheaf_map W.left _ _ hy _).trans
    ((eval_evExt (e := e) (coeffPoly g) i y hy').trans ?_)
  rw [coeffEquiv_apply, eval_evExt, eval₂_coeffPoly, eval₂_coeffPoly]
  rfl

omit [Finite ι] in
/-- For `B` convex, every finite étale cover of `S°` with Hausdorff total space is locally
isomorphic to opens of `ℂ^{m+1}`, so that `ComplexAnalytic.KummerModel.extensionSheaf` applies. -/
theorem isLocallyOpenInAffine_of_convex (hBc : Convex ℝ B) (W : FiniteEtaleOver (punctured hB))
    [T2Space W.left] : IsLocallyOpenInAffine W.left := by
  obtain ⟨ι, _, k, ⟨e⟩⟩ := exists_iso_sigma_cover hB hBc W
  exact isLocallyOpenInAffine_left e

end

end ComplexAnalytic.KummerModel
