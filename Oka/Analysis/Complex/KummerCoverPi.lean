/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analysis.Complex.KummerCover
import Oka.Topology.Covering.Basic

/-!
# Finite coverings of a product with a power of the punctured disc

Let `B` be a convex open subset of a real normed space `E` and let `Δ*` be the punctured unit
disc. The space `B × (Δ*)ʳ` has fundamental group `ℤʳ`, and every covering of it with finite
fibres is, on each path component, a quotient of a Kummer covering
`B × (Δ*)ʳ → B × (Δ*)ʳ, (b, u) ↦ (b, u₁ᴹ, …, uᵣᴹ)` by a subgroup of the group `(ℤ / M)ʳ` of
`M`-th roots of unity acting coordinatewise.

The proof is that of `Oka/Analysis/Complex/KummerCover.lean`: a covering `p : X → B × (Δ*)ʳ` with
finite fibres receives a lift `ψ` of the universal covering
`B × {Re w < 0}ʳ → B × (Δ*)ʳ, (b, w) ↦ (b, exp w)`. The translations `w ↦ w + 2πia` under which
`ψ` is invariant form a subgroup `Γ ≤ ℤʳ` of finite index, so `Mℤʳ ≤ Γ` for `M` the index, and
`(b, u) ↦ ψ(b, M log u)` identifies the quotient of the Kummer covering of degree `M` by
`Γ / Mℤʳ` with a path component of `X`.

## Main definitions

- `KummerPi.base B r`: the set `B × (Δ*)ʳ` inside `E × ℂʳ`.
- `KummerPi.cover B r M`: the Kummer covering `(b, u) ↦ (b, uᴹ)` of `B × (Δ*)ʳ`.
- `KummerPi.rot B r M a`: multiplication of the coordinates by the roots of unity
  `exp(2πi aⱼ / M)`.
- `KummerPi.expMap B r`: the universal covering `(b, w) ↦ (b, exp w)`.
- `KummerPi.fundamentalGroupEquiv`: the fundamental group of `B × (Δ*)ʳ` is `ℤʳ`.

## Main results

- `KummerPi.isAddQuotientCoveringMap_expMap`: `B × (Δ*)ʳ` is the quotient of `B × {Re w < 0}ʳ` by
  the translations by `2πiℤʳ`.
- `KummerPi.isCoveringMap_cover`: the Kummer map is a covering map with finite fibres.
- `IsCoveringMap.exists_kummerPi`: a path component of a covering of `B × (Δ*)ʳ` with finite
  fibres is the image of an open map `Φ` from `B × (Δ*)ʳ` with `p ∘ Φ` the Kummer covering of some
  degree `M` and whose fibres are the orbits of a subgroup `Γ ≤ ℤʳ` containing `Mℤʳ`, acting by
  `KummerPi.rot`.
- `IsCoveringMap.exists_kummerPi_of_pathConnectedSpace`: a path connected covering of `B × (Δ*)ʳ`
  with finite fibres is such a quotient of a Kummer covering.
- `IsCoveringMap.exists_sigma_kummerPi`: a covering of `B × (Δ*)ʳ` with finite fibres is a finite
  disjoint union of quotients of Kummer coverings.
-/

open Set Topology Complex

namespace KummerPi

noncomputable section

variable {E : Type*} (B : Set E) (r : ℕ)

/-- The product `B × (Δ*)ʳ` of `B` with a power of the punctured unit disc. -/
def base : Set (E × (Fin r → ℂ)) := B ×ˢ univ.pi fun _ ↦ Kummer.puncturedDisc

variable {B r} in
lemma mem_base {x : E × (Fin r → ℂ)} :
    x ∈ base B r ↔ x.1 ∈ B ∧ ∀ i, x.2 i ≠ 0 ∧ ‖x.2 i‖ < 1 := by
  simp [base, Kummer.puncturedDisc]

lemma isOpen_base [TopologicalSpace E] {B : Set E} (hB : IsOpen B) : IsOpen (base B r) :=
  hB.prod (isOpen_set_pi finite_univ fun _ _ ↦ Kummer.isOpen_puncturedDisc)

/-- The Kummer covering `(b, u) ↦ (b, u₁ᴹ, …, uᵣᴹ)` of `B × (Δ*)ʳ`. -/
def cover (M : ℕ+) (y : base B r) : base B r :=
  ⟨(y.1.1, fun i ↦ y.1.2 i ^ (M : ℕ)), mem_base.2 ⟨(mem_base.1 y.2).1, fun i ↦
    ⟨pow_ne_zero _ ((mem_base.1 y.2).2 i).1, by
      rw [norm_pow]
      exact pow_lt_one₀ (norm_nonneg _) ((mem_base.1 y.2).2 i).2 M.ne_zero⟩⟩⟩

@[simp]
lemma cover_apply (M : ℕ+) (y : base B r) :
    (cover B r M y : E × (Fin r → ℂ)) = (y.1.1, fun i ↦ y.1.2 i ^ (M : ℕ)) :=
  rfl

/-- Multiplication of the `j`-th coordinate by the root of unity `exp(2πi aⱼ / M)`. -/
def rot (M : ℕ+) (a : Fin r → ℤ) (y : base B r) : base B r :=
  ⟨(y.1.1, fun i ↦ Complex.exp (2 * Real.pi * Complex.I * a i / M) * y.1.2 i), mem_base.2
    ⟨(mem_base.1 y.2).1, fun i ↦ by
      have hn : ‖Complex.exp (2 * Real.pi * Complex.I * a i / M)‖ = 1 := by
        rw [Complex.norm_exp]
        simp
      exact ⟨mul_ne_zero (Complex.exp_ne_zero _) ((mem_base.1 y.2).2 i).1, by
        rw [norm_mul, hn, one_mul]
        exact ((mem_base.1 y.2).2 i).2⟩⟩⟩

@[simp]
lemma rot_apply (M : ℕ+) (a : Fin r → ℤ) (y : base B r) :
    (rot B r M a y : E × (Fin r → ℂ)) =
      (y.1.1, fun i ↦ Complex.exp (2 * Real.pi * Complex.I * a i / M) * y.1.2 i) :=
  rfl

/-- The subset `B × {Re w < 0}ʳ` of `E × ℂʳ`, the universal covering space of `B × (Δ*)ʳ`. -/
def logCover : Set (E × (Fin r → ℂ)) := B ×ˢ univ.pi fun _ ↦ {w : ℂ | w.re < 0}

variable {B r} in
lemma mem_logCover {x : E × (Fin r → ℂ)} : x ∈ logCover B r ↔ x.1 ∈ B ∧ ∀ i, (x.2 i).re < 0 := by
  simp [logCover]

lemma isOpen_logCover [TopologicalSpace E] {B : Set E} (hB : IsOpen B) :
    IsOpen (logCover B r) :=
  hB.prod (isOpen_set_pi finite_univ fun _ _ ↦ isOpen_lt Complex.continuous_re continuous_const)

lemma convex_logCover [AddCommGroup E] [Module ℝ E] {B : Set E} (hB : Convex ℝ B) :
    Convex ℝ (logCover B r) :=
  hB.prod (convex_pi fun _ _ ↦ convex_halfSpace_re_lt 0)

/-- The universal covering `(b, w) ↦ (b, exp w)` of `B × (Δ*)ʳ`. -/
def expMap (x : logCover B r) : base B r :=
  ⟨(x.1.1, fun i ↦ Complex.exp (x.1.2 i)), mem_base.2 ⟨(mem_logCover.1 x.2).1, fun i ↦
    ⟨Complex.exp_ne_zero _, by
      rw [Complex.norm_exp]
      exact Real.exp_lt_one_iff.2 ((mem_logCover.1 x.2).2 i)⟩⟩⟩

@[simp]
lemma expMap_apply (x : logCover B r) :
    (expMap B r x : E × (Fin r → ℂ)) = (x.1.1, fun i ↦ Complex.exp (x.1.2 i)) :=
  rfl

lemma continuous_expMap [TopologicalSpace E] : Continuous (expMap B r) := by
  unfold expMap
  fun_prop

/-- A point of `B × {Re w < 0}ʳ` over a point of `B × (Δ*)ʳ`, given by the principal logarithm. -/
def logLift (y : base B r) : logCover B r :=
  ⟨(y.1.1, fun i ↦ Complex.log (y.1.2 i)), mem_logCover.2 ⟨(mem_base.1 y.2).1, fun i ↦ by
    rw [Complex.log_re]
    exact Real.log_neg (norm_pos_iff.2 ((mem_base.1 y.2).2 i).1) ((mem_base.1 y.2).2 i).2⟩⟩

@[simp]
lemma expMap_logLift (y : base B r) : expMap B r (logLift B r y) = y :=
  Subtype.ext (Prod.ext rfl (funext fun i ↦ Complex.exp_log ((mem_base.1 y.2).2 i).1))

lemma surjective_expMap : Function.Surjective (expMap B r) :=
  fun y ↦ ⟨logLift B r y, expMap_logLift B r y⟩

/-- The translation `(b, w) ↦ (b, w + 2πia)` of `B × {Re w < 0}ʳ`. -/
def shift (a : Fin r → ℤ) (x : logCover B r) : logCover B r :=
  ⟨(x.1.1, fun i ↦ x.1.2 i + a i * (2 * Real.pi * Complex.I)), mem_logCover.2
    ⟨(mem_logCover.1 x.2).1, fun i ↦ by simpa using (mem_logCover.1 x.2).2 i⟩⟩

@[simp]
lemma shift_apply (a : Fin r → ℤ) (x : logCover B r) :
    (shift B r a x : E × (Fin r → ℂ)) =
      (x.1.1, fun i ↦ x.1.2 i + a i * (2 * Real.pi * Complex.I)) :=
  rfl

lemma shift_zero (x : logCover B r) : shift B r 0 x = x :=
  Subtype.ext (Prod.ext rfl (funext fun i ↦ by simp))

lemma shift_add (a b : Fin r → ℤ) (x : logCover B r) :
    shift B r (a + b) x = shift B r a (shift B r b x) :=
  Subtype.ext (Prod.ext rfl (funext fun i ↦ by simp; ring))

@[fun_prop]
lemma continuous_shift [TopologicalSpace E] (a : Fin r → ℤ) : Continuous (shift B r a) := by
  unfold shift
  fun_prop

@[simp]
lemma expMap_shift (a : Fin r → ℤ) (x : logCover B r) : expMap B r (shift B r a x) = expMap B r x :=
  Subtype.ext (Prod.ext rfl (funext fun i ↦ by
    simp [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I]))

variable {B r} in
lemma exists_eq_shift {x x' : logCover B r} (h : expMap B r x = expMap B r x') :
    ∃ a : Fin r → ℤ, x = shift B r a x' := by
  have h₁ := congrArg (fun y : base B r ↦ y.1.1) h
  have h₂ (i : Fin r) := congrArg (fun y : base B r ↦ y.1.2 i) h
  choose a ha using fun i ↦ Complex.exp_eq_exp_iff_exists_int.1 (h₂ i)
  exact ⟨a, Subtype.ext (Prod.ext h₁ (funext ha))⟩

instance : AddAction (Fin r → ℤ) (logCover B r) where
  vadd := shift B r
  zero_vadd := shift_zero B r
  add_vadd := shift_add B r

lemma vadd_def (a : Fin r → ℤ) (x : logCover B r) : a +ᵥ x = shift B r a x :=
  rfl

lemma preimage_prodMap_exp_base :
    Prod.map (id : E → E) (Pi.map fun _ : Fin r ↦ Complex.exp) ⁻¹' base B r = logCover B r := by
  ext ⟨b, w⟩
  simp [mem_base, mem_logCover, Complex.norm_exp, Complex.exp_ne_zero]

lemma isOpenMap_expMap [TopologicalSpace E] : IsOpenMap (expMap B r) := by
  have h : IsOpenMap (Prod.map (id : E → E) (Pi.map fun _ : Fin r ↦ Complex.exp)) :=
    IsOpenMap.id.prodMap (IsOpenMap.piMap (fun _ ↦ Complex.isOpenMap_exp)
      (Filter.eventually_cofinite.2 (Set.toFinite _)))
  convert (h.restrictPreimage (base B r)).comp
    (Homeomorph.setCongr (preimage_prodMap_exp_base B r).symm).isOpenMap using 1
  funext y
  rfl

/-- **`B × (Δ*)ʳ` is the quotient of `B × {Re w < 0}ʳ` by the translations by `2πiℤʳ`.** -/
theorem isAddQuotientCoveringMap_expMap [TopologicalSpace E] :
    IsAddQuotientCoveringMap (expMap B r) (Fin r → ℤ) where
  toIsQuotientMap := (isOpenMap_expMap B r).isQuotientMap (continuous_expMap B r)
    (surjective_expMap B r)
  continuous_const_vadd a := continuous_shift B r a
  apply_eq_iff_mem_orbit {x x'} := by
    rw [AddAction.mem_orbit_iff]
    refine ⟨fun h ↦ ?_, ?_⟩
    · obtain ⟨a, rfl⟩ := exists_eq_shift h
      exact ⟨a, rfl⟩
    · rintro ⟨a, rfl⟩
      exact expMap_shift B r a x'
  disjoint x := by
    have hU : IsOpen {z : logCover B r | ∀ i, ‖z.1.2 i - x.1.2 i‖ < 1} := by
      rw [setOf_forall]
      exact isOpen_iInter_of_finite fun i ↦ isOpen_lt (by fun_prop) continuous_const
    refine ⟨{z | ∀ i, ‖z.1.2 i - x.1.2 i‖ < 1}, hU.mem_nhds (fun i ↦ by simp),
      fun a ⟨z, ⟨z', hz', hz⟩, hz''⟩ ↦ ?_⟩
    change shift B r a z' = z at hz
    subst hz
    funext i
    have h1 := hz' i
    have h2 := hz'' i
    simp only [shift_apply] at h1 h2
    have h : ‖(a i : ℂ) * (2 * Real.pi * Complex.I)‖ < 2 := by
      calc _ = ‖(z'.1.2 i + a i * (2 * Real.pi * Complex.I) - x.1.2 i) - (z'.1.2 i - x.1.2 i)‖ := by
              ring_nf
        _ ≤ ‖z'.1.2 i + a i * (2 * Real.pi * Complex.I) - x.1.2 i‖ + ‖z'.1.2 i - x.1.2 i‖ :=
              norm_sub_le _ _
        _ < 1 + 1 := add_lt_add h2 h1
        _ = 2 := by norm_num
    by_contra hj
    have h1 : (1 : ℝ) ≤ |(a i : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hj
    have h2 : ‖(a i : ℂ) * (2 * Real.pi * Complex.I)‖ = |(a i : ℝ)| * (2 * Real.pi) := by
      rw [norm_mul, Complex.norm_intCast, norm_mul, norm_mul, Complex.norm_I,
        Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
      norm_num
    rw [h2] at h
    nlinarith [Real.two_le_pi]

variable {B r}

lemma nonempty_logCover (y : base B r) : (logCover B r).Nonempty :=
  ⟨_, (logLift B r y).2⟩

/-- **The fundamental group of `B × (Δ*)ʳ` is `ℤʳ`**, for `B` convex. -/
def fundamentalGroupEquiv [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] (hB : Convex ℝ B) (y : base B r) :
    FundamentalGroup (base B r) y ≃* Multiplicative (Fin r → ℤ) :=
  haveI : ContractibleSpace (logCover B r) :=
    (convex_logCover r hB).contractibleSpace (nonempty_logCover y)
  ((isAddQuotientCoveringMap_expMap B r).fundamentalGroupEquiv
    (⟨logLift B r y, expMap_logLift B r y⟩ : expMap B r ⁻¹' {y})).trans
    MulOpposite.opMulEquiv.symm

/-- The dilation `(b, w) ↦ (b, M w)` of `B × {Re w < 0}ʳ`. -/
def scale (M : ℕ+) (x : logCover B r) : logCover B r :=
  ⟨(x.1.1, fun i ↦ (M : ℂ) * x.1.2 i), mem_logCover.2 ⟨(mem_logCover.1 x.2).1, fun i ↦ by
    simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
    exact mul_neg_of_pos_of_neg (by exact_mod_cast M.pos) ((mem_logCover.1 x.2).2 i)⟩⟩

/-- The contraction `(b, w) ↦ (b, w / M)` of `B × {Re w < 0}ʳ`. -/
def unscale (M : ℕ+) (x : logCover B r) : logCover B r :=
  ⟨(x.1.1, fun i ↦ x.1.2 i / (M : ℂ)), mem_logCover.2 ⟨(mem_logCover.1 x.2).1, fun i ↦ by
    rw [Complex.div_natCast_re]
    exact div_neg_of_neg_of_pos ((mem_logCover.1 x.2).2 i) (by exact_mod_cast M.pos)⟩⟩

lemma scale_unscale (M : ℕ+) (x : logCover B r) : scale M (unscale M x) = x :=
  Subtype.ext (Prod.ext rfl (funext fun i ↦ mul_div_cancel₀ _ (by exact_mod_cast M.ne_zero)))

lemma unscale_scale (M : ℕ+) (x : logCover B r) : unscale M (scale M x) = x :=
  Subtype.ext (Prod.ext rfl (funext fun i ↦ mul_div_cancel_left₀ _ (by exact_mod_cast M.ne_zero)))

@[fun_prop]
lemma continuous_scale [TopologicalSpace E] (M : ℕ+) : Continuous (scale (B := B) (r := r) M) := by
  unfold scale
  fun_prop

@[fun_prop]
lemma continuous_unscale [TopologicalSpace E] (M : ℕ+) :
    Continuous (unscale (B := B) (r := r) M) := by
  unfold unscale
  fun_prop

lemma scale_shift (M : ℕ+) (a : Fin r → ℤ) (x : logCover B r) :
    scale M (shift B r a x) = shift B r ((M : ℤ) • a) (scale M x) :=
  Subtype.ext (Prod.ext rfl (funext fun i ↦ by simp [scale]; ring))

lemma expMap_scale (M : ℕ+) (x : logCover B r) :
    expMap B r (scale M x) = cover B r M (expMap B r x) :=
  Subtype.ext (Prod.ext rfl (funext fun i ↦ by simp [scale, Complex.exp_nat_mul]))

lemma expMap_unscale_shift (M : ℕ+) (a : Fin r → ℤ) (x : logCover B r) :
    expMap B r (unscale M (shift B r a x)) = rot B r M a (expMap B r (unscale M x)) :=
  Subtype.ext (Prod.ext rfl (funext fun i ↦ by
    simp only [expMap_apply, rot_apply, unscale, shift_apply, ← Complex.exp_add]
    congr 1
    field_simp
    ring))
/-- The dilation `(b, w) ↦ (b, M w)`, as a homeomorphism of `B × {Re w < 0}ʳ`. -/
def scaleHomeomorph [TopologicalSpace E] (M : ℕ+) : logCover B r ≃ₜ logCover B r where
  toFun := scale M
  invFun := unscale M
  left_inv := unscale_scale M
  right_inv := scale_unscale M
  continuous_toFun := continuous_scale M
  continuous_invFun := continuous_unscale M

lemma isLocalHomeomorph_cover [TopologicalSpace E] (M : ℕ+) :
    IsLocalHomeomorph (cover B r M) := by
  have h : IsLocalHomeomorph (cover B r M ∘ expMap B r) := by
    have : cover B r M ∘ expMap B r = expMap B r ∘ scaleHomeomorph M :=
      funext fun x ↦ (expMap_scale M x).symm
    rw [this]
    exact (isAddQuotientCoveringMap_expMap B r).isCoveringMap.isLocalHomeomorph.comp
      (scaleHomeomorph M).isLocalHomeomorph
  rw [isLocalHomeomorph_iff_isLocalHomeomorphOn_univ] at h ⊢
  have := h.of_comp_right
    (isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.1
      (isAddQuotientCoveringMap_expMap B r).isCoveringMap.isLocalHomeomorph)
  rwa [image_univ, (surjective_expMap B r).range_eq] at this

lemma finite_preimage_pow (M : ℕ+) (t : ℂ) : ((fun u : ℂ ↦ u ^ (M : ℕ)) ⁻¹' {t}).Finite := by
  classical
  refine (Polynomial.nthRoots (M : ℕ) t).toFinset.finite_toSet.subset fun u hu ↦ ?_
  rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_nthRoots M.pos]
  exact hu

lemma preimage_prodMap_pow_base (M : ℕ+) :
    Prod.map (id : E → E) (Pi.map fun _ : Fin r ↦ fun u : ℂ ↦ u ^ (M : ℕ)) ⁻¹' base B r =
      base B r := by
  ext ⟨b, u⟩
  simp only [mem_preimage, Prod.map_apply, id_eq, mem_base, Pi.map_apply, norm_pow, ne_eq,
    pow_eq_zero_iff (PNat.ne_zero M),
    pow_lt_one_iff_of_nonneg (norm_nonneg _) (PNat.ne_zero M)]

lemma isClosedMap_cover [NormedAddCommGroup E] (M : ℕ+) : IsClosedMap (cover B r M) := by
  have hpow : IsProperMap fun u : ℂ ↦ u ^ (M : ℕ) :=
    isProperMap_iff_isClosedMap_and_compact_fibers.2 ⟨continuous_pow _, isClosedMap_pow ℂ (M : ℕ),
      fun t ↦ (finite_preimage_pow M t).isCompact⟩
  have hF : IsClosedMap (Prod.map (id : E → E) (Pi.map fun _ : Fin r ↦ fun u : ℂ ↦ u ^ (M : ℕ))) :=
    (isProperMap_id.prodMap (IsProperMap.pi_map fun _ ↦ hpow)).isClosedMap
  convert (hF.restrictPreimage (base B r)).comp
    (Homeomorph.setCongr (preimage_prodMap_pow_base M).symm).isClosedMap using 1
  funext y
  rfl

lemma finite_preimage_cover (M : ℕ+) (y : base B r) : (cover B r M ⁻¹' {y}).Finite := by
  refine Finite.of_finite_image (f := fun z : base B r ↦ z.1.2)
    ((Set.Finite.pi (t := fun i ↦ (fun u : ℂ ↦ u ^ (M : ℕ)) ⁻¹' {y.1.2 i})
      fun i ↦ finite_preimage_pow M _).subset ?_) ?_
  · rintro _ ⟨z, hz, rfl⟩ i -
    exact congrArg (fun y : base B r ↦ y.1.2 i) hz
  · intro z hz z' hz' h
    have h₁ := congrArg (fun y : base B r ↦ y.1.1) (hz.trans hz'.symm)
    exact Subtype.ext (Prod.ext h₁ h)

lemma surjective_cover (M : ℕ+) : Function.Surjective (cover B r M) := by
  intro y
  obtain ⟨x, rfl⟩ := surjective_expMap B r y
  exact ⟨expMap B r (unscale M x), by rw [← expMap_scale, scale_unscale]⟩

/-- The Kummer map `(b, u) ↦ (b, uᴹ)` of `B × (Δ*)ʳ` is a covering map. -/
theorem isCoveringMap_cover [NormedAddCommGroup E] (M : ℕ+) : IsCoveringMap (cover B r M) :=
  (isClosedMap_cover M).isCoveringMap_of_isLocalHomeomorph (finite_preimage_cover M)
    (isLocalHomeomorph_cover M)

end

end KummerPi

open KummerPi

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {B : Set E} {r : ℕ}
  {X : Type*} [TopologicalSpace X] {p : X → base B r}

/-- **The path components of a covering of `B × (Δ*)ʳ` are quotients of Kummer coverings.** Let
`p` be a covering map of `B × (Δ*)ʳ` with finite fibres, `B` convex and open. The path component
of any `e₀` is the image of a continuous open map `Φ` from `B × (Δ*)ʳ` such that `p ∘ Φ` is the
Kummer covering of some degree `M`, and whose fibres are the orbits of a subgroup `Γ ≤ ℤʳ`
containing `Mℤʳ`, acting through the roots of unity `KummerPi.rot`. -/
theorem IsCoveringMap.exists_kummerPi (hB : Convex ℝ B) (hBo : IsOpen B) (hp : IsCoveringMap p)
    (hfin : ∀ y, (p ⁻¹' {y}).Finite) (e₀ : X) :
    ∃ (M : ℕ+) (Γ : AddSubgroup (Fin r → ℤ)) (Φ : base B r → X), (∀ a, (M : ℤ) • a ∈ Γ) ∧
      Continuous Φ ∧ IsOpenMap Φ ∧ range Φ = pathComponent e₀ ∧
      (∀ y, p (Φ y) = cover B r M y) ∧ ∀ y y', Φ y = Φ y' ↔ ∃ a ∈ Γ, y' = rot B r M a y := by
  set x₀ := logLift B r (p e₀)
  haveI : ContractibleSpace (logCover B r) :=
    (convex_logCover r hB).contractibleSpace (nonempty_logCover (p e₀))
  haveI : LocallyPathConnectedSpace (logCover B r) :=
    (isOpen_logCover r hBo).locallyPathConnectedSpace
  have hexp := (isAddQuotientCoveringMap_expMap B r).isCoveringMap
  obtain ⟨ψ, ⟨hψ₀, hψ⟩, -⟩ := hp.existsUnique_continuousMap_lifts
    ⟨expMap B r, hexp.continuous⟩ x₀ e₀ (expMap_logLift B r _).symm
  have hψ' (x : logCover B r) : p (ψ x) = expMap B r x := congrFun hψ x
  have L1 (a : Fin r → ℤ) (x : logCover B r) (h : ψ (shift B r a x) = ψ x) (x' : logCover B r) :
      ψ (shift B r a x') = ψ x' := by
    have := hp.eq_of_comp_eq (g₁ := ψ ∘ shift B r a) (g₂ := ψ) (by fun_prop) ψ.continuous
      (funext fun z ↦ by simp [hψ']) x h
    exact congrFun this x'
  let Γ : AddSubgroup (Fin r → ℤ) :=
    { carrier := {a | ∀ x, ψ (shift B r a x) = ψ x}
      add_mem' := fun {a b} ha hb x ↦ by
        simp only [mem_setOf_eq] at ha hb ⊢
        rw [shift_add, ha, hb]
      zero_mem' := fun x ↦ by simp only [shift_zero]
      neg_mem' := fun {a} ha x ↦ by
        simp only [mem_setOf_eq] at ha ⊢
        rw [← ha (shift B r (-a) x), ← shift_add, add_neg_cancel, shift_zero] }
  have hΓ (a : Fin r → ℤ) : a ∈ Γ ↔ ∀ x, ψ (shift B r a x) = ψ x := Iff.rfl
  -- `Γ` has finite index since the fibre over `p e₀` is finite.
  haveI := (hfin (p e₀)).to_subtype
  let f : (Fin r → ℤ) → p ⁻¹' {p e₀} := fun a ↦ ⟨ψ (shift B r a x₀), by simp [hψ', x₀]⟩
  have hf (a b : Fin r → ℤ) : f a = f b ↔ -a + b ∈ Γ := by
    constructor
    · intro h
      refine L1 (-a + b) (shift B r a x₀) ?_
      rw [← shift_add, show -a + b + a = b by abel]
      exact (congrArg Subtype.val h).symm
    · intro h
      refine Subtype.ext ?_
      change ψ (shift B r a x₀) = ψ (shift B r b x₀)
      rw [← h (shift B r a x₀), ← shift_add, show -a + b + a = b by abel]
  haveI : Finite ((Fin r → ℤ) ⧸ Γ) := by
    refine Finite.of_injective (Quotient.lift f fun a b h ↦ (hf a b).2 ?_) ?_
    · exact QuotientAddGroup.leftRel_apply.1 h
    · rintro ⟨a⟩ ⟨b⟩ h
      exact Quotient.sound (QuotientAddGroup.leftRel_apply.2 ((hf a b).1 h))
  let M : ℕ+ := ⟨Γ.index, Nat.pos_of_ne_zero (AddSubgroup.index_ne_zero_of_finite)⟩
  have hM (a : Fin r → ℤ) : (M : ℤ) • a ∈ Γ := by
    rw [natCast_zsmul]
    exact AddSubgroup.nsmul_index_mem Γ a
  -- The map `(b, u) ↦ ψ(b, M log u)`.
  let Φ : base B r → X := fun y ↦ ψ (scale M (logLift B r y))
  have L2 (x : logCover B r) : Φ (expMap B r x) = ψ (scale M x) := by
    obtain ⟨a, ha⟩ := exists_eq_shift (expMap_logLift B r (expMap B r x))
    simp only [Φ]
    rw [ha, scale_shift]
    exact hM a _
  have hcont : Continuous Φ := by
    rw [(isAddQuotientCoveringMap_expMap B r).toIsQuotientMap.continuous_iff]
    have : Φ ∘ expMap B r = ψ ∘ scale M := funext L2
    rw [this]
    fun_prop
  have hpΦ (y : base B r) : p (Φ y) = cover B r M y := by
    simp only [Φ, hψ', expMap_scale, expMap_logLift]
  have hscale : ∀ S : Set (logCover B r), IsOpen S → IsOpen (scale M '' S) := fun S hS ↦ by
    rw [image_eq_preimage_of_inverse (unscale_scale M) (scale_unscale M)]
    exact hS.preimage (continuous_unscale M)
  have hψo : IsOpenMap ψ := by
    refine (IsLocalHomeomorph.of_comp (g := p) ?_ hp.isLocalHomeomorph ψ.continuous).isOpenMap
    have : p ∘ ψ = expMap B r := funext hψ'
    rw [this]
    exact hexp.isLocalHomeomorph
  refine ⟨M, Γ, Φ, hM, hcont, fun U hU ↦ ?_, ?_, hpΦ, fun y y' ↦ ?_⟩
  · have : Φ '' U = ψ '' (scale M '' (expMap B r ⁻¹' U)) := by
      ext e
      constructor
      · rintro ⟨y, hy, rfl⟩
        obtain ⟨x, rfl⟩ := surjective_expMap B r y
        exact ⟨scale M x, ⟨x, hy, rfl⟩, (L2 x).symm⟩
      · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
        exact ⟨expMap B r x, hx, L2 x⟩
    rw [this]
    exact hψo _ (hscale _ (hU.preimage hexp.continuous))
  · ext e
    constructor
    · rintro ⟨y, rfl⟩
      have h := (PathConnectedSpace.joined x₀ (scale M (logLift B r y))).somePath.map
        ψ.continuous
      rw [hψ₀] at h
      exact ⟨h⟩
    · intro he
      obtain ⟨γ⟩ := (mem_pathComponent_iff.1 he)
      obtain ⟨Γ', hΓ', hΓ'0⟩ := hexp.exists_path_lifts
        ⟨fun t ↦ p (γ t), hp.continuous.comp γ.continuous⟩ x₀ (by simp [x₀])
      have := hp.eq_of_comp_eq (g₁ := ψ ∘ Γ') (g₂ := γ) (by fun_prop) γ.continuous
        (funext fun t ↦ by simpa [hψ'] using congrFun hΓ' t) 0 (by simp [hΓ'0, hψ₀])
      refine ⟨expMap B r (unscale M (Γ' 1)), ?_⟩
      rw [L2, scale_unscale]
      simpa using congrFun this 1
  · obtain ⟨x, rfl⟩ := surjective_expMap B r y
    constructor
    · intro h
      obtain ⟨x', rfl⟩ := surjective_expMap B r y'
      rw [L2, L2] at h
      have h' : expMap B r (scale M x') = expMap B r (scale M x) := by
        rw [← hψ', ← h, hψ']
      obtain ⟨c, hc⟩ := exists_eq_shift h'
      rw [hc] at h
      refine ⟨c, L1 c _ h.symm, ?_⟩
      rw [← unscale_scale M x', hc, expMap_unscale_shift, unscale_scale]
    · rintro ⟨c, hc, rfl⟩
      rw [← unscale_scale M x, ← expMap_unscale_shift, L2, L2, scale_unscale, scale_unscale]
      exact (hc _).symm

/-- **A path connected covering of `B × (Δ*)ʳ` with finite fibres is a quotient of a Kummer
covering**: there is a surjective continuous open map `Φ` from `B × (Δ*)ʳ` over the Kummer covering
of some degree `M` whose fibres are the orbits of a subgroup `Γ ≤ ℤʳ` containing `Mℤʳ`. -/
theorem IsCoveringMap.exists_kummerPi_of_pathConnectedSpace [PathConnectedSpace X]
    (hB : Convex ℝ B) (hBo : IsOpen B) (hp : IsCoveringMap p) (hfin : ∀ y, (p ⁻¹' {y}).Finite) :
    ∃ (M : ℕ+) (Γ : AddSubgroup (Fin r → ℤ)) (Φ : base B r → X), (∀ a, (M : ℤ) • a ∈ Γ) ∧
      Continuous Φ ∧ IsOpenMap Φ ∧ Function.Surjective Φ ∧
      (∀ y, p (Φ y) = cover B r M y) ∧ ∀ y y', Φ y = Φ y' ↔ ∃ a ∈ Γ, y' = rot B r M a y := by
  obtain ⟨M, Γ, Φ, hM, hcont, hopen, hrange, hpΦ, hfib⟩ :=
    hp.exists_kummerPi hB hBo hfin (Classical.arbitrary X)
  refine ⟨M, Γ, Φ, hM, hcont, hopen, ?_, hpΦ, hfib⟩
  rw [← range_eq_univ, hrange]
  exact eq_univ_of_forall fun e ↦ PathConnectedSpace.joined _ e

/-- **A covering of `B × (Δ*)ʳ` with finite fibres is a finite disjoint union of quotients of
Kummer coverings**, indexed by its path components. -/
theorem IsCoveringMap.exists_sigma_kummerPi (hB : Convex ℝ B) (hBo : IsOpen B)
    (hp : IsCoveringMap p) (hfin : ∀ y, (p ⁻¹' {y}).Finite) :
    Finite (ZerothHomotopy X) ∧ ∃ (M : ZerothHomotopy X → ℕ+)
      (Γ : ZerothHomotopy X → AddSubgroup (Fin r → ℤ)) (Φ : ZerothHomotopy X → base B r → X),
      (∀ c a, (M c : ℤ) • a ∈ Γ c) ∧ (∀ c, Continuous (Φ c)) ∧ (∀ c, IsOpenMap (Φ c)) ∧
      (∀ c y, p (Φ c y) = cover B r (M c) y) ∧ (∀ e, ∃ c y, Φ c y = e) ∧
      (∀ c c' y y', Φ c y = Φ c' y' → c = c') ∧
      ∀ c y y', Φ c y = Φ c y' ↔ ∃ a ∈ Γ c, y' = rot B r (M c) a y := by
  choose rep hrep using ZerothHomotopy.mk_surjective (X := X)
  choose M Γ Φ hM hcont hopen hrange hpΦ hfib using
    fun c ↦ hp.exists_kummerPi hB hBo hfin (rep c)
  have hmem (c : ZerothHomotopy X) (y : base B r) : Φ c y ∈ pathComponent (rep c) :=
    hrange c ▸ mem_range_self y
  have hsep (c c' : ZerothHomotopy X) (y y' : base B r) (h : Φ c y = Φ c' y') : c = c' := by
    have h₁ := hmem c y
    have h₂ := hmem c' y'
    rw [h] at h₁
    rw [← hrep c, ← hrep c']
    exact Quotient.sound ((mem_pathComponent_iff.1 h₁).trans (mem_pathComponent_iff.1 h₂).symm)
  refine ⟨?_, M, Γ, Φ, hM, hcont, hopen, hpΦ, fun e ↦ ?_, hsep, hfib⟩
  · by_cases hX : Nonempty X
    · obtain ⟨e⟩ := hX
      haveI := (hfin (p e)).to_subtype
      choose s hs using fun c ↦ KummerPi.surjective_cover (M c) (p e)
      exact Finite.of_injective (fun c ↦ (⟨Φ c (s c), by simp [hpΦ, hs]⟩ : p ⁻¹' {p e}))
        fun c c' h ↦ hsep c c' _ _ (congrArg Subtype.val h)
    · haveI : IsEmpty X := not_nonempty_iff.1 hX
      haveI : IsEmpty (ZerothHomotopy X) := ⟨fun c ↦ ZerothHomotopy.rec (motive := fun _ ↦ False)
        (fun e ↦ isEmptyElim e) c⟩
      infer_instance
  · have he : e ∈ pathComponent (rep (ZerothHomotopy.mk e)) :=
      mem_pathComponent_iff.2 (Quotient.exact (hrep (ZerothHomotopy.mk e)))
    rw [← hrange] at he
    obtain ⟨y, hy⟩ := he
    exact ⟨_, y, hy⟩
