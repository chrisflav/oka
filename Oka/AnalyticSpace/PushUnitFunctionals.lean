/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.AnalyticSpace.PushUnitStalk
import Oka.AnalyticSpace.HartogsTorsionFree
import Oka.Geometry.RingedSpace.LocallyRingedSpace.ReflexiveHull

/-!
# Separating functionals on `f_* 𝒪_X` from stalk data

Let `f : X ⟶ Y` be a morphism of locally ringed spaces and `b₁, …, b_m` global sections of `𝒪_X`
whose germs generate every stalk of `f_* 𝒪_X` over `𝒪_Y`. Let `μ_{k j}` be global sections of
`𝒪_Y` such that every relation `∑ⱼ cⱼ bⱼ = 0` between germs gives `∑ⱼ cⱼ μ_{k j} = 0`, and
conversely `∑ⱼ cⱼ μ_{k j} = 0` for all `k` implies `∑ⱼ cⱼ bⱼ = 0`. Then
`τ_k (∑ⱼ cⱼ bⱼ) = ∑ⱼ cⱼ μ_{k j}` defines separating functionals on `f_* 𝒪_X`
(`AlgebraicGeometry.LocallyRingedSpace.Hom.separatingFunctionalsOfStalks`).
-/

open CategoryTheory TopologicalSpace Opposite

universe u

noncomputable section

namespace AlgebraicGeometry.LocallyRingedSpace.Hom

variable {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) {m r : ℕ}
  (b : Fin m → X.presheaf.obj (op ((Opens.map f.base).obj ⊤)))
  (μ : Fin r → Fin m → Y.presheaf.obj (op ⊤))

/-- `c` represents `u` over `W ⊆ V`: `u = ∑ⱼ cⱼ bⱼ` on `f⁻¹ W`. -/
def IsRep {V : Opens Y} (u : X.presheaf.obj (op ((Opens.map f.base).obj V))) {W : Opens Y}
    (hW : W ≤ V) (c : Fin m → Y.presheaf.obj (op W)) : Prop :=
  X.res ((Opens.map f.base).monotone hW) u =
    ∑ j, f.cApp W (c j) * X.res ((Opens.map f.base).monotone le_top) (b j)

variable {f b}

lemma IsRep.res {V : Opens Y} {u : X.presheaf.obj (op ((Opens.map f.base).obj V))}
    {W : Opens Y} {hW : W ≤ V} {c : Fin m → Y.presheaf.obj (op W)} (h : IsRep f b u hW c)
    {W' : Opens Y} (h' : W' ≤ W) : IsRep f b u (h'.trans hW) fun j ↦ Y.res h' (c j) := by
  unfold IsRep at h ⊢
  rw [← res_res _ ((Opens.map f.base).monotone h') ((Opens.map f.base).monotone hW), h,
    res_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [res_mul, res_res, cApp_res]

lemma IsRep.add {V : Opens Y} {u u' : X.presheaf.obj (op ((Opens.map f.base).obj V))}
    {W : Opens Y} {hW : W ≤ V} {c c' : Fin m → Y.presheaf.obj (op W)} (h : IsRep f b u hW c)
    (h' : IsRep f b u' hW c') : IsRep f b (u + u') hW (c + c') := by
  unfold IsRep at h h' ⊢
  rw [show X.res ((Opens.map f.base).monotone hW) (u + u') =
    X.res ((Opens.map f.base).monotone hW) u + X.res ((Opens.map f.base).monotone hW) u' from
    map_add _ _ _, h, h', ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Pi.add_apply, map_add, add_mul]

lemma IsRep.mul {V : Opens Y} {u : X.presheaf.obj (op ((Opens.map f.base).obj V))}
    {W : Opens Y} {hW : W ≤ V} {c : Fin m → Y.presheaf.obj (op W)} (h : IsRep f b u hW c)
    (a : Y.presheaf.obj (op V)) :
    IsRep f b (f.cApp V a * u) hW fun j ↦ Y.res hW a * c j := by
  unfold IsRep at h ⊢
  rw [res_mul, ← cApp_res f hW a, h, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [map_mul, mul_assoc]

/-- Germs of sections of `𝒪_Y` determine them. -/
lemma res_eq_of_forall_germ_eq {W : Opens Y} {s t : Y.presheaf.obj (op W)}
    (h : ∀ y (hy : y ∈ W), Y.presheaf.germ W y hy s = Y.presheaf.germ W y hy t) : s = t :=
  res_eq_of_locally fun y hy ↦ exists_res_eq_of_germ_eq hy s t (h y hy)

variable (hker : ∀ (y : Y) (c : Fin m → Y.presheaf.stalk y),
    ∑ j, f.stalkAlgMap y (c j) * f.pgerm ⊤ trivial (b j) = 0 →
      ∀ k, ∑ j, c j * Y.presheaf.germ ⊤ y trivial (μ k j) = 0)

include hker in
/-- **Two representations give the same values of the functionals.** -/
lemma sum_mul_eq_of_isRep {V : Opens Y} {u : X.presheaf.obj (op ((Opens.map f.base).obj V))}
    {W : Opens Y} {hW : W ≤ V} {c c' : Fin m → Y.presheaf.obj (op W)} (h : IsRep f b u hW c)
    (h' : IsRep f b u hW c') (k : Fin r) :
    ∑ j, c j * Y.res le_top (μ k j) = ∑ j, c' j * Y.res le_top (μ k j) := by
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib]
  refine res_eq_of_forall_germ_eq fun y hy ↦ ?_
  unfold IsRep at h h'
  have hd : f.pgerm W hy (∑ j, f.cApp W (c j - c' j) *
      X.res ((Opens.map f.base).monotone le_top) (b j)) = 0 := by
    simp only [map_sub, sub_mul, Finset.sum_sub_distrib, ← h, ← h', sub_self]
    exact map_zero _
  have hd1 : f.pgerm W hy (∑ j, f.cApp W (c j - c' j) *
      X.res ((Opens.map f.base).monotone le_top) (b j)) =
      ∑ j, f.stalkAlgMap y (Y.presheaf.germ W y hy (c j - c' j)) * f.pgerm ⊤ trivial (b j) :=
    (map_sum _ _ _).trans (Finset.sum_congr rfl fun j _ ↦
      (pgerm_mul_cApp f W hy _ _).trans (congrArg (_ * ·) (germ_res_pushforward f le_top hy _)))
  have := hker y _ (hd1.symm.trans hd) k
  refine Eq.trans ?_ (map_zero _).symm
  refine (map_sum _ _ _).trans (Eq.trans (Finset.sum_congr rfl fun j _ ↦ ?_) this)
  exact (congrArg _ (sub_mul _ _ _).symm).trans ((map_mul _ _ _).trans
    (congrArg (HMul.hMul _) (germ_res le_top y hy _)))

lemma res_sum_mul {W W' : Opens Y} (h : W' ≤ W) (c : Fin m → Y.presheaf.obj (op W)) (k : Fin r) :
    Y.res h (∑ j, c j * Y.res le_top (μ k j)) =
      ∑ j, Y.res h (c j) * Y.res le_top (μ k j) := by
  rw [res_sum]
  exact Finset.sum_congr rfl fun j _ ↦ by rw [res_mul, res_res]

variable (hgen : StalkGenerates f (W := ⊤) b)

include hgen in
lemma exists_isRep {V : Opens Y} (u : X.presheaf.obj (op ((Opens.map f.base).obj V))) {y : Y}
    (hy : y ∈ V) : ∃ (W : Opens Y) (hW : W ≤ V), y ∈ W ∧ ∃ c, IsRep f b u hW c := by
  obtain ⟨W, h, hyW, c, hc⟩ := exists_eq_sum_of_stalkGenerates f b hgen le_top u hy
  exact ⟨W, h, hyW, c, hc⟩

variable (b) in
/-- `t` is the value at `u` of the `k`-th functional: `t = ∑ⱼ cⱼ μ_{k j}` for every
representation `u = ∑ⱼ cⱼ bⱼ`. -/
def IsTauValue (k : Fin r) {V : Opens Y} (u : X.presheaf.obj (op ((Opens.map f.base).obj V)))
    (t : Y.presheaf.obj (op V)) : Prop :=
  ∀ (W : Opens Y) (hW : W ≤ V) (c : Fin m → Y.presheaf.obj (op W)), IsRep f b u hW c →
    Y.res hW t = ∑ j, c j * Y.res le_top (μ k j)

include hgen hker in
lemma exists_isTauValue (k : Fin r) {V : Opens Y}
    (u : X.presheaf.obj (op ((Opens.map f.base).obj V))) : ∃ t, IsTauValue b μ k u t := by
  choose W hW hyW c hc using fun y (hy : y ∈ V) ↦ exists_isRep hgen u hy
  obtain ⟨t, ht⟩ := exists_sectRes_eq_of_locally (SheafOfModules.unit Y.ringSheaf) W hW hyW
    (fun y hy ↦ (∑ j, c y hy j * Y.res le_top (μ k j) : Y.presheaf.obj (op (W y hy))))
    fun y hy y' hy' ↦ by
      change Y.res _ _ = Y.res _ _
      rw [res_sum_mul, res_sum_mul]
      exact sum_mul_eq_of_isRep μ hker ((hc y hy).res inf_le_left)
        ((hc y' hy').res inf_le_right) k
  refine ⟨t, fun W' hW' c' hc' ↦ res_eq_of_locally fun y hy ↦ ?_⟩
  refine ⟨W y (hW' hy) ⊓ W', inf_le_right, ⟨hyW y (hW' hy), hy⟩, ?_⟩
  have e := ht y (hW' hy)
  change Y.res (hW y (hW' hy)) t = _ at e
  rw [res_res, ← res_res _ (inf_le_left : W y (hW' hy) ⊓ W' ≤ W y (hW' hy)) (hW y (hW' hy)), e,
    res_sum_mul, res_sum_mul]
  exact sum_mul_eq_of_isRep μ hker ((hc y (hW' hy)).res inf_le_left) (hc'.res inf_le_right) k

include hgen in
lemma IsTauValue.unique {k : Fin r} {V : Opens Y}
    {u : X.presheaf.obj (op ((Opens.map f.base).obj V))} {t t' : Y.presheaf.obj (op V)}
    (h : IsTauValue b μ k u t) (h' : IsTauValue b μ k u t') : t = t' :=
  res_eq_of_locally fun y hy ↦ by
    obtain ⟨W, hW, hyW, c, hc⟩ := exists_isRep hgen u hy
    exact ⟨W, hW, hyW, (h W hW c hc).trans (h' W hW c hc).symm⟩

include hker in
/-- `IsTauValue` can be checked on local representations. -/
lemma IsTauValue.of_local {k : Fin r} {V : Opens Y}
    {u : X.presheaf.obj (op ((Opens.map f.base).obj V))} {t : Y.presheaf.obj (op V)}
    (h : ∀ y ∈ V, ∃ (W : Opens Y) (hW : W ≤ V), y ∈ W ∧ ∃ c, IsRep f b u hW c ∧
      Y.res hW t = ∑ j, c j * Y.res le_top (μ k j)) : IsTauValue b μ k u t := by
  intro W' hW' c' hc'
  refine res_eq_of_locally fun y hy ↦ ?_
  obtain ⟨W, hW, hyW, c, hc, e⟩ := h y (hW' hy)
  refine ⟨W ⊓ W', inf_le_right, ⟨hyW, hy⟩, ?_⟩
  rw [res_res, ← res_res _ (inf_le_left : W ⊓ W' ≤ W) hW, e, res_sum_mul, res_sum_mul]
  exact sum_mul_eq_of_isRep μ hker (hc.res inf_le_left) (hc'.res inf_le_right) k

include hgen hker in
lemma IsTauValue.add {k : Fin r} {V : Opens Y}
    {u u' : X.presheaf.obj (op ((Opens.map f.base).obj V))} {t t' : Y.presheaf.obj (op V)}
    (h : IsTauValue b μ k u t) (h' : IsTauValue b μ k u' t') :
    IsTauValue b μ k (u + u') (t + t') := by
  refine IsTauValue.of_local μ hker fun y hy ↦ ?_
  obtain ⟨W₁, h₁, hy₁, c₁, hc₁⟩ := exists_isRep hgen u hy
  obtain ⟨W₂, h₂, hy₂, c₂, hc₂⟩ := exists_isRep hgen u' hy
  have e₁ := h _ _ _ (hc₁.res (inf_le_left : W₁ ⊓ W₂ ≤ W₁))
  have e₂ := h' _ _ _ (hc₂.res (inf_le_right : W₁ ⊓ W₂ ≤ W₂))
  refine ⟨W₁ ⊓ W₂, inf_le_left.trans h₁, ⟨hy₁, hy₂⟩, _,
    (hc₁.res inf_le_left).add (hc₂.res inf_le_right), ?_⟩
  rw [show Y.res (inf_le_left.trans h₁ : W₁ ⊓ W₂ ≤ V) (t + t') =
    Y.res (inf_le_left.trans h₁ : W₁ ⊓ W₂ ≤ V) t + Y.res (inf_le_left.trans h₁) t' from
    map_add _ _ _, e₁, e₂, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ ↦ (add_mul _ _ _).symm

include hgen hker in
lemma IsTauValue.mul {k : Fin r} {V : Opens Y}
    {u : X.presheaf.obj (op ((Opens.map f.base).obj V))} {t : Y.presheaf.obj (op V)}
    (h : IsTauValue b μ k u t) (a : Y.presheaf.obj (op V)) :
    IsTauValue b μ k (f.cApp V a * u) (a * t) := by
  refine IsTauValue.of_local μ hker fun y hy ↦ ?_
  obtain ⟨W, hW, hyW, c, hc⟩ := exists_isRep hgen u hy
  refine ⟨W, hW, hyW, _, hc.mul a, ?_⟩
  rw [res_mul, h W hW c hc, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ ↦ (mul_assoc _ _ _).symm

include hgen hker in
lemma IsTauValue.res {k : Fin r} {V : Opens Y}
    {u : X.presheaf.obj (op ((Opens.map f.base).obj V))} {t : Y.presheaf.obj (op V)}
    (h : IsTauValue b μ k u t) {V' : Opens Y} (hV' : V' ≤ V) :
    IsTauValue b μ k (X.res ((Opens.map f.base).monotone hV') u) (Y.res hV' t) := by
  refine IsTauValue.of_local μ hker fun y hy ↦ ?_
  obtain ⟨W, hW, hyW, c, hc⟩ := exists_isRep hgen u (hV' hy)
  have hc' := hc.res (inf_le_left : W ⊓ V' ≤ W)
  refine ⟨W ⊓ V', inf_le_right, ⟨hyW, hy⟩, fun j ↦ Y.res (inf_le_left : W ⊓ V' ≤ W) (c j), ?_, ?_⟩
  · unfold IsRep at hc' ⊢
    rw [res_res]
    exact hc'
  · rw [res_res]
    exact h _ _ _ hc'

/-- The value of the `k`-th functional. -/
def tau (k : Fin r) {V : Opens Y} (u : X.presheaf.obj (op ((Opens.map f.base).obj V))) :
    Y.presheaf.obj (op V) :=
  (exists_isTauValue μ hker hgen k u).choose

lemma tau_spec (k : Fin r) {V : Opens Y} (u : X.presheaf.obj (op ((Opens.map f.base).obj V))) :
    IsTauValue b μ k u (tau μ hker hgen k u) :=
  (exists_isTauValue μ hker hgen k u).choose_spec

variable (hsep : ∀ (y : Y) (c : Fin m → Y.presheaf.stalk y),
    (∀ k, ∑ j, c j * Y.presheaf.germ ⊤ y trivial (μ k j) = 0) →
      ∑ j, f.stalkAlgMap y (c j) * f.pgerm ⊤ trivial (b j) = 0)

include hsep in
lemma eq_zero_of_forall_tau_eq_zero {V : Opens Y}
    (u : X.presheaf.obj (op ((Opens.map f.base).obj V))) (h : ∀ k, tau μ hker hgen k u = 0) :
    u = 0 := by
  -- the germs of `u` vanish
  have hgerm : ∀ y (hy : y ∈ V), f.pgerm V hy u = 0 := by
    intro y hy
    obtain ⟨W, hW, hyW, c, hc⟩ := exists_isRep hgen u hy
    have hs := hsep y (fun j ↦ Y.presheaf.germ W y hyW (c j)) fun k ↦ by
      have e := tau_spec μ hker hgen k u W hW c hc
      rw [h k, res_zero] at e
      have e' := congrArg (Y.presheaf.germ W y hyW) e
      rw [map_zero, map_sum] at e'
      refine Eq.trans (Finset.sum_congr rfl fun j _ ↦ ?_) e'.symm
      exact ((map_mul _ _ _).trans (congrArg (HMul.hMul _) (germ_res le_top y hyW _))).symm
    unfold IsRep at hc
    refine (germ_res_pushforward f hW hyW u).symm.trans ((congrArg (f.pgerm W hyW) hc).trans ?_)
    refine (map_sum _ _ _).trans (Eq.trans (Finset.sum_congr rfl fun j _ ↦ ?_) hs)
    exact (pgerm_mul_cApp f W hyW _ _).trans
      (congrArg (HMul.hMul _) (germ_res_pushforward f le_top hyW _))
  refine res_eq_of_locally fun x hx ↦ ?_
  obtain ⟨W, hW, hyW, e⟩ := (pgerm_eq_zero_iff f V hx u).1 (hgerm _ hx)
  exact ⟨_, (Opens.map f.base).monotone hW, hyW, e.trans (res_zero _ _).symm⟩

/-- **Separating functionals on `f_* 𝒪_X` from stalk data**: `τ_k (∑ⱼ cⱼ bⱼ) = ∑ⱼ cⱼ μ_{k j}`. -/
def separatingFunctionalsOfStalks : SeparatingFunctionals (pushUnit f) ⊤ where
  m := r
  τ k V _ u := tau μ hker hgen k (V := V) u
  τ_add k V _ u u' := (tau_spec μ hker hgen k (u + u' :
      X.presheaf.obj (op ((Opens.map f.base).obj V)))).unique μ hgen
    ((tau_spec μ hker hgen k u).add μ hker hgen (tau_spec μ hker hgen k u'))
  τ_smul k V _ a u := by
    let u' : X.presheaf.obj (op ((Opens.map f.base).obj V)) := u
    exact (tau_spec μ hker hgen k (f.cApp V a * u')).unique μ hgen
      ((tau_spec μ hker hgen k u').mul μ hker hgen a)
  τ_res k V _ V' _ h u := (tau_spec μ hker hgen k (X.res ((Opens.map f.base).monotone h) u :
      X.presheaf.obj (op ((Opens.map f.base).obj V')))).unique μ hgen
    ((tau_spec μ hker hgen k u).res μ hker hgen h)
  eq_zero_of_τ V _ u h := eq_zero_of_forall_tau_eq_zero μ hker hgen hsep u h

end AlgebraicGeometry.LocallyRingedSpace.Hom
