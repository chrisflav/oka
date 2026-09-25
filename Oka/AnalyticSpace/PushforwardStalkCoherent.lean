/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.AnalyticSpace.FinitePushforwardCoherent

/-!
# Coherence of `f_* 𝒪_X` from its stalks

Let `f : X ⟶ Y` be a morphism of locally ringed spaces such that `𝒪_Y` has locally finitely
generated tuple relations. Suppose that near every point of `Y` there are finitely many sections
`g₁, …, g_m` of `f_* 𝒪_X` and finitely many relations `ρ₁, …, ρ_L` between them such that, at every
nearby point `y'`, the germs of the `g_j` generate the stalk `(f_* 𝒪_X)_{y'}` over `𝒪_{Y,y'}` and
the germs of the `ρ_l` generate the relations between them. Then `f_* 𝒪_X` is coherent
(`AlgebraicGeometry.LocallyRingedSpace.Hom.isCoherent_pushUnit_of_stalks`).
-/

open CategoryTheory TopologicalSpace Opposite

universe u

noncomputable section

namespace AlgebraicGeometry.LocallyRingedSpace.Hom

variable {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y)

/-- `f^♯` on sections over `U`. -/
abbrev cApp (U : Opens Y) :
    Y.presheaf.obj (op U) →+* X.presheaf.obj (op ((Opens.map f.base).obj U)) :=
  (f.c.app (op U)).hom

lemma cApp_res {U V : Opens Y} (h : U ≤ V) (r : Y.presheaf.obj (op V)) :
    f.cApp U (Y.res h r) = X.res ((Opens.map f.base).monotone h) (f.cApp V r) :=
  c_app_res f h r

/-- The structure map `𝒪_{Y,y} → (f_* 𝒪_X)_y`. -/
abbrev stalkAlgMap (y : Y) : Y.presheaf.stalk y →+* (f.base _* X.presheaf).stalk y :=
  ((TopCat.Presheaf.stalkFunctor _ y).map f.c).hom

lemma stalkAlgMap_germ {U : Opens Y} {y : Y} (hy : y ∈ U) (r : Y.presheaf.obj (op U)) :
    f.stalkAlgMap y (Y.presheaf.germ U y hy r) =
      (f.base _* X.presheaf).germ U y hy (f.c.app (op U) r) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply U y hy f.c r

lemma germ_res_pushforward {U V : Opens Y} (h : U ≤ V) {y : Y} (hy : y ∈ U)
    (s : X.presheaf.obj (op ((Opens.map f.base).obj V))) :
    (f.base _* X.presheaf).germ U y hy (X.res ((Opens.map f.base).monotone h) s) =
      (f.base _* X.presheaf).germ V y (h hy) s :=
  TopCat.Presheaf.germ_res_apply (f.base _* X.presheaf) (homOfLE h) y hy s

/-- Sections of `f_* 𝒪_X` with equal germs agree near the point. -/
lemma exists_res_eq_of_pushforward_germ_eq {U : Opens Y} {y : Y} (hy : y ∈ U)
    (s t : X.presheaf.obj (op ((Opens.map f.base).obj U)))
    (h : (f.base _* X.presheaf).germ U y hy s = (f.base _* X.presheaf).germ U y hy t) :
    ∃ (W : Opens Y) (hW : W ≤ U), y ∈ W ∧
      X.res ((Opens.map f.base).monotone hW) s = X.res ((Opens.map f.base).monotone hW) t := by
  obtain ⟨W, hyW, iU, iV, e⟩ := TopCat.Presheaf.germ_eq (f.base _* X.presheaf) y hy hy s t h
  obtain rfl : iU = iV := Subsingleton.elim _ _
  exact ⟨W, leOfHom iU, hyW, e⟩

/-- Sections of `𝒪_Y` with equal germs agree near the point. -/
lemma _root_.AlgebraicGeometry.LocallyRingedSpace.exists_res_eq_of_germ_eq {U : Opens Y}
    {y : Y} (hy : y ∈ U) (s t : Y.presheaf.obj (op U))
    (h : Y.presheaf.germ U y hy s = Y.presheaf.germ U y hy t) :
    ∃ (W : Opens Y) (hW : W ≤ U), y ∈ W ∧ Y.res hW s = Y.res hW t := by
  obtain ⟨W, hyW, iU, iV, e⟩ := TopCat.Presheaf.germ_eq Y.presheaf y hy hy s t h
  obtain rfl : iU = iV := Subsingleton.elim _ _
  exact ⟨W, leOfHom iU, hyW, e⟩

variable {W : Opens Y} {m : ℕ} (g : Fin m → X.presheaf.obj (op ((Opens.map f.base).obj W)))

/-- The germs of the `g j` generate the stalks of `f_* 𝒪_X` at all points of `W`. -/
def StalkGenerates : Prop :=
  ∀ (y : Y) (hy : y ∈ W) (z : (f.base _* X.presheaf).stalk y), ∃ r : Fin m → Y.presheaf.stalk y,
    z = ∑ j, f.stalkAlgMap y (r j) * (f.base _* X.presheaf).germ W y hy (g j)

/-- The germs of the `ρ l` generate the relations between the germs of the `g j` at all points of
`W`. -/
def StalkRelations {L : ℕ} (ρ : Fin L → Fin m → Y.presheaf.obj (op W)) : Prop :=
  ∀ (y : Y) (hy : y ∈ W) (r : Fin m → Y.presheaf.stalk y),
    ∑ j, f.stalkAlgMap y (r j) * (f.base _* X.presheaf).germ W y hy (g j) = 0 →
      ∃ c : Fin L → Y.presheaf.stalk y, ∀ j, r j = ∑ l, c l * Y.presheaf.germ W y hy (ρ l j)

/-- **Local generation from stalks.** -/
lemma exists_eq_sum_of_stalkGenerates (hg : StalkGenerates f g) {W' : Opens Y} (hW' : W' ≤ W)
    (t : X.presheaf.obj (op ((Opens.map f.base).obj W'))) {y : Y} (hy : y ∈ W') :
    ∃ (W'' : Opens Y) (h : W'' ≤ W'), y ∈ W'' ∧ ∃ c : Fin m → Y.presheaf.obj (op W''),
      X.res ((Opens.map f.base).monotone h) t = ∑ j, f.cApp W'' (c j) *
        X.res ((Opens.map f.base).monotone (h.trans hW')) (g j) := by
  obtain ⟨r, hr⟩ := hg y (hW' hy) ((f.base _* X.presheaf).germ W' y hy t)
  choose U hyU ρ hρ using fun j ↦ Y.presheaf.exists_germ_eq (r j)
  obtain ⟨W₁, hyW₁, hW₁⟩ := exists_open_forall Y y (fun j V ↦ V ≤ U j)
    (fun _ _ _ h₁ h₂ ↦ h₁.trans h₂) fun j ↦ ⟨U j, hyU j, le_rfl⟩
  let W₂ := W₁ ⊓ W'
  have h₂ : W₂ ≤ W' := inf_le_right
  have hy₂ : y ∈ W₂ := ⟨hyW₁, hy⟩
  have h₂U : ∀ j, W₂ ≤ U j := fun j ↦ inf_le_left.trans (hW₁ j)
  have key : (f.base _* X.presheaf).germ W₂ y hy₂ (X.res ((Opens.map f.base).monotone h₂) t) =
      (f.base _* X.presheaf).germ W₂ y hy₂
        (show X.presheaf.obj (op ((Opens.map f.base).obj W₂)) from
          ∑ j, f.cApp W₂ (Y.res (h₂U j) (ρ j)) *
            X.res ((Opens.map f.base).monotone (h₂.trans hW')) (g j)) := by
    rw [germ_res_pushforward f h₂, hr]
    erw [map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    erw [map_mul]
    rw [germ_res_pushforward f (h₂.trans hW'), ← hρ j]
    congr 1
    rw [← TopCat.Presheaf.germ_res_apply Y.presheaf (homOfLE (h₂U j)) y hy₂ (ρ j)]
    exact stalkAlgMap_germ f _ _
  obtain ⟨W₃, h₃, hy₃, e⟩ := f.exists_res_eq_of_pushforward_germ_eq hy₂ _ _ key
  refine ⟨W₃, h₃.trans h₂, hy₃, fun j ↦ Y.res (h₃.trans (h₂U j)) (ρ j), ?_⟩
  rw [← res_res _ ((Opens.map f.base).monotone h₃) ((Opens.map f.base).monotone h₂), e]
  simp only [res_sum, res_mul, res_res, cApp_res]

/-- **Coherence of `f_* 𝒪_X` from its stalks.** -/
theorem isCoherent_pushUnit_of_stalks
    (hY : HasLocalTupleRelations (SheafOfModules.unit Y.ringSheaf))
    (h : ∀ y : Y, ∃ (W : Opens Y) (m L : ℕ)
      (g : Fin m → X.presheaf.obj (op ((Opens.map f.base).obj W)))
      (ρ : Fin L → Fin m → Y.presheaf.obj (op W)), y ∈ W ∧
      (∀ l, ∑ j, f.cApp W (ρ l j) * g j = 0) ∧ StalkGenerates f g ∧
      StalkRelations f g ρ) :
    (pushUnit f).IsCoherent := by
  classical
  refine isCoherent_of_hasLocalModuleRelations _ (fun y ↦ ?_) fun V k t y hy ↦ ?_
  · obtain ⟨W, m, L, g, ρ, hyW, -, hg, -⟩ := h y
    refine ⟨W, m, g, hyW, fun W' hW' t y' hy' ↦ ?_⟩
    obtain ⟨W'', h'', hy'', c, hc⟩ := exists_eq_sum_of_stalkGenerates f g hg hW' t hy'
    exact ⟨W'', h'', hy'', c, hc⟩
  obtain ⟨W, m, L, g, ρ, hyW, hρ, hg, hrel⟩ := h y
  -- coefficients of the `t i` near `y`
  let P : Fin k → Opens Y → Prop := fun i W₀ ↦ ∃ (h₀ : W₀ ≤ W ⊓ V)
    (r : Fin m → Y.presheaf.obj (op W₀)),
    X.res ((Opens.map f.base).monotone (h₀.trans inf_le_right)) (t i) =
      ∑ j, f.cApp W₀ (r j) *
        X.res ((Opens.map f.base).monotone (h₀.trans inf_le_left)) (g j)
  have hPmono : ∀ i W₀ W₁, W₁ ≤ W₀ → P i W₀ → P i W₁ := by
    rintro i W₀ W₁ hle ⟨h₀, r, hr⟩
    refine ⟨hle.trans h₀, fun j ↦ Y.res hle (r j), ?_⟩
    rw [← res_res _ ((Opens.map f.base).monotone hle)
      ((Opens.map f.base).monotone (h₀.trans inf_le_right)), hr]
    simp only [res_sum, res_mul, res_res, cApp_res]
  obtain ⟨W₀, hyW₀, hP⟩ := exists_open_forall Y y P hPmono fun i ↦ by
    obtain ⟨W'', h'', hy'', c, hc⟩ := exists_eq_sum_of_stalkGenerates f g hg
      (inf_le_left : W ⊓ V ≤ W) (X.res ((Opens.map f.base).monotone
        (inf_le_right : W ⊓ V ≤ V)) (t i)) ⟨hyW, hy⟩
    refine ⟨W'', hy'', h'', c, ?_⟩
    rw [← hc, res_res]
  let W₁ := W₀ ⊓ (W ⊓ V)
  have hP₁ : ∀ i, P i W₁ := fun i ↦ hPmono i _ _ inf_le_left (hP i)
  choose h₁ r hr using hP₁
  have h₁W : W₁ ≤ W := inf_le_right.trans inf_le_left
  have h₁V : W₁ ≤ V := inf_le_right.trans inf_le_right
  let v : Fin (k + L) → Fin m → Y.presheaf.obj (op W₁) :=
    Fin.append r fun l j ↦ Y.res h₁W (ρ l j)
  have hr' : ∀ i, X.res ((Opens.map f.base).monotone h₁V) (t i) =
      ∑ j, f.cApp W₁ (r i j) * X.res ((Opens.map f.base).monotone h₁W) (g j) := hr
  refine exists_localRelations_of_tuple hY (pushUnit f) t h₁V ⟨hyW₀, hyW, hy⟩
    (fun i j ↦ (show (SheafOfModules.unit Y.ringSheaf).val.obj (op W₁) from v i j)) ?_ ?_
  · intro W' h' b hb
    have hb' : ∀ j, ∑ i, b (Fin.castAdd L i) * Y.res h' (r i j) =
        -∑ l, b (Fin.natAdd k l) * Y.res (h'.trans h₁W) (ρ l j) := by
      intro j
      have hj := hb j
      change ∑ i, b i * Y.res h' (v i j) = 0 at hj
      rw [Fin.sum_univ_add] at hj
      simp only [v, Fin.append_left, Fin.append_right, res_res] at hj
      exact eq_neg_of_add_eq_zero_left hj
    change ∑ i, f.cApp W' (b (Fin.castAdd L i)) *
      X.res ((Opens.map f.base).monotone (h'.trans h₁V)) (t i) = 0
    have e₁ : ∀ i, X.res ((Opens.map f.base).monotone (h'.trans h₁V)) (t i) =
        ∑ j, f.cApp W' (Y.res h' (r i j)) *
          X.res ((Opens.map f.base).monotone (h'.trans h₁W)) (g j) := fun i ↦ by
      rw [← res_res _ ((Opens.map f.base).monotone h') ((Opens.map f.base).monotone h₁V), hr',
        res_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [res_mul, res_res, cApp_res]
    simp only [e₁, Finset.mul_sum]
    rw [Finset.sum_comm]
    have e₂ : ∀ j, ∑ i, f.cApp W' (b (Fin.castAdd L i)) *
        (f.cApp W' (Y.res h' (r i j)) *
          X.res ((Opens.map f.base).monotone (h'.trans h₁W)) (g j)) =
        -∑ l, f.cApp W' (b (Fin.natAdd k l)) *
          (X.res ((Opens.map f.base).monotone (h'.trans h₁W))
            (f.cApp W (ρ l j)) *
          X.res ((Opens.map f.base).monotone (h'.trans h₁W)) (g j)) := fun j ↦ by
      calc _ = f.cApp W' (∑ i, b (Fin.castAdd L i) * Y.res h' (r i j)) *
            X.res ((Opens.map f.base).monotone (h'.trans h₁W)) (g j) := by
            simp only [map_sum, map_mul, Finset.sum_mul, mul_assoc]
        _ = f.cApp W' (-∑ l, b (Fin.natAdd k l) * Y.res (h'.trans h₁W) (ρ l j)) *
            X.res ((Opens.map f.base).monotone (h'.trans h₁W)) (g j) := by rw [hb' j]
        _ = _ := by
            simp only [map_neg, map_sum, map_mul, neg_mul, Finset.sum_mul, cApp_res, mul_assoc]
    simp only [e₂, Finset.sum_neg_distrib, neg_eq_zero]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun l _ ↦ ?_
    simp only [← Finset.mul_sum, ← res_mul, ← res_sum, hρ l, res_zero, mul_zero]
  · intro W' h' a ha y' hy'
    change ∑ i, f.cApp W' (a i) *
      X.res ((Opens.map f.base).monotone (h'.trans h₁V)) (t i) = 0 at ha
    let s : Fin m → Y.presheaf.obj (op W') := fun j ↦ ∑ i, a i * Y.res h' (r i j)
    have hs : ∑ j, f.cApp W' (s j) *
        X.res ((Opens.map f.base).monotone (h'.trans h₁W)) (g j) = 0 := by
      rw [← ha]
      simp only [s, map_sum, map_mul, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [← res_res _ ((Opens.map f.base).monotone h') ((Opens.map f.base).monotone h₁V), hr',
        res_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [res_mul, res_res, ← cApp_res, mul_assoc]
    have hy'W : y' ∈ W := h₁W (h' hy')
    have hgerm : ∑ j, f.stalkAlgMap y' (Y.presheaf.germ W' y' hy' (s j)) *
        (f.base _* X.presheaf).germ W y' hy'W (g j) = 0 := by
      have := congrArg ((f.base _* X.presheaf).germ W' y' hy') hs
      erw [map_sum, map_zero] at this
      rw [← this]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [stalkAlgMap_germ]
      erw [map_mul]
      rw [germ_res_pushforward f (h'.trans h₁W)]
      rfl
    obtain ⟨c, hc⟩ := hrel y' hy'W _ hgerm
    choose U hyU γ hγ using fun l ↦ Y.presheaf.exists_germ_eq (c l)
    obtain ⟨W₂, hyW₂, hW₂⟩ := exists_open_forall Y y' (fun l V ↦ V ≤ U l)
      (fun _ _ _ h₁ h₂ ↦ h₁.trans h₂) fun l ↦ ⟨U l, hyU l, le_rfl⟩
    let W₃ := W₂ ⊓ W'
    have h₃ : W₃ ≤ W' := inf_le_right
    have h₃U : ∀ l, W₃ ≤ U l := fun l ↦ inf_le_left.trans (hW₂ l)
    have hy₃ : y' ∈ W₃ := ⟨hyW₂, hy'⟩
    let Q : Fin m → Opens Y → Prop := fun j V ↦ ∃ hV : V ≤ W₃,
      Y.res (hV.trans h₃) (s j) =
        ∑ l, Y.res (hV.trans (h₃U l)) (γ l) * Y.res (hV.trans (h₃.trans (h'.trans h₁W))) (ρ l j)
    obtain ⟨W₄, hyW₄, hQ⟩ := exists_open_forall Y y' Q (fun j V V' hle ⟨hV, hj⟩ ↦
      ⟨hle.trans hV, by
        rw [← res_res _ hle (hV.trans h₃), hj, res_sum]
        simp only [res_mul, res_res]⟩) fun j ↦ by
      obtain ⟨V, hV, hyV, e⟩ := LocallyRingedSpace.exists_res_eq_of_germ_eq hy₃ (Y.res h₃ (s j))
        (∑ l, Y.res (h₃U l) (γ l) * Y.res (h₃.trans (h'.trans h₁W)) (ρ l j)) (by
          erw [TopCat.Presheaf.germ_res_apply Y.presheaf (homOfLE h₃) y' hy₃]
          rw [hc j]
          erw [map_sum]
          refine Finset.sum_congr rfl fun l _ ↦ ?_
          erw [map_mul]
          rw [← hγ l]
          erw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply])
      refine ⟨V, hyV, hV, ?_⟩
      rw [← res_res _ hV h₃, e, res_sum]
      simp only [res_mul, res_res]
    let W₅ := W₄ ⊓ W₃
    have h₅ : W₅ ≤ W₃ := inf_le_right
    have hQ₅ : ∀ j, Q j W₅ := fun j ↦ by
      obtain ⟨hV, hj⟩ := hQ j
      refine ⟨h₅, ?_⟩
      rw [← res_res _ (inf_le_left : W₅ ≤ W₄) (hV.trans h₃), hj, res_sum]
      simp only [res_mul, res_res]
    refine ⟨W₅, h₅.trans h₃, ⟨hyW₄, hy₃⟩, fun l ↦ -Y.res (h₅.trans (h₃U l)) (γ l), fun j ↦ ?_⟩
    change ∑ i, Fin.append (fun i ↦ Y.res (h₅.trans h₃) (a i))
      (fun l ↦ -Y.res (h₅.trans (h₃U l)) (γ l)) i * Y.res ((h₅.trans h₃).trans h') (v i j) = 0
    rw [Fin.sum_univ_add]
    simp only [v, Fin.append_left, Fin.append_right, res_res, neg_mul, Finset.sum_neg_distrib,
      ← sub_eq_add_neg, sub_eq_zero]
    obtain ⟨hV₅, hj⟩ := hQ₅ j
    simp only [s, res_sum, res_mul, res_res] at hj
    exact hj

end AlgebraicGeometry.LocallyRingedSpace.Hom
