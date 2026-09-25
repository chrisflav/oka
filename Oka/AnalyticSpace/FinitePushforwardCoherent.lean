/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.AnalyticSpace.LocalTupleRelations
import Oka.Geometry.RingedSpace.LocallyRingedSpace.CoherentPushforwardClosedEmbedding
import Oka.Geometry.RingedSpace.LocallyRingedSpace.CocycleTwist
import Oka.Analytification.RET.ES.FinitePushforward

/-!
# Pushforward of coherent sheaves along maps with finite fibres

Let `f : X ⟶ Y` be a morphism of locally ringed spaces whose underlying map is closed with finite
fibres, with `X` Hausdorff. If `f_* 𝒪_X` is a coherent `𝒪_Y`-module, then `f_* M` is coherent for
every coherent `𝒪_X`-module `M`
(`AlgebraicGeometry.LocallyRingedSpace.Hom.isCoherent_pushforward_of_isClosedMap`).

Near a point `y ∈ Y`, the fibre `f⁻¹ y` has pairwise disjoint neighbourhoods whose union
contains `f⁻¹ V` for a neighbourhood `V` of `y`, since `f` is closed
(`AlgebraicGeometry.LocallyRingedSpace.Hom.exists_fibre_cover`). Local generators and local
relations of `M` near the points of the fibre therefore glue to generators and relations of `f_* M`
as a module over `f_* 𝒪_X`, and these give generators and relations over `𝒪_Y` because
`f_* 𝒪_X` is locally finitely generated with locally finitely generated tuple relations
(`AlgebraicGeometry.LocallyRingedSpace.HasLocalModuleRelations.hasLocalTupleRelations`).
-/

open CategoryTheory TopologicalSpace Opposite

universe u

noncomputable section

namespace AlgebraicGeometry.LocallyRingedSpace

variable {X Y : LocallyRingedSpace.{u}}

/-! ### Gluing sections over disjoint opens -/

section Glue

variable (N : SheafOfModules.{u} X.ringSheaf) {ι : Type*} {W : Opens X} (O : ι → Opens X)
  (hO : ∀ i, O i ≤ W) (hW : W ≤ ⨆ i, O i)

include hW in
/-- Sections over `W` agreeing on a cover of `W` are equal. -/
lemma sectRes_ext (s t : N.val.obj (op W)) (h : ∀ i, sectRes N (hO i) s = sectRes N (hO i) t) :
    s = t :=
  modRes_eq_of_cover N O hW hO s t h

include hW in
/-- **Gluing over pairwise disjoint opens.** -/
lemma exists_sectRes_eq_of_disjoint (hdisj : ∀ i j, i ≠ j → O i ⊓ O j = ⊥)
    (s : ∀ i, N.val.obj (op (O i))) : ∃ t : N.val.obj (op W), ∀ i, sectRes N (hO i) t = s i := by
  classical
  obtain ⟨t, ht, -⟩ := modRes_existsUnique_gluing N O hW hO s fun a b ↦ by
    by_cases hab : a = b
    · subst hab
      rfl
    · have := subsingleton_val_obj_of_eq_bot N (hdisj a b hab)
      exact @Subsingleton.elim _ this _ _
  exact ⟨t, ht⟩

include hW in
/-- **Extension by zero** over pairwise disjoint opens. -/
lemma exists_extend_zero (hdisj : ∀ i j, i ≠ j → O i ⊓ O j = ⊥) (i₀ : ι)
    (s : N.val.obj (op (O i₀))) : ∃ t : N.val.obj (op W),
      sectRes N (hO i₀) t = s ∧ ∀ i, i ≠ i₀ → sectRes N (hO i) t = 0 := by
  classical
  obtain ⟨t, ht⟩ := exists_sectRes_eq_of_disjoint N O hO hW hdisj (Pi.single i₀ s)
  exact ⟨t, (ht i₀).trans (Pi.single_eq_same _ _), fun i hi ↦ (ht i).trans
    (Pi.single_eq_of_ne hi _)⟩

end Glue

/-! ### Neighbourhoods of fibres -/

namespace Hom

variable (f : X ⟶ Y)

/-- **Separating a fibre**: for a closed map with Hausdorff source, the points of a finite fibre
over `y` have pairwise disjoint neighbourhoods, inside given ones, covering `f⁻¹ V` for a
neighbourhood `V ≤ W` of `y`. -/
lemma exists_fibre_cover [T2Space X.toPresheafedSpace] (hf : IsClosedMap f.base) {y : Y}
    (hfin : (f.base ⁻¹' {y}).Finite) {W : Opens Y} (hyW : y ∈ W)
    (U : f.base ⁻¹' {y} → Opens X) (hU : ∀ x, x.1 ∈ U x) :
    ∃ (V : Opens Y) (O : f.base ⁻¹' {y} → Opens X), V ≤ W ∧ y ∈ V ∧ (∀ x, x.1 ∈ O x) ∧
      (∀ x, O x ≤ U x) ∧ (∀ x, O x ≤ (Opens.map f.base).obj V) ∧
      (∀ x x', x ≠ x' → O x ⊓ O x' = ⊥) ∧ (Opens.map f.base).obj V ≤ ⨆ x, O x := by
  obtain ⟨D, hD, hdisj⟩ := hfin.t2_separation
  let O₁ : f.base ⁻¹' {y} → Opens X := fun x ↦ U x ⊓ ⟨D x.1, (hD x.1).2⟩
  obtain ⟨V₁, hyV, hVO⟩ := hf.exists_preimage_le (⨆ x, O₁ x) fun x hx ↦
    Opens.mem_iSup.2 ⟨⟨x, hx⟩, hU _, (hD x).1⟩
  let V := V₁ ⊓ W
  refine ⟨V, fun x ↦ O₁ x ⊓ (Opens.map f.base).obj V, inf_le_right, ⟨hyV, hyW⟩,
    fun x ↦ ⟨⟨hU x, (hD x.1).1⟩, ?_⟩, fun x ↦ inf_le_left.trans inf_le_left,
    fun x ↦ inf_le_right, fun x x' hxx' ↦ ?_, fun z hz ↦ ?_⟩
  · change f.base x.1 ∈ V
    rw [show f.base x.1 = y from x.2]
    exact ⟨hyV, hyW⟩
  · refine eq_bot_iff.2 fun z hz ↦ ?_
    exact (hdisj x.2 x'.2 (fun h ↦ hxx' (Subtype.ext h))).le_bot ⟨hz.1.1.2, hz.2.1.2⟩
  · obtain ⟨x, hx⟩ := Opens.mem_iSup.1 (hVO hz.1)
    exact Opens.mem_iSup.2 ⟨x, hx, hz⟩

/-- **Combinations near a fibre are combinations over a neighbourhood**: if near every point of
the fibre over `y` the tuple `t` is a combination of the tuples `S l` with coefficients in `𝒪_X`,
then so it is over `f⁻¹ V` for a neighbourhood `V` of `y`. -/
theorem exists_combination_of_fibre [T2Space X.toPresheafedSpace] (hf : IsClosedMap f.base)
    {y : Y} (hfin : (f.base ⁻¹' {y}).Finite) (N : SheafOfModules.{u} X.ringSheaf) {W : Opens Y}
    {κ : Type*} [Fintype κ] {m : ℕ} (t : Fin m → N.val.obj (op ((Opens.map f.base).obj W)))
    (S : κ → Fin m → N.val.obj (op ((Opens.map f.base).obj W))) (hy : y ∈ W)
    (h : ∀ x ∈ f.base ⁻¹' {y}, ∃ (U : Opens X) (hU : U ≤ (Opens.map f.base).obj W), x ∈ U ∧
      ∃ c : κ → X.presheaf.obj (op U), ∀ j, sectRes N hU (t j) = ∑ l, c l • sectRes N hU (S l j)) :
    ∃ (V : Opens Y) (hV : V ≤ W), y ∈ V ∧
      ∃ C : κ → X.presheaf.obj (op ((Opens.map f.base).obj V)), ∀ j,
        sectRes N ((Opens.map f.base).monotone hV) (t j) =
          ∑ l, C l • sectRes N ((Opens.map f.base).monotone hV) (S l j) := by
  choose U hUW hxU c hc using fun x : f.base ⁻¹' {y} ↦ h x.1 x.2
  obtain ⟨V, O, hVW, hyV, hxO, hOU, hOV, hdisj, hcov⟩ := exists_fibre_cover f hf hfin hy U hxU
  choose C hC using fun l : κ ↦ exists_sectRes_eq_of_disjoint
    (SheafOfModules.unit X.ringSheaf) O hOV hcov hdisj
    (fun x ↦ (show X.presheaf.obj (op _) from X.res (hOU x) (c x l)))
  refine ⟨V, hVW, hyV, C, fun j ↦ ?_⟩
  refine sectRes_ext N _ hOV hcov _ _ fun x ↦ ?_
  have e₁ := congrArg (sectRes N (hOU x)) (hc x j)
  rw [sectRes_sectRes, sectRes_sum] at e₁
  rw [sectRes_sectRes, e₁, sectRes_sum]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [sectRes_smul, sectRes_smul, sectRes_sectRes, sectRes_sectRes]
  congr 1
  exact (hC l x).symm

/-! ### Generators of `f_* M` -/

variable (M : SheafOfModules.{u} X.ringSheaf)

/-- `f_* 𝒪_X`. -/
abbrev pushUnit : SheafOfModules.{u} Y.ringSheaf :=
  (SheafOfModules.pushforward.{u} f.toRingSheafHom).obj (SheafOfModules.unit X.ringSheaf)

/-- **Local generators of `f_* M`**: if `f_* 𝒪_X` and `M` are locally finitely generated, so is
`f_* M`. -/
theorem isLocallyFinitelyGeneratedModule_pushforward_of_isClosedMap [T2Space X.toPresheafedSpace]
    (hf : IsClosedMap f.base) (hfin : ∀ y, (f.base ⁻¹' {y}).Finite)
    (hA : IsLocallyFinitelyGeneratedModule (pushUnit f))
    (hM : IsLocallyFinitelyGeneratedModule M) :
    IsLocallyFinitelyGeneratedModule ((SheafOfModules.pushforward.{u} f.toRingSheafHom).obj M) := by
  classical
  intro y
  obtain ⟨WA, p, α, hyWA, hαgen⟩ := hA y
  haveI := (hfin y).fintype
  choose U k s hxU hsgen using fun x : f.base ⁻¹' {y} ↦ hM x.1
  obtain ⟨V, O, hVW, hyV, hxO, hOU, hOV, hdisj, hcov⟩ :=
    exists_fibre_cover f hf (hfin y) hyWA U hxU
  let κ := Σ x : f.base ⁻¹' {y}, Fin (k x)
  choose S hS hS0 using fun a : κ ↦
    exists_extend_zero M O hOV hcov hdisj a.1 (sectRes M (hOU a.1) (s a.1 a.2))
  let ι := Fin p × κ
  let e := Fintype.equivFin ι
  let G : ι → M.val.obj (op ((Opens.map f.base).obj V)) := fun b ↦
    X.res ((Opens.map f.base).monotone hVW) (α b.1) • S b.2
  refine ⟨V, Fintype.card ι, fun l ↦ G (e.symm l), hyV, fun W' hW' t y' hy' ↦ ?_⟩
  have hW'V : (Opens.map f.base).obj W' ≤ (Opens.map f.base).obj V :=
    (Opens.map f.base).monotone hW'
  -- Step 1: a combination of the `S a` with coefficients in `𝒪_X`
  obtain ⟨V₁, hV₁, hy'V₁, C, hC⟩ := exists_combination_of_fibre f hf (hfin y') M (m := 1)
    (fun _ ↦ (show M.val.obj (op ((Opens.map f.base).obj W')) from t))
    (fun a _ ↦ sectRes M hW'V (S a)) hy' fun x' hx' ↦ by
      have hx'V : x' ∈ (Opens.map f.base).obj V := hW'V (show f.base x' ∈ W' by
        rw [show f.base x' = y' from hx']; exact hy')
      obtain ⟨x, hx⟩ := Opens.mem_iSup.1 (hcov hx'V)
      have hW₀ : O x ⊓ (Opens.map f.base).obj W' ≤ U x := inf_le_left.trans (hOU x)
      obtain ⟨W₁, hW₁, hx'W₁, cx, hcx⟩ := hsgen x (O x ⊓ (Opens.map f.base).obj W') hW₀
        (sectRes M inf_le_right t) x' ⟨hx, show f.base x' ∈ W' by
          rw [show f.base x' = y' from hx']; exact hy'⟩
      refine ⟨W₁, hW₁.trans inf_le_right, hx'W₁,
        fun a ↦ if h : a.1 = x then cx (Fin.cast (by rw [h]) a.2) else 0, fun _ ↦ ?_⟩
      rw [sectRes_sectRes] at hcx
      rw [hcx, Fintype.sum_sigma, Finset.sum_eq_single x]
      · refine Finset.sum_congr rfl fun l _ ↦ ?_
        dsimp only
        rw [dif_pos rfl, Fin.cast_eq_self, sectRes_sectRes]
        have e₂ := congrArg (sectRes M (hW₁.trans inf_le_left)) (hS ⟨x, l⟩)
        rw [sectRes_sectRes, sectRes_sectRes] at e₂
        rw [e₂]
      · intro x'' _ hx''
        refine Finset.sum_eq_zero fun l _ ↦ ?_
        dsimp only
        rw [dif_neg hx'', zero_smul]
      · simp
  -- Step 2: the coefficients are combinations of the generators `α` of `f_* 𝒪_X`
  let P : κ → Opens Y → Prop := fun a V'' ↦ ∃ (h : V'' ≤ V₁) (d : Fin p → Y.presheaf.obj (op V'')),
    sectRes (pushUnit f) h (show (pushUnit f).val.obj (op V₁) from C a) =
      ∑ l, d l • sectRes (pushUnit f) (h.trans (hV₁.trans (hW'.trans hVW))) (α l)
  have hPmono : ∀ a V'' V''', V''' ≤ V'' → P a V'' → P a V''' := by
    rintro a V'' V''' hle ⟨h, d, hd⟩
    refine ⟨hle.trans h, fun l ↦ Y.res hle (d l), ?_⟩
    rw [← sectRes_sectRes _ hle h, hd, sectRes_sum_smul]
    simp only [sectRes_sectRes]
  obtain ⟨V₂, hy'V₂, hP⟩ := exists_open_forall Y y' P hPmono fun a ↦ by
    obtain ⟨V'', h, hy'', d, hd⟩ := hαgen V₁ (hV₁.trans (hW'.trans hVW)) (C a) y' hy'V₁
    exact ⟨V'', hy'', h, d, hd⟩
  let V₃ := V₂ ⊓ V₁
  have hP₃ : ∀ a, P a V₃ := fun a ↦ hPmono a _ _ inf_le_left (hP a)
  choose h₃ d hd using hP₃
  have h₃₁ : V₃ ≤ V₁ := inf_le_right
  refine ⟨V₃, h₃₁.trans hV₁, ⟨hy'V₂, hy'V₁⟩, fun l ↦ d (e.symm l).2 (e.symm l).1, ?_⟩
  let φ : Y.presheaf.obj (op V₃) → X.presheaf.obj (op ((Opens.map f.base).obj V₃)) :=
    fun r ↦ f.c.app (op V₃) r
  have hd' : ∀ a, X.res ((Opens.map f.base).monotone h₃₁) (C a) =
      ∑ l, φ (d a l) * X.res ((Opens.map f.base).monotone
        (h₃₁.trans (hV₁.trans (hW'.trans hVW)))) (α l) := fun a ↦ hd a
  have e1 := congrArg (sectRes M ((Opens.map f.base).monotone h₃₁)) (hC 0)
  simp only [sectRes_sectRes, sectRes_sum, sectRes_smul] at e1
  change sectRes M ((Opens.map f.base).monotone (h₃₁.trans hV₁)) t =
    ∑ l, φ (d (e.symm l).2 (e.symm l).1) •
      sectRes M ((Opens.map f.base).monotone ((h₃₁.trans hV₁).trans hW')) (G (e.symm l))
  rw [e1]
  symm
  refine (Fintype.sum_equiv e.symm _ (fun b : ι ↦ φ (d b.2 b.1) •
    sectRes M ((Opens.map f.base).monotone ((h₃₁.trans hV₁).trans hW')) (G b))
    fun _ ↦ rfl).trans ?_
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  simp only [G, hd', sectRes_smul, Finset.sum_smul, mul_smul, res_res]

/-- **Local relations of `f_* M`**: if `f_* 𝒪_X` is locally finitely generated with locally finitely
generated tuple relations, and `M` has locally finitely generated relations, then so has
`f_* M`. -/
theorem hasLocalModuleRelations_pushforward_of_isClosedMap [T2Space X.toPresheafedSpace]
    (hf : IsClosedMap f.base) (hfin : ∀ y, (f.base ⁻¹' {y}).Finite)
    (hA : IsLocallyFinitelyGeneratedModule (pushUnit f)) (hAT : HasLocalTupleRelations (pushUnit f))
    (hM : HasLocalModuleRelations M) :
    HasLocalModuleRelations ((SheafOfModules.pushforward.{u} f.toRingSheafHom).obj M) := by
  classical
  intro V m t y hy
  obtain ⟨WA, p, α, hyWA, hαgen⟩ := hA y
  haveI := (hfin y).fintype
  have hxV : ∀ x : f.base ⁻¹' {y}, x.1 ∈ (Opens.map f.base).obj V := fun x ↦
    show f.base x.1 ∈ V by rw [show f.base x.1 = y from x.2]; exact hy
  choose U hUV k g hxU hg hgcompl using fun x : f.base ⁻¹' {y} ↦
    hM ((Opens.map f.base).obj V) m t x.1 (hxV x)
  obtain ⟨V₀, O, hV₀, hyV₀, hxO, hOU, hOV, hdisj, hcov⟩ :=
    exists_fibre_cover f hf (hfin y) (show y ∈ V ⊓ WA from ⟨hy, hyWA⟩) U hxU
  have hV₀V : V₀ ≤ V := hV₀.trans inf_le_left
  have hV₀A : V₀ ≤ WA := hV₀.trans inf_le_right
  let κ := Σ x : f.base ⁻¹' {y}, Fin (k x)
  choose Gx hGx hGx0 using fun (a : κ) (j : Fin m) ↦
    exists_extend_zero (SheafOfModules.unit X.ringSheaf) O hOV hcov hdisj a.1
      (show X.presheaf.obj (op (O a.1)) from X.res (hOU a.1) (g a.1 a.2 j))
  let φ : ∀ {W : Opens Y},
      Y.presheaf.obj (op W) →+* X.presheaf.obj (op ((Opens.map f.base).obj W)) :=
    fun {W} ↦ (f.c.app (op W)).hom
  have hφres : ∀ {W W' : Opens Y} (hle : W' ≤ W) (r : Y.presheaf.obj (op W)),
      φ (Y.res hle r) = X.res ((Opens.map f.base).monotone hle) (φ r) :=
    fun hle r ↦ Hom.c_app_res f hle r
  let G : κ → Fin m → X.presheaf.obj (op ((Opens.map f.base).obj V₀)) := fun a j ↦ Gx a j
  have hG : ∀ a j, X.res (hOV a.1) (G a j) = X.res (hOU a.1) (g a.1 a.2 j) := hGx
  have hG0 : ∀ a j x, x ≠ a.1 → X.res (hOV x) (G a j) = 0 := hGx0
  -- the glued relations of `M`
  have hGrel : ∀ a : κ, ∑ j, G a j • sectRes M ((Opens.map f.base).monotone hV₀V) (t j) = 0 := by
    rintro ⟨x₀, l⟩
    refine sectRes_ext M O hOV hcov _ _ fun x ↦ ?_
    rw [sectRes_sum, sectRes_zero]
    by_cases hx : x = x₀
    · subst hx
      have e := congrArg (sectRes M (hOU x)) (hg x l)
      rw [sectRes_zero, sectRes_sum] at e
      rw [← e]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [sectRes_smul, sectRes_smul, sectRes_sectRes, sectRes_sectRes]
      congr 1
      exact hG ⟨x, l⟩ j
    · refine Finset.sum_eq_zero fun j _ ↦ ?_
      rw [sectRes_smul, hG0 ⟨x₀, l⟩ j x hx, zero_smul]
  let ι := Fin p × κ
  let e := Fintype.equivFin ι
  let v : Fin (m + Fintype.card ι) → Fin m → X.presheaf.obj (op ((Opens.map f.base).obj V₀)) :=
    Fin.append (fun i j ↦ if i = j then 1 else 0) fun ν j ↦
      X.res ((Opens.map f.base).monotone hV₀A) (α (e.symm ν).1) * G (e.symm ν).2 j
  refine exists_localRelations_of_tuple hAT _ t hV₀V hyV₀
    (fun i j ↦ (show (pushUnit f).val.obj (op V₀) from v i j)) ?_ ?_
  · intro W' h b hb
    have hb' : ∀ j, φ (b (Fin.castAdd _ j)) = -∑ ν, φ (b (Fin.natAdd m ν)) *
        (X.res ((Opens.map f.base).monotone (h.trans hV₀A)) (α (e.symm ν).1) *
          X.res ((Opens.map f.base).monotone h) (G (e.symm ν).2 j)) := by
      intro j
      have hj := hb j
      change ∑ i, φ (b i) * X.res ((Opens.map f.base).monotone h) (v i j) = 0 at hj
      rw [Fin.sum_univ_add] at hj
      simp only [v, Fin.append_left, Fin.append_right, res_mul, res_res] at hj
      rw [Finset.sum_eq_single j (fun i _ hij ↦ by rw [if_neg hij, res_zero, mul_zero])
        (by simp), if_pos rfl, show X.res ((Opens.map f.base).monotone h) 1 = 1 from map_one _,
        mul_one] at hj
      exact eq_neg_of_add_eq_zero_left hj
    change ∑ i, φ (b (Fin.castAdd _ i)) •
      sectRes M ((Opens.map f.base).monotone (h.trans hV₀V)) (t i) = 0
    simp only [hb', neg_smul, Finset.sum_neg_distrib, Finset.sum_smul, neg_eq_zero]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun ν _ ↦ ?_
    have hν := congrArg (sectRes M ((Opens.map f.base).monotone h)) (hGrel (e.symm ν).2)
    rw [sectRes_zero, sectRes_sum] at hν
    simp only [sectRes_smul, sectRes_sectRes] at hν
    simp only [mul_smul, ← Finset.smul_sum, hν, smul_zero]
  · intro W' h a ha y' hy'
    have ha' : ∑ i, φ (a i) • sectRes M ((Opens.map f.base).monotone (h.trans hV₀V)) (t i) = 0 :=
      ha
    have hW'O : (Opens.map f.base).obj W' ≤ (Opens.map f.base).obj V₀ :=
      (Opens.map f.base).monotone h
    -- Step 1: glue the local expressions of `f^♯ a` in terms of the relations of `M`
    obtain ⟨V₁, hV₁, hy'V₁, C, hC⟩ := exists_combination_of_fibre f hf (hfin y')
      (SheafOfModules.unit X.ringSheaf) (κ := κ) (m := m)
      (fun j ↦ (show X.presheaf.obj (op ((Opens.map f.base).obj W')) from φ (a j)))
      (fun a' j ↦ (show X.presheaf.obj (op ((Opens.map f.base).obj W')) from
        X.res hW'O (G a' j))) hy' fun x' hx' ↦ by
      have hx'W : x' ∈ (Opens.map f.base).obj W' := show f.base x' ∈ W' by
        rw [show f.base x' = y' from hx']; exact hy'
      obtain ⟨x, hx⟩ := Opens.mem_iSup.1 (hcov (hW'O hx'W))
      have hW₀ : O x ⊓ (Opens.map f.base).obj W' ≤ U x := inf_le_left.trans (hOU x)
      have hrel : ∑ i, X.res (inf_le_right : O x ⊓ (Opens.map f.base).obj W' ≤ _) (φ (a i)) •
          sectRes M (hW₀.trans (hUV x)) (t i) = 0 := by
        have hh := congrArg (sectRes M (inf_le_right : O x ⊓ _ ≤ _)) ha'
        rw [sectRes_zero, sectRes_sum] at hh
        simp only [sectRes_smul, sectRes_sectRes] at hh
        exact hh
      obtain ⟨W₁, hW₁, hx'W₁, cx, hcx⟩ := hgcompl x _ hW₀ _ hrel x' ⟨hx, hx'W⟩
      refine ⟨W₁, hW₁.trans inf_le_right, hx'W₁,
        fun a' ↦ if hh : a'.1 = x then cx (Fin.cast (by rw [hh]) a'.2) else 0, fun j ↦ ?_⟩
      change X.res _ (φ (a j)) = ∑ a', (if hh : a'.1 = x then cx (Fin.cast (by rw [hh]) a'.2)
        else 0) * X.res _ (X.res hW'O (G a' j))
      have hcxj := hcx j
      rw [res_res] at hcxj
      rw [hcxj, Fintype.sum_sigma, Finset.sum_eq_single x]
      · refine Finset.sum_congr rfl fun l _ ↦ ?_
        dsimp only
        rw [dif_pos rfl, Fin.cast_eq_self, res_res]
        congr 1
        have e₂ := congrArg (X.res (hW₁.trans inf_le_left)) (hG ⟨x, l⟩ j)
        rw [res_res, res_res] at e₂
        exact e₂.symm
      · intro x'' _ hx''
        refine Finset.sum_eq_zero fun l _ ↦ ?_
        dsimp only
        rw [dif_neg hx'', zero_mul]
      · simp
    -- Step 2: the coefficients are combinations of the generators `α` of `f_* 𝒪_X`
    let P : κ → Opens Y → Prop := fun a' V'' ↦ ∃ (h' : V'' ≤ V₁)
      (d : Fin p → Y.presheaf.obj (op V'')),
      sectRes (pushUnit f) h' (show (pushUnit f).val.obj (op V₁) from C a') =
        ∑ l, d l • sectRes (pushUnit f) (h'.trans (hV₁.trans (h.trans hV₀A))) (α l)
    have hPmono : ∀ a' V'' V''', V''' ≤ V'' → P a' V'' → P a' V''' := by
      rintro a' V'' V''' hle ⟨h', d, hd⟩
      refine ⟨hle.trans h', fun l ↦ Y.res hle (d l), ?_⟩
      rw [← sectRes_sectRes _ hle h', hd, sectRes_sum_smul]
      simp only [sectRes_sectRes]
    obtain ⟨V₂, hy'V₂, hP⟩ := exists_open_forall Y y' P hPmono fun a' ↦ by
      obtain ⟨V'', h', hy'', d, hd⟩ := hαgen V₁ (hV₁.trans (h.trans hV₀A)) (C a') y' hy'V₁
      exact ⟨V'', hy'', h', d, hd⟩
    let V₃ := V₂ ⊓ V₁
    have hP₃ : ∀ a', P a' V₃ := fun a' ↦ hPmono a' _ _ inf_le_left (hP a')
    choose h₃ d hd using hP₃
    have h₃₁ : V₃ ≤ V₁ := inf_le_right
    have hd' : ∀ a', X.res ((Opens.map f.base).monotone h₃₁) (C a') =
        ∑ l, φ (d a' l) * X.res ((Opens.map f.base).monotone
          (h₃₁.trans (hV₁.trans (h.trans hV₀A)))) (α l) := fun a' ↦ hd a'
    refine ⟨V₃, h₃₁.trans hV₁, ⟨hy'V₂, hy'V₁⟩, fun ν ↦ -d (e.symm ν).2 (e.symm ν).1,
      fun j ↦ ?_⟩
    change ∑ i, φ (Fin.append (fun i ↦ Y.res (h₃₁.trans hV₁) (a i))
      (fun ν ↦ -d (e.symm ν).2 (e.symm ν).1) i) *
        X.res ((Opens.map f.base).monotone ((h₃₁.trans hV₁).trans h)) (v i j) = 0
    rw [Fin.sum_univ_add]
    simp only [v, Fin.append_left, Fin.append_right, res_mul, res_res, map_neg, neg_mul,
      Finset.sum_neg_distrib]
    rw [Finset.sum_eq_single j (fun i _ hij ↦ by rw [if_neg hij, res_zero, mul_zero])
      (by simp), if_pos rfl,
      show X.res ((Opens.map f.base).monotone ((h₃₁.trans hV₁).trans h)) 1 = 1 from map_one _,
      mul_one, ← sub_eq_add_neg, sub_eq_zero]
    have hCj := congrArg (X.res ((Opens.map f.base).monotone h₃₁)) (hC j)
    change X.res _ (X.res _ (φ (a j))) = X.res _ (∑ a', C a' * X.res _ (X.res hW'O (G a' j)))
      at hCj
    rw [res_res, res_sum] at hCj
    simp only [res_mul, res_res] at hCj
    rw [hφres, hCj]
    symm
    refine (Fintype.sum_equiv e.symm _ (fun b : ι ↦ φ (d b.2 b.1) *
      (X.res ((Opens.map f.base).monotone (((h₃₁.trans hV₁).trans h).trans hV₀A)) (α b.1) *
        X.res ((Opens.map f.base).monotone ((h₃₁.trans hV₁).trans h)) (G b.2 j)))
      fun _ ↦ rfl).trans ?_
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun a' _ ↦ ?_
    rw [hd', Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [mul_assoc]

/-- **Pushforward of coherent sheaves along a closed map with finite fibres**: for `f : X ⟶ Y`
closed with finite fibres, `X` Hausdorff and `f_* 𝒪_X` coherent, `f_* M` is coherent for every
coherent `𝒪_X`-module `M`. -/
theorem isCoherent_pushforward_of_isClosedMap [T2Space X.toPresheafedSpace]
    (hf : IsClosedMap f.base) (hfin : ∀ y, (f.base ⁻¹' {y}).Finite) [(pushUnit f).IsCoherent]
    [M.IsCoherent] : ((SheafOfModules.pushforward.{u} f.toRingSheafHom).obj M).IsCoherent :=
  isCoherent_of_hasLocalModuleRelations _
    (isLocallyFinitelyGeneratedModule_pushforward_of_isClosedMap f M hf hfin
      (isLocallyFinitelyGeneratedModule_of_isFiniteType _)
      (isLocallyFinitelyGeneratedModule_of_isFiniteType M))
    (hasLocalModuleRelations_pushforward_of_isClosedMap f M hf hfin
      (isLocallyFinitelyGeneratedModule_of_isFiniteType _)
      (hasLocalModuleRelations_of_isCoherent _).hasLocalTupleRelations
      (hasLocalModuleRelations_of_isCoherent M))

end Hom

end AlgebraicGeometry.LocallyRingedSpace

namespace ComplexAnalytic.AnalyticSpace

open AlgebraicGeometry.LocallyRingedSpace

/-- **Grauert's finite mapping theorem reduces to the structure sheaf**: if `f_* 𝒪_X` is coherent
for every finite morphism `f : X ⟶ Y` with Hausdorff source, then so is `f_* M` for every coherent
`𝒪_X`-module `M`. -/
theorem finiteMappingTheorem_of_isCoherent_pushUnit
    (h : ∀ ⦃X Y : AnalyticSpace.{u}⦄ (f : X ⟶ Y) [IsFinite f] [T2Space X],
      (Hom.pushUnit f.toLRSHom).IsCoherent) :
    FiniteMappingTheorem.{u} := by
  intro X Y f _ _ M _
  haveI := h f
  exact Hom.isCoherent_pushforward_of_isClosedMap f.toLRSHom M IsFinite.isClosedMap
    fun y ↦ (haveI := IsFinite.finite_fiber (f := f) y; Set.toFinite _)

end ComplexAnalytic.AnalyticSpace
