/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.AlgebraicGeometry.ProjectiveSpace.SerreFiniteness
import Oka.AlgebraicGeometry.Modules.CoherentPushforward
import Oka.AlgebraicGeometry.IdempotentMod
import Oka.RingTheory.AdicCompletion.FiniteComplete
import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# Zariski's connectedness theorem for projective schemes over a complete DVR

Let `R` be a complete discrete valuation ring and `X ⊆ ℙⁿ_R` an integral closed subscheme
dominating `Spec R`. Then the special fibre of `X → Spec R` is connected.

The proof is the degree-zero case of the theorem on formal functions, in Čech form. Write `T` for
the image of a uniformizer `t` in `Γ(X, ⊤)` and `Z = V(T)`. A splitting `Z = Z₁ ⊔ Z₂` gives on
every affine chart `Vᵢ = X ∩ D₊(xᵢ)` idempotents modulo `Tⁿ` (`Scheme.exists_isIdemMod`), unique
modulo `Tⁿ` (`Scheme.IsIdemMod.sub_mem`), hence Čech `0`-cochains `xₙ` of `𝒪_X` with
`d xₙ ∈ Tⁿ Č¹` and `xₙ ≡ x₁ mod T`. The Čech cohomology `Ȟ¹(𝒪_X)` is a finite `R`-module
(Serre, `ProjectiveSpace.cechFinite_of_isCoherent`), so its `t`-power torsion is killed by some
`t^N`; this lets one correct `x₁` by a multiple of `T` to a cocycle, i.e. a global function `g`
with `g² ≡ g mod T` and `g` nontrivial modulo `T`. As `Γ(X, 𝒪_X)` is a domain finite over the
complete ring `R`, this contradicts `eq_zero_or_eq_one_mod_of_finite`.
-/

universe u

open CategoryTheory Limits TopologicalSpace Opposite IsLocalRing
open AlgebraicGeometry.Scheme.Modules
open scoped AlgebraicGeometry.ProjectiveSpace

namespace AlgebraicGeometry.ProjectiveSpace

variable {R : Type u} [CommRing R] {n : ℕ} {X : Scheme.{u}} (i : X ⟶ ℙ(n; R))

local notation "U" => stdCover n R

local notation "ρ" => globalRingHom n R

/-- The pushforward `i_* 𝒪_X` as an `𝒪_{ℙⁿ}`-module. -/
noncomputable abbrev pushO : ℙ(n; R).Modules :=
  (SheafOfModules.pushforward.{u} i.toLRSHom.toRingSheafHom).obj (SheafOfModules.unit _)

/-- The constant `r`, as a global function on `X`. -/
noncomputable abbrev constX (r : R) : Γ(X, ⊤) := i.appTop (ρ r)

/-- The preimage in `X` of a Čech open of the standard cover. -/
noncomputable abbrev cechOpenX {q : ℕ} (σ : Fin (q + 1) → ULift.{u} (Fin (n + 1))) : X.Opens :=
  i ⁻¹ᵁ TopCat.Presheaf.cechOpen U σ

lemma isAffineOpen_cechOpenX [IsClosedImmersion i] {q : ℕ}
    (σ : Fin (q + 1) → ULift.{u} (Fin (n + 1))) : IsAffineOpen (cechOpenX i σ) :=
  (isAffineOpen_cechOpen_stdCover σ).preimage i

lemma cechSmul_pushO_apply (r : R) (q : ℕ) (y : (cech U (pushO i)).X q)
    (σ : Fin (q + 1) → ULift.{u} (Fin (n + 1))) :
    (((Scheme.Modules.cechSmul U (pushO i) (ρ r)).f q y : TopCat.Presheaf.CechCochain U
      ((SheafOfModules.toSheaf _).obj (pushO i)).obj q) σ : Γ(X, cechOpenX i σ)) =
      (constX i r |_ cechOpenX i σ) * (show Γ(X, cechOpenX i σ) from
        (y : TopCat.Presheaf.CechCochain U
          ((SheafOfModules.toSheaf _).obj (pushO i)).obj q) σ) := by
  change i.app _ (ρ r |_ TopCat.Presheaf.cechOpen U σ) * _ = _
  rw [Scheme.Hom.app_restrictOpen]
  rfl


/-! ### Multiplication by `T` is injective -/

section Injective

variable [IsIntegral X] {T : Γ(X, ⊤)}

lemma mul_restrict_injective (hgen : genericPoint X ∈ X.basicOpen T) (V : X.Opens)
    (s : Γ(X, V)) (hs : (T |_ V) * s = 0) : s = 0 := by
  rcases V.1.eq_empty_or_nonempty with h | h
  · have hV : V = ⊥ := SetLike.ext' h
    haveI : Subsingleton Γ(X, V) :=
      CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty hV)
    exact Subsingleton.elim _ _
  · haveI : Nonempty V := by simpa using h
    refine (mul_eq_zero.mp hs).resolve_left fun h0 => ?_
    have hgV : genericPoint X ∈ V := ((genericPoint_spec X).mem_open_set_iff V.isOpen).mpr
      (by simpa using h)
    have : genericPoint X ∈ X.basicOpen (T |_ V) :=
      (Scheme.mem_basicOpen_restrict_iff hgV).2 hgen
    rw [h0, Scheme.basicOpen_zero] at this
    exact this

end Injective


/-! ### The idempotent cochains -/

section Idem

variable [IsClosedImmersion i] {t : R} {Z₁ Z₂ : Set X}
  (hZ₁ : IsClosed Z₁) (hZ₂ : IsClosed Z₂) (hdisj : Disjoint Z₁ Z₂)
  (hcov : ∀ x, x ∉ X.basicOpen (constX i t) → x ∈ Z₁ ∨ x ∈ Z₂)

include hZ₁ hZ₂ hdisj hcov in
lemma exists_isIdemMod_cechOpenX {q : ℕ} (σ : Fin (q + 1) → ULift.{u} (Fin (n + 1))) {m : ℕ}
    (hm : 1 ≤ m) :
    ∃ e : Γ(X, cechOpenX i σ), Scheme.IsIdemMod Z₁ (constX i t |_ cechOpenX i σ) m e :=
  Scheme.exists_isIdemMod hZ₁ hZ₂ hdisj (isAffineOpen_cechOpenX i σ) _
    (fun x hx hxT => hcov x fun h => hxT ((Scheme.mem_basicOpen_restrict_iff hx).2 h)) hm

/-- The Čech `0`-cochain of `i_* 𝒪_X` given by `tᵐ`-idempotents for `Z₁` on the charts. -/
noncomputable def idemCochain {m : ℕ} (hm : 1 ≤ m) : (cech U (pushO i)).X 0 :=
  (fun σ => (exists_isIdemMod_cechOpenX i hZ₁ hZ₂ hdisj hcov σ hm).choose :
    TopCat.Presheaf.CechCochain U ((SheafOfModules.toSheaf _).obj (pushO i)).obj 0)

lemma idemCochain_spec {m : ℕ} (hm : 1 ≤ m) (σ : Fin 1 → ULift.{u} (Fin (n + 1))) :
    Scheme.IsIdemMod Z₁ (constX i t |_ cechOpenX i σ) m
      (show Γ(X, cechOpenX i σ) from (idemCochain i hZ₁ hZ₂ hdisj hcov hm :
        TopCat.Presheaf.CechCochain U ((SheafOfModules.toSheaf _).obj (pushO i)).obj 0) σ) :=
  (exists_isIdemMod_cechOpenX i hZ₁ hZ₂ hdisj hcov σ hm).choose_spec

/-- Restrictions of the components of `idemCochain` are `tᵐ`-idempotents. -/
lemma idemCochain_res {m : ℕ} (hm : 1 ≤ m) {q : ℕ} (τ : Fin (q + 1) → ULift.{u} (Fin (n + 1)))
    (σ : Fin 1 → ULift.{u} (Fin (n + 1)))
    (h : TopCat.Presheaf.cechOpen U τ ≤ TopCat.Presheaf.cechOpen U σ) :
    Scheme.IsIdemMod Z₁ (constX i t |_ cechOpenX i τ) m
      (X.presheaf.map (homOfLE (i.preimage_mono h)).op
        (show Γ(X, cechOpenX i σ) from (idemCochain i hZ₁ hZ₂ hdisj hcov hm :
          TopCat.Presheaf.CechCochain U ((SheafOfModules.toSheaf _).obj (pushO i)).obj 0) σ)) := by
  have := (idemCochain_spec i hZ₁ hZ₂ hdisj hcov hm σ).res (i.preimage_mono h)
  have hT : X.presheaf.map (homOfLE (i.preimage_mono h)).op (constX i t |_ cechOpenX i σ) =
      constX i t |_ cechOpenX i τ := TopCat.Presheaf.restrict_restrict _ _ _
  rwa [hT] at this

omit [IsClosedImmersion i] in
lemma constX_pow_restrict (r : R) (k : ℕ) (V : X.Opens) :
    constX i (r ^ k) |_ V = (constX i r |_ V) ^ k := by
  simp only [constX, map_pow, TopCat.Presheaf.restrictOpen, TopCat.Presheaf.restrict]

include hZ₁ hZ₂ hdisj hcov in
lemma idemCochain_d {m : ℕ} (hm : 1 ≤ m) :
    ∃ y, (cech U (pushO i)).d 0 1 (idemCochain i hZ₁ hZ₂ hdisj hcov hm) =
      (Scheme.Modules.cechSmul U (pushO i) (ρ (t ^ m))).f 1 y := by
  have key (τ : Fin 2 → ULift.{u} (Fin (n + 1))) : ∃ c : Γ(X, cechOpenX i τ),
      (((cech U (pushO i)).d 0 1 (idemCochain i hZ₁ hZ₂ hdisj hcov hm) :
        TopCat.Presheaf.CechCochain U ((SheafOfModules.toSheaf _).obj (pushO i)).obj 1) τ :
          Γ(X, cechOpenX i τ)) = (constX i t |_ cechOpenX i τ) ^ m * c := by
    have h0 := idemCochain_res i hZ₁ hZ₂ hdisj hcov hm τ (τ ∘ Fin.succAbove 0)
      (TopCat.Presheaf.cechOpen_le_comp U τ _)
    have h1 := idemCochain_res i hZ₁ hZ₂ hdisj hcov hm τ (τ ∘ Fin.succAbove 1)
      (TopCat.Presheaf.cechOpen_le_comp U τ _)
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (h0.sub_mem (isAffineOpen_cechOpenX i τ) hm h1)
    refine ⟨c, ?_⟩
    rw [mul_comm, hc]
    refine (TopCat.Presheaf.cechComplex_d_apply U _ 0 _ τ).trans ?_
    refine (TopCat.Presheaf.cechD_apply U _ 0 _ τ).trans ?_
    refine (Fin.sum_univ_two _).trans ?_
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul,
      ← sub_eq_add_neg]
    rfl
  choose c hc using key
  refine ⟨(c : TopCat.Presheaf.CechCochain U ((SheafOfModules.toSheaf _).obj (pushO i)).obj 1),
    ?_⟩
  funext τ
  rw [hc τ, cechSmul_pushO_apply, constX_pow_restrict]

include hZ₁ hZ₂ hdisj hcov in
lemma idemCochain_sub {M : ℕ} (hM : 1 ≤ M) :
    ∃ w, idemCochain i hZ₁ hZ₂ hdisj hcov hM - idemCochain i hZ₁ hZ₂ hdisj hcov le_rfl =
      (Scheme.Modules.cechSmul U (pushO i) (ρ t)).f 0 w := by
  have key (σ : Fin 1 → ULift.{u} (Fin (n + 1))) : ∃ c : Γ(X, cechOpenX i σ),
      (show Γ(X, cechOpenX i σ) from (idemCochain i hZ₁ hZ₂ hdisj hcov hM :
        TopCat.Presheaf.CechCochain U ((SheafOfModules.toSheaf _).obj (pushO i)).obj 0) σ) -
      (show Γ(X, cechOpenX i σ) from (idemCochain i hZ₁ hZ₂ hdisj hcov le_rfl :
        TopCat.Presheaf.CechCochain U ((SheafOfModules.toSheaf _).obj (pushO i)).obj 0) σ) =
        (constX i t |_ cechOpenX i σ) * c := by
    have h0 := (idemCochain_spec i hZ₁ hZ₂ hdisj hcov hM σ).mono hM
    have h1 := idemCochain_spec i hZ₁ hZ₂ hdisj hcov (le_refl 1) σ
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp
      (h0.sub_mem (isAffineOpen_cechOpenX i σ) le_rfl h1)
    exact ⟨c, by rw [← hc, pow_one, mul_comm]⟩
  choose c hc using key
  refine ⟨(c : TopCat.Presheaf.CechCochain U ((SheafOfModules.toSheaf _).obj (pushO i)).obj 0),
    ?_⟩
  funext σ
  rw [cechSmul_pushO_apply, ← hc σ]
  rfl

end Idem


/-! ### Local lemmas -/

lemma _root_.AlgebraicGeometry.Scheme.mem_basicOpen_one_sub_mul {Y : Scheme.{u}} {V : Y.Opens}
    {τ : Γ(Y, V)} (w : Γ(Y, V)) {x : Y} (hx : x ∈ V) (hτ : x ∉ Y.basicOpen τ) :
    x ∈ Y.basicOpen (1 - τ * w) := by
  rw [Scheme.mem_basicOpen _ _ _ hx] at hτ ⊢
  rw [map_sub, map_one, map_mul]
  exact IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _
    ((mem_nonunits_iff.mpr hτ) |> fun h => mul_mem_nonunits_left h)

lemma _root_.AlgebraicGeometry.Scheme.not_mem_basicOpen_mul {Y : Scheme.{u}} {V : Y.Opens}
    {τ : Γ(Y, V)} (w : Γ(Y, V)) {x : Y} (hτ : x ∉ Y.basicOpen τ) :
    x ∉ Y.basicOpen (τ * w) := by
  rw [Scheme.basicOpen_mul]
  exact fun h => hτ h.1

/-! ### The main argument -/

section Main

variable [IsClosedImmersion i] [IsIntegral X] {t : R}

omit [IsClosedImmersion i] in
/-- A global section of `𝒪_X` which is locally a multiple of `T` on every chart is globally a
multiple of `T`, if `T` is a nonzerodivisor. -/
lemma exists_eq_mul_of_forall_cechOpenX (hgen : genericPoint X ∈ X.basicOpen (constX i t))
    (s : Γ(X, ⊤)) (hs : ∀ σ : Fin 1 → ULift.{u} (Fin (n + 1)), ∃ c : Γ(X, cechOpenX i σ),
      s |_ cechOpenX i σ = (constX i t |_ cechOpenX i σ) * c) :
    ∃ b : Γ(X, ⊤), s = constX i t * b := by
  let G := (SheafOfModules.toSheaf _).obj (pushO i)
  have hW : ∀ j, U j ≤ ⊤ := fun _ => le_top
  have hcov : (⊤ : ℙ(n; R).Opens) ≤ ⨆ j, U j := (iSup_stdCover n R).ge
  choose c hc using hs
  let cb : (cech U (pushO i)).X 0 :=
    (c : TopCat.Presheaf.CechCochain U G.obj 0)
  have hsc : (Scheme.Modules.cechSmul U (pushO i) (ρ t)).f 0 cb =
      TopCat.Presheaf.cechAugment U G.obj hW (show Γ(pushO i, ⊤) from s) := by
    funext σ
    rw [cechSmul_pushO_apply, ← hc σ]
    rfl
  have hdc : TopCat.Presheaf.cechD U G.obj 0 cb = 0 := by
    have h1 :
        (Scheme.Modules.cechSmul U (pushO i) (ρ t)).f 1 ((cech U (pushO i)).d 0 1 cb) = 0 := by
      rw [← cechSmul_f_comm, hsc]
      exact (funext (TopCat.Presheaf.cechComplex_d_apply U G.obj 0 _)).trans
        (TopCat.Presheaf.cechD_cechAugment U G.obj hW _)
    have h2 : (cech U (pushO i)).d 0 1 cb = 0 := by
      funext τ
      have := congrFun h1 τ
      rw [cechSmul_pushO_apply] at this
      exact mul_restrict_injective hgen _ _ this
    exact (funext (TopCat.Presheaf.cechComplex_d_apply U G.obj 0 cb)).symm.trans h2
  obtain ⟨b, hb⟩ := TopCat.Presheaf.exists_cechAugment_eq U hW G hcov cb hdc
  refine ⟨(show Γ(X, ⊤) from b), TopCat.Presheaf.cechAugment_injective U hW G hcov ?_⟩
  change TopCat.Presheaf.cechAugment U G.obj hW (show Γ(pushO i, ⊤) from s) =
    TopCat.Presheaf.cechAugment U G.obj hW
      (show Γ(pushO i, ⊤) from constX i t * (show Γ(X, ⊤) from b))
  rw [← hsc, ← hb]
  funext σ
  rw [cechSmul_pushO_apply]
  change _ = TopCat.Presheaf.restrictOpen (F := X.presheaf)
    (constX i t * (show Γ(X, ⊤) from b)) (cechOpenX i σ) le_top
  simp only [TopCat.Presheaf.restrictOpen, TopCat.Presheaf.restrict, map_mul]
  rfl

/-- The `R`-algebra structure on `Γ(X, ⊤)` through `X → ℙⁿ_R → Spec R`. -/
noncomputable abbrev algebraX : Algebra R Γ(X, ⊤) :=
  (i.appTop.hom.comp (globalRingHom n R)).toAlgebra

variable [IsDomain R] [IsDiscreteValuationRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R]

/-- **Zariski's connectedness theorem, splitting form.** Let `X ⊆ ℙⁿ_R` be an integral closed
subscheme over a complete DVR `R` with uniformizer `t`, such that `t` does not vanish at the
generic point. Then the zero locus of `t` on `X` admits no splitting into two disjoint nonempty
closed pieces. -/
theorem not_split (ht : Irreducible t) (hgen : genericPoint X ∈ X.basicOpen (constX i t))
    {Z₁ Z₂ : Set X} (hZ₁ : IsClosed Z₁) (hZ₂ : IsClosed Z₂) (hdisj : Disjoint Z₁ Z₂)
    (hcov : ∀ x, x ∉ X.basicOpen (constX i t) → x ∈ Z₁ ∨ x ∈ Z₂)
    (hne₁ : ∃ x ∈ Z₁, x ∉ X.basicOpen (constX i t))
    (hne₂ : ∃ x ∈ Z₂, x ∉ X.basicOpen (constX i t)) : False := by
  set T := constX i t with hTdef
  let K := cech U (pushO i)
  haveI : IsLocallyNoetherian ℙ(n; R) := LocallyOfFiniteType.isLocallyNoetherian (toSpec n R)
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (i ≫ toSpec n R)
  haveI : (SheafOfModules.unit X.toLocallyRingedSpace.ringSheaf).IsCoherent :=
    X.isCoherentStructureSheaf
  haveI : (pushO i).IsCoherent := isCoherent_pushforward_of_isClosedImmersion i _
  have h0 := cechFinite_of_isCoherent (pushO i) 0
  have h1 := cechFinite_of_isCoherent (pushO i) 1
  obtain ⟨N, hN⟩ := CechFinite.exists_pow_smul_eq_d (p := 0) U ρ h1 t
  -- `t` acts injectively on cochains
  have hinj : ∀ (q k : ℕ) (z : K.X q),
      (Scheme.Modules.cechSmul U (pushO i) (ρ (t ^ k))).f q z = 0 → z = 0 := by
    have hpowinj : ∀ (V : X.Opens) (k : ℕ) (s : Γ(X, V)), (T |_ V) ^ k * s = 0 → s = 0 := by
      intro V k
      induction k with
      | zero => intro s h; simpa using h
      | succ k ih =>
        intro s h
        rw [pow_succ', mul_assoc] at h
        exact ih _ (mul_restrict_injective hgen _ _ h)
    intro q k z hz
    funext σ
    have h := congrFun hz σ
    rw [cechSmul_pushO_apply, constX_pow_restrict] at h
    exact hpowinj _ k _ h
  -- the chase
  obtain ⟨a, hda, z, hz⟩ := exists_cocycle_sub_eq_smul U ρ t N (hinj 2) hN
    (idemCochain i hZ₁ hZ₂ hdisj hcov (le_refl 1))
    (idemCochain i hZ₁ hZ₂ hdisj hcov (Nat.le_add_left 1 N))
    (idemCochain_d i hZ₁ hZ₂ hdisj hcov _) (idemCochain_sub i hZ₁ hZ₂ hdisj hcov _)
  -- the cocycle `a` is a global function `g`
  let G := (SheafOfModules.toSheaf _).obj (pushO i)
  have hW : ∀ j, U j ≤ ⊤ := fun _ => le_top
  have hcovP : (⊤ : ℙ(n; R).Opens) ≤ ⨆ j, U j := (iSup_stdCover n R).ge
  obtain ⟨g', hg'⟩ := TopCat.Presheaf.exists_cechAugment_eq U hW G hcovP a
    ((funext (TopCat.Presheaf.cechComplex_d_apply U G.obj 0 a)).symm.trans hda)
  let g : Γ(X, ⊤) := g'
  set x₁ := idemCochain i hZ₁ hZ₂ hdisj hcov (le_refl 1)
  have hloc (σ : Fin 1 → ULift.{u} (Fin (n + 1))) :
      (show Γ(X, cechOpenX i σ) from
        (x₁ : TopCat.Presheaf.CechCochain U G.obj 0) σ) =
        g |_ cechOpenX i σ + (T |_ cechOpenX i σ) *
          (show Γ(X, cechOpenX i σ) from (z : TopCat.Presheaf.CechCochain U G.obj 0) σ) := by
    have h := congrFun hz σ
    rw [cechSmul_pushO_apply] at h
    have ha : (show Γ(X, cechOpenX i σ) from (a : TopCat.Presheaf.CechCochain U G.obj 0) σ) =
        g |_ cechOpenX i σ := by
      rw [← hg']
      rfl
    rw [← ha, ← h]
    change _ = _ + ((x₁ : TopCat.Presheaf.CechCochain U G.obj 0) σ -
      (a : TopCat.Presheaf.CechCochain U G.obj 0) σ)
    abel
  -- `g² ≡ g mod T`
  obtain ⟨b, hb⟩ := exists_eq_mul_of_forall_cechOpenX i hgen (g * g - g) fun σ => by
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp
      (idemCochain_spec i hZ₁ hZ₂ hdisj hcov (le_refl 1) σ).1
    set e := (show Γ(X, cechOpenX i σ) from (x₁ : TopCat.Presheaf.CechCochain U G.obj 0) σ)
    set w := (show Γ(X, cechOpenX i σ) from (z : TopCat.Presheaf.CechCochain U G.obj 0) σ)
    refine ⟨c - w * (2 * e - 1) + (T |_ cechOpenX i σ) * w * w, ?_⟩
    have hres : (g * g - g) |_ cechOpenX i σ =
        g |_ cechOpenX i σ * g |_ cechOpenX i σ - g |_ cechOpenX i σ := by
      simp only [TopCat.Presheaf.restrictOpen, TopCat.Presheaf.restrict, map_mul, map_sub]
    rw [hres]
    have he := hloc σ
    rw [pow_one] at hc
    linear_combination
      (-(g |_ cechOpenX i σ + e - (T |_ cechOpenX i σ) * w - 1)) * he - hc
  -- `Γ(X, 𝒪_X)` is a finite `R`-algebra
  letI := algebraX i
  have hfin : Module.Finite R Γ(X, ⊤) := by
    letI := Scheme.Modules.sectionsModule ρ (pushO i)
    have h0' := (cechFinite_zero_iff U ρ (iSup_stdCover n R) (pushO i)).1 h0
    let φ : Γ(pushO i, ⊤) →ₗ[R] Γ(X, ⊤) :=
      { toFun := fun s => s
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    exact Module.Finite.of_surjective φ fun s => ⟨s, rfl⟩
  have hmax : (IsLocalRing.maximalIdeal R).map (algebraMap R Γ(X, ⊤)) = Ideal.span {T} := by
    rw [ht.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
    rfl
  have hgg : g * g - g ∈ (IsLocalRing.maximalIdeal R).map (algebraMap R Γ(X, ⊤)) := by
    rw [hmax, hb]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  -- a chart through a point
  have hchart (x : X) : ∃ σ : Fin 1 → ULift.{u} (Fin (n + 1)), x ∈ cechOpenX i σ := by
    have hx : i x ∈ ⨆ j, U j := hcovP trivial
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    refine ⟨fun _ => j, ?_⟩
    change i x ∈ TopCat.Presheaf.cechOpen U (fun _ : Fin 1 => j)
    rw [TopCat.Presheaf.cechOpen_const]
    exact hj
  rcases eq_zero_or_eq_one_mod_of_finite g hgg with hg | hg
  · obtain ⟨x, hxZ, hxT⟩ := hne₁
    obtain ⟨σ, hxσ⟩ := hchart x
    rw [hmax] at hg
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hg
    have hx1 : x ∈ X.basicOpen (show Γ(X, cechOpenX i σ) from
        (x₁ : TopCat.Presheaf.CechCochain U G.obj 0) σ) :=
      ((idemCochain_spec i hZ₁ hZ₂ hdisj hcov (le_refl 1) σ).2 x hxσ
        fun h => hxT ((Scheme.mem_basicOpen_restrict_iff hxσ).1 h)).2 hxZ
    rw [hloc σ] at hx1
    have : g |_ cechOpenX i σ = (T |_ cechOpenX i σ) * (c |_ cechOpenX i σ) := by
      rw [← hc, mul_comm]
      simp only [TopCat.Presheaf.restrictOpen, TopCat.Presheaf.restrict, map_mul]
    rw [this, ← mul_add] at hx1
    exact Scheme.not_mem_basicOpen_mul _
      (fun h => hxT ((Scheme.mem_basicOpen_restrict_iff hxσ).1 h)) hx1
  · obtain ⟨x, hxZ, hxT⟩ := hne₂
    obtain ⟨σ, hxσ⟩ := hchart x
    rw [hmax] at hg
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hg
    have hxT' : x ∉ X.basicOpen (T |_ cechOpenX i σ) :=
      fun h => hxT ((Scheme.mem_basicOpen_restrict_iff hxσ).1 h)
    have hx1 : x ∈ X.basicOpen (show Γ(X, cechOpenX i σ) from
        (x₁ : TopCat.Presheaf.CechCochain U G.obj 0) σ) ↔ x ∈ Z₁ :=
      (idemCochain_spec i hZ₁ hZ₂ hdisj hcov (le_refl 1) σ).2 x hxσ hxT'
    have hgσ : g |_ cechOpenX i σ = 1 - (T |_ cechOpenX i σ) * (c |_ cechOpenX i σ) := by
      have : g = 1 - c * T := by rw [hc]; ring
      rw [this, mul_comm]
      simp only [TopCat.Presheaf.restrictOpen, TopCat.Presheaf.restrict, map_mul, map_sub,
        map_one]
    rw [hloc σ, hgσ] at hx1
    have hmem : x ∈ X.basicOpen (1 - (T |_ cechOpenX i σ) *
        (c |_ cechOpenX i σ - (show Γ(X, cechOpenX i σ) from
          (z : TopCat.Presheaf.CechCochain U G.obj 0) σ))) :=
      Scheme.mem_basicOpen_one_sub_mul _ hxσ hxT'
    have heq : (1 - (T |_ cechOpenX i σ) * (c |_ cechOpenX i σ) + (T |_ cechOpenX i σ) *
        (show Γ(X, cechOpenX i σ) from (z : TopCat.Presheaf.CechCochain U G.obj 0) σ)) =
        1 - (T |_ cechOpenX i σ) * (c |_ cechOpenX i σ - (show Γ(X, cechOpenX i σ) from
          (z : TopCat.Presheaf.CechCochain U G.obj 0) σ)) := by ring
    rw [heq] at hx1
    exact hdisj.ne_of_mem (hx1.1 hmem) hxZ rfl

omit [IsIntegral X] [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [IsClosedImmersion i] in
/-- The constant `t` (a uniformizer) is a unit at `x` iff `x` is not in the special fibre. -/
lemma mem_basicOpen_constX_iff (ht : Irreducible t) (x : X) :
    x ∈ X.basicOpen (constX i t) ↔ (i ≫ toSpec n R) x ≠ closedPoint R := by
  have h1 : X.basicOpen (constX i t) =
      (i ≫ toSpec n R) ⁻¹ᵁ (Spec (.of R)).basicOpen ((Scheme.ΓSpecIso (.of R)).inv t) := by
    rw [Scheme.preimage_basicOpen]
    rfl
  rw [h1, basicOpen_eq_of_affine]
  change (i ≫ toSpec n R) x ∈ PrimeSpectrum.basicOpen t ↔ _
  generalize (i ≫ toSpec n R) x = p
  constructor
  · rintro hp rfl
    exact (PrimeSpectrum.mem_basicOpen _ _).1 hp
      ((IsLocalRing.mem_maximalIdeal t).mpr ht.not_isUnit)
  · intro hp
    refine (PrimeSpectrum.mem_basicOpen _ _).2 fun htp => ?_
    apply hp
    have hne : p.asIdeal ≠ ⊥ := fun h => ht.ne_zero (by simpa [h] using htp)
    have hmax : p.asIdeal.IsMaximal := _root_.IsPrime.to_maximal_ideal hne
    exact PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal hmax)

end Main

/-- **Zariski's connectedness theorem** for projective schemes over a complete discrete valuation
ring. Let `X ⊆ ℙⁿ_R` be an integral closed subscheme whose generic point lies over the generic
point of `Spec R`. Then the special fibre of `X → Spec R` is preconnected. -/
theorem isPreconnected_closedFibre [IsDomain R] [IsDiscreteValuationRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [IsClosedImmersion i] [IsIntegral X]
    (hgen : (i ≫ toSpec n R) (genericPoint X) ≠ closedPoint R) :
    _root_.IsPreconnected ((i ≫ toSpec n R) ⁻¹' {closedPoint R}) := by
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hZ : (i ≫ toSpec n R) ⁻¹' {closedPoint R} = (X.basicOpen (constX i t) : Set X)ᶜ := by
    ext x
    exact ⟨fun h hb => (mem_basicOpen_constX_iff i ht x).1 hb h,
      fun h => by_contra fun hn => h ((mem_basicOpen_constX_iff i ht x).2 hn)⟩
  have hZc : IsClosed ((i ≫ toSpec n R) ⁻¹' {closedPoint R}) := by
    rw [hZ]
    exact (X.basicOpen (constX i t)).isOpen.isClosed_compl
  rw [isPreconnected_closed_iff]
  intro u v hu hv hsuv hsu hsv
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  set Z := (i ≫ toSpec n R) ⁻¹' {closedPoint R}
  have hZmem (x : X) : x ∈ Z ↔ x ∉ X.basicOpen (constX i t) := by
    rw [hZ]
    rfl
  refine not_split i ht ((mem_basicOpen_constX_iff i ht _).2 hgen) (hZc.inter hu)
    (hZc.inter hv) ?_ ?_ ?_ ?_
  · rw [Set.disjoint_iff]
    rintro x ⟨⟨hxZ, hxu⟩, ⟨-, hxv⟩⟩
    exact (Set.eq_empty_iff_forall_notMem.mp hne) x ⟨hxZ, hxu, hxv⟩
  · intro x hx
    have hxZ := (hZmem x).2 hx
    rcases hsuv hxZ with h | h
    · exact Or.inl ⟨hxZ, h⟩
    · exact Or.inr ⟨hxZ, h⟩
  · obtain ⟨x, hxZ, hxu⟩ := hsu
    exact ⟨x, ⟨hxZ, hxu⟩, (hZmem x).1 hxZ⟩
  · obtain ⟨x, hxZ, hxv⟩ := hsv
    exact ⟨x, ⟨hxZ, hxv⟩, (hZmem x).1 hxZ⟩

end AlgebraicGeometry.ProjectiveSpace
