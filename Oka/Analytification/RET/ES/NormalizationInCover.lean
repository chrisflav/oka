/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.AlgebraicGeometry.Normalization
import Oka.Analytification.RET.ES.CodimTwoAlgebra
import Oka.Analytification.RET.ES.NormalHartogs
import Oka.RingTheory.IntegralClosureEtale

/-!
# Normalisation in a finite étale cover of a big open

Let `X` be an affine scheme whose ring of functions `A` is a noetherian finite product of normal
domains, `U ⊆ X` an open whose complement has codimension at least two and `p : Y ⟶ U` finite
étale. Let `f = p ≫ U.ι` and `q : Y' ⟶ X` the relative normalisation `f.fromNormalization`. Then
`q` is finite, `Γ(Y', 𝒪)` is a finite product of normal domains, `q⁻¹ U` has complement of
codimension at least two, and `Y ≅ q⁻¹ U` over `U`. This proves
`ComplexAnalytic.NormalizationInCover` (`ComplexAnalytic.normalizationInCover`), hence
`ComplexAnalytic.mem_essImage_of_restrict'`.

## Proof

The pullback square is smooth base change of relative normalisation along `U.ι`, together with
`p` being integral (`ComplexAnalytic.isPullback_toNormalization`).

For the ring `Γ(Y', 𝒪) = integralClosure A Γ(Y, 𝒪)`, choose a nonzerodivisor `a ∈ A` with
`D(a) ⊆ U`. Then `Γ(f⁻¹ D(a), 𝒪)` is finite étale over `A_a`, so its integral closure over `A` is
finite, a finite product of normal domains and has going down over `A`
(`finite_isFiniteProductOfNormalDomains_hasGoingDown_integralClosure`). Restriction
`Γ(Y, 𝒪) → Γ(f⁻¹ D(a), 𝒪)` identifies the integral closures of `A`: this is checked on the cover
of `Y` by the affine opens `f⁻¹ D(b)`, where `D(b) ⊆ U` and `Γ(D(b), 𝒪)` is zero or a normal
domain; there `Γ(f⁻¹ D(b), 𝒪)` is étale over `Γ(D(b), 𝒪)`, hence embeds into its localisation at
`a` and contains every element of it integral over `Γ(D(b), 𝒪)`
(`injective_algebraMap_away_of_etale`, `exists_algebraMap_eq_of_isIntegral_of_etale`). Going down
bounds the heights of primes of `Γ(Y', 𝒪)` below by those of their contractions, which gives the
codimension statement.
-/

open CategoryTheory Limits Opposite AlgebraicGeometry

universe u

namespace ComplexAnalytic

/-! ### The pullback square -/

/-- **The normalisation of `X` in a scheme integral over an open `U`** restricts to it over `U`:
for `p : Y ⟶ U` integral, the square formed by `f.toNormalization`, `p`, `f.fromNormalization`
and `U.ι` is a pullback, where `f = p ≫ U.ι`. -/
lemma isPullback_toNormalization {X Y : Scheme.{u}} (U : X.Opens) (p : Y ⟶ U) [IsIntegralHom p]
    [QuasiCompact (p ≫ U.ι)] [QuasiSeparated (p ≫ U.ι)] :
    IsPullback (p ≫ U.ι).toNormalization p (p ≫ U.ι).fromNormalization U.ι := by
  have h₀ : IsPullback (𝟙 Y) p (p ≫ U.ι) U.ι := IsPullback.of_horiz_isIso_mono ⟨by simp⟩
  have hsnd : pullback.snd (p ≫ U.ι) U.ι = h₀.isoPullback.inv ≫ p := by simp
  haveI : IsIntegralHom (pullback.snd (p ≫ U.ι) U.ι) := by rw [hsnd]; infer_instance
  refine IsPullback.of_iso_pullback ⟨by simp⟩
    (h₀.isoPullback ≪≫ asIso (pullback.snd (p ≫ U.ι) U.ι).toNormalization ≪≫
      asIso ((p ≫ U.ι).normalizationPullback U.ι)) ?_ ?_
  · simp only [Iso.trans_hom, asIso_hom, Category.assoc,
      Scheme.Hom.toNormalization_normalizationPullback_fst, IsPullback.isoPullback_hom_fst_assoc,
      Category.id_comp]
  · simp only [Iso.trans_hom, asIso_hom, Category.assoc, Scheme.Hom.normalizationPullback_snd,
      Scheme.Hom.toNormalization_fromNormalization, IsPullback.isoPullback_hom_snd]

/-- For `p : Y ⟶ U` finite étale and an affine open `V ⊆ U` of `X`, the preimage of `V` in `Y`
is affine and `Γ(X, V) → Γ(Y, (p ≫ U.ι)⁻¹ V)` is finite étale. -/
lemma isAffineOpen_preimage_finite_etale_app {X Y : Scheme.{u}} {U : X.Opens} (p : Y ⟶ U)
    [IsFinite p] [Etale p] {V : X.Opens} (hV : IsAffineOpen V) (hVU : V ≤ U) :
    IsAffineOpen ((p ≫ U.ι) ⁻¹ᵁ V) ∧ ((p ≫ U.ι).app V).hom.Finite ∧
      ((p ≫ U.ι).app V).hom.Etale := by
  have hV' : IsAffineOpen (U.ι ⁻¹ᵁ V) :=
    hV.preimage_of_isOpenImmersion U.ι (by simpa using hVU)
  have haff : IsAffineOpen ((p ≫ U.ι) ⁻¹ᵁ V) := hV'.preimage p
  refine ⟨haff, ?_, ?_⟩
  · have : IsIso (U.ι.app V) := U.ι.isIso_app V (by simpa using hVU)
    rw [Scheme.Hom.comp_app]
    change ((p.app (U.ι ⁻¹ᵁ V)).hom.comp (U.ι.app V).hom).Finite
    have h₁ : (p.app (U.ι ⁻¹ᵁ V)).hom.Finite :=
      RingHom.IsIntegral.to_finite (IsIntegralHom.isIntegral_app p _ hV') (by
        have := HasRingHomProperty.appLE (P := @LocallyOfFiniteType) p inferInstance
          ⟨_, hV'⟩ ⟨_, hV'.preimage p⟩ le_rfl
        simpa [Scheme.Hom.app_eq_appLE] using this)
    exact h₁.comp (RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (U.ι.app V)).2)
  · have := HasRingHomProperty.appLE (P := @Etale) (p ≫ U.ι) inferInstance ⟨_, hV⟩ ⟨_, haff⟩
      le_rfl
    simpa [Scheme.Hom.app_eq_appLE] using this

/-! ### Integral elements over basic opens -/

section Local

variable {X Y : Scheme.{u}} (f : Y ⟶ X) (a b : Γ(X, ⊤))

/-- The hypotheses at a basic open `D(b)` of `X` for comparing sections over `f⁻¹ D(b)` with
sections over `f⁻¹ (D(b) ∩ D(a))`: the preimage `f⁻¹ D(b)` is affine,
`Γ(X, D(b)) → Γ(Y, f⁻¹ D(b))` is étale, and `Γ(X, D(b))` is zero or a normal domain in which `a`
does not vanish. -/
structure IsEtaleNormalAt : Prop where
  isAffineOpen : IsAffineOpen (f ⁻¹ᵁ X.basicOpen b)
  etale : (f.app (X.basicOpen b)).hom.Etale
  normal : Subsingleton Γ(X, X.basicOpen b) ∨ (IsDomain Γ(X, X.basicOpen b) ∧
    IsIntegrallyClosed Γ(X, X.basicOpen b) ∧
      X.presheaf.map (homOfLE (le_top : X.basicOpen b ≤ ⊤)).op a ≠ 0)

variable {f a b}

/-- Composing two restriction maps of a scheme. -/
lemma res_res_apply {Z : Scheme.{u}} {V₁ V₂ V₃ : Z.Opens} (h₁ : V₂ ≤ V₁) (h₂ : V₃ ≤ V₂)
    (s : Γ(Z, V₁)) : Z.presheaf.map (homOfLE h₂).op (Z.presheaf.map (homOfLE h₁).op s) =
      Z.presheaf.map (homOfLE (h₂.trans h₁)).op s := by
  change (Z.presheaf.map _ ≫ Z.presheaf.map _) s = _
  rw [← Functor.map_comp]
  rfl

/-- The basic open of the image of `a` in `Γ(Y, f⁻¹ D(b))` is `f⁻¹ D(b) ∩ f⁻¹ D(a)`. -/
lemma basicOpen_app_res :
    Y.basicOpen (f.app (X.basicOpen b)
      (X.presheaf.map (homOfLE (le_top : X.basicOpen b ≤ ⊤)).op a)) =
        f ⁻¹ᵁ X.basicOpen b ⊓ f ⁻¹ᵁ X.basicOpen a := by
  rw [← Scheme.Hom.preimage_basicOpen, Scheme.basicOpen_res, Scheme.Hom.preimage_inf]

/-- Restriction `Γ(Y, f⁻¹ D(b)) → Γ(Y, f⁻¹ D(b) ∩ f⁻¹ D(a))` is injective. -/
lemma injective_res_inf (h : IsEtaleNormalAt f a b) :
    Function.Injective (Y.presheaf.map (homOfLE (inf_le_left :
      f ⁻¹ᵁ X.basicOpen b ⊓ f ⁻¹ᵁ X.basicOpen a ≤ f ⁻¹ᵁ X.basicOpen b)).op) := by
  set R := Γ(X, X.basicOpen b)
  set r : R := X.presheaf.map (homOfLE (le_top : X.basicOpen b ≤ ⊤)).op a
  letI : Algebra R Γ(Y, f ⁻¹ᵁ X.basicOpen b) := (f.app (X.basicOpen b)).hom.toAlgebra
  haveI : Algebra.Etale R Γ(Y, f ⁻¹ᵁ X.basicOpen b) := h.etale
  letI := (Y.presheaf.map (homOfLE (Y.basicOpen_le (f.app (X.basicOpen b) r))).op).hom.toAlgebra
  haveI := h.isAffineOpen.isLocalization_basicOpen (f.app (X.basicOpen b) r)
  have hinj := injective_algebraMap_away_of_etale (R := R) (S := Γ(Y, f ⁻¹ᵁ X.basicOpen b))
    (Sᵣ := Γ(Y, Y.basicOpen (f.app (X.basicOpen b) r))) (r := r) h.normal
  have hle : Y.basicOpen (f.app (X.basicOpen b) r) ≤
      f ⁻¹ᵁ X.basicOpen b ⊓ f ⁻¹ᵁ X.basicOpen a := (basicOpen_app_res (a := a) (b := b)).le
  have key : ∀ s, algebraMap Γ(Y, f ⁻¹ᵁ X.basicOpen b)
      Γ(Y, Y.basicOpen (f.app (X.basicOpen b) r)) s = Y.presheaf.map (homOfLE hle).op
        (Y.presheaf.map (homOfLE (inf_le_left : f ⁻¹ᵁ X.basicOpen b ⊓ f ⁻¹ᵁ X.basicOpen a ≤
          f ⁻¹ᵁ X.basicOpen b)).op s) := fun s ↦ (res_res_apply _ _ s).symm
  intro s t hst
  apply hinj
  rw [key, key, hst]

/-- A section over `f⁻¹ D(b) ∩ f⁻¹ D(a)` integral over `Γ(X, D(b))` extends to `f⁻¹ D(b)`. -/
lemma exists_res_inf_eq (h : IsEtaleNormalAt f a b)
    (x : Γ(Y, f ⁻¹ᵁ X.basicOpen b ⊓ f ⁻¹ᵁ X.basicOpen a))
    (hx : (f.appLE (X.basicOpen b) _ inf_le_left).hom.IsIntegralElem x) :
    ∃ s : Γ(Y, f ⁻¹ᵁ X.basicOpen b), Y.presheaf.map (homOfLE (inf_le_left :
      f ⁻¹ᵁ X.basicOpen b ⊓ f ⁻¹ᵁ X.basicOpen a ≤ f ⁻¹ᵁ X.basicOpen b)).op s = x := by
  set R := Γ(X, X.basicOpen b)
  set r : R := X.presheaf.map (homOfLE (le_top : X.basicOpen b ≤ ⊤)).op a
  set Z := Y.basicOpen (f.app (X.basicOpen b) r)
  letI : Algebra R Γ(Y, f ⁻¹ᵁ X.basicOpen b) := (f.app (X.basicOpen b)).hom.toAlgebra
  haveI : Algebra.Etale R Γ(Y, f ⁻¹ᵁ X.basicOpen b) := h.etale
  letI := (Y.presheaf.map (homOfLE (Y.basicOpen_le (f.app (X.basicOpen b) r))).op).hom.toAlgebra
  haveI := h.isAffineOpen.isLocalization_basicOpen (f.app (X.basicOpen b) r)
  letI : Algebra R Γ(Y, Z) := ((algebraMap Γ(Y, f ⁻¹ᵁ X.basicOpen b) Γ(Y, Z)).comp
    (algebraMap R Γ(Y, f ⁻¹ᵁ X.basicOpen b))).toAlgebra
  haveI : IsScalarTower R Γ(Y, f ⁻¹ᵁ X.basicOpen b) Γ(Y, Z) := .of_algebraMap_eq' rfl
  have heq : Z = f ⁻¹ᵁ X.basicOpen b ⊓ f ⁻¹ᵁ X.basicOpen a := basicOpen_app_res
  have hcomp : (Y.presheaf.map (homOfLE heq.le).op).hom.comp
      (f.appLE (X.basicOpen b) _ inf_le_left).hom = algebraMap R Γ(Y, Z) := by
    rw [← CommRingCat.hom_comp, Scheme.Hom.appLE_map]
    rfl
  have hx' : IsIntegral R (Y.presheaf.map (homOfLE heq.le).op x) := by
    obtain ⟨p, hp, hpx⟩ := hx
    refine ⟨p, hp, ?_⟩
    rw [← hcomp, ← Polynomial.hom_eval₂, hpx, map_zero]
  obtain ⟨s, hs⟩ := exists_algebraMap_eq_of_isIntegral_of_etale (R := R)
    (S := Γ(Y, f ⁻¹ᵁ X.basicOpen b)) (Sᵣ := Γ(Y, Z)) (r := r) h.normal _ hx'
  refine ⟨s, ?_⟩
  have hinv : ∀ y, Y.presheaf.map (homOfLE heq.ge).op (Y.presheaf.map (homOfLE heq.le).op y) =
      y := fun y ↦ by
    rw [res_res_apply]
    exact congrArg (fun φ ↦ φ y) (congrArg CommRingCat.Hom.hom (Y.presheaf.map_id _))
  rw [← hinv x, ← hs]
  exact (res_res_apply _ _ s).symm

/-- `ComplexAnalytic.injective_res_inf` for an open equal to `f⁻¹ D(b)`. -/
lemma injective_res_of_eq (h : IsEtaleNormalAt f a b) (V : Y.Opens)
    (hV : V = f ⁻¹ᵁ X.basicOpen b) :
    Function.Injective (Y.presheaf.map (homOfLE (inf_le_left :
      V ⊓ f ⁻¹ᵁ X.basicOpen a ≤ V)).op) := by
  subst hV
  exact injective_res_inf h

variable (f a) {𝔅 : Set Γ(X, ⊤)} (hcov : ∀ y : Y, ∃ b ∈ 𝔅, f.base y ∈ X.basicOpen b)
  (hmul : ∀ b ∈ 𝔅, ∀ b' ∈ 𝔅, b * b' ∈ 𝔅) (hgood : ∀ b ∈ 𝔅, IsEtaleNormalAt f a b)

include hcov hgood in
/-- If the `f⁻¹ D(b)` for `b ∈ 𝔅` cover `Y`, restriction `Γ(Y, 𝒪) → Γ(f⁻¹ D(a), 𝒪)` is
injective. -/
lemma injective_res_preimage_basicOpen : Function.Injective (Y.presheaf.map (homOfLE (le_top :
    f ⁻¹ᵁ X.basicOpen a ≤ ⊤)).op) := by
  intro s t hst
  refine TopCat.Sheaf.eq_of_locally_eq' Y.sheaf (fun b : 𝔅 ↦ f ⁻¹ᵁ X.basicOpen b.1) ⊤
    (fun _ ↦ homOfLE le_top) (fun y _ ↦ ?_) s t fun b ↦ ?_
  · obtain ⟨b, hb, hy⟩ := hcov y
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨b, hb⟩, hy⟩
  · apply injective_res_inf (hgood b.1 b.2)
    change Y.presheaf.map _ (Y.presheaf.map _ s) = Y.presheaf.map _ (Y.presheaf.map _ t)
    rw [res_res_apply, res_res_apply,
      ← res_res_apply (le_top : f ⁻¹ᵁ X.basicOpen a ≤ ⊤) inf_le_right,
      ← res_res_apply (le_top : f ⁻¹ᵁ X.basicOpen a ≤ ⊤) inf_le_right, hst]

include hcov hmul hgood in
/-- If the `f⁻¹ D(b)` for `b ∈ 𝔅` cover `Y` and `𝔅` is closed under multiplication, every
section over `f⁻¹ D(a)` integral over `Γ(X, 𝒪)` extends to `Y`. -/
lemma exists_res_preimage_basicOpen_eq (x : Γ(Y, f ⁻¹ᵁ X.basicOpen a))
    (hx : (f.appLE ⊤ (f ⁻¹ᵁ X.basicOpen a) le_top).hom.IsIntegralElem x) :
    ∃ s : Γ(Y, ⊤), Y.presheaf.map (homOfLE (le_top : f ⁻¹ᵁ X.basicOpen a ≤ ⊤)).op s = x := by
  have hloc : ∀ b : 𝔅, ∃ s : Γ(Y, f ⁻¹ᵁ X.basicOpen b.1),
      Y.presheaf.map (homOfLE (inf_le_left :
        f ⁻¹ᵁ X.basicOpen b.1 ⊓ f ⁻¹ᵁ X.basicOpen a ≤ _)).op s =
      Y.presheaf.map (homOfLE (inf_le_right :
        f ⁻¹ᵁ X.basicOpen b.1 ⊓ f ⁻¹ᵁ X.basicOpen a ≤ _)).op x := by
    intro b
    refine exists_res_inf_eq (hgood b.1 b.2) _ ?_
    obtain ⟨p, hp, hpx⟩ := hx
    refine ⟨p.map (X.presheaf.map (homOfLE (le_top : X.basicOpen b.1 ≤ ⊤)).op).hom,
      hp.map _, ?_⟩
    rw [Polynomial.eval₂_map, ← CommRingCat.hom_comp, Scheme.Hom.map_appLE]
    have : (f.appLE ⊤ (f ⁻¹ᵁ X.basicOpen b.1 ⊓ f ⁻¹ᵁ X.basicOpen a) le_top).hom =
        (Y.presheaf.map (homOfLE (inf_le_right :
          f ⁻¹ᵁ X.basicOpen b.1 ⊓ f ⁻¹ᵁ X.basicOpen a ≤ _)).op).hom.comp
          (f.appLE ⊤ (f ⁻¹ᵁ X.basicOpen a) le_top).hom := by
      rw [← CommRingCat.hom_comp, Scheme.Hom.appLE_map]
    rw [this, ← Polynomial.hom_eval₂, hpx, map_zero]
  choose s hs using hloc
  obtain ⟨t, ht, -⟩ := TopCat.Sheaf.existsUnique_gluing' Y.sheaf
    (fun b : 𝔅 ↦ f ⁻¹ᵁ X.basicOpen b.1) ⊤ (fun _ ↦ homOfLE le_top) (fun y _ ↦ by
      obtain ⟨b, hb, hy⟩ := hcov y
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨b, hb⟩, hy⟩) s (fun b b' ↦ by
    have hV : f ⁻¹ᵁ X.basicOpen b.1 ⊓ f ⁻¹ᵁ X.basicOpen b'.1 =
        f ⁻¹ᵁ X.basicOpen (b.1 * b'.1) := by
      rw [Scheme.basicOpen_mul, Scheme.Hom.preimage_inf]
    apply injective_res_of_eq (hgood _ (hmul _ b.2 _ b'.2)) _ hV
    change Y.presheaf.map (homOfLE _).op (Y.presheaf.map (homOfLE inf_le_left).op (s b)) =
      Y.presheaf.map (homOfLE _).op (Y.presheaf.map (homOfLE inf_le_right).op (s b'))
    rw [res_res_apply, res_res_apply,
      ← res_res_apply (inf_le_left : f ⁻¹ᵁ X.basicOpen b.1 ⊓ f ⁻¹ᵁ X.basicOpen a ≤ _)
        (inf_le_inf_right _ inf_le_left), hs,
      ← res_res_apply (inf_le_left : f ⁻¹ᵁ X.basicOpen b'.1 ⊓ f ⁻¹ᵁ X.basicOpen a ≤ _)
        (inf_le_inf_right _ inf_le_right), hs, res_res_apply, res_res_apply])
  refine ⟨t, TopCat.Sheaf.eq_of_locally_eq' Y.sheaf
    (fun b : 𝔅 ↦ f ⁻¹ᵁ X.basicOpen b.1 ⊓ f ⁻¹ᵁ X.basicOpen a) (f ⁻¹ᵁ X.basicOpen a)
    (fun _ ↦ homOfLE inf_le_right) (fun y hy ↦ ?_) _ _ fun b ↦ ?_⟩
  · obtain ⟨b, hb, hyb⟩ := hcov y
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨b, hb⟩, hyb, hy⟩
  · change Y.presheaf.map _ (Y.presheaf.map _ t) = Y.presheaf.map _ x
    rw [res_res_apply, ← res_res_apply (le_top : f ⁻¹ᵁ X.basicOpen b.1 ≤ ⊤) inf_le_left]
    erw [ht b]
    exact hs b

end Local

/-! ### Choice of the basic opens -/

section Choice

variable {X : Scheme.{u}} [IsAffine X]

/-- If `Γ(X, 𝒪)` is a noetherian finite product of normal domains and the complement of `U` has
codimension at least two, then `U` contains `D(a)` for a nonzerodivisor `a`. -/
lemma exists_nonZeroDivisor_basicOpen_le [IsNoetherianRing Γ(X, ⊤)]
    (hX : IsFiniteProductOfNormalDomains Γ(X, ⊤)) {U : X.Opens} (hU : HasCodimTwoComplement U) :
    ∃ a ∈ nonZeroDivisors Γ(X, ⊤), X.basicOpen a ≤ U := by
  obtain ⟨a, haI, ha⟩ := exists_mem_nonZeroDivisors_of_forall_not_le hX (complIdeal U)
    fun P hP hle ↦ by
      haveI : P.IsPrime := hP.1.1
      have h₂ := two_le_height_of_complIdeal_le hU P hle
      rw [Ideal.height_eq_zero_iff.2 hP] at h₂
      exact absurd h₂ (by norm_num)
  refine ⟨a, ha, fun x hx ↦ ?_⟩
  by_contra hxU
  exact (mem_pointIdeal_iff x a).1 ((mem_complIdeal_iff U a).1 haI x hxU) hx

/-- For `Γ(X, 𝒪) ≃ ∏ Dᵢ`, every point of an open `U` has a basic open neighbourhood inside `U`
cut out by an element supported on a single factor. -/
lemma exists_single_basicOpen_le {ι : Type u} [DecidableEq ι] [Finite ι] {D : ι → Type u}
    [∀ i, CommRing (D i)] (e : Γ(X, ⊤) ≃+* ∀ i, D i) {U : X.Opens} {x : X} (hx : x ∈ U) :
    ∃ i d, x ∈ X.basicOpen (e.symm (Pi.single i d)) ∧
      X.basicOpen (e.symm (Pi.single i d)) ≤ U := by
  haveI := Fintype.ofFinite ι
  obtain ⟨i, hi⟩ : ∃ i, e.symm (Pi.single i 1) ∉ pointIdeal x := by
    by_contra! h
    have h₁ : (1 : Γ(X, ⊤)) ∈ pointIdeal x := by
      have : (1 : Γ(X, ⊤)) = ∑ i, e.symm (Pi.single i 1) := by
        rw [← map_sum, Finset.univ_sum_single]
        exact (map_one e.symm).symm
      rw [this]
      exact Ideal.sum_mem _ fun i _ ↦ h i
    exact (pointIdeal x).ne_top_iff_one.1 Ideal.IsPrime.ne_top' h₁
  obtain ⟨c, hcU, hxc⟩ := (isAffineOpen_top X).exists_basicOpen_le (V := U) ⟨x, hx⟩ trivial
  have hb : e.symm (Pi.single i (e c i)) = e.symm (Pi.single i 1) * c := by
    rw [symm_single_mul_eq, one_mul]
  refine ⟨i, e c i, ?_, ?_⟩
  · rw [hb, Scheme.basicOpen_mul]
    exact ⟨by by_contra h; exact hi ((mem_pointIdeal_iff x _).2 h), hxc⟩
  · rw [hb, Scheme.basicOpen_mul]
    exact inf_le_right.trans hcU

end Choice

/-! ### The normalisation -/

/-- **Normalisation in a finite étale cover of a big open.** Let `X` be affine with `Γ(X, 𝒪)` a
noetherian finite product of normal domains, `U ⊆ X` an open whose complement has codimension at
least two and `p : Y ⟶ U` finite étale. Then the relative normalisation of `X` in `Y` is finite
over `X`, its ring of functions is a finite product of normal domains, and the preimage of `U`
has complement of codimension at least two. -/
theorem fromNormalization_properties {X Y : Scheme.{u}} [IsAffine X] [IsNoetherian X]
    [IsNoetherianRing Γ(X, ⊤)] (hX : IsFiniteProductOfNormalDomains Γ(X, ⊤)) (U : X.Opens)
    (hU : HasCodimTwoComplement U) (p : Y ⟶ U) [IsFinite p] [Etale p] :
    IsFinite (p ≫ U.ι).fromNormalization ∧
      IsFiniteProductOfNormalDomains Γ((p ≫ U.ι).normalization, ⊤) ∧
      HasCodimTwoComplement ((p ≫ U.ι).fromNormalization ⁻¹ᵁ U) := by
  classical
  obtain ⟨ι, hι, D, _, _, _, ⟨e⟩⟩ := id hX
  obtain ⟨a, ha, haU⟩ := exists_nonZeroDivisor_basicOpen_le hX hU
  let 𝔅 : Set Γ(X, ⊤) := {b | (∃ i d, b = e.symm (Pi.single i d)) ∧ X.basicOpen b ≤ U}
  have hcov : ∀ y : Y, ∃ b ∈ 𝔅, (p ≫ U.ι).base y ∈ X.basicOpen b := fun y ↦ by
    obtain ⟨i, d, h₁, h₂⟩ := exists_single_basicOpen_le e (x := (p ≫ U.ι).base y) (p.base y).2
    exact ⟨_, ⟨⟨i, d, rfl⟩, h₂⟩, h₁⟩
  have hmul : ∀ b ∈ 𝔅, ∀ b' ∈ 𝔅, b * b' ∈ 𝔅 := by
    rintro _ ⟨⟨i, d, rfl⟩, hb⟩ b' -
    refine ⟨⟨i, _, symm_single_mul_eq e i d b'⟩, ?_⟩
    rw [Scheme.basicOpen_mul]
    exact inf_le_left.trans hb
  have hgood : ∀ b ∈ 𝔅, IsEtaleNormalAt (p ≫ U.ι) a b := by
    rintro _ ⟨⟨i, d, rfl⟩, hb⟩
    obtain ⟨h₁, -, h₃⟩ :=
      isAffineOpen_preimage_finite_etale_app p ((isAffineOpen_top X).basicOpen _) hb
    exact ⟨h₁, h₃, subsingleton_or_isDomain_of_isLocalization_single e i d _ ha⟩
  -- the finite étale algebra `Γ(Y, (p ≫ U.ι)⁻¹ D(a))` over `Γ(X, 𝒪)_a`
  obtain ⟨-, hfin, het⟩ :=
    isAffineOpen_preimage_finite_etale_app p ((isAffineOpen_top X).basicOpen a) haU
  letI : Algebra Γ(X, X.basicOpen a) Γ(Y, (p ≫ U.ι) ⁻¹ᵁ X.basicOpen a) :=
    ((p ≫ U.ι).app (X.basicOpen a)).hom.toAlgebra
  letI : Algebra Γ(X, ⊤) Γ(Y, (p ≫ U.ι) ⁻¹ᵁ X.basicOpen a) :=
    ((algebraMap Γ(X, X.basicOpen a) Γ(Y, (p ≫ U.ι) ⁻¹ᵁ X.basicOpen a)).comp
      (algebraMap Γ(X, ⊤) Γ(X, X.basicOpen a))).toAlgebra
  haveI : IsScalarTower Γ(X, ⊤) Γ(X, X.basicOpen a) Γ(Y, (p ≫ U.ι) ⁻¹ᵁ X.basicOpen a) :=
    .of_algebraMap_eq' rfl
  haveI : Module.Finite Γ(X, X.basicOpen a) Γ(Y, (p ≫ U.ι) ⁻¹ᵁ X.basicOpen a) := hfin
  haveI : Algebra.Etale Γ(X, X.basicOpen a) Γ(Y, (p ≫ U.ι) ⁻¹ᵁ X.basicOpen a) := het
  obtain ⟨hB₁, hB₂, hB₃⟩ := finite_isFiniteProductOfNormalDomains_hasGoingDown_integralClosure hX
    ha Γ(X, X.basicOpen a) Γ(Y, (p ≫ U.ι) ⁻¹ᵁ X.basicOpen a)
  -- restriction identifies the integral closures in `Γ(Y, 𝒪)` and `Γ(Y, (p ≫ U.ι)⁻¹ D(a))`
  letI : Algebra Γ(X, ⊤) Γ(Y, (p ≫ U.ι) ⁻¹ᵁ ⊤) := ((p ≫ U.ι).app ⊤).hom.toAlgebra
  have hnat : ∀ r : Γ(X, ⊤), Y.presheaf.map (homOfLE (le_top :
      (p ≫ U.ι) ⁻¹ᵁ X.basicOpen a ≤ ⊤)).op ((p ≫ U.ι).app ⊤ r) =
      (p ≫ U.ι).app (X.basicOpen a) (X.presheaf.map (homOfLE (le_top :
        X.basicOpen a ≤ ⊤)).op r) := fun r ↦ by
    change ((p ≫ U.ι).app ⊤ ≫ Y.presheaf.map _) r = (X.presheaf.map _ ≫ (p ≫ U.ι).app _) r
    rw [Scheme.Hom.naturality]
    rfl
  let ρ : Γ(Y, (p ≫ U.ι) ⁻¹ᵁ ⊤) →ₐ[Γ(X, ⊤)] Γ(Y, (p ≫ U.ι) ⁻¹ᵁ X.basicOpen a) :=
    { toRingHom := (Y.presheaf.map (homOfLE (le_top :
        (p ≫ U.ι) ⁻¹ᵁ X.basicOpen a ≤ ⊤)).op).hom
      commutes' := hnat }
  have hρ : Function.Injective ρ := injective_res_preimage_basicOpen (p ≫ U.ι) a hcov hgood
  have hΦ : Function.Bijective ρ.mapIntegralClosure := by
    refine ⟨fun x y hxy ↦ Subtype.ext (hρ (congrArg Subtype.val hxy)), fun x ↦ ?_⟩
    obtain ⟨s, hs⟩ := exists_res_preimage_basicOpen_eq (p ≫ U.ι) a hcov hmul hgood x.1 (by
      obtain ⟨q, hq, hqx⟩ := x.2
      refine ⟨q, hq, ?_⟩
      convert hqx using 2
      ext r
      exact hnat r)
    refine ⟨⟨s, (isIntegral_algHom_iff ρ hρ).1 ?_⟩, Subtype.ext hs⟩
    change IsIntegral _ (ρ s)
    rw [show ρ s = x.1 from hs]
    exact x.2
  let Φ := AlgEquiv.ofBijective _ hΦ
  -- the ring of functions of the normalisation
  set q₀ := (p ≫ U.ι).fromNormalization
  let ψ : Γ((p ≫ U.ι).normalization, ⊤) ≃+* integralClosure Γ(X, ⊤) Γ(Y, (p ≫ U.ι) ⁻¹ᵁ ⊤) :=
    ((p ≫ U.ι).normalizationObjIso (isAffineOpen_top X)).commRingCatIsoToRingEquiv
  have hψ : ∀ r, ψ (q₀.appTop r) = algebraMap _ _ r := fun r ↦ by
    change ((p ≫ U.ι).fromNormalization.app ⊤ ≫
      ((p ≫ U.ι).normalizationObjIso (isAffineOpen_top X)).hom) r = _
    rw [Scheme.Hom.fromNormalization_app _ (isAffineOpen_top X), Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
    rfl
  letI : Algebra Γ(X, ⊤) Γ((p ≫ U.ι).normalization, ⊤) := q₀.appTop.hom.toAlgebra
  let Ψ : Γ((p ≫ U.ι).normalization, ⊤) ≃ₐ[Γ(X, ⊤)]
      integralClosure Γ(X, ⊤) Γ(Y, (p ≫ U.ι) ⁻¹ᵁ X.basicOpen a) :=
    { toRingEquiv := ψ.trans Φ.toRingEquiv
      commutes' := fun r ↦ by
        change Φ (ψ (q₀.appTop r)) = _
        rw [hψ, AlgEquiv.commutes] }
  haveI : Module.Finite Γ(X, ⊤) Γ((p ≫ U.ι).normalization, ⊤) :=
    Module.Finite.equiv Ψ.symm.toLinearEquiv
  haveI : Algebra.HasGoingDown Γ(X, ⊤) Γ((p ≫ U.ι).normalization, ⊤) :=
    Algebra.HasGoingDown.of_algEquiv Ψ.symm
  haveI : IsNoetherianRing Γ((p ≫ U.ι).normalization, ⊤) :=
    isNoetherian_of_tower Γ(X, ⊤) inferInstance
  haveI : IsAffine (p ≫ U.ι).normalization := isAffine_of_isAffineHom q₀
  refine ⟨?_, hB₂.of_ringEquiv Ψ.toRingEquiv, fun y hy ↦ ?_⟩
  · rw [HasAffineProperty.iff_of_isAffine (P := @IsFinite)]
    exact ⟨inferInstance, RingHom.finite_algebraMap.2 inferInstance⟩
  · have hcomap : pointIdeal (q₀.base y) =
        (pointIdeal y).comap (algebraMap Γ(X, ⊤) Γ((p ≫ U.ι).normalization, ⊤)) := by
      ext r
      rw [Ideal.mem_comap, mem_pointIdeal_iff, mem_pointIdeal_iff]
      change _ ↔ y ∉ ((p ≫ U.ι).normalization).basicOpen (q₀.app ⊤ r)
      rw [← Scheme.Hom.preimage_basicOpen]
      rfl
    have h₂ := hU _ hy
    rw [ringKrullDim_stalk_eq_height, hcomap] at h₂
    rw [ringKrullDim_stalk_eq_height]
    exact h₂.trans (WithBot.coe_le_coe.2 (Ideal.height_comap_le_height _))

/-- **`ComplexAnalytic.NormalizationInCover` holds**: the normalisation of a normal affine scheme
`X` in a finite étale cover of an open with complement of codimension at least two. -/
theorem normalizationInCover : NormalizationInCover.{u} := by
  intro X _ hX U hU Y p hp
  let p₀ : Y.obj.left ⟶ (U : Scheme.{u}) := p.hom.left
  haveI : IsFinite p₀ := hp.1
  haveI : Etale p₀ := hp.2
  haveI := isNoetherianRing_of_isAffine X
  haveI : IsNoetherian X.obj.left := {}
  obtain ⟨hfin, hnorm, hcodim⟩ := fromNormalization_properties hX U hU p₀
  haveI : LocallyOfFiniteType X.obj.hom := X.property
  have hlft : LocallyOfFiniteType ((p₀ ≫ U.ι).fromNormalization ≫ X.obj.hom) := by
    infer_instance
  have haff : IsAffine (p₀ ≫ U.ι).normalization :=
    isAffine_of_isAffineHom (p₀ ≫ U.ι).fromNormalization
  let Yn : SchemeLFTℂ.{u} := ⟨Over.mk ((p₀ ≫ U.ι).fromNormalization ≫ X.obj.hom), hlft⟩
  let q : Yn ⟶ X := ObjectProperty.homMk (Over.homMk (p₀ ≫ U.ι).fromNormalization rfl)
  let e : Y ⟶ Yn := ObjectProperty.homMk (Over.homMk (p₀ ≫ U.ι).toNormalization (by
    change _ ≫ (p₀ ≫ U.ι).fromNormalization ≫ X.obj.hom = Y.obj.hom
    rw [Scheme.Hom.toNormalization_fromNormalization_assoc, Category.assoc]
    exact Over.w p.hom))
  exact ⟨Yn, q, e, haff, hfin, hnorm, hcodim, isPullback_toNormalization U p₀⟩

/-- **Essential surjectivity from a big open of a normal affine scheme.** Let `X` be an affine
scheme of finite type over `ℂ` whose ring of functions is a finite product of normal domains and
`U ⊆ X` an open whose complement has codimension at least two. If the restriction of a Hausdorff
finite étale cover `W` of `X^an` to `U^an` is the analytification of a finite étale cover of `U`,
then `W` is the analytification of a finite étale cover of `X`. -/
theorem mem_essImage_of_restrict' (X : SchemeLFTℂ.{u}) [IsAffine X.obj.left]
    (hX : IsFiniteProductOfNormalDomains Γ(X.obj.left, ⊤))
    (U : X.obj.left.Opens) (hU : HasCodimTwoComplement U)
    (W : AnalyticSpace.FiniteEtaleOver (analytification.obj X)) [T2Space W.left]
    (hW : (analytificationFiniteEtaleOver (X.restrict U)).essImage (restrictFiniteEtaleOver W U)) :
    (analytificationFiniteEtaleOver X).essImage W :=
  mem_essImage_of_restrict_of_normalizationInCover normalizationInCover X hX U hU W hW

end ComplexAnalytic
