/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.ES.Curve
import Oka.Analytification.RET.ES.SeparatedProduct

/-!
# Separated finite étale covers in dimension zero

Every finite étale cover with separated structure map of the analytification of an affine scheme
`X` of finite type over `ℂ` with `dim Γ(X, 𝒪_X) ≤ 0` is the analytification of a finite étale
cover of `X` (`ComplexAnalytic.separatedCoversAlgebraic_of_ringKrullDim_le_zero`).

For `X` integral of dimension zero, with `K = Γ(X, 𝒪_X)`, the line `T = Spec K[t]` is an affine
integral curve with a section `s : X ⟶ T` (`t ↦ 0`) of the projection `π : T ⟶ X`. A cover `W` of
`X^an` is the pullback along `s^an` of its pullback along `π^an`, which is algebraic by the
Riemann existence theorem for affine curves. The general case reduces to this one by passing to
the reduced quotient and to the normalisation, a finite product of fields.

## Main results

- `ComplexAnalytic.SeparatedCoversAlgebraic.of_ringKrullDim_eq_one`: affine integral curves.
- `ComplexAnalytic.SeparatedCoversAlgebraic.of_isDomain_of_ringKrullDim_eq_zero`: the integral
  case of dimension zero.
- `ComplexAnalytic.SeparatedCoversAlgebraic.of_isReduced_of_ringKrullDim_le`,
  `ComplexAnalytic.SeparatedCoversAlgebraic.of_ringKrullDim_le`: the induction step on the
  dimension.
- `ComplexAnalytic.separatedCoversAlgebraic_of_ringKrullDim_le_zero`: dimension zero.
-/

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace ComplexAnalytic

open AnalyticSpace

noncomputable section

/-- **Affine integral curves**: `SeparatedCoversAlgebraic` holds for an affine integral scheme of
finite type over `ℂ` of dimension one. -/
theorem SeparatedCoversAlgebraic.of_ringKrullDim_eq_one (X : SchemeLFTℂ.{u}) [IsAffine X.obj.left]
    [IsIntegral X.obj.left] (hdim : ringKrullDim Γ(X.obj.left, ⊤) = 1) :
    SeparatedCoversAlgebraic X := fun W hW ↦
  haveI := t2Space_analytification_of_isAffine X
  haveI := FiniteEtaleOver.t2Space_left_of_isSeparatedMap W hW
  mem_essImage_analytificationFiniteEtaleOver_of_ringKrullDim_eq_one X hdim W

/-! ### The line over an affine scheme -/

namespace SchemeLFTℂ

variable (X : SchemeLFTℂ.{u}) [IsAffine X.obj.left]

/-- `Spec Γ(X, 𝒪_X)[t] ⟶ X`. -/
def lineToBase : Spec (CommRingCat.of (Polynomial Γ(X.obj.left, ⊤))) ⟶ X.obj.left :=
  Spec.map (CommRingCat.ofHom Polynomial.C) ≫ X.obj.left.isoSpec.inv

/-- `X ⟶ Spec Γ(X, 𝒪_X)[t]`, the zero section. -/
def lineZero : X.obj.left ⟶ Spec (CommRingCat.of (Polynomial Γ(X.obj.left, ⊤))) :=
  X.obj.left.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom 0))

lemma lineZero_lineToBase : lineZero X ≫ lineToBase X = 𝟙 _ := by
  have h : CommRingCat.ofHom (Polynomial.C (R := Γ(X.obj.left, ⊤))) ≫
      CommRingCat.ofHom (Polynomial.evalRingHom 0) = 𝟙 _ := by
    ext a
    simp
  simp only [lineZero, lineToBase, Category.assoc]
  rw [← Spec.map_comp_assoc, h, Spec.map_id]
  erw [Category.id_comp]
  exact Iso.hom_inv_id _

/-- **The line `Spec Γ(X, 𝒪_X)[t]`** over `X`, as a scheme locally of finite type over `ℂ`. -/
def line : SchemeLFTℂ.{u} :=
  ⟨Over.mk (lineToBase X ≫ X.obj.hom), by
    haveI : LocallyOfFiniteType X.obj.hom := X.property
    haveI : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom
        (Polynomial.C (R := Γ(X.obj.left, ⊤))))) := by
      rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
      exact RingHom.finiteType_algebraMap.mpr inferInstance
    change LocallyOfFiniteType (lineToBase X ≫ X.obj.hom)
    rw [lineToBase]
    infer_instance⟩

/-- The projection of the line to `X`. -/
def lineπ : line X ⟶ X :=
  ObjectProperty.homMk (Over.homMk (lineToBase X) rfl)

/-- The zero section of the line. -/
def lineι : X ⟶ line X :=
  ObjectProperty.homMk (Over.homMk (lineZero X) (by
    change lineZero X ≫ lineToBase X ≫ X.obj.hom = X.obj.hom
    rw [← Category.assoc, lineZero_lineToBase, Category.id_comp]))

lemma lineι_lineπ : lineι X ≫ lineπ X = 𝟙 X := by
  ext1
  exact Over.OverMorphism.ext (lineZero_lineToBase X)

instance : IsAffine (line X).obj.left :=
  inferInstanceAs (IsAffine (Spec (CommRingCat.of (Polynomial Γ(X.obj.left, ⊤)))))

instance [IsDomain Γ(X.obj.left, ⊤)] : IsIntegral (line X).obj.left :=
  inferInstanceAs (IsIntegral (Spec (CommRingCat.of (Polynomial Γ(X.obj.left, ⊤)))))

lemma ringKrullDim_line :
    ringKrullDim Γ((line X).obj.left, ⊤) = ringKrullDim Γ(X.obj.left, ⊤) + 1 := by
  obtain ⟨_, _⟩ := X.exists_algebra_finiteType
  haveI := Algebra.FiniteType.isNoetherianRing ℂ Γ(X.obj.left, ⊤)
  exact (ringKrullDim_eq_of_ringEquiv (R := Γ((line X).obj.left, ⊤)) (Scheme.ΓSpecIso
    (CommRingCat.of (Polynomial Γ(X.obj.left, ⊤)))).commRingCatIsoToRingEquiv).trans
    Polynomial.ringKrullDim_of_isNoetherianRing

end SchemeLFTℂ

/-- A cover of `X^an` is the pullback of its pullback to `T^an` along `s^an`, for a section `s` of
`π : T ⟶ X`. -/
lemma nonempty_iso_pullbackFiniteEtaleOver_of_section {X T : SchemeLFTℂ.{u}} (π : T ⟶ X)
    (s : X ⟶ T) (hs : s ≫ π = 𝟙 X) (W : AnalyticSpace.FiniteEtaleOver (analytification.obj X)) :
    Nonempty (pullbackFiniteEtaleOver (pullbackFiniteEtaleOver W π) s ≅ W) := by
  have h₁ := IsPullback.of_hasPullback W.hom (analytification.map π)
  have h₂ := IsPullback.of_hasPullback (pullback.snd W.hom (analytification.map π))
    (analytification.map s)
  have h := h₂.paste_horiz h₁
  have hsπ : analytification.map s ≫ analytification.map π = 𝟙 _ := by
    rw [← CategoryTheory.Functor.map_comp, hs, CategoryTheory.Functor.map_id]
  have hi := h.isIso_fst_of_isIso (by erw [hsπ]; exact IsIso.id _)
  refine ⟨MorphismProperty.Over.isoMk (@asIso _ _ _ _ (pullback.fst _ _ ≫ pullback.fst _ _) hi) ?_⟩
  refine h.w.trans ?_
  erw [hsπ, Category.comp_id]
  rfl

/-- **The integral case of dimension zero.** -/
theorem SeparatedCoversAlgebraic.of_isDomain_of_ringKrullDim_eq_zero (X : SchemeLFTℂ.{u})
    [IsAffine X.obj.left] [IsDomain Γ(X.obj.left, ⊤)]
    (hdim : ringKrullDim Γ(X.obj.left, ⊤) = 0) : SeparatedCoversAlgebraic X := by
  intro W hW
  have hT := SeparatedCoversAlgebraic.of_ringKrullDim_eq_one (SchemeLFTℂ.line X)
    (by rw [SchemeLFTℂ.ringKrullDim_line, hdim, zero_add])
  have h₁ := mem_essImage_pullbackFiniteEtaleOver
    (hT _ (isSeparatedMap_pullbackFiniteEtaleOver W hW (SchemeLFTℂ.lineπ X)))
    (SchemeLFTℂ.lineι X)
  obtain ⟨e⟩ := nonempty_iso_pullbackFiniteEtaleOver_of_section _ _ (SchemeLFTℂ.lineι_lineπ X) W
  obtain ⟨Z, ⟨e'⟩⟩ := h₁
  exact ⟨Z, ⟨e' ≪≫ e⟩⟩

/-! ### Induction on the dimension -/

section Dimension

variable (n : ℕ)
  (hdom : ∀ (Y : SchemeLFTℂ.{u}) [IsAffine Y.obj.left], IsDomain Γ(Y.obj.left, ⊤) →
    ringKrullDim Γ(Y.obj.left, ⊤) ≤ n → SeparatedCoversAlgebraic Y)
  (hlow : ∀ (Y : SchemeLFTℂ.{u}) [IsAffine Y.obj.left], ringKrullDim Γ(Y.obj.left, ⊤) < n →
    SeparatedCoversAlgebraic Y)

include hdom hlow in
/-- **The reduced case of the induction step.** If `SeparatedCoversAlgebraic` holds for all
affine integral schemes of dimension `≤ n` and all affine schemes of dimension `< n`, then it
holds for every reduced affine scheme of dimension `≤ n`: the normalisation is a finite product of
domains of dimension `≤ n`, and the conductor has dimension `< n`. -/
theorem SeparatedCoversAlgebraic.of_isReduced_of_ringKrullDim_le (X : SchemeLFTℂ.{u})
    [IsAffine X.obj.left] [IsReduced Γ(X.obj.left, ⊤)] (hX : ringKrullDim Γ(X.obj.left, ⊤) ≤ n) :
    SeparatedCoversAlgebraic X := by
  classical
  obtain ⟨_, _⟩ := X.exists_algebra_finiteType
  obtain ⟨S, _, _, _, hinj, hS, hdimS, I, hI, hdimI⟩ := exists_normalization Γ(X.obj.left, ⊤) ℂ
  obtain ⟨ι, _, D, _, _, _, ⟨e⟩⟩ := hS
  refine SeparatedCoversAlgebraic.of_milnorSquare X S hinj I hI ?_
    (hlow _ ((ringKrullDim_eq_of_ringEquiv (SchemeLFTℂ.specAlgebraΓEquiv X _)).trans_lt
      (lt_natCast_of_add_one_le (hdimI.trans hX))))
  refine SeparatedCoversAlgebraic.of_ringEquiv_pi D _
    ((SchemeLFTℂ.specAlgebraΓEquiv X S).trans e) fun i Y _ ⟨e'⟩ ↦ ?_
  haveI : IsDomain Γ(Y.obj.left, ⊤) := MulEquiv.isDomain (D i) e'.toMulEquiv
  refine hdom Y this ?_
  rw [ringKrullDim_eq_of_ringEquiv e']
  refine (ringKrullDim_le_of_surjective ((Pi.evalRingHom D i).comp e.toRingHom)
    fun d ↦ ⟨e.symm (Pi.single i d), ?_⟩).trans (hdimS.trans hX)
  simp

include hdom hlow in
/-- **The induction step.** Under the hypotheses of
`ComplexAnalytic.SeparatedCoversAlgebraic.of_isReduced_of_ringKrullDim_le`,
`SeparatedCoversAlgebraic` holds for every affine scheme of finite type over `ℂ` of dimension
`≤ n`. -/
theorem SeparatedCoversAlgebraic.of_ringKrullDim_le (X : SchemeLFTℂ.{u}) [IsAffine X.obj.left]
    (hX : ringKrullDim Γ(X.obj.left, ⊤) ≤ n) : SeparatedCoversAlgebraic X := by
  let R := Γ(X.obj.left, ⊤) ⧸ nilradical Γ(X.obj.left, ⊤)
  haveI : IsReduced R := (Ideal.isRadical_iff_quotient_reduced _).1 (Ideal.radical_isRadical _)
  haveI : IsReduced Γ((SchemeLFTℂ.specAlgebra X R).obj.left, ⊤) :=
    isReduced_of_injective (SchemeLFTℂ.specAlgebraΓEquiv X R).toRingHom
      (SchemeLFTℂ.specAlgebraΓEquiv X R).injective
  exact SeparatedCoversAlgebraic.of_quotient_nilradical X
    (SeparatedCoversAlgebraic.of_isReduced_of_ringKrullDim_le n hdom hlow _
      ((ringKrullDim_eq_of_ringEquiv (SchemeLFTℂ.specAlgebraΓEquiv X R)).trans_le
        ((ringKrullDim_le_of_surjective _ Ideal.Quotient.mk_surjective).trans hX)))

end Dimension

/-- An affine scheme of negative dimension satisfies `SeparatedCoversAlgebraic`. -/
theorem separatedCoversAlgebraic_of_ringKrullDim_lt_zero (X : SchemeLFTℂ.{u})
    [IsAffine X.obj.left] (hX : ringKrullDim Γ(X.obj.left, ⊤) < 0) :
    SeparatedCoversAlgebraic X := by
  haveI : Subsingleton Γ(X.obj.left, ⊤) := not_nontrivial_iff_subsingleton.1 fun _ ↦
    (ringKrullDim_nonneg_of_nontrivial.trans_lt hX).false
  exact separatedCoversAlgebraic_of_subsingleton X

/-- **Riemann existence in dimension zero**: every finite étale cover with separated structure
map of the analytification of an affine scheme `X` of finite type over `ℂ` with
`dim Γ(X, 𝒪_X) ≤ 0` is the analytification of a finite étale cover of `X`. -/
theorem separatedCoversAlgebraic_of_ringKrullDim_le_zero (X : SchemeLFTℂ.{u})
    [IsAffine X.obj.left] (hX : ringKrullDim Γ(X.obj.left, ⊤) ≤ 0) :
    SeparatedCoversAlgebraic X :=
  SeparatedCoversAlgebraic.of_ringKrullDim_le 0
    (fun Y _ _ hY ↦ SeparatedCoversAlgebraic.of_isDomain_of_ringKrullDim_eq_zero Y
      (le_antisymm (by exact_mod_cast hY) ringKrullDim_nonneg_of_nontrivial))
    (fun Y _ hY ↦ separatedCoversAlgebraic_of_ringKrullDim_lt_zero Y (by exact_mod_cast hY)) X
    (by exact_mod_cast hX)

end

end ComplexAnalytic
