/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.ES.DimZero

/-!
# Riemann existence theorem in dimension at most one

Let `X` be a scheme locally of finite type over `ℂ` all of whose affine opens have Krull dimension
`≤ 1` (for instance `topologicalKrullDim X ≤ 1`). Then analytification is an equivalence between
finite étale covers of `X` and finite étale covers of `X^an` with separated structure map
(`ComplexAnalytic.analytificationSepFiniteEtaleOverEquiv`).

The separatedness hypothesis cannot be dropped:
`ComplexAnalytic.AnalyticSpace.doubledLineOver` is a finite étale cover of `ℂ¹` whose total space
is not Hausdorff.

## Proof

Full faithfulness is `ComplexAnalytic.fullyFaithfulAnalytificationSepFiniteEtaleOver`.
Essential surjectivity is Zariski-local (`ComplexAnalytic.SeparatedCoversAlgebraic.of_cover`), so
`X` may be assumed affine. For `X` affine of dimension `≤ 1` pass to the reduced quotient and
then, through the Milnor square of the normalisation, to a finite product of domains of
dimension `≤ 1` and to the conductor, of dimension `≤ 0`
(`ComplexAnalytic.SeparatedCoversAlgebraic.of_ringKrullDim_le`). Domains of dimension one are
handled by the Riemann existence theorem for affine curves, domains of dimension zero and schemes
of dimension zero by `Oka/Analytification/RET/ES/DimZero.lean`.

## Main results

- `ComplexAnalytic.separatedCoversAlgebraic_of_ringKrullDim_le_one`: affine schemes of dimension
  `≤ 1`.
- `ComplexAnalytic.mem_essImage_analytificationFiniteEtaleOver_of_ringKrullDim_le_one`: a finite
  étale cover of `X^an` with Hausdorff total space, for `X` affine of dimension `≤ 1`, is
  algebraic.
- `ComplexAnalytic.essSurj_analytificationSepFiniteEtaleOver`,
  `ComplexAnalytic.isEquivalence_analytificationSepFiniteEtaleOver`,
  `ComplexAnalytic.analytificationSepFiniteEtaleOverEquiv`: the Riemann existence theorem for
  schemes all of whose affine opens have dimension `≤ 1`.
- `ComplexAnalytic.isEquivalence_analytificationSepFiniteEtaleOver_of_topologicalKrullDim_le_one`,
  `ComplexAnalytic.analytificationSepFiniteEtaleOverEquivOfTopologicalKrullDimLEOne`: the same
  for `topologicalKrullDim X ≤ 1`.
-/

open CategoryTheory AlgebraicGeometry

universe u

namespace ComplexAnalytic

open AnalyticSpace

noncomputable section

/-- A positive element of `WithBot ℕ∞` is at least `1`. -/
lemma one_le_of_pos_withBotENat {x : WithBot ℕ∞} (h : 0 < x) : 1 ≤ x := by
  cases x with
  | bot => exact absurd h (not_lt_bot)
  | coe n => exact WithBot.coe_le_coe.2 (Order.one_le_iff_pos.2 (WithBot.coe_lt_coe.1 h))

/-- An element of `WithBot ℕ∞` below `1` is at most `0`. -/
lemma le_zero_of_lt_one_withBotENat {x : WithBot ℕ∞} (h : x < 1) : x ≤ 0 :=
  not_lt.1 fun h' ↦ (not_le.2 h) (one_le_of_pos_withBotENat h')

/-- An affine scheme with nontrivial ring of global sections is nonempty. -/
lemma nonempty_of_isAffine_of_nontrivial (X : Scheme.{u}) [IsAffine X]
    [Nontrivial Γ(X, ⊤)] : Nonempty X :=
  ⟨X.isoSpec.inv.base (Nonempty.some (inferInstance : Nonempty (PrimeSpectrum Γ(X, ⊤))))⟩

/-- **Affine integral schemes of dimension `≤ 1`.** -/
theorem SeparatedCoversAlgebraic.of_isDomain_of_ringKrullDim_le_one (X : SchemeLFTℂ.{u})
    [IsAffine X.obj.left] [IsDomain Γ(X.obj.left, ⊤)] (hX : ringKrullDim Γ(X.obj.left, ⊤) ≤ 1) :
    SeparatedCoversAlgebraic X := by
  by_cases h₀ : ringKrullDim Γ(X.obj.left, ⊤) ≤ 0
  · exact SeparatedCoversAlgebraic.of_isDomain_of_ringKrullDim_eq_zero X
      (le_antisymm h₀ ringKrullDim_nonneg_of_nontrivial)
  · haveI := nonempty_of_isAffine_of_nontrivial X.obj.left
    haveI := isIntegral_of_isAffine_of_isDomain X.obj.left
    exact SeparatedCoversAlgebraic.of_ringKrullDim_eq_one X
      (le_antisymm hX (one_le_of_pos_withBotENat (not_le.mp h₀)))

/-- **Riemann existence for affine schemes of dimension `≤ 1`**: every finite étale cover with
separated structure map of the analytification of an affine scheme `X` of finite type over `ℂ`
with `dim Γ(X, 𝒪_X) ≤ 1` is the analytification of a finite étale cover of `X`. -/
theorem separatedCoversAlgebraic_of_ringKrullDim_le_one (X : SchemeLFTℂ.{u})
    [IsAffine X.obj.left] (hX : ringKrullDim Γ(X.obj.left, ⊤) ≤ 1) :
    SeparatedCoversAlgebraic X :=
  SeparatedCoversAlgebraic.of_ringKrullDim_le 1
    (fun Y _ _ hY ↦ SeparatedCoversAlgebraic.of_isDomain_of_ringKrullDim_le_one Y
      (by exact_mod_cast hY))
    (fun Y _ hY ↦ separatedCoversAlgebraic_of_ringKrullDim_le_zero Y
      (le_zero_of_lt_one_withBotENat (by exact_mod_cast hY))) X (by exact_mod_cast hX)

/-- **Riemann existence for affine schemes of dimension `≤ 1`**, for covers with Hausdorff total
space. -/
theorem mem_essImage_analytificationFiniteEtaleOver_of_ringKrullDim_le_one (X : SchemeLFTℂ.{u})
    [IsAffine X.obj.left] (hX : ringKrullDim Γ(X.obj.left, ⊤) ≤ 1)
    (W : AnalyticSpace.FiniteEtaleOver (analytification.obj X)) [T2Space W.left] :
    (analytificationFiniteEtaleOver X).essImage W :=
  separatedCoversAlgebraic_of_ringKrullDim_le_one X hX W (T2Space.isSeparatedMap (X := W.left) _)

/-- **Riemann existence in dimension zero**, for covers with Hausdorff total space. -/
theorem mem_essImage_analytificationFiniteEtaleOver_of_ringKrullDim_le_zero (X : SchemeLFTℂ.{u})
    [IsAffine X.obj.left] (hX : ringKrullDim Γ(X.obj.left, ⊤) ≤ 0)
    (W : AnalyticSpace.FiniteEtaleOver (analytification.obj X)) [T2Space W.left] :
    (analytificationFiniteEtaleOver X).essImage W :=
  separatedCoversAlgebraic_of_ringKrullDim_le_zero X hX W (T2Space.isSeparatedMap (X := W.left) _)

/-! ### Schemes of dimension at most one -/

section

variable (X : SchemeLFTℂ.{u})
  (hX : ∀ U ∈ X.obj.left.affineOpens, ringKrullDim Γ(X.obj.left, U) ≤ 1)

include hX in
/-- **Every separated finite étale cover of `X^an` is algebraic**, for `X` all of whose affine
opens have dimension `≤ 1`. -/
theorem separatedCoversAlgebraic_of_forall_affineOpens :
    SeparatedCoversAlgebraic X := by
  refine SeparatedCoversAlgebraic.of_cover (fun U : X.obj.left.affineOpens ↦ U.1)
    (iSup_affineOpens_eq_top X.obj.left) fun U ↦ ?_
  haveI : IsAffine (X.restrict U.1).obj.left := U.2
  exact separatedCoversAlgebraic_of_ringKrullDim_le_one _
    ((ringKrullDim_eq_of_ringEquiv (Scheme.Opens.topIso U.1).commRingCatIsoToRingEquiv).trans_le
      (hX U.1 U.2))

include hX in
/-- **Riemann existence theorem in dimension `≤ 1`**: the analytification functor from finite
étale covers of `X` to finite étale covers of `X^an` with separated structure map is essentially
surjective. -/
theorem essSurj_analytificationSepFiniteEtaleOver :
    (analytificationSepFiniteEtaleOver X).EssSurj :=
  (separatedCoversAlgebraic_iff_essSurj X).1 (separatedCoversAlgebraic_of_forall_affineOpens X hX)

include hX in
/-- **Riemann existence theorem in dimension `≤ 1`**: the analytification functor from finite
étale covers of `X` to finite étale covers of `X^an` with separated structure map is an
equivalence. -/
theorem isEquivalence_analytificationSepFiniteEtaleOver :
    (analytificationSepFiniteEtaleOver X).IsEquivalence :=
  haveI := essSurj_analytificationSepFiniteEtaleOver X hX
  { }

/-- **Riemann existence theorem in dimension `≤ 1`**, as an equivalence of categories
`FEt(X) ≌ SepFEt(X^an)`. -/
def analytificationSepFiniteEtaleOverEquiv :
    SchemeLFTℂ.FiniteEtaleOver X ≌ SeparatedFiniteEtaleOver (analytification.obj X) :=
  haveI := isEquivalence_analytificationSepFiniteEtaleOver X hX
  (analytificationSepFiniteEtaleOver X).asEquivalence

lemma analytificationSepFiniteEtaleOverEquiv_functor :
    (analytificationSepFiniteEtaleOverEquiv X hX).functor = analytificationSepFiniteEtaleOver X :=
  rfl

end

/-! ### Topological dimension -/

section

variable (X : SchemeLFTℂ.{u}) (hX : topologicalKrullDim X.obj.left ≤ 1)

include hX in
/-- A scheme of topological dimension `≤ 1` has affine opens of Krull dimension `≤ 1`. -/
lemma ringKrullDim_le_one_of_topologicalKrullDim_le_one :
    ∀ U ∈ X.obj.left.affineOpens, ringKrullDim Γ(X.obj.left, U) ≤ 1 := fun U hU ↦ by
  rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim Γ(X.obj.left, U)]
  change topologicalKrullDim (Spec Γ(X.obj.left, U)) ≤ 1
  rw [← IsHomeomorph.topologicalKrullDim_eq _
    (IsAffineOpen.isoSpec hU).hom.homeomorph.isHomeomorph]
  exact (topologicalKrullDim_subspace_le X.obj.left U).trans hX

include hX in
/-- **Riemann existence theorem for schemes of topological dimension `≤ 1`.** -/
theorem isEquivalence_analytificationSepFiniteEtaleOver_of_topologicalKrullDim_le_one :
    (analytificationSepFiniteEtaleOver X).IsEquivalence :=
  isEquivalence_analytificationSepFiniteEtaleOver X
    (ringKrullDim_le_one_of_topologicalKrullDim_le_one X hX)

/-- **Riemann existence theorem for schemes of topological dimension `≤ 1`**, as an equivalence of
categories `FEt(X) ≌ SepFEt(X^an)`. -/
def analytificationSepFiniteEtaleOverEquivOfTopologicalKrullDimLEOne :
    SchemeLFTℂ.FiniteEtaleOver X ≌ SeparatedFiniteEtaleOver (analytification.obj X) :=
  analytificationSepFiniteEtaleOverEquiv X (ringKrullDim_le_one_of_topologicalKrullDim_le_one X hX)

end

end

end ComplexAnalytic
