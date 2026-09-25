/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.ES.Induction

/-!
# The Riemann existence theorem

Let `X` be a scheme locally of finite type over `ℂ`. Analytification is an equivalence between
finite étale covers of `X` and finite étale covers of `X^an` with separated structure map,

* for every `X`, assuming the extension statement `ComplexAnalytic.BoundedSections.CapExtension m`
  for all `m` (`ComplexAnalytic.riemannExistence`), or more generally coherence of bounded
  sections `ComplexAnalytic.BoundedCoherent n` for all `n`
  (`ComplexAnalytic.isEquivalence_analytificationSepFiniteEtaleOver_of_boundedCoherent`);
* unconditionally, if all affine opens of `X` have Krull dimension `≤ 2`, for instance if
  `topologicalKrullDim X ≤ 2`
  (`ComplexAnalytic.isEquivalence_analytificationSepFiniteEtaleOver_of_le_two`,
  `ComplexAnalytic.isEquivalence_analytificationSepFiniteEtaleOver_of_topologicalKrullDim_le_two`).

## Proof

Full faithfulness is `ComplexAnalytic.fullyFaithfulAnalytificationSepFiniteEtaleOver`.
Essential surjectivity is Zariski-local, so `X` may be assumed affine, where it is
`ComplexAnalytic.separatedCoversAlgebraic_of_ringKrullDim_le`.
-/

open CategoryTheory AlgebraicGeometry

universe u

namespace ComplexAnalytic

open AnalyticSpace

noncomputable section

/-! ### Bounded dimension -/

section Bounded

variable {n : ℕ} (hB : ∀ m ≤ n, BoundedCoherent.{u} m) (X : SchemeLFTℂ.{u})
  (hX : ∀ U ∈ X.obj.left.affineOpens, ringKrullDim Γ(X.obj.left, U) ≤ n)

include hB hX in
/-- **Every separated finite étale cover of `X^an` is algebraic**, for `X` all of whose affine
opens have dimension `≤ n`, if bounded sections are coherent in dimensions `≤ n`. -/
theorem separatedCoversAlgebraic_of_forall_affineOpens_le :
    SeparatedCoversAlgebraic X := by
  refine SeparatedCoversAlgebraic.of_cover (fun U : X.obj.left.affineOpens ↦ U.1)
    (iSup_affineOpens_eq_top X.obj.left) fun U ↦ ?_
  haveI : IsAffine (X.restrict U.1).obj.left := U.2
  exact separatedCoversAlgebraic_of_ringKrullDim_le hB _
    ((ringKrullDim_eq_of_ringEquiv (Scheme.Opens.topIso U.1).commRingCatIsoToRingEquiv).trans_le
      (hX U.1 U.2))

include hB hX in
/-- **Riemann existence theorem in dimension `≤ n`, given coherence of bounded sections**: for `X`
all of whose affine opens have dimension `≤ n`, analytification is an equivalence between finite
étale covers of `X` and finite étale covers of `X^an` with separated structure map. -/
theorem isEquivalence_analytificationSepFiniteEtaleOver_of_forall_affineOpens_le :
    (analytificationSepFiniteEtaleOver X).IsEquivalence :=
  haveI := (separatedCoversAlgebraic_iff_essSurj X).1
    (separatedCoversAlgebraic_of_forall_affineOpens_le hB X hX)
  { }

end Bounded

/-- In a scheme of topological dimension `≤ n`, all affine opens have Krull dimension `≤ n`. -/
lemma ringKrullDim_le_of_topologicalKrullDim_le (X : Scheme.{u}) {n : WithBot ℕ∞}
    (hX : topologicalKrullDim X ≤ n) :
    ∀ U ∈ X.affineOpens, ringKrullDim Γ(X, U) ≤ n := fun U hU ↦ by
  rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim Γ(X, U)]
  change topologicalKrullDim (Spec Γ(X, U)) ≤ n
  rw [← IsHomeomorph.topologicalKrullDim_eq _
    (IsAffineOpen.isoSpec hU).hom.homeomorph.isHomeomorph]
  exact (topologicalKrullDim_subspace_le X U).trans hX

/-! ### Dimension at most two -/

section LETwo

variable (X : SchemeLFTℂ.{u})

/-- **Riemann existence theorem in dimension `≤ 2`**: for `X` all of whose affine opens have
dimension `≤ 2`, analytification is an equivalence between finite étale covers of `X` and finite
étale covers of `X^an` with separated structure map. -/
theorem isEquivalence_analytificationSepFiniteEtaleOver_of_le_two
    (hX : ∀ U ∈ X.obj.left.affineOpens, ringKrullDim Γ(X.obj.left, U) ≤ 2) :
    (analytificationSepFiniteEtaleOver X).IsEquivalence :=
  isEquivalence_analytificationSepFiniteEtaleOver_of_forall_affineOpens_le
    (fun _ hm ↦ boundedCoherent_of_le_two hm) X (by exact_mod_cast hX)

/-- **Riemann existence theorem in dimension `≤ 2`**, as an equivalence of categories
`FEt(X) ≌ SepFEt(X^an)`. -/
def analytificationSepFiniteEtaleOverEquivOfLETwo
    (hX : ∀ U ∈ X.obj.left.affineOpens, ringKrullDim Γ(X.obj.left, U) ≤ 2) :
    SchemeLFTℂ.FiniteEtaleOver X ≌ SeparatedFiniteEtaleOver (analytification.obj X) :=
  haveI := isEquivalence_analytificationSepFiniteEtaleOver_of_le_two X hX
  (analytificationSepFiniteEtaleOver X).asEquivalence

/-- **Riemann existence theorem for schemes of topological dimension `≤ 2`.** -/
theorem isEquivalence_analytificationSepFiniteEtaleOver_of_topologicalKrullDim_le_two
    (hX : topologicalKrullDim X.obj.left ≤ 2) :
    (analytificationSepFiniteEtaleOver X).IsEquivalence :=
  isEquivalence_analytificationSepFiniteEtaleOver_of_le_two X
    (ringKrullDim_le_of_topologicalKrullDim_le X.obj.left hX)

/-- **Riemann existence theorem for schemes of topological dimension `≤ 2`**, as an equivalence of
categories `FEt(X) ≌ SepFEt(X^an)`. -/
def analytificationSepFiniteEtaleOverEquivOfTopologicalKrullDimLETwo
    (hX : topologicalKrullDim X.obj.left ≤ 2) :
    SchemeLFTℂ.FiniteEtaleOver X ≌ SeparatedFiniteEtaleOver (analytification.obj X) :=
  analytificationSepFiniteEtaleOverEquivOfLETwo X
    (ringKrullDim_le_of_topologicalKrullDim_le X.obj.left hX)

end LETwo

/-! ### All dimensions -/

section General

variable (X : SchemeLFTℂ.{u})

/-- **Every separated finite étale cover of `X^an` is algebraic**, if bounded sections are
coherent in all dimensions. -/
theorem separatedCoversAlgebraic_of_boundedCoherent (hB : ∀ n, BoundedCoherent.{u} n) :
    SeparatedCoversAlgebraic X := by
  refine SeparatedCoversAlgebraic.of_cover (fun U : X.obj.left.affineOpens ↦ U.1)
    (iSup_affineOpens_eq_top X.obj.left) fun U ↦ ?_
  haveI : IsAffine (X.restrict U.1).obj.left := U.2
  obtain ⟨k, hk⟩ := exists_ringKrullDim_le_natCast (X.restrict U.1)
  exact separatedCoversAlgebraic_of_ringKrullDim_le (n := k) (fun m _ ↦ hB m) _ hk

/-- **Riemann existence theorem, given coherence of bounded sections**: analytification is an
equivalence between finite étale covers of `X` and finite étale covers of `X^an` with separated
structure map. -/
theorem isEquivalence_analytificationSepFiniteEtaleOver_of_boundedCoherent
    (hB : ∀ n, BoundedCoherent.{u} n) : (analytificationSepFiniteEtaleOver X).IsEquivalence :=
  haveI := (separatedCoversAlgebraic_iff_essSurj X).1
    (separatedCoversAlgebraic_of_boundedCoherent X hB)
  { }

/-- Bounded sections are coherent in all dimensions, assuming
`ComplexAnalytic.BoundedSections.CapExtension m` for all `m`. -/
theorem boundedCoherent_of_forall_capExtension (hcap : ∀ m, BoundedSections.CapExtension.{u} m)
    (n : ℕ) : BoundedCoherent.{u} n :=
  boundedCoherent_of_capExtension fun m _ _ ↦ hcap m

/-- **The Riemann existence theorem**, assuming `ComplexAnalytic.BoundedSections.CapExtension m`
for all `m`: for every scheme `X` locally of finite type over `ℂ`, analytification is an
equivalence between finite étale covers of `X` and finite étale covers of `X^an` with separated
structure map. -/
theorem riemannExistence (hcap : ∀ m, BoundedSections.CapExtension.{u} m) :
    (analytificationSepFiniteEtaleOver X).IsEquivalence :=
  isEquivalence_analytificationSepFiniteEtaleOver_of_boundedCoherent X
    (boundedCoherent_of_forall_capExtension hcap)

/-- **The Riemann existence theorem**, assuming `ComplexAnalytic.BoundedSections.CapExtension m`
for all `m`, as an equivalence of categories `FEt(X) ≌ SepFEt(X^an)`. -/
def riemannExistenceEquiv (hcap : ∀ m, BoundedSections.CapExtension.{u} m) :
    SchemeLFTℂ.FiniteEtaleOver X ≌ SeparatedFiniteEtaleOver (analytification.obj X) :=
  haveI := riemannExistence X hcap
  (analytificationSepFiniteEtaleOver X).asEquivalence

lemma riemannExistenceEquiv_functor (hcap : ∀ m, BoundedSections.CapExtension.{u} m) :
    (riemannExistenceEquiv X hcap).functor = analytificationSepFiniteEtaleOver X :=
  rfl

end General

end

end ComplexAnalytic
