/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Analysis.Lojasiewicz.ComplexZeroSet
import Oka.Analytification.RET.ClosedPoints
import Oka.Topology.Homotopy.LocallyContractible

/-!
# The analytification of a scheme locally of finite type over `ℂ` is locally contractible,
if real algebraic sets are

For `X` locally of finite type over `ℂ`, every point of `X^an` lies in the image of
`j^an : (Spec ℂ[x] ⧸ (g))^an ⟶ X^an` for an open immersion `j`
(`ComplexAnalytic.exists_openImmersion_specPresentation`,
`ComplexAnalytic.exists_analytification_map_eq_of_openImmersion`), which is an open embedding on
points (`ComplexAnalytic.isOpenEmbedding_analytification_map`). The source is homeomorphic to
the zero locus `AnalyticSpace.analytification g` (`ComplexAnalytic.analytificationSpecIso`),
whose points are, through the closed embedding into `ℂⁿ`, the common zeros of the `gⱼ`
(`ComplexAnalytic.isClosedEmbedding_base_analytificationIncl`,
`ComplexAnalytic.range_base_analytificationIncl`); non-reducedness plays no role, since only the
zero set enters. That set is a real algebraic set
(`MvPolynomial.locallyContractibleSpace_complexZeroSet`), and local contractibility is local
(`LocallyContractibleSpace.of_isOpenEmbedding_cover`).

## Main results

- `ComplexAnalytic.locallyContractibleSpace_analytification_presentation`: the zero locus
  `AnalyticSpace.analytification g` is locally contractible if real algebraic sets are.
- `ComplexAnalytic.locallyContractibleSpace_analytification_of_zeroSet`: **`X^an` is locally
  contractible if zero sets of real polynomials are.**
- `ComplexAnalytic.locallyContractibleSpace_analytification_of_lojasiewicz`: **`X^an` is locally
  contractible if every real polynomial satisfies the Łojasiewicz gradient inequality**
  (`MvPolynomial.LojasiewiczGradient`), by
  `MvPolynomial.locallyContractibleSpace_zeroSet_of_lojasiewicz`.

The hypotheses are hypotheses of the theorems: neither the local contractibility of real
algebraic sets nor the gradient inequality is proved in this file.
-/

open CategoryTheory AlgebraicGeometry Topology

universe u

namespace ComplexAnalytic

open AnalyticSpace

/-- **The zero locus of a presentation is locally contractible, if real algebraic sets are.** -/
theorem locallyContractibleSpace_analytification_presentation
    (h : ∀ (n : ℕ) (f : MvPolynomial (Fin n) ℝ),
      LocallyContractibleSpace {x : Fin n → ℝ // MvPolynomial.eval x f = 0})
    {n k : ℕ} (g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ) :
    LocallyContractibleSpace (AnalyticSpace.analytification.{u} g) :=
  ((isClosedEmbedding_base_analytificationIncl g).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (range_base_analytificationIncl g))).symm.locallyContractibleSpace
    (MvPolynomial.locallyContractibleSpace_complexZeroSet h g)

/-- **The analytification of a scheme locally of finite type over `ℂ` is locally contractible,
if zero sets of real polynomials are.** -/
theorem locallyContractibleSpace_analytification_of_zeroSet
    (h : ∀ (n : ℕ) (f : MvPolynomial (Fin n) ℝ),
      LocallyContractibleSpace {x : Fin n → ℝ // MvPolynomial.eval x f = 0})
    (X : SchemeLFTℂ.{u}) : LocallyContractibleSpace (analytification.obj X) := by
  refine LocallyContractibleSpace.of_isOpenEmbedding_cover.{u} fun x ↦ ?_
  obtain ⟨n, k, g, j, hj, hx⟩ :=
    exists_openImmersion_specPresentation X ((analytificationπ X).left.base x)
  obtain ⟨y, rfl⟩ := exists_analytification_map_eq_of_openImmersion j x hx
  refine ⟨analytification.obj (SchemeLFTℂ.specPresentation g), inferInstance, _,
    isOpenEmbedding_analytification_map j, ⟨y, rfl⟩, ?_⟩
  exact (LocallyRingedSpace.homeoOfIso
    (forgetToLocallyRingedSpace.mapIso (analytificationSpecIso g))).symm.locallyContractibleSpace
    (locallyContractibleSpace_analytification_presentation h g)

/-- **The analytification of a scheme locally of finite type over `ℂ` is locally contractible,
if every real polynomial satisfies the Łojasiewicz gradient inequality.** -/
theorem locallyContractibleSpace_analytification_of_lojasiewicz
    (h : ∀ (n : ℕ) (f : MvPolynomial (Fin n) ℝ), f.LojasiewiczGradient)
    (X : SchemeLFTℂ.{u}) : LocallyContractibleSpace (analytification.obj X) :=
  locallyContractibleSpace_analytification_of_zeroSet
    (fun n f ↦ MvPolynomial.locallyContractibleSpace_zeroSet_of_lojasiewicz f (h n f)) X

end ComplexAnalytic
