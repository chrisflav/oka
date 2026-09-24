/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.GAGA.Proper.Induction
import Oka.Analytification.RET.ES.NilThickening

/-!
# Essential surjectivity and the reduction

For an affine scheme `X` locally of finite type over `ℂ`, if every finite étale cover of
`(X_red)^an` is the analytification of a finite étale cover of `X_red`, then every finite étale
cover of `X^an` is the analytification of a finite étale cover of `X`. Here `X_red` is
`ComplexAnalytic.SchemeLFTℂ.reducedSubscheme X ⊤`, whose inclusion into `X` is a closed immersion
which is surjective on underlying spaces.

## Main results

- `ComplexAnalytic.SchemeLFTℂ.surjective_reducedSubschemeι_top`: `X_red ⟶ X` is surjective.
- `ComplexAnalytic.essSurj_analytificationFiniteEtaleOver_of_reducedSubscheme`: essential
  surjectivity of the analytification on finite étale covers for `X_red` implies it for `X`.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace ComplexAnalytic

/-- The inclusion of the reduced closed subscheme on all of `X` is surjective. -/
lemma SchemeLFTℂ.surjective_reducedSubschemeι_top (X : SchemeLFTℂ.{u}) :
    Function.Surjective (X.reducedSubschemeι ⊤).hom.left.base := by
  rw [← Set.range_eq_univ, X.range_reducedSubschemeι]
  rfl

/-- **Essential surjectivity for `X_red` implies essential surjectivity for `X`**, for `X` affine:
if every finite étale cover of `(X_red)^an` is the analytification of a finite étale cover of
`X_red`, the same holds for `X`. -/
theorem essSurj_analytificationFiniteEtaleOver_of_reducedSubscheme (X : SchemeLFTℂ.{u})
    [IsAffine X.obj.left] [(analytificationFiniteEtaleOver (X.reducedSubscheme ⊤)).EssSurj] :
    (analytificationFiniteEtaleOver X).EssSurj :=
  essSurj_analytificationFiniteEtaleOver_of_isClosedImmersion (X.reducedSubschemeι ⊤)
    X.surjective_reducedSubschemeι_top

end ComplexAnalytic
