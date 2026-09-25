/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.Main
import Oka.Analytification.RET.ES.CapExtension

/-!
# The Riemann existence theorem

For every scheme `X` locally of finite type over `ℂ`, analytification is an equivalence between
finite étale covers of `X` and finite étale covers of `X^an` with separated structure map
(`ComplexAnalytic.riemannExistenceTheorem`, bundled as
`ComplexAnalytic.riemannExistenceTheoremEquiv`). Separatedness is necessary: the line with a
doubled origin is a finite étale cover of `ℂ` that is not the analytification of a scheme.
-/

open CategoryTheory

universe u

namespace ComplexAnalytic

/-- **The Riemann existence theorem**: for every scheme `X` locally of finite type over `ℂ`,
analytification `FEt(X) ⥤ SepFEt(X^an)` is an equivalence of categories. -/
theorem riemannExistenceTheorem (X : SchemeLFTℂ.{u}) :
    (analytificationSepFiniteEtaleOver X).IsEquivalence :=
  riemannExistence X BoundedSections.capExtension

/-- **The Riemann existence theorem**, bundled: finite étale covers of `X` are equivalent to finite
étale covers of `X^an` with separated structure map. -/
noncomputable def riemannExistenceTheoremEquiv (X : SchemeLFTℂ.{u}) :
    SchemeLFTℂ.FiniteEtaleOver X ≌ AnalyticSpace.SeparatedFiniteEtaleOver (analytification.obj X) :=
  riemannExistenceEquiv X BoundedSections.capExtension

end ComplexAnalytic
