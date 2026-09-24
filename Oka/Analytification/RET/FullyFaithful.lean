/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.Connected

/-!
# Analytification is fully faithful on finite étale covers

For every scheme `X` locally of finite type over `ℂ`, the analytification functor
`FEt(X) ⥤ FEt(X^an)` is fully faithful: it is faithful (`Oka/Analytification/RET/Faithful.lean`),
and full because analytification preserves connectedness
(`ComplexAnalytic.analytificationPreservesConnected`,
`ComplexAnalytic.full_analytificationFiniteEtaleOver`).
-/

open CategoryTheory

universe u

namespace ComplexAnalytic

instance (X : SchemeLFTℂ.{u}) : (analytificationFiniteEtaleOver X).Full :=
  full_analytificationFiniteEtaleOver analytificationPreservesConnected X

/-- **Analytification is fully faithful on finite étale covers.** -/
noncomputable def fullyFaithfulAnalytificationFiniteEtaleOver (X : SchemeLFTℂ.{u}) :
    (analytificationFiniteEtaleOver X).FullyFaithful :=
  .ofFullyFaithful _

end ComplexAnalytic
