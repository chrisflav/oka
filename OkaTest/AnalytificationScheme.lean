/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import OkaTest.AnalytificationChangeOfVariables
import Oka.Analytification.SchemeAffine

/-!
# The analytification functor on schemes, at the node

`Oka/Analytification/Scheme.lean` defines the analytification of a scheme locally of finite type
over `ℂ` as a representing object, with no reference to presentations. This file runs it on the
node `Spec (ℂ[x, y] ⧸ (x y))` and recovers the node `AnalyticSpace.node` as its analytification,
with the comparison morphism to the scheme being the one of `Oka/Analytification/Presentation.lean`.
-/

open CategoryTheory AlgebraicGeometry ComplexAnalytic ComplexAnalytic.AnalyticSpace

noncomputable section

/-- The node `Spec (ℂ[x, y] ⧸ (x y))`, as a scheme locally of finite type over `ℂ`. -/
abbrev nodeScheme : SchemeLFTℂ := SchemeLFTℂ.specPresentation nodeTuple2.{0}

/-- **The analytification of the node scheme is the node.** -/
def nodeSchemeAnalytificationIso : analytification.obj nodeScheme ≅ AnalyticSpace.node.{0} :=
  analytificationSpecIso nodeTuple2.{0} ≪≫ eqToIso node_eq_analytification_nodeTuple2.symm

/-- The isomorphism carries the comparison morphism of the functor to the one of the zero locus
of the presentation. -/
example : toOverSpec.map (analytificationSpecIso nodeTuple2.{0}).hom ≫
    analytificationToSpecOver nodeTuple2.{0} = analytificationπ nodeScheme :=
  analytificationSpecIso_hom_comp _

/-- The universal property at the node: morphisms from an analytic space `Z` into the
analytification are morphisms `Z ⟶ Spec (ℂ[x, y] ⧸ (x y))` over `Spec ℂ`. -/
example (Z : AnalyticSpace.{0}) :
    (Z ⟶ analytification.obj nodeScheme) ≃
      (toOverSpec.obj Z ⟶ schemeToOverSpec.obj nodeScheme.obj) :=
  analytificationHomEquiv Z nodeScheme

end
