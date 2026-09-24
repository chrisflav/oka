/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.Scheme
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Schemes locally of finite type over `ℂ` are locally noetherian
-/

universe u

namespace ComplexAnalytic

/-- A scheme locally of finite type over `ℂ` is locally noetherian. -/
instance SchemeLFTℂ.isLocallyNoetherian (Y : SchemeLFTℂ.{u}) :
    AlgebraicGeometry.IsLocallyNoetherian Y.obj.left :=
  haveI : AlgebraicGeometry.LocallyOfFiniteType Y.obj.hom := Y.property
  haveI : IsNoetherianRing (ULift.{u} ℂ) := isNoetherianRing_of_ringEquiv ℂ ULift.ringEquiv.symm
  AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian Y.obj.hom

end ComplexAnalytic
