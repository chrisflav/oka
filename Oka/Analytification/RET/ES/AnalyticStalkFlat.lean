/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.ES.Algebraize
import Mathlib.RingTheory.Regular.Flat

/-!
# Flatness of analytic stalks over global functions

For an affine scheme `V` of finite type over `ℂ` and `v ∈ V^an`, the stalk `𝒪_{V^an,v}` is flat
over `Γ(V, 𝒪_V)` (`ComplexAnalytic.flat_analytificationStalk`): it is the composite of the
localization `Γ(V, 𝒪_V) → 𝒪_{V,π v}` and the faithfully flat map `𝒪_{V,π v} → 𝒪_{V^an,v}`.
Consequently weakly regular sequences of global functions stay weakly regular on the stalks
(`ComplexAnalytic.isWeaklyRegular_analytificationStalk`).
-/

open CategoryTheory Opposite AlgebraicGeometry RingTheory.Sequence

universe u

namespace ComplexAnalytic

open AnalyticSpace

variable (V : SchemeLFTℂ.{u}) [IsAffine V.obj.left]

/-- **Analytic stalks are flat over global functions.** -/
theorem flat_analytificationStalk (v : analytification.obj V) :
    Module.Flat Γ(V.obj.left, ⊤) ((analytification.obj V).presheaf.stalk v) := by
  have hU := AlgebraicGeometry.isAffineOpen_top V.obj.left
  let x : (⊤ : V.obj.left.Opens) := ⟨(analytificationπLRS V).base v, trivial⟩
  letI : Algebra Γ(V.obj.left, ⊤) (V.obj.left.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk V.obj.left.presheaf x
  letI : Algebra (V.obj.left.presheaf.stalk x) ((analytification.obj V).presheaf.stalk v) :=
    ((analytificationπLRS V).stalkMap v).hom.toAlgebra
  haveI : IsScalarTower Γ(V.obj.left, ⊤) (V.obj.left.presheaf.stalk x)
      ((analytification.obj V).presheaf.stalk v) :=
    IsScalarTower.of_algebraMap_eq fun a ↦
      (LocallyRingedSpace.stalkMap_germ_apply (analytificationπLRS V) ⊤ v trivial a).symm
  haveI : IsLocalization.AtPrime (V.obj.left.presheaf.stalk x) (hU.primeIdealOf x).asIdeal :=
    hU.isLocalization_stalk x
  haveI : Module.Flat Γ(V.obj.left, ⊤) (V.obj.left.presheaf.stalk x) :=
    IsLocalization.flat _ (hU.primeIdealOf x).asIdeal.primeCompl
  haveI : Module.FaithfullyFlat (V.obj.left.presheaf.stalk x)
      ((analytification.obj V).presheaf.stalk v) :=
    faithfullyFlat_stalkMap_analytificationπ V v
  exact Module.Flat.trans Γ(V.obj.left, ⊤) (V.obj.left.presheaf.stalk x) _

/-- **Weakly regular sequences of global functions stay weakly regular on analytic stalks.** -/
theorem isWeaklyRegular_analytificationStalk (v : analytification.obj V)
    {rs : List Γ(V.obj.left, ⊤)} (h : IsWeaklyRegular Γ(V.obj.left, ⊤) rs) :
    IsWeaklyRegular ((analytification.obj V).presheaf.stalk v)
      (rs.map fun a ↦ (analytification.obj V).presheaf.Γgerm v (analytificationΓ V a)) := by
  haveI := flat_analytificationStalk V v
  exact h.of_flat

end ComplexAnalytic
