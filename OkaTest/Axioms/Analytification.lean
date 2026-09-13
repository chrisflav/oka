/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka

/-!
# Axiom regression tests: Analytification

The comparison morphisms of `Oka/Analytification/`: `ℂ^ι ⟶ Spec (MvPolynomial ι ℂ)` and its
map on stalks, `X^an ⟶ Spec (ℂ[x]/I)` for a presented affine `ℂ`-algebra, the local ring of
`𝔸^ι` at the origin with its completion, the faithful flatness of the germs over it and the same
at an arbitrary point — where it becomes a statement about the stalk map itself — the
analytification as a functor on finitely generated `ℂ`-algebras, the stalk map of the
comparison morphism of a presented algebra, the naturality of the comparison morphism, the
faithful flatness of that stalk map, the analytification of a sheaf, the identification of
the analytification of `A_f` with the non-vanishing locus of `f` and the same open on the `Spec`
side, the glue data of an affine cover with distinguished
overlaps together with the morphisms out of the space it glues to and the same glue data on the
`Spec` side, the image of the analytification in `ℂ^n`, and the family of
monic polynomials of a polynomial monic in the last variable, with the finiteness over `ℂ^n`
that it supplies, the glue of a refined overlap that meets two different members of the
original cover with the symmetry law it satisfies, the square saying that the refined
transition lies over the original cover's own transition, and that the refined datum refines the
space it refines — at the pairs whose refined members lie over one member of the original, at the
pairs where they lie over two, and at a family of extra factors at which both hold at once.

See `OkaTest/Axioms.lean` for what these assertions are for and how to update one.
-/

/-! ### The comparison morphism `ℂ^ι ⟶ Spec (MvPolynomial ι ℂ)` -/

/--
info: 'complexSpaceToSpec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms complexSpaceToSpec

/--
info: 'mem_complexSpaceToSpec_base_asIdeal_iff' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms mem_complexSpaceToSpec_base_asIdeal_iff

/--
info: 'isMaximal_complexSpaceToSpec_base_asIdeal' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isMaximal_complexSpaceToSpec_base_asIdeal

/--
info: 'complexSpaceToSpec_base_injective' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms complexSpaceToSpec_base_injective

/--
info: 'complexAffineSpaceToAffineSpace' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms complexAffineSpaceToAffineSpace

/-! ### The stalk map of the comparison morphism -/

/--
info: 'toStalk_stalkMap_complexSpaceToSpec' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms toStalk_stalkMap_complexSpaceToSpec

/--
info: 'okaStalkEquiv_stalkMap_complexSpaceToSpec' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms okaStalkEquiv_stalkMap_complexSpaceToSpec

/--
info: 'isUnit_ofMvPolynomial_of_mem_primeCompl' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isUnit_ofMvPolynomial_of_mem_primeCompl

/--
info: 'stalkMap_eq_lift' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms stalkMap_eq_lift

/-! ### The analytification of a presented affine `ℂ`-algebra

`Oka/Analytification/Presentation.lean`. The guard for
`AlgebraicGeometry.LocallyRingedSpace.toΓSpec_naturality`, which that file consumes, is in
`OkaTest/Axioms/Sheaves.lean` with the rest of the mirror-tree `LocallyRingedSpace` material;
it sat here while PR #71 was in the merge queue, to keep two branches from appending to the
same file's tail, and that reason has expired. -/

/--
info: 'ComplexAnalytic.AnalyticSpace.analytification' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.analytification

/--
info: 'ComplexAnalytic.mem_zeroLocus_polySection_iff' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.mem_zeroLocus_polySection_iff

/--
info: 'ComplexAnalytic.AnalyticSpace.mem_toΓSpec_base_asIdeal_iff' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.mem_toΓSpec_base_asIdeal_iff

/--
info: 'ComplexAnalytic.analytificationToSpec' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.analytificationToSpec

/--
info: 'ComplexAnalytic.mem_analytificationToSpec_base_asIdeal_iff' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.mem_analytificationToSpec_base_asIdeal_iff

/--
info: 'ComplexAnalytic.analytificationToSpec_base_asIdeal' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.analytificationToSpec_base_asIdeal

/--
info: 'ComplexAnalytic.isMaximal_analytificationToSpec_base_asIdeal' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isMaximal_analytificationToSpec_base_asIdeal

/--
info: 'ComplexAnalytic.analytificationToSpec_base_injective' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.analytificationToSpec_base_injective

/--
info: 'ComplexAnalytic.analytificationToSpec_comp_specMk' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.analytificationToSpec_comp_specMk

/-! ### The universal property of the analytification -/

/--
info: 'ComplexAnalytic.Γ_map_comp_ofMvPolynomial' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.Γ_map_comp_ofMvPolynomial

/--
info: 'ComplexAnalytic.analytificationInclHom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.analytificationInclHom

/--
info: 'ComplexAnalytic.eval₂_analytificationCoord_eq_zero' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.eval₂_analytificationCoord_eq_zero

/--
info: 'ComplexAnalytic.existsUnique_hom_analytification' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.existsUnique_hom_analytification

/--
info: 'ComplexAnalytic.hom_ext_analytification' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.hom_ext_analytification

/--
info: 'ComplexAnalytic.analytificationIsoOfPresentationIdealEq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.analytificationIsoOfPresentationIdealEq

/-! ### The local ring at the origin and its completion

`Oka/Analytification/LocalRing.lean`. `polyLocalAdicCompletionEquiv_of_algebraMap` is guarded
alongside the isomorphism because it is what says the isomorphism is the one induced by the
inclusion of polynomials. -/

/--
info: 'ComplexAnalytic.polyLocalToMvPowerSeries' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.polyLocalToMvPowerSeries

/--
info: 'ComplexAnalytic.polyLocalAdicCompletionEquiv' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.polyLocalAdicCompletionEquiv

/--
info: 'ComplexAnalytic.polyLocalAdicCompletionEquiv_of_algebraMap' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.polyLocalAdicCompletionEquiv_of_algebraMap

/--
info: 'ComplexAnalytic.flat_polyLocalToMvPowerSeries' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.flat_polyLocalToMvPowerSeries

/-! ### The germs are faithfully flat over the local ring at the origin

`Oka/Analytification/Flatness.lean`. `coe_polyLocalToGerm` is guarded alongside the flatness
because it is what makes the two maps out of `ℂ[x]_{(x)}` into a scalar tower; without it the
descent has nothing to run in. -/

/--
info: 'ComplexAnalytic.polyLocalToGerm' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.polyLocalToGerm

/--
info: 'ComplexAnalytic.coe_polyLocalToGerm' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coe_polyLocalToGerm

/--
info: 'ComplexAnalytic.flat_polyLocalToGerm' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.flat_polyLocalToGerm

/--
info: 'ComplexAnalytic.faithfullyFlat_polyLocalToGerm' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.faithfullyFlat_polyLocalToGerm

/-! ### The same at an arbitrary point, and for the geometric stalk map

`Oka/Analytification/FlatnessAtAPoint.lean`. `polyLocalToGermAt_eq_comp` is guarded alongside the
two flatness statements because it is the *only* mathematical step between them and the results
at the origin — everything else in that file is transport — and
`LocalOkaRing.ofMvPolynomial_taylorAlgHom` because it is in turn the only step in it that is
about germs rather than about localisations. -/

/--
info: 'MvPolynomial.map_taylorEquiv_primeCompl' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MvPolynomial.map_taylorEquiv_primeCompl

/--
info: 'LocalOkaRing.ofMvPolynomial_taylorAlgHom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LocalOkaRing.ofMvPolynomial_taylorAlgHom

/-! ### The Taylor coefficients of a shifted polynomial, and of a germ

`Oka/Algebra/MvPolynomial/Taylor.lean`, `Oka/Algebra/MvPolynomial/PDeriv.lean` and
`Oka/Polynomial/Germ.lean`. The two mirror-tree statements read the constant and the linear
coefficient of `p(x + z)` — the second as a partial derivative — and the two after them are what
carries that to a germ: at the origin the germ of a polynomial *is* the polynomial, and so the
linear coefficient of the germ at any point is a partial derivative there. They are guarded under
this heading rather than in `OkaTest/Axioms/RingTheory.lean` for the reason
`MvPolynomial.map_taylorEquiv_primeCompl` above is: their consumer is the germ of a polynomial,
which is what this file's routing row covers. -/

/--
info: 'MvPolynomial.constantCoeff_taylorAlgHom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MvPolynomial.constantCoeff_taylorAlgHom

/--
info: 'MvPolynomial.coeff_single_one_taylorAlgHom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MvPolynomial.coeff_single_one_taylorAlgHom

/--
info: 'LocalOkaRing.ofMvPolynomial_zero_X' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LocalOkaRing.ofMvPolynomial_zero_X

/--
info: 'LocalOkaRing.coe_ofMvPolynomial_zero' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LocalOkaRing.coe_ofMvPolynomial_zero

/--
info: 'LocalOkaRing.coeff_single_one_ofMvPolynomial' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LocalOkaRing.coeff_single_one_ofMvPolynomial

/--
info: 'ComplexAnalytic.polyLocalToGermAt' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.polyLocalToGermAt

/--
info: 'ComplexAnalytic.polyLocalToGermAt_eq_comp' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.polyLocalToGermAt_eq_comp

/--
info: 'ComplexAnalytic.faithfullyFlat_polyLocalToGermAt' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.faithfullyFlat_polyLocalToGermAt

/--
info: 'ComplexAnalytic.okaStalkEquiv_comp_stalkMap' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.okaStalkEquiv_comp_stalkMap

/--
info: 'ComplexAnalytic.faithfullyFlat_stalkMap_complexSpaceToSpec' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.faithfullyFlat_stalkMap_complexSpaceToSpec

/-! ### Presentation-independence -/

/--
info: 'ComplexAnalytic.eval₂Hom_transported' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.eval₂Hom_transported

/--
info: 'ComplexAnalytic.analytificationMap' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.analytificationMap

/--
info: 'ComplexAnalytic.analytificationMap_comp' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.analytificationMap_comp

/--
info: 'ComplexAnalytic.analytificationIsoOfPresHom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.analytificationIsoOfPresHom

/--
info: 'ComplexAnalytic.PresHom.ofRename' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.PresHom.ofRename

/--
info: 'ComplexAnalytic.PresHom.ofRename_comp_ofRename' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.PresHom.ofRename_comp_ofRename

/-! ### The analytification as a functor -/

/--
info: 'ComplexAnalytic.analytificationFunctor' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.analytificationFunctor

/--
info: 'ComplexAnalytic.Presentation.isoOfRename' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.Presentation.isoOfRename

/--
info: 'ComplexAnalytic.Presentation.algEquivOfIso' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.Presentation.algEquivOfIso

/--
info: 'ComplexAnalytic.Presentation.isoOfAlgEquiv_algEquivOfIso' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.Presentation.isoOfAlgEquiv_algEquivOfIso

/--
info: 'ComplexAnalytic.Presentation.algEquivOfIso_isoOfAlgEquiv' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.Presentation.algEquivOfIso_isoOfAlgEquiv

/--
info: 'ComplexAnalytic.exists_presentation' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.exists_presentation

/--
info: 'ComplexAnalytic.finiteType_presentationAlg' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.finiteType_presentationAlg

/--
info: 'ComplexAnalytic.toFGAlg' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.toFGAlg

/--
info: 'ComplexAnalytic.toFGAlgFullyFaithful' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.toFGAlgFullyFaithful

/--
info: 'ComplexAnalytic.analytificationFGAlg' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.analytificationFGAlg

/--
info: 'ComplexAnalytic.analytificationFGAlgCompIso' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.analytificationFGAlgCompIso

/--
info: 'ComplexAnalytic.analytificationFGAlgObjIso' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.analytificationFGAlgObjIso

/-! ### The stalk map of `X^an ⟶ Spec (ℂ[x] ⧸ I)`

`Oka/Analytification/PresentationStalk.lean`. -/

/--
info: 'ComplexAnalytic.quotientToGerm' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.quotientToGerm

/--
info: 'ComplexAnalytic.toStalk_stalkMap_analytificationToSpec' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.toStalk_stalkMap_analytificationToSpec

/--
info: 'ComplexAnalytic.isUnit_quotientToGerm_iff' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isUnit_quotientToGerm_iff

/--
info: 'ComplexAnalytic.stalkMap_analytificationToSpec_eq_lift' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.stalkMap_analytificationToSpec_eq_lift

/--
info: 'ComplexAnalytic.algebraMapSubmonoid_primeCompl_eq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.algebraMapSubmonoid_primeCompl_eq

/--
info: 'ComplexAnalytic.analytificationStalkQuotEquiv' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.analytificationStalkQuotEquiv

/-! ### The comparison morphism is natural

`Oka/Analytification/Comparison.lean`. The component lemmas are guarded alongside the two natural
transformations because a transformation whose components nobody can compute is inert, which is
the same obligation `ComplexAnalytic.analytificationFGAlgObjIso` discharges above. -/

/--
info: 'ComplexAnalytic.analytificationToSpec_naturality' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.analytificationToSpec_naturality

/--
info: 'ComplexAnalytic.analytificationToSpecNatTrans' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.analytificationToSpecNatTrans

/--
info: 'ComplexAnalytic.analytificationToSpecNatTrans_app' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.analytificationToSpecNatTrans_app

/--
info: 'ComplexAnalytic.specFunctor' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.specFunctor

/--
info: 'ComplexAnalytic.specFunctor_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.specFunctor_eq

/--
info: 'ComplexAnalytic.analytificationFGAlgToSpec' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.analytificationFGAlgToSpec

/--
info: 'ComplexAnalytic.analytificationFGAlgToSpec_app' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.analytificationFGAlgToSpec_app

/-! ### The analytification of a sheaf

`Oka/Analytification/Sheaf.lean`, and the general pullback of `𝒪`-modules along a morphism of
locally ringed spaces it is built from. -/

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.Hom.toRingSheafHom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.Hom.toRingSheafHom

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.Hom.pullbackModules' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.Hom.pullbackModules

/--
info: 'ComplexAnalytic.analytificationSheaf' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.analytificationSheaf

/--
info: 'ComplexAnalytic.analytificationSheafAdj' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.analytificationSheafAdj

/--
info: 'ComplexAnalytic.preservesColimits_analytificationSheaf' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.preservesColimits_analytificationSheaf

/--
info: 'ComplexAnalytic.analytificationSheafUnitToUnit' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.analytificationSheafUnitToUnit

/--
info: 'ComplexAnalytic.analytificationFGAlgObjIso_hom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.analytificationFGAlgObjIso_hom

/--
info: 'ComplexAnalytic.analytificationFGAlgToSpec_app_toFGAlg_obj' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.analytificationFGAlgToSpec_app_toFGAlg_obj

/-! ### The germ of a polynomial, and the flatness of the stalk map of `X^an ⟶ Spec (ℂ[x] ⧸ I)`

`Oka/Analytification/FlatnessAtAPoint.lean` and `Oka/Analytification/PresentationFlatness.lean`.
`ComplexAnalytic.injective_germOfMvPolynomial` is guarded alongside the flatness because it is
what the non-vacuity test rests on, and `ComplexAnalytic.stalkMap_analytificationToSpec_eq_comp`
because a flatness deduced through three identifications is only as good as the square that says
they commute. -/

/--
info: 'ComplexAnalytic.germOfMvPolynomial' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.germOfMvPolynomial

/--
info: 'ComplexAnalytic.injective_germOfMvPolynomial' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.injective_germOfMvPolynomial

/--
info: 'ComplexAnalytic.ker_stalkMap_analytificationIncl' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.ker_stalkMap_analytificationIncl

/--
info: 'ComplexAnalytic.germQuotEquivStalk' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.germQuotEquivStalk

/--
info: 'ComplexAnalytic.germQuotEquivStalk_mk_germOfMvPolynomial' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.germQuotEquivStalk_mk_germOfMvPolynomial

/--
info: 'ComplexAnalytic.stalkMap_analytificationToSpec_eq_comp' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.stalkMap_analytificationToSpec_eq_comp

/--
info: 'ComplexAnalytic.faithfullyFlat_stalkMap_analytificationToSpec' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.faithfullyFlat_stalkMap_analytificationToSpec

/--
info: 'ComplexAnalytic.flat_stalkMap_analytificationToSpec' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.flat_stalkMap_analytificationToSpec

/-! ### GAGA's local half: the analytification of a sheaf is exact -/

/--
info: 'ComplexAnalytic.preservesFiniteLimits_analytificationSheaf' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.preservesFiniteLimits_analytificationSheaf

/-! ### The analytification of `𝒪_X` is `𝒪_{X^an}` -/

/--
info: 'TopologicalSpace.Opens.final_map' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TopologicalSpace.Opens.final_map

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.isIso_pullbackModulesUnitToUnit' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.isIso_pullbackModulesUnitToUnit

/--
info: 'ComplexAnalytic.analytificationSheafUnitIso' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.analytificationSheafUnitIso

/--
info: 'ComplexAnalytic.analytificationSheafFreeIso' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.analytificationSheafFreeIso


/-! ### The analytification of a distinguished open -/

/--
info: 'ComplexAnalytic.AnalyticSpace.pullbackΓ_eval₂' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.pullbackΓ_eval₂

/--
info: 'ComplexAnalytic.localisationIso' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.localisationIso

/--
info: 'ComplexAnalytic.localisationIso_hom_ofRestrict' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.localisationIso_hom_ofRestrict

/--
info: 'ComplexAnalytic.localisationIso_inv_localisationProj' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.localisationIso_inv_localisationProj

/--
info: 'ComplexAnalytic.eval_localisationProj' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.eval_localisationProj

/--
info: 'ComplexAnalytic.base_localisationProj' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.base_localisationProj

/--
info: 'ComplexAnalytic.localisationOpen_ne_top' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.localisationOpen_ne_top

/-! ### The analytification of a coherent sheaf is coherent

`Oka/Analytification/SheafCoherent.lean`, whose title this header now matches: it used to read
*the analytification of a finitely presented sheaf*, which was that file's title until the
coherent statement was added, and which under-described the last of the guards below.

`ComplexAnalytic.AnalyticSpace.isCoherent_free` is the one of them that lives elsewhere
(`Oka/AnalyticSpace/Coherent.lean`); it is Oka's theorem in every finite rank, and the others
rest on it. -/

/--
info: 'ComplexAnalytic.AnalyticSpace.isCoherent_free' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.isCoherent_free

/--
info: 'ComplexAnalytic.isCoherent_analytificationSheaf_cokernel' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isCoherent_analytificationSheaf_cokernel

/--
info: 'ComplexAnalytic.isCoherent_analytificationSheaf_cokernel_sectionsHom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isCoherent_analytificationSheaf_cokernel_sectionsHom

/--
info: 'ComplexAnalytic.isCoherent_analytificationSheaf_of_isCoherent' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isCoherent_analytificationSheaf_of_isCoherent

/-! ### The distinguished open, through the functor -/

/--
info: 'ComplexAnalytic.rename_localisationIncl_mem' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.rename_localisationIncl_mem

/--
info: 'ComplexAnalytic.localisationPresHom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.localisationPresHom

/--
info: 'ComplexAnalytic.analytificationMap_localisationPresHom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.analytificationMap_localisationPresHom

/--
info: 'ComplexAnalytic.localisationIso_inv_analytificationMap' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.localisationIso_inv_analytificationMap

/-! ### The projection is an open immersion -/

/--
info: 'ComplexAnalytic.isOpenImmersion_localisationProj' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isOpenImmersion_localisationProj

/--
info: 'ComplexAnalytic.isOpenImmersion_analytificationMap_localisationPresHom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isOpenImmersion_analytificationMap_localisationPresHom

/-! ### Two polynomials cutting out the same distinguished open, up to a unit

The four statements `Oka/Analytification/LocalisationIndependence.lean` gained for the
cross-member overlap of a refinement: the isomorphism at a **unit multiple** and its triangle,
that the inverted polynomial is a unit upstairs, and that every polynomial of a localisation is a
unit multiple of a renamed one.

**That file's `…OfDvdPow` block is unguarded and this heading does not retrofit it** —
`ComplexAnalytic.localisationPresentedAlgebraEquivOfDvdPow`,
`ComplexAnalytic.localisationPresentationIsoOfDvdPow`,
`ComplexAnalytic.localisationPresentedAlgebraEquivOfDvdPow_localisationRingHom` and
`ComplexAnalytic.localisationPresentationIsoOfDvdPow_hom_comp`, together with
`ComplexAnalytic.localisationRenameEquiv_localisationRingHom` and
`ComplexAnalytic.localisationPresentedAlgebraEquiv_localisationRingHom` above them. They are
unguarded because the file has no `## Main results` heading — its list of statements sits under
the title — so `scripts/guard_coverage.py` reads nothing from it in either direction, and the
guards below land in *guarded and advertised nowhere* rather than in the overlap. Guarding what a
branch adds is this project's practice; guarding declarations a branch does not touch is another
branch's business.

**The clause this replaces counted, and which set it counted was the whole question.** It read
*"That file's other four declarations are unguarded"*, written at `900c9d7`: true of that file's
*advertised* statements at that commit and false of its declarations, which were already more.
The names above are of the declarations, which is the reading a reader can check. -/

/--
info: 'ComplexAnalytic.localisationPresentationIsoOfUnitMul' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.localisationPresentationIsoOfUnitMul

/--
info: 'ComplexAnalytic.localisationPresentationIsoOfUnitMul_hom_comp' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.localisationPresentationIsoOfUnitMul_hom_comp

/--
info: 'ComplexAnalytic.isUnit_mk_rename_localisationIncl' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isUnit_mk_rename_localisationIncl

/--
info: 'ComplexAnalytic.exists_mk_rename_eq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.exists_mk_rename_eq

/-! ### The same distinguished open of two *different* members

The two statements `Oka/Analytification/LocalisationIndependence.lean` gained for the step after
the block above: an isomorphism of two presented algebras carrying one cutting polynomial to the
other identifies the two localisations, and the identification is one over that isomorphism.
Everything in the block above keeps the base fixed and varies the polynomial; these vary the base.

The same sentence as that heading applies to the coverage figures: that file still has no
`## Main results` heading, so these land in *guarded and advertised nowhere* rather than in the
overlap, and the declarations the heading above names as unguarded are still unguarded.

**The clause this replaces was false at the commit that wrote it.** It read *"the file's original
eight stay unguarded"*, written at `e54b1c3`; at that commit eight of that file's declarations
were guarded and six were not, and the six are the ones named one heading up. -/

/--
info: 'ComplexAnalytic.localisationPresentedAlgebraEquivOfAlgEquiv' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.localisationPresentedAlgebraEquivOfAlgEquiv

/--
info: 'ComplexAnalytic.localisationPresentedAlgebraEquivOfAlgEquiv_localisationRingHom' depends on
  axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.localisationPresentedAlgebraEquivOfAlgEquiv_localisationRingHom

/--
info: 'ComplexAnalytic.localisationPresentationIsoOfAlgEquiv' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.localisationPresentationIsoOfAlgEquiv

/--
info: 'ComplexAnalytic.localisationPresentationIsoOfAlgEquiv_hom_comp' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.localisationPresentationIsoOfAlgEquiv_hom_comp

/-! ### The same distinguished open on the `Spec` side

`Oka/Analytification/SpecDistinguishedOpen.lean`, the mirror of
`### Two polynomials cutting out the same distinguished open, up to a unit` and
`### The same distinguished open of two *different* members`. The triangle is guarded beside
`ComplexAnalytic.isOpenImmersion_Spec_map_localisationRingHom` and
`ComplexAnalytic.isOpenImmersion_specFunctor_map_localisationHom` because it is the only thing
either of them uses, and the isomorphism is guarded because a triangle over an identification
nobody can name is inert.

The range and the isomorphism with the open subspace are under the same heading rather than one
of their own: they are the same distinguished open, and the open immersion is what makes both of
them statable. -/

/--
info: 'ComplexAnalytic.specLocalisationRingIso' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.specLocalisationRingIso

/--
info: 'ComplexAnalytic.localisationRingHom_comp_eq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.localisationRingHom_comp_eq

/--
info: 'ComplexAnalytic.isOpenImmersion_Spec_map_localisationRingHom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isOpenImmersion_Spec_map_localisationRingHom

/--
info: 'ComplexAnalytic.isOpenImmersion_specFunctor_map_localisationHom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isOpenImmersion_specFunctor_map_localisationHom

/--
info: 'ComplexAnalytic.specLocalisationOpen' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.specLocalisationOpen

/--
info: 'ComplexAnalytic.range_base_specFunctor_map_localisationHom' depends on
  axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.range_base_specFunctor_map_localisationHom

/--
info: 'ComplexAnalytic.specLocalisationIso' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.specLocalisationIso

/--
info: 'ComplexAnalytic.specLocalisationIso_hom_ofRestrict' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.specLocalisationIso_hom_ofRestrict

/--
info: 'ComplexAnalytic.specLocalisationIso_inv_specFunctor_map' depends on
  axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.specLocalisationIso_inv_specFunctor_map

/-! ### The glue data of an affine cover with distinguished overlaps

The `ComplexAnalytic.localisationOpen` lemmas are guarded under this heading rather than under
`### The analytification of a distinguished open` because this heading is what they are for.
`ComplexAnalytic.localisationOpen_mul` is the triple overlap;
`ComplexAnalytic.localisationOpen_rename` is the overlap of a refined member read upstairs; and
`ComplexAnalytic.exists_localisationOpen_eq_rename`, the converse of that one for every
distinguished open at once, is what says an overlap cut out of a *localisation* still needs only
one polynomial — the arity a cover datum asks for.
`ComplexAnalytic.exists_pow_mul_eq_rename` and
`ComplexAnalytic.eval_rename_localisationIncl_ne_zero` are what its proof calls,
`ComplexAnalytic.eq_localisationVar_or_exists_localisationIncl` is what
`ComplexAnalytic.exists_pow_mul_eq_rename` calls in turn, and
`ComplexAnalytic.exists_localisationOpen_eq_comap` is its `Opens.map` form; they are guarded
beside it.

`Oka/Analytification/DistinguishedOpenPullback.lean`'s advertised results are guarded next —
`ComplexAnalytic.pullbackΓ_analytificationMap_polyToGlobal`,
`ComplexAnalytic.localisationOpen_eq_comap_analytificationMap`,
`ComplexAnalytic.exists_localisationOpen_eq_comap_analytificationMap` and
`ComplexAnalytic.exists_comap_analytificationMap_eq_comap_localisationProj` — and they belong
under this heading for the same reason: a distinguished open pulls back along
`ComplexAnalytic.analytificationMap` to a distinguished open, which is what says the overlap an
overlap is *transported* to is still one of the opens a cover datum can name.
`ComplexAnalytic.exists_comap_analytificationMap_eq_comap_localisationProj` is that composed with
`ComplexAnalytic.exists_localisationOpen_eq_comap`, and is the pair's conclusion.
-/

/--
info: 'ComplexAnalytic.localisationOpen_mul' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.localisationOpen_mul

/--
info: 'ComplexAnalytic.localisationOpen_rename' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.localisationOpen_rename

/--
info: 'ComplexAnalytic.eq_localisationVar_or_exists_localisationIncl' depends on axioms:
  [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.eq_localisationVar_or_exists_localisationIncl

/--
info: 'ComplexAnalytic.exists_pow_mul_eq_rename' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.exists_pow_mul_eq_rename

/--
info: 'ComplexAnalytic.eval_rename_localisationIncl_ne_zero' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.eval_rename_localisationIncl_ne_zero

/--
info: 'ComplexAnalytic.exists_localisationOpen_eq_rename' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.exists_localisationOpen_eq_rename

/--
info: 'ComplexAnalytic.exists_localisationOpen_eq_comap' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.exists_localisationOpen_eq_comap

/--
info: 'ComplexAnalytic.pullbackΓ_analytificationMap_polyToGlobal' depends on
  axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.pullbackΓ_analytificationMap_polyToGlobal

/--
info: 'ComplexAnalytic.localisationOpen_eq_comap_analytificationMap' depends on
  axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.localisationOpen_eq_comap_analytificationMap

/--
info: 'ComplexAnalytic.exists_localisationOpen_eq_comap_analytificationMap' depends
  on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.exists_localisationOpen_eq_comap_analytificationMap

/--
info: 'ComplexAnalytic.exists_comap_analytificationMap_eq_comap_localisationProj'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.exists_comap_analytificationMap_eq_comap_localisationProj

/--
info: 'ComplexAnalytic.range_base_localisationProj' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.range_base_localisationProj

/--
info: 'ComplexAnalytic.coverOverlapIso_hom_coverIncl' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverOverlapIso_hom_coverIncl

/--
info: 'ComplexAnalytic.coverTransition' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverTransition

/--
info: 'ComplexAnalytic.coverTriple' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverTriple

/--
info: 'ComplexAnalytic.range_coverTransitionHom_subset' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.range_coverTransitionHom_subset

/--
info: 'ComplexAnalytic.range_comp_coverTransitionHom_subset' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.range_comp_coverTransitionHom_subset

/--
info: 'ComplexAnalytic.coverGlueData' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverGlueData

/--
info: 'ComplexAnalytic.coverGlueData_U' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverGlueData_U

/--
info: 'ComplexAnalytic.comapAlgMap_coverOverlapIso' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.comapAlgMap_coverOverlapIso

/--
info: 'ComplexAnalytic.comapAlgMap_coverGlueIso' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.comapAlgMap_coverGlueIso

/--
info: 'ComplexAnalytic.comapAlgMap_coverIncl_eq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.comapAlgMap_coverIncl_eq

/--
info: 'ComplexAnalytic.glueDataCLinear_coverGlueData' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.glueDataCLinear_coverGlueData

/--
info: 'ComplexAnalytic.coverAnalytification_toLocallyRingedSpace' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverAnalytification_toLocallyRingedSpace

/--
info: 'ComplexAnalytic.isOpenImmersion_coverIota' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isOpenImmersion_coverIota

/--
info: 'ComplexAnalytic.coverIota' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverIota

/--
info: 'ComplexAnalytic.coverAnalytificationOpenCover_obj' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverAnalytificationOpenCover_obj

/--
info: 'ComplexAnalytic.coverAnalytificationOpenCover_map' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverAnalytificationOpenCover_map

/-! #### Morphisms out of `X^an`

`ComplexAnalytic.coverGlueMorphisms`, the statements that make it usable and the ones that record
its round trip: `ComplexAnalytic.comm_coverGlueData`,
`ComplexAnalytic.toLRSHom_coverGlueMorphisms`,
`ComplexAnalytic.coverIota_comp_coverGlueMorphisms`,
`ComplexAnalytic.coverAnalytification_hom_ext`, `ComplexAnalytic.coverIncl_comp_coverIota`,
`ComplexAnalytic.coverGlueMorphisms_coverIota` and
`ComplexAnalytic.coverGlueMorphisms_eq_glueMorphismsOfGlueData`.
They belong with the block above rather than in one of their own: the cover is what
`ComplexAnalytic.AnalyticSpace.glueMorphisms` consumes and these are what supply its hypothesis,
so `ComplexAnalytic.coverAnalytificationOpenCover_obj` and `…_map` directly above are the same
line of statements one step earlier.
-/

/--
info: 'ComplexAnalytic.comm_coverGlueData' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.comm_coverGlueData

/--
info: 'ComplexAnalytic.coverGlueMorphisms' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverGlueMorphisms

/--
info: 'ComplexAnalytic.toLRSHom_coverGlueMorphisms' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.toLRSHom_coverGlueMorphisms

/--
info: 'ComplexAnalytic.coverIota_comp_coverGlueMorphisms' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverIota_comp_coverGlueMorphisms

/--
info: 'ComplexAnalytic.coverAnalytification_hom_ext' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverAnalytification_hom_ext

/--
info: 'ComplexAnalytic.coverIncl_comp_coverIota' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverIncl_comp_coverIota

/--
info: 'ComplexAnalytic.coverGlueMorphisms_coverIota' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverGlueMorphisms_coverIota

/--
info: 'ComplexAnalytic.coverGlueMorphisms_eq_glueMorphismsOfGlueData' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverGlueMorphisms_eq_glueMorphismsOfGlueData

/-! ### The glue data of the members' `Spec`s

`Oka/Analytification/SpecAffineCover.lean`, the mirror of the block above with
`ComplexAnalytic.specFunctor` in place of the analytification. It is a heading of its own rather
than part of that block because the two constructions share an *input* and nothing else: neither
file's declarations appear in the other's statements — and that is still true now that the file
which relates them exists. It is `Oka/Analytification/CoverComparison.lean`, guarded below under a
heading of its own: it names declarations from both of these blocks, neither of these blocks names
anything of the other's, and so it takes a third heading rather than pulling either of these two
under the other.

**This paragraph has now been wrong twice, in the two ways this file goes wrong.** It read "the
file that will relate them … does not exist yet" until that file arrived, which is an absence a
heading was justified by and the next branch retired; and its replacement said that file was "the
last block below", which was a *position* and was false on the day it was written. The heading is
named and not pointed at for that reason, and the paragraph under that heading says the same thing
from the other side.

`ComplexAnalytic.range_specTransitionHom_subset` and its composite are guarded because
`ComplexAnalytic.specTriple` consumes the second of them: it supplies the `D(f_ji)` half of
`AlgebraicGeometry.LocallyRingedSpace.liftRestrict`'s obligation so that `hrange` does not have to
ask for it. **They were guarded before anything consumed them** — as the evidence for the file's
claim that half of that hypothesis is free — and the analytic mirrors added alongside them in the
block above stand in the same relation to `ComplexAnalytic.coverTriple`.
-/

/--
info: 'ComplexAnalytic.specOverlapIso' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.specOverlapIso

/--
info: 'ComplexAnalytic.specTransition' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.specTransition

/--
info: 'ComplexAnalytic.specGlueIso_symm' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.specGlueIso_symm

/--
info: 'ComplexAnalytic.range_specTransitionHom_subset' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.range_specTransitionHom_subset

/--
info: 'ComplexAnalytic.range_comp_specTransitionHom_subset' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.range_comp_specTransitionHom_subset

/--
info: 'ComplexAnalytic.specTriple' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.specTriple

/--
info: 'ComplexAnalytic.specTriple_fac' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.specTriple_fac

/--
info: 'ComplexAnalytic.specGlueData'' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.specGlueData'

/--
info: 'ComplexAnalytic.specGlueData' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.specGlueData

/--
info: 'ComplexAnalytic.specGlueData_U' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.specGlueData_U

/--
info: 'ComplexAnalytic.specGlued' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.specGlued

/--
info: 'ComplexAnalytic.specIota' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.specIota

/--
info: 'ComplexAnalytic.isOpenImmersion_specIota' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isOpenImmersion_specIota

/--
info: 'ComplexAnalytic.specIncl_comp_specIota' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.specIncl_comp_specIota

/--
info: 'ComplexAnalytic.specGluedOpenCover' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.specGluedOpenCover

/--
info: 'ComplexAnalytic.specGluedOpenCover_obj' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.specGluedOpenCover_obj

/--
info: 'ComplexAnalytic.specGluedOpenCover_map' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.specGluedOpenCover_map

/-! ### A morphism of covered schemes analytifies

The definitions and results of `Oka/Analytification/CoverFunctoriality.lean`, which is the
morphism *between* two gluings of the kind `### The glue data of an affine cover with distinguished
overlaps` builds. A heading of its own rather than a `####` under that one, because its subject is
a morphism of two covers where everything there is one cover; under this file's topic heading at
all, because `ComplexAnalytic.coverGlueMorphisms` is what it is built from and
`OkaTest/Axioms.lean`'s routing rule puts a file's guards under the heading its topic belongs to.

**Named by heading and not by position**, which is not a stylistic preference: this block and the
`Spec`-side glue-data block above it were written against the same anchor by two branches that did
not know about each other, so whichever landed second would have carried a false "the block above"
had it pointed rather than named. That block does point, and it is still right — it sits directly
under the block it names, and nothing may be inserted between them without repairing its first
sentence.
-/

/--
info: 'ComplexAnalytic.coverMapPart' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverMapPart

/--
info: 'ComplexAnalytic.coverMap' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverMap

/--
info: 'ComplexAnalytic.coverIota_comp_coverMap' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverIota_comp_coverMap

/--
info: 'ComplexAnalytic.coverMap_unique' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverMap_unique

/--
info: 'ComplexAnalytic.comm_coverMapPart_id' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.comm_coverMapPart_id

/--
info: 'ComplexAnalytic.coverMap_id' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverMap_id

/--
info: 'ComplexAnalytic.comm_coverMapPart_comp' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.comm_coverMapPart_comp

/--
info: 'ComplexAnalytic.coverMap_comp' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverMap_comp

/-! ### The comparison morphism `X^an ⟶ X`

The definitions and results of `Oka/Analytification/CoverComparison.lean`, together with
`ComplexAnalytic.toLRSHom_localisationProj_comp_analytificationToSpec`, which that file declares
and does not advertise: the morphism from the gluing
`### The glue data of an affine cover with distinguished overlaps` builds to the gluing
`### The glue data of the members' `Spec`s` builds. It is a heading of its own rather than a
`####` under either because it is about neither cover on its own: its input is one datum and its
content is that the affine comparison morphism is natural enough to descend to it. Placed after
both blocks it consumes, and **named by heading rather than by position**, which is what the
blocks above cannot be revised into cheaply: `"the block above"` points at a block in
`### The same distinguished open of two *different* members`, in
`#### Morphisms out of `X^an`` and in `### The glue data of the members' `Spec`s`, and every
one of them is true — each really does sit under the block it names. That is the hazard, not a
contradiction: a pointer is true only relative to a position, so every one of them constrains what
may be inserted where, and a name constrains nothing.

**The figure this replaces was exact when written and is not now.** It read *"occurs three times
up there"*, written at `dd7e70e`, when three was the number of them; the localisation-independence
blocks were appended above afterwards, carry pointers of their own, and nothing swept this
sentence.
-/

/--
info: 'ComplexAnalytic.toLRSHom_localisationProj_comp_analytificationToSpec' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.toLRSHom_localisationProj_comp_analytificationToSpec

/--
info: 'ComplexAnalytic.comparisonPart' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.comparisonPart

/--
info: 'ComplexAnalytic.coverIncl_comp_analytificationToSpec' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverIncl_comp_analytificationToSpec

/--
info: 'ComplexAnalytic.comparisonPart_comp_specTransition' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.comparisonPart_comp_specTransition

/--
info: 'ComplexAnalytic.comparisonPartIota' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.comparisonPartIota

/--
info: 'ComplexAnalytic.comm_comparisonPartIota' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.comm_comparisonPartIota

/--
info: 'ComplexAnalytic.analytificationToSpecGlued' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.analytificationToSpecGlued

/--
info: 'ComplexAnalytic.toLRSHom_coverIota_comp_analytificationToSpecGlued' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.toLRSHom_coverIota_comp_analytificationToSpecGlued

/--
info: 'ComplexAnalytic.analytificationToSpecGlued_unique' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.analytificationToSpecGlued_unique

/-! ### Two cover data with isomorphic members give the same `X^an`

The definitions and results of `Oka/Analytification/CoverIndependence.lean`, the first two
instalments of taxis #1107. It is a heading of its own rather than a `####` under
`### A morphism of covered schemes analytifies`, whose `ComplexAnalytic.coverMap` it is built
from, because its subject is two data for *one* gluing where that block's is a morphism between
two gluings — and it is placed after the blocks it consumes for the same reason that one gives,
**named by heading and not by position**.

**The same-index pair is guarded on its own account even though it is an instance of the
reindexed pair**, which that file measures and says: `ComplexAnalytic.coverMap_hom_inv` is
`ComplexAnalytic.coverMap_reindex_hom_inv` at `Equiv.refl` with no coercion at all. A guard on an
advertised name is a statement about that name, and the census
`scripts/guard_coverage.py` reports counts advertised names rather than distinct facts, so
dropping either pair here would open a gap without removing a claim.
-/

/--
info: 'ComplexAnalytic.coverMap_hom_inv' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverMap_hom_inv

/--
info: 'ComplexAnalytic.coverMap_inv_hom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverMap_inv_hom

/--
info: 'ComplexAnalytic.coverAnalytificationIso' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverAnalytificationIso

/--
info: 'ComplexAnalytic.coverReindexInv' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverReindexInv

/--
info: 'ComplexAnalytic.coverMap_reindex_hom_inv' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverMap_reindex_hom_inv

/--
info: 'ComplexAnalytic.coverMap_reindex_inv_hom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverMap_reindex_inv_hom

/--
info: 'ComplexAnalytic.coverAnalytificationReindexIso' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverAnalytificationReindexIso

/-! ### A morphism of covered schemes on the `Spec` side

The definitions and results of `Oka/Analytification/SpecFunctoriality.lean`, which is to
`### The glue data of the members' `Spec`s` what `### A morphism of covered schemes analytifies` is
to `### The glue data of an affine cover with distinguished overlaps`. A heading of its own for the
reason that block gives about itself: its subject is a morphism of two covers where the glue-data
blocks are each about one.

`ComplexAnalytic.comm_specGlueData` is guarded here and not with the `Spec`-side glue data,
because that is where it is declared — its analytic mirror sits under
`### Morphisms out of `X^an``, which is a `####` inside the analytic glue-data block, and the
`Spec` side has no such section: nothing needed a family out of the members until this file.
-/

/--
info: 'ComplexAnalytic.comm_specGlueData' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.comm_specGlueData

/--
info: 'ComplexAnalytic.specMapPart' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.specMapPart

/--
info: 'ComplexAnalytic.specMap' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.specMap

/--
info: 'ComplexAnalytic.specIota_comp_specMap' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.specIota_comp_specMap

/--
info: 'ComplexAnalytic.specMap_unique' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.specMap_unique

/--
info: 'ComplexAnalytic.comm_specMapPart_id' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.comm_specMapPart_id

/--
info: 'ComplexAnalytic.specMap_id' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.specMap_id

/--
info: 'ComplexAnalytic.comm_specMapPart_comp' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.comm_specMapPart_comp

/--
info: 'ComplexAnalytic.specMap_comp' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.specMap_comp

/-! ### The comparison morphism commutes with a morphism of covered schemes

`Oka/Analytification/ComparisonSquare.lean` —
`ComplexAnalytic.toLRSHom_map_comp_analytificationToSpec` and
`ComplexAnalytic.toLRSHom_coverMap_comp_analytificationToSpecGlued` — the only statement in the
tree that needs `### The comparison morphism `X^an ⟶ X``, `### A morphism of covered schemes
analytifies` and `### A morphism of covered schemes on the `Spec` side` at once, which is why it
is a fourth heading rather than an addition to any of the three, and why it is placed after all of
them.

`ComplexAnalytic.toLRSHom_map_comp_analytificationToSpec` is the naturality square at the member
morphism, and it is guarded although the file states it only to use it: it is the whole content of
the square below, so a proof of the square whose axioms differed from its would mean the square
was proved some other way.
-/

/--
info: 'ComplexAnalytic.toLRSHom_map_comp_analytificationToSpec' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.toLRSHom_map_comp_analytificationToSpec

/--
info: 'ComplexAnalytic.toLRSHom_coverMap_comp_analytificationToSpecGlued' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.toLRSHom_coverMap_comp_analytificationToSpecGlued

/-! ### The two-level index category of a glue data

The advertised results of `Oka/Analytification/GlueShape.lean`, which arrived under `Oka/`
when `ComplexAnalytic.coverAnalytification` gave the shape a consumer. They sit here rather than
in a file of their own because the module is `Oka.Analytification.GlueShape` and
`OkaTest/Axioms.lean`'s table routes `Oka/Analytification/` here — the same row that carries
`ComplexAnalytic.coverGlueData`, under `### The glue data of an affine cover with distinguished
overlaps`, which is what the shape's diagram produces. **That clause read "directly above" until
2026-08-30**, by which time several blocks had been appended between the two — and it is named
rather than pointed at for the reason `### The comparison morphism `X^an ⟶ X`` and
`### Two presentations of each member give the same `X^an`` both give. **The count of blocks
between them is deliberately not stated**: it was four when this was repaired and more by the end
of the same afternoon, which is the whole argument for naming.

`ComplexAnalytic.GlueShape.lift_uniq` says the shape has no morphisms a glue-data diagram does
not account for; `ComplexAnalytic.GlueShape.hsymm_of_hglue` that `hsymm` is a consequence of its
one law; `ComplexAnalytic.GlueShape.not_ctHRange` that `hrange` is **not** a consequence of the
diagram, which is the file's negative result; and
`ComplexAnalytic.GlueShape.hRange_of_no_three` and
`ComplexAnalytic.GlueShape.hCocycle_of_no_three` that neither triple-overlap hypothesis has
content below three members. **Named rather than pointed at from the front**, for the reason the
paragraph above gives about `"directly above"`: an ordinal into a list is a pointer, and the list
is what an append moves.
-/

/--
info: 'ComplexAnalytic.GlueShape.lift_uniq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.GlueShape.lift_uniq

/--
info: 'ComplexAnalytic.GlueShape.hsymm_of_hglue' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.GlueShape.hsymm_of_hglue

/--
info: 'ComplexAnalytic.GlueShape.not_ctHRange' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.GlueShape.not_ctHRange

/--
info: 'ComplexAnalytic.GlueShape.hRange_of_no_three' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.GlueShape.hRange_of_no_three

/--
info: 'ComplexAnalytic.GlueShape.hCocycle_of_no_three' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.GlueShape.hCocycle_of_no_three

/-! ### A standard étale algebra over a presented `ℂ`-algebra is presented

The results `Oka/Analytification/StandardEtale.lean` advertises about the two operations —
adjoin a variable, add a relation — about the forms of the identification with
`StandardEtalePair.Ring` (the one that names the quotient, the one that names `P.Ring`, and the
one that quantifies the polynomial lifts of `f` and `g` away), and about the bridge from
`Polynomial.derivative` to `MvPolynomial.pderiv` that a consumer of `StandardEtalePair.cond` has
to come through. **This heading is not all of what that file advertises**: the rest of its
`## Main results` is guarded under `### `StandardEtalePair.cond` at a point`.

**The clause this replaces was exact when written and was falsified by the next push to the file
it counts.** It read *"The six advertised results of `Oka/Analytification/StandardEtale.lean`"*,
written at `1bb563e`, when that file advertised those and no more; `5ae9ed5` appended
`ComplexAnalytic.exists_mk_pderiv_mul_add_eq_mk_pow` and
`ComplexAnalytic.eval_pderiv_ne_zero` to the same `## Main results`, guarded them under the
heading below, and swept nothing.

**The bridge is one declaration and it needed no helpers**, which is worth recording because the
obvious proof needs two: a crossing lemma for `MvPolynomial.optionEquivLeft` that Mathlib has
only for `MvPolynomial.sumRingEquiv`, and a reindexing lemma for
`ComplexAnalytic.localisationVarEquiv`. Both are avoided by inducting on the polynomial instead
of opening the equivalence up, which also plants no equation lemma; the proof's own docstring
has the measurement.
-/

/--
info: 'ComplexAnalytic.presentedAlgebraSnocEquiv' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.presentedAlgebraSnocEquiv

/--
info: 'ComplexAnalytic.polyPresentedAlgebraEquiv' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.polyPresentedAlgebraEquiv

/--
info: 'ComplexAnalytic.etalePresentedAlgebraEquiv' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.etalePresentedAlgebraEquiv

/--
info: 'ComplexAnalytic.etalePresentedAlgebraEquivRing' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.etalePresentedAlgebraEquivRing

/--
info: 'ComplexAnalytic.exists_presentation_standardEtale' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.exists_presentation_standardEtale

/--
info: 'ComplexAnalytic.polyPresentedAlgebraEquiv_mk_pderiv' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.polyPresentedAlgebraEquiv_mk_pderiv

/-! ### `StandardEtalePair.cond` at a point

The two results of `Oka/Analytification/StandardEtale.lean` that read that field: the equation
moved from `A[X]` down to the polynomial ring the presentation cuts with, and the same equation
evaluated at a point of the hypersurface off the zero locus of `G`. The third of the chain is in
the guard block below, since it is declared one file on.
-/

/--
info: 'ComplexAnalytic.exists_mk_pderiv_mul_add_eq_mk_pow' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.exists_mk_pderiv_mul_add_eq_mk_pow

/--
info: 'ComplexAnalytic.eval_pderiv_ne_zero' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.eval_pderiv_ne_zero

/-! ### The étale presentation analytifies to a distinguished open

The advertised results of `Oka/Analytification/StandardEtaleAnalytification.lean`: the ideal
identity that lets the two presentations be compared at all, the isomorphism read against the open
immersion, the statement that it is an isomorphism **over the base**, and — last, and about the
étale hypothesis rather than about the comparison — `StandardEtalePair.cond` read at a point of
the hypersurface's analytification. The third is the one that makes the first two say something
about the projection of the étale cover rather than about two spaces that happen to be isomorphic.
-/

/--
info: 'ComplexAnalytic.presentationIdeal_etalePresentation_eq_localisation' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.presentationIdeal_etalePresentation_eq_localisation

/--
info: 'ComplexAnalytic.etaleAnalytificationIso_hom_ofRestrict' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.etaleAnalytificationIso_hom_ofRestrict

/--
info: 'ComplexAnalytic.etaleAnalytificationIso_hom_comp' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.etaleAnalytificationIso_hom_comp

/--
info: 'ComplexAnalytic.eval_pderiv_ne_zero_of_mem' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.eval_pderiv_ne_zero_of_mem

/-! ### The image of the analytification in `ℂ^n` -/

/--
info: 'ComplexAnalytic.isClosedEmbedding_base_analytificationIncl' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isClosedEmbedding_base_analytificationIncl

/--
info: 'ComplexAnalytic.range_base_analytificationIncl' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.range_base_analytificationIncl

/-! ### The monic-hypersurface family of a polynomial -/

/--
info: 'ComplexAnalytic.lastVarPolyEquiv' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.lastVarPolyEquiv

/--
info: 'ComplexAnalytic.eval_eq_eval_lastVarPolyEquiv' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.eval_eq_eval_lastVarPolyEquiv

/--
info: 'ComplexAnalytic.polyFamily' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.polyFamily

/--
info: 'ComplexAnalytic.monic_polyFamily' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.monic_polyFamily

/--
info: 'ComplexAnalytic.natDegree_polyFamily' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.natDegree_polyFamily

/--
info: 'ComplexAnalytic.continuous_coeff_polyFamily' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.continuous_coeff_polyFamily

/--
info: 'ComplexAnalytic.lastVarSection' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.lastVarSection

/--
info: 'ComplexAnalytic.evalHom_lastVarSection' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.evalHom_lastVarSection

/--
info: 'ComplexAnalytic.isFinite_comp_proj_of_monic' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isFinite_comp_proj_of_monic

/--
info: 'ComplexAnalytic.isFinite_analytification_comp_proj' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isFinite_analytification_comp_proj

/-! ### Refining one member of a cover by distinguished opens

`Oka/Analytification/CoverRefinement.lean`. The refined members, the polynomials cutting their
overlaps out, the glue isomorphism built from `ComplexAnalytic.localisationPresentationIsoMul`,
the two laws that are algebraic, **the two that are geometric**, and the space the refined datum
glues to with its morphism down to the fixed member. The geometric pair was absent here until
`ComplexAnalytic.localisationOpen_rename` — guarded under
`### The glue data of an affine cover with distinguished overlaps` above — gave them the one
statement they were waiting for.

`ComplexAnalytic.not_isIso_refineToBase` is guarded like the rest and is a **negative**: the
morphism is not an isomorphism, at an empty family. A guard on it says only that its proof uses
no axiom beyond the three, which is worth as much here as anywhere — the theorem is what says
this construction produces a morphism and not an identification.

`ComplexAnalytic.refineObj`, `ComplexAnalytic.refinePoly` and `ComplexAnalytic.refineMul` are
`abbrev`s and carry no guard of their own: an `abbrev` is definitionally its body, so a guard on
one would assert the axioms of `ComplexAnalytic.localisationPresentation`, which is guarded where
it is defined.
-/

/--
info: 'ComplexAnalytic.refineMulIso' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineMulIso

/--
info: 'ComplexAnalytic.refineMul_comm' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineMul_comm

/--
info: 'ComplexAnalytic.refineGlue' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineGlue

/--
info: 'ComplexAnalytic.eqToIso_symm'' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.eqToIso_symm'

/--
info: 'ComplexAnalytic.refineGlue_symm' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineGlue_symm

/--
info: 'ComplexAnalytic.eqToHom_localisationHom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.eqToHom_localisationHom

/--
info: 'ComplexAnalytic.refineGlue_comp' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineGlue_comp

/--
info: 'ComplexAnalytic.refineGlue_analytification_comp' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineGlue_analytification_comp

/--
info: 'ComplexAnalytic.refineTransitionHom_localisationProj' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineTransitionHom_localisationProj

/--
info: 'ComplexAnalytic.refineTripleIncl_localisationProj' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineTripleIncl_localisationProj

/--
info: 'ComplexAnalytic.refineHrange' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineHrange

/--
info: 'ComplexAnalytic.refineTriple_localisationProj' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineTriple_localisationProj

/--
info: 'ComplexAnalytic.refineHcocycle' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineHcocycle

/--
info: 'ComplexAnalytic.refineAnalytification' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineAnalytification

/--
info: 'ComplexAnalytic.refineToBase' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineToBase

/--
info: 'ComplexAnalytic.coverIota_comp_refineToBase' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverIota_comp_refineToBase

/--
info: 'ComplexAnalytic.isEmpty_refineAnalytification' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isEmpty_refineAnalytification

/--
info: 'ComplexAnalytic.not_isIso_refineToBase' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.not_isIso_refineToBase

/-! ### The glue of a refined overlap that meets two different members

`Oka/Analytification/CrossMemberGlue.lean`. The re-association of a double localisation over
either of its two factors, the transport across an isomorphism of the bases with a unit
correcting the cutting polynomial, and the cross-member glue those two compose to, each with its
coherence triangle. `ComplexAnalytic.refineGlue_eq_localisationPresentationIsoOfMulEq` is the
`rfl` saying the same-member glue guarded above is an instance of the first of them.

The two triangles are what carry the content: an isomorphism of the right type between two
descriptions of an overlap says nothing until it is recorded as a morphism over the thing both
descriptions lie over, which here is the original cover's own overlap and not either member.
-/

/--
info: 'ComplexAnalytic.localisationPresentationIsoOfMulEq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.localisationPresentationIsoOfMulEq

/--
info: 'ComplexAnalytic.localisationPresentationIsoOfMulEq_hom_comp' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.localisationPresentationIsoOfMulEq_hom_comp

/--
info: 'ComplexAnalytic.refineGlue_eq_localisationPresentationIsoOfMulEq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineGlue_eq_localisationPresentationIsoOfMulEq

/--
info: 'ComplexAnalytic.localisationPresentationIsoOfAlgEquivUnitMul' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.localisationPresentationIsoOfAlgEquivUnitMul

/--
info: 'ComplexAnalytic.localisationPresentationIsoOfAlgEquivUnitMul_hom_comp' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.localisationPresentationIsoOfAlgEquivUnitMul_hom_comp

/--
info: 'ComplexAnalytic.refineCrossProj' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineCrossProj

/--
info: 'ComplexAnalytic.refineCrossProj_localisationHom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineCrossProj_localisationHom

/--
info: 'ComplexAnalytic.refineCrossGlue' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineCrossGlue

/--
info: 'ComplexAnalytic.refineCrossGlue_hom_comp' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineCrossGlue_hom_comp

/-! ### The `poly` field of a refined cover datum

`Oka/Analytification/CrossMemberDatum.lean`. The refined member for a general `σ`, the datum's
`poly` with its diagonal normalised, the extra factor carrying the transport, and the field the
two multiply to — with the two cases read back off it and the constant-`σ` reductions to
`Oka/Analytification/CoverRefinement.lean`'s member and polynomial.

They are guarded together and after the glue above because the point of the file is which of the
two the case split lands in: `ComplexAnalytic.refineDatumPoly`'s *type* carries neither a `dite`
nor a `▸`, and `ComplexAnalytic.refineDatumFactor`'s carries the `▸` between two values of one
type. The pair `ComplexAnalytic.refineDatumPoly_of_eq` and `ComplexAnalytic.refineDatumPoly_of_ne`
is what makes that a relocation and not a loss.
-/

/--
info: 'ComplexAnalytic.refineDatumObj' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumObj

/--
info: 'ComplexAnalytic.refineDatumObj_const' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumObj_const

/--
info: 'ComplexAnalytic.polyDiagOne' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.polyDiagOne

/--
info: 'ComplexAnalytic.polyDiagOne_of_eq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.polyDiagOne_of_eq

/--
info: 'ComplexAnalytic.polyDiagOne_of_ne' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.polyDiagOne_of_ne

/--
info: 'ComplexAnalytic.refineDatumFactor' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumFactor

/--
info: 'ComplexAnalytic.refineDatumPoly' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumPoly

/--
info: 'ComplexAnalytic.refineDatumPoly_of_eq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumPoly_of_eq

/--
info: 'ComplexAnalytic.refineDatumPoly_of_ne' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumPoly_of_ne

/--
info: 'ComplexAnalytic.refineDatumPoly_const' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumPoly_const

/--
info: 'ComplexAnalytic.coverOverlap_refineDatumPoly_const' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverOverlap_refineDatumPoly_const

/-! ### The `glue` of a cross-member refined datum where the two members are equal

`Oka/Analytification/CrossMemberDatumGlue.lean`. The refined overlap with its cutting polynomial
abstracted, the swap of two refining polynomials over one member, that swap transported across an
equality of members, and the datum's own `glue` on the branch where the two members are equal —
each with its symmetry and its coherence triangle, plus the analytified triangle and the
constant-`σ` reduction.

They are guarded together and after the `poly` field because the point of the file is the
transport: `ComplexAnalytic.refineSwapGlueOfEq` is the one declaration whose two sides sit over
two different objects of `ComplexAnalytic.Presentation`, and every statement above it is over one.
`ComplexAnalytic.refineDatumCrossAlgEquiv` is guarded here and is what the unequal branch, in the
section at the end of this file, feeds to `Oka/Analytification/CrossMemberGlue.lean`'s glue: it is
the original datum's own glue and not a missing construction.
`ComplexAnalytic.refineSwapGlue_eq` and `ComplexAnalytic.refineDatumGlueEq_eq` are guarded beside
the definitions they unfold, which is where a reader looking for a missing guard would expect
them.
-/

/--
info: 'ComplexAnalytic.refineDatumOverlap' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumOverlap

/--
info: 'ComplexAnalytic.coverOverlap_refineDatumObj' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverOverlap_refineDatumObj

/--
info: 'ComplexAnalytic.refineSwapGlue' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineSwapGlue

/--
info: 'ComplexAnalytic.refineSwapMul' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineSwapMul

/--
info: 'ComplexAnalytic.refineSwapGlue_eq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineSwapGlue_eq

/--
info: 'ComplexAnalytic.refineSwapGlue_symm' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineSwapGlue_symm

/--
info: 'ComplexAnalytic.refineSwapGlue_comp' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineSwapGlue_comp

/--
info: 'ComplexAnalytic.refineSwapGlueOfEq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineSwapGlueOfEq

/--
info: 'ComplexAnalytic.refineSwapGlueOfEq_symm' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineSwapGlueOfEq_symm

/--
info: 'ComplexAnalytic.refineSwapGlueOfEq_comp' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineSwapGlueOfEq_comp

/--
info: 'ComplexAnalytic.refineDatumGlueEq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumGlueEq

/--
info: 'ComplexAnalytic.refineDatumGlueEq_eq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumGlueEq_eq

/--
info: 'ComplexAnalytic.refineDatumGlueEq_symm' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumGlueEq_symm

/--
info: 'ComplexAnalytic.refineDatumGlueEq_comp' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumGlueEq_comp

/--
info: 'ComplexAnalytic.refineDatumGlueEq_analytification_comp' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumGlueEq_analytification_comp

/--
info: 'ComplexAnalytic.refineDatumGlueEq_const' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumGlueEq_const

/--
info: 'ComplexAnalytic.refineDatumCrossAlgEquiv' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumCrossAlgEquiv

/-! ### The diagonal of a cover datum is unread

`Oka/Analytification/DiagonalIndependence.lean`. The transports that say each piece of
`Oka/Analytification/AffineCover.lean`'s glue datum reads `poly` only at the pair it is indexed
by, the two geometric hypotheses transporting because they are stated at distinct indices, the
glue datum and the glued analytic space depending on nothing at the diagonal, and the
diagonal-normalised datum of `Oka/Analytification/CrossMemberDatum.lean` as the instance.

They are guarded together and after `ComplexAnalytic.refineDatumPoly` above because the
normalisation is what that declaration uses and this is the statement it left open.
`ComplexAnalytic.glueDiagOne` is the only definition among them; everything else is a transport,
and each is `Classical.choice` only through the `HEq` machinery and the `Classical.dec` inside
`ComplexAnalytic.polyDiagOne`.
-/

/--
info: 'ComplexAnalytic.coverOverlap_congr' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverOverlap_congr

/--
info: 'ComplexAnalytic.coverOverlapSpace_congr' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverOverlapSpace_congr

/--
info: 'ComplexAnalytic.coverOpen_congr' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverOpen_congr

/--
info: 'ComplexAnalytic.coverPart_congr' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverPart_congr

/--
info: 'ComplexAnalytic.coverTriplePart_congr' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverTriplePart_congr

/--
info: 'ComplexAnalytic.heq_coverIncl' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.heq_coverIncl

/--
info: 'ComplexAnalytic.heq_coverOverlapIso' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.heq_coverOverlapIso

/--
info: 'ComplexAnalytic.heq_coverTripleIncl' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.heq_coverTripleIncl

/--
info: 'ComplexAnalytic.heq_coverGlueIso' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.heq_coverGlueIso

/--
info: 'ComplexAnalytic.heq_coverTransition' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.heq_coverTransition

/--
info: 'ComplexAnalytic.heq_coverTransitionHom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.heq_coverTransitionHom

/--
info: 'ComplexAnalytic.heq_coverTriple' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.heq_coverTriple

/--
info: 'ComplexAnalytic.hrange_congr' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.hrange_congr

/--
info: 'ComplexAnalytic.hcocycle_congr' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.hcocycle_congr

/--
info: 'ComplexAnalytic.coverGlueData'_congr' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverGlueData'_congr

/--
info: 'ComplexAnalytic.coverGlueData_congr' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverGlueData_congr

/--
info: 'ComplexAnalytic.coverAnalytification_congr' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverAnalytification_congr

/--
info: 'ComplexAnalytic.glueDiagOne' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.glueDiagOne

/--
info: 'ComplexAnalytic.heq_glueDiagOne' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.heq_glueDiagOne

/--
info: 'ComplexAnalytic.glueDiagOne_of_eq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.glueDiagOne_of_eq

/--
info: 'ComplexAnalytic.hsymm_glueDiagOne' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.hsymm_glueDiagOne

/--
info: 'ComplexAnalytic.coverAnalytification_polyDiagOne' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverAnalytification_polyDiagOne

/-! ### Finiteness over a presented base

`Oka/Analytification/HypersurfaceFinite.lean`. The coordinates of the projection `ℂ^(n+1) ⟶ ℂ^n`,
the factorisation of the analytified structure map `A ⟶ A[X] ⧸ (F)` through the ambient `ℂ^(n+1)`,
and the finiteness that cancelling `A^an ↪ ℂ^n` against it gives. They are guarded here rather
than in `OkaTest/Axioms/Morphisms.lean`, where the projection's own finiteness lives, because the
file that declares them is under `Oka/Analytification/`; the theorem they generalise,
`ComplexAnalytic.isFinite_comp_proj_of_range_subset`, is guarded there beside
`ComplexAnalytic.isFinite_comp_proj_of_range_eq`.
-/

/--
info: 'ComplexAnalytic.AnalyticSpace.coordPullback_proj' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.coordPullback_proj

/--
info: 'ComplexAnalytic.analytificationMap_hypersurfacePresHom_comp' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.analytificationMap_hypersurfacePresHom_comp

/--
info: 'ComplexAnalytic.isFinite_analytificationMap_hypersurfacePresHom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isFinite_analytificationMap_hypersurfacePresHom


/-! ### The unequal branch of that `glue`, and the field the two branches assemble into

`Oka/Analytification/CrossMemberDatumGlue.lean`. The two equations a caller's choice of `r` and
`u` has to satisfy, the cross-member glue conjugated onto the datum's own overlaps, the projection
of a cross-member refined overlap to the original overlap, the coherence triangle over that
projection, and the `glue` field the two branches assemble into with its two readers and its
constant-`σ` reduction.

They are guarded here rather than beside the equal branch above because the file's section split
is the same: everything above is the branch that needs a transport between two members, and
everything here takes the caller's choice as an argument. `ComplexAnalytic.RefineDatumCrossEq` and
`ComplexAnalytic.RefineDatumCrossUnit` are `abbrev`s and so are guarded like the definitions they
are, and `ComplexAnalytic.refineDatumGlueNe_eq` and `ComplexAnalytic.refineDatumCrossProj_eq` sit
beside the definitions they unfold, as their equal-branch counterparts do.
-/

/--
info: 'ComplexAnalytic.RefineDatumCrossEq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.RefineDatumCrossEq

/--
info: 'ComplexAnalytic.RefineDatumCrossUnit' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.RefineDatumCrossUnit

/--
info: 'ComplexAnalytic.refineDatumGlueNe' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumGlueNe

/--
info: 'ComplexAnalytic.refineDatumGlueNe_eq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumGlueNe_eq

/--
info: 'ComplexAnalytic.refineDatumCrossProj' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumCrossProj

/--
info: 'ComplexAnalytic.refineDatumCrossProj_eq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumCrossProj_eq

/--
info: 'ComplexAnalytic.isoOfAlgEquiv_symm_refineDatumCrossAlgEquiv' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isoOfAlgEquiv_symm_refineDatumCrossAlgEquiv

/--
info: 'ComplexAnalytic.refineDatumGlueNe_comp' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumGlueNe_comp

/--
info: 'ComplexAnalytic.refineDatumGlue' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumGlue

/--
info: 'ComplexAnalytic.refineDatumGlue_of_eq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumGlue_of_eq

/--
info: 'ComplexAnalytic.refineDatumGlue_of_ne' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumGlue_of_ne

/--
info: 'ComplexAnalytic.refineDatumGlue_const' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumGlue_const


/-! ### The analytified form of the unequal branch's triangle, and the projection it needs

`Oka/Analytification/CrossMemberDatumGlue.lean`. The `a`-side projection of a cross-member refined
overlap followed down to its member, the same statement under the analytification functor, and the
unequal branch's coherence triangle analytified.

They are guarded in their own section rather than folded into the one above because the section
above enumerates what that branch had when it was written, and the file's `## What is not here`
said at the time that the analytified triangle was absent. They are all theorems, so none of them
is the `abbrev` case that section records.
-/

/--
info: 'ComplexAnalytic.refineDatumCrossProj_localisationHom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumCrossProj_localisationHom

/--
info: 'ComplexAnalytic.refineDatumCrossProj_analytification_localisationProj' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumCrossProj_analytification_localisationProj

/--
info: 'ComplexAnalytic.refineDatumGlueNe_analytification_comp' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumGlueNe_analytification_comp

/-! ### The caller's choice in a cross-member `glue`

`Oka/Analytification/CrossMemberChoice.lean`: the two obligations a cross-member `glue` puts on
the caller collapse to one associate statement, and that statement holds — so the choice the field
takes exists at every ordered pair. -/

/--
info: 'ComplexAnalytic.coverOverlapClass' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverOverlapClass

/--
info: 'ComplexAnalytic.coverOverlapClass_mul' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverOverlapClass_mul

/--
info: 'ComplexAnalytic.refineDatumCrossAlgEquiv_symm' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumCrossAlgEquiv_symm

/--
info: 'ComplexAnalytic.exists_refineDatumCrossEq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.exists_refineDatumCrossEq

/--
info: 'ComplexAnalytic.refineDatumCross_exists_iff' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumCross_exists_iff

/--
info: 'ComplexAnalytic.RefineDatumCrossFactor' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.RefineDatumCrossFactor

/--
info: 'ComplexAnalytic.exists_refineDatumCrossFactor' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.exists_refineDatumCrossFactor

/--
info: 'ComplexAnalytic.exists_refineDatumCrossUnit_of_factor' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.exists_refineDatumCrossUnit_of_factor

/--
info: 'ComplexAnalytic.exists_refineDatumCross' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.exists_refineDatumCross

/-! ### Two adjoined roots, and the composition law for a renaming that it needs

`Oka/Analytification/ChangeOfVariables.lean` and `Oka/Analytification/HypersurfaceFinite.lean`.
The general composition law for `ComplexAnalytic.PresHom.ofRename` with the ideal statement under
it, and the two-step hypersurface extension it makes expressible as one map of presentations,
with its finiteness.

Appended as their own section rather than folded into the two above because those sections
enumerate what their files had when they were written, and because every branch on this board adds
a section at the end of this file — a section moved is a conflict for somebody else.

**And then six more were appended into this one, so the enumeration above is four of what it now
guards and not all of them.** The other six are
`Oka/Analytification/HypersurfaceFinite.lean`'s tower block:
`ComplexAnalytic.towerPresentation` and `ComplexAnalytic.towerPresHom`, the `m`-step
generalisation of the two-step extension named above, with
`ComplexAnalytic.isFinite_analytificationMap_towerPresHom` and the three `rfl` identifications
`ComplexAnalytic.towerPresentation_one` and `ComplexAnalytic.towerPresHom_one`, the tower at one
step, and `ComplexAnalytic.towerPresHom_two`, the tower at two — which is the evidence that
`ComplexAnalytic.isFinite_analytificationMap_hypersurfacePresHom_comp_hypersurfacePresHom` is
subsumed rather than sitting beside it, and not a base case: the recursion's is `m = 0`. **That
name is spelled out because two of the four are two-step theorems and only this one is
subsumed**: the other, `ComplexAnalytic.hypersurfacePresHom_comp_hypersurfacePresHom`, is an
equation of presentation morphisms, and nothing states `ComplexAnalytic.towerPresHom` as a
`ComplexAnalytic.PresHom.ofRename`, so on the tower line there is nothing for it to be subsumed
by. **The `def`s here are `towerPresentation` and `towerPresHom`**, and the rest are theorems;
this clause read *"All four are theorems"*, which was true of the four and said nothing about the
six.

**Widened rather than split**, and the alternative was real: this file's rule is that a guard goes
in the section of the push that added it, so a tower section of its own at the end would have been
consistent with it. Against that, the tower is the `m`-step form of the very extension this
section's headline is about, so a split separates a statement from its generalisation;
`Oka/Analytification/HypersurfaceFinite.lean`'s guards are already spread over three sections and
`Oka/Analytification/ChangeOfVariables.lean`'s over two, so the boundary would buy no property the
file has elsewhere; and moving six guard blocks is the one operation here that can drop a guard
without any check noticing. **The members are named rather than counted**, which is the repair
`Oka/Analytification/RefineDatumUnitFamily.lean`'s section below now uses for the same defect: a
list a reader can check beats a number they have to recount.
-/

/--
info: 'ComplexAnalytic.rename_mem_presentationIdeal' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.rename_mem_presentationIdeal

/--
info: 'ComplexAnalytic.PresHom.ofRename_comp' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.PresHom.ofRename_comp

/--
info: 'ComplexAnalytic.hypersurfacePresHom_comp_hypersurfacePresHom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.hypersurfacePresHom_comp_hypersurfacePresHom

/--
info: 'ComplexAnalytic.isFinite_analytificationMap_hypersurfacePresHom_comp_hypersurfacePresHom'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  ComplexAnalytic.isFinite_analytificationMap_hypersurfacePresHom_comp_hypersurfacePresHom

/--
info: 'ComplexAnalytic.towerPresentation' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.towerPresentation

/--
info: 'ComplexAnalytic.towerPresHom' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.towerPresHom

/--
info: 'ComplexAnalytic.isFinite_analytificationMap_towerPresHom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isFinite_analytificationMap_towerPresHom

/--
info: 'ComplexAnalytic.towerPresentation_one' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.towerPresentation_one

/--
info: 'ComplexAnalytic.towerPresHom_one' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.towerPresHom_one

/--
info: 'ComplexAnalytic.towerPresHom_two' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.towerPresHom_two

/-! ### The hypersurface over an open subset of the base

`Oka/Analytification/OpenBaseFiniteness.lean`, **the whole of it**, in the order they are guarded:
the image in `ℂ^n` of the points of a hypersurface at which a second polynomial vanishes, its
closedness, the vacuity of that vanishing above the complement, the finiteness of the hypersurface
over the cylinder, the two witnesses bounding the complement at `ℂ^n` and at `∅`, the monicity of
`X² - C a`, and the **three** declarations of the witness between them — the bad set of the
parabola with its last coordinate inverted, and that it is neither empty nor everything, which
together are the only case the theorems downstream are interesting in.

**This paragraph is an exact enumeration and it has now gone false twice, in two different ways.**
It said *"the two witnesses"* and a third arrived — a **stale** count, the kind that moves when
somebody adds a declaration and that a writer thinks to re-check. A first draft of this very push
then corrected that and left *"and one at which it is proper and nonempty"* describing **three**
declarations, and omitted the monicity entirely — a count that was **never right**, which no later
change could have made wrong and which only a reading of the paragraph against the file catches.
**The two look identical here and are found by opposite habits.** Nothing mechanical sees either:
a sweep scoped to `Oka/` does not reach a guard file, and `scripts/check_docstring_names.py`
resolves every name in such a sentence. That is what lana-agents/oka#349 was rejected for, one
section over.

The first is a `def` and is guarded for that reason: the convention here is every declaration and
not every theorem, and `scripts/guard_coverage.py` cannot report a missing guard on a name
advertised under `## Main definitions`, which it does not read. **It is that file's only `def`.**
-/

/--
info: 'ComplexAnalytic.hypersurfaceCommonZeroImage' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.hypersurfaceCommonZeroImage

/--
info: 'ComplexAnalytic.isClosed_hypersurfaceCommonZeroImage' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isClosed_hypersurfaceCommonZeroImage

/--
info: 'ComplexAnalytic.eval_ne_zero_of_notMem_hypersurfaceCommonZeroImage' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.eval_ne_zero_of_notMem_hypersurfaceCommonZeroImage

/--
info: 'ComplexAnalytic.isFinite_analytification_comp_projRestrict' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isFinite_analytification_comp_projRestrict

/--
info: 'ComplexAnalytic.hypersurfaceCommonZeroImage_one' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.hypersurfaceCommonZeroImage_one

/--
info: 'ComplexAnalytic.hypersurfaceCommonZeroImage_X' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.hypersurfaceCommonZeroImage_X

/--
info: 'ComplexAnalytic.monic_X_sq_sub_C' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.monic_X_sq_sub_C

/--
info: 'ComplexAnalytic.hypersurfaceCommonZeroImage_parabola' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.hypersurfaceCommonZeroImage_parabola

/--
info: 'ComplexAnalytic.hypersurfaceCommonZeroImage_parabola_nonempty' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.hypersurfaceCommonZeroImage_parabola_nonempty

/--
info: 'ComplexAnalytic.hypersurfaceCommonZeroImage_parabola_ne_univ' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.hypersurfaceCommonZeroImage_parabola_ne_univ

/-! ### The refined datum's symmetry law, and the monomorphism under it

`Oka/Analytification/RefineDatumSymm.lean`. The universal property of a localisation at a
distinguished open, the monomorphism it makes of the structure map, the two monomorphisms of the
cross-member projection that follow, and what they buy for the refined cover datum's `glue`:
`ComplexAnalytic.refineDatumGlueNe_unique`, that the coherence triangle determines the
cross-member branch; `ComplexAnalytic.refineDatumGlueNe_congr`, that that branch does not depend
on the caller's choice; `ComplexAnalytic.refineDatumGlueNe_symm`, that it is symmetric; and
`ComplexAnalytic.refineDatumGlue_symm`, the symmetry law of the refined cover datum itself, at
every ordered pair.

**That clause read *the three consequences for the refined cover datum's `glue`*, and it was short
of its own section on the day it was written.** `ComplexAnalytic.refineDatumGlue_symm` was guarded
by `46525e6`, the commit that wrote the clause, and no clause of it described that declaration;
each subject the clause did list was exact, which is why re-reading the numeral against them never
caught it. That is an enumeration stopping early rather than a count rotting, so
`OkaTest/Axioms.lean`'s *falsified by the next append to either* does not reach it — and it is why
the subjects are named here instead: a name a reader can look up is checkable against the section
in a way that a numeral agreeing with a list is not.

The `instance`s here are guarded for the same reason the rest are: the convention here is every
declaration and not every theorem, and `scripts/guard_coverage.py` reports nothing about a name
it does not find under `## Main results`.
-/

/--
info: 'ComplexAnalytic.ringHom_ext_localisationRingHom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.ringHom_ext_localisationRingHom

/--
info: 'ComplexAnalytic.mono_localisationHom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.mono_localisationHom

/--
info: 'ComplexAnalytic.mono_refineCrossProj' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.mono_refineCrossProj

/--
info: 'ComplexAnalytic.mono_refineDatumCrossProj' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.mono_refineDatumCrossProj

/--
info: 'ComplexAnalytic.refineDatumGlueNe_unique' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumGlueNe_unique

/--
info: 'ComplexAnalytic.refineDatumGlueNe_congr' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumGlueNe_congr

/--
info: 'ComplexAnalytic.refineDatumGlueNe_symm' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumGlueNe_symm

/--
info: 'ComplexAnalytic.refineDatumGlue_symm' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumGlue_symm

/-! ### The cross-member refined transition, over the original cover's transition

`Oka/Analytification/RefineDatumTransition.lean`. The comparison of a cross-member refined overlap
with the original overlap it lies over, on a double overlap and on a triple one, the square saying
that the refined transition lies over the original datum's own transition, and what that makes of
`hrange`: the half the original law supplies, and the equivalence saying it is the only half.

The `def`s here are guarded for the same reason the rest are: the convention here is every
declaration and not every theorem.
-/

/--
info: 'ComplexAnalytic.refineDatumCrossProjSpace' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumCrossProjSpace

/--
info: 'ComplexAnalytic.refineDatumCrossProjSpace_localisationProj' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumCrossProjSpace_localisationProj

/--
info: 'ComplexAnalytic.refineDatumCrossPart' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumCrossPart

/--
info: 'ComplexAnalytic.refineDatumCrossPart_eq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumCrossPart_eq

/--
info: 'ComplexAnalytic.refineDatumCrossPart_coverIncl' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumCrossPart_coverIncl

/--
info: 'ComplexAnalytic.refineDatumGlueNe_analytification_localisationProj' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumGlueNe_analytification_localisationProj

/--
info: 'ComplexAnalytic.refineDatumTransitionHom_localisationProj_of_ne' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumTransitionHom_localisationProj_of_ne

/--
info: 'ComplexAnalytic.coverOpen_refineDatumPoly_of_ne' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverOpen_refineDatumPoly_of_ne

/--
info: 'ComplexAnalytic.range_refineDatumCrossTriple_subset' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.range_refineDatumCrossTriple_subset

/--
info: 'ComplexAnalytic.refineDatumCrossTriple' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumCrossTriple

/--
info: 'ComplexAnalytic.refineDatumCrossTriple_eq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumCrossTriple_eq

/--
info: 'ComplexAnalytic.refineDatumCrossTriple_coverTripleIncl' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumCrossTriple_coverTripleIncl

/--
info: 'ComplexAnalytic.range_refineDatumTransitionHom_localisationProj_subset' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.range_refineDatumTransitionHom_localisationProj_subset

/--
info: 'ComplexAnalytic.range_refineDatumTransitionHom_subset_iff' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.range_refineDatumTransitionHom_subset_iff

/-! ### The side condition of the two-root renaming

`ComplexAnalytic.rename_mem_presentationIdeal`'s first consumer, and the composite law of
`Oka/Analytification/HypersurfaceFinite.lean` with its hypothesis discharged at it. Both are
theorems.

Appended as its own section for the reason the section above gives: a section moved is a conflict
for somebody else.
-/

/--
info: 'ComplexAnalytic.rename_localisationIncl_comp_mem' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.rename_localisationIncl_comp_mem

/--
info: 'ComplexAnalytic.hypersurfacePresHom_comp_hypersurfacePresHom'' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.hypersurfacePresHom_comp_hypersurfacePresHom'

/-! ### The cut-out datum of an analytification, and the standard étale local isomorphism

`ComplexAnalytic.isCutOutBy_analytificationInclHom` is the datum every consumer of
`ComplexAnalytic.IsCutOutBy` on the projection line asks for, and the guards below it are
`Oka/Analytification/StandardEtaleLocalIso.lean` in order. Every one of them is a theorem.

Appended as its own section for the reason the sections above give: a section moved is a conflict
for somebody else.
-/

/--
info: 'ComplexAnalytic.isCutOutBy_analytificationInclHom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isCutOutBy_analytificationInclHom

/--
info: 'ComplexAnalytic.section_hypersurfacePresentation_empty' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.section_hypersurfacePresentation_empty

/--
info: 'ComplexAnalytic.isCutOutBy_analytificationInclHom_hypersurface' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isCutOutBy_analytificationInclHom_hypersurface

/--
info: 'ComplexAnalytic.isLocalIso_hypersurface_ofRestrict_comp_proj' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isLocalIso_hypersurface_ofRestrict_comp_proj

/--
info: 'ComplexAnalytic.isLocalIso_hypersurface_of_standardEtale' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isLocalIso_hypersurface_of_standardEtale

/--
info: 'ComplexAnalytic.isLocalIso_analytificationMap_etalePresHom_comp' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isLocalIso_analytificationMap_etalePresHom_comp

/-! ### The refined `hrange` at the triples whose three members are not all different

`Oka/Analytification/RefineDatumRange.lean`. The identification of two members the index map sends
two indices to and the two transport lemmas that cross it, the refined overlap of two members
lying over one, the equal branch's transition over its member on a double overlap and on a triple
one, `hrange` at an all-equal triple, the free half at the two mixed triples that have one, and
what is left at each of the three shapes with a residue.

`ComplexAnalytic.coverSpaceHomOfEq` is a `def` and is guarded for the same reason the rest are:
the convention here is every declaration and not every theorem.

Appended as its own section for the reason the two sections above give: a section moved is a
conflict for somebody else.
-/

/--
info: 'ComplexAnalytic.coverSpaceHomOfEq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverSpaceHomOfEq

/--
info: 'ComplexAnalytic.coverSpaceHomOfEq_refl' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverSpaceHomOfEq_refl

/--
info: 'ComplexAnalytic.mem_localisationOpen_coverSpaceHomOfEq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.mem_localisationOpen_coverSpaceHomOfEq

/--
info: 'ComplexAnalytic.mem_coverOpen_coverSpaceHomOfEq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.mem_coverOpen_coverSpaceHomOfEq

/--
info: 'ComplexAnalytic.coverOpen_refineDatumPoly_of_eq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverOpen_refineDatumPoly_of_eq

/--
info: 'ComplexAnalytic.refineDatumTransitionHom_localisationProj_of_eq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumTransitionHom_localisationProj_of_eq

/--
info: 'ComplexAnalytic.refineDatumTripleIncl_localisationProj_of_eq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumTripleIncl_localisationProj_of_eq

/--
info: 'ComplexAnalytic.refineDatumTripleIncl_localisationProj_apply_of_eq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumTripleIncl_localisationProj_apply_of_eq

/--
info: 'ComplexAnalytic.range_refineDatumTransitionHom_subset_of_eq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.range_refineDatumTransitionHom_subset_of_eq

/--
info: 'ComplexAnalytic.range_refineDatumTransitionHom_localisationProj_subset_of_eq_ac' depends on
  axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.range_refineDatumTransitionHom_localisationProj_subset_of_eq_ac

/--
info: 'ComplexAnalytic.range_refineDatumTransitionHom_localisationProj_subset_of_eq_ab' depends on
  axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.range_refineDatumTransitionHom_localisationProj_subset_of_eq_ab

/--
info: 'ComplexAnalytic.range_refineDatumTransitionHom_subset_iff_of_ne_bc' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.range_refineDatumTransitionHom_subset_iff_of_ne_bc

/--
info: 'ComplexAnalytic.range_refineDatumTransitionHom_subset_iff_of_eq_ac' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.range_refineDatumTransitionHom_subset_iff_of_eq_ac

/--
info: 'ComplexAnalytic.range_refineDatumTransitionHom_subset_iff_of_eq_ab' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.range_refineDatumTransitionHom_subset_iff_of_eq_ab

/--
info: 'ComplexAnalytic.range_refineDatumTransitionHom_subset_iff_of_eq_bc' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.range_refineDatumTransitionHom_subset_iff_of_eq_bc

/-! ### A surjection of presented algebras analytifies to a finite morphism

`Oka/Analytification/SurjectionFinite.lean`. The surjectivity of a rename at the identity, the
triangle over `ℂ^n` it induces, the closed embedding that follows and the finiteness that follows
from that.

Appended as its own section for the reason the sections above give: a section moved is a conflict
for somebody else.
-/

/--
info: 'ComplexAnalytic.PresHom.ofRename_id_toRingHom_surjective' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.PresHom.ofRename_id_toRingHom_surjective

/--
info: 'ComplexAnalytic.analytificationMap_ofRename_id_comp' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.analytificationMap_ofRename_id_comp

/--
info: 'ComplexAnalytic.isClosedEmbedding_base_analytificationMap_ofRename_id' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isClosedEmbedding_base_analytificationMap_ofRename_id

/--
info: 'ComplexAnalytic.isFinite_analytificationMap_ofRename_id' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isFinite_analytificationMap_ofRename_id

/-! ### The refined cover datum's glue data, and the cocycle law named

`Oka/Analytification/RefineDatumGlueData.lean`. The two conditions the range law of a
cross-member refined cover datum reduces to, that law itself with the five shapes joined, the
equivalence saying the two conditions are exactly what it asks, the cocycle law — statable only
once the range law is a single proof — and the glue data and analytic space that take it as their
one hypothesis.

The `def`s and `abbrev`s here are guarded for the reason the
`Oka/Analytification/RefineDatumRange.lean` section above gives: the convention here is every
declaration and not every theorem.

Appended as its own section for the reason the sections above give: a section moved is a conflict
for somebody else.
-/

/--
info: 'ComplexAnalytic.RefineDatumRangeCross' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.RefineDatumRangeCross

/--
info: 'ComplexAnalytic.RefineDatumRangeEq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.RefineDatumRangeEq

/--
info: 'ComplexAnalytic.refineDatumHrange' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumHrange

/--
info: 'ComplexAnalytic.refineDatumHrange_iff' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumHrange_iff

/--
info: 'ComplexAnalytic.RefineDatumCocycle' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.RefineDatumCocycle

/--
info: 'ComplexAnalytic.refineDatumGlueData' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumGlueData

/--
info: 'ComplexAnalytic.refineDatumAnalytification' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumAnalytification

/--
info: 'ComplexAnalytic.refineDatumAnalytification_toLocallyRingedSpace' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumAnalytification_toLocallyRingedSpace


/-! ### A module-finite map of presented algebras analytifies to a finite morphism

`Oka/Analytification/ModuleFiniteAnalytification.lean`, together with
`ComplexAnalytic.lastVarPolyEquiv_rename_localisationIncl`,
`ComplexAnalytic.lastVarPolyEquiv_symm_C` and `ComplexAnalytic.lastVarPolyEquiv_symm_X`, which it
needs and which live in `Oka/Analytification/MonicHypersurface.lean`. That file declares further
`ComplexAnalytic.lastVarPolyEquiv` lemmas this one does not read, so the naming above selects
rather than totals, and it is what makes *which* of them are here checkable at all. The values of
the tower's variables and the evaluation at them, the compatibility of that evaluation with each
inclusion of variables the tower uses and with the one-variable reading of the last one, the
tower's relations dying, the tower's structure map as one renaming, every ideal of the polynomial
ring being a presentation ideal, an isomorphism of presentations being finite, the join of the
surjection with the tower, and the general theorem.

**The `ComplexAnalytic.lastVarPolyEquiv` lemmas named above are guarded here and not in
`### The monic-hypersurface family of a polynomial` above**, where their file's other guards are,
for the reason the sections above give: a section moved is a conflict for somebody else, and so
is one grown in the middle.

**`ComplexAnalytic.hypersurfacePresentation` is guarded here and it is not new.** It is
`Oka/Analytification/StandardEtaleAnalytification.lean`'s and it was unguarded; this push cites it
in a `## Main results` block, which is what makes `scripts/guard_coverage.py` count it as
*advertised*, and an advertised declaration with no guard is the gap that script measures. Guarding
it is a line, and the alternative — not naming it — would have been hiding the gap rather than
closing it.

`ComplexAnalytic.towerVal`, `ComplexAnalytic.towerVar` and `ComplexAnalytic.towerVal_self` depend
on **no** axioms, and `ComplexAnalytic.towerIncl`, `ComplexAnalytic.towerVal_localisationVar` and
`ComplexAnalytic.towerVal_towerVar` on `propext` and `Quot.sound` only — the last two because
`omega` discharges their bound, and `ComplexAnalytic.towerIncl` for the same reason. **No
`Classical.choice` in any of the six**, which is what a proof that is a `change` to the `dite` and
one `dif_pos` or `dif_neg` costs. Those six lines are what they are and not the usual triple.
-/

/--
info: 'ComplexAnalytic.lastVarPolyEquiv_rename_localisationIncl' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.lastVarPolyEquiv_rename_localisationIncl

/--
info: 'ComplexAnalytic.lastVarPolyEquiv_symm_C' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.lastVarPolyEquiv_symm_C

/--
info: 'ComplexAnalytic.lastVarPolyEquiv_symm_X' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.lastVarPolyEquiv_symm_X

/--
info: 'ComplexAnalytic.towerVal' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.towerVal

/--
info: 'ComplexAnalytic.towerAeval' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.towerAeval

/--
info: 'ComplexAnalytic.towerVal_localisationVar' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.towerVal_localisationVar

/--
info: 'ComplexAnalytic.towerVal_self' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.towerVal_self

/--
info: 'ComplexAnalytic.towerAeval_rename_localisationIncl' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.towerAeval_rename_localisationIncl

/--
info: 'ComplexAnalytic.towerAeval_lastVarPolyEquiv_symm' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.towerAeval_lastVarPolyEquiv_symm

/--
info: 'ComplexAnalytic.presentationIdeal_towerPresentation_le_ker' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.presentationIdeal_towerPresentation_le_ker

/--
info: 'ComplexAnalytic.towerIncl' depends on axioms:
  [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.towerIncl

/--
info: 'ComplexAnalytic.towerVar' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.towerVar

/--
info: 'ComplexAnalytic.towerVal_towerVar' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.towerVal_towerVar

/--
info: 'ComplexAnalytic.towerAeval_rename_towerIncl' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.towerAeval_rename_towerIncl

/--
info: 'ComplexAnalytic.towerPresHom_toRingHom_mk' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.towerPresHom_toRingHom_mk

/--
info: 'ComplexAnalytic.exists_presentationIdeal_eq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.exists_presentationIdeal_eq

/--
info: 'ComplexAnalytic.isFinite_analytificationMap_of_inv' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isFinite_analytificationMap_of_inv

/--
info: 'ComplexAnalytic.isFinite_analytificationMap_ofRename_id_comp_towerPresHom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isFinite_analytificationMap_ofRename_id_comp_towerPresHom

/--
info: 'ComplexAnalytic.isFinite_analytificationMap_of_finite' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isFinite_analytificationMap_of_finite

/--
info: 'ComplexAnalytic.hypersurfacePresentation' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.hypersurfacePresentation

/-! ### The cocycle law of a cross-member refinement, and the space it leaves unconditional

`Oka/Analytification/RefineDatumCocycle.lean`, one declaration of
`Oka/Analytification/AffineCover.lean` and three of
`Oka/Analytification/RefineDatumRange.lean` that this line added: the pair cancellation the three
mixed shapes run on, the descent of a refined triple overlap, the two edge statements that replace
`ComplexAnalytic.refineTriple_localisationProj`, the five shapes, the law itself, and the glue data
and analytic space that no longer ask for it.

`ComplexAnalytic.coverTransition_hom_comp` is guarded here rather than in the
`Oka/Analytification/AffineCover.lean` section above, and
`ComplexAnalytic.coverSpaceHomOfEq_trans`, `ComplexAnalytic.coverSpaceHomOfEq_self` and
`ComplexAnalytic.coverSpaceHomOfEq_comp_symm` here rather than in the
`Oka/Analytification/RefineDatumRange.lean` section above, for the reason every section here
gives: a section moved is a conflict for somebody else, and so is a guard inserted into one. The
three were declared in `Oka/Analytification/RefineDatumCocycle.lean` when this section was
written and were moved to the file that owns `ComplexAnalytic.coverSpaceHomOfEq` afterwards; the
guards stayed.

**The `def`s here are `ComplexAnalytic.refineDatumTripleProj`,
`ComplexAnalytic.refineDatumTripleCross`, `ComplexAnalytic.refineDatumGlueDataOfLaws` and
`ComplexAnalytic.refineDatumAnalytificationOfLaws`**, and are guarded for the reason the
`Oka/Analytification/RefineDatumRange.lean` section gives: the convention here is every
declaration and not every theorem. **This clause read *six*, and it read six at the commit that
wrote it**, where the section already had twenty-seven guards and the four `def`s named above. The
section below on a refined cover datum at a family that is not `1` says why a count of this kind
is the one nothing catches.

Appended as its own section for the reason the sections above give: a section moved is a conflict
for somebody else.
-/


/--
info: 'ComplexAnalytic.coverTransition_hom_comp' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverTransition_hom_comp

/--
info: 'ComplexAnalytic.coverTransitionHom_of_fac' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverTransitionHom_of_fac

/--
info: 'ComplexAnalytic.coverSpaceHomOfEq_trans' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverSpaceHomOfEq_trans

/--
info: 'ComplexAnalytic.coverSpaceHomOfEq_self' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverSpaceHomOfEq_self

/--
info: 'ComplexAnalytic.coverSpaceHomOfEq_comp_symm' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverSpaceHomOfEq_comp_symm

/--
info: 'ComplexAnalytic.coverTransitionHom_of_fac_eq_ab' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverTransitionHom_of_fac_eq_ab

/--
info: 'ComplexAnalytic.coverTransitionHom_of_fac_eq_bc' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverTransitionHom_of_fac_eq_bc

/--
info: 'ComplexAnalytic.coverTransitionHom_of_fac_eq_ac' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverTransitionHom_of_fac_eq_ac

/--
info: 'ComplexAnalytic.refineDatumTripleProj' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumTripleProj

/--
info: 'ComplexAnalytic.refineDatumTripleProj_eq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumTripleProj_eq

/--
info: 'ComplexAnalytic.refineDatumTripleCross' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumTripleCross

/--
info: 'ComplexAnalytic.refineDatumTripleCross_eq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumTripleCross_eq

/--
info: 'ComplexAnalytic.refineDatumTripleCross_coverIncl' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumTripleCross_coverIncl

/--
info: 'ComplexAnalytic.refineDatumTriple_localisationProj_of_ne' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumTriple_localisationProj_of_ne

/--
info: 'ComplexAnalytic.refineDatumTriple_localisationProj_of_eq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumTriple_localisationProj_of_eq

/--
info: 'ComplexAnalytic.refineDatumCocycle_of_localisationProj' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumCocycle_of_localisationProj

/--
info: 'ComplexAnalytic.refineDatumTripleProj_cocycle_of_eq_eq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumTripleProj_cocycle_of_eq_eq

/--
info: 'ComplexAnalytic.refineDatumCrossTriple_ofRestrict' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumCrossTriple_ofRestrict

/--
info: 'ComplexAnalytic.refineDatumCrossTriple_coverTriple' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumCrossTriple_coverTriple

/--
info: 'ComplexAnalytic.refineDatumTripleProj_cocycle_of_ne_ne' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumTripleProj_cocycle_of_ne_ne

/--
info: 'ComplexAnalytic.refineDatumTripleProj_cocycle_of_eq_ab' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumTripleProj_cocycle_of_eq_ab

/--
info: 'ComplexAnalytic.refineDatumTripleProj_cocycle_of_eq_bc' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumTripleProj_cocycle_of_eq_bc

/--
info: 'ComplexAnalytic.refineDatumTripleProj_cocycle_of_eq_ac' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumTripleProj_cocycle_of_eq_ac

/--
info: 'ComplexAnalytic.refineDatumHcocycle' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumHcocycle

/--
info: 'ComplexAnalytic.refineDatumGlueDataOfLaws' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumGlueDataOfLaws

/--
info: 'ComplexAnalytic.refineDatumAnalytificationOfLaws' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumAnalytificationOfLaws

/--
info: 'ComplexAnalytic.refineDatumAnalytificationOfLaws_toLocallyRingedSpace' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumAnalytificationOfLaws_toLocallyRingedSpace

/-! ### A refined cover datum at a non-constant `σ`, and the two conditions met

`Oka/Analytification/RefineDatumWitness.lean`, one declaration of
`Oka/Analytification/DistinguishedOpen.lean` and one of
`Oka/Analytification/CrossMemberDatumGlue.lean` that this line added: `D(1)` is the whole space in
both the plain and the transported form, both equations have a solution wherever the four
polynomials are units, the caller's `r` and `u` at a trivial refining family, the two laws they
satisfy, the two adopted conditions discharged, the glue data and the analytic space, and the
sentence that makes the index map non-constant.

`ComplexAnalytic.localisationOpen_one` and
`ComplexAnalytic.exists_refineDatumCross_of_isUnit` are guarded here rather than in the
`Oka/Analytification/DistinguishedOpen.lean` and
`Oka/Analytification/CrossMemberDatumGlue.lean` sections above, for the reason every section here
gives: a section moved is a conflict for somebody else, and so is a guard inserted into one.

The `def`s here are guarded for the reason the `Oka/Analytification/RefineDatumRange.lean`
section gives: the convention here is every declaration and not every theorem.

**`ComplexAnalytic.not_isConstant_id` is the one guard in this section with an empty axiom list**,
and it is worth one line of explanation rather than being read as an anomaly: it is a statement
about a `Nontrivial` type and the identity, with no analytic geometry in it at all, and every
other declaration on this line reaches `Classical.choice` through the analytification functor.

Appended as its own section for the reason the sections above give: a section moved is a conflict
for somebody else.
-/

/--
info: 'ComplexAnalytic.localisationOpen_one' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.localisationOpen_one

/--
info: 'ComplexAnalytic.exists_refineDatumCross_of_isUnit' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.exists_refineDatumCross_of_isUnit

/--
info: 'ComplexAnalytic.mem_localisationOpen_transport_one' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.mem_localisationOpen_transport_one

/--
info: 'ComplexAnalytic.exists_refineDatumCross_one' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.exists_refineDatumCross_one

/--
info: 'ComplexAnalytic.refineDatumOneR' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumOneR

/--
info: 'ComplexAnalytic.refineDatumOneU' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumOneU

/--
info: 'ComplexAnalytic.refineDatumOneCrossEq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumOneCrossEq

/--
info: 'ComplexAnalytic.refineDatumOneCrossUnit' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumOneCrossUnit

/--
info: 'ComplexAnalytic.refineDatumOneRangeEq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumOneRangeEq

/--
info: 'ComplexAnalytic.refineDatumOneRangeCross' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumOneRangeCross

/--
info: 'ComplexAnalytic.refineDatumOneGlueData' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumOneGlueData

/--
info: 'ComplexAnalytic.refineDatumOneAnalytification' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumOneAnalytification

/--
info: 'ComplexAnalytic.not_isConstant_id' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.not_isConstant_id

/-! ### The standard étale analytification is finite over an open subset of the base

`Oka/Analytification/StandardEtaleFiniteness.lean`, together with
`ComplexAnalytic.hypersurfacePresentation_empty` from
`Oka/Analytification/StandardEtaleAnalytification.lean`, which is the spelling bridge between the
presentation the comparison is stated for and the one-element family every statement about a
hypersurface of `ℂ^(n+1)` is written in.

This is taxis #1112's §1 at `k = 0`: the hypersurface over `V` in the presentation spelling, the
containment of that part in `D(G)` above a `V` avoiding the bad set — which is the geometry and is
the only place `G` does anything — and the finiteness of the standard étale analytification over
`V`, where `ComplexAnalytic.etaleAnalytificationIso` is spent. The last of those four is the same
statement at the largest such `V`, the complement of
`ComplexAnalytic.hypersurfaceCommonZeroImage`.

**A fifth was appended after that sentence was written and it named nothing**:
`ComplexAnalytic.isFinite_restrictHom_analytificationMap_etalePresHom_comp_parabola`, the instance
at the parabola with its last coordinate inverted — the first pair on this line for which that
open subset of the base is both proper and non-empty. So this section guards the spelling bridge
named above **and every declaration of** `Oka/Analytification/StandardEtaleFiniteness.lean`, which
is one more than that file has. *"The last of the four"* was true of the four listed and false of
the section, and which of the two a numeral in a header means is settled here by enumerating the
section.

**No `ComplexAnalytic.AnalyticSpace.IsFiniteEtale` is guarded *in this section*, and two of the
three clauses that used to follow are no longer true.** The sentence read *"none is stated, … and
the restricted one waits on a transport of `ComplexAnalytic.AnalyticSpace.IsLocalIso` along a
restriction that the repository does not have"*. The transport is
`ComplexAnalytic.AnalyticSpace.isLocalIso_restrictHom` (`Oka/AnalyticSpace/OpenSubspace.lean`,
guarded in `OkaTest/Axioms/Morphisms.lean`), and the restricted `IsFiniteEtale` is both stated and
guarded — **in this file**, in the *Finite étale over an open subset of the base* section below.
**`here` is read as this section and not as this file**, which is the only reading that survives,
and it is spelled out because it did not survive being left implicit. What stays true and is the
reason the section is worth this paragraph: **the unrestricted `IsFiniteEtale` is false**, and
`Oka/Analytification/MonicHypersurface.lean` carries the witness.

Appended as its own section for the reason the sections above give: a section moved is a conflict
for somebody else.
-/

/--
info: 'ComplexAnalytic.hypersurfacePresentation_empty' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.hypersurfacePresentation_empty

/--
info: 'ComplexAnalytic.isFinite_restrictHom_hypersurface_comp_proj' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isFinite_restrictHom_hypersurface_comp_proj

/--
info: 'ComplexAnalytic.map_le_localisationOpen_of_subset_compl' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.map_le_localisationOpen_of_subset_compl

/--
info: 'ComplexAnalytic.isFinite_restrictHom_analytificationMap_etalePresHom_comp' depends on
  axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isFinite_restrictHom_analytificationMap_etalePresHom_comp

/--
info: 'ComplexAnalytic.isFinite_restrictHom_analytificationMap_etalePresHom_comp_compl' depends on
  axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isFinite_restrictHom_analytificationMap_etalePresHom_comp_compl

/--
info: 'ComplexAnalytic.isFinite_restrictHom_analytificationMap_etalePresHom_comp_parabola'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isFinite_restrictHom_analytificationMap_etalePresHom_comp_parabola

/-! ### A refined cover datum at a family that is not `1`, and the two conditions again

`Oka/Analytification/RefineDatumUnitFamily.lean`, all of it but
`ComplexAnalytic.refineDatumUnitFamAnalytification_toLocallyRingedSpace`: the second adopted
condition at an injective index map, the first at the original datum's own cutting polynomial and
at *every* refining family, the choice at a family that is a unit on each overlap, the caller's
`r` and `u` and the two laws they satisfy, and the glue data and the analytic space they assemble
to.

**This header read "all nine of it", and it went false when
`ComplexAnalytic.refineDatumUnitFamAnalytification_toLocallyRingedSpace` was added to that file.**
That guard is in a **section of its own at the end of this file** rather than appended here, on
this file's standing convention that a section moved is a conflict for somebody else — and the
header now names the one declaration it leaves out rather than counting the rest, because a
section header that counts what is under it goes false silently.

**The `def`s here are the caller's `ComplexAnalytic.refineDatumUnitFamR` and
`ComplexAnalytic.refineDatumUnitFamU`, and the `ComplexAnalytic.refineDatumUnitFamGlueData` and
`ComplexAnalytic.refineDatumUnitFamAnalytification` they assemble to**, and are guarded for the
reason the `Oka/Analytification/RefineDatumRange.lean` section gives: the convention here is every
declaration and not every theorem.

**This clause read *three*, and it read three on the day it was written.** That is the *other* way
a count in a section header goes false, and the `### The hypersurface over an open subset of the
base` section above states the distinction: the *nine* corrected in the paragraph above moved when
a declaration was added, so a writer thinks to re-check it, while the *three* could not have been
made wrong by any later change and only a reading of the sentence against
`Oka/Analytification/RefineDatumUnitFamily.lean` catches it. **The two look identical in the file
and are found by opposite habits**, and it is why the four are now named rather than counted: a
name a reader can check beats a number they have to recount.
`ComplexAnalytic.refineDatumUnitFamAnalytification_toLocallyRingedSpace` is a `theorem`, so those
are the file's `def`s as well and the correction above does not move them.

**Every guard below has the same three axioms, including the two that discharge a condition.**
`ComplexAnalytic.refineDatumRangeEq_of_injective` is a one-line term and carries `Classical.choice`
only through `ComplexAnalytic.RefineDatumRangeEq`'s own statement, which mentions
`ComplexAnalytic.refineDatumGlue`; that is worth saying because the section above it records the
opposite case, a guard with an *empty* list, for the same kind of reason — what an axiom list
reports here is the statement's ancestry and not the proof's difficulty.

`OkaTest/RefineDatumUnitFamily.lean`'s instance of all this is in the test library and carries no
guard, as `ComplexAnalytic.nodeCoverObj` and `ComplexAnalytic.lineCoverObj` carry none.
-/

/--
info: 'ComplexAnalytic.refineDatumRangeEq_of_injective' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumRangeEq_of_injective

/--
info: 'ComplexAnalytic.refineDatumRangeCross_poly' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumRangeCross_poly

/--
info: 'ComplexAnalytic.exists_refineDatumCross_unitFam' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.exists_refineDatumCross_unitFam

/--
info: 'ComplexAnalytic.refineDatumUnitFamR' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumUnitFamR

/--
info: 'ComplexAnalytic.refineDatumUnitFamU' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumUnitFamU

/--
info: 'ComplexAnalytic.refineDatumUnitFamCrossEq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumUnitFamCrossEq

/--
info: 'ComplexAnalytic.refineDatumUnitFamCrossUnit' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumUnitFamCrossUnit

/--
info: 'ComplexAnalytic.refineDatumUnitFamGlueData' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumUnitFamGlueData

/--
info: 'ComplexAnalytic.refineDatumUnitFamAnalytification' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumUnitFamAnalytification

/-! ### A cover glued along the whole of each member

`Oka/Analytification/CoverGlueTop.lean`, the whole of it: the general form of the member inclusion
off the diagonal, its surjectivity when the overlap is `⊤`, the surjectivity of the member's
inclusion into the gluing, the isomorphism that follows, and the `eqToHom` helper the first of
them produces.

**One of them is a `def`**, `ComplexAnalytic.isoCoverGlued`, and it is guarded for the reason
the `Oka/Analytification/RefineDatumRange.lean` section gives: the convention here is every
declaration and not every theorem. **This clause read *two*, and it read two at the commit that
wrote it**, where `Oka/Analytification/CoverGlueTop.lean` already held the theorems and the `def`
it holds now.

**The instance that consumes them is `ComplexAnalytic.isoNodeRefineGlued` in
`OkaTest/RefineDatumUnitFamilyNode.lean`, which carries no guard**, as no declaration of the test
library does.
-/

/--
info: 'ComplexAnalytic.surjective_base_eqToHom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.surjective_base_eqToHom

/--
info: 'ComplexAnalytic.f_coverGlueData_of_ne' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.f_coverGlueData_of_ne

/--
info: 'ComplexAnalytic.surjective_f_coverGlueData' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.surjective_f_coverGlueData

/--
info: 'ComplexAnalytic.surjective_ι_coverGlueData' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.surjective_ι_coverGlueData

/--
info: 'ComplexAnalytic.isoCoverGlued' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isoCoverGlued

/-! ### The gap that file opened and closed in the same push

`ComplexAnalytic.coverIncl` is an `abbrev` of `Oka/Analytification/AffineCover.lean` and carried no
guard, because until `ComplexAnalytic.f_coverGlueData_of_ne` named it in a `## Main results` bullet
it was advertised nowhere. **Citing an older declaration in such a block makes it a newly
*unguarded advertised* result**, and the identity `Δguards = Δ(in both) + Δ(nowhere)` that
`scripts/guard_coverage.py` is checked by still closes when that happens — so the row that moves
is `unguarded`, and nothing else says why.
The gap is closed here rather than reported.
-/

/--
info: 'ComplexAnalytic.coverIncl' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverIncl

/-! ### Finite étale over an open subset of the base, which is both halves at once

`Oka/Analytification/StandardEtaleFiniteEtale.lean`.
`ComplexAnalytic.isFiniteEtale_restrictHom_analytificationMap_etalePresHom_comp` and its `_compl`
companion are the guards below, and neither adds an axiom to the two halves it conjoins. The
finiteness half is `ComplexAnalytic.isFinite_restrictHom_analytificationMap_etalePresHom_comp`, the
local-isomorphism half is
`ComplexAnalytic.isLocalIso_analytificationMap_etalePresHom_comp`, both guarded above, and the
transport that joins them is `ComplexAnalytic.AnalyticSpace.isLocalIso_restrictHom`, guarded in
`OkaTest/Axioms/Morphisms.lean` beside the `IsFinite` statement it is the analogue of. All four
carry the same three axioms.
-/

/--
info: 'ComplexAnalytic.isFiniteEtale_restrictHom_analytificationMap_etalePresHom_comp' depends on
  axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isFiniteEtale_restrictHom_analytificationMap_etalePresHom_comp

/--
info: 'ComplexAnalytic.isFiniteEtale_restrictHom_analytificationMap_etalePresHom_comp_compl'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isFiniteEtale_restrictHom_analytificationMap_etalePresHom_comp_compl

/-! ### The refinement's space is its glue data's gluing

`Oka/Analytification/RefineDatumUnitFamily.lean`'s tenth declaration, and the section above says
why it is here rather than there.
`ComplexAnalytic.refineDatumUnitFamAnalytification_toLocallyRingedSpace` relates the two
definitions guarded at the end of that section, which is what makes every statement about the
gluing a statement about the space. Same three axioms as all nine of them —
`ComplexAnalytic.refineDatumAnalytificationOfLaws_toLocallyRingedSpace` at the same arguments and
nothing else.

The two instances that spend it, `ComplexAnalytic.nodeRefinement_toLocallyRingedSpace` and
`ComplexAnalytic.lineRefinement_toLocallyRingedSpace`, are in
`OkaTest/RefineDatumUnitFamilyNode.lean` and carry no guard: this file imports `Oka` and not
`OkaTest`, so no declaration of a test file is in its environment.

Appended as its own section for the reason the sections above give: a section moved is a conflict
for somebody else.
-/

/--
info: 'ComplexAnalytic.refineDatumUnitFamAnalytification_toLocallyRingedSpace' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumUnitFamAnalytification_toLocallyRingedSpace

/-! ### The local isomorphism over a presented base

`Oka/Analytification/StandardEtaleLocalIsoBase.lean`, the whole of it, in the order they are
declared. **Two are a `def`** — `ComplexAnalytic.hypersurfaceOnly` and
`ComplexAnalytic.hypersurfaceCompare`, both `abbrev` — and the rest are theorems.

The statement the section exists for is the last:
`ComplexAnalytic.isLocalIso_analytificationMap_etalePresHom`, the analytification of a standard
étale morphism over a **presented** base as a local isomorphism onto that base, at every `k`. It
is the first thing on this line stated at a base other than `ℂ^n`, and its target is `X^an`
rather than `ℂ^n` — the composite with `ComplexAnalytic.analytificationInclHom` is a different
statement and is false at `k ≥ 1`, which
`Oka/Analytification/StandardEtaleLocalIso.lean` records and this file's earlier section guards
the `k = 0` half of.

Appended as its own section rather than folded into a section above, for the reason those
sections give: a section moved is a conflict for somebody else. Nothing here is
`ComplexAnalytic.AnalyticSpace.IsFiniteEtale`; the finiteness field at `k ≥ 1` is untouched by
that file and by this section.
-/

/--
info: 'ComplexAnalytic.hypersurfaceOnly' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.hypersurfaceOnly

/--
info: 'ComplexAnalytic.presentationIdeal_hypersurfaceOnly_le' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.presentationIdeal_hypersurfaceOnly_le

/--
info: 'ComplexAnalytic.hypersurfaceCompare' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.hypersurfaceCompare

/--
info: 'ComplexAnalytic.hypersurfaceCompare_comp' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.hypersurfaceCompare_comp

/--
info: 'ComplexAnalytic.range_section_hypersurfacePresentation' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.range_section_hypersurfacePresentation

/--
info: 'ComplexAnalytic.isCutOutBy_hypersurfaceCompare' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isCutOutBy_hypersurfaceCompare

/--
info: 'ComplexAnalytic.pullbackΓ_proj_ofMvPolynomial' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.pullbackΓ_proj_ofMvPolynomial

/--
info: 'ComplexAnalytic.isLocalIso_hypersurfaceOnly_ofRestrict_comp_proj' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isLocalIso_hypersurfaceOnly_ofRestrict_comp_proj

/--
info: 'ComplexAnalytic.localisationOpen_mul_pderiv' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.localisationOpen_mul_pderiv

/--
info: 'ComplexAnalytic.restrictSections_hypersurfaceCompare' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.restrictSections_hypersurfaceCompare

/--
info: 'ComplexAnalytic.ofRestrict_comp_analytificationMap_comp_analytificationInclHom'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.ofRestrict_comp_analytificationMap_comp_analytificationInclHom

/--
info: 'ComplexAnalytic.isLocalIso_ofRestrict_comp_analytificationMap' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isLocalIso_ofRestrict_comp_analytificationMap

/--
info: 'ComplexAnalytic.comap_localisationOpen_hypersurfaceCompare' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.comap_localisationOpen_hypersurfaceCompare

/--
info: 'ComplexAnalytic.isLocalIso_analytificationMap_etalePresHom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isLocalIso_analytificationMap_etalePresHom

/-! ### The glued `Spec`s, as a scheme

`Oka/Analytification/SpecScheme.lean`, the whole of it, in the order they are declared. **Two are
a `def`** — `ComplexAnalytic.specScheme` and `ComplexAnalytic.specSchemeIota` — one is an
`instance`, and the rest are theorems.

The section exists because the `Spec`-side section above guards a gluing of locally ringed spaces
and says nothing about a scheme: `ComplexAnalytic.specGlued` is guarded there, and that its
promotion `ComplexAnalytic.specScheme` is a scheme is a different statement in a different module.
It is the **first** `AlgebraicGeometry.Scheme` guarded in this file.

The last one is the reason the module exists rather than a corollary of it:
`ComplexAnalytic.exists_basicOpen_specSchemeIota_inter` is the local form of the condition
`Oka/Analytification/CoverIndependence.lean` names as what a common refinement of two cover data
has to reproduce. It is about two members of **one** datum and is not a common refinement; that
module's docstring says what a refinement needs beyond it.

Appended as its own section rather than folded into the `Spec`-side section above, for the reason
those sections give: a section moved is a conflict for somebody else.
-/

/--
info: 'ComplexAnalytic.specScheme' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.specScheme

/--
info: 'ComplexAnalytic.specScheme_toLocallyRingedSpace' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.specScheme_toLocallyRingedSpace

/--
info: 'ComplexAnalytic.specSchemeIota' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.specSchemeIota

/--
info: 'ComplexAnalytic.isOpenImmersion_specSchemeIota' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isOpenImmersion_specSchemeIota

/--
info: 'ComplexAnalytic.isAffineOpen_specSchemeIota' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isAffineOpen_specSchemeIota

/--
info: 'ComplexAnalytic.exists_basicOpen_specSchemeIota_inter' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.exists_basicOpen_specSchemeIota_inter

/-! ### The base map of the standard étale projection, on points

`Oka/Analytification/StandardEtaleAnalytification.lean`, appended as its own section so that no
section above moves.

`ComplexAnalytic.base_analytificationMap_etalePresHom_comp_apply` is the only description of that
morphism on points in the repository, and it is what a statement about its *image* has to be fed;
`ComplexAnalytic.base_condEtaleProj_ne_zero` (`OkaTest/StandardEtaleNotFinite.lean`) is the first
consumer and is a test declaration, so it is not guarded here. -/

/--
info: 'ComplexAnalytic.base_analytificationMap_etalePresHom_comp_apply' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.base_analytificationMap_etalePresHom_comp_apply

/-! ### The projection to `ℂ^n` at a presented base, refuted

`Oka/Analytification/StandardEtaleNotLocalIso.lean`, appended as its own section for the reason
the sections above give: a section moved is a conflict for somebody else.

**The negative counterpart of `ComplexAnalytic.isLocalIso_analytificationMap_etalePresHom_comp`
and `ComplexAnalytic.isLocalIso_analytificationMap_etalePresHom`, both guarded above.** The three
are stated at two different morphisms and that is the content: the structure map to the base's own
analytification is a local isomorphism at every `k`, and the same map followed by the base's
inclusion into `ℂ^n` is one at `k = 0` and is not one as soon as a relation of the base is a
non-zero polynomial and the source is not empty. The hypotheses of the last are unsatisfiable at
`k = 0`, so the three do not overlap.

Its only new ingredient is `MvPolynomial.eq_zero_of_eval_eq_zero_of_isOpen`, a mirror-tree lemma
guarded in `OkaTest/Axioms/RingTheory.lean`.
`ComplexAnalytic.not_isLocalIso_analytificationMap_etalePresHom_comp_node`
(`OkaTest/StandardEtaleNotLocalIso.lean`) meets both hypotheses at the node and is a test
declaration, so it is not guarded here. -/

/--
info: 'ComplexAnalytic.not_isLocalIso_analytificationMap_etalePresHom_comp' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.not_isLocalIso_analytificationMap_etalePresHom_comp

/-! ### The morphism from a cross-member refinement down to the cover it refines

`Oka/Analytification/RefineDatumToBase.lean` and one lemma of
`Oka/Analytification/RefineDatumRange.lean`, appended as their own section for the reason the
sections above give: a section moved is a conflict for somebody else.

**`ComplexAnalytic.coverMap` is guarded above and this is its first instance outside
`Oka/Analytification/CoverFunctoriality.lean` whose compatibility hypothesis is discharged rather
than taken from a caller** — the guard on `ComplexAnalytic.comm_refineDatumMapPart` is the one
that says so, and it is the only declaration here that would notice if either of the two squares
it runs on started resting on a fourth axiom. Inside that file the two functor laws discharge the
hypothesis already, `ComplexAnalytic.comm_coverMapPart_id` at the identity data and
`ComplexAnalytic.comm_coverMapPart_comp` at a composite; the qualifier is there because a draft of
this paragraph did without it and was false.
`ComplexAnalytic.refineDatumPresHom` is an `abbrev` with no content and is guarded because it is
advertised under `## Main definitions`; `ComplexAnalytic.coverSpaceHomOfEq_comp_coverIota` is
guarded here rather than in that file's own section for the same reason the section exists.

`ComplexAnalytic.coverIota_comp_refineDatumToBase_assoc` is the `@[reassoc]` companion and is not
guarded: it is generated from the lemma above it, which is. -/

/--
info: 'ComplexAnalytic.coverSpaceHomOfEq_comp_coverIota' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverSpaceHomOfEq_comp_coverIota

/--
info: 'ComplexAnalytic.refineDatumPresHom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumPresHom

/--
info: 'ComplexAnalytic.comm_refineDatumMapPart' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.comm_refineDatumMapPart

/--
info: 'ComplexAnalytic.refineDatumToBase' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumToBase

/--
info: 'ComplexAnalytic.coverIota_comp_refineDatumToBase' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverIota_comp_refineDatumToBase

/--
info: 'ComplexAnalytic.refineDatumToBase_unique' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumToBase_unique

/-! ### Two cover data over one scheme

`Oka/Analytification/SpecTwoData.lean`, the whole of it, in the order they are declared. **One is
a `def`** — `ComplexAnalytic.specSchemeIotaMap` — one is an `instance`, and the rest are
theorems.

The section exists because the scheme section above guards statements about **one** cover datum
and every declaration here is about two: a member of a second datum carried into the first datum's
scheme, that it is an affine open there, and the doubly-distinguished open across the two.

**These are not the first guarded statements in this file about a pair of data**, and an earlier
version of this paragraph said they were. The section above for
`Oka/Analytification/SpecFunctoriality.lean` guards that file's declarations, and from its
`### The morphism` heading on they are about two cover data on the `Spec` side;
`ComplexAnalytic.coverMap` further up is a morphism out of two data as well. The second datum is
opened by a `variable` line in each case, which is why a sweep of the prose for the phrase returned
neither.

**What is new is the way the two data are related.** There the caller hands in an index map `σ`
and morphisms `ψ i : obj i ⟶ obj' (σ i)`, matching the members up before anything is proved. Here
nothing matches them up: the only relation is a single morphism between what the two data glue,
every pair of members is admissible, and the last theorem produces its two indices rather than
taking them.

`ComplexAnalytic.mem_opensRange_specSchemeIotaMap` and
`ComplexAnalytic.exists_index_basicOpen_specSchemeIotaMap` are the ones that ask for
`CategoryTheory.IsIso` on the morphism between the two gluings; the rest hold at an open
immersion. **None of them is a common refinement**, and
`Oka/Analytification/SpecTwoData.lean`'s own `## What is not here` says which piece of one is
still missing and what the two steps after it were measured to cost.

Appended as its own section rather than folded into the section above, for the reason those
sections give: a section moved is a conflict for somebody else.
-/

/--
info: 'ComplexAnalytic.specSchemeIotaMap' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.specSchemeIotaMap

/--
info: 'ComplexAnalytic.isOpenImmersion_specSchemeIotaMap' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isOpenImmersion_specSchemeIotaMap

/--
info: 'ComplexAnalytic.isAffineOpen_specSchemeIotaMap' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isAffineOpen_specSchemeIotaMap

/--
info: 'ComplexAnalytic.exists_basicOpen_specSchemeIotaMap_inter' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.exists_basicOpen_specSchemeIotaMap_inter

/--
info: 'ComplexAnalytic.mem_opensRange_specSchemeIotaMap' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.mem_opensRange_specSchemeIotaMap

/--
info: 'ComplexAnalytic.exists_index_basicOpen_specSchemeIotaMap' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.exists_index_basicOpen_specSchemeIotaMap

/-! ### The projection of `D(1)`, and the isomorphism the `V = ⊤` bridge makes available

`Oka/Analytification/DistinguishedOpen.lean`'s one declaration on this line: at `f = 1` the
projection of a distinguished open is not merely an open immersion but an isomorphism.

Guarded here rather than in the `Oka/Analytification/DistinguishedOpen.lean` sections above, and
appended as its own section, for the reason every section here gives: a section moved is a conflict
for somebody else, and so is a guard inserted into one.

**The axiom list is the same three as its ingredients'** —
`ComplexAnalytic.localisationIso_hom_ofRestrict` and `ComplexAnalytic.localisationOpen_one` are
guarded above and `ComplexAnalytic.AnalyticSpace.isIso_ofRestrict_of_eq_univ` in
`OkaTest/Axioms/AnalyticSpace.lean`, so this guard records that composing the three adds nothing,
which is the whole claim the theorem makes.
-/

/--
info: 'ComplexAnalytic.isIso_localisationProj_one' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isIso_localisationProj_one

/-! ### A section over a member of the glued `Spec`, in polynomials

`Oka/Analytification/SpecMemberSections.lean`, appended as its own section for the reason the
sections above give: a section moved is a conflict for somebody else.

**The continuation of `ComplexAnalytic.exists_basicOpen_specSchemeIota_inter` and
`ComplexAnalytic.exists_index_basicOpen_specSchemeIotaMap`, both guarded above, into the vocabulary
a cover datum is written in.** Those theorems produce *sections*; the guards at the foot of this
section are the same statements with *polynomials* in the members' own variables, and the ones
before them are what carries one to the other — every section over the range of an open immersion
out of a presented algebra's spectrum is such a polynomial, and the open it cuts out in the glued
scheme is the image of `D(p)` under that immersion.

**`ComplexAnalytic.presentationSection`, `ComplexAnalytic.surjective_presentationSection` and
`ComplexAnalytic.basicOpen_presentationSection` are stated at an arbitrary open immersion, and
`ComplexAnalytic.specSchemeIotaSection`, `ComplexAnalytic.surjective_specSchemeIotaSection` and
`ComplexAnalytic.basicOpen_specSchemeIotaSection` are them at
`ComplexAnalytic.specSchemeIota`.** The generality is what the cross-datum guards need: a carried
member is `ComplexAnalytic.specSchemeIotaMap` and is not `ComplexAnalytic.specSchemeIota` of
anything in the first datum, so the second side of those statements has no one-datum spelling.

Its only new ingredient is `AlgebraicGeometry.IsOpenImmersion.specΓIsoTop`, a mirror-tree
isomorphism guarded in `OkaTest/Axioms/Sheaves.lean`. -/

/--
info: 'ComplexAnalytic.presentationSection' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.presentationSection

/--
info: 'ComplexAnalytic.surjective_presentationSection' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.surjective_presentationSection

/--
info: 'ComplexAnalytic.basicOpen_presentationSection' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.basicOpen_presentationSection

/--
info: 'ComplexAnalytic.specSchemeIotaSection' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.specSchemeIotaSection

/--
info: 'ComplexAnalytic.surjective_specSchemeIotaSection' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.surjective_specSchemeIotaSection

/--
info: 'ComplexAnalytic.basicOpen_specSchemeIotaSection' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.basicOpen_specSchemeIotaSection

/--
info: 'ComplexAnalytic.exists_mvPolynomial_basicOpen_specSchemeIota_inter' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.exists_mvPolynomial_basicOpen_specSchemeIota_inter

/--
info: 'ComplexAnalytic.exists_mvPolynomial_basicOpen_specSchemeIotaMap_inter' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.exists_mvPolynomial_basicOpen_specSchemeIotaMap_inter

/--
info: 'ComplexAnalytic.exists_index_mvPolynomial_basicOpen_specSchemeIotaMap' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.exists_index_mvPolynomial_basicOpen_specSchemeIotaMap

/-! ### The pointwise existential, chosen into a family

`Oka/Analytification/SpecMemberChoice.lean`, appended as its own section for the reason the
sections above give: a section moved is a conflict for somebody else.

**The axiom list below is the content, and that is what the guard is a check of.** The theorem is
`ComplexAnalytic.exists_index_mvPolynomial_basicOpen_specSchemeIotaMap` — guarded elsewhere in
this file — with `choose` applied to it, so `Classical.choice` is what the step *is* rather than
something the proof happens to use. The two lists are identical, which is the honest reading here:
this repository's guards do not distinguish a proof that uses choice incidentally from one whose
whole content is choice, and this pair is the clearest example of that limit in the tree. -/

/--
info: 'ComplexAnalytic.exists_family_mvPolynomial_basicOpen_specSchemeIotaMap' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.exists_family_mvPolynomial_basicOpen_specSchemeIotaMap

/-! ### Localising at `1`

`Oka/Analytification/LocalisationIndependence.lean`, appended as its own section for the reason
the sections above give: a section moved is a conflict for somebody else.

**The presentation-level sibling of `ComplexAnalytic.isIso_localisationProj_one`**, which is
guarded above in this file and is the *analytic* statement at the same polynomial. Neither is
derived from the other: no statement in this repository says
`ComplexAnalytic.analytificationFunctor` is full, faithful or reflects isomorphisms, so the two
are guarded separately because they are proved separately — this one out of
`IsLocalization.atUnits` and
`ComplexAnalytic.localisationPresentedAlgebraEquiv_localisationRingHom`, that one out of
`ComplexAnalytic.localisationIso` and `ComplexAnalytic.localisationOpen_one`.

**Both `def`s are guarded and not only the three propositions.**
`ComplexAnalytic.presentedAlgebraEquivLocalisationOne` and
`ComplexAnalytic.localisationIsoOne` are data, so nothing else would notice if either started
resting on a fourth axiom, and `ComplexAnalytic.isIso_localisationHom_one` is the consumer that
carries them both. -/

/--
info: 'ComplexAnalytic.bijective_localisationRingHom_one' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.bijective_localisationRingHom_one

/--
info: 'ComplexAnalytic.presentedAlgebraEquivLocalisationOne' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.presentedAlgebraEquivLocalisationOne

/--
info: 'ComplexAnalytic.localisationIsoOne' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.localisationIsoOne

/--
info: 'ComplexAnalytic.localisationIsoOne_hom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.localisationIsoOne_hom

/--
info: 'ComplexAnalytic.isIso_localisationHom_one' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isIso_localisationHom_one

/-! ### A distinguished open of a member, as an affine open of the glued scheme

The **member-level** half of `Oka/Analytification/SpecRefinedMember.lean`, plus the one declaration
`Oka/Analytification/SpecDistinguishedOpen.lean` gained for it. Appended as its own section for
the reason the sections above give: a section moved is a conflict for somebody else.

**This sentence named that whole file until its general level landed**, and it is narrowed rather
than deleted: the five declarations stated at an arbitrary open immersion are guarded under the
heading that names the general level, and the five here are those five at
`ComplexAnalytic.specSchemeIota`.

**Every declaration here is guarded, including the two that are data.**
`ComplexAnalytic.refinedPres` and `ComplexAnalytic.refinedIota` are a presentation and a morphism
of schemes, so nothing else would notice if either started resting on a fourth axiom, and the
three statements below them are exactly the statements *about* them.

**`ComplexAnalytic.opensRange_Spec_map_localisationRingHom` is guarded here rather than beside
`ComplexAnalytic.isOpenImmersion_Spec_map_localisationRingHom` above** for the same
section-is-a-conflict reason, and because the two are one branch's worth of work: it exists
because the composite whose range `ComplexAnalytic.opensRange_refinedIota` describes has to be
taken apart, and its axiom list is the interesting one of the pair, since Mathlib's
`AlgebraicGeometry.Scheme.Hom.opensRange_localizationAway` is what it is proved out of.
-/

/--
info: 'ComplexAnalytic.opensRange_Spec_map_localisationRingHom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.opensRange_Spec_map_localisationRingHom

/--
info: 'ComplexAnalytic.refinedPres' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refinedPres

/--
info: 'ComplexAnalytic.refinedIota' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refinedIota

/--
info: 'ComplexAnalytic.isOpenImmersion_refinedIota' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isOpenImmersion_refinedIota

/--
info: 'ComplexAnalytic.isAffineOpen_refinedIota' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isAffineOpen_refinedIota

/--
info: 'ComplexAnalytic.opensRange_refinedIota' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.opensRange_refinedIota

/-! ### The refined member's range, in the section vocabulary

`Oka/Analytification/SpecRefinedMemberSection.lean`, appended as its own section for the reason
the sections above give: a section moved is a conflict for somebody else.

**This section said *"One declaration, and it is the whole file"*, and that stopped being true
when the general form landed**: `Oka/Analytification/SpecRefinedMemberSection.lean` now declares
`ComplexAnalytic.opensRange_presentationRefinedIota_eq_basicOpen` as well, guarded under the
heading that names the general level. **The sentence is corrected here rather than deleted**,
because what it was recording — that this section guards the whole of what that file asserts — is
what stopped being true and is worth saying once.

**Its second claim needed the same correction.** This section said
`ComplexAnalytic.opensRange_refinedIota_eq_basicOpen` *"is
`ComplexAnalytic.opensRange_refinedIota` composed with
`ComplexAnalytic.basicOpen_specSchemeIotaSection`"*, which was its proof and is no longer: it is
now the general theorem at `ComplexAnalytic.specSchemeIota`, and the composition happens there.
The guard is unchanged and is still a check that nothing was introduced, since the two proofs
have the same axiom list and this guard is what says so.

**Named and not located**: a section appended at the end of this file cannot say which section is
above it and stay true, since the next branch appends between them. That is a weaker claim than a
locating one, and it is the honest reason this section carries one `#print axioms` rather than a
reason to leave it out: the declaration is advertised under a `## Main results`, and the rule this
directory enforces is about placement rather than about how much a guard can surprise. **That
clause read *a weaker claim than most guards here make* until 2026-09-13**, which is
`OkaTest/Axioms.lean`'s proportion class: it selects a share of this file's guards without naming
one of them or giving a total, and the comparison it is making is between kinds of claim and not
between this section and a population. -/

/--
info: 'ComplexAnalytic.opensRange_refinedIota_eq_basicOpen' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.opensRange_refinedIota_eq_basicOpen

/-! ### The refined member, at an arbitrary open immersion

The general level of `Oka/Analytification/SpecRefinedMember.lean` and
`Oka/Analytification/SpecRefinedMemberSection.lean`: a polynomial in the variables of a
presentation, refining the open a presented affine open immersion into `X` names, rather than the
open a member of a cover datum names. Appended as its own section for the reason the sections
above give: a section moved is a conflict for somebody else.

**One section for six declarations across two files, rather than two insertions under the two
headings that name those files.** The subject the placement rule in `OkaTest/Axioms.lean` asks for
is the general level, and it is one subject; splitting it would put half of it under a heading
whose own text is about a member of a cover datum.

**Every member-level guard this file carried when this section was written is now a guard on an
application of one of these**, and the scoping is not decoration: another section in this file
guards `ComplexAnalytic.opensRange_refinedIota_le`, which is a member-level guard on an
application of `ComplexAnalytic.opensRange_presentationRefinedIota_le` and so of neither of the
six.
`ComplexAnalytic.refinedPres`, `ComplexAnalytic.refinedIota`,
`ComplexAnalytic.isOpenImmersion_refinedIota`, `ComplexAnalytic.isAffineOpen_refinedIota`,
`ComplexAnalytic.opensRange_refinedIota` and
`ComplexAnalytic.opensRange_refinedIota_eq_basicOpen` are the six below at
`ComplexAnalytic.specSchemeIota`, so **the two sets of guards are not independent and this file
does not pretend they are**: what the member-level six now check is that specialising introduced
nothing, and what the six below check is the mathematics. Both are worth keeping — a change to
`ComplexAnalytic.specSchemeIota` itself would move the first six and not the second.

**Named and not located.** No sentence here says which section is above or below it; the next
branch appends between them.
-/

/--
info: 'ComplexAnalytic.presentationRefinedPres' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.presentationRefinedPres

/--
info: 'ComplexAnalytic.presentationRefinedIota' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.presentationRefinedIota

/--
info: 'ComplexAnalytic.isOpenImmersion_presentationRefinedIota' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isOpenImmersion_presentationRefinedIota

/--
info: 'ComplexAnalytic.isAffineOpen_presentationRefinedIota' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isAffineOpen_presentationRefinedIota

/--
info: 'ComplexAnalytic.opensRange_presentationRefinedIota' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.opensRange_presentationRefinedIota

/--
info: 'ComplexAnalytic.opensRange_presentationRefinedIota_eq_basicOpen' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.opensRange_presentationRefinedIota_eq_basicOpen

/-! ### The two-datum choice, read through the refined member

`Oka/Analytification/SpecRefinedChoice.lean`, which is the whole file. Appended as its own section
for the reason the sections above give: a section moved is a conflict for somebody else.

**What the guard below is a check of is the composition of two lists this file already
records.** The theorem is
`ComplexAnalytic.exists_family_mvPolynomial_basicOpen_specSchemeIotaMap` — guarded here — rewritten
three times at `ComplexAnalytic.opensRange_presentationRefinedIota_eq_basicOpen`, also guarded
here, plus `eq_top_iff` and `TopologicalSpace.Opens.mem_iSup` from Mathlib. So the guard says that
composing them, and the covering statement the composition makes, introduced nothing.

**`Classical.choice` is in the list and is not a surprise**: the theorem this is proved from is
itself a `choose` over the points of a scheme, and its own guard in this file records the same
three axioms.

**Named and not located.** No sentence here says which section is above or below it; the next
branch appends between them.
-/

/--
info: 'ComplexAnalytic.exists_family_opensRange_presentationRefinedIota_eq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.exists_family_opensRange_presentationRefinedIota_eq

/-! ### The analytification is Hausdorff, and the standard étale cover is a covering map

`Oka/Analytification/Hausdorff.lean`, the whole of it, appended as its own section for the reason
the sections above give: a section moved is a conflict for somebody else.

**The instance is one `inferInstanceAs` and the two theorems are one `haveI` each**, so every one
of those axiom lists is a union of lists this file and `OkaTest/Axioms/AnalyticSpace.lean` already
record — `ComplexAnalytic.t2Space_zeroLocus` for `ComplexAnalytic.t2Space_analytification`, and
`ComplexAnalytic.isFiniteEtale_restrictHom_analytificationMap_etalePresHom_comp` together with
`ComplexAnalytic.AnalyticSpace.isCoveringMap_base_of_isFiniteEtale` for
`ComplexAnalytic.isCoveringMap_base_restrictHom_analytificationMap_etalePresHom_comp` and its
`_compl` companion. The guards are a check that the third rung introduced nothing, which is what a
corollary of a theorem in another file most plausibly could. **Named and not located**: a section
appended at the end of this file cannot say which section is above it and stay true, since the next
branch appends between
them. Said in full rather than by pointing at a neighbouring section that says it — that citation
was itself the species it names, and it survived this branch's rebase only because the section that
landed in between happens to carry the same sentence. -/

/--
info: 'ComplexAnalytic.t2Space_analytification' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.t2Space_analytification

/--
info: 'ComplexAnalytic.isCoveringMap_base_restrictHom_analytificationMap_etalePresHom_comp'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isCoveringMap_base_restrictHom_analytificationMap_etalePresHom_comp

/--
info: 'ComplexAnalytic.isCoveringMap_base_restrictHom_analytificationMap_etalePresHom_comp_compl'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  ComplexAnalytic.isCoveringMap_base_restrictHom_analytificationMap_etalePresHom_comp_compl

/-! ### The refined member sits inside the member it refines

The containment half of `Oka/Analytification/SpecRefinedMember.lean`, at both of that file's two
levels. Appended as its own section for the reason the sections above give: a section moved is a
conflict for somebody else.

**What the guards below are a check of is one Mathlib name reaching this shape.** Each is the
corresponding `opensRange` equation in that file followed by
`AlgebraicGeometry.Scheme.Hom.image_le_opensRange`, and the member-level one is the general one
applied — so what they record together is that the containment costs no axiom the equations did
not already cost, and those are guarded here too.

**The guards below are the reason a count elsewhere in this file is written the way it is.**
`ComplexAnalytic.opensRange_refinedIota_le` is a member-level guard on an application of
`ComplexAnalytic.opensRange_presentationRefinedIota_le`, and neither is among the declarations
the section named *The refined member, at an arbitrary open immersion* enumerates; that section's
sentence about the member-level guards is scoped to the guards it was written against and says so.

**Named and not located.** No sentence here says which section is above or below it; the next
branch appends between them.
-/

/--
info: 'ComplexAnalytic.opensRange_presentationRefinedIota_le' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.opensRange_presentationRefinedIota_le

/--
info: 'ComplexAnalytic.opensRange_refinedIota_le' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.opensRange_refinedIota_le

/-! ### The chosen family as an affine open cover of the glued scheme

`Oka/Analytification/SpecRefinedCover.lean`, which is the whole file. Appended as its own section
for the reason the sections above give: a section moved is a conflict for somebody else.

**The second guard below is the first applied twice.** The first assembles the four functions
`ComplexAnalytic.exists_family_mvPolynomial_basicOpen_specSchemeIotaMap` chooses into an
`AlgebraicGeometry.Scheme.AffineOpenCover` whose index type is the points of the glued scheme; the
second is that theorem with `ComplexAnalytic.opensRange_presentationRefinedIota_le` at each of its
two conjuncts.

**`Classical.choice` is in every guard below and is not a surprise**: the theorem they descend
from is a `choose` over the points of a scheme, and its own guard in this file records the same
three axioms. **What they check that the guards on
`ComplexAnalytic.exists_family_mvPolynomial_basicOpen_specSchemeIotaMap` and
`ComplexAnalytic.exists_family_opensRange_presentationRefinedIota_eq` do not is that building the
structure introduced nothing** — the covering field is the choice step's own second conjunct after
one rewrite, and if that were not so the axiom list would be the place it showed.

**Named and not located.** No sentence here says which section is above or below it; the next
branch appends between them.
-/

/--
info: 'ComplexAnalytic.exists_affineOpenCover_opensRange_presentationRefinedIota_eq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.exists_affineOpenCover_opensRange_presentationRefinedIota_eq

/--
info: 'ComplexAnalytic.exists_affineOpenCover_opensRange_le' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.exists_affineOpenCover_opensRange_le

/-! ### The refined cover's space maps onto the one it refines

`Oka/Analytification/RefineDatumCover.lean`'s refining condition, the image of the morphism down
and the surjectivity that follows, and the condition and the surjectivity again at the trivial
refining family. Appended as its own section rather than merged into an existing one, and the
reason is stated here rather than cited: moving or reordering a section of this file is a conflict
for every branch that has appended to it, and several appended to it on the day this was written.

**What the guards below are a check of is the one place on this line that needs an equality
of ranges rather than a containment.** `ComplexAnalytic.range_base_refineDatumToBase` computes the
image of `ComplexAnalytic.refineDatumToBase` — guarded here — and its `⊇` half spends
`ComplexAnalytic.range_base_localisationProj`, the equality, where every other consumer on this
line of files spends `ComplexAnalytic.range_base_localisationProj_subset`. The others are
corollaries of it, of `Oka/Analytification/RefineDatumWitness.lean`'s trivial-family witness, or
of the condition `ComplexAnalytic.RefineDatumCovers`, which is a `Prop`-valued definition and is
guarded because every hypothesis on this line is.

**`Classical.choice` is in every guard below and is not a surprise**: the source's own glue data is
built by `ComplexAnalytic.refineDatumOneR` and `ComplexAnalytic.refineDatumOneU`, both `choose`n,
and `AlgebraicGeometry.LocallyRingedSpace.GlueData.ι_jointly_surjective` runs through the gluing's
construction. This file's guards for `ComplexAnalytic.refineDatumToBase` and
`ComplexAnalytic.refineDatumOneAnalytification` record the same three.

**Named and not located, and this section holds itself to that.** No sentence in it says which
section precedes or follows it — including the placement sentence, which gives its reason instead
of citing a neighbour's; the next branch appends between them.
-/

/--
info: 'ComplexAnalytic.RefineDatumCovers' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.RefineDatumCovers

/--
info: 'ComplexAnalytic.refineDatumToBase_base_coverIota' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumToBase_base_coverIota

/--
info: 'ComplexAnalytic.range_base_refineDatumToBase' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.range_base_refineDatumToBase

/--
info: 'ComplexAnalytic.surjective_base_refineDatumToBase' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.surjective_base_refineDatumToBase

/--
info: 'ComplexAnalytic.surjective_base_refineDatumToBase_iff' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.surjective_base_refineDatumToBase_iff

/--
info: 'ComplexAnalytic.refineDatumOneCovers' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumOneCovers

/--
info: 'ComplexAnalytic.surjective_base_refineDatumOneToBase' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.surjective_base_refineDatumOneToBase

/-! ### The refining condition is strictly stronger than the surjectivity it gives

`Oka/Analytification/RefineDatumCover.lean`'s counterexample section, and the two general lemmas
that explain it. Appended as its own section rather than merged into an existing one, and the
reason is stated here rather than cited: moving or reordering a section of this file is a conflict
for every branch that has appended to it.

**What the guards below are a check of is a non-implication.**
`ComplexAnalytic.dupStrict` exhibits a cover datum, an index map and a refining family at which
`ComplexAnalytic.refineDatumToBase` is surjective on bases and `ComplexAnalytic.RefineDatumCovers`
is false — so the sufficient condition guarded above is not necessary, and the three sentences of
`Oka/Analytification/RefineDatumCover.lean` that say *strictly* now have a theorem under them.
`ComplexAnalytic.dupSurjective_refine` and `ComplexAnalytic.dupNot_refineDatumCovers` are its two
halves and are guarded separately because each is quotable on its own;
`ComplexAnalytic.dupPtStrict` is the same statement with the point hypothesis discharged, and it
is the one that makes the counterexample unconditional.

`ComplexAnalytic.mem_range_of_refineDatumCovers` and
`ComplexAnalytic.not_refineDatumCovers_of_notMem_range` are the general reason: the condition
forces the index map to hit every index whose member has a point, which the glued-space form does
not ask, and which is why `ComplexAnalytic.refineDatumOneCovers` takes a surjectivity hypothesis.

**The split between what this section guards and what it deliberately leaves unguarded is named on
both sides, and the two sides are not one section of that file.** Guarded are the general lemmas
`ComplexAnalytic.mem_range_of_refineDatumCovers` and
`ComplexAnalytic.not_refineDatumCovers_of_notMem_range`, which are under that file's
`### The condition` and not under its counterexample section, together with the statements of the
witness `ComplexAnalytic.dupSurjective_refine`, `ComplexAnalytic.dupNot_refineDatumCovers`,
`ComplexAnalytic.dupStrict` and `ComplexAnalytic.dupPtStrict`, each guarded immediately below.
**What the counterexample section adds beyond those is the witness's plumbing**, and it is listed
here in full, because a sentence that says what is
deliberately unguarded is worth nothing if a reader cannot check it against the section: the
index type `ComplexAnalytic.dupIdx` and `ComplexAnalytic.dup_no_three`; the cover datum's own six
pieces — `ComplexAnalytic.dupObj`, `ComplexAnalytic.dupPoly`, `ComplexAnalytic.dupGlue` and the
**three** law proofs `ComplexAnalytic.dupHsymm`, `ComplexAnalytic.dupHrange`,
`ComplexAnalytic.dupHcocycle`; the index map `ComplexAnalytic.dupSigma`, which is the one that
misses the second member; the two steps `ComplexAnalytic.dupCoverOpen_eq_top` and
`ComplexAnalytic.dupSurjective_coverIota` that carry the redundancy argument; and
`ComplexAnalytic.dupPtPres` with `ComplexAnalytic.dupPtPoint`, the presentation of a point and the
point itself. `Oka/Analytification/GlueShape.lean`'s counterexample
sets the convention this follows: it guards `ComplexAnalytic.GlueShape.not_ctHRange` and advertises
none of the `ct` definitions that produce it.

**This account of the split read *"Nineteen declarations land in that section, six of them
guarded"* before it was swept, and the numeral was exact for a set the sentence did not name.**
`2de5583` wrote it and says it measured on `e2ba53b`, and nineteen is what `e2ba53b` *adds* to
`Oka/Analytification/RefineDatumCover.lean` — a count of a push, and `e2ba53b` is where it is
exact. What that file's counterexample section holds is seventeen declarations, four of them
guarded, at `e2ba53b` and at `c367aa8` alike: `ComplexAnalytic.mem_range_of_refineDatumCovers` and
`ComplexAnalytic.not_refineDatumCovers_of_notMem_range` went in under `### The condition` in the
same push, which is why this section's opening sentence lists them separately from it. **A count
of a commit is not a count of a section**, and the thirteen that went with the nineteen was exact
for the counterexample section under either reading, which is why nothing in the enumeration
moved.

**Three laws are proved and two of them are vacuous, which are different counts and the ones the
prose above must not collapse.** `ComplexAnalytic.dup_no_three` makes the two *triple-overlap*
hypotheses vacuous — `ComplexAnalytic.GlueShape.HRange` and `ComplexAnalytic.GlueShape.HCocycle`,
through `ComplexAnalytic.GlueShape.hRange_of_no_three` and
`ComplexAnalytic.GlueShape.hCocycle_of_no_three`. `ComplexAnalytic.dupHsymm` is not one of them: it
is the symmetry law, it is proved outright rather than vacuously, and the reason is that a
reflexive isomorphism is its own inverse. So *"three laws are proved here"* and *"two of this
datum's laws are vacuous"* are both true and count different sets; a sentence that says **two law
proofs** has collapsed them and has dropped `ComplexAnalytic.dupHsymm` on the way.

**`Classical.choice` is in every guard below for the reason the sections on the rest of that file
give** — the refined glue data is built from two `choose`n witnesses — and not because anything
here is a choice.

**Named and not located.** No sentence in this section says which section precedes or follows it;
the next branch appends between them.
-/

/--
info: 'ComplexAnalytic.mem_range_of_refineDatumCovers' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.mem_range_of_refineDatumCovers

/--
info: 'ComplexAnalytic.not_refineDatumCovers_of_notMem_range' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.not_refineDatumCovers_of_notMem_range

/--
info: 'ComplexAnalytic.dupSurjective_refine' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.dupSurjective_refine

/--
info: 'ComplexAnalytic.dupNot_refineDatumCovers' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.dupNot_refineDatumCovers

/--
info: 'ComplexAnalytic.dupStrict' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.dupStrict

/--
info: 'ComplexAnalytic.dupPtStrict' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.dupPtStrict

/-! ### The refining condition at an index map that is the identity

`Oka/Analytification/RefineDatumCover.lean`'s
`### The condition at an index map that is the identity`, which reads
`ComplexAnalytic.RefineDatumCovers` at `σ = id` — where the index a point must be reached through
is forced, the identification of two members is the identity, and the condition is left saying that
each `D(fam i)` is the whole of its member. Appended as its own section rather than merged into an
existing one, and the reason is stated here rather than cited: moving or reordering a section of
this file is a conflict for every branch that has appended to it.

**What the guards below are a check of is a collapse and not a new geometry.** Every one of those
proofs is the identification being disposed of by `ComplexAnalytic.coverSpaceHomOfEq_self`, so
`Classical.choice` is in every guard below for the reason the sections above it give — the refined
glue data is built from two `choose`n witnesses — and not because anything here is a choice.

**The consumer is in the test library and carries no guard**, which is that library's convention
rather than an omission: `OkaTest/RefineDatumUnitFamily.lean` applies
`ComplexAnalytic.not_refineDatumCovers_id_of_ne_top` to `ComplexAnalytic.lineRefinement` and
concludes that the one refinement in this repository that cuts its members down does not meet the
condition.

**What none of the guards below says is anything about surjectivity.**
`ComplexAnalytic.dupStrict`, guarded above, is the theorem that the condition is strictly stronger
than the surjectivity of `ComplexAnalytic.refineDatumToBase`, so refuting the condition at a datum
decides nothing about that morphism there.

**Named and not located.** No sentence in this section says which section precedes or follows it;
the next branch appends between them.
-/

/--
info: 'ComplexAnalytic.mem_localisationOpen_of_refineDatumCovers_id' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.mem_localisationOpen_of_refineDatumCovers_id

/--
info: 'ComplexAnalytic.localisationOpen_eq_top_of_refineDatumCovers_id' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.localisationOpen_eq_top_of_refineDatumCovers_id

/--
info: 'ComplexAnalytic.not_refineDatumCovers_id_of_ne_top' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.not_refineDatumCovers_id_of_ne_top

/-! ### The refining condition at an identity index map is that equation, and not merely implies it

The converse half of `Oka/Analytification/RefineDatumCover.lean`'s
`### The condition at an index map that is the identity`, and the `Iff` that
joins the two. **Appended as its own section rather than merged into the one that guards the
forward half**, for the reason this file gives everywhere: moving or reordering a section is a
conflict for every branch that has appended to it, and a section that counts only its own guards
cannot be made stale by an append.

**What the guards below are a check of is that five sentences became true.** The branch that
built the forward direction said at five sites that the condition at `σ = id` *is* `∀ i, D(fam i) =
⊤`, and proved `→`; `ComplexAnalytic.refineDatumCovers_id_iff` is the biconditional those sentences
assert, so they are now statements of a theorem rather than of a reading.
`ComplexAnalytic.refineDatumCovers_id_of_forall_eq_top` is the direction that was missing and it is
a term with no tactic in it.

**`Classical.choice` is in every guard below for the reason the other sections of this file
give** — the refined glue data is built from two `choose`n witnesses — and not because anything
here is a choice.

**Named and not located.** No sentence in this section says which section precedes or follows it;
the next branch appends between them.
-/

/--
info: 'ComplexAnalytic.refineDatumCovers_id_of_forall_eq_top' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumCovers_id_of_forall_eq_top

/--
info: 'ComplexAnalytic.refineDatumCovers_id_iff' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumCovers_id_iff

/-! ### The morphism down at a family that is a unit on each overlap

`Oka/Analytification/RefineDatumCover.lean`'s
`### The instance at a family that is a unit on each overlap`, which names
`ComplexAnalytic.refineDatumToBase` at an injective index map and a family that is a unit on each
overlap, and reads the surjectivity equivalence at those arguments. Appended as its own section
rather than merged into any above it, and the reason is stated here rather than cited: moving or
reordering a section of this file is a conflict for every branch that has appended to it.

**One of the guards below is for a definition.** `ComplexAnalytic.refineDatumUnitFamToBase` is a
`def` and is advertised under `## Main definitions` rather than `## Main results`, so
`scripts/guard_coverage.py` counts it as guarded and advertised nowhere — which is that script's
own recorded behaviour for a definition and not a gap.
`ComplexAnalytic.surjective_base_refineDatumUnitFamToBase_iff` is the theorem and is advertised.

**Neither is a new construction.** The definition is the general morphism at the unit family's own
choices and the theorem is the general equivalence read at them, so `Classical.choice` is in every
guard below for the reason the other sections of this file give — the refined glue data is built
from two `choose`n witnesses — and not because anything here is a choice.

**Named and not located.** No sentence in this section says which section precedes or follows it;
the next branch appends between them.
-/

/--
info: 'ComplexAnalytic.refineDatumUnitFamToBase' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumUnitFamToBase

/--
info: 'ComplexAnalytic.surjective_base_refineDatumUnitFamToBase_iff' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.surjective_base_refineDatumUnitFamToBase_iff

/-! ### The overlap of two refined members at one immersion

The declarations under `Oka/Analytification/SpecRefinedMemberSection.lean`'s own overlap heading
that are stated at an arbitrary open immersion, together with the declaration
`Oka/Analytification/SpecDistinguishedOpen.lean` gained for them — the same shape as
`### A distinguished open of a member, as an affine open of the glued scheme`, and for the same
reason. Appended as its own section for the reason the sections above give: a section moved is a
conflict for somebody else.

**That qualifier is not decoration and it replaces a count that read low.** This clause read *"the
five declarations"* under that heading, and the heading also holds one that this section does not
guard: `ComplexAnalytic.opensRange_refinedIota_eq_basicOpen`, the member-level range statement,
guarded under `### The refined member's range, in the section vocabulary` instead.

**Its own section rather than an insertion under either of that file's two headings here, and the
reason is the subject and not the file.** `### The refined member, at an arbitrary open immersion`
covers the general level of `Oka/Analytification/SpecRefinedMember.lean` and of that file, and it
pairs its general declarations with member-level ones, saying in terms that the two sets are not
independent; these have no member-level counterpart, so inserting them there would falsify that
pairing while stating nothing about it. `### The refined member's range, in the
section vocabulary` is about one member's range, and these are about two members' overlap.

**What each of the guards below is a check of.** `ComplexAnalytic.presentationSection_mul` is two
`map_mul`s and is here because it is a declaration and not because anything about it is
surprising. `ComplexAnalytic.opensRange_presentationRefinedIota_inf` is
`AlgebraicGeometry.Scheme.basicOpen_mul` read through the general range theorem;
`ComplexAnalytic.basicOpen_res_presentationSection` is `AlgebraicGeometry.Scheme.basicOpen_res`
with no affineness hypothesis and `ComplexAnalytic.basicOpen_res_presentationSection'` is that
theorem at the exchanged pair and one `inf_comm`.
`ComplexAnalytic.image_basicOpen_rename_Spec_map_localisationRingHom` is the one that carries
content — an image of a preimage under an open immersion, on `Spec` and with no section in
sight — and `ComplexAnalytic.opensRange_presentationRefinedIota_rename` is that theorem transported
up along the caller's immersion. **`Classical.choice` is in every guard below for the reason the
sections on the rest of that file give** — the scheme structure underneath is built from chosen
witnesses — and not because anything here is a choice.

**What these do not assert, said here because a guard file is where a reader checks a claim against
a list.** None of them is a `poly`, none quantifies over two indices, and none says anything about
two members of a cover datum chosen inside *different* members — which is the half of the
doubly-distinguished condition that file's own prose says is not supplied. **What they now do
assert is that half's complement**: at two refined members of the *same* immersion the overlap is a
refined member of each of them at a polynomial in that member's own variables, which is the
doubly-distinguished condition there and is not the same claim as being a `poly`.

**Named and not located.** No sentence here says which section is above or below it. -/

/--
info: 'ComplexAnalytic.presentationSection_mul' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.presentationSection_mul

/--
info: 'ComplexAnalytic.opensRange_presentationRefinedIota_inf' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.opensRange_presentationRefinedIota_inf

/--
info: 'ComplexAnalytic.basicOpen_res_presentationSection' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.basicOpen_res_presentationSection

/--
info: 'ComplexAnalytic.basicOpen_res_presentationSection'' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.basicOpen_res_presentationSection'

/--
info: 'ComplexAnalytic.image_basicOpen_rename_Spec_map_localisationRingHom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.image_basicOpen_rename_Spec_map_localisationRingHom

/--
info: 'ComplexAnalytic.opensRange_presentationRefinedIota_rename' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.opensRange_presentationRefinedIota_rename

/-! ### The refined members as an open cover of the space they refine

`Oka/Analytification/RefineDatumCover.lean`'s open-cover section, together with the lemma that
section moved the refining condition into. Appended as its own section rather than merged into an
existing one, and the reason is stated rather than cited: moving or reordering a section of this
file is a conflict for every branch that has appended to it, and several have.

**What the guards below are a check of is that a cover of `X^an` by the refined members needs no
refined datum.** Every one of them but three is stated at an index map and a refining family alone
— `ComplexAnalytic.refineDatumMemberIota` is `ComplexAnalytic.localisationProj` followed by
`ComplexAnalytic.coverIota`, and no cross-member choice, no `q` and none of the three refined
laws appears in any of them. The other three are
`ComplexAnalytic.range_base_refineDatumToBase_eq_iUnion_range`,
`ComplexAnalytic.surjective_base_refineDatumToBase_iff_iUnion_range` and
`ComplexAnalytic.refineDatumOneOpenCover`, and the first two are the bridge to the morphism down.

**`Classical.choice` is in every guard below and two declarations are why.**
`ComplexAnalytic.refineDatumOpenCover`'s `idx` field chooses an index for each point, which is
what makes that definition `noncomputable`, and
`AlgebraicGeometry.LocallyRingedSpace.GlueData.ι_jointly_surjective` runs through the gluing's
construction inside
`ComplexAnalytic.iUnion_coverIota_image_localisationOpen_eq_univ`. Every guard in this file for a
declaration of that module records the same three.

**Named and not located, and this section holds itself to that.** No sentence in it says which
section precedes or follows it; the next branch appends between them.
-/

/--
info: 'ComplexAnalytic.iUnion_coverIota_image_localisationOpen_eq_univ' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.iUnion_coverIota_image_localisationOpen_eq_univ

/--
info: 'ComplexAnalytic.refineDatumMemberIota' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumMemberIota

/--
info: 'ComplexAnalytic.isOpenImmersion_refineDatumMemberIota' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isOpenImmersion_refineDatumMemberIota

/--
info: 'ComplexAnalytic.range_base_refineDatumMemberIota' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.range_base_refineDatumMemberIota

/--
info: 'ComplexAnalytic.iUnion_range_base_refineDatumMemberIota' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.iUnion_range_base_refineDatumMemberIota

/--
info: 'ComplexAnalytic.iUnion_range_base_refineDatumMemberIota_eq_univ' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.iUnion_range_base_refineDatumMemberIota_eq_univ

/--
info: 'ComplexAnalytic.refineDatumOpenCover' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumOpenCover

/--
info: 'ComplexAnalytic.refineDatumOpenCover_obj' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumOpenCover_obj

/--
info: 'ComplexAnalytic.refineDatumOpenCover_map' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumOpenCover_map

/--
info: 'ComplexAnalytic.range_base_refineDatumToBase_eq_iUnion_range' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.range_base_refineDatumToBase_eq_iUnion_range

/--
info: 'ComplexAnalytic.surjective_base_refineDatumToBase_iff_iUnion_range' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.surjective_base_refineDatumToBase_iff_iUnion_range

/--
info: 'ComplexAnalytic.refineDatumOneOpenCover' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumOneOpenCover

/-! ### The refined space's own cover, and the factorisation through the morphism down

`Oka/Analytification/RefineDatumCover.lean`'s cover of the space a cross-member refinement glues
to, and the two statements that carry each of its maps down to a member of the cover of `X^an`.
Appended as its own section rather than merged into an existing one, and the reason is stated
rather than cited: moving or reordering a section of this file is a conflict for every branch that
has appended to it, and several have.

**What these are a check of is the opposite of what the section above them checks**, which is why
they are guarded apart: every declaration here reads the whole refined datum — the caller's `q`,
the cross-member choices `rr` and `uu` and the two adopted conditions — because the space it covers
is the gluing those produce. A declaration here that elaborated without them would be a
declaration about the wrong space.

**`Classical.choice` in every guard below, and the `idx` field is again why.** The cover is
`ComplexAnalytic.coverAnalytificationOpenCover` at the refined datum, and
`AlgebraicGeometry.LocallyRingedSpace.GlueData.openCover` chooses an index for each point of the
gluing; the theorems inherit it through the definition they are about.

**No sentence here names a neighbouring section, and none says how much of that module this
section covers** — the two properties this file can actually hold itself to, and an append
elsewhere leaves both of them true.
-/

/--
info: 'ComplexAnalytic.refineDatumGluedOpenCover' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumGluedOpenCover

/--
info: 'ComplexAnalytic.refineDatumGluedOpenCover_obj' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumGluedOpenCover_obj

/--
info: 'ComplexAnalytic.refineDatumGluedOpenCover_map' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumGluedOpenCover_map

/--
info: 'ComplexAnalytic.refineDatumGluedOpenCover_map_comp_refineDatumToBase' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumGluedOpenCover_map_comp_refineDatumToBase

/--
info: 'ComplexAnalytic.refineDatumOpenCover_map_eq_comp' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumOpenCover_map_eq_comp

/-! ### The refined datum refines the cover it refines

`Oka/Analytification/RefineDatumRefines.lean`'s equality at a pair of refined members lying over
one member of the original cover, its instance at a constant index map, the containment where they
lie over two, and `ComplexAnalytic.coverIota_image_inter_of_eq`, the transport the equality is
built on, which that file declares itself — together with the three lemmas they are built from,
which are guarded here although they live in the two files that own their subjects, since nothing
else in this file guards them. Appended as its own section rather than merged into another: moving
or reordering a section of this file is a conflict for every branch that has appended to it.

**What the guards below are a check of is one lemma and one `subst`.**
`ComplexAnalytic.image_base_localisationProj_localisationOpen_rename` is
`ComplexAnalytic.localisationOpen_rename` read forwards, and it spends
`ComplexAnalytic.range_base_localisationProj` — the equality — rather than
`ComplexAnalytic.range_base_localisationProj_subset`, because the image of a preimage is the set
met with the *range* and the containment would give one inclusion of the two.
`ComplexAnalytic.coverIota_image_inter_of_eq` is where the transport along `σ a = σ b` is paid, by
`subst` at two free indices, and it is the only consumer of
`ComplexAnalytic.injective_base_coverIota`.

**`Classical.choice` is in every guard below and is not a surprise**:
`ComplexAnalytic.polyDiagOne` and `ComplexAnalytic.refineDatumFactor` are both `open Classical`
case splits, and the analytification of a presentation runs through a gluing. The guards this file
carries for `ComplexAnalytic.refineDatumToBase` and
`ComplexAnalytic.range_base_refineDatumToBase` record the same three.

**Named and not located.** No sentence here says which section precedes or follows it.
-/

/--
info: 'ComplexAnalytic.image_base_localisationProj_localisationOpen_rename' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.image_base_localisationProj_localisationOpen_rename

/--
info: 'ComplexAnalytic.injective_base_coverIota' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.injective_base_coverIota

/--
info: 'ComplexAnalytic.coverIota_image_coverOpen' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverIota_image_coverOpen

/--
info: 'ComplexAnalytic.coverIota_image_inter_of_eq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverIota_image_inter_of_eq

/--
info: 'ComplexAnalytic.refineDatumMemberIota_image_coverOpen_of_eq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumMemberIota_image_coverOpen_of_eq

/--
info: 'ComplexAnalytic.refineDatumMemberIota_image_coverOpen_const' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumMemberIota_image_coverOpen_const

/--
info: 'ComplexAnalytic.refineDatumMemberIota_image_coverOpen_subset_of_ne' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumMemberIota_image_coverOpen_subset_of_ne

/-! ### The refined datum refines across members, and the two members meet in nothing else

**Every declaration of `Oka/Analytification/RefineDatumRefinesCross.lean`** — its equality at a
pair of refined members lying over two different members of the original cover, the family of
extra factors at which that holds at every ordered pair, and the steps under its earlier headings
that those two are proved through — together with the lemmas written for them elsewhere: in
`Oka/Analytification/AffineCover.lean`, and in the files that own evaluation and the non-vanishing
locus. They are guarded here because nothing else in this file guards them. Appended as its own
section rather than merged into the one above, for the reason that section gives: moving or
reordering a section of this file is a conflict for every branch that has appended to it.

**The enumeration above counts nothing, and that is deliberate rather than an omission.** A clause
that counts the declarations of a file or the guards of a section is falsified by the next append
to either, and the section above this one had exactly such a clause repaired by a separate branch
on 2026-09-04 — it had enumerated six of its seven guards. The spelling that survives an append is
the one used here: name the file whose declarations are guarded and the files the rest were
written in, and leave the arithmetic to a reader, who can run `grep -c '#print axioms'` over the
section and get an answer that is right on the day they run it.

**What the guards are a check of is two things and neither is analytic.**
`ComplexAnalytic.localisationOpen_eq_of_isUnit_mul` is the whole of the passage from an identity
between classes in a presented algebra to an equality of non-vanishing loci — evaluation at a
point kills the presentation ideal, and a unit does not vanish — and
`ComplexAnalytic.preimage_range_coverIota` is the whole of the passage from the glue data's
description of when two points of two members become one to the statement that the two members
meet in the overlap and in nothing else. Everything else here is bookkeeping between the two.

**`Classical.choice` is in every guard below and is expected**:
`ComplexAnalytic.refineDatumFactor` is an `open Classical` case split, the analytification of a
presentation runs through a gluing, and the last guard's statement is an existential produced by
`choose` from another one.

**Named and not located.** No sentence here says which section precedes or follows it.
-/

/--
info: 'ComplexAnalytic.quotientEval_mk' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.quotientEval_mk

/--
info: 'ComplexAnalytic.localisationOpen_eq_of_isUnit_mul' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.localisationOpen_eq_of_isUnit_mul

/--
info: 'ComplexAnalytic.range_coverTransitionHom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.range_coverTransitionHom

/--
info: 'ComplexAnalytic.preimage_range_coverIota' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.preimage_range_coverIota

/--
info: 'ComplexAnalytic.range_coverIota_inter' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.range_coverIota_inter

/--
info: 'ComplexAnalytic.coverOverlapIso_hom_coverTransitionHom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverOverlapIso_hom_coverTransitionHom

/--
info: 'ComplexAnalytic.base_coverIota_localisationProj' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.base_coverIota_localisationProj

/--
info: 'ComplexAnalytic.image_localisationOpen_localisationProj' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.image_localisationOpen_localisationProj

/--
info: 'ComplexAnalytic.localisationOpen_rename_eq_comap_coverGlueIso' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.localisationOpen_rename_eq_comap_coverGlueIso

/--
info: 'ComplexAnalytic.coverIota_image_localisationOpen_of_ne' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverIota_image_localisationOpen_of_ne

/--
info: 'ComplexAnalytic.refineDatumMemberIota_image_coverOpen_of_ne' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumMemberIota_image_coverOpen_of_ne

/--
info: 'ComplexAnalytic.exists_refineDatumMemberIota_image_coverOpen' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.exists_refineDatumMemberIota_image_coverOpen
