/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka

/-!
# Axiom regression tests: General sheaf theory and ringed spaces

Results that mention nothing analytic: presheaves and sheaves on a topological space, and the
presheaved, ringed and locally ringed spaces built out of them — gluing, open immersions, global
sections and germs, algebra structures over a cover, stalk maps and colimits, inverse images and
sheets, and the `Γ`-`Spec` adjunction. What is guarded here is mirror-tree material of
`Oka/Geometry/RingedSpace/`, together with material from `Oka/Topology/` and
`Oka/AlgebraicGeometry/`.

**That is a description and not a list, and the headings below are the record**: every one of
them names the module, or all the modules, that its assertions defend, so that mapping lives
next to the assertions and not in this paragraph. The stance is
`OkaTest/Axioms/LocalOkaRing.lean`'s, and it is taken here because the mix moves — the sentence
this replaces named `Oka/Topology/Sheaves/`, which on 2026-08-28 accounted for four of the
eighty-seven guards below, and `Oka/CategoryTheory/`, which accounted for none of them.

**One file and not two, and the reason is not inertia.** The obvious cut — sheaves off from
ringed spaces — is clean at the section boundary, but what it cuts off is the sections whose
module is under `Oka/Topology/Sheaves/`, and what it leaves undivided is the
locally-ringed-space material, the side that actually grows; it therefore buys none of the
concurrent-pull-request relief that `OkaTest/Axioms.lean` gives as the whole point of splitting.
The cut that would buy it is by module *within* `Oka/Geometry/RingedSpace/`, and that is a
larger proposal than a wrong docstring: it moves every `#guard_msgs` block in the file at once
and conflicts with every branch in flight. **If this file's size ever starts costing rebases,
split it that way and not the obvious way.** Note also that `OkaTest/Axioms.lean`'s routing
table names only "general presheaf and sheaf theory" for this file: a ringed-space assertion
belongs here too.

See `OkaTest/Axioms.lean` for what these assertions are for and how to update one.
-/

/-! ### Quotients of presheaves of rings

`Oka/Topology/Sheaves/QuotientPresheaf.lean`. -/

/--
info: 'TopCat.Presheaf.surjective_stalkFunctor_map_toQuotientSpan' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TopCat.Presheaf.surjective_stalkFunctor_map_toQuotientSpan

/--
info: 'TopCat.Presheaf.ker_stalkFunctor_map_toQuotientSpan' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TopCat.Presheaf.ker_stalkFunctor_map_toQuotientSpan


/-! ### Pushforward along an embedding is fully faithful

`Oka/Topology/Sheaves/Functors.lean`, for presheaves and for sheaves. -/

/--
info: 'TopCat.Presheaf.pushforwardFullyFaithful' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TopCat.Presheaf.pushforwardFullyFaithful

/--
info: 'TopCat.Sheaf.pushforwardFullyFaithful' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TopCat.Sheaf.pushforwardFullyFaithful

/-! ### Gluing locally ringed spaces along an open cover

`Oka/Geometry/RingedSpace/PresheafedSpace/Gluing.lean`. -/

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.GlueData.ι_eq_iff' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.GlueData.ι_eq_iff

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.GlueData.isOpen_iff' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.GlueData.isOpen_iff

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.OpenCover.isIso_fromGlued' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.OpenCover.isIso_fromGlued

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.OpenCover.glueMorphisms' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.OpenCover.glueMorphisms

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.OpenCover.existsUnique_glueMorphisms' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.OpenCover.existsUnique_glueMorphisms

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.openCoverOfOpens' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.openCoverOfOpens

/-! ### Two open immersions of locally ringed spaces with the same image

`Oka/Geometry/RingedSpace/OpenImmersion.lean`. -/

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.isoOfRangeEq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.isoOfRangeEq

/-! ### Gluing morphisms over a cover by open subsets

`Oka/Geometry/RingedSpace/OpenImmersion.lean`,
`Oka/Geometry/RingedSpace/PresheafedSpace/Gluing.lean` and
`Oka/Geometry/RingedSpace/LocallyRingedSpace.lean` — the range of a pullback and `restrictLE`,
the gluing itself, and the two empty-cover extensionality lemmas. -/

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.range_pullback_to_base_of_left' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.range_pullback_to_base_of_left

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.restrictLE' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.restrictLE

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.existsUnique_glueMorphisms_of_opens' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.existsUnique_glueMorphisms_of_opens

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.hom_ext_of_isEmpty' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.hom_ext_of_isEmpty


/--
info: 'AlgebraicGeometry.LocallyRingedSpace.hom_ext_restrict_of_isEmpty' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.hom_ext_restrict_of_isEmpty

/-! ### Locality of global sections

`Oka/Geometry/RingedSpace/LocallyRingedSpace.lean`. -/

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.section_ext_of_cover' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.section_ext_of_cover

/-! ### Functoriality of global sections, read elementwise

`Oka/Geometry/RingedSpace/LocallyRingedSpace.lean`. The two lemmas the `Iso` versions
below specialise: `AlgebraicGeometry.LocallyRingedSpace.Γ` is contravariant, and these
say so at an element rather than at the map. -/

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.Γ_map_id_apply' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.Γ_map_id_apply

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.Γ_map_comp_apply' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.Γ_map_comp_apply

/-! ### Crossing an isomorphism on global sections

`Oka/Geometry/RingedSpace/LocallyRingedSpace.lean`. -/

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.Γ_map_inv_hom_apply' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.Γ_map_inv_hom_apply

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.Γ_map_hom_inv_apply' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.Γ_map_hom_inv_apply

/-! ### Sections and germs on an open subspace

`Oka/Geometry/RingedSpace/LocallyRingedSpace.lean`. -/

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.germ_eq_stalkMap_ofRestrict' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.germ_eq_stalkMap_ofRestrict

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.Γ_map_over_ambient' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.Γ_map_over_ambient


/--
info: 'AlgebraicGeometry.LocallyRingedSpace.germ_res' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.germ_res

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.c_app_res' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.c_app_res

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.Γ_map_ofRestrict_apply' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.Γ_map_ofRestrict_apply

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.Γgerm_Γ_map' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.Γgerm_Γ_map

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.restrictStalkIso_hom_stalkAlgMap' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.restrictStalkIso_hom_stalkAlgMap

/-! ### The image of an open subspace

`Oka/Geometry/RingedSpace/LocallyRingedSpace.lean`. What the underlying map of
`AlgebraicGeometry.LocallyRingedSpace.ofRestrict` hits, for one open and for a composite
of two. -/

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.range_ofRestrict' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.range_ofRestrict

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.range_ofRestrict_comp' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.range_ofRestrict_comp

/-! ### Lifting sections and germs along a stalkwise-surjective morphism

`Oka/Geometry/RingedSpace/LocallyRingedSpace.lean`'s `LocalModel` section. A germ in the
image of a stalk map is the germ of a section on a smaller open, and the family version
that a finite generating set needs. -/

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.exists_localLift' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.exists_localLift

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.exists_localCombination' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.exists_localCombination

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.exists_localLift_family' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.exists_localLift_family

/-! ### The `Γ`-`Spec` adjunction

`Oka/AlgebraicGeometry/GammaSpecAdjunction.lean`. Consumed by
`Oka/Analytification/Presentation.lean`. -/

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.toΓSpec_naturality' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.toΓSpec_naturality

/-! ### Gluing an algebra structure over an open cover

`Oka/Geometry/RingedSpace/LocallyRingedSpace.lean`. -/

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.existsUnique_glueSection' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.existsUnique_glueSection

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.glueSection' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.glueSection

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.glueSection_eq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.glueSection_eq

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.isCompatible_map_le_top' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.isCompatible_map_le_top

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.glueSection_map_le_top' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.glueSection_map_le_top

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.resAlgMap_eq_comp' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.resAlgMap_eq_comp

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.glueAlgMap' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.glueAlgMap

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.resAlgMap_glueAlgMap' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.resAlgMap_glueAlgMap

/-! ### Pulling an algebra structure back, and gluing one given on the members of a cover

`Oka/Geometry/RingedSpace/LocallyRingedSpace.lean` and
`Oka/Geometry/RingedSpace/PresheafedSpace/Gluing.lean`. -/

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.comapAlgMap' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.comapAlgMap

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.comapAlgMap_ofRestrict' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.comapAlgMap_ofRestrict

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.comapAlgMap_comp' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.comapAlgMap_comp

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.comapAlgMap_hom_injective' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.comapAlgMap_hom_injective

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.iSup_isOpenEmbedding_obj_top' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.iSup_isOpenEmbedding_obj_top

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.glueAlgMapRestrict' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.glueAlgMapRestrict

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.resAlgMap_glueAlgMapRestrict' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.resAlgMap_glueAlgMapRestrict

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.OpenCover.opensRange' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.OpenCover.opensRange

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.OpenCover.iSup_opensRange' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.OpenCover.iSup_opensRange

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.OpenCover.isoRestrict' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.OpenCover.isoRestrict

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.OpenCover.isoRestrict_hom_fac' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.OpenCover.isoRestrict_hom_fac

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.OpenCover.restrictAlgMap' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.OpenCover.restrictAlgMap

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.OpenCover.restrictAlgMap_comapAlgMap' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.OpenCover.restrictAlgMap_comapAlgMap

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.GlueData.openCover' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.GlueData.openCover


/--
info: 'AlgebraicGeometry.LocallyRingedSpace.OpenCover' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.OpenCover

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.OpenCover.isCompatible_restrictAlgMap_comapAlgMap' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.OpenCover.isCompatible_restrictAlgMap_comapAlgMap

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.OpenCover.glueAlgMapRestrict_comapAlgMap' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.OpenCover.glueAlgMapRestrict_comapAlgMap

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.OpenCover.comapAlgMap_ext' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.OpenCover.comapAlgMap_ext

/-! ### The germ of a global section of `𝒪_{Spec R}` at a prime

`Oka/AlgebraicGeometry/Spec.lean`. Mirror-tree material with nothing analytic in it. -/

/--
info: 'AlgebraicGeometry.StructureSheaf.germ_algebraMap_mem_maximalIdeal_iff' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.StructureSheaf.germ_algebraMap_mem_maximalIdeal_iff

/--
info: 'AlgebraicGeometry.StructureSheaf.germ_algebraMap_mem_maximalIdeal_iff'' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.StructureSheaf.germ_algebraMap_mem_maximalIdeal_iff'

/-! ### Stalk maps along a factorisation, and the coproduct of locally ringed spaces

`Oka/Geometry/RingedSpace/LocallyRingedSpace.lean` and
`Oka/Geometry/RingedSpace/LocallyRingedSpace/HasColimits.lean`. Two out of three for stalk maps,
the coproduct's cover and the injectivity of its inclusions, and the four properties of a descent
map out of it that a finite étale morphism is built from, together with one that it is not built
from: `AlgebraicGeometry.LocallyRingedSpace.isSeparatedMap_base_sigmaDesc`, since
`IsSeparatedMap` is no part of `ComplexAnalytic.AnalyticSpace.IsFiniteEtale` and a descent map can
be finite étale without it.

**Since 2026-09-20 the last four assertions of this section are of a different kind from the rest
of it**, and the sentence above does not reach them: they are the identification of the
coproduct's space with the topological disjoint union of the members' —
`AlgebraicGeometry.LocallyRingedSpace.sigmaEquivSigma` and `…sigmaHomeoSigma`, with the two
equations that pin the map against `CategoryTheory.Limits.Sigma.ι`. They are the conclusion the
cover and the disjointness above are the hypotheses of, and taxis #2091 is what asked for them.

**Every declaration that second file lists under `## Main results` is asserted here, and that is
still not a complete guard of it.** The sentence that stood here named `sigmaOpenCover` among the
unasserted ones and it is asserted below; what remains unasserted is what the file does not
advertise — `exists_sigma_ι_base_eq`, `eq_of_sigmaι_base_eq`, `sigmaι_base_injective`,
`disjoint_range_sigmaι` and the rest. `python3 scripts/guard_coverage.py --by-file` is what
distinguishes the two, and it reports the advertised half only. -/

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.isIso_stalkMap_of_comp' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.isIso_stalkMap_of_comp

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.base_sigmaι_sigmaDesc' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.base_sigmaι_sigmaDesc

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.image_base_sigmaDesc' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.image_base_sigmaDesc

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.isClosedMap_base_sigmaDesc' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.isClosedMap_base_sigmaDesc

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.isSeparatedMap_base_sigmaDesc' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.isSeparatedMap_base_sigmaDesc

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.fiberSigmaDescEquiv' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.fiberSigmaDescEquiv

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.isLocalHomeomorph_base_sigmaDesc' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.isLocalHomeomorph_base_sigmaDesc

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.isIso_stalkMap_sigmaDesc' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.isIso_stalkMap_sigmaDesc


/--
info: 'AlgebraicGeometry.LocallyRingedSpace.sigmaOpenCover' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.sigmaOpenCover

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.sigma_ι_isOpenImmersion' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.sigma_ι_isOpenImmersion

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.exists_colimit_ι_base_eq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.exists_colimit_ι_base_eq

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.sigmaι_base_eq_iff' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.sigmaι_base_eq_iff

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.disjoint_opensRange_sigmaOpenCover' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.disjoint_opensRange_sigmaOpenCover

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.sigmaEquivSigma' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.sigmaEquivSigma

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.sigmaHomeoSigma' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.sigmaHomeoSigma

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.sigmaHomeoSigma_symm_apply' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.sigmaHomeoSigma_symm_apply

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.sigmaHomeoSigma_sigmaι_base' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.sigmaHomeoSigma_sigmaι_base

/-! ### The inverse image of a locally ringed space along a continuous map

`Oka/Geometry/RingedSpace/LocallyRingedSpace/InverseImage.lean`. The three definitions — the
space, the morphism to the base, and the comparison morphism a morphism into the base factors
through — and the results about each: for the morphism to the base, the same isomorphism read as
a statement about the stalks and as a statement about the morphism; for the comparison morphism,
that its base map is the identity, that it is a factorisation, and the two readings of its stalk
map. -/

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.inverseImage' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.inverseImage

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.stalkInverseImageIso' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.stalkInverseImageIso

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.inverseImageHom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.inverseImageHom

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.stalkMap_inverseImageHom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.stalkMap_inverseImageHom

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.toInverseImage' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.toInverseImage

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.toInverseImage_base' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.toInverseImage_base

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.toInverseImage_comp' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.toInverseImage_comp

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.stalkMap_toInverseImage' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.stalkMap_toInverseImage

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.isIso_stalkMap_toInverseImage' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.isIso_stalkMap_toInverseImage

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.isIso_toInverseImage' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.isIso_toInverseImage

/-! ### The sheets of a map

`Oka/Topology/IsLocalHomeomorph.lean`. The family of opens on which a map is an open embedding,
and that for a local homeomorphism it covers. Pure topology; the guards sit here, beside what
these lemmas were *written for* — that file's own docstring says so, and names
`AlgebraicGeometry.LocallyRingedSpace.sheetIso`, guarded under the next heading — and **not**
beside a consumer, because until now there was none: the sheet material below **deliberately does
not import** `Oka/Topology/IsLocalHomeomorph.lean`, to keep the `OpenPartialHomeomorph` chain out
of its closure, and says so in terms. `Oka/AnalyticSpace/CoveringSpace.lean` is the first module
of the library to import it at all, and **its** guards are in `OkaTest/Axioms/Morphisms.lean`. -/

/--
info: 'sheetOpens' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms sheetOpens

/--
info: 'IsLocalHomeomorph.exists_mem_sheetOpens' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms IsLocalHomeomorph.exists_mem_sheetOpens

/--
info: 'IsLocalHomeomorph.sSup_sheetOpens' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms IsLocalHomeomorph.sSup_sheetOpens


/-! ### The connected component of a point of a disjoint union

`Oka/Topology/Connected/Clopen.lean`. Pure topology, and the guard sits here for the reason the
sheets above do: beside the material of the same kind, and not beside its consumer, which is
`Oka/AnalyticSpace/ConnectedComponents.lean` and is guarded in `OkaTest/Axioms/Morphisms.lean`.
**One declaration, and it is the whole of that file.** -/

/--
info: 'connectedComponent_sigmaMk' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms connectedComponent_sigmaMk


/-! ### Over a sheet, the inverse image is the base

`Oka/Geometry/RingedSpace/LocallyRingedSpace/InverseImageSheet.lean`, which builds on the
inverse-image group directly above. The three definitions — the sheet mapped to the base, the
open it lies over, and the comparison between them — and the results that file advertises:
`AlgebraicGeometry.LocallyRingedSpace.coe_sheetImage`, which pins the open to `p '' V`,
`AlgebraicGeometry.LocallyRingedSpace.isIso_sheetHom`, and
`AlgebraicGeometry.LocallyRingedSpace.sheetIso`. -/

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.sheetToBase' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.sheetToBase

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.sheetImage' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.sheetImage

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.sheetHom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.sheetHom

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.coe_sheetImage' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.coe_sheetImage

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.isIso_sheetHom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.isIso_sheetHom

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.sheetIso' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.sheetIso

/-! ### Sections over the range of an open immersion of schemes

`Oka/AlgebraicGeometry/OpenImmersion.lean`, appended as its own section for the reason
`OkaTest/Axioms.lean` gives: a section moved is a conflict for somebody else. Mirror-tree
material with nothing analytic in it, and it sits with
`AlgebraicGeometry.StructureSheaf.germ_algebraMap_mem_maximalIdeal_iff` above rather than in
`OkaTest/Axioms/Analytification.lean` for the same reason that one does.

**The `def` is guarded here and not only the theorems.**
`AlgebraicGeometry.IsOpenImmersion.specΓIsoTop` is an isomorphism rather than a proposition, so
nothing else in this repository would notice if it started resting on a fourth axiom, and
`ComplexAnalytic.presentationSection` (`OkaTest/Axioms/Analytification.lean`) is the consumer
that would carry it.

**A first version of this section had four guards.** The fourth was for a definition spelled
*Scheme.Hom.opensRangeIso* — deliberately not backticked, since it names nothing in this tree —
which turned out to be `AlgebraicGeometry.IsOpenImmersion.ΓIsoTop` already in the mirror file's
own target module; that file's header records what happened. Nothing guards `ΓIsoTop` — it is
Mathlib's, and `OkaTest/Axioms.lean` scopes this directory to what this repository declares. -/

/--
info: 'AlgebraicGeometry.IsOpenImmersion.image_basicOpen_ΓIsoTop' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.IsOpenImmersion.image_basicOpen_ΓIsoTop

/--
info: 'AlgebraicGeometry.IsOpenImmersion.specΓIsoTop' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.IsOpenImmersion.specΓIsoTop

/--
info: 'AlgebraicGeometry.IsOpenImmersion.image_primeSpectrum_basicOpen' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.IsOpenImmersion.image_primeSpectrum_basicOpen


/-! ### The uniqueness of a morphism into an inverse image, and functoriality in the space over `Y`

`Oka/Geometry/RingedSpace/LocallyRingedSpace/InverseImage.lean`, the same module as
`### The inverse image of a locally ringed space along a continuous map`. **A section of its own
rather than an addition to that one**, and the reason is not that the subject changed: that
section's docstring *enumerates* what it holds — *"the three definitions … and the results about
each"* — so an addition to it would have to rewrite that enumeration, and a section moved is a
conflict for somebody else.

What is here is the half of that file's universal property that used to be absent — a morphism
into `p⁻¹Y` is determined by its base map together with its composite to `Y`, with the
sheafification uniqueness it rests on — and the functoriality of `p ↦ p⁻¹Y` in the space over `Y`,
which is what a morphism *out of* an inverse image is built from.

**Two of the four `def`s guarded here generate an equation lemma and neither equation lemma is
guarded** — `AlgebraicGeometry.LocallyRingedSpace.compHom` and
`AlgebraicGeometry.LocallyRingedSpace.inverseImageMap` are the two, and
`AlgebraicGeometry.LocallyRingedSpace.inverseImageIso` and
`AlgebraicGeometry.LocallyRingedSpace.inverseImageMapOfEq` are the two that generate none. That is
this module's convention rather than an omission: it already carried five equation lemmas before
this section, of `AlgebraicGeometry.LocallyRingedSpace.inverseImageAdjunct`,
`AlgebraicGeometry.LocallyRingedSpace.inverseImageDesc`,
`AlgebraicGeometry.LocallyRingedSpace.stalkInverseImageIso`,
`AlgebraicGeometry.LocallyRingedSpace.stalkToInverseImageSheafIso` and
`AlgebraicGeometry.LocallyRingedSpace.toInverseImageSheaf`, and
`git grep "print axioms AlgebraicGeometry.LocallyRingedSpace.<n>.eq_1" -- OkaTest` finds nothing
for any of the five, nor for `AlgebraicGeometry.LocallyRingedSpace.compHom.eq_1` and
`AlgebraicGeometry.LocallyRingedSpace.inverseImageMap.eq_1`, the two this section adds.

**That sentence said *six* and named `AlgebraicGeometry.LocallyRingedSpace.sheetToBase` as the
sixth until 2026-09-07. It was false when written rather than true and falsified, so this is a
correction and not one of this repository's dated records.** `sheetToBase` is declared in
`Oka/Geometry/RingedSpace/LocallyRingedSpace/InverseImageSheet.lean`, and `git grep -c` for the
token in `Oka/Geometry/RingedSpace/LocallyRingedSpace/InverseImage.lean` returns 0. **The
instrument that settles which module owns an equation lemma is the dump and not `git grep`**:
`scripts/DumpOkaDecls.lean` writes `module<TAB>name` read off `env.header.moduleData`, and
`grep -P "^Oka\.Geometry\.RingedSpace\.LocallyRingedSpace\.InverseImage\t" | grep "\.eq_"`
over its output returns seven rows here — the five this paragraph names, together with those two
generated by this section. The retired figure came from reading
a `git grep` list of names, which carries no declaring module and had drawn in a neighbouring
one. -/

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.inverseImageSheaf_hom_ext' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.inverseImageSheaf_hom_ext

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.inverseImage_hom_ext' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.inverseImage_hom_ext

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.compHom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.compHom

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.compHom_base' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.compHom_base

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.isIso_toInverseImage_compHom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.isIso_toInverseImage_compHom

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.inverseImageIso' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.inverseImageIso

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.inverseImageIso_hom_base' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.inverseImageIso_hom_base

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.inverseImageIso_inv_base_apply' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.inverseImageIso_inv_base_apply

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.inverseImageMap' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.inverseImageMap

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.inverseImageMap_base' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.inverseImageMap_base

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.inverseImageMap_comp' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.inverseImageMap_comp

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.inverseImageMapOfEq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.inverseImageMapOfEq

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.inverseImageMapOfEq_base' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.inverseImageMapOfEq_base

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.inverseImageMapOfEq_comp' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.inverseImageMapOfEq_comp
