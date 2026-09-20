/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka

/-!
# Axiom regression tests: Complex analytic spaces

Complex analytic spaces as objects, and the constructions that build one: local models and the
node; the residue field, the continuity and naturality of the value of a section, and the
rigidity of germs; open subspaces — in general and at the open that is everything — and the
non-vanishing locus; that being a complex analytic space is a local condition; **gluing** — the
`ℂ`-algebra structure of a glued space, a cover by abstract spaces, the analytic structure on
the gluing, the fields of
`CategoryTheory.GlueData.ofGlueData'`, and gluing a morphism; and the
**coproduct** — the disjoint union of a family, the trivial `n`-sheeted cover, the sheet
comparison, and the one-sheeted disjoint union; and that the spaces this development
**constructs** are **Hausdorff**, which is the one heading below naming a property of a space
rather than a construction of one; and the **fibre product** — the gluing of the ambient pullbacks
over a covering family, the limit cone it presents, the reduction of a general cospan to that
shape, and `CategoryTheory.Limits.HasPullbacks ComplexAnalytic.AnalyticSpace` itself, whose own
heading says why it is guarded here. **Guards about the category rather than about an object or a
morphism in it are `ComplexAnalytic.AnalyticSpace.hasCoproducts`, `…hasFiniteCoproducts` and
`…hasPullbacks`**, the first two under `### The disjoint union is the coproduct`, whose own
paragraph calls them *the two `Has…` instances*; so the last is the third of three and not the
only one, and a category-level guard in this file is not an exception the routing recipe had to
swallow. **Two of the headings below are about morphisms after all** — gluing one, and that a
morphism to `ℂ^n` is determined by the pullbacks of the coordinates — because each is a statement
about the space the construction produces; the *classes* of
morphisms are `OkaTest/Axioms/Morphisms.lean`'s.

**That is a description and not a list, and the headings below are the record**: each names the
statement its assertions defend, and the recipe beside `OkaTest/Axioms.lean`'s routing table
resolves them to modules. The stance is `OkaTest/Axioms/Sheaves.lean`'s and
`OkaTest/Axioms/LocalOkaRing.lean`'s, and it is taken here because this file is past the size at
which a list stays true: at `883b62f` it held 138 guards under nineteen headings over nineteen
modules.

**The sentence this replaces named local models, the node and the value of a section**, which at
`27c185a` was at most 19 of the 102 guards there and four of the sixteen headings there. At
`883b62f` gluing alone — **the five headings named above**, from the `ℂ`-algebra structure of a
glued space to gluing a morphism — was 51 of those 138 and **the four coproduct headings named
above** 32, and neither appeared in it. **Six of the nineteen modules are not
`Oka/AnalyticSpace/`'s** and contributed 29 guards there:
`Oka/CategoryTheory/GlueData.lean` ten, four modules of `Oka/Geometry/RingedSpace/` fifteen, and
`Oka/AlgebraicGeometry/GammaSpecAdjunction.lean` four — most of them under the gluing headings,
beside the analytic statements they serve. See `OkaTest/Axioms.lean` on why a mirror-tree module
such as the first has no row of its own.

**Every figure above is pinned to the commit it was measured at, and this file used to take that
decision the other way.** The paragraphs above carried undated counts and said in terms that the
list to recheck after adding a guard was every one of them; `OkaTest/Axioms.lean`'s rule that
prose about a section should name rather than count says instead that a numeral a reader has to
recheck should not be written, and the two cannot both be followed. **What settles it is that the
rechecking did not happen**, measured at `883b62f`, before this paragraph was rewritten:
*eighteen headings* was false in both sentences carrying it, falsified by `a6dcf31`, which
appended a nineteenth; *130 guards* was false in both places, falsified by `1a7cd87`; the
coproduct *24* was false, falsified by that same commit, which put two guards under the trivial
cover, and moved again by `a6dcf31`, which appended a fourth coproduct heading, so the partition
the number was of changed as well as its value; and the ledger below carried that same number
once more, as what the three coproduct headings *hold now*, where it is pinned to `4853cc2`
instead. **All four were already false when the sweep that reached this file fenced this block**
(`5d45345`), which left them standing on the ground that the conflict of rules had to be settled
before anything here was touched. The gluing *51*, the *29* outside `Oka/AnalyticSpace/` and the
module count are what happened to survive.

**The same numeral had done it once before, and that record is the sharper one.** When the warning
that stood here was written the coproduct read *19* and the sentence carrying it said the number
*"has simply not moved yet"*. The **very next commit to touch this file** falsified it —
`d58c85d`, four guards under the trivial cover — and it then stood wrong for **23 commits**,
because it was the one numeral nobody rechecked. A reader who wants today's arithmetic runs the
**two** recipes beside `OkaTest/Axioms.lean`'s routing table — the one that resolves a guard name
to its module, and the one that attributes a guard to the heading above it. **The counts in the
paragraphs above are what those two returned at the commit each is pinned to**, and the reason to
prefer a member a reader can check to a cardinal they have to recount is
`OkaTest/Axioms/Analytification.lean`'s tower section's.

**The ledger of what has moved, in two rounds, because the second round found the first one's
values already stale.** Counted as `#print axioms` **names**, which here equals the command count,
at every figure below.

At `4c91029` five numerals had gone false and were repaired to *112*, *51*, *29*, *ten* and
*fifteen*, from *108*, *48*, *27*, *nine* and *fourteen*; all five had been right at `f63cb3a`,
which wrote them, and four guards added and none removed since —
`AlgebraicGeometry.LocallyRingedSpace.GlueData.ext_of_toGlueData`,
`CategoryTheory.GlueData'.ext_of_heq`,
`ComplexAnalytic.AnalyticSpace.ofGlueDataCLinear_congr` and
`ComplexAnalytic.AnalyticSpace.nonvanishing_pullbackΓ` — accounted for every one of the five
deltas exactly, three of them under gluing headings and two outside `Oka/AnalyticSpace/`. **What
had made *48* uncheckable rather than merely stale is that the sentence listing the gluing
headings named four of them and the number counted five**, so a recount could not tell a wrong
number from a different partition; the list above is the five the number is of.

**Two of those five went stale again before `0ad0426` touched anything, and one of them was
never repaired at `4c91029` at all.** At `a4f3a81` the guard total is **122** and not *112*, and
the coproduct subtotal is **23** and not the *19* that has stood since `f63cb3a` — ten guards
arrived between `4c91029` and `a4f3a81`, four from lana-agents/oka#365 and six from
lana-agents/oka#380, and **only the four are under a coproduct heading**, which is why the
coproduct moved by exactly four and the gluing *51* did not move at all. The other six have a
heading of their own, and the last paragraph below is why every count of this file taken before
it charged them to the sheet comparison anyway. The *19* is the case this file's own warning
is about: it stood in the same clause as the *51*, was the same kind of number, and had simply not
moved yet when the clause was written.

**`0ad0426` added seven guards under one new heading and one new module**, so *112* → **129**,
seventeen headings → **eighteen** and eighteen modules → **nineteen**; the gluing *51*, the *29*
outside `Oka/AnalyticSpace/`, the *ten*, the *fifteen* and the *four* are all unmoved, because
`Oka/AnalyticSpace/Hausdorff.lean` is under `Oka/AnalyticSpace/` and none of its guards is under a
gluing or coproduct heading.

**Why every count above was wrong in the same place, and the one line that fixes it.** The
paragraph that stood here said six guards from `Oka/AnalyticSpace/OpenSubspace.lean` —
`ComplexAnalytic.AnalyticSpace.mono_ofRestrict`, `ComplexAnalytic.AnalyticSpace.liftTop`,
`ComplexAnalytic.AnalyticSpace.liftTop_ofRestrict`,
`ComplexAnalytic.AnalyticSpace.isIso_ofRestrict_of_eq_univ`,
`ComplexAnalytic.AnalyticSpace.isIso_liftTop` and
`ComplexAnalytic.AnalyticSpace.liftTop_comp_restrictHom_top` — sat under
`### The sheet comparison is ℂ-linear`, which is about none of them, and had to be moved.
**They never sat there.** `3177e67` gave them a heading of its own,
`### The open subspace at an open that is everything`, and that section's own prose argues for
the placement in terms. What `3177e67` did not do is write the heading in the `/-! ### … -/`
form the rule beside `OkaTest/Axioms.lean`'s routing table asks for: it opened the doc comment
on one line and put the `###` on the next. **Every count this file has ever been given matches a
header by its opening delimiter and `###` on one line**, so all of them were blind to the
eighteenth heading and charged its six guards to the seventeenth. The repair is the one line that
pulls that `###` up onto the delimiter, and it moves no guard.

**This paragraph located that anchor in a per-heading `awk` in the recipe beside that table, and
there was no such `awk`.** That recipe resolves a guard *name* to its module and reads no heading
at all, so every count of this file had in fact been taken by an instrument written out on a
thread and kept nowhere — which is why each of them repeated the same blindness. There is a
per-heading recipe beside the table now; it matches a heading in either form, and
`.orchestra/validation.sh` rejects the second outright.

**Two numerals were wrong from `3177e67` for that one reason, and neither is the kind an author
is told to recheck.** The heading count, because a heading the instrument cannot see is not one
the author is warned they added: *sixteen* at `a4f3a81` where the file held seventeen, hence the
ledger row above reading *seventeen* where it should read **eighteen**. And the coproduct, whose
three headings held `8 + 11 + 4 = 23` at that repair, and `9 + 11 + 4 = 24` at `4853cc2` where
that clause was written — and which was read as *29*. Both were repaired there; the guard total
did not move, which is the check that no guard was touched, and it stood at *129* until the
disjoint union's `¬ IsIso` was added.

**So this is not the defect lana-agents/oka#358 repaired at `4c91029`, though it was filed as a
recurrence of it.** That one was a guard appended past a heading. `3177e67` appended a heading
too — it did the thing the rule asks for — and the counting still went wrong, one level down: **an
instrument blind to a heading reports a wrong partition for every section after it, and reports
it silently.** No checker in `scripts/` attributes a guard to a heading, so there is nothing to
harden there; the operative sentence is already in `OkaTest/Axioms.lean` and it already says
`/-! ### … -/`, on one line. What this file lacked was a reason to believe the form mattered.
`scripts/check_module_docstrings.py`'s own docstring has carried that reason since 2026-08-23: a
one-line grep for an opening delimiter carrying `##` returns 58 where its own predicate returns
59, and it names `Oka/LocalOkaRing.lean`, *"whose header is written across two lines"*, as the
file the grep cannot see.
The same has been true of this file since `3177e67`, across the one recount of it taken
since — `0ad0426`'s, which is where the *seventeen* above came from — and nobody joined the two
up.

See `OkaTest/Axioms.lean` for what these assertions are for and how to update one.
-/

/-! ### Local models, and the node as a complex analytic space -/

/--
info: 'ComplexAnalytic.AnalyticSpace.ofCutOut' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.ofCutOut

/--
info: 'ComplexAnalytic.isLocalModel_zeroLocus' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isLocalModel_zeroLocus

/--
info: 'ComplexAnalytic.isCLinearHom_restrictTopIso_inv' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isCLinearHom_restrictTopIso_inv

/--
info: 'ComplexAnalytic.isCLinearHom_restrictTopIso_inv_constants' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isCLinearHom_restrictTopIso_inv_constants

/--
info: 'ComplexAnalytic.AnalyticSpace.zeroLocus' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.zeroLocus

/--
info: 'ComplexAnalytic.AnalyticSpace.isCoherentStructureSheaf_zeroLocus' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.isCoherentStructureSheaf_zeroLocus

/--
info: 'ComplexAnalytic.mem_zeroLocus_nodeSection_iff' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.mem_zeroLocus_nodeSection_iff

/--
info: 'ComplexAnalytic.isCoherentStructureSheaf_node' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isCoherentStructureSheaf_node

/-! ### The residue field of a complex analytic space is `ℂ` -/

/--
info: 'ComplexAnalytic.AnalyticSpace.existsUnique_sub_stalkAlgMap_mem_maximalIdeal' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.existsUnique_sub_stalkAlgMap_mem_maximalIdeal

/--
info: 'ComplexAnalytic.AnalyticSpace.evalStalk_eq_zero_iff' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.evalStalk_eq_zero_iff

/--
info: 'ComplexAnalytic.eval_ofCutOut' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.eval_ofCutOut

/--
info: 'ComplexAnalytic.eval_nodeCoord' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.eval_nodeCoord

/--
info: 'ComplexAnalytic.nodeCoord_mul' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.nodeCoord_mul

/--
info: 'ComplexAnalytic.nodeCoord_ne_zero' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.nodeCoord_ne_zero

/-! ### Continuity of the value of a section -/

/--
info: 'ComplexAnalytic.evalStalk_chart' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.evalStalk_chart

/--
info: 'ComplexAnalytic.AnalyticSpace.continuous_eval' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.continuous_eval

/--
info: 'ComplexAnalytic.AnalyticSpace.continuous_eval_top' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.continuous_eval_top

/-! ### Naturality of evaluation, and rigidity of germs on `ℂ^ι` -/

/--
info: 'ComplexAnalytic.AnalyticSpace.evalStalk_stalkMap' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.evalStalk_stalkMap

/--
info: 'ComplexAnalytic.AnalyticSpace.eval_c_app' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.eval_c_app

/--
info: 'ComplexAnalytic.okaStalk_ringHom_ext' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.okaStalk_ringHom_ext

/-! ### A morphism to `ℂ^n` is determined by the pullbacks of the coordinates

`AlgebraicGeometry.LocallyRingedSpace.hom_stalk_ext` is general locally-ringed-space material
with no row of its own in the topic table of `OkaTest/Axioms.lean`; it sits here because the
only thing that uses it is the rigidity statement below. If a reviewer prefers it in
`OkaTest/Axioms/Sheaves.lean` that is a two-line change.

**The clause *the only thing that uses it* has stopped being true, and the sentence is left
standing rather than repaired because `OkaTest/Axioms.lean` quotes it verbatim** — its routing
paragraph cites this heading as one of the two precedents for guarding a mirror-tree declaration
beside its consumer, and editing a quoted sentence silently breaks the quotation at the other
end. What falsifies it is `AlgebraicGeometry.LocallyRingedSpace.hom_ext_of_comp_eq`, declared in
the same mirror-tree file and proved from
`AlgebraicGeometry.LocallyRingedSpace.hom_stalk_ext`; it is guarded in
`OkaTest/Axioms/Morphisms.lean`, beside the statements about covers that are its only consumers,
which is this same practice rather than a departure from it. **The placement of the guard below
is unchanged** and its reason now reads *the only thing in this file's subject that uses it*. -/

/--
info: 'ComplexAnalytic.eval_complexAffineSpace' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.eval_complexAffineSpace

/--
info: 'ComplexAnalytic.eval_restrict_complexAffineSpace' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.eval_restrict_complexAffineSpace

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.hom_stalk_ext' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.hom_stalk_ext

/--
info: 'ComplexAnalytic.AnalyticSpace.hom_ext_complexAffineSpace' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.hom_ext_complexAffineSpace

/--
info: 'ComplexAnalytic.nodeCoord_ne' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.nodeCoord_ne

/-! ### An open subspace of a complex analytic space is a complex analytic space -/

/--
info: 'ComplexAnalytic.exists_local_model_restrict' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.exists_local_model_restrict

/--
info: 'ComplexAnalytic.AnalyticSpace.restrict' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.restrict

/--
info: 'ComplexAnalytic.AnalyticSpace.ofRestrict' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.ofRestrict

/-! ### Being a complex analytic space is a local condition

`Oka/AnalyticSpace/Local.lean`. -/

/--
info: 'ComplexAnalytic.HasLocalModels' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.HasLocalModels

/--
info: 'ComplexAnalytic.AnalyticSpace.hasLocalModels' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.hasLocalModels

/--
info: 'ComplexAnalytic.AnalyticSpace.ofHasLocalModels' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.ofHasLocalModels

/--
info: 'ComplexAnalytic.HasLocalModels.restrict' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.HasLocalModels.restrict

/--
info: 'ComplexAnalytic.HasLocalModels.of_iSup_eq_top' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.HasLocalModels.of_iSup_eq_top

/--
info: 'ComplexAnalytic.hasLocalModels_iff_iSup_eq_top' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.hasLocalModels_iff_iSup_eq_top

/--
info: 'ComplexAnalytic.AnalyticSpace.ofOpens' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.ofOpens

/-! ### The `ℂ`-algebra structure of a glued analytic space

`Oka/AnalyticSpace/Local.lean`. -/

/--
info: 'ComplexAnalytic.AnalyticSpace.ofOpensCompatible' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.ofOpensCompatible

/--
info: 'ComplexAnalytic.AnalyticSpace.map_ofOpensCompatible_algebraMap' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.map_ofOpensCompatible_algebraMap

/-! ### The non-vanishing locus of a section, and mapping into an open subspace

`Oka/AnalyticSpace/Nonvanishing.lean`. -/

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.liftRestrict' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.liftRestrict

/--
info: 'AlgebraicGeometry.RingedSpace.isUnit_res_of_le_basicOpen' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.RingedSpace.isUnit_res_of_le_basicOpen

/--
info: 'ComplexAnalytic.AnalyticSpace.liftOpen' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.liftOpen

/--
info: 'ComplexAnalytic.AnalyticSpace.liftOpen_fac' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.liftOpen_fac

/--
info: 'ComplexAnalytic.AnalyticSpace.hom_ext_restrict' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.hom_ext_restrict

/--
info: 'ComplexAnalytic.AnalyticSpace.mem_nonvanishing_iff' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.mem_nonvanishing_iff

/--
info: 'ComplexAnalytic.AnalyticSpace.nonvanishing_pullbackΓ' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.nonvanishing_pullbackΓ

/--
info: 'ComplexAnalytic.AnalyticSpace.isUnit_resΓ_of_le_nonvanishing' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.isUnit_resΓ_of_le_nonvanishing

/-! ### Gluing an analytic space out of a cover by abstract spaces

`Oka/AnalyticSpace/Glue.lean`. -/

/--
info: 'ComplexAnalytic.IsCLinearHom.eq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.IsCLinearHom.eq

/--
info: 'ComplexAnalytic.isCLinearHom_comapAlgMap' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isCLinearHom_comapAlgMap

/--
info: 'ComplexAnalytic.isCLinearHom_ofRestrict' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isCLinearHom_ofRestrict

/--
info: 'ComplexAnalytic.IsCLinearHom.of_openCover' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.IsCLinearHom.of_openCover

/--
info: 'ComplexAnalytic.HasLocalModels.of_iso' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.HasLocalModels.of_iso

/--
info: 'ComplexAnalytic.AnalyticSpace.ofOpenCover' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.ofOpenCover

/--
info: 'ComplexAnalytic.AnalyticSpace.comapAlgMap_ofOpenCover_algebraMap' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.comapAlgMap_ofOpenCover_algebraMap

/--
info: 'ComplexAnalytic.AnalyticSpace.ofGlueData' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.ofGlueData

/--
info: 'ComplexAnalytic.AnalyticSpace.algebraMap_ofOpenCover_comapAlgMap' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.algebraMap_ofOpenCover_comapAlgMap

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.liftRestrict_uniq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.liftRestrict_uniq

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.hom_ext_restrict' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.hom_ext_restrict

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.isOpenImmersion_ofRestrict' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.isOpenImmersion_ofRestrict

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.restrictInfIsoPullback' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.restrictInfIsoPullback

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.isOpenImmersion_f'' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.isOpenImmersion_f'

/-! ### The analytic structure on a gluing -/

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.toSpecOfAlgMap' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.toSpecOfAlgMap

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.comp_toSpecOfAlgMap' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.comp_toSpecOfAlgMap

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.toSpecOfAlgMap_injective' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.toSpecOfAlgMap_injective

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.exists_toSpecOfAlgMap_eq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.exists_toSpecOfAlgMap_eq

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.GlueData.vIsoPullback' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.GlueData.vIsoPullback

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.GlueData.isCompatible_restrictAlgMap' depends on
  axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.GlueData.isCompatible_restrictAlgMap

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.GlueData.ext_of_toGlueData' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.GlueData.ext_of_toGlueData

/--
info: 'ComplexAnalytic.GlueDataCLinear' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.GlueDataCLinear

/--
info: 'ComplexAnalytic.glueDataCLinear_comapAlgMap' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.glueDataCLinear_comapAlgMap

/--
info: 'ComplexAnalytic.glueDataCLinear_of_isCLinearHom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.glueDataCLinear_of_isCLinearHom

/--
info: 'ComplexAnalytic.isCompatible_of_glueDataCLinear' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isCompatible_of_glueDataCLinear

/--
info: 'ComplexAnalytic.AnalyticSpace.ofGlueDataCLinear' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.ofGlueDataCLinear

/--
info: 'ComplexAnalytic.AnalyticSpace.comapAlgMap_ofGlueDataCLinear_algebraMap' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.comapAlgMap_ofGlueDataCLinear_algebraMap

/--
info: 'ComplexAnalytic.AnalyticSpace.algebraMap_ofGlueDataCLinear_comapAlgMap' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.algebraMap_ofGlueDataCLinear_comapAlgMap

/--
info: 'ComplexAnalytic.AnalyticSpace.ofGlueDataCLinear_congr' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.ofGlueDataCLinear_congr

/-! ### The fields of `CategoryTheory.GlueData.ofGlueData'` -/

/--
info: 'CategoryTheory.GlueData.ofGlueData'_f_self' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.GlueData.ofGlueData'_f_self

/--
info: 'CategoryTheory.GlueData.ofGlueData'_f_of_ne' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.GlueData.ofGlueData'_f_of_ne

/--
info: 'CategoryTheory.GlueData.ofGlueData'_t_self' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.GlueData.ofGlueData'_t_self

/--
info: 'CategoryTheory.GlueData.ofGlueData'_t_of_ne' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.GlueData.ofGlueData'_t_of_ne

/--
info: 'CategoryTheory.GlueData'.f'_self' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.GlueData'.f'_self

/--
info: 'CategoryTheory.GlueData'.f'_of_ne' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.GlueData'.f'_of_ne

/--
info: 'CategoryTheory.GlueData.ofGlueData'_t_comp_f_of_ne' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.GlueData.ofGlueData'_t_comp_f_of_ne

/--
info: 'CategoryTheory.GlueData.ofGlueData'_comm' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.GlueData.ofGlueData'_comm

/--
info: 'CategoryTheory.GlueData.comm_of_ofGlueData'_comm' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.GlueData.comm_of_ofGlueData'_comm

/--
info: 'CategoryTheory.GlueData'.ext_of_heq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.GlueData'.ext_of_heq

/--
info: 'ComplexAnalytic.AnalyticSpace.comapAlgMap_toLRSHom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.comapAlgMap_toLRSHom

/-! ### Gluing a morphism

`ComplexAnalytic.AnalyticSpace.glueMorphisms` glues out of an **open cover** and asks for
agreement over a categorical pullback.
`AlgebraicGeometry.LocallyRingedSpace.GlueData.glueMorphisms` glues out of a **gluing** and asks
for agreement over the glue datum's own overlaps, which is the only form a caller who built the
datum can state; **it is not a special case of `ComplexAnalytic.AnalyticSpace.glueMorphisms`**,
and
`…GlueData.pullback_condition_of_comm` is the transport between them, through
`…GlueData.vIsoPullback` under the heading above.
`ComplexAnalytic.AnalyticSpace.glueMorphismsOfGlueData` is those two composed rather than an idea
of its own: it glues a morphism of **analytic spaces** out of a gluing, taking its pullback
hypothesis from `…GlueData.pullback_condition_of_comm` and its `ℂ`-linearity
hypothesis over the structures the members were given, which
`ComplexAnalytic.AnalyticSpace.comapAlgMap_ofGlueDataCLinear_algebraMap` identifies with the one
the gluing induces. **That composition was already being made, at one datum**:
`ComplexAnalytic.coverGlueMorphisms` is an instance of it by
`ComplexAnalytic.coverGlueMorphisms_eq_glueMorphismsOfGlueData`, and both are guarded in
`OkaTest/Axioms/Analytification.lean` under that file's cover heading rather than here.

**`ComplexAnalytic.AnalyticSpace.glueMorphismsOfOpens` is the third shape and is not a case of
either.** It glues out of a covering family of **opens of the source**, where the overlap is
`U i ⊓ U j` and the compatibility is an equation between morphisms out of the open subspace on it.
`ComplexAnalytic.AnalyticSpace.pullback_compat_of_restrictLE` is the transport from that form to
the categorical one, through
`AlgebraicGeometry.LocallyRingedSpace.restrictInfIsoPullback` under the heading above, and it is
the analytic reading of the compatibility step inside
`AlgebraicGeometry.LocallyRingedSpace.existsUnique_glueMorphisms_of_opens`, which is guarded in
`OkaTest/Axioms/Sheaves.lean`. `ComplexAnalytic.AnalyticSpace.ιCLinear` is guarded here rather
than under a heading of its own because it is the same file and the same subject read the other
way round: a morphism **into** a gluing rather than out of one.

**This description opened *Two levels, and the second is not a special case of the first* until
2026-09-07**, when the analytic gluing out of a datum was added and the opening sentence became a
count of what the heading held. It was exact when written, and the clause it made survives on
`AlgebraicGeometry.LocallyRingedSpace.GlueData.glueMorphisms`, which is the declaration it was
about.
-/

/--
info: 'ComplexAnalytic.AnalyticSpace.isCLinearHom_glueMorphisms' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.isCLinearHom_glueMorphisms

/--
info: 'ComplexAnalytic.AnalyticSpace.glueMorphisms' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.glueMorphisms

/--
info: 'ComplexAnalytic.AnalyticSpace.toLRSHom_glueMorphisms' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.toLRSHom_glueMorphisms

/--
info: 'ComplexAnalytic.AnalyticSpace.ι_glueMorphisms' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.ι_glueMorphisms

/--
info: 'ComplexAnalytic.AnalyticSpace.isCLinearHom_map_comp' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.isCLinearHom_map_comp

/--
info: 'ComplexAnalytic.AnalyticSpace.glueMorphisms_map_comp' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.glueMorphisms_map_comp

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.GlueData.pullback_condition_of_comm' depends on
  axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.GlueData.pullback_condition_of_comm

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.GlueData.glueMorphisms' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.GlueData.glueMorphisms

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.GlueData.ι_glueMorphisms' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.GlueData.ι_glueMorphisms

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.GlueData.hom_ext' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.GlueData.hom_ext

/--
info: 'ComplexAnalytic.AnalyticSpace.glueMorphismsOfGlueData' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.glueMorphismsOfGlueData

/--
info: 'ComplexAnalytic.AnalyticSpace.ι_glueMorphismsOfGlueData' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.ι_glueMorphismsOfGlueData

/--
info: 'ComplexAnalytic.AnalyticSpace.pullback_compat_of_restrictLE' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.pullback_compat_of_restrictLE

/--
info: 'ComplexAnalytic.AnalyticSpace.glueMorphismsOfOpens' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.glueMorphismsOfOpens

/--
info: 'ComplexAnalytic.AnalyticSpace.ofRestrict_comp_glueMorphismsOfOpens' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.ofRestrict_comp_glueMorphismsOfOpens

/--
info: 'ComplexAnalytic.AnalyticSpace.hom_ext_of_opens' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.hom_ext_of_opens

/--
info: 'ComplexAnalytic.AnalyticSpace.existsUnique_glueMorphismsOfOpens' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.existsUnique_glueMorphismsOfOpens

/--
info: 'ComplexAnalytic.AnalyticSpace.ιCLinear' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.ιCLinear

/-! ### The disjoint union of a family of analytic spaces

`Oka/AnalyticSpace/Sigma.lean`. The object, its inclusions, the descent map, the non-vacuity
statements — the disjoint union is empty at an empty index type and at empty members, and an
inclusion is not surjective — and that an inclusion is not an isomorphism.

**And, since 2026-09-20, that its underlying space is the topological disjoint union of the
members' underlying spaces**: `ComplexAnalytic.AnalyticSpace.sigmaHomeoSigma` with the two lemmas
beside it, `…sigmaHomeoSigma_symm_apply` and `…sigmaHomeoSigma_preimage_range`. **Those three
are this section's only assertions over a statement about the topology**; every other one here is
about the carrier, the `ℂ`-algebra structure or the universal property. **The first of them was
guarded in `OkaTest/Axioms/Morphisms.lean` until that date**, beside the covers that consume it,
which is a routing this file's own rule does not support: the statement is about
`ComplexAnalytic.AnalyticSpace.sigma` at an arbitrary family of analytic spaces and mentions no
cover. taxis #2094 moved the declaration and its guard together and wrote the other two. -/

/--
info: 'ComplexAnalytic.AnalyticSpace.sigma' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.sigma

/--
info: 'ComplexAnalytic.AnalyticSpace.comapAlgMap_sigma' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.comapAlgMap_sigma

/--
info: 'ComplexAnalytic.AnalyticSpace.sigmaι' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.sigmaι

/--
info: 'ComplexAnalytic.AnalyticSpace.sigmaHomeoSigma' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.sigmaHomeoSigma

/--
info: 'ComplexAnalytic.AnalyticSpace.sigmaHomeoSigma_symm_apply' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.sigmaHomeoSigma_symm_apply

/--
info: 'ComplexAnalytic.AnalyticSpace.sigmaHomeoSigma_preimage_range' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.sigmaHomeoSigma_preimage_range

/--
info: 'ComplexAnalytic.isCLinearHom_sigmaDesc' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isCLinearHom_sigmaDesc

/--
info: 'ComplexAnalytic.AnalyticSpace.sigmaDesc' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.sigmaDesc

/--
info: 'ComplexAnalytic.AnalyticSpace.isEmpty_sigma' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.isEmpty_sigma

/--
info: 'ComplexAnalytic.AnalyticSpace.isEmpty_sigma_of_members' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.isEmpty_sigma_of_members

/--
info: 'ComplexAnalytic.AnalyticSpace.not_surjective_sigmaι_base' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.not_surjective_sigmaι_base

/--
info: 'ComplexAnalytic.AnalyticSpace.not_isIso_sigmaι' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.not_isIso_sigmaι

/--
info: 'ComplexAnalytic.AnalyticSpace.sigmaι_sigmaDesc' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.sigmaι_sigmaDesc

/-! ### The trivial `n`-sheeted cover, the descent map, and the inclusions

`Oka/AnalyticSpace/SigmaFiniteEtale.lean`. That finiteness and being a local isomorphism pass
from the members of a disjoint union to a descent map out of it; the trivial `ι`-sheeted cover
`∐_{i : ι} X ⟶ X` with its count of sheets; and the same two properties of the **inclusion** of a
member, which hold for every family and are the other direction — together with what that
inclusion's image being **clopen** gives: a disjoint union with two distinct inhabited members is
not preconnected. The header names the subjects rather than counting the guards, so appending one
does not falsify it. -/

/--
info: 'ComplexAnalytic.AnalyticSpace.toLRSHom_sigmaDesc' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.toLRSHom_sigmaDesc

/--
info: 'ComplexAnalytic.AnalyticSpace.isFinite_sigmaDesc' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.isFinite_sigmaDesc

/--
info: 'ComplexAnalytic.AnalyticSpace.isLocalIso_sigmaDesc' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.isLocalIso_sigmaDesc

/--
info: 'ComplexAnalytic.AnalyticSpace.isFiniteEtale_sigmaDesc' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.isFiniteEtale_sigmaDesc

/--
info: 'ComplexAnalytic.AnalyticSpace.sigmaFold' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.sigmaFold

/--
info: 'ComplexAnalytic.AnalyticSpace.isFiniteEtale_sigmaFold' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.isFiniteEtale_sigmaFold

/--
info: 'ComplexAnalytic.AnalyticSpace.card_fiber_sigmaFold' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.card_fiber_sigmaFold

/--
info: 'ComplexAnalytic.AnalyticSpace.isClosed_range_sigmaι_base' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.isClosed_range_sigmaι_base

/--
info: 'ComplexAnalytic.AnalyticSpace.isFinite_sigmaι' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.isFinite_sigmaι

/--
info: 'ComplexAnalytic.AnalyticSpace.isLocalIso_sigmaι' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.isLocalIso_sigmaι

/--
info: 'ComplexAnalytic.AnalyticSpace.isFiniteEtale_sigmaι' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.isFiniteEtale_sigmaι

/--
info: 'ComplexAnalytic.AnalyticSpace.isClopen_range_sigmaι_base' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.isClopen_range_sigmaι_base

/--
info: 'ComplexAnalytic.AnalyticSpace.sigmaιOpens' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.sigmaιOpens

/--
info: 'ComplexAnalytic.AnalyticSpace.coe_sigmaιOpens' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.coe_sigmaιOpens

/--
info: 'ComplexAnalytic.AnalyticSpace.isClosed_sigmaιOpens' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.isClosed_sigmaιOpens

/--
info: 'ComplexAnalytic.AnalyticSpace.sigmaιOpens_ne_bot' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.sigmaιOpens_ne_bot

/--
info: 'ComplexAnalytic.AnalyticSpace.sigmaιOpens_ne_top' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.sigmaιOpens_ne_top

/--
info: 'ComplexAnalytic.AnalyticSpace.not_preconnectedSpace_sigma' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.not_preconnectedSpace_sigma


/-! ### The sheet comparison is `ℂ`-linear

`Oka/AnalyticSpace/InverseImageSheet.lean`. The `ℂ`-algebra half of
`AlgebraicGeometry.LocallyRingedSpace.sheetIso`, whose locally-ringed-space half is guarded in
`OkaTest/Axioms/Sheaves.lean`: the two structures the comparison relates, and that it and its
inverse respect them. -/

/--
info: 'ComplexAnalytic.comapAlgMap_sheetToBase' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.comapAlgMap_sheetToBase

/--
info: 'ComplexAnalytic.isCLinearHom_sheetHom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isCLinearHom_sheetHom

/--
info: 'ComplexAnalytic.isCLinearHom_sheetIso_inv' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isCLinearHom_sheetIso_inv

/--
info: 'ComplexAnalytic.comapAlgMap_sheetHom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.comapAlgMap_sheetHom

/-! ### The open subspace at an open that is everything

`ComplexAnalytic.AnalyticSpace.ofRestrict` is guarded above; guarded here are
`ComplexAnalytic.AnalyticSpace.liftTop`, its section at an open that is everything, and the
statements that make the two invertible — that the inclusion is a monomorphism, that the section
is a section of it, and the two `IsIso` statements that follow — together with the factorisation
of a morphism through its own restriction over `⊤` that they exist for. **Named rather than
counted**, and every declaration this branch adds under `Oka/AnalyticSpace/OpenSubspace.lean` is
guarded here except `ComplexAnalytic.AnalyticSpace.isFinite_of_restrictHom_top`, which is a class
of morphisms and is in `OkaTest/Axioms/Morphisms.lean` with the finite étale one. **Appended as
its own section rather than folded into the open-subspace heading above**, for the reason the
sections above give: a section moved is a conflict for somebody else.

**`ComplexAnalytic.AnalyticSpace.liftTop` is a `def` and is guarded anyway, and an earlier head of
this branch left it out** — which made the sentence above false, since that sentence quantifies
over declarations and its own pull-request body counts this one among them. The rule it is guarded
under is the one `Oka/Analytification/RefineDatumToBase.lean`'s guards state in terms for
`ComplexAnalytic.refineDatumPresHom`: a definition advertised under a `## Main definitions`
heading is guarded even when it has no content of its own, and
`Oka/AnalyticSpace/OpenSubspace.lean` advertises this one. **That is not a claim about the whole
file**: `ComplexAnalytic.AnalyticSpace.resΓ` is advertised there too and is guarded nowhere, which
predates this branch and is not its to close.

`ComplexAnalytic.AnalyticSpace.mono_ofRestrict` is the one with a life outside this line — a
cancellation property of the inclusion at *every* open, which before this had to be routed through
`AlgebraicGeometry.LocallyRingedSpace` by hand. The consumers that asked are
`ComplexAnalytic.AnalyticSpace.isFinite_of_restrictHom_top` and
`ComplexAnalytic.AnalyticSpace.isFiniteEtale_of_restrictHom_top`, both guarded in
`OkaTest/Axioms/Morphisms.lean` with the classes of morphisms rather than here.
-/

/--
info: 'ComplexAnalytic.AnalyticSpace.mono_ofRestrict' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.mono_ofRestrict

/--
info: 'ComplexAnalytic.AnalyticSpace.liftTop' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.liftTop

/--
info: 'ComplexAnalytic.AnalyticSpace.liftTop_ofRestrict' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.liftTop_ofRestrict

/--
info: 'ComplexAnalytic.AnalyticSpace.isIso_ofRestrict_of_eq_univ' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.isIso_ofRestrict_of_eq_univ

/--
info: 'ComplexAnalytic.AnalyticSpace.isIso_liftTop' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.isIso_liftTop

/--
info: 'ComplexAnalytic.AnalyticSpace.liftTop_comp_restrictHom_top' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.liftTop_comp_restrictHom_top

/-! ### The analytic spaces this development constructs are Hausdorff

`Oka/AnalyticSpace/Hausdorff.lean`, the whole of it, appended as its own heading rather than under
one above: no heading above it names a separation property. **The clause that stood here said a
guard appended past the end of the file would have landed under the sheet comparison, and that
this is what had happened to the six guards below.** It had not; they have a heading of their own
and always did. See the last paragraph of the module docstring for what actually went wrong and
why this file's own counts could not see it.

**Every guard below is one `inferInstanceAs`**, so a guard here is a weak check by design —
what it defends is that no route to `T2Space` of a construction ever acquires an axiom, which is
exactly the failure a `sorry` in a subtype instance would produce.
`ComplexAnalytic.t2Space_analytification` is not here: it is `Oka/Analytification/Hausdorff.lean`'s
and is guarded in `OkaTest/Axioms/Analytification.lean` with the covering-map corollaries it exists
for. **That sentence called it *"the seventh"*, which the two sentences before it falsify** — the
whole of `Oka/AnalyticSpace/Hausdorff.lean` is guarded here and that instance is not in it, so the
ordinal counted a set it does not belong to; it is dropped rather than incremented, since no
ordinal was doing any work in it. It is a leftover from a six-instance draft.
-/

/--
info: 'ComplexAnalytic.t2Space_complexSpace' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.t2Space_complexSpace

/--
info: 'ComplexAnalytic.t2Space_restrict_complexAffineSpace' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.t2Space_restrict_complexAffineSpace

/--
info: 'ComplexAnalytic.t2Space_zeroLocusSubspace' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.t2Space_zeroLocusSubspace

/--
info: 'ComplexAnalytic.t2Space_restrict' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.t2Space_restrict

/--
info: 'ComplexAnalytic.t2Space_complexAffineSpace' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.t2Space_complexAffineSpace

/--
info: 'ComplexAnalytic.t2Space_zeroLocus' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.t2Space_zeroLocus

/--
info: 'ComplexAnalytic.t2Space_node' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.t2Space_node

/-! ### The one-sheeted disjoint union is the space itself

`Oka/AnalyticSpace/Sigma.lean`'s uniqueness half of the universal property and the isomorphism it
buys at a subsingleton index type, together with `Oka/AnalyticSpace/SigmaFiniteEtale.lean`'s
reading of that at the fold map — the statement, its packaging as an isomorphism, the `simp` lemma
that lets the general round trip fire through a `def`, and the projection of the packaging.
Appended as its own section rather than merged into the disjoint-union sections above: moving or
reordering a section of this file is a conflict for every branch that has appended to it.

**What the guards below are a check of is one universal property.**
`ComplexAnalytic.AnalyticSpace.hom_ext_sigma` is
`CategoryTheory.Limits.Sigma.hom_ext` carried across
`ComplexAnalytic.AnalyticSpace.forgetToLocallyRingedSpace`, and everything else here is that
lemma with `ComplexAnalytic.AnalyticSpace.sigmaι_sigmaDesc` and two-out-of-three for isomorphisms.
No structure sheaf is read anywhere in the section, which is the point of it:
`Oka/AnalyticSpace/SigmaFiniteEtale.lean` had recorded the fold map's case as absent and priced it
as a statement about the structure sheaves.

**`Classical.choice` is in every guard below and is not a surprise**: the disjoint union is built
by `ComplexAnalytic.AnalyticSpace.ofOpenCover` out of a gluing, and every statement here mentions
`ComplexAnalytic.AnalyticSpace.sigma`.

**Named and not located.** No sentence here says which section precedes or follows it.
-/

/--
info: 'ComplexAnalytic.AnalyticSpace.hom_ext_sigma' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.hom_ext_sigma

/--
info: 'ComplexAnalytic.AnalyticSpace.isIso_sigmaι' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.isIso_sigmaι

/--
info: 'ComplexAnalytic.AnalyticSpace.sigmaι_sigmaFold' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.sigmaι_sigmaFold

/--
info: 'ComplexAnalytic.AnalyticSpace.isIso_sigmaFold' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.isIso_sigmaFold

/--
info: 'ComplexAnalytic.AnalyticSpace.sigmaFoldIso' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.sigmaFoldIso

/--
info: 'ComplexAnalytic.AnalyticSpace.sigmaFoldIso_hom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.sigmaFoldIso_hom

/-! ### The disjoint union is the coproduct

`Oka/AnalyticSpace/Sigma.lean`: the inclusions read as a cofan, the colimit proof that bundles the
two halves of the universal property already guarded above, and the two `Has…` instances that
follow from it. Appended as its own section rather than merged into another, for the reason the
sections of this file give for that: moving or reordering a section is a conflict for every branch
that has appended to it.

**The two `Has…` instances are guarded although neither has a proof of its own.**
`ComplexAnalytic.AnalyticSpace.hasCoproducts` is a Mathlib converter at the colimit below and
`ComplexAnalytic.AnalyticSpace.hasFiniteCoproducts` is a second converter at the first, so a
reader might expect the axioms of the colimit to settle both. They are guarded because a guard of
a corollary does not guard what it is a corollary of and the converse fails the same way, and
because an instance is consumed by instance search rather than by name, which is the harder thing
to notice going wrong.

**`Classical.choice` is in every guard below and is not a surprise**, for the reason the
disjoint-union sections of this file already give: the object is built by
`ComplexAnalytic.AnalyticSpace.ofOpenCover` out of a gluing, and every statement here mentions
`ComplexAnalytic.AnalyticSpace.sigma`.

**Named by file rather than counted**, as the sections above say and for the reason they give.

**Named and not located.** No sentence here says which section precedes or follows it.
-/

/--
info: 'ComplexAnalytic.AnalyticSpace.cofanSigma' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.cofanSigma

/--
info: 'ComplexAnalytic.AnalyticSpace.isColimitCofanSigma' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.isColimitCofanSigma

/--
info: 'ComplexAnalytic.AnalyticSpace.hasCoproducts' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.hasCoproducts

/--
info: 'ComplexAnalytic.AnalyticSpace.hasFiniteCoproducts' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.hasFiniteCoproducts

/-! ### The open subspace on a chart is the local model that chart presents

`Oka/AnalyticSpace/Basic.lean` and `Oka/AnalyticSpace/OpenSubspace.lean`: that two analytic
spaces with the same underlying locally ringed space and the same `ℂ`-algebra structure are
equal, and the two statements that consequence was written for — that an open subspace carrying a
chart on the whole of itself **is** the `ComplexAnalytic.AnalyticSpace.ofCutOut` that chart
presents, and that every point has such a neighbourhood. Appended as its own section rather than
merged into another, because moving or reordering a section is a conflict for every branch that
has appended to it.

**Two modules under one heading, and the routing table sends both here.**
`OkaTest/Axioms.lean`'s row *analytic spaces, local models, the node* is where a module is sent by
what declares it, and `ComplexAnalytic.AnalyticSpace.ext'` is declared in
`Oka/AnalyticSpace/Basic.lean` while the other two are declared in
`Oka/AnalyticSpace/OpenSubspace.lean`. They are under one heading because the first exists only
for the second, and the spelling that shows it is not the spelling the proof uses. **Every figure
in this paragraph is at the commit that adds this section.** `git grep "AnalyticSpace\.ext'" --
Oka/ OkaTest/` returns 8 lines in 3 files, of which **exactly one is a use site**: the proof of
`ComplexAnalytic.restrict_eq_ofCutOut` in `Oka/AnalyticSpace/OpenSubspace.lean`, which does not
spell the name in full. The other 7 are 3 prose citations under `Oka/` — 2 in
`Oka/AnalyticSpace/Basic.lean` and 1 in `Oka/AnalyticSpace/OpenSubspace.lean` — and 4 lines of
this section: 2 in its prose, and 2 in its guard on that name, the `#print axioms` command and
its expected output. Grepping the fully-qualified name instead returns 6 of those 8 and **not**
the use site, because the proof is not among them. **The bare `git grep "ext'" -- Oka/ OkaTest/`
is the wrong instrument for this question, and its own output is why.** It returns 27 lines in 11
files: the 8 above; the line that *declares* the name, which writes it bare inside its namespace
as `theorem ext'`; 4 lines of code using a different name that really does end in a prime,
`SetLike.ext'` and `AlgebraicGeometry.LocallyRingedSpace.Hom.ext'` among them; 4 further lines of
this paragraph; and **10 `#print axioms` guard outputs in which the apostrophe is the closing
quote of a name that does not end in one at all**, such as the guard on
`AlgebraicGeometry.LocallyRingedSpace.GlueData.hom_ext`.

**`Classical.choice` is in all three guards and none of it is this section's subject.** The axiom
reaches `ComplexAnalytic.AnalyticSpace` itself, so every statement mentioning an analytic space
carries it whatever its own proof does; what these guards record is that neither the equality of
two analytic spaces nor the chart identification adds an axiom of its own. In particular
`ComplexAnalytic.AnalyticSpace.ext'` is four `cases` and an `rfl` and
`ComplexAnalytic.restrict_eq_ofCutOut` is a `RingHom.ext` over the `ℂ`-linearity hypothesis, and
the axiom list would look the same if either had been an argument of real weight.

**Named by file rather than counted**, in the spelling `### The disjoint union is the coproduct`
uses of itself and for the reason this file gives for that: a numeral over the sections of this
file is one a reader has to recheck, and the record at the head of this file is of four such
numerals standing false.

**Named and not located.** No sentence here says which section precedes or follows it.
-/

/--
info: 'ComplexAnalytic.AnalyticSpace.ext'' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.ext'

/--
info: 'ComplexAnalytic.restrict_eq_ofCutOut' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.restrict_eq_ofCutOut

/--
info: 'ComplexAnalytic.exists_restrict_eq_ofCutOut' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.exists_restrict_eq_ofCutOut

/-! ### The double of an analytic space along an open, and the complex line with two origins

Two copies of a space glued along an open subspace: the glue datum and the glued space one
category down, the analytic structure on it, the fold, that the fold is finite étale, and that
the double is not Hausdorff when a point outside the open is in its closure — with `ℂ¹` and its
origin as the concrete instance.

**Two modules, and the routing table sends both here.** `OkaTest/Axioms.lean`'s row *analytic
spaces, local models, the node* is where a module is sent by what declares it.
`Oka/AnalyticSpace/Double.lean` declares the analytic half;
`Oka/Geometry/RingedSpace/PresheafedSpace/Double.lean` declares the rest and is a mirror-tree
module, which `OkaTest/Axioms.lean` says has no row of its own — the same arrangement the section
headed *The fields of `CategoryTheory.GlueData.ofGlueData'`* is under.

**Why the finite-étale guards are here and not in `OkaTest/Axioms/Morphisms.lean`.** The module
docstring above says the *classes* of morphisms are that file's. These guards are not about the
classes: they are about one construction of a space and the morphism it comes with, which is the
arrangement `ComplexAnalytic.AnalyticSpace.isFiniteEtale_sigmaFold` is already guarded in under a
coproduct heading in this file. A guard here on `ComplexAnalytic.AnalyticSpace.IsFiniteEtale`
itself, or on one of its closure properties, would belong there and there is none.

**Two claims of the module docstring above were rechecked against this section and both survive.**
*"which is the one heading below naming a property of a space rather than a construction of one"*
is still exact: this heading names two constructions, and reading all twenty-two section headings
at the commit that adds this section leaves *The analytic spaces this development constructs are
Hausdorff* the only one naming a property. **A reader who takes that clause to be
about subjects rather than about headings should read this sentence as its amendment**, because
`ComplexAnalytic.AnalyticSpace.not_t2Space_doubledLine` is a guard on the negation of that
property. And *"Two of the headings below are about morphisms after all"* is unmoved: this
heading is about a space, in the sense the coproduct headings are.

**Every numeral in the module docstring above is pinned to a commit, so this section repairs
none of them** — including *"Six of the nineteen modules are not `Oka/AnalyticSpace/`'s"* and its
*"four modules of `Oka/Geometry/RingedSpace/` fifteen"*, both of which are `883b62f`'s and both
of which this section would have moved had they been live.

**`Classical.choice` is in every guard below and none of it is this section's subject.** The
axiom reaches `ComplexAnalytic.AnalyticSpace` and `AlgebraicGeometry.LocallyRingedSpace` alike,
so every statement here carries it whatever its own proof does; what these guards record is that
none of the constructions adds an axiom of its own — not the gluing, not the promotion to an
analytic space, and not the two-origin witness.

**The `_assoc` lemma the `reassoc` attribute generates is not guarded**, which is this
repository's standing arrangement: at the commit that adds this section the declaration dump
holds thirty-five names ending in `_assoc` — thirty-four of them at `d2ae161` and this section's
one — and no `#print axioms` in `OkaTest/Axioms/` names any of them.

**Named by file rather than counted**, in the spelling the section headed *The disjoint union is
the coproduct* uses of itself, and for the reason this file gives for it. **Named and not
located**: no sentence here says which section precedes or follows it.
-/

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.double' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.double

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.doubleFold' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.doubleFold

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.doubleFoldPartialHomeomorph' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.doubleFoldPartialHomeomorph

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.doubleFold_base_comp_ι_base' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.doubleFold_base_comp_ι_base

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.doubleFold_base_ι_base' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.doubleFold_base_ι_base

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.doubleGlueData' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.doubleGlueData

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.doubleGlueData'' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.doubleGlueData'

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.doubleGlueData_U' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.doubleGlueData_U

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.doubleGlueData_V_of_ne' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.doubleGlueData_V_of_ne

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.doubleGlueData_comm' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.doubleGlueData_comm

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.doubleGlueData_f_eq_t_comp_f' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.doubleGlueData_f_eq_t_comp_f

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.doubleGlueData_f_of_ne' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.doubleGlueData_f_of_ne

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.doubleGlueData_t_comp_f_of_ne' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.doubleGlueData_t_comp_f_of_ne

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.doubleGlueData_ι_base_eq_iff' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.doubleGlueData_ι_base_eq_iff

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.doubleGlueData_ι_base_eq_iff_of_ne' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.doubleGlueData_ι_base_eq_iff_of_ne

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.finite_preimage_base_doubleFold' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.finite_preimage_base_doubleFold

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.image_base_doubleFold' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.image_base_doubleFold

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.injective_base_doubleGlueData_ι' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.injective_base_doubleGlueData_ι

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.isClosedMap_base_doubleFold' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.isClosedMap_base_doubleFold

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.isIso_stalkMap_doubleFold' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.isIso_stalkMap_doubleFold

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.isLocalHomeomorph_base_doubleFold' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.isLocalHomeomorph_base_doubleFold

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.not_t2Space_double' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.not_t2Space_double

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.preimage_base_doubleFold_singleton' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.preimage_base_doubleFold_singleton

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.ι_doubleFold' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.ι_doubleFold

/--
info: 'ComplexAnalytic.AnalyticSpace.double' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.double

/--
info: 'ComplexAnalytic.AnalyticSpace.doubleFold' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.doubleFold

/--
info: 'ComplexAnalytic.AnalyticSpace.double_toLocallyRingedSpace' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.double_toLocallyRingedSpace

/--
info: 'ComplexAnalytic.AnalyticSpace.doubledLine' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.doubledLine

/--
info: 'ComplexAnalytic.AnalyticSpace.doubledLineFold' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.doubledLineFold

/--
info: 'ComplexAnalytic.AnalyticSpace.doubledLineOver' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.doubledLineOver

/--
info: 'ComplexAnalytic.AnalyticSpace.exists_finiteEtaleOver_not_t2Space' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.exists_finiteEtaleOver_not_t2Space

/--
info: 'ComplexAnalytic.AnalyticSpace.glueDataCLinear_double' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.glueDataCLinear_double

/--
info: 'ComplexAnalytic.AnalyticSpace.isFiniteEtale_doubleFold' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.isFiniteEtale_doubleFold

/--
info: 'ComplexAnalytic.AnalyticSpace.isFiniteEtale_doubledLineFold' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.isFiniteEtale_doubledLineFold

/--
info: 'ComplexAnalytic.AnalyticSpace.isFinite_doubleFold' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.isFinite_doubleFold

/--
info: 'ComplexAnalytic.AnalyticSpace.isLocalIso_doubleFold' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.isLocalIso_doubleFold

/--
info: 'ComplexAnalytic.AnalyticSpace.neBot_nhdsWithin_compl_origin' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.neBot_nhdsWithin_compl_origin

/--
info: 'ComplexAnalytic.AnalyticSpace.not_t2Space_double' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.not_t2Space_double

/--
info: 'ComplexAnalytic.AnalyticSpace.not_t2Space_double_compl_singleton' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.not_t2Space_double_compl_singleton

/--
info: 'ComplexAnalytic.AnalyticSpace.not_t2Space_doubledLine' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.not_t2Space_doubledLine

/--
info: 'ComplexAnalytic.AnalyticSpace.not_t2Space_left_doubledLineOver' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.not_t2Space_left_doubledLineOver

/--
info: 'ComplexAnalytic.AnalyticSpace.origin' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.origin

/--
info: 'ComplexAnalytic.AnalyticSpace.toLRSHom_doubleFold' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.toLRSHom_doubleFold


/-! ### The fibre product glued out of a family of opens, and its two projections

`Oka/AnalyticSpace/PullbackGlue.lean`, the whole of it, in the order the declarations are made.
**Thirty-three names**, of which fourteen are the ones the section opened with at `a401c63`.

The glue datum assembled out of `Oka/AnalyticSpace/PullbackBlock.lean`'s transition data, the
`ℂ`-linearity that lets it be promoted, the analytic space it glues to, the two projections and
the square they make commute — together with the two forms of the `t_fac` law the datum's field
asks for and the two overlap compatibilities the projections are glued from.

**The routing, argued rather than assumed, because the module is new.** Every
`#print axioms` name below resolves to `Oka/AnalyticSpace/PullbackGlue.lean`, so the recipe beside
`OkaTest/Axioms.lean`'s routing table asks one question and not one per name: does *analytic
spaces, local models, the node* cover that module. It does — the module builds an analytic space,
`ComplexAnalytic.AnalyticSpace.Pullback.glued`, by
`ComplexAnalytic.AnalyticSpace.ofGlueDataCLinear`, which is the construction the module docstring
above names when it says *the analytic structure on the gluing*. **The arrangement is
`Oka/AnalyticSpace/Double.lean`'s exactly**: a glue datum stated one category down, the analytic
space it glues to, and the morphisms that come with the construction, all under one heading in
this file.

**Why this is not a third heading about morphisms.** The module docstring above says **two** of
the headings below are about morphisms after all, and names them. This is not a third, for the
reason the section headed *The double of an analytic space along an open, and the complex line
with two origins* gives for itself: the heading is about a space, and
`ComplexAnalytic.AnalyticSpace.Pullback.p1`, `…p2` and `…p_comm` are part of the construction of
that space in the way `ComplexAnalytic.AnalyticSpace.doubleFold` is part of the double's — not
statements whose subject is a morphism and which name no new space, which is what the two it does
name have in common.
A guard here on `ComplexAnalytic.AnalyticSpace.IsFiniteEtale` or on any other *class* of
morphisms would belong in `OkaTest/Axioms/Morphisms.lean`, and there is none. **The lift is tested
against the same criterion and passes it for the same reason**:
`ComplexAnalytic.AnalyticSpace.Pullback.gluedLift` is a morphism, and it names
`ComplexAnalytic.AnalyticSpace.Pullback.glued` — it is the universal property of that space, in
the same way `…p1` and `…p2` are its projections.

**And it is not `OkaTest/Axioms/Morphisms.lean`'s, even though the module sits on top of one that
is.** `Oka/AnalyticSpace/PullbackBlock.lean` is guarded there, under
*The transition data of a fibre product glued over a family of opens*, and its own section argues
that placement from the same recipe. The two modules resolve differently because the recipe asks
what a module *is*, not what it imports: that one is transition data and states no object of
`ComplexAnalytic.AnalyticSpace` beyond the overlaps its morphisms need, while this one's headline
declaration is an analytic space. **Nothing below is a declaration of
`Oka/AnalyticSpace/PullbackBlock.lean`**, so no name is guarded twice.

**Nothing generated is guarded, which is this repository's standing arrangement, and here there
now is something generated.** The push that added the first fourteen added **no** `_assoc` lemma,
**no** `.eq_1` equation lemma and **no** match lemma, and that sentence is pinned to it: at
`a401c63` the module's tab-anchored row count in the declaration dump was fourteen, four of them
`def`s — `ComplexAnalytic.AnalyticSpace.Pullback.gluing`, `…glued`, `…p1` and `…p2`. **The push
that adds the lift makes the row count thirty-six against thirty-three guards, and the three that
are not guarded are generated**: `…Pullback.overlapLift_fV_assoc` and `…overlapLift_t_fV_assoc`,
which the `reassoc` attribute produces from two of the names below, and
`ComplexAnalytic.AnalyticSpace.restrictLE.congr_simp`, which is a congruence lemma for a
declaration of `Oka/AnalyticSpace/OpenSubspace.lean` that this module is merely where it was first
demanded. **No `.eq_1` and no match lemma at either commit.** Equation lemmas are generated on
demand, so both sentences are statements about the environment at the commit each names and
neither is a prediction about later ones.

**What is guarded under *this heading* still does not include a fibre product**, and the lift did
not change that. `ComplexAnalytic.AnalyticSpace.Pullback.gluedLift` says a competing cone
*factors* through the gluing and `…gluedLift_p1` and `…gluedLift_p2` say through which legs; **no
guard of this section says the factorisation is unique**, and `CategoryTheory.Limits.IsLimit`
needs that.

**This paragraph said *no declaration below* and *below* reached past this section, so it is
retired and rescoped rather than recounted.** It was written when this heading was the last in the
file and it was exact then, at `a401c63` and at the commit that added the lift. It is not exact
now: the heading that follows this one, *The gluing is the fibre product: uniqueness of the lift,
the limit cone, and `HasPullback`*, guards
`ComplexAnalytic.AnalyticSpace.Pullback.gluedLift_uniq`, `…gluedIsLimit` and
`…hasPullback_of_cover`, which say exactly the three things this paragraph denied of everything
below it. **The claim survives with *below* replaced by *in this section*, and it is checked that
way**: none of the thirty-three names under this heading mentions uniqueness, a limit or a
`CategoryTheory.Limits.HasPullback`.

**What did not move is the synthesis probe.**
`CategoryTheory.Limits.HasPullbacks ComplexAnalytic.AnalyticSpace` still does not synthesise —
re-run at the commit that adds the section headed *The gluing is the fibre product: uniqueness of
the lift, the limit cone, and `HasPullback`* and not carried over, as it was re-run at the
commit that added the lift. The probe is
`#synth CategoryTheory.Limits.HasPullbacks ComplexAnalytic.AnalyticSpace`, run rather than
grepped, with the category **positional** — the form
`Oka/AnalyticSpace/AffineProductOpen.lean` uses, and the form that asks about the class rather
than about an object. `…hasPullback_of_cover` does not make it synthesise because it asks for a
covering family along which the base change is already known, and nothing produces one for a
general cospan.

**The probe moved on 2026-09-08 and this paragraph is the record of what it said before.** Both
sentences above are pinned to the commits they were run at and neither is retired; what is retired
is the reading of *still does not synthesise* as a claim about the tree.
`Oka/AnalyticSpace/PullbackReduction.lean` produced the covering family, and
`ComplexAnalytic.AnalyticSpace.hasPullbacks` is the class; it is guarded under the section headed
*The reduction of a general cospan, and the category with pullbacks*. **No positional pointer is
written here**: the paragraph above is about a *below* that reached past its own section, and this
one names each section it mentions by its heading. -/

/--
info: 'ComplexAnalytic.AnalyticSpace.Pullback.t'_fac' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.Pullback.t'_fac

/--
info: 'ComplexAnalytic.AnalyticSpace.Pullback.t'Map_fac' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.Pullback.t'Map_fac

/--
info: 'ComplexAnalytic.AnalyticSpace.Pullback.gluing' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.Pullback.gluing

/--
info: 'ComplexAnalytic.AnalyticSpace.Pullback.glueDataCLinear_gluing' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.Pullback.glueDataCLinear_gluing

/--
info: 'ComplexAnalytic.AnalyticSpace.Pullback.glued' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.Pullback.glued

/--
info: 'ComplexAnalytic.AnalyticSpace.Pullback.glued_toLocallyRingedSpace' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.Pullback.glued_toLocallyRingedSpace

/--
info: 'ComplexAnalytic.AnalyticSpace.Pullback.fV_comp_toBase' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.Pullback.fV_comp_toBase

/--
info: 'ComplexAnalytic.AnalyticSpace.Pullback.fV_comp_snd' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.Pullback.fV_comp_snd

/--
info: 'ComplexAnalytic.AnalyticSpace.Pullback.p1' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.Pullback.p1

/--
info: 'ComplexAnalytic.AnalyticSpace.Pullback.p2' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.Pullback.p2

/--
info: 'ComplexAnalytic.AnalyticSpace.Pullback.toBase_comp' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.Pullback.toBase_comp

/--
info: 'ComplexAnalytic.AnalyticSpace.Pullback.ι_p1' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.Pullback.ι_p1

/--
info: 'ComplexAnalytic.AnalyticSpace.Pullback.ι_p2' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.Pullback.ι_p2

/--
info: 'ComplexAnalytic.AnalyticSpace.Pullback.p_comm' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.Pullback.p_comm

/--
info: 'ComplexAnalytic.AnalyticSpace.Pullback.ι' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.Pullback.ι

/--
info: 'ComplexAnalytic.AnalyticSpace.Pullback.toLRSHom_ι' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.Pullback.toLRSHom_ι

/--
info: 'ComplexAnalytic.AnalyticSpace.Pullback.fV_comp_ι' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.Pullback.fV_comp_ι

/--
info: 'ComplexAnalytic.AnalyticSpace.Pullback.ι_comp_p1' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.Pullback.ι_comp_p1

/--
info: 'ComplexAnalytic.AnalyticSpace.Pullback.ι_comp_p2' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.Pullback.ι_comp_p2

/--
info: 'ComplexAnalytic.AnalyticSpace.Pullback.conePreimage' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.Pullback.conePreimage

/--
info: 'ComplexAnalytic.AnalyticSpace.Pullback.liftMember' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.Pullback.liftMember

/--
info: 'ComplexAnalytic.AnalyticSpace.Pullback.liftMember_fst' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.Pullback.liftMember_fst

/--
info: 'ComplexAnalytic.AnalyticSpace.Pullback.liftMember_snd' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.Pullback.liftMember_snd

/--
info: 'ComplexAnalytic.AnalyticSpace.Pullback.overlapLift' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.Pullback.overlapLift

/--
info: 'ComplexAnalytic.AnalyticSpace.Pullback.overlapLift_fV' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.Pullback.overlapLift_fV

/--
info: 'ComplexAnalytic.AnalyticSpace.Pullback.overlapLift_snd' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.Pullback.overlapLift_snd

/--
info: 'ComplexAnalytic.AnalyticSpace.Pullback.overlapLift_t_fV' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.Pullback.overlapLift_t_fV

/--
info: 'ComplexAnalytic.AnalyticSpace.Pullback.conePreimage_covers' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.Pullback.conePreimage_covers

/--
info: 'ComplexAnalytic.AnalyticSpace.Pullback.restrictLE_comp_liftMember_comp_ι' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.Pullback.restrictLE_comp_liftMember_comp_ι

/--
info: 'ComplexAnalytic.AnalyticSpace.Pullback.gluedLift' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.Pullback.gluedLift

/--
info: 'ComplexAnalytic.AnalyticSpace.Pullback.ofRestrict_comp_gluedLift' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.Pullback.ofRestrict_comp_gluedLift

/--
info: 'ComplexAnalytic.AnalyticSpace.Pullback.gluedLift_p1' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.Pullback.gluedLift_p1

/--
info: 'ComplexAnalytic.AnalyticSpace.Pullback.gluedLift_p2' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.Pullback.gluedLift_p2


/-! ### The gluing is the fibre product: uniqueness of the lift, the limit cone, and `HasPullback`

`Oka/AnalyticSpace/PullbackLimit.lean`, the whole of it, in the order the declarations are made.
**Nine names**, and the module is new.

The image of a member of the gluing, the factorisation of a morphism through a member that image
computation makes available, the uniqueness of the lift out of a competing cone, the limit cone
that uniqueness completes, and the fibre product it gives.

**The routing, argued rather than assumed, because the module is new.** Every `#print axioms` name
below resolves to `Oka/AnalyticSpace/PullbackLimit.lean`, so the recipe beside
`OkaTest/Axioms.lean`'s routing table asks one question and not one per name: does *analytic
spaces, local models, the node* cover that module. It does, and **for the reason the section above
gives for the lift**: `ComplexAnalytic.AnalyticSpace.Pullback.gluedIsLimit` is the universal
property of `ComplexAnalytic.AnalyticSpace.Pullback.glued`, the analytic space that section's
module builds, and `…hasPullback_of_cover` asserts that an analytic space with that property
exists. A statement that a named space is a limit is a statement about that space in the way
`ComplexAnalytic.AnalyticSpace.Pullback.p1` and `…p2` are — it names no class of morphisms and
introduces no morphism whose subject is not `…glued`.

**This is not a third heading about morphisms.** The module docstring at the head of this file
says **two** of the headings here are about morphisms after all and names them; the section above
argued it was not a third and this is not a fourth, on the same criterion. The four names below
that are morphisms or about morphisms —
`ComplexAnalytic.AnalyticSpace.Pullback.liftι`, `…liftι_fac`, `…liftι_eq_liftMember` and
`…isOpenImmersion_toLRSHom_ι` — are all about
`ComplexAnalytic.AnalyticSpace.Pullback.ι`, whose own guards are under the section above and for
whose placement that section already argues. **A guard here on
`ComplexAnalytic.AnalyticSpace.IsFiniteEtale` or on any other *class* of morphisms would belong in
`OkaTest/Axioms/Morphisms.lean`, and there is none.**

**Two declarations of this push are guarded in `OkaTest/Axioms/Morphisms.lean` and not here**, and
they are not declarations of this module: `ComplexAnalytic.AnalyticSpace.range_base_ofRestrict` is
`Oka/AnalyticSpace/OpenSubspace.lean`'s and `…range_base_pullbackFst_ofRestrict` is
`Oka/AnalyticSpace/PullbackOpen.lean`'s, and every other guard of that second module is in that
file already. The recipe asks what a module *is*: those two are about the underlying map of a
morphism, which is that file's subject, and this module's headline declaration is a limit.
**Nothing below is a declaration of either of those modules**, so no name is guarded twice.

**One `info:` line below is 101 characters and cannot be wrapped**, which is
`ComplexAnalytic.AnalyticSpace.Pullback.range_base_ofRestrict_comp_subset_ι`'s: `#guard_msgs`
compares the message and the name is most of the message. **Lines like it stood under `OkaTest/`
before this one, and how many is not written down here, because the next guard on a long name
moves it**: they are in `OkaTest/Axioms/SheafOfModules.lean`, `OkaTest/Axioms/Sheaves.lean`,
`OkaTest/Axioms/Morphisms.lean`, `OkaTest/Axioms/Analytification.lean` and this file, each an
`info:` line of a long name, and a scan for lines over a hundred **characters** lists whichever
stand on the day it is run — in codepoints and not in bytes, since `awk 'length > 100'` counts
bytes, and an em dash is three of them, so it reports lines here that are not long. **Its own
`#print axioms` line is *not* wrapped**, the name fitting after the command, so the line-based
`#print axioms\s+(\S+)` scan `OkaTest/Axioms.lean` warns about reads all nine of this section's
guards and not eight.

**This paragraph read *Thirteen such lines already stand under `OkaTest/`*, split that figure
across the files by name, and closed *This is the fourteenth and there are no others*,
until 2026-09-13.** It was exact at `7a99bfc`, the commit that wrote it; `2d376d5` and
`7b7ce5a` each appended a long `info:` line to `OkaTest/Axioms/Morphisms.lean` and swept
nothing, which falsified the total, that file's share of it and the closing clause together.
**The files it named are still the files that carry such lines**, which is why naming them is
what survives an append and counting them was not.

**Nothing generated is guarded and here there is nothing generated.** The module's tab-anchored
row count in `scripts/DumpOkaDecls.lean`'s output is **nine** against nine guards: no `_assoc`
lemma, no `.eq_1` equation lemma, no match lemma and no congruence lemma. **One match lemma was
avoided rather than absent** — `ComplexAnalytic.AnalyticSpace.range_base_ofRestrict`, in the other
file, was first written with a destructuring `fun ⟨y, hy⟩ ↦ …` and generated one; its own
docstring records why it is `Subtype.range_val` instead. Equation lemmas are generated on demand,
so this is a statement about the environment at the commit that adds this section and not a
prediction about later ones.

**What is guarded here does include a fibre product, and it is the first heading in this file of
which that is true.** `ComplexAnalytic.AnalyticSpace.Pullback.hasPullback_of_cover` says a cospan
has one — under two hypotheses, that the `U i` cover `X` and that the base change of `g` along
each `U i ⟶ X ⟶ Z` already exists. **Neither hypothesis is discharged anywhere in this
repository for a general cospan**, so
`CategoryTheory.Limits.HasPullbacks ComplexAnalytic.AnalyticSpace` still does not synthesise; the
section headed *The fibre product glued out of a family of opens, and its two projections* records
the probe and it was re-run at this commit.

**Both hypotheses are discharged now and the sentence above is kept as the record.** The section
headed *The reduction of a general cospan, and the category with pullbacks* guards
`ComplexAnalytic.AnalyticSpace.hasPullback_ofRestrict_comp`, which is the
second hypothesis at the family the first is discharged by, and
`ComplexAnalytic.AnalyticSpace.hasPullbacks`, which is what the probe now finds. **This is not a
recount and the heading is unchanged**: what this section guards is still the cover-indexed
statement and not the general one, and *the first heading in this file of which that is true* is
still exact, because a first stays first. -/

/--
info: 'ComplexAnalytic.AnalyticSpace.Pullback.range_base_ι' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.Pullback.range_base_ι

/--
info: 'ComplexAnalytic.AnalyticSpace.Pullback.isOpenImmersion_toLRSHom_ι' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.Pullback.isOpenImmersion_toLRSHom_ι

/--
info: 'ComplexAnalytic.AnalyticSpace.Pullback.liftι' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.Pullback.liftι

/--
info: 'ComplexAnalytic.AnalyticSpace.Pullback.liftι_fac' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.Pullback.liftι_fac

/--
info: 'ComplexAnalytic.AnalyticSpace.Pullback.range_base_ofRestrict_comp_subset_ι' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.Pullback.range_base_ofRestrict_comp_subset_ι

/--
info: 'ComplexAnalytic.AnalyticSpace.Pullback.liftι_eq_liftMember' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.Pullback.liftι_eq_liftMember

/--
info: 'ComplexAnalytic.AnalyticSpace.Pullback.gluedLift_uniq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.Pullback.gluedLift_uniq

/--
info: 'ComplexAnalytic.AnalyticSpace.Pullback.gluedIsLimit' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.Pullback.gluedIsLimit

/--
info: 'ComplexAnalytic.AnalyticSpace.Pullback.hasPullback_of_cover' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.Pullback.hasPullback_of_cover


/-! ### The reduction of a general cospan, and the category with pullbacks

`Oka/AnalyticSpace/PullbackReduction.lean`, the whole of it, in the order the declarations are
made. **Eight names**, and the module is new.

A space that *is* a local model on the nose and the neighbourhood of a point that is one; then a
cospan of three of them, a cospan with the source of its first leg arbitrary, a cospan with only
its base a local model, the covering family a general cospan needs, and the general cospan itself;
then the category.

**Every guard here is of one of three kinds and the three partition the eight.** Two are about a
*space*: `ComplexAnalytic.IsCutOutModel` is a predicate on one and
`ComplexAnalytic.exists_isCutOutModel_restrict` says every point of one has a neighbourhood
satisfying it. Five say a *cospan has a fibre product* —
`ComplexAnalytic.AnalyticSpace.hasPullback_of_isCutOutModel`, `…_right`, `…_base`,
`…hasPullback_ofRestrict_comp` and `…hasPullback`. One is about the *category*:
`ComplexAnalytic.AnalyticSpace.hasPullbacks`. Two plus five plus one is eight, which is the number
of `#print axioms` lines below.

**The routing is by module and the module rule is what puts the last of those three here.**
`OkaTest/Axioms.lean`'s recipe resolves every `#print axioms` name of a file to the module the
declaration lives in and asks whether the row's phrase covers what comes back; all eight resolve
to `Oka/AnalyticSpace/PullbackReduction.lean`, and *analytic spaces, local models, the node*
covers that module — two of its eight declarations are about local models by name, and the other
six are the ladder that carries the fibre product from a cospan of local models to an arbitrary
one. The section headed *The gluing is the fibre product: uniqueness of the lift, the limit cone,
and `HasPullback`* took the same decision for
`ComplexAnalytic.AnalyticSpace.Pullback.hasPullback_of_cover` and gives the same reason.

**`ComplexAnalytic.AnalyticSpace.hasPullbacks` is about the category rather than about any
morphism in it, which is the description `OkaTest/Axioms/Morphisms.lean` gives of a kind of its
own, and it is here and not there.** That is a real tension and it is said rather than left to be
found. What settles it is that the routing rule is over modules and not over statements: splitting
one module's eight guards across two files to follow a kind would put a name in
`OkaTest/Axioms/Morphisms.lean` whose module has no other guard there, which is the shape the
section headed *The gluing is the fibre product: uniqueness of the lift, the limit cone, and
`HasPullback`* declined for the opposite reason — it kept two names *out* of this file because
their modules' other guards were already elsewhere. **And a category-level guard here is not a
first**: `ComplexAnalytic.AnalyticSpace.hasCoproducts` and `…hasFiniteCoproducts`, under the
section headed *The disjoint union is the coproduct*, are `CategoryTheory.Limits.HasCoproducts`
and `CategoryTheory.Limits.HasFiniteCoproducts` of this same category and are guarded in this
file, by the same module rule and with no tension recorded there. So this section is the third of
three and the module rule has already decided the question twice. **A reader looking for
`CategoryTheory.Limits.HasPullbacks ComplexAnalytic.AnalyticSpace` in that file will not find it,
and this paragraph is the pointer that stops the search there.**

**This is not a third heading about morphisms.** The module docstring at the head of this file
says **two** of the headings here are about morphisms after all and names them; the sections
headed *The fibre product glued out of a family of opens, and its two projections* and *The gluing
is the fibre product: uniqueness of the lift, the limit cone, and `HasPullback`* each argued they
were not a further one, and this is not a further one either, on the same criterion. Nothing below
names a *class* of morphisms — no `ComplexAnalytic.AnalyticSpace.IsFinite`,
no `…IsFiniteEtale`, no `…IsLocalIso` — and a guard on one would belong in
`OkaTest/Axioms/Morphisms.lean`.

**Nothing generated is guarded and here there is nothing generated.** The module's tab-anchored row
count in `scripts/DumpOkaDecls.lean`'s output is **eight** against eight guards: no `_assoc` lemma,
no `.eq_1` equation lemma, no match lemma and no congruence lemma. `ComplexAnalytic.IsCutOutModel`
is a `def` into `Prop` and generates none; the two `instance`s generate none either. Equation
lemmas are generated on demand, so this is a statement about the environment at the commit that
adds this section and not a prediction about later ones.

**No `info:` line below reaches 100 characters** — the longest is
`ComplexAnalytic.AnalyticSpace.hasPullback_of_isCutOutModel_right`'s, at 91 — so the count of
over-long `info:` lines under `OkaTest/` that the section headed *The gluing is the fibre product:
uniqueness of the lift, the limit cone, and `HasPullback`* states is unchanged by this push, and
none of the eight `#print axioms` lines below is wrapped.

**The synthesis probe succeeds at the commit that adds this section, and that is the change.**
`#synth CategoryTheory.Limits.HasPullbacks ComplexAnalytic.AnalyticSpace` answers
`ComplexAnalytic.AnalyticSpace.hasPullbacks`, run rather than grepped, with the category
**positional** — the same form the sections headed *The fibre product glued out of a family of
opens, and its two projections* and *The gluing is the fibre product: uniqueness of the lift, the
limit cone, and `HasPullback`* record it failing in — and with `example : False := trivial` at the
foot of the probe file, which errored, so the file did elaborate and a green `#synth` is not the
false alarm taxis #1821 records. **Those two records are pinned to their own commits and neither
is retired by this**; what they say of the tree at those commits was exact. -/

/--
info: 'ComplexAnalytic.IsCutOutModel' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.IsCutOutModel

/--
info: 'ComplexAnalytic.exists_isCutOutModel_restrict' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.exists_isCutOutModel_restrict

/--
info: 'ComplexAnalytic.AnalyticSpace.hasPullback_of_isCutOutModel' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.hasPullback_of_isCutOutModel

/--
info: 'ComplexAnalytic.AnalyticSpace.hasPullback_of_isCutOutModel_right' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.hasPullback_of_isCutOutModel_right

/--
info: 'ComplexAnalytic.AnalyticSpace.hasPullback_of_isCutOutModel_base' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.hasPullback_of_isCutOutModel_base

/--
info: 'ComplexAnalytic.AnalyticSpace.hasPullback_ofRestrict_comp' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.hasPullback_ofRestrict_comp

/--
info: 'ComplexAnalytic.AnalyticSpace.hasPullback' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.hasPullback

/--
info: 'ComplexAnalytic.AnalyticSpace.hasPullbacks' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.hasPullbacks
