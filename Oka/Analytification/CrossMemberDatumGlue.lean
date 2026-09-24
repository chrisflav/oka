/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Analytification.CrossMemberDatum

/-!
# The `glue` field of a cross-member refined datum: the two branches, and the case split between
them

`Oka/Analytification/CrossMemberDatum.lean` builds the `poly` field of a refined cover datum whose
members lie over different members of the original cover, and prices the next field in its
`## What is not here`:

> **No `glue`, no `hrange`, no `hsymm` and no `hcocycle`** … The glue is where the transport this
> file relocates has to be paid: at `σ a = σ b` the two sides of `ComplexAnalytic.refineGlue`'s
> configuration sit over `obj (σ a)` and over `obj (σ b)`, which are propositionally and not
> definitionally equal, so the equal branch needs a transport between two objects of
> `ComplexAnalytic.Presentation` that the one-member file never meets. **That is measured only as a
> type mismatch and no attempt to discharge it is compiled**; nothing here is evidence about its
> size.

**The type mismatch is real and it is discharged here in one tactic.** The equal branch of the
glue, its symmetry, its coherence triangle and the analytified form of that triangle are all
below; what the branch costs is one generalisation and `subst`.

**The other branch is `Oka/Analytification/CrossMemberGlue.lean`'s cross-member glue, and the
field is the two of them under a case split.** `ComplexAnalytic.refineDatumGlueNe` conjugates that
glue onto the datum's own overlaps — the same three-factor shape as the equal branch, with
`ComplexAnalytic.refineDatumPoly_of_ne` in place of `ComplexAnalytic.refineDatumPoly_of_eq` — and
`ComplexAnalytic.refineDatumGlue` is `dite (σ a = σ b)` of the two.

## The choice is the caller's, and that is a decision this file makes

The cross-member glue takes a polynomial `r`, a unit `u` and two equations, and a bullet saying
nothing there produces `q` is what both facing files carry. **The field takes them rather than
producing them**, indexed by the ordered pair and guarded by `σ a ≠ σ b`, which is exactly what
`ComplexAnalytic.refineDatumPoly` already does with `q`. Two consequences and neither is hidden:

* the existence question is untouched *here* — nothing below says a choice exists, and nothing
  below instantiates `ComplexAnalytic.exists_localisationOpen_eq_rename` or
  `ComplexAnalytic.exists_mk_rename_eq`. **It is settled elsewhere and only in its algebraic
  half**: `ComplexAnalytic.exists_refineDatumCross`
  (`Oka/Analytification/CrossMemberChoice.lean`) produces a choice at every ordered pair, spending
  the second of those two and neither the first nor the geometric one, and the first bullet of
  `## What is not here` says what that does and does not buy;
* **`hsymm` is a theorem about the field after all, and it is not proved here.** A cover datum's
  symmetry law relates the pair `(a, b)` to the pair `(b, a)`, and off the diagonal those are two
  independent choices. **This bullet read *"`hsymm` becomes an obligation on the caller's choice
  rather than a theorem about the field … whether they can be made compatibly is unproved in both
  directions"* until `Oka/Analytification/RefineDatumSymm.lean` landed**, and that file proves the
  law for two arbitrary independent choices: the two never have to be compatible, because the
  coherence triangle below determines the isomorphism and the inverse of the one at `(a, b)`
  satisfies the triangle at `(b, a)`. What is still true is that this file does not state it —
  the monomorphism that makes the triangle determining is not available here.

## The case split needs no transport, and that is worth saying because the last one did

The field's type names `ComplexAnalytic.refineDatumPoly` and no case at all, so **both branches
are isomorphisms between the same two objects** and the `dite` is a split between two *terms* of
one type. `ComplexAnalytic.refineDatumFactor` splits between two *values* of one type and needs a
`▸` for the equal case; nothing of that shape survives at this level. Had it not been so the split
would have been a third transport, in the shape of the overlap, where every statement below would
meet it.

## The transport, and why generalising the two members is the whole trick

`σ a = σ b` is an equation between two *applications*, so neither side is a local variable and
`subst` does not apply to it. What does apply is the same equation with both members generalised:
for free `i j : J` and `h : i = j`, `subst h` replaces `j` by `i` throughout and the two
presentations become the one presentation, definitionally. So the file is arranged in three
layers, and only the first has any mathematics in it:

* `ComplexAnalytic.refineSwapGlue` — over **one** member, at two bare refining polynomials `x` and
  `y`. This is `Oka/Analytification/CoverRefinement.lean`'s glue with the family replaced by its
  two values, and it is built from the same two localisation isomorphisms at the two orders of the
  product.
* `ComplexAnalytic.refineSwapGlueOfEq` — the same over two members related by `h : i = j`, which
  is the previous one after `subst h`.
* `ComplexAnalytic.refineDatumGlueEq` — the datum's field, which is the previous one conjugated by
  the two transports that turn `ComplexAnalytic.refineDatumPoly` into the polynomial each side is
  stated at. Those two are `ComplexAnalytic.refineDatumPoly_of_eq` at the equation and at its
  `Eq.symm`, and nothing else is needed. (Spelled that way because field notation on a local
  hypothesis, in backticks, has no whitespace in it, so `scripts/check_docstring_names.py` reads
  it as a declaration reference — and the one this paragraph first used *resolved*, against
  something in Mathlib that has nothing to do with this file. A checker that reports zero
  unresolved names has not said the citations are right.)

**The two bare polynomials are what make the middle layer possible.** Stating the swap for a
*family* `K → MvPolynomial …` would put `K`'s indexing between `subst` and the goal; stating it at
`x` and `y` leaves the equation `i = j` as the only dependency, and that is what `subst` consumes.

## `refineDatumOverlap`, and why the overlap is spelled with its polynomial free

`ComplexAnalytic.coverOverlap` of the refined data at `(a, b)` is a presentation built from the
`a`-th refined member and one polynomial, and every statement below has to name it twice at two
*different* polynomials — once at `ComplexAnalytic.refineDatumPoly` and once at the renamed
refining polynomial it equals. `ComplexAnalytic.refineDatumOverlap` is that presentation with the
polynomial abstracted, so the two spellings differ in one argument rather than in a nested
structure literal, and `ComplexAnalytic.coverOverlap_refineDatumObj` says the abstraction is the
overlap on the nose. It is an `abbrev` for the reason
`ComplexAnalytic.refineDatumObj` is: everything below rewrites through it.

## The `rw` discipline, in both of its forms, and two things neither file describes

`Oka/Analytification/CrossMemberGlue.lean` states the discipline — open a definition with `change`
or a term, not with `rw` — and `Oka/Analytification/CrossMemberDatum.lean` adds the variant where
the planted equation lemma belongs to another file. **Both fired here**, the second one only when
the unequal branch was added, **and two things neither file describes fired as well.**

* **The plain form, caught by the declaration dump and not by the build.** The first draft proved
  the two symmetry laws and the two coherence triangles with `rw [refineSwapGlue]` and
  `rw [refineDatumGlueEq]`. That is green, and it plants `ComplexAnalytic.refineSwapGlue.eq_1`,
  `ComplexAnalytic.refineDatumGlueEq.eq_1` and `ComplexAnalytic.refineDatumGlueEq.congr_simp`:
  `Δdump` was **+17** where the file declared fourteen things. The cure is
  `ComplexAnalytic.refineSwapGlue_eq` and `ComplexAnalytic.refineDatumGlueEq_eq`, two `rfl`
  theorems that say the same thing under a name this file owns, and rewriting with those instead.
  It is also a better interface, which is why they are advertised.
* **A definition whose body cannot be written back down cannot be opened by `change` either.**
  The swap's middle factor was `eqToIso (by rw [mul_comm])`, and an anonymous tactic proof has no
  spelling — so `ComplexAnalytic.refineSwapGlue_eq` could not be stated until the transport was
  named, and `ComplexAnalytic.refineSwapMul` is that name. **Only that one of the two `rfl`
  theorems named above was blocked on it**: `ComplexAnalytic.refineDatumGlueEq_eq`'s right-hand
  side spells `ComplexAnalytic.refineSwapGlueOfEq` and two `ComplexAnalytic.refineDatumPoly_of_eq`
  congruences, and mentions `ComplexAnalytic.refineSwapMul` nowhere — so it was statable with the
  `mul_comm` proof still anonymous. **A definition that a later proof will have to open should
  not carry an anonymous proof term**, and this is the shape of that rule.
* **Three generated declarations are left, and each is `simp only … at` and not `rw`.**
  `ComplexAnalytic.refineDatumGlueEq.congr_simp` is planted by the `simp only … at e` in
  `ComplexAnalytic.refineDatumGlueEq_analytification_comp`;
  `ComplexAnalytic.refineDatumGlueNe.congr_simp` and
  `ComplexAnalytic.refineDatumCrossProj.congr_simp` by the ones in
  `ComplexAnalytic.refineDatumGlueNe_analytification_comp` and
  `ComplexAnalytic.refineDatumCrossProj_analytification_localisationProj` — **and the two have
  different numbers of sources, which no single deletion can tell you.** Deleting each theorem and
  re-dumping, three times and from a tree restored between runs: the triangle alone costs
  `Δdump = −2` and takes `ComplexAnalytic.refineDatumGlueNe.congr_simp` with it; the projection
  lemma alone costs **`−1`** and takes neither; the two together cost `−4`. So the first has one
  source and **`ComplexAnalytic.refineDatumCrossProj.congr_simp` is planted redundantly, by either
  theorem on its own** — the triangle's hypothesis mentions
  `ComplexAnalytic.refineDatumCrossProj` at `h` and at `h.symm`, so simp needs the congruence
  lemma to traverse it there exactly as it does in the projection lemma. **A branch that drops the
  projection lemma should expect `−1` and not `−2`**, and deleting both leaves a dump that is this
  file's own predecessor plus `ComplexAnalytic.refineDatumCrossProj_localisationHom`, which
  is where the arithmetic closes. The
  one-member file's analytified triangle uses the same tactic and plants nothing, and the
  difference is that all three definitions here take a proof argument, so simp needs a congruence
  lemma to traverse them. They belong to this module and are the benign kind;
  `Oka/Analytification/CrossMemberGlue.lean` carries the same shape, at the `congr_simp`
  companions of `ComplexAnalytic.localisationPresentationIsoOfMulEq` and
  `ComplexAnalytic.localisationPresentationIsoOfAlgEquivUnitMul`. **Named and not counted**, and
  the reason is sharper here than it is there: a numeral in this sentence counts *another
  module's* dump rows, so the edit that falsifies it is one nobody reading this file would open.
  **Recorded rather than removed**, because removing them means giving up `simp only … at` on a
  hypothesis that mentions a definition with a proof argument, and nothing here is worth that.
  **The arithmetic this makes**: three declarations and `Δdump = +5`, which is the figure to check
  a branch on this file by — an unexplained `Δdump` here is a planted equation lemma and not a
  rounding.
* **The other-file variant fired, and from `simp only` rather than from `rw`.** The first draft
  of `ComplexAnalytic.refineDatumGlueNe_comp` cancelled its two transports with
  `simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]`. That is green,
  and it plants **`ComplexAnalytic.refineCrossGlue.congr_simp` into this module** — an equation
  lemma for a definition `Oka/Analytification/CrossMemberGlue.lean` owns, which is exactly the
  variant that file's neighbour records and which nothing before this branch had produced under
  `Oka/`. Attributed by re-running the dump after the change and not inferred: the row is there
  with the `simp only` and gone without it. The cure is the explicit rewrite chain that proof now
  carries, which needs no congruence lemma because every step is a named rewrite at a named
  lemma. **`simp only` is subject to the same discipline as `rw` and neither file says so** — the
  tactic is not what plants the lemma, traversing a definition with a proof argument is.
* **`rw` can also fail to find a lemma that is visibly present.** After
  `simp only [Category.assoc]` the goal is right-associated, so the subterm
  `eqToHom … ≫ localisationHom …` does not occur — it occurs as
  `eqToHom … ≫ (localisationHom … ≫ localisationHom …)` — and rewriting with the two-factor lemma
  reports *did not find an occurrence of the pattern* against a goal that prints it. `reassoc_of%`
  on the same lemma is what closes it, at both orientations, and that is a Mathlib term elaborator
  and not a new lemma.

## The two branches do not analytify to the same shape, and the price on record was an estimate

`Oka/Analytification/CoverRefinement.lean` and the equal branch here each state a coherence
triangle and then its image under `ComplexAnalytic.analytificationFunctor`, and in both the image
comes out with `ComplexAnalytic.localisationProj` in every position but the glue. The recipe is
three lines — build the mapped equation with `congrArg`, normalise the *hypothesis* with
`CategoryTheory.Functor.map_comp` and
`ComplexAnalytic.analytificationFunctor_map_localisationPresHom`, discharge with `exact` — and
this file's `## What is not here` priced the unequal branch's version at *"one application of the
analytification functor"* on the strength of it.

**That was right about the functor application and wrong about the shape.** The rewrite fires on a
`ComplexAnalytic.localisationPresHom`, and every factor of `ComplexAnalytic.refineDatumGlueEq_comp`
is one *in the statement*. The factors of `ComplexAnalytic.refineDatumGlueNe_comp` are
`ComplexAnalytic.refineDatumCrossProj`, which is a `def`: `CategoryTheory.Functor.map_comp` splits
a composite and does not enter a definition, so after it there is nothing for the rewrite to see.
**Adding it to the `simp` set is not merely useless but detectably so** — `linter.unusedSimpArgs`
reports the argument as unused, which is how this was found rather than argued.

**And it stays unused one level deeper, which is the answer to the obvious objection.** Opening the
projection first with `ComplexAnalytic.refineDatumCrossProj_eq`, at both `h` and `h.symm`, does not
help: the linter reports the same argument on the same line, because
`ComplexAnalytic.refineCrossProj` underneath is a `def` too and the rewrite needs a
`ComplexAnalytic.localisationPresHom` in the *statement* and not in the unfolding. **The route is
worse than useless, and that is measured rather than asserted**: neither way of reassembling the
hypothesis afterwards closed, one failing to find its pattern and the other exceeding the default
`maxHeartbeats` of 200000 at the `exact`. So a reader who thinks of unfolding before reading on is
answered here.

So the two branches' analytified triangles are in different vocabularies, and no better choice of
tactic makes one look like the other: the difference is in what the statements are built from.
What closes the gap is a separate statement rather than a better proof —
`ComplexAnalytic.refineDatumCrossProj_analytification_localisationProj`, which does the rewrite
once on the `a`-side projection and which a consumer composes with. **The estimate was short by
that lemma and by the algebraic one under it**, and this section exists because the estimate stood
in a `## What is not here`, where a price is a claim like any other.

**The general-level mirror was measured and is deliberately not here.** The same statement one
level down — `ComplexAnalytic.refineCrossProj` followed down to the member, under the functor,
stated at `Oka/Analytification/CrossMemberGlue.lean`'s own variables — compiles by the same three
lines. It is left out because nothing would consume it: the datum-level pair above is what the
triangle beside them is stated against, and a lemma carrying an axiom guard is a claim that
something reads it.

**What did not change is the triangle's shape over the overlap.** It is still not over a member and
there is still no member-level version of it, for the reason
`ComplexAnalytic.refineDatumGlueNe_comp`'s own docstring gives: the two refined members lie over
`obj (σ a)` and `obj (σ b)` and a cover datum carries no morphism between those. The new projection
lemma is about one member and one side of the overlap and is not a step towards one that is not.

## Main definitions

- `ComplexAnalytic.refineDatumOverlap`: **the refined overlap with its cutting polynomial
  abstracted**, which is the presentation every statement below is between.
- `ComplexAnalytic.refineSwapGlue`: **the swap of two refining polynomials over one member.**
- `ComplexAnalytic.refineSwapGlueOfEq`: **the same across two members that are equal**, which is
  the transport the file exists to discharge.
- `ComplexAnalytic.refineDatumGlueEq`: **the `glue` of the refined datum where the two members are
  equal**, at the polynomial the datum's own `poly` field produces.
- `ComplexAnalytic.refineDatumCrossAlgEquiv`: **the algebra isomorphism a cross-member glue takes,
  read off the original datum's own glue.** It is what the unequal branch below feeds to
  `Oka/Analytification/CrossMemberGlue.lean`'s glue, and it is one application of
  `ComplexAnalytic.Presentation.algEquivOfIso` to the datum's `glue`.
- `ComplexAnalytic.RefineDatumCrossEq` and `ComplexAnalytic.RefineDatumCrossUnit`: **the two
  equations the caller's choice of `r` and `u` has to satisfy at an ordered pair**, named because
  the same lines occur in four signatures and because they are what a `hsymm` would be stated
  against.
- `ComplexAnalytic.refineDatumGlueNe`: **the `glue` of the refined datum where the two members are
  different**, the cross-member glue conjugated onto the datum's own overlaps.
- `ComplexAnalytic.refineDatumCrossProj`: **the refined overlap of two different members, read as
  a localisation of the original overlap**, which is what the triangle on that branch is over.
- `ComplexAnalytic.refineDatumGlue`: **the `glue` field**, the two branches under a case split on
  `σ a = σ b`.

## Main results

- `ComplexAnalytic.coverOverlap_refineDatumObj`: the abstraction above is the refined overlap, by
  `rfl`.
- `ComplexAnalytic.refineSwapMul`: the two orders of the product present the same localisation.
- `ComplexAnalytic.refineSwapGlue_eq` and `ComplexAnalytic.refineDatumGlueEq_eq`: **the two
  definitions unfolded, by `rfl`**, so that a proof can open them without planting an equation
  lemma. See the `rw` section above for what that costs when they are absent.
- `ComplexAnalytic.refineSwapGlue_symm` and `ComplexAnalytic.refineSwapGlueOfEq_symm`: **the swap
  is its own inverse**, which is the shape of the symmetry law a cover datum asks for.
- `ComplexAnalytic.refineSwapGlue_comp` and `ComplexAnalytic.refineSwapGlueOfEq_comp`: **the
  coherence triangle**, over the member on the far side. The transported one carries the
  transport of members as its last factor, since its two composites end over two different
  objects.
- `ComplexAnalytic.refineDatumGlueEq_symm`: **the symmetry law, at the datum.**
- `ComplexAnalytic.refineDatumGlueEq_comp` and
  `ComplexAnalytic.refineDatumGlueEq_analytification_comp`: **the coherence triangle at the
  datum**, and the analytified form of it. The second is the shape the two geometric laws consume.
- `ComplexAnalytic.refineDatumGlueEq_const`: **at constant `σ` the equal branch is the one-member
  file's glue**, conjugated by the two transports that file's overlap already needs — and it is
  `rfl`, which is what says this is the same construction and not a second one of the same shape.
- `ComplexAnalytic.refineDatumGlueNe_eq` and `ComplexAnalytic.refineDatumCrossProj_eq`: **the
  unequal branch and its projection unfolded, by `rfl`**, for the reason the two above are.
- `ComplexAnalytic.refineDatumCrossProj_localisationHom` and
  `ComplexAnalytic.refineDatumCrossProj_analytification_localisationProj`: **the projection to the
  original overlap, followed down to the member, is the datum's own two structure maps**, and the
  same under the functor. The second is the one place on this branch where the structure maps come
  out as the analytified projections, and the analytified triangle below is not.
- `ComplexAnalytic.isoOfAlgEquiv_symm_refineDatumCrossAlgEquiv`: **reading the algebra
  isomorphism back gives the datum's own `glue`**, by `rfl`. This is what lets the triangle below
  be stated about `glue` and not about an algebra isomorphism built from it.
- `ComplexAnalytic.refineDatumGlueNe_comp`: **the coherence triangle on the unequal branch**, over
  the *original overlap* rather than over a member, with the datum's `glue` as its right-hand
  factor. Its docstring records why the two conjugating transports are kept as isomorphisms.
- `ComplexAnalytic.refineDatumGlueNe_analytification_comp`: **the same, analytified.** Unlike
  `ComplexAnalytic.refineDatumGlueEq_analytification_comp` it keeps its two projections under the
  functor, for the reason the section below gives.
- `ComplexAnalytic.refineDatumGlue_of_eq` and `ComplexAnalytic.refineDatumGlue_of_ne`: **the two
  branches read back off the field**, which is `dif_pos` and `dif_neg`.
- `ComplexAnalytic.refineDatumGlue_const`: **at constant `σ` the field is the one-member file's
  glue, for every choice** — and, unlike the equal branch's version, it is *not* `rfl`; its
  docstring says which instance is in the way and what buying the `rfl` back would cost.
- `ComplexAnalytic.exists_refineDatumCross_of_isUnit`: **both equations have a solution as soon as
  the four polynomials they are stated at are units**, at a `q` and a `fam` the caller names. It
  is not `ComplexAnalytic.exists_refineDatumCross`, which produces `q` itself, and the two are not
  comparable.

## What is not here

* **Nothing *here* produces `r` or `u`, and something elsewhere now does.** The field below is a
  function of the caller's choice at every ordered pair and this file instantiates nothing;
  `ComplexAnalytic.exists_refineDatumCross` (`Oka/Analytification/CrossMemberChoice.lean`)
  produces `q`, `r`, `u` and both obligations at every ordered pair, from the input datum's
  symmetry law alone. **So the sentence this bullet used to carry — that nothing produces `r` or
  `u` — is retired, and so is the reading that went with it**: three existentials did not have to
  be instantiated, one did, and it is `ComplexAnalytic.exists_mk_rename_eq`.
  **What is not retired is what a choice buys.** Both obligations are equations between elements
  of the overlap algebras, and **no statement anywhere says the refined overlap a choice induces
  is the geometric one** — that is where `ComplexAnalytic.exists_localisationOpen_eq_rename` and
  `ComplexAnalytic.exists_comap_analytificationMap_eq_comap_localisationProj` would be spent, and
  neither is spent anywhere. So a `glue` field taking no arguments is one application away and a
  refined cover datum is not, and of the absence `Oka/Analytification/CrossMemberGlue.lean`
  records as *"nothing here produces `q`"* and `Oka/Analytification/CrossMemberDatum.lean` as
  *"nothing produces a `q` that makes this formula correct"* it is the algebraic half that is
  retired and not the geometric one those files' own bullets are about. (The two were quoted here
  jointly as *"nothing produces `q`"*, which is neither file's wording and makes the second the
  wider claim it is not: its bullet is about a `q` that satisfies one formula, not about
  producing a `q` at all.)
* **No `hsymm` here, and it is a theorem elsewhere rather than an open question.**
  `ComplexAnalytic.refineDatumGlueEq_symm` is the half of the law whose members are equal. **This
  bullet said of the other half that the two orders *"carry two independent choices of `r` and
  `u`, and whether they can be made compatibly is unproved in both directions"*, and that the law
  was therefore an obligation on a caller's choice rather than a theorem** — until
  `Oka/Analytification/RefineDatumSymm.lean` landed and proved it for two arbitrary independent
  choices. The compatibility is never needed. What that file spends and this one does not have is
  a monomorphism: with `ComplexAnalytic.refineDatumCrossProj` one,
  `ComplexAnalytic.refineDatumGlueNe_comp` below determines its isomorphism instead of merely
  constraining it, and everything follows from the triangle.
* **No `hrange` and no `hcocycle`**, in either branch. They are geometric where everything here is
  algebraic, and `Oka/Analytification/CoverRefinement.lean`'s corresponding section says what
  makes them cheap for one fixed member: that every refined member lies over it. **This bullet
  ended *"which is the sentence a general `σ` does not have"*, and a general `σ` has a replacement
  for it**: `ComplexAnalytic.refineDatumTransitionHom_localisationProj_of_ne`
  (`Oka/Analytification/RefineDatumTransition.lean`) says the refined transition lies over the
  original cover's own *transition*, and it is the two triangles below joined — nothing else went
  into it. It buys `hrange` at a triple whose three members are different, up to one containment
  in the caller's own open, and buys nothing for `hrange` at the other triples. **This bullet
  ended *"and buys nothing at the other triples and nothing for `hcocycle`"*, and the clause about
  `hcocycle` is false**: `ComplexAnalytic.refineDatumTriple_localisationProj_of_ne`
  (`Oka/Analytification/RefineDatumCocycle.lean`) is `ComplexAnalytic.coverTriple_fac` followed by
  exactly that lemma, and **four of the cocycle law's five shapes are read through it** — every one
  except the shape whose three members are equal, since at two members equal the remaining two
  edges are still unequal. What stays true is the clause about `hrange`, which is
  `Oka/Analytification/RefineDatumRange.lean`'s own finding.
* **No witness at a non-constant `σ` *here*, and the theorem above is not one.**
  `ComplexAnalytic.refineDatumGlue_const` says the general form reduces to a configuration the
  test files already exhibit, which is weaker than a witness and says nothing about `σ` ever
  being non-constant — the same gap `Oka/Analytification/CrossMemberDatum.lean` records for the
  `poly` field. **What this bullet said was missing outright now exists**, in
  `Oka/Analytification/RefineDatumWitness.lean`, and it is
  `ComplexAnalytic.exists_refineDatumCross_of_isUnit` above that supplies its `r` and `u` — so
  this file holds an input to the witness and still exhibits none of its own.
* **No scheme and no `admissible`**, as in the four files this one sits beside.
-/

open CategoryTheory MvPolynomial

universe u

namespace ComplexAnalytic

noncomputable section

variable {J B : Type u} (obj : J → Presentation.{u})

/-! ### The refined overlap, with its cutting polynomial free -/

/-- **The refined overlap of the `a`-th member with cutting polynomial `p`**: the localisation of
the `a`-th refined member `D(x)` at `p`, as a presentation.

Spelled this way because every statement below names it at two polynomials that are equal but not
identical, and an abbreviation that differs in one argument is what `rw` can move between. An
`abbrev` for the reason `ComplexAnalytic.refineDatumObj` is one. -/
abbrev refineDatumOverlap (i : J) (x : MvPolynomial (ULift.{u} (Fin (obj i).n)) ℂ)
    (p : MvPolynomial (ULift.{u} (Fin ((obj i).n + 1))) ℂ) : Presentation.{u} :=
  ⟨(obj i).n + 1 + 1, (obj i).k + 1 + 1,
    localisationPresentation.{u} (localisationPresentation.{u} (obj i).g x) p⟩

variable (σ : B → J) (fam : ∀ b : B, MvPolynomial (ULift.{u} (Fin (obj (σ b)).n)) ℂ)

/-- **The abstraction is the refined overlap**, for any family of cutting polynomials and on the
nose. This is what lets the statements below be about the abbreviation rather than about a nested
structure literal. -/
theorem coverOverlap_refineDatumObj
    (p : ∀ a : B, B → MvPolynomial (ULift.{u} (Fin ((obj (σ a)).n + 1))) ℂ) (a b : B) :
    coverOverlap.{u} (refineDatumObj.{u} obj σ fam) p a b =
      refineDatumOverlap.{u} obj (σ a) (fam a) (p a b) :=
  rfl

/-! ### The swap over one member, and the transport of it -/

/-- **The two orders of the product present the same localisation.** Named rather than inlined
because the two proofs below unfold `ComplexAnalytic.refineSwapGlue` and have to spell its
transport; an anonymous `by rw [mul_comm]` cannot be written back down. -/
theorem refineSwapMul (i : J) (x y : MvPolynomial (ULift.{u} (Fin (obj i).n)) ℂ) :
    (⟨(obj i).n + 1, (obj i).k + 1, localisationPresentation.{u} (obj i).g (y * x)⟩ :
        Presentation.{u}) =
      ⟨(obj i).n + 1, (obj i).k + 1, localisationPresentation.{u} (obj i).g (x * y)⟩ := by
  rw [mul_comm]

/-- **The swap of two refining polynomials over one member**: the overlap cut out of `D(x)` by `y`
and the overlap cut out of `D(y)` by `x` are the same localisation, at the product read in either
order.

`Oka/Analytification/CoverRefinement.lean`'s glue is this at the two values of a family; stating
it at two bare polynomials is what makes the transport below a `subst`, since the equation between
members is then the statement's only dependency. -/
def refineSwapGlue (i : J) (x y : MvPolynomial (ULift.{u} (Fin (obj i).n)) ℂ) :
    refineDatumOverlap.{u} obj i x (rename (localisationIncl.{u} (obj i).n) y) ≅
      refineDatumOverlap.{u} obj i y (rename (localisationIncl.{u} (obj i).n) x) :=
  localisationPresentationIsoMul.{u} (obj i).g x y ≪≫
    eqToIso (refineSwapMul.{u} obj i x y) ≪≫
      (localisationPresentationIsoMul.{u} (obj i).g y x).symm

/-- **The swap, unfolded**, by `rfl`.

It exists so that the two proofs below can rewrite with a declaration of this file rather than
with the *name* of a definition: `rw [refineSwapGlue]` plants
`ComplexAnalytic.refineSwapGlue.eq_1` in this module, which
`Oka/Analytification/CrossMemberDatum.lean`'s discipline section is about and which the
declaration dump is what shows. -/
theorem refineSwapGlue_eq (i : J) (x y : MvPolynomial (ULift.{u} (Fin (obj i).n)) ℂ) :
    refineSwapGlue.{u} obj i x y =
      localisationPresentationIsoMul.{u} (obj i).g x y ≪≫
        eqToIso (refineSwapMul.{u} obj i x y) ≪≫
          (localisationPresentationIsoMul.{u} (obj i).g y x).symm :=
  rfl

/-- **The swap is its own inverse.** The two orders differ by the transport along `mul_comm`, and
that is the only asymmetry in the definition. -/
theorem refineSwapGlue_symm (i : J) (x y : MvPolynomial (ULift.{u} (Fin (obj i).n)) ℂ) :
    refineSwapGlue.{u} obj i y x = (refineSwapGlue.{u} obj i x y).symm := by
  rw [refineSwapGlue_eq, refineSwapGlue_eq, Iso.trans_symm, Iso.trans_symm, Iso.symm_symm_eq,
    Iso.trans_assoc, eqToIso_symm']

/-- **The coherence triangle over the member.** Crossing to the other description of the overlap
and then going down to the member is going down directly, which is what says the swap is the
identification of two parts of one member and not merely an isomorphism of the right type. -/
theorem refineSwapGlue_comp (i : J) (x y : MvPolynomial (ULift.{u} (Fin (obj i).n)) ℂ) :
    (refineSwapGlue.{u} obj i x y).hom ≫
        localisationHom.{u} (localisationPresentation.{u} (obj i).g y)
            (rename (localisationIncl.{u} (obj i).n) x) ≫ localisationHom.{u} (obj i).g y =
      localisationHom.{u} (localisationPresentation.{u} (obj i).g x)
          (rename (localisationIncl.{u} (obj i).n) y) ≫ localisationHom.{u} (obj i).g x := by
  rw [← localisationPresentationIsoMul_hom_comp.{u} (obj i).g x y,
    ← localisationPresentationIsoMul_hom_comp.{u} (obj i).g y x, refineSwapGlue_eq]
  simp only [Iso.trans_hom, eqToIso.hom, Category.assoc, Iso.symm_hom]
  rw [show (localisationPresentationIsoMul.{u} (obj i).g y x).inv ≫
      (localisationPresentationIsoMul.{u} (obj i).g y x).hom ≫
        localisationHom.{u} (obj i).g (x * y) = localisationHom.{u} (obj i).g (x * y) from
    (localisationPresentationIsoMul.{u} (obj i).g y x).inv_hom_id_assoc _]
  exact congrArg _ (eqToHom_localisationHom.{u} (obj i).g (mul_comm y x))

/-- **The swap across two members that are equal.**

This is the transport `Oka/Analytification/CrossMemberDatum.lean` prices and does not discharge,
and `subst h` is the whole of it — available because `i` and `j` are bound here, where in the
datum below they are `σ a` and `σ b` and neither is a variable. -/
def refineSwapGlueOfEq {i j : J} (h : i = j)
    (x : MvPolynomial (ULift.{u} (Fin (obj i).n)) ℂ)
    (y : MvPolynomial (ULift.{u} (Fin (obj j).n)) ℂ) :
    refineDatumOverlap.{u} obj i x (rename (localisationIncl.{u} (obj i).n) (h ▸ y)) ≅
      refineDatumOverlap.{u} obj j y (rename (localisationIncl.{u} (obj j).n) (h ▸ x)) := by
  subst h
  exact refineSwapGlue.{u} obj i x y

/-- **The transported swap is its own inverse.** -/
theorem refineSwapGlueOfEq_symm {i j : J} (h : i = j)
    (x : MvPolynomial (ULift.{u} (Fin (obj i).n)) ℂ)
    (y : MvPolynomial (ULift.{u} (Fin (obj j).n)) ℂ) :
    refineSwapGlueOfEq.{u} obj h.symm y x = (refineSwapGlueOfEq.{u} obj h x y).symm := by
  subst h
  exact refineSwapGlue_symm.{u} obj i x y

/-- **The coherence triangle of the transported swap.**

Its two composites end over `obj j` and over `obj i`, which are equal and not identical, so the
statement carries the transport of members as its last factor. That factor is `eqToHom` of
`congrArg` and is the identity as soon as `h` is `rfl`, which is what the proof uses. -/
theorem refineSwapGlueOfEq_comp {i j : J} (h : i = j)
    (x : MvPolynomial (ULift.{u} (Fin (obj i).n)) ℂ)
    (y : MvPolynomial (ULift.{u} (Fin (obj j).n)) ℂ) :
    (refineSwapGlueOfEq.{u} obj h x y).hom ≫
        localisationHom.{u} (localisationPresentation.{u} (obj j).g y)
            (rename (localisationIncl.{u} (obj j).n) (h ▸ x)) ≫ localisationHom.{u} (obj j).g y =
      localisationHom.{u} (localisationPresentation.{u} (obj i).g x)
          (rename (localisationIncl.{u} (obj i).n) (h ▸ y)) ≫
        localisationHom.{u} (obj i).g x ≫ eqToHom (congrArg obj h) := by
  subst h
  rw [eqToHom_refl, Category.comp_id]
  exact refineSwapGlue_comp.{u} obj i x y

/-! ### The field, at the pairs whose members are equal -/

variable (poly : ∀ i : J, J → MvPolynomial (ULift.{u} (Fin (obj i).n)) ℂ)
  (q : ∀ a : B, B → MvPolynomial (ULift.{u} (Fin (obj (σ a)).n)) ℂ)

/-- **The `glue` of the refined cover datum, where the two refined members lie over one member.**

The transported swap, conjugated by the two equations that turn the datum's own `poly` field into
the polynomial each side of it is stated at. Nothing else enters: the diagonal normalisation is
already inside that field, and the original datum's `glue` is not read at all in this branch —
which is the sentence `Oka/Analytification/CrossMemberGlue.lean` uses to say why the cross-member
case is the one that is different. -/
def refineDatumGlueEq {a b : B} (h : σ a = σ b) :
    coverOverlap.{u} (refineDatumObj.{u} obj σ fam) (refineDatumPoly.{u} obj poly σ fam q) a b ≅
      coverOverlap.{u} (refineDatumObj.{u} obj σ fam) (refineDatumPoly.{u} obj poly σ fam q) b a :=
  eqToIso (congrArg (refineDatumOverlap.{u} obj (σ a) (fam a))
      (refineDatumPoly_of_eq.{u} obj poly σ fam q h)) ≪≫
    refineSwapGlueOfEq.{u} obj h (fam a) (fam b) ≪≫
      eqToIso (congrArg (refineDatumOverlap.{u} obj (σ b) (fam b))
        (refineDatumPoly_of_eq.{u} obj poly σ fam q h.symm)).symm

/-- **The field, unfolded**, by `rfl`, and for the reason
`ComplexAnalytic.refineSwapGlue_eq` exists. -/
theorem refineDatumGlueEq_eq {a b : B} (h : σ a = σ b) :
    refineDatumGlueEq.{u} obj σ fam poly q h =
      eqToIso (congrArg (refineDatumOverlap.{u} obj (σ a) (fam a))
          (refineDatumPoly_of_eq.{u} obj poly σ fam q h)) ≪≫
        refineSwapGlueOfEq.{u} obj h (fam a) (fam b) ≪≫
          eqToIso (congrArg (refineDatumOverlap.{u} obj (σ b) (fam b))
            (refineDatumPoly_of_eq.{u} obj poly σ fam q h.symm)).symm :=
  rfl

/-- **The symmetry law, on this branch.** A cover datum asks for it at every ordered pair; this is
the half of that quantifier whose two members are equal. -/
theorem refineDatumGlueEq_symm {a b : B} (h : σ a = σ b) :
    refineDatumGlueEq.{u} obj σ fam poly q h.symm =
      (refineDatumGlueEq.{u} obj σ fam poly q h).symm := by
  rw [refineDatumGlueEq_eq, refineDatumGlueEq_eq, Iso.trans_symm, Iso.trans_symm,
    Iso.trans_assoc, eqToIso_symm', eqToIso_symm', refineSwapGlueOfEq_symm]

/-- **The coherence triangle at the datum**, with the transport of members as its last factor.

The two conjugating transports cancel against the structure maps, one at each orientation, and
that is the whole proof — but the cancellation lemma has to be reassociated first, because the
goal is right-associated and the two-factor form of the lemma does not occur in it. -/
theorem refineDatumGlueEq_comp {a b : B} (h : σ a = σ b) :
    (refineDatumGlueEq.{u} obj σ fam poly q h).hom ≫
        localisationHom.{u} (refineDatumObj.{u} obj σ fam b).g
            (refineDatumPoly.{u} obj poly σ fam q b a) ≫
          localisationHom.{u} (obj (σ b)).g (fam b) =
      localisationHom.{u} (refineDatumObj.{u} obj σ fam a).g
          (refineDatumPoly.{u} obj poly σ fam q a b) ≫
        localisationHom.{u} (obj (σ a)).g (fam a) ≫ eqToHom (congrArg obj h) := by
  rw [refineDatumGlueEq_eq]
  simp only [Iso.trans_hom, eqToIso.hom, Category.assoc]
  rw [reassoc_of% (eqToHom_localisationHom.{u} (localisationPresentation.{u} (obj (σ b)).g (fam b))
      (refineDatumPoly_of_eq.{u} obj poly σ fam q h.symm).symm),
    ← reassoc_of% (eqToHom_localisationHom.{u}
      (localisationPresentation.{u} (obj (σ a)).g (fam a))
      (refineDatumPoly_of_eq.{u} obj poly σ fam q h))]
  exact congrArg (eqToHom (congrArg (refineDatumOverlap.{u} obj (σ a) (fam a))
    (refineDatumPoly_of_eq.{u} obj poly σ fam q h)) ≫ ·)
      (refineSwapGlueOfEq_comp.{u} obj h (fam a) (fam b))

/-- **The coherence triangle, analytified**, with the structure maps read as
`ComplexAnalytic.localisationProj`. This is the form the two geometric laws consume, and it is the
previous statement under the functor with nothing added. -/
theorem refineDatumGlueEq_analytification_comp {a b : B} (h : σ a = σ b) :
    analytificationFunctor.{u}.map (refineDatumGlueEq.{u} obj σ fam poly q h).hom ≫
        localisationProj.{u} (refineDatumObj.{u} obj σ fam b).g
            (refineDatumPoly.{u} obj poly σ fam q b a) ≫
          localisationProj.{u} (obj (σ b)).g (fam b) =
      localisationProj.{u} (refineDatumObj.{u} obj σ fam a).g
          (refineDatumPoly.{u} obj poly σ fam q a b) ≫
        localisationProj.{u} (obj (σ a)).g (fam a) ≫
          analytificationFunctor.{u}.map (eqToHom (congrArg obj h)) := by
  have e := congrArg (analytificationFunctor.{u}.map)
    (refineDatumGlueEq_comp.{u} obj σ fam poly q h)
  simp only [Functor.map_comp, analytificationFunctor_map_localisationPresHom] at e
  exact e

/-- **At constant `σ` the field is the one-member file's glue**, conjugated by the two transports
that identify the two descriptions of the refined overlap.

`rfl`, which is the statement worth having: the general construction does not merely agree with
the one-member one, it *is* it once the polynomials are identified, so everything
`Oka/Analytification/CoverRefinement.lean` proves about that glue is available here at constant
`σ` with no further work. -/
theorem refineDatumGlueEq_const (i : J)
    (fam' : B → MvPolynomial (ULift.{u} (Fin (obj i).n)) ℂ)
    (q' : ∀ _ : B, B → MvPolynomial (ULift.{u} (Fin (obj i).n)) ℂ) (a b : B) :
    refineDatumGlueEq.{u} obj (fun _ ↦ i) fam' poly q'
        (rfl : (fun _ ↦ i) a = (fun _ ↦ i) b) =
      eqToIso (coverOverlap_refineDatumPoly_const.{u} obj poly i fam' q' a b) ≪≫
        refineGlue.{u} (obj i).g fam' a b ≪≫
          eqToIso (coverOverlap_refineDatumPoly_const.{u} obj poly i fam' q' b a).symm :=
  rfl

/-! ### What the other branch would take, and where it comes from -/

/-- **The algebra isomorphism a cross-member glue takes, read off the original datum's own glue.**

`Oka/Analytification/CrossMemberGlue.lean`'s glue asks for an isomorphism of the two *presented
algebras* of the original overlap, where a cover datum carries an isomorphism of the two
*presentations*; the two are interchangeable and the bridge is on `master`. Recorded here because
the unequal branch's remaining inputs are then exactly the ones about the caller's extra factor,
and this is the one that is not.

`ComplexAnalytic.refineDatumGlueNe` below is what uses it, and
`ComplexAnalytic.isoOfAlgEquiv_symm_refineDatumCrossAlgEquiv` is the round trip that lets the
coherence triangle on that branch be stated about `glue` itself. -/
def refineDatumCrossAlgEquiv
    (glue : ∀ i j : J, coverOverlap.{u} obj poly i j ≅ coverOverlap.{u} obj poly j i) (i j : J) :
    PresentedAlgebra.{u} ((obj i).n + 1) ((obj i).k + 1)
        (localisationPresentation.{u} (obj i).g (poly i j)) ≃ₐ[ℂ]
      PresentedAlgebra.{u} ((obj j).n + 1) ((obj j).k + 1)
        (localisationPresentation.{u} (obj j).g (poly j i)) :=
  (Presentation.algEquivOfIso.{u} (glue i j)).symm

/-! ### The field, at the pairs whose members are different -/

variable (glue : ∀ i j : J, coverOverlap.{u} obj poly i j ≅ coverOverlap.{u} obj poly j i)

/-- **The equation `ComplexAnalytic.refineCrossGlue` asks of the caller's `r` at the ordered pair
`(a, b)`**: the algebra isomorphism the original datum's `glue` gives carries the class of
`q a b * fam a` to the class of `r`.

Named because the same six lines occur in three signatures below, and `abbrev` so that a caller
may pass one of these where `ComplexAnalytic.refineCrossGlue` asks for the equation itself. -/
abbrev RefineDatumCrossEq (a b : B)
    (r : MvPolynomial (ULift.{u} (Fin ((obj (σ b)).n + 1))) ℂ) : Prop :=
  refineDatumCrossAlgEquiv.{u} obj poly glue (σ a) (σ b)
      (Ideal.Quotient.mk (presentationIdeal.{u} (localisationPresentation.{u} (obj (σ a)).g
        (poly (σ a) (σ b)))) (rename (localisationIncl.{u} (obj (σ a)).n) (q a b * fam a))) =
    Ideal.Quotient.mk (presentationIdeal.{u} (localisationPresentation.{u} (obj (σ b)).g
      (poly (σ b) (σ a)))) r

/-- **The equation `ComplexAnalytic.refineCrossGlue` asks of the caller's unit `u`**: the class of
`q b a * fam b` is `u` times the class of `r`.

The two agree only up to a unit because `ComplexAnalytic.exists_mk_rename_eq` produces one, and
that is the whole reason the third step of the cross-member chain exists. -/
abbrev RefineDatumCrossUnit (a b : B)
    (r : MvPolynomial (ULift.{u} (Fin ((obj (σ b)).n + 1))) ℂ)
    (u : (PresentedAlgebra.{u} ((obj (σ b)).n + 1) ((obj (σ b)).k + 1)
      (localisationPresentation.{u} (obj (σ b)).g (poly (σ b) (σ a))))ˣ) : Prop :=
  Ideal.Quotient.mk (presentationIdeal.{u} (localisationPresentation.{u} (obj (σ b)).g
      (poly (σ b) (σ a)))) (rename (localisationIncl.{u} (obj (σ b)).n) (q b a * fam b)) =
    (u : PresentedAlgebra.{u} ((obj (σ b)).n + 1) ((obj (σ b)).k + 1)
        (localisationPresentation.{u} (obj (σ b)).g (poly (σ b) (σ a)))) *
      Ideal.Quotient.mk (presentationIdeal.{u} (localisationPresentation.{u} (obj (σ b)).g
        (poly (σ b) (σ a)))) r

/-! ### When a caller can meet both equations at once -/

/-- **Both equations have a solution as soon as the four polynomials they are stated at are
units**, and then the caller owes nothing further at that ordered pair.

`r` is a preimage of the transported class under `Ideal.Quotient.mk`, which is surjective, so
`ComplexAnalytic.RefineDatumCrossEq` holds **by construction and says nothing**; all the content
is in `ComplexAnalytic.RefineDatumCrossUnit`, which then relates two elements that are both units
— the left-hand side by hypothesis, the right-hand side because an `AlgEquiv` carries a unit to a
unit — and `u` is their ratio.

**This is not `ComplexAnalytic.exists_refineDatumCross`**, which produces `q` as well and whose
content is that the factor's class is an *associate* of the transported one. Here `q` is the
caller's and the hypotheses are about it; the two are not comparable, and a caller who has this
one does not need that one. `Oka/Analytification/RefineDatumWitness.lean` is what it was written
for.

**The hypotheses are on the four factors separately rather than on the two products
`q a b * fam a` and `q b a * fam b`.** The product form is what the proof uses and is the more
natural statement, but it does not instantiate: at a refining family given as `fun _ ↦ 1` the
`1` carries an index type the caller's `σ` has not been reduced in, and `simp only [mul_one]`
reports the argument unused. Splitting costs two `rw [map_mul, map_mul]` here and removes the
problem at every call site. -/
theorem exists_refineDatumCross_of_isUnit (a b : B)
    (hqa : IsUnit (Ideal.Quotient.mk (presentationIdeal.{u} (localisationPresentation.{u}
      (obj (σ a)).g (poly (σ a) (σ b))))
      (MvPolynomial.rename (localisationIncl.{u} (obj (σ a)).n) (q a b))))
    (hfa : IsUnit (Ideal.Quotient.mk (presentationIdeal.{u} (localisationPresentation.{u}
      (obj (σ a)).g (poly (σ a) (σ b))))
      (MvPolynomial.rename (localisationIncl.{u} (obj (σ a)).n) (fam a))))
    (hqb : IsUnit (Ideal.Quotient.mk (presentationIdeal.{u} (localisationPresentation.{u}
      (obj (σ b)).g (poly (σ b) (σ a))))
      (MvPolynomial.rename (localisationIncl.{u} (obj (σ b)).n) (q b a))))
    (hfb : IsUnit (Ideal.Quotient.mk (presentationIdeal.{u} (localisationPresentation.{u}
      (obj (σ b)).g (poly (σ b) (σ a))))
      (MvPolynomial.rename (localisationIncl.{u} (obj (σ b)).n) (fam b)))) :
    ∃ (r : MvPolynomial (ULift.{u} (Fin ((obj (σ b)).n + 1))) ℂ)
      (u : (PresentedAlgebra.{u} ((obj (σ b)).n + 1) ((obj (σ b)).k + 1)
        (localisationPresentation.{u} (obj (σ b)).g (poly (σ b) (σ a))))ˣ),
      RefineDatumCrossEq.{u} obj σ fam poly q glue a b r ∧
        RefineDatumCrossUnit.{u} obj σ fam poly q a b r u := by
  have ha : IsUnit (Ideal.Quotient.mk (presentationIdeal.{u} (localisationPresentation.{u}
      (obj (σ a)).g (poly (σ a) (σ b))))
      (MvPolynomial.rename (localisationIncl.{u} (obj (σ a)).n) (q a b * fam a))) := by
    rw [map_mul, map_mul]; exact hqa.mul hfa
  have hb : IsUnit (Ideal.Quotient.mk (presentationIdeal.{u} (localisationPresentation.{u}
      (obj (σ b)).g (poly (σ b) (σ a))))
      (MvPolynomial.rename (localisationIncl.{u} (obj (σ b)).n) (q b a * fam b))) := by
    rw [map_mul, map_mul]; exact hqb.mul hfb
  set L := refineDatumCrossAlgEquiv.{u} obj poly glue (σ a) (σ b)
    (Ideal.Quotient.mk (presentationIdeal.{u} (localisationPresentation.{u} (obj (σ a)).g
      (poly (σ a) (σ b)))) (MvPolynomial.rename (localisationIncl.{u} (obj (σ a)).n)
        (q a b * fam a))) with hL
  refine ⟨Function.surjInv (Ideal.Quotient.mk_surjective (I :=
    presentationIdeal.{u} (localisationPresentation.{u} (obj (σ b)).g (poly (σ b) (σ a))))) L, ?_⟩
  have hmk : Ideal.Quotient.mk (presentationIdeal.{u} (localisationPresentation.{u}
      (obj (σ b)).g (poly (σ b) (σ a)))) (Function.surjInv (Ideal.Quotient.mk_surjective (I :=
        presentationIdeal.{u} (localisationPresentation.{u} (obj (σ b)).g (poly (σ b) (σ a))))) L)
      = L := Function.surjInv_eq _ _
  obtain ⟨v, hv⟩ : IsUnit L :=
    hL ▸ ha.map (refineDatumCrossAlgEquiv.{u} obj poly glue (σ a) (σ b))
  obtain ⟨w, hw⟩ := hb
  refine ⟨w * v⁻¹, hmk.symm, ?_⟩
  change Ideal.Quotient.mk _ _ = _
  rw [hmk, ← hv, Units.val_mul, mul_assoc, Units.inv_mul, mul_one, hw]

/-- **The `glue` of the refined cover datum, where the two refined members lie over two different
members.**

`Oka/Analytification/CrossMemberGlue.lean`'s cross-member glue, conjugated by the two equations
that turn the datum's own `poly` field into the polynomial each side of it is stated at — the
**same three-factor shape** as `ComplexAnalytic.refineDatumGlueEq`, with
`ComplexAnalytic.refineSwapGlueOfEq` replaced by `ComplexAnalytic.refineCrossGlue` and
`ComplexAnalytic.refineDatumPoly_of_eq` by `ComplexAnalytic.refineDatumPoly_of_ne`. The middle
factor is where the original datum's own `glue` is read, through
`ComplexAnalytic.refineDatumCrossAlgEquiv` above, and it is read exactly once.

**`r`, `u` and the two equations are the caller's**, as `q` already is in
`ComplexAnalytic.refineDatumPoly`; nothing here produces them, and this file's `## What is not
here` says what that defers and what it does not.

The two conjugating transports are `CategoryTheory.eqToIso` and not `CategoryTheory.eqToHom`
for a measured reason, recorded at `ComplexAnalytic.refineDatumGlueNe_comp`. -/
def refineDatumGlueNe {a b : B} (h : σ a ≠ σ b)
    (r : MvPolynomial (ULift.{u} (Fin ((obj (σ b)).n + 1))) ℂ)
    (he : RefineDatumCrossEq.{u} obj σ fam poly q glue a b r)
    (u : (PresentedAlgebra.{u} ((obj (σ b)).n + 1) ((obj (σ b)).k + 1)
      (localisationPresentation.{u} (obj (σ b)).g (poly (σ b) (σ a))))ˣ)
    (hu : RefineDatumCrossUnit.{u} obj σ fam poly q a b r u) :
    coverOverlap.{u} (refineDatumObj.{u} obj σ fam) (refineDatumPoly.{u} obj poly σ fam q) a b ≅
      coverOverlap.{u} (refineDatumObj.{u} obj σ fam) (refineDatumPoly.{u} obj poly σ fam q) b a :=
  eqToIso (congrArg (refineDatumOverlap.{u} obj (σ a) (fam a))
      (refineDatumPoly_of_ne.{u} obj poly σ fam q h)) ≪≫
    refineCrossGlue.{u} (obj (σ a)).g (obj (σ b)).g (poly (σ a) (σ b)) (fam a) (q a b)
        (poly (σ b) (σ a)) (fam b) (q b a) r
        (refineDatumCrossAlgEquiv.{u} obj poly glue (σ a) (σ b)) he u hu ≪≫
      (eqToIso (congrArg (refineDatumOverlap.{u} obj (σ b) (fam b))
        (refineDatumPoly_of_ne.{u} obj poly σ fam q h.symm))).symm

/-- **The unequal branch, unfolded**, by `rfl`, and for the reason
`ComplexAnalytic.refineDatumGlueEq_eq` exists: the triangle below has to open it, and a `rw` at
the definition would plant an equation lemma under its own name. -/
theorem refineDatumGlueNe_eq {a b : B} (h : σ a ≠ σ b)
    (r : MvPolynomial (ULift.{u} (Fin ((obj (σ b)).n + 1))) ℂ)
    (he : RefineDatumCrossEq.{u} obj σ fam poly q glue a b r)
    (u : (PresentedAlgebra.{u} ((obj (σ b)).n + 1) ((obj (σ b)).k + 1)
      (localisationPresentation.{u} (obj (σ b)).g (poly (σ b) (σ a))))ˣ)
    (hu : RefineDatumCrossUnit.{u} obj σ fam poly q a b r u) :
    refineDatumGlueNe.{u} obj σ fam poly q glue h r he u hu =
      eqToIso (congrArg (refineDatumOverlap.{u} obj (σ a) (fam a))
          (refineDatumPoly_of_ne.{u} obj poly σ fam q h)) ≪≫
        refineCrossGlue.{u} (obj (σ a)).g (obj (σ b)).g (poly (σ a) (σ b)) (fam a) (q a b)
            (poly (σ b) (σ a)) (fam b) (q b a) r
            (refineDatumCrossAlgEquiv.{u} obj poly glue (σ a) (σ b)) he u hu ≪≫
          (eqToIso (congrArg (refineDatumOverlap.{u} obj (σ b) (fam b))
            (refineDatumPoly_of_ne.{u} obj poly σ fam q h.symm))).symm :=
  rfl

/-- **The refined overlap of two different members, read as a localisation of the original
overlap.**

`ComplexAnalytic.refineCrossProj` at the datum's own cutting polynomial, which is the composite
the triangle below is stated over. There is no member-level version of it and that is not an
oversight: the two refined members lie over `obj (σ a)` and `obj (σ b)` and a cover datum contains
no morphism between those. -/
def refineDatumCrossProj {a b : B} (h : σ a ≠ σ b) :
    coverOverlap.{u} (refineDatumObj.{u} obj σ fam) (refineDatumPoly.{u} obj poly σ fam q) a b ⟶
      coverOverlap.{u} obj poly (σ a) (σ b) :=
  (eqToIso (congrArg (refineDatumOverlap.{u} obj (σ a) (fam a))
      (refineDatumPoly_of_ne.{u} obj poly σ fam q h))).hom ≫
    refineCrossProj.{u} (obj (σ a)).g (poly (σ a) (σ b)) (fam a) (q a b)

/-- **The projection, unfolded**, by `rfl`, for the reason above. -/
theorem refineDatumCrossProj_eq {a b : B} (h : σ a ≠ σ b) :
    refineDatumCrossProj.{u} obj σ fam poly q h =
      (eqToIso (congrArg (refineDatumOverlap.{u} obj (σ a) (fam a))
          (refineDatumPoly_of_ne.{u} obj poly σ fam q h))).hom ≫
        refineCrossProj.{u} (obj (σ a)).g (poly (σ a) (σ b)) (fam a) (q a b) :=
  rfl

/-- **The projection to the original overlap, followed down to the member, is the datum's own two
structure maps.**

`ComplexAnalytic.refineCrossProj_localisationHom` at the datum's own cutting polynomial, with the
transport cancelled against the outer structure map. So reading the `a`-side of a cross-member
refined overlap over the *original overlap* rather than over the member loses nothing: a consumer
that wants it over `obj (σ a)` composes this with the triangle below.

**This is not the member-level triangle the paragraph above says does not exist, and it is not a
step towards one.** That absence is about *two* members and a morphism between them that a cover
datum does not carry; this statement mentions one member and says where the `a`-side goes. Nothing
here says anything about the `b`-side, and there is no analogue of it that could.

The transport cancels the way `ComplexAnalytic.refineDatumGlueEq_comp`'s do, by
`ComplexAnalytic.eqToHom_localisationHom` reassociated. The extra step is
`CategoryTheory.eqToIso.hom`, because `ComplexAnalytic.refineDatumCrossProj` carries its transport
as an isomorphism and the cancellation lemma is stated at the morphism. -/
theorem refineDatumCrossProj_localisationHom {a b : B} (h : σ a ≠ σ b) :
    refineDatumCrossProj.{u} obj σ fam poly q h ≫
        localisationHom.{u} (obj (σ a)).g (poly (σ a) (σ b)) =
      localisationHom.{u} (refineDatumObj.{u} obj σ fam a).g
          (refineDatumPoly.{u} obj poly σ fam q a b) ≫
        localisationHom.{u} (obj (σ a)).g (fam a) := by
  rw [refineDatumCrossProj_eq, eqToIso.hom, Category.assoc, refineCrossProj_localisationHom,
    ← reassoc_of% (eqToHom_localisationHom.{u}
      (localisationPresentation.{u} (obj (σ a)).g (fam a))
      (refineDatumPoly_of_ne.{u} obj poly σ fam q h))]

/-- **The same, analytified**, with the structure maps read as `ComplexAnalytic.localisationProj`.
The previous statement under the functor with nothing added.

**This is the statement the analytified triangle below does not give**, and the reason is the
difference between the two branches. Every factor of `ComplexAnalytic.refineDatumGlueEq_comp` is a
`ComplexAnalytic.localisationHom` *in the statement*, so its image under the functor rewrites into
`ComplexAnalytic.localisationProj` everywhere but the glue. The factors of
`ComplexAnalytic.refineDatumGlueNe_comp` are `ComplexAnalytic.refineDatumCrossProj`, and that is a
`def`: `CategoryTheory.Functor.map_comp` cannot enter one, so nothing in the mapped triangle is a
structure map that the rewrite can see. This is where that rewrite happens instead, once, on the
`a`-side projection, and it is what a consumer composes with to get past the functor. -/
theorem refineDatumCrossProj_analytification_localisationProj {a b : B} (h : σ a ≠ σ b) :
    analytificationFunctor.{u}.map (refineDatumCrossProj.{u} obj σ fam poly q h) ≫
        localisationProj.{u} (obj (σ a)).g (poly (σ a) (σ b)) =
      localisationProj.{u} (refineDatumObj.{u} obj σ fam a).g
          (refineDatumPoly.{u} obj poly σ fam q a b) ≫
        localisationProj.{u} (obj (σ a)).g (fam a) := by
  have e := congrArg (analytificationFunctor.{u}.map)
    (refineDatumCrossProj_localisationHom.{u} obj σ fam poly q h)
  simp only [Functor.map_comp, analytificationFunctor_map_localisationPresHom] at e
  exact e

/-- **Reading the algebra isomorphism back gives the datum's own `glue`.**

`ComplexAnalytic.refineDatumCrossAlgEquiv` is `ComplexAnalytic.Presentation.algEquivOfIso` of the
glue, inverted for the direction `ComplexAnalytic.PresHom` runs in; the cross-member triangle's
right-hand factor is `ComplexAnalytic.Presentation.isoOfAlgEquiv` of the inverse of that, and the
two inversions cancel. By `rfl`, which is what lets the triangle below be stated about `glue`
itself rather than about an algebra isomorphism built from it. -/
theorem isoOfAlgEquiv_symm_refineDatumCrossAlgEquiv (i j : J) :
    Presentation.isoOfAlgEquiv.{u} (refineDatumCrossAlgEquiv.{u} obj poly glue i j).symm =
      glue i j :=
  rfl

/-- **The coherence triangle on this branch, and it is over the *original overlap*.**

`ComplexAnalytic.refineDatumGlueEq_comp` is over the member, with the transport of members as its
last factor. **There is no such statement here and its absence is not a weakening**: the two
refined members lie over `obj (σ a)` and `obj (σ b)`, and a cover datum contains no morphism
between those — its `glue` relates the two *overlaps* and nothing relates the two members. So this
is over the original overlap, exactly as `Oka/Analytification/CrossMemberGlue.lean`'s `## What the
triangle is over, and it is not the members` sets out, and the right-hand factor is the datum's
own `glue`.

**Why the two transports are `CategoryTheory.eqToIso` and not `CategoryTheory.eqToHom`, and it is
measured.** Written with `eqToHom` the proof has to cancel `eqToHom h.symm ≫ eqToHom h` against
each other, and `CategoryTheory.eqToHom_refl` on these presentations does not elaborate:
`rw [eqToHom_trans_assoc, eqToHom_refl]` gives `(deterministic) timeout at isDefEq, maximum number
of heartbeats (200000)` at the second rewrite, because the objects are nested
`ComplexAnalytic.localisationPresentation` structures and the lemma's object argument is a
metavariable read off the type. Kept as isomorphisms, the same cancellation is
`CategoryTheory.Iso.inv_hom_id_assoc` at an isomorphism the rewrite already has in hand, and it is
instant. Both spellings are the same morphism (`CategoryTheory.eqToIso.hom`); only one of them
elaborates here. -/
theorem refineDatumGlueNe_comp {a b : B} (h : σ a ≠ σ b)
    (r : MvPolynomial (ULift.{u} (Fin ((obj (σ b)).n + 1))) ℂ)
    (he : RefineDatumCrossEq.{u} obj σ fam poly q glue a b r)
    (u : (PresentedAlgebra.{u} ((obj (σ b)).n + 1) ((obj (σ b)).k + 1)
      (localisationPresentation.{u} (obj (σ b)).g (poly (σ b) (σ a))))ˣ)
    (hu : RefineDatumCrossUnit.{u} obj σ fam poly q a b r u) :
    (refineDatumGlueNe.{u} obj σ fam poly q glue h r he u hu).hom ≫
        refineDatumCrossProj.{u} obj σ fam poly q h.symm =
      refineDatumCrossProj.{u} obj σ fam poly q h ≫ (glue (σ a) (σ b)).hom := by
  rw [refineDatumGlueNe_eq, refineDatumCrossProj_eq, refineDatumCrossProj_eq, Iso.trans_hom,
    Iso.trans_hom, Iso.symm_hom, Category.assoc, Category.assoc, Iso.inv_hom_id_assoc,
    refineCrossGlue_hom_comp, isoOfAlgEquiv_symm_refineDatumCrossAlgEquiv, Category.assoc]

/-- **The coherence triangle on this branch, analytified**, and it is over the original overlap
for the reason the statement above is.

The previous statement under the functor with nothing added — but **not in the shape the equal
branch's version has, and the difference is measured rather than predicted**.
`ComplexAnalytic.refineDatumGlueEq_analytification_comp` comes out with
`ComplexAnalytic.localisationProj` in every position but the glue; here the projections stay under
`ComplexAnalytic.analytificationFunctor`, because
`ComplexAnalytic.refineDatumCrossProj` is a `def` and `CategoryTheory.Functor.map_comp` does not
enter one. Adding
`ComplexAnalytic.analytificationFunctor_map_localisationPresHom` to the `simp` set below rewrites
nothing and `linter.unusedSimpArgs` reports it as unused; that is how the difference was found and
it is why it is not in the list.

`ComplexAnalytic.refineDatumCrossProj_analytification_localisationProj` is what a consumer
composes with to push the `a`-side projection down to its member, and between the two of them this
branch is in the same vocabulary as the equal one. -/
theorem refineDatumGlueNe_analytification_comp {a b : B} (h : σ a ≠ σ b)
    (r : MvPolynomial (ULift.{u} (Fin ((obj (σ b)).n + 1))) ℂ)
    (he : RefineDatumCrossEq.{u} obj σ fam poly q glue a b r)
    (u : (PresentedAlgebra.{u} ((obj (σ b)).n + 1) ((obj (σ b)).k + 1)
      (localisationPresentation.{u} (obj (σ b)).g (poly (σ b) (σ a))))ˣ)
    (hu : RefineDatumCrossUnit.{u} obj σ fam poly q a b r u) :
    analytificationFunctor.{u}.map
          (refineDatumGlueNe.{u} obj σ fam poly q glue h r he u hu).hom ≫
        analytificationFunctor.{u}.map (refineDatumCrossProj.{u} obj σ fam poly q h.symm) =
      analytificationFunctor.{u}.map (refineDatumCrossProj.{u} obj σ fam poly q h) ≫
        analytificationFunctor.{u}.map (glue (σ a) (σ b)).hom := by
  have e := congrArg (analytificationFunctor.{u}.map)
    (refineDatumGlueNe_comp.{u} obj σ fam poly q glue h r he u hu)
  simp only [Functor.map_comp] at e
  exact e

/-! ### The field, assembled -/

variable (r : ∀ _ b : B, MvPolynomial (ULift.{u} (Fin ((obj (σ b)).n + 1))) ℂ)
  (u : ∀ a b : B, (PresentedAlgebra.{u} ((obj (σ b)).n + 1) ((obj (σ b)).k + 1)
    (localisationPresentation.{u} (obj (σ b)).g (poly (σ b) (σ a))))ˣ)

open Classical in
/-- **The `glue` field of the refined cover datum, at every ordered pair.**

The two branches joined by a case split on `σ a = σ b`, which is the same split
`ComplexAnalytic.refineDatumPoly` makes inside a polynomial and this one makes between two
isomorphisms.

**The two branches have the same type and the split needs no transport.** The field's type names
`ComplexAnalytic.refineDatumPoly` and no case at all, so both branches are isomorphisms between
the same two objects; what the equal branch of `ComplexAnalytic.refineDatumFactor` needs a `▸` for
is that its two *values* live in types indexed by the two members, and nothing of that shape
survives here. Had it not been so the split would have been the third transport on this line, and
it would have had to sit in the shape of the overlap where every statement below would meet it.

**What the caller supplies is the choice, not its existence.** `r` and `u` are families over
ordered pairs and `he`, `hu` are the two equations at the pairs whose members differ, exactly as
`q` is a family in `ComplexAnalytic.refineDatumPoly`. **That a choice exists is settled** and not
here: `ComplexAnalytic.exists_refineDatumCross` (`Oka/Analytification/CrossMemberChoice.lean`)
produces one at every ordered pair, algebraically. What is untouched here, and is the absence
`Oka/Analytification/CrossMemberGlue.lean` records as *"nothing here produces `q`"*, is whether
the overlap a choice refines to is the geometric one.

**This paragraph also asked whether the choices at `(a, b)` and at `(b, a)` can be made
compatibly, calling that what a `hsymm` would be stated against.** They cannot be shown to be and
they do not have to be: `ComplexAnalytic.refineDatumGlue_symm` is the law at two arbitrary
choices, and `ComplexAnalytic.refineDatumGlueNe_congr` says this field does not depend on the
choice at all. Both are in `Oka/Analytification/RefineDatumSymm.lean` and neither is available at
this point in the import order. -/
def refineDatumGlue
    (he : ∀ a b : B, ∀ _ : σ a ≠ σ b,
      RefineDatumCrossEq.{u} obj σ fam poly q glue a b (r a b))
    (hu : ∀ a b : B, ∀ _ : σ a ≠ σ b,
      RefineDatumCrossUnit.{u} obj σ fam poly q a b (r a b) (u a b)) (a b : B) :
    coverOverlap.{u} (refineDatumObj.{u} obj σ fam) (refineDatumPoly.{u} obj poly σ fam q) a b ≅
      coverOverlap.{u} (refineDatumObj.{u} obj σ fam) (refineDatumPoly.{u} obj poly σ fam q) b a :=
  if h : σ a = σ b then refineDatumGlueEq.{u} obj σ fam poly q h
  else refineDatumGlueNe.{u} obj σ fam poly q glue h (r a b) (he a b h) (u a b) (hu a b h)

/-- **Where the two refined members lie over one member**, the field is the equal branch. -/
theorem refineDatumGlue_of_eq
    (he : ∀ a b : B, ∀ _ : σ a ≠ σ b,
      RefineDatumCrossEq.{u} obj σ fam poly q glue a b (r a b))
    (hu : ∀ a b : B, ∀ _ : σ a ≠ σ b,
      RefineDatumCrossUnit.{u} obj σ fam poly q a b (r a b) (u a b)) {a b : B} (h : σ a = σ b) :
    refineDatumGlue.{u} obj σ fam poly q glue r u he hu a b =
      refineDatumGlueEq.{u} obj σ fam poly q h :=
  dif_pos h

/-- **Where they lie over two**, it is the cross-member branch at the caller's choice for that
ordered pair. -/
theorem refineDatumGlue_of_ne
    (he : ∀ a b : B, ∀ _ : σ a ≠ σ b,
      RefineDatumCrossEq.{u} obj σ fam poly q glue a b (r a b))
    (hu : ∀ a b : B, ∀ _ : σ a ≠ σ b,
      RefineDatumCrossUnit.{u} obj σ fam poly q a b (r a b) (u a b)) {a b : B} (h : σ a ≠ σ b) :
    refineDatumGlue.{u} obj σ fam poly q glue r u he hu a b =
      refineDatumGlueNe.{u} obj σ fam poly q glue h (r a b) (he a b h) (u a b) (hu a b h) :=
  dif_neg h

/-- **At constant `σ` the field is `Oka/Analytification/CoverRefinement.lean`'s glue**, for every
choice: every pair is on the diagonal, so the cross-member branch is never taken and `r`, `u` and
the two equations are never read.

**Unlike `ComplexAnalytic.refineDatumGlueEq_const` this is not `rfl`**, and the reason is the
`open Classical in` above: the `dite`'s instance is `Classical.propDecidable`, which does not
reduce on `(fun _ ↦ i) a = (fun _ ↦ i) b` even though that equation is `rfl`. So the statement
goes through `ComplexAnalytic.refineDatumGlue_of_eq`, which is `dif_pos`, and then through the
equal branch's own constant case. A `DecidableEq J` hypothesis would buy the `rfl` back and would
cost every consumer an instance argument; `ComplexAnalytic.refineDatumFactor` and
`ComplexAnalytic.polyDiagOne` make the same trade in the same direction. -/
theorem refineDatumGlue_const (i : J)
    (fam' : B → MvPolynomial (ULift.{u} (Fin (obj i).n)) ℂ)
    (q' : ∀ _ : B, B → MvPolynomial (ULift.{u} (Fin (obj i).n)) ℂ)
    (r' : ∀ _ _ : B, MvPolynomial (ULift.{u} (Fin ((obj i).n + 1))) ℂ)
    (u' : ∀ _ _ : B, (PresentedAlgebra.{u} ((obj i).n + 1) ((obj i).k + 1)
      (localisationPresentation.{u} (obj i).g (poly i i)))ˣ)
    (he' : ∀ a b : B, ∀ _ : (fun _ ↦ i) a ≠ (fun _ ↦ i) b,
      RefineDatumCrossEq.{u} obj (fun _ ↦ i) fam' poly q' glue a b (r' a b))
    (hu' : ∀ a b : B, ∀ _ : (fun _ ↦ i) a ≠ (fun _ ↦ i) b,
      RefineDatumCrossUnit.{u} obj (fun _ ↦ i) fam' poly q' a b (r' a b) (u' a b)) (a b : B) :
    refineDatumGlue.{u} obj (fun _ ↦ i) fam' poly q' glue r' u' he' hu' a b =
      eqToIso (coverOverlap_refineDatumPoly_const.{u} obj poly i fam' q' a b) ≪≫
        refineGlue.{u} (obj i).g fam' a b ≪≫
          eqToIso (coverOverlap_refineDatumPoly_const.{u} obj poly i fam' q' b a).symm := by
  rw [refineDatumGlue_of_eq.{u} obj (fun _ ↦ i) fam' poly q' glue r' u' he' hu'
    (rfl : (fun _ ↦ i) a = (fun _ ↦ i) b)]
  exact refineDatumGlueEq_const.{u} obj poly i fam' q' a b

end

end ComplexAnalytic
