/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka

/-!
# Axiom regression tests: Weierstrass division and preparation

The Weierstrass division and preparation theorems and their uniqueness statements, from
`Oka/Weierstrass.lean` and `Oka/OkaLemma.lean`, together with the germ-versus-function dictionary
that `Oka/Weierstrass.lean` builds on the way to preparation.

See `OkaTest/Axioms.lean` for what these assertions are for and how to update one.

## Why all of `Oka/Weierstrass.lean` is routed here, and not by namespace

Until `47c2e82` grew the headings below, the only results `Oka/Weierstrass.lean` then advertised
that were guarded anywhere were `localweierstrass_division` and `localweierstrass_preparation`,
which this file already pinned. The names `47c2e82` added span the root namespace and four
others — `LocalOkaRing`, `OkaRing`, `MvPowerSeries` and `Polynomial`. **`LocalOkaRing` and
`OkaRing` are each named by a row of `OkaTest/Axioms.lean`'s table; `MvPowerSeries` and
`Polynomial` are named by none.** **They are all here anyway, because that table routes by the
module a declaration lives in and not by the namespace it is declared into**, and its own
re-measurement recipe says so: resolve every `#print axioms` name to its module and ask whether
some module's guards are covered by no row. Every one of them resolves to `Oka.Weierstrass`,
whose guards this row already covered.

`exists_analyticAt_implicit` is the one where topic and module pull apart, and it stays here too.
It is the analytic implicit function theorem, so `OkaTest/Axioms/Analysis.lean` is arguable on
topic — **complex analysis** is the first thing that row names. **The module rule above is what
settles it**: the theorem is declared in `Oka/Weierstrass.lean`, and its own docstring states it
*"in the form needed for the Weierstrass preparation theorem"*.

**Two clauses of the two paragraphs above were repaired together, they are about the same object —
`OkaTest/Axioms.lean`'s table — and they had failed in two different ways.** *"three of which have
a row of their own"* was **wrong on the day it was written**: `47c2e82` wrote it, and the table
**at `47c2e82`** already named two of the four namespaces that same sentence lists and no more.
The table's twelve rows at `47c2e82` and its twelve at `0b09e45` differ in one row's wording and
in nothing else, so nothing about that count rotted. The clause that replaces it names all four
namespaces and their status, which is the enumeration `OkaTest/Axioms.lean`'s rule paragraph
exempts.

**The other clause did rot, and it was a quotation rather than a count.** `f6a5fa9` wrote *that
row reads «complex analysis, and the topology of polynomial zero loci»*, which was exact at
`f6a5fa9`; `ca56617` reworded that row and the quotation has been wrong since, with nothing in
`scripts/` able to see it. **A quotation of another file's row is falsified by the next rewording
of that row exactly as a count of its rows is falsified by the next row**, so what is left here is
the word the argument needs and not the sentence it was cut from.

An earlier draft of this paragraph settled it the same way for a different and false reason: that
`OkaTest/Axioms/Analysis.lean` guards only mirror-tree modules. That file guards
`Oka.Analytic.DividedDifference` declarations, and `README.md` puts that directory **outside** the
mirror tree — its worked example of a general file with no single Mathlib counterpart is
`Oka/Analytic/ParametricCircleIntegral.lean`, the neighbour in the same directory, and **at
`v4.32.0` — the revision `lakefile.toml` pins, resolved by `lake-manifest.json` to
`81a5d257c8e410db227a6665ed08f64fea08e997` — Mathlib has no `Analytic` directory for either to
mirror**. Only the argument changed; no guard moved.

**That last clause is the one claim of its class a directory test decides outright**, because what
it denies is a path and not a declaration: `test -d .lake/packages/mathlib/Mathlib/Analytic` fails
at that rev, and `ls` there returns **33** entries, of which two are files —
`Mathlib/Init.lean` and `Mathlib/Tactic.lean` — and the other **31** are directories, `Analysis`
being the only one whose name begins *Analy*. None of the three questions
`OkaTest/Axioms.lean`'s seventh census object puts to an instrument is answered *yes* here: a
directory cannot be spelled another way, cannot be inherited from a general statement, and is not
generated.

**The control is positive, and it is why the clause writes `Analytic` and not *analytic*.**
`Mathlib/Analysis/Analytic/` does exist at that rev and is not the directory this clause is about:
`README.md`'s rule is a **path** mirror, so what `Oka/Analytic/X.lean` names upstream is
`Mathlib/Analytic/X.lean`, and a directory one level down under `Mathlib/Analysis/` is a different
path. **The absence is not by itself what puts `Oka/Analytic/` outside the mirror tree**, and this
clause does not claim that it is: `README.md` allows a mirror file at a *proposed* path that does
not yet exist upstream, and the reason it gives for this directory is that
`Oka/Analytic/ParametricCircleIntegral.lean` spans several Mathlib files rather than extending one.

**That clause read *and Mathlib has no Analytic directory for either to mirror* until
2026-09-21**, with no version and no instrument beside it; `git show
c6bfc1f:OkaTest/Axioms/Weierstrass.lean` carries the retired wording at `:56–57`, wrapped after
*has*. **The claim is unchanged and only its warrant is**, which is why the retired wording is
kept here rather than struck. `OkaTest/Axioms.lean`'s seventh census object is the rule and taxis
#2133 is the enumeration this site is one of fourteen in.
-/

/-! ### Weierstrass theory -/

/--
info: 'localweierstrass_division' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms localweierstrass_division

/--
info: 'localweierstrass_division_unique' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms localweierstrass_division_unique

/--
info: 'localweierstrass_preparation' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms localweierstrass_preparation

/-! ### The germ–function dictionary

`Oka/Weierstrass.lean`'s own `## Main results` calls these *the dictionary between functions and
germs used to reduce Oka's coherence lemma to them*. -/

/--
info: 'OkaRing.germ_toOkaRing' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms OkaRing.germ_toOkaRing

/--
info: 'LocalOkaRing.fromPolynomial' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LocalOkaRing.fromPolynomial

/--
info: 'OkaRing.exists_restrict_eq_of_germ_eq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms OkaRing.exists_restrict_eq_of_germ_eq

/--
info: 'LocalOkaRing.exists_okaRing_germ' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LocalOkaRing.exists_okaRing_germ

/--
info: 'OkaRing.exists_isUnit_restrict' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms OkaRing.exists_isUnit_restrict

/-! ### Realizing germ polynomials by polynomials over a neighbourhood

`LocalOkaRing.exists_isWeierstrassPolynomial_realize` was covered before this heading only
through its consumers: `LocalOkaRing.exists_monic_realize_congr`,
`LocalOkaRing.exists_monic_realize_ulift` and `LocalOkaRing.exists_congr_monic_realize_of_ne_zero`
in `Oka/UliftCoord.lean` all rest on it, and all three are guarded — so `#print axioms` already
covered it *transitively*. **A transitive guard is not a guard**: it fails the moment the consumer
is restated or removed, and it says nothing about this lemma on its own. Its two neighbours in the
preparation chain, `localweierstrass_preparation` above and
`LocalOkaRing.exists_congr_localweierstrass_preparation` in `OkaTest/Axioms/LocalOkaRing.lean`,
were pinned and it was not, so the chain was held at both ends and not in the middle.

An earlier version of the first sentence called this lemma *the one of the twelve with live
consumers*, and that was false when it was written rather than rotted since:
`MvPowerSeries.exists_direction` and `lineEquiv`, both guarded below in this file, are consumed in
the proof of `LocalOkaRing.exists_congr_isGeneralIn`, which `OkaTest/Axioms/LocalOkaRing.lean`
already pinned at `47c2e82`. Only the sentence changed; no guard moved. -/

/--
info: 'LocalOkaRing.exists_isWeierstrassPolynomial_realize' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LocalOkaRing.exists_isWeierstrassPolynomial_realize

/--
info: 'LocalOkaRing.exists_poly_germPoly' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LocalOkaRing.exists_poly_germPoly

/--
info: 'Polynomial.exists_map_restrict_eq_zero' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Polynomial.exists_map_restrict_eq_zero

/-! ### The change of coordinates making finitely many germs general in the last variable -/

/--
info: 'MvPowerSeries.Represents.homogeneous_eval_eq_zero' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MvPowerSeries.Represents.homogeneous_eval_eq_zero

/--
info: 'MvPowerSeries.exists_direction' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MvPowerSeries.exists_direction

/--
info: 'lineEquiv' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms lineEquiv

/-! ### The analytic implicit function theorem

The input to `localweierstrass_preparation` above, and the reason division by the generic
Weierstrass polynomial suffices to prove it. -/

/--
info: 'exists_analyticAt_implicit' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exists_analyticAt_implicit
