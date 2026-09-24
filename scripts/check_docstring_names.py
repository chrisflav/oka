#!/usr/bin/env python3
"""Check that every backticked dotted name in a comment or docstring resolves.

Nothing else in this repository looks inside a comment.  `lake build --wfail` sees only
elaborated terms; `lake lint` checks declaration *names* and `simp` normal forms; `lake exe
lint-style` checks whitespace, line endings and unicode; `mk_all --check` checks imports; and the
declaration-name diff that every pull request body runs compares declarations rather than the
prose citing them.  A backticked name in a `/-- … -/` or `/-! … -/` block that names nothing at
all passes every one of them, and on 2026-08-20/21 that cost four separate findings in one day,
each caught by a human who happened to be reading the file for another reason.  The worst was
five wrong names appearing at once because the cause was structural — a file drafted in a
scratch buffer with no `namespace` line — which is the class that proofreading cannot see and a
checker cannot miss.

Usage:

    python3 scripts/check_docstring_names.py             # dump the environment, then check
    python3 scripts/check_docstring_names.py --dump F    # reuse a dump written earlier
    python3 scripts/check_docstring_names.py --tree DIR  # ...against another checkout
    python3 scripts/check_docstring_names.py --diff BASE # the name diff, no build needed
    python3 scripts/check_docstring_names.py --diff BASE --sites   # ...per occurrence
    python3 scripts/check_docstring_names.py --ambiguous # list the elided citations with several
    python3 scripts/check_docstring_names.py --self-test #   resolutions; see "Elided citations"

Exits 0 when every candidate resolves, 1 when some do not, and 2 when the tool itself cannot
answer: the environment dump fails, `--tree` or `--diff` names something that is not a checkout of
this repository, `--sites` is given without `--diff`, or the self-test does not pass.  `lake build`
must have run first: this reads the oleans, it does not produce them.  `--diff` is the exception
and reads no environment at all.

## The name diff, and the no-op that used to drive it

Every pull request body on this project reports how the *distinct* candidate count moved between
the base and the branch, and until 2026-08-29 this script offered no way to compute one, so each
session wrote its own driver.  The obvious driver is wrong:

    spec = importlib.util.spec_from_file_location("chk", "scripts/check_docstring_names.py")
    m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
    def names(tree):
        os.chdir(tree); return set(m.candidates())     # the chdir is inert

`REPO` below is bound **at import time from this file's own path**, and `os.chdir` does not move
it, so that driver scans one tree twice and prints `added: [] removed: []` with equal counts
whatever the branch did.  **Its failure mode is the answer the reader is hoping for**: a
docs-only branch is supposed to move the count by zero, so the no-op's output is what a clean
branch produces — no error, no traceback, no suspicious figure.  It shipped in two verdicts
before anything noticed, and what noticed was a delivery note whose figure disagreed with it.

So `--diff BASE` is here, it needs no build because candidacy is a text property, and
`--self-test` is a **positive** control: two fixture trees that differ, asserted to diff to
non-empty.  "Two identical trees diff to empty" is the test the broken driver passes.

**One implementation scans both trees** — this file's, whichever tree it lives in.  That is
deliberate and it is what isolates a change in the *prose* from a change in the *rules*: a branch
that edits `is_name_shaped`, `comment_regions` or **the walk** — `ROOTS` and `PROSE_DIRS` — will
not show up in `--diff` at all.  Run the check itself, not the diff, to see the effect of such a
change.  The walk is named here because it is the only member of that class this repository has
actually exercised: the widening of 2026-08-31 had to take its own headline delta as two runs,
one for the walk and one for the prose, and it is also the only member that falsifies the
base-figure agreement recorded below.

**`--diff` alone is silent on a branch that only rewords, and `--sites` is what is not.**  A
docstring commit that swaps words *between* backticked names that already exist adds no name and
no occurrence, so `added`, `removed` and both figures are identical on the two trees — which is
byte-for-byte the output of a driver that read one tree twice.  That happened on
lana-agents/oka#246, whose delivery note had to say in terms that none of its figures was
evidence.  `--sites` compares the `file:line` of every occurrence instead of the name set: on that
branch it reports **9 moved sites across 8 names, all in the edited file, every delta `+1`**, and
an empty site diff is what a same-tree comparison returns by construction.  Pick the report by
what the branch can move — declarations move the distinct count, rewording moves occurrences, a
word swapped between two existing names moves only sites.

**The two figures `--diff` prints are the headline's own**, and there is no second definition of
either: the `N backticked names (M distinct)` line at the end of a normal run is
`sum(len(v) for v in candidates().values())` and `len(candidates())`, which is exactly what
`report` below computes.  So `--diff BASE --tree BASE` reproduces the base's own headline — **when
the base's copy of this script walks the same directories** — and a pull request body can quote
both figures from one command.

**That qualification is not decorative, and the walk widening of 2026-08-31 is what added it.**
Measured 2026-08-29, before `scripts/` was walked: `f6a5fa9` gave `6112 backticked names (2159
distinct)` and `70580e1` gave `6115 (2159)`, each agreeing with that tree's own copy of this
script loaded by path.  Re-measured 2026-08-31 with *this* copy, on worktrees of the same two
commits: **`6120 (2161)` and `6123 (2161)`**, `+8 / +2` on each, which is those trees' own
`scripts/` prose newly read.  Both readings are correct and they answer different questions —
this script's is the one a Δ needs, because a Δ has to scan both trees by one rule, and the base's
own is the figure that base's CI printed.  **So quoting a base figure from here as "what the base
reported" is wrong for any base cut before 2026-08-31, and nothing flags it**: `--diff` prints
both numbers from one implementation and neither is marked.  Re-date this paragraph rather than
extend it the next time the walk moves, and note that this file is a `.py` and so is checked by
nothing — the only thing keeping the figures above honest is that they were re-run.

A note on taxis #1192 reported the occurrence count as running "one or two below" the headline;
it does not, and what was being compared was two different trees.

## What counts as a candidate

A backtick-delimited run of non-backtick, non-whitespace characters, occurring inside a `--`,
`/- -/`, `/-- -/` or `/-! -/` region of a `.lean` file under `Oka/` or `scripts/`,
containing at least one `.`, and shaped like a Lean name: every dot-separated component non-empty
and starting with a letter or `_`, every character alphanumeric or one of `_ ' ! ?`.  That shape
test alone discards `Mathlib/RingTheory/Filtration.lean`, `[M.IsCoherent]`, `Scheme.{0}`,
`?V.isOpenEmbedding` and `⊤.isOpenEmbedding` without any of them needing to be listed anywhere.

**It also discarded every `…`-elided citation in this tree**, which is a second population with a
rule of its own; see "Elided citations" below.  The two do not overlap, and the two figures this
section is about count elided citations neither before that change nor after it.

**`scripts/` is in the walk and was not until 2026-08-31**, which made the module docstrings of
`scripts/DumpEnvNames.lean` and `scripts/DumpOkaDecls.lean` — the two files that *describe* this
check — the only Lean prose in the repository that it did not read.  taxis #1337 has the
measurement; what found it is that a reviewer who knows this script well predicted, on a
one-paragraph edit to `scripts/DumpOkaDecls.lean`, that the headline figure would move, and it
could not.  Three of the eight dotted candidates under `scripts/` were findings, and two of those
three share one paragraph of `scripts/DumpEnvNames.lean` — the one under its "The format, and why
the two kinds are told apart" heading, which states this field-notation rule and then exhibits a
citation it rejects.

`scripts/` is walked for its `.lean` files only, like `Oka/`.  **The `.py` files there —
this one included — are still read by nothing**, and they carry the same prose in the same
backticked form: the field-notation rule below is stated with `head.tail` twice in this very
docstring.  Whether a Python docstring should be checked at all is a separate question and this
script does not answer it; what widening the walk to `.lean` alone settles is that the two Lean
helpers are no longer the exception.

**Widening the walk turned up a class of name the escape hatch did not have a clause for**: prose
*about* the rules, where the name is written as an example and resolving would defeat the point of
writing it.  Both members are in `scripts/DumpEnvNames.lean` — the schematic `head.tail`, and
`Mathlib.RingTheory.Filtration.someDecl`, which is exhibited there precisely as a citation the
tightened
field-notation rule now rejects.  They are in `scripts/docstring-names-ignore.txt` under a header
clause of their own; see that file for why no rewording fixes the second one.

## What counts as resolving

Deliberately more permissive than Lean's own name resolution, in the direction that avoids false
positives.  A candidate resolves if any of the following holds.

* **Suffix rule.**  Some constant in the environment of `Oka` ends with it, as a run of whole
  components.  This is "resolves with every namespace in the environment open", so
  `Multicoequalizer.desc` passes in a file that opens `CategoryTheory.Limits` and equally in one
  that does not.  Tracking each file's own `open`s and `namespace`s, which is what Lean would
  do, buys precision this check does not need and costs a false positive every time the tracking
  is wrong.

* **Module rule.**  It is the name of a module in the environment.  Docstrings here cite modules
  in the same backticked form as declarations: `Oka.Weierstrass`, `Mathlib.RingTheory.Filtration`.

* **File rule.**  It names a file that exists in the repository.  This is what lets `README.md`
  and `lakefile.toml` — whose components happen to be identifier-shaped, unlike anything with a
  `/` in it — through without an entry each in the ignore file.

* **Field-notation rule.**  Splitting the candidate as `head.tail` at any dot, `head` resolves by
  the suffix rule **to a declaration** and is *not itself a namespace* — no constant or module has
  it as a run of components with further components after it.  Then `head.tail` is generalised
  field notation on the term `head` rather than a declaration name, which is legitimate and
  idiomatic prose: `restrictTopIso.hom`, `adicCompletionEquiv.symm`,
  `existsUnique_axisIncl.exists.choose`, `AlgebraicGeometry.identityToΓSpec.naturality`.

  **The head must be a declaration and not a module, and until 2026-08-31 it could be either.**
  Field notation is on a *term*; a module is not one and has no fields.  Because
  `scripts/DumpEnvNames.lean` wrote modules and constants into one undifferentiated list, this
  rule could not tell them apart, and every module that is an *empty namespace* — which is every
  module of the test library this repository then carried, since they all declared into
  `ComplexAnalytic` — became a head under which **any tail whatsoever** was accepted,
  unexamined.  Planted on `master` = `4f96682` and reverted: a bogus tail under such a module was
  accepted silently while `` `ComplexAnalytic.zzz_planted_bogus` `` was reported.  It cost eight
  real citations in this
  tree — three declaration references naming nothing and five bare file names with no directory,
  one of which (`PullbackStalk.lean`) is ambiguous between two files that state the same result.
  The dump now tags each line `module` or `decl`; taxis #1326 has the measurement, and
  `--self-test` asserts both halves.

  The namespace condition is what keeps this from swallowing the findings it is meant to leave
  alone.  `AlgebraicGeometry.Scheme.OpenCover.glueMorphisms` — the reference this checker was
  written to catch, Mathlib having renamed the namespace to `Scheme.Cover` while leaving the
  *type* called `X.OpenCover` — has `AlgebraicGeometry.Scheme.OpenCover` as a head that does
  resolve, so without the namespace condition it would be accepted; with it the head is a
  namespace with twenty declarations in it and the candidate is still reported.

  **A generated name does not count as making its parent a namespace**, and this is not a
  refinement: without it the rule is *non-monotone*, which no other rule here is.  Lean plants an
  equation lemma under a definition's own name — `thatDef.eq_1`, and `_proof_1` beside it — the
  first time any tactic anywhere unfolds it.  So `rw [thatDef]` in one file would make `thatDef`
  a namespace, and every `` `thatDef.someField` `` citation *in every other file* would start
  being reported, at a distance, with a message about the environment having nothing in it when
  what happened is that the environment gained something.  Measured on `master` = `af2991d`, with
  no branch involved and against a **planted** citation, this tree containing none of that shape:
  `AlgebraicGeometry.AffineScheme.Γ` has exactly one child in the whole environment,
  `AlgebraicGeometry.AffineScheme.Γ.eq_1`, so before this condition existed a fixture citing
  `` `AlgebraicGeometry.AffineScheme.Γ.someField` `` was reported while the structurally identical
  `` `AlgebraicGeometry.identityToΓSpec.naturality` `` — a citation this tree really makes, at
  `Oka/AlgebraicGeometry/GammaSpecAdjunction.lean:61`, whose head has no children at all — was
  accepted.

  **The membership test is not "Lean generated it".**  It is: does Lean generate it *on demand,
  after the declaration, because of something in another file*?  Only that makes the
  classification non-monotone, and only that is what this list repairs.  So the components
  generated for an inductive or a structure (`rec`, `casesOn`, `mk`, `injEq`, `noConfusion`,
  `sizeOf_spec`, `ctorIdx`) are absent — a head that carries those really is a type — and so are
  the ones `deriving` writes (`beq`, `repr`, `hash`, `decEq`, `ord`, `toJson`, `fromJson`): they
  arrive *with* the declaration, so a head that has one had it from the start and no other file
  can add it.

  **How the list going stale would be noticed**: not by maintaining it against Lean's, but by the
  finding message, which names the head, says it does resolve, and names the declaration that made
  it a namespace — so a suffix this list is missing costs one line rather than the session the
  first instance cost.  **That is how `congr_simp` was found**, three days after the list was
  written, when a new definition acquired one.

  **And how the list is audited, which is cheaper than reading Lean's source**: iterate the dump,
  group every name by its head, and list the components that are the *sole* child of a head not
  already matched here — a component that is some head's only non-matched child is a candidate for
  being generated, because a head with a real declaration under it has one.  Sorted by frequency
  on `af2991d`, with the components already listed removed, the top of that list is

      2182  congr_simp          748  default        605  noConfusion      213  toJson
       207  beq                 197  repr           191  fromJson          92  go
        85  induct_unfolding     81  hash            59  decEq             44  loop

  and everything in it is decided by the paragraph above: `congr_simp`, `induct_unfolding`,
  `fun_cases_unfolding` (25), `hcongr_N` (7 at the top arity) and the nested `match_N_M` (10) are
  planted on demand and are in the list; `noConfusion` is a structure component; `beq`, `repr`,
  `toJson`, `fromJson`, `hash`, `decEq` and `ord` are `deriving`'s; and `default`, `go`, `loop`,
  `run`, `aux` and `elim` are names authors write.  **`congr` is the trap and is deliberately
  out**: seven heads have it as their only non-matched child and it looks exactly like
  `congr_simp`, but `EventuallyMeasurableSet.congr` and `LinearMap.Nondegenerate.congr` are
  Mathlib lemmas somebody wrote.  A suffix goes in this list only when every occurrence of it in
  the dump is generated, and `congr` fails that.

  Over the heads this tree's own citations produce, the whole list changes the classification of
  exactly one — and it is not the planted head above, which no citation here has.  It is `Γ`,
  which resolves by the suffix rule and was a namespace only because of
  `AlgebraicGeometry.AffineScheme.Γ.eq_1`, the one name in the whole environment with `Γ` as an
  interior component: on `af2991d`, 237 heads both resolve and are namespaces without this
  condition and 236 with it, and **236 with `congr_simp` and the four beside it added — the same
  236, not merely as many**.  **No citation's verdict moves**, on either change.  `Γ.map`,
  `Γ.obj`, `Γ.rightOp` and `Γ.map_comp`, 13 sites between them, are taken by the short-head rule
  below, which is tried first, on both sides of the change.  What this buys is monotonicity, not a
  repair to anything this tree currently says.

  The hole this leaves, stated so that nobody has to rediscover it: a *misspelled* declaration in
  a namespace that contains no other declaration — or none other than generated ones — is read as
  field notation and accepted.  The common structural failure — a whole file's worth of names in
  the wrong namespace — is not of that shape, because the namespace either exists with
  declarations in it or does not resolve at all.  How wide the widening is, since the "exactly
  one" above is a fact about today's citations rather than about the rule: on `af2991d` **11267
  runs in this environment have children and only generated ones**, 11263 of them declarations,
  and every one is a head some future citation could be read as field notation on where before it
  would have been reported.  **That figure was 8896 (8892 declarations) before `congr_simp` and
  the four beside it went in**, so this list is where the widening lives and it is worth saying
  what each addition costs.  2371 runs stop being namespaces: 2182 because of `congr_simp` and
  nothing else, 85 `induct_unfolding`, 31 `hcongr_N`, 25 `fun_cases_unfolding`, 12 `match_N_M`,
  and 36 heads that carry two of them.

* **Short-head rule.**  The head component is at most two characters *and is not a root
  namespace* — no constant begins with it and continues with a component an author wrote.
  `i.stalkMap`, `Γ.map`, `φ.symm`, `U.extend'`, `w.2` are field notation on a local binder.

  The second condition is not decoration.  An earlier version of this rule said that no namespace
  on this project or in Mathlib is that short; that is **false** — `Eq`, `Or`, `Ne` and `Id` are,
  with 52, 24, 38 and 20 constants under them, `Eq.symm` and `Eq.mp` among them — so without it a
  misspelled `Eq.symmm` is accepted silently.

  *Root* namespace rather than namespace-anywhere, and the difference is the whole live
  population of this rule.  `M`, `V` and `X` all occur as interior components of real constants —
  `Lean.Meta.Grind.EMatch.M.run`, `Std.Time.Modifier.V.elim`, `Std.Time.Modifier.X.noConfusion` —
  so the namespace-anywhere test rejects ten of the twelve short heads this tree's citations use
  and reports 33 names at 46 sites, every one of them a citation this rule exists to accept.  None
  of the twelve occurs at the root and all four of `Eq`, `Or`, `Ne` and `Id` do.  Measured, not
  assumed — the first version of this rule assumed and was wrong in both directions on the same
  day.

  A *used* head here means one where nothing else would accept the citation: not resolving, not
  ignored, not a file, not field notation, so this rule is what stands between it and a finding.
  **The `seven` heads and `twelve` false positives this paragraph claimed until 2026-08-30 do not
  reproduce under that definition or any other tried** — on `dab084a` it gives twelve heads and 33
  names, and thirteen and 37 with the condition above removed — and they are left recorded rather
  than quietly replaced, because a figure nobody can reproduce is worth knowing about.  The move
  between those two is one head: `Γ` was in this population until the generated-name condition
  above, and its four citations are now field notation as well, so they no longer need this rule.
  That is the only interaction between the two rules and it changed no verdict.

Anything left over is a finding unless `scripts/docstring-names-ignore.txt` lists it.

## Elided citations, `…Ns.decl`

**This repository's house form for a long name is to elide the leading namespace with `…`**, and
until 2026-09-19 this check could not see one — and by the enumeration this file opens with,
nothing else in this repository looks inside a comment at all.  `is_name_shaped` rejects a
component that does not begin with a letter or `_`; `…` is neither, so the citation
`` `…SeparatedFiniteEtaleOver.hasFiniteLimits` `` was never a candidate, was never looked up, and
**could not have been reported however it was spelled**.  The citations most likely to be mistyped
were exactly the ones outside the check, and the headline `0 unresolved` was a statement about the
other spelling only.  taxis #2056 is the filing, and it records that **two citations naming no
declaration at all survived three rounds, two graders and a green CI** in
`Oka/AnalyticSpace/GaloisCategory.lean`, caught in the end by a reader and not by a check.

**Both are reported by this rule, and that is a run and not an argument.**  At `1569409`, the
round that carried them, `--tree` on a worktree of that commit names exactly those two elided
citations, each with the message its own defect deserves.  (The dump there has to be `master`'s,
so that run also reports seven *plain* names and all seven are the dump's doing rather than the
branch's: five are Mathlib's, under the `Mathlib.CategoryTheory.Galois.Basic` that branch newly
imports and absent from an environment without it, and two — `…preGaloisCategory` and
`…fintypeFiberFunctor_isFiberFunctor` — are instances declared in the very file, at `:200` and
`:222`.  **The two elided ones are not of that kind**: `preservesEpis_` occurs nowhere in that
tree's own *source* either, and the coproducts instance it means is declared
`SeparatedFiniteEtaleOver.preservesFiniteCoproducts_fintypeFiber` — no `Functor` — while the
`Functor` spelling is `FiniteEtaleOver`'s, one category out.)

They are counted and resolved as a **second population**, reported on their own line, and the two
headline figures above do not move.  That is deliberate: an elided citation is not a Lean name —
nothing would resolve it, `os.path.exists` cannot take it, the field-notation and short-head rules
are meaningless on it — and by "The name diff" above, every pull request body on this project
quotes `N backticked names (M distinct)` as a branch's own figure.  Folding 165 occurrences into
that number would have made every such figure already written down incomparable with every one
written after.

* **What is in scope.**  A backticked run beginning `…` whose remainder is `is_name_shaped` — so
  at least one dot, every component identifier-shaped.  **165 occurrences, 107 distinct, in 14
  files** at `daeb942`, one since-deleted test file holding 109 of them.

* **What resolving means.**  Some declaration or module in the environment ends with the remainder
  as a run of whole components **and has at least one component before it** — a proper suffix,
  which is what the `…` asserts: it stands for an elided namespace, so there has to be one.  The
  weaker reading, which would also accept a name that *is* the remainder, changes no verdict here
  and is measured: **0 of the 107 resolve only as a whole name** at `daeb942`.

* **The wrong-namespace case, which is the one the filing was written about, needs no machinery
  beyond that.**  taxis #2056 predicted that a resolver checking only existence would *pass*
  `` `…SeparatedFiniteEtaleOver.preservesFiniteCoproducts_fintypeFiberFunctor` `` — the first of
  the two live defects — because that name does resolve, to `FiniteEtaleOver`'s declaration one
  category out, and asked for a resolver that prefers the enclosing file's namespace.  **Measured
  against `1569409`, the round that carried it: as a run of whole components it resolves to
  nothing**, because the real declaration's penultimate component is `FiniteEtaleOver` and the
  citation's is `SeparatedFiniteEtaleOver`.  Matching *whole components* is already the suffix
  rule's definition and it is what separates the two.  **The namespace-preferring resolver is not
  needed for the gate**, and it is not here; what the last component buys instead is the
  *message*, below.

* **The message, and why it is the deliverable.**  A bare *names nothing* would have sent the
  author of that citation looking for a typo in a name that is spelled correctly one namespace
  over.  So a finding also says where the final component **does** occur — `` `…Wrong.foo` ``
  reports that `foo` occurs under `Planted.Right` — or, when it occurs nowhere at all, says that,
  which is the other of the two live defects: nothing in the tree ends in `.preservesEpis_…`.

* **Ambiguity is a figure and not a finding.**  Six of the 107 resolve under more than one
  namespace at `daeb942`, and every one is a correct citation: `…GlueData.ι_jointly_surjective`
  is six of Mathlib's, `…Pullback.hasPullback_of_cover` is ambiguous between
  `AlgebraicGeometry.Scheme.` and **this repository's own**.  Gating on ambiguity would report six
  citations that are right, which is how a check earns an ignore-list and stops being a check.
  The count is printed on every run and `--ambiguous` lists them.

* **A dotless `` `…decl` `` is out of scope, and that is a measurement rather than a preference.**
  **207 occurrences, 107 distinct, in 31 files** at `daeb942` — and the dotless `…` elides a
  *prefix of the last component* rather than a namespace, so what follows is a fragment and not a
  name: `…_of_coeff`, `…_iff_restrictPreimage`, `…_apply`, and `…isPullback_map…` with an elision
  at both ends.  **26 occurrences (11 distinct) begin with `_`**, which no Lean component does.
  Read as citations they would report **29 occurrences (14 distinct)** on a tree that has no
  defect of that shape at all — a check that cries wolf on a house form, which is the failure the
  permissiveness of every rule above is chosen to avoid.  They are counted on the report line so
  that the class stays visible, and they are not resolved.  taxis #2056's thread has
  `oka-slot-3`'s independent run of both halves; its **29** and **26** are occurrence counts of
  the same 14 and 11 distinct forms this paragraph gives, which is a reconciliation and not a
  correction — the two runs agree name for name.

`scripts/docstring-names-ignore.txt` takes an elided citation **with its `…`**, so that an entry
cannot be confused with the plain name it elides and so that ignoring one does not ignore the
other.

## What a green here does NOT mean

A name that resolves *somewhere* but not where the prose means it to is accepted; so is a name
spelled correctly that describes the wrong theorem, and any name outside backticks.  The suffix
rule in particular accepts `Foo.bar` whenever any namespace at all has a `bar` in it.
"""

from __future__ import annotations

import argparse
import collections
import os
import re
import subprocess
import sys
import tempfile

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
IGNORE_FILE = os.path.join("scripts", "docstring-names-ignore.txt")
DUMP_SCRIPT = os.path.join("scripts", "DumpEnvNames.lean")
ROOTS = ("Oka",)

# Directories walked for prose that are **not** library roots: no `<name>.lean` root module sits
# beside them, and their presence is not what makes a directory a checkout of this repository.
# Keeping them out of `ROOTS` is what stops `check_tree` from asking a worktree for `scripts.lean`
# and `candidates` from trying to open it.
PROSE_DIRS = ("scripts",)

# A candidate whose head component is at most this long, and is not a root namespace, is field
# notation on a local binder rather than a declaration reference.
MAX_LOCAL_HEAD = 2

# The house form for a long name: `…Ns.decl` elides the leading namespace.  It is U+2026 and not
# three dots, and a component starting with it is not identifier-shaped, which is why
# `is_name_shaped` rejected the whole class and nothing checked it until taxis #2056.
ELLIPSIS = "…"

# How many witnesses a finding's message keeps for the final component of an unresolved elided
# citation.  The message names where that component *does* occur, which is what turns "names
# nothing" into "not under the namespace you wrote"; a handful is enough to say that and a cap is
# what keeps a common last component from holding thousands of names in memory.
MAX_WITNESSES = 6

# A name component the elaborator generates for the declaration it hangs off, rather than one an
# author wrote.  Such a component must not make its parent a namespace: see the field-notation
# rule in the module docstring above for why, and for the audit that says what is in this list
# and what is deliberately not.  **The membership test is not "Lean generated it" but "Lean
# generates it on demand, after the declaration, because of something in another file"** — that
# is what makes the namespace classification non-monotone and is the only thing this list exists
# to repair.  So the components generated for an *inductive* or a *structure* (`rec`, `casesOn`,
# `mk`, `injEq`, `noConfusion`, `ctorIdx`, `sizeOf_spec`) and the ones `deriving` writes at the
# declaration (`beq`, `repr`, `hash`, `decEq`, `ord`, `toJson`, `fromJson`) are absent: they
# arrive with the declaration, so a head that carries them carried them from the start.
GENERATED_COMPONENT = re.compile(
    r"_.*|eq_\d+|eq_def|eq_unfold|match_\d+(_\d+)*|proof_\d+"
    r"|induct(_unfolding)?|fun_cases(_unfolding)?|congr_simp|hcongr_\d+")


def comment_regions(text: str) -> list[tuple[int, int]]:
    """Offsets of every comment and docstring region, block comments nesting as Lean's do.

    String literals are skipped, so that a `--` or `/-` inside one does not open a region.
    """
    regions = []
    i, n = 0, len(text)
    while i < n:
        if text.startswith("--", i):
            j = text.find("\n", i)
            if j == -1:
                j = n
            regions.append((i, j))
            i = j
        elif text.startswith("/-", i):
            depth, j = 1, i + 2
            start = j
            while j < n and depth > 0:
                if text.startswith("/-", j):
                    depth += 1
                    j += 2
                elif text.startswith("-/", j):
                    depth -= 1
                    j += 2
                else:
                    j += 1
            regions.append((start, j - 2 if depth == 0 else n))
            i = j
        elif text[i] == '"':
            j = i + 1
            while j < n:
                if text[j] == "\\":
                    j += 2
                elif text[j] == '"':
                    j += 1
                    break
                else:
                    j += 1
            i = j
        else:
            i += 1
    return regions


def is_name_shaped(s: str) -> bool:
    """Whether `s` could be a Lean name: dot-separated components of identifier characters."""
    parts = s.split(".")
    if len(parts) < 2:
        return False
    for p in parts:
        if not p or not (p[0].isalpha() or p[0] == "_"):
            return False
        if any(not (c.isalnum() or c in "_'!?") for c in p):
            return False
    return True


def candidates(repo: str | None = None) -> dict[str, list[tuple[str, int]]]:
    """Every candidate name in the tree, as a map from the name to the places it occurs.

    `repo` is the checkout to walk, defaulting to the one this file lives in.  It is a parameter
    and not the module-level `REPO` so that two trees can be scanned in one process, which is
    what `--diff` needs and what the `os.chdir` driver this replaced could not do.

    **The elided citations are not in here and never were**, which is what keeps the two figures
    this returns comparable across the change that started checking them; `scan_prose` returns
    those separately and the module docstring says why they are a population of their own.  So
    this is the whole of what `--diff` compares and of what the headline counts, as before.
    """
    found, _, _ = scan_prose(repo)
    return found


def prose_files(repo: str) -> list[str]:
    """Every `.lean` file the walk reads, sorted, as absolute paths.

    The two loops differ in one line and it is the reason `PROSE_DIRS` is a separate constant: a
    library root has a `<name>.lean` module beside the directory and is `open`ed unconditionally,
    while a prose directory has none and `scripts.lean` does not exist.  `os.walk` on a directory
    that is not there yields nothing rather than raising, so a `PROSE_DIRS` entry absent from a
    tree costs a silent zero — which is what lets `--self-test` plant fixtures with no `scripts/`
    and what would let a `--diff` base predating this change be scanned without special-casing.
    """
    paths = []
    for root in ROOTS:
        for dirpath, _, filenames in os.walk(os.path.join(repo, root)):
            paths += [os.path.join(dirpath, f) for f in filenames if f.endswith(".lean")]
        paths.append(os.path.join(repo, root + ".lean"))
    for extra in PROSE_DIRS:
        for dirpath, _, filenames in os.walk(os.path.join(repo, extra)):
            paths += [os.path.join(dirpath, f) for f in filenames if f.endswith(".lean")]
    return sorted(paths)


def scan_prose(repo: str | None = None) -> tuple[dict[str, list[tuple[str, int]]],
                                                 dict[str, list[tuple[str, int]]],
                                                 dict[str, list[tuple[str, int]]]]:
    """One walk, three populations: plain candidates, elided citations, and the dotless rest.

    Returned in that order, each in the `candidates()` shape — name to the places it occurs — and
    **the second and third are keyed without their `…`**, so `` `…Ns.decl` `` is `Ns.decl`.  The
    one walk is what keeps the three exhaustive of each other: a backticked run that begins with
    `…` is in exactly one of the last two or in neither, never in the first, and a run that does
    not begin with `…` can only be in the first.

    The third population is not resolved against anything; see "Elided citations" in the module
    docstring for the measurement that says a dotless `` `…decl` `` elides a prefix of the last
    *component* and so is not a name at all.  It is returned rather than dropped so that the
    report can print its size, because a class nobody counts is how this one got to 165
    occurrences without a check.

    A run beginning with `…` whose remainder is neither name-shaped nor dotless-identifier-shaped
    is in none of the three — `` `…Foo.bar…` `` would be, with an elision at each end.  **There
    are none at `daeb942`**, and the shape is named here so that the exhaustiveness above is read
    as the two-of-three claim it is rather than as an all-three one.
    """
    repo = REPO if repo is None else repo
    found: dict[str, list[tuple[str, int]]] = {}
    elided: dict[str, list[tuple[str, int]]] = {}
    dotless: dict[str, list[tuple[str, int]]] = {}
    for path in prose_files(repo):
        rel = os.path.relpath(path, repo)
        with open(path, encoding="utf-8") as f:
            text = f.read()
        for (a, b) in comment_regions(text):
            for m in re.finditer(r"`([^`\s]+)`", text[a:b]):
                s = m.group(1)
                site = (rel, text.count("\n", 0, a + m.start()) + 1)
                if s.startswith(ELLIPSIS):
                    rest = s[len(ELLIPSIS):]
                    if is_name_shaped(rest):
                        elided.setdefault(rest, []).append(site)
                    elif "." not in rest and rest and (rest[0].isalpha() or rest[0] == "_"):
                        dotless.setdefault(rest, []).append(site)
                elif "." in s and is_name_shaped(s):
                    found.setdefault(s, []).append(site)
    return found, elided, dotless


def scan(dump: str, wanted: set[str],
         heads: set[str]) -> tuple[set[str], set[str], set[str], set[str], dict[str, str],
                                   int, bool]:
    """One pass over the dump, classifying `wanted` and `heads` against every name in it.

    A *suffix* is a run of whole components reaching the end of the name; a *namespace* is a run
    of whole components with at least one component after it, **where that next component is one
    an author wrote**; a *root namespace* is a namespace run that also starts at the first
    component.  Iterating over the dump and testing its runs against the two small sets, rather
    than indexing every run of every name, keeps this linear in the dump with nothing but those
    sets held in memory.

    Each line of the dump is `<kind>` TAB `<name>` with `kind` either `module` or `decl`, and a
    name never contains a tab.  **An untagged line is read as a declaration**, so a dump written
    before `scripts/DumpEnvNames.lean` grew the tag still parses; `tagged` in the return says
    whether any tag was seen, and the caller says so on stderr rather than quietly treating a
    module as a term.  The two resolution sets are what the tag is for: the suffix and module
    rules take either kind, and the *field-notation* rule takes only `resolved_decl`, because a
    module has no fields.

    The `GENERATED_COMPONENT` condition is the one thing here that is not the obvious reading of
    "namespace".  Without it a `def` becomes a namespace the moment any tactic anywhere unfolds
    it, because that plants an equation lemma under its own name — so the classification would
    depend on which files happen to contain a `rw [thatDef]`, and it would turn *off* the
    field-notation rule for citations of that definition in unrelated files.

    Returns `(resolved, resolved_decl, namespaces, root_namespaces, namespace_cause, lines,
    tagged)`, `namespace_cause` being one witness per namespace: the **first** run this pass meets
    that put it there, which is what the finding message needs in order to say why field notation
    was not tried.  It is the head
    plus the one component after it, so it need not be a name in the dump — against a dump whose
    only `Planted` entry is `Planted.Sub.child` the witness is `Planted.Sub` — and where a head
    has several children it is the one the dump happens to list first, not the shortest.  Neither
    weakens what the message is for: when a head's children are *all* generated, every candidate
    witness is one of them, so a suffix `GENERATED_COMPONENT` is missing always gets named.
    """
    resolved: set[str] = set()
    resolved_decl: set[str] = set()
    namespaces: set[str] = set()
    root_namespaces: set[str] = set()
    namespace_cause: dict[str, str] = {}
    lines = 0
    tagged = False
    with open(dump, encoding="utf-8") as f:
        for line in f:
            full = line.rstrip("\n")
            if not full:
                continue
            kind, tab, rest = full.partition("\t")
            if tab:
                tagged = True
                full, is_module = rest, kind == "module"
            else:
                is_module = False
            lines += 1
            parts = full.split(".")
            last = len(parts) - 1
            for i in range(len(parts)):
                run = parts[i]
                for j in range(i, len(parts)):
                    if j > i:
                        run += "." + parts[j]
                    if j == last:
                        if run in wanted:
                            resolved.add(run)
                            if not is_module:
                                resolved_decl.add(run)
                    elif run in heads and not GENERATED_COMPONENT.fullmatch(parts[j + 1]):
                        namespaces.add(run)
                        namespace_cause.setdefault(run, ".".join(parts[:j + 2]))
                        if i == 0:
                            root_namespaces.add(run)
    return (resolved, resolved_decl, namespaces, root_namespaces, namespace_cause, lines,
            tagged)


def scan_elided(dump: str, tails: set[str]) -> tuple[dict[str, set[str]], dict[str, set[str]],
                                                     dict[str, int]]:
    """A second pass over the dump, resolving `…`-elided citations by proper component-run suffix.

    A separate pass and not another parameter to `scan`: the two ask different questions of the
    same lines — `scan` wants runs that reach the end *or* have something after them, keyed on two
    small sets, while this wants only runs that reach the end and start after the first component,
    plus a witness for the final component alone.  Folding them together would have meant a third
    condition inside the innermost loop of a function whose contract four self-test checks pin.
    Reading 337k lines twice costs well under a second and the check has already spent nine on the
    import.

    Returns `(resolutions, witnesses, occurrences)`.

    * `resolutions[tail]` is every full name ending in `tail` as a run of whole components **with
      at least one component before it**.  Empty means unresolved; more than one means the
      citation is ambiguous, which is a figure here and not a finding — see the module docstring.
    * `witnesses[last]`, for the *final component* of each tail, is up to `MAX_WITNESSES` of the
      names ending in it.  This is what a finding's message uses to say where the component does
      occur, which is the difference between "you made a typo" and "you named the wrong
      namespace", and the second is the defect that motivated the whole rule.
    * `occurrences[last]` is how many there are in total, because the witnesses are capped and a
      message that shows three of forty must say so.

    Modules count, as they do for the plain suffix and module rules: a docstring cites
    `…AnalyticSpace.PullbackGlue` in the same form as a declaration.  Field notation does not
    arise — the head of an elided citation is by construction not written out, so there is no head
    to notate on.
    """
    finals = {t.rsplit(".", 1)[-1] for t in tails}
    resolutions: dict[str, set[str]] = {t: set() for t in tails}
    witnesses: dict[str, set[str]] = {f: set() for f in finals}
    occurrences: dict[str, int] = {f: 0 for f in finals}
    with open(dump, encoding="utf-8") as f:
        for line in f:
            full = line.rstrip("\n")
            if not full:
                continue
            _, tab, rest = full.partition("\t")
            if tab:
                full = rest
            parts = full.split(".")
            last = parts[-1]
            if last not in finals:
                continue
            occurrences[last] += 1
            if len(witnesses[last]) < MAX_WITNESSES:
                witnesses[last].add(full)
            # Runs that reach the end and start after the first component: `i` from 1, never 0,
            # which is the whole of what makes this a *proper* suffix and the `…` mean something.
            for i in range(1, len(parts)):
                run = ".".join(parts[i:])
                if run in resolutions:
                    resolutions[run].add(full)
    return resolutions, witnesses, occurrences


def read_ignore(repo: str | None = None) -> set[str]:
    path = os.path.join(REPO if repo is None else repo, IGNORE_FILE)
    if not os.path.exists(path):
        return set()
    out = set()
    with open(path, encoding="utf-8") as f:
        for line in f:
            line = line.split("#", 1)[0].strip()
            if line:
                out.add(line)
    return out


def build_dump(repo: str | None = None) -> str:
    """Run `scripts/DumpEnvNames.lean` in `repo` and return the path it wrote."""
    repo = REPO if repo is None else repo
    fd, path = tempfile.mkstemp(prefix="oka-env-names-", suffix=".txt")
    os.close(fd)
    proc = subprocess.run(
        ["lake", "env", "lean", DUMP_SCRIPT], cwd=repo,
        env=dict(os.environ, OKA_ENV_NAME_DUMP=path), capture_output=True, text=True,
    )
    if proc.returncode != 0 or not os.path.getsize(path):
        sys.stderr.write(proc.stdout + proc.stderr)
        sys.stderr.write(
            "\nFailed to dump the environment of `Oka`. `lake build` must have run\n"
            "first: this reads the oleans, it does not produce them.\n"
        )
        os.unlink(path)
        sys.exit(2)
    return path


def report(repo: str, found: dict[str, list[tuple[str, int]]]) -> str:
    """The one line that names a tree and its two figures, in the headline's own wording."""
    total = sum(len(v) for v in found.values())
    return f"{repo}: {total} backticked names ({len(found)} distinct)"


def check_tree(path: str, what: str) -> str:
    """Resolve a `--tree` / `--diff` argument, failing loudly rather than on a missing file.

    Without this a mistyped path reaches `candidates`, which walks a directory that is not there
    — `os.walk` on a missing directory yields nothing rather than raising — and then dies on
    `Oka.lean` with a bare `FileNotFoundError`.  A worktree that has not been created yet is the
    common case and it deserves a sentence.
    """
    real = os.path.realpath(path)
    if not all(os.path.exists(os.path.join(real, f + ".lean")) for f in ROOTS):
        sys.stderr.write(
            f"{what} {path!r} is not a checkout of this repository: expected "
            + " and ".join(f"{f}.lean" for f in ROOTS) + f" under {real}.\n"
            "Create the base with `git worktree add /tmp/<dir> <sha>`.\n")
        sys.exit(2)
    return real


def site_map(found: dict[str, list[tuple[str, int]]]) -> dict[str, dict[str, list[int]]]:
    """`name -> file -> sorted lines`, which is `candidates()` regrouped and nothing more."""
    out: dict[str, dict[str, list[int]]] = {}
    for name, sites in found.items():
        per = out.setdefault(name, {})
        for path, line in sites:
            per.setdefault(path, []).append(line)
    for per in out.values():
        for lines in per.values():
            lines.sort()
    return out


def site_changes(base_found: dict[str, list[tuple[str, int]]],
                 tree_found: dict[str, list[tuple[str, int]]]
                 ) -> tuple[dict[str, list[tuple[str, int, int]]],
                            dict[str, list[tuple[str, int]]],
                            dict[str, list[tuple[str, int]]]]:
    """Where every occurrence sits, compared per name **and per file**.

    Returns `(moved, added, removed)`, each keyed by file.  A name keeps its count in a file, so
    its lines pair up in order and each changed pair is a *move* — that is the common case, since
    inserting a line shifts every citation below it by the same amount.  When the count in that
    file changes, the lines are reported as added and removed instead and no pairing is guessed:
    a name that gains an occurrence *and* shifts in the same file shows up as several additions
    and removals rather than as one gain plus some moves, and saying so is cheaper than a
    heuristic that would be wrong somewhere.  Keying by file keeps a gain in one file from
    disturbing the pairing in another.

    **That difference is a multiset difference and not a set one**, because `candidates()`
    returns one entry per *occurrence*: a name backticked twice on one line is two entries with
    the same line number, so under `set` a line that loses one of a pair cancels against itself
    and the whole report comes out empty — the same-tree output, on trees that differ.  Five
    lines on `master` carry a name twice, so it is not hypothetical.  `Counter` is what keeps the
    promise the paragraph above makes.
    """
    before, after = site_map(base_found), site_map(tree_found)
    moved: dict[str, list[tuple[str, int, int]]] = {}
    added: dict[str, list[tuple[str, int]]] = {}
    removed: dict[str, list[tuple[str, int]]] = {}
    for name in sorted(set(before) | set(after)):
        per_before, per_after = before.get(name, {}), after.get(name, {})
        for path in sorted(set(per_before) | set(per_after)):
            was, now = per_before.get(path, []), per_after.get(path, [])
            if was == now:
                continue
            if len(was) == len(now):
                for old_line, new_line in zip(was, now):
                    if old_line != new_line:
                        moved.setdefault(path, []).append((name, old_line, new_line))
            else:
                was_at, now_at = collections.Counter(was), collections.Counter(now)
                for line in sorted((was_at - now_at).elements()):
                    removed.setdefault(path, []).append((name, line))
                for line in sorted((now_at - was_at).elements()):
                    added.setdefault(path, []).append((name, line))
    return moved, added, removed


def print_sites(moved: dict[str, list[tuple[str, int, int]]],
                added: dict[str, list[tuple[str, int]]],
                removed: dict[str, list[tuple[str, int]]]) -> None:
    """The `--sites` half of the report: every occurrence that is not where it was.

    Grouped by file, with each file's line named once, because a one-line insertion moves every
    citation below it and the interesting thing is then the *shape* — one file, one delta — and
    not the list.  The list is printed anyway and nothing is truncated: a report that silently
    caps reads as "that was all of it".
    """
    files = sorted(set(moved) | set(added) | set(removed))
    total_moved = sum(len(v) for v in moved.values())
    total_added = sum(len(v) for v in added.values())
    total_removed = sum(len(v) for v in removed.values())
    print(f"sites {total_moved} moved, {total_added} added, {total_removed} removed, "
          f"in {len(files)} file(s)")
    if not files:
        print("  (none)")
    for path in files:
        deltas = {new - old for _, old, new in moved.get(path, [])}
        shape = f"{len(moved.get(path, []))} moved"
        if len(deltas) == 1:
            shape += f", all {next(iter(deltas)):+d}"
        elif deltas:
            shape += f", deltas {min(deltas):+d}..{max(deltas):+d}"
        for label, count in (("added", len(added.get(path, []))),
                             ("removed", len(removed.get(path, [])))):
            if count:
                shape += f", {count} {label}"
        print(f"  {path} \u2014 {shape}")
        for name, old_line, new_line in sorted(moved.get(path, []), key=lambda s: s[1]):
            print(f"    ~ {old_line} \u2192 {new_line} ({new_line - old_line:+d})\t{name}")
        for name, line in sorted(added.get(path, []), key=lambda s: s[1]):
            print(f"    + {line}\t{name}")
        for name, line in sorted(removed.get(path, []), key=lambda s: s[1]):
            print(f"    - {line}\t{name}")


def diff_trees(base: str, tree: str, sites: bool = False) -> int:
    """Print the added and removed *distinct* candidate names between two checkouts.

    Both trees are scanned by this file's rules; see the module docstring for why, and for what
    that hides.  This is a reporter and not a gate, so it exits 0 whatever the diff is.  A removal
    is not by itself a defect: a name leaves the
    set when the last docstring citing it is reworded, which is what most prose commits do.

    With `sites`, the per-occurrence report follows; see the module docstring for the branch that
    needs it.  The summary above it is unchanged, so a body that quotes the two figures reads the
    same with the flag and without.

    **The elided citations get their own summary line and their own added/removed lists, and are
    in neither of the two figures**, for the reason the module docstring gives.  `--sites` is
    about the plain population only: a moved elided citation is not reported, and that is the one
    thing this report is now silent about that it could be made to say.  It is left out because
    the `name -> file -> lines` pairing `site_changes` does would have to be duplicated for a
    second population to say it, and nothing has asked for it; the summary line moves whenever an
    elided citation is added or removed, which is what a body needs.
    """
    base_found, base_elided, _ = scan_prose(base)
    tree_found, tree_elided, _ = scan_prose(tree)
    added = sorted(set(tree_found) - set(base_found))
    removed = sorted(set(base_found) - set(tree_found))
    print("base   " + report(base, base_found))
    print("branch " + report(tree, tree_found))
    print(f"distinct {len(base_found)} \u2192 {len(tree_found)}: "
          f"{len(added)} added, {len(removed)} removed")
    for label, names, where in (("added", added, tree_found), ("removed", removed, base_found)):
        print(f"{label}:")
        if not names:
            print("  (none)")
        for name in names:
            path, line = where[name][0]
            extra = f" (+{len(where[name]) - 1} more)" if len(where[name]) > 1 else ""
            print(f"  {name}\t{path}:{line}{extra}")
    # The elided population, reported beside the plain one and never folded into it.  A branch
    # that adds an elided citation moves neither figure `report` prints nor the `added`/`removed`
    # lists, which is how the class reached 165 occurrences with no figure of its own in any run
    # of this script.
    el_added = sorted(set(tree_elided) - set(base_elided))
    el_removed = sorted(set(base_elided) - set(tree_elided))
    print(f"elided {sum(len(v) for v in base_elided.values())} ({len(base_elided)} distinct) "
          f"\u2192 {sum(len(v) for v in tree_elided.values())} ({len(tree_elided)} distinct): "
          f"{len(el_added)} added, {len(el_removed)} removed")
    for label, names, where in (("added", el_added, tree_elided),
                                ("removed", el_removed, base_elided)):
        print(f"elided {label}:")
        if not names:
            print("  (none)")
        for name in names:
            path, line = where[name][0]
            extra = f" (+{len(where[name]) - 1} more)" if len(where[name]) > 1 else ""
            print(f"  {ELLIPSIS}{name}\t{path}:{line}{extra}")
    if sites:
        print_sites(*site_changes(base_found, tree_found))
    return 0


def self_test() -> int:
    """Plant two fixture trees that differ and assert the diff names the difference.

    **The test that matters is the positive one.**  "Two identical trees diff to empty" is what
    the `os.chdir` driver this option replaced printed on every branch it was ever run on, so a
    self-test built only from that would have passed while measuring nothing.  **Every check below
    carries a `positive:` or `negative:` label and there are twenty-five and eleven** — a count is
    stated here rather than left to be inferred because a reader who trusts the labels has to be
    able to see that none is missing.  **It was eighteen and eight until 2026-09-19**, when the
    elided-citation block below added seven and three; `grep -c '^ *check("positive: '` on this
    file is the check on this sentence and it is one command.  **The anchor is load-bearing**: a
    pattern written against the bare label alone matches this sentence too, which publishes it,
    and returns one more than the number it is published to check.

    Twenty of them are about the *rules* rather than about the walk, and they reach them by
    planting an environment as a `--dump` file instead of building one.  That is the only way to
    hold everything fixed but the environment, which is the variable the field-notation rule turns
    on, and it keeps the whole self-test free of `lake`.  Four of those are about the
    `module`/`decl` tag: a module head must be *reported*, a declaration head with the same shape
    must not be, the message must say which of the two declined it, and an untagged dump must
    revert loudly rather than silently.

    **Four are about the walk and arrived with taxis #1337**, which found that `scripts/` had
    never been in it.  They are one positive — a name in a `scripts/*.lean` docstring is read and
    reported — and three controls that fix the boundary on both sides, so that neither narrowing
    the walk back nor widening it to everything passes here.

    **The last ten are the elided citations and arrived with taxis #2056.**  They are the only
    block here whose positive control is a defect this repository actually shipped: two citations
    of declarations that do not exist, green through three rounds and two graders because the
    checker could not see the spelling they were written in.  Four of the ten fix decisions
    rather than behaviour — that ambiguity is a figure, that the two headline figures do not move,
    that a dotless `…name` is out of scope, and that a match which is the whole name is not a
    proper suffix — because each of those is a place where a later change could be *more*
    thorough and be wrong for it.
    """
    def plant(root: str, body: str) -> str:
        os.makedirs(os.path.join(root, "Oka"), exist_ok=True)
        with open(os.path.join(root, "Oka.lean"), "w", encoding="utf-8") as h:
            h.write("import Oka.Fixture\n")
        with open(os.path.join(root, "Oka", "Fixture.lean"), "w", encoding="utf-8") as h:
            h.write(body)
        return root

    failures: list[str] = []

    def check(label: str, ok: bool, detail: str = "") -> None:
        print(f"{'ok  ' if ok else 'FAIL'} {label}" + (f" \u2014 {detail}" if detail else ""))
        if not ok:
            failures.append(label)

    with tempfile.TemporaryDirectory(prefix="oka-docstring-names-selftest-") as tmp:
        shared = "/-! `Shared.one` and `Shared.one` again, plus `Shared.two`. -/\n"
        a = plant(os.path.join(tmp, "a"), shared + "/-- `Only.inA` -/\ndef f := 1\n")
        b = plant(os.path.join(tmp, "b"), shared + "/-- `Only.inB` -/\ndef f := 1\n")

        ca, cb = candidates(a), candidates(b)

        # POSITIVE control, and the only one the broken driver fails.  Both trees are scanned in
        # one process, which is exactly what `os.chdir` could not make happen.
        # Note the two counts are *equal* here, on purpose: a driver that compares only the
        # `M distinct` figures passes a pair of trees whose name sets differ.
        check("positive: two trees scanned in one process differ", set(ca) != set(cb),
              f"{len(ca)} vs {len(cb)} distinct, and the sets differ")
        check("positive: the added name is the one planted",
              sorted(set(cb) - set(ca)) == ["Only.inB"], str(sorted(set(cb) - set(ca))))
        check("positive: the removed name is the one planted",
              sorted(set(ca) - set(cb)) == ["Only.inA"], str(sorted(set(ca) - set(cb))))

        # Negative control.  Stated as such: the driver this replaced passed this one too.
        check("negative: a tree against itself diffs to empty",
              set(ca) == set(candidates(a)))

        # The defect itself, asserted rather than described: `os.chdir` does not move the walk,
        # because `REPO` is bound at import from `__file__`.  This is the one check that scans
        # the real tree, and it is why the parameter above had to exist.
        cwd = os.getcwd()
        try:
            os.chdir(a)
            check("negative: `os.chdir` does not move the walk (the defect this option fixes)",
                  set(candidates()) != set(ca) and set(candidates()) == set(candidates(REPO)),
                  f"{len(candidates())} distinct from {REPO} while cwd is the fixture")
        finally:
            os.chdir(cwd)

        # Occurrences are counted per site, distinct names once.  The headline's two figures.
        check("positive: occurrences count every site", len(ca.get("Shared.one", [])) == 2,
              str(ca.get("Shared.one")))
        check("positive: `Shared.two` is one occurrence", len(ca.get("Shared.two", [])) == 1)

        # The case `--sites` exists for, and the one every other check here is blind to: a tree
        # with a line inserted above the citations.  Identical name sets, identical occurrence
        # counts, every moved site at the same delta.  The assertion is on the *set* of deltas
        # and not on a number of moves: `shared` carries three citations, so the number here is
        # four, and a number written down would go stale the next time a fixture gains a name.
        # A same-tree comparison returns nothing, which is what makes this a positive control
        # rather than a restatement of "two trees differ".
        d = plant(os.path.join(tmp, "d"), "/-! spacer -/\n" + shared
                  + "/-- `Only.inA` -/\ndef f := 1\n")
        cd = candidates(d)
        moved, gained, lost = site_changes(ca, cd)
        same = site_changes(ca, ca)
        check("positive: a line inserted above a citation moves its site and nothing else",
              set(ca) == set(cd)
              and sum(len(v) for v in ca.values()) == sum(len(v) for v in cd.values())
              and not gained and not lost
              and {n - o for sites in moved.values() for _, o, n in sites} == {1}
              and same == ({}, {}, {}),
              f"{sum(len(v) for v in moved.values())} moved, "
              f"{len(gained)} added, {len(lost)} removed; same-tree {same}")

        # The other way a site report can go silent, and it is the one `set` made it go silent
        # *by construction*: two citations of one name on one line are two entries with the same
        # line number, so dropping one of them cancels under a set difference.  Here the name
        # sets are identical, the occurrence totals differ by one, and the honest answer is one
        # removed site — which the pairing branch never sees, because the counts are unequal.
        e = plant(os.path.join(tmp, "e"), "/-! `Dup.name` and `Dup.name` again. -/\n")
        g = plant(os.path.join(tmp, "g"), "/-! `Dup.name` once. -/\n")
        ce, cg = candidates(e), candidates(g)
        dropped = site_changes(ce, cg)
        check("positive: dropping one of two citations of a name on one line is a removed site",
              set(ce) == set(cg)
              and sum(len(v) for v in ce.values()) - sum(len(v) for v in cg.values()) == 1
              and dropped == ({}, {}, {"Oka/Fixture.lean": [("Dup.name", 1)]})
              and site_changes(ce, ce) == ({}, {}, {}),
              f"{sum(len(v) for v in ce.values())} → "
              f"{sum(len(v) for v in cg.values())} occurrences; {dropped[2]}")

        # Candidacy is a property of comment regions, so code is not scanned.
        c = plant(os.path.join(tmp, "c"), "/-! nothing here -/\ndef g := `NotA.candidate\n")
        check("negative: a backtick outside a comment is not a candidate",
              "NotA.candidate" not in candidates(c), str(sorted(candidates(c))))

        # The CLI itself, end to end, because a recipe that is quoted has to be executable as
        # printed.  `--diff` must not need a build.
        proc = subprocess.run(
            [sys.executable, os.path.abspath(__file__), "--diff", a, "--tree", b],
            capture_output=True, text=True, env=dict(os.environ, PYTHONDONTWRITEBYTECODE="1"))
        check("positive: the CLI runs `--diff` with no build and reports the added name",
              proc.returncode == 0 and "Only.inB" in proc.stdout,
              proc.stdout.strip().replace("\n", " | ") or proc.stderr.strip())

        bad = subprocess.run(
            [sys.executable, os.path.abspath(__file__), "--diff",
             os.path.join(tmp, "does-not-exist")],
            capture_output=True, text=True, env=dict(os.environ, PYTHONDONTWRITEBYTECODE="1"))
        check("positive: a path that is not a checkout is reported, not a traceback",
              bad.returncode == 2 and "Traceback" not in bad.stderr
              and "is not a checkout" in bad.stderr,
              bad.stderr.strip().replace("\n", " | ") or f"rc={bad.returncode}")

        # The field-notation rule, against a *planted environment* rather than the real one.
        # `--dump` is what makes this possible without a build: the four runs below differ only
        # in which names the environment contains, which is exactly the variable under test.
        h = plant(os.path.join(tmp, "h"), "/-! `Planted.someField` -/\n")

        def env(name: str, *names: str) -> str:
            path = os.path.join(tmp, name)
            with open(path, "w", encoding="utf-8") as f:
                f.write("".join(n + "\n" for n in names))
            return path

        def run_on(dump: str) -> subprocess.CompletedProcess:
            return subprocess.run(
                [sys.executable, os.path.abspath(__file__), "--tree", h, "--dump", dump],
                capture_output=True, text=True,
                env=dict(os.environ, PYTHONDONTWRITEBYTECODE="1"))

        # The control: `Planted` resolves and has nothing under it, so `Planted.someField` is
        # field notation on a definition and is accepted.  Without this the two checks after it
        # could both pass on a script that accepts everything.
        bare = run_on(env("env-bare.txt", "Planted", "Unrelated.decl"))
        check("positive: field notation on a definition with no children is accepted",
              bare.returncode == 0 and "names nothing" not in bare.stdout,
              bare.stdout.strip().replace("\n", " | "))

        # **The defect.**  A tactic in some other file unfolds `Planted`, Lean plants its equation
        # lemma, and the citation above — untouched, in a file nobody edited — starts failing.
        # This is the check that fails on the un-fixed script, where it exits 1.
        eqn = run_on(env("env-eq.txt", "Planted", "Planted.eq_1", "Planted._proof_1",
                         "Unrelated.decl"))
        check("positive: a generated equation lemma does not make its definition a namespace",
              eqn.returncode == 0 and "names nothing" not in eqn.stdout,
              eqn.stdout.strip().replace("\n", " | ") or "rc=0, nothing reported")

        # The same defect one suffix over, and the reason this check exists as well as the one
        # above: `eq_1` was the first instance and not the class.  Each name here is planted by a
        # tactic in some *other* file — a congruence lemma for `simp` or `grind`, the companions
        # of `fun_induction` and `fun_cases`, a nested `match` auxiliary — so each of them turns
        # the field-notation rule off at a distance exactly as `eq_1` did.  **This check fails on
        # a script whose `GENERATED_COMPONENT` is missing any one of the five**, which is what
        # makes it an assertion about the list rather than about `congr_simp`.
        gen = run_on(env("env-gen.txt", "Planted", "Planted.congr_simp", "Planted.hcongr_3",
                         "Planted.match_1_1", "Planted.induct_unfolding",
                         "Planted.fun_cases_unfolding", "Unrelated.decl"))
        check("positive: the on-demand generated components do not make a definition a namespace",
              gen.returncode == 0 and "names nothing" not in gen.stdout,
              gen.stdout.strip().replace("\n", " | ") or "rc=0, nothing reported")

        # And the boundary, which is the half of the audit that is a judgement: `congr` is *not*
        # in the list.  It is the sole non-generated child of seven heads in this environment and
        # so looks exactly like `congr_simp` to the audit, but `EventuallyMeasurableSet.congr`
        # and `LinearMap.Nondegenerate.congr` are Mathlib lemmas somebody wrote.  A script that
        # added it by pattern-matching on the suffix would pass every other check here.
        near = run_on(env("env-congr.txt", "Planted", "Planted.congr", "Unrelated.decl"))
        check("negative: `congr` is not a generated component and still blocks field notation",
              near.returncode == 1 and "`Planted.someField` names nothing" in near.stdout,
              near.stdout.strip().replace("\n", " | ") or f"rc={near.returncode}")

        # The half of the rule that must survive the fix, and would not survive deleting the
        # namespace condition: an author-written declaration under the head still means the head
        # is a namespace and `Planted.someField` is a misspelling rather than field notation.
        real = run_on(env("env-real.txt", "Planted", "Planted.realChild", "Unrelated.decl"))
        check("negative: a declaration an author wrote still blocks field notation",
              real.returncode == 1 and "`Planted.someField` names nothing" in real.stdout,
              real.stdout.strip().replace("\n", " | ") or f"rc={real.returncode}")

        # And the message says *why*, naming both the head and the declaration that made it a
        # namespace — the two facts whose absence made the first instance of this defect take a
        # session to diagnose, and the reason a suffix missing from `GENERATED_COMPONENT` is a
        # one-line fix rather than another one.
        check("positive: the message names the head that resolves and what made it a namespace",
              "`Planted` does resolve" in real.stdout
              and "`Planted.realChild` makes it a namespace" in real.stdout,
              real.stdout.strip().replace("\n", " | "))

        # The tag, and the rule it exists for.  `env` above writes untagged lines, which the
        # checker reads as declarations, so every check up to here is about a declaration head;
        # these three are the module head, and they are the whole of taxis #1326.
        def tagged_env(name: str, *kinded: str) -> str:
            path = os.path.join(tmp, name)
            with open(path, "w", encoding="utf-8") as f:
                f.write("".join(k + "\n" for k in kinded))
            return path

        # **The defect.**  `Planted` is a module with nothing declared into it — which is what
        # every module of the former test library was, since they all declared into
        # `ComplexAnalytic` — so it resolves and is not a namespace, and before the tag existed the
        # field-notation rule
        # accepted `Planted.someField` and never looked at the tail.  A module has no fields.
        mod = run_on(tagged_env("env-module.txt", "module\tPlanted", "decl\tUnrelated.decl"))
        check("negative: field notation on a *module* head is reported",
              mod.returncode == 1 and "`Planted.someField` names nothing" in mod.stdout,
              mod.stdout.strip().replace("\n", " | ") or f"rc={mod.returncode}")

        # ...and the message says which of the two reasons declined it, because "names nothing"
        # about a head that plainly does resolve is the report that costs a reader a session.
        check("positive: the message says the head resolves only as a module",
              "only as a **module**" in mod.stdout,
              mod.stdout.strip().replace("\n", " | "))

        # The control that makes the one above a statement about the *tag* and not about the
        # fixture: the same two names, the same shape, `Planted` tagged as a declaration instead.
        # Without this, a script that reported every tagged dump would pass.
        dec = run_on(tagged_env("env-decl.txt", "decl\tPlanted", "decl\tUnrelated.decl"))
        check("positive: field notation on a declaration head is still accepted, tag and all",
              dec.returncode == 0 and "names nothing" not in dec.stdout,
              dec.stdout.strip().replace("\n", " | ") or "rc=0, nothing reported")

        # A dump from a checkout older than the tag has no kinds in it.  It must still parse, it
        # must revert to the behaviour that dump was written for, and it must say so — a silent
        # revert is indistinguishable in the report from the fix working.
        legacy = run_on(env("env-legacy.txt", "Planted", "Unrelated.decl"))
        check("positive: an untagged dump is accepted, reverts, and says so on stderr",
              legacy.returncode == 0 and "names nothing" not in legacy.stdout
              and "no `module`/`decl` tags" in legacy.stderr,
              (legacy.stderr.strip() or legacy.stdout.strip()).replace("\n", " | "))

        # **The walk, and the boundary it stops at.**  Until 2026-08-31 `scripts/` was outside it,
        # so the two Lean helpers that describe this checker were checked by nothing; taxis #1337
        # has the measurement.  The failure mode is the one this whole file is built against — a
        # green run that measured less than the reader thinks — so it gets one positive and three
        # controls, which between them say the walk widened by exactly one directory and one
        # extension and that nothing else in the tree moved.
        #
        # Every other fixture here has no `scripts/` at all, which is why they still work: a
        # `PROSE_DIRS` entry missing from a tree costs a silent zero rather than a traceback.
        w = plant(os.path.join(tmp, "w"), "/-! `Planted.someField` -/\n")
        for sub, leaf, body in (
                ("scripts", "Tool.lean", "/-! `Walked.zzzBogus` -/\n"),
                # A Lean comment in a `.py` file, so that the *extension* filter is the only
                # thing keeping it out and a check that widened `.lean` to `*` would fail here.
                ("scripts", "Tool.py", "/-! `Unwalked.zzzPy` -/\n"),
                # A `.lean` file in a directory that is in neither list, so that the *directory*
                # list is the only thing keeping it out.
                ("docs", "Note.lean", "/-! `Unwalked.zzzDir` -/\n")):
            os.makedirs(os.path.join(w, sub), exist_ok=True)
            with open(os.path.join(w, sub, leaf), "w", encoding="utf-8") as fh:
                fh.write(body)
        walked = subprocess.run(
            [sys.executable, os.path.abspath(__file__), "--tree", w,
             "--dump", tagged_env("env-walk.txt", "decl\tPlanted", "decl\tUnrelated.decl")],
            capture_output=True, text=True,
            env=dict(os.environ, PYTHONDONTWRITEBYTECODE="1"))
        check("positive: a name in a `scripts/*.lean` docstring is read and reported",
              walked.returncode == 1 and "Walked.zzzBogus" in walked.stdout
              and "scripts/Tool.lean" in walked.stdout,
              walked.stdout.strip().replace("\n", " | ") or f"rc={walked.returncode}")
        check("negative: a `.py` file under `scripts/` is not read",
              "Unwalked.zzzPy" not in walked.stdout)
        check("negative: a `.lean` file outside the walked directories is not read",
              "Unwalked.zzzDir" not in walked.stdout)
        # Absence from stdout is also what a run that never read `Oka/Fixture.lean` would print,
        # so the headline is asserted too: exactly two candidates were read — the planted one and
        # the bogus one under `scripts/` — and exactly one of them failed.
        check("positive: `Planted.someField` in the same tree still resolves",
              "Planted.someField" not in walked.stdout
              and "2 backticked names (2 distinct)" in walked.stdout
              and "1 unresolved" in walked.stdout,
              "the run above reports one name and it is the planted one")

        # **Elided citations, and this is the planted-defect control taxis #2056 asks for.**
        # Until 2026-09-19 a citation beginning `…` was not a candidate at all — `is_name_shaped`
        # rejects a component that does not begin with a letter or `_` — so the checker was green
        # on `Oka/AnalyticSpace/GaloisCategory.lean`'s two citations of declarations that did not
        # exist, through three rounds and two graders.  A rule whose whole content is *and now it
        # is not green on that* is worth exactly as much as the fixture that shows it, so the
        # fixture is here and the two shapes below are the two real defects: a tail whose final
        # component exists **under another namespace**, and one that exists nowhere.
        el_env = tagged_env(
            "env-elided.txt",
            "decl\tPlanted.Right.foo", "decl\tPlanted.Other.bar", "module\tPlanted.Mod.Fixture",
            "decl\tFirst.Amb.thing", "decl\tSecond.Amb.thing", "decl\tExact.name",
            "decl\tUnrelated.decl")

        def run_tree(tree: str, dump: str = el_env) -> subprocess.CompletedProcess:
            return subprocess.run(
                [sys.executable, os.path.abspath(__file__), "--tree", tree, "--dump", dump],
                capture_output=True, text=True,
                env=dict(os.environ, PYTHONDONTWRITEBYTECODE="1"))

        good = run_tree(plant(os.path.join(tmp, "el-good"),
                              "/-! `Unrelated.decl`, `…Right.foo`, `…Mod.Fixture` and "
                              "`…Amb.thing`. -/\n"))
        check("positive: an elided citation resolving as a proper component run is accepted",
              good.returncode == 0 and "…Right.foo` names nothing" not in good.stdout,
              good.stdout.strip().replace("\n", " | "))
        check("positive: an elided citation of a *module* resolves",
              "…Mod.Fixture` names nothing" not in good.stdout,
              "the module rule takes either kind, as it does for a written-out name")
        # Ambiguity is a figure and not a finding, and this is where that decision lives.  Six
        # citations at `daeb942` resolve under more than one namespace and every one is correct —
        # `…Pullback.hasPullback_of_cover` is ambiguous between Mathlib's and this repository's —
        # so gating on it would report six right sentences, which is how a check earns an
        # ignore-list and stops being a check.
        check("positive: an elided citation with two resolutions is counted, not reported",
              good.returncode == 0
              and "3 elided citations (3 distinct): 0 unresolved, 1 resolving under more than "
                  "one namespace" in good.stdout,
              good.stdout.strip().replace("\n", " | "))
        # The population separation, asserted rather than described: three elided citations sit
        # in that fixture and the headline figure every pull request body quotes says **one**.
        # Without this a later change that folded them in would pass every other check here and
        # silently make every figure in this repository's history incomparable with every one
        # written after it.
        check("negative: elided citations are not counted in the two headline figures",
              "1 backticked names (1 distinct)" in good.stdout,
              good.stdout.strip().replace("\n", " | "))

        bad = run_tree(plant(os.path.join(tmp, "el-bad"),
                             "/-! `…Wrong.foo`, `…Nothing.zzzNoSuchComponent`, "
                             "`…Exact.name` and `…zzzDotless`. -/\n"))
        check("positive: an elided citation naming nothing is reported (the defect this adds)",
              bad.returncode == 1 and "`…Wrong.foo` names nothing" in bad.stdout,
              bad.stdout.strip().replace("\n", " | ") or f"rc={bad.returncode}")
        # **The message is the deliverable and not the exit code.**  `…Wrong.foo` is spelled
        # correctly one namespace over, so a bare *names nothing* sends its author hunting for a
        # typo that is not there; that is the first of the two real defects exactly.
        check("positive: the message says where the final component does occur",
              "the final component `foo` does occur, in `Planted.Right.foo`" in bad.stdout,
              bad.stdout.strip().replace("\n", " | "))
        # ...and the other of the two, which is a different sentence because it is a different
        # defect: nothing in the tree ends in `.preservesEpis_fintypeFiberFunctor` at all.
        check("positive: a final component occurring nowhere is called a misspelling instead",
              "nothing in the environment ends in `.zzzNoSuchComponent` at all" in bad.stdout,
              bad.stdout.strip().replace("\n", " | "))
        # The `…` stands for an elided namespace, so there has to be one: a match that is the
        # *whole* name is not a proper suffix.  0 of the 107 distinct citations at `daeb942`
        # resolve only that way, so this pins a decision rather than a repair.
        check("negative: a match that is the whole name is not a proper suffix",
              "`…Exact.name` names nothing" in bad.stdout,
              bad.stdout.strip().replace("\n", " | "))
        # The scope decision, which is a measurement: read as citations the dotless forms would
        # report 29 occurrences on a tree that has no defect of that shape, because `…_of_coeff`
        # elides a prefix of a *component* and is not a name.  `zzzDotless` resolves nowhere in
        # the planted environment, so only the scope rule can be keeping it quiet.
        check("negative: a dotless `…name` is not resolved and not reported",
              "zzzDotless" not in bad.stdout
              and "1 dotless `…name` occurrences (1 distinct)" in bad.stdout,
              bad.stdout.strip().replace("\n", " | "))

        # The escape hatch reaches the new shape, and it takes the `…` with it so that ignoring
        # an elided citation cannot silently ignore the written-out name it elides.
        ign = plant(os.path.join(tmp, "el-ignore"), "/-! `…Wrong.foo`. -/\n")
        os.makedirs(os.path.join(ign, "scripts"), exist_ok=True)
        with open(os.path.join(ign, IGNORE_FILE), "w", encoding="utf-8") as fh:
            fh.write("# planted by --self-test\n…Wrong.foo\n")
        ignored_run = run_tree(ign)
        check("positive: the ignore file silences an elided citation, with its `…`",
              ignored_run.returncode == 0 and "names nothing" not in ignored_run.stdout,
              ignored_run.stdout.strip().replace("\n", " | ")
              or f"rc={ignored_run.returncode}")

    if failures:
        print(f"\n{len(failures)} check(s) failed: " + ", ".join(failures))
        return 2
    print("\nself-test passed.")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(
        description="Check that backticked dotted names in comments resolve.")
    ap.add_argument("--dump", metavar="FILE",
                    help="reuse a name dump written earlier instead of building one")
    ap.add_argument("--tree", metavar="DIR", default=REPO,
                    help="the checkout to read, defaulting to the one this script lives in")
    ap.add_argument("--diff", metavar="BASE_DIR",
                    help="report the distinct-name diff from BASE_DIR to --tree, and stop; "
                         "reads no environment, so no build is needed")
    ap.add_argument("--sites", action="store_true",
                    help="with --diff, also report every occurrence that moved, by file:line; "
                         "this is the only report a branch that only rewords can move")
    ap.add_argument("--ambiguous", action="store_true",
                    help="list the elided citations that resolve under more than one namespace; "
                         "the count is printed either way, and none of them is a finding")
    ap.add_argument("--self-test", action="store_true",
                    help="plant two fixture trees that differ and assert the diff sees it")
    args = ap.parse_args()

    if args.self_test:
        return self_test()

    repo = check_tree(args.tree, "--tree")
    if args.diff:
        return diff_trees(check_tree(args.diff, "--diff"), repo, sites=args.sites)
    if args.sites:
        sys.stderr.write("--sites reports where occurrences moved between two trees, so it needs "
                         "--diff BASE_DIR to have a second tree to move them from.\n")
        sys.exit(2)

    found, elided, dotless = scan_prose(repo)
    # Every proper prefix of every candidate is a possible head for the field-notation rule, and
    # has to be classified as resolving-or-not and as a namespace-or-not just as candidates do.
    wanted = set(found)
    heads = set()
    for name in found:
        parts = name.split(".")
        for k in range(1, len(parts)):
            heads.add(".".join(parts[:k]))
    wanted |= heads

    dump = args.dump or build_dump(repo)
    (resolved, resolved_decl, namespaces, root_namespaces, namespace_cause, dumped,
     tagged) = scan(dump, wanted, heads)
    elided_resolutions, elided_witnesses, elided_occurrences = scan_elided(dump, set(elided))
    if not args.dump:
        os.unlink(dump)
    if not tagged:
        # Not an error: the dump parses, and reverting to the pre-tag behaviour is the only thing
        # that can be done with it.  Said out loud because the difference is invisible in the
        # report — the names a module head would have swallowed are exactly the ones nobody sees.
        sys.stderr.write(
            "This dump has no `module`/`decl` tags, so it predates the ones\n"
            "`scripts/DumpEnvNames.lean` writes and modules cannot be told from declarations in\n"
            "it. Field notation is therefore accepted on a module head as it was before taxis\n"
            "#1326; rebuild the dump from this checkout to get the stricter rule.\n")
        resolved_decl = resolved

    def is_field_notation(name: str) -> bool:
        """Is `name` generalised field notation on a term, rather than a declaration reference?

        The head has to resolve to a **declaration**.  `resolved` rather than `resolved_decl`
        here is the defect taxis #1326 records: a module resolves too, and a module that is an
        empty namespace — as every module of the former test library was, its declarations being
        named into `ComplexAnalytic` — was read as a field-notation head, so any tail after it was
        never looked at.
        """
        parts = name.split(".")
        for k in range(len(parts) - 1, 0, -1):
            head = ".".join(parts[:k])
            if head in resolved_decl and head not in namespaces:
                return True
        return False

    def blocked_head(name: str) -> tuple[str, str] | None:
        """The head that resolves, and why field notation was not tried on it anyway.

        The one thing a reader of a finding cannot see from the message alone.  A head that
        resolves is a head the prose is probably right about, and *why* the rule declined it is
        a fact about something else entirely — either another declaration (see `scan`) or the
        head being a module, which has no fields to notate.
        """
        parts = name.split(".")
        for k in range(len(parts) - 1, 0, -1):
            head = ".".join(parts[:k])
            if head not in resolved:
                continue
            # The **longest** resolving head, and then why it was declined: a shorter one always
            # resolves too — `Oka` is a namespace because `Oka.Weierstrass` is a module —
            # and naming it instead sends the reader to the wrong prefix of their own citation.
            if head in namespaces:
                return head, namespace_cause.get(head, "another declaration under it")
            if head not in resolved_decl:
                return head, "module"
        return None

    def is_local_binder(name: str) -> bool:
        head = name.split(".")[0]
        return len(head) <= MAX_LOCAL_HEAD and head not in root_namespaces

    ignored = read_ignore(repo)
    findings = [
        name for name in sorted(found)
        if name not in resolved
        and name not in ignored
        and not is_local_binder(name)
        and not os.path.exists(os.path.join(repo, name))
        and not is_field_notation(name)
    ]

    for name in findings:
        for (path, line) in found[name]:
            print(f"{path}:{line}: `{name}` names nothing in the environment")
        blocked = blocked_head(name)
        if blocked:
            head, cause = blocked
            if cause == "module":
                print(f"    `{head}` does resolve, but only as a **module**, and field notation "
                      f"is on a term: a module has no fields. Cite the declaration by the name "
                      f"it is declared under, or the file by its path.")
            else:
                print(f"    `{head}` does resolve, so this would be read as field notation, but "
                      f"`{cause}` makes it a namespace and the field-notation rule does not "
                      f"apply to namespaces")

    # The elided half.  Its findings are printed after the plain ones and counted on their own
    # line, so that the two figures every pull request body quotes keep meaning what they meant.
    elided_findings = [
        tail for tail in sorted(elided)
        if not elided_resolutions[tail] and ELLIPSIS + tail not in ignored
    ]
    ambiguous = sorted(t for t in elided if len(elided_resolutions[t]) > 1)

    for tail in elided_findings:
        for (path, line) in elided[tail]:
            print(f"{path}:{line}: `{ELLIPSIS}{tail}` names nothing in the environment")
        last = tail.rsplit(".", 1)[-1]
        seen, total_seen = elided_witnesses[last], elided_occurrences[last]
        if seen:
            more = f" (+{total_seen - len(seen)} more)" if total_seen > len(seen) else ""
            print(f"    the final component `{last}` does occur, in "
                  + ", ".join(f"`{n}`" for n in sorted(seen)) + more
                  + f": the namespace `{ELLIPSIS}` stands for is not the one this citation names.")
        else:
            print(f"    nothing in the environment ends in `.{last}` at all, so this is a "
                  f"misspelled name rather than a wrongly elided one.")

    total = sum(len(v) for v in found.values())
    print(f"checked {total} backticked names ({len(found)} distinct) against {dumped} "
          f"declarations and modules: {len(findings)} unresolved")
    elided_total = sum(len(v) for v in elided.values())
    print(f"checked {elided_total} elided citations ({len(elided)} distinct): "
          f"{len(elided_findings)} unresolved, {len(ambiguous)} resolving under more than one "
          f"namespace")
    if args.ambiguous:
        for tail in ambiguous:
            print(f"  `{ELLIPSIS}{tail}` — " + ", ".join(
                f"`{n}`" for n in sorted(elided_resolutions[tail])))
        if not ambiguous:
            print("  (none)")
    dotless_total = sum(len(v) for v in dotless.values())
    print(f"not checked: {dotless_total} dotless `{ELLIPSIS}name` occurrences "
          f"({len(dotless)} distinct), which elide a prefix of a component rather than a "
          f"namespace")
    if findings or elided_findings:
        print(
            "\nEach name above is spelled in a comment and resolves to nothing. Fix the prose.\n"
            f"If one of them is not a declaration reference at all, add it to {IGNORE_FILE}\n"
            "with a comment saying what it is instead; an elided citation goes in there with\n"
            f"its `{ELLIPSIS}`.")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
