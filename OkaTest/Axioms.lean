/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import OkaTest.Axioms.AnalyticSpace
import OkaTest.Axioms.Analysis
import OkaTest.Axioms.Analytification
import OkaTest.Axioms.ComplexSpace
import OkaTest.Axioms.CutOut
import OkaTest.Axioms.LocalOkaRing
import OkaTest.Axioms.MainTheorem
import OkaTest.Axioms.Morphisms
import OkaTest.Axioms.RingTheory
import OkaTest.Axioms.SheafOfModules
import OkaTest.Axioms.Sheaves
import OkaTest.Axioms.Weierstrass

/-!
# Axiom regression test

The library is `sorry`-free, and its results rest only on the three standard axioms of Lean:
`propext`, `Classical.choice` and `Quot.sound`. A `sorry` is only a warning, not an error, so
nothing in an ordinary `lake build` would notice if one were reintroduced — the proof of a
theorem depending on it would simply start depending on `sorryAx` as well.

The files imported above pin that down: each `#guard_msgs` in them fails the build if the axiom
dependencies of the named theorem ever change. Together with the `sorry` grep in
`.github/workflows/lean_action_ci.yml` that is what keeps the completeness claim in `README.md`
honest.

These files are not part of the `Oka` library; they are the `OkaTest` library of
`lakefile.toml`, whose `globs = ["OkaTest.+"]` picks up every module under `OkaTest/` and which
`defaultTargets` also builds, so plain `lake build` exercises them. Adding a file under
`OkaTest/Axioms/` therefore needs no change to `lakefile.toml`. The layout follows Mathlib's own
`MathlibTest`: a test library must live in a directory of its own, outside the source tree of
the library it tests, or Lake rejects its imports.

## Where to put a new assertion

**Add it to the file for its topic, under the matching `/-! ### … -/` heading, and if there is
no such file, add a new one and one import line here. Never append to whichever file you
happened to open.**

| topic | file |
| --- | --- |
| Oka's theorem and the coherence of `𝒪_X` | `OkaTest/Axioms/MainTheorem.lean` |
| Weierstrass division and preparation | `OkaTest/Axioms/Weierstrass.lean` |
| complex analysis, `π₁(ℂ ∖ {0})`, and polynomial zero loci | `OkaTest/Axioms/Analysis.lean` |
| `LocalOkaRing`: Rückert, maximal ideal, regularity | `OkaTest/Axioms/LocalOkaRing.lean` |
| `OkaRing` and the structure sheaf of `ℂ^ι` | `OkaTest/Axioms/ComplexSpace.lean` |
| analytification, and the comparison morphisms to `Spec` | `OkaTest/Axioms/Analytification.lean` |
| general presheaf and sheaf theory, and ringed spaces | `OkaTest/Axioms/Sheaves.lean` |
| sheaves of modules and coherence | `OkaTest/Axioms/SheafOfModules.lean` |
| zero loci and closed immersions | `OkaTest/Axioms/CutOut.lean` |
| analytic spaces, local models, the node | `OkaTest/Axioms/AnalyticSpace.lean` |
| morphisms of analytic spaces | `OkaTest/Axioms/Morphisms.lean` |
| general commutative ring theory | `OkaTest/Axioms/RingTheory.lean` |

That rule is the whole point of the split, and it is not a matter of taste. Until 2026-08-20
every assertion lived in this one file and every pull request appended to its end, so git
reported a conflict between *any* two concurrent pull requests: only one could merge per rebase
round, and each of the others needed a rebase, a force-push, a re-`attach_pr` and a fresh
review of a tree whose library files were byte-identical to the one already approved. That cost
four such cycles in a single morning. Issue #558's append-at-the-end convention reduced the
damage but could not remove it, because two additions at the end of a file still collide.
Concurrent pull requests that touch *different files* do not. See issue #640.

**Every row above has been measured against the guards it routes to, and here is how to
re-measure one.** For each row, resolve every `#print axioms` name in its file to the module the
declaration lives in, and ask whether the row's phrase covers what comes back. In a built
checkout, with the dump taken **after** `lake build` and on the branch being measured — `lake env
lean` reads the oleans, so a dump taken across a branch switch is the other branch's:

    OKA_DECL_DUMP=/tmp/d.txt lake env lean scripts/DumpOkaDecls.lean
    perl -0777 -ne 'while(/^[ \t]*#print axioms(?:[ \t]+|[ \t]*\n[ \t]+)(\S+)[ \t]*$/mg)
        { print "$1\n" }' OkaTest/Axioms/<File>.lean | sort -u |
      while read -r n; do awk -F'\t' -v n="$n" '$2==n {print $1; exit}' /tmp/d.txt; done |
      sort | uniq -c | sort -rn

**The `perl` is not decoration.** The obvious `grep -oP '(?<=#print axioms ).*'` misses a guard
whose name is wrapped onto the next line, and this directory has such guards today; a census
taken that way comes out short of `scripts/guard_coverage.py`'s by one for each of them, and that
script is where the regular expression above is from. **This clause read *"there is one such
guard today, in `OkaTest/Axioms/SheafOfModules.lean`"* and on 2026-09-04 there were four of them
in three files**, so it had stopped being true — exactly what the *name rather than count* rule
below forbids, in the paragraph that states the recipe. A row is wrong when some module's guards
are covered by no row at all — that is the failure this table exists to prevent — and not merely
when its phrase is shorter than the file.

**A second recipe, for the other question the rule above raises: which *heading* a guard sits
under.** The one above resolves a guard to its module; this one counts guards per section, which
is what a module docstring's subtotals are of and what nothing in `scripts/` read at `c48bf8a`,
where `scripts/guard_coverage.py` is the only file there that lifts a `#print axioms` out of a
guard file and it resolves each to a declaration name rather than to the heading above it:

    awk '/^\/[-]! ### /{if(h!="")print n"\t"h; h=$0; n=0; next}
         /^### /        {if(h!="")print n"\t"h; h=$0; n=0; next}
         /^#print axioms/{n++}
         END{print n"\t"h}' OkaTest/Axioms/<File>.lean

**The bracket in the first pattern is a Lean requirement and not an awk one.** This file is
itself a doc comment and Lean's block comments nest, so spelling the opening delimiter literally
here would open a comment that never closes; at a shell you would type it without the brackets.
**Neither of the two oddities that are awk's is optional and both were paid for.** The trailing
space in the first pattern is what stops a `####` sub-heading opening a section of its own —
there are two today — and without it `OkaTest/Axioms/Morphisms.lean` comes out with one section
too many: the sub-heading gets a row of its own and its guards are subtracted from the `###`
section that contains them, so two rows are wrong and the total is right, which is the shape
that survives an append and is why no numeral is given here. The second pattern, matching
a heading on a line of its own, is what sees one whose author opened the doc comment on one line
and wrote the `###` on the next: that form elaborates identically, and a recipe blind to it
charges the heading's guards to the *previous* one and reports a wrong partition from there to
the end of the file, silently. **That is how `OkaTest/Axioms/AnalyticSpace.lean`'s docstring came
to give a coproduct subtotal of *29* for a partition holding 23.**
`.orchestra/validation.sh` now rejects the two-line form, so the second pattern is a fallback
rather than a licence, and the check there says why it is a `grep` and not a comparison of these
counts.

**The worked example is `OkaTest/Axioms/AnalyticSpace.lean`**, the one file whose per-heading
distribution this account works through — and it has been checked against its own prose more than
once, because each reconciliation had gone stale before the next was taken. Run the `awk` above
to get today's partition; that file's docstring carries the ledger of those recounts and says in
terms which of its numerals are records pinned to a commit and which are undated claims about the
tree that go stale. The two rows worth knowing before you run it are the sheet comparison
and the open subspace at `⊤`: while the second heading stood in the two-line form `3177e67`
wrote it in, every count of that file charged its guards to the first, because no instrument then
in use could see it.

**Prose about a section should name rather than count, and this file is not exempt.** A clause
that counts the declarations of a file or the guards of a section is falsified by the next append
to either, and nothing in `scripts/` can tell such a clause from a sentence that happens to
contain a number, so the only defence is how the sentence is written. A section's opening should
name the file whose declarations are guarded and the files the rest were written in; a reader who
wants the arithmetic can run `grep -c '#print axioms'` over the section and get an answer that is
right on the day they run it. **A spelling is exempt when it cannot rot.** A figure
pinned to a commit or a date is a record — which is what the measurements further down are, and
they say so — and so is a numeral about a repair that has already landed, since falsifying either
means rewriting history rather than appending. **Rotting slowly is not the same as not rotting**,
and a *proportion* is the shape that tests the difference. *Most of them*, *the bulk of*, *the
largest member* name no member and give no total, so the append that falsifies one is usually not
the next one — which is why the mechanism above does not reach it — and when it comes it is as
silent as a count's, with nothing in `scripts/` to answer it, since the population has to be
classified by hand before it can be measured. **A proportion is therefore not exempt, and it is
not one of the objects above either**, which count; what it is owed is the naming form, for the
reason the redundancy exemption below gives. **Argued at taxis #1721**, which measured the shape
under the guard files and under `Oka/` and found it live in both; the comparative spelling read as
absent from the tree until the second of those was scanned, which is the fence and not the tree.
**The rule was first written into the guard section next to the one that carried the defect** —
`OkaTest/Axioms/Analytification.lean`'s *The refined datum refines across members, and the two
members meet in nothing else*, which was created already in the naming form and whose opening
names the files its guards were written in and counts none of them. The section that carried the
defect is the one immediately above it, whose clause enumerating six of its seven guards had been
repaired by a separate branch the same day. **That opening is the
spelling to copy.** The rule is repeated here because this is the file every author of a new guard
section reads, and because when it was written this file was itself carrying counts of the class —
the wrapped-guard clause in the `perl` paragraph, the section count in the `awk` paragraph, and the
row total in the worked example — and **on 2026-09-04 all three were false**. Only the first leaves
a record, quoted and dated where it stood; the other two sentences were rewritten to carry no
figure at all. **Do not answer this with a checker** — it would have to guess which numbers in a
docstring are censuses, and `scripts/` has no way to tell.

**A proportion can be spelled as an adverb, and `most`, `bulk` and `largest` are the three tokens
that spelling does not carry.** *Mostly*, *largely*, *chiefly* attach to the thing selected rather
than to the population, so they carry no *of them* and no determiner either; a pattern written from
*Most of them*, *the bulk of* and *the largest member* anchors on one or the other, and `\bmost\b`
does not match `mostly` at all. *For the most part* is the mixed case and is worth naming: it does
carry the token, so a `most` pattern returns it, and it has no determiner and no population, so a
pattern built on either of those does not. **The adverbial spelling was live in this file when this
paragraph was written** — the clause of the paragraph opening *Most mirror-tree material is routed
by a row* that describes `OkaTest/Axioms/Sheaves.lean`'s guards said **mostly
`Oka/Geometry/RingedSpace/`**, the same proportion that file's own docstring had been repaired out
of by lana-agents/oka#478 and in a different spelling: what that push removed there is *Almost all
of it is the mirror-tree material of* `Oka/Geometry/RingedSpace/`. **The claim was shared and the
spelling was not**, which is this paragraph's own thesis holding at the site that motivated it; and
the clause is repaired here to the naming form that push installed there. **A pin does not exempt a
proportion the way it exempts a figure**, and that is the second thing this widening settles: a
reader can re-run a figure at the commit it is pinned to and cannot re-run *nearly all of them* at
any commit, because the population has to be classified by hand first, which is the objection
above.

**A numeral that totals a naming the same passage gives is exempt too, and by a mechanism
different from the ones above.** Those work by being about the past. This one works by being
redundant: *the four results of such-and-such a module*, with the four then named or described in
the same breath, adds nothing to the naming beside it — and naming is what the rule asks for in
the first place. Strike the numeral and the same append leaves the same passage stale, in the same
place, saying the same wrong thing; so the numeral is a way of writing the list and not a second
claim about the section. **What this is not is a promise that such a clause stays true.** It goes
false exactly when the naming goes false, and a naming that has gone false is a sentence that is
wrong about *what is there* — which is the failure this rule is content to have, and the opposite
of a count that goes wrong while every word around it still reads.

**The corollary is the one that costs triage time.** A *the two*, *both* or *the pair* is out of
class only when the passage accounts for both. Where it instead counts a section's contents by
kind and names none of them — *the definition is guarded and not only the two theorems* — a third
theorem appended falsifies it in silence, and it is a census clause like any other. **Which kind a
clause is has to be read and cannot be matched**, so the refusal of a checker above covers this
exemption as much as the rule it qualifies.

**An audit paragraph is exempt through the pinning spelling and not because it is an audit**, and
the case that settled it is `OkaTest/Axioms/AnalyticSpace.lean`'s module docstring. That block is
a ledger of numerals that had gone false — which commit falsified each, and the instrument bug
that made a whole partition wrong — and it argued in terms for its own undated counts, telling a
reader that the list to recheck after adding a guard was every one of them. **At `883b62f` those
counts had rotted in four places**, one of them inside the ledger itself, written as what three
headings *hold now*; and all four were already false when the sweep that reached that file fenced
the block rather than touching it, so the rechecking the paragraph asked for is what did not
happen. **A paragraph whose subject is rot gets no licence to carry it.** The way to keep such a
record is to pin every figure in it to the commit it was measured at, which is what that file now
does, and the two rules then agree instead of having to be ranked. **The exemption attaches to a
figure and not to the paragraph around it**, so a pinned opening does not reach a present-tense
clause further down; that is what left the `Δdump` sentence below contested until taxis #1721
measured its population.

**The rule has a third object and the two named above are not the whole of it: a clause that counts
or quotes rows — of the table above, or of the declaration dump — is in the class too.** It is not
falsified by an append to any guard section, so no scan built on that line can see it — the noun
after the numeral is *rows*, and not *declarations* or *guards*. The worked case is
`OkaTest/Axioms/Weierstrass.lean`'s routing paragraph, which carried one of each and they failed
differently: *"three of which have a row of their own"* was **wrong at the commit that wrote it**,
two of the four namespaces it lists being named by a row and no more, while a **quotation** of the
`OkaTest/Axioms/Analysis.lean` row beside it was exact when written and went wrong when that row
was reworded. **A quotation is in the class for the same reason a count is**: it asserts something
about a structure the clause does not own, and the owner changes it without looking.

**Swept at `c8e77d0`, and what the sweep found is a shape rather than a list.** The class has two
populations. A clause about the table above is exempt on its face — by naming the rows it counts,
or by pinning the figure to the commit it was taken at. A clause about
`scripts/DumpOkaDecls.lean`'s rows is the case the sweep had to classify, and the shape it found is
the `Δdump` note recording what a draft the file did not take would have cost. **Those two
sentences read *Clauses about the table above are few … Clauses about `scripts/DumpOkaDecls.lean`'s
rows are many, and nearly all of them are one shape*, until 2026-09-13** — three proportions over
two populations neither sentence owns, which is the class this same docstring's *A proportion is
therefore not exempt* rules on, under a pin that exempts a figure and cannot exempt a proportion.
**Such a note is exempt under the pinning spelling and not the naming one**, and reading it under
the naming one is the mistake the first draft of this paragraph made. Whether it names every row it
counts varies, and that is the question the naming exemption would turn on; here it does not arise,
because a figure about an abandoned draft is falsified by rewriting history rather than by an
append. The `Δdump` notes written in the present tense are the ones the rule reaches, and where
such a note gives its figure against the same file's declaration count, the declaration-count
object already reached it; `Oka/Analytification/CrossMemberDatumGlue.lean`'s gives it against that
count *and* the planted rows the file keeps deliberately, says so in the same breath, and is
reached by this object alone.

**The widening is not free, and at `c8e77d0` it cost two repairs.** At that commit
`Oka/Analytification/CrossMemberGlue.lean` said its module adds its own declarations to the dump
*"and nothing else, apart from two `congr_simp` lemmas"*, and
`Oka/Analytification/CrossMemberDatumGlue.lean` said that file *"carries two of exactly this
shape"* — a live count of planted rows naming none of them, the second of them about a file the
clause does not own. **Both were exact when measured**, the dump carrying two such rows under
that module and no more, **and both were one `simp only` from being silently wrong.** They were
left to a push of their own — *they are under `Oka/`, and the subject of this one is the rule and
the routing paragraph that motivated it* — and that push is `bcfee65` (lana-agents/oka#443),
which put both clauses into the naming form.

**That deferral is the record this file keeps of the fifth object below catching the rule file
itself.** *They are left to a push of their own* asserts that no push has taken those two sites,
which is a claim about the tree with the arithmetic left out; `6c37417` wrote it at
2026-09-05T10:34:27Z and `bcfee65` falsified it at 2026-09-05T12:27:25Z, so it stood for under
two hours and then read as an open invitation to work already done. **None of the seven patterns
taxis #1727 published matches it**: the sentence is affirmative and carries no negative word at
all, while what it asserts is a negative about every push there has been — so the scan that found
the sites either side of it in this file could not have found this one, and reading is what did.
It is pinned here rather than struck, because a clause that
has gone false is worth more as a dated record than as a repair nobody can see.
`Oka/AnalyticSpace/Sigma.lean`'s account of *the only declaration in the library that names
the empty analytic space* names its writing commit and its falsifying commit for the same reason,
and is the spelling copied here.

**What the sweep asked of each clause is that and only that**: which population it is in, and
under which spelling it is exempt. Whether the other figures those sentences carry are still
exact is a question in the objects named above and was not re-asked here, which is what a sweep of
one class is and is not. **The membership is recorded as a shape and not as a list of sites** —
a list of where a class is instantiated goes stale on the next `Δdump` note anyone writes, and
the draft of this paragraph that carried one named a small part of the tree's sites and reached a
verdict that fails at a site it had not named. **The record of the sweep is what makes this
paragraph cheap to have installed**, not the rule: a rule that grows and is not swept is the
failure this file exists to prevent, and `scripts/` cannot do this one either, for the reason the
checker sentence above gives.

**The rule has a fourth object, and where the counting three — declarations of a file, guards of a
section, rows of a table or of the dump — all turn on a numeral, this one carries none: a pointer
that reaches a member of a list by its position, *the last row* or *the first bullet* or *the
third of those*, is falsified by the next append or reorder exactly as a count is falsified by the
next append.** Nothing in it matches on a digit or on a number word standing for one, so no scan
written for the counting objects can see it; and unlike them it is not greppable even in
principle, because *the last row*, *the bullet above* and *the section below* are ordinary
English, and an occurrence has to be read to tell whether the thing it points into is one that
grows.

**The asymmetry with the enumeration exemption is what makes this an object of its own rather than
a case of a counting one.** That exemption acquits a numeral by redundancy: the passage names what
it counts, so striking the numeral leaves the same passage stale in the same place, saying the
same wrong thing. **A positional pointer has no naming to be redundant with** — it *is* the
reference, and striking it leaves the sentence with no subject. So the exemption that acquits the
counting objects cannot reach this one, and the repair is not to add a figure but to put the name
where the position was.

**The rot is not hypothetical and this tree records an instance of it.**
`Oka/Analytification/RefineDatumCover.lean`'s `## What is not here` says of a section it points
at that *"it was the last section of this file when that sentence was written and is no longer, so
it is named here rather than counted"* — a pointer that went wrong under an append, repaired by
naming the section it meant, `### The condition at an index map that is the identity`. **That
repair is the spelling to copy**, and it was written before the shape had a name.

**This file was carrying one of these, in its own account of the mirror-tree tail**, where *"read
a consumer off the imports, not off a name grep"* reached a bullet of that account by position; it
now names `Oka/CategoryTheory/GlueData.lean`, which is that bullet's subject. `README.md`'s
account of why the `docBlameThm` linter stays off carried another, pointing into the table of what
generates findings; it now names the `@[simps]` and `@[mk_iff]` row. **Both were true when they
were written and neither was pinned to anything**, which is the whole of the difference between
this object and a record.

**The sweep is owed and is not in this push; taxis #1709 carries it**, with a scan that narrows
the tree to the clauses worth reading and an account of what that scan does and does not reach.
What no scan can do is decide membership, which turns on whether the thing pointed into grows, and
that has to be read. **Do not answer this one with a checker either**: the refusal recorded for
the counting objects applies unchanged, and here it is stronger, since there is not even a numeral
to anchor a pattern on.

**The rule has a fifth object, and it is the counting rule with the numeral struck out.** A clause
that says what the tree does or does not *contain* — *nothing in this repository says that …*, *no
file under such-and-such a directory has such a section*, *the only consumer of it in the library*
— is falsified by the next push that adds the thing, in exactly the way a count is falsified by
the next append. **The numeral was never what made a count rot.** What makes it rot is that it
quantifies over a population the sentence does not own, and a universal quantifies over the same
population with the arithmetic left out. So the counting objects and this one fail by one
mechanism, and the defence is the one they already share: name what you mean, and say where the
boundary is.

**Membership turns on ownership and not on truth.** A clause is in the class when it quantifies
over something it does not own — the repository, the library, a directory, another file, *the
tree* — and it is in the class whether or not it holds today, since holding today is the normal
state of one of these and is exactly what makes it invisible. The exempt spellings are these, and
each is exempt by the mechanism that acquits its counterpart among the counting objects:

* **pinned** — an absence attributed to a commit or a date, which is a record and is falsified by
  rewriting history rather than by an append, as a pinned figure is;
* **self-limiting** — *is exhibited **or claimed***, *is not proved or claimed here*, *so far* — a
  claim about the writer's own scope rather than about the tree, which an append cannot reach.
  `Oka/AnalyticSpace/FiniteEtaleOver.lean`'s *"No witness against dropping any of the three is
  exhibited or claimed"* is the spelling to copy;
* **bounded to what the file owns** — *nothing below in this file*, *nothing here does*, *the only
  place in this file where* — since whoever would falsify it is appending to this same module, and
  reading its docstring is part of that append.

**The exemption attaches to the clause and not to the paragraph around it**, as it does for the
pinning spelling among the counting objects: a paragraph that opens with an absence pinned to a
date does not thereby acquit a flat universal further down. **A `## What is not here` section is
not exempt as a section either** — that discipline is what this rule is for rather than what it is
against, and a bullet of one is written in the self-limiting spelling or the pinned one like any
other sentence.

**Do not answer this one with a checker either, and here the refusal is at its strongest.** A
pattern can be written, and taxis #1727 carries one over a whitespace-normalised read of each file
— a clause that wraps across two source lines is invisible to a line-oriented scan, which is why
**taxis #1712** tells a worker to read each file as one string. **That issue's own finding is a
different failure of the same instrument and is the sharper warning**: the regex taxis #1685
published to define a spelling could not match the example that issue quoted to define it, so a
published pattern is worth what it scores against its own examples and no more. What no pattern
can do is tell a claim about the tree from a description of method (*there is no mathematical
content in either*) or from a pointer (*the only place in this file where*), and it returns those
alongside what is in the class. The scan narrows the tree to what is worth reading; the reading is
the work.

**The standing rule, which is the whole of the remedy.** No sentence about what the tree does or
does not contain goes into a `.lean` file unless it was checked at the head being pushed from —
and for a claim about what instance search finds, *checked* means compiled, not grepped and not
read. **taxis #1720**'s subject was false at the commit that wrote it, and it landed in the push
that was repairing **taxis #1713**'s, which was of this class too; **taxis #1727** is the filing
that made them one.

**The rule has a sixth object, and a scan really does narrow this one: a
clause asserting a *dependency relation between two named files* — *that file is downstream of
this one*, *this file does not import that one*, *no file in this repository imports both*, *N
modules below* — is a claim that has to be **measured**, and at `5a525bc` no script in this
repository measures it.** Every member carries a token from a short
list, so grepping `downstream`, `upstream`, `import` and `import closure` gets a worker to the
population in one run; **what the scan cannot do is decide the verdict**, since that is an
`import`-graph question and not a text one. That is the opposite shape from the fourth object
above, which no pattern narrows and whose verdicts a reader can reach by reading.

**The hole is that names are checked and paths are not.** `scripts/check_docstring_names.py`
resolves **names**, and a path is not a name; at `5a525bc` no script here joins a backticked name
to the path beside it, and none joins two paths to each other. **So a sentence whose *name* half is
exact can carry a *path* half that is false**, and the checker returns 0 unresolved either way —
which is what happened in
lana-agents/oka#492, where a reviewer verified the cited declaration through
`scripts/DumpOkaDecls.lean`'s `module<TAB>name` rows, correctly, and the false clause was the one
beside it.

**Since 2026-09-20 one script does join two paths of this repository to each other**, and it is
`scripts/module_graph.py`; the paragraph opening *The instrument this rule has asked for* says what
it reads, what it was run against before being believed, and what it still cannot decide. **Neither
pinned sentence above is retired by it**: each is a measurement at `5a525bc`, neither was written in
the present tense, and the hole the second of them names — that no script joins a backticked *name*
to the *path* beside it — is still open, this one joining paths to paths and nothing else.

**The two failure modes, and each has cost this repository a push.** The first is **inferring the
relation from the file names or from `Oka.lean`'s ordering**, and that ordering is not the graph:
the list is alphabetical, and at `ca96745` **117 of its 214 adjacent pairs are
incomparable** — among them `Oka/Analytification/StandardEtaleFiniteness.lean` and
`Oka/Analytification/StandardEtaleLocalIso.lean`, whose final components agree in their first
thirteen letters and which sit on consecutive lines of it. **The worked instance is in this
push**: `Oka/Analytification/LocalisationFunctor.lean` explained its own existence by saying the
analytification functor *lives two files further on* from
`Oka/Analytification/DistinguishedOpen.lean`, when `Oka/Analytification/Functor.lean`, which
declares that functor, and `Oka/Analytification/ChangeOfVariables.lean`, which declares its action
on maps, are both **incomparable** with that file — not further on at any distance, in either
direction. That clause is quoted in that file today with the walk that retired it. The
second is **taking an import as a reason without checking which way the reason runs**:
lana-agents/oka#491 is a whole pull request spent on one clause of
`Oka/AnalyticSpace/CutOutProduct.lean` that gave an import as the reason a declaration had no
earlier home, **where the cited import is what gave that file both
ingredients and so falsified the reason**. The repaired clause is quoted in that file today and is
the worked instance to read; taxis #1804 settled the same thing from the other side, a *parallel*
file having been called a downstream one.

**The instrument is a graph walk, and the parser is the whole of it.** Read the import lines of
each `.lean`, keep those naming a module of this repository, close transitively, and ask three
questions of a pair: is `b` in the closure of `a`, is `a` in the closure of `b`, and at what BFS
edge distance. That settles *upstream*, *downstream*, *incomparable* and every *N modules
downstream* numeral in one run. **The obvious parser is wrong here twice over.**
`^import\s+([\w.]+)` over the raw file text follows an `import` line written inside a comment, and
it matches neither the keyword nor the module of a `public import`, which **27** files of this
tree write. **Say which population a figure of this kind is over, because two reasonable ones
differ here.** Over the **309** modules under `Oka/` and `OkaTest/` together with `Oka.lean` and
`OkaTest.lean`, at `ca96745`: **30** of the **787** repository-internal import edges are written
`public import`, and they sit in **13** files; the remaining ones of the 27 write `public import`
on Mathlib modules only. Counting `scripts/DumpOkaDecls.lean` and `scripts/DumpEnvNames.lean`,
which import `Oka` and `OkaTest` as well, gives **791** edges for the same 30. Use
`scripts/import_cost.py`'s `IMPORT` pattern over its nesting-aware `strip_comments`, which is
the parser that script's own published figures are computed with, or say what you used instead.
**Checking the *delta* is not a check on the parser**: on the
`Oka/Analytification/StandardEtaleFiniteness.lean` and
`Oka/Analytification/StandardEtaleLocalIso.lean` pair the naive regex understates both closures by
exactly 14 — **74** and **76** against **88** and **90** — and returns the two marginal costs,
**5** and **3**, unchanged.

**The compiled instrument is decisive and is cheaper to write than the walk**: a scratch file
that `import`s both modules
and states one declaration using both. If it elaborates, neither is downstream of the other, and
any clause saying otherwise is false. **Use it when the clause is load-bearing**, because a graph
walk is a script and a script is a claim.

**Exclude both aggregators and say that you did.** `Oka.lean` is the one `mk_all` generates and it
imports every module of the library; `OkaTest.lean` is its test-side twin, with **94** import lines
at the commit that writes this, one for each module under `OkaTest/`. Each of the two is therefore
a hit for every question of this shape — the same carve-out the mirror-tree paragraph below makes
for the same reason. **Every *N modules downstream* figure this file states of its own is taken
under both exclusions**, which is a claim about the file and not about the figures preceding any
one sentence of it. There are six, one of them stated twice, and at the commit that writes this
they are **10** for `OkaTest/HolomorphicMapOpen.lean`, **9** for
`OkaTest/FiniteMorphism.lean`, **3** for `OkaTest/CoherentFree.lean`, **124** for
`Oka/Analytification/AffineCover.lean`, **147** for
`Oka/Analytification/UniversalProperty.lean` and **95** for
`Oka/Algebra/Category/ModuleCat/Sheaf/Quasicoherent.lean`. Over the same population with neither
aggregator excluded they are **11**, **10**, **4**, **126**, **149** and **97**; with `Oka.lean`
alone excluded, **11**, **10**, **4**, **125**, **148** and **96**. **So the one-module carve-out
gets every one of the six wrong**, and on the three whose subject is under `OkaTest/` it changes
nothing at all, that root not being downstream of a test module. **The one exception is a subject
this file does not own** — the **210** and **95** of `Oka/Analytification/CoverGlueTop.lean`, and
the **175** and **86** they retired — and the paragraph repairing that file's population
enumeration records them as downstream counts with `Oka` excluded from the tally.

**Swept at `5a525bc`, and unlike the fifth object's sweep this one found live defects.** Reading
every one of the **307** tracked `.lean` files under `Oka/` and `OkaTest/`, together with the two
root modules `Oka.lean` and `OkaTest.lean`, as one whitespace-normalised string of its **comment
content alone**, and cutting it into sentences: **398** carry a dependency
token, of which **158 name a second module or root of this repository** and are decidable by the
walk. **Three of the 158 were false** and are repaired in the push that wrote this paragraph:
`Oka/Analytification/SpecDistinguishedOpen.lean`'s *"no file in this repository imports both"*,
which the import block at the head of that same file falsifies;
`Oka/Analytification/LocalisationFunctor.lean`'s enumeration of another file's imports, short by
one, together with a *further on* that named an incomparable pair; and
`Oka/Analytification/StandardEtaleLocalIso.lean`'s *"imports this one's imports"*, true of one of
the two imports. Each is repaired with its retired wording kept as a dated record.

**`5a525bc` is a pin and not the head, so the delta to `ca96745` was read rather than assumed.**
Over the comment lines that range adds, **five** sentences carry a dependency token. Four are
`Oka/AnalyticSpace/CutOutCompose.lean`'s account of its own relation to
`Oka/AnalyticSpace/CutOutProduct.lean` — *incomparable*, closures of **42** and **65** modules
under `Oka/`, **25** the cost of the import it declines, and a dated record of the *downstream*
that was there before — and all four hold at `ca96745` on a walk of mine. The fifth is
`OkaTest/Axioms/Morphisms.lean`'s *"this file imports `Oka` and not `OkaTest`, so no declaration
of a test file is in its environment"*, and that file's one import line is `import Oka`. A sweep
pinned to a commit says nothing about the commits after it, and the cost of carrying the pin
forward is this paragraph.

**What the sweep did not reach, so that a later one knows where to start.** The **240** sentences
that carry a dependency token and name **no** second module **were not read.** The column was
dropped for the instrument it wants rather than for its size, and **how many of the 240 want that
instrument was not counted**: a sentence like *"no statement downstream of here consumes it"*
(`Oka/UliftCoord.lean`) or *"Nothing downstream of this file needs any of it yet"*
(`Oka/Analytification/AffineCover.lean`) quantifies over a downstream *set* and over what its
declarations *use*, which wants the reverse closure and a grep over it. **Do not read that as
saying the column is out of reach, because one of its cheapest members was false.** A clause about
a file's own *importers* is one reverse edge and no grep at all, and
`Oka/AnalyticSpace/Factorisation.lean`'s *"nothing imports this file except the root module"* had
**three** importers, two of them not the root module. It was true at the commit that wrote it and
went false the next day; it is repaired in this push, with the retired wording kept there as a
dated record. **It was found by this branch's reviewer and not by the sweep**, and nothing about
it needed the instrument this column was dropped for. Its own sentence names no module of this
repository, which is the criterion this paragraph splits on and puts it here; a splitter that
joined it to the sentence before it, which names one, would put it in the **158** instead and make
*three of the 158* an undercount by one. The sweep did not report it, which says which side its
splitter put it on. And **closure-size figures against Mathlib** are a different graph and are
not in this class at all: `scripts/import_cost.py` is the instrument for those and its own
docstring is where that hazard is written down. **That sentence ended *"Neither column was swept
and this paragraph does not claim it was"* until 2026-09-07**, and it was exact at `ca96745`, the
commit that wrote it, and what retires it is the sweep recorded in the paragraph opening *The
second sweep, at `3187978`*.

**The second sweep, at `3187978`, read the half of that column whose referent is in the sentence
beside it.** Over the same population — the **312** tracked `.lean` files under `Oka/` and
`OkaTest/` together with `Oka.lean` and `OkaTest.lean`, comment content alone, whitespace-normalised
and cut into sentences — the splitter of the push that wrote this paragraph gives **402** sentences
carrying a dependency token, **180** naming a second module of this repository **in the sentence**,
and **222** naming none. **Of those 222, 90 name one in the neighbouring sentence** and were all
read; **73 of the 90 assert a relation inside this repository** and are decidable by the walk,
and the other **17** are closure figures against `Mathlib/`, which *"closure-size figures against
Mathlib are a different graph and are not in this class at all"* puts outside it. **The remaining
132 name none in either and are still unread**: they are the ones that want the reverse closure
and a grep over it, and nothing here decides one of them.

**Two of the 90 were false** and are repaired in this push, each with its
retired wording kept as a dated record: `Oka/Analytification/SpecScheme.lean`'s *"and nothing in
`Oka/Analytification/` does"*, which `Oka/Analytification/SpecTwoData.lean` and
`Oka/Analytification/SpecRefinedMember.lean` have falsified since the day after it was written, and
`Oka/Analytification/CoverGlueTop.lean`'s downstream counts **175** and **86**, each exact at the
commit it was taken at, neither pinned, and now **210** and **95**.

**The two splitters do not agree and neither is wrong.** `bda9e42`'s reports 398 / 158 / 240 at
`5a525bc` and this one 402 / 180 / 222 at `3187978`, five commits later; a partition of prose into
sentences is an artefact of where the splitter cuts, so the three figures of a run are comparable
with each other and not across runs. **What is not an artefact is that the column has decidable
members** — the count of those found by reading it is now two, against one found by a reviewer
looking at a file for another reason. **A third sweep still owes the 132**, and the cheapest thing
it can do first is what this one did: carry the neighbouring sentence, since a clause whose
referent is one sentence away is a pair claim that a splitter, and not the prose, put in this
column.

**The third sweep, at `d2ae161`, decided six of the column that wants the reverse closure — and
two of them needed an instrument this rule did not name.** It did **not** partition the 132: it
ran a narrower pattern for the shape that column is made of, a quantifier over a *downstream set*:
one of `nothing`, `anything`, `everything`, `nobody`, or `no`/`any`/`every`/`all` with a noun after
it, immediately before `downstream`; or `downstream` immediately before one of `has`, `have`,
`needs`, `depends`, `consumes`, `can`, `reads`, `uses`, `wants`. Over the same population, now
**316** tracked `.lean` files under `Oka/` and `OkaTest/` together with `Oka.lean` and
`OkaTest.lean`, comment content alone, whitespace-normalised and cut into sentences, it returns
**21**. That pattern is a choice like any splitter and the figure is a fact about it as much as
about the tree. **Which of the 21 the splitter of the sweep recorded in the paragraph opening *The
second sweep, at `3187978`* puts in its 132 was not checked and is not claimed**, for the reason the
paragraph opening *The two splitters do not agree* gives: the two splitters already differ by about
a factor of two, so a figure from one run does not subtract from a figure of another.

**The 21 is `d2ae161`'s and this paragraph falsifies it as prose, which is said here rather than
left to be discovered.** `OkaTest/Axioms.lean` is in the population the pattern runs over, and a
sweep that quotes what it swept is matched by its own pattern: at the head that writes this the
figure is **31**, the ten extra being this paragraph's own quotations of the sites below. **That
is the shape taxis #1727's second round was rejected for** — repairing into a spelling the rule
itself scans raises the raw count — and the remedy here is the one this file already uses for the
sweeps above, which is to pin the figure to a commit and say what moved it, not to choose a
paraphrase that dodges the pattern. **This branch's review round demonstrated that rather than only
predicting it**: `829c4e7`, the head as first delivered, gave **30**, and repairing the paragraph
below — which quoted two shapes as strings with counts beside them, into prose that names their
sites instead — raised it to **31**. **A later sweep should take 21 as `d2ae161`'s and re-derive
its own at its own head**, and should expect every sweep of this class to inflate the count it
reports.

**All six that were decided hold, and the list is what was found rather than a claim about the
other fifteen.**

* `OkaTest/HolomorphicMapOpen.lean`'s *"reachable from everything downstream of
  `OkaTest/FiniteMorphism.lean`"* — **true, and by a forward edge rather than by a reverse walk**:
  `OkaTest/FiniteMorphism.lean` imports it at distance **1**, so the **9** modules downstream of
  that file are a subset of the **10** downstream of this one. **A downstream-set claim whose
  subject is the file making it is a pair claim in disguise** and costs one edge.
* `Oka/Analytification/AffineCover.lean`'s *"Nothing downstream of this file needs any of it yet"*,
  of the locally directed cover API — **true**: the four tokens grepped for — the dotted module
  name of `Mathlib/AlgebraicGeometry/Cover/Directed.lean`, together with `SmallAffineZariski`,
  `LocallyDirected` and `directedCover` — occur in the code of **none** of its **124** downstream
  modules.
* `Oka/UliftCoord.lean`'s *"no statement downstream of here consumes it"*, of
  `IsWeierstrassPolynomial`'s vanishing condition — **true, and the reverse closure was not what
  decided it**: that predicate occurs in the code of exactly two modules of this repository,
  `Oka/Weierstrass.lean` and `Oka/Statement.lean`, and neither is downstream of
  `Oka/UliftCoord.lean`. **Locating the subject can be cheaper than enumerating the set**, and it
  is the first thing to try.
* `OkaTest/AffineSections.lean`'s *"without using `OkaTest.AffineSections.specXPresentation` or
  anything downstream of it"* — **true**, and this one is decided outright rather than
  grepped. See the instrument below.
* `Oka/AnalyticSpace/SigmaFiniteEtale.lean`'s *"nothing downstream reads it there"*, of
  `ComplexAnalytic.AnalyticSpace.card_fiber_sigmaFold` at an infinite index type — **true, and
  true more strongly than it says**: that theorem has **no** users at all in the environment, at
  any index type.
* `OkaTest/CoherentFree.lean`'s *"everything downstream is at the locally ringed space spelling"* —
  **true and vacuous**, which is worth separating from the confirmations above: its **3**
  downstream modules mention **neither** spelling in code, so the universal holds over an empty
  set. **A vacuous member of this class is not a confirmation of anything** and a later sweep
  should not count it as one.

**Every downstream figure above excludes `Oka.lean` and `OkaTest.lean`**, the two aggregators, for
the reason this paragraph's own carve-out gives — and here that exclusion changes no verdict rather
than being taken on trust: neither root module mentions any of the subjects grepped for, so counting
them would have moved the four downstream figures to **10**, **11**, **126** and **4** and left
every hit count at **0**.

**The instrument this rule did not name, and it decides a shape the other two cannot.** A clause of
the form *"proved without using `X`, or anything downstream of `X`"* is about **declarations** and
not about modules, so neither the import walk nor the compiled scratch file reaches it. The
environment does: walk `ConstantInfo`'s value and type through `Expr.getUsedConstants`,
transitively,
and ask whether `X` is in the set. On `OkaTest.AffineSections.isCoherent_cokernel_specXHom` that set
has **4352** constants and `OkaTest.AffineSections.specXPresentation` is **not** among them, with
`OkaTest.AffineSections.specXHom`, which is, as the positive control. **Because the set is
transitively closed, the same run settles the *or anything downstream of it* half**, which is why
this is a decision and not a sample. **Run backwards it decides the *nothing reads it* shape too**:
scan `env.constants` for those whose value or type mentions the target, which is what returned **0**
for `ComplexAnalytic.AnalyticSpace.card_fiber_sigmaFold`. **Put a deliberate control error at the
foot of the file**, since an `#eval` that never runs and an `#eval` that prints nothing are the same
on the terminal.

**One repair lands with this sweep and it is not one of the 21.**
`Oka/Analytification/CoverGlueTop.lean`'s population enumeration named **311** files for its own
numeral of **312** — *"together with
`OkaTest.lean`, and excluding the aggregator `Oka.lean`"*, where the tracked `.lean` files under
`Oka/` and `OkaTest/` are 310 at `3187978` and 312 needs both root modules. **The reviewer of
lana-agents/oka#498 found it, declined to reject on it and left it for a later seat**, and this is
that seat; the retired wording is kept there as a dated record. Its **210** and **95** are
unaffected, because they are downstream counts with `Oka` excluded from the tally while the
population is the graph the walk runs over, and **separating those two is the repair** — conflating
them is what let an enumeration disagree with its own numeral in a sentence three reviewers read.

**Two shapes in the 21 are not import-graph claims at all and no walk decides them, and each is
given by its sites rather than as a quotation with a count.** The first says that the index of a
point is *chosen* and that nothing downstream depends on which; it is a claim that a choice is
immaterial and not that a set is empty, and its sites are `Oka/Analytification/AffineCover.lean`,
`Oka/Analytification/RefineDatumCover.lean`, `Oka/Analytification/SpecAffineCover.lean` and
`Oka/Geometry/RingedSpace/PresheafedSpace/Gluing.lean`. The second says that no term downstream can
meet a stuck `Eq.mpr`; it is a consequence of the transported thing being a `Prop`, and its sites
are `Oka/AlgebraicGeometry/Modules/Tilde.lean`, twice, and `OkaTest/FiniteMorphism.lean`. **The
sites of a shape do not all spell it the same way**, which is why neither is given here as a quoted
string with a number beside it: `Oka/Analytification/RefineDatumCover.lean` writes the first as
*`idx` is a choice*, `Oka/Geometry/RingedSpace/PresheafedSpace/Gluing.lean` as *depends on which
index is picked*, and `OkaTest/FiniteMorphism.lean` writes the second with *nothing* where the
others write *no term*. **A count beside a quoted string is a claim about that string and `git
grep -c` is what decides it**; a sweep that means the shape owes the sites instead, which is what
this paragraph gives. **Both shapes are true for reasons a reverse closure cannot supply**, and a
sweep that reported them as measured would be claiming more than it ran. The remaining members of
the 21 were read and not decided, and this paragraph does not say they hold.

**The fourth sweep, at `7a99bfc`, read the seven the third left undecided, and one of them is
false.** Same population rule and same published pattern, re-implemented rather than reused: the
tracked `.lean` files under `Oka/` and `OkaTest/` together with `Oka.lean` and `OkaTest.lean` are
now **323**, comment content alone, whitespace-normalised and cut into sentences, and the pattern
returns **31**, of which **11** are in this file. Those two figures are what the third sweep's
reviewer reported at its own head, reproduced here on a further implementation; **the set behind
them was not compared and is not claimed to be the same set**, for the reason the paragraph opening
*The two splitters do not agree* gives. Of the **20** outside this file, six are decided in the
paragraph opening *All six that were decided hold*, four are the index-of-a-point shape and three
the stuck-`Eq.mpr` shape, and the remaining **seven** are these.
`Oka/Analytification/AffineCover.lean` holds three of the 20 — one among the six, one of the
index-of-a-point shape, and one of these seven.

* `Oka/AnalyticSpace/FiniteEtaleOver.lean`'s *"the downstream uses of the property — a
  Galois-category structure, the comparison functor taxis #1113 wants — ask for them"*, of the four
  anonymous `CategoryTheory.MorphismProperty` instances on
  `ComplexAnalytic.AnalyticSpace.isFiniteEtale` — **false, and repaired in this push with the
  retired wording kept there as a dated record.** **Neither named use existed at the commit that
  made that repair**: there was no `PreGaloisCategory` instance in this repository, which three
  files say of themselves in those words, and taxis #1113 was open. **The first of the two exists
  from 2026-09-15**, when `Oka/AnalyticSpace/GaloisCategory.lean` declared one at
  `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver`, and **taxis #1113 is still open**;
  what that changes is the register of the sentence and not the verdict on the wording, which was
  false when written. The one consumption of any of the four is in
  that same file, at `ComplexAnalytic.AnalyticSpace.isFiniteEtale_of_restrictHom_top`.
* `Oka/Analytification/UniversalProperty.lean`'s *"Everything downstream is stated in the second
  spelling"*, of the two spellings of a factorisation that
  `ComplexAnalytic.comp_zeroLocusSubspaceι_iff` identifies — **true, and the token that decides it
  is not the one the sentence names first.** `zeroLocusSubspaceι` occurs in the code of **7** of the
  **147** modules downstream, and `restrictTopIso` in **3**; neither is a counterexample, because
  the spelling being denied is that pair *through* `ComplexAnalytic.toAmbient`, and that name
  occurs in the code of **none** of the 147. **One** of those **7** states a factorisation through
  `zeroLocusSubspaceι` — `OkaTest/Factorisation.lean`, in `existsUnique_liftHom_node`,
  `eq_id_of_comp_zeroLocusSubspaceι` and `exists_liftHom` — and it is about a cut-out ambient space
  and not about an analytification, at which the second spelling does not typecheck. Of the other
  six, five use the name for a cut-out datum, a pushforward or an `IsIso`; the sixth is
  `OkaTest/Axioms/CutOut.lean`, whose eight occurrences in code are all `#print axioms` guard
  lines, which is none of those three uses. **None of the six states a factorisation** — a guard
  line states nothing at all — and that is what the verdict rests on.
* `Oka/Algebra/Category/ModuleCat/Sheaf/Quasicoherent.lean`'s *"Anything downstream has to spell it
  the same way"*, of the map a presentation is built out of — **true, and no longer vacuous.** The
  pinned Mathlib names that composite nowhere: `relations.s ≫` matches **one** line under
  `Mathlib/`, and it is inside the *type* of `SheafOfModules.Presentation.isColimit`. Of the **95**
  modules downstream, one uses it — `Oka/Analytification/SheafCoherent.lean` — and it spells it
  `(SheafOfModules.freeHomEquiv _).symm P.relations.s ≫ kernel.ι P.generators.π`, which is the
  quoted composite with the namespace the quotation drops. **The two strings are not equal**: they
  differ by exactly the fifteen characters `SheafOfModules.`, because the docstring quotes the
  spelling `SheafOfModules.Presentation.cokernelIso` is stated with, inside
  `namespace SheafOfModules`, while its one consumer is inside `namespace ComplexAnalytic` and has
  to carry the prefix. **What *the same way* asks for is the term and not the characters**, and
  Mathlib settles that it has to be: its own source spells the composite
  `(freeHomEquiv _).symm P.relations.s ≫ (kernel.ι _)`, leaving `kernel.ι`'s argument to be
  inferred, so this docstring's quotation is already a normalisation of Mathlib and not a
  transcription of it.
* `Oka/AnalyticSpace/Finite.lean`'s *"nothing here or downstream consumes one"*, of an `IsProper`
  class — **true and vacuous**, in the sense the `OkaTest/CoherentFree.lean` bullet above separates
  out: `IsProper` as a whole word occurs in the code of **no** module of this repository, so there
  is no such class for anything to consume.
* `Oka/Analytification/AffineCover.lean`'s *"Neither is needed by anything downstream"*, of a
  comparison theorem and of a choice among Mathlib's cover APIs — **true, and decided by the build
  and not by a grep.** The comparison theorem is described rather than named, so there is no token
  to grep for at all; the **four** tokens that the bullet about this same file greps for — its own
  enumeration, the dotted module name together with the three API tokens — occur in the code of
  none of its **124** downstream modules, which reproduces. What
  settles the claim is neither of those: every module downstream is proved without either subject,
  which the build establishes and a grep cannot.
* `Oka/Analytification/CoverIndependence.lean`'s *"everything downstream of a presentation"* —
  **not a claim of this class.** Its *downstream* is of a datum and not of the import graph, and the
  sentence enumerates its own members in its own words. The pattern matches the word; no walk is
  owed.
* `Oka/Regular.lean`'s *"a corollary is only a de-duplication if nothing downstream can tell"* —
  **not a claim of this class either.** It states the condition under which a design choice counts
  as de-duplication; it does not assert that the condition holds here. The consumer claim in the
  clause beside it — that the three results are what the Krull-dimension induction and
  `LocalOkaRing.span_fromPolynomial_X_sub_C_ne_span_lastVar` consume — is checkable and holds:
  both named consumers are in `Oka/Regular.lean` itself, and outside it the three results are named
  only by `OkaTest/Axioms/LocalOkaRing.lean` and `OkaTest/GermQuotientDegreeOne.lean`.

**Two instruments this rule still did not name, and one warning about which token to reach for.**
Each of the two decides a shape the three instruments this rule already names do not settle.

**The local-instance rebuild, for an instance.** **No use site of an instance names it** — typeclass
synthesis puts the term there and writes nothing in the source — so a grep decides who consumes one
for a *named* instance no better than for an anonymous one, and neither the import walk nor the
compiled scratch file is about declarations at all. **The build decides it.** Put `local` in front
of each `instance` — Lean 4 takes `local instance : … where`, so an anonymous declaration stays
anonymous and becomes file-scoped — change nothing else, and build the library: **a green build is
a proof that nothing outside that file consumes one**, and the errors of a red one name the
consumers. On `ComplexAnalytic.AnalyticSpace.isFiniteEtale`'s four that is `lake build` exit 0 over
4153 jobs at `7a99bfc` and over 4154 at `2cf6efa`, the push that added a module to that same file's
neighbourhood.

**This paragraph prescribed `attribute [local instance]` until 2026-09-12, and that is not this
instrument**: the attribute *promotes* a declaration that is not an instance, which is what
`Oka/Analytification/SpecDistinguishedOpen.lean` uses it for and says so; applied to one that is
already a global `instance` it adds a local one and **removes nothing**, so importers still
synthesise it and **the build is green whatever the answer is**. Two modules settle it, and they
are the cheapest way to check any claim of this shape:
a module `A` declaring a one-field `Prop` class of a natural number and an anonymous
`instance` of it at `0`; a module `B` importing `A` and asking `#synth` for that instance. With a
plain `instance`, `B` resolves it; with **`local instance`**, `B` reports *failed to synthesize*;
with a plain `instance` and the attribute beside it, `B` resolves it again. **Only the middle row
is the instrument**, and the retired wording is kept here as a dated record because two review
rounds re-ran the middle row while this file prescribed the third.

**That numeral read 2026-09-08 from the commit that wrote this record, which is the day the
retired wording was *written* and not the day it was retired.** `0c370e5` put
`attribute [local instance]` into this paragraph at `2026-09-08T17:20:17Z`; `0eed5cd` replaced it
and wrote this record at `2026-09-12T16:45:34Z`, so the paragraph prescribed it **from** the first
of those days **until** the second and the record named the day its wording began. **This is a
correction and not one of this repository's dated records**, a dated record presupposing that what
it quotes read true until the day it names, which the numeral this repair replaces never did.
**The instrument is `git log -G` or the removed side of `git show 0eed5cd`, and not `git log -S`**:
`-S` reports a commit only when the count of a string changes, and this retirement quotes what it
retires into the record replacing it, so the count does not move and the pickaxe returns `0c370e5`
alone — the commit whose date the wrong numeral was. `Oka/AnalyticSpace/FiniteEtaleOver.lean`'s
paragraph on the same experiment took the same numeral from the same push and is corrected with
this one.

**Deleting them outright is the weaker run and it is worth saying why**: the build stops at the
first module that fails, which is the declaring one, so a deletion answers *who at all* and then
tells you nothing about anything past the failure. The local-instance run answers *who outside*
and reaches every module. A sweep should say which of the two it ran.

**An anonymous instance is not nameless, which is worth knowing before reaching for a guard.** Lean
generates a name for it and the name is not internal, so `scripts/DumpOkaDecls.lean` emits it like
any other constant: `ComplexAnalytic.AnalyticSpace.isFiniteEtale`'s four appear in `oka-decls.txt`
against `Oka.AnalyticSpace.FiniteEtaleOver` as
`ComplexAnalytic.AnalyticSpace.instIsStableUnderCompositionIsFiniteEtale` and three formed the same
way, and `#print axioms` elaborates on each. **What makes a guard the wrong instrument is not that
there is nothing to guard**: the generated name is derived from the class and the argument rather
than chosen, and a second anonymous instance of the same class takes that name with a numeric
suffix after it, so **the name a guard would pin moves when a sibling is added above it** — which
the two-module file above shows for the class it declares. A guard would also answer *does this
exist*, which was never the question. The third instrument, the environment walk, is the one that
could answer *who consumes it* by name, and on this toolchain it cannot be run as this rule states
it: `Lean.ConstantInfo.value?` is `none` for every *imported* theorem — `Nat.add_comm` included —
and a `Prop`-valued instance is a theorem, so a scan of the environment over values returns **0**
for a positive control as readily as for the target. **Put a positive control in that walk**, for
the same reason this rule asks for a deliberate control error at the foot of a scratch file.

**When the subject of the claim does not exist, the build decides it and a grep cannot.** *"Nothing
downstream needs `X`"* has two shapes. If `X` is in the tree, the reverse closure and a grep for `X`
decide it, which is what the `Oka/Analytification/AffineCover.lean` bullet above about the locally
directed cover API did. If `X` is *not* in the tree — a theorem nobody has stated, an API nobody has
chosen — a grep returns zero from both a true claim and a mis-spelled one, and the honest instrument
is that every module downstream is proved without `X`, which the build already establishes. **Say
which of the two a verdict rests on**, because the second is the weaker statement and reads exactly
like the first.

**And pick the token that is unique to the spelling being denied.** A claim that everything
downstream uses one of two spellings is decided by whatever the *other* spelling has and this one
does not, which is rarely the token the sentence puts first: on
`Oka/Analytification/UniversalProperty.lean` above, grepping `zeroLocusSubspaceι` reports seven
downstream modules and every one of them is a false positive, while `ComplexAnalytic.toAmbient` —
which is where the discarded spelling's `restrictTopIso` enters — reports none and settles it.

**This block is matched by the pattern it reports on**, as the paragraph opening *The 21 is
`d2ae161`'s* says of the third sweep's. The **31** it reports is `7a99bfc`'s and does not include
what is written here; at **`0c370e5`**, the head that wrote this block, the pattern returns **42**
over a population of **324**, and the whole of the difference is in this file, whose own count goes
**11 → 22** while no other file's moves — the eleven added are this block's quotations of the
sentences it decides. **That figure was written as *at the head that writes this* and is now pinned
to the commit instead**, because the phrase is inherited by every later push to this file while the
measurement is not: the push repairing the instrument paragraph above re-derived it and it is still
**42 / 22** over **324**, but that is a second run and not the same claim. A fifth sweep should
re-derive its own figure at its own head and should expect to have raised it again.

**The instrument this rule has asked for since `5a525bc` is now a script, and the clause saying it
is not is retired here.** `scripts/module_graph.py` is the walk: it reads
`scripts/import_cost.py`'s `IMPORT` over that module's own nesting-aware `strip_comments`, closes
the repository-internal edges in both directions, and answers the three questions of a pair, the
downstream set, the upstream set and the direct importers, with `--grep` and `--word` over the
comment-stripped **code** of a set. `README.md` names it, it has a `--self-test` that plants the
four hazards this paragraph already records — an `import` line inside a comment, a `public import`,
a pair whose names look
ordered and is not, and an aggregator that conducts — and it is a tool and not a gate, for the
reason `README.md` gives of the other three. **That sentence read *at `5a525bc` no script in this
repository measures it* and is kept above as the pin it always was**: it is exact at `5a525bc` and
this push is what makes it a fact about a commit rather than about the tree.

**The script is not evidence about itself, so it was run against the figures this file already
carries.** At `ca96745` it returns **787** repository-internal import edges, **30** of them written
`public import` in **13** files, and **117** of `Oka.lean`'s **214** adjacent pairs incomparable —
the three figures the paragraphs above state at that commit, each reproduced without being read off
them. The `Oka/Analytification/StandardEtaleFiniteness.lean` and
`…/StandardEtaleLocalIso.lean` closures come back **88** and **90** at that commit on the
self-inclusive count those paragraphs use. **A walk that agreed with nothing already published
would be the thing to distrust**, which is why this control is here and not in the pull request.

**The fifth sweep, at `0b2759b`, is the first to run a pattern *inside* the column the second sweep
left unread.** Same population rule — every tracked `.lean` under `Oka/` and `OkaTest/` together
with `Oka.lean` and `OkaTest.lean`, now **355** files — comment content alone, whitespace-normalised
and cut into sentences, with a fourth splitter: **702** sentences carry a dependency token, **338**
name a second module of this repository in the sentence, **167** name one in a neighbouring
sentence and **197** name none in either. **Those figures are not comparable with 402 / 180 / 90 /
132**, for the reason the paragraph opening *The two splitters do not agree* gives, and this one
counts `importer` and `importing` as tokens where the description of the earlier runs names four
words; the three columns of a run are comparable with each other and with nothing else.

**Of the 197, thirty-six match one of the two narrow patterns and a hundred and sixty-one match
neither and are still unread.** The third sweep's published downstream-set pattern matches **17**
of them, none in this file; a second pattern for the *importer* shape — a quantifier immediately
before `imports`, or `imports` immediately before *it*, *this*, *them*, *either* or *both*, or the
word `importer`, or `imported by`, or `is not imported` — matches **20**, one of them in this file,
with one sentence matching both. **The importer shape had never been run as a pattern**, and the
paragraph opening *What the sweep did not reach* is why it was run here: the cheapest member of this
column that anybody has ever checked was false, and it was found by a reviewer looking at a file for
another reason.

**Over the whole population, not only the residue, the downstream-set pattern returns 44, of which
22 are in this file.** The **22** outside it are the twenty the paragraph opening *The fourth sweep,
at `7a99bfc`* accounts for, plus exactly **two** written since, and both are in
`Oka/AnalyticSpace/`.

* `Oka/AnalyticSpace/GaloisCategory.lean`'s *"The class can now be cited by name from any module
  downstream of this one, and only from there"* — **true, in both directions and with no
  exception.** The modules of this repository whose import closure contains
  `Mathlib/CategoryTheory/Galois/Basic.lean` are **104**, and that set is exactly this file, its
  **101** downstream modules and the two aggregators: **0** modules can name the class without being
  downstream of it and **0** downstream modules cannot. **The walk is half of this measurement and
  not the whole of it** — the other half is a Mathlib closure per module, which is
  `scripts/import_cost.py`'s graph and not this one, and a verdict of the form *only from there*
  needs both because the *only* is a claim about what is **not** reachable by the other route.
* `Oka/AnalyticSpace/ConnectedComponents.lean`'s *"without this nothing downstream elaborates at
  all"*, of the universe crossing — **not a claim of this class**, in the way
  `Oka/Analytification/CoverIndependence.lean`'s above is not: its *downstream* is of the
  construction and not of the import graph, and under the import-graph reading it is plainly false,
  that file having **97** downstream modules of which nearly all are test modules that name the
  crossing nowhere. **The reading that makes it checkable is the file's own declaration order, and
  under that one it is false by one**: `…SeparatedFiniteEtaleOver.coprodLeftHomeoSigma`, the
  declaration immediately below it, neither names it nor needs it, and only the theorem after *that*
  does. **It is recorded and not repaired**, because the reading its own sentence supports — the
  steps that consume the decomposition — is true, and a sweep that repaired on the weaker of two
  readings would be claiming the stronger.

**The importer column's other decidable members are four, and all four are true.** Each is a binary
claim about a **Mathlib** file rather than a size, so `scripts/import_cost.py` decides it and the
carve-out for *closure-size figures against Mathlib* does not reach it:
`Oka/Analytification/LocalisationIndependence.lean`'s *"`Cover/Directed.lean` is not imported"*;
`Oka/Analytification/OpenBaseFiniteness.lean`'s *"this file does not import it"*, of algebraic
closedness, which holds for `Mathlib/Analysis/Complex/Polynomial/Basic.lean` and for
`Mathlib/FieldTheory/IsAlgClosed/Basic.lean` alike;
`Oka/RingTheory/MvPolynomial/Localization.lean`'s *"that file is not imported"*, of
`Mathlib/RingTheory/Extension/Presentation/Basic.lean`; and
`OkaTest/FiniteMorphism.lean`'s *"`Mathlib.Analysis.Complex.Polynomial.Basic` is imported by this
file for `Complex.isAlgClosed` alone, and `Oka` does not bring it in"*, whose second half is the one
worth running — it is in that file's closure of **3557** and not in `Oka`'s of **3513**. The rest of
the 20 are marginal-cost sentences already pinned to a commit, this file's own text, or statements
of the rule rather than claims about the tree.

**The five grep-decidable verdicts of the third and fourth sweeps were re-run at `0b2759b`, and
all five reproduce with their sets grown.** `Oka/Analytification/AffineCover.lean`: the four
tokens in the code of **0** of **130** downstream modules, against 124 then.
`OkaTest/CoherentFree.lean`: neither spelling in the code of its **3**, so still true and still
vacuous. `Oka/Analytification/UniversalProperty.lean`: `zeroLocusSubspaceι` in **7** of **153**,
`restrictTopIso` in **3**, `ComplexAnalytic.toAmbient` in **0**, which is the token that settles it.
`Oka/Algebra/Category/ModuleCat/Sheaf/Quasicoherent.lean`: `relations.s ≫` in **1** of **101**, and
it is `Oka/Analytification/SheafCoherent.lean`. `Oka/AnalyticSpace/Finite.lean`: `IsProper` as a
whole word in the code of **0** of **226**.

**That last one is where a substring test and a token test part, and the script carries both because
of it.** `--grep IsProper` returns **3** at `0b2759b` — `OkaTest/Axioms/Morphisms.lean`,
`OkaTest/CoveringBaseChange.lean` and `OkaTest/FiniteMorphism.lean` — and every one of the three is
`IsProperMap`, which is a different class and is in the code of **6** modules. A verdict taken from
the wrong one of the two reads *the class this file declines to declare is consumed downstream* off
the class it declines in favour of. **Say which of the two a figure is**, which is the same
instruction the paragraph opening *And pick the token that is unique to the spelling being denied*
gives about which token, one level down.

**The decidable pair column was re-run mechanically at `0b2759b`, and it is clean.** Of the **338**
sentences naming a second module in the sentence, **213** name exactly one, which is where a pairing
can be made without reading; each was given to the walk together with a direction read off the
sentence — *which imports this file*, *this file imports*, *is downstream of this one*, *neither
imports it nor is imported by it*, *is not in this file's import closure* — and the two compared.
**17 disagreed and all 17 are false positives of the direction reader**, each read at its site: a
quotation of a clause this file or another already retired, a *neither … nor* whose negation the
reader inverted, an *imports `Oka` and not `OkaTest`* about the two aggregators, or a pointer at a
third file's claim. **No false pair claim is on `0b2759b`** under that reader, which is a statement
about a heuristic over 213 of 338 sentences and not about the column.

**What this sweep did not read, so that a sixth knows where to start: the 161.** They are the
sentences of the residue that match neither narrow pattern, and they were not opened. The shapes
visible in a sample of them are marginal import costs against Mathlib, *upstreaming this costs*
figures on mirror paths, and *cannot be cited by name here* clauses about a namespace; the first two
are `scripts/import_cost.py`'s graph and out of this class, and **the third is not** — it is the
shape `Oka/AnalyticSpace/GaloisCategory.lean`'s push had to repair across the tree, and a sixth
sweep that
took only that shape would be taking the part of the 161 with a known live history.

**Every figure of this sweep is pinned to `0b2759b`, and this block raises two of them, which is
said here rather than left to be found.** The block matches its own patterns, as the paragraph
opening *The 21 is `d2ae161`'s* predicted of any sweep that quotes what it swept. **At `0b2759b`
with this block applied** the three-column partition is **719 / 344 / 170 / 205** against
`0b2759b`'s **702 / 338 / 167 / 197**, and the downstream-set pattern over the whole population
is **46 / 24** against **44 / 22** — **per-file identical in every other file of the 355**, the
whole of both deltas being
this file's own count going **62 → 79** and **22 → 24**. **The residue's two narrow columns are
`0b2759b`'s 17 and 20**; at `0b2759b` with this block applied the importer one is **25**, the
added ones being this block's quotations, and the downstream-set one is unmoved at **17**, because
what this block adds to that pattern names a module in the sentence and so is not in the residue
at all. **A sixth sweep should
take 44 as `0b2759b`'s**, re-derive its own in its own tree, and expect to have raised it again.

**The figures this block raises are indexed to a tree and not to a head, and that is the whole of
what the paragraph opening *This block is matched by the pattern it reports on* asks of a sweep
that quotes what it sweeps.** *At `0b2759b` with this block applied* describes a tree, and no
later push can change which tree it describes; *at the head that writes this* is inherited by every
later push to this file while the measurement is not, which is why that same paragraph pinned its
own figure to `0c370e5` rather than leaving it in that form. **The difference is not academic on
a linear history**: a branch lands as a commit whose parent is the tip at the time it lands and
not the tip
it was cut from, so a head-indexed figure is a claim about a tree the branch never saw whenever a
neighbour lands first. Between this block's base and this writing `master` moved from `0b2759b` to
`e6a49ab`, and the population that rule picks out went **355 → 357** with it; **not one figure in
this block is a statement about that tree**, and the five sentences that indexed one to *this
head* or to *the head that writes it* have been re-indexed for that reason rather than
re-measured.

**The rule has a seventh object, and it is the fifth one with its domain outside this
repository.** A clause asserting that **Mathlib** lacks something — *Mathlib does not have this*,
*nothing in Mathlib says that*, *no declaration under `Mathlib/…/` binds two of them*, *that
statement is absent from Mathlib* — has the fifth object's grammar, the fifth object's consumers
and the fifth object's failure mode, with the quantifier pointed at a library nobody on this board
commits to. **The three census instruments this file names take their population from `Oka/` and
`OkaTest/`** — `scripts/guard_coverage.py` reads `## Main results` sections,
`scripts/check_docstring_names.py` resolves a name against the environment of `Oka` + `OkaTest`,
and `scripts/module_graph.py`, the sixth object's walk, follows the `import` lines of these
modules and of Mathlib's only in order to close them — **so none of the three can reach a sentence
of this class**, which is why it is an object of its own and not a note under the fifth.
`scripts/import_cost.py`, also named here, *does* walk Mathlib's own graph and is priced against
it, and it is the exception that says where the difficulty is: it prices an `import`, which is a
fact about files, where a sentence of this class is about what Mathlib **states**, and no walk of
import lines decides one of those.

**And it rots by a mechanism the fifth object does not have.** A claim about this tree is falsified
by a commit on this board and can be re-checked by reading one; a claim about Mathlib is falsified
by a **version bump nobody here makes**, and `bash .orchestra/validation.sh` will not say a word.
`scripts/check_docstring_names.py` cannot be pressed into service for it, because it is the
opposite polarity: it checks that a backticked name **resolves**, so it cannot see a claim that
something is *absent*, and a name that stops resolving after a bump fails it for the wrong reason.
**The principle is written down here, in a script docstring, about that script's own figure** —
`scripts/import_cost.py:71`: *"It is a fact about Mathlib at a version and it will drift; the
masking is what does not."* **At `a414f61` no file under `Oka/`, `OkaTest/` or `scripts/` and not
`README.md` cited that line**, which is a claim about a literal string and so is one `grep`; whether
the principle is stated a second time somewhere in other words is not something a `grep` decides
and is not claimed here.

**What such a sentence owes is a version, and then one of three forms.** The version is
`lakefile.toml`'s `rev`, which is `v4.32.0` at `a414f61`, or `lake-manifest.json`'s resolved `rev`,
which at that commit is `81a5d257c8e410db227a6665ed08f64fea08e997`; name one, and prefer the second
where the claim is fine enough that a patch release could move it.

* **(a) a quoted instrument, run at that version.** `Oka/Topology/Connected/Clopen.lean` is the
  worked example and, of the thirty-one sentences the hand pass below leaves in class at
  `a414f61`, the only one that pins a version at all: *"at `v4.32.0` no statement in Mathlib
  mentions `connectedComponent` together with a disjoint union at all: `grep -rn
  'connectedComponent' Mathlib/ | grep -iE 'sigma|Sum\.|coprod'` returns **nothing**, against
  **56** occurrences of `connectedComponent` in the destination file itself."* A command, a
  verdict, a control and a version, in one sentence.
* **(b) a pointer to the sibling sentence that carries (a)**, for a claim repeated across files.
  At `a414f61` *`CategoryTheory.GlueData.ofGlueData'` has no projection lemmas in Mathlib* is
  **seven** sentences in seven files — `Oka/Analytification/AffineCover.lean`,
  `Oka/Analytification/ComparisonSquare.lean`, `Oka/Analytification/SpecAffineCover.lean`,
  `Oka/CategoryTheory/GlueData.lean`, `Oka/Geometry/RingedSpace/PresheafedSpace/Double.lean`,
  `Oka/Geometry/RingedSpace/PresheafedSpace/Gluing.lean` and `README.md` — of which **two**, the
  fourth and the sixth, say what was run (*`grep` finds it only in its own defining file*). **Five
  sites inherit an instrument they do not print**, which is neither bare nor (a); what such a site
  owes is the pointer. **Swept on 2026-09-21 by taxis #2118, which is why the paragraph above is
  pinned**: all five now name `Oka/CategoryTheory/GlueData.lean`, which carries the version, the
  rev and the command as run, and the two instrumented sites carry the version too. **The scan does
  not see that sweep** — every one of its per-file rows is unmoved across it, because a pointer is
  not one of the six spellings and the universal it points at stays where it was; `--list` diffed
  between the two commits is what shows it, and a sweep of form (b) owes that diff rather than the
  headline. **That flatness is one case of an arithmetic and not a rule about the form**, and the
  close of *This block is matched by the scan it publishes* below is where the arithmetic is and
  where the sweep that comes out the other way is named.
* **(c) a bounded restatement that is not a universal at all.**
  *`Mathlib/Topology/Covering/Basic.lean` has only conjugation by a homeomorphism* is settled by
  reading one file; *any cancellation lemma for `IsCoveringMap` is absent from Mathlib* is not
  settled by reading anything.

**The fourth form is not honest, and it is worse than carrying no instrument: a scan whose spelling
cannot in principle decide the claim.** Its exactness is read as evidence, and the reader who would
otherwise have gone and looked does not. Round 1 of lana-agents/oka#597 was rejected on exactly one
ground and the ground was one of these: *"no declaration under `Mathlib/CategoryTheory/Galois/`
binds two fibre functors of one category — its **eleven** files carry **37** occurrences of `⥤
FintypeCat` between them … no one line has two, every `variable` line among them binds exactly
one"*. **Every numeral in it was exact and the claim was false**, because the second such functor
is spelled `F ⋙ E` or inherited from a `variable` block a hundred lines above;
`CategoryTheory.PreGaloisCategory.FiberFunctor.comp_right` and
`CategoryTheory.PreGaloisCategory.autEquivAutWhiskerRight` are two of the three counterexamples,
and that branch's round 2 dropped the scan rather than keeping it. **The test to apply before
publishing one is three questions**: can the thing being denied be spelled another way, can it be
inherited from a binder the scan does not read, and can it be generated? A *yes* to any of the
three means the scan narrows and does not decide, and the sentence has to say so instead of
reporting a number.

**A second instance of that shape is live in this tree and is repaired in the push that writes
this, and it is worth having because the escape is a spelling and not a telescope.**
`Oka/Topology/Covering/Basic.lean` read *"the direction Mathlib does not have in any form: across
`Mathlib/Topology/Covering/`, `isClosedMap` occurs only inside proofs"*. At `v4.32.0` the exact
token `isClosedMap` occurs **once** in that directory and it is inside a proof, so the clause is
true of what it wrote; `IsClosedMap`, which is the predicate it means, stands in the **statements**
of `IsClosedMap.isEvenlyCovered_of_openPartialHomeomorph` and
`IsClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn` and in the `alias` beside the second. **A
capital letter is the whole of the difference**, and the headline the scan was offered for is true
for a reason the scan never touched: those three occurrences are the hypothesis and not the
conclusion.

**And the environment is not Mathlib.** `scripts/DumpEnvNames.lean` dumps the environment of `Oka`
+ `OkaTest`, which imports some of Mathlib and not all of it — the rework of lana-agents/oka#597
measured **ten** of `Mathlib/CategoryTheory/Galois/`'s **eleven** modules in that dump at its own
head, and the same two counts hold at `a414f61` on a run of this block's — so an absence measured
in that dump is an absence from **this build's imports**, which is a weaker statement standing one
word away from the one that will be read.

**The scan is `python3 scripts/mathlib_absence.py`, and it reports pattern hits rather than
defects.** Six spellings, over the comment content of every tracked `.lean` under `Oka/` and
`OkaTest/` and over the whole of every tracked `.md`, `.py`, `.sh`, `.yml` and `.toml` under those
and under `scripts/`, plus the three root files, **whitespace-normalised before matching** because
a hard wrap at column 100 is where a clause of this class hides — the failure mode taxis #1712
records of `git log -S`. Every run prints the version and rev `lake-manifest.json` pins, because a
hit list is worth nothing without one. **At `a414f61` it returns 34 sentences in 25 files, against
a denominator of 1112 sentences naming Mathlib at all in 215 files**, which `--mentions` reports
and which exists because the six shapes are spellings and not meanings: the clause
*`Mathlib/Topology/Covering/Basic.lean` has only conjugation by a homeomorphism* is the same claim
as *Mathlib has no cancellation lemma* and matches nothing, and neither does a negative carried by
*none*, by a noun, or by a sentence that never writes the word. **Do not read the 34 as a count
of the class.**

**Classification is a hand pass, and three of those 34 are out of class**, each for a reason no
pattern sees: two in `Oka/AnalyticSpace/FundamentalGroup.lean` are about **that file's own
contents** with Mathlib as the yardstick — *"none proves anything Mathlib does not"* — and are
already acquitted by the fifth object's self-limiting spelling; one in
`scripts/check_docstring_names.py` is a universal about Mathlib namespaces that the next clause
**retracts** — *"that is false"* — and then refutes with four counterexamples. Of the **31** left,
**6** carry an instrument in the same sentence, **1** pins a version, and **25** are bare. Those
four figures are `a414f61`'s and a later sweep should re-take them at its own head rather than
inherit them.

**Swept at `a414f61`: one file of the twenty-three, and the bound is chosen rather than
reached.** (The 31 in-class sentences are in 23 files: `Oka/AnalyticSpace/FundamentalGroup.lean`
and `scripts/check_docstring_names.py` drop out of the 25 with the three out-of-class ones.)
`Oka/Topology/Covering/Basic.lean` carries **six** of the 31, more than any other file at that
commit, and its claims are about `Mathlib/Topology/Covering/` and
`Mathlib/Topology/SeparatedMap.lean`, which are three files and one file and can be read out.
All six are repaired into (a) or (c), each with the retired wording kept as a dated record and
nothing struck. **One of the six was false**:
*"Mathlib has no cancellation lemma for `IsCoveringMap` at all"*, where
`IsCoveringMap.comp_homeomorph_iff` is `IsCoveringMap (f ∘ g) ↔ IsCoveringMap f` at a homeomorphism
`g` and its forward direction cancels one — and the clause offered in support named
`comp_homeomorph` and `homeomorph_comp` and not the two `_iff` lemmas standing beside them in the
same namespace. **The *at all* makes it false a second way**, since
`IsCoveringMap.eq_of_comp_eq` and its three companions cancel the covering map out of an equality
of composites at merely continuous companions.

**The remaining 25 of the 31 are untouched**, and **the two nearest are named rather than left to
be found**. `Oka/Analysis/Complex/FundamentalGroup.lean` and
`Oka/AnalyticSpace/FiniteEtaleOver.lean` each say that Mathlib has no composition or cancellation
lemma for `IsCoveringMap`, in a clause bounded to one file —
*`Mathlib/Topology/Covering/Basic.lean` has only conjugation by a homeomorphism* — and
**both stand, on a reading this push pins instead of assuming**: a composition
or cancellation lemma *for `IsCoveringMap`* is one that writes `IsCoveringMap` of a composite, and
the four in that file that do are the two builders and their two `_iff` forms, every one of them at
a homeomorphism. **Under a wider reading of *cancellation* neither would stand**, because those
four `_of_comp` lemmas cancel `f` out of an equality of composites; they write `IsCoveringMap` only
as a hypothesis on `f` alone and conclude that two companions agree, which is what puts them
outside the bounded reading and what makes saying so worth a clause. That is this object's own
first question — *can the thing being denied be spelled another way?* — asked of a phrase rather
than of a token, and the swept paragraph in `Oka/Topology/Covering/Basic.lean` now carries both
halves of the split so that neither site rests on a reading nobody wrote down. **That is what form
(c) buys**: each of the two clauses is settled by reading one named file, where the enumeration
next door was not, and it is why the two sites are named here instead of being left in the 25 in
silence.

**Two figures that sweep leaves behind, and both are about the instrument rather than about the
file.** `Oka/Topology/Covering/Basic.lean` carries **19** sentences naming Mathlib at `a414f61`
and the scan matches **6** of them; read by hand, three of the other thirteen are negatives too —
*Mathlib has the relative form and not this one*, *`IsSeparatedMap.t2Space` in
`Oka/Topology/SeparatedMap.lean`, which is not*, *which Mathlib also does not have* — and **each
is about a named declaration**, which is what makes a negative bounded in the sense of (c) and is
why the six shapes did not have to reach them. And the file's raw count goes **6 → 8** across the
push that sweeps it, not 6 → 0, because **a dated record quotes the wording it retires**: repairing
into an exempt spelling *raises* the number a scan of this class returns, exactly as the fifth
object's sweeps found of theirs. **Neither figure is a defect count**, and a later sweep that
reports a rise should first check whether it is reading its own records.

**This block is matched by the scan it publishes, as the fifth object's is matched by its own.**
The **34 / 25** above is `a414f61`'s and does not include what the push writing this adds; at
`a414f61` with that push applied the scan returns **53** over **27** files, and the whole of the
rise is in three files — `OkaTest/Axioms.lean` **0 → 9**, this block's quotations of the sentences
it decides; `scripts/mathlib_absence.py` **0 → 8**, its docstring's worked examples together with
its self-test fixtures; and `Oka/Topology/Covering/Basic.lean` **6 → 8**. **No other file's count
moves.** A later sweep should re-derive its own figure at its own head, and **what it should
expect is arithmetic rather than a property of the repair's form**: the headline moves by the
number of sentences the push *adds* that match one of the six shapes, minus the number it
*removes* that did.

**Two later sweeps have now tested that, and they come out opposite ways.**
`lana-agents/oka#605` — taxis #2118, a sweep of form (b) — is `ae732d9` → `d4c49af`, and it is
**53 over 27 files at both ends with the per-file table byte-identical, every row**; `--list`
diffed is **6 out and 6 in**, because a (b) repair keeps the universal in a spelling the scan
still matches and adds the pointer beside it, and because the dated records it writes say *what
the clause carried* rather than re-quoting the absence. The one clause those records do quote,
*`grep` finds `ofGlueData'` only in its own defining file*, matches none of the six either.
`lana-agents/oka#606` — taxis #2127, a sweep of form (a) — is `a3d656d` → `57e5a1a`, and it is
**53 → 55 in 27 files at both ends**; `--list` diffed is **2 out and 4 in**, the two retired
clauses against the two repaired sentences and the two dated records quoting them, so the
headline moves by `4 − 2`.

**Neither the form nor the phrase *repairs into an exempt spelling* predicts either figure**, and
`#606` is what shows it: it repairs into a spelling that is **still matched** — *Mathlib has no
lemma about the `hom` or the `inv` of …* and *Mathlib has no statement of it and no instance that
yields it* are both hits — so the whole of its rise is its two records, and a repair that did
reach an exempt spelling would *lower* the figure by one per site with only a quoting record to
put it back. **So count your own added and removed hits before reading the headline**, and where
the two are equal expect it flat and diff `--list` instead.

**That clause read *and should expect to have raised it again* until 2026-09-21**, with no
qualification — `git show 57e5a1a:OkaTest/Axioms.lean` carries it at `:1145–1146`, wrapped after
*have*. It was written at `ae732d9`, by the push that wrote this whole block, on the only instance
it had: that push's own **34 → 53**. `lana-agents/oka#605` was the first later sweep to test it
and came out flat, which is what taxis #2129 was filed on; `lana-agents/oka#606` was the second
and raised it. **The prediction was wrong and the mechanism *Two figures that sweep leaves
behind* gives is not** — *a dated record quotes the wording it retires* — and both of `#606`'s
do, which is the whole of its `4 − 2`. **The push writing this repair is the third data point and
is its own**: `57e5a1a` → here is **55 → 56 in 27 files**, `--list` **1 in and 0 out**, and the
one is the sentence in the paragraph above that quotes what `#606` repaired into; the clause
retired here was never a hit, so `1 − 0` is the whole of it.

**Most mirror-tree material is routed by a row, and a small tail of it is deliberately routed by
none.** `README.md`'s *Layout: the Mathlib mirror tree* defines a mirror-tree file by its path — a
file under `Oka/` mirroring a path under `Mathlib/`, holding no complex-analytic mathematics and
staged for upstreaming. **That is 221 of the 645 guards at `27c185a`**, and two rows exist to route
almost nothing else: `OkaTest/Axioms/Sheaves.lean` is **87 of 87** mirror-tree, of
`Oka/Geometry/RingedSpace/` together with `Oka/Topology/` and `Oka/AlgebraicGeometry/`, in the
naming form its own docstring puts the same fact in; the three directories still exhaust that file
under a `moduleData` join at the commit that writes this. `OkaTest/Axioms/RingTheory.lean` is **19
of 19**. So being mirror-tree is not what decides whether a row names a module, and the criterion
above applies to mirror-tree modules exactly as to any other.

**What gets no row is a mirror-tree module whose subject no existing row names.** Such a module
has no subject *in this development*, so the only row that could name it would name a source
directory rather than a topic, and the table routes by topic. **Guard one in the file of the
analytic result that motivated it**, under that result's heading — which is what
`OkaTest/Axioms/Morphisms.lean` already says of `Oka/Topology/Covering/Basic.lean`: *"mirror-tree
topological criteria … say nothing about analytic spaces; they are guarded here rather than apart
from their consumers."* `OkaTest/Axioms/AnalyticSpace.lean` reaches the same placement for a
module the sheaves row *does* route — *"general locally-ringed-space material with **no row of its
own** in the topic table … it sits here because the only thing that uses it is the rigidity
statement below"* — so this paragraph records a practice with two independent precedents rather
than inventing one.

At `27c185a` that tail is **18 guards in six modules**, against 645 in all: seven from
`Oka/CategoryTheory/GlueData.lean` (in `OkaTest/Axioms/AnalyticSpace.lean`), five from
`Oka/Topology/Covering/Basic.lean` (in `OkaTest/Axioms/Morphisms.lean`), three from
`Oka/Topology/IsLocalHomeomorph.lean` (in `OkaTest/Axioms/Sheaves.lean`), and one each from
`Oka/CategoryTheory/Limits/Shapes/KernelBiprod.lean` (in `OkaTest/Axioms/SheafOfModules.lean`),
`Oka/Topology/Category/TopCat/Opens.lean` (in `OkaTest/Axioms/Analytification.lean`) and
`Oka/FieldTheory/IsAlgClosed/Basic.lean` (in `OkaTest/Axioms/RingTheory.lean`). **The rule above
was being written down for the first time when that tail was measured, and the tail did not
follow it**, and the members that do not are named here rather than counted. Of the six modules
that record enumerates, these sit apart from their consumers' guards:

* **`Oka/CategoryTheory/GlueData.lean`**, the largest member. At `c48bf8a` the one module under
  `Oka/` that imports it is `Oka/Analytification/AffineCover.lean`, whose guards are all in
  `OkaTest/Axioms/Analytification.lean`; and its guards sit under a heading of their own rather
  than under an analytic result's, so it fails both halves of the rule.
* **`Oka/Topology/IsLocalHomeomorph.lean`**, whose one importer under `Oka/` at that same commit
  is `Oka/AnalyticSpace/CoveringSpace.lean`, guarded in `OkaTest/Axioms/Morphisms.lean`. It was
  placed beside the file it was *written for*, which **deliberately does not import it** for the
  import-cost reason that file gives, and `OkaTest/Axioms/Sheaves.lean`'s heading for it says so.
* **`Oka/FieldTheory/IsAlgClosed/Basic.lean`**, which at that commit **no module under `Oka/`
  imports**: `Oka/AnalyticSpace/CoveringMap.lean` names its one theorem in a docstring and does
  not import it, and at that commit the one proof term in the repository that consumes
  `IsAlgClosed.card_setOf_pow_eq` is in `OkaTest/FiniteMorphism.lean`, a file this repository does
  not guard although `OkaTest/Axioms/RingTheory.lean` guards that theorem. **So** there is no
  analytic result to place it beside — the conclusion of the measurement above it and not a second
  claim, and it goes false exactly when that measurement does.

**Read a consumer off the imports, not off a name grep.** All three were got wrong that way
before they were measured, and `Oka/CategoryTheory/GlueData.lean` was got wrong in the draft of
this very paragraph: `ofGlueData'` is Mathlib's name and several files mention it, and at
`c48bf8a` one module under `Oka/` imports the module that proves things about it.

**The instrument is `git grep -l -E '^import <module>$'`, and the population the three figures
above are taken over is `Oka/` — not the repository.** Saying which is not pedantry, because the
grep answers differently on either side of that line. `Oka.lean` is the aggregator `mk_all`
generates; it imports every module of the library, so it is a hit for all three and is excluded
above. And at `c48bf8a` **70 of the 93 files under `OkaTest/` import that aggregator** rather than
any module of it, so under `OkaTest/` an import grep separates no consumers at all — which is why
the third bullet reaches that side by a name grep instead, and says so. **Moving any of them is a
tidy-up and not a defect in the table**, and none of the three had been moved when this paragraph
was pinned at `c48bf8a`.

**The figure is here so that a later sweep can tell growth from noise**: a tail that stays near
this size is the expected one, and a tail that doubles means a row really is missing.

**That test has been run at `a8c2f63` and it does not answer on its own terms.** Re-counting the
six modules that record enumerates gives **22** guards there against the 18 recorded, with
`Oka/CategoryTheory/GlueData.lean`, `Oka/Topology/IsLocalHomeomorph.lean` and
`Oka/FieldTheory/IsAlgClosed/Basic.lean` the larger side at **14** to 8 — growth the doubling
criterion reads as noise. But the tail is what the routing table leaves unrouted and not that
record's list, and at `a8c2f63` three further mirror-tree modules carry guards and are routed by
no row of it: `Oka/Analysis/Calculus/Implicit.lean`, whose guards are the level-set and
local-homeomorphism criteria that put `Oka/Topology/IsLocalHomeomorph.lean` in the tail already,
with six in `OkaTest/Axioms/Morphisms.lean`; and `Oka/SetTheory/Cardinal/Finite.lean` and
`Oka/Logic/Equiv/Set.lean`, which no row names at all, with one each in
`OkaTest/Axioms/Morphisms.lean` too and both beside the degree results that consume them — which
is this rule being followed. Read that way the tail is **30 guards in nine modules** at
`a8c2f63`, and every module that joined it is one the `27c185a` record does not name.
**Re-counting the modules a record enumerates answers a question about those modules, and this
test is about the tail**: a missing row shows up as a new member and not as a bigger one.

**Two modules look like that case and are not**, and the difference is the whole of the criterion.
`Oka/Algebra/MvPolynomial/PDeriv.lean` and `Oka/Algebra/MvPolynomial/Taylor.lean` are mirror-tree
and are guarded in `OkaTest/Axioms/Analytification.lean`, but the general commutative ring theory
row does name their subject — `Oka/Algebra/MvPolynomial/Equiv.lean` and
`Oka/Algebra/MvPolynomial/Funext.lean` are guarded under it. **A routed module guarded elsewhere
is a different question from a module no row routes**, and this paragraph does not take it.

## What these guards cover, and what they do not

**Nothing here claims to be complete, and the gap is measured rather than guessed.**
`python3 scripts/guard_coverage.py` counts the declarations this repository's module docstrings
advertise under a `## Main results` heading and asks which of them some `#print axioms` names. **At
`7b6fd39`, the base this file's tranche was written on, that was 502 guarded names against 506
advertised declarations, of which 179 were named by no guard at all, spread over 63 files; the
nineteen guards added below account for nineteen of those 179, leaving 160 unguarded in 61
files.** **A second tranche of twelve was measured against `0ac74d4`, where the gap stood at 162
in 61 files, and leaves 150 in 60.** Ten of those twelve are the whole of
`Oka/ChangeOfCoordinates.lean`'s `## Main results`; the other two are the ones lana-agents/oka#201
put into the gap by *advertising* them, which is the mechanism of the next paragraph running the
other way and the reason a tranche is a standing job rather than a finite one. So **still close to
a third** of what the library announces as its main results carries no axiom assertion. Neither
list contains the other: **175 guarded names are advertised in no `## Main results`**, which is
not a defect, since a guard on a lemma no docstring announces is worth exactly as much as one on
a lemma it does — and that figure is unchanged across both tranches, which is what says each was
drawn from the advertised-and-unguarded pool and not from somewhere else.

The figures are pinned to a commit rather than to a date, because a paragraph that says *"on the
tree this lands in"* cannot be re-run without first finding which tree that was. **The two totals
are what goes stale; the gap is not**, which is why the sentence above reports a base and a delta
rather than a current total. A pull request that guards the result it advertises moves both
totals and leaves their difference alone: between `7b6fd39` and `3f185f0` two of them landed, the
totals went 502 and 506 to 512 and 516, and the gap stayed 179 in 63 files. So a later run that
reproduces the 160 and the 61 has reproduced this measurement even if neither total matches.

**That is a measurement and not a rule, and this file does not turn it into one.** Some of the 160
should probably stay unguarded — `Oka/Analytic/ParametricCircleIntegral.lean` is general complex
analysis with a Mathlib destination and contributes 17 of them — so the right number is not zero,
nobody has decided what it is, and the script is a reporter run by hand rather than a check in
`.orchestra/validation.sh`. What the paragraph above rules out is only the reading that an
absent guard means somebody decided against one.

## Updating an assertion

If a theorem is legitimately restated or renamed, do **not** delete its assertion. Run the
corresponding `#print axioms` (for instance with `lake env lean OkaTest/Axioms/<File>.lean`, or
in the editor) and paste the message Lean actually prints back into the expected docstring.
The expected message must stay `[propext, Classical.choice, Quot.sound]`: any other axiom —
`sorryAx` above all — is a regression, not something to record.
-/
