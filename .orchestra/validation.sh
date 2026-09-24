#!/usr/bin/env bash
# Validation for the `oka` repository. Run it from anywhere:
#
#   bash .orchestra/validation.sh
#
# CI (`.github/workflows/lean_action_ci.yml`) runs only `lake build --wfail` and `lake lint`;
# every other check below is local to this script. What "lint" means is defined once, as
# `lintDriver` in `lakefile.toml`, so that at least that much cannot drift.
#
# Exits 0 only if every check below passes; the first failing check stops the script and
# exits non-zero.

set -uo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/.." || exit 1

# Verify the worktree is clean.
if [ -n "$(git status --porcelain)" ]; then
  echo "The working tree is not clean. Commit changes or discard if temporary."
  git status --short
  exit 1
fi

# Verify the library is free of `sorry`. This runs before the build because it is instant and
# the build is not; it is a fast fail, not the only defence. **`lake build --wfail` below does
# catch a `sorry`** — measured 2026-08-20 by planting one and watching
# `declaration uses \`sorry\`` become `error: build failed`. (This comment previously said the
# build "would not fail on it", which is true of a bare `lake build` and false with `--wfail`.)
#
# The negative lookarounds keep `sorryAx`, `unsorry` and `sorry_foo` from matching. The bare word
# *does* match in comments and docstrings, so prose under `Oka/` should avoid it.
if grep -rnP '(?<![A-Za-z_])sorry(?![A-Za-z_])' --include='*.lean' Oka Oka.lean; then
  echo 'Found a `sorry` in the library, at the location(s) listed above.'
  exit 1
fi

# Fetch build cache. Needed before the two steps below, both of which build Mathlib
# artifacts.
lake exe cache get || exit 1

# Verify all .lean files are imported by the root module `Oka.lean`.
lake exe mk_all --lib Oka --git --check || exit 1

# Verify everything builds, and that it builds without warnings.
lake build --wfail || exit 1

# Verify the environment linters are clean — fourteen are in the default set here, nine of them
# Batteries' and five Mathlib's; `#list_linters` prints the lot. These check the whole
# environment, not one file: missing docstrings on definitions, names that break the naming
# convention, `@[simp]` lemmas whose left-hand side is not in `simp` normal form, and about ten
# more. `lake build` sees none of it, which is how the project reached 2026-08-20 with 19
# findings nobody had looked at.
#
# The linter and the module it runs on are configured once, as `lintDriver` in `lakefile.toml`,
# so that this script and the CI workflow cannot disagree about what "lint" means. Note that
# `#lint` in a scratch file that does nothing but `import Oka` is NOT a substitute: it only
# lints the current file's declarations and reports a green on an environment full of findings.
#
# Needs the oleans, so it has to come after the build; given those it takes a few seconds.
lake lint || exit 1

# Verify Mathlib's text-based style linter is clean. Until now it was enforced by nothing at
# all, despite being quoted in every pull request description on this project.
#
# It checks *less* than its name suggests, and it has more parts than the name of one executable
# suggests. `lintStyleCli` (`.lake/packages/mathlib/scripts/lint-style.lean:268-271`) sums five
# terms, and **seven checks actually run over this repository**. Five are per-file, inside
# `lintModules`: Windows line endings, trailing whitespace, a space before a semicolon,
# disallowed unicode and variant selectors, and the string "Adaptation note". Two are about
# module *names*: `UpperCamelCase`, and filenames forbidden on Windows or on Nix (`CON`, `LPT1`,
# `*`, `?`, `!`, ...). Line length and copyright headers are *build* linters, caught by `lake
# build --wfail` above via `weak.linter.mathlibStandardSet`. Do not read a green `lint-style` as
# "Mathlib style has been checked"; it is disjoint from, and much narrower than, the environment
# linters.
#
# **Three further sub-checks are gated off by default, and not one of them can simply be switched
# on here.** Two are the remaining terms of the five, `linter.checkInitImports` and
# `linter.allScriptsDocumented`; the third, `linter.pythonStyle`, is nested inside `lintModules`,
# which is why the sum has five terms while six things in it have a switch. Putting each in
# `[leanOptions]` in turn, 2026-08-24, gives a crash and not a report:
#
#   checkInitImports      uncaught exception, no such file or directory: Mathlib.lean
#   allScriptsDocumented  uncaught exception, no such file or directory: scripts/README.md
#   pythonStyle           could not execute external process './scripts/print-style-errors.sh'
#
# Each reads a path out of the working directory that only Mathlib's own checkout has — and
# Mathlib turns all three on for itself, at `lakefile.lean:32-34`, which is why the paths are
# there and the crashes are here. The first is about `Mathlib.Init` and there is nothing here
# for it to do; the third is `defValue := false` where it is registered, and carries a TODO
# saying the Python linters assume they are run from Mathlib's `scripts/`.
#
# **The second is about our `scripts/` directory, and the decision is not to write
# `scripts/README.md`.** With one planted the check reports six undocumented scripts —
# `docstring-names-ignore.txt` among them, since only Mathlib's own `noshake.json` and
# `nolints-style.txt` are exempt — and **a file holding those six names in backticks and not one
# word of prose exits 0**. Measured, and it is the whole enforcement value: the check reads for
# `` `name` `` and can say nothing about whether a description is present, let alone true.
# Each script under `scripts/` documents itself in its own header instead, which says what the
# tool is *for* rather than only that it exists; an index that no check can keep honest is the
# defect this repository repairs most often, and buying one to silence a switch that is already
# off is the wrong trade.
#
# One trap, and it is upstream's rather than ours: `modulesOSForbidden` is gated on
# `linter.modulesUpperCamelCase` (`Mathlib/Tactic/Linter/TextBased.lean:602`) and not on the
# `linter.modulesForbiddenWindows` declared directly above it at `:589`, which is registered and
# **read nowhere in Mathlib**. Both default `true`, so both module-name checks do run here. But
# setting `modulesUpperCamelCase = false` to allow one module name would silently switch off the
# forbidden-filename check too, and setting `modulesForbiddenWindows = false` would do nothing.
#
# The `nolints file could not be read` warning is harmless and always present, and its absence
# is a choice rather than an omission. `lint-style` reads `scripts/nolints-style.txt` relative
# to the working directory for a list of findings to suppress, and on failing to open it prints
# that line to stderr and continues with an empty list
# (`.lake/packages/mathlib/scripts/lint-style.lean:262-267`). Creating the file — even
# completely empty — silences the warning and still exits 0; that was measured in both shapes,
# so this is a decision and not an untried alternative.
#
# **The reason not to create it is that there is nothing for it to hold.** Every one of the
# seven checks that run, listed above, reports a mechanical defect in a file of ours, every one
# of them is fixable, and there are none. Mathlib's own eleven entries are all
# self-references — the linter for the string "Adaptation note" firing inside
# `Mathlib/Tactic/AdaptationNote.lean` and inside the linter's own implementation — a case this
# repository cannot have. So an empty file here would exist only to suppress the notice of its
# own absence, while carrying the one capability we should not want: silencing a fixable style
# finding instead of fixing it.
#
# That is not hypothetical. `scripts/docstring-names-ignore.txt` was created on 2026-08-22 at
# 16:53Z saying "This file is empty, and the intention is that it stays that way", and had two
# entries by 19:49Z the same day. Those entries are correct and that file earns its keep — its
# checker has a real class of unfixable false positive. This one does not.
#
# If you disagree, the change is `touch scripts/nolints-style.txt` plus a header comment, and it
# needs an argument about what would ever go in it rather than about the warning.
lake exe lint-style Oka || exit 1

# Verify that every backticked dotted name in a comment or docstring resolves to something.
#
# Nothing above looks inside a comment. `lake build --wfail` sees only elaborated terms, `lake
# lint` checks declaration *names*, `lint-style` checks whitespace and unicode, `mk_all
# --check` checks imports, and the declaration-name diff that every pull request body runs
# compares declarations rather than the prose citing them. A backticked name in a `/-- … -/`
# block that names nothing at all passed every one of them until this line existed, and on
# 2026-08-20/21 that cost four separate findings in one day, each caught by a human who happened
# to be reading the file for another reason.
#
# `scripts/check_docstring_names.py` documents its own rules; the short version is that it is
# deliberately permissive — a name resolves if *any* declaration in the environment ends with
# it, or it is a module, or a file in the repository, or field notation — because a check that
# cries wolf is worse than none on a project that quotes a green `validation.sh` as evidence in
# every pull request body. `scripts/docstring-names-ignore.txt` is the escape hatch, and every
# entry in it is a place this checker has been told to stop looking; prefer fixing a rule to
# growing it. **Neither this sentence nor that file's own header says how many entries there
# are**: nothing checks a count, and the two that used to say otherwise were both written in the
# same commit and both false two hours fifty-six minutes later. The dates are in the
# `lint-style` comment above.
#
# It runs `lake env lean scripts/DumpEnvNames.lean` to read the environment, so it has to come
# after the build; given the oleans it takes about ten seconds, nine of them the import. It
# needs `python3`, which is the only thing in this script that does.
#
# **The self-test first, and a failure of it means something different from a failure of the
# line below it.** The check reports that the *tree* is wrong — a backticked name that resolves
# to nothing — and the fix is in a `.lean` file. The self-test reports that the *instrument* is
# wrong, and until it is fixed a green line below is not evidence of anything: it plants each
# defect the checker exists to find and confirms the checker still finds it, so a check whose
# assertion has silently gone vacuous fails here rather than passing everywhere. That is the
# more urgent of the two and it is why it runs before rather than after.
#
# This option arrived the same day it was wired in (2026-08-30, #242), so unlike the one below
# it was never green-by-omission for long. The one below it was: `check_module_docstrings.py`
# has had a `--self-test` since 2026-08-23 and neither this script nor CI ran it once in the
# seven days between. Both were verified only by sessions running the command by hand and
# quoting the output in a pull request body — a convention, kept by four of them, and the thing
# a `|| exit 1` exists to stop being a convention.
#
# Unlike the check, the self-test needs no build and no oleans: it plants its fixtures in a
# `TemporaryDirectory`, and exactly one of its checks reads the real tree at all — what it does
# there is a text walk, not a build. That one check is worth more than one walk, and the count is
# below with what the walks cost; a reader who takes "one" for a walk count gets it wrong by
# four. It could therefore run earlier
# than this; it is here so that the instrument and the check it verifies stay one comment block
# apart rather than two places to keep in step. **Order 2s, and a small multiple of that on a
# loaded machine** — measured 2026-08-30 at 1.94–1.97s over three runs on a warm checkout, against
# 1.85–1.92s before the two `GENERATED_COMPONENT` checks were added and 1.76–1.79s before the four
# field-notation ones. Essentially all of it is still the `os.chdir` negative control, which walks
# the real tree four times at about 0.45s a walk; every other check runs on a planted fixture of a
# line or two, and the six that check the field-notation rule plant an *environment* as a `--dump`
# file rather than reading the real one, so the count of real-tree readers above is unchanged.
#
# **This line read a bare `1.8s` until 2026-08-30**, which was the true cost before those
# checks existed. It is stated as an order and a spread because a single number measured on one
# machine is what let the `check_module_docstrings.py` pin below go three times stale before
# anybody noticed — and it has now absorbed two additions on the same day without moving off
# `order 2s`, which is the property it was rewritten for. The field-notation checks re-enter this
# script as a subprocess in order to exercise `main()` rather than an internal function — **sixteen
# of the twenty-six checks now do**, and that figure has been wrong twice: it read `eight` from
# 2026-08-30, which was right when written, through the four tag checks of taxis #1326, which took
# it to twelve without moving it, to the four walk checks of taxis #1337, which take it to sixteen.
# An interpreter start that imports this script costs 0.029s against 0.009s for a bare one, so
# eight extra re-entries are worth about a quarter of a second and the pin above did not move: on
# one machine on 2026-08-31, five runs each, the walk checks measured 2.33–2.38s against
# 2.32–2.49s without them, which is inside the noise of that machine and says nothing about the
# 1.94–1.97s recorded on another.
# Against a whole-script time in minutes, and it buys the only evidence that the line below is
# an instrument rather than a `pass` statement.
python3 scripts/check_docstring_names.py --self-test || exit 1
python3 scripts/check_docstring_names.py || exit 1

# Verify that every `.lean` file under `Oka/` has a module docstring with a
# non-empty body.
#
# The check above looks at the names *inside* a docstring, so on an empty one it finds nothing to
# check and passes; and an empty `/-! -/` elaborates, so the build does not see it either. Seven
# files under `Oka/` carried one from the second commit in the repository until 2026-08-23 — 892
# lines and 74 declarations between them, all of them in the mirror tree, every one of them
# therefore making the claim a mirror path makes without stating it — and this
# script exited 0 on all seven for four months.
#
# It is deliberately the narrow rule: a non-empty body, and nothing about what the body says —
# except that the block has to be the module docstring and not a `/-! ### … -/` section header,
# which is a distinction and not a wording rule, and without which the check would pass a file
# whose module docstring had been deleted outright.
# `scripts/check_module_docstrings.py` explains why, and has a `--self-test` that plants each
# defect and confirms it is reported — **which is the first of the two lines below**, since a
# check that has only ever been seen to pass is not evidence of anything. That sentence was here
# from 2026-08-23 and named a capability the script offered while this file ran neither it nor
# the other one; it now describes what runs, which is what it always read as.
#
# Same division as above: the self-test failing means the *instrument* is broken and nothing the
# line after it prints can be trusted; the check failing means a `.lean` file is missing a
# module docstring. It plants its fixtures in a `TemporaryDirectory` and never reads the real
# tree, so its cost is interpreter starts and not I/O: three of its checks run the checker as a
# subprocess in a planted `git init` tree, which is the only way to exercise the repository-root
# resolution `main()` does and a direct call to `check` skips.
# **Order 0.1s, and a small multiple of that on a loaded machine** — measured 2026-08-30
# at 0.120–0.123s over three runs on a warm sixteen-core checkout under moderate load, and at
# 0.27–0.45s the same day, on the same code, by the session that wrote those three checks.
# The figure is stated as an order and a spread on purpose: this line previously read **0.04s**,
# which was the true cost before the three subprocesses existed, and a single number measured on
# one machine is what let it go three times stale without anybody noticing.
#
# Text only: no build, no oleans, so both could run anywhere in this script. They are last
# because they are the cheapest and a failure of the check is the least urgent.
python3 scripts/check_module_docstrings.py --self-test || exit 1
python3 scripts/check_module_docstrings.py || exit 1

echo "Validation succeeded."
