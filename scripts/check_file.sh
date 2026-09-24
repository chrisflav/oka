#!/usr/bin/env bash
# A fast per-file check that applies the *same* Lean options the build applies.
#
#   bash scripts/check_file.sh Oka/Foo/Bar.lean [more files…]
#   bash scripts/check_file.sh --self-test
#
# This exists because `lake env lean FILE.lean` **does not apply `lakefile.toml`'s
# `[leanOptions]`**. That is measured, on three of the block's five entries; *why* it does not is
# not measured and no explanation should be read into this comment. What reproduces, 2026-08-23:
#
#   * a 102-character docstring line: `lake env lean` prints nothing and exits 0; with
#     `-Dweak.linter.mathlibStandardSet=true` it reports `This line exceeds the 100 character
#     limit`;
#   * `theorem t (x : Foo) : True := trivial` for an undefined `Foo`: `lake env lean` exits 0 and
#     warns only about `x`; with `-DautoImplicit=false` it is `Unknown identifier 'Foo'`;
#   * `#check fun x : Nat => x`: `lake env lean` prints `fun x => x`, and with
#     `-Dpp.unicode.fun=true` it prints `fun x ↦ x`. This third one is not about linting at all,
#     which is why it is here — it says the *block* is not in effect rather than that some linter
#     is off.
#
# So "`lake env lean` was silent" is not evidence that a linter passed — it is evidence that no
# linter ran. This script reads the options out of `lakefile.toml` at run time rather than
# hardcoding them, because a stale copy of that list would reintroduce exactly the drift it
# exists to remove.
#
# ---------------------------------------------------------------------------------------------
# THIS IS NOT `validation.sh`, AND A GREEN RUN HERE IS NOT EVIDENCE THAT ANYTHING COMPILES.
#
# It does not run:
#
#   * `lake exe mk_all --lib Oka --check` — a new file missing from `Oka.lean`;
#   * `lake lint` (`runLinter`) — the *environment* linters: `docBlame`, `simpNF`,
#     `defsWithUnderscore` and about ten more, which check the whole environment and not one file;
#   * `lake exe lint-style` — the text linters (trailing whitespace, disallowed unicode, module
#     name casing);
#   * `scripts/check_docstring_names.py` — the backticked-name checker, which is where several of
#     this project's late failures have actually come from;
#   * the `sorry` grep, and anything at all about files that do not import the one being checked.
#
# A claim of the form "this compiles", in an issue, a review comment or a handover message, means
# `bash .orchestra/validation.sh`. This is for the edit loop.
#
# One further caveat, measured: the linter options carry TOML's `weak.` prefix, which means an
# option Lean does not know about is **ignored rather than rejected**. The style linters are
# registered by `Mathlib.Tactic.Linter`, so a file whose imports do not reach it gets no style
# linting from this script and no warning that it did not. Every file under `Oka/`
# imports far more than that, so this matters only for scratch files.
# ---------------------------------------------------------------------------------------------

set -uo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/.." || exit 1

# Print the whole leading comment block, which is where the "what this is NOT" list lives.
#
# **The range must not stop at the first separator.** It did, and `--help` then printed the three
# probes and none of the disclaimer — while `README.md` said "Its own `--help` lists this too".
# `self_test` now asserts that the disclaimer is in the output, so the two cannot drift again.
usage() {
  awk 'NR > 1 { if ($0 !~ /^#/) exit; sub(/^# ?/, ""); print }' "${BASH_SOURCE[0]}"
}

# Read `[leanOptions]` out of `lakefile.toml` as `-Dkey=value` arguments. Comments are stripped,
# so a `#` inside a quoted option value would be mangled; there are none, and if one is ever
# added this parser is where to fix it.
read_lean_options() {
  awk '
    /^[[:space:]]*\[/ {
      insec = ($0 ~ /^[[:space:]]*\[leanOptions\][[:space:]]*$/)
      next
    }
    !insec { next }
    {
      sub(/#.*/, "")
      eq = index($0, "=")
      if (eq == 0) next
      key = substr($0, 1, eq - 1)
      val = substr($0, eq + 1)
      gsub(/^[[:space:]]+|[[:space:]]+$/, "", key)
      gsub(/^[[:space:]]+|[[:space:]]+$/, "", val)
      gsub(/^"|"$/, "", val)
      if (key != "" && val != "") print "-D" key "=" val
    }
  ' lakefile.toml
}

# Warnings are made fatal the way `lake build --wfail` makes them fatal: by looking at the output.
#
# **`-DwarningAsError=true` is NOT what `--wfail` does, and using it here is wrong.** Measured:
# with that option a file wrapping `#print axioms` in `#guard_msgs` fails, because
# `linter.hashCommand`'s warning about `#print` becomes an *error*, `#guard_msgs` then captures it,
# and the docstring no longer matches the generated message — a file that the build passes.
# `--wfail` leaves warnings as warnings inside Lean and fails at the lake level on the build log,
# so `#guard_msgs` sees what it expects to see.
run_check() {
  local -a opts=()
  local line out rc
  while IFS= read -r line; do opts+=("$line"); done < <(read_lean_options)
  if [ "${#opts[@]}" -eq 0 ]; then
    echo "scripts/check_file.sh: no [leanOptions] found in lakefile.toml; refusing to run a" >&2
    echo "check weaker than the build. Fix the parser rather than deleting this guard." >&2
    return 1
  fi
  # One file per `lake env lean`: it takes exactly one, and passing two makes it print
  # `Expected exactly one file name` followed by its own usage dump. The loop is what makes the
  # `[more files…]` in the usage line true.
  local status=0
  for f in "$@"; do
    out="$(lake env lean "${opts[@]}" "$f" 2>&1)"
    rc=$?
    [ -n "$out" ] && printf '%s\n' "$out"
    if [ "$rc" -ne 0 ]; then
      status="$rc"
    elif printf '%s' "$out" | grep -qE '(^|[^[:alnum:]_])(warning|error):'; then
      status=1
    fi
  done
  return "$status"
}

# Three fixtures and a positive control. The control is the point: without it a green self-test
# would be consistent with the script passing no options at all, which is the failure mode it
# exists to rule out.
self_test() {
  local dir status=0
  dir="$(mktemp -d)" || return 1
  trap 'rm -rf "$dir"' RETURN

  printf 'import Mathlib.Tactic.Linter\n\n/-- A clean file. -/\ntheorem checkFileClean : True := trivial\n' \
    > "$dir/clean.lean"
  {
    printf 'import Mathlib.Tactic.Linter\n\n/-- '
    printf 'a%.0s' $(seq 1 101)
    printf ' -/\ntheorem checkFileLong : True := trivial\n'
  } > "$dir/long.lean"
  printf 'import Mathlib.Tactic.Linter\n\n/-- An accidental auto-bound implicit. -/\ntheorem checkFileAuto (x : ThisTypeDoesNotExist) : True := trivial\n' \
    > "$dir/auto.lean"
  # A regression fixture. Files of this shape (`#guard_msgs` around `#print axioms`) all
  # failed while this script made warnings fatal with `-DwarningAsError=true` instead of
  # by inspecting the output: `linter.hashCommand` warns about `#print`, the option promoted that
  # warning to an error, and `#guard_msgs` then reported a message mismatch.
  printf 'import Mathlib.Tactic.Linter\n\n/--\ninfo: '"'"'Nat.add'"'"' does not depend on any axioms\n-/\n#guard_msgs (whitespace := lax) in\n#print axioms Nat.add\n' \
    > "$dir/guard.lean"

  expect() {
    local want="$1" name="$2" ; shift 2
    "$@" > /dev/null 2>&1
    local got=$?
    if [ "$got" -eq "$want" ] || { [ "$want" -ne 0 ] && [ "$got" -ne 0 ]; }; then
      echo "ok       $name (exit $got)"
    else
      echo "FAILED   $name: expected exit $want, got $got"
      status=1
    fi
  }

  expect 0 "clean file passes"                   run_check "$dir/clean.lean"
  expect 1 "over-long line is rejected"          run_check "$dir/long.lean"
  expect 1 "auto-bound implicit is rejected"     run_check "$dir/auto.lean"
  expect 0 "#guard_msgs around #print axioms passes" run_check "$dir/guard.lean"
  # The control: both bad fixtures are accepted by the command this script replaces.
  expect 0 "control: bare lake env lean accepts the over-long line" \
    lake env lean "$dir/long.lean"
  expect 0 "control: bare lake env lean accepts the auto-bound implicit" \
    lake env lean "$dir/auto.lean"
  # `--help` must carry the disclaimer, because `README.md` says it does. This is a regression
  # guard: the first version of `usage` stopped at the separator above the disclaimer and printed
  # none of it.
  local help
  help="$(usage)"
  for needle in "validation.sh" "mk_all" "lint-style" "check_docstring_names.py" "sorry"; do
    if printf '%s' "$help" | grep -qF -- "$needle"; then
      echo "ok       --help mentions $needle"
    else
      echo "FAILED   --help does not mention $needle"
      status=1
    fi
  done
  expect 0 "two files at once are both checked" run_check "$dir/clean.lean" "$dir/guard.lean"
  expect 1 "two files at once fail if either fails" run_check "$dir/clean.lean" "$dir/long.lean"

  if [ "$status" -eq 0 ]; then echo "self-test passed."; else echo "self-test FAILED."; fi
  return "$status"
}

case "${1-}" in
  ""|-h|--help) usage; exit 0 ;;
  --self-test)  self_test; exit $? ;;
  *)            run_check "$@"; exit $? ;;
esac
