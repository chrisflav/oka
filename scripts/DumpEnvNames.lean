/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka

/-!
# Environment name dump, for `scripts/check_docstring_names.py`

Writes every non-internal constant name and every imported module name in the environment of
`Oka`, one per line, to the file named by the environment variable
`OKA_ENV_NAME_DUMP` (default `env-names.txt` in the working directory).

This file is deliberately **not** part of the library: it is run with `lake env lean`, so it
is compiled fresh each time against the oleans the build has already produced, and it is not
reachable from `Oka.lean`. Adding it to a library would make every build
elaborate a file whose only purpose is to write a temporary file.

Module names are dumped alongside constants because docstrings on this project cite modules —
`Oka.Weierstrass`, `Mathlib.RingTheory.Filtration` — in exactly the same backticked form as
declarations, and a checker that knew only about constants would report all of them.

## The format, and why the two kinds are told apart

Each line is `<kind>` TAB `<name>`, with `kind` either `module` or `decl`. **A name never
contains a tab**, so the split is unambiguous.

The tag exists because the checker's field-notation rule — which accepts `head.tail` when `head`
resolves and is not a namespace, reading it as generalised field notation on the *term* `head` —
is only ever right when `head` is a **declaration**. A module is not a term and has no fields, so
`` `Mathlib.RingTheory.Filtration.someDecl` `` is not field notation on anything; without the tag
it was accepted anyway, because modules and constants arrived here in one undifferentiated list and
the rule could not see which it had. That made every module that is not also a namespace a head
under which any tail whatsoever passed unchecked. See taxis #1326 for the control that measured it.

**An untagged line is read as a declaration**, so a dump written by a checkout that predates the
tag still parses; the checker says on stderr that it cannot tell modules from declarations in
that case rather than silently reverting to the old behaviour.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let path := (← IO.getEnv "OKA_ENV_NAME_DUMP").getD "env-names.txt"
  let h ← IO.FS.Handle.mk path IO.FS.Mode.write
  for m in env.header.moduleNames do
    h.putStrLn s!"module\t{m}"
  for (n, _) in env.constants.toList do
    unless n.isInternal do
      h.putStrLn s!"decl\t{n}"
