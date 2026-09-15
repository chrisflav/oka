/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka

/-!
# Tripwire: `simp` lemmas over a bundled category do not fire at a concrete object

Several `@[simp]` lemmas in this library never fire, and the reason is not a defect in them.
It is an upstream discrimination-tree mismatch, reproducible in three lines with nothing from
this project in sight:

```lean
theorem myLemma {R : CommRingCat} (x : R) : x + 0 = x := add_zero x

example {R : CommRingCat} (x : R) : x + 0 = x := by simp only [myLemma]        -- succeeds
example (x : (CommRingCat.of ℤ : CommRingCat)) : x + 0 = x := by
  simp only [myLemma]                                                          -- FAILS
```

## The mechanism, measured rather than guessed

`#discr_tree_simp_key myLemma` prints `@HAdd.hAdd _.1 _.1 _.1 _ _ 0`: because `R` is a
variable, the carrier `↑R` is stored as the *projection* key `CommRingCat.0` applied to a
star. Computing the lookup keys of the two goals gives

```
variable object : HAdd.hAdd CommRingCat.0 ‹R› CommRingCat.0 ‹R› CommRingCat.0 ‹R› * ‹inst› 0
concrete object : HAdd.hAdd Int Int Int * ‹inst› 0
```

At a concrete `CommRingCat.of ℤ` the carrier is **reduced to `Int`** before the keys are
taken, so the position that the stored lemma indexes under `CommRingCat.0` is indexed under
`Int` in the goal. The keys differ in their very first argument — and in length — so the
lemma is not retrieved from the tree at all. That matches what `simp`'s own tracing shows:
with `set_option trace.Meta.Tactic.simp.unify true` the lemma is never so much as attempted.

`rw` is unaffected because its `kabstract` matches on head index plus `isDefEq`, which is
strictly more permissive than a discrimination-tree lookup.

Consequences, all of them checked:

* it has nothing to do with `TopCat`, presheaves, germs or this project — `CommRingCat` and
  `+` reproduce it;
* restating the lemma at the concrete object does **not** help: `simp` stores the restated
  lemma's keys with the carrier still unreduced, so it misses the goal for the same reason;
* passing *any* argument that pins the object explicitly does help, because a `simp` argument
  given as a term is indexed from the instantiated expression, exactly as the goal is.

So the workaround in this library is `rw`, or `simp [lem (ι := ι)]`. See taxis issue #583.

## What this file is for

The `fail_if_success (simp only [...]; done)` lines below are **tripwires, not tests of our
code**. Each asserts that the matching failure is still present. If one of them starts
failing, the upstream behaviour has changed for the better, and the right response is to
delete that line and then re-check the `@[simp]` attributes and the explanatory comments in
`Oka/StalkEquiv.lean` — in particular `okaStalkEquiv_germ_algebraMap`, which is deliberately
not `@[simp]` because it would be shadowed by `okaStalkEquiv_germ` *once the latter fires*.

The `done` is not decoration. `simp only` with an inert argument does not always fail: it
still beta-reduces and normalises projections, and that counts as progress, so it reports
`unsolved goals` rather than an error. `simp only [lem]; done` fails in both cases, which is
the property a tripwire needs.

The lines after each tripwire are ordinary regression tests: they pin the workarounds that
the library actually relies on.

`set_option linter.unusedSimpArgs false` is needed because the linter — correctly — reports
the inert argument inside the tripwire, and the project builds with `--wfail`.
-/

set_option linter.unusedSimpArgs false

open CategoryTheory TopologicalSpace Opposite

section MinimalReproduction

private theorem addZeroLemma {R : CommRingCat} (x : R) : x + 0 = x := add_zero x

/-- Over a *variable* object of a bundled category the lemma fires, as one would expect. -/
example {R : CommRingCat} (x : R) : x + 0 = x := by simp only [addZeroLemma]

/-- Over a *concrete* object it does not, and pinning the object restores it. -/
example (x : (CommRingCat.of ℤ : CommRingCat)) : x + 0 = x := by
  fail_if_success (simp only [addZeroLemma]; done)
  simp only [addZeroLemma (R := CommRingCat.of ℤ)]

end MinimalReproduction

section StalkEquiv

variable {ι : Type} [Fintype ι]

/-- The shape the library actually meets: `okaStalkEquiv_germ` is `@[simp]` and inert, and
both `rw` and pinning the index type work.

**All three halves are exercised below**, which until 2026-08-27 only two of them were: the
`fail_if_success` is the inertness, the `have` is `rw`, and the closing `simp only` is the
pinning. The `rw` half was prose here and prose again in `Oka/StalkEquiv.lean`'s comment above
`okaStalkEquiv_germ_algebraMap`, which cites this file as the place holding the tripwires — so
one line makes a claim in two files build-enforced. -/
example {y : ι → ℂ} {U : Opens (ι → ℂ)} (hy : y ∈ U) (f : OkaRing U) :
    okaStalkEquiv y ((okaCommPresheaf ι).germ U y hy f) = OkaRing.germ hy f := by
  fail_if_success (simp only [okaStalkEquiv_germ]; done)
  have _rw : okaStalkEquiv y ((okaCommPresheaf ι).germ U y hy f) = OkaRing.germ hy f := by
    rw [okaStalkEquiv_germ]
  simp only [okaStalkEquiv_germ (ι := ι)]

/-- Mathlib's own germ lemmas are affected in the same way, which is what rules out any
explanation local to this project. -/
example {F : (TopCat.of ℂ : TopCat).Presheaf CommRingCat} {y : (TopCat.of ℂ : TopCat)}
    {U V : Opens (TopCat.of ℂ : TopCat)} (h : U ≤ V) (hy : y ∈ U) (f : F.obj (op V)) :
    F.germ U y hy (F.map (homOfLE h).op f) = F.germ V y (h hy) f := by
  fail_if_success (simp only [TopCat.Presheaf.germ_res_apply]; done)
  simp only [TopCat.Presheaf.germ_res_apply (F := F)]

end StalkEquiv
