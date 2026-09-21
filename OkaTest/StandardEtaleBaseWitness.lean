/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka

/-!
# The square-root cover of an arbitrary presented base

`ComplexAnalytic.isLocalIso_analytificationMap_etalePresHom`
(`Oka/Analytification/StandardEtaleLocalIsoBase.lean`) says that the analytification of a standard
étale morphism over a **presented** base is a local isomorphism onto that base, at every `k`.
`OkaTest/StandardEtaleLocalIsoBase.lean` already instantiates it at `k = 1`, twice, over the node
`ComplexAnalytic.nodeG`. **What is here is a family and not a further instance**: one
`StandardEtalePair` and one theorem firing the library statement at **every** `n`, `k`, `g` and
`a` at once, with a `k = 1` instance as a corollary rather than as the deliverable.

That distinction is the whole reason this file is separate from the one above.
`OkaTest/StandardEtaleLocalIsoBase.lean`'s own `## What is not checked here` states the gap in
terms — *"Both witnesses are at one presentation with one relation. The theorem is general in `k`
and this file is evidence that it is instantiable, not that it is instantiable uniformly."*
`ComplexAnalytic.isLocalIso_analytificationMap_etalePresHom_sqrtCover` is the uniform statement,
and it is still an instantiation and not a construction: no analysis, no implicit function theorem
of either kind, and no new declaration under `Oka/`.

## The pair, and how it stands to the two already in the tree

`ComplexAnalytic.sqrtCoverPair a` is `f = X² − C a`, `g = X`, over any `ℂ`-algebra and any `a` in
it. There are now three `StandardEtalePair`s that the local-isomorphism theorem has been fired at,
and they are three different things:

* `ComplexAnalytic.sqSubOnePair` (`OkaTest/OpenBaseFiniteness.lean`), `f = X² − 1`, `g = X − 1`.
  **Degenerate**: `ComplexAnalytic.sqSubOnePair_X` pins the class of `X` to `−1` and
  `ComplexAnalytic.sqSubOneRingEquiv` identifies its standard étale algebra with the base
  **wherever `2` is a unit of the base**, which is free at the `ℂ`-algebra that witness is fired
  over, so `ComplexAnalytic.isLocalIso_analytificationMap_etalePresHom_node_sqSubOne` fires the
  theorem at an isomorphism — deliberately, since that is the route
  `Oka/Analytification/StandardEtaleLocalIsoBase.lean` named as cheapest. **That clause carried no
  hypothesis until 2026-09-21.**
* `ComplexAnalytic.sqSubOneTwoPair` (`OkaTest/StandardEtaleLocalIsoBase.lean`), `f = X² − 1`,
  `g = 2`. Not degenerate, and over a commutative ring rather than a `ℂ`-algebra — which is what
  the `g` buys: `g = 2` puts the `2` on the right of `cond`, where the `g = X` below needs it
  inverted on the left and so needs a `ℂ`-algebra. Its `f` is `ComplexAnalytic.sqrtCoverPair 1`'s.
* `ComplexAnalytic.sqrtCoverPair`, here. It is the only one of the three that **varies**, and that
  is what it is for: `ComplexAnalytic.condPair` (`OkaTest/StandardEtaleCond.lean`) is this pair at
  `n = 1`, `k = 0` and `a` the class of `z₀`, and `ComplexAnalytic.sqrtCoverPair 1` has the same
  `f` as the two above. A family is what a statement quantified over `a` needs, and neither fixed
  pair supplies one.

`ComplexAnalytic.exists_ne_hasMap_sqrtCoverPair_four` is the control against the first bullet's
degeneracy: two distinct points of one fibre, so nothing forces the class of `X` and the algebra is
not the base. **That control is over `ℂ` at `a = 4` and is not a statement about the cover of any
particular base** — see *What is not here*.

## The two lifts are the two computations `ComplexAnalytic.condF_eq` already runs

`ComplexAnalytic.isLocalIso_analytificationMap_etalePresHom` takes a `StandardEtalePair` over
`ComplexAnalytic.PresentedAlgebra n k g` together with two polynomials of `ℂ^(n+1)` lifting its
`f` and `g` through `ComplexAnalytic.polyPresentedAlgebraEquiv`. Take the lifts to be
`ComplexAnalytic.sqrtCoverF a = z_n² − a` and `ComplexAnalytic.sqrtCoverG n = z_n`; then the two
hypotheses are `ComplexAnalytic.polyPresentedAlgebraEquiv_mk_X_var` and
`ComplexAnalytic.polyPresentedAlgebraEquiv_mk_rename` and nothing else — the same two lemmas
`ComplexAnalytic.condF_eq` uses at `k = 0`, with the `change` that file needs replaced by the
`rw` an `abbrev` written in those two spellings admits.

## The `k = 1` instance, and the two spaces it exhibits

`ComplexAnalytic.hyperbolaBase` is `z₀z₁ − 1` in `ℂ²`, so `k = 1`, and the `a` inverted over it is
`z₀`, a unit on that base: the cover is the square root of a nowhere-vanishing function.

**Both spaces are exhibited non-empty, and only one of the two exhibitions rules anything out.**
`ComplexAnalytic.AnalyticSpace.IsLocalIso` has two fields and **both quantify over the source**,
so a morphism out of an empty space is a local isomorphism whatever its base is, and **a point of
the base rules out no vacuity at all**. `Oka/Analytification/StandardEtaleLocalIso.lean` states
that of both fields together — *"both fields of `ComplexAnalytic.AnalyticSpace.IsLocalIso`
quantify over the points of the source, so an empty analytification satisfies them vacuously"* —
while `Oka/AnalyticSpace/LocalIso.lean`'s own docstring says it of the stalk field only,
`IsLocalHomeomorph` being where the other one hides its quantifier. The point that does rule the
vacuity out is `ComplexAnalytic.hyperbolaEtalePt`, the tuple `(1, 1, 1, 1)` of `ℂ⁴`, whose three
relations are `1 · 1 − 1`, `1 · 1 − 1` and `1 − 1`.
`ComplexAnalytic.hyperbolaPoint` is a point of the base and is here for a different and weaker
reason: with `ComplexAnalytic.eval_hyperbolaBase_zero_ne_zero` it says the base is a **proper
non-empty** subset of `ℂ²`, which is what separates `k = 1` here from a `k = 1` written with the
relation `0`, whose analytification is `ℂ^n` and at which an instance would exhibit the index
rather than the content.

**The general theorem admits vacuous instances and nothing here removes them.** At `a = 0` its
relations are `z_n² = 0` and `w · z_n = 1`, which force `z_n = 0` and then `0 = 1`: the source is
empty and the conclusion holds for the reason above. **That is a theorem and not only this
paragraph** — `ComplexAnalytic.not_nonempty_analytification_etalePresentation_sqrtCover_zero`,
below and at every base, so the argument here can be checked rather than believed. It exhibits one
vacuous instance and removes none, which is what *admits* says. So
`ComplexAnalytic.nonempty_analytification_etalePresentation_hyperbola` is a statement about the
hyperbola at `a = z₀` and **not** about the family — the family is genuinely quantified over an `a`
at which it says nothing, and that is a fact about the library theorem it instantiates rather than
a defect of either.

## Both statements at one base, and the sentence that had to become false

An earlier form of this file said, under *What is not here*, that **nothing here bears on the
*projection* statement** — `ComplexAnalytic.not_isLocalIso_analytificationMap_etalePresHom_comp`
(`Oka/Analytification/StandardEtaleNotLocalIso.lean`), which is this same standard étale morphism
followed by the inclusion of the base into `ℂ^n`. That sentence stood two paragraphs above the
discharge of both of that statement's hypotheses at this file's own base, so the instance was one
term away and the file bore on the statement whatever the sentence said. **The way to make it true
was to make it false**, and `ComplexAnalytic.not_isLocalIso_hyperbolaSqrtCover_comp` is that
instance.

At the hyperbola, and at the **same** standard étale data, both of these hold:

* `ComplexAnalytic.isLocalIso_hyperbolaSqrtCover` — the analytification of the standard étale
  morphism **onto the base's own analytification** is a local isomorphism;
* `ComplexAnalytic.not_isLocalIso_hyperbolaSqrtCover_comp` — the **same morphism followed by the
  inclusion of the hyperbola into `ℂ²`** is not.

That is the contrast `Oka/Analytification/StandardEtaleLocalIsoBase.lean` draws in prose and
`OkaTest/StandardEtaleNotLocalIso.lean` compiles at the node, drawn here at a second base.

**Only one of the two hypotheses needed anything new.**
`ComplexAnalytic.nonempty_analytification_etalePresentation_hyperbola` above *is* the second, at
the same three arguments rather than at a restatement of them. The first is
`ComplexAnalytic.hyperbolaBase_ne_zero`, the contrapositive of
`ComplexAnalytic.eval_hyperbolaBase_zero_ne_zero`: a polynomial with a non-zero evaluation is not
the zero polynomial. **That step is the only thing in this section the repository did not already
have**, and it is one `rw`, which is what makes the section an instantiation and not an argument.

**What a second base buys, and it is less than it looks.** Vacuity is settled by one satisfied
instance and `OkaTest/StandardEtaleNotLocalIso.lean` supplied it at the node; a second instance
adds nothing there. What it does add is that neither hypothesis is discharged the same way twice:
`ComplexAnalytic.nodeG_ne_zero` is `mul_ne_zero` at a relation written as a product, and
`ComplexAnalytic.hyperbolaBase_ne_zero` is an evaluation at a relation written as a difference, so
the properness hypothesis is met at two unrelated bases by two routes rather than by one idiom
twice. **No claim beyond that is made here.** Nothing anywhere in this file says either curve is
smooth, singular, irreducible or connected, and
`ComplexAnalytic.not_isLocalIso_analytificationMap_etalePresHom_comp` asks none of it — it is
general in `g` already, and neither instance narrows it.

## Main definitions

- `ComplexAnalytic.sqrtCoverPair`: **the pair `f = X² − C a`, `g = X`** over an arbitrary
  `ℂ`-algebra.
- `ComplexAnalytic.sqrtCoverF` and `ComplexAnalytic.sqrtCoverG`: the two lifts, `z_n² − a` and
  `z_n`.
- `ComplexAnalytic.hyperbolaBase`: the hyperbola `z₀z₁ = 1` in `ℂ²`, a presentation with `k = 1`.
- `ComplexAnalytic.hyperbolaPoint`: the point `(1, 1)` of its analytification.
- `ComplexAnalytic.hyperbolaEtalePt`: the tuple `(1, 1, 1, 1)`, a point of the source of the
  `k = 1` witness.

## Main results

- `ComplexAnalytic.sqrtCoverF_eq` and `ComplexAnalytic.sqrtCoverG_eq`: the two lifts are lifts.
- `ComplexAnalytic.isLocalIso_analytificationMap_etalePresHom_sqrtCover`: **the square-root cover
  of a presented base analytifies to a local isomorphism onto that base**, for every base and
  every `a`.
- `ComplexAnalytic.isLocalIso_hyperbolaSqrtCover`: **the same at `k = 1`**, over the hyperbola.
- `ComplexAnalytic.eval_etalePresentation_hyperbolaEtalePt` and
  `ComplexAnalytic.nonempty_analytification_etalePresentation_hyperbola`: **the source of that
  witness is not empty**, so it is not a statement about a morphism out of an empty space.
- `ComplexAnalytic.not_nonempty_analytification_etalePresentation_sqrtCover_zero`: **the family's
  source is empty at `a = 0`**, at every base — one vacuous instance exhibited, and none removed.
- `ComplexAnalytic.hyperbolaBase_ne_zero` and
  `ComplexAnalytic.not_isLocalIso_hyperbolaSqrtCover_comp`: **the same morphism followed by the
  inclusion of the hyperbola into `ℂ²` is *not* a local isomorphism**, so at this base the two
  statements come apart.
- `ComplexAnalytic.hasMap_two_sqrtCoverPair_four`,
  `ComplexAnalytic.hasMap_neg_two_sqrtCoverPair_four` and
  `ComplexAnalytic.exists_ne_hasMap_sqrtCoverPair_four`: **two distinct points of one fibre**, so
  `ComplexAnalytic.sqrtCoverPair` is not the degenerate pair.
- `ComplexAnalytic.eval_hyperbolaBase_zero_ne_zero`: the origin is off the hyperbola, so the base
  is a proper subset of `ℂ²`.

## What is not here

* **No claim that the family is non-vacuous.** The paragraph above gives `a = 0` as an instance
  whose source is empty. What is proved is that the *hyperbola* instance is not one; nothing below
  says which `a` are the good ones, and nothing below needs to, since the library theorem's
  conclusion holds either way.
* **No `ComplexAnalytic.AnalyticSpace.IsFiniteEtale` at `k ≥ 1`.** Unrestricted finiteness there
  is false — `Oka/Analytification/MonicHypersurface.lean` carries the counterexample — and this
  file witnesses the local-isomorphism field alone, which is the field
  `Oka/Analytification/StandardEtaleLocalIsoBase.lean` supplies.
* **Nothing is proved about the étale algebra over `ComplexAnalytic.hyperbolaBase` itself.** The
  two-point fibre above is over `ℂ` at `a = 4`, which is enough to refute *"the class of `X` is
  forced"* for `ComplexAnalytic.sqrtCoverPair` as a family, and it is **not** a statement that the
  cover of the hyperbola is connected, non-trivial, or anything else. A reader who wants that
  wants a statement nobody here has made.
* **No non-degenerate instantiation of `ComplexAnalytic.sqSubOnePair`.** The degeneracy recorded
  above is that file's own two theorems read together, not a new one.
* **No claim that this is the smallest `k ≥ 1` witness.** `OkaTest/StandardEtaleLocalIsoBase.lean`
  is smaller in the only sense that matters — its two pairs are constants where this one is a
  family.
* **Nothing about *which* bases the projection statement fails at**, beyond the two that now
  instantiate it — `OkaTest/StandardEtaleNotLocalIso.lean`'s node and the hyperbola here. It is
  also not instantiated at the second node lift `ComplexAnalytic.nodeEtaleGSubOne`, whose
  ingredients are all in the tree; that is a decision and the bullet recording it is in
  `OkaTest/StandardEtaleNotLocalIso.lean`, where the node's instance lives.
* **No statement about which `a` make
  `ComplexAnalytic.isLocalIso_analytificationMap_etalePresHom_sqrtCover` vacuous.**
  `ComplexAnalytic.not_nonempty_analytification_etalePresentation_sqrtCover_zero` says `a = 0` is
  one of them, at every base; **that is one `a` and not a characterisation**, and in the other
  direction nothing here goes beyond the hyperbola's own `a = z₀`, where
  `ComplexAnalytic.nonempty_analytification_etalePresentation_hyperbola` exhibits a point. A point
  of the source **is** a point of the base together with an invertible square root of `a` there —
  that is what the two relations `z_n² = a` and `w · z_n = 1` say at a point, and the second of
  them is what the proof below contradicts — so the question is about `a` **and the base
  together**, and no condition on `a` alone settles it. In particular it is **not** *"the class of
  `a` is a unit in the presented algebra"*: that condition says nothing about the base having a
  point at all, and where the presented algebra is the zero ring it holds of every `a`, `a = 0`
  included, at which the theorem below still empties the source. **No declaration approaches the
  question in either direction.** What this bullet used to say — that the emptiness at `a = 0` was
  *a theorem nowhere* — was true when it was written and is what the theorem below retires.

  **A draft of this file said the node was chosen in `OkaTest/StandardEtaleLocalIsoBase.lean`
  rather than the hyperbola because the node is inside the projection statement's hypotheses and
  this file's base is not. That is false, and the section above is what refutes it.** Those
  hypotheses are `∃ j, g j ≠ 0` and a non-empty source, and both hold at the hyperbola —
  `ComplexAnalytic.hyperbolaBase_ne_zero` and
  `ComplexAnalytic.nonempty_analytification_etalePresentation_hyperbola`, which are no longer two
  theorems a reader has to put together but the two arguments of one. What is true is that
  `OkaTest/StandardEtaleLocalIsoBase.lean` chose the node **deliberately** for that property while
  this file chose the hyperbola for a different one
  — `a = z₀` is a unit there, so the cover is the square root of a nowhere-vanishing function —
  and *deliberately* is not *uniquely*. **The clause was written while the projection statement
  was prose; lana-agents/oka#373 compiled it, and a claim about which bases satisfy its
  hypotheses became something a reader can check.**

## A name that is taken, and is a different object

`OkaTest/HypersurfaceFinite.lean` already owns `ComplexAnalytic.sqrtG`: a **monic polynomial**
`X² − x₀` over `ℂ[x₀, x₁]`, the second square root in that file's `{x₁² = x₀} ∩ {x₂² = x₀}`. It is
not this file's `g`, and the `sqrtCover` prefix here is what keeps the two apart — Lean refuses
the collision outright, so this is a naming note and not a defect either file had.

## Relation to `ComplexAnalytic.condPair`

`ComplexAnalytic.condPair` (`OkaTest/StandardEtaleCond.lean`) is `ComplexAnalytic.sqrtCoverPair` at
`n = 1`, `k = 0` and `a` the class of `z₀`, so this file's pair subsumes it. **That file is not
refactored onto it here.** Its subject is `StandardEtalePair.cond` *at a point* and its two
points, its module docstring argues its data at length, and rewriting it would put a second and
unrelated narrative into this change. The duplication is one `def` with four fields and it is
named here rather than hidden.
-/

open CategoryTheory MvPolynomial Polynomial

universe u

namespace ComplexAnalytic

noncomputable section

/-! ### The square-root pair over an arbitrary `ℂ`-algebra -/

/-- **The pair `f = X² − C a`, `g = X`**, over any `ℂ`-algebra.

`monic_f` is `Polynomial.monic_X_pow_sub_C`. `cond` is
`derivative f * C (2⁻¹) + f * 0 = g ^ 1`, which is `C 2 * X * C 2⁻¹ = X`; the inverse of `2` is
`algebraMap ℂ R 2⁻¹`, and that is the one step where `R` is used as a `ℂ`-algebra rather than as a
commutative ring. `IsUnit (2 : R)` would do instead and is not the hypothesis the consumer has:
every `ComplexAnalytic.PresentedAlgebra` is a `ℂ`-algebra by construction. -/
def sqrtCoverPair {R : Type*} [CommRing R] [Algebra ℂ R] (a : R) : StandardEtalePair R where
  f := Polynomial.X ^ 2 - Polynomial.C a
  monic_f := Polynomial.monic_X_pow_sub_C _ two_ne_zero
  g := Polynomial.X
  cond := by
    refine ⟨Polynomial.C (algebraMap ℂ R (2⁻¹ : ℂ)), 0, 1, ?_⟩
    have h2 : (2 : R) * algebraMap ℂ R (2⁻¹ : ℂ) = 1 := by
      rw [show (2 : R) = algebraMap ℂ R (2 : ℂ) from (map_ofNat _ 2).symm, ← map_mul]
      norm_num
    simp only [derivative_sub, derivative_X_pow, derivative_C, sub_zero, mul_zero, add_zero,
      Nat.cast_ofNat, pow_one]
    rw [mul_right_comm, ← Polynomial.C_mul, h2, map_one, one_mul]
    norm_num

/-- The `f` of `ComplexAnalytic.sqrtCoverPair`, by `rfl`.

This and the next exist so that **nothing below has to `rw` or `simp` at
`ComplexAnalytic.sqrtCoverPair` itself**: unfolding a definition that way plants an auto-generated
equation lemma under its own name, which `OkaTest/StandardEtaleCond.lean`'s module docstring
records happening once and says how it was found. -/
@[simp]
theorem sqrtCoverPair_f {R : Type*} [CommRing R] [Algebra ℂ R] (a : R) :
    (sqrtCoverPair a).f = Polynomial.X ^ 2 - Polynomial.C a := rfl

/-- The `g` of `ComplexAnalytic.sqrtCoverPair`, by `rfl`. -/
@[simp]
theorem sqrtCoverPair_g {R : Type*} [CommRing R] [Algebra ℂ R] (a : R) :
    (sqrtCoverPair a).g = Polynomial.X := rfl

/-! ### The control: the class of `X` is not forced -/

/-- **`2` is a point of the fibre of `ComplexAnalytic.sqrtCoverPair (4 : ℂ)`.**

`StandardEtalePair.HasMap x` is `aeval x f = 0` together with `IsUnit (aeval x g)`, and here that
is `2² − 4 = 0` and `IsUnit (2 : ℂ)`. -/
theorem hasMap_two_sqrtCoverPair_four : (sqrtCoverPair (4 : ℂ)).HasMap (2 : ℂ) := by
  refine ⟨?_, ?_⟩
  · rw [sqrtCoverPair_f]; norm_num
  · rw [sqrtCoverPair_g, Polynomial.aeval_X]; exact isUnit_iff_ne_zero.2 (by norm_num)

/-- **And so is `−2`**, which is the point of stating either.

`ComplexAnalytic.sqSubOnePair_X` pins the class of `X` in that pair's standard étale algebra to
`−1` — both relations are used, and where `2` is a unit of the base the algebra collapses onto it,
which is `ComplexAnalytic.sqSubOneRingEquiv`'s hypothesis and not this lemma's. Here two distinct
elements of the same `ℂ` satisfy `StandardEtalePair.HasMap`, so no relation pins the class of `X`
down and the same collapse cannot happen. **That is a statement about
`ComplexAnalytic.sqrtCoverPair` at one `ℂ`-algebra and one `a`**, which is all that is needed to
separate it from the degenerate pair, and it is not a statement about the cover of any particular
base.

**That clause read *the algebra collapses onto the base* with no hypothesis until 2026-09-21.** -/
theorem hasMap_neg_two_sqrtCoverPair_four : (sqrtCoverPair (4 : ℂ)).HasMap (-2 : ℂ) := by
  refine ⟨?_, ?_⟩
  · rw [sqrtCoverPair_f]; norm_num
  · rw [sqrtCoverPair_g, Polynomial.aeval_X]; exact isUnit_iff_ne_zero.2 (by norm_num)

/-- **The fibre of `ComplexAnalytic.sqrtCoverPair (4 : ℂ)` has at least two points**, which is
the two theorems above with the distinctness they are stated for.

`ComplexAnalytic.sqSubOnePair` admits no such pair over any base: its `X` is `−1` there and
nothing else. -/
theorem exists_ne_hasMap_sqrtCoverPair_four :
    ∃ x y : ℂ, x ≠ y ∧ (sqrtCoverPair (4 : ℂ)).HasMap x ∧ (sqrtCoverPair (4 : ℂ)).HasMap y :=
  ⟨2, -2, by norm_num, hasMap_two_sqrtCoverPair_four, hasMap_neg_two_sqrtCoverPair_four⟩

/-! ### The two polynomial lifts -/

/-- **The polynomial being inverted**: the new variable `z_n`, which is
`ComplexAnalytic.localisationVar n`.

Spelled at that name and not as `MvPolynomial.X (ULift.up (Fin.last n))` so that
`ComplexAnalytic.polyPresentedAlgebraEquiv_mk_X_var` applies with no rewriting. -/
abbrev sqrtCoverG (n : ℕ) : MvPolynomial (ULift.{u} (Fin (n + 1))) ℂ :=
  MvPolynomial.X (localisationVar.{u} n)

/-- **The polynomial cutting out the hypersurface**: `z_n² − a`, the square root of `a`.

`a` is read one variable up along `ComplexAnalytic.localisationIncl`, which is the spelling
`ComplexAnalytic.polyPresentedAlgebraEquiv_mk_rename` is stated at. -/
abbrev sqrtCoverF {n : ℕ} (a : MvPolynomial (ULift.{u} (Fin n)) ℂ) :
    MvPolynomial (ULift.{u} (Fin (n + 1))) ℂ :=
  MvPolynomial.X (localisationVar.{u} n) ^ 2 - MvPolynomial.rename (localisationIncl.{u} n) a

/-- **`ComplexAnalytic.sqrtCoverF a` is a lift of the `f` of `ComplexAnalytic.sqrtCoverPair`** at
the class of `a`.

Two applications of `ComplexAnalytic.polyPresentedAlgebraEquiv_mk_X_var` and
`ComplexAnalytic.polyPresentedAlgebraEquiv_mk_rename` under `map_sub` and `map_pow`, and nothing
else: `ComplexAnalytic.condF_eq` is the same computation at `k = 0` with two `have`s in front,
which are the observation that its two variables *are* those two spellings and which
`ComplexAnalytic.sqrtCoverF` writes out instead. -/
theorem sqrtCoverF_eq {n k : ℕ} (g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ)
    (a : MvPolynomial (ULift.{u} (Fin n)) ℂ) :
    polyPresentedAlgebraEquiv.{u} g (Ideal.Quotient.mk _ (sqrtCoverF.{u} a)) =
      (sqrtCoverPair (Ideal.Quotient.mk (presentationIdeal.{u} g) a)).f := by
  rw [sqrtCoverPair_f, map_sub, map_pow, map_sub, map_pow, polyPresentedAlgebraEquiv_mk_X_var,
    polyPresentedAlgebraEquiv_mk_rename]

/-- **`ComplexAnalytic.sqrtCoverG n` is a lift of the `g` of `ComplexAnalytic.sqrtCoverPair`**,
which is `ComplexAnalytic.polyPresentedAlgebraEquiv_mk_X_var` and nothing else. -/
theorem sqrtCoverG_eq {n k : ℕ} (g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ)
    (a : MvPolynomial (ULift.{u} (Fin n)) ℂ) :
    polyPresentedAlgebraEquiv.{u} g (Ideal.Quotient.mk _ (sqrtCoverG.{u} n)) =
      (sqrtCoverPair (Ideal.Quotient.mk (presentationIdeal.{u} g) a)).g := by
  rw [sqrtCoverPair_g]
  exact polyPresentedAlgebraEquiv_mk_X_var.{u} g

/-- **The square-root cover of a presented base analytifies to a local isomorphism onto that
base**, for every base and every `a`.

`ComplexAnalytic.isLocalIso_analytificationMap_etalePresHom` at
`ComplexAnalytic.sqrtCoverPair` and the two lifts above. **The whole content is that its three
hypotheses are jointly satisfiable at every `k`**, which is what its file's `## What is not here`
said nothing below produced. -/
theorem isLocalIso_analytificationMap_etalePresHom_sqrtCover {n k : ℕ}
    (g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ)
    (a : MvPolynomial (ULift.{u} (Fin n)) ℂ) :
    AnalyticSpace.IsLocalIso
      (analytificationMap.{u} (etalePresHom.{u} g (sqrtCoverF.{u} a) (sqrtCoverG.{u} n))) :=
  isLocalIso_analytificationMap_etalePresHom.{u} g _ _ _ (sqrtCoverF_eq.{u} g a)
    (sqrtCoverG_eq.{u} g a)

/-! ### An instance of that family whose source is empty -/

/-- **At `a = 0` the source of the square-root cover is empty**, at every base.

The two new relations of `ComplexAnalytic.etalePresentation` are then `z_n² = 0` and
`w · z_n = 1`: the first forces `z_n = 0` at any point, and the second becomes `−1 = 0`. **No
hypothesis on the base at all** — it holds at every `n`, `k` and `g`, which is the generality the
family theorem itself is stated at.

**What it does and does not say about
`ComplexAnalytic.isLocalIso_analytificationMap_etalePresHom_sqrtCover`.** That theorem's
conclusion is *true* here, and for the reason a reader has to know: both fields of
`ComplexAnalytic.AnalyticSpace.IsLocalIso` quantify over the source, so a morphism out of an empty
space satisfies them. **So this exhibits one vacuous instance of the family and removes none.**
Which `a` give a non-empty source is a different question: a point of the source is a point of the
base carrying an invertible square root of `a`, so it is a question about `a` **and the base
together** rather than about `a` alone, and nothing here approaches it. See *What is not here* for
one reading of it that is not the question — that the class of `a` is a unit — and why.

The two indices are `Fin.last (k + 1)` for `F` and `Fin.castSucc (Fin.last k)` for the
localisation relation, `ComplexAnalytic.etalePresentation` being `Fin.snoc` of
`ComplexAnalytic.localisationPresentation` — so reaching the second needs
`ComplexAnalytic.localisationPresentation_eq_snoc` and a **second** `Fin.snoc_last`, which is the
one step of this that is not immediate. -/
theorem not_nonempty_analytification_etalePresentation_sqrtCover_zero {n k : ℕ}
    (g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ) :
    ¬ Nonempty (AnalyticSpace.analytification.{u}
      (etalePresentation.{u} g (sqrtCoverF.{u} (0 : MvPolynomial (ULift.{u} (Fin n)) ℂ))
        (sqrtCoverG.{u} n))) := by
  rintro ⟨p, hp⟩
  have h := (mem_zeroLocus_polySection_iff.{u} _ _).1 hp
  have hF := h (Fin.last (k + 1))
  have hG := h (Fin.castSucc (Fin.last k))
  rw [etalePresentation, Fin.snoc_last] at hF
  rw [etalePresentation, Fin.snoc_castSucc, localisationPresentation_eq_snoc,
    Fin.snoc_last] at hG
  simp only [sqrtCoverF, rename_zero, sub_zero, map_pow, rename_X, MvPolynomial.eval_X, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, sqrtCoverG, map_sub, map_mul,
    map_one] at hF hG
  rw [hF, mul_zero, zero_sub, neg_eq_zero] at hG
  exact one_ne_zero hG

/-! ### A base with `k = 1` -/

/-- **The hyperbola `z₀z₁ = 1` in `ℂ²`**, as a presentation with one relation. -/
abbrev hyperbolaBase : Fin 1 → MvPolynomial (ULift.{u} (Fin 2)) ℂ :=
  ![MvPolynomial.X (ULift.up 0) * MvPolynomial.X (ULift.up 1) - 1]

/-- The point `(1, 1)` of `ℂ²`. -/
abbrev hyperbolaPt : ULift.{u} (Fin 2) → ℂ := fun _ ↦ 1

/-- **The relation vanishes at `(1, 1)`**, since `1 · 1 − 1 = 0`. -/
theorem eval_hyperbolaBase_hyperbolaPt (j : Fin 1) :
    MvPolynomial.eval hyperbolaPt.{u} (hyperbolaBase.{u} j) = 0 := by
  fin_cases j
  change MvPolynomial.eval hyperbolaPt.{u}
    (MvPolynomial.X (ULift.up 0) * MvPolynomial.X (ULift.up 1) - 1) = 0
  simp

/-- **The base's analytification is not empty.**
`ComplexAnalytic.mem_zeroLocus_polySection_iff` reduces membership to the evaluation above, and
`Fin 1` is one case.

**This is not what stops the theorem below being vacuous**, and an earlier draft of this file said
it was. Both fields of `ComplexAnalytic.AnalyticSpace.IsLocalIso` quantify over the *source*, so a
morphism out of an empty space onto a non-empty base satisfies them, which
`Oka/Analytification/StandardEtaleLocalIso.lean` states in terms; the point that rules the
vacuity out is `ComplexAnalytic.hyperbolaEtalePt` below. What this does is pair with
`ComplexAnalytic.eval_hyperbolaBase_zero_ne_zero` to make the base a **proper non-empty** subset of
`ℂ²`, which is a different and still necessary thing: at a `k = 1` presentation whose relation is
`0` the base is all of `ℂ^n` and an instance would exhibit the index rather than the content. -/
def hyperbolaPoint : AnalyticSpace.analytification.{u} hyperbolaBase.{u} :=
  ⟨⟨hyperbolaPt.{u}, trivial⟩,
    (mem_zeroLocus_polySection_iff.{u} _ _).2 eval_hyperbolaBase_hyperbolaPt.{u}⟩

/-- **And it is not all of `ℂ²`**: the relation is `−1` at the origin.

Together with `ComplexAnalytic.hyperbolaPoint` this is what makes `k = 1` here a base and not a
relation that says nothing — a presentation whose single relation is `0` has `k = 1` and the same
analytification as `k = 0`. -/
theorem eval_hyperbolaBase_zero_ne_zero :
    MvPolynomial.eval (fun _ ↦ (0 : ℂ)) (hyperbolaBase.{u} 0) ≠ 0 := by
  change MvPolynomial.eval (fun _ ↦ (0 : ℂ))
    (MvPolynomial.X (ULift.up 0) * MvPolynomial.X (ULift.up 1) - 1) ≠ 0
  simp

/-- **The witness: `k = 1`.** The square root of `z₀` over the hyperbola `z₀z₁ = 1` analytifies to
a local isomorphism onto the hyperbola's analytification.

One application of `ComplexAnalytic.isLocalIso_analytificationMap_etalePresHom_sqrtCover`, and by
itself it is a restatement of that theorem at chosen arguments. What makes it more than one is the
three theorems around it: `ComplexAnalytic.hyperbolaPoint` and
`ComplexAnalytic.eval_hyperbolaBase_zero_ne_zero` say the base is a proper non-empty subset of
`ℂ²`, and `ComplexAnalytic.nonempty_analytification_etalePresentation_hyperbola` says the source is
not empty, which is the one of the three that rules out a vacuity. -/
theorem isLocalIso_hyperbolaSqrtCover :
    AnalyticSpace.IsLocalIso (analytificationMap.{u} (etalePresHom.{u} hyperbolaBase.{u}
      (sqrtCoverF.{u} (MvPolynomial.X (ULift.up 0))) (sqrtCoverG.{u} 2))) :=
  isLocalIso_analytificationMap_etalePresHom_sqrtCover.{u} hyperbolaBase.{u} _

/-! ### The source of that witness is not empty -/

/-- The tuple `(1, 1, 1, 1)` of `ℂ⁴`: the point `(1, 1)` of the hyperbola, the square root `1` of
`z₀` there, and the inverse of `G = z₂`. -/
abbrev hyperbolaEtalePt : ULift.{u} (Fin 4) → ℂ := fun _ ↦ 1

/-- **The three relations vanish there**: `1 · 1 − 1`, `1 · 1 − 1` and `1 − 1`.

The three are the hyperbola's own relation, the localisation relation `w · G − 1` inverting
`G = z₂`, and `F = z₂² − z₀`; they arrive in that order because
`ComplexAnalytic.etalePresentation` is `Fin.snoc` of `ComplexAnalytic.localisationPresentation`. -/
theorem eval_etalePresentation_hyperbolaEtalePt (j : Fin 3) :
    MvPolynomial.eval hyperbolaEtalePt.{u}
      (etalePresentation.{u} hyperbolaBase.{u}
        (sqrtCoverF.{u} (MvPolynomial.X (ULift.up 0))) (sqrtCoverG.{u} 2) j) = 0 := by
  fin_cases j <;>
    simp [etalePresentation, localisationPresentation, polyPresentation, localisationIncl,
      localisationVar, Fin.snoc]

/-- **The source of `ComplexAnalytic.isLocalIso_hyperbolaSqrtCover` is not empty**, so that
witness is not a statement about a morphism out of an empty space.

**It is a statement about this instance and not about the family.**
`ComplexAnalytic.isLocalIso_analytificationMap_etalePresHom_sqrtCover` has instances whose source
*is* empty — at `a = 0` its two new relations are `z_n² = 0` and `w · z_n = 1`, which force
`z_n = 0` and then `0 = 1` — and nothing below or above rules those out. -/
theorem nonempty_analytification_etalePresentation_hyperbola :
    Nonempty (AnalyticSpace.analytification.{u}
      (etalePresentation.{u} hyperbolaBase.{u}
        (sqrtCoverF.{u} (MvPolynomial.X (ULift.up 0))) (sqrtCoverG.{u} 2))) :=
  ⟨⟨⟨hyperbolaEtalePt.{u}, trivial⟩,
    (mem_zeroLocus_polySection_iff.{u} _ _).2 eval_etalePresentation_hyperbolaEtalePt.{u}⟩⟩

/-! ### The projection to `ℂ²` over the hyperbola -/

/-- **The hyperbola's single relation is a non-zero polynomial**, which is
`ComplexAnalytic.not_isLocalIso_analytificationMap_etalePresHom_comp`'s properness hypothesis at
this base.

The contrapositive of `ComplexAnalytic.eval_hyperbolaBase_zero_ne_zero`: a polynomial with a
non-zero evaluation is not the zero polynomial, so rewriting by the assumed equation leaves
`map_zero`. **This is the only step of this section that was not already in the repository.**

`ComplexAnalytic.nodeG_ne_zero` (`OkaTest/StandardEtaleNotLocalIso.lean`) is the same hypothesis
at the node and takes the other route: the relation there is written as a product of two
variables, so `mul_ne_zero` closes it and no evaluation is needed. **Neither proof transfers as
written** — there is no product for `mul_ne_zero` to be applied to here, and the node's relation
is a product of variables, on which `MvPolynomial.eval (fun _ ↦ 0)` is `0` and refutes nothing. -/
theorem hyperbolaBase_ne_zero : ∃ j, hyperbolaBase.{u} j ≠ 0 :=
  ⟨0, fun h ↦ eval_hyperbolaBase_zero_ne_zero.{u} (by rw [h, map_zero])⟩

/-- **The square-root cover of the hyperbola, followed by the inclusion of the hyperbola into
`ℂ²`, is not a local isomorphism.**

`ComplexAnalytic.not_isLocalIso_analytificationMap_etalePresHom_comp` at
`ComplexAnalytic.hyperbolaBase` and the two lifts above, with its two hypotheses supplied by
`ComplexAnalytic.hyperbolaBase_ne_zero` and
`ComplexAnalytic.nonempty_analytification_etalePresentation_hyperbola`. An instantiation and not
an argument: nothing is re-proved here.

Read it against `ComplexAnalytic.isLocalIso_hyperbolaSqrtCover`, which is the same standard étale
data **without** the inclusion into `ℂ²`. The two together are what
`Oka/Analytification/StandardEtaleLocalIsoBase.lean` states in prose and
`OkaTest/StandardEtaleNotLocalIso.lean` compiles at the node, at a second base. -/
theorem not_isLocalIso_hyperbolaSqrtCover_comp :
    ¬ AnalyticSpace.IsLocalIso
      (analytificationMap.{u} (etalePresHom.{u} hyperbolaBase.{u}
          (sqrtCoverF.{u} (MvPolynomial.X (ULift.up 0))) (sqrtCoverG.{u} 2)) ≫
        analytificationInclHom.{u} hyperbolaBase.{u}) :=
  not_isLocalIso_analytificationMap_etalePresHom_comp.{u} _ _ _ hyperbolaBase_ne_zero.{u}
    nonempty_analytification_etalePresentation_hyperbola.{u}

end

end ComplexAnalytic
