/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import OkaTest.Analytification
import OkaTest.OpenBaseFiniteness
import OkaTest.OpenSubspace

/-!
# The `k ≥ 1` witness for the standard étale local isomorphism over a presented base

`ComplexAnalytic.isLocalIso_analytificationMap_etalePresHom`
(`Oka/Analytification/StandardEtaleLocalIsoBase.lean`) is stated at every `k`, and until this file
it had no instance at `k ≥ 1`. That file's own `## What is not here` says so and names the cheapest
route:

> **No `k ≥ 1` instance is exhibited, so the new content of the last theorem is unwitnessed.** …
> The cheapest would be `ComplexAnalytic.sqSubOnePair` (`OkaTest/OpenBaseFiniteness.lean`), which
> is a `StandardEtalePair` over an **arbitrary** commutative ring and so over a presented algebra
> at any `k`: **an instantiation and not a construction**, and this file does not make it.

It is right about the route, and `ComplexAnalytic.isLocalIso_analytificationMap_etalePresHom_node`
is that instantiation. **What the route does not say is that the cheapest pair's cover is an
isomorphism**, which is why there are two witnesses here and not one.

## The base is the node, and `g = ![0]` would have witnessed the index rather than the content

The base is `ComplexAnalytic.nodeG`, that is `n = 2`, `k = 1`, `ℂ[x, y]/(xy)`.

**A `k ≥ 1` presentation of `ℂ^n` would prove nothing.** Both `g = ![]` and `g = ![0]` present
`ℂ^n`, so an instance at either would exhibit the *index* `k ≥ 1` and not the content: the whole
difference between this theorem and the `k = 0` one is that the target is `X^an` rather than
`ℂ^n`, and at those two they are the same space.

**The node is a base at which the two `k ≥ 1` statements come apart**, which is the property the
library file's argument turns on. `Oka/Analytification/StandardEtaleLocalIso.lean` argues that the
*other* `k ≥ 1` statement — the same morphism followed by `ComplexAnalytic.analytificationInclHom`
— is false *"whenever `X^an` is a proper non-empty closed subset of `ℂ^n`, since its image is the
whole of `X^an` and a local isomorphism has open image"*, and it says in terms that neither
qualification follows from `k ≥ 1`: at `g = 0` the image is the whole of `ℂ^n`. The node's zero
locus is proper and non-empty, so it is inside that argument's hypotheses and `g = ![0]` is not.
**Nothing below proves that composite is not a local isomorphism** — see `## What is not checked
here`; the claim made is only that the witness sits where the question is live.

## Two pairs, because the cheapest one is an isomorphism

* `ComplexAnalytic.sqSubOnePair` is `f = X² − 1`, `g = X − 1`. Its own file proves
  `ComplexAnalytic.sqSubOnePair_X : (sqSubOnePair R).X = -1` — both relations are used — and
  builds `ComplexAnalytic.sqSubOneRingEquiv` out of it, so **the standard étale algebra is the
  base**. The morphism `ComplexAnalytic.isLocalIso_analytificationMap_etalePresHom_node_sqSubOne`
  is about is therefore an isomorphism, and a local isomorphism for a reason the theorem does not
  need.
* `ComplexAnalytic.sqSubOneTwoPair` is `f = X² − 1`, **`g = 2`**. Inverting `2` changes nothing
  over a `ℂ`-algebra, so the algebra is `R[X]/(X² − 1)` — two sheets, and not the base.

**`g = 2` and not `g = 1`, and the difference is a `1/2`.** With `g = 1` the `cond` field asks for
`derivative f * p₁ + f * p₂ = 1`, which needs `2` inverted in the coefficients and so a
`ℂ`-algebra hypothesis on `R`. With `g = 2` it asks for `2` on the right, and
`2X · X + (X² − 1)(−2) = 2` is an identity over **any** commutative ring — which is the same
economy `ComplexAnalytic.sqSubOnePair` records for its own `cond`, where the avoidable `1/2` is
called out in that file's docstring.

## The lifts, and the one place `simp` does not close on its own

`ComplexAnalytic.isLocalIso_analytificationMap_etalePresHom` asks for `F` and `G` in the new
variable together with `hF` and `hG` identifying their classes with the pair's `f` and `g` through
`ComplexAnalytic.polyPresentedAlgebraEquiv`. For `F = Z² − 1` and `G = Z − 1` both are `simp`:
`ComplexAnalytic.polyPresentedAlgebraEquiv_mk_X_var` gives the variable and the ring-hom lemmas
give the rest, with `ComplexAnalytic.sqSubOnePair_f` and `ComplexAnalytic.sqSubOnePair_g` on the
other side. **For `G = 2` it is `map_ofNat` twice and not `simp`** — the numeral has to be carried
through `Ideal.Quotient.mk` and then through the equivalence, and neither step is a `simp` lemma
in this configuration.

**Every definition below is unfolded by a `show … from rfl` and never by naming it to `simp`, and
the difference is measurable.** A draft that wrote `simp [nodeEtaleF, nodeEtaleG, nodeG, …]` put
**five** auto-generated equation lemmas into this module's row of
`scripts/DumpOkaDecls.lean` — one for each of the four definitions here **and
`ComplexAnalytic.nodeG.eq_1`, for a definition `OkaTest/Analytification.lean` owns**, which is the
one worth avoiding: a delta-unfold plants the equation lemma in the module that does the
unfolding, not in the module that made the definition. With the `show`s the module contributes
exactly its own declarations and `grep -E 'eq_1|match_'` over them is empty. This is the same
economy `ComplexAnalytic.sqSubOnePair_f`'s docstring buys with a named `rfl` lemma; a `show` is
the cheaper form where only one proof needs the unfolding.

## Neither space is empty, which is the half a reader cannot take on trust

`ComplexAnalytic.AnalyticSpace.IsLocalIso` of a morphism whose source is empty is not obviously
false, so a witness that exhibits no point is one a reader cannot tell from a vacuity. That is
taxis #1196's species — *"nothing says `localisationOpen …` is ever non-empty, so
`ComplexAnalytic.etaleAnalytificationIso` could be an isomorphism of empty spaces"* — and both
ends are exhibited below:

* the **base** by `nodeOrigin`, through `ComplexAnalytic.analytification_nodeG`, which is `rfl`;
* the **source of the `ComplexAnalytic.sqSubOneTwoPair` witness** by the tuple `(0, 0, 1, 1/2)` of
  `ℂ⁴`, whose three relations evaluate to `0 · 0`, `2⁻¹ · 2 − 1` and `1 − 1`;
* the **source of the `ComplexAnalytic.sqSubOnePair` witness** by `(0, 0, −1, −1/2)`, which is a
  different space — the two witnesses invert different `G`, so their presentations differ in one
  relation and a point of one is not a point of the other.

**There are two source bullets because there are two sources**, and this section said *"the
source"* while exhibiting one of them. The heading's *"neither space is empty"* is now what the
declarations below prove.

**On the import of `OkaTest.OpenSubspace`.** It is for one named witness, `nodeOrigin`, which is
the reason `OkaTest/HolomorphicMapGeneral.lean` gives for the same edge. Re-deriving the origin
here would be a second copy of a definition this repository already owns, and this project has
spent branches retiring duplicates of exactly that shape.

**And that name is unqualified on purpose.** `OkaTest/OpenSubspace.lean` opens no `namespace`, so
`nodeOrigin` is in the root namespace and prefixing it with this file's own namespace names
nothing. `scripts/check_docstring_names.py` is what says so, and it said it about a draft of this
file: everything else cited here is under `ComplexAnalytic`, which is what makes the one bare name
read as a typo rather than as the fact it is. **The prefixed form is not written out above because
the checker reads this paragraph too** — a docstring cannot quote the name it is explaining is
absent, which is the second thing that draft learned.

## Main definitions

- `ComplexAnalytic.sqSubOneTwoPair`: **the pair `f = X² − 1`, `g = 2`**, over an arbitrary
  commutative ring — the pair whose algebra is not the base.
- `ComplexAnalytic.nodeEtaleF`, `ComplexAnalytic.nodeEtaleG` and
  `ComplexAnalytic.nodeEtaleGSubOne`: the lifts `Z² − 1`, `2` and `Z − 1` in the new variable.
- `ComplexAnalytic.nodeEtalePt` and `ComplexAnalytic.nodeEtaleSqSubOnePt`: the tuples
  `(0, 0, 1, 1/2)` and `(0, 0, −1, −1/2)`, one point of each witness's source.

**The two witnesses are named and never numbered**, here or below. The prose above calls
`ComplexAnalytic.sqSubOnePair` the first of the two pairs and `## Main results` lists the
`ComplexAnalytic.sqSubOneTwoPair` witness first, so an ordinal in this file resolves two ways;
until it was repaired, `ComplexAnalytic.nonempty_analytification_etalePresentation_node`'s
docstring and the bullet above read *"the first witness"* and *"the second witness's source"* about
the same declaration.

## Main results

- `ComplexAnalytic.isLocalIso_analytificationMap_etalePresHom_node`: **the `k ≥ 1` witness**, at
  the node and at `ComplexAnalytic.sqSubOneTwoPair`.
- `ComplexAnalytic.isLocalIso_analytificationMap_etalePresHom_node_sqSubOne`: the same at
  `ComplexAnalytic.sqSubOnePair`, which is the instantiation
  `Oka/Analytification/StandardEtaleLocalIsoBase.lean` names as cheapest — and whose cover is the
  base.
- `ComplexAnalytic.nonempty_analytification_nodeG`: **the base is not empty.**
- `ComplexAnalytic.eval_etalePresentation_nodeEtalePt` and
  `ComplexAnalytic.nonempty_analytification_etalePresentation_node`: **the source of the
  `ComplexAnalytic.sqSubOneTwoPair` witness is not empty.**
- `ComplexAnalytic.eval_etalePresentation_nodeEtaleSqSubOnePt` and
  `ComplexAnalytic.nonempty_analytification_etalePresentation_node_sqSubOne`: **the same for the
  `ComplexAnalytic.sqSubOnePair` witness**, whose source is a different space — a different `G`
  and so a different presentation. With the two together, **neither** witness is a statement about
  an empty space; that claim was made here when only the first of the two was proved.

## What is not checked here

* **Nothing about how many sheets either cover has.** `ComplexAnalytic.sqSubOnePair`'s algebra is
  the base — that is `ComplexAnalytic.sqSubOneRingEquiv`'s statement and it is quoted here, not
  reproved — and `ComplexAnalytic.sqSubOneTwoPair`'s is `R[X]/(X² − 1)`, which is **not** shown
  below to be anything other than the base. Two sheets is what the algebra says to a reader and
  not what any declaration here says; proving it, or proving the second cover is not an
  isomorphism, is a separate statement and nothing below attempts it.
* **No proof that the composite with `ComplexAnalytic.analytificationInclHom` fails at this
  base.** `Oka/Analytification/StandardEtaleLocalIso.lean` argues that in prose, from a local
  isomorphism having open image and the node having empty interior in `ℂ²`. **The argument is not
  a theorem in this repository**, here or anywhere, and the base above was chosen so that its
  hypotheses hold rather than so that its conclusion is available.
* **Nothing at `k ≥ 2`, and nothing about a general `k`.** Both witnesses are at one presentation
  with one relation. The theorem is general in `k` and this file is evidence that it is
  instantiable, not that it is instantiable uniformly.
* **No finiteness *here*, and so no `ComplexAnalytic.AnalyticSpace.IsFiniteEtale` below.** Neither
  witness above has a finiteness field and nothing in this file supplies one. **This bullet read
  *The finiteness half at `k ≥ 1` does not exist —
  `Oka/Analytification/StandardEtaleFiniteEtale.lean` and
  `Oka/Analytification/StandardEtaleFiniteness.lean` both record it absent* until 2026-09-20**,
  and all three clauses of that were falsified the same day by `5888ddb`: the half exists, as
  `ComplexAnalytic.isFinite_restrictHom_analytificationMap_etalePresHom`
  (`Oka/Analytification/StandardEtaleFinitenessBase.lean`), and both of the files it named now
  carry dated records saying so instead. **The class is instantiated at
  `ComplexAnalytic.sqSubOneTwoPair` in `OkaTest/StandardEtaleFiniteEtaleBase.lean`**, which
  imports this file. Unrestricted finiteness quantified over pairs is still false, with the
  counterexample in `Oka/Analytification/MonicHypersurface.lean`; what that instance turns on is
  that `g = 2` inverts nothing, which is the one thing a reader should carry away from it.
* **No `#print axioms` guard.** `OkaTest/Axioms/` guards declarations of the `Oka` library;
  nothing below is one. `ComplexAnalytic.condPair` and `ComplexAnalytic.sqSubOnePair`, the two
  standard étale pairs this repository already has, are unguarded for the same reason.
-/

open MvPolynomial

universe u

namespace ComplexAnalytic

noncomputable section

/-! ### The pair `f = X² − 1`, `g = 2` -/

variable (R : Type*) [CommRing R]

/-- **The pair `f = X² − 1`, `g = 2`**, over an arbitrary commutative ring.

`cond` is discharged at `p₁ = X`, `p₂ = −2`, `n = 1`, which is `2X · X − 2(X² − 1) = 2`. **No
hypothesis on `R`**, and that is what `g = 2` buys over the equally natural `g = 1`: with `1` on
the right the same identity needs `2` inverted in the coefficients, and so a `ℂ`-algebra. Over a
`ℂ`-algebra the two pairs have the same standard étale algebra, since `2` is already a unit
there. -/
def sqSubOneTwoPair : StandardEtalePair R where
  f := Polynomial.X ^ 2 - 1
  monic_f := by simpa using Polynomial.monic_X_pow_sub_C (1 : R) two_ne_zero
  g := 2
  cond := ⟨Polynomial.X, -2, 1, by
    simp only [Polynomial.derivative_sub, Polynomial.derivative_X_pow, Polynomial.derivative_one,
      sub_zero, Nat.cast_ofNat, map_ofNat, pow_one]
    ring⟩

/-- The `f` of `ComplexAnalytic.sqSubOneTwoPair`, by `rfl`.

This and the next exist so that **nothing below has to `rw` or `simp` at
`ComplexAnalytic.sqSubOneTwoPair` itself**, which is the reason
`ComplexAnalytic.sqSubOnePair_f` gives for its own existence: unfolding a definition that way
plants an auto-generated equation lemma under its own name. -/
@[simp]
theorem sqSubOneTwoPair_f : (sqSubOneTwoPair R).f = Polynomial.X ^ 2 - 1 := rfl

/-- The `g` of `ComplexAnalytic.sqSubOneTwoPair`, by `rfl`. -/
@[simp]
theorem sqSubOneTwoPair_g : (sqSubOneTwoPair R).g = 2 := rfl

/-! ### The lifts, in the new variable -/

/-- `F = Z² − 1`, in the variable `ComplexAnalytic.localisationVar 2` adjoined to the node's two.

Both pairs below have the same `f`, so both witnesses have the same `F`. -/
def nodeEtaleF : MvPolynomial (ULift.{u} (Fin 3)) ℂ :=
  MvPolynomial.X (localisationVar.{u} 2) ^ 2 - 1

/-- `G = 2`, the lift of `ComplexAnalytic.sqSubOneTwoPair`'s `g`. -/
def nodeEtaleG : MvPolynomial (ULift.{u} (Fin 3)) ℂ := 2

/-- `G = Z − 1`, the lift of `ComplexAnalytic.sqSubOnePair`'s `g`. -/
def nodeEtaleGSubOne : MvPolynomial (ULift.{u} (Fin 3)) ℂ :=
  MvPolynomial.X (localisationVar.{u} 2) - 1

/-! ### The two witnesses -/

/-- **A standard étale morphism over the node analytifies to a local isomorphism onto the node**
— `ComplexAnalytic.isLocalIso_analytificationMap_etalePresHom` at `k = 1`, which is the instance
`Oka/Analytification/StandardEtaleLocalIsoBase.lean` records as missing.

The pair is `ComplexAnalytic.sqSubOneTwoPair`, whose standard étale algebra is `R[X]/(X² − 1)`
rather than the base; `hG` is `map_ofNat` twice, carrying the numeral through
`Ideal.Quotient.mk` and then through `ComplexAnalytic.polyPresentedAlgebraEquiv`. -/
theorem isLocalIso_analytificationMap_etalePresHom_node :
    AnalyticSpace.IsLocalIso
      (analytificationMap.{u} (etalePresHom.{u} nodeG.{u} nodeEtaleF.{u} nodeEtaleG.{u})) :=
  isLocalIso_analytificationMap_etalePresHom.{u} nodeG.{u} nodeEtaleF.{u} nodeEtaleG.{u}
    (sqSubOneTwoPair (PresentedAlgebra.{u} 2 1 nodeG.{u}))
    (by simp [show nodeEtaleF.{u} = MvPolynomial.X (localisationVar.{u} 2) ^ 2 - 1 from rfl])
    (by
      rw [show nodeEtaleG.{u} = (2 : MvPolynomial (ULift.{u} (Fin 3)) ℂ) from rfl]
      simp only [sqSubOneTwoPair_g, map_ofNat])

/-- **The same at `ComplexAnalytic.sqSubOnePair`**, which is the instantiation
`Oka/Analytification/StandardEtaleLocalIsoBase.lean` names as the cheapest.

It is cheapest and it is the weaker of the two: `ComplexAnalytic.sqSubOneRingEquiv` identifies
that pair's standard étale algebra with the base, so this morphism is an isomorphism and is a
local isomorphism for a reason the theorem does not need. **That is why it is not the only witness
here.** -/
theorem isLocalIso_analytificationMap_etalePresHom_node_sqSubOne :
    AnalyticSpace.IsLocalIso
      (analytificationMap.{u} (etalePresHom.{u} nodeG.{u} nodeEtaleF.{u} nodeEtaleGSubOne.{u})) :=
  isLocalIso_analytificationMap_etalePresHom.{u} nodeG.{u} nodeEtaleF.{u} nodeEtaleGSubOne.{u}
    (sqSubOnePair (PresentedAlgebra.{u} 2 1 nodeG.{u}))
    (by simp [show nodeEtaleF.{u} = MvPolynomial.X (localisationVar.{u} 2) ^ 2 - 1 from rfl])
    (by simp [show nodeEtaleGSubOne.{u} = MvPolynomial.X (localisationVar.{u} 2) - 1 from rfl])

/-! ### Neither space is empty -/

/-- **The base is not empty.** `ComplexAnalytic.analytification_nodeG` is `rfl` onto
`ComplexAnalytic.AnalyticSpace.node`, and `nodeOrigin` is a point of that. -/
theorem nonempty_analytification_nodeG :
    Nonempty (AnalyticSpace.analytification.{u} nodeG.{u}) :=
  ⟨analytification_nodeG.{u} ▸ nodeOrigin.{u}⟩

/-- The tuple `(0, 0, 1, 1/2)` of `ℂ⁴`: the origin of the node, the square root `1`, and the
inverse of `G = 2`. -/
def nodeEtalePt : ULift.{u} (Fin 4) → ℂ :=
  fun i ↦ if i.down = 2 then 1 else if i.down = 3 then 2⁻¹ else 0

/-- **The three relations vanish there**: `0 · 0`, `2⁻¹ · 2 − 1` and `1 − 1`.

`map_ofNat` is what carries `G = 2` through `MvPolynomial.rename` and then through
`MvPolynomial.eval`; without it the middle goal is left as
`2⁻¹ * eval nodeEtalePt (rename _ 2) - 1 = 0`. -/
theorem eval_etalePresentation_nodeEtalePt (j : Fin 3) :
    MvPolynomial.eval nodeEtalePt.{u}
      (etalePresentation.{u} nodeG.{u} nodeEtaleF.{u} nodeEtaleG.{u} j) = 0 := by
  fin_cases j <;>
    simp [etalePresentation, localisationPresentation, polyPresentation, localisationIncl,
      localisationVar, Fin.snoc, map_ofNat,
      show nodeG.{u} = fun _ ↦ nodePoly.{u} from rfl,
      show nodePoly.{u} =
        MvPolynomial.X (ULift.up 0) * MvPolynomial.X (ULift.up 1) from rfl,
      show nodeEtaleF.{u} = MvPolynomial.X (localisationVar.{u} 2) ^ 2 - 1 from rfl,
      show nodeEtaleG.{u} = (2 : MvPolynomial (ULift.{u} (Fin 3)) ℂ) from rfl,
      show nodeEtalePt.{u} =
        fun i ↦ if i.down = 2 then (1 : ℂ) else if i.down = 3 then 2⁻¹ else 0 from rfl]

/-- **The source of the `ComplexAnalytic.sqSubOneTwoPair` witness is not empty**, so that witness
is not a statement about a morphism out of an empty space.

It says nothing about the other one, which is over a different presentation;
`ComplexAnalytic.nonempty_analytification_etalePresentation_node_sqSubOne` is that. -/
theorem nonempty_analytification_etalePresentation_node :
    Nonempty (AnalyticSpace.analytification.{u}
      (etalePresentation.{u} nodeG.{u} nodeEtaleF.{u} nodeEtaleG.{u})) :=
  ⟨⟨⟨nodeEtalePt.{u}, trivial⟩,
    (mem_zeroLocus_polySection_iff.{u} _ _).2 eval_etalePresentation_nodeEtalePt.{u}⟩⟩

/-- The tuple `(0, 0, −1, −1/2)` of `ℂ⁴`: the origin of the node, the square root `−1`, and the
inverse of `G = Z − 1` there.

**`Z = 1` is not available and `Z = −1` is forced**, which is the difference between this point
and `ComplexAnalytic.nodeEtalePt`: `ComplexAnalytic.sqSubOnePair`'s `g` is `X − 1` rather than `2`,
so the two new relations are `Z² − 1 = 0` and `w(Z − 1) = 1` together, and the first root of the
first relation is killed by the second. -/
def nodeEtaleSqSubOnePt : ULift.{u} (Fin 4) → ℂ :=
  fun i ↦ if i.down = 2 then -1 else if i.down = 3 then -2⁻¹ else 0

/-- **The three relations vanish there**: `0 · 0`, `(−2⁻¹)(−1 − 1) − 1` and `(−1)² − 1`.

Unlike `ComplexAnalytic.eval_etalePresentation_nodeEtalePt` this needs no `map_ofNat`: the `G`
here is `Z − 1` and carries through `MvPolynomial.rename` as a variable and a one. -/
theorem eval_etalePresentation_nodeEtaleSqSubOnePt (j : Fin 3) :
    MvPolynomial.eval nodeEtaleSqSubOnePt.{u}
      (etalePresentation.{u} nodeG.{u} nodeEtaleF.{u} nodeEtaleGSubOne.{u} j) = 0 := by
  fin_cases j <;>
    simp [etalePresentation, localisationPresentation, polyPresentation, localisationIncl,
      localisationVar, Fin.snoc,
      show nodeG.{u} = fun _ ↦ nodePoly.{u} from rfl,
      show nodePoly.{u} =
        MvPolynomial.X (ULift.up 0) * MvPolynomial.X (ULift.up 1) from rfl,
      show nodeEtaleF.{u} = MvPolynomial.X (localisationVar.{u} 2) ^ 2 - 1 from rfl,
      show nodeEtaleGSubOne.{u} = MvPolynomial.X (localisationVar.{u} 2) - 1 from rfl,
      show nodeEtaleSqSubOnePt.{u} =
        fun i ↦ if i.down = 2 then (-1 : ℂ) else if i.down = 3 then -2⁻¹ else 0 from rfl]
  ring

/-- **The source of the `ComplexAnalytic.sqSubOnePair` witness is not empty either**, which is
what makes `## Main results`' claim true of both witnesses rather than of one.

The two are over **different presentations** — `ComplexAnalytic.nodeEtaleG` against
`ComplexAnalytic.nodeEtaleGSubOne` — so they are morphisms out of two different spaces and
`ComplexAnalytic.nonempty_analytification_etalePresentation_node` says nothing about this one. -/
theorem nonempty_analytification_etalePresentation_node_sqSubOne :
    Nonempty (AnalyticSpace.analytification.{u}
      (etalePresentation.{u} nodeG.{u} nodeEtaleF.{u} nodeEtaleGSubOne.{u})) :=
  ⟨⟨⟨nodeEtaleSqSubOnePt.{u}, trivial⟩,
    (mem_zeroLocus_polySection_iff.{u} _ _).2 eval_etalePresentation_nodeEtaleSqSubOnePt.{u}⟩⟩

end

end ComplexAnalytic
