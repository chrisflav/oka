/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka

/-!
# A standard étale pair whose algebra is the base, and whose open subset of the base is empty

`Oka/Analytification/OpenBaseFiniteness.lean` removes from `ℂ^n` the image of the locus where a
second polynomial `G` vanishes on the hypersurface `{F = 0}`, and proves that over the complement
`V` the inversion of `G` is vacuous. Its own `## What is not here` says that the size of `V` is a
hypothesis on `(F, G)` and not a theorem, and settles both extremes at witnesses — `V = ℂ^n` at
`G = 1`, and `V = ∅` at `F = G = X`.

**This file says the sharper thing, which is that `V` can be empty on a pair whose standard étale
algebra is the base itself, so that there was nothing to remove.** At `f = X² − 1`, `g = X − 1`:

* the pair is a `StandardEtalePair` over **any** commutative ring, `cond` discharged at
  `p₁ = X − 1`, `p₂ = −1`, `n = 2`;
* whenever `2` is a unit its **structure map is an isomorphism** onto the standard étale algebra
  — that is what `ComplexAnalytic.sqSubOneRingEquiv` is, since the inverse it exhibits is
  `Algebra.ofId` — and the algebra is finite over the base
  (`ComplexAnalytic.moduleFinite_sqSubOnePair`) as well as étale;
* and `ComplexAnalytic.hypersurfaceCommonZeroImage` of it is **all of `ℂ^n`**, so the open subset
  of the base that file constructs is empty and its theorem says nothing.

So *"finiteness over an open subset of the base"* is a **sufficient** condition and not the shape
of taxis #1112's eventual result. Nothing in
`Oka/Analytification/OpenBaseFiniteness.lean` is wrong — every theorem there is true and
`ComplexAnalytic.hypersurfaceCommonZeroImage` is the right object for the statement it makes.
What this file changes is an estimate of what that statement buys.

## Why the existing witness does not already say this

`ComplexAnalytic.hypersurfaceCommonZeroImage_X` is at `F = G = X` and already gives an empty `V`.
That pair **is** a `StandardEtalePair` too — `ComplexAnalytic.xPair`, `cond` at `p₁ = 0`,
`p₂ = 1`, `n = 1` since `derivative X = 1` — so "the bad set is everything on a standard étale
pair" is not the new content either. What separates the two is what the algebra *is*: there the
class of `X` is `0` and is inverted, so the algebra is the **zero ring**
(`ComplexAnalytic.subsingleton_xPairRing`), where here the class of `X` is `−1`, `g` becomes the
unit `−2`, and the algebra is the base. An empty `V` over the zero ring is uninformative; an empty
`V` over an isomorphism is the finding.

Both halves of that comparison are theorems below rather than remarks, because the whole reason
this file exists is that the version of them on taxis #1112 was arithmetic on a thread.

## `cond` needs no `1/2`, and the equivalence does

The witness this file was written from used `p₁ = (1 − X)/2`, `p₂ = 1`, `n = 1`, which needs `2`
inverted in the base. It is not necessary:

    derivative (X² − 1) * (X − 1) + (X² − 1) * (−1) = 2X² − 2X − X² + 1 = (X − 1)²

so `ComplexAnalytic.sqSubOnePair` is defined over an arbitrary `CommRing` with no hypothesis at
all. Where `2` does have to be a unit is `ComplexAnalytic.sqSubOneRingEquiv` and nowhere else, and
that is not an artefact of the proof. `ComplexAnalytic.sqSubOnePair_X` says the two relations
**force** the class of `X` to be `−1`, so `g` becomes `−2` and `2` is a unit of the algebra over
every base at all (`ComplexAnalytic.isUnit_two_sqSubOnePairRing`) — hence
`ComplexAnalytic.isUnit_two_of_sqSubOneRingEquiv`, which is the hypothesis read backwards out of
its own conclusion. Over `ℤ` there is therefore no such equivalence. **What the algebra is over
`ℤ` — `ℤ[1/2]` — is a further statement and is not proved here**; pricing the hypothesis needs
only that it cannot be dropped. Over a `ℂ`-algebra — which is every base in this development,
`ComplexAnalytic.isUnit_two_mvPolynomial` for the one used here — it is free.

## Main definitions

- `ComplexAnalytic.sqSubOnePair`: **the pair `f = X² − 1`, `g = X − 1`** over an arbitrary
  commutative ring.
- `ComplexAnalytic.sqSubOneRingEquiv`: **its standard étale algebra is the base**, given that `2`
  is a unit.
- `ComplexAnalytic.sqSubOneRingEquivPolyBase`: the same at the base
  `Oka/Analytification/OpenBaseFiniteness.lean` works over, where the hypothesis is discharged.
- `ComplexAnalytic.xPair`: **the pair `f = g = X`**, which is the one
  `ComplexAnalytic.hypersurfaceCommonZeroImage_X` is about, exhibited as a `StandardEtalePair` so
  that the comparison above is between two of them.

## Main results

- `ComplexAnalytic.sqSubOnePair_X`: **the class of `X` in the standard étale algebra is `−1`** —
  `(X − 1)(X + 1) = X² − 1 = 0` with `X − 1` invertible. This is the one computation everything
  else about the algebra rests on.
- `ComplexAnalytic.isUnit_two_sqSubOnePairRing` and
  `ComplexAnalytic.isUnit_two_of_sqSubOneRingEquiv`: **`2` is a unit of the algebra over every
  base, so the equivalence's hypothesis cannot be dropped.**
- `ComplexAnalytic.moduleFinite_sqSubOnePair`: the algebra is **finite** over the base, given that
  `2` is a unit — the hypothesis is `ComplexAnalytic.sqSubOneRingEquiv`'s, transported. It is also
  étale, but that is Mathlib's instance for *every* pair and is not evidence about this one.
  **This row carried no hypothesis until 2026-09-21**, immediately under the row that prices one.
- `ComplexAnalytic.subsingleton_xPairRing`: **the algebra of `f = g = X` is the zero ring**, which
  is what makes the witness already on record degenerate and this one not.
- `ComplexAnalytic.hypersurfaceCommonZeroImage_sqSubOnePair`: **the bad set of this pair is all of
  `ℂ^n`** — the punchline, and `ComplexAnalytic.hypersurfaceCommonZeroImage_X`'s proof with the
  root `0` replaced by `1` and a second evaluation, since here `F` and `G` differ.

## What is not here

* **No boundary construction, and no claim that one would work.** The diagnosis on taxis #1112 —
  that what has to be removed is the image of `closure({g ≠ 0}) ∩ {g = 0}` inside the hypersurface
  rather than of `{g = 0}` itself — is an **unmeasured proposal** by `oka-slot-1-e3`, recorded
  there and neither used nor tested here. That same comment prices it as needing a different
  finiteness proof, since over the larger open set the source is no longer the whole hypersurface
  and so `ComplexAnalytic.isFinite_comp_projRestrict_of_range_eq`'s `hrange` is not satisfied by
  the hypersurface's own range; that price is a reading of theirs and not a measurement of mine.
* **Nothing is analytified.** `ComplexAnalytic.sqSubOneRingEquiv` is algebra and
  `ComplexAnalytic.hypersurfaceCommonZeroImage_sqSubOnePair` is a set in `ℂ^n`; the two are
  related by the choice of `f` and `g` and by nothing else. In particular this is **not** a
  counterexample to `IsFiniteEtale` of anything, and not a strengthening of taxis #1112's `Pex`,
  which is a counterexample to a statement rather than a witness that a strategy under-delivers.
* **No general-degree or general-root version.** One pair, chosen because its algebra is
  computable.
* **Under `OkaTest/` and not under `Oka/`.** It is a witness, and
  `OkaTest/StandardEtaleCond.lean` is the precedent for a `StandardEtalePair` witness living
  here. It also needs `Mathlib.RingTheory.Etale.StandardEtale`, which reaches
  `Oka/Analytification/OpenBaseFiniteness.lean` through no import — that file's own
  `## What is not here` declines to pay an import for a second witness, and a test file imports
  `Oka` and pays nothing.
-/

open CategoryTheory Polynomial

universe u

namespace ComplexAnalytic

noncomputable section

/-! ### The pair -/

variable (R : Type*) [CommRing R]

/-- **The pair `f = X² − 1`, `g = X − 1`**, over an arbitrary commutative ring.

`cond` is discharged at `p₁ = X − 1`, `p₂ = −1`, `n = 2`, which is
`2X(X − 1) − (X² − 1) = (X − 1)²`. **No hypothesis on `R`**: the `1/2` in the witness this file
was written from is avoidable, and where `2` really does have to be a unit is
`ComplexAnalytic.sqSubOneRingEquiv`. -/
def sqSubOnePair : StandardEtalePair R where
  f := Polynomial.X ^ 2 - 1
  monic_f := by simpa using Polynomial.monic_X_pow_sub_C (1 : R) two_ne_zero
  g := Polynomial.X - 1
  cond := ⟨Polynomial.X - 1, -1, 2, by
    simp only [derivative_sub, derivative_X_pow, derivative_one, sub_zero, Nat.cast_ofNat,
      map_ofNat]
    ring⟩

/-- The `f` of `ComplexAnalytic.sqSubOnePair`, by `rfl`.

This and the next exist so that **nothing below has to `rw` or `simp` at
`ComplexAnalytic.sqSubOnePair` itself**: unfolding a definition that way plants an auto-generated
equation lemma under its own name, which `OkaTest/StandardEtaleCond.lean`'s module docstring
records happening once and says how it was found. -/
@[simp]
theorem sqSubOnePair_f : (sqSubOnePair R).f = Polynomial.X ^ 2 - 1 := rfl

/-- The `g` of `ComplexAnalytic.sqSubOnePair`, by `rfl`. -/
@[simp]
theorem sqSubOnePair_g : (sqSubOnePair R).g = Polynomial.X - 1 := rfl

variable {R}

/-! ### The algebra is the base -/

/-- **The class of `X` in the standard étale algebra of `ComplexAnalytic.sqSubOnePair` is `−1`.**

Both relations are used and neither on its own suffices: `X² − 1 = 0` gives
`(X − 1)(X + 1) = 0`, and `X − 1` is a unit there because `StandardEtalePair.Ring` inverts `g`.
So `X + 1 = 0`.

**This is why the equivalence below needs `2` inverted.** With the class of `X` pinned to `−1`,
`g` is the constant `−2`, and an algebra in which `−2` is a unit cannot be the base unless `2`
already was one. -/
theorem sqSubOnePair_X : (sqSubOnePair R).X = -1 := by
  have h := (StandardEtalePair.hasMap_X (P := sqSubOnePair R))
  have hf : (sqSubOnePair R).X ^ 2 - 1 = 0 := by simpa using h.1
  have hg : IsUnit ((sqSubOnePair R).X - 1) := by simpa using h.2
  have hmul : ((sqSubOnePair R).X - 1) * ((sqSubOnePair R).X + 1) = 0 := by linear_combination hf
  exact eq_neg_of_add_eq_zero_left (hg.mul_right_eq_zero.mp hmul)

/-- **`−1` is a point of the base at which `f` vanishes and `g` is invertible**, which is what
`StandardEtalePair.lift` asks for. `f (−1) = 0` is `1 − 1`, and `g (−1) = −2`. -/
theorem sqSubOnePair_hasMap_neg_one (h2 : IsUnit (2 : R)) :
    (sqSubOnePair R).HasMap (-1 : R) := by
  constructor
  · simp
  · have h : (Polynomial.aeval (-1 : R)) (sqSubOnePair R).g = -2 := by
      rw [sqSubOnePair_g]
      simp only [map_sub, Polynomial.aeval_X, map_one]
      norm_num
    rw [h]
    exact h2.neg

/-- **The standard étale algebra of `ComplexAnalytic.sqSubOnePair` is the base itself wherever `2`
is a unit of the base**, which is `h2`, so the morphism it names is an isomorphism there.

Both directions are forced. Out of the algebra there is exactly one map sending the class of `X`
to `−1`, which is `StandardEtalePair.lift`; into it there is exactly one `R`-algebra map, the
structure map. That they are inverse is `StandardEtalePair.hom_ext` in one direction — the
composite fixes the class of `X` because `ComplexAnalytic.sqSubOnePair_X` says that class **is**
`−1` — and, in the other, that an `R`-algebra endomorphism of `R` is the identity.

`h2` is not removable: over `ℤ` the algebra is `ℤ[1/2]`.

**This head carried no hypothesis until 2026-09-21**, two paragraphs above the sentence that
prices one. The claim is unchanged and only its warrant was missing. -/
def sqSubOneRingEquiv (h2 : IsUnit (2 : R)) : (sqSubOnePair R).Ring ≃ₐ[R] R :=
  AlgEquiv.ofAlgHom ((sqSubOnePair R).lift (-1 : R) (sqSubOnePair_hasMap_neg_one h2))
    (Algebra.ofId R _) (AlgHom.ext fun x ↦ by simp)
    (StandardEtalePair.hom_ext (by simp [Algebra.ofId, sqSubOnePair_X]))

/-- **`2` is a unit in the standard étale algebra whatever the base is** — the class of `X` is
`-1` by `ComplexAnalytic.sqSubOnePair_X` and `g` is inverted there, so `-2` is a unit and hence so
is `2`.

This is the fact that makes `ComplexAnalytic.sqSubOneRingEquiv`'s hypothesis a feature of the pair
rather than of the proof. -/
theorem isUnit_two_sqSubOnePairRing : IsUnit (2 : (sqSubOnePair R).Ring) := by
  have h := (StandardEtalePair.hasMap_X (P := sqSubOnePair R))
  have hu : IsUnit ((sqSubOnePair R).X - 1) := by simpa using h.2
  rw [sqSubOnePair_X, show (-1 : (sqSubOnePair R).Ring) - 1 = -2 by norm_num] at hu
  simpa using hu

/-- **`ComplexAnalytic.sqSubOneRingEquiv`'s hypothesis is necessary**: if the standard étale
algebra is the base, then `2` was already a unit of the base.

So over `ℤ` there is no such equivalence, and the algebra is not `ℤ`. **What it *is* — `ℤ[1/2]` —
is a further statement and is not proved here**; all that is needed to price the hypothesis is
that it cannot be dropped. -/
theorem isUnit_two_of_sqSubOneRingEquiv (e : (sqSubOnePair R).Ring ≃ₐ[R] R) :
    IsUnit (2 : R) := by
  have h := (isUnit_two_sqSubOnePairRing (R := R)).map e.toAlgHom
  rwa [map_ofNat] at h

/-- **The algebra is finite over the base wherever `2` is a unit of it**, transported along
`ComplexAnalytic.sqSubOneRingEquiv` and carrying that equivalence's hypothesis, which is `h2`.

Étaleness is *not* proved here and is not evidence about this pair: `Algebra.Etale R P.Ring` is a
Mathlib instance for **every** `StandardEtalePair`, so it holds at `F = G = X` and at the zero
ring just as much. Finiteness is the half that sees which pair this is.

**This head carried no hypothesis until 2026-09-21.** -/
theorem moduleFinite_sqSubOnePair (h2 : IsUnit (2 : R)) :
    Module.Finite R (sqSubOnePair R).Ring :=
  Module.Finite.equiv (sqSubOneRingEquiv h2).symm.toLinearEquiv

/-! ### The pair already on record, and why it is degenerate -/

variable (R) in
/-- **The pair `f = g = X`**, which is the one `ComplexAnalytic.hypersurfaceCommonZeroImage_X` is
about, exhibited as a `StandardEtalePair`.

`cond` is `derivative X * 0 + X * 1 = X ^ 1`. It is here only so that the comparison this file
makes is between two standard étale pairs and not between one of them and a pair of polynomials:
the point of `ComplexAnalytic.subsingleton_xPairRing` below is that being a `StandardEtalePair` is
not by itself enough to make an empty open subset of the base informative. -/
def xPair : StandardEtalePair R where
  f := Polynomial.X
  monic_f := Polynomial.monic_X
  g := Polynomial.X
  cond := ⟨0, 1, 1, by simp⟩

/-- **The standard étale algebra of `ComplexAnalytic.xPair` is the zero ring.**

Its two relations are `X = 0` and `X` invertible, so `0` is a unit. Nothing here is special to
`X`: it is what inverting an element one has just killed always does, and it is why an empty open
subset of the base for that pair says nothing about the strategy.

The two `rfl` hypotheses do locally what `ComplexAnalytic.sqSubOnePair_f` and
`ComplexAnalytic.sqSubOnePair_g` do globally, and for the same reason — nothing may `rw` or `simp`
at `ComplexAnalytic.xPair` itself. They are not `@[simp]` lemmas of their own because this pair
has one consumer. -/
theorem subsingleton_xPairRing : Subsingleton (xPair R).Ring := by
  have h := (StandardEtalePair.hasMap_X (P := xPair R))
  have hf : (xPair R).f = Polynomial.X := rfl
  have hg : (xPair R).g = Polynomial.X := rfl
  have hx : (xPair R).X = 0 := by simpa [hf] using h.1
  have hu : IsUnit (0 : (xPair R).Ring) := by simpa [hg, hx] using h.2
  exact subsingleton_of_zero_eq_one (isUnit_zero_iff.mp hu)

/-! ### At the base of `Oka/Analytification/OpenBaseFiniteness.lean` -/

/-- **`2` is a unit in `ℂ[x₁, …, x_n]`**, since it is `MvPolynomial.C` of a unit of `ℂ`.

The `rw` is the whole of it: `(2 : MvPolynomial σ ℂ)` is an `OfNat` literal and has to be turned
into `MvPolynomial.C 2` before the ring hom can be applied to it, which is `map_ofNat` read
backwards. -/
theorem isUnit_two_mvPolynomial {σ : Type*} : IsUnit (2 : MvPolynomial σ ℂ) := by
  rw [show (2 : MvPolynomial σ ℂ) = MvPolynomial.C 2 from
    (map_ofNat (MvPolynomial.C : ℂ →+* MvPolynomial σ ℂ) 2).symm]
  exact (isUnit_iff_ne_zero.mpr (two_ne_zero : (2 : ℂ) ≠ 0)).map
    (MvPolynomial.C : ℂ →+* MvPolynomial σ ℂ)

/-- **The standard étale algebra of `ComplexAnalytic.sqSubOnePair` over the base
`Oka/Analytification/OpenBaseFiniteness.lean` works over is that base**, the hypothesis of
`ComplexAnalytic.sqSubOneRingEquiv` being discharged by
`ComplexAnalytic.isUnit_two_mvPolynomial`.

It is stated separately from the theorem below so that the two halves of this file's claim are
about the same `n` and the same ring, and neither is a reader's instantiation of a general
statement. -/
def sqSubOneRingEquivPolyBase (n : ℕ) :
    (sqSubOnePair (MvPolynomial (ULift.{u} (Fin n)) ℂ)).Ring ≃ₐ[MvPolynomial
      (ULift.{u} (Fin n)) ℂ] MvPolynomial (ULift.{u} (Fin n)) ℂ :=
  sqSubOneRingEquiv isUnit_two_mvPolynomial

variable {n : ℕ}

/-- **The bad set of `ComplexAnalytic.sqSubOnePair` is all of `ℂ^n`**, so the open subset of the
base of `Oka/Analytification/OpenBaseFiniteness.lean` is empty for a pair whose standard étale
algebra is the base itself.

The hypersurface `{X² − 1 = 0}` is the pair of hyperplanes where the last coordinate is `±1`, and
`G = X − 1` vanishes on the whole of one of them, whose projection to `ℂ^n` is onto. So the
witness at a base point `w` is `(w, 1)`, which is
`ComplexAnalytic.hypersurfaceCommonZeroImage_X`'s `(w, 0)` with the root moved — and, unlike
there, `F` and `G` differ, so the evaluation has to be done twice.

**`hr` is not decoration.** Rewriting with `ComplexAnalytic.range_base_analytificationIncl`
directly fails — *"Did not find an occurrence of the pattern"*, with a note that the target is not
type-correct at `instances` transparency — because the pattern is stated at
`ComplexAnalytic.analytificationIncl` and the goal carries the
`ComplexAnalytic.AnalyticSpace.Hom.toLRSHom` wrapper. Ascribing the statement first and rewriting
with the ascription is what goes through, and it is why
`ComplexAnalytic.hypersurfaceCommonZeroImage_X` has the same detour. -/
theorem hypersurfaceCommonZeroImage_sqSubOnePair :
    hypersurfaceCommonZeroImage.{u} (n := n)
      (sqSubOnePair (MvPolynomial (ULift.{u} (Fin n)) ℂ)).f
      (sqSubOnePair (MvPolynomial (ULift.{u} (Fin n)) ℂ)).g = Set.univ := by
  rw [sqSubOnePair_f, sqSubOnePair_g]
  refine Set.eq_univ_of_forall fun w ↦ ?_
  set z : ULift.{u} (Fin (n + 1)) → ℂ := (uliftSnocHomeo.{u} n).symm (w, 1) with hz
  have hF : MvPolynomial.eval z ((lastVarPolyEquiv.{u} n).symm
      ((Polynomial.X ^ 2 - 1 : Polynomial (MvPolynomial (ULift.{u} (Fin n)) ℂ)))) = 0 := by
    rw [eval_lastVarPolyEquiv_symm.{u}, hz, Homeomorph.apply_symm_apply]
    simp [polyFamily]
  have hG : MvPolynomial.eval z ((lastVarPolyEquiv.{u} n).symm
      ((Polynomial.X - 1 : Polynomial (MvPolynomial (ULift.{u} (Fin n)) ℂ)))) = 0 := by
    rw [eval_lastVarPolyEquiv_symm.{u}, hz, Homeomorph.apply_symm_apply]
    simp [polyFamily]
  have hmem : z ∈ Set.range ⇑(AnalyticSpace.Hom.toLRSHom
      (analytificationInclHom.{u} ![(lastVarPolyEquiv.{u} n).symm
        ((Polynomial.X ^ 2 - 1 : Polynomial (MvPolynomial (ULift.{u} (Fin n)) ℂ)))])).base := by
    have hr : Set.range ⇑(AnalyticSpace.Hom.toLRSHom
        (analytificationInclHom.{u} ![(lastVarPolyEquiv.{u} n).symm
          ((Polynomial.X ^ 2 - 1 : Polynomial (MvPolynomial (ULift.{u} (Fin n)) ℂ)))])).base =
        {y | ∀ j, MvPolynomial.eval y (![(lastVarPolyEquiv.{u} n).symm
          ((Polynomial.X ^ 2 - 1 : Polynomial (MvPolynomial (ULift.{u} (Fin n)) ℂ)))] j) = 0} :=
      range_base_analytificationIncl.{u} _
    rw [hr]
    intro j
    fin_cases j
    exact hF
  obtain ⟨y, hy⟩ := hmem
  refine ⟨y, ?_, ?_⟩
  · change MvPolynomial.eval _ _ = 0
    rw [hy]
    exact hG
  · have h1 : ⇑(AnalyticSpace.proj.{u} n).toLRSHom.base z = w := by
      rw [base_proj_eq.{u}, hz]
      simp
    exact (congrArg (⇑(AnalyticSpace.proj.{u} n).toLRSHom.base) hy).trans h1

end

end ComplexAnalytic
