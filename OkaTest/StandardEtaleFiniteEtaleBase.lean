/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import OkaTest.StandardEtaleLocalIsoBase

/-!
# The `k ≥ 1` witness for the finite étale class, at a pair that inverts nothing

`ComplexAnalytic.isFiniteEtale_restrictHom_analytificationMap_etalePresHom`
(`Oka/Analytification/StandardEtaleFiniteEtaleBase.lean`) is stated at every `k`, and until this
file it had no instance at `k ≥ 1`. That file's own `## What is not here` says so and names the
obstacle:

> **No instance of the class below at any `k ≥ 1` pair.** … the reason is that the second
> hypothesis of the finiteness half — an open subset of `ℂ^n` avoiding the bad set — is a
> condition on the pair that nothing below bounds. **Whether that open subset is non-empty at any
> `k ≥ 1` pair is proved nowhere.**

It is provable at a pair this repository already owns, and the open subset is not merely non-empty:
it is **everything**. `ComplexAnalytic.sqSubOneTwoPair` (`OkaTest/StandardEtaleLocalIsoBase.lean`)
is `f = X² − 1`, `g = 2`; over a `ℂ`-algebra `2` is a unit, so `G` vanishes at no point of the
hypersurface at all and `ComplexAnalytic.hypersurfaceCommonZeroImage` is empty. `V` may then be
`⊤`, and `ComplexAnalytic.AnalyticSpace.isFiniteEtale_of_restrictHom_top`
(`Oka/AnalyticSpace/FiniteEtaleOver.lean`) takes the restriction off entirely.

## This does not touch the counterexample, and the reason it does not is the whole content

`Oka/Analytification/StandardEtaleFiniteEtaleBase.lean`'s `## What is not here` opens with **No
unrestricted `ComplexAnalytic.AnalyticSpace.IsFiniteEtale`, and there never will be: it is
false**, and that bullet is about the statement **quantified over pairs**. It stays false, and
`ComplexAnalytic.not_isFiniteEtale_condEtaleProj` (`OkaTest/StandardEtaleNotFinite.lean`) is its
witness. What is below is an unrestricted instance **at one pair**, and the reason it exists is
exactly that this pair inverts nothing: **the restriction comes off precisely where there is no
localisation to make it necessary.** A pair whose `g` is a non-unit is the case the counterexample
is about and nothing here reaches it.

## The two node pairs are the two extremes of the bad set, and they share their `f`

`OkaTest/StandardEtaleLocalIsoBase.lean` carries two witnesses of the local-isomorphism half over
the node, at two pairs with the same `f = X² − 1` and different `g`. The bad set separates them
completely:

* at `ComplexAnalytic.sqSubOnePair`, `g = X − 1`, and
  `ComplexAnalytic.hypersurfaceCommonZeroImage_sqSubOnePair` (`OkaTest/OpenBaseFiniteness.lean`)
  makes the bad set **all of `ℂ^n`** — so the only `V` the finiteness half admits is empty, and
  the theorem at the top of this file says nothing whatever at that pair;
* at `ComplexAnalytic.sqSubOneTwoPair`, `g = 2`, and
  `ComplexAnalytic.hypersurfaceCommonZeroImage_sqSubOneTwoPair` below makes it **empty** — so
  every `V` is admissible, including `⊤`.

**So the pair whose algebra is not the base is also the pair at which the restriction is
removable.** The sibling file's reason for having two witnesses — that
`ComplexAnalytic.sqSubOneRingEquiv` makes `ComplexAnalytic.sqSubOnePair`'s algebra the base — is a
statement about the algebra; this is a second and independent reason, about the bad set, and it
points the same way.

**What keeps the instance below from being a `k ≥ 1` instance of a vacuous statement is the bad
set and not the algebra**: it is empty, so `V = ⊤` is admissible and the restricted morphism is
the whole of the unrestricted one, and the two non-emptiness witnesses cited below —
`ComplexAnalytic.nonempty_analytification_etalePresentation_node` and
`ComplexAnalytic.nonempty_analytification_nodeG` — say the source and the base have a point. At the
other pair the bad set is all of `ℂ^n`, the only admissible `V` is empty, and an instance there
would be a statement about empty spaces. **Whether this cover is an isomorphism is decided
nowhere in this repository** — `OkaTest/StandardEtaleLocalIsoBase.lean`'s
`## What is not checked here` says of the `ComplexAnalytic.sqSubOneTwoPair` witness that proving
its cover to be anything other than the base is a separate statement nothing there attempts, and
this file's own `## What is not checked here` says it again — and no sentence here rests on it.
**The other pair is not in that position and this paragraph does not put it there**: that file's
`## Two pairs` heading calls the cheapest pair's cover an isomorphism, on the strength of
`ComplexAnalytic.sqSubOneRingEquiv`, which is the asymmetry the first sentence above turns on.

## Why the bad-set computation is here and not beside its mirror

`ComplexAnalytic.hypersurfaceCommonZeroImage_sqSubOnePair` is in `OkaTest/OpenBaseFiniteness.lean`
and the computation below is its mirror, so that file is where a reader will look for it. It
cannot be declared there: `ComplexAnalytic.sqSubOneTwoPair` is declared in
`OkaTest/StandardEtaleLocalIsoBase.lean`, which **imports** `OkaTest/OpenBaseFiniteness.lean`, so
the definition is downstream of the file the statement would go in. The alternative is to move the
definition, which would take a `StandardEtalePair` out of the module whose subject it is; the
placement below is the cheaper of the two and is not a preference.

**This module adds no import edge into the `Oka` library.** Its only `import` is
`OkaTest.StandardEtaleLocalIsoBase`, and every `Oka` module the statements below name —
`Oka.Analytification.StandardEtaleFiniteEtaleBase`,
`Oka.Analytification.StandardEtaleFinitenessBase` and `Oka.AnalyticSpace.FiniteEtaleOver` — is
already in that module's import closure at the commit this file is cut from.

## Neither statement is about an empty space, and neither re-proves it

`ComplexAnalytic.nonempty_analytification_etalePresentation_node`
(`OkaTest/StandardEtaleLocalIsoBase.lean`) exhibits the point `(0, 0, 1, 1/2)` of the source of
**this** witness — the same presentation, since the `G` is the same — and
`ComplexAnalytic.nonempty_analytification_nodeG` exhibits a point of the base. Both are cited and
neither is reproduced.

**The preimage subtlety does not arise here and would if the `V` were proper.**
`OkaTest/CondFiniteEtale.lean` records that `ComplexAnalytic.AnalyticSpace.restrictHom f V`
restricts the source to the **preimage** of `V`, so a non-empty `V` does not by itself say the
source of the restricted morphism is non-empty, and
`ComplexAnalytic.nonempty_restrict_preimage_condGoodOpen` is what closes that at the `k = 0`
witness. At `V = ⊤` the preimage is the whole source, and
`ComplexAnalytic.isFiniteEtale_analytificationMap_etalePresHom_node` is about the unrestricted
morphism in any case.

## Two elaboration facts, paid for once

* **`Opens.map_top` cannot be used to turn the open
  `(Opens.map (analytificationInclHom g).toLRSHom.base).obj ⊤` into `⊤`.** The two are at
  `Opens (ULift (Fin 2) → ℂ)` and at
  `Opens ↑(ComplexAnalytic.AnalyticSpace.complexAffineSpace 2)`, which are definitionally equal and
  not syntactically equal; `rw` fails with *"Did not find an occurrence of the pattern"* and the
  note that the target is not type-correct at `instances` transparency. `exact` closes the goal,
  the two being defeq — which is also why the statement below may be written with a bare `⊤`.
* **The same mismatch makes `rw [Set.compl_empty]` fail on the `hV` goal**, whose `∅` is at the
  affine space's type and whose `Set.univ` would be at `ULift (Fin n) → ℂ`. Rewriting at the bad
  set itself and finishing with `Set.notMem_empty` is what goes through. This is the coercion
  `Oka/Analytification/OpenBaseFiniteness.lean` already records at
  `ComplexAnalytic.hypersurfaceCommonZeroImage_parabola_nonempty`.

**No `rw` or `simp` below names a definition**, for the reason
`OkaTest/StandardEtaleLocalIsoBase.lean` gives at length: a delta-unfold plants the auto-generated
equation lemma in the module that does the unfolding rather than in the module that owns the
definition. The unfoldings of
`ComplexAnalytic.nodeEtaleF` and `ComplexAnalytic.nodeEtaleG` that the last two proofs need are
definitional and are done by `exact`, and `ComplexAnalytic.sqSubOneTwoPair` is reached through
`ComplexAnalytic.sqSubOneTwoPair_f` and `ComplexAnalytic.sqSubOneTwoPair_g`, which exist for
exactly that purpose.

## Main results

- `ComplexAnalytic.lastVarPolyEquiv_symm_sqSubOneTwoPair_f` and
  `ComplexAnalytic.lastVarPolyEquiv_symm_sqSubOneTwoPair_g`: **the pair's `f` and `g` in the
  multivariate vocabulary**, general in `n`, which is the identification the theorems below
  consume.
- `ComplexAnalytic.hypersurfaceCommonZeroImage_sqSubOneTwoPair`: **the bad set of this pair is
  empty**, general in `n` — the mirror of
  `ComplexAnalytic.hypersurfaceCommonZeroImage_sqSubOnePair`, which is `Set.univ` at the other
  node pair.
- `ComplexAnalytic.isFiniteEtale_restrictHom_analytificationMap_etalePresHom_node`: **the `k ≥ 1`
  instance of the class**, at the node and at `ComplexAnalytic.sqSubOneTwoPair`, over `⊤`.
- `ComplexAnalytic.isFiniteEtale_analytificationMap_etalePresHom_node`: **and the restriction
  comes off**, by `ComplexAnalytic.AnalyticSpace.isFiniteEtale_of_restrictHom_top`.

## What is not checked here

* **No claim that this cover is non-trivial, and none about how many sheets it has.**
  `ComplexAnalytic.sqSubOneTwoPair`'s algebra is `R[X]/(X² − 1)`, which is not the base;
  `OkaTest/StandardEtaleLocalIsoBase.lean`'s own `## What is not checked here` says in terms that
  nothing there proves the cover is anything other than the base, and nothing here proves it
  either. **What is below is that the class holds**, not that the cover is connected, not that it
  has two sheets, and not that it is or is not an isomorphism.
* **Nothing at `k ≥ 2`, and nothing uniform in `k`.** One presentation, one relation, one pair, as
  in the file this one imports.
* **Nothing about the composite with `ComplexAnalytic.analytificationInclHom`**, which is a
  different morphism and whose local-isomorphism half
  `Oka/Analytification/StandardEtaleLocalIso.lean` argues false for a base with a proper non-empty
  zero locus. The node is such a base; the
  argument is still not a theorem of this repository, here or anywhere.
* **No general statement about the size of `V`, and no second instance at which it is proper.** It
  remains a hypothesis on the pair `(F, G)` rather than a theorem, and **the bad set carries no
  `k` at all** — `ComplexAnalytic.hypersurfaceCommonZeroImage` is a function of `(F, G)` and of
  nothing else, so the computation below is a `k`-free statement and the `k` enters only where
  the class is instantiated. The bad set below is an extreme, as
  `ComplexAnalytic.hypersurfaceCommonZeroImage_one` is. **The only pair at which this class is
  instantiated with a `V` that is proper *and* non-empty is still the parabola**
  (`ComplexAnalytic.hypersurfaceCommonZeroImage_parabola`, instantiated by
  `OkaTest/CondFiniteEtale.lean`), and that instantiation is at `k = 0`; nothing here is a
  `k ≥ 1` counterpart of it.
* **No `OkaTest/Axioms/` guard and no `#print axioms`.** `OkaTest/Axioms/` guards declarations of
  the `Oka` library; every declaration below is in the test library, which is the rule
  `ComplexAnalytic.condPair` and `ComplexAnalytic.sqSubOnePair` are already unguarded under and
  the one `OkaTest/CondFiniteEtale.lean` states for its own contents.
* **Nothing in `Oka/Analytification/Hausdorff.lean` is instantiated.** That file's two
  covering-map corollaries are at `k = 0` and are about the **composite to `ℂ^n`**; what the
  theorems below would let be stated is the `k ≥ 1` counterpart **over `X^an`**, which is a
  different morphism, and stating it is a separate deliverable that this file does not start.
  **Its Hausdorff result is not in that position**: `ComplexAnalytic.t2Space_analytification` binds
  `{n k : ℕ}`, is declared above that file's `noncomputable section` and so outside the `Fin 0`
  block its two corollaries live in, and is about a space rather than a morphism — so it is at
  every `k` already, and is what would discharge the separation hypothesis of the `X^an`
  counterpart rather than something that counterpart owes. **The `ℂ^n`
  composite at this very pair is not a local isomorphism** —
  `ComplexAnalytic.not_isLocalIso_analytificationMap_etalePresHom_comp_node`
  (`OkaTest/StandardEtaleNotLocalIso.lean`), at the same
  `ComplexAnalytic.nodeEtaleF` and `ComplexAnalytic.nodeEtaleG` the instance below is at — so
  nothing below is a step towards a `k ≥ 1` corollary of that shape and no reader should take it
  for one.
-/

open MvPolynomial TopologicalSpace

universe u

namespace ComplexAnalytic

noncomputable section

variable {n : ℕ}

/-! ### The pair in the multivariate vocabulary -/

/-- **`ComplexAnalytic.sqSubOneTwoPair`'s `f = X² − 1` in the new variable**, general in `n`.

`ComplexAnalytic.lastVarPolyEquiv_symm_X` is the whole of it, and the `1` goes through as a
ring-hom image. At `n = 2` the right-hand side is `ComplexAnalytic.nodeEtaleF` by definition, which
is what lets the theorems below be stated at the node's own lifts. -/
theorem lastVarPolyEquiv_symm_sqSubOneTwoPair_f :
    (lastVarPolyEquiv.{u} n).symm (sqSubOneTwoPair (MvPolynomial (ULift.{u} (Fin n)) ℂ)).f
      = MvPolynomial.X (localisationVar.{u} n) ^ 2 - 1 := by
  rw [sqSubOneTwoPair_f]
  simp [lastVarPolyEquiv_symm_X]

/-- **`ComplexAnalytic.sqSubOneTwoPair`'s `g = 2` in the new variable**, general in `n`.

`map_ofNat` and nothing else, which is the same step
`ComplexAnalytic.isLocalIso_analytificationMap_etalePresHom_node` pays for on the other side of
`ComplexAnalytic.polyPresentedAlgebraEquiv`: a numeral is not carried by `simp` through these
equivalences. At `n = 2` the right-hand side is `ComplexAnalytic.nodeEtaleG` by definition. -/
theorem lastVarPolyEquiv_symm_sqSubOneTwoPair_g :
    (lastVarPolyEquiv.{u} n).symm (sqSubOneTwoPair (MvPolynomial (ULift.{u} (Fin n)) ℂ)).g
      = 2 := by
  rw [sqSubOneTwoPair_g]
  simp only [map_ofNat]

/-! ### The bad set is empty -/

/-- **The bad set of `ComplexAnalytic.sqSubOneTwoPair` is empty**, so the open subset of the base
that `Oka/Analytification/StandardEtaleFinitenessBase.lean`'s finiteness half asks for may be all
of `ℂ^n`.

`G = 2` is a unit of every `ℂ`-algebra, so it vanishes at no point of `ℂ^(n+1)` at all — the
hypersurface is not even looked at, and `F` is not read. That is the whole proof, and it is
`ComplexAnalytic.hypersurfaceCommonZeroImage_one`'s with `1` replaced by `2`.

**This is the mirror of `ComplexAnalytic.hypersurfaceCommonZeroImage_sqSubOnePair`**
(`OkaTest/OpenBaseFiniteness.lean`), which is `Set.univ` at the other node pair. The two pairs have
the same `f`, so the two computations differ only in `g` and land at the two extremes: the bad set
is a statement about what is inverted and not about the hypersurface. -/
theorem hypersurfaceCommonZeroImage_sqSubOneTwoPair :
    hypersurfaceCommonZeroImage.{u} (n := n)
      (sqSubOneTwoPair (MvPolynomial (ULift.{u} (Fin n)) ℂ)).f
      (sqSubOneTwoPair (MvPolynomial (ULift.{u} (Fin n)) ℂ)).g = ∅ := by
  refine Set.eq_empty_of_forall_notMem ?_
  rintro w ⟨y, hy, -⟩
  rw [lastVarPolyEquiv_symm_sqSubOneTwoPair_g.{u}] at hy
  simp only [map_ofNat] at hy
  norm_num at hy

/-! ### The two witnesses -/

/-- **The `k ≥ 1` instance of the finite étale class** —
`ComplexAnalytic.isFiniteEtale_restrictHom_analytificationMap_etalePresHom` at `k = 1`, over the
node `ComplexAnalytic.nodeG` and at `ComplexAnalytic.sqSubOneTwoPair`, which is the instance
`Oka/Analytification/StandardEtaleFiniteEtaleBase.lean` records as missing.

**The `V` is `⊤` and that is a theorem and not a convenience**:
`ComplexAnalytic.hypersurfaceCommonZeroImage_sqSubOneTwoPair` makes the bad set empty, so `⊤`
avoids it. The consumed theorem restricts over the open
`(Opens.map (analytificationInclHom nodeG).toLRSHom.base).obj ⊤` and the statement here is written
with a bare `⊤`; the two are definitionally equal and `rw`
cannot be used to move between them, for the reason the module docstring records.

The two lift hypotheses are `ComplexAnalytic.lastVarPolyEquiv_symm_sqSubOneTwoPair_f` and
`ComplexAnalytic.lastVarPolyEquiv_symm_sqSubOneTwoPair_g` followed by the same two steps
`ComplexAnalytic.isLocalIso_analytificationMap_etalePresHom_node` takes on the other side. -/
theorem isFiniteEtale_restrictHom_analytificationMap_etalePresHom_node :
    AnalyticSpace.IsFiniteEtale (AnalyticSpace.restrictHom
      (analytificationMap.{u} (etalePresHom.{u} nodeG.{u} nodeEtaleF.{u} nodeEtaleG.{u})) ⊤) := by
  have h := isFiniteEtale_restrictHom_analytificationMap_etalePresHom.{u} nodeG.{u}
    (sqSubOneTwoPair (MvPolynomial (ULift.{u} (Fin 2)) ℂ)).f
    (sqSubOneTwoPair (MvPolynomial (ULift.{u} (Fin 2)) ℂ)).g
    (sqSubOneTwoPair (MvPolynomial (ULift.{u} (Fin 2)) ℂ)).monic_f
    (sqSubOneTwoPair (PresentedAlgebra.{u} 2 1 nodeG.{u}))
    (by
      rw [lastVarPolyEquiv_symm_sqSubOneTwoPair_f.{u}]
      simp [sqSubOneTwoPair_f])
    (by
      rw [lastVarPolyEquiv_symm_sqSubOneTwoPair_g.{u}]
      simp only [sqSubOneTwoPair_g, map_ofNat])
    ⊤
    (by
      rw [hypersurfaceCommonZeroImage_sqSubOneTwoPair.{u}]
      exact fun x _ ↦ Set.notMem_empty x)
  rw [lastVarPolyEquiv_symm_sqSubOneTwoPair_f.{u},
    lastVarPolyEquiv_symm_sqSubOneTwoPair_g.{u}] at h
  exact h

/-- **And the restriction comes off**: the analytification of this standard étale morphism over the
node is finite étale, unrestricted.

One term, through `ComplexAnalytic.AnalyticSpace.isFiniteEtale_of_restrictHom_top`, which is the
same step `OkaTest/CondFiniteEtale.lean` takes in the other direction to say that the `k = 0`
morphism is **not** finite étale at `⊤`.

**This is not a counterexample to anything.** The unrestricted class quantified over pairs is
false and stays false — `ComplexAnalytic.not_isFiniteEtale_condEtaleProj` is the witness, at a
pair whose `g` is not a unit. Here `g = 2`, nothing is inverted, and the restriction was never
doing any work; that is the content of this theorem and not an exception to that one. -/
theorem isFiniteEtale_analytificationMap_etalePresHom_node :
    AnalyticSpace.IsFiniteEtale
      (analytificationMap.{u} (etalePresHom.{u} nodeG.{u} nodeEtaleF.{u} nodeEtaleG.{u})) :=
  AnalyticSpace.isFiniteEtale_of_restrictHom_top.{u} _
    isFiniteEtale_restrictHom_analytificationMap_etalePresHom_node.{u}

end

end ComplexAnalytic
