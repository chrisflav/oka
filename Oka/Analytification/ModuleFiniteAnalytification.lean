/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Analytification.HypersurfaceFinite
import Oka.Analytification.SurjectionFinite

/-!
# The analytification of a module-finite map of presented `ℂ`-algebras is finite

`Oka/Analytification/HypersurfaceFinite.lean` decomposed this statement into three obstructions
and discharged two of them; `Oka/Analytification/SurjectionFinite.lean` supplied the analytic half
of the third and said in terms what was left:

> What nothing states is the **construction** that produces such a surjection from a module-finite
> `ComplexAnalytic.PresHom` — the generators and the kernel — and that is a statement about
> presentations with no analysis in it.

**This file is that construction, and `ComplexAnalytic.isFinite_analytificationMap_of_finite` is
the theorem it closes.** A `ComplexAnalytic.PresHom` whose ring map is module-finite analytifies
to an `ComplexAnalytic.AnalyticSpace.IsFinite` morphism, with no monicity, no tower and no
surjection in its statement.

## The route, and the one thing it forces

Write `A = ℂ[x] ⧸ (g)` for the source presentation and `B = ℂ[y] ⧸ (g')` for the target, so that
the ring map goes `B ⟶ A` and `A` is a finite `B`-module. Pick module generators `a₁, …, a_m` of
`A` over `B`. Each is integral over `B` because `A` is module-finite over it, so each carries a
monic polynomial with coefficients in `B`; lift those coefficients to `ℂ[y]` — monically, which
is `Polynomial.lifts_and_natDegree_eq_and_monic` — and the `m` lifted polynomials are the input
`ComplexAnalytic.towerPresHom` takes. The tower is then a presented algebra in `n' + m` variables
which is finite over `B` by `ComplexAnalytic.isFinite_analytificationMap_towerPresHom`, and `A` is
a quotient of it.

**What that forces, and it is the decision this file had to take**: the quotient is taken inside
the tower's own polynomial ring, so what it presents is a presentation of `A` in `n' + m`
variables and **not** the given `g`. `ComplexAnalytic.isFinite_analytificationMap_ofRename_id` is
stated for a surjection in the *same* number of variables — the caveat
`Oka/Analytification/SurjectionFinite.lean` attaches to it — and that hypothesis is met here
exactly because the quotient is taken there. The price is that the theorem's own morphism has to
be transported back along `ComplexAnalytic.analytificationIsoOfPresHom`, which is why
`ComplexAnalytic.isFinite_analytificationMap_of_inv` is in this file: an isomorphism of
presentations analytifies to an isomorphism, and an isomorphism is finite.

So the morphism factors as **isomorphism, then surjection, then tower**, and the two right-hand
factors are `ComplexAnalytic.isFinite_analytificationMap_ofRename_id_comp_towerPresHom`.

## The evaluation, and why it is indexed by `ℕ` rather than by the stage

`ComplexAnalytic.towerVal` gives the value of *every* variable of *every* stage at once: it takes
a bare `N` and decides by comparing `i.down.1` with `n'`. That is not a convenience.
`ComplexAnalytic.localisationIncl`, `ComplexAnalytic.towerIncl` and `ComplexAnalytic.towerVar` all
preserve `.1` on the nose, so `towerVal` composed with any of them is **definitionally** the
value at the smaller stage, and `ComplexAnalytic.towerAeval_rename_localisationIncl` and
`ComplexAnalytic.towerAeval_rename_towerIncl` are `MvPolynomial.aeval_rename` followed by
`congr 1` with nothing left to prove. An indexing that split `ULift (Fin (n' + m))` as a sum
would make each of those a transport, and the tower is `m` of them deep.

**With that, the whole of the tower's ideal dying is one induction and one `sup_le`.**
`ComplexAnalytic.presentationIdeal_hypersurfacePresentation` splits the ideal at each stage into
the old relations renamed up and the one new polynomial;
`ComplexAnalytic.presentationIdeal_towerPresentation_le_ker` closes the first half by the
inductive hypothesis and the second by
`ComplexAnalytic.towerAeval_lastVarPolyEquiv_symm`, which is the only place the one-variable
reading of the last variable is unwound.

## The two identifications the assembly runs on

* `ComplexAnalytic.towerPresHom_toRingHom_mk`: **the tower's structure map is one renaming.**
  It sends the class of `p` to the class of `p` read in the tower's variables, by an induction in
  which each step is `ComplexAnalytic.PresHom.ofRename_toRingHom_mk` and
  `MvPolynomial.rename_rename`. Without it the composite `A ⟵ tower ⟵ B` cannot be compared with
  the given `ψ` on the variables of `g'`, which is what `ComplexAnalytic.PresHom.ext` reduces to
  through `Ideal.Quotient.ringHom_ext` and `MvPolynomial.ringHom_ext`.
* `ComplexAnalytic.exists_presentationIdeal_eq`: **every ideal of the polynomial ring is a
  presentation ideal**, because `MvPolynomial (ULift (Fin N)) ℂ` is Noetherian. This is what turns
  the kernel of the evaluation into a `ComplexAnalytic.Presentation`-shaped object at all, and it
  is nine lines: `IsNoetherian.noetherian` gives a `Finset`, `Finset.equivFin` indexes it, and the
  range of that indexing is the coercion of the `Finset`.

## What this file's declaration count is, and the two rows that are not declarations

`scripts/DumpOkaDecls.lean` reports **eighteen** rows for this module and it declares **sixteen**.
The two extras are `ComplexAnalytic.presentationIdeal_towerPresentation_le_ker.match_1_1` and
`ComplexAnalytic.towerPresHom_toRingHom_mk.match_1_1`, the match auxiliaries of the two structural
recursions on the number of stages — the same class
`Oka/Analytification/HypersurfaceFinite.lean` already carries for
`ComplexAnalytic.towerPresentation` and `ComplexAnalytic.isFinite_analytificationMap_towerPresHom`,
and unavoidable at that recursion. **No `.eq_1` is planted, and that is not automatic**: a first
draft of this file had four, one of them for
`ComplexAnalytic.hypersurfacePresHom`, which is *another file's* definition — the route
`Oka/Analytification/RefineDatumTransition.lean` records. Every unfolding here is a `change` to
the definition's body rather than a `rw` or a `simp` at its name, which is the rule
`ComplexAnalytic.isFinite_analytificationMap_towerPresHom` states for itself. It also costs less
in axioms: the three value lemmas come out with no `Classical.choice`.

## Main definitions

- `ComplexAnalytic.towerVal`: **the values of the tower's variables**, at every stage at once —
  the base's variables go to their images and the `i`-th adjoined variable goes to the `i`-th
  generator.
- `ComplexAnalytic.towerAeval`: the evaluation of the `N`-variable polynomial ring at those
  values.
- `ComplexAnalytic.towerIncl` and `ComplexAnalytic.towerVar`: **the base's variables and the
  adjoined ones**, inside the tower's `n' + m`.

## Main results

- `ComplexAnalytic.towerVal_self`, `ComplexAnalytic.towerVal_localisationVar` and
  `ComplexAnalytic.towerVal_towerVar`: **the values, read off at the three kinds of variable.**
- `ComplexAnalytic.towerAeval_rename_localisationIncl` and
  `ComplexAnalytic.towerAeval_rename_towerIncl`: **the evaluation is compatible with every
  inclusion of variables the tower uses.**
- `ComplexAnalytic.towerAeval_lastVarPolyEquiv_symm`: **evaluating a polynomial in `N + 1`
  variables, read as a one-variable polynomial over the first `N`, is `Polynomial.eval₂` at the
  value of the last variable.**
- `ComplexAnalytic.presentationIdeal_towerPresentation_le_ker`: **the tower's relations are killed
  by the evaluation**, as soon as the base's relations are and each adjoined polynomial vanishes
  at its own generator.
- `ComplexAnalytic.towerPresHom_toRingHom_mk`: **the tower's structure map is one renaming**, on
  classes.
- `ComplexAnalytic.exists_presentationIdeal_eq`: **every ideal of the polynomial ring is a
  presentation ideal.**
- `ComplexAnalytic.isFinite_analytificationMap_of_inv`: **an isomorphism of presentations
  analytifies to a finite morphism.**
- `ComplexAnalytic.isFinite_analytificationMap_ofRename_id_comp_towerPresHom`: **a presented
  algebra whose ideal contains a monic tower's is finite over the tower's base.**
- `ComplexAnalytic.isFinite_analytificationMap_of_finite`: **the analytification of a
  module-finite map of presented `ℂ`-algebras is finite.**

## What is not here

* **No converse, and nothing about the fibres.** Nothing says a finite analytification comes from
  a module-finite map, and nothing here counts a fibre or relates its cardinality to a degree —
  which is what the Riemann-existence line will want of a *covering* and is a different statement
  from finiteness.
* **Nothing about `ComplexAnalytic.AnalyticSpace.IsFiniteEtale` and nothing about the comparison
  functor.** This file supplies one input to the comparison of finite étale covers and touches
  neither the functor, nor degree preservation, nor full faithfulness.
* **No `AlgebraicGeometry.Scheme`.** The statement is at the presentation level for the reason
  `Oka/Analytification/Comparison.lean` gives in its own titled section, and building
  `Oka/Analytification/AffineCover.lean`'s `analytificationOfScheme` is a different and
  `{u}`-collapsing job.
* **The different-numbers-of-variables surjection is still unproved, and is still not needed.**
  `Oka/Analytification/SurjectionFinite.lean`'s caveat stands unweakened: what is proved there is
  the same-variables case, and the construction above produces exactly that case because the
  quotient is taken inside the tower's own polynomial ring. Nothing here is evidence about a
  surjection between presentations in different numbers of variables.
* **No canonical choice of tower.** `m`, the generators, the monic lifts and the presentation of
  the kernel are all chosen inside the proof and none of them is named by a definition; the
  theorem is an existence statement about the morphism it is handed and says nothing about how
  a *particular* tower relates to a *particular* presentation.
-/

open CategoryTheory Opposite AlgebraicGeometry Topology

universe u

namespace ComplexAnalytic

variable {n n' k k' : ℕ}

/-! ### The values of the tower's variables -/

section Values

variable {A : Type u} [CommRing A] [Algebra ℂ A] (b : ULift.{u} (Fin n') → A) (a : ℕ → A)

/-- **The values of the tower's variables**, at every stage at once: the first `n'` variables go
to `b`, the base's own images, and the variable numbered `n' + i` goes to `a i`, the `i`-th
adjoined generator.

The test is on `i.down.1` and the argument `N` is a bare natural number, so that this one
definition covers every stage of the tower. That is what makes
`ComplexAnalytic.towerAeval_rename_localisationIncl` and
`ComplexAnalytic.towerAeval_rename_towerIncl` hold with nothing to prove: every inclusion of
variables the tower uses preserves `.1`. -/
def towerVal (N : ℕ) (i : ULift.{u} (Fin N)) : A :=
  if h : i.down.1 < n' then b (ULift.up ⟨i.down.1, h⟩) else a (i.down.1 - n')

/-- The evaluation of the `N`-variable polynomial ring at `ComplexAnalytic.towerVal`. -/
noncomputable def towerAeval (N : ℕ) : MvPolynomial (ULift.{u} (Fin N)) ℂ →ₐ[ℂ] A :=
  MvPolynomial.aeval (towerVal b a N)

omit [CommRing A] [Algebra ℂ A] in
/-- The variable adjoined at the `i`-th stage takes the `i`-th generator as its value. -/
theorem towerVal_localisationVar (i : ℕ) :
    towerVal b a (n' + i + 1) (localisationVar.{u} (n' + i)) = a i := by
  change (if h : n' + i < n' then b (ULift.up ⟨n' + i, h⟩) else a (n' + i - n')) = a i
  rw [dif_neg (by omega)]
  congr 1
  omega

omit [CommRing A] [Algebra ℂ A] in
/-- The base's own variables take the base's own values. -/
theorem towerVal_self (j : ULift.{u} (Fin n')) : towerVal b a n' j = b j := by
  change (if h : j.down.1 < n' then b (ULift.up ⟨j.down.1, h⟩) else a (j.down.1 - n')) = b j
  rw [dif_pos j.down.2]

/-- **The evaluation is compatible with adjoining one variable.** `MvPolynomial.aeval_rename` and
then `congr 1`, which has nothing to prove because `ComplexAnalytic.localisationIncl` preserves
`.1` and `ComplexAnalytic.towerVal` reads nothing else. -/
theorem towerAeval_rename_localisationIncl (N : ℕ) (p : MvPolynomial (ULift.{u} (Fin N)) ℂ) :
    towerAeval b a (N + 1) (MvPolynomial.rename (localisationIncl.{u} N) p) =
      towerAeval b a N p := by
  change MvPolynomial.aeval (towerVal b a (N + 1))
    (MvPolynomial.rename (localisationIncl.{u} N) p) = MvPolynomial.aeval (towerVal b a N) p
  rw [MvPolynomial.aeval_rename]
  congr 1

/-- **Evaluating a polynomial in `N + 1` variables, read as a one-variable polynomial over the
first `N`, is `Polynomial.eval₂` at the value of the last variable.**

Both sides are ring maps out of `Polynomial (MvPolynomial (ULift (Fin N)) ℂ)`, so
`Polynomial.ringHom_ext` reduces the statement to the constants and to `Polynomial.X`, which are
`ComplexAnalytic.lastVarPolyEquiv_symm_C` and `ComplexAnalytic.lastVarPolyEquiv_symm_X`. Doing it
this way rather than by `MvPolynomial.ringHom_ext` on the left-hand ring avoids splitting an
arbitrary variable of `ULift (Fin (N + 1))` into the last one and the rest. -/
theorem towerAeval_lastVarPolyEquiv_symm (N : ℕ)
    (P : Polynomial (MvPolynomial (ULift.{u} (Fin N)) ℂ)) :
    towerAeval b a (N + 1) ((lastVarPolyEquiv.{u} N).symm P) =
      Polynomial.eval₂ (towerAeval b a N).toRingHom
        (towerVal b a (N + 1) (localisationVar.{u} N)) P := by
  have key : ((towerAeval b a (N + 1)).toRingHom.comp
      ((lastVarPolyEquiv.{u} N).symm.toAlgHom.toRingHom)) =
      Polynomial.eval₂RingHom (towerAeval b a N).toRingHom
        (towerVal b a (N + 1) (localisationVar.{u} N)) := by
    refine Polynomial.ringHom_ext (fun p ↦ ?_) ?_
    · change towerAeval b a (N + 1) ((lastVarPolyEquiv.{u} N).symm (Polynomial.C p)) = _
      rw [lastVarPolyEquiv_symm_C, towerAeval_rename_localisationIncl]
      simp
    · change towerAeval b a (N + 1) ((lastVarPolyEquiv.{u} N).symm Polynomial.X) = _
      rw [lastVarPolyEquiv_symm_X]
      change MvPolynomial.aeval (towerVal b a (N + 1)) (MvPolynomial.X _) = _
      simp
  exact RingHom.congr_fun key P

/-- **The tower's relations are killed by the evaluation**, as soon as the base's relations are
and each adjoined polynomial vanishes at its own generator.

The induction is on the number of stages and each step is one `sup_le`:
`ComplexAnalytic.presentationIdeal_hypersurfacePresentation` splits the stage's ideal into the
previous relations renamed up — the inductive hypothesis, through
`ComplexAnalytic.towerAeval_rename_localisationIncl` — and the span of the one new polynomial,
which is the hypothesis at `Fin.last`, through
`ComplexAnalytic.towerAeval_lastVarPolyEquiv_symm`. **No index is transported**: `n' + (m + 1)`
and `(n' + m) + 1` are the same numeral to `Lean`, and the stage's own variables are the previous
ones under `ComplexAnalytic.localisationIncl`. -/
theorem presentationIdeal_towerPresentation_le_ker
    (g' : Fin k' → MvPolynomial (ULift.{u} (Fin n')) ℂ)
    (hb : ∀ j, towerAeval b a n' (g' j) = 0) :
    ∀ (m : ℕ) (G : ∀ i : Fin m, Polynomial (MvPolynomial (ULift.{u} (Fin (n' + i.1))) ℂ))
      (_ : ∀ i : Fin m,
        Polynomial.eval₂ (towerAeval b a (n' + i.1)).toRingHom (a i.1) (G i) = 0),
      presentationIdeal.{u} (towerPresentation.{u} g' m G) ≤
        RingHom.ker (towerAeval b a (n' + m)).toRingHom
  | 0, _, _ => Ideal.span_le.2 (by rintro _ ⟨j, rfl⟩; exact hb j)
  | (m + 1), G, hG => by
      have ih := presentationIdeal_towerPresentation_le_ker g' hb m (fun i ↦ G i.castSucc)
        (fun i ↦ hG i.castSucc)
      change presentationIdeal.{u} (hypersurfacePresentation.{u}
        (towerPresentation.{u} g' m fun i ↦ G i.castSucc)
        ((lastVarPolyEquiv.{u} (n' + m)).symm (G (Fin.last m)))) ≤ _
      rw [presentationIdeal_hypersurfacePresentation]
      refine sup_le (Ideal.span_le.2 ?_) (Ideal.span_le.2 ?_)
      · rintro _ ⟨j, rfl⟩
        change towerAeval b a (n' + m + 1)
          (MvPolynomial.rename (localisationIncl.{u} (n' + m)) _) = 0
        rw [towerAeval_rename_localisationIncl]
        exact ih (Ideal.subset_span ⟨j, rfl⟩)
      · rintro _ rfl
        change towerAeval b a (n' + m + 1) _ = 0
        rw [towerAeval_lastVarPolyEquiv_symm, towerVal_localisationVar]
        exact hG (Fin.last m)

end Values

/-! ### The two blocks of the tower's variables -/

/-- The base's `n'` variables, read inside the tower's `n' + m`. -/
def towerIncl (n' m : ℕ) : ULift.{u} (Fin n') → ULift.{u} (Fin (n' + m)) :=
  fun j ↦ ULift.up ⟨j.down.1, by omega⟩

/-- The `i`-th variable adjoined by the tower, read inside the tower's `n' + m`. -/
def towerVar (n' m i : ℕ) (h : n' + i < n' + m) : ULift.{u} (Fin (n' + m)) :=
  ULift.up ⟨n' + i, h⟩

section Values

variable {A : Type u} [CommRing A] [Algebra ℂ A] (b : ULift.{u} (Fin n') → A) (a : ℕ → A)

omit [CommRing A] [Algebra ℂ A] in
/-- The `i`-th adjoined variable takes the `i`-th generator as its value. -/
theorem towerVal_towerVar (m i : ℕ) (h : n' + i < n' + m) :
    towerVal b a (n' + m) (towerVar.{u} n' m i h) = a i := by
  change (if hlt : n' + i < n' then b (ULift.up ⟨n' + i, hlt⟩) else a (n' + i - n')) = a i
  rw [dif_neg (by omega)]
  congr 1
  omega

/-- **The evaluation is compatible with the whole of the tower's inclusion of the base's
variables**, and for the same reason as one stage of it: `ComplexAnalytic.towerIncl` preserves
`.1`, so `congr 1` closes `MvPolynomial.aeval_rename`. -/
theorem towerAeval_rename_towerIncl (m : ℕ) (p : MvPolynomial (ULift.{u} (Fin n')) ℂ) :
    towerAeval b a (n' + m) (MvPolynomial.rename (towerIncl.{u} n' m) p) =
      towerAeval b a n' p := by
  change MvPolynomial.aeval (towerVal b a (n' + m))
    (MvPolynomial.rename (towerIncl.{u} n' m) p) = MvPolynomial.aeval (towerVal b a n') p
  rw [MvPolynomial.aeval_rename]
  congr 1

end Values

/-- **The tower's structure map is one renaming**, on classes: it sends the class of `p` to the
class of `p` read in the tower's variables.

The induction is on the number of stages. The base case is
`ComplexAnalytic.PresHom.id` and `MvPolynomial.rename_id_apply`; each step is
`ComplexAnalytic.hypersurfacePresHom`, which is a `ComplexAnalytic.PresHom.ofRename` at
`ComplexAnalytic.localisationIncl`, so `ComplexAnalytic.PresHom.ofRename_toRingHom_mk` and
`MvPolynomial.rename_rename` compose the two inclusions into `ComplexAnalytic.towerIncl` one
stage up — which is `rfl`, both being the identity on `.1`.

This is what lets the composite `A ⟵ tower ⟵ B` be compared with a given
`ComplexAnalytic.PresHom` on the variables of the base presentation, which is what
`ComplexAnalytic.PresHom.ext` reduces to through `Ideal.Quotient.ringHom_ext` and
`MvPolynomial.ringHom_ext`. -/
theorem towerPresHom_toRingHom_mk (g' : Fin k' → MvPolynomial (ULift.{u} (Fin n')) ℂ) :
    ∀ (m : ℕ) (G : ∀ i : Fin m, Polynomial (MvPolynomial (ULift.{u} (Fin (n' + i.1))) ℂ))
      (p : MvPolynomial (ULift.{u} (Fin n')) ℂ),
      (towerPresHom.{u} g' m G).toRingHom (Ideal.Quotient.mk (presentationIdeal.{u} g') p) =
        Ideal.Quotient.mk (presentationIdeal.{u} (towerPresentation.{u} g' m G))
          (MvPolynomial.rename (towerIncl.{u} n' m) p)
  | 0, _, p =>
      congrArg (Ideal.Quotient.mk (presentationIdeal.{u} g'))
        (MvPolynomial.rename_id_apply p).symm
  | (m + 1), G, p => by
      change (PresHom.comp.{u} (hypersurfacePresHom.{u} _ _)
        (towerPresHom.{u} g' m _)).toRingHom _ = _
      rw [PresHom.comp]
      change (hypersurfacePresHom.{u} _ _).toRingHom
        ((towerPresHom.{u} g' m fun i ↦ G i.castSucc).toRingHom _) = _
      rw [towerPresHom_toRingHom_mk g' m (fun i ↦ G i.castSucc) p]
      change Ideal.Quotient.mk _ (MvPolynomial.rename (localisationIncl.{u} (n' + m))
        (MvPolynomial.rename (towerIncl.{u} n' m) p)) = _
      rw [MvPolynomial.rename_rename]
      rfl

/-! ### Presentations of an ideal and of an isomorphism -/

/-- **Every ideal of the polynomial ring is a presentation ideal**, because
`MvPolynomial (ULift (Fin N)) ℂ` is Noetherian: `IsNoetherian.noetherian` gives a `Finset`
generating it, `Finset.equivFin` indexes that `Finset` by a `Fin`, and the range of the indexing
is the `Finset`'s coercion. -/
theorem exists_presentationIdeal_eq {N : ℕ} (I : Ideal (MvPolynomial (ULift.{u} (Fin N)) ℂ)) :
    ∃ (K : ℕ) (r : Fin K → MvPolynomial (ULift.{u} (Fin N)) ℂ), presentationIdeal.{u} r = I := by
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian I : I.FG)
  refine ⟨s.card, fun j ↦ (s.equivFin.symm j : MvPolynomial (ULift.{u} (Fin N)) ℂ), ?_⟩
  have hrange : Set.range (fun j ↦ (s.equivFin.symm j : MvPolynomial (ULift.{u} (Fin N)) ℂ)) =
      (↑s : Set (MvPolynomial (ULift.{u} (Fin N)) ℂ)) := by
    ext x
    exact ⟨by rintro ⟨j, rfl⟩; exact (s.equivFin.symm j).2,
      fun hx ↦ ⟨s.equivFin ⟨x, hx⟩, by simp⟩⟩
  rw [presentationIdeal, hrange]
  exact hs

variable {g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ}
  {g' : Fin k' → MvPolynomial (ULift.{u} (Fin n')) ℂ}

/-- **An isomorphism of presentations analytifies to a finite morphism.**

`ComplexAnalytic.analytificationIsoOfPresHom` makes the induced morphism the `hom` of an
isomorphism, and `ComplexAnalytic.AnalyticSpace.isFinite_of_isIso` is the rest. This is what
carries the general theorem back from the presentation the construction produces to the one it
was handed. -/
theorem isFinite_analytificationMap_of_inv (ψ : PresHom.{u} g g') (χ : PresHom.{u} g' g)
    (h₁ : ψ.toRingHom.comp χ.toRingHom = RingHom.id (PresentedAlgebra.{u} n k g))
    (h₂ : χ.toRingHom.comp ψ.toRingHom = RingHom.id (PresentedAlgebra.{u} n' k' g')) :
    AnalyticSpace.IsFinite (analytificationMap.{u} ψ) := by
  haveI : IsIso (analytificationMap.{u} ψ) :=
    (analytificationIsoOfPresHom.{u} ψ χ h₁ h₂).isIso_hom
  exact AnalyticSpace.isFinite_of_isIso _

/-- **A presented algebra whose ideal contains a monic tower's is finite over the tower's base.**

This is the join of the two halves of `Oka/Analytification/HypersurfaceFinite.lean`'s third
obstruction: `ComplexAnalytic.isFinite_analytificationMap_ofRename_id` for the surjection of the
tower onto the algebra, `ComplexAnalytic.isFinite_analytificationMap_towerPresHom` for the tower,
and `ComplexAnalytic.AnalyticSpace.isFinite_comp` between them. The surjection is in the *same*
number of variables — `n' + m`, the tower's — which is the form the caveat in
`Oka/Analytification/SurjectionFinite.lean` licenses. -/
theorem isFinite_analytificationMap_ofRename_id_comp_towerPresHom {K : ℕ} (m : ℕ)
    (G : ∀ i : Fin m, Polynomial (MvPolynomial (ULift.{u} (Fin (n' + i.1))) ℂ))
    (hG : ∀ i, (G i).Monic)
    (r : Fin K → MvPolynomial (ULift.{u} (Fin (n' + m))) ℂ)
    (h : ∀ j, MvPolynomial.rename (id : ULift.{u} (Fin (n' + m)) → ULift.{u} (Fin (n' + m)))
      (towerPresentation.{u} g' m G j) ∈ presentationIdeal.{u} r) :
    AnalyticSpace.IsFinite (analytificationMap.{u}
      ((PresHom.ofRename.{u} id h).comp (towerPresHom.{u} g' m G))) := by
  rw [analytificationMap_comp]
  haveI h1 := isFinite_analytificationMap_ofRename_id.{u} h
  haveI h2 := isFinite_analytificationMap_towerPresHom.{u} g' m G hG
  infer_instance

/-! ### The general theorem -/

/-- **The analytification of a module-finite map of presented `ℂ`-algebras is finite.**

The ring map `ComplexAnalytic.PresHom.toRingHom` of `ψ` goes `B ⟶ A` and the induced morphism goes
`A^an ⟶ B^an`, so *module-finite* is finiteness of the source over the target, which is what a
finite morphism of spaces asks.

The proof is the construction the section above describes, and every choice it makes is local to
it: `Module.Finite.fg_top` gives module generators, `Algebra.IsIntegral.of_finite` a monic
polynomial over `B` for each, `Polynomial.lifts_and_natDegree_eq_and_monic` a *monic* lift of each
to `ℂ[y]` — no `Nontrivial` hypothesis, which matters because a presented algebra may be the zero
ring — and `ComplexAnalytic.exists_presentationIdeal_eq` a presentation of the kernel of the
resulting evaluation. That the evaluation is onto is the spanning statement read through
`Submodule.mem_span_range_iff_exists_fun`, with the coefficients lifted to `ℂ[y]` and the
generators supplied by `ComplexAnalytic.towerVar`.

`ComplexAnalytic.towerPresHom_toRingHom_mk` is what identifies the composite with `ψ`, on the
classes of the base's variables; the two are then equal by `ComplexAnalytic.PresHom.ext` because
both fix the constants. -/
theorem isFinite_analytificationMap_of_finite (ψ : PresHom.{u} g g')
    (hψ : ψ.toRingHom.Finite) :
    AnalyticSpace.IsFinite (analytificationMap.{u} ψ) := by
  classical
  letI := ψ.toRingHom.toAlgebra
  haveI : Module.Finite (PresentedAlgebra.{u} n' k' g') (PresentedAlgebra.{u} n k g) := hψ
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top :
    (⊤ : Submodule (PresentedAlgebra.{u} n' k' g') (PresentedAlgebra.{u} n k g)).FG)
  set m := s.card
  set a₀ : Fin m → PresentedAlgebra.{u} n k g :=
    fun i ↦ (s.equivFin.symm i : PresentedAlgebra.{u} n k g) with ha₀
  set a : ℕ → PresentedAlgebra.{u} n k g := fun t ↦ if h : t < m then a₀ ⟨t, h⟩ else 0 with ha
  set b : ULift.{u} (Fin n') → PresentedAlgebra.{u} n k g :=
    fun j ↦ ψ.toRingHom (Ideal.Quotient.mk (presentationIdeal.{u} g') (MvPolynomial.X j)) with hbdef
  have hbase : (towerAeval b a n').toRingHom =
      ψ.toRingHom.comp (Ideal.Quotient.mk (presentationIdeal.{u} g')) := by
    refine MvPolynomial.ringHom_ext (fun c ↦ ?_) (fun i ↦ ?_)
    · change towerAeval b a n' (MvPolynomial.C c) = _
      have hc : ψ.toRingHom (presentedAlgebraMap.{u} g' c) = presentedAlgebraMap.{u} g c :=
        RingHom.congr_fun ψ.commutes c
      change _ = ψ.toRingHom (presentedAlgebraMap.{u} g' c)
      rw [hc]
      change MvPolynomial.aeval (towerVal b a n') (MvPolynomial.C c) = _
      rw [MvPolynomial.aeval_C]
      rfl
    · change MvPolynomial.aeval (towerVal b a n') (MvPolynomial.X i) = _
      rw [MvPolynomial.aeval_X, towerVal_self]
      exact congrFun hbdef i
  have hbaseapp : ∀ p, towerAeval b a n' p =
      ψ.toRingHom (Ideal.Quotient.mk (presentationIdeal.{u} g') p) :=
    fun p ↦ RingHom.congr_fun hbase p
  have hb : ∀ j, towerAeval b a n' (g' j) = 0 := by
    intro j
    have hzero : Ideal.Quotient.mk (presentationIdeal.{u} g') (g' j) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨j, rfl⟩)
    rw [hbaseapp, hzero, map_zero]
  haveI : Algebra.IsIntegral (PresentedAlgebra.{u} n' k' g') (PresentedAlgebra.{u} n k g) :=
    Algebra.IsIntegral.of_finite _ _
  have hint : ∀ i : Fin m, ∃ Q : Polynomial (MvPolynomial (ULift.{u} (Fin n')) ℂ),
      Q.Monic ∧ Polynomial.eval₂ (towerAeval b a n').toRingHom (a₀ i) Q = 0 := by
    intro i
    obtain ⟨p, hpm, hpr⟩ := Algebra.IsIntegral.isIntegral
      (R := PresentedAlgebra.{u} n' k' g') (a₀ i)
    obtain ⟨Q, hQmap, _, hQm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
      (Polynomial.mem_lifts_of_surjective Ideal.Quotient.mk_surjective p) hpm
    refine ⟨Q, hQm, ?_⟩
    have hpr' : Polynomial.eval₂ ψ.toRingHom (a₀ i) p = 0 := by
      rw [show ψ.toRingHom = algebraMap (PresentedAlgebra.{u} n' k' g')
        (PresentedAlgebra.{u} n k g) from (RingHom.algebraMap_toAlgebra _).symm,
        ← Polynomial.aeval_def]
      exact hpr
    rw [hbase, ← Polynomial.eval₂_map, hQmap]
    exact hpr'
  choose Q hQm hQr using hint
  set Q' : ℕ → Polynomial (MvPolynomial (ULift.{u} (Fin n')) ℂ) :=
    fun t ↦ if h : t < m then Q ⟨t, h⟩ else 1 with hQ'
  set G : ∀ i : Fin m, Polynomial (MvPolynomial (ULift.{u} (Fin (n' + i.1))) ℂ) :=
    fun i ↦ (Q' i.1).map (MvPolynomial.rename (towerIncl.{u} n' i.1) :
      MvPolynomial (ULift.{u} (Fin n')) ℂ →ₐ[ℂ] _).toRingHom with hG
  have hGm : ∀ i, (G i).Monic := by
    intro i
    refine Polynomial.Monic.map _ ?_
    simp only [hQ', dif_pos i.2]
    exact hQm _
  have hGr : ∀ i : Fin m,
      Polynomial.eval₂ (towerAeval b a (n' + i.1)).toRingHom (a i.1) (G i) = 0 := by
    intro i
    have hcomp : (towerAeval b a (n' + i.1)).toRingHom.comp
        (MvPolynomial.rename (towerIncl.{u} n' i.1) :
          MvPolynomial (ULift.{u} (Fin n')) ℂ →ₐ[ℂ] _).toRingHom =
        (towerAeval b a n').toRingHom :=
      RingHom.ext fun p ↦ towerAeval_rename_towerIncl b a i.1 p
    rw [hG, Polynomial.eval₂_map, hcomp]
    have hai : a i.1 = a₀ i := by simp [ha, dif_pos i.2]
    have hQi : Q' i.1 = Q i := by simp [hQ', dif_pos i.2]
    rw [hai, hQi]
    exact hQr i
  have hker := presentationIdeal_towerPresentation_le_ker b a g' hb m G hGr
  have hsurj : Function.Surjective (towerAeval b a (n' + m)) := by
    intro x
    have hx : x ∈ Submodule.span (PresentedAlgebra.{u} n' k' g') (Set.range a₀) := by
      have hrange : Set.range a₀ = (↑s : Set (PresentedAlgebra.{u} n k g)) := by
        ext y
        exact ⟨by rintro ⟨j, rfl⟩; exact (s.equivFin.symm j).2,
          fun hy ↦ ⟨s.equivFin ⟨y, hy⟩, by simp [ha₀]⟩⟩
      rw [hrange, hs]
      trivial
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hx
    choose P hP using fun i : Fin m ↦ Ideal.Quotient.mk_surjective (I := presentationIdeal.{u} g')
      (c i)
    refine ⟨∑ i : Fin m, MvPolynomial.rename (towerIncl.{u} n' m) (P i) *
      MvPolynomial.X (towerVar.{u} n' m i.1 (by omega)), ?_⟩
    rw [map_sum, ← hc]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_mul, towerAeval_rename_towerIncl, hbaseapp, hP i]
    have hval : towerAeval b a (n' + m)
        (MvPolynomial.X (towerVar.{u} n' m i.1 (by omega))) = a₀ i := by
      change MvPolynomial.aeval (towerVal b a (n' + m))
        (MvPolynomial.X (towerVar.{u} n' m i.1 (by omega))) = a₀ i
      rw [MvPolynomial.aeval_X, towerVal_towerVar]
      simp [ha, dif_pos i.2]
    rw [hval, Algebra.smul_def, RingHom.algebraMap_toAlgebra]
  obtain ⟨K, r, hr⟩ := exists_presentationIdeal_eq.{u}
    (RingHom.ker (towerAeval b a (n' + m)).toRingHom)
  have hrmem : ∀ j, MvPolynomial.rename
      (id : ULift.{u} (Fin (n' + m)) → ULift.{u} (Fin (n' + m)))
      (towerPresentation.{u} g' m G j) ∈ presentationIdeal.{u} r := by
    intro j
    rw [hr, MvPolynomial.rename_id_apply]
    exact hker (Ideal.subset_span ⟨j, rfl⟩)
  set e : PresentedAlgebra.{u} (n' + m) K r ≃+* PresentedAlgebra.{u} n k g :=
    (Ideal.quotEquivOfEq hr).trans (RingHom.quotientKerEquivOfSurjective hsurj)
  have hemk : ∀ p, e (Ideal.Quotient.mk (presentationIdeal.{u} r) p) =
      towerAeval b a (n' + m) p := fun _ ↦ rfl
  have hcommα : (e : PresentedAlgebra.{u} (n' + m) K r →+* PresentedAlgebra.{u} n k g).comp
      (presentedAlgebraMap.{u} r) = presentedAlgebraMap.{u} g := by
    refine RingHom.ext fun c ↦ ?_
    change e (Ideal.Quotient.mk (presentationIdeal.{u} r) (MvPolynomial.C c)) = _
    rw [hemk]
    change MvPolynomial.aeval (towerVal b a (n' + m)) (MvPolynomial.C c) = _
    rw [MvPolynomial.aeval_C]
    rfl
  set α : PresHom.{u} g r := ⟨e.toRingHom, hcommα⟩
  have hcommβ : (e.symm : PresentedAlgebra.{u} n k g →+* PresentedAlgebra.{u} (n' + m) K r).comp
      (presentedAlgebraMap.{u} g) = presentedAlgebraMap.{u} r := by
    refine RingHom.ext fun c ↦ ?_
    change e.symm (presentedAlgebraMap.{u} g c) = presentedAlgebraMap.{u} r c
    have hec : e (presentedAlgebraMap.{u} r c) = presentedAlgebraMap.{u} g c :=
      RingHom.congr_fun hcommα c
    rw [← hec, e.symm_apply_apply]
  set β : PresHom.{u} r g := ⟨e.symm.toRingHom, hcommβ⟩
  have h₁ : α.toRingHom.comp β.toRingHom = RingHom.id (PresentedAlgebra.{u} n k g) :=
    RingHom.ext fun x ↦ e.apply_symm_apply x
  have h₂ : β.toRingHom.comp α.toRingHom = RingHom.id (PresentedAlgebra.{u} (n' + m) K r) :=
    RingHom.ext fun x ↦ e.symm_apply_apply x
  set χ : PresHom.{u} r g' :=
    (PresHom.ofRename.{u} id hrmem).comp (towerPresHom.{u} g' m G) with hχ
  have hcomp : α.comp χ = ψ := by
    refine PresHom.ext (Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun c ↦ ?_)
      (fun i ↦ ?_)))
    · have h1 : (α.comp χ).toRingHom (presentedAlgebraMap.{u} g' c) =
          presentedAlgebraMap.{u} g c := RingHom.congr_fun (α.comp χ).commutes c
      have h2 : ψ.toRingHom (presentedAlgebraMap.{u} g' c) = presentedAlgebraMap.{u} g c :=
        RingHom.congr_fun ψ.commutes c
      change (α.comp χ).toRingHom (presentedAlgebraMap.{u} g' c) =
        ψ.toRingHom (presentedAlgebraMap.{u} g' c)
      rw [h1, h2]
    · change (α.comp χ).toRingHom (Ideal.Quotient.mk (presentationIdeal.{u} g')
        (MvPolynomial.X i)) = _
      change α.toRingHom (χ.toRingHom _) = _
      rw [hχ]
      change α.toRingHom ((PresHom.ofRename.{u} id hrmem).toRingHom
        ((towerPresHom.{u} g' m G).toRingHom _)) = _
      rw [towerPresHom_toRingHom_mk, PresHom.ofRename_toRingHom_mk, MvPolynomial.rename_id_apply]
      change e (Ideal.Quotient.mk (presentationIdeal.{u} r) _) = _
      rw [hemk, towerAeval_rename_towerIncl]
      exact hbaseapp (MvPolynomial.X i)
  have hsplit : analytificationMap.{u} ψ =
      analytificationMap.{u} α ≫ analytificationMap.{u} χ := by
    rw [← analytificationMap_comp, hcomp]
  rw [hsplit]
  haveI := isFinite_analytificationMap_of_inv.{u} α β h₁ h₂
  haveI := isFinite_analytificationMap_ofRename_id_comp_towerPresHom.{u} m G hGm r hrmem
  infer_instance

end ComplexAnalytic
