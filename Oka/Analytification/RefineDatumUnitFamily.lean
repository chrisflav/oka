/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Analytification.RefineDatumCocycle

/-!
# A refined cover datum at a family that is not `1`: both adopted conditions, at an injective `σ`

`Oka/Analytification/RefineDatumWitness.lean` builds a refined cover datum for every cover datum
and every index map by taking the refining family constantly `1`, and its own `## What is not
here` said what that leaves — the sentence this file retires, quoted here and narrowed there:

> **No witness at a refining family that is not a unit**, which is what a *proper* refinement at a
> non-constant `σ` would be. … the one condition that would not come free is `RefineDatumRangeEq`,
> which asks the transition's image to land in `D(fam c)` and has no free half at any file on this
> line.

**The first half of that is the deliverable and the second half is not what blocks it.** Both
conditions `Oka/Analytification/RefineDatumGlueData.lean` adopts are free at a refining family
this file leaves arbitrary, and what buys them is not the family at all: it is that the index map
does not collapse two indices.

## `RefineDatumRangeEq` is vacuous at an injective `σ`, and that is its binders and not its content

Everything four files say about that condition is true — its target belongs to the caller's
refining family, no half of it is free, and the original cover's geometry bears on it not at all.
None of it is about what the condition is *quantified over*:

```
∀ a b c : B, a ≠ b → a ≠ c → b ≠ c → σ a ≠ σ b → ∀ hbc : σ b = σ c, …
```

It asks for `b ≠ c` **and** `σ b = σ c`. At an injective `σ` there is no such pair, so
`ComplexAnalytic.refineDatumRangeEq_of_injective` closes it in one line, for every cover datum,
every `q`, every choice of `rr` and `uu`, and every refining family. **The condition with no free
half is free wherever the index map is injective** — which is the shape a refinement of a cover by
itself has, `B = J` and `σ = id`, and is the shape taxis #1107's third deliverable is about.

This does not weaken `Oka/Analytification/RefineDatumGlueData.lean`'s
`ComplexAnalytic.refineDatumHrange_iff`: the pair of conditions is still exactly what the refined
range law asks, and what is shown here is that one of the two is satisfiable for free at a class
of index maps, not that the law is weaker than the pair.

## And `RefineDatumRangeCross` is free at the caller's own `q`, for *every* family

`ComplexAnalytic.refineDatumOneRangeCross` discharges the first condition at
`q = poly ∘ σ` with the family fixed at `1`. **The three free halves it calls are general in the
family** — `fam` is a `variable` in each of
`ComplexAnalytic.range_refineDatumTransitionHom_localisationProj_subset_of_eq_ab`,
`..._of_eq_ac` (`Oka/Analytification/RefineDatumRange.lean`) and
`ComplexAnalytic.range_refineDatumTransitionHom_localisationProj_subset`
(`Oka/Analytification/RefineDatumTransition.lean`), and none of them constrains it — so the same
three-way split proves `ComplexAnalytic.refineDatumRangeCross_poly` at an arbitrary one.
`refineDatumOneRangeCross` is its instance at `fam = fun _ ↦ 1`; that declaration is left as it
stands, since a witness file's readable special case is worth its three lines.

**So the trivial family in `Oka/Analytification/RefineDatumWitness.lean` is doing work for
`RefineDatumRangeEq` alone**, exactly as that file says, and at an injective `σ` there is no work
left for it to do.

## What a proper witness still owes, and it is the choice

With both range conditions free, a caller owes only the two cross-member equations, and
`ComplexAnalytic.exists_refineDatumCross_of_isUnit`
(`Oka/Analytification/CrossMemberDatumGlue.lean`) supplies them from four units. At `q = poly ∘ σ`
two of the four are `ComplexAnalytic.isUnit_mk_rename_localisationIncl` verbatim and the other two
are a hypothesis on the family:

> `fam a` is a unit of the localisation of the member `σ a` at `f_{σa σb}`,

which geometrically is `D(fam a) ⊇ D(f_{σa σb})` — **the refined member contains the whole
overlap**. That is a real restriction and it is the one this file does not remove; what it is not
is the range condition four files named.

**The hypothesis is asked for only where `σ a ≠ σ b`, and the two implications inside
`ComplexAnalytic.exists_refineDatumCross_unitFam`'s existential are what keeps the choice total
without a `dite`.** `rr` and `uu` are total families and a hypothesis restricted to `σ a ≠ σ b`
cannot produce a value at a collapsing pair; putting the restriction on the two *conclusions*
lets the equal branch answer `⟨0, 1, …⟩` and lets the two projections below take the `σ a ≠ σ b`
that a refined datum asks them at anyway. The `dite` form was not attempted and nothing here says
it fails.

## Main definitions

- `ComplexAnalytic.refineDatumUnitFamR` and `ComplexAnalytic.refineDatumUnitFamU`: **the caller's
  `r` and `u` at a family that is a unit on each overlap**, chosen from the criterion above.
- `ComplexAnalytic.refineDatumUnitFamGlueData` and
  `ComplexAnalytic.refineDatumUnitFamAnalytification`: **the glue data and the analytic space of a
  refinement at an injective `σ` and such a family**, taking the original datum's three laws and
  nothing else.

## Main results

- `ComplexAnalytic.refineDatumRangeEq_of_injective`: **the second adopted condition is vacuous at
  an injective index map**, for every family, every cutting polynomial and every choice.
- `ComplexAnalytic.refineDatumRangeCross_poly`: **the first adopted condition at the original
  datum's own cutting polynomial, for every family** — the generalisation of
  `ComplexAnalytic.refineDatumOneRangeCross` off the trivial one.
- `ComplexAnalytic.exists_refineDatumCross_unitFam`: **both cross-member equations have a
  solution at every ordered pair** as soon as the family is a unit on each overlap.
- `ComplexAnalytic.refineDatumUnitFamCrossEq` and
  `ComplexAnalytic.refineDatumUnitFamCrossUnit`: the two equations, at the pairs the datum asks
  them at.
- `ComplexAnalytic.refineDatumUnitFamAnalytification_toLocallyRingedSpace`: **the space is that
  glue data's gluing**, with no transport — the relation without which the two definitions above
  are two well-typed objects and every statement about the gluing says nothing about the space.

## What is not here

* **A family that is not a unit *on the overlap* is still out of reach.**
  `ComplexAnalytic.exists_refineDatumCross_unitFam`'s `hfam` is a genuine hypothesis and nothing
  here discharges it; a refinement that cuts *into* an overlap rather than containing it meets
  none of this, and no file on this line says what such a refinement would need.
* **`RefineDatumRangeCross` is not discharged at a general `q`**, only at the original datum's own
  `poly ∘ σ`, as in `Oka/Analytification/RefineDatumWitness.lean`. A caller who names a different
  cutting polynomial gets nothing from this file.
* **Nothing about a non-injective `σ`.** At an index map that collapses two indices
  `RefineDatumRangeEq` recovers all of its content, and the only thing that meets it there is the
  trivial family — `ComplexAnalytic.refineDatumOneRangeEq`, which is the whole of what that
  witness's `fam ≡ 1` is for.
* **Nothing about `ComplexAnalytic.exists_refineDatumCross`.** Whether the `q` it produces
  satisfies either condition is untouched here in both directions; this file, like the witness
  file, exhibits `r` and `u` rather than asking for them.
* **No statement that the refined space is the original one**, in either direction. **This bullet
  also said there is *"no morphism between the two gluings"*, and that half is retired**: the space
  above is `ComplexAnalytic.refineDatumAnalytificationOfLaws` at particular arguments, so
  `ComplexAnalytic.refineDatumToBase` (`Oka/Analytification/RefineDatumToBase.lean`) applies to it
  with no work — down to the original cover, in that direction only, and it is not claimed to be an
  isomorphism anywhere. What *is* known about the refined space when the caller's `q` is the
  datum's own `poly` and the family is that same polynomial is that it is **one of its own refined
  members**: every refined overlap is then the whole refined member and
  `ComplexAnalytic.isoCoverGlued` (`Oka/Analytification/CoverGlueTop.lean`) applies. That is a fact
  about those inputs and not about this construction, which says nothing about the overlaps at a
  family it is not given.
* **No scheme, no `admissible`, and no comparison functor**, as in the files this one sits beside.
-/

open CategoryTheory MvPolynomial AlgebraicGeometry

universe u

namespace ComplexAnalytic

noncomputable section

variable {J B : Type u} (obj : J → Presentation.{u})
  (poly : ∀ i : J, J → MvPolynomial (ULift.{u} (Fin (obj i).n)) ℂ)
  (σ : B → J)
  (fam : ∀ b : B, MvPolynomial (ULift.{u} (Fin (obj (σ b)).n)) ℂ)
  (q : ∀ a : B, B → MvPolynomial (ULift.{u} (Fin (obj (σ a)).n)) ℂ)
  (glue : ∀ i j : J, coverOverlap.{u} obj poly i j ≅ coverOverlap.{u} obj poly j i)
  (rr : ∀ _ b : B, MvPolynomial (ULift.{u} (Fin ((obj (σ b)).n + 1))) ℂ)
  (uu : ∀ a b : B, (PresentedAlgebra.{u} ((obj (σ b)).n + 1) ((obj (σ b)).k + 1)
    (localisationPresentation.{u} (obj (σ b)).g (poly (σ b) (σ a))))ˣ)
  (he : ∀ a b : B, ∀ _ : σ a ≠ σ b,
    RefineDatumCrossEq.{u} obj σ fam poly q glue a b (rr a b))
  (hu : ∀ a b : B, ∀ _ : σ a ≠ σ b,
    RefineDatumCrossUnit.{u} obj σ fam poly q a b (rr a b) (uu a b))

/-! ### The condition with no free half, where the index map does not collapse -/

/-- **`ComplexAnalytic.RefineDatumRangeEq` is vacuous at an injective index map.**

The condition is quantified over triples with `b ≠ c` **and** `σ b = σ c`, and an injective `σ`
admits no such pair. Nothing about the containment it asks for is used, so this holds for every
cover datum, every cutting polynomial, every refining family and every choice of `rr` and `uu` —
which is why it is stated here rather than at any particular one of them.

**This is not a weakening of `ComplexAnalytic.refineDatumHrange_iff`.** That theorem says the two
conditions are exactly what the refined range law asks, and it stands: what is shown here is that
one of the pair is satisfiable for free at a class of index maps, not that the law needs less than
the pair. -/
theorem refineDatumRangeEq_of_injective (hσ : Function.Injective σ) :
    RefineDatumRangeEq.{u} obj poly σ fam q glue rr uu he hu :=
  fun _ _ _ _ _ hbc _ h ↦ absurd (hσ h) hbc

end

noncomputable section

variable {J B : Type u} (obj : J → Presentation.{u})
  (poly : ∀ i : J, J → MvPolynomial (ULift.{u} (Fin (obj i).n)) ℂ)
  (σ : B → J)
  (fam : ∀ b : B, MvPolynomial (ULift.{u} (Fin (obj (σ b)).n)) ℂ)
  (glue : ∀ i j : J, coverOverlap.{u} obj poly i j ≅ coverOverlap.{u} obj poly j i)
  (rr : ∀ _ b : B, MvPolynomial (ULift.{u} (Fin ((obj (σ b)).n + 1))) ℂ)
  (uu : ∀ a b : B, (PresentedAlgebra.{u} ((obj (σ b)).n + 1) ((obj (σ b)).k + 1)
    (localisationPresentation.{u} (obj (σ b)).g (poly (σ b) (σ a))))ˣ)
  (he : ∀ a b : B, ∀ _ : σ a ≠ σ b,
    RefineDatumCrossEq.{u} obj σ fam poly (fun x y ↦ poly (σ x) (σ y)) glue a b (rr a b))
  (hu : ∀ a b : B, ∀ _ : σ a ≠ σ b,
    RefineDatumCrossUnit.{u} obj σ fam poly (fun x y ↦ poly (σ x) (σ y)) a b (rr a b) (uu a b))

/-! ### The other condition, at the original datum's own cutting polynomial -/

/-- **`ComplexAnalytic.RefineDatumRangeCross` holds at `q = poly ∘ σ`, for every refining
family.**

At that `q` the condition's target `D(q b c)` is `ComplexAnalytic.coverOpen obj poly (σ b) (σ c)`,
which is the open the three free halves land in — and each of the three is general in the family,
so nothing here is special to `1`. The split is on `σ a` against `σ b` and `σ c`, and the fourth
branch is absent because `σ a = σ b` with `σ a = σ c` forces the `σ b = σ c` the condition
excludes. Only the third branch reads the original datum's own `hrange`.

**`ComplexAnalytic.refineDatumOneRangeCross` is this at `fam = fun _ ↦ 1`** and is deliberately
left standing: a witness file's readable special case is worth its three lines, and rewriting it
to call this one would put a `def`-level change into a file this one does not otherwise touch. -/
theorem refineDatumRangeCross_poly
    (hrange : ∀ i j k : J, i ≠ j → i ≠ k → j ≠ k →
      Set.range (coverTripleIncl.{u} obj poly i j k ≫
          coverTransitionHom.{u} obj poly glue i j).base ⊆
        (coverOpen.{u} obj poly j k : Set (coverSpace.{u} obj j))) :
    RefineDatumRangeCross.{u} obj poly σ fam (fun x y ↦ poly (σ x) (σ y)) glue rr uu he hu := by
  intro a b c _ _ _ hbc
  by_cases hab : σ a = σ b
  · exact range_refineDatumTransitionHom_localisationProj_subset_of_eq_ab.{u} obj poly σ
      fam (fun x y ↦ poly (σ x) (σ y)) glue rr uu he hu hab fun e ↦ hbc (hab ▸ e)
  · by_cases hac : σ a = σ c
    · exact range_refineDatumTransitionHom_localisationProj_subset_of_eq_ac.{u} obj poly σ
        fam (fun x y ↦ poly (σ x) (σ y)) glue rr uu he hu hab hac
    · exact range_refineDatumTransitionHom_localisationProj_subset.{u} obj poly σ fam
        (fun x y ↦ poly (σ x) (σ y)) glue rr uu hrange he hu hab hac hbc

end

noncomputable section

variable {J B : Type u} (obj : J → Presentation.{u})
  (poly : ∀ i : J, J → MvPolynomial (ULift.{u} (Fin (obj i).n)) ℂ)
  (σ : B → J)
  (fam : ∀ b : B, MvPolynomial (ULift.{u} (Fin (obj (σ b)).n)) ℂ)
  (glue : ∀ i j : J, coverOverlap.{u} obj poly i j ≅ coverOverlap.{u} obj poly j i)
  (hfam : ∀ a b : B, σ a ≠ σ b → IsUnit (Ideal.Quotient.mk (presentationIdeal.{u}
    (localisationPresentation.{u} (obj (σ a)).g (poly (σ a) (σ b))))
    (MvPolynomial.rename (localisationIncl.{u} (obj (σ a)).n) (fam a))))

/-! ### The choice, at a family that is a unit on each overlap -/

include hfam in
/-- **Both cross-member equations have a solution at every ordered pair**, for the refinement
whose cutting polynomial is the original datum's own and whose family is a unit on each overlap.

`ComplexAnalytic.exists_refineDatumCross_of_isUnit` at four units: two of them are
`ComplexAnalytic.isUnit_mk_rename_localisationIncl` — the polynomial that was inverted is a unit
upstairs — and two are the hypothesis, spent at the ordered pair and at its reverse.

**The two conclusions carry the `σ a ≠ σ b` rather than the statement carrying it**, so that the
pair of families below is total. `rr` and `uu` are total by type, and `hfam` says nothing at a
pair the index map collapses, so a statement restricted to `σ a ≠ σ b` could not produce a value
there; wrapping the conclusions instead lets the equal branch answer with junk that no consumer
can reach, since a refined datum asks both equations only where `σ a ≠ σ b`. -/
theorem exists_refineDatumCross_unitFam (a b : B) :
    ∃ (r : MvPolynomial (ULift.{u} (Fin ((obj (σ b)).n + 1))) ℂ)
      (u : (PresentedAlgebra.{u} ((obj (σ b)).n + 1) ((obj (σ b)).k + 1)
        (localisationPresentation.{u} (obj (σ b)).g (poly (σ b) (σ a))))ˣ),
      (σ a ≠ σ b →
          RefineDatumCrossEq.{u} obj σ fam poly (fun x y ↦ poly (σ x) (σ y)) glue a b r) ∧
        (σ a ≠ σ b →
          RefineDatumCrossUnit.{u} obj σ fam poly (fun x y ↦ poly (σ x) (σ y)) a b r u) := by
  by_cases h : σ a = σ b
  · exact ⟨0, 1, fun hc ↦ absurd h hc, fun hc ↦ absurd h hc⟩
  · obtain ⟨r, u, hr, hru⟩ := exists_refineDatumCross_of_isUnit.{u} obj σ fam poly
      (fun x y ↦ poly (σ x) (σ y)) glue a b
      (isUnit_mk_rename_localisationIncl.{u} (obj (σ a)).g (poly (σ a) (σ b))) (hfam a b h)
      (isUnit_mk_rename_localisationIncl.{u} (obj (σ b)).g (poly (σ b) (σ a)))
      (hfam b a (Ne.symm h))
    exact ⟨r, u, fun _ ↦ hr, fun _ ↦ hru⟩

include hfam in
/-- **The caller's `r` at a family that is a unit on each overlap**, at every ordered pair. -/
def refineDatumUnitFamR (a b : B) : MvPolynomial (ULift.{u} (Fin ((obj (σ b)).n + 1))) ℂ :=
  (exists_refineDatumCross_unitFam.{u} obj poly σ fam glue hfam a b).choose

include hfam in
/-- **The caller's unit at a family that is a unit on each overlap**, at every ordered pair. -/
def refineDatumUnitFamU (a b : B) : (PresentedAlgebra.{u} ((obj (σ b)).n + 1) ((obj (σ b)).k + 1)
    (localisationPresentation.{u} (obj (σ b)).g (poly (σ b) (σ a))))ˣ :=
  (exists_refineDatumCross_unitFam.{u} obj poly σ fam glue hfam a b).choose_spec.choose

include hfam in
/-- **The first equation**, at the pairs a refined datum asks it at. -/
theorem refineDatumUnitFamCrossEq (a b : B) (h : σ a ≠ σ b) :
    RefineDatumCrossEq.{u} obj σ fam poly (fun x y ↦ poly (σ x) (σ y)) glue a b
      (refineDatumUnitFamR.{u} obj poly σ fam glue hfam a b) :=
  (exists_refineDatumCross_unitFam.{u} obj poly σ fam glue hfam a b).choose_spec.choose_spec.1 h

include hfam in
/-- **The second equation**, at the same pairs. -/
theorem refineDatumUnitFamCrossUnit (a b : B) (h : σ a ≠ σ b) :
    RefineDatumCrossUnit.{u} obj σ fam poly (fun x y ↦ poly (σ x) (σ y)) a b
      (refineDatumUnitFamR.{u} obj poly σ fam glue hfam a b)
      (refineDatumUnitFamU.{u} obj poly σ fam glue hfam a b) :=
  (exists_refineDatumCross_unitFam.{u} obj poly σ fam glue hfam a b).choose_spec.choose_spec.2 h

/-! ### The glue data and the space -/

variable (hsym : ∀ i j : J, glue j i = (glue i j).symm)
  (hrange : ∀ i j k : J, i ≠ j → i ≠ k → j ≠ k →
    Set.range (coverTripleIncl.{u} obj poly i j k ≫
        coverTransitionHom.{u} obj poly glue i j).base ⊆
      (coverOpen.{u} obj poly j k : Set (coverSpace.{u} obj j)))

include hfam in
/-- **The glue data of a refined cover datum at an injective index map and a family that is a unit
on each overlap**, asking for the original datum's three laws and nothing else.

`ComplexAnalytic.refineDatumGlueDataOfLaws` with the first condition discharged by
`ComplexAnalytic.refineDatumRangeCross_poly` and the second by
`ComplexAnalytic.refineDatumRangeEq_of_injective`. **The family is arbitrary apart from `hfam`**,
so unlike `ComplexAnalytic.refineDatumOneGlueData` this is a refinement and not a reindexing
whenever `D(fam b)` is a proper open of its member. -/
def refineDatumUnitFamGlueData (hσ : Function.Injective σ)
    (hcocycle : ∀ i j k : J, ∀ hij : i ≠ j, ∀ hik : i ≠ k, ∀ hjk : j ≠ k,
      coverTriple.{u} obj poly glue hrange i j k hij hik hjk ≫
        coverTriple.{u} obj poly glue hrange j k i hjk hij.symm hik.symm ≫
          coverTriple.{u} obj poly glue hrange k i j hik.symm hjk.symm hij = 𝟙 _) :
    LocallyRingedSpace.GlueData.{u} :=
  refineDatumGlueDataOfLaws.{u} obj poly σ fam (fun x y ↦ poly (σ x) (σ y)) glue
    (refineDatumUnitFamR.{u} obj poly σ fam glue hfam)
    (refineDatumUnitFamU.{u} obj poly σ fam glue hfam)
    (refineDatumUnitFamCrossEq.{u} obj poly σ fam glue hfam)
    (refineDatumUnitFamCrossUnit.{u} obj poly σ fam glue hfam) hrange
    (refineDatumRangeCross_poly.{u} obj poly σ fam glue _ _ _ _ hrange)
    (refineDatumRangeEq_of_injective.{u} obj poly σ fam _ glue _ _ _ _ hσ) hsym hcocycle

include hfam in
/-- **The analytic space that refinement glues to.**

`ComplexAnalytic.refineDatumAnalytificationOfLaws` at the same arguments. -/
def refineDatumUnitFamAnalytification (hσ : Function.Injective σ)
    (hcocycle : ∀ i j k : J, ∀ hij : i ≠ j, ∀ hik : i ≠ k, ∀ hjk : j ≠ k,
      coverTriple.{u} obj poly glue hrange i j k hij hik hjk ≫
        coverTriple.{u} obj poly glue hrange j k i hjk hij.symm hik.symm ≫
          coverTriple.{u} obj poly glue hrange k i j hik.symm hjk.symm hij = 𝟙 _) :
    AnalyticSpace.{u} :=
  refineDatumAnalytificationOfLaws.{u} obj poly σ fam (fun x y ↦ poly (σ x) (σ y)) glue
    (refineDatumUnitFamR.{u} obj poly σ fam glue hfam)
    (refineDatumUnitFamU.{u} obj poly σ fam glue hfam)
    (refineDatumUnitFamCrossEq.{u} obj poly σ fam glue hfam)
    (refineDatumUnitFamCrossUnit.{u} obj poly σ fam glue hfam) hrange
    (refineDatumRangeCross_poly.{u} obj poly σ fam glue _ _ _ _ hrange)
    (refineDatumRangeEq_of_injective.{u} obj poly σ fam _ glue _ _ _ _ hσ) hsym hcocycle

include hfam in
/-- **That space has that glue data's gluing underneath it**, with no transport.

`ComplexAnalytic.refineDatumAnalytificationOfLaws_toLocallyRingedSpace` at the same arguments, and
it is here for that theorem's own stated reason: without it the two definitions above are two
well-typed objects with no recorded relation to each other, and every statement about the gluing
says nothing about the space. -/
theorem refineDatumUnitFamAnalytification_toLocallyRingedSpace (hσ : Function.Injective σ)
    (hcocycle : ∀ i j k : J, ∀ hij : i ≠ j, ∀ hik : i ≠ k, ∀ hjk : j ≠ k,
      coverTriple.{u} obj poly glue hrange i j k hij hik hjk ≫
        coverTriple.{u} obj poly glue hrange j k i hjk hij.symm hik.symm ≫
          coverTriple.{u} obj poly glue hrange k i j hik.symm hjk.symm hij = 𝟙 _) :
    (refineDatumUnitFamAnalytification.{u} obj poly σ fam glue hfam hsym hrange hσ
        hcocycle).toLocallyRingedSpace =
      (refineDatumUnitFamGlueData.{u} obj poly σ fam glue hfam hsym hrange hσ
        hcocycle).toGlueData.glued :=
  refineDatumAnalytificationOfLaws_toLocallyRingedSpace.{u} obj poly σ fam
    (fun x y ↦ poly (σ x) (σ y)) glue
    (refineDatumUnitFamR.{u} obj poly σ fam glue hfam)
    (refineDatumUnitFamU.{u} obj poly σ fam glue hfam)
    (refineDatumUnitFamCrossEq.{u} obj poly σ fam glue hfam)
    (refineDatumUnitFamCrossUnit.{u} obj poly σ fam glue hfam) hrange
    (refineDatumRangeCross_poly.{u} obj poly σ fam glue _ _ _ _ hrange)
    (refineDatumRangeEq_of_injective.{u} obj poly σ fam _ glue _ _ _ _ hσ) hsym hcocycle

end

end ComplexAnalytic
