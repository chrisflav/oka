/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Analytification.RefineDatumCover

/-!
# The refined datum refines the cover it refines, wherever two refined members lie over one

Three files record the same absence, and all three say it is a statement about
`ComplexAnalytic.refineDatumPoly` rather than about a morphism.
`Oka/Analytification/CrossMemberDatum.lean`:

> **What neither of them says is that the refined datum *refines* the original space**, which is a
> statement about `ComplexAnalytic.refineDatumPoly` — that the refined overlaps are cut out where
> it says they are — and is about neither `ComplexAnalytic.polyDiagOne` nor a surjection
> downstairs; nothing on this line states it, and a morphism that is onto is not a refinement of
> covers.

`Oka/Analytification/RefineDatumCover.lean` and `Oka/Analytification/RefineDatumToBase.lean` say
the same thing in their own `## What is not here`, the second calling it *"the remaining half"* of
the quoted bullet.

**This file states it and settles it wherever the two refined members lie over one member of the
original cover.** Where they lie over two, what is proved is a containment, and the sharpest thing
this file has to say is where that containment stops — see the section of that name.

## What the statement is, and it is an equality of two subsets of `X^an`

`ComplexAnalytic.refineDatumMemberIota b` is the `b`-th refined member sitting in the space the
refinement refines, so `Set.range` of its base is *where the `b`-th refined member is* as a subset
of `X^an`. The refined datum's own overlap at `(a, b)` is `ComplexAnalytic.coverOpen` of
`ComplexAnalytic.refineDatumObj` at `ComplexAnalytic.refineDatumPoly` — an open of the `a`-th
refined member, cut out by one polynomial, and *that polynomial is the whole of what the datum
claims about where the two members meet.*

So the datum refines exactly when, for every ordered pair, that open lands on the intersection of
the two refined members:

`refineDatumMemberIota a '' (refined overlap at (a, b)) = range (…iota a) ∩ range (…iota b)`.

**It is an equality and not a containment, and the two inclusions are different facts.** `⊆` says
the polynomial does not cut out too much; `⊇` says a point in both members is in the open, which
is what fails when the polynomial is too small and is the direction the caller's choice bears on.

## The same-member pairs, where it is a theorem and asks the caller for nothing

`ComplexAnalytic.refineDatumMemberIota_image_coverOpen_of_eq`. At `σ a = σ b` the field is
`ComplexAnalytic.refineDatumPoly_of_eq` — the *other* refining polynomial alone, transported —
because `ComplexAnalytic.polyDiagOne` normalised the diagonal, and the whole computation is then
one member's:

* `ComplexAnalytic.image_base_localisationProj_localisationOpen_rename`
  (`Oka/Analytification/DistinguishedOpen.lean`) sends the refined overlap down into the member it
  lies over, as `D(fam a) ⊓ D(fam b)`;
* `ComplexAnalytic.injective_base_coverIota` (`Oka/Analytification/AffineCover.lean`) turns the
  image of that intersection into the intersection of the two images, which is `Set.image_inter`
  and is the only place injectivity is spent.

**The transport is one `subst` and it is paid in a lemma of its own.** `fam b` is a polynomial in
the variables of `obj (σ b)` where the formula needs one over `obj (σ a)`; the equation
`σ a = σ b` cannot be `subst`ed as it stands, so
`ComplexAnalytic.coverIota_image_inter_of_eq` states the set identity at two *free* indices with an
equation between them, where `subst` applies. That is the same manoeuvre
`Oka/Analytification/CrossMemberDatumGlue.lean` describes for the equal branch of the glue, and it
is why the `subst` is performed once in this file and by nothing that consumes that lemma. A
consumer still *carries* the transport where the formula wants `fam b` over the `a`-th member —
`ComplexAnalytic.refineDatumPoly_of_eq` is **stated** with an `h ▸ fam b` — and carries none where
it hands `fam b` to this lemma at its own free index, which is what the free indices are for.

**The caller's `q` is not read at these pairs**, which is `ComplexAnalytic.refineDatumFactor`'s
shape and not a hypothesis discharged here.

## The instance that has no other pairs

`ComplexAnalytic.refineDatumMemberIota_image_coverOpen_const`: at a constant `σ` **every** ordered
pair is a same-member pair, so the equality holds at all of them with no hypothesis — the
refinement `Oka/Analytification/CoverRefinement.lean` builds refines the cover it refines, and that
is the statement, not a corollary of a surjection. It is the theorem above at `rfl` and nothing
else.

## The cross-member pairs, where the containment stops exactly at the caller's `q`

`ComplexAnalytic.refineDatumMemberIota_image_coverOpen_subset_of_ne` is what holds with no
condition: at `σ a ≠ σ b` the refined overlap lands inside the `a`-th refined member **and** inside
the part of the member `σ b` that meets the member `σ a`. The second is
`ComplexAnalytic.coverIota_image_coverOpen`, which says `D(f_ij)` and `D(f_ji)` have one image;
the factor `poly (σ a) (σ b)` in `ComplexAnalytic.refineDatumPoly_of_ne` is what puts the overlap
there, and it is a factor of the field whatever the caller chose.

**What is missing is `D(fam b)` and not the member**, and that is the sharp form of the absence
the three files record. Landing in the member `σ b` is free; landing in the *refined* member `b`
is a statement about the caller's `q`, and
`Oka/Analytification/CrossMemberDatum.lean` says in terms that nothing supplies one:

> what it supplies obeys `ComplexAnalytic.RefineDatumCrossFactor`, a rule about classes in an
> overlap algebra, and nothing says the polynomial it supplies is one under which the chain above
> cuts out the refined overlap.

**Nothing here is evidence that the equality fails at a cross-member pair**, and this file does not
claim it does: what it claims is that the two halves of the pair statement are `poly (σ a) (σ b)`
and `q a b`, and that the first is discharged here and the second is not. **The missing step is a
geometric reading of a condition stated in an algebra, and it is taken in
`Oka/Analytification/RefineDatumRefinesCross.lean`** — this paragraph ended *"a condition
currently stated in an algebra"* while that was the whole of what anything said about it.

## Main results

- `ComplexAnalytic.coverIota_image_inter_of_eq`: **two refining polynomials over one member give
  two subsets of `X^an` whose intersection is the image of their intersection** — the transport and
  the injectivity, in one lemma, so that the `subst` is paid there and by no consumer of it.
- `ComplexAnalytic.refineDatumMemberIota_image_coverOpen_of_eq`: **the refined datum refines, at
  every pair of refined members lying over one member of the original.** The equality, on no
  hypothesis about the caller's extra factor.
- `ComplexAnalytic.refineDatumMemberIota_image_coverOpen_const`: **so a refinement of one fixed
  member refines**, at every pair and with nothing left open.
- `ComplexAnalytic.refineDatumMemberIota_image_coverOpen_subset_of_ne`: **and where the two
  members are different, the containment that holds for free** — into the `a`-th refined member
  and into the part of the member `σ b` that meets the member `σ a`.

## What is not here

* **No equality at a cross-member pair, in either direction, *below*.** Neither the statement
  that `ComplexAnalytic.refineDatumPoly` cuts out the intersection there nor a counterexample to
  it is in this file, and the containment above is not evidence for either: it is the half that
  needs no hypothesis, and the half it omits is exactly the one a condition on `q` supplies.
  **This bullet stood for the tree until 2026-09-04**, when
  `Oka/Analytification/RefineDatumRefinesCross.lean` proved the equality on
  `ComplexAnalytic.RefineDatumCrossFactor` and then at a family obeying it at every ordered pair;
  what remains here is the statement about this file, and the reason the two are separate files is
  that the cross-member proof reads the datum's own `glue` and nothing above does.
* **Nothing about `ComplexAnalytic.RefineDatumCrossFactor` *here*.** The rule
  `Oka/Analytification/CrossMemberChoice.lean` produces a factor under is an identity between
  classes in an overlap algebra, and this file does not open it. **This bullet said no statement
  anywhere read it geometrically and that none of the three steps of such a reading was in the
  tree**; `Oka/Analytification/RefineDatumRefinesCross.lean` reads it, and the three steps — a
  class equal to a unit multiple of another has the same non-vanishing locus, the analytified glue
  carries one locus to the other, and the two members' inclusions agree on the overlap — are the
  three that file names. What is still true of *this* file is the first clause: no statement below
  mentions the rule, and the equality above holds at pairs where the caller's factor is not read
  at all.
* **No injectivity and no isomorphism.** `Oka/Analytification/RefineDatumCover.lean`'s *"No
  injectivity, and no claim that anything is an isomorphism"* is untouched in both halves: an
  equality of images is a statement about sets and says nothing about fibres, and **nothing here is
  about `ComplexAnalytic.refineDatumToBase`**. The statements about the refined members are about
  `ComplexAnalytic.refineDatumMemberIota`, which is a composite of two open immersions;
  `ComplexAnalytic.coverIota_image_inter_of_eq` is about `ComplexAnalytic.coverIota` and
  `ComplexAnalytic.localisationOpen`, at two free indices of `J` and with no refining family in its
  statement at all.
* **No statement about the refined datum's own space.** `ComplexAnalytic.refineDatumMemberIota`
  reads no refined datum — that is the property `Oka/Analytification/RefineDatumCover.lean` builds
  its open cover on — so nothing here needs the three refined laws, and nothing here says a word
  about the space they glue to.
* **No `Spec` side, no scheme and no `admissible`**, as in the files this one sits beside.
-/

open CategoryTheory MvPolynomial AlgebraicGeometry TopologicalSpace Topology

universe u

namespace ComplexAnalytic

noncomputable section

variable {J B : Type u} (obj : J → Presentation.{u})
  (poly : ∀ i : J, J → MvPolynomial (ULift.{u} (Fin (obj i).n)) ℂ)
  (σ : B → J)
  (fam : ∀ b : B, MvPolynomial (ULift.{u} (Fin (obj (σ b)).n)) ℂ)
  (glue : ∀ i j : J, coverOverlap.{u} obj poly i j ≅ coverOverlap.{u} obj poly j i)
  (hsym : ∀ i j : J, glue j i = (glue i j).symm)
  (hrange : ∀ i j k : J, i ≠ j → i ≠ k → j ≠ k →
    Set.range (coverTripleIncl.{u} obj poly i j k ≫
        coverTransitionHom.{u} obj poly glue i j).base ⊆
      (coverOpen.{u} obj poly j k : Set (coverSpace.{u} obj j)))
  (hcocycle : ∀ i j k : J, ∀ hij : i ≠ j, ∀ hik : i ≠ k, ∀ hjk : j ≠ k,
    coverTriple.{u} obj poly glue hrange i j k hij hik hjk ≫
      coverTriple.{u} obj poly glue hrange j k i hjk hij.symm hik.symm ≫
        coverTriple.{u} obj poly glue hrange k i j hik.symm hjk.symm hij = 𝟙 _)

/-! ### The transport, in one lemma -/

/-- **Two refining polynomials read over one member, and the image of their intersection.**

The two refined members of an equal pair lie over the *same* member of the original cover, so
their images in `X^an` are the images of two distinguished opens of that one member and
`Set.image_inter` applies — `ComplexAnalytic.injective_base_coverIota` is the hypothesis it asks
for.

**The two indices are free and the equation between them is an argument**, which is the whole
reason the lemma exists: `fam b` is a polynomial over `obj (σ b)` where the formula needs one over
`obj (σ a)`, and `σ a = σ b` is an equation between two applications and cannot be `subst`ed. At
free `i` and `j` it can, and after the `subst` there is no transport left. -/
theorem coverIota_image_inter_of_eq {i j : J} (h : i = j)
    (f : MvPolynomial (ULift.{u} (Fin (obj i).n)) ℂ)
    (f' : MvPolynomial (ULift.{u} (Fin (obj j).n)) ℂ) :
    (coverIota.{u} obj poly glue hrange hsym hcocycle i).toLRSHom.base ''
        ((localisationOpen.{u} (obj i).g f :
            Set (AnalyticSpace.analytification.{u} (obj i).g)) ∩
          (localisationOpen.{u} (obj i).g (h ▸ f') :
            Set (AnalyticSpace.analytification.{u} (obj i).g))) =
      (coverIota.{u} obj poly glue hrange hsym hcocycle i).toLRSHom.base ''
          (localisationOpen.{u} (obj i).g f :
            Set (AnalyticSpace.analytification.{u} (obj i).g)) ∩
        (coverIota.{u} obj poly glue hrange hsym hcocycle j).toLRSHom.base ''
          (localisationOpen.{u} (obj j).g f' :
            Set (AnalyticSpace.analytification.{u} (obj j).g)) := by
  subst h
  exact Set.image_inter (injective_base_coverIota.{u} obj poly glue hrange hsym hcocycle i)

variable (q : ∀ a : B, B → MvPolynomial (ULift.{u} (Fin (obj (σ a)).n)) ℂ)

/-! ### Where the two refined members lie over one member -/

/-- **The refined datum refines, at every pair of refined members over one member.**

The image in `X^an` of the refined overlap at `(a, b)` is exactly where the `a`-th and `b`-th
refined members meet. No hypothesis on the caller's extra factor: at `σ a = σ b` the field is
`ComplexAnalytic.refineDatumPoly_of_eq`, which does not read it.

The chain is `ComplexAnalytic.refineDatumPoly_of_eq`, then
`ComplexAnalytic.image_base_localisationProj_localisationOpen_rename` to push the overlap down into
the member it lies over, then `ComplexAnalytic.coverIota_image_inter_of_eq` to push it into
`X^an`; `ComplexAnalytic.range_base_refineDatumMemberIota` is what puts the right-hand side in the
same vocabulary. **The last step is `rfl` and not a rewrite**: the `b`-th refined member's
inclusion *is* the projection followed by `ComplexAnalytic.coverIota`, so `Set.image_comp` closes
the goal definitionally rather than through an equation about the composite. -/
theorem refineDatumMemberIota_image_coverOpen_of_eq {a b : B} (h : σ a = σ b) :
    (refineDatumMemberIota.{u} obj poly σ fam glue hsym hrange hcocycle a).toLRSHom.base ''
        (coverOpen.{u} (refineDatumObj.{u} obj σ fam)
            (refineDatumPoly.{u} obj poly σ fam q) a b :
          Set (coverSpace.{u} (refineDatumObj.{u} obj σ fam) a)) =
      Set.range (refineDatumMemberIota.{u} obj poly σ fam glue hsym hrange
          hcocycle a).toLRSHom.base ∩
        Set.range (refineDatumMemberIota.{u} obj poly σ fam glue hsym hrange
          hcocycle b).toLRSHom.base := by
  have hpoly : coverOpen.{u} (refineDatumObj.{u} obj σ fam)
      (refineDatumPoly.{u} obj poly σ fam q) a b =
      localisationOpen.{u} (localisationPresentation.{u} (obj (σ a)).g (fam a))
        (MvPolynomial.rename (localisationIncl.{u} (obj (σ a)).n) (h ▸ fam b)) :=
    congrArg (localisationOpen.{u} (localisationPresentation.{u} (obj (σ a)).g (fam a)))
      (refineDatumPoly_of_eq.{u} obj poly σ fam q h)
  have key : ⇑(localisationProj.{u} (obj (σ a)).g (fam a)).toLRSHom.base ''
      (coverOpen.{u} (refineDatumObj.{u} obj σ fam)
          (refineDatumPoly.{u} obj poly σ fam q) a b :
        Set (coverSpace.{u} (refineDatumObj.{u} obj σ fam) a)) =
      (localisationOpen.{u} (obj (σ a)).g (fam a) :
          Set (AnalyticSpace.analytification.{u} (obj (σ a)).g)) ∩
        (localisationOpen.{u} (obj (σ a)).g (h ▸ fam b) :
          Set (AnalyticSpace.analytification.{u} (obj (σ a)).g)) := by
    rw [hpoly]
    exact (image_base_localisationProj_localisationOpen_rename.{u} (obj (σ a)).g (fam a)
      (h ▸ fam b)).trans (Opens.coe_inf _ _)
  rw [range_base_refineDatumMemberIota.{u} obj poly σ fam glue hsym hrange hcocycle a,
    range_base_refineDatumMemberIota.{u} obj poly σ fam glue hsym hrange hcocycle b,
    ← coverIota_image_inter_of_eq.{u} obj poly glue hsym hrange hcocycle h (fam a) (fam b),
    ← key, ← Set.image_comp]
  rfl

/-! ### Where they lie over two -/

/-- **And where the two refined members lie over two members, the containment that is free.**

The refined overlap lands in the `a`-th refined member — that is `Set.image_subset_range` and
nothing about the datum — and in the part of the member `σ b` that meets the member `σ a`, which
is `ComplexAnalytic.coverIota_image_coverOpen` applied to the factor `poly (σ a) (σ b)` that
`ComplexAnalytic.refineDatumPoly_of_ne` puts in the field whatever the caller chose.

**It does not say the overlap lands in the `b`-th refined member**, and the module docstring's
`### The cross-member pairs` is where that gap is what it is: `D(fam b)` is what is missing, the
member is not, and nothing here is evidence about the equality in either direction. -/
theorem refineDatumMemberIota_image_coverOpen_subset_of_ne {a b : B} (hab : σ a ≠ σ b) :
    (refineDatumMemberIota.{u} obj poly σ fam glue hsym hrange hcocycle a).toLRSHom.base ''
        (coverOpen.{u} (refineDatumObj.{u} obj σ fam)
            (refineDatumPoly.{u} obj poly σ fam q) a b :
          Set (coverSpace.{u} (refineDatumObj.{u} obj σ fam) a)) ⊆
      Set.range (refineDatumMemberIota.{u} obj poly σ fam glue hsym hrange
          hcocycle a).toLRSHom.base ∩
        (coverIota.{u} obj poly glue hrange hsym hcocycle (σ b)).toLRSHom.base ''
          (coverOpen.{u} obj poly (σ b) (σ a) : Set (coverSpace.{u} obj (σ b))) := by
  have hpoly : coverOpen.{u} (refineDatumObj.{u} obj σ fam)
      (refineDatumPoly.{u} obj poly σ fam q) a b =
      localisationOpen.{u} (localisationPresentation.{u} (obj (σ a)).g (fam a))
        (MvPolynomial.rename (localisationIncl.{u} (obj (σ a)).n)
          (poly (σ a) (σ b) * q a b)) :=
    congrArg (localisationOpen.{u} (localisationPresentation.{u} (obj (σ a)).g (fam a)))
      (refineDatumPoly_of_ne.{u} obj poly σ fam q hab)
  have key : ⇑(localisationProj.{u} (obj (σ a)).g (fam a)).toLRSHom.base ''
      (coverOpen.{u} (refineDatumObj.{u} obj σ fam)
          (refineDatumPoly.{u} obj poly σ fam q) a b :
        Set (coverSpace.{u} (refineDatumObj.{u} obj σ fam) a)) =
      (localisationOpen.{u} (obj (σ a)).g (fam a) :
          Set (AnalyticSpace.analytification.{u} (obj (σ a)).g)) ∩
        (localisationOpen.{u} (obj (σ a)).g (poly (σ a) (σ b) * q a b) :
          Set (AnalyticSpace.analytification.{u} (obj (σ a)).g)) := by
    rw [hpoly]
    exact (image_base_localisationProj_localisationOpen_rename.{u} (obj (σ a)).g (fam a)
      (poly (σ a) (σ b) * q a b)).trans (Opens.coe_inf _ _)
  have hsub : ⇑(localisationProj.{u} (obj (σ a)).g (fam a)).toLRSHom.base ''
      (coverOpen.{u} (refineDatumObj.{u} obj σ fam)
          (refineDatumPoly.{u} obj poly σ fam q) a b :
        Set (coverSpace.{u} (refineDatumObj.{u} obj σ fam) a)) ⊆
      (coverOpen.{u} obj poly (σ a) (σ b) : Set (coverSpace.{u} obj (σ a))) := by
    rw [key]
    intro x hx
    have hx2 := hx.2
    rw [localisationOpen_mul.{u} (obj (σ a)).g (poly (σ a) (σ b)) (q a b)] at hx2
    exact hx2.1
  refine Set.subset_inter (Set.image_subset_range _ _) ?_
  rw [← coverIota_image_coverOpen.{u} obj poly glue hrange hsym hcocycle (σ a) (σ b) hab]
  rintro _ ⟨w, hw, rfl⟩
  exact ⟨_, hsub ⟨w, hw, rfl⟩, rfl⟩

end

/-! ### A refinement of one fixed member has no other pairs -/

noncomputable section

variable {J B : Type u} (obj : J → Presentation.{u})
  (poly : ∀ i : J, J → MvPolynomial (ULift.{u} (Fin (obj i).n)) ℂ)
  (glue : ∀ i j : J, coverOverlap.{u} obj poly i j ≅ coverOverlap.{u} obj poly j i)
  (hsym : ∀ i j : J, glue j i = (glue i j).symm)
  (hrange : ∀ i j k : J, i ≠ j → i ≠ k → j ≠ k →
    Set.range (coverTripleIncl.{u} obj poly i j k ≫
        coverTransitionHom.{u} obj poly glue i j).base ⊆
      (coverOpen.{u} obj poly j k : Set (coverSpace.{u} obj j)))
  (hcocycle : ∀ i j k : J, ∀ hij : i ≠ j, ∀ hik : i ≠ k, ∀ hjk : j ≠ k,
    coverTriple.{u} obj poly glue hrange i j k hij hik hjk ≫
      coverTriple.{u} obj poly glue hrange j k i hjk hij.symm hik.symm ≫
        coverTriple.{u} obj poly glue hrange k i j hik.symm hjk.symm hij = 𝟙 _)
  (i : J) (fam : B → MvPolynomial (ULift.{u} (Fin (obj i).n)) ℂ)
  (q : ∀ _ : B, B → MvPolynomial (ULift.{u} (Fin (obj i).n)) ℂ)

/-- **A refinement of one fixed member refines, at every ordered pair.**

`Oka/Analytification/CoverRefinement.lean`'s shape is a constant `σ`, so every pair of refined
members lies over one member of the original and the theorem above applies at `rfl` — there is no
second case and no hypothesis. Stated because *"the refined datum refines the original space"* is
what three files record as absent, and at this shape the absence is now closed outright rather
than closed at some of the pairs. -/
theorem refineDatumMemberIota_image_coverOpen_const (a b : B) :
    (refineDatumMemberIota.{u} obj poly (fun _ ↦ i) fam glue hsym hrange
        hcocycle a).toLRSHom.base ''
        (coverOpen.{u} (refineDatumObj.{u} obj (fun _ ↦ i) fam)
            (refineDatumPoly.{u} obj poly (fun _ ↦ i) fam q) a b :
          Set (coverSpace.{u} (refineDatumObj.{u} obj (fun _ ↦ i) fam) a)) =
      Set.range (refineDatumMemberIota.{u} obj poly (fun _ ↦ i) fam glue hsym hrange
          hcocycle a).toLRSHom.base ∩
        Set.range (refineDatumMemberIota.{u} obj poly (fun _ ↦ i) fam glue hsym hrange
          hcocycle b).toLRSHom.base :=
  refineDatumMemberIota_image_coverOpen_of_eq.{u} obj poly (fun _ ↦ i) fam glue hsym hrange
    hcocycle q rfl

end

end ComplexAnalytic
