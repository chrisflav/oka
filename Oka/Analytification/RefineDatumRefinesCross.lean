/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Analytification.DistinguishedOpenPullback
import Oka.Analytification.RefineDatumRefines

/-!
# The refined datum refines across members too, and at a factor the choice supplies

`Oka/Analytification/RefineDatumRefines.lean` states what it is for the refined datum to *refine*
the space it refines — that for every ordered pair of refined members the image of the refined
overlap is exactly where the two members meet —

`refineDatumMemberIota a '' (refined overlap at (a, b)) = range (…iota a) ∩ range (…iota b)`,

and settles it wherever `σ a = σ b`. Where `σ a ≠ σ b` it proves only the containment that costs
nothing, and its `## What is not here` records the equality as absent in both directions. **This
file proves it**, on the condition on the caller's extra factor that
`Oka/Analytification/CrossMemberChoice.lean` already produces, and then at a factor that file
supplies — so the absence three files record is closed at every ordered pair and not at some of
them.

## What was missing, and it was one change of vocabulary

At `σ a ≠ σ b` the refined overlap is cut out by `poly (σ a) (σ b) * q a b`, and
`ComplexAnalytic.refineDatumMemberIota_image_coverOpen_subset_of_ne` spends the first factor: it
puts the overlap inside the part of the member `σ b` that meets the member `σ a`. What it does not
do is put it inside `D(fam b)` — inside the *refined* member `b` rather than the member it lies
over — and that is a statement about `q a b`, which the datum reads and nothing constrains.

`ComplexAnalytic.RefineDatumCrossFactor` is the constraint the cross-member glue already imposes:
the class of `q a b` in the overlap algebra on the `σ a` side is a **unit multiple** of the class
of `fam b` carried over by the datum's own glue. It is an identity between elements of a quotient
of a polynomial ring, and `Oka/Analytification/CrossMemberChoice.lean` says in terms that the
geometry never enters it. Reading it geometrically is what this file does, and it is three steps.

**Step 1 — a unit does not move a non-vanishing locus.** An equation between classes is an
equation about values, because evaluation at a point of the analytification kills the presentation
ideal; and the image of a unit under a ring map into `ℂ` is nonzero. That is
`ComplexAnalytic.localisationOpen_eq_of_isUnit_mul`, in
`Oka/Analytification/DistinguishedOpen.lean`, whose converse — that an equality of opens gives an
associate — is a Nullstellensatz statement nothing in this repository proves and which is not
needed here.

**Step 2 — the analytified glue carries one locus to the other.** The unit having been discarded,
what is left is that the class of `q a b` *is* the image of the class of `fam b` under the algebra
map of the datum's `glue`, and `ComplexAnalytic.localisationOpen_eq_comap_analytificationMap`
(`Oka/Analytification/DistinguishedOpenPullback.lean`) turns exactly that into an equality of
opens across the analytified map. This step was expected to be the expensive one and it is one
lemma, because that file was written for this class of question.

**Step 3 — carry it into `X^an`.** The overlap's own space maps into `X^an` by two routes — down
into the member `σ a` and in, or across by the analytified glue and down into the member `σ b` and
in — and `ComplexAnalytic.base_coverIota_localisationProj`
(`Oka/Analytification/AffineCover.lean`) says the two agree.

## And the direction that is not about `q` at all

The `⊇` half needs something the tree did not have either: that a point lying in **both** members
lies over their overlap. `ComplexAnalytic.coverIota_image_coverOpen` is not that statement and its
docstring says so. `ComplexAnalytic.preimage_range_coverIota` is, and it is proved in
`Oka/Analytification/AffineCover.lean` from the glue data's description of when two points of two
members become one point of `X^an`. **The condition on `q` is not what that half needs and no
choice of `q` could supply it**, which is worth separating: at the trivial refining family `fam ≡
1` the whole statement reduces to it, so even the cheapest instance of this file's theorem is not
a corollary of the containment that was already there.

## Main results

- `ComplexAnalytic.localisationOpen_rename_eq_comap_coverGlueIso`: **the rule the caller's factor
  obeys, read as an equality of opens** — steps 1 and 2, and the only place either the unit or
  the algebra map is mentioned.
- `ComplexAnalytic.coverIota_image_localisationOpen_of_ne`: **so the two members' opens have one
  image in `X^an`** — step 3, and the form the theorem below consumes.
- `ComplexAnalytic.refineDatumMemberIota_image_coverOpen_of_ne`: **the refined datum refines, at a
  pair of refined members lying over two members of the original**, on the rule and nothing else.
- `ComplexAnalytic.exists_refineDatumMemberIota_image_coverOpen`: **and at a factor that exists**
  — a family obeying the rule at every ordered pair, at which the equality holds at every ordered
  pair, the equal ones included. This is the statement the three files' absence was about.

## What is not here

* **No canonical factor.** The family the last result produces is a `choose` from an existential
  whose own producer is a `choose`; a different run gives a different family, and nothing says
  two of them cut out the same overlaps. What is claimed is that one exists.
* **No refined cover datum, and no space.** Nothing here is about the space the refined datum
  glues to: `ComplexAnalytic.refineDatumToBase` occurs in this file only in this sentence, and the
  three refined laws are not read. What reaches the refinement at all reaches it through
  `ComplexAnalytic.refineDatumMemberIota`, a composite of two open immersions into the space the
  refinement refines; the results under `### The rule on the caller's factor, read as an equality
  of opens` and `### So the two members' opens have one image` are stated at free indices of `J`,
  with no `B`, no `σ` and no refining family in them at all.
* **No injectivity and no isomorphism.** An equality of images is a statement about sets and says
  nothing about fibres — the reading `Oka/Analytification/RefineDatumCover.lean` records — and
  nothing here upgrades a refinement to a comparison of any kind.
* **Nothing about the symmetry of the choice.** The rule is imposed at each ordered pair
  separately, and this file reads it at `(a, b)` only; whether the resulting refined datum's own
  `glue` is symmetric is a question about that field and is untouched.
* **No `Spec` side, no scheme and no `admissible`**, as in the files this one sits beside.
-/

open CategoryTheory MvPolynomial AlgebraicGeometry TopologicalSpace Topology

universe u

namespace ComplexAnalytic

noncomputable section

variable {J : Type u} (obj : J → Presentation.{u})
  (poly : ∀ i : J, J → MvPolynomial (ULift.{u} (Fin (obj i).n)) ℂ)
  (glue : ∀ i j : J, coverOverlap.{u} obj poly i j ≅ coverOverlap.{u} obj poly j i)
  (hrange : ∀ i j k : J, i ≠ j → i ≠ k → j ≠ k →
    Set.range (coverTripleIncl.{u} obj poly i j k ≫
        coverTransitionHom.{u} obj poly glue i j).base ⊆
      (coverOpen.{u} obj poly j k : Set (coverSpace.{u} obj j)))
  (hsymm : ∀ i j : J, glue j i = (glue i j).symm)
  (hcocycle : ∀ i j k : J, ∀ hij : i ≠ j, ∀ hik : i ≠ k, ∀ hjk : j ≠ k,
    coverTriple.{u} obj poly glue hrange i j k hij hik hjk ≫
      coverTriple.{u} obj poly glue hrange j k i hjk hij.symm hik.symm ≫
        coverTriple.{u} obj poly glue hrange k i j hik.symm hjk.symm hij = 𝟙 _)

/-! ### The rule on the caller's factor, read as an equality of opens -/

/-- **The rule the caller's extra factor obeys, read geometrically**: if the class of `x` in the
overlap algebra on the `i` side is a unit multiple of the class of `y` carried over from the `j`
side by the datum's own glue, then `D(x)` upstairs is the preimage of `D(y)` upstairs along the
analytified glue.

This is steps 1 and 2 of the module docstring and the only statement here that mentions either the
unit or the algebra map. The unit goes first —
`ComplexAnalytic.localisationOpen_eq_of_isUnit_mul` replaces `x` by any representative of the
transported class — and what is left is the hypothesis of
`ComplexAnalytic.localisationOpen_eq_comap_analytificationMap` at the `ComplexAnalytic.PresHom`
underlying `glue i j`, which is where the algebra becomes geometry.

**The representative is produced and not supplied**, by surjectivity of `Ideal.Quotient.mk`, and
nothing depends on which one it is: both lemmas above see it only through its class.

`ComplexAnalytic.refineDatumCrossAlgEquiv` is the datum's algebra isomorphism and its inverse is
the ring map of `(glue i j).hom` by definition, which is why no transport appears in the proof. -/
theorem localisationOpen_rename_eq_comap_coverGlueIso (i j : J)
    (x : MvPolynomial (ULift.{u} (Fin (obj i).n)) ℂ)
    (y : MvPolynomial (ULift.{u} (Fin (obj j).n)) ℂ)
    (u : (PresentedAlgebra.{u} ((obj i).n + 1) ((obj i).k + 1)
      (localisationPresentation.{u} (obj i).g (poly i j)))ˣ)
    (h : coverOverlapClass.{u} obj poly i j x =
      (u : PresentedAlgebra.{u} ((obj i).n + 1) ((obj i).k + 1)
        (localisationPresentation.{u} (obj i).g (poly i j))) *
        (refineDatumCrossAlgEquiv.{u} obj poly glue i j).symm
          (coverOverlapClass.{u} obj poly j i y)) :
    localisationOpen.{u} (localisationPresentation.{u} (obj i).g (poly i j))
        (MvPolynomial.rename (localisationIncl.{u} (obj i).n) x) =
      (Opens.map (coverGlueIso.{u} obj poly glue i j).hom.base).obj
        (localisationOpen.{u} (localisationPresentation.{u} (obj j).g (poly j i))
          (MvPolynomial.rename (localisationIncl.{u} (obj j).n) y)) := by
  obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective
    ((glue i j).hom.toRingHom (coverOverlapClass.{u} obj poly j i y))
  rw [localisationOpen_eq_of_isUnit_mul.{u} _ _ p u (h.trans (congrArg (fun z ↦
    (u : PresentedAlgebra.{u} ((obj i).n + 1) ((obj i).k + 1)
      (localisationPresentation.{u} (obj i).g (poly i j))) * z) hp.symm))]
  exact localisationOpen_eq_comap_analytificationMap.{u} (glue i j).hom _ p hp.symm

/-! ### So the two members' opens have one image -/

/-- **The two opens the rule relates have one image in `X^an`.**

`D(f_ij) ⊓ D(x)` inside the member `i` and `D(f_ji) ⊓ D(y)` inside the member `j` are the same
subset of `X^an`, as soon as `x` and `y` are related by the rule.

The proof is the previous lemma and step 3. Both intersections are pushed onto the overlap's own
space by `ComplexAnalytic.image_localisationOpen_localisationProj`, where the previous lemma says
one is the image of the other under the analytified glue — an isomorphism, so the image of a
preimage is the whole — and `ComplexAnalytic.base_coverIota_localisationProj` says the two routes
from that space into `X^an` agree. **No injectivity is spent**, in either member: the statement is
an equality of two images and not of two sets upstairs. -/
theorem coverIota_image_localisationOpen_of_ne (i j : J) (hij : i ≠ j)
    (x : MvPolynomial (ULift.{u} (Fin (obj i).n)) ℂ)
    (y : MvPolynomial (ULift.{u} (Fin (obj j).n)) ℂ)
    (u : (PresentedAlgebra.{u} ((obj i).n + 1) ((obj i).k + 1)
      (localisationPresentation.{u} (obj i).g (poly i j)))ˣ)
    (h : coverOverlapClass.{u} obj poly i j x =
      (u : PresentedAlgebra.{u} ((obj i).n + 1) ((obj i).k + 1)
        (localisationPresentation.{u} (obj i).g (poly i j))) *
        (refineDatumCrossAlgEquiv.{u} obj poly glue i j).symm
          (coverOverlapClass.{u} obj poly j i y)) :
    (coverIota.{u} obj poly glue hrange hsymm hcocycle i).toLRSHom.base ''
        ((coverOpen.{u} obj poly i j : Set (coverSpace.{u} obj i)) ∩
          (localisationOpen.{u} (obj i).g x :
            Set (AnalyticSpace.analytification.{u} (obj i).g))) =
      (coverIota.{u} obj poly glue hrange hsymm hcocycle j).toLRSHom.base ''
        ((coverOpen.{u} obj poly j i : Set (coverSpace.{u} obj j)) ∩
          (localisationOpen.{u} (obj j).g y :
            Set (AnalyticSpace.analytification.{u} (obj j).g))) := by
  have hsurj : Function.Surjective
      ⇑(coverGlueIso.{u} obj poly glue i j).hom.base :=
    (LocallyRingedSpace.homeoOfIso (coverGlueIso.{u} obj poly glue i j)).surjective
  have himg : ⇑(coverGlueIso.{u} obj poly glue i j).hom.base ''
      (localisationOpen.{u} (localisationPresentation.{u} (obj i).g (poly i j))
        (MvPolynomial.rename (localisationIncl.{u} (obj i).n) x) : Set _) =
      (localisationOpen.{u} (localisationPresentation.{u} (obj j).g (poly j i))
        (MvPolynomial.rename (localisationIncl.{u} (obj j).n) y) : Set _) := by
    have hpre : (localisationOpen.{u} (localisationPresentation.{u} (obj i).g (poly i j))
        (MvPolynomial.rename (localisationIncl.{u} (obj i).n) x) : Set _) =
        ⇑(coverGlueIso.{u} obj poly glue i j).hom.base ⁻¹'
          (localisationOpen.{u} (localisationPresentation.{u} (obj j).g (poly j i))
            (MvPolynomial.rename (localisationIncl.{u} (obj j).n) y) : Set _) := by
      rw [localisationOpen_rename_eq_comap_coverGlueIso.{u} obj poly glue i j x y u h]
      rfl
    rw [hpre]
    exact Set.image_preimage_eq _ hsurj
  refine (congrArg (fun s ↦ ⇑(coverIota.{u} obj poly glue hrange hsymm hcocycle i).toLRSHom.base
      '' s) (image_localisationOpen_localisationProj.{u} obj poly i j x)).symm.trans
    (Eq.trans ?_ (congrArg (fun s ↦
      ⇑(coverIota.{u} obj poly glue hrange hsymm hcocycle j).toLRSHom.base '' s)
      (image_localisationOpen_localisationProj.{u} obj poly j i y)))
  rw [← himg, Set.image_image, Set.image_image, Set.image_image]
  exact Set.image_congr' (base_coverIota_localisationProj.{u} obj poly glue hrange hsymm hcocycle
    i j hij)

end

/-! ### The refined datum refines at a cross-member pair -/

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
  (q : ∀ a : B, B → MvPolynomial (ULift.{u} (Fin (obj (σ a)).n)) ℂ)

/-- **The refined datum refines, at a pair of refined members lying over two members of the
original** — on the rule the caller's extra factor obeys, and on nothing else.

The half that is free is `ComplexAnalytic.refineDatumMemberIota_image_coverOpen_subset_of_ne`, and
this is the equality. Three ingredients, of which only the first reads the hypothesis:

* `ComplexAnalytic.coverIota_image_localisationOpen_of_ne` identifies the image of
  `D(f_ij) ⊓ D(q a b)` with that of `D(f_ji) ⊓ D(fam b)` — where the rule is spent;
* `ComplexAnalytic.preimage_range_coverIota` says a point of the `b`-th refined member that is in
  the member `σ a` at all is in the overlap, which is what makes the intersection of the two
  refined members reachable from the `σ a` side and **is not a statement about `q`**;
* `ComplexAnalytic.injective_base_coverIota` turns an intersection of two images inside the member
  `σ a` into the image of an intersection, exactly as in the equal case.

The rest is `ComplexAnalytic.refineDatumPoly_of_ne` — the field is `poly (σ a) (σ b) * q a b` —
and `ComplexAnalytic.image_base_localisationProj_localisationOpen_rename` to push the refined
overlap down into the member it lies over. **The last step is `rfl`**, for the reason the equal
case's is: the `a`-th refined member's inclusion *is* the projection followed by
`ComplexAnalytic.coverIota`. -/
theorem refineDatumMemberIota_image_coverOpen_of_ne {a b : B} (hab : σ a ≠ σ b)
    (hq : RefineDatumCrossFactor.{u} obj poly glue σ fam q a b) :
    (refineDatumMemberIota.{u} obj poly σ fam glue hsym hrange hcocycle a).toLRSHom.base ''
        (coverOpen.{u} (refineDatumObj.{u} obj σ fam)
            (refineDatumPoly.{u} obj poly σ fam q) a b :
          Set (coverSpace.{u} (refineDatumObj.{u} obj σ fam) a)) =
      Set.range (refineDatumMemberIota.{u} obj poly σ fam glue hsym hrange
          hcocycle a).toLRSHom.base ∩
        Set.range (refineDatumMemberIota.{u} obj poly σ fam glue hsym hrange
          hcocycle b).toLRSHom.base := by
  obtain ⟨u, hu⟩ := hq
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
        ((coverOpen.{u} obj poly (σ a) (σ b) : Set (coverSpace.{u} obj (σ a))) ∩
          (localisationOpen.{u} (obj (σ a)).g (q a b) :
            Set (AnalyticSpace.analytification.{u} (obj (σ a)).g))) := by
    rw [hpoly]
    refine (image_base_localisationProj_localisationOpen_rename.{u} (obj (σ a)).g (fam a)
      (poly (σ a) (σ b) * q a b)).trans ?_
    rw [localisationOpen_mul.{u} (obj (σ a)).g (poly (σ a) (σ b)) (q a b)]
    exact (Opens.coe_inf _ _).trans (congrArg (fun s ↦
      (localisationOpen.{u} (obj (σ a)).g (fam a) :
        Set (AnalyticSpace.analytification.{u} (obj (σ a)).g)) ∩ s) (Opens.coe_inf _ _))
  have hcross := coverIota_image_localisationOpen_of_ne.{u} obj poly glue hrange hsym hcocycle
    (σ a) (σ b) hab (q a b) (fam b) u hu
  have hinter : Set.range (refineDatumMemberIota.{u} obj poly σ fam glue hsym hrange
        hcocycle b).toLRSHom.base ∩
      Set.range (coverIota.{u} obj poly glue hrange hsym hcocycle (σ a)).toLRSHom.base =
      ⇑(coverIota.{u} obj poly glue hrange hsym hcocycle (σ b)).toLRSHom.base ''
        ((coverOpen.{u} obj poly (σ b) (σ a) : Set (coverSpace.{u} obj (σ b))) ∩
          (localisationOpen.{u} (obj (σ b)).g (fam b) :
            Set (AnalyticSpace.analytification.{u} (obj (σ b)).g))) := by
    rw [range_base_refineDatumMemberIota.{u} obj poly σ fam glue hsym hrange hcocycle b,
      ← preimage_range_coverIota.{u} obj poly glue hrange hsym hcocycle (σ a) (σ b) hab,
      ← Set.image_inter_preimage, Set.inter_comm]
  have hsubA : Set.range (refineDatumMemberIota.{u} obj poly σ fam glue hsym hrange
      hcocycle a).toLRSHom.base ⊆
      Set.range (coverIota.{u} obj poly glue hrange hsym hcocycle (σ a)).toLRSHom.base := by
    rw [range_base_refineDatumMemberIota.{u} obj poly σ fam glue hsym hrange hcocycle a]
    exact Set.image_subset_range _ _
  have hRHS : Set.range (refineDatumMemberIota.{u} obj poly σ fam glue hsym hrange
        hcocycle a).toLRSHom.base ∩
      Set.range (refineDatumMemberIota.{u} obj poly σ fam glue hsym hrange
        hcocycle b).toLRSHom.base =
      ⇑(coverIota.{u} obj poly glue hrange hsym hcocycle (σ a)).toLRSHom.base ''
        ((localisationOpen.{u} (obj (σ a)).g (fam a) :
            Set (AnalyticSpace.analytification.{u} (obj (σ a)).g)) ∩
          ((coverOpen.{u} obj poly (σ a) (σ b) : Set (coverSpace.{u} obj (σ a))) ∩
            (localisationOpen.{u} (obj (σ a)).g (q a b) :
              Set (AnalyticSpace.analytification.{u} (obj (σ a)).g)))) := by
    rw [← Set.inter_eq_self_of_subset_left hsubA, Set.inter_assoc,
      Set.inter_comm (Set.range (coverIota.{u} obj poly glue hrange hsym hcocycle
        (σ a)).toLRSHom.base), hinter, ← hcross,
      range_base_refineDatumMemberIota.{u} obj poly σ fam glue hsym hrange hcocycle a,
      ← Set.image_inter (injective_base_coverIota.{u} obj poly glue hrange hsym hcocycle (σ a))]
  rw [hRHS, ← key, ← Set.image_comp]
  rfl

end

/-! ### And at a factor that exists -/

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

/-- **There is an extra factor at which the refined datum refines, at every ordered pair.**

`ComplexAnalytic.exists_refineDatumCrossFactor` supplies a family obeying the rule at every
ordered pair — algebraically, and with no hypothesis on `σ`, on the members being distinct, or on
the cover beyond the symmetry every consumer of a cover datum carries. At such a family the two
cases meet: `ComplexAnalytic.refineDatumMemberIota_image_coverOpen_of_eq` closes the pairs whose
refined members lie over one member, reading no factor at all, and the theorem above closes the
rest.

**This is the statement three files record as absent** — that the refined datum *refines* the
space it refines, a statement about `ComplexAnalytic.refineDatumPoly` and not about a morphism
downstairs — closed at every ordered pair rather than at some of them, and it is what
`Oka/Analytification/CrossMemberDatum.lean` says nothing supplies: *"nothing says the polynomial
it supplies is one under which the chain above cuts out the refined overlap"*. Something does.

**The family is not canonical and nothing here says the refined datum is determined by it.** It
comes from a `choose`, its producer is a `choose`, and two runs give two families; what is claimed
is that the condition and the geometry are simultaneously satisfiable. -/
theorem exists_refineDatumMemberIota_image_coverOpen :
    ∃ q : ∀ a : B, B → MvPolynomial (ULift.{u} (Fin (obj (σ a)).n)) ℂ,
      ∀ a b : B,
        (refineDatumMemberIota.{u} obj poly σ fam glue hsym hrange hcocycle a).toLRSHom.base ''
            (coverOpen.{u} (refineDatumObj.{u} obj σ fam)
                (refineDatumPoly.{u} obj poly σ fam q) a b :
              Set (coverSpace.{u} (refineDatumObj.{u} obj σ fam) a)) =
          Set.range (refineDatumMemberIota.{u} obj poly σ fam glue hsym hrange
              hcocycle a).toLRSHom.base ∩
            Set.range (refineDatumMemberIota.{u} obj poly σ fam glue hsym hrange
              hcocycle b).toLRSHom.base := by
  choose q u hqu using exists_refineDatumCrossFactor.{u} obj poly glue σ fam
  refine ⟨q, fun a b ↦ ?_⟩
  rcases eq_or_ne (σ a) (σ b) with h | h
  · exact refineDatumMemberIota_image_coverOpen_of_eq.{u} obj poly σ fam glue hsym hrange
      hcocycle q h
  · exact refineDatumMemberIota_image_coverOpen_of_ne.{u} obj poly σ fam glue hsym hrange
      hcocycle q h ⟨u a b, hqu a b⟩

end

end ComplexAnalytic
