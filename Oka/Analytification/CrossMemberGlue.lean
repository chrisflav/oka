/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Analytification.CoverRefinement

/-!
# The glue of a refined overlap that meets two different members

`Oka/Analytification/CoverRefinement.lean` refines **one fixed member** of a cover by
distinguished opens. Its `σ` is constant, so every overlap of the refined data is an overlap
inside one member, and its own `## What is not here` says why that is a boundary rather than a
size: the cross-member case *"has to transport the original `glue` through two localisations and
it is the only part that uses the original data's own glue isomorphism at all"*. **This file
builds that transport**, as an isomorphism with a coherence triangle, and it uses the original
`glue` exactly once. (That sentence is quoted as this branch leaves it: the same branch narrows
the bullet it sits in, and a quotation of the version on the parent commit would be a citation of
a tree nobody can check out.)

## The chain, and it is three tools that had never been composed

Write `A` for the `i`-th member and `A'` for the `j`-th, `f` for the polynomial cutting the
original overlap out of `A` and `f'` for its mirror, `x` and `x'` for the two refining
polynomials, and `q`, `q'` for the extra factors that cut the cross-member overlap down inside
each refined member. The refined overlap is presented as `((A)_x)_{f·q}` on one side and as
`((A')_{x'})_{f'·q'}` on the other, and the two are identified in three steps:

1. **Re-associate each side over the original overlap.** `((A)_x)_{f·q}` and `((A)_f)_{q·x}` are
   both the single localisation `A_{(f·q)·x} = A_{(q·x)·f}`, by
   `ComplexAnalytic.localisationPresentationIsoMul` twice with a transport between the two
   products. That is `ComplexAnalytic.localisationPresentationIsoOfMulEq` below, which is the
   general form of the same-member glue: `ComplexAnalytic.refineGlue` **is** an instance of it,
   by `rfl`, and `ComplexAnalytic.refineGlue_eq_localisationPresentationIsoOfMulEq` says so.
2. **Cross from `A_f` to `A'_{f'}`**, which is the only step that reads the original data's glue:
   `ComplexAnalytic.localisationPresentationIsoOfAlgEquiv` at the algebra isomorphism the glue
   gives. A caller holds `glue i j` as an isomorphism of *presentations* and reaches the algebra
   isomorphism through `ComplexAnalytic.Presentation.algEquivOfIso`.
3. **Correct the cutting polynomial by a unit.** Step 2 lands at the localisation of `A'_{f'}` at
   *some* polynomial whose class is the image of the class of `q·x`; the polynomial the other
   side actually offers is `q'·x'`, and the two agree only up to a unit — which is exactly what
   `ComplexAnalytic.exists_mk_rename_eq` produces and what an equality of non-vanishing loci does
   not give. `ComplexAnalytic.localisationPresentationIsoOfUnitMul` absorbs it.

Steps 2 and 3 are packaged as `ComplexAnalytic.localisationPresentationIsoOfAlgEquivUnitMul`, and
the answer to whether the two compose at all is **yes, as a two-term `Iso.trans` with a
two-rewrite triangle**; nothing had to be re-proved through `PresentedAlgebra` and back.

## What the triangle is over, and it is not the members

In the same-member case both descriptions of an overlap lie over one fixed member, and
`ComplexAnalytic.refineGlue_comp` is the statement that the glue commutes with the two structure
maps down to it. **Here there is no such object.** The two refined members lie over `A` and over
`A'`, and the data contains no morphism between those two — the original `glue` relates `A_f` and
`A'_{f'}` and nothing relates `A` and `A'`. So the coherence statement is over the *original
overlap*: `ComplexAnalytic.refineCrossProj` is a refined overlap read as a localisation of the
original overlap, and `ComplexAnalytic.refineCrossGlue_hom_comp` says the glue commutes with the
two of those and the isomorphism between them.
`ComplexAnalytic.refineCrossProj_localisationHom` puts that projection back over the member, so a
consumer that wants the member-level statement composes the two and gets one whose right-hand
side ends in the original glue.

## Every proof below opens a definition with `change` and not with `rw`

All four coherence triangles have to see through the `Iso.trans` their definition is, and a `rw`
at the definition would generate an auto-generated equation lemma under its own name, as
`Oka/Analytification/CoverRefinement.lean` records itself doing at `ComplexAnalytic.refineMul` and
at `ComplexAnalytic.refineGlue`, which is how that file states it too. The declaration dump is
what shows such a lemma and the build is not, which is why `change` is worth the extra lines: with
it this file adds its own declarations to the dump and nothing else, apart from the `congr_simp`
companions of `ComplexAnalytic.localisationPresentationIsoOfMulEq` and
`ComplexAnalytic.localisationPresentationIsoOfAlgEquivUnitMul` — both take a proof argument, and
the `simp only` in the last proof needs a congruence lemma to traverse them. **Named rather than
counted**: a numeral here is a claim about this module's dump rows that the next `simp only`
anyone adds to this file falsifies, and by this paragraph's own argument the dump is the only
thing that would show it.

## Where the two general statements would live if one lemma moved

`ComplexAnalytic.localisationPresentationIsoOfMulEq` and
`ComplexAnalytic.localisationPresentationIsoOfAlgEquivUnitMul` mention no cover and no refinement,
and neither belongs here on its subject. **They are held here for different reasons and only one
of them is a reason.**

`ComplexAnalytic.localisationPresentationIsoOfMulEq` is built from
`ComplexAnalytic.localisationPresentationIsoMul`, so
`Oka/Analytification/LocalisationComposite.lean` is where it goes; what keeps it here is one line,
that its triangle needs `ComplexAnalytic.eqToHom_localisationHom`, which is declared in
`Oka/Analytification/CoverRefinement.lean` and is a general statement about a transport cancelling
against a structure map. Moving that lemma earlier is the right change and it is **not** bundled
here: it would move a declaration between files in the same branch that adds nine, and a census
taken across a move counts the moved file.

`ComplexAnalytic.localisationPresentationIsoOfAlgEquivUnitMul` is held by nothing. Its two
ingredients and both of their triangles are in `Oka/Analytification/LocalisationIndependence.lean`
— which `Oka/Analytification/LocalisationComposite.lean` imports, so that file is *downstream* of
them rather than beside them — and it touches `ComplexAnalytic.eqToHom_localisationHom` nowhere.
**It could move to the file that declares its ingredients today, with no lemma moved and no census
taken across a move.** It is here because it and the statement above are the two halves of one
chain and splitting them across two files at the moment of writing them would have made the chain
harder to read, which is a reason to state and not a reason to hide.

## Main definitions

- `ComplexAnalytic.localisationPresentationIsoOfMulEq`: **two double localisations with the same
  product are isomorphic**, which re-associates a refined overlap over whichever of its two
  factors a consumer wants underneath it.
- `ComplexAnalytic.localisationPresentationIsoOfAlgEquivUnitMul`: **the transport across an
  isomorphism of the bases, followed by a change of cutting polynomial by a unit.**
- `ComplexAnalytic.refineCrossProj`: **the refined overlap, projected to the original overlap**
  rather than to its own member.
- `ComplexAnalytic.refineCrossGlue`: **the glue of a cross-member refined overlap**, the whole
  chain above.

## Main results

- `ComplexAnalytic.localisationPresentationIsoOfMulEq_hom_comp` and
  `ComplexAnalytic.localisationPresentationIsoOfAlgEquivUnitMul_hom_comp`: **the two coherence
  triangles of the steps.** The second is over the isomorphism of the two bases, which is where
  this line stops being about one member.
- `ComplexAnalytic.refineCrossProj_localisationHom`: **the projection to the original overlap,
  followed down to the member, is the refined overlap's own two structure maps.**
- `ComplexAnalytic.refineCrossGlue_hom_comp`: **the coherence triangle of the cross-member glue**,
  over the original overlap. This is the content of the file: without it the glue would be an
  isomorphism of the right type with no recorded relation to the data it is built from.
- `ComplexAnalytic.refineGlue_eq_localisationPresentationIsoOfMulEq`: **the same-member glue is an
  instance of the re-association**, by `rfl`. Evidence that the general statement is the right
  one rather than a second one of the same shape.

## What is not here

* **No refined cover datum, and its `poly` field is the one part that now exists.** A datum needs
  one polynomial per ordered pair of refined members, uniformly in the pair, and the two cases are
  different formulas — for `σ a = σ b` the overlap is cut out by the other refining polynomial
  alone (`ComplexAnalytic.refineGlue`'s configuration) and for `σ a ≠ σ b` by `f · q` above.
  `ComplexAnalytic.refineDatumPoly` (`Oka/Analytification/CrossMemberDatum.lean`) is that field
  and it is **one product**, with `ComplexAnalytic.refineDatumPoly_of_eq` and
  `ComplexAnalytic.refineDatumPoly_of_ne` reading the two cases back off it.

  **What that file corrects here is the sentence that a cover datum's `poly i i` being
  unconstrained stops the second formula serving at the first.** It does, and normalising the
  diagonal removes the obstruction, because `CategoryTheory.GlueData.ofGlueData'` discards `V i i`
  — so `ComplexAnalytic.polyDiagOne` changes no glued space. **That last clause was an argument
  when it was written here and is now a theorem**:
  `ComplexAnalytic.coverAnalytification_polyDiagOne`
  (`Oka/Analytification/DiagonalIndependence.lean`), an instance of
  `ComplexAnalytic.coverAnalytification_congr` — two cover data glue to the same analytic space as
  soon as they agree off the diagonal. Read it and not this sentence: this one says what the
  argument was and that one is what holds. **What is still exactly right is the transport**:
  *"in the equal case the branch is handed `fam b`, which is a polynomial over the member `σ b`,
  where it must produce one over the member `σ a`"*. It has
  not gone anywhere; it sits inside `ComplexAnalytic.refineDatumFactor`, between two values of one
  type, instead of in the shape of the refined overlap where every construction below would meet
  it. The equal case's *second* transport, between two objects of
  `ComplexAnalytic.Presentation`, is paid in `Oka/Analytification/CrossMemberDatumGlue.lean`,
  which builds that branch of the glue with its symmetry and its coherence triangle — **and the
  same file now assembles the two branches into a `glue` field**,
  `ComplexAnalytic.refineDatumGlue`, whose unequal branch is
  `ComplexAnalytic.refineCrossGlue` below conjugated onto the datum's own overlaps. What that
  field takes is the caller's `r`, `u` and two equations, one per ordered pair off the diagonal,
  so the bullet below is what it is still a function of; `hsymm` holds on the equal branch alone,
  and neither geometric law is touched *here* — `hrange` is proved of both branches at once in
  `Oka/Analytification/RefineDatumGlueData.lean`, from two conditions that file adopts and shows
  *equivalent* to it, so what a caller carries there is the range law under another name rather
  than a discharge of it; and `hcocycle` is stated there and proved in
  `Oka/Analytification/RefineDatumCocycle.lean`, from the original datum's own three laws.
* **Nothing here produces `q`.** The extra factor and the unit are arguments. This bullet used to
  offer `ComplexAnalytic.exists_localisationOpen_eq_rename`,
  `ComplexAnalytic.exists_mk_rename_eq` and
  `ComplexAnalytic.exists_comap_analytificationMap_eq_comap_localisationProj` as *where they come
  from*, and **that reading is wrong in a way worth recording rather than deleting**:
  `ComplexAnalytic.exists_refineDatumCross` (`Oka/Analytification/CrossMemberChoice.lean`)
  produces a choice from the second alone, and the two that produce an equality of opens are the
  ones an associate does not follow from — `ComplexAnalytic.exists_mk_rename_eq`'s own docstring
  names that implication as a Nullstellensatz statement this repository does not prove. A worker
  who took the list at face value would spend a session on the two that are not the obstruction.
  A choice being an existential, a datum built from one chooses. **This bullet then said that
  choice was *"what a `hsymm` would then have to be stated against"*, and that nothing anywhere
  says the choice for the pair `(a, b)` and the choice for `(b, a)` can be made compatibly** —
  the second half is still true and the first is not.
  `Oka/Analytification/RefineDatumSymm.lean` states the symmetry law against two arbitrary
  independent choices and proves it, because the coherence triangle below determines the
  isomorphism once the projection it is over is known to be a monomorphism.
* **No `hrange` and no `hcocycle` here, and the two no longer stand or fall together.** They are
  the cross-member analogue of `ComplexAnalytic.refineHrange` and
  `ComplexAnalytic.refineHcocycle`.
  **This bullet said of both that the argument discharging those does not transfer, because it
  cancels against the projection of the *one* fixed member and three cross-member triple overlaps
  sit over three different members with no common target. That was said of `hcocycle`'s argument,
  and it does not stand either.** The cancellation is against the projection of the member the
  triple's *first* index lies over, which exists whatever `σ` is
  (`ComplexAnalytic.refineDatumCocycle_of_localisationProj`); what has no analogue is the step
  after it, which reads all three edges of the triple over one member. **Both laws are proved
  now**: the range law in `Oka/Analytification/RefineDatumGlueData.lean`, from two conditions that
  file adopts and shows *equivalent* to it — so what a caller carries there is the range law under
  another name and not a discharge of it — and the cocycle law, stated there as
  `ComplexAnalytic.RefineDatumCocycle`, in `Oka/Analytification/RefineDatumCocycle.lean`, from the
  original datum's own three laws and no further hypothesis.

  **`hrange`'s argument is a different one and it does transfer**, with the original datum's own
  `hrange` in place of the fixed member.
  `ComplexAnalytic.refineDatumTransitionHom_localisationProj_of_ne`
  (`Oka/Analytification/RefineDatumTransition.lean`) is the sentence it is read off — the refined
  transition lies over the original cover's own *transition*, there being no morphism between two
  members to lie over — and
  `ComplexAnalytic.range_refineDatumTransitionHom_subset_iff` says what is left at a triple whose
  three members are different: one containment, in the caller's own `D(q b c)`, and nothing more.
  Nothing *there* is evidence about the mixed triples, where the refined `glue` takes its equal
  branch; `Oka/Analytification/RefineDatumRange.lean` is what settles those, out of the equal
  branch's own triangle over a member.
* **No scheme and no `admissible`**, as in the three files this one sits beside.
-/

open CategoryTheory

universe u

namespace ComplexAnalytic

noncomputable section

variable {n k : ℕ} (g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ)

/-! ### Re-associating a double localisation over either factor -/

/-- **Two double localisations whose products agree are isomorphic**, over the member they both
sit in.

Localising at `x` and then at `y` is localising at `y·x`
(`ComplexAnalytic.localisationPresentationIsoMul`); so is localising at `x'` and then at `y'` when
`y'·x' = y·x`, and the two single localisations are then literally the same object. The transport
between them is an `eqToIso` and not a coherence isomorphism, because
`ComplexAnalytic.localisationPresentation` is applied to equal polynomials.

**This is the general form of the same-member glue.**
`ComplexAnalytic.refineGlue_eq_localisationPresentationIsoOfMulEq` below says
`ComplexAnalytic.refineGlue` is this at `x' = y` and `y' = x`, by `rfl`; what a cross-member
overlap needs instead is the case `x' = f`, where the object underneath becomes the original
overlap rather than the other refining open. -/
def localisationPresentationIsoOfMulEq (x y x' y' : MvPolynomial (ULift.{u} (Fin n)) ℂ)
    (h : y * x = y' * x') :
    (⟨n + 1 + 1, k + 1 + 1, localisationPresentation.{u} (localisationPresentation.{u} g x)
        (MvPolynomial.rename (localisationIncl.{u} n) y)⟩ : Presentation.{u}) ≅
      ⟨n + 1 + 1, k + 1 + 1, localisationPresentation.{u} (localisationPresentation.{u} g x')
        (MvPolynomial.rename (localisationIncl.{u} n) y')⟩ :=
  localisationPresentationIsoMul.{u} g x y ≪≫ eqToIso (by rw [h]) ≪≫
    (localisationPresentationIsoMul.{u} g x' y').symm

/-- **The triangle**: the re-association commutes with the two pairs of structure maps down to the
member.

The two outer steps are `ComplexAnalytic.localisationPresentationIsoMul_hom_comp` at each end and
the middle one is `ComplexAnalytic.eqToHom_localisationHom`, which is where the transport of the
first step is discharged. Its equality argument is passed explicitly rather than left to `rw`,
which would leave the polynomial equation as a second goal. -/
theorem localisationPresentationIsoOfMulEq_hom_comp
    (x y x' y' : MvPolynomial (ULift.{u} (Fin n)) ℂ) (h : y * x = y' * x') :
    (localisationPresentationIsoOfMulEq.{u} g x y x' y' h).hom ≫
        localisationHom.{u} (localisationPresentation.{u} g x')
          (MvPolynomial.rename (localisationIncl.{u} n) y') ≫ localisationHom.{u} g x' =
      localisationHom.{u} (localisationPresentation.{u} g x)
          (MvPolynomial.rename (localisationIncl.{u} n) y) ≫ localisationHom.{u} g x := by
  change (localisationPresentationIsoMul.{u} g x y ≪≫ eqToIso _ ≪≫
    (localisationPresentationIsoMul.{u} g x' y').symm).hom ≫ _ = _
  rw [Iso.trans_hom, Iso.trans_hom, Category.assoc, Category.assoc,
    ← localisationPresentationIsoMul_hom_comp.{u} g x' y', Iso.symm_hom,
    ← Category.assoc ((localisationPresentationIsoMul.{u} g x' y').inv), Iso.inv_hom_id,
    Category.id_comp, eqToIso.hom, eqToHom_localisationHom.{u} g h,
    localisationPresentationIsoMul_hom_comp]

/-- **The same-member glue is an instance of the re-association**, at `x' = y` and `y' = x`.

`ComplexAnalytic.refineGlue` is `ComplexAnalytic.refineMulIso` at both ends with the two products
identified by `mul_comm`, which is this definition with the two factors exchanged; the two terms
agree on the nose and the only difference between them is the proof of the polynomial equation,
which is irrelevant. Stated because it is the evidence that the general statement above is the
right generalisation rather than a second construction of the same shape. -/
theorem refineGlue_eq_localisationPresentationIsoOfMulEq {K : Type u}
    (fam : K → MvPolynomial (ULift.{u} (Fin n)) ℂ) (a b : K) :
    refineGlue.{u} g fam a b =
      localisationPresentationIsoOfMulEq.{u} g (fam a) (fam b) (fam b) (fam a)
        (mul_comm _ _) :=
  rfl

/-! ### Crossing to another member, and correcting the cutting polynomial -/

variable {n' k' : ℕ} (g' : Fin k' → MvPolynomial (ULift.{u} (Fin n')) ℂ)

/-- **The transport across an isomorphism of the bases, followed by a change of cutting polynomial
by a unit.**

`ComplexAnalytic.localisationPresentationIsoOfAlgEquiv` needs the class of `q` to go to the class
of the polynomial it localises at; a caller who obtains the second polynomial geometrically gets
one whose class agrees only up to a unit, which is the form
`ComplexAnalytic.exists_mk_rename_eq` produces. The intermediate `r` is where the two meet: `e`
carries the class of `q` to the class of `r` exactly, and `q'` is a unit multiple of `r`.

**Both hypotheses are on classes and not on polynomials**, for the reason
`ComplexAnalytic.localisationPresentationIsoOfAlgEquiv` gives: an isomorphism of presentations
gives a map of presented algebras and says nothing about polynomials.

`u`, `r` and the two hypotheses are arguments and not an existential, for the reason
`ComplexAnalytic.localisationPresentationIsoOfUnitMul`'s docstring sets out at length: a glue is
built out of the isomorphism rather than out of its existence, and two consumers holding the same
witnesses get the same isomorphism, which is what makes a coherence law between them
statable. -/
def localisationPresentationIsoOfAlgEquivUnitMul (q : MvPolynomial (ULift.{u} (Fin n)) ℂ)
    (r q' : MvPolynomial (ULift.{u} (Fin n')) ℂ)
    (e : PresentedAlgebra.{u} n k g ≃ₐ[ℂ] PresentedAlgebra.{u} n' k' g')
    (he : e (Ideal.Quotient.mk (presentationIdeal.{u} g) q) =
      Ideal.Quotient.mk (presentationIdeal.{u} g') r)
    (u : (PresentedAlgebra.{u} n' k' g')ˣ)
    (hu : Ideal.Quotient.mk (presentationIdeal.{u} g') q' =
      (u : PresentedAlgebra.{u} n' k' g') * Ideal.Quotient.mk (presentationIdeal.{u} g') r) :
    (⟨n + 1, k + 1, localisationPresentation.{u} g q⟩ : Presentation.{u}) ≅
      ⟨n' + 1, k' + 1, localisationPresentation.{u} g' q'⟩ :=
  localisationPresentationIsoOfAlgEquiv.{u} g q r e he ≪≫
    localisationPresentationIsoOfUnitMul.{u} g' r q' u hu

/-- **The triangle**: the composite is still one over the two members, and the unit correction
does not disturb that.

The two steps are `ComplexAnalytic.localisationPresentationIsoOfUnitMul_hom_comp`, which is over
the second member alone, and `ComplexAnalytic.localisationPresentationIsoOfAlgEquiv_hom_comp`,
which is the one that crosses. The right-hand factor is the isomorphism of the members that `e`
gives, so this is `ComplexAnalytic.localisationPresentationIsoOfDvdPow_hom_comp`'s statement with
the identity replaced by something with content. -/
theorem localisationPresentationIsoOfAlgEquivUnitMul_hom_comp
    (q : MvPolynomial (ULift.{u} (Fin n)) ℂ) (r q' : MvPolynomial (ULift.{u} (Fin n')) ℂ)
    (e : PresentedAlgebra.{u} n k g ≃ₐ[ℂ] PresentedAlgebra.{u} n' k' g')
    (he : e (Ideal.Quotient.mk (presentationIdeal.{u} g) q) =
      Ideal.Quotient.mk (presentationIdeal.{u} g') r)
    (u : (PresentedAlgebra.{u} n' k' g')ˣ)
    (hu : Ideal.Quotient.mk (presentationIdeal.{u} g') q' =
      (u : PresentedAlgebra.{u} n' k' g') * Ideal.Quotient.mk (presentationIdeal.{u} g') r) :
    (localisationPresentationIsoOfAlgEquivUnitMul.{u} g g' q r q' e he u hu).hom ≫
        localisationHom.{u} g' q' =
      localisationHom.{u} g q ≫ (Presentation.isoOfAlgEquiv e.symm).hom := by
  change (localisationPresentationIsoOfAlgEquiv.{u} g q r e he ≪≫
    localisationPresentationIsoOfUnitMul.{u} g' r q' u hu).hom ≫ _ = _
  rw [Iso.trans_hom, Category.assoc, localisationPresentationIsoOfUnitMul_hom_comp,
    localisationPresentationIsoOfAlgEquiv_hom_comp]

/-! ### The cross-member glue -/

/-- **A refined overlap, projected to the original overlap it sits inside.**

The refined member is `A_x` and the refined overlap is cut out of it by `f · q` read upstairs, so
it is `((A)_x)_{f·q}`; re-associated over `f` it is a localisation of the original overlap `A_f`,
and this is that description followed by the structure map. **It is the map a cross-member glue
is a morphism over**, because the original `glue` relates the two overlaps and nothing in the data
relates the two members. -/
def refineCrossProj (f x q : MvPolynomial (ULift.{u} (Fin n)) ℂ) :
    (⟨n + 1 + 1, k + 1 + 1, localisationPresentation.{u} (localisationPresentation.{u} g x)
        (MvPolynomial.rename (localisationIncl.{u} n) (f * q))⟩ : Presentation.{u}) ⟶
      ⟨n + 1, k + 1, localisationPresentation.{u} g f⟩ :=
  (localisationPresentationIsoOfMulEq.{u} g x (f * q) f (q * x) (by ring)).hom ≫
    localisationHom.{u} (localisationPresentation.{u} g f)
      (MvPolynomial.rename (localisationIncl.{u} n) (q * x))

/-- **The projection to the original overlap, followed down to the member, is the refined
overlap's own two structure maps.**

So nothing is lost by reading a refined overlap over the original overlap rather than over the
member: a consumer that wants the member-level statement composes this with
`ComplexAnalytic.refineCrossGlue_hom_comp`. It is
`ComplexAnalytic.localisationPresentationIsoOfMulEq_hom_comp` and the associativity of
composition. -/
theorem refineCrossProj_localisationHom (f x q : MvPolynomial (ULift.{u} (Fin n)) ℂ) :
    refineCrossProj.{u} g f x q ≫ localisationHom.{u} g f =
      localisationHom.{u} (localisationPresentation.{u} g x)
          (MvPolynomial.rename (localisationIncl.{u} n) (f * q)) ≫ localisationHom.{u} g x := by
  change ((localisationPresentationIsoOfMulEq.{u} g x (f * q) f (q * x) _).hom ≫ _) ≫ _ = _
  rw [Category.assoc, localisationPresentationIsoOfMulEq_hom_comp]

/-- **The glue of a cross-member refined overlap.**

`x` refines the member `A` and `x'` refines the member `A'`; the original cover's overlap of the
two members is `A_f` on one side and `A'_{f'}` on the other, and `e` is the isomorphism between
them that the original datum's `glue` gives. The refined overlap is cut out of `A_x` by `f · q`
and out of `A'_{x'}` by `f' · q'`, and this identifies the two.

Both sides are re-associated over the original overlap, the middle step crosses, and the unit
absorbs the difference between the polynomial the crossing produces and the one the other side
offers. **The original `glue` is read exactly once**, which is the sentence
`Oka/Analytification/CoverRefinement.lean` uses to say why this case is not a larger version of
the one it builds. -/
def refineCrossGlue (f x q : MvPolynomial (ULift.{u} (Fin n)) ℂ)
    (f' x' q' : MvPolynomial (ULift.{u} (Fin n')) ℂ)
    (r : MvPolynomial (ULift.{u} (Fin (n' + 1))) ℂ)
    (e : PresentedAlgebra.{u} (n + 1) (k + 1) (localisationPresentation.{u} g f) ≃ₐ[ℂ]
      PresentedAlgebra.{u} (n' + 1) (k' + 1) (localisationPresentation.{u} g' f'))
    (he : e (Ideal.Quotient.mk (presentationIdeal.{u} (localisationPresentation.{u} g f))
        (MvPolynomial.rename (localisationIncl.{u} n) (q * x))) =
      Ideal.Quotient.mk (presentationIdeal.{u} (localisationPresentation.{u} g' f')) r)
    (u : (PresentedAlgebra.{u} (n' + 1) (k' + 1) (localisationPresentation.{u} g' f'))ˣ)
    (hu : Ideal.Quotient.mk (presentationIdeal.{u} (localisationPresentation.{u} g' f'))
        (MvPolynomial.rename (localisationIncl.{u} n') (q' * x')) =
      (u : PresentedAlgebra.{u} (n' + 1) (k' + 1) (localisationPresentation.{u} g' f')) *
        Ideal.Quotient.mk (presentationIdeal.{u} (localisationPresentation.{u} g' f')) r) :
    (⟨n + 1 + 1, k + 1 + 1, localisationPresentation.{u} (localisationPresentation.{u} g x)
        (MvPolynomial.rename (localisationIncl.{u} n) (f * q))⟩ : Presentation.{u}) ≅
      ⟨n' + 1 + 1, k' + 1 + 1, localisationPresentation.{u} (localisationPresentation.{u} g' x')
        (MvPolynomial.rename (localisationIncl.{u} n') (f' * q'))⟩ :=
  localisationPresentationIsoOfMulEq.{u} g x (f * q) f (q * x) (by ring) ≪≫
    localisationPresentationIsoOfAlgEquivUnitMul.{u} (localisationPresentation.{u} g f)
      (localisationPresentation.{u} g' f')
      (MvPolynomial.rename (localisationIncl.{u} n) (q * x)) r
      (MvPolynomial.rename (localisationIncl.{u} n') (q' * x')) e he u hu ≪≫
    (localisationPresentationIsoOfMulEq.{u} g' x' (f' * q') f' (q' * x') (by ring)).symm

/-- **The coherence triangle of the cross-member glue**, and it is over the *original overlap*.

Going from one refined overlap to the other and then down to the original overlap of the second
member is going down to the original overlap of the first and crossing there. This is the
cross-member analogue of `ComplexAnalytic.refineGlue_comp`, with one difference that is not a
weakening: there the two structure maps have the same target, because every refined member lies
over one fixed member, and here they do not, because the two refined members lie over two
different ones. The right-hand factor is the isomorphism of the two original overlaps.

The proof is the two re-association steps cancelling against the projections they were built into
and `ComplexAnalytic.localisationPresentationIsoOfAlgEquivUnitMul_hom_comp` in the middle. The
`simp only` is `Category.assoc` and `CategoryTheory.Iso.inv_hom_id_assoc` and nothing else: the
inverse of the second re-association meets the copy of it inside
`ComplexAnalytic.refineCrossProj`, and what has to happen first is the reassociation of a
five-term composite. -/
theorem refineCrossGlue_hom_comp (f x q : MvPolynomial (ULift.{u} (Fin n)) ℂ)
    (f' x' q' : MvPolynomial (ULift.{u} (Fin n')) ℂ)
    (r : MvPolynomial (ULift.{u} (Fin (n' + 1))) ℂ)
    (e : PresentedAlgebra.{u} (n + 1) (k + 1) (localisationPresentation.{u} g f) ≃ₐ[ℂ]
      PresentedAlgebra.{u} (n' + 1) (k' + 1) (localisationPresentation.{u} g' f'))
    (he : e (Ideal.Quotient.mk (presentationIdeal.{u} (localisationPresentation.{u} g f))
        (MvPolynomial.rename (localisationIncl.{u} n) (q * x))) =
      Ideal.Quotient.mk (presentationIdeal.{u} (localisationPresentation.{u} g' f')) r)
    (u : (PresentedAlgebra.{u} (n' + 1) (k' + 1) (localisationPresentation.{u} g' f'))ˣ)
    (hu : Ideal.Quotient.mk (presentationIdeal.{u} (localisationPresentation.{u} g' f'))
        (MvPolynomial.rename (localisationIncl.{u} n') (q' * x')) =
      (u : PresentedAlgebra.{u} (n' + 1) (k' + 1) (localisationPresentation.{u} g' f')) *
        Ideal.Quotient.mk (presentationIdeal.{u} (localisationPresentation.{u} g' f')) r) :
    (refineCrossGlue.{u} g g' f x q f' x' q' r e he u hu).hom ≫
        refineCrossProj.{u} g' f' x' q' =
      refineCrossProj.{u} g f x q ≫ (Presentation.isoOfAlgEquiv e.symm).hom := by
  change (localisationPresentationIsoOfMulEq.{u} g x (f * q) f (q * x) _ ≪≫
      localisationPresentationIsoOfAlgEquivUnitMul.{u} (localisationPresentation.{u} g f)
        (localisationPresentation.{u} g' f')
        (MvPolynomial.rename (localisationIncl.{u} n) (q * x)) r
        (MvPolynomial.rename (localisationIncl.{u} n') (q' * x')) e he u hu ≪≫
      (localisationPresentationIsoOfMulEq.{u} g' x' (f' * q') f' (q' * x') _).symm).hom ≫
    ((localisationPresentationIsoOfMulEq.{u} g' x' (f' * q') f' (q' * x') _).hom ≫ _) =
      ((localisationPresentationIsoOfMulEq.{u} g x (f * q) f (q * x) _).hom ≫ _) ≫ _
  rw [Iso.trans_hom, Iso.trans_hom, Iso.symm_hom]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [localisationPresentationIsoOfAlgEquivUnitMul_hom_comp]

end

end ComplexAnalytic
