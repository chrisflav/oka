/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Analytification.LocalisationFunctor
import Oka.RingTheory.Localization.Away.Basic

/-!
# The presentation of a distinguished open depends on the polynomial only up to a unique iso

`ComplexAnalytic.localisationPresentation g f` adjoins a variable and the equation `t·f - 1`, so
the polynomial `f` occurs in the *type* of everything built from it: two polynomials cutting out
the same distinguished open give two different objects of `ComplexAnalytic.Presentation` and two
different analytic spaces. This file says they are canonically the same one.

The first four statements identify the two presentations and put the identification over the
member; the next four are about the case where the two polynomials differ by a **unit**, and about
where such a pair comes from; the three after those vary the base rather than the polynomial;
and the last group is about the one polynomial there is nothing to say about, `f = 1`:

* `ComplexAnalytic.localisationPresentationIsoOfDvdPow` — **the presentations of the localisation
  at `f` and at `f'` are isomorphic** whenever the images of `f` and `f'` in `A` each divide a
  power of the other, which is the algebraic form of *"`f` and `f'` cut out the same distinguished
  open"*.
* `ComplexAnalytic.localisationPresentedAlgebraEquiv_localisationRingHom` — **the identification
  with `Localization.Away` commutes with the structure map** `A ⟶ A_f`. This is what makes the
  first isomorphism canonical rather than merely available, and it is proved without an
  `Algebra (ComplexAnalytic.PresentedAlgebra n k g)` instance on the localised presented algebra:
  see *The shape this settles* below.
* `ComplexAnalytic.localisationPresentedAlgebraEquivOfDvdPow_localisationRingHom` — **the
  isomorphism of the first bullet is one of `A`-algebras**: it carries `A ⟶ A_f` to `A ⟶ A_{f'}`.
  Without this the two structure maps are unrelated and the isomorphism, though canonical, says
  nothing about the presentations *as distinguished opens of the same member*.
* `ComplexAnalytic.localisationPresentationIsoOfDvdPow_hom_comp` — **the triangle**: the same
  statement in `ComplexAnalytic.Presentation`, as an equation between morphisms. This is the form
  a coherence law consumes, and it is the sense in which a transition morphism built from a
  witness does not depend on the witness.
* `ComplexAnalytic.localisationPresentationIsoOfUnitMul` and
  `ComplexAnalytic.localisationPresentationIsoOfUnitMul_hom_comp` — **the same two at a unit
  multiple**, which is the pair of divisibilities at exponent one and is the form the statement
  below produces.
* `ComplexAnalytic.isUnit_mk_rename_localisationIncl` — **the polynomial that was inverted is a
  unit upstairs**, which is the last equation of `ComplexAnalytic.localisationPresentation` read
  as an invertibility.
* `ComplexAnalytic.exists_mk_rename_eq` — **every polynomial of a localisation is a unit multiple
  of a renamed polynomial of the base.** This is the algebraic form of
  `ComplexAnalytic.exists_localisationOpen_eq_rename`, whose geometric conclusion discards the
  unit; the unit is what the isomorphism above needs and what an equality of non-vanishing loci
  does not give.
* `ComplexAnalytic.localisationPresentedAlgebraEquivOfAlgEquiv_localisationRingHom` — **and that
  identification of two localised algebras is one over the two members**: it carries `A ⟶ A_q` to
  `A' ⟶ A'_{q'}` composed with the isomorphism of the members. It stands to the bullet below as
  `ComplexAnalytic.localisationPresentedAlgebraEquivOfDvdPow_localisationRingHom` stands to the
  first, and it is the half with content for the same reason: an isomorphism of two localisations
  compatible with nothing identifies two objects and relates nothing.
* `ComplexAnalytic.localisationPresentationIsoOfAlgEquiv` and
  `ComplexAnalytic.localisationPresentationIsoOfAlgEquiv_hom_comp` — **the base moves too**: an
  isomorphism of two presented algebras carrying one cutting polynomial to the other identifies
  the two localisations, over that isomorphism. Everything before this keeps the base fixed, and a
  cross-member overlap of a refined cover is the case where it does not.
* `ComplexAnalytic.isIso_localisationHom_one` — **localising at `1` changes nothing**: the
  structure map `A ⟶ A_1` is an isomorphism in `ComplexAnalytic.Presentation`, so the
  presentation of `D(1)` is the base's own up to canonical isomorphism even though it carries an
  extra variable and an extra equation. `ComplexAnalytic.bijective_localisationRingHom_one` is
  the ring-level half and `ComplexAnalytic.localisationIsoOne` the isomorphism the instance
  names. For a general `f` the statement is false, which is
  `ComplexAnalytic.localisationOpen_ne_top`.

## Where this is needed

Taxis #996. `Mathlib/AlgebraicGeometry/Cover/Directed.lean`'s locally directed cover — the shape
a scheme actually supplies, and the one
`Mathlib/AlgebraicGeometry/Sites/SmallAffineZariski.lean` instantiates for every scheme with no
hypotheses — indexes the members of a cover by a *category* and asks for a transition morphism per
**arrow**. An arrow of that index category is a proof of `∃ f, X.basicOpen f = U`, and it is
proof-irrelevant: the section `f` witnessing it is neither recoverable from it nor unique. On this
side the polynomial is in the type, so a transition built from a witness has to be shown
independent of the witness. That is the first statement above.

## The shape this settles, and it is a choice among two

Building the analytification of a locally directed cover can be done **choice-first** — pick a
presentation for each member and a witness for each arrow, then prove the functoriality laws up to
the coherence isomorphisms — or **choice-free**, building each member as a colimit over all its
presentations so that no choice is made and the laws hold on the nose.

**Choice-first, and the reason is stronger than "the choices are isomorphic".** The isomorphism
`ComplexAnalytic.localisationPresentedAlgebraEquivOfDvdPow` is
`IsLocalization.algEquiv`, transported: it is not *an* isomorphism between the two localisations
but **the unique `A`-algebra map** between them, since both are localisations of `A` at the same
saturated submonoid. Uniqueness is what discharges a coherence law, and it is available here
because the second statement above puts the identification over `A` rather than only over `ℂ`. The
colimit construction would buy the same laws at the price of machinery this development has no
other use for.

## What is not here

**No transition morphism, and no locally directed cover.** Nothing below mentions
`AlgebraicGeometry.Scheme`, and the file adds no Mathlib import: `Cover/Directed.lean` is not
imported, so its declarations cannot even be named in a docstring here — which is why the two
Mathlib files above are cited by path.

**No composite of two localisations.** The second half of taxis #996 is that the witness of a
composite arrow is a third polynomial, and its algebra is `IsLocalization.Away.mul`, already in
Mathlib. What is missing is the transport of that statement to
`ComplexAnalytic.localisationPresentation`, and the obstruction is recorded in
`Oka/Analytification/DistinguishedOpen.lean`'s docstring for
`ComplexAnalytic.localisationPresentedAlgebraEquiv`: there is deliberately no
`Algebra (ComplexAnalytic.PresentedAlgebra n k g)` instance on the localised presented algebra,
so `IsLocalization.Away.mul` cannot be applied to it directly. The compatibility proved here is
what such a transport would be built from.
-/

open CategoryTheory MvPolynomial

namespace ComplexAnalytic

universe u

variable {n k : ℕ} (g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ)
  (f f' : MvPolynomial (ULift.{u} (Fin n)) ℂ)

/-! ### The identification is over `A`, not only over `ℂ` -/

/-- **The reindexing of the variables carries the structure map to `MvPolynomial.awayBaseHom`.**

Both sides send the class of `p` to the class of `MvPolynomial.rename some p`: on the left the
renaming is `ComplexAnalytic.localisationIncl` followed by
`ComplexAnalytic.localisationVarEquiv`, which is `some` by
`ComplexAnalytic.localisationVarEquiv_localisationIncl`. -/
theorem localisationRenameEquiv_localisationRingHom (x : PresentedAlgebra.{u} n k g) :
    localisationRenameEquiv.{u} g f (localisationRingHom.{u} g f x) =
      MvPolynomial.awayBaseHom (presentationIdeal.{u} g) f x := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  change localisationRenameEquiv.{u} g f
    ((PresHom.ofRename.{u} (localisationIncl.{u} n) _).toRingHom _) = _
  simp [localisationRenameEquiv, PresHom.ofRename, MvPolynomial.awayBaseHom,
    MvPolynomial.rename_rename, Function.comp_def]

/-- **`ComplexAnalytic.localisationPresentedAlgebraEquiv` commutes with the structure map**: the
identification of `ℂ[x, t] ⧸ (g, t·f - 1)` with `Localization.Away` is an isomorphism *over* `A`,
and not merely over `ℂ`.

This is the statement that lets a consumer use the universal property of the localisation on
anything built from `ComplexAnalytic.localisationRingHom` — for instance to see that two
descriptions of the same distinguished open agree over the member they sit in — without an
`Algebra (ComplexAnalytic.PresentedAlgebra n k g)` instance being introduced on the localised
presented algebra, which `Oka/Analytification/DistinguishedOpen.lean` deliberately avoids. -/
theorem localisationPresentedAlgebraEquiv_localisationRingHom (x : PresentedAlgebra.{u} n k g) :
    localisationPresentedAlgebraEquiv.{u} g f (localisationRingHom.{u} g f x) =
      algebraMap (PresentedAlgebra.{u} n k g)
        (Localization.Away (Ideal.Quotient.mk (presentationIdeal.{u} g) f)) x := by
  change MvPolynomial.awayQuotientEquiv _ _ (localisationRenameEquiv.{u} g f _) = _
  rw [localisationRenameEquiv_localisationRingHom, MvPolynomial.awayQuotientEquiv_apply,
    MvPolynomial.awayLift_awayBaseHom]

/-! ### Two polynomials cutting out the same distinguished open -/

variable (h : ∃ N, Ideal.Quotient.mk (presentationIdeal.{u} g) f' ∣
    Ideal.Quotient.mk (presentationIdeal.{u} g) f ^ N)
  (h' : ∃ M, Ideal.Quotient.mk (presentationIdeal.{u} g) f ∣
    Ideal.Quotient.mk (presentationIdeal.{u} g) f' ^ M)

include h h' in
/-- **The two presented algebras are isomorphic**, when the images of `f` and `f'` in `A` each
divide a power of the other.

The middle step is `IsLocalization.Away.algEquivOfDvdPow`, which is an isomorphism over `A`; it is
restricted to `ℂ` only because `ComplexAnalytic.Presentation` is a category of `ℂ`-algebras. It is
the unique `A`-algebra map between the two localisations, so nothing about this isomorphism is
chosen. -/
noncomputable def localisationPresentedAlgebraEquivOfDvdPow :
    PresentedAlgebra.{u} (n + 1) (k + 1) (localisationPresentation.{u} g f) ≃ₐ[ℂ]
      PresentedAlgebra.{u} (n + 1) (k + 1) (localisationPresentation.{u} g f') :=
  (localisationPresentedAlgebraEquiv.{u} g f).trans
    (((IsLocalization.Away.algEquivOfDvdPow _ _ h h').restrictScalars ℂ).trans
      (localisationPresentedAlgebraEquiv.{u} g f').symm)

include h h' in
/-- **The two presentations are isomorphic objects of `ComplexAnalytic.Presentation`**, hence have
isomorphic analytifications, by `ComplexAnalytic.analytificationFunctor`.

This is what says a transition morphism built from a *witness* that two members overlap in a
distinguished open does not depend on the witness. -/
noncomputable def localisationPresentationIsoOfDvdPow :
    (⟨n + 1, k + 1, localisationPresentation.{u} g f⟩ : Presentation.{u}) ≅
      ⟨n + 1, k + 1, localisationPresentation.{u} g f'⟩ :=
  Presentation.isoOfAlgEquiv (localisationPresentedAlgebraEquivOfDvdPow.{u} g f f' h h').symm

/-! ### The identification of two witnesses is over `A` -/

include h h' in
/-- **The witness-independence isomorphism carries one structure map to the other**: the image
of `A ⟶ A_f` is `A ⟶ A_{f'}`, on the nose.

`ComplexAnalytic.localisationPresentedAlgebraEquivOfDvdPow`'s docstring says it is *the unique
`A`-algebra map* between the two localisations. This is that fact in the form a consumer can use:
`IsLocalization.Away.algEquivOfDvdPow` is an `A`-algebra map by construction, and the two outer
steps are `ComplexAnalytic.localisationPresentedAlgebraEquiv_localisationRingHom`, which is what
puts the identification with `Localization.Away` over `A` rather than only over `ℂ`.

**Without this the isomorphism is compatible with nothing.** Two presentations of the same
distinguished open are interesting only as opens *of the member they sit in*, and the member
enters solely through the structure map. -/
theorem localisationPresentedAlgebraEquivOfDvdPow_localisationRingHom
    (x : PresentedAlgebra.{u} n k g) :
    localisationPresentedAlgebraEquivOfDvdPow.{u} g f f' h h' (localisationRingHom.{u} g f x) =
      localisationRingHom.{u} g f' x := by
  rw [localisationPresentedAlgebraEquivOfDvdPow, AlgEquiv.trans_apply,
    localisationPresentedAlgebraEquiv_localisationRingHom, AlgEquiv.trans_apply,
    AlgEquiv.restrictScalars_apply, AlgEquiv.commutes,
    ← localisationPresentedAlgebraEquiv_localisationRingHom, AlgEquiv.symm_apply_apply]

include h h' in
/-- **The triangle**: the two structure maps agree once the two presentations are identified by
`ComplexAnalytic.localisationPresentationIsoOfDvdPow`.

This is the sense in which a transition morphism built from a *witness* that one member is a
distinguished open of another does not depend on the witness: replacing `f` by any `f'` cutting
out the same open changes the morphism `A_f ⟶ A` only by composition with the coherence
isomorphism. It is the shape a coherence law consumes, and it is
`ComplexAnalytic.localisationPresentedAlgebraEquivOfDvdPow_localisationRingHom` read through
`ComplexAnalytic.PresHom.ext` — the companion of
`ComplexAnalytic.localisationPresentationIsoMul_hom_comp`, which does the same for the other
half of the arrow story. -/
theorem localisationPresentationIsoOfDvdPow_hom_comp :
    (localisationPresentationIsoOfDvdPow.{u} g f f' h h').hom ≫ localisationHom.{u} g f' =
      localisationHom.{u} g f := by
  refine PresHom.ext (RingHom.ext fun x ↦ ?_)
  change (localisationPresentedAlgebraEquivOfDvdPow.{u} g f f' h h').symm
    (localisationRingHom.{u} g f' x) = _
  rw [AlgEquiv.symm_apply_eq]
  exact (localisationPresentedAlgebraEquivOfDvdPow_localisationRingHom.{u} g f f' h h' x).symm

/-! ### Associates, and the polynomials of a localisation up to one

The hypotheses of `ComplexAnalytic.localisationPresentationIsoOfDvdPow` are two divisibilities of
*powers*, which is the weakest form that still gives the isomorphism. The two statements below are
about the case where one polynomial is a **unit multiple** of the other — both divisibilities at
exponent one — and about where such a pair comes from.

**Where it comes from is the point.** `ComplexAnalytic.exists_pow_mul_eq_rename`
(`Oka/Analytification/DistinguishedOpen.lean`) proves an equation in the polynomial ring, and
`ComplexAnalytic.exists_localisationOpen_eq_rename` reads off the geometric half of it: two
polynomials cut out the same open. **That discards the algebra**, and the algebra is what a
transition morphism needs — an equality of non-vanishing loci does not give a divisibility over a
general presented `ℂ`-algebra, which would be a Nullstellensatz statement and is proved nowhere
here. Read modulo the ideal, the same equation says the two polynomials are *associates*, and that
is what `ComplexAnalytic.exists_mk_rename_eq` records.
-/

/-- **A unit multiple gives the isomorphism**, at exponent one in both directions.

`ComplexAnalytic.localisationPresentationIsoOfDvdPow` asks for `∃ N, q' ∣ q ^ N` and its mirror;
a unit multiple gives both with `N = M = 1`, since `q = q' * u⁻¹` and `q' = q * u`.

**Why this is a `def` taking `u` and `hu`, and not `∃ Q, Nonempty (_ ≅ _)`.** The existence form
is the one a spike writes, because it is one statement; it is the wrong one here, and the reason
is what the arguments buy rather than a preference for data over propositions:

* **A glue is built out of the isomorphism, not out of its existence.** A cover datum's `glue`
  field is an `Iso`, and `ComplexAnalytic.coverTransition` transports it; `Nonempty` gives a
  consumer nothing to transport, and `Classical.choice` on it would produce an isomorphism no
  second consumer could recognise as the same one.
* **The witness is what makes two calls agree.** Two consumers holding the same `Q`, `u` and `hu`
  get the *same* isomorphism here, so a coherence law between them is statable; an existential
  re-chosen at each call site is not, and coherence between two transitions is the whole content
  of the laws such a datum has to satisfy.
* **The triangle needs the same arguments.**
  `ComplexAnalytic.localisationPresentationIsoOfUnitMul_hom_comp` below is about *this*
  isomorphism at *these* arguments, and it is what says it is one over the member the two opens
  sit in.

`ComplexAnalytic.exists_mk_rename_eq` is where the three arguments come from, and the split
between the two is exactly `ComplexAnalytic.localisationPresentationIsoOfDvdPow`'s own: a `def`
taking hypotheses, and a separate existence producing them. -/
noncomputable def localisationPresentationIsoOfUnitMul (q q' : MvPolynomial (ULift.{u} (Fin n)) ℂ)
    (u : (PresentedAlgebra.{u} n k g)ˣ)
    (hu : Ideal.Quotient.mk (presentationIdeal.{u} g) q' =
      (u : PresentedAlgebra.{u} n k g) * Ideal.Quotient.mk (presentationIdeal.{u} g) q) :
    (⟨n + 1, k + 1, localisationPresentation.{u} g q⟩ : Presentation.{u}) ≅
      ⟨n + 1, k + 1, localisationPresentation.{u} g q'⟩ :=
  localisationPresentationIsoOfDvdPow.{u} g q q'
    ⟨1, ((u⁻¹ : (PresentedAlgebra.{u} n k g)ˣ) : PresentedAlgebra.{u} n k g), by
      rw [pow_one, hu, mul_comm (u : PresentedAlgebra.{u} n k g), mul_assoc, ← Units.val_mul,
        mul_inv_cancel, Units.val_one, mul_one]⟩
    ⟨1, (u : PresentedAlgebra.{u} n k g), by rw [pow_one, hu, mul_comm]⟩

/-- **The triangle**, for the isomorphism above: it is one over the member the two opens sit in.

`ComplexAnalytic.localisationPresentationIsoOfDvdPow_hom_comp` at the two divisibilities the
definition supplies, and it is stated rather than left to a consumer to unfold: an isomorphism
that is not over the base identifies two objects and relates nothing, which is the distinction
`ComplexAnalytic.localisationPresentedAlgebraEquivOfDvdPow_localisationRingHom` above exists to
make. -/
theorem localisationPresentationIsoOfUnitMul_hom_comp (q q' : MvPolynomial (ULift.{u} (Fin n)) ℂ)
    (u : (PresentedAlgebra.{u} n k g)ˣ)
    (hu : Ideal.Quotient.mk (presentationIdeal.{u} g) q' =
      (u : PresentedAlgebra.{u} n k g) * Ideal.Quotient.mk (presentationIdeal.{u} g) q) :
    (localisationPresentationIsoOfUnitMul.{u} g q q' u hu).hom ≫ localisationHom.{u} g q' =
      localisationHom.{u} g q :=
  localisationPresentationIsoOfDvdPow_hom_comp.{u} g q q' _ _

/-- **The polynomial that was inverted is a unit upstairs**, which is the whole content of the
last equation of `ComplexAnalytic.localisationPresentation`: `t · f = 1` in the presented algebra,
read as an invertibility rather than as a relation.

Everything below is this fact and `ComplexAnalytic.exists_pow_mul_eq_rename`. -/
theorem isUnit_mk_rename_localisationIncl :
    IsUnit (Ideal.Quotient.mk (presentationIdeal.{u} (localisationPresentation.{u} g f))
      (MvPolynomial.rename (localisationIncl.{u} n) f)) := by
  have key : (Ideal.Quotient.mk (presentationIdeal.{u} (localisationPresentation.{u} g f))
      (MvPolynomial.rename (localisationIncl.{u} n) f)) *
        Ideal.Quotient.mk _ (MvPolynomial.X (localisationVar.{u} n)) = 1 := by
    rw [← map_mul, ← sub_eq_zero, ← map_one (Ideal.Quotient.mk _), ← map_sub,
      Ideal.Quotient.eq_zero_iff_mem]
    refine Ideal.subset_span ⟨Fin.last k, ?_⟩
    rw [localisationPresentation_last]
    ring
  exact isUnit_iff_exists.2 ⟨_, key, by rw [mul_comm]; exact key⟩

/-- **Every polynomial of a localisation is a unit multiple of a renamed one**, in the presented
algebra — the algebraic form of `ComplexAnalytic.exists_localisationOpen_eq_rename`.

`ComplexAnalytic.exists_pow_mul_eq_rename` is the equation in the polynomial ring; modulo the
ideal its correction term dies, and what is left is `mk (rename Q) = uᴰ · mk q` with
`u = mk (rename f)` the unit above. **`D` survives here where the geometric form drops it**: a
non-vanishing locus does not see a non-vanishing factor, but a divisibility does, and the unit is
what a consumer feeds to `ComplexAnalytic.localisationPresentationIsoOfUnitMul`.

The two statements are not interchangeable, and the direction that fails is worth naming: this
one gives the equality of opens (a unit does not vanish), and the equality of opens does **not**
give this one — over a general presented `ℂ`-algebra that implication is a Nullstellensatz
statement and nothing in this repository proves it. -/
theorem exists_mk_rename_eq (q : MvPolynomial (ULift.{u} (Fin (n + 1))) ℂ) :
    ∃ (Q : MvPolynomial (ULift.{u} (Fin n)) ℂ) (u : (PresentedAlgebra.{u} (n + 1) (k + 1)
        (localisationPresentation.{u} g f))ˣ),
      Ideal.Quotient.mk (presentationIdeal.{u} (localisationPresentation.{u} g f))
          (MvPolynomial.rename (localisationIncl.{u} n) Q) =
        (u : PresentedAlgebra.{u} (n + 1) (k + 1) (localisationPresentation.{u} g f)) *
          Ideal.Quotient.mk (presentationIdeal.{u} (localisationPresentation.{u} g f)) q := by
  obtain ⟨D, Q, r, h⟩ := exists_pow_mul_eq_rename.{u} f q
  obtain ⟨u, hu⟩ := isUnit_mk_rename_localisationIncl.{u} g f
  refine ⟨Q, u ^ D, ?_⟩
  have hrel : Ideal.Quotient.mk (presentationIdeal.{u} (localisationPresentation.{u} g f))
      (MvPolynomial.X (localisationVar.{u} n) *
        MvPolynomial.rename (localisationIncl.{u} n) f - 1) = 0 :=
    (Ideal.Quotient.eq_zero_iff_mem).2 (Ideal.subset_span
      ⟨Fin.last k, localisationPresentation_last.{u} g f⟩)
  have hq := congrArg (Ideal.Quotient.mk
    (presentationIdeal.{u} (localisationPresentation.{u} g f))) h
  rw [map_mul, map_pow, map_add, map_mul, hrel, zero_mul, add_zero, ← hu] at hq
  rw [← hq, Units.val_pow_eq_pow_val]

/-! ### Two presentations identified, and the localisations carried across

Everything above keeps the **base** fixed and varies the polynomial. This section varies the base:
given an isomorphism of two presented algebras carrying one cutting polynomial to the other, the
two localisations are isomorphic over it.

**That is the case a cross-member overlap is in.** In `ComplexAnalytic.coverGlueData'` the overlap
of two members is presented once on each side and the datum's `glue` identifies the two — an
isomorphism of two *different* presentations. Refining such a cover localises both sides again,
and nothing above can cross between them, because every statement above is about one base.

The commutative algebra is Mathlib's: `IsLocalization.algEquivOfAlgEquiv` transports a
localisation along an isomorphism of the bases matching the submonoids, and for
`Localization.Away` the submonoid condition is `Submonoid.map_powers`, a `simp` lemma. What is
here is the transport of that statement to this development's presentations, and the fact that it
is one **over the two members**, which is what the isomorphism is used for and what the
isomorphism alone does not say.
-/

section Transport

variable {n' k' : ℕ} {g' : Fin k' → MvPolynomial (ULift.{u} (Fin n')) ℂ}
  (q : MvPolynomial (ULift.{u} (Fin n)) ℂ) (q' : MvPolynomial (ULift.{u} (Fin n')) ℂ)
  (e : PresentedAlgebra.{u} n k g ≃ₐ[ℂ] PresentedAlgebra.{u} n' k' g')
  (he : e (Ideal.Quotient.mk (presentationIdeal.{u} g) q) =
    Ideal.Quotient.mk (presentationIdeal.{u} g') q')

include he in
/-- **The two localised presented algebras are isomorphic**, when an isomorphism of the bases
carries the class of `q` to the class of `q'`.

`ComplexAnalytic.localisationPresentedAlgebraEquiv` at each end and
`IsLocalization.algEquivOfAlgEquiv` in the middle. The hypothesis is stated on the **classes** and
not on the polynomials, because that is the form it arrives in: an isomorphism of presentations
gives a map of presented algebras and says nothing about polynomials.

The hypothesis is what fixes the isomorphism: `q'` is not determined by `e` and `q`, only its
class is, and two polynomials with the same class give the same statement. -/
noncomputable def localisationPresentedAlgebraEquivOfAlgEquiv :
    PresentedAlgebra.{u} (n + 1) (k + 1) (localisationPresentation.{u} g q) ≃ₐ[ℂ]
      PresentedAlgebra.{u} (n' + 1) (k' + 1) (localisationPresentation.{u} g' q') :=
  (localisationPresentedAlgebraEquiv.{u} g q).trans
    ((IsLocalization.algEquivOfAlgEquiv
        (M := Submonoid.powers (Ideal.Quotient.mk (presentationIdeal.{u} g) q))
        (T := Submonoid.powers (Ideal.Quotient.mk (presentationIdeal.{u} g') q'))
        (Localization.Away (Ideal.Quotient.mk (presentationIdeal.{u} g) q))
        (Localization.Away (Ideal.Quotient.mk (presentationIdeal.{u} g') q')) e
        (by simp [he])).trans
      (localisationPresentedAlgebraEquiv.{u} g' q').symm)

include he in
/-- **And the isomorphism is one over the two members**: it carries the structure map `A ⟶ A_q` to
`A' ⟶ A'_{q'}` composed with `e`.

The companion of `ComplexAnalytic.localisationPresentedAlgebraEquivOfDvdPow_localisationRingHom`,
which says the same for two witnesses over one member, and it is the half with content for the
same reason: an isomorphism of two localisations that is compatible with nothing identifies two
objects and relates nothing. The two outer steps are
`ComplexAnalytic.localisationPresentedAlgebraEquiv_localisationRingHom` and the middle one is
`IsLocalization.algEquivOfAlgEquiv_eq`.

**The first step is a `change` and not a `rw` at the definition above**, which is the one
difference from the proof of the `OfDvdPow` companion. A `rw` at a definition generates an
auto-generated equation lemma for it, under the definition's own name, and the environment carries
`ComplexAnalytic.localisationPresentedAlgebraEquivOfDvdPow.eq_1` for exactly that reason. **The
declaration dump is what shows such a lemma and the build is not** — `comm -13` on
`scripts/DumpOkaDecls.lean`'s output. The `change` costs the two submonoids written out and leaves
the environment with the four declarations of this section and nothing else.

(This paragraph used to add that a generated `eq_1` switches off
`scripts/check_docstring_names.py`'s field-notation rule for that name. **It does not**: that
script's `GENERATED_COMPONENT` excludes `eq_\d+` from the namespace test, and its own self-test
checks assert the exclusion. The hazard was real and was closed before this file was
written; the reason for the `change` is the dump and nothing else.) -/
theorem localisationPresentedAlgebraEquivOfAlgEquiv_localisationRingHom
    (x : PresentedAlgebra.{u} n k g) :
    localisationPresentedAlgebraEquivOfAlgEquiv.{u} g q q' e he
        (localisationRingHom.{u} g q x) =
      localisationRingHom.{u} g' q' (e x) := by
  have hx : localisationPresentedAlgebraEquiv.{u} g q (localisationRingHom.{u} g q x) =
      algebraMap (PresentedAlgebra.{u} n k g)
        (Localization.Away (Ideal.Quotient.mk (presentationIdeal.{u} g) q)) x :=
    localisationPresentedAlgebraEquiv_localisationRingHom.{u} g q x
  change (localisationPresentedAlgebraEquiv.{u} g' q').symm
    (IsLocalization.algEquivOfAlgEquiv
      (M := Submonoid.powers (Ideal.Quotient.mk (presentationIdeal.{u} g) q))
      (T := Submonoid.powers (Ideal.Quotient.mk (presentationIdeal.{u} g') q'))
      (Localization.Away (Ideal.Quotient.mk (presentationIdeal.{u} g) q))
      (Localization.Away (Ideal.Quotient.mk (presentationIdeal.{u} g') q')) e (by simp [he])
      (localisationPresentedAlgebraEquiv.{u} g q (localisationRingHom.{u} g q x))) = _
  rw [hx, IsLocalization.algEquivOfAlgEquiv_eq,
    ← localisationPresentedAlgebraEquiv_localisationRingHom, AlgEquiv.symm_apply_apply]

include he in
/-- **The two localisations are isomorphic objects of `ComplexAnalytic.Presentation`**, hence have
isomorphic analytifications through `ComplexAnalytic.analytificationFunctor`.

A consumer holding an isomorphism of *presentations* rather than of algebras — which is the shape
a cover datum's glue field is in — reaches this through
`ComplexAnalytic.Presentation.algEquivOfIso`. -/
noncomputable def localisationPresentationIsoOfAlgEquiv :
    (⟨n + 1, k + 1, localisationPresentation.{u} g q⟩ : Presentation.{u}) ≅
      ⟨n' + 1, k' + 1, localisationPresentation.{u} g' q'⟩ :=
  Presentation.isoOfAlgEquiv (localisationPresentedAlgebraEquivOfAlgEquiv.{u} g q q' e he).symm

include he in
/-- **The triangle**: the isomorphism of the localisations sits over the isomorphism of the
members.

`ComplexAnalytic.localisationPresentationIsoOfDvdPow_hom_comp` is the same statement when the two
members are one and the same and the right-hand factor is the identity; here the members are two
and the factor is the isomorphism between them. It is what a coherence law consumes, and it is
`ComplexAnalytic.localisationPresentedAlgebraEquivOfAlgEquiv_localisationRingHom` read through
`ComplexAnalytic.PresHom.ext`. -/
theorem localisationPresentationIsoOfAlgEquiv_hom_comp :
    (localisationPresentationIsoOfAlgEquiv.{u} g q q' e he).hom ≫ localisationHom.{u} g' q' =
      localisationHom.{u} g q ≫ (Presentation.isoOfAlgEquiv e.symm).hom := by
  refine PresHom.ext (RingHom.ext fun x ↦ ?_)
  change (localisationPresentedAlgebraEquivOfAlgEquiv.{u} g q q' e he).symm
    (localisationRingHom.{u} g' q' x) = localisationRingHom.{u} g q (e.symm x)
  rw [AlgEquiv.symm_apply_eq, localisationPresentedAlgebraEquivOfAlgEquiv_localisationRingHom,
    AlgEquiv.apply_symm_apply]

end Transport

/-! ### The degenerate polynomial: localising at `1` changes nothing

Every statement above keeps `f` general and compares two localisations. This section is about the
one polynomial for which there is nothing to compare: at `f = 1` the distinguished open is the
whole member, and the presentation `ComplexAnalytic.localisationPresentation g 1` — which still
carries an extra variable and an extra equation — presents the base algebra itself.

**The extra variable does not go away and that is the point.** The adjoined equation at `f = 1` is
`X_last * 1 - 1` and not `X_last - 1`; the object below is genuinely `⟨n + 1, k + 1, …⟩` and is
isomorphic to `⟨n, k, g⟩` rather than equal to it, which is why the conclusion is an `IsIso` and
not a `rfl`.

**Why the route goes through the algebras.** The inverse has to send the adjoined variable to the
constant `1`, and `ComplexAnalytic.PresHom.ofRename` sends variables to variables — this
repository has no `ComplexAnalytic.PresHom` constructor for a polynomial substitution, as
`Oka/Analytification/ChangeOfVariables.lean` records. `ComplexAnalytic.Presentation.isoOfAlgEquiv`
is what avoids writing one, and it puts no constraint on the two variable counts. -/

/-- **The structure map `A ⟶ A_1` is bijective.**

`IsLocalization.atUnits` at the powers of the class of `1`, whose generator is a unit because
`map_one` makes it `1`; then `ComplexAnalytic.localisationPresentedAlgebraEquiv` is cancelled on
the left, which is legitimate exactly because
`ComplexAnalytic.localisationPresentedAlgebraEquiv_localisationRingHom` puts that identification
over `A` and not merely over `ℂ`. This is a consumer of that lemma of the kind its own docstring
anticipates.

**`IsLocalization.atOne` is the closer-looking fit and is not the one.** It asks for the instance
`IsLocalization.Away (1 : R) S` with a syntactic `1`, where the object here is
`Localization.Away (Ideal.Quotient.mk _ 1)`; `IsLocalization.atUnits` takes the submonoid
explicitly and its side condition falls to one `rw` chain. A reader who reaches for `atOne` should
expect an *instance* failure rather than a proof failure.

**The `have`s are not collapsible into a `simp` for free.**
`ComplexAnalytic.localisationPresentedAlgebraEquiv` and `ComplexAnalytic.localisationRingHom` are
`def`s, and naming either as a rewrite rule generates its equation lemma into this module — the
hazard `Oka/Analytification/RefineDatumCocycle.lean` records at its own `rw`s. It is recorded in
many files here and counting them is not worth the sentence. The step is stated as a `funext` of
the existing lemma for that reason. -/
theorem bijective_localisationRingHom_one :
    Function.Bijective (localisationRingHom.{u} g 1) := by
  have h1 : Ideal.Quotient.mk (presentationIdeal.{u} g) (1 : MvPolynomial (ULift.{u} (Fin n)) ℂ)
      = 1 := map_one _
  have hb : Function.Bijective
      (algebraMap (PresentedAlgebra.{u} n k g)
        (Localization.Away (Ideal.Quotient.mk (presentationIdeal.{u} g)
          (1 : MvPolynomial (ULift.{u} (Fin n)) ℂ)))) := by
    refine (IsLocalization.atUnits (PresentedAlgebra.{u} n k g)
      (Submonoid.powers (Ideal.Quotient.mk (presentationIdeal.{u} g)
        (1 : MvPolynomial (ULift.{u} (Fin n)) ℂ))) ?_).bijective
    rw [Submonoid.powers_eq_closure, Submonoid.closure_le, Set.singleton_subset_iff, h1]
    exact isUnit_one
  have hcomp : ⇑(localisationPresentedAlgebraEquiv.{u} g 1) ∘ ⇑(localisationRingHom.{u} g 1) =
      ⇑(algebraMap (PresentedAlgebra.{u} n k g)
        (Localization.Away (Ideal.Quotient.mk (presentationIdeal.{u} g)
          (1 : MvPolynomial (ULift.{u} (Fin n)) ℂ)))) :=
    funext fun x ↦ localisationPresentedAlgebraEquiv_localisationRingHom.{u} g 1 x
  have hequiv := (localisationPresentedAlgebraEquiv.{u} g 1).bijective
  have hb' : Function.Bijective
      (⇑(localisationPresentedAlgebraEquiv.{u} g 1) ∘ ⇑(localisationRingHom.{u} g 1)) := by
    rw [hcomp]; exact hb
  exact (Function.Bijective.of_comp_iff' hequiv _).mp hb'

/-- **The base algebra and its localisation at `1` are the same `ℂ`-algebra**, along the structure
map itself.

`AlgEquiv.ofBijective` at `ComplexAnalytic.bijective_localisationRingHom_one`. It is a declaration
of its own rather than inlined because it is what a caller who wants the *algebras* rather than
the presentations reaches for, and it has no other name; the two declarations below are about
`ComplexAnalytic.Presentation`. -/
noncomputable def presentedAlgebraEquivLocalisationOne :
    PresentedAlgebra.{u} n k g ≃ₐ[ℂ]
      PresentedAlgebra.{u} (n + 1) (k + 1) (localisationPresentation.{u} g 1) :=
  AlgEquiv.ofBijective (PresHom.toAlgHom.{u} (localisationPresHom.{u} g 1))
    (bijective_localisationRingHom_one.{u} g)

/-- **The presentation of `D(1)` is isomorphic to the base's own**, in
`ComplexAnalytic.Presentation`.

`ComplexAnalytic.Presentation.isoOfAlgEquiv` at
`ComplexAnalytic.presentedAlgebraEquivLocalisationOne`. Nothing here says the two objects are
equal — they have different variable counts — and nothing here is about a general `f`: for a
general `f` the statement is **false**, and `ComplexAnalytic.localisationOpen_ne_top` is the
reason, that `D(f)` is proper whenever `f` has a zero on the space. The bare `1` is doing the
work. -/
noncomputable def localisationIsoOne :
    (⟨n + 1, k + 1, localisationPresentation.{u} g 1⟩ : Presentation.{u}) ≅ ⟨n, k, g⟩ :=
  Presentation.isoOfAlgEquiv.{u} (presentedAlgebraEquivLocalisationOne.{u} g)

/-- **And that isomorphism's forward direction is the structure map itself.**

`ComplexAnalytic.PresHom.ext` at `rfl`: `ComplexAnalytic.Presentation.isoOfAlgEquiv e`'s `hom` is
`e`'s ring map with a proof beside it, `e` is `AlgEquiv.ofBijective` of
`ComplexAnalytic.localisationPresHom`'s own algebra map, and a `ComplexAnalytic.PresHom` is a ring
map and a proposition — so the two are the same term.

**This is the load-bearing step and it is the one to be hardest on.** Without it the declaration
above says only that *some* isomorphism exists between the two presentations, and an `IsIso` of a
morphism that is not `ComplexAnalytic.localisationHom` is worth nothing to a caller: the whole
question this answers is about that morphism. -/
theorem localisationIsoOne_hom : (localisationIsoOne.{u} g).hom = localisationHom.{u} g 1 :=
  PresHom.ext rfl

/-- **`ComplexAnalytic.localisationHom g 1` is an isomorphism.**

The two declarations above, joined by `ComplexAnalytic.localisationIsoOne_hom`.

**An `instance` and not a `theorem`**, for the reason
`ComplexAnalytic.isOpenImmersion_specSchemeIota` gives for its own: instance search does not
unfold a definition, so a caller holding `ComplexAnalytic.localisationHom g 1` in the shape a
construction handed it needs the statement in the form search can try. It is cheap to try — the
head is a single named morphism at a literal `1`. A consumer that would rather have a `theorem`
pays a `haveI`.

**What this does and does not settle about the analytic side.** It is the presentation-level
statement, one category down from
`ComplexAnalytic.isIso_localisationProj_one`
(`Oka/Analytification/DistinguishedOpen.lean`), which says the *analytic* projection at `f = 1` is
an isomorphism. **One of the two implications holds and the other is what is missing**: this
statement gives the analytic one, by pushing it through
`ComplexAnalytic.analytificationFunctor` and reading the result with
`ComplexAnalytic.analytificationFunctor_map_localisationPresHom` — functoriality and nothing
more. The analytic form does **not** give this one: no statement in this repository says that
functor is full, faithful or reflects isomorphisms.

**What it is *for* is that a construction taking an isomorphism in
`ComplexAnalytic.Presentation` can now be fed at `f = 1`** — and whether any particular such
construction's remaining hypotheses hold is a question about that construction and is not answered
here. -/
instance isIso_localisationHom_one : IsIso (localisationHom.{u} g 1) := by
  rw [← localisationIsoOne_hom.{u} g]
  infer_instance

end ComplexAnalytic
