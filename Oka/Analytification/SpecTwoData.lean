/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Analytification.SpecScheme

/-!
# Two cover data over one scheme: the members of the second are affine opens of the first's

`Oka/Analytification/SpecScheme.lean` promotes the gluing of a cover datum to an
`AlgebraicGeometry.Scheme` and ends with
`ComplexAnalytic.exists_basicOpen_specSchemeIota_inter`, which says that two members of **one**
datum meet in an open distinguished in both. Its own titled section says what that is not:

> it is **not** a common refinement, which needs **two data and an isomorphism of what they glue**,
> **a choice of such an open at every point**, and **the refined family assembled into a cover
> datum with its three laws**.

**This file is the first of those three and the local half of the second.**

## What is new here, and it is not that the data are two

**This is not the first statement in this repository about two cover data, and an earlier draft of
this paragraph said it was.** Four files under `Oka/Analytification/` already open a second cover
datum beside the first, and the second datum is a family of presentations named `obj'` in each:
`Oka/Analytification/SpecFunctoriality.lean`, `Oka/Analytification/ComparisonSquare.lean`,
`Oka/Analytification/CoverFunctoriality.lean` — which opens a third — and
`Oka/Analytification/CoverIndependence.lean`, which opens a second and a third.

**In every one of them the caller matches the members up before anything is proved, and the
spelling differs.** Three take an index map `σ` together with morphisms
`ψ i : obj i ⟶ obj' (σ i)`; `Oka/Analytification/CoverIndependence.lean` takes **no `σ`** and
matches by the identity on the index type — its `ψ i` is an isomorphism `obj i ≅ obj' i` — and, for
its third datum, by an `Equiv` of index types. What they have in common is the part that matters
here: which member of the second family a member of the first is compared against is fixed in
advance, and nothing there asks whether two members chosen *independently* meet at all.

**Here there is no index map.** The two data are related only by a morphism `Φ` of what they glue;
every pair of members is admissible, `ComplexAnalytic.exists_basicOpen_specSchemeIotaMap_inter` is
stated at an arbitrary `(i, j)`, and `ComplexAnalytic.exists_index_basicOpen_specSchemeIotaMap`
produces both of its indices instead of taking them. **That is the shape a common refinement of two
covers needs and a member-matched comparison does not supply**, and it is what
`Oka/Analytification/CoverIndependence.lean` names as the condition such a refinement has to
reproduce.

**Two drafts of this paragraph were wrong before this one, each because of its sweep, and the pair
is worth more than either repair.** The first claimed to be the first statement about two data at
all; it was checked by a whitespace-normalised search of the *prose* for `two cover data`, and the
thing it is about is a `variable` line — `variable (obj' : K → Presentation.{u})` contains neither
word, so no prose pattern reaches it and all four files above were invisible. **The second
searched the construction and searched for the wrong one**: the pattern was a disjunction, of which
the second alternative matched any file introducing a second *index* type, and two files that
index **cutting polynomials** by one — `Oka/Analytification/CoverRefinement.lean:286` and
`Oka/Analytification/CrossMemberGlue.lean:272`, whose `fam : K → MvPolynomial …` refines a single
member and is taxis #1287's subject — were read as second cover data. Neither contains `obj'`
anywhere. **The instrument that separates them is the name of the construction and not of its
index type**, and the sweep behind the list above is `obj'`, which returns those four files and
this one.

## What is assumed, and it is one morphism

A second cover datum, indexed by a second type `K`, and a morphism

    Φ : specScheme obj' poly' … ⟶ specScheme obj poly …

between what the two glue. **Nothing here produces one.** That two cover data are two covers *of
one scheme* is, in this repository, exactly the statement that such a `Φ` is an isomorphism —
there is no `AlgebraicGeometry.Scheme` anywhere on this line except
`ComplexAnalytic.specScheme` itself, so "the same scheme" has to be said this way, and taxis
#1107's thread says it in those words.

**The four declarations below that do not mention a point need only
`AlgebraicGeometry.IsOpenImmersion Φ`**, which is strictly weaker and costs nothing to state; only
`ComplexAnalytic.mem_opensRange_specSchemeIotaMap` and
`ComplexAnalytic.exists_index_basicOpen_specSchemeIotaMap` ask for `CategoryTheory.IsIso`, and they
ask for it to know that `Φ` is surjective on points.

## The three spellings, recorded so they are not paid twice

1. **`ComplexAnalytic.specSchemeIotaMap` is a composite and nothing else.**
   `AlgebraicGeometry.isAffineOpen_opensRange` then applies to it with no image lemma: the
   `AlgebraicGeometry.IsAffine` side condition is on the *source*, which is a spectrum, so
   carrying a member across `Φ` needs neither `AlgebraicGeometry.IsAffineOpen.preimage_of_isIso`
   nor `AlgebraicGeometry.IsAffineOpen.image_of_isOpenImmersion`.
2. **The open-immersion instance is stated by hand**, for the reason
   `ComplexAnalytic.isOpenImmersion_specSchemeIota` gives at the one-datum spelling: instance
   search does not unfold the definition, and `AlgebraicGeometry.isAffineOpen_opensRange` is the
   consumer that needs one.
3. **Surjectivity of `Φ` is `AlgebraicGeometry.Scheme.homeoOfIso`** at `CategoryTheory.asIso Φ`,
   not an inverse-composed-with-itself calculation. The calculation was tried first and it fails
   on the *index type*: `AlgebraicGeometry.LocallyRingedSpace.GlueData.ι_jointly_surjective`
   returns a `j` at the glue datum's own `J` field, which is `K` by `rfl` but not syntactically,
   so `rw` on the equation it returns reports a pattern mismatch and then an application type
   mismatch. Destructuring the homeomorphism's surjectivity instead never names the index.

## Main definitions

- `ComplexAnalytic.specSchemeIotaMap`: **the `j`-th member of the second datum, carried into the
  first datum's scheme along `Φ`.**

## Main results

- `ComplexAnalytic.isOpenImmersion_specSchemeIotaMap`: a carried member is an open subscheme.
- `ComplexAnalytic.isAffineOpen_specSchemeIotaMap`: **a member of the second datum is an affine
  open of the first datum's scheme.**
- `ComplexAnalytic.exists_basicOpen_specSchemeIotaMap_inter`: **every point of the overlap of a
  member of the first datum with a member of the second lies in an open distinguished in both.**
  Which Mathlib lemma that is, and why it is not a call to the one-datum statement, are on the
  declaration and deliberately not here: a name in this block is a declaration this file
  advertises, and neither of those two is one.
- `ComplexAnalytic.mem_opensRange_specSchemeIotaMap`: at an isomorphism, the carried members cover.
- `ComplexAnalytic.exists_index_basicOpen_specSchemeIotaMap`: **at every point of the first
  datum's scheme there is a member of each datum and an open distinguished in both containing it**,
  with no index handed in.

## What is not here

* **No common refinement.** The third of the three pieces quoted above — the refined family
  assembled into a cover *datum*, with its `poly`, its `glue` and its three laws — is untouched,
  and nothing here says what it costs. That is the piece taxis #1287 has spent a fortnight on for
  a refinement of **one** datum.
* **No choice.** `ComplexAnalytic.exists_index_basicOpen_specSchemeIotaMap` is an existential at
  each point and not a function on points. A refinement indexes its members by something, and
  choosing that index set is not done here.
* **No polynomial form, and it is the next step rather than a wall.** The two sections it produces
  live in `Γ(X, U)` for the two members `U`, where a cover datum's overlaps are `D(poly i j)` for
  a polynomial in the member's own variables. Two steps close that gap and both were measured
  before this file was written rather than guessed at: `Γ(X, (specSchemeIota … i).opensRange)` is
  `CommRingCat.of (obj i).alg` by `AlgebraicGeometry.Scheme.Hom.appIso` at `⊤` composed with
  `AlgebraicGeometry.Scheme.ΓSpecIso`, which compiles as one term; and the lift from
  `ComplexAnalytic.PresentedAlgebra` to a polynomial is `Ideal.Quotient.mk_surjective`, which this
  repository already spends widely. **Neither is here**, because the first has no
  complex-analytic content and `README.md`'s mirror-tree rule puts it under
  `Oka/AlgebraicGeometry/` rather than in this tree. **Both have since been added, and neither to
  this file**: the first is `AlgebraicGeometry.IsOpenImmersion.specΓIsoTop`
  (`Oka/AlgebraicGeometry/OpenImmersion.lean`), exactly where that rule puts it, and
  `ComplexAnalytic.surjective_specSchemeIotaSection`
  (`Oka/Analytification/SpecMemberSections.lean`) is the two of them together at one member.
  **This bullet's own subject is no longer absent either, and that clause is why this sentence
  exists**: `ComplexAnalytic.exists_index_mvPolynomial_basicOpen_specSchemeIotaMap` (same file) is
  the polynomial form of the last theorem below, and
  `ComplexAnalytic.exists_mvPolynomial_basicOpen_specSchemeIotaMap_inter` is the fixed-index one.
  **What was priced wrong while it was absent was the second lift.**
  `ComplexAnalytic.surjective_specSchemeIotaSection` reaches a member of *this* datum and a carried
  member of the second is `ComplexAnalytic.specSchemeIotaMap`, which is not
  `ComplexAnalytic.specSchemeIota` of anything here; the statement became cheap when that file
  restated its three lemmas at an arbitrary open immersion. **The last part of it that was still
  absent — any of it that is a *choice* rather than an existential — has since been added, and
  not to this file either**:
  `ComplexAnalytic.exists_family_mvPolynomial_basicOpen_specSchemeIotaMap`
  (`Oka/Analytification/SpecMemberChoice.lean`) is one `choose` on the polynomial form just named.
  **What this file's first two bullets decline is untouched by that**: the family that theorem
  produces is indexed by the *points* of the scheme, which is not what a refinement indexes its
  members by, and choosing that index set is not done here.
* **No consumer of `ComplexAnalytic.exists_basicOpen_specSchemeIota_inter` *in this file*.** It
  applies the same Mathlib lemma at a different pair of affine opens rather than calling that
  theorem, and taxis #1507 measured that absence rather than asserting it. **This bullet used to
  say the theorem had none anywhere, and that is no longer true**:
  `ComplexAnalytic.exists_mvPolynomial_basicOpen_specSchemeIota_inter`
  (`Oka/Analytification/SpecMemberSections.lean`) restates it with polynomials in the two members'
  own variables and its proof term reads this one. What is unchanged is this file's own position —
  nothing below calls it, for the reason given above and not for want of anyone who does.
* **Nothing that constructs `Φ`**, in either direction, and no statement that two cover data with
  isomorphic gluings have anything else in common.
* **Nothing on the analytic side.** `X^an` is glued from analytic spaces and is not a scheme;
  as in `Oka/Analytification/SpecScheme.lean`, nothing here touches it.
* **No `AlgebraicGeometry.Scheme.GlueData`**, and no scheme-level glue datum. The gluing stays in
  `Oka/Analytification/SpecAffineCover.lean` at the level of locally ringed spaces.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry

universe u

namespace ComplexAnalytic

noncomputable section

variable {J : Type u} (obj : J → Presentation.{u})
  (poly : ∀ i : J, J → MvPolynomial (ULift.{u} (Fin (obj i).n)) ℂ)
  (glue : ∀ i j : J, coverOverlap.{u} obj poly i j ≅ coverOverlap.{u} obj poly j i)
  (hrange : ∀ i j k : J, i ≠ j → i ≠ k → j ≠ k →
    Set.range (specTripleIncl.{u} obj poly i j k ≫ specTransitionHom.{u} obj poly glue i j).base ⊆
      (specOpen.{u} obj poly j k : Set (specSpace.{u} obj j)))
  (hsymm : ∀ i j : J, glue j i = (glue i j).symm)
  (hcocycle : ∀ i j k : J, ∀ hij : i ≠ j, ∀ hik : i ≠ k, ∀ hjk : j ≠ k,
    specTriple.{u} obj poly glue hrange i j k hij hik hjk ≫
      specTriple.{u} obj poly glue hrange j k i hjk hij.symm hik.symm ≫
      specTriple.{u} obj poly glue hrange k i j hik.symm hjk.symm hij = 𝟙 _)

variable {K : Type u} (obj' : K → Presentation.{u})
  (poly' : ∀ i : K, K → MvPolynomial (ULift.{u} (Fin (obj' i).n)) ℂ)
  (glue' : ∀ i j : K, coverOverlap.{u} obj' poly' i j ≅ coverOverlap.{u} obj' poly' j i)
  (hrange' : ∀ i j k : K, i ≠ j → i ≠ k → j ≠ k →
    Set.range (specTripleIncl.{u} obj' poly' i j k ≫
        specTransitionHom.{u} obj' poly' glue' i j).base ⊆
      (specOpen.{u} obj' poly' j k : Set (specSpace.{u} obj' j)))
  (hsymm' : ∀ i j : K, glue' j i = (glue' i j).symm)
  (hcocycle' : ∀ i j k : K, ∀ hij : i ≠ j, ∀ hik : i ≠ k, ∀ hjk : j ≠ k,
    specTriple.{u} obj' poly' glue' hrange' i j k hij hik hjk ≫
      specTriple.{u} obj' poly' glue' hrange' j k i hjk hij.symm hik.symm ≫
      specTriple.{u} obj' poly' glue' hrange' k i j hik.symm hjk.symm hij = 𝟙 _)

/-! ### A member of the second datum, inside the first datum's scheme -/

/-- **The `j`-th member of the second cover datum, carried into the first datum's scheme.**

`ComplexAnalytic.specSchemeIota` for the second datum, followed by `Φ`. There is no transport in
it and no hypothesis on `Φ`; everything below that needs one asks for it there. -/
def specSchemeIotaMap
    (Φ : specScheme.{u} obj' poly' glue' hrange' hsymm' hcocycle' ⟶
      specScheme.{u} obj poly glue hrange hsymm hcocycle) (j : K) :
    Spec (CommRingCat.of (obj' j).alg) ⟶ specScheme.{u} obj poly glue hrange hsymm hcocycle :=
  specSchemeIota.{u} obj' poly' glue' hrange' hsymm' hcocycle' j ≫ Φ

/-- **A carried member is an open subscheme of the first datum's scheme**, as soon as `Φ` is an
open immersion — in particular whenever it is an isomorphism.

An `instance` and not a `theorem`, and stated by hand rather than found, for the reason
`ComplexAnalytic.isOpenImmersion_specSchemeIota` gives: instance search does not unfold
`ComplexAnalytic.specSchemeIotaMap`, and `AlgebraicGeometry.isAffineOpen_opensRange` below is a
consumer that needs one. -/
instance isOpenImmersion_specSchemeIotaMap
    (Φ : specScheme.{u} obj' poly' glue' hrange' hsymm' hcocycle' ⟶
      specScheme.{u} obj poly glue hrange hsymm hcocycle) [IsOpenImmersion Φ] (j : K) :
    IsOpenImmersion
      (specSchemeIotaMap.{u} obj poly glue hrange hsymm hcocycle obj' poly' glue' hrange' hsymm'
        hcocycle' Φ j) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ Φ))

/-- **A member of the second datum is an affine open of the first datum's scheme.**

`AlgebraicGeometry.isAffineOpen_opensRange` at the instance above, exactly as
`ComplexAnalytic.isAffineOpen_specSchemeIota` is it at the one-datum spelling: the
`AlgebraicGeometry.IsAffine` side condition is on the **source**, which is a spectrum here as
there, so carrying a member across `Φ` costs no image lemma. -/
theorem isAffineOpen_specSchemeIotaMap
    (Φ : specScheme.{u} obj' poly' glue' hrange' hsymm' hcocycle' ⟶
      specScheme.{u} obj poly glue hrange hsymm hcocycle) [IsOpenImmersion Φ] (j : K) :
    IsAffineOpen
      (specSchemeIotaMap.{u} obj poly glue hrange hsymm hcocycle obj' poly' glue' hrange' hsymm'
        hcocycle' Φ j).opensRange :=
  isAffineOpen_opensRange _

/-! ### Overlaps across the two data are distinguished in both -/

/-- **Every point of the overlap of a member of the first datum with a member of the second lies
in an open distinguished in both.**

`AlgebraicGeometry.exists_basicOpen_le_affine_inter` at
`ComplexAnalytic.isAffineOpen_specSchemeIota` and
`ComplexAnalytic.isAffineOpen_specSchemeIotaMap`. This is
`ComplexAnalytic.exists_basicOpen_specSchemeIota_inter` across **two** cover data, and it is the
local statement `Oka/Analytification/CoverIndependence.lean` names as what a common refinement has
to reproduce. **It does not consume that theorem** — it is the same Mathlib lemma at a different
pair of affine opens. -/
theorem exists_basicOpen_specSchemeIotaMap_inter
    (Φ : specScheme.{u} obj' poly' glue' hrange' hsymm' hcocycle' ⟶
      specScheme.{u} obj poly glue hrange hsymm hcocycle) [IsOpenImmersion Φ] (i : J) (j : K)
    (x : specScheme.{u} obj poly glue hrange hsymm hcocycle)
    (hx : x ∈ (specSchemeIota.{u} obj poly glue hrange hsymm hcocycle i).opensRange ⊓
      (specSchemeIotaMap.{u} obj poly glue hrange hsymm hcocycle obj' poly' glue' hrange' hsymm'
        hcocycle' Φ j).opensRange) :
    ∃ (f : Γ(specScheme.{u} obj poly glue hrange hsymm hcocycle,
        (specSchemeIota.{u} obj poly glue hrange hsymm hcocycle i).opensRange))
      (g : Γ(specScheme.{u} obj poly glue hrange hsymm hcocycle,
        (specSchemeIotaMap.{u} obj poly glue hrange hsymm hcocycle obj' poly' glue' hrange'
          hsymm' hcocycle' Φ j).opensRange)),
      (specScheme.{u} obj poly glue hrange hsymm hcocycle).basicOpen f =
        (specScheme.{u} obj poly glue hrange hsymm hcocycle).basicOpen g ∧
      x ∈ (specScheme.{u} obj poly glue hrange hsymm hcocycle).basicOpen f :=
  exists_basicOpen_le_affine_inter
    (isAffineOpen_specSchemeIota.{u} obj poly glue hrange hsymm hcocycle i)
    (isAffineOpen_specSchemeIotaMap.{u} obj poly glue hrange hsymm hcocycle obj' poly' glue'
      hrange' hsymm' hcocycle' Φ j) x hx

/-! ### At an isomorphism, both families cover -/

/-- **At an isomorphism, the carried members cover the first datum's scheme.**

`AlgebraicGeometry.Scheme.homeoOfIso` makes `Φ` surjective on points and
`AlgebraicGeometry.LocallyRingedSpace.GlueData.ι_jointly_surjective` covers the second datum's own
gluing. Destructuring the homeomorphism's surjectivity first is what keeps the proof to three
lines; see spelling 3 in this module's docstring for the index-type mismatch that the other order
runs into. -/
theorem mem_opensRange_specSchemeIotaMap
    (Φ : specScheme.{u} obj' poly' glue' hrange' hsymm' hcocycle' ⟶
      specScheme.{u} obj poly glue hrange hsymm hcocycle) [IsIso Φ]
    (x : specScheme.{u} obj poly glue hrange hsymm hcocycle) :
    ∃ j : K, x ∈ (specSchemeIotaMap.{u} obj poly glue hrange hsymm hcocycle obj' poly' glue'
      hrange' hsymm' hcocycle' Φ j).opensRange := by
  obtain ⟨y, rfl⟩ := (Scheme.homeoOfIso (asIso Φ)).surjective x
  obtain ⟨j, z, rfl⟩ :=
    (specGlueData.{u} obj' poly' glue' hrange' hsymm' hcocycle').ι_jointly_surjective y
  exact ⟨j, z, rfl⟩

/-- **At every point of the first datum's scheme there is a member of each datum and an open
distinguished in both containing it.**

The two joint surjectivities, then
`ComplexAnalytic.exists_basicOpen_specSchemeIotaMap_inter`. This is the statement this file is for:
no index is handed in, so it is a statement about the two data and not about a chosen pair of
members.

**It is an existential at each point and not a choice.** A common refinement indexes its members
by something, and picking that index set is not here; this module's `## What is not here` says what
that costs. Turning the two sections into polynomials in the members' own variables is not here
either and is no longer anywhere absent:
`ComplexAnalytic.exists_index_mvPolynomial_basicOpen_specSchemeIotaMap`
(`Oka/Analytification/SpecMemberSections.lean`) is this statement in that vocabulary, and its proof
term reads this one. -/
theorem exists_index_basicOpen_specSchemeIotaMap
    (Φ : specScheme.{u} obj' poly' glue' hrange' hsymm' hcocycle' ⟶
      specScheme.{u} obj poly glue hrange hsymm hcocycle) [IsIso Φ]
    (x : specScheme.{u} obj poly glue hrange hsymm hcocycle) :
    ∃ (i : J) (j : K)
      (f : Γ(specScheme.{u} obj poly glue hrange hsymm hcocycle,
        (specSchemeIota.{u} obj poly glue hrange hsymm hcocycle i).opensRange))
      (g : Γ(specScheme.{u} obj poly glue hrange hsymm hcocycle,
        (specSchemeIotaMap.{u} obj poly glue hrange hsymm hcocycle obj' poly' glue' hrange'
          hsymm' hcocycle' Φ j).opensRange)),
      (specScheme.{u} obj poly glue hrange hsymm hcocycle).basicOpen f =
        (specScheme.{u} obj poly glue hrange hsymm hcocycle).basicOpen g ∧
      x ∈ (specScheme.{u} obj poly glue hrange hsymm hcocycle).basicOpen f := by
  obtain ⟨i, y, rfl⟩ :=
    (specGlueData.{u} obj poly glue hrange hsymm hcocycle).ι_jointly_surjective x
  obtain ⟨j, hj⟩ :=
    mem_opensRange_specSchemeIotaMap.{u} obj poly glue hrange hsymm hcocycle obj' poly' glue'
      hrange' hsymm' hcocycle' Φ _
  obtain ⟨f, g, hfg, hx⟩ :=
    exists_basicOpen_specSchemeIotaMap_inter.{u} obj poly glue hrange hsymm hcocycle obj' poly'
      glue' hrange' hsymm' hcocycle' Φ i j _ ⟨⟨y, rfl⟩, hj⟩
  exact ⟨i, j, f, g, hfg, hx⟩

end

end ComplexAnalytic
