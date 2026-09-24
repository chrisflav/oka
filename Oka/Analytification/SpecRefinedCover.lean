/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Analytification.SpecRefinedChoice

/-!
# The chosen family is an affine open cover, and it refines both data

`Oka/Analytification/SpecRefinedChoice.lean` ends at
`ComplexAnalytic.exists_family_opensRange_presentationRefinedIota_eq`: given two cover data and an
isomorphism `Φ` of what they glue, there are four functions on the points of the glued scheme `X`
— a member of each datum and a polynomial in each member's own variables — such that at every
point the two chosen refined members are **the same affine open of `X`**, and the first family's
supremum is `⊤`.

**This file assembles that family into an object.** The two theorems below say that the two cover
data admit a common refinement by an affine open cover of `X`: one exhibits the cover with the
presentation of every member named on both sides, and the other states the containment that the
word *refinement* ordinarily means.

## The index type, and the sentence this file corrects

`Oka/Analytification/SpecMemberChoice.lean`'s `## What the index type is` is the standing statement
on this line and reads, in part, that *"a refinement indexed by points is not a refinement anybody
would assemble — the assembly step chooses a set of opens and an index type for it … and that
choice is not made here."*

**That is right about a cover *datum* and wrong about a cover, and the difference is what this file
turns on.** `AlgebraicGeometry.Scheme.AffineOpenCover` is `AlgebraicGeometry.Scheme.AffineCover` at
`AlgebraicGeometry.IsOpenImmersion`, and its index type is an arbitrary `Type`: it carries a
choice function `idx` from the points of the scheme to that index type and a field asking that
every point lie in the range of the component `idx` names. **So the points of `X` are a legal index
type, the identity is a legal choice function, and that field is the second half of the choice
step's own conclusion** — no set has to be chosen and no index type has to be invented.

**What a cover datum needs and this does not supply is `poly` and the three laws**, together with
the condition `Oka/Analytification/SpecScheme.lean` names: every pairwise overlap must be a
distinguished open of *each* of the two members it lies in. That is the third of that file's three
pieces and none of it is here, which is the reason this file's title says *cover* and not *cover
datum*.

**The condition is not uniformly out of reach, and which half is out of reach is worth stating.**
Where two members of the cover below are chosen inside **one** member of a datum — which many
pairs are, the index type being the points of `X` and `idx` sending many of them to one member —
the overlap is a chosen open of that member again, at the product of the two polynomials, by
`ComplexAnalytic.opensRange_presentationRefinedIota_inf`. **That is the ambient member's statement
and not the condition**, which asks for a polynomial in each of the two chosen opens' own
variables — one more variable each than the member has. The map that carries a polynomial across is
the one `ComplexAnalytic.localisationIncl` names, and
`ComplexAnalytic.opensRange_presentationRefinedIota_rename`
(`Oka/Analytification/SpecRefinedMemberSection.lean`) does carry one across it, at both of the two
chosen opens — **so at those pairs the condition holds and what is missing is the indexing and the
laws**. Where they are chosen inside **different** members it is what the
points of `X` cannot give, and that is the half the third piece is against.

## What the two statements are, and why there are two

The first names the presentation of every member of the cover on both sides — each is
`ComplexAnalytic.presentationRefinedIota` of a member of the respective datum at a polynomial in
that member's own variables — so a reader gets the affine opens *and* the data cutting them out.
The second says only that every member of the cover is **contained in** a member of each datum,
which is the ordinary definition of one cover refining another. **The second is the first plus
`ComplexAnalytic.opensRange_presentationRefinedIota_le` and is four lines**; it is stated
separately because a caller who wants the refinement statement should not have to read four bound
functions to find it.

**Both are existentials over the cover and not definitions of one**, for the reason
`Oka/Analytification/SpecMemberChoice.lean`'s `## Existential over four functions` section gives of
the four functions it declines to define: nothing distinguishes one choice from another, so a
`def` would name an arbitrary member of a class and every later statement would carry the
arbitrariness anyway. A consumer that wants the cover recovers it from either statement with one
`obtain`.

## Two elaboration facts, recorded because each cost a compile

* **The universe on `AlgebraicGeometry.Scheme.AffineOpenCover` has to be written.** Its index type
  lives in a universe the rest of the statement does not pin, so the spelling below is
  `.AffineOpenCover.{u}`; without it the index field fails with *"has type `Type u` … but is
  expected to have type `Type u_1`"*.
* **The covering field is discharged by the choice step's own second conjunct after one rewrite.**
  Membership in the set-range of a component and membership in its
  `AlgebraicGeometry.Scheme.Hom.opensRange` are definitionally the same, so no bridge lemma is
  needed and none should be added.

## Main results

- `ComplexAnalytic.exists_affineOpenCover_opensRange_presentationRefinedIota_eq`: **two cover data
  and an isomorphism of what they glue admit a common refinement by an affine open cover of the
  glued scheme**, every member of which is a chosen distinguished open of a member of each datum,
  with the presentations named.
- `ComplexAnalytic.exists_affineOpenCover_opensRange_le`: **and every member of that cover is
  contained in a member of each datum**, which is the ordinary sense in which one cover refines
  another.

## What is not here

* **No cover datum.** No `poly`, no `glue`, and none of the three laws, so nothing here is or
  produces a common refinement *of two cover data*. That is
  `Oka/Analytification/SpecScheme.lean`'s third piece and taxis #1287's line, and this file adds to
  none of `Oka/Analytification/CrossMemberDatum.lean`,
  `Oka/Analytification/CrossMemberDatumGlue.lean` or the `Oka/Analytification/RefineDatum*.lean`
  files. **The title says *cover* for that reason and the module name does too**: this is not a
  common refinement in the sense the enclosing programme is after.
* **Nothing small, and nothing finite.** The cover produced below is indexed by the points of `X`,
  so it is as large as `X`; no set of opens is cut down and no subcover is extracted.
  `AlgebraicGeometry.Scheme.OpenCover.finiteSubcover` needs the space to be compact, and
  `ComplexAnalytic.specScheme` is not known to be and in general is not, its index type being
  arbitrary.
* **Nothing that constructs the isomorphism `Φ`**, in either direction. It is a hypothesis here
  exactly as it is in `Oka/Analytification/SpecTwoData.lean`, and nothing in this repository
  produces one.
* **No new mathematics about the opens themselves.** Both statements are the imported choice step
  repackaged; the affineness of every member is
  `ComplexAnalytic.isAffineOpen_presentationRefinedIota` and is not restated here, since the
  spectrum of the presented algebra is the source of every component of the cover and Mathlib's
  own instance reads it off.
* **Nothing analytic.** No analytification, no `X^an`, no comparison morphism: everything here is
  on the `Spec` side.
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

/-- **Two cover data and an isomorphism of what they glue admit a common refinement by an affine
open cover of the glued scheme**, with the presentation of every member named on both sides.

The cover's index type is the points of `X`, its choice function is the identity, and its covering
field is the second conjunct of
`ComplexAnalytic.exists_family_opensRange_presentationRefinedIota_eq`'s source, which says that
every point lies in its own chosen open. **That is the whole construction**: the components are
the chosen refined members of the first datum, and the equation below is the choice step's first
conjunct rewritten into the vocabulary of ranges.

**The first conjunct is `rfl` at the cover built here and is not `rfl` for a reader**, which is why
it is stated. The statement quantifies over a cover, so from outside nothing says how the
components were chosen; both conjuncts together are what identify the components as refined
members of the two data, and either alone would leave one of the data unmentioned.

**The second conjunct is the one that mentions the second datum.** Its immersion is
`ComplexAnalytic.specSchemeIotaMap … Φ (idx' b)`, which is not
`ComplexAnalytic.specSchemeIota` of anything in the first datum — the reason
`ComplexAnalytic.presentationRefinedIota` takes an arbitrary open immersion. -/
theorem exists_affineOpenCover_opensRange_presentationRefinedIota_eq
    (Φ : specScheme.{u} obj' poly' glue' hrange' hsymm' hcocycle' ⟶
      specScheme.{u} obj poly glue hrange hsymm hcocycle) [IsIso Φ] :
    ∃ (𝒰 : (specScheme.{u} obj poly glue hrange hsymm hcocycle).AffineOpenCover.{u})
      (idx : 𝒰.I₀ → J) (idx' : 𝒰.I₀ → K)
      (fam : ∀ b, MvPolynomial (ULift.{u} (Fin (obj (idx b)).n)) ℂ)
      (fam' : ∀ b, MvPolynomial (ULift.{u} (Fin (obj' (idx' b)).n)) ℂ),
      ∀ b, (𝒰.f b).opensRange =
            (presentationRefinedIota.{u}
              (specSchemeIota.{u} obj poly glue hrange hsymm hcocycle (idx b))
                (fam b)).opensRange ∧
          (𝒰.f b).opensRange =
            (presentationRefinedIota.{u} (specSchemeIotaMap.{u} obj poly glue hrange hsymm hcocycle
              obj' poly' glue' hrange' hsymm' hcocycle' Φ (idx' b)) (fam' b)).opensRange := by
  obtain ⟨idx, idx', fam, fam', h⟩ :=
    exists_family_mvPolynomial_basicOpen_specSchemeIotaMap.{u} obj poly glue hrange hsymm hcocycle
      obj' poly' glue' hrange' hsymm' hcocycle' Φ
  refine ⟨{
    I₀ := ↥(specScheme.{u} obj poly glue hrange hsymm hcocycle)
    X := fun b => CommRingCat.of (presentationRefinedPres.{u} (obj (idx b)) (fam b)).alg
    f := fun b => presentationRefinedIota.{u}
      (specSchemeIota.{u} obj poly glue hrange hsymm hcocycle (idx b)) (fam b)
    idx := fun x => x
    covers := fun x => by
      have hx := (h x).2
      rw [← opensRange_presentationRefinedIota_eq_basicOpen] at hx
      exact hx }, idx, idx', fam, fam', fun b => ⟨rfl, ?_⟩⟩
  rw [opensRange_presentationRefinedIota_eq_basicOpen,
    opensRange_presentationRefinedIota_eq_basicOpen]
  exact (h b).1

/-- **And every member of that cover is contained in a member of each datum** — the ordinary sense
in which one cover refines another.

The theorem above with `ComplexAnalytic.opensRange_presentationRefinedIota_le` applied to each of
its two conjuncts. **This is the statement to cite for *refinement*** : it mentions no polynomial,
no presentation and no chosen function, so a caller who wants only that the two data have a common
affine refinement reads one existential and two containments.

**It is weaker than the theorem above in exactly one way and stronger in none**: the containment
forgets which distinguished open of the member the component is, which is the content the other
statement keeps. Nothing here says the containments are proper, and at a polynomial that is a unit
they are equalities. -/
theorem exists_affineOpenCover_opensRange_le
    (Φ : specScheme.{u} obj' poly' glue' hrange' hsymm' hcocycle' ⟶
      specScheme.{u} obj poly glue hrange hsymm hcocycle) [IsIso Φ] :
    ∃ 𝒰 : (specScheme.{u} obj poly glue hrange hsymm hcocycle).AffineOpenCover.{u},
      (∀ b, ∃ i : J, (𝒰.f b).opensRange ≤
        (specSchemeIota.{u} obj poly glue hrange hsymm hcocycle i).opensRange) ∧
      (∀ b, ∃ k : K, (𝒰.f b).opensRange ≤
        (specSchemeIotaMap.{u} obj poly glue hrange hsymm hcocycle
          obj' poly' glue' hrange' hsymm' hcocycle' Φ k).opensRange) := by
  obtain ⟨𝒰, idx, idx', fam, fam', h⟩ :=
    exists_affineOpenCover_opensRange_presentationRefinedIota_eq.{u} obj poly glue hrange hsymm
      hcocycle obj' poly' glue' hrange' hsymm' hcocycle' Φ
  refine ⟨𝒰, fun b => ⟨idx b, ?_⟩, fun b => ⟨idx' b, ?_⟩⟩
  · rw [(h b).1]
    exact opensRange_presentationRefinedIota_le _ _
  · rw [(h b).2]
    exact opensRange_presentationRefinedIota_le _ _

end

end ComplexAnalytic
