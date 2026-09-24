/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Analytification.SpecAffineCover

/-!
# The comparison morphism `X^an ⟶ X` for a glued scheme

`Oka/Analytification/Comparison.lean` builds the comparison morphism of a *presentation*,
`ComplexAnalytic.analytificationToSpec g : A^an ⟶ Spec A`, and makes it natural.
`Oka/Analytification/AffineCover.lean` glues the analytifications of a family of presentations
into `X^an`, and `Oka/Analytification/SpecAffineCover.lean` glues their `Spec`s into `X`. **This
file is the morphism between the two gluings**, glued from the members' comparison morphisms.

## What the construction costs, and it is one hypothesis and two naturality squares

`AlgebraicGeometry.LocallyRingedSpace.GlueData.glueMorphisms` maps out of a glue datum's gluing
into any locally ringed space, given a family out of the members agreeing over the overlaps. So
once `X` exists — which is what `Oka/Analytification/SpecAffineCover.lean` supplies — the whole
content of this file is that

```
analytificationToSpec (obj i).g ≫ specIota i
```

is such a family, and **that is two instances of one naturality square**. Both are
`ComplexAnalytic.analytificationToSpecNatTrans`, which has been in the tree since
`Oka/Analytification/Comparison.lean`:

* at `ComplexAnalytic.localisationHom`, which says the comparison commutes with passing to a
  distinguished open — `ComplexAnalytic.coverIncl_comp_analytificationToSpec` below;
* at `(glue i j).hom`, which says it commutes with the transition —
  `ComplexAnalytic.comparisonPart_comp_specTransition` below.

Nothing else about the comparison morphism is used. In particular no property of
`ComplexAnalytic.analytificationToSpec` beyond naturality enters, and neither does any of
`Oka/Analytification/AffineCover.lean`'s second half.

## The input asks for two range hypotheses and two cocycle hypotheses, over one datum

`ComplexAnalytic.coverAnalytification` and `ComplexAnalytic.specGlued` are built from **the same**
family of presentations, the same polynomials and the same `glue`, and `hsymm` is a hypothesis on
`glue` alone and so is literally shared. `hrange` and `hcocycle` are not: `hrange` is a statement
about the ranges of base maps, and the analytic side's members are non-vanishing loci in `ℂ^n`
where the `Spec` side's are basic opens of a spectrum. `ComplexAnalytic.analytificationToSpec` is
not a homeomorphism between them, so nothing transports. `hcocycle` is stated through whichever
side's triple-overlap morphisms it is about.

**So a caller supplies four hypotheses over one datum, and the two extra ones are the price of
having both spaces.** Below three members the price is zero: both triple-overlap hypotheses are
vacuous there, on both sides and for the same reason, so the `Spec`-side pair is the same one-line
elimination the analytic pair already was.

## `ComplexAnalytic.comparisonPart` is the reason the two squares compose

The family's compatibility is an equation over the *overlaps*, and the overlap has two
descriptions on each side — as `Spec`/analytification of the presentation
`ComplexAnalytic.coverOverlap`, and as an open subspace of the ambient member.
`ComplexAnalytic.comparisonPart` is the comparison morphism of that presentation read through
both identifications at once, and it is what lets the naturality square at
`ComplexAnalytic.localisationHom` — which is stated at the presentation — be used against
`ComplexAnalytic.coverIncl`, which is stated at the open subspace. Without it the two squares are
about different objects and do not compose.

## Main definitions

- `ComplexAnalytic.comparisonPart`: the comparison morphism at an overlap, read through
  `ComplexAnalytic.coverOverlapIso` and `ComplexAnalytic.specOverlapIso`.
- `ComplexAnalytic.comparisonPartIota`: the `i`-th member's contribution to the glued morphism,
  `A_i^an ⟶ Spec A_i ⟶ X`.
- `ComplexAnalytic.analytificationToSpecGlued`: **the comparison morphism `X^an ⟶ X`**, which is
  what this file exists for.

## Main results

- `ComplexAnalytic.coverIncl_comp_analytificationToSpec`: **the comparison commutes with passing
  to a distinguished open of a member**, in the vocabulary of the two cover files.
- `ComplexAnalytic.comparisonPart_comp_specTransition`: **and with the transition.** These two are
  the naturality squares, and between them they are the whole content of the compatibility.
- `ComplexAnalytic.comm_comparisonPartIota`: **the members' comparison morphisms agree over the
  overlaps**, which is `AlgebraicGeometry.LocallyRingedSpace.GlueData.glueMorphisms`' hypothesis
  in the form a caller can supply it.
- `ComplexAnalytic.toLRSHom_coverIota_comp_analytificationToSpecGlued`: **it restricts to the
  affine comparison on each member.** This is the statement that says the construction is the
  intended one; a definition ignoring its input would satisfy the type and nothing else here.
- `ComplexAnalytic.analytificationToSpecGlued_unique`: **and it is the only morphism that does.**

## What is not here

* **No `AlgebraicGeometry.Scheme`.** `ComplexAnalytic.specFunctor` lands in
  `AlgebraicGeometry.LocallyRingedSpace` and `ComplexAnalytic.specGlued` is a gluing of such, so
  `X` is a locally ringed space here and the comparison morphism is one of locally ringed spaces.
  `Oka/Analytification/Comparison.lean` and `Oka/Analytification/AffineCover.lean` each argue in a
  titled section that the absence of `AlgebraicGeometry.Scheme` from their statements is a
  *result*; **this file does not weaken either, and it did not have to** — nothing in the
  construction wanted one, since `AlgebraicGeometry.LocallyRingedSpace.GlueData.glueMorphisms`
  maps into an arbitrary locally ringed space.
* **No source at the analytic-space level.** `ComplexAnalytic.analytificationToSpecGlued` is
  stated out of `(coverAnalytification …).toLocallyRingedSpace`, not out of
  `ComplexAnalytic.coverAnalytification` itself, because its target is not an analytic space and
  there is no morphism of analytic spaces to be had. `ComplexAnalytic.coverGlueMorphisms` is the
  declaration for the case where the target *is* one; it is not applicable here and that is why
  this file goes through the glue datum directly. The two agree on the source:
  `ComplexAnalytic.coverAnalytification_toLocallyRingedSpace` is `rfl`.
* **No comparison of the two covers' opens.** That
  `ComplexAnalytic.analytificationToSpecGlued` carries `ComplexAnalytic.coverOpen` into
  `ComplexAnalytic.specOpen` is a statement about the cover rather than about the morphism, and
  nothing below needs it. `Oka/Analytification/SpecAffineCover.lean` makes the same point.
* **No statement that the comparison is an isomorphism, or flat, or anything else.** Those are
  theorems about `ComplexAnalytic.analytificationToSpec` and belong wherever that is studied;
  this file glues, and gluing preserves nothing on its own.
* **No functoriality.** `Oka/Analytification/CoverFunctoriality.lean` — a morphism of covered
  schemes analytified — is a different construction and does not pass through here. That the
  square between the two commutes is `Oka/Analytification/ComparisonSquare.lean`, which imports
  both and is where it belongs for that reason. **This bullet said the square was stated in
  neither file until that one arrived**, which is the honest form of the same sentence: the file
  it names still does not state it.
-/

open CategoryTheory TopologicalSpace AlgebraicGeometry

universe u

namespace ComplexAnalytic

noncomputable section

/-! ### The naturality square at a distinguished open -/

variable {n k : ℕ} (g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ)
  (f : MvPolynomial (ULift.{u} (Fin n)) ℂ)

/-- **The comparison morphism commutes with passing to a distinguished open**, at the
locally-ringed-space level and at the presentation's own spelling.

`ComplexAnalytic.analytificationToSpecNatTrans`'s naturality at
`ComplexAnalytic.localisationHom`, with the two functors' actions on that morphism unfolded.
Stated separately from the two cover files' vocabulary because it is a fact about one
presentation and its localisation, with no cover in sight;
`ComplexAnalytic.coverIncl_comp_analytificationToSpec` is this square with both sides rewritten
through the identifications of an overlap. -/
theorem toLRSHom_localisationProj_comp_analytificationToSpec :
    (localisationProj.{u} g f).toLRSHom ≫ analytificationToSpec.{u} g =
      analytificationToSpec.{u} (localisationPresentation.{u} g f) ≫
        specFunctor.{u}.map (localisationHom.{u} g f) := by
  have h := analytificationToSpecNatTrans.{u}.naturality (localisationHom.{u} g f)
  simp only [Functor.comp_map, analytificationToSpecNatTrans_app,
    analytificationFunctor_map_localisationPresHom] at h
  exact h

/-! ### The comparison at an overlap

`ComplexAnalytic.coverOverlapIso_hom_coverIncl` — that the overlap's comparison isomorphism
followed into the member is `ComplexAnalytic.localisationProj` — was declared here and is now in
`Oka/Analytification/AffineCover.lean`, unchanged and under the same name. It is a statement in
that file's vocabulary with no `Spec` in it, and it acquired a second consumer in
`Oka/Analytification/CoverRefinement.lean`, which cannot import this file: the `Spec` side is
four `Oka` modules a refinement of an analytic cover has no reason to carry. Its one use below is
unchanged — the `congrArg` in the `calc` of
`ComplexAnalytic.coverIncl_comp_analytificationToSpec`, which is not a rewrite and never was; the
other mention below is a citation in a docstring.
-/

variable {J : Type u} (obj : J → Presentation.{u})
  (poly : ∀ i : J, J → MvPolynomial (ULift.{u} (Fin (obj i).n)) ℂ)

/-- **The comparison morphism at an overlap**, from the analytic overlap as an open subspace of
`A_i^an` to the `Spec`-side overlap as an open subspace of `Spec A_i`.

It is `ComplexAnalytic.analytificationToSpec` of the presentation
`ComplexAnalytic.coverOverlap` — the one object the two cover files share — read through
`ComplexAnalytic.coverOverlapIso` at the source and `ComplexAnalytic.specOverlapIso` at the
target. **Naming it is what makes the two naturality squares compose**: the square at
`ComplexAnalytic.localisationHom` is stated at the presentation and the square at `(glue i j).hom`
is stated at the presentation too, while the compatibility this file needs is stated at the open
subspaces, and this is the morphism the two spellings meet in. -/
def comparisonPart (i j : J) :
    coverPart.{u} obj poly i j ⟶ specPart.{u} obj poly i j :=
  (coverOverlapIso.{u} obj poly i j).inv ≫
    analytificationToSpecNatTrans.{u}.app (coverOverlap.{u} obj poly i j) ≫
      (specOverlapIso.{u} obj poly i j).hom

/-- **The comparison commutes with passing to an overlap.**

The first of the two naturality squares, in the cover files' vocabulary:
`ComplexAnalytic.toLRSHom_localisationProj_comp_analytificationToSpec` with
`ComplexAnalytic.coverOverlapIso_hom_coverIncl` on the analytic side and
`ComplexAnalytic.specLocalisationIso_hom_ofRestrict` on the `Spec` side.

The `show` in the proof is doing one thing and it is worth a sentence: it applies
`ComplexAnalytic.specLocalisationIso_hom_ofRestrict` at the `ComplexAnalytic.specOverlapIso`
spelling **without** `rw [specOverlapIso]`, which would plant an equation lemma on another file's
definition. Nothing would break if it did — `scripts/check_docstring_names.py` has excluded
generated components since lana-agents/oka#261, which is the branch that stopped an `rw` on a
definition in one file from turning off the field-notation rule for that definition's field
citations in every other — but the two spellings are definitionally equal, so the equation lemma
buys nothing, and one `show` avoids leaving the tree a name it did not ask for. Measured when
this file was written: with the `rw` the environment carries
`ComplexAnalytic.specOverlapIso.eq_1` and the file adds one declaration more than it does without
it — eighteen against seventeen at the time, and it is the *difference* that is the point, since
the level moves whenever anything else in the file does. -/
theorem coverIncl_comp_analytificationToSpec (i j : J) :
    coverIncl.{u} obj poly i j ≫ analytificationToSpec.{u} (obj i).g =
      comparisonPart.{u} obj poly i j ≫ specIncl.{u} obj poly i j := by
  rw [comparisonPart, Category.assoc, Category.assoc,
    show (specOverlapIso.{u} obj poly i j).hom ≫ specIncl.{u} obj poly i j =
        specFunctor.{u}.map (localisationHom.{u} (obj i).g (poly i j)) from
      specLocalisationIso_hom_ofRestrict.{u} (obj i).g (poly i j)]
  refine (Iso.eq_inv_comp _).mpr ?_
  calc (coverOverlapIso.{u} obj poly i j).hom ≫
        coverIncl.{u} obj poly i j ≫ analytificationToSpec.{u} (obj i).g
      = ((coverOverlapIso.{u} obj poly i j).hom ≫ coverIncl.{u} obj poly i j) ≫
          analytificationToSpec.{u} (obj i).g := (Category.assoc _ _ _).symm
    _ = (localisationProj.{u} (obj i).g (poly i j)).toLRSHom ≫
          analytificationToSpec.{u} (obj i).g :=
        congrArg (· ≫ analytificationToSpec.{u} (obj i).g)
          (coverOverlapIso_hom_coverIncl.{u} obj poly i j)
    _ = _ := toLRSHom_localisationProj_comp_analytificationToSpec.{u} (obj i).g (poly i j)

variable (glue : ∀ i j : J, coverOverlap.{u} obj poly i j ≅ coverOverlap.{u} obj poly j i)

/-- **The comparison commutes with the transition.**

The second naturality square, and it is `ComplexAnalytic.analytificationToSpecNatTrans`'s
naturality at `(glue i j).hom` and nothing else — `ComplexAnalytic.coverGlueIso` and
`ComplexAnalytic.specGlueIso` are the two functors applied to that one morphism, and the four
`ComplexAnalytic.coverOverlapIso`/`ComplexAnalytic.specOverlapIso` factors of the two transitions
cancel in pairs. -/
theorem comparisonPart_comp_specTransition (i j : J) :
    comparisonPart.{u} obj poly i j ≫ (specTransition.{u} obj poly glue i j).hom =
      (coverTransition.{u} obj poly glue i j).hom ≫ comparisonPart.{u} obj poly j i := by
  have hnat := analytificationToSpecNatTrans.{u}.naturality (glue i j).hom
  simp only [comparisonPart, specTransition, coverTransition, coverGlueIso, specGlueIso,
    Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc, Iso.hom_inv_id_assoc,
    Functor.comp_map] at hnat ⊢
  exact congrArg ((coverOverlapIso.{u} obj poly i j).inv ≫ ·)
    ((reassoc_of% hnat) (specOverlapIso.{u} obj poly j i).hom).symm

/-! ### The comparison morphism -/

variable (hrange : ∀ i j k : J, i ≠ j → i ≠ k → j ≠ k →
    Set.range (coverTripleIncl.{u} obj poly i j k ≫
        coverTransitionHom.{u} obj poly glue i j).base ⊆
      (coverOpen.{u} obj poly j k : Set (coverSpace.{u} obj j)))
  (hsymm : ∀ i j : J, glue j i = (glue i j).symm)
  (hcocycle : ∀ i j k : J, ∀ hij : i ≠ j, ∀ hik : i ≠ k, ∀ hjk : j ≠ k,
    coverTriple.{u} obj poly glue hrange i j k hij hik hjk ≫
      coverTriple.{u} obj poly glue hrange j k i hjk hij.symm hik.symm ≫
      coverTriple.{u} obj poly glue hrange k i j hik.symm hjk.symm hij = 𝟙 _)
  (hrangeSpec : ∀ i j k : J, i ≠ j → i ≠ k → j ≠ k →
    Set.range (specTripleIncl.{u} obj poly i j k ≫
        specTransitionHom.{u} obj poly glue i j).base ⊆
      (specOpen.{u} obj poly j k : Set (specSpace.{u} obj j)))
  (hcocycleSpec : ∀ i j k : J, ∀ hij : i ≠ j, ∀ hik : i ≠ k, ∀ hjk : j ≠ k,
    specTriple.{u} obj poly glue hrangeSpec i j k hij hik hjk ≫
      specTriple.{u} obj poly glue hrangeSpec j k i hjk hij.symm hik.symm ≫
      specTriple.{u} obj poly glue hrangeSpec k i j hik.symm hjk.symm hij = 𝟙 _)

/-- **The `i`-th member's contribution to the comparison morphism**: the affine comparison
`A_i^an ⟶ Spec A_i` followed by the inclusion of `Spec A_i` into `X`. -/
abbrev comparisonPartIota (i : J) :
    coverSpace.{u} obj i ⟶ specGlued.{u} obj poly glue hrangeSpec hsymm hcocycleSpec :=
  analytificationToSpec.{u} (obj i).g ≫
    specIota.{u} obj poly glue hrangeSpec hsymm hcocycleSpec i

/-- **The members' comparison morphisms agree over the overlaps.**

The hypothesis `AlgebraicGeometry.LocallyRingedSpace.GlueData.glueMorphisms` needs, at the pairs a
caller can say anything about. It is the two naturality squares and
`ComplexAnalytic.specIncl_comp_specIota` — the `Spec`-side glue datum's own compatibility, already
read back into the vocabulary the input is written in — and nothing else. -/
theorem comm_comparisonPartIota (i j : J) (hij : i ≠ j) :
    coverIncl.{u} obj poly i j ≫
        comparisonPartIota.{u} obj poly glue hsymm hrangeSpec hcocycleSpec i =
      (coverTransition.{u} obj poly glue i j).hom ≫ coverIncl.{u} obj poly j i ≫
        comparisonPartIota.{u} obj poly glue hsymm hrangeSpec hcocycleSpec j := by
  have hA := coverIncl_comp_analytificationToSpec.{u} obj poly i j
  have hA' := coverIncl_comp_analytificationToSpec.{u} obj poly j i
  have hB := comparisonPart_comp_specTransition.{u} obj poly glue i j
  have hC := specIncl_comp_specIota.{u} obj poly glue hrangeSpec hsymm hcocycleSpec i j hij
  calc coverIncl.{u} obj poly i j ≫
        comparisonPartIota.{u} obj poly glue hsymm hrangeSpec hcocycleSpec i
      = (coverIncl.{u} obj poly i j ≫ analytificationToSpec.{u} (obj i).g) ≫
          specIota.{u} obj poly glue hrangeSpec hsymm hcocycleSpec i := (Category.assoc _ _ _).symm
    _ = (comparisonPart.{u} obj poly i j ≫ specIncl.{u} obj poly i j) ≫
          specIota.{u} obj poly glue hrangeSpec hsymm hcocycleSpec i := congrArg (· ≫ _) hA
    _ = comparisonPart.{u} obj poly i j ≫ specIncl.{u} obj poly i j ≫
          specIota.{u} obj poly glue hrangeSpec hsymm hcocycleSpec i := Category.assoc _ _ _
    _ = comparisonPart.{u} obj poly i j ≫ (specTransition.{u} obj poly glue i j).hom ≫
          specIncl.{u} obj poly j i ≫
            specIota.{u} obj poly glue hrangeSpec hsymm hcocycleSpec j := congrArg (_ ≫ ·) hC
    _ = (comparisonPart.{u} obj poly i j ≫ (specTransition.{u} obj poly glue i j).hom) ≫
          specIncl.{u} obj poly j i ≫
            specIota.{u} obj poly glue hrangeSpec hsymm hcocycleSpec j :=
        (Category.assoc _ _ _).symm
    _ = ((coverTransition.{u} obj poly glue i j).hom ≫ comparisonPart.{u} obj poly j i) ≫
          specIncl.{u} obj poly j i ≫
            specIota.{u} obj poly glue hrangeSpec hsymm hcocycleSpec j := congrArg (· ≫ _) hB
    _ = (coverTransition.{u} obj poly glue i j).hom ≫ comparisonPart.{u} obj poly j i ≫
          specIncl.{u} obj poly j i ≫
            specIota.{u} obj poly glue hrangeSpec hsymm hcocycleSpec j := Category.assoc _ _ _
    _ = (coverTransition.{u} obj poly glue i j).hom ≫
          (comparisonPart.{u} obj poly j i ≫ specIncl.{u} obj poly j i) ≫
            specIota.{u} obj poly glue hrangeSpec hsymm hcocycleSpec j :=
        congrArg (_ ≫ ·) (Category.assoc _ _ _).symm
    _ = (coverTransition.{u} obj poly glue i j).hom ≫
          (coverIncl.{u} obj poly j i ≫ analytificationToSpec.{u} (obj j).g) ≫
            specIota.{u} obj poly glue hrangeSpec hsymm hcocycleSpec j :=
        congrArg
          (fun m ↦ _ ≫ m ≫ specIota.{u} obj poly glue hrangeSpec hsymm hcocycleSpec j) hA'.symm
    _ = _ := congrArg (_ ≫ ·) (Category.assoc _ _ _)

/-- **The comparison morphism `X^an ⟶ X`.**

`AlgebraicGeometry.LocallyRingedSpace.GlueData.glueMorphisms` at the analytic glue datum and the
family `ComplexAnalytic.comparisonPartIota`, whose overlap hypothesis is
`ComplexAnalytic.comm_comparisonPartIota` read through
`ComplexAnalytic.comm_coverGlueData` — which turns a compatibility stated at the chosen overlaps,
which is all a caller has, into the one stated at every pair, which is what a glue datum's
`glue_condition` has.

The source is `(coverAnalytification …).toLocallyRingedSpace` and not
`ComplexAnalytic.coverAnalytification`: the target is a gluing of spectra and is not an analytic
space, so there is no morphism of analytic spaces here to be had. The two spellings of the source
are the same term — `ComplexAnalytic.coverAnalytification_toLocallyRingedSpace` is `rfl` — so a
caller holding `X^an` as an analytic space can use this without transporting anything. -/
def analytificationToSpecGlued :
    (coverAnalytification.{u} obj poly glue hrange hsymm hcocycle).toLocallyRingedSpace ⟶
      specGlued.{u} obj poly glue hrangeSpec hsymm hcocycleSpec :=
  LocallyRingedSpace.GlueData.glueMorphisms
    (coverGlueData.{u} obj poly glue hrange hsymm hcocycle)
    (comparisonPartIota.{u} obj poly glue hsymm hrangeSpec hcocycleSpec)
    (comm_coverGlueData.{u} obj poly glue hrange hsymm hcocycle _
      (comm_comparisonPartIota.{u} obj poly glue hsymm hrangeSpec hcocycleSpec))

/-- **It restricts to the affine comparison on each member.**

`AlgebraicGeometry.LocallyRingedSpace.GlueData.ι_glueMorphisms`, stated at
`ComplexAnalytic.coverIota` rather than at the glue datum's own `ι` — the same choice
`ComplexAnalytic.isOpenImmersion_coverIota` makes, and for the same reason: a statement spelled at
the glue datum's `ι` is a statement about a gluing wearing `X^an`'s name.
`ComplexAnalytic.toLRSHom_coverIota` is the `rfl` that makes the two spellings interchangeable.

**This is the statement that says the construction is the intended one**: everything else here is
true of a morphism that ignores the family it is glued from.

**It is `@[reassoc]` and deliberately not `@[simp]`**, which is a consequence of that choice of
spelling rather than an oversight: `ComplexAnalytic.toLRSHom_coverIota` is itself a `simp` lemma,
so this left-hand side rewrites to the glue datum's `ι` and is not in simp-normal form. **Measured
rather than asserted** — with `@[simp]` planted here and nothing else changed, `lake lint` reports
it and names the lemma that does the rewriting:

    error: @ComplexAnalytic.toLRSHom_coverIota_comp_analytificationToSpecGlued
      Left-hand side simplifies from … to … using
        simp +contextual only [*, @ComplexAnalytic.toLRSHom_coverIota]

`simpNF` is one of the fourteen **environment** linters `lake lint` runs. **`lake exe lint-style`
exits 0 on the same planted attribute with nothing to say**, because it is the seven *text* checks
and cannot see an attribute; `.orchestra/validation.sh` warns in terms against reading a green
there as a green from the environment linters, and this docstring said `lint-style` until
2026-08-30. A proof that wants the normal form has it from `ComplexAnalytic.toLRSHom_coverIota`
for nothing; a *reader* wants this one. -/
@[reassoc]
theorem toLRSHom_coverIota_comp_analytificationToSpecGlued (i : J) :
    (coverIota.{u} obj poly glue hrange hsymm hcocycle i).toLRSHom ≫
        analytificationToSpecGlued.{u} obj poly glue hrange hsymm hcocycle
          hrangeSpec hcocycleSpec =
      analytificationToSpec.{u} (obj i).g ≫
        specIota.{u} obj poly glue hrangeSpec hsymm hcocycleSpec i :=
  LocallyRingedSpace.GlueData.ι_glueMorphisms
    (coverGlueData.{u} obj poly glue hrange hsymm hcocycle) _ _ i

/-- **And it is the only morphism that does.**

`AlgebraicGeometry.LocallyRingedSpace.GlueData.hom_ext` at the analytic glue datum. With the
lemma above this is the universal property in the form a caller uses it, and it is what lets a
consumer identify a morphism into `X` by checking it on the members. -/
theorem analytificationToSpecGlued_unique
    (φ : (coverAnalytification.{u} obj poly glue hrange hsymm hcocycle).toLocallyRingedSpace ⟶
      specGlued.{u} obj poly glue hrangeSpec hsymm hcocycleSpec)
    (h : ∀ i, (coverIota.{u} obj poly glue hrange hsymm hcocycle i).toLRSHom ≫ φ =
      analytificationToSpec.{u} (obj i).g ≫
        specIota.{u} obj poly glue hrangeSpec hsymm hcocycleSpec i) :
    φ = analytificationToSpecGlued.{u} obj poly glue hrange hsymm hcocycle
      hrangeSpec hcocycleSpec :=
  LocallyRingedSpace.GlueData.hom_ext
    (coverGlueData.{u} obj poly glue hrange hsymm hcocycle) _ _ fun i ↦
      (h i).trans (toLRSHom_coverIota_comp_analytificationToSpecGlued.{u} obj poly glue hrange
        hsymm hcocycle hrangeSpec hcocycleSpec i).symm

end

end ComplexAnalytic
