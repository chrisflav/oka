/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Analytification.CoverComparison
import Oka.Analytification.CoverFunctoriality
import Oka.Analytification.SpecFunctoriality

/-!
# The comparison morphism commutes with a morphism of covered schemes

`Oka/Analytification/CoverComparison.lean` builds `X^an ⟶ X` for one covered scheme;
`Oka/Analytification/CoverFunctoriality.lean` and `Oka/Analytification/SpecFunctoriality.lean`
build `X^an ⟶ Y^an` and `X ⟶ Y` from a morphism of covered schemes. **This file is the one
statement that needs all three**: the square they form commutes.

```
        X^an ------ coverMap ------> Y^an
          |                            |
   analytificationToSpecGlued   analytificationToSpecGlued
          |                            |
          v                            v
          X ------- specMap ---------> Y
```

## It is one more instance of one naturality square

`Oka/Analytification/CoverComparison.lean`'s module docstring says its whole content is *"two
instances of one naturality square"*, both of `ComplexAnalytic.analytificationToSpecNatTrans` —
at `ComplexAnalytic.localisationHom`, and at the transition `(glue i j).hom`. **This is the same
transformation a third time, at `ψ i`**, and
`ComplexAnalytic.toLRSHom_map_comp_analytificationToSpec` below is
`ComplexAnalytic.toLRSHom_localisationProj_comp_analytificationToSpec` with the localisation
morphism replaced by the member morphism and **one `simp only` argument fewer**, which is forced
rather than chosen: see that lemma's docstring below.

Nothing else about the comparison morphism enters. In particular no property of
`ComplexAnalytic.analytificationToSpec` beyond naturality is used, and neither
`ComplexAnalytic.comparisonPart` nor either of that file's two squares appears in the proof: they
are what make `ComplexAnalytic.analytificationToSpecGlued` exist, and this file consumes it only
through its restriction lemma.

## The proof is `hom_ext` and four rewrites, and two of them are traps

The square is checked on the members, by
`AlgebraicGeometry.LocallyRingedSpace.GlueData.hom_ext` at the *analytic* glue datum — the target
is a gluing of spectra and is not an analytic space, so
`ComplexAnalytic.coverAnalytification_hom_ext` does not apply and this goes through the glue datum
directly, the same choice `ComplexAnalytic.analytificationToSpecGlued` itself makes. On each
member it is `ComplexAnalytic.coverIota_comp_coverMap`, then
`ComplexAnalytic.toLRSHom_coverIota_comp_analytificationToSpecGlued` on both sides, then the
naturality square and `ComplexAnalytic.specIota_comp_specMap`.

Two things in that are not discoverable from the error messages and are recorded here because
each cost a measured number of attempts:

* **After `AlgebraicGeometry.LocallyRingedSpace.GlueData.hom_ext` the index has type
  `(coverGlueData …).J` and not `J`**, so every lemma stated at `J` stops unifying and the
  failure is reported as a missing rewrite pattern. The per-member statement is therefore proved
  as a `∀ i : J` first and the extensionality closed with `fun i ↦ main i`, where the elaborator
  bridges the definitional equality. `ComplexAnalytic.coverGlueData_U` exists for a sibling of
  this reason, which its docstring gives: `CategoryTheory.GlueData.ofGlueData'` has no projection
  lemmas in Mathlib, measured with the version and the command in
  `Oka/CategoryTheory/GlueData.lean`. **This clause named the sibling for the reason and repeated
  the universal bare until 2026-09-21**, when taxis #2118 gave it the anchor for the evidence.
* **`ComplexAnalytic.analytificationFunctor_obj` is what makes the associativity rewrites fire.**
  `(coverIota …).toLRSHom` has domain `(AnalyticSpace.analytification (obj' (σ i)).g)` where the
  composite expects `(analytificationFunctor.obj (obj' (σ i)))`, and until the two spellings are
  identified `rw [Category.assoc]` fails on a goal that *displays* as `(f ≫ g) ≫ h` — the
  pathology `Oka/CategoryTheory/GlueData.lean`'s module docstring predicts by name. `simp` reports
  it as *"the target expression is not type-correct under the `instances` transparency level"*
  rather than as a rewrite failure, which is the only clue that the two spellings are the cause.
  That lemma was added in `Oka/Analytification/Functor.lean` for the same reason one file over.

## Main results

- `ComplexAnalytic.toLRSHom_map_comp_analytificationToSpec`: **the affine comparison is natural in
  the presentation**, in the spelling the two cover files use.
- `ComplexAnalytic.toLRSHom_coverMap_comp_analytificationToSpecGlued`: **the square commutes**,
  which is what this file exists for.

## What is not here

* **No functor and no naturality *of a functor*.** There is no category of covered schemes in this
  repository, so there is nothing for `ComplexAnalytic.analytificationToSpecGlued` to be a natural
  transformation *between*; what is proved is the square at one morphism of covered data.
  `Oka/Analytification/CoverFunctoriality.lean` makes the same disclaimer about its two laws and
  for the same reason.
* **No non-identity instance.** `OkaTest/ProjectiveLine.lean` and `OkaTest/AffineCover.lean` are
  the two covers this repository has and neither has a map to the other, so nothing below is
  exercised at a `σ` other than the identity. That is a real gap and it is the same one both
  functoriality files record.
* **No statement that either vertical map is an isomorphism.** Those are theorems about
  `ComplexAnalytic.analytificationToSpec` and belong wherever that is studied; this file relates
  two morphisms that already exist.
* **Nothing about cover independence.** Two covers of one scheme is taxis #1107 and is a different
  question: a morphism of cover *data* is what the input here is, and no scheme is an input to
  anything on this line. **This bullet said *"there is no scheme in any of these files"* until
  2026-09-02**, which `Oka/Analytification/SpecScheme.lean` retired; nothing in that module is an
  input, and the distinction is the one this bullet was making.
-/

open CategoryTheory TopologicalSpace AlgebraicGeometry

universe u

namespace ComplexAnalytic

noncomputable section

variable {J K : Type u} (obj : J → Presentation.{u}) (obj' : K → Presentation.{u})
  (σ : J → K) (ψ : ∀ i : J, obj i ⟶ obj' (σ i))

/-- **The comparison morphism commutes with a morphism of presentations**, at the
locally-ringed-space level.

`ComplexAnalytic.analytificationToSpecNatTrans`'s naturality at `ψ i`, with the two functors'
actions unfolded — the same three steps as
`ComplexAnalytic.toLRSHom_localisationProj_comp_analytificationToSpec`, with
`ComplexAnalytic.localisationHom` replaced by the member morphism.

**The one difference is that its `simp only` list has three entries and this one has two, and the
drop is forced.** That lemma unfolds
`ComplexAnalytic.analytificationFunctor_map_localisationPresHom` because its morphism *is* a
`ComplexAnalytic.localisationPresHom`; here the morphism is arbitrary
and there is nothing for it to rewrite. Keeping it is not merely redundant: `lake build` reports
*"This simp argument is unused"*, and `.orchestra/validation.sh` builds with `--wfail`, so it
would fail the build. Measured by putting it back. -/
theorem toLRSHom_map_comp_analytificationToSpec (i : J) :
    (analytificationFunctor.{u}.map (ψ i)).toLRSHom ≫
        analytificationToSpec.{u} (obj' (σ i)).g =
      analytificationToSpec.{u} (obj i).g ≫ specFunctor.{u}.map (ψ i) := by
  have h := analytificationToSpecNatTrans.{u}.naturality (ψ i)
  simp only [Functor.comp_map, analytificationToSpecNatTrans_app] at h
  exact h

/-! ### The square -/

variable (poly : ∀ i : J, J → MvPolynomial (ULift.{u} (Fin (obj i).n)) ℂ)
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
  (hrangeSpec : ∀ i j k : J, i ≠ j → i ≠ k → j ≠ k →
    Set.range (specTripleIncl.{u} obj poly i j k ≫
        specTransitionHom.{u} obj poly glue i j).base ⊆
      (specOpen.{u} obj poly j k : Set (specSpace.{u} obj j)))
  (hcocycleSpec : ∀ i j k : J, ∀ hij : i ≠ j, ∀ hik : i ≠ k, ∀ hjk : j ≠ k,
    specTriple.{u} obj poly glue hrangeSpec i j k hij hik hjk ≫
      specTriple.{u} obj poly glue hrangeSpec j k i hjk hij.symm hik.symm ≫
      specTriple.{u} obj poly glue hrangeSpec k i j hik.symm hjk.symm hij = 𝟙 _)
  (poly' : ∀ i : K, K → MvPolynomial (ULift.{u} (Fin (obj' i).n)) ℂ)
  (glue' : ∀ i j : K, coverOverlap.{u} obj' poly' i j ≅ coverOverlap.{u} obj' poly' j i)
  (hrange' : ∀ i j k : K, i ≠ j → i ≠ k → j ≠ k →
    Set.range (coverTripleIncl.{u} obj' poly' i j k ≫
        coverTransitionHom.{u} obj' poly' glue' i j).base ⊆
      (coverOpen.{u} obj' poly' j k : Set (coverSpace.{u} obj' j)))
  (hsymm' : ∀ i j : K, glue' j i = (glue' i j).symm)
  (hcocycle' : ∀ i j k : K, ∀ hij : i ≠ j, ∀ hik : i ≠ k, ∀ hjk : j ≠ k,
    coverTriple.{u} obj' poly' glue' hrange' i j k hij hik hjk ≫
      coverTriple.{u} obj' poly' glue' hrange' j k i hjk hij.symm hik.symm ≫
      coverTriple.{u} obj' poly' glue' hrange' k i j hik.symm hjk.symm hij = 𝟙 _)
  (hrangeSpec' : ∀ i j k : K, i ≠ j → i ≠ k → j ≠ k →
    Set.range (specTripleIncl.{u} obj' poly' i j k ≫
        specTransitionHom.{u} obj' poly' glue' i j).base ⊆
      (specOpen.{u} obj' poly' j k : Set (specSpace.{u} obj' j)))
  (hcocycleSpec' : ∀ i j k : K, ∀ hij : i ≠ j, ∀ hik : i ≠ k, ∀ hjk : j ≠ k,
    specTriple.{u} obj' poly' glue' hrangeSpec' i j k hij hik hjk ≫
      specTriple.{u} obj' poly' glue' hrangeSpec' j k i hjk hij.symm hik.symm ≫
      specTriple.{u} obj' poly' glue' hrangeSpec' k i j hik.symm hjk.symm hij = 𝟙 _)
  (hcomm : ∀ i j : J, i ≠ j →
    coverIncl.{u} obj poly i j ≫
        (coverMapPart.{u} obj obj' poly' glue' hrange' hsymm' hcocycle' σ ψ i).toLRSHom =
      (coverTransition.{u} obj poly glue i j).hom ≫ coverIncl.{u} obj poly j i ≫
        (coverMapPart.{u} obj obj' poly' glue' hrange' hsymm' hcocycle' σ ψ j).toLRSHom)
  (hcommSpec : ∀ i j : J, i ≠ j →
    specIncl.{u} obj poly i j ≫
        specMapPart.{u} obj obj' poly' glue' hrangeSpec' hsymm' hcocycleSpec' σ ψ i =
      (specTransition.{u} obj poly glue i j).hom ≫ specIncl.{u} obj poly j i ≫
        specMapPart.{u} obj obj' poly' glue' hrangeSpec' hsymm' hcocycleSpec' σ ψ j)

/-- **The square commutes**: the comparison morphism of the source, followed by the induced
morphism of the two gluings of spectra, is the analytified morphism followed by the comparison
morphism of the target.

**A caller supplies eight hypotheses over one datum**, which is the price of holding four objects:
`ComplexAnalytic.coverAnalytification` and `ComplexAnalytic.specGlued` each ask for a range and a
cocycle condition on each side, and `hsymm` is shared because it is a hypothesis on `glue` alone.
The two compatibility hypotheses are genuinely two — one is an equation of morphisms of analytic
spaces read through the forgetful functor and the other of morphisms of locally ringed spaces, and
neither implies the other. `Oka/Analytification/CoverComparison.lean` makes the same accounting
for the four its own input needs.

The proof is the members and nothing else; see this file's module docstring for the two steps in
it that are not discoverable from the error messages. -/
theorem toLRSHom_coverMap_comp_analytificationToSpecGlued :
    (coverMap.{u} obj poly glue hrange hsymm hcocycle obj' poly' glue' hrange' hsymm'
        hcocycle' σ ψ hcomm).toLRSHom ≫
      analytificationToSpecGlued.{u} obj' poly' glue' hrange' hsymm' hcocycle'
        hrangeSpec' hcocycleSpec' =
    analytificationToSpecGlued.{u} obj poly glue hrange hsymm hcocycle hrangeSpec hcocycleSpec ≫
      specMap.{u} obj poly glue hrangeSpec hsymm hcocycleSpec obj' poly' glue' hrangeSpec' hsymm'
        hcocycleSpec' σ ψ hcommSpec := by
  have main : ∀ i : J,
      (coverIota.{u} obj poly glue hrange hsymm hcocycle i).toLRSHom ≫
          (coverMap.{u} obj poly glue hrange hsymm hcocycle obj' poly' glue' hrange' hsymm'
            hcocycle' σ ψ hcomm).toLRSHom ≫
            analytificationToSpecGlued.{u} obj' poly' glue' hrange' hsymm' hcocycle'
              hrangeSpec' hcocycleSpec' =
        (coverIota.{u} obj poly glue hrange hsymm hcocycle i).toLRSHom ≫
          analytificationToSpecGlued.{u} obj poly glue hrange hsymm hcocycle hrangeSpec
              hcocycleSpec ≫
            specMap.{u} obj poly glue hrangeSpec hsymm hcocycleSpec obj' poly' glue' hrangeSpec'
              hsymm' hcocycleSpec' σ ψ hcommSpec := by
    intro i
    have keyL : (coverIota.{u} obj poly glue hrange hsymm hcocycle i).toLRSHom ≫
          (coverMap.{u} obj poly glue hrange hsymm hcocycle obj' poly' glue' hrange' hsymm'
            hcocycle' σ ψ hcomm).toLRSHom =
        (analytificationFunctor.{u}.map (ψ i)).toLRSHom ≫
          (coverIota.{u} obj' poly' glue' hrange' hsymm' hcocycle' (σ i)).toLRSHom :=
      congrArg AnalyticSpace.Hom.toLRSHom
        (coverIota_comp_coverMap.{u} obj poly glue hrange hsymm hcocycle obj' poly' glue'
          hrange' hsymm' hcocycle' σ ψ hcomm i)
    rw [reassoc_of% keyL]
    simp only [analytificationFunctor_obj, Category.assoc]
    rw [toLRSHom_coverIota_comp_analytificationToSpecGlued,
      toLRSHom_coverIota_comp_analytificationToSpecGlued_assoc]
    exact ((reassoc_of% (toLRSHom_map_comp_analytificationToSpec.{u} obj obj' σ ψ i)) _).trans
      (congrArg (analytificationToSpec.{u} (obj i).g ≫ ·)
        (specIota_comp_specMap.{u} obj poly glue hrangeSpec hsymm hcocycleSpec obj' poly' glue'
          hrangeSpec' hsymm' hcocycleSpec' σ ψ hcommSpec i)).symm
  exact LocallyRingedSpace.GlueData.hom_ext
    (coverGlueData.{u} obj poly glue hrange hsymm hcocycle) _ _ fun i ↦ main i

end

end ComplexAnalytic
