/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Algebra.Category.ModuleCat.Sheaf.Coherent.Free
import Oka.AlgebraicGeometry.Modules.Tilde
import Oka.AnalyticSpace.Coherent
import Oka.AnalyticSpace.IdealSheaf
import Oka.Analytification.Sheaf

/-!
# The analytification of a coherent sheaf is coherent

`Oka/Analytification/Sheaf.lean` builds the analytification of a sheaf of modules on
`Spec (ℂ[x] ⧸ I)` and proves it **exact** — right exactness from the adjunction, left exactness
from the flatness of the stalk maps of the comparison morphism. This file draws the conclusion
GAGA consumes: **the analytification of a coherent sheaf is coherent**
(`ComplexAnalytic.isCoherent_analytificationSheaf_of_isCoherent`), through the presented case
(`ComplexAnalytic.isCoherent_analytificationSheaf_cokernel`) which is where the analysis is.

## The coherent statement, and the route it does *not* take

The direct argument does not work and the obstruction is not analytic.
`SheafOfModules.IsCoherent` quantifies over every object of the site and over every morphism
`free L ⟶ M.over X`; downstairs those `L`-indexed families are not in the image of the functor,
so no argument of the form "apply the functor to an upstairs presentation" reaches them.

**The classical route instead gets a presentation out of coherence, and that is what this file
now does.** On `Spec A` the passage is entirely algebraic and happens in
`Oka/AlgebraicGeometry/Modules/Tilde.lean`:

* `SheafOfModules.IsCoherent.isFinitePresentation` — a coherent sheaf is finitely presented on
  *some* covering;
* `AlgebraicGeometry.Scheme.Modules.finitePresentation_Γ_of_isFinitePresentation` — hence `Γ M` is
  a finitely presented `A`-module, which is the quasi-compactness argument on `Spec A`;
* `AlgebraicGeometry.Scheme.Modules.exists_isFinite_presentation_of_isCoherent` — hence `M` has a
  finite **global** `SheafOfModules.Presentation`, through `M ≅ (Γ M)^~` and
  `AlgebraicGeometry.presentationTilde`.

**So the local-to-global step happens at the level of modules and never at the level of sheaves**,
which is why no analytic input is needed for it and why the presented statement below is still
the one carrying all of the mathematics.

Note that **finite presentation is not the finite-type argument run again on the relations**: it
is false at quasicoherent-plus-finite-type, for the reason in the module docstring of
`Oka/AlgebraicGeometry/Modules/Tilde.lean`. That is why the middle step above is
`AlgebraicGeometry.Scheme.Modules.finitePresentation_Γ_of_isFinitePresentation`, which carries
`SheafOfModules.IsFinitePresentation` in its hypothesis and in its name, and not
`SheafOfModules.IsFiniteType`.

**That is a statement about which hypothesis suffices, and not about the class being absent.**
`SheafOfModules.IsFiniteType` occurs below and is load-bearing: it is a hypothesis of
`SheafOfModules.IsCoherent.cokernel`, it is supplied by hand inside
`ComplexAnalytic.isCoherent_analytificationSheaf_cokernel`, and
`SheafOfModules.GeneratingSections.IsFiniteType` is what makes the two index types of a
`SheafOfModules.Presentation` finite in the proof of the coherent statement. What it does not do
is reach `Module.FinitePresentation A (Γ M)`, which is the module-level step.

## The coherent statement now has a witness, and the presented form is still the one to apply

**This section used to say the coherent statement had no witness in this repository**, because no
sheaf on a `Spec` was proved coherent and every coherent sheaf this development exhibited lived on
an analytic space. `AlgebraicGeometry.isCoherentStructureSheaf_spec` retired that, so the
hypothesis is inhabited.

**Do not read the coherent statement as superseding the presented one.** It is a corollary of it,
and its hypothesis is strictly stronger.

## The proof, which is three transports and no new mathematics

`SheafOfModules.IsCoherent.cokernel` needs a source of finite type and a **coherent target**;
`SheafOfModules.IsCoherent.free` supplies the target, out of Oka's theorem
(`ComplexAnalytic.AnalyticSpace.isCoherent_free`), and the analytification of a free sheaf is
free on the same index type (`ComplexAnalytic.analytificationSheafFreeIso`). Right exactness
moves the cokernel across the functor. Nothing is computed.

## Main results

- `ComplexAnalytic.isCoherent_analytificationSheaf_cokernel`: **the analytification of the
  cokernel of a morphism of finite free sheaves is coherent.**
- `ComplexAnalytic.isCoherent_analytificationSheaf_of_isCoherent`: **the analytification of a
  coherent sheaf is coherent**, which is the previous statement plus the affine dictionary.
- `ComplexAnalytic.isCoherent_analytificationSheaf_cokernel_sectionsHom`: the same for the
  quotient of `𝒪_{Spec A}` by a finitely generated ideal sheaf, which is the shape a subscheme
  of `Spec (ℂ[x] ⧸ I)` arrives in.

## What is *not* here

**GAGA proper.** Agreement of `Hom` and of cohomology across analytification is untouched. The
negative on record — that faithfully flat descent from
`ComplexAnalytic.faithfullyFlat_stalkMap_analytificationToSpec` does not give it, because
`X^an ⟶ Spec A` misses every non-closed point — is *unmeasured*, and should be re-measured
before it is relied on.

## References

- [Jean-Pierre Serre, *Géométrie algébrique et géométrie analytique*][serre1956]
- [Hans Grauert and Reinhold Remmert, *Coherent analytic sheaves*][grauert-remmert1984], §A
-/

open CategoryTheory AlgebraicGeometry Limits

universe u

noncomputable section

namespace ComplexAnalytic

variable {n k : ℕ} (g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ)

/-- **The analytification of the cokernel of a morphism of finite free sheaves is coherent.**

The target `(free K)^an` is free of the same rank, hence coherent by
`ComplexAnalytic.AnalyticSpace.isCoherent_free`, which is Oka's theorem in every finite rank;
the source `(free I)^an` is free, hence of finite type; and the analytification, being a left
adjoint, carries the cokernel to the cokernel. `SheafOfModules.IsCoherent.cokernel` then applies,
and note that it asks only for the *source* to be of finite type — no coherence of `(free I)^an`
is used. -/
theorem isCoherent_analytificationSheaf_cokernel {I K : Type u} [Finite I] [Finite K]
    (ψ : SheafOfModules.free (R := (Spec.locallyRingedSpaceObj (CommRingCat.of
          (MvPolynomial (ULift.{u} (Fin n)) ℂ ⧸ presentationIdeal.{u} g))).ringSheaf) I ⟶
      SheafOfModules.free (R := (Spec.locallyRingedSpaceObj (CommRingCat.of
          (MvPolynomial (ULift.{u} (Fin n)) ℂ ⧸ presentationIdeal.{u} g))).ringSheaf) K) :
    ((analytificationSheaf.{u} g).obj (cokernel ψ)).IsCoherent := by
  haveI := preservesColimits_analytificationSheaf.{u} g
  haveI : ((analytificationSheaf.{u} g).obj (SheafOfModules.free I)).IsFiniteType :=
    SheafOfModules.IsFiniteType.of_iso
      (M := SheafOfModules.free (R := (AnalyticSpace.analytification.{u}
        g).toLocallyRingedSpace.ringSheaf) I)
      (analytificationSheafFreeIso.{u} g I).symm
  haveI : (SheafOfModules.free (R := (AnalyticSpace.analytification.{u}
      g).toLocallyRingedSpace.ringSheaf) K).IsCoherent :=
    (AnalyticSpace.analytification.{u} g).isCoherent_free K
  haveI : ((analytificationSheaf.{u} g).obj (SheafOfModules.free K)).IsCoherent :=
    SheafOfModules.IsCoherent.of_iso
      (M := SheafOfModules.free (R := (AnalyticSpace.analytification.{u}
        g).toLocallyRingedSpace.ringSheaf) K)
      (analytificationSheafFreeIso.{u} g K).symm
  haveI : (cokernel ((analytificationSheaf.{u} g).map ψ)).IsCoherent :=
    SheafOfModules.IsCoherent.cokernel _
  exact SheafOfModules.IsCoherent.of_iso
    (M := cokernel ((analytificationSheaf.{u} g).map ψ))
    (PreservesCokernel.iso (analytificationSheaf.{u} g) ψ).symm

/-- **The analytification of the quotient of `𝒪_{Spec A}` by a finitely generated ideal sheaf is
coherent.**

`AlgebraicGeometry.LocallyRingedSpace.sectionsHom f : 𝒪^I ⟶ 𝒪` is the map whose cokernel is that
quotient, and it is a morphism of finite free sheaves once `𝒪` is read as `free PUnit`
(`SheafOfModules.freePUnitIso`); composing with an isomorphism does not change the cokernel
(`CategoryTheory.Limits.cokernelCompIsIso`). This is the shape in which a closed subscheme of
`Spec (ℂ[x] ⧸ I)` presents its structure sheaf. -/
theorem isCoherent_analytificationSheaf_cokernel_sectionsHom {I : Type u} [Finite I]
    (f : I → (Spec.locallyRingedSpaceObj (CommRingCat.of
        (MvPolynomial (ULift.{u} (Fin n)) ℂ ⧸ presentationIdeal.{u} g))).presheaf.obj
      (Opposite.op ⊤)) :
    ((analytificationSheaf.{u} g).obj (cokernel
      ((Spec.locallyRingedSpaceObj (CommRingCat.of
        (MvPolynomial (ULift.{u} (Fin n)) ℂ ⧸ presentationIdeal.{u} g))).sectionsHom
          f))).IsCoherent := by
  haveI : ((analytificationSheaf.{u} g).obj (cokernel
      ((Spec.locallyRingedSpaceObj (CommRingCat.of
        (MvPolynomial (ULift.{u} (Fin n)) ℂ ⧸ presentationIdeal.{u} g))).sectionsHom f ≫
          (SheafOfModules.freePUnitIso).inv))).IsCoherent :=
    isCoherent_analytificationSheaf_cokernel.{u} g _
  exact SheafOfModules.IsCoherent.of_iso
    (M := (analytificationSheaf.{u} g).obj (cokernel
      ((Spec.locallyRingedSpaceObj (CommRingCat.of
        (MvPolynomial (ULift.{u} (Fin n)) ℂ ⧸ presentationIdeal.{u} g))).sectionsHom f ≫
          (SheafOfModules.freePUnitIso).inv)))
    ((analytificationSheaf.{u} g).mapIso (cokernelCompIsIso _ _))

set_option backward.isDefEq.respectTransparency false in
/-- **The analytification of a coherent sheaf is coherent.**

The statement GAGA is usually quoted as needing, and it is
`ComplexAnalytic.isCoherent_analytificationSheaf_cokernel` plus the affine dictionary. All of the
analysis is in that theorem — Oka's coherence of `𝒪_X` in every finite rank, and right exactness
of the analytification; **this adds no analysis at all.** What it adds is
`AlgebraicGeometry.Scheme.Modules.exists_isFinite_presentation_of_isCoherent`, which turns
coherence on `Spec A` into a finite *global* presentation, and
`SheafOfModules.Presentation.cokernelIso`, which reads that presentation as a cokernel of finite
free sheaves so the presented theorem applies. See the module docstring for why the
local-to-global step is algebraic.

**This hypothesis used to be uninhabited in this repository**, and the paragraph here said so.
`AlgebraicGeometry.isCoherentStructureSheaf_spec` inhabits it.
`ComplexAnalytic.isCoherent_analytificationSheaf_cokernel` remains the
form to apply when only a presentation is in hand, which is the weaker hypothesis and the one
every other witness in this development satisfies.

**The `set_option` is the `Spec R` versus `Spec (CommRingCat.of ↑R)` seam.** The hypothesis
arrives as `M.IsCoherent` at the `AlgebraicGeometry.LocallyRingedSpace.ringSheaf` spelling of the
base and is consumed at the `AlgebraicGeometry.Scheme.Modules` spelling; the two are definitionally
equal — that equality is `rfl`, measured — but instance search does not cross it without the
option. Measured by deleting it; no explanation is offered. -/
theorem isCoherent_analytificationSheaf_of_isCoherent
    (M : SheafOfModules.{u} (Spec.locallyRingedSpaceObj (CommRingCat.of
        (MvPolynomial (ULift.{u} (Fin n)) ℂ ⧸ presentationIdeal.{u} g))).ringSheaf)
    [M.IsCoherent] :
    ((analytificationSheaf.{u} g).obj M).IsCoherent := by
  obtain ⟨P, hP⟩ := AlgebraicGeometry.Scheme.Modules.exists_isFinite_presentation_of_isCoherent
    (R := CommRingCat.of (MvPolynomial (ULift.{u} (Fin n)) ℂ ⧸ presentationIdeal.{u} g)) M
  haveI := hP
  haveI : Finite P.generators.I :=
    SheafOfModules.GeneratingSections.IsFiniteType.finite (σ := P.generators)
  haveI : Finite P.relations.I :=
    SheafOfModules.GeneratingSections.IsFiniteType.finite (σ := P.relations)
  haveI : ((analytificationSheaf.{u} g).obj (cokernel
      ((SheafOfModules.freeHomEquiv _).symm P.relations.s ≫ kernel.ι P.generators.π))).IsCoherent :=
    isCoherent_analytificationSheaf_cokernel.{u} g _
  exact SheafOfModules.IsCoherent.of_iso
    (M := (analytificationSheaf.{u} g).obj (cokernel
      ((SheafOfModules.freeHomEquiv _).symm P.relations.s ≫ kernel.ι P.generators.π)))
    ((analytificationSheaf.{u} g).mapIso P.cokernelIso)

end ComplexAnalytic
