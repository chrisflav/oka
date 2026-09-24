/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.AnalyticSpace.PullbackModulesStalk
import Oka.Geometry.RingedSpace.LocallyRingedSpace.Modules
import Oka.Analytification.PresentationFlatness
import Oka.Analytification.Presentation

/-!
# The analytification of a sheaf

For a presentation `g` of a finitely generated `ℂ`-algebra `A`, the comparison morphism
`ComplexAnalytic.analytificationToSpec g : X^an ⟶ Spec A` pulls sheaves of modules back:

```
ComplexAnalytic.analytificationSheaf g :
  SheafOfModules (Spec A).ringSheaf ⥤ SheafOfModules (X^an).ringSheaf
```

**This is the functor whose exactness on coherent sheaves is GAGA**, and it is the object that
every account of this development so far has described as missing.

## It was not missing, and there was no design question

`Oka/Analytification/Presentation.lean` and its siblings say that GAGA needs "the analytification
of a *sheaf*", and call it a construction with a design question in front of it — which
pullback, along what, in which category. **Mathlib has the functor.**
`SheafOfModules.pullback` is defined for any morphism of sheaves of rings over a continuous
functor of sites, as the left adjoint of `SheafOfModules.pushforward`, and
`AlgebraicGeometry.Scheme.Modules` uses exactly it to make sheaves of modules functorial for
schemes. Nothing in it is special to schemes.

The one thing that had to be supplied is
`AlgebraicGeometry.LocallyRingedSpace.Hom.toRingSheafHom`, the morphism of sheaves of rings
attached to a morphism of locally ringed spaces. It is Mathlib's
`AlgebraicGeometry.Scheme.Hom.toRingCatSheafHom` verbatim, four lines. It is in
`Oka/Geometry/RingedSpace/LocallyRingedSpace/Modules.lean`, next to
`AlgebraicGeometry.LocallyRingedSpace.ringSheaf`, because the two have to agree on how the site
is spelled.

## The obstacle really was a coercion

`ringSheaf`'s site used to be `Opens.grothendieckTopology ↑Y`, and
`TopologicalSpace.Opens.map f.base` produces `Opens.grothendieckTopology ↑Y.toPresheafedSpace`.
The two are definitionally equal and **instance search does not cross them**: with the site
spelled `↑Y`, Mathlib's continuity instance for `Opens.map f.base` is not found, because the
discrimination-tree key is built from the elaborated implicit arguments. So with that spelling
`toRingSheafHom` cannot be stated **as things stand** — but this is a cost and not an
impossibility, and `AlgebraicGeometry.LocallyRingedSpace.ringSheaf`'s own docstring is where that
correction lives: the missing instance transports by `inferInstanceAs` from the
`↑Y.toPresheafedSpace` spelling, and with it stated `toRingSheafHom` elaborates at the `↑Y` site.
Re-measured 2026-08-25 at `master` = `d12d334`, positive and negative; this paragraph previously
said that declaring the instance oneself does not help and that `toRingSheafHom` cannot be stated
at all, both of which are false.

Re-spelling `ringSheaf` costs four sites and no proof changes; `ringSheaf`'s own docstring records
why it must stay that way.

## Main definitions

- `ComplexAnalytic.analytificationSheaf`: **the analytification of a sheaf of modules.**
- `ComplexAnalytic.analytificationSheafAdj`: it is left adjoint to pushforward along the
  comparison morphism, which is what determines it.
- `ComplexAnalytic.analytificationSheafUnitToUnit`: **the analytification of `𝒪_X` maps
  canonically to `𝒪_{X^an}`** — the map a comparison theorem between the two structure sheaves
  is a statement about.
- `ComplexAnalytic.analytificationSheafUnitIso`: **that map is an isomorphism**, so the
  analytification of `𝒪_X` *is* `𝒪_{X^an}`; and `ComplexAnalytic.analytificationSheafFreeIso`,
  the same for a free sheaf on any index type.

## Main results

- `ComplexAnalytic.preservesColimits_analytificationSheaf`: **the analytification of a sheaf is
  right exact**, free from the adjunction.
- `ComplexAnalytic.preservesFiniteLimits_analytificationSheaf`: **the analytification of a sheaf
  is left exact** — *GAGA's local half*, and the two together say the functor is exact.

## Exactness, and that no coherence hypothesis appears

**Left exactness is unrestricted.** `preservesFiniteLimits_analytificationSheaf` is stated for all
sheaves of modules on `Spec (ℂ[x] ⧸ I)`, with no finiteness or coherence hypothesis anywhere, and
none of its inputs has one. Coherence is what the classical GAGA *comparison* theorem needs; the
exactness which is its local input is true without it, so the unrestricted form is what is stated
— it is strictly stronger and a consumer can restrict it.

The proof consumes flatness at exactly one place — that `ModuleCat.extendScalars` along
`(analytificationToSpec g).stalkMap y` preserves monomorphisms — and
`Oka/Algebra/Category/ModuleCat/Sheaf/PullbackExact.lean` records the measurement that deleting
it breaks that step and nothing else.

## What is not here

* **The comparison theorem.** GAGA proper also asserts that `Hom` and cohomology agree between
  `X` and `X^an` for coherent sheaves. Exactness of analytification is its local input and is a
  strictly smaller statement.
* **Coherence of the image**, which is next door rather than here.
  `Oka/Analytification/SheafCoherent.lean` proves that the analytification of a **cokernel of
  finite free sheaves** is coherent, out of the exactness proved here and Oka's theorem in every
  finite rank. **The statement for a *coherent* sheaf is a corollary of it and is now proved**,
  as `ComplexAnalytic.isCoherent_analytificationSheaf_of_isCoherent`: the bullet that used to
  stand here said it needed a global presentation of the coherent sheaf and that
  `SheafOfModules.IsCoherent.isFinitePresentation` gives only a local one, which was true, and the
  local-to-global passage is
  `AlgebraicGeometry.Scheme.Modules.exists_isFinite_presentation_of_isCoherent` — algebra on
  `Spec A`, with no analytic input. **The presented form is still the weaker hypothesis and the
  one to apply**; the coherent form is no longer uninhabited, since
  `AlgebraicGeometry.isCoherentStructureSheaf_spec`, and the clause here that said otherwise is
  retired. See `Oka/Analytification/SheafCoherent.lean`.
* **Anything analytic.** Every line here is the `Γ`–`Spec` adjunction and category theory. The
  analytic content is upstream.

## References

- [Hans Grauert and Reinhold Remmert, *Coherent analytic sheaves*][grauert-remmert1984], §A
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

noncomputable section

namespace ComplexAnalytic

variable {n k : ℕ} (g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ)

/-- **The analytification of a sheaf of modules on `Spec (ℂ[x] ⧸ I)`**: pullback along the
comparison morphism `X^an ⟶ Spec (ℂ[x] ⧸ I)`. -/
def analytificationSheaf :
    SheafOfModules.{u}
        (Spec.locallyRingedSpaceObj
          (CommRingCat.of
            (MvPolynomial (ULift.{u} (Fin n)) ℂ ⧸ presentationIdeal.{u} g))).ringSheaf ⥤
      SheafOfModules.{u} (AnalyticSpace.analytification.{u} g).toLocallyRingedSpace.ringSheaf :=
  (analytificationToSpec.{u} g).pullbackModules

/-- **The analytification of a sheaf is left adjoint to pushforward along the comparison
morphism.** It is defined as that left adjoint, so this is the adjunction rather than a theorem
about it — and it is what determines the functor up to unique isomorphism. -/
def analytificationSheafAdj :
    analytificationSheaf.{u} g ⊣
      SheafOfModules.pushforward.{u} (analytificationToSpec.{u} g).toRingSheafHom :=
  (analytificationToSpec.{u} g).pullbackModulesAdj

/-- **The analytification of a sheaf is right exact**, and that half of GAGA's exactness costs
nothing: it is a left adjoint, and a left adjoint preserves colimits.

The half that is *not* free is preservation of finite limits — kernels — and that is exactly
where the flatness of the stalk maps has to be consumed. Stating the free half separately is what
makes the shape of the remaining work visible. -/
theorem preservesColimits_analytificationSheaf :
    Limits.PreservesColimits (analytificationSheaf.{u} g) :=
  (analytificationSheafAdj.{u} g).leftAdjoint_preservesColimits

/-- **The analytification of `𝒪_X` maps canonically to `𝒪_{X^an}`.**

This is what makes the structure sheaf of `X^an` an algebra over the analytification of the
structure sheaf of `X`, and it is the map a comparison theorem between the two is a statement
about. It needs no hypothesis: it is the adjunct of the unit map, which exists for any morphism
of locally ringed spaces. -/
def analytificationSheafUnitToUnit :
    (analytificationSheaf.{u} g).obj
        (SheafOfModules.unit
          (Spec.locallyRingedSpaceObj
            (CommRingCat.of
              (MvPolynomial (ULift.{u} (Fin n)) ℂ ⧸ presentationIdeal.{u} g))).ringSheaf) ⟶
      SheafOfModules.unit
        (AnalyticSpace.analytification.{u} g).toLocallyRingedSpace.ringSheaf :=
  (analytificationToSpec.{u} g).pullbackModulesUnitToUnit

/-- **GAGA's local half: the analytification of a sheaf is left exact.**

Together with `ComplexAnalytic.preservesColimits_analytificationSheaf`, which is free from the
adjunction, this says the functor is **exact**.

It is `AlgebraicGeometry.LocallyRingedSpace.Hom.preservesFiniteLimits_pullbackModules` — pullback
of `𝒪`-modules along a morphism with flat stalk maps is left exact — instantiated at the
comparison morphism, whose stalk maps are faithfully flat by
`ComplexAnalytic.faithfullyFlat_stalkMap_analytificationToSpec`. **That flatness is the only
analytic input**, and it is the only place any flatness is consumed.

There is **no coherence or finiteness hypothesis**; see the module docstring on why the
unrestricted statement is the right one. -/
theorem preservesFiniteLimits_analytificationSheaf :
    Limits.PreservesFiniteLimits (analytificationSheaf.{u} g) :=
  (analytificationToSpec.{u} g).preservesFiniteLimits_pullbackModules
    fun y ↦ (faithfullyFlat_stalkMap_analytificationToSpec.{u} g y).flat

/-- **The analytification of `𝒪_X` is `𝒪_{X^an}`.**

`AlgebraicGeometry.LocallyRingedSpace.Hom.pullbackModulesUnitIso` at the comparison morphism. It
needs nothing analytic — only that `TopologicalSpace.Opens.map` is a final functor — and it is
what makes `ComplexAnalytic.analytificationSheafUnitToUnit` a comparison rather than merely a
map. -/
def analytificationSheafUnitIso :
    (analytificationSheaf.{u} g).obj
        (SheafOfModules.unit
          (Spec.locallyRingedSpaceObj
            (CommRingCat.of
              (MvPolynomial (ULift.{u} (Fin n)) ℂ ⧸ presentationIdeal.{u} g))).ringSheaf) ≅
      SheafOfModules.unit
        (AnalyticSpace.analytification.{u} g).toLocallyRingedSpace.ringSheaf :=
  (analytificationToSpec.{u} g).pullbackModulesUnitIso

/-- **The analytification of a free sheaf is free**, on the same index type, which need not be
finite. This is the base case of any argument that the analytification of a coherent sheaf is
coherent: a coherent sheaf is locally a cokernel of a map of free sheaves, and the analytification
is right exact. -/
def analytificationSheafFreeIso (I : Type u) :
    (analytificationSheaf.{u} g).obj (SheafOfModules.free I) ≅ SheafOfModules.free I :=
  (analytificationToSpec.{u} g).pullbackModulesFreeIso I

end ComplexAnalytic
