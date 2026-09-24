/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.AnalyticSpace.Glue
import Oka.Geometry.RingedSpace.LocallyRingedSpace.HasColimits

/-!
# The disjoint union of a family of complex analytic spaces

`ComplexAnalytic.AnalyticSpace.ofOpenCover` builds an analytic space from a cover of a locally
ringed space by abstract spaces mapping in by open immersions. The inclusions of a coproduct are
such a cover — `AlgebraicGeometry.LocallyRingedSpace.sigmaOpenCover` — so a disjoint union of
analytic spaces is one application of it, once its compatibility hypothesis is discharged.

**That hypothesis is the whole of the work, and disjointness is the whole of the hypothesis.**
`ComplexAnalytic.AnalyticSpace.ofOpenCover` asks for `TopCat.Presheaf.IsCompatible`: the
`ℂ`-algebra structures carried from the members must agree on the pairwise intersections of the
members' images. For a coproduct those intersections are `⊥` for `i ≠ j`
(`AlgebraicGeometry.LocallyRingedSpace.disjoint_opensRange_sigmaOpenCover`), and the sections of a
sheaf over `⊥` form the terminal ring, so any two of them agree; for `i = j` the two restrictions
are the same map. There is no analysis and no sheaf argument in it.

## Main definitions

- `ComplexAnalytic.AnalyticSpace.sigma`: **the disjoint union**, whose underlying locally ringed
  space is the coproduct on the nose.
- `ComplexAnalytic.AnalyticSpace.sigmaι`: the inclusion of a member, as a morphism of analytic
  spaces.
- `ComplexAnalytic.AnalyticSpace.sigmaDesc`: the morphism out of a disjoint union determined by a
  morphism out of each member.
- `ComplexAnalytic.AnalyticSpace.cofanSigma`: the inclusions read as a
  `CategoryTheory.Limits.Cofan` on the disjoint union, which is the shape the colimit interface
  presents them in.

## Main results

- `ComplexAnalytic.AnalyticSpace.comapAlgMap_sigma`: **the disjoint union's `ℂ`-algebra structure
  pulls back to each member's own**, which is what says the object is the disjoint union and not
  an unrelated space with the right carrier.
- `ComplexAnalytic.AnalyticSpace.sigmaHomeoSigma`: **and its underlying space is the topological
  disjoint union of the members' underlying spaces**, as a homeomorphism onto the `Sigma` type.
  `ComplexAnalytic.AnalyticSpace.sigmaHomeoSigma_symm_apply` and
  `ComplexAnalytic.AnalyticSpace.sigmaHomeoSigma_preimage_range` say it is the identification the
  inclusions make and not some other homeomorphism with the same source and target. **This is the
  one statement in this file about the *topology* of `ComplexAnalytic.AnalyticSpace.sigma`** —
  everything else here is about its carrier, its `ℂ`-algebra structure or its universal property,
  and `≃ₜ` occurs in this file only in the type of the declaration below. It is the
  locally-ringed-space statement of the same shape read at a `rfl`, and it was added on
  2026-09-20, with the two lemmas beside it, by taxis #2094.
- `ComplexAnalytic.isCLinearHom_sigmaDesc`: **a descent map out of a coproduct of locally ringed
  spaces is `ℂ`-linear as soon as its restrictions are**, with no agreement-on-overlaps
  hypothesis. Nothing in it is analytic, so it is stated for a family of locally ringed spaces.
- `ComplexAnalytic.AnalyticSpace.sigmaι_sigmaDesc`: **the descent map restricts to the given
  morphism on each member**, which is the universal property in the form this file keeps.
- `ComplexAnalytic.AnalyticSpace.hom_ext_sigma`: **and a morphism out of a disjoint union is
  determined by those restrictions**, which is its uniqueness half. No agreement of the
  restrictions is asked for anywhere, in either direction.
- `ComplexAnalytic.AnalyticSpace.isColimitCofanSigma`: **the two halves above, bundled — the
  disjoint union is the coproduct.** `## What is not here` used to say this bundle was absent and
  that nothing consumed one.
- `ComplexAnalytic.AnalyticSpace.hasCoproducts` and
  `ComplexAnalytic.AnalyticSpace.hasFiniteCoproducts`: **the category of analytic spaces has
  coproducts of families indexed by any type of its own universe, and finite ones**, which is
  what lets `∐` and `⨿` be written for these objects. The second is
  `CategoryTheory.Limits.hasFiniteCoproducts_of_hasCoproducts` at the first and adds no
  mathematics; the finite index types it quantifies over live in `Type 0` and are reached by
  `CategoryTheory.Discrete.equivalence`.
- `ComplexAnalytic.AnalyticSpace.isEmpty_sigma`,
  `ComplexAnalytic.AnalyticSpace.isEmpty_sigma_of_members` and
  `ComplexAnalytic.AnalyticSpace.not_surjective_sigmaι_base`: the non-vacuity statements, at
  either end — the disjoint union is empty when the index type is empty and when the members are,
  and an inclusion is not surjective when a second member has a point.
- `ComplexAnalytic.AnalyticSpace.not_isIso_sigmaι`: **so an inclusion is not an isomorphism**,
  under the same two hypotheses. **This is still not a statement that the disjoint union and the
  member are non-isomorphic** — that would be a statement about an invariant, and the caveat on
  the item above applies here word for word.
- `ComplexAnalytic.AnalyticSpace.isIso_sigmaι`: **at a subsingleton index type it is one**, which
  is the case `ComplexAnalytic.AnalyticSpace.not_surjective_sigmaι_base` and
  `ComplexAnalytic.AnalyticSpace.not_isIso_sigmaι` exclude by asking for a second index with an
  inhabited member. Its inverse is a descent map, so nothing about the structure sheaves is
  computed on the way.

## Why the descent map needs a lemma at all

`ComplexAnalytic.AnalyticSpace.Hom` carries an `IsCLinearHom` field, and the universal property of
the coproduct in `AlgebraicGeometry.LocallyRingedSpace` does not supply it: it produces a morphism
of locally ringed spaces and nothing more. `ComplexAnalytic.IsCLinearHom.of_openCover` says
`ℂ`-linearity is local on the source and asks for **no** agreement of the pieces on the overlaps —
which is exactly why it applies here, where the map arrives from a universal property rather than
from `AlgebraicGeometry.LocallyRingedSpace.OpenCover.glueMorphisms` and so carries no such
hypothesis to hand over.

## One seam, and it is not the one it looks like

**Supply `ComplexAnalytic.AnalyticSpace.comapAlgMap_ofOpenCover_algebraMap`'s cover argument
explicitly.** With every argument left as `_` the unifier works backwards from the goal into the
coproduct and does not come back: elaboration fails with a heartbeat timeout that survives
`maxHeartbeats 2000000`. Nothing about the statement is at fault — `#check` on it is instant.

**It is the cover and not the rest**, measured in both directions: naming the cover and leaving
the family, the compatibility and the local models as `_` elaborates in seconds, while naming
those three and leaving the cover as `_` still times out. The shape to recognise is therefore **a
projection of an earlier argument in a later argument's type** — the index `j` has type `𝒰.J`, so
a metavariable cover hands the unifier `?𝒰.J =?= ι`, which it cannot invert and so unfolds. That
rule is about the projection and not about coproducts, and it reaches past this lemma.

**The spelling of the round trip is not part of it**, which is worth saying because it looks as
though it should be. `(sigmaCover F).map j` and `Sigma.ι _ j` are equal by `rfl` and **not**
reducibly — `with_reducible rfl` fails on them — and yet the round trip below proves at either
spelling with the arguments named, and fails at either spelling with them left as `_`. The
statement uses `(sigmaCover F).map j` because that is the shape the cover-indexed consumers
(`ComplexAnalytic.IsCLinearHom.of_openCover` among them) present, not because the other spelling
costs anything.

## What is not here

**This section used to open by saying that no `CategoryTheory.Limits.IsColimit` was here, that the
two halves of the universal property were here as separate lemmas, and that what the bundle would
additionally buy was an interface nothing consumed. The bundle is here now and the reason it was
worth building is the interface it buys.** `ComplexAnalytic.AnalyticSpace.isColimitCofanSigma`
is it, and **the mathematics is still the two lemmas**:
`ComplexAnalytic.AnalyticSpace.sigmaι_sigmaDesc` is existence and
`ComplexAnalytic.AnalyticSpace.hom_ext_sigma` is uniqueness, and the bundle passes each of them to
one field of `CategoryTheory.Limits.Cofan.IsColimit.mk` and proves nothing of its own. What it
adds is the interface — the cofan, `ComplexAnalytic.AnalyticSpace.hasCoproducts` and
`ComplexAnalytic.AnalyticSpace.hasFiniteCoproducts`, and `∐` and `⨿` becoming writable for these
objects.

**What asks for that interface is `Mathlib/CategoryTheory/Galois/Basic.lean`'s definition of a
Galois category**, whose namespace is not in this file's import closure and so cannot be
cited by name here. **What is here does not satisfy it.** That definition asks for finite
coproducts of the *category of finite étale covers of a fixed base*, which is
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver`; the instances below are about
`ComplexAnalytic.AnalyticSpace`, and carrying a colimit from the one to the other is a statement
about that comma category which this file does not make. So the reading to avoid is that the
axiom is stated here: what is here is the ingredient it would be built from.

**That statement is made in `Oka/AnalyticSpace/FiniteEtaleOver.lean`**, as
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.hasFiniteCoproducts`, and its proof reads
`ComplexAnalytic.AnalyticSpace.sigmaι_sigmaDesc` and
`ComplexAnalytic.AnalyticSpace.hom_ext_sigma` rather than
`ComplexAnalytic.AnalyticSpace.isColimitCofanSigma`: the descent map has to be re-wrapped as a
morphism over the base in any case, and once it is there is nothing left for the bundle to carry.
**So this file's own claim — that it does not make that statement — stays exact**, and what would
go stale is a reading of it as a claim that no file makes it.

**Nothing about `ComplexAnalytic.AnalyticSpace.IsFinite` or
`ComplexAnalytic.AnalyticSpace.IsLocalIso`** for the inclusions or for `∐_{Fin n} X ⟶ X`, and no
count of sheets. All of it is `Oka/AnalyticSpace/SigmaFiniteEtale.lean`'s, which imports this
file — **and the reason is not the same for the two**. The descent map's needs the fibres of that
map, which is why it is stated where they are; the **inclusion**'s needs only that the members
are pairwise disjoint, which is `ComplexAnalytic.AnalyticSpace.not_surjective_sigmaι_base`'s own
input and is here, so `ComplexAnalytic.AnalyticSpace.isFiniteEtale_sigmaι` is over there for the
import edge to `Oka/AnalyticSpace/Finite.lean` alone: this file reaches neither of the two
classes. It is not that its proofs read nothing from here —
`ComplexAnalytic.AnalyticSpace.isLocalIso_sigmaι`, one of the two rungs it is built from, rewrites
with `ComplexAnalytic.AnalyticSpace.sigmaι_toLRSHom` twice.

**No claim that the disjoint union is not one of its members** beyond
`ComplexAnalytic.AnalyticSpace.not_surjective_sigmaι_base`, which is about the *inclusion* being
non-surjective on points at a two-member family with the other member inhabited. That an analytic
space is not *isomorphic* to another is a statement about an invariant and nothing here computes
one.
## The `Mathlib/CategoryTheory/Galois/Basic.lean` scoping, and the record for it

**Every sentence of this file that scopes that namespace read *this repository's import closure*,
until 2026-09-15**, when `Oka/AnalyticSpace/GaloisCategory.lean` imported that file and declared
`CategoryTheory.PreGaloisCategory` at
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver` together with
`CategoryTheory.PreGaloisCategory.FiberFunctor` at its `FintypeCat`-valued fibre functor. **From
that commit the class is in this repository's import closure and is still not in this file's**,
which is why those sentences now say *this file's*: no import of this module reaches the one that
pays for the class, so nothing here can name it and every clause of this file that says so stays
exact. The rescoping is this file's whole share of that push, and `git diff` against the commit it
is cut from shows it.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
  AlgebraicGeometry.LocallyRingedSpace TopologicalSpace

universe u

namespace ComplexAnalytic

noncomputable section

variable {ι : Type u} (F : ι → AnalyticSpace.{u})

namespace AnalyticSpace

/-- **The inclusions of a family of analytic spaces are an open cover of their coproduct**, taken
in `AlgebraicGeometry.LocallyRingedSpace`. This is
`AlgebraicGeometry.LocallyRingedSpace.sigmaOpenCover` at the underlying spaces, named because
every statement below is indexed by it. -/
def sigmaCover : (∐ fun i ↦ (F i).toLocallyRingedSpace : LocallyRingedSpace.{u}).OpenCover :=
  sigmaOpenCover fun i ↦ (F i).toLocallyRingedSpace

@[simp]
lemma sigmaCover_obj (j : ι) : (sigmaCover F).obj j = (F j).toLocallyRingedSpace := rfl

/-- **The `ℂ`-algebra structures of the members are compatible on the coproduct.**

The hypothesis of `ComplexAnalytic.AnalyticSpace.ofOpenCover`, and the only thing between a
coproduct of analytic spaces and an analytic space. For `i = j` the two restrictions are the same
morphism of `TopologicalSpace.Opens`, which is a proposition-valued category, so the two sides are
the same term. For `i ≠ j` the intersection of the two members' images is `⊥`, by
`AlgebraicGeometry.LocallyRingedSpace.disjoint_opensRange_sigmaOpenCover` and `disjoint_iff`, and
the sections of a sheaf over `⊥` are a terminal ring — `TopCat.Sheaf.isTerminalOfEqEmpty` and
`CommRingCat.subsingleton_of_isTerminal` — so *any* two of them agree and nothing about the
structures is used. -/
theorem isCompatible_sigma (c : ℂ) :
    TopCat.Presheaf.IsCompatible
      (∐ fun i ↦ (F i).toLocallyRingedSpace : LocallyRingedSpace.{u}).presheaf
      (fun j ↦ ((sigmaCover F).opensRange j).isOpenEmbedding.isOpenMap.functor.obj ⊤)
      fun j ↦ (sigmaCover F).restrictAlgMap j (F j).algebraMap c := by
  intro i j
  by_cases hij : i = j
  · subst hij; rfl
  · have hd : ((sigmaCover F).opensRange i) ⊓ ((sigmaCover F).opensRange j) = ⊥ :=
      disjoint_iff.mp (disjoint_opensRange_sigmaOpenCover _ hij)
    have hbot : (((sigmaCover F).opensRange i).isOpenEmbedding.isOpenMap.functor.obj ⊤) ⊓
        (((sigmaCover F).opensRange j).isOpenEmbedding.isOpenMap.functor.obj ⊤) = ⊥ := by
      simpa using hd
    haveI : Subsingleton
        ((∐ fun i ↦ (F i).toLocallyRingedSpace : LocallyRingedSpace.{u}).presheaf.obj (op
          ((((sigmaCover F).opensRange i).isOpenEmbedding.isOpenMap.functor.obj ⊤) ⊓
            (((sigmaCover F).opensRange j).isOpenEmbedding.isOpenMap.functor.obj ⊤)))) :=
      CommRingCat.subsingleton_of_isTerminal
        ((∐ fun i ↦ (F i).toLocallyRingedSpace : LocallyRingedSpace.{u}).sheaf.isTerminalOfEqEmpty
          hbot)
    exact Subsingleton.elim _ _

/-- **The disjoint union of a family of complex analytic spaces.**

`ComplexAnalytic.AnalyticSpace.ofOpenCover` at the coproduct's own open cover, with each member's
`ℂ`-algebra structure and each member's local models. Its underlying locally ringed space is the
coproduct on the nose, which is
`ComplexAnalytic.AnalyticSpace.sigma_toLocallyRingedSpace` below. -/
def sigma : AnalyticSpace.{u} :=
  ofOpenCover (sigmaCover F) (fun j ↦ (F j).algebraMap) (isCompatible_sigma F)
    fun j ↦ (F j).hasLocalModels

@[simp]
lemma sigma_toLocallyRingedSpace :
    (sigma F).toLocallyRingedSpace = ∐ fun i ↦ (F i).toLocallyRingedSpace := rfl

/-- **The disjoint union's `ℂ`-algebra structure pulls back to each member's own.**

This is the statement that `ComplexAnalytic.AnalyticSpace.sigma` is the disjoint union rather than
some other analytic space with the right carrier, and it is what makes the inclusions `ℂ`-linear.

**Stated at `(sigmaCover F).map j`** because that is the shape the cover-indexed consumers
present; `Sigma.ι _ j` is the same morphism by `rfl` — though not reducibly — and the statement
proves at that spelling too. See the header on what the actual seam is. -/
theorem comapAlgMap_sigma (j : ι) :
    comapAlgMap ((sigmaCover F).map j) (sigma F).algebraMap = (F j).algebraMap :=
  comapAlgMap_ofOpenCover_algebraMap (sigmaCover F) (fun j ↦ (F j).algebraMap)
    (isCompatible_sigma F) (fun j ↦ (F j).hasLocalModels) j

/-- **The inclusion of a member into the disjoint union**, as a morphism of analytic spaces.

Its underlying morphism of locally ringed spaces is the coproduct inclusion, and its
`ℂ`-linearity is `ComplexAnalytic.AnalyticSpace.comapAlgMap_sigma` read elementwise. -/
def sigmaι (j : ι) : F j ⟶ sigma F where
  toLRSHom' := (sigmaCover F).map j
  isCLinear c := congrArg (fun m : ℂ →+* _ ↦ m c) (comapAlgMap_sigma F j)

@[simp]
lemma sigmaι_toLRSHom (j : ι) :
    (sigmaι F j).toLRSHom = Sigma.ι (fun i ↦ (F i).toLocallyRingedSpace) j := rfl

/-- **The space underlying the disjoint union is the topological disjoint union of the members'
spaces.**

`AlgebraicGeometry.LocallyRingedSpace.sigmaHomeoSigma` read here, and **there is nothing to
transport**: `ComplexAnalytic.AnalyticSpace.sigma_toLocallyRingedSpace` is `rfl`, so the carrier of
`ComplexAnalytic.AnalyticSpace.sigma` *is* the carrier of the locally-ringed-space coproduct and
the two statements have the same type.

**What this adds to `ComplexAnalytic.AnalyticSpace.sigma`'s own docstring is the topology.** That
the carrier is the coproduct's is `rfl`; that the coproduct's carrier is the `Sigma` type, with the
disjoint-union topology, is the mirror-tree statement and is not.

**A bijection would not do for the consumer this is built for.**
`Oka/AnalyticSpace/ConnectedComponents.lean` reads connected components off the members, and a
continuous bijection carries neither a clopen set nor a component; the open half of the
identification is `AlgebraicGeometry.LocallyRingedSpace.sigmaι_isOpenImmersion`, spent one level
down. -/
def sigmaHomeoSigma : ((sigma F : AnalyticSpace.{u}) : Type u) ≃ₜ
    Σ i, ((F i : AnalyticSpace.{u}) : Type u) :=
  LocallyRingedSpace.sigmaHomeoSigma fun i ↦ (F i).toLocallyRingedSpace

/-- **Its inverse sends a pair to the image of the second component under the inclusion of the
first**, by `rfl`.

**Not a `@[simp]` lemma, and the reason is a run of `lake lint` and not a preference.** With the
attribute, `simpNF` reports *Left-hand side simplifies* and names
`dsimp only [ComplexAnalytic.AnalyticSpace.sigma_toLocallyRingedSpace]` as what does it: that
lemma is itself `@[simp]`, and what it rewrites here is the *type* of the homeomorphism's source,
`↑↑(sigma F).toPresheafedSpace` to `↑↑(∐ fun i ↦ (F i).toLocallyRingedSpace).toPresheafedSpace`,
so the left-hand side is not in simp normal form however the right-hand side is spelled. **The
analogue one level down, `AlgebraicGeometry.LocallyRingedSpace.sigmaHomeoSigma_symm_apply`, has no
such neighbour and is a simp lemma there**, which is the difference the `rfl` above hides. -/
lemma sigmaHomeoSigma_symm_apply (j : ι) (x : F j) :
    (sigmaHomeoSigma F).symm ⟨j, x⟩ = (sigmaι F j).toLRSHom.base x := rfl

/-- **The member of the disjoint union indexed by `j` is the image of the `j`-th inclusion**, as
sets of points.

This is the form a statement about the pieces consumes, and it is what says the identification
above is the one the inclusions make and not some other homeomorphism with the same source and
target. The proof is three steps and no mathematics: `Homeomorph.image_symm` reads the preimage as
the image under the inverse, `Set.range_comp` reads that image of a range as the range of a
composite, and the composite is the inclusion's map on points by `rfl` — which is
`ComplexAnalytic.AnalyticSpace.sigmaHomeoSigma_symm_apply` under a binder.

**Not a `@[simp]` lemma either, and for the same reason plus one more**: `simpNF` names
`ComplexAnalytic.AnalyticSpace.sigma_toLocallyRingedSpace` on the left-hand side's type and
`Set.range_sigmaMk`, which rewrites `Set.range (Sigma.mk j)` to `Sigma.fst ⁻¹' {j}`, on its
right-hand argument. -/
lemma sigmaHomeoSigma_preimage_range (j : ι) :
    sigmaHomeoSigma F ⁻¹' Set.range (Sigma.mk j) = Set.range (sigmaι F j).toLRSHom.base := by
  rw [← Homeomorph.image_symm, ← Set.range_comp]
  rfl

end AnalyticSpace

/-- **A morphism out of a coproduct is `ℂ`-linear as soon as its restrictions to the members
are**, with no agreement of the restrictions on the overlaps required.

`ComplexAnalytic.IsCLinearHom.of_openCover` at
`AlgebraicGeometry.LocallyRingedSpace.sigmaOpenCover`. The generality of that lemma is what makes
this possible: a descent map arrives from the universal property of the coproduct, not from
`AlgebraicGeometry.LocallyRingedSpace.OpenCover.glueMorphisms`, and so carries no
agreement-on-overlaps hypothesis to hand over.

The step is stated as a `have … := Sigma.ι_desc …` and used by `▸` rather than by `rw`: `i` is
bound at `(sigmaOpenCover _).J`, so the goal presents `(sigmaOpenCover _).map i ≫ Sigma.desc g`
and `rw [Sigma.ι_desc]` reports *"did not find an occurrence"*.

**Stated for a family of locally ringed spaces and not for the family of this file**, because
nothing in it is analytic: `ComplexAnalytic.IsCLinearHom` is a predicate on a morphism of locally
ringed spaces and the proof is `of_openCover` at the coproduct's own cover.
`ComplexAnalytic.AnalyticSpace.sigmaDesc` below is the instance at
`fun i ↦ (F i).toLocallyRingedSpace`. -/
theorem isCLinearHom_sigmaDesc {J : Type u} (f : J → LocallyRingedSpace.{u})
    {Y : LocallyRingedSpace.{u}} (g : ∀ i, f i ⟶ Y)
    {α : ℂ →+* (∐ f : LocallyRingedSpace.{u}).presheaf.obj (op ⊤)}
    {β : ℂ →+* Y.presheaf.obj (op ⊤)}
    (h : ∀ i, IsCLinearHom (g i) (comapAlgMap (Sigma.ι f i) α) β) :
    IsCLinearHom (Sigma.desc g) α β :=
  IsCLinearHom.of_openCover (sigmaOpenCover f) fun i ↦ by
    have e : (sigmaOpenCover f).map i ≫ Sigma.desc g = g i := Sigma.ι_desc g i
    exact e ▸ h i

namespace AnalyticSpace

/-- **The morphism out of a disjoint union determined by a morphism out of each member.**

The coproduct's descent map, with its `ℂ`-linearity supplied by
`ComplexAnalytic.isCLinearHom_sigmaDesc`. -/
def sigmaDesc {Y : AnalyticSpace.{u}} (g : ∀ i, F i ⟶ Y) : sigma F ⟶ Y where
  toLRSHom' := Sigma.desc fun i ↦ (g i).toLRSHom
  isCLinear := isCLinearHom_sigmaDesc (fun i ↦ (F i).toLocallyRingedSpace)
    (fun i ↦ (g i).toLRSHom) fun i ↦ by
    have e : comapAlgMap (Sigma.ι (fun i ↦ (F i).toLocallyRingedSpace) i)
        (sigma F).algebraMap = (F i).algebraMap := comapAlgMap_sigma F i
    exact e ▸ (g i).isCLinear

@[simp]
lemma sigmaι_sigmaDesc {Y : AnalyticSpace.{u}} (g : ∀ i, F i ⟶ Y) (j : ι) :
    sigmaι F j ≫ sigmaDesc F g = g j :=
  forgetToLocallyRingedSpace.map_injective (Sigma.ι_desc (fun i ↦ (g i).toLRSHom) j)

/-- **A morphism out of a disjoint union is determined by its restrictions to the members**, with
no agreement condition to check: the members are disjoint and there are no overlaps.

This is the uniqueness half of the universal property, of which
`ComplexAnalytic.AnalyticSpace.sigmaDesc` and
`ComplexAnalytic.AnalyticSpace.sigmaι_sigmaDesc` are the existence half. Together they are what a
consumer of a colimit would use, and
`ComplexAnalytic.AnalyticSpace.isColimitCofanSigma` below is the two of them bundled as
`CategoryTheory.Limits.IsColimit` — **this docstring used to say that bundle was not here**. That
declaration hands this theorem to one field of `CategoryTheory.Limits.Cofan.IsColimit.mk` and
proves nothing further, so what is written out below is still the whole of the uniqueness.

**The proof is the coproduct's own `hom_ext` and nothing else.** A morphism of analytic spaces is
determined by its morphism of locally ringed spaces
(`ComplexAnalytic.AnalyticSpace.forgetToLocallyRingedSpace` is faithful, which is what
`map_injective` is), and there `CategoryTheory.Limits.Sigma.hom_ext` applies to the coproduct that
`ComplexAnalytic.AnalyticSpace.sigma` is on the nose. Nothing analytic enters, and in particular
the `ℂ`-algebra structures are never compared — they cannot differ, the two morphisms having the
same source and target. -/
theorem hom_ext_sigma {Y : AnalyticSpace.{u}} {f g : sigma F ⟶ Y}
    (h : ∀ i, sigmaι F i ≫ f = sigmaι F i ≫ g) : f = g :=
  forgetToLocallyRingedSpace.map_injective <|
    Limits.Sigma.hom_ext _ _ fun i ↦ forgetToLocallyRingedSpace.congr_map (h i)

/-! ### The disjoint union is the coproduct -/

/-- **The inclusions of the members, read as a cofan on the disjoint union.**

A `CategoryTheory.Limits.Cofan` is a cocone over a family, and this is
`ComplexAnalytic.AnalyticSpace.sigma` with `ComplexAnalytic.AnalyticSpace.sigmaι` in the two
slots. There is no content: the declaration exists because
`ComplexAnalytic.AnalyticSpace.isColimitCofanSigma` has to name the cocone it is a colimit of, and
because that cocone is what `CategoryTheory.Limits.Cofan.inj` presents the inclusions as. -/
def cofanSigma : Limits.Cofan F := Limits.Cofan.mk (sigma F) (sigmaι F)

/-- **The disjoint union is the coproduct of its members**: the cofan of the inclusions is a
colimit.

**The mathematics is the two lemmas above and this adds none of it.**
`ComplexAnalytic.AnalyticSpace.sigmaDesc` supplies the descent map,
`ComplexAnalytic.AnalyticSpace.sigmaι_sigmaDesc` is the factorisation field and
`ComplexAnalytic.AnalyticSpace.hom_ext_sigma` is the uniqueness field, each handed to
`CategoryTheory.Limits.Cofan.IsColimit.mk` as it stands.

**The uniqueness field is a term and not a `rw`, and the reason is the seam this file already
records.** `## One seam, and it is not the one it looks like` says that
`(sigmaCover F).map j` and `Sigma.ι _ j` are equal by `rfl` and **not** reducibly; the same holds
of `(cofanSigma F).inj i` and `sigmaι F i`, and it is what makes `rw [h i]` report the target as
not type-correct under the `instances` transparency level. Composing the hypothesis with
`ComplexAnalytic.AnalyticSpace.sigmaι_sigmaDesc` by `Eq.trans` is the same step at default
transparency, where term elaboration performs the check the rewrite refuses. -/
def isColimitCofanSigma : Limits.IsColimit (cofanSigma F) :=
  Limits.Cofan.IsColimit.mk _ (fun t ↦ sigmaDesc F fun i ↦ t.inj i)
    (fun _ i ↦ sigmaι_sigmaDesc F _ i)
    (fun _ _ h ↦ hom_ext_sigma F fun i ↦ (h i).trans (sigmaι_sigmaDesc F _ i).symm)

/-- **`ComplexAnalytic.AnalyticSpace` has coproducts of families indexed by any type of its own
universe.**

`CategoryTheory.Limits.hasCoproducts_of_colimit_cofans` at
`ComplexAnalytic.AnalyticSpace.cofanSigma` and
`ComplexAnalytic.AnalyticSpace.isColimitCofanSigma`, which is a cofan and a colimit proof for
*every* family at once rather than for the one this section's `variable` names. It is stated at
`Type u` because that is the universe `ComplexAnalytic.AnalyticSpace.sigma` accepts an index type
from.

**Stating it for every index type is what makes it subsume
`CategoryTheory.Limits.HasCoproduct` at the family `F` this section's `variable` names**, so that
`∐ F` is writable with no second instance beside it — checked by elaborating `∐ F` rather than
argued from the shapes. -/
instance hasCoproducts : Limits.HasCoproducts.{u} AnalyticSpace.{u} :=
  Limits.hasCoproducts_of_colimit_cofans (fun f ↦ cofanSigma f) (fun f ↦ isColimitCofanSigma f)

/-- **And so it has finite coproducts**, which is the form a consumer that quantifies over `Fin n`
asks for.

`CategoryTheory.Limits.hasFiniteCoproducts_of_hasCoproducts` at
`ComplexAnalytic.AnalyticSpace.hasCoproducts`, and there is no mathematics in the step:
`CategoryTheory.Limits.HasFiniteCoproducts` quantifies over `Fin n`, which lives in `Type 0`,
and the converter crosses to the universe above by `CategoryTheory.Discrete.equivalence` at
`Equiv.ulift`.

**Its universe arguments are left to unification, and that is worth doing rather than writing them
out.** `CategoryTheory.Limits.hasFiniteCoproducts_of_hasCoproducts` takes them in the order
*coproduct index, morphisms, objects*, which for `ComplexAnalytic.AnalyticSpace.{u}` is
`u, u, u+1` — the object universe being one above the one the space's points live in, and the
`u` in `CategoryTheory.Limits.HasCoproducts.{u}` above being the first of the three and not the
last. -/
instance hasFiniteCoproducts : Limits.HasFiniteCoproducts AnalyticSpace.{u} :=
  Limits.hasFiniteCoproducts_of_hasCoproducts AnalyticSpace.{u}

/-! ### Non-vacuity, at the two ends -/

/-- **The disjoint union of the empty family is empty.**

The reading this closes is at the bottom end: a construction that returned some fixed space for
every family would satisfy everything above. Every point of a coproduct is in the image of some
member (`AlgebraicGeometry.LocallyRingedSpace.exists_sigma_ι_base_eq`) and there are no members,
so the carrier is empty. **Emptiness is a property of a space built some other way, and nothing in
the library is defined as the empty analytic space**: that is as true of the sibling below and of
`ComplexAnalytic.isEmpty_refineAnalytification` — the same statement for a refinement at an empty
index type — as it is of this one. `Oka/AnalyticSpace/LocalModel.lean` uses the phrase only to
say that the node is *not* it.

The sentence this replaces said that this was *the only declaration in the library that names the
empty analytic space*. That was exact at `0b19eb1`, which wrote it, and **`9ce75e2` falsified it
six days later** by adding `ComplexAnalytic.isEmpty_refineAnalytification` and sweeping nothing
here; `ComplexAnalytic.AnalyticSpace.surjective_base_or_isEmpty_of_isFiniteEtale` names the same
property of an arbitrary analytic space in its second branch. -/
theorem isEmpty_sigma [IsEmpty ι] : IsEmpty (sigma F) := by
  refine ⟨fun x ↦ ?_⟩
  obtain ⟨i, _, _⟩ := exists_sigma_ι_base_eq (fun i ↦ (F i).toLocallyRingedSpace) x
  exact IsEmpty.elim ‹IsEmpty ι› i

/-- **And so is the disjoint union of a family whose members are all empty**, which is the same
reading of the same lemma at the other quantifier.

`AlgebraicGeometry.LocallyRingedSpace.exists_sigma_ι_base_eq` again — every point of a coproduct
is in the image of some member — with the emptiness discharged at the point of the member rather
than at the index. It is the proof above with `y` in place of `i`.

**It implies the theorem above and does not replace it.** At an empty index type
`∀ i, IsEmpty (F i)` holds vacuously, so that statement follows from this one; what does not
follow is its *use*: instance search does not find the members' instance from `[IsEmpty ι]`, and
a caller would have to write the vacuous one out by hand. The hypothesis is
an instance rather than an explicit argument for the same reason the one above is: the callers
that want it have it that way, a trivial cover over an empty base being `fun _ ↦ X` at an empty
`X`. `AlgebraicGeometry.LocallyRingedSpace.hom_ext_of_isEmpty` takes the explicit form and its
docstring gives the reason, which is that the carrier of a `restrict` is not something instance
search finds; no `restrict` is involved here. -/
theorem isEmpty_sigma_of_members [∀ i, IsEmpty (F i : Type u)] : IsEmpty (sigma F) := by
  refine ⟨fun x ↦ ?_⟩
  obtain ⟨i, y, _⟩ := exists_sigma_ι_base_eq (fun i ↦ (F i).toLocallyRingedSpace) x
  exact IsEmpty.elim (‹∀ i, IsEmpty (F i : Type u)› i) y

/-- **With a second member that has a point, an inclusion is not surjective**, so the disjoint
union is not the member in disguise.

The reading this closes is at the top end, and it needs both hypotheses: at a one-member family
the inclusion *is* surjective — `ComplexAnalytic.AnalyticSpace.isIso_sigmaι` below says it is an
isomorphism there — and at a family whose other members are empty it is surjective again.
`AlgebraicGeometry.LocallyRingedSpace.eq_of_sigmaι_base_eq` is the whole proof — a point of the
`j`-th member cannot be in the image of the `i`-th.

Note what it is not: two analytic spaces with different carriers can still be isomorphic to a
third, and this says nothing about `ComplexAnalytic.AnalyticSpace.sigma F` being non-isomorphic to
`F i`. That is a statement about an invariant and nothing here computes one. -/
theorem not_surjective_sigmaι_base {i j : ι} (hij : i ≠ j) (y : (F j).toLocallyRingedSpace) :
    ¬ Function.Surjective (sigmaι F i).toLRSHom.base := by
  intro hs
  obtain ⟨x, hx⟩ := hs ((Sigma.ι (fun i ↦ (F i).toLocallyRingedSpace) j).base y)
  exact hij (eq_of_sigmaι_base_eq _ hx)

/-- **So under the same two hypotheses an inclusion is not an isomorphism.**

`ComplexAnalytic.AnalyticSpace.surjective_base_of_isIso` (`Oka/AnalyticSpace/Basic.lean`) against
the theorem above: an isomorphism is surjective on points and this inclusion is not. Both
hypotheses are still needed, for the reasons that theorem gives, and no import is added — that
lemma sits in a module this file already reaches.

**The caveat above is unchanged and this does not weaken it.** It says nothing about
`ComplexAnalytic.AnalyticSpace.sigma F` being non-isomorphic to `F i`: this refutes `IsIso` for
*this* morphism, and two spaces with different carriers can still be isomorphic by some other
one. The statement about an invariant is still the statement nothing here computes. -/
theorem not_isIso_sigmaι {i j : ι} (hij : i ≠ j) (y : (F j).toLocallyRingedSpace) :
    ¬ IsIso (sigmaι F i) := fun _ ↦
  not_surjective_sigmaι_base F hij y (surjective_base_of_isIso _)

/-- **At a one-member family the inclusion is an isomorphism**, which is the converse case
`ComplexAnalytic.AnalyticSpace.not_surjective_sigmaι_base` and
`ComplexAnalytic.AnalyticSpace.not_isIso_sigmaι` leave open, and the reason each of them asks for
a second index as well as for a point of a member.

`ComplexAnalytic.AnalyticSpace.not_isIso_sigmaι` needs a second index with an inhabited member;
this is what happens when there is no second index at all. `[Subsingleton ι]` and not `[Unique ι]`
is the honest hypothesis: `j` supplies the point that would make `ι` unique, and a caller who has
the index has it.

**The inverse is a descent map and there is no sheaf argument in it.** Each member is sent to
`F j` by the `eqToHom` of `Subsingleton.elim`, and the two round trips are
`ComplexAnalytic.AnalyticSpace.sigmaι_sigmaDesc` and
`ComplexAnalytic.AnalyticSpace.hom_ext_sigma`. So this is a corollary of the universal property
rather than a computation with the structure sheaves — worth saying because
`Oka/AnalyticSpace/SigmaFiniteEtale.lean` recorded the fold map's case as absent and priced it as
*"a statement about the structure sheaves as well"*, and that price is not what it costs. -/
instance isIso_sigmaι [Subsingleton ι] (j : ι) : IsIso (sigmaι F j) := by
  refine ⟨sigmaDesc F (fun i ↦ eqToHom (congrArg F (Subsingleton.elim i j))), ?_, ?_⟩
  · simp
  · refine hom_ext_sigma F fun i ↦ ?_
    have hij : i = j := Subsingleton.elim i j
    subst hij
    rw [← Category.assoc, sigmaι_sigmaDesc]
    simp

end AnalyticSpace

end

end ComplexAnalytic
