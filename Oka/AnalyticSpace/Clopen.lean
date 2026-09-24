/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.AnalyticSpace.OpenSubspace
import Oka.Geometry.RingedSpace.PresheafedSpace.Gluing

/-!
# Gluing a morphism along a clopen subspace and its complement

`ComplexAnalytic.AnalyticSpace.clopenCompl` makes the complement of an open subspace whose carrier
is closed into an open subspace again, so a clopen subset of an analytic space splits it into two
open subspaces which cover it and do not meet. This file says what that split buys: a morphism out
of the whole space is the same thing as a morphism out of each half, with no compatibility
condition to check.

## The gluing is `existsUnique_glueMorphisms_of_opens` and the work is choosing which spelling

`AlgebraicGeometry.LocallyRingedSpace.OpenCover.existsUnique_glueMorphisms` phrases the agreement
of two members on their overlap as an equation of morphisms out of the *categorical pullback* of
their inclusions, and its own docstring gives the reason that spelling is hard to use: to discharge
the hypothesis one has to know what the points of that pullback are, and the lemmas that would
discharge it are statements about spaces one can name.
`AlgebraicGeometry.LocallyRingedSpace.existsUnique_glueMorphisms_of_opens` is that statement for a
cover by opens, with the agreement phrased on `X.restrict (U i ⊓ U j)` — an open
subspace, and so a space the caller already understands. **That is the spelling this file uses,
and at a clopen pair its hypothesis is free at each pair of indices**:

* at a repeated index the two inclusions of the overlap into the member are `restrictLE` at two
  proofs of one inequality between opens, so proof irrelevance makes them the same term and the
  obligation is `rfl`;
* at the two distinct indices the overlap is `U ⊓ Uᶜ`, whose carrier is empty, and
  `AlgebraicGeometry.LocallyRingedSpace.hom_ext_restrict_of_isEmpty` says any two morphisms out of
  it agree. That lemma's docstring names a disjoint pair of members of an open cover as what it is
  for.

**So no analysis, no sheaf argument and no computation with sections happens below.** What does
happen is bookkeeping about universes and about `ℂ`-linearity, and both are worth naming because
neither is visible in the statements.

**The index type is `ULift.{u} Bool`.** `existsUnique_glueMorphisms_of_opens` asks for an index
type in the same universe as the spaces, and `Bool` lives in `Type 0` — instantiating the gluing
at a bare `Bool` cover instead reports an application type mismatch whose expected index type is
still a metavariable. The members are selected by `cond` rather than by an `if`, which keeps each
member of the pair definitionally equal to the open it names and so keeps the two factorisation
lemmas free of a transport; **an `if` keeps them too**, and
`ComplexAnalytic.AnalyticSpace.clopenCover`'s own docstring says so rather than leave the spelling
looking forced.

**`ℂ`-linearity is recovered afterwards and not carried through the gluing.** The glued morphism
arrives as a morphism of locally ringed spaces, `ComplexAnalytic.IsCLinearHom` being a condition on
a morphism of those rather than structure on a morphism of analytic spaces.
`ComplexAnalytic.IsCLinearHom` is a condition on **global sections only**, so it holds as soon as
it holds after restriction to each member of a cover, and
`AlgebraicGeometry.LocallyRingedSpace.section_ext_of_cover` is what turns that into a proof.
`ComplexAnalytic.AnalyticSpace.exists_hom_complexAffineSpace_of_local` glues a morphism to `ℂ^m`
the same way and for the same reason, and its treatment of linearity is the one copied here.

## Main definitions

- `ComplexAnalytic.AnalyticSpace.clopenCover`: **a clopen open and its complement, as a
  two-member cover** indexed by `ULift Bool`, in the shape
  `AlgebraicGeometry.LocallyRingedSpace.existsUnique_glueMorphisms_of_opens` consumes.
- `ComplexAnalytic.AnalyticSpace.clopenCoverHom`: a morphism out of each half of that pair, read
  as a family indexed by the cover.
- `ComplexAnalytic.AnalyticSpace.descClopen`: **the morphism glued from a morphism out of each
  half.** It is opaque, being chosen from the existence statement below; what a caller consumes is
  the pair of factorisations, in the way
  `ComplexAnalytic.AnalyticSpace.liftRestrict_fac` rather than
  `ComplexAnalytic.AnalyticSpace.liftRestrict` is what that construction's callers consume.

## Main results

- `ComplexAnalytic.AnalyticSpace.clopenCover_covers`: every point lies in one of the two halves.
- `ComplexAnalytic.AnalyticSpace.clopenCover_inf_of_ne`: and the two halves do not meet, which is
  the fact that makes the gluing's compatibility hypothesis vacuous.
- `ComplexAnalytic.AnalyticSpace.existsUnique_hom_of_clopen`: **a morphism out of a clopen half
  and a morphism out of the other glue to a unique morphism out of the whole space**, with no
  agreement between them asked for anywhere. This is the whole content of the file, and
  `ComplexAnalytic.AnalyticSpace.ofRestrict_descClopen`,
  `ComplexAnalytic.AnalyticSpace.ofRestrict_clopenCompl_descClopen` and
  `ComplexAnalytic.AnalyticSpace.hom_ext_of_clopen` are it, taken apart.
- `ComplexAnalytic.AnalyticSpace.ofRestrict_descClopen` and
  `ComplexAnalytic.AnalyticSpace.ofRestrict_clopenCompl_descClopen`: **the glued morphism restricts
  to the given one on each half**, which is the existence half.
- `ComplexAnalytic.AnalyticSpace.hom_ext_of_clopen`: **and two morphisms out of the space which
  agree on both halves are equal**, which is the uniqueness half stated as an extensionality
  lemma. It is derived from the uniqueness above by instantiating it at the restrictions of one of
  the two morphisms, so no second gluing is run for it.

## What is not here

* **No statement that the two halves exhibit the space as a coproduct.** That is what the results
  above amount to, and saying it needs a cocone and a `CategoryTheory.Limits.IsColimit`, which is
  done for covers in `Oka/AnalyticSpace/FiniteEtaleOver.lean` rather than for bare analytic spaces
  — the statement its `## What is not here` was asking for is about morphisms over a base, and
  nothing over a base is in scope in this file.
* **Nothing about a clopen subset that is not presented as an open with a closed carrier.** The
  input here is `(U : X.Opens)` together with `IsClosed (U : Set X)`, which is the shape
  `ComplexAnalytic.AnalyticSpace.clopenCompl` and
  `ComplexAnalytic.AnalyticSpace.isFiniteEtale_ofRestrict_of_isClosed` take. Turning an
  `IsClopen` on a bare `Set X` into that shape is a conversion, and it belongs beside whichever
  construction produces the set.
* **Nothing about more than two parts.** A partition into finitely many clopen pieces is the same
  argument at a larger index type. It is not written because the statement the direct-summand
  axiom of `Mathlib/CategoryTheory/Galois/Basic.lean` asks for is binary, and that axiom is what
  sent this file's results to `Oka/AnalyticSpace/FiniteEtaleOver.lean`.
-/

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry Topology

namespace ComplexAnalytic.AnalyticSpace

universe u

variable {X Y : AnalyticSpace.{u}}

/-- **A clopen open subset and its complement, as a two-member cover of the space.**

The index type is `ULift.{u} Bool` because
`AlgebraicGeometry.LocallyRingedSpace.existsUnique_glueMorphisms_of_opens` asks for an index type
in the universe of the spaces, and `Bool` is in `Type 0`.

`cond` rather than an `if`: this is then definitionally `U` at `ULift.up true` and
`ComplexAnalytic.AnalyticSpace.clopenCompl U hU` at `ULift.up false`, which is what keeps the two
factorisation lemmas free of a transport.

**Those two definitional equalities are not what picks `cond`, because an `if` has them as well.**
Planted and read back: `fun b ↦ if b.down then U else clopenCompl U hU` proves both of them by
`rfl`, with no `Decidable` instance written by hand and no error. So this is a choice of spelling
and not a necessity — what it avoids is the instance argument that `ite` carries and `cond` does
not, which is a term one does not have to look at rather than an elaboration that fails. -/
def clopenCover (U : X.Opens) (hU : IsClosed (U : Set X)) : ULift.{u} Bool → X.Opens :=
  fun b ↦ cond b.down U (clopenCompl U hU)

/-- **The two members cover the space**: a point is in the open or in its complement.

The hypothesis `AlgebraicGeometry.LocallyRingedSpace.existsUnique_glueMorphisms_of_opens` takes,
stated at the carrier of the underlying locally ringed space, which is the type that appears in
that theorem's binder. -/
theorem clopenCover_covers (U : X.Opens) (hU : IsClosed (U : Set X))
    (x : X.toLocallyRingedSpace) : ∃ i, x ∈ clopenCover U hU i := by
  by_cases h : x ∈ (U : Set X)
  · exact ⟨ULift.up true, h⟩
  · refine ⟨ULift.up false, ?_⟩
    change x ∈ ((clopenCompl U hU : X.Opens) : Set X)
    rw [coe_clopenCompl]
    exact h

/-- **And two distinct members do not meet.**

This is what makes the compatibility hypothesis of
`AlgebraicGeometry.LocallyRingedSpace.existsUnique_glueMorphisms_of_opens` free at the two distinct
pairs of indices, through
`AlgebraicGeometry.LocallyRingedSpace.hom_ext_restrict_of_isEmpty`.

Stated as an equation of carriers rather than as `Disjoint`, because the emptiness lemma it feeds
asks for `(V : Set X) = ∅` — and stated with the hypothesis `i ≠ j` rather than at the two indices
separately, because both diagonal cases of the gluing are discharged by proof irrelevance instead
and never reach this. -/
theorem clopenCover_inf_of_ne (U : X.Opens) (hU : IsClosed (U : Set X)) {i j : ULift.{u} Bool}
    (hij : i ≠ j) : ((clopenCover U hU i ⊓ clopenCover U hU j : X.Opens) : Set X) = ∅ := by
  obtain ⟨b⟩ := i
  obtain ⟨c⟩ := j
  cases b <;> cases c <;> simp_all [clopenCover, coe_clopenCompl]

/-- **A morphism out of each half, read as a family indexed by the cover.**

Written by cases on the index rather than by `Bool.rec` applied to the two morphisms, because the
two branches have different types — `X.restrict (clopenCover U hU i) ⟶ Y` at the two values of `i`
— and the motive is what the `cases` supplies. -/
noncomputable def clopenCoverHom (U : X.Opens) (hU : IsClosed (U : Set X))
    (f : X.restrict U ⟶ Y) (g : X.restrict (clopenCompl U hU) ⟶ Y) (i : ULift.{u} Bool) :
    X.restrict (clopenCover U hU i) ⟶ Y := by
  obtain ⟨b⟩ := i
  cases b
  · exact g
  · exact f

/-- **A morphism out of a clopen open subspace and a morphism out of its complement glue to a
unique morphism out of the whole space**, and nothing is asked of the two.

The gluing is `AlgebraicGeometry.LocallyRingedSpace.existsUnique_glueMorphisms_of_opens` at
`ComplexAnalytic.AnalyticSpace.clopenCover`, whose compatibility hypothesis is discharged in the
two ways the module docstring describes: `rfl` at a repeated index, by proof irrelevance on the two
inequalities between opens that `AlgebraicGeometry.LocallyRingedSpace.restrictLE` is applied to,
and `AlgebraicGeometry.LocallyRingedSpace.hom_ext_restrict_of_isEmpty` at a pair of distinct ones.

**The morphism that theorem produces is one of locally ringed spaces**, so it is promoted here by
supplying `ComplexAnalytic.IsCLinearHom` — established through
`AlgebraicGeometry.LocallyRingedSpace.section_ext_of_cover`, since linearity is a condition on
global sections and therefore holds as soon as it holds after restriction to each member. The step
that carries a pullback along the glued morphism to a pullback along the member's own morphism is
`AlgebraicGeometry.LocallyRingedSpace.Γ_map_comp_apply` at the factorisation, and it is used twice:
once for linearity, and once — as `congrArg` in the uniqueness field — to read an equation of
morphisms of analytic spaces as one of morphisms of locally ringed spaces. -/
theorem existsUnique_hom_of_clopen (U : X.Opens) (hU : IsClosed (U : Set X))
    (f : X.restrict U ⟶ Y) (g : X.restrict (clopenCompl U hU) ⟶ Y) :
    ∃! φ : X ⟶ Y, X.ofRestrict U ≫ φ = f ∧ X.ofRestrict (clopenCompl U hU) ≫ φ = g := by
  have hcover := clopenCover_covers U hU
  obtain ⟨φ₀, hφ₀, huniq⟩ := LocallyRingedSpace.existsUnique_glueMorphisms_of_opens
    (X := X.toLocallyRingedSpace) (Y := Y.toLocallyRingedSpace)
    (clopenCover U hU) hcover
    (fun i ↦ (clopenCoverHom U hU f g i).toLRSHom)
    (fun i j ↦ by
      by_cases hij : i = j
      · subst hij; rfl
      · exact LocallyRingedSpace.hom_ext_restrict_of_isEmpty (clopenCover_inf_of_ne U hU hij) _ _)
  have key : ∀ (i : ULift.{u} Bool) (a : Y.presheaf.obj (op ⊤)),
      (LocallyRingedSpace.Γ.map
          (X.toLocallyRingedSpace.ofRestrict (clopenCover U hU i).isOpenEmbedding).op).hom
            ((LocallyRingedSpace.Γ.map φ₀.op).hom a) =
        (LocallyRingedSpace.Γ.map (clopenCoverHom U hU f g i).toLRSHom.op).hom a := fun i a ↦
    (LocallyRingedSpace.Γ_map_comp_apply _ φ₀ a).symm.trans
      (congrArg (fun n : X.toLocallyRingedSpace.restrict (clopenCover U hU i).isOpenEmbedding ⟶
          Y.toLocallyRingedSpace ↦ (LocallyRingedSpace.Γ.map n.op).hom a) (hφ₀ i))
  have hclin : IsCLinearHom φ₀ X.algebraMap Y.algebraMap := fun c ↦
    LocallyRingedSpace.section_ext_of_cover X.toLocallyRingedSpace (clopenCover U hU) hcover _ _
      fun i ↦ (key i _).trans (((clopenCoverHom U hU f g i).isCLinear c).trans
        (isCLinearHom_ofRestrict X.toLocallyRingedSpace X.algebraMap (clopenCover U hU i) c).symm)
  refine ⟨⟨φ₀, hclin⟩, ⟨?_, ?_⟩, ?_⟩
  · exact forgetToLocallyRingedSpace.map_injective (hφ₀ (ULift.up true))
  · exact forgetToLocallyRingedSpace.map_injective (hφ₀ (ULift.up false))
  · rintro ψ ⟨hψ₁, hψ₂⟩
    refine forgetToLocallyRingedSpace.map_injective (huniq ψ.toLRSHom ?_)
    intro i
    obtain ⟨b⟩ := i
    cases b
    · exact congrArg (fun m ↦ forgetToLocallyRingedSpace.map m) hψ₂
    · exact congrArg (fun m ↦ forgetToLocallyRingedSpace.map m) hψ₁

/-- **The morphism glued from a morphism out of a clopen open subspace and one out of its
complement.**

Chosen from `ComplexAnalytic.AnalyticSpace.existsUnique_hom_of_clopen`, so it is opaque and its
two factorisations below are what a caller uses — the same arrangement, and for the same reason,
as `ComplexAnalytic.AnalyticSpace.liftRestrict` and
`ComplexAnalytic.AnalyticSpace.liftRestrict_fac`. -/
noncomputable def descClopen (U : X.Opens) (hU : IsClosed (U : Set X))
    (f : X.restrict U ⟶ Y) (g : X.restrict (clopenCompl U hU) ⟶ Y) : X ⟶ Y :=
  (existsUnique_hom_of_clopen U hU f g).choose

/-- **The glued morphism restricts to the given one on the clopen open subspace.** -/
theorem ofRestrict_descClopen (U : X.Opens) (hU : IsClosed (U : Set X))
    (f : X.restrict U ⟶ Y) (g : X.restrict (clopenCompl U hU) ⟶ Y) :
    X.ofRestrict U ≫ descClopen U hU f g = f :=
  (existsUnique_hom_of_clopen U hU f g).choose_spec.1.1

/-- **And to the given one on the complement.** -/
theorem ofRestrict_clopenCompl_descClopen (U : X.Opens) (hU : IsClosed (U : Set X))
    (f : X.restrict U ⟶ Y) (g : X.restrict (clopenCompl U hU) ⟶ Y) :
    X.ofRestrict (clopenCompl U hU) ≫ descClopen U hU f g = g :=
  (existsUnique_hom_of_clopen U hU f g).choose_spec.1.2

/-- **Two morphisms out of a space which agree on a clopen open subspace and on its complement are
equal.**

The uniqueness half of `ComplexAnalytic.AnalyticSpace.existsUnique_hom_of_clopen`, in the shape an
extensionality lemma is used in. It is obtained by instantiating that statement at the restrictions
of `φ`, which both morphisms then satisfy — so no second gluing is run and
`ComplexAnalytic.AnalyticSpace.descClopen` does not appear in the proof. -/
theorem hom_ext_of_clopen (U : X.Opens) (hU : IsClosed (U : Set X)) {φ ψ : X ⟶ Y}
    (h₁ : X.ofRestrict U ≫ φ = X.ofRestrict U ≫ ψ)
    (h₂ : X.ofRestrict (clopenCompl U hU) ≫ φ = X.ofRestrict (clopenCompl U hU) ≫ ψ) :
    φ = ψ := by
  obtain ⟨χ, -, huniq⟩ := existsUnique_hom_of_clopen U hU (X.ofRestrict U ≫ φ)
    (X.ofRestrict (clopenCompl U hU) ≫ φ)
  exact (huniq φ ⟨rfl, rfl⟩).trans (huniq ψ ⟨h₁.symm, h₂.symm⟩).symm

end ComplexAnalytic.AnalyticSpace
