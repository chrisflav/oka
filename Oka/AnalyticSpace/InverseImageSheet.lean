/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.AnalyticSpace.Basic
import Oka.Geometry.RingedSpace.LocallyRingedSpace.InverseImageSheet

/-!
# The sheet comparison is `ℂ`-linear

`AlgebraicGeometry.LocallyRingedSpace.sheetIso` identifies `(p⁻¹Y)|V` with `Y|(p '' V)` as
locally ringed spaces, for `V` an open on which `p` is an open embedding. If `Y` carries a
`ℂ`-algebra structure `β` on its global sections, both sides inherit one, and this file says the
identification respects them: `ComplexAnalytic.isCLinearHom_sheetHom`, and the same for the
inverse.

That matters because a morphism of locally ringed spaces between complex analytic spaces can be
antiholomorphic — complex conjugation is a ring automorphism of the sheaf of holomorphic
functions — so an isomorphism of locally ringed spaces is *not* on its own an identification of
analytic spaces. `ComplexAnalytic.IsCLinearHom` is the missing half, and every consumer of
`sheetIso` on the analytic side needs it.

## Why this is a separate file from the comparison itself

`Oka/Geometry/RingedSpace/LocallyRingedSpace/InverseImageSheet.lean` is mirror-tree material with
an upstream destination beside `Mathlib/Geometry/RingedSpace/LocallyRingedSpace.lean`;
`ComplexAnalytic.IsCLinearHom` is this project's own and has no Mathlib home, so the two have
different destinations and `README.md`'s *split by destination, not by subject* applies. The
statement here is the one thing about `sheetIso` that could not travel with it.

## There is nothing to choose, and that is the content

The `ℂ`-algebra structure on the sheet is `β` **pulled back along the map to `Y`** and the one on
`Y|(p '' V)` is `β` **restricted**, and those are the same operation:
`AlgebraicGeometry.LocallyRingedSpace.comapAlgMap_ofRestrict`, packaged as
`ComplexAnalytic.isCLinearHom_ofRestrict`. So both sides of the comparison are
`β` pulled back along their own map to `Y`, the comparison commutes with those two maps
(`AlgebraicGeometry.LocallyRingedSpace.liftRestrict_fac`), and `ℂ`-linearity is
`ComplexAnalytic.IsCLinearHom.of_comp`. **No section is computed and no hypothesis beyond the
sheet hypothesis is used**; in particular `Y` need not be an analytic space and `p` need not be a
local homeomorphism.

The structure on the sheet is stated in two spellings, because a consumer can arrive holding
either: pulled back along `AlgebraicGeometry.LocallyRingedSpace.sheetToBase` in one step, or the
structure on the whole of `p⁻¹Y` restricted to `V`.
`ComplexAnalytic.comapAlgMap_sheetToBase` says they agree.

## Main results

- `ComplexAnalytic.comapAlgMap_sheetToBase`: **the sheet's structure is the inverse image's,
  restricted** — the two spellings of the same structure.
- `ComplexAnalytic.isCLinearHom_sheetHom`: **the sheet comparison is `ℂ`-linear.**
- `ComplexAnalytic.isCLinearHom_sheetIso_inv`: and so is its inverse, so the identification is
  `ℂ`-linear in both directions.
- `ComplexAnalytic.comapAlgMap_sheetHom`: the same as an **equality of structures** rather than
  as two linearity statements — the form a consumer already holding a structure on `p⁻¹Y`
  recognises.

## What is not here

* **No analytic space, and this is still true of this file.** `Y` is an arbitrary locally ringed
  space with a `ℂ`-algebra structure on its global sections; nothing here asks it to have local
  models. The transport of `ComplexAnalytic.HasLocalModels` across `sheetIso` that a covering
  space of an analytic space needs is `Oka/AnalyticSpace/CoveringSpace.lean`, and it is
  `ComplexAnalytic.HasLocalModels.of_iso` along
  `AlgebraicGeometry.LocallyRingedSpace.sheetIso`. It consumes the `ℂ`-linearity proved below,
  exactly as this bullet predicted, but one step further off than that: `of_iso`'s own hypothesis
  there is discharged by the by-definition `ComplexAnalytic.isCLinearHom_comapAlgMap`, and
  `ComplexAnalytic.isCLinearHom_sheetHom` enters through
  `ComplexAnalytic.comapAlgMap_sheetHom`, which is proved from it.
* **Nothing about a cover — and the assembly does not need what this bullet used to say it
  would.** One sheet at a time, as in the file this builds on. What was written here was that
  assembling the sheets of a local homeomorphism into a structure on the whole of `p⁻¹Y` needs
  `AlgebraicGeometry.LocallyRingedSpace.glueAlgMap` and the agreement of the sheets on their
  overlaps. **It needs neither**, and `Oka/AnalyticSpace/CoveringSpace.lean` is the measurement:
  `AlgebraicGeometry.LocallyRingedSpace.inverseImageHom` is defined on the whole of `p⁻¹Y`, so the
  structure pulled back along it is already global and the sheets are used for the *property* of
  having local models and for nothing else. `ComplexAnalytic.comapAlgMap_sheetHom` below is what
  makes that work: it says the sheet's structure is the global one restricted, so no two sheets are
  ever compared and the overlap identity this bullet reached for is never formed.
-/

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry TopCat Topology

universe u

namespace ComplexAnalytic

noncomputable section

variable (Y : LocallyRingedSpace.{u}) {E : TopCat.{u}} (p : E ⟶ Y.toTopCat) (V : Opens E)
  (hV : IsOpenEmbedding fun x : V ↦ p x) (β : ℂ →+* Y.presheaf.obj (op ⊤))

/-- **The `ℂ`-algebra structure a sheet inherits is the one `p⁻¹Y` inherits, restricted.**

The left-hand side is `β` pulled back in one step along
`AlgebraicGeometry.LocallyRingedSpace.sheetToBase`; the right-hand side is `β` pulled back to the
whole of `p⁻¹Y` and then restricted to `V`. They agree because `sheetToBase` is by definition the
composite of the two morphisms, and pulling back along a composite is pulling back twice
(`AlgebraicGeometry.LocallyRingedSpace.comapAlgMap_comp`,
`AlgebraicGeometry.LocallyRingedSpace.comapAlgMap_ofRestrict`).

Both spellings occur: the first is what the proofs below want, and the second is what a consumer
holding a structure on `p⁻¹Y` has. -/
theorem comapAlgMap_sheetToBase :
    LocallyRingedSpace.comapAlgMap (LocallyRingedSpace.sheetToBase Y p V) β =
      (Y.inverseImage p).resAlgMap
        (LocallyRingedSpace.comapAlgMap (Y.inverseImageHom p) β) V := by
  rw [LocallyRingedSpace.sheetToBase, LocallyRingedSpace.comapAlgMap_comp]
  exact LocallyRingedSpace.comapAlgMap_ofRestrict _ _ _

include hV in
/-- **The sheet comparison `(p⁻¹Y)|V ⟶ Y|(p '' V)` is `ℂ`-linear.**

Both structures are `β` pulled back along the respective map to `Y`, and the comparison commutes
with those maps by `AlgebraicGeometry.LocallyRingedSpace.liftRestrict_fac`, so this is
`ComplexAnalytic.IsCLinearHom.of_comp` and there is no computation in it. The hypothesis `hV` is
used only to have a comparison at all. -/
theorem isCLinearHom_sheetHom :
    IsCLinearHom (LocallyRingedSpace.sheetHom Y p V hV)
      (LocallyRingedSpace.comapAlgMap (LocallyRingedSpace.sheetToBase Y p V) β)
      (Y.resAlgMap β (LocallyRingedSpace.sheetImage Y p V hV)) :=
  IsCLinearHom.of_comp (LocallyRingedSpace.liftRestrict_fac _ _ _)
    (isCLinearHom_comapAlgMap _ β) (isCLinearHom_ofRestrict Y β _)

include hV in
/-- **The sheet comparison is `ℂ`-linear in the other direction too.**

`AlgebraicGeometry.LocallyRingedSpace.sheetIso`'s inverse composed with
`AlgebraicGeometry.LocallyRingedSpace.sheetToBase` is the inclusion of `p '' V`, so the same
`ComplexAnalytic.IsCLinearHom.of_comp` applies with the two structures exchanged. Together with
`ComplexAnalytic.isCLinearHom_sheetHom` this makes `sheetIso` an identification of the two
`ℂ`-algebra structures and not merely of the two spaces. -/
theorem isCLinearHom_sheetIso_inv :
    IsCLinearHom (LocallyRingedSpace.sheetIso Y p V hV).inv
      (Y.resAlgMap β (LocallyRingedSpace.sheetImage Y p V hV))
      (LocallyRingedSpace.comapAlgMap (LocallyRingedSpace.sheetToBase Y p V) β) := by
  refine IsCLinearHom.of_comp (q := LocallyRingedSpace.sheetToBase Y p V)
    (p := Y.ofRestrict (LocallyRingedSpace.sheetImage Y p V hV).isOpenEmbedding) ?_
    (isCLinearHom_ofRestrict Y β _) (isCLinearHom_comapAlgMap _ β)
  have h : (LocallyRingedSpace.sheetIso Y p V hV).inv ≫ LocallyRingedSpace.sheetHom Y p V hV =
      𝟙 _ := by
    have hid := (LocallyRingedSpace.sheetIso Y p V hV).inv_hom_id
    rwa [LocallyRingedSpace.sheetIso_hom] at hid
  have hfac : LocallyRingedSpace.sheetHom Y p V hV ≫
      Y.ofRestrict (LocallyRingedSpace.sheetImage Y p V hV).isOpenEmbedding =
      LocallyRingedSpace.sheetToBase Y p V :=
    LocallyRingedSpace.liftRestrict_fac _ _ _
  rw [← hfac, ← Category.assoc, h, Category.id_comp]

/-- **The structure `p⁻¹Y` inherits restricts, over a sheet, to the structure on `p '' V`
transported across the comparison.**

This is `ComplexAnalytic.isCLinearHom_sheetHom` and
`ComplexAnalytic.isCLinearHom_sheetIso_inv` in the form that says the transport is an equality of
structures rather than a pair of inequalities — `ComplexAnalytic.IsCLinearHom.eq` applied to the
two witnesses of `ℂ`-linearity over `β` on the source. It is the form in which a consumer that
already has a structure on `p⁻¹Y` recognises it.

**The `▸` is the only one in this file and it moves no data.** It substitutes along
`ComplexAnalytic.comapAlgMap_sheetToBase`, an equality of ring homomorphisms, inside a goal which
is itself an equality of ring homomorphisms — a `Prop`. There is no `CategoryTheory.eqToHom` and
no `cast` here or anywhere below. -/
theorem comapAlgMap_sheetHom :
    LocallyRingedSpace.comapAlgMap (LocallyRingedSpace.sheetHom Y p V hV)
        (Y.resAlgMap β (LocallyRingedSpace.sheetImage Y p V hV)) =
      (Y.inverseImage p).resAlgMap
        (LocallyRingedSpace.comapAlgMap (Y.inverseImageHom p) β) V :=
  (comapAlgMap_sheetToBase Y p V β) ▸
    (isCLinearHom_comapAlgMap (LocallyRingedSpace.sheetHom Y p V hV) _).eq
      (isCLinearHom_sheetHom Y p V hV β)

end

end ComplexAnalytic
