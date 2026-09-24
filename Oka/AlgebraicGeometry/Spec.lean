/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Mathlib.AlgebraicGeometry.Spec

/-!
# A global section of `𝒪_{Spec R}` vanishes at a prime exactly when it lies in it

Material for `Mathlib/AlgebraicGeometry/Spec.lean`; see `README.md` on the mirror tree.
Upstreaming it adds nothing: that file's transitive closure is **2029** Mathlib modules, the
import above is the target itself, and the cost is **0**, measured with
`python3 scripts/import_cost.py Oka/AlgebraicGeometry/Spec.lean`.

**This file was `Oka/AlgebraicGeometry/StructureSheaf.lean` until taxis #935**, proposing
`Mathlib/AlgebraicGeometry/StructureSheaf.lean` at **19** on a closure of 2010 — the price of
`Mathlib.AlgebraicGeometry.Spec`. Both statements below name `Spec.locallyRingedSpaceObj`: the
second in its statement, and the first in the `haveI` that supplies the stalk's `IsLocalRing`
instance, which is stated at that spelling and nowhere else. The target imports the structure
sheaf and not the other way round, so the old path had to buy the import to state either
theorem, and the new one is free. **The namespace does not move with the file**: both stay
`AlgebraicGeometry.StructureSheaf`, which is what their subject is, and `README.md`'s rule is
about destinations rather than about names.

Mathlib proves the other direction — the germ of `a` at `x` is a unit when `x ∈ basicOpen a` —
as `isUnit_toStalk` in `Mathlib/AlgebraicGeometry/StructureSheaf.lean`, and **that declaration is
not `public` under the module system, so it is not merely unstated here but uncitable**. The
direction below is the one every consumer wants anyway, because it is the hypothesis of the
criteria that say a quotient sheaf is *not* zero.

Both are one step from the stalk being the localisation at the prime
(`AlgebraicGeometry.StructureSheaf.IsLocalization.to_stalk`), and the step is
`IsLocalization.AtPrime.to_map_mem_maximal_iff`.

## Main results

- `AlgebraicGeometry.StructureSheaf.germ_algebraMap_mem_maximalIdeal_iff`: **the germ at `p` of
  the global section attached to `a` lies in the maximal ideal of the stalk exactly when `a ∈ p`.**
- `AlgebraicGeometry.StructureSheaf.germ_algebraMap_mem_maximalIdeal_iff'`: the same at the
  `Spec.locallyRingedSpaceObj` spelling, which is the one a consumer holding a locally ringed
  space is in. The two statements are definitionally the same and neither `rw` nor instance
  search crosses between them; the second exists so that no caller has to.
-/

open CategoryTheory Opposite TopologicalSpace

universe u

noncomputable section

namespace AlgebraicGeometry.StructureSheaf

/-- **The germ at `p` of the global section of `𝒪_{Spec R}` attached to `a : R` lies in the
maximal ideal of the stalk exactly when `a` lies in `p`.**

The stalk is the localisation of `R` at `p`
(`AlgebraicGeometry.StructureSheaf.IsLocalization.to_stalk`) and the germ of the global section
is the image of `a` under the localisation map
(`AlgebraicGeometry.StructureSheaf.algebraMap_germ_apply`), so this is
`IsLocalization.AtPrime.to_map_mem_maximal_iff`.

The `IsLocalRing` instance on the stalk is stated in the `Spec.locallyRingedSpaceObj` spelling,
which instance search does not cross to `Spec.structureSheaf`; it is introduced by
`inferInstanceAs` inside the statement rather than by an instance declaration, so that no new
global instance is created for a seam. -/
theorem germ_algebraMap_mem_maximalIdeal_iff (R : Type u) [CommRing R] (a : R)
    (p : PrimeSpectrum R) :
    haveI : IsLocalRing ((Spec.structureSheaf R).presheaf.stalk p) :=
      inferInstanceAs (IsLocalRing
        ((Spec.locallyRingedSpaceObj (CommRingCat.of R)).presheaf.stalk p))
    ((Spec.structureSheaf R).presheaf.germ ⊤ p trivial).hom (algebraMap R _ a) ∈
      IsLocalRing.maximalIdeal ((Spec.structureSheaf R).presheaf.stalk p) ↔ a ∈ p.asIdeal := by
  have e : ((Spec.structureSheaf R).presheaf.germ ⊤ p trivial).hom (algebraMap R _ a) =
      algebraMap R ((Spec.structureSheaf R).presheaf.stalk p) a :=
    StructureSheaf.algebraMap_germ_apply (R := R) ⊤ p trivial a
  rw [e]
  exact IsLocalization.AtPrime.to_map_mem_maximal_iff _ p.asIdeal a

/-- **The germ criterion at the `Spec.locallyRingedSpaceObj` spelling.**

`AlgebraicGeometry.StructureSheaf.germ_algebraMap_mem_maximalIdeal_iff` says the same thing about
`Spec.structureSheaf`. The two are definitionally equal and the proof below is `exact`, which
crosses at default transparency; **instance search does not cross, which is why the first
statement has to carry its `IsLocalRing` instance by hand and this one does not**, and `rw` does
not cross either, which is why a consumer holding a locally ringed space needs this spelling
rather than the first.

The section itself is written in the `Spec.structureSheaf` spelling because the `Algebra R`
instance is stated there and nowhere else; that ascription is the one place a caller meets the
seam. -/
theorem germ_algebraMap_mem_maximalIdeal_iff' (R : Type u) [CommRing R] (a : R)
    (p : PrimeSpectrum R) :
    ((Spec.locallyRingedSpaceObj (CommRingCat.of R)).presheaf.germ ⊤ p trivial).hom
        (algebraMap R ((Spec.structureSheaf R).presheaf.obj (op ⊤)) a) ∈
      IsLocalRing.maximalIdeal
        ((Spec.locallyRingedSpaceObj (CommRingCat.of R)).presheaf.stalk p) ↔
      a ∈ p.asIdeal :=
  germ_algebraMap_mem_maximalIdeal_iff R a p

end AlgebraicGeometry.StructureSheaf
