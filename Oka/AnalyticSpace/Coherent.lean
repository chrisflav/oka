/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Algebra.Category.ModuleCat.Sheaf.Coherent.Locality
import Oka.AnalyticSpace.Basic
import Oka.Coherent

/-!
# Coherence of the structure sheaf of a complex analytic space

We deduce from `isCoherent_unit_okaSheaf` (Oka's coherence theorem for `ℂ^ι`) that the
structure sheaf of an arbitrary complex analytic space is coherent.

## Strategy

Coherence of `𝒪_X` is a local property of `X`, and being a local model is invariant under
isomorphism of locally ringed spaces (`ComplexAnalytic.IsLocalModel.of_iso`), so by definition
of an analytic space it suffices to treat a local model `i : M ⟶ Y`, where `Y` is an open
subset of some `ℂ^n` and `M` is cut out by finitely many holomorphic functions `f₁, …, f_k`
on `Y`. There:

- `𝒪_Y` is coherent, being the restriction of `𝒪_{ℂ^n}` to an open subset;
- the ideal sheaf `I = (f₁, …, f_k) ⊆ 𝒪_Y` is of finite type, hence coherent as a finite type
  subsheaf of a coherent sheaf (`SheafOfModules.IsCoherent.of_mono`);
- therefore `i_*𝒪_M ≅ 𝒪_Y/I` is coherent as a sheaf of `𝒪_Y`-modules, being the quotient of a
  coherent sheaf by a coherent subsheaf;
- coherence over `𝒪_Y` implies coherence over the quotient ring sheaf `𝒪_Y/I`, since for a
  surjection of sheaves of rings the submodules of a module over the quotient are the same
  computed over either ring;
- finally `𝒪_M` is the inverse image of `𝒪_Y/I` along the closed embedding `i`, and inverse
  image along an embedding preserves coherence, being exact and compatible with stalks.

## Main definitions

- `AlgebraicGeometry.LocallyRingedSpace.ringSheaf`: the structure sheaf of a locally ringed
  space, viewed as a sheaf of (not necessarily commutative) rings, so that the machinery of
  `SheafOfModules` applies.
- `AlgebraicGeometry.LocallyRingedSpace.IsCoherentStructureSheaf`: `𝒪_X` is coherent as a
  sheaf of modules over itself.

## Main results

- `isCoherentStructureSheaf_complexSpace`: Oka's coherence theorem, restated for
  `complexSpace ι` as a locally ringed space.
- `ComplexAnalytic.AnalyticSpace.isCoherentStructureSheaf`: the structure sheaf of any complex
  analytic space is coherent.

## Remaining work

The reduction above is complete; two ingredients are still open, and everything else in this
file is proved from them.

- `isCoherent_over_iff_restrict`: transport of coherence along the equivalence of sites
  `Over U ≌ Opens ↥U`. Mathlib provides the equivalence and the induced equivalence of sheaf
  categories, but not a transport of `SheafOfModules.IsCoherent`; since coherence quantifies
  over all objects and their slices, such a transport has to be established simultaneously for
  a site and all of its slice sites.
- `IsCutOutBy.isCoherentStructureSheaf`: the geometric step. Besides the closed immersion
  transfer, this needs coherence of the cokernel of a morphism of coherent sheaves, which is
  not yet available in `Oka.Algebra.Category.ModuleCat.Sheaf.Coherent.Stability` (only
  `isFiniteType_cokernel` is).

## References

- [Hans Grauert and Reinhold Remmert, *Coherent analytic sheaves*][grauert-remmert1984], §A
- [Jean-Pierre Serre, *Faisceaux algébriques cohérents*][serre1955], §2
-/

open CategoryTheory TopologicalSpace Opposite Limits SheafOfModules

universe u

namespace AlgebraicGeometry

namespace LocallyRingedSpace

variable (X : LocallyRingedSpace.{u})

/-- The structure sheaf of a locally ringed space, viewed as a sheaf of rings rather than of
commutative rings. This is the form in which the theory of `SheafOfModules` and coherence
applies. -/
noncomputable def ringSheaf : Sheaf (Opens.grothendieckTopology X) RingCat.{u} :=
  ⟨X.presheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u},
    (TopCat.Presheaf.isSheaf_iff_isSheaf_comp
      (forget₂ CommRingCat.{u} RingCat.{u}) X.presheaf).1 X.IsSheaf⟩

/-- A locally ringed space has **coherent structure sheaf** if `𝒪_X` is coherent as a sheaf of
modules over itself. -/
def IsCoherentStructureSheaf : Prop :=
  (SheafOfModules.unit X.ringSheaf).IsCoherent

end LocallyRingedSpace

end AlgebraicGeometry

open AlgebraicGeometry

/-- The structure sheaf of `ℂ^ι` as a locally ringed space is the sheaf of rings `okaSheaf ι`. -/
lemma complexSpace_ringSheaf (ι : Type u) [Fintype ι] :
    (complexSpace ι).ringSheaf = okaSheaf ι :=
  rfl

/-- **Oka's coherence theorem**, for `ℂ^ι` as a locally ringed space: the structure sheaf of
`ℂ^ι` is coherent over itself. -/
theorem isCoherentStructureSheaf_complexSpace (ι : Type u) [Fintype ι] :
    (complexSpace ι).IsCoherentStructureSheaf := by
  show (SheafOfModules.unit (complexSpace ι).ringSheaf).IsCoherent
  rw [complexSpace_ringSheaf]
  exact isCoherent_unit_okaSheaf ι

/-- Complex affine `n`-space has coherent structure sheaf. -/
theorem isCoherentStructureSheaf_complexAffineSpace (n : ℕ) :
    (complexAffineSpace.{u} n).IsCoherentStructureSheaf :=
  isCoherentStructureSheaf_complexSpace _

namespace AlgebraicGeometry.LocallyRingedSpace

/-- A family of open subsets covering a topological space covers the terminal object of its
site of opens. -/
lemma coversTop_opens {T : Type u} [TopologicalSpace T] {A : Type u} (V : A → Opens T)
    (hcov : ∀ x : T, ∃ a, x ∈ V a) :
    (Opens.grothendieckTopology T).CoversTop V := by
  intro Z x hx
  obtain ⟨a, ha⟩ := hcov x
  exact ⟨Z ⊓ V a, homOfLE inf_le_left, ⟨a, ⟨homOfLE inf_le_right⟩⟩, ⟨hx, ha⟩⟩

/-- Restricting `𝒪_X` to the slice site `Over U` is the same thing as passing to the structure
sheaf of the open subspace `X|_U`.

Under `TopologicalSpace.Opens.overEquivalence : Over U ≌ Opens ↥U` the site `(Opens X).over U`
is equivalent to the site of opens of `U`, and by
`TopologicalSpace.Opens.overPullbackSheafEquivOver` this equivalence carries the restriction of
`𝒪_X` to `Over U` to the structure sheaf of `X.restrict U`. Coherence is invariant under such a
transport of site and ring sheaf. -/
theorem isCoherent_over_iff_restrict (X : LocallyRingedSpace.{u}) (U : Opens X) :
    SheafOfModules.IsCoherent (R := X.ringSheaf.over U)
        ((SheafOfModules.unit X.ringSheaf).over U) ↔
      (X.restrict U.isOpenEmbedding).IsCoherentStructureSheaf :=
  sorry

/-- Coherence of the structure sheaf passes to open subspaces. -/
theorem IsCoherentStructureSheaf.restrict {X : LocallyRingedSpace.{u}}
    (hX : X.IsCoherentStructureSheaf) (U : Opens X) :
    (X.restrict U.isOpenEmbedding).IsCoherentStructureSheaf := by
  haveI : (SheafOfModules.unit X.ringSheaf).IsCoherent := hX
  exact (isCoherent_over_iff_restrict X U).1 (SheafOfModules.IsCoherent.over _ U)

/-- Coherence of the structure sheaf is a local property: it may be checked on any open cover. -/
theorem isCoherentStructureSheaf_of_openCover (X : LocallyRingedSpace.{u}) {I : Type u}
    (U : I → Opens X) (hU : ∀ x : X, ∃ i, x ∈ U i)
    (h : ∀ i, (X.restrict (U i).isOpenEmbedding).IsCoherentStructureSheaf) :
    X.IsCoherentStructureSheaf := by
  haveI (i : I) : SheafOfModules.IsCoherent (R := X.ringSheaf.over (U i))
      ((SheafOfModules.unit X.ringSheaf).over (U i)) :=
    (isCoherent_over_iff_restrict X (U i)).2 (h i)
  exact SheafOfModules.IsCoherent.of_coversTop (R := X.ringSheaf)
    (SheafOfModules.unit X.ringSheaf) U (coversTop_opens U hU)

end AlgebraicGeometry.LocallyRingedSpace

namespace ComplexAnalytic

/-- If `i : X ⟶ Y` cuts out `X` inside `Y` by finitely many global sections and `𝒪_Y` is
coherent, then so is `𝒪_X`.

This is the geometric heart of the deduction. Writing `I ⊆ 𝒪_Y` for the ideal sheaf generated
by the `fⱼ`, the argument is:

1. `I` is of finite type by construction, hence coherent as a finite type subsheaf of the
   coherent sheaf `𝒪_Y` (`SheafOfModules.IsCoherent.of_mono`).
2. The quotient `𝒪_Y/I` is coherent over `𝒪_Y`, being the cokernel of a morphism of coherent
   sheaves.
3. `𝒪_Y/I` is then coherent as a sheaf of modules over itself: for a surjection of sheaves of
   rings `𝒪_Y ↠ 𝒪_Y/I`, a sheaf of `𝒪_Y/I`-modules has the same subsheaves of modules
   computed over `𝒪_Y` as over `𝒪_Y/I`, and finite generation is likewise unchanged.
4. `IsCutOutBy` says exactly that `i` identifies `𝒪_X` with the inverse image of `𝒪_Y/I` along
   the closed embedding `i.base`; inverse image along an embedding is exact and computes
   stalks, so it preserves coherence. -/
theorem IsCutOutBy.isCoherentStructureSheaf {X Y : LocallyRingedSpace.{u}} {i : X ⟶ Y} {k : ℕ}
    {f : Fin k → Y.presheaf.obj (op ⊤)} (hf : IsCutOutBy i f)
    (hY : Y.IsCoherentStructureSheaf) : X.IsCoherentStructureSheaf :=
  sorry

/-- The structure sheaf of a local model is coherent. -/
theorem IsLocalModel.isCoherentStructureSheaf {M : LocallyRingedSpace.{u}} (hM : IsLocalModel M) :
    M.IsCoherentStructureSheaf := by
  obtain ⟨n, k, U, i, f, hcut⟩ := hM
  exact hcut.isCoherentStructureSheaf
    ((isCoherentStructureSheaf_complexAffineSpace.{u} n).restrict U)

/-- **Coherence of the structure sheaf of a complex analytic space.**

Every point of an analytic space has a neighbourhood isomorphic to a local model, whose
structure sheaf is coherent by `IsLocalModel.isCoherentStructureSheaf`; since coherence is a
local property, `𝒪_X` is coherent. -/
theorem AnalyticSpace.isCoherentStructureSheaf (X : AnalyticSpace.{u}) :
    X.toLocallyRingedSpace.IsCoherentStructureSheaf := by
  choose U M hM he using X.local_model
  refine LocallyRingedSpace.isCoherentStructureSheaf_of_openCover _
    (fun x : X.toLocallyRingedSpace ↦ (U x).1) (fun x ↦ ⟨x, (U x).2⟩) fun x ↦ ?_
  exact (IsLocalModel.of_iso (he x).some (hM x)).isCoherentStructureSheaf

end ComplexAnalytic
