/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.AlgebraicGeometry.Chow
import Oka.Analytification.GAGA.ProjectiveGAGA

/-!
# Chow's lemma over `ℂ`

For an integral scheme `Y` proper over `ℂ` there are a projective scheme `Y'` over `ℂ`, a closed
immersion `j : Y' ⟶ ℙᴺ` and a morphism `π : Y' ⟶ Y` over `ℂ` such that
`(π, j) : Y' ⟶ Y ×_ℂ ℙᴺ` is a closed immersion and `π` is an isomorphism over a nonempty open
`U ⊆ Y` (`ComplexAnalytic.exists_chow`). The scheme `Y'` is integral.

Over an open `V ⊆ Y`, `π⁻¹ V` is the preimage of `V ×_ℂ ℙᴺ` under the closed immersion `(π, j)`;
for `V = Spec A` this identifies `π⁻¹ V` with a closed subscheme of `ℙᴺ_A`.
-/

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace ComplexAnalytic

/-- **Chow's lemma over `ℂ`.** For an integral scheme `Y` proper over `ℂ` there are `N`, a scheme
`Y'` over `ℂ`, a closed immersion `j : Y' ⟶ ℙᴺ` and a morphism `π : Y' ⟶ Y` over `ℂ`, such that
`(π, j) : Y' ⟶ Y ×_ℂ ℙᴺ` is a closed immersion, `π` restricts to an isomorphism `π⁻¹ U ≅ U` for
some nonempty open `U ⊆ Y`, and `Y'` is integral. -/
theorem exists_chow (Y : SchemeLFTℂ.{u}) [IsIntegral Y.obj.left] [IsProper Y.obj.hom] :
    ∃ (N : ℕ) (Y' : SchemeLFTℂ.{u}) (j : Y' ⟶ projectiveSpace.{u} N) (π : Y' ⟶ Y)
      (U : Y.obj.left.Opens),
      IsClosedImmersion j.hom.left ∧
      IsClosedImmersion (pullback.lift π.hom.left j.hom.left
        ((Over.w π.hom).trans (Over.w j.hom).symm) :
          Y'.obj.left ⟶ pullback Y.obj.hom (projectiveSpace.{u} N).obj.hom) ∧
      (U : Set Y.obj.left).Nonempty ∧ IsIso (π.hom.left ∣_ U) ∧ IsIntegral Y'.obj.left := by
  obtain ⟨N, Z, c, U, hc, hq, hU, hπ, hZ⟩ := AlgebraicGeometry.exists_chow Y.obj.hom
  have : LocallyOfFiniteType (c ≫ pullback.fst _ _ ≫ Y.obj.hom) := by
    have : LocallyOfFiniteType Y.obj.hom := Y.property
    infer_instance
  let Y' : SchemeLFTℂ.{u} := ⟨Over.mk (c ≫ pullback.fst _ _ ≫ Y.obj.hom), this⟩
  let π : Y' ⟶ Y := ObjectProperty.homMk (Over.homMk (c ≫ pullback.fst _ _) (Category.assoc _ _ _))
  let j : Y' ⟶ projectiveSpace.{u} N := ObjectProperty.homMk (Over.homMk (c ≫ pullback.snd _ _)
    (by
      change (c ≫ pullback.snd _ _) ≫ ProjectiveSpace.toSpec N _ = c ≫ pullback.fst _ _ ≫ _
      rw [Category.assoc, ← pullback.condition]))
  have hlift : pullback.lift π.hom.left j.hom.left ((Over.w π.hom).trans (Over.w j.hom).symm) =
      c := by
    apply pullback.hom_ext
    · exact pullback.lift_fst _ _ _
    · exact pullback.lift_snd _ _ _
  refine ⟨N, Y', j, π, U, hq, ?_, hU, hπ, hZ⟩
  rw [hlift]
  exact hc

/-- The scheme `Y'` in Chow's lemma is projective. -/
theorem exists_chow_isProjectiveℂ (Y : SchemeLFTℂ.{u}) [IsIntegral Y.obj.left]
    [IsProper Y.obj.hom] :
    ∃ (Y' : SchemeLFTℂ.{u}) (π : Y' ⟶ Y) (U : Y.obj.left.Opens), IsProjectiveℂ Y' ∧
      (U : Set Y.obj.left).Nonempty ∧ IsIso (π.hom.left ∣_ U) ∧ IsIntegral Y'.obj.left := by
  obtain ⟨N, Y', j, π, U, hj, -, hU, hπ, hY'⟩ := exists_chow Y
  exact ⟨Y', π, U, ⟨N, j, hj⟩, hU, hπ, hY'⟩

end ComplexAnalytic
