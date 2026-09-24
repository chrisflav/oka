/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.AlgebraicGeometry.ChowIrreducible
import Oka.Analytification.GAGA.Proper.Chow

/-!
# Chow's lemma over `ℂ` for irreducible schemes

For an irreducible scheme `Y` proper over `ℂ` there are a projective scheme `Y'` over `ℂ`, a
closed immersion `j : Y' ⟶ ℙᴺ` and a morphism `π : Y' ⟶ Y` over `ℂ` such that
`(π, j) : Y' ⟶ Y ×_ℂ ℙᴺ` is a closed immersion and `π` is an isomorphism over a nonempty open
`U ⊆ Y` (`ComplexAnalytic.exists_chow_of_irreducibleSpace`). The scheme `Y'` is irreducible and
`π⁻¹ U` is scheme-theoretically dense in `Y'`.
-/

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace ComplexAnalytic

/-- **Chow's lemma over `ℂ`, irreducible case.** For an irreducible scheme `Y` proper over `ℂ`
there are `N`, a scheme `Y'` over `ℂ`, a closed immersion `j : Y' ⟶ ℙᴺ` and a morphism
`π : Y' ⟶ Y` over `ℂ`, such that `(π, j) : Y' ⟶ Y ×_ℂ ℙᴺ` is a closed immersion, `π` restricts to
an isomorphism `π⁻¹ U ≅ U` for some nonempty open `U ⊆ Y`, `Y'` is irreducible and `π⁻¹ U` is
scheme-theoretically dense in `Y'`. -/
theorem exists_chow_of_irreducibleSpace (Y : SchemeLFTℂ.{u}) [IrreducibleSpace Y.obj.left]
    [IsProper Y.obj.hom] :
    ∃ (N : ℕ) (Y' : SchemeLFTℂ.{u}) (j : Y' ⟶ projectiveSpace.{u} N) (π : Y' ⟶ Y)
      (U : Y.obj.left.Opens),
      IsClosedImmersion j.hom.left ∧
      IsClosedImmersion (pullback.lift π.hom.left j.hom.left
        ((Over.w π.hom).trans (Over.w j.hom).symm) :
          Y'.obj.left ⟶ pullback Y.obj.hom (projectiveSpace.{u} N).obj.hom) ∧
      (U : Set Y.obj.left).Nonempty ∧ IsIso (π.hom.left ∣_ U) ∧ IrreducibleSpace Y'.obj.left ∧
      IsSchemeTheoreticallyDominant (π.hom.left ⁻¹ᵁ U).ι := by
  obtain ⟨N, Z, c, U, hc, hq, hU, hπ, hZ, hd⟩ :=
    AlgebraicGeometry.exists_chow_of_irreducibleSpace Y.obj.hom
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
  refine ⟨N, Y', j, π, U, hq, ?_, hU, hπ, hZ, hd⟩
  rw [hlift]
  exact hc

end ComplexAnalytic
