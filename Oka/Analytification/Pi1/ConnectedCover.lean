/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Pi1.FundamentalGroup.Galois

/-!
# A connected finite étale cover has connected total space

In pi1's Galois category `AlgebraicGeometry.FiniteEtale S` of finite étale schemes over a connected
scheme `S`, an object is *connected* (`CategoryTheory.PreGaloisCategory.IsConnected`: not initial,
no non-trivial subobjects) when its underlying scheme is a connected topological space. The
converse-free direction proved here is the one needed to make the topological monodromy action on
the fibres of a connected cover transitive. Neither direction is in pi1.

## Main results

- `AlgebraicGeometry.FiniteEtale.connectedSpace_left_of_isConnected`.
-/

universe u

open CategoryTheory PreGaloisCategory Limits

namespace AlgebraicGeometry.FiniteEtale

/-- **A connected object of `FEt(S)` has connected total space**, for `S` connected. A clopen
`U` of the total space gives a subobject that is finite étale (an open and closed immersion
composed with the structure map), not initial (finite étale over a connected base and nonempty,
hence surjective, so its fibre is nonempty), hence an isomorphism. -/
theorem connectedSpace_left_of_isConnected {S : Scheme.{u}} [ConnectedSpace S] {Ω : Type u}
    [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ S) (A : FiniteEtale S) [IsConnected A] :
    ConnectedSpace A.left := by
  have hne : Nonempty A.left := by
    obtain ⟨p⟩ := nonempty_fiber_of_isConnected (fiber ξ) A
    exact ⟨(Limits.pullback.fst A.hom ξ).base p⟩
  refine connectedSpace_iff_clopen.2 ⟨hne, fun U hU ↦ ?_⟩
  by_cases hU0 : U = ∅
  · exact Or.inl hU0
  refine Or.inr ?_
  let V : A.left.Opens := ⟨U, hU.isOpen⟩
  haveI : IsClosedImmersion V.ι := by
    apply isClosedImmersion_of_isPreimmersion_of_isClosed
    simpa [V] using hU.isClosed
  let a : A.left ⟶ S := A.hom
  haveI : IsFiniteEtale a := A.2
  haveI : IsFiniteEtale V.ι := ⟨⟩
  haveI hVA : IsFiniteEtale (V.ι ≫ a) := inferInstance
  let B : FiniteEtale S := ⟨Over.mk (V.ι ≫ a), hVA⟩
  let i : B ⟶ A := MorphismProperty.Over.homMk V.ι
  haveI : Mono i := (FiniteEtale.mono_iff S B A i).2 ⟨inferInstanceAs (IsOpenImmersion V.ι),
    inferInstanceAs (IsClosedImmersion V.ι)⟩
  have hB : IsInitial B → False := by
    rw [not_initial_iff_fiber_nonempty (fiber ξ)]
    haveI : Nonempty V := by
      obtain ⟨v, hv⟩ := Set.nonempty_iff_ne_empty.2 hU0
      exact ⟨⟨v, hv⟩⟩
    obtain ⟨s⟩ : Nonempty (Spec (.of Ω)) := inferInstance
    obtain ⟨v, hv⟩ := (IsFiniteEtale.surjective (V.ι ≫ a)).surj (ξ s)
    obtain ⟨p, -⟩ := Scheme.Pullback.exists_preimage_pullback v s hv
    exact ⟨p⟩
  haveI : IsIso i := IsConnected.noTrivialComponent B i hB
  haveI : IsIso ((MorphismProperty.Over.forget _ _ _ ⋙ Over.forget _).map i) :=
    Functor.map_isIso _ i
  haveI : IsIso V.ι := this
  have hsurj := (Scheme.homeoOfIso (asIso V.ι)).surjective
  rw [Set.eq_univ_iff_forall]
  intro z
  obtain ⟨v, rfl⟩ := hsurj z
  exact v.2

end AlgebraicGeometry.FiniteEtale
