/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.ES.KummerEvalSections

/-!
# Sections of a finite étale cover of `B × Δ*` with prescribed values on the Kummer pieces

Keep the notation of `Oka/Analytification/RET/ES/KummerSections.lean`, with `e` a decomposition
of the finite étale cover `W` of `S°` into Kummer covers of degrees `kᵢ`. A section of `𝒪_W` is
determined by its values (`ComplexAnalytic.KummerModel.eq_of_forall_eval_eq_piece`), and every
family of holomorphic functions `gᵢⱼ` on `V` is the family of coefficients of a section over
`p⁻¹(V ∩ S°)` (`ComplexAnalytic.KummerModel.exists_section_eval_eq`), which is then bounded near
`t = 0`. Together with `ComplexAnalytic.KummerModel.isBoundedNearZero_iff` this identifies the
bounded sections with the families `(gᵢⱼ)`.

## Main results

- `ComplexAnalytic.KummerModel.isLocallyOpenInAffine_left`: `W` is locally isomorphic to opens of
  `ℂ^{m+1}`.
- `ComplexAnalytic.KummerModel.piece_base_eq_iff`: the pieces are disjoint and injective.
- `ComplexAnalytic.KummerModel.exists_section_eval_eq`: every family `(gᵢⱼ)` comes from a section.
-/

open CategoryTheory Opposite AlgebraicGeometry Topology TopologicalSpace

universe u

namespace ComplexAnalytic.KummerModel

open AnalyticSpace

noncomputable section

variable {m : ℕ} {B : Set (ULift.{u} (Fin m) → ℂ)} {hB : IsOpen B}
  {W : FiniteEtaleOver (punctured hB)} {ι : Type u} {k : ι → ℕ+} [Finite ι]
  (e : W ≅ FiniteEtaleOver.sigma fun i ↦ cover hB (k i))

instance isLocalIso_piece (i : ι) : IsLocalIso (piece e i) := by
  have hiso : IsIso e.inv.left :=
    ((MorphismProperty.Over.forget _ _ _ ⋙ CategoryTheory.Over.forget _).mapIso e).isIso_inv
  exact @isLocalIso_comp _ _ _ _ _ (isLocalIso_sigmaι (fun i ↦ (cover hB (k i)).left) i)
    (@isLocalIso_of_isIso _ _ e.inv.left hiso)

/-- The pieces of `W` are disjoint and each is injective. -/
lemma piece_base_eq_iff (i j : ι) (y y' : punctured hB) :
    (piece e i).toLRSHom.base y = (piece e j).toLRSHom.base y' ↔
      (⟨i, y⟩ : Σ _ : ι, punctured hB) = ⟨j, y'⟩ := by
  have hinj : Function.Injective e.inv.left.toLRSHom.base :=
    (FiniteEtaleOver.isHomeomorph_base_hom_left e.symm).injective
  have h := LocallyRingedSpace.sigmaι_base_eq_iff
    (fun i ↦ (cover hB (k i)).left.toLocallyRingedSpace) i j y y'
  refine ⟨fun h' ↦ h.1 (hinj h'), fun h' ↦ ?_⟩
  cases h'
  rfl

lemma injective_piece_base (i : ι) : Function.Injective (piece e i).toLRSHom.base := fun y y' h ↦
  eq_of_heq (Sigma.mk.inj ((piece_base_eq_iff e i i y y').1 h)).2

include e in
/-- `W` is locally isomorphic to opens of `ℂ^{m+1}`. -/
theorem isLocallyOpenInAffine_left : IsLocallyOpenInAffine W.left := fun w ↦ by
  obtain ⟨i, y, rfl⟩ := exists_piece e w
  exact ⟨m + 1, puncturedOpens B hB, piece e i, y, inferInstance, rfl⟩

include e in
/-- **A section of `𝒪_W` is determined by its values.** -/
theorem eq_of_forall_eval_eq_piece {O : W.left.Opens} {s s' : W.left.presheaf.obj (op O)}
    (h : ∀ w (hw : w ∈ O), W.left.eval w hw s = W.left.eval w hw s') : s = s' :=
  eq_of_forall_eval_eq (isLocallyOpenInAffine_left e) h

/-- The holomorphic function `x ↦ ∑_{j < k} tʲ gⱼ(b, tᵏ)` on `ℂ^{m+1}`. -/
def kummerFun {k : ℕ+} (g : Fin k → (ULift.{u} (Fin m) → ℂ) × ℂ → ℂ)
    (x : ULift.{u} (Fin (m + 1)) → ℂ) : ℂ :=
  ∑ j : Fin k, x zero ^ (j : ℕ) * g j (Kummer.powMap k (splitEquiv m x))

lemma differentiableOn_kummerFun {k : ℕ+} {g : Fin k → (ULift.{u} (Fin m) → ℂ) × ℂ → ℂ}
    {V' : Set ((ULift.{u} (Fin m) → ℂ) × ℂ)} (hg : ∀ j, DifferentiableOn ℂ (g j) V') :
    DifferentiableOn ℂ (kummerFun g)
      {x | Kummer.powMap k (splitEquiv m x) ∈ V'} := by
  have hs : Differentiable ℂ (fun x : ULift.{u} (Fin (m + 1)) → ℂ ↦ splitEquiv m x) := by
    refine Differentiable.prodMk (differentiable_pi.2 fun i ↦ ?_) (differentiable_apply _)
    exact differentiable_apply _
  refine DifferentiableOn.fun_sum fun j _ ↦ ((differentiable_apply _).differentiableOn.pow _).mul
    ((hg j).comp ((((Kummer.differentiable_powMap (E := ULift.{u} (Fin m) → ℂ) k).comp
      hs).differentiableOn : DifferentiableOn ℂ (fun y ↦ Kummer.powMap k (splitEquiv m y)) _))
      fun _ hx ↦ hx)

/-- **Every family of holomorphic coefficients comes from a section of `𝒪_W`.** -/
theorem exists_section_eval_eq {V : Set (ULift.{u} (Fin (m + 1)) → ℂ)} (hV : IsOpen V)
    (g : ∀ i, Fin (k i) → (ULift.{u} (Fin m) → ℂ) × ℂ → ℂ)
    (hg : ∀ i j, DifferentiableOn ℂ (g i j) ((splitEquiv m).symm ⁻¹' V)) :
    ∃ s : W.left.presheaf.obj (op ((Opens.map W.hom.toLRSHom.base).obj
        (puncturedPreimage hB hV))),
      ∀ i (y : punctured hB)
        (hy : W.hom.toLRSHom.base ((piece e i).toLRSHom.base y) ∈ puncturedPreimage hB hV),
        W.left.eval _ hy s = kummerFun (g i) y.1 := by
  choose I Y hIY using exists_piece e
  have hrep (i : ι) (y : punctured hB) :
      I ((piece e i).toLRSHom.base y) = i ∧ Y ((piece e i).toLRSHom.base y) = y := by
    have h := (piece_base_eq_iff e _ _ _ _).1 (hIY ((piece e i).toLRSHom.base y))
    exact ⟨(Sigma.mk.inj h).1, eq_of_heq (Sigma.mk.inj h).2⟩
  let f : W.left → ℂ := fun w ↦ kummerFun (g (I w)) (Y w).1
  have hf (i : ι) (y : punctured hB) : f ((piece e i).toLRSHom.base y) = kummerFun (g i) y.1 := by
    have key : ∀ i' (_ : i' = i) (y' : punctured hB) (_ : y' = y),
        kummerFun (g i') y'.1 = kummerFun (g i) y.1 := by
      rintro _ rfl _ rfl
      rfl
    exact key _ (hrep i y).1 _ (hrep i y).2
  set O := (Opens.map W.hom.toLRSHom.base).obj (puncturedPreimage hB hV)
  obtain ⟨s, hs⟩ := exists_eval_eq_of_local (isLocallyOpenInAffine_left e) (O := O) f
    fun w hw ↦ by
      obtain ⟨i, y₀, rfl⟩ := exists_piece e w
      set Ui : (punctured hB).Opens := (Opens.map (piece e i).toLRSHom.base).obj O
      set T : Opens (ULift.{u} (Fin (m + 1)) → ℂ) :=
        (puncturedOpens B hB).isOpenEmbedding.isOpenMap.functor.obj Ui
      have hT : ∀ x ∈ T, Kummer.powMap (k i) (splitEquiv m x) ∈ (splitEquiv m).symm ⁻¹' V := by
        rintro _ ⟨y, hy, rfl⟩
        change (splitEquiv m).symm (Kummer.powMap (k i) (splitEquiv m y.1)) ∈ V
        rw [splitEquiv_symm_powMap, ← coe_hom_base_piece e i y]
        exact hy
      let t : (punctured hB).presheaf.obj (op Ui) :=
        OkaRing.mk (U := T) (fun x ↦ kummerFun (g i) x.1) (okaAnalytic_restrict fun x hx ↦
          analyticAt_of_differentiableOn_of_finiteDimensional T.isOpen
            ((differentiableOn_kummerFun (hg i)).mono hT) hx)
      have ht (y : punctured hB) (hy : y ∈ Ui) :
          (punctured hB).eval y hy t = kummerFun (g i) y.1 := by
        rw [eval_restrict_complexAffineSpace_of]
        rfl
      obtain ⟨σ, hσ⟩ := exists_eval_eq_image (piece e i) (injective_piece_base e i) t
      refine ⟨_, Set.mem_image_of_mem (piece e i).toLRSHom.base (show y₀ ∈ Ui from hw), ?_, σ, ?_⟩
      · rintro _ ⟨y, hy, rfl⟩
        exact hy
      · rintro _ ⟨y, hy, rfl⟩
        rw [hσ y hy, ht, hf]
  exact ⟨s, fun i y hy ↦ (hs _ hy).trans (hf i y)⟩

end

end ComplexAnalytic.KummerModel
