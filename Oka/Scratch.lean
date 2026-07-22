import Oka.AnalyticSpace.Coherent

open CategoryTheory Limits TopologicalSpace Opposite SheafOfModules AlgebraicGeometry

universe u

namespace AlgebraicGeometry.LocallyRingedSpace

variable (Y : LocallyRingedSpace.{u})

/-- Restriction of a section of the structure sheaf to a smaller open subset. -/
abbrev res {U V : Opens Y} (h : U ≤ V) (s : Y.presheaf.obj (op V)) : Y.presheaf.obj (op U) :=
  Y.presheaf.map (homOfLE h).op s

/-- The structure sheaf of `Y` has **locally finitely generated relations**: every finite family
of sections has, near every point, finitely many relations generating all the others.

This is the concrete form of coherence, in the shape of `oka`. Unlike coherence stated via
`SheafOfModules.IsCoherent`, it refers only to open subsets, sections and restriction maps, so
it is manifestly local and transports along isomorphisms without any transport of sites. -/
def HasLocalRelations : Prop :=
  ∀ (V : Opens Y) (m : ℕ) (f : Fin m → Y.presheaf.obj (op V)) (x : Y), x ∈ V →
    ∃ (W : Opens Y) (hWV : W ≤ V) (k : ℕ) (g : Fin k → (Fin m → Y.presheaf.obj (op W))),
      x ∈ W ∧ ∀ (W' : Opens Y) (hW' : W' ≤ W),
        LinearMap.ker (linOfFun fun i ↦ Y.res (hW'.trans hWV) (f i)) =
          Submodule.span (Y.presheaf.obj (op W'))
            (Set.range fun l ↦ (fun i ↦ Y.res hW' (g l i)))

set_option maxHeartbeats 1000000 in
/-- A locally ringed space whose structure sheaf has locally finitely generated relations has
coherent structure sheaf. -/
theorem isCoherentStructureSheaf_of_hasLocalRelations (h : Y.HasLocalRelations) :
    Y.IsCoherentStructureSheaf := by
  classical
  haveI : (unit Y.ringSheaf).IsFiniteType := by apply SheafOfModules.isFiniteType_unit
  refine isCoherent_of_forall_kernel (M := unit Y.ringSheaf) ?_
  intro X I hI φ
  haveI := hI
  haveI : Fintype I := Fintype.ofFinite I
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin I
  set f : Fin m → Y.presheaf.obj (op X) := fun i ↦
    PresheafOfModules.sections.eval (freeHomEquiv _ φ (e.symm i)) (op (Over.mk (𝟙 X))) with hf
  choose V hVX k g hxV hgen using fun (x : X) ↦ h X m f x.1 x.2
  refine ⟨↥X, fun a ↦ Over.mk (homOfLE (hVX a)),
    coversTop_over X V hVX (fun x hx ↦ ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩), fun a ↦ ?_⟩
  set Ya : Over X := Over.mk (homOfLE (hVX a))
  set L := ULift.{u} (Fin (k a))
  have hWV : ∀ W : (Over Ya)ᵒᵖ, W.unop.left.left ≤ V a := fun W ↦ leOfHom W.unop.hom.left
  have hWX : ∀ W : (Over Ya)ᵒᵖ, W.unop.left.left ≤ X := fun W ↦ (hWV W).trans (hVX a)
  set ψ : free L ⟶ (free I).over Ya :=
    (freeHomEquiv _).symm (fun l ↦ sectionOfTerminal Over.mkIdTerminal ((free I).over Ya)
      (freeEvalSymm (R := Y.ringSheaf.over X) (I := I) (op (Over.mk (𝟙 Ya)).left)
        (fun i ↦ g a l.down (e i)))) with hψ
  have key_φ : ∀ (W : (Over Ya)ᵒᵖ) (b : ((free I).over Ya).val.obj W)
      (bc : I → Y.presheaf.obj (op W.unop.left.left))
      (_ : ∀ i, bc i = freeEval (op W.unop.left) b i)
      (v : Y.presheaf.obj (op W.unop.left.left)) (_ : v = (φ.over Ya).val.app W b),
      v = ∑ i : I, bc i * Y.res (hWX W) (f (e i)) := by
    intro W b bc hbc v hv
    have hsec : ∀ i : I, (PresheafOfModules.sections.eval (freeHomEquiv _ φ i)
        (op W.unop.left) : Y.presheaf.obj (op W.unop.left.left)) =
        Y.res (hWX W) (f (e i)) := by
      intro i
      simp only [hf, Equiv.symm_apply_apply]
      exact (PresheafOfModules.sections_property (freeHomEquiv _ φ i)
        (Over.mkIdTerminal.from W.unop.left).op).symm
    rw [hv, show (φ.over Ya).val.app W b = φ.val.app (op W.unop.left) b from rfl,
      val_app_eq_sum]
    refine Finset.sum_congr rfl (fun i _ ↦ ?_)
    rw [hbc i, ← hsec i]
    rfl
  have key_ψ : ∀ (W : (Over Ya)ᵒᵖ) (c : (free L).val.obj W)
      (cc : L → Y.presheaf.obj (op W.unop.left.left)) (_ : ∀ l, cc l = freeEval W c l) (i : I)
      (v : Y.presheaf.obj (op W.unop.left.left))
      (_ : v = freeEval (op W.unop.left) (ψ.val.app W c) i),
      v = ∑ l : L, cc l * Y.res (hWV W) (g a l.down (e i)) := by
    intro W c cc hcc i v hv
    obtain ⟨cc', hcc'⟩ : ∃ cc' : L → (Y.ringSheaf.over X).obj.obj (op W.unop.left),
        ∀ l, cc' l = cc l := ⟨fun l ↦ cc l, fun _ ↦ rfl⟩
    obtain ⟨vv, hvv⟩ : ∃ vv : L → I → (Y.ringSheaf.over X).obj.obj (op W.unop.left),
        ∀ l i, vv l i = Y.res (hWV W) (g a l.down (e i)) :=
      ⟨fun l i ↦ Y.res (hWV W) (g a l.down (e i)), fun _ _ ↦ rfl⟩
    have hsec : ∀ l : L, PresheafOfModules.sections.eval (freeHomEquiv _ ψ l) W =
        freeEvalSymm (op W.unop.left) (vv l) := by
      intro l
      rw [hψ, Equiv.apply_symm_apply, sectionOfTerminal_val,
        show vv l = fun i ↦ Y.res (hWV W) (g a l.down (e i)) from funext (hvv l)]
      exact map_freeEvalSymm (R := Y.ringSheaf.over X) (I := I)
        ((Over.mkIdTerminal.from W.unop).left).op (fun i ↦ g a l.down (e i))
    have h1 : ψ.val.app W c = freeEvalSymm (op W.unop.left)
        (fun i ↦ ∑ l : L, cc l * Y.res (hWV W) (g a l.down (e i))) := by
      have hrhs : freeEvalSymm (R := Y.ringSheaf.over X) (I := I) (op W.unop.left)
          (fun i ↦ ∑ l : L, cc l * Y.res (hWV W) (g a l.down (e i))) =
          ∑ l : L, cc' l • freeEvalSymm (op W.unop.left) (vv l) := by
        have hpi : (fun i ↦ ∑ l : L, cc l * Y.res (hWV W) (g a l.down (e i))) =
            ∑ l : L, cc' l • vv l := by
          funext i
          rw [Finset.sum_apply]
          refine Finset.sum_congr rfl (fun l _ ↦ ?_)
          rw [Pi.smul_apply, hcc', hvv]
          rfl
        refine (congrArg (freeEvalSymm (R := Y.ringSheaf.over X) (I := I)
          (op W.unop.left)) hpi).trans ((map_sum _ _ _).trans ?_)
        exact Finset.sum_congr rfl (fun l _ ↦ map_smul _ _ _)
      rw [val_app_eq_sum, hrhs]
      simp only [hsec, hcc', hcc]
      rfl
    rw [hv, h1]
    exact congrFun (freeEval_freeEvalSymm _ _) i
  have hgker : ∀ (W' : Opens Y) (hh : W' ≤ V a) (l : Fin (k a)),
      ∑ j : Fin m, Y.res hh (g a l j) * Y.res (hh.trans (hVX a)) (f j) = 0 := by
    intro W' hh l
    have hmem : (fun j ↦ Y.res hh (g a l j)) ∈
        LinearMap.ker (linOfFun fun j : Fin m ↦ Y.res (le_trans hh (hVX a)) (f j)) := by
      rw [hgen a W' hh]
      exact Submodule.subset_span ⟨l, rfl⟩
    rw [LinearMap.mem_ker, linOfFun_apply] at hmem
    exact hmem
  refine ⟨L, inferInstance, ψ, ?_, ?_⟩
  · ext W c
    obtain ⟨cc, hcc⟩ : ∃ cc : L → Y.presheaf.obj (op W.unop.left.left),
        ∀ l, cc l = freeEval W c l := ⟨fun l ↦ freeEval W c l, fun _ ↦ rfl⟩
    obtain ⟨v, hv⟩ : ∃ v : Y.presheaf.obj (op W.unop.left.left),
        v = (φ.over Ya).val.app W (ψ.val.app W c) := ⟨_, rfl⟩
    have h0 : v = 0 := by
      rw [key_φ W (ψ.val.app W c)
        (fun i ↦ ∑ l : L, cc l * Y.res (hWV W) (g a l.down (e i)))
        (fun i ↦ (key_ψ W c cc hcc i _ rfl).symm) v hv]
      have hterm : ∀ i : I, (∑ l : L, cc l * Y.res (hWV W) (g a l.down (e i))) *
            Y.res (hWX W) (f (e i)) =
          ∑ l : L, cc l * (Y.res (hWV W) (g a l.down (e i)) * Y.res (hWX W) (f (e i))) := by
        intro i
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl (fun l _ ↦ mul_assoc _ _ _)
      simp only [hterm]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero (fun l _ ↦ ?_)
      rw [← Finset.mul_sum, Equiv.sum_comp e (fun j : Fin m ↦
        Y.res (hWV W) (g a l.down j) * Y.res (hWX W) (f j)),
        hgker _ (hWV W) l.down, mul_zero]
    exact hv.symm.trans h0
  · intro W b hb
    obtain ⟨bc, hbc⟩ : ∃ bc : I → Y.presheaf.obj (op W.unop.left.left),
        ∀ i, bc i = freeEval (op W.unop.left) b i :=
      ⟨fun i ↦ freeEval (op W.unop.left) b i, fun _ ↦ rfl⟩
    have hcker : (fun j ↦ bc (e.symm j)) ∈ LinearMap.ker
        (linOfFun fun j : Fin m ↦ Y.res (hWX W) (f j)) := by
      rw [LinearMap.mem_ker, linOfFun_apply,
        ← Equiv.sum_comp e (fun j : Fin m ↦ bc (e.symm j) * Y.res (hWX W) (f j))]
      obtain ⟨v, hv⟩ : ∃ v : Y.presheaf.obj (op W.unop.left.left),
          v = (φ.over Ya).val.app W b := ⟨_, rfl⟩
      have h0 : v = 0 := hv.trans hb
      rw [key_φ W b bc hbc v hv] at h0
      simpa only [Equiv.symm_apply_apply] using h0
    rw [hgen a W.unop.left.left (hWV W)] at hcker
    obtain ⟨r, hr⟩ :=
      (Submodule.mem_span_range_iff_exists_fun (Y.presheaf.obj (op W.unop.left.left))).1 hcker
    refine ⟨freeEvalSymm W (fun l : L ↦ (r l.down : Y.presheaf.obj (op W.unop.left.left))), ?_⟩
    refine freeEval_injective (op W.unop.left) (funext fun i ↦ ?_)
    have h1 := key_ψ W
      (freeEvalSymm W (fun l : L ↦ (r l.down : Y.presheaf.obj (op W.unop.left.left))))
      (fun l ↦ r l.down)
      (fun l ↦ (congrFun (freeEval_freeEvalSymm (R := (Y.ringSheaf.over X).over Ya) (I := L) W
        (fun l : L ↦ (r l.down : Y.presheaf.obj (op W.unop.left.left)))) l).symm) i _ rfl
    have hsum : (∑ l : L, (r l.down : Y.presheaf.obj (op W.unop.left.left)) *
        Y.res (hWV W) (g a l.down (e i))) =
        ∑ j : Fin (k a), r j * Y.res (hWV W) (g a j (e i)) :=
      Fintype.sum_equiv Equiv.ulift _ _ (fun _ ↦ rfl)
    have h2 : (∑ j : Fin (k a), r j * Y.res (hWV W) (g a j (e i))) = bc i := by
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Equiv.symm_apply_apply]
        using congrFun hr (e i)
    exact h1.trans (hsum.trans (h2.trans (hbc i)))

end AlgebraicGeometry.LocallyRingedSpace
