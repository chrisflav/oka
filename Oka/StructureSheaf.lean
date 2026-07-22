/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Analysis.Analytic.Within
import Mathlib.Topology.Sheaves.LocalPredicate
import Oka.OkaRing

/-!
# The structure sheaf of `ℂ^ι`

We assemble the rings `OkaRing U` of holomorphic functions on the opens `U` of `ℂ^ι` into a
sheaf of rings `okaSheaf ι` on the site of opens of `ℂ^ι`.

## Main definitions

- `okaPresheaf`: the presheaf of rings `U ↦ OkaRing U`.
- `okaSheaf`: the structure sheaf of `ℂ^ι`, i.e. `okaPresheaf` together with the sheaf condition.
-/

open CategoryTheory TopologicalSpace Opposite

universe u

variable {ι : Type u} [Fintype ι]

namespace OkaRing

@[ext]
lemma ext {U : Opens (ι → ℂ)} {f g : OkaRing U} (h : f.toFun = g.toFun) : f = g :=
  Subtype.ext h

@[simp]
lemma restrict_toFun {U V : Opens (ι → ℂ)} (h : U ≤ V) (f : OkaRing V) :
    (OkaRing.restrict h f).toFun = f.toFun ∘ Opens.inclusion h :=
  rfl

@[simp]
lemma restrict_self {U : Opens (ι → ℂ)} (f : OkaRing U) :
    OkaRing.restrict le_rfl f = f :=
  rfl

@[simp]
lemma restrict_restrict {U V W : Opens (ι → ℂ)} (h : U ≤ V) (h' : V ≤ W) (f : OkaRing W) :
    OkaRing.restrict h (OkaRing.restrict h' f) = OkaRing.restrict (h.trans h') f :=
  rfl

end OkaRing

section Analytic

/-- Being holomorphic is a pointwise condition: since `U` is open, `OkaAnalytic f` holds if and
only if the extension of `f` by zero is analytic at every point of `U`. -/
lemma okaAnalytic_iff {U : Opens (ι → ℂ)} (f : U → ℂ) :
    OkaAnalytic f ↔ ∀ x ∈ U, AnalyticAt ℂ (Function.extend Subtype.val f 0) x :=
  U.isOpen.analyticOn_iff_analyticOnNhd

omit [Fintype ι] in
/-- Extending by zero commutes with restriction, up to functions agreeing near a point of the
smaller open set. -/
lemma extend_eventuallyEq_extend {U V : Opens (ι → ℂ)} (h : U ≤ V) (f : V → ℂ)
    {x : ι → ℂ} (hx : x ∈ U) :
    Function.extend Subtype.val (f ∘ Opens.inclusion h) 0 =ᶠ[nhds x]
      Function.extend Subtype.val f 0 := by
  filter_upwards [U.isOpen.mem_nhds hx] with y hy
  have h₁ : Function.extend Subtype.val (f ∘ Opens.inclusion h) 0 y = f ⟨y, h hy⟩ :=
    Subtype.val_injective.extend_apply (f := (Subtype.val : U → ι → ℂ)) _ _ ⟨y, hy⟩
  have h₂ : Function.extend Subtype.val f 0 y = f ⟨y, h hy⟩ :=
    Subtype.val_injective.extend_apply (f := (Subtype.val : V → ι → ℂ)) _ _ ⟨y, h hy⟩
  rw [h₁, h₂]

omit [Fintype ι] in
/-- Near a point of `U`, the extension by zero of the restriction of a globally defined
function agrees with the function itself. -/
lemma extend_restrict_eventuallyEq {U : Opens (ι → ℂ)} (g : (ι → ℂ) → ℂ)
    {x : ι → ℂ} (hx : x ∈ U) :
    Function.extend Subtype.val (fun y : U ↦ g y) 0 =ᶠ[nhds x] g := by
  filter_upwards [U.isOpen.mem_nhds hx] with y hy
  exact Subtype.val_injective.extend_apply (f := (Subtype.val : U → ι → ℂ)) _ _ ⟨y, hy⟩

/-- A function which is holomorphic at every point of `U` restricts to an element of the ring
of holomorphic functions on `U`. -/
lemma okaAnalytic_restrict {U : Opens (ι → ℂ)} {g : (ι → ℂ) → ℂ}
    (hg : ∀ x ∈ U, AnalyticAt ℂ g x) :
    OkaAnalytic (fun y : U ↦ g y) := by
  rw [okaAnalytic_iff]
  exact fun x hx ↦ (hg x hx).congr (extend_restrict_eventuallyEq g hx).symm

/-- The extension by zero of `f : OkaRing U` agrees with `f` on `U`. -/
lemma OkaRing.toGlobalFun_apply {U : Opens (ι → ℂ)} (f : OkaRing U) {x : ι → ℂ} (hx : x ∈ U) :
    f.toGlobalFun _ x = f.toFun _ ⟨x, hx⟩ :=
  Subtype.val_injective.extend_apply (f := (Subtype.val : U → ι → ℂ)) _ _ ⟨x, hx⟩

/-- Holomorphic functions restrict to holomorphic functions. -/
lemma OkaAnalytic.restrict {U V : Opens (ι → ℂ)} (h : U ≤ V) {f : V → ℂ} (hf : OkaAnalytic f) :
    OkaAnalytic (f ∘ Opens.inclusion h) := by
  rw [okaAnalytic_iff] at hf ⊢
  exact fun x hx ↦ (hf x (h hx)).congr (extend_eventuallyEq_extend h f hx).symm

/-- Being holomorphic is a local condition. -/
lemma okaAnalytic_of_locally {U : Opens (ι → ℂ)} (f : U → ℂ)
    (hf : ∀ x : U, ∃ (V : Opens (ι → ℂ)) (_ : x.1 ∈ V) (h : V ≤ U),
      OkaAnalytic (f ∘ Opens.inclusion h)) :
    OkaAnalytic f := by
  rw [okaAnalytic_iff]
  intro x hx
  obtain ⟨V, hxV, h, hV⟩ := hf ⟨x, hx⟩
  rw [okaAnalytic_iff] at hV
  exact (hV x hxV).congr (extend_eventuallyEq_extend h f hxV)

end Analytic

/-- The presheaf of rings of holomorphic functions on `ℂ^ι`. -/
noncomputable def okaPresheaf (ι : Type u) [Fintype ι] : (Opens (ι → ℂ))ᵒᵖ ⥤ RingCat.{u} where
  obj U := RingCat.of (OkaRing U.unop)
  map f := RingCat.ofHom (OkaRing.restrict (leOfHom f.unop)).toRingHom
  map_id U := by ext f; rfl
  map_comp f g := by ext h; rfl

/-- Being holomorphic, as a local predicate on the sheaf of `ℂ`-valued functions. -/
def okaLocalPredicate (ι : Type u) [Fintype ι] :
    TopCat.LocalPredicate (X := TopCat.of (ι → ℂ)) (fun _ ↦ ℂ) where
  pred {_} f := OkaAnalytic f
  res i _ hf := hf.restrict (leOfHom i)
  locality _ hf := okaAnalytic_of_locally _ fun x ↦ by
    obtain ⟨V, hxV, i, hi⟩ := hf x
    exact ⟨V, hxV, leOfHom i, hi⟩

/-- The presheaf of holomorphic functions is, as a presheaf of types, the subpresheaf of the
sheaf of all `ℂ`-valued functions cut out by the local predicate `OkaAnalytic`. -/
noncomputable def okaPresheafIsoSubpresheaf (ι : Type u) [Fintype ι] :
    okaPresheaf ι ⋙ CategoryTheory.forget RingCat.{u} ≅
      TopCat.subpresheafToTypes (okaLocalPredicate ι).toPrelocalPredicate :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)

/-- The presheaf of holomorphic functions on `ℂ^ι` is a sheaf. -/
theorem okaPresheaf_isSheaf (ι : Type u) [Fintype ι] :
    Presheaf.IsSheaf (Opens.grothendieckTopology (ι → ℂ)) (okaPresheaf ι) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (CategoryTheory.forget RingCat.{u}),
    isSheaf_iff_isSheaf_of_type]
  have h := TopCat.subpresheafToTypes.isSheaf (okaLocalPredicate ι)
  rw [TopCat.Presheaf.IsSheaf, isSheaf_iff_isSheaf_of_type] at h
  exact Presieve.isSheaf_iso _ (okaPresheafIsoSubpresheaf ι).symm h

/-- The structure sheaf of `ℂ^ι`: the sheaf of rings of holomorphic functions. -/
noncomputable def okaSheaf (ι : Type u) [Fintype ι] :
    Sheaf (Opens.grothendieckTopology (ι → ℂ)) RingCat.{u} :=
  ⟨okaPresheaf ι, okaPresheaf_isSheaf ι⟩
