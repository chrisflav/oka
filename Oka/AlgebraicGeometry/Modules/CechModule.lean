/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.AlgebraicGeometry.ProjectiveSpace.RelativeSerre
import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-!
# Čech cohomology of `𝒪_X`-modules as modules over a ring of constants

Let `X` be a scheme, `ρ : R →+* Γ(X, ⊤)` a ring of global constants, `U : ι → X.Opens` a family of
opens and `F` an `𝒪_X`-module. Multiplication by `ρ r` is an endomorphism of the underlying
abelian sheaf of `F` (`Scheme.Modules.smulAb`), hence of the Čech complex `Č•(U, F)`
(`Scheme.Modules.cechSmul`). This makes the Čech cohomology `Ȟᵠ(U, F)` an `R`-module
(`Scheme.Modules.cechHomologyModule`, not an instance), and the maps in the long exact sequence
of a short exact sequence of `𝒪_X`-modules are `R`-linear.

## Main results

* `Scheme.Modules.CechFinite ρ U F q`: `Ȟᵠ(U, F)` is a finitely generated `R`-module.
* `Scheme.Modules.cechFinite_X₃`: for a short exact sequence `0 → F₁ → F₂ → F₃ → 0` of
  `𝒪_X`-modules which is surjective on all `U_σ`, and `R` noetherian, finiteness of `Ȟᵠ(F₂)` and
  `Ȟᵠ⁺¹(F₁)` implies finiteness of `Ȟᵠ(F₃)`.
* `Scheme.Modules.cechFinite_of_iso`, `Scheme.Modules.cechFinite_sigma`: invariance under
  isomorphisms and finite coproducts.
* `Scheme.Modules.cechFinite_of_exactAt`, `Scheme.Modules.cechFinite_of_cocycles`: criteria.
-/

universe u

open CategoryTheory Limits TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-! ### Multiplication by global functions -/

section SMul

lemma ores_add {V W : X.Opens} (h : W ≤ V) (r s : Γ(X, V)) :
    TopCat.Presheaf.restrictOpen (r + s) W h =
      TopCat.Presheaf.restrictOpen r W h + TopCat.Presheaf.restrictOpen s W h := by
  simp [TopCat.Presheaf.restrictOpen, TopCat.Presheaf.restrict]

variable (F : X.Modules)

lemma smulAb_app_apply (a : Γ(X, ⊤)) (V : X.Opensᵒᵖ) (s : Γ(F, V.unop)) :
    (smulAb F a).app V s = (a |ₒ V.unop) • s :=
  rfl

lemma smulAb_add (a b : Γ(X, ⊤)) : smulAb F (a + b) = smulAb F a + smulAb F b := by
  ext V s
  change ((a + b) |ₒ V.unop) • (show Γ(F, V.unop) from s) =
    (a |ₒ V.unop) • (show Γ(F, V.unop) from s) + (b |ₒ V.unop) • (show Γ(F, V.unop) from s)
  rw [ores_add, add_smul]

lemma smulAb_mul (a b : Γ(X, ⊤)) : smulAb F (a * b) = smulAb F b ≫ smulAb F a := by
  ext V s
  change ((a * b) |ₒ V.unop) • (show Γ(F, V.unop) from s) =
    (a |ₒ V.unop) • (b |ₒ V.unop) • (show Γ(F, V.unop) from s)
  rw [ores_mul, mul_smul]

lemma smulAb_one : smulAb F 1 = 𝟙 _ := by
  ext V s
  change ((1 : Γ(X, ⊤)) |ₒ V.unop) • (show Γ(F, V.unop) from s) = s
  rw [ores_one, one_smul]

lemma smulAb_zero : smulAb F 0 = 0 := by
  ext V s
  change ((0 : Γ(X, ⊤)) |ₒ V.unop) • (show Γ(F, V.unop) from s) = 0
  rw [ores_zero, zero_smul]

variable {F} in
lemma smulAb_naturality {G : X.Modules} (φ : F ⟶ G) (a : Γ(X, ⊤)) :
    smulAb F a ≫ ((SheafOfModules.toSheaf X.ringCatSheaf).map φ).hom =
      ((SheafOfModules.toSheaf X.ringCatSheaf).map φ).hom ≫ smulAb G a := by
  ext V s
  change φ.val.app V ((a |ₒ V.unop) • (show Γ(F, V.unop) from s)) =
    (a |ₒ V.unop) • φ.val.app V s
  exact (φ.val.app V).hom.map_smul _ _

end SMul

/-! ### The action on Čech cohomology -/

variable {ι : Type u} (U : ι → X.Opens)

/-- The Čech complex functor `F ↦ Č•(U, F)` on `𝒪_X`-modules. -/
noncomputable abbrev cechFunctor : X.Modules ⥤ CochainComplex AddCommGrpCat.{u} ℕ :=
  SheafOfModules.toSheaf X.ringCatSheaf ⋙ sheafToPresheaf _ _ ⋙
    TopCat.Presheaf.cechComplexFunctor U

instance : (cechFunctor U).Additive := by
  dsimp only [cechFunctor]
  infer_instance

/-- The Čech complex `Č•(U, F)` of the underlying abelian sheaf of `F`. -/
noncomputable abbrev cech (F : X.Modules) : CochainComplex AddCommGrpCat.{u} ℕ :=
  (cechFunctor U).obj F

/-- The map of Čech complexes induced by a morphism of `𝒪_X`-modules. -/
noncomputable abbrev cechMap {F G : X.Modules} (φ : F ⟶ G) : cech U F ⟶ cech U G :=
  (cechFunctor U).map φ

/-- Multiplication by a global function on the Čech complex. -/
noncomputable abbrev cechSmul (F : X.Modules) (a : Γ(X, ⊤)) : cech U F ⟶ cech U F :=
  (TopCat.Presheaf.cechComplexFunctor U).map (smulAb F a)

lemma cechSmul_naturality {F G : X.Modules} (φ : F ⟶ G) (a : Γ(X, ⊤)) :
    cechSmul U F a ≫ cechMap U φ = cechMap U φ ≫ cechSmul U G a := by
  change (TopCat.Presheaf.cechComplexFunctor U).map _ ≫
      (TopCat.Presheaf.cechComplexFunctor U).map
        ((SheafOfModules.toSheaf X.ringCatSheaf).map φ).hom = _ ≫ _
  rw [← CategoryTheory.Functor.map_comp, smulAb_naturality]
  rfl

lemma cechSmul_one (F : X.Modules) : cechSmul U F 1 = 𝟙 _ := by
  rw [cechSmul, smulAb_one]
  exact (TopCat.Presheaf.cechComplexFunctor U).map_id _

lemma cechSmul_mul (F : X.Modules) (a b : Γ(X, ⊤)) :
    cechSmul U F (a * b) = cechSmul U F b ≫ cechSmul U F a := by
  rw [cechSmul, smulAb_mul]
  exact (TopCat.Presheaf.cechComplexFunctor U).map_comp _ _

lemma cechSmul_zero (F : X.Modules) : cechSmul U F 0 = 0 := by
  rw [cechSmul, smulAb_zero]
  exact (TopCat.Presheaf.cechComplexFunctor U).map_zero _ _

lemma cechSmul_add (F : X.Modules) (a b : Γ(X, ⊤)) :
    cechSmul U F (a + b) = cechSmul U F a + cechSmul U F b := by
  rw [cechSmul, smulAb_add]
  exact (TopCat.Presheaf.cechComplexFunctor U).map_add

variable {R : Type u} [CommRing R] (ρ : R →+* Γ(X, ⊤))

/-- The action of `R` on `Ȟᵠ(U, F)` through `ρ`. -/
noncomputable def cechHomologyAct (F : X.Modules) (q : ℕ) :
    R →+* AddMonoid.End ((cech U F).homology q) where
  toFun r := (HomologicalComplex.homologyMap (cechSmul U F (ρ r)) q).hom
  map_one' := by
    rw [map_one, cechSmul_one, HomologicalComplex.homologyMap_id]
    rfl
  map_mul' r s := by
    rw [map_mul, cechSmul_mul, HomologicalComplex.homologyMap_comp]
    rfl
  map_zero' := by
    rw [map_zero, cechSmul_zero, HomologicalComplex.homologyMap_zero]
    rfl
  map_add' r s := by
    rw [map_add, cechSmul_add, HomologicalComplex.homologyMap_add]
    rfl

/-- `Ȟᵠ(U, F)` as an `R`-module through `ρ`. -/
noncomputable abbrev cechHomologyModule (F : X.Modules) (q : ℕ) :
    Module R ((cech U F).homology q) :=
  Module.compHom _ (cechHomologyAct U ρ F q)

lemma cechHomology_smul_def (F : X.Modules) (q : ℕ) (r : R) (x : (cech U F).homology q) :
    letI := cechHomologyModule U ρ F q
    r • x = HomologicalComplex.homologyMap (cechSmul U F (ρ r)) q x :=
  rfl

/-- **Finiteness of Čech cohomology**: `Ȟᵠ(U, F)` is a finitely generated `R`-module. -/
def CechFinite (F : X.Modules) (q : ℕ) : Prop :=
  letI := cechHomologyModule U ρ F q
  Module.Finite R ((cech U F).homology q)

/-- The `R`-linear map `Ȟᵠ(U, F) → Ȟᵠ(U, G)` induced by a morphism of `𝒪_X`-modules. -/
noncomputable def cechHomologyLinear {F G : X.Modules} (φ : F ⟶ G) (q : ℕ) :
    letI := cechHomologyModule U ρ F q
    letI := cechHomologyModule U ρ G q
    (cech U F).homology q →ₗ[R] (cech U G).homology q :=
  letI := cechHomologyModule U ρ F q
  letI := cechHomologyModule U ρ G q
  { toFun := HomologicalComplex.homologyMap (cechMap U φ) q
    map_add' := map_add _
    map_smul' r x := by
      simp only [cechHomology_smul_def, RingHom.id_apply]
      rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
        ← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
        cechSmul_naturality] }

lemma cechHomologyLinear_apply {F G : X.Modules} (φ : F ⟶ G) (q : ℕ)
    (x : (cech U F).homology q) :
    cechHomologyLinear U ρ φ q x = HomologicalComplex.homologyMap (cechMap U φ) q x :=
  rfl

/-! ### Short exact sequences -/

section ShortExact

variable {S : ShortComplex X.Modules}
  (hS : (S.map (SheafOfModules.toSheaf X.ringCatSheaf)).ShortExact)
  (hsurj : ∀ (n : ℕ) (σ : Fin (n + 1) → ι),
    Function.Surjective (S.g.val.app (op (TopCat.Presheaf.cechOpen U σ))))

include hS hsurj

/-- The short exact sequence of Čech complexes of a short exact sequence of `𝒪_X`-modules which
is surjective on all `U_σ`. -/
lemma cech_shortExact : (S.map (cechFunctor U)).ShortExact :=
  TopCat.Presheaf.cechComplex_shortExact_of_sheaf hS hsurj

/-- The connecting map `Ȟᵠ(U, S.X₃) → Ȟᵠ⁺¹(U, S.X₁)` is `R`-linear. -/
noncomputable def cechδLinear (q : ℕ) :
    letI := cechHomologyModule U ρ S.X₃ q
    letI := cechHomologyModule U ρ S.X₁ (q + 1)
    (cech U S.X₃).homology q →ₗ[R] (cech U S.X₁).homology (q + 1) :=
  letI := cechHomologyModule U ρ S.X₃ q
  letI := cechHomologyModule U ρ S.X₁ (q + 1)
  { toFun := (cech_shortExact U hS hsurj).δ q (q + 1) (by simp)
    map_add' := map_add _
    map_smul' r x := by
      simp only [cechHomology_smul_def, RingHom.id_apply]
      let Φ : S.map (cechFunctor U) ⟶ S.map (cechFunctor U) :=
        { τ₁ := cechSmul U S.X₁ (ρ r)
          τ₂ := cechSmul U S.X₂ (ρ r)
          τ₃ := cechSmul U S.X₃ (ρ r)
          comm₁₂ := (cechSmul_naturality U S.f (ρ r))
          comm₂₃ := (cechSmul_naturality U S.g (ρ r)) }
      have h := HomologicalComplex.HomologySequence.δ_naturality Φ (cech_shortExact U hS hsurj)
        (cech_shortExact U hS hsurj) q (q + 1) (by simp)
      have hx := ConcreteCategory.congr_hom h x
      simp only [ConcreteCategory.comp_apply] at hx
      exact hx.symm }

lemma cechδLinear_apply (q : ℕ) (x : (cech U S.X₃).homology q) :
    cechδLinear U ρ hS hsurj q x = (cech_shortExact U hS hsurj).δ q (q + 1) (by simp) x :=
  rfl

/-- **Finiteness along a short exact sequence.** If `R` is noetherian, `Ȟᵠ(U, S.X₂)` and
`Ȟᵠ⁺¹(U, S.X₁)` are finite, then so is `Ȟᵠ(U, S.X₃)`. -/
theorem cechFinite_X₃ [IsNoetherianRing R] (q : ℕ) (h₂ : CechFinite U ρ S.X₂ q)
    (h₁ : CechFinite U ρ S.X₁ (q + 1)) : CechFinite U ρ S.X₃ q := by
  letI := cechHomologyModule U ρ S.X₁ (q + 1)
  letI := cechHomologyModule U ρ S.X₂ q
  letI := cechHomologyModule U ρ S.X₃ q
  have : Module.Finite R ((cech U S.X₂).homology q) := h₂
  have : Module.Finite R ((cech U S.X₁).homology (q + 1)) := h₁
  let g := cechHomologyLinear U ρ S.g q
  let δ := cechδLinear U ρ hS hsurj q
  have hex : Function.Exact g δ := by
    have e := (cech_shortExact U hS hsurj).homology_exact₃ q (q + 1) (by simp)
    exact (ShortComplex.ab_exact_iff_function_exact _).1 e
  have : Module.Finite R (LinearMap.range δ) := Module.Finite.of_injective
    (LinearMap.range δ).subtype Subtype.val_injective
  exact Module.Finite.of_exact (f := g) (g := δ.rangeRestrict)
    (fun x => by
      rw [← hex x]
      simp [LinearMap.rangeRestrict, Subtype.ext_iff])
    δ.surjective_rangeRestrict

end ShortExact

/-! ### Criteria -/

/-- Exactness implies finiteness. -/
lemma cechFinite_of_exactAt (F : X.Modules) (q : ℕ) (h : (cech U F).ExactAt q) :
    CechFinite U ρ F q := by
  letI := cechHomologyModule U ρ F q
  rw [HomologicalComplex.exactAt_iff_isZero_homology, AddCommGrpCat.isZero_iff_subsingleton] at h
  exact Module.Finite.of_finite

lemma cechHomologyLinear_comp_apply {F G K : X.Modules} (φ : F ⟶ G) (ψ : G ⟶ K) (q : ℕ)
    (x : (cech U F).homology q) :
    cechHomologyLinear U ρ ψ q (cechHomologyLinear U ρ φ q x) =
      cechHomologyLinear U ρ (φ ≫ ψ) q x := by
  simp only [cechHomologyLinear_apply]
  rw [← ConcreteCategory.comp_apply, ← HomologicalComplex.homologyMap_comp,
    ← CategoryTheory.Functor.map_comp]

lemma cechHomologyLinear_id_apply (F : X.Modules) (q : ℕ) (x : (cech U F).homology q) :
    cechHomologyLinear U ρ (𝟙 F) q x = x := by
  simp only [cechHomologyLinear_apply, CategoryTheory.Functor.map_id,
    HomologicalComplex.homologyMap_id]
  rfl

lemma cechHomologyLinear_sum_apply {F G : X.Modules} {J : Type*} (s : Finset J)
    (φ : J → (F ⟶ G)) (q : ℕ) (x : (cech U F).homology q) :
    cechHomologyLinear U ρ (∑ j ∈ s, φ j) q x = ∑ j ∈ s, cechHomologyLinear U ρ (φ j) q x := by
  simp only [cechHomologyLinear_apply, CategoryTheory.Functor.map_sum]
  rw [← HomologicalComplex.homologyFunctor_map, CategoryTheory.Functor.map_sum]
  simp only [HomologicalComplex.homologyFunctor_map, AddCommGrpCat.finsetSum_apply]

/-- Finiteness is invariant under isomorphisms of `𝒪_X`-modules. -/
lemma cechFinite_of_iso {F G : X.Modules} (e : F ≅ G) (q : ℕ) (h : CechFinite U ρ F q) :
    CechFinite U ρ G q := by
  letI := cechHomologyModule U ρ F q
  letI := cechHomologyModule U ρ G q
  have : Module.Finite R ((cech U F).homology q) := h
  refine Module.Finite.of_surjective (cechHomologyLinear U ρ e.hom q) fun y =>
    ⟨cechHomologyLinear U ρ e.inv q y, ?_⟩
  rw [cechHomologyLinear_comp_apply, e.inv_hom_id, cechHomologyLinear_id_apply]

/-- Finiteness for a finite coproduct. -/
lemma cechFinite_sigma {I : Type u} [Finite I] (G : I → X.Modules) (q : ℕ)
    (h : ∀ i, CechFinite U ρ (G i) q) : CechFinite U ρ (∐ G) q := by
  have := Fintype.ofFinite I
  have := HasBiproduct.of_hasCoproduct G
  refine cechFinite_of_iso U ρ (biproduct.isoCoproduct G) q ?_
  letI := cechHomologyModule U ρ (⨁ G) q
  letI (i : I) := cechHomologyModule U ρ (G i) q
  have (i : I) : Module.Finite R ((cech U (G i)).homology q) := h i
  let Φ : (∀ i, (cech U (G i)).homology q) →ₗ[R] (cech U (⨁ G)).homology q :=
    ∑ i, (cechHomologyLinear U ρ (biproduct.ι G i) q).comp (LinearMap.proj i)
  refine Module.Finite.of_surjective Φ fun x =>
    ⟨fun i => cechHomologyLinear U ρ (biproduct.π G i) q x, ?_⟩
  have htot : ∑ i, biproduct.π G i ≫ biproduct.ι G i = 𝟙 (⨁ G) :=
    IsBilimit.total (biproduct.isBilimit G)
  conv_rhs => rw [← cechHomologyLinear_id_apply U ρ (⨁ G) q x, ← htot,
    cechHomologyLinear_sum_apply]
  simp only [Φ, LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    cechHomologyLinear_comp_apply]

/-! ### Cochain-level descriptions -/

lemma cechSmul_f_apply (F : X.Modules) (a : Γ(X, ⊤)) (q : ℕ) (z : (cech U F).X q)
    (σ : Fin (q + 1) → ι) :
    ((cechSmul U F a).f q z : TopCat.Presheaf.CechCochain U
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj F).obj q) σ =
      (a |ₒ TopCat.Presheaf.cechOpen U σ) •
        (show Γ(F, TopCat.Presheaf.cechOpen U σ) from
          (z : TopCat.Presheaf.CechCochain U
            ((SheafOfModules.toSheaf X.ringCatSheaf).obj F).obj q) σ) :=
  rfl

omit [CommRing R] in
lemma exists_iCycles_eq (K : CochainComplex AddCommGrpCat.{u} ℕ) (i : ℕ) (z : K.X i)
    (hz : K.d i (i + 1) z = 0) : ∃ c, K.iCycles i c = z := by
  have hex := ShortComplex.exact_of_f_is_kernel
    (ShortComplex.mk (K.iCycles i) (K.d i (i + 1)) (K.iCycles_d i (i + 1)))
    (K.cyclesIsKernel i (i + 1) (by simp))
  exact (ShortComplex.ab_exact_iff _).1 hex z hz

/-- The action of `R` on the Čech cochains of degree `q`, through `ρ`. -/
noncomputable def cechCochainAct (F : X.Modules) (q : ℕ) :
    R →+* AddMonoid.End ((cech U F).X q) where
  toFun r := ((cechSmul U F (ρ r)).f q).hom
  map_one' := by
    rw [map_one, cechSmul_one]
    rfl
  map_mul' r s := by
    rw [map_mul, cechSmul_mul, HomologicalComplex.comp_f]
    rfl
  map_zero' := by
    rw [map_zero, cechSmul_zero]
    rfl
  map_add' r s := by
    rw [map_add, cechSmul_add, HomologicalComplex.add_f_apply]
    rfl

/-- The Čech cochains of degree `q` as an `R`-module through `ρ`. -/
noncomputable abbrev cechCochainModule (F : X.Modules) (q : ℕ) : Module R ((cech U F).X q) :=
  Module.compHom _ (cechCochainAct U ρ F q)

/-- **A cochain-level criterion for finiteness.** Let `R` be noetherian. If there are finitely many
`(p+1)`-cochains `s j` such that every `(p+1)`-cocycle is an `R`-combination of them up to a
coboundary, then `Ȟᵖ⁺¹(U, F)` is finite. -/
theorem cechFinite_of_cocycles [IsNoetherianRing R] (F : X.Modules) (p : ℕ) {N : ℕ}
    (s : Fin N → (cech U F).X (p + 1))
    (h : ∀ z : (cech U F).X (p + 1), (cech U F).d (p + 1) (p + 2) z = 0 →
      ∃ (r : Fin N → R) (c : (cech U F).X p),
        z = ∑ j, (cechSmul U F (ρ (r j))).f (p + 1) (s j) + (cech U F).d p (p + 1) c) :
    CechFinite U ρ F (p + 1) := by
  classical
  letI := cechHomologyModule U ρ F (p + 1)
  letI := cechCochainModule U ρ F (p + 1)
  letI := cechCochainModule U ρ F (p + 2)
  let K := cech U F
  have hiinj : Function.Injective (K.iCycles (p + 1)) :=
    (AddCommGrpCat.mono_iff_injective _).1 inferInstance
  let dL : K.X (p + 1) →ₗ[R] K.X (p + 2) :=
    { toFun := K.d (p + 1) (p + 2)
      map_add' := map_add _
      map_smul' := fun r x => by
        change K.d (p + 1) (p + 2) ((cechSmul U F (ρ r)).f (p + 1) x) =
          (cechSmul U F (ρ r)).f (p + 2) (K.d (p + 1) (p + 2) x)
        rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
          (cechSmul U F (ρ r)).comm] }
  let M : Submodule R (K.X (p + 1)) := Submodule.span R (Set.range s)
  let P : Submodule R (K.X (p + 1)) := M ⊓ LinearMap.ker dL
  have hM : M.FG := Submodule.fg_span (Set.finite_range s)
  haveI : _root_.IsNoetherian R M := isNoetherian_of_fg_of_noetherian M hM
  have hP : P.FG := by
    have h1 := _root_.IsNoetherian.noetherian (P.comap M.subtype)
    have h2 := h1.map M.subtype
    rwa [Submodule.map_comap_subtype, inf_eq_right.mpr inf_le_left] at h2
  haveI : Module.Finite R P := Module.Finite.iff_fg.mpr hP
  have hcyc (x : P) : K.d (p + 1) (p + 2) (x : K.X (p + 1)) = 0 := x.2.2
  choose t ht using fun x : P => exists_iCycles_eq K (p + 1) (x : K.X (p + 1)) (hcyc x)
  let θ : P →ₗ[R] K.homology (p + 1) :=
    { toFun := fun x => K.homologyπ (p + 1) (t x)
      map_add' := fun a b => by
        rw [← map_add]
        congr 1
        apply hiinj
        rw [map_add, ht, ht, ht]
        rfl
      map_smul' := fun r a => by
        rw [cechHomology_smul_def, RingHom.id_apply, ← ConcreteCategory.comp_apply,
          HomologicalComplex.homologyπ_naturality, ConcreteCategory.comp_apply]
        congr 1
        apply hiinj
        rw [← ConcreteCategory.comp_apply, HomologicalComplex.cyclesMap_i,
          ConcreteCategory.comp_apply, ht, ht]
        rfl }
  refine Module.Finite.of_surjective θ fun x => ?_
  obtain ⟨c, rfl⟩ := (AddCommGrpCat.epi_iff_surjective (K.homologyπ (p + 1))).1 inferInstance x
  have hz : K.d (p + 1) (p + 2) (K.iCycles (p + 1) c) = 0 := by
    rw [← ConcreteCategory.comp_apply, K.iCycles_d]
    rfl
  obtain ⟨r, b, hzb⟩ := h _ hz
  let m : K.X (p + 1) := ∑ j, (cechSmul U F (ρ (r j))).f (p + 1) (s j)
  have hmM : m ∈ M := Submodule.sum_mem _ fun j _ =>
    Submodule.smul_mem M (r j) (Submodule.subset_span ⟨j, rfl⟩)
  have hdb : K.iCycles (p + 1) (K.toCycles p (p + 1) b) = K.d p (p + 1) b := by
    rw [← ConcreteCategory.comp_apply, HomologicalComplex.toCycles_i]
  have hm : m = K.iCycles (p + 1) (c - K.toCycles p (p + 1) b) := by
    rw [map_sub, hdb, hzb]
    abel
  have hmZ : m ∈ LinearMap.ker dL := by
    rw [LinearMap.mem_ker, hm]
    change K.d (p + 1) (p + 2) _ = 0
    rw [← ConcreteCategory.comp_apply, K.iCycles_d]
    rfl
  refine ⟨⟨m, hmM, hmZ⟩, ?_⟩
  change K.homologyπ (p + 1) (t ⟨m, hmM, hmZ⟩) = _
  have htm : t ⟨m, hmM, hmZ⟩ = c - K.toCycles p (p + 1) b := hiinj ((ht _).trans hm)
  rw [htm, map_sub, ← ConcreteCategory.comp_apply (K.toCycles p (p + 1)),
    HomologicalComplex.toCycles_comp_homologyπ]
  change _ - 0 = _
  rw [sub_zero]

omit [CommRing R] in
lemma exists_toCycles_eq_of_homologyπ_eq_zero (K : CochainComplex AddCommGrpCat.{u} ℕ) (p : ℕ)
    (z : K.cycles (p + 1)) (hz : K.homologyπ (p + 1) z = 0) :
    ∃ b : K.X p, K.toCycles p (p + 1) b = z := by
  have hex := ShortComplex.exact_of_g_is_cokernel
    (ShortComplex.mk (K.toCycles p (p + 1)) (K.homologyπ (p + 1))
      (K.toCycles_comp_homologyπ p (p + 1)))
    (K.homologyIsCokernel p (p + 1) (by simp))
  exact (ShortComplex.ab_exact_iff _).1 hex z hz

/-- **Bounded torsion.** If `Ȟᵖ⁺¹(U, F)` is a finite module over the noetherian ring `R`, then for
every `t ∈ R` there is `N` such that every `(p+1)`-cocycle `y` with `tᵏ y` a coboundary for some
`k` has `t^N y` a coboundary. -/
theorem CechFinite.exists_pow_smul_eq_d [IsNoetherianRing R] {F : X.Modules} {p : ℕ}
    (h : CechFinite U ρ F (p + 1)) (t : R) :
    ∃ N : ℕ, ∀ y : (cech U F).X (p + 1), (cech U F).d (p + 1) (p + 2) y = 0 →
      ∀ (k : ℕ) (c : (cech U F).X p),
        (cechSmul U F (ρ (t ^ k))).f (p + 1) y = (cech U F).d p (p + 1) c →
        ∃ c' : (cech U F).X p,
          (cechSmul U F (ρ (t ^ N))).f (p + 1) y = (cech U F).d p (p + 1) c' := by
  letI := cechHomologyModule U ρ F (p + 1)
  haveI : Module.Finite R ((cech U F).homology (p + 1)) := h
  let K := cech U F
  let f : ℕ →o Submodule R (K.homology (p + 1)) :=
    { toFun := fun k => LinearMap.ker (t ^ k • LinearMap.id)
      monotone' := fun k l hkl x hx => by
        simp only [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply] at hx ⊢
        rw [← Nat.sub_add_cancel hkl, pow_add, mul_smul, hx, smul_zero] }
  obtain ⟨N, hN⟩ := (monotone_stabilizes_iff_noetherian.mpr inferInstance) f
  refine ⟨N, fun y hy k c hc => ?_⟩
  obtain ⟨cy, hcy⟩ := exists_iCycles_eq K (p + 1) y hy
  have hiinj : Function.Injective (K.iCycles (p + 1)) :=
    (AddCommGrpCat.mono_iff_injective _).1 inferInstance
  have hsmul (r : R) : r • K.homologyπ (p + 1) cy = K.homologyπ (p + 1)
      (HomologicalComplex.cyclesMap (cechSmul U F (ρ r)) (p + 1) cy) := by
    rw [cechHomology_smul_def, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      HomologicalComplex.homologyπ_naturality]
  have hi (r : R) : K.iCycles (p + 1)
      (HomologicalComplex.cyclesMap (cechSmul U F (ρ r)) (p + 1) cy) =
        (cechSmul U F (ρ r)).f (p + 1) y := by
    rw [← ConcreteCategory.comp_apply, HomologicalComplex.cyclesMap_i,
      ConcreteCategory.comp_apply, hcy]
  have hk : K.homologyπ (p + 1) cy ∈ f k := by
    change t ^ k • K.homologyπ (p + 1) cy = 0
    rw [hsmul]
    have : HomologicalComplex.cyclesMap (cechSmul U F (ρ (t ^ k))) (p + 1) cy =
        K.toCycles p (p + 1) c := by
      apply hiinj
      rw [hi, hc, ← ConcreteCategory.comp_apply, HomologicalComplex.toCycles_i]
    rw [this, ← ConcreteCategory.comp_apply, HomologicalComplex.toCycles_comp_homologyπ]
    rfl
  have hN' : K.homologyπ (p + 1) cy ∈ f N := by
    rw [hN (max k N) (le_max_right k N)]
    exact f.monotone (le_max_left k N) hk
  change t ^ N • K.homologyπ (p + 1) cy = 0 at hN'
  rw [hsmul] at hN'
  obtain ⟨c', hc'⟩ := exists_toCycles_eq_of_homologyπ_eq_zero K p _ hN'
  refine ⟨c', ?_⟩
  rw [← hi, ← hc', ← ConcreteCategory.comp_apply, HomologicalComplex.toCycles_i]

lemma cechSmul_f_comm (F : X.Modules) (a : Γ(X, ⊤)) (p : ℕ) (z : (cech U F).X p) :
    (cech U F).d p (p + 1) ((cechSmul U F a).f p z) =
      (cechSmul U F a).f (p + 1) ((cech U F).d p (p + 1) z) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, (cechSmul U F a).comm]

lemma cechSmul_f_mul (F : X.Modules) (a b : Γ(X, ⊤)) (p : ℕ) (z : (cech U F).X p) :
    (cechSmul U F (a * b)).f p z = (cechSmul U F a).f p ((cechSmul U F b).f p z) := by
  rw [cechSmul_mul, HomologicalComplex.comp_f, ConcreteCategory.comp_apply]

/-- **The degree-zero formal-functions chase.** Let `t ∈ R` act injectively on `Č²(U, F)`, and let
`N` bound the `t`-power torsion of `Ȟ¹(U, F)` (`CechFinite.exists_pow_smul_eq_d`). If `x₁, xₘ` are
`0`-cochains with `d xₘ ∈ t^{N+1} Č¹` and `xₘ ≡ x₁ mod t`, then `x₁` is congruent modulo `t` to a
`0`-cocycle. -/
theorem exists_cocycle_sub_eq_smul {F : X.Modules} (t : R) (N : ℕ)
    (hinj : ∀ (k : ℕ) (z : (cech U F).X 2), (cechSmul U F (ρ (t ^ k))).f 2 z = 0 → z = 0)
    (hN : ∀ y : (cech U F).X 1, (cech U F).d 1 2 y = 0 →
      ∀ (k : ℕ) (c : (cech U F).X 0),
        (cechSmul U F (ρ (t ^ k))).f 1 y = (cech U F).d 0 1 c →
        ∃ c' : (cech U F).X 0, (cechSmul U F (ρ (t ^ N))).f 1 y = (cech U F).d 0 1 c')
    (x₁ xₘ : (cech U F).X 0)
    (hdm : ∃ y, (cech U F).d 0 1 xₘ = (cechSmul U F (ρ (t ^ (N + 1)))).f 1 y)
    (hdiff : ∃ w, xₘ - x₁ = (cechSmul U F (ρ t)).f 0 w) :
    ∃ a : (cech U F).X 0, (cech U F).d 0 1 a = 0 ∧
      ∃ z, x₁ - a = (cechSmul U F (ρ t)).f 0 z := by
  let K := cech U F
  obtain ⟨y, hy⟩ := hdm
  obtain ⟨w, hw⟩ := hdiff
  have hdy : K.d 1 2 y = 0 := by
    apply hinj (N + 1)
    rw [← cechSmul_f_comm, ← hy]
    exact ConcreteCategory.congr_hom (K.d_comp_d 0 1 2) xₘ
  obtain ⟨c, hc⟩ := hN y hdy (N + 1) xₘ hy.symm
  refine ⟨x₁ - (cechSmul U F (ρ t)).f 0 (c - w), ?_, c - w, by abel⟩
  have hx₁ : x₁ = xₘ - (cechSmul U F (ρ t)).f 0 w := by rw [← hw]; abel
  rw [hx₁, map_sub, map_sub, hy, cechSmul_f_comm, cechSmul_f_comm, map_sub, map_sub, ← hc,
    ← cechSmul_f_mul, ← map_mul, ← pow_succ']
  abel

/-! ### Degree zero -/

section DegreeZero

variable (hU : ⨆ i, U i = ⊤)

/-- The global sections `Γ(F, ⊤)` as an `R`-module through `ρ`. -/
noncomputable abbrev sectionsModule (F : X.Modules) : Module R Γ(F, ⊤) :=
  Module.compHom _ ρ

include hU in
/-- `Γ(F, ⊤) → Ȟ⁰(U, F)`, `R`-linearly, is bijective. -/
theorem exists_linearEquiv_cech_zero (F : X.Modules) :
    letI := sectionsModule ρ F
    letI := cechHomologyModule U ρ F 0
    Nonempty (Γ(F, ⊤) ≃ₗ[R] (cech U F).homology 0) := by
  letI := sectionsModule ρ F
  letI := cechHomologyModule U ρ F 0
  let K := cech U F
  let G := (SheafOfModules.toSheaf X.ringCatSheaf).obj F
  have hW : ∀ i, U i ≤ ⊤ := fun _ => le_top
  have hcov : (⊤ : X.Opens) ≤ ⨆ i, U i := hU.ge
  have haug (s : Γ(F, ⊤)) : K.d 0 1 (TopCat.Presheaf.cechAugment U G.obj hW s) = 0 :=
    (funext (TopCat.Presheaf.cechComplex_d_apply U G.obj 0 _)).trans
      (TopCat.Presheaf.cechD_cechAugment U G.obj hW s)
  choose t ht using fun s : Γ(F, ⊤) =>
    exists_iCycles_eq K 0 (TopCat.Presheaf.cechAugment U G.obj hW s) (haug s)
  have hπ : IsIso (K.homologyπ 0) := K.isIso_homologyπ 0 0 (by simp) (by simp)
  have hπinj : Function.Injective (K.homologyπ 0) :=
    (AddCommGrpCat.mono_iff_injective _).1 inferInstance
  have hiinj : Function.Injective (K.iCycles 0) :=
    (AddCommGrpCat.mono_iff_injective _).1 inferInstance
  let ψ : Γ(F, ⊤) →ₗ[R] K.homology 0 :=
    { toFun := fun s => K.homologyπ 0 (t s)
      map_add' := fun a b => by
        rw [← map_add]
        congr 1
        apply hiinj
        rw [map_add, ht, ht, ht, map_add]
      map_smul' := fun r a => by
        rw [cechHomology_smul_def, RingHom.id_apply, ← ConcreteCategory.comp_apply,
          HomologicalComplex.homologyπ_naturality, ConcreteCategory.comp_apply]
        congr 1
        apply hiinj
        rw [← ConcreteCategory.comp_apply, HomologicalComplex.cyclesMap_i,
          ConcreteCategory.comp_apply, ht, ht]
        funext σ
        change TopCat.Presheaf.restrictOpen (F := F.presheaf)
            ((ρ r) • (show Γ(F, ⊤) from a)) (TopCat.Presheaf.cechOpen U σ) le_top =
          (ρ r |ₒ TopCat.Presheaf.cechOpen U σ) • TopCat.Presheaf.restrictOpen (F := F.presheaf)
            (show Γ(F, ⊤) from a) (TopCat.Presheaf.cechOpen U σ) le_top
        rw [mres_smul] }
  refine ⟨LinearEquiv.ofBijective ψ ⟨fun a b hab => ?_, fun x => ?_⟩⟩
  · apply TopCat.Presheaf.cechAugment_injective U hW G hcov
    rw [← ht, ← ht]
    exact congrArg _ (hπinj hab)
  · obtain ⟨c, rfl⟩ := (AddCommGrpCat.epi_iff_surjective (K.homologyπ 0)).1 inferInstance x
    have hc : TopCat.Presheaf.cechD U G.obj 0 (K.iCycles 0 c) = 0 := by
      have h1 := ConcreteCategory.congr_hom (K.iCycles_d 0 1) c
      exact (funext (TopCat.Presheaf.cechComplex_d_apply U G.obj 0 _)).symm.trans h1
    obtain ⟨s, hs⟩ := TopCat.Presheaf.exists_cechAugment_eq U hW G hcov _ hc
    refine ⟨s, congrArg (K.homologyπ 0) (hiinj ?_)⟩
    exact (ht s).trans hs

include hU in
lemma cechFinite_zero_iff (F : X.Modules) :
    CechFinite U ρ F 0 ↔ (letI := sectionsModule ρ F; Module.Finite R Γ(F, ⊤)) := by
  letI := sectionsModule ρ F
  letI := cechHomologyModule U ρ F 0
  obtain ⟨e⟩ := exists_linearEquiv_cech_zero U ρ hU F
  constructor
  · intro h
    haveI : Module.Finite R ((cech U F).homology 0) := h
    exact Module.Finite.equiv e.symm
  · intro h
    exact Module.Finite.equiv e

end DegreeZero

end AlgebraicGeometry.Scheme.Modules
