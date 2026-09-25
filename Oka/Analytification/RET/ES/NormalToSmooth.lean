/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.AnalyticSpace.HartogsTorsionFree
import Oka.Analytification.RET.ES.BoundedSectionsHartogs
import Oka.Analytification.RET.ES.Normalization
import Oka.Analytification.RET.ES.FiniteSplitting
import Oka.Geometry.RingedSpace.LocallyRingedSpace.ReflexiveHull

/-!
# Essential surjectivity: from a big open of a normal affine scheme

Let `X` be an affine scheme of finite type over `ℂ` whose ring of functions `A` is a finite product
of normal domains, `U ⊆ X` an open whose complement has codimension at least two (for instance the
smooth locus) and `W` a Hausdorff finite étale cover of `X^an` whose restriction to `U^an` is the
analytification of a finite étale cover `Y ⟶ U`. Then `W` is the analytification of a finite étale
cover of `X` (`ComplexAnalytic.mem_essImage_of_restrict`), granted two statements recorded as
hypotheses:

* `ComplexAnalytic.NormalHartogs`: on `X^an`, sections over `Ω ∩ U^an` extend uniquely to `Ω`
  for every open `Ω`;
* `ComplexAnalytic.NormalizationInCover`: the normalisation `q : Y' ⟶ X` of `X` in `Y` is finite,
  `Y'` is affine with ring of functions a finite product of normal domains, `q⁻¹ U` has complement
  of codimension at least two, and `Y ≅ q⁻¹ U` over `U`.

## Proof

With `B = Γ(Y', 𝒪)`, the stalks of `q^an_* 𝒪` are `𝒪_{X^an,v} ⊗[A] B`
(`ComplexAnalytic.finiteAnalyticSplitting`). Over `U^an`, both `q^an : Y'^an ⟶ X^an` and
`p : W ⟶ X^an` have the local model `Y ⟶ U`, which identifies the sections of `q^an_* 𝒪` and
`p_* 𝒪_W` over opens inside `U^an` (`ComplexAnalytic.compareEquiv₀`). Hartogs extension holds on
`Y'^an` by `ComplexAnalytic.NormalHartogs` for `Y'`, and on `W`, which is étale over `X^an`, by
`ComplexAnalytic.bijective_res_of_isLocalIso`. Hence the identification extends to an isomorphism
`q^an_* 𝒪 ≅ p_* 𝒪_W` of presheaves of rings on `X^an` over `𝒪_{X^an}`
(`ComplexAnalytic.compareIso`). Therefore `𝒪_{X^an,v} ⊗[A] B → (p_* 𝒪_W)_v` is bijective for
every `v` (`ComplexAnalytic.bijective_pushforwardStalkTensorMap_of_iso`), and the
algebraisation criterion `ComplexAnalytic.exists_iso_of_bijective_pushforwardStalkTensorMap`
applies.

The Hartogs extension for coherent submodules of free modules on opens of `ℂⁿ`
(`ComplexAnalytic.BoundedSections.bijective_restrict_of_regularPair`) is the analytic input for
`ComplexAnalytic.NormalHartogs` through a Noether normalisation `X ⟶ 𝔸ⁿ`.

## Main definitions

- `ComplexAnalytic.HasCodimTwoComplement`: the complement of an open has codimension at least two.
- `ComplexAnalytic.NormalHartogs`, `ComplexAnalytic.NormalizationInCover`: the two hypotheses.
- `ComplexAnalytic.compareIso`: the isomorphism of pushforwards of two spaces over `X^an` with a
  common local model over `U`, both with Hartogs extension across the complement of `U^an`.

## Main results

- `ComplexAnalytic.BoundedSections.bijective_restrict_of_regularPair`: Hartogs extension for
  coherent sheaves with separating functionals on opens of `ℂⁿ`.
- `ComplexAnalytic.LocalModel.bijective_secMap`: a local model identifies sections over opens
  inside `U^an`.
- `ComplexAnalytic.bijective_res_of_isLocalIso`: Hartogs extension transfers along local
  isomorphisms.
- `ComplexAnalytic.bijective_pushforwardStalkTensorMap_of_iso`: the stalk criterion transports
  along isomorphisms of pushforwards.
- `ComplexAnalytic.mem_essImage_of_restrict`: the reduction.
-/

open CategoryTheory Opposite AlgebraicGeometry Topology TopologicalSpace TensorProduct

universe u

/-! ### Hartogs extension on open subsets of `ℂⁿ` -/

namespace ComplexAnalytic.BoundedSections

open AnalyticSpace LocallyRingedSpace

variable {n : ℕ} {N : (AnalyticSpace.complexAffineSpace.{u} n).Opens}

/-- **Hartogs extension for coherent submodules of free modules on opens of `ℂⁿ`.** Let `N ⊆ ℂⁿ`
be open, `g, h` holomorphic on `N` whose germs form a regular sequence at their common zeros, and
`O ⊆ N` the complement of the common zero set `T`. Let `M` be a coherent sheaf on `N` with
separating functionals, such that at every `z ∈ T` the germ of `g` is a nonzerodivisor on
`𝒪_{ℂⁿ,z}` and `[g, h]` is weakly regular on `M_z`. Then restriction `M(V) → M(V ∩ O)` is
bijective for every open `V ⊆ N`. -/
theorem bijective_restrict_of_regularPair {M : SheafOfModules.{u} (space N).ringSheaf}
    [M.IsCoherent] (D : SeparatingFunctionals M ⊤) (g h : (space N).presheaf.obj (op ⊤))
    (hP : ∀ z : Cn.{u} n, z ∈ N → holFun g z = 0 → holFun h z = 0 →
      ∃ G H : LocalOkaRing (ULift.{u} (Fin n)),
        (G : MvPowerSeries (ULift.{u} (Fin n)) ℂ).Represents (fun w ↦ holFun g (w + z)) ∧
        (H : MvPowerSeries (ULift.{u} (Fin n)) ℂ).Represents (fun w ↦ holFun h (w + z)) ∧
        RingTheory.Sequence.IsWeaklyRegular (LocalOkaRing (ULift.{u} (Fin n))) [G, H])
    (O : (space N).Opens) (hO : (O : Set (space N)) = {y | holFun g y.1 = 0 ∧ holFun h y.1 = 0}ᶜ)
    (hg𝒪 : ∀ z : space N, holFun g z.1 = 0 → holFun h z.1 = 0 →
      IsSMulRegular ((space N).presheaf.stalk z) ((space N).presheaf.germ ⊤ z trivial g))
    (hreg : ∀ z : space N, holFun g z.1 = 0 → holFun h z.1 = 0 →
      RingTheory.Sequence.IsWeaklyRegular ((space N).stalkFunctor z |>.obj M)
        [(space N).presheaf.germ ⊤ z trivial g, (space N).presheaf.germ ⊤ z trivial h])
    (V : (space N).Opens) :
    Function.Bijective fun t : M.val.obj (op V) ↦ modRes t (V ⊓ O) inf_le_left := by
  let P : RegularPairFamily (img (⊤ : (space N).Opens) : Set (Cn.{u} n)) :=
    { k := 1
      g := fun _ ↦ holFun g
      h := fun _ ↦ holFun h
      continuousOn_g := fun _ ↦ (differentiableOn_holFun g).continuousOn
      continuousOn_h := fun _ ↦ (differentiableOn_holFun h).continuousOn
      isWeaklyRegular := fun _ z hz hgz hhz ↦ hP z (img_le _ z hz) hgz hhz }
  refine bijective_restrict_of_separatingFunctionals D
    (T := {y | holFun g y.1 = 0 ∧ holFun h y.1 = 0}) (fun _ _ ↦ trivial) O hO g h
    (fun y _ hy ↦ (eval_space g y _).trans hy.1) (fun y _ hy ↦ (eval_space h y _).trans hy.2)
    (fun z hz ↦ hg𝒪 z hz.1 hz.2) (fun z hz ↦ hreg z hz.1 hz.2) (fun V' _ ↦ ?_) V
  refine (bijective_map_of_regularPairFamily P (V := V') (V' := V' ⊓ O) le_top inf_le_left
    ?_).2
  rintro _ ⟨⟨y, hy, rfl⟩, hyZ⟩
  refine ⟨y, ⟨hy, ?_⟩, rfl⟩
  have : y ∈ (O : Set (space N)) := by
    rw [hO]
    exact fun hgh ↦ hyZ (Set.mem_iUnion.2 ⟨0, hgh⟩)
  exact this

end ComplexAnalytic.BoundedSections

/-! ### Sections through a local model -/

namespace ComplexAnalytic

open AnalyticSpace SchemeLFTℂ

noncomputable section

namespace LocalModel

variable {X : SchemeLFTℂ.{u}} {T : AnalyticSpace.{u}} {q : T ⟶ analytification.obj X}
  {U : X.obj.left.Opens} (M : LocalModel q U)

/-- `e` is an open immersion of locally ringed spaces. -/
theorem isOpenImmersion_e : LocallyRingedSpace.IsOpenImmersion M.e.toLRSHom := by
  set O := (TopologicalSpace.Opens.map q.toLRSHom.base).obj
    (analytificationOpenImmersionPreimage (X.restrictι U))
  set i := M.isPullback.isoIsPullback _ _ (isPullback_ofRestrict_preimage_restrictι q U)
  have he : M.e.toLRSHom = i.hom.toLRSHom ≫ (T.ofRestrict O).toLRSHom :=
    congrArg Hom.toLRSHom M.e_eq
  haveI : IsIso i.hom.toLRSHom := Functor.map_isIso forgetToLocallyRingedSpace i.hom
  haveI : LocallyRingedSpace.IsOpenImmersion i.hom.toLRSHom :=
    LocallyRingedSpace.IsOpenImmersion.of_isIso _
  haveI : LocallyRingedSpace.IsOpenImmersion (T.ofRestrict O).toLRSHom :=
    LocallyRingedSpace.isOpenImmersion_ofRestrict T.toLocallyRingedSpace O
  rw [he]
  infer_instance

/-- The image of `e` is `q⁻¹(U^an)`. -/
theorem range_e : Set.range M.e.toLRSHom.base = ((TopologicalSpace.Opens.map q.toLRSHom.base).obj
      (analytificationOpenImmersionPreimage (X.restrictι U)) : Set T) := by
  ext t
  constructor
  · rintro ⟨z, rfl⟩
    rw [M.e_eq]
    exact ((M.isPullback.isoIsPullback _ _
      (isPullback_ofRestrict_preimage_restrictι q U)).hom.toLRSHom.base z).2
  · intro ht
    refine M.mem_range_e t ?_
    rw [range_analytification_map_restrictι]
    have : (analytificationπ X).left.base (q.toLRSHom.base t) ∈
        Set.range (X.restrictι U).hom.left.base := ht
    obtain ⟨x, hx⟩ := this
    change (analytificationπLRS X).base (q.toLRSHom.base t) ∈ (U : Set X.obj.left)
    exact hx ▸ x.2

/-- **`e` is bijective on sections over opens inside `q⁻¹(U^an)`.** -/
theorem bijective_e_c_app (V : T.Opens)
    (hV : V ≤ (TopologicalSpace.Opens.map q.toLRSHom.base).obj
      (analytificationOpenImmersionPreimage (X.restrictι U))) :
    Function.Bijective (M.e.toLRSHom.c.app (op V)).hom := by
  haveI : PresheafedSpace.IsOpenImmersion M.e.toLRSHom.toHom := M.isOpenImmersion_e
  haveI : IsIso (M.e.toLRSHom.c.app (op V)) := by
    refine PresheafedSpace.IsOpenImmersion.c_iso' (f := M.e.toLRSHom.toHom)
      ((TopologicalSpace.Opens.map M.e.toLRSHom.base).obj V) ?_
    ext y
    refine ⟨fun hy ↦ ?_, ?_⟩
    · obtain ⟨z, rfl⟩ : y ∈ Set.range M.e.toLRSHom.base := by
        rw [M.range_e]
        exact hV hy
      exact ⟨z, hy, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact hz
  exact ConcreteCategory.bijective_of_isIso _

/-- The composite `Y^an ⟶ V^an ⟶ X^an`. -/
def toBase : analytification.obj M.Y ⟶ analytification.obj X :=
  analytification.map M.p ≫ analytification.map (X.restrictι U)

/-- `e` followed by `q` is `Y^an ⟶ V^an ⟶ X^an`. -/
lemma e_comp : M.e ≫ q = M.toBase :=
  M.isPullback.w

/-- The preimage of an open of `X^an` under `e ≫ q`. -/
lemma preimage_e_preimage (Ω : (analytification.obj X).Opens) :
    (TopologicalSpace.Opens.map M.e.toLRSHom.base).obj
        ((TopologicalSpace.Opens.map q.toLRSHom.base).obj Ω) =
      (TopologicalSpace.Opens.map M.toBase.toLRSHom.base).obj Ω :=
  congrArg (fun f : analytification.obj M.Y ⟶ analytification.obj X ↦
    (TopologicalSpace.Opens.map f.toLRSHom.base).obj Ω) M.e_comp

/-- Sections of `T` over `q⁻¹ Ω` pulled back to `Y^an` along `e`, as sections over the preimage of
`Ω` under `Y^an ⟶ V^an ⟶ X^an`. -/
def secMap (Ω : (analytification.obj X).Opens) :
    T.presheaf.obj (op ((TopologicalSpace.Opens.map q.toLRSHom.base).obj Ω)) ⟶
      (analytification.obj M.Y).presheaf.obj
        (op ((TopologicalSpace.Opens.map M.toBase.toLRSHom.base).obj Ω)) :=
  M.e.toLRSHom.c.app (op ((TopologicalSpace.Opens.map q.toLRSHom.base).obj Ω)) ≫
    (analytification.obj M.Y).presheaf.map (homOfLE (M.preimage_e_preimage Ω).ge).op

/-- **A local model identifies sections over opens inside `U^an`** with sections of `Y^an`. -/
theorem bijective_secMap (Ω : (analytification.obj X).Opens)
    (hΩ : Ω ≤ analytificationOpenImmersionPreimage (X.restrictι U)) :
    Function.Bijective (M.secMap Ω).hom := by
  have h2 : Function.Bijective ((analytification.obj M.Y).presheaf.map
      (homOfLE (M.preimage_e_preimage Ω).ge).op).hom := by
    rw [show homOfLE (M.preimage_e_preimage Ω).ge = eqToHom (M.preimage_e_preimage Ω).symm
      from Subsingleton.elim _ _]
    exact ConcreteCategory.bijective_of_isIso _
  exact h2.comp (M.bijective_e_c_app _ fun _ h ↦ hΩ h)

lemma secMap_naturality {Ω Ω' : (analytification.obj X).Opens} (h : Ω' ≤ Ω) :
    T.presheaf.map (homOfLE ((TopologicalSpace.Opens.map q.toLRSHom.base).monotone h)).op ≫
        M.secMap Ω' =
      M.secMap Ω ≫ (analytification.obj M.Y).presheaf.map (homOfLE
        ((TopologicalSpace.Opens.map M.toBase.toLRSHom.base).monotone h)).op := by
  rw [secMap, secMap, ← Category.assoc, M.e.toLRSHom.c.naturality, Category.assoc]
  simp only [TopCat.Presheaf.pushforward_obj_map, Category.assoc]
  exact congrArg (fun φ ↦ M.e.toLRSHom.c.app _ ≫ φ)
    (((analytification.obj M.Y).presheaf.map_comp _ _).symm.trans
      ((congrArg _ (Subsingleton.elim _ _)).trans
        ((analytification.obj M.Y).presheaf.map_comp _ _)))

lemma c_app_secMap (Ω : (analytification.obj X).Opens) :
    q.toLRSHom.c.app (op Ω) ≫ M.secMap Ω = M.toBase.toLRSHom.c.app (op Ω) := by
  have h := PresheafedSpace.congr_app (congrArg (fun f ↦ f.toLRSHom.toHom) M.e_comp) (op Ω)
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) h).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) (((analytification.obj M.Y).presheaf.map_comp _ _).symm.trans
    ((congrArg _ (Subsingleton.elim _ (𝟙 _))).trans
      ((analytification.obj M.Y).presheaf.map_id _)))).trans (Category.comp_id _)

lemma secMap_res {Ω Ω' : (analytification.obj X).Opens} (h : Ω' ≤ Ω)
    (s : T.presheaf.obj (op ((TopologicalSpace.Opens.map q.toLRSHom.base).obj Ω))) :
    M.secMap Ω' (T.presheaf.map
      (homOfLE ((TopologicalSpace.Opens.map q.toLRSHom.base).monotone h)).op s) =
      (analytification.obj M.Y).presheaf.map (homOfLE
        ((TopologicalSpace.Opens.map M.toBase.toLRSHom.base).monotone h)).op (M.secMap Ω s) :=
  ConcreteCategory.congr_hom (M.secMap_naturality h) s

lemma secMap_c_app (Ω : (analytification.obj X).Opens)
    (s : (analytification.obj X).presheaf.obj (op Ω)) :
    M.secMap Ω (q.toLRSHom.c.app (op Ω) s) = M.toBase.toLRSHom.c.app (op Ω) s :=
  ConcreteCategory.congr_hom (M.c_app_secMap Ω) s

end LocalModel

/-! ### Comparing two spaces over `X^an` with a common local model -/

section Compare

variable {X : SchemeLFTℂ.{u}} {U : X.obj.left.Opens} {T₁ T₂ : AnalyticSpace.{u}}
  {q₁ : T₁ ⟶ analytification.obj X} {q₂ : T₂ ⟶ analytification.obj X} (M₁ : LocalModel q₁ U)
  (e₂ : analytification.obj M₁.Y ⟶ T₂)
  (h₂ : IsPullback e₂ (analytification.map M₁.p) q₂ (analytification.map (X.restrictι U)))

/-- The local model of `q₂` with the finite étale cover `Y ⟶ V` of the local model `M₁` of `q₁`. -/
def LocalModel.withE : LocalModel q₂ U :=
  ⟨M₁.Y, M₁.p, M₁.isFiniteEtale_p, e₂, h₂⟩

/-- **Over opens inside `U^an`**, the sections of `q₁_* 𝒪` and `q₂_* 𝒪` are identified through
their common local model `Y^an`. -/
def compareEquiv₀ (Ω : (analytification.obj X).Opens)
    (hΩ : Ω ≤ analytificationOpenImmersionPreimage (X.restrictι U)) :
    T₁.presheaf.obj (op ((TopologicalSpace.Opens.map q₁.toLRSHom.base).obj Ω)) ≃+*
      T₂.presheaf.obj (op ((TopologicalSpace.Opens.map q₂.toLRSHom.base).obj Ω)) :=
  (RingEquiv.ofBijective _ (M₁.bijective_secMap Ω hΩ)).trans
    (RingEquiv.ofBijective _ ((M₁.withE e₂ h₂).bijective_secMap Ω hΩ)).symm

lemma secMap_compareEquiv₀ (Ω : (analytification.obj X).Opens)
    (hΩ : Ω ≤ analytificationOpenImmersionPreimage (X.restrictι U))
    (s : T₁.presheaf.obj (op ((TopologicalSpace.Opens.map q₁.toLRSHom.base).obj Ω))) :
    (M₁.withE e₂ h₂).secMap Ω (compareEquiv₀ M₁ e₂ h₂ Ω hΩ s) = M₁.secMap Ω s :=
  (RingEquiv.ofBijective _ ((M₁.withE e₂ h₂).bijective_secMap Ω hΩ)).apply_symm_apply _

lemma compareEquiv₀_c_app (Ω : (analytification.obj X).Opens)
    (hΩ : Ω ≤ analytificationOpenImmersionPreimage (X.restrictι U))
    (s : (analytification.obj X).presheaf.obj (op Ω)) :
    compareEquiv₀ M₁ e₂ h₂ Ω hΩ (q₁.toLRSHom.c.app (op Ω) s) = q₂.toLRSHom.c.app (op Ω) s :=
  ((M₁.withE e₂ h₂).bijective_secMap Ω hΩ).1 ((secMap_compareEquiv₀ M₁ e₂ h₂ Ω hΩ _).trans
    ((M₁.secMap_c_app Ω s).trans ((M₁.withE e₂ h₂).secMap_c_app Ω s).symm))

lemma compareEquiv₀_res {Ω Ω' : (analytification.obj X).Opens} (h : Ω' ≤ Ω)
    (hΩ : Ω ≤ analytificationOpenImmersionPreimage (X.restrictι U))
    (s : T₁.presheaf.obj (op ((TopologicalSpace.Opens.map q₁.toLRSHom.base).obj Ω))) :
    compareEquiv₀ M₁ e₂ h₂ Ω' (h.trans hΩ) (T₁.presheaf.map
      (homOfLE ((TopologicalSpace.Opens.map q₁.toLRSHom.base).monotone h)).op s) =
      T₂.presheaf.map (homOfLE ((TopologicalSpace.Opens.map q₂.toLRSHom.base).monotone h)).op
        (compareEquiv₀ M₁ e₂ h₂ Ω hΩ s) := by
  refine ((M₁.withE e₂ h₂).bijective_secMap Ω' (h.trans hΩ)).1 ?_
  refine (secMap_compareEquiv₀ M₁ e₂ h₂ Ω' _ _).trans ?_
  refine (M₁.secMap_res h s).trans ?_
  refine Eq.trans ?_ ((M₁.withE e₂ h₂).secMap_res h _).symm
  exact congrArg _ (secMap_compareEquiv₀ M₁ e₂ h₂ Ω hΩ s).symm

/-- Composing two restriction maps of sections. -/
lemma presheaf_map_map_apply (T : AnalyticSpace.{u}) {A B C : T.Opens} (f : op A ⟶ op B)
    (g : op B ⟶ op C) (k : op A ⟶ op C) (s : T.presheaf.obj (op A)) :
    T.presheaf.map g (T.presheaf.map f s) = T.presheaf.map k s :=
  (ConcreteCategory.congr_hom (T.presheaf.map_comp f g) s).symm.trans
    (congrArg (fun k' ↦ T.presheaf.map k' s) (Subsingleton.elim _ _))

variable
  (hH₁ : ∀ Ω : (analytification.obj X).Opens, Function.Bijective (T₁.presheaf.map
    (homOfLE ((TopologicalSpace.Opens.map q₁.toLRSHom.base).monotone
      (inf_le_left : Ω ⊓ analytificationOpenImmersionPreimage (X.restrictι U) ≤ Ω))).op).hom)
  (hH₂ : ∀ Ω : (analytification.obj X).Opens, Function.Bijective (T₂.presheaf.map
    (homOfLE ((TopologicalSpace.Opens.map q₂.toLRSHom.base).monotone
      (inf_le_left : Ω ⊓ analytificationOpenImmersionPreimage (X.restrictι U) ≤ Ω))).op).hom)

/-- **The comparison of sections of `q₁_* 𝒪` and `q₂_* 𝒪` over any open `Ω` of `X^an`**: restrict
to `Ω ∩ U^an`, compare through the common local model and extend back, using that both have
Hartogs extension across the complement of `U^an`. -/
def compareEquiv (Ω : (analytification.obj X).Opens) :
    T₁.presheaf.obj (op ((TopologicalSpace.Opens.map q₁.toLRSHom.base).obj Ω)) ≃+*
      T₂.presheaf.obj (op ((TopologicalSpace.Opens.map q₂.toLRSHom.base).obj Ω)) :=
  (RingEquiv.ofBijective _ (hH₁ Ω)).trans ((compareEquiv₀ M₁ e₂ h₂
    (Ω ⊓ analytificationOpenImmersionPreimage (X.restrictι U)) inf_le_right).trans
      (RingEquiv.ofBijective _ (hH₂ Ω)).symm)

lemma res_compareEquiv (Ω : (analytification.obj X).Opens)
    (s : T₁.presheaf.obj (op ((TopologicalSpace.Opens.map q₁.toLRSHom.base).obj Ω))) :
    T₂.presheaf.map (homOfLE ((TopologicalSpace.Opens.map q₂.toLRSHom.base).monotone
      (inf_le_left : Ω ⊓ analytificationOpenImmersionPreimage (X.restrictι U) ≤ Ω))).op
        (compareEquiv M₁ e₂ h₂ hH₁ hH₂ Ω s) =
      compareEquiv₀ M₁ e₂ h₂ _ inf_le_right (T₁.presheaf.map
        (homOfLE ((TopologicalSpace.Opens.map q₁.toLRSHom.base).monotone
          (inf_le_left : Ω ⊓ analytificationOpenImmersionPreimage (X.restrictι U) ≤ Ω))).op s) :=
  (RingEquiv.ofBijective _ (hH₂ Ω)).apply_symm_apply _

/-- The comparison is compatible with the pullbacks from `X^an`. -/
lemma compareEquiv_c_app (Ω : (analytification.obj X).Opens)
    (s : (analytification.obj X).presheaf.obj (op Ω)) :
    compareEquiv M₁ e₂ h₂ hH₁ hH₂ Ω (q₁.toLRSHom.c.app (op Ω) s) = q₂.toLRSHom.c.app (op Ω) s := by
  refine (hH₂ Ω).1 ((res_compareEquiv M₁ e₂ h₂ hH₁ hH₂ Ω _).trans ?_)
  have n₁ := ConcreteCategory.congr_hom (q₁.toLRSHom.c.naturality
    (homOfLE (inf_le_left : Ω ⊓ analytificationOpenImmersionPreimage (X.restrictι U) ≤ Ω)).op) s
  have n₂ := ConcreteCategory.congr_hom (q₂.toLRSHom.c.naturality
    (homOfLE (inf_le_left : Ω ⊓ analytificationOpenImmersionPreimage (X.restrictι U) ≤ Ω)).op) s
  exact (congrArg _ n₁.symm).trans ((compareEquiv₀_c_app M₁ e₂ h₂ _ inf_le_right _).trans n₂)

/-- The comparison commutes with restriction. -/
lemma compareEquiv_res {Ω Ω' : (analytification.obj X).Opens} (h : Ω' ≤ Ω)
    (s : T₁.presheaf.obj (op ((TopologicalSpace.Opens.map q₁.toLRSHom.base).obj Ω))) :
    compareEquiv M₁ e₂ h₂ hH₁ hH₂ Ω' (T₁.presheaf.map
      (homOfLE ((TopologicalSpace.Opens.map q₁.toLRSHom.base).monotone h)).op s) =
      T₂.presheaf.map (homOfLE ((TopologicalSpace.Opens.map q₂.toLRSHom.base).monotone h)).op
        (compareEquiv M₁ e₂ h₂ hH₁ hH₂ Ω s) := by
  have hle : Ω' ⊓ analytificationOpenImmersionPreimage (X.restrictι U) ≤
      Ω ⊓ analytificationOpenImmersionPreimage (X.restrictι U) := inf_le_inf_right _ h
  refine (hH₂ Ω').1 ((res_compareEquiv M₁ e₂ h₂ hH₁ hH₂ Ω' _).trans ?_)
  refine (congrArg _ ((presheaf_map_map_apply T₁ _ _
    (homOfLE ((TopologicalSpace.Opens.map q₁.toLRSHom.base).monotone
      (inf_le_left.trans h : Ω' ⊓ analytificationOpenImmersionPreimage (X.restrictι U) ≤ Ω))).op
    s).trans (presheaf_map_map_apply T₁
      (homOfLE ((TopologicalSpace.Opens.map q₁.toLRSHom.base).monotone
        (inf_le_left : Ω ⊓ analytificationOpenImmersionPreimage (X.restrictι U) ≤ Ω))).op
      (homOfLE ((TopologicalSpace.Opens.map q₁.toLRSHom.base).monotone hle)).op _ s).symm)).trans
    ?_
  refine (compareEquiv₀_res M₁ e₂ h₂ hle inf_le_right _).trans ?_
  refine (congrArg _ (res_compareEquiv M₁ e₂ h₂ hH₁ hH₂ Ω s).symm).trans ?_
  exact (presheaf_map_map_apply T₂ _ _
    (homOfLE ((TopologicalSpace.Opens.map q₂.toLRSHom.base).monotone
      (inf_le_left.trans h : Ω' ⊓ analytificationOpenImmersionPreimage (X.restrictι U) ≤ Ω))).op
    _).trans (presheaf_map_map_apply T₂ _ _ _ _).symm

/-- **The comparison isomorphism** `q₁_* 𝒪_{T₁} ≅ q₂_* 𝒪_{T₂}` of presheaves of rings on `X^an`. -/
def compareIso : q₁.toLRSHom.base _* T₁.presheaf ≅ q₂.toLRSHom.base _* T₂.presheaf :=
  NatIso.ofComponents (fun Ω ↦ (compareEquiv M₁ e₂ h₂ hH₁ hH₂ Ω.unop).toCommRingCatIso)
    fun {_ Ω'} f ↦ CommRingCat.hom_ext (RingHom.ext fun s ↦
      (congrArg (compareEquiv M₁ e₂ h₂ hH₁ hH₂ Ω'.unop)
        (congrArg (fun k ↦ T₁.presheaf.map k s) (Subsingleton.elim _ _))).trans
      ((compareEquiv_res M₁ e₂ h₂ hH₁ hH₂ (leOfHom f.unop) s).trans
        (congrArg (fun k ↦ T₂.presheaf.map k _) (Subsingleton.elim _ _))))

lemma compareIso_hom_app (Ω : (analytification.obj X).Opens)
    (s : T₁.presheaf.obj (op ((TopologicalSpace.Opens.map q₁.toLRSHom.base).obj Ω))) :
    (compareIso M₁ e₂ h₂ hH₁ hH₂).hom.app (op Ω) s = compareEquiv M₁ e₂ h₂ hH₁ hH₂ Ω s :=
  rfl

/-- The comparison isomorphism is compatible with the pullbacks from `X^an`. -/
lemma c_comp_compareIso :
    q₁.toLRSHom.c ≫ (compareIso M₁ e₂ h₂ hH₁ hH₂).hom = q₂.toLRSHom.c := by
  ext Ω s
  exact compareEquiv_c_app M₁ e₂ h₂ hH₁ hH₂ Ω s

end Compare

/-! ### Transporting the stalk criterion along an isomorphism of pushforwards -/

section Transport

variable {V : SchemeLFTℂ.{u}} {T₁ T₂ : AnalyticSpace.{u}} (q₁ : T₁ ⟶ analytification.obj V)
  (q₂ : T₂ ⟶ analytification.obj V) {B : Type u} [CommRing B] [Algebra Γ(V.obj.left, ⊤) B]
  (φ₁ : B →+* T₁.presheaf.obj (op ⊤))
  (hφ₁ : ∀ a, φ₁ (algebraMap Γ(V.obj.left, ⊤) B a) = q₁.pullbackΓ (analytificationΓ V a))
  (Θ : q₁.toLRSHom.base _* T₁.presheaf ≅ q₂.toLRSHom.base _* T₂.presheaf)
  (hΘ : q₁.toLRSHom.c ≫ Θ.hom = q₂.toLRSHom.c) (φ₂ : B →+* T₂.presheaf.obj (op ⊤))
  (hφ₂' : ∀ b, φ₂ b = Θ.hom.app (op ⊤) (φ₁ b))
  (hφ₂ : ∀ a, φ₂ (algebraMap Γ(V.obj.left, ⊤) B a) = q₂.pullbackΓ (analytificationΓ V a))

include hΘ hφ₂' in
/-- `𝒪_{V^an,v} ⊗ B → (q₂)_* 𝒪` is `𝒪_{V^an,v} ⊗ B → (q₁)_* 𝒪` followed by the stalk of `Θ`. -/
lemma pushforwardStalkTensorMap_eq_comp (v : analytification.obj V)
    (x : (analytification.obj V).presheaf.stalk v ⊗[Γ(V.obj.left, ⊤)] B) :
    pushforwardStalkTensorMap q₂ φ₂ hφ₂ v x =
      (TopCat.Presheaf.stalkFunctor CommRingCat v).map Θ.hom
        (pushforwardStalkTensorMap q₁ φ₁ hφ₁ v x) := by
  induction x using TensorProduct.induction_on with
  | zero =>
    rw [map_zero, map_zero]
    exact (map_zero ((TopCat.Presheaf.stalkFunctor CommRingCat v).map Θ.hom).hom).symm
  | tmul s b =>
    rw [pushforwardStalkTensorMap_tmul, pushforwardStalkTensorMap_tmul]
    refine Eq.trans ?_
      (map_mul ((TopCat.Presheaf.stalkFunctor CommRingCat v).map Θ.hom).hom _ _).symm
    refine congrArg₂ (· * ·) ?_ ?_
    · change (TopCat.Presheaf.stalkFunctor CommRingCat v).map q₂.toLRSHom.c s =
        (TopCat.Presheaf.stalkFunctor CommRingCat v).map Θ.hom
          ((TopCat.Presheaf.stalkFunctor CommRingCat v).map q₁.toLRSHom.c s)
      rw [← hΘ, Functor.map_comp]
      rfl
    · rw [hφ₂']
      exact (TopCat.Presheaf.stalkFunctor_map_germ_apply _ _ _ _ _).symm
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy]
    exact (map_add ((TopCat.Presheaf.stalkFunctor CommRingCat v).map Θ.hom).hom _ _).symm

include hΘ hφ₂' in
/-- **The stalk criterion transports along an isomorphism of pushforwards.** -/
theorem bijective_pushforwardStalkTensorMap_of_iso (v : analytification.obj V)
    (hv : Function.Bijective (pushforwardStalkTensorMap q₁ φ₁ hφ₁ v)) :
    Function.Bijective (pushforwardStalkTensorMap q₂ φ₂ hφ₂ v) := by
  have h : ⇑(pushforwardStalkTensorMap q₂ φ₂ hφ₂ v) =
      (TopCat.Presheaf.stalkFunctor CommRingCat v).map Θ.hom ∘
        pushforwardStalkTensorMap q₁ φ₁ hφ₁ v :=
    funext (pushforwardStalkTensorMap_eq_comp q₁ q₂ φ₁ hφ₁ Θ hΘ φ₂ hφ₂' hφ₂ v)
  rw [h]
  exact (ConcreteCategory.bijective_of_isIso _).comp hv

end Transport

/-! ### Hartogs extension along local isomorphisms -/

section Sheet

variable {Z X' : AnalyticSpace.{u}} (q : Z ⟶ X') [IsLocalIso q]

/-- The image of an open under a local isomorphism, as an open. -/
def localIsoImage (W : Z.Opens) : X'.Opens :=
  ⟨q.toLRSHom.base '' W, IsLocalIso.isLocalHomeomorph.isOpenMap _ W.isOpen⟩

lemma le_preimage_localIsoImage (W : Z.Opens) :
    W ≤ (TopologicalSpace.Opens.map q.toLRSHom.base).obj (localIsoImage q W) :=
  fun x hx ↦ ⟨x, hx, rfl⟩

/-- Pulling back sections over `q(W)` to `W`. -/
def localIsoSheetMap (W : Z.Opens) :
    X'.presheaf.obj (op (localIsoImage q W)) ⟶ Z.presheaf.obj (op W) :=
  q.toLRSHom.c.app (op (localIsoImage q W)) ≫
    Z.presheaf.map (homOfLE (le_preimage_localIsoImage q W)).op

/-- **Sheets of a local isomorphism**: every point of an open `Ω` has a neighbourhood `N ⊆ Ω` such
that for every open `W ⊆ N`, pulling back sections over `q(W)` to `W` is bijective. -/
theorem exists_sheet_of_isLocalIso (z : Z) (Ω : Z.Opens) (hz : z ∈ Ω) :
    ∃ N : Z.Opens, N ≤ Ω ∧ z ∈ N ∧ ∀ W ≤ N, Function.Bijective (localIsoSheetMap q W).hom := by
  obtain ⟨e, hze, he⟩ := IsLocalIso.isLocalHomeomorph (f := q) z
  let N : Z.Opens := ⟨e.source ∩ Ω, e.open_source.inter Ω.isOpen⟩
  have hinjN : Set.InjOn q.toLRSHom.base (N : Set Z) := fun x hx y hy hxy ↦ by
    rw [he] at hxy
    exact e.injOn hx.1 hy.1 hxy
  refine ⟨N, fun _ h ↦ h.2, ⟨hze, hz⟩, fun W hW ↦ ?_⟩
  let j := Z.ofRestrict N ≫ q
  have hjinj : Function.Injective j.toLRSHom.base := fun x y hxy ↦
    Subtype.ext (hinjN x.2 y.2 hxy)
  haveI : LocallyRingedSpace.IsOpenImmersion j.toLRSHom :=
    LocallyRingedSpace.IsOpenImmersion.of_stalk_iso _
      ((IsLocalIso.isLocalHomeomorph (f := j)).isOpenEmbedding_of_injective hjinj)
  -- the image of the preimage of `q(W)` in `N` is `W`
  set V := localIsoImage q W
  have hWeq : N.isOpenEmbedding.isOpenMap.functor.obj
      ((TopologicalSpace.Opens.map (Z.ofRestrict N).toLRSHom.base).obj
        ((TopologicalSpace.Opens.map q.toLRSHom.base).obj V)) = W := by
    ext x
    constructor
    · rintro ⟨y, ⟨w, hw, hwy⟩, rfl⟩
      have hwy' : w = y.1 := hinjN (hW hw) y.2 hwy
      change y.1 ∈ W
      rw [← hwy']
      exact hw
    · intro hx
      exact ⟨⟨x, hW hx⟩, ⟨x, hx, rfl⟩, rfl⟩
  haveI : IsIso (j.toLRSHom.c.app (op V)) := by
    refine PresheafedSpace.IsOpenImmersion.c_iso' (f := j.toLRSHom.toHom)
      ((TopologicalSpace.Opens.map j.toLRSHom.base).obj V) ?_
    ext y
    refine ⟨fun hy ↦ ?_, ?_⟩
    · obtain ⟨w, hw, rfl⟩ := hy
      exact ⟨⟨w, hW hw⟩, ⟨w, hw, rfl⟩, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact hx
  have hc : localIsoSheetMap q W =
      j.toLRSHom.c.app (op V) ≫ Z.presheaf.map (homOfLE hWeq.ge).op := by
    change _ ≫ _ = (q.toLRSHom.c.app (op V) ≫ Z.presheaf.map _) ≫ _
    exact (congrArg (fun φ ↦ q.toLRSHom.c.app (op V) ≫ φ)
      ((congrArg _ (Subsingleton.elim _ _)).trans (Z.presheaf.map_comp _ _))).trans
        (Category.assoc _ _ _).symm
  have h2 : Function.Bijective (Z.presheaf.map (homOfLE hWeq.ge).op).hom := by
    rw [show homOfLE hWeq.ge = eqToHom hWeq.symm from Subsingleton.elim _ _]
    exact ConcreteCategory.bijective_of_isIso _
  rw [hc]
  exact h2.comp (ConcreteCategory.bijective_of_isIso (j.toLRSHom.c.app (op V)))

lemma localIsoImage_mono {W W' : Z.Opens} (h : W' ≤ W) : localIsoImage q W' ≤ localIsoImage q W :=
  Set.image_mono h

/-- Pulling back sections along a local isomorphism commutes with restriction. -/
lemma localIsoSheetMap_res {W W' : Z.Opens} (h : W' ≤ W)
    (t : X'.presheaf.obj (op (localIsoImage q W))) :
    localIsoSheetMap q W' (X'.res (localIsoImage_mono q h) t) =
      Z.res h (localIsoSheetMap q W t) := by
  have n := ConcreteCategory.congr_hom (q.toLRSHom.c.naturality
    (homOfLE (localIsoImage_mono q h)).op) t
  refine (congrArg (Z.presheaf.map (homOfLE (le_preimage_localIsoImage q W')).op) n).trans ?_
  exact (presheaf_map_map_apply Z _ _
    (homOfLE (h.trans (le_preimage_localIsoImage q W))).op _).trans
    (presheaf_map_map_apply Z _ _ _ _).symm

variable (O : X'.Opens)
  (hH : ∀ Ω : X'.Opens, Function.Bijective (X'.res (inf_le_left : Ω ⊓ O ≤ Ω)))

include hH in
/-- **Hartogs extension transfers along local isomorphisms: injectivity.** -/
theorem injective_res_of_isLocalIso (Ω : Z.Opens) :
    Function.Injective (Z.res (inf_le_left :
      Ω ⊓ (TopologicalSpace.Opens.map q.toLRSHom.base).obj O ≤ Ω)) := by
  intro s t hst
  refine LocallyRingedSpace.res_eq_of_locally fun z hz ↦ ?_
  obtain ⟨N, hNΩ, hzN, hN⟩ := exists_sheet_of_isLocalIso q z Ω hz
  refine ⟨N, hNΩ, hzN, ?_⟩
  obtain ⟨a, ha⟩ := (hN N le_rfl).2 (Z.res hNΩ s)
  obtain ⟨b, hb⟩ := (hN N le_rfl).2 (Z.res hNΩ t)
  set O' := (TopologicalSpace.Opens.map q.toLRSHom.base).obj O
  have hW' : N ⊓ O' ≤ N := inf_le_left
  -- `a` and `b` agree over `q(N ⊓ q⁻¹ O)`
  have hab : X'.res (localIsoImage_mono q hW') a = X'.res (localIsoImage_mono q hW') b := by
    refine (hN _ hW').1 ((localIsoSheetMap_res q hW' a).trans ((congrArg _ ha).trans ?_))
    refine Eq.trans ?_ ((localIsoSheetMap_res q hW' b).trans (congrArg _ hb)).symm
    refine (LocallyRingedSpace.res_res _ _ _ _).trans ?_
    refine Eq.trans ?_ (LocallyRingedSpace.res_res _ _ _ _).symm
    have hle : N ⊓ O' ≤ Ω ⊓ O' := inf_le_inf_right _ hNΩ
    refine (LocallyRingedSpace.res_res _ hle inf_le_left s).symm.trans ?_
    exact (congrArg (Z.res hle) hst).trans (LocallyRingedSpace.res_res _ hle inf_le_left t)
  have hle : localIsoImage q N ⊓ O ≤ localIsoImage q (N ⊓ O') := by
    rintro _ ⟨⟨x, hx, rfl⟩, hxO⟩
    exact ⟨x, ⟨hx, hxO⟩, rfl⟩
  have hab' : X'.res (inf_le_left : localIsoImage q N ⊓ O ≤ localIsoImage q N) a =
      X'.res (inf_le_left : localIsoImage q N ⊓ O ≤ localIsoImage q N) b :=
    (LocallyRingedSpace.res_res _ hle _ a).symm.trans ((congrArg (X'.res hle) hab).trans
      (LocallyRingedSpace.res_res _ hle _ b))
  rw [← ha, ← hb, (hH (localIsoImage q N)).1 hab']

include hH in
/-- **Hartogs extension transfers along local isomorphisms.** If restriction
`𝒪(Ω) → 𝒪(Ω ∩ O)` is bijective for every open `Ω` of `X'`, then for a local isomorphism
`q : Z ⟶ X'` restriction `𝒪(Ω) → 𝒪(Ω ∩ q⁻¹ O)` is bijective for every open `Ω` of `Z`. -/
theorem bijective_res_of_isLocalIso (Ω : Z.Opens) :
    Function.Bijective (Z.res (inf_le_left :
      Ω ⊓ (TopologicalSpace.Opens.map q.toLRSHom.base).obj O ≤ Ω)) := by
  set O' := (TopologicalSpace.Opens.map q.toLRSHom.base).obj O
  refine ⟨injective_res_of_isLocalIso q O hH Ω, fun s ↦ ?_⟩
  -- local extensions
  have hloc : ∀ z ∈ Ω, ∃ (N : Z.Opens) (hNΩ : N ≤ Ω), z ∈ N ∧ ∃ u : Z.presheaf.obj (op N),
      Z.res (inf_le_left : N ⊓ O' ≤ N) u = Z.res (inf_le_inf_right O' hNΩ) s := by
    intro z hz
    obtain ⟨N, hNΩ, hzN, hN⟩ := exists_sheet_of_isLocalIso q z Ω hz
    have hW' : N ⊓ O' ≤ N := inf_le_left
    obtain ⟨a₀, ha₀⟩ := (hN _ hW').2 (Z.res (inf_le_inf_right O' hNΩ) s)
    have hle₁ : localIsoImage q N ⊓ O ≤ localIsoImage q (N ⊓ O') := by
      rintro _ ⟨⟨x, hx, rfl⟩, hxO⟩
      exact ⟨x, ⟨hx, hxO⟩, rfl⟩
    have hle₂ : localIsoImage q (N ⊓ O') ≤ localIsoImage q N ⊓ O := by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx.1, rfl⟩, hx.2⟩
    obtain ⟨a, ha⟩ := (hH (localIsoImage q N)).2 (X'.res hle₁ a₀)
    refine ⟨N, hNΩ, hzN, localIsoSheetMap q N a, ?_⟩
    refine (localIsoSheetMap_res q hW' a).symm.trans (Eq.trans ?_ ha₀)
    congr 1
    refine (LocallyRingedSpace.res_res _ hle₂ inf_le_left a).symm.trans ?_
    refine (congrArg (X'.res hle₂) ha).trans ((LocallyRingedSpace.res_res _ hle₂ hle₁ a₀).trans ?_)
    exact LocallyRingedSpace.res_self _ _
  choose N hNΩ hzN u hu using hloc
  -- the local extensions agree on overlaps
  obtain ⟨t, ht⟩ := LocallyRingedSpace.exists_sectRes_eq_of_locally
    (SheafOfModules.unit Z.ringSheaf) N hNΩ hzN u fun y hy y' hy' ↦ by
      refine injective_res_of_isLocalIso q O hH (N y hy ⊓ N y' hy') ?_
      refine (LocallyRingedSpace.res_res _ _ _ _).trans
        (Eq.trans ?_ (LocallyRingedSpace.res_res _ _ _ _).symm)
      have h₁ : N y hy ⊓ N y' hy' ⊓ O' ≤ N y hy ⊓ O' := inf_le_inf_right _ inf_le_left
      have h₂ : N y hy ⊓ N y' hy' ⊓ O' ≤ N y' hy' ⊓ O' := inf_le_inf_right _ inf_le_right
      refine (LocallyRingedSpace.res_res _ h₁ inf_le_left _).symm.trans ?_
      refine Eq.trans ?_ (LocallyRingedSpace.res_res _ h₂ inf_le_left _)
      rw [hu, hu, LocallyRingedSpace.res_res, LocallyRingedSpace.res_res]
  refine ⟨t, LocallyRingedSpace.res_eq_of_locally fun y hy ↦ ?_⟩
  refine ⟨N y hy.1 ⊓ O', inf_le_inf_right O' (hNΩ y hy.1), ⟨hzN y hy.1, hy.2⟩, ?_⟩
  refine (LocallyRingedSpace.res_res _ _ _ _).trans ?_
  have h₁ : N y hy.1 ⊓ O' ≤ N y hy.1 := inf_le_left
  refine (LocallyRingedSpace.res_res _ h₁ (hNΩ y hy.1) t).symm.trans ?_
  change Z.res h₁ (LocallyRingedSpace.sectRes (SheafOfModules.unit Z.ringSheaf) (hNΩ y hy.1) t) = _
  rw [ht, hu]
  rfl
end Sheet

/-! ### Hartogs extension and normalisation -/

section Main

/-- The complement of the open `U` of a scheme has **codimension at least two**: the local ring
at every point outside `U` has dimension at least two. -/
def HasCodimTwoComplement {Y : Scheme.{u}} (U : Y.Opens) : Prop :=
  ∀ y : Y, y ∉ U → 2 ≤ ringKrullDim (Y.presheaf.stalk y)

/-- **Hartogs extension on normal affine schemes** (not proved here). Let `X` be an affine scheme
of finite type over `ℂ` whose ring of functions is a finite product of normal domains and `U ⊆ X`
an open whose complement has codimension at least two. Then for every open `Ω ⊆ X^an`,
restriction `𝒪_{X^an}(Ω) → 𝒪_{X^an}(Ω ∩ U^an)` is bijective. -/
def NormalHartogs : Prop :=
  ∀ (X : SchemeLFTℂ.{u}) [IsAffine X.obj.left], IsFiniteProductOfNormalDomains Γ(X.obj.left, ⊤) →
    ∀ U : X.obj.left.Opens, HasCodimTwoComplement U →
    ∀ Ω : (analytification.obj X).Opens, Function.Bijective ((analytification.obj X).res
      (inf_le_left : Ω ⊓ analytificationOpenImmersionPreimage (X.restrictι U) ≤ Ω))

/-- **Normalisation in a finite étale cover of an open** (not proved here). Let `X` be an affine
scheme of finite type over `ℂ` whose ring of functions is a finite product of normal domains,
`U ⊆ X` an open whose complement has codimension at least two and `p : Y ⟶ U` finite étale.
Then there is a finite morphism `q : Y' ⟶ X` from an affine scheme `Y'` whose ring of functions is
a finite product of normal domains, such that `q⁻¹ U` has complement of codimension at least two
and `Y ≅ q⁻¹ U` over `U` (the normalisation of `X` in `Y`). -/
def NormalizationInCover : Prop :=
  ∀ (X : SchemeLFTℂ.{u}) [IsAffine X.obj.left], IsFiniteProductOfNormalDomains Γ(X.obj.left, ⊤) →
    ∀ U : X.obj.left.Opens, HasCodimTwoComplement U →
    ∀ (Y : SchemeLFTℂ.{u}) (p : Y ⟶ X.restrict U), SchemeLFTℂ.isFiniteEtale p →
    ∃ (Yn : SchemeLFTℂ.{u}) (q : Yn ⟶ X) (e : Y ⟶ Yn), IsAffine Yn.obj.left ∧
      AlgebraicGeometry.IsFinite q.hom.left ∧ IsFiniteProductOfNormalDomains Γ(Yn.obj.left, ⊤) ∧
      HasCodimTwoComplement (q.hom.left ⁻¹ᵁ U) ∧
      IsPullback e.hom.left p.hom.left q.hom.left (X.restrictι U).hom.left

/-- A point lies in the range of the inclusion of an open exactly if it lies in the open. -/
lemma mem_range_opens_ι_base {S : Scheme.{u}} (V : S.Opens) (z : S) :
    z ∈ Set.range V.ι.base ↔ z ∈ V := by
  rw [Scheme.Opens.range_ι]
  rfl

/-- The analytification of `q⁻¹ U` is the preimage of the analytification of `U`. -/
lemma analytificationOpenImmersionPreimage_restrictι_preimage {Y X : SchemeLFTℂ.{u}} (q : Y ⟶ X)
    (U : X.obj.left.Opens) :
    analytificationOpenImmersionPreimage (Y.restrictι (q.hom.left ⁻¹ᵁ U)) =
      (TopologicalSpace.Opens.map (analytification.map q).toLRSHom.base).obj
        (analytificationOpenImmersionPreimage (X.restrictι U)) := by
  ext y
  have hy : (analytificationπLRS X).base ((analytification.map q).toLRSHom.base y) =
      q.hom.left.base ((analytificationπLRS Y).base y) :=
    congrArg (fun f ↦ f.base y) (analytificationπLRS_naturality q)
  change (analytificationπLRS Y).base y ∈ Set.range (q.hom.left ⁻¹ᵁ U).ι.base ↔
    (analytificationπLRS X).base ((analytification.map q).toLRSHom.base y) ∈ Set.range U.ι.base
  rw [mem_range_opens_ι_base, mem_range_opens_ι_base, hy]
  rfl

/-- A restriction map is bijective if one along an equal open is. -/
lemma bijective_presheaf_map_of_eq (Z : AnalyticSpace.{u}) {Ω V₁ V₂ : Z.Opens} (h : V₁ = V₂)
    (h₁ : V₁ ≤ Ω) (h₂ : V₂ ≤ Ω) (hb : Function.Bijective (Z.presheaf.map (homOfLE h₁).op).hom) :
    Function.Bijective (Z.presheaf.map (homOfLE h₂).op).hom := by
  subst h
  exact hb

/-- **Essential surjectivity from a big open of a normal affine scheme.** Let `X` be an affine
scheme of finite type over `ℂ` whose ring of functions is a finite product of normal domains and
`U ⊆ X` an open whose complement has codimension at least two (e.g. the smooth locus). Assume
`NormalHartogs` and `NormalizationInCover`. If the restriction of a Hausdorff finite étale cover
`W` of `X^an` to `U^an` is the analytification of a finite étale cover of `U`, then `W` is the
analytification of a finite étale cover of `X`. -/
theorem mem_essImage_of_restrict (hH : NormalHartogs.{u}) (hN : NormalizationInCover.{u})
    (X : SchemeLFTℂ.{u}) [IsAffine X.obj.left]
    (hX : IsFiniteProductOfNormalDomains Γ(X.obj.left, ⊤))
    (U : X.obj.left.Opens) (hU : HasCodimTwoComplement U)
    (W : AnalyticSpace.FiniteEtaleOver (analytification.obj X)) [T2Space W.left]
    (hW : (analytificationFiniteEtaleOver (X.restrict U)).essImage (restrictFiniteEtaleOver W U)) :
    (analytificationFiniteEtaleOver X).essImage W := by
  haveI : IsFiniteEtale W.hom := W.prop
  obtain ⟨M⟩ := nonempty_localModel_of_mem_essImage W U hW
  obtain ⟨Yn, q, e, hYn, hq, hnorm, hcodim, hpb⟩ := hN X hX U hU M.Y M.p M.isFiniteEtale_p
  haveI := hYn
  haveI := hq
  haveI := t2Space_analytification_of_isAffine Yn
  haveI : AnalyticSpace.IsFinite (analytification.map q) :=
    isFinite_analytification_map_of_isFinite q
  -- the local model of `q^an` over `U`
  let Mq : LocalModel (analytification.map q) U :=
    ⟨M.Y, M.p, M.isFiniteEtale_p, analytification.map e,
      isPullback_analytification_map_of_isPullback hpb⟩
  -- Hartogs extension for `q^an_* 𝒪` and `p_* 𝒪_W`
  set Ua := analytificationOpenImmersionPreimage (X.restrictι U)
  have hH₁ : ∀ Ω : (analytification.obj X).Opens, Function.Bijective
      ((analytification.obj Yn).presheaf.map (homOfLE
        ((TopologicalSpace.Opens.map (analytification.map q).toLRSHom.base).monotone
          (inf_le_left : Ω ⊓ Ua ≤ Ω))).op).hom := by
    intro Ω
    refine bijective_presheaf_map_of_eq _ ?_ _ _ (hH Yn hnorm _ hcodim
      ((TopologicalSpace.Opens.map (analytification.map q).toLRSHom.base).obj Ω))
    rw [analytificationOpenImmersionPreimage_restrictι_preimage]
    ext y
    exact Iff.rfl
  haveI : IsLocalIso W.hom := IsFiniteEtale.isLocalIso (self := W.prop)
  have hH₂ : ∀ Ω : (analytification.obj X).Opens, Function.Bijective
      (W.left.presheaf.map (homOfLE ((TopologicalSpace.Opens.map W.hom.toLRSHom.base).monotone
          (inf_le_left : Ω ⊓ Ua ≤ Ω))).op).hom := by
    intro Ω
    refine bijective_presheaf_map_of_eq _ ?_ _ _ (bijective_res_of_isLocalIso W.hom Ua
      (hH X hX U hU) ((TopologicalSpace.Opens.map W.hom.toLRSHom.base).obj Ω))
    ext y
    exact Iff.rfl
  let Θ := compareIso Mq M.e M.isPullback hH₁ hH₂
  -- the algebra of functions on `Yn`
  letI := q.hom.left.appTop.hom.toAlgebra
  haveI : Module.Finite Γ(X.obj.left, ⊤) Γ(Yn.obj.left, ⊤) := q.hom.left.finite_appTop
  have hφ₁ : ∀ a, analytificationΓ Yn (algebraMap Γ(X.obj.left, ⊤) Γ(Yn.obj.left, ⊤) a) =
      (analytification.map q).pullbackΓ (analytificationΓ X a) :=
    analytificationΓ_naturality q
  let φ : Γ(Yn.obj.left, ⊤) →+* W.left.presheaf.obj (op ⊤) :=
    (Θ.hom.app (op ⊤)).hom.comp (analytificationΓ Yn)
  have hφ : ∀ a, φ (algebraMap Γ(X.obj.left, ⊤) Γ(Yn.obj.left, ⊤) a) =
      W.hom.pullbackΓ (analytificationΓ X a) := fun a ↦ by
    change Θ.hom.app (op ⊤) (analytificationΓ Yn _) = _
    rw [hφ₁]
    exact ConcreteCategory.congr_hom (congrArg (fun f ↦ f.app (op ⊤))
      (c_comp_compareIso Mq M.e M.isPullback hH₁ hH₂)) _
  -- the stalk criterion for `Yn`, transported to `W`
  have hbij : ∀ v, Function.Bijective (pushforwardStalkTensorMap W.hom φ hφ v) := by
    intro v
    refine bijective_pushforwardStalkTensorMap_of_iso _ _ _ hφ₁ Θ
      (c_comp_compareIso Mq M.e M.isPullback hH₁ hH₂) φ (fun _ ↦ rfl) hφ v ?_
    have hs := finiteAnalyticSplitting.{u} Yn X q v
    have h : ⇑(stalkTensorMap (analytification.map q) (analytificationΓ Yn) hφ₁ v) =
        TopCat.Presheaf.pushforwardStalkToPi (analytification.map q).toLRSHom.base
          (analytification.obj Yn).presheaf v ∘
        pushforwardStalkTensorMap (analytification.map q) (analytificationΓ Yn) hφ₁ v :=
      funext fun x ↦ (pushforwardStalkToPi_pushforwardStalkTensorMap _ _ _ v x).symm
    rw [← Function.Bijective.of_comp_iff'
      (bijective_pushforwardStalkToPi (analytification.map q) v),
      ← h]
    exact hs
  obtain ⟨h, ⟨i⟩⟩ := exists_iso_of_bijective_pushforwardStalkTensorMap X W Γ(Yn.obj.left, ⊤) φ hφ
    hbij
  exact ⟨_, ⟨i⟩⟩

end Main

end

end ComplexAnalytic
