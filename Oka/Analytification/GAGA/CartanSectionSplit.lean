/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytic.OkaRingDifferentiable
import Oka.Analytification.GAGA.CartanBundle
import Mathlib.Geometry.RingedSpace.OpenImmersion
import Oka.ComplexSpace

/-!
# Cartan's matrix lemma for sections over an open subspace of `ℂ^ι`

Let `f : Y ⟶ ℂ^ι` be an open immersion of locally ringed spaces. Sections of `𝒪_Y` over an open
`W` are holomorphic functions on `f(W)`; we evaluate them at points of `f(W)` by the ring
homomorphism `ComplexAnalytic.secEval`. Matrices of sections are equal if they are equal at every
point (`ComplexAnalytic.matrix_ext_secEval`), and holomorphic matrix-valued functions give
matrices of sections (`ComplexAnalytic.exists_matrix_secEval_eq`).

The main result is Cartan's matrix lemma in this language: for compact sets `K₁`, `K₂` with the
splitting property `Complex.MatrixSplit` (e.g. adjacent closed boxes), an invertible matrix `G` of
sections near `K₁ ∩ K₂` splits as `G = H₁ H₂` with `Hᵢ` invertible near `Kᵢ`
(`ComplexAnalytic.exists_matrix_split_sections`).
-/

universe u

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry Set

namespace Complex

variable {ι : Type*} [Finite ι]

open scoped Matrix.Norms.Operator in
/-- The compact sets `K₁`, `K₂ ⊆ ℂ^ι` have **Cartan's splitting property** for `κ × κ`-matrices:
every holomorphic invertible matrix `g` on `V₁ ∩ V₂`, for open `V₁ ⊇ K₁` and `V₂ ⊇ K₂`, splits as
`g = h₁ h₂` on `V₁' ∩ V₂'` with `hᵢ` holomorphic and invertible on open `Vᵢ'` between `Kᵢ` and
`Vᵢ`. -/
def MatrixSplit (κ : Type*) [Fintype κ] [DecidableEq κ] (K₁ K₂ : Set (ι → ℂ)) : Prop :=
  ∀ V₁ V₂ : Set (ι → ℂ), IsOpen V₁ → IsOpen V₂ → K₁ ⊆ V₁ → K₂ ⊆ V₂ →
    ∀ g : (ι → ℂ) → Matrix κ κ ℂ, DifferentiableOn ℂ g (V₁ ∩ V₂) →
      (∀ x ∈ V₁ ∩ V₂, IsUnit (g x)) →
      ∃ V₁' V₂' : Set (ι → ℂ), IsOpen V₁' ∧ IsOpen V₂' ∧ K₁ ⊆ V₁' ∧ K₂ ⊆ V₂' ∧ V₁' ⊆ V₁ ∧
        V₂' ⊆ V₂ ∧ ∃ h₁ h₂ : (ι → ℂ) → Matrix κ κ ℂ, DifferentiableOn ℂ h₁ V₁' ∧
          (∀ x ∈ V₁', IsUnit (h₁ x)) ∧ DifferentiableOn ℂ h₂ V₂' ∧ (∀ x ∈ V₂', IsUnit (h₂ x)) ∧
          ∀ x ∈ V₁' ∩ V₂', g x = h₁ x * h₂ x

end Complex

namespace Complex

variable {ι : Type*} [Finite ι] [DecidableEq ι] {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- Boxes adjacent in the real direction have Cartan's splitting property. -/
theorem matrixSplit_re (i : ι) {a b : ι → ℂ} (hre : (a i).re ≤ (b i).re)
    (him : (a i).im ≤ (b i).im) {x₀ x₁ : ℝ} (hx₀ : x₀ ≤ (a i).re) (hx₁ : (b i).re ≤ x₁) :
    MatrixSplit κ (closedBox (Function.update a i ⟨x₀, (a i).im⟩) b)
      (closedBox a (Function.update b i ⟨x₁, (b i).im⟩)) := by
  intro V₁ V₂ hV₁ hV₂ hK₁ hK₂ g hg hgu
  cases isEmpty_or_nonempty κ
  · exact ⟨V₁, V₂, hV₁, hV₂, hK₁, hK₂, subset_rfl, subset_rfl, 1, 1, differentiableOn_const 1,
      fun _ _ ↦ isUnit_one, differentiableOn_const 1, fun _ _ ↦ isUnit_one,
      fun _ _ ↦ Subsingleton.elim _ _⟩
  open scoped Matrix.Norms.Operator in
  exact exists_mul_split_closedBox_of_isOpen (𝔸 := Matrix κ κ ℂ) i hre him hx₀ hx₁ hV₁ hV₂ hK₁
    hK₂ hg hgu

/-- Boxes adjacent in the imaginary direction have Cartan's splitting property. -/
theorem matrixSplit_im (i : ι) {a b : ι → ℂ} (hre : (a i).re ≤ (b i).re)
    (him : (a i).im ≤ (b i).im) {y₀ y₁ : ℝ} (hy₀ : y₀ ≤ (a i).im) (hy₁ : (b i).im ≤ y₁) :
    MatrixSplit κ (closedBox (Function.update a i ⟨(a i).re, y₀⟩) b)
      (closedBox a (Function.update b i ⟨(b i).re, y₁⟩)) := by
  intro V₁ V₂ hV₁ hV₂ hK₁ hK₂ g hg hgu
  cases isEmpty_or_nonempty κ
  · exact ⟨V₁, V₂, hV₁, hV₂, hK₁, hK₂, subset_rfl, subset_rfl, 1, 1, differentiableOn_const 1,
      fun _ _ ↦ isUnit_one, differentiableOn_const 1, fun _ _ ↦ isUnit_one,
      fun _ _ ↦ Subsingleton.elim _ _⟩
  open scoped Matrix.Norms.Operator in
  exact exists_mul_split_closedBox_of_isOpen_im (𝔸 := Matrix κ κ ℂ) i hre him hy₀ hy₁ hV₁ hV₂
    hK₁ hK₂ hg hgu

section MatrixDiff

variable {κ : Type*} [Finite κ]

open scoped Matrix.Norms.Operator

omit [DecidableEq ι] in
lemma differentiableOn_matrix_of {s : Set (ι → ℂ)} {φ : κ → κ → (ι → ℂ) → ℂ}
    (h : ∀ k l, DifferentiableOn ℂ (φ k l) s) :
    DifferentiableOn ℂ (fun x ↦ Matrix.of fun k l ↦ φ k l x) s := by
  classical
  cases nonempty_fintype κ
  cases nonempty_fintype ι
  have e : (fun x ↦ Matrix.of fun k l ↦ φ k l x) =
      fun x ↦ ∑ k, ∑ l, φ k l x • Matrix.single k l (1 : ℂ) := by
    funext x
    ext k l
    simp [Matrix.sum_apply, Matrix.single_apply, ite_and]
  rw [e]
  exact DifferentiableOn.fun_sum fun k _ ↦ DifferentiableOn.fun_sum fun l _ ↦
    (h k l).smul_const _

omit [DecidableEq ι] in
lemma DifferentiableOn.matrix_apply {s : Set (ι → ℂ)} {g : (ι → ℂ) → Matrix κ κ ℂ}
    (hg : DifferentiableOn ℂ g s) (k l : κ) : DifferentiableOn ℂ (fun x ↦ g x k l) s := by
  cases nonempty_fintype κ
  cases nonempty_fintype ι
  exact (LinearMap.toContinuousLinearMap
    (Matrix.entryLinearMap ℂ ℂ k l)).differentiable.comp_differentiableOn hg

end MatrixDiff

end Complex

namespace ComplexAnalytic

variable {ι : Type u} [Fintype ι] {Y : LocallyRingedSpace.{u}} (f : Y ⟶ complexSpace ι)
  [LocallyRingedSpace.IsOpenImmersion f]

/-- The image of an open of `Y` under the open immersion `f : Y ⟶ ℂ^ι`. -/
noncomputable abbrev imageOpens (W : Opens Y.toPresheafedSpace) : Opens (ι → ℂ) :=
  (LocallyRingedSpace.IsOpenImmersion.opensFunctor f).obj W

/-- A section of `𝒪_Y` over `W`, as a holomorphic function on `f(W)`. -/
noncomputable def secOka {W : Opens Y.toPresheafedSpace} :
    Y.presheaf.obj (op W) →+* OkaRing (imageOpens f W) :=
  (LocallyRingedSpace.IsOpenImmersion.invApp f W).hom

/-- The value of a section of `𝒪_Y` over `W` at a point of `f(W)`. -/
noncomputable def secEval {W : Opens Y.toPresheafedSpace} {x : ι → ℂ} (hx : x ∈ imageOpens f W) :
    Y.presheaf.obj (op W) →+* ℂ :=
  (OkaRing.evalHom hx).comp (secOka f)

variable {f}

lemma secEval_apply {W : Opens Y.toPresheafedSpace} {x : ι → ℂ} (hx : x ∈ imageOpens f W)
    (r : Y.presheaf.obj (op W)) : secEval f hx r = OkaRing.evalHom hx (secOka f r) :=
  rfl

/-- Values of sections are compatible with restriction. -/
lemma secEval_map {W W' : Opens Y.toPresheafedSpace} (h : W' ≤ W) {x : ι → ℂ}
    (hx : x ∈ imageOpens f W')
    (r : Y.presheaf.obj (op W)) :
    secEval f hx (Y.presheaf.map (homOfLE h).op r) =
      secEval f ((LocallyRingedSpace.IsOpenImmersion.opensFunctor f).monotone h hx) r := by
  have e := congrArg (fun φ ↦ φ.hom r)
    (LocallyRingedSpace.IsOpenImmersion.inv_naturality f (homOfLE h).op)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  rw [secEval_apply, secEval_apply, secOka]
  erw [e]
  rfl

/-- Sections of `𝒪_Y` are determined by their values. -/
lemma sec_ext {W : Opens Y.toPresheafedSpace} {r r' : Y.presheaf.obj (op W)}
    (h : ∀ x (hx : x ∈ imageOpens f W), secEval f hx r = secEval f hx r') : r = r' := by
  have hinj : Function.Injective (secOka f (W := W)) :=
    (ConcreteCategory.bijective_of_isIso (LocallyRingedSpace.IsOpenImmersion.invApp f W)).1
  refine hinj (OkaRing.ext (funext fun x ↦ ?_))
  exact h x.1 x.2

/-- Holomorphic functions on `f(W)` are sections of `𝒪_Y` over `W`. -/
lemma exists_secEval_eq {W : Opens Y.toPresheafedSpace} (g : (ι → ℂ) → ℂ)
    (hg : DifferentiableOn ℂ g (imageOpens f W)) :
    ∃ r : Y.presheaf.obj (op W), ∀ x (hx : x ∈ imageOpens f W), secEval f hx r = g x := by
  have hsurj : Function.Surjective (secOka f (W := W)) :=
    (ConcreteCategory.bijective_of_isIso (LocallyRingedSpace.IsOpenImmersion.invApp f W)).2
  obtain ⟨r, hr⟩ := hsurj (OkaRing.ofDifferentiableOn g hg)
  exact ⟨r, fun x hx ↦ by rw [secEval_apply, hr]; rfl⟩

/-- Sections of `𝒪_Y` are holomorphic on `f(W)`. -/
lemma differentiableOn_secEval {W : Opens Y.toPresheafedSpace} (r : Y.presheaf.obj (op W)) :
    ∃ g : (ι → ℂ) → ℂ, DifferentiableOn ℂ g (imageOpens f W) ∧
      ∀ x (hx : x ∈ imageOpens f W), secEval f hx r = g x :=
  ⟨OkaRing.toGlobalFun _ (secOka f r), OkaRing.differentiableOn_toGlobalFun _,
    fun _ hx ↦ (OkaRing.toGlobalFun_apply _ hx).symm⟩

section Matrix

variable {κ κ' : Type*}

lemma isOpenEmbedding_base : Topology.IsOpenEmbedding f.base :=
  PresheafedSpace.IsOpenImmersion.base_open (f := f.toHom)

/-- Matrices of sections of `𝒪_Y` are determined by their values. -/
lemma matrix_ext_secEval {W : Opens Y.toPresheafedSpace}
    {H H' : Matrix κ κ' (Y.presheaf.obj (op W))}
    (h : ∀ x (hx : x ∈ imageOpens f W),
      H.map (secEval f hx) = H'.map (secEval f hx)) : H = H' :=
  Matrix.ext fun k l ↦ sec_ext fun x hx ↦ congrFun (congrFun (h x hx) k) l

/-- Matrices of holomorphic functions on `f(W)` are matrices of sections of `𝒪_Y` over `W`. -/
lemma exists_matrix_secEval_eq {W : Opens Y.toPresheafedSpace} (g : (ι → ℂ) → Matrix κ κ' ℂ)
    (hg : ∀ k l, DifferentiableOn ℂ (fun x ↦ g x k l) (imageOpens f W)) :
    ∃ H : Matrix κ κ' (Y.presheaf.obj (op W)),
      ∀ x (hx : x ∈ imageOpens f W), H.map (secEval f hx) = g x := by
  choose H hH using fun k l ↦ exists_secEval_eq (f := f) _ (hg k l)
  exact ⟨Matrix.of H, fun x hx ↦ Matrix.ext fun k l ↦ hH k l x hx⟩

/-- Values of restricted matrices of sections. -/
lemma secEval_mapMatrix_map {W W' : Opens Y.toPresheafedSpace} (h : W' ≤ W) {x : ι → ℂ}
    (hx : x ∈ imageOpens f W') (H : Matrix κ κ' (Y.presheaf.obj (op W))) :
    (H.map (Y.presheaf.map (homOfLE h).op).hom).map (secEval f hx) =
      H.map (secEval f ((LocallyRingedSpace.IsOpenImmersion.opensFunctor f).monotone h hx)) :=
  Matrix.ext fun _ _ ↦ secEval_map h hx _

end Matrix

section Split

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

omit [Fintype κ] in
/-- The value of a restriction of a section at a point of a smaller open. -/
lemma mem_imageOpens_of_le {W W' : Opens Y.toPresheafedSpace} (h : W' ≤ W) {x : ι → ℂ}
    (hx : x ∈ imageOpens f W') : x ∈ imageOpens f W :=
  (LocallyRingedSpace.IsOpenImmersion.opensFunctor f).monotone h hx

open scoped Matrix.Norms.Operator in
/-- **Cartan's matrix lemma for sections.** Let `K₁`, `K₂ ⊆ ℂ^ι` be compact with Cartan's
splitting property, `Kᵢ ⊆ f(Wᵢ)`, and let `G` be an invertible matrix of sections of `𝒪_Y` over
an open `Ω₀` with `K₁ ∩ K₂ ⊆ f(Ω₀)`. Then there are opens `Ωᵢ ≤ Wᵢ` with `Kᵢ ⊆ f(Ωᵢ)` and
`Ω₁ ⊓ Ω₂ ≤ Ω₀`, and invertible matrices `Hᵢ` of sections over `Ωᵢ` with `G = H₁ H₂` on
`Ω₁ ⊓ Ω₂`. -/
theorem exists_matrix_split_sections {K₁ K₂ : Set (ι → ℂ)} (hK₁ : IsCompact K₁)
    (hK₂ : IsCompact K₂) (hsplit : Complex.MatrixSplit κ K₁ K₂)
    {W₁ W₂ Ω₀ : Opens Y.toPresheafedSpace}
    (hK₁W : K₁ ⊆ imageOpens f W₁) (hK₂W : K₂ ⊆ imageOpens f W₂)
    (hK : K₁ ∩ K₂ ⊆ imageOpens f Ω₀) (G G' : Matrix κ κ (Y.presheaf.obj (op Ω₀)))
    (hG : G * G' = 1) :
    ∃ (Ω₁ Ω₂ : Opens Y.toPresheafedSpace), Ω₁ ≤ W₁ ∧ Ω₂ ≤ W₂ ∧ ∃ h₀ : Ω₁ ⊓ Ω₂ ≤ Ω₀,
      K₁ ⊆ imageOpens f Ω₁ ∧ K₂ ⊆ imageOpens f Ω₂ ∧
      ∃ H₁ H₁' : Matrix κ κ (Y.presheaf.obj (op Ω₁)), H₁ * H₁' = 1 ∧
      ∃ H₂ H₂' : Matrix κ κ (Y.presheaf.obj (op Ω₂)), H₂ * H₂' = 1 ∧
        G.map (Y.presheaf.map (homOfLE h₀).op).hom =
          H₁.map (Y.presheaf.map (homOfLE (inf_le_left : Ω₁ ⊓ Ω₂ ≤ Ω₁)).op).hom *
            H₂.map (Y.presheaf.map (homOfLE (inf_le_right : Ω₁ ⊓ Ω₂ ≤ Ω₂)).op).hom := by
  haveI : CompleteSpace (Matrix κ κ ℂ) := FiniteDimensional.complete ℂ _
  have hemb := isOpenEmbedding_base (f := f)
  -- the matrix `G` as a function
  choose φ hφd hφ using fun k l ↦ differentiableOn_secEval (f := f) (G k l)
  set g : (ι → ℂ) → Matrix κ κ ℂ := fun x ↦ Matrix.of fun k l ↦ φ k l x with hgdef
  have hgG : ∀ x (hx : x ∈ imageOpens f Ω₀), g x = G.map (secEval f hx) := fun x hx ↦
    Matrix.ext fun k l ↦ (hφ k l x hx).symm
  have hgu : ∀ x ∈ (imageOpens f Ω₀ : Set (ι → ℂ)), IsUnit (g x) := by
    intro x hx
    have e : g x * G'.map (secEval f hx) = 1 := by
      rw [hgG x hx, ← Matrix.map_mul, hG, Matrix.map_one _ (map_zero _) (map_one _)]
    exact ⟨⟨_, _, e, (Matrix.mul_eq_one_comm_of_card_eq κ κ ℂ rfl).mp e⟩, rfl⟩
  have hgd : DifferentiableOn ℂ g (imageOpens f Ω₀) :=
    Complex.differentiableOn_matrix_of fun k l ↦ hφd k l
  -- neighbourhoods of `K₁`, `K₂` meeting inside `f(Ω₀)`
  obtain ⟨N₁, N₂, hN₁, hN₂, hKN₁, hKN₂, hN⟩ := Complex.exists_isOpen_inter_subset hK₁ hK₂
    (imageOpens f Ω₀).isOpen hK
  set V₁ := (imageOpens f W₁ : Set (ι → ℂ)) ∩ N₁
  set V₂ := (imageOpens f W₂ : Set (ι → ℂ)) ∩ N₂
  have hV₁₂ : V₁ ∩ V₂ ⊆ imageOpens f Ω₀ := fun x hx ↦ hN ⟨hx.1.2, hx.2.2⟩
  obtain ⟨V₁', V₂', hV₁', hV₂', hKV₁', hKV₂', hV₁'V₁, hV₂'V₂, h₁, h₂, hh₁, hh₁u, hh₂, hh₂u,
    hgh⟩ := hsplit V₁ V₂ ((imageOpens f W₁).isOpen.inter hN₁)
      ((imageOpens f W₂).isOpen.inter hN₂) (fun x hx ↦ ⟨hK₁W hx, hKN₁ hx⟩)
      (fun x hx ↦ ⟨hK₂W hx, hKN₂ hx⟩) g (hgd.mono hV₁₂) fun x hx ↦ hgu x (hV₁₂ hx)
  -- the new opens
  let Ω₁ : Opens Y.toPresheafedSpace := W₁ ⊓ (Opens.map f.base).obj ⟨V₁', hV₁'⟩
  let Ω₂ : Opens Y.toPresheafedSpace := W₂ ⊓ (Opens.map f.base).obj ⟨V₂', hV₂'⟩
  have hΩ₁ : (imageOpens f Ω₁ : Set (ι → ℂ)) = V₁' := by
    ext x
    refine ⟨?_, fun hx ↦ ?_⟩
    · rintro ⟨y, hy, rfl⟩
      exact hy.2
    · obtain ⟨y, hy, rfl⟩ := (hV₁'V₁ hx).1
      exact ⟨y, ⟨hy, hx⟩, rfl⟩
  have hΩ₂ : (imageOpens f Ω₂ : Set (ι → ℂ)) = V₂' := by
    ext x
    refine ⟨?_, fun hx ↦ ?_⟩
    · rintro ⟨y, hy, rfl⟩
      exact hy.2
    · obtain ⟨y, hy, rfl⟩ := (hV₂'V₂ hx).1
      exact ⟨y, ⟨hy, hx⟩, rfl⟩
  have h₀ : Ω₁ ⊓ Ω₂ ≤ Ω₀ := by
    intro y hy
    have hy' : f.base y ∈ imageOpens f Ω₀ :=
      hV₁₂ ⟨hV₁'V₁ hy.1.2, hV₂'V₂ hy.2.2⟩
    obtain ⟨z, hz, hzy⟩ := hy'
    rwa [← hemb.injective hzy]
  have hΩ₁₂ : ∀ x ∈ imageOpens f (Ω₁ ⊓ Ω₂), x ∈ V₁' ∩ V₂' := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨hy.1.2, hy.2.2⟩
  -- the factors as matrices of sections
  obtain ⟨H₁, hH₁⟩ := exists_matrix_secEval_eq (f := f) (W := Ω₁) h₁ fun k l ↦ by
    rw [hΩ₁]; exact Complex.DifferentiableOn.matrix_apply hh₁ k l
  obtain ⟨H₁', hH₁'⟩ := exists_matrix_secEval_eq (f := f) (W := Ω₁)
    (fun x ↦ Ring.inverse (h₁ x)) fun k l ↦ by
      rw [hΩ₁]; exact Complex.DifferentiableOn.matrix_apply (hh₁.inverse hh₁u) k l
  obtain ⟨H₂, hH₂⟩ := exists_matrix_secEval_eq (f := f) (W := Ω₂) h₂ fun k l ↦ by
    rw [hΩ₂]; exact Complex.DifferentiableOn.matrix_apply hh₂ k l
  obtain ⟨H₂', hH₂'⟩ := exists_matrix_secEval_eq (f := f) (W := Ω₂)
    (fun x ↦ Ring.inverse (h₂ x)) fun k l ↦ by
      rw [hΩ₂]; exact Complex.DifferentiableOn.matrix_apply (hh₂.inverse hh₂u) k l
  refine ⟨Ω₁, Ω₂, inf_le_left, inf_le_left, h₀, hKV₁'.trans hΩ₁.ge, hKV₂'.trans hΩ₂.ge,
    H₁, H₁', ?_, H₂, H₂', ?_, ?_⟩
  · refine matrix_ext_secEval (f := f) fun x hx ↦ ?_
    have hx' : x ∈ V₁' := hΩ₁ ▸ hx
    rw [Matrix.map_mul, hH₁ x hx, hH₁' x hx, Matrix.map_one _ (map_zero _) (map_one _),
      Ring.mul_inverse_cancel _ (hh₁u x hx')]
  · refine matrix_ext_secEval (f := f) fun x hx ↦ ?_
    have hx' : x ∈ V₂' := hΩ₂ ▸ hx
    rw [Matrix.map_mul, hH₂ x hx, hH₂' x hx, Matrix.map_one _ (map_zero _) (map_one _),
      Ring.mul_inverse_cancel _ (hh₂u x hx')]
  · refine matrix_ext_secEval (f := f) fun x hx ↦ ?_
    erw [Matrix.map_mul, secEval_mapMatrix_map, secEval_mapMatrix_map, secEval_mapMatrix_map,
      hH₁, hH₂, ← hgG, hgh x (hΩ₁₂ x hx)]

end Split

end ComplexAnalytic
