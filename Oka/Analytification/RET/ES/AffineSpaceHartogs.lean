/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.ES.AnalyticStalkFlat
import Oka.Analytification.RET.ES.FiniteSplitting
import Oka.Analytification.RET.ES.NormalToSmooth
import Oka.AnalyticSpace.HartogsExtension
import Oka.Analytic.HartogsRegular
import Oka.RingTheory.NormalDepthTwo

/-!
# Hartogs extension on affine space across the zero set of a regular pair of polynomials

Let `p₁, p₂` be polynomials in `N` variables forming a weakly regular sequence. On `ℂ^N`, and on
`(𝔸^N)^an`, restriction of holomorphic functions from an open `Ω` to the part of `Ω` where `p₁`
or `p₂` does not vanish is bijective
(`ComplexAnalytic.hasHartogsExtension_analytification_affineSpace`). The germs of `p₁, p₂` form
a regular sequence at every point since analytic stalks are flat over polynomials
(`ComplexAnalytic.flat_analytificationStalk`), and Hartogs extension on `ℂ^N` is
`OkaRing.existsUnique_restrict_eq_of_isWeaklyRegular`.
-/

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace RingTheory.Sequence

universe u

namespace ComplexAnalytic

open AnalyticSpace

noncomputable section

variable {n : ℕ}

/-- **Hartogs extension on `ℂⁿ`** across the common zero set of two functions whose germs form
a regular sequence at their common zeros. -/
theorem hasHartogsExtension_complexAffineSpace
    (g h : (AnalyticSpace.complexAffineSpace.{u} n).presheaf.obj (op ⊤))
    (hreg : ∀ z : AnalyticSpace.complexAffineSpace.{u} n,
      (AnalyticSpace.complexAffineSpace.{u} n).eval z (U := ⊤) trivial g = 0 →
      (AnalyticSpace.complexAffineSpace.{u} n).eval z (U := ⊤) trivial h = 0 →
      IsWeaklyRegular (LocalOkaRing (ULift.{u} (Fin n)))
        [OkaRing.germ (U := ⊤) (y := z) trivial g, OkaRing.germ (U := ⊤) (y := z) trivial h])
    (O : (AnalyticSpace.complexAffineSpace.{u} n).Opens)
    (hO : ∀ z, z ∈ O ↔ ¬ ((AnalyticSpace.complexAffineSpace.{u} n).eval z (U := ⊤) trivial g = 0 ∧
      (AnalyticSpace.complexAffineSpace.{u} n).eval z (U := ⊤) trivial h = 0)) :
    HasHartogsExtension (AnalyticSpace.complexAffineSpace.{u} n) O := by
  intro Ω
  let gΩ : OkaRing Ω := OkaRing.restrict (le_top : Ω ≤ ⊤) g
  let hΩ : OkaRing Ω := OkaRing.restrict (le_top : Ω ≤ ⊤) h
  have hval : ∀ (f : (AnalyticSpace.complexAffineSpace.{u} n).presheaf.obj (op ⊤)) z (hz : z ∈ Ω),
      (OkaRing.restrict (le_top : Ω ≤ ⊤) f : OkaRing Ω).toGlobalFun _ z =
        (AnalyticSpace.complexAffineSpace.{u} n).eval z (U := ⊤) trivial f := by
    intro f z hz
    rw [(OkaRing.restrict (le_top : Ω ≤ ⊤) f).toGlobalFun_apply hz, eval_complexAffineSpace]
    rfl
  have H := OkaRing.existsUnique_restrict_eq_of_isWeaklyRegular (U := Ω) (V := Ω ⊓ O)
    inf_le_left gΩ hΩ (fun z hz hgz hhz ↦ by
      rw [OkaRing.germ_restrict, OkaRing.germ_restrict]
      exact hreg z ((hval g z hz).symm.trans hgz) ((hval h z hz).symm.trans hhz))
    (fun z hz ↦ ⟨hz.1, (hO z).2 fun ⟨hgz, hhz⟩ ↦
      hz.2 ⟨(hval g z hz.1).trans hgz, (hval h z hz.1).trans hhz⟩⟩)
  refine ⟨fun F F' hFF' ↦ ?_, fun f ↦ ?_⟩
  · obtain ⟨_, -, hu⟩ := H ((AnalyticSpace.complexAffineSpace.{u} n).res inf_le_left F)
    exact (hu F rfl).trans (hu F' hFF'.symm).symm
  · obtain ⟨F, hF, -⟩ := H f
    exact ⟨F, hF⟩

/-- **Germs of a regular pair of polynomials** form a regular sequence in the ring of convergent
power series at every point of `ℂ^N`. -/
theorem isWeaklyRegular_germ_polyFun {N : ℕ} {p₁ p₂ : MvPolynomial (Fin N) (ULift.{u} ℂ)}
    (hp : IsWeaklyRegular (MvPolynomial (Fin N) (ULift.{u} ℂ)) [p₁, p₂])
    (w : AnalyticSpace.complexAffineSpace.{u} N) :
    IsWeaklyRegular (LocalOkaRing (ULift.{u} (Fin N)))
      [OkaRing.germ (U := ⊤) (y := w) trivial (polyFun N p₁),
        OkaRing.germ (U := ⊤) (y := w) trivial (polyFun N p₂)] := by
  set e := analytificationAffineSpaceIso.{u} N
  obtain ⟨x, rfl⟩ : ∃ x, e.hom.toLRSHom.base x = w :=
    ⟨e.inv.toLRSHom.base w, congrArg (fun f ↦ f.toLRSHom.base w) e.inv_hom_id⟩
  let ι : MvPolynomial (Fin N) (ULift.{u} ℂ) ≃+* Γ((affineSpace.{u} N).obj.left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin N) (ULift.{u} ℂ)))
      ).commRingCatIsoToRingEquiv.symm
  haveI : IsAffine (affineSpace.{u} N).obj.left :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of (MvPolynomial (Fin N) (ULift.{u} ℂ)))))
  have h2 := isWeaklyRegular_analytificationStalk (affineSpace.{u} N) x (hp.map_ringEquiv ι)
  haveI := isLocalIso_of_isIso e.hom
  let σ := RingEquiv.ofBijective (e.hom.toLRSHom.stalkMap x).hom
    (ConcreteCategory.bijective_of_isIso (e.hom.toLRSHom.stalkMap x))
  have hσ : ∀ p, σ ((AnalyticSpace.complexAffineSpace.{u} N).presheaf.Γgerm
      (e.hom.toLRSHom.base x) (polyFun N p)) =
      (analytification.obj (affineSpace.{u} N)).presheaf.Γgerm x
        (analytificationΓ (affineSpace.{u} N) (ι p)) := fun p ↦
    (LocallyRingedSpace.stalkMap_germ_apply e.hom.toLRSHom ⊤ x trivial (polyFun N p)).trans
      (congrArg _ (Γ_map_polyFun p))
  have key : ∀ p, okaStalkEquiv (ι := ULift.{u} (Fin N)) (e.hom.toLRSHom.base x)
      (σ.symm ((analytification.obj (affineSpace.{u} N)).presheaf.Γgerm x
        (analytificationΓ (affineSpace.{u} N) (ι p)))) =
      OkaRing.germ (U := ⊤) (y := e.hom.toLRSHom.base x) trivial (polyFun N p) := fun p ↦ by
    rw [← hσ, RingEquiv.symm_apply_apply]
    exact okaStalkEquiv_germ (U := ⊤) trivial (polyFun N p)
  have h4 : IsWeaklyRegular (LocalOkaRing (ULift.{u} (Fin N)))
      [okaStalkEquiv (ι := ULift.{u} (Fin N)) (e.hom.toLRSHom.base x)
        (σ.symm ((analytification.obj (affineSpace.{u} N)).presheaf.Γgerm x
          (analytificationΓ (affineSpace.{u} N) (ι p₁)))),
        okaStalkEquiv (ι := ULift.{u} (Fin N)) (e.hom.toLRSHom.base x)
        (σ.symm ((analytification.obj (affineSpace.{u} N)).presheaf.Γgerm x
          (analytificationΓ (affineSpace.{u} N) (ι p₂))))] :=
    (h2.map_ringEquiv σ.symm).map_ringEquiv
      (okaStalkEquiv (ι := ULift.{u} (Fin N)) (e.hom.toLRSHom.base x))
  rw [key, key] at h4
  exact h4

/-- **Hartogs extension on `(𝔸^N)^an`** across the common zero set of a weakly regular pair of
polynomials. -/
theorem hasHartogsExtension_analytification_affineSpace {N : ℕ}
    {p₁ p₂ : MvPolynomial (Fin N) (ULift.{u} ℂ)}
    (hp : IsWeaklyRegular (MvPolynomial (Fin N) (ULift.{u} ℂ)) [p₁, p₂]) :
    HasHartogsExtension (analytification.obj (affineSpace.{u} N))
      (nonvanishingOpens _
        (analytificationΓ (affineSpace.{u} N) ((Scheme.ΓSpecIso (.of _)).inv p₁))
        (analytificationΓ (affineSpace.{u} N) ((Scheme.ΓSpecIso (.of _)).inv p₂))) := by
  set e := analytificationAffineSpaceIso.{u} N
  have H := hasHartogsExtension_complexAffineSpace (polyFun N p₁) (polyFun N p₂)
    (fun z _ _ ↦ isWeaklyRegular_germ_polyFun hp z) _
    (mem_nonvanishingOpens_iff _ (polyFun N p₁) (polyFun N p₂))
  haveI := isLocalIso_of_isIso e.hom
  intro Ω
  refine bijective_presheaf_map_of_eq _ ?_ _ _ (bijective_res_of_isLocalIso e.hom _ H Ω)
  refine congrArg (Ω ⊓ ·) ?_
  ext x
  change ¬ (_ ∧ _) ↔ ¬ (_ ∧ _)
  rw [eval_analytificationΓ_affineSpace, eval_analytificationΓ_affineSpace, eval_polyFun,
    eval_polyFun]

end

end ComplexAnalytic
