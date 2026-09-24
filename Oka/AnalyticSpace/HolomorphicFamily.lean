/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.AnalyticSpace.OpenBaseProjection

/-!
# The family of a monic polynomial with holomorphic coefficients

`Oka/AnalyticSpace/OpenBaseProjection.lean` proves that a hypersurface of the cylinder `V × ℂ`
cut out by a continuous family `q : V → ℂ[X]` of monic polynomials of one fixed degree is finite
over `V`, and its family is a hypothesis. **This file produces one**, from a
`P : Polynomial (OkaRing V)` that is monic: its coefficients are holomorphic functions on `V`,
so the family they give is holomorphic in the base point and not merely continuous in it.

That is the shape a Weierstrass polynomial has. `Oka/Weierstrass.lean`'s preparation theorem
produces exactly a monic element of `Polynomial (OkaRing U)` for a polydisc `U`, so this is the
bridge that turns its output into an input of the projection theorem — and it is why the base
here is an open `V` and not the whole of `ℂ^n`, since a germ's Weierstrass polynomial exists on
some neighbourhood and on no more.

## Why this is not `Oka/Weierstrass.lean`'s cylinder relabelled

`Oka/Weierstrass.lean` already interprets a polynomial over `OkaRing U` as a holomorphic function
on a cylinder: `Polynomial.toOkaRing`, built from `OkaRing.pullbackInit` and `OkaRing.lastVar`.
**It is not usable here and it is not moved.** It is stated at index type `Fin n` and for the
cylinder `TopologicalSpace.Opens.extend'`, whose membership is read by `Fin.init`; everything on
the `ComplexAnalytic.AnalyticSpace` side is at `ULift (Fin n)` and at `ComplexAnalytic.cylinder`,
which is defined as a *preimage* under `ComplexAnalytic.AnalyticSpace.proj`. The two are the same
construction and they do not typecheck against each other; `Oka/AnalyticSpace/ProjectionStalk.lean`
records that there is no morphism of spaces between the two spellings of `ℂ^n` above `Type 0`,
which is why they cannot be bridged rather than duplicated.

**So the analogue is built here beside the original, and the original is left alone.** The choice
is between relabelling `OkaRing.pullbackInit` — which `Oka/Weierstrass.lean` and
`Oka/Statement.lean` consume throughout, both `Fin`-indexed — and writing forty lines against
`ComplexAnalytic.cylinder`. The second is what this file does, and the duplication is the `ULift`
one that `Oka/AnalyticSpace/OpenBaseProjection.lean` already carries for the cylinder itself, not
a fresh one.

`ComplexAnalytic.uliftInitCLM` is the only new piece of analysis and it is not analysis: the
projection to the first `n` coordinates is a continuous linear map, so
`OkaAnalytic.comp_continuousLinearMap` — which is already general in *both* index types — gives
the pullback with nothing to prove.

## What each hypothesis of the projection theorem costs

* `hm`, `hd` — `Polynomial.Monic.map` and `Polynomial.Monic.natDegree_map`, exactly as in the
  polynomial case. The degree is `P.natDegree`, *fixed*, which is what
  `Oka/Topology/Algebra/Polynomial.lean` needs and cannot weaken to a bound.
* `hc` — **`OkaRing.continuous_evalHom` and nothing else.** The coefficient of the family in
  degree `j` at a base point `w` *is* the value of `P.coeff j` at `w`, and a holomorphic function
  is continuous. This is the hypothesis the projection theorem calls its only analytic input, and
  it is the one place below where holomorphy is used at all rather than continuity.
* `hrange` — `ComplexAnalytic.evalHom_cylinderSection`, which says the section this file attaches
  to `P` has the family for its values.

## Main definitions

- `ComplexAnalytic.uliftInitCLM`: the projection of `ℂ^(n+1)` to its first `n` coordinates, as a
  continuous linear map.
- `ComplexAnalytic.pullbackCylinder`: holomorphic functions on `V`, pulled back to the cylinder
  over `V`.
- `ComplexAnalytic.lastCoord`: the last coordinate, as a holomorphic function on the cylinder.
- `ComplexAnalytic.cylinderSection`: **a polynomial over `OkaRing V`, as a holomorphic function on
  the cylinder over `V`.**
- `ComplexAnalytic.okaFamily`: **the family of one-variable polynomials of `P`**, its coefficients
  evaluated at a point of the base.

## Main results

- `ComplexAnalytic.evalHom_cylinderSection`: **the value of the section at a point of the cylinder
  is the value of the family at the first `n` coordinates, evaluated at the last.**
- `ComplexAnalytic.monic_okaFamily`, `ComplexAnalytic.natDegree_okaFamily` and
  `ComplexAnalytic.continuous_coeff_okaFamily`: **the family of a monic `P` is monic, of one
  fixed degree, and has continuous coefficients** — the three hypotheses the projection theorem
  over an open base asks of a family.
- `ComplexAnalytic.isFinite_comp_projRestrict_of_monic`: **the hypersurface of the cylinder over
  `V` cut out by a monic polynomial with holomorphic coefficients is finite over `V`.**

## What is not here

* **Nothing from a germ in this file.** `P` is a hypothesis below and nothing here chooses the
  neighbourhood it lives on. **The extraction is no longer absent from the repository**:
  `LocalOkaRing.exists_monic_realize_ulift` in `Oka/UliftCoord.lean` produces a monic
  `P : Polynomial (OkaRing W)` with `W : Opens (ULift (Fin n) → ℂ)` from a germ Weierstrass
  polynomial, and `LocalOkaRing.exists_congr_monic_realize_of_ne_zero` chains it with the
  preparation theorem to start from an arbitrary nonzero germ. What that file does **not**
  produce is a hypersurface or its image, which is what
  `ComplexAnalytic.isFinite_comp_projRestrict_of_monic` still asks a caller for; see the next
  bullet for why it is a range condition.
* **No `ComplexAnalytic.IsCutOutBy` form.** The cut-out form of the projection theorem,
  `ComplexAnalytic.isFinite_comp_projRestrict_of_isCutOutBy`, takes the cutting section as the
  restriction of an **entire** function, and
  `ComplexAnalytic.cylinderSection` is not one — that is the point of the file. Carrying the
  cut-out form across needs the global sections of the cylinder subspace identified with
  `OkaRing (ComplexAnalytic.cylinder V)`, which
  `Oka/AnalyticSpace/OpenBaseProjection.lean` states in terms that it does not do:
  *"the global sections of the cylinder subspace are not `OkaRing (cylinder V)` on the nose, so
  `germ_mem_maximalIdeal_iff` does not apply to a section that is not a restriction."* So the
  theorem below takes its image as a set equation, and a caller must supply one.
* **No `IsFiniteEtale`, and nothing about stalks.** The other half is
  `Oka/AnalyticSpace/SimpleZeroStalk.lean` and its transport is
  `ComplexAnalytic.isIso_stalkMap_comp_projRestrict`; neither is invoked and no simple-zero
  hypothesis appears below.
* **No bound on the fibres.** The degree bounds the number of roots, and nothing here says so;
  that absence is `Oka/AnalyticSpace/MonicProjection.lean`'s and is unchanged.
-/

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry Topology

universe u

noncomputable section

namespace ComplexAnalytic

variable {n : ℕ}

/-! ### The cylinder's two coordinate functions -/

/-- **The projection of `ℂ^(n+1)` to its first `n` coordinates**, as a continuous linear map.

The `ULift`-indexed analogue of `finInitCLM`, and the reason
`ComplexAnalytic.pullbackCylinder` costs nothing: `OkaAnalytic.comp_continuousLinearMap` is
stated for an arbitrary continuous linear map between two `ℂ^ι`s with different index types. -/
def uliftInitCLM (n : ℕ) : (ULift.{u} (Fin (n + 1)) → ℂ) →L[ℂ] (ULift.{u} (Fin n) → ℂ) :=
  ContinuousLinearMap.pi fun j ↦ ContinuousLinearMap.proj (ULift.up j.down.castSucc)

/-- **It is the first component of `ComplexAnalytic.uliftSnocHomeo`**, on the nose, which is what
lets `ComplexAnalytic.mem_cylinder` discharge the membership hypothesis below. -/
@[simp]
theorem uliftInitCLM_apply (z : ULift.{u} (Fin (n + 1)) → ℂ) :
    uliftInitCLM.{u} n z = (uliftSnocHomeo.{u} n z).1 :=
  rfl

variable (V : Opens (ULift.{u} (Fin n) → ℂ))

/-- **Holomorphic functions on `V`, pulled back to the cylinder over `V`.**

The analogue of `OkaRing.pullbackInit`, at `ULift (Fin n)` and at `ComplexAnalytic.cylinder`; see
the module docstring on why the original is not moved. Every field but the first is `rfl`,
because the ring operations on `OkaRing` are pointwise. -/
def pullbackCylinder : OkaRing V →ₐ[ℂ] OkaRing (cylinder.{u} V) where
  toFun f := OkaRing.mk (fun z ↦ f.toFun _ ⟨uliftInitCLM.{u} n z.1, mem_cylinder.1 z.2⟩)
    (OkaAnalytic.comp_continuousLinearMap (uliftInitCLM.{u} n)
      (fun _ hz ↦ mem_cylinder.1 hz) f.2)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simp]
theorem pullbackCylinder_toFun (f : OkaRing V) (z : ↥(cylinder.{u} V)) :
    (pullbackCylinder.{u} V f).toFun _ z =
      f.toFun _ ⟨uliftInitCLM.{u} n z.1, mem_cylinder.1 z.2⟩ :=
  rfl

/-- **The last coordinate, as a holomorphic function on the cylinder over `V`.**

The analogue of `OkaRing.lastVar`. A coordinate projection is a continuous linear map and so is
analytic at every point; the restriction to the cylinder is `okaAnalytic_restrict`. -/
def lastCoord : OkaRing (cylinder.{u} V) :=
  OkaRing.mk (fun z ↦ z.1 (ULift.up (Fin.last n)))
    (okaAnalytic_restrict fun x _ ↦
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ULift.{u} (Fin (n + 1)) ↦ ℂ)
        (ULift.up (Fin.last n))).analyticAt x)

@[simp]
theorem lastCoord_toFun (z : ↥(cylinder.{u} V)) :
    (lastCoord.{u} V).toFun _ z = z.1 (ULift.up (Fin.last n)) :=
  rfl

/-! ### A polynomial with holomorphic coefficients, as a function on the cylinder -/

/-- **A polynomial over `OkaRing V`, as the holomorphic function
`(w, t) ↦ ∑ i, (P.coeff i) w * t ^ i` on the cylinder over `V`.**

Evaluation at `ComplexAnalytic.lastCoord` with the coefficients pulled back along
`ComplexAnalytic.pullbackCylinder`, exactly as `Polynomial.toOkaRing` is on the `Fin`-indexed
side. -/
def cylinderSection : Polynomial (OkaRing V) →ₐ[ℂ] OkaRing (cylinder.{u} V) :=
  Polynomial.eval₂AlgHom (pullbackCylinder.{u} V) (lastCoord.{u} V) fun _ ↦ Commute.all _ _

@[simp]
theorem cylinderSection_C (f : OkaRing V) :
    cylinderSection.{u} V (Polynomial.C f) = pullbackCylinder.{u} V f :=
  Polynomial.eval₂_C _ _

@[simp]
theorem cylinderSection_X :
    cylinderSection.{u} V (Polynomial.X : Polynomial (OkaRing V)) = lastCoord.{u} V :=
  Polynomial.eval₂_X _ _

/-! ### The family of one-variable polynomials -/

variable (P : Polynomial (OkaRing V))

/-- **The family of one-variable polynomials of `P`**: the coefficients of `P`, which are
holomorphic functions on `V`, evaluated at a point of `V`.

Mapping `P` along evaluation at `w`, which is a ring homomorphism `OkaRing V →+* ℂ`, so the
family inherits monicity and degree from `P` with nothing to prove. -/
def okaFamily : ↥V → Polynomial ℂ :=
  fun w ↦ P.map (OkaRing.evalHom w.2)

/-- **Every member of the family of a monic `P` is monic.** -/
theorem monic_okaFamily (hP : P.Monic) (w : ↥V) : (okaFamily.{u} V P w).Monic :=
  hP.map _

/-- **Every member has the same degree**, which is the hypothesis
`ComplexAnalytic.isFinite_comp_projRestrict_of_range_eq` cannot weaken to a bound. -/
theorem natDegree_okaFamily (hP : P.Monic) (w : ↥V) :
    (okaFamily.{u} V P w).natDegree = P.natDegree :=
  hP.natDegree_map _

/-- **The coefficients vary continuously**, because each of them is a holomorphic function of the
base point: `(okaFamily V P w).coeff j` is the value of `P.coeff j` at `w`.

`OkaRing.continuous_evalHom` is the whole proof, and it is the only place in this file where
holomorphy is used rather than continuity. No monicity is needed. -/
theorem continuous_coeff_okaFamily (j : ℕ) :
    Continuous fun w : ↥V ↦ (okaFamily.{u} V P w).coeff j := by
  simp only [okaFamily, Polynomial.coeff_map]
  exact OkaRing.continuous_evalHom (P.coeff j)

/-- **The value of the section at a point of the cylinder is the value of the family at the first
`n` coordinates, evaluated at the last.**

The analogue of `OkaRing.evalHom_toOkaRing`, and the reason it is stated in the `eval₂` form
first: both sides are ring homomorphisms out of `Polynomial (OkaRing V)`, so
`Polynomial.ringHom_ext` reduces it to the constants and to `X`. -/
theorem evalHom_cylinderSection' {z : ULift.{u} (Fin (n + 1)) → ℂ} (hz : z ∈ cylinder.{u} V) :
    OkaRing.evalHom hz (cylinderSection.{u} V P) =
      Polynomial.eval₂ (OkaRing.evalHom (mem_cylinder.1 hz)) (z (ULift.up (Fin.last n))) P := by
  have key : (OkaRing.evalHom hz).comp (cylinderSection.{u} V).toRingHom =
      Polynomial.eval₂RingHom (OkaRing.evalHom (mem_cylinder.1 hz))
        (z (ULift.up (Fin.last n))) := by
    refine Polynomial.ringHom_ext (fun a ↦ ?_) ?_
    · rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        cylinderSection_C, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
      rfl
    · rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        cylinderSection_X, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
      rfl
  have := congrArg (fun Φ ↦ Φ P) key
  simpa using this

/-- **The same, read through `ComplexAnalytic.cylinderHomeo`**, which is the spelling
`ComplexAnalytic.isFinite_comp_projRestrict_of_range_eq` states its hypothesis in.

This is the `hF` of the polynomial case: it is what says the section attached to `P` really is
the Weierstrass polynomial of the family `ComplexAnalytic.okaFamily V P` on the cylinder. -/
theorem evalHom_cylinderSection {z : ULift.{u} (Fin (n + 1)) → ℂ} (hz : z ∈ cylinder.{u} V) :
    OkaRing.evalHom hz (cylinderSection.{u} V P) =
      (okaFamily.{u} V P (cylinderHomeo.{u} V ⟨z, hz⟩).1).eval
        (cylinderHomeo.{u} V ⟨z, hz⟩).2 := by
  rw [evalHom_cylinderSection', okaFamily, Polynomial.eval_map]
  rfl

/-! ### Finiteness of the projection over `V` -/

variable {W : AnalyticSpace.{u}}

/-- **A hypersurface of the cylinder over `V` cut out by a monic polynomial with holomorphic
coefficients is finite over `V`.**

`ComplexAnalytic.isFinite_comp_projRestrict_of_range_eq` with all three hypotheses on the family
supplied by `ComplexAnalytic.okaFamily`, and the image condition read off the section by
`ComplexAnalytic.evalHom_cylinderSection`. Nothing is asked of `P` but monicity — in particular
its degree is whatever it is, and it is fixed because `P` is one polynomial and not a family.

**The image is a hypothesis and not a cut-out datum.** See the module docstring: the cut-out form
of the projection theorem takes an entire section, and this one is not entire. -/
theorem isFinite_comp_projRestrict_of_monic
    (i : W ⟶ (AnalyticSpace.complexAffineSpace.{u} (n + 1)).restrict (cylinder.{u} V))
    (hi : IsClosedEmbedding (i.toLRSHom.base : W → _))
    (hP : P.Monic)
    (hrange : Set.range (i.toLRSHom.base : W → _) =
      {z | OkaRing.evalHom z.2 (cylinderSection.{u} V P) = 0}) :
    AnalyticSpace.IsFinite (i ≫ AnalyticSpace.projRestrict.{u} V) := by
  refine isFinite_comp_projRestrict_of_range_eq i hi (monic_okaFamily.{u} V P hP)
    (natDegree_okaFamily.{u} V P hP) (continuous_coeff_okaFamily.{u} V P) ?_
  rw [hrange]
  ext z
  simp only [Set.mem_setOf_eq]
  rw [evalHom_cylinderSection.{u} V P z.2]
  exact Iff.rfl

end ComplexAnalytic

end
