/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.OkaRing
import Oka.LocalOkaRing

/-!
# The Weierstrass preparation theorem

We state the Weierstrass preparation theorem: a holomorphic function on a neighbourhood of the
origin in `ℂ^{n+1}` which does not vanish identically on the last coordinate axis factors, near
the origin, as a unit times a Weierstrass polynomial.

## Main definitions

- `IsWeierstrassPolynomial`: a monic polynomial whose lower coefficients vanish at the origin.
- `LocalOkaRing.fromPolynomial`: a polynomial over the germs in `n` variables, viewed as a germ
  in `n + 1` variables.
- `Polynomial.toOkaRing`: a polynomial over `OkaRing U` viewed as a holomorphic function on the
  cylinder `U.extend'` over `U`.
- `OkaRing.germ`: the Taylor series of a holomorphic function at a point of its domain.
- `OkaRing.germPoly`: the coefficientwise germ of a polynomial over `OkaRing U` at a point of
  the cylinder over `U`, Taylor expanded in the polynomial variable.

## Main results

Besides the statements of the local Weierstrass preparation and division theorems
(`localweierstrass_preparation` and `localweierstrass_division`), this file develops the
dictionary between functions and germs used to reduce Oka's coherence lemma to them:

- `OkaRing.germ_toOkaRing`: the germ of the function attached to a polynomial is the germ
  polynomial, viewed as a germ via `LocalOkaRing.fromPolynomial`.
- `OkaRing.exists_restrict_eq_of_germ_eq`, `LocalOkaRing.exists_okaRing_germ`,
  `OkaRing.exists_isUnit_restrict`: germs detect local equality, are realized by functions on
  neighbourhoods, and detect local invertibility.
- `LocalOkaRing.exists_isWeierstrassPolynomial_realize` and
  `LocalOkaRing.exists_poly_germPoly`: realizations of germ polynomials by polynomials over
  the holomorphic functions on a neighbourhood.
- `Polynomial.exists_map_restrict_eq_zero`: a polynomial in the last variable whose attached
  function vanishes near a point of the cylinder vanishes coefficientwise near the base point.
- `MvPowerSeries.Represents.homogeneous_eval_eq_zero`, `MvPowerSeries.exists_direction`,
  `lineEquiv`: choice of a linear change of coordinates making finitely many nonzero germs
  general in the last variable.
-/

open Polynomial TopologicalSpace

variable {n : ℕ}

/-- A local Weierstrass polynomial is a monic polynomial whose coefficients below the leading
one vanish at the origin. -/
structure IsLocalWeierstrassPolynomial
  (P : (MvPowerSeries (Fin n) ℂ)[X]) : Prop where
  monic : P.Monic
  apply_zero (i : ℕ) (hi : i < P.degree) :
  MvPowerSeries.constantCoeff (P.coeff i) = 0

section FromPolynomial

namespace MvPowerSeries

/-- Evaluating a monomial in the first `n` of `n + 1` variables only sees the first `n`
coordinates. -/
lemma evalMonomial_mapDomain (e : Fin n →₀ ℕ) (x : Fin (n + 1) → ℂ) :
    evalMonomial (Finsupp.mapDomain Fin.castSucc e) x = evalMonomial e (Fin.init x) := by
  rw [evalMonomial_eq_prod, evalMonomial_eq_prod, Fin.prod_univ_castSucc]
  have hlast : Finsupp.mapDomain Fin.castSucc e (Fin.last n) = 0 :=
    Finsupp.mapDomain_notin_range e (Fin.last n) (by simp)
  rw [hlast, pow_zero, mul_one]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [Finsupp.mapDomain_apply (Fin.castSucc_injective n)]
  rfl

/-- A power series in `n` variables representing `F` represents, as a power series in `n + 1`
variables, the pullback of `F` along the projection to the first `n` coordinates. -/
lemma Represents.rename_castSucc {P : MvPowerSeries (Fin n) ℂ} {F : (Fin n → ℂ) → ℂ}
    (hP : P.Represents F) :
    (rename Fin.castSucc P).Represents (fun x ↦ F (Fin.init x)) := by
  have hcont : Continuous (Fin.init : (Fin (n + 1) → ℂ) → (Fin n → ℂ)) :=
    continuous_pi fun i ↦ continuous_apply i.castSucc
  filter_upwards [(hcont.tendsto 0).eventually hP] with x hx
  have hinj : Function.Injective
      (Finsupp.mapDomain (M := ℕ) (Fin.castSucc : Fin n → Fin (n + 1))) :=
    Finsupp.mapDomain_injective (Fin.castSucc_injective n)
  have hvanish : ∀ d ∉ Set.range (Finsupp.mapDomain (M := ℕ) (Fin.castSucc : Fin n → Fin (n + 1))),
      (rename Fin.castSucc P).term x d = 0 := fun d hd ↦ by
    rw [term, coeff_rename_eq_zero _ _ hd, zero_mul]
  refine (Function.Injective.hasSum_iff hinj hvanish).mp ?_
  have hfun : (rename Fin.castSucc P).term x ∘ Finsupp.mapDomain Fin.castSucc =
      P.term (Fin.init x) := by
    funext e
    rw [Function.comp_apply, term, term, evalMonomial_mapDomain]
    congr 1
    have hemb : Finsupp.mapDomain (M := ℕ) Fin.castSucc e =
        Finsupp.embDomain ⟨Fin.castSucc, Fin.castSucc_injective n⟩ e := by
      simp only [Finsupp.embDomain_eq_mapDomain, Function.Embedding.coeFn_mk]
    rw [hemb]
    exact coeff_embDomain_rename ⟨Fin.castSucc, Fin.castSucc_injective n⟩ P e
  rw [hfun]
  exact hx

variable {ι : Type*}

/-- The power series `X i` represents the `i`-th coordinate function. -/
lemma represents_X (i : ι) : (X i : MvPowerSeries ι ℂ).Represents (fun x ↦ x i) := by
  classical
  refine .of_forall fun x ↦ ?_
  have h : ∀ d ≠ Finsupp.single i 1, (X i : MvPowerSeries ι ℂ).term x d = 0 := fun d hd ↦ by
    rw [term, coeff_X, if_neg hd, zero_mul]
  have h1 : (X i : MvPowerSeries ι ℂ).term x (Finsupp.single i 1) = x i := by
    rw [term, coeff_X, if_pos rfl, one_mul]
    simp [evalMonomial]
  simpa only [h1] using hasSum_single (f := (X i : MvPowerSeries ι ℂ).term x)
    (Finsupp.single i 1) h

end MvPowerSeries

namespace LocalOkaRing

open MvPowerSeries

/-- The inclusion of germs in `n` variables into germs in `n + 1` variables. -/
noncomputable def renameSucc : LocalOkaRing (Fin n) →ₐ[ℂ] LocalOkaRing (Fin (n + 1)) :=
  ((MvPowerSeries.rename Fin.castSucc).comp (localOkaSubring (Fin n)).val).codRestrict
    (localOkaSubring (Fin (n + 1))) fun P ↦
      (Represents.rename_castSucc P.2.represents_eval).locallyConvergent

@[simp]
lemma coe_renameSucc (P : LocalOkaRing (Fin n)) :
    (renameSucc P : MvPowerSeries (Fin (n + 1)) ℂ) =
      MvPowerSeries.rename Fin.castSucc (P : MvPowerSeries (Fin n) ℂ) :=
  rfl

/-- The last coordinate, as a germ in `n + 1` variables. -/
noncomputable def lastX : LocalOkaRing (Fin (n + 1)) :=
  ⟨MvPowerSeries.X (Fin.last n), (represents_X _).locallyConvergent⟩

@[simp]
lemma coe_lastX : ((lastX : LocalOkaRing (Fin (n + 1))) : MvPowerSeries (Fin (n + 1)) ℂ) =
    MvPowerSeries.X (Fin.last n) :=
  rfl

end LocalOkaRing

end FromPolynomial

/-- A polynomial over the germs in `n` variables, viewed as a germ in `n + 1` variables. -/
noncomputable def LocalOkaRing.fromPolynomial :
    (LocalOkaRing (Fin n))[X] →ₐ[ℂ] LocalOkaRing (Fin (n + 1)) :=
  Polynomial.eval₂AlgHom LocalOkaRing.renameSucc LocalOkaRing.lastX fun _ ↦ Commute.all _ _

namespace LocalOkaRing

@[simp]
lemma fromPolynomial_C (P : LocalOkaRing (Fin n)) :
    fromPolynomial (Polynomial.C P) = renameSucc P :=
  Polynomial.eval₂_C _ _

@[simp]
lemma fromPolynomial_X :
    fromPolynomial (Polynomial.X : (LocalOkaRing (Fin n))[X]) = lastX :=
  Polynomial.eval₂_X _ _

/-- The underlying power series of `LocalOkaRing.fromPolynomial Q` is
`MvPowerSeries.fromPolynomial'` applied to the underlying polynomial of power series. -/
lemma coe_fromPolynomial (Q : (LocalOkaRing (Fin n))[X]) :
    (fromPolynomial Q : MvPowerSeries (Fin (n + 1)) ℂ) =
      MvPowerSeries.fromPolynomial'
        (Q.map (Subring.subtype (localOkaSubring (Fin n)).toSubring)) := by
  induction Q using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, AddMemClass.coe_add, hp, hq, Polynomial.map_add, map_add]
  | monomial k a =>
    rw [fromPolynomial, Polynomial.eval₂AlgHom_apply, Polynomial.eval₂_monomial,
      Polynomial.map_monomial, MvPowerSeries.fromPolynomial',
      Polynomial.eval₂AlgHom_apply, Polynomial.eval₂_monomial]
    simp only [RingHom.coe_coe, MulMemClass.coe_mul, SubmonoidClass.coe_pow, coe_renameSucc,
      coe_lastX]
    rfl

lemma fromPolynomial_injective :
    Function.Injective (fromPolynomial (n := n)) := by
  intro Q₁ Q₂ h
  have h2 : (fromPolynomial Q₁ : MvPowerSeries (Fin (n + 1)) ℂ) = fromPolynomial Q₂ :=
    congrArg Subtype.val h
  rw [coe_fromPolynomial, coe_fromPolynomial] at h2
  exact Polynomial.map_injective _ (fun a b hab ↦ Subtype.ext hab)
    (MvPowerSeries.fromPolynomial'_injective h2)

end LocalOkaRing

/-- The Weierstrass preparation theorem for germs; uniqueness is omitted. -/
theorem localweierstrass_preparation
    (f : LocalOkaRing (Fin (n + 1)))
    (hf : (f : MvPowerSeries (Fin (n + 1)) ℂ).IsGeneralIn (.last _)) :
    ∃ (u : LocalOkaRing (Fin (n + 1))) (hu : IsUnit u)
      (g : (LocalOkaRing (Fin (n)))[X])
      (hg : IsLocalWeierstrassPolynomial
           (Polynomial.map (Subring.subtype (localOkaSubring _).toSubring) g)),
      f = LocalOkaRing.fromPolynomial g * u :=
  sorry







/-- The Weierstrass division theorem for germs; uniqueness is omitted. -/
theorem localweierstrass_division
      (q : (LocalOkaRing (Fin (n)))[X])
      (hq : IsLocalWeierstrassPolynomial
           (Polynomial.map (Subring.subtype (localOkaSubring _).toSubring) q))
      (f : LocalOkaRing (Fin (n + 1))) :
      ∃ (a : LocalOkaRing (Fin (n + 1)))
        (b : (LocalOkaRing (Fin (n)))[X]) (hd : b.degree < q.degree),
      f = a * (LocalOkaRing.fromPolynomial q) + (LocalOkaRing.fromPolynomial b) :=
  sorry

section ToOkaRing

/-!
### Polynomials as holomorphic functions on a cylinder

A polynomial `P` over `OkaRing U` is interpreted as the holomorphic function
`(z, w) ↦ ∑ i, (P.coeff i) z * w ^ i` on the cylinder `U.extend'` over `U`. Formally,
`Polynomial.toOkaRing` is evaluation at the last coordinate function, with coefficients pulled
back along the projection to the first `n` coordinates.
-/

/-- The projection of `ℂ^{n + 1}` to the first `n` coordinates, as a continuous linear map. -/
noncomputable def finInitCLM : (Fin (n + 1) → ℂ) →L[ℂ] (Fin n → ℂ) :=
  ContinuousLinearMap.pi fun i ↦ ContinuousLinearMap.proj i.castSucc

@[simp]
lemma finInitCLM_apply (x : Fin (n + 1) → ℂ) : finInitCLM x = Fin.init x :=
  rfl

/-- Pullback of holomorphic functions along the projection of the cylinder over `U` to `U`. -/
noncomputable def OkaRing.pullbackInit (U : Opens (Fin n → ℂ)) :
    OkaRing U →ₐ[ℂ] OkaRing U.extend' where
  toFun f := OkaRing.mk (fun y ↦ f.toFun _ ⟨Fin.init y.1, Opens.mem_extend'.mp y.2⟩)
    (OkaAnalytic.comp_continuousLinearMap finInitCLM
      (fun _ hy ↦ Opens.mem_extend'.mp hy) f.2)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simp]
lemma OkaRing.pullbackInit_toFun {U : Opens (Fin n → ℂ)} (f : OkaRing U)
    (y : U.extend') :
    (OkaRing.pullbackInit U f).toFun _ y = f.toFun _ ⟨Fin.init y.1, Opens.mem_extend'.mp y.2⟩ :=
  rfl

/-- The last coordinate, as a holomorphic function on the cylinder over `U`. -/
noncomputable def OkaRing.lastVar (U : Opens (Fin n → ℂ)) : OkaRing U.extend' :=
  OkaRing.mk (fun y ↦ y.1 (Fin.last n))
    (okaAnalytic_restrict fun x _ ↦
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n + 1) ↦ ℂ)
        (Fin.last n)).analyticAt x)

@[simp]
lemma OkaRing.lastVar_toFun (U : Opens (Fin n → ℂ)) (y : U.extend') :
    (OkaRing.lastVar U).toFun _ y = y.1 (Fin.last n) :=
  rfl

/-- A polynomial with coefficients holomorphic functions on `U`, viewed as the holomorphic
function `(z, w) ↦ ∑ i, (P.coeff i) z * w ^ i` on the cylinder over `U`. -/
noncomputable
def Polynomial.toOkaRing (U : Opens (Fin n → ℂ)) :
    (OkaRing U)[X] →ₐ[ℂ] OkaRing U.extend' :=
  Polynomial.eval₂AlgHom (OkaRing.pullbackInit U) (OkaRing.lastVar U) fun _ ↦ Commute.all _ _

@[simp]
lemma Polynomial.toOkaRing_C (U : Opens (Fin n → ℂ)) (f : OkaRing U) :
    Polynomial.toOkaRing U (Polynomial.C f) = OkaRing.pullbackInit U f :=
  Polynomial.eval₂_C _ _

@[simp]
lemma Polynomial.toOkaRing_X (U : Opens (Fin n → ℂ)) :
    Polynomial.toOkaRing U (Polynomial.X : (OkaRing U)[X]) = OkaRing.lastVar U :=
  Polynomial.eval₂_X _ _

/-- Transporting the evaluation of a holomorphic function along an equality of points. -/
lemma OkaRing.evalHom_congr {U : Opens (Fin n → ℂ)} {x y : Fin n → ℂ} (hx : x ∈ U)
    (hy : y ∈ U) (h : x = y) (f : OkaRing U) :
    OkaRing.evalHom hx f = OkaRing.evalHom hy f := by
  subst h
  rfl

/-- The value of `Polynomial.toOkaRing U P` at a point of the cylinder is obtained by
evaluating the coefficients at the base point and the resulting polynomial at the last
coordinate. -/
lemma OkaRing.evalHom_toOkaRing {U : Opens (Fin n → ℂ)} {y : Fin (n + 1) → ℂ}
    (hy : y ∈ U.extend') (P : (OkaRing U)[X]) :
    OkaRing.evalHom hy (Polynomial.toOkaRing U P) =
      Polynomial.eval₂ (OkaRing.evalHom (Opens.mem_extend'.mp hy)) (y (Fin.last n)) P := by
  have key : (OkaRing.evalHom hy).comp (Polynomial.toOkaRing U).toRingHom =
      Polynomial.eval₂RingHom (OkaRing.evalHom (Opens.mem_extend'.mp hy)) (y (Fin.last n)) := by
    refine Polynomial.ringHom_ext (fun a ↦ ?_) ?_
    · rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        Polynomial.toOkaRing_C, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
      rfl
    · rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        Polynomial.toOkaRing_X, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
      rfl
  have := congrArg (fun Φ ↦ Φ P) key
  simpa using this

/-- Interpreting polynomials as functions on the cylinder commutes with restriction. -/
lemma Polynomial.toOkaRing_map_restrict {U W : Opens (Fin n → ℂ)} (h : W ≤ U)
    (P : (OkaRing U)[X]) :
    Polynomial.toOkaRing W (P.map (OkaRing.restrict h).toRingHom) =
      OkaRing.restrict (TopologicalSpace.Opens.extend'_mono h) (Polynomial.toOkaRing U P) := by
  apply OkaRing.ext
  funext z
  have h1 := OkaRing.evalHom_toOkaRing z.2 (P.map (OkaRing.restrict h).toRingHom)
  have h2 := OkaRing.evalHom_toOkaRing ((TopologicalSpace.Opens.extend'_mono h) z.2) P
  rw [Polynomial.eval₂_map] at h1
  have hcomp : (OkaRing.evalHom (Opens.mem_extend'.mp z.2)).comp
      (OkaRing.restrict h).toRingHom =
      OkaRing.evalHom (Opens.mem_extend'.mp (TopologicalSpace.Opens.extend'_mono h z.2)) :=
    RingHom.ext fun a ↦ rfl
  rw [hcomp] at h1
  calc (Polynomial.toOkaRing W (P.map (OkaRing.restrict h).toRingHom)).toFun _ z
      = OkaRing.evalHom z.2 (Polynomial.toOkaRing W (P.map (OkaRing.restrict h).toRingHom)) :=
        rfl
    _ = OkaRing.evalHom (TopologicalSpace.Opens.extend'_mono h z.2)
          (Polynomial.toOkaRing U P) := by rw [h1, h2]
    _ = (OkaRing.restrict (TopologicalSpace.Opens.extend'_mono h)
          (Polynomial.toOkaRing U P)).toFun _ z := rfl

end ToOkaRing















variable {n : ℕ} (U : Opens (Fin n → ℂ))

/-- A Weierstrass polynomial is a monic polynomial whose coefficients below the leading one
vanish at the origin. -/
structure IsWeierstrassPolynomial (P : (OkaRing U)[X]) : Prop where
  monic : P.Monic
  apply_zero (i : ℕ) (hi : i < P.degree) : (P.coeff i).toGlobalFun _ 0 = 0

section Germ

/-!
### Germs of holomorphic functions at arbitrary points

`OkaRing.germ hy` sends a holomorphic function on `U` to its Taylor series at the point
`y ∈ U`, i.e. to the Taylor series at the origin of the translated function. The germ map is
local in every respect: two functions with the same germ agree on a neighbourhood, every germ
is realized by a function on a neighbourhood, and a function whose germ is a unit is invertible
near the point.
-/

open MvPowerSeries

namespace OkaRing

variable {ι : Type*} [Fintype ι] {U : Opens (ι → ℂ)} {y : ι → ℂ}

/-- The Taylor series of a holomorphic function at a point `y` of its domain. -/
noncomputable def germ (hy : y ∈ U) : OkaRing U →ₐ[ℂ] LocalOkaRing ι :=
  (toLocalOkaRingHom (U.shift y) (by simpa using hy)).comp
    (shift U y : OkaRing U ≃ₐ[ℂ] OkaRing (U.shift y)).toAlgHom

/-- Near the origin, the translate of `f` by `y` agrees with `z ↦ f (z + y)`. -/
lemma shift_toGlobalFun_eventuallyEq (hy : y ∈ U) (f : OkaRing U) :
    (shift U y f).toGlobalFun _ =ᶠ[nhds (0 : ι → ℂ)] fun z ↦ f.toGlobalFun _ (z + y) := by
  filter_upwards [(U.shift y).isOpen.mem_nhds (show (0 : ι → ℂ) ∈ U.shift y by simpa using hy)]
    with z hz
  rw [(shift U y f).toGlobalFun_apply hz, f.toGlobalFun_apply (show z + y ∈ U from hz)]
  rfl

/-- The germ of `f` at `y` sums to `z ↦ f (z + y)` near the origin. -/
lemma germ_represents (hy : y ∈ U) (f : OkaRing U) :
    ((germ hy f : LocalOkaRing ι) : MvPowerSeries ι ℂ).Represents
      (fun z ↦ f.toGlobalFun _ (z + y)) :=
  (toLocalOkaRing_represents (show (0 : ι → ℂ) ∈ U.shift y by simpa using hy)
    ((shift U y : OkaRing U ≃ₐ[ℂ] OkaRing (U.shift y)) f)).congr
    (shift_toGlobalFun_eventuallyEq hy f)

/-- The germ of `f` at `y` is the unique locally convergent power series summing to
`z ↦ f (z + y)` near the origin. -/
lemma germ_eq_of_represents {P : LocalOkaRing ι} (hy : y ∈ U) {f : OkaRing U}
    (h : (P : MvPowerSeries ι ℂ).Represents (fun z ↦ f.toGlobalFun _ (z + y))) :
    germ hy f = P :=
  toLocalOkaRing_eq_of_represents
    (h0 := show (0 : ι → ℂ) ∈ U.shift y by simpa using hy)
    (h.congr (shift_toGlobalFun_eventuallyEq hy f).symm)

/-- At the origin, the germ is the Taylor series at the origin. -/
lemma germ_zero_mem (h0 : (0 : ι → ℂ) ∈ U) (f : OkaRing U) :
    germ h0 f = toLocalOkaRingHom U h0 f := by
  refine germ_eq_of_represents h0 ?_
  have h : (fun z ↦ f.toGlobalFun _ (z + 0)) = f.toGlobalFun _ := by
    funext z
    rw [add_zero]
  rw [h]
  exact toLocalOkaRing_represents h0 f

/-- Taking germs commutes with restriction. -/
@[simp]
lemma germ_restrict {V : Opens (ι → ℂ)} (hVU : V ≤ U) (hy : y ∈ V) (f : OkaRing U) :
    germ hy (restrict hVU f) = germ (hVU hy) f := by
  refine germ_eq_of_represents hy ?_
  refine (germ_represents (hVU hy) f).congr ?_
  filter_upwards [(V.shift y).isOpen.mem_nhds
    (show (0 : ι → ℂ) ∈ V.shift y by simpa using hy)] with z hz
  rw [f.toGlobalFun_apply (show z + y ∈ U from hVU hz),
    (restrict hVU f).toGlobalFun_apply (show z + y ∈ V from hz)]
  rfl

/-- The germ of a translated function is the germ at the translated point. -/
lemma germ_shift (v : ι → ℂ) {z : ι → ℂ} (hz : z ∈ U) (hy : y ∈ U.shift v)
    (hyz : y + v = z) (f : OkaRing U) :
    germ hy (shift U v f) = germ hz f := by
  subst hyz
  refine germ_eq_of_represents hy ?_
  refine (germ_represents (show y + v ∈ U from hy) f).congr ?_
  filter_upwards [((U.shift v).shift y).isOpen.mem_nhds
    (show (0 : ι → ℂ) ∈ (U.shift v).shift y by simpa using hy)] with w hw
  have hw' : w + y ∈ U.shift v := hw
  have hw'' : w + (y + v) ∈ U := by
    have h8 : (w + y) + v ∈ U := hw'
    rwa [add_assoc] at h8
  rw [f.toGlobalFun_apply hw'', (shift U v f).toGlobalFun_apply hw']
  change f.toFun _ ⟨w + (y + v), hw''⟩ = f.toFun _ ⟨(w + y) + v, hw'⟩
  congr 1
  exact Subtype.ext (add_assoc w y v).symm

/-- The constant term of the germ at `y` is the value at `y`. -/
lemma constantCoeff_germ (hy : y ∈ U) (f : OkaRing U) :
    LocalOkaRing.constantCoeff (germ hy f) = evalHom hy f := by
  have h1 : HasSum (((germ hy f : LocalOkaRing ι) : MvPowerSeries ι ℂ).term 0)
      (f.toGlobalFun _ (0 + y)) :=
    Filter.Eventually.self_of_nhds
      (p := fun z ↦ HasSum (((germ hy f : LocalOkaRing ι) : MvPowerSeries ι ℂ).term z)
        (f.toGlobalFun _ (z + y))) (germ_represents hy f)
  have h2 : HasSum (((germ hy f : LocalOkaRing ι) : MvPowerSeries ι ℂ).term 0)
      (MvPowerSeries.constantCoeff ((germ hy f : LocalOkaRing ι) : MvPowerSeries ι ℂ)) := by
    have h3 := hasSum_single
      (f := ((germ hy f : LocalOkaRing ι) : MvPowerSeries ι ℂ).term 0) 0
      (fun d hd ↦ by rw [term, evalMonomial_eq_zero hd, mul_zero])
    simpa only [term, evalMonomial_zero, mul_one, coeff_zero_eq_constantCoeff] using h3
  have h4 := h2.unique h1
  rw [LocalOkaRing.constantCoeff_apply, h4, zero_add, f.toGlobalFun_apply hy]
  rfl

/-- A function whose germ at `y` vanishes vanishes on a neighbourhood of `y`. -/
lemma exists_restrict_eq_zero (hy : y ∈ U) {f : OkaRing U} (h : germ hy f = 0) :
    ∃ (W : Opens (ι → ℂ)) (hWU : W ≤ U), y ∈ W ∧ restrict hWU f = 0 := by
  have hrep := germ_represents hy f
  rw [h, ZeroMemClass.coe_zero] at hrep
  have hzero : ∀ᶠ z in nhds (0 : ι → ℂ), f.toGlobalFun _ (z + y) = 0 := by
    filter_upwards [hrep] with z hz
    have h5 : HasSum ((0 : MvPowerSeries ι ℂ).term z) (0 : ℂ) := by
      have : (0 : MvPowerSeries ι ℂ).term z = fun _ ↦ (0 : ℂ) := funext fun d ↦ term_zero z d
      rw [this]
      exact hasSum_zero
    exact hz.unique h5
  obtain ⟨t, hts, htopen, ht0⟩ := mem_nhds_iff.mp hzero
  refine ⟨U ⊓ ⟨(fun z ↦ z - y) ⁻¹' t, htopen.preimage (continuous_id.sub continuous_const)⟩,
    inf_le_left, ⟨hy, by simpa using ht0⟩, ?_⟩
  apply OkaRing.ext
  funext z
  obtain ⟨hzU, hzt⟩ := z.2
  have h6 : f.toGlobalFun _ ((z.1 - y) + y) = 0 := hts hzt
  rw [sub_add_cancel, f.toGlobalFun_apply hzU] at h6
  exact h6

/-- Two functions with the same germ at `y` agree on a neighbourhood of `y`. -/
lemma exists_restrict_eq_of_germ_eq (hy : y ∈ U) {f g : OkaRing U}
    (h : germ hy f = germ hy g) :
    ∃ (W : Opens (ι → ℂ)) (hWU : W ≤ U), y ∈ W ∧ restrict hWU f = restrict hWU g := by
  obtain ⟨W, hWU, hyW, hz⟩ := exists_restrict_eq_zero hy (f := f - g)
    (by rw [map_sub, h, sub_self])
  rw [map_sub, sub_eq_zero] at hz
  exact ⟨W, hWU, hyW, hz⟩

/-- A nowhere vanishing holomorphic function is invertible. -/
lemma isUnit_of_forall_ne_zero {f : OkaRing U} (h : ∀ z : U, f.toFun _ z ≠ 0) :
    IsUnit f := by
  have hg : ∀ x ∈ U, AnalyticAt ℂ (fun w ↦ (f.toGlobalFun _ w)⁻¹) x := fun x hx ↦
    (f.analyticAt_toGlobalFun hx).inv (by rw [f.toGlobalFun_apply hx]; exact h ⟨x, hx⟩)
  have hmul : f * OkaRing.mk _ (okaAnalytic_restrict hg) = 1 := by
    apply OkaRing.ext
    funext z
    change f.toFun _ z * (f.toGlobalFun _ z.1)⁻¹ = 1
    rw [f.toGlobalFun_apply z.2]
    exact mul_inv_cancel₀ (h z)
  exact IsUnit.of_mul_eq_one _ hmul

/-- The ring of holomorphic functions on a nonempty open set is nontrivial. -/
lemma nontrivial (hy : y ∈ U) : Nontrivial (OkaRing U) :=
  ⟨⟨1, 0, fun hc ↦ one_ne_zero (α := ℂ) (by
    have h1 := congrArg (evalHom hy) hc
    rwa [map_one, map_zero] at h1)⟩⟩

/-- A function whose germ at `y` is invertible is invertible on a neighbourhood of `y`. -/
lemma exists_isUnit_restrict (hy : y ∈ U) {f : OkaRing U} (h : IsUnit (germ hy f)) :
    ∃ (W : Opens (ι → ℂ)) (hWU : W ≤ U), y ∈ W ∧ IsUnit (restrict hWU f) := by
  rw [LocalOkaRing.isUnit_iff, constantCoeff_germ] at h
  have hcont : ContinuousAt (f.toGlobalFun _) y := (f.analyticAt_toGlobalFun hy).continuousAt
  have hne : f.toGlobalFun _ y ≠ 0 := by
    rw [f.toGlobalFun_apply hy]
    exact h
  obtain ⟨t, hts, htopen, hyt⟩ := mem_nhds_iff.mp (hcont.eventually_ne hne)
  refine ⟨U ⊓ ⟨t, htopen⟩, inf_le_left, ⟨hy, hyt⟩, ?_⟩
  refine isUnit_of_forall_ne_zero fun z ↦ ?_
  have h7 : f.toGlobalFun _ z.1 ≠ 0 := hts z.2.2
  rw [f.toGlobalFun_apply z.2.1] at h7
  exact h7

end OkaRing

end Germ

section GermPoly

/-!
### Germs of polynomial functions on a cylinder

The germ at a point `(y', w)` of the cylinder `V.extend'` of the function attached to a
polynomial `Q` over `OkaRing V` is again polynomial: it is obtained by taking germs of the
coefficients at `y'` and Taylor expanding at `w` in the polynomial variable. This is the
content of `OkaRing.germ_toOkaRing`, which links `Polynomial.toOkaRing` with
`LocalOkaRing.fromPolynomial`.
-/

open MvPowerSeries

/-- Membership in a finite infimum of open sets. -/
lemma TopologicalSpace.Opens.mem_finset_inf {X α : Type*} [TopologicalSpace X] {s : Finset α}
    {f : α → Opens X} {x : X} : x ∈ s.inf f ↔ ∀ i ∈ s, x ∈ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.inf_insert]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact h1
      · exact ih.mp h2 i hi
    · intro h
      exact ⟨h a (Finset.mem_insert_self a s), ih.mpr fun i hi ↦
        h i (Finset.mem_insert_of_mem hi)⟩

namespace OkaRing

variable {n : ℕ} {V : Opens (Fin n → ℂ)} {y' : Fin n → ℂ}

/-- Taylor expansion of a polynomial over `OkaRing V` at the point `(y', w)` of the cylinder:
take germs of the coefficients at `y'` and expand the polynomial variable at `w`. -/
noncomputable def germPoly (hy' : y' ∈ V) (w : ℂ) :
    (OkaRing V)[X] →ₐ[ℂ] (LocalOkaRing (Fin n))[X] :=
  ((Polynomial.aeval
      (Polynomial.X + Polynomial.C (algebraMap ℂ (LocalOkaRing (Fin n)) w))).restrictScalars
    ℂ).comp (Polynomial.mapAlgHom (germ hy'))

lemma germPoly_apply (hy' : y' ∈ V) (w : ℂ) (Q : (OkaRing V)[X]) :
    germPoly hy' w Q = (Q.map (germ hy').toRingHom).comp
      (Polynomial.X + Polynomial.C (algebraMap ℂ (LocalOkaRing (Fin n)) w)) := by
  rw [germPoly, AlgHom.comp_apply, AlgHom.restrictScalars_apply, Polynomial.aeval_def,
    Polynomial.comp, Polynomial.algebraMap_eq]
  rfl

/-- `OkaRing.germPoly` as a Taylor expansion. -/
lemma germPoly_eq_taylor (hy' : y' ∈ V) (w : ℂ) (Q : (OkaRing V)[X]) :
    germPoly hy' w Q = Polynomial.taylor (algebraMap ℂ (LocalOkaRing (Fin n)) w)
      (Q.map (germ hy').toRingHom) := by
  rw [germPoly_apply, Polynomial.taylor_apply]

/-- At a point with vanishing last coordinate, `OkaRing.germPoly` is just the coefficientwise
germ. -/
lemma germPoly_zero (hy' : y' ∈ V) (Q : (OkaRing V)[X]) :
    germPoly hy' 0 Q = Q.map (germ hy').toRingHom := by
  rw [germPoly_eq_taylor, map_zero, Polynomial.taylor_zero]

lemma monic_germPoly (hy' : y' ∈ V) (w : ℂ) {Q : (OkaRing V)[X]} (hQ : Q.Monic) :
    (germPoly hy' w Q).Monic := by
  rw [germPoly_apply]
  exact (hQ.map _).comp_X_add_C _

lemma natDegree_germPoly_le (hy' : y' ∈ V) (w : ℂ) (Q : (OkaRing V)[X]) :
    (germPoly hy' w Q).natDegree ≤ Q.natDegree := by
  rw [germPoly_eq_taylor, Polynomial.natDegree_taylor]
  exact Polynomial.natDegree_map_le

/-- The germ of the pullback of `f` is the image of the germ of `f` under the inclusion of
germ rings. -/
lemma germ_pullbackInit {y : Fin (n + 1) → ℂ} (hy : y ∈ V.extend') (f : OkaRing V) :
    germ hy (pullbackInit V f) =
      LocalOkaRing.renameSucc (germ (Opens.mem_extend'.mp hy) f) := by
  refine germ_eq_of_represents hy ?_
  have h1 : ((LocalOkaRing.renameSucc (germ (Opens.mem_extend'.mp hy) f) :
      LocalOkaRing (Fin (n + 1))) : MvPowerSeries (Fin (n + 1)) ℂ).Represents
      (fun x ↦ f.toGlobalFun _ (Fin.init x + Fin.init y)) := by
    rw [LocalOkaRing.coe_renameSucc]
    exact Represents.rename_castSucc (germ_represents (Opens.mem_extend'.mp hy) f)
  refine h1.congr ?_
  have hcont : Continuous (fun x : Fin (n + 1) → ℂ ↦ x + y) :=
    continuous_id.add continuous_const
  filter_upwards [IsOpen.mem_nhds (V.extend'.isOpen.preimage hcont)
    (show ((0 : Fin (n + 1) → ℂ) + y) ∈ V.extend' by rwa [zero_add])] with x hx
  have hx' : Fin.init (x + y) ∈ V := Opens.mem_extend'.mp hx
  rw [f.toGlobalFun_apply (show Fin.init x + Fin.init y ∈ V from hx'),
    (pullbackInit V f).toGlobalFun_apply hx]
  rfl

/-- The germ of the last coordinate function at `y` is `X_last + y_last`. -/
lemma germ_lastVar {y : Fin (n + 1) → ℂ} (hy : y ∈ V.extend') :
    germ hy (lastVar V) =
      LocalOkaRing.lastX + algebraMap ℂ (LocalOkaRing (Fin (n + 1))) (y (Fin.last n)) := by
  refine germ_eq_of_represents hy ?_
  have h1 : ((LocalOkaRing.lastX +
      algebraMap ℂ (LocalOkaRing (Fin (n + 1))) (y (Fin.last n)) : LocalOkaRing (Fin (n + 1))) :
      MvPowerSeries (Fin (n + 1)) ℂ).Represents
      ((fun z ↦ z (Fin.last n)) + Function.const _ (y (Fin.last n))) := by
    have h2 := (represents_X (ι := Fin (n + 1)) (Fin.last n)).add
      (represents_algebraMap (ι := Fin (n + 1)) (y (Fin.last n)))
    rw [AddMemClass.coe_add, LocalOkaRing.coe_lastX]
    exact h2
  refine h1.congr ?_
  have hcont : Continuous (fun x : Fin (n + 1) → ℂ ↦ x + y) :=
    continuous_id.add continuous_const
  filter_upwards [IsOpen.mem_nhds (V.extend'.isOpen.preimage hcont)
    (show ((0 : Fin (n + 1) → ℂ) + y) ∈ V.extend' by rwa [zero_add])] with z hz
  rw [(lastVar V).toGlobalFun_apply hz]
  rfl

/-- Key compatibility: the germ at `y` of the function attached to a polynomial `Q` is the
polynomial germ `OkaRing.germPoly` of `Q`, viewed as a germ via
`LocalOkaRing.fromPolynomial`. -/
theorem germ_toOkaRing {y : Fin (n + 1) → ℂ} (hy : y ∈ V.extend') (Q : (OkaRing V)[X]) :
    germ hy (Polynomial.toOkaRing V Q) =
      LocalOkaRing.fromPolynomial
        (germPoly (Opens.mem_extend'.mp hy) (y (Fin.last n)) Q) := by
  have key : (germ hy).toRingHom.comp (Polynomial.toOkaRing V).toRingHom =
      LocalOkaRing.fromPolynomial.toRingHom.comp
        (germPoly (Opens.mem_extend'.mp hy) (y (Fin.last n))).toRingHom := by
    refine Polynomial.ringHom_ext (fun a ↦ ?_) ?_
    · have hL : germ hy (Polynomial.toOkaRing V (Polynomial.C a)) =
          LocalOkaRing.renameSucc (germ (Opens.mem_extend'.mp hy) a) := by
        rw [Polynomial.toOkaRing_C]
        exact germ_pullbackInit hy a
      have hR : LocalOkaRing.fromPolynomial
          (germPoly (Opens.mem_extend'.mp hy) (y (Fin.last n)) (Polynomial.C a)) =
          LocalOkaRing.renameSucc (germ (Opens.mem_extend'.mp hy) a) := by
        rw [germPoly_apply, Polynomial.map_C, Polynomial.C_comp,
          LocalOkaRing.fromPolynomial_C]
        rfl
      simpa using hL.trans hR.symm
    · have hL : germ hy (Polynomial.toOkaRing V Polynomial.X) =
          LocalOkaRing.lastX +
            algebraMap ℂ (LocalOkaRing (Fin (n + 1))) (y (Fin.last n)) := by
        rw [Polynomial.toOkaRing_X]
        exact germ_lastVar hy
      have hR : LocalOkaRing.fromPolynomial
          (germPoly (Opens.mem_extend'.mp hy) (y (Fin.last n)) Polynomial.X) =
          LocalOkaRing.lastX +
            algebraMap ℂ (LocalOkaRing (Fin (n + 1))) (y (Fin.last n)) := by
        rw [germPoly_apply, Polynomial.map_X, Polynomial.X_comp, map_add,
          LocalOkaRing.fromPolynomial_X, LocalOkaRing.fromPolynomial_C]
        rw [AlgHom.commutes]
      simpa using hL.trans hR.symm
  have h9 := congrArg (fun Φ : (OkaRing V)[X] →+* LocalOkaRing (Fin (n + 1)) ↦ Φ Q) key
  simpa using h9

end OkaRing

namespace LocalOkaRing

open OkaRing TopologicalSpace

variable {ι : Type*} [Fintype ι] {n : ℕ}

/-- Every germ is realized by a holomorphic function on a neighbourhood of any prescribed
point. -/
lemma exists_okaRing_germ (P : LocalOkaRing ι) (y : ι → ℂ) :
    ∃ (W : Opens (ι → ℂ)) (hy : y ∈ W) (f : OkaRing W), OkaRing.germ hy f = P := by
  obtain ⟨U, h0, f₀, hf₀⟩ := LocalOkaRing.exists_okaRing P
  refine ⟨U.shift (-y), by simpa using h0, shift U (-y) f₀, ?_⟩
  rw [germ_shift (-y) h0 (by simpa using h0) (add_neg_cancel y) f₀, germ_zero_mem h0]
  exact hf₀

/-- Every polynomial over the germ ring is realized, coefficientwise, by a polynomial over the
holomorphic functions on a neighbourhood of any prescribed point. -/
lemma exists_poly_map_germ (g : (LocalOkaRing (Fin n))[X]) (y' : Fin n → ℂ) :
    ∃ (V : Opens (Fin n → ℂ)) (hy' : y' ∈ V) (Q : (OkaRing V)[X]),
      Q.map (OkaRing.germ hy').toRingHom = g ∧ Q.natDegree ≤ g.natDegree := by
  classical
  choose W hyW fc hfc using fun j : ℕ ↦ LocalOkaRing.exists_okaRing_germ (g.coeff j) y'
  set d := g.natDegree with hd
  set V : Opens (Fin n → ℂ) := (Finset.range (d + 1)).inf W with hV
  have hy' : y' ∈ V := Opens.mem_finset_inf.mpr fun j _ ↦ hyW j
  have hle : ∀ j, j ∈ Finset.range (d + 1) → V ≤ W j := fun j hj ↦ Finset.inf_le hj
  set c : ℕ → OkaRing V := fun j ↦
    if h : j ∈ Finset.range (d + 1) then OkaRing.restrict (hle j h) (fc j) else 0 with hc
  have hgerm : ∀ j ∈ Finset.range (d + 1), OkaRing.germ hy' (c j) = g.coeff j := by
    intro j hj
    rw [hc]
    simp only [dif_pos hj]
    rw [germ_restrict (hle j hj) hy' (fc j)]
    exact hfc j
  set Q : (OkaRing V)[X] :=
    ∑ j ∈ Finset.range (d + 1), Polynomial.C (c j) * Polynomial.X ^ j with hQ
  have hcoeff : ∀ k, Q.coeff k = if k ∈ Finset.range (d + 1) then c k else 0 := by
    intro k
    rw [hQ, Polynomial.finsetSum_coeff]
    have h1 : ∀ j ∈ Finset.range (d + 1),
        (Polynomial.C (c j) * Polynomial.X ^ j).coeff k = if j = k then c j else 0 := by
      intro j _
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      rcases eq_or_ne j k with rfl | hjk
      · simp
      · rw [if_neg (Ne.symm hjk), mul_zero, if_neg hjk]
    rw [Finset.sum_congr rfl h1, Finset.sum_ite_eq' (Finset.range (d + 1)) k c]
  have hQdeg : Q.natDegree ≤ d := by
    refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun N hN ↦ ?_
    rw [hcoeff]
    rw [if_neg (by simp; omega)]
  refine ⟨V, hy', Q, ?_, hQdeg⟩
  refine Polynomial.ext fun k ↦ ?_
  rw [Polynomial.coeff_map, hcoeff]
  by_cases hk : k ∈ Finset.range (d + 1)
  · rw [if_pos hk]
    exact hgerm k hk
  · rw [if_neg hk, map_zero]
    refine (Polynomial.coeff_eq_zero_of_natDegree_lt ?_).symm
    simp only [Finset.mem_range] at hk
    omega

/-- Monic refinement of `LocalOkaRing.exists_poly_map_germ`. -/
lemma exists_poly_map_germ_monic {g : (LocalOkaRing (Fin n))[X]} (hg : g.Monic)
    (y' : Fin n → ℂ) :
    ∃ (V : Opens (Fin n → ℂ)) (hy' : y' ∈ V) (Q : (OkaRing V)[X]),
      Q.map (OkaRing.germ hy').toRingHom = g ∧ Q.Monic ∧ Q.natDegree = g.natDegree := by
  obtain ⟨V, hy', Q₀, hmap, hdeg⟩ := exists_poly_map_germ g y'
  haveI : Nontrivial (OkaRing V) := OkaRing.nontrivial hy'
  set d := g.natDegree with hd
  set Q : (OkaRing V)[X] :=
    Q₀ + Polynomial.C (1 - Q₀.coeff d) * Polynomial.X ^ d with hQ
  have hcoeffd : Q.coeff d = 1 := by
    rw [hQ, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl,
      mul_one]
    ring
  have hQdeg : Q.natDegree ≤ d := by
    refine Polynomial.natDegree_add_le_of_degree_le hdeg ?_
    exact (Polynomial.natDegree_C_mul_le _ _).trans (by simp)
  have hmonic : Q.Monic := Polynomial.monic_of_natDegree_le_of_coeff_eq_one d hQdeg hcoeffd
  have hcd : (OkaRing.germ hy').toRingHom (Q₀.coeff d) = 1 := by
    have h3 := congrArg (fun p ↦ p.coeff d) hmap
    simp only [Polynomial.coeff_map] at h3
    rw [h3]
    exact hg
  refine ⟨V, hy', Q, ?_, hmonic, ?_⟩
  · rw [hQ, Polynomial.map_add, hmap, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow,
      Polynomial.map_X, map_sub, map_one, hcd, sub_self, Polynomial.C_0, zero_mul, add_zero]
  · refine le_antisymm hQdeg ?_
    exact Polynomial.le_natDegree_of_ne_zero (by rw [hcoeffd]; exact one_ne_zero)

open Polynomial in
/-- A local Weierstrass polynomial is the coefficientwise germ at the origin of a Weierstrass
polynomial over the holomorphic functions on a neighbourhood of the origin. -/
lemma exists_isWeierstrassPolynomial_realize {g : (LocalOkaRing (Fin n))[X]}
    (hg : IsLocalWeierstrassPolynomial
      (g.map (Subring.subtype (localOkaSubring (Fin n)).toSubring))) :
    ∃ (V : Opens (Fin n → ℂ)) (h0 : (0 : Fin n → ℂ) ∈ V) (Q : (OkaRing V)[X]),
      Q.map (OkaRing.germ h0).toRingHom = g ∧ IsWeierstrassPolynomial V Q := by
  have hinj : Function.Injective (Subring.subtype (localOkaSubring (Fin n)).toSubring) :=
    fun a b hab ↦ Subtype.ext hab
  have hgmonic : g.Monic := (Function.Injective.monic_map_iff hinj).mpr hg.monic
  obtain ⟨V, h0, Q, hmap, hQmonic, hQdeg⟩ := exists_poly_map_germ_monic hgmonic 0
  refine ⟨V, h0, Q, hmap, hQmonic, ?_⟩
  intro i hi
  have hi' : i < Q.natDegree := by
    have h1 := lt_of_lt_of_le hi Polynomial.degree_le_natDegree
    exact_mod_cast h1
  have hdeg2 : (i : WithBot ℕ) <
      (g.map (Subring.subtype (localOkaSubring (Fin n)).toSubring)).degree := by
    rw [Polynomial.degree_map_eq_of_injective hinj,
      Polynomial.degree_eq_natDegree hgmonic.ne_zero]
    exact_mod_cast hQdeg ▸ hi'
  have hzero := hg.apply_zero i hdeg2
  rw [Polynomial.coeff_map] at hzero
  have hgi : OkaRing.germ h0 (Q.coeff i) = g.coeff i := by
    have := congrArg (fun p ↦ p.coeff i) hmap
    simpa using this
  rw [(Q.coeff i).toGlobalFun_apply h0]
  have h5 : LocalOkaRing.constantCoeff (OkaRing.germ h0 (Q.coeff i)) =
      OkaRing.evalHom h0 (Q.coeff i) := OkaRing.constantCoeff_germ h0 (Q.coeff i)
  rw [hgi] at h5
  rw [show (Q.coeff i).toFun _ ⟨0, h0⟩ = OkaRing.evalHom h0 (Q.coeff i) from rfl, ← h5]
  exact hzero

end LocalOkaRing

end GermPoly

section Slice

/-- If the holomorphic function attached to a polynomial `P` vanishes near a point of the
cylinder, then the coefficients of `P` vanish on a neighbourhood of the base point: a
polynomial in the last variable vanishing on an open set vanishes coefficientwise. -/
lemma Polynomial.exists_map_restrict_eq_zero {V : Opens (Fin n → ℂ)} (P : (OkaRing V)[X])
    {W : Opens (Fin (n + 1) → ℂ)} (hWV : W ≤ V.extend') {y : Fin (n + 1) → ℂ} (hy : y ∈ W)
    (h : OkaRing.restrict hWV (Polynomial.toOkaRing V P) = 0) :
    ∃ (V' : Opens (Fin n → ℂ)) (hV' : V' ≤ V), Fin.init y ∈ V' ∧
      P.map (OkaRing.restrict hV').toRingHom = 0 := by
  classical
  obtain ⟨I, u, hu, hsub⟩ := isOpen_pi_iff.mp W.isOpen y hy
  set u' : Fin (n + 1) → Set ℂ := fun i ↦ if i ∈ I then u i else Set.univ with hu'
  have hu'open : ∀ i, IsOpen (u' i) := fun i ↦ by
    rw [hu']
    dsimp only
    split
    · exact (hu i ‹_›).1
    · exact isOpen_univ
  have hyu' : ∀ i, y i ∈ u' i := fun i ↦ by
    rw [hu']
    dsimp only
    split
    · exact (hu i ‹_›).2
    · trivial
  have hpi : ∀ x : Fin (n + 1) → ℂ, (∀ i, x i ∈ u' i) → x ∈ W := by
    intro x hx
    refine hsub fun i hi ↦ ?_
    have h1 := hx i
    rw [hu'] at h1
    dsimp only at h1
    rwa [if_pos (by simpa using hi)] at h1
  set B : Opens (Fin n → ℂ) := ⟨Set.pi Set.univ (fun i : Fin n ↦ u' i.castSucc),
    isOpen_set_pi Set.finite_univ fun i _ ↦ hu'open _⟩ with hB
  refine ⟨V ⊓ B, inf_le_left, ⟨Opens.mem_extend'.mp (hWV hy), fun i _ ↦ hyu' _⟩, ?_⟩
  refine Polynomial.ext fun k ↦ ?_
  rw [Polynomial.coeff_map, Polynomial.coeff_zero]
  apply OkaRing.ext
  funext z
  have hzV : z.1 ∈ V := z.2.1
  have hzB : ∀ i : Fin n, z.1 i ∈ u' i.castSucc := fun i ↦ z.2.2 i (Set.mem_univ i)
  -- the one variable polynomial at the base point `z`
  set pz : ℂ[X] := P.map (OkaRing.evalHom hzV) with hpz
  have hroots : ∀ ζ ∈ u' (Fin.last n), pz.IsRoot ζ := by
    intro ζ hζ
    have hxW : Fin.snoc z.1 ζ ∈ W := by
      refine hpi _ fun i ↦ ?_
      induction i using Fin.lastCases with
      | last => rwa [Fin.snoc_last]
      | cast j => rw [Fin.snoc_castSucc]; exact hzB j
    have h0 : OkaRing.evalHom hxW (OkaRing.restrict hWV (Polynomial.toOkaRing V P)) = 0 := by
      rw [h, map_zero]
    rw [OkaRing.evalHom_restrict, OkaRing.evalHom_toOkaRing (hWV hxW)] at h0
    have hpt : Fin.init (Fin.snoc z.1 ζ : Fin (n + 1) → ℂ) = z.1 := by simp
    have hcast : Polynomial.eval₂
        (OkaRing.evalHom (Opens.mem_extend'.mp (hWV hxW)))
        ((Fin.snoc z.1 ζ : Fin (n + 1) → ℂ) (Fin.last n)) P =
        Polynomial.eval₂ (OkaRing.evalHom hzV) ζ P := by
      have hhom : OkaRing.evalHom (U := V) (Opens.mem_extend'.mp (hWV hxW)) =
          OkaRing.evalHom hzV :=
        RingHom.ext fun a ↦ OkaRing.evalHom_congr _ _ hpt a
      rw [hhom, Fin.snoc_last]
    rw [hcast, Polynomial.eval₂_eq_eval_map] at h0
    exact h0
  have hinf : Set.Infinite (u' (Fin.last n)) :=
    infinite_of_mem_nhds (y (Fin.last n))
      ((hu'open (Fin.last n)).mem_nhds (hyu' (Fin.last n)))
  have hpz0 : pz = 0 :=
    Polynomial.eq_zero_of_infinite_isRoot pz (hinf.mono fun ζ hζ ↦ hroots ζ hζ)
  have hck : OkaRing.evalHom hzV (P.coeff k) = 0 := by
    have h2 := congrArg (fun p : ℂ[X] ↦ p.coeff k) hpz0
    simpa [hpz] using h2
  exact hck

end Slice

section LineDirection

/-!
### Choosing a good direction

Given finitely many nonzero germs at the origin, there is a direction `v`, not orthogonal to
the last coordinate axis, along which no germ vanishes identically. After the linear change of
coordinates `lineEquiv` this makes all the germs general in the last variable.
-/

open MvPowerSeries

variable {ι : Type*} [Fintype ι]

/-- If the function represented by `P` vanishes along the line spanned by `v` near the origin,
all homogeneous parts of `P` vanish at `v`. -/
theorem MvPowerSeries.Represents.homogeneous_eval_eq_zero [DecidableEq ι]
    {P : MvPowerSeries ι ℂ} {F : (ι → ℂ) → ℂ} (hP : P.Represents F) (v : ι → ℂ)
    (hv : ∀ᶠ t : ℂ in nhds 0, F (t • v) = 0) (k : ℕ) :
    ∑ d ∈ degFinset ι k, coeff d P * evalMonomial d v = 0 := by
  have hconv := hP.locallyConvergent
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hP.and hconv)
  set ρ : ℝ := ε / 2 with hρdef
  have hρ0 : 0 < ρ := by positivity
  have hmem : ∀ x : ι → ℂ, ‖x‖ ≤ ρ → HasSum (P.term x) (F x) ∧ P.SummableAt x := by
    intro x hx
    refine hball ?_
    rw [mem_ball_zero_iff]
    calc ‖x‖ ≤ ρ := hx
      _ < ε := by rw [hρdef]; linarith
  set l : ℝ := ρ / (‖v‖ + 1) with hl
  have hl0 : 0 < l := by positivity
  set y₀ : ι → ℂ := (l : ℂ) • v with hy₀
  have hy₀ρ : ‖y₀‖ ≤ ρ := by
    rw [hy₀, norm_smul, Complex.norm_real, Real.norm_of_nonneg hl0.le, hl,
      div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [norm_nonneg v, hρ0]
  -- the coefficients of the one variable restriction to the line through `y₀`
  set a : ℕ → ℂ := fun m ↦ ∑ d ∈ degFinset ι m, coeff d P * evalMonomial d y₀ with ha
  have ha0 : ∀ m, a m = 0 := by
    refine eq_zero_of_hasSum_zero (C := ∑' d, ‖P.term y₀ d‖) (fun m ↦ ?_) ?_
    · calc ‖a m‖ ≤ ∑ d ∈ degFinset ι m, ‖P.term y₀ d‖ := by
            rw [ha]
            exact (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun d _ ↦ rfl))
        _ ≤ ∑' d, ‖P.term y₀ d‖ :=
            le_hasSum (hasSum_degree_norm (hmem y₀ hy₀ρ).2) m fun _ _ ↦
              Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
    · have hcont : Filter.Tendsto (fun t : ℂ ↦ t * (l : ℂ)) (nhds 0) (nhds 0) := by
        have h1 : Continuous (fun t : ℂ ↦ t * (l : ℂ)) := continuous_id.mul continuous_const
        have h2 := h1.tendsto 0
        rwa [zero_mul] at h2
      filter_upwards [Metric.ball_mem_nhds (0 : ℂ) one_pos, hcont.eventually hv] with t ht htl
      rw [mem_ball_zero_iff] at ht
      have hty : ‖t • y₀‖ ≤ ρ := by
        rw [norm_smul]
        calc ‖t‖ * ‖y₀‖ ≤ 1 * ρ :=
              mul_le_mul ht.le hy₀ρ (norm_nonneg _) zero_le_one
          _ = ρ := one_mul ρ
      have hFty : F (t • y₀) = 0 := by
        have h3 : t • y₀ = (t * (l : ℂ)) • v := by rw [hy₀, smul_smul]
        rw [h3]
        exact htl
      have h4 := hasSum_degree (hmem (t • y₀) hty).1
      rw [hFty] at h4
      have hfun : (fun m ↦ ∑ d ∈ degFinset ι m, P.term (t • y₀) d) =
          fun m ↦ a m * t ^ m := by
        funext m
        rw [ha, Finset.sum_mul]
        refine Finset.sum_congr rfl fun d hd ↦ ?_
        rw [term, evalMonomial_smul, mem_degFinset.mp hd]
        ring
      rwa [hfun] at h4
  -- homogeneity in the scaling factor `l`
  have hk := ha0 k
  simp only [ha] at hk
  have h5 : ∑ d ∈ degFinset ι k, coeff d P * evalMonomial d y₀ =
      (l : ℂ) ^ k * ∑ d ∈ degFinset ι k, coeff d P * evalMonomial d v := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d hd ↦ ?_
    rw [hy₀, evalMonomial_smul, mem_degFinset.mp hd]
    ring
  rw [h5] at hk
  exact (mul_eq_zero.mp hk).resolve_left
    (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hl0.ne'))

/-- Finitely many nonzero power series admit a common direction `v`, transverse to the
hyperplane of the first `n` coordinates, at which some homogeneous part of each of them does
not vanish. -/
theorem MvPowerSeries.exists_direction {p : ℕ}
    (P : Fin p → MvPowerSeries (Fin (n + 1)) ℂ) (hP : ∀ i, P i ≠ 0) :
    ∃ v : Fin (n + 1) → ℂ, v (Fin.last n) ≠ 0 ∧
      ∀ i, ∃ k, ∑ d ∈ degFinset (Fin (n + 1)) k, coeff d (P i) * evalMonomial d v ≠ 0 := by
  classical
  have hex : ∀ i, ∃ d, coeff d (P i) ≠ 0 := fun i ↦ by
    by_contra hc
    push Not at hc
    exact hP i (MvPowerSeries.ext fun d ↦ by rw [hc d, map_zero])
  choose D hD using hex
  set k : Fin p → ℕ := fun i ↦ ∑ j, D i j with hk
  set hpol : Fin p → MvPolynomial (Fin (n + 1)) ℂ := fun i ↦
    ∑ e ∈ degFinset (Fin (n + 1)) (k i), MvPolynomial.monomial e (coeff e (P i)) with hhp
  have hh : ∀ i, hpol i ≠ 0 := by
    intro i hzero
    have h3 := congrArg (MvPolynomial.coeff (D i)) hzero
    rw [hhp] at h3
    simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial,
      MvPolynomial.coeff_zero] at h3
    rw [Finset.sum_ite_eq' (degFinset (Fin (n + 1)) (k i)) (D i)
      (fun e ↦ coeff e (P i))] at h3
    rw [if_pos (self_mem_degFinset (D i))] at h3
    exact hD i h3
  set q : MvPolynomial (Fin (n + 1)) ℂ := MvPolynomial.X (Fin.last n) * ∏ i, hpol i with hq
  have hq0 : q ≠ 0 :=
    mul_ne_zero (MvPolynomial.X_ne_zero _) (Finset.prod_ne_zero_iff.mpr fun i _ ↦ hh i)
  obtain ⟨v, hv⟩ : ∃ v, MvPolynomial.eval v q ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hq0 (MvPolynomial.funext fun v ↦ by rw [hc v, map_zero])
  rw [hq, map_mul, MvPolynomial.eval_X, map_prod] at hv
  have hvlast : v (Fin.last n) ≠ 0 := left_ne_zero_of_mul hv
  have hvh : ∀ i, MvPolynomial.eval v (hpol i) ≠ 0 := fun i ↦
    Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul hv) i (Finset.mem_univ i)
  refine ⟨v, hvlast, fun i ↦ ⟨k i, ?_⟩⟩
  have heval : MvPolynomial.eval v (hpol i) =
      ∑ e ∈ degFinset (Fin (n + 1)) (k i), coeff e (P i) * evalMonomial e v := by
    rw [hhp]
    dsimp only
    rw [map_sum]
    refine Finset.sum_congr rfl fun e _ ↦ ?_
    rw [MvPolynomial.eval_monomial]
    rfl
  rw [← heval]
  exact hvh i

set_option linter.unusedFintypeInType false in
/-- If the partial evaluation of `P` along the `i`-th axis vanishes, so does the represented
function along that axis, near the origin. -/
theorem MvPowerSeries.Represents.eventually_axis_eq_zero [DecidableEq ι]
    {P : MvPowerSeries ι ℂ}
    {F : (ι → ℂ) → ℂ} (hP : P.Represents F) (i : ι) (h : partialEval i P = 0) :
    ∀ᶠ t : ℂ in nhds 0, F (t • Pi.single i 1) = 0 := by
  classical
  have htend : Filter.Tendsto (fun t : ℂ ↦ t • Pi.single i (1 : ℂ)) (nhds 0) (nhds 0) := by
    have h1 : Continuous (fun t : ℂ ↦ t • Pi.single i (1 : ℂ)) :=
      continuous_id.smul continuous_const
    have h2 := h1.tendsto 0
    rwa [zero_smul] at h2
  filter_upwards [htend.eventually hP] with t ht
  have hvan : ∀ d ∉ Set.range (fun m : ℕ ↦ Finsupp.single i m),
      P.term (t • Pi.single i (1 : ℂ)) d = 0 := by
    intro d hd
    have hj : ∃ j, j ≠ i ∧ d j ≠ 0 := by
      by_contra hc
      push Not at hc
      refine hd ⟨d i, ?_⟩
      change Finsupp.single i (d i) = d
      refine Finsupp.ext fun j ↦ ?_
      rcases eq_or_ne j i with rfl | hj
      · rw [Finsupp.single_eq_same]
      · rw [Finsupp.single_apply, if_neg fun hij ↦ hj hij.symm]
        exact (hc j hj).symm
    obtain ⟨j, hji, hdj⟩ := hj
    rw [term]
    have hev : evalMonomial d (t • Pi.single i (1 : ℂ)) = 0 := by
      rw [evalMonomial_eq_prod]
      refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
      rw [Pi.smul_apply, Pi.single_eq_of_ne hji, smul_zero]
      exact zero_pow hdj
    rw [hev, mul_zero]
  have h2 := (Function.Injective.hasSum_iff (Finsupp.single_injective i) hvan).mpr ht
  have hfun : P.term (t • Pi.single i (1 : ℂ)) ∘ (fun m : ℕ ↦ Finsupp.single i m) =
      fun _ ↦ (0 : ℂ) := by
    funext m
    rw [Function.comp_apply, term]
    have hc : coeff (Finsupp.single i m) P = 0 := by
      have h3 := congrArg (PowerSeries.coeff m) h
      rwa [coeff_partialEval, map_zero] at h3
    rw [hc, zero_mul]
  rw [hfun] at h2
  exact (h2.unique hasSum_zero).symm ▸ rfl

/-- A linear automorphism of `ℂ^{n+1}` whose inverse maps the last coordinate axis onto the
line spanned by a vector `v` with `v_last ≠ 0`. -/
noncomputable def lineEquiv (v : Fin (n + 1) → ℂ) (hv : v (Fin.last n) ≠ 0) :
    (Fin (n + 1) → ℂ) ≃L[ℂ] (Fin (n + 1) → ℂ) := by
  refine (LinearEquiv.ofLinear
    (LinearMap.id - (LinearMap.proj (Fin.last n)).smulRight
      ((v (Fin.last n))⁻¹ • (v - Pi.single (Fin.last n) 1)))
    (LinearMap.id + (LinearMap.proj (Fin.last n)).smulRight (v - Pi.single (Fin.last n) 1))
    ?_ ?_).toContinuousLinearEquiv
  · -- τ ∘ σ = id
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.id_apply, LinearMap.smulRight_apply, LinearMap.proj_apply]
    have hlast : (x + x (Fin.last n) • (v - Pi.single (Fin.last n) (1 : ℂ)) :
        Fin (n + 1) → ℂ) (Fin.last n) = x (Fin.last n) * v (Fin.last n) := by
      rw [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.single_eq_same, smul_eq_mul]
      ring
    rw [hlast, smul_smul]
    have hcoeff : x (Fin.last n) * v (Fin.last n) * (v (Fin.last n))⁻¹ = x (Fin.last n) := by
      field_simp
    rw [hcoeff, add_sub_cancel_right]
  · -- σ ∘ τ = id
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.id_apply, LinearMap.smulRight_apply, LinearMap.proj_apply]
    have hlast : (x - x (Fin.last n) •
        ((v (Fin.last n))⁻¹ • (v - Pi.single (Fin.last n) (1 : ℂ))) :
        Fin (n + 1) → ℂ) (Fin.last n) = x (Fin.last n) * (v (Fin.last n))⁻¹ := by
      rw [Pi.sub_apply, Pi.smul_apply, Pi.smul_apply, Pi.sub_apply, Pi.single_eq_same,
        smul_eq_mul, smul_eq_mul]
      field_simp
      ring
    rw [hlast, smul_smul, sub_add_cancel]

/-- The inverse of `lineEquiv` sends the last coordinate axis to the line spanned by `v`. -/
lemma lineEquiv_symm_smul_single (v : Fin (n + 1) → ℂ) (hv : v (Fin.last n) ≠ 0) (t : ℂ) :
    (lineEquiv v hv).symm (t • Pi.single (Fin.last n) 1) = t • v := by
  rw [ContinuousLinearEquiv.symm_apply_eq]
  change t • Pi.single (Fin.last n) (1 : ℂ) =
    t • v - (t • v) (Fin.last n) • ((v (Fin.last n))⁻¹ • (v - Pi.single (Fin.last n) (1 : ℂ)))
  rw [Pi.smul_apply, smul_eq_mul, smul_smul, mul_assoc, mul_inv_cancel₀ hv, mul_one,
    smul_sub, sub_sub_cancel]

end LineDirection

section GermPolyMore

open MvPowerSeries

variable {n : ℕ}

/-- Being a member of `Polynomial.degreeLT R d` bounds the `natDegree` when `0 < d`. -/
lemma Polynomial.natDegree_lt_of_mem_degreeLT {R : Type*} [CommRing R] {d : ℕ} (hd : 0 < d)
    {g : R[X]} (hg : g ∈ Polynomial.degreeLT R d) : g.natDegree < d := by
  rcases eq_or_ne g 0 with rfl | hg0
  · simpa using hd
  · exact (Polynomial.natDegree_lt_iff_degree_lt hg0).mpr (Polynomial.mem_degreeLT.mp hg)

namespace OkaRing

variable {V : Opens (Fin n → ℂ)} {y' : Fin n → ℂ}

/-- Taking polynomial germs commutes with restriction of the coefficients. -/
lemma germPoly_map_restrict {V' : Opens (Fin n → ℂ)} (h : V' ≤ V) (hy' : y' ∈ V') (w : ℂ)
    (R : (OkaRing V)[X]) :
    germPoly hy' w (R.map (restrict h).toRingHom) = germPoly (h hy') w R := by
  rw [germPoly_eq_taylor, germPoly_eq_taylor, Polynomial.map_map]
  have hcomp : (germ hy').toRingHom.comp (restrict h).toRingHom = (germ (h hy')).toRingHom :=
    RingHom.ext fun a ↦ germ_restrict h hy' a
  rw [hcomp]

end OkaRing

namespace LocalOkaRing

open OkaRing

/-- Every polynomial over the germ ring arises as the polynomial germ, at any prescribed point
of the cylinder, of a polynomial over the holomorphic functions near the base point. -/
lemma exists_poly_germPoly (g : (LocalOkaRing (Fin n))[X]) (y' : Fin n → ℂ) (w : ℂ) :
    ∃ (V' : Opens (Fin n → ℂ)) (hy' : y' ∈ V') (R : (OkaRing V')[X]),
      OkaRing.germPoly hy' w R = g ∧ R.natDegree ≤ g.natDegree := by
  obtain ⟨V', hy', R, hmap, hdeg⟩ :=
    exists_poly_map_germ
      (Polynomial.taylor (-(algebraMap ℂ (LocalOkaRing (Fin n)) w)) g) y'
  refine ⟨V', hy', R, ?_, by rwa [Polynomial.natDegree_taylor] at hdeg⟩
  rw [OkaRing.germPoly_eq_taylor, hmap, Polynomial.taylor_taylor, add_neg_cancel,
    Polynomial.taylor_zero]

end LocalOkaRing

/-- Weierstrass polynomials restrict to Weierstrass polynomials. -/
lemma IsWeierstrassPolynomial.map_restrict {V V' : Opens (Fin n → ℂ)} (h : V' ≤ V)
    (h0 : (0 : Fin n → ℂ) ∈ V') {Q : (OkaRing V)[X]} (hQ : IsWeierstrassPolynomial V Q) :
    IsWeierstrassPolynomial V' (Q.map (OkaRing.restrict h).toRingHom) := by
  haveI : Nontrivial (OkaRing V') := OkaRing.nontrivial h0
  haveI : Nontrivial (OkaRing V) := OkaRing.nontrivial (h h0)
  have hdeg : (Q.map (OkaRing.restrict h).toRingHom).degree = Q.degree := by
    rw [Polynomial.degree_eq_natDegree
        (hQ.monic.map (OkaRing.restrict h).toRingHom).ne_zero,
      Polynomial.degree_eq_natDegree hQ.monic.ne_zero,
      hQ.monic.natDegree_map]
  refine ⟨hQ.monic.map _, fun j hj ↦ ?_⟩
  rw [hdeg] at hj
  have hzero := hQ.apply_zero j hj
  rw [(Q.coeff j).toGlobalFun_apply (h h0)] at hzero
  rw [Polynomial.coeff_map, OkaRing.toGlobalFun_apply _ h0]
  exact hzero

end GermPolyMore
