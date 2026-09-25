/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytic.Puiseux
import Oka.Analytification.RET.ES.Codim2.BlowupChart
import Oka.Analytification.RET.ES.Codim2.GraphInduction
import Oka.Analytification.RET.ES.Codim2.RestrictCover
import Oka.Analytification.RET.ES.Codim2.DescentBaseChange

/-!
# The branch locus near a b-point after Puiseux base change

Let `t = x_{i_t}` and `w = x_{i_w}` be two coordinates of `ℂⁿ` and let `P` be a monic polynomial in
`w` whose coefficients are holomorphic functions of the other coordinates on a region
`{x | x' ∈ G, |t| < r}`, `x'` the point `x` with `t = w = 0` and `G` convex, such that `P` is
separable over `t ≠ 0` (`ComplexAnalytic.BoundedSections.BPointData`). The zero set of `P` is the
branch locus near a *b-point*.

After the Puiseux base change `α : t ↦ tˢ` of `Puiseux.exists_prod_eq_of_radius`, `P` splits as
`∏ⱼ (w - φⱼ(x', t))` with branches `φⱼ` which are disjoint over `t ≠ 0`
(`ComplexAnalytic.BoundedSections.BPointData.PuiseuxData`). Hence the preimage of
`N ∖ N° ∪ {t = 0}` is a graph configuration (`…BPointData.PuiseuxData.config`).

## Main definitions

- `ComplexAnalytic.BoundedSections.BPointData`: the data at a b-point.
- `ComplexAnalytic.BoundedSections.BPointData.PuiseuxData`: a Puiseux splitting of `P`.
- `ComplexAnalytic.BoundedSections.BPointData.PuiseuxData.config`: the graph configuration after
  base change.
-/

open CategoryTheory Opposite AlgebraicGeometry Topology TopologicalSpace Filter Set Metric
  Polynomial Kummer

universe u

namespace ComplexAnalytic.BoundedSections

open AnalyticSpace

noncomputable section

variable {n : ℕ}

/-- The point `x` with the coordinates `t` and `w` set to `0`. -/
def baseProj (it iw : ULift.{u} (Fin n)) (x : Cn.{u} n) : Cn.{u} n :=
  Function.update (Function.update x it 0) iw 0

section BaseProj

variable {it iw : ULift.{u} (Fin n)}

lemma baseProj_apply (x : Cn.{u} n) (j : ULift.{u} (Fin n)) :
    baseProj it iw x j = if j = iw ∨ j = it then 0 else x j := by
  by_cases hw : j = iw
  · subst hw
    simp [baseProj]
  · by_cases ht : j = it
    · subst ht
      simp [baseProj, Function.update_of_ne hw]
    · simp [baseProj, hw, ht]

lemma baseProj_update_iw (x : Cn.{u} n) (a : ℂ) :
    baseProj it iw (Function.update x iw a) = baseProj it iw x := by
  funext j
  simp only [baseProj_apply]
  split_ifs with h
  · rfl
  · rw [Function.update_of_ne (not_or.1 h).1]

lemma baseProj_update_it (x : Cn.{u} n) (a : ℂ) :
    baseProj it iw (Function.update x it a) = baseProj it iw x := by
  funext j
  simp only [baseProj_apply]
  split_ifs with h
  · rfl
  · rw [Function.update_of_ne (not_or.1 h).2]

lemma baseProj_baseProj (x : Cn.{u} n) : baseProj it iw (baseProj it iw x) = baseProj it iw x := by
  funext j
  simp only [baseProj_apply]
  split_ifs <;> rfl

lemma baseProj_coordPow (s : ℕ) (x : Cn.{u} n) :
    baseProj it iw (coordPow it s x) = baseProj it iw x :=
  baseProj_update_it x _

lemma differentiable_baseProj : Differentiable ℂ (baseProj (n := n) it iw) :=
  differentiableOn_univ.1 (differentiableOn_update (differentiableOn_update differentiableOn_id
    (differentiableOn_const 0) it) (differentiableOn_const 0) iw)

lemma update_baseProj_it (hne : it ≠ iw) (x : Cn.{u} n) :
    Function.update (baseProj it iw x) it (x it) = Function.update x iw 0 := by
  funext j
  by_cases ht : j = it
  · subst ht
    simp [Function.update_of_ne hne]
  · rw [Function.update_of_ne ht, baseProj_apply]
    by_cases hw : j = iw
    · subst hw
      simp
    · simp [hw, ht]

end BaseProj

/-- **The data at a b-point.** Two coordinates `t`, `w` and a monic polynomial `P` in `w` whose
coefficients are independent of `w` and holomorphic on the region `R = {x | x' ∈ G, |t| < r}`,
where `x' = baseProj t w x` and `G` is convex and open, such that `P(x)` is separable for
`x ∈ R` with `t ≠ 0`, and such that `N ⊆ R` and `N°` is the complement in `N` of the zero set of
`P(x)(w)`. -/
structure BPointData (N N₀ : (AnalyticSpace.complexAffineSpace.{u} n).Opens) where
  /-- The coordinate `t`. -/
  it : ULift.{u} (Fin n)
  /-- The coordinate `w`. -/
  iw : ULift.{u} (Fin n)
  it_ne_iw : it ≠ iw
  /-- The polynomial. -/
  P : Polynomial (Cn.{u} n → ℂ)
  monic : P.Monic
  coeff_update : ∀ k x a, P.coeff k (Function.update x iw a) = P.coeff k x
  /-- The region of the parameters. -/
  G : Set (Cn.{u} n)
  convex : Convex ℝ G
  isOpen : IsOpen G
  /-- The radius in `t`. -/
  r : ℝ
  pos : 0 < r
  mem_region : ∀ x : Cn.{u} n, x ∈ N → baseProj it iw x ∈ G ∧ ‖x it‖ < r
  differentiableOn_coeff : ∀ k, DifferentiableOn ℂ (P.coeff k)
    {x | baseProj it iw x ∈ G ∧ ‖x it‖ < r}
  separable : ∀ x, baseProj it iw x ∈ G → ‖x it‖ < r → x it ≠ 0 →
    (P.map (Pi.evalRingHom (fun _ ↦ ℂ) x)).Separable
  mem_iff : ∀ x : Cn.{u} n, x ∈ N →
    (x ∈ N₀ ↔ (P.map (Pi.evalRingHom (fun _ ↦ ℂ) x)).eval (x iw) ≠ 0)

namespace BPointData

variable {N N₀ : (AnalyticSpace.complexAffineSpace.{u} n).Opens} (d : BPointData N N₀)

/-- The value `P(x)(w)`. -/
def val (x : Cn.{u} n) : ℂ :=
  (d.P.map (Pi.evalRingHom (fun _ ↦ ℂ) x)).eval (x d.iw)

lemma map_update (x : Cn.{u} n) (a : ℂ) :
    d.P.map (Pi.evalRingHom (fun _ ↦ ℂ) (Function.update x d.iw a)) =
      d.P.map (Pi.evalRingHom (fun _ ↦ ℂ) x) := by
  ext k
  simp [d.coeff_update]

lemma val_update (x : Cn.{u} n) (a : ℂ) :
    d.val (Function.update x d.iw a) = (d.P.map (Pi.evalRingHom (fun _ ↦ ℂ) x)).eval a := by
  rw [val, map_update, Function.update_self]

lemma map_ne_zero (x : Cn.{u} n) : d.P.map (Pi.evalRingHom (fun _ ↦ ℂ) x) ≠ 0 :=
  (d.monic.map _).ne_zero

/-- A nonzero polynomial does not vanish identically near any point. -/
lemma not_eventually_eval_eq_zero {q : ℂ[X]} (hq : q ≠ 0) (c : ℂ) :
    ¬ ∀ᶠ ε in 𝓝 (0 : ℂ), q.eval (c + ε) = 0 := by
  intro h
  have hinf : {ε : ℂ | q.eval (c + ε) = 0}.Infinite := infinite_of_mem_nhds 0 h
  refine hq (Polynomial.eq_zero_of_infinite_isRoot q ?_)
  have : (fun ε ↦ c + ε) '' {ε : ℂ | q.eval (c + ε) = 0} ⊆ {a | q.IsRoot a} := by
    rintro _ ⟨ε, hε, rfl⟩
    exact hε
  exact ((hinf.image (add_right_injective c).injOn)).mono this

/-- `P(x)(w)` does not vanish identically along the line through `x` in the direction of `w`. -/
lemma not_eventually_val (x : Cn.{u} n) : ¬ ∀ᶠ y in 𝓝 x, y d.it = x d.it → d.val y = 0 := by
  intro h
  have ht : Tendsto (fun ε : ℂ ↦ Function.update x d.iw (x d.iw + ε)) (𝓝 0) (𝓝 x) := by
    have hc : Continuous fun ε : ℂ ↦ Function.update x d.iw (x d.iw + ε) :=
      continuous_const.update d.iw (continuous_const.add continuous_id)
    simpa using hc.tendsto 0
  refine not_eventually_eval_eq_zero (d.map_ne_zero x) (x d.iw) ?_
  filter_upwards [ht.eventually h] with ε hε
  rw [← d.val_update]
  exact hε (Function.update_of_ne d.it_ne_iw _ _)

/-- The region `R = {x | x' ∈ G, |t| < r}`. -/
def region : Set (Cn.{u} n) :=
  {x | baseProj d.it d.iw x ∈ d.G ∧ ‖x d.it‖ < d.r}

lemma isOpen_region : IsOpen d.region :=
  (d.isOpen.preimage differentiable_baseProj.continuous).inter
    (isOpen_lt (continuous_apply d.it).norm continuous_const)

lemma differentiableOn_val : DifferentiableOn ℂ d.val d.region := by
  have h : ∀ x, d.val x = ∑ k ∈ Finset.range (d.P.natDegree + 1), d.P.coeff k x * x d.iw ^ k :=
    fun x ↦ by
      rw [val, eval_eq_sum_range, d.monic.natDegree_map]
      simp [coeff_map]
  have : d.val = fun x ↦ ∑ k ∈ Finset.range (d.P.natDegree + 1), d.P.coeff k x * x d.iw ^ k :=
    funext h
  rw [this]
  exact DifferentiableOn.fun_sum fun k _ ↦ (d.differentiableOn_coeff k).mul
    ((differentiable_apply d.iw).pow k).differentiableOn

lemma subset_region : ∀ x ∈ N, x ∈ d.region :=
  d.mem_region

/-! ### The polynomial in the variables `(x', t)` -/

/-- The point with parameters `x'` and `t`. -/
def sec (p : Cn.{u} n × ℂ) : Cn.{u} n :=
  Function.update (baseProj d.it d.iw p.1) d.it p.2

/-- The polynomial `P` as a polynomial with coefficients functions of `(x', t)`. -/
def Q : Polynomial (Cn.{u} n × ℂ → ℂ) :=
  d.P.map (RingHom.pi fun p ↦ Pi.evalRingHom (fun _ ↦ ℂ) (d.sec p))

lemma Q_coeff (k : ℕ) (p : Cn.{u} n × ℂ) : d.Q.coeff k p = d.P.coeff k (d.sec p) := by
  rw [Q, coeff_map]
  rfl

lemma Q_monic : d.Q.Monic :=
  d.monic.map _

lemma Q_map_eval (p : Cn.{u} n × ℂ) :
    d.Q.map (Pi.evalRingHom (fun _ ↦ ℂ) p) = d.P.map (Pi.evalRingHom (fun _ ↦ ℂ) (d.sec p)) := by
  ext k
  simp [Q_coeff]

lemma sec_baseProj (x : Cn.{u} n) (t : ℂ) : d.sec (baseProj d.it d.iw x, t) = d.sec (x, t) := by
  simp [sec, baseProj_baseProj]

lemma P_map_eq (x : Cn.{u} n) : d.P.map (Pi.evalRingHom (fun _ ↦ ℂ) x) =
    d.Q.map (Pi.evalRingHom (fun _ ↦ ℂ) (baseProj d.it d.iw x, x d.it)) := by
  rw [Q_map_eval, sec_baseProj, sec, update_baseProj_it d.it_ne_iw, map_update]

/-- The parameter region `x' ∈ G`, as a subset of `ℂⁿ`. -/
def G' : Set (Cn.{u} n) :=
  baseProj d.it d.iw ⁻¹' d.G

lemma convex_G' : Convex ℝ d.G' := by
  have hlin : IsLinearMap ℝ (baseProj (n := n) d.it d.iw) := by
    constructor
    · intro x y
      funext j
      simp only [baseProj, Pi.add_apply]
      by_cases hw : j = d.iw
      · subst hw; simp
      by_cases ht : j = d.it
      · subst ht; simp [Function.update_of_ne hw]
      · simp [Function.update_of_ne hw, Function.update_of_ne ht]
    · intro c x
      funext j
      simp only [baseProj, Pi.smul_apply]
      by_cases hw : j = d.iw
      · subst hw; simp
      by_cases ht : j = d.it
      · subst ht; simp [Function.update_of_ne hw]
      · simp [Function.update_of_ne hw, Function.update_of_ne ht]
  exact d.convex.is_linear_preimage hlin

lemma isOpen_G' : IsOpen d.G' :=
  d.isOpen.preimage differentiable_baseProj.continuous

lemma sec_mem_region {p : Cn.{u} n × ℂ} (hp : p.1 ∈ d.G') (ht : ‖p.2‖ < d.r) :
    d.sec p ∈ d.region := by
  refine ⟨?_, ?_⟩
  · rw [sec, baseProj_update_it, baseProj_baseProj]
    exact hp
  · rwa [sec, Function.update_self]

lemma differentiableOn_Q_coeff (k : ℕ) :
    DifferentiableOn ℂ (d.Q.coeff k) (d.G' ×ˢ ball 0 d.r) := by
  have hsec : Differentiable ℂ d.sec := differentiableOn_univ.1
    (differentiableOn_update (fun e _ ↦ ((differentiable_baseProj (it := d.it) (iw := d.iw)
      e.1).comp e differentiableAt_fst).differentiableWithinAt)
      differentiable_snd.differentiableOn d.it)
  have : d.Q.coeff k = fun p ↦ d.P.coeff k (d.sec p) := funext (d.Q_coeff k)
  rw [this]
  exact (d.differentiableOn_coeff k).comp hsec.differentiableOn fun p hp ↦
    d.sec_mem_region hp.1 (mem_ball_zero_iff.1 hp.2)

lemma separable_Q {y : Cn.{u} n} (hy : y ∈ d.G') {x : ℂ} (hx : x ≠ 0) (hxr : ‖x‖ < d.r) :
    (d.Q.map (Pi.evalRingHom (fun _ ↦ ℂ) (y, x))).Separable := by
  rw [Q_map_eval]
  have hmem := d.sec_mem_region (p := (y, x)) hy hxr
  refine d.separable _ hmem.1 hmem.2 ?_
  rwa [sec, Function.update_self]

/-! ### Puiseux splittings -/

/-- **A Puiseux splitting of `P`**: after `t = τˢ`, `P` is `∏ⱼ (w - φⱼ(x', τ))` with branches
disjoint over `τ ≠ 0`. -/
structure PuiseuxData where
  /-- The ramification index. -/
  s : ℕ
  pos : 0 < s
  /-- The radius in `τ`. -/
  ρ : ℝ
  ρ_pos : 0 < ρ
  pow_ρ : ρ ^ s = d.r
  /-- The branches. -/
  φ : Fin d.Q.natDegree → Cn.{u} n × ℂ → ℂ
  differentiableOn : ∀ j, DifferentiableOn ℂ (φ j) (d.G' ×ˢ ball 0 ρ)
  prod_eq : ∀ y ∈ d.G', ∀ t ∈ ball (0 : ℂ) ρ,
    d.Q.map (Pi.evalRingHom (fun _ ↦ ℂ) (y, t ^ s)) = ∏ j, (X - C (φ j (y, t)))
  injective : ∀ y ∈ d.G', ∀ t : ℂ, t ≠ 0 → ‖t‖ < ρ → Function.Injective fun j ↦ φ j (y, t)

/-- **Puiseux splittings exist.** -/
theorem nonempty_puiseuxData : Nonempty d.PuiseuxData := by
  obtain ⟨s, ρ, φ, hρ, hρs, hφd, hprod, -, hinj⟩ := Puiseux.exists_prod_eq_of_radius
    d.convex_G' d.isOpen_G' d.pos d.Q_monic d.differentiableOn_Q_coeff
    fun y hy x hx hxr ↦ d.separable_Q hy hx hxr
  exact ⟨⟨s, s.pos, ρ, hρ, hρs, φ, hφd, hprod, fun y hy t ht htr ↦ hinj y hy t ht htr⟩⟩

/-! ### The graph configuration after base change -/

/-- The part `N° ∩ {t ≠ 0}` of `N°`. -/
def N₀t : (AnalyticSpace.complexAffineSpace.{u} n).Opens :=
  N₀ ⊓ ⟨{x : Cn.{u} n | x d.it ≠ 0}, isOpen_ne_fun (continuous_apply d.it) continuous_const⟩

lemma mem_N₀t {x : Cn.{u} n} : x ∈ d.N₀t ↔ x ∈ N₀ ∧ x d.it ≠ 0 :=
  Iff.rfl

lemma N₀t_le : d.N₀t ≤ N₀ :=
  inf_le_left

namespace PuiseuxData

variable {d} (D : d.PuiseuxData)

/-- The open `α⁻¹(N)` for the Puiseux map `α : t ↦ tˢ`. -/
def N' : (AnalyticSpace.complexAffineSpace.{u} n).Opens :=
  ⟨coordPow d.it D.s ⁻¹' {x | x ∈ N}, (isOpen_setOf_mem N).preimage (continuous_coordPow _)⟩

/-- The open `α⁻¹(N° ∩ {t ≠ 0})`. -/
def N₀' : (AnalyticSpace.complexAffineSpace.{u} n).Opens :=
  ⟨coordPow d.it D.s ⁻¹' {x | x ∈ d.N₀t}, (isOpen_setOf_mem _).preimage (continuous_coordPow _)⟩

lemma mem_N' {x : Cn.{u} n} : x ∈ D.N' ↔ coordPow d.it D.s x ∈ N :=
  Iff.rfl

lemma mem_N₀' {x : Cn.{u} n} : x ∈ D.N₀' ↔ coordPow d.it D.s x ∈ d.N₀t :=
  Iff.rfl

lemma N₀'_le (h₀ : N₀ ≤ N) : D.N₀' ≤ D.N' :=
  fun _ hx ↦ h₀ (d.N₀t_le hx)

lemma mem_N₀'_iff (x : Cn.{u} n) : x ∈ D.N₀' ↔ coordPow d.it D.s x ∈ d.N₀t :=
  Iff.rfl

/-- The branches `w = φⱼ(x', t)` as functions on `ℂⁿ`. -/
def ψ (j : Fin d.Q.natDegree) (x : Cn.{u} n) : ℂ :=
  D.φ j (baseProj d.it d.iw x, x d.it)

lemma pow_lt_iff {a : ℂ} : ‖a‖ ^ D.s < d.r ↔ ‖a‖ < D.ρ := by
  rw [← D.pow_ρ]
  exact pow_lt_pow_iff_left₀ (norm_nonneg a) D.ρ_pos.le D.pos.ne'

lemma mem_of_mem_cyl {x : Cn.{u} n} (hx : x ∈ cyl D.N' d.iw) :
    (baseProj d.it d.iw x, x d.it) ∈ d.G' ×ˢ ball (0 : ℂ) D.ρ := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨h₁, h₂⟩ := d.mem_region _ ((D.mem_N').1 ha)
  refine ⟨?_, ?_⟩
  · change baseProj d.it d.iw (baseProj d.it d.iw x) ∈ d.G
    rwa [baseProj_baseProj, ← baseProj_update_iw x a, ← baseProj_coordPow D.s]
  · rw [coordPow_self, Function.update_of_ne d.it_ne_iw, norm_pow, D.pow_lt_iff] at h₂
    exact mem_ball_zero_iff.2 h₂

lemma differentiableOn_ψ (j : Fin d.Q.natDegree) :
    DifferentiableOn ℂ (D.ψ j) (cyl D.N' d.iw) := by
  have hm : Differentiable ℂ fun x : Cn.{u} n ↦ ((baseProj d.it d.iw x, x d.it) : Cn.{u} n × ℂ) :=
    differentiable_baseProj.prodMk (differentiable_apply d.it)
  exact (D.differentiableOn j).comp hm.differentiableOn fun x hx ↦ D.mem_of_mem_cyl hx

lemma exists_contact : ∃ k : Fin d.Q.natDegree → Fin d.Q.natDegree → ℕ,
    Codim2.IsContactFamily (d.G' ×ˢ ball 0 D.ρ) D.φ k :=
  Codim2.isContactFamily_of_injective d.isOpen_G' d.convex_G'.isPreconnected D.differentiableOn
    fun z hz hz0 ↦ D.injective z.1 hz.1 z.2 hz0 (mem_ball_zero_iff.1 hz.2)

lemma prod_eq_of_mem {x : Cn.{u} n} (hx : x ∈ cyl D.N' d.iw) :
    d.P.map (Pi.evalRingHom (fun _ ↦ ℂ) (coordPow d.it D.s x)) = ∏ j, (X - C (D.ψ j x)) := by
  have hmem := D.mem_of_mem_cyl hx
  rw [d.P_map_eq, baseProj_coordPow, coordPow_self]
  exact D.prod_eq _ hmem.1 _ hmem.2

lemma mem_N₀'_iff_graphs (x : Cn.{u} n) (hx : x ∈ D.N') :
    x ∈ D.N₀' ↔ x d.it ≠ 0 ∧ ∀ j, x d.iw ≠ D.ψ j x := by
  have hcyl : x ∈ cyl D.N' d.iw := mem_cyl_of_mem hx
  refine ((D.mem_N₀'_iff x).trans d.mem_N₀t).trans ?_
  refine (and_congr (d.mem_iff _ ((D.mem_N').1 hx)) Iff.rfl).trans ?_
  rw [coordPow_self, coordPow_of_ne _ _ d.it_ne_iw.symm, D.prod_eq_of_mem hcyl,
    eval_prod, Finset.prod_ne_zero_iff, and_comm, pow_ne_zero_iff D.pos.ne']
  simp [sub_eq_zero]

/-- **The graph configuration after base change**: over `α⁻¹(N)`, the complement of
`α⁻¹(N° ∩ {t ≠ 0})` is `{t = 0}` together with the graphs `w = φⱼ(x', t)`. -/
def config : GraphConfig D.N' D.N₀' where
  it := d.it
  iw := d.iw
  it_ne_iw := d.it_ne_iw
  m := d.Q.natDegree
  ψ := D.ψ
  ψ_update j x a := by
    simp only [ψ, baseProj_update_iw, Function.update_of_ne d.it_ne_iw]
  differentiableOn_ψ := D.differentiableOn_ψ
  k := D.exists_contact.choose
  exists_unit i j hij := by
    obtain ⟨u, hu, hu0, hψu⟩ := D.exists_contact.choose_spec.exists_unit i j hij
    have hm : Differentiable ℂ fun x : Cn.{u} n ↦
        ((baseProj d.it d.iw x, x d.it) : Cn.{u} n × ℂ) :=
      differentiable_baseProj.prodMk (differentiable_apply d.it)
    refine ⟨fun x ↦ u (baseProj d.it d.iw x, x d.it), fun x a ↦ ?_,
      hu.comp hm.differentiableOn fun x hx ↦ D.mem_of_mem_cyl hx,
      fun x hx ↦ hu0 _ (D.mem_of_mem_cyl hx), fun x hx ↦ hψu _ (D.mem_of_mem_cyl hx)⟩
    simp only [baseProj_update_iw, Function.update_of_ne d.it_ne_iw]
  mem_iff x hx := D.mem_N₀'_iff_graphs x hx

end PuiseuxData

end BPointData

end

end ComplexAnalytic.BoundedSections
