/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.RenameIndex

/-!
# Realizing a germ Weierstrass polynomial at `ULift`-indexed coordinates

`LocalOkaRing.exists_isWeierstrassPolynomial_realize` (`Oka/Weierstrass.lean`) turns a germ
Weierstrass polynomial into an honest `Q : Polynomial (OkaRing V)` for some neighbourhood `V` of
the origin in `ℂ^(Fin n)`. **Everything on the `ComplexAnalytic.AnalyticSpace` side indexes the
coordinates by `ULift (Fin n)`**, so that `ℂ^n` lives in an arbitrary universe
(`Oka/ComplexSpace.lean`), and in particular `ComplexAnalytic.okaFamily` and
`ComplexAnalytic.isFinite_comp_projRestrict_of_monic` in
`Oka/AnalyticSpace/HolomorphicFamily.lean` take a `Polynomial (OkaRing V)` with
`V : Opens (ULift (Fin n) → ℂ)`. This file moves the realization across.

## Why this is short, against what two files predict

`Oka/AnalyticSpace/HolomorphicFamily.lean` and `Oka/Analytification/MonicHypersurface.lean` both
record the germ step as needing `Oka/RenameIndex.lean`'s kind of work. **At the level of
`OkaRing` it needs none**, because the transport was already stated in the generality that
covers it: `OkaRing.congr` in `Oka/StructureSheaf.lean` takes an arbitrary
`φ : ℂ^ι ≃L[ℂ] ℂ^κ` with `ι` and `κ` independent, and `LocalOkaRing.congr_germ` in
`Oka/ChangeOfCoordinates.lean` is already the square saying that taking germs commutes with it.
So the only thing missing was the `φ`, and `Mathlib`'s
`ContinuousLinearEquiv`/`LinearEquiv.funCongrLeft` supplies it with no analysis.

**The theorem below is therefore stated for an arbitrary `φ` and not for `ULift`**, which is what
that measurement says the statement is really about; the `ULift` form is a corollary and is the
one a caller wants.

## Main definitions

- `LocalOkaRing.uliftCoord`: the coordinate space of `ULift ι` identified with that of `ι`, as a
  continuous linear equivalence. It is the map `LocalOkaRing.uliftEquiv` is
  `LocalOkaRing.congr` of, which `LocalOkaRing.congr_uliftCoord` says.

## Main results

- `LocalOkaRing.exists_monic_realize_congr`: **a germ Weierstrass polynomial in `n` variables is
  realized by a monic polynomial over the holomorphic functions on a neighbourhood of the origin
  of `ℂ^κ`**, for any `ℂ`-linear identification of `ℂ^(Fin n)` with `ℂ^κ`.
- `LocalOkaRing.exists_monic_realize_ulift`: the same at `κ = ULift (Fin n)`, with the germ read
  back through `LocalOkaRing.uliftEquiv`, which is the shape
  `Oka/AnalyticSpace/HolomorphicFamily.lean` takes.
- `LocalOkaRing.exists_congr_monic_realize_of_ne_zero`: **from a nonzero germ**, composing the
  above with Weierstrass preparation. After a linear change of coordinates of `ℂ^(n+1)` every
  nonzero germ is a unit times the germ of a monic polynomial over `OkaRing W` for some
  neighbourhood `W` of the origin in `ULift`-indexed coordinates.

## What is not here

* **No finiteness statement, and no image.**
  `ComplexAnalytic.isFinite_comp_projRestrict_of_monic` takes its hypersurface as a **range
  condition** — a set equation `Set.range i.base = {z | evalHom z (cylinderSection W P) = 0}` —
  and not as a `ComplexAnalytic.IsCutOutBy` datum, because `ComplexAnalytic.cylinderSection` is
  not the restriction of an entire function;
  `Oka/AnalyticSpace/OpenBaseProjection.lean` says why. **Nothing here produces such a range
  condition from a germ**, and nothing here is about analytic spaces at all: the results below
  produce the `P` that theorem asks for and stop. A caller supplies the morphism and its image.
* **No control on the neighbourhood.** `V` and `W` are whatever
  `LocalOkaRing.exists_isWeierstrassPolynomial_realize` produces; nothing says they are polydiscs,
  connected, or contained in any given set, and nothing below chooses between two of them.
* **Nothing about the change of coordinates.**
  `LocalOkaRing.exists_congr_monic_realize_of_ne_zero` concludes about `LocalOkaRing.congr φ f`
  and not about `f`, exactly as
  `LocalOkaRing.exists_congr_localweierstrass_preparation` does; no statement below removes the
  `φ` or relates the resulting hypersurface to the one before the change.
* **No uniqueness.** The Weierstrass polynomial of a germ is unique, and that is not proved here
  or anywhere in this repository; two applications of the results below may produce unrelated
  `P`s.
* **No `IsWeierstrassPolynomial` at `κ`, and it is a missing statement rather than a missing
  proof.** The predicate is declared at index type `Fin n` and nowhere else, so the results below
  keep only its `monic` field — which is all
  `ComplexAnalytic.isFinite_comp_projRestrict_of_monic` asks — and there is no way to state that
  the transported `P` satisfies the vanishing condition. Generalising the predicate the way
  `OkaRing.congr` is already general is what would be needed, and nothing here needs it.
-/

open TopologicalSpace

universe u v

noncomputable section

namespace LocalOkaRing

variable {n : ℕ} {κ : Type*} [Fintype κ]

/-! ### The coordinate relabelling underlying `LocalOkaRing.uliftEquiv` -/

/-- **The coordinate space of `ULift ι`, identified with that of `ι`**, as a continuous linear
equivalence `ℂ^ι ≃L[ℂ] ℂ^(ULift ι)`.

This is the map `LocalOkaRing.uliftEquiv` is `LocalOkaRing.congr` of, inverted so that it points
the way a caller needs — from the `Fin`-indexed side, where `Oka/Weierstrass.lean` states its
theorems, to the `ULift`-indexed side, where `ComplexAnalytic.AnalyticSpace` lives. It is
`Mathlib`'s `LinearEquiv.funCongrLeft` at `Equiv.ulift` and nothing else: relabelling coordinates
is linear, and a linear map between finite-dimensional spaces is continuous. -/
def uliftCoord (ι : Type v) [Fintype ι] : (ι → ℂ) ≃L[ℂ] (ULift.{u} ι → ℂ) :=
  ((LinearEquiv.funCongrLeft ℂ ℂ (Equiv.ulift.{u} (α := ι)).symm).toContinuousLinearEquiv).symm

/-- Its inverse reads a `ULift`-indexed point at the index it came from. -/
@[simp]
theorem uliftCoord_symm_apply {ι : Type v} [Fintype ι] (z : ULift.{u} ι → ℂ) (i : ι) :
    (uliftCoord.{u} ι).symm z i = z (ULift.up i) :=
  rfl

/-- Its forward map reads an `ι`-indexed point at the underlying index. -/
@[simp]
theorem uliftCoord_apply {ι : Type v} [Fintype ι] (w : ι → ℂ) (j : ULift.{u} ι) :
    uliftCoord.{u} ι w j = w j.down :=
  rfl

/-- **`LocalOkaRing.uliftEquiv` is the change of coordinates along
`LocalOkaRing.uliftCoord`**, which is what lets `LocalOkaRing.congr_germ` be applied to it.

Both sides are `LocalOkaRing.congr` of the same continuous linear equivalence — `uliftCoord` is
defined as the inverse of the one `LocalOkaRing.congrEquiv Equiv.ulift` uses — so
`LocalOkaRing.congr_symm` is the whole proof. -/
theorem congr_uliftCoord (ι : Type v) [Fintype ι] :
    congr (uliftCoord.{u} ι) = (uliftEquiv.{u} ι).symm := by
  rw [uliftEquiv, congrEquiv, congr_symm]
  rfl

/-! ### Realizing a germ Weierstrass polynomial at other coordinates -/

/-- **A germ Weierstrass polynomial is realized by a monic polynomial over the holomorphic
functions on a neighbourhood of the origin of `ℂ^κ`**, for any `ℂ`-linear identification `φ` of
`ℂ^(Fin n)` with `ℂ^κ`.

`LocalOkaRing.exists_isWeierstrassPolynomial_realize` does the work; this only moves its output
across `φ`. Both halves of that move are already stated in the generality needed:
`OkaRing.congr φ V` transports the coefficients, `LocalOkaRing.congr_germ` says taking germs
commutes with it, and `Polynomial.Monic.map` carries monicity — which is the *first field* of
`IsWeierstrassPolynomial` and is all that
`ComplexAnalytic.isFinite_comp_projRestrict_of_monic` asks of its polynomial.

**The vanishing condition of `IsWeierstrassPolynomial` is dropped, and it could not have been
carried even if something wanted it.** It says the lower coefficients vanish at the origin, and no
statement downstream of here consumes it — but **the predicate does not typecheck at `κ` at all**:
`IsWeierstrassPolynomial` is declared under `variable {n : ℕ} (U : Opens (Fin n → ℂ))` in
`Oka/Weierstrass.lean`, so it exists only at index type `Fin n`. The mathematics transports for
free — `φ` is linear, so `φ 0 = 0`, and `LocalOkaRing.congr_germ` does the rest — and what is
missing is the *statement*: the predicate would first have to be generalised in its index type
the way `OkaRing.congr` already is. See this file's `## What is not here`. -/
theorem exists_monic_realize_congr (φ : (Fin n → ℂ) ≃L[ℂ] (κ → ℂ))
    {g : Polynomial (LocalOkaRing (Fin n))}
    (hg : IsLocalWeierstrassPolynomial
      (Polynomial.map (localOkaSubring (Fin n)).toSubring.subtype g)) :
    ∃ (W : Opens (κ → ℂ)) (h0 : (0 : κ → ℂ) ∈ W) (P : Polynomial (OkaRing W)),
      P.Monic ∧
      Polynomial.map (OkaRing.germ h0).toRingHom P =
        Polynomial.map (congr φ).toRingHom g := by
  obtain ⟨V, h0, Q, hQg, hQW⟩ := exists_isWeierstrassPolynomial_realize hg
  have h0' : (0 : κ → ℂ) ∈ φ.opensCongr V := by simpa using h0
  refine ⟨φ.opensCongr V, h0', Polynomial.map (OkaRing.congr φ V).toRingHom Q,
    hQW.monic.map _, ?_⟩
  rw [Polynomial.map_map, ← hQg, Polynomial.map_map]
  congr 1
  refine RingHom.ext fun f ↦ ?_
  simpa using (congr_germ φ h0 f).symm

/-- **The `ULift`-indexed form**: a germ Weierstrass polynomial in `n` variables is realized by a
monic `P : Polynomial (OkaRing W)` for a neighbourhood `W` of the origin of `ℂ^(ULift (Fin n))`,
which is the index convention `ComplexAnalytic.okaFamily` and
`ComplexAnalytic.isFinite_comp_projRestrict_of_monic` are stated at.

*Realized* is the same relation `LocalOkaRing.exists_isWeierstrassPolynomial_realize` states,
read back through `LocalOkaRing.uliftEquiv`: the germ of `P` at the origin, relabelled from
`ULift (Fin n)` to `Fin n`, **is** `g` on the nose. -/
theorem exists_monic_realize_ulift {g : Polynomial (LocalOkaRing (Fin n))}
    (hg : IsLocalWeierstrassPolynomial
      (Polynomial.map (localOkaSubring (Fin n)).toSubring.subtype g)) :
    ∃ (W : Opens (ULift.{u} (Fin n) → ℂ)) (h0 : (0 : ULift.{u} (Fin n) → ℂ) ∈ W)
      (P : Polynomial (OkaRing W)),
      P.Monic ∧
      Polynomial.map (uliftEquiv.{u} (Fin n)).toRingHom
        (Polynomial.map (OkaRing.germ h0).toRingHom P) = g := by
  obtain ⟨W, h0, P, hP, hPg⟩ := exists_monic_realize_congr (uliftCoord.{u} (Fin n)) hg
  refine ⟨W, h0, P, hP, ?_⟩
  rw [hPg, Polynomial.map_map, congr_uliftCoord]
  have hid : RingHom.comp (uliftEquiv.{u} (Fin n)).toRingHom
      ((uliftEquiv.{u} (Fin n)).symm).toRingHom = RingHom.id (LocalOkaRing (Fin n)) := by
    refine RingHom.ext fun x ↦ ?_
    simp
  rw [hid, Polynomial.map_id]

/-! ### From a nonzero germ -/

/-- **From a nonzero germ**: after a linear change of coordinates of `ℂ^(n+1)`, every nonzero
germ is a unit times the germ of a **monic polynomial over the holomorphic functions on a
neighbourhood of the origin of `ℂ^(ULift (Fin n))`**.

This is `LocalOkaRing.exists_congr_localweierstrass_preparation` — Weierstrass preparation with
its genericity hypothesis traded for the change of coordinates `φ` — followed by
`LocalOkaRing.exists_monic_realize_ulift`. **It is the arrow
`Oka/AnalyticSpace/HolomorphicFamily.lean` and `Oka/Analytification/MonicHypersurface.lean` both
record as missing**, and its target `P` is exactly what `ComplexAnalytic.okaFamily` and
`ComplexAnalytic.isFinite_comp_projRestrict_of_monic` take.

Read the conclusion carefully: it is about `LocalOkaRing.congr φ f` and **not** about `f`, and
`φ` is produced rather than chosen, exactly as in the preparation theorem this rests on. What it
does *not* give is a hypersurface or its image; see this file's `## What is not here`. -/
theorem exists_congr_monic_realize_of_ne_zero {f : LocalOkaRing (Fin (n + 1))} (hf : f ≠ 0) :
    ∃ (φ : (Fin (n + 1) → ℂ) ≃L[ℂ] (Fin (n + 1) → ℂ)) (u : LocalOkaRing (Fin (n + 1)))
      (_ : IsUnit u) (W : Opens (ULift.{u} (Fin n) → ℂ))
      (h0 : (0 : ULift.{u} (Fin n) → ℂ) ∈ W) (P : Polynomial (OkaRing W)),
      P.Monic ∧
      congr φ f = fromPolynomial (Polynomial.map (uliftEquiv.{u} (Fin n)).toRingHom
        (Polynomial.map (OkaRing.germ h0).toRingHom P)) * u := by
  obtain ⟨φ, u, hu, g, hg, hfeq⟩ := exists_congr_localweierstrass_preparation hf
  obtain ⟨W, h0, P, hP, hPg⟩ := exists_monic_realize_ulift.{u} hg
  exact ⟨φ, u, hu, W, h0, P, hP, by rw [hPg]; exact hfeq⟩

end LocalOkaRing

end
