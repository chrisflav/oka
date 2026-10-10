# Blueprint: π₁ᵉᵗ(X, x̄) ≅ π₁^top(X^an, x)^ for X connected, locally of finite type over ℂ

**Status: done** (`ComplexAnalytic.etaleFundamentalGroupEquivCompletion`). Stages 1–3 and 4a on
`wp-pi1-comparison`; 4b by H1 (`wp-pi1-semialgebraic`, ~3.1k lines, the gradient inequality) and
H2 (`wp-pi1-lojasiewicz`, ~1.2k lines, flow retraction and charts) — far below the estimate
below, which assumed full curve selection and growth asymptotics.

Branch: `lana-agents/oka` `wp-pi1-comparison` (off `origin/master` at `da228a2`), worktree
`/home/christian/oka-pi1`. Helper branches `wp-pi1-*` (§4b).

## 0. Target

For `X : SchemeLFTℂ` with `ConnectedSpace X.obj.left` (arbitrary: singular, non-reduced) and
`x : analytification.obj X`, with `ξₓ : Spec ℂ ⟶ X` the geometric point at the closed point
`π(x)` (`AlgebraicGeometry.pointOfClosedPoint`):

    π₁ᵉᵗ(ξₓ) ≃ₜ* ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of (FundamentalGroup X^an x))

`π₁ᵉᵗ(ξ) = Aut (AlgebraicGeometry.FiniteEtale.fiber ξ)` from pi1 (new dependency, pinned at
`ca7def9`, the commit iut uses). Mathlib's `IsFundamentalGroup` (`CategoryTheory/Galois/
IsFundamentalgroup.lean`) turns "a compact group acting naturally, continuously, faithfully and
transitively on Galois fibres" into `toAutMulEquiv` + `toAut_isHomeomorph`; the whole proof is
organised as checking those four conditions for the profinite completion.

## 1. Algebraic ↔ analytic (Galois-category transport)

* 1.1 `IsFundamentalGroup` transports along an equivalence `e : C ≌ D` with `F ≅ e.functor ⋙ F'`
  (generic, `Oka/CategoryTheory/Galois/`). ~200 lines.
* 1.2 pi1 `FiniteEtale X.obj.left ≌ SchemeLFTℂ.FiniteEtaleOver X` (forget/remember the
  ℂ-structure), composed with `riemannExistenceTheoremEquiv`. ~300 lines.
* 1.3 fibre functors: `fiber ξₓ ≅ e ⋙ SeparatedFiniteEtaleOver.fintypeFiberFunctor x`. Points of
  `A ×_X Spec ℂ` ↔ points of `A` over `π(x)` (pullback of the preimmersion `ξₓ`) ↔ points of `A^an`
  over `x` (`analytificationπ` is a bijection onto closed points, `RET/ClosedPoints.lean`; points
  over a closed point under a finite map are closed). Naturality in `A`. ~500 lines.

## 2. Analytic finite étale = finite topological covering

Already in oka: `AnalyticSpace.coveringSpace` / `isFiniteEtale_coveringSpaceHom`
(`CoveringSpace.lean`) and `isCoveringMap_base_of_isFiniteEtale` (`CoveringMap.lean`). Only glue.

## 3. Covering theory (generic topology, Mathlib candidates, `Oka/Topology/Covering/`)

* 3.1 monodromy is natural in maps of covers; transitive on the fibre of a path-connected cover.
  ~200 lines.
* 3.2 construction: `B` locally path connected and semilocally simply connected, `H ≤ π₁(B, b)`
  ⇒ covering `E_H → B` with fibre `π₁/H` over `b`, monodromy = left translation, `E_H` Hausdorff
  if `B` is (path-space quotient; `IsOpen.trivializationDiscrete`). ~1200 lines.
* 3.3 `LocallyContractibleSpace B` (Mathlib, classical) ⇒ locally path connected and semilocally
  simply connected (free → based null-homotopy). ~300 lines.
* 3.4 profinite completion criterion: `π` acting naturally on the fibres of a Galois category,
  transitively on connected objects, with every finite-index normal subgroup containing the kernel
  of some fibre ⇒ `IsFundamentalGroup F (completion π)`. ~300 lines.
* 3.5 analytic assembly at `B = X^an` (monodromy on `A.hom.base ⁻¹' {x}`, `E_N` made analytic,
  separated, finite étale). ~500 lines.

Outcome: the comparison theorem **under the hypothesis `LocallyContractibleSpace X^an`**.

## 4. Local contractibility of X^an

Non-reducedness is irrelevant here: locally `X^an` is the zero set in `ℂⁿ = ℝ²ⁿ` of the
polynomials of an affine presentation (no radical needed), so 4 is a statement about real
algebraic sets.

* 4a (milestone, cheap): `X` smooth ⇒ `X^an` locally homeomorphic to opens of `ℂᵈ`
  (`isLocallyOpenInAffine_analytification`, `RET/ES/Smooth.lean`) ⇒ locally contractible.
  ~200 lines. Covers the IUT use case (hyperbolic curves).
* 4b (general): **every real algebraic set `Z = f⁻¹(0) ⊆ ℝᴺ` is locally contractible.** Route
  (Łojasiewicz 1963/1984): `Z` is a local neighbourhood retract, via the gradient flow of `f ≥ 0`
  (take `f = Σ gᵢ²`); trajectories have length `≤ C f^{1-θ}` by the **Łojasiewicz gradient
  inequality** `|∇f| ≥ c |f|^θ`, `θ < 1`, so the limit map is a continuous retraction `R` of a
  neighbourhood `W ⊇ B_ρ(p)`; then `(z, t) ↦ R((1-t) z + t p)` contracts `Z ∩ B_ρ'(p)` inside any
  given neighbourhood. No stratification, no triangulation. The gradient inequality needs
  semialgebraic geometry:
  - H1 `wp-pi1-semialgebraic`: Tarski–Seidenberg (Cohen–Hörmander quantifier elimination over ℝ),
    semialgebraic sets/functions, one-variable structure (finite unions of intervals,
    eventual monotonicity and continuity, power-type growth `f(t) ~ c tᵅ`, α ∈ ℚ), curve selection
    lemma, Łojasiewicz gradient inequality for real polynomials. **~9–11k lines.**
  - H2 `wp-pi1-lojasiewicz`: gradient flow of a polynomial on an open set (global existence while
    bounded, continuous dependence; Mathlib Picard–Lindelöf/Gronwall), finite length and
    continuity of the limit map **given** the gradient inequality, local retraction ⇒
    `LocallyContractibleSpace` for real algebraic sets; charts of `X^an` as such sets ⇒
    `LocallyContractibleSpace (analytification.obj X)`. **~4–6k lines.**
  - Total 4b: **~13–17k lines**; risk concentrated in quantifier elimination and curve selection.

Alternatives considered and rejected: semialgebraic triangulation (BCR 9.2; needs everything in
H1 plus a triangulation layer, ~25k), Milnor's conic structure (curve selection plus stratified
vector fields tangent to all strata — Whitney-type conditions, larger and less modular), reduction
to the smooth/normal locus (small loops through singular points are exactly what is not
controlled; circular), resolution (out of reach).

## 5. Totals

Stages 1–3 + 4a: ~4k lines (this agent). 4b: ~13–17k lines (two helpers + integration).
