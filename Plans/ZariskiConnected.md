# Zariski connectedness for projective models over a complete DVR (wp-zariski)

Consumer: `TemperedFundamentalGroups.SemistableReduction.Statement.ZariskiConnected` (tfg,
`SemistableReduction/ZariskiConnected.lean`), assumed by Theorem B
(`strongComponentA_body_of_tree`). The goal is `theorem Statement.zariskiConnected`, proved in tfg
on top of the general algebraic geometry in oka.

## 1. Truth check

* `ModelCode O'` is `⟨m, I : (projSpace O' m).IdealSheafData⟩`, `scheme = I.subscheme`, and
  `toSpec = subschemeι ≫ projSpace.toSpec`. So every model code is **projective** (a closed
  subscheme of `ℙᵐ_{O'}`) and proper. `projSpace O' m` is *syntactically* oka's `ℙ(m; O')`
  (`Proj (homogeneousSubmodule (Fin (m+1)) O')`, with the same `MvPolynomial.gradedAlgebra`
  instance). There is no difference between the general case and the `projModelCode` case.
* `j' : Spec L ⟶ X` scheme-theoretically dominant gives `X` reduced
  (`IsSchemeTheoreticallyDominant.isReduced`) and irreducible (it is the closure of one point),
  so `X` is integral.
* `ker (O' → L)` is either `⊥` or `𝔪`.
  - If it is `𝔪`, the generic point of `X` lies in the closed special fibre, so the special fibre
    is all of `X`: nonempty and irreducible, hence connected.
  - If it is `⊥`, `X → Spec O'` has closed image containing the generic point, so it is surjective
    and the special fibre is nonempty. `ϖ'` is a nonzerodivisor on every `Γ(X, V)` (`X` is
    integral and `ϖ' ≠ 0` in the function field). Zariski's theorem then applies.
* **Semistability is not needed**: integrality + projectivity + the base being a complete DVR
  suffice. Empty special fibres cannot occur. **The statement is true as written.**

## 2. The argument (degree-0 formal functions, Čech form)

Let `U_i = D₊(x_i) ∩ X` be the standard affine cover, `C•` the (ordered) Čech complex of `O_X`, so
`H⁰(C) = A := Γ(X, O)`, `t := ϖ'`. Suppose `X₀ = Z₁ ⊔ Z₂` with `Z₁, Z₂` nonempty and closed.

1. On each affine `U_σ = Spec A_σ` the set `V(t) = X₀ ∩ U_σ` splits, which gives an idempotent of
   `A_σ/t`. It lifts uniquely to an idempotent `ε_{σ,n} ∈ A_σ/tⁿ` (nilpotent kernel), and by
   uniqueness these are compatible under restriction and in `n`. So `ε_n` is a 0-cocycle of `C/tⁿ`,
   and `ε_{n+1} ↦ ε_n`.
2. A hand chase: lift `ε_n` to `x_n ∈ C⁰`. Then `d x_n = tⁿ y_n` with `y_n` a 1-cocycle, and
   `[y_n] = t[y_{n+1}]` in `H¹(C)`. `H¹(C)` is a **finite** `O'`-module, so its `t`-torsion is
   killed by some `t^N`, which gives `[y_1] = t^N [y_{N+1}] = 0`. Hence `ε_1` lifts to `a ∈ A`
   with `a² − a ∈ tA` and `ā ≠ 0, 1`. (Only `H⁰` and `H¹` are used, never `lim`.)
3. `A` is a domain and a finite module over the complete DVR `O'`. So it is `tA`-adically complete,
   and `HenselianRing A (tA)` holds (Mathlib, `IsAdicComplete.henselianRing`). Hensel lifting of
   `X² − X` gives an idempotent `≡ a`, which is `0` or `1`. Contradiction.

What has to be built: **Serre finiteness**, i.e. Čech `H⁰` and `H¹` of a coherent sheaf on
`ℙⁿ_R`, for `R` noetherian, are finite `R`-modules.

## 3. Survey

* Mathlib: no coherent cohomology. It has `Sheaf.H` (Ext), Artin–Rees/Krull, adic completion,
  `IsAdicComplete.henselianRing`, idempotent lifting along nilpotent kernels, and
  `IsSchemeTheoreticallyDominant.isReduced` / `Hom.app_injective`.
* **oka (master 192edb0) has almost all the infrastructure**:
  - sheaf cohomology `TopCat.Sheaf.H` with LES;
  - the ordered Čech complex (`cechComplex`), with Čech LES for sequences surjective on the
    `U_σ`;
  - Leray (vanishing form) and `cechH1Equiv`;
  - affine Serre vanishing; `Hᵠ = 0` for `q ≥ n+1` on `ℙⁿ`;
  - twisting sheaves `O(k)`, whose Čech complex is the Laurent model (exact except `q = n`,
    `k ≤ −n−1`), and `Γ(O(k))` finite;
  - Theorem A (`0 → K → ⊕O(−m) → F → 0` with `K` coherent);
  - Serre vanishing for `m ≫ 0`;
  - pushforward of coherent along closed immersions; `O_X` coherent on locally noetherian `X`.

  Missing: finiteness of `Hᵠ(F)` for *untwisted* `F` (needs `Hⁿ(O(k))` for `k ≤ −n−1`, the
  top-degree Laurent cohomology), and `R`-module structures on Čech cohomology.
* formal-schemes: no cohomology or formal functions. pi1, tfg: nothing relevant, except tfg's
  extension-of-valuation machinery (`UniqueExtDVR`, `henselianLocalRing_valuationSubring`, spectral
  norm complete).
* Cheaper alternatives assessed:
  - (a) Twisting trick with `H¹(F(m)) = 0` for `m ≫ 0`: it needs multiplicative structure on
    twists and a rank-one argument in the completion. It is not cheaper and is more fragile.
  - (b) `lim H⁰(X_n)`: not needed; step 2 above uses only `H⁰`, `H¹` and bounded torsion.
  - (c) Normality / Hartogs: no elementary route avoids `H¹`.

## 4. Placement

* **oka** (branch `wp-zariski`): Serre finiteness and the Zariski core. oka is where the entire
  projective-space cohomology lives; moving ~13k lines down to pi1 is not sensible.
* **tfg** (branch `wp-zariski`): `Statement.zariskiConnected` glue. **New dependency on oka.**
  - Compatibility: same Lean v4.32.0, same Mathlib rev 81a5d257.
  - oka requires pi1 4996dc3 and heights 3539e2a; tfg pins pi1 60129404, an ancestor of both
    4996dc3 and pi1 master 7647d28.
  - Proposal: bump tfg's pi1 pin to master 7647d28, which iut already builds against with tfg.
  - The oka files tfg imports do not import Pi1/Heights, so only the algebraic closure is built.

## 5. Stages (oka unless stated) and line estimates

| # | Content | File(s) | est. |
|---|---------|---------|------|
| S1 | Leray, converse direction: if `Hᵖ(U_σ,F)=0` (p≥1) on all intersections and `Hᵠ(X,F)=0`, then Čech `Hᵠ(U,F)=0` (dimension shift along `injSES`, base `cechHomologyToH_injective`) | `Topology/Sheaves/Cohomology/LerayCech.lean` | 250 |
| S2 | Čech complex of `F : ℙ(n;R).Modules` as a complex of `R`-modules (`R` acting through constants), iso to oka's after `forget₂`; Čech LES for short exact sequences of quasi-coherent sheaves in `ModuleCat R` | `AlgebraicGeometry/ProjectiveSpace/CechModule.lean` | 400 |
| S3 | Top-degree Laurent cohomology: `Hⁿ` of the Čech complex of `O(k)` is a finite `R`-module (cocycle ≡ its `proj univ` part, which lives in a finite module of monomials with all exponents negative) | `RingTheory/MvPolynomial/CechProjectiveTop.lean` | 300 |
| S4 | **Serre finiteness**: Čech `Hᵠ(ℙⁿ_R, F)` is a finite `R`-module for coherent `F` and all `q` (descending induction from S1 + `H_eq_zero_of_le_of_isQuasicoherent`, Theorem A, S2, S3) | `AlgebraicGeometry/ProjectiveSpace/SerreFiniteness.lean` | 400 |
| S5 | Closed subschemes `i : X ⟶ ℙ(n;R)`: Čech complex of `i_*O_X` on the standard cover = Čech complex of the rings `Γ(X, i⁻¹U_σ)`; `H⁰ = Γ(X,O_X)` as `R`-algebras; finite `H⁰`, `H¹` | `AlgebraicGeometry/ProjectiveSpace/ClosedSubschemeFinite.lean` | 300 |
| S6 | **Zariski core**: `R` a DVR with `IsAdicComplete 𝔪 R`, uniformizer `t`, `X ⊆ ℙⁿ_R` closed, integral, `t` nonzero at the generic point ⇒ the special fibre is connected (steps 2.1–2.3) | `AlgebraicGeometry/ZariskiConnected.lean` | 700–900 |
| T1 | tfg: `IsAdicComplete (maximalIdeal O') O'` from completeness of `O` (unique extension / spectral norm, existing tfg material) | tfg `SemistableReduction/ZariskiConnectedProof.lean` | 150–300 |
| T2 | tfg: integrality of `c'.scheme` from `j'`, the case split on `ker (O' → L)`, applying S6; `Statement.zariskiConnected` | same | 200–300 |

Total ≈ 2700–3200 lines (oka ≈ 2300–2500, tfg ≈ 400–600).

## 6. Risks

* **R1 (S2)**: `R`-module structures on sections (`sectionsModule` is not an instance) and the
  spelling `X.Modules` vs `SheafOfModules ringSheaf`. Mitigation: build the `ModuleCat R` complex
  by hand and transport exactness along `forget₂`.
* **R2 (S5)**: identifying sections of `i_* O_X` with the *rings* `Γ(X, i⁻¹U_σ)` (defeq through
  `SheafOfModules.unit`/pushforward), compatibly with the `R`-action.
* **R3 (T1)**: completeness of `O'` is not an instance. Fallback: show `O'` is finite over `O`
  and run step 2.3 with `t = ϖ_O`.
* **R4**: build cost of the oka import closure inside tfg (first build, once).

## 7. Helpers (≤ 2, own worktrees)

* H-top (`oka wp-zariski-top`): S3, pure algebra on `CechProjective`.
* H-tfg (`tfg wp-zariski-dvr`): T1.

The lead does S1, S2, S4, S5, S6 and T2.

## 8. Status (2026-10-09): done

| Stage | Result |
|-------|--------|
| S1 | `TopCat.Sheaf.cech_exactAt_of_H_eq_zero` (`Topology/Sheaves/Cohomology/LerayCech.lean`) |
| S2 | `Scheme.Modules.CechFinite`, `cechFinite_X₃`, `cechFinite_of_cocycles`, `cechFinite_zero_iff`, `CechFinite.exists_pow_smul_eq_d`, `exists_cocycle_sub_eq_smul` (`AlgebraicGeometry/Modules/CechModule.lean`) |
| S3 | `ProjectiveSpace.exists_eq_sum_cechSmul_add_cechD` (`ProjectiveSpace/TwistCohomologyTop.lean`, `RingTheory/MvPolynomial/CechProjectiveTop.lean`; helper H-top) |
| S4 | `ProjectiveSpace.cechFinite_of_isCoherent` (`ProjectiveSpace/SerreFiniteness.lean`) |
| S5/S6 | `Scheme.IsIdemMod` (`AlgebraicGeometry/IdempotentMod.lean`), `IsAdicComplete.of_finite`, `eq_zero_or_eq_one_mod_of_finite` (`RingTheory/AdicCompletion/FiniteComplete.lean`), `ProjectiveSpace.not_split`, `ProjectiveSpace.isPreconnected_closedFibre` (`ProjectiveSpace/ZariskiConnected.lean`) |
| T1 | tfg `ZariskiDVR.isAdicComplete_maximalIdeal`, `ZariskiDVR.finite` (helper H-tfg) |
| T2 | tfg `SemistableReduction.Statement.zariskiConnected` (`SemistableReduction/ZariskiConnectedProof.lean`) |

Actual size: about 2000 lines in oka and 250 in tfg. Normality and semistability turned out not
to be needed.
