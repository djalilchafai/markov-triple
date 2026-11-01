# HILBERT_STATUS (Phase 3, `MarkovTriple/Hilbert/`)

Status legend: PORTED = text ported with only mechanical changes (header, namespace
`CutoffRigidity.Riemann.Diff` -> `MarkovTriple.Hilbert`, `module`/`public` removed); NEW = written here;
MERGED = two source copies replaced by one. Everything builds with `lake build` (Lean v4.35.0-rc2);
no `sorry`, no `axiom`, no `maxHeartbeats`; every file <= 530 lines; `Hilbert/AxiomCheck.lean` shows
only `propext, Classical.choice, Quot.sound` for all main theorems. `Frozen/`, `Sanity/`,
`Divergences/` untouched; `check_frozen.py` OK.
Sources: CR = `cutoff-rigidity-diffusions` (`CutoffRigidity/Riemann/*`), GP = `ginibre-poincare`.

## Items

| Item | Source | File | Status | Changes |
|---|---|---|---|---|
| complexification, `rcfc`, `UnitOp` (real CFC via `Cx H`) | CR `DiffFrComplex` | `Complexify.lean` | PORTED | none |
| `FormData` (dense D, symmetric nonneg A), completion `K`, `ι`, `Q`, `E`, Friedrichs resolvent `R=ιι†` | CR `DiffFriedrichs` | `Friedrichs.lean` | PORTED | none; this is THE form structure |
| `DirFormData`, `DirFriedrichs`, `closed_of_bounded`, `contraction_mem`, `fixed_of_comparison` | CR `DiffMarkov` | `DirMerge.lean` | MERGED | `structure DirFormData` deleted, every use replaced by `FormData`; rest verbatim |
| `DirFriedrichs S` instantiated from the completion construction (`Q` = H-limits of energy-Cauchy D-sequences, `E` = limit of energies) | -- | `DirBridge.lean` | NEW | `FormData.dirFriedrichs`, `exists_K_limit` |
| `cfcSemigroup` (`h_t(R)`, `h_t(r)=exp(-t(1/r-1))`), resolvents `R_lambda`, implicit-Euler limit (Dini), eigenvectors, `cfcSemigroup_mapsTo` | CR `DiffCfcSemigroup` | `CfcSemigroup.lean` | PORTED | none |
| strong continuity, derivative, Duhamel formula | CR `DiffFrDeriv` | `SemigroupDeriv.lean` | PORTED | none |
| smoothing `T_t = R^k B` | CR `DiffFrPow` | `SemigroupSmoothing.lean` | PORTED | none |
| `FormData.resolvent`, `semigroup`, `E_resolvent`, `eq_resolvent_of_weak`, `AF` | CR `DiffFrResolvent` | `Resolvent.lean` | PORTED | none |
| graph-defined self-adjoint operator `1 - R^{-1}` (`resolventGenerator`) | GP `GinibreFullSemigroupGenerator` (complex only); CR `positiveResolventOperator` (`GibbsSelfAdjoint`) | `ResolventGenerator.lean` | MERGED / GENERALISED | GP text generalised from `ℂ` to `[RCLike 𝕜]` (so real and complex); added `mem_domain_resolventGenerator_iff`, `resolventGenerator_apply_eq_iff`. CR's `positiveResolventOperator` is NOT ported separately (it lives behind `GibbsSobolev` and is subsumed by this graph construction) |
| generator of the semigroup = `resolventGenerator R` exactly; extends `-A` | -- | `Generator.lean` | NEW | `tendsto_generator_iff` (iff, both directions), `generator_extends`, `hasRightDeriv_semigroup_of_mem_range` |
| **(1)** existence | -- | `Existence.lean` | NEW | `FormData.exists_semigroup` |
| **(2)** spectral gap <=> L2 decay | -- | `SpectralGap.lean` | NEW | `hasSpectralGap_iff_hasExpDecay`; via resolvents and Euler scheme (Yosida bound), no `d/dt` |
| Beurling-Deny (cone invariance) | CR `DiffMarkov.fixed_of_comparison` (Q-level restatement) | `BeurlingDeny.lean` | NEW | works on `FormData.Q/E` directly |
| `L^2(mu)` form data of a `MarkovTriple`; well-definedness of `A[f] = -[Lf]` on classes | -- | `TripleForm.lean` | NEW | via Cauchy-Schwarz for `q(f,g)=∫Γ(f,g)` + density |
| **(3)** bridge to frozen `IsSemigroupOf` | -- | `Bridge.lean` | NEW | `isSemigroupOf_tripleSemigroup` (needs `IsMarkovianForm`, see below) |
| `esa` => generator = closure of `L|A0` | -- | `Closure.lean` | NEW | `FullMarkovTriple.generator_graph_eq_closure` |
| checkable criterion for `IsMarkovianForm` | CR `contraction_mem` generalised (approximation on the core) | `MarkovCriterion.lean` | NEW | `exists_contraction_of_approx`, `isMarkovianForm_of_approx` |
| `OperatorSquareCompletion` (Poincare => integrated Gamma_2) | GP `Endgame/GeneratorCompletion` | `OperatorSquareCompletion.lean` | PORTED | namespace only |
| non-vacuity of the bridge | -- | `Sanity.lean` | NEW | trivial triple: `IsMarkovianForm` holds, so a witness of `IsSemigroupOf` exists |
| axiom audit | -- | `AxiomCheck.lean` | NEW | |

## Precise statements

(1) `FormData.exists_semigroup (S : FormData H)` [real Hilbert, complete]: there are
`P : ℝ≥0 → H →L[ℝ] H` and `G : H →ₗ.[ℝ] H` with `IsSelfAdjointContractionSemigroup P` (`P 0 = 1`,
`P (s+t) = P s * P t`, `t ↦ P t u` continuous for each `u`, each `P t` self-adjoint, `‖P t‖ ≤ 1`,
`0 ≤ ⟪P t u, u⟫`), `IsSelfAdjoint G`, `G.IsClosed`, dense domain, `IsGeneratorOf G P`
(`(∃ h : x ∈ dom G, G ⟨x,h⟩ = v) ↔ t⁻¹(P_t x - x) → v` as `t ↓ 0`), `⟪G x, x⟫ ≤ 0`, and for every
`f : S.D`: `f ∈ dom G` and `G f = -S.A f`. (`G = -A_F`, `P_t = h_t((1+A_F)^{-1})`.)

(2) `S.HasSpectralGap λ`: `λ‖u‖² ≤ E(u,u)` for `u ∈ Q` with `u ⟂ N`, `N = {n | R n = n} = ker G`.
`S.HasExpDecay λ`: `‖P_t u‖ ≤ e^{-λ t}‖u‖` for `u ⟂ N`, `t ≥ 0`. For `0 ≤ λ` they are equivalent
(`hasSpectralGap_iff_hasExpDecay`).

(3) `isSemigroupOf_tripleSemigroup (T : MarkovTriple E) (hM : IsMarkovianForm T) :
IsSemigroupOf T (tripleSemigroup T)`, where `tripleSemigroup T = (formData T).semigroup` and
`IsMarkovianForm T := ∀ u ∈ Q, ∃ v ∈ Q, v = |u| ∧ E(v,v) ≤ E(u,u)`
(first Beurling-Deny criterion for the closure of `ℰ(f)=∫Γ f f` on `𝒜₀`).
Proved WITHOUT `hM`: `P 0 = id`, semigroup law, strong continuity, self-adjointness, `P_t 1 = 1`
(from `L 1 = 0` via the `k=0` case of `diffusion`), generator extends `L|𝒜₀`.
Uses `hM` only for: positivity preservation.

## What is MISSING for the bridge, exactly

**The only missing hypothesis is positivity preservation of `P_t`, i.e. the Markov property of the
form.** It does not follow from the fields of `MarkovTriple`/`FullMarkovTriple`: `diffusion` only
applies when `ψ(f) ∈ 𝒜₀` (no stability of `𝒜₀` under smooth `ψ`), so `|f|`, `f∧1` or `ψ_ε(f)` are
not known to lie in the form domain, and `FullMarkovTriple.esa`/`ibp_A`/`semigroup_stable` do not
supply it (`semigroup_stable` is itself conditional on `IsSemigroupOf`). Hypothesis offered:
`IsMarkovianForm T`; sufficient and checkable on the core (`isMarkovianForm_of_approx`): for every
`f ∈ 𝒜₀`, `ε > 0` there is `g ∈ 𝒜₀` with `‖[g] - |[f]|‖₂ < ε` and `∫Γ g g ≤ ∫Γ f f + ε`
(e.g. `g = ψ_ε(f) ∈ 𝒜₀`).

## Known weak points (self-assessment)

1. `IsMarkovianForm` is an extra hypothesis (see above). Non-vacuity is checked only on the trivial
   triple (`Γ = 0`); NOT on the circle, OU, or any triple with `Γ ≠ 0`.
2. `esa` is not needed for existence of an `IsSemigroupOf` witness. It gives only
   `graph(generator) = closure(graph(-A|D))`. **Uniqueness of the `IsSemigroupOf` witness (the claim in the
   docstring of `Frozen/Semigroup.lean`) is NOT proved**; in particular `IsSemigroupOf` does not
   assert contractivity, so uniqueness would need extra work.
3. GP's complex CFC construction `resolventCfcEvolution` (complex Hilbert spaces, scalar function
   `e^t * glue(r/t)`) is NOT ported: the real construction (complexification + `rcfc`) replaces it.
   I did not prove that GP's multiplier equals `hfun` (it should: `e^t e^{-t/r}`); the complex-H
   semigroup is not available here. CR's `positiveResolventOperator` is not ported separately
   (subsumed by `resolventGenerator`).
4. The CR files are ported verbatim; they still emit deprecation / unused-simp-arg linter warnings.
   `DirMerge.lean`'s `contraction_mem`/`fixed_of_comparison` (core-level, `hD : Tm D ⊆ D`) are kept
   but unused by the bridge (replaced by the Q-level `BeurlingDeny.lean`).
5. The spectral-gap notions are stated relative to `N = ker G` (orthogonality to fixed points), not
   relative to constants; identifying `N` with constants (ergodicity) is left to users.
6. `FullMarkovTriple.generator_graph_eq_closure` is declared in namespace `MarkovTriple.Hilbert`
   (full name `MarkovTriple.Hilbert.FullMarkovTriple.generator_graph_eq_closure`), so `F.generator_graph_eq_closure`
   dot notation does not work.
7. All of `Hilbert/` needs `CompleteSpace H` (true for `Lp`); `FormData` needs `D` dense.
