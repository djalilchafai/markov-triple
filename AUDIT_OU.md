# AUDIT_OU (round 5, hostile)

Scope: `Sanity/OU/*`, `Frozen/{MarkovTriple,FullMarkovTriple,CD,CDFull,Ergodic,Semigroup}`.
Audit file: `MarkovTriple/Audit/OUAudit.lean` (not imported by root; compiles; the axiom walk takes ~2 min).

## Verdicts
1. **Fields of `ouFull` are not satisfied by junk. GENUINE.**
   - `ouTriple.L = Lo f x = f''(x) - x f'(x)` and `Γ = Go f g x = f'(x) g'(x)`, via `deriv`.
     `Γ`, `L` are constrained only on `A₀`/`A = C^∞`, where `deriv` is the true derivative; junk values off `A`
     are never constrained. Checked by `rfl` in the audit file.
   - `μ = gaussianReal 0 1` (`rfl`), `IsProbabilityMeasure` instance is inferred. `A₀ = C_c^∞` (`Sm f ∧ HasCompactSupport f`);
     `A = C^∞` (no growth condition).
   - `memLp` (continuous + compact support), `dense` (Mathlib `Lp.dense_hasCompactSupport_contDiff`),
     `comp_mem` (support in union of supports, `ψ 0 = 0`), `diffusion`/`diffusion_A` (quantified over all smooth ψ, g in algebra),
     `ibp` / `ibp_A*` (genuine Gaussian IBP `ibp_master`; integrability proved) are all real statements, not a.e.-weakened.
     The quantifier shapes match the frozen structure exactly (they typecheck as fields).
   - Caveat (known, round 3): polynomials are NOT in `A₀` (`comp_mem` + `memLp`, `Audit/Frozen3OU`), so C_c^∞ is forced, and
     ESA of `L|C_c^∞` is proved (`ou_esa`, via Hermite closure). Fine.
   - Weak spots by design (not defects): `semigroup_stable` is existential only; `A = C^∞` is large, so `CDFull`/`ibp_AA` on it
     are strong statements (and they are proved).
2. **`ou_poincare` = sharp Gaussian PI(1). Verified.** Statement `PoincareIneq (1/1)`: probability measure and
   `Var f ≤ 1 * ∫ f'^2 dγ` for all `f ∈ C_c^∞`. Unfolded form proved in audit
   (`ou_poincare_unfolded`: `∫f² - (∫f)² ≤ ∫ f'²`). Numeric check (quadrature): He_1 (identity): Var = 1 = E;
   He_n: Var/E = 1/n (2/4, 6/18, 24/96); `x·cutoff_R`: Var,E -> 1 (0.42/1.36 at R=1, 0.9988/0.9998 at R=3). So constant 1 is sharp
   (sharpness is not proved in Lean; identity is not in `A₀`, only in its closure).
3. **`ErgodicL2` is the closure-kernel statement** (Frozen/Ergodic): `u ∈ L²` with `f_n ∈ A₀`, `f_n -> u`, `L f_n -> 0` in L² => `u` a.e. const.
   Not trivially true: it needs a conclusion about every such `u`; the proof shows Hermite coefficients `<He_m,u> = 0` for m≥1 by IBP and
   completeness of the Hermite basis. Hypothesis is satisfiable for `u = 1` (cutoffs `cut (1/(n+1)) ∈ A₀` in audit; convergence
   is exactly `cutoff_approx` in Cutoff.lean, not re-proved by me). Sanity: would fail for a non-ergodic triple (e.g. Γ=0 on 2 points, `Audit/TwoPoint`).
4. **`semigroup_stable` proof matches the 8-clause `IsSemigroupOf`.** Destructuring `⟨h0, hadd, hcont, hself, -, -, -, hgen⟩`
   has exactly 8 slots: P0=id, additivity, strong continuity, self-adjoint, positivity, sub-Markov, P t 1 = 1, generator (the last three
   discarded except generator). No extra hypothesis (`IsSG P` = clauses 1–3; `GenA₀` = clause 8 verbatim). Uses `IsSemigroupOf ouTriple P`
   for the hypothesised `P` only; existence of such `P` is `Hilbert.isSemigroupOf_full` (generic), so the field is not vacuous.
5. **Banned constructs:** grep over Sanity/OU/*, Sanity/Circle.lean, Sanity/CircleFull.lean, Frozen/*: no `sorry`, `axiom`,
   `native_decide`, `set_option`, `unsafe`, `implemented_by`, `@[extern]`, `opaque`, `admit`, macros/syntax. Only `#print axioms` lines.
   Axiom walk (228 non-internal constants in modules `MarkovTriple.Sanity.OU.*`): 0 with non-standard axioms, 0 unsafe/partial/opaque/axiom.
   `ouFull`, `ouFull_CDFull`, `ou_ergodic`, `ou_poincare`: `[propext, Classical.choice, Quot.sound]`.
6. **Non-vacuity chain.** Audit file proves/compiles: `Γ(id,id) ≡ 1`; `L id = -x`; `Γ₂(id) = 1 = ρΓ(id)` (CD(1,∞) tight on id);
   `ou_poincare_unfolded`. Also `ouFull_Γ_ne_zero` in library. Numerics above agree (Var(id) = 1 ≤ E(id) = 1 in the limit).

## Residual notes (no refutation found)
- Sharpness of constant 1 and Hermite-eigenvalue facts are checked numerically, not in Lean.
- The ErgodicL2 satisfiability example in the audit shows only membership of the cutoff sequence in `A₀`.
