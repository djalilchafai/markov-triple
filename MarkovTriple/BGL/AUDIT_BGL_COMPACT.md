# Audit round 10 (hostile): `BGL/Theory/Compact/*`

Scope: `compact_gradientInterpolation`, `compact_entropyInterpolation`, `compact_gradient_bound`,
`compact_logSobolev`, `CompactTriple.fisher_decay`, `fisher_antitone`, `Circle.circle_gradient_bound`,
`circle_entropy_deriv`, `circle_fisher_antitone`.  Own view formed from the Lean statements first
(GAPS_COMPACT.md was only skimmed at the end for the "Not done" section; it agrees with the findings below).
Book paraphrased only (Thm 3.3.18, Cor 3.3.19, Prop 5.7.1, compact triples Def 3.3.26).

## Verdict

No soundness defect found (no High, no Medium-correctness).  Two non-vacuity/coverage caveats (Medium,
informational) and three Low documentation items.

## (1) Do the structures hold as STATED?  Yes.

Read field by field (`GradientBound.lean:55-72`, `LogSobolev.lean:95-109`) against the instance proofs
(`Compact/Gradient.lean:176-190`, `Compact/Entropy.lean:405-420`).  Specific attacks:

* Bochner junk: every integral in a field is either guarded by an explicit `Integrable` conjunct
  (`GradientInterpolation.hasDerivAt`, `hasDerivAt_I`) or is the integral of a bounded function against a
  probability measure.  Where the proof equates integrals it does so by `integral_congr_ae` (no integrability
  needed), and the places that need integrability (`integral_sub`, `integral_mono_ae` in `fisher_deriv_le`) are
  fed real integrability proofs (`C.i2`, `entJ_integrable`).  `entI_nonneg` is not Bochner-junk dependent.
* a.e./representative: `Pt t f` is `Classical.choose` of F8, a function that lies in `𝒜` (hence in `𝒜₀`
  by `A_eq`) EXACTLY, not a.e.  So `ε + Pt`, `Λ ∘ (ε + Pt)` are literal members of `𝒜₀`, `L`, `ΓA`, `Γ₂` are
  applied to genuine test functions, and the only a.e. passages (`orb_ae`, `L_Pt`, `L_Pt2`, `tri_ae`) go
  through the L² classes.  `ΓA_congr_A`/`L_congr_A` are used where two representatives meet.  F8 is therefore
  not a representative problem for compact triples (it is for non-compact `𝒜 ≠ 𝒜₀`, out of scope).
* Uniformity in the cutoff: `hasDerivAt_I` quantifies `∀ C : BE.Cut ε M` for arbitrary `M` with `φ ≤ M`; the
  instance (`entI_hasDerivAt`, `entJ_integrable`) takes `K` and `M` as arguments, so it is uniform.  `BE.Cut` is
  inhabited (`exists_cut`), so the `∀` is not vacuous; `Λ`, `Θ` have compact support (`hΛc`, `hΘc`), as
  required by the chain-rule lemma `hasDerivAt_pairS`.
* Continuity at 0: `continuousOn_I/E` are obtained from `continuousAt` on all of `ℝ` of `s ↦ orb ψ s`
  (`semigroup` strongly continuous composed with `toNNReal`); the one-sided `Ici 0` statement follows.  Derivative
  fields are only for `s > 0` (resp. `0 < s < t`), where `toNNReal` is the identity locally.
* `hasDerivAt_gradPhi` uses `t - s > 0` for the second orbit; `t = 0` gives empty `Ioo` and the Gronwall step
  is vacuous but `Pt_zero` handles the end points (`gradient_bound`).
* `CD` side: `hCD.2 g` is used only to drop `(n⁻¹).toReal * (L g)^2 ≥ 0` (true for `n = ∞`, `n ≥ 1`).
* Axioms: `lake env lean MarkovTriple/BGL/Audit/CompactAxiomWalk.lean` (2 min) walked all 99 non-internal
  constants defined in `MarkovTriple.BGL.Theory.Compact.*`: 0 with extra axioms, 0 with `sorry`
  (only `propext`, `Classical.choice`, `Quot.sound`).  Grep of `Theory/Compact/*.lean` for
  `sorry|axiom|native_decide|unsafe|opaque|implemented_by|extern|set_option`: no hit.  The `esa` field is not used.

## (2) Non-vacuity of `compact_logSobolev` and of the CD hypothesis

* `compact_logSobolev C (hρ : 0 < ρ) (hCD : CD ρ n)` has NO ergodicity/probability hypothesis: probability
  comes from `finite_prob` + constants in `𝒜₀` (unital `A` and `A_eq`), connectedness F9 gives ergodicity.
* Witness 1 (degenerate, constructed): `Sanity.trivialCompact` (one-point space, `Γ = 0`) has `CD(ρ,n)` for
  every `ρ ∈ ℝ`, `1 ≤ n` (`trivialCompact_CD`), so `compact_logSobolev` applies
  (`Audit/CompactCircle.lean: lsi_on_trivial`, compiles).  This only shows the hypotheses are jointly
  satisfiable, not that the theorem is interesting: on a point `LS` is trivial, and `Γ = 0`.
  F9 forces the underlying measure to be a single atom when `Γ = 0` (any non-constant `f` has `Γ f = 0`).
* Circle: `CD(ρ, n)` only for `ρ ≤ 0` (`circle_CD`; for `ρ > 0` take `f` with `f'' = 0 ≠ f'` somewhere:
  `Γ₂ f = (f'')²` is not `≥ ρ (f')²`).  Hence `compact_logSobolev` has NO nontrivial (`Γ ≠ 0`) instance in this
  library.  Severity: Medium (informational): the theorem is "proved for all compact triples", but its
  `ρ > 0` branch is only exercised on a one-point space.  The gradient/Fisher half IS exercised
  non-trivially on the circle (`ρ = 0`).
* No contradiction between `ρ > 0`, `CompactTriple` and `Γ ≠ 0`: the round sphere `S^m` (`m ≥ 2`) has
  `CD(m-1, m)` (Bochner), is compact, ergodic, `𝒜 = C^∞(S^m)`.  (`S^1` is the circle: `m - 1 = 0`, matching
  `circle_CD_zero_one`.)  Bonnet–Myers is consistent with, not contradicting, this.
* What a Γ ≠ 0, ρ > 0 witness needs (assessed, NOT built): `E = S²`, `μ` normalised surface measure,
  `𝒜₀ = 𝒜 = C^∞(S²)` as a subalgebra of bounded functions.  A polynomial algebra will NOT do: D2/F3 demand
  stability under every smooth `ψ`.  Required: (a) `L = Δ_{S²}`, `Γ = ⟨∇·,∇·⟩` on `C^∞(S²)` with
  D1–D8 (IBP on the sphere; no divergence theorem on spheres in Mathlib, or use the ambient formulation
  `Γ(f,g) = ∇f̃·∇g̃ − (Ef̃)(Eg̃)`); (b) F2 (positivity detection: density of `𝒜₀`, as `ae_nonneg_of_pairing`
  for the circle); (c) F8 `P_t 𝒜₀ ⊂ 𝒜₀`: needs the spherical harmonic (Legendre) expansion with rapid
  coefficient decay, i.e. smoothing of the heat flow (elliptic regularity on `S²`; this is the circle's
  `smoothing`/`Rapid` machinery but with Legendre polynomials and `ℓ(ℓ+1)` eigenvalues, not in Mathlib);
  (d) F10 ESA via an eigenbasis; (e) `CD(1,2)` via Bochner on `C^∞(S²)` (`Γ₂ f = |Hess f|² + |∇f|²`, needs
  a coordinate/ambient Hessian calculus).  Zonal-only reduction does not give a triple on `S²` (functions of the
  latitude only live on `[−1,1]` with Jacobi/Legendre generator `(1−x²)f'' − 2x f'`, which is a legitimate
  1-D diffusion triple with `CD(1,2)` but on an interval with a degenerate boundary: `𝒜₀ = C^∞([−1,1])`,
  F8 via polynomial invariance + density is feasible and is the cheapest nontrivial `ρ > 0` witness, ~1.5–3 kloc,
  still needs IBP with the weight `1` (Lebesgue measure on `[−1,1]`, `∫ ((1−x²)f')' g = −∫ (1−x²) f'g'`, easy),
  the Bochner `Γ₂` computation, and F8 for smooth non-polynomial `f` which again needs regularity).  Full
  `S²`: estimate 5–10 kloc and several weeks.  Not recommended without a dedicated plan.

## (3) Circle unfoldings (new, sorry-free, not imported by root): `Audit/CompactCircle.lean`

Compiles (`lake env lean`); axioms `propext, Classical.choice, Quot.sound` (printed in-file).
* `Pt_mc`: `P_t[cos 2πn·] = e^{-(2πn)² t} cos 2πn·` a.e. (Fourier action, from `semigroup_mc`).
* `Gamma_Pt_mc`: `Γ(P_t cos_n) = e^{-2 lam t} (2πn)² sin²`; `semigroup_Gamma_mc`:
  `P_t Γ(cos_n) = ((2πn)²/2)(1 − e^{-lam(2n) t} cos 2π(2n)·)` (uses `P_t 1 = 1`, `lam(2n) = 4 lam n`).
* `explicit_ineq`: by hand, `a²(2πn)² sin² ≤ ((2πn)²/2)(1 − a⁴ cos 4πn·)` where `a = e^{-lam t} ≤ 1`
  (identity `(1−a²)(½(1+a²) − a² sin²) ≥ 0`).  `circle_gradient_bound_mode` derives the SAME inequality from the
  library theorem `circle_gradient_bound` via the closed forms (consistency check), `strict_at_quarter` shows
  strictness at `x = 1/4`, `t > 0` (so the bound is not an equality in disguise).
* `fisher_antitone_concrete`: `circle_fisher_antitone` instantiated at `φ = ½ + ½cos`, `ε = ½`
  (`g_s = 1 + ½ e^{-(2π)² s} cos`).  Closed form `I(s) = (2π)²(1 − √(1 − e^{-2(2π)² s}/4))`
  (from `∫ sin²/(1+b cos) = (1−√(1−b²))/b²`, `b = a/2`), `fisherClosed_antitone` proved.
  Numerics (`scratchpad/fisher_check.py`, 2·10⁵-point midpoint quadrature): quadrature `I(s)` matches the closed form to
  1e-13 relative at `s = 0, .01, .05, .1, .3`; central difference of `e(s) = ∫ g log g` matches `−I(s)`
  (1e-7); `I` antitone on `[0,.5]`; gradient bound residual `max(lhs − rhs) = −0.878 < 0`, modes `n = 1,2,5`:
  `max(lhs − rhs) ≤ 3e-13` (equality at `t = 0`), strictly negative for `t > 0`.
* `Audit/CompactAxiomWalk.lean`: the walk script (item (1)).

## Findings

| # | Sev | Where | Issue | Fix |
|---|-----|-------|-------|-----|
| 1 | Medium (info) | `Compact/Consequences.lean:30` `compact_logSobolev` | No instance with `Γ ≠ 0` and `ρ > 0`; the circle has `ρ ≤ 0` only; only `trivialCompact` (`Γ = 0`, one atom). The `ρ>0` branch is exercised on a point only. | Build an `S²` (or interval/Jacobi) triple; or state the limitation in the theorem docstring (GAPS_COMPACT.md already does). |
| 2 | Low/Medium | same | Conclusion is `LS` on `𝒜₀` only (`LogSobolevIneq` class `𝒜₀`); the extension to `𝒟(ℰ)` exists (`FullTriple.logSobolev_extend_domain`) but is not packaged as `compact_logSobolev_domain`. Gradient bound is the weak form (not the `√` form, nor the `n < ∞` improved bound). | Add a one-line corollary via `LS.extend`; document weak form (done in GAPS_COMPACT.md). |
| 3 | Low | `Compact/Consequences.lean:15,19` docstring | Names `compact_fisher_decay`, `compact_fisher_antitone`, `circle_entropy_decay` do not exist; actual: `CompactTriple.fisher_decay`, `CompactTriple.fisher_antitone`, `Circle.circle_entropy_deriv`. | Fix docstring. |
| 4 | Low | `Theory/GradientBound.lean:9`, `Theory/LogSobolev.lean:16` headers | Say "conditional / G1,G3 NOT derived" without pointing to `Compact/` where they are discharged for compact triples. | Add a one-line pointer. |
| 5 | Info | `Frozen/CompactTriple.lean` | `CompactTriple` forces finite probability `μ`, unital `𝒜 = 𝒜₀`, closed under all smooth `ψ`: genuine instances must be `C^∞`-type algebras, not polynomial. Relevant to witness estimates. | None. |
