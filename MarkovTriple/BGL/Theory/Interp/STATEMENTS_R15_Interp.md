# Round 15 (Interp stage): target statements, fixed BEFORE the proofs

Book = Bakry-Gentil-Ledoux; Thm 3.3.18, Cor 3.3.19, Lemmas 3.3.20-3.3.21 on book pp. 163-164 (PDF = book + 17).
Frozen structures `GradientInterpolation` (GradientBound.lean), `StrongInterpolation` (Strong/Main.lean),
`EntropyInterpolation` (LogSobolev.lean), `FiniteDimInterpolation` (LogSobolevDim.lean) are NOT modified.

## What the book's proof actually yields (read first; it dictates the targets)
The proof of Thm 3.3.18 (p. 164) works with `G_eps = sqrt(Gamma(P_{t-s}f)+eps^2) - eps` and
`Phi(s) = int h P_s G_eps`.  It differentiates `Phi` with `d/ds int G P_s h = -E(P_s h, G)` (spectral calculus,
`G in D(E)` by Lemma 3.3.20) and `d/ds G_eps = -Gamma(P_{t-s}f, P_{t-s}Lf)/(G_eps+eps)`; the sign comes from
Lemma 3.3.21.  Consequently the book proves the *eps-form* (`StrongInterpolation`), NOT the equality
`Phi' = 2 int P_s h Gamma_2(P_{t-s} f)` of the plain `Phi(s) = int P_s h Gamma(P_{t-s} f)`: there `Gamma(P_{t-s}f)` is
only in `L^1` ("no a priori control of the L^2 norm", p. 163), hence not in `D(E)`, and the book does not differentiate it.
Cor 3.3.19 is deduced from Thm 3.3.18 by Jensen (p. 163).  So:

* **G1 (`GradientInterpolation`)**: NOT a book statement; not targeted.  Replaced by the book route: G1' + Jensen.
* **G3 (`EntropyInterpolation`)**, **G3' (`FiniteDimInterpolation`)**: the book gives these only as formal computations
  (Prop 5.7.1 / Thm 5.7.4 appeal to Prop 3.3.17); no step for the `L^1` differentiation of
  `I(s) = int Gamma(g_s)/g_s` is written.  Not targeted unless time remains (reported as remaining).

## T1 (main).  `FullTriple.strongInterpolation : T.CD rho n -> T.StrongInterpolation`, for EVERY `T : FullTriple E`
Hypotheses: `hCD : T.CD rho n` for some `rho : R`, `n : ENNReal` (ESA is the field `esa` of `FullTriple`).
Conclusion: exactly the frozen structure `StrongInterpolation` (same fields: for all eps>0, f,h in A0, 0 <= h a.e., t:
continuity of `strongPhi eps f h t` on `[0,t]`; on `(0,t)` integrability of `P_s h psi_eps(Gamma g_s)`,
`P_s h strongD eps g_s` and `HasDerivAt (strongPhi ..) (int P_s h strongD eps g_s) s`).
Uses: Lemma 3.3.20 (`G_eps in D(E)` via Prop 3.3.6 (ii) = `mem_formDomain_of_ESA`, and the bound
`Gamma(G_eps) <= Gamma_2 - rho Gamma` from `reinforced_cd`, i.e. (3.2.4)); Prop 3.3.16 (i)-(iii)/3.3.17
(`integrable_Γ₂_of_domain`); Props 3.3.5 (ii) (`gammaE_self_eq_ΓA`); (c) symmetric IBP (`ibp_of_domain`)
plus the bounded-test-function extension (T3).
The converse of Prop 3.3.17 is NOT used (only the forward direction).

## T2.  Consequences, unconditional for every FullTriple with `CD(rho,n)`, `rho >= 0`:
`FullTriple.strong_gradient_bound_unconditional`: `sqrt(Gamma(P_t f)) <= e^{-rho t} P_t(sqrt Gamma f)` a.e. (Thm 3.3.18)
(= `strong_gradient_bound hCD hrho (strongInterpolation hCD)`).
Weak form Cor 3.3.19 for `rho >= 0`: from T2 and Jensen for the sub-Markov `P_t` (only if reached).
For rho < 0 the eps-form needs the error term of GAPS.md and is NOT claimed.

## T3 (analytic lemma; the step the book states as "by density", Lemma 3.3.21, p. 164)
`ibp_bdd`: `G in A`, `MemLp G 2`, class in `D(E)`, `L G in L^1`; `k in A`, `MemLp k 2`, class in `D(E)`, `|k| <= M` a.e.
Then `int Gamma(G,k) = - int k L G`.
Book: for `k in A0` this is F7; for bounded `k in D(E)` "extended by density".  Our proof: `A0` dense in `D(E)`
(form-convergent `a_j -> [k]`), truncate `chi(a_j) in A0` (F3, `chi` smooth bounded, `chi = id` on `[-M,M]`), limit by
dominated convergence along an a.e.-convergent subsequence.  (Records a justification the book omits.)

## T4 (analytic, no triple): differentiation lemmas (L^1-differentiability of `psi o u`, product rule with an
`L^2`-differentiable bounded curve): the "derivation of Phi is then justified" step of p. 164, made explicit because
`P_s h`, `P_{t-s} f` are only a.e.-classes (no pointwise `s`-regularity).

## Out of scope / reported if not reached: G3, G3', weak-form Jensen, Gibbs corollaries (depend on T1 only).

## Status (appended after the proofs; statements above unchanged, see ERRATA E6)
* T1 `FullTriple.strongInterpolation` (`StrongMain.lean`): PROVED.  T3 `FullTriple.ibp_bdd` (`IbpBdd.lean`): PROVED.  T4 `hasDerivAt_integral_comp`, `hasDerivAt_pair`,
  `continuous_pair` (`Nemytskii.lean`, `Pairing.lean`): PROVED.  Supporting: `Orbit`, `Curve` (K-differentiability, `GB`), `PsiBounds`, `Lemma3320`, `Setup`.
* T2 strong bound `strong_gradient_bound_unconditional` (`Main.lean`): PROVED; Gibbs and OU corollaries: PROVED.  T2 weak form (Jensen): NOT done.
* G1, G3, G3': not discharged (see AUDIT_R15_INTERP_SELF.md §4).
