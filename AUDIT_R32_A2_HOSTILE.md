# Hostile audit, Round 32 Stream A2 (IsFellerC0 for Gibbs on R^d under linear growth of grad V)

Verdict: **ACCEPT-WITH-DOC-FIXES** (one INFO doc fix applied: ERRATA R32-A2-4; no soundness issue found).

## Mechanical checks
* Merged `worktree-agent-a1dfa92c98d0c7a0e` (freeze f9082df, proofs e2082ee). Full `lake build`: success (9602 jobs), log has 0 occurrences of "warning"/"error".
* `grep` for sorry / set_option / native_decide / axiom in `Stochastic/R32A2/*` (excluding the AxiomCheck file): none.
* `#print axioms` for all 10 declarations in `AxiomCheckR32A2.lean` (semigroup_comparison, rd_isFellerC0_of_lyapunov, Lr_hL_le, cut_bounds_lin, gibbsRdFull_isFellerC0_of_linGrowth, ..._of_hessBdd, gibbsRdFull_bridge_of_linGrowth, ..._of_hessBdd, cosData_isFellerC0, cosData_bridge): all `[propext, Classical.choice, Quot.sound]`.
* `python3 scripts/check_frozen.py`: OK.
* Git: f9082df touches exactly `STATEMENTS_R32_A2.md` (new) and `frozen-manifest.json` (+5 lines, own entry). `git diff main -- frozen-manifest.json` is that one entry only. The statements file differs between f9082df and HEAD only by the appended Status section.

## Soundness (re-derived on paper)
(a) `semigroup_comparison`: Phi(s)=<P_s[f],eta>, Phi' = <P_s[Lf],eta> (hasDerivAt_semigroup_cls, s>0), Lf - lam f <= eps a.e. and sub-Markov (`semigroup_le_const`, needs finite mu so constants are in L2) give P_s(Lf - lam f) <= eps a.e., hence Phi' <= lam Phi + eps m for eta >= 0; Psi=e^{-lam s}(Phi+eps m/lam) has Psi' <= 0, Psi antitone on [0,inf) (continuity at 0 from strong continuity), so Phi(t) <= e^{lam t}Phi(0)+eps m (e^{lam t}-1)/lam; test eta = 1_B, B={v>kappa}, gives mu(B)=0. Correct; hypotheses (a.e. inequality, finite mu, lam, eps>0) honest.
(b) `rd_isFellerC0_of_lyapunov`: hypotheses are satisfiable (instantiated by the Gibbs proof and by cosData/gaussData) and are not contradictory. Conclusion is the R24 `IsFellerC0` (single definition in `Stochastic/R24/Operator.lean`, no shadowing). Step: phi_K <= m^{-1} u_n a.e. (on ||y||<=R+1 use u_n=h>=m, outside cutoff=0), P_t monotone, comparison, u_n<=h, eps_n->0, a.e. to everywhere by continuity (`le_of_ae_le_cont`, open-pos), squeeze with h->0; then R31X `rd_isFellerC0_iff_cutoff` (needs hA, hA0, supplied by `rfl`). Valid. ERRATA R32-A2-1 (binder `n : N`) is pure type ascription.
(c) Gibbs: phi(s)=1/(1+s^2), phi'=-2s/(1+s^2)^2, phi''=(6s^2-2)/(1+s^2)^3 (checked), Gamma(q)=4q, -Lq <= 3C'(d+1)(1+q) (via (sum|y|)^2<=d q). L h <= 2qA(1+q)/(1+q^2)^2 + 12/(1+q^2) <= (3A+12)h, using 2q(1+q)<=3(1+q^2) and 12q^4-24q^3+24q^2+8q+12>0. |d_i h|<=6h checked. Cut-offs: |L cut_R| <= B(d+dC') because |dV||d cut| <= C'(1+l)|d cut| <= C'B from the weighted derivative bounds (1+l/R)^2|d cut|<=B/R. L(cut h) = cut Lh + h L cut + 2 Gamma(cut,h) <= lam cut h + (K+12dK) h on {q>=R^2} where h<=1/(1+R^4); zero-derivative case inside. All correct. Honest: only linear growth is used.
(d) Non-vacuity: `cosData` (V=|x|^2/2+cos(x_0)/2, HessGe 1/2, bounded Hessian, proved BddHess3) and `gaussData` instantiate `..._of_hessBdd`; `cosData_bridge` builds HessGe V 0 from HessGe 1/2 by nlinarith. Gaussian sanity: R30S `gaussRdFull_bridge_all` is an independent unconditional bridge (Mehler); the two are consistent (both give a Feller/bridge for the Gaussian). Caveat (INFO): the equality `gibbsRdFull_unconditional (gaussData d) = gaussRdFull d` is not stated formally in this stream, so the cross-check is informal. No contradiction with R31-X: V=e^{x^2} has |V'|=2|x|e^{x^2}, super-linear, outside the hypothesis.
(e) ERRATA R32-A2-1: confirmed type-ascription only.
(f) Honesty: Status/GAPS/ERRATA R32-A2-2/3 claim nothing for fullU, riemFull, 1-D gibbsFull, necessity, or unconditional bridge beyond `linGrowth` + `HessGe V 0`. "Convexity unused for IsFellerC0" is accurate (the Feller theorems take no HessGe; `GibbsRdData` has no rho). Note HessGe V 0 is still required for the bridge via R31U.

## Findings
* INFO-1 (doc, fixed): frozen Route prose says h=1/(1+|y|^2); delivered/proved h=1/(1+|y|^4) (needed). Recorded as ERRATA R32-A2-4; statements unaffected.
* INFO-2: the Gaussian cross-check with `gaussRdFull_bridge_all` is not a formal identification of the two triples.
* No LOW/MEDIUM/HIGH findings.
