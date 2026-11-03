# Round 16 (Entropy stage): target statements, fixed BEFORE the proofs

Book = BGL, Prop 5.5.3 / Prop 5.7.1 / Thm 5.7.4 (pp. 266-272; "for t>0, P_t f is in A and bounded together with
Gamma(P_t f) and L P_t f" p. 270).  Frozen structures `EntropyInterpolation` (LogSobolev.lean),
`FiniteDimInterpolation` (LogSobolevDim.lean) are NOT modified.  Notation: `g_s = eps + Pt s.toNNReal phi`,
`e(s) = int g_s log g_s`, `I(s) = int Gamma(g_s)/g_s`, `u_s = Gamma(P_s phi)`.

## Standing hypotheses and why
* `[IsFiniteMeasure T.mu]` (needed: for infinite mu, `g_s log g_s` is not integrable (constant `eps log eps`), the Bochner
  integral is the junk value 0, `entE` is constant 0 while `entI` is generally > 0, so `e' = -I` is FALSE; see AUDIT).
* `0 <= phi` a.e. and `phi <= M` everywhere (as in the frozen structure).
* `hCD : T.CD rho n` with `0 <= rho` (only for the steps that need `Gamma(P_s phi)` bounded / Thm 3.3.18) and
* `BddGamma T`: `forall phi : T.A0, exists B, Gamma(phi) <= B a.e.` (book: "bounded together with Gamma(P_t f)", p. 270;
  NOT derivable for an abstract `FullTriple`, since `A0 ⊂ L^p` only gives `Gamma phi ∈ L^p`; true for compact triples
  and for every instance whose `A0` consists of bounded functions with bounded gradient).

## E1 (unconditional in the triple, finite mu)
`FullTriple.entE_continuousOn`  : `ContinuousOn (entE phi eps) (Ici 0)`  (eps>0, 0<=phi a.e., phi<=M).
`FullTriple.entI_continuousOn`  : `ContinuousOn (entI phi eps) (Ici 0)`.
`FullTriple.hasDerivAt_entE`    : `HasDerivAt (entE phi eps) (-entI phi eps s) s` for all `s > 0` (de Bruijn, Prop 5.5.3).
Route: `L^2`-differentiability of `s ↦ P_s phi` (Interp `hasDerivAt_orb`), chain rule for the compactly supported
smooth `Θ` (`x log x` on `[eps, eps+M]`), `ibp_bdd` with `k = Θ'(g_s)`, `Γ(g,Θ'(g)) = Θ''(g) Γ(g) = Γ(g)/g`.

## E2 (analysis, no triple): product/quotient rule `r ↦ ∫ u_r / g_r`
`u : R → L^1` differentiable at `s`, `g : R → L^2` differentiable at `s`, `g_r >= eps` a.e., `u_s ∈ L^∞`, `u_r >= 0` :
`d/dr ∫ u_r/g_r = ∫ u'/g_s - ∫ u_s g'/g_s^2`.   (Replaces the Nemytskii technique by the bounded-`u_s` trick.)
Consequence `FullTriple.hasDerivAt_entI_formula` (under `BddGamma`, `rho >= 0`): `I'(s) = ∫ [2Γ(g,Lg)/g - Γ(g) Lg/g^2]`.

## E3 (identification, if reached) `FullTriple.entropyInterpolation (hCD) (hρ : 0 ≤ ρ) [IsFiniteMeasure] (hB : BddGamma T) :
T.EntropyInterpolation`: the remaining fields (integrability of `gΓ₂(Λ∘g)`, `gΓ(Λ∘g)`, and `I' = -2 J`).

## E4 consequences (if E3 reached): `logSobolev_of_CD_infty` for non-compact full triples with CD(rho,∞), rho>0,
probability measure, `BddGamma`; Gibbs / OU corollaries.  FiniteDimInterpolation fields `bdd`, `ext`: only attempted
after E3.

Out of scope here: rho<0; infinite mu.

## Status (appended after the proofs; statements above unchanged, see ERRATA R16-E1..E3)
* E1 PROVED: `FullTriple.entE_continuousOn`, `entI_continuousOn`, `hasDerivAt_entE` (`EntropyDeBruijn.lean`; finite `μ`, no `CD`).
* E2 PROVED as analysis: `continuous_integral_div`, `hasDerivAt_integral_div`, `hasDerivAt_integral_smooth`, `continuous_integral_smooth`
  (`EntropyQuot.lean`, `EntropyAnalysis.lean`).
* E3 PROVED: `FullTriple.entropyInterpolation` (`EntropyMain.lean`), via `entI_eq_neg_pair`/`hasDerivAt_entI_pair` (`EntropyFisher.lean`),
  `Γ₂_comp` (`EntropyChain.lean`), `fisher_alg` (`EntropyIdentity.lean`), `fisherHyp` (`EntropyMain.lean`).  `BddGamma` not needed (R16-E1).
* E4: `logSobolev_unconditional`, `logSobolev_domain_unconditional`, `gibbsFull_logSobolev_unconditional` PROVED (`EntropyApplications.lean`);
  `FiniteDimInterpolation.bdd` PROVED (`finiteDim_bdd`); `ext` NOT proved (reduction `finiteDimInterpolation_of_ext`, `logSobolev_dim_of_ext`).
