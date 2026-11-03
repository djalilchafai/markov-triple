# Round 16 (Jensen stage): target statements, fixed BEFORE the proofs

Book: BGL, Thm 3.3.18 and Cor 3.3.19 (p. 163: "by Jensen's inequality for P_t, which is sub-Markov"), Thm 3.3.23 (pp. 164-165).
No frozen definition (`GradientInterpolation`, `HasGradientBound`, ...) is modified.

## J1 (generic, no triple, no kernel): `jensen_sq`
`P : L^2(mu) ->L[R] L^2(mu)` with (pos) `u >= 0 a.e. => P u >= 0 a.e.` and (sub-Markov) `u <= 1 a.e. => P u <= 1 a.e.` (u in L^2).
`w, W in L^2(mu)`, `0 <= w` a.e., `W = w^2` a.e.  Conclusion: `(P w)^2 <= P W` a.e.
(The class of w is exactly: nonnegative, in L^2, with w^2 in L^2 (the class W is given); no boundedness; mu may be infinite.)
Proof plan: u_n = min(1, n w) in L^2; for q in Q: 0 <= P((w - q u_n)^2) = P(w^2) - 2q P(w u_n) + q^2 P(u_n^2) <= P(w^2) - 2q P(w u_n) + q^2,
hence (P(w u_n))^2 <= P(w^2); w u_n -> w in L^2 (dominated convergence), subsequence a.e.

## J2: `FullTriple.gradient_bound_unconditional`
`T : FullTriple E`, `hCD : T.CD rho n` (any n), `0 <= rho`, `f : T.A0`, `t : R>=0`.
Conclusion = exactly that of the conditional `FullTriple.gradient_bound`:
`Gamma(P_t f) <= e^{-2 rho t} P_t(Gamma f)` a.e. (P_t Gamma f = semigroup t [Gamma f], Gamma f in A0).  Book Cor 3.3.19.
Route: `strong_gradient_bound_unconditional` (Thm 3.3.18), square (both sides >= 0), `jensen_sq` with P = semigroup t, w = sqrtGamma f.

## J3: consequences
`FullTriple.hasGradientBound_unconditional : HasGradientBound T.toDiffusionTriple T.A rho` (same proof as `FullTriple.hasGradientBound`);
`FullTriple.conservative_of_complete_unconditional` (Thm 3.3.23 first claim) for complete T with CD(rho,n), rho >= 0, no GradientInterpolation;
Gibbs (R): `gibbsFull_gradient_bound_unconditional`, `gibbsFull_hasGradientBound`; Gibbs (R^d, explicit WeakHypo/F8): `gibbsRdFull_gradient_bound_unconditional`.
OU and Lebesgue already had unconditional weak bounds (own proofs); not re-derived.

## J4: NOT claimed (reported open)
rho < 0 (needs the eps-form with error term, GAPS.md); `GradientInterpolation` (G1: not a book statement); G3, G3'.
