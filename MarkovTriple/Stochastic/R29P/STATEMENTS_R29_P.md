# Round 29, Stream P: frozen target statements

Written BEFORE any proof.  Namespace `MarkovTriple.Stochastic.R29P`.  Two open questions: (1) pointwise mass one for `IsFellerC0` + S11 (R25-E-2, R27-K-1);
(2) the converse of BGL Prop. 3.3.17 for `n = infinity` without completeness and without `Core2` (R24-B-1).

## Decisions made before proving (honest; no claim beyond what is proved)

(1) NOT settled by a proof or by a counterexample.  What is frozen is an exact characterisation: a mass deficit at `x0` is the same thing as
local non-tightness (mass escaping to infinity).  Consequences: a deficit point can exist only on a non-compact `X`, and a counterexample
must lose mass AT INFINITY for starting points converging to `x0`.  Heuristic hand analysis (not formalised, not claimed as a theorem): for a diffusion on an interval
(any `Gamma = a f'^2` is `Gamma = f'^2` in the intrinsic coordinate; a degenerate `a` pushes the singular point to infinite intrinsic distance and disconnects, contradicting F9/S10, or
leaves a regular/entrance point whose boundary condition is forced by ESA of `C_c^infty`), a loss at a single mu-null point is not expected: escape to infinity in a fixed time
from points near `x0` looks incompatible with conservativity at a fixed comparison point (the hitting time of `R` from a fixed point tends to infinity with `R`).  No Lean statement.

(2) NOT settled.  By hand (not formalised): for 1-D weighted triples `Gamma(f) = f'^2`, `L = d^2 - V' d`, `V'' >= rho`, the map `V' - rho x` is monotone, so at a finite end
either `V'` is bounded (regular end, expected to violate ESA) or `V' -> -infinity`, and then the boundary term has the favourable sign, so `Lf in L^2` would follow from `f'' , sqrt(V''-rho) f' in L^2`;
so no 1-D counterexample is expected; a counterexample, if any, is higher-dimensional or non-geometric.  The abstract proof breaks exactly where it always did (BGL Prop. 3.3.17 / ERRATA R15-1):
the bound `|int Lf g| <= C ||g||` is obtained for `g in (1-L) A_0` only (dense in `L^2`), while `Lf` itself is not known to be in `L^2`, so density in `L^2` does not identify `Lf`.
Only the real-analysis identity behind the 1-D computation is frozen as a Lean statement (P5, P6); it is not connected to a `FullTriple`.

## Statements (`Stochastic/R29P/Tight.lean`, `Stochastic/R29P/OneD.lean`)

Setting of R27 `Mass`: `X` locally compact T2 second countable Borel, `T : DiffusionTriple X` (`S : StandardTriple X` where S11 is used),
`[IsFiniteMeasureOnCompacts T.mu]`, `[T.mu.IsOpenPosMeasure]`, `hF : IsFellerC0 T`, `kappa = fellerKernelInf hF`.
```
-- P1 (no S11): mass one at x0 gives local tightness at x0 (for EVERY nearby point)
theorem fellerKernelInf_tight_of_univ_eq_one (t : R>=0) (x0 : X) (h : fellerKernelInf hF t x0 Set.univ = 1)
    (eps : R>=0inf) (heps : 0 < eps) :
    exists K : Set X, IsCompact K /\ exists U in nhds x0, forall y in U, 1 - eps <= fellerKernelInf hF t y K

-- P2 (S11): a.e.-local tightness gives mass one at x0
theorem fellerKernelInf_univ_eq_one_of_tight (S) (hF : IsFellerC0 S.toDiffusionTriple) (t) (x0 : X)
    (htight : forall eps : R>=0inf, 0 < eps -> exists K : Set X, IsCompact K /\ exists U in nhds x0,
        forall^m y dS.mu, y in U -> 1 - eps <= fellerKernelInf hF t y K) :
    fellerKernelInf hF t x0 Set.univ = 1

-- P3: the characterisation
theorem fellerKernelInf_univ_eq_one_iff_tight (S) (hF) (t) (x0) :
    fellerKernelInf hF t x0 Set.univ = 1 <-> (the hypothesis `htight` of P2)

-- P4: a deficit point forces a non-compact space
theorem fellerKernelInf_univ_eq_one_of_compactSpace [CompactSpace X] (S) (hF) (t) (x) : fellerKernelInf hF t x Set.univ = 1
theorem fellerKernelInf_deficit_noncompact (S) (hF) (t) (x) (h : fellerKernelInf hF t x Set.univ != 1) : not (CompactSpace X)

-- P5 (pure real analysis, 1-D mechanism): u, u', V1, V2 with HasDerivAt u (u' x), HasDerivAt V1 (V2 x) on [a,b], u', V2, V1, u continuous on [a,b], a <= b:
theorem oneD_boundary_identity :
    int x in a..b, (u' x - V1 x * u x / 2)^2 = int x in a..b, (u' x + V1 x * u x / 2)^2 - (V1 b * u b^2 - V1 a * u a^2) + int x in a..b, V2 x * u x^2
-- P6: if V1 a <= 0 then
--   int (u' - V1 u/2)^2 <= int (u' + V1 u/2)^2 + int V2 u^2 - V1 b * u b^2
theorem oneD_boundary_bound
```
(Reading: `u = f' sqrt(w)`, `w = e^{-V}`, `V1 = V'`, `V2 = V''`: `int (Lf)^2 w = int (u' - V'u/2)^2`, `int (f'')^2 w = int (u' + V'u/2)^2`.)

## DIFFERENCE FROM BGL
None for P1-P4 (BGL takes kernels as given; the argument is Feller continuity + Urysohn + inner regularity).  P5/P6 are a by-hand 1-D computation, not BGL's method; they are not used to prove a `FullTriple` statement.
