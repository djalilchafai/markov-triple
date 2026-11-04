# STATEMENTS R26-I -- `Core2`: abstract reductions and the first eigenbasis criterion

Method "Armstrong": statements first.  Namespace `MarkovTriple.BGL`, directory `MarkovTriple/BGL/Theory/Extension/R26/`
(the brief's `BGL/Extension/R26/*`).  `T : FullTriple E`.

## Scope and honest framing

The open item is `Core2` for complete triples with `CD`.  After analysis (see `GAPS.md`, Round 26-I) no abstract
BGL theorem `IsComplete + CD(rho,n) => Core2` is claimed or attempted: the abstract objects (`FullTriple`) carry no
hypoellipticity (no statement that `(1-L)^{-1}` maps `A_0` into `A`), and the fourth-order cut-off needs control of
`L L zeta`, `Gamma(zeta, Gamma(zeta, .))`, `Gamma_2(zeta,b)` that is not a consequence of `IsComplete`.  What is stated
here is (A) an exact orthogonality form of `Core2` (the shape a counterexample must have) and (B) a criterion that
proves `Core2` for triples whose test algebra contains an eigenbasis, applied to the compact zonal sphere.

## Statements

* **I1** `FullTriple.core2_iff_orth : T.Core2 <-> forall w : Lp R 2 T.mu, (forall b : T.A0, inner R (Psil T b) w = 0) -> w = 0`
  where `Psil T b = [b] - 2[L b] + [L L b] = (1-L)^2 b`.  (Counterexample shape: a nonzero `L^2` vector orthogonal to
  `(1-L)^2 A_0`.)
* **I2** `FullTriple.core2_of_eigen (S : Set T.A0) (c : T.A0 -> R)`, `0 <= c phi` for `phi in S`,
  `T.L phi =ae -(c phi) * phi` for `phi in S`, and `(Submodule.span R (T.cls '' S)).topologicalClosure = top`
  (the classes of the eigenfunctions in `S` span a dense subspace of `L^2`) imply `T.Core2`.
* **I3** `sFull_core2 : sFull.Core2` for the compact zonal sphere `S^3` (`Instances/Sphere`), from I2 with the
  Chebyshev eigenfunctions `U_k` (`L U_k = -k(k+2) U_k`) and `dense_span_eZ`.

## DIFFERENCE FROM BGL

BGL (p. 161-162) uses `Core2` tacitly (ERRATA R15-1).  I2/I3 are new, elementary, not in the book: when `A_0` contains a
complete eigensystem `(1-L)^2` acts diagonally by `(1+c)^2` and its range contains every eigenvector.
