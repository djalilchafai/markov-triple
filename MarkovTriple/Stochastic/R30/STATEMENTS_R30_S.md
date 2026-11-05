# Round 30, Stream S (stochastic layer): frozen target statements

Written BEFORE any proof.  Namespace `MarkovTriple.Stochastic.R30`.  Goal: an unconditional `MarkovProcessBridge` for `gaussRdFull d`
(`d >= 1`), by discharging the two hypotheses of R29's `gaussRdFull_bridge_of_rep` (`Stochastic/R29/GaussRd.lean`).

Notation: `gam d = Measure.pi (fun _ => gaussianReal 0 1)`, `mehlerKernelRd d t x = (gam d).map (z |-> e^{-t} x + sqrt(1-e^{-2t}) z)` (R29),
`T := (gaussRdFull d).toDiffusionTriple`.

## S1. the reference measure is the product Gaussian (all `d`)
```
theorem gaussRdFull_mu (d : N) : (gaussRdFull d).toDiffusionTriple.mu = gam d
```
(The Gibbs normalisation `Z = int exp(-|x|^2/2) dx` is `(2 pi)^{d/2}`; proved through `gam d = volume.withDensity (prod of Gaussian pdfs)`.)

## S2. the Mehler formula for the Friedrichs semigroup on the test class
```
theorem gaussRdFull_isTestClassRep (hd : 1 <= d) : IsTestClassRep (gaussRdFull d).toDiffusionTriple (mehlerKernelRd d)
```
i.e. for `t >= 0`, `f in C_c^infty(R^d)` and `u in L^2(gam d)` with `u = f` a.e.: `P_t u (x) = int f(e^{-t} x + sqrt(1-e^{-2t}) y) d gam(y)` for a.e. `x`.
Route (BGL Sect. 2.7.1, no Hermite completeness in dimension `d`): `Q_s f(x) = int f(e^{-s} x + c_s y) dgam(y)` is smooth in `x`, `C^1` in `s > 0` as an
`L^2(gam)`-valued map with `d/ds Q_s f = L Q_s f` (Gaussian integration by parts); Duhamel/energy argument `s |-> <P_{t-s} phi, Q_s f>` is constant
(`phi in C_c^infty`), using the core property F10 of the Full triple and symmetry `<L v, w> = <v, L w>` for `v` in the Friedrichs domain, `w` smooth with `w, L w in L^2`.

## S3. the bridge
```
noncomputable def gaussRdFull_bridge (hd : 1 <= d) : MarkovProcessBridge (gaussRdFull d).toDiffusionTriple
theorem gaussRdFull_bridge_kernel (hd) (t) (x) : (gaussRdFull_bridge hd).kernel t x = mehlerKernelRd d t x
theorem gaussRdFull_bridge_isMarkov (hd) (t) (x) : (gaussRdFull_bridge hd).kernel t x Set.univ = 1
```
(The bridge is `R29.gaussRdFull_bridge_of_rep (gaussRdFull_mu d) (gaussRdFull_isTestClassRep hd)`.)

Whatever is not delivered is reported in the Status section (to be appended in the proof commit), GAPS and ERRATA, not silently dropped.
