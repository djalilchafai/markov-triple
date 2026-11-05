# Round 32, Stream A2: `IsFellerC0` for the Gibbs semigroup on `R^d` under a growth hypothesis on `grad V`

Written BEFORE any proof.  Namespace `MarkovTriple.Stochastic.R32A2`; files `Stochastic/R32A2/{Comp,Lyap,Gibbs}.lean`, `AxiomCheckR32A2.lean`.

## Route (BGL-style Lyapunov / comparison argument)

By R31X `rd_isFellerC0_iff_cutoff` it suffices to show decay at infinity of the continuous representative of `P_t phi_K`.
Take the Lyapunov function `h(y) = 1/(1+|y|^2)` (`|.|` Euclidean).  With `|d_i V(y)| <= C(1+|y|_1)` one has `L h <= lam h`
(`L = Delta - grad V . grad`), and the positivity/Markov property of `P_t` gives the comparison `P_t h <= e^{lam t} h`.
Since `h` is not in `A_0`, it is approximated by `u_n = chi_n h`, `chi_n` the radial cut-offs of `GibbsRd/Cutoff.lean`
(`L u_n <= lam u_n + eps_n`, `eps_n -> 0`); `phi_K <= u_n / m` for `n` large.  Hence
`P_t phi_K <= (1/m) e^{lam t} h` a.e., so everywhere for the continuous representative, which tends to `0` at infinity.
No convexity is used for `IsFellerC0` itself (only linear growth of `grad V`); convexity enters only via the R31U bridges.

## Statements

(1) `Comp.lean` (generic; `D : DiffusionTriple E`, `[IsFiniteMeasure D.mu]`):
```
theorem semigroup_comparison (D : DiffusionTriple E) [IsFiniteMeasure D.μ] (f : D.A₀) {lam ε : ℝ}
    (hlam : 0 < lam) (hε : 0 < ε) (hL : ∀ᵐ x ∂D.μ, D.L f.1 x ≤ lam * f.1 x + ε) (t : ℝ≥0) :
    (D.semigroup t (D.cls f) : E → ℝ) ≤ᵐ[D.μ]
      fun x => Real.exp (lam * t) * f.1 x + ε * ((Real.exp (lam * t) - 1) / lam)
```
(2) `Lyap.lean` (generic `S : FullTriple (Rd d)` with `[IsFiniteMeasure S.μ] [IsFiniteMeasureOnCompacts] [IsOpenPosMeasure]`,
`hA : S.A = Afull d`, `hA₀ : S.A₀ = A₀ d`):
```
theorem rd_isFellerC0_of_lyapunov {lam : ℝ} (hlam : 0 < lam) (h : Rd d → ℝ) (hh : Continuous h) (hpos : ∀ y, 0 < h y)
    (hdec : Tendsto h (cocompact (Rd d)) (𝓝 0)) (u : ℕ → Rd d → ℝ) (hu : ∀ n, u n ∈ A₀ d)
    (hu0 : ∀ n y, 0 ≤ u n y ∧ u n y ≤ h y) (hue : ∀ n y, ‖y‖ ≤ n → u n y = h y)
    (ε : ℕ → ℝ) (hεpos : ∀ n, 0 < ε n) (hε0 : Tendsto ε atTop (𝓝 0))
    (hL : ∀ n x, S.toDiffusionTriple.L (u n) x ≤ lam * u n x + ε n) : IsFellerC0 S.toDiffusionTriple
```
(3) `Gibbs.lean` (`G : GibbsRdData d`):
```
theorem gibbsRdFull_isFellerC0_of_linGrowth (G : GibbsRdData d) {C : ℝ}
    (hC : ∀ (x : Rd d) (i : Fin d), |pderiv G.V i x| ≤ C * (1 + ∑ j, |x j|)) :
    IsFellerC0 G.gibbsRdFull_unconditional.toDiffusionTriple
theorem gibbsRdFull_isFellerC0_of_hessBdd (G : GibbsRdData d)
    (hH : ∃ C, ∀ (x : Rd d) (i j : Fin d), |pderiv (pderiv G.V i) j x| ≤ C) :
    IsFellerC0 G.gibbsRdFull_unconditional.toDiffusionTriple      -- i.e. grad V Lipschitz
noncomputable def gibbsRdFull_bridge_of_linGrowth (G : GibbsRdData d) (hV : HessGe G.V 0) {C : ℝ} (hC : <as above>) :
    MarkovProcessBridge G.gibbsRdFull_unconditional.toDiffusionTriple      -- via R31U
```
In particular, `HessGe V rho` (`rho > 0`) together with bounded Hessian gives an unconditional bridge.

## Not claimed
* The elliptic `fullU` and Riemannian `riemFull_unconditional` instances (growth hypotheses on the coefficients are not formulated here).
* The d = 1 counter-model `V = e^{x^2}` (failure of decay) is NOT formalised; it stays informal (ERRATA R31-X-1).
* Necessity of any growth hypothesis.

## DIFFERENCE FROM BGL
BGL does not treat the `C_0`-Feller property.  The Lyapunov comparison `L h <= lam h => P_t h <= e^{lam t} h` is the standard
sub-solution / maximum-principle argument for Markov semigroups (positivity, BGL Sect. 1.2); the extra step (cut-off
approximation, since `h` is not in `A_0`) is a standard truncation.
