# Round 31, Stream X: frozen target statements (decay at infinity / `IsFellerC0` for the `R^d` Gibbs / elliptic / Riemannian `FullTriple`s)

Written BEFORE any proof.  Namespace `MarkovTriple.Stochastic.R31X`, file `Stochastic/R31X/Cutoff.lean` (+ `AxiomCheckR31X.lean`).

## Decisions made before proving (honest)

* The expected target "`HessGe V rho`, `rho > 0` implies `IsFellerC0`" is NOT stated as a theorem: a pen-and-paper analysis indicates it is FALSE without a growth
  condition on `grad V` (1-d model `V = e^{x^2}`: `Hess V >= 2`, but `int^infty dx / V'(x) < infinity`, so `+-infinity` is an ENTRANCE boundary of the
  diffusion `L = d^2 - V' d`; then `Q_t f(x)` does not tend to `0` as `|x| -> infinity` for `0 <= f in C_c`, `f != 0`).  A Bakry-Emery / `CD(rho,inf)` argument cannot
  exclude this since `CD(rho,inf)` only constrains `V` from below.  This is recorded as an informal obstruction (GAPS, ERRATA R31-X-1); NO formal proof of the failure is claimed.
* What is stated and proved: a sharpening of G2 (`rd_isFellerC0_iff_decay`, R30T) which reduces decay at infinity, for ALL `f in C_c`, to decay for ONE cut-off function
  per compact set (positivity of the semigroup + squeeze).  This is the exact form in which any future Lyapunov / tightness estimate has to be fed.

## Statement (`Stochastic/R31X/Cutoff.lean`)

Setting: `d : N`, `S : FullTriple (Rd d)` with `[IsFiniteMeasureOnCompacts S.toDiffusionTriple.mu] [S.toDiffusionTriple.mu.IsOpenPosMeasure]`, `hA : S.A = Afull d`, `hA0 : S.A_0 = A_0 d`.
```
theorem rd_isFellerC0_iff_cutoff (hA : S.A = Afull d) (hA₀ : S.A₀ = A₀ d) :
    IsFellerC0 S.toDiffusionTriple ↔ ∀ (t : ℝ≥0) (K : Set (Rd d)), IsCompact K →
      ∃ φ : C_c(Rd d, ℝ), (∀ y, 0 ≤ φ y ∧ φ y ≤ 1) ∧ (∀ y ∈ K, φ y = 1) ∧
        ∀ g : C(Rd d, ℝ),
          (S.toDiffusionTriple.semigroup t (ccL2 S.toDiffusionTriple φ) : Rd d → ℝ) =ᵐ[S.toDiffusionTriple.μ] g →
            Tendsto g (cocompact (Rd d)) (𝓝 0)
```
Instance corollaries (by `rfl` for `hA, hA0`): `gibbsRdFull_isFellerC0_iff_cutoff`, `fullU_isFellerC0_iff_cutoff`, `riemFull_isFellerC0_iff_cutoff`.

## DIFFERENCE FROM BGL
None: BGL does not discuss this property.  The statement is positivity + squeeze for the Markov semigroup (BGL Section 1.2.1, positivity / Markov property).
