# Round 32, Stream Y (F8 for the round sphere `S^{n-1}`, second attempt): frozen target statements

Written BEFORE any proof.  Namespace `MarkovTriple.BGL.SphereN`; new files `Instances/SphereN/Full/{Sup,Series,F8U}.lean`.
Follows BGL §2.2 / Appendix C.5 (spherical harmonics, eigenvalues `-k(k+n-2)`).  `σ n` is the normalised measure on `S^{n-1}`,
`restr p` the restriction of a polynomial, `ev p` its evaluation on `ℝ^n`, `IsHarm k h` = homogeneous of degree `k` and `lap h = 0`.

## Plan (no new method)
(1) Sup bound of harmonic homogeneous polynomials by their `L²(σ)` norm WITHOUT mean value property: Green on the sphere
(`ibp_sphere`) and the extrinsic formula give `Σ_i ∫_S (∂_i h)² = k(2k+n-2) ∫_S h²`; Euler `k h = Σ y_i ∂_i h` and Cauchy-Schwarz
give by induction on `k` that `h(y)² ≤ |y|^{2k} (∏_{m≤k} (2m+n-2)/m) ∫_S h²`, and `∏ ≤ n^k`.
(2) Derivatives of harmonic homogeneous polynomials are harmonic homogeneous, so the same bounds hold for all `C^m` norms.
(3) Heat smoothing: for `t > 0` and ANY `u ∈ L²(σ)`, `P_t u = Σ_k e^{-λ_k t} Π_k u` (orthogonal projections onto the
finite-dimensional spaces of harmonic restrictions, `dense_span_harm`, `harm_orth`, `sphere_semigroup_harm`); since
`‖Π_k u‖ ≤ ‖u‖` and `e^{-λ_k t}` decays like `e^{-c k²}`, the series of polynomials `Σ_k e^{-λ_k t} h_k(y)` converges in `C^∞(ℝ^n)`;
its restriction to the sphere is the `L²` limit.  (So the coefficient-decay lemma `coeff_pow` is NOT needed.)

## Frozen statements
```
theorem harm_grad_L2 (hn : 2 ≤ n) {k : ℕ} {h : Pn n} (hh : IsHarm k h) :
    ∑ i, ∫ x, (restr (MvPolynomial.pderiv i h) x)^2 ∂σ n = (k : ℝ) * (2 * k + n - 2) * ∫ x, (restr h x)^2 ∂σ n

theorem harm_sup (hn : 2 ≤ n) {k : ℕ} {h : Pn n} (hh : IsHarm k h) (y : Fin n → ℝ) :
    (ev h y)^2 ≤ nrm y ^ (2 * k) * (n : ℝ) ^ k * ∫ x, (restr h x)^2 ∂σ n

theorem sphereF8_pos (hn : 2 ≤ n) {t : ℝ≥0} (ht : 0 < t) (u : Lp ℝ 2 (σ n)) :
    (sphereDiffusion n hn).semigroup t u ∈ smoothCls n

theorem sphereF8 (hn : 2 ≤ n) : SphereF8 n hn

noncomputable def sphereFullU (hn : 2 ≤ n) : FullTriple (Sph n) := sphereFull hn (sphereF8 hn)
theorem sphereFullU_CD (hn : 2 ≤ n) : (sphereFullU hn).CD ((n : ℝ) - 2) ((n : ℝ≥0∞) - 1)
theorem sphereFullU_core2 (hn : 2 ≤ n) : (sphereFullU hn).Core2
```

## Not claimed
Anything beyond the statements above.  If the proofs are not completed, the Status section appended in the proof commit lists
exactly which of them are proved; statements are never weakened silently (ERRATA row `R32-Y-n`).
