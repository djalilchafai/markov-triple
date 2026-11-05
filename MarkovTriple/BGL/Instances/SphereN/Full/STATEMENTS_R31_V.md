# Round 31, Stream V (F8 for the round sphere `S^{n-1}`): frozen target statements

Written BEFORE any proof.  Namespace `MarkovTriple.BGL.SphereN`; file `Instances/SphereN/Full/F8.lean`.
Follows BGL §2.2 / Appendix C.5 (spherical harmonics, eigenvalues `-k(k+n-2)`).

## GOAL (honest scope)
Discharge `SphereF8 n hn` (`P_t f ∈ C^∞(S^{n-1})` for `f ∈ 𝒜₀`), i.e. an unconditional `sphereFull`.  The R29 GAPS entry
records the obstruction: smoothness of `P_t f = Σ_k e^{-λ_k t} proj_k f` needs `C^m` bounds on the harmonic projections.
This is a large analytic task (sup-norm bounds for harmonic polynomials, `L²` decay of `proj_k f` via `L^m f`, `C^m`
convergence of the series).  It is NOT claimed that it will be closed.  The frozen targets below are the part planned as
certain; anything beyond is recorded in the Status section / GAPS.

## Planned, certain
```
theorem sphereF8_zero (hn : 2 ≤ n) (f : (sphereDiffusion n hn).A₀) :
    ∃ g ∈ A₀S n, ((sphereDiffusion n hn).semigroup 0 ((sphereDiffusion n hn).cls f) : Sph n → ℝ) =ᵐ[σ n] g
theorem sphereF8_iff (hn : 2 ≤ n) :
    SphereF8 n hn ↔ ∀ (t : ℝ≥0) (f : (sphereDiffusion n hn).A₀),
      (sphereDiffusion n hn).semigroup t ((sphereDiffusion n hn).cls f) ∈ smoothCls n
theorem sphereF8_of_span (hn : 2 ≤ n) (t : ℝ≥0) {u : Lp ℝ 2 (σ n)}
    (hu : u ∈ Submodule.span ℝ {v | ∃ p : Pn n, v = (sphereDiffusion n hn).cls ⟨restr p, restr_mem p⟩}) :
    (sphereDiffusion n hn).semigroup t u ∈ smoothCls n
```
(`sphereF8_of_span` is the linear extension of `sphere_semigroup_poly_mem`.)

## Not claimed
`SphereF8 n hn` for all `f`, and unconditional `sphereFull`, unless a Status section appended in the proof commit says so.
