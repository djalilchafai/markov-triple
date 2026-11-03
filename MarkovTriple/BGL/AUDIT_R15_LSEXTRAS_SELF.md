# R15 self-audit: `n = 1` stage of BGL Thm 5.7.4 and optimality of `(n-1)/(ρ n)` (author's own attack, before the hostile audit)

Statements: `MarkovTriple/BGL/Theory/STATEMENTS_R15_LSExtras.md` (written before the proofs; only additions, no change).
Files: `Theory/LSToPI.lean`, `Theory/LogSobolevDimOne.lean`, `Instances/Sphere/LSOptimal.lean`, `Instances/Circle/Poincare.lean`,
`Instances/Circle/LSOne.lean`.  Build: 0 errors, 0 warnings, no `sorry`, axioms only `propext, Classical.choice, Quot.sound`.

## Attacks and findings

1. **Vacuity of the `n = 1` theorem.**  `compact_logSobolev_one` needs `CD 0 1` and `PI c`.  Both are theorems for the library circle
   (`circle_CD_zero_one` existing, `circle_PI` new, `c = 1/(4π²)`), so the hypotheses are satisfiable and the conclusion
   `circle_LS` is a genuine instance.  `FiniteDimInterpolation (1/c)` is *proved* (not assumed) for compact triples with `CD(0,1)`, `P(c)`.
   For `c < 1/(4π²)` the hypothesis `PI c` is false on the circle (`circle_not_PI_lt`), so the theorem cannot be applied there: consistent.
2. **Edge `n = 1`.**  `FullTriple.CD` has the conjunct `1 ≤ n`; `(1⁻¹).toReal = 1`, so `CD 0 1` is `Γ₂ ≥ (Lf)²`.  Used correctly in
   `integral_exp_Γ₂_ge_one` (the `hinv` step).  No constant `dimLSConst ρ 1` is defined (it would be the junk `0/0 = 0`); the `n = 1`
   constant is the Poincaré constant `c`.  The generalisation `c ≠ 1` of the book's `P(1)` is a deviation (scale-free; book: `c = 1`
   for the `2π`-torus; library circle has period 1).  `n = ∞`: not part of this stage (Prop. 5.7.1 is in `LogSobolevMain`).
3. **Consistency with the `n > 1` theorem as `n → 1`.**  `ρ n/(n-1) → 1` is only meaningful with `ρ = n-1` (`CD(n-1,n)`, sphere `S^n`);
   for `n = 1` that is `CD(0,1)`, circle, and `(n-1)/(ρ n) := c`.  Not a formal statement (no limit theorem is claimed); the book's
   phrase "with the convention `ρn/(n-1) = 1`" is realised only through the hypothesis `P(c)`.
4. **Dual Poincaré (Prop. 4.8.3).**  The book states it on `𝒟(L)`; `integral_Γ_le_of_PI` is stated for `f ∈ 𝒜₀` (all that is needed, `f = e^{g/2}`
   with the explicit hypothesis `he : e^{g/2} ∈ 𝒜₀`, the book's "Prop. 3.3.17 applies"; automatic on compact triples).  The proof does not
   use the semigroup (Cauchy-Schwarz/Young on `∫(f-m)Lf`).
5. **`LS ⇒ PI` hypothesis `1 ∈ 𝒜₀`.**  The library's `LS`/`PI` live on non-unital `𝒜₀` for general triples; `PI_of_LS` is stated under
   `(fun _ => 1) ∈ T.A₀`.  Unconditional only for `CompactTriple` (`PI_of_LS`).  For OU/Lebesgue/Gibbs triples (non-unital `𝒜₀`) the
   implication is NOT formalized; it would need `LS.extend` and `1 ∈ 𝒟(ℰ)` (open).  Not vacuous: the circle and sphere satisfy it.
6. **Taylor step.**  Book: `Ent(f²) = 2ε²∫g² + o(ε²)`.  Here only the lower bound `Ent ≥ 2ε²∫g² - 8M³ε³ - ε⁴(∫g²)²` is proved
   (enough since LS bounds `Ent` from above).  Junk values: `f = 1 + εg` with `|εg| ≤ 1/2` is `≥ 1/2 > 0`; `Real.log (x^2) = 2 log x`
   holds for all real `x` (`Real.log_pow`); `Ent` is the genuine entropy (`integrable_sq_mul_log_sq` for `f ∈ 𝒜₀`, `μ` probability).  The bound
   `x log x ≤ x(x-1)` is used for `x = 1 + ε² ∫ g² > 0`.  Limit `ε → 0+` via `𝓝[>] 0`.
7. **a.e. vs everywhere.**  Identities between `Γ`, `Γ₂`, `L` hold a.e. (as in the library); eigenfunction equation `L f = -λ f` a.e.;
   `Γ(1,h) = 0` a.e. (from the diffusion property `ψ(r) = r²`, needs `1 ∈ 𝒜₀`).  No everywhere claim is made.
8. **Sharpness on `S³`.**  The triple is the *zonal* sphere (functions of the polar angle, weight `(2/π) sin²θ`): `sphere_not_LS_lt` says `LS(c)`
   fails on the class `𝒜₀` of *this* triple (zonal smooth functions) for `c < 1/3`.  Since `𝒜₀ ⊂ 𝒟(ℰ)`, failure on `𝒜₀` implies failure on
   the form domain; on the full `S³` (non-zonal functions) the same inequality fails a fortiori, but that is not a statement about a library object.
   `c ≤ 0` is excluded by the `0 < C` conjunct of `LS`/`PI`, and `not_PI_of_eigen_pos` also handles `c ≤ 0` (hypothesis `c < 1/λ` only).
   The eigenfunction is `UZ 1 = 2x` (`λ = 3`, `∫ f² = 1` by the existing orthonormality `inner_eZ`).
9. **Optimality means: no smaller constant in the library's `LS(c, 0)`**; it is *not* a statement about `LS(c, D)` with `D > 0` (the book's
   `LS(C,D)` is weaker; no claim).
10. **Circle normalisation.**  Library circle `ℝ/ℤ`, `Γ(f) = f'²`: `λ₁ = (2π)²`, constant `1/(4π²)`.  The book's `2π`-torus gives `1`; the statement
    here is the same inequality after scaling (not proved as a scaling lemma).  `circle_PI` is *new* (not in the repo before): `circle_var_le` is
    Wirtinger via Mathlib's Parseval (`AddCircle.hasSum_sq_fourierCoeff`) and `fourierCoeffOn_of_hasDerivAt`.
11. **Duplication risk.**  `tendsto_entE_of_PI`, `ent_le_fisher_of_PI`, `ent_sq_add_le_of_PI`, `logSobolev_of_PI_finiteDim` are textual copies of existing
    proofs with `P(c)` instead of `CD(ρ,n), ρ > 0`; a future change in the originals would not propagate.  (Could be unified by refactoring
    `tendsto_entE` to take `P(c)`; not done: new-files-only rule.)
12. **What is NOT covered** (exact): non-compact `FullTriple`s for `n = 1` (only the named structure `FiniteDimInterpolation` + `EntropyInterpolation`
    are available there, as in R14); `LS ⇒ PI` for non-unital `𝒜₀`; optimality for `Sⁿ`, `n ≠ 3`, and for the Jacobi operator (not in the repo);
    optimality of constants for `D > 0`; the book's remark on Prop. 5.7.5 (interval, Neumann/periodic) - not formalized.

## Attack surface for the hostile auditor
* `FullTriple.integral_exp_Γ₂_ge_one`: check the algebra against the book's p. 272-273 (a = 1/3 step, (5.7.8) at a = 1/2, Y ≥ 0 step) and the
  general-`c` generalisation `(1/c) ∫ e^g Γ ≤ ∫ e^g Γ₂`.
* `DiffusionTriple.PI_of_LS`: hypothesis `1 ∈ 𝒜₀`; the `D = 0` restriction; correctness of `log_sq_lower` constants (`8`, `|t| ≤ 1/2`).
* `CompactTriple.compact_logSobolev_one`: `FiniteDimInterpolation (1/c)` pins `κ = 1/c`; confirm `logSobolev_of_PI_finiteDim` is not vacuous for large `κ`
  (the structure is false for `κ` above the true rate; same caveat as `logSobolev_of_finiteDim`, audit R14-3).
* `circle_var_le` and `fourierCoeff_cx_D`: integration by parts on `[0,1]`, `n = 0` case, periodicity `F(0+1) = F(0)`.
* `sphere_not_PI_lt`: eigenfunction identification (`LZ_UZ`, `inner_eZ`), `sCompact.toDiffusionTriple` unfolds to `sT` by `rfl`-level defeq.
* Whether "optimality" as formalized (non-existence of `LS(c, 0)` for `c < 1/3` on the zonal triple) matches the book's claim.
