# R14 self-audit (adversarial) of the Thm 5.7.4 (`n < ∞`) statements

Targets: `Theory/STATEMENTS_R14_LSIDim.md`.  Files: `Theory/LogSobolevDimChain.lean`, `Theory/LogSobolevDim.lean`,
`Instances/Sphere/LogSobolevDim.lean`.  Attacks performed BEFORE proving (A), and the outcome (R).

1. **Vacuity of `CD ρ n`, finite `n`, `ρ > 0`.**  (A) is there a triple with `Γ ≠ 0`, `ρ > 0`, `n < ∞`?  (R) yes: zonal `S³`,
   `sphere_CD_two_three : CD 2 3`, `sphere_Γ_ne_zero` (existing).  OU (`n = ∞` only) and circle (`ρ = 0`) give no finite-`n` instance.
2. **Vacuity of the named structure `FiniteDimInterpolation κ`.**  (A) could `bdd`/`ext` be unsatisfiable?  (R) both are THEOREMS on every
   compact triple (`CompactTriple.finiteDimInterpolation`), witnessed on the sphere (`sphere_finiteDimInterpolation`, `κ = 3`).
   `ext` is only claimed for `κ = ρ n/(n-1)` coming from `CD ρ n`; for larger `κ` it would be false (not an issue: it is a hypothesis,
   and the theorem then says nothing).  `bdd`: `B` is a common bound, no junk (`|L f| ≤ B` and `Γ f ≤ B` a.e.).
3. **`n ≤ 1` edge cases.**  `1 < n` is a hypothesis (`n = 1`: `m/(m-1)` junk; the book treats the torus separately, p. 272).  `n = ⊤`
   excluded in Thm 5.7.4's finite form (`n ≠ ⊤`); `dimLSConst ρ ⊤ = 1/ρ` (`dimLSConst_top`) agrees with Prop. 5.7.1.
   `dimLSConst_lt` needs `1 ≤ n` (for `n = 0`, `0⁻¹ = ⊤`, toReal junk): hypothesis added (see ERRATA R14-1).
4. **Constant as `n → ∞`.**  `dimLSConst_tendsto : (n:ℕ) → ∞ ⇒ dimLSConst ρ n → 1/ρ`; `dimLSConst_eq : = 1/(ρ n/(n-1))` for `1<n<∞`;
   `dimLSConst_lt : < 1/ρ` for `ρ > 0`, `n < ∞`.  `sphere_LS_dim_lt : 1/3 < 1/2`.
5. **Junk values.**  `Ent`, `LS`: existing hazards (`LogSobolevIneq` docstring); `LS` is quantified over `𝒜₀` (bounded), `Ent(f²)` genuine.
   `n.toReal` is used only after `n ≠ ⊤`; `(n⁻¹).toReal = (n.toReal)⁻¹` (`ENNReal.toReal_inv`).  `ρ` may be of any sign in Part A;
   `ρ > 0` only used for `e(s) → m log m` (Poincaré/spectral gap, as in the `n = ∞` proof) and `0 < κ`.
6. **a.e. vs everywhere.**  Same convention as the library: identities of functions in `𝒜` are a.e. (`L_congr_A` is used wherever `L` is applied
   to an a.e. representative; `Pt` is a chosen representative, `L`, `Γ` are a.e. class invariant).
7. **Is the hypothesis `he : e^{g/2} ∈ 𝒜₀` (Part A2) too strong?**  On non-compact triples it typically FAILS (`e^{g/2} ∉ C_c^∞`), so A2 is
   effectively a compact-triple statement; it is NOT used for the general conditional theorem (which uses `ext`).  It encodes exactly the
   book's use of Prop. 3.3.17 for `e^{ag}` (`∫Γ₂(f) = ∫(Lf)²`); stated honestly as a hypothesis, not hidden.
8. **Does `ext` smuggle in the conclusion?**  `ext` is (5.7.12) for `f ∈ 𝒜` in log-cutoff form (`∫ fΓ₂(log f) ≥ κ ∫ fΓ(log f)`), the book's
   claim p. 272.  The rest (Gronwall, limit, `φ = f²`) is proved.  It is a genuine extra assumption for non-compact triples, flagged as such.
9. **Deviation from the book, stated precisely:** (i) the book's last step "extends to `f ∈ 𝒜`" is a hypothesis (`ext`), not derived (needs
   Props 3.3.16 (iv)-(viii)/3.3.17: open, GAPS G5); (ii) the book states (5.7.5) as a criterion (Prop 5.7.3) and uses it for `P_t f`; the
   library's proof of Prop 5.7.1 (entropy interpolation) is reused with `ρ` replaced by `κ` in `I' ≤ -2κ I`, which is the same
   argument (p. 269: `Φ'' ≥ -(2/C)Φ'`); (iii) `e^{ag}` computations use `a = 3/(2(n+2))` and `a = 1/2` exactly as the book.
10. **Optimality** (book p. 272) and `n = 1` are not formalized.

## Attack surface for the independent auditor (most likely vacuous / misformalized)
* `FullTriple.FiniteDimInterpolation.ext`: premises (bounds `B`, integrability) correct in form?  Is `Cut`-cutoff form equivalent to `f Γ₂(log f)`?
* `FullTriple.FiniteDimInterpolation.bdd`: quantification over `entG` (chosen representative).
* `integral_exp_Γ₂_ge`: hypothesis `he`; coefficient `(4m-1)/(4(m+2)²)` vs (5.7.11); `ρ m/(m-1)` vs (5.7.12).
* `Γ₂_exp`: vs (5.7.6) (`2a`, `a²` factors); uses `Γ₂` of the library (`Γ₂(f) = ½(LΓ(f) - 2Γ(f,Lf))`).
* `dimLSConst` / `LS` convention (`Ent(f²) ≤ 2C ℰ(f)`), `logSobolev_of_CD_dim` conclusion `LS (dimLSConst ρ n) 0` on `𝒜₀`.
* `sphere_LS_dim : LS (1/3) 0`: on the ZONAL `S³` quotient interval only (existing limitation of the sphere instance).
