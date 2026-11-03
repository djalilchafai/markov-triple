# AUDIT R16 REG (self-attack, Armstrong step b)

Scope: `GibbsRd/RegReduction.lean`. Candid summary: `WeakHypo`/`F8` for `EllData d` are NOT proved unconditionally for
`d ≥ 1`; they are reduced to the single Prop `EllReg` (proved for `d = 0`).

1. **Is `EllReg` vacuous or false?**  Vacuity: hypotheses are satisfiable (e.g. all `x_k = 0`), conclusion non-trivial for
   `d ≥ 1`. Falsity: classically true (`(1−L)x_k = x_{k+1}` weak, `x_n ∈ L²_loc` ⇒ `x_k ∈ H^{2(n−k)}_loc` by interior regularity
   with smooth coefficients, `L` locally uniformly elliptic since `a` is continuous positive definite; Sobolev gives `C^m` for
   `2n > m + d/2`). `MemLp 2 μ` ⇒ `L²_loc(dx)` since `w` is continuous positive (locally bounded below).
2. **Representatives vs a.e.**  `x 0 =ᵐ[μ] g`; `μ ~ Lebesgue` (`w>0`), `IsOpenPosMeasure`, so continuous representatives are unique
   (`eq_of_ae_μ`); this is used to glue `C^m` representatives into a `C^∞` one (`smooth_rep_of_forall`).
3. **Uniform ellipticity / unbounded coefficients.**  The theorem is local; only local ellipticity is used classically.
   `a_bdd` and integrability of `w` are not needed for regularity (they matter for completeness, elsewhere).
4. **d = 0.**  `ℝ^0` is a point; `EllReg` is trivial (every function is constant). So `weakHypo_dim_zero`, `f8_dim_zero` are true
   theorems of no analytic content.
5. **How F8 uses the Friedrichs identity.**  `t>0`: `P_t = R^n ψ_{t,n}(R)` (`cfcSemigroup_eq_pow_mul`); `Φ = ψ(R) f ∈ L²`;
   chain `x_k = R^{n−k}Φ` satisfies `∫ (R v) L a = ∫ (R v − v) a` (`resolvent_weak`, general). Natural subtraction: for `k<n`,
   `n−k = (n−k−1)+1`, checked. The `∃ n` precedes `x` and depends only on `m`, the right quantifier order for the classical theorem.
6. **WeakHypo chain.**  `x_k = (1−λ)^k u` satisfies the chain equation (`(1−λ)^k λ ∫ u a` on both sides), checked in Lean.
7. **Strength of `EllReg`.**  Equivalent in content to the textbook theorem; `n` cannot be independent of `m` (false).
8. No definition of `WeakHypo`/`F8` changed; no hypothesis added to them; the theorems take `EllReg` explicitly.

## Attack surface (for the hostile auditor)
* A1. Is `EllReg`'s global `MemLp 2 E.μ` hypothesis too weak to make the classical theorem true? (Should be fine: regularity is local.)
* A2. Quantifier order `∀ m, ∃ n, ∀ x` correct (n depends on `m` and `E` only)?
* A3. `E.diff.μ` vs `E.μ`, `E.diff.L = E.L`, `E.diff.A₀ = A₀ d` are definitional, used silently in `weakHypo_of_reg`, `f8_of_reg`.
* A4. The missing piece is `EllReg` for `d ≥ 1`: every downstream claim for `EllData` is still conditional.
* A5. The `d = 0` theorems have no analytic content.
