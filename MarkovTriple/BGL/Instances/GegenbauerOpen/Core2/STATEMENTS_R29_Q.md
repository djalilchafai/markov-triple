# Round 29, Stream Q (`Core2` on the Gegenbauer open-interval family): frozen target statements

Written BEFORE any proof.  Namespace `MarkovTriple.BGL.Instances.GegenbauerOpen.Core2Q`; files `Instances/GegenbauerOpen/Core2/*`.

## SCOPE (honest, decided before proving)
The whole `FullTriple` layer for the Gegenbauer open interval (`Basic`, `Diffusion`, `Full/*`, `ESA/*`, `Riemannian/R24/Go*`, about 4000 lines) is
hard-wired to `lambda = 3/2` (`goμ = (3/4)(1-x²)dx`, `goL = (1-x²)f'' - 4x f'`, constants `3/4`, `4x`, explicit primitives, the R24 series `aa_n`).
It is not parametric in `lambda`.  A `FullTriple` (hence `Core2`) for another `lambda` needs a full re-development (PreFull, RegLocal, Sem,
Weyl/Regularity/Prim for ESA, and for `lambda >= 7/2` a fourth-order regularity/Weyl argument).  This stream does NOT attempt that.
Deliverable (Q1): a parametric, `FullTriple`-free formalisation of the exact Frobenius/`L²` exponent count behind the R26-I heuristic.
The `Core2` threshold itself stays an UNPROVED, labelled heuristic.

## Q1 (parametric in real `lam`)
```
noncomputable def gL (lam : ℝ) (f : ℝ → ℝ) : ℝ → ℝ := fun x => (1 - x^2) * deriv (deriv f) x - (2*lam+1) * x * deriv f x
noncomputable def gρ (lam : ℝ) (x : ℝ) : ℝ := (1 - x^2) ^ (lam - 1/2)

theorem gL_three_halves (f : ℝ → ℝ) : gL (3/2) f = goL f
theorem gL_pow (lam r : ℝ) {x : ℝ} (hx : x ∈ Ioo (-1) 1) :
    gL lam (fun y => (1-y)^r) x = r * (1-x)^(r-1) * ((r-1)*(1+x) + (2*lam+1)*x)
theorem gL_pow_indicial (lam r : ℝ) : (r-1)*(1+1) + (2*lam+1)*1 = 2*r + 2*lam - 1        -- bracket at x = 1; indicial polynomial r(2r+2lam-1)
theorem pow_sq_integrable_iff (lam r : ℝ) :
    IntegrableOn (fun x => ((1-x)^r)^2 * gρ lam x) (Ioo 0 1) ↔ 0 < 2*r + lam + 1/2
theorem exponent_regular_L2 {lam : ℝ} (h : -1/2 < lam) : 0 < 2*0 + lam + 1/2 ∧ 0 < 2*1 + lam + 1/2
theorem exponent_half_sub_lam_L2_iff (lam : ℝ) : 0 < 2*(1/2-lam) + lam + 1/2 ↔ lam < 3/2
theorem exponent_three_half_sub_lam_L2_iff (lam : ℝ) : 0 < 2*(3/2-lam) + lam + 1/2 ↔ lam < 7/2
```
Meaning (formal part only): `L_lam` maps `t^r` (`t = 1-x`) to `r(2r+2lam-1) t^(r-1)` + higher order, so the Frobenius exponents of
`(1-L)² u = 0` at `x = 1` are `0, 1` (analytic) and `1/2 - lam, 3/2 - lam` (the shifted roots of the indicial polynomial); the number of
exponents whose `t^r` is `L²(ρ_lam)` near the endpoint is 4 for `lam < 3/2`, 3 for `3/2 <= lam < 7/2`, 2 for `lam >= 7/2`.  Only the action of one
factor `L` and the `L²` criterion are claimed formally, NOT the Frobenius theory of the fourth-order equation.

## NOT claimed (remains the R26-I heuristic, unproved)
`Core2` fails for `3/2 <= lam < 7/2` and holds for `lam >= 7/2`.  No `FullTriple` for `lam ≠ 3/2` is constructed; no deficiency pair for
`lam ≠ 3/2`; nothing for `hypRiem` or abstract complete triples.

## Status (after proof)
All seven Q1 theorems delivered in `Core2/Frobenius.lean` with the frozen names and statements (no deviation; `Core2Q.gL`, `Core2Q.gρ`),
axioms `propext, Classical.choice, Quot.sound` only (`Core2/AxiomCheckR29Q.lean`), no `sorry`.  The positive (`lam >= 7/2`) and negative
(`3/2 <= lam < 7/2`) halves of the `Core2` threshold were NOT proved: see GAPS "Round 29, Stream Q".
