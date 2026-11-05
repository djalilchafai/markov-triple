# Round 32, Stream Z (`Core2L` on the Gegenbauer open-interval family, negative half at `lam = 5/2`): frozen target statements

Written BEFORE any proof.  Namespace `MarkovTriple.BGL.Instances.GegenbauerOpen.Core2Z`; files `Instances/GegenbauerOpen/Core2/Z/*`
(`Series.lean`, `Pair.lean`, `Main.lean`, `AxiomCheckR32Z.lean`).  Reuses `Core2W.muL`, `Core2W.Core2L`, `Core2W.not_core2L_of_pair`
(R31-W), `Core2Q.gL`, `Core2Q.gρ`, `goA₀`, `GoSeries`.

## CHOICE (decided before proving)
Option (i) of the brief: `lam = 5/2`, negative half.  Options (ii) (`lam ≥ 7/2`, positive half) and (iii) (hyperbolic plane) are NOT attempted.

## SCOPE (same caveat as R31-W)
`Core2L lam` is the FullTriple-free literal transcription of `FullTriple.Core2` for `L_lam = gL lam` on `C_c^∞(-1,1)` in `L²(muL lam)`.
No `FullTriple` for `lam = 5/2` exists in the library; nothing here asserts `F1–F10` or an ESA statement for `lam = 5/2`.

## Z1 (the pair exists for `lam = 5/2`)
```lean
theorem deficiency_pair_five_halves : ∃ w h : ℝ → ℝ,
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w (Ioo (-1 : ℝ) 1) ∧
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h (Ioo (-1 : ℝ) 1) ∧
    (∀ x ∈ Ioo (-1 : ℝ) 1, Core2Q.gL (5 / 2) w x = w x) ∧
    MemLp h 2 (Core2W.muL (5 / 2)) ∧ MemLp (fun x => w x - Core2Q.gL (5 / 2) h x) 2 (Core2W.muL (5 / 2)) ∧
      ∃ x ∈ Ioo (-1 : ℝ) 1, w x ≠ 0
```
Mathematics: indicial exponents at `x = 1` are `0` and `-2` (they differ by an integer, so the second Frobenius solution carries a
logarithm: `t² log t` term).  `w = (1-x²)^(-2) A`, `A = Σ c_n xⁿ`, `(1-x²)A'' + 2xA' + 3A = 0`, `c_0 = 1, c_1 = 0`,
`c_{n+2} = c_n (n²-3n-3)/((n+1)(n+2))`, `|c_n| ≲ n^{-5/2}` (actually `~ n^{-3}`; the logarithm is the reason `A` is only
Lipschitz, not smooth, at `±1`), so `|A(x) - A(1)| ≤ C (1-x²)`.  `h = α (1-x²)^(-1)`, `α = -A(1)/4`,
`L_{5/2} (s^r) = s^r (-2r + 4r(r+2) x²/s)`, so `L h = α s^(-2)(2 - 6x²)` and
`w - L h = s^(-2)(A - A(1)) - 6α s^(-1)`, weighted bound `(w - L h)² ρ_{5/2} ≤ (C + 3|A(1)|/2)²` with `ρ_{5/2} = s²`.

## Z2 (main)
```lean
theorem not_core2L_five_halves : ¬ Core2W.Core2L (5 / 2)
```

## NOT claimed
`Core2L lam` for other `lam` (heuristic: `Core2L lam` fails for `3/2 < lam < 7/2` at least; only `lam = 2, 5/2` proved here and in R31-W);
no `FullTriple` for `lam = 5/2`; nothing for `lam ≥ 7/2` or for the hyperbolic plane.
