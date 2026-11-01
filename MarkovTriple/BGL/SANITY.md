# Non-vacuity of the BGL surface (`MarkovTriple/BGL/Sanity/`)

All items below are fully proved (only `propext`, `Classical.choice`, `Quot.sound`, see `AxiomCheck.lean`).

| Instance | File | What it shows |
|---|---|---|
| `trivialDiffusion μ` (any finite discrete space, `μ` probability, `L = Γ = 0`, `𝒜₀ = ⊤`) | `Sanity/Trivial.lean` | every field of `DiffusionTriple` is satisfiable, including: `bounded` (finite range), `memLp`, `dense`, `comp_mem`, `exhaustion` (`u_n = 1`, increasing a.e., tends to `1`), `finite_prob`, D8. |
| `trivialDiffusion_semigroup_cls` | same | the Friedrichs semigroup `DiffusionTriple.semigroup` of the trivial triple is `P_t = id` on classes of test functions (via `Hilbert.FormData.semigroup_eigen`). |
| `trivialCompact : CompactTriple Unit` (one-point space, Dirac measure) | same | `StandardTriple` (S10 ergodic, S11 conservative: `P_t u_n = u_n → 1`), `FullTriple` (F1–F10 with `𝒜 = 𝒜₀ = ⊤`), `CompactTriple`. F2 uses the test function `1`; F8 uses `P_t = id`; F10 uses `generator_cls` (`𝒜₀ ⊂ 𝒟(L)`, `L` extends `L|𝒜₀`). |
| `trivialCompact_CD ρ (1 ≤ n)`, `trivialCompact_not_CD_zero` | same | `CD(ρ,n)` for all `n ∈ [1,∞]`, fails for `n < 1`. |
| `trivialCompact_PI`, `trivialCompact_LS` | same | `P(1)` and `LS(1,0)` hold (generic definitions). |
| `circleDiffusion : DiffusionTriple 𝕋` | `Sanity/Circle.lean` | D1–D8 data for the circle: Haar probability measure, `𝒜₀ = C^∞(𝕋)`, `L f = f''`, `Γ(f,g) = f'g'` (`Γ ≠ 0`); boundedness by compactness, exhaustion `u_n = 1`, `∫ f'' = 0`, a.e. diffusion property from the old pointwise proof. S10, S11, F1–F10 for the circle are NOT proved here (later stage). |

Why the one-point space for the standard/full/compact trivial triple: with `L = 0` on a space with two
points of positive mass, `L u = 0` for every `u`, so S10 (ergodicity) fails.  Finite spaces with `L ≠ 0`
are excluded by the diffusion property.  The trivial compact triple does not test `Γ ≠ 0`; the circle
`DiffusionTriple` does (D1–D8 only).

Consistency theorems proved on the generic structures (also evidence against vacuity):
`DiffusionTriple.L_mul_ae` (BGL (3.1.6) polarised) and `ΓA_ae_eq` (the formula-defined `Γ` of F4 agrees
a.e. with the field `Γ` on `𝒜₀`), `FullTriple.integrable_F7`.
