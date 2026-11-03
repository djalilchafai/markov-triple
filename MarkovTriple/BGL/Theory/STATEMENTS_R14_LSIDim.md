# R14: target statements, BGL Thm 5.7.4 for `n < ∞` (written BEFORE the proofs)

Source: Bakry-Gentil-Ledoux, Sect. 5.7, pp. 268-272: Prop. 5.7.1, Prop. 5.7.3 (5.7.5), Thm 5.7.4 and its
proof ((5.7.6)-(5.7.12)); p. 269-270 (use of (5.7.5) for `P_t f`, "bounded together with Γ(P_t f), L P_t f").
Changes to these statements only via a logged erratum in `ERRATA.md`.

Conventions (as in `Theory/Poincare.lean`, `Frozen/CD.lean`): `n : ℝ≥0∞`, `1 < n`, `n ≠ ⊤` (the book: `n > 1`, finite;
`n = ∞` is Prop 5.7.1 = `logSobolev_of_CD_infty`), `n⁻¹.toReal = 1/n`.  `LS C 0` is `DiffusionTriple.LS C 0`:
`Ent(f²) ≤ 2 C ℰ(f)` for `f ∈ 𝒜₀`, `μ` probability (BGL Def 5.1.1).  Book constant `C = (n-1)/(ρ n) = (1 - n⁻¹)/ρ`.

## Part A (unconditional on any named structure) — `Theory/LogSobolevDimChain.lean`

A1. `FullTriple.Γ₂_exp` — BGL (5.7.6) (via the chain rule (3.3.2) for `Γ₂`).  `T : FullTriple`, `g ∈ T.A`, `a : ℝ`:
`Γ₂(e^{ag}) =ᵐ a² e^{2ag} (Γ₂(g) + a Γ(g, Γ(g)) + a² Γ(g)²)`  (`Γ = ΓA`).

A2. `FullTriple.integral_exp_Γ₂_ge` — BGL (5.7.11) and (5.7.12).  `T : FullTriple`, `CD ρ n`, `1 < n < ∞` (`m := n.toReal`),
`g ∈ T.A₀`, and `he : e^{g/2} ∈ T.A₀` (hypothesis: the book's "Prop. 3.3.17 applies to `e^{ag}`", the integrated identity
`∫Γ₂(f) = ∫(Lf)²` for `f = e^{g/2}`; automatic on compact triples):
`ρ m/(m-1) ∫ e^g Γ(g) + (4m-1)/(4(m+2)²) ∫ e^g Γ(g)² ≤ ∫ e^g Γ₂(g)`; in particular `ρ m/(m-1) ∫ e^g Γ(g) ≤ ∫ e^g Γ₂(g)`.
No sign condition on `ρ`.

## Part B (Thm 5.7.4, conditional) — `Theory/LogSobolevDim.lean`

B0. `dimLSConst ρ n := (1 - (n⁻¹).toReal)/ρ`.  Checks: `dimLSConst ρ ⊤ = 1/ρ`; `dimLSConst ρ n < 1/ρ` for `ρ > 0`, `n < ∞`;
`dimLSConst ρ n → 1/ρ` as `n → ∞`.

B1. `structure FullTriple.FiniteDimInterpolation T κ : Prop` — the named analytic input (never an axiom), exactly the
two facts the book uses without proof (p. 270 and p. 272):
 * `bdd`: for `φ ∈ 𝒜₀`, `φ ≥ 0`, `ε > 0`, `s > 0`: `g_s = ε + P_s φ` has `Γ(g_s)` and `L g_s` bounded a.e. (book p. 270: "for t > 0, `P_t f`
   is in `𝒜` and moreover bounded together with Γ(P_t f) and L P_t f");
 * `ext`: (5.7.12) extended (book p. 272, "by Prop. 3.3.6 and Lemma 3.3.16 ... (5.7.12) extends to functions `f ∈ 𝒜` which are bounded,
   together with Γ(f) and Lf"), in the `log`-cutoff form used by the semigroup argument: for `f ∈ 𝒜` with `ε ≤ f ≤ ε+M`, `Γ(f)`, `Lf`
   bounded a.e., a cutoff `Λ` of `log` on `[ε,ε+M]` (`BE.Cut`), and integrability of `f Γ₂(Λ∘f)`, `f Γ(Λ∘f)`:
   `κ ∫ f Γ(Λ∘f) ≤ ∫ f Γ₂(Λ∘f)`.

B2. `FullTriple.ent_le_fisher_dim` — Prop. 5.7.1's proof with `ρ` replaced by `κ` in the decay of `I`: `μ` probability,
`EntropyInterpolation`, `FiniteDimInterpolation T κ`, `0 < ρ`, `CD ρ n` (used only for `e(s) → m log m`, Poincaré), `0 < κ`:
`Ent(ε+φ) ≤ (∫Γ(φ)/(ε+φ))/(2κ)`.

B3. `FullTriple.logSobolev_of_CD_dim` — **BGL Thm 5.7.4**: `μ` probability, `EntropyInterpolation`,
`FiniteDimInterpolation T (ρ m/(m-1))`, `ρ > 0`, `1 < n < ∞`, `CD ρ n` ⇒ `T.LS (dimLSConst ρ n) 0`  (`LS((n-1)/(ρ n))`).

B4. `CompactTriple.finiteDimInterpolation`: for every `CompactTriple`, `CD ρ n`, `1 < n < ∞`: `FiniteDimInterpolation (ρ m/(m-1))`
(PROVED; Part A1/A2 with `𝒜 = 𝒜₀`).  `compact_logSobolev_dim`: `CompactTriple`, `ρ > 0`, `CD ρ n`, `1<n<∞` ⇒ `LS((1-n⁻¹)/ρ) 0`,
unconditional (uses `compact_entropyInterpolation`).

## Part C (instance) — `Instances/Sphere/LogSobolevDim.lean`

C1. `sphere_LS_dim : sCompact.toDiffusionTriple.LS (1/3) 0` (zonal `S³`, `CD(2,3)`: `(3-1)/(2·3) = 1/3`), strictly better than
`sphere_LS : LS (1/2) 0`; `sphere_LS_dim_lt : 1/3 < 1/2`.

## Not covered (stated exactly)
* General (non-compact) `FullTriple` instances: need `EntropyInterpolation` (G3) and `FiniteDimInterpolation` (book p. 270/272, via
  Prop. 3.3.6/Lemma 3.3.16/Prop 3.3.17, not in the library).
* `n = 1` (torus, `ρ = 0`; book p. 272 handles it separately via (5.7.13)): not formalized (`ρ = 0`, no LS constant).
* Optimality of `(n-1)/(ρ n)` (book remarks): not formalized.
* OU, circle: finite-`n` `CD(ρ,n)` with `ρ>0` does not hold (OU: only `n = ∞`; circle `ρ = 0`), so no new instance there.
