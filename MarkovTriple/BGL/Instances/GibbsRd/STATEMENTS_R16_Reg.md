# STATEMENTS R16 (Armstrong method): regularity for `EllData d` — written BEFORE the proofs

Goal ("full fix"): prove `EllData.WeakHypo` (BGL Def. 3.3.8, `𝒜 = C^∞(ℝ^d)`, all `λ ∈ ℝ`) and `EllData.F8`
(Def. 3.3.1 (viii)) for all `d`, definitions UNCHANGED (`GibbsRd/EllPI.lean`).

## Survey of Mathlib (what exists / does not)
* Exists: `ContDiffBump`, convolution `MeasureTheory.convolution` with `HasCompactSupport.contDiff_convolution_*`,
  `Lp.dense_hasCompactSupport_contDiff`, `integral_fderiv_*` IBP, Fourier/Plancherel on `Lp`, `Continuous.ae_eq_iff_eq`.
* Does NOT exist: Sobolev spaces `H^k_loc`, weak derivatives as a theory, difference-quotient (Nirenberg) lemma,
  Caccioppoli/Gårding inequality, Sobolev/Morrey embedding, interior elliptic regularity (any dimension).
* Consequence: interior elliptic regularity with variable smooth coefficients in `ℝ^d`, `d ≥ 2`, is a multi-thousand-line
  development (Sobolev scale + Friedrichs mollifier commutator + difference quotients + Sobolev embedding).  NOT delivered
  in this round (see "Status").  1-D is done (`Gibbs/Reg*.lean`, du Bois-Reymond).

## Classical theorems (to be formalised)
* (E) Interior elliptic regularity (Evans §6.3 Thm 2–3 / Gilbarg–Trudinger Thm 8.8, 8.10, Cor 8.11): if `u ∈ L²_loc`
  is a weak solution of `div(w a ∇u) = w h`, `h ∈ H^k_loc`, coefficients smooth, locally uniformly elliptic, then `u ∈ H^{k+2}_loc`.
* (Sob) `H^s_loc ⊂ C^m` for `s > m + d/2` (Morrey/Sobolev).
* (S) Semigroup smoothing `P_t = R^n ψ_{t,n}(R)` (`Hilbert.cfcSemigroup_eq_pow_mul`), `R = (1−L)⁻¹` Friedrichs resolvent,
  weak resolvent identity `resolvent_weak` (general for `DiffusionTriple`).

## Statements (namespace `MarkovTriple.BGL.Instances.GibbsRd`, `EllData`; file `RegReduction.lean`)

Notation: `μ = E.μ = Z⁻¹ w dx`, `L = E.L`, `𝒜₀ = A₀ d`.

R0 (the single named analytic input, **Prop, not axiom**, `EllData.EllReg`).  A finite resolvent chain of `L²(μ)` functions
`x₀,…,xₙ` with `∫ x_k · L a dμ = ∫ (x_k − x_{k+1}) · a dμ` (`a ∈ 𝒜₀`, `k < n`) has a `C^m` representative of `x₀` when
`n` is large enough:
`EllReg E := ∀ m : ℕ, ∃ n : ℕ, ∀ x : ℕ → (Rd d → ℝ), (∀ k ≤ n, MemLp (x k) 2 μ) →
  (∀ k < n, ∀ a ∈ A₀ d, ∫ x k · L a dμ = ∫ (x k − x (k+1)) · a dμ) → ∃ g, ContDiff ℝ m g ∧ x 0 =ᵐ[μ] g`.
(Classical truth: `(1−L)x_k = x_{k+1}`, so `x_n ∈ L²_loc`, `x_k ∈ H^{2(n−k)}_loc` by (E), and (Sob) with `2n > m + d/2`.)

R1 `EllData.weakHypo_of_reg : E.EllReg → E.WeakHypo`   (chain `x_k = (1−λ)^k u`).
R2 `EllData.f8_of_reg : E.EllReg → E.F8`   (`t = 0` trivial; `t > 0`: chain `x_k = R^{n−k} ψ_{t,n}(R) f`, `x₀ = P_t f`).
R3 `EllData.ellReg_of_dim_zero (d = 0)` : `EllReg` holds unconditionally for `d = 0` (`ℝ^0` is a point).
R4 (not claimed unless proved): `EllData.ellReg : E.EllReg` for all `d`; hence `weakHypo`, `f8` unconditional.

## Status at end of round
R1, R2, R3 as Lean theorems; R0/R4 OPEN for `d ≥ 1` (the exact missing statement is R0 itself).  `WeakHypo`/`F8`
definitions untouched; no hypothesis added to them (the reduction theorems take `EllReg` as an explicit argument).
