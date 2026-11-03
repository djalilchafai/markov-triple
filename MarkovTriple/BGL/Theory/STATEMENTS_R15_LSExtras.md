# R15: target statements, the two remainders of BGL Thm 5.7.4 (written BEFORE the proofs)

Source: Bakry-Gentil-Ledoux, p. 238-240 (Prop. 5.1.3, first assertion and its proof), p. 270-272 (Thm 5.7.4, proof,
(5.7.6)-(5.7.12)), p. 272-273 (the paragraph after the proof: "the lower bound `ρn/(n-1)` ... being optimal", the case `n = 1`,
(5.7.13), "The constant is optimal since it is already optimal for the Poincare inequality"), p. 214 (Prop. 4.8.3 dual form).
Changes to these statements only via a logged erratum in `ERRATA.md`.  Conventions as in `STATEMENTS_R14_LSIDim.md`:
`LS C 0` = `DiffusionTriple.LS C 0` (`Ent(f^2) <= 2 C E(f)` on `A0`), `PI C` = `DiffusionTriple.PI C` (`Var f <= C E(f)` on `A0`),
`CD ρ n` = `FullTriple.CD`.

## Part 2 (optimality) -- `Theory/LSToPI.lean`, `Instances/Sphere/LSOptimal.lean`

L1. `DiffusionTriple.PI_of_LS` -- **BGL Prop. 5.1.3, first assertion** (p. 238): `T : DiffusionTriple`, `h1 : (fun _ => 1) ∈ T.A₀`
(the unit lies in the test algebra), `T.LS C 0` ⟹ `T.PI C`.  Proof: the book's: `f = 1 + ε g`, `∫ g = 0`, Taylor expansion of
`Ent(f^2) = 2 ε² ∫ g² + o(ε²)`, `E(f) = ε² E(g)`, and `ε → 0`; general `g` by `g - ∫ g`.
*Hypothesis `h1`*: the book works on `D(E)`, which contains the constants for a probability measure; the library's `LS`/`PI` live on the
non-unital `A0`, so `1 ∈ A0` is an explicit assumption (true for every `CompactTriple`: `A = A0` unital).  No claim for non-unital
`A0` (e.g. Lebesgue/OU Hermite `A0`): there the implication needs the extension to `D(E)` and is NOT formalized.
L2. `CompactTriple.PI_of_LS`: `C : CompactTriple E`, `C.LS c 0` ⟹ `C.PI c` (unconditional, uses L1 with `h1` from `A = A0`).
L3. `DiffusionTriple.not_PI_of_eigen` (the "optimality" principle in the book's wording "Poincare constant already optimal"):
`T` probability, `f ∈ A0`, `λ > 0`, `L f = -λ f` a.e., `∫ f² = 1` ⟹ `¬ T.PI c` for every `c < 1/λ`.
L4. `Instances/Sphere/LSOptimal.lean`: `sphere_not_PI_lt : ∀ c < 1/3, ¬ sCompact.toDiffusionTriple.PI c`;
`sphere_not_LS_lt : ∀ c < 1/3, ¬ sCompact.toDiffusionTriple.LS c 0`; `sphere_LS_dim_optimal`: `LS (1/3) 0` and no smaller constant,
i.e. the constant `(n-1)/(ρ n) = 1/3` of Thm 5.7.4 for `S³` (CD(2,3)) is optimal.  (Here `LS (1/3) 0` is `sphere_LS_dim`.)
Optimality is for the *class* `A0` of the triple (hence also for `D(E)`: `A0 ⊂ D(E)`; the larger class can only make LS stronger).

## Part 1 (case `n = 1`) -- `Theory/LogSobolevDimOne.lean`

Book text (p. 272-273): CD(0,1), Poincare `P(1)` (torus), dual form `∫Γ₂(f) ≥ ∫Γ(f)`; applied to `f = e^{g/2}` gives (5.7.13);
`CD(0,1)` with (5.7.9) at `a = 1/3`, compared with (5.7.8) at `a = 1/2`: `∫ e^g Γ(g,Γ(g)) + (2/3) ∫ e^g Γ(g)² ≤ 0`; hence
`∫ e^g Γ₂(g) ≥ ∫ e^g Γ(g)` = (5.7.12) "with the convention `ρn/(n-1) = 1`"; "the log-Sobolev inequality with constant 1 (equal to the
Poincare constant) follows similarly".

The book states `P(1)` for the torus of its normalisation.  The argument is scale-free: we formalize it with a general Poincare constant `c > 0`
(the book: `c = 1`), the circle of the library having `c = 1/(4π²)`.

N1. `FullTriple.integral_Γ_le_of_PI` -- the dual form of Prop. 4.8.3 (p. 214) restricted to `A0`:
`T : FullTriple`, `T.PI c`, `f ∈ T.A0` ⟹ `∫ ΓA f f ≤ c ∫ Γ₂ f f`.  (Proof: `∫Γ₂(f) = ∫(Lf)²` (`integral_Γ₂`, BGL (3.3.8)),
`E(f) = -∫ f L f = -∫ (f - m) L f`, Cauchy-Schwarz/Young, `Var f ≤ c E(f)`.)
N2. `FullTriple.integral_exp_Γ₂_ge_one` -- (5.7.13) + the `a=1/3` step: `T : FullTriple`, `T.CD 0 1`, `T.PI c`, `g ∈ T.A0`,
`he : e^{g/2} ∈ T.A0` ⟹ (i) `∫ e^g Γ(g,Γ(g)) + (2/3) ∫ e^g Γ(g)² ≤ 0`;  (ii) `(1/c) ∫ e^g Γ(g) ≤ ∫ e^g Γ₂(g)`
(book (5.7.12) with `ρn/(n-1) := 1` for `c = 1`).
N3. `FullTriple.tendsto_entE_of_PI`, `ent_le_fisher_of_PI`, `logSobolev_of_PI_finiteDim` -- Prop. 5.7.1's argument with the Poincare
inequality as input instead of `CD(ρ,·), ρ>0` (the limit `e(s) → m log m` only needs `P(c)`; Prop. 5.7.1 p. 266-268 / Thm 5.7.4 p. 270):
`T.EntropyInterpolation`, `T.PI c₀`, `κ > 0`, `T.FiniteDimInterpolation κ` ⟹ `T.LS (1/κ) 0`.
N4. `CompactTriple.finiteDimInterpolation_one`: `C : CompactTriple`, `CD 0 1`, `PI c` ⟹ `FiniteDimInterpolation (1/c)`.
N5. `CompactTriple.compact_logSobolev_one` -- **the book's `n = 1` statement (p. 273)**: `CompactTriple`, `CD 0 1`, `PI c` ⟹ `LS c 0`
(`c = 1`: "log-Sobolev with constant 1").  Combined with L2: for compact triples with `CD(0,1)`: `LS c 0 ↔ PI c`
(`compact_LS_iff_PI_of_CD_zero_one`).
N6. `Instances/Circle/LSOne.lean` (only if circle `PI` is obtained): `circle_PI : PI (1/(4π²))`, `circle_LS : LS (1/(4π²)) 0`,
`circle_LS_optimal`.  If not obtained it is reported as open (the circle's Poincare inequality is not in the repo).

## Explicitly NOT claimed
* No `dimLSConst ρ 1` (formula `(1 - n⁻¹)/ρ` at `ρ = 0, n = 1` is `0/0 = 0` junk; the n=1 constant is the Poincare constant `c`).
* `FiniteDimInterpolation` for non-compact `FullTriple`s; the `n=1` case for non-compact triples (only the named hypotheses).
* `LS ⟹ PI` for non-unital `A0` (see L1).
* Optimality for other `n`, other `ρ` (only `S³`, `n = 3`, the instance of the book's sentence about spheres; the book's general claim for
  `Sⁿ`/Jacobi is not available since only `S³` is in the repo).

## Addenda recorded during the proofs (no statement above was weakened or changed)
* L3 also has the form `DiffusionTriple.not_PI_of_eigen_pos` (hypothesis `0 < ∫ f²` instead of `∫ f² = 1`; `not_PI_of_eigen` is the corollary
  stated above).  Used for the circle (no normalisation computed).
* N6 was obtained: `Instances/Circle/Poincare.lean` (`circle_var_le`: Wirtinger via Parseval, `Var f ≤ (1/(4π²)) ∫ (f')²`), and
  `Instances/Circle/LSOne.lean` (`circle_PI`, `circle_LS`, `circle_not_PI_lt`, `circle_not_LS_lt`, `circle_LS_optimal`; library circle is `ℝ/ℤ`, constant `1/(4π²)`).
* Auxiliary lemmas of L1: `log_sq_lower` (`(1+t)² log (1+t)² ≥ 2t + 3t² - 8|t|³`, `|t| ≤ 1/2`), `DiffusionTriple.Γ_one_left`
  (`Γ(1,h) = 0`), `Γ_add_const_self`, `Γ_smul_self`, `sq_integral_le_of_LS` (core, `∫ g = 0`).
* N3 reproduces (copies) the proofs of `tendsto_entE`, `ent_le_fisher_dim`, `ent_sq_add_le_dim`, `logSobolev_of_finiteDim` with `P(c)` in place of
  `CD(ρ,n), ρ > 0`: the existing files are untouched (no new-files-only violation), at the cost of duplicated proof text.
