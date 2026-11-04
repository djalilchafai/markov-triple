# Round 23, Stream R (`(ℝ^d, Lebesgue)`, d ≥ 2): statements fixed BEFORE the proofs

Namespace `MarkovTriple.BGL.LebesgueRd`; files `Basic.lean` (S1), `Gamma2.lean` (S1', pointwise CD), `AxiomCheck.lean`.
Method: statements first; deviations are logged in `## Status` and proposed as `ERRATA.md` rows `R23-R-*`.

## Route choice (line estimates, BEFORE coding)
* (b) tensorisation of `lebesgueFull`: needs a general product theorem for `DiffusionTriple`/`FullTriple` (form domains of tensor products,
  ESA of a sum of commuting ESA operators = Nelson-type theorem, S11/F8 for the product semigroup `P_t⊗P_t`): not in Mathlib, not in this repo;
  honest estimate 3000+ lines.  Rejected.
* (c) Fourier/Plancherel: Mathlib has the L² Fourier transform only on inner product spaces via `Lp`-extension; identifying `𝒟(L)` with
  `{(1+|ξ|²) û ∈ L²}`, `F8` regularity (`P_t f ∈ C^∞`) and `F10` need Sobolev + Schwartz-density arguments plus the link with the repo's
  Friedrichs-constructed `generator`; estimate 2500+ lines.
* (a) heat-kernel port of the 1-D files (`Lebesgue/{Heat,Identify,ODE,Cutoff,Core2*,Ergodic,Full*}.lean`, ≈2600 lines, 1-D specific: `deriv`, ODE in `x`):
  the port to `ℝ^d` is ≈ 3500 lines.
* S1 (DiffusionTriple, `Basic.lean`) is route independent, ≈ 450 lines; S1' (Γ₂, Bochner with constant 1/d and its sharpness) ≈ 250 lines.
  Plan: deliver S1 and S1' in this round, state S2–S4 precisely, do NOT claim them.

## Carrier: `Fin d → ℝ` with `volume`
`volume` on `Fin d → ℝ` is `Measure.pi (fun _ => volume)`, the d-dimensional Lebesgue (Haar) measure, and is the measure transported from
`EuclideanSpace ℝ (Fin d)` by `EuclideanSpace.volume_preserving_measurableEquiv`.  The operators `L = Σ ∂ᵢ²`, `Γ(f,g) = Σ ∂ᵢf ∂ᵢg` are written with
`fderiv ℝ f x (Pi.single i 1)`, independent of the norm (sup vs Euclidean), so the triple is the Euclidean one.  `Fin d → ℝ` is chosen because the
frozen files (`pderiv`, F3/F6 shapes) are stated for `Fin k → ℝ` and the 1-D proofs port verbatim.

## Definitions
```lean
abbrev Sm {d} (f : (Fin d → ℝ) → ℝ) : Prop := ContDiff ℝ (⊤ : ℕ∞) f
def A₀ (d : ℕ) : NonUnitalSubalgebra ℝ ((Fin d → ℝ) → ℝ)   -- C_c^∞(ℝ^d)
def A  (d : ℕ) : Subalgebra ℝ ((Fin d → ℝ) → ℝ)             -- C^∞(ℝ^d)
noncomputable def dd (i : Fin d) (f : (Fin d → ℝ) → ℝ) : (Fin d → ℝ) → ℝ := fun x => fderiv ℝ f x (Pi.single i 1)
noncomputable def Lf (f) : (Fin d → ℝ) → ℝ := fun x => ∑ i, dd i (dd i f) x
noncomputable def Gf (f g) : (Fin d → ℝ) → ℝ := fun x => ∑ i, dd i f x * dd i g x
```

## S1: DiffusionTriple (D1–D8) on ℝ^d (every d; the case d = 0 needs the finite-measure clause, so S1 is stated for `d ≥ 1`)
```lean
noncomputable def lebesgueRdDiffusion (d : ℕ) (hd : 1 ≤ d) : DiffusionTriple (Fin d → ℝ)
-- μ = volume, 𝒜₀ = C_c^∞, L = Lf, Γ = Gf
theorem lebesgueRd_L_eq / lebesgueRd_Γ_eq   -- identification of L, Γ (rfl)
```
Components: `ibp_Lf : Sm f → g ∈ A₀ → ∫ g * Lf f = -∫ Gf f g`, `diffusion_c` (chain rule for `Γ`), `dense_Lp`, exhaustion
`cut n x = smoothTransition (2 - (Σ xᵢ²)/(n+1)²)`.
(For `d = 0` the space is a point, μ a probability measure; not needed, excluded.)

## S1': Γ, Γ₂, pointwise Bochner (what `CD(0,n)` reduces to once a FullTriple exists)
```lean
theorem ΓA_eq_Gf  : Sm f → Sm g → (lebesgueRdDiffusion d hd).ΓA f g = Gf f g
theorem Γ₂_eq     : Sm f → (lebesgueRdDiffusion d hd).Γ₂ f f x = ∑ i, ∑ j, (dd i (dd j f) x)^2
theorem bochner_Rd : Sm f → (1/d) * (Lf f x)^2 ≤ (lebesgueRdDiffusion d hd).Γ₂ f f x          -- Cauchy–Schwarz
theorem bochner_Rd_sharp : n real, n < d → ¬ (∀ f, Sm f → ∀ x, (1/n) * (Lf f x)^2 ≤ Γ₂ f f x)   -- f = Σ xᵢ²/2: Γ₂ = d, (Lf)² = d²  (proved as the iff `bochner_Rd_iff`)
```
This is the pointwise (ρ,n)-inequality on `𝒜 = C^∞`: `CD(ρ,n)` for `ρ ≤ 0` iff `n ≥ d`, at the level of the diffusion triple's `Γ₂`.  It is NOT the
predicate `FullTriple.CD`, which needs a `FullTriple`.

## S2 semigroup, S3 FullTriple, S4 CD (TARGETS of the assignment, stated, NOT claimed)
```lean
noncomputable def lebesgueRdFull (d : ℕ) (hd : 2 ≤ d) : FullTriple (Fin d → ℝ)       -- S3 (F1–F10, S10, S11)
theorem lebesgueRd_CD_iff : (lebesgueRdFull d hd).CD ρ n ↔ ρ ≤ 0 ∧ (d:ℝ≥0∞) ≤ n     -- S4 (n-range via f = Σ xᵢ²/2 ∈ 𝒜)
```
The easy full-triple fields F1, F2, F3, F5, F6, F7, F9 depend only on S1-type calculus and are candidates if time allows (see Status); F8, F10, S10, S11
need the heat kernel / Fourier analysis (open).

## DIFFERENCE FROM BGL
* BGL treats `ℝ^d` with `𝒜₀ = C_c^∞`; no deviation in S1.
* `E = Fin d → ℝ` (sup norm) instead of `EuclideanSpace`; operators are norm independent; measure identical (Lebesgue).
* S1 only for `d ≥ 1` (DiffusionTriple.finite_prob is vacuous because `volume` is infinite).

## Status
Stage reached: **S1 and S1' PROVED; S2, S3, S4 NOT done (not attempted beyond the route assessment).**  No sorry, no set_option, 0 warnings,
axioms of all theorems below: propext, Classical.choice, Quot.sound (`AxiomCheck.lean`).

Proved (namespace `MarkovTriple.BGL.LebesgueRd`):
* `Basic.lean`: `A₀ d`, `A d`, `dd`, `Lf`, `Gf`, `ibp_cs`, `ibp_L`, `integral_Lf`, `dd_comp`, `Gf_comp` (chain rule, D3 diffusion), `dense_Lp`, `cut` exhaustion,
  `not_isFiniteMeasure (hd : 1 ≤ d)`, and **`lebesgueRdDiffusion (d) (hd : 1 ≤ d) : DiffusionTriple (Fin d → ℝ)`** (all D1–D8 fields), `lebesgueRd_{L,Γ,μ}_eq`.  = stage S1, for every d ≥ 1 (incl. d ≥ 2).
* `Gamma2.lean`: `dd_dd_symm`, `Lf_mul`, `dd_Lf`, `ΓA_eq_Gf`, **`Γ₂_eq : Γ₂ f f x = Σᵢⱼ (∂ᵢ∂ⱼ f)²`**, **`bochner_Rd : (1/d)(Δf)² ≤ Γ₂ f`**, and
  **`bochner_Rd_iff : 0 < n → ((∀ f smooth, ∀ x, ρ Γ f + (1/n)(Δf)² ≤ Γ₂ f) ↔ ρ ≤ 0 ∧ d ≤ n)`** with test functions `y ↦ y₀` and `|y|²/2` (named `quad`).
  Deviation from the Statements section: the sharpness theorem is stated as this iff (stronger than `bochner_Rd_sharp`), for real `n > 0`.
  This is the pointwise (ρ,n)-condition on `C^∞(ℝ^d)` for the diffusion triple's `Γ₂`; it is NOT `FullTriple.CD` (no `FullTriple` exists yet).

### Update (continuation): stage S3a PROVED, `FullEasy.lean`
`Lf_comp` (second-order chain rule `Δ(ψ∘f) = Σ ∂ⱼψ Δfⱼ + Σ ∂ₗ∂ⱼψ Γ(fⱼ,fₗ)`), `F1`, `F2` (bump function `bump`, positivity detection), `A_comp` (F3), `L_mem_A` (F4),
`F5`, `F6Γ`, `F6L`, `ibp_L'`, `F7`, `F9` (connexity), all for `lebesgueRdDiffusion d hd` and `𝒜 = A d`; axioms: propext, Classical.choice, Quot.sound (`AxiomCheck.lean`).
Still OPEN for `lebesgueRdFull` (the heat-kernel stage, route (a), was assessed and NOT attempted beyond that; nothing of it is claimed):
  (i) Gaussian smoothing `heatRd a φ x = ∫ φ(x + a z) dγ_d(z)` on `C_c^∞(ℝ^d)`: smoothness, `∂ᵢ heat = heat ∂ᵢ`, L² membership (port of Lebesgue/Heat.lean lines 1–150, generic in d via `Measure.pi gaussianReal`);
  (ii) strong L²-derivative `d/dt heatRd = Δ heatRd` (Heat.lean 150–559, Taylor remainder `rho`, ≈ 450 lines in 1-D; in ℝ^d the Taylor/remainder bounds need second derivatives in all directions);
  (iii) Duhamel identification `semigroup_eq_heat` (Identify.lean) ⇒ F8 (`P_t f ∈ C^∞`) and S11 (`P_t u_n → 1` via `heatM_tendsto_one`);
  (iv) S10 (ergodicity): 1-D uses du Bois-Reymond; in ℝ^d needs `∇u = 0` in the weak sense ⇒ constant (mollification or Fourier);
  (v) F10 (ESA of Δ on C_c^∞): the 1-D proof (`ODE.lean`, `Core2*.lean`) uses the explicit ODE resolvent `v − v'' = ψ`, which has NO analogue in ℝ^d; needs elliptic regularity / Bessel potential (Fourier) — the hardest step, ≳ 1500 lines.
Therefore `lebesgueRdFull` and `lebesgueRd_CD_iff` (as `FullTriple.CD`) are NOT stated as theorems.

NOT done (exact open items for `lebesgueRdFull`; F1,F2,F3,F4,F5,F6,F7,F9 are now done, see Update above):
* F1, F2, F3, F4, F5, F6, F7, F9: elementary, follow from the calculus above (port of `Lebesgue/FullEasy.lean`, ~250 lines; needs `Lf_mul`, `ibp_L` — already here; F6L needs the second-order chain rule `L(ψ∘f)` = Σ ∂ψ Lf + Σ ∂²ψ Γ, not proved in this round); F2 via bump functions.
* S2/F8/S11/S10/F10 (heat semigroup identification `P_t f = e^{tΔ}f ∈ C^∞`, `P_t 1 = 1`, ergodicity, ESA of Δ on C_c^∞): this is the bulk.  Route estimate (see top): port of the 1-D `Heat/Identify/ODE/Cutoff/Core2*/Ergodic` ≈ 3500 lines in ℝ^d; Fourier route ≈ 2500 lines; tensorisation: needs a product theorem for `FullTriple` (not in the library), ≈ 3000 lines.  None attempted.
* Consequently `lebesgueRd_CD_iff` (S4) is not stated as a Lean theorem about `FullTriple.CD`; its content (the Bochner range `ρ ≤ 0 ∧ d ≤ n`) is `bochner_Rd_iff`.  The conjunct `1 ≤ n` of `FullTriple.CD` is implied by `d ≤ n` for `d ≥ 1`.

Proposed ERRATA rows (not added): 
| R23-R-1 | INFO | First `(ℝ^d, Lebesgue)`, d ≥ 1 piece: `lebesgueRdDiffusion d hd : DiffusionTriple (Fin d → ℝ)` with `𝒜₀ = C_c^∞`, `L = Δ`, `Γ = ∇f·∇g` (D1–D8 all proved), `Γ₂ = Σ (∂ᵢ∂ⱼf)²`, and `bochner_Rd_iff` (range `ρ ≤ 0 ∧ d ≤ n` of the Bochner inequality on `C^∞`). It is NOT a `FullTriple`: F6L, F8, F10, S10, S11 for `ℝ^d` remain open. |
| R23-R-2 | INFO (scope) | R22-E4-1 'ℝ^d, d ≥ 2 not formalised as a FullTriple' remains true; only the DiffusionTriple and pointwise Γ₂ stage is now present. |
Proposed import in `MarkovTriple.lean`: `MarkovTriple.BGL.Instances.LebesgueRd.{Basic,Gamma2,FullEasy,AxiomCheck}`.  Frozen manifest: this statements file is registered as a `proposed` entry; no existing entry changed.

