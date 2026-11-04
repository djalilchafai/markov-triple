# Round 24, Stream A: `FullTriple` on `(ℝ^d, Lebesgue)`: statements fixed BEFORE the proofs

Namespace `MarkovTriple.BGL.LebesgueRd`; files `Instances/LebesgueRd/Full/*`.  Method: statements first, deviations in `## DIFFERENCE FROM BGL`,
errata rows `R24-A-*`.  Base: `lebesgueRdDiffusion d hd` (R23-R), `𝒜₀ = C_c^∞`, `𝒜 = C^∞`, `L = Δ`, `Γ = ∇f·∇g`, F1–F7, F9 proved (`FullEasy.lean`).

## 0. What the `FullTriple` structure requires (no probability-measure obstruction)
`FullTriple E extends StandardTriple E` with fields F1–F10, `StandardTriple` adds S10 (`ergodic`) and S11 (`conservative`, via exhaustion sequences,
so that `1 ∉ L²` is allowed).  `DiffusionTriple.finite_prob` is vacuous for infinite `μ` (the 1-D `lebesgueFull` is the precedent).  **Nothing forces a
probability measure; no obstruction theorem is formalised or needed.**  The fields still OPEN for `ℝ^d` (R23-R) are exactly:
F8 (`semigroup_A`), F10 (`esa`), S10 (`ergodic`), S11 (`conservative`).

Why the existing `ℝ^d` machinery does not apply: `EllData d` (`GibbsRd/Ell.lean`) builds `μ = Z⁻¹ w dx` with `Z = ∫ w < ∞` (fields `integrable`, `a_exh`),
hence its `diff`, `ellReg`, `weakHypo_unconditional`, `f8_unconditional`, `full` are for PROBABILITY measures (the Gaussian `ℝ^d` triple
`(gaussData d).gibbsRdFull_unconditional` with `CD 1 ∞` already exists).  The Lebesgue case `w ≡ 1` would need `a = I/w` with a proper
`a`-gradient-1 function, impossible for integrable `w`; so the elliptic-regularity chain of `GibbsRd/Elliptic*` cannot be instantiated and is not
reused.  (Statement-level obstruction, not formalised.)

## 1. Route (DIFFERENCE FROM BGL)
BGL (Prop 3.3.10, 3.3.11, Thm 3.3.23) obtains S10, F10 from hypoellipticity (Weyl's lemma for `Δ`) + completeness, and S11 from completeness + `CD(0,∞)`.
Here, with infinite `μ` and no elliptic-regularity chain available, the SAME statements are obtained from the **Gaussian heat flow**
`heatRd a φ(x) = E φ(x - aZ)`, `Z ~ N(0,I_d)` (`a² = 2t`), by a port of the 1-D proofs of `Instances/Lebesgue/{Heat,Identify,Core,Ergodic,Full}.lean`:
* `∂ₐ heatRd a φ = a · heatRd a (Δφ)` strongly in `L²` (`hasDerivAt_heatL2`);
* `heatRd a φ ∈ 𝒟(L)`, `L heatRd a φ = heatRd a (Δφ)` (cut-offs `ζ_k = s(2 - √(1+|x|²)/(M(k+1)))`, closedness of the Friedrichs generator);
* **F10** (core): if `w ⟂ (1 - L)𝒜₀` then `g(a) = ⟪w, heat_a φ⟫` solves `g' = a g`, is bounded (contraction), hence `g(0) = 0`, `⟪w,φ⟫ = 0 ∀φ ∈ 𝒜₀`, `w = 0`
  (replaces the 1-D resolvent ODE `v - v'' = ψ`, which has no analogue in `ℝ^d`; also replaces Weyl's lemma);
* **S10**: `u ∈ 𝒟(L)`, `Lu = 0` ⇒ `⟪u, heat_a φ⟫` is constant in `a`, tends to `0` (`‖heat_a φ‖₂ → 0`), so `u = 0` (a constant in `L²(ℝ^d)`, `d ≥ 1`, is `0`);
* Duhamel identification `P_t [f] = [heatRd (√(2t)) f]` for `f ∈ 𝒜₀` ⇒ **F8** (smooth representative) and **S11** (dominated convergence, `∫ g = 1`).

## 2. Statements (frozen)

### Part H-a (`HeatDefs.lean`, `HeatAPI.lean`)
```lean
noncomputable def gam (d : ℕ) : Measure (Fin d → ℝ) := Measure.pi fun _ => gaussianReal 0 1
noncomputable def heatRd (a : ℝ) (φ : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : ℝ := ∫ z, φ (x - a • z) ∂(gam d)
noncomputable def heatL2 (φ) (a : ℝ) : Lp ℝ 2 volume := if h : MemLp (heatRd a φ) 2 volume then h.toLp (heatRd a φ) else 0
theorem heatRd_smooth (hφ : φ ∈ A₀ d) (a) : Sm (heatRd a φ)
theorem dd_heatRd (hφ) (a) (i) : dd i (heatRd a φ) = heatRd a (dd i φ)
theorem Lf_heatRd (hφ) (a) : Lf (heatRd a φ) = heatRd a (Lf φ)
theorem abs_heatRd_le (hC : ∀ x, |φ x| ≤ C) (a x) : |heatRd a φ x| ≤ C
theorem integrable_heatRd / memLp_heatRd (hφ) (a) : MemLp (heatRd a φ) 2 volume
theorem integral_heatRd (hφ) (a) : ∫ heatRd a φ = ∫ φ
theorem coeFn_heatL2, heatL2_zero
theorem integral_mul_heatRd_comm (hφ hψ) (a) : ∫ ψ * heatRd a φ = ∫ φ * heatRd a ψ
theorem norm_heatL2_le (hφ) (a) : ‖heatL2 φ a‖ ≤ ‖heatL2 φ 0‖
theorem heatRd_tendsto_one (ha : a ≠ 0) (hmeas) (hle : ∀ n, ∀ᵐ y, |u n y| ≤ 1) (hlim : ∀ᵐ y, u n y → 1) x : heatRd a (u n) x → 1
theorem tendsto_heatL2_zero (hφ) (hd : 1 ≤ d) : Tendsto (fun a : ℝ => heatL2 φ a) atTop (𝓝 0)
```
(exact Lean text: `HeatAPI.lean` stub, verbatim).
### Part H-b (`HeatDeriv.lean`)
```lean
theorem hasDerivAt_heatL2 (hφ : φ ∈ A₀ d) (a : ℝ) : HasDerivAt (fun b : ℝ => heatL2 φ b) (a • heatL2 (Lf φ) a) a
```
### Part B-a (`DomainAPI.lean`)
```lean
theorem isComplete_lebesgueRd (hd : 1 ≤ d) : (lebesgueRdDiffusion d hd).IsComplete
theorem preFull_lebesgueRd (hd : 1 ≤ d) : PreFull (lebesgueRdDiffusion d hd) (A d)
theorem domain_of_smooth_L2 (hd) (hu : Sm u) (h0 : MemLp u 2 volume) (h1 : ∀ i, MemLp (dd i u) 2 volume) (h2 : MemLp (Lf u) 2 volume) :
    ∃ h : h0.toLp u ∈ (lebesgueRdDiffusion d hd).generator.domain, (lebesgueRdDiffusion d hd).generator ⟨h0.toLp u, h⟩ = h2.toLp (Lf u)
theorem domain_of_approx ...        -- graph limits of test functions are in the domain
theorem heatL2_mem_domain (hd) (hφ : φ ∈ A₀ d) (a : ℝ) :
    ∃ h : heatL2 φ a ∈ gen.domain, gen ⟨heatL2 φ a, h⟩ = heatL2 (Lf φ) a
```
### Part B-b (`Full/Esa.lean`, `Full/Ergodic.lean`, `Full/Identify.lean`, `Full/Main.lean`)
```lean
theorem esa_lebesgueRd (hd : 1 ≤ d) : (lebesgueRdDiffusion d hd).ESAProp                                   -- F10
theorem ergodic_lebesgueRd (hd) (u) (hu : u ∈ gen.domain) (h : gen ⟨u,hu⟩ = 0) : ∃ c : ℝ, (u : _ → ℝ) =ᵐ[volume] fun _ => c   -- S10
theorem semigroup_eq_heatRd (hd) (hf : f ∈ A₀ d) (t : ℝ≥0) :
    (lebesgueRdDiffusion d hd).semigroup t ((lebesgueRdDiffusion d hd).cls ⟨f, hf⟩) = heatL2 f (Real.sqrt (2 * t))
theorem conservative_lebesgueRd (hd) : S11 for lebesgueRdDiffusion
noncomputable def lebesgueRdFull (d : ℕ) (hd : 1 ≤ d) : FullTriple (Fin d → ℝ)
   -- toDiffusionTriple = lebesgueRdDiffusion d hd, A = A d
theorem lebesgueRdFull_CD_iff (hd) (ρ : ℝ) (n : ℝ≥0∞) : (lebesgueRdFull d hd).CD ρ n ↔ ρ ≤ 0 ∧ (d : ℝ≥0∞) ≤ n
```
Also (finite-measure counterpart, wrappers only): `gaussRdFull d : FullTriple (Fin d → ℝ)` = `(gaussData d).gibbsRdFull_unconditional` with `CD 1 ∞`
(already proved in `GibbsRd`; `d ≥ 1` irrelevant).

## Status (to be updated at the end of the round)
(see the end of this file)
