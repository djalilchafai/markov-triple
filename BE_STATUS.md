# Bakry–Émery semigroup interpolation (Phase 4b): `CD(ρ,∞) ⇒ LSI(1/ρ)` — status

Files: `MarkovTriple/FunctionalInequalities/BE*.lean` (21 files, all < 230 lines; no `sorry`, no axiom,
no heartbeat bump; every declaration depends only on `propext, Classical.choice, Quot.sound`, see
`FunctionalInequalities/AxiomCheck.lean`).  NO Frozen file was edited (the frozen field `ibp_AA` already
carries the one non-derivable integration by parts).

## Main theorems (all PROVED, modulo the explicit hypothesis `BEStable F`)

For `F : FullMarkovTriple E`, `[IsProbabilityMeasure F.μ]`, `ρ > 0`, `F.CDFull ρ ∞`,
`F.toMarkovTriple.ErgodicL2`, `hB : BEStable F`:

* `BE.ent_le_fisher`: for `φ ∈ 𝒜₀`, `φ ≥ 0` a.e., `ε > 0`:
  `Ent(ε + φ) ≤ (∫ Γ(φ,φ)/(ε+φ) dμ) / (2ρ)`; `BE.ent_le_fisherInfo`: same with the frozen
  `fisherInfo F.toMarkovTriple (fun x => ε + φ x) / (2ρ)`.
* `BE.ent_sq_add_le`: `Ent(ε + f²) ≤ 2 (1/ρ) ℰ(f)` for `f ∈ 𝒜₀`.
* `BE.logSobolevIneq_of_CD`: `F.toMarkovTriple.LogSobolevIneq (1/ρ)` — frozen normalisation
  `Ent(f²) ≤ 2 C ℰ(f)`, `C = 1/ρ` (Gaussian: `ρ = 1`, `C = 1`; constants checked: `Γ(f²) = 4f²Γ(f)`,
  `4f²/(ε+f²) ≤ 4`, then `ε → 0` by dominated convergence, `BE.tendsto_Ent_add`).

Route (entropy route; `e(s) = Ent(ε + P_sφ)`, `q = e'`, `i = -q` the Fisher information):
1. `BEFlow`: `d/ds P_s[φ] = P_s[Lφ]` in `L²` (`hasDerivAt_orbit`), `|u| ≤ c ⇒ |P_t u| ≤ c`
   (sub-Markov + positivity clause), `∫P_t u = ∫u`, and `L_rep_eq`: if `f ∈ 𝒜`, `f,Lf ∈ L²`, `[f] = P_s[φ]`
   then `[Lf] = P_s[Lφ]` (`resolvent_eq` + commutation of `P_s` with the resolvent).
2. `BEL2/BENem/BENem2/BENem3`: `L²`-valued calculus without any pointwise-in-time regularity:
   `r ↦ ∫Θ(a_r)` and `r ↦ ∫Λ(a_r) b_r` are differentiable (resp. continuous) for `L²` curves `a, b`
   (`b` uniformly bounded), `Θ,Λ` smooth with bounded derivatives (`taylor2`, Cauchy–Schwarz toolkit).
   `BECutoff/BECut`: smooth compactly supported `Θ = x log x`, `Λ = log` near `[ε, ε+M]`.
3. `BEMain1-4`: `e' = q` and `q' ≥ -2ρ q` at every `s > 0` (`exists_deriv_qFun`): regular representative
   `u = Λ(ε + g)`, `H = exp ∘ u` of the flow from `semigroup_stable` + `BEStable`, `L²`-identification
   `P_s Lφ = L H`, `P_s L²φ = L L H`, then `BEAlg.alg` (pure `Γ`-calculus):
   `2ρ ∫ H Γ(u) ≤ ∫ (LH)²/H + ∫ u L(LH)` (`= 2∫HΓ₂(u)`), from `ibp_AA` (5 uses), `diffusion_A`, `CDFull`.
4. `BEMain5/6`: `e, q` continuous on `[0,∞)`; `q(0) = -∫Γ(φ)/(ε+φ)` (`ibp_A` + chain rule);
   `e(T) → 0` (`poincare_of_CD_infty` ⇒ `expDecay_of_poincare`; `P_T[φ] → ∫φ` in `L²`, Lipschitz `Θ`).
5. `BEGronwall`: `i(s) ≤ e^{-2ρ s} i(0)` and `e(0) ≤ i(0)/(2ρ)` (real-variable lemma `ent_le_of_decay`).

## The hypothesis `BEStable F` (`BEStable.lean`) — EVERYTHING not derivable from the frozen fields

```
structure BEStable (F) : Prop where
  A₀_bdd : ∀ f ∈ F.A₀, MemLp f ∞ F.μ
  reg : ∀ φ ∈ F.A₀, ∀ s > 0, ∀ g ∈ F.A, [P_s φ] =ᵐ g → ∀ ψ smooth, BEReg F (ψ ∘ g)
BEReg f := f, Lf, Γ(f,f) ∈ L^∞  ∧  L(Lf), L(Γ(f,f)) ∈ L².
```
Why it is needed: `ibp_AA` only integrates by parts against `k ∈ L^∞` with `Lk ∈ L²`; the Bakry–Émery
computation uses it with `k ∈ {u, Lu, Γ(u), exp u}`, `u = log P_s h`.  This is the classical regularity
(`Γ(P_s h)` bounded, `LΓ(P_s h) ∈ L²`, ...).  `reg` quantifies over all smooth `ψ` (and all
representatives `g`) because the proof forms `ψ∘g` for `ψ = Λ(ε + ·)` and `exp ∘ Λ(ε+·)`; a pointwise
`L` is not null-set stable, so a single fixed representative must carry all identities.
Also used from the frozen fields (not hypotheses): `ibp_AA`, `ibp_A`, `semigroup_stable`, `esa`
(through `resolvent_eq`), `A_comp`, `diffusion_A`, `CDFull`, positivity/sub-Markov/`P_t 1 = 1`.

## Instances

* PROVED `BEStable.of_A_eq_A₀` (finite `μ`, `𝒜 = 𝒜₀`, bounded test functions) and `BE.circle_BEStable`
  (`BECircle.lean`).  The circle is only `CD(0,∞)` (`ρ = 0`), so `logSobolevIneq_of_CD` does not apply
  (it needs `ρ > 0`), but the machinery does with `ρ = 0`: `BE.circle_second_order` — along the circle
  heat flow, `q = (d/ds)Ent(ε + P_sφ)` is differentiable with `q' ≥ 0` (Fisher information non-increasing),
  for any non-negative bounded `φ ∈ C^∞(𝕋)` (non-vacuity example with `Γ ≠ 0` included).
* PROVED `BEStable ouFull` (`Sanity/OU/BEStable.lean`, `ouFull_BEStable`) and hence the end-to-end
  Gaussian log-Sobolev inequality `ou_lsi : ouFull.toMarkovTriple.LogSobolevIneq (1/1)` via
  `BE.logSobolevIneq_of_CD` + `ouFull_CDFull` + `ou_ergodic`.  See `OU_BESTABLE.md`.

## Other remarks

* Pointwise gradient bound `Γ(P_t f) ≤ e^{-2ρt} P_tΓ(f)` did NOT fall out (it needs the same regularity
  plus time-derivatives of `Γ(P_t f)` pointwise); not attempted.
* `ErgodicL2` and `IsProbabilityMeasure` are used exactly where ERRATA B1 demands (convergence `e(T) → 0`).
* Only the non-degenerate `ε`-shift is handled: `h = ε + φ`, `φ ≥ 0` in `𝒜₀` (constants are in `𝒜`, not `𝒜₀`).
* Design note: the `L²`-calculus route avoids any pointwise-in-time differentiation of `Γ(P_t h)`;
  `ibp_AA` + `BEStable` are the only places where regularity enters.
