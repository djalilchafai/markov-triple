# Round 25, Stream F: `Core2` for `(ℝ^d, Lebesgue)` and the Gaussian `ℝ^d` triple (statements fixed BEFORE the proofs)

Namespace `MarkovTriple.BGL.LebesgueRd`; files `Instances/LebesgueRd/Core2/*`.  `Core2` is `FullTriple.Core2` (`Extension/Converse.lean:237`):
`∀ a ∈ 𝒜₀, ∃ b_n ∈ 𝒜₀, (1-L)b_n → a and L(1-L)b_n → La in L²`, equivalently (`core2_iff_dense`) `(1-L)²𝒜₀` dense in `L²`
(`L²`-essential self-adjointness of `L²` on `𝒜₀`).  Round 24 D: `Core2` is NOT a consequence of F1-F10 + CD (`goFullTriple_not_core2`, non-complete).

## Targets
```lean
-- F1: the finite-measure Gaussian triple (wrapper of the existing R18 theorem `gaussData_core2`)
theorem gaussRdFull_core2 (d : ℕ) : (gaussRdFull d).Core2
-- F2: Lebesgue measure on ℝ^d, d ≥ 1 (infinite measure; `lebesgueRdFull` of R24-A)
theorem lebesgueRdFull_core2 (hd : 1 ≤ d) : (lebesgueRdFull d hd).Core2
-- F3: consequence, the Core2-based converse of BGL Prop 3.3.17 for (ℝ^d, Lebesgue)
theorem lebesgueRdFull_mem_domain_of_Γ₂ {ρ : ℝ} {n : ℝ≥0∞} (hCD : (lebesgueRdFull d hd).CD ρ n) {f} (hf : f ∈ (lebesgueRdFull d hd).A)
    (hf2 : MemLp f 2 (lebesgueRdFull d hd).μ) (hG : Integrable (FullTriple.G (lebesgueRdFull d hd) f f) (lebesgueRdFull d hd).μ)
    (hG2 : Integrable ((lebesgueRdFull d hd).toDiffusionTriple.Γ₂ f f) (lebesgueRdFull d hd).μ) :
    ∃ hF : hf2.toLp f ∈ (lebesgueRdFull d hd).toDiffusionTriple.generator.domain,
      (((lebesgueRdFull d hd).toDiffusionTriple.generator ⟨hf2.toLp f, hF⟩ : Lp ℝ 2 (lebesgueRdFull d hd).μ) : _ → ℝ)
        =ᵐ[(lebesgueRdFull d hd).μ] (lebesgueRdFull d hd).L f
```

## Route for F2 (DIFFERENCE FROM BGL)
BGL does not treat Core2 (tacit step, ERRATA R15-1).  Route here: `core2_of_dense`; density of `(1-L)²𝒜₀` by orthogonality.  If `w ⟂ Ψₗ 𝒜₀`:
1. fourth-order cut-off: for `v = heatRd a φ` (`φ ∈ 𝒜₀`), `b_n = cut n * v ∈ 𝒜₀`, `[b_n] → [v]`, `[L b_n] → [L v]`, `[LL b_n] → [LL v]` in `L²`
   (`L(χv) = χLv + 2Γ(χ,v) + vLχ` iterated; the commutator terms are `(scaled ∂^kχ_n) × (∂^j v)`, bounded by `C/n` times `L²` jets of `v`, all of the form `heatRd a ψ`, `ψ ∈ 𝒜₀`);
2. hence `⟨w, heat_a (1-L)²φ⟩ = 0`; with `G_k(a) = ⟨w, heat_a L^kφ⟩`: `G₀' = aG₁`, `G₁' = aG₂`, `G₂ = 2G₁ - G₀`, so `H = G₁ - G₀` solves `H' = aH`, bounded, so `H ≡ 0`;
3. then `G₀' = aG₀`, bounded, `G₀(0) = ⟨w,φ⟩ = 0` for all `φ ∈ 𝒜₀`, so `w = 0`.
This is the heat-flow ODE argument of R24-A F10 pushed one order up; it replaces the 1-D resolvent construction of `Lebesgue/Core2.lean` (no resolvent solution `v` is needed).

## Part 2 (abstract; no theorem claimed)
No theorem "complete + `CD(ρ,∞)` ⇒ `Core2`" is known to us or in BGL (`Γ₂ ≥ ρΓ` gives no bound on `Lχ_n`, which the 4th-order cut-off needs, cf. R24 `hyp_core2_route_status`).
No formal statement is attempted beyond what R24 D has; `hypRiem`: nothing claimed.  Documented in `GAPS.md`.

## Status (end of Round 25, stream F): F1, F2, F3 PROVED as stated (statement section unchanged)
Files: `Core2/Cut4.lean` (rescaled profiles `Sc`, `SmallFam`, `Qf`, `abs_Lf_mul_le`, `cutoff4_graph_aux`: the fourth-order cut-off), `Core2/Main.lean`
(`heat_graph4`, `inner_heat_orth4`, `ode_all_zero`, `eq_zero_of_orth4`, `dense_Ψ_lebesgueRd`, `lebesgueRdFull_core2`, `gaussRdFull_core2`,
`lebesgueRdFull_mem_domain_of_Γ₂`), `Core2/AxiomCheckR25F.lean` (all: propext, Classical.choice, Quot.sound only).  No sorry, no set_option, 0 warnings.
Deviation from the plan text: none in the statements; the ODE step is implemented as `H = G₁ - G₀`, `H' = aH` (then `G₀' = aG₀`), exactly as in the route.
`gaussRdFull_core2` is a rename of R18 `gaussData_core2` (`BddHess3` route), no new analysis.
Part 2 (abstract): no theorem claimed.  The route above used, for `(ℝ^d, Lebesgue)`, the explicit structure `Δ(χ_n v) = χ_n Δ v + 2Γ(χ_n,v) + vΔχ_n` with
`|∂^kχ_n| ≤ C n^{-k}` and `v` with `L²` jets up to order 4 (`heatRd a φ`); for a general complete triple with `CD(ρ,∞)` the available hypotheses (`Γ₂ ≥ ρΓ`,
`Γχ ≤ 1`) bound no `Lχ_n`, `Γ(χ_n, Γ(χ_n,·))`, `LLχ_n`, so the same step is unavailable; hypRiem: nothing claimed.
