# Hostile audit, Round 24 Stream A (FullTriple on (R^d, Lebesgue))

Auditor merged `worktree-agent-a1099c578b27f3286` (impl HEAD a1194b1, base 6bff800). Full `lake build` (9455 jobs): success, 0 warnings, 0 errors.

## Verdict: ACCEPT (no HIGH/MEDIUM findings; 3 LOW doc-level, 2 fixed here)

## Checks
(a) Real object. `lebesgueRdDiffusion d hd` has `μ := volume` on `Fin d → ℝ` (`finite_prob` discharged by `not_isFiniteMeasure hd`, so genuinely infinite),
`A₀ = {C^∞ ∧ HasCompactSupport}`, `L = Lf = Σ ∂ᵢ²` and `Γ = Gf = Σ ∂ᵢf ∂ᵢg` (defined via `fderiv`), `A = C^∞`.
Frozen structures (`StandardTriple`, `FullTriple`, `ESAProp`, `IsExhaustion`) are untouched: `git diff 6bff800..HEAD` touches only `Full/*`, `MarkovTriple.lean`, GAPS, manifest.
S10 is the genuine "L u = 0 on 𝒟(L) => u a.e. constant" (quantification over all `u ∈ domain`, not vacuous; proof shows `u = 0`, correct since `1 ∉ L²`).
S11 is the frozen exhaustion-sequence form (hypotheses are satisfiable: `cut` is an exhaustion; the proof handles t = 0 and t > 0 separately).
F10 is the genuine `ESAProp`: every `u ∈ 𝒟(generator)` is a graph limit of `cls (a n)`, `a n ∈ 𝒜₀` (via `core_of_orth`).
`lebesgueRdFull` fields are all assigned from proofs, no hypothesis-parameters; `FullTriple.toDiffusionTriple = lebesgueRdDiffusion` by `rfl`.
(b) Manifest. Exactly one entry for `STATEMENTS_R24_A.md`, status `proposed`, sha256 matches the current file; `scripts/check_frozen.py` prints OK.
The entry and the file were added in commit 5277c76 (21:31), before every proof commit (first proof 21:36+); that commit's hash (2ae2cd...) differs from the final one only because
a "Status (end of Round 24)" section was APPENDED in a1194b1 (diff confirms: only +10 lines at the end, frozen text lines 1-77 unchanged); the manifest was updated consistently. Acceptable (status append, not statement change).
(c) Build and axioms. No `sorry`, `set_option`, `native_decide`, `axiom` in `Full/*` (only a docstring containing "axioms"). `#print axioms` run by me (via full import `MarkovTriple`) and by `AxiomCheckR24A`:
`lebesgueRdFull`, `esa_lebesgueRd`, `ergodic_lebesgueRd`, `conservative_lebesgueRd`, `semigroup_A`, `semigroup_eq_heatRd`, `lebesgueRdFull_CD_iff`, `gaussRdFull`: all `[propext, Classical.choice, Quot.sound]`.
(d) Mathematics. `heatRd a φ(x) = E φ(x - aZ)` has variance a^2, so `∂ₐ = a Δ` (as `∂ₛ = Δ/2` with s=a^2): matches `hasDerivAt_heatL2 : d/da heat = a • heat(Δφ)`.
Semigroup `e^{tΔ}` (L = Δ, Γ = ∇f·∇g, no 1/2) corresponds to a = sqrt(2t): `semigroup_eq_heatRd` states exactly `heatL2 f (sqrt (2 t))`. Correct.
Duhamel: `g(s) = ⟪P_s f, Q_{t-s}ψ⟫`, derivative cancels via symmetry of the generator and `heatL2_mem_domain`; one-sided constancy from continuity on [0,t]; endpoints use heat symmetry. Sound.
F10: `w ⟂ (1-L)𝒜₀` transported to smoothed functions by cut-off graph convergence, `G' = sG`, `|G| ≤ C`, so `G(s) = G(0) e^{s²/2}` forces `G(0)=0` (`zero_of_ode_bdd`, checked). Sound and independent of Weyl's lemma.
S10: `G` constant, tends to 0 (`‖heat_a φ‖₂ → 0`, needs d ≥ 1), so `⟪u,φ⟫ = 0` for all φ in 𝒜₀, `u = 0`. Sound.
CD: pointwise Γ₂ = Σ(∂ᵢⱼ f)²; iff proved both directions incl. n = ∞ and using continuity to upgrade a.e. to everywhere; 1 ≤ n is part of the CD definition. Sound.
(e) Honesty. "No obstruction" is correct: `FullTriple` never requires a probability measure (`finite_prob` is a vacuous implication). The related claim that `EllData` machinery is for probability
measures and cannot be instantiated with w = 1 is a heuristic remark, explicitly marked not formalised: acceptable. 1-D `lebesgueFull` is cited only as precedent; no shadowing: `gam`, `heatRd`, `heatL2`, `semigroup_A` etc. are in `MarkovTriple.BGL.LebesgueRd`, and the repo builds with no clash.
`gaussRdFull` is a plain `def` alias of `(gaussData d).gibbsRdFull_unconditional` with `CD 1 ∞`, probability-measure instance, PI and LS; nothing new claimed. `gaussRdFull` had no earlier definition.
(f) Docs.

## Findings
* LOW-1 (fixed): GAPS Round 23 block still said "PARTIAL: (R^d, Lebesgue) ... missing F8, F10, S10, S11" and "OPEN: FullTriple on R^d", contradicting the new Round 24 entry. Annotated as superseded/closed.
* LOW-2 (not fixed, frozen file): `STATEMENTS_R24_A.md` still contains the placeholder "## Status (to be updated at the end of the round) (see the end of this file)" above the appended status; harmless. Left as is to keep the manifest hash.
* LOW-3 (not fixed): the status text says "no ERRATA needed"; the 'a = I/w impossible for integrable w' remark in section 0 is only a heuristic. Neither affects correctness. GAPS correctly notes the Core2 / Prop 3.3.17 converse for this triple is unexamined (the triple is complete, so the generic converse applies via `isComplete_lebesgueRd`, a possible follow-up).
