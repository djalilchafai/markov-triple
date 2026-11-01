# AUDIT_FROZEN3 (round 3, hostile)

Scope: DECISIONS 8-11, `Frozen/*`, `Sanity/{Circle,Lebesgue,Trivial,Ergodic}`, `Hilbert/{TripleForm,MarkovCriterion,Bridge,FullBridge}`.
Lean artefacts (not imported by root, all under `MarkovTriple/Audit/`):
`Frozen3Axioms.lean` (env walk), `Frozen3OU.lean` (G2, proved, no sorry), `Frozen3Conservative.lean` (G1, proved, no sorry),
`Frozen3CircleFull.lean` (G3: circle `FullMarkovTriple`, 2 deliberate `sorry`: `esa`, `semigroup_stable`).
BGL numbering/content is UNVERIFIED (no book access); statements about "what BGL asks" below are from memory and flagged.

## Summary table

| id | sev | where | finding | fix |
|---|---|---|---|---|
| N1 | HIGH (design) | `Frozen/MarkovTriple.lean:46,49` | `comp_mem` (all smooth ψ, ψ(0)=0) + `memLp` forces every `f ∈ A₀` to be μ-essentially bounded (pick ψ growing faster than 1/μ(\|f\|>n)). Not only "polynomials excluded" (ERRATA G2): every OU/Gibbs class with an unbounded element is impossible. PROVED for N(0,1): `Frozen3Audit.no_identity_in_A0_gaussian` (ψ=exp(z²)−1; any `T : MarkovTriple ℝ` with `μ = gaussianReal 0 1` has `id ∉ T.A₀`). C_c^∞ / Schwartz / C^∞(𝕋) remain fine. | restrict ψ to temperate class (below), or document A₀ ⊂ L^∞ ∩ ⋂Lᵖ |
| N2 | MEDIUM | `Frozen/Semigroup.lean:29-37` | G1 confirmed and sharpened: (a) finite μ: Friedrichs semigroup of a bare triple is NOT conservative when a Dirichlet–Poincaré inequality holds. PROVED: `Hilbert.not_conservative_of_dirichlet_poincare` (hyp. `∫f² ≤ c·energy f` on A₀, μ finite ≠0; conclusion: Friedrichs `P_t` violates clause 6). Applies to C_c^∞(0,1), Γ=f'g', c=1/2. (b) infinite μ: clause 6 is vacuous (PROVED `Frozen3Audit.markov_clause_vacuous_lebesgue`) AND `IsSemigroupOf` has no contractivity/sub-Markov clause, so e.g. a Robin-with-negative-coefficient self-adjoint extension on C_c^∞(0,∞) (positivity preserving, strongly continuous, generator extends L, grows like e^{κ²t}) is a witness. (c) even for a FullMarkovTriple with infinite μ, conservativeness is not derivable from `esa` (stochastically incomplete complete manifolds have esa for C_c^∞ yet P_t1<1; from memory of Azencott/Dodziuk/Grigor'yan, not formalised). | add clause `∀ t u, u ≤ᵐ 1 → P t u ≤ᵐ 1` (sub-Markov; derivable for the Friedrichs semigroup with the same truncation machinery: ψ_n smooth, ψ_n(0)=0, 0≤ψ_n'≤1, ψ_n→(0∨t)∧1, normal contraction + BeurlingDeny). Keep clause 6 for finite μ; for infinite μ add a separate predicate `IsConservative` (∫P_t g = ∫g, g∈L¹∩L²) used as a hypothesis only. Do NOT put conservativeness in `IsSemigroupOf` for infinite μ. |
| N3 | MEDIUM | `FullMarkovTriple.lean:66,74` | G3 (esa/semigroup_stable never inhabited for Γ≠0). Now: every other field of FullMarkovTriple is proved for the circle with `A = A₀ = C^∞(𝕋)` (`Frozen3CircleFull.lean`, `circleFull`; `circleFull_Γ_ne_zero`). Only `esa`, `semigroup_stable` remain. No contradiction found in any field. Obstacles below. | prove the two fields (plan below) |
| N4 | LOW | `MarkovTriple.lean:46` | `memLp : ∀ p ≠ ∞` includes p∈[0,1): for infinite μ this demands ∫\|f\|^p<∞ for p<1 (e.g. fails for classes decaying like 1/(1+x²)); BGL's ⋂ is over 1≤p<∞ (from memory). `memLp2`/`integrable_of_mem` only use p=1,2. | quantify `∀ p, 1 ≤ p → p ≠ ∞` |
| N5 | LOW | `scripts/check_frozen.py` | Works (OK, 13/13 listed, no unlisted, all `proposed`). Weak points: `--update` rewrites hashes with no external anchor; manifest, script and hashed files live in the same tree; `Frozen/*` import only `Frozen/*` and Mathlib (checked), so no unhashed dependency, but the *hash of Mathlib pin* is not covered (lake-manifest). | store manifest SHA in DECISIONS.md/CI, run in CI (E3) |
| N6 | INFO | `Frozen/Ergodic.lean` | For infinite μ `ErgodicL2` degenerates (L²-kernel of L̄ is {0}); fine, true for Lebesgue. Not a defect. | none |
| N7 | INFO | `Semigroup.lean:20` | docstring "such a P is unique under esa" still unproved (ERRATA L1). `semigroup_stable` universally quantifies over P so the circle proof needs uniqueness anyway (plan below). | prove or soften |

Axiom walk (item 5): `Frozen3Axioms.lean` over all 770 non-private constants of all `MarkovTriple.*` modules reachable from the root
(586 theorems, 166 defs): offenders = [], no `axiom`/`opaque`/`unsafe`/`partial` declarations, no `sorryAx`. (Run takes ~3 min.)
New Audit theorems also depend only on propext/Classical.choice/Quot.sound.

## (1) Vacuity / contradiction of `MarkovTriple`, `FullMarkovTriple`

Circle (`Sanity/Circle.lean:150,420`) and Lebesgue (`Sanity/Lebesgue.lean:~190`) prove EVERY field (read: no `sorry`, `circleTriple`/`lebesgueTriple` closed terms).
- Γ, L junk: `Γ f g = D f * D g`, `L = D∘D` are defined by `deriv` for all functions, but every field constrains them only on A₀, and every
  derived quantity (`Γ₂`, `CD`, `energy`, `qf`) evaluates Γ, L only on elements of A₀ (`Γ_mem`, `L_mem` keep us inside), so junk values never enter. OK.
- `comp_mem` is not trivially quantified: k arbitrary, ψ arbitrary C^∞ with ψ(0)=0 (Lebesgue proof uses compact support; circle uses C^∞ closure).
  Non-vacuity of `diffusion`/`dense`/`ibp` with Γ≠0: `circle_Γ_ne_zero`; Lebesgue Γ≠0 is clear (`Γ(f,f)=f'^2`).
- Bochner junk: ibp both sides integrable by `memLp`+`Γ_mem`+`L_mem`. OK.
- Consistency consequence derived by me (not a defect): `ibp` + pointwise `carre_du_champ` on A₀ give `∫L(fg)=0` and `∫fLg=∫gLf` for all f,g∈A₀.
- Verdict: no contradiction, no junk interference. The non-vacuity is real for Γ≠0 on both finite and infinite μ. Only N1/N4 are design objections.

## (2) comp_mem vs L^p (G2)

Claim (paper proof): `f ∈ A₀` not μ-ess-bounded ⇒ a_n := μ(\|f\|>n) > 0 for all n, a_n<∞ (f∈L²). Take smooth even ψ with ψ(0)=0, ψ(t) ≥ n/a_n for \|t\|≥n.
Then ∫\|ψ(f)\| ≥ n for all n, contradicting `comp_mem`+`memLp 1`. Hence A₀ ⊂ L^∞. Formalised for N(0,1) + identity (`Frozen3OU.lean`).
Consequences: OU/Gibbs with polynomial or polynomial-growth A₀ cannot be instances. A₀ = C_c^∞ or Schwartz-type remain instances (OU: L preserves C_c^∞; Schwartz stable
under ψ with ψ(0)=0). The full triple is unaffected as long as `A = C^∞` (A_comp for all ψ, no Lᵖ requirement on A).
What BGL asks (from memory, unverified): stability of A₀ under smooth ψ is the "diffusion algebra" hypothesis; I do not remember whether it restricts ψ.
Faithful formulation proposal (works whichever way BGL reads): quantify `comp_mem` and `diffusion` over
`Function.HasTemperateGrowth ψ ∧ ψ 0 = 0` (Mathlib has this predicate: smooth, all iterated derivatives polynomially bounded) on A₀, keep ALL smooth ψ on A (`A_comp`, `diffusion_A`).
Then: polynomial/poly-growth A₀ are admissible (ψ(f) of poly growth), C_c^∞ and circle trivially satisfy it (weaker hypothesis), and the truncations ψ_δ=√(t²+δ²)−δ are
temperate (needs a one-off Lean proof of iterated-derivative bounds; alternatively use a smaller sub-class of ψ with bounded derivatives of all orders ≥1, which still contains ψ_δ and the
normal-contraction approximants, and still keeps polynomial classes stable). Cost: `Lebesgue/Circle comp_mem/diffusion` proofs weaken trivially; `isMarkovianForm` needs `trunc δ` ∈ class.

## (3) `isMarkovianForm` and `isSemigroupOf_full`

- Statement `IsMarkovianForm` (`Bridge.lean:39`): ∀u∈Q ∃v∈Q, v=|u| ∧ E(v)≤E(u): this is exactly the first Beurling–Deny criterion for the Friedrichs closure (Q, E). Correct.
- Proof (`MarkovCriterion.lean:208-253`): ψ_δ(f)∈A₀ by `comp_mem`; `Γ(ψ_δ f)=ψ_δ'(f)²Γ f ≤ Γ f` by unconditional `diffusion` (symmetry step `T.Γ_symm` checked);
  L² approximation by dominated convergence with bound `0≤|t|−ψ_δ(t)≤min(δ,|t|)` (checked: `trunc_bounds`); lower semicontinuity from `closed_of_bounded`. Hypotheses used: `comp_mem`, `diffusion`, `memLp 2`, `Γ_nonneg`, `ibp` (via `qf`). Nothing smuggled. Works for infinite μ.
- Note positivity only (|u|). L^∞/sub-Markov needs the normal contraction `u↦(0∨u)∧1`, same proof with ψ_n; this is the missing derivation behind N2.
- `resolvent_eq` (`FullBridge.lean:166`): identity checked by hand: ⟨R(u−v)−u,(1−L)g⟩ = ⟨f−Lf,g⟩−⟨f,g⟩+⟨f,Lg⟩ = −⟨Lf,g⟩+⟨f,Lg⟩ = 0 by `ibp_A` and `ibp_A_symm` (both equal −∫Γ(f,g)); density from `esa`. Correct; uses f∈A only through the two fields.
- `tripleSemigroup_one`: needs `1∈A`, `L 1=0` (`diffusion_A` with k=0, ψ≡1, empty sums), `MemLp 1 2` (finite μ). Correct. Side effect: for finite μ `ibp_A_symm` with f=1 forces `∫Lg=0` ∀g∈A₀; true for all intended instances.
- `isSemigroupOf_full` correct and unconditional for full triples. It is therefore not vacuous: `semigroup_stable` always has a witness P.

## (4) G1 counterexample and the `IsSemigroupOf` clause

Formal: `Frozen3Conservative.lean`, `not_conservative_of_dirichlet_poincare` (axioms clean). Proof: conservative ⇒ `P_t u=u` ⇒ (by `tendsto_generator_iff`) `u∈D(A_F)`, `A_F u=0` ⇒ `R u=u`
⇒ `u∈Q`, `E(u)=0` (`E_R`) ⇒ approximants f_n∈A₀, `E(f_n)→0`, `‖f_n‖²≤c E(f_n)` ⇒ `u=0`, contradicting ‖1‖²=μ(univ)>0.
Instance of the hypothesis: C_c^∞(0,1) (Lebesgue on (0,1)): f(x)²≤x∫f'² ⇒ ∫f²≤½∫f'². (I did not build the C_c^∞(0,1) MarkovTriple in Lean; the theorem is stated abstractly for any triple satisfying the inequality. Density of C_c^∞(0,1) in L²(0,1) would be the only new work.)
Recommendation: see N2 (sub-Markov clause yes; conservativeness clause only for finite μ).

## (3b) What `FullMarkovTriple` is missing for conservativeness at infinite μ
Cutoffs: nothing in the structure gives `φ_n ↑ 1`. Conservativeness for infinite μ needs a volume-growth type condition (not derivable). Treat as hypothesis `IsConservative`.

## G3 (item 1b): circle as FullMarkovTriple, exact obstacles

Proved in `Frozen3CircleFull.lean` (with `A := C^∞(𝕋)` as a `Subalgebra`, reusing `circleTriple`): `A₀_le, A_measurable, A_comp` (no ψ(0)=0 needed), `L_mem_A, Γ_mem_A, Γ_symm_A, Γ_add_A, Γ_smul_A, Γ_nonneg_A, L_add_A, L_smul_A, carre_du_champ_A, diffusion_A, ibp_A` (A=A₀ so ibp_c + continuity gives integrability), `ibp_A_symm` (ibp_c with roles swapped + Γ symmetry). 
Remaining (sorry):
1. `esa`: `(1−L)C^∞(𝕋)` dense in L². Route A (no Fourier basis): trigonometric polynomials `Atrig` ⊂ A₀ are dense in L² (already `AC_top`, `dense_Lp`). Filter Atrig by total degree d (finite-dimensional, L-invariant since D cC=−2π sC, D sC=2π cC). On V_d, `1−L` is injective (u=Lu ⇒ ∫u²=∫uLu=−∫Γ(u,u)≤0 ⇒ u=0 a.e. ⇒ u=0 by continuity + full support of Haar), hence surjective by finite dimensionality; so range ⊇ Atrig, dense. Needs ~150 lines (degree filtration of `Algebra.adjoin`, full support of `haarAddCircle`, a.e.-zero continuous ⇒ zero).
2. `semigroup_stable` (the hard one). For every `P` with `IsSemigroupOf` (so uniqueness is part of the proof): (a) show ⟨P_t u, e⟩ for e=cos(2πn·), sin(2πn·) ∈ A₀ satisfies g'=−4π²n² g (right derivative from clause 7 + semigroup law + self-adjointness: P_{t+h}e−P_te = P_t(P_he−e)); conclude g(t)=e^{−4π²n²t}g(0) (Mathlib right-derivative ODE uniqueness); (b) Fourier-expand P_tu in L² (real cos/sin basis; Mathlib's `fourierBasis` is complex, so a real↔complex bridge is needed: this is the main cost); (c) the series Σ e^{−4π²n²t}(a_n cos+b_n sin) with a_n,b_n bounded converges in C^∞ (`contDiff_tsum`/`hasDerivAt_tsum`) to a smooth g, equal a.e. to P_tu; (d) `MemLp g 2`, `MemLp (L g) 2` trivial for continuous g on a compact space. ~400+ lines. No contradiction expected (statement is true).
No mathematical obstruction to `FullMarkovTriple` for the circle; only formalisation cost (real Fourier, uniqueness of semigroup from the generator clause). Lebesgue ℝ analog needs the heat kernel: same shape, harder (Fourier transform instead of series); recommended order: circle first.

## (6) What phase 4 (Bakry–Émery) will need beyond the current surface

Poincaré (finite μ, `ErgodicL2`, CD(ρ,∞) on A₀ only) needs NO stable class, via an integrated L² route:
 (i) for g∈A₀: `∫LΓ(g)=0` (apply `ibp_A_symm` with f=1∈A, test Γ g... precisely `∫1·L h = −∫Γ(1,h)=0` for h=Γ g∈A₀ using `diffusion_A` k=0); (ii) hence `∫Γ₂(g)=∫(Lg)²` and by CD a.e. `∫(Lg)²≥ρ∫Γ(g)`; (iii) both sides continuous in the graph norm, `esa`/`resolvent_eq` ⇒ valid for all g∈D(L̄); (iv) spectral: σ(−L̄)⊂{0}∪[ρ,∞), ergodic ⇒ gap ρ ⇒ `Var(f)≤ℰ(f)/ρ` (`SpectralGap.lean` exists). Minimal extra lemmas: (i), (iii), a lemma "ℰ(g)=⟨g,−L̄g⟩, ‖L̄g‖² continuous in graph norm", kernel of L̄ = constants from `ErgodicL2`.
LSI / pointwise Γ(P_tf)≤e^{−2ρt}P_tΓf (the semigroup interpolation) needs more, none currently provided:
 1. sub-Markov L^∞ bound for P_t (N2) and `P_t(f+ε)=P_tf+ε` (finite μ) so that Φ(P_tf) with Φ=x log x on [ε,M] is `ψ(P_tf)` for a smooth ψ on ℝ (A_comp) with bounded range.
 2. an enlarged stable-class field: for f∈A₀, t≥0, g=P_tf: `g∈A`, `g, Lg, Γ(g), L(Γ g)` ∈ L² (and `g` essentially bounded), and `Γ(g,Lg)∈L²`; currently `semigroup_stable` gives only g, Lg ∈ L². Without `Γ(g)∈L²`, `LΓ(g)∈L²` one cannot apply `ibp_A_symm`/`resolvent_eq` to `Γ(P_tf)` to get `∫LΓ(P_tf)=0` and `Γ(P_tf)∈L¹`.
 3. time regularity: `s↦Γ(P_sf)` differentiable in L¹ (or `s↦P_s f` in the graph norm of A-calculus) with derivative `2Γ(g,Lg)`; the Hilbert-level derivative lemmas (`hasDerivAt_semigroup`) give L² derivative of g only. Needs `Γ: L²-graph → L¹` continuity (Γ(g)−Γ(h) bound by Cauchy–Schwarz with `Γ(g−h)` in L¹, i.e. ℰ-norm).
 4. `CDFull` (Γ₂≥ρΓ on A) is already stated; also need `Γ₂` of g=P_tf to be in L¹ (part of 2).
 5. infinite μ: constants are not in A₀ and `1∈A` is not in L²; replace the integration against 1 by a cutoff sequence `φ_n∈A₀, 0≤φ_n≤1, φ_n↑1, sup Γ(φ_n)≤1/n` (Gaffney-type; also gives `esa`), plus an integrability class (√Γ(h)∈L¹); then `∫Lh=lim∫φ_nLh=−lim∫Γ(h,φ_n)=0`. Or restrict phase 4 to probability μ (recommended: all LSI/PI/Ent targets have `IsProbabilityMeasure`).
 6. ergodicity transfer: `ErgodicL2` ⇒ `P_tf→∫f` in L² (spectral; `SpectralGap.lean`).

## Prioritized to-do for phase 4
1. Decide N1: adopt temperate-ψ (or bounded-derivative ψ) in `comp_mem`/`diffusion`; otherwise document A₀⊂L^∞ and restrict OU/Gibbs instances to C_c^∞/Schwartz. Frozen change: re-hash, re-audit.
2. Decide N2: add the sub-Markov clause to `IsSemigroupOf` and prove it for `tripleSemigroup` (normal contraction via truncations); add `IsConservative` as separate predicate; keep clause 6 as is for finite μ.
3. N4: `1 ≤ p` in `memLp`.
4. Poincaré via the integrated L² route (needs only existing fields): lemmas (i)-(iv) above. Cheapest first deliverable; no stable class needed.
5. Prove `esa` for the circle (Route A), then `semigroup_stable` (real Fourier). Gives the first genuine `FullMarkovTriple` with Γ≠0 and exercises `isSemigroupOf_full`, `resolvent_eq`, `tripleSemigroup_one` beyond Γ=0.
6. Strengthen `semigroup_stable` (items 2-3 of §6) before attempting LSI; check on circle/ℝ that the strengthened statement is provable (circle: P_tf has rapidly decaying Fourier coefficients, so all bounds hold).
7. Prove or soften `Semigroup.lean` uniqueness docstring (L1); run `check_frozen.py` and `Frozen3Axioms.lean` in CI (E3).
