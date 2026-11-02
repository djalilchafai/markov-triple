# AUDIT: strong gradient bound, extension to D(L), completeness (HEAD 22c80b2)

Scope: Theory/Strong/*, Theory/Extension/*, Theory/Complete/*, Instances/OU/Strong*.lean,
Instances/Lebesgue/{GradBound,StrongBound}.lean. Book: Prop 3.3.16/3.3.17, Thm 3.3.18, Lemma 3.3.21, Def 3.3.9, Thm 3.3.23.

## Verdict
No soundness defect found. Build is green. All 24 headline `#print axioms` (re-run from a scratch file) give only
`[propext, Classical.choice, Quot.sound]`. grep over the scope: no `sorry`, `admit`, `native_decide`, `maxHeartbeats`,
`set_option`, or `axiom` declaration. Remaining findings are scope/fidelity gaps and presentation.

## Findings (severity ranked)

### MEDIUM-1: `gamma_limits` covers only part of Prop 3.3.16 (i)-(iii); the rest of 3.3.16 and all of 3.3.17 are absent
`FullTriple.gamma_limits` (Extension/Main.lean:368) is faithful for what it states:
for every u in D(L), Gamma and Gamma_2 extend as L^1 limits along ANY graph-convergent sequence in A0 (so the extension is
independent of the sequence: this is the content of (iii)), such a sequence exists (ESA), `int Gamma_2 = ||Lu||^2` (3.3.8),
`int Gamma = -<Lu,u>`, and CD extends (`rho*G1 + n^-1 (Lu)^2 <= G2`, which is (ii); CD(rho,n) is more general than the book's
CD(rho,inf)). Gaps:
* only the diagonal `Gamma(u)`, `Gamma_2(u)`; no bilinear extension (i), no explicit continuity statement for the extension map
  (the `dist_G1_le`/`dist_K1_le` estimates are there but not packaged);
* Prop 3.3.16 (iv)-(viii) (Hessian extension, product rule (vi), (vii), extended inequality (viii)) are NOT formalized;
* Prop 3.3.17 (identification of the two definitions on A ∩ D(L), Gamma_2(f) in L^1 for f in A ∩ D(L), converse under ergodicity)
  is NOT formalized. `Theory/Gamma2Integral.lean` header admits this.
Fix: do not describe `gamma_limits` as "Prop 3.3.16" without "(i)-(iii), diagonal, operator level". Add the missing items to
the correspondence table as open. Strong/Main does not depend on them (it works with A0 and Pt f in A), so Thm 3.3.18 is unaffected.

### MEDIUM-2: `strong_gradient_bound` assumes `0 <= rho`; the book's Thm 3.3.18 is for any real rho
Book: "CD(rho, inf), every f in A0, t >= 0" with rho in R (proof written for rho = 0 only, "extension straightforward").
`strong_integrated/strong_eps/strong_gradient_bound` require `hρ : 0 ≤ ρ`; the real inequality `key_ineq` genuinely uses
`rho >= 0` (`rho*(S-eps) <= rho*u/S`). For rho < 0 the theorem is not formalized. All instances (circle 0, OU 1, sphere 2,
Lebesgue 0) are covered. `reinforced_cd` and `strongD_ge`'s inputs do not need the sign. Fix: state the restriction in docstrings
as a deviation (the docstring of Strong/Main.lean does mention `ρ ≥ 0`), or prove the rho < 0 case (replace `psi_eps` by a
rescaled functional, or use `Phi(s) = e^{-rho s}...` with the sign-adjusted inequality; not a trivial rewrite). Also note the
hypothesis is `CD rho n` for arbitrary n (stronger theorem than the book's n = inf, fine).

### MEDIUM-3: `ouFull_conservative_of_complete` / `lebesgue_conservative_of_complete` are non-vacuous routes but redundant statements
The proofs genuinely go through `ExtendedAlgebra.conservative_of_complete` (Conservation/Mass.lean:252), which takes
`HasGradientBound` + `IsComplete` and never reads the S11 field (`DiffusionTriple` has no S11; `ExtendedAlgebra` is a Prop built
from F1-F10 fields). Lebesgue: the gradient bound is proved from the explicit heat kernel and Jensen; OU: via `ouFull_GradientInterpolation`.
Hence not "just reading S11". But the conclusion is the same as the `conservative` field of `StandardTriple` (S11), which
`lebesgueFull`/`ouFull` carry, so as theorems they give no new information about these instances: they are consistency checks of the
abstract theorem (Thm 3.3.23), not evidence for it beyond that. (Slightly stronger than S11: all exhaustion sequences, not only
nonnegative ones.) Fix: wording only ("independent re-derivation"). The second claim of Thm 3.3.23 (rho > 0 => mu(E) < inf) lives in
Conservation/Finite.lean (outside scope).

### LOW-1: `StrongInterpolation` is a Prop-structure hypothesis; satisfiable, not obviously over-strong
Content: for all eps > 0, f,h in A0, h >= 0 a.e., t >= 0: `Phi_eps` continuous on [0,t]; for s in (0,t) integrability of two
integrands and `HasDerivAt Phi_eps (int P_s h * strongD) s` with `strongD = L(psi_eps∘Gamma g) - 2 psi_eps'(Gamma g) Gamma(g,Lg)`,
g = P_{t-s} f. It is discharged unconditionally, with kernel axioms only, for (a) every compact triple
(`CompactTriple.strongInterpolation`, CompactCurve/CompactMain: L^2-differentiability of Gamma(P_{t-r} f), cutoff `Fcut` equal
to psi_eps on [-(B+1),B+1], product rule, symmetry of L) and (b) OU (`ouFull_StrongInterpolation`, explicit Mehler derivatives,
`strongD_eq` identifies `sD` with `strongD`, Gaussian IBP). Both discharges are real (OU bypasses nothing: Pt s h = m0 h s is
proved by `Pt_eq_m0`). The structure is an honest statement of Lemma 3.3.20 + the differentiation step; it is the analytic
content the book glosses ("Lemma 3.3.21 ... extended by density"). Mild observation: it quantifies over all `eps`, `h` and
includes integrability of both integrands; true for all realized instances, so no vacuity or hidden strengthening for them.
For an abstract FullTriple it remains an assumption (unlike the book, which derives it from ESA + CD). Lebesgue does not use it
(heat kernel Jensen instead): the Lebesgue strong bound is an independent proof of the `eps`-form.

### LOW-2: statement fidelity of the strong bound (checked, OK)
`√Γ(P_t f) <= e^{-rho t} P_t(√Γ f)` is encoded as `Real.sqrt (ΓA (Pt t f) (Pt t f) x) <= exp(-ρ t) * (semigroup t (sqrtΓcls f)) x`
a.e. (classes; `√Γ f ∈ L^2` since Γ f ∈ A0 ⊂ L^1, `memLp_sqrtΓ`). Domain f ∈ A0 as in the book; Γ on `P_t f ∈ A` is the extended
`ΓA`. Pointwise would be wrong for L^p classes, a.e. is correct. ε→0 step (`strong_of_eps`) uses positivity/monotonicity of the
semigroup on L^2 (`semigroup_mono`) and ψ_ε(r) ↑ √r (`tendsto_psiS_sqrt`, `psiS_le_sqrt`): correct, with `ae_all_iff` over ε=1/(n+1).
The Gronwall step (`strong_integrated`: Ψ = e^{-ρ s} Φ continuous on [0,t], derivative ≥ 0 on (0,t) via `strongD_ge` and `Pt_nonneg`,
`monotoneOn_of_deriv_nonneg`) and endpoint identification (Φ(0) = ∫hψ(ΓP_t f), Φ(t) = ∫ P_t h ψ(Γ f)) are right; positivity
detection uses field F2 `pos_detect` (satisfied by all instances, including OU where 𝒜₀ = C_c^∞). Lemma 3.3.21 is `strongD_ge`
(a.e. pointwise form, rho >= 0, n general); the book's integrated form with h in D(E) is not needed.

### LOW-3: `reinforced_cd` (ℚ-density) is valid
`poly_ineq` gives, for each rational (a,b), a.e. `0 <= K(f)·K(shifted product) − K(f, shifted product)^2` (Cauchy-Schwarz for the
a.e.-positive form K = Γ_2 − ρΓ on test pair f, (f−a)(w−b); the expansion uses K1, K2 product rules and shift invariance, all proved).
`hessian_ineq` takes `ae_all_iff` over the countable ℚ×ℚ, then at each good x extends the (closed, polynomial-in-(a,b)) condition
from the dense `ℚ×ℚ → ℝ×ℝ` (`Rat.denseRange_cast.prodMap`, `DenseRange.induction_on`, closed set `isClosed_le`) to all reals and
evaluates at (a,b) = (f x, w x), giving `Γ(w,Γf)^2 <= 2K(f)(Γf Γw + Γ(f,w)^2)`. Then `reinforced_cd` with w = Γf and
`Γ(f,Γf)^2 <= Γf Γ(Γf)` (ΓA_cs) gives `Y^2 <= 4KΓf·Y`, division by Y > 0, trivial case Y = 0. Algebra checked by hand; sign of ρ not
used; finite-n term dropped (weaker but sufficient). Matches BGL (3.3.6).

### LOW-4: completeness (Def 3.3.9) encoding and cutoffs are real
`IsComplete`: ∃ ζ_k ∈ 𝒜0, ζ_k ≥ 0 a.e., increasing a.e., ζ_k → 1 a.e., `Γ(ζ_k) <= (1/(k+1))^2` a.e. (index shift; `√Γ ζ_k <= 1/(k+1)` is
stronger than the book's `1/k` for k >= 1; the √ is lost in the book's PDF text). "positive" read as nonnegative (book convention).
Lebesgue/OU witnesses (`Complete/Real.lean`): ζ_k = χ(x/(M(k+1))), χ(x) = smoothTransition(2 − x²), M = max(1, ‖χ'‖∞):
smooth and compactly supported (so ∈ C_c^∞ = 𝒜0 for both; for OU 1 ∉ 𝒜0 so genuine cutoffs are required and are used);
0 <= ζ_k (`chi_nonneg`); `zeta_mono` proven via smoothTransition monotonicity and (x/R)² decreasing in R; `zeta_tendsto`: ζ_k(x) = 1
once k >= ⌈|x|⌉ (since |x|/R_k <= 1 as R_k >= k), everywhere, hence a.e.; `zeta_deriv_sq_le`: |ζ_k'| <= |χ'|/R_k <= 1/(k+1).
The hypothesis `Γ f f = f'·f'` a.e. is discharged by `rfl` for both `lebesgueDiffusion` and `ouDiff`, i.e. definitionally; correct.

### LOW-5: housekeeping
* Strong/AxiomCheck.lean and the `#print axioms` lines at the bottoms of the audited files are fine; nothing else imports them.
* Linter warnings only (unused simp args in GradBound:61, unused `hε` in OU/StrongMain:42, `haveI`).
* Sphere instance uses rho = 2 with CD(2,3) (`sphere_CD_two_three`): consistent with the stated constant; unrelated to the generic
  theorem's soundness.
* `Strong/Main.lean` docstring says "ρ ≥ 0" as a deviation but README-level docs should list MEDIUM-1/2 as open items.

## Suggested fixes (priority)
1. Document `gamma_limits` as Prop 3.3.16 (i)-(iii), diagonal; add 3.3.16 (iv)-(viii) and 3.3.17 to the open list.
2. Document the ρ ≥ 0 restriction as a deviation from Thm 3.3.18 (or prove ρ < 0).
3. Reword the two `*_conservative_of_complete` docstrings as consistency checks (S11 is a field).
4. Optionally add a one-line docstring on `StrongInterpolation` that it replaces the book's Lemma 3.3.20-3.3.21 density argument and is an assumption for abstract triples.
