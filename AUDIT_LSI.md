# AUDIT_LSI (round 7, hostile) — `MarkovTriple.Sanity.OU.ou_lsi`

Verdict: no refutation found. No CRITICAL/HIGH/MEDIUM findings. LOW/INFO notes below.

## (1) Unfolding / frozen statement
- `Audit/LSIAudit.lean` (not imported by root, compiles, sorry-free, std axioms only) proves
  `gaussian_lsi_unfolded : IsProbabilityMeasure (gaussianReal 0 1) ∧ ∀ f, ContDiff ℝ ⊤ f → HasCompactSupport f →
   Ent (gaussianReal 0 1) (f²) ≤ 2 * ∫ (deriv f)² ∂(gaussianReal 0 1)` directly from `ou_lsi`
  (unfolding energy/ouFull/ouTriple/Go by simp). Also an `example` that A₀ contains a nonzero function.
- Frozen `LogSobolevIneq T C` (Frozen/LSI.lean:15-17) = `IsProbabilityMeasure μ ∧ ∀ f ∈ A₀, Ent μ (f²) ≤ 2*C*energy f`,
  `energy f = ∫ Γ f f dμ` (Frozen/Energy.lean). With C=1/1 this is Gross' normalisation for N(0,1)
  (equality for e^{λx}). Not weaker/vacuous: probability conjunct present; quantifier over all of A₀=C_c^∞; no junk,
  since for f ∈ C_c^∞ the function f² log f² is continuous with compact support (integrable), so `Ent` is the honest value.
- Numerics (python, grid ±12): e^{λx} truncated: Ent = RHS (equality, λ=0.3,1,2: 0.2155/0.2155, 14.778/14.778, 23848/23922 trunc.);
  He_3·e^{-x²/2s}, (1+x)e^{-x²/2}, smooth bump: all satisfy Ent ≤ RHS (e.g. 0.32 ≤ 6.5, 0.035 ≤ 0.26). Consistent.

## (2) `mehler_ae` (Sanity/OU/MehlerEq.lean:~100)
- Destructuring `obtain ⟨h0, hadd, hcont, hself, -, -, -, hgen⟩ := hP` matches the 8 clauses of frozen `IsSemigroupOf`
  (Frozen/Semigroup.lean:38-47): P0=id, semigroup, strong cont., self-adjoint, [pos, ≤1, 1↦1 discarded], generator on A₀.
  Positional but correct. `hgen` is a genuine clause of the frozen def (the semigroup is characterised by its generator on A₀),
  so `eigen_hL` (Stable.lean:55) using it is legitimate, not smuggling. No extra hypothesis beyond `IsSemigroupOf ouTriple P`.
- `Mh a c f x = ∫ f(a x + c y) dγ(y)` (Mehler.lean:18) with a=e^{-t}, c=√(1−e^{-2t}) (MehlerEq statement): real Mehler kernel.
  Proof by equality of Hermite coefficients (coeff_Mh via rotation invariance of γ⊗γ, Q_eq Hermite identity a²+b²=1).
- `mehlerS`: smoothness by dominated differentiation; `decay_Mh` gives |x|^m|Mh f| ≤ C using compact support of f
  (R-bound argument, |c|≤1) — correct; derivative formula iteratedDeriv_Mh a^n Mh(f^{(n)}) gives all Schwartz seminorms.
  Needs only 0<a, |c|≤1 (satisfied for t>0, and t=0).
- g = Mh uses `Continuous.ae_eq_iff_eq` with `γ.IsOpenPosMeasure` (BEStable.lean:13, proved from Gaussian ≪ Lebesgue): valid.

## (3) `beReg_comp_schwartz` and consumption
- Statement for ALL smooth ψ:ℝ→ℝ (`ContDiff ℝ ⊤`), G Schwartz. Trick: bump ∈ ContDiffBump 0 with rIn=|C|+1 ≥ sup|G|,
  `bump·ψ'` smooth compact support ⇒ temperate growth, composes with G (temperate), equals ψ'∘G since bump=1 on the ball. Correct.
  (ψ∘G)'=W Schwartz; L(ψ∘G)=Ls W, Γ=W², LL, LΓ are Schwartz images ⇒ L∞ / L² w.r.t. γ (probability, so L∞⊂L²). Correct.
- `BEStable.reg` (FunctionalInequalities/BEStable.lean:30-34): ∀φ∈A₀, s>0, g∈A with P_sφ =ᵐ g, ∀ smooth ψ: BEReg (ψ∘g).
  `ouFull_BEStable` supplies exactly this, with P = Friedrichs semigroup (isSemigroupOf_full), g upgraded from a.e. equality to
  equality with `Mh …` by continuity; quantifiers match. `A₀_bdd` clause proved by compact support.
- Note `BEReg` uses `ouFull.L/Γ` which are defeq to Lo/Go (used via `show`); fine.

## (4) Banned constructs / axioms
- grep (sorry|axiom|native_decide|unsafe|opaque|implemented_by|extern) over MarkovTriple/: only comment/doc hits. No `set_option` in audited files.
- Axiom walk (LSIAudit.lean, `run_cmd`): 405 non-internal constants in MarkovTriple.Sanity.OU.*, FunctionalInequalities.BE*, Frozen.LSI:
  0 with non-standard axioms, 0 unsafe/partial/opaque/axiom. `#print axioms ou_lsi` = [propext, Classical.choice, Quot.sound].

## (5) Junk / representative / finiteness
- `deriv` appears only on smooth functions (Sm); `Ent` junk branch unreachable (see 1). ψ∘g representative issue handled by `hgeq`
  (g equals Mh pointwise, not merely a.e.). Finite-measure assumptions: `BEAlg` lemmas need `IsFiniteMeasure`, discharged by
  `IsProbabilityMeasure ouFull.μ`, which is the real γ (not an extra assumption); `logSobolevIneq_of_CD` takes `[IsProbabilityMeasure F.μ]`
  as instance and the frozen def re-exports it as the conjunct.

## Findings
- LOW/cosmetic: `LogSobolevIneq (1/1)` — literal `1/1` (ρ=1) is fine but reads oddly; no action.
- INFO: LSI is stated on C_c^∞ only (frozen design); extension to H¹ not claimed. Not a defect.
- INFO: `mehler_ae` destructures `IsSemigroupOf` positionally; if clauses of the frozen def are reordered it fails to compile (safe failure). Optional fix: named projections.
