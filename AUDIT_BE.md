# AUDIT_BE (round 6, hostile)

Scope: `FunctionalInequalities/BE*.lean` (esp. BEStable, BELSI, BEAlg, BEMain1-6, BEGronwall, BECircle),
`Frozen/{LSI,Fisher,CDFull,FullMarkovTriple,Semigroup}`. Lean files (not imported by root, compile):
`MarkovTriple/Audit/BEAudit.lean` (3 s), `MarkovTriple/Audit/BEAxiomWalk.lean` (2 min).

## Verdicts

| # | Question | Verdict |
|---|----------|---------|
| 1 | Is `BEStable` satisfiable with `Γ ≠ 0`, `ρ > 0`, ergodic (is `logSobolevIneq_of_CD` vacuous)? | **NOT vacuous (mathematical argument below); NOT yet proved in Lean for any rho>0 triple** |
| 2 | Constants `Ent(f²) ≤ 2(1/ρ)ℰ(f)`, `Ent(ε+φ) ≤ I/(2ρ)` | **CORRECT, sharp** |
| 3 | Hidden assumptions / junk / circularity in BEMain*, BEAlg, tendsto_Ent_add | **None found** |
| 4 | Axioms / banned constructs | **Clean**: 263 constants, 0 non-standard axioms, 0 axiom/opaque/unsafe/partial |

## 1. Satisfiability of `BEStable` (the main risk)

Lean-checked facts (`Audit/BEAudit.lean`, axioms `propext, Classical.choice, Quot.sound`):
* `ou_hyps`: `ouFull` is a probability space, `CDFull 1 ∞`, `ErgodicL2`, `Γ(id,id) ≠ 0`.
* `conditional_gaussian_LSI : BEStable ouFull → ouFull.LogSobolevIneq (1/1)`: every hypothesis of
  `logSobolevIneq_of_CD` EXCEPT `BEStable` is discharged for OU. So the only way the theorem could be
  vacuous is `¬ BEStable ouFull`.
* `ou_A₀_bdd`: clause `A₀_bdd` holds for OU (`A₀ = C_c^∞`); it does not contradict CD(ρ>0).
* `ou_not_BEReg_id`: `BEReg ouFull id` is FALSE (id ∈ 𝒜 unbounded). So `reg` is not trivially true; it really is
  a statement about `P_sφ`, and it is false for general g ∈ 𝒜.  It is also not trivially false: see next.

Mathematical proof that `BEStable ouFull` is TRUE (so no vacuity; I tried to refute it and failed):
`𝒜 = C^∞(ℝ)` and γ has full support, so `g ∈ 𝒜` with `g =ᵐ P_sφ` equals the continuous version, i.e. Mehler:
`g(x) = ∫ φ(a x + b y) dγ(y)`, `a = e^{-s}`, `b = √(1-a²) > 0`, `φ ∈ C_c^∞`, supp φ ⊂ [-R,R].
* `g^{(k)} = a^k P_s φ^{(k)}`, and for k ≥ 1, `|g^{(k)}(x)| ≤ a^k ‖φ^{(k)}‖_∞ · γ(|a x + b Y| ≤ R)
  ≤ C_k exp(-(a|x|-R)_+² / 2b²)`. Hence `sup_x |x|^m |g^{(k)}(x)| < ∞` for all m ≥ 0, k ≥ 1, and `|g| ≤ ‖φ‖_∞`.
* Let 𝒦 = {h smooth, bounded, with `sup |x|^m |h^{(k)}| < ∞` for all m, all k ≥ 1}.  𝒦 is closed under
  `h ↦ ψ∘h` (ψ smooth: (ψ∘h)^{(k)} is a sum of `ψ^{(j)}(h) ∏ h^{(k_i)}`, k_i ≥ 1, ψ^{(j)} bounded on the
  compact range of h), under products, under `Γ(h) = h'²`, and under `L h = h'' - x h'` ((x h')^{(k)} = x h^{(k+1)} + k h^{(k)}).
  So for `g ∈ 𝒦`: `ψ∘g, L(ψ∘g), Γ(ψ∘g), L L(ψ∘g), L Γ(ψ∘g) ∈ 𝒦`, all bounded, hence in L²(γ) (finite measure).
  This is exactly `BEReg`. So `BEStable ouFull` holds.  (It also gives the unconditional Gaussian LSI.)
* Independent reassurance: any compact full triple with `𝒜 ⊆ L^∞` satisfies `BEStable` (proof of
  `of_A_eq_A₀` only uses boundedness).  With ρ > 0: round spheres `S^n` (n ≥ 2), `𝒜 = 𝒜₀ = C^∞`, Ric = n-1 > 0,
  `CD(n-1,n) ⇒ CDFull(n-1,∞)`, ergodic.  (Bonnet–Myers: finite-dimensional ρ>0 forces compactness, so the
  boundedness regime is the generic one; OU is the infinite-dimensional case, handled by Mehler decay.)
* The Fisher-type clause `L Γ(ψ∘g) ∈ L²` is not incompatible with ρ > 0: nothing in 𝒦 conflicts with CD(1,∞)
  (Γ₂(u) = u''² + u'² ≥ Γ(u)); BEStable only bounds smooth bounded quantities and says nothing on the sign of Γ₂.
* Does `BEStable` force `A₀` bounded and contradict CD(ρ,∞)? It forces `A₀ ⊂ L^∞`; consistent (OU: C_c^∞; sphere: C^∞).
  It does not force `Γ = 0`, nor 𝒜 bounded (`ouFull.A ∋ id`).

Findings:
* **F1 [MEDIUM, status not soundness]** `BEStable ouFull` is not proved in Lean, hence no unconditional Gaussian LSI.
  Remaining work (pure analysis, no abstract machinery left):
  (a) Mehler formula in Lean: `[P_sφ] =ᵐ x ↦ ∫ φ(e^{-s}x + √(1-e^{-2s}) y) dγ` for φ ∈ C_c^∞ (e.g. verify by
      checking it is smooth, in the domain, and solves the resolvent identity `R(φ - Lφ)`-type equation; or
      Hermite-series route: `P_s He_n = e^{-ns} He_n` and the integral formula agrees on He_n by the Gaussian shift identity);
  (b) derivative-under-integral and the Gaussian-tail bound above giving `P_sφ ∈ 𝒦`;
  (c) closure lemmas of 𝒦 under ψ∘, L, Γ (elementary induction), then `BEStable ouFull` by (a)-(c)+`BEReg` unfolding;
  (d) `exact ou_gaussian_LSI := logSobolevIneq_of_CD ouFull hB one_pos ouFull_CDFull ou_ergodic`  (already compiles as
      `conditional_gaussian_LSI`).
* **F2 [LOW]** `reg` quantifies over EVERY `g ∈ 𝒜` representing `P_sφ`.  Harmless for OU and compact examples, but
  over-strong for a general `𝒜` containing a.e.-modified functions (L is pointwise on 𝒜, not null-set invariant: a
  modified g could break `Lbdd`).  Sufficient and weaker: `∃ g ∈ 𝒜, [g] = P_sφ ∧ ∀ ψ, BEReg (ψ∘g)`; the proof of `step`
  (BEMain2) only uses the g obtained from `semigroup_stable`, so it would have to take the g from the hypothesis instead.
  Recommended only if a future instance has non-smooth 𝒜.
* **F3 [LOW, doc]** BEStable docstring: "Both clauses hold on any compact full triple with `𝒜₀ = 𝒜`" is correct only when
  also `𝒜₀ ⊂ L^∞`, which is true for compact continuous test functions but is an extra hypothesis (`of_A_eq_A₀` takes it).
* **F4 [INFO]** `BECircle.lean` has a global `instance : IsProbabilityMeasure circleFull.μ`; harmless, but visible
  to anything importing BECircle.  `circle_second_order` is non-junk: it is `exists_deriv_qFun` with ρ=0 (statement
  `0 ≤ q'`), hypotheses satisfiable by `1 + cos` with `Γ ≠ 0` (proved in the file); `circle_BEStable` is a real instance
  because 𝒜 = 𝒜₀ ⊂ C^∞(𝕋) is bounded.  It is NOT an instance of the `ρ > 0` theorem (circle is CD(0,∞)), so
  it provides no end-to-end evidence for `logSobolevIneq_of_CD`.

## 2. Constants

Frozen: `LogSobolevIneq C := IsProbabilityMeasure μ ∧ ∀ f ∈ 𝒜₀, Ent(f²) ≤ 2 C ℰ(f)`, ℰ = ∫Γ(f,f).
* Gaussian (ρ=1, Γ(f)=f'², C = 1): `Ent(f²) ≤ 2∫f'²` is the standard sharp Gross inequality.  Sharpness check
  (analytic and numerical quadrature): `f = e^{λx}`: `Ent(f²) = 2λ² e^{2λ²} = 2∫f'²` (equality, λ=0.3,1,2 agree to 1e-15).
  So `C = 1/ρ` is the right constant and cannot be improved.
* `ent_le_fisher`: `Ent(h) ≤ I(h)/(2ρ)`; derivation `e' = q = -I`, `I(s) ≤ e^{-2ρs} I(0)` (`fisher_decay`), `e(∞)=0`, hence
  `e(0) = ∫_0^∞ I ≤ I(0)/(2ρ)` (`ent_le_of_decay`). With `h = f²`: `Γ(f²) = 4f²Γ(f)` (`Γ_sq`), `4f²Γ/(ε+f²) ≤ 4Γ`,
  so `Ent(ε+f²) ≤ 4ℰ(f)/(2ρ) = 2(1/ρ)ℰ(f)` (`ent_sq_add_le`), matches `2·C·ℰ` with `C = 1/ρ`.  `ent_le_fisherInfo` uses the frozen
  `fisherInfo(ε+φ)` with `Γ(ε+φ)=Γ(φ)` (`Γ_const_add`); no junk since `Γφ/(ε+φ) ≤ Γφ/ε` is integrable (so the Bochner integral is genuine).

## 3. Hidden assumptions

* a.e./representatives: handled by a single fixed regular representative `u = Λ(ε+g)`, `H = exp∘u` from `semigroup_stable`
  (BEMain2 `step`); `L` identifications are done in L² via `L_rep_eq` (resolvent_eq), not pointwise. `aflow ∈ [ε, ε+M]`
  only a.e., used only under `filter_upwards`. OK.
* `Cut` (BECut) has compactly supported smooth Θ, Λ equal to x log x, log on a neighbourhood of [ε, ε+M], M ≥ max(‖φ‖_∞,1).
  No junk: `Θ_eq`, `deriv_Θ_eq` etc. proved from `hΘeq` (eventually-equal in `𝓝 y`).
* `Ent` junk: `Ent(ε+φ)` is a true entropy (φ bounded); the final step `tendsto_Ent_add` (dominated convergence with the
  `1+(1+|g|)²` bound from `|x log x| ≤ x²+1`-type lemma `abs_mul_log_le`, `g=f² ∈ L²` since f ∈ 𝒜₀ ⊂ L⁴) shows
  `Ent(ε+f²) → Ent(f²)`; `f² log f²` is integrable (limit statement is about the same Bochner integral so no junk).
* Circularity: `ErgodicL2`, `IsProbabilityMeasure` enter only through `poincare_of_CD_infty`/`expDecay_of_poincare`
  (`tendsto_eFun`) and `oneL2`/`MemLp (1)`.  `Poincare.lean` imports only GapFromSquare/TripleSquare/Hilbert (resolvent,
  functional calculus), NOT any BE file and no semigroup interpolation: not circular.  It uses `CDFull.toCD` (CD on 𝒜₀).
* Uses of CD: `CDFull ρ ∞` pointwise a.e. on 𝒜 in `alg` (n⁻¹ = 0 for ∞ via `ENNReal.inv_top`), correct.
* `ibp_AA` use: five instances in `alg`, with all L²/L^∞ side-conditions supplied by BEReg; checked signatures match the frozen field
  (`f,Lf,k,Lk ∈ L²`, `k ∈ L^∞`).

## 4. Axioms / banned constructs

`Audit/BEAxiomWalk.lean`: every non-internal constant in `MarkovTriple.FunctionalInequalities.*` and `MarkovTriple.Frozen.*`
(263 constants): 0 with axioms other than `propext, Classical.choice, Quot.sound`; 0 axiom/opaque/unsafe/partial declarations.
grep over `FunctionalInequalities/`, `Frozen/` for `sorry|axiom|native_decide|unsafe|implemented_by|@[extern|opaque|admit|set_option|macro|syntax|elab|partial`:
only a comment in Frozen/MarkovTriple.lean ("nothing is an axiom").  `Audit/BEAudit.lean` axioms: standard.

## What remains for a fully unconditional Gaussian LSI

Only `BEStable ouFull` (F1): Mehler/Gaussian-tail estimate `P_sφ ∈ 𝒦` plus closure of 𝒦, as detailed above.  Everything else
(`CDFull 1 ∞`, `ErgodicL2`, `IsProbabilityMeasure`, `semigroup_stable`, `ibp_AA`, the interpolation) is already proved for `ouFull`.
