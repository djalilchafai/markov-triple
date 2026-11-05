# AUDIT R30 Stream S (hostile): unconditional MarkovProcessBridge for `gaussRdFull d`

Verdict: **ACCEPT**.  No CRITICAL/HIGH/MEDIUM findings.  Merge of `worktree-agent-a742058ecf33a9679` (7603754 freeze, ae21d22 proofs) onto base 09dcbbe.

## Verification performed
* Full `lake build`: "Build completed successfully (9572 jobs)", whole log contains 0 warnings/errors; the 9 new modules (GaussMeasure, MehlerBasic, L2Deriv, Duhamel, MehlerTime, MehlerL2, GaussIdentify, GaussBridge, AxiomCheckR30S) all compiled and are imported in `MarkovTriple.lean`.
* `grep sorry|set_option|native_decide|admit|axiom` over `R30/`: only a prose occurrence of "sorry" in the STATEMENTS Status line.
* Own `#print axioms` (via `import MarkovTriple`) on `gaussRdFull_mu`, `gaussRdFull_semigroup_eq_Q`, `gaussRdFull_isTestClassRep`, `duhamel_unique`, `green_Qν`, `hasDerivAt_Mh_time`, `gaussRdFull_bridge_all`, `gaussRdFull_bridge`, `gaussData_bridge`, `gaussRdFull_bridge_kernel`: all exactly `[propext, Classical.choice, Quot.sound]`.
* `scripts/check_frozen.py`: OK.

## (a) Bridge genuine; `duhamel_unique` not circular
* `gaussRdFull_bridge_all d := gaussRdFull_bridge_of_rep (gaussRdFull_mu d) (gaussRdFull_isTestClassRep_all d)`; type is the genuine `MarkovProcessBridge (gaussRdFull d).toDiffusionTriple` whose `rep` quantifies over all bounded measurable `g` with `MemLp g 2 μ` against the real `T.semigroup`; `kernel_zero/add` come from R29 `mehlerSemigroup` (exact at every x). `gaussRdFull_bridge_kernel` is `rfl`.
* `duhamel_unique` hypotheses: `Q` continuous on ℝ, `HasDerivAt Q (DQ s) s` for s>0, Green identity `⟨L̄v, Q s⟩ = ⟨v, DQ s⟩` for all `v ∈ 𝒟(L̄)`, s>0.  Conclusion `P_t (Q 0) = Q t`.  Nothing assumes the conclusion.  Proof read in full: tests against `F = cls g` (dense, in 𝒟(L̄)), `u s = P_{t-s}F` with derivative `-P_{t-s}L̄F` for 0<s<t via `hasDerivAt_semigroup` (t-s>0, `R g0 = F`), `gg s = ⟨u s, Q s⟩`; derivative = `⟨u',Q⟩+⟨u,DQ⟩ = -⟨L̄ P F,Q⟩+⟨PF,DQ⟩ = 0` using commutation `P L̄F = L̄ P F` and Green on `v = P_{t-s}F ∈ 𝒟(L̄)`.  Constancy on [ε,t] from `constant_of_has_deriv_right_zero`; endpoint 0 handled by continuity of `gg` (from continuity of `u`, `Q`) and uniqueness of limits along 𝓝[>]0; endpoint t by continuity.  t=0 case separately (`semigroup_zero`).  Self-adjointness of `P_t` gives `gg 0 = ⟨P_t Q0, F⟩`.  Correct; junk values of `u s` for s>t are irrelevant.
* Green identity `green_Qν`: from the `esa` field (core property: `a n ∈ A₀`, `cls(a n)→v`, `Lcls(a n)→L̄v`) plus smooth IBP `E.ibp_sm` with compact support of `a n`; limits by joint continuity of inner product.  Genuine.

## (b) S1
`gam d = Measure.pi fun _ => gaussianReal 0 1` (HeatDefs.lean:19): the true N(0,I_d).  `gaussData_dens_eq`: `gdens x = (√(2π))⁻ᵈ e^{-|x|²/2}` (checked `gdens_eq`), `∫ gdens = 1` from `gam` being a probability measure with `gam_eq_withDensity`, hence `Z = ∫e^{-|x|²/2} = (√(2π))^d = (2π)^{d/2}`.  Z is obtained by normalisation against the already-known product density rather than by a Fubini Gaussian integral; logically equivalent and sound.  d=0: `Fin 0 → ℝ` is a point, `gam 0 = Dirac`, Z=1; the statements are true and non-abused (degenerate, L=0, kernels Dirac).

## (c) Operator
`gauss_L_eq` proves `(gaussData d).toEll.L f = Lou f` with `Lou g = Σ∂ᵢ²g − Σxᵢ∂ᵢg` (V = |x|²/2, ∇V = x).  `aa σ = e^{-σ}`, `cc σ = √(1−e^{-2σ})` match `ouA`, `√ouVar`.  Hand check of `Lou_Mh`: ∂ᵢMh = a·Mh(∂ᵢφ), ∂ᵢ²Mh = a²Mh(∂ᵢ²φ), so Lou Mh = a²Mh(Δφ) − aΣxᵢMh(∂ᵢφ): matches the Lean statement (proved via heat-flow API).  `hasDerivAt_Mh_time` has derivative `Lou (Mh (aa s)(cc s) φ) x` at s>0: consistent with ∂ₛQₛ = LQₛ (cc'(s)=a²/c, aa'=-a, Gaussian IBP).  Sign conventions consistent with the Green identity (`generator` = L̄ = Δ − x·∇, nonpositive).

## (d) Scope
C_c^∞ → all bounded measurable L² is done inside R29 `gaussRdFull_bridge_of_rep` via `KernelBridge.ofTestClass` (R15 `RepExtend`), already audited in R29; `gaussRdFull_bridge_all` takes only `d`; no leftover hypothesis (axioms clean, no `sorry`).  `1 ≤ d` in the frozen forms is a dummy (`_hd`), disclosed in ERRATA R30-S-2.

## (e) History
7603754 contains only `STATEMENTS_R30_S.md` + its manifest entry (no Status section).  ae21d22 appends the Status section (announced in the frozen text) and updates that file's sha256.  `git diff 09dcbbe HEAD -- frozen-manifest.json` = only the one new entry.  OK.

## (g) Docs
GAPS: Round 28-M row for `gaussRdFull d` and the R29-O PARTIAL bullet are annotated ("[ANNOTATION R30-S: ...]"), originals retained; new "Round 30, Stream S" section present.  ERRATA R30-S-1..3 present.

## Findings
* LOW-1 (doc, no action): STATEMENTS Status says "0 warnings"; confirmed.  The headline wording "Z = (2π)^{d/2}" is obtained by normalisation, not by direct Gaussian integration (see (b)); sound.
* LOW-2: `gaussRdFull_bridge`/`gaussRdFull_isTestClassRep` frozen forms carry an unused hypothesis; harmless and documented.
* INFO: `duhamel_unique` requires derivative only on (0,∞) and continuity at 0, which is exactly what the Mehler flow provides (cc not differentiable at 0).
* No doc edits needed.
