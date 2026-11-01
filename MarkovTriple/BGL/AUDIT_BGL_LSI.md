# AUDIT_BGL_LSI (round 9, hostile) — unconditional Gaussian LSI and gradient bound, BGL framework

Verdict: no soundness defect found. 0 critical, 0 high, 0 medium; 3 low/informational.
Audit files (not imported by root, sorry-free, axioms = propext/Classical.choice/Quot.sound):
`BGL/Audit/LSIUnfold.lean`, `BGL/Audit/GradUnfold.lean`, `BGL/Audit/LSIWalk.lean`.

## (1) `ouFull_LS` unfolded — PASS
`LSIUnfold.concrete_lsi`: for every `f : ℝ → ℝ`, `ContDiff ℝ ⊤ f`, `HasCompactSupport f`:
`Integrable (f² log f²) γ` AND `∫ f² log f² dγ − (∫ f² dγ) log(∫ f² dγ) ≤ 2 ∫ (deriv f)² dγ`,
`γ = gaussianReal 0 1`. Proved from `ouFull_LS` (so integrability is real, no Bochner junk on the LHS;
the RHS integrand `(f')²` is continuous compactly supported, so integrable).
Normalisation: `LogSobolevIneq μ Γ 𝒞 C D := prob ∧ 0<C ∧ 0≤D ∧ ∀ f∈𝒞, Ent(f²) ≤ 2Cℰ(f)+D∫f²`
(BGL Frozen/LSI.lean:21); `LS 1 0` is `Ent(f²) ≤ 2ℰ(f)`, `ℰ(f)=∫Γ(f,f)=∫f'²` (`Γ := Go`, f'·g').
That is Gross's inequality with the sharp constant (equality for `e^{λx}`: Ent = 2λ²e^{2λ²} = RHS).
Test class `𝒜₀ = C_c^∞(ℝ)`, nonempty, Γ ≠ 0, so not vacuous (probe `lsi_empty` in Probes.lean does not apply).
Numerics (Gauss quadrature on [-14,14]): `e^{λx}·1_{|x|<8}` λ=.5,1,2,3: LHS/RHS = 1 − 1e-9, 1−5e-9, 0.9999, 0.983;
`x`, He2, He3, cos 3x, 1+.3x: 0.73/2, 3.15/8, 14.8/36, 0.15/9, 0.1715/0.18. All satisfied; the
near-equality for exponentials confirms the constant 2 (C=1) cannot be improved and is not accidentally weak.

## (6) Agreement with the old `ou_lsi` — PASS (equivalence proved)
`LSIUnfold.old_of_new : Sanity.OU.ouFull.toMarkovTriple.LogSobolevIneq (1/1)` from `concrete_lsi`
(i.e. from BGL `ouFull_LS`), and `LSIUnfold.new_of_old : old ⇒ ouFull.toDiffusionTriple.LS 1 0`.
Both unfold to the same inequality on the same class `C_c^∞`, same measure, same Γ, same `Ent`
(the two `Ent` defs are syntactically identical; `energy` agree by `rfl`+`sq`).
Note: `new_of_old` is cheap because `ou_lsi` is already an unconditional theorem; it only shows
the statements coincide, not independence of proofs (the two proofs are in fact independent routes:
old = `BE.logSobolevIneq_of_CD` + `BEStable`; new = `EntropyInterpolation` + Gronwall).

## (2) The regularity structures — PASS (INFO-1, INFO-2)
`GradientInterpolation` (Theory/GradientBound.lean:~92): continuity of Φ(s)=∫P_s h·Γ(P_{t−s}f) on [0,t];
for 0<s<t integrability of k_sΓ(g_s), k_sΓ₂(g_s) and `Φ' = 2∫k_sΓ₂(g_s)`. Hand check: Φ' = ∫(Lk)Γ(g) − 2∫kΓ(g,Lg)
= ∫k(LΓ(g)−2Γ(g,Lg)) = 2∫kΓ₂(g) (book's computation in 3.3.18). Genuine, not trivially true; CD(ρ,∞) is NOT in the
structure (applied separately in `gradient_integrated`).
`EntropyInterpolation` (Theory/LogSobolev.lean:~108): continuity of e,I on [0,∞), `e'=−I`, `I'=−2J_Λ` with integrability
of `gΓ₂(Λ∘g)`, `gΓ(Λ∘g)`, for each cutoff Λ of log. Standard de Bruijn/second-derivative content; no field states LSI, Poincaré,
a decay estimate, or a limit at ∞.
Circularity: `ent_le_fisher` gets the s→∞ limit from `tendsto_entE` (Convergence.lean), which uses Poincaré
derived by `poincare_of_CD_infty` from CD(ρ,∞) + `ESAProp` (Theory/Poincare.lean) — independent of both structures. Ergodicity/spectral
gap is exactly what Bakry–Émery needs (BGL 5.7.1 uses P_t f → ∫f); not circular. `LogSobolevMain` re-uses no LSI/PI field.
Instance proofs (LSIGrad.lean:172, LSIMain.lean:51–93) prove the fields as stated with `e'=−I`, `I'=−2J` (`entJ` via the
identified `Γ₂ = f''²+f'²`, `Γ = f'²`), with explicit bounded-continuous integrability (`integrable_of_bd`, `Bd`,`Lin` families,
Gaussian IBP `ibpγ` with bounded G,G' — no hidden growth assumption). Junk-Bochner search: every integral in a field has a
bounded continuous (or linear-growth against γ) integrand; the structure fields for `entE`/`entI` themselves assert no
integrability, but (INFO-1) integrability of the `entI` integrand for s>0 follows from `hasDerivAt_I`'s second clause via
`entI_eq` (a.e. equality) and at s=0 from φ∈𝒜₀ bounded; `entE`'s integrand is a.e. in [ε log ε, (ε+M)log(ε+M)] hence integrable. So
no junk-satisfiable instance exists for a FullTriple satisfying F1–F10, but a reader must make this deduction (documentation nit).
INFO-2: `GradientInterpolation.hasDerivAt` is stated only for `h ≥ᵐ 0` and uses `.toNNReal` clamps; in the interior (0,t) the clamps are inactive.

## (3) `Pt_eq_Uf` / `Pt_eq_m0` (LSIMehler.lean:311,319) — PASS
`Pt` is `Classical.choose` of an `𝒜`-representative (smooth, hence continuous) of the Friedrichs semigroup class; `Pt_mehler`
(Full.lean) gives a.e. equality with `Uf φ r = ∫ φ(e^{-r}x + √(1−e^{-2r})y) dγ(y)`, the genuine Mehler kernel for `L f = f''−xf'`
(checked: P_t x = e^{-t}x, `∂_s P_s φ = L P_s φ` is proved in `hasDerivAt_Uf_s`). Both sides continuous, γ has full support
(`IsOpenPosMeasure γ` instance, BEStable.lean:16), so `Continuous.ae_eq_iff_eq` upgrades to everywhere. Valid at r=0 too (`ec 0 = 0`).
Even a wrong `Pt` could not falsify the *statement* of `ouFull_LS` (it does not mention Pt); the statement of the gradient bound
only mentions `Pt` through the class `semigroup t`, which is identified in GradUnfold.

## (4) `ouFull_gradient_bound` — PASS (INFO-3)
`GradUnfold.concrete_grad`: for f∈C_c^∞, t≥0, a.e. x,
`(e^{-t} ∫ f'(e^{-t}x+cy)dγ(y))² ≤ e^{-2t} ∫ f'(e^{-t}x+cy)² dγ(y)`, c=√(1−e^{−2t}).
This is Γ(P_t f) ≤ e^{−2ρt}P_tΓ(f) with ρ=1 (BGL Cor 3.3.19: strong form of Thm 3.3.18), the right inequality, true
(Jensen) and tight: equality iff f' is constant on the relevant support (f=x truncated at large R: ratio observed
0.92–0.96 on x∈[-3,3], bump R=6, margin ≥ 5e-5, never negative). INFO-3: for OU it reduces to Cauchy–Schwarz/Jensen, so the
test is mathematically easy, but the Lean path is the general interpolation proof, which is what the framework is meant to exercise.

## (5) Axioms / banned constructs — PASS
`LSIWalk.lean`: walked all 472 non-internal constants of namespace `MarkovTriple.BGL` in the import closure of `LSIMain`
(+Convergence, GradientBound): 0 with extra axioms, 0 with sorry, 0 axiom/opaque declarations.
`#print axioms` for the five targets (+ `ouFull_CD`, `Pt_mehler`, `ouFull`): propext, Classical.choice, Quot.sound only.
Grep over all `MarkovTriple/**` excluding Audit: no `sorry`/`axiom`/`native_decide`/`unsafe`/`opaque`/`implemented_by`/`extern`
(one comment mention of "sorry" in Sanity/Ergodic.lean:147), no maxHeartbeats/maxRecDepth overrides.

## Findings
| id | sev | location | note | fix |
|----|-----|----------|------|-----|
| INFO-1 | info | Theory/LogSobolev.lean `EntropyInterpolation` | integrability of the entE/entI integrands is implicit (derivable) | add a docstring remark or explicit fields |
| INFO-2 | info | Theory/GradientBound.lean `GradientInterpolation` | `.toNNReal` clamps, a.e.-nonneg h; harmless | none |
| INFO-3 | info | LSIMain.lean `ouFull_gradient_bound` | statement is Jensen for OU; non-vacuous & tight | optionally cite `GradUnfold.concrete_grad` |
No counterexample to any claim was found.
