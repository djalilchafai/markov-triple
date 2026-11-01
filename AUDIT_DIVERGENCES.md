# Hostile audit of the Divergences layer

Scope: `MarkovTriple/Divergences/*.lean` (12 files) against the three source repos (shallow clones in the scratchpad `src/`). Lean v4.35.0-rc2. Nothing under Divergences/, Frozen/, Sanity/ was edited.

Artifacts (not imported by the root):
- `MarkovTriple/Audit/DivergencesAxioms.lean`: environment-walking axiom check. It covers every non-private, non-internal, non-projection constant whose module is under `MarkovTriple.Divergences`.
- `MarkovTriple/Audit/DivergencesCounterexamples.lean`: compiled junk-value witnesses (F2, F3, F4 below).

## Verdicts

| Question | Verdict |
|---|---|
| (a) vacuous or silently weakened statements | None found. Ported statements are textually the sources' modulo namespace, `Ent` generalisation, and the `PseudoMetricSpace` generalisation of weak duality. The one deliberate divergence is `wassersteinSq` for non-probability marginals (F2). |
| (b) junk-value traps | Three traps exist (F1 to F3). They are junk at non-probability inputs only. Every theorem that depends on the intended meaning carries `IsProbabilityMeasure` or an explicit integrability hypothesis. |
| (c) Ent identical to Frozen, and bridge correct | Yes. Divergences does not redeclare `Ent` (grep finds no second `def Ent`), it imports `Frozen.Ent`, and `Frozen/Ent.lean` matches its sha256 in `frozen-manifest.json` (94fcfe85...). The bridge is correct on every edge case checked (see C). |
| (d) axioms | PASS. 138 constants (115 theorems, 23 defs) were checked and the offenders list is empty, so every one depends only on propext, Classical.choice and Quot.sound. No `sorry`, `axiom`, `opaque`, `native_decide` or `set_option maxHeartbeats` appears in Divergences. |

## Per-file verdict

| File | Verdict |
|---|---|
| Entropy.lean | OK. F1 applies to `Ent`; all substantive theorems are guarded. |
| TotalVariation.lean | OK. F3 applies to the def; every theorem is guarded by probability. Normalisation is `sup_A |μA-νA|` (max 1), identical to the source and to Pinsker's constant. |
| Pinsker.lean | OK. `TV^2 <= KL/2` is the correct Pinsker constant for this normalisation. The infinite-KL case is handled in `totalVariationDistance_sq_le_klDiv`. |
| Tensorization.lean | OK. Statements are the sources', generalised to `Ent` of a nonnegative `h`; the square versions are corollaries. F1 caveat (low). |
| Wasserstein.lean | OK. F2 caveat (medium): the unified definition differs from cutoff-fastdiff off probability measures. |
| WeakDuality.lean | OK. Generalisation to `PseudoMetricSpace` with cost `dist^2` is sound; the `_norm` form is the original. |
| CompactDuality.lean | OK. Statement is the source's. The `PseudoMetrizableSpace` assumptions are redundant given `SecondCountable` and `T2` (cosmetic). |
| Gelbrich.lean | OK. `wassersteinSqP` is kept verbatim. `wassersteinSq_eq_wassersteinSq_P` is stated for probability marginals only, which is exactly what is needed. |
| KLScalarVariational.lean | OK. `klLogWitness` correctly avoids `log 0 = 0` by sending zero to `-n`. |
| KLVariational.lean | OK. Statements need probability measures. `relativeEntropyTest` has no junk because the tests are bounded and measurable. |
| Varentropy.lean | OK. The extended `evariance` is used, and `variance` only under `MemLp` (`salez_reverse_pinsker` converts via `varentropy.toReal`, which equals `variance` by definition). I did not re-check the constants of Salez eq. (10) against arXiv (no network); the theorem is proved, so it is at least true. |
| AxiomCheck.lean | Incomplete (F5, info). It lists 43 names out of 138 public constants. |

## Findings

### F1. `Ent` is not normalised for non-probability `μ` (LOW, by design)
Location: `Frozen/Ent.lean:13` (`Ent`). Divergences/Entropy.lean:34 (`Ent_nonneg`) and `Tensorization.lean:238` (`Ent_prod_tensorization`) are related.
Counterexample (compiled in `DivergencesCounterexamples.lean`): `Ent (2 • dirac 0) (fun _ => 1) = -(2 * log 2)`. The entropy of a constant is `-m log m`, not 0, and it is negative for `m > 1`.
Related junk: `Ent` returns the Bochner junk value when `f` or `f log f` is not integrable (`∫ = 0`). If `f` is not integrable, then `Ent μ f = ∫ f log f`.
Impact: `Ent_nonneg` and the bridge correctly require `IsProbabilityMeasure`. `Ent_map`, `Ent_eq_of_moments` and `Ent_prod_tensorization` have no probability hypothesis. They are true as stated (the tensorization is the unnormalised matrix inequality, `∫A log A + ∫B log B <= ∫h log h + T log T`), but for non-probability s-finite `μ`, `ν` they do not mean "relative entropy tensorises". The tensorization theorems carry integrability hypotheses on all log-moments, so the junk case is excluded.
Fix: none required. Optionally add a docstring warning on `Ent_prod_tensorization` ("for probability measures this is the usual tensorization of relative entropy").

### F2. `wassersteinSq` differs from cutoff-fastdiff for non-probability marginals (MEDIUM for downstream porting, no proof defect)
Location: `Wasserstein.lean:35` against `cutoff-fastdiff/Cutfast/Defs.lean:86`.
The unified definition takes the infimum over all measures with the given marginals. The CF definition takes the infimum over probability couplings only.
Counterexample (compiled): for `μ = ν = 2 • dirac 0` on `ℝ¹`, `wassersteinSq μ μ = 0` (via `wassersteinSq_self`), while `Gelbrich.wassersteinSqP μ μ = ⊤` (the family is empty).
Impact: the two agree for probability marginals (`wassersteinSq_eq_wassersteinSqP`). Every Gelbrich/affine/elliptic statement assumes `IsProbabilityMeasure` on the relevant measures, so ported theorems are unaffected. Any future CF lemma stated for arbitrary `μ ν : Measure (E d)` must be re-checked. For example, a CF-style "W2 = ⊤ when masses differ from 1" would now be false for mass `m ≠ 1`, where the cost is finite.
`wassersteinSq_self`, `wassersteinSq_comm`, `wassersteinSq_le_cost` and weak duality are unconditionally true for the unified def, with no probability assumption. This is correct but stronger than CF's.
Fix: document (already in the module docstring); no code change.

### F3. `totalVariationDistance` junk value for infinite measures (LOW)
Location: `TotalVariation.lean:19`.
`sSup` of an unbounded real set is 0. Counterexample (compiled): `totalVariationDistance volume 0 = 0` on `ℝ`, even though the true value is infinite. For finite measures the set is bounded, so there is no junk.
Impact: every theorem that uses it assumes probability measures, so the junk is unreachable there. The def is unusable for σ-finite non-finite measures.
Fix: none, or state in the docstring that it is meaningful for finite measures only.

### F4. klDiv bridge edge cases (no defect; recorded for completeness)
- `ν` not absolutely continuous with respect to `μ`: `klDiv ν μ = ⊤`. The bridge theorems require `hAC` (or derive it from `klDiv ≠ ⊤`) and never claim an equality in this case. Hand check: for `ν ⊥ μ`, `rnDeriv = 0` a.e. and `Ent μ 0 = 0` while `klDiv = ⊤`, so a hypothesis-free "klDiv = ofReal Ent" would be false. The port does not state it.
- `ν ≪ μ` with `h log h` not integrable: `klDiv = ⊤` and Ent is junk. The theorem `klDiv_ne_top_iff_integrable_rnDeriv_mul_log` states the exact iff. `klDiv_eq_ofReal_Ent_rnDeriv` takes integrability as an input, and `toReal_klDiv_eq_Ent_rnDeriv` takes `klDiv ≠ ⊤`.
- `klDiv_withDensity_eq_ofReal_integral` needs `hnorm : ∫ f = 1` and the integrability of `f log f`, so `ν` is a probability measure by construction. This matches the source.
- Pinsker handles `klDiv = ⊤` with a separate `ENNReal` form (`totalVariationDistance_sq_le_klDiv`).

### F5. `AxiomCheck.lean` covers only part of the public API (INFO)
`Divergences/AxiomCheck.lean` prints 43 names; 138 public constants exist. The unlisted ones are `Ent_prod_decomposition` helpers, `Coupling.*`, `Gelbrich.*`, `varentropy_eq_top_iff` and others. The full check is now scripted in `Audit/DivergencesAxioms.lean` and passes. Fix: optionally replace the list in `AxiomCheck.lean` with the `#audit_divergences` command.

### F6. Minor (cosmetic)
- `squareEntropy` is an `abbrev` of `Ent μ (f^2)`. This is reducible, so `simp` can unfold it to `Ent`. It is harmless and intended.
- `Wasserstein.lean` works over `PseudoEMetricSpace` plus a bare `MeasurableSpace` (no `BorelSpace`). `edist^2` may then be non-measurable and `∫⁻` is the outer integral. This is identical to the CR source and all lemmas still hold; the Borel-space theorems add `BorelSpace` where they need it.
- `CompactDuality.lean`: the `PseudoMetrizableSpace` instance arguments on the main theorem are redundant.

## Not checked
- The non-vacuity of `wassersteinSq_elliptic`'s hypotheses (rotation-invariant `η` with identity covariance, i.e. a standard Gaussian) was not proven in Lean here; the source repo presumably has that.
- The Salez constants (equation (10), arXiv 2501.01304) were not compared with the paper online.
- The hypotheses of the ported theorems were compared by diff against CR for TotalVariation, Pinsker, Varentropy, KLScalar, KLVariational, WeakDuality and CompactDuality, and by hand against GP for entropy and tensorization. Gelbrich vs CF was compared by hand for statements only, not proofs.
