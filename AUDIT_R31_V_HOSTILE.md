# Hostile audit, Round 31 Stream V (F8 for the sphere)

Verdict: **ACCEPT** (scope is honest; nothing unconditional is claimed).

Checks performed
1. `lake build` (merge of worktree-agent-a487e04f319209911): success, 9582 jobs, no warning/error/sorry lines in the log.
2. No `sorry`/`set_option`/`native_decide`/`axiom` in F8.lean, Orth.lean, AxiomCheckR31V.lean (only `#print axioms` lines match). All 8 `#print axioms` outputs are `[propext, Classical.choice, Quot.sound]`. `scripts/check_frozen.py`: OK.
3. History: freeze commit 0f7223c touches exactly STATEMENTS_R31_V.md and frozen-manifest.json; the manifest diff vs main is only the one `proposed` entry for this file. Later commits 8b0a50b, f2e4957 are proof commits. Frozen theorem texts match delivered statements.
4. Soundness: `harm_orth` is a genuine integral of the product of restrictions against the normalised sphere measure `σ n` (`restr h x * restr h' x`), for `IsHarm k h`, `IsHarm k' h'`, `k ≠ k'` (non-vacuous; harmonic polynomials exist for every k). `lamS n k = k(k+n-2)` and `LS_restr_harm` gives `LS(restr h) = -k(k+n-2) restr h`, so lamS is the eigenvalue magnitude on S^{n-1} (Sph n lives in R^n). `LS_symm` derives from `ibp_sphere` + symmetry of ΓS (hypothesis `1 ≤ n`, `f,g ∈ A₀S`). `lamS_strictMono` needs n ≥ 2 and is correct (n=2: k²). `coeff_step`/`coeff_pow` are the expected identities; the iterate stays in `A₀S` (via `LS_mem`). 
5. Honesty: `SphereF8` and `sphereFull` remain explicitly conditional in STATEMENTS Status, GAPS and ERRATA R31-V-1.

Findings (severity ranked)
- LOW (doc): `sphereF8_iff` is `Iff.rfl` (definitional unfolding, plus `smoothCls` membership) and `sphereF8_zero` is trivial (`P_0 = id`). Docs call them "PROVED", accurate, but they carry no analytic content toward F8. Real content toward F8 is only `sphereF8_of_span` (linear extension of the R29 polynomial lemma) and the orthogonality/decay identities.
- LOW (doc): the GAPS entry states "no formal obstruction found" and size estimates ("several thousand lines", "1000+ lines each"). These are labelled as estimates/analysis, not theorems; the sentence "no formal obstruction found" means only absence of a found obstruction. Acceptable as worded; reader should not take them as proven feasibility.
- LOW (doc): GAPS claim "`2^k` from the mean value property on B(0,2) suffices" is a heuristic plan, not verified in Lean; also "coefficients of a smooth f decay faster than any power of λ_k" follows from coeff_pow only after Cauchy-Schwarz/Bessel-type bounds that are not formalised (coeff_pow gives the exact identity, not the decay bound itself). Wording "hence" is slightly strong.
- INFO: `harm_orth` etc. are inside the F8 route but do not discharge any hypothesis of `sphereFull`; nothing in the library depends on them.

No proof or statement changes made by this audit.
