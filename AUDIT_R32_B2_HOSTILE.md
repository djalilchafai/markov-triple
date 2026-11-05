# Audit R32 Stream B2 (hostile): pointwise reverse Poincare

Verdict: **ACCEPT**

Audited: implementation branch worktree-agent-ae41fb863f59605c0 (freeze 56b9266, proofs 9e95902), merged on top of main e758c1a.

## Checks
1. `lake build` (full, 9600 jobs): success; log has 0 warnings, 0 errors, no `sorry`.
2. `grep` for sorry/set_option/native_decide/axiom in `Stochastic/R32B2/*.lean`: none (only `#print axioms` lines). `AxiomCheckR32B2.lean` is imported in `MarkovTriple.lean`; all 5 declarations (`pos_detect_L2`, `sqrt_form`, `weak_mono`, `reverse_integrated`, `reverse_poincare_pointwise`) depend only on propext, Classical.choice, Quot.sound. `scripts/check_frozen.py`: OK.
3. Git: freeze commit 56b9266 contains only `STATEMENTS_R32_B2.md` and the manifest entry. `git diff main -- frozen-manifest.json` is exactly one added entry. The only later change to the statements file is an appended Status section (the statement text is byte-identical to the freeze), with the entry re-hashed (39933f.. -> 1d113e..), as the process allows. Other touched files: MarkovTriple.lean (4 imports), GAPS.md, ERRATA.md; no frozen/fenced file edited.
4. Soundness.
   * `pos_detect_L2`: not circular. Uses the `DiffusionTriple` fields `dense` (D2) and `comp_mem` and dominated convergence only; hypotheses non-vacuous (g ranges over nonneg test functions; u in L2). Remark: D2 density is a structure FIELD, so for an abstract triple it is assumed as part of the definition of `DiffusionTriple` (this is BGL's definition), and each library instance discharges it; the theorem itself does not assume more than the structure.
   * `sqrt_form`, `weak_mono`, `reverse_integrated`: proofs read in full; they use only `strong_mono`/`strongInterpolation`/`theta_hasDerivAt`/`Pt_bdd` (R31U) under `hCD : CD 0 ∞` and finite mu, `jensen_sq`, and self-adjointness of the semigroup (`selfadj_test`). They do NOT use `reverse_poincare_sup` or any C-bounded extra hypothesis.
   * `reverse_poincare_pointwise`: `T.Pt t f` is a chosen A-representative with `Pt_ae` : semigroup class a.e. equal to it, so `P_t(f*f)` is `Pt t (f*f)`, the genuine semigroup applied to the class of f*f (f*f in A0 by `mul_mem`). `ΓA` is the library carre du champ on A defined by the formula (1/2)(L(f g) - f Lg - g Lf); it is class-invariant (`ΓA_congr_A`) so not a junk value for `Pt t f ∈ A`. Final step uses ordinary F2 (`pos_detect`) on an A element. The proof is a faithful BGL interpolation argument.
   * Non-vacuity: I checked in a scratch file (not committed) that `ouFull` (Gaussian, mu a probability measure) satisfies `CD 0 ∞` (from `ouFull_CD` plus `ΓA_nonneg`) and that `reverse_poincare_pointwise ouFull cd0 f t ht` typechecks. 
   * The hypothesis `0 < t` is unused (`have _ := ht`); disclosed in Status, ERRATA R32-B2-2.
5. Honesty: docs claim only CD(0,∞) with finite mu on a generic FullTriple; explicitly list rho<0, 1-D gibbsFull, non-finite mu, and `rd_kernel_ac` extension as NOT done; IsFellerC0 untouched. GAPS annotation of the old OPEN line is by annotation, not deletion.

## Findings
* LOW (L1): the library contains no instantiated corollary of `reverse_poincare_pointwise` (e.g. for `ouFull`/`gaussRdFull`, which have CD 1 ∞ and need the trivial weakening to CD 0 ∞). Non-vacuity is therefore shown only by my scratch check, not in-tree. Doc-level; not a soundness issue.
* INFO (I1): D2 density is part of the `DiffusionTriple` structure (assumed per instance, proved per instance), not proved from scratch in general; this is the expected reading.
* INFO (I2): `0 < t` unused (disclosed).
* INFO (I3): the Status section sits in a file whose manifest hash was refreshed after the freeze; statement text unchanged.

No unsound or misleading claims found.
