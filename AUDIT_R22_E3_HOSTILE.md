# Hostile audit, Round 22 stream E3 (implementation commit 69dcdf9, merged into this audit commit)

Verdict: ACCEPT. No HIGH or MEDIUM finding. Two LOW doc wording points, one LOW scope remark.
Method: merged the implementation, built `MarkovTriple.Stochastic.R22.AxiomCheck` (build OK, 0 warnings, no `sorry`/`set_option`/`axiom`
in `R22/*.lean`), read every line of the four Lean files and of `STATEMENTS_R22_E3.md`.

## Verified
* Axioms: `#print axioms` on `secondCountableOnePoint`, `Uequiv`, `exists_kernel_of_posContraction_noncompact`, `ncKernelRep`,
  `ncKernelRep_subInvariant`, `ncKernelRep_C0`, `nc_exists_exact_ck`, `c0_dense`, `exists_kernelRepresentation_not_exact_ck`:
  only propext, Classical.choice, Quot.sound.
* `scripts/check_frozen.py`: OK; the only manifest change is the added `STATEMENTS_R22_E3.md` (`proposed`); changed files are exactly
  the 4 Lean files, the statements file and the manifest; no fenced file edited, lakefile/manifest/toolchain untouched.
* (1) Faithfulness of the obstruction. `KernelRepresentation` (`Stochastic/KernelRep.lean:37-45`) has fields `κ`, `subMarkov`, `rep`
  (a.e. representation of `P_t` on bounded measurable `L²` functions, per `t`) and NO Chapman-Kolmogorov or continuity field.
  `badRep` (`Obstruction.lean:48-65`) fills all three genuinely: `subMarkov` is proved case by case, `rep` by `badKernel2_ae`
  (`γ{0}=0` via `gaussianReal_absolutelyContinuous`), and `badRep_subInvariant` gives `γ.bind κ_t ≤ γ` for every `t`. The failure at
  `s=t=1, x=0` is checked: `badKernel2 0 = dirac 5` vs the Mehler Gaussian of variance `ouVar 2 ≠ 0`, which gives `{5}` mass 0.
  No weakened structure; the structure is the library's, unmodified.
* The kernels are indexed by `t : ℝ≥0` and `K.κ (s+t) x ≠ (K.κ t ∘ₖ K.κ s) x` is the exact (pointwise) CK negation.
* Claim (i) "nothing new" is accurate: `MarkovProcessSemigroupData` (`MarkovProcessInterface.lean:53-63`) requires `kernel_add : ∀ s t`
  (exact CK for all real times) and `kernel_zero`; `ouMarkovProcessBridge`, `circleMarkovProcessBridge`, `fellerMarkovProcessBridge`,
  `sphereMarkovProcessBridge` exist.
* (iii) `exists_kernel_of_posContraction_noncompact` (`NonCompact.lean:129-135`): conclusion quantifies over every
  `f : C₀(X,ℝ)` and every `u : Lp ℝ 2 μ` with `u =ᵐ f`. `C₀` is `ZeroAtInftyContinuousMap` (`open scoped ZeroAtInfty`). Hypotheses
  (`hpos`, `hle`, `hmass`) are the R15-style ones; `IsFiniteMeasure μ` is used (instance `IsFiniteMeasure (muP μ)`, `1 ∈ L²`, density
  of `C_c` in `L²` via `exists_hasCompactSupport_eLpNorm_sub_le`, which needs finite/regular measure; `c0_dense` is stated for finite
  `T.μ`). Claims about infinite `μ` (open) are honest.
* One-point compactification argument: `secondCountableOnePoint` (`OnePointCountable.lean`) is a correct explicit countable basis
  (images of a basis of `X` plus complements of a compact exhaustion); `ncMeas` is the Borel structure, `μ.map (↑)` gives no mass to
  `∞` through `MeasurableEmbedding` (`Uequiv` is surjective via `Function.extend`), `extC0` is continuous by
  `OnePoint.continuous_iff` and `coclosedCompact = cocompact`; the restricted kernel is `comap (↑)`, sub-invariance transferred through
  `bind_le_of_integral_le` on `X⁺` and `hι.comap_apply`. No gap found. T2/locally compact of `X` give compact T2 second countable
  (hence metrizable) `OnePoint X`, which is what the compact theorem needs (the build confirms).
* Non-vacuity: `AxiomCheck.lean:18-19` `ncKernelRep ouDiff : KernelRepresentation ouDiff` is typechecked by the library (OU on `ℝ`,
  `γ` finite); `ncKernelRep_subInvariant`, `nc_exists_exact_ck` are `rfl`-thin wrappers around library lemmas (no new content, but correct).

## Findings
* LOW-1 (doc, GAPS wording). The proposed GAPS line "Round 17 item (2) non-compact: closed for finite `μ`" overstates. `Theory/GAPS.md`
  line 213 item (2) reads "non-compact (locally compact σ-compact) Riesz-Markov-**Feller** extension". E3 proves only the Riesz-Markov
  (kernel representation) part, for FINITE `μ` and sub-Markov kernels; no Feller/`C₀`-Feller property, no non-compact bridge,
  no infinite `μ`. Suggested wording: "item (2): Riesz-Markov kernel representation closed for finite `μ`; Feller extension and
  infinite `μ` open; item (1) open, with the obstruction R22-E3-2".
* LOW-2 (doc, ERRATA R22-E3-1). "supersedes R17-4": the Stochastic-section row R17-4 (ERRATA.md line 186, "Non-compact extension (R16-2 (ii))
  not done in R17; remaining work in AUDIT_R17.md item 3") is accurately described, but R17-4 is an ambiguous id (many sections reuse it).
  Cite as "R17-4 of the Round 17 stochastic section (ERRATA.md:186) and `AUDIT_R17.md` item 3". Also say the route taken is the
  one-point-compactification alternative that item 3 mentioned, not the `C_{K_n}` Hahn-Banach redo (a)-(d); finite `μ` makes the
  weighted `L²(h²μ)` reduction unnecessary. "Locally compact sigma-compact Polish" in R17 equals the second-countable T2 case here.
* LOW-3 (scope, R22-E3-2). The obstruction is on the non-compact OU triple, whereas `rieszKernel` exists only on compact spaces and is one
  specific `Classical.choose`; the result says the library API (`KernelRepresentation`, sub-invariance) cannot imply exact CK, NOT that the
  actual `rieszKernel` fails CK. The files state this ("no bridge can be extracted from the API"); keep that phrasing. The same one-point
  trick would apply on a compact space but is not formalised. Also `rieszKernel_continuous` is a misleading name (a.e. representation only,
  `RieszRep.lean:148-151`), so the docstring's list of "defining properties" is fine.
* INFO. Proposed ERRATA R22-E3-3 (instance in a global `R22`-namespace instance): harmless; `OnePoint X` second countability is
  indeed absent from this Mathlib version (the instance builds without clashing).

No Lean file was edited by this audit.
