# Round 15 gap closure: self-attack (author's audit, before the independent audit)

Targets: `Theory/Extension/STATEMENTS_R15_Gaps.md` (fixed before the proofs; no erratum was needed: the final Lean statements are
those listed there, plus the auxiliary lemmas `jL_smul/jL_lin/jE_smul/jE_lin`, `GraphConv.lin`, `FormConv.lin`, `coe_lin`,
`HH_lin_*`, `GG2_lin_left`, `GG_lin_left`, `hessE_cls_ae`, which are helpers and change no statement).

## 1. Vacuity / satisfiability
* Hypotheses are only `T : FullTriple E` and `hCD : T.CD ρ n` (for `gammaE`: none).  `FullTriple` and `CD` are inhabited (compact
  instances, sphere, OU); no extra hypothesis was added.  `hessE_cls`, `gamma2E_cls` have concrete test inputs (any `a ∈ 𝒜₀`),
  so the identification statements are not about an empty domain.  `Γ₂_ext_eq_gamma2E` needs `f ∈ 𝒜`, `MemLp f 2`, `[f] ∈ 𝒟(L)`:
  satisfiable (e.g. `f ∈ 𝒜₀`, using `cls_mem_generator_domain`).
* Linearity statements take the target element as a parameter with an equation `w = u + c • u'`; they are not vacuous because `w`
  is arbitrary with its own membership proof, and the equation is satisfiable by `w := u + c•u'` (domain is a submodule).
  They are not circular: the proofs pass through sequences, not through the statements.
* The bounds are not trivial: `C` in `hessE_bound` is the `C_h` of `HH_bound` (depends on `‖Γ h‖_∞`), the `Γ₂` constant is the
  explicit `2(1+|ρ|)+4|ρ|`, the one for `gammaE` is `1`.

## 2. `Classical.choose`
`hessE`, `gamma2E`, `gammaE` are `Classical.choose` of the existence theorems.  In the new code, `choose` is touched only through
the specification theorems `hessE_tendsto`, `gamma2E_tendsto`, `gammaE_tendsto` (and `tendsto_nhds_unique` to compare limits).
No proof unfolds the definitions.

## 3. Junk values, a.e. vs everywhere, norms
* All equalities in `Lp` are genuine equalities of `Lp` elements (hence a.e. as functions); `gammaE_cs`, `gammaE_self_nonneg`,
  `Γ₂_ext_eq_gamma2E`, `hessE_cls_ae` are stated a.e. with explicit coercions to functions.  No everywhere-statement is claimed.
* The norm on `Lp ℝ 2 × Lp ℝ 2` in `hessE_bound`/`gamma2E_bound` is Mathlib's sup norm, equivalent to the graph norm of the book
  (`graphSq ≤ 2‖jL‖²`); the book's boundedness is up to constants, so the sup norm is a legitimate form of the statement.
  The norm on `𝒟(ℰ)` is the Hilbert norm of `KE` through `qEquiv.symm` (E3 of STATEMENTS_R14: equivalent to `(‖·‖₂²+ℰ)^{1/2}`);
  `norm_jE_sq` identifies it on `𝒜₀` with that expression.  There is NO new lemma identifying `‖qEquiv.symm g‖²` with `‖g‖₂² + ℰ(g)` for
  general `g ∈ 𝒟(ℰ)` (it follows by continuity; not needed).
* Convergence statements (2): "`g_ℓ → g` in `𝒟(ℰ)`" is stated in `KE` (norm of the Hilbert space), "`f_ℓ → f` in `𝒟(L)`" as convergence
  of `(f_ℓ, L f_ℓ)` in `L² × L²`.  Both are the book's topologies.  The index is an arbitrary filter (sequences are a special case).
* Total functions: `hessE` is meaningful only with its membership proofs `hu : u ∈ 𝒟(L)`; all statements carry them.  `HH`
  involves `Hess` (a total function) only on `𝒜₀` where all terms are in `𝒜`.
* Scalar `c : ℝ`; `smul` on `Lp` is the standard one (`Lp.coeFn_smul` used in `𝒜₀`-level lemmas).

## 4. Deviations from the book (routine)
* The book's "bounded bilinear operator" is proved as: linearity in each slot (scalar combos) + the estimate; continuity is a
  consequence (second/third statements of (v) are derived from them via `hessE_lin_*` and `hessE_bound`, not by a diagonal argument:
  the book's diagonal argument is the proof that the extension is well defined, which is `bil_spec`, used since round 14).
* Cauchy–Schwarz for `gammaE`: the book quotes it from Prop. 3.1.5 for the closure; we derive it by passing to a.e.-convergent
  subsequences from the pointwise `ΓA` Cauchy–Schwarz on `𝒜₀` (same idea as in the book's closure argument).
* `gamma2E_lin_right` is derived from the left slot and `gamma2E_comm` (symmetry of `Γ₂` on `𝒜₀`, `Γ₂_comm`).

## 5. Not done
* 3.3.17 converse (T3), as before.  Not claimed here: continuity of `H` jointly in `(f,g)` (follows from bound + bilinearity, not stated);
  `L²`-version of (v) 2nd/3rd statements; `gamma2E` continuity in graph norm as a separate statement (it is `gamma2E_bound` + bilinearity).

## 6. Attack surface for the independent audit
1. `GraphConv.lin`/`FormConv.lin`: the dependent-type handling of `⟨w,hw⟩ = ⟨u,hu⟩ + c•⟨u',hu'⟩` and `erw [map_add, map_smul]` on `qEquiv.symm`
   (the `erw` is there because `Q` and `T.formDomain` are defeq but not syntactically equal); check that `FormConv` is the right topology.
2. The sup norm on `L² × L²` and the use of `‖qEquiv.symm g‖` in `hessE_bound`: is the stated estimate the book's "bounded"?
3. `hessE_tendsto_left`: sign/`1 • ` bookkeeping when writing `f_i = f₀ + (f_i - f₀)`; the subtype `↥generator.domain` is used for `f`; check
   the hypothesis is graph convergence in the full `𝒟(L)` (not only along `𝒜₀`).
4. `hessE_cls` relies on `DiffusionTriple.generator_cls` (graph of the generator on `𝒜₀` is `L`): verify `GraphConv` constant sequence.
5. `Γ₂_ext_eq_gamma2E`: it is `Γ₂_ext_eq` with `γ₂ := gamma2E u u` and `GG2_self`; the content of `GG2_self` is `GG2_ae`, `G2cls_ae` (two a.e. identifications).
6. `gammaE_cs` nested subsequences: the third a.e. statement is discarded with `-`; check that `a3` (the `b`-diagonal along `φ ∘ ψ`) is really
   the `s3` subsequence on the SAME index `φ (ψ m)` as `a1, a2` composed with `ψ` (used `comp hψ.tendsto_atTop`).
7. Documentation erratum E5: check that the superseding table in `STATEMENTS_R14.md` agrees with the code (names) and that no statement was altered.
