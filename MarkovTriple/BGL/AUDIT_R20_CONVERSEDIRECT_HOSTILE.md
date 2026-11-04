# Hostile audit, Round 20 Stream D3 (direct converse of BGL Prop 3.3.17), commit 4e10305

Verdict: the unconditional-of-Core2 claim HOLDS. No mathematical or Lean defect found. Only documentation findings.

## Method
Built ConverseDirect, ConverseDirectInst, ConverseDirectAxioms (Mathlib not rebuilt; build copied, packages symlinked).
Throwaway meta-probe (deleted) computed the transitive closure of `MarkovTriple.*` constants used by each theorem and
searched for names containing `Core2`, `CoreCut`, `GrowHess`; control: `FullTriple.mem_domain_of_Γ₂` correctly reports `FullTriple.Core2`.

## Findings (severity-ranked)

### No HIGH, no MEDIUM mathematical/Lean findings.

### M-doc-1 (MEDIUM, docs): earlier errata not reconciled
ERRATA R15-1 (HIGH, "The unconditional converse is OPEN"), R17-2, R19-M1 ("net result"), and GAPS lines ~80, ~152 are NOT
annotated; only a new section R20-D3-1..3 was appended. A reader of R15-1 still sees "open". Needed: a cross-reference
"see R20-D3-1: unconditional of Core2 under completeness" in R15-1/R17-2/R19-M1/GAPS (not done; frozen-adjacent text, so only
append-style notes). R20-D3-1 itself states the right scope but R15-1's wording "ESA does not give this by abstract operator theory"
is still consistent (completeness + CD is the extra input), so no falsity, only staleness.

### L-doc-2 (LOW): "unconditional" wording
Docs (GAPS "PROVED unconditionally in the abstract framework", ERRATA R20-D3-2 "unconditional for every EllData/RiemData with Curv ρ")
are accurate only modulo completeness (a hypothesis) and Curv; GAPS adds the caveat for abstract incomplete triples, ERRATA does not.
Incomparability with the Core2 result is stated correctly everywhere (no overclaim that it supersedes).

### L-doc-3 (LOW): unverified side claim
AUDIT/inst docs say the result covers ℝ^d Gibbs "via GibbsRdData.toEll ... without GrowHess3". The same document says this reduction
is not re-proved. Not compiled; should be phrased as a hope. `hypRiem` satisfies `Curv 1` (HypUnconditional.lean), so the hyperbolic
plane claim is fine but is not itself instantiated in ConverseDirectInst (generic `riem_..._direct` only).

### I-1 (INFO): `n` irrelevant
CD(ρ,n) is used only through `Γ₂ ≥ ρΓ` (K_nonneg) and Hessian CS; fine for any n ≥ 1. Ergodicity unused: correct.

## Checks
1. Statements: `#check` with pp.explicit of `mem_domain_of_Γ₂_direct`: hypotheses are exactly `IsComplete`, `CD ρ n`, `f ∈ A`,
   `MemLp f 2`, `Integrable (G f f)`, `Integrable (Γ₂ f f)`; conclusion text identical to `mem_domain_of_Γ₂` (only `Core2` replaced by
   `IsComplete`). Transitive dependency closure of the direct theorem, memLp_L_of_Γ₂, cutoff_bound, hessCS, cutoff_Γ₂_identity,
   mem_domain_of_ESA and all five applications contains NO Core2/CoreCut/GrowHess name. No circularity.
2. Satisfiability: `IsComplete` = ∃ ζ_k ∈ 𝒜₀, ζ_k ≥ 0 a.e., monotone, ζ_k → 1 a.e., Γζ_k ≤ (k+1)^-2 (Def 3.3.9); it provides all cut-off
   properties used (≤ 1 derived from monotone + limit; Γ ≤ 1). `CD ρ n` is `1 ≤ n ∧ ∀ f ∈ 𝒜, ρΓ f + n⁻¹ (Lf)² ≤ Γ₂ f` a.e., for all of 𝒜,
   Γ₂ f := ½LΓf − Γ(f,Lf) via `Γ₂_eq`; sign of ρ irrelevant. Instances exist (OU, circle, Lebesgue, EllData, RiemData) with
   axiom-clean completeness proofs, so not vacuous. OU f=id: id ∈ C^∞ = 𝒜, not compactly supported so ∉ 𝒜₀, Γ=Γ₂=1 ∈ L¹(γ),
   id ∈ L²(γ); mathematically [x] ∈ 𝒟(L̄), L̄[x] = [−x] is true (first Hermite eigenfunction, eigenvalue −1). Conclusion matches.
3. Hand math: identity re-derived. ∫χ²(Lf)² = ∫(χ²Lf)Lf = −∫Γ(f,χ²Lf) (F7, χ²Lf ∈ 𝒜₀ by ideal) = −∫χ²Γ(f,Lf) − 2∫χLfΓ(f,χ);
   −Γ(f,Lf) = Γ₂ − ½LΓf; ∫χ²LΓf = −2∫χΓ(Γf,χ) (F7 for p = Γf ∈ 𝒜 against χ² ∈ 𝒜₀). Sum gives the stated identity, signs correct.
   Integrability: every integrand is χ²·u or χ·(𝒜-element)·Γ(.,χ) with χ ∈ 𝒜₀, hence in 𝒜₀ by F1, hence in L¹ (A₀ ⊂ L^p): no integrability
   of f assumed or smuggled; Lean uses `intA₀`/`mulA₀`. hessCS: Hess f χ f = ½Γ(χ,Γf) (checked from the definition, G_comm), so (3.3.7)
   H(f)(χ,f)² ≤ K Γχ Γf gives factor 4 correctly (matches Riemannian |Hess f(∇χ,∇f)| ≤ |Hess f||∇χ||∇f|, |Hess f|² ≤ Γ₂−ρΓ).
   cutoff_bound constants re-derived by hand: X ≤ ∫χ²Γ₂ + ∫(K+Γf) + ½X + 2∫Γf and χ²Γ₂ ≤ K + |ρ|Γf, absorbing ½X (finite since integrable)
   gives X ≤ 4∫K + 2(|ρ|+3)∫Γf: matches. Fatou: ζ_k → 1 a.e. so liminf ζ_k²(Lf)² = (Lf)² a.e., ∫(Lf)² ≤ liminf ≤ C: correct.
   Maximal domain: F10 (core form) gives g = lim a_n, La_n → L̄g; ⟨f,L̄g⟩ = lim⟨f,La_n⟩ = lim⟨Lf,a_n⟩ (F7 symmetry f ∈ 𝒜, a_n ∈ 𝒜₀) = ⟨Lf,g⟩,
   so f ∈ 𝒟(L̄*) = 𝒟(L̄) and L̄f = Lf; uses only F7 and F10 (generator self-adjoint). Conclusion `=ᵐ L f` correct.
4. Axioms: all 12 `#print axioms` = propext, Classical.choice, Quot.sound. No sorry, no set_option in the three files. 0 warnings in the build.
5. Docs: `## DIFFERENCE FROM BGL` is present in STATEMENTS, AUDIT, ConverseDirect (module doc), Inst, Axioms, GAPS entry; accurate. See M-doc-1, L-doc-2/3.
6. `python3 scripts/check_frozen.py`: OK. `git diff main..4e10305` on frozen-manifest.json: 5 added lines (one `proposed` entry), no removed
   line; no frozen/fenced file modified (MarkovTriple.lean imports added only).
