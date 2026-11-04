# AUDIT R23-G2 (hostile): `goFull` over `goDiff`, F10 as hypothesis

Target: `MarkovTriple/BGL/Instances/GegenbauerOpen/Full/{Defs,PreFull,RegLocal,Sem,NotL2,Ergodic,Curv,Main,AxiomCheckR23G2}.lean`
and `STATEMENTS_R23_G2.md` (implementation commit 2307284, on main dc4119a). Verdict: **ACCEPT** (0 HIGH, 0 MEDIUM, 2 LOW).

## Plain statement of what is proved
`goFull : goDiff.ESAProp -> FullTriple Real` is **conditional**: nothing in the repository proves `goDiff.ESAProp`
(stream G1's `go_esaProp` is not in this tree).  Everything else (F1-F9, S10, CD, non-completeness) is unconditional.

## Verified
1. **Genuine `FullTriple`.**  `Main.lean:34-49` fills every field of the frozen `FullTriple` (Frozen/FullTriple.lean:26-74) with
   proved terms.  F3/F6 are the library's own fields (`A_comp`, `diffusion_Γ_A`, `diffusion_L_A`, quantified over all smooth psi and
   all tuples in `goA`); `goPreFull : PreFull goDiff goA` is the library's `PreFull` (Gibbs/FunctPreFull.lean:27), not re-encoded.
   `goA` (Defs.lean:17-21) is a `Subalgebra` (contains constants, closed under + and *); `L f ∈ goA` is proved (`go_L_mem_A`).
2. **`hF10` use** (grep over `Full/*.lean`): exactly `Main.lean:31` (S11 `conservative`, via `conservative_of_esa`) and `Main.lean:49`
   (`esa := hF10`); the other occurrences are binders/docs.  `go_F8`, `go_ergodic`, `go_reg_*`, `go_not_integrable_sq`, `goPreFull`, `go_A_comp`,
   `go_diffusion_L_A`, `goA_CD`, `go_not_complete` take no `hF10` argument (so cannot depend on it), and `#print axioms` for all of them
   and for `goFull`, `goFull_CD`, `goFull_CD'`, `goFull_not_complete` gives only `propext, Classical.choice, Quot.sound`.
3. **CD** is the library `FullTriple.CD` (Frozen/CD.lean:20: `1 ≤ n ∧ ∀ f ∈ T.A, ∀ᵐ ...`); `goFull_CD'` (Main.lean:55) gives it for all `f ∈ goA`,
   `ρ ≤ 3`, `4 ≤ n`, using the ae-set `(-1,1)` (`ae_go`) and locality of `L, ΓA, Γ₂` (Curv.lean:47-56).  `(3,4)` = `(n-1,n)` for `n = 2λ+1 = 4`, matching S^4.
   `goFull_not_complete` (Main.lean:65-67) is verbatim `¬ (goFull hF10).toDiffusionTriple.IsComplete` (the argument `hF10` is unused in the proof but needed to form the term).
4. **Consistency of `hF10` with the rest.**  Mathematically the object is the zonal sector of the punctured sphere S^4 minus two poles with
   `C_c^∞` as test algebra: Δ is essentially self-adjoint on `C_c^∞(S^n \ pt)` iff `n ≥ 4`, so F10 holds (both endpoints limit-point; indeed
   `go_not_integrable_sq` is the Weyl alternative for `Lu=0`), F8 (interior smoothing), F9, F2 etc. hold, ergodic and conservative hold, CD(3,4) holds, and
   it is not complete (finite distance to the poles, R22 `go_not_complete`).  I see no logical reason for inconsistency; F10 plus F8/S10 do not interact
   (S10 is proved without F10).
5. **Regularity maths, by hand.**  `L = (1-x²)∂² - 4x∂`, weight `(1-x²)`: `((1-x²)² U')' = (1-x²)((1-x²)U'' - 4xU') = (1-x²) L U`, so the weak
   equation gives `(1-x²)² U' = c + ∫_0^x (1-y²) h`, exactly `go_reg_C1`'s conclusion (RegLocal.lean:425-437); regularity gain follows by induction
   (`go_reg_gain`), and `go_F8` glues `C^n` representatives on the open set via `Measure.eqOn_open_of_ae_eq` (Sem.lean:103-122) and `P_t = R^{n+1} ψ(R)`.
   `go_not_integrable_sq`: `c>0 ⇒ U' = c/(1-x²)² ≥ c/(4(1-x)²)` since `(1-x²)² ≤ 4(1-x)²` on `[0,1)`, so `U ≥ c/(4(1-x)) + const ≥ c/(8(1-x))`
   near 1, and `(1-x²)U² ≥ (1-x)(c/8)²(1-x)^{-2} = C/(1-x)`, not integrable.  The exponent is right (NotL2.lean:63-130).  `go_ergodic` needs only this:
   `u ∈ D(L)`, `Lu=0` ⇒ weak equation with `h=0` (`go_weak_of_generator_zero`, symmetry of generator against `a ∈ 𝒜₀ ⊂ D`), `u ∈ L² ⇒ c = 0 ⇒ U'=0 ⇒ U` constant
   on the connected `(-1,1)`.  One endpoint suffices because `c` is a single constant.
6. **Hygiene.**  `lake build ...Full.AxiomCheckR23G2` (all 9 modules): 0 errors, 0 warnings; no `sorry`, `set_option`, `axiom`, `native_decide` in `Full/*.lean`.
   `python3 scripts/check_frozen.py`: OK; diff vs dc4119a = 10 new files under `Full/` plus one `proposed` entry for `STATEMENTS_R23_G2.md` in `frozen-manifest.json`;
   no lakefile/manifest/toolchain/fenced file touched.

## The question about `goFull go_esaProp` (non-complete, CD(3,4)) vs. library theorems
* `FullTriple.mem_domain_of_Γ₂_direct` (ConverseDirect.lean:295) and `memLp_L_of_Γ₂` (:230) take `hC : IsComplete`; `goFull_not_complete` falsifies it, so no
  contradiction.  Likewise `conservative_of_complete`, `tendsto_Pt_complete`, `Finite.lean:116/214`, `JensenGrad.lean:84`, `FunctESA/FunctCutoff` all take completeness.
* `FullTriple.mem_domain_of_Γ₂` (Converse.lean:429) assumes `Core2` (`𝒜₀` core for L²).  For this example `Core2` is mathematically **false** (L² is ESA on
  `C_c^∞(R^n \ 0)` only for `n ≥ 8`; here `n = 4`), so the theorem is not applicable; I also checked heuristically that the conclusion itself survives for
  `f = r^s` (`Γ₂ ∈ L¹` forces `s > 0` hence `Lf ∈ L²`).  No counterexample to a stated theorem.
* The Extension theorems (`gamma_limits`, `cauchy_G1_K1`, `dist_G1_le`, gradient bounds) use `CD` through `𝒜₀` and F10 only; they are true on S^4 minus poles.
* Side note: `goFull go_esaProp` would be (if `go_esaProp` lands) a model of F1-F10 + CD(3,4) with `Core2` false, i.e. evidence that `Core2` is not derivable
  from F1-F10 (the R15 ERRATA question); this is an observation, not a bug.

## Findings
* LOW-1: `STATEMENTS_R23_G2.md`, "Consequence" paragraph: "that check against its conclusion is not done here" is now settled by this audit (completeness hypothesis of
  `mem_domain_of_Γ₂_direct` is false for `goFull`, hence nothing to refute; `mem_domain_of_Γ₂` needs `Core2`, false here).  No action required for correctness.
* LOW-2: `goFull_not_complete` and `goFull_CD(')` carry the unused/necessary-for-typing hypothesis `hF10`; once `go_esaProp` exists, unconditional versions
  `goFull go_esaProp` apply.  The "(DIFFERENCE FROM BGL) 1." doc is accurate (λ=3/2 only, `C_c^∞` instead of polynomials).
* No HIGH or MEDIUM findings.  The statement text matches the Lean (checked `goFull`, `goA`, CD, non-completeness).

## Caveat
Conditional on F10 (not proved anywhere in this tree).  Non-completeness is inherited from the R22 `go_not_complete` (audited in AUDIT_R22_E2_HOSTILE.md).
