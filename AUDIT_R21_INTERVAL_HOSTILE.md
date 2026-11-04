# AUDIT R21 -- interval triple ((0,1), Lebesgue, C_c^inf((0,1))), hostile audit

Target: `MarkovTriple/BGL/Instances/Interval/{Basic,Diffusion,NotComplete,NotESA,AxiomCheckR21}.lean`,
`STATEMENTS_R21_Interval.md` (implementation commit 464dcf1, merged into this branch).  Verdict: ACCEPT.
No finding above LOW.

## Findings

### HIGH
None.

### MEDIUM
None.

### LOW
* L1 (STATEMENTS, I6 and ERRATA row R21-4): the Gegenbauer limit-point/limit-circle computation is labelled
  "derived by hand, not cross-checked".  I cross-checked it independently (below): it is CORRECT.  The label can be
  upgraded from "unverified" to "verified by an independent hand computation".  No change of content needed.
* L2 (STATEMENTS, "Consistency with BGL"): "the book states the interval as the typical non-ESA example" is an
  unchecked claim about the book; I did not verify it (no book text in the repo).  Harmless, not used anywhere.
* L3 (STATEMENTS, R21-1): the phrase "`Γ₂ f = (f'')² ≥ (Lf)²/n`" is true but the real statement is the equality
  `Γ₂ f = (Lf)²` (so CD(ρ,n) for all ρ ≤ 0, n ≥ 1, i.e. even `n = 1`, the true dimension).  Cosmetic.
* L4 (STATEMENTS Data block): `ivDiff` is listed as `noncomputable def`; the source has `@[reducible] noncomputable def`.
  Cosmetic.
* L5 (scope, not an error): `IvCD` (pointwise, all `C^inf`) is not `FullTriple.CD`; the file says so openly
  (DIFFERENCE FROM BGL item 2, R21-3).  Since `Γ₂ = (f'')^2` is an identity, any reasonable extended algebra gives CD(0,1).
  `ivDiff_CD` is therefore a correct but cheap statement; do not cite it as "CD on a Markov triple" in the sense of Def. 3.3.x.

## What I verified

1. Build/hygiene.  `lake build MarkovTriple.BGL.Instances.Interval.AxiomCheckR21` succeeds; `lake env lean` on each of
   Basic, Diffusion, NotComplete, NotESA gives no output (0 warnings, 0 errors).  `grep` finds no `sorry` and no
   `set_option` in the Interval directory.  `#print axioms` of `ivA₀_dense, ivDiff, iv_ΓA, iv_Γ₂_eq, ivDiff_CD,
   abs_le_of_Γ, iv_not_complete, iv_exp_orth, iv_not_esaProp, iv_no_fullTriple`: only `propext, Classical.choice,
   Quot.sound`.  `scripts/check_frozen.py` prints OK.  `git diff 1214578..HEAD` touches only the 6 new Interval files and
   `frozen-manifest.json`, where the only change is one new `proposed` entry for `STATEMENTS_R21_Interval.md`.  No fenced
   file, lakefile, manifest of packages, or toolchain touched.
2. `ivDiff : DiffusionTriple ℝ` is a genuine, non-degenerate structure.  `μ = volume.restrict (Ioo 0 1)` is a probability
   measure (instance `isProb_ivμ`).  `ivA₀` is a `NonUnitalSubalgebra` with carrier
   `{f smooth, tsupport f ⊆ Ioo 0 1}`; it is nontrivial (contains `ivcut n`, with `0 ≤ ivcut ≤ 1`, `ivcut → 1` on `(0,1)`, monotone),
   so it is neither empty nor `{0}`; `dense` is the real theorem `ivA₀_dense` (all 1 ≤ p < ∞, proof via
   `MemLp.exist_eLpNorm_sub_le` plus cut-off with tail estimate `‖g‖∞ (4/(n+1))^{1/p}`); read line by line, it is sound.
   `Γ = f'g'`, `L = f''` reuse `Lebesgue.Gf/Lf`; `ibp`/`integral_L` transport from ℝ via `integral_iv`
   (functions in 𝒜₀ and their derivatives vanish off (0,1), so `∫ ∂ivμ = ∫ ∂volume`) -- correct.  All fields are proved,
   none by `trivial`/vacuity.  ℝ-vs-(0,1) mismatch is harmless: ae statements only see (0,1), and 𝒜₀-elements vanish outside.
3. Non-vacuity of the predicates.  `IsComplete` (Frozen/Complete.lean) is satisfiable: `gibbsDiff_isComplete`,
   `diff_isComplete`, `riemDiff_isComplete` exist in the library for ℝ^d-type triples, so it is not unsatisfiable by encoding.
   The encoding is exactly `∃ ζ_k ∈ 𝒜₀, ζ_k ≥ 0, increasing, → 1 ae, Γ(ζ_k) ≤ 1/(k+1)^2 ae`; `iv_not_complete` uses only
   membership, `→ 1` ae and the Γ bound (it ignores monotonicity/positivity, i.e. it proves a stronger statement).
   Mathematics: ζ ∈ C_c^∞(0,1), |ζ'| ≤ c  ⟹  |ζ(x)| ≤ c x (FTC from 0 where ζ=0), so ζ_k(x) ≤ x/(k+1) → 0 ≠ 1;
   the proof (`abs_le_of_Γ`) handles the ae-bound properly through `ae_restrict_iff'`.  The `(ae ivμ).NeBot` use is legitimate
   since ivμ ≠ 0.  `ESAProp` (Theory/ESAOne.lean) is F10 verbatim (core of the Friedrichs generator) and is satisfiable
   (it is a field of `FullTriple`, instantiated for Gibbs/Riemannian/compact triples), so `iv_not_esaProp` is not a
   vacuous consequence of an unsatisfiable predicate.  `iv_not_esaProp` proof logic: `u = exp|_(0,1)` ∈ L², nonzero,
   `∫ exp (f'' - f) = 0` for f ∈ 𝒜₀ (two IBPs, no boundary terms); `R u ∈ dom G`, `G R u = R u - u`; ESA would give
   `a_n → R u`, `L a_n → G R u`, hence `0 = ⟨u,(L-1)a_n⟩ → ⟨u, G R u - R u⟩ = -‖u‖^2`, contradiction.  Correct.
   `iv_no_fullTriple` follows by `h ▸ T.esaProp`.  Mathematically also standard: L = d²/dx² on C_c^∞(0,1) has deficiency
   indices (2,2), Friedrichs = Dirichlet, so not ESA.
4. `iv_Γ₂_eq`: Γ₂ f = ½ L Γ(f) - Γ(f,Lf) = ½ (f'^2)'' - f' f''' = (f'')^2.  Correct.  `ivDiff_CD`: ρ f'^2 + (1/n)(f'')^2 ≤ (f'')^2 for
   ρ ≤ 0, 1/n ∈ [0,1]; correct, including n = ∞ (`(⊤)⁻¹.toReal = 0`).
5. Claim "this example does NOT show completeness is needed inside the hypotheses of `FullTriple.mem_domain_of_Γ₂_direct`":
   ACCURATE.  That theorem (Theory/Extension/ConverseDirect.lean:295) takes a `FullTriple T` (hence F10) together with `hC : IsComplete` and
   `hCD : T.CD ρ n`.  The interval triple fails F10 independently of completeness (`iv_no_fullTriple`), so it lies outside the
   theorem's setting; it only shows that completeness does not follow from the bare `DiffusionTriple` axioms plus curvature
   (and `IvCD` is anyway not `FullTriple.CD`).  The docs state exactly this (Status, R21-2) -- no overclaim found.  The
   remark that a non-complete FullTriple is open (I6) is honest.
6. Gegenbauer independent verification.  Weight w = (1-x²)^{λ-1/2}; (w(1-x²)f')'/w = (1-x²)f'' - (2λ+1)x f' = L f,
   so L is symmetric in L²(w) with Γ(f) = (1-x²)f'².  Near x = 1, t = 1-x: L f ≈ 2t f_tt + (2λ+1) f_t.  L f = 0 has
   solutions 1 and f_t ∝ t^{-(λ+1/2)}, i.e. f ~ t^{1/2-λ} (log t if λ = 1/2).  Then |f|² w ~ t^{1-2λ} t^{λ-1/2} = t^{1/2-λ},
   integrable at 0 iff λ < 3/2 (the borderline λ = 3/2 gives t^{-1}, not integrable).  Thus the endpoints are limit-circle for
   λ < 3/2 (λ > -1/2 for w integrable) and limit-point iff λ ≥ 3/2; by Weyl's alternative, L on C_c^∞(-1,1) is ESA iff
   λ ≥ 3/2 (both endpoints are symmetric).  With n = 2λ+1 this is n ≥ 4, matching the classical fact that the
   (radial/zonal) Laplacian on S^n minus a point is ESA iff n ≥ 4.  CONCLUSION: the earlier conjecture "λ ≥ 1/2 gives ESA"
   was WRONG; ESA needs λ ≥ 3/2.  Non-completeness for all λ > -1/2: Γ-distance between ±1 is ∫ dx/√(1-x²) = π < ∞, so
   ζ_k ≤ (arcsin x + π/2)/(k+1) ≤ π/(k+1) → 0, contradicting ζ_k → 1 (same argument as I3).  The research-suggestion remark
   (for n ≥ 4 one generator, a complete and a non-complete presentation) is plausible and correctly flagged as a suggestion.
7. `DIFFERENCE FROM BGL` section: items 1-3 are accurate.  Item 3 ("no deviation in IsComplete or ESAProp") is true:
   both are used from the library as stated.  Item 2 (CD) is the one real deviation, openly declared.

## Proposed ERRATA rows R21-1..R21-4
All four are accurate as written (R21-4 is now also independently confirmed, see L1).  No change requested beyond the
cosmetic items L1-L4.
