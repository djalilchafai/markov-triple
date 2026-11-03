# AUDIT R17 SobSharp (hostile self-audit): sharp Sobolev embedding `k > m + d/2`

Files: `Instances/GibbsRd/SobSharp{ML2,Fourier,Hat,Bound,Weak,Wgt,Core,Main}.lean`, `EllRegSharp.lean`, `AxiomCheckR17SobSharp.lean`;
statements `Instances/GibbsRd/STATEMENTS_R17_SobSharp.md` (written first, registered `proposed` in `frozen-manifest.json`).

## 1. Statement faithfulness
* `sob_contDiff_rep_sharp (m k) (hk : d + 2*m < 2*k) (hf : HasSobL2 k f) : ∃ g, ContDiff ℝ (m : WithTop ℕ∞) g ∧ f =ᵐ[volume] g`.
  `d + 2m < 2k ⇔ k > m + d/2` (Folland Thm 9.17, Evans §5.6.3 Thm 6).  `HasSobL2` is the pre-existing definition (iterated
  weak derivatives of every word of length `≤ k`, each in `L²_loc`; weak derivative tested against `C_c^∞` with the corrected `ContDiff ℝ ∞`,
  see R16-Sob-E1).  The proof uses ONLY the pure-power words `(i,…,i)` plus `f ∈ L²_loc`; stronger hypothesis than needed is a harmless
  weakening of the theorem's strength not of its truth.  Conclusion `ContDiff ℝ (m : WithTop ℕ∞)` is `C^m` (finite `m`, no `ω` issue).
* `sob_contDiff_rep_sharp'` : `k = m + d/2 + 1` (nat division = `⌊d/2⌋ + 1`) satisfies `d + 2m < 2k` (omega).  Check: d=3,m=0: k=2 (3<4 ok);
  d=4,m=0: k=3 (4<6; note `k=2` would give `4<4` false, as it must: `H^2(ℝ^4) ⊄ C^0`).
* `smooth_of_weak_all_orders_sharp`: conclusion `ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)`, i.e. `C^∞`, NOT analytic; checked in the source (`∞` via `open scoped ContDiff`
  = `((⊤:ℕ∞):WithTop ℕ∞)`; the same spelling as existing `smooth_of_weak_all_orders`).
* `ellReg_sharp_order` / `ellReg_sharp`: same hypotheses as `EllData.EllReg`, chain length `n = m + d/2 + 1`; conclusion `C^m` representative of `x 0`
  `μ`-a.e.  `ellReg_of_sharp : E.EllReg` re-derives the existing definition (no change of `EllReg`, `ellReg`, downstream).

## 2. Vacuity / junk-value checks
* No hypothesis is contradictory: `HasSobL2 k f` is satisfied by every `f ∈ C_c^∞` (derivatives classical), e.g. `f = 0`; the weak-derivative test class is
  `ContDiff ℝ ∞` (non-trivial: `cutoff`, bumps), not `⊤ = ω`.
* Junk values: `∫` of non-integrable functions is `0` in Lean, which would make equalities vacuous.  Every use is guarded:
  `integral_sq_fourier_lft` (Plancherel) applies to Schwartz functions (`SchwartzMap.integral_norm_sq_fourier`, integrability `integrable_sq_hat`);
  `hat_energy` proves Integrable AND the identity; `wgt_hat_lintegral_le` is a `lintegral` inequality (no junk) converted to Integrable by
  `lintegral_ofReal_ne_top_iff_integrable`; `integral_sq_mol_le` assumes `MemLp G 2` AND `Integrable G`.
* `sob_core_sharp` needs `F` a.e. zero off a compact `K0`, which is what makes `F ∈ L¹ ∩ L²` (`memLp_of_locL2`, `integrable_of_locL2`); the
  localisation `local_rep_sharp` uses `cutoff R * f` (smooth, compactly supported) exactly as the old `local_rep`.
* Degenerate dimensions: `d = 0` is covered (`norm_pow_le` treats `d=0` separately; `EuclideanSpace ℝ (Fin 0)` is a point).  `k ≥ 1` follows from `d + 2m < 2k`.

## 3. Proof-route audit (what could silently go wrong)
* Euclidean transport: `lft F = (↑) ∘ F ∘ ofLp`; `integral_ofLp`, `integrable_lft`, `lft_mol` use Mathlib's measure-preserving `ofLp`/`toLp`.
  `lft_mol` is the identity `lft (F ⋆ ρ) = lft F ⋆[mul] lft ρ` (checked by Lean, not assumed), used for the convolution theorem
  `Real.fourier_mul_convolution_eq`, giving `|𝓕 (F⋆ρ_n)| ≤ |𝓕 F|` (`norm_hat_mol_le`).
* Fourier normalisation: Mathlib `𝓕 f ξ = ∫ e^{-2πi⟨x,ξ⟩} f x dx`, so `𝓕(∂_i f) = 2πi ξ_i 𝓕 f` (`fourier_lft_pd`), the weight is `(2π ξ_i)^{2k}`.  The constants
  are irrelevant for the statement (only finiteness is used).
* Pointwise inversion `F_n = 𝓕⁻ 𝓕 F_n` (`Continuous.fourierInv_fourier_eq`, `F_n` continuous, integrable, `𝓕 F_n` integrable by domination by `|𝓕 F|`), dominated convergence to
  `𝓕⁻ 𝓕 F`, and `F_n → F` a.e. (`ae_tendsto_mol`, Lebesgue differentiation): hence `F = 𝓕⁻ 𝓕 F` a.e. with `𝓕⁻𝓕F ∈ C^m` (`contDiff_fourier`, needs `(1+|ξ|)^m 𝓕F ∈ L¹`).
* The `L¹` hypothesis `2(k-m) > d` enters ONLY through `integrable_one_add_norm` with `r = 2(k-m)` and `finrank = d` (`finrank_euclideanSpace_fin`).  The inequality
  `(1+|ξ|)^{2k} ≤ C (1 + Σ (2πξ_i)^{2k})` (`one_add_norm_pow_le_wgt`) is where isotropy is recovered from pure powers.
* Sanity: the hypotheses are exactly as strong as classical `H^k`, so no spurious strengthening of the conclusion: conclusion is classical `C^m` for `k>m+d/2`.

## 4. Axioms / hygiene
`#print axioms` (`AxiomCheckR17SobSharp.lean`): `[propext, Classical.choice, Quot.sound]` for all 12 headline/ingredient theorems.  No `sorry`, no new `axiom`, no
`set_option` in any new file; new files build with 0 warnings/0 errors; frozen files untouched (`scripts/check_frozen.py` OK); `lakefile.toml`, `lake-manifest.json`,
`lean-toolchain` untouched.

## 5. What is NOT done
* Optimality of `k > m + d/2` (not claimed; known by `|x|^{-a}`-type counterexamples).
* `W^{k,p}`, `p ≠ 2`; global (weighted) Sobolev spaces; `m + d/2` for non-integer orders.
* Downstream files are unchanged: `EllRegProof.ellReg` still uses order `m + d` (valid); `ellReg_of_sharp` exposes the sharper order.
