# AUDIT R16 E2 (self-attack, Armstrong method): weak Caccioppoli (E1) and interior H² (E2)

Targets: `Instances/GibbsRd/STATEMENTS_R16_E2.md`.  Files: `EllipticE1`, `EllipticE2A`–`E2E`, `AxiomCheckR16E2`.  No `sorry`, no `set_option`, standard axioms.

## 1. Hypotheses: vacuity / satisfiability
* `H = {LocL2 u, WeakDeriv u (g i) i, LocL2 (g i), LocL2 h, VeryWeakSol u h}`.  Satisfiable: `u` smooth, `g i = ∂ᵢ u`, `h = L u`
  (the very weak equation is `∫ u L a w = ∫ (Lu) a w`, symmetry of `L` w.r.t. `w dx`, `EllData.ibp_master`).  NOT proved in Lean as an instance lemma
  (honest gap: no Lean lemma `smooth ⇒ H`); the trivial instance `u = h = 0` is not informative.
* `WeakDeriv` uses `C^∞` test functions (R16-E1); `Sm` is `ContDiff ℝ ((⊤:ℕ∞)) ` = Mathlib `∞`, NOT analytic.  `VeryWeakSol` tests on `A₀ d` (smooth, compact support).
* `EllData` supplies `a` symmetric, positive definite pointwise, bounded above globally, `w > 0` smooth.  Ellipticity is only needed LOCALLY (`local_ellipticity` on `S`);
  `a_bdd` (global upper bound) is used only through `hΛ`.
* The equation has NO lower-order terms and no zero-order term (pure `L = w⁻¹ div(w a ∇)`), as in `EllReg`; Evans' Thm 1 has `c u` terms which are not needed.

## 2. Local vs global L²
* Everything is `L²_loc` (`LocL2`, test of `MemLp` on `volume.restrict K` for every compact `K`).  Global `MemLp ... volume` occurs only for objects with
  compact support (`memLp_of_locL2_cs`), which is where `weakForm_extend`, `dq_ibp_L2`, `eLpNorm_dq_le`, `abs_integral_mul_le` apply.
* Integrability of `c · F · G` (`F,G ∈ L²_loc`, `c` continuous, compact support) is `integrable_cs_mul_mul`, used for every integrand; no integrability is assumed.

## 3. Test-function class used in the weak form
* E1: `v = ζ²u`, `vⱼ = ζ²gⱼ + 2ζ∂ⱼζ u` (compactly supported `H¹`), through `weakForm_extend` (mollification argument, already audited).
* E2: `v = D_{−t}(ζ² D_t u)` with weak derivatives `D_{−t}(ζ²D_t gⱼ + ∂ⱼ(ζ²) D_t u)` (`weakDeriv_dq`, `smooth_mul`), again through `weakForm_extend`.
  `v` has compact support (`hasCompactSupport_dq`) and lies in `L²` (`memLp_dq`).

## 4. Constants uniform in t (checked by construction)
`energy_bound` fixes, BEFORE introducing `t`: `S = cthickening 1 (tsupport ζ)`, `λ` (`local_ellipticity` on `S`), `m = Z·m₀` (lower bound of `w` on `S`), `Wc`, `Λ`,
`Bz` (sup of `|ζ|, |∂ⱼζ|`), the cut-off `χ = cut (N+1) = 1` on `S`, `C₁` (`dq_local_bound` on `supp χ`), `M` (`abs_dq_le` for `χ·w·aᵢⱼ`), `B = ΣΣ M`.
The constant is `Cbound (λ m) (B Bz d) (Bz²) Gs H0 (d Bz² C₁²) (2 Wc Λ)` with `Gs = ∫χ²Σgᵢ²`, `H0 = ∫χ²(hw)²` — none depends on `t`.
`energy_step` only needs `|t| ≤ 1` (for `x + te ∈ S`, `supp D_{−t}Φ ⊂ S`, `hDm`).  `t = 0` is allowed (`dq` with `/0 = 0`, harmless: nothing divides by `t`).

## 5. d = 0, d = 1
`d = 0`: `Fin 0` sums are empty; `interior_H2` has no `i, k`; `energy_bound` trivial (`∫ 0 ≤ C`); `local_ellipticity` handles `d = 0` separately.
`d = 1`: no special case used; `Pi.single 0 1`, `Fin 1` sums reduce to one term.  `Cbound` is only used through `final_arith`, which needs `a > 0` (`λ m > 0`).

## 6. Where the textbook proof is changed (honest)
* Evans proves the bound for `∫ζ²|D_tDu|²` using `‖D_{−t}(ζ²D_tu)‖ ≤ C ‖D(ζ²D_tu)‖` AND `‖D_tu‖_{L²(supp ζ)} ≤ C‖Du‖_{L²}`.  Here both are used as written
  (`eLpNorm_dq_le`, `dq_local_bound`).  Young's inequality is performed pointwise with explicit constants (`pw_R2`, `qf_young`) and the absorption in `final_arith`.
* Evans' coefficients are `a^{ij}` with Lipschitz bounds `‖a‖_{C¹}`; here `Aᵢⱼ = w aᵢⱼ` and the Lipschitz bound is `abs_dq_le` applied to `χ Aᵢⱼ` (valid as `χ = 1` on `S`).
* The test-function identity uses a non-divergence-free coefficient `A(·+te)` in front of `D_t g`: this is the (shifted) coefficient of Evans' Step 2, not `A`.

## 7. Attack surface (for the hostile auditor)
1. `WeakDeriv`/`Sm` definitions and the `⊤ : ℕ∞` casts (shared with all R16 files).
2. `VeryWeakSol` vs the real `EllReg`/`resolvent_weak` form (`Z⁻¹` factor, `E.L`, `A₀ d`): E1/E2 are NOT yet connected to `EllReg`; gap `L²_loc ⇒ H¹_loc` (Friedrichs) remains for `weakHypo_of_reg`.
3. `weakForm_extend` (previous batch) is relied upon, including `weakDeriv_zero_off`.
4. `dq` at `t = 0`, and the use of `cthickening |t|` vs `cthickening 1` (`hSv`).
5. `energy_step` hypotheses: `hTS`, `hSv`, `hχ1 : ∀ x ∈ S, χ x = 1`, `hDm` (only on `tsupport ζ`), `hY0`; their discharge in `energy_bound`.
6. `Cbound`/`final_arith`: existential only (the exact formula is irrelevant, but check `a > 0`, `K₁, K₂ ≥ 0`).
7. `interior_H2` extraction of `eLpNorm` on `K` from `∫ ζ² Σ` (`ζ = 1` on `K`, `cut (N+1)`), sequence `1/(n+1)`.
8. Absence of E3 and of the Friedrichs step (`interior_regularity_step` is NOT delivered).
