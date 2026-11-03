# AUDIT R16 Friedrichs (self-attack, Armstrong method step (b))

Scope: `EllipticFriedrichs{Kernel,Young,Comm,Est,Eq,Energy,Main,Ell}.lean`, statements in
`Instances/GibbsRd/STATEMENTS_R16_Friedrichs.md`, errata R16-F1..F3.

## 1. What is proved (all `0 sorry`, axioms propext/choice/Quot.sound only)
`EllData.sobolev_one_of_veryWeak : LocL2 u → LocL2 h → E.VeryWeakSol u h → Sobolev 1 u`  (generic: `Elliptic.sobolev_one_of_veryWeak`).
Route: scaled even mollifier (`exists_frMollSeq`); Friedrichs commutator formula (`comm_formula`) and uniform `L²` bound
(`comm_bound`: `∫ T² ≤ C ∫ Σ(∂ⱼφ)²`); equation for `ρ⋆u` by testing with `ρ⋆φ` (`test_eq`, Fubini `integral_moll_swap`, `ρ` even);
Caccioppoli identity `energy_identity` and absorption `energy_est`; weak compactness `weakDeriv_of_approx`; gluing `weakDeriv_of_local`.

## 2. Attacks and outcomes
* **Vacuity of `WeakDeriv`/`Sobolev`.** Uses `Elliptic.WeakDeriv` with `C^∞` test functions (erratum R16-E1 fixed the analytic-`⊤` vacuity).
  `Sobolev 1 u := LocL2 u ∧ ∀ i, ∃ g, WeakDeriv u g i ∧ LocL2 g`: genuine.  The test `∀ a, Sm a → HasCompactSupport a → …` in the hypothesis
  `veq` also uses `Sm = ContDiff ℝ (⊤:ℕ∞)` (Mathlib `∞`), non-vacuous.  Hypotheses are satisfiable (any smooth `u` with `Pop b u = F`).
* **Constants uniform in `ε`.** `comm_bound` constant `C = (Lb·d·(C₁+1))²·d` with `Lb` = sup of `‖D b_ij‖` on `closedBall 0 (R₀+1)` and
  `C₁ ≥ ∫|∂ᵢρ_n(z)|‖z‖dz` uniform in `n` BY SCALING (`exists_frMollSeq`, via `Measure.integral_comp_smul`).  `energy_est` constant depends on
  `b|closedBall(R₀+1)`, `R₀`, `ζ` (through `Z, M₁, M₂`), `λ`, `C₁`; it is quantified BEFORE `ρ,u,F` (`∃ C, ∀ ρ u F`): checked in the statement.
* **Local vs global.** Only local Lipschitz bounds and local ellipticity on the compact `closedBall 0 R₀`; `u,F ∈ L²_loc` only: data cut by
  the indicator of `closedBall 0 (R₀+2)` (`cutoff_h1`), the equation being used only for test functions vanishing off `closedBall 0 (R₀+1)`
  (checked: `Pop b a` also vanishes there, `Pop_zero_off`).  Support radius of `cut R`: `‖y‖ > 2R ⇒ cut R y = 0` from `‖y‖ ≤ √qd y`.
* **Regularity of coefficients actually needed.** `Sm` (C^∞) is used for `pderiv` calculus (`Sm.pderiv`, product rule); the commutator estimate
  needs only `C¹`/Lipschitz locally; the identity `comm_formula` needs `∂ᵢ∂ⱼ` of `b` NOT (only `∂ᵢ b`).  Symmetry used (erratum R16-F3).
* **Even mollifier.** `integral_moll_swap` needs `ρ(−x)=ρ(x)`; `exists_frMollSeq` symmetrises (`s = (r+r(−·))/2`), checked `∫ s = 1`, support.
* **`d = 0` and `d = 1`.** All statements are for arbitrary `d` (no `d>0` case split was needed; sums over `Fin 0` empty, `ℝ^0` a point:
  `Sobolev 1` trivial).  `d = 1`: `Fin 1 → ℝ`, `‖·‖` sup norm = `|x|`; the scaling `integral_comp_smul` uses `finrank = d` (checked `hfin`).
* **Norm conventions.** `‖x‖` is the SUP norm on `Fin d → ℝ`; kernels' support "‖x‖ < 1/(n+1)"; `cut` uses the Euclidean `qd`; the comparison
  is explicit (`‖y‖ ≤ √qd y`).  `Lb` is for the operator norm of `fderiv` w.r.t. the sup norm and `‖Pi.single i 1‖ ≤ 1`.
* **Junk values.** `integral` of non-integrable functions is `0`: every inequality of the form `∫… ≤ …` is accompanied by explicit integrability
  (`comm_bound` returns `Integrable T²`; `amgm_int` returns integrability of the product; `int_of_zero_off` for continuous functions vanishing
  off a ball).  `conv_sq_le` is stated only for continuous compactly supported `G` for this reason (erratum R16-F2).
* **Statement drift.** E2 and Y1 differ from the first-written form (R16-F1/F2), M1 gets an explicit symmetry hypothesis (R16-F3).

## 3. Remaining / not claimed
* Smooth coefficients only (as in `EllData`); no `H²_loc`, no higher regularity (other agent's `EllipticE*.lean`).
* Not done here: instantiating `EllReg`/`weakHypo_of_reg` (needs `H¹_loc ⇒ H²_loc ⇒ … ⇒ C^m` + Sobolev embedding).  The Friedrichs step is delivered in the
  exact form `LocL2 u → LocL2 h → VeryWeakSol u h → Sobolev 1 u`.
* The chain `x_k = (1-λ)^k f` of `weakHypo_of_reg`: `VeryWeakSol (x_{k}) (x_{k}-x_{k+1})` with `h ∈ L²_loc` from `locL2_of_memLp` (G1) — to be wired by
  the glue agent (not done here).

## 4. Attack surface (for the independent auditor)
1. `exists_frMollSeq`: check evenness, `∫ = 1`, support, and the scaling identity for `∫|∂ᵢρ_n|‖z‖` (`hpd`, `hint`, `integral_comp_smul`).
2. `comm_formula`: sign conventions of `pderiv_moll_ker` (`∂ᵢ(ρ⋆H)(x) = ∫ ∂ᵢρ(x−y)H(y)dy`) and the three-term identity.
3. `term_bound`: the cases (`x` outside `closedBall (R₀+1)`), the use of `pderiv_ker_support` (derivative support ⊆ closed unit ball), local Lipschitz.
4. `comm_bound`: the sum bookkeeping `Σᵢⱼ ∫ … = ∫ κ(x−y) G(y)`, constants `c̄`, `Integrable T²`.
5. `test_eq`/`integral_moll_swap`: Fubini integrability, evenness, the admissible class of test functions (`zero off R+1`).
6. `energy_identity` signs; `caccioppoli_alg` (symmetry); `absorb` (pure arithmetic) — check `η`, `hCTη`.
7. `cutoff_h1`: replacement of `u,F` by indicators (`veq'`), the convergence `hconv`, final `congr_ae` (`cut R·ũ = cut R·u`).
8. `EllData.bco_elliptic`: `w ≥ Z m` on compacts from `exists_dens_lower`; `Pop_bco`: `Pop (w a) f = L f · w`.
9. The hypotheses of `EllData.sobolev_one_of_veryWeak` match `VeryWeakSol` exactly as used by `weakHypo_of_reg` (`resolvent_weak` form): `h` must be `LocL2`.
