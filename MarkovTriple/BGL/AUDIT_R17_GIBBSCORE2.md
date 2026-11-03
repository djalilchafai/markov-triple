# AUDIT R17 Stream A: `Core2` and the converse of Prop. 3.3.17 for Gibbs triples (hostile self-audit, Armstrong method)

Statements fixed BEFORE the proofs in `Instances/Gibbs/STATEMENTS_R17_Core2.md` (registered `proposed` in `frozen-manifest.json`);
none was weakened while proving (naming remarks in ERRATA R17-1).  Files: `Instances/Gibbs/{Core2Resolvent,Core2Calc,Core2Cut,Core2Main,Core2Example,AxiomCheckR17Core2}.lean`.

## What is proved (1-D Gibbs, `G : GibbsData`)
* A1 `GibbsData.exists_resolvent_smooth`: for `a ∈ C_c^∞`, `∃ v` smooth, `v ∈ L²(μ)`, `L v = v - a` pointwise.  (The Friedrichs resolvent
  `R[a]`, its weak equation `DiffusionTriple.resolvent_weak`, the `C^{j+2}` gain `resolvent_gain` of `RegSemigroup.lean` for all `j`, the symmetric
  integration by parts against test functions, and du Bois-Reymond/`ae_eq_zero_of_integral_contDiff_smul_eq_zero`.)  NO hypothesis on `V`.
* A2 `memLp_deriv_resolvent` (`v' ∈ L²(μ)`, Caccioppoli with the cut-offs, NO hypothesis on `V`) and `resolvent_jet_L2`
  (`v'' = v - a + V'v'`, `v''' = v' - a' + V''v' + V'v''` in `L²(μ)` under `BddJet`).
* `Core2Calc`: the cut-off commutators `L(ψv) - Lv`, `L²(ψv) - L²v` in jets (BGL's product rule `L(fg) = fLg + gLf + 2Γ(f,g)` three times).
* `Core2Cut.cutoff_ZL`: `χ_n v → v`, `L(χ_n v) → Lv`, `L²(χ_n v) → L²v` in `L²(μ)` (dominated convergence; the coefficients are uniformly bounded by
  `BddJet` and the bounded cut-off jets `χ_n^{(j)}`, `j ≤ 4`).
* A3 `GibbsData.gibbsFull_core2 (hb : G.BddJet) : G.gibbsFull_unconditional.Core2`.
* A4 `GibbsData.gibbs_mem_domain_of_Γ₂`: the converse of Prop. 3.3.17 (p. 162), UNCONDITIONAL (no `Core2` hypothesis) for `BddJet` Gibbs triples with `V'' ≥ ρ`.
* A5 `sqrtGibbs_bddJet`: `V = √(1+x²)` is a `GibbsData` with `BddJet` (non-Gaussian, non-compact), so A3/A4 are not about an empty class.
`#print axioms` (file `AxiomCheckR17Core2.lean`): only `propext`, `Classical.choice`, `Quot.sound`.  No `sorry`, no `set_option`, 0 warnings.

## What is NOT proved (honest scope)
1. **`Core2` for arbitrary `GibbsData` (any smooth `V` with `e^{-V}` integrable) and for `EllData`/`GibbsRdData` on `ℝ^d`: NOT proved.**
   * `Core2` is (by `core2_of_dense` and its easy converse) equivalent to essential self-adjointness of `L²` on `C_c^∞`.  By the Hilbert-space argument
     (`w ⊥ (1-L)²C_c^∞` ⇒ `u := w` smooth by the proved elliptic regularity, `(1-L)²u = 0` classically), what is missing for a general `V` is exactly
     `(1-L)u ∈ L²(μ)` for an `L²` solution `u` of `(1-L)²u = 0`.  The Caccioppoli identity for such `u`
     (`∫ψ²w² = 2∫ψ(wΓ(ψ,u) - uΓ(ψ,w))`, `w = (1-L)u`, no `Lψ` appears) gives only `W_n² ≤ C n⁻¹ W_{2n}^{3/2}`, which allows super-exponential growth of
     `W_n = ‖w 1_{B_n}‖`; we found no way to close it, nor a counter-model.  We believe that for rapidly growing, oscillating `V` (potentials
     `W = V'²/4 - V''/2` of the ground-state transform with `H` e.s.a. but `H²` not e.s.a. on `C_c^∞`) `Core2` can FAIL; we did not prove that.
   * the method used (direct cut-off of the resolvent solution, as for OU/Lebesgue) needs control of the commutators `[L,χ_n]` (`V'χ_n'`, `V''χ_n'`, ...); under
     `BddJet` this is a dominated convergence.  The natural extension is `V'' ≥ ρ`, `|V''|,` and `|V'|,|V'''| ≤ C(1+|x|)` (the Gaussian case): it needs a
     cut-off Bochner estimate `∫ψ²v''² ≤ ∫ψ²(Lv)² - ∫ψ²V''v'² - 2∫ψψ'V'v'²` (derived by hand, not formalized) and `n`-dependent coefficient bounds; NOT done.
2. `ℝ^d` (`EllData`, `GibbsRdData`): nothing new beyond R16.  The same method would need, in `d` dimensions, (i) the smooth resolvent solution (fine: `EllReg` chain
   `x₀ = R[a], x₁ = a, x_{k+2} = x_{k+1} - L x_{k+1}`), (ii) `∇v, ∇²v ∈ L²(μ)` by a cut-off Bochner/Caccioppoli estimate (Hessian of `v`), (iii) `d`-dimensional
   cut-off commutators `L²(ψ v)` in the form `ψ L²v + 2LψLv + 4Γ(ψ,Lv) + vL²ψ + 4Γ(v,Lψ) + 4Γ₂(ψ,v)` with `Γ₂(ψ,v) = ∇²ψ:∇²v + ∇²V(∇ψ,∇v)`, bounded for bounded
   `∇V, ∇²V, ∇³V`.  None of (ii)-(iii) is in the repository for non-test `v`; not attempted.
3. The ergodicity hypothesis of the book is not used (as in R15).

## Attacks
* **Statement faithfulness.** A3 uses the unchanged definition `FullTriple.Core2` (R15).  A4 is `FullTriple.mem_domain_of_Γ₂` (R15) for `T = gibbsFull_unconditional`
  with `CD(ρ,∞)` from `V'' ≥ ρ` (`gibbsFull_CD_unconditional`); the only addition over BGL p. 162 is `BddJet`, a genuine restriction recorded in the statements file.
  `T.L = Lg V` and `T.A₀ = C_c^∞` by definitional unfolding (the proof of A3 relies on this and typechecks).
* **Vacuity.** `BddJet` is satisfiable (A5, with a genuine `GibbsData`).  `MemLp` hypotheses: all `L²(μ)` statements are about the probability measure `G.μ`;
  `v ∈ L²` is a genuine element (`R[a]`).  Hypotheses of A4 on `f` are satisfied by `f = 1` and by every `f ∈ C_c^∞`.
  `ContDiff ℝ ⊤` (analytic in this Mathlib) is NOT used: every smoothness hypothesis is `Sm = ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)` (grep; test functions in
  `ae_eq_zero_of_integral_contDiff_smul_eq_zero` are `ContDiff ℝ ∞`).
* **Cut-off family.** `χ_n = chiR (Rn n)` with `Rn n = n+1` (Lebesgue file); `0 ≤ χ ≤ 1`, `χ_n = 1` on `|x| ≤ Rn n`, derivatives up to order 4 bounded uniformly in `n`
  (`chiR_iter_bound`); `χ_n v ∈ C_c^∞`.
* **Uniform bounds are not circular.** `UB`/`Good` only encode: continuous, `sup_{n,x}` finite, eventually zero at each `x`; the eight coefficient families were
  checked individually (`coeff_good`); `L²` memberships of `v, v', v'', v''', Lv, LLv` are proved in `Core2Main`/`Core2Resolvent`, `LLv = (v - a) - La` from `Lg_sub`.
* **Pointwise identities** `L_mul_expand`, `LL_mul_expand` are proved by `ring` after three applications of `Lg_mul`; used with `a = v - Lv` pointwise for `La = Lv - L²v`.
* **Name/instance risk.** `G.gibbsDiff.μ` vs `G.μ` are defeq but not syntactically equal; handled by `Eq.trans … e6.symm` (no `sorry`-like coercion tricks).

## Attack surface left for an independent auditor
Is `BddJet` too strong to be interesting (it excludes `V = x²/2` and every polynomial of degree ≥ 2)?  Yes: the covered class is Laplace-type potentials
(`V ~ |x|`).  OU is covered by its own earlier proof.  The class in item 1 (linear growth of `V'`) would subsume both.
