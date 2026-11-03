# Round 18, Stream A3 (`Core2` for the Gibbs triple on `ℝ^d`): statements fixed BEFORE the proofs.

Change only by a logged erratum in `ERRATA.md` (prefix `R18-`); deviations go to the `Status` section at the end.
Setting: `G : GibbsRdData d` (`μ = Z⁻¹ e^{-V} dx`, `𝒜₀ = C_c^∞(ℝ^d)`, `L f = Δf − ∇V·∇f`, `Γ = ∇f·∇g`,
`G.gibbsRdFull_unconditional : FullTriple (Rd d)`).  All names in `MarkovTriple.BGL.Instances.GibbsRd`.

## Mathematical plan (BGL Sect. 3.3, Prop. 3.3.17 p. 161-162, last claim; reduction `FullTriple.core2_of_dense`/R15-1)
`Core2`: for `a ∈ 𝒜₀` find `b_n ∈ 𝒜₀` with `(1-L) b_n → a` and `L(1-L) b_n → L a` in `L²(μ)`.

1. *Resolvent solution.*  `c = [a] ∈ L²(μ)`, `v := (1-L)⁻¹ c` (Friedrichs resolvent).  The chain `x₀ = v, x₁ = a, x_k = (1-L)^{k-1} a`
   (all in `𝒜₀`) satisfies the weak equations `(1-L)x_k = x_{k+1}` (resolvent_weak + symmetry on `𝒜₀`), so the proved
   `EllReg` (`EllData.ellReg`) gives a `C^m` representative for every `m`, hence a `C^∞` one; integrating by parts against
   `C_c^∞` the weak equation upgrades to the classical `L v = v - a` (everywhere, continuity).
2. *Energy estimates* (BGL Sect. 3.2 / Bakry's argument, `Γ₂ ≥ ρ Γ`).  With cut-offs `χ_R(x) = s(2 - |x|²/R²)`:
   (i) Caccioppoli `∫ χ² |∇v|² dμ ≤ C(‖v‖² + ‖a‖²)` uniformly in `R` (test `χ² v` in `∫ g L v = -∫ Γ(g,v)`), so `∇v ∈ L²`.
   (ii) Cut-off Bochner: `∫ φ Γ₂(v) dμ = ½∫ Γ(v) Lφ dμ - ∫ φ Γ(v, Lv) dμ` for `φ = χ²`, with
   `Γ₂(v) = ‖Hess v‖² + Hess V(∇v,∇v) ≥ ‖Hess v‖² + ρ|∇v|²` (`gibbsRd_Γ₂_eq`, `HessGe V ρ`, `ρ` ANY sign); the terms are
   bounded using `|Lφ| ≤ K` and (i); `Fatou` gives `Hess v ∈ L²(μ)`.  (Only a LOWER bound `Hess V ≥ ρ` is used here: this is the
   `Γ₂ ≥ ρΓ` argument of the book; but `|Lχ_R| ≤ K` needs the linear growth of `∇V`, i.e. bounded `Hess V` (below).)
3. *Cut-off in the graph norm of `L²`.*  `b_R = χ_R v ∈ 𝒜₀`.  `(1-L) b_R - a = (χ_R - 1)a - R_R`,
   `R_R = v Lχ_R + 2Γ(χ_R, v)`, and (polarised Bochner `L Γ(f,g) = Γ(Lf,g)+Γ(f,Lg)+2Σ f_ij g_ij + 2 Σ V_ij f_i g_j`)
   `L R_R = (Lv)(Lχ) + v L(Lχ) + 4Γ(Lχ,v) + 2Γ(χ,Lv) + 4 Σ χ_ij v_ij + 4 Σ V_ij χ_i v_j`.
   Uniform (in `R`) bounds for `χ, ∂χ, ∂²χ, Lχ, ∂(Lχ), L(Lχ)`, supported in `{R² ≤ |x|² ≤ 2R²}`, follow from the scaling
   `∂^α χ_R = R^{-|α|} (∂^α χ)(x/R)`, the linear growth `|∂ᵢV(x)| ≤ C(1+|x|)` (bounded Hessian) and bounded `∇³V`.
   Dominated convergence with `v, ∇v, ∇²v, a ∈ L²` gives `R_R → 0`, `L R_R → 0`.
4. *Assembly*: `Core2` for `gibbsRdFull_unconditional`; with `gibbsRdFull_CD_unconditional` and
   `FullTriple.mem_domain_of_Γ₂` the **unconditional converse of Prop. 3.3.17** for these data.

**Hypothesis (the weakest one our proof uses; admits `ρ > 0`):** `BddHess3`: `∂ᵢ∂ⱼ V` and `∂ᵢ∂ⱼ∂ₖ V` are bounded on `ℝ^d`.
It does NOT bound `∇V` (so `Hess V ≥ ρ > 0`, which forces `|∇V| → ∞`, is allowed; contrast ERRATA R17-M1).
Not claimed: `Core2` for `GibbsRdData` with unbounded `Hess V` / `∇³V`; for general `EllData d` / `RiemData d` (needs
bounds on the metric `a` and its derivatives, commutators `[L, χ]` involve `∂a`; not attempted in this stream).

## Targets
* **B0** `structure GibbsRdData.BddHess3 (G : GibbsRdData d) : Prop` with fields
  `hess : ∃ C, ∀ x i j, |pderiv (pderiv G.V i) j x| ≤ C`,
  `third : ∃ C, ∀ x i j k, |pderiv (pderiv (pderiv G.V i) j) k x| ≤ C`.
  Lemma `GibbsRdData.BddHess3.grad_growth : ∃ C, ∀ x i, |pderiv G.V i x| ≤ C * (1 + ∑ j, |x j|)`.
* **B1** (calculus, `Core2RdCalc.lean`, `Sm V`, `Sm f`, `Sm g`, no measure):
  `Lr_mul : Lr V (f * g) x = f x * Lr V g x + g x * Lr V f x + 2 * Gr f g x`;
  `Lr_Gr : Lr V (Gr f g) x = Gr (Lr V f) g x + Gr f (Lr V g) x + 2 * ∑ i, ∑ j, pderiv (pderiv f i) j x * pderiv (pderiv g i) j x
     + 2 * ∑ i, ∑ j, pderiv (pderiv V i) j x * pderiv f i x * pderiv g j x`;
  `Lr_remainder` (the formula of step 3 for `R = v · Lχ + 2 Γ(χ,v)`).
* **B2** (cut-offs, `Core2RdCut.lean`, `hb : G.BddHess3`, `χ n := cut ((n:ℝ)+1)`): `∃ K, ∀ n x i j`:
  `|χ n x| ≤ 1`, `|∂ᵢ χ n x|, |∂ⱼ∂ᵢ χ n x|, |Lχ n x|, |∂ᵢ(Lχ n) x|, |L(Lχ n) x| ≤ K`, and all of these derivative/`L` quantities
  vanish when `qd x < (n+1)²`.
* **B3** (`Core2RdResolvent.lean`): `GibbsRdData.exists_resolvent_smooth (ha : a ∈ A₀ d) : ∃ v, Sm v ∧ MemLp v 2 G.toEll.μ ∧ ∀ x, Lr G.V v x = v x - a x`
  (no hypothesis on `V`).
* **B4** (`Core2RdEnergy.lean`): `memLp_grad_resolvent : ∀ i, MemLp (pderiv v i) 2 μ` (no hypothesis on `V`); and
  `memLp_hess_resolvent (hρ : HessGe G.V ρ) (hP : ∃ K, ∀ n x, |Lr G.V (cut ((n:ℝ)+1)) x| ≤ K) : ∀ i j, MemLp (pderiv (pderiv v i) j) 2 μ`.
* **B5** (`Core2RdMain.lean`): `gibbsRd_core2 (hb : G.BddHess3) : G.gibbsRdFull_unconditional.Core2` (hypotheses: ONLY `BddHess3`);
  `gibbsRd_mem_domain_of_Γ₂ (hb) (hρ : HessGe G.V ρ) {f} (hf : f ∈ A) (hf2 : MemLp f 2 μ) (hG hG2 : Integrable ..) :
   [f] ∈ 𝒟(L) ∧ L[f] = [Lf] a.e.` (the converse of Prop. 3.3.17), `ρ` of any sign.
* **B6** (`Core2RdExample.lean`, non-vacuity): (a) `gaussData d` satisfies `BddHess3` and `HessGe _ 1` (`ρ = 1 > 0`, `∇V` unbounded);
  (b) non-Gaussian: `V(x) = |x|²/2 + cos(x₀)/2` on `ℝ^{d+1}` is a `GibbsRdData` with `BddHess3` and `HessGe V (1/2)`.

## Status
All targets B0-B6 PROVED as stated (statement section unchanged), no deviation of content.  Files: `Core2RdDefs` (B0),
`Core2RdCalc` (B1), `Core2RdCut` (B0-lemma `grad_growth`, B2 `cut_bounds`/`cut_vanish`), `Core2RdResolvent` (B3), `Core2RdEnergy` (B4),
`Core2RdZL` + `Core2RdCutZL` + `Core2RdAssemble` (dominated-convergence bookkeeping and `core2_of_ZL`), `Core2RdMain` (B5), `Core2RdExample` + `Core2RdWitness` (B6),
`AxiomCheckR18Core2Rd` (only `propext`, `Classical.choice`, `Quot.sound`).  Names/signature details: ERRATA R18-2.  NOT done: `EllData d`, `RiemData d`,
unbounded `Hess V`/`∇³V`.
