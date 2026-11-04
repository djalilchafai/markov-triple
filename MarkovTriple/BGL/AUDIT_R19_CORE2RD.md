# AUDIT R19 (Stream A5): `Core2` and the converse of BGL Prop. 3.3.17 for Gibbs measures on `ℝ^d` WITHOUT `BddHess3` (hostile self-audit)

Statements fixed first: `Instances/GibbsRd/STATEMENTS_R19_Core2Rd.md` (`proposed` in `frozen-manifest.json`, hash refreshed once after appending the Status section; `check_frozen.py` OK).
Book: BGL PDF found (`/tmp/claude-1000/bgl/bgl.txt`); Prop. 3.3.17 (pp. 161-162: converse "under the additional ergodicity property", handled in this repository by
`FullTriple.Core2`, ERRATA R15-1/R15-2), Prop. 3.2.1 (p. 142, ESA by cut-offs), Def. 3.3.9 (p. 157, completeness) checked.

## 1. What is proved (`MarkovTriple.BGL.Instances.GibbsRd`; axioms `propext`, `Classical.choice`, `Quot.sound` only, `AxiomCheckR19Core2Rd.lean`)
| item | name | file |
|---|---|---|
| hypothesis | `GibbsRdData.GrowHess3` : `∃C, |∂ᵢ∂ⱼV| ≤ C(1+Σ|∂ₗV|)`, `∃C, |∂ᵢ∂ⱼ∂ₖV| ≤ C(1+Σ|∂ₗV|)`; `BddHess3.growHess3`; `GrowHess3.laplace_le : ΔV ≤ |∇V|²/4+B`; `memLp_mul_growth` | `Core2RdWDefs` |
| C1 | `memLp_hess_resolvent_free` : `Hess v ∈ L²` from `HessGe V ρ` ONLY (no bound on `L(cut)`, no growth) | `Core2RdWHess` |
| C2 | `memLp_V_mul_of_hardy` : `f,∇f ∈ L²`, `ΔV ≤ |∇V|²/4+B` ⇒ `∂ₖV f ∈ L²` | `Core2RdWHardy` |
| C3 | `resolvent_weighted_L2` : `∂ₖV v`, `∂ₖV ∂ᵢv`, `∂ⱼV(∂ₖV v) ∈ L²` | `Core2RdWMain` |
| C4 | `good_dw`, `ZL_Lchi`, `ZL_dLchi`, `ZL_LLchi`, `cutoff_ZL_w` | `Core2RdWCut` |
| **C5** | `GibbsRdData.gibbsRd_core2_w (hρ : HessGe G.V ρ) (hgr : G.GrowHess3) : G.gibbsRdFull_unconditional.Core2`; `gibbsRd_mem_domain_of_Γ₂_w` | `Core2RdWMain` |
| **C6** | `quarData d` (`V = Σ xᵢ⁴/4 + xᵢ²/2`): `quarData_witness : GrowHess3 ∧ HessGe V 1 ∧ ¬ BddHess3 (d+1)`, `quarData_core2`, `quarData_mem_domain_of_Γ₂` | `Core2RdWExample` |

## 2. The mathematics (BGL route, no new method)
R18's obstruction: `Lχ_n = Δχ_n − ∇V·∇χ_n`, `∂Lχ_n`, `L(Lχ_n)` bounded uniformly (pointwise) — needs bounded `Hess V`, `∇³V`.  Replacement:
* *Hessian, free of `Lχ`.* `Γ₂(v) = ‖Hess v‖² + Hess V(∇v,∇v) ≥ ‖Hess v‖² + ρ|∇v|²` (Bochner, BGL (1.16.5)); `∫φ LΓ(v) dμ = −∫Γ(φ,Γ v) dμ` (IBP with compactly supported `φ=cut²`),
  `−½∇φ·∇Γ(v) = −2ψ Σ q_k a_l h_{lk} ≤ ¼ψ²‖Hess v‖² + 4|∇ψ|²|∇v|²` (Young, `hessIBP_pt`), absorbed; Fatou (`memLp_two_of_cut`). Only `Σ|∂ₖ cut|² ≤ 8C²` is used.
* *Hardy.* `∫g|∇V|² = ∫gΔV + ∫Γ(g,V)` (`ibp_Lr` with `f := V`), `g = η²f²`, Young with constants `1/4`, `ΔV ≤ |∇V|²/4 + B`; applied to `f = v`, `f = ∂ᵢv`, `f = ∂ₖV·v` (the last needs `∇f ∈ L²`, from `GrowHess3` and the first two).
* *Commutators.* `L(χv)`, `L²(χv)` expanded with the proved Bochner commutation (`Lr_Lr_mul`, R18, unchanged); `Lχ_n`, `∂ₖLχ_n`, `LLχ_n` expanded in `∂^αχ_n` (`1≤|α|≤4`, `Good`: uniformly bounded by `cut_deriv_bound`, vanishing near each point) times `∂ᵢV`, `∂ᵢ∂ⱼV`, `∂ᵢ∂ⱼ∂ₖV`, `∂ᵢV∂ⱼV`; each product is `Good × (jet ∈ L²)`, `ZL.of_good` (dominated convergence). `GrowHess3` converts `∂²V·g`, `∂³V·g` to `(1+|∇V|)g` (`memLp_mul_growth`).
The R18 files are untouched; `cutoff_ZL`/`coeffGood`/`cut_bounds` (bounded version) are not used by the new theorem except the generic bookkeeping `ZL`, `Good`, `core2_of_ZL`, `Lr_Lr_mul`, `chi`.

## 3. Faithfulness and non-vacuity
* `pp` of the statements: `gibbsRd_core2_w : ∀ {d} (G : GibbsRdData d) {ρ}, HessGe G.V ρ → G.GrowHess3 → G.gibbsRdFull_unconditional.Core2` — `FullTriple.Core2` is the unchanged R15 definition; the converse conclusion is the unchanged `FullTriple.mem_domain_of_Γ₂` with `gibbsRdFull_CD_unconditional`. No hidden hypothesis; `GibbsRdData` unchanged.
* Hypotheses NOT contradictory: `quarData d` is a genuine `GibbsRdData` (`ofConvex`, `e^{-V}` integrable from `Hess V ≥ 1`), `HessGe V 1` (`ρ = 1 > 0`), `GrowHess3` (constants 3 and 6: `x² ≤ 1+|x|³`, `|V'|=|x|³+|x|`), and `¬ BddHess3` for `d+1 ≥ 1` (`∂₀∂₀V = 3x₀²+1` unbounded, Lean `quarData_not_bddHess3`).
  The theorems `quarData_core2`, `quarData_mem_domain_of_Γ₂` are INSTANTIATED; `∇V ~ x³`, `∇²V ~ x²`, `∇³V ~ x` (so R18 did not apply). `BddHess3 ⇒ GrowHess3` (`growHess3`), hence all R18 witnesses (`gaussData_growHess3`) are covered.
* `ContDiff` is `(⊤ : ℕ∞)` (`Sm`), not analytic.  `quarV` is real-analytic, harmless.
* Probed (`#print`): `GrowHess3` has exactly the two displayed fields; no `sorry`/`axiom`/`set_option`/`native_decide` in `Core2RdW*.lean`; each new file compiled with `lake env lean`: 0 warnings, 0 errors; full `lake build` OK (9347 jobs, 0 warnings in the log).

## 4. What is NOT proved (exact; no overclaim)
* The task asked for `HessGe V ρ` alone.  We could NOT remove `GrowHess3`: the weights `∂²V·v`, `∂³V·v`, `∂²V·∇v` that appear in `Lχ_n`, `∂Lχ_n`, `LLχ_n`, `V_ij χ_i v_j` are controlled only through `|∂²V|, |∂³V| ≲ 1+|∇V|`, which converts them to the Hardy jets.
  Without it we have neither a proof nor a counterexample: for `Hess V ≥ ρ` alone (e.g. `V'' ≳ e^{x²}` oscillating relative to `V'`, outside `GrowHess`), no integral estimate of BGL type (Bochner `∫(Lv)² = ∫Γ₂(v)`) controls `∫|∂³V|²v²` or `∫|∂²V|²|∇v|²`; the Caccioppoli identity for an `L²` solution of `(1−L)²u = 0` alone was not closed either (R17/R18 audits).  This is exactly the gap `GrowHess3` leaves; `GrowHess3` is the `ℝ^d` analogue of the 1-D `GrowHess` (Round 18) and is NOT claimed sharp.
* `GrowHess3` is stated with `Σₗ|∂ₗV|` (the `ℓ¹` norm of `∇V`); `|∇V|₂` gives the same class (norm equivalence, `d` fixed).
* The Hessian lower bound is the constant `ρ`; a `V` with only `Hess V ≥ −C(1+|∇V|)` (the 1-D BE hypothesis) is NOT covered in `ℝ^d` (the 1-D BE estimate was not generalised: `Γ₂ ≥ ρΓ` with constant `ρ` is what is used).
* The radial quartic `|x|⁴/4+|x|²/2` satisfies `GrowHess3` and `Hess V ≥ I` (hand check: `V_ij = (q+1)δ_ij + 2x_ix_j`, `q ≤ M·ℓ¹(x)`, `M ≤ max(1,q)`), but is NOT formalised; the formal witness is the separable quartic. No non-polynomial witness was formalised (`cosData`-type potentials are in `BddHess3` already).
* `EllData d`, `RiemData d`: not attempted (commutators involve `∂a`).  Core2 for arbitrary smooth `V` (≡ e.s.a. of `L²` on `C_c^∞`): neither proved nor refuted.
* `d = 0` is covered by the same proofs (empty sums); no separate witness for `quarData 0` beyond the trivial space.

## 5. Hostile checks
1. *Is `∫φ LΓ(v) = −∫Γ(φ,Γ v)` legitimately used with `Γ v` only smooth, not compactly supported?* Yes: `ibp_Lr` needs `Sm` and compact support of ONE factor (`φ = cut²`).
2. *Absorption circularity?* Each integral has compact support (finite); absorption is done before `R → ∞`, constants independent of `R`.
3. *Hardy for `f = ∂ₖV v`*: requires `∇f ∈ L²`: `∂ᵢ(∂ₖV v) = ∂ᵢ∂ₖV v + ∂ₖV ∂ᵢv`; first term by `GrowHess3` and `∂ₘV v ∈ L²`, second is `W2` (Hardy for `∂ᵢv`, which needs `Hess v ∈ L²`, C1). No circularity: order W1 → C1 → W2 → W3.
4. *`ΔV ≤ |∇V|²/4 + B` from `GrowHess3`*: `ΔV ≤ dC(1+s)`, `s² ≤ d|∇V|²` (Cauchy–Schwarz), AM-GM; proved in `laplace_le` (case `d = 0` separate).
5. *`Good` really holds for the `n`-dependent cut-off* (`R = n+1`): uniform bound from `cut_deriv_bound` (`R ≥ 1`), vanishing `n ≥ ⌈|x|²⌉` by `dw_zero_of_open`.
6. *Index conventions*: `pderiv (pderiv V i) j = ∂ⱼ∂ᵢV`; all sums are over free indices, symmetric by `pderiv_symm` where needed (only in the unchanged R18 Bochner file).
7. *Build hygiene*: `.lake/build` copied, `.lake/packages` symlinked; `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`, `Instances/Gibbs/`, `Riemannian/` and all frozen/fenced files untouched.
