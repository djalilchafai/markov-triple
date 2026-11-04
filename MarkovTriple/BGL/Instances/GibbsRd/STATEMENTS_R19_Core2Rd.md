# Round 19, Stream A5 (`Core2` for the Gibbs triple on `ℝ^d` WITHOUT `BddHess3`): statements fixed BEFORE the proofs.

Change only by a logged erratum in `ERRATA.md` (prefix `R19-Rd-`); deviations go to the `Status` section at the end.
Setting as in `STATEMENTS_R18_Core2Rd.md`: `G : GibbsRdData d`, `μ = Z⁻¹ e^{-V} dx`, `𝒜₀ = C_c^∞`, `L f = Δf − ∇V·∇f`, `Γ = ∇f·∇g`.
Names live in `MarkovTriple.BGL.Instances.GibbsRd`.  Files `Core2RdW*.lean` (R18 files untouched).

## Why R18 needed `BddHess3`, and the replacement (BGL Prop. 3.2.1 p. 142, Def. 3.3.9, Prop. 3.3.17 p. 161-162)
R18 cut off `v = (1-L)^{-1}a` by `χ_n v` and bounded the commutator coefficients `Lχ_n = Δχ_n − ∇V·∇χ_n`, `∂(Lχ_n)`, `L(Lχ_n)` UNIFORMLY
(pointwise), which needs `|∇V| ≲ 1+|x|`, `∇³V` bounded.  Here the coefficients are NOT bounded; they are `(bounded Good χ_n-derivative) × (weighted jet of v)`,
and the weighted jets lie in `L²(μ)` by two integral estimates (d-dimensional versions of the 1-D `memLp_of_hardy`, Round 18):

1. *(Hessian, no cut-off Laplacian).*  The cut-off Bochner identity `∫φ‖Hess v‖² + ∫φ Hess V(∇v,∇v) = −½∫Γ(φ,Γ(v)) − ∫φ Γ(v,Lv)` (`Γ₂ = ½LΓ − Γ(·,L·)`,
   `∫φ LΓ(v) = −∫Γ(φ,Γ v)`), with `Hess V ≥ ρ` and Young `4 ψ ψ_k v_l v_{lk} ≤ ½ψ² v_{lk}² + 8 ψ_k² v_l²`, gives `Hess v ∈ L²(μ)`
   from `∇v ∈ L²` with NO bound on `Lχ_n` (R18 used `|Lχ_n| ≤ K`).  This is the `Γ₂ ≥ ρΓ` argument of BGL Sect. 3.2/3.3.
2. *(Hardy).*  `∫ g|∇V|² dμ = ∫ gΔV dμ + ∫ Γ(g,V) dμ` (IBP `ibp_Lr` with test function `V`); with `g = η²f²`, `ΔV ≤ |∇V|²/4 + B`:
   `f, ∇f ∈ L²(μ) ⇒ ∂ₖV·f ∈ L²(μ)` for all `k`.

**Hypothesis `GrowHess3`** (the weakest the route uses): `∃ C, ∀ x i j, |∂ᵢ∂ⱼV x| ≤ C(1 + Σ_k |∂ₖV x|)` and
`∃ C, ∀ x i j k, |∂ᵢ∂ⱼ∂ₖV x| ≤ C(1 + Σ_l |∂ₗV x|)`  (the `ℝ^d` analogue of the 1-D `GrowHess`).  `BddHess3 ⇒ GrowHess3` (constants).
Together with the curvature hypothesis `HessGe V ρ` (any `ρ ∈ ℝ`) that the converse already has.
Not claimed: `Core2` for `V` with `Hess V ≥ ρ` only (no growth control of `∇²V,∇³V` by `∇V`), nor `EllData`/`RiemData`.

## Targets
* **C0** `structure GibbsRdData.GrowHess3 (G : GibbsRdData d) : Prop` (fields `hess`, `third` as above);
  `GibbsRdData.BddHess3.growHess3 : G.BddHess3 → G.GrowHess3`;
  `GrowHess3.laplace_le : ∃ B, ∀ x, ∑ i, ∂ᵢ∂ᵢV x ≤ (∑ k, (∂ₖV x)²)/4 + B`.
* **C1** `memLp_hess_resolvent_free (hρ : HessGe G.V ρ) : ∀ i j, MemLp (pderiv (pderiv v i) j) 2 μ`   (for `v` smooth, `v ∈ L²`, `Lv = v − a`, `a ∈ 𝒜₀`;
  NO hypothesis `hP` on `L(cut)`; `ρ` any sign).
* **C2** `memLp_V_mul_of_hardy`: `Sm f`, `MemLp f 2 μ`, `∀ i, MemLp (∂ᵢ f) 2 μ`, `∃ B, ∀ x, ΔV x ≤ |∇V x|²/4 + B` ⟹ `∀ k, MemLp (∂ₖV · f) 2 μ`.
* **C3** `resolvent_weighted_L2 (hg : G.GrowHess3) (hρ : HessGe G.V ρ)`:  for `v` as in C1, all of
  `∂ₖV v`, `∂ₖV ∂ᵢ v`, `∂ⱼV (∂ₖV v)`  lie in `L²(μ)`.
* **C4** `cutoff_ZL_w (hg : G.GrowHess3)`: from `v, ∇v, ∇²v ∈ L²`, `Lv, LLv, ∂Lv ∈ L²` and the C3 jets: `χ_n v − v`, `L(χ_n v) − Lv`, `LL(χ_n v) − LLv → 0` in `L²(μ)`.
* **C5** (main) `GibbsRdData.gibbsRd_core2_w (hg : G.GrowHess3) (hρ : HessGe G.V ρ) : G.gibbsRdFull_unconditional.Core2`  and
  `gibbsRd_mem_domain_of_Γ₂_w (hg) (hρ) …` (converse of BGL Prop. 3.3.17 (p. 162), same conclusion as `gibbsRd_mem_domain_of_Γ₂`).
* **C6** (non-vacuity, a `ρ > 0` witness OUTSIDE `BddHess3`) `quarData d : GibbsRdData d` with `V = Σᵢ (xᵢ⁴/4 + xᵢ²/2)` (separable ℓ⁴-quartic):
  `quarData_growHess3`, `quarData_hessGe : HessGe V 1`, `¬ (quarData (d+1)).BddHess3`; `quarData_core2`, `quarData_mem_domain_of_Γ₂` instantiated.

## Status
All targets C0-C6 PROVED as stated; deviations (logged as ERRATA R19-Rd-4, none weakens a statement):
* C3 `resolvent_weighted_L2 (hgr) hv h0 h1 h2` takes `v ∈ L²`, `∇v ∈ L²`, `∇²v ∈ L²` as hypotheses (C1 provides `∇²v ∈ L²` in the main theorem) instead of `Lv = v − a`, `hρ`.
* C4 `cutoff_ZL_w` takes the additional weighted jet `∂ₖV · Lv ∈ L²` (`hWL`; proved in the main theorem from `∂ₖV v ∈ L²` and `a ∈ C_c`).
* C6 `quarData_not_bddHess3 (d) : ¬ (quarData (d+1)).BddHess3`.
Files: `Core2RdWDefs` (C0, `memLp_mul_growth`), `Core2RdWHess` (C1), `Core2RdWHardy` (C2), `Core2RdWCut` (`good_dw`, `ZL_Lchi`, `ZL_dLchi`, `ZL_LLchi`, C4),
`Core2RdWMain` (C3, C5), `Core2RdWExample` (C6), `AxiomCheckR19Core2Rd` (only `propext`, `Classical.choice`, `Quot.sound`).
NOT proved: `Core2` under `HessGe V ρ` alone (no `GrowHess3`); `EllData`/`RiemData`.
