# AUDIT R20 (Stream D1): the converse of BGL Prop. 3.3.17 for Gibbs triples WITHOUT `Core2` and WITHOUT growth hypotheses

Hostile self-audit.  Statements: `Instances/Gibbs/STATEMENTS_R20_Direct.md`.  Files: `Instances/Gibbs/Direct{Core,Main,Example,Old}.lean`,
`Instances/GibbsRd/Direct{Core,Main,Example}.lean`, `Instances/Gibbs/AxiomCheckR20Direct.lean`.

## DIFFERENCE FROM BGL

* **BGL** (Prop. 3.3.17, pp. 161-162, converse): `f ∈ 𝒜 ∩ L²`, `Γ(f), Γ₂(f) ∈ L¹` ⇒ `f ∈ 𝒟(L)`.  The book uses the functional `b ↦ ∫ f L(b − Lb)` on `(1−L)𝒜₀`,
  Cauchy-Schwarz for `K = Γ₂ − ρΓ`, Riesz, and an identification step that silently needs `𝒜₀` to be a core for `L²` (`FullTriple.Core2`, ERRATA R15-1).
  R17-R19 proved `Core2` for Gibbs triples only under growth conditions (`BddJet`, `GrowHess`, `PolyHess` on `ℝ`; `BddHess3`, `GrowHess3` on `ℝ^d`; `CoreCut` for `EllData`).
* **Here**: `Core2` is NOT used.  (1) `FullTriple.mem_domain_of_ESA` (BGL Prop. 3.3.6 (i); essential self-adjointness of `L`, F10, true for every Gibbs triple):
  smooth `f ∈ L²` with `L f ∈ L²` lies in `𝒟(L̄)` and `L̄[f] = [Lf]`.  (2) `L f ∈ L²` is proved by a cut-off Caccioppoli estimate in the spirit of BGL Prop. 3.2.1
  (p. 142) applied to `Γ₂` instead of `Γ`:
  `∫χ²(Lf)² = ∫χ²Γ₂(f) + ∫χ Γ(χ,Γf) − 2∫χ (Lf) Γ(χ,f)`.
* **Hypotheses that differ**: BGL: `CD(ρ,n)` abstractly + (implicitly) the core of `L²`.  Here: `V'' ≥ ρ` (resp. `HessGe V ρ`, `ρ` of any sign), `f ∈ 𝒜`,
  `f ∈ L²`, `Γ(f), Γ₂(f) ∈ L¹`; no condition on `V`, `V'''`, `∇³V` beyond smoothness and `e^{-V} ∈ L¹`.  The Hessian-type control of the cross term
  `Γ(χ,Γf)` is specific to the Gibbs/flat-metric structure (`Γ₂ = f''² + V''f'²`; `|Hess f|² + Hess V(∇f,∇f)`); BGL's statement is for an abstract Full Markov Triple.
* `Core2` is not needed for these instances; the `Core2*` theorems (R17-R19) remain valid independent facts (they give `Core2` itself, a stronger property than the converse
  needs) and are not used by the new theorems.  `Core2` for general smooth `V` remains open.

## 1. The argument, line by line (what was proved)

1D (`Gibbs/DirectCore.lean`, `memLp_Lg_of_Γ₂`): `f` smooth, `u = Lf`, `χ = χ_n` with `0 ≤ χ ≤ 1`, `|χ'| ≤ K` (`chiR_iter_bound`).  F7 (`ibp_sm`) with test `χ²u`:
`∫χ²u² = −∫(χ²u)'f'`; F7 with `χ²` against `Γ f = f'²`: `∫χ²L(f'²) = −∫(χ²)'(f'²)' = −4∫χχ'f'f''`; Bochner (`Γ₂_eq`, the DEFINITION `Γ₂ = ½(LΓ − 2Γ(f,L·))` plus the
calculus identity) `f'u' = ½L(f'²) − (f''² + V''f'²)`.  Hence `∫χ²u² = −2∫χχ'uf' + 2∫χχ'f'f'' + ∫χ²Γ₂`.  Pointwise (`direct_pt`): `−2χχ'uf' ≤ ½χ²u² + 2K²f'²`,
`2χχ'f'f'' ≤ K(f'² + f''²)`, `f''² = Γ₂ − V''f'² ≤ |Γ₂| + |ρ|f'²` (the ONLY use of `V'' ≥ ρ`), `χ²Γ₂ ≤ |Γ₂|`.  So `∫χ²u² ≤ ½∫χ²u² + ∫W` with `W ∈ L¹` independent of `n`
(`Γ(f), Γ₂(f) ∈ L¹`), hence `∫(χ_nu)² ≤ 2∫W` and Fatou (`memLp_two_of_cutoff`) gives `u ∈ L²`.  `ℝ^d` (`GibbsRd/DirectCore.lean`, `memLp_Lr_of_Γ₂`) is the same with
`Γ(χ,Γf) = 2Σ∂ₖχ ∂ⱼf ∂ₖ∂ⱼf`, `2|Σ a_k b_j H_jk| ≤ |a|²|b|² + |H|²` (`sum_cross`), `|∇χ_n|² ≤ 8C²` (`sum_sq_pderiv_cut_le`), `|Hess f|² = Γ₂ − Hess V(∇f,∇f) ≤ |Γ₂| + |ρ||∇f|²`.

Cut-off integrals are over compactly supported continuous integrands, so every integrability claim is elementary; no a-priori information on `Lf` is used (no circularity: `f ∈ L²` is not even used).

## 2. Faithfulness / suspicious points checked

* **Final shape** equals `gibbs_mem_domain_of_Γ₂` / `gibbsRd_mem_domain_of_Γ₂_w` (same hypotheses `hf hf2 hG hG2`, same conclusion `∃ hF, generator ⟨[f],hF⟩ =ᵐ L f`), with the hypotheses
  `BddJet`/`PolyHess`/`GrowHess3` and `Core2` REMOVED and only `hρ` kept.
* **Is the result too good?** Consistency checks: (i) the book's second paragraph of 3.3.17 gives the converse direction `f ∈ 𝒟(L) ⇒ Γ(f), Γ₂(f) ∈ L¹, ∫Γ₂ = ∫(Lf)²`; our estimate yields the
  inequality `∫(Lf)² ≤ 2∫W`-type, compatible.  (ii) On OU, `V = x²/2`, the hypotheses recover the known domain.  (iii) The proof never uses `P_t`, ergodicity or `Core2`; the only global input is ESA of
  `L` (F10) through `mem_domain_of_ESA`, which the repo proves for every Gibbs triple (`gibbsFull_unconditional`, i.e. via `WeakHypo` + `f8`, not an axiom).  (iv) The statement does NOT assert
  `Core2`; it is a weaker, different conclusion (membership of one given `f`).
* **Where could it be circular?** `gibbsFull_unconditional` is built from `G.weakHypo`, `G.f8` (proved in R16-R17).  The new theorems depend on nothing weaker than those.
* **Hypothesis `HG`:** `FullTriple.G T f f = ΓA f f` (formula-defined) equals `Go f f = f'²` for smooth `f` (`gibbsDiff_ΓA`); `Γ₂` of the frozen `DiffusionTriple` equals `f''² + V''f'²` (`Γ₂_eq`) / the
  `ℝ^d` Bochner formula (`gibbsRd_Γ₂_eq`).  Both conversions are proved in `DirectMain.lean`, not assumed.
* **`ρ`:** any real number (`ρ ≤ 0` allowed).  In `ℝ^d`, `HessGe V ρ` is the matrix inequality `Hess V ≥ ρ·Id`.
* **Axioms:** `#print axioms` for every new declaration lists only `propext`, `Classical.choice`, `Quot.sound` (`AxiomCheckR20Direct.lean`).  No `sorry`, no `set_option`.

## 3. Hypotheses not contradictory; witnesses OUTSIDE all previous classes (`ρ > 0`)

1-D (`Gibbs/DirectExample.lean`).  `spikyGibbs`: `V = ∬ (2 + sin(e^{t²}))` (double primitive from `0`, no closed form).  Proved in Lean:
* `spkV_ge : V(x) ≥ x²/2`, hence `e^{-V} ∈ L¹` (`GibbsData`); `spikyGibbs_convex : V'' = 2 + sin(e^{x²}) ≥ 1` (`ρ = 1 > 0`).
* `abs_spkP1_le : |V'(x)| ≤ 3|x|` and `spk_peak`: for every `X` there is `x ≥ X` with `e^{x²} = 2πk` (`k ∈ ℕ`), where `V'''(x) = 2x e^{x²}` (cos = 1).
* `spikyGibbs_not_polyHess : ¬ PolyHess` (the third conjunct `|V'''| ≤ C(1 + |V'|^N)` fails for every `C, N`: `2x e^{x²} ≥ 2x^{2N+1}/N!` against `C(1+3^N)x^N`).  Since `GrowHess ⇒ PolyHess` (`GrowHess.polyHess`), `BddHess ⇒ GrowHess` and `BddJet` requires `V'''` bounded (false here, `V''' = 2xe^{x²}cos(e^{x²})` unbounded), none of the R17 (`BddJet`), R18 (`GrowHess`/`BddHess`), R19 (`PolyHess`) theorems applies; `Core2` for this `V` is neither proved nor refuted (the cut-off commutator argument needs `V'''v ∈ L²`).
* `spikyGibbs_mem_domain_of_Γ₂`: the converse holds with hypotheses only `V'' ≥ 1`.  Non-vacuity with an actual function: `spikyGibbs_id_mem_domain` (`f = id`: `Γ(f) = 1`, `Γ₂(f) = V'' ≤ 3`,
  `x ∈ L²(μ)` by `spikyGibbs_memLp_id`; `[x] ∈ 𝒟(L)`, `L[x] = [−V']`).
* Earlier witnesses re-proved by the direct route with only their convexity lemma (`Gibbs/DirectOld.lean`): `expGibbs` (`V = e^{x²}`, `ρ = 2`; this one lies in `PolyHess`, so it is NOT outside the old classes),
  `quarGibbs` (`x⁴/4`-type, `ρ = 1`, in `GrowHess`), `cosGibbs` (`ρ = 1/2`, `BddHess`).  They are listed to show the direct theorem applies with `V''≥ρ` as only input, not as new witnesses.

`ℝ^d` (`GibbsRd/DirectExample.lean`).  `spikyData d`: `V(x) = Σᵢ v(xᵢ)` with `v = spkV`.  `hessGe_spkVd : HessGe V 1`; `spikyData_not_growHess3 (d) : ¬ (spikyData (d+1)).GrowHess3`
(third condition fails at `x = (x₀,0,…,0)`: `|∂₀³V| = 2x₀e^{x₀²}` vs `C(1+Σ|∂ₗV|) ≤ C(1+3x₀)`), hence also not `BddHess3` (`BddHess3.growHess3`); `spikyData_witness`;
`spikyData_mem_domain_of_Γ₂`.  (`CoreCut` for `EllData`: not checked for this `V`.)

## 4. What is NOT proved / limits

* `Core2` itself (ESA of `L²` on `𝒜₀`) is NOT proved for these potentials; the direct theorem sidesteps it.  The abstract `FullTriple.mem_domain_of_Γ₂` remains conditional on `Core2`.
* `EllData`/`RiemData` (variable metric): the cross term `Γ(χ,Γf)` then needs the abstract `|Hess f|`-type bound; not attempted (the R19 `CoreCut` results remain the only coverage there).
* The estimate needs `Γ₂(f) ≥ ρΓ(f)` in the *Hessian* form (`f''² ≤ Γ₂ + |ρ|Γ`); for a general Full Markov Triple one has only `Γ₂ ≥ ρΓ + (Lf)²/n`, which does not control `Γ(χ,Γf)`.
* The statements D1-2/D1-4 carried a superfluous hypothesis `MemLp f 2` (dropped in the proofs: stronger lemma; ERRATA R20-D1-1).
* The ERRATA R15-1 remark stays true as a statement about the book's proof route; what changes is that for Gibbs triples the converse does not need `Core2`.
