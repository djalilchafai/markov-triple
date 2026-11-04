# Round 20, Stream D1 (converse of BGL Prop. 3.3.17 for Gibbs WITHOUT `Core2`, WITHOUT growth hypotheses): statements fixed BEFORE the proofs.

Change only by a logged deviation in a `Status` section below and an erratum in `ERRATA.md` (prefix `R20-D1-`).
Files: `Instances/Gibbs/Direct*.lean` (1-D), `Instances/GibbsRd/Direct*.lean` (`ℝ^d`); audit `MarkovTriple/BGL/AUDIT_R20_DIRECT.md`.

## DIFFERENCE FROM BGL

* **What BGL does** (Prop. 3.3.17, p. 161-162, converse): for `f ∈ 𝒜 ∩ L²` with `Γ(f), Γ₂(f) ∈ L¹` the book shows `f ∈ 𝒟(L)` through the linear
  functional `b ↦ ∫ f L(b - Lb)` on `(1-L)𝒜₀`, Cauchy-Schwarz for `K(f,h) = Γ₂(f,h) - ρΓ(f,h)`, Riesz, and then identification of the
  representing vector.  The identification silently uses that `𝒜₀` is a core for `L²`, i.e. essential self-adjointness of `L²` on `𝒜₀`
  (the hypothesis `FullTriple.Core2`, ERRATA R15-1).  Rounds 17-19 proved `Core2` for Gibbs triples only under growth conditions
  (`BddJet`, `GrowHess`, `PolyHess` on `ℝ`; `BddHess3`, `GrowHess3` on `ℝ^d`; `CoreCut` for `EllData`).
* **What we do instead (this stream)**: `Core2` is NOT used, and no growth condition on `V` is used.  Route:
  1. (BGL Prop. 3.3.6 (i), already in the repo as `FullTriple.mem_domain_of_ESA`) essential self-adjointness of `L` on `𝒜₀` (F10; proved for every Gibbs triple,
     `gibbsFull_unconditional`) gives `𝒟(L*) = 𝒟(L̄)`: a smooth `f ∈ L²` with `L f ∈ L²` belongs to `𝒟(L̄)` and `L̄[f] = [Lf]`.
  2. It remains to show `L f ∈ L²(μ)`.  This is proved by a cut-off (Caccioppoli) estimate in the spirit of BGL Prop. 3.2.1 (p. 142), applied to `Γ₂`
     instead of `Γ`: for `χ ∈ C_c^∞`,
     `∫χ²(Lf)² = ∫χ²Γ₂(f) + ∫χ Γ(χ, Γ f) − 2∫χ (Lf) Γ(χ,f)`
     (definition of `Γ₂ = ½(LΓ(f) − 2Γ(f,Lf))` and two integrations by parts, F7).  The last term is absorbed by Young; the cross term
     `Γ(χ, Γ f) = 2 Hess f(∇χ,∇f)` is controlled by `|Hess f|² = Γ₂(f) − Hess V(∇f,∇f) ≤ Γ₂(f) + |ρ| Γ(f)` (Bochner formula + `Hess V ≥ ρ`),
     with `Γ(f), Γ₂(f) ∈ L¹` and `|∇χ_n| ≤ K`, `χ_n → 1` (completeness cut-offs).  Fatou gives `L f ∈ L²`.
* **Why**: the existence of such an argument was observed after R19; it shows that the converse of 3.3.17 for Gibbs triples needs only ESA of `L`
  (which holds for all `V`) and the cut-off Bochner identity; `Core2` (ESA of `L²`, a genuinely 4th-order statement) is not needed.
* **Hypotheses that differ**: BGL needs `CD(ρ,n)` abstractly plus (implicitly) the core of `L²`.  We need: `V'' ≥ ρ` (resp. `HessGe V ρ`, any sign of `ρ`),
  `f ∈ 𝒜`, `f ∈ L²`, `Γ(f), Γ₂(f) ∈ L¹` — nothing on `V`, `V'''`, `∇³V` beyond smoothness and integrability of `e^{-V}` (the `GibbsData`
  structure); ergodicity (S10) not used.  The use of the Hessian-type bound is specific to the Gibbs (flat metric) structure
  (`Γ₂ = f''² + V'' f'²`, resp. `|Hess f|² + Hess V(∇f,∇f)`), whereas BGL's abstract statement is for any Full Markov Triple.
* `Core2` is not needed, and the `Core2*` results (R17-R19) remain valid independent facts; they are not used by the new theorems.

## Targets (names in `MarkovTriple.BGL.Instances.Gibbs`, resp. `MarkovTriple.BGL.Instances.GibbsRd`)

* **D1-1 (1-D)** `GibbsData.gibbs_mem_domain_of_Γ₂_direct {ρ : ℝ} (hρ : ∀ x, ρ ≤ deriv (deriv G.V) x) {f : ℝ → ℝ}
  (hf : f ∈ G.gibbsFull_unconditional.A) (hf2 : MemLp f 2 G.μ) (hG : Integrable (FullTriple.G G.gibbsFull_unconditional f f) G.μ)
  (hG2 : Integrable (G.gibbsFull_unconditional.toDiffusionTriple.Γ₂ f f) G.μ) :
  ∃ hF : hf2.toLp f ∈ G.gibbsFull_unconditional.toDiffusionTriple.generator.domain,
    ((G.gibbsFull_unconditional.toDiffusionTriple.generator ⟨hf2.toLp f, hF⟩ : Lp ℝ 2 G.μ) : ℝ → ℝ) =ᵐ[G.μ] G.gibbsFull_unconditional.L f`
  (same conclusion as `gibbs_mem_domain_of_Γ₂`; no `BddJet`/`PolyHess`/`Core2`).
* **D1-2 (1-D, the key estimate)** `GibbsData.memLp_Lg_of_Γ₂ {ρ} (hρ) {f} (hf : Sm f) (hf2 : MemLp f 2 G.μ) (hG : Integrable (Go f f) G.μ)
  (hG2 : Integrable (fun x => f'' x ^ 2 + V'' x * f' x ^ 2) G.μ) : MemLp (Lg G.V f) 2 G.μ`.
* **D1-3 (`ℝ^d`)** `GibbsRdData.gibbsRd_mem_domain_of_Γ₂_direct {ρ : ℝ} (hρ : HessGe G.V ρ) {f : Rd d → ℝ}
  (hf : f ∈ G.gibbsRdFull_unconditional.A) (hf2 : MemLp f 2 G.toEll.μ) (hG : Integrable (FullTriple.G G.gibbsRdFull_unconditional f f) G.toEll.μ)
  (hG2 : Integrable (G.gibbsRdFull_unconditional.toDiffusionTriple.Γ₂ f f) G.toEll.μ) :
  ∃ hF : hf2.toLp f ∈ G.gibbsRdFull_unconditional.toDiffusionTriple.generator.domain,
    ((G.gibbsRdFull_unconditional.toDiffusionTriple.generator ⟨hf2.toLp f, hF⟩ : Lp ℝ 2 G.toEll.μ) : Rd d → ℝ) =ᵐ[G.toEll.μ]
      G.gibbsRdFull_unconditional.L f`.
* **D1-4 (`ℝ^d`, key estimate)** `GibbsRdData.memLp_Lr_of_Γ₂ {ρ} (hρ : HessGe G.V ρ) {f} (hf : Sm f) (hf2) (hG : Integrable (Gr f f))
  (hG2 : Integrable (‖Hess f‖² + Hess V(∇f,∇f))) : MemLp (Lr G.V f) 2 G.toEll.μ`.
* **D1-5 (witnesses, NOT in any previous class)**: 1-D `V = exp(x²)`-type is in `PolyHess`, hence NOT new; new witnesses in `AUDIT_R20_DIRECT.md`:
  a potential `V = x²/2 + Σ_k ε_k φ((x − k) k²)`-type with `V'' ≥ 1` and `V'''` not polynomially dominated by `V'`
  (hypotheses of D1-1 exhibited non-vacuously), and `V = exp(x²)`, `V = x⁶ + x²/2` (no growth lemma used).  Witness statements are `example`s /
  theorems `spikyGibbs_hρ`, `spikyGibbs_not_polyHess`, `spikyGibbs_mem_domain_of_Γ₂` (see Status for what was formalised).
* Axioms of all new theorems: `propext`, `Classical.choice`, `Quot.sound` only.

## Not claimed
* `Core2` (still open for general `V`); nothing here changes the Core2* results.
* `EllData`/`RiemData` (variable metric): not attempted in this stream (cross term needs the abstract analogue of `|Hess f|²`).

## Status
All targets D1-1 ... D1-5 are PROVED (build green; axioms `propext`, `Classical.choice`, `Quot.sound`, `Gibbs/AxiomCheckR20Direct.lean`; audit
`BGL/AUDIT_R20_DIRECT.md`).  Files: `Gibbs/DirectCore.lean` (D1-2, `memLp_Lg_of_Γ₂`), `Gibbs/DirectMain.lean` (D1-1), `GibbsRd/DirectCore.lean` (D1-4,
`memLp_Lr_of_Γ₂`), `GibbsRd/DirectMain.lean` (D1-3), `Gibbs/DirectExample.lean`, `GibbsRd/DirectExample.lean`, `Gibbs/DirectOld.lean` (D1-5).

Logged deviations (none weakens a statement):
* **R20-D1-1 (strengthening)**: the key estimates `memLp_Lg_of_Γ₂` / `memLp_Lr_of_Γ₂` do not need the hypothesis `MemLp f 2` stated in D1-2/D1-4
  (`Lf ∈ L²` follows from `Γ(f), Γ₂(f) ∈ L¹` and `V'' ≥ ρ` alone); `f ∈ L²` is used only in the final theorems D1-1/D1-3 (to form the class `[f]`).
  The proved lemmas therefore have one hypothesis fewer than stated.
* **R20-D1-2 (names)**: the witness theorems are named `spikyGibbs_convex` (`V'' ≥ 1`, i.e. `ρ = 1`; the draft name `spikyGibbs_hρ`), `spikyGibbs_not_polyHess`,
  `spikyGibbs_mem_domain_of_Γ₂` (1-D) and `spikyData_witness`, `spikyData_not_growHess3`, `spikyData_mem_domain_of_Γ₂` (`ℝ^d`).  The spiky potential is NOT
  of the form `x²/2 + Σ ε_k φ(...)`: it is the double primitive of `V'' = 2 + sin(e^{x²})` (`V''' = 2x e^{x²} cos(e^{x²})`, `|V'| ≤ 3|x|`), which is cheaper to formalise
  and has the same property (`V'''` not polynomially dominated by `V'`).  Non-vacuity with a concrete `f`: `spikyGibbs_id_mem_domain` (`f = id`).
* **R20-D1-3 (scope)**: `EllData`/`RiemData` not attempted (see "Not claimed").  `Core2` is not used; `FullTriple.mem_domain_of_Γ₂` (abstract, conditional on `Core2`) is unchanged.
* The manifest hash of this file was refreshed after this Status section was added (own entry only).
