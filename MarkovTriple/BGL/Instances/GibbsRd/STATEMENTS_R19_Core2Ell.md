# Round 19, Stream A6 (`Core2` and the converse of BGL Prop. 3.3.17 for `EllData d` and `RiemData d`): statements fixed BEFORE the proofs.

Change only by a logged erratum in `ERRATA.md` (prefix `R19-Ell-`); deviations go to the `Status` section at the end.
All names in `MarkovTriple.BGL.Instances.GibbsRd` (Riemannian corollaries in `...Instances.Riemannian`).
Setting: `E : EllData d`, `L f = w⁻¹ Σᵢ ∂ᵢ(w Σⱼ aᵢⱼ ∂ⱼ f)`, `Γ(f,g) = Σ aᵢⱼ ∂ᵢf ∂ⱼg`, `μ = Z⁻¹ w dx`, `𝒜₀ = C_c^∞(ℝ^d)`,
Full triple `E.fullU := E.full E.weakHypo_unconditional E.f8_unconditional` (proved `WeakHypo`, `F8`, via `EllData.ellReg`).

## Mathematical plan (BGL Prop. 3.2.1 p. 142 cut-off; Def. 3.3.9; Prop. 3.3.17 p. 161-162; `Core2` of `Extension/Converse.lean`)
`Core2`: for `a ∈ 𝒜₀` find `b_n ∈ 𝒜₀` with `(1-L) b_n → a`, `L(1-L) b_n → L a` in `L²(μ)`.
The whole argument is written in the `L, Γ, Γ₂` calculus (no coordinates of `a`, `w`): this is what makes the commutators
`[L,χ_n]`, `[L²,χ_n]` (which in coordinates contain `∂a, ∂²a, ∂³a, ∇log w`) manageable.

1. *Resolvent.* `v = (1-L)⁻¹[a]` has a `C^∞` representative with `L v = v - a` classically (`EllData.ellReg` chain, as in R18 B3).
2. *Caccioppoli* (Prop. 3.2.1): with cut-offs `χ_n`, `Γ(χ_n) ≤ K`: `∫ χ_n² Γ(v) dμ ≤ ½∫a² + 4K∫v²`; Fatou: `Γ(v) ∈ L¹`.
3. *Cut-off Bochner* (replaces the R18 Hessian estimate; no Hessian of `v` is needed): with `Γ₂(f,g) := ½(LΓ(f,g) - Γ(Lf,g) - Γ(f,Lg))` (Def. 3.3.12)
   and `Curv ρ` (`ρ Γ(f) ≤ Γ₂(f)` on `C^∞`, `ρ ∈ ℝ` of any sign), the identity `∫ φ Γ₂(v) = ½∫ Γ(v) Lφ - ∫ φ Γ(v, Lv)` with `φ = χ_n²` (`|Lφ| ≤ 4K`)
   and Fatou give `Γ₂(v) - ρΓ(v) ∈ L¹` (it is `≥ 0`).
4. *Graph-norm cut-off.* `b_n = χ_n v ∈ 𝒜₀`; with `F = χ_n`:
   `L(Fv) - Lv = (F-1)Lv + vLF + 2Γ(F,v)`,
   `LL(Fv) - LLv = (F-1)LLv + 2 LF·Lv + 4Γ(F,Lv) + v LLF + 4Γ(LF,v) + 4Γ₂(F,v)`  (pure Leibniz rule + definition of `Γ₂`).
   Dominated convergence, using `|Γ(f,g)|² ≤ Γ(f)Γ(g)` and `|Γ₂'(f,g)|² ≤ Γ₂'(f)Γ₂'(g)` for `Γ₂' := Γ₂ - ρΓ ≥ 0` (Cauchy–Schwarz for a nonnegative symmetric
   bilinear form), and locality (`F = 1` near `x` ⇒ all commutator terms vanish at `x`).
5. *Assembly*: `FullTriple.mem_domain_of_Γ₂` (converse of Prop. 3.3.17) with `full_CD`.

## Hypothesis class `H` (the weakest our argument uses; stated on the data)
**C0** `def EllData.G2 (E) (f g : Rd d → ℝ) (x) : ℝ := (E.L (E.Γ f g) x - E.Γ (E.L f) g x - E.Γ f (E.L g) x) / 2`.
**C1** `structure EllData.CutFamily (E : EllData d) (χ : ℕ → Rd d → ℝ) : Prop` with fields
`smooth : ∀ n, Sm (χ n)`, `cs : ∀ n, HasCompactSupport (χ n)`, `mem : ∀ n x, 0 ≤ χ n x ∧ χ n x ≤ 1`,
`eventually_one : ∀ x, ∀ᶠ n in atTop, ∀ᶠ y in 𝓝 x, χ n y = 1`,
`bound : ∃ K, ∀ n x, E.Γ (χ n) (χ n) x ≤ K ∧ |E.L (χ n) x| ≤ K ∧ |E.L (E.L (χ n)) x| ≤ K ∧ E.Γ (E.L (χ n)) (E.L (χ n)) x ≤ K ∧ E.G2 (χ n) (χ n) x ≤ K`.
`def EllData.CoreCut (E) : Prop := ∃ χ, E.CutFamily χ` ("`E` admits a cut-off family with bounded `Γχ, Lχ, L²χ, Γ(Lχ), Γ₂(χ)`").
(BGL Def. 3.3.9 exhaustion cut-offs with the additional bounds on the first two `L`-jets that the `L²`-graph norm requires.)

## Targets
* **T1** (`Core2EllMain.lean`) `theorem EllData.ell_core2 {ρ : ℝ} (hρ : E.Curv ρ) (hC : E.CoreCut) : E.fullU.Core2`
  (hypotheses: ONLY a curvature lower bound of any sign and `CoreCut`; completeness `a_exh` is part of `EllData`).
* **T2** `theorem EllData.ell_mem_domain_of_Γ₂ {ρ} (hρ : E.Curv ρ) (hC : E.CoreCut) {f} (hf : f ∈ E.fullU.A) (hf2 : MemLp f 2 E.μ)
  (hG : Integrable (FullTriple.G E.fullU f f) E.μ) (hG2 : Integrable (E.fullU.toDiffusionTriple.Γ₂ f f) E.μ) :
  ∃ hF : hf2.toLp f ∈ E.fullU.toDiffusionTriple.generator.domain, ((E.fullU.toDiffusionTriple.generator ⟨hf2.toLp f, hF⟩ : Lp ℝ 2 E.μ) : Rd d → ℝ) =ᵐ[E.μ] E.fullU.L f`
  — the unconditional converse of Prop. 3.3.17.
* **T3** (`Riemannian/Core2RiemMain.lean`) for `R : RiemData d`: `RiemData.riem_core2 (hρ : R.Curv ρ) (hC : R.toEll.CoreCut) : R.riemFull_unconditional.Core2`
  and `RiemData.riem_mem_domain_of_Γ₂` (same conclusion as T2).
* **T4** (`Core2EllGibbs.lean`, recovery) `GibbsRdData.BddHess3.coreCut (hb : G.BddHess3) : G.toEll.CoreCut`; hence `G.toEll.ell_core2` for every Gibbs datum with `BddHess3`
  (`ρ` from `BddHess3.hessGe` and `gibbsRd_curv`): `GibbsRdData.gibbsRd_core2_via_ell`. (`ofGibbs` then gives the Riemannian flat case.)
* **T5** (non-vacuity, `ρ > 0`): `gaussData d`, `cosData d` satisfy `CoreCut` and `Curv ρ` (`ρ = 1, 1/2`); consequently `ell_core2`/`ell_mem_domain_of_Γ₂` are instantiated.
  Non-Gibbs (variable metric): the conformal plane `confRiem` (`Curv 2`) — attempted, see Status.
* **T6** (sufficient condition relative to `a_exh`, attempted) `EllData.JetExh`: a smooth proper `ψ ≥ 0`, `Γψ ≤ 1`, with `|Lψ| ≤ C(1+ψ)`, `|LLψ| ≤ C(1+ψ)`,
  `|LΓψ| ≤ C(1+ψ)²`, `Γ(Lψ) ≤ C(1+ψ)²`, `Γ(Γψ) ≤ C(1+ψ)⁴` implies `CoreCut` (cut-offs `σ(ψ/(n+1))`).
* **T7** (hyperbolic plane `hypRiem`, `V = 2cosh d`): decided mathematically in `AUDIT_R19_CORE2ELL.md`: the natural exhaustion `ψ = log(1+V)` has `|Lψ| ~ e^{ψ}`, so `JetExh`
  and `CoreCut` with radial cut-offs FAIL; neither `Core2` nor its negation is claimed for `hypRiem`.

## Status
(filled at the end of the round)
