# Round 20, Stream D2 (the converse of BGL Prop. 3.3.17 WITHOUT `Core2` / `CoreCut` for `EllData d`, `RiemData d`): statements fixed BEFORE the proofs.

Change only by a logged erratum in `ERRATA.md` (prefix `R20-D2-`); deviations go to the `Status` section at the end.

## DIFFERENCE FROM BGL
* **What BGL does** (Prop. 3.3.17, p. 161-162, converse): for `f ∈ 𝒜 ∩ L²` with `Γ(f), Γ₂(f) ∈ L¹` one shows that the linear form
  `h ↦ ∫ f L²h`-type form `ℓ_f` is bounded for the graph norm of `(1−L)` on `𝒜₀` and extends it to `L²` by density of
  `(L² + Id)𝒜₀` (spectral decomposition); this silently needs that `𝒜₀` is a core for `L²` (ERRATA R15-1; formalised as the
  hypothesis `FullTriple.Core2` of `Extension/Converse.lean`, proved in R17-R19 only under growth assumptions: `CoreCut` for
  `EllData`/`RiemData`, `GrowHess3`, `PolyHess`, ...).
* **What we do instead** (closer to BGL's Prop. 3.2.1, p. 142, the cut-off / Caccioppoli technique, applied to `Γ₂`): we prove
  directly `L f ∈ L²(μ)` for smooth `f` with `Γ(f), Γ₂(f) ∈ L¹`, by the cut-off identity (`φ = χ²`, `χ` a completeness cut-off)
  `∫ χ²(Lf)² = ∫ χ²Γ₂(f) + ∫ χ Γ(χ, Γ f) − 2 ∫ χ Lf Γ(χ, f)`
  (Bochner `Γ₂ = ½LΓ − Γ(·,L·)` and two integrations by parts), and then use the EXISTING abstract result (BGL Prop. 3.3.6 (i), from ESA
  F10; `FullTriple.mem_domain_of_ESA`): `f ∈ 𝒜 ∩ L²`, `Lf ∈ L²` ⇒ `[f] ∈ 𝒟(L)`, `L[f] = [Lf]`. `Core2` is never used.
* **Why**: (a) `Core2` is a much stronger statement than the converse needs (essential self-adjointness of `L²` on `𝒜₀`); the
  converse only needs `Lf ∈ L²`, and ESA of `L` (F10, proved for `EllData` as `fullU`) identifies the maximal operator with the
  closure. (b) The cross term `Γ(χ, Γ f) = 2 Hess f(∇χ, ∇f)` is controlled by `|∇χ|` alone through
  `|Γ(χ,Γf)|² ≤ 4 Γ(χ) Γ(f) (Γ₂(f) − ρΓ(f))` (a Hessian Cauchy–Schwarz, valid in the Riemannian chart because
  `Γ₂(f) − ρΓ(f) ≥ ‖Hess f‖²_g` by Bochner `riem_bochner` and `Ric + ∇∇W ≥ ρ g`), so neither `Lχ`, `Γ₂(χ)`, `L²χ`, `Γ(Lχ)` nor
  any growth condition on `a` or `w` is needed. `|∇χ|_g ≤ 1` is exactly Def. 3.3.9 completeness (`a_exh`, `diff_isComplete`).
* **Hypotheses that differ**: here ONLY `Curv ρ` (`ρ ∈ ℝ` of any sign) and the completeness field of the data (`a_exh`/`g_exh`);
  NO `CoreCut`, NO `Core2`, NO growth of `∂a`, `∇ log w`. In particular the hyperbolic plane `hypRiem` (`Curv 1`, no `CoreCut`,
  `AUDIT_R19_CORE2ELL.md` §6) is covered. `Core2`/`CoreCut` results of R17-R19 stand as independent facts (they prove something
  stronger about `L²`); we do not claim `Core2` for `hypRiem`.
* Note: neither `f ∈ L²` nor `ρ > 0` is used in the estimate `Lf ∈ L²`; `f ∈ L²` is only needed to speak of `[f] ∈ 𝒟(L)`.

Setting: `E : EllData d`, `L f = w⁻¹ Σᵢ ∂ᵢ(w Σⱼ aᵢⱼ ∂ⱼ f)`, `Γ(f,g) = Σ aᵢⱼ ∂ᵢf ∂ⱼg`, `μ = Z⁻¹ w dx`, `𝒜 = C^∞(ℝ^d)`, `𝒜₀ = C_c^∞`,
`E.fullU` the proved Full triple of R19 (`WeakHypo`, `F8` proved).

## Targets
* **D1** (`GibbsRd/DirectEllCut.lean`) `EllData.exists_gradCut (E) : ∃ χ : ℕ → Rd d → ℝ`, with `Sm (χ n)`, compact support, `0 ≤ χ n ≤ 1`,
  `Γ(χ n) ≤ 1` everywhere, `χ n x → 1` for `μ`-a.e. `x` (from `diff_isComplete`, i.e. `a_exh`).
* **D2** (`GibbsRd/DirectEllCore.lean`) `def EllData.HessCS (ρ) : Prop := ∀ f u, Sm f → Sm u → ∀ x, (Γ u (Γ f f) x)² ≤ 4 Γ(u)(x) Γ(f)(x) (G2 f f x − ρ Γ f f x)`
  and `theorem EllData.memLp_L_of_hessCS (hρ : E.Curv ρ) (hH : E.HessCS ρ) (hf : Sm f) (hG : Integrable (E.Γ f f) E.μ) (hG2 : Integrable (E.G2 f f) E.μ) : MemLp (E.L f) 2 E.μ`.
* **D3** (`Riemannian/DirectRiemHess.lean`) the Hessian Cauchy–Schwarz `RiemData.riem_hessCS (hρ : R.Curv ρ) : R.toEll.HessCS ρ` (Bochner + `riem_ricci_of_curv`).
* **D4** (`Riemannian/DirectRiemTransport.lean`) every `E : EllData d` is the `toEll` of a `RiemData`: `EllData.toRiem`, `EllData.toRiem_toEll : E.toRiem.toEll = E`;
  hence `EllData.hessCS_of_curv (hρ : E.Curv ρ) : E.HessCS ρ`.
* **D5** (`GibbsRd/DirectEllMain.lean`) the converse of Prop. 3.3.17 without `Core2`/`CoreCut`:
  `theorem EllData.ell_mem_domain_of_Γ₂_direct {ρ : ℝ} (hρ : E.Curv ρ) {f : Rd d → ℝ} (hf : f ∈ E.fullU.A) (hf2 : MemLp f 2 E.μ)
  (hG : Integrable (FullTriple.G E.fullU f f) E.μ) (hG2 : Integrable (E.fullU.toDiffusionTriple.Γ₂ f f) E.μ) :
  ∃ hF : hf2.toLp f ∈ E.fullU.toDiffusionTriple.generator.domain, ((E.fullU.toDiffusionTriple.generator ⟨hf2.toLp f, hF⟩ : Lp ℝ 2 E.μ) : Rd d → ℝ) =ᵐ[E.μ] E.fullU.L f`
  (same conclusion shape as `EllData.ell_mem_domain_of_Γ₂`, hypotheses `hρ` only).
* **D6** (`Riemannian/DirectRiemMain.lean`) `RiemData.riem_mem_domain_of_Γ₂_direct {ρ} (hρ : R.Curv ρ) ...` (same shape as `riem_mem_domain_of_Γ₂`, no `hC`).
* **D7** (non-vacuity, `Riemannian/DirectRiemMain.lean`) `hypRiem` (`Curv 1`, no `CoreCut`) and `confRiem` (`Curv 2`): the theorems apply to every `f ∈ 𝒜₀`
  (hypotheses automatic), and `Curv ρ` has `ρ > 0` witnesses outside the `CoreCut` class; `#print axioms` only `propext`, `Classical.choice`, `Quot.sound`
  (`Riemannian/AxiomCheckR20DirectEll.lean`).

## Status
D1-D7 PROVED as stated (names as in the statements; `EllData.cutoff_identity`, `cutoff_bound`, `ell_mem_domain_of_hessCS`, `RiemData.hess_cs`, `hessNorm_le_G2'`, `EllData.ext'`, `detA`, `Wr`
are auxiliary).  Deviations / clarifications (ERRATA R20-D2-*):
* D2's hypothesis `hG2` is stated for the formula `E.G2 f f` (equal to `Γ₂ f f` pointwise; `ell_mem_domain_of_hessCS` converts the `Γ₂` of the Full triple); `HessCS` is proved for every `E` from `Curv ρ` (D4), so D5/D6 have `Curv ρ` only.
* D7: `hypRiem_mem_domain_of_A₀_direct` / `EllData.ell_mem_domain_of_A₀_direct` discharge the hypotheses for every test function; "no `CoreCut` for `hypRiem`" is the R19 by-hand argument, not formalised.
* `Core2EllCalc`/`Core2EllEnergy`/`Core2EllMain` are imported only for the calculus lemmas (`G2`, `G2'`, `Γ_leib`, `sm_G2`) and the definition `EllData.fullU`; no `Core2`/`CoreCut` result is used.
Files: `GibbsRd/DirectEll{Cut,Core,Main}.lean`, `Riemannian/DirectRiem{Hess,Transport,Main}.lean`, `Riemannian/AxiomCheckR20DirectEll.lean` (axioms: only `propext`, `Classical.choice`, `Quot.sound`).
