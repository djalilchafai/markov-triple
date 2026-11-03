# Round 16: Bochner's formula for a weighted Riemannian chart with variable co-metric (target statements)

Written BEFORE any proof (Armstrong step (a)).  Source: BGL Sect. 1.16 ((1.16.4), (1.16.5), (1.16.8)), App. C.3
(Thm C.3.2, (C.3.1) `Ric_ij = R_{ki}^k_j`, (C.3.3)), Sect. 1.11.3.  Setting: `R : RiemData d` of
`Riemannian/Data.lean` (global chart `R^d`, co-metric `g^{ij}` = `R.g`, `W = R.W`, `L = Δ_g - ∇W·∇`,
`Γ₂` = the library's formula `½(LΓ(f) − 2Γ(f,Lf))`, `R.riemDiff.Γ₂`).  Changes only by a logged erratum in `ERRATA.md`.

## Definitions (coordinate formulas of the book; all functions `R^d → ℝ`)

* `gl i j x := ((g^{ij}(x))⁻¹)_{ij}` : the metric `G = (g_{ij})`, the inverse matrix of the co-metric (App. C.3: `G* = g`).
* `chr k i j x := ½ Σ_p g^{kp} (∂_i g_{jp} + ∂_j g_{ip} − ∂_p g_{ij})` : Christoffel symbols `γ_{ij}^k` (Thm C.3.2).
* `hess u i j x := ∂_i ∂_j u − Σ_k γ_{ij}^k ∂_k u` : the Hessian `∇∇u` (C.3.2 / `∇_i w_j = ∂_i w_j − γ_{ij}^k w_k`).
* `riem i j k l x := ∂_i γ_{jl}^k − ∂_j γ_{il}^k + Σ_p (γ_{ip}^k γ_{jl}^p − γ_{jp}^k γ_{il}^p)` : the Riemann tensor
  `R_{ij}{}^k{}_l`, defined by `(∇_i∇_j − ∇_j∇_i) Z^k = R_{ij}{}^k{}_l Z^l` (App. C.3, p. 507), torsion-free.
* `ricci i j x := Σ_k R_{ki}{}^k{}_j` (C.3.1).
* `beRicci i j x := ricci i j x + hess W i j x` : the weighted (Bakry-Emery) tensor `Ric_g + ∇∇W`.

## Targets

* **T1 (first-order identities)** for every smooth `u`: `Γ`-gradient `∂_k Γ(u) = 2 Σ g^{ij} ∇_k∇_i u ∂_j u` ((1.16.x) first-order
  identity); Laplacian `L u = Σ g^{ij} hess u i j − Σ g^{ij} ∂_iW ∂_j u` (book (C.3.3) with (1.11.10)); torsion-free,
  metric compatibility `∂_k g^{ij} = −Σ_m(γ_{km}^i g^{mj} + γ_{km}^j g^{im})`.
* **T2 (Bochner, (1.16.4) and (1.16.5), Thm C.3.3)**: for every `f` with `Sm f` and every `x`
  `R.riemDiff.Γ₂ f f x = Σ_{ijkl} g^{ik} g^{jl} H_{ij} H_{kl} + Σ_{ijkl} (Ric+Hess W)_{ij} (g^{ik}∂_k f)(g^{jl}∂_l f)`,
  `H = hess f`.
* **T3 (criterion, (1.16.8))** `riem_curv_of_ricci`: if for all `x` and all `ξ ∈ R^d`
  `ρ Σ g_{ij}(x) ξ^i ξ^j ≤ Σ (Ric+Hess W)_{ij}(x) ξ^i ξ^j` (i.e. `Ric_g + ∇∇W ≥ ρ g`), then `R.Curv ρ`.
  Needs `‖Hess f‖²_HS ≥ 0` (positive definiteness of `g^{ij}`).
* **T4 (hand checks)** `d = 1`: `ricci = 0`; flat metric `ofGibbs`: `chr = 0`, `ricci = 0`, `hess = ∂∂`.
* **T5 (non-flat inhabitant)**: see `AUDIT_R16_BOCHNER_SELF.md` and the status at the end of this file.

## Addendum (written after the proofs; no target above was changed)

Lean names (all in `MarkovTriple/BGL/Instances/Riemannian/`, namespace `MarkovTriple.BGL.Instances.Riemannian.RiemData`
unless noted; `R : RiemData d`):

| Target | Lean declaration (file) |
| --- | --- |
| definitions `gl`, `chr1`, `chr`, `hess`, `riem`, `ricci`, `beRicci` | `Curvature.lean`, `CurvInv.lean` (`gl`) |
| T1 symmetry / compatibility | `chr_symm`, `pderiv_g_chr` (`Curvature.lean`) |
| T1 `Σ γ_{ib}^b = ∂ log w_g`, Jacobi | `trace_chr`, `pderiv_log_wg`, `pderiv_detg` (`CurvLap.lean`, `CurvInv.lean`) |
| T1 `L u = Σ g^{ij}∇_i∇_ju − Σ g^{ij}∂_iW∂_ju` | `L_eq_hess` (`CurvLap.lean`) |
| T1 `∂_kΓ(u,v)` | `pderiv_GamF`, `pderiv_GamF_self` (`CurvCov.lean`) |
| Ricci identity, antisymmetry of lowered `R` | `cov3_ricci` (`CurvCov.lean`), `riem_antisymm` (`CurvRiem.lean`) |
| T2 Bochner (1.16.4) | `riem_bochner` (`BochnerRiem.lean`); right side `‖H‖²_HS + Σ BE_{ij} ∇^if ∇^jf`, `∇^if = grad f i` |
| T3 criterion (1.16.8) | `riem_curv_of_ricci` (`BochnerCrit.lean`), `hessNorm_nonneg` |
| T4 | `ricci_fin_one`, `ofGibbs_chr`, `ofGibbs_ricci`, `ofGibbs_bochner` (`BochnerChecks.lean`) |
| T5 | `confRiem`, `confRiem.ricci_eq`, `confRiem.hess_W`, `confRiem.curv`, `confRiem_poincare`, ... (`BochnerExample.lean`) |

T2 form used in Lean: `∑ i j k l, g i k * g j l * hess f i j * hess f k l + ∑ i j, beRicci i j * grad f i * grad f j`.
T5 content: `confRiem : RiemData 2`, `g^{ij} = e^{-|x|²}δ`, `W = 2e^{|x|²}`; `Ric = −2δ`, `∇∇W = 4e^{|x|²}(1+|x|²)δ`,
`Curv 2` unconditionally; Poincaré/gap/decay/`CD` only under the named hypotheses `WeakHypo` (and `F8`).
Status: T1-T5 proved, no `sorry`, standard axioms only.  Not proved: `WeakHypo`, `F8` (unchanged from earlier rounds).
