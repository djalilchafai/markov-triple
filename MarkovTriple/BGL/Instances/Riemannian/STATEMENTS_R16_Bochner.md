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

## Status
(filled at the end of the round)
