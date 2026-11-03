# AUDIT R16 E3 (self-attack, Armstrong method): higher interior regularity

Targets: `Instances/GibbsRd/STATEMENTS_R16_E3.md`.  Files `EllipticE3A`-`E3D`, `AxiomCheckR16E3`.  No `sorry`, no `set_option`, standard axioms.

## 1. Vacuity of H
`EllData.veryWeakSol_of_smooth` proves `Sm u ⇒ VeryWeakSol u (E.L u)`; with `g i = pderiv u i` (`weakDeriv_of_smooth`) and `LocL2` of smooth
functions (`LocL2.of_smooth`) H is satisfiable by every smooth function with `h = L u`; and `Sobolev k (L u)` for all `k` (`Sobolev.of_smooth`, `sm_L`),
so the final theorem's hypotheses are non-vacuous.  Conclusion is then trivially true there; no contradiction possible since `WeakDeriv` uses `C^∞` test functions (not `ω`).

## 2. Derivation checked
`w L a = Σᵢ ∂ᵢ Pᵢ(a)`, `∂_m Pᵢ(a) = Qᵢ(a) + Pᵢ(∂_m a)` uses `∂_m∂ⱼ a = ∂ⱼ∂_m a` (`pderiv_symm`, `a` smooth) and `∂_m∂ᵢ Pᵢ = ∂ᵢ∂_m Pᵢ` (Pᵢ smooth).
Weak step: test `w L a ∈ A₀` against `∂_m u` (WeakDeriv of `u`, direction `m`), `Qᵢ a ∈ A₀` against `∂ᵢu`, `∂_m a ∈ A₀` in the equation of `u`,
`a` against `Bᵢⱼ ∂ᵢu` (direction `j`, product rule `WeakDeriv.smooth_mul`) and `w h` (direction `m`).  Signs verified in Lean (no free constants).
Commutation of weak derivatives is NOT used (only of classical derivatives of smooth test functions).  `Bᵢⱼ = ∂_m(w aᵢⱼ)` is `C^∞` (`sm_Bc`), so `Bᵢⱼ Gᵢⱼ`, `∂ⱼBᵢⱼ gᵢ` are in `H^k` by `Sobolev.smooth_mul`.

## 3. Induction bookkeeping
`interior_sobolev (k+1)`: `Sobolev (k+1) h ⇒ Sobolev k h`, IH gives `u ∈ H^{k+2}`, hence `gᵢ ∈ H^{k+1}`, `Gᵢⱼ ∈ H^k` with the weak-derivative witnesses CHOSEN from the
`Sobolev` structure (not the given `g`: the given `g` is only used via `hg`, and `g'` is a.e. equal by `WeakDeriv.unique`, never needed).  `h' ∈ H^k` needs `h, H_m ∈ H^k`, `gᵢ ∈ H^k`, `Gᵢⱼ ∈ H^k`: all available.
Then IH(k) applied to `(g' m, h')` gives `g' m ∈ H^{k+2}` hence `u ∈ H^{k+3}`.  Both the equation for `g' m` and its `WeakDeriv` data come from the same chosen witnesses.

## 4. d = 0, 1
`d = 0`: `Fin 0` empty; everything is vacuous/sums empty (`m : Fin 0` does not exist); `interior_sobolev` still holds (it follows from `interior_H2_sobolev`, whose requirement `∀ i` is empty).
`d = 1`: `Bc` is `(w a)'`, sums have one term; no special-casing.

## 5. Compatibility of the two Sobolev predicates
`Elliptic.WeakDeriv`/`LocL2` and `Sob.WeakDeriv`/`LocL2` are `Iff.rfl`-equal (the cast `((⊤:ℕ∞):WithTop ℕ∞)` is the `∞` of Mathlib's `ContDiff` notation); `sobolev_iff_hasSobL2` by induction.

## 6. Honest remarks
* The E3 hypotheses require `Sobolev k h` for all `k` in the final interface; for the glue, `h = Z⁻¹`-multiple of a smooth right-hand side or a resolvent combination `λu − f` with smooth `f`: that needs `u ∈ H^k` first, a bootstrap (`h = λ u − f`, `Sobolev k h ⇐ Sobolev k u`): use `interior_sobolev` inductively: `Sobolev k u ⇒ Sobolev k h ⇒ Sobolev (k+2) u`.  The glue must organise it; not done here.
* The starting point still needs `u ∈ H¹_loc` (Friedrichs step), not provided here.
* `d` is arbitrary; no lower-order terms.

## 7. Attack surface (for the hostile auditor)
1. `EllData.hprime` formula and the sign of the `Σ ∂ⱼ(Bᵢⱼgᵢ)` term (checked only by the Lean proof of `veryWeakSol_deriv`).
2. `interior_sobolev`: choice of witnesses; use of `Sobolev.mono`, `Sobolev.smooth_mul`, `Sobolev.finset_sum` (new, in `namespace Elliptic`).
3. `interior_regularity_all_orders` weakens `Sobolev (k+2) ⇒ Sobolev k` via `mono` twice (trivial).
4. `sobolev_iff_hasSobL2` being `Iff.rfl`-based: confirms identical definitions; check the cast `∞`.
5. `veryWeakSol_of_smooth`: uses `Γ` symmetry via `a_symm`.
6. Everything depends on `interior_H2_sobolev` (E2) and `weakForm_extend` (previous batches), and on `smooth_of_weak_all_orders` (Sob branch).
