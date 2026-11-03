# STATEMENTS R16 E3 (Armstrong method): higher interior regularity, written BEFORE the proofs

Namespace `MarkovTriple.BGL.Instances.GibbsRd`; files `EllipticE3*.lean`.  Textbook: Evans PDE §6.3.1 Thm 2 (higher interior regularity;
infinite differentiability is Thm 3), Gilbarg–Trudinger Thm 8.10.  Hypotheses "H" as in `STATEMENTS_R16_E2.md`:
`E : EllData d`, `u h : Rd d → ℝ`, `g : Fin d → Rd d → ℝ`, `LocL2 u`, `∀ i, WeakDeriv u (g i) i`, `∀ i, LocL2 (g i)`, `LocL2 h`, `E.VeryWeakSol u h`.

## E3.1 (key step)  `EllData.veryWeakSol_deriv`
`E : EllData d`, `m : Fin d`, `LocL2 u`, `∀ i, WeakDeriv u (g i) i`, `E.VeryWeakSol u h`,
`∀ i j, WeakDeriv (g i) (G i j) j`, `WeakDeriv h H m` ⇒
`E.VeryWeakSol (g m) h'` where `h' x = (w x)⁻¹ * (w x * H x + pderiv w m x * h x − Σᵢⱼ (Bᵢⱼ x * Gᵢⱼ x + pderiv Bᵢⱼ j x * gᵢ x))`, `Bᵢⱼ = ∂_m(w aᵢⱼ)`.
(i.e. `w h' = ∂_m(h w) − Σᵢⱼ ∂ⱼ(∂_mAᵢⱼ gᵢ)`.)  `h'` is `L²_loc` if `h, H, gᵢ, Gᵢⱼ` are.

## E3.2 (induction)  `EllData.interior_sobolev`
H (with `E`), and `Sobolev k h` ⇒ `Sobolev (k+2) u`, for every `k : ℕ`.  (`k = 0` is `interior_H2_sobolev`.)

## E3.3 (core interface for the glue)  `interior_regularity_all_orders`
H and `∀ k, Sobolev k h` ⇒ `∀ k, Sobolev k u`; and, via the compatibility `Sobolev_iff_HasSobL2 : Sobolev k f ↔ Sob.HasSobL2 k f`
(`Elliptic.Sobolev` and `Sob.HasSobL2` have identical definitions up to the cast `∞`), `∃ φ, Sm φ ∧ u =ᵐ φ` (Sob.`smooth_of_weak_all_orders`).
Also `EllData.veryWeakSol_of_smooth`: `Sm u`, `h = E.L u` ⇒ `E.VeryWeakSol u h` (non-vacuity of H, with `g i = pderiv u i`).

## Status at the end of the batch (targets above unchanged; names exactly as stated, no erratum)
PROVED (0 sorry, axioms propext/choice/Quot.sound, `AxiomCheckR16E3.lean`):
* `EllData.comm_identity` (`EllipticE3A`): `∂_m(w L a) = Σᵢ ∂ᵢ(Qᵢ a) + w L(∂_m a)`, `Qᵢ a = Σⱼ Bᵢⱼ ∂ⱼ a`.
* E3.1 `EllData.veryWeakSol_deriv` (`EllipticE3B`), hypotheses weaker than stated (only `WeakDeriv`s, no `LocL2`).
* `EllData.sobolev_hprime`, E3.2 `EllData.interior_sobolev` (stated with `hu hg hgL hW hh`; `LocL2 h` is the `k = 0` part of `Sobolev k h`).
* E3.3 `EllData.interior_regularity_all_orders`, `EllData.interior_smooth_rep` (`∃ φ, Sm φ ∧ u =ᵐ φ`), `sobolev_iff_hasSobL2`, `weakDeriv_iff_sob`
  (both `Iff.rfl`), `EllData.veryWeakSol_of_smooth`.
* Note: the statement above wrote the compatibility lemma as `Sobolev_iff_HasSobL2`; the Lean name is `sobolev_iff_hasSobL2` (naming only, no mathematical change); `interior_sobolev` omits the redundant `LocL2 h` hypothesis (it is the `k=0` part of `Sobolev k h`).
