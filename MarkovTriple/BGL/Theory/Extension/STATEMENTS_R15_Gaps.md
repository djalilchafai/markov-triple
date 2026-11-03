# Round 15 (gap closure for Prop. 3.3.16, audit of round 14): target statements, fixed BEFORE the proofs
(changes only by a logged erratum at the end of this file).  Source: BGL p. 160 (Prop. 3.3.16 (iv), (v)) and Prop. 3.1.5.
Setting: `T : FullTriple E`, `hCD : T.CD ρ n` (any `n`; ESA is a field of `FullTriple`).  Notation: `D(L) = T.toDiffusionTriple.generator.domain`,
`L u := generator ⟨u,hu⟩`, `jL a = ([a],[La])`, `‖(u,Lu)‖` = sup norm of `L² × L²` (the graph norm up to a constant),
`‖x‖_E = ‖qEquiv.symm x‖` in `KE` (the Hilbert norm `(‖·‖₂² + ℰ)^{1/2}` of `𝒟(ℰ)`, E3 of STATEMENTS_R14.md).
All equalities of `Lp` elements are equalities in `L¹` (i.e. a.e. as functions).  Linear combinations are stated as
`w = u + c • u'` (the target element `w`, with its own membership proof, is a parameter, to avoid dependent rewriting).

## (1) `hessE` (HessExtLin.lean)
* `hessE_lin_left` : `w = u + c•u'` (in `Lp ℝ 2`) ⇒ `hessE hCD w hw g h = hessE hCD u hu g h + c • hessE hCD u' hu' g h`.
* `hessE_lin_mid`  : `w = g + c•g'` (in `T.formDomain`) ⇒ `hessE hCD u hu w h = hessE hCD u hu g h + c • hessE hCD u hu g' h`.
* `hessE_lin_right`: `h'' = h + c•h'` (in `T.A₀`) ⇒ `hessE hCD u hu g h'' = hessE hCD u hu g h + c • hessE hCD u hu g h'`.
* `hessE_bound`: for every `h : T.A₀` there is `C ≥ 0` with, for all `u ∈ D(L)`, `g ∈ 𝒟(ℰ)`:
  `‖hessE hCD u hu g h‖ ≤ C * ‖(u, L u)‖ * ‖qEquiv.symm g‖` (`C` depends only on `h`, `ρ`, not on `u, g`).
* `hessE_cls`: for `a b h ∈ 𝒜₀`: `hessE hCD [a] (cls_mem_generator_domain a) (clsQ b) h = HH T a b h`
  (the class of `H(a)(b,h)`; with `HH_ae`: `= Hess T a b h` a.e.).

## (2) Prop. 3.3.16 (v), 2nd and 3rd statements (HessExtLin.lean)
* `hessE_tendsto_left`: `f : ι → D(L)`, `f₀ : D(L)`, a filter `l` on `ι`, `((f i).1, L (f i)) → (f₀.1, L f₀)` in `L² × L²` along `l`
  (graph convergence), `g ∈ 𝒟(ℰ)`, `h ∈ 𝒜₀` ⇒ `hessE hCD (f i).1 (f i).2 g h → hessE hCD f₀.1 f₀.2 g h` in `L¹` along `l`.
* `hessE_tendsto_mid`: fixed `u ∈ D(L)`, `g : ι → 𝒟(ℰ)`, `g₀`, with `qEquiv.symm (g i) → qEquiv.symm g₀` in `KE` along `l`
  ⇒ `hessE hCD u hu (g i) h → hessE hCD u hu g₀ h` in `L¹`.

## (3a) bilinear `Γ₂` (Gamma2ELin.lean)
* `GG2_self : GG2 T a a = G2cls T a` (`a : 𝒜₀`).
* `gamma2E_lin_left`, `gamma2E_lin_right` (as above), `gamma2E_comm : gamma2E u v = gamma2E v u`,
  `gamma2E_bound : ‖gamma2E hCD u v hu hv‖ ≤ (2(1+|ρ|)+4|ρ|) ‖(u,Lu)‖ ‖(v,Lv)‖`,
  `gamma2E_cls : gamma2E [a] [b] = GG2 T a b`, `gamma2E_self_tendsto`: `G2cls (a k) → gamma2E u u` for graph-convergent `a_k → u`.
* `Γ₂_ext_eq_gamma2E`: for `f ∈ 𝒜`, `MemLp f 2`, `[f] ∈ D(L)`: `gamma2E hCD [f] [f] hu hu =ᵐ Γ₂ f f` (links Prop. 3.3.17's `Γ₂_ext_eq`
  to the bilinear `gamma2E`).

## (3b) `Γ` on `𝒟(ℰ)` (GammaELin.lean)
* `gammaE_lin_left`, `gammaE_lin_right` (linear combinations in `T.formDomain`), `gammaE_bound : ‖gammaE u v‖ ≤ ‖u‖_E ‖v‖_E`,
  `gammaE_self_nonneg : 0 ≤ᵐ gammaE u u`, `gammaE_cs : ∀ᵐ x, (gammaE u v x)^2 ≤ gammaE u u x * gammaE v v x` (the Cauchy–Schwarz
  `|Γ(u,v)|² ≤ Γ(u)Γ(v)` promised in STATEMENTS_R14.md S1; symmetry is `gammaE_comm`, existing).

## (4) Documentation: ERRATA.md E5 (R15-G) and a superseding status table in STATEMENTS_R14.md.

## Errata log (R15)
(none yet)
