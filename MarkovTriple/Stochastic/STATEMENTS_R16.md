# Round 16 (stochastic layer, "full fix"): frozen target statements

Written BEFORE any proof (Armstrong method).  Later changes only by a logged erratum in `ERRATA.md`.
All existing files untouched.  Namespace `MarkovTriple.Stochastic` (`.Circle`, `.Sphere` for instances).
Standing setting (as in R15): `X` compact, `T2`, second countable, Borel; `T : DiffusionTriple X`, `[IsFiniteMeasure T.μ]`.
`clsC μ f = ContinuousMap.toLp 2 μ ℝ f`; `P_t = T.semigroup t`.

## Decision on routes (mathematical)

* ROUTE A (Feller + full support): ALLOWED, proved.  Extra hypotheses, exactly:
  (F) `IsFeller T`: for every `t` and `f : C(X,ℝ)`, `P_t [f]` has a continuous representative;
  (S) `T.μ.IsOpenPosMeasure` (full support);
  and, for the `KernelBridge` (equality invariance), (C) `∀ t, P_t 1 = 1` (conservative).
* ROUTE B (rational times, no Feller): NOT claimed.  It yields exact CK only for rational times on a
  properly exceptional set (Fukushima-type), and the extension to all real `t` needs pathwise right-continuity
  in `t` which `L²`-strong continuity does not give.  Not formalised; documented in `AUDIT_R16_SELF.md` (item 7).
* Item (4) (σ-finite, locally compact): NOT done; documented (item 9).

## T1. Feller criterion (file `FellerKernel.lean`)

```
def IsFeller (T : DiffusionTriple X) [IsFiniteMeasure T.μ] : Prop :=
  ∀ (t : ℝ≥0) (f : C(X, ℝ)), ∃ g : C(X, ℝ), (T.semigroup t (clsC T.μ f) : X → ℝ) =ᵐ[T.μ] ⇑g
theorem isFeller_of_dense [T.μ.IsOpenPosMeasure] (D : Set C(X,ℝ)) (hD : Dense D)
    (h : ∀ t, ∀ d ∈ D, ∃ g : C(X,ℝ), (T.semigroup t (clsC T.μ d) : X → ℝ) =ᵐ[T.μ] ⇑g) : IsFeller T
```
(sup-norm contractivity of `P_t` on classes of continuous functions + uniform limits are continuous.)

## T2. The exact kernel semigroup (file `FellerKernel.lean`), `[T.μ.IsOpenPosMeasure]`, `hF : IsFeller T`

```
noncomputable def fellerOp (hF) (t) (f : C(X,ℝ)) : C(X,ℝ)          -- the continuous representative of P_t [f]
theorem fellerOp_ae : (P_t (clsC μ f) : X → ℝ) =ᵐ[μ] ⇑(fellerOp hF t f)
theorem fellerOp_zero : fellerOp hF 0 f = f
theorem fellerOp_add : fellerOp hF (s+t) f = fellerOp hF s (fellerOp hF t f)     -- exact, everywhere
noncomputable def fellerKernel (hF) (t) : Kernel X X                              -- Riesz-Markov per point x
theorem integral_fellerKernel : ∫ y, f y ∂(fellerKernel hF t x) = fellerOp hF t f x     -- for all x
instance : IsFiniteKernel (fellerKernel hF t);  theorem fellerKernel_subMarkov : fellerKernel hF t x univ ≤ 1
theorem fellerKernel_zero : fellerKernel hF 0 = Kernel.id
theorem fellerKernel_add (s t) : fellerKernel hF (s+t) = fellerKernel hF t ∘ₖ fellerKernel hF s   -- EXACT CK
noncomputable def fellerSemigroup (hF) : SubMarkovKernelSemigroup X
theorem fellerKernel_bind_le : T.μ.bind (fellerKernel hF t) ≤ T.μ
theorem fellerKernel_rep : ∀ t g, Measurable g → (∃ C, ∀ x, |g x| ≤ C) → ∀ hL : MemLp g 2 T.μ,
    (T.semigroup t (hL.toLp g) : X → ℝ) =ᵐ[T.μ] fun x => ∫ y, g y ∂(fellerKernel hF t x)
theorem fellerKernel_unique (κ' : Kernel X X) [∀ x, IsFiniteMeasure (κ' x)]
    (hc : ∀ f : C(X,ℝ), Continuous fun x => ∫ y, f y ∂(κ' x))
    (hr : ∀ f : C(X,ℝ), (P_t (clsC μ f) : X → ℝ) =ᵐ[μ] fun x => ∫ y, f y ∂(κ' x)) : ∀ x, κ' x = fellerKernel hF t x
```
Conservative case `hcons : ∀ t, T.semigroup t T.one2 = T.one2`:
```
theorem fellerKernel_isMarkov (hcons) : ∀ t x, fellerKernel hF t x univ = 1
theorem fellerKernel_bind (hcons) : T.μ.bind (fellerKernel hF t) = T.μ        -- EQUALITY invariance
noncomputable def fellerBridge (hF) (hcons) : KernelBridge T                  -- κ = fellerKernel hF
theorem fellerBridge_isMarkov : (fellerBridge hF hcons).toSubMarkovKernelSemigroup.IsMarkov
```
Corollary: every conservative `CompactTriple`-like triple on compact metrizable `X` with (F),(S) has a `KernelBridge`.
(`integral_semigroup_eq : P_t 1 = 1 → ∫ P_t u = ∫ u` is the symmetric-semigroup step.)

## T3. Circle (file `CircleFeller.lean`), `cT`, `μ₀`, `circleKernel`

```
instance : cT.μ.IsOpenPosMeasure
theorem circle_isFeller : IsFeller cT.toDiffusionTriple          -- via isFeller_of_dense, D = trigSpan (Stone–Weierstrass)
theorem circle_fellerKernel_eq (t x) : fellerKernel circle_isFeller t x = circleKernel t x   -- EVERYWHERE
noncomputable def circleFellerBridge : KernelBridge cT           -- ≠ new data: its κ is circleKernel
```
(needs: `x ↦ ∫ f d circleKernel t x` continuous for continuous `f` (dominated convergence), then `fellerKernel_unique`.)

## T4. Sphere `S³` zonal (file `SphereFeller.lean`)

```
instance : sT.μ.IsOpenPosMeasure                    -- μZ has full support on Zon = [-1,1]
theorem sphere_isFeller : IsFeller sT.toDiffusionTriple         -- via isFeller_of_dense, D = AZ (Weierstrass `AC_top`), `semigroup_cls_mem`
noncomputable def sphereBridge : KernelBridge sT                -- using `semigroup_one`
```
(If an instance-specific hypothesis blocks one of these, it is reported as open, never assumed.)

## Axioms
Only `propext, Classical.choice, Quot.sound` (checked in `AxiomCheckR16.lean`).
