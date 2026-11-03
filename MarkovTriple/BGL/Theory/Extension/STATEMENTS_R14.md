# Round 14 target statements (frozen before proofs; change only by a logged erratum below)

Source: Bakry–Gentil–Ledoux (BGL), Ch. 3.  Page numbers are book pages (PDF page = book page + 17).
Setting for everything: `T : FullTriple E` (F1–F10: in particular `𝒜₀ ⊂ 𝒜`, ideal F1, F7 integration by parts
`∫Γ(f,g) = −∫ g Lf = −∫ f Lg` for `f ∈ 𝒜`, `g ∈ 𝒜₀`, and ESA = F10 in core form).  `Γ` on `𝒜` is `ΓA`
(`G T`), a.e. equalities.  `cls a ∈ L²` is the class of `a ∈ 𝒜₀`, `𝒟(ℰ) = T.formDomain`, `𝒟(L) = T.generator.domain`,
`ℰ = T.closedForm`.  "Form convergence" `a_k → u` (u ∈ 𝒟(ℰ)): `cls a_k → u` in `L²` and `ℰ(u − a_k) → 0`.
"Graph convergence" `a_k → u` (u ∈ 𝒟(L)): `cls a_k → u`, `L a_k → L u` in `L²` (this is the 𝒟(L)-topology of the book).

## S1. `Γ` on `𝒟(ℰ)` (BGL Prop. 3.1.5 / (3.1.10), used silently in Prop. 3.3.5 (ii); NOT in the library before R14)
* `FullTriple.gammaE T u v : L¹(μ)` for `u v ∈ 𝒟(ℰ)`: `L¹`-limit of `Γ(a_k,b_k)` along ANY form-convergent
  `a_k → u`, `b_k → v` in `𝒜₀` (spec theorem `gammaE_spec`: existence of the limit and independence of the sequences).
  Hypotheses: none beyond `FullTriple`.  Consequences: `∫ gammaE u v = ℰ(u,v)` (`gammaE_integral`),
  `gammaE (cls a) (cls b) = [Γ(a,b)]` for `a, b ∈ 𝒜₀` (`gammaE_cls`), bilinearity/symmetry, and the Cauchy–Schwarz
  `|Γ(u,v)|² ≤ Γ(u)Γ(v)` a.e.
* Product rule (BGL Prop. 3.1.5, quoted in the proof of 3.3.5): for `k, h ∈ 𝒜₀`, `u ∈ 𝒟(ℰ)`: `[k]·u ∈ 𝒟(ℰ)` and
  `Γ(k u, h) = k Γ(u,h) + u Γ(k,h)` a.e. (`gammaE_mul`).

## S2. Props 3.3.5, 3.3.6 (book pp. 155–156)
* **3.3.5 (i)**  `f ∈ 𝒜 ∩ L²`, `w ∈ L²` with `⟪f, Lh⟫ = ⟪w, h⟫` for all `h ∈ 𝒜₀` (i.e. `f ∈ 𝒟(L*)`, `L*f = w`, Def. 3.1.9)
  ⇒ `w = L f` a.e.   (`adjoint_eq_L`)
* **3.3.5 (ii)**  `f ∈ 𝒜 ∩ 𝒟(ℰ)` (i.e. `f ∈ 𝒜`, `[f] = u ∈ 𝒟(ℰ)`) ⇒ `gammaE u u = Γ_𝒜(f)` a.e.   (`gammaE_eq_ΓA`),
  and the bilinear version for `f, g ∈ 𝒜 ∩ 𝒟(ℰ)`.
* **3.3.5 (iii)**  `f ∈ 𝒜 ∩ 𝒟(ℰ)`, `L f ∈ L²` ⇒ `[f] ∈ 𝒟(L)` and `L[f] = [Lf]`.   (`mem_domain_of_L2`)
* **3.3.6 (i)**  (ESA) `f ∈ 𝒜 ∩ L²`, `L f ∈ L²` ⇒ `[f] ∈ 𝒟(L)`, `L[f] = [Lf]`.   (`mem_domain_of_ESA`)
* **3.3.6 (ii)** (ESA) `f ∈ 𝒜 ∩ L²`, `Γ_𝒜(f) ∈ L¹` ⇒ `[f] ∈ 𝒟(ℰ)`.   (`mem_formDomain_of_ESA`)
  Deviation recorded (routine): the book represents the functional `h ↦ ∫ h Lf` as `ℰ(g,h)`; `ℰ` alone is not a
  Hilbert inner product on `𝒟(ℰ)` when constants are in the domain, so we represent it with `ℰ(g,h) + ⟪g,h⟫` and
  conclude `f + g ∈ 𝒟(L*) = 𝒟(L)` exactly as in the book.

## S3. Hessian (BGL Def. 3.3.13, (3.3.3)–(3.3.5), (3.3.7); pp. 158–159)
* `Hess T f g h := ½ (Γ(g,Γ(f,h)) + Γ(h,Γ(f,g)) − Γ(f,Γ(g,h)))` with `Γ = ΓA` (total function, meaningful on `𝒜`).
* On `𝒜` (a.e.): symmetric in `(g,h)`; linear in each slot; first-order in `g`:
  `H(f)(kg,h) = k H(f)(g,h) + g H(f)(k,h)`; (3.3.4) `Γ₂(hf,g) = hΓ₂(f,g) + fΓ₂(h,g) + 2H(g)(h,f)`.
* **(3.3.7)** `CD(ρ,n)` (any `n ≥ 1`) ⇒ for `f,g,h ∈ 𝒜`: `H(f)(g,h)² ≤ (Γ₂(f) − ρΓ(f)) Γ(g)Γ(h)` a.e.
  Book route (C.6.8, p. 517): positivity of the quadratic form in `(X₁, Y₂₃)` obtained from `K(f₁ + s(f₂−a)(f₃−b))`,
  with the book's observation that the discriminant gives `H² ≤ ½K(Γ(f₂)Γ(f₃)+Γ(f₂,f₃)²) ≤ KΓ(f₂)Γ(f₃)`.
* (3.3.5) integration by parts when one of `f,g,h ∈ 𝒜₀` (both forms).

## S4. Prop. 3.3.16 (iv)–(viii) (book p. 160); (i)–(iii) are `gamma_limits` (R12).  Hypotheses: ESA, `CD(ρ,∞)`.
* **(iv)/(v)** for `g,h ∈ 𝒜₀`: if `a_k → f ∈ 𝒟(L)` (graph), `H(a_k)(g,h)` converges in `L²` (limit `H(f)(g,h)`, independent of
  the sequence); for `h ∈ 𝒜₀`, `g ∈ 𝒟(ℰ)`: the same in `L¹` along graph-convergent `a_k → f`, form-convergent `b_k → g`
  (`Hess1`, `hessE_spec`); the map is bilinear.
* **(viii)** `H(f)(g,h)² ≤ (Γ₂(f) − ρΓ(f)) Γ(g)Γ(h)` a.e. for `f ∈ 𝒟(L)`, `g ∈ 𝒟(ℰ)`, `h ∈ 𝒜₀`, with the extended
  `Γ₂, Γ` (`gamma_limits` and `gammaE`).
* **(vi)** `H(f)(hg,k) = hH(f)(g,k) + gH(f)(h,k)` for `f ∈ 𝒟(L)`, `h,k ∈ 𝒜₀`, `g ∈ 𝒟(ℰ)`.
* **(vii)** `h ∈ 𝒜₀`, `f ∈ 𝒟(L)` ⇒ `hf ∈ 𝒟(L)` and `Γ₂(hf,g) = hΓ₂(f,g) + fΓ₂(h,g) + 2H(g)(f,h)` for `g ∈ 𝒟(L)`.

## S5. Prop. 3.3.17 (book pp. 161–162)  Hypotheses: ESA, `CD(ρ,∞)`.
* `f ∈ 𝒜 ∩ 𝒟(L)` ⇒ extended `Γ₂([f]) = Γ₂^𝒜(f)` a.e.; for `g ∈ 𝒜 ∩ 𝒟(ℰ)`, `h ∈ 𝒜₀`: extended `H(f)(g,h) = H_𝒜(f)(g,h)`.
* `f ∈ 𝒜 ∩ 𝒟(L)` ⇒ `Γ₂^𝒜(f), Γ_𝒜(f) ∈ L¹`, `∫Γ₂^𝒜(f) = ∫(Lf)²`.
* Converse (ergodicity S10): `f ∈ 𝒜 ∩ L²`, `Γ₂^𝒜(f), Γ_𝒜(f) ∈ L¹` ⇒ `[f] ∈ 𝒟(L)`.

## Status at the end of round 14 (see also `BGL/AUDIT_R14_SELF.md`)

| Item | Lean | Status |
|---|---|---|
| S1 `gammaE`, `gammaE_integral`, `gammaE_cls`, Leibniz `gammaE_mulE` | `ClosedGamma`, `ClosedProd` | proved |
| 3.3.5 (i) | `adjoint_eq_L` (`ClosedDetect`) | proved |
| 3.3.5 (ii) | `gammaE_eq_ΓA`, `gammaE_self_eq_ΓA` (`ClosedIdent`) | proved |
| 3.3.5 (iii) | `mem_domain_of_formDomain` | proved |
| 3.3.6 (i), (ii) | `mem_domain_of_ESA`, `mem_formDomain_of_ESA` (core: `mem_domain_of_adjoint`) | proved |
| S3 Hessian algebra, (3.3.4), (3.3.7), (3.3.5) IBP | `Hessian`, `HessLin`, `IdentIBP` | proved |
| 3.3.16 (iv), (v) (`L¹`) | `hessE_exists`, `hessE_tendsto` (`HessExt`) | proved (see E1) |
| 3.3.16 (vi) | `hessE_mulE` | proved |
| 3.3.16 (viii) | `hessE_ineq` | proved (see E2) |
| 3.3.16 (vii) | - | OPEN |
| 3.3.17 Hessian identification (`g,h ∈ 𝒜₀`; `g ∈ 𝒜∩𝒟(ℰ)`) | `hessE_eq_Hess`, `hessE_eq_Hess'` (`Ident`) | proved |
| 3.3.17 `Γ(f) ∈ L¹`, `∫Γ(f) = −⟪Lf,f⟫` | `integrable_ΓA_of_domain` | proved |
| 3.3.17 `Γ₂` identification, `Γ₂(f) ∈ L¹`, `∫Γ₂ = ∫(Lf)²`, converse under ergodicity | - | OPEN |

## Errata log
* E1 (round 14, weakening, recorded honestly).  S4 (iv)/(v): only the `L¹` convergence statement (jointly in
  `f ∈ 𝒟(L)` graph-convergent and `g ∈ 𝒟(ℰ)` form-convergent, `h ∈ 𝒜₀`) is proved.  The `L²` statement of the first
  bullet of (v) (for `g, h ∈ 𝒜₀`) is NOT proved (it follows the same route with the `L²` bound
  `∫H(a)(g,h)² ≤ ‖Γ g‖_∞‖Γ h‖_∞ ∫(Γ₂(a) − ρΓ(a))`; not needed for 3.3.17 as formalized).
* E2 (round 14, reformulation).  S4 (viii) is stated with explicit `L¹`-limits `γ₁, γ₂` of `Γ(a_k)`, `Γ₂(a_k)` along a
  graph-convergent sequence (these are the `Γ, Γ₂` of Prop. 3.3.16 (i)–(iii) given by `gamma_limits`), and `Γ(g)` is
  `gammaE g g`; no named extended `Γ₂/Γ` on `𝒟(L)` as a function was introduced.
* E3 (round 14, equivalent formulation).  `FormConv` is convergence in the Hilbert space `K` of `𝒟(ℰ)` (norm
  `(‖·‖₂² + ℰ)^{1/2}`), equivalent to "`cls a_k → u` in `L²` and `ℰ(u − a_k) → 0`".

## Round 14b targets (closing the three open items; fixed before the proofs)
* **T1 = 3.3.16 (v), `L²` part** (removes E1).  `CD(ρ,n)`, ESA.  For `g, h ∈ 𝒜₀` and `f ∈ 𝒟(L)`: there is `H₂ ∈ L²` with
  `H(a_k)(g,h) → H₂` in `L²` for every graph-convergent `a_k → f`, and `H₂ = hessE f [g] h` a.e.  (`hess2_exists`, `hess2_eq_hessE`).
* **T2 = 3.3.16 (vii).**  Bilinear `Γ₂` on `𝒟(L) × 𝒟(L)` into `L¹` (`gamma2E`, limit of `Γ₂(a_k,b_k)` along graph-convergent
  sequences; polarisation of the quadratic form of 3.3.16 (i)–(iii)).  For `h ∈ 𝒜₀`, `f ∈ 𝒟(L)`: `h f ∈ 𝒟(L)` (`mulE h [f]`) and for `g ∈ 𝒟(L)`:
  `Γ₂(hf,g) = h Γ₂(f,g) + f Γ₂(h,g) + 2 H(g)(f,h)` a.e.  (`mulE_mem_domain`, `gamma2E_mulE`).  Uses closedness of the generator (Prop. 3.3.16 (vii) proof "the change of variables formula goes to the limit").
* **T3 = 3.3.17 converse** (ergodicity S10).  `f ∈ 𝒜 ∩ L²`, `Γ_𝒜(f), Γ₂^𝒜(f) ∈ L¹` ⇒ `[f] ∈ 𝒟(L)`.

### Status of round 14b
* T1: `hess2_exists` (`HessL2`) PROVED; E1 is withdrawn (the `L²` statement and its identification with `hessE` are now proved).
* T2: `gamma2E_exists`/`gamma2E_tendsto` (`Gamma2E`), `mulE_mem_domain` (`MulDomain`), `gamma2E_mulE` (`Gamma2Mul`) PROVED.
* T3 (converse): NOT proved.  Exact statement and what is missing: see `BGL/AUDIT_R14_SELF.md` §4.
* Erratum E4: the book's `Γ₂` identification in Prop. 3.3.17 is "along the same lines" as for `H` (chain rule + IBP).  Our proof
  (`Γ₂_ext_eq`) does not use the chain rule (vii); it uses the integrated identity `int_m_Γ₂` instead.  Recorded as a difference of route,
  not of statement.
