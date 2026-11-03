# Round 14 self-audit (author's attack on his own statements)

Scope: `MarkovTriple/BGL/Theory/Extension/{ClosedBasic,ClosedGamma,ClosedProd,ClosedIdent,ClosedDetect,Hessian,HessLin,
HessExt,HessExt2,IdentIBP,Ident,Gamma2Ident}.lean`.  Target statements: `Extension/STATEMENTS_R14.md` (written before the
proofs; deviations are logged there as E1–E3).  The files contain proofs, so they were NOT added to
`frozen-manifest.json` (that mechanism is for statement-only files under `BGL/Frozen/`; `check_frozen.py` prints OK and no
existing hash changed).

Book source of every public statement is in its docstring.  Hypotheses used: `T : FullTriple E` (F1–F10, including F10 =
ESA in core form, a *field*), plus `T.CD ρ n` where a curvature condition is needed.

## 1. Vacuity / satisfiability checks

* `FormConv`, `GraphConv`: sequences exist for every element (`exists_formConv`: density of `𝒜₀` in `𝒟(ℰ)`, D7;
  `exists_graphConv`: F10), so the "for every sequence" clauses of `gammaE_exists`, `hessE_exists` are not vacuous; the
  limits are obtained from `bil_spec`, i.e. from a genuine Cauchy argument plus independence of the sequence.
* `gammaE`, `hessE` are `Classical.choose` of those existence theorems; their characterising properties
  (`gammaE_tendsto`, `hessE_tendsto`) quantify over ALL approximating sequences, so the choice is canonical and there is no
  junk value.  `hessE` carries `hCD` as an argument; it is a proof (irrelevant).
* "f ∈ 𝒜 ∩ L²" is encoded as `hf : f ∈ T.A`, `hf2 : MemLp f 2 μ`, class `hf2.toLp f`; "∈ 𝒟(ℰ)/𝒟(L)" as membership of the class in
  `T.formDomain` / `T.generator.domain`.  All hypothesis sets are satisfiable in the circle triple (`𝒜 = 𝒜₀ ⊂ 𝒟(L)`) and
  contain `𝒜₀` in every full triple (so the statements are about a non-empty class, and for non-compact triples include the
  genuine `𝒜₀ ⊂ 𝒜 ∩ 𝒟(L)` cases).  Satisfiability of the *curvature* hypothesis: `CD(ρ,n)` holds in the existing instances
  (circle, OU, sphere, Lebesgue with `ρ = 0`).
* Not tested formally (candidates for the hostile audit): a non-compact full triple where `𝒜 ∩ 𝒟(L) ⊋ 𝒜₀`
  (the statements 3.3.5/3.3.17 are non-trivial only there); no instance of this kind is in the library besides OU/Lebesgue,
  where `𝒜₀ ⊊ 𝒜`.

## 2. Junk values / total functions

* `G T f g = ΓA f g`, `Hess`, `Γ₂`, `L` are total functions of `E → ℝ`.  Every theorem that uses them has all its function
  arguments in `𝒜` (or `𝒜₀`) by hypothesis; `Hess_memA`, `Hess_memA₀`, `G_mem`, `Γ₂_memA` record the closure.  `HH`, `GG`, `Gm`
  take `𝒜₀`-subtypes, so no junk.
* a.e. vs everywhere: all identities between elements of `𝒜` are a.e. (book convention); the representatives of `L¹`/`L²`
  classes enter only through `coeFn` and a.e. identities.  `exhaustion` (Def. 3.1.1) is used to pass from
  "`k φ = k ψ` a.e. for all `k ∈ 𝒜₀`" to `φ = ψ` a.e. (`ae_eq_of_mul_A₀`); this is where `φ` is allowed to be non-integrable.
* `ae_zero_of_forall_integral_A₀` (the density step): needs D2 (density in `L²`, cut-off stability `ψ_m(t) = t e^{-t²/(m+1)}`)
  and the exhaustion sequence; no positivity or local integrability of `𝒜` is assumed.

## 3. Deviations from the book (all routine, none changes a statement)

* 3.3.5 (ii): the book tests against `∫ k · ` and uses `kf ∈ 𝒟(ℰ)`, `Γ(kf,h) = kΓ(f,h) + fΓ(k,h)` (Prop. 3.1.5, which was not in
  the library: proved as `mul_formDomain`, `gammaE_mulE`).  We obtain `k · Γ_𝒟 = k · Γ_𝒜` a.e. for every `k ∈ 𝒜₀` and conclude by
  exhaustion (stronger than the integrated test, avoids a density argument for `L¹`).
* 3.3.6 (ii): Riesz representation in the Hilbert space `K` of `𝒟(ℰ)` (form `ℰ + ⟪,⟫`) instead of `ℰ` alone (see E3 and the
  docstring); the conclusion `f + g ∈ 𝒟(L*) = 𝒟(L)` is the book's.
* 3.3.5 (i) is proved with the explicit detection lemma (the book: "density of `𝒜₀` in `L²`"; `Lf` is only known to be in `𝒜`,
  not in `L²`, so a cut-off argument is needed).
* (3.3.7) is derived from `CD(ρ,n)` exactly as in (C.6.8) (quadratic form in `(X₁, Y₂₃)` via `K(f + s(g−a)(h−b))`, rational
  `a, b, s`, continuity); it gives `H² ≤ ½K(ΓgΓh + Γ(g,h)²) ≤ KΓgΓh`.
* 3.3.17 Hessian: the book reduces `∫kH(f)(g,h)` to `∫ f E(g,h,k)`; we give `E` explicitly (`E3`, `int_mul_Hess`), with F1, F7, F6 only.
  The passage `g ∈ 𝒜₀ → g ∈ 𝒜 ∩ 𝒟(ℰ)` uses the first-order property (vi) of the extension (the book's "other chain rule").
* 3.3.17 `Γ₂`: the book only says "along the same lines".  We use the explicit integrated identity `int_m_Γ₂`, the identification of
  `Γ(a_k)` (3.3.5 (ii)) and of `L` (3.3.5 (i)), and an `L²`-Cauchy argument for `Γ(a_k, m)` (bound `‖Γ(a,m)‖₂² ≤ ‖Γ m‖_∞ ℰ(a)`).

## 4. What is NOT done (exact statements)

* 3.3.16 (v), first bullet in `L²`: for `g,h ∈ 𝒜₀`, `a_k → f` in `𝒟(L)` ⇒ `H(a_k)(g,h)` converges in `L²`.  (Only the `L¹`
  statement, jointly in `(f,g)`, is proved: `hessE_tendsto`.)
* 3.3.16 (vii): `h ∈ 𝒜₀`, `f ∈ 𝒟(L)` ⇒ `hf ∈ 𝒟(L)` and `Γ₂(hf,g) = hΓ₂(f,g) + fΓ₂(h,g) + 2H(g)(f,h)`, `g ∈ 𝒟(L)`.  Needs the
  bilinear extension of `Γ₂` to `𝒟(L) × 𝒟(L)` (by `bil_spec` with `|K(a,b)|` bounded by `√K(a)√K(b)`) and the closedness of the
  generator (graph of `h a_k` is Cauchy since `L(h a) = hLa + aLh + 2Γ(h,a)`).
* 3.3.17 converse: `f ∈ L² ∩ 𝒜`, `Γ₂(f), Γ(f) ∈ L¹`, ergodicity (S10) ⇒ `f ∈ 𝒟(L)`.  The book's proof is spectral
  (`(L²+Id)^{-1}(L+ρId)`, density of `{Lh}` in `L²` under ESA + ergodicity); not formalized.
* Prop. 3.3.5/3.3.6 statements are for classes `[f]` of functions of `𝒜 ∩ L²`; nothing is said about `f ∈ 𝒜` with `[f]`
  defined only up to a.e. (inevitable).

## 5. Attack surface for the independent audit (most likely misformalizations)

1. `FormConv` (convergence in `K`, defined through `qEquiv.symm` of `formDomain = formData.Q`): check that it is the book's
   topology on `𝒟(ℰ)` (`norm_jE_sq`: `‖jE a‖² = ‖[a]‖² + ∫Γ(a)`).
2. `mul_formDomain` / `mulE`: the product `k · v` is defined as the `K`-limit of `k b_n`; its identification with the pointwise
   product is `mulE_ae` (a.e.).
3. `hessE_ineq` (viii): stated with explicit `γ₁, γ₂` (E2); check that these are exactly the extended `Γ, Γ₂` (they are: `gamma_limits`).
4. `Γ₂_ext_eq`, `integrable_Γ₂_of_domain`: the identification uses `adjoint_eq_L` (3.3.5 (i)), itself relying on the
   `𝒜₀`-detection lemma; both only use F1, F6, F7, F10 and the D2 density.
5. `ibp_of_domain`: `∫(Lk)g = −∫Γ(k,g)` for `k ∈ 𝒜 ∩ 𝒟(L)`, `g ∈ 𝒜 ∩ 𝒟(ℰ)` (input (c) of Lemmas 3.3.20–3.3.21).
6. Any use of `Classical.choose` (`gammaE`, `hessE`, `mulE`): only through their `*_tendsto`/`*_ae` characterisations.
