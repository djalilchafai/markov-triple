# Round 29, Stream N (spectral theory of the round sphere `S^{n-1}`; StandardTriple, conditional FullTriple): frozen target statements

Written BEFORE any proof.  Namespace `MarkovTriple.BGL.SphereN`; files `Instances/SphereN/Full/*`.  Follows BGL §2.2 / §2.7 / Appendix C.5
(spheres: spherical harmonics, eigenvalues `-k(k+n-2)`, `CD(n-2,n-1)`).  Builds on `sphereDiffusion n hn`, `LS_extrinsic`, `sphere_CD`, `ibp_sphere` (R28 L).

## SCOPE (honest)
Three groups, each delivered or recorded in GAPS with the exact obstruction.
* (N2) Fischer decomposition and density of harmonic polynomials in `L²(σ)`; eigenfunction property.
* (N3) consequences for the semigroup: eigenaction, ESA (F10) directly from the eigenbasis, S10, S11, `sphereStandard`.
* (N4) `sphereFull`: a `FullTriple` whose ONLY non-proved input is F8 (`P_t` maps `𝒜₀ = C^∞(S^{n-1})` into `C^∞`), named `SphereF8` (a `Prop`, never an axiom;
  the library pattern of `GibbsData.F8`); `CD (n-2) (n-1)`; `Core2` (unconditional given the triple).
F8 for ALL `f ∈ 𝒜₀` is NOT claimed; only the restricted statement for restrictions of polynomials (`sphere_semigroup_poly_mem`) is planned.
Poincaré inequality / Obata / Lichnerowicz as inequalities on all of `L²` are NOT planned (no orthonormal basis is constructed).

## Definitions
```
abbrev Pn (n : ℕ) := MvPolynomial (Fin n) ℝ
noncomputable def lap (p : Pn n) : Pn n := ∑ i, pderiv i (pderiv i p)          -- MvPolynomial.pderiv
noncomputable def rsq : Pn n := ∑ i, X i * X i                                    -- |x|²
def IsHarm (k : ℕ) (p : Pn n) : Prop := p.IsHomogeneous k ∧ lap p = 0
noncomputable def restr (p : Pn n) : Sph n → ℝ := fun x => MvPolynomial.eval (cv (x : Ee n)) p
def harmSet (n) (hn : 2 ≤ n) : Set (sphereDiffusion n hn).A₀ := {f | ∃ k h, IsHarm k h ∧ f.1 = restr h}   -- (needs restr h ∈ A₀S, `restr_mem`)
```

## N2 (`Full/Fischer.lean`, `Full/Harm.lean`, `Full/Density.lean`)
```
theorem fischer {d : ℕ} {p : Pn n} (hn : 0 < n) (hp : p.IsHomogeneous d) :
    p ∈ Submodule.span ℝ {q | ∃ (j k : ℕ) (h : Pn n), IsHarm k h ∧ k + 2 * j = d ∧ q = rsq ^ j * h}
theorem restr_mem (p : Pn n) : restr p ∈ A₀S n
theorem restr_rsq_mul (q : Pn n) : restr (rsq * q) = restr q
theorem restr_mem_span_harm (hn : 0 < n) (p : Pn n) :
    restr p ∈ Submodule.span ℝ {f | ∃ k h, IsHarm k h ∧ f = restr h}
theorem LS_restr_harm {k : ℕ} {h : Pn n} (hh : IsHarm k h) :
    LS (restr h) = fun x => -((k : ℝ) * (k + n - 2)) * restr h x
theorem dense_span_harm (hn : 2 ≤ n) :
    (Submodule.span ℝ ((sphereDiffusion n hn).cls '' harmSet n hn)).topologicalClosure = ⊤
```
(`LS_restr_harm` is the extrinsic formula `LS_extrinsic` + Euler's identity; `dense_span_harm` is Stone–Weierstrass (polynomials dense in `C(S)`, hence in `L²(σ)`) + `restr_mem_span_harm`.)

## N3 (`Full/Spectral.lean`)
```
theorem sphere_semigroup_harm (hn : 2 ≤ n) {k} {h} (hh : IsHarm k h) (t : ℝ≥0) :
    (sphereDiffusion n hn).semigroup t ((sphereDiffusion n hn).cls ⟨restr h, restr_mem h⟩)
      = Real.exp (-((k : ℝ) * (k + n - 2)) * t) • (sphereDiffusion n hn).cls ⟨restr h, restr_mem h⟩
theorem sphere_esa (hn : 2 ≤ n) : ∀ u ∈ (sphereDiffusion n hn).generator.domain, ∃ a : ℕ → (sphereDiffusion n hn).A₀,
    (cls (a m) → u) ∧ (Lcls (a m) → generator ⟨u, hu⟩)               -- the F10 `esa` field statement for `sphereDiffusion`
noncomputable def sphereStandard (hn : 2 ≤ n) : StandardTriple (Sph n)   -- toDiffusionTriple = sphereDiffusion n hn; S10, S11 proved
theorem sphere_ergodic, sphere_semigroup_one (P_t 1 = 1)
theorem sphere_semigroup_poly_mem (hn : 2 ≤ n) (t : ℝ≥0) (p : Pn n) :
    ∃ g ∈ A₀S n, ((sphereDiffusion n hn).semigroup t ((sphereDiffusion n hn).cls ⟨restr p, restr_mem p⟩) : Sph n → ℝ) =ᵐ[σ n] g
```

## N4 (`Full/Full.lean`)
```
def SphereF8 (n : ℕ) (hn : 2 ≤ n) : Prop := ∀ (t : ℝ≥0) (f : (sphereDiffusion n hn).A₀), ∃ g ∈ A₀S n,
    ((sphereDiffusion n hn).semigroup t ((sphereDiffusion n hn).cls f) : Sph n → ℝ) =ᵐ[σ n] g
noncomputable def sphereFull (hn : 2 ≤ n) (h8 : SphereF8 n hn) : FullTriple (Sph n)   -- A = A₀S n; toStandardTriple = sphereStandard hn
theorem sphereFull_CD (hn) (h8) : (sphereFull hn h8).CD ((n : ℝ) - 2) ((n - 1 : ℝ≥0∞))      -- CD(n-2, n-1)
theorem sphereFull_core2 (hn) (h8) : (sphereFull hn h8).Core2
```

## Not claimed
`SphereF8` is not proved (the obstruction: uniform `C^m` bounds of spherical harmonics polynomial in the degree, i.e. a Sobolev/Bernstein-type estimate, absent from
Mathlib and not formalised here).  No unconditional `FullTriple` instance, no Feller/bridge statement, no Poincaré inequality for all of `L²`.

## Status (after the proofs)
(to be filled after the proofs; deviations from the frozen text will be listed here and in ERRATA `R29-N-*`)
