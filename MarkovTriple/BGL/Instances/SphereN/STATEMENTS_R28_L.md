# Round 28, Stream L (the genuine round sphere `S^{n-1} ⊂ ℝ^n`): frozen target statements

Written BEFORE any proof.  Namespace `MarkovTriple.BGL.SphereN`; files `Instances/SphereN/*`.  Only `MarkovTriple.lean`, `GAPS.md`, `ERRATA.md`,
`frozen-manifest.json` are edited outside this directory.  Follows BGL §2.2 / Appendix C.5 (spheres): `Γ(f,g) = ∇F·∇G − (x·∇F)(x·∇G)`,
`L = Δ_{S^{n-1}}`, `CD(n−2, n−1)`.  This is the genuine sphere, NOT the zonal one-dimensional Gegenbauer reduction of `Instances/Sphere/*`.

## SCOPE (honest)
Planned theorem groups, in this order; each is delivered or recorded in GAPS with the exact obstruction:
(L1) the space, surface measure, algebra `𝒜₀ = 𝒜 = C^∞(S^{n-1})` and the intrinsic operators `Γ, L` (via the degree-0 homogeneous extension, so no
independence-of-extension problem arises in the definition), plus the extrinsic formulas for restrictions of `C^∞(ℝ^n)` functions;
(L2) `DiffusionTriple` (D1-D8) incl. integration by parts, obtained from the `ℝ^n` integration by parts (`LebesgueRd.ibp_L`) through the polar
decomposition `homeomorphUnitSphereProd` / `Measure.toSphere` of Mathlib and an annular radial cut-off;
(L3) pointwise `CD(n−2, n−1)` for all `f ∈ 𝒜₀` from the Euclidean Bochner identity `Γ₂ = |Hess|²` applied to the degree-0 extension
(Hessian block decomposition and Cauchy-Schwarz on the `(n−1)`-dimensional tangent space);
(L4) `FullTriple`/`StandardTriple` upgrade (needs `F10`, ESA / `Core2`): ONLY attempted if L1-L3 are done; no claim otherwise.

## Common definitions (`SphereN/Basic.lean`, `SphereN/Ops.lean`)
```
abbrev Ee (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev Sph (n : ℕ) := Metric.sphere (0 : Ee n) 1
/-- normalized surface measure: Mathlib's `volume.toSphere` (cone/radial construction) divided by its total mass -/
noncomputable def σ (n : ℕ) : Measure (Sph n) := ((volume : Measure (Ee n)).toSphere univ)⁻¹ • (volume : Measure (Ee n)).toSphere
/-- degree-0 homogeneous extension of `f : S^{n-1} → ℝ` to `ℝ^n` (value `0` at the origin, irrelevant) -/
noncomputable def ext {n} (f : Sph n → ℝ) : (Fin n → ℝ) → ℝ := fun y => if h : y ≠ 0 then f ⟨‖y‖⁻¹ • toLp 2 y, _⟩ else 0
def SmO {n} (F : (Fin n → ℝ) → ℝ) : Prop := ContDiffOn ℝ (⊤ : ℕ∞) F {y | y ≠ 0}
/-- `𝒜₀ = 𝒜 = C^∞(S^{n-1})`, as the algebra (with unit) of `f` whose degree-0 extension is `C^∞` off the origin -/
def A₀S (n : ℕ) : Subalgebra ℝ (Sph n → ℝ) := {f | SmO (ext f)}
noncomputable def ΓS {n} (f g : Sph n → ℝ) : Sph n → ℝ := fun x => LebesgueRd.Gf (ext f) (ext g) (x : Fin n → ℝ)
noncomputable def LS {n} (f : Sph n → ℝ) : Sph n → ℝ := fun x => LebesgueRd.Lf (ext f) (x : Fin n → ℝ)
```
(`LebesgueRd.Gf F G = Σ_i ∂_iF ∂_iG`, `LebesgueRd.Lf F = Σ_i ∂_i²F` with `dd i = ∂_i`, `Instances/LebesgueRd/Basic.lean`.)

## L1: algebra, operators (`SphereN/Ops.lean`)
```
theorem A₀S_of_contDiff {n} {F : (Fin n → ℝ) → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F) : (fun x : Sph n => F x) ∈ A₀S n
theorem ΓS_mem {n} {f g : Sph n → ℝ} (hf : f ∈ A₀S n) (hg : g ∈ A₀S n) : ΓS f g ∈ A₀S n
theorem LS_mem  {n} {f : Sph n → ℝ} (hf : f ∈ A₀S n) : LS f ∈ A₀S n
/-- extrinsic formulas, independent of the extension: -/
theorem ΓS_extrinsic {n} {F G : (Fin n → ℝ) → ℝ} (hF : Sm F) (hG : Sm G) (x : Sph n) :
    ΓS (fun z : Sph n => F z) (fun z : Sph n => G z) x
      = ∑ i, dd i F x * dd i G x - (∑ i, x i * dd i F x) * (∑ i, x i * dd i G x)
theorem LS_extrinsic {n} {F : (Fin n → ℝ) → ℝ} (hF : Sm F) (x : Sph n) :
    LS (fun z : Sph n => F z) x
      = Lf F x - ∑ i, ∑ j, x i * x j * dd i (dd j F) x - ((n : ℝ) - 1) * ∑ i, x i * dd i F x
```

## L2: the triple (`SphereN/Triple.lean`)
```
noncomputable def sphereDiffusion (n : ℕ) (hn : 2 ≤ n) : DiffusionTriple (Sph n)
  -- μ = σ n, A₀ = (A₀S n).toNonUnitalSubalgebra, Γ = ΓS, L = LS
theorem sphereDiffusion_μ : (sphereDiffusion n hn).μ = σ n
theorem sphereDiffusion_Γ : (sphereDiffusion n hn).Γ = ΓS
theorem sphereDiffusion_L : (sphereDiffusion n hn).L = LS
theorem σ_isProbabilityMeasure (hn : 1 ≤ n) : IsProbabilityMeasure (σ n)
theorem ibp_sphere {f g} (hf : f ∈ A₀S n) (hg : g ∈ A₀S n) : ∫ x, g x * LS f x ∂σ n = - ∫ x, ΓS f g x ∂σ n
```
Fields `dense` (Stone–Weierstrass for the coordinate functions + density of `C(S)` in `L^p`), `exhaustion` (`u_k = 1`), `comp_mem`, `diffusion`
(chain rule for the extension) are proved, not assumed.

## L3: curvature (`SphereN/Curv.lean`)
```
theorem sphere_CD {n} (hn : 2 ≤ n) {f : Sph n → ℝ} (hf : f ∈ A₀S n) (x : Sph n) :
    ((n : ℝ) - 2) * ΓS f f x + (1 / ((n : ℝ) - 1)) * (LS f x) ^ 2 ≤ (sphereDiffusion n hn).Γ₂ f f x
```
(`CD(n−2, n−1)`, the book's curvature `(d−1)` and dimension `d` with `d = n−1`.  Equality is NOT claimed.)

## Not claimed
No semigroup, `FullTriple`, `Core2`/ESA, Feller or heat-kernel statement is made unless L4 is delivered and listed in the Status section below.
