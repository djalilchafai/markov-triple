# Round 29, Stream R (tying the abstract atlas to the genuine sphere): frozen target statements

Written BEFORE any proof.  Namespace `MarkovTriple.BGL.SphereN.Atlas`; files `Instances/SphereN/Atlas/*`.  Only `MarkovTriple.lean`, `GAPS.md`, `ERRATA.md`,
`frozen-manifest.json` are edited outside this directory.  Builds on R27-J (`Atlas`, `sphereAtlas : Atlas S2 2`, `Gch`, `Lch`, `gS`, `wS`, `ptS`, namespace
`MarkovTriple.BGL.Instances.Riemannian.R27`), R28-L (`Sph n`, `ΓS`, `LS`, `A₀S`, `σ`, `sphereDiffusion`, namespace `MarkovTriple.BGL.SphereN`) and R26-H (`atlasDiff`).
BGL: Appendix C.3 (chartwise `Γ`, `L` from `(g,w)`), C.5 (spheres).  Notation: `E = ext f` is the degree-0 homogeneous extension of `f` (R28).

## SCOPE (honest)
(R1) `S2 ≃ Sph 3` and chartwise = extrinsic `Γ`, `L` on `𝒜₀ = A₀S 3` (each stereographic chart `b`); gluing by `sphereAtlas.glueΓ/glueL`.
(R2) the chartwise volume: `∫_{ℝ²} (f ∘ e ∘ pt_b) w_S dy = (∫ w_S) ∫ f dσ` (the pushforward of `w_S dy` under `e ∘ pt_b` is a multiple of `σ`), constant `∫ w_S = 4π` is a bonus (not frozen).
(R3) the circle: `Sph 2` versus `𝕋 = ℝ/ℤ` (`circleDiffusion`, `atlasDiff`) via `κ(t) = (cos 2πt, sin 2πt)`; the generators differ by the factor `(2π)²`
(`𝕋` has length 1, the unit circle length `2π`).  This is NOT a bug of either side: `Γ_𝕋 = (2π)² Γ_{Sph 2}∘κ`, `L_𝕋 = (2π)² L_{Sph 2}∘κ`.
(R4) zonal reduction (only attempted if R1-R3 are done): for `f = φ(x₀)` on `Sph n`, `Γ = (1-x₀²)φ'ψ'`, `L = (1-x₀²)φ'' - (n-1)x₀φ'`.
The library's `sFull` ("`S³`", Gegenbauer weight `(1-x²)^{1/2}`, `λ = 1`) is the zonal reduction of `Sph 4 ⊂ ℝ⁴` (`n = 4`; BGL: `S^d`, `d = n-1 = 3`).
(R5) the general-`d` stereographic atlas of `S^d` is NOT attempted (listed as open in GAPS if not delivered).

## R1 (`Atlas/Chart3.lean`, `Atlas/Chart3Ops.lean`)
```
def toSph3 (p : S2) : Sph 3            -- p ↦ ⟨toLp 2 p.1, _⟩
def eS2 : S2 ≃ Sph 3                   -- bijective (inverse p ↦ ⟨ofLp p, _⟩)
theorem eS2_coord (p : S2) (a : Fin 3) : (eS2 p : Ee 3) a = p.1 a
theorem chart_Γ_eq {f h : Sph 3 → ℝ} (hf : f ∈ A₀S 3) (hh : h ∈ A₀S 3) (b : Bool) (y : Ev 2) :
    Gch gS (fun y => f (eS2 (ptS b y))) (fun y => h (eS2 (ptS b y))) y = ΓS f h (eS2 (ptS b y))
theorem chart_L_eq {f : Sph 3 → ℝ} (hf : f ∈ A₀S 3) (b : Bool) (y : Ev 2) :
    Lch gS wS (fun y => f (eS2 (ptS b y))) y = LS f (eS2 (ptS b y))
theorem smooth_of_A₀S {f : Sph 3 → ℝ} (hf : f ∈ A₀S 3) (k : ℕ) : sphereAtlas.Smooth k (fun p => f (eS2 p))
theorem glueΓ_eq_ΓS {f h} (hf : f ∈ A₀S 3) (hh : h ∈ A₀S 3) :
    sphereAtlas.glueΓ (fun p => f (eS2 p)) (fun p => h (eS2 p)) = fun p => ΓS f h (eS2 p)
theorem glueL_eq_LS {f} (hf : f ∈ A₀S 3) : sphereAtlas.glueL (fun p => f (eS2 p)) = fun p => LS f (eS2 p)
theorem glue_eq_sphereDiffusion {f h} (hf : f ∈ A₀S 3) (hh : h ∈ A₀S 3) :
    sphereAtlas.glueΓ (f ∘ eS2) (h ∘ eS2) = (sphereDiffusion 3 (by norm_num)).Γ f h ∘ eS2 ∧
    sphereAtlas.glueL (f ∘ eS2) = (sphereDiffusion 3 (by norm_num)).L f ∘ eS2
```
(Proof idea: with `E = ext f`, `P = ptS b`, chain rule `∂ᵢ(E∘P) = Σ_a ∂_aE(P) ∂ᵢP_a`; `R27.Gch_coord`/`Lch_coord` give `((1+r²)/2)² Σᵢ ∂ᵢP_a∂ᵢP_c = δ_{ac} - P_aP_c` and `L P_a = -2P_a`;
Euler for degree 0: `Σ x_a ∂_aE = 0`, `Σ x_a x_c ∂_a∂_cE = 0` on `|x|=1`.)

## R2 (`Atlas/Volume.lean`)
```
theorem chart_integral {f : Sph 3 → ℝ} (hf : f ∈ A₀S 3) (b : Bool) :
    ∫ y : Ev 2, f (eS2 (ptS b y)) * wS y = (∫ y : Ev 2, wS y) * ∫ x, f x ∂σ 3
```
Route: the map `Φ(y,r) = r · pt_b(y)` from `ℝ²×(0,∞)` onto `ℝ³` minus a closed ray, `|det DΦ| = r² w_S(y)` (Gram determinant), Mathlib change of variables, `polar` (R28), Gaussian radial weight.
Bonus (not frozen): `integral_wS : ∫ wS = 4 * π`.

## R3 (`Atlas/Circle.lean`)
```
def κ (x : 𝕋) : Sph 2                  -- ⟨toLp 2 ![cC x, sC x], _⟩ , cC x = cos 2πx, sC x = sin 2πx
theorem κ_injective : Function.Injective κ
theorem κ_surjective : Function.Surjective κ
theorem circle_A₀ {f} (hf : f ∈ A₀S 2) : (fun x => f (κ x)) ∈ MarkovTriple.Sanity.Circle.A₀
theorem circle_Γ {f h} (hf : f ∈ A₀S 2) (hh : h ∈ A₀S 2) (x : 𝕋) :
    Gc (fun x => f (κ x)) (fun x => h (κ x)) x = (2 * π) ^ 2 * ΓS f h (κ x)
theorem circle_L {f} (hf : f ∈ A₀S 2) (x : 𝕋) : Lc (fun x => f (κ x)) x = (2 * π) ^ 2 * LS f (κ x)
theorem circle_atlasDiff {f h} (hf : f ∈ A₀S 2) (hh : h ∈ A₀S 2) (x : 𝕋) :
    atlasDiff.Γ (fun x => f (κ x)) (fun x => h (κ x)) x = (2 * π) ^ 2 * ΓS f h (κ x) ∧
    atlasDiff.L (fun x => f (κ x)) x = (2 * π) ^ 2 * LS f (κ x)
theorem circle_integral {f} (hf : f ∈ A₀S 2) : ∫ x, f (κ x) ∂μ₀ = ∫ z, f z ∂σ 2
```

## R4 (`Atlas/Zonal.lean`, only if reached)
```
theorem zonal_Γ {n} {φ ψ : ℝ → ℝ} (hφ : ContDiff ℝ ⊤ φ) (hψ : ContDiff ℝ ⊤ ψ) (x : Sph n) :
    ΓS (fun z : Sph n => φ (cv z 0)) ... = (1 - x₀²) deriv φ x₀ * deriv ψ x₀           -- n ≥ 1
theorem zonal_L (hφ) : LS (fun z => φ (z 0)) x = (1 - x₀²) deriv (deriv φ) x₀ - (n - 1) x₀ deriv φ x₀
```
