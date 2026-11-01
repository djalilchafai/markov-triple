import Mathlib
import MarkovTriple.Frozen.Semigroup

/-! # Full Markov triples (BGL §3.3–3.4) -/

open MeasureTheory
open scoped ENNReal

/-- A **full Markov triple** (BGL §3.3–3.4; numbering unverified): a Markov triple together with an
extended algebra `𝒜 ⊇ 𝒜₀` (unital, hence containing the constants, and stable under *all* smooth
`ψ`) on which the `Γ`-calculus still holds, `L|𝒜₀` essentially self-adjoint, and a stable class
property making semigroup interpolation legitimate.  All items are fields to be proved by instances.

* `A_comp` : `𝒜` is stable under all smooth `ψ : ℝᵏ → ℝ` (no condition `ψ(0) = 0`).
* `diffusion_A` : the chain rule on `𝒜`; with `k = 0`, `ψ ≡ 1` it gives `L 1 = 0`, `Γ(1,·) = 0`.
* `esa` : essential self-adjointness of `L|𝒜₀` in `L²(μ)`, stated through the range criterion
  (Reed–Simon Thm X.26 for the symmetric non-positive operator `L|𝒜₀`, which is symmetric and
  `≤ 0` by `ibp`, `Γ_nonneg`): `(1 − L)𝒜₀` is dense in `L²(μ)`. This avoids constructing the
  closure as a `LinearPMap`.
* `ibp_A`, `ibp_A_symm` (ERRATA F6) : integration by parts for `f ∈ 𝒜` with `f, Lf ∈ L²` against
  `g ∈ 𝒜₀`, in *both* slots: `∫ g Lf = −∫ Γ(f,g)` and `∫ f Lg = −∫ Γ(f,g)`.  Together with `esa`
  they say exactly that `f ∈ D(L̄)` and `L̄ f = L f` (proved in `Hilbert/Closure.lean`:
  `FullMarkovTriple.mem_generator_graph`).  The second slot is what is needed to see that the
  constant `1 ∈ 𝒜` (when `μ` is finite) is in the closure domain with `L̄ 1 = 0`, i.e. `P_t 1 = 1`
  (`Hilbert/Bridge.lean`), although `1 ∉ 𝒜₀`.
* `ibp_AA` (ERRATA P4-1; BGL-style mixed integration by parts on `𝒜`, the BGL numbering is
  UNVERIFIED): for `f, k ∈ 𝒜` with `f, Lf, k, Lk ∈ L²(μ)` and `k` essentially bounded
  (`MemLp k ∞ μ`): `Γ(f,k) ∈ L¹(μ)` and `∫ k Lf = −∫ Γ(f,k)`.  It is **not derivable** from the other
  fields (AUDIT_PHASE4.md, "Next step", item 1): `ibp_A`/`ibp_A_symm` only test against `g ∈ 𝒜₀`;
  `P_t h` and `Φ'(P_t h)` lie in `𝒜 ∖ 𝒜₀`; deriving it from `Γ g = ½L(g²) − gLg` is circular
  (needs `Γ g ∈ L¹`), and no field ties the pointwise `Γ` on `𝒜` to the closed form.  This is the
  input of the semigroup interpolation (LSI).  Instances: `circleFull` (`𝒜 = 𝒜₀`, compact),
  `trivialFull`; OU/Lebesgue are not full triples yet.
* `semigroup_stable` : for every `P` with `IsSemigroupOf`, `P_t` maps `𝒜₀` classes into classes of
  elements of `𝒜` in the `L²`-domain with `L g ∈ L²` (BGL "stable class" / §3.3-3.4). -/
structure FullMarkovTriple (E : Type*) [MeasurableSpace E] extends MarkovTriple E where
  /-- the extended algebra `𝒜` (unital). -/
  A : Subalgebra ℝ (E → ℝ)
  /-- `𝒜₀ ⊆ 𝒜`. -/
  A₀_le : ∀ f ∈ A₀, f ∈ A
  /-- measurability of elements of `𝒜`. -/
  A_measurable : ∀ f ∈ A, Measurable f
  /-- `𝒜` is stable under composition with every smooth `ψ : ℝᵏ → ℝ`. -/
  A_comp : ∀ (k : ℕ) (ψ : (Fin k → ℝ) → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ →
    ∀ f : Fin k → (E → ℝ), (∀ i, f i ∈ A) → (fun x => ψ (fun i => f i x)) ∈ A
  /-- `L` takes values in `𝒜` on `𝒜`. -/
  L_mem_A : ∀ f ∈ A, L f ∈ A
  /-- `Γ` takes values in `𝒜`. -/
  Γ_mem_A : ∀ f ∈ A, ∀ g ∈ A, Γ f g ∈ A
  /-- symmetry on `𝒜`. -/
  Γ_symm_A : ∀ f ∈ A, ∀ g ∈ A, Γ f g = Γ g f
  /-- additivity of `Γ` on `𝒜`. -/
  Γ_add_A : ∀ f ∈ A, ∀ f' ∈ A, ∀ g ∈ A, Γ (f + f') g = Γ f g + Γ f' g
  /-- homogeneity of `Γ` on `𝒜`. -/
  Γ_smul_A : ∀ (c : ℝ), ∀ f ∈ A, ∀ g ∈ A, Γ (c • f) g = c • Γ f g
  /-- positivity of `Γ` on `𝒜`. -/
  Γ_nonneg_A : ∀ f ∈ A, ∀ x, 0 ≤ Γ f f x
  /-- additivity of `L` on `𝒜`. -/
  L_add_A : ∀ f ∈ A, ∀ g ∈ A, L (f + g) = L f + L g
  /-- homogeneity of `L` on `𝒜`. -/
  L_smul_A : ∀ (c : ℝ), ∀ f ∈ A, L (c • f) = c • L f
  /-- pointwise carré du champ identity on `𝒜`. -/
  carre_du_champ_A : ∀ f ∈ A, ∀ g ∈ A, ∀ x,
    Γ f g x = (L (f * g) x - f x * L g x - g x * L f x) / 2
  /-- diffusion property (chain rule) on `𝒜`, for every smooth `ψ`. -/
  diffusion_A : ∀ (k : ℕ) (ψ : (Fin k → ℝ) → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ →
    ∀ f : Fin k → (E → ℝ), (∀ i, f i ∈ A) →
      (∀ g ∈ A, Γ (fun x => ψ (fun i => f i x)) g =
        fun x => ∑ i, MarkovTriple.pderiv ψ i (fun j => f j x) * Γ (f i) g x) ∧
      L (fun x => ψ (fun i => f i x)) =
        fun x => ∑ i, MarkovTriple.pderiv ψ i (fun j => f j x) * L (f i) x +
          ∑ i, ∑ j, MarkovTriple.pderiv₂ ψ i j (fun l => f l x) * Γ (f i) (f j) x
  /-- essential self-adjointness of `L|𝒜₀` on `L²(μ)`, via the range criterion. -/
  esa : Dense {u : Lp ℝ 2 μ | ∃ f ∈ A₀, (u : E → ℝ) =ᵐ[μ] f - L f}
  /-- integration by parts for `f ∈ 𝒜` in the `L²`-domain against `g ∈ 𝒜₀`: `Lf` in the test slot. -/
  ibp_A : ∀ f ∈ A, MemLp f 2 μ → MemLp (L f) 2 μ → ∀ g ∈ A₀,
    Integrable (Γ f g) μ ∧ ∫ x, g x * L f x ∂μ = -∫ x, Γ f g x ∂μ
  /-- the symmetric identity (ERRATA F6): `L g` (`g ∈ 𝒜₀`) in the slot of `f ∈ 𝒜`. -/
  ibp_A_symm : ∀ f ∈ A, MemLp f 2 μ → MemLp (L f) 2 μ → ∀ g ∈ A₀,
    ∫ x, f x * L g x ∂μ = -∫ x, Γ f g x ∂μ
  /-- mixed integration by parts on `𝒜` (ERRATA P4-1): `f, k ∈ 𝒜`, `f, Lf, k, Lk ∈ L²`, `k ∈ L^∞`. -/
  ibp_AA : ∀ f ∈ A, ∀ k ∈ A, MemLp f 2 μ → MemLp (L f) 2 μ → MemLp k 2 μ → MemLp (L k) 2 μ →
    MemLp k ∞ μ → Integrable (Γ f k) μ ∧ ∫ x, k x * L f x ∂μ = -∫ x, Γ f k x ∂μ
  /-- stable class: any semigroup of the triple maps `𝒜₀` into (classes of) `𝒜 ∩ D(L)`. -/
  semigroup_stable : ∀ P, MarkovTriple.IsSemigroupOf toMarkovTriple P → ∀ t : NNReal,
    ∀ f ∈ A₀, ∀ u : Lp ℝ 2 μ, (u : E → ℝ) =ᵐ[μ] f →
      ∃ g ∈ A, MemLp g 2 μ ∧ MemLp (L g) 2 μ ∧ ((P t u : Lp ℝ 2 μ) : E → ℝ) =ᵐ[μ] g
