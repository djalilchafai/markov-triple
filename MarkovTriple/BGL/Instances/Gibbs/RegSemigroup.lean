import Mathlib
import MarkovTriple.BGL.Instances.Gibbs.RegHypo
import MarkovTriple.BGL.Frozen.Semigroup
import MarkovTriple.BGL.FormData
import MarkovTriple.BGL.Semigroup.Mass
import MarkovTriple.BGL.Analysis.Hilbert.SemigroupSmoothing

/-!
# F8 for the Gibbs triple (BGL Def. 3.3.1 (viii)) is a theorem (R15)

`GibbsData.f8 : G.F8` for every `G : GibbsData`: for `f ∈ C_c^∞(ℝ)` and `t ≥ 0` the `L²`-class of `P_t f`
(Friedrichs semigroup) has a `C^∞` representative.

**Classical theorems formalised.**
* (S) *Smoothing / range property of the semigroup*: for `t > 0` and every `k`, `P_t = R^k ψ_{t,k}(R)` with
  `R = (1 - L)⁻¹` the Friedrichs resolvent (`Hilbert.cfcSemigroup_eq_pow_mul`), i.e. `P_t f ∈ Ran R^k ⊂ 𝒟(L^k)`
  (the semigroup is analytic, `P_t L^k` bounded).
* (E) *Elliptic regularity* (BGL Sect. 1.12) in the form of `RegCore.lean`: `x = R v` is the weak solution of
  `L x = x - v` (the resolvent identity on `𝒜₀`, `∫ x L a = ∫ (x - v) a`), so `v ∈ C^j ⇒ x ∈ C^{j+2}`; iterating,
  `R^{m+1} g ∈ C^{2m+1}` for every `g ∈ L²(μ)`.
* `t = 0`: `P_0 = id`, and `f ∈ 𝒜₀ ⊂ 𝒜`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal InnerProductSpace
open MarkovTriple.Sanity.OU (Sm)
open MarkovTriple.Sanity.OU hiding A₀ γ φ

local notation "OA₀" => MarkovTriple.Sanity.OU.A₀

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E] (T : DiffusionTriple E)

/-- **Weak form of the resolvent identity** on `𝒜₀`: for `v ∈ L²(μ)` and `x = R v` (Friedrichs resolvent
`R = (1 - L)⁻¹`), `∫ x · L a dμ = ∫ (x - v) · a dμ` for every `a ∈ 𝒜₀`. -/
theorem DiffusionTriple.resolvent_weak (v : Lp ℝ 2 T.μ) (a : E → ℝ) (ha : a ∈ T.A₀) :
    ∫ y, ((DiffusionTriple.formData T).R v : E → ℝ) y * T.L a y ∂T.μ =
      ∫ y, (((DiffusionTriple.formData T).R v : E → ℝ) y - (v : E → ℝ) y) * a y ∂T.μ := by
  set S := DiffusionTriple.formData T with hS
  set x : Lp ℝ 2 T.μ := S.R v with hx
  set c : Lp ℝ 2 T.μ := T.cls ⟨a, ha⟩ with hc
  set Lc : Lp ℝ 2 T.μ := T.Lcls ⟨a, ha⟩ with hLc
  have hres : S.R (c - Lc) = c := by
    have := S.R_resolvent ⟨T.clsₗ ⟨a, ha⟩, ⟨⟨a, ha⟩, rfl⟩⟩
    have e : S.opA ⟨T.clsₗ ⟨a, ha⟩, ⟨⟨a, ha⟩, rfl⟩⟩ = -Lc := by
      show S.A _ = _
      exact DiffusionTriple.formA_apply T ⟨a, ha⟩
    have e1 : S.emb ⟨T.clsₗ ⟨a, ha⟩, ⟨⟨a, ha⟩, rfl⟩⟩ = c := rfl
    rw [e, e1] at this
    rw [sub_eq_add_neg]; exact this
  have hsym : inner ℝ (S.R v) (c - Lc) = inner ℝ v (S.R (c - Lc)) := by
    have := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 S.R_isSelfAdjoint) v (c - Lc)
    exact this
  rw [hres, inner_sub_right] at hsym
  have i1 : ∫ y, (x : E → ℝ) y * T.L a y ∂T.μ = inner ℝ x Lc := by
    rw [L2_inner_eq]
    refine integral_congr_ae ?_
    filter_upwards [DiffusionTriple.coeFn_Lcls T ⟨a, ha⟩] with y hy
    rw [hy]
  have i2 : ∫ y, ((x : E → ℝ) y - (v : E → ℝ) y) * a y ∂T.μ = inner ℝ x c - inner ℝ v c := by
    rw [← inner_sub_left, L2_inner_eq]
    refine integral_congr_ae ?_
    filter_upwards [DiffusionTriple.coeFn_cls T ⟨a, ha⟩, Lp.coeFn_sub x v] with y hy hy2
    rw [hy, hy2]; rfl
  rw [i1, i2]
  linarith

end MarkovTriple.BGL

namespace MarkovTriple.BGL.Instances.Gibbs

namespace GibbsData
variable (G : GibbsData)

/-- the Friedrichs resolvent of the Gibbs triple -/
noncomputable abbrev Rres : Lp ℝ 2 G.gibbsDiff.μ →L[ℝ] Lp ℝ 2 G.gibbsDiff.μ :=
  (DiffusionTriple.formData G.gibbsDiff).R

lemma integrable_Lp (u : Lp ℝ 2 G.gibbsDiff.μ) : Integrable (u : ℝ → ℝ) G.μ :=
  (Lp.memLp u).integrable (by norm_num)

/-- **Resolvent regularity gain**: if `v ∈ L²(μ)` has a `C^j` representative, `R v` has a `C^{j+2}` one. -/
theorem resolvent_gain (v : Lp ℝ 2 G.gibbsDiff.μ) (j : ℕ)
    (hv : ∃ vt : ℝ → ℝ, ContDiff ℝ (j : WithTop ℕ∞) vt ∧ (v : ℝ → ℝ) =ᵐ[volume] vt) :
    ∃ X : ℝ → ℝ, ContDiff ℝ ((j + 2 : ℕ) : WithTop ℕ∞) X ∧ (G.Rres v : ℝ → ℝ) =ᵐ[volume] X := by
  obtain ⟨vt, hvt, hvae⟩ := hv
  have hx := G.integrable_Lp (G.Rres v)
  have hvi := G.integrable_Lp v
  have hh : Integrable (fun y => (G.Rres v : ℝ → ℝ) y - (v : ℝ → ℝ) y) G.μ := hx.sub hvi
  have hweak : ∀ a ∈ OA₀, ∫ y, (G.Rres v : ℝ → ℝ) y * Lg G.V a y ∂G.μ =
      ∫ y, ((fun y => (G.Rres v : ℝ → ℝ) y - (v : ℝ → ℝ) y) y) * a y ∂G.μ :=
    fun a ha => G.gibbsDiff.resolvent_weak v a ha
  have key : ∀ i : ℕ, i ≤ j + 2 →
      ∃ X : ℝ → ℝ, ContDiff ℝ (i : WithTop ℕ∞) X ∧ (G.Rres v : ℝ → ℝ) =ᵐ[volume] X := by
    intro i
    induction i with
    | zero =>
      intro _
      obtain ⟨U, hU, hae⟩ := G.weak_reg_C1 hx hh hweak
      exact ⟨U, hU.of_le (by norm_num), hae⟩
    | succ i ih =>
      intro hi
      obtain ⟨X, hX, hXae⟩ := ih (by omega)
      set k : ℕ := min i j with hk
      have hXk : ContDiff ℝ (k : WithTop ℕ∞) X := hX.of_le (by exact_mod_cast min_le_left i j)
      have hvk : ContDiff ℝ (k : WithTop ℕ∞) vt := hvt.of_le (by exact_mod_cast min_le_right i j)
      obtain ⟨U, hU, hUae⟩ := G.weak_reg_gain hx hh hweak k
        ⟨fun y => X y - vt y, hXk.sub hvk, by
          filter_upwards [hXae, hvae] with y h1 h2
          simp only [h1, h2]⟩
      refine ⟨U, hU.of_le ?_, hUae⟩
      have : i + 1 ≤ k + 2 := by omega
      exact_mod_cast this
  exact key (j + 2) le_rfl

/-- `R v ∈ C¹` (a.e. representative) for every `v ∈ L²(μ)`. -/
theorem resolvent_C1 (v : Lp ℝ 2 G.gibbsDiff.μ) :
    ∃ X : ℝ → ℝ, ContDiff ℝ 1 X ∧ (G.Rres v : ℝ → ℝ) =ᵐ[volume] X :=
  G.weak_reg_C1 (G.integrable_Lp (G.Rres v))
    ((G.integrable_Lp (G.Rres v)).sub (G.integrable_Lp v))
    (fun a ha => G.gibbsDiff.resolvent_weak v a ha)

/-- `R^{m+1} g ∈ C^{2m+1}` (a.e. representative) for every `g ∈ L²(μ)`. -/
theorem resolvent_pow_reg (m : ℕ) (g : Lp ℝ 2 G.gibbsDiff.μ) :
    ∃ X : ℝ → ℝ, ContDiff ℝ ((2 * m + 1 : ℕ) : WithTop ℕ∞) X ∧
      ((G.Rres ^ (m + 1)) g : ℝ → ℝ) =ᵐ[volume] X := by
  induction m with
  | zero =>
    obtain ⟨X, hX, hae⟩ := G.resolvent_C1 g
    exact ⟨X, by simpa using hX, by simpa using hae⟩
  | succ m ih =>
    obtain ⟨X, hX, hae⟩ := ih
    obtain ⟨Y, hY, haeY⟩ := G.resolvent_gain ((G.Rres ^ (m + 1)) g) (2 * m + 1) ⟨X, hX, hae⟩
    refine ⟨Y, ?_, ?_⟩
    · have : 2 * (m + 1) + 1 = 2 * m + 1 + 2 := by ring
      rw [this]; exact hY
    · rw [pow_succ']
      exact haeY

/-- **F8 for the Gibbs triple** (BGL Def. 3.3.1 (viii)) is a theorem. -/
theorem f8 : G.F8 := by
  intro t f
  set S := DiffusionTriple.formData G.gibbsDiff with hS
  by_cases ht : t = 0
  · subst ht
    refine ⟨f.1, f.2.1, ?_⟩
    have : G.gibbsDiff.semigroup 0 = 1 := S.semigroup_zero
    rw [this]
    exact G.gibbsDiff.coeFn_cls f
  · have hmain : ∀ n : ℕ, ∃ X : ℝ → ℝ, ContDiff ℝ (n : WithTop ℕ∞) X ∧
        (G.gibbsDiff.semigroup t (G.gibbsDiff.cls f) : ℝ → ℝ) =ᵐ[volume] X := by
      intro n
      have hP : G.gibbsDiff.semigroup t = S.R ^ (n + 1) * Hilbert.Cx.rcfc (Hilbert.psiFun t (n + 1)) S.R :=
        Hilbert.cfcSemigroup_eq_pow_mul S.R_unitOp ht (n + 1)
      obtain ⟨X, hX, hae⟩ := G.resolvent_pow_reg n (Hilbert.Cx.rcfc (Hilbert.psiFun t (n + 1)) S.R (G.gibbsDiff.cls f))
      refine ⟨X, hX.of_le ?_, ?_⟩
      · have : n ≤ 2 * n + 1 := by omega
        exact_mod_cast this
      · rw [hP]; exact hae
    obtain ⟨U, hU, hae⟩ := smooth_rep_of_forall hmain
    exact ⟨U, hU, G.ae_mu_of_ae_vol hae⟩

end GibbsData

end MarkovTriple.BGL.Instances.Gibbs
