import Mathlib
import MarkovTriple.Stochastic.R27.GoAlg
import MarkovTriple.BGL.Instances.GegenbauerOpen.Converse.Main
import MarkovTriple.BGL.SemigroupLemmas

/-!
# Round 27 (K), part 2b: the semigroup of `goFullTriple` maps polynomials to polynomials

* smooth functions `f : ℝ → ℝ` are in the generator domain of `goFullTriple` with `G f = L f` (R24-B converse, no completeness);
* on polynomials `L = goM`; eigenpolynomials of `goM` are `P_t`-eigenvectors (`semigroup_eigen`);
* `exists_eigen_decomp` (finite spectral decomposition) gives `P_t [p] = [q]` with `q` a polynomial.
-/

open MeasureTheory Filter Topology Set Polynomial
open scoped ENNReal NNReal

namespace MarkovTriple.Stochastic.R27

open MarkovTriple.BGL MarkovTriple.BGL.Instances.GegenbauerOpen

/-- the polynomial as a function on `ℝ` -/
noncomputable def polyFn (q : ℝ[X]) : ℝ → ℝ := fun x => q.eval x

lemma polyFn_smooth (q : ℝ[X]) : Lebesgue.Sm (polyFn q) := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
    have : polyFn (p + q) = fun x => polyFn p x + polyFn q x := by funext x; simp [polyFn]
    rw [this]; exact hp.add hq
  | monomial n a =>
    have : polyFn (monomial n a) = fun x => a * x ^ n := by funext x; simp [polyFn]
    rw [this]
    exact contDiff_const.mul (contDiff_id.pow n)

lemma deriv_polyFn (q : ℝ[X]) : deriv (polyFn q) = polyFn (derivative q) := by
  funext x; exact Polynomial.deriv q

lemma goL_polyFn (q : ℝ[X]) : goL (polyFn q) = polyFn (goM q) := by
  funext x
  simp only [goL, deriv_polyFn, polyFn, goM_apply]
  simp [eval_sub, eval_mul, eval_pow]

/-- a continuous function is `goμ`-a.e. bounded -/
lemma ae_bound_of_continuous {g : ℝ → ℝ} (hg : Continuous g) : ∃ C, ∀ᵐ x ∂goμ, ‖g x‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn hg.continuousOn
  exact ⟨C, ae_go fun x hx => hC x (Ioo_subset_Icc_self hx)⟩

lemma integrable_of_continuous {g : ℝ → ℝ} (hg : Continuous g) : Integrable g goμ := by
  obtain ⟨C, hC⟩ := ae_bound_of_continuous hg
  exact Integrable.of_bound hg.aestronglyMeasurable C hC

lemma memLp_of_continuous {g : ℝ → ℝ} (hg : Continuous g) : MemLp g 2 goμ := by
  obtain ⟨C, hC⟩ := ae_bound_of_continuous hg
  exact MemLp.of_bound hg.aestronglyMeasurable C hC

lemma smooth_mem_goA {f : ℝ → ℝ} (hf : Lebesgue.Sm f) : f ∈ goFullTriple.A :=
  ⟨hf.continuous.measurable, hf.contDiffOn⟩

/-- **Smooth functions on `ℝ` are in the generator domain of `goFullTriple`, with `G f = L f`** (via the R24-B converse). -/
theorem go_smooth_mem_domain {f : ℝ → ℝ} (hf : Lebesgue.Sm f) :
    ∃ hF : (memLp_of_continuous hf.continuous).toLp f ∈ goFullTriple.toDiffusionTriple.generator.domain,
      ((goFullTriple.toDiffusionTriple.generator ⟨(memLp_of_continuous hf.continuous).toLp f, hF⟩ : Lp ℝ 2 goμ) : ℝ → ℝ)
        =ᵐ[goμ] goL f := by
  have hG : Integrable (FullTriple.G goFullTriple f f) goμ := by
    refine integrable_of_continuous ?_
    have : FullTriple.G goFullTriple f f = fun x => (1 - x ^ 2) * (deriv f x * deriv f x) :=
      funext fun x => go_ΓA hf hf x
    rw [this]
    have := hf.deriv'.continuous
    fun_prop
  have hG2 : Integrable (goFullTriple.toDiffusionTriple.Γ₂ f f) goμ := by
    refine integrable_of_continuous ?_
    have : goFullTriple.toDiffusionTriple.Γ₂ f f = goDiff.Γ₂ f f := rfl
    have e : goDiff.Γ₂ f f = fun x => (1 - x ^ 2) ^ 2 * deriv (deriv f) x ^ 2
      - 2 * x * (1 - x ^ 2) * (deriv f x * deriv (deriv f) x) + (3 + x ^ 2) * deriv f x ^ 2 :=
      funext fun x => go_Γ₂_eq hf x
    rw [this, e]
    have h1 := hf.deriv'.continuous
    have h2 := hf.deriv'.deriv'.continuous
    fun_prop
  exact goFullTriple_mem_domain_of_Γ₂ (smooth_mem_goA hf) (memLp_of_continuous hf.continuous) hG hG2

end MarkovTriple.Stochastic.R27
