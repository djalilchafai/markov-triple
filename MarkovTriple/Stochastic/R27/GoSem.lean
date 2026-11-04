import Mathlib
import MarkovTriple.Stochastic.R27.GoPoly

/-!
# Round 27 (K), part 2c: `P_t` maps polynomial classes to polynomial classes (`goFullTriple`)
-/

open MeasureTheory Filter Topology Set Polynomial
open scoped ENNReal NNReal

namespace MarkovTriple.Stochastic.R27

open MarkovTriple.BGL MarkovTriple.BGL.Instances.GegenbauerOpen

/-- the polynomial `q` as an element of `L²(goμ)` -/
noncomputable def polyLp (q : ℝ[X]) : Lp ℝ 2 goμ :=
  (memLp_of_continuous (polyFn_smooth q).continuous).toLp (polyFn q)

lemma coeFn_polyLp (q : ℝ[X]) : (polyLp q : ℝ → ℝ) =ᵐ[goμ] polyFn q :=
  MemLp.coeFn_toLp _

/-- `ι : ℝ[X] → L²(goμ)` is linear -/
noncomputable def polyι : ℝ[X] →ₗ[ℝ] Lp ℝ 2 goμ where
  toFun := polyLp
  map_add' p q := by
    refine Lp.ext ?_
    filter_upwards [coeFn_polyLp (p + q), coeFn_polyLp p, coeFn_polyLp q, Lp.coeFn_add (polyLp p) (polyLp q)]
      with x h1 h2 h3 h4
    rw [h4, Pi.add_apply, h1, h2, h3]; simp [polyFn]
  map_smul' c q := by
    refine Lp.ext ?_
    filter_upwards [coeFn_polyLp (c • q), coeFn_polyLp q, Lp.coeFn_smul c (polyLp q)] with x h1 h2 h3
    simp only [RingHom.id_apply]
    rw [h3, Pi.smul_apply, h1, h2]; simp [polyFn]

lemma polyι_apply (q : ℝ[X]) : polyι q = polyLp q := rfl

/-- generator on polynomials: `G [q] = [M q]` -/
theorem go_poly_generator (q : ℝ[X]) :
    ∃ hF : polyι q ∈ goFullTriple.toDiffusionTriple.generator.domain,
      goFullTriple.toDiffusionTriple.generator ⟨polyι q, hF⟩ = polyι (goM q) := by
  obtain ⟨hF, hG⟩ := go_smooth_mem_domain (polyFn_smooth q)
  refine ⟨hF, Lp.ext ?_⟩
  filter_upwards [hG, coeFn_polyLp (goM q)] with x h1 h2
  have h3 : ((polyι (goM q) : Lp ℝ 2 goμ) : ℝ → ℝ) x = goL (polyFn q) x := by
    rw [polyι_apply, h2, ← congrFun (goL_polyFn q) x]
  exact h1.trans h3.symm

/-- eigenpolynomials are eigenvectors of the semigroup -/
theorem go_semigroup_eigen (q : ℝ[X]) {c : ℝ} (hc : 0 ≤ c) (hq : goM q = (-c) • q) (t : ℝ≥0) :
    goFullTriple.toDiffusionTriple.semigroup t (polyι q) = Real.exp (-c * t) • polyι q := by
  obtain ⟨hF, hG⟩ := go_poly_generator q
  rw [hq, map_smul] at hG
  have hR := ((DiffusionTriple.formData goFullTriple.toDiffusionTriple).generator_apply_eq_iff hF _).1 hG
  have h2 : polyι q - (-c) • polyι q = (1 + c) • polyι q := by
    rw [neg_smul, sub_neg_eq_add, add_smul, one_smul]
  erw [h2, map_smul] at hR
  have hne : (1 + c) ≠ 0 := by positivity
  have hR' : (DiffusionTriple.formData goFullTriple.toDiffusionTriple).R (polyι q) = (1 + c)⁻¹ • polyι q := by
    calc _ = (1 + c)⁻¹ • ((1 + c) • (DiffusionTriple.formData goFullTriple.toDiffusionTriple).R (polyι q)) := by
          rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
      _ = _ := by rw [hR]; rfl
  exact (DiffusionTriple.formData goFullTriple.toDiffusionTriple).semigroup_eigen hc hR' t

/-- **`P_t` maps polynomial classes to polynomial classes** (`goFullTriple`). -/
theorem go_semigroup_poly_cls (t : ℝ≥0) (p : ℝ[X]) :
    ∃ q : ℝ[X], goFullTriple.toDiffusionTriple.semigroup t (polyι p) = polyι q := by
  have hN := aeval_chi_goM (p.natDegree + 1) p (by
    have := degree_le_natDegree (p := p)
    refine lt_of_le_of_lt this ?_
    exact_mod_cast Nat.lt_succ_self _)
  have key := exists_eigen_decomp goM polyι
    (goFullTriple.toDiffusionTriple.semigroup t).toLinearMap goMu goMu_injective
    (fun j q hq => ⟨Real.exp (-goMu j * t) • q, by
      rw [map_smul]
      exact (go_semigroup_eigen q (goMu_nonneg j) (by simpa using hq) t).symm⟩) _ p hN
  obtain ⟨q, hq⟩ := key
  exact ⟨q, hq.symm⟩

end MarkovTriple.Stochastic.R27
