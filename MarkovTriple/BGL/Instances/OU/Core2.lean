import Mathlib
import MarkovTriple.BGL.Instances.OU.Core2Cut
import MarkovTriple.BGL.Instances.OU.Full
import MarkovTriple.BGL.Theory.Extension.Core2Reduce

/-!
# OU: `Core2` and the unconditional converse of BGL Prop. 3.3.17

`(1 − L)² C_c^∞` is dense in `L²(γ)` (Hermite basis + `cutoff_approx2`), hence `ouFull.Core2`
(`FullTriple.core2_of_dense`), hence `FullTriple.mem_domain_of_Γ₂` holds for `ouFull` with no extra hypothesis.
-/

open MeasureTheory Filter Topology ProbabilityTheory Polynomial
open scoped ENNReal NNReal Real InnerProductSpace
open MarkovTriple.Sanity.OU hiding A₀

local notation "OA₀" => MarkovTriple.Sanity.OU.A₀

namespace MarkovTriple.BGL.Instances.OU

open MarkovTriple.Sanity.OU in
/-- cut-off approximants of a polynomial in the graph norm of `L²`. -/
theorem pf_approx2 (p : ℝ[X]) :
    ∃ g : ℕ → ℝ → ℝ, (∀ k, g k ∈ OA₀) ∧
      Tendsto (fun k => eLpNorm (g k - pf p) 2 γ) atTop (𝓝 0) ∧
      Tendsto (fun k => eLpNorm (Lo (g k) - Lo (pf p)) 2 γ) atTop (𝓝 0) ∧
      Tendsto (fun k => eLpNorm (Lo (Lo (g k)) - Lo (Lo (pf p))) 2 γ) atTop (𝓝 0) := by
  refine cutoff_approx2 (pf_sm p) (pf_PG p).memLp_two ?_ ?_ ?_ ?_ ?_ ?_
  · rw [deriv_pf]; exact (pf_PG _).memLp_two
  · rw [deriv_pf, deriv_pf]; exact (pf_PG _).memLp_two
  · rw [Lo_pf]; exact (pf_PG _).memLp_two
  · rw [Lo_pf, deriv_pf]; exact (pf_PG _).memLp_two
  · rw [deriv_pf, Lo_pf]; exact (pf_PG _).memLp_two
  · rw [Lo_pf, Lo_pf]; exact (pf_PG _).memLp_two

lemma hh_eq_pf (n : ℕ) : hh n = pf (C (√(n.factorial : ℝ))⁻¹ * He n) := by
  funext x; simp [hh, pf]

/-- `Ψ g = [g − 2 L g + L L g]` for test functions. -/
lemma Ψ_ae (g : ℝ → ℝ) (hg : g ∈ OA₀) :
    ((FullTriple.Ψₗ ouFull ⟨g, hg⟩ : Lp ℝ 2 γ) : ℝ → ℝ) =ᵐ[γ] fun x => g x - 2 * Lo g x + Lo (Lo g) x := by
  have hLg : Lo g ∈ OA₀ := MarkovTriple.Sanity.OU.A₀.Lo_mem hg
  have e : FullTriple.Ψₗ ouFull ⟨g, hg⟩ =
      (ouFull.toDiffusionTriple.cls ⟨g, hg⟩ - ouFull.toDiffusionTriple.Lcls ⟨g, hg⟩) -
        (ouFull.toDiffusionTriple.Lcls ⟨g, hg⟩ - ouFull.toDiffusionTriple.Lcls ⟨Lo g, hLg⟩) := rfl
  rw [e]
  filter_upwards [Lp.coeFn_sub (ouFull.toDiffusionTriple.cls ⟨g, hg⟩ - ouFull.toDiffusionTriple.Lcls ⟨g, hg⟩)
      (ouFull.toDiffusionTriple.Lcls ⟨g, hg⟩ - ouFull.toDiffusionTriple.Lcls ⟨Lo g, hLg⟩),
    Lp.coeFn_sub (ouFull.toDiffusionTriple.cls ⟨g, hg⟩) (ouFull.toDiffusionTriple.Lcls ⟨g, hg⟩),
    Lp.coeFn_sub (ouFull.toDiffusionTriple.Lcls ⟨g, hg⟩) (ouFull.toDiffusionTriple.Lcls ⟨Lo g, hLg⟩),
    DiffusionTriple.coeFn_cls ouFull.toDiffusionTriple ⟨g, hg⟩,
    DiffusionTriple.coeFn_Lcls ouFull.toDiffusionTriple ⟨g, hg⟩,
    DiffusionTriple.coeFn_Lcls ouFull.toDiffusionTriple ⟨Lo g, hLg⟩] with x e1 e2 e3 e4 e5 e6
  rw [e1, Pi.sub_apply, e2, e3, Pi.sub_apply, Pi.sub_apply, e4, e5, e6]
  show g x - Lo g x - (Lo g x - Lo (Lo g) x) = _
  ring

lemma hL_mem_closure_Ψ (n : ℕ) :
    hL n ∈ (LinearMap.range (FullTriple.Ψₗ ouFull)).topologicalClosure := by
  obtain ⟨g, hg, h1, h2, h3⟩ := pf_approx2 (C (√(n.factorial : ℝ))⁻¹ * He n)
  rw [← hh_eq_pf] at h1 h2 h3
  have hL1 : ∀ x, Lo (hh n) x = -(n : ℝ) * hh n x := fun x => congrFun (Lo_hh n) x
  have hL2 : ∀ x, Lo (Lo (hh n)) x = (n : ℝ) ^ 2 * hh n x := by
    intro x
    have : Lo (hh n) = (-(n : ℝ)) • hh n := by funext y; rw [hL1 y]; simp
    rw [this, Lo_smul _ (hh_sm n)]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hL1 x]; ring
  have hgm : ∀ k, MemLp (fun x => g k x - 2 * Lo (g k) x + Lo (Lo (g k)) x) 2 γ := fun k => by
    have a := memLp_A₀ (hg k) 2
    have b := memLp_A₀ (MarkovTriple.Sanity.OU.A₀.Lo_mem (hg k)) 2
    have c := memLp_A₀ (MarkovTriple.Sanity.OU.A₀.Lo_mem (MarkovTriple.Sanity.OU.A₀.Lo_mem (hg k))) 2
    exact (a.sub (b.const_mul 2)).add c
  have htarget : MemLp (fun x => (1 + (n : ℝ)) ^ 2 * hh n x) 2 γ := (hh_memLp n).const_mul _
  have hlim : Tendsto (fun k => (hgm k).toLp _) atTop (𝓝 (htarget.toLp _)) := by
    refine tendsto_toLp hgm htarget ?_
    have hb : ∀ k, eLpNorm ((fun x => g k x - 2 * Lo (g k) x + Lo (Lo (g k)) x) -
        fun x => (1 + (n : ℝ)) ^ 2 * hh n x) 2 γ ≤
        eLpNorm (g k - hh n) 2 γ + eLpNorm ((2 : ℝ) • (Lo (g k) - Lo (hh n))) 2 γ +
          eLpNorm (Lo (Lo (g k)) - Lo (Lo (hh n))) 2 γ := by
      intro k
      have e : ((fun x => g k x - 2 * Lo (g k) x + Lo (Lo (g k)) x) -
          fun x => (1 + (n : ℝ)) ^ 2 * hh n x) =
          ((g k - hh n) - (2 : ℝ) • (Lo (g k) - Lo (hh n))) + (Lo (Lo (g k)) - Lo (Lo (hh n))) := by
        funext x
        simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        rw [hL1 x, hL2 x]
        ring
      rw [e]
      exact (eLpNorm_add_le one_le_two).trans (add_le_add (eLpNorm_sub_le one_le_two) le_rfl)
    have h2' : Tendsto (fun k => eLpNorm ((2 : ℝ) • (Lo (g k) - Lo (hh n))) 2 γ) atTop (𝓝 0) := by
      have := ENNReal.Tendsto.const_mul (a := ‖(2 : ℝ)‖ₑ) h2 (Or.inr enorm_ne_top)
      simp only [mul_zero] at this
      refine this.congr (fun k => ?_)
      rw [eLpNorm_const_smul]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa using (h1.add h2').add h3) (fun _ => zero_le) hb
  have hmem : ∀ k, (hgm k).toLp _ ∈ LinearMap.range (FullTriple.Ψₗ ouFull) := fun k =>
    ⟨⟨g k, hg k⟩, by
      refine Lp.ext ?_
      filter_upwards [Ψ_ae (g k) (hg k), (hgm k).coeFn_toLp] with x h1 h2
      exact h1.trans h2.symm⟩
  have hcl : (htarget.toLp _) ∈ (LinearMap.range (FullTriple.Ψₗ ouFull)).topologicalClosure :=
    mem_closure_of_tendsto hlim (Eventually.of_forall hmem)
  have hr : ((1 + (n : ℝ)) ^ 2) ≠ 0 := by positivity
  have hcl' := Submodule.smul_mem _ (((1 + (n : ℝ)) ^ 2)⁻¹) hcl
  have e : hL n = ((1 + (n : ℝ)) ^ 2)⁻¹ • htarget.toLp _ := by
    rw [hL]
    refine Lp.ext ?_
    filter_upwards [htarget.coeFn_toLp, Lp.coeFn_smul (((1 + (n : ℝ)) ^ 2)⁻¹) (htarget.toLp _),
      (hh_memLp n).coeFn_toLp] with x h1 h2 h3
    rw [h3, h2, Pi.smul_apply, h1, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hr, one_mul]
  rw [e]; exact hcl'

/-- **Density of `(1 − L)² C_c^∞` in `L²(γ)`.** -/
theorem ou_dense_Ψ : Dense (Set.range (FullTriple.Ψₗ ouFull)) := by
  have h : Dense ((LinearMap.range (FullTriple.Ψₗ ouFull) : Submodule ℝ (Lp ℝ 2 γ)) : Set (Lp ℝ 2 γ)) := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top]
    rw [eq_top_iff, ← hbasis.dense_span]
    refine Submodule.topologicalClosure_minimal _ ?_ isClosed_closure
    rw [Submodule.span_le]
    rintro _ ⟨n, rfl⟩
    rw [hbasis_apply]
    exact hL_mem_closure_Ψ n
  have e : Set.range (FullTriple.Ψₗ ouFull) = ((LinearMap.range (FullTriple.Ψₗ ouFull) : Submodule ℝ (Lp ℝ 2 γ)) : Set (Lp ℝ 2 γ)) :=
    (LinearMap.coe_range _).symm
  rw [e]; exact h

/-- **`Core2` for the Ornstein–Uhlenbeck triple.** -/
theorem ouFull_core2 : ouFull.Core2 := FullTriple.core2_of_dense ou_dense_Ψ

/-- **Converse of BGL Prop. 3.3.17 for OU, unconditional** (`ouFull_CD : CD(1,∞)` is proved in `Full.lean`). -/
theorem ou_mem_domain_of_Γ₂ {f : ℝ → ℝ} (hf : f ∈ ouFull.A) (hf2 : MemLp f 2 ouFull.μ)
    (hG : Integrable (FullTriple.G ouFull f f) ouFull.μ)
    (hG2 : Integrable (ouFull.toDiffusionTriple.Γ₂ f f) ouFull.μ) :
    ∃ hF : hf2.toLp f ∈ ouFull.toDiffusionTriple.generator.domain,
      ((ouFull.toDiffusionTriple.generator ⟨hf2.toLp f, hF⟩ : Lp ℝ 2 ouFull.μ) : ℝ → ℝ) =ᵐ[ouFull.μ]
        ouFull.L f :=
  FullTriple.mem_domain_of_Γ₂ ouFull_CD ouFull_core2 hf hf2 hG hG2

end MarkovTriple.BGL.Instances.OU
