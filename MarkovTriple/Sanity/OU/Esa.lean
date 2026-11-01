import MarkovTriple.Sanity.OU.Cutoff

/-! # OU (Part 8): essential self-adjointness (range criterion) -/

open MeasureTheory Filter Topology ProbabilityTheory Polynomial
open scoped ENNReal NNReal Real InnerProductSpace

namespace MarkovTriple.Sanity.OU

lemma tendsto_toLp {g : ℕ → ℝ → ℝ} (hg : ∀ k, MemLp (g k) 2 γ) {f : ℝ → ℝ} (hf : MemLp f 2 γ)
    (h : Tendsto (fun k => eLpNorm (g k - f) 2 γ) atTop (𝓝 0)) :
    Tendsto (fun k => (hg k).toLp (g k)) atTop (𝓝 (hf.toLp f)) := by
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm _ _ hf]
  refine h.congr fun k => ?_
  exact eLpNorm_congr_ae ((((hg k).coeFn_toLp).sub (EventuallyEq.refl _ f)).symm)

lemma Lo_zero : Lo (0 : ℝ → ℝ) = 0 := by funext x; simp [Lo]

lemma Lo_hh (n : ℕ) : Lo (hh n) = fun x => -(n : ℝ) * hh n x := by
  have : hh n = (√(n.factorial : ℝ))⁻¹ • pf (He n) := by funext x; simp [hh, pf]
  rw [this, Lo_smul _ (pf_sm _), Lo_He]
  funext x; simp [pf]; ring

lemma deriv_hh_memLp (n : ℕ) : MemLp (deriv (hh n)) 2 γ := by
  have : hh n = (√(n.factorial : ℝ))⁻¹ • pf (He n) := by funext x; simp [hh, pf]
  rw [this, deriv_smul_s _ (pf_sm _), deriv_pf]
  exact ((pf_PG (derivative (He n))).memLp_two).const_smul _

lemma Lo_hh_memLp (n : ℕ) : MemLp (Lo (hh n)) 2 γ := by
  rw [Lo_hh]
  have := (hh_memLp n).const_mul (-(n : ℝ))
  exact this

/-- graph-norm approximants of the Hermite function `hh n` by test functions. -/
theorem hh_approx (n : ℕ) :
    ∃ g : ℕ → ℝ → ℝ, (∀ k, g k ∈ A₀) ∧
      Tendsto (fun k => eLpNorm (g k - hh n) 2 γ) atTop (𝓝 0) ∧
      Tendsto (fun k => eLpNorm (Lo (g k) - Lo (hh n)) 2 γ) atTop (𝓝 0) :=
  cutoff_approx (hh_sm n) (hh_memLp n) (deriv_hh_memLp n) (Lo_hh_memLp n)

/-- the range of `1 − L` on test functions, as a submodule of `L²(γ)` -/
noncomputable def rangeK : Submodule ℝ (Lp ℝ 2 γ) where
  carrier := {u | ∃ f ∈ A₀, (u : ℝ → ℝ) =ᵐ[γ] f - Lo f}
  add_mem' := by
    rintro u v ⟨f, hf, hu⟩ ⟨g, hg, hv⟩
    refine ⟨f + g, add_mem hf hg, ?_⟩
    filter_upwards [Lp.coeFn_add u v, hu, hv] with x h1 h2 h3
    rw [h1, Pi.add_apply, h2, h3, Lo_add hf.1 hg.1]
    simp; ring
  zero_mem' := ⟨0, zero_mem _, by
    filter_upwards [Lp.coeFn_zero ℝ 2 γ] with x h1
    rw [h1]; simp [Lo]⟩
  smul_mem' := by
    rintro c u ⟨f, hf, hu⟩
    refine ⟨c • f, A₀.smul_mem c hf, ?_⟩
    filter_upwards [Lp.coeFn_smul c u, hu] with x h1 h2
    rw [h1, Pi.smul_apply, h2, Lo_smul c hf.1]
    simp; ring

lemma hL_mem_closure (n : ℕ) : hL n ∈ rangeK.topologicalClosure := by
  obtain ⟨g, hg, h1, h2⟩ := hh_approx n
  have hgm : ∀ k, MemLp (g k - Lo (g k)) 2 γ := fun k =>
    memLp_A₀ (sub_mem (hg k) (A₀.Lo_mem (hg k))) 2
  set u : ℕ → Lp ℝ 2 γ := fun k => (hgm k).toLp (g k - Lo (g k)) with hu
  have hmem : ∀ k, u k ∈ rangeK := fun k =>
    ⟨g k, hg k, (hgm k).coeFn_toLp⟩
  have htarget : MemLp (fun x => (1 + (n : ℝ)) * hh n x) 2 γ := (hh_memLp n).const_mul _
  have hlim : Tendsto u atTop (𝓝 (htarget.toLp _)) := by
    refine tendsto_toLp hgm htarget ?_
    have hb : ∀ k, eLpNorm (g k - Lo (g k) - fun x => (1 + (n : ℝ)) * hh n x) 2 γ ≤
        eLpNorm (g k - hh n) 2 γ + eLpNorm (Lo (g k) - Lo (hh n)) 2 γ := by
      intro k
      have e : (g k - Lo (g k) - fun x => (1 + (n : ℝ)) * hh n x) =
          (g k - hh n) - (Lo (g k) - Lo (hh n)) := by
        funext x
        simp only [Pi.sub_apply, Lo_hh]
        ring
      rw [e]
      exact eLpNorm_sub_le one_le_two
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (by simpa using h1.add h2)
      (fun _ => zero_le) hb
  have hcl : (htarget.toLp _) ∈ rangeK.topologicalClosure :=
    mem_closure_of_tendsto hlim (Eventually.of_forall hmem)
  have e : htarget.toLp _ = (1 + (n : ℝ)) • hL n := by
    rw [hL]
    refine Lp.ext ?_
    filter_upwards [htarget.coeFn_toLp, Lp.coeFn_smul (1 + (n : ℝ)) ((hh_memLp n).toLp (hh n)),
      (hh_memLp n).coeFn_toLp] with x h1 h2 h3
    rw [h1, h2, Pi.smul_apply, h3]; simp
  rw [e] at hcl
  have := Submodule.smul_mem _ ((1 + (n : ℝ))⁻¹) hcl
  rwa [smul_smul, inv_mul_cancel₀ (by positivity), one_smul] at this

lemma orth_span_eq_bot : (Submodule.span ℝ (Set.range hL))ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro w hw
  refine eq_zero_of_orth_hL fun n => ?_
  exact (Submodule.mem_orthogonal' _ _ |>.1 hw) (hL n) (Submodule.subset_span ⟨n, rfl⟩) |> fun h => by
    simpa [real_inner_comm] using h

/-- the Hermite Hilbert basis of `L²(γ)` -/
noncomputable def hbasis : HilbertBasis ℕ ℝ (Lp ℝ 2 γ) :=
  HilbertBasis.mkOfOrthogonalEqBot orthonormal_hL orth_span_eq_bot

lemma hbasis_apply (n : ℕ) : hbasis n = hL n := by
  have := HilbertBasis.coe_mkOfOrthogonalEqBot orthonormal_hL orth_span_eq_bot
  exact congrFun this n

/-- **`esa` for OU**: `(1 − L) C_c^∞` is dense in `L²(γ)`. -/
theorem ou_esa : Dense {u : Lp ℝ 2 γ | ∃ f ∈ A₀, (u : ℝ → ℝ) =ᵐ[γ] f - Lo f} := by
  have h : Dense (rangeK : Set (Lp ℝ 2 γ)) := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top]
    rw [eq_top_iff, ← hbasis.dense_span]
    refine Submodule.topologicalClosure_minimal _ ?_ isClosed_closure
    rw [Submodule.span_le]
    rintro _ ⟨n, rfl⟩
    rw [hbasis_apply]
    exact hL_mem_closure n
  exact h

end MarkovTriple.Sanity.OU
