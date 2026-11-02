import MarkovTriple.BGL.Analysis.OU.Semigroup
import MarkovTriple.BGL.Analysis.OU.Series

/-! # OU (Part 14): `semigroup_stable` -/

open MeasureTheory Filter Topology Polynomial Set
open scoped ENNReal NNReal Real InnerProductSpace

namespace MarkovTriple.Sanity.OU

open MarkovTriple.Sanity.Circle (IsSG)

/-- a.e. identification of a pointwise Hermite series with an `L²`-sum -/
lemma ae_eq_of_hasSum (c : ℕ → ℝ) (g : ℝ → ℝ) (hg : ∀ x, HasSum (fun n => c n * hh n x) (g x))
    (w : Lp ℝ 2 γ) (hw : HasSum (fun n => c n • hL n) w) : g =ᵐ[γ] w := by
  set S : ℕ → Lp ℝ 2 γ := fun N => ∑ n ∈ Finset.range N, c n • hL n with hS
  have hSw : Tendsto S atTop (𝓝 w) := hw.tendsto_sum_nat
  have hnorm : Tendsto (fun N => eLpNorm (⇑(S N) - ⇑w) 2 γ) atTop (𝓝 0) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm' S w).1 hSw
  have hmeas : TendstoInMeasure γ (fun N => ⇑(S N)) atTop ⇑w :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) hnorm
  obtain ⟨ns, hns, hae⟩ := hmeas.exists_seq_tendsto_ae
  -- pointwise description of the partial sums
  have hterm : ∀ n, (c n • hL n : Lp ℝ 2 γ) =ᵐ[γ] fun x => c n * hh n x := fun n => by
    filter_upwards [Lp.coeFn_smul (c n) (hL n), (hh_memLp n).coeFn_toLp] with x h1 h2
    rw [h1, Pi.smul_apply, hL, h2]; simp
  have hpt' : ∀ N : ℕ, ∀ᵐ x ∂γ, (S N : ℝ → ℝ) x = ∑ n ∈ Finset.range N, c n * hh n x := by
    intro N
    induction N with
    | zero =>
      filter_upwards [Lp.coeFn_zero ℝ 2 γ] with x h1
      simp [hS]
    | succ N ih =>
      filter_upwards [ih, Lp.coeFn_add (S N) (c N • hL N), hterm N] with x h1 h2 h3
      have : S (N + 1) = S N + c N • hL N := by
        simp only [hS]; rw [Finset.sum_range_succ]
      rw [this, h2, Pi.add_apply, h1, h3, Finset.sum_range_succ]
  have hpt : ∀ᵐ x ∂γ, ∀ N, (S N : ℝ → ℝ) x = ∑ n ∈ Finset.range N, c n * hh n x :=
    ae_all_iff.2 hpt'
  filter_upwards [hae, hpt] with x h1 h2
  have h3 : Tendsto (fun i => (S (ns i) : ℝ → ℝ) x) atTop (𝓝 (g x)) := by
    simp_rw [h2]
    exact ((hg x).tendsto_sum_nat).comp hns.tendsto_atTop
  exact tendsto_nhds_unique h3 h1

section Stable

variable {P : ℝ≥0 → (Lp ℝ 2 γ →L[ℝ] Lp ℝ 2 γ)}

/-- the generator clause of `IsSemigroupOf`, in the form used here -/
def GenA₀ (P : ℝ≥0 → (Lp ℝ 2 γ →L[ℝ] Lp ℝ 2 γ)) : Prop :=
  ∀ g ∈ A₀, ∀ u v : Lp ℝ 2 γ, (u : ℝ → ℝ) =ᵐ[γ] g → (v : ℝ → ℝ) =ᵐ[γ] Lo g →
    Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ • (P t u - u)) (𝓝[>] 0) (𝓝 v)

lemma eigen_hL (hP : IsSG P) (hgen : GenA₀ P) (n : ℕ) (t : ℝ≥0) :
    P t (hL n) = Real.exp (-(n : ℝ) * t) • hL n := by
  obtain ⟨g, hg, h1, h2⟩ := hh_approx n
  have hgm : ∀ k, MemLp (g k) 2 γ := fun k => memLp_A₀ (hg k) 2
  have hLm : ∀ k, MemLp (Lo (g k)) 2 γ := fun k => memLp_A₀ (A₀.Lo_mem (hg k)) 2
  have hu := tendsto_toLp hgm (hh_memLp n) h1
  have hv := tendsto_toLp hLm (Lo_hh_memLp n) h2
  have hlim : (Lo_hh_memLp n).toLp (Lo (hh n)) = (-(n : ℝ)) • hL n := by
    refine Lp.ext ?_
    filter_upwards [(Lo_hh_memLp n).coeFn_toLp, Lp.coeFn_smul (-(n : ℝ)) (hL n),
      (hh_memLp n).coeFn_toLp] with x h1 h2 h3
    rw [h1, h2, Pi.smul_apply, hL, h3, Lo_hh]; simp
  rw [hlim] at hv
  exact eigen_of_closure hP (n : ℝ) (u := fun k => (hgm k).toLp (g k))
    (v := fun k => (hLm k).toLp (Lo (g k)))
    (fun k => hgen (g k) (hg k) _ _ (hgm k).coeFn_toLp (hLm k).coeFn_toLp) hu hv t

lemma hasSum_P (hP : IsSG P) (hgen : GenA₀ P) (u : Lp ℝ 2 γ) (t : ℝ≥0) :
    HasSum (fun (n : ℕ) => (Real.exp (-(n : ℝ) * t) * ⟪hL n, u⟫_ℝ) • hL n) (P t u) := by
  have h := (P t).hasSum (hbasis.hasSum_repr u)
  have e : (fun n => P t (hbasis.repr u n • hbasis n)) =
      fun (n : ℕ) => (Real.exp (-(n : ℝ) * t) * ⟪hL n, u⟫_ℝ) • hL n := by
    funext n
    rw [map_smul, hbasis_apply, eigen_hL hP hgen, HilbertBasis.repr_apply_apply, hbasis_apply,
      smul_smul]
    rw [mul_comm]
  rw [e] at h
  exact h

lemma good_of_exp {a : ℕ → ℝ} {C t : ℝ} (ht : 0 < t)
    (h : ∀ n : ℕ, |a n| ≤ C * Real.exp (-(n : ℝ) * t)) : Good a := by
  intro m
  have hs : Summable (fun n : ℕ => ((n : ℝ)) ^ m * Real.exp (-t * (n : ℝ))) :=
    Real.summable_pow_mul_exp_neg_nat_mul m ht
  have hs1 := (summable_nat_add_iff 1).2 hs
  have hs2 : Summable (fun n : ℕ => C * (Real.exp t * (((n + 1 : ℕ) : ℝ) ^ m *
      Real.exp (-t * ((n + 1 : ℕ) : ℝ))))) := (hs1.mul_left _).mul_left _
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hs2
  have e : ((n : ℝ) + 1) ^ m * (C * Real.exp (-(n : ℝ) * t)) =
      C * (Real.exp t * (((n + 1 : ℕ) : ℝ) ^ m * Real.exp (-t * ((n + 1 : ℕ) : ℝ)))) := by
    push_cast
    have : Real.exp t * Real.exp (-t * ((n : ℝ) + 1)) = Real.exp (-(n : ℝ) * t) := by
      rw [← Real.exp_add]; congr 1; ring
    calc ((n : ℝ) + 1) ^ m * (C * Real.exp (-(n : ℝ) * t))
        = C * (((n : ℝ) + 1) ^ m * (Real.exp t * Real.exp (-t * ((n : ℝ) + 1)))) := by rw [this]; ring
      _ = _ := by ring
  rw [← e]
  exact mul_le_mul_of_nonneg_left (h n) (by positivity)

theorem smoothing_ou (hP : IsSG P) (hgen : GenA₀ P) (t : ℝ≥0) (ht : 0 < t) (u : Lp ℝ 2 γ) :
    ∃ g : ℝ → ℝ, Sm g ∧ MemLp g 2 γ ∧ MemLp (Lo g) 2 γ ∧ (P t u : ℝ → ℝ) =ᵐ[γ] g := by
  set a : ℕ → ℝ := fun (n : ℕ) => Real.exp (-(n : ℝ) * t) * ⟪hL n, u⟫_ℝ with ha_def
  have hbound : ∀ n : ℕ, |a n| ≤ ‖u‖ * Real.exp (-(n : ℝ) * t) := by
    intro n
    rw [ha_def, abs_mul, abs_of_pos (Real.exp_pos _)]
    have := abs_real_inner_le_norm (hL n) u
    rw [orthonormal_hL.1 n, one_mul] at this
    calc Real.exp (-(n : ℝ) * t) * |⟪hL n, u⟫_ℝ| ≤ Real.exp (-(n : ℝ) * t) * ‖u‖ :=
          mul_le_mul_of_nonneg_left this (Real.exp_pos _).le
      _ = _ := by ring
  have ha : Good a := good_of_exp (C := ‖u‖) (by exact_mod_cast ht) hbound
  have hpt : ∀ x, HasSum (fun n => a n * hh n x) (Tser a 0 x) := by
    intro x
    have := (summable_Tser ha 0 x).hasSum
    simpa [Tser, dh_zero] using this
  have hsum := hasSum_P hP hgen u t
  have hae := ae_eq_of_hasSum a (Tser a 0) hpt (P t u) hsum
  -- the derivative series
  have hb : Good (fun (n : ℕ) => -(n : ℝ) * a n) := ha.neg_mul_nat
  have hbs : Summable (fun (n : ℕ) => (-(n : ℝ) * a n) • hL n) := by
    refine Summable.of_norm ?_
    have := hb 0
    have hn1 : ∀ n, ‖hL n‖ = 1 := orthonormal_hL.1
    simpa [norm_smul, hn1] using this
  have hpt2 : ∀ x, HasSum (fun (n : ℕ) => (-(n : ℝ) * a n) * hh n x) (Tser (fun (n : ℕ) => -(n : ℝ) * a n) 0 x) := by
    intro x
    have := (summable_Tser hb 0 x).hasSum
    simpa [Tser, dh_zero] using this
  have hae2 := ae_eq_of_hasSum _ _ hpt2 _ hbs.hasSum
  refine ⟨Tser a 0, Tser_sm ha 0, (Lp.memLp (P t u)).ae_eq hae.symm, ?_, hae.symm⟩
  rw [Lo_Tser ha]
  exact (Lp.memLp _).ae_eq hae2.symm

end Stable

end MarkovTriple.Sanity.OU
