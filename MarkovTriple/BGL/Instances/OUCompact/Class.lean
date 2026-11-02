import Mathlib
import MarkovTriple.BGL.Analysis.OU.Alg

/-!
# The test class `ℬ` for the compact Ornstein–Uhlenbeck triple

`ℬ = {f ∈ C^∞(ℝ) : f bounded, f' ∈ 𝒮(ℝ)}`: bounded smooth functions whose derivative is a Schwartz
function.  It contains the constants and `C_c^∞(ℝ)`, is stable under every smooth `ψ`
(`Bm.comp`), under `L f = f'' - x f'` and `Γ(f,g) = f'g'`, and (see `Mehler.lean`) under the
Ornstein–Uhlenbeck semigroup.  This is the algebra `𝒜 = 𝒜₀` of the compact-type OU triple.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal Real SchwartzMap
open MarkovTriple.Sanity.OU hiding A₀

namespace MarkovTriple.BGL.Instances.OUCompact

/-- the test class: bounded smooth functions with Schwartz derivative. -/
def Bm (f : ℝ → ℝ) : Prop :=
  Sm f ∧ (∃ C, ∀ x, |f x| ≤ C) ∧ ∃ W : 𝓢(ℝ, ℝ), ⇑W = deriv f

/-! ### Schwartz functions -/

lemma schw_bdd (W : 𝓢(ℝ, ℝ)) : ∃ C, ∀ x, |W x| ≤ C := by
  obtain ⟨C, -, hC⟩ := W.decay 0 0
  exact ⟨C, fun x => by simpa using hC x⟩

lemma schw_decay (W : 𝓢(ℝ, ℝ)) (k : ℕ) : ∃ C, ∀ x, |x| ^ k * |W x| ≤ C := by
  obtain ⟨C, -, hC⟩ := W.decay k 0
  exact ⟨C, fun x => by simpa using hC x⟩

lemma schw_sm (W : 𝓢(ℝ, ℝ)) : Sm W := W.smooth ⊤

/-- every Schwartz function is in `ℬ` -/
lemma bm_schwartz (S : 𝓢(ℝ, ℝ)) : Bm ⇑S :=
  ⟨schw_sm S, schw_bdd S, SchwartzMap.derivCLM ℝ ℝ S, by
    funext x; exact SchwartzMap.derivCLM_apply ℝ S x⟩

lemma bm_const (c : ℝ) : Bm (fun _ => c) :=
  ⟨contDiff_const, ⟨|c|, fun _ => le_rfl⟩, 0, by funext x; simp⟩

lemma Bm.sm {f : ℝ → ℝ} (hf : Bm f) : Sm f := hf.1

lemma Bm.bdd {f : ℝ → ℝ} (hf : Bm f) : ∃ C, ∀ x, |f x| ≤ C := hf.2.1

lemma Bm.deriv_schwartz {f : ℝ → ℝ} (hf : Bm f) : ∃ W : 𝓢(ℝ, ℝ), ⇑W = deriv f := hf.2.2

/-- elements of `ℬ` have temperate growth (all derivatives bounded). -/
lemma Bm.temperate {f : ℝ → ℝ} (hf : Bm f) : f.HasTemperateGrowth := by
  obtain ⟨C, hC⟩ := hf.bdd
  obtain ⟨W, hW⟩ := hf.deriv_schwartz
  refine ⟨hf.1, fun n => ?_⟩
  rcases n with _ | n
  · exact ⟨0, C, fun x => by simpa using hC x⟩
  · obtain ⟨D, -, hD⟩ := W.decay 0 n
    refine ⟨0, D, fun x => ?_⟩
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_succ', ← hW,
      ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    simpa using hD x

/-! ### Algebraic closure -/

lemma Bm.add {f g : ℝ → ℝ} (hf : Bm f) (hg : Bm g) : Bm (f + g) := by
  obtain ⟨C, hC⟩ := hf.bdd
  obtain ⟨D, hD⟩ := hg.bdd
  obtain ⟨W, hW⟩ := hf.deriv_schwartz
  obtain ⟨V, hV⟩ := hg.deriv_schwartz
  refine ⟨hf.1.add hg.1, ⟨C + D, fun x => (abs_add_le _ _).trans (add_le_add (hC x) (hD x))⟩,
    W + V, ?_⟩
  rw [deriv_add_s hf.1 hg.1, ← hW, ← hV]; rfl

lemma Bm.smul (c : ℝ) {f : ℝ → ℝ} (hf : Bm f) : Bm (c • f) := by
  obtain ⟨C, hC⟩ := hf.bdd
  obtain ⟨W, hW⟩ := hf.deriv_schwartz
  refine ⟨hf.1.const_smul c, ⟨|c| * C, fun x => ?_⟩, c • W, ?_⟩
  · simpa [abs_mul] using mul_le_mul_of_nonneg_left (hC x) (abs_nonneg c)
  · rw [deriv_smul_s c hf.1, ← hW]; rfl

lemma Bm.mul {f g : ℝ → ℝ} (hf : Bm f) (hg : Bm g) : Bm (f * g) := by
  obtain ⟨C, hC⟩ := hf.bdd
  obtain ⟨D, hD⟩ := hg.bdd
  obtain ⟨W, hW⟩ := hf.deriv_schwartz
  obtain ⟨V, hV⟩ := hg.deriv_schwartz
  refine ⟨hf.1.mul hg.1, ⟨C * D, fun x => ?_⟩,
    SchwartzMap.bilinLeftCLM (ContinuousLinearMap.mul ℝ ℝ) hg.temperate W +
      SchwartzMap.bilinLeftCLM (ContinuousLinearMap.mul ℝ ℝ) hf.temperate V, ?_⟩
  · rw [Pi.mul_apply, abs_mul]
    exact mul_le_mul (hC x) (hD x) (abs_nonneg _) ((abs_nonneg _).trans (hC x))
  · rw [deriv_mul_s hf.1 hg.1, ← hW, ← hV]
    funext x
    simp [mul_comm]

/-! ### Stability under `L` and `Γ` -/

/-- `Ls W = W' - x W`, the Ornstein–Uhlenbeck operator on the derivative of `f` (`W = f'`). -/
noncomputable def Ls (W : 𝓢(ℝ, ℝ)) : 𝓢(ℝ, ℝ) :=
  SchwartzMap.derivCLM ℝ ℝ W -
    SchwartzMap.bilinLeftCLM (ContinuousLinearMap.mul ℝ ℝ) (g := fun x : ℝ => x)
      Function.HasTemperateGrowth.id' W

lemma Ls_apply (W : 𝓢(ℝ, ℝ)) (x : ℝ) : Ls W x = deriv W x - W x * x := by
  simp [Ls, SchwartzMap.derivCLM_apply]

lemma Lo_eq_Ls {u : ℝ → ℝ} {W : 𝓢(ℝ, ℝ)} (h : ⇑W = deriv u) : Lo u = ⇑(Ls W) := by
  funext x
  rw [Ls_apply, h]
  simp only [Lo]
  ring

lemma bm_Lo {f : ℝ → ℝ} (hf : Bm f) : Bm (MarkovTriple.Sanity.OU.Lo f) := by
  obtain ⟨W, hW⟩ := hf.deriv_schwartz
  rw [Lo_eq_Ls hW]
  exact bm_schwartz _

lemma bm_Go {f g : ℝ → ℝ} (hf : Bm f) (hg : Bm g) : Bm (MarkovTriple.Sanity.OU.Go f g) := by
  obtain ⟨W, hW⟩ := hf.deriv_schwartz
  obtain ⟨V, hV⟩ := hg.deriv_schwartz
  have : MarkovTriple.Sanity.OU.Go f g = ⇑(SchwartzMap.bilinLeftCLM (ContinuousLinearMap.mul ℝ ℝ)
      (SchwartzMap.hasTemperateGrowth V) W) := by
    funext x
    simp [MarkovTriple.Sanity.OU.Go, ← hW, ← hV]
  rw [this]
  exact bm_schwartz _

/-- `ℬ` contains `C_c^∞` -/
lemma bm_of_cs {f : ℝ → ℝ} (hf : Sm f) (hc : HasCompactSupport f) : Bm f := by
  obtain ⟨C, hC⟩ := hf.continuous.bounded_above_of_compact_support hc
  refine ⟨hf, ⟨C, fun x => by simpa using hC x⟩, ?_⟩
  exact ⟨(hc.deriv).toSchwartzMap hf.deriv', rfl⟩

/-! ### Stability under smooth composition -/

/-- a smooth function composed with a bounded temperate-growth curve has temperate growth. -/
lemma temperate_comp_bdd {k : ℕ} (g : (Fin k → ℝ) → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (F : ℝ → Fin k → ℝ) (hF : F.HasTemperateGrowth) (R : ℝ) (hR : ∀ x, ‖F x‖ ≤ R) :
    (g ∘ F).HasTemperateGrowth := by
  set t : Set (Fin k → ℝ) := Metric.closedBall 0 (|R| + 1) with ht
  have htc : IsCompact t := isCompact_closedBall _ _
  have hU : UniqueDiffOn ℝ t := uniqueDiffOn_convex (convex_closedBall _ _)
    ⟨0, Metric.ball_subset_interior_closedBall (Metric.mem_ball_self (by positivity))⟩
  have hgt : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g t := hg.contDiffOn
  have hcont : ∀ n : ℕ, ∃ M, ∀ x ∈ t, ‖iteratedFDerivWithin ℝ n g t x‖ ≤ M := fun n =>
    htc.exists_bound_of_continuousOn
      (hgt.continuousOn_iteratedFDerivWithin (by exact_mod_cast le_top) hU)
  choose M hM using hcont
  refine hF.comp' (t := t) ?_ hU hgt ?_ 
  · rintro _ ⟨x, rfl⟩
    rw [ht, Metric.mem_closedBall, dist_zero_right]
    linarith [hR x, abs_nonneg R, le_abs_self R]
  · intro N
    refine ⟨0, ∑ n ∈ Finset.range (N + 1), |M n|, Finset.sum_nonneg fun n _ => abs_nonneg _, ?_⟩
    intro n hn x hx
    have h1 : M n ≤ ∑ n ∈ Finset.range (N + 1), |M n| :=
      (le_abs_self _).trans (Finset.single_le_sum (f := fun n => |M n|)
        (fun n _ => abs_nonneg _) (Finset.mem_range.2 (Nat.lt_succ_of_le hn)))
    simpa using (hM n x hx).trans h1

/-- the vector of values `(f_i x)_i` of elements of `ℬ` has temperate growth. -/
lemma temperate_pi {k : ℕ} {f : Fin k → ℝ → ℝ} (hf : ∀ i, Bm (f i)) :
    (fun x => fun i => f i x).HasTemperateGrowth := by
  have : (fun x => fun i => f i x) = fun x => ∑ i, (ContinuousLinearMap.single ℝ (fun _ : Fin k => ℝ) i) (f i x) := by
    funext x j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [this]
  exact Function.HasTemperateGrowth.sum fun i _ =>
    ((ContinuousLinearMap.single ℝ (fun _ : Fin k => ℝ) i).hasTemperateGrowth).comp (hf i).temperate

lemma Bm.comp (k : ℕ) (ψ : (Fin k → ℝ) → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (f : Fin k → ℝ → ℝ) (hf : ∀ i, Bm (f i)) : Bm (fun x => ψ (fun i => f i x)) := by
  have hsm : ∀ i, Sm (f i) := fun i => (hf i).1
  choose Cb hCb using fun i => (hf i).bdd
  set R : ℝ := ∑ i, max (Cb i) 0 with hRdef
  have hR : ∀ x, ‖(fun i => f i x)‖ ≤ R := by
    intro x
    refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ => le_max_right _ _)).2 fun i => ?_
    rw [Real.norm_eq_abs]
    exact ((hCb i x).trans (le_max_left _ _)).trans
      (Finset.single_le_sum (f := fun i => max (Cb i) 0) (fun i _ => le_max_right _ _)
        (Finset.mem_univ i))
  refine ⟨sm_comp k ψ hψ f hsm, ?_, ?_⟩
  · obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : Fin k → ℝ) R).exists_bound_of_continuousOn
      hψ.continuous.continuousOn
    refine ⟨M, fun x => ?_⟩
    simpa using hM _ (by simpa using hR x)
  · choose W hW using fun i => (hf i).deriv_schwartz
    have hT : ∀ i, (fun x => MarkovTriple.BGL.pderiv ψ i (fun j => f j x)).HasTemperateGrowth := fun i =>
      temperate_comp_bdd (MarkovTriple.BGL.pderiv ψ i) (contDiff_pderiv ψ hψ i) _ (temperate_pi hf) R hR
    refine ⟨∑ i, SchwartzMap.bilinLeftCLM (ContinuousLinearMap.mul ℝ ℝ) (hT i) (W i), ?_⟩
    funext x
    rw [deriv_comp1 ψ hψ f hsm]
    simp [← hW, mul_comm]

end MarkovTriple.BGL.Instances.OUCompact
