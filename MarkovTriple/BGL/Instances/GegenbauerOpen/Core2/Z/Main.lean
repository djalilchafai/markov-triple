import Mathlib
import MarkovTriple.BGL.Instances.GegenbauerOpen.Core2.Z.Pair
import MarkovTriple.BGL.Instances.GegenbauerOpen.Core2.W.Main

/-!
# R32-Z: `Core2L` fails for the Gegenbauer operator `L_{5/2}` on `C_c^∞(-1,1)` (FullTriple-free statement)

See `STATEMENTS_R32_Z.md`: `deficiency_pair_five_halves`, `not_core2L_five_halves`.
-/

open MeasureTheory Filter Topology Set

namespace MarkovTriple.BGL.Instances.GegenbauerOpen.Core2Z

open MarkovTriple.BGL.Instances.GegenbauerOpen
open MarkovTriple.BGL.Instances.GegenbauerOpen.Core2Q
open MarkovTriple.BGL.Instances.GegenbauerOpen.R24

/-- **Z1**: the deficiency pair for `lam = 5/2`. -/
theorem deficiency_pair_five_halves : ∃ w h : ℝ → ℝ,
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w (Ioo (-1 : ℝ) 1) ∧
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h (Ioo (-1 : ℝ) 1) ∧
    (∀ x ∈ Ioo (-1 : ℝ) 1, Core2Q.gL (5 / 2) w x = w x) ∧
    MemLp h 2 (Core2W.muL (5 / 2)) ∧ MemLp (fun x => w x - Core2Q.gL (5 / 2) h x) 2 (Core2W.muL (5 / 2)) ∧
      ∃ x ∈ Ioo (-1 : ℝ) 1, w x ≠ 0 := by
  refine ⟨wf, hf (-Lam / 4), wf_smooth, hf_smooth _, fun x hx => wf_L hx, ?_, ?_,
    ⟨0, ⟨by norm_num, by norm_num⟩, ?_⟩⟩
  · exact Core2W.memLp_muL (hf_smooth _).continuousOn _ fun x hx => h_bound _ hx
  · refine Core2W.memLp_muL ?_ _ fun x hx => g_bound hx
    have h1 : ContinuousOn wf (Ioo (-1 : ℝ) 1) := wf_smooth.continuousOn
    have h2 : ContinuousOn (gL (5 / 2) (hf (-Lam / 4))) (Ioo (-1 : ℝ) 1) := by
      have : ContinuousOn (fun x : ℝ => -Lam / 4 * ((1 - x ^ 2) ^ (-1 : ℝ) * (2 - 4 * x ^ 2 / (1 - x ^ 2))))
          (Ioo (-1 : ℝ) 1) := by
        refine continuousOn_const.mul (ContinuousOn.mul ?_ ?_)
        · exact ContinuousOn.rpow_const (by fun_prop) fun x hx =>
            Or.inl (Core2W.one_sub_sq_pos' hx).ne'
        · exact continuousOn_const.sub (ContinuousOn.div (by fun_prop) (by fun_prop)
            fun x hx => (Core2W.one_sub_sq_pos' hx).ne')
      exact this.congr fun x hx => hf_L _ hx
    exact h1.sub h2
  · rw [wf_zero]; norm_num

/-- **Z2 (main)**: `Core2L (5/2)` fails (graph-core property of `L_{5/2}` on `C_c^∞(-1,1)` in `L²((1-x²)² dx)`). -/
theorem not_core2L_five_halves : ¬ Core2W.Core2L (5 / 2) := by
  obtain ⟨w, h, hw, hh, hwL, hh2, hg2, hne⟩ := deficiency_pair_five_halves
  exact Core2W.not_core2L_of_pair (5 / 2) w h hw hh hwL hh2 hg2 hne

end MarkovTriple.BGL.Instances.GegenbauerOpen.Core2Z
