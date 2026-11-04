import Mathlib
import MarkovTriple.BGL.Instances.IntervalGen.Diffusion
import MarkovTriple.BGL.Frozen.Complete

/-!
# `(Ω, C_c^∞(Ω))` is NOT complete for bounded open `Ω ⊆ ℝ` (G3)

BGL Def. 3.3.9 needs `ζ_k ∈ 𝒜₀`, `ζ_k → 1` a.e., `Γ(ζ_k) ≤ 1/(k+1)²`.  If `Γ(ζ) ≤ c²` a.e. then `|ζ'| ≤ c` everywhere
(`ζ'` is continuous, `Ω` is open, `ζ' = 0` off `Ω`), so `ζ` is `c`-Lipschitz on `ℝ`; with `ζ(y) = 0` for `y ∉ Ω`
(such `y` exists: `Ω` is bounded) we get `|ζ(x)| ≤ c |x - y|`.  See `STATEMENTS_R22_E1.md`.
-/

open MeasureTheory Filter Topology Set

namespace MarkovTriple.BGL.Instances.IntervalGen

namespace BddOpen

variable {Ω : BddOpen}

/-- `Γ(ζ) ≤ c²` a.e. on `Ω` implies `|ζ'| ≤ c` everywhere. -/
lemma abs_deriv_le {ζ : ℝ → ℝ} (hζ : ζ ∈ Ω.A₀) {c : ℝ} (hc : 0 ≤ c)
    (hΓ : Ω.diff.Γ ζ ζ ≤ᵐ[Ω.μ] fun _ => c ^ 2) (t : ℝ) : |deriv ζ t| ≤ c := by
  by_cases ht : t ∈ Ω.carrier
  · by_contra hlt
    rw [not_le] at hlt
    have hsq : c ^ 2 < (deriv ζ t) ^ 2 := by
      have := abs_nonneg (deriv ζ t)
      nlinarith [sq_abs (deriv ζ t)]
    set U : Set ℝ := {s | s ∈ Ω.carrier ∧ c ^ 2 < (deriv ζ s) ^ 2} with hU
    have hUopen : IsOpen U :=
      Ω.isOpen.inter (isOpen_lt continuous_const ((A₀_smooth hζ).deriv'.continuous.pow 2))
    have hUpos : 0 < volume U := hUopen.measure_pos volume ⟨t, ht, hsq⟩
    have h1 := (Ω.ae_μ_iff).1 hΓ
    have h2 : volume U = 0 := by
      refine measure_mono_null (fun s hs => ?_) (ae_iff.1 h1)
      intro hcon
      have := hcon hs.1
      simp only [Lebesgue.Gf] at this
      nlinarith [hs.2]
    exact hUpos.ne' h2
  · rw [zero_off (deriv_mem_A₀ hζ) ht, abs_zero]; exact hc

lemma abs_le_of_Γ {ζ : ℝ → ℝ} (hζ : ζ ∈ Ω.A₀) {c : ℝ} (hc : 0 ≤ c)
    (hΓ : Ω.diff.Γ ζ ζ ≤ᵐ[Ω.μ] fun _ => c ^ 2) {y : ℝ} (hy : y ∉ Ω.carrier) (x : ℝ) :
    |ζ x| ≤ c * |x - y| := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ) (f := ζ) (s := Set.univ) (C := c)
    (fun t _ => ((A₀_smooth hζ).differentiable (by simp)) t)
    (fun t _ => by rw [Real.norm_eq_abs]; exact abs_deriv_le hζ hc hΓ t)
    convex_univ (Set.mem_univ y) (Set.mem_univ x)
  rw [zero_off hζ hy, sub_zero] at h
  simpa [Real.norm_eq_abs] using h

end BddOpen

/-- **G3**: `(Ω, C_c^∞(Ω))` is not complete (BGL Def. 3.3.9). -/
theorem BddOpen.not_complete (Ω : BddOpen) : ¬ Ω.diff.IsComplete := by
  rintro ⟨ζ, hmem, -, -, hlim, hΓ⟩
  obtain ⟨y, hy⟩ := Ω.compl_nonempty
  have hne : Ω.μ ≠ 0 := (Ω.isProb_μ).ne_zero
  have : (ae Ω.μ).NeBot := ae_neBot.2 hne
  obtain ⟨x, hxlim, hx⟩ := (hlim.and ((Ω.ae_μ_iff).2 (Filter.Eventually.of_forall fun _ h => h))).exists
  have hb : ∀ k : ℕ, ζ k x ≤ |x - y| * (1 / ((k : ℝ) + 1)) := fun k => by
    have := BddOpen.abs_le_of_Γ (hmem k) (c := 1 / ((k : ℝ) + 1)) (by positivity) (hΓ k) hy x
    nlinarith [le_abs_self (ζ k x)]
  have hzero : Tendsto (fun k : ℕ => |x - y| * (1 / ((k : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul |x - y|
  have := le_of_tendsto_of_tendsto hxlim hzero (Filter.Eventually.of_forall hb)
  linarith

end MarkovTriple.BGL.Instances.IntervalGen
