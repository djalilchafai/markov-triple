import Mathlib
import MarkovTriple.BGL.Instances.Lebesgue.Core2Cut
import MarkovTriple.BGL.Instances.Lebesgue.Full
import MarkovTriple.BGL.Theory.Extension.Core2Reduce

/-!
# Brownian triple on `(ℝ, Lebesgue)`: `Core2` and the unconditional converse of BGL Prop. 3.3.17

For `a ∈ C_c^∞`, the `L²`-solution `v` of `v − v'' = a` (`exists_resolvent_solution`) is smooth with `v, …, v⁗ ∈ L²`;
`b_n = χ_n v ∈ C_c^∞` satisfies `(1−L)b_n → a` and `L(1−L)b_n → L a` in `L²` (`cutoff4_tendsto`).
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace MarkovTriple.BGL.Lebesgue

open MarkovTriple.BGL

theorem lebesgueFull_core2 : lebesgueFull.Core2 := by
  intro a
  have hψ : a.1 ∈ A₀ := a.2
  obtain ⟨v, hv, h0, h1, h2, hvψ⟩ := exists_resolvent_solution hψ
  have hv2 : deriv (deriv v) = fun x => v x - a.1 x := by
    funext x; have := hvψ x; linarith
  have hv3 : deriv (deriv (deriv v)) = fun x => deriv v x - deriv a.1 x := by
    rw [hv2]; funext x
    exact (((hv.hasDerivAt x).sub ((smooth hψ).hasDerivAt x))).deriv
  have hv4 : deriv (deriv (deriv (deriv v))) = fun x => deriv (deriv v) x - deriv (deriv a.1) x := by
    rw [hv3]; funext x
    exact (((hv.deriv'.hasDerivAt x).sub ((smooth hψ).deriv'.hasDerivAt x))).deriv
  have h3 : MemLp (deriv (deriv (deriv v))) 2 volume := by
    rw [hv3]; exact h1.sub (memLp_of (deriv_mem hψ) 2)
  have h4 : MemLp (deriv (deriv (deriv (deriv v)))) 2 volume := by
    rw [hv4]; exact h2.sub (memLp_of (deriv_mem (deriv_mem hψ)) 2)
  obtain ⟨c1, c2⟩ := cutoff_graph hv h0 h1 h2
  have hLb : ∀ n : ℕ, Lf (chiR (Rn n) * v) ∈ A₀ := fun n => deriv_mem (deriv_mem (a_mem hv n))
  have hLLb : ∀ n : ℕ, MemLp (Lf (Lf (chiR (Rn n) * v))) 2 volume := fun n =>
    memLp_of (deriv_mem (deriv_mem (hLb n))) 2
  have c3 : Tendsto (fun n : ℕ => (hLLb n).toLp (Lf (Lf (chiR (Rn n) * v)))) atTop
      (𝓝 (h4.toLp (deriv (deriv (deriv (deriv v)))))) :=
    tendsto_toLp_of_integral_sq hLLb h4 (cutoff4_tendsto hv h0 h1 h2 h3 h4)
  refine ⟨fun n => ⟨chiR (Rn n) * v, a_mem hv n⟩, ?_, ?_⟩
  · have e : h0.toLp v - h2.toLp (deriv (deriv v)) = lebesgueDiffusion.cls a := by
      have hd : MemLp (fun x => v x - deriv (deriv v) x) 2 volume := h0.sub h2
      have h3' : h0.toLp v - h2.toLp (deriv (deriv v)) = hd.toLp (fun x => v x - deriv (deriv v) x) := by
        rw [← MemLp.toLp_sub]; rfl
      rw [h3']
      refine Lp.ext ?_
      filter_upwards [hd.coeFn_toLp, lebesgueDiffusion.coeFn_cls a] with x h4' h5
      rw [h4', h5]; exact hvψ x
    have := c1.sub c2
    rw [e] at this
    exact this
  · have e : h2.toLp (deriv (deriv v)) - h4.toLp (deriv (deriv (deriv (deriv v)))) =
        lebesgueDiffusion.Lcls a := by
      have hd : MemLp (fun x => deriv (deriv v) x - deriv (deriv (deriv (deriv v))) x) 2 volume := h2.sub h4
      have h3' : h2.toLp (deriv (deriv v)) - h4.toLp (deriv (deriv (deriv (deriv v)))) =
          hd.toLp (fun x => deriv (deriv v) x - deriv (deriv (deriv (deriv v))) x) := by
        rw [← MemLp.toLp_sub]; rfl
      rw [h3']
      refine Lp.ext ?_
      filter_upwards [hd.coeFn_toLp, lebesgueDiffusion.coeFn_Lcls a] with x h4' h5
      rw [h4', h5]
      show _ = Lf a.1 x
      rw [congrFun hv4 x]; unfold Lf; ring
    have := c2.sub c3
    rw [e] at this
    exact this

/-- **Converse of BGL Prop. 3.3.17 for the Brownian triple, unconditional.** -/
theorem lebesgue_mem_domain_of_Γ₂ {ρ : ℝ} (hρ : ρ ≤ 0) {n : ℝ≥0∞} (hn : 1 ≤ n) {f : ℝ → ℝ}
    (hf : f ∈ lebesgueFull.A) (hf2 : MemLp f 2 lebesgueFull.μ)
    (hG : Integrable (FullTriple.G lebesgueFull f f) lebesgueFull.μ)
    (hG2 : Integrable (lebesgueFull.toDiffusionTriple.Γ₂ f f) lebesgueFull.μ) :
    ∃ hF : hf2.toLp f ∈ lebesgueFull.toDiffusionTriple.generator.domain,
      ((lebesgueFull.toDiffusionTriple.generator ⟨hf2.toLp f, hF⟩ : Lp ℝ 2 lebesgueFull.μ) : ℝ → ℝ)
        =ᵐ[lebesgueFull.μ] lebesgueFull.L f :=
  FullTriple.mem_domain_of_Γ₂ (lebesgue_CD hρ hn) lebesgueFull_core2 hf hf2 hG hG2

end MarkovTriple.BGL.Lebesgue
