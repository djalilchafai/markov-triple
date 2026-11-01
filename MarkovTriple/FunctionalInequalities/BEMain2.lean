import Mathlib
import MarkovTriple.FunctionalInequalities.BEMain1

/-! # Bakry–Émery (Phase 4b): the regular representative of the flow at time `s > 0` -/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal
open MarkovTriple.Hilbert

namespace MarkovTriple.BE

variable {E : Type*} [MeasurableSpace E] (F : FullMarkovTriple E)

theorem step [IsProbabilityMeasure F.μ] (hB : BEStable F) {φ : E → ℝ} (hφ : φ ∈ F.A₀)
    (h0 : 0 ≤ᵐ[F.μ] φ) {M : ℝ} (hM : 0 < M) (hb : ∀ᵐ x ∂F.μ, |φ x| ≤ M) {ε : ℝ}
    (hε : 0 < ε) (C : Cut ε M) {s : ℝ} (hs : 0 < s) :
    ∃ u : E → ℝ, u ∈ F.A ∧ BEReg F u ∧
      MemLp (F.L (F.L (fun x => Real.exp (u x)))) 2 F.μ ∧
      (aflow F hφ ε s : E → ℝ) =ᵐ[F.μ] (fun x => Real.exp (u x)) ∧
      (orb F (F.L_mem φ hφ) s : E → ℝ) =ᵐ[F.μ] F.L (fun x => Real.exp (u x)) ∧
      (orb F (F.L_mem (F.L φ) (F.L_mem φ hφ)) s : E → ℝ) =ᵐ[F.μ]
        F.L (F.L (fun x => Real.exp (u x))) := by
  have hs' : (0 : ℝ≥0) < s.toNNReal := Real.toNNReal_pos.2 hs
  obtain ⟨g, hgA, hg2, hLg2, hgae⟩ := F.semigroup_stable _ (isSemigroupOf_full F) s.toNNReal φ hφ
    (cl F hφ) (coeFn_cl F hφ)
  have hgae' : ((tripleSemigroup F.toMarkovTriple s.toNNReal (cl F hφ) : Lp ℝ 2 F.μ) : E → ℝ)
      =ᵐ[F.μ] g := hgae
  have hψ : ContDiff ℝ (⊤ : ℕ∞) (fun y => C.Λ (ε + y)) :=
    C.hΛ.comp (contDiff_const.add contDiff_id)
  set u : E → ℝ := fun x => C.Λ (ε + g x) with hu
  have huA : u ∈ F.A := comp_mem_A F hψ hgA
  have hru : BEReg F u := hB.reg φ hφ s.toNNReal hs' g hgA hgae' _ hψ
  have hH : BEReg F (fun x => Real.exp (u x)) :=
    hB.reg φ hφ s.toNNReal hs' g hgA hgae' (fun y => Real.exp (C.Λ (ε + y)))
      (Real.contDiff_exp.comp hψ)
  have hHA : (fun x => Real.exp (u x)) ∈ F.A := exp_comp_mem F huA
  -- the flow is `H`
  have hrange := aflow_range hφ h0 hM hb ε s
  have hflow : (aflow F hφ ε s : E → ℝ) =ᵐ[F.μ] (fun x => Real.exp (u x)) := by
    filter_upwards [aflow_coe hφ ε s, hrange, hgae'] with x h1 h2 h3
    have h4 : (orb F hφ s : E → ℝ) x = g x := h3
    rw [h1, h4] at h2 ⊢
    simp only [hu]
    have hmem : ε + g x ∈ Set.Icc ε (ε + M) := ⟨by linarith [h2.1], by linarith [h2.2]⟩
    rw [C.Λ_eq hmem, Real.exp_log (by linarith [h2.1])]
    ring
  -- `f = H - ε`
  set H : E → ℝ := fun x => Real.exp (u x) with hHdef
  have hconst : (fun _ : E => ε) ∈ F.A := comp_mem_A F (contDiff_const (c := ε)) huA
  have hfA : (fun x => H x - ε) ∈ F.A := F.A.sub_mem hHA hconst
  have hLf : F.L (fun x => H x - ε) = F.L H := by
    have e : (fun x => H x - ε) = H + (-ε) • (1 : E → ℝ) := by
      funext x; simp [sub_eq_add_neg]
    rw [e, F.L_add_A H hHA ((-ε) • (1 : E → ℝ)) (F.A.smul_mem F.A.one_mem _),
      F.L_smul_A (-ε) 1 F.A.one_mem, F.L_one]
    simp
  have hHb : MemLp H ∞ F.μ := memLp_exp_top F huA hru.bdd
  have hLHb : MemLp (F.L H) ∞ F.μ := memLp_LG_top F huA hru
  have hf2 : MemLp (fun x => H x - ε) 2 F.μ :=
    (memLp_of_memLp_top hHb 2).sub (memLp_const ε)
  have hLf2 : MemLp (F.L (fun x => H x - ε)) 2 F.μ := by
    rw [hLf]; exact memLp_of_memLp_top hLHb 2
  have hfs : hf2.toLp (fun x => H x - ε) =
      tripleSemigroup F.toMarkovTriple s.toNNReal (cl F hφ) := by
    refine Lp.ext ?_
    filter_upwards [hf2.coeFn_toLp, hflow, aflow_coe hφ ε s, hgae'] with x a b c d
    rw [a]
    have h4 : (orb F hφ s : E → ℝ) x = (tripleSemigroup F.toMarkovTriple s.toNNReal
      (cl F hφ) : E → ℝ) x := rfl
    rw [← h4]
    linarith
  have hVid := L_rep_eq F hφ hfA hf2 hLf2 hfs
  have hV : (orb F (F.L_mem φ hφ) s : E → ℝ) =ᵐ[F.μ] F.L H := by
    have h4 : (orb F (F.L_mem φ hφ) s : E → ℝ) =
        (tripleSemigroup F.toMarkovTriple s.toNNReal (cl F (F.L_mem φ hφ)) : E → ℝ) := rfl
    rw [h4, ← hVid]
    filter_upwards [hLf2.coeFn_toLp] with x a
    rw [a, hLf]
  have hf₂A : F.L H ∈ F.A := F.L_mem_A H hHA
  have hf₂ : MemLp (F.L H) 2 F.μ := memLp_of_memLp_top hLHb 2
  have hfs₂ : hf₂.toLp (F.L H) =
      tripleSemigroup F.toMarkovTriple s.toNNReal (cl F (F.L_mem φ hφ)) := by
    rw [← hVid]
    refine Lp.ext ?_
    filter_upwards [hf₂.coeFn_toLp, hLf2.coeFn_toLp] with x a b
    rw [a, b, hLf]
  have hW := L_rep_eq F (F.L_mem φ hφ) hf₂A hf₂ hH.LL hfs₂
  refine ⟨u, huA, hru, hH.LL, hflow, hV, ?_⟩
  have h4 : (orb F (F.L_mem (F.L φ) (F.L_mem φ hφ)) s : E → ℝ) =
      (tripleSemigroup F.toMarkovTriple s.toNNReal
        (cl F (F.L_mem (F.L φ) (F.L_mem φ hφ))) : E → ℝ) := rfl
  rw [h4, ← hW]
  filter_upwards [hH.LL.coeFn_toLp] with x a
  rw [a]

end MarkovTriple.BE
