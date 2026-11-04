import Mathlib
import MarkovTriple.BGL.Instances.LebesgueRd.Full.HeatAPI
import MarkovTriple.BGL.Instances.LebesgueRd.Full.DomainAux
import MarkovTriple.BGL.Instances.LebesgueRd.FullEasy
import MarkovTriple.BGL.SemigroupLemmas
import MarkovTriple.BGL.Semigroup.Characterization
import MarkovTriple.BGL.Instances.LebesgueRd.Gamma2
import MarkovTriple.BGL.Instances.Gibbs.FunctPreFull
import MarkovTriple.BGL.Frozen.Complete

/-!
# Completeness, `PreFull`, cut-off approximation and domain membership for `(ℝ^d, Lebesgue)` (Round 24, stream A, part B-a)

STUB (statements fixed; proofs `sorry` until stream B-a delivers).
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal LinearPMap

namespace MarkovTriple.BGL.LebesgueRd

variable {d : ℕ}

/-- completeness (BGL Def. 3.3.9) with cut-offs `ζ_k = s(2 - ψ/(M(k+1)))`, `ψ = √(1+|x|²)`. -/
theorem isComplete_lebesgueRd (hd : 1 ≤ d) : (lebesgueRdDiffusion d hd).IsComplete := by
  obtain ⟨C, hC0, hC⟩ := cut_bounds (d := d)
  set M : ℕ := ⌈(d : ℝ) * C⌉₊ + 1 with hM
  have hM1 : (d : ℝ) * C ≤ M := by
    have := Nat.le_ceil ((d : ℝ) * C)
    rw [hM]; push_cast; linarith
  have hMpos : (0 : ℝ) < M := by rw [hM]; positivity
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdC : (d : ℝ) * C ^ 2 ≤ (M : ℝ) ^ 2 := by
    have h0 : (0 : ℝ) ≤ d * C := by positivity
    nlinarith
  have hmono : ∀ x : Fin d → ℝ, Monotone fun n : ℕ => (cut n : (Fin d → ℝ) → ℝ) x := fun x =>
    monotone_nat_of_le_succ fun n => cut_mono n x
  refine ⟨fun k => cut (M * (k + 1)), fun k => cut_mem _,
    fun k => Filter.Eventually.of_forall fun x => cut_nonneg _ x,
    fun k => Filter.Eventually.of_forall fun x => hmono x (Nat.mul_le_mul_left _ (by omega)),
    Filter.Eventually.of_forall fun x => (cut_tendsto x).comp ?_, fun k => ?_⟩
  · refine tendsto_atTop_mono (fun k => ?_) tendsto_id
    have : 1 ≤ M := by rw [hM]; omega
    show k ≤ M * (k + 1)
    nlinarith
  · refine Filter.Eventually.of_forall fun x => ?_
    show Gf _ _ x ≤ _
    have hR : ((M : ℝ) * ((k : ℝ) + 1)) ≤ ((M * (k + 1) : ℕ) : ℝ) + 1 := by push_cast; linarith
    have hk0 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hMk : (0 : ℝ) < (M : ℝ) * ((k : ℝ) + 1) := by positivity
    have hterm : ∀ i : Fin d, dd i (cut (M * (k + 1)) : (Fin d → ℝ) → ℝ) x *
        dd i (cut (M * (k + 1)) : (Fin d → ℝ) → ℝ) x ≤ (C / ((M : ℝ) * ((k : ℝ) + 1))) ^ 2 := by
      intro i
      have h1 := (hC (M * (k + 1)) i x).1
      have h2 : C / (((M * (k + 1) : ℕ) : ℝ) + 1) ≤ C / ((M : ℝ) * ((k : ℝ) + 1)) :=
        div_le_div_of_nonneg_left hC0 hMk hR
      rw [← _root_.sq]
      calc _ = |dd i (cut (M * (k + 1)) : (Fin d → ℝ) → ℝ) x| ^ 2 := (sq_abs _).symm
        _ ≤ _ := pow_le_pow_left₀ (abs_nonneg _) (h1.trans h2) 2
    calc Gf (cut (M * (k + 1)) : (Fin d → ℝ) → ℝ) (cut (M * (k + 1))) x
        ≤ ∑ _i : Fin d, (C / ((M : ℝ) * ((k : ℝ) + 1))) ^ 2 :=
          Finset.sum_le_sum fun i _ => hterm i
      _ = d * C ^ 2 / ((M : ℝ) ^ 2 * ((k : ℝ) + 1) ^ 2) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp
      _ ≤ M ^ 2 / ((M : ℝ) ^ 2 * ((k : ℝ) + 1) ^ 2) :=
          div_le_div_of_nonneg_right hdC (by positivity)
      _ = (1 / ((k : ℝ) + 1)) ^ 2 := by field_simp

/-- the semigroup-free extended-algebra axioms F1, F2, F4–F7, F9 for `𝒜 = C^∞` (assembly of `FullEasy.lean`). -/
theorem preFull_lebesgueRd (hd : 1 ≤ d) : PreFull (lebesgueRdDiffusion d hd) (A d) where
  A₀_le := fun _ hf => A₀_le_A hf
  A_measurable := fun _ hf => (mem_A.1 hf).continuous.measurable
  ideal := fun _ hf _ hh => F1 hf hh
  pos_detect := fun _ hf h => F2 hf h
  L_mem_A := fun _ hf => L_mem_A hf
  ΓA_nonneg := fun _ hf => F5 hd hf
  diffusion_Γ_A := fun k ψ hψ f hf _ hg => F6Γ hd k ψ hψ f hf hg
  ibp_A := fun _ hf _ hg => F7 hd hf hg
  connected := fun _ hf h => F9 hd hf h

/-- limits of graph-convergent test functions lie in the domain (closedness of the generator). -/
theorem domain_of_approx (hd : 1 ≤ d) {u y : Lp ℝ 2 (volume : Measure (Fin d → ℝ))} (a : ℕ → (Fin d → ℝ) → ℝ)
    (ha : ∀ n, a n ∈ A₀ d)
    (h1 : Tendsto (fun n => (lebesgueRdDiffusion d hd).cls ⟨a n, ha n⟩) atTop (𝓝 u))
    (h2 : Tendsto (fun n => (lebesgueRdDiffusion d hd).Lcls ⟨a n, ha n⟩) atTop (𝓝 y)) :
    ∃ h : u ∈ (lebesgueRdDiffusion d hd).generator.domain,
      (lebesgueRdDiffusion d hd).generator ⟨u, h⟩ = y := by
  set D := lebesgueRdDiffusion d hd with hD
  have hG : D.generator.IsClosed := (DiffusionTriple.formData D).generator_isClosed
  have hmem : ∀ n, (D.cls ⟨a n, ha n⟩, D.Lcls ⟨a n, ha n⟩) ∈ D.generator.graph := by
    intro n
    rw [LinearPMap.mem_graph_iff]
    refine ⟨⟨D.cls ⟨a n, ha n⟩, D.cls_mem_generator_domain ⟨a n, ha n⟩⟩, ?_⟩
    simp only [true_and]
    rw [D.generator_cls ⟨a n, ha n⟩ (D.cls_mem_generator_domain ⟨a n, ha n⟩)]
  have hlim : (u, y) ∈ D.generator.graph :=
    hG.mem_of_tendsto (h1.prodMk_nhds h2) (Filter.Eventually.of_forall hmem)
  rw [LinearPMap.mem_graph_iff] at hlim
  obtain ⟨z, hz⟩ := hlim
  simp only [] at hz
  obtain ⟨hz1, hz2⟩ := hz
  subst hz1
  exact ⟨z.2, hz2⟩

/-- smooth `u` with `u, ∂ᵢu, Δu ∈ L²` lies in `𝒟(L)` with `L u = Δu` (cut-offs + closedness of the Friedrichs generator). -/
theorem domain_of_smooth_L2 (hd : 1 ≤ d) {u : (Fin d → ℝ) → ℝ} (hu : Sm u) (h0 : MemLp u 2 volume)
    (h1 : ∀ i, MemLp (dd i u) 2 volume) (h2 : MemLp (Lf u) 2 volume) :
    ∃ h : h0.toLp u ∈ (lebesgueRdDiffusion d hd).generator.domain,
      (lebesgueRdDiffusion d hd).generator ⟨h0.toLp u, h⟩ = h2.toLp (Lf u) := by
  have c := cutoff_tendsto_Rd hu h0 h1 h2 (fun n => memLp_of (a_mem_cut hu n) 2)
    (fun n => memLp_of (Lf_mem (a_mem_cut hu n)) 2)
  exact domain_of_approx hd (fun n => cut n * u) (a_mem_cut hu) c.1 c.2

/-- the smoothed test functions lie in `𝒟(L)`, `L (heat φ) = heat (Δφ)` (uses only the `HeatAPI` facts). -/
theorem heatL2_mem_domain (hd : 1 ≤ d) {φ : (Fin d → ℝ) → ℝ} (hφ : φ ∈ A₀ d) (a : ℝ) :
    ∃ h : heatL2 φ a ∈ (lebesgueRdDiffusion d hd).generator.domain,
      (lebesgueRdDiffusion d hd).generator ⟨heatL2 φ a, h⟩ = heatL2 (Lf φ) a := by
  have h0 := memLp_heatRd hφ a
  have h1 : ∀ i, MemLp (dd i (heatRd a φ)) 2 volume := fun i => by
    rw [dd_heatRd hφ a i]; exact memLp_heatRd (dd_mem hφ i) a
  have hL := memLp_heatRd (Lf_mem hφ) a
  have h2 : MemLp (Lf (heatRd a φ)) 2 volume := by rw [Lf_heatRd hφ a]; exact hL
  obtain ⟨h, hg⟩ := domain_of_smooth_L2 hd (heatRd_smooth hφ a) h0 h1 h2
  have e1 : heatL2 φ a = h0.toLp (heatRd a φ) := by simp only [heatL2, h0, ↓reduceDIte]
  have e2 : heatL2 (Lf φ) a = h2.toLp (Lf (heatRd a φ)) := by
    simp only [heatL2, hL, ↓reduceDIte]
    refine Lp.ext ?_
    filter_upwards [hL.coeFn_toLp, h2.coeFn_toLp] with x h3 h4
    rw [h3, h4, Lf_heatRd hφ a]
  rw [e2]
  refine ⟨e1 ▸ h, ?_⟩
  rw [← hg]
  congr 1
  exact Subtype.ext e1

end MarkovTriple.BGL.LebesgueRd

#print axioms isComplete_lebesgueRd
