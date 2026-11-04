import Mathlib
import MarkovTriple.BGL.Instances.LebesgueRd.Full.EsaCut
import MarkovTriple.BGL.Instances.LebesgueRd.Full.HeatDeriv
import MarkovTriple.BGL.Instances.Gibbs.FunctESA

/-!
# F10 (`esa_lebesgueRd`): `C_c^∞(ℝ^d)` is a core for the Friedrichs generator of `(ℝ^d, Lebesgue)`

Heat-flow argument (Round 24, stream A, part B-b; replaces the 1-D resolvent ODE of `Lebesgue/Core.lean`):
if `w ⟂ (1 - L)𝒜₀` then `g(s) = ⟪w, heatL2 φ s⟫` satisfies `g' = s g`, `|g| ≤ ‖w‖ ‖φ‖₂`, hence `g(0) = 0`,
i.e. `w ⟂ 𝒜₀`, `w = 0`.  The orthogonality `w ⟂ (1 - L)𝒜₀` is first transported to the heat-smoothed test
functions through the cut-off approximants `ζ_n heatRd s φ ∈ 𝒜₀` (`heat_graph`).
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace

namespace MarkovTriple.BGL.LebesgueRd

open MarkovTriple.BGL

variable {d : ℕ}

lemma heatL2_eq {φ : (Fin d → ℝ) → ℝ} (hφ : φ ∈ A₀ d) (s : ℝ) :
    heatL2 φ s = (memLp_heatRd hφ s).toLp (heatRd s φ) := by
  unfold heatL2
  simp [memLp_heatRd hφ s]

/-- the cut-offs of the smoothed test function are graph approximants of `heatL2 φ s`. -/
theorem heat_graph (hd : 1 ≤ d) {φ : (Fin d → ℝ) → ℝ} (hφ : φ ∈ A₀ d) (s : ℝ) :
    ∃ a : ℕ → (lebesgueRdDiffusion d hd).A₀,
      Tendsto (fun n => (lebesgueRdDiffusion d hd).cls (a n)) atTop (𝓝 (heatL2 φ s)) ∧
      Tendsto (fun n => (lebesgueRdDiffusion d hd).Lcls (a n)) atTop (𝓝 (heatL2 (Lf φ) s)) := by
  set u : (Fin d → ℝ) → ℝ := heatRd s φ with hu
  have hus : Sm u := heatRd_smooth hφ s
  have h0 : MemLp u 2 volume := memLp_heatRd hφ s
  have h1 : ∀ i, MemLp (dd i u) 2 volume := fun i => by
    rw [hu, dd_heatRd hφ s i]; exact memLp_heatRd (dd_mem hφ i) s
  have hLu : Lf u = heatRd s (Lf φ) := Lf_heatRd hφ s
  have h2 : MemLp (Lf u) 2 volume := by rw [hLu]; exact memLp_heatRd (Lf_mem hφ) s
  have hmem : ∀ n : ℕ, cut n * u ∈ A₀ d := fun n =>
    mem_A₀.2 ⟨(cut_smooth n).mul hus, (cut_cs n).mul_right⟩
  have hm : ∀ n : ℕ, MemLp (cut n * u) 2 volume := fun n => memLp_of (hmem n) 2
  have hm2 : ∀ n : ℕ, MemLp (Lf (cut n * u)) 2 volume := fun n => memLp_of (Lf_mem (hmem n)) 2
  obtain ⟨c1, c2⟩ := cutoff_graph hus h0 h1 h2 hm hm2
  refine ⟨fun n => ⟨cut n * u, hmem n⟩, ?_, ?_⟩
  · have e : heatL2 φ s = h0.toLp u := by rw [heatL2_eq hφ s]
    rw [e]; exact c1
  · have e : heatL2 (Lf φ) s = h2.toLp (Lf u) := by
      rw [heatL2_eq (Lf_mem hφ) s]
      refine Lp.ext ?_
      filter_upwards [(memLp_heatRd (Lf_mem hφ) s).coeFn_toLp, h2.coeFn_toLp] with x p q
      rw [p, q, hLu]
    rw [e]; exact c2

/-- transport of `⟪w, (1 - L) a⟫ = 0` (`a ∈ 𝒜₀`) to the smoothed test functions. -/
theorem inner_heat_sub (hd : 1 ≤ d) {φ : (Fin d → ℝ) → ℝ} (hφ : φ ∈ A₀ d) (s : ℝ)
    (w : Lp ℝ 2 (volume : Measure (Fin d → ℝ)))
    (hw : ∀ a : (lebesgueRdDiffusion d hd).A₀,
      inner ℝ ((lebesgueRdDiffusion d hd).cls a - (lebesgueRdDiffusion d hd).Lcls a) w = 0) :
    inner ℝ w (heatL2 φ s) = inner ℝ w (heatL2 (Lf φ) s) := by
  obtain ⟨a, c1, c2⟩ := heat_graph hd hφ s
  have hlim : Tendsto (fun n => inner ℝ ((lebesgueRdDiffusion d hd).cls (a n) -
      (lebesgueRdDiffusion d hd).Lcls (a n)) w) atTop
      (𝓝 (inner ℝ (heatL2 φ s - heatL2 (Lf φ) s) w)) := (c1.sub c2).inner tendsto_const_nhds
  have hz : (fun n => inner ℝ ((lebesgueRdDiffusion d hd).cls (a n) -
      (lebesgueRdDiffusion d hd).Lcls (a n)) w) = fun _ => 0 := funext fun n => hw (a n)
  rw [hz] at hlim
  have := tendsto_nhds_unique hlim tendsto_const_nhds
  rw [inner_sub_left, sub_eq_zero] at this
  rw [real_inner_comm, this, real_inner_comm]

theorem hasDerivAt_inner_heat {φ : (Fin d → ℝ) → ℝ} (hφ : φ ∈ A₀ d) (w : Lp ℝ 2 (volume : Measure (Fin d → ℝ)))
    (s : ℝ) :
    HasDerivAt (fun b : ℝ => inner ℝ w (heatL2 φ b)) (s * inner ℝ w (heatL2 (Lf φ) s)) s := by
  have h := (hasDerivAt_const s w).inner ℝ (hasDerivAt_heatL2 hφ s)
  simpa [inner_smul_right] using h

/-- `g' = s g`, `g` bounded ⇒ `g 0 = 0`. -/
theorem zero_of_ode_bdd (g : ℝ → ℝ) (hg : ∀ s, HasDerivAt g (s * g s) s) (B : ℝ)
    (hB : ∀ s, |g s| ≤ B) : g 0 = 0 := by
  set h : ℝ → ℝ := fun s => g s * Real.exp (-(s ^ 2 / 2)) with hh
  have hd : ∀ s, HasDerivAt h 0 s := by
    intro s
    have e1 : HasDerivAt (fun s : ℝ => -(s ^ 2 / 2)) (-s) s :=
      (((hasDerivAt_pow 2 s).div_const 2).neg).congr_deriv (by simp)
    have := (hg s).mul e1.exp
    refine this.congr_deriv ?_
    ring
  have hc : ∀ s, h s = h 0 := fun s =>
    is_const_of_deriv_eq_zero (fun x => (hd x).differentiableAt) (fun x => (hd x).deriv) s 0
  have hgs : ∀ s, g s = g 0 * Real.exp (s ^ 2 / 2) := by
    intro s
    have := hc s
    simp only [hh, zero_pow two_ne_zero, zero_div, neg_zero, Real.exp_zero, mul_one] at this
    have hne : Real.exp (-(s ^ 2 / 2)) ≠ 0 := Real.exp_ne_zero _
    calc g s = g s * Real.exp (-(s ^ 2 / 2)) * Real.exp (s ^ 2 / 2) := by
          rw [mul_assoc, ← Real.exp_add]; simp
      _ = _ := by rw [this]
  by_contra hne
  have hpos : 0 < |g 0| := abs_pos.2 hne
  have hB0 : |g 0| ≤ B := hB 0
  set q : ℝ := B / |g 0| with hq
  have hq0 : 0 ≤ q := div_nonneg (hpos.le.trans hB0) hpos.le
  have h1 := hB (Real.sqrt (2 * q))
  rw [hgs, abs_mul, abs_of_pos (Real.exp_pos _), Real.sq_sqrt (by positivity)] at h1
  have h2 : q + 1 ≤ Real.exp (2 * q / 2) := by
    have := Real.add_one_le_exp q
    rwa [show 2 * q / 2 = q by ring]
  have h3 : B < |g 0| * Real.exp (2 * q / 2) := by
    have : B = |g 0| * q := by rw [hq]; field_simp
    nlinarith
  linarith

/-- **F10 (ESA)**: `𝒜₀ = C_c^∞(ℝ^d)` is a core for the Friedrichs generator of `(ℝ^d, Lebesgue)`. -/
theorem esa_lebesgueRd (hd : 1 ≤ d) : (lebesgueRdDiffusion d hd).ESAProp := by
  refine DiffusionTriple.core_of_orth _ (fun w hw => ?_)
  refine (lebesgueRdDiffusion d hd).eq_zero_of_orth w (fun g => ?_)
  obtain ⟨φ, hφ⟩ := g
  set G : ℝ → ℝ := fun s => inner ℝ w (heatL2 φ s) with hG
  have hder : ∀ s, HasDerivAt G (s * G s) s := fun s => by
    have := hasDerivAt_inner_heat hφ w s
    rwa [← inner_heat_sub hd hφ s w hw] at this
  have hbd : ∀ s, |G s| ≤ ‖w‖ * ‖heatL2 φ 0‖ := fun s =>
    (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (norm_heatL2_le hφ s) (norm_nonneg _))
  have h0 := zero_of_ode_bdd G hder _ hbd
  simp only [hG] at h0
  rw [heatL2_zero hφ] at h0
  exact h0

end MarkovTriple.BGL.LebesgueRd
