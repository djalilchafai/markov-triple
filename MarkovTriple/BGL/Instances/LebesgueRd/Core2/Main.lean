import Mathlib
import MarkovTriple.BGL.Instances.LebesgueRd.Core2.Cut4
import MarkovTriple.BGL.Instances.LebesgueRd.Full.Main
import MarkovTriple.BGL.Instances.LebesgueRd.Full.Esa
import MarkovTriple.BGL.Instances.LebesgueRd.Full.GaussFinite
import MarkovTriple.BGL.Instances.GibbsRd.Core2RdWitness
import MarkovTriple.BGL.Theory.Extension.Core2Reduce

/-!
# `Core2` for `(ℝ^d, Lebesgue)` and the Gaussian `ℝ^d` triple (Round 25, stream F)

Statements: `STATEMENTS_R25_F.md`.  Route (DIFFERENCE FROM BGL, which never states `Core2`): `core2_of_dense`; if `w ⟂ (1-L)²𝒜₀`,
the fourth-order cut-off (`cutoff4_graph_aux`) transports the orthogonality to `heat_a φ`, then two applications of the
heat-flow ODE trick of R24-A (F10) give `⟪w, φ⟫ = 0`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace

namespace MarkovTriple.BGL.LebesgueRd

open MarkovTriple.BGL

variable {d : ℕ}

/-- `heat_a ψ` with `ψ ∈ 𝒜₀` is smooth and its jets are in `L²`. -/
lemma memLp_heat_dd {ψ : (Fin d → ℝ) → ℝ} (hψ : ψ ∈ A₀ d) (a : ℝ) (i : Fin d) :
    MemLp (dd i (heatRd a ψ)) 2 volume := by
  rw [dd_heatRd hψ a i]; exact memLp_heatRd (dd_mem hψ i) a

lemma memLp_heat_Lf {ψ : (Fin d → ℝ) → ℝ} (hψ : ψ ∈ A₀ d) (a : ℝ) :
    MemLp (Lf (heatRd a ψ)) 2 volume := by
  rw [Lf_heatRd hψ a]; exact memLp_heatRd (Lf_mem hψ) a

lemma cls_eq_toLp (hd : 1 ≤ d) (b : (lebesgueRdDiffusion d hd).A₀)
    (h : MemLp b.1 2 (volume : Measure (Fin d → ℝ))) :
    (lebesgueRdDiffusion d hd).cls b = h.toLp b.1 := by
  refine Lp.ext ?_
  filter_upwards [DiffusionTriple.coeFn_cls (lebesgueRdDiffusion d hd) b, h.coeFn_toLp] with x p q
  rw [p, q]

lemma Lcls_eq_toLp (hd : 1 ≤ d) (b : (lebesgueRdDiffusion d hd).A₀)
    (h : MemLp (Lf b.1) 2 (volume : Measure (Fin d → ℝ))) :
    (lebesgueRdDiffusion d hd).Lcls b = h.toLp (Lf b.1) := by
  refine Lp.ext ?_
  filter_upwards [DiffusionTriple.coeFn_Lcls (lebesgueRdDiffusion d hd) b, h.coeFn_toLp] with x p q
  rw [p, q]

lemma heatL2_eq_toLp {ψ : (Fin d → ℝ) → ℝ} (hψ : ψ ∈ A₀ d) (s : ℝ) :
    heatL2 ψ s = (memLp_heatRd hψ s).toLp (heatRd s ψ) := by
  unfold heatL2
  simp [memLp_heatRd hψ s]

/-- the cut-offs of `heat_a φ` converge in the `L²`-graph norm of `L²`: `[b_n], [L b_n], [LL b_n]`. -/
theorem heat_graph4 (hd : 1 ≤ d) {φ : (Fin d → ℝ) → ℝ} (hφ : φ ∈ A₀ d) (a : ℝ) :
    ∃ b : ℕ → (lebesgueRdFull d hd).A₀,
      Tendsto (fun n => (lebesgueRdFull d hd).toDiffusionTriple.cls (b n)) atTop (𝓝 (heatL2 φ a)) ∧
      Tendsto (fun n => (lebesgueRdFull d hd).toDiffusionTriple.Lcls (b n)) atTop (𝓝 (heatL2 (Lf φ) a)) ∧
      Tendsto (fun n => FullTriple.LLₗ (lebesgueRdFull d hd) (b n)) atTop
        (𝓝 (heatL2 (Lf (Lf φ)) a)) := by
  set v : (Fin d → ℝ) → ℝ := heatRd a φ with hv
  have hvs : Sm v := heatRd_smooth hφ a
  have h0 : MemLp v 2 volume := memLp_heatRd hφ a
  have h1 : ∀ i, MemLp (dd i v) 2 volume := fun i => memLp_heat_dd hφ a i
  have h2 : MemLp (Lf v) 2 volume := memLp_heat_Lf hφ a
  have h11 : ∀ j i, MemLp (dd i (dd j v)) 2 volume := fun j i => by
    rw [hv, dd_heatRd hφ a j, dd_heatRd (dd_mem hφ j) a i]; exact memLp_heatRd (dd_mem (dd_mem hφ j) i) a
  have h12 : ∀ j, MemLp (Lf (dd j v)) 2 volume := fun j => by
    rw [hv, dd_heatRd hφ a j, Lf_heatRd (dd_mem hφ j) a]; exact memLp_heatRd (Lf_mem (dd_mem hφ j)) a
  have h3 : ∀ i, MemLp (dd i (Lf v)) 2 volume := fun i => by
    rw [hv, Lf_heatRd hφ a, dd_heatRd (Lf_mem hφ) a i]; exact memLp_heatRd (dd_mem (Lf_mem hφ) i) a
  have hLLv : Lf (Lf v) = heatRd a (Lf (Lf φ)) := by rw [hv, Lf_heatRd hφ a, Lf_heatRd (Lf_mem hφ) a]
  have h4 : MemLp (Lf (Lf v)) 2 volume := by rw [hLLv]; exact memLp_heatRd (Lf_mem (Lf_mem hφ)) a
  have hmem : ∀ n : ℕ, cut n * v ∈ A₀ d := fun n => mem_A₀.2 ⟨(cut_smooth n).mul hvs, (cut_cs n).mul_right⟩
  have hm : ∀ n : ℕ, MemLp (cut n * v) 2 volume := fun n => memLp_of (hmem n) 2
  have hm2 : ∀ n : ℕ, MemLp (Lf (cut n * v)) 2 volume := fun n => memLp_of (Lf_mem (hmem n)) 2
  have hm4 : ∀ n : ℕ, MemLp (Lf (Lf (cut n * v))) 2 volume := fun n => memLp_of (Lf_mem (Lf_mem (hmem n))) 2
  obtain ⟨c1, c2⟩ := cutoff_graph hvs h0 h1 h2 hm hm2
  have c3 := tendsto_toLp_of_integral_sq' hm4 h4 (cutoff4_graph_aux hvs h0 h1 h2 h11 h12 h3 h4)
  refine ⟨fun n => ⟨cut n * v, hmem n⟩, ?_, ?_, ?_⟩
  · have e : heatL2 φ a = h0.toLp v := by rw [heatL2_eq_toLp hφ a]
    rw [e]
    refine c1.congr fun n => ?_
    exact (cls_eq_toLp hd ⟨cut n * v, hmem n⟩ (hm n)).symm
  · have e : heatL2 (Lf φ) a = h2.toLp (Lf v) := by
      rw [heatL2_eq_toLp (Lf_mem hφ) a]
      refine Lp.ext ?_
      filter_upwards [(memLp_heatRd (Lf_mem hφ) a).coeFn_toLp, h2.coeFn_toLp] with x p q
      rw [p, q, hv, Lf_heatRd hφ a]
    rw [e]
    refine c2.congr fun n => ?_
    exact (Lcls_eq_toLp hd ⟨cut n * v, hmem n⟩ (hm2 n)).symm
  · have e : heatL2 (Lf (Lf φ)) a = h4.toLp (Lf (Lf v)) := by
      rw [heatL2_eq_toLp (Lf_mem (Lf_mem hφ)) a]
      refine Lp.ext ?_
      filter_upwards [(memLp_heatRd (Lf_mem (Lf_mem hφ)) a).coeFn_toLp, h4.coeFn_toLp] with x p q
      rw [p, q, hLLv]
    rw [e]
    refine c3.congr fun n => ?_
    exact (Lcls_eq_toLp hd ⟨Lf (cut n * v), Lf_mem (hmem n)⟩ (hm4 n)).symm


/-- orthogonality to `(1-L)²𝒜₀` transported to the smoothed test functions. -/
theorem inner_heat_orth4 (hd : 1 ≤ d) {φ : (Fin d → ℝ) → ℝ} (hφ : φ ∈ A₀ d) (a : ℝ)
    (w : Lp ℝ 2 (volume : Measure (Fin d → ℝ)))
    (hw : ∀ b : (lebesgueRdFull d hd).A₀, inner ℝ (FullTriple.Ψₗ (lebesgueRdFull d hd) b) w = 0) :
    inner ℝ w (heatL2 φ a) - 2 * inner ℝ w (heatL2 (Lf φ) a) + inner ℝ w (heatL2 (Lf (Lf φ)) a) = 0 := by
  obtain ⟨b, c1, c2, c3⟩ := heat_graph4 hd hφ a
  have hΨ : ∀ n, FullTriple.Ψₗ (lebesgueRdFull d hd) (b n) =
      (lebesgueRdFull d hd).toDiffusionTriple.cls (b n) - (2 : ℝ) •
        (lebesgueRdFull d hd).toDiffusionTriple.Lcls (b n) + FullTriple.LLₗ (lebesgueRdFull d hd) (b n) := by
    intro n
    simp only [FullTriple.Ψₗ, LinearMap.sub_apply, FullTriple.Φₗ_apply, DiffusionTriple.Lclsₗ]
    rw [two_smul]
    show ((lebesgueRdFull d hd).toDiffusionTriple.cls (b n) - (lebesgueRdFull d hd).toDiffusionTriple.Lcls (b n)) -
      ((lebesgueRdFull d hd).toDiffusionTriple.Lcls (b n) - FullTriple.LLₗ (lebesgueRdFull d hd) (b n)) =
      (lebesgueRdFull d hd).toDiffusionTriple.cls (b n) - ((lebesgueRdFull d hd).toDiffusionTriple.Lcls (b n) +
        (lebesgueRdFull d hd).toDiffusionTriple.Lcls (b n)) + FullTriple.LLₗ (lebesgueRdFull d hd) (b n)
    abel
  have hlim : Tendsto (fun n => inner ℝ (FullTriple.Ψₗ (lebesgueRdFull d hd) (b n)) w) atTop
      (𝓝 (inner ℝ (heatL2 φ a - (2 : ℝ) • heatL2 (Lf φ) a + heatL2 (Lf (Lf φ)) a) w)) := by
    have h5 := ((c1.sub (c2.const_smul (2 : ℝ))).add c3)
    have := Filter.Tendsto.inner (𝕜 := ℝ) h5 (tendsto_const_nhds (x := w))
    exact this.congr fun n => by rw [hΨ n]
  have hz : (fun n => inner ℝ (FullTriple.Ψₗ (lebesgueRdFull d hd) (b n)) w) = fun _ => 0 :=
    funext fun n => hw (b n)
  rw [hz] at hlim
  have h0 := tendsto_nhds_unique hlim tendsto_const_nhds
  rw [inner_add_left, inner_sub_left, inner_smul_left] at h0
  simp only [real_inner_comm w] at h0
  simpa using h0


/-- `g' = s g`, `g` bounded ⇒ `g ≡ 0`. -/
lemma ode_all_zero (g : ℝ → ℝ) (hg : ∀ s, HasDerivAt g (s * g s) s) (B : ℝ) (hB : ∀ s, |g s| ≤ B) :
    ∀ s, g s = 0 := by
  have h0 := zero_of_ode_bdd g hg B hB
  set h : ℝ → ℝ := fun s => g s * Real.exp (-(s ^ 2 / 2)) with hh
  have hd : ∀ s, HasDerivAt h 0 s := by
    intro s
    have e1 : HasDerivAt (fun s : ℝ => -(s ^ 2 / 2)) (-s) s :=
      (((hasDerivAt_pow 2 s).div_const 2).neg).congr_deriv (by simp)
    have := (hg s).mul e1.exp
    refine this.congr_deriv ?_
    ring
  intro s
  have hc : h s = h 0 :=
    is_const_of_deriv_eq_zero (fun x => (hd x).differentiableAt) (fun x => (hd x).deriv) s 0
  have h00 : h 0 = 0 := by simp [hh, h0]
  have h1 : g s * Real.exp (-(s ^ 2 / 2)) = 0 := hc.trans h00
  exact (mul_eq_zero.1 h1).resolve_right (Real.exp_ne_zero _)

/-- **Orthogonality to `(1-L)²𝒜₀` forces `w = 0`.** -/
theorem eq_zero_of_orth4 (hd : 1 ≤ d) (w : Lp ℝ 2 (volume : Measure (Fin d → ℝ)))
    (hw : ∀ b : (lebesgueRdFull d hd).A₀, inner ℝ (FullTriple.Ψₗ (lebesgueRdFull d hd) b) w = 0) : w = 0 := by
  refine (lebesgueRdDiffusion d hd).eq_zero_of_orth w (fun g => ?_)
  obtain ⟨φ, hφ⟩ := g
  set G0 : ℝ → ℝ := fun s => inner ℝ w (heatL2 φ s) with hG0
  set G1 : ℝ → ℝ := fun s => inner ℝ w (heatL2 (Lf φ) s) with hG1
  set G2 : ℝ → ℝ := fun s => inner ℝ w (heatL2 (Lf (Lf φ)) s) with hG2
  have hrel : ∀ s, G2 s = 2 * G1 s - G0 s := fun s => by
    have := inner_heat_orth4 hd hφ s w hw
    simp only [hG0, hG1, hG2]; linarith
  have hd0 : ∀ s, HasDerivAt G0 (s * G1 s) s := fun s => hasDerivAt_inner_heat hφ w s
  have hd1 : ∀ s, HasDerivAt G1 (s * G2 s) s := fun s => hasDerivAt_inner_heat (Lf_mem hφ) w s
  have hb : ∀ (ψ : (Fin d → ℝ) → ℝ), ψ ∈ A₀ d → ∀ s, |inner ℝ w (heatL2 ψ s)| ≤ ‖w‖ * ‖heatL2 ψ 0‖ :=
    fun ψ hψ s => (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left (norm_heatL2_le hψ s) (norm_nonneg _))
  have hb0 : ∀ s, |G0 s| ≤ ‖w‖ * ‖heatL2 φ 0‖ := hb φ hφ
  have hb1 : ∀ s, |G1 s| ≤ ‖w‖ * ‖heatL2 (Lf φ) 0‖ := hb _ (Lf_mem hφ)
  -- `H = G₁ - G₀` solves `H' = s H`
  have hH : ∀ s, HasDerivAt (fun t => G1 t - G0 t) (s * (G1 s - G0 s)) s := fun s => by
    refine ((hd1 s).sub (hd0 s)).congr_deriv ?_
    rw [hrel s]; ring
  have hHz := ode_all_zero _ hH (‖w‖ * ‖heatL2 (Lf φ) 0‖ + ‖w‖ * ‖heatL2 φ 0‖) (fun s =>
    (abs_sub _ _).trans (add_le_add (hb1 s) (hb0 s)))
  have hG : ∀ s, HasDerivAt G0 (s * G0 s) s := fun s => by
    have : G1 s = G0 s := by have := hHz s; linarith
    simpa [this] using hd0 s
  have h0 := zero_of_ode_bdd G0 hG _ hb0
  simp only [hG0] at h0
  rw [heatL2_zero hφ] at h0
  exact h0

/-- **`(1-L)²𝒜₀` is dense in `L²(ℝ^d)`.** -/
theorem dense_Ψ_lebesgueRd (hd : 1 ≤ d) : Dense (Set.range (FullTriple.Ψₗ (lebesgueRdFull d hd))) := by
  have : Set.range (FullTriple.Ψₗ (lebesgueRdFull d hd)) =
      ((LinearMap.range (FullTriple.Ψₗ (lebesgueRdFull d hd)) : Submodule ℝ _) : Set _) :=
    (LinearMap.coe_range _).symm
  rw [this, Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    Submodule.eq_bot_iff]
  intro w hw
  refine eq_zero_of_orth4 hd w fun b => ?_
  exact (Submodule.mem_orthogonal _ _).1 hw _ ⟨b, rfl⟩

/-- **F2: `Core2` for `(ℝ^d, Lebesgue)`, `d ≥ 1`.** -/
theorem lebesgueRdFull_core2 (hd : 1 ≤ d) : (lebesgueRdFull d hd).Core2 :=
  FullTriple.core2_of_dense (dense_Ψ_lebesgueRd hd)

/-- **F1: `Core2` for the Gaussian `ℝ^d` triple** (R18 `gaussData_core2`). -/
theorem gaussRdFull_core2 (d : ℕ) : (gaussRdFull d).Core2 :=
  Instances.GibbsRd.gaussData_core2 d

/-- **F3: the `Core2`-based converse of BGL Prop 3.3.17 for `(ℝ^d, Lebesgue)`.** -/
theorem lebesgueRdFull_mem_domain_of_Γ₂ (hd : 1 ≤ d) {ρ : ℝ} {n : ℝ≥0∞}
    (hCD : (lebesgueRdFull d hd).CD ρ n) {f : (Fin d → ℝ) → ℝ} (hf : f ∈ (lebesgueRdFull d hd).A)
    (hf2 : MemLp f 2 (lebesgueRdFull d hd).μ)
    (hG : Integrable (FullTriple.G (lebesgueRdFull d hd) f f) (lebesgueRdFull d hd).μ)
    (hG2 : Integrable ((lebesgueRdFull d hd).toDiffusionTriple.Γ₂ f f) (lebesgueRdFull d hd).μ) :
    ∃ hF : hf2.toLp f ∈ (lebesgueRdFull d hd).toDiffusionTriple.generator.domain,
      (((lebesgueRdFull d hd).toDiffusionTriple.generator ⟨hf2.toLp f, hF⟩ :
        Lp ℝ 2 (lebesgueRdFull d hd).μ) : (Fin d → ℝ) → ℝ) =ᵐ[(lebesgueRdFull d hd).μ]
        (lebesgueRdFull d hd).L f :=
  FullTriple.mem_domain_of_Γ₂ hCD (lebesgueRdFull_core2 hd) hf hf2 hG hG2

end MarkovTriple.BGL.LebesgueRd
