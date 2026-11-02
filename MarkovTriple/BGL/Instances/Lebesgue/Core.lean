import Mathlib
import MarkovTriple.BGL.Instances.Lebesgue.Diffusion
import MarkovTriple.BGL.Instances.Lebesgue.Cutoff
import MarkovTriple.BGL.Instances.Lebesgue.ODE
import MarkovTriple.BGL.SemigroupLemmas
import MarkovTriple.BGL.Semigroup.Characterization
import MarkovTriple.BGL.Calculus.Density
import MarkovTriple.BGL.Semigroup.ESA

/-!
# Generator, ESA (F10) and ergodicity (S10) for the Brownian triple on `(ℝ, Lebesgue)`

* `domain_of_smooth_L2`: a smooth `u` with `u, u', u'' ∈ L²` lies in `𝒟(L)` and `L u = u''`
  (closedness of the Friedrichs generator + cutoffs).
* F10: `C_c^∞` is a core (Nelson-type argument with the explicit solution of `v - v'' = ψ`).
* S10: from the energy form of ergodicity (`ergodic_iff_energy`) and du Bois-Reymond.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal LinearPMap InnerProductSpace

namespace MarkovTriple.BGL.Lebesgue

open MarkovTriple.BGL

lemma cls_eq {f : ℝ → ℝ} (hf : f ∈ A₀) (h : MemLp f 2 volume) :
    lebesgueDiffusion.cls ⟨f, hf⟩ = h.toLp f := rfl

lemma Lcls_eq {f : ℝ → ℝ} (hf : f ∈ A₀) (h : MemLp (Lf f) 2 volume) :
    lebesgueDiffusion.Lcls ⟨f, hf⟩ = h.toLp (Lf f) := rfl

/-- limits of graph-convergent test functions lie in the domain. -/
theorem domain_of_approx {u y : Lp ℝ 2 (volume : Measure ℝ)} (a : ℕ → ℝ → ℝ) (ha : ∀ n, a n ∈ A₀)
    (h1 : Tendsto (fun n => lebesgueDiffusion.cls ⟨a n, ha n⟩) atTop (𝓝 u))
    (h2 : Tendsto (fun n => lebesgueDiffusion.Lcls ⟨a n, ha n⟩) atTop (𝓝 y)) :
    ∃ h : u ∈ lebesgueDiffusion.generator.domain, lebesgueDiffusion.generator ⟨u, h⟩ = y := by
  have hG : lebesgueDiffusion.generator.IsClosed := (DiffusionTriple.formData lebesgueDiffusion).generator_isClosed
  have hmem : ∀ n, (lebesgueDiffusion.cls ⟨a n, ha n⟩, lebesgueDiffusion.Lcls ⟨a n, ha n⟩) ∈ lebesgueDiffusion.generator.graph := by
    intro n
    rw [LinearPMap.mem_graph_iff]
    refine ⟨⟨lebesgueDiffusion.cls ⟨a n, ha n⟩, lebesgueDiffusion.cls_mem_generator_domain ⟨a n, ha n⟩⟩, ?_⟩
    simp only [true_and]
    rw [lebesgueDiffusion.generator_cls ⟨a n, ha n⟩ (lebesgueDiffusion.cls_mem_generator_domain ⟨a n, ha n⟩)]
  have hlim : (u, y) ∈ lebesgueDiffusion.generator.graph :=
    hG.mem_of_tendsto (h1.prodMk_nhds h2) (Filter.Eventually.of_forall hmem)
  rw [LinearPMap.mem_graph_iff] at hlim
  obtain ⟨z, hz⟩ := hlim
  simp only [] at hz
  obtain ⟨hz1, hz2⟩ := hz
  subst hz1
  exact ⟨z.2, hz2⟩

lemma a_mem {u : ℝ → ℝ} (hu : Sm u) (n : ℕ) : chiR (Rn n) * u ∈ A₀ :=
  mem_A₀.2 ⟨(chiR_smooth _).mul hu, (chiR_cs (Rn_pos n).ne').mul_right⟩

lemma cutoff_graph {u : ℝ → ℝ} (hu : Sm u) (h0 : MemLp u 2 volume)
    (h1 : MemLp (deriv u) 2 volume) (h2 : MemLp (deriv (deriv u)) 2 volume) :
    Tendsto (fun n : ℕ => lebesgueDiffusion.cls ⟨chiR (Rn n) * u, a_mem hu n⟩) atTop (𝓝 (h0.toLp u)) ∧
      Tendsto (fun n : ℕ => lebesgueDiffusion.Lcls ⟨chiR (Rn n) * u, a_mem hu n⟩) atTop
        (𝓝 (h2.toLp (deriv (deriv u)))) :=
  cutoff_tendsto hu h0 h1 h2 (fun n => memLp_of (a_mem hu n) 2)
    (fun n => memLp_of (deriv_mem (deriv_mem (a_mem hu n))) 2)

/-- **Smooth functions with `u, u', u'' ∈ L²` are in `𝒟(L)`, with `L u = u''`.** -/
theorem domain_of_smooth_L2 {u : ℝ → ℝ} (hu : Sm u) (h0 : MemLp u 2 volume)
    (h1 : MemLp (deriv u) 2 volume) (h2 : MemLp (deriv (deriv u)) 2 volume) :
    ∃ h : h0.toLp u ∈ lebesgueDiffusion.generator.domain,
      lebesgueDiffusion.generator ⟨h0.toLp u, h⟩ = h2.toLp (deriv (deriv u)) :=
  domain_of_approx _ (a_mem hu) (cutoff_graph hu h0 h1 h2).1 (cutoff_graph hu h0 h1 h2).2

/-! ### F10: `C_c^∞` is a core -/

lemma inner_cls_cls (f g : ℝ → ℝ) (hf : f ∈ A₀) (hg : g ∈ A₀) :
    inner ℝ (lebesgueDiffusion.cls ⟨f, hf⟩) (lebesgueDiffusion.cls ⟨g, hg⟩) = ∫ x, f x * g x := by
  rw [L2_inner_eq]
  refine integral_congr_ae ?_
  filter_upwards [lebesgueDiffusion.coeFn_cls ⟨f, hf⟩, lebesgueDiffusion.coeFn_cls ⟨g, hg⟩] with x h1 h2
  rw [h1, h2]

theorem orth_of_ode (w : Lp ℝ 2 (volume : Measure ℝ))
    (hw : ∀ a : lebesgueDiffusion.A₀, inner ℝ (lebesgueDiffusion.cls a - lebesgueDiffusion.Lcls a) w = 0) : w = 0 := by
  refine lebesgueDiffusion.eq_zero_of_orth w (fun g => ?_)
  rw [real_inner_comm]
  obtain ⟨v, hv, h0, h1, h2, hvψ⟩ := exists_resolvent_solution (ψ := g.1) g.2
  obtain ⟨c1, c2⟩ := cutoff_graph hv h0 h1 h2
  have hlim : Tendsto (fun n : ℕ => inner ℝ (lebesgueDiffusion.cls ⟨chiR (Rn n) * v, a_mem hv n⟩ -
      lebesgueDiffusion.Lcls ⟨chiR (Rn n) * v, a_mem hv n⟩) w) atTop
      (𝓝 (inner ℝ (h0.toLp v - h2.toLp (deriv (deriv v))) w)) :=
    (c1.sub c2).inner tendsto_const_nhds
  have hz : (fun n : ℕ => inner ℝ (lebesgueDiffusion.cls ⟨chiR (Rn n) * v, a_mem hv n⟩ -
      lebesgueDiffusion.Lcls ⟨chiR (Rn n) * v, a_mem hv n⟩) w) = fun _ => 0 :=
    funext fun n => hw ⟨chiR (Rn n) * v, a_mem hv n⟩
  rw [hz] at hlim
  have e : h0.toLp v - h2.toLp (deriv (deriv v)) = lebesgueDiffusion.cls g := by
    have hd : MemLp (fun x => v x - deriv (deriv v) x) 2 volume := h0.sub h2
    have h3 : h0.toLp v - h2.toLp (deriv (deriv v)) = hd.toLp (fun x => v x - deriv (deriv v) x) := by
      rw [← MemLp.toLp_sub]; rfl
    rw [h3]
    refine Lp.ext ?_
    filter_upwards [hd.coeFn_toLp, lebesgueDiffusion.coeFn_cls g] with x h4 h5
    rw [h4, h5]; exact hvψ x
  rw [e] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds

/-- **F10 (ESA)**: `𝒜₀` is a core for the Friedrichs generator. -/
theorem esa_lebesgue (u : Lp ℝ 2 (volume : Measure ℝ)) (hu : u ∈ lebesgueDiffusion.generator.domain) :
    ∃ a : ℕ → lebesgueDiffusion.A₀, Tendsto (fun n => lebesgueDiffusion.cls (a n)) atTop (𝓝 u) ∧
      Tendsto (fun n => lebesgueDiffusion.Lcls (a n)) atTop (𝓝 (lebesgueDiffusion.generator ⟨u, hu⟩)) := by
  set S := DiffusionTriple.formData lebesgueDiffusion with hS
  let M : Submodule ℝ (Lp ℝ 2 (volume : Measure ℝ)) := LinearMap.range (DiffusionTriple.clsₗ lebesgueDiffusion - DiffusionTriple.Lclsₗ lebesgueDiffusion)
  have hM : M.topologicalClosure = ⊤ := by
    rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
    intro w hw
    rw [Submodule.mem_orthogonal] at hw
    exact orth_of_ode w (fun a => hw _ ⟨a, rfl⟩)
  have hdense : Dense (M : Set (Lp ℝ 2 (volume : Measure ℝ))) :=
    Submodule.dense_iff_topologicalClosure_eq_top.2 hM
  set g : Lp ℝ 2 (volume : Measure ℝ) := u - S.generator ⟨u, hu⟩ with hg
  obtain ⟨m, hmM, hmg⟩ := mem_closure_iff_seq_limit.1 (hdense.closure_eq ▸ Set.mem_univ g)
  have hm : ∀ n, ∃ a : lebesgueDiffusion.A₀, lebesgueDiffusion.cls a - lebesgueDiffusion.Lcls a = m n := by
    intro n
    obtain ⟨a, ha⟩ := hmM n
    exact ⟨a, ha⟩
  choose a ha using hm
  have hRu : S.R g = u := (S.generator_apply_eq_iff hu _).1 rfl
  have h1 : Tendsto (fun n => lebesgueDiffusion.cls (a n)) atTop (𝓝 u) := by
    have : Tendsto (fun n => S.R (m n)) atTop (𝓝 (S.R g)) := (S.R.continuous.tendsto g).comp hmg
    rw [hRu] at this
    refine this.congr (fun n => ?_)
    rw [← ha n]; exact DiffusionTriple.R_cls_sub lebesgueDiffusion (a n)
  refine ⟨a, h1, ?_⟩
  have h2 : Tendsto (fun n => lebesgueDiffusion.cls (a n) - m n) atTop (𝓝 (u - g)) := h1.sub hmg
  have e : u - g = S.generator ⟨u, hu⟩ := by rw [hg]; abel
  rw [e] at h2
  refine h2.congr (fun n => ?_)
  rw [← ha n]; abel

end MarkovTriple.BGL.Lebesgue
