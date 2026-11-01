import Mathlib
import MarkovTriple.Frozen.Poincare
import MarkovTriple.Frozen.Ergodic
import MarkovTriple.Frozen.CD
import MarkovTriple.Frozen.CDFull
import MarkovTriple.Hilbert.Closure
import MarkovTriple.Hilbert.FullBridge
import MarkovTriple.Hilbert.TripleForm

/-!
# Integrated `Γ₂` identities and the fixed space of the resolvent (finite measure)

For a full Markov triple `F` with `μ` finite (`1 ∈ L²`):

* `∫ L h dμ = 0` for `h ∈ 𝒜₀` (`ibp_A_symm` with `f = 1 ∈ 𝒜`, `Γ(1,h) = 0`);
* `∫ Γ₂(g) dμ = ∫ (L g)² dμ` for `g ∈ 𝒜₀`;
* `CD(ρ,n)` gives `ρ ∫Γ(g) ≤ ∫ (L g)²`;
* under `ErgodicL2`, the fixed space `{n | R n = n}` of the Friedrichs resolvent consists of the
  constants.
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal InnerProductSpace

namespace MarkovTriple.Hilbert

variable {E : Type*} [MeasurableSpace E]

lemma _root_.FullMarkovTriple.Γ_one_left (F : FullMarkovTriple E) {g : E → ℝ} (hg : g ∈ F.A) :
    F.Γ (1 : E → ℝ) g = 0 := by
  have h := (F.diffusion_A 0 (fun _ => (1 : ℝ)) contDiff_const (fun i => Fin.elim0 i)
    (fun i => Fin.elim0 i)).1 g hg
  show F.Γ (fun _ => (1 : ℝ)) g = fun _ => 0
  rw [h]
  funext x
  simp

/-- `∫ L h = 0` for `h ∈ 𝒜₀`, finite measure. -/
lemma _root_.FullMarkovTriple.integral_L (F : FullMarkovTriple E) [IsFiniteMeasure F.μ]
    {h : E → ℝ} (hh : h ∈ F.A₀) : ∫ x, F.L h x ∂F.μ = 0 := by
  have h1 : MemLp (1 : E → ℝ) 2 F.μ := memLp_const 1
  have hL : MemLp (F.L (1 : E → ℝ)) 2 F.μ := by rw [F.L_one]; exact MemLp.zero
  have := F.ibp_A_symm 1 F.A.one_mem h1 hL h hh
  have e : ∫ x, F.Γ (1 : E → ℝ) h x ∂F.μ = 0 := by
    rw [F.Γ_one_left (F.A₀_le h hh)]; simp
  simpa [e] using this

/-- `∫ Γ₂ g = ∫ (L g)²` for `g ∈ 𝒜₀`. -/
lemma _root_.FullMarkovTriple.integral_Γ₂ (F : FullMarkovTriple E) [IsFiniteMeasure F.μ]
    {g : E → ℝ} (hg : g ∈ F.A₀) :
    ∫ x, F.toMarkovTriple.Γ₂ g x ∂F.μ = ∫ x, F.L g x * F.L g x ∂F.μ := by
  set T := F.toMarkovTriple
  have hΓ : T.Γ g g ∈ T.A₀ := T.Γ_mem g hg g hg
  have hLg : T.L g ∈ T.A₀ := T.L_mem g hg
  have i1 : Integrable (T.L (T.Γ g g)) T.μ := integrable_of_mem T (T.L_mem _ hΓ)
  have i2 : Integrable (T.Γ g (T.L g)) T.μ := integrable_of_mem T (T.Γ_mem g hg _ hLg)
  have hint : T.Γ₂ g = fun x => (1 / 2 : ℝ) * (T.L (T.Γ g g) x - 2 * T.Γ g (T.L g) x) := by
    funext x; simp only [MarkovTriple.Γ₂]; ring
  rw [hint, integral_const_mul, integral_sub i1 (i2.const_mul 2), integral_const_mul,
    F.integral_L hΓ, T.ibp g hg (T.L g) hLg]
  ring

/-- `CD ρ n` integrated, with the dimensional term:
`ρ ∫ Γ g + (1/n) ∫ (L g)² ≤ ∫ (L g)²`. -/
lemma _root_.FullMarkovTriple.rho_integral_le_dim (F : FullMarkovTriple E) [IsFiniteMeasure F.μ]
    {ρ : ℝ} {n : ℝ≥0∞} (hCD : F.toMarkovTriple.CD ρ n) {g : E → ℝ} (hg : g ∈ F.A₀) :
    ρ * ∫ x, F.Γ g g x ∂F.μ + (n⁻¹).toReal * ∫ x, F.L g x * F.L g x ∂F.μ ≤
      ∫ x, F.L g x * F.L g x ∂F.μ := by
  set T := F.toMarkovTriple
  have hΓ : T.Γ g g ∈ T.A₀ := T.Γ_mem g hg g hg
  have hLg : T.L g ∈ T.A₀ := T.L_mem g hg
  have i1 : Integrable (T.Γ g g) T.μ := integrable_of_mem T hΓ
  have i4 : Integrable (fun x => T.L g x * T.L g x) T.μ :=
    integrable_of_mem T (T.A₀.mul_mem hLg hLg)
  have i3 : Integrable (T.Γ₂ g) T.μ := by
    have i1' : Integrable (T.L (T.Γ g g)) T.μ := integrable_of_mem T (T.L_mem _ hΓ)
    have i2 : Integrable (T.Γ g (T.L g)) T.μ := integrable_of_mem T (T.Γ_mem g hg _ hLg)
    have : T.Γ₂ g = fun x => (1 / 2 : ℝ) * (T.L (T.Γ g g) x - 2 * T.Γ g (T.L g) x) := by
      funext x; simp only [MarkovTriple.Γ₂]; ring
    rw [this]; exact (i1'.sub (i2.const_mul 2)).const_mul _
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (i1.const_mul ρ) (i4.const_mul _),
    ← F.integral_Γ₂ hg]
  refine integral_mono_ae ((i1.const_mul ρ).add (i4.const_mul _)) i3 ?_
  filter_upwards [hCD.2 g hg] with x hx
  show ρ * T.Γ g g x + (n⁻¹).toReal * (T.L g x * T.L g x) ≤ T.Γ₂ g x
  nlinarith [hx]

/-- `CD ρ n` integrated: `ρ ∫ Γ g ≤ ∫ (L g)²`. -/
lemma _root_.FullMarkovTriple.rho_integral_le (F : FullMarkovTriple E) [IsFiniteMeasure F.μ]
    {ρ : ℝ} {n : ℝ≥0∞} (hCD : F.toMarkovTriple.CD ρ n) {g : E → ℝ} (hg : g ∈ F.A₀) :
    ρ * ∫ x, F.Γ g g x ∂F.μ ≤ ∫ x, F.L g x * F.L g x ∂F.μ := by
  have h := F.rho_integral_le_dim hCD hg
  have : 0 ≤ (n⁻¹).toReal * ∫ x, F.L g x * F.L g x ∂F.μ :=
    mul_nonneg ENNReal.toReal_nonneg (integral_nonneg fun x => mul_self_nonneg _)
  linarith

/-- Under `ErgodicL2`, the fixed space of the Friedrichs resolvent is made of constants. -/
theorem fixed_const (F : FullMarkovTriple E) (herg : F.toMarkovTriple.ErgodicL2)
    (n : Lp ℝ 2 F.μ) (hn : (formData F.toMarkovTriple).R n = n) :
    ∃ c : ℝ, (n : E → ℝ) =ᵐ[F.μ] fun _ => c := by
  let T := F.toMarkovTriple
  let S := formData T
  have hdom : n ∈ S.generator.domain := (S.mem_domain_generator_iff n).2 ⟨0, by simpa using hn⟩
  have hG : S.generator ⟨n, hdom⟩ = 0 := (S.generator_apply_eq_iff hdom 0).2 (by simpa using hn)
  have hmem := S.generator.mem_graph ⟨n, hdom⟩
  rw [hG] at hmem
  have hmem2 : ((n, (0 : Lp ℝ 2 F.μ)) : Lp ℝ 2 F.μ × Lp ℝ 2 F.μ) ∈
      (S.graphA.topologicalClosure : Set _) := by
    have := hmem
    rw [FullMarkovTriple.generator_graph_eq_closure F] at this
    exact this
  rw [Submodule.topologicalClosure_coe] at hmem2
  obtain ⟨p, hp, hplim⟩ := mem_closure_iff_seq_limit.1 hmem2
  have hex : ∀ k, ∃ f : T.A₀, (toLp0 T f, Lt0 T f) = p k := by
    intro k
    obtain ⟨d, hd⟩ := hp k
    obtain ⟨d', f, hf⟩ := d
    refine ⟨f, ?_⟩
    have e1 : (S.D.subtype.prod (-S.A)) ⟨d', f, hf⟩ = p k := hd
    rw [← e1]
    have e2 : S.A ⟨d', f, hf⟩ = -Lt0 T f := by
      subst hf
      exact formA_apply T f
    refine Prod.ext ?_ ?_
    · exact hf
    · show Lt0 T f = -S.A ⟨d', f, hf⟩
      rw [e2]; simp
  choose f hf using hex
  have h1 : Tendsto (fun k => toLp0 T (f k)) atTop (𝓝 n) := by
    have := (continuous_fst.tendsto _).comp hplim
    refine this.congr (fun k => ?_)
    simp [← hf k]
  have h2 : Tendsto (fun k => Lt0 T (f k)) atTop (𝓝 0) := by
    have := (continuous_snd.tendsto _).comp hplim
    refine this.congr (fun k => ?_)
    simp [← hf k]
  have key : ∀ (v : ℕ → Lp ℝ 2 F.μ) (a : Lp ℝ 2 F.μ), Tendsto v atTop (𝓝 a) →
      Tendsto (fun k => eLpNorm ((v k : E → ℝ) - (a : E → ℝ)) 2 F.μ) atTop (𝓝 0) := by
    intro v a hv
    have h0 : Tendsto (fun k => v k - a) atTop (𝓝 0) := by
      simpa using hv.sub_const a
    have h3 := (continuous_enorm.tendsto (0 : Lp ℝ 2 F.μ)).comp h0
    simp only [enorm_zero] at h3
    refine h3.congr (fun k => ?_)
    simp only [Function.comp_apply]
    rw [Lp.enorm_def]
    exact eLpNorm_congr_ae (Lp.coeFn_sub _ _)
  refine herg n ⟨fun k => (f k).1, fun k => (f k).2, ?_, ?_⟩
  · refine (key _ n h1).congr (fun k => ?_)
    exact eLpNorm_congr_ae ((coeFn_toLp0 T (f k)).sub (Filter.EventuallyEq.refl _ _))
  · have := key _ 0 h2
    refine this.congr (fun k => ?_)
    refine eLpNorm_congr_ae ?_
    filter_upwards [coeFn_Lt0 T (f k), Lp.coeFn_zero ℝ 2 F.μ] with x e1 e2
    simp only [Pi.sub_apply, e1, e2, Pi.zero_apply, sub_zero]
    rfl

end MarkovTriple.Hilbert
