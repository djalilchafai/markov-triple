import Mathlib
import MarkovTriple.BGL.Instances.OUCompact.Mehler
import MarkovTriple.BGL.Instances.OU.Diffusion

/-!
# The Ornstein–Uhlenbeck triple with `𝒜₀ = ℬ` as a BGL `DiffusionTriple` (D1–D8)

`E = ℝ`, `μ = γ = N(0,1)`, `𝒜₀ = ℬ = {f ∈ C^∞ bounded, f' ∈ 𝒮}` (`OUCompact.Bm`), `L f = f'' − x f'`,
`Γ(f,g) = f'g'`.  Since `1 ∈ ℬ` the exhaustion sequence is constant.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal Real SchwartzMap
open MarkovTriple.Sanity.OU hiding A₀

local notation "OA₀" => MarkovTriple.Sanity.OU.A₀

namespace MarkovTriple.BGL.Instances.OUCompact

/-- `ℬ` as a non-unital subalgebra. -/
def Bsub : NonUnitalSubalgebra ℝ (ℝ → ℝ) where
  carrier := {f | Bm f}
  add_mem' := fun {_f _g} hf hg => Bm.add hf hg
  zero_mem' := bm_const 0
  mul_mem' := fun {_f _g} hf hg => Bm.mul hf hg
  smul_mem' := fun c {_f} hf => Bm.smul c hf

lemma mem_Bsub {f : ℝ → ℝ} : f ∈ Bsub ↔ Bm f := Iff.rfl

/-- `ℬ` as a unital subalgebra (it contains the constants). -/
def Bfull : Subalgebra ℝ (ℝ → ℝ) where
  carrier := {f | Bm f}
  add_mem' := fun {_f _g} hf hg => Bm.add hf hg
  zero_mem' := bm_const 0
  mul_mem' := fun {_f _g} hf hg => Bm.mul hf hg
  one_mem' := bm_const 1
  algebraMap_mem' := fun r => bm_const r

lemma mem_Bfull {f : ℝ → ℝ} : f ∈ Bfull ↔ Bm f := Iff.rfl

lemma Bm.integrable {f : ℝ → ℝ} (hf : Bm f) : Integrable f γ := by
  obtain ⟨C, hC⟩ := hf.bdd
  exact Integrable.of_bound (C := C) hf.sm.continuous.aestronglyMeasurable
    (ae_of_all _ fun x => by simpa using hC x)

lemma Bm.deriv_bm {f : ℝ → ℝ} (hf : Bm f) : Bm (deriv f) := by
  obtain ⟨W, hW⟩ := hf.deriv_schwartz
  rw [← hW]; exact bm_schwartz W

lemma Bm.memLp {f : ℝ → ℝ} (hf : Bm f) (p : ℝ≥0∞) : MemLp f p γ := by
  obtain ⟨C, hC⟩ := hf.bdd
  exact (MemLp.of_bound (p := ∞) hf.sm.continuous.aestronglyMeasurable C
    (ae_of_all _ fun x => by simpa using hC x)).mono_exponent le_top

/-- Gaussian integration by parts on `ℬ`: `∫ g · L f dγ = −∫ g' f' dγ`. -/
theorem ibp_bm {f g : ℝ → ℝ} (hf : Bm f) (hg : Bm g) :
    ∫ x, g x * Lo f x ∂γ = -∫ x, deriv g x * deriv f x ∂γ :=
  ibp_master hf.sm hg.sm (hg.mul (bm_Lo hf)).integrable (bm_Go hg hf).integrable
    (hg.mul hf.deriv_bm).integrable

lemma integral_Lo_zero_bm {f : ℝ → ℝ} (hf : Bm f) : ∫ x, Lo f x ∂γ = 0 := by
  have := ibp_bm hf (bm_const 1)
  simpa using this

lemma Go_integral_comm' (f g : ℝ → ℝ) : ∫ x, deriv g x * deriv f x ∂γ = ∫ x, Go f g x ∂γ :=
  integral_congr_ae (ae_of_all _ fun x => by simp [Go, mul_comm])

/-- `γ` charges every nonempty open set (needed nowhere here; kept for symmetry with `OU`). -/
noncomputable def ouB : DiffusionTriple ℝ where
  μ := γ
  sigmaFinite := inferInstance
  finite_prob := fun _ => inferInstance
  A₀ := Bsub
  measurable := fun f hf => hf.sm.continuous.measurable
  bounded := fun f hf => hf.bdd
  memLp := fun f hf p _ _ => Bm.memLp hf p
  dense := fun p hp hp' => by
    have := hp
    refine (MarkovTriple.Sanity.OU.dense_Lp p hp').mono ?_
    rintro u ⟨f, hf, hu⟩
    exact ⟨f, bm_of_cs hf.1 hf.2, hu⟩
  comp_mem := fun k ψ hψ _ f hf => Bm.comp k ψ hψ f hf
  exhaustion := ⟨fun _ => fun _ => 1, fun _ => bm_const 1,
    fun _ => Eventually.of_forall fun _ => le_rfl,
    Eventually.of_forall fun _ => tendsto_const_nhds⟩
  Γ := Go
  L := Lo
  Γ_mem := fun f hf g hg => bm_Go hf hg
  L_mem := fun f hf => bm_Lo hf
  Γ_symm := fun f _ g _ => Eventually.of_forall fun x => by simp [Go, mul_comm]
  Γ_add := fun f hf f' hf' g _ => Eventually.of_forall fun x => by
    simp [Go, deriv_add_s hf.1 hf'.1, add_mul]
  Γ_smul := fun c f hf g _ => Eventually.of_forall fun x => by
    simp [Go, deriv_smul_s c hf.1, mul_assoc]
  Γ_nonneg := fun f _ => Eventually.of_forall fun x => by
    simpa [Go] using mul_self_nonneg (deriv f x)
  diffusion := fun k ψ hψ _ f hf g hg => Eventually.of_forall fun x =>
    congrFun ((diffusion_s k ψ hψ f (fun i => (hf i).1)).1 g hg.1) x
  ibp := fun f hf g hg => by
    have := ibp_bm hf hg
    rw [this, Go_integral_comm']
  integral_L := fun f hf => integral_Lo_zero_bm hf

/-- On smooth functions the formula-defined `ΓA` of the triple is `f' g'`. -/
lemma ouB_ΓA {f g : ℝ → ℝ} (hf : Sm f) (hg : Sm g) : ouB.ΓA f g = Go f g := by
  funext x
  have e : ouB.ΓA f g x = (Lo (f * g) x - f x * Lo g x - g x * Lo f x) / 2 := rfl
  rw [e, Lo_mul hf hg x]; simp only [Go]; ring

instance : IsProbabilityMeasure ouB.μ := (inferInstance : IsProbabilityMeasure γ)

end MarkovTriple.BGL.Instances.OUCompact
