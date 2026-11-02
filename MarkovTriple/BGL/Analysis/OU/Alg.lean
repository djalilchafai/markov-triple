import MarkovTriple.BGL.Analysis.OU.Gauss

/-! # OU (Part 3): the algebras `𝒜₀ = C_c^∞`, `𝒜 = C^∞`, Gamma2 identity (the legacy `MarkovTriple` structure was removed) -/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal Real

namespace MarkovTriple.Sanity.OU

/-- `C_c^∞(ℝ)` as a non-unital subalgebra of `ℝ → ℝ`. -/
def A₀ : NonUnitalSubalgebra ℝ (ℝ → ℝ) where
  carrier := {f | Sm f ∧ HasCompactSupport f}
  add_mem' := fun {f g} (hf : Sm f ∧ HasCompactSupport f) (hg : Sm g ∧ HasCompactSupport g) =>
    ⟨hf.1.add hg.1, hf.2.add hg.2⟩
  zero_mem' := (⟨contDiff_const, HasCompactSupport.zero⟩ : Sm (0 : ℝ → ℝ) ∧ HasCompactSupport (0 : ℝ → ℝ))
  mul_mem' := fun {f g} (hf : Sm f ∧ HasCompactSupport f) (hg : Sm g ∧ HasCompactSupport g) =>
    ⟨hf.1.mul hg.1, hf.2.mul_right⟩
  smul_mem' := fun c {f} (hf : Sm f ∧ HasCompactSupport f) => ⟨hf.1.const_smul c, hf.2.smul_left⟩

/-- `C^∞(ℝ)` as a unital subalgebra. -/
def Afull : Subalgebra ℝ (ℝ → ℝ) where
  carrier := {f | Sm f}
  add_mem' := fun {f g} (hf : Sm f) (hg : Sm g) => hf.add hg
  zero_mem' := (contDiff_const : Sm (0 : ℝ → ℝ))
  mul_mem' := fun {f g} (hf : Sm f) (hg : Sm g) => hf.mul hg
  one_mem' := (contDiff_const : Sm (1 : ℝ → ℝ))
  algebraMap_mem' := fun r => (contDiff_const : Sm (fun _ : ℝ => r))

lemma mem_A₀ {f : ℝ → ℝ} : f ∈ A₀ ↔ Sm f ∧ HasCompactSupport f := Iff.rfl
lemma mem_Afull {f : ℝ → ℝ} : f ∈ Afull ↔ Sm f := Iff.rfl

lemma A₀.sm {f : ℝ → ℝ} (hf : f ∈ A₀) : Sm f := hf.1
lemma A₀.cs {f : ℝ → ℝ} (hf : f ∈ A₀) : HasCompactSupport f := hf.2

lemma A₀.deriv_mem {f : ℝ → ℝ} (hf : f ∈ A₀) : deriv f ∈ A₀ := ⟨hf.1.deriv', hf.2.deriv⟩

lemma A₀.Lo_mem {f : ℝ → ℝ} (hf : f ∈ A₀) : Lo f ∈ A₀ := by
  have h1 := A₀.deriv_mem (A₀.deriv_mem hf)
  have h2 : (fun x : ℝ => x * deriv f x) ∈ A₀ :=
    ⟨sm_id.mul hf.1.deriv', (A₀.deriv_mem hf).2.mul_left⟩
  exact sub_mem h1 h2

lemma A₀.Go_mem {f g : ℝ → ℝ} (hf : f ∈ A₀) (hg : g ∈ A₀) : Go f g ∈ A₀ :=
  mul_mem (A₀.deriv_mem hf) (A₀.deriv_mem hg)

lemma A₀.le {f : ℝ → ℝ} (hf : f ∈ A₀) : f ∈ Afull := hf.1

lemma integrable_cs {f : ℝ → ℝ} (hf : f ∈ A₀) : Integrable f γ :=
  hf.1.continuous.integrable_of_hasCompactSupport hf.2

lemma memLp_A₀ {f : ℝ → ℝ} (hf : f ∈ A₀) (p : ℝ≥0∞) : MemLp f p γ :=
  hf.1.continuous.memLp_of_hasCompactSupport hf.2

/-- IBP, test function (compact support) in the first slot. -/
lemma ibp_cs_left {f g : ℝ → ℝ} (hf : Sm f) (hg : g ∈ A₀) :
    ∫ x, g x * Lo f x ∂γ = -∫ x, deriv g x * deriv f x ∂γ := by
  have hg' := A₀.deriv_mem hg
  refine ibp_master hf hg.1 ?_ ?_ ?_
  · exact (hg.1.continuous.mul (sm_Lo hf).continuous).integrable_of_hasCompactSupport hg.2.mul_right
  · exact (hg'.1.continuous.mul hf.deriv'.continuous).integrable_of_hasCompactSupport hg'.2.mul_right
  · exact (hg.1.continuous.mul hf.deriv'.continuous).integrable_of_hasCompactSupport hg.2.mul_right

/-- IBP, test function (compact support) in the `L` slot. -/
lemma ibp_cs_right {f g : ℝ → ℝ} (hf : Sm f) (hg : g ∈ A₀) :
    ∫ x, f x * Lo g x ∂γ = -∫ x, deriv f x * deriv g x ∂γ := by
  have hg' := A₀.deriv_mem hg
  have hL := A₀.Lo_mem hg
  refine ibp_master hg.1 hf ?_ ?_ ?_
  · exact (hf.continuous.mul (sm_Lo hg.1).continuous).integrable_of_hasCompactSupport hL.2.mul_left
  · exact (hf.deriv'.continuous.mul hg'.1.continuous).integrable_of_hasCompactSupport hg'.2.mul_left
  · exact (hf.continuous.mul hg'.1.continuous).integrable_of_hasCompactSupport hg'.2.mul_left

lemma integrable_Γ_cs {f g : ℝ → ℝ} (hf : Sm f) (hg : g ∈ A₀) : Integrable (Go f g) γ :=
  (hf.deriv'.continuous.mul (A₀.deriv_mem hg).1.continuous).integrable_of_hasCompactSupport
    (A₀.deriv_mem hg).2.mul_left

lemma comp_mem_A₀ (k : ℕ) (ψ : (Fin k → ℝ) → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (h0 : ψ 0 = 0)
    (f : Fin k → ℝ → ℝ) (hf : ∀ i, f i ∈ A₀) : (fun x => ψ (fun i => f i x)) ∈ A₀ := by
  refine ⟨sm_comp k ψ hψ f fun i => (hf i).1, ?_⟩
  refine HasCompactSupport.intro (K := ⋃ i, tsupport (f i))
    (isCompact_iUnion fun i => (hf i).2) fun x hx => ?_
  have : ∀ i, f i x = 0 := fun i =>
    image_eq_zero_of_notMem_tsupport (fun h => hx (Set.mem_iUnion.2 ⟨i, h⟩))
  have e : (fun i => f i x) = 0 := funext this
  simp only [e, h0]

lemma dense_Lp (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    Dense {u : Lp ℝ p γ | ∃ f ∈ A₀, (u : ℝ → ℝ) =ᵐ[γ] f} := by
  refine (Lp.dense_hasCompactSupport_contDiff (F := ℝ) (μ := γ) hp).mono ?_
  rintro u ⟨g, hug, hcs, hcd⟩
  exact ⟨g, ⟨hcd, hcs⟩, hug⟩

/-! ### Curvature -/

theorem ou_Gamma2 {f : ℝ → ℝ} (hf : Sm f) (x : ℝ) :
    (Lo (Go f f) x - 2 * Go f (Lo f) x) / 2 = deriv (deriv f) x ^ 2 + deriv f x ^ 2 := by
  have hdd : ∀ y, HasDerivAt (deriv f) (deriv (deriv f) y) y := fun y => hf.deriv'.hasDerivAt y
  have hddd : ∀ y, HasDerivAt (deriv (deriv f)) (deriv (deriv (deriv f)) y) y :=
    fun y => hf.deriv'.deriv'.hasDerivAt y
  have hF : ∀ y, HasDerivAt (Go f f)
      (deriv (deriv f) y * deriv f y + deriv f y * deriv (deriv f) y) y := fun y =>
    (hdd y).mul (hdd y)
  have h1 : deriv (Go f f) = fun y =>
      deriv (deriv f) y * deriv f y + deriv f y * deriv (deriv f) y :=
    funext fun y => (hF y).deriv
  have hF2 : HasDerivAt (deriv (Go f f))
      (deriv (deriv (deriv f)) x * deriv f x + deriv (deriv f) x * deriv (deriv f) x +
        (deriv (deriv f) x * deriv (deriv f) x + deriv f x * deriv (deriv (deriv f)) x)) x := by
    rw [h1]
    exact ((hddd x).mul (hdd x)).add ((hdd x).mul (hddd x))
  have hL : HasDerivAt (Lo f)
      (deriv (deriv (deriv f)) x - (deriv f x + x * deriv (deriv f) x)) x := by
    unfold Lo
    exact (hddd x).sub ((hasDerivAt_id x).mul (hdd x) |>.congr_deriv (by simp))
  have e1 : Lo (Go f f) x = deriv (deriv (Go f f)) x - x * deriv (Go f f) x := rfl
  have e2 : Go f (Lo f) x = deriv f x * deriv (Lo f) x := rfl
  rw [e1, e2, hF2.deriv, hL.deriv, h1]
  ring

end MarkovTriple.Sanity.OU
