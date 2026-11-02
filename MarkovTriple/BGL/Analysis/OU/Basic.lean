import Mathlib
import MarkovTriple.BGL.Frozen.PartialDeriv

/-!
# Ornstein–Uhlenbeck on `(ℝ, γ)`: basic calculus (Part 1)

`γ = gaussianReal 0 1`, `L f = f'' − x f'`, `Γ(f,g) = f' g'`; `𝒜₀ = C_c^∞(ℝ)`, `𝒜 = C^∞(ℝ)`.
This file: calculus on smooth functions, Gaussian density, the Gaussian integration by parts
(`ibp_master`), and the algebras.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace MarkovTriple.Sanity.OU

/-- smooth functions -/
abbrev Sm (f : ℝ → ℝ) : Prop := ContDiff ℝ (⊤ : ℕ∞) f

/-- the Gaussian measure `γ = N(0,1)` -/
noncomputable abbrev γ : Measure ℝ := gaussianReal 0 1

/-- the Gaussian density -/
noncomputable abbrev φ : ℝ → ℝ := gaussianPDFReal 0 1

/-- generator `L f = f'' − x f'` -/
noncomputable def Lo (f : ℝ → ℝ) : ℝ → ℝ := fun x => deriv (deriv f) x - x * deriv f x

/-- carré du champ `Γ(f,g) = f' g'` -/
noncomputable def Go (f g : ℝ → ℝ) : ℝ → ℝ := fun x => deriv f x * deriv g x

/-! ### Smooth calculus -/
section Calc
variable {f g : ℝ → ℝ}

lemma Sm.deriv' (hf : Sm f) : Sm (deriv f) := (contDiff_infty_iff_deriv.1 hf).2

lemma Sm.hasDerivAt (hf : Sm f) (x : ℝ) : HasDerivAt f (deriv f x) x :=
  ((hf.differentiable (by simp)) x).hasDerivAt

lemma deriv_mul_s (hf : Sm f) (hg : Sm g) : deriv (f * g) = deriv f * g + f * deriv g := by
  funext x
  have := ((hf.hasDerivAt x).mul (hg.hasDerivAt x)).deriv
  simpa [add_comm] using this

lemma deriv_add_s (hf : Sm f) (hg : Sm g) : deriv (f + g) = deriv f + deriv g := by
  funext x
  exact ((hf.hasDerivAt x).add (hg.hasDerivAt x)).deriv

lemma deriv_smul_s (c : ℝ) (hf : Sm f) : deriv (c • f) = c • deriv f := by
  funext x
  exact ((hf.hasDerivAt x).const_smul c).deriv

lemma sm_id : Sm (fun x : ℝ => x) := contDiff_id

lemma Lo_mul (hf : Sm f) (hg : Sm g) (x : ℝ) :
    Lo (f * g) x = Lo f x * g x + 2 * (deriv f x * deriv g x) + f x * Lo g x := by
  unfold Lo
  rw [deriv_mul_s hf hg, deriv_add_s (show Sm (deriv f * g) from hf.deriv'.mul hg)
    (show Sm (f * deriv g) from hf.mul hg.deriv'),
    deriv_mul_s hf.deriv' hg, deriv_mul_s hf hg.deriv']
  simp only [Pi.add_apply, Pi.mul_apply]
  ring

lemma Lo_add (hf : Sm f) (hg : Sm g) : Lo (f + g) = Lo f + Lo g := by
  funext x
  unfold Lo
  rw [deriv_add_s hf hg, deriv_add_s hf.deriv' hg.deriv']
  simp only [Pi.add_apply]; ring

lemma Lo_smul (c : ℝ) (hf : Sm f) : Lo (c • f) = c • Lo f := by
  funext x
  unfold Lo
  rw [deriv_smul_s c hf, deriv_smul_s c hf.deriv']
  simp only [Pi.smul_apply, smul_eq_mul]; ring

lemma sm_Lo (hf : Sm f) : Sm (Lo f) := by
  unfold Lo
  exact hf.deriv'.deriv'.sub (sm_id.mul hf.deriv')

lemma sm_Go (hf : Sm f) (hg : Sm g) : Sm (Go f g) := hf.deriv'.mul hg.deriv'

lemma clm_pi_apply {k : ℕ} (Λ : (Fin k → ℝ) →L[ℝ] ℝ) (v : Fin k → ℝ) :
    Λ v = ∑ i, v i * Λ (Pi.single i 1) := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (Pi.single i (v i) : Fin k → ℝ) = v i • (Pi.single i (1 : ℝ) : Fin k → ℝ) := by
    ext j; by_cases h : j = i <;> simp [h]
  rw [this, map_smul, smul_eq_mul]

lemma hasDerivAt_comp1 {k : ℕ} (ψ : (Fin k → ℝ) → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (γ : Fin k → ℝ → ℝ) (d : Fin k → ℝ) (t : ℝ) (hγ : ∀ i, HasDerivAt (γ i) (d i) t) :
    HasDerivAt (fun u : ℝ => ψ (fun i => γ i u))
      (∑ i, MarkovTriple.BGL.pderiv ψ i (fun j => γ j t) * d i) t := by
  have hγ' : HasDerivAt (fun u : ℝ => fun i => γ i u) d t := hasDerivAt_pi.2 hγ
  have hψd : HasFDerivAt ψ (fderiv ℝ ψ (fun i => γ i t)) (fun i => γ i t) :=
    ((hψ.differentiable (by simp)) _).hasFDerivAt
  have := hψd.comp_hasDerivAt t hγ'
  refine this.congr_deriv ?_
  rw [clm_pi_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold MarkovTriple.BGL.pderiv; ring

lemma contDiff_pderiv {k : ℕ} (ψ : (Fin k → ℝ) → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (i : Fin k) :
    ContDiff ℝ (⊤ : ℕ∞) (MarkovTriple.BGL.pderiv ψ i) := by
  unfold MarkovTriple.BGL.pderiv
  exact (hψ.fderiv_right (by simp)).clm_apply contDiff_const

lemma deriv_comp1 {k : ℕ} (ψ : (Fin k → ℝ) → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (f : Fin k → ℝ → ℝ) (hf : ∀ i, Sm (f i)) :
    deriv (fun x => ψ (fun i => f i x)) =
      fun y => ∑ i, MarkovTriple.BGL.pderiv ψ i (fun j => f j y) * deriv (f i) y := by
  funext y
  exact (hasDerivAt_comp1 ψ hψ f (fun i => deriv (f i) y) y (fun i => (hf i).hasDerivAt y)).deriv

lemma sm_comp (k : ℕ) (ψ : (Fin k → ℝ) → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (f : Fin k → ℝ → ℝ) (hf : ∀ i, Sm (f i)) : Sm (fun x => ψ (fun i => f i x)) :=
  hψ.comp (contDiff_pi.2 hf)

lemma diffusion_s (k : ℕ) (ψ : (Fin k → ℝ) → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (f : Fin k → ℝ → ℝ) (hf : ∀ i, Sm (f i)) :
    (∀ g, Sm g → Go (fun x => ψ (fun i => f i x)) g =
        fun x => ∑ i, MarkovTriple.BGL.pderiv ψ i (fun j => f j x) * Go (f i) g x) ∧
      Lo (fun x => ψ (fun i => f i x)) =
        fun x => ∑ i, MarkovTriple.BGL.pderiv ψ i (fun j => f j x) * Lo (f i) x +
          ∑ i, ∑ j, MarkovTriple.BGL.pderiv₂ ψ i j (fun l => f l x) * Go (f i) (f j) x := by
  have hD := deriv_comp1 ψ hψ f hf
  refine ⟨fun g _ => ?_, ?_⟩
  · funext x
    simp only [Go, hD, Finset.sum_mul, mul_assoc]
  · funext x
    unfold Lo
    rw [hD]
    have hi : ∀ i, HasDerivAt (fun u : ℝ => MarkovTriple.BGL.pderiv ψ i (fun j => f j u) * deriv (f i) u)
        ((∑ j, MarkovTriple.BGL.pderiv (MarkovTriple.BGL.pderiv ψ i) j (fun l => f l x) * deriv (f j) x)
            * deriv (f i) x + MarkovTriple.BGL.pderiv ψ i (fun j => f j x) * deriv (deriv (f i)) x) x := by
      intro i
      have h1 := hasDerivAt_comp1 (MarkovTriple.BGL.pderiv ψ i) (contDiff_pderiv ψ hψ i) f
        (fun j => deriv (f j) x) x (fun j => (hf j).hasDerivAt x)
      have h2 := (hf i).deriv'.hasDerivAt x
      exact h1.mul h2
    have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hi i)
    have h3 := hsum.deriv
    simp only at h3
    rw [h3]
    simp only [MarkovTriple.BGL.pderiv₂, Go, Finset.sum_add_distrib, Finset.sum_mul]
    have : ∀ i j, MarkovTriple.BGL.pderiv (MarkovTriple.BGL.pderiv ψ i) j =
        fun z => fderiv ℝ (fun y => MarkovTriple.BGL.pderiv ψ i y) z (Pi.single j 1) := fun i j => rfl
    simp only [this]
    have hs : ∑ i, ∑ j, (fderiv ℝ (fun y => MarkovTriple.BGL.pderiv ψ i y) (fun l => f l x))
          (Pi.single j 1) * deriv (f j) x * deriv (f i) x =
        ∑ i, ∑ j, (fderiv ℝ (fun y => MarkovTriple.BGL.pderiv ψ i y) (fun l => f l x))
          (Pi.single j 1) * (deriv (f i) x * deriv (f j) x) :=
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    have e4 : ∑ i, MarkovTriple.BGL.pderiv ψ i (fun j => f j x) * (deriv (deriv (f i)) x - x * deriv (f i) x)
        = ∑ i, MarkovTriple.BGL.pderiv ψ i (fun j => f j x) * deriv (deriv (f i)) x
          - x * ∑ i, MarkovTriple.BGL.pderiv ψ i (fun j => f j x) * deriv (f i) x := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [e4, hs]
    ring

end Calc

end MarkovTriple.Sanity.OU
