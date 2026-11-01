import Mathlib
import MarkovTriple.Frozen.MarkovTriple
import MarkovTriple.Frozen.CD
import MarkovTriple.Frozen.Gamma2

/-!
# Sanity instance with an INFINITE measure: Lebesgue measure on `ℝ` (NOT frozen)

`μ = volume` on `ℝ` (σ-finite, not finite), `𝒜₀ = C_c^∞(ℝ)` (a non-unital algebra: it does not
contain the constants, which are not in `L^p`), `L f = f''`, `Γ(f,g) = f' g'`.
Every field of `MarkovTriple` is proved.  This shows that the redesigned structure admits
σ-finite non-finite measures (DECISIONS items 8–10), and that stability of `𝒜₀` under smooth `ψ`
with `ψ(0) = 0` is satisfiable (compact support is preserved because `ψ(0) = 0`).

Density in `Lᵖ` is Mathlib's `MeasureTheory.Lp.dense_hasCompactSupport_contDiff`; integration by
parts is `MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace MarkovTriple.Sanity.Lebesgue

/-- `C_c^∞(ℝ)` as a non-unital subalgebra of `ℝ → ℝ`. -/
def A₀ : NonUnitalSubalgebra ℝ (ℝ → ℝ) where
  carrier := {f | ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f}
  add_mem' := fun {f g} (hf : ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g ∧ HasCompactSupport g) => ⟨hf.1.add hg.1, hf.2.add hg.2⟩
  zero_mem' := (⟨contDiff_const, HasCompactSupport.zero⟩ :
    ContDiff ℝ (⊤ : ℕ∞) (0 : ℝ → ℝ) ∧ HasCompactSupport (0 : ℝ → ℝ))
  mul_mem' := fun {f g} (hf : ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g ∧ HasCompactSupport g) => ⟨hf.1.mul hg.1, hf.2.mul_right⟩
  smul_mem' := fun c {f} (hf : ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f) =>
    ⟨hf.1.const_smul c, hf.2.smul_left⟩

lemma mem_A₀ {f : ℝ → ℝ} : f ∈ A₀ ↔ ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f := by
  constructor <;> intro h <;> exact h

lemma smooth {f : ℝ → ℝ} (hf : f ∈ A₀) : ContDiff ℝ (⊤ : ℕ∞) f := (mem_A₀.1 hf).1
lemma cs {f : ℝ → ℝ} (hf : f ∈ A₀) : HasCompactSupport f := (mem_A₀.1 hf).2

lemma deriv_mem {f : ℝ → ℝ} (hf : f ∈ A₀) : deriv f ∈ A₀ :=
  mem_A₀.2 ⟨(contDiff_infty_iff_deriv.1 (smooth hf)).2, (cs hf).deriv⟩

lemma hasDerivAt_of {f : ℝ → ℝ} (hf : f ∈ A₀) (x : ℝ) : HasDerivAt f (deriv f x) x :=
  ((smooth hf).differentiable (by simp) x).hasDerivAt

lemma integrable_of {f : ℝ → ℝ} (hf : f ∈ A₀) : Integrable f :=
  (smooth hf).continuous.integrable_of_hasCompactSupport (cs hf)

lemma memLp_of {f : ℝ → ℝ} (hf : f ∈ A₀) (p : ℝ≥0∞) : MemLp f p :=
  (smooth hf).continuous.memLp_of_hasCompactSupport (cs hf)

/-- generator `L f = f''`. -/
noncomputable def Lf (f : ℝ → ℝ) : ℝ → ℝ := deriv (deriv f)

/-- carré du champ `Γ(f,g) = f' g'`. -/
noncomputable def Gf (f g : ℝ → ℝ) : ℝ → ℝ := fun x => deriv f x * deriv g x

lemma deriv_mul' {f g : ℝ → ℝ} (hf : f ∈ A₀) (hg : g ∈ A₀) :
    deriv (f * g) = deriv f * g + f * deriv g := by
  funext x
  have := ((hasDerivAt_of hf x).mul (hasDerivAt_of hg x)).deriv
  simpa [add_comm] using this

lemma deriv_add' {f g : ℝ → ℝ} (hf : f ∈ A₀) (hg : g ∈ A₀) : deriv (f + g) = deriv f + deriv g := by
  funext x
  exact ((hasDerivAt_of hf x).add (hasDerivAt_of hg x)).deriv

lemma deriv_smul' (c : ℝ) {f : ℝ → ℝ} (hf : f ∈ A₀) : deriv (c • f) = c • deriv f := by
  funext x
  exact ((hasDerivAt_of hf x).const_smul c).deriv

lemma Lf_mul {f g : ℝ → ℝ} (hf : f ∈ A₀) (hg : g ∈ A₀) (x : ℝ) :
    Lf (f * g) x = Lf f x * g x + 2 * (deriv f x * deriv g x) + f x * Lf g x := by
  unfold Lf
  rw [deriv_mul' hf hg, deriv_add' (mul_mem (deriv_mem hf) hg) (mul_mem hf (deriv_mem hg)),
    deriv_mul' (deriv_mem hf) hg, deriv_mul' hf (deriv_mem hg)]
  simp only [Pi.add_apply, Pi.mul_apply]
  ring

lemma ibp_L {f g : ℝ → ℝ} (hf : f ∈ A₀) (hg : g ∈ A₀) :
    ∫ x, g x * Lf f x ∂volume = -∫ x, Gf f g x ∂volume := by
  have hd := deriv_mem hf
  have h := integral_mul_deriv_eq_deriv_mul_of_integrable (u := g) (v := deriv f)
    (u' := deriv g) (v' := deriv (deriv f))
    (fun x _ => hasDerivAt_of hg x) (fun x _ => hasDerivAt_of hd x)
    (integrable_of (mul_mem hg (deriv_mem hd))) (integrable_of (mul_mem (deriv_mem hg) hd))
    (integrable_of (mul_mem hg hd))
  try simp only [Pi.mul_apply] at h
  unfold Gf Lf
  rw [h]
  congr 2
  funext x; ring

/-! ### Chain rule on `ℝ` -/

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
      (∑ i, MarkovTriple.pderiv ψ i (fun j => γ j t) * d i) t := by
  have hγ' : HasDerivAt (fun u : ℝ => fun i => γ i u) d t := hasDerivAt_pi.2 hγ
  have hψd : HasFDerivAt ψ (fderiv ℝ ψ (fun i => γ i t)) (fun i => γ i t) :=
    ((hψ.differentiable (by simp)) _).hasFDerivAt
  have := hψd.comp_hasDerivAt t hγ'
  refine this.congr_deriv ?_
  rw [clm_pi_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold MarkovTriple.pderiv; ring

lemma contDiff_pderiv {k : ℕ} (ψ : (Fin k → ℝ) → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (i : Fin k) :
    ContDiff ℝ (⊤ : ℕ∞) (MarkovTriple.pderiv ψ i) := by
  unfold MarkovTriple.pderiv
  exact (hψ.fderiv_right (by simp)).clm_apply contDiff_const

lemma deriv_comp1 {k : ℕ} (ψ : (Fin k → ℝ) → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (f : Fin k → ℝ → ℝ) (hf : ∀ i, f i ∈ A₀) :
    deriv (fun x => ψ (fun i => f i x)) =
      fun y => ∑ i, MarkovTriple.pderiv ψ i (fun j => f j y) * deriv (f i) y := by
  funext y
  exact (hasDerivAt_comp1 ψ hψ f (fun i => deriv (f i) y) y (fun i => hasDerivAt_of (hf i) y)).deriv

lemma comp_mem_A₀ (k : ℕ) (ψ : (Fin k → ℝ) → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (h0 : ψ 0 = 0)
    (f : Fin k → ℝ → ℝ) (hf : ∀ i, f i ∈ A₀) : (fun x => ψ (fun i => f i x)) ∈ A₀ := by
  refine mem_A₀.2 ⟨hψ.comp (contDiff_pi.2 fun i => smooth (hf i)), ?_⟩
  refine HasCompactSupport.intro (K := ⋃ i, tsupport (f i))
    (isCompact_iUnion fun i => (cs (hf i))) fun x hx => ?_
  have : ∀ i, f i x = 0 := fun i =>
    image_eq_zero_of_notMem_tsupport (fun h => hx (Set.mem_iUnion.2 ⟨i, h⟩))
  have e : (fun i => f i x) = 0 := funext this
  simp only [e, h0]

lemma diffusion_c (k : ℕ) (ψ : (Fin k → ℝ) → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (f : Fin k → ℝ → ℝ) (hf : ∀ i, f i ∈ A₀) :
    (∀ g ∈ A₀, Gf (fun x => ψ (fun i => f i x)) g =
        fun x => ∑ i, MarkovTriple.pderiv ψ i (fun j => f j x) * Gf (f i) g x) ∧
      Lf (fun x => ψ (fun i => f i x)) =
        fun x => ∑ i, MarkovTriple.pderiv ψ i (fun j => f j x) * Lf (f i) x +
          ∑ i, ∑ j, MarkovTriple.pderiv₂ ψ i j (fun l => f l x) * Gf (f i) (f j) x := by
  have hD := deriv_comp1 ψ hψ f hf
  refine ⟨fun g _ => ?_, ?_⟩
  · funext x
    simp only [Gf, hD, Finset.sum_mul, mul_assoc]
  · funext x
    unfold Lf
    rw [hD]
    have hi : ∀ i, HasDerivAt (fun u : ℝ => MarkovTriple.pderiv ψ i (fun j => f j u) * deriv (f i) u)
        ((∑ j, MarkovTriple.pderiv (MarkovTriple.pderiv ψ i) j (fun l => f l x) * deriv (f j) x)
            * deriv (f i) x + MarkovTriple.pderiv ψ i (fun j => f j x) * deriv (deriv (f i)) x) x := by
      intro i
      have h1 := hasDerivAt_comp1 (MarkovTriple.pderiv ψ i) (contDiff_pderiv ψ hψ i) f
        (fun j => deriv (f j) x) x (fun j => hasDerivAt_of (hf j) x)
      have h2 := hasDerivAt_of (deriv_mem (hf i)) x
      exact h1.mul h2
    have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hi i)
    have h3 := hsum.deriv
    simp only at h3
    rw [h3]
    simp only [MarkovTriple.pderiv₂, Gf, Finset.sum_add_distrib, Finset.sum_mul]
    have : ∀ i j, MarkovTriple.pderiv (MarkovTriple.pderiv ψ i) j =
        fun z => fderiv ℝ (fun y => MarkovTriple.pderiv ψ i y) z (Pi.single j 1) := fun i j => rfl
    simp only [this]
    rw [add_comm]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring

lemma dense_Lp (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    Dense {u : Lp ℝ p (volume : Measure ℝ) | ∃ f ∈ A₀, (u : ℝ → ℝ) =ᵐ[volume] f} := by
  refine (Lp.dense_hasCompactSupport_contDiff (F := ℝ) (μ := (volume : Measure ℝ)) hp).mono ?_
  rintro u ⟨g, hug, hcs, hcd⟩
  exact ⟨g, mem_A₀.2 ⟨hcd, hcs⟩, hug⟩

/-- **The Lebesgue Markov triple on `ℝ`**: infinite σ-finite measure, `𝒜₀ = C_c^∞(ℝ)`,
`L f = f''`, `Γ(f,g) = f' g'`. -/
noncomputable def lebesgueTriple : MarkovTriple ℝ where
  μ := volume
  sigmaFinite := inferInstance
  A₀ := A₀
  Γ := Gf
  L := Lf
  measurable := fun f hf => (smooth hf).continuous.measurable
  memLp := fun f hf p _ => memLp_of hf p
  comp_mem := fun k ψ hψ h0 f hf => comp_mem_A₀ k ψ hψ h0 f hf
  Γ_mem := fun f hf g hg => mul_mem (deriv_mem hf) (deriv_mem hg)
  L_mem := fun f hf => deriv_mem (deriv_mem hf)
  Γ_symm := fun f _ g _ => by funext x; simp [Gf, mul_comm]
  Γ_add := fun f hf f' hf' g _ => by
    funext x; simp [Gf, deriv_add' hf hf', add_mul]
  Γ_smul := fun c f hf g _ => by
    funext x; simp [Gf, deriv_smul' c hf, mul_assoc]
  Γ_nonneg := fun f _ x => by simpa [Gf] using mul_self_nonneg (deriv f x)
  L_add := fun f hf g hg => by
    unfold Lf
    rw [deriv_add' hf hg, deriv_add' (deriv_mem hf) (deriv_mem hg)]
  L_smul := fun c f hf => by
    unfold Lf
    rw [deriv_smul' c hf, deriv_smul' c (deriv_mem hf)]
  carre_du_champ := fun f hf g hg x => by
    rw [Lf_mul hf hg x]
    simp only [Gf]
    ring
  ibp := fun f hf g hg => ibp_L hf hg
  dense := fun p hp hp' => dense_Lp p hp'
  diffusion := fun k ψ hψ _ f hf => diffusion_c k ψ hψ f hf

/-- The measure is σ-finite but **not finite**: this triple lives on an infinite measure space. -/
theorem lebesgueTriple_not_finite : lebesgueTriple.μ Set.univ = ∞ := Real.volume_univ

theorem lebesgueTriple_sigmaFinite : SigmaFinite lebesgueTriple.μ := lebesgueTriple.sigmaFinite

/-- `Γ₂(f) = (f'')²` (flat). -/
theorem lebesgue_Γ₂ {f : ℝ → ℝ} (hf : f ∈ A₀) (x : ℝ) :
    lebesgueTriple.Γ₂ f x = (lebesgueTriple.L f x) ^ 2 := by
  have h := Lf_mul (deriv_mem hf) (deriv_mem hf) x
  show (Lf (Gf f f) x - 2 * Gf f (Lf f) x) / 2 = (Lf f x) ^ 2
  have e : Gf f f = deriv f * deriv f := rfl
  rw [e, h]
  simp only [Gf, Lf]
  ring

/-- `CD(0,n)` for every `1 ≤ n ≤ ∞` on the line. -/
theorem lebesgue_CD {ρ : ℝ} (hρ : ρ ≤ 0) {n : ℝ≥0∞} (hn : 1 ≤ n) : lebesgueTriple.CD ρ n := by
  refine ⟨lt_of_lt_of_le one_pos hn, fun f hf => Filter.Eventually.of_forall fun x => ?_⟩
  rw [lebesgue_Γ₂ hf x]
  have h1 : (n⁻¹).toReal ≤ 1 := by
    have : n⁻¹ ≤ 1 := ENNReal.inv_le_one.2 hn
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top this
  have h2 : ρ * lebesgueTriple.Γ f f x ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hρ (lebesgueTriple.Γ_nonneg f hf x)
  have h3 : (n⁻¹).toReal * (lebesgueTriple.L f x) ^ 2 ≤ (lebesgueTriple.L f x) ^ 2 := by
    nlinarith [sq_nonneg (lebesgueTriple.L f x)]
  linarith

end MarkovTriple.Sanity.Lebesgue

#print axioms MarkovTriple.Sanity.Lebesgue.lebesgueTriple
#print axioms MarkovTriple.Sanity.Lebesgue.lebesgueTriple_not_finite
#print axioms MarkovTriple.Sanity.Lebesgue.lebesgue_CD
