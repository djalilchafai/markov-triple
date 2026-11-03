import Mathlib
import MarkovTriple.BGL.Instances.GibbsRd.Calculus
import MarkovTriple.BGL.Frozen.DiffusionTriple
import MarkovTriple.BGL.Frozen.GammaA
import MarkovTriple.BGL.Frozen.Gamma2

/-!
# Weighted elliptic operators `L = w⁻¹ div (w a ∇ ·)` on `ℝ^d` as BGL `DiffusionTriple`s (D1–D8)

BGL Sect. 1.11.2 (1.11.1)–(1.11.9): for a smooth symmetric positive definite matrix field `a = (g^{ij})` and a smooth
positive density `w`, the operator `L f = (1/w) Σᵢ ∂ᵢ(w Σⱼ aᵢⱼ ∂ⱼ f)` has carré du champ
`Γ(f,g) = Σᵢⱼ aᵢⱼ ∂ᵢf ∂ⱼg` and is symmetric for `dμ = Z⁻¹ w dx` (`∫ g L f dμ = −∫ Γ(f,g) dμ`).
The weighted Riemannian operators of Sect. 1.11.3 (`Riemannian/`) and the Gibbs operators `Δ − ∇V·∇` (`GibbsRd/Gibbs`)
are special cases (`a = g^{ij}`, `w = e^{-W} det(g)^{-1/2}`; resp. `a = δ`, `w = e^{-V}`).

Proved here, with no hypothesis beyond the fields of `EllData`: `EllData.diff : DiffusionTriple (Rd d)` (D1–D8, test
algebra `𝒜₀ = C_c^∞(ℝ^d)`), `ΓA_eq` (the formula-defined `Γ` of Def. 3.3.1 (iv) is the coordinate one) and the change
of variables formulas (3.1.2)/(3.1.8) on `C^∞` for `Γ` and `L`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace MarkovTriple.BGL.Instances.GibbsRd

open MarkovTriple.BGL (pderiv pderiv₂ DiffusionTriple)

variable {d : ℕ}

/-- Data of a weighted elliptic diffusion operator in global coordinates on `ℝ^d`:
`a = (g^{ij})` smooth, symmetric, positive definite, bounded above (so that the Euclidean cut-offs have bounded
`Γ`: completeness), `w` smooth positive and integrable. -/
structure EllData (d : ℕ) where
  /-- the matrix of second-order coefficients (the co-metric `g^{ij}`) -/
  a : Fin d → Fin d → Rd d → ℝ
  /-- the (unnormalised) reversible density of `L` with respect to `dx` -/
  w : Rd d → ℝ
  a_smooth : ∀ i j, Sm (a i j)
  a_symm : ∀ i j x, a i j x = a j i x
  a_pos : ∀ (x v : Rd d), v ≠ 0 → 0 < ∑ i, ∑ j, a i j x * v i * v j
  a_bdd : ∃ Λ : ℝ, ∀ (x v : Rd d), ∑ i, ∑ j, a i j x * v i * v j ≤ Λ * ∑ i, v i ^ 2
  w_smooth : Sm w
  w_pos : ∀ x, 0 < w x
  integrable : Integrable w volume

namespace EllData
variable (E : EllData d)

/-- the carré du champ `Γ(f,g) = Σᵢⱼ aᵢⱼ ∂ᵢf ∂ⱼg` (BGL (1.11.2)) -/
noncomputable def Γ (f g : Rd d → ℝ) : Rd d → ℝ :=
  fun x => ∑ i, ∑ j, E.a i j x * pderiv f i x * pderiv g j x

/-- the generator `L f = w⁻¹ Σᵢ ∂ᵢ(w Σⱼ aᵢⱼ ∂ⱼ f)` (BGL Sect. 1.11.3) -/
noncomputable def L (f : Rd d → ℝ) : Rd d → ℝ :=
  fun x => (E.w x)⁻¹ * ∑ i, pderiv (fun y => E.w y * ∑ j, E.a i j y * pderiv f j y) i x

/-- the normalising constant -/
noncomputable def Z : ℝ := ∫ x, E.w x

lemma Z_pos : 0 < E.Z := by
  unfold Z
  refine (integral_pos_iff_support_of_nonneg (fun x => (E.w_pos x).le) E.integrable).2 ?_
  have : Function.support E.w = Set.univ := Set.eq_univ_of_forall fun x => (E.w_pos x).ne'
  rw [this]; simp [(NeZero.ne (volume : Measure (Rd d)))]

/-- the normalised density -/
noncomputable def dens (x : Rd d) : ℝ := E.w x / E.Z

lemma dens_pos (x : Rd d) : 0 < E.dens x := div_pos (E.w_pos x) E.Z_pos

lemma dens_smooth : Sm E.dens := E.w_smooth.div_const _

lemma dens_integrable : Integrable E.dens volume := E.integrable.div_const _

lemma integral_dens : ∫ x, E.dens x = 1 := by
  unfold dens
  rw [integral_div]
  exact div_self E.Z_pos.ne'

/-- the reversible probability measure `μ = Z⁻¹ w dx` -/
noncomputable def μ : Measure (Rd d) := volume.withDensity (fun x => ENNReal.ofReal (E.dens x))

instance : IsProbabilityMeasure E.μ := by
  refine ⟨?_⟩
  unfold μ
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal E.dens_integrable
      (Filter.Eventually.of_forall fun x => (E.dens_pos x).le), integral_dens]
  simp

lemma integral_μ (F : Rd d → ℝ) : ∫ x, F x ∂E.μ = ∫ x, E.dens x * F x := by
  unfold μ
  rw [integral_withDensity_eq_integral_toReal_smul (f := fun x => ENNReal.ofReal (E.dens x))
    (ENNReal.measurable_ofReal.comp E.dens_smooth.continuous.measurable)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [ENNReal.toReal_ofReal (E.dens_pos x).le]

instance : E.μ.IsOpenPosMeasure := by
  refine ⟨fun U hU hne h0 => ?_⟩
  unfold μ at h0
  rw [withDensity_apply _ hU.measurableSet] at h0
  have h1 := (lintegral_eq_zero_iff (ENNReal.measurable_ofReal.comp
    E.dens_smooth.continuous.measurable)).1
    (by simpa using h0 : ∫⁻ x in U, ENNReal.ofReal (E.dens x) ∂volume = 0)
  have h2 : ∀ᵐ x ∂(volume.restrict U), False := by
    filter_upwards [h1] with x hx
    simp [ENNReal.ofReal_eq_zero, not_le.2 (E.dens_pos x)] at hx
  have := (ae_restrict_iff' hU.measurableSet).1 h2
  have h3 : volume U = 0 := by
    have : ∀ᵐ x ∂volume, x ∉ U := by
      filter_upwards [this] with x hx hxU using hx hxU
    simpa [ae_iff] using this
  exact hU.measure_ne_zero volume hne h3

/-! ### Smoothness and supports -/

lemma sm_Γ {f g : Rd d → ℝ} (hf : Sm f) (hg : Sm g) : Sm (E.Γ f g) :=
  ContDiff.sum fun i _ => ContDiff.sum fun j _ =>
    ((E.a_smooth i j).mul (hf.pderiv i)).mul (hg.pderiv j)

/-- the inner vector field `Pᵢ(f) = w Σⱼ aᵢⱼ ∂ⱼ f` -/
noncomputable def P (f : Rd d → ℝ) (i : Fin d) : Rd d → ℝ :=
  fun y => E.w y * ∑ j, E.a i j y * pderiv f j y

lemma sm_P {f : Rd d → ℝ} (hf : Sm f) (i : Fin d) : Sm (E.P f i) :=
  E.w_smooth.mul (ContDiff.sum fun j _ => (E.a_smooth i j).mul (hf.pderiv j))

lemma L_eq (f : Rd d → ℝ) (x : Rd d) : E.L f x = (E.w x)⁻¹ * ∑ i, pderiv (E.P f i) i x := rfl

lemma sm_L {f : Rd d → ℝ} (hf : Sm f) : Sm (E.L f) :=
  (E.w_smooth.inv fun x => (E.w_pos x).ne').mul
    (ContDiff.sum fun i _ => (E.sm_P hf i).pderiv i)

lemma hcs_sum {ι : Type*} (s : Finset ι) {F : ι → Rd d → ℝ} (hF : ∀ i ∈ s, HasCompactSupport (F i)) :
    HasCompactSupport (fun x => ∑ i ∈ s, F i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact HasCompactSupport.intro isCompact_empty fun _ _ => rfl
  | insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    exact (hF j (Finset.mem_insert_self _ _)).add (ih fun i hi => hF i (Finset.mem_insert_of_mem hi))

lemma hcs_of_factor {F u : Rd d → ℝ} (hu : HasCompactSupport u) (h : ∀ x, u x = 0 → F x = 0) :
    HasCompactSupport F :=
  HasCompactSupport.intro hu fun x hx => h x (image_eq_zero_of_notMem_tsupport hx)

lemma hcs_P {f : Rd d → ℝ} (hc : HasCompactSupport f) (i : Fin d) : HasCompactSupport (E.P f i) := by
  have : HasCompactSupport (fun y => ∑ j, E.a i j y * pderiv f j y) :=
    hcs_sum _ fun j _ => hcs_of_factor (hc.fderiv_apply ℝ (Pi.single j 1)) fun x hx => by
      simp only [pderiv] at hx ⊢; rw [hx]; ring
  exact hcs_of_factor this fun x hx => by simp only [P]; rw [hx]; ring

lemma hcs_L {f : Rd d → ℝ} (hc : HasCompactSupport f) : HasCompactSupport (E.L f) := by
  have : HasCompactSupport (fun x => ∑ i, pderiv (E.P f i) i x) :=
    hcs_sum _ fun i _ => (E.hcs_P hc i).fderiv_apply ℝ (Pi.single i 1)
  exact hcs_of_factor this fun x hx => by rw [L_eq, hx]; ring

lemma hcs_Γ_right {f g : Rd d → ℝ} (hc : HasCompactSupport g) : HasCompactSupport (E.Γ f g) :=
  hcs_sum _ fun i _ => hcs_sum _ fun j _ =>
    hcs_of_factor (hc.fderiv_apply ℝ (Pi.single j 1)) fun x hx => by
      simp only [pderiv] at hx ⊢; rw [hx]; ring

lemma hcs_Γ_left {f g : Rd d → ℝ} (hc : HasCompactSupport f) : HasCompactSupport (E.Γ f g) :=
  hcs_sum _ fun i _ => hcs_sum _ fun j _ =>
    hcs_of_factor (hc.fderiv_apply ℝ (Pi.single i 1)) fun x hx => by
      simp only [pderiv] at hx ⊢; rw [hx]; ring

lemma L_mem {f : Rd d → ℝ} (hf : f ∈ A₀ d) : E.L f ∈ A₀ d := ⟨E.sm_L hf.1, E.hcs_L hf.2⟩

lemma Γ_mem {f g : Rd d → ℝ} (hf : f ∈ A₀ d) (hg : g ∈ A₀ d) : E.Γ f g ∈ A₀ d :=
  ⟨E.sm_Γ hf.1 hg.1, E.hcs_Γ_right hg.2⟩

lemma Γ_symm (f g : Rd d → ℝ) : E.Γ f g = E.Γ g f := by
  funext x
  unfold Γ
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [E.a_symm i j x]; ring

lemma Γ_nonneg (f : Rd d → ℝ) (x : Rd d) : 0 ≤ E.Γ f f x := by
  by_cases h : (fun i => pderiv f i x) = 0
  · have : E.Γ f f x = 0 := by simp [Γ, congrFun h]
    rw [this]
  · have := E.a_pos x _ h
    unfold Γ
    refine this.le.trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring

/-! ### Integration by parts -/

/-- master integration by parts: `∫ w (g L f + Γ(g,f)) dx = 0` when `g` or `f` has compact support. -/
lemma ibp_master {f g : Rd d → ℝ} (hf : Sm f) (hg : Sm g)
    (hc : HasCompactSupport g ∨ HasCompactSupport f) :
    ∫ x, (E.w x * g x * E.L f x + E.w x * E.Γ g f x) = 0 := by
  classical
  have hHs : ∀ i, Sm (fun y => g y * E.P f i y) := fun i => hg.mul (E.sm_P hf i)
  have hHc : ∀ i, HasCompactSupport (fun y => g y * E.P f i y) := by
    intro i
    rcases hc with h | h
    · exact h.mul_right
    · exact (E.hcs_P h i).mul_left
  have hsum : ∀ x, ∑ i, pderiv (fun y => g y * E.P f i y) i x =
      E.w x * g x * E.L f x + E.w x * E.Γ g f x := by
    intro x
    have hP : ∀ i, pderiv (fun y => g y * E.P f i y) i x =
        pderiv g i x * E.P f i x + g x * pderiv (E.P f i) i x := fun i =>
      pderiv_mul (f := g) (g := E.P f i) hg (E.sm_P hf i) i x
    simp only [hP, Finset.sum_add_distrib]
    have h1 : ∑ i, g x * pderiv (E.P f i) i x = E.w x * g x * E.L f x := by
      rw [← Finset.mul_sum, E.L_eq]
      have := (E.w_pos x).ne'
      field_simp
    have h2 : ∑ i, pderiv g i x * E.P f i x = E.w x * E.Γ g f x := by
      unfold P Γ
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [h1, h2]; ring
  have hint : ∀ i, ∫ x, pderiv (fun y => g y * E.P f i y) i x = 0 := fun i =>
    integral_pderiv_eq_zero (hHs i) (hHc i) i
  have hI : ∀ i, Integrable (fun x => pderiv (fun y => g y * E.P f i y) i x) volume := fun i =>
    ((hHs i).pderiv i).continuous.integrable_of_hasCompactSupport
      ((hHc i).fderiv_apply ℝ (Pi.single i 1))
  calc ∫ x, (E.w x * g x * E.L f x + E.w x * E.Γ g f x)
      = ∫ x, ∑ i, pderiv (fun y => g y * E.P f i y) i x :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => (hsum x).symm)
    _ = ∑ i, ∫ x, pderiv (fun y => g y * E.P f i y) i x := integral_finsetSum _ fun i _ => hI i
    _ = 0 := Finset.sum_eq_zero fun i _ => hint i

end EllData

end MarkovTriple.BGL.Instances.GibbsRd
