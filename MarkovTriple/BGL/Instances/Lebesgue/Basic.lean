import Mathlib
import MarkovTriple.BGL.Frozen.DiffusionTriple

/-!
# Brownian triple on `(ℝ, Lebesgue)`: the algebras and the calculus (BGL Ch. 3, §3.2 example)

`𝒜₀ = C_c^∞(ℝ)` (non-unital), `𝒜 = C^∞(ℝ)` (unital), `L f = f''`, `Γ(f,g) = f' g'`.
This file contains only the elementary real-variable calculus (no semigroup): the algebras, the
chain rule on smooth functions, integration by parts, the cutoff sequence.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace MarkovTriple.BGL.Lebesgue

/-- smooth functions. -/
abbrev Sm (f : ℝ → ℝ) : Prop := ContDiff ℝ (⊤ : ℕ∞) f

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

/-- `C^∞(ℝ)` as a unital subalgebra. -/
def A : Subalgebra ℝ (ℝ → ℝ) where
  carrier := {f | ContDiff ℝ (⊤ : ℕ∞) f}
  add_mem' := fun {f g} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) => hf.add hg
  zero_mem' := (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (0 : ℝ → ℝ))
  mul_mem' := fun {f g} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) => hf.mul hg
  algebraMap_mem' := fun r => (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : ℝ => r))

lemma mem_A₀ {f : ℝ → ℝ} : f ∈ A₀ ↔ ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f := Iff.rfl
lemma mem_A {f : ℝ → ℝ} : f ∈ A ↔ ContDiff ℝ (⊤ : ℕ∞) f := Iff.rfl

lemma smooth {f : ℝ → ℝ} (hf : f ∈ A₀) : Sm f := (mem_A₀.1 hf).1
lemma cs {f : ℝ → ℝ} (hf : f ∈ A₀) : HasCompactSupport f := (mem_A₀.1 hf).2
lemma A₀_le_A {f : ℝ → ℝ} (hf : f ∈ A₀) : f ∈ A := smooth hf

lemma Sm.deriv' {f : ℝ → ℝ} (hf : Sm f) : Sm (deriv f) := (contDiff_infty_iff_deriv.1 hf).2

lemma Sm.hasDerivAt {f : ℝ → ℝ} (hf : Sm f) (x : ℝ) : HasDerivAt f (deriv f x) x :=
  (hf.differentiable (by simp) x).hasDerivAt

lemma deriv_mem {f : ℝ → ℝ} (hf : f ∈ A₀) : deriv f ∈ A₀ :=
  mem_A₀.2 ⟨(smooth hf).deriv', (cs hf).deriv⟩

lemma hasDerivAt_of {f : ℝ → ℝ} (hf : f ∈ A₀) (x : ℝ) : HasDerivAt f (deriv f x) x :=
  (smooth hf).hasDerivAt x

lemma integrable_of {f : ℝ → ℝ} (hf : f ∈ A₀) : Integrable f :=
  (smooth hf).continuous.integrable_of_hasCompactSupport (cs hf)

lemma memLp_of {f : ℝ → ℝ} (hf : f ∈ A₀) (p : ℝ≥0∞) : MemLp f p :=
  (smooth hf).continuous.memLp_of_hasCompactSupport (cs hf)

/-- generator `L f = f''`. -/
noncomputable def Lf (f : ℝ → ℝ) : ℝ → ℝ := deriv (deriv f)

/-- carré du champ `Γ(f,g) = f' g'`. -/
noncomputable def Gf (f g : ℝ → ℝ) : ℝ → ℝ := fun x => deriv f x * deriv g x

lemma deriv_mul_sm {f g : ℝ → ℝ} (hf : Sm f) (hg : Sm g) :
    deriv (f * g) = deriv f * g + f * deriv g := by
  funext x
  have := ((hf.hasDerivAt x).mul (hg.hasDerivAt x)).deriv
  simpa [add_comm] using this

lemma deriv_add_sm {f g : ℝ → ℝ} (hf : Sm f) (hg : Sm g) : deriv (f + g) = deriv f + deriv g := by
  funext x
  exact ((hf.hasDerivAt x).add (hg.hasDerivAt x)).deriv

lemma deriv_smul_sm (c : ℝ) {f : ℝ → ℝ} (hf : Sm f) : deriv (c • f) = c • deriv f := by
  funext x
  exact ((hf.hasDerivAt x).const_smul c).deriv

lemma Lf_mul {f g : ℝ → ℝ} (hf : Sm f) (hg : Sm g) (x : ℝ) :
    Lf (f * g) x = Lf f x * g x + 2 * (deriv f x * deriv g x) + f x * Lf g x := by
  unfold Lf
  rw [deriv_mul_sm hf hg,
    deriv_add_sm (f := deriv f * g) (g := f * deriv g) (hf.deriv'.mul hg) (hf.mul hg.deriv'),
    deriv_mul_sm hf.deriv' hg, deriv_mul_sm hf hg.deriv']
  simp only [Pi.add_apply, Pi.mul_apply]
  ring

/-- Integration by parts, one compactly supported factor. -/
lemma ibp_cs {u v : ℝ → ℝ} (hu : Sm u) (hv : Sm v)
    (hcs : HasCompactSupport u ∨ HasCompactSupport v) :
    ∫ x, u x * deriv v x = -∫ x, deriv u x * v x := by
  have h1 : Integrable (u * deriv v) := by
    refine (hu.continuous.mul hv.deriv'.continuous).integrable_of_hasCompactSupport ?_
    rcases hcs with h | h
    · exact h.mul_right
    · exact h.deriv.mul_left
  have h2 : Integrable (deriv u * v) := by
    refine (hu.deriv'.continuous.mul hv.continuous).integrable_of_hasCompactSupport ?_
    rcases hcs with h | h
    · exact h.deriv.mul_right
    · exact h.mul_left
  have h3 : Integrable (u * v) := by
    refine (hu.continuous.mul hv.continuous).integrable_of_hasCompactSupport ?_
    rcases hcs with h | h
    · exact h.mul_right
    · exact h.mul_left
  exact integral_mul_deriv_eq_deriv_mul_of_integrable (fun x _ => hu.hasDerivAt x)
    (fun x _ => hv.hasDerivAt x) h1 h2 h3

lemma ibp_L {f g : ℝ → ℝ} (hf : Sm f) (hg : g ∈ A₀) :
    ∫ x, g x * Lf f x = -∫ x, Gf f g x := by
  have h := ibp_cs (smooth hg) hf.deriv' (Or.inl (cs hg))
  unfold Lf Gf
  rw [h]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only; ring

lemma ibp_L' {f g : ℝ → ℝ} (hf : Sm f) (hg : g ∈ A₀) :
    ∫ x, f x * Lf g x = -∫ x, Gf f g x := by
  have h := ibp_cs hf (smooth hg).deriv' (Or.inr (cs hg).deriv)
  unfold Lf Gf
  rw [h]

/-! ### Chain rule on `ℝ` for smooth functions -/

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

lemma comp_sm {k : ℕ} (ψ : (Fin k → ℝ) → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (f : Fin k → ℝ → ℝ) (hf : ∀ i, Sm (f i)) : Sm (fun x => ψ (fun i => f i x)) :=
  hψ.comp (contDiff_pi.2 hf)

lemma comp_mem_A₀ (k : ℕ) (ψ : (Fin k → ℝ) → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (h0 : ψ 0 = 0)
    (f : Fin k → ℝ → ℝ) (hf : ∀ i, f i ∈ A₀) : (fun x => ψ (fun i => f i x)) ∈ A₀ := by
  refine mem_A₀.2 ⟨comp_sm ψ hψ f (fun i => smooth (hf i)), ?_⟩
  refine HasCompactSupport.intro (K := ⋃ i, tsupport (f i))
    (isCompact_iUnion fun i => (cs (hf i))) fun x hx => ?_
  have : ∀ i, f i x = 0 := fun i =>
    image_eq_zero_of_notMem_tsupport (fun h => hx (Set.mem_iUnion.2 ⟨i, h⟩))
  have e : (fun i => f i x) = 0 := funext this
  simp only [e, h0]

/-- Chain rules for `Γ` and `L` on smooth functions (`ψ` smooth, no vanishing condition). -/
lemma diffusion_c (k : ℕ) (ψ : (Fin k → ℝ) → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (f : Fin k → ℝ → ℝ) (hf : ∀ i, Sm (f i)) :
    (∀ g : ℝ → ℝ, Gf (fun x => ψ (fun i => f i x)) g =
        fun x => ∑ i, MarkovTriple.BGL.pderiv ψ i (fun j => f j x) * Gf (f i) g x) ∧
      Lf (fun x => ψ (fun i => f i x)) =
        fun x => ∑ i, MarkovTriple.BGL.pderiv ψ i (fun j => f j x) * Lf (f i) x +
          ∑ i, ∑ j, MarkovTriple.BGL.pderiv₂ ψ i j (fun l => f l x) * Gf (f i) (f j) x := by
  have hD := deriv_comp1 ψ hψ f hf
  refine ⟨fun g => ?_, ?_⟩
  · funext x
    simp only [Gf, hD, Finset.sum_mul, mul_assoc]
  · funext x
    unfold Lf
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
    simp only [MarkovTriple.BGL.pderiv₂, Gf, Finset.sum_add_distrib, Finset.sum_mul]
    have : ∀ i j, MarkovTriple.BGL.pderiv (MarkovTriple.BGL.pderiv ψ i) j =
        fun z => fderiv ℝ (fun y => MarkovTriple.BGL.pderiv ψ i y) z (Pi.single j 1) := fun i j => rfl
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

/-! ### The cutoff sequence -/

/-- the cutoff `χ(x) = smoothTransition(2 - x²)`: `= 1` on `[-1,1]`, `= 0` off `[-√2, √2]`. -/
noncomputable def chi (x : ℝ) : ℝ := Real.smoothTransition (2 - x ^ 2)

lemma chi_smooth : Sm chi :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub (contDiff_id.pow 2))

lemma chi_zero {x : ℝ} (hx : 2 < |x|) : chi x = 0 := by
  unfold chi
  apply Real.smoothTransition.zero_of_nonpos
  nlinarith [sq_abs x, abs_nonneg x]

lemma chi_cs : HasCompactSupport chi := by
  refine HasCompactSupport.intro (K := Set.Icc (-2) 2) isCompact_Icc fun x hx => ?_
  refine chi_zero ?_
  by_contra h
  exact hx (abs_le.1 (not_lt.1 h))

lemma chi_mem : chi ∈ A₀ := mem_A₀.2 ⟨chi_smooth, chi_cs⟩

lemma chi_nonneg (x : ℝ) : 0 ≤ chi x := Real.smoothTransition.nonneg _
lemma chi_le_one (x : ℝ) : chi x ≤ 1 := Real.smoothTransition.le_one _
lemma chi_eq_one {x : ℝ} (hx : |x| ≤ 1) : chi x = 1 := by
  unfold chi
  apply Real.smoothTransition.one_of_one_le
  nlinarith [sq_abs x, abs_nonneg x]

/-- scaled cutoff `χ(x / R)`. -/
noncomputable def chiR (R : ℝ) (x : ℝ) : ℝ := chi (x / R)

lemma chiR_smooth (R : ℝ) : Sm (chiR R) := chi_smooth.comp (contDiff_id.div_const R)

lemma chiR_cs {R : ℝ} (hR : R ≠ 0) : HasCompactSupport (chiR R) := by
  refine HasCompactSupport.intro (K := Set.Icc (-(2 * |R|)) (2 * |R|)) isCompact_Icc fun x hx => ?_
  refine chi_zero ?_
  have hR' : 0 < |R| := abs_pos.2 hR
  by_contra h
  apply hx
  rw [abs_div] at h
  have := not_lt.1 h
  rw [div_le_iff₀ hR'] at this
  exact abs_le.1 this

lemma deriv_chiR (R : ℝ) (x : ℝ) : deriv (chiR R) x = deriv chi (x / R) / R := by
  have h1 : HasDerivAt (fun x : ℝ => x / R) (1 / R) x := (hasDerivAt_id x).div_const R
  have := (chi_smooth.hasDerivAt (x / R)).comp x h1
  have e : chiR R = chi ∘ (fun x : ℝ => x / R) := rfl
  rw [e, this.deriv]
  ring

lemma deriv_deriv_chiR (R : ℝ) (x : ℝ) :
    deriv (deriv (chiR R)) x = deriv (deriv chi) (x / R) / R ^ 2 := by
  have e : deriv (chiR R) = fun x => deriv chi (x / R) / R := funext (deriv_chiR R)
  rw [e]
  have h1 : HasDerivAt (fun x : ℝ => x / R) (1 / R) x := (hasDerivAt_id x).div_const R
  have := (chi_smooth.deriv'.hasDerivAt (x / R)).comp x h1
  have h2 := this.div_const R
  refine h2.deriv.trans ?_
  field_simp

/-- the exhaustion sequence `u_n(x) = χ(x/(n+1))`: smooth in `n` the monotone form
`smoothTransition(2 - x²/(n+1)²)`. -/
noncomputable def cut (n : ℕ) : ℝ → ℝ := fun x => Real.smoothTransition (2 - x ^ 2 / ((n : ℝ) + 1) ^ 2)

lemma cut_eq (n : ℕ) : cut n = chiR ((n : ℝ) + 1) := by
  funext x; simp [cut, chiR, chi, div_pow]

lemma cut_mem (n : ℕ) : cut n ∈ A₀ := by
  rw [cut_eq]
  exact mem_A₀.2 ⟨chiR_smooth _, chiR_cs (by positivity)⟩

lemma cut_mono (n : ℕ) (x : ℝ) : cut n x ≤ cut (n + 1) x := by
  unfold cut
  apply Real.smoothTransition.monotone
  have h1 : ((n : ℝ) + 1) ^ 2 ≤ (((n + 1 : ℕ) : ℝ) + 1) ^ 2 := by
    push_cast; nlinarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  have h2 : x ^ 2 / (((n + 1 : ℕ) : ℝ) + 1) ^ 2 ≤ x ^ 2 / ((n : ℝ) + 1) ^ 2 :=
    div_le_div_of_nonneg_left (sq_nonneg x) (by positivity) h1
  linarith

lemma cut_nonneg (n : ℕ) (x : ℝ) : 0 ≤ cut n x := Real.smoothTransition.nonneg _
lemma cut_le_one (n : ℕ) (x : ℝ) : cut n x ≤ 1 := Real.smoothTransition.le_one _

lemma cut_tendsto (x : ℝ) : Tendsto (fun n => cut n x) atTop (𝓝 1) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop (⌈|x|⌉₊)] with n hn
  rw [cut_eq]
  symm
  apply chi_eq_one
  have h1 : |x| ≤ (n : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hn)
  rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < (n : ℝ) + 1), div_le_one (by positivity)]
  linarith

end MarkovTriple.BGL.Lebesgue
