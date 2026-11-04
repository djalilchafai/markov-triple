import Mathlib
import MarkovTriple.BGL.Frozen.DiffusionTriple
import MarkovTriple.BGL.Instances.Lebesgue.Basic

/-!
# Brownian triple on `(ℝ^d, Lebesgue)`: algebras, calculus, and the `DiffusionTriple` (stage S1)

`𝒜₀ = C_c^∞(ℝ^d)`, `𝒜 = C^∞(ℝ^d)`, `L f = Σᵢ ∂ᵢ² f`, `Γ(f,g) = Σᵢ ∂ᵢf ∂ᵢg` on `Fin d → ℝ` with `volume`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace MarkovTriple.BGL.LebesgueRd

variable {d : ℕ}

/-- smooth functions. -/
abbrev Sm (f : (Fin d → ℝ) → ℝ) : Prop := ContDiff ℝ (⊤ : ℕ∞) f

/-- `C_c^∞(ℝ^d)`. -/
def A₀ (d : ℕ) : NonUnitalSubalgebra ℝ ((Fin d → ℝ) → ℝ) where
  carrier := {f | ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f}
  add_mem' := fun {f g} (hf : ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g ∧ HasCompactSupport g) => ⟨hf.1.add hg.1, hf.2.add hg.2⟩
  zero_mem' := (⟨contDiff_const, HasCompactSupport.zero⟩ :
    ContDiff ℝ (⊤ : ℕ∞) (0 : (Fin d → ℝ) → ℝ) ∧ HasCompactSupport (0 : (Fin d → ℝ) → ℝ))
  mul_mem' := fun {f g} (hf : ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g ∧ HasCompactSupport g) => ⟨hf.1.mul hg.1, hf.2.mul_right⟩
  smul_mem' := fun c {f} (hf : ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f) =>
    ⟨hf.1.const_smul c, hf.2.smul_left⟩

/-- `C^∞(ℝ^d)`. -/
def A (d : ℕ) : Subalgebra ℝ ((Fin d → ℝ) → ℝ) where
  carrier := {f | ContDiff ℝ (⊤ : ℕ∞) f}
  add_mem' := fun {f g} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) => hf.add hg
  zero_mem' := (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (0 : (Fin d → ℝ) → ℝ))
  mul_mem' := fun {f g} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) => hf.mul hg
  algebraMap_mem' := fun r => (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : Fin d → ℝ => r))

lemma mem_A₀ {f : (Fin d → ℝ) → ℝ} : f ∈ A₀ d ↔ ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f := Iff.rfl
lemma mem_A {f : (Fin d → ℝ) → ℝ} : f ∈ A d ↔ ContDiff ℝ (⊤ : ℕ∞) f := Iff.rfl

lemma smooth {f : (Fin d → ℝ) → ℝ} (hf : f ∈ A₀ d) : Sm f := (mem_A₀.1 hf).1
lemma cs {f : (Fin d → ℝ) → ℝ} (hf : f ∈ A₀ d) : HasCompactSupport f := (mem_A₀.1 hf).2
lemma A₀_le_A {f : (Fin d → ℝ) → ℝ} (hf : f ∈ A₀ d) : f ∈ A d := smooth hf

/-- the partial derivative `∂ᵢ f`. -/
noncomputable def dd (i : Fin d) (f : (Fin d → ℝ) → ℝ) : (Fin d → ℝ) → ℝ :=
  fun x => fderiv ℝ f x (Pi.single i 1)

/-- `L f = Σᵢ ∂ᵢ² f` (the Laplacian). -/
noncomputable def Lf (f : (Fin d → ℝ) → ℝ) : (Fin d → ℝ) → ℝ := fun x => ∑ i, dd i (dd i f) x

/-- `Γ(f,g) = ∇f · ∇g`. -/
noncomputable def Gf (f g : (Fin d → ℝ) → ℝ) : (Fin d → ℝ) → ℝ := fun x => ∑ i, dd i f x * dd i g x

lemma Sm.dd {f : (Fin d → ℝ) → ℝ} (hf : Sm f) (i : Fin d) : Sm (dd i f) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

lemma cs_dd {f : (Fin d → ℝ) → ℝ} (hf : HasCompactSupport f) (i : Fin d) :
    HasCompactSupport (dd i f) :=
  hf.mono' ((subset_tsupport _).trans (tsupport_fderiv_apply_subset ℝ (Pi.single i 1)))

lemma dd_mem {f : (Fin d → ℝ) → ℝ} (hf : f ∈ A₀ d) (i : Fin d) : dd i f ∈ A₀ d :=
  mem_A₀.2 ⟨(smooth hf).dd i, cs_dd (cs hf) i⟩

lemma hasFDerivAt_of {f : (Fin d → ℝ) → ℝ} (hf : Sm f) (x : Fin d → ℝ) :
    HasFDerivAt f (fderiv ℝ f x) x :=
  ((hf.differentiable (by simp)) x).hasFDerivAt

lemma dd_mul {f g : (Fin d → ℝ) → ℝ} (hf : Sm f) (hg : Sm g) (i : Fin d) (x : Fin d → ℝ) :
    dd i (f * g) x = dd i f x * g x + f x * dd i g x := by
  have := ((hasFDerivAt_of hf x).mul (hasFDerivAt_of hg x)).fderiv
  unfold dd
  rw [this]
  simp
  ring

lemma dd_add {f g : (Fin d → ℝ) → ℝ} (hf : Sm f) (hg : Sm g) (i : Fin d) :
    dd i (f + g) = dd i f + dd i g := by
  funext x
  unfold dd
  rw [fderiv_add ((hf.differentiable (by simp)) x) ((hg.differentiable (by simp)) x)]
  rfl

lemma dd_smul (c : ℝ) {f : (Fin d → ℝ) → ℝ} (hf : Sm f) (i : Fin d) :
    dd i (c • f) = c • dd i f := by
  funext x
  unfold dd
  rw [fderiv_const_smul ((hf.differentiable (by simp)) x)]
  rfl

/-- Integration by parts in direction `i`, one compactly supported factor. -/
lemma ibp_cs {u v : (Fin d → ℝ) → ℝ} (hu : Sm u) (hv : Sm v)
    (hcs : HasCompactSupport u ∨ HasCompactSupport v) (i : Fin d) :
    ∫ x, u x * dd i v x = -∫ x, dd i u x * v x := by
  have h1 : Integrable (fun x => u x * dd i v x) := by
    refine (hu.continuous.mul (hv.dd i).continuous).integrable_of_hasCompactSupport ?_
    rcases hcs with h | h
    · exact h.mul_right
    · exact (cs_dd h i).mul_left
  have h2 : Integrable (fun x => dd i u x * v x) := by
    refine ((hu.dd i).continuous.mul hv.continuous).integrable_of_hasCompactSupport ?_
    rcases hcs with h | h
    · exact (cs_dd h i).mul_right
    · exact h.mul_left
  have h3 : Integrable (fun x => u x * v x) := by
    refine (hu.continuous.mul hv.continuous).integrable_of_hasCompactSupport ?_
    rcases hcs with h | h
    · exact h.mul_right
    · exact h.mul_left
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (v := Pi.single i 1) h2 h1 h3
    (fun x _ => (hu.differentiable (by simp)) x) (fun x _ => (hv.differentiable (by simp)) x)

lemma dd_const (c : ℝ) (i : Fin d) : dd i (fun _ : Fin d → ℝ => c) = 0 := by
  funext x; simp [dd]

lemma Gf_mem {f g : (Fin d → ℝ) → ℝ} (hf : f ∈ A₀ d) (hg : g ∈ A₀ d) : Gf f g ∈ A₀ d := by
  have : Gf f g = ∑ i, dd i f * dd i g := by funext x; simp [Gf]
  rw [this]
  exact sum_mem fun i _ => mul_mem (dd_mem hf i) (dd_mem hg i)

lemma Lf_mem {f : (Fin d → ℝ) → ℝ} (hf : f ∈ A₀ d) : Lf f ∈ A₀ d := by
  have : Lf f = ∑ i, dd i (dd i f) := by funext x; simp [Lf]
  rw [this]
  exact sum_mem fun i _ => dd_mem (dd_mem hf i) i

lemma integrable_of {f : (Fin d → ℝ) → ℝ} (hf : f ∈ A₀ d) : Integrable f :=
  (smooth hf).continuous.integrable_of_hasCompactSupport (cs hf)

lemma memLp_of {f : (Fin d → ℝ) → ℝ} (hf : f ∈ A₀ d) (p : ℝ≥0∞) : MemLp f p :=
  (smooth hf).continuous.memLp_of_hasCompactSupport (cs hf)

lemma ibp_L {f g : (Fin d → ℝ) → ℝ} (hf : Sm f) (hg : g ∈ A₀ d) :
    ∫ x, g x * Lf f x = -∫ x, Gf f g x := by
  have hint : ∀ i, Integrable (fun x => g x * dd i (dd i f) x) := fun i =>
    ((smooth hg).continuous.mul ((hf.dd i).dd i).continuous).integrable_of_hasCompactSupport
      (cs hg).mul_right
  have hint2 : ∀ i, Integrable (fun x => dd i f x * dd i g x) := fun i =>
    ((hf.dd i).continuous.mul ((smooth hg).dd i).continuous).integrable_of_hasCompactSupport
      (cs_dd (cs hg) i).mul_left
  have e1 : (fun x => g x * Lf f x) = fun x => ∑ i, g x * dd i (dd i f) x := by
    funext x; simp [Lf, Finset.mul_sum]
  have e2 : (fun x => Gf f g x) = fun x => ∑ i, dd i f x * dd i g x := rfl
  rw [e1, e2, integral_finsetSum _ (fun i _ => hint i), integral_finsetSum _ (fun i _ => hint2 i),
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ibp_cs (smooth hg) (hf.dd i) (Or.inl (cs hg)) i]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only; ring

lemma integral_Lf {f : (Fin d → ℝ) → ℝ} (hf : f ∈ A₀ d) : ∫ x, Lf f x = 0 := by
  have hint : ∀ i, Integrable (fun x => dd i (dd i f) x) := fun i =>
    integrable_of (dd_mem (dd_mem hf i) i)
  have e1 : (fun x => Lf f x) = fun x => ∑ i, dd i (dd i f) x := rfl
  rw [e1, integral_finsetSum _ (fun i _ => hint i)]
  refine Finset.sum_eq_zero fun i _ => ?_
  have h := ibp_cs (d := d) (u := fun _ => (1 : ℝ)) (v := dd i f) contDiff_const
    ((smooth hf).dd i) (Or.inr (cs_dd (cs hf) i)) i
  simpa [dd_const] using h

/-! ### Chain rule -/

lemma dd_comp {k : ℕ} (ψ : (Fin k → ℝ) → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (f : Fin k → (Fin d → ℝ) → ℝ) (hf : ∀ j, Sm (f j)) (i : Fin d) (x : Fin d → ℝ) :
    dd i (fun y => ψ (fun j => f j y)) x =
      ∑ j, MarkovTriple.BGL.pderiv ψ j (fun l => f l x) * dd i (f j) x := by
  have hF : HasFDerivAt (fun y => fun j => f j y)
      (ContinuousLinearMap.pi fun j => fderiv ℝ (f j) x) x :=
    hasFDerivAt_pi'.2 fun j => hasFDerivAt_of (hf j) x
  have hψd : HasFDerivAt ψ (fderiv ℝ ψ (fun l => f l x)) (fun l => f l x) :=
    ((hψ.differentiable (by simp)) _).hasFDerivAt
  have h := hψd.comp x hF
  have h2 : fderiv ℝ (fun y => ψ fun j => f j y) x = _ := h.fderiv
  unfold dd
  rw [h2]
  simp only [ContinuousLinearMap.comp_apply]
  rw [MarkovTriple.BGL.Lebesgue.clm_pi_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [ContinuousLinearMap.pi_apply, MarkovTriple.BGL.pderiv]
  ring

lemma comp_sm {k : ℕ} (ψ : (Fin k → ℝ) → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (f : Fin k → (Fin d → ℝ) → ℝ) (hf : ∀ i, Sm (f i)) : Sm (fun x => ψ (fun i => f i x)) :=
  hψ.comp (contDiff_pi.2 hf)

lemma comp_mem_A₀ (k : ℕ) (ψ : (Fin k → ℝ) → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (h0 : ψ 0 = 0)
    (f : Fin k → (Fin d → ℝ) → ℝ) (hf : ∀ i, f i ∈ A₀ d) :
    (fun x => ψ (fun i => f i x)) ∈ A₀ d := by
  refine mem_A₀.2 ⟨comp_sm ψ hψ f (fun i => smooth (hf i)), ?_⟩
  refine HasCompactSupport.intro (K := ⋃ i, tsupport (f i))
    (isCompact_iUnion fun i => (cs (hf i))) fun x hx => ?_
  have : ∀ i, f i x = 0 := fun i =>
    image_eq_zero_of_notMem_tsupport (fun h => hx (Set.mem_iUnion.2 ⟨i, h⟩))
  have e : (fun i => f i x) = 0 := funext this
  simp only [e, h0]

lemma Gf_comp {k : ℕ} (ψ : (Fin k → ℝ) → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (f : Fin k → (Fin d → ℝ) → ℝ) (hf : ∀ i, Sm (f i)) (g : (Fin d → ℝ) → ℝ) :
    Gf (fun x => ψ (fun i => f i x)) g =
      fun x => ∑ j, MarkovTriple.BGL.pderiv ψ j (fun l => f l x) * Gf (f j) g x := by
  funext x
  simp only [Gf, dd_comp ψ hψ f hf, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

lemma dense_Lp (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    Dense {u : Lp ℝ p (volume : Measure (Fin d → ℝ)) | ∃ f ∈ A₀ d, (u : (Fin d → ℝ) → ℝ) =ᵐ[volume] f} := by
  refine (Lp.dense_hasCompactSupport_contDiff (F := ℝ) (μ := (volume : Measure (Fin d → ℝ))) hp).mono ?_
  rintro u ⟨g, hug, hcs, hcd⟩
  exact ⟨g, mem_A₀.2 ⟨hcd, hcs⟩, hug⟩

/-! ### Cutoff sequence -/

/-- `|x|²`. -/
noncomputable def sq (x : Fin d → ℝ) : ℝ := ∑ i, x i ^ 2

lemma sq_nonneg' (x : Fin d → ℝ) : 0 ≤ sq x := Finset.sum_nonneg fun i _ => by positivity

lemma sq_smooth : Sm (sq : (Fin d → ℝ) → ℝ) :=
  ContDiff.sum fun i _ => ((contDiff_apply ℝ ℝ i).pow 2)

noncomputable def cut (n : ℕ) : (Fin d → ℝ) → ℝ :=
  fun x => Real.smoothTransition (2 - sq x / ((n : ℝ) + 1) ^ 2)

lemma cut_smooth (n : ℕ) : Sm (cut n : (Fin d → ℝ) → ℝ) :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub (sq_smooth.div_const _))

lemma cut_cs (n : ℕ) : HasCompactSupport (cut n : (Fin d → ℝ) → ℝ) := by
  refine HasCompactSupport.intro (K := Metric.closedBall 0 (2 * ((n : ℝ) + 1)))
    (isCompact_closedBall _ _) fun x hx => ?_
  unfold cut
  apply Real.smoothTransition.zero_of_nonpos
  rw [Metric.mem_closedBall, dist_zero_right] at hx
  have hn : (0 : ℝ) < ((n : ℝ) + 1) := by positivity
  have : ∃ i, 2 * ((n : ℝ) + 1) < |x i| := by
    by_contra h
    push Not at h
    exact hx ((pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => by simpa using h i)
  obtain ⟨i, hi⟩ := this
  have h1 : x i ^ 2 ≤ sq x :=
    Finset.single_le_sum (f := fun i => x i ^ 2) (fun j _ => by positivity) (Finset.mem_univ i)
  have h2 : (2 * ((n : ℝ) + 1)) ^ 2 < x i ^ 2 := by
    rw [← sq_abs (x i)]; exact pow_lt_pow_left₀ hi (by positivity) (by norm_num)
  have h3 : 4 * ((n : ℝ) + 1) ^ 2 < sq x := by nlinarith
  have h4 : 4 ≤ sq x / ((n : ℝ) + 1) ^ 2 := by
    rw [le_div_iff₀ (by positivity)]; linarith
  linarith

lemma cut_mem (n : ℕ) : (cut n : (Fin d → ℝ) → ℝ) ∈ A₀ d := mem_A₀.2 ⟨cut_smooth n, cut_cs n⟩

lemma cut_mono (n : ℕ) (x : Fin d → ℝ) : cut n x ≤ cut (n + 1) x := by
  unfold cut
  apply Real.smoothTransition.monotone
  have h1 : ((n : ℝ) + 1) ^ 2 ≤ (((n + 1 : ℕ) : ℝ) + 1) ^ 2 := by
    push_cast; nlinarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  have h2 : sq x / (((n + 1 : ℕ) : ℝ) + 1) ^ 2 ≤ sq x / ((n : ℝ) + 1) ^ 2 :=
    div_le_div_of_nonneg_left (sq_nonneg' x) (by positivity) h1
  linarith

lemma cut_nonneg (n : ℕ) (x : Fin d → ℝ) : 0 ≤ cut n x := Real.smoothTransition.nonneg _

lemma cut_tendsto (x : Fin d → ℝ) : Tendsto (fun n => cut n x) atTop (𝓝 1) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop (⌈sq x⌉₊)] with n hn
  unfold cut
  symm
  apply Real.smoothTransition.one_of_one_le
  have h1 : sq x ≤ (n : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hn)
  have h2 : sq x / ((n : ℝ) + 1) ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]; nlinarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  linarith

lemma cut_exhaustion : MarkovTriple.BGL.IsExhaustion (volume : Measure (Fin d → ℝ)) (A₀ d) cut :=
  ⟨cut_mem, fun n => Filter.Eventually.of_forall (cut_mono n),
    Filter.Eventually.of_forall cut_tendsto⟩

lemma not_isFiniteMeasure (hd : 1 ≤ d) : ¬ IsFiniteMeasure (volume : Measure (Fin d → ℝ)) := fun h => by
  have h1 := h.measure_univ_lt_top
  rw [volume_pi, Measure.pi_univ] at h1
  have : ∏ i : Fin d, (volume : Measure ℝ) Set.univ = ⊤ := by
    simp only [Real.volume_univ, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact ENNReal.top_pow (by omega)
  rw [this] at h1
  exact lt_irrefl _ h1

/-- **The Brownian triple on `(ℝ^d, Lebesgue)`** (`d ≥ 1`): `𝒜₀ = C_c^∞`, `L = Δ`, `Γ = ∇f·∇g`. -/
@[reducible] noncomputable def lebesgueRdDiffusion (d : ℕ) (hd : 1 ≤ d) :
    MarkovTriple.BGL.DiffusionTriple (Fin d → ℝ) where
  μ := volume
  sigmaFinite := inferInstance
  finite_prob := fun h => absurd h (not_isFiniteMeasure hd)
  A₀ := A₀ d
  measurable := fun f hf => (smooth hf).continuous.measurable
  bounded := fun f hf => by
    obtain ⟨C, hC⟩ := (smooth hf).continuous.bounded_above_of_compact_support (cs hf)
    exact ⟨C, fun x => by simpa using hC x⟩
  memLp := fun f hf p _ _ => memLp_of hf p
  dense := fun p hp hp' => by
    have := hp
    exact dense_Lp p hp'
  comp_mem := fun k ψ hψ h0 f hf => comp_mem_A₀ k ψ hψ h0 f hf
  exhaustion := ⟨cut, cut_exhaustion⟩
  Γ := Gf
  L := Lf
  Γ_mem := fun f hf g hg => Gf_mem hf hg
  L_mem := fun f hf => Lf_mem hf
  Γ_symm := fun f _ g _ => Filter.Eventually.of_forall fun x => by
    simp [Gf, mul_comm]
  Γ_add := fun f hf f' hf' g _ => Filter.Eventually.of_forall fun x => by
    simp [Gf, dd_add (smooth hf) (smooth hf'), add_mul, Finset.sum_add_distrib]
  Γ_smul := fun c f hf g _ => Filter.Eventually.of_forall fun x => by
    simp [Gf, dd_smul c (smooth hf), mul_assoc, Finset.mul_sum]
  Γ_nonneg := fun f _ => Filter.Eventually.of_forall fun x => by
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  diffusion := fun k ψ hψ _ f hf g _ =>
    Filter.Eventually.of_forall fun x => by
      have := congrFun (Gf_comp ψ hψ f (fun i => smooth (hf i)) g) x
      simpa using this
  ibp := fun f hf g hg => ibp_L (smooth hf) hg
  integral_L := fun f hf => integral_Lf hf

theorem lebesgueRd_L_eq (hd : 1 ≤ d) : (lebesgueRdDiffusion d hd).L = Lf := rfl
theorem lebesgueRd_Γ_eq (hd : 1 ≤ d) : (lebesgueRdDiffusion d hd).Γ = Gf := rfl
theorem lebesgueRd_μ_eq (hd : 1 ≤ d) : (lebesgueRdDiffusion d hd).μ = volume := rfl

end MarkovTriple.BGL.LebesgueRd
