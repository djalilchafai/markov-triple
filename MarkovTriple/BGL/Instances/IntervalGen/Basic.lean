import Mathlib
import MarkovTriple.BGL.Instances.Interval.Diffusion

/-!
# Bounded open subsets of `ℝ`: the algebra `𝒜₀ = C_c^∞(Ω)`, cut-offs and density

State space `ℝ`, `μ = |Ω|⁻¹ · volume.restrict Ω`; `𝒜₀ = {f smooth, tsupport f ⊆ Ω}`.
See `STATEMENTS_R22_E1.md`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace MarkovTriple.BGL.Instances.IntervalGen


/-- a bounded nonempty open subset of `ℝ`. -/
structure BddOpen where
  carrier : Set ℝ
  isOpen : IsOpen carrier
  isBounded : Bornology.IsBounded carrier
  nonempty : carrier.Nonempty

namespace BddOpen

/-- the interval `(a,b)`. -/
def Ioo (a b : ℝ) (h : a < b) : BddOpen where
  carrier := Set.Ioo a b
  isOpen := isOpen_Ioo
  isBounded := Metric.isBounded_Ioo a b
  nonempty := Set.nonempty_Ioo.2 h

variable (Ω : BddOpen)

lemma compl_nonempty : (Ω.carrierᶜ).Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty, compl_empty_iff] at h
  have := Ω.isBounded
  rw [h] at this
  exact (NormedSpace.unbounded_univ ℝ ℝ) this

lemma vol_pos : 0 < volume Ω.carrier := Ω.isOpen.measure_pos volume Ω.nonempty

lemma vol_lt_top : volume Ω.carrier < ∞ := Ω.isBounded.measure_lt_top

/-- normalised Lebesgue measure on `Ω`. -/
noncomputable abbrev μ : Measure ℝ := (volume Ω.carrier)⁻¹ • volume.restrict Ω.carrier

instance isProb_μ : IsProbabilityMeasure Ω.μ :=
  ⟨by
    simp only [Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
    exact ENNReal.inv_mul_cancel Ω.vol_pos.ne' Ω.vol_lt_top.ne⟩

lemma ae_μ_iff {P : ℝ → Prop} :
    (∀ᵐ x ∂Ω.μ, P x) ↔ ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Ω.carrier → P x := by
  rw [← ae_restrict_iff' Ω.isOpen.measurableSet]
  have : (volume Ω.carrier)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 Ω.vol_lt_top.ne
  simp only [ae_iff, Measure.smul_apply, smul_eq_mul, mul_eq_zero, this, false_or]

/-- integrals of functions vanishing off `Ω` over `μ` and over `volume`, up to the normalising constant. -/
lemma integral_μ {h : ℝ → ℝ} (hh : ∀ x ∉ Ω.carrier, h x = 0) :
    ∫ x, h x ∂Ω.μ = ((volume Ω.carrier)⁻¹).toReal * ∫ x, h x := by
  rw [integral_smul_measure, smul_eq_mul,
    setIntegral_eq_integral_of_forall_compl_eq_zero hh]

/-- `C_c^∞(Ω)`: smooth functions whose topological support lies in `Ω`. -/
def A₀ : NonUnitalSubalgebra ℝ (ℝ → ℝ) where
  carrier := {f | Lebesgue.Sm f ∧ tsupport f ⊆ Ω.carrier}
  add_mem' := fun {f g} hf hg =>
    ⟨hf.1.add hg.1, Interval.tsupport_add_sub.trans (union_subset hf.2 hg.2)⟩
  zero_mem' := ⟨contDiff_const, by simp⟩
  mul_mem' := fun {f g} hf hg => ⟨hf.1.mul hg.1, tsupport_mul_subset_left.trans hf.2⟩
  smul_mem' := fun c {f} hf =>
    ⟨hf.1.const_smul c, (tsupport_smul_subset_right (fun _ => c) f).trans hf.2⟩

lemma mem_A₀ {f : ℝ → ℝ} : f ∈ Ω.A₀ ↔ Lebesgue.Sm f ∧ tsupport f ⊆ Ω.carrier := Iff.rfl

variable {Ω}

lemma A₀_smooth {f : ℝ → ℝ} (hf : f ∈ Ω.A₀) : Lebesgue.Sm f := hf.1

lemma A₀_cs {f : ℝ → ℝ} (hf : f ∈ Ω.A₀) : HasCompactSupport f :=
  IsCompact.of_isClosed_subset Ω.isBounded.isCompact_closure (isClosed_tsupport f)
    (hf.2.trans subset_closure)

lemma A₀_le {f : ℝ → ℝ} (hf : f ∈ Ω.A₀) : f ∈ Lebesgue.A₀ :=
  Lebesgue.mem_A₀.2 ⟨hf.1, A₀_cs hf⟩

lemma deriv_mem_A₀ {f : ℝ → ℝ} (hf : f ∈ Ω.A₀) : deriv f ∈ Ω.A₀ :=
  ⟨hf.1.deriv', (tsupport_deriv_subset (f := f)).trans hf.2⟩

lemma zero_off {f : ℝ → ℝ} (hf : f ∈ Ω.A₀) {x : ℝ} (hx : x ∉ Ω.carrier) : f x = 0 :=
  image_eq_zero_of_notMem_tsupport (fun h => hx (hf.2 h))

lemma comp_mem_A₀ (k : ℕ) (ψ : (Fin k → ℝ) → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (h0 : ψ 0 = 0)
    (f : Fin k → ℝ → ℝ) (hf : ∀ i, f i ∈ Ω.A₀) : (fun x => ψ (fun i => f i x)) ∈ Ω.A₀ := by
  refine ⟨Lebesgue.comp_sm ψ hψ f (fun i => (hf i).1), ?_⟩
  have hsub : Function.support (fun x => ψ (fun i => f i x)) ⊆ ⋃ i, tsupport (f i) := by
    intro x hx
    by_contra hxx
    apply hx
    have : ∀ i, f i x = 0 := fun i =>
      image_eq_zero_of_notMem_tsupport (fun h => hxx (Set.mem_iUnion.2 ⟨i, h⟩))
    have e : (fun i => f i x) = 0 := funext this
    simp only [e, h0]
  refine (closure_minimal hsub (isClosed_iUnion_of_finite fun i => isClosed_tsupport _)).trans ?_
  exact iUnion_subset fun i => (hf i).2

variable (Ω)

/-! ### The exhaustion sequence -/

/-- `K n = {x | 1/(n+1) ≤ dist(x, Ωᶜ)}`: closed, contained in `Ω`. -/
def K (n : ℕ) : Set ℝ := {x | 1 / ((n : ℝ) + 1) ≤ Metric.infDist x Ω.carrierᶜ}

lemma isClosed_K (n : ℕ) : IsClosed (Ω.K n) :=
  isClosed_le continuous_const (Metric.continuous_infDist_pt _)

lemma K_subset (n : ℕ) : Ω.K n ⊆ Ω.carrier := by
  intro x hx
  by_contra h
  have h0 : Metric.infDist x Ω.carrierᶜ = 0 := Metric.infDist_zero_of_mem h
  have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  have hx' : 1 / ((n : ℝ) + 1) ≤ Metric.infDist x Ω.carrierᶜ := hx
  linarith

lemma exists_cut (n : ℕ) : ∃ θ : ℝ → ℝ, Lebesgue.Sm θ ∧ (∀ x, 0 ≤ θ x ∧ θ x ≤ 1) ∧
    (∀ x ∈ Ω.K n, θ x = 1) ∧ Function.support θ ⊆ Ω.K (n + 1) ∧ tsupport θ ⊆ Ω.K (n + 1) := by
  have hn2 : ((n + 1 : ℕ) : ℝ) + 1 = (n : ℝ) + 2 := by push_cast; ring
  have hlt : 1 / ((n : ℝ) + 2) < 1 / ((n : ℝ) + 1) :=
    one_div_lt_one_div_of_lt (by positivity) (by linarith)
  obtain ⟨f, hf, hr, hs, ht⟩ := exists_contDiff_zero_iff_one_iff_of_isClosed
    (n := (⊤ : ℕ∞)) (E := ℝ)
    (s := {x | Metric.infDist x Ω.carrierᶜ ≤ 1 / ((n : ℝ) + 2)}) (t := Ω.K n)
    (isClosed_le (Metric.continuous_infDist_pt _) continuous_const) (Ω.isClosed_K n)
    (Set.disjoint_left.2 fun x hx1 hx2 => by
      have hx2' : 1 / ((n : ℝ) + 1) ≤ Metric.infDist x Ω.carrierᶜ := hx2
      have hx1' : Metric.infDist x Ω.carrierᶜ ≤ 1 / ((n : ℝ) + 2) := hx1
      linarith)
  have hsupp : Function.support f ⊆ Ω.K (n + 1) := by
    intro x hx
    have hxs : x ∉ {x | Metric.infDist x Ω.carrierᶜ ≤ 1 / ((n : ℝ) + 2)} := fun h => hx ((hs x).1 h)
    have : 1 / ((n : ℝ) + 2) < Metric.infDist x Ω.carrierᶜ := not_le.1 hxs
    show 1 / (((n + 1 : ℕ) : ℝ) + 1) ≤ Metric.infDist x Ω.carrierᶜ
    rw [hn2]; exact this.le
  exact ⟨f, hf, fun x => ⟨(hr ⟨x, rfl⟩).1, (hr ⟨x, rfl⟩).2⟩, fun x hx => (ht x).1 hx, hsupp,
    closure_minimal hsupp (Ω.isClosed_K _)⟩

/-- the cut-off sequence. -/
noncomputable def cut (n : ℕ) : ℝ → ℝ := Classical.choose (Ω.exists_cut n)

lemma cut_smooth (n : ℕ) : Lebesgue.Sm (Ω.cut n) := (Classical.choose_spec (Ω.exists_cut n)).1

lemma cut_range (n : ℕ) (x : ℝ) : 0 ≤ Ω.cut n x ∧ Ω.cut n x ≤ 1 :=
  (Classical.choose_spec (Ω.exists_cut n)).2.1 x

lemma cut_eq_one {n : ℕ} {x : ℝ} (hx : x ∈ Ω.K n) : Ω.cut n x = 1 :=
  (Classical.choose_spec (Ω.exists_cut n)).2.2.1 x hx

lemma cut_support (n : ℕ) : Function.support (Ω.cut n) ⊆ Ω.K (n + 1) :=
  (Classical.choose_spec (Ω.exists_cut n)).2.2.2.1

lemma cut_tsupport (n : ℕ) : tsupport (Ω.cut n) ⊆ Ω.carrier :=
  ((Classical.choose_spec (Ω.exists_cut n)).2.2.2.2).trans (Ω.K_subset _)

lemma cut_mem (n : ℕ) : Ω.cut n ∈ Ω.A₀ := ⟨Ω.cut_smooth n, Ω.cut_tsupport n⟩

lemma cut_mono (n : ℕ) (x : ℝ) : Ω.cut n x ≤ Ω.cut (n + 1) x := by
  by_cases hx : x ∈ Function.support (Ω.cut n)
  · rw [Ω.cut_eq_one (Ω.cut_support n hx)]
    exact (Ω.cut_range n x).2
  · rw [Function.notMem_support.1 hx]; exact (Ω.cut_range _ x).1

lemma pos_dist {x : ℝ} (hx : x ∈ Ω.carrier) : 0 < Metric.infDist x Ω.carrierᶜ :=
  (Ω.isOpen.isClosed_compl.notMem_iff_infDist_pos Ω.compl_nonempty).1 (not_not.2 hx)

lemma cut_tendsto {x : ℝ} (hx : x ∈ Ω.carrier) : Tendsto (fun n => Ω.cut n x) atTop (𝓝 1) := by
  refine tendsto_const_nhds.congr' ?_
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt (Ω.pos_dist hx)
  filter_upwards [eventually_ge_atTop N] with n hn
  refine (Ω.cut_eq_one (n := n) ?_).symm
  show 1 / ((n : ℝ) + 1) ≤ _
  refine le_trans ?_ hN.le
  exact one_div_le_one_div_of_le (by positivity) (by have : (N : ℝ) ≤ n := by exact_mod_cast hn
                                                     linarith)

end BddOpen

end MarkovTriple.BGL.Instances.IntervalGen
