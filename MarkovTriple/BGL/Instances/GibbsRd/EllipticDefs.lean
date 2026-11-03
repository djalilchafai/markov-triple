import Mathlib
import MarkovTriple.BGL.Instances.GibbsRd.Calculus

/-!
# Weak derivatives and the local Sobolev predicate `Sobolev k` on `ℝ^d` (R16, elliptic half)

Statements: `STATEMENTS_R16_Elliptic.md` (D1–D3, B1–B6).  Textbook: Evans PDE §5.2.1 (weak derivatives), Thm 1 (uniqueness).

`WeakDeriv f g i` is the shared definition with the Sobolev agent, with ONE correction (erratum R16-E1): the test functions
are `C^∞` (`ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ`, Mathlib's `∞`), not `ContDiff ℝ ⊤ φ` which in current Mathlib is
real-ANALYTIC (`⊤ : WithTop ℕ∞` is `ω`) — compactly supported analytic functions vanish, so that text is vacuous.
-/

open MeasureTheory

namespace MarkovTriple.BGL.Instances.GibbsRd.Elliptic

open MarkovTriple.BGL (pderiv)

/-- `g = ∂ᵢ f` in the weak (distributional) sense, with `f, g` locally integrable (Lebesgue measure). -/
def WeakDeriv {d : ℕ} (f g : (Fin d → ℝ) → ℝ) (i : Fin d) : Prop :=
  MeasureTheory.LocallyIntegrable f ∧ MeasureTheory.LocallyIntegrable g ∧
    ∀ φ : (Fin d → ℝ) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
      ∫ x, f x * (fderiv ℝ φ x (Pi.single i 1)) = - ∫ x, g x * φ x

/-- `f ∈ L²_loc(ℝ^d)`: square integrable on every compact set. -/
def LocL2 {d : ℕ} (f : (Fin d → ℝ) → ℝ) : Prop :=
  ∀ K : Set (Fin d → ℝ), IsCompact K → MemLp f 2 (volume.restrict K)

/-- `f ∈ H^k_loc(ℝ^d)`: `f ∈ L²_loc` and all iterated weak partial derivatives up to order `k` exist and are `L²_loc`. -/
def Sobolev {d : ℕ} : ℕ → ((Fin d → ℝ) → ℝ) → Prop
  | 0, f => LocL2 f
  | k + 1, f => LocL2 f ∧ ∀ i : Fin d, ∃ g : (Fin d → ℝ) → ℝ, WeakDeriv f g i ∧ Sobolev k g

variable {d : ℕ}

lemma LocL2.locallyIntegrable {f : (Fin d → ℝ) → ℝ} (hf : LocL2 f) : LocallyIntegrable f := by
  rw [locallyIntegrable_iff]
  intro K hK
  have : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hK.measure_lt_top⟩
  exact (hf K hK).integrable (by norm_num)

lemma WeakDeriv.left {f g : (Fin d → ℝ) → ℝ} {i : Fin d} (h : WeakDeriv f g i) : LocallyIntegrable f := h.1
lemma WeakDeriv.right {f g : (Fin d → ℝ) → ℝ} {i : Fin d} (h : WeakDeriv f g i) : LocallyIntegrable g := h.2.1

/-- `f * c` is integrable for locally integrable `f` and continuous compactly supported `c`. -/
lemma integrable_mul_cs {f c : (Fin d → ℝ) → ℝ} (hf : LocallyIntegrable f) (hc : Continuous c)
    (hs : HasCompactSupport c) : Integrable (fun x => f x * c x) := by
  have := hf.integrable_smul_left_of_hasCompactSupport hc hs
  simpa [smul_eq_mul, mul_comm] using this

/-- **B2** uniqueness of the weak derivative (fundamental lemma of the calculus of variations, in Mathlib). -/
theorem WeakDeriv.unique {f g g' : (Fin d → ℝ) → ℝ} {i : Fin d} (h : WeakDeriv f g i) (h' : WeakDeriv f g' i) :
    g =ᵐ[volume] g' := by
  have := ae_eq_of_integral_contDiff_smul_eq (μ := (volume : Measure (Fin d → ℝ))) h.2.1 h'.2.1 (fun φ hφ hs => by
    have e1 := h.2.2 φ hφ hs
    have e2 := h'.2.2 φ hφ hs
    simp only [smul_eq_mul, mul_comm (φ _)]
    linarith)
  filter_upwards [this] with x hx using hx

/-- integration by parts against a smooth compactly supported test function -/
lemma ibp_smooth {ψ φ : (Fin d → ℝ) → ℝ} (hψ : Sm ψ) (hφ : Sm φ) (hc : HasCompactSupport φ) (i : Fin d) :
    ∫ x, ψ x * pderiv φ i x = - ∫ x, pderiv ψ i x * φ x := by
  have h0 := integral_pderiv_eq_zero (f := ψ * φ) (hψ.mul hφ) (hc.mul_left) i
  have hI1 : Integrable (fun x => pderiv ψ i x * φ x) :=
    ((hψ.pderiv i).continuous.mul hφ.continuous).integrable_of_hasCompactSupport hc.mul_left
  have hI2 : Integrable (fun x => ψ x * pderiv φ i x) :=
    (hψ.continuous.mul (hφ.pderiv i).continuous).integrable_of_hasCompactSupport
      (hc.fderiv_apply ℝ (Pi.single i 1)).mul_left
  have e : ∀ x, pderiv (ψ * φ) i x = pderiv ψ i x * φ x + ψ x * pderiv φ i x := fun x => pderiv_mul hψ hφ i x
  simp only [e] at h0
  rw [integral_add hI1 hI2] at h0
  linarith

/-- **B3** smooth functions have their classical derivative as weak derivative. -/
theorem weakDeriv_of_smooth {f : (Fin d → ℝ) → ℝ} (hf : Sm f) (i : Fin d) : WeakDeriv f (pderiv f i) i :=
  ⟨hf.continuous.locallyIntegrable, ((hf.pderiv i).continuous).locallyIntegrable, fun _ hφ hs =>
    ibp_smooth hf hφ hs i⟩

theorem WeakDeriv.add {f g f' g' : (Fin d → ℝ) → ℝ} {i : Fin d} (h : WeakDeriv f g i) (h' : WeakDeriv f' g' i) :
    WeakDeriv (f + f') (g + g') i := by
  refine ⟨h.1.add h'.1, h.2.1.add h'.2.1, fun φ hφ hs => ?_⟩
  have hd : Continuous (fun x => fderiv ℝ φ x (Pi.single i 1)) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdc : HasCompactSupport (fun x => fderiv ℝ φ x (Pi.single i 1)) := hs.fderiv_apply ℝ (Pi.single i 1)
  have hc := hφ.continuous
  have := h.2.2 φ hφ hs
  have := h'.2.2 φ hφ hs
  simp only [Pi.add_apply, add_mul]
  rw [integral_add (integrable_mul_cs h.1 hd hdc) (integrable_mul_cs h'.1 hd hdc),
    integral_add (integrable_mul_cs h.2.1 hc hs) (integrable_mul_cs h'.2.1 hc hs)]
  linarith

theorem WeakDeriv.const_mul {f g : (Fin d → ℝ) → ℝ} {i : Fin d} (c : ℝ) (h : WeakDeriv f g i) :
    WeakDeriv (fun x => c * f x) (fun x => c * g x) i := by
  refine ⟨?_, ?_, fun φ hφ hs => ?_⟩
  · exact h.1.smul c
  · exact h.2.1.smul c
  · have := h.2.2 φ hφ hs
    have e1 : ∫ x, c * f x * fderiv ℝ φ x (Pi.single i 1) = c * ∫ x, f x * fderiv ℝ φ x (Pi.single i 1) := by
      rw [← integral_const_mul]; exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
    have e2 : ∫ x, c * g x * φ x = c * ∫ x, g x * φ x := by
      rw [← integral_const_mul]; exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
    rw [e1, e2, this]; ring

/-- **B5** product rule with a smooth function. -/
theorem WeakDeriv.smooth_mul {f g : (Fin d → ℝ) → ℝ} {i : Fin d} {ψ : (Fin d → ℝ) → ℝ} (hψ : Sm ψ)
    (h : WeakDeriv f g i) :
    WeakDeriv (fun x => ψ x * f x) (fun x => ψ x * g x + pderiv ψ i x * f x) i := by
  have hψc := hψ.continuous
  have hpc := (hψ.pderiv i).continuous
  have loc : ∀ {u : (Fin d → ℝ) → ℝ} {c : (Fin d → ℝ) → ℝ}, LocallyIntegrable u → Continuous c →
      LocallyIntegrable (fun x => c x * u x) := by
    intro u c hu hc
    rw [locallyIntegrable_iff]
    intro K hK
    exact (hu.integrableOn_isCompact hK).continuousOn_mul hc.continuousOn hK
  refine ⟨loc h.1 hψc, (loc h.2.1 hψc).add (loc h.1 hpc), fun φ hφ hs => ?_⟩
  have hφS : Sm φ := hφ
  have hψφ : Sm (ψ * φ) := hψ.mul hφS
  have key := h.2.2 (ψ * φ) hψφ hs.mul_left
  have hd : Continuous (fun x => fderiv ℝ φ x (Pi.single i 1)) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdc : HasCompactSupport (fun x => fderiv ℝ φ x (Pi.single i 1)) := hs.fderiv_apply ℝ (Pi.single i 1)
  have e : ∀ x, fderiv ℝ (ψ * φ) x (Pi.single i 1) = pderiv ψ i x * φ x + ψ x * fderiv ℝ φ x (Pi.single i 1) :=
    fun x => pderiv_mul hψ hφS i x
  simp only [e] at key
  have hI1 := integrable_mul_cs h.1 (hpc.mul hφS.continuous) hs.mul_left
  have hI2 := integrable_mul_cs h.1 (hψc.mul hd) hdc.mul_left
  have hI3 := integrable_mul_cs h.2.1 (hψc.mul hφS.continuous) hs.mul_left
  have hI4 := integrable_mul_cs h.1 hφS.continuous hs
  have hI5 := integrable_mul_cs (loc h.1 hpc) hφS.continuous hs
  have hI6 := integrable_mul_cs (loc h.2.1 hψc) hφS.continuous hs
  have e1 : ∫ x, f x * (pderiv ψ i x * φ x + ψ x * fderiv ℝ φ x (Pi.single i 1)) =
      (∫ x, (pderiv ψ i x * f x) * φ x) + ∫ x, (ψ x * f x) * fderiv ℝ φ x (Pi.single i 1) := by
    rw [← integral_add]
    · exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
    · exact (hI5)
    · exact (integrable_mul_cs (loc h.1 hψc) hd hdc)
  have e2 : ∫ x, (ψ x * g x + pderiv ψ i x * f x) * φ x =
      (∫ x, g x * (ψ x * φ x)) + ∫ x, (pderiv ψ i x * f x) * φ x := by
    rw [← integral_add]
    · exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
    · exact (hI3)
    · exact hI5
  rw [e2]
  simp only [Pi.mul_apply] at key
  beta_reduce
  linarith

/-! ### B6: closure properties of `LocL2` and `Sobolev` -/

lemma LocL2.mul_continuous {f c : (Fin d → ℝ) → ℝ} (hf : LocL2 f) (hc : Continuous c) :
    LocL2 (fun x => c x * f x) := by
  intro K hK
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  refine (hf K hK).of_le_mul (c := max C 0) (hc.aestronglyMeasurable.mul (hf K hK).aestronglyMeasurable) ?_
  refine (ae_restrict_iff' hK.measurableSet).2 (Filter.Eventually.of_forall fun x hx => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right ((hC x hx).trans (le_max_left _ _)) (norm_nonneg _)

lemma LocL2.add {f g : (Fin d → ℝ) → ℝ} (hf : LocL2 f) (hg : LocL2 g) : LocL2 (fun x => f x + g x) :=
  fun K hK => (hf K hK).add (hg K hK)

lemma LocL2.of_smooth {f : (Fin d → ℝ) → ℝ} (hf : Sm f) : LocL2 f := by
  have h1 : LocL2 (fun _ : Fin d → ℝ => (1 : ℝ)) := fun K hK => by
    have : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hK.measure_lt_top⟩
    exact memLp_const 1
  simpa using h1.mul_continuous hf.continuous

lemma Sobolev.locL2 : ∀ {k : ℕ} {f : (Fin d → ℝ) → ℝ}, Sobolev k f → LocL2 f
  | 0, _, h => h
  | _ + 1, _, h => h.1

lemma Sobolev.mono : ∀ {k : ℕ} {f : (Fin d → ℝ) → ℝ}, Sobolev (k + 1) f → Sobolev k f
  | 0, _, h => h.1
  | k + 1, _, h => ⟨h.1, fun i => by
      obtain ⟨g, hg, hS⟩ := h.2 i
      exact ⟨g, hg, Sobolev.mono hS⟩⟩

lemma Sobolev.add : ∀ {k : ℕ} {f g : (Fin d → ℝ) → ℝ}, Sobolev k f → Sobolev k g →
    Sobolev k (fun x => f x + g x)
  | 0, _, _, hf, hg => LocL2.add hf hg
  | k + 1, _, _, hf, hg => ⟨LocL2.add hf.1 hg.1, fun i => by
      obtain ⟨a, ha, hSa⟩ := hf.2 i
      obtain ⟨b, hb, hSb⟩ := hg.2 i
      exact ⟨fun x => a x + b x, ha.add hb, Sobolev.add hSa hSb⟩⟩

lemma Sobolev.of_smooth : ∀ (k : ℕ) {f : (Fin d → ℝ) → ℝ}, Sm f → Sobolev k f
  | 0, _, hf => LocL2.of_smooth hf
  | k + 1, _, hf => ⟨LocL2.of_smooth hf, fun i =>
      ⟨pderiv _ i, weakDeriv_of_smooth hf i, Sobolev.of_smooth k (hf.pderiv i)⟩⟩

/-- **B6** `H^k_loc` is stable under multiplication by smooth functions (Leibniz rule for weak derivatives). -/
theorem Sobolev.smooth_mul : ∀ {k : ℕ} {f ψ : (Fin d → ℝ) → ℝ}, Sobolev k f → Sm ψ →
    Sobolev k (fun x => ψ x * f x)
  | 0, _, _, hf, hψ => LocL2.mul_continuous hf hψ.continuous
  | k + 1, f, ψ, hf, hψ => ⟨LocL2.mul_continuous hf.1 hψ.continuous, fun i => by
      obtain ⟨g, hg, hS⟩ := hf.2 i
      exact ⟨fun x => ψ x * g x + pderiv ψ i x * f x, hg.smooth_mul hψ,
        Sobolev.add (Sobolev.smooth_mul hS hψ) (Sobolev.smooth_mul hf.mono (hψ.pderiv i))⟩⟩


end MarkovTriple.BGL.Instances.GibbsRd.Elliptic
