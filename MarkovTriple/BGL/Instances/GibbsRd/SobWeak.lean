import MarkovTriple.BGL.Instances.GibbsRd.SobDefs

/-!
# Algebra of weak derivatives (R16 Sob)

Sum, multiplication by a smooth function (one-step Leibniz), stability of `HasSobL1` under smooth
cutoffs, `WeakIter` existence, and locality (a weak derivative of a function a.e. vanishing on an open
set vanishes a.e. there).
-/

open MeasureTheory
open scoped ContDiff

namespace MarkovTriple.BGL.Instances.GibbsRd.Sob

variable {d : ℕ}

theorem contDiff_pd' (i : Fin d) {φ : (Fin d → ℝ) → ℝ} (h : ContDiff ℝ ∞ φ) :
    Continuous (pd i φ) := (contDiff_pd i h).continuous

theorem integrable_mul_test {f ψ : (Fin d → ℝ) → ℝ} (hf : LocallyIntegrable f)
    (hc : Continuous ψ) (hs : HasCompactSupport ψ) : Integrable (fun x => f x * ψ x) := by
  simpa using hf.integrable_smul_right_of_hasCompactSupport hc hs

theorem locallyIntegrable_mul_cont {f χ : (Fin d → ℝ) → ℝ} (hf : LocallyIntegrable f)
    (hχ : Continuous χ) : LocallyIntegrable (fun x => χ x * f x) := by
  rw [locallyIntegrable_iff]
  intro K hK
  have h1 : IntegrableOn f K := hf.integrableOn_isCompact hK
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hχ.continuousOn
  refine Integrable.bdd_mul (c := C) h1 hχ.aestronglyMeasurable.restrict ?_
  exact ae_restrict_of_forall_mem hK.measurableSet hC

theorem WeakDeriv.add {f₁ g₁ f₂ g₂ : (Fin d → ℝ) → ℝ} {i : Fin d} (h₁ : WeakDeriv f₁ g₁ i)
    (h₂ : WeakDeriv f₂ g₂ i) : WeakDeriv (fun x => f₁ x + f₂ x) (fun x => g₁ x + g₂ x) i := by
  refine ⟨h₁.1.add h₂.1, h₁.2.1.add h₂.2.1, fun φ hφ hc => ?_⟩
  have hD := contDiff_pd' i hφ
  have hDc := hasCompactSupport_pd i hc
  have e1 : ∫ x, f₁ x * pd i φ x = -∫ x, g₁ x * φ x := h₁.2.2 φ hφ hc
  have e2 : ∫ x, f₂ x * pd i φ x = -∫ x, g₂ x * φ x := h₂.2.2 φ hφ hc
  have i1 := integrable_mul_test h₁.1 hD hDc
  have i2 := integrable_mul_test h₂.1 hD hDc
  have j1 := integrable_mul_test h₁.2.1 hφ.continuous hc
  have j2 := integrable_mul_test h₂.2.1 hφ.continuous hc
  show ∫ x, (f₁ x + f₂ x) * pd i φ x = -∫ x, (g₁ x + g₂ x) * φ x
  simp only [add_mul]
  rw [integral_add i1 i2, integral_add j1 j2, e1, e2]
  ring

theorem WeakDeriv.mul_smooth {f g χ : (Fin d → ℝ) → ℝ} {i : Fin d} (h : WeakDeriv f g i)
    (hχ : ContDiff ℝ ∞ χ) :
    WeakDeriv (fun x => χ x * f x) (fun x => χ x * g x + pd i χ x * f x) i := by
  refine ⟨locallyIntegrable_mul_cont h.1 hχ.continuous,
    (locallyIntegrable_mul_cont h.2.1 hχ.continuous).add
      (locallyIntegrable_mul_cont h.1 (contDiff_pd' i hχ)), fun φ hφ hc => ?_⟩
  have hψ : ContDiff ℝ ∞ (fun x => χ x * φ x) := hχ.mul hφ
  have hψc : HasCompactSupport (fun x => χ x * φ x) := hc.mul_left
  have e : ∫ x, f x * pd i (fun x => χ x * φ x) x = -∫ x, g x * (χ x * φ x) := h.2.2 _ hψ hψc
  have hder : ∀ x, pd i (fun x => χ x * φ x) x
      = pd i χ x * φ x + χ x * pd i φ x := by
    intro x
    have : fderiv ℝ (fun y => χ y * φ y) x = χ x • fderiv ℝ φ x + φ x • fderiv ℝ χ x :=
      ((hχ.differentiable (by simp) x).hasFDerivAt.mul
        (hφ.differentiable (by simp) x).hasFDerivAt).fderiv
    simp only [pd]
    rw [this]
    simp
    ring
  simp only [hder] at e
  show ∫ x, (χ x * f x) * pd i φ x = -∫ x, (χ x * g x + pd i χ x * f x) * φ x
  have hDχ := contDiff_pd' i hχ
  have hDφ := contDiff_pd' i hφ
  have hDφc := hasCompactSupport_pd i hc
  have a1 : Integrable (fun x => f x * (pd i χ x * φ x)) := by
    have := integrable_mul_test h.1 (hDχ.mul hφ.continuous) (hc.mul_left (f := pd i χ))
    simpa using this
  have a2 : Integrable (fun x => f x * (χ x * pd i φ x)) :=
    integrable_mul_test h.1 (hχ.continuous.mul hDφ) hDφc.mul_left
  have b1 : Integrable (fun x => g x * (χ x * φ x)) :=
    integrable_mul_test h.2.1 (hχ.continuous.mul hφ.continuous) hc.mul_left
  have b2 : Integrable (fun x => f x * pd i χ x * φ x) := by
    have := integrable_mul_test h.1 (hDχ.mul hφ.continuous) (hc.mul_left (f := pd i χ))
    simpa [mul_assoc] using this
  simp only [mul_add] at e
  rw [integral_add a1 a2] at e
  have : ∀ x, χ x * f x * pd i φ x = f x * (χ x * pd i φ x) := fun x => by ring
  simp only [this]
  have e' : ∫ x, f x * (χ x * pd i φ x)
      = -(∫ x, g x * (χ x * φ x)) - ∫ x, f x * (pd i χ x * φ x) := by linarith
  rw [e']
  have : ∀ x, (χ x * g x + pd i χ x * f x) * φ x
      = g x * (χ x * φ x) + f x * (pd i χ x * φ x) := fun x => by ring
  simp only [this]
  rw [integral_add b1 a1]
  ring

theorem HasSobL1.add : ∀ (k : ℕ) {a b : (Fin d → ℝ) → ℝ}, HasSobL1 k a → HasSobL1 k b →
    HasSobL1 k (fun x => a x + b x)
  | 0, _, _, ha, hb => LocallyIntegrable.add ha hb
  | k + 1, _, _, ha, hb => ⟨ha.1.add hb.1, fun i => by
      obtain ⟨g₁, hg₁, hk₁⟩ := ha.2 i
      obtain ⟨g₂, hg₂, hk₂⟩ := hb.2 i
      exact ⟨_, hg₁.add hg₂, HasSobL1.add k hk₁ hk₂⟩⟩

theorem HasSobL1.mul_smooth : ∀ (k : ℕ) {f χ : (Fin d → ℝ) → ℝ}, HasSobL1 k f → ContDiff ℝ ∞ χ →
    HasSobL1 k (fun x => χ x * f x)
  | 0, _, _, hf, hχ => locallyIntegrable_mul_cont hf hχ.continuous
  | k + 1, f, χ, hf, hχ => ⟨locallyIntegrable_mul_cont hf.1 hχ.continuous, fun i => by
      obtain ⟨g, hg, hk⟩ := hf.2 i
      refine ⟨_, hg.mul_smooth hχ, HasSobL1.add k (HasSobL1.mul_smooth k hk hχ) ?_⟩
      exact HasSobL1.mul_smooth k (HasSobL1.mono k hf) (contDiff_pd i hχ)⟩

/-- Existence of iterated weak derivatives along a word. -/
theorem exists_weakIter : ∀ (l : List (Fin d)) (k : ℕ) {f : (Fin d → ℝ) → ℝ}, l.length ≤ k →
    HasSobL1 k f → ∃ g, WeakIter l f g ∧ HasSobL1 (k - l.length) g
  | [], k, f, _, hf => ⟨f, rfl, by simpa using hf⟩
  | i :: l, k, f, hlk, hf => by
    have hlk' : l.length ≤ k := by simp at hlk; omega
    obtain ⟨h, hh, hh'⟩ := exists_weakIter l k hlk' hf
    have hpos : k - l.length = (k - (i :: l).length) + 1 := by simp at hlk ⊢; omega
    rw [hpos] at hh'
    obtain ⟨g, hg, hg'⟩ := hh'.2 i
    exact ⟨g, ⟨h, hh, hg⟩, hg'⟩

/-- Locality: weak derivative of a function a.e. zero on an open set vanishes a.e. there. -/
theorem WeakDeriv.ae_zero_of_open {f g : (Fin d → ℝ) → ℝ} {i : Fin d} (h : WeakDeriv f g i)
    {U : Set (Fin d → ℝ)} (hU : IsOpen U) (hf0 : ∀ᵐ x, x ∈ U → f x = 0) :
    ∀ᵐ x, x ∈ U → g x = 0 := by
  refine hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero (h.2.1.locallyIntegrableOn U) ?_
  intro φ hφ hc hsub
  have e := h.2.2 φ hφ hc
  have h0 : ∫ x, f x * (fderiv ℝ φ x (Pi.single i 1)) = 0 := by
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hf0] with x hx
    by_cases hxU : x ∈ U
    · simp [hx hxU]
    · have : x ∉ tsupport φ := fun hh => hxU (hsub hh)
      have hd : fderiv ℝ φ x = 0 := fderiv_of_notMem_tsupport ℝ this
      simp [hd]
  rw [h0] at e
  have : ∫ x, g x * φ x = 0 := by linarith
  simpa [mul_comm] using this

theorem WeakIter.ae_zero_of_open : ∀ (l : List (Fin d)) {f g : (Fin d → ℝ) → ℝ}, WeakIter l f g →
    ∀ {U : Set (Fin d → ℝ)}, IsOpen U → (∀ᵐ x, x ∈ U → f x = 0) → ∀ᵐ x, x ∈ U → g x = 0
  | [], _, _, h, _, _, h0 => by subst h; exact h0
  | i :: l, _, _, ⟨h, hh, hg⟩, _, hU, h0 =>
      hg.ae_zero_of_open hU (WeakIter.ae_zero_of_open l hh hU h0)

end MarkovTriple.BGL.Instances.GibbsRd.Sob
