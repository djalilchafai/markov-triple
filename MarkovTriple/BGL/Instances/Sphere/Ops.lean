import Mathlib
import MarkovTriple.BGL.Instances.Sphere.Basic
import MarkovTriple.BGL.Instances.Sphere.Trig
import MarkovTriple.BGL.Instances.Sphere.Hadamard
import MarkovTriple.BGL.Frozen.PartialDeriv

/-!
# The operators `Γ`, `L` on the zonal sphere `S³`

In the `θ`-picture (`x = cos θ`): `Γ(f,g) = F' G'` and `L f = F'' + 2 cot θ · F'`, with `F = f(cos ·)`.
The quotient `F'/sin θ` is `Dq F` (a smooth even function, by the Hadamard lemma).
-/

open MeasureTheory Real Set Filter Topology
open MarkovTriple.Sanity.OU (Sm deriv_comp1 contDiff_pderiv)
open MarkovTriple.BGL (pderiv pderiv₂)

namespace MarkovTriple.BGL.Instances.Sphere

/-- even and `2π`-periodic. -/
def EP (H : ℝ → ℝ) : Prop := (∀ θ, H (-θ) = H θ) ∧ (∀ θ, H (θ + 2 * π) = H θ)

lemma ep_ext (f : Zon → ℝ) : EP (ext f) := ⟨ext_neg f, ext_add_two_pi f⟩

lemma EP.add {F G : ℝ → ℝ} (hF : EP F) (hG : EP G) : EP (F + G) :=
  ⟨fun θ => by simp [hF.1, hG.1], fun θ => by simp [hF.2, hG.2]⟩

lemma EP.mul {F G : ℝ → ℝ} (hF : EP F) (hG : EP G) : EP (F * G) :=
  ⟨fun θ => by simp [hF.1, hG.1], fun θ => by simp [hF.2, hG.2]⟩

lemma EP.const (c : ℝ) : EP (fun _ => c) := ⟨fun _ => rfl, fun _ => rfl⟩

lemma EP.cos : EP (fun θ => Real.cos θ) := ⟨fun θ => by simp, fun θ => by simp⟩

lemma EP.deriv_odd {F : ℝ → ℝ} (h : EP F) (θ : ℝ) : deriv F (-θ) = -deriv F θ :=
  MarkovTriple.BGL.Instances.Sphere.deriv_odd h.1 θ

lemma EP.deriv_per {F : ℝ → ℝ} (h : EP F) (θ : ℝ) : deriv F (θ + 2 * π) = deriv F θ :=
  deriv_periodic h.2 θ

lemma EP.deriv2 {F : ℝ → ℝ} (h : EP F) : EP (deriv (deriv F)) :=
  ⟨fun θ => deriv_even_of_odd (fun x => h.deriv_odd x) θ, fun θ => deriv_periodic (fun x => h.deriv_per x) θ⟩

lemma EP.comp {k : ℕ} (ψ : (Fin k → ℝ) → ℝ) {F : Fin k → ℝ → ℝ} (hF : ∀ i, EP (F i)) :
    EP (fun θ => ψ (fun i => F i θ)) :=
  ⟨fun θ => by simp [(hF _).1], fun θ => by simp [(hF _).2]⟩

lemma EP.Dq {F : ℝ → ℝ} (h : EP F) : EP (Dq F) := ⟨Dq_even h.1, Dq_periodic h.1 h.2⟩

lemma EP.dG {F G : ℝ → ℝ} (hF : EP F) (hG : EP G) : EP (fun θ => deriv F θ * deriv G θ) :=
  ⟨fun θ => by
      show deriv F (-θ) * deriv G (-θ) = deriv F θ * deriv G θ
      rw [hF.deriv_odd, hG.deriv_odd]; ring,
    fun θ => by
      show deriv F (θ + 2 * π) * deriv G (θ + 2 * π) = deriv F θ * deriv G θ
      rw [hF.deriv_per, hG.deriv_per]⟩

/-- vanishing of `F'` at the multiples of `π` (needed for `Dq`). -/
lemma hF0 {F : ℝ → ℝ} (hF : Sm F) (h : EP F) (k : ℤ) : deriv F (k * π) = 0 :=
  deriv_zero_of_even_periodic hF h.1 h.2 k

/-! ### the operators in the `θ`-picture -/

/-- `L` in the `θ`-picture: `F'' + 2 cos θ · (F'/sin θ)`. -/
noncomputable def dL (F : ℝ → ℝ) (θ : ℝ) : ℝ := deriv (deriv F) θ + 2 * (cos θ * Dq F θ)

/-- `Γ` in the `θ`-picture. -/
noncomputable def dG (F G : ℝ → ℝ) (θ : ℝ) : ℝ := deriv F θ * deriv G θ

lemma sm_Dq {F : ℝ → ℝ} (hF : Sm F) (h : EP F) : Sm (Dq F) := contDiff_Dq hF (hF0 hF h)

lemma sm_dL {F : ℝ → ℝ} (hF : Sm F) (h : EP F) : Sm (dL F) := by
  unfold dL
  exact hF.deriv'.deriv'.add (contDiff_const.mul (contDiff_cos.mul (sm_Dq hF h)))

lemma sm_dG {F G : ℝ → ℝ} (hF : Sm F) (hG : Sm G) : Sm (dG F G) := hF.deriv'.mul hG.deriv'

lemma ep_dL {F : ℝ → ℝ} (h : EP F) : EP (dL F) := by
  unfold dL
  exact h.deriv2.add ((EP.const 2).mul (EP.cos.mul h.Dq))

lemma ep_dG {F G : ℝ → ℝ} (hF : EP F) (hG : EP G) : EP (dG F G) := hF.dG hG

/-- `Dq` of a product. -/
lemma Dq_mul {F G : ℝ → ℝ} (hF : Sm F) (hG : Sm G) (eF : EP F) (eG : EP G) (θ : ℝ) :
    Dq (F * G) θ = Dq F θ * G θ + F θ * Dq G θ := by
  have hFG : Sm (F * G) := hF.mul hG
  have e1 : Dq (F * G) = fun θ => Dq F θ * G θ + F θ * Dq G θ := by
    refine eq_of_sin_mul_eq (sm_Dq hFG (eF.mul eG)).continuous
      (((sm_Dq hF eF).continuous.mul hG.continuous).add (hF.continuous.mul (sm_Dq hG eG).continuous))
      fun θ => ?_
    have h1 := sin_mul_Dq (hF0 hFG (eF.mul eG)) θ
    have h2 := sin_mul_Dq (hF0 hF eF) θ
    have h3 := sin_mul_Dq (hF0 hG eG) θ
    have h4 : deriv (F * G) θ = deriv F θ * G θ + F θ * deriv G θ := by
      have := ((hF.hasDerivAt θ).mul (hG.hasDerivAt θ)).deriv
      simpa [add_comm] using this
    rw [h1, h4, ← h2, ← h3]; ring
  exact congrFun e1 θ

lemma dL_mul {F G : ℝ → ℝ} (hF : Sm F) (hG : Sm G) (eF : EP F) (eG : EP G) (θ : ℝ) :
    dL (F * G) θ = dL F θ * G θ + 2 * dG F G θ + F θ * dL G θ := by
  have hd : deriv (F * G) = deriv F * G + F * deriv G := MarkovTriple.Sanity.OU.deriv_mul_s hF hG
  have hdd : deriv (deriv (F * G)) θ = deriv (deriv F) θ * G θ + 2 * (deriv F θ * deriv G θ) +
      F θ * deriv (deriv G) θ := by
    have h1 := MarkovTriple.Sanity.OU.deriv_add_s (f := deriv F * G) (g := F * deriv G)
      (hF.deriv'.mul hG) (hF.mul hG.deriv')
    have h2 := MarkovTriple.Sanity.OU.deriv_mul_s hF.deriv' hG
    have h3 := MarkovTriple.Sanity.OU.deriv_mul_s hF hG.deriv'
    rw [hd, h1, h2, h3]
    simp only [Pi.add_apply, Pi.mul_apply]; ring
  unfold dL dG
  rw [hdd, Dq_mul hF hG eF eG θ]; ring

/-- `Dq` of a smooth composition. -/
lemma Dq_comp {k : ℕ} (ψ : (Fin k → ℝ) → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {F : Fin k → ℝ → ℝ}
    (hF : ∀ i, Sm (F i)) (eF : ∀ i, EP (F i)) (θ : ℝ) :
    Dq (fun θ => ψ (fun i => F i θ)) θ = ∑ i, pderiv ψ i (fun j => F j θ) * Dq (F i) θ := by
  have hc : Sm (fun θ => ψ (fun i => F i θ)) := hψ.comp (contDiff_pi.2 hF)
  have e1 : Dq (fun θ => ψ (fun i => F i θ)) =
      fun θ => ∑ i, pderiv ψ i (fun j => F j θ) * Dq (F i) θ := by
    refine eq_of_sin_mul_eq (sm_Dq hc (EP.comp ψ eF)).continuous ?_ fun θ => ?_
    · refine continuous_finset_sum _ fun i _ => ?_
      exact (((contDiff_pderiv ψ hψ i).comp (contDiff_pi.2 hF)).continuous).mul
        (sm_Dq (hF i) (eF i)).continuous
    · have h1 := sin_mul_Dq (hF0 hc (EP.comp ψ eF)) θ
      rw [h1, deriv_comp1 ψ hψ F hF, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← sin_mul_Dq (hF0 (hF i) (eF i)) θ]; ring
  exact congrFun e1 θ

/-- second derivative of a smooth composition. -/
lemma deriv2_comp {k : ℕ} (ψ : (Fin k → ℝ) → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {F : Fin k → ℝ → ℝ}
    (hF : ∀ i, Sm (F i)) (θ : ℝ) :
    deriv (deriv (fun θ => ψ (fun i => F i θ))) θ =
      ∑ i, pderiv ψ i (fun j => F j θ) * deriv (deriv (F i)) θ +
        ∑ i, ∑ j, pderiv₂ ψ i j (fun l => F l θ) * (deriv (F i) θ * deriv (F j) θ) := by
  have h := congrFun (MarkovTriple.Sanity.OU.diffusion_s k ψ hψ F hF).2 θ
  have hD := deriv_comp1 ψ hψ F hF
  simp only [MarkovTriple.Sanity.OU.Lo, MarkovTriple.Sanity.OU.Go] at h
  rw [hD] at h
  rw [hD]
  -- `h : (∑ ...)' - θ * ∑ ... = ...`
  have : deriv (fun y => ∑ i, pderiv ψ i (fun j => F j y) * deriv (F i) y) θ =
      ∑ i, pderiv ψ i (fun j => F j θ) * deriv (deriv (F i)) θ +
        ∑ i, ∑ j, pderiv₂ ψ i j (fun l => F l θ) * (deriv (F i) θ * deriv (F j) θ) := by
    have h' : deriv (fun y => ∑ i, pderiv ψ i (fun j => F j y) * deriv (F i) y) θ -
        θ * ∑ i, pderiv ψ i (fun j => F j θ) * deriv (F i) θ =
        ∑ i, pderiv ψ i (fun j => F j θ) * (deriv (deriv (F i)) θ - θ * deriv (F i) θ) +
          ∑ i, ∑ j, pderiv₂ ψ i j (fun l => F l θ) * (deriv (F i) θ * deriv (F j) θ) := h
    have e4 : ∑ i, pderiv ψ i (fun j => F j θ) * (deriv (deriv (F i)) θ - θ * deriv (F i) θ)
        = ∑ i, pderiv ψ i (fun j => F j θ) * deriv (deriv (F i)) θ
          - θ * ∑ i, pderiv ψ i (fun j => F j θ) * deriv (F i) θ := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [e4] at h'
    linarith
  exact this

lemma dL_comp {k : ℕ} (ψ : (Fin k → ℝ) → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {F : Fin k → ℝ → ℝ}
    (hF : ∀ i, Sm (F i)) (eF : ∀ i, EP (F i)) (θ : ℝ) :
    dL (fun θ => ψ (fun i => F i θ)) θ =
      ∑ i, pderiv ψ i (fun j => F j θ) * dL (F i) θ +
        ∑ i, ∑ j, pderiv₂ ψ i j (fun l => F l θ) * dG (F i) (F j) θ := by
  unfold dL dG
  rw [deriv2_comp ψ hψ hF θ, Dq_comp ψ hψ hF eF θ]
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  have : ∀ i, 2 * (cos θ * (pderiv ψ i (fun j => F j θ) * Dq (F i) θ)) =
      pderiv ψ i (fun j => F j θ) * (2 * (cos θ * Dq (F i) θ)) := fun i => by ring
  simp only [this]
  ring

/-! ### transport to `Zon` -/

/-- `Γ` on `Zon`. -/
noncomputable def GZ (f g : Zon → ℝ) : Zon → ℝ := mk (dG (ext f) (ext g))

/-- `L` on `Zon`. -/
noncomputable def LZ (f : Zon → ℝ) : Zon → ℝ := mk (dL (ext f))

lemma apply_eq_ext (f : Zon → ℝ) (x : Zon) : f x = ext f (arc x) := by simp [ext, cosZ_arc]

lemma ext_GZ {f g : Zon → ℝ} (hf : f ∈ AZ) (hg : g ∈ AZ) : ext (GZ f g) = dG (ext f) (ext g) :=
  ext_mk (ep_dG (ep_ext f) (ep_ext g)).1 (ep_dG (ep_ext f) (ep_ext g)).2

lemma ext_LZ {f : Zon → ℝ} : ext (LZ f) = dL (ext f) :=
  ext_mk (ep_dL (ep_ext f)).1 (ep_dL (ep_ext f)).2

lemma GZ_mem {f g : Zon → ℝ} (hf : f ∈ AZ) (hg : g ∈ AZ) : GZ f g ∈ AZ := by
  show Sm (ext (GZ f g))
  rw [ext_GZ hf hg]; exact sm_dG hf hg

lemma LZ_mem {f : Zon → ℝ} (hf : f ∈ AZ) : LZ f ∈ AZ := by
  show Sm (ext (LZ f))
  rw [ext_LZ]; exact sm_dL hf (ep_ext f)

lemma GZ_apply (f g : Zon → ℝ) (x : Zon) : GZ f g x = dG (ext f) (ext g) (arc x) := rfl
lemma LZ_apply (f : Zon → ℝ) (x : Zon) : LZ f x = dL (ext f) (arc x) := rfl

/-- the carré du champ formula `ΓA f g = ½ (L(fg) − f L g − g L f)` equals `GZ`. -/
lemma ΓA_eq {f g : Zon → ℝ} (hf : f ∈ AZ) (hg : g ∈ AZ) (x : Zon) :
    (LZ (f * g) x - f x * LZ g x - g x * LZ f x) / 2 = GZ f g x := by
  have hfg : ext (f * g) = ext f * ext g := rfl
  rw [LZ_apply, LZ_apply, LZ_apply, GZ_apply, hfg, dL_mul hf hg (ep_ext f) (ep_ext g),
    apply_eq_ext f x, apply_eq_ext g x]
  simp only [dG]
  ring

lemma ext_const (c : ℝ) : ext (fun _ : Zon => c) = fun _ => c := rfl

end MarkovTriple.BGL.Instances.Sphere
