import Mathlib
import MarkovTriple.BGL.Instances.LebesgueRd.Basic
import MarkovTriple.BGL.Frozen.GammaA
import MarkovTriple.BGL.Frozen.Gamma2

/-!
# `Γ₂` on `(ℝ^d, Lebesgue)` and the pointwise Bochner inequality (stage S1')

`Γ₂(f) = Σᵢⱼ (∂ᵢ∂ⱼ f)²` for `f ∈ C^∞(ℝ^d)`, hence `Γ₂(f) ≥ (1/d)(Δf)²` (Cauchy–Schwarz), sharp.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace MarkovTriple.BGL.LebesgueRd

variable {d : ℕ}

lemma dd_dd_symm {f : (Fin d → ℝ) → ℝ} (hf : Sm f) (i j : Fin d) (x : Fin d → ℝ) :
    dd i (dd j f) x = dd j (dd i f) x := by
  have hsym := (hf.contDiffAt (x := x)).isSymmSndFDerivAt (by simp)
  have key : ∀ i j, dd i (dd j f) x = fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1) := by
    intro i j
    unfold dd
    have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
      ((hf.fderiv_right (m := 1) (by simp)).differentiable (by simp)) x
    rw [fderiv_clm_apply hd (differentiableAt_const _)]
    simp
  rw [key, key]
  exact hsym _ _

lemma dd_fsum {k : ℕ} {h : Fin k → (Fin d → ℝ) → ℝ} (hh : ∀ j, Sm (h j)) (i : Fin d) :
    dd i (fun x => ∑ j, h j x) = fun x => ∑ j, dd i (h j) x := by
  funext x
  unfold dd
  have := HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ => hasFDerivAt_of (hh j) x)
  rw [this.fderiv]
  simp

lemma Lf_fsum {k : ℕ} {h : Fin k → (Fin d → ℝ) → ℝ} (hh : ∀ j, Sm (h j)) (x : Fin d → ℝ) :
    Lf (fun y => ∑ j, h j y) x = ∑ j, Lf (h j) x := by
  unfold Lf
  have : ∀ i, dd i (dd i (fun y => ∑ j, h j y)) x = ∑ j, dd i (dd i (h j)) x := by
    intro i
    rw [dd_fsum hh i, dd_fsum (fun j => (hh j).dd i) i]
  simp only [this]
  exact Finset.sum_comm

lemma Lf_mul {f g : (Fin d → ℝ) → ℝ} (hf : Sm f) (hg : Sm g) (x : Fin d → ℝ) :
    Lf (f * g) x = f x * Lf g x + g x * Lf f x + 2 * Gf f g x := by
  unfold Lf Gf
  have h1 : ∀ i, dd i (f * g) = dd i f * g + f * dd i g := fun i => by
    funext y; simpa using dd_mul hf hg i y
  have h2 : ∀ i, dd i (dd i (f * g)) x =
      dd i (dd i f) x * g x + 2 * (dd i f x * dd i g x) + f x * dd i (dd i g) x := by
    intro i
    have hA : Sm (dd i f * g) := (hf.dd i).mul hg
    have hB : Sm (f * dd i g) := hf.mul (hg.dd i)
    rw [h1 i, dd_add hA hB i]
    simp only [Pi.add_apply]
    rw [dd_mul (hf.dd i) hg i x, dd_mul hf (hg.dd i) i x]
    ring
  simp only [h2, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
  ring

lemma dd_Lf {f : (Fin d → ℝ) → ℝ} (hf : Sm f) (j : Fin d) (x : Fin d → ℝ) :
    dd j (Lf f) x = Lf (dd j f) x := by
  have e : Lf f = fun y => ∑ i, dd i (dd i f) y := rfl
  rw [e, dd_fsum (fun i => (hf.dd i).dd i) j]
  unfold Lf
  refine Finset.sum_congr rfl fun i _ => ?_
  have e1 : dd i (dd i (dd j f)) = dd i (dd j (dd i f)) := by
    funext y; congr 1; funext z; exact dd_dd_symm hf i j z
  have e2 : dd i (dd j (dd i f)) x = dd j (dd i (dd i f)) x :=
    dd_dd_symm (hf.dd i) i j x
  rw [e1]
  exact e2.symm

lemma Gf_symm (f g : (Fin d → ℝ) → ℝ) : Gf f g = Gf g f := by
  funext x; simp [Gf, mul_comm]

lemma ΓA_eq_Gf (hd : 1 ≤ d) {f g : (Fin d → ℝ) → ℝ} (hf : Sm f) (hg : Sm g) :
    (lebesgueRdDiffusion d hd).ΓA f g = Gf f g := by
  funext x
  show (Lf (f * g) x - f x * Lf g x - g x * Lf f x) / 2 = Gf f g x
  rw [Lf_mul hf hg x]
  ring

/-- `Γ₂(f) = Σᵢⱼ (∂ᵢ∂ⱼ f)²`. -/
theorem Γ₂_eq (hd : 1 ≤ d) {f : (Fin d → ℝ) → ℝ} (hf : Sm f) (x : Fin d → ℝ) :
    (lebesgueRdDiffusion d hd).Γ₂ f f x = ∑ i, ∑ j, (dd i (dd j f) x) ^ 2 := by
  have hLf : Sm (Lf f) := by
    have : Lf f = fun y => ∑ i, dd i (dd i f) y := rfl
    rw [this]; exact ContDiff.sum fun i _ => (hf.dd i).dd i
  have hG : Sm (Gf f f) := by
    have : Gf f f = fun y => ∑ i, dd i f y * dd i f y := rfl
    rw [this]; exact ContDiff.sum fun i _ => (hf.dd i).mul (hf.dd i)
  show (Lf ((lebesgueRdDiffusion d hd).ΓA f f) x -
    (lebesgueRdDiffusion d hd).ΓA f (Lf f) x - (lebesgueRdDiffusion d hd).ΓA (Lf f) f x) / 2 = _
  rw [ΓA_eq_Gf hd hf hf, ΓA_eq_Gf hd hf hLf, ΓA_eq_Gf hd hLf hf]
  have e1 : Gf f f = fun y => ∑ j, dd j f y * dd j f y := rfl
  have hu : ∀ j, Sm (fun y => dd j f y * dd j f y) := fun j => (hf.dd j).mul (hf.dd j)
  have e2 : ∀ j, Lf (fun y => dd j f y * dd j f y) x =
      2 * (dd j f x * Lf (dd j f) x) + 2 * Gf (dd j f) (dd j f) x := by
    intro j
    have := Lf_mul (hf.dd j) (hf.dd j) x
    simp only [Pi.mul_def] at this
    rw [this]; ring
  rw [e1, Lf_fsum hu x]
  simp only [e2]
  have e3 : Gf f (Lf f) x = ∑ j, dd j f x * Lf (dd j f) x := by
    unfold Gf
    exact Finset.sum_congr rfl fun j _ => by rw [dd_Lf hf j x]
  rw [Gf_symm (Lf f) f, e3]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  unfold Gf Lf
  have : ∀ j, ∑ i, dd i (dd j f) x * dd i (dd j f) x = ∑ i, (dd i (dd j f) x) ^ 2 :=
    fun j => Finset.sum_congr rfl fun i _ => by ring
  simp only [this]
  rw [Finset.sum_comm (f := fun j i => (dd i (dd j f) x) ^ 2)]
  ring

/-- Pointwise Bochner inequality with the dimensional constant `1/d` (Cauchy–Schwarz). -/
theorem bochner_Rd (hd : 1 ≤ d) {f : (Fin d → ℝ) → ℝ} (hf : Sm f) (x : Fin d → ℝ) :
    (1 / (d : ℝ)) * (Lf f x) ^ 2 ≤ (lebesgueRdDiffusion d hd).Γ₂ f f x := by
  rw [Γ₂_eq hd hf x]
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have h1 : (Lf f x) ^ 2 ≤ (d : ℝ) * ∑ i, (dd i (dd i f) x) ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin d)))
      (f := fun i => dd i (dd i f) x)
    simpa [Lf] using this
  have h2 : ∑ i, (dd i (dd i f) x) ^ 2 ≤ ∑ i, ∑ j, (dd i (dd j f) x) ^ 2 :=
    Finset.sum_le_sum fun i _ =>
      Finset.single_le_sum (f := fun j => (dd i (dd j f) x) ^ 2) (fun j _ => by positivity)
        (Finset.mem_univ i)
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hdpos]
  nlinarith

/-- the quadratic test function `|x|²/2`. -/
noncomputable def quad (x : Fin d → ℝ) : ℝ := ∑ j, (1 / 2 : ℝ) * (x j * x j)

lemma quad_smooth : Sm (quad : (Fin d → ℝ) → ℝ) :=
  ContDiff.sum fun j _ => contDiff_const.mul
    (((contDiff_apply ℝ ℝ j)).mul (contDiff_apply ℝ ℝ j))

lemma dd_coord (i j : Fin d) (x : Fin d → ℝ) :
    dd i (fun y : Fin d → ℝ => y j) x = if j = i then 1 else 0 := by
  unfold dd
  have : HasFDerivAt (fun y : Fin d → ℝ => y j) (ContinuousLinearMap.proj j) x :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) j).hasFDerivAt
  rw [this.fderiv]
  simp [Pi.single_apply]

lemma dd_quad (i : Fin d) (x : Fin d → ℝ) : dd i quad x = x i := by
  have hh : ∀ j, Sm (fun y : Fin d → ℝ => (1 / 2 : ℝ) * (y j * y j)) := fun j =>
    contDiff_const.mul ((contDiff_apply ℝ ℝ j).mul (contDiff_apply ℝ ℝ j))
  have e : quad = fun y : Fin d → ℝ => ∑ j, (1 / 2 : ℝ) * (y j * y j) := rfl
  rw [e, dd_fsum hh i]
  have hj : ∀ j, dd i (fun y : Fin d → ℝ => (1 / 2 : ℝ) * (y j * y j)) x =
      x j * (if j = i then 1 else 0) := by
    intro j
    have hc : Sm (fun y : Fin d → ℝ => y j) := contDiff_apply ℝ ℝ j
    have h1 : (fun y : Fin d → ℝ => (1 / 2 : ℝ) * (y j * y j)) =
        (1 / 2 : ℝ) • ((fun y : Fin d → ℝ => y j) * (fun y : Fin d → ℝ => y j)) := rfl
    have hm : Sm ((fun y : Fin d → ℝ => y j) * (fun y : Fin d → ℝ => y j)) := hc.mul hc
    have h2 := dd_smul (1 / 2 : ℝ) hm i
    rw [h1, h2, Pi.smul_apply, dd_mul hc hc i x, dd_coord]
    simp
    ring
  simp only [hj]
  simp

lemma dd_dd_quad (i j : Fin d) (x : Fin d → ℝ) :
    dd i (dd j quad) x = if j = i then 1 else 0 := by
  have : dd j quad = fun y : Fin d → ℝ => y j := funext (dd_quad j)
  rw [this, dd_coord]

lemma Lf_quad (x : Fin d → ℝ) : Lf quad x = d := by
  simp [Lf, dd_dd_quad]

lemma Γ₂_quad (hd : 1 ≤ d) (x : Fin d → ℝ) : (lebesgueRdDiffusion d hd).Γ₂ quad quad x = d := by
  rw [Γ₂_eq hd quad_smooth x]
  simp [dd_dd_quad]

lemma Gf_quad_zero : Gf (quad : (Fin d → ℝ) → ℝ) quad 0 = 0 := by
  simp [Gf, dd_quad]

lemma Gf_coord (hd : 1 ≤ d) (x : Fin d → ℝ) :
    Gf (fun y : Fin d → ℝ => y ⟨0, hd⟩) (fun y => y ⟨0, hd⟩) x = 1 := by
  unfold Gf
  simp only [dd_coord]
  rw [Finset.sum_eq_single (⟨0, hd⟩ : Fin d) (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
  simp

lemma Lf_coord (hd : 1 ≤ d) (x : Fin d → ℝ) : Lf (fun y : Fin d → ℝ => y ⟨0, hd⟩) x = 0 := by
  have : ∀ i, dd i (fun y : Fin d → ℝ => y ⟨0, hd⟩) = fun _ => if (⟨0, hd⟩ : Fin d) = i then 1 else 0 :=
    fun i => funext (dd_coord i _)
  simp [Lf, this, dd_const]

lemma Γ₂_coord (hd : 1 ≤ d) (x : Fin d → ℝ) :
    (lebesgueRdDiffusion d hd).Γ₂ (fun y : Fin d → ℝ => y ⟨0, hd⟩) (fun y => y ⟨0, hd⟩) x = 0 := by
  have hc : Sm (fun y : Fin d → ℝ => y ⟨0, hd⟩) := contDiff_apply ℝ ℝ _
  rw [Γ₂_eq hd hc x]
  have : ∀ i, dd i (fun y : Fin d → ℝ => y ⟨0, hd⟩) = fun _ => if (⟨0, hd⟩ : Fin d) = i then 1 else 0 :=
    fun i => funext (dd_coord i _)
  simp [this, dd_const]

/-- **Exact range of the Bochner inequality on `C^∞(ℝ^d)`**: for `n > 0`,
`Γ₂(f) ≥ ρ Γ(f) + (1/n)(Δf)²` for all smooth `f` iff `ρ ≤ 0` and `d ≤ n`.  (Pointwise statement
for the diffusion triple's `Γ₂`; not the predicate `FullTriple.CD`.) -/
theorem bochner_Rd_iff (hd : 1 ≤ d) {ρ n : ℝ} (hn : 0 < n) :
    (∀ f : (Fin d → ℝ) → ℝ, Sm f → ∀ x, ρ * Gf f f x + (1 / n) * (Lf f x) ^ 2 ≤
        (lebesgueRdDiffusion d hd).Γ₂ f f x) ↔ ρ ≤ 0 ∧ (d : ℝ) ≤ n := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  constructor
  · intro h
    constructor
    · have := h _ (contDiff_apply ℝ ℝ (⟨0, hd⟩ : Fin d)) 0
      rw [Gf_coord hd, Lf_coord hd, Γ₂_coord hd] at this
      linarith
    · have := h _ quad_smooth 0
      rw [Gf_quad_zero, Lf_quad, Γ₂_quad hd] at this
      have h2 : (1 / n) * (d : ℝ) ^ 2 ≤ d := by linarith
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hn] at h2
      nlinarith
  · rintro ⟨hρ, hdn⟩ f hf x
    have h1 : 0 ≤ Gf f f x := Finset.sum_nonneg fun i _ => mul_self_nonneg _
    have h2 := bochner_Rd hd hf x
    have h3 : (1 / n) * (Lf f x) ^ 2 ≤ (1 / (d : ℝ)) * (Lf f x) ^ 2 :=
      mul_le_mul_of_nonneg_right (one_div_le_one_div_of_le hdpos hdn) (sq_nonneg _)
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hρ h1]

end MarkovTriple.BGL.LebesgueRd
