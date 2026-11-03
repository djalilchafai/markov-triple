import Mathlib
import MarkovTriple.BGL.Instances.Riemannian.BochnerChecks

/-!
# A genuinely non-flat example: the conformal plane `g_{ij} = e^{|x|²} δ_{ij}` with weight `W = 2 e^{|x|²}`

`confRiem : RiemData 2`: co-metric `g^{ij} = e^{-|x|²} δ_{ij}` on `ℝ²` (so `φ = |x|²/2`, `g_{ij} = e^{2φ} δ_{ij}`), weight
`W(x) = 2 e^{|x|²}` (`e^{-W} dμ_g = e^{-2e^{|x|²} + |x|²} dx`).  All fields of `RiemData` are proved (bounded co-metric
`≤ 1`, integrability by Gaussian domination).  The coordinate formulas of `Curvature.lean` give, for every `x`,

* `γ_{ij}^k = δ_{jk} x_i + δ_{ik} x_j − δ_{ij} x_k` (the conformal Christoffel symbols),
* `Ric_{ij} = −2 δ_{ij}` (`confRiem_ricci`; Gauss curvature `K = −2 e^{-|x|²} ≠ 0`: **not flat**),
* `∇∇W_{ij} = 4 e^{|x|²} (1 + |x|²) δ_{ij}` (`confRiem_hess_W`),

hence `Ric + ∇∇W = (4 e^{|x|²}(1+|x|²) − 2) δ ≥ 2 g` and, by `riem_curv_of_ricci`, `confRiem.Curv 2`
(`confRiem_curv`): `CD(2,∞)` for the formula-defined `Γ₂` on a non-flat weighted Riemannian manifold.
Under the named hypothesis `WeakHypo` the Poincaré inequality, spectral gap and `L²` decay follow
(`confRiem_poincare` ...).  NOT claimed: `WeakHypo` itself, `F8`.
-/

open MeasureTheory Filter Topology

namespace MarkovTriple.BGL.Instances.Riemannian

open MarkovTriple.BGL.Instances.GibbsRd
open MarkovTriple.BGL (pderiv pderiv₂ DiffusionTriple)
open scoped ENNReal

/-- the co-metric `g^{ij}(x) = e^{-|x|²} δ_{ij}` -/
noncomputable def confG (i j : Fin 2) (x : Rd 2) : ℝ := if i = j then Real.exp (-qd x) else 0

lemma sm_exp_qd : Sm (fun x : Rd 2 => Real.exp (qd x)) := sm_qd.exp

lemma sm_exp_neg_qd : Sm (fun x : Rd 2 => Real.exp (-qd x)) := sm_qd.neg.exp

lemma confG_diag (x : Rd 2) :
    (Matrix.of fun i j : Fin 2 => confG i j x) = Matrix.diagonal (fun _ => Real.exp (-qd x)) := by
  ext i j
  by_cases h : i = j
  · subst h; simp [confG]
  · simp [confG, h]

lemma confG_det (x : Rd 2) :
    Matrix.det (Matrix.of fun i j : Fin 2 => confG i j x) = Real.exp (-qd x) * Real.exp (-qd x) := by
  rw [confG_diag, Matrix.det_diagonal]
  simp [sq]

lemma confG_det_rpow (x : Rd 2) :
    (Matrix.det (Matrix.of fun i j : Fin 2 => confG i j x)) ^ (-(1 / 2 : ℝ)) = Real.exp (qd x) := by
  rw [confG_det, ← Real.exp_add, show -qd x + -qd x = (-2 * qd x) by ring, ← Real.exp_mul]
  congr 1
  ring

/-- **The non-flat conformal example** -/
noncomputable def confRiem : RiemData 2 where
  g := confG
  W := fun x => 2 * Real.exp (qd x)
  g_smooth := fun i j => by
    unfold confG
    by_cases h : i = j
    · simp only [h, ite_true]; exact sm_exp_neg_qd
    · simp only [h, ite_false]; exact contDiff_const
  g_symm := fun i j x => by
    unfold confG
    by_cases h : i = j
    · subst h; rfl
    · simp [h, Ne.symm h]
  g_posDef := fun x => by
    rw [confG_diag, Matrix.posDef_diagonal_iff]
    intro i
    exact Real.exp_pos _
  g_bdd := ⟨1, fun x v => by
    have : ∑ i, ∑ j, confG i j x * v i * v j = ∑ i, Real.exp (-qd x) * v i ^ 2 := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_eq_single i]
      · simp [confG]; ring
      · intro j _ hji; simp [confG, Ne.symm hji]
      · simp
    rw [this, one_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    have h1 : Real.exp (-qd x) ≤ 1 := by
      rw [Real.exp_le_one_iff]; linarith [qd_nonneg x]
    nlinarith [sq_nonneg (v i)]⟩
  W_smooth := contDiff_const.mul sm_exp_qd
  integrable := by
    have hcont : Continuous (fun x : Rd 2 => Real.exp (-(2 * Real.exp (qd x))) *
        (Matrix.det (Matrix.of fun i j : Fin 2 => confG i j x)) ^ (-(1 / 2 : ℝ))) := by
      simp only [confG_det_rpow]
      exact (Real.continuous_exp.comp (continuous_const.mul sm_exp_qd.continuous).neg).mul
        sm_exp_qd.continuous
    refine Integrable.mono' (g := fun x : Rd 2 => Real.exp (-(qd x / 2)))
      (integrable_of_convex_rd (V := fun x : Rd 2 => qd x / 2) (sm_qd.div_const 2) one_pos hessGe_gauss)
      hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    rw [confG_det_rpow, Real.norm_eq_abs, abs_of_nonneg (by positivity), ← Real.exp_add]
    apply Real.exp_le_exp.2
    have := Real.add_one_le_exp (qd x)
    have h0 := qd_nonneg x
    nlinarith

namespace confRiem

lemma pderiv_exp_qd (k : Fin 2) (x : Rd 2) :
    pderiv (fun y : Rd 2 => Real.exp (qd y)) k x = Real.exp (qd x) * (2 * x k) := by
  have h : HasFDerivAt (fun y : Rd 2 => Real.exp (qd y))
      (Real.exp (qd x) • fderiv ℝ qd x) x := (sm_qd.hasFDerivAt' x).exp
  unfold pderiv
  rw [h.fderiv]
  have := pderiv_qd k x
  unfold pderiv at this
  simp [this]

lemma gl_eq (i j : Fin 2) (x : Rd 2) : confRiem.gl i j x = if i = j then Real.exp (qd x) else 0 := by
  have h := confRiem.mat_mul_gl x i j
  have hg : ∀ a b, confRiem.g a b x = if a = b then Real.exp (-qd x) else 0 := fun a b => rfl
  simp only [hg] at h
  have : ∑ a, (if i = a then Real.exp (-qd x) else 0) * confRiem.gl a j x =
      Real.exp (-qd x) * confRiem.gl i j x := by
    simp [ite_mul, Finset.sum_ite_eq]
  rw [this] at h
  have hne : Real.exp (-qd x) ≠ 0 := (Real.exp_pos _).ne'
  have : confRiem.gl i j x = Real.exp (qd x) * (Real.exp (-qd x) * confRiem.gl i j x) := by
    rw [← mul_assoc, ← Real.exp_add]; simp
  rw [this, h]
  by_cases hij : i = j <;> simp [hij]

lemma gl_fun (i j : Fin 2) : confRiem.gl i j = fun y => if i = j then Real.exp (qd y) else 0 :=
  funext fun y => gl_eq i j y

lemma pderiv_gl (a b c : Fin 2) (x : Rd 2) :
    pderiv (confRiem.gl a b) c x = if a = b then Real.exp (qd x) * (2 * x c) else 0 := by
  rw [gl_fun]
  by_cases h : a = b
  · simp only [h, ite_true]; exact pderiv_exp_qd c x
  · simp [h, pderiv_const]

lemma chr_eq (k i j : Fin 2) (x : Rd 2) : confRiem.chr k i j x =
    (if j = k then x i else 0) + (if i = k then x j else 0) - (if i = j then x k else 0) := by
  unfold RiemData.chr RiemData.chr1
  simp only [pderiv_gl]
  have hg : ∀ a b, confRiem.g a b x = if a = b then Real.exp (-qd x) else 0 := fun a b => rfl
  simp only [hg, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have h1 : Real.exp (-qd x) * Real.exp (qd x) = 1 := by rw [← Real.exp_add]; simp
  rw [Real.exp_neg]
  have hE : Real.exp (qd x) ≠ 0 := (Real.exp_pos _).ne'
  split_ifs <;> field_simp <;> ring

lemma chr_fun (k i j : Fin 2) : confRiem.chr k i j = fun y =>
    (if j = k then y i else 0) + (if i = k then y j else 0) - (if i = j then y k else 0) :=
  funext fun y => chr_eq k i j y

lemma sm_ite_coord (p : Prop) [Decidable p] (i : Fin 2) : Sm (fun y : Rd 2 => if p then y i else 0) := by
  by_cases h : p
  · simp only [h, ite_true]; exact contDiff_apply ℝ ℝ i
  · simp only [h, ite_false]; exact contDiff_const

lemma pderiv_ite_coord (p : Prop) [Decidable p] (i m : Fin 2) (x : Rd 2) :
    pderiv (fun y : Rd 2 => if p then y i else 0) m x = if p then (if m = i then 1 else 0) else 0 := by
  by_cases h : p
  · simp only [h, ite_true]; exact pderiv_coord i m x
  · simp [h, pderiv_const]

lemma pderiv_chr (k i j m : Fin 2) (x : Rd 2) : pderiv (confRiem.chr k i j) m x =
    (if j = k then (if m = i then 1 else 0) else 0) + (if i = k then (if m = j then 1 else 0) else 0) -
      (if i = j then (if m = k then 1 else 0) else 0) := by
  rw [chr_fun]
  rw [pderiv_sub' ((sm_ite_coord _ i).add (sm_ite_coord _ j)) (sm_ite_coord _ k) m x,
    pderiv_add' (sm_ite_coord _ i) (sm_ite_coord _ j) m x, pderiv_ite_coord, pderiv_ite_coord,
    pderiv_ite_coord]

/-- **Ricci tensor of the conformal plane**: `Ric_{ij} = −2 δ_{ij}` -/
theorem ricci_eq (i j : Fin 2) (x : Rd 2) : confRiem.ricci i j x = if i = j then -2 else 0 := by
  unfold RiemData.ricci RiemData.riem
  simp only [pderiv_chr, chr_eq, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp <;> ring

/-- the conformal plane is not flat: `Ric_{00} = −2 ≠ 0` (Gauss curvature `−2 e^{-|x|²}`) -/
theorem ricci_00 (x : Rd 2) : confRiem.ricci 0 0 x = -2 := by
  rw [ricci_eq]; simp

lemma pderiv_W (k : Fin 2) (x : Rd 2) : pderiv confRiem.W k x = 4 * (Real.exp (qd x) * x k) := by
  show pderiv (fun y : Rd 2 => 2 * Real.exp (qd y)) k x = _
  rw [pderiv_mul' contDiff_const sm_exp_qd, pderiv_const, pderiv_exp_qd]
  ring

lemma pderiv_W_fun (k : Fin 2) : pderiv confRiem.W k = fun y => 4 * (Real.exp (qd y) * y k) :=
  funext fun y => pderiv_W k y

/-- `∇∇W_{ij} = 4 e^{|x|²}(1 + |x|²) δ_{ij}` for the conformal plane -/
theorem hess_W (i j : Fin 2) (x : Rd 2) :
    confRiem.hess confRiem.W i j x = if i = j then 4 * (Real.exp (qd x) * (1 + qd x)) else 0 := by
  unfold RiemData.hess
  rw [pderiv_W_fun j]
  have hsm : Sm (fun y : Rd 2 => Real.exp (qd y) * y j) := sm_exp_qd.mul (contDiff_apply ℝ ℝ j)
  rw [pderiv_mul' contDiff_const hsm, pderiv_const, zero_mul, zero_add,
    pderiv_mul' sm_exp_qd (contDiff_apply ℝ ℝ j), pderiv_exp_qd, pderiv_coord]
  simp only [chr_eq, pderiv_W, Fin.sum_univ_two, qd, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp <;> ring

theorem beRicci_eq (i j : Fin 2) (x : Rd 2) :
    confRiem.beRicci i j x = if i = j then 4 * (Real.exp (qd x) * (1 + qd x)) - 2 else 0 := by
  unfold RiemData.beRicci
  rw [ricci_eq, hess_W]
  by_cases h : i = j
  · simp [h]; ring
  · simp [h]

/-- **`Ric + ∇∇W ≥ 2 g` for the conformal plane** hence `CD(2,∞)` (`Curv 2`) for the formula-defined `Γ₂`. -/
theorem curv : confRiem.Curv 2 := by
  refine confRiem.riem_curv_of_ricci fun x ξ => ?_
  simp only [beRicci_eq, gl_eq, Fin.sum_univ_two]
  have h1 : 1 ≤ Real.exp (qd x) := Real.one_le_exp (qd_nonneg x)
  have h0 := qd_nonneg x
  have h2 : 0 ≤ ξ 0 ^ 2 + ξ 1 ^ 2 := by positivity
  simp
  nlinarith [mul_nonneg h2 (sub_nonneg.2 h1), mul_nonneg h2 (mul_nonneg (Real.exp_pos (qd x)).le h0)]

end confRiem

/-! ### The conditional Riemannian theorems on the non-flat example -/

/-- **Poincaré inequality** for `(ℝ², e^{|x|²}δ, e^{-2e^{|x|²}} dμ_g)` with constant `1/2`, under the named hypothesis
`WeakHypo` (Def. 3.3.8; not proved here). -/
theorem confRiem_poincare (hH : confRiem.WeakHypo) : confRiem.riemDiff.PI (1 / 2) := by
  have := confRiem.riem_poincare (ρ := 2) (by norm_num) confRiem.curv hH
  simpa using this

theorem confRiem_spectralGap (hH : confRiem.WeakHypo) :
    (DiffusionTriple.formData confRiem.riemDiff).HasSpectralGap 2 :=
  confRiem.riem_spectralGap (by norm_num) confRiem.curv hH

theorem confRiem_expDecay (hH : confRiem.WeakHypo) :
    (DiffusionTriple.formData confRiem.riemDiff).HasExpDecay 2 :=
  confRiem.riem_expDecay (by norm_num) confRiem.curv hH

/-- `CD(2,∞)` of the Full triple under `WeakHypo` and `F8` (named hypotheses) -/
theorem confRiem_CD (hH : confRiem.WeakHypo) (h8 : confRiem.F8) :
    (confRiem.riemFull hH h8).CD 2 ∞ := confRiem.riemFull_CD hH h8 confRiem.curv

end MarkovTriple.BGL.Instances.Riemannian
