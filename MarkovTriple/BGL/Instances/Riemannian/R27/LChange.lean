import Mathlib
import MarkovTriple.BGL.Instances.Riemannian.R27.Piola

/-!
# `L = (1/w) ∂ᵢ (w g^{ij} ∂ⱼ ·)` is a scalar under a change of chart (BGL Appendix C.3), any dimension `d`

Given a transition `τ` of class `C²` with the pushforward laws `g_b ∘ τ = J g_a Jᵀ` and `w_a = (w_b ∘ τ) |det J|`
(`J = Dτ`, co-metric `g`, density `w = det(g)^{-1/2}`), the vector fields `W_a = w_a g_a ∇(F∘τ)` and `V_b = w_b g_b ∇F`
are related by `W_a = sgn(det J) · adj(J) (V_b ∘ τ)`; the Piola identity `Σₖ ∂ₖ adj(J)_{ki} = 0`
(`piola_identity`) gives `div W_a = sgn(det J) det J · (div V_b) ∘ τ`, whence `L_a (F∘τ) = (L_b F) ∘ τ`.
-/

open MarkovTriple.BGL (pderiv)
open Filter Topology

namespace MarkovTriple.BGL.Instances.Riemannian.R27

section algebra
open Matrix

lemma adj_mulVec_alg {n : Type*} [Fintype n] [DecidableEq n] (J G : Matrix n n ℝ) (u : n → ℝ) (k : n) :
    ∑ i, J.adjugate k i * ∑ m, (∑ p, ∑ l, J i p * G p l * J m l) * u m =
      J.det * ∑ l, G k l * ∑ i, u i * J i l := by
  have h1 : ∀ i, ∑ m, (∑ p, ∑ l, J i p * G p l * J m l) * u m = (J *ᵥ (G *ᵥ (Jᵀ *ᵥ u))) i := by
    intro i
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Finset.mul_sum, Finset.sum_mul]
    calc _ = ∑ m, ∑ p, ∑ l, J i p * G p l * J m l * u m := rfl
      _ = ∑ p, ∑ m, ∑ l, J i p * G p l * J m l * u m := Finset.sum_comm
      _ = _ := by
            refine Finset.sum_congr rfl fun p _ => ?_
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
            ring
  have h2 : ∑ i, J.adjugate k i * (J *ᵥ (G *ᵥ (Jᵀ *ᵥ u))) i =
      (J.adjugate *ᵥ (J *ᵥ (G *ᵥ (Jᵀ *ᵥ u)))) k := by
    simp [Matrix.mulVec, dotProduct]
  simp only [h1]
  rw [h2, Matrix.mulVec_mulVec, Matrix.adjugate_mul]
  simp only [Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul, Matrix.one_mulVec]
  congr 1
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  congr 1
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

lemma sum_J_adj {n : Type*} [Fintype n] [DecidableEq n] (J : Matrix n n ℝ) (l i : n) :
    ∑ k, J l k * J.adjugate k i = if l = i then J.det else 0 := by
  have := congrFun (congrFun (Matrix.mul_adjugate J) l) i
  simpa [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply] using this

end algebra

variable {d : ℕ}

/-- the carré du champ is a scalar under a change of chart (restatement of `R26.gamma_chart_change` with `Gch`) -/
theorem Gch_chart_change (ga gb : Fin d → Fin d → Ev d → ℝ) (τ : Ev d → Ev d) (F H : Ev d → ℝ) (x : Ev d)
    (hτ : DifferentiableAt ℝ τ x) (hF : DifferentiableAt ℝ F (τ x)) (hH : DifferentiableAt ℝ H (τ x))
    (hg : ∀ i j, gb i j (τ x) = ∑ k, ∑ l, jac τ x i k * ga k l x * jac τ x j l) :
    Gch gb F H (τ x) = Gch ga (F ∘ τ) (H ∘ τ) x :=
  R26.gamma_chart_change ga gb τ F H x hτ hF hH hg

/-- pointwise relation between the two vector fields `W_a`, `V_b` -/
lemma W_identity (ga gb : Fin d → Fin d → Ev d → ℝ) (wa wb : Ev d → ℝ) (τ : Ev d → Ev d) (F : Ev d → ℝ)
    (z : Ev d) (s : ℝ) (hs : |(jac τ z).det| = s * (jac τ z).det)
    (hτ : DifferentiableAt ℝ τ z) (hF : DifferentiableAt ℝ F (τ z))
    (hg : ∀ i j, gb i j (τ z) = ∑ k, ∑ l, jac τ z i k * ga k l z * jac τ z j l)
    (hw : wa z = wb (τ z) * |(jac τ z).det|) (k : Fin d) :
    wa z * ∑ j, ga k j z * pderiv (F ∘ τ) j z =
      s * ∑ i, (jac τ z).adjugate k i * (wb (τ z) * ∑ m, gb i m (τ z) * pderiv F m (τ z)) := by
  have hc : ∀ l, pderiv (F ∘ τ) l z = ∑ i, pderiv F i (τ z) * jac τ z i l := fun l =>
    R26.pderiv_comp_eq τ F z hτ hF l
  have h1 : ∑ i, (jac τ z).adjugate k i * (wb (τ z) * ∑ m, gb i m (τ z) * pderiv F m (τ z)) =
      wb (τ z) * ((jac τ z).det * ∑ l, ga k l z * ∑ i, pderiv F i (τ z) * jac τ z i l) := by
    rw [← adj_mulVec_alg (jac τ z) (fun p l => ga p l z) (fun m => pderiv F m (τ z)) k, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hg]
    ring
  rw [h1, hw, hs]
  simp only [hc]
  ring

/-- **`L` is a scalar under a change of chart** (any dimension; `τ ∈ C²`, `g, w ∈ C¹`). -/
theorem Lch_chart_change (ga gb : Fin d → Fin d → Ev d → ℝ) (wa wb : Ev d → ℝ) (τ : Ev d → Ev d)
    (F : Ev d → ℝ) (x : Ev d)
    (hτ : ContDiffAt ℝ 2 τ x) (hF : ContDiffAt ℝ 2 F (τ x))
    (_hga : ∀ i j, ContDiffAt ℝ 1 (ga i j) x) (_hwa : ContDiffAt ℝ 1 wa x)
    (hgb : ∀ i j, ContDiffAt ℝ 1 (gb i j) (τ x)) (hwb : ContDiffAt ℝ 1 wb (τ x))
    (hwa0 : wa x ≠ 0)
    (hg : ∀ᶠ z in 𝓝 x, ∀ i j, gb i j (τ z) = ∑ k, ∑ l, jac τ z i k * ga k l z * jac τ z j l)
    (hw : ∀ᶠ z in 𝓝 x, wa z = wb (τ z) * |(jac τ z).det|) :
    Lch gb wb F (τ x) = Lch ga wa (F ∘ τ) x := by
  classical
  -- regularity
  have hτa : ∀ a, ContDiffAt ℝ 2 (fun y => τ y a) x := fun a => contDiffAt_pi.1 hτ a
  have hJc : ∀ a b, ContDiffAt ℝ 1 (fun y => jac τ y a b) x := fun a b => contDiffAt_pderiv (hτa a) b
  have hJd : ∀ a b, DifferentiableAt ℝ (fun y => jac τ y a b) x := fun a b =>
    (hJc a b).differentiableAt (by norm_num)
  have hτd : DifferentiableAt ℝ τ x := hτ.differentiableAt (by norm_num)
  have hτev : ∀ᶠ z in 𝓝 x, DifferentiableAt ℝ τ z :=
    (hτ.eventually (by norm_num)).mono fun z hz => hz.differentiableAt (by norm_num)
  have hFev : ∀ᶠ z in 𝓝 x, DifferentiableAt ℝ F (τ z) :=
    hτ.continuousAt.eventually ((hF.eventually (by norm_num)).mono fun y hy =>
      hy.differentiableAt (by norm_num))
  -- the determinant of the Jacobian
  have hdetc : ContinuousAt (fun z => (jac τ z).det) x := by
    have hM : ContinuousAt (fun z => jac τ z) x :=
      continuousAt_pi.2 fun a => continuousAt_pi.2 fun b => (hJc a b).continuousAt
    exact (Continuous.matrix_det continuous_id).continuousAt.comp hM
  have hdet0 : (jac τ x).det ≠ 0 := by
    intro h0
    have := hw.self_of_nhds
    rw [h0] at this
    simp at this
    exact hwa0 this
  obtain ⟨s, hs1, hs⟩ : ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
      ∀ᶠ z in 𝓝 x, |(jac τ z).det| = s * (jac τ z).det := by
    rcases lt_or_gt_of_ne hdet0 with h | h
    · refine ⟨-1, Or.inr rfl, ?_⟩
      filter_upwards [hdetc.eventually (gt_mem_nhds h)] with z hz
      rw [abs_of_neg hz]; ring
    · refine ⟨1, Or.inl rfl, ?_⟩
      filter_upwards [hdetc.eventually (lt_mem_nhds h)] with z hz
      rw [abs_of_pos hz]; ring
  have hsx := hs.self_of_nhds
  have hss : s * s = 1 := by rcases hs1 with h | h <;> rw [h] <;> norm_num
  -- the vector fields
  set V : Fin d → Ev d → ℝ := fun i y => wb y * ∑ m, gb i m y * pderiv F m y with hV
  have hVd : ∀ i, DifferentiableAt ℝ (V i) (τ x) := by
    intro i
    have hp : ∀ m, DifferentiableAt ℝ (pderiv F m) (τ x) := fun m =>
      (contDiffAt_pderiv hF m).differentiableAt (by norm_num)
    refine ((hwb.differentiableAt (by norm_num)).mul ?_)
    exact DifferentiableAt.fun_sum fun m _ => ((hgb i m).differentiableAt (by norm_num)).mul (hp m)
  have hadj : ∀ k i, DifferentiableAt ℝ (fun z => (jac τ z).adjugate k i) x := by
    intro k i
    simp_rw [Matrix.adjugate_apply]
    refine differentiableAt_det (fun y => (jac τ y).updateRow i (Pi.single k 1)) x ?_
    intro a b
    by_cases ha : a = i
    · subst ha; simp
    · simpa [Matrix.updateRow_apply, ha] using hJd a b
  have hVτ : ∀ i, DifferentiableAt ℝ (fun z => V i (τ z)) x := fun i => (hVd i).comp x hτd
  -- the divergence of `W`
  have hW : ∀ᶠ z in 𝓝 x, ∀ k, wa z * ∑ j, ga k j z * pderiv (F ∘ τ) j z =
      s * ∑ i, (jac τ z).adjugate k i * V i (τ z) := by
    filter_upwards [hg, hw, hs, hτev, hFev] with z hgz hwz hsz hτz hFz k
    exact W_identity ga gb wa wb τ F z s hsz hτz hFz hgz hwz k
  have hdivW : ∑ k, pderiv (fun y => wa y * ∑ j, ga k j y * pderiv (F ∘ τ) j y) k x =
      s * (jac τ x).det * ∑ i, pderiv (V i) i (τ x) := by
    have e1 : ∀ k, pderiv (fun y => wa y * ∑ j, ga k j y * pderiv (F ∘ τ) j y) k x =
        pderiv (fun z => s * ∑ i, (jac τ z).adjugate k i * V i (τ z)) k x := fun k =>
      pderiv_congr_eventually (hW.mono fun z hz => hz k) k
    have e2 : ∀ k, pderiv (fun z => s * ∑ i, (jac τ z).adjugate k i * V i (τ z)) k x =
        s * ∑ i, ((jac τ x).adjugate k i * pderiv (fun z => V i (τ z)) k x +
          V i (τ x) * pderiv (fun z => (jac τ z).adjugate k i) k x) := by
      intro k
      rw [pderiv_const_mul, pderiv_sum Finset.univ (F := fun i z => (jac τ z).adjugate k i * V i (τ z)) (fun i _ => (hadj k i).mul (hVτ i))]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [pderiv_mul (hadj k i) (hVτ i)]
    simp_rw [e1, e2]
    rw [← Finset.mul_sum]
    have p1 : ∑ k, ∑ i, V i (τ x) * pderiv (fun z => (jac τ z).adjugate k i) k x = 0 := by
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [← Finset.mul_sum, piola_identity τ x hτ i, mul_zero]
    have p2 : ∑ k, ∑ i, (jac τ x).adjugate k i * pderiv (fun z => V i (τ z)) k x =
        (jac τ x).det * ∑ i, pderiv (V i) i (τ x) := by
      have hc : ∀ i k, pderiv (fun z => V i (τ z)) k x = ∑ l, pderiv (V i) l (τ x) * jac τ x l k :=
        fun i k => R26.pderiv_comp_eq τ (V i) x hτd (hVd i) k
      simp_rw [hc, Finset.mul_sum]
      rw [Finset.sum_comm]
      have : ∀ i, ∑ k, ∑ l, (jac τ x).adjugate k i * (pderiv (V i) l (τ x) * jac τ x l k) =
          (jac τ x).det * pderiv (V i) i (τ x) := by
        intro i
        rw [Finset.sum_comm]
        have h2 : ∀ l, ∑ k, (jac τ x).adjugate k i * (pderiv (V i) l (τ x) * jac τ x l k) =
            pderiv (V i) l (τ x) * (if l = i then (jac τ x).det else 0) := by
          intro l
          rw [← sum_J_adj (jac τ x) l i, Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ring
        simp_rw [h2]
        rw [Finset.sum_eq_single i (fun l _ hl => by simp [hl]) (by simp)]
        simp [mul_comm]
      simp_rw [this]
    simp_rw [Finset.sum_add_distrib]
    rw [p1, add_zero, p2]
    ring
  -- conclusion
  unfold Lch
  rw [hdivW]
  have hwx : wa x = wb (τ x) * (s * (jac τ x).det) := by
    have := hw.self_of_nhds
    rwa [hsx] at this
  have hwb0 : wb (τ x) ≠ 0 := by
    intro h; apply hwa0; rw [hwx, h, zero_mul]
  have hsd : s * (jac τ x).det ≠ 0 := by
    intro h; apply hwa0; rw [hwx, h, mul_zero]
  rw [hwx]
  have hs0 : s ≠ 0 := by intro h; rw [h] at hss; norm_num at hss
  simp only [hV]
  field_simp
