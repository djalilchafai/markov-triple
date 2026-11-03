import MarkovTriple.BGL.Instances.GibbsRd.SobCore

/-!
# `C^m` representative for compactly supported `F` with `HasSobL1 (m + d) F` (R16 Sob, S4 core)

Induction on `m`: the first derivatives of `F_n = F ⋆ ρ_n` are `(∂_i F) ⋆ ρ_n`, which converge uniformly
by the case `m − 1`; `hasFDerivAt_of_tendstoUniformly` then shows the uniform limit of `F_n` is `C^1` with the
limit derivative, which is `C^{m-1}`.
-/

open MeasureTheory Filter Topology
open scoped ContDiff Convolution

namespace MarkovTriple.BGL.Instances.GibbsRd.Sob

variable {d : ℕ}

/-- the linear form `v ↦ Σ aᵢ vᵢ`. -/
noncomputable def lin (a : Fin d → ℝ) : (Fin d → ℝ) →L[ℝ] ℝ := ∑ i, a i • ContinuousLinearMap.proj i

theorem lin_apply (a v : Fin d → ℝ) : lin a v = ∑ i, a i * v i := by simp [lin]

theorem eq_lin (L : (Fin d → ℝ) →L[ℝ] ℝ) : L = lin (fun i => L (Pi.single i 1)) := by
  ext v
  rw [lin_apply]
  refine (L.pi_apply_eq_sum_univ v).trans ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (fun j => if i = j then (1 : ℝ) else 0) = Pi.single i 1 := by
    funext j; simp [Pi.single_apply, eq_comm]
  rw [this]; simp [mul_comm]

theorem lin_sub (a b : Fin d → ℝ) : lin a - lin b = lin (a - b) := by
  ext v
  simp [lin_apply, Finset.sum_sub_distrib, sub_mul]

theorem norm_lin_le (a : Fin d → ℝ) : ‖lin a‖ ≤ ∑ i, |a i| := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg fun i _ => abs_nonneg _) fun v => ?_
  rw [lin_apply, Real.norm_eq_abs]
  calc |∑ i, a i * v i| ≤ ∑ i, |a i * v i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |a i| * ‖v‖ := Finset.sum_le_sum fun i _ => by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (by simpa using norm_le_pi_norm v i) (abs_nonneg _)
    _ = (∑ i, |a i|) * ‖v‖ := by rw [Finset.sum_mul]

theorem tendstoUniformly_fderiv {ψ : ℕ → (Fin d → ℝ) → ℝ} {ĝ : Fin d → (Fin d → ℝ) → ℝ}
    (h : ∀ i, TendstoUniformly (fun n x => pd i (ψ n) x) (ĝ i) atTop) :
    TendstoUniformly (fun n x => fderiv ℝ (ψ n) x) (fun x => lin (fun i => ĝ i x)) atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have hd : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  have he : 0 < ε / ((d : ℝ) + 1) := div_pos hε hd
  have hev : ∀ᶠ n in atTop, ∀ i, ∀ x, dist (ĝ i x) (pd i (ψ n) x) < ε / ((d : ℝ) + 1) :=
    eventually_all.2 fun i => (Metric.tendstoUniformly_iff.1 (h i)) _ he
  filter_upwards [hev] with n hn x
  rw [dist_eq_norm, eq_lin (fderiv ℝ (ψ n) x), lin_sub]
  refine lt_of_le_of_lt (norm_lin_le _) ?_
  calc ∑ i, |(fun i => ĝ i x) i - (fun i => (fderiv ℝ (ψ n) x) (Pi.single i 1)) i|
      ≤ ∑ _i : Fin d, ε / ((d : ℝ) + 1) := Finset.sum_le_sum fun i _ => by
        have := hn i x
        rw [Real.dist_eq] at this
        exact this.le
    _ = (d : ℝ) * (ε / ((d : ℝ) + 1)) := by simp
    _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ hd]; nlinarith

theorem HasSobL1.mono_le : ∀ (j k : ℕ) {f : (Fin d → ℝ) → ℝ}, HasSobL1 (k + j) f → HasSobL1 k f
  | 0, _, _, h => h
  | j + 1, k, _, h => HasSobL1.mono_le j k (HasSobL1.mono (k + j) h)

theorem sob_core_contDiff {K0 : Set (Fin d → ℝ)} (hK0 : IsCompact K0) :
    ∀ (m : ℕ) {F : (Fin d → ℝ) → ℝ}, (∀ᵐ x, x ∉ K0 → F x = 0) → HasSobL1 (m + d) F →
    ∃ g : (Fin d → ℝ) → ℝ, ContDiff ℝ (m : WithTop ℕ∞) g ∧ F =ᵐ[volume] g ∧
      TendstoUniformly (fun n => mol F (rho n)) g atTop
  | 0, F, hF0, hF => by
    obtain ⟨g, hg, h1, h2⟩ := sob_core hK0 hF0 (by simpa using hF)
    exact ⟨g, by simpa using (contDiff_zero (𝕜 := ℝ)).2 hg, h1, h2⟩
  | m + 1, F, hF0, hF => by
    have hF' : HasSobL1 ((m + d) + 1) F := by rwa [show m + 1 + d = m + d + 1 by omega] at hF
    choose gi hgw hgk using hF'.2
    have hgi0 : ∀ i, ∀ᵐ x, x ∉ K0 → gi i x = 0 := fun i =>
      (hgw i).ae_zero_of_open hK0.isClosed.isOpen_compl
        (by filter_upwards [hF0] with x hx h using hx h)
    choose ĝ hĝ using fun i => sob_core_contDiff hK0 m (hgi0 i) (hgk i)
    obtain ⟨g, hgc, hgF, hgU⟩ := sob_core hK0 hF0
      (HasSobL1.mono_le (m + 1) d (by rwa [show d + (m + 1) = m + 1 + d by omega]))
    have hFloc : LocallyIntegrable F := hF.locallyIntegrable _
    have hsm : ∀ n, ContDiff ℝ ∞ (mol F (rho n)) := fun n =>
      contDiff_mol hFloc (contDiff_rho n) (hasCompactSupport_rho n)
    have hpd : ∀ n i, pd i (mol F (rho n)) = mol (gi i) (rho n) := fun n i =>
      pd_mol_weak (hgw i) (contDiff_rho n) (hasCompactSupport_rho n)
    have hfd := tendstoUniformly_fderiv (ψ := fun n => mol F (rho n)) (ĝ := ĝ) fun i => by
      simpa only [hpd] using (hĝ i).2.2
    have hder : ∀ x, HasFDerivAt g (lin fun i => ĝ i x) x := fun x =>
      hasFDerivAt_of_tendstoUniformly hfd
        (fun n x => ((hsm n).differentiable (by simp) x).hasFDerivAt)
        (fun x => hgU.tendsto_at x) x
    refine ⟨g, ?_, hgF, hgU⟩
    have hfe : fderiv ℝ g = fun x => lin fun i => ĝ i x := funext fun x => (hder x).fderiv
    have : ContDiff ℝ (m : WithTop ℕ∞) (fderiv ℝ g) := by
      rw [hfe]
      exact ContDiff.sum fun i _ => ((hĝ i).1).smul contDiff_const
    have h1 := contDiff_succ_iff_fderiv (𝕜 := ℝ) (n := (m : WithTop ℕ∞)) (f := g)
    push_cast
    refine h1.2 ⟨fun x => (hder x).differentiableAt, fun h => absurd h (by simp), this⟩

end MarkovTriple.BGL.Instances.GibbsRd.Sob
