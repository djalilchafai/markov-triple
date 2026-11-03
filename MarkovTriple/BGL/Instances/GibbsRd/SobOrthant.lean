import MarkovTriple.BGL.Instances.GibbsRd.SobDefs

/-!
# Sobolev inequality `‖φ‖_∞ ≤ ‖∂_0 ⋯ ∂_{d-1} φ‖_{L¹}` for `φ ∈ C_c^∞(ℝ^d)` (R16 Sob, S1)

Induction on `d` by slicing `x = (x₀, x')` (`Fin.cons`) and the 1-D fundamental theorem of calculus
(`HasCompactSupport.integral_Iic_deriv_eq`), then Fubini through `MeasurableEquiv.piFinSuccAbove`.
-/

open MeasureTheory
open scoped ContDiff

namespace MarkovTriple.BGL.Instances.GibbsRd.Sob

variable {d : ℕ}

theorem hasDerivAt_line {ψ : (Fin d → ℝ) → ℝ} {x : Fin d → ℝ} (hψ : DifferentiableAt ℝ ψ x)
    (v : Fin d → ℝ) : HasDerivAt (fun t : ℝ => ψ (x + t • v)) (fderiv ℝ ψ x v) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  exact (hψ.hasFDerivAt).comp_hasDerivAt_of_eq 0 h1 (by simp)

theorem cons_line (s : ℝ) (x : Fin d → ℝ) (t : ℝ) (j : Fin d) :
    (Fin.cons s (x + t • Pi.single j 1) : Fin (d + 1) → ℝ)
      = (Fin.cons s x : Fin (d + 1) → ℝ) + t • Pi.single j.succ 1 := by
  ext i
  refine Fin.cases ?_ (fun k => ?_) i
  · simp
  · simp [Pi.single_apply]

theorem contDiff_cons (s : ℝ) : ContDiff ℝ ∞ (fun y : Fin d → ℝ => (Fin.cons s y : Fin (d + 1) → ℝ)) := by
  refine contDiff_pi.2 fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using contDiff_const
  · simpa using contDiff_apply ℝ ℝ j

theorem contDiff_slice {ψ : (Fin (d + 1) → ℝ) → ℝ} (h : ContDiff ℝ ∞ ψ) (s : ℝ) :
    ContDiff ℝ ∞ (fun y : Fin d → ℝ => ψ (Fin.cons s y)) :=
  h.comp (contDiff_cons s)

theorem hasCompactSupport_slice {ψ : (Fin (d + 1) → ℝ) → ℝ} (h : HasCompactSupport ψ) (s : ℝ) :
    HasCompactSupport (fun y : Fin d → ℝ => ψ (Fin.cons s y)) := by
  refine HasCompactSupport.intro (K := (fun z : Fin (d + 1) → ℝ => Fin.tail z) '' tsupport ψ)
    (h.isCompact.image (by fun_prop)) ?_
  intro y hy
  by_contra hne
  apply hy
  refine ⟨Fin.cons s y, subset_tsupport _ hne, ?_⟩
  simp

theorem pd_succ_slice {ψ : (Fin (d + 1) → ℝ) → ℝ} (hψ : Differentiable ℝ ψ) (s : ℝ) (j : Fin d)
    (y : Fin d → ℝ) :
    pd j.succ ψ (Fin.cons s y) = pd j (fun z => ψ (Fin.cons s z)) y := by
  have hs : Differentiable ℝ (fun z : Fin d → ℝ => ψ (Fin.cons s z)) :=
    hψ.comp ((contDiff_cons s).differentiable (by simp))
  have h1 := hasDerivAt_line (hs y) (Pi.single j 1)
  have h2 := hasDerivAt_line (hψ (Fin.cons s y)) (Pi.single j.succ 1)
  have : (fun t : ℝ => ψ (Fin.cons s (y + t • Pi.single j 1)))
      = (fun t : ℝ => ψ ((Fin.cons s y : Fin (d + 1) → ℝ) + t • Pi.single j.succ 1)) := by
    funext t; rw [cons_line]
  rw [this] at h1
  exact (h2.unique h1)

theorem hasDerivAt_slice0 {ψ : (Fin (d + 1) → ℝ) → ℝ} (hψ : Differentiable ℝ ψ) (t : ℝ)
    (y : Fin d → ℝ) :
    HasDerivAt (fun u : ℝ => ψ (Fin.cons u y)) (pd 0 ψ (Fin.cons t y)) t := by
  have hg : HasDerivAt (fun u : ℝ => (Fin.cons u y : Fin (d + 1) → ℝ)) (Pi.single 0 1) t := by
    rw [hasDerivAt_pi]
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using hasDerivAt_id' t
    · simpa using hasDerivAt_const t (y j)
  exact (hψ (Fin.cons t y)).hasFDerivAt.comp_hasDerivAt t hg

theorem iterD_slice (l : List (Fin d)) {ψ : (Fin (d + 1) → ℝ) → ℝ} (hψ : ContDiff ℝ ∞ ψ) (s : ℝ)
    (y : Fin d → ℝ) :
    iterD (l.map Fin.succ) ψ (Fin.cons s y) = iterD l (fun z => ψ (Fin.cons s z)) y := by
  induction l generalizing y with
  | nil => rfl
  | cons i l ih =>
    have hd : Differentiable ℝ (iterD (l.map Fin.succ) ψ) :=
      (contDiff_iterD _ hψ).differentiable (by simp)
    simp only [List.map_cons, iterD]
    rw [pd_succ_slice hd]
    congr 1
    funext z
    exact ih z

theorem contDiff_cons_first (y : Fin d → ℝ) :
    ContDiff ℝ ∞ (fun u : ℝ => (Fin.cons u y : Fin (d + 1) → ℝ)) := by
  refine contDiff_pi.2 fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Fin.cons_zero]; exact contDiff_id
  · simpa using contDiff_const

theorem hasCompactSupport_first {ψ : (Fin (d + 1) → ℝ) → ℝ} (h : HasCompactSupport ψ)
    (y : Fin d → ℝ) : HasCompactSupport (fun u : ℝ => ψ (Fin.cons u y)) := by
  refine HasCompactSupport.intro (K := (fun z : Fin (d + 1) → ℝ => z 0) '' tsupport ψ)
    (h.isCompact.image (by fun_prop)) ?_
  intro u hu
  by_contra hne
  apply hu
  exact ⟨Fin.cons u y, subset_tsupport _ hne, by simp⟩

/-- 1-D step: `|ψ(s)| ≤ ∫ |ψ'|` for `ψ ∈ C_c^∞(ℝ)`. -/
theorem abs_le_integral_deriv {h : ℝ → ℝ} (hh : ContDiff ℝ 1 h) (hc : HasCompactSupport h) (s : ℝ) :
    |h s| ≤ ∫ t, |deriv h t| := by
  have hI : Integrable (fun t => deriv h t) :=
    (hh.continuous_deriv le_rfl).integrable_of_hasCompactSupport hc.deriv
  rw [← hc.integral_Iic_deriv_eq hh s]
  calc |∫ x in Set.Iic s, deriv h x| ≤ ∫ x in Set.Iic s, |deriv h x| := by
        simpa using norm_integral_le_integral_norm (μ := volume.restrict (Set.Iic s)) (fun x => deriv h x)
    _ ≤ ∫ t, |deriv h t| :=
        setIntegral_le_integral hI.abs (Filter.Eventually.of_forall fun _ => abs_nonneg _)

theorem abs_le_integral_mixD : ∀ (d : ℕ) (φ : (Fin d → ℝ) → ℝ), ContDiff ℝ ∞ φ →
    HasCompactSupport φ → ∀ x, |φ x| ≤ ∫ y, |iterD (List.finRange d) φ y|
  | 0, φ, _, _, x => by
    have hx : x = default := Subsingleton.elim _ _
    have hv : (volume : Measure (Fin 0 → ℝ)) = Measure.dirac default := by
      rw [volume_pi, Measure.pi_of_empty]
      congr 1
      exact Subsingleton.elim _ _
    rw [hv, integral_dirac, hx]
    simp [iterD]
  | d + 1, φ, hφ, hc, x => by
    set ψ := iterD ((List.finRange d).map Fin.succ) φ with hψdef
    have hψ : ContDiff ℝ ∞ ψ := contDiff_iterD _ hφ
    have hψc : HasCompactSupport ψ := hasCompactSupport_iterD _ hc
    have hfr : iterD (List.finRange (d + 1)) φ = pd 0 ψ := by
      rw [List.finRange_succ]; rfl
    have hDc : Continuous (pd 0 ψ) := (contDiff_pd 0 hψ).continuous
    have hDcs : HasCompactSupport (pd 0 ψ) := hasCompactSupport_pd 0 hψc
    -- IH on the slice
    have h1 := abs_le_integral_mixD d (fun z => φ (Fin.cons (x 0) z)) (contDiff_slice hφ _)
      (hasCompactSupport_slice hc _) (Fin.tail x)
    have hx : (Fin.cons (x 0) (Fin.tail x) : Fin (d + 1) → ℝ) = x := Fin.cons_self_tail x
    rw [hx] at h1
    have h2 : ∀ y, iterD (List.finRange d) (fun z => φ (Fin.cons (x 0) z)) y
        = ψ (Fin.cons (x 0) y) := fun y => by
      rw [hψdef, iterD_slice _ hφ]
    simp only [h2] at h1
    refine h1.trans ?_
    -- Fubini
    have hGint : Integrable (fun y => |pd 0 ψ y|) :=
      (hDc.abs).integrable_of_hasCompactSupport (by simpa using hDcs.norm)
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0
    have hmp : MeasurePreserving e volume (volume.prod volume) :=
      volume_preserving_piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0
    have hesymm : ∀ (t : ℝ) (y : Fin d → ℝ), e.symm (t, y) = Fin.cons t y := fun t y => by
      simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply]
      rfl
    have hFint : Integrable (fun p : ℝ × (Fin d → ℝ) => |pd 0 ψ (Fin.cons p.1 p.2)|)
        (volume.prod volume) := by
      have := (hmp.symm e).integrable_comp_emb (g := fun y => |pd 0 ψ y|) e.symm.measurableEmbedding
      have h3 := this.2 hGint
      refine h3.congr (Filter.Eventually.of_forall fun p => ?_)
      simp [Function.comp, hesymm]
    have hint : ∫ y, |pd 0 ψ y| = ∫ y', ∫ t, |pd 0 ψ (Fin.cons t y')| := by
      have h4 := hmp.integral_comp' (g := fun p : ℝ × (Fin d → ℝ) => |pd 0 ψ (Fin.cons p.1 p.2)|)
      have h5 : ∀ y, |pd 0 ψ (Fin.cons (e y).1 (e y).2)| = |pd 0 ψ y| := fun y => by
        have : (Fin.cons (e y).1 (e y).2 : Fin (d + 1) → ℝ) = y := by
          have := hesymm (e y).1 (e y).2
          rw [← this]; simp
        rw [this]
      simp only [h5] at h4
      rw [h4, integral_prod_symm _ hFint]
    rw [hfr, hint]
    have hslice_int : Integrable (fun y' => |ψ (Fin.cons (x 0) y')|) := by
      refine (((hψ.continuous.comp (contDiff_cons (x 0)).continuous).abs)).integrable_of_hasCompactSupport ?_
      simpa using (hasCompactSupport_slice hψc (x 0)).norm
    refine integral_mono hslice_int hFint.integral_prod_right (fun y' => ?_)
    have hsm : ContDiff ℝ 1 (fun u : ℝ => ψ (Fin.cons u y')) :=
      ((hψ.comp (contDiff_cons_first y')).of_le (by simp))
    have hsc : HasCompactSupport (fun u : ℝ => ψ (Fin.cons u y')) :=
      hasCompactSupport_first hψc y'
    have := abs_le_integral_deriv hsm hsc (x 0)
    refine this.trans (le_of_eq ?_)
    congr 1
    funext t
    rw [(hasDerivAt_slice0 (hψ.differentiable (by simp)) t y').deriv]

end MarkovTriple.BGL.Instances.GibbsRd.Sob
