import Mathlib
import MarkovTriple.BGL.Instances.OU.LSIBase
import MarkovTriple.BGL.Theory.ALevel

/-!
# OU log-Sobolev / gradient bound (Part 2): the Mehler functions `P_s φ` and their derivatives

For `φ ∈ C_c^∞` let `Uf φ s x = ∫ φ(e^{-s} x + √(1-e^{-2s}) y) dγ(y)` (the old OU Mehler transform).
* `Pt s φ = Uf φ s` everywhere for `s ≥ 0` (a.e. identity of `Pt_mehler` upgraded by continuity);
* `m0..m3 φ s x = ∂_x^k (P_s φ)`: bounded uniformly in `s ≥ 0`;
* `∂_s P_s φ = L P_s φ` pointwise for `s > 0`, and `∂_s ∂_x P_s φ = ∂_x L P_s φ`.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal Real
open MarkovTriple.Sanity.OU hiding A₀

local notation "OA₀" => MarkovTriple.Sanity.OU.A₀

namespace MarkovTriple.BGL.Instances.OU

noncomputable def ea (s : ℝ) : ℝ := Real.exp (-s)
noncomputable def ec (s : ℝ) : ℝ := √(1 - Real.exp (-s) ^ 2)
noncomputable def Uf (φ : ℝ → ℝ) (s x : ℝ) : ℝ := Mh (ea s) (ec s) φ x

lemma ea_pos (s : ℝ) : 0 < ea s := Real.exp_pos _

lemma ea_le_one {s : ℝ} (hs : 0 ≤ s) : ea s ≤ 1 := by
  unfold ea; exact Real.exp_le_one_iff.2 (by linarith)

lemma ea_cont : Continuous ea := by unfold ea; fun_prop

lemma ec_cont : Continuous ec := by unfold ec; fun_prop

lemma one_sub_pos {s : ℝ} (hs : 0 < s) : 0 < 1 - Real.exp (-s) ^ 2 := by
  have : Real.exp (-s) < 1 := by
    have := Real.exp_lt_exp.2 (show -s < 0 by linarith)
    simpa using this
  have h0 := Real.exp_pos (-s)
  nlinarith

lemma ec_pos {s : ℝ} (hs : 0 < s) : 0 < ec s := Real.sqrt_pos.2 (one_sub_pos hs)

lemma ec_mono {s t : ℝ} (_hs : 0 < s) (hst : s ≤ t) : ec s ≤ ec t := by
  unfold ec
  apply Real.sqrt_le_sqrt
  have h1 : Real.exp (-t) ≤ Real.exp (-s) := Real.exp_le_exp.2 (by linarith)
  have h0 := Real.exp_pos (-t)
  nlinarith

lemma hasDerivAt_ea (s : ℝ) : HasDerivAt ea (-ea s) s := by
  have := (hasDerivAt_neg s).exp
  refine (show HasDerivAt (fun s => Real.exp (-s)) _ s from this).congr_deriv ?_
  simp [ea]

lemma hasDerivAt_ec {s : ℝ} (hs : 0 < s) : HasDerivAt ec (ea s ^ 2 / ec s) s := by
  have h1 : HasDerivAt (fun s : ℝ => 1 - Real.exp (-s) ^ 2) (2 * ea s ^ 2) s := by
    have h := (hasDerivAt_ea s).pow 2
    have := (hasDerivAt_const s (1 : ℝ)).sub h
    refine this.congr_deriv ?_
    simp; ring
  have h2 := h1.sqrt (one_sub_pos hs).ne'
  refine (show HasDerivAt ec _ s from h2).congr_deriv ?_
  have : ec s ≠ 0 := (ec_pos hs).ne'
  have e : √(1 - Real.exp (-s) ^ 2) = ec s := rfl
  rw [e]; field_simp

lemma Uf_bound {φ : ℝ → ℝ} {B : ℝ} (hB : ∀ y, |φ y| ≤ B) (s x : ℝ) : |Uf φ s x| ≤ B := by
  unfold Uf Mh
  have := norm_integral_le_of_norm_le_const (μ := γ)
    (f := fun y => φ (ea s * x + ec s * y)) (C := B) (ae_of_all _ fun y => by simpa using hB _)
  simpa using this

lemma bdd_of_A₀ {φ : ℝ → ℝ} (hφ : φ ∈ OA₀) : ∃ B, ∀ y, |φ y| ≤ B := A₀.bdd hφ

/-! ### The functions `m_k = ∂_x^k P_s φ` -/

noncomputable def m0 (φ : ℝ → ℝ) (s x : ℝ) : ℝ := Uf φ s x
noncomputable def m1 (φ : ℝ → ℝ) (s x : ℝ) : ℝ := ea s * Uf (deriv φ) s x
noncomputable def m2 (φ : ℝ → ℝ) (s x : ℝ) : ℝ := ea s ^ 2 * Uf (deriv (deriv φ)) s x
noncomputable def m3 (φ : ℝ → ℝ) (s x : ℝ) : ℝ :=
  ea s ^ 3 * Uf (deriv (deriv (deriv φ))) s x

variable {φ : ℝ → ℝ}

lemma d0x (hφ : φ ∈ OA₀) (s x : ℝ) : HasDerivAt (m0 φ s) (m1 φ s x) x :=
  hasDerivAt_Mh hφ _ _ x

lemma d1x (hφ : φ ∈ OA₀) (s x : ℝ) : HasDerivAt (m1 φ s) (m2 φ s x) x := by
  have := (hasDerivAt_Mh (A₀.deriv_mem hφ) (ea s) (ec s) x).const_mul (ea s)
  refine (show HasDerivAt (m1 φ s) _ x from this).congr_deriv ?_
  simp only [m2, Uf]; ring

lemma d2x (hφ : φ ∈ OA₀) (s x : ℝ) : HasDerivAt (m2 φ s) (m3 φ s x) x := by
  have := (hasDerivAt_Mh (A₀.deriv_mem (A₀.deriv_mem hφ)) (ea s) (ec s) x).const_mul (ea s ^ 2)
  refine (show HasDerivAt (m2 φ s) _ x from this).congr_deriv ?_
  simp only [m3, Uf]; ring

lemma m0_cont (hφ : φ ∈ OA₀) (s : ℝ) : Continuous (m0 φ s) :=
  continuous_iff_continuousAt.2 fun x => (d0x hφ s x).continuousAt

lemma m1_cont (hφ : φ ∈ OA₀) (s : ℝ) : Continuous (m1 φ s) :=
  continuous_iff_continuousAt.2 fun x => (d1x hφ s x).continuousAt

lemma m2_cont (hφ : φ ∈ OA₀) (s : ℝ) : Continuous (m2 φ s) :=
  continuous_iff_continuousAt.2 fun x => (d2x hφ s x).continuousAt

lemma m3_cont (hφ : φ ∈ OA₀) (s : ℝ) : Continuous (m3 φ s) := by
  have h : Continuous (Uf (deriv (deriv (deriv φ))) s) :=
    continuous_iff_continuousAt.2 fun x =>
      (hasDerivAt_Mh (A₀.deriv_mem (A₀.deriv_mem (A₀.deriv_mem hφ))) (ea s) (ec s) x).continuousAt
  exact continuous_const.mul h

lemma deriv_m0 (hφ : φ ∈ OA₀) (s : ℝ) : deriv (m0 φ s) = m1 φ s :=
  funext fun x => (d0x hφ s x).deriv

lemma deriv_m1 (hφ : φ ∈ OA₀) (s : ℝ) : deriv (m1 φ s) = m2 φ s :=
  funext fun x => (d1x hφ s x).deriv

lemma sm_m0 (hφ : φ ∈ OA₀) (s : ℝ) : Sm (m0 φ s) := sm_Mh _ _ hφ

/-! ### Bounds, uniform in `s ≥ 0` -/

lemma m0_bd (hφ : φ ∈ OA₀) (S : Set ℝ) : Bd S (m0 φ) := by
  obtain ⟨B, hB⟩ := bdd_of_A₀ hφ
  exact ⟨B, fun s _ x => Uf_bound hB s x⟩

lemma abs_ea_pow_le {s : ℝ} (hs : 0 ≤ s) (n : ℕ) : |ea s ^ n| ≤ 1 := by
  rw [abs_pow, abs_of_pos (ea_pos s)]
  exact pow_le_one₀ (ea_pos s).le (ea_le_one hs)

lemma m1_bd (hφ : φ ∈ OA₀) {S : Set ℝ} (hS : S ⊆ Ici 0) : Bd S (m1 φ) := by
  obtain ⟨B, hB⟩ := bdd_of_A₀ (A₀.deriv_mem hφ)
  refine ⟨B, fun s hs x => ?_⟩
  have h1 := abs_ea_pow_le (hS hs) 1
  have h2 := Uf_bound hB s x
  have h0 : 0 ≤ B := (abs_nonneg _).trans h2
  simp only [m1, abs_mul]
  rw [pow_one] at h1
  calc |ea s| * |Uf (deriv φ) s x| ≤ 1 * B := mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
    _ = B := one_mul B

lemma m2_bd (hφ : φ ∈ OA₀) {S : Set ℝ} (hS : S ⊆ Ici 0) : Bd S (m2 φ) := by
  obtain ⟨B, hB⟩ := bdd_of_A₀ (A₀.deriv_mem (A₀.deriv_mem hφ))
  refine ⟨B, fun s hs x => ?_⟩
  have h1 := abs_ea_pow_le (hS hs) 2
  have h2 := Uf_bound hB s x
  simp only [m2, abs_mul]
  calc |ea s ^ 2| * |Uf (deriv (deriv φ)) s x| ≤ 1 * B :=
        mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
    _ = B := one_mul B

lemma m3_bd (hφ : φ ∈ OA₀) {S : Set ℝ} (hS : S ⊆ Ici 0) : Bd S (m3 φ) := by
  obtain ⟨B, hB⟩ := bdd_of_A₀ (A₀.deriv_mem (A₀.deriv_mem (A₀.deriv_mem hφ)))
  refine ⟨B, fun s hs x => ?_⟩
  have h1 := abs_ea_pow_le (hS hs) 3
  have h2 := Uf_bound hB s x
  simp only [m3, abs_mul]
  calc |ea s ^ 3| * |Uf (deriv (deriv (deriv φ))) s x| ≤ 1 * B :=
        mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
    _ = B := one_mul B

/-! ### Continuity in `s` and the `s`-derivative -/

lemma Uf_cont_s (hφ : φ ∈ OA₀) (x : ℝ) : Continuous (fun s => Uf φ s x) := by
  obtain ⟨B, hB⟩ := bdd_of_A₀ hφ
  unfold Uf Mh
  refine continuous_of_dominated (bound := fun _ => B) (fun s => ?_) (fun s => ae_of_all _ fun y => ?_)
    (integrable_const _) (ae_of_all _ fun y => ?_)
  · exact (hφ.1.continuous.comp (by fun_prop)).aestronglyMeasurable
  · simpa using hB _
  · exact hφ.1.continuous.comp (by
      have := ea_cont; have := ec_cont; fun_prop)

lemma m0_cont_s (hφ : φ ∈ OA₀) (x : ℝ) : Continuous (fun s => m0 φ s x) := Uf_cont_s hφ x

lemma m1_cont_s (hφ : φ ∈ OA₀) (x : ℝ) : Continuous (fun s => m1 φ s x) :=
  ea_cont.mul (Uf_cont_s (A₀.deriv_mem hφ) x)

lemma hasDerivAt_Uf_s (hφ : φ ∈ OA₀) {s : ℝ} (hs : 0 < s) (x : ℝ) :
    HasDerivAt (fun s => Uf φ s x) (m2 φ s x - x * m1 φ s x) s := by
  obtain ⟨D, hD⟩ := bdd_of_A₀ (A₀.deriv_mem hφ)
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD 0)
  have hs2 : 0 < s / 2 := half_pos hs
  have hKpos : 0 < ec (s / 2) := ec_pos hs2
  set K := (ec (s / 2))⁻¹ with hK
  have hK0 : 0 ≤ K := inv_nonneg.2 hKpos.le
  set S : Set ℝ := Ioo (s / 2) (s + 1) with hSdef
  have hS : S ∈ 𝓝 s := Ioo_mem_nhds (by linarith) (by linarith)
  have hφ' : Continuous (deriv φ) := (A₀.deriv_mem hφ).1.continuous
  set F : ℝ → ℝ → ℝ := fun s' y => φ (ea s' * x + ec s' * y) with hF
  set F' : ℝ → ℝ → ℝ := fun s' y => -(ea s' * x) * deriv φ (ea s' * x + ec s' * y) +
    (ea s' ^ 2 / ec s') * (y * deriv φ (ea s' * x + ec s' * y)) with hF'
  have hd : ∀ y, ∀ s' ∈ S, HasDerivAt (fun s' => F s' y) (F' s' y) s' := by
    intro y s' hs'
    have hs'0 : 0 < s' := by have := hs'.1; linarith
    have h1 : HasDerivAt (fun s' => ea s' * x + ec s' * y)
        (-ea s' * x + (ea s' ^ 2 / ec s') * y) s' :=
      ((hasDerivAt_ea s').mul_const x).add ((hasDerivAt_ec hs'0).mul_const y)
    have h2 := (hφ.1.hasDerivAt (ea s' * x + ec s' * y)).comp s' h1
    refine (show HasDerivAt (fun s' => F s' y) _ s' from h2).congr_deriv ?_
    simp only [hF']; ring
  have hb : ∀ y, ∀ s' ∈ S, ‖F' s' y‖ ≤ D * |x| + D * K * |y| := by
    intro y s' hs'
    have hs'0 : 0 < s' := by have := hs'.1; linarith
    have hea : |ea s'| ≤ 1 := by
      rw [abs_of_pos (ea_pos s')]; exact ea_le_one hs'0.le
    have hea2 : ea s' ^ 2 ≤ 1 := by
      have := ea_pos s'; have := ea_le_one hs'0.le; nlinarith
    have hec : 0 < ec s' := ec_pos hs'0
    have hecK : (ec s')⁻¹ ≤ K := by
      rw [hK]; exact inv_anti₀ hKpos (ec_mono hs2 hs'.1.le)
    have hd1 := hD (ea s' * x + ec s' * y)
    rw [Real.norm_eq_abs]
    have e1 : |-(ea s' * x) * deriv φ (ea s' * x + ec s' * y)| ≤ D * |x| := by
      rw [abs_mul, abs_neg, abs_mul]
      calc |ea s'| * |x| * |deriv φ _| ≤ 1 * |x| * D :=
            mul_le_mul (mul_le_mul_of_nonneg_right hea (abs_nonneg _)) hd1 (abs_nonneg _)
              (by positivity)
        _ = D * |x| := by ring
    have e2 : |(ea s' ^ 2 / ec s') * (y * deriv φ (ea s' * x + ec s' * y))| ≤ D * K * |y| := by
      rw [abs_mul, abs_mul, abs_div, abs_of_pos hec, abs_of_nonneg (by positivity : 0 ≤ ea s' ^ 2)]
      have h3 : ea s' ^ 2 / ec s' ≤ K := by
        calc ea s' ^ 2 / ec s' ≤ 1 / ec s' := by gcongr
          _ = (ec s')⁻¹ := one_div _
          _ ≤ K := hecK
      calc ea s' ^ 2 / ec s' * (|y| * |deriv φ _|) ≤ K * (|y| * D) := by
            apply mul_le_mul h3 (mul_le_mul_of_nonneg_left hd1 (abs_nonneg _))
              (by positivity) hK0
        _ = D * K * |y| := by ring
    exact (abs_add_le _ _).trans (add_le_add e1 e2)
  have hint1 : Integrable (fun y => deriv φ (ea s * x + ec s * y)) γ :=
    integrable_comp_mh (A₀.deriv_mem hφ) _ _ x
  have hint2 : Integrable (fun y => y * deriv φ (ea s * x + ec s * y)) γ := by
    refine integrable_lin (C := D) ((measurable_id.mul
      ((hφ'.comp (by have := ea_cont; have := ec_cont; fun_prop)).measurable)).aestronglyMeasurable)
      fun y => ?_
    rw [abs_mul]
    calc |y| * |deriv φ _| ≤ |y| * D := mul_le_mul_of_nonneg_left (hD _) (abs_nonneg _)
      _ ≤ D * (1 + |y|) := by nlinarith [abs_nonneg y]
  have hbd : Integrable (fun y : ℝ => D * |x| + D * K * |y|) γ :=
    (integrable_const _).add (by simpa using (integrable_pow_abs 1).const_mul (D * K))
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := γ) (F := F) (F' := F')
    (x₀ := s) (s := S) (bound := fun y => D * |x| + D * K * |y|) hS
    (Eventually.of_forall fun s' =>
      (hφ.1.continuous.comp (by have := ea_cont; have := ec_cont; fun_prop)).aestronglyMeasurable)
    (integrable_comp_mh hφ _ _ x)
    ((by have := ea_cont; have := ec_cont; fun_prop : Continuous (F' s)).aestronglyMeasurable)
    (ae_of_all _ fun y s' hs' => hb y s' hs')
    hbd
    (ae_of_all _ fun y s' hs' => hd y s' hs')
  refine (show HasDerivAt (fun s => Uf φ s x) _ s from key.2).congr_deriv ?_
  -- compute the integral
  have hG : ∀ y, HasDerivAt (fun y => deriv φ (ea s * x + ec s * y))
      (ec s * deriv (deriv φ) (ea s * x + ec s * y)) y := by
    intro y
    have h1 : HasDerivAt (fun y => ea s * x + ec s * y) (ec s) y := by
      simpa using ((hasDerivAt_id y).const_mul (ec s)).const_add (ea s * x)
    have h2 := ((A₀.deriv_mem hφ).1.hasDerivAt (ea s * x + ec s * y)).comp y h1
    exact (show HasDerivAt (fun y => deriv φ (ea s * x + ec s * y)) _ y from h2).congr_deriv
      (mul_comm _ _)
  obtain ⟨D2, hD2⟩ := bdd_of_A₀ (A₀.deriv_mem (A₀.deriv_mem hφ))
  have hib := ibpγ hG ⟨D, fun y => hD _⟩ ⟨|ec s| * D2, fun y => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hD2 _) (abs_nonneg _)⟩
  have hint3 : Integrable (fun y => ec s * deriv (deriv φ) (ea s * x + ec s * y)) γ :=
    (integrable_comp_mh (A₀.deriv_mem (A₀.deriv_mem hφ)) _ _ x).const_mul _
  have hyG : ∫ y, y * deriv φ (ea s * x + ec s * y) ∂γ =
      ec s * ∫ y, deriv (deriv φ) (ea s * x + ec s * y) ∂γ := by
    have h0 : ∫ y, (ec s * deriv (deriv φ) (ea s * x + ec s * y) -
        y * deriv φ (ea s * x + ec s * y)) ∂γ = 0 := hib.2
    rw [integral_sub hint3 hint2, integral_const_mul] at h0
    linarith
  have hI : ∫ y, F' s y ∂γ = -(ea s * x) * ∫ y, deriv φ (ea s * x + ec s * y) ∂γ +
      (ea s ^ 2 / ec s) * ∫ y, y * deriv φ (ea s * x + ec s * y) ∂γ := by
    simp only [hF']
    rw [integral_add (hint1.const_mul _) (hint2.const_mul _), integral_const_mul,
      integral_const_mul]
  have hec : ec s ≠ 0 := (ec_pos hs).ne'
  rw [hI, hyG]
  simp only [m2, m1, Uf, Mh]
  field_simp
  ring

lemma hasDerivAt_m1_s (hφ : φ ∈ OA₀) {s : ℝ} (hs : 0 < s) (x : ℝ) :
    HasDerivAt (fun s => m1 φ s x) (m3 φ s x - x * m2 φ s x - m1 φ s x) s := by
  have h := (hasDerivAt_ea s).mul (hasDerivAt_Uf_s (A₀.deriv_mem hφ) hs x)
  refine (show HasDerivAt (fun s => m1 φ s x) _ s from h).congr_deriv ?_
  simp only [m1, m2, m3, Uf]
  ring

lemma hasDerivAt_m0_s (hφ : φ ∈ OA₀) {s : ℝ} (hs : 0 < s) (x : ℝ) :
    HasDerivAt (fun s => m0 φ s x) (m2 φ s x - x * m1 φ s x) s :=
  hasDerivAt_Uf_s hφ hs x

/-! ### Identification of `Pt` with the Mehler functions; `Γ`, `Γ₂` of explicit functions -/

lemma ΓA_eq_of_hasDeriv {g g1 : ℝ → ℝ} (hg : Sm g) (h : ∀ x, HasDerivAt g (g1 x) x) :
    ouDiff.ΓA g g = fun x => g1 x * g1 x := by
  rw [ouDiff_ΓA hg hg]
  funext x
  simp only [Go, (h x).deriv]

lemma Γ₂_eq_of_hasDeriv {g g1 g2 : ℝ → ℝ} (hg : Sm g) (h1 : ∀ x, HasDerivAt g (g1 x) x)
    (h2 : ∀ x, HasDerivAt g1 (g2 x) x) (x : ℝ) :
    ouDiff.Γ₂ g g x = g2 x ^ 2 + g1 x ^ 2 := by
  rw [ou_Γ₂_eq hg x]
  have e1 : deriv g = g1 := funext fun x => (h1 x).deriv
  rw [e1, (h2 x).deriv]

/-- `P_r φ` (the chosen `𝒜`-representative) is the Mehler function, everywhere. -/
theorem Pt_eq_Uf (φ : ouFull.A₀) (r : ℝ≥0) : ouFull.Pt r φ = Uf φ.1 (r : ℝ) := by
  have h1 := ouFull.Pt_ae r φ
  have h2 := Pt_mehler r φ.2 (ouDiff.cls φ) (DiffusionTriple.coeFn_cls ouDiff φ)
  have h3 : ouFull.Pt r φ =ᵐ[γ] Uf φ.1 (r : ℝ) := h1.symm.trans h2
  have hc1 : Continuous (ouFull.Pt r φ) := (show Sm _ from ouFull.Pt_mem_A r φ).continuous
  have hc2 : Continuous (Uf φ.1 (r : ℝ)) := m0_cont φ.2 _
  exact (Continuous.ae_eq_iff_eq γ hc1 hc2).1 h3

theorem Pt_eq_m0 (φ : ouFull.A₀) {s : ℝ} (hs : 0 ≤ s) : ouFull.Pt s.toNNReal φ = m0 φ.1 s := by
  rw [Pt_eq_Uf, Real.coe_toNNReal s hs]; rfl

end MarkovTriple.BGL.Instances.OU
