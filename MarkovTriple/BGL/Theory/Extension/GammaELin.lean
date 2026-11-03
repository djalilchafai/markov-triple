import Mathlib
import MarkovTriple.BGL.Theory.Extension.ClosedProd
import MarkovTriple.BGL.Theory.Extension.SeqLin
import MarkovTriple.BGL.Theory.Extension.HessExtLin

/-!
# `Γ` on `𝒟(ℰ)`: bilinearity, bound, nonnegativity and Cauchy–Schwarz (BGL Prop. 3.1.5 / (3.1.10))

Round 15 gap closure; statements fixed in `Extension/STATEMENTS_R15_Gaps.md` (3b): `gammaE_lin_left/right`,
`gammaE_bound`, `gammaE_self_nonneg`, `gammaE_cs` (`|Γ(u,v)|² ≤ Γ(u)Γ(v)` a.e., obtained by passing to a.e.-convergent
subsequences in the pointwise inequality on `𝒜₀`, `G_cs_A₀`, i.e. ΓA_cs).  Symmetry is `gammaE_comm` (ClosedGamma).
-/

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal InnerProductSpace

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

namespace FullTriple

variable {T : FullTriple E}

lemma GG_lin_left (a a' b : T.A₀) (c : ℝ) : GG T (a + c • a') b = GG T a b + c • GG T a' b := by
  refine Lp.ext ?_
  filter_upwards [GG_ae (a + c • a') b, GG_ae a b, GG_ae a' b,
    Lp.coeFn_add (GG T a b) (c • GG T a' b), Lp.coeFn_smul c (GG T a' b),
    G_lin_left (A₀_memA a.2) (A₀_memA a'.2) c (A₀_memA b.2)] with x e1 e2 e3 e4 e5 e6
  rw [e4, Pi.add_apply, e5, Pi.smul_apply, e1, e2, e3, coe_lin, e6]
  rfl

/-- **Linearity of `Γ` on `𝒟(ℰ)` in the first slot.** -/
theorem gammaE_lin_left {u u' w v : T.formDomain} (c : ℝ) (hwe : w = u + c • u') :
    gammaE T w v = gammaE T u v + c • gammaE T u' v := by
  obtain ⟨a, ha⟩ := exists_formConv u
  obtain ⟨a', ha'⟩ := exists_formConv u'
  obtain ⟨b, hb⟩ := exists_formConv v
  have t1 := gammaE_tendsto (ha.lin c hwe ha') hb
  have t2 := (gammaE_tendsto ha hb).add ((gammaE_tendsto ha' hb).const_smul c)
  exact tendsto_nhds_unique t1 (t2.congr (fun k => (GG_lin_left (a k) (a' k) (b k) c).symm))

/-- **Linearity of `Γ` on `𝒟(ℰ)` in the second slot.** -/
theorem gammaE_lin_right {u v v' w : T.formDomain} (c : ℝ) (hwe : w = v + c • v') :
    gammaE T u w = gammaE T u v + c • gammaE T u v' := by
  rw [gammaE_comm u w, gammaE_comm u v, gammaE_comm u v']
  exact gammaE_lin_left c hwe

/-- `‖Γ(u,v)‖₁ ≤ ‖u‖_{𝒟(ℰ)} ‖v‖_{𝒟(ℰ)}` (Hilbert norm of `𝒟(ℰ)`). -/
theorem gammaE_bound (u v : T.formDomain) :
    ‖gammaE T u v‖ ≤ ‖(DiffusionTriple.formData T.toDiffusionTriple).qEquiv.symm u‖ *
      ‖(DiffusionTriple.formData T.toDiffusionTriple).qEquiv.symm v‖ := by
  obtain ⟨a, ha⟩ := exists_formConv u
  obtain ⟨b, hb⟩ := exists_formConv v
  have t1 := (gammaE_tendsto ha hb).norm
  have t2 := ha.norm.mul hb.norm
  refine le_of_tendsto_of_tendsto' t1 t2 (fun k => ?_)
  simpa using norm_GG_le (a k) (b k)

/-- `Γ(u) ≥ 0` a.e. on `𝒟(ℰ)`. -/
theorem gammaE_self_nonneg (u : T.formDomain) : 0 ≤ᵐ[T.μ] (gammaE T u u : E → ℝ) := by
  obtain ⟨a, ha⟩ := exists_formConv u
  have s := gammaE_tendsto ha ha
  have : Fact ((1 : ℝ≥0∞) ≤ 1) := ⟨le_rfl⟩
  obtain ⟨φ, hφ, h1⟩ := Lp_ae_subseq s
  have hall : ∀ᵐ x ∂T.μ, ∀ m, 0 ≤ (GG T (a m) (a m) : E → ℝ) x := by
    rw [ae_all_iff]
    intro m
    filter_upwards [GG_ae (a m) (a m), T.ΓA_nonneg _ (A₀_memA (a m).2)] with x h1 h2
    rw [h1]; exact h2
  filter_upwards [h1, hall] with x hx hn
  exact ge_of_tendsto' hx (fun m => hn (φ m))

/-- **Cauchy–Schwarz for `Γ` on `𝒟(ℰ)`** (BGL Prop. 3.1.5 / (3.1.10)): `Γ(u,v)² ≤ Γ(u) Γ(v)` a.e. -/
theorem gammaE_cs (u v : T.formDomain) :
    ∀ᵐ x ∂T.μ, ((gammaE T u v : Lp ℝ 1 T.μ) : E → ℝ) x ^ 2 ≤
      ((gammaE T u u : Lp ℝ 1 T.μ) : E → ℝ) x * ((gammaE T v v : Lp ℝ 1 T.μ) : E → ℝ) x := by
  obtain ⟨a, ha⟩ := exists_formConv u
  obtain ⟨b, hb⟩ := exists_formConv v
  have s1 := gammaE_tendsto ha hb
  have s2 := gammaE_tendsto ha ha
  have s3 := gammaE_tendsto hb hb
  have : Fact ((1 : ℝ≥0∞) ≤ 1) := ⟨le_rfl⟩
  obtain ⟨φ, hφ, a1, a2⟩ := Lp_ae_subseq_two s1 s2
  obtain ⟨ψ, hψ, a3, -⟩ := Lp_ae_subseq_two (s3.comp hφ.tendsto_atTop) (s3.comp hφ.tendsto_atTop)
  have hall : ∀ᵐ x ∂T.μ, ∀ m, ((GG T (a m) (b m) : Lp ℝ 1 T.μ) : E → ℝ) x ^ 2 ≤
      ((GG T (a m) (a m) : Lp ℝ 1 T.μ) : E → ℝ) x * ((GG T (b m) (b m) : Lp ℝ 1 T.μ) : E → ℝ) x := by
    rw [ae_all_iff]
    intro m
    filter_upwards [GG_ae (a m) (b m), GG_ae (a m) (a m), GG_ae (b m) (b m), G_cs_A₀ (a m) (b m)]
      with x h1 h2 h3 h4
    rw [h1, h2, h3]; exact h4
  filter_upwards [a1, a2, a3, hall] with x h1 h2 h3 h5
  have l1 := (h1.comp hψ.tendsto_atTop).pow 2
  have l2 := (h2.comp hψ.tendsto_atTop).mul h3
  exact le_of_tendsto_of_tendsto' l1 l2 (fun m => h5 (φ (ψ m)))

end FullTriple

end MarkovTriple.BGL
