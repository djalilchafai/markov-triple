import Mathlib
import MarkovTriple.BGL.Instances.GegenbauerOpen.Diffusion

/-!
# The extended algebra `𝒜` of the zonal Gegenbauer `FullTriple` (R23-G2), and local smooth modifications

`goA = {f : ℝ → ℝ | Measurable f ∧ ContDiffOn ℝ ⊤ f (Ioo (-1) 1)}`: smooth on the open interval, nothing at
the endpoints (and nothing outside).  See `STATEMENTS_R23_G2.md`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace MarkovTriple.BGL.Instances.GegenbauerOpen

/-- the extended algebra `𝒜`. -/
def goA : Subalgebra ℝ (ℝ → ℝ) where
  carrier := {f | Measurable f ∧ ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (Ioo (-1 : ℝ) 1)}
  mul_mem' := fun hf hg => ⟨hf.1.mul hg.1, hf.2.mul hg.2⟩
  add_mem' := fun hf hg => ⟨hf.1.add hg.1, hf.2.add hg.2⟩
  algebraMap_mem' := fun _ => ⟨measurable_const, contDiffOn_const⟩

lemma mem_goA {f : ℝ → ℝ} :
    f ∈ goA ↔ Measurable f ∧ ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (Ioo (-1 : ℝ) 1) := Iff.rfl

lemma goA₀_le_goA {f : ℝ → ℝ} (hf : f ∈ goA₀) : f ∈ goA :=
  ⟨(goA₀_smooth hf).continuous.measurable, (goA₀_smooth hf).contDiffOn⟩

lemma isOpen_Ioo11 : IsOpen (Ioo (-1 : ℝ) 1) := isOpen_Ioo

/-- a compact subset of `(-1,1)` is contained in the region where some `gocut n` is `1`. -/
lemma exists_gocut_eq_one {K : Set ℝ} (hK : IsCompact K) (hKI : K ⊆ Ioo (-1 : ℝ) 1) :
    ∃ n : ℕ, K ⊆ Ioo (-1 + 4 / ((n : ℝ) + 1)) (1 - 4 / ((n : ℝ) + 1)) := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, empty_subset _⟩
  obtain ⟨x0, hx0, hmin⟩ := hK.exists_isMinOn hne
    (f := fun x : ℝ => min (x + 1) (1 - x)) (by fun_prop)
  set δ := min (x0 + 1) (1 - x0) with hδ
  have hδpos : 0 < δ := lt_min (by linarith [(hKI hx0).1]) (by linarith [(hKI hx0).2])
  obtain ⟨n, hn⟩ := exists_nat_gt (4 / δ)
  refine ⟨n, fun x hx => ?_⟩
  have h1 : δ ≤ min (x + 1) (1 - x) := hmin hx
  have h2 : 4 / ((n : ℝ) + 1) < δ := by
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hδpos] at hn
    nlinarith
  exact ⟨by linarith [le_min_iff.1 h1 |>.1], by linarith [le_min_iff.1 h1 |>.2]⟩

lemma gocut_eq_one_of_mem {n : ℕ} {x : ℝ}
    (hx : x ∈ Ioo (-1 + 4 / ((n : ℝ) + 1)) (1 - 4 / ((n : ℝ) + 1))) : gocut n x = 1 := by
  have hpos : 0 < 4 / ((n : ℝ) + 1) := by positivity
  refine gocut_eq_one ⟨by linarith [hx.1], by linarith [hx.2]⟩ ?_
  rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
  · linarith [hx.1]
  · linarith [hx.2]

/-- `χ f` is globally smooth for `χ ∈ C_c^∞((-1,1))` and `f` smooth on `(-1,1)`. -/
lemma smooth_cut_mul {f : ℝ → ℝ} (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (Ioo (-1 : ℝ) 1))
    (n : ℕ) : Lebesgue.Sm (fun x => gocut n x * f x) := by
  show ContDiff ℝ _ _
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ Ioo (-1 : ℝ) 1
  · exact ((gocut_smooth n).contDiffAt).mul (hf.contDiffAt (isOpen_Ioo.mem_nhds hx))
  · have hxs : x ∉ tsupport (gocut n) := fun h => hx (gocut_tsupport n h)
    have hz : (fun x => gocut n x * f x) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [(isClosed_tsupport (gocut n)).isOpen_compl.mem_nhds hxs] with y hy
      simp [image_eq_zero_of_notMem_tsupport hy]
    exact (contDiffAt_const).congr_of_eventuallyEq hz

/-- **local smooth modification**: for `f ∈ C^∞((-1,1))` and compact `K ⊆ (-1,1)` there is a globally
smooth `g` and an open `U ⊇ K` with `f = g` on `U`. -/
lemma exists_smooth_agree {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (Ioo (-1 : ℝ) 1)) {K : Set ℝ} (hK : IsCompact K)
    (hKI : K ⊆ Ioo (-1 : ℝ) 1) :
    ∃ g : ℝ → ℝ, Lebesgue.Sm g ∧ ∃ U : Set ℝ, IsOpen U ∧ K ⊆ U ∧ EqOn f g U := by
  obtain ⟨n, hn⟩ := exists_gocut_eq_one hK hKI
  refine ⟨fun x => gocut n x * f x, smooth_cut_mul hf n, _, isOpen_Ioo, hn, fun x hx => ?_⟩
  simp [gocut_eq_one_of_mem hx]

lemma exists_smooth_agree_at {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (Ioo (-1 : ℝ) 1)) {x : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) :
    ∃ g : ℝ → ℝ, Lebesgue.Sm g ∧ f =ᶠ[𝓝 x] g := by
  obtain ⟨g, hg, U, hU, hxU, hfg⟩ := exists_smooth_agree hf isCompact_singleton
    (singleton_subset_iff.2 hx)
  exact ⟨g, hg, Filter.mem_of_superset (hU.mem_nhds (singleton_subset_iff.1 hxU)) hfg⟩

end MarkovTriple.BGL.Instances.GegenbauerOpen
