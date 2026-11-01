import Mathlib
import MarkovTriple.Hilbert.DirMerge
import MarkovTriple.Hilbert.Resolvent

/-!
# The sequence-based Friedrichs data `DirFriedrichs S` from the completion-based `FormData` API

`FormData.dirFriedrichs S : DirFriedrichs S` identifies `Q = range ι` with the set of `H`-limits of
energy-Cauchy sequences in `D`, and `E` (the form of `Friedrichs.lean`) with the limit of the
energies `en f_n g_n`.  This is the link that merges the two copies of the construction in
`cutoff-rigidity-diffusions` (`FormData` in `DiffFriedrichs`, `DirFormData` in `DiffMarkov`).
-/

open Filter Topology Set
open scoped NNReal InnerProductSpace

set_option linter.unusedSectionVars false

namespace MarkovTriple.Hilbert

namespace FormData

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  (S : FormData H)

/-- `D → K`. -/
noncomputable def kc (f : S.D) : S.K := ((show S.Dom from f : S.Dom) : S.K)

lemma kc_sub (f g : S.D) : S.kc (f - g) = S.kc f - S.kc g :=
  UniformSpace.Completion.coe_sub (show S.Dom from f) (show S.Dom from g)

lemma ι_kc (f : S.D) : S.ι (S.kc f) = (f : H) := S.ι_coe (show S.Dom from f)

lemma en_eq_inner_sub (f g : S.D) :
    S.en f g = inner ℝ (S.kc f) (S.kc g) - inner ℝ (f : H) (g : H) := by
  unfold kc
  rw [UniformSpace.Completion.inner_coe, inner_dom]
  show inner ℝ (S.A f) (g : H) = _
  have h1 : S.emb (show S.Dom from f) = (f : H) := rfl
  have h2 : S.emb (show S.Dom from g) = (g : H) := rfl
  have h3 : S.opA (show S.Dom from f) = S.A f := rfl
  rw [h1, h2, h3]; ring

lemma norm_kc_sq (f : S.D) : ‖S.kc f‖ ^ 2 = ‖(f : H)‖ ^ 2 + S.en f f := by
  rw [← real_inner_self_eq_norm_sq, S.en_eq_inner_sub, ← real_inner_self_eq_norm_sq]; ring

lemma dist_kc (f g : S.D) : dist (S.kc f) (S.kc g) = ‖S.kc (f - g)‖ := by
  rw [dist_eq_norm, S.kc_sub]

/-- an energy-Cauchy `D`-sequence converging in `H` converges in `K` to a point with `ι x = u`. -/
lemma exists_K_limit (f : ℕ → S.D) (u : H) (hf : Tendsto (fun n => (f n : H)) atTop (𝓝 u))
    (hc : S.EnCauchy f) :
    ∃ x : S.K, Tendsto (fun n => S.kc (f n)) atTop (𝓝 x) ∧ S.ι x = u := by
  have hH : CauchySeq (fun n => (f n : H)) := hf.cauchySeq
  have hK : CauchySeq (fun n => S.kc (f n)) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N1, h1⟩ := Metric.cauchySeq_iff.1 hH (min 1 (ε ^ 2 / 2)) (lt_min one_pos (by positivity))
    obtain ⟨N2, h2⟩ := hc (ε ^ 2 / 2) (by positivity)
    refine ⟨max N1 N2, fun m hm n hn => ?_⟩
    have a := h1 m (le_trans (le_max_left _ _) hm) n (le_trans (le_max_left _ _) hn)
    have b := h2 m (le_trans (le_max_right _ _) hm) n (le_trans (le_max_right _ _) hn)
    have hsq := S.norm_kc_sq (f m - f n)
    rw [S.dist_kc]
    rw [dist_eq_norm] at a
    have : ‖S.kc (f m - f n)‖ ^ 2 < ε ^ 2 := by
      rw [hsq]
      have : ‖((f m - f n : S.D) : H)‖ ^ 2 < ε ^ 2 / 2 := by
        have h0 := norm_nonneg ((f m : H) - f n)
        have e : ((f m - f n : S.D) : H) = (f m : H) - f n := rfl
        rw [e]
        have h3 : ‖(f m : H) - f n‖ < 1 := lt_of_lt_of_le a (min_le_left _ _)
        have h4 : ‖(f m : H) - f n‖ < ε ^ 2 / 2 := lt_of_lt_of_le a (min_le_right _ _)
        nlinarith
      linarith
    exact lt_of_pow_lt_pow_left₀ 2 hε.le this
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hK
  refine ⟨x, hx, ?_⟩
  have h1 : Tendsto (fun n => S.ι (S.kc (f n))) atTop (𝓝 (S.ι x)) :=
    (S.ι.continuous.tendsto x).comp hx
  have h2 : ∀ n, S.ι (S.kc (f n)) = (f n : H) := fun n => S.ι_kc (f n)
  simp only [h2] at h1
  exact tendsto_nhds_unique h1 hf

open Classical in
/-- **`FormData` ⟹ `DirFriedrichs`.** -/
noncomputable def dirFriedrichs : DirFriedrichs S where
  Q := (S.Q : Set H)
  E u v := if h : u ∈ S.Q ∧ v ∈ S.Q then S.E ⟨u, h.1⟩ ⟨v, h.2⟩ else 0
  mem_Q u := by
    constructor
    · rintro ⟨x, rfl⟩
      have hx : x ∈ closure (Set.range ((↑) : S.Dom → S.K)) :=
        UniformSpace.Completion.denseRange_coe x
      obtain ⟨s, hs, hslim⟩ := mem_closure_iff_seq_limit.1 hx
      have hs' : ∀ n, ∃ g : S.D, S.kc g = s n := fun n => by
        obtain ⟨g, hg⟩ := hs n
        exact ⟨g, hg⟩
      choose f hf using hs'
      have hfK : Tendsto (fun n => S.kc (f n)) atTop (𝓝 x) := by
        have : (fun n => S.kc (f n)) = s := funext hf
        rw [this]; exact hslim
      refine ⟨f, ?_, ?_⟩
      · have := (S.ι.continuous.tendsto x).comp hfK
        refine this.congr (fun n => ?_)
        exact S.ι_kc (f n)
      · intro ε hε
        obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hfK.cauchySeq (min 1 ε) (lt_min one_pos hε)
        refine ⟨N, fun m hm n hn => ?_⟩
        have h1 := hN m hm n hn
        rw [S.dist_kc] at h1
        have h2 := S.norm_kc_sq (f m - f n)
        have h3 : S.en (f m - f n) (f m - f n) ≤ ‖S.kc (f m - f n)‖ ^ 2 := by
          nlinarith [sq_nonneg ‖((f m - f n : S.D) : H)‖]
        have h4 : ‖S.kc (f m - f n)‖ < 1 := lt_of_lt_of_le h1 (min_le_left _ _)
        have h5 : ‖S.kc (f m - f n)‖ < ε := lt_of_lt_of_le h1 (min_le_right _ _)
        have h6 := norm_nonneg (S.kc (f m - f n))
        nlinarith
    · rintro ⟨f, hf, hc⟩
      obtain ⟨x, -, hx⟩ := S.exists_K_limit f u hf hc
      exact ⟨x, hx⟩
  E_lim f g u v hf hfc hg hgc := by
    obtain ⟨x, hx, hxu⟩ := S.exists_K_limit f u hf hfc
    obtain ⟨y, hy, hyv⟩ := S.exists_K_limit g v hg hgc
    have huQ : u ∈ S.Q := ⟨x, hxu⟩
    have hvQ : v ∈ S.Q := ⟨y, hyv⟩
    have hE : S.E ⟨u, huQ⟩ ⟨v, hvQ⟩ = inner ℝ x y - inner ℝ u v := by
      have e1 : (⟨u, huQ⟩ : S.Q) = S.qEquiv x := Subtype.ext (by rw [qEquiv_apply, hxu])
      have e2 : (⟨v, hvQ⟩ : S.Q) = S.qEquiv y := Subtype.ext (by rw [qEquiv_apply, hyv])
      rw [e1, e2, E_eq, hxu, hyv]
    have hlim : Tendsto (fun n => inner ℝ (S.kc (f n)) (S.kc (g n)) -
        inner ℝ (f n : H) (g n : H)) atTop (𝓝 (inner ℝ x y - inner ℝ u v)) :=
      (hx.inner hy).sub (hf.inner hg)
    have hdite : (if h : u ∈ S.Q ∧ v ∈ S.Q then S.E ⟨u, h.1⟩ ⟨v, h.2⟩ else 0) =
        inner ℝ x y - inner ℝ u v := by
      rw [dif_pos (show u ∈ S.Q ∧ v ∈ S.Q from ⟨huQ, hvQ⟩)]; exact hE
    rw [hdite]
    exact hlim.congr (fun n => (S.en_eq_inner_sub (f n) (g n)).symm)

end FormData

end MarkovTriple.Hilbert
