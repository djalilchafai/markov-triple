import Mathlib

/-!
# Finite-sum reindexing helpers (index gymnastics for tensor identities)

`s3a`, `s3b`: swap the outer / inner pair of a triple sum over `Fin d`; `s4a`, `s4b`, `s4c` likewise for quadruple sums.
-/

namespace MarkovTriple.BGL.Instances.Riemannian

variable {d : ℕ}

lemma s3a (F : Fin d → Fin d → Fin d → ℝ) :
    ∑ a, ∑ b, ∑ c, F a b c = ∑ b, ∑ a, ∑ c, F a b c := Finset.sum_comm

lemma s3b (F : Fin d → Fin d → Fin d → ℝ) :
    ∑ a, ∑ b, ∑ c, F a b c = ∑ a, ∑ c, ∑ b, F a b c :=
  Finset.sum_congr rfl fun _ _ => Finset.sum_comm

lemma s4a (F : Fin d → Fin d → Fin d → Fin d → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ e, F a b c e = ∑ b, ∑ a, ∑ c, ∑ e, F a b c e := Finset.sum_comm

lemma s4b (F : Fin d → Fin d → Fin d → Fin d → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ e, F a b c e = ∑ a, ∑ c, ∑ b, ∑ e, F a b c e :=
  Finset.sum_congr rfl fun _ _ => Finset.sum_comm

lemma s4c (F : Fin d → Fin d → Fin d → Fin d → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ e, F a b c e = ∑ a, ∑ b, ∑ e, ∑ c, F a b c e :=
  Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm

end MarkovTriple.BGL.Instances.Riemannian
