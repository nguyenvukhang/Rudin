import Rudin.Results.Basic

open Set

namespace Rudin

variable {a b : ℝ} {I : a < b} {P : Partition I} {f α : ℝ → ℝ}
  (hf : BddOn f (Icc a b))
  (hα : MonotoneOn α (Icc a b))

namespace IsTag
variable {t : ℕ → ℝ}

include hf in
theorem ge_m (ht : IsTag P t) (i : ℕ) : m P f i ≤ f (t i)
  := by --
  exact (bdd_f_bdd_on_interval hf i).csInf_le (ht i) -- ∎

include hf in
theorem le_M (ht : IsTag P t) (i : ℕ) : f (t i) ≤ M P f i
  := by --
  exact (bdd_f_bdd_on_interval hf i).le_csSup (ht i) -- ∎

end IsTag
end Rudin
