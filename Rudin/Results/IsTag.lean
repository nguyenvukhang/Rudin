import Rudin.Defs.Globals
import Rudin.Partition.Interval

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
  exact (P.interval_bdd_on hf i).csInf_le (ht i) -- ∎

include hf in
theorem le_M (ht : IsTag P t) (i : ℕ) : f (t i) ≤ M P f i
  := by --
  exact (P.interval_bdd_on hf i).le_csSup (ht i) -- ∎

end IsTag
end Rudin
