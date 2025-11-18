import Rudin.Partition.Core.Endpoints
import Rudin.Partition.Core.Monotone

namespace Rudin

variable {a b : ℝ} {I : a < b} (P : Partition I)

namespace Partition

theorem mono : Monotone P
  := by --
  refine monotone_nat_of_le_succ ?_
  intro k
  simp only [P.fn_eq]
  if hk : k + 1 < P.n then
    rw [dif_pos hk, dif_pos (Nat.lt_of_succ_lt hk)]
    exact P.get_mono k.le_succ
  else
  rw [dif_neg hk]
  if hk : k < P.n then
    rw [dif_pos hk]
    conv => rhs; rw [P.b_eqᵢ]
    exact P.get_mono (Nat.le_sub_one_of_lt hk)
  else
  rw [dif_neg hk] -- ∎

end Partition
end Rudin
