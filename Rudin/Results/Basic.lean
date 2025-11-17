import Rudin.Axioms
import Rudin.Prelude
import Rudin.Partition
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Defs

open Set

namespace Rudin

variable {a b : ℝ} {I : a < b} {P P' : Partition I} (f α : ℝ → ℝ)
  (hf : BddOn f (Icc a b))
  (hα : MonotoneOn α (Icc a b))

example : L P f α ≤ U P f α := by
  let g (i : Fin P.n) := α P[i] - α P[i.val - 1]
  have hg (i : Fin P.n) : 0 ≤ g i := by
    rw [sub_nonneg]
    refine hα ?_ ?_ ?_
    · exact P.mem_principal _
    · exact P.mem_principal_fin
    · exact P.get_mono (Nat.sub_le i 1)
  have (i : Fin P.n) : m P f i * g i ≤ M P f i * g i := by
    if h₀ : g i = 0 then
      rw [h₀]
      simp only [mul_zero]
      exact le_rfl
    else
    replace h₀ : 0 < g i := (hg i).lt_of_ne' h₀
    rw [mul_le_mul_iff_left₀ h₀]
    exact m_le_M P hf i
  exact Finset.sum_le_sum fun i _ ↦ this i

end Rudin
