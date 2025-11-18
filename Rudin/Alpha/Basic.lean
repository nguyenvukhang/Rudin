import Rudin.Axioms
import Rudin.Prelude
import Rudin.Partition
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Defs

open Set

namespace Rudin

variable {a b : ℝ} {I : a < b} {P : Partition I} {α : ℝ → ℝ}
  (hα : MonotoneOn α (Icc a b))

include hα in
private lemma α_nonnegᵢ (i : Fin P.n) : (0 : ℝ) ≤ α P[i] - α P[↑i - 1]
  := by --
  rw [sub_nonneg]
  refine hα ?_ ?_ ?_
  · exact P.mem_principalᵢ ⟨i - 1, Nat.sub_lt_of_lt i.is_lt⟩
  · exact P.mem_principalᵢ i
  · exact P.get_mono (Nat.sub_le i 1) -- ∎

include hα in
theorem α_nonneg (i : ℕ) : (0 : ℝ) ≤ α (P i) - α (P (i - 1))
  := by --
  have h := P.fn_eq₂ i
  if hi : i < P.n then
    rw [dif_pos hi] at h
    rw [h.1, h.2]
    exact α_nonnegᵢ hα ⟨i, hi⟩
  else
    rw [dif_neg hi] at h
    rw [h.1, h.2, sub_self] -- ∎

include hα in
lemma Partition.Δ_nonneg (i : ℕ) : (0 : ℝ) ≤ P.Δ α i
  := by --
  exact α_nonneg hα i -- ∎

private lemma α_telescopeᵢ : ∑ i : Fin P.n, (α P[i] - α P[↑i - 1]) = α b - α a
  := by --
  let n := P.n
  have h₁ (i : Fin n) : P i = P[i] := Partition.ieq.idx_fin P
  have h₂ (i : Fin n) : P (i - 1) = P[↑i - 1] := Partition.ieq.idx_cond P _
  have : ∑ i : Fin n, (α P[i] - α P[↑i - 1]) = ∑ i : Fin n, (α (P i) - α (P (i - 1))) := by
    simp only [h₁, h₂]
  rw [this]
  let φ (i : ℕ) : ℝ := α (P i) - α (P (i - 1))
  change ∑ i : Fin n, φ i = α b - α a
  rw [Fin.sum_univ_eq_sum_range]
  rw [Finset.sum_range_sub₁]
  rw [<-P.a_eq, <-P.b_eq] -- ∎

theorem α_telescope : ∑ i ∈ Finset.range P.n, (α (P i) - α (P (i - 1))) = α b - α a
  := by --
  rw [Finset.sum_range_sub₁, <-P.a_eq, <-P.b_eq] -- ∎

end Rudin
