import Mathlib.Data.Set.Lattice
import Mathlib.Order.Interval.Set.LinearOrder

import Rudin.Partition.Endpoints

namespace Rudin

variable {a b : ℝ} {I : a < b} (P : Partition I)

namespace Partition

/-- The induction lemma. -/
--* Breaking apart a union ⋃ j < k + 1 to k ∪ ⋃ j < k.
private lemma ℓ₀ (i : ℕ) : ⋃ j ≤ i, P.interval j = Set.Icc a (P i)
  := by --
  induction i with
  | zero =>
    simp only [Nat.le_zero]
    rw [Set.iUnion_iUnion_eq_left]
    exact congrArg (Set.Icc · (P 0)) P.head_eq₂
  | succ k ih =>
    rw [Set.biUnion_le] -- breaks up a union.
    simp only [Nat.lt_add_one_iff]
    rw [ih]
    dsimp only [Partition.interval]
    rw [add_tsub_cancel_right]
    refine Set.Icc_union_Icc_eq_Icc ?_ ?_
    · exact P.min_a (P k) P.mem_indexed
    · exact P.mono k.le_succ -- ∎

/-- Union of all the intervals gives the entire total interval. -/
theorem iUnionEqTotal : ⋃ i < P.n, P.interval i = Set.Icc a b
  := by --
  have : P.n - 1 < P.n := P.len_sub_one_lt
  have h := ℓ₀ P (P.n - 1)
  simp only [Nat.le_sub_one_iff_lt P.len_pos] at h
  rw [h]
  exact congrArg (Set.Icc a ·) P.tail_eq₂ -- ∎

theorem cover {x : ℝ} : x ∈ Set.Icc a b → ∃ i < P.n, ↑x ∈ P.interval i
  := by --
  intro hx
  rw [<-P.iUnionEqTotal, Set.mem_iUnion₂, bex_def] at hx
  exact hx -- ∎

end Partition
end Rudin
