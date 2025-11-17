import Mathlib.Data.Set.Lattice
import Mathlib.Order.Interval.Set.LinearOrder

import Rudin.Partition.Endpoints
import Rudin.Partition.Prelude

namespace Rudin

open Set

variable {a b : ℝ} {I : a < b} (P : Partition I)

namespace Partition

noncomputable instance : Insert (Ioo a b) (Partition I) := {
  insert x P := by --
    if hxP : ↑x ∈ P then exact P else
    let l' := P.l.orderedInsert (· ≤ ·) ↑x
    have sorted' : l'.Sorted (· < ·) := by
      refine P.sorted'.orderedInsert_sorted_lt ?_
      rw [<-P.mem_iff_mem_list]
      exact hxP
    have h₀ : l' ≠ [] := by
      refine List.ne_nil_of_length_pos ?_
      rw [List.length_pos_iff_exists_mem]
      use x
      rw [List.mem_orderedInsert]
      exact Or.inl rfl
    exact {
      l := l'
      sorted'
      head' := by
        rw [<-List.head_eq_iff_head?_eq_some h₀]
        refine le_antisymm ?_ ?_
        · -- head ≤ a. This follows from the current list being sorted.
          have ha' : a ∈ l' := by
            rw [List.mem_orderedInsert]
            exact Or.inr P.mem_a₂
          exact List.sorted_head_min h₀ sorted'.le_of_lt a ha'
        · -- a ≤ head. This follows from the minimality of a ∈ P.
          have h : l'.head h₀ ∈ l' := List.head_mem h₀
          rw [List.mem_orderedInsert] at h
          rcases h with hx | hP
          · rw [hx]
            exact x.prop.1.le
          · have : l'.head h₀ ∈ P := P.mem_iff_mem_list.mpr hP
            exact P.min_a (l'.head h₀) this
      tail' := by
        rw [<-List.getLast_eq_iff_getLast?_eq_some h₀]
        refine le_antisymm ?_ ?_
        · -- tail ≤ b. This follows from the maximality of b ∈ P.
          have h : l'.getLast h₀ ∈ l' := List.getLast_mem h₀
          rw [List.mem_orderedInsert] at h
          rcases h with hx | hP
          · rw [hx]
            exact x.prop.2.le
          · have : l'.getLast h₀ ∈ P := P.mem_iff_mem_list.mpr hP
            exact P.max_b (l'.getLast h₀) this
        · -- b ≤ tail. This follows from the current list being sorted.
          have hb' : b ∈ l' := by
            rw [List.mem_orderedInsert]
            exact Or.inr P.mem_b₂
          exact List.sorted_last_max h₀ sorted'.le_of_lt b hb'
    }
} -- ∎

end Partition
end Rudin
