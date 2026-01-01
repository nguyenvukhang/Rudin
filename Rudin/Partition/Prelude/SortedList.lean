import Mathlib.Data.List.NodupEquivFin

universe u

variable {α : Type u} [Preorder α] {l : List α}

namespace List

theorem sorted_head_min (h₀ : l ≠ []) (hl : l.SortedLE) : ∀ x ∈ l, l.head h₀ ≤ x
  := by --
  induction l with
  | nil => contradiction
  | cons a l ih =>
  intro x hx
  change a ≤ x
  replace hl := List.pairwise_cons.mp hl.pairwise
  replace hx := List.mem_cons.mp hx
  rcases hx with hxa | hxl
  · exact ge_of_eq hxa
  · exact hl.1 x hxl -- ∎

theorem sorted_last_max (h₀ : l ≠ []) (hl : l.SortedLE) : ∀ x ∈ l, x ≤ l.getLast h₀
  := by --
  intro x hx
  rw [mem_iff_get] at hx
  obtain ⟨i, hi⟩ := hx
  subst hi
  rw [getLast_eq_getElem h₀]
  exact hl <| Nat.le_sub_one_of_lt i.is_lt -- ∎

theorem sorted_le_iff_monotone : l.SortedLE ↔ Monotone l.get
  := by --
  rw [<-List.sortedLE_ofFn_iff, List.ofFn_get l] -- ∎

end List
