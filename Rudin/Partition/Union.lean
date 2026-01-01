import Rudin.Partition.Endpoints
import Rudin.Partition.Prelude.SortedLE

namespace Rudin

variable {a b : ℝ} {I : a < b}

namespace Partition

noncomputable instance : Union (Partition I)
  := by --
  refine { union P₁ P₂ := ?_ }
  let s₁ := P₁.l.toFinset
  let s₂ := P₂.l.toFinset
  let s := s₁ ∪ s₂
  let l := s.sort (· ≤ ·) -- the source of the noncomputability.
  have hl_mem {x} : x ∈ l ↔ x ∈ s := Finset.mem_sort (· ≤ ·)
  have hs_a : a ∈ s := Finset.mem_union_left s₂ P₁.mem_a
  have hs₀ : s.Nonempty := Set.nonempty_of_mem hs_a
  have hl_a : a ∈ l := hl_mem.mpr hs_a
  have hl_b : b ∈ l := hl_mem.mpr (Finset.mem_union_left s₂ P₁.mem_b)
  have hl_sort : List.SortedLE l := (s.pairwise_sort (· ≤ ·)).sortedLE
  have hl₀ : l ≠ [] := List.ne_nil_of_mem hl_a
  exact {
    l := l
    head' := by
      rw [<-List.head_eq_iff_head?_eq_some hl₀]
      refine le_antisymm ?_ ?_
      · exact hl_sort.sorted_head_min hl₀ a hl_a
      · have h_min : s.min' hs₀ = a := by
          refine (Finset.min'_eq_iff s hs₀ a).mpr ⟨hs_a, fun x hx ↦ ?_⟩
          rcases Finset.mem_union.mp hx with hx₁ | hx₂
          · exact P₁.min_a x hx₁
          · exact P₂.min_a x hx₂
        rw [<-h_min]
        exact Finset.min'_le s _ (hl_mem.mp (List.head_mem hl₀))
    tail' := by
      rw [<-List.getLast_eq_iff_getLast?_eq_some hl₀]
      refine le_antisymm ?_ ?_
      · have h_max : s.max' hs₀ = b := by
          refine (Finset.max'_eq_iff s hs₀ b).mpr ⟨?_, fun x hx ↦ ?_⟩
          · exact (Finset.mem_sort (· ≤ ·)).mp hl_b
          · rcases Finset.mem_union.mp hx with hx₁ | hx₂
            · exact P₁.max_b x hx₁
            · exact P₂.max_b x hx₂
        rw [<-h_max]
        exact Finset.le_max' s _ (hl_mem.mp (List.getLast_mem hl₀))
      · exact hl_sort.sorted_last_max hl₀ b hl_b
    sorted' := Finset.sortedLT_sort s
  } -- ∎

@[simp]
theorem union_eq_unionSet (P₁ P₂ : Partition I) : P₁ ∪ P₂ = (P₁ : Set ℝ) ∪ P₂
  := by --
  let s₁ := P₁.l.toFinset
  let s₂ := P₂.l.toFinset
  let s := s₁ ∪ s₂
  let l := s.sort (· ≤ ·) -- the source of the noncomputability.
  have hl_mem {x} : x ∈ l ↔ x ∈ s := Finset.mem_sort (· ≤ ·)
  refine Set.ext fun x ↦ ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
  · rcases Finset.mem_union.mp (hl_mem.mp (List.mem_dedup.mp hx)) with h₁ | h₂
    · exact Or.inl h₁
    · exact Or.inr h₂
  · have : x ∈ s := by
      rcases hx with h₁ | h₂
      · exact Finset.mem_union_left s₂ h₁
      · exact Finset.mem_union_right s₁ h₂
    exact List.mem_toFinset.mpr (hl_mem.mpr this) -- ∎

noncomputable instance : SemilatticeSup (Partition I) where
  sup P₁ P₂ := P₁ ∪ P₂
  le_sup_left P₁ P₂ := by
    change (P₁ : Set ℝ) ⊆ ↑(P₁ ∪ P₂)
    rw [union_eq_unionSet]
    exact Set.subset_union_left
  le_sup_right P₁ P₂ := by
    change (P₂ : Set ℝ) ⊆ ↑(P₁ ∪ P₂)
    rw [union_eq_unionSet]
    exact Set.subset_union_right
  sup_le a b c (hab : (a : Set ℝ) ⊆ c) (hbc : (b : Set ℝ) ⊆ c) := by
    change ↑(a ∪ b) ⊆ (c : Set ℝ)
    rw [union_eq_unionSet]
    exact Set.union_subset hab hbc

end Partition
end Rudin
