import Rudin.Partition.Core
import Rudin.Partition.Monotone

namespace Rudin

variable {a b : ℝ} {I : a < b} (P : Partition I)

namespace Partition

theorem min_a : ∀ x ∈ P, a ≤ x
  := by --
  intro x hx
  rw [<-P.head_eq₂]
  rw [P.mem_iff_x] at hx
  obtain ⟨i, hx⟩ : ∃ i, P i = x := hx
  subst hx
  exact P.mono (Nat.zero_le i) -- ∎

theorem max_b : ∀ x ∈ P, x ≤ b
  := by --
  intro x hx
  rw [<-P.tail_eq₂]
  obtain ⟨i, hi, heq⟩ := P.exists_fin_index_of_mem hx
  subst heq
  exact P.mono (Nat.le_sub_one_of_lt hi) -- ∎

theorem minimal_a : Minimal (· ∈ P) a
  := by --
  exact ⟨P.mem_a, fun x hx _ ↦ P.min_a x hx⟩ -- ∎

theorem maximal_b : Maximal (· ∈ P) b
  := by --
  exact ⟨P.mem_b, fun x hx _ ↦ P.max_b x hx⟩ -- ∎

theorem min_a₂ : ∀ i, a ≤ P i
  := by --
  intro i
  exact P.min_a (P i) P.mem_indexed -- ∎

theorem max_b₂ : ∀ i, P i ≤ b
  := by --
  intro i
  exact P.max_b (P i) P.mem_indexed -- ∎

namespace ab

theorem ofList : [a, b] ⊆ P.l
  := by --
  intro x hx
  rw [List.mem_pair] at hx
  rcases hx with ha' | hb'
  · subst ha'; exact P.mem_a₂
  · subst hb'; exact P.mem_b₂ -- ∎

theorem ofFinset : {a, b} ⊆ P.l.toFinset
  := by --
  intro x hx
  rw [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with ha' | hb'
  · rw [ha']; exact P.mem_a
  · rw [hb']; exact P.mem_b -- ∎

end ab
end Partition
end Rudin
