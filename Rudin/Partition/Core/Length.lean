import Rudin.Defs.Partition

namespace Rudin

variable {a b : ℝ} {I : a < b} (P : Partition I)

namespace Partition

theorem ne_nil : P.l ≠ []
  := by --
  have h := P.head'
  by_contra h'
  rw [h', List.head?_nil] at h
  contradiction -- ∎

theorem len_ne_zero : P.n ≠ 0
  := by --
  exact List.eq_nil_iff_length_eq_zero.not.mp P.ne_nil -- ∎

theorem len_pos : 0 < P.n
  := by --
  exact Nat.zero_lt_of_ne_zero P.len_ne_zero -- ∎

theorem len_sub_one_lt : P.n - 1 < P.n
  := by --
  exact Nat.sub_one_lt P.len_ne_zero -- ∎

theorem two_le_len : 2 ≤ P.n
  := by --
  have : ({a, b} : Finset ℝ) ⊆ P.l.toFinset := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [List.mem_toFinset]
    rcases hx with ha | hb
    · rw [ha]; exact List.mem_of_mem_head? P.head'
    · rw [hb]; exact List.mem_of_getLast? P.tail'
  have : 2 ≤ P.l.toFinset.card := by
    rw [Finset.le_card_iff_exists_subset_card]
    exact ⟨{a, b}, this, Finset.card_pair I.ne⟩
  rw [List.toFinset_card_of_nodup P.nodup] at this
  exact this -- ∎

theorem one_lt_len : 1 < P.n
  := by --
  exact one_lt_two.trans_le P.two_le_len -- ∎

/-- If P₁ ⊂ P₂, then n₁ < n₂. -/
theorem len_strictMono : StrictMono (fun P : Partition I ↦ P.n)
  := by --
  intro P₁ P₂ hlt
  change P₁.l.length < P₂.l.length
  rw [<-List.toFinset_card_of_nodup P₁.nodup, <-List.toFinset_card_of_nodup P₂.nodup]
  exact Finset.card_lt_card hlt -- ∎

theorem len_mono : Monotone (fun P : Partition I ↦ P.n)
  := by --
  exact len_strictMono.monotone -- ∎

end Partition
end Rudin
