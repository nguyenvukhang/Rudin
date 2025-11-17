import Rudin.Partition.Endpoints
import Mathlib.Tactic

namespace Rudin

variable {a b : ℝ} {I : a < b} (P : Partition I)

namespace Partition

/-- The partition that ≤ everything else. The partition with only two points. -/
instance : Bot (Partition I)
  := by --
  refine { bot := ?_ }
  refine { l := [a, b], head' := rfl, tail' := rfl, sorted' := ?_ }
  exact List.Sorted.cons I (List.sorted_singleton b) -- ∎

example : (⊥ : Partition I).n = 2 := rfl -- length is immediately 2.

theorem eq_bot_iff : P = ⊥ ↔ P.l = [a, b]
  := by --
  refine ⟨?_, (Partition.ext_iff.mpr ·)⟩
  intro h; subst h; exact rfl -- ∎

theorem eq_bot_iff₂ : P = ⊥ ↔ P.l.toFinset = {a, b}
  := by --
  refine ⟨?_, ?_⟩
  · intro h
    subst h
    change [a, b].toFinset = {a, b}
    rw [List.toFinset_cons]
    exact rfl
  · intro h
    refine (eq_bot_iff P).mpr ?_
    rw [<-eq_Finset_sort, h, Finset.sort_insert]
    · refine (List.cons_inj_right a).mpr ?_
      exact Finset.sort_singleton (· ≤ ·) b
    · intro c hc
      rw [Finset.mem_singleton] at hc
      subst hc
      exact I.le
    · exact Finset.notMem_of_lt_min I rfl -- ∎

theorem eq_bot_iff₃ : P = ⊥ ↔ P 0 = a ∧ P 1 = b
  := by --
  have hP₁ (hn : P.n = 2) : P[1] = P[P.n - 1] := by
    refine congrArg (P.l.get) ?_
    rw [Fin.mk.injEq, hn]
  refine ⟨?_, ?_⟩
  · intro hP
    have hn : P.n = 2 := by subst hP; exact rfl
    simp only [P.fun_eq]
    simp only [hn]
    rw [dif_pos zero_lt_two, dif_pos one_lt_two]
    refine ⟨?_, ?_⟩
    · exact P.idx_eq_a
    · rw [hP₁ hn]
      exact P.idx_eq_b
  · intro ⟨ha, hb⟩
    have : P.n ≤ 2 := by
      have := P.le_index_of_eq_b hb
      exact Nat.le_succ_of_pred_le this
    have hn : P.n = 2 := le_antisymm this P.two_le_len
    rw [eq_bot_iff]
    refine List.ext_getElem hn ?_
    intro i hi hi'
    if hi₀ : i = 0 then
      subst hi₀
      rw [List.getElem_cons_zero]
      exact P.idx_eq_a
    else if hi₁ : i = 1 then
      subst hi₁
      rw [List.getElem_cons_succ, List.getElem_cons_zero]
      change P[1] = b
      rw [hP₁ hn]
      exact P.idx_eq_b
    else
      have h₁ : 2 ≤ i := (Nat.two_le_iff i).mpr ⟨hi₀, hi₁⟩
      have h₂ : i < 2 := by rw [<-hn]; exact hi
      exact False.elim (h₂.not_ge h₁) -- ∎

instance : OrderBot (Partition I)
  := by --
  refine { bot_le P x hx := ?_ }
  change x ∈ [a, b].toFinset at hx
  rw [List.mem_toFinset, List.mem_cons, List.mem_singleton] at hx
  rcases hx with ha | hb
  · rw [ha]; exact P.mem_a
  · rw [hb]; exact P.mem_b -- ∎

theorem ne_bot_exists (P : Partition I) : P ≠ ⊥ → ∃ x ∈ Set.Ioo a b, x ∈ P
  := by --
  intro hP
  contrapose! hP
  rw [Partition.eq_bot_iff₂]
  refine le_antisymm ?_ ?_
  · intro x hx
    have ha : a ≤ x := P.min_a x hx
    have hb : x ≤ b := P.max_b x hx
    have : x ∉ Set.Ioo a b := by contrapose! hP; exact ⟨x, hP, hx⟩
    rw [Set.mem_Ioo, not_and_or] at this
    push_neg at this
    rcases this with ha' | hb'
    · rw [le_antisymm ha' ha]
      exact Finset.mem_insert_self a {b}
    · rw [le_antisymm hb hb']
      refine Finset.mem_insert_of_mem ?_
      exact Finset.mem_singleton.mpr rfl
  · intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with ha | hb
    · rw [ha]; exact P.mem_a
    · rw [hb]; exact P.mem_b -- ∎

theorem mem_bot {x : ℝ} : x ∈ (⊥ : Partition I) → (x = a ∨ x = b)
  := by --
  intro hx
  change x ∈ [a, b].toFinset at hx
  have hx : x ∈ [a, b] := List.mem_dedup.mp hx
  rw [List.mem_pair] at hx
  exact hx -- ∎

theorem bot_cover (x : Set.Icc a b) : ↑x ∈ (⊥ : Partition I).interval 1
  := by --
  exact x.prop -- ∎

end Partition
end Rudin
