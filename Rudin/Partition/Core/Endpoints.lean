import Rudin.Partition.Defs

namespace Rudin

variable {a b : ℝ} {I : a < b}

section Prelude
variable {P : Partition I}

private lemma ℓ₀ : P.l ≠ []
  := by --
  have h := P.head'
  by_contra h'
  rw [h', List.head?_nil] at h
  contradiction -- ∎

private lemma ℓ₁ : 0 < P.n
  := by --
  exact Nat.zero_lt_of_ne_zero (List.eq_nil_iff_length_eq_zero.not.mp ℓ₀) -- ∎

private lemma ℓₙ : P.n - 1 < P.n
  := by --
  exact Nat.sub_one_lt (List.eq_nil_iff_length_eq_zero.not.mp ℓ₀) -- ∎

end Prelude

namespace Partition

variable (P : Partition I)

theorem idx_eq_a : P[0]'(ℓ₁) = a
  := by --
  refine (List.getElem_eq_iff ℓ₁).mpr ?_
  rw [<-P.head']
  exact List.head?_eq_getElem?.symm -- ∎

theorem idx_eq_b : P[P.n - 1]'(ℓₙ) = b
  := by --
  refine (List.getElem_eq_iff ℓₙ).mpr ?_
  rw [<-P.tail', List.getLast?_eq_some_getLast ℓ₀, List.getElem?_eq_getElem ℓₙ]
  exact congrArg some (List.getLast_eq_getElem ℓ₀).symm -- ∎

theorem head_eq : P.head = a := List.head_of_mem_head? P.head'
theorem head_eq₂ : P 0 = a
  := by --
  rw [P.fun_eq, dif_pos ℓ₁]
  exact P.idx_eq_a -- ∎

theorem tail_eq : P.tail = b := List.getLast_of_mem_getLast? P.tail'
theorem tail_eq₂ : P (P.n - 1) = b
  := by --
  rw [P.fun_eq, dif_pos ℓₙ]
  exact P.idx_eq_b -- ∎
theorem tail_eq₃ {i : ℕ} (hi : P.n ≤ i) : P i = b
  := by --
  rw [P.fun_eq, dif_neg hi.not_gt] -- ∎

theorem mem_a₂ : a ∈ P.l := List.mem_of_mem_head? P.head'
theorem mem_a : a ∈ P := List.mem_toFinset.mpr P.mem_a₂

theorem mem_b₂ : b ∈ P.l := List.mem_of_getLast? P.tail'
theorem mem_b : b ∈ P := List.mem_toFinset.mpr P.mem_b₂

-- Funlike lemmas

lemma fun_eq_lt {i : ℕ} (hi : i < P.n) : P i = P[i] := dif_pos hi
lemma fun_eq_ge {i : ℕ} (hi : P.n ≤ i) : P i = b := dif_neg hi.not_gt
lemma fun_eq_ge₁ {i : ℕ} (hi : P.n - 1 ≤ i) : P i = b
  := by --
  rcases hi.lt_or_eq with hlt | heq
  · exact P.fun_eq_ge (Nat.le_of_pred_lt hlt)
  · subst heq
    exact P.tail_eq₂ -- ∎

end Partition
end Rudin
