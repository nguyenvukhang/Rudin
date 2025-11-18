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

theorem a_eqᵢ : a = P[0]'(ℓ₁)
  := by --
  refine ((List.getElem_eq_iff ℓ₁).mpr ?_).symm
  rw [<-P.head']
  exact List.head?_eq_getElem?.symm -- ∎

theorem b_eqᵢ : b = P[P.n - 1]'(ℓₙ)
  := by --
  refine ((List.getElem_eq_iff ℓₙ).mpr ?_).symm
  rw [<-P.tail']
  exact List.getLast?_eq_getElem?.symm -- ∎

theorem a_eq : a = P 0
  := by --
  rw [P.fn_eq, dif_pos ℓ₁]
  exact P.a_eqᵢ -- ∎
theorem b_eq : b = P (P.n - 1)
  := by --
  rw [P.fn_eq, dif_pos ℓₙ]
  exact P.b_eqᵢ -- ∎

theorem mem_aᵢ : a ∈ P.l := List.mem_of_mem_head? P.head'
theorem mem_a : a ∈ P := List.mem_toFinset.mpr P.mem_aᵢ

theorem mem_bᵢ : b ∈ P.l := List.mem_of_getLast? P.tail'
theorem mem_b : b ∈ P := List.mem_toFinset.mpr P.mem_bᵢ

end Partition
end Rudin
