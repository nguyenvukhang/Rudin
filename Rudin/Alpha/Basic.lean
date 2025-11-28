import Rudin.Lemmas.Globals

open Set

namespace Rudin

variable {a b : ℝ} {I : a < b} {P : Partition I} {f α : ℝ → ℝ}
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
lemma Partition.Δ_nonneg (P : Partition I) (i : ℕ) : (0 : ℝ) ≤ P.Δ α i
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

include hα in
lemma α_sub_nonneg (h : a ≤ b) : 0 ≤ α b - α a
  := by --
  rw [sub_nonneg]
  exact hα (left_mem_Icc.mpr h) (right_mem_Icc.mpr h) h -- ∎

include hα in
theorem α_trivial_Δ (h : α a = α b) (i : ℕ) : P.Δ α i = 0
  := by --
  have (P : Partition I) (i : ℕ) : α (P i) = α a := by
    refine le_antisymm ?_ ?_
    · rw [h]
      refine hα ?_ ?_ ?_
      · exact P.mem_Icc i
      · exact right_mem_Icc.mpr I.le
      · exact P.max_b₂ i
    · refine hα ?_ ?_ ?_
      · exact left_mem_Icc.mpr I.le
      · exact P.mem_Icc i
      · exact P.min_a₂ i
  dsimp only [Partition.Δ]
  rw [this P i, this P (i - 1)]
  exact sub_self (α a) -- ∎

include hα in
theorem α_trivial_U (h : α a = α b) : U P f α = 0
  := by --
  dsimp only [U]
  simp only [α_trivial_Δ hα h, mul_zero]
  exact Finset.sum_const_zero -- ∎

include hα in
theorem α_trivial_L (h : α a = α b) : L P f α = 0
  := by --
  dsimp only [L]
  simp only [α_trivial_Δ hα h, mul_zero]
  exact Finset.sum_const_zero -- ∎

end Rudin
