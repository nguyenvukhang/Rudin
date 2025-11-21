import Rudin.Partition.Endpoints
import Rudin.Prelude

open Set

namespace Rudin
variable {a b : ℝ} {I : a < b} (P : Partition I) {f : ℝ → ℝ}

namespace Partition

/-- Each interval is non-empty. -/
theorem interval_nonempty (i : ℕ) : (P.interval i).Nonempty
  := by --
  dsimp only [Partition.interval, P.fn_eq]
  if hi : i < P.n then
    have : i - 1 < P.n := Nat.sub_lt_of_lt hi
    rw [dif_pos hi, dif_pos (Nat.sub_lt_of_lt hi), Set.nonempty_Icc]
    exact P.get_mono (Nat.sub_le i 1)
  else
  rw [dif_neg hi]
  push_neg at hi
  rcases hi.lt_or_eq with hlt | heq
  · have : ¬i - 1 < P.n := by
      have : P.n ≤ i - 1 := Nat.le_sub_one_of_lt hlt
      exact Nat.not_lt.mpr this
    rw [dif_neg this]
    exact Set.Nonempty.of_subtype
  · have : i - 1 < P.n := by
      have : 1 < i := by rw [<-heq]; exact P.one_lt_len
      rw [heq]
      exact Nat.sub_one_lt_of_lt this
    rw [dif_pos this, Set.nonempty_Icc]
    conv => rhs; rw [P.b_eqᵢ]
    refine P.get_mono ?_
    subst heq
    exact le_rfl -- ∎

theorem interval_subset (i : ℕ) : P.interval i ⊆ Icc a b
  := by --
  rintro x ⟨hx₀ : P (i - 1) ≤ x, hx₁ : x ≤ P i⟩
  have ha : a ≤ P (i - 1) := P.min_a₂ (i - 1)
  have hb : P i ≤ b := P.max_b₂ i
  refine ⟨?_, ?_⟩
  · exact ha.trans hx₀
  · exact hx₁.trans hb -- ∎

theorem mem_principalᵢ (i : Fin P.n) : P[i] ∈ Icc a b
  := by --
  refine ⟨?_, ?_⟩
  · exact P.min_a P[i] P.mem_indexedᵢ
  · exact P.max_b P[i] P.mem_indexedᵢ -- ∎

theorem interval_bdd_on (hf : BddOn f (Icc a b)) (i : ℕ)
  : BddOn f (P.interval i)
  := by --
  exact hf.anti (P.interval_subset i) -- ∎

end Partition
end Rudin
