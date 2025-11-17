import Rudin.Partition.Endpoints

namespace Rudin
variable {a b : ℝ} {I : a < b} (P : Partition I)

namespace Partition

theorem interval_subset (i : ℕ) : P.interval i ⊆ Set.Icc a b := by
  rintro x ⟨hx₀ : P (i - 1) ≤ x, hx₁ : x ≤ P i⟩
  have ha : a ≤ P (i - 1) := P.min_a₂ (i - 1)
  have hb : P i ≤ b := P.max_b₂ i
  refine ⟨?_, ?_⟩
  · exact ha.trans hx₀
  · exact hx₁.trans hb

theorem mem_principal_fin {i : Fin P.n} : P[i] ∈ Set.Icc a b
  := by --
  refine ⟨?_, ?_⟩
  · exact P.min_a P[i] P.mem_indexed_fin
  · exact P.max_b P[i] P.mem_indexed_fin -- ∎

theorem mem_principal {i : ℕ} (hi : i < P.n) : P[i] ∈ Set.Icc a b
  := by --
  refine ⟨?_, ?_⟩
  · refine P.min_a P[i] ?_
    rw [P.mem_iff_mem_list]
    exact List.mem_of_getElem rfl
  · refine P.max_b P[i] ?_
    rw [P.mem_iff_mem_list]
    exact List.mem_of_getElem rfl -- ∎


end Partition
end Rudin
