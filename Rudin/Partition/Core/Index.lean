import Rudin.Partition.Defs
import Rudin.Partition.Core.Endpoints
import Rudin.Partition.Core.Monotone

namespace Rudin

variable {a b x : ℝ} {I : a < b} (P : Partition I)

namespace Partition

-- All the equivalences of index fetching. Everything leads back to `P i`.
namespace ieq
section IndexEquivalence
lemma get_fin {i : Fin P.n} : P i = P.l.get i := dif_pos i.is_lt
lemma get_cond {i : ℕ} (hi : i < P.n) : P i = P.l.get ⟨i, hi⟩ := dif_pos hi
lemma l_fin {i : Fin P.n} : P i = P.l[i] := dif_pos i.is_lt
lemma l_cond {i : ℕ} (hi : i < P.n) : P i = P.l[i] := dif_pos hi
lemma idx_fin {i : Fin P.n} : P i = P[i] := dif_pos i.is_lt
lemma idx_cond {i : ℕ} (hi : i < P.n) : P i = P[i] := dif_pos hi
end IndexEquivalence
end ieq

theorem mem_iff_mem_list : x ∈ P ↔ x ∈ P.l
  := by --
  exact List.mem_toFinset -- ∎

theorem mem_indexed {i : ℕ} : P i ∈ P
  := by --
  dsimp only
  if hi : i < P.n then
    rw [dif_pos hi, P.mem_iff_mem_list]
    exact List.mem_of_getElem rfl
  else
    rw [dif_neg hi]
    exact P.mem_b -- ∎

theorem mem_indexed_fin {i : Fin P.n} : P[i] ∈ P
  := by --
  rw [P.mem_iff_mem_list]
  exact List.mem_of_getElem rfl -- ∎

theorem mem_iff_x {x : ℝ} : x ∈ P ↔ ∃ i, P i = x
  := by --
  constructor
  · intro hxP
    rw [P.mem_iff_mem_list, List.mem_iff_get] at hxP
    obtain ⟨i, hi⟩ := hxP
    refine ⟨i, ?_⟩
    have : ↑i < P.n := i.is_lt
    simp only [↓reduceDIte, this]
    exact hi
  · intro ⟨i, heq⟩
    subst heq
    exact P.mem_indexed -- ∎

theorem exists_fin_index_of_mem {x : ℝ} : x ∈ P → ∃ i < P.n, P i = x
  := by --
  intro hxP
  rw [P.mem_iff_mem_list, List.mem_iff_get] at hxP
  obtain ⟨i, hi⟩ := hxP
  refine ⟨i, i.is_lt, ?_⟩
  rw [Partition.ieq.get_fin]
  exact hi -- ∎

theorem le_index_of_eq_b {i : ℕ} : P i = b → P.n - 1 ≤ i
  := by --
  contrapose!
  intro h
  rw [dif_pos (Nat.lt_of_lt_pred h)]
  conv => rhs; rw [<-P.idx_eq_b]
  exact (P.get_strictMono h).ne -- ∎

end Partition
end Rudin
