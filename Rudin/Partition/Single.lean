import Rudin.Partition.Endpoints

namespace Rudin

variable {a b : ℝ} (I : a < b) (x : Set.Ioo a b)

namespace Partition

/-- Construct a partition that has at most three points: [a, x, b]. -/
noncomputable def single : Partition I
  := by --
  exact {
    l := [a, x, b]
    head' := rfl
    tail' := rfl
    sorted' := by
      open List in
      refine Pairwise.sortedLT ?_
      refine pairwise_cons_cons.mpr ?_
      refine ⟨?_, ?_, ?_⟩
      · exact x.prop.1
      · exact pairwise_pair.mpr I
      · exact pairwise_pair.mpr x.prop.2
  } -- ∎

/-- If the input `x` is within bounds, add it, else ignore. -/
-- noncomputable def single_unbounded (x : ℝ) :
-- Partition I := if hx : x ∈ Set.Icc a b then single I hx else ⊥

-- Some nice instant-wins.
example : (single I x).n = 3 :=rfl
example : x = (single I x) 1 := rfl
example : (single I x).interval 1 = Set.Icc a x := rfl
example : (single I x).interval 2 = Set.Icc (x : ℝ) b := rfl

theorem mem_single_self : ↑x ∈ single I x
  := by --
  change ↑x ∈ [a, ↑x, b].toFinset
  refine List.mem_toFinset.mpr ?_
  exact List.mem_cons_of_mem a List.mem_cons_self -- ∎

theorem mem_single_iff {y : ℝ} : y ∈ single I x ↔ (y = a ∨ y = b ∨ y = x)
  := by --
  constructor
  · intro h
    rw [single] at h
    have : y ∈ [a, x, b].toFinset := h
    simp only [List.toFinset_cons, List.toFinset_nil, insert_empty_eq,
               Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with h₁ | h₂ | h₃
    · exact Or.inl h₁
    · exact Or.inr (Or.inr h₂)
    · exact Or.inr (Or.inl h₃)
  · intro h
    rcases h with ha | hb | hyx
    · rw [ha]; exact (single I x).mem_a
    · rw [hb]; exact (single I x).mem_b
    · rw [hyx]; exact mem_single_self I x -- ∎

theorem single_cover (t : Set.Icc a b) :
  ↑t ∈ (single I x).interval 1 ∨
  ↑t ∈ (single I x).interval 2
  := by --
  have : Set.Icc a b = Set.Icc a x ∪ Set.Icc x b := by
    refine le_antisymm ?_ ?_
    · intro t ht
      rcases lt_or_ge t ↑x with hlt | hge
      · exact Or.inl ⟨ht.1, hlt.le⟩
      · exact Or.inr ⟨hge, ht.2⟩
    · intro t ht
      rcases ht with ha | hb
      · exact ⟨ha.1, ha.2.trans x.prop.2.le⟩
      · exact ⟨x.prop.1.le.trans hb.1, hb.2⟩
  have : ↑t ∈ Set.Icc a x ∪ Set.Icc x b := by rw [<-this]; exact t.prop
  exact this -- ∎

end Partition
end Rudin
