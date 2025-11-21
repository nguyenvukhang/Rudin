import Mathlib.Data.Set.Lattice
import Mathlib.Order.Interval.Set.LinearOrder

import Rudin.Partition.Endpoints
import Rudin.Partition.Prelude
import Rudin.Partition.OrderBot
import Rudin.Partition.Insert

namespace Rudin

open Set

variable {a b x : ℝ} {I : a < b} {P₁ P₂ : Partition I} {ℓ : List ℝ}

namespace Partition

noncomputable def extend (P : Partition I) : List ℝ → Partition I
  | [] => P
  | x :: xs => (insert x P).extend xs

theorem extend_mono (ℓ : List ℝ)
  : Monotone (fun P : Partition I ↦ P.extend ℓ)
  := by --
  intro P₁ P₂ hle
  induction ℓ generalizing P₁ P₂ with
  | nil => exact hle
  | cons x xs ih => exact ih (insert_mono x hle) -- ∎

/-- If P₁ ≤ P₂, and `xs` is a list fully contained in P₂, then using all of
`xs` to refine P₁ will still not give us a finer partition than P₂. -/
lemma extend_le (hxs : ∀ t ∈ ℓ, t ∈ P₂)
  : P₁ ≤ P₂ → P₁.extend ℓ ≤ P₂
  := by --
  intro hP
  induction ℓ generalizing P₁ P₂ with
  | nil => exact hP
  | cons x xs ih =>
    change (insert x P₁).extend xs ≤ P₂
    have hxsᵢ : ∀ t ∈ xs, t ∈ P₂ := (hxs · <| List.mem_cons_of_mem x ·)
    refine ih hxsᵢ ?_
    intro t ht
    rw [mem_insert_iff] at ht
    rcases ht with ⟨htx, htI⟩ | htP₁
    · subst htx
      exact hxs t List.mem_cons_self
    · exact hP htP₁ -- ∎

lemma le_extend (P : Partition I) (ℓ : List ℝ) : P ≤ P.extend ℓ
  := by --
  intro t ht
  induction ℓ generalizing P with
  | nil => exact ht
  | cons x xs ih =>
  change t ∈ (ι' x P).extend xs
  dsimp only [ι', ι]
  if h : P.IsInsertable x then
    rw [dif_pos h]
    refine ih _ ?_
    rw [mem_iff_mem_list, List.mem_orderedInsert]
    refine Or.inr ?_
    exact P.mem_iff_mem_list.mp ht
  else
  rw [dif_neg h]
  exact ih P ht -- ∎

/-- If `ℓ` is used to extend/refine partition P, then all elements of `ℓ` that
are in `[a, b]` shall be found in the resulting partition. -/
private lemma mem_extender (P : Partition I) {t : ℝ}
  : t ∈ ℓ → t ∈ Icc a b → t ∈ P.extend ℓ
  := by --
  intro ht htI
  induction ℓ with
  | nil => exact False.elim ((List.mem_nil_iff t).mp ht)
  | cons x xs ih =>
  change t ∈ (insert x P).extend xs
  if htx : t = x then
    subst htx
    have : t ∈ insert t P := P.mem_insert_self_iff.mpr htI
    exact (insert t P).le_extend xs this
  else
  specialize ih (List.mem_of_ne_of_mem htx ht)
  have : P.extend xs ≤ (insert x P).extend xs := extend_mono xs (le_insert P)
  exact this ih -- ∎

lemma extends_bot {P : Partition I} : (⊥ : Partition I).extend P.l = P
  := by --
  refine le_antisymm ?_ ?_
  · intro x hx
    refine extend_le ?_ (OrderBot.bot_le P) hx
    intro t
    exact P.mem_iff_mem_list.mpr
  · intro x hx
    refine (⊥ : Partition I).mem_extender ?_ (P.subset_Icc hx)
    exact P.mem_iff_mem_list.mp hx -- ∎

private lemma extendable_of_le' : P₁ ≤ P₂ → P₁.extend P₂.l = P₂
  := by --
  intro hP
  refine le_antisymm ?_ ?_
  · apply extend_le ?_ hP
    intro t
    exact P₂.mem_iff_mem_list.mpr
  · intro x hx
    refine mem_extender ?_ ?_ ?_
    · exact P₂.mem_iff_mem_list.mp hx
    · exact P₂.subset_Icc hx -- ∎

/-- If P₁ ≤ P₂, then it takes a finite number of points to bring P₁ to P₂. -/
theorem extendable_of_le : P₁ ≤ P₂ → ∃ ℓ, P₁.extend ℓ = P₂
  := by --
  exact (⟨P₂.l, extendable_of_le' ·⟩) -- ∎

end Partition
end Rudin
