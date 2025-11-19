import Rudin.Defs.Globals
import Rudin.Prelude.BddOn

import Rudin.Partition.Core
import Rudin.Partition.Core.Endpoints
import Rudin.Partition.Core.Index
import Rudin.Partition.Core.Length
import Rudin.Partition.Core.Monotone
import Rudin.Partition.Extend
import Rudin.Partition.Cover
import Rudin.Partition.Endpoints
import Rudin.Partition.Insert
import Rudin.Partition.Interval
import Rudin.Partition.Monotone
import Rudin.Partition.OrderBot
import Rudin.Partition.Prelude
import Rudin.Partition.Prelude.Nodup
import Rudin.Partition.Prelude.SortedList
import Rudin.Partition.Single
import Rudin.Partition.SpecialPartitions
import Rudin.Partition.Union

import Mathlib.Order.Interval.Finset.Defs

open Set

namespace Rudin

variable {a b : ℝ} {I : a < b} (P : Partition I)

example {n k : ℕ} {f : ℕ → ℝ} : ∑ i ∈ Finset.range n, f i =
  ∑ i ∈ Finset.range k, f i + ∑ i ∈ Finset.Ico k n, f i := by
  refine Eq.symm (Finset.sum_range_add_sum_Ico f ?_)
  sorry

private lemma L_mono₁ (x : ℝ)
  (hf : BddOn f (Icc a b))
  (hα : MonotoneOn α (Icc a b))
  : L P f α ≤ L (insert x P) f α
  := by
  if h : ¬(x ∉ P ∧ x ∈ Icc a b) then
    simp only [P.insert_eq]
    dsimp only [L, Partition.ι']
    simp only [h, ↓reduceDIte]
    exact le_rfl
  else
  rw [not_not] at h
  obtain ⟨hxP, hxI⟩ := h
  have : (insert x P).n = P.n + 1 := P.insert_n hxP hxI
  dsimp only [L]
  simp only [this]
  have : x ∈ insert x P := P.mem_insert_self_iff.mpr hxI
  obtain ⟨k, hk : insert x P k = x⟩ := (insert x P).mem_iff_x.mp this
  sorry

/-- If P' is a refinement of P, then the lower sum obtained from P' will be
greater or equal to that of P. -/
theorem L_mono₂
  (hf : BddOn f (Icc a b))
  (hα : MonotoneOn α (Icc a b))
  : Monotone fun P : Rudin.Partition I ↦ Rudin.L P f α
  := by
  intro P P' hle -- P' is a refinement of P
  change L P f α ≤ L P' f α
  obtain ⟨ℓ, heq⟩ := Partition.extendable_of_le hle
  subst heq
  induction ℓ generalizing P with
  | nil => exact le_rfl
  | cons x xs ih =>
  change L P f α ≤ L ((insert x P).extend xs) f α
  refine (L_mono₁ P x hf hα).trans ?_
  refine ih ?_
  exact (insert x P).le_extend xs

end Rudin
