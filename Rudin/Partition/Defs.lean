import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Real.Archimedean
import Mathlib.Order.Interval.Finset.Nat

variable {a b : ℝ}

namespace Rudin

@[ext]
structure Partition (I : a < b) where
  /-- The list of boundary points of the partition. -/
  l : List ℝ
  head' : l.head? = some a
  tail' : l.getLast? = some b
  sorted' : l.Sorted (· < ·)

variable {I : a < b} (P : Partition I)

namespace Partition

/-- The number of boundary points of the partition -/
def n : ℕ := P.l.length

private lemma ℓ₀ {P : Partition I} : P.l ≠ []
  := by --
  have h := P.head'
  by_contra h'
  rw [h', List.head?_nil] at h
  contradiction -- ∎

/-- The recommended way of getting the value of the head, instead of
`head'` in the definitions. -/
def head : ℝ := P.l.head ℓ₀

/-- The recommended way of getting the value of the tail, instead of
`tail'` in the definitions. -/
def tail : ℝ := P.l.getLast ℓ₀

section Instances

/-- The i-th boundary point, but checked.
`a = x₀ < x₁ < ... < xₙ₋₁ = b` -/
instance {I : a < b} : GetElem (Partition I) ℕ ℝ fun P i ↦ i < P.n where
  getElem P i hi := P.l.get ⟨i, hi⟩

/-- The i-th boundary point, but unchecked.
`a = x₀ < x₁ < ... < xₙ₋₁ = b` -/
instance {I : a < b} : CoeFun (Partition I) (fun _ => ℕ → ℝ) where
  coe P i := if _ : i < P.n then P[i] else b

/-- The i-th interval. `[xᵢ₋₁, xᵢ]` -/
def interval (i : ℕ) : Set ℝ := Set.Icc (P (i - 1)) (P i)

lemma sorted_le (P : Partition I) : P.l.Sorted (· ≤ ·) := P.sorted'.le_of_lt

/-- The partition contains no duplicate boundary points. -/
lemma nodup : P.l.Nodup
  := by --
  rw [List.nodup_iff_pairwise_ne, List.pairwise_iff_get]
  intro i j hij
  exact (P.sorted'.get_strictMono hij).ne -- ∎

lemma eq_Finset_sort (P : Partition I) : P.l.toFinset.sort (· ≤ ·) = P.l
  := by -- ∎
  exact (List.toFinset_sort (· ≤ ·) P.nodup).mpr P.sorted_le -- ∎

/-- Each partition corresponds uniquely to a representative set. -/
instance : SetLike (Partition I) ℝ
  := by --
  exact {
    coe P := P.l.toFinset
    coe_injective' P₁ P₂ heq := by
      rewrite [Finset.coe_inj] at heq
      rewrite [Partition.ext_iff, <-P₁.eq_Finset_sort, <-P₂.eq_Finset_sort]
      exact congrArg (Finset.sort · (· ≤ ·)) heq
  } -- ∎

end Instances

end Partition

end Rudin
