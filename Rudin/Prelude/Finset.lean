import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

theorem Finset.sum_fin {f : ℕ → ℝ} {n : ℕ} : ∑ i : Fin n, f i = ∑ i < n, f i
  := by --
  have : Finset.range n = Finset.Iio n := by
    refine Finset.ext ?_
    intro _
    simp only [Finset.mem_range, Finset.mem_Iio]
  rw [Fin.sum_univ_eq_sum_range, this] -- ∎

example {f : ℕ → ℝ} {n : ℕ} : ∑ i : Fin n, f i = ∑ i ∈ Finset.range n, f i
  := by --
  exact Fin.sum_univ_eq_sum_range f n -- ∎

theorem Finset.sum_Iio_eq_range {f : ℕ → ℝ} {n : ℕ} : ∑ i < n, f i = ∑ i ∈ Finset.range n, f i
  := by --
  rw [<-sum_fin]
  exact Fin.sum_univ_eq_sum_range f n -- ∎

example {f : ℕ → ℝ} {n : ℕ} : ∑ i ∈ Finset.range n, (f (i + 1) - f i) = f n - f 0
  := by --
  exact Finset.sum_range_sub f n -- ∎

theorem Finset.sum_range_sub₁ (f : ℕ → ℝ) (n : ℕ)
  : ∑ i ∈ Finset.range n, (f i - f (i - 1)) = f (n - 1) - f 0
  := by --
  induction n with
  | zero =>
    rw [Finset.range_zero, Finset.sum_sub_distrib]
    simp only [Finset.sum_empty, sub_self, zero_tsub]
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    rw [sub_add_sub_cancel', add_tsub_cancel_right] -- ∎
