import Mathlib.Data.Real.Archimedean

import Rudin.Defs.Partition

namespace Rudin

open Set

variable {a b : ℝ} {I : a < b} (P : Partition I)

namespace Partition

/-- Given any distance `ε`, there exists a partition such that each subinterval
is less than `ε` in width. -/
theorem exists_lt (I : a < b) {ε : ℝ} (hε : 0 < ε) : ∃ P : Partition I, ∀ i, |P i - P (i - 1)| < ε
  := by --
  obtain ⟨n, hn : (b - a) / ε + 1 < n⟩ := exists_nat_gt ((b - a) / ε + 1)
  have hbaε₀ : 0 < (b - a) / ε := div_pos (sub_pos.mpr I) hε
  have hn₁ : 1 < n := by
    refine (Nat.one_lt_cast (α := ℝ)).mp ?_
    exact (lt_add_of_pos_left 1 hbaε₀).trans hn
  have hn₀ : 0 < (n : ℝ) - 1 := by
    refine sub_pos.mpr ?_
    exact Nat.one_lt_cast.mpr hn₁
  have hn₀' : 0 < ((n : ℝ) - 1)⁻¹ := inv_pos_of_pos hn₀
  have hI : 0 < (b - a) * ((n : ℝ) - 1)⁻¹ := mul_pos (sub_pos.mpr I) hn₀'
  have hbaε₁ : (b - a) * ((n : ℝ) - 1)⁻¹ < ε := by
    replace hn : (b - a) / ε < n - 1 := lt_tsub_of_add_lt_right hn
    refine (div_lt_comm₀ hε ?_).mp hn
    exact hbaε₀.trans hn
  let f (i : ℕ) : ℝ := a + (b - a) * ((n : ℝ) - 1)⁻¹ * i
  have hfa : f 0 = a := by
    dsimp only [f]
    rw [Nat.cast_zero, mul_zero, add_zero]
  have hfb : f (n - 1) = b := by
    dsimp only [f]
    rw [Nat.cast_sub hn₁.le, Nat.cast_one]
    rw [inv_mul_cancel_right₀ hn₀.ne']
    exact add_sub_cancel a b
  have hf : StrictMonoOn f (Finset.range n) := by
    intro i hi j hj hij
    refine add_lt_add_right ?_ a
    refine mul_lt_mul_of_pos_left (Nat.cast_lt.mpr hij) ?_
    exact mul_pos (sub_pos.mpr I) hn₀'
  let P := Partition.ofFn I hf hfa hfb
  use P
  intro i
  have heqₙ : P.n = n := ofFn_eq_n I hf hfa hfb
  if hi₀ : i < P.n then
    rw [heqₙ] at hi₀
    have hi₁ : i - 1 < n := Nat.sub_lt_of_lt hi₀
    have : P i = f i := ofFn_eq_f I hf hfa hfb hi₀
    rw [ofFn_eq_f I hf hfa hfb hi₀, ofFn_eq_f I hf hfa hfb hi₁]
    if hi₀ : i = 0 then
      subst hi₀
      rw [sub_self, abs_zero]
      exact hε
    else
    have hi₀ : 0 < i := Nat.zero_lt_of_ne_zero hi₀
    dsimp only [f]
    rw [Nat.cast_pred hi₀, add_sub_add_left_eq_sub]
    rw [mul_sub, mul_one, <-sub_add, sub_self, zero_add]
    rw [abs_of_pos hI]
    exact hbaε₁
  else
    have hP := P.fn_eq₂ i
    rw [dif_neg hi₀] at hP
    rw [hP.1, hP.2, sub_self, abs_zero]
    exact hε -- ∎

end Partition
end Rudin
