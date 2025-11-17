import Mathlib.Data.Real.Archimedean

variable {A : Set ℝ} (hA₀ : A.Nonempty)

include hA₀ in
theorem sSup.exist_sub_lt_ε (hA : BddAbove A)
  : ∀ ε > 0, ∃ a ∈ A, sSup A - a < ε
  := by --
  intro ε hε
  let m := (Real.exists_isLUB hA₀ hA).choose
  let hm : IsLUB A m := (Real.exists_isLUB hA₀ hA).choose_spec
  dsimp only [sSup]
  rw [dif_pos ⟨hA₀, hA⟩]
  by_contra! h
  have : m - ε ∈ upperBounds A := by
    intro a ha
    specialize h a ha
    exact le_sub_comm.mp h
  refine (hm.2 this).not_gt ?_
  exact sub_lt_self m hε -- ∎

include hA₀ in
theorem sInf.exist_sub_lt_ε (hA : BddBelow A)
  : ∀ ε > 0, ∃ a ∈ A, a - sInf A < ε
  := by --
  intro ε hε
  obtain ⟨a, haA, ha⟩ := sSup.exist_sub_lt_ε hA₀.neg hA.neg ε hε
  refine ⟨-a, haA, ?_⟩
  dsimp only [sInf]
  rw [sub_neg_eq_add, neg_add_eq_sub]
  exact ha -- ∎

lemma eq_zero_of_nonneg_le_pos {a : ℝ} (ha : 0 ≤ a) : (∀ ε > 0, a ≤ ε) → a = 0
  := by --
  intro h
  rcases ha.eq_or_lt with heq | hlt
  · exact heq.symm
  · specialize h (a / 2) (half_pos hlt)
    exact False.elim (h.not_gt (div_two_lt_of_pos hlt)) -- ∎
