import Mathlib.Data.Real.Archimedean

variable {A B : Set ℝ} (hA₀ : A.Nonempty) (hB₀ : B.Nonempty)

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

include hA₀ in
theorem sSup.mono (hB : BddAbove B) : A ⊆ B → sSup A ≤ sSup B
  := by --
  intro hAB
  exact csSup_le_csSup hB hA₀ hAB -- ∎

include hA₀ in
theorem sInf.anti (hB : BddBelow B) : A ⊆ B → sInf B ≤ sInf A
  := by --
  intro hAB
  exact csInf_le_csInf hB hA₀ hAB -- ∎

include hA₀ in
theorem sSup.set_add_right (hA : BddAbove A) (b : ℝ) : sSup A + b = sSup { a + b | a ∈ A }
  := by --
  have hAb₀ : { a + b | a ∈ A }.Nonempty := by
    obtain ⟨a₀, ha₀⟩ := hA₀
    exact ⟨a₀ + b, a₀, ha₀, rfl⟩
  refine le_antisymm ?_ ?_
  · refine (Real.le_sSup_iff ?_ hAb₀).mpr ?_
    · obtain ⟨M, hM⟩ := hA
      use M + b
      intro y ⟨x, hxA, heq⟩
      subst heq
      exact add_le_add_right (hM hxA) b
    · intro ε hε
      rw [<-Left.neg_pos_iff] at hε
      obtain ⟨x, hxA, hlt⟩ := sSup.exist_sub_lt_ε hA₀ hA (-ε) hε
      refine ⟨x + b, ⟨x, hxA, rfl⟩, ?_⟩
      rw [add_right_comm]
      refine add_lt_add_right ?_ b
      rw [<-lt_add_neg_iff_add_lt]
      exact lt_add_of_tsub_lt_left hlt
  · refine csSup_le hAb₀ ?_
    intro y ⟨x, hxA, heq⟩
    subst heq
    exact add_le_add_right (ConditionallyCompleteLattice.le_csSup A x hA hxA) _ -- ∎

include hA₀ in
theorem sSup.set_add_left (hA : BddAbove A) (b : ℝ) : b + sSup A = sSup { b + a | a ∈ A }
  := by --
  have : { b + a | a ∈ A } = { a + b | a ∈ A } := by simp only [add_comm]
  rw [this, add_comm]
  exact set_add_right hA₀ hA b -- ∎

include hA₀ in
theorem sSup.set_sub (hA : BddAbove A) (b : ℝ) : sSup A - b = sSup { a - b | a ∈ A }
  := by -- ∎
  exact set_add_right hA₀ hA (-b) -- ∎

include hA₀ in
theorem sInf.set_add_right (hA : BddBelow A) (b : ℝ) : sInf A + b = sInf { a + b | a ∈ A }
  := by --
  simp only [sInf]
  rw [<-neg_eq_iff_eq_neg]
  rw [neg_add, neg_neg]
  rw [sSup.set_add_right hA₀.neg hA.neg (-b)]
  refine congrArg sSup ?_
  refine le_antisymm ?_ ?_
  · intro y ⟨x, hx, heq⟩
    subst heq
    refine ⟨-x, hx, ?_⟩
    rw [neg_add']
    exact (sub_neg_eq_add (-x) b).symm
  · rintro y ⟨x, hx, heq : x + b = -y⟩
    rw [<-neg_eq_iff_eq_neg] at heq
    subst heq
    refine ⟨-x, Set.neg_mem_neg.mpr hx, ?_⟩
    exact (neg_add x b).symm -- ∎

include hA₀ in
theorem sInf.set_add_left (hA : BddBelow A) (b : ℝ) : b + sInf A = sInf { b + a | a ∈ A }
  := by --
  have : { b + a | a ∈ A } = { a + b | a ∈ A } := by simp only [add_comm]
  rw [this, add_comm]
  exact set_add_right hA₀ hA b -- ∎

include hA₀ in
theorem sInf.set_sub (hA : BddBelow A) (b : ℝ) : sInf A - b = sInf { a - b | a ∈ A }
  := by --
  exact set_add_right hA₀ hA (-b) -- ∎

include hA₀ in
theorem sInf.sub_set (hA : BddBelow A) (b : ℝ) : b - sInf A = sSup { b - a | a ∈ A }
  := by --
  have hAb₀ : { b - a | a ∈ A }.Nonempty := by
    obtain ⟨a₀, ha₀⟩ := hA₀
    exact ⟨b - a₀, a₀, ha₀, rfl⟩
  refine le_antisymm ?_ ?_
  · refine (Real.le_sSup_iff ?_ hAb₀).mpr ?_
    · obtain ⟨m, hm⟩ := hA
      use b - m
      intro y ⟨x, hx, heq⟩
      subst heq
      exact tsub_le_tsub_left (hm hx) b
    · intro ε hε
      rw [<-Left.neg_pos_iff] at hε
      obtain ⟨x, hxA, hlt⟩ := sInf.exist_sub_lt_ε hA₀ hA (-ε) hε
      refine ⟨b - x, ⟨x, hxA, rfl⟩, ?_⟩
      rw [sub_add]
      exact sub_lt_sub_left (lt_add_of_tsub_lt_left hlt) b
  · refine csSup_le hAb₀ ?_
    · intro y ⟨x, hx, heq⟩
      subst heq
      refine sub_le_sub_left ?_ b
      exact ConditionallyCompleteLattice.csInf_le A x hA hx -- ∎

lemma eq_zero_of_nonneg_le_pos {a : ℝ} (ha : 0 ≤ a) : (∀ ε > 0, a ≤ ε) → a = 0
  := by --
  intro h
  rcases ha.eq_or_lt with heq | hlt
  · exact heq.symm
  · specialize h (a / 2) (half_pos hlt)
    exact False.elim (h.not_gt (div_two_lt_of_pos hlt)) -- ∎
