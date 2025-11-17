import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Real.Basic

variable {l : List ℝ} {x : ℝ}

namespace List

theorem Sorted.orderedInsert_eq (hl : (x :: l).Sorted (· ≤ ·))
  : l.orderedInsert (· ≤ ·) x = x :: l
  := by --
  induction l with
  | nil => exact rfl
  | cons y ys ih =>
    rw [List.orderedInsert]
    have : x ≤ y := by
      rw [sorted_cons] at hl
      obtain ⟨h, _⟩ := hl
      exact h y mem_cons_self
    simp only [↓reduceIte, this] -- ∎

theorem Nodup.orderedInsert (hl : l.Nodup) (hx : x ∉ l) : (l.orderedInsert (· ≤ ·) x).Nodup
  := by --
  let r : ℝ → ℝ → Prop := (· ≤ ·)
  induction l with
  | nil =>
    rw [List.orderedInsert, nodup_cons];
    exact ⟨not_mem_nil, hl⟩
  | cons y ys ih =>
    have hys : ys.Nodup := hl.of_cons
    have hxys : x ∉ ys := not_mem_of_not_mem_cons hx
    specialize ih hl.of_cons (not_mem_of_not_mem_cons hx)
    change (ys.orderedInsert r x).Nodup at ih
    change ((y :: ys).orderedInsert r x).Nodup
    rw [List.orderedInsert]
    if hle : x ≤ y then
      have : r x y := hle
      simp only [↓reduceIte, this]
      exact hl.cons hx
    else
      have : ¬r x y := hle
      simp only [↓reduceIte, this]
      refine nodup_cons.mpr ?_
      refine ⟨?_, ih⟩
      rw [mem_orderedInsert]
      push_neg
      refine ⟨?_, hl.notMem⟩
      exact (ne_of_not_mem_cons hx).symm -- ∎

theorem Sorted.orderedInsert_of_lt (hl : l.Sorted (· < ·)) :
  l.orderedInsert (· < ·) x = l.orderedInsert (· ≤ ·) x
  := by --
  induction l with
  | nil => exact rfl
  | cons y ys ih =>
    specialize ih hl.of_cons
    let lt : ℝ → ℝ → Prop := (· < ·)
    let le : ℝ → ℝ → Prop := (· ≤ ·)
    change (y :: ys).orderedInsert lt x = (y :: ys).orderedInsert le x
    change List.orderedInsert lt x ys = List.orderedInsert le x ys at ih

    simp only [List.orderedInsert]

    rcases lt_trichotomy x y with hlt | heq | hgt
    · -- x < y
      have : lt x y := hlt
      simp only [↓reduceIte, this]
      have : le x y := hlt.le
      simp only [↓reduceIte, this]
    · -- x = y
      subst heq
      have : ¬lt x x := lt_irrefl x
      simp only [↓reduceIte, this]
      have : le x x := Std.IsPreorder.le_refl x
      simp only [↓reduceIte, this]
      refine (cons_inj_right x).mpr ?_
      rw [ih]
      exact hl.le_of_lt.orderedInsert_eq
    · -- x > y
      have : ¬lt x y := hgt.not_gt
      simp only [↓reduceIte, this]
      have : ¬le x y := hgt.not_ge
      simp only [↓reduceIte, this]
      exact congrArg (List.cons y) ih -- ∎

-- This is the ultimate goal.
theorem Sorted.orderedInsert_sorted_lt (hlt : l.Sorted (· < ·)) (hx : x ∉ l)
  : (l.orderedInsert (· ≤ ·) x).Sorted (· < ·)
  := by --
  have h₁ : (l.orderedInsert (· ≤ ·) x).Sorted (· ≤ ·) := hlt.le_of_lt.orderedInsert x l
  have h₀ : l.Nodup := by
    rw [List.nodup_iff_pairwise_ne, List.pairwise_iff_get]
    intro i j hij
    exact (hlt.get_strictMono hij).ne
  exact h₁.lt_of_le (h₀.orderedInsert hx) -- ∎

example : ∃ k : Fin (l.orderedInsert (· ≤ ·) x).length,
  ∀ i, (hi : i < k) →
  haveI : i < l.length := by
    suffices i + 1 < l.length + 1 by exact Nat.succ_lt_succ_iff.mp this
    rw [<-l.orderedInsert_length (· ≤ ·) x]
    refine k.is_lt.trans_le' hi
  l[i] = (l.orderedInsert (· ≤ ·) x)[i] := by
  let le : ℝ → ℝ → Prop := (· ≤ ·)
  let l' := l.orderedInsert le x
  have hxl' : x ∈ l' := (mem_orderedInsert le).mpr (Or.inl rfl)
  obtain ⟨k, hk⟩ := mem_iff_get.mp hxl'
  use k
  intro i hik
  have hi : i < l.length := by
    suffices i + 1 < l.length + 1 by exact Nat.succ_lt_succ_iff.mp this
    rw [<-l.orderedInsert_length (· ≤ ·) x]
    refine k.is_lt.trans_le' hik
  induction l with
  | nil =>
    exact False.elim (Nat.not_succ_le_zero i hi)
  | cons y ys ih =>
    simp only [orderedInsert.eq_2, orderedInsert]
    have : x ∈ ys := by
      sorry
    if hxy : x ≤ y then
      simp only [↓reduceIte, hxy]
      sorry
    else
      simp only [↓reduceIte, hxy]
      sorry

example : ∃ k : Fin l.length,
  ∀ i, (hi : i < k) →
  haveI : i < (l.orderedInsert (· ≤ ·) x).length := by
    rw [l.orderedInsert_length (· ≤ ·) x]
    exact (Nat.lt_add_right 1 k.is_lt).trans' hi
  l[i] = (l.orderedInsert (· ≤ ·) x)[i] := by
  let le : ℝ → ℝ → Prop := (· ≤ ·)
  let l' := l.orderedInsert le x
  have hxl' : x ∈ l' := (mem_orderedInsert le).mpr (Or.inl rfl)
  obtain ⟨k, hk⟩ := mem_iff_get.mp hxl'
  -- intro i hik
  sorry

end List
