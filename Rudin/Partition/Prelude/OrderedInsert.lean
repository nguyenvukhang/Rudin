import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Real.Basic

universe u

variable {l : List ℝ} {x : ℝ} (hl : l.SortedLT) (hx : x ∉ l) {i j k : ℕ}

namespace List

theorem SortedLT.orderedInsert_sortedLE (hl : l.SortedLT) : (l.orderedInsert (· ≤ ·) x).SortedLE
  := by --
  exact (hl.sortedLE.pairwise.orderedInsert x l).sortedLE -- ∎

theorem SortedLE.orderedInsert_sortedLE (hl : l.SortedLE) : (l.orderedInsert (· ≤ ·) x).SortedLE
  := by --
  exact (hl.pairwise.orderedInsert x l).sortedLE -- ∎

theorem mem_orderedInsert_self {α : Type u} (r : α → α → Prop)
  [DecidableRel r] {a : α} {l : List α} : a ∈ orderedInsert r a l
  := by --
  exact (mem_orderedInsert r).mpr (Or.inl rfl) -- ∎

theorem SortedLE.orderedInsert_eq (hl : (x :: l).SortedLE)
  : l.orderedInsert (· ≤ ·) x = x :: l
  := by --
  induction l with
  | nil => exact rfl
  | cons y ys ih =>
    rw [List.orderedInsert]
    have : x ≤ y := by
      obtain ⟨h, _⟩ := List.pairwise_cons.mp hl.pairwise
      exact h y mem_cons_self
    simp only [↓reduceIte, this] -- ∎

/-- `Nodup` list implies that its orderedInsert is also `Nodup`. -/
theorem Nodup.orderedInsert (hl : l.Nodup) (hx : x ∉ l) : (l.orderedInsert (· ≤ ·) x).Nodup
  := by --
  let r : ℝ → ℝ → Prop := (· ≤ ·)
  induction l with
  | nil =>
    rw [List.orderedInsert, nodup_cons]
    exact ⟨not_mem_nil, hl⟩
  | cons y ys ih =>
    change ((y :: ys).orderedInsert r x).Nodup
    rw [List.orderedInsert]
    if hle : r x y then -- x ≤ y
      simp only [↓reduceIte, hle]
      exact hl.cons hx
    else
      simp only [↓reduceIte, hle]
      refine nodup_cons.mpr ?_
      specialize ih hl.of_cons (not_mem_of_not_mem_cons hx)
      refine ⟨?_, ih⟩
      rw [mem_orderedInsert, not_or]
      refine ⟨?_, hl.notMem⟩
      exact (ne_of_not_mem_cons hx).symm -- ∎

include hl in
theorem SortedLT.orderedInsert_of_lt :
  l.orderedInsert (· < ·) x = l.orderedInsert (· ≤ ·) x
  := by --
  induction l with
  | nil => exact rfl
  | cons y ys ih =>
    specialize ih hl.pairwise.of_cons.sortedLT
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
      exact SortedLE.orderedInsert_eq hl.sortedLE
    · -- x > y
      have : ¬lt x y := hgt.not_gt
      simp only [↓reduceIte, this]
      have : ¬le x y := hgt.not_ge
      simp only [↓reduceIte, this]
      exact congrArg (List.cons y) ih -- ∎

-- This is the ultimate goal.
include hl hx in
theorem SortedLT.orderedInsert_sorted_lt
  : (l.orderedInsert (· ≤ ·) x).SortedLT
  := by --
  have h₀ : l.Nodup := by
    rw [List.nodup_iff_pairwise_ne, List.pairwise_iff_get]
    intro i j hij
    exact (hl hij).ne
  exact hl.orderedInsert_sortedLE.sortedLT_of_nodup (h₀.orderedInsert hx) -- ∎

-- main: List.getElem_cons_succ
private lemma ℓ₁ {y : ℝ} {ys : List ℝ} {i : ℕ} (hi₀ : 0 < i) (hi : i < (y :: ys).length) :
  haveI : i - 1 < ys.length := Nat.sub_lt_right_of_lt_add hi₀ hi
  (y :: ys)[i] = ys[i - 1]
  := by --
  induction i with
  | zero =>
    refine False.elim ?_
    exact Nat.not_succ_le_zero 0 hi₀
  | succ k ih =>
    simp only [getElem_cons_succ, add_tsub_cancel_right] -- ∎

include hl hx in
theorem orderedInsert_leᵢ (hi : i < l.length) :
  haveI : i < (l.orderedInsert (· ≤ ·) x).length := by
    rw [orderedInsert_length]
    exact Nat.lt_add_right 1 hi
  l[i] ≤ x → l[i] = (l.orderedInsert (· ≤ ·) x)[i]
  := by --
  intro hle
  induction l generalizing i with
  | nil =>
    exact False.elim (Nat.not_succ_le_zero i hi)
  | cons y ys ih =>
    simp only [orderedInsert]
    have : y < x := by
      have : y ≤ (y :: ys)[i] := by
        change (y :: ys)[0] ≤ (y :: ys)[i]
        exact hl.sortedLE (Nat.zero_le i)
      exact (this.trans hle).lt_of_ne' (ne_of_not_mem_cons hx)
    simp only [↓reduceIte, this.not_ge]
    if hi₀ : i = 0 then subst hi₀; simp only [getElem_cons_zero] else
    have hi₁ : i - 1 + 1 = i := Nat.succ_pred_eq_of_ne_zero hi₀
    -- idea: use induction hypothesis with i - 1
    have hxys : x ∉ ys := not_mem_of_not_mem_cons hx
    have : i - 1 < ys.length := by
      refine Nat.sub_one_lt_of_le ?_ ?_
      · exact Nat.zero_lt_of_ne_zero hi₀
      · exact Nat.le_of_lt_succ hi
    specialize ih hl.pairwise.of_cons.sortedLT hxys this
    have heqᵢ := ℓ₁ (Nat.zero_lt_of_ne_zero hi₀) hi
    rw [heqᵢ] at hle
    specialize ih hle
    rw [heqᵢ, ih]
    refine (ℓ₁ ?_ _).symm
    exact Nat.zero_lt_of_ne_zero hi₀ -- ∎

include hl hx in
theorem orderedInsert_geᵢ (hi : i < l.length) :
  haveI : i + 1 < (l.orderedInsert (· ≤ ·) x).length := by
    rw [orderedInsert_length]
    exact Nat.add_lt_add_right hi 1
  x ≤ l[i] → l[i] = (l.orderedInsert (· ≤ ·) x)[i + 1]
  := by --
  intro hge
  induction l generalizing i with
  | nil =>
    exact False.elim (Nat.not_succ_le_zero i hi)
  | cons y ys ih =>
    simp only [orderedInsert]
    if hxy : x ≤ y then
      simp only [↓reduceIte, hxy]
      exact rfl
    else
      simp only [↓reduceIte, hxy]
      replace hxy : y < x := lt_of_not_ge hxy
      if hi₀ : i = 0 then subst hi₀; exact False.elim (hxy.not_ge hge) else
      have : i - 1 < ys.length := by
        refine Nat.sub_one_lt_of_le ?_ ?_
        · exact Nat.zero_lt_of_ne_zero hi₀
        · exact Nat.le_of_lt_succ hi
      specialize ih hl.pairwise.of_cons.sortedLT (not_mem_of_not_mem_cons hx) this
      have heqᵢ := ℓ₁ (Nat.zero_lt_of_ne_zero hi₀) hi
      have : x ≤ ys[i - 1] := le_of_le_of_eq hge heqᵢ
      specialize ih this
      have hi_sub : i - 1 + 1 = i := Nat.succ_pred_eq_of_ne_zero hi₀
      simp only [hi_sub] at ih
      rw [heqᵢ]
      exact ih -- ∎

include hl hx in
theorem orderedInsert_get (hi : i < l.length) :
  haveI : i + 1 < (l.orderedInsert (· ≤ ·) x).length := by
    rw [orderedInsert_length]
    exact Nat.succ_lt_succ hi
  l[i] = if l[i] ≤ x then
    (l.orderedInsert (· ≤ ·) x)[i]
  else
    (l.orderedInsert (· ≤ ·) x)[i + 1]
  := by --
  rcases le_total l[i] x with hle | hge
  · simp only [↓reduceIte, hle]
    exact orderedInsert_leᵢ hl hx hi hle
  · have : ¬l[i] ≤ x := by
      refine not_le_of_gt (hge.lt_of_ne' ?_)
      contrapose! hx
      exact mem_of_getElem hx
    simp only [↓reduceIte, this]
    exact orderedInsert_geᵢ hl hx hi hge -- ∎

include hl hx in
theorem orderedInsert_lt (hik : i < k) (hk : k < l.length + 1) :
  haveI : k < (l.orderedInsert (· ≤ ·) x).length := by rw [orderedInsert_length]; exact hk
  haveI : i < l.length := hik.trans_le (Nat.le_of_lt_succ hk)
  (l.orderedInsert (· ≤ ·) x)[k] = x → l[i] ≤ x
  := by --
  have hil : i < l.length := hik.trans_le (Nat.le_of_lt_succ hk)
  intro hkx
  by_contra hle
  have := orderedInsert_get hl hx hil
  simp only [↓reduceIte, hle] at this
  have hlt : x < l[i] := lt_of_not_ge hle
  rw [<-hkx, this] at hlt
  refine hlt.not_ge ?_
  refine hl.orderedInsert_sortedLE hik -- ∎

include hl hx in
theorem orderedInsert_ge (hik : i ≥ k) (hi : i < l.length) (hk : k < l.length + 1) :
  haveI : k < (l.orderedInsert (· ≤ ·) x).length := by rw [orderedInsert_length]; exact hk
  (l.orderedInsert (· ≤ ·) x)[k] = x → x ≤ l[i]
  := by --
  intro hkx
  by_contra hle'
  have hle : l[i] ≤ x := Std.le_of_not_ge hle'
  have hlt : l[i] < x := lt_of_le_not_ge hle hle'
  have := orderedInsert_get hl hx hi
  simp only [↓reduceIte, hle] at this
  rw [<-hkx, this] at hlt
  refine hlt.not_ge ?_
  exact hl.orderedInsert_sortedLE hik -- ∎

end List
