import Rudin.Partition.Prelude
import Rudin.Partition.Core.Length
import Rudin.Partition.Endpoints

namespace Rudin

open Set

variable {a b x : ℝ} {I : a < b} {P P₁ P₂ : Partition I} {ℓ : List ℝ}

namespace Partition

/-- A check to see if the element `x` can be inserted into partition `P`. -/
structure IsInsertable (x : ℝ) (P : Partition I) : Prop where
  notMem' : x ∉ P
  Icc' : x ∈ Icc a b

namespace IsInsertable

lemma not_of_mem : x ∈ P → ¬P.IsInsertable x
  := by --
  intro hxP h
  exact False.elim (h.notMem' hxP) -- ∎
lemma not_of_lt_a : x < a → ¬P.IsInsertable x
  := by --
  intro hxa h
  exact False.elim (hxa.not_ge h.Icc'.1) -- ∎
lemma not_of_gt_b : b < x → ¬P.IsInsertable x
  := by --
  intro hbx h
  exact False.elim (hbx.not_ge h.Icc'.2) -- ∎
lemma ge_a (h : IsInsertable x P) : a ≤ x := h.Icc'.left
lemma le_b (h : IsInsertable x P) : x ≤ b := h.Icc'.right

end IsInsertable

noncomputable def ι (h : IsInsertable x P) : Partition I
  := by --
  let l' := P.l.orderedInsert (· ≤ ·) x
  have sorted' : l'.SortedLT := by
    refine P.sorted'.orderedInsert_sorted_lt ?_
    rw [<-P.mem_iff_mem_list]
    exact h.notMem'
  have h₀ : l' ≠ [] := by
    refine List.ne_nil_of_length_pos ?_
    rw [List.orderedInsert_length]
    exact Nat.zero_lt_succ P.l.length
  refine { l := P.l.orderedInsert (· ≤ ·) x, sorted', head' := ?_, tail' := ?_ }
  · rw [<-List.head_eq_iff_head?_eq_some h₀]
    refine le_antisymm ?_ ?_
    · -- head ≤ a. This follows from the current list being sorted.
      have ha' : a ∈ l' := by
        rw [List.mem_orderedInsert]
        exact Or.inr P.mem_aᵢ
      exact sorted'.sortedLE.sorted_head_min h₀ a ha'
    · -- a ≤ head. This follows from the minimality of a ∈ P.
      have h : l'.head h₀ ∈ l' := List.head_mem h₀
      rw [List.mem_orderedInsert] at h
      rcases h with hx | hP
      · rw [hx]
        exact h.Icc'.1
      · have : l'.head h₀ ∈ P := P.mem_iff_mem_list.mpr hP
        exact P.min_a (l'.head h₀) this
  · rw [<-List.getLast_eq_iff_getLast?_eq_some h₀]
    refine le_antisymm ?_ ?_
    · -- tail ≤ b. This follows from the maximality of b ∈ P.
      have h : l'.getLast h₀ ∈ l' := List.getLast_mem h₀
      rw [List.mem_orderedInsert] at h
      rcases h with hx | hP
      · rw [hx]
        exact h.Icc'.2
      · have : l'.getLast h₀ ∈ P := P.mem_iff_mem_list.mpr hP
        exact P.max_b (l'.getLast h₀) this
    · -- b ≤ tail. This follows from the current list being sorted.
      have hb' : b ∈ l' := by
        rw [List.mem_orderedInsert]
        exact Or.inr P.mem_bᵢ
      exact sorted'.sortedLE.sorted_last_max h₀ b hb' -- ∎

noncomputable def ι' (x : ℝ) (P : Partition I) : Partition I
  := by --
  if h : P.IsInsertable x then exact ι h else exact P -- ∎

noncomputable instance : Insert ℝ (Partition I) where insert x P := ι' x P

variable (P : Partition I) (hxP : P.IsInsertable x)

lemma insert_eq : insert x P = ι' x P := rfl

theorem insert_eq_of_mem (hxP : x ∈ P)
  : insert x P = P
  := by --
  change ι' x P = P
  dsimp only [ι']
  rw [dif_neg (IsInsertable.not_of_mem hxP)] -- ∎

include hxP in -- successful insert
theorem insert_eq₂ : insert x P = ι hxP
  := by --
  change ι' x P = ι hxP
  dsimp only [ι']
  rw [dif_pos hxP] -- ∎

include hxP in -- successful insert
theorem insert_list_eq : (insert x P).l = P.l.orderedInsert (· ≤ ·) x
  := by --
  change (ι' x P).l = P.l.orderedInsert (· ≤ ·) x
  dsimp only [ι', ι]
  rw [dif_pos hxP] -- ∎

include hxP in -- successful insert
theorem insert_n : (insert x P).n = P.n + 1
  := by --
  change (insert x P).l.length = P.l.length + 1
  rw [P.insert_list_eq hxP, List.orderedInsert_length] -- ∎

include hxP in -- successful insert
lemma insert_idx_Ioo {k : ℕ} : insert x P k = x → k ∈ Ioo 0 P.n
  := by --
  intro h
  refine ⟨?_, ?_⟩
  · by_contra h₀
    rw [Nat.eq_zero_of_not_pos h₀] at h
    refine False.elim (hxP.notMem' ?_)
    rw [<-h, <-(insert x P).a_eq]
    exact P.mem_a
  · by_contra! h'
    have hbx : b ≠ x := by
      by_contra! hbx
      refine hxP.notMem' ?_
      subst hbx
      exact P.mem_b
    rcases h'.eq_or_lt with heq | hlt
    · refine hbx ?_
      replace heq : k = (insert x P).n - 1 := by
        rw [P.insert_n hxP]
        exact heq.symm
      rw [heq] at h
      rw [<-h, Partition.fn_eq, dif_pos (insert x P).len_sub_one_lt]
      exact (insert x P).b_eqᵢ
    · refine hbx ?_
      rw [Partition.fn_eq] at h
      have : ¬k < (insert x P).n := by
        rw [not_lt, P.insert_n hxP]
        exact hlt
      rw [dif_neg this] at h
      exact h -- ∎

lemma le_insert : P ≤ insert x P
  := by --
  if h : P.IsInsertable x then
    intro t ht
    rw [mem_iff_mem_list] at ht ⊢
    rw [P.insert_list_eq h, List.mem_orderedInsert]
    refine Or.inr ht
  else
    change P ≤ ι' x P
    dsimp only [ι']
    rw [dif_neg h] -- ∎

lemma mem_insert_self_iff : x ∈ insert x P ↔ x ∈ Icc a b
  := by --
  constructor
  · intro h
    exact ⟨(insert x P).min_a x h, (insert x P).max_b x h⟩
  · intro h
    if hxP : x ∈ P then exact P.le_insert hxP else
    replace h : P.IsInsertable x := ⟨hxP, h⟩
    rw [mem_iff_mem_list, P.insert_list_eq h]
    exact List.mem_orderedInsert_self (· ≤ ·) -- ∎

lemma mem_insert_iff {t : ℝ} : t ∈ insert x P ↔ t = x ∧ t ∈ Icc a b ∨ t ∈ P
  := by --
  constructor
  · intro (htP' : t ∈ ι' x P)
    dsimp only [ι', ι] at htP'
    refine or_iff_not_imp_right.mpr ?_
    intro htP
    if h : P.IsInsertable x then
      rw [dif_pos h] at htP'
      rw [mem_iff_mem_list] at htP'
      rw [List.mem_orderedInsert] at htP'
      rcases htP' with htx | hl
      · refine ⟨htx, ?_⟩
        subst htx
        exact h.2
      · refine False.elim ?_
        rw [<-mem_iff_mem_list] at hl
        exact htP hl
    else
    rw [dif_neg h] at htP'
    exact False.elim (htP htP')
  · intro h
    rcases h with ⟨htx, htI⟩ | htP
    · subst htx
      exact (mem_insert_self_iff P).mpr htI
    · exact P.le_insert htP -- ∎

theorem insert_mono (x : ℝ) : Monotone (fun P : Partition I ↦ insert x P)
  := by --
  intro P₁ P₂ hleP t (h₁ : t ∈ insert x P₁)
  simp only
  rw [mem_insert_iff] at h₁ ⊢
  rcases h₁ with ⟨htx, htI⟩ | htP₁
  · subst htx
    exact Or.inl ⟨rfl, htI⟩
  · exact Or.inr (hleP htP₁) -- ∎

section Get
variable {i k : ℕ}

include hxP in -- successful insert
private lemma orderedInsert_le₀ :
  P i ≤ x → P i = (insert x P) i
  := by --
  intro hx
  if hi : P.n ≤ i then
    refine False.elim (hxP.notMem' ?_)
    have hxb : x = b := by
      rw [P.fn_eq, dif_neg hi.not_gt] at hx
      exact le_antisymm hxP.Icc'.2 hx
    subst hxb
    exact P.mem_b
  else
  replace hi : i < P.n := Nat.lt_of_not_le hi
  simp only [Partition.fn_eq]
  rw [dif_pos hi]
  have hi' : i < (insert x P).n := hi.trans_le (len_mono P.le_insert)
  rw [dif_pos hi']
  rw [P.fn_eq, dif_pos hi] at hx
  change i < (insert x P).l.length at hi'
  rw [P.insert_list_eq hxP] at hi'
  have : x ∉ P.l := P.mem_iff_mem_list.not.mp hxP.notMem'
  have : P[i] = (List.orderedInsert (· ≤ ·) x P.l)[i] := List.orderedInsert_leᵢ P.sorted' this hi hx
  rw [this]
  simp only [<-P.insert_list_eq hxP]
  exact rfl -- ∎

include hxP in -- successful insert
private lemma orderedInsert_ge₀ :
  x ≤ P i → P i = (insert x P) (i + 1)
  := by --
  intro hx
  if hi : P.n ≤ i then
    simp only [Partition.fn_eq]
    rw [dif_neg hi.not_gt]
    have : ¬i + 1 < (insert x P).n := by
      rw [P.insert_n hxP]
      exact (Nat.succ_le_succ hi).not_gt
    rw [dif_neg this]
  else
  replace hi : i < P.n := Nat.lt_of_not_le hi
  simp only [Partition.fn_eq]
  rw [dif_pos hi]
  have hi' : i + 1 < (insert x P).n := by
    rw [P.insert_n hxP]
    exact Nat.succ_lt_succ hi
  rw [dif_pos hi']
  rw [P.fn_eq, dif_pos hi] at hx
  change i + 1 < (insert x P).l.length at hi'
  rw [P.insert_list_eq hxP] at hi'
  have : x ∉ P.l := P.mem_iff_mem_list.not.mp hxP.notMem'
  have : P[i] = (P.l.orderedInsert (· ≤ ·) x)[i + 1] := List.orderedInsert_geᵢ P.sorted' this hi hx
  rw [this]
  simp only [<-P.insert_list_eq hxP]
  exact rfl -- ∎

include hxP in -- successful insert
lemma orderedInsert_lt (hk : k < P.n + 1) (hik : i < k) :
  (insert x P) k = x → P i ≤ x
  := by --
  have hxPᵢ : x ∉ P.l := P.mem_iff_mem_list.not.mp hxP.notMem'
  have h := List.orderedInsert_lt P.sorted' hxPᵢ hik
  specialize h hk
  have hk₁ : k < (insert x P).n := by rw [P.insert_n hxP]; exact hk
  change k < (insert x P).l.length at hk₁
  rw [P.insert_list_eq hxP] at hk₁
  have : (List.orderedInsert (· ≤ ·) x P.l)[k] = insert x P k := by
    rw [P.insert_eq₂ hxP, Partition.fn_eq, dif_pos]
    exact rfl
  rw [this] at h
  intro heq
  specialize h heq
  refine le_trans ?_ h
  exact (ieq.l_cond P (hik.trans_le (Nat.le_of_lt_succ hk))).le -- ∎

include hxP in -- successful insert
lemma orderedInsert_ge (hi : i < P.n) (hk : k < P.n + 1) (hik : i ≥ k)
  : (insert x P) k = x → x ≤ P i
  := by --
  have hxPᵢ : x ∉ P.l := P.mem_iff_mem_list.not.mp hxP.notMem'
  have h := List.orderedInsert_ge P.sorted' hxPᵢ hik hi hk
  have hk₁ : k < (insert x P).n := by rw [P.insert_n hxP]; exact hk
  change k < (insert x P).l.length at hk₁
  rw [P.insert_list_eq hxP] at hk₁
  have : (List.orderedInsert (· ≤ ·) x P.l)[k] = insert x P k := by
    rw [P.insert_eq₂ hxP, Partition.fn_eq, dif_pos]
    exact rfl
  rw [this] at h
  intro heq
  specialize h heq
  refine le_trans h ?_
  exact (ieq.l_cond P hi).symm.le -- ∎

include hxP in -- successful insert
theorem insert_get {k : ℕ} (hk : insert x P k = x) : ∀ i,
  if i < k then
    P i = insert x P i
  else
    P i = insert x P (i + 1)
  := by --
  intro i
  let P' := insert x P
  have hkP'n : k < P'.n := by
    -- If `k < P'.n`, then `x = b`, making the insert invalid.
    by_contra hlt
    refine hxP.notMem' ?_
    rw [<-hk, P'.fn_eq, dif_neg hlt]
    exact P.mem_b
  have hkPn : k < P.n + 1 := by
    rw [<-P.insert_n hxP]
    exact hkP'n
  if hiPn : P.n ≤ i then
    -- If `P.n ≤ i`, we have an out-of-bounds case.
    -- Then the result becomes `b = b`, which is trivial.
    have : ¬i < k := by
      refine (le_trans ?_ hiPn).not_gt
      rw [P.insert_n hxP] at hkP'n
      exact (Nat.le_of_lt_succ hkP'n)
    simp only [reduceIte, this, Partition.fn_eq]
    have : ¬i + 1 < P'.n := by
      rw [P.insert_n hxP]
      exact (Nat.succ_le_succ hiPn).not_gt
    rw [dif_neg hiPn.not_gt, dif_neg this]
  else
  replace hiPn : i < P.n := Nat.lt_of_not_le hiPn
  if hik : i < k then
    simp only [reduceIte, hik]
    refine P.orderedInsert_le₀ hxP ?_
    exact P.orderedInsert_lt hxP hkPn hik hk
  else
    simp only [reduceIte, hik]
    refine P.orderedInsert_ge₀ hxP ?_
    have hki : k ≤ i := Nat.le_of_not_lt hik
    exact P.orderedInsert_ge hxP hiPn hkPn hki hk -- ∎

end Get
end Partition
end Rudin
