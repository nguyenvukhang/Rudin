import Mathlib.Data.Set.Lattice
import Mathlib.Order.Interval.Set.LinearOrder

import Rudin.Partition.Endpoints
import Rudin.Partition.Prelude
import Rudin.Partition.OrderBot

namespace Rudin

open Set

variable {a b : ℝ} {I : a < b} {P₁ P₂ : Partition I} {ℓ : List ℝ}

namespace Partition

noncomputable def ι {x : ℝ} {P : Partition I} (hxP : x ∉ P) (hxI : x ∈ Icc a b)
  : Partition I -- x ∉ P ∧ x ∈ Icc a b
  := by --
  let l' := P.l.orderedInsert (· ≤ ·) x
  have sorted' : l'.Sorted (· < ·) := by
    refine P.sorted'.orderedInsert_sorted_lt ?_
    rw [<-P.mem_iff_mem_list]
    exact hxP
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
      exact List.sorted_head_min h₀ sorted'.le_of_lt a ha'
    · -- a ≤ head. This follows from the minimality of a ∈ P.
      have h : l'.head h₀ ∈ l' := List.head_mem h₀
      rw [List.mem_orderedInsert] at h
      rcases h with hx | hP
      · rw [hx]
        exact hxI.1
      · have : l'.head h₀ ∈ P := P.mem_iff_mem_list.mpr hP
        exact P.min_a (l'.head h₀) this
  · rw [<-List.getLast_eq_iff_getLast?_eq_some h₀]
    refine le_antisymm ?_ ?_
    · -- tail ≤ b. This follows from the maximality of b ∈ P.
      have h : l'.getLast h₀ ∈ l' := List.getLast_mem h₀
      rw [List.mem_orderedInsert] at h
      rcases h with hx | hP
      · rw [hx]
        exact hxI.2
      · have : l'.getLast h₀ ∈ P := P.mem_iff_mem_list.mpr hP
        exact P.max_b (l'.getLast h₀) this
    · -- b ≤ tail. This follows from the current list being sorted.
      have hb' : b ∈ l' := by
        rw [List.mem_orderedInsert]
        exact Or.inr P.mem_bᵢ
      exact List.sorted_last_max h₀ sorted'.le_of_lt b hb' -- ∎

noncomputable def ι' (x : ℝ) (P : Partition I)
  : Partition I -- x ∉ P ∧ x ∈ Icc a b
  := by --
  if h : x ∉ P ∧ x ∈ Icc a b then exact ι h.1 h.2 else exact P -- ∎

noncomputable instance : Insert ℝ (Partition I) where insert x P := ι' x P

variable {x : ℝ} (P : Partition I) (hxP : x ∉ P) (hxI : x ∈ Icc a b)

lemma insert_eq : insert x P = ι' x P := rfl

theorem insert_eq_of_mem (hxP : x ∈ P)
  : insert x P = P
  := by --
  change ι' x P = P
  dsimp only [ι']
  have : ¬(x ∉ P ∧ x ∈ Icc a b) := not_and.mpr fun h a ↦ h hxP
  rw [dif_neg this] -- ∎

include hxP hxI in -- successful insert
theorem insert_eq₂ : insert x P = ι hxP hxI
  := by --
  change ι' x P = ι hxP hxI
  dsimp only [ι']
  rw [dif_pos ⟨hxP, hxI⟩] -- ∎

include hxP hxI in -- successful insert
theorem insert_list_eq : (insert x P).l = P.l.orderedInsert (· ≤ ·) x
  := by --
  change (ι' x P).l = P.l.orderedInsert (· ≤ ·) x
  dsimp only [ι', ι]
  rw [dif_pos ⟨hxP, hxI⟩] -- ∎

include hxP hxI in -- successful insert
theorem insert_n : (insert x P).n = P.n + 1
  := by --
  change (insert x P).l.length = P.l.length + 1
  rw [P.insert_list_eq hxP hxI, List.orderedInsert_length] -- ∎

lemma le_insert : P ≤ insert x P
  := by --
  if h : x ∉ P ∧ x ∈ Icc a b then
    intro t ht
    rw [mem_iff_mem_list] at ht ⊢
    rw [P.insert_list_eq h.1 h.2, List.mem_orderedInsert]
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
    rw [mem_iff_mem_list, P.insert_list_eq hxP h]
    exact List.mem_orderedInsert_self (· ≤ ·) -- ∎

lemma mem_insert_iff {t : ℝ} : t ∈ insert x P ↔ t = x ∧ t ∈ Icc a b ∨ t ∈ P
  := by --
  constructor
  · intro (htP' : t ∈ ι' x P)
    dsimp only [ι', ι] at htP'
    refine or_iff_not_imp_right.mpr ?_
    intro htP
    if h : x ∉ P ∧ x ∈ Icc a b then
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

include hxP hxI in -- successful insert
private lemma insert_get' {k : ℕ} (hk : x = insert x P k) :
  ∀ i, P i = insert x P (if i < k then i else i + 1)
  := by --
  let P' := insert x P
  have hPn₁ : P'.n = P.n + 1 := P.insert_n hxP hxI
  intro i

  have hxPᵢ : x ∉ P.l := P.mem_iff_mem_list.not.mp hxP
  have hkP'n : k < P'.n := by
    by_contra!
    have : P' k = b := by rw [P'.fn_eq, dif_neg this.not_gt]
    have : x = b := by rw [<-this]; exact hk
    have : x ∈ P := by rw [this]; exact P.mem_b
    exact hxP this

  if hi : P.n ≤ i then
    have : k < P.n + 1 := Nat.lt_of_lt_of_eq hkP'n hPn₁
    have : k ≤ P.n := Nat.le_of_lt_succ this
    have : k ≤ i := this.trans hi
    have : ¬i < k := this.not_gt
    simp only [reduceIte, this]
    have : P i = b := by
      rw [P.fn_eq]
      have : ¬i < P.n := hi.not_gt
      rw [dif_neg this]
    rw [this]
    rw [(insert x P).fn_eq]
    have : ¬i + 1 < (insert x P).n := by
      rw [Nat.not_lt, hPn₁]
      exact Nat.add_le_add_right hi 1
    rw [dif_neg this]
  else

  replace hiPl : i < P.l.length := Nat.lt_of_not_le hi
  have h₀ := List.orderedInsert_get P.sorted' hxPᵢ hiPl

  haveI : i < (P.l.orderedInsert (· ≤ ·) x).length := by
    rw [List.orderedInsert_length]
    exact Nat.lt_add_right 1 hiPl
  haveI : k < (P.l.orderedInsert (· ≤ ·) x).length := by
    rw [List.orderedInsert_length]
    exact Nat.lt_of_lt_of_eq hkP'n hPn₁


  have h_insert_eq_i : (List.orderedInsert (· ≤ ·) x P.l)[i] = insert x P i := by
    rw [P.insert_eq₂ hxP hxI]
    dsimp only [Partition.ι]
    rw [Partition.fn_eq]
    rw [dif_pos]
    exact rfl

  have h_insert_eq_k : (List.orderedInsert (· ≤ ·) x P.l)[k] = insert x P k := by
    rw [P.insert_eq₂ hxP hxI]
    dsimp only [Partition.ι]
    rw [Partition.fn_eq]
    rw [dif_pos]
    exact rfl


  if hik : i < k then
    simp only [↓reduceIte, hik]
    have h := List.orderedInsert_lt P.sorted' hxPᵢ hik
    have : k < P.l.length + 1 := Nat.lt_of_lt_of_eq hkP'n hPn₁
    specialize h this
    have : P.l[i] ≤ x := by
      refine h ?_
      conv => rhs; rw [hk]
      exact h_insert_eq_k
    simp only [reduceIte, this] at h₀
    rw [h_insert_eq_i] at h₀
    rw [ieq.l_cond P hiPl, h₀]
  else
  simp only [↓reduceIte, hik]
  replace hik : k ≤ i := by exact Nat.le_of_not_lt hik
  have h := List.orderedInsert_ge P.sorted' hxPᵢ hik
  specialize h hiPl (Nat.lt_of_lt_of_eq hkP'n hPn₁)
  have : x ≤ P.l[i] := by
    refine h ?_
    conv => rhs; rw [hk]
    exact h_insert_eq_k
  have : ¬P.l[i] ≤ x := by
    refine not_le_of_gt ?_
    refine this.lt_of_ne ?_
    by_contra h
    have : x ∈ P := by
      rw [h, P.mem_iff_mem_list]
      exact List.getElem_mem hiPl
    exact hxP this
  simp only [reduceIte, this] at h₀
  rw [ieq.l_cond P hiPl, h₀]
  rw [P.insert_eq₂ hxP hxI]
  dsimp only [Partition.ι]
  rw [Partition.fn_eq]
  rw [dif_pos]
  exact rfl -- ∎

include hxP hxI in -- successful insert
theorem insert_get {k : ℕ} (hk : x = insert x P k) : ∀ i,
  if i < k then
    P i = insert x P i
  else
    P i = insert x P (i + 1)
  := by --
  intro i
  have := P.insert_get' hxP hxI hk i
  if h : i < k then
    simp only [reduceIte, h] at this ⊢
    exact this
  else
    simp only [reduceIte, h] at this ⊢
    exact this -- ∎

end Get
end Partition
end Rudin
