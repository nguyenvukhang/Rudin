import Mathlib.Data.Finset.Sort
import Mathlib.Data.Real.Basic

variable {a b : ℝ}

namespace Rudin

@[ext]
structure Partition (I : a < b) where
  /-- The list of boundary points of the partition. -/
  l : List ℝ
  head' : l.head? = some a
  tail' : l.getLast? = some b
  sorted' : l.SortedLT

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

private lemma ℓₙ {P : Partition I} : P.n - 1 < P.n
  := by --
  exact Nat.sub_one_lt (List.eq_nil_iff_length_eq_zero.not.mp ℓ₀) -- ∎

/-- The i-th boundary point, but checked.
`a = x₀ < x₁ < ... < xₙ₋₁ = b` -/
instance {I : a < b} : GetElem (Partition I) ℕ ℝ fun P i ↦ i < P.n where
  getElem P i hi := P.l.get ⟨i, hi⟩

private theorem ℓb (P : Partition I) : P[P.n - 1]'(ℓₙ) = b
  := by --
  refine (List.getElem_eq_iff ℓₙ).mpr ?_
  rw [<-P.tail']
  exact List.getLast?_eq_getElem?.symm -- ∎

/-- The recommended way of getting the value of the head, instead of
`head'` in the definitions. -/
def head : ℝ := P.l.head ℓ₀

/-- The recommended way of getting the value of the tail, instead of
`tail'` in the definitions. -/
def tail : ℝ := P.l.getLast ℓ₀

lemma sorted_le (P : Partition I) : P.l.SortedLE := P.sorted'.sortedLE

/-- The partition contains no duplicate boundary points. -/
lemma nodup : P.l.Nodup
  := by --
  rw [List.nodup_iff_pairwise_ne, List.pairwise_iff_get]
  intro i j hij
  exact (P.sorted' hij).ne -- ∎

lemma eq_Finset_sort (P : Partition I) : P.l.toFinset.sort (· ≤ ·) = P.l
  := by -- ∎
  exact (List.toFinset_sort (· ≤ ·) P.nodup).mpr P.sorted_le.pairwise -- ∎

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

/-- The i-th boundary point, but unchecked.
`a = x₀ < x₁ < ... < xₙ₋₁ = b` -/
instance {I : a < b} : FunLike (Partition I) ℕ ℝ
  := by --
  exact {
    coe P i := if _ : i < P.n then P[i] else b
    coe_injective' := by
      intro P₁ P₂ h
      rw [funext_iff] at h
      have ℓ₀ {P : Partition I} : 0 < P.n := List.length_pos_iff.mpr ℓ₀
      have ℓ₁ {P : Partition I} : 1 ≤ P.n := Nat.one_le_iff_ne_zero.mpr ℓ₀.ne'
      if hc₁ : P₁.n < P₂.n then
        specialize h (P₁.n - 1)
        simp only [tsub_lt_self_iff, zero_lt_one, and_true] at h
        rewrite [dif_pos ℓ₀, dif_pos (Nat.sub_lt_of_lt hc₁)] at h
        conv at h => lhs; rw [ℓb P₁, <-ℓb P₂]
        have hlt : P₁.n - 1 < P₂.n - 1 := Nat.sub_lt_sub_right ℓ₁ hc₁
        exact False.elim (h.not_gt (P₂.sorted' hlt))
      else if hc₂ : P₂.n < P₁.n then
        specialize h (P₂.n - 1)
        simp only [tsub_lt_self_iff, zero_lt_one, and_true] at h
        rewrite [dif_pos ℓ₀, dif_pos (Nat.sub_lt_of_lt hc₂)] at h
        conv at h => rhs; rw [ℓb P₂, <-ℓb P₁]
        have hlt : P₂.n - 1 < P₁.n - 1 := Nat.sub_lt_sub_right ℓ₁ hc₂
        exact False.elim (h.not_lt (P₁.sorted' hlt))
      else
      have heq_n : P₁.n = P₂.n := le_antisymm (Nat.le_of_not_lt hc₂) (Nat.le_of_not_lt hc₁)
      rw [Partition.ext_iff]
      refine List.ext_getElem heq_n ?_
      intro i hi₁ hi₂
      specialize h i
      change (if x : i < P₁.n then P₁[i] else b) = if x : i < P₂.n then P₂[i] else b at h
      have : i < P₁.n := hi₁; rw [dif_pos this] at h
      have : i < P₂.n := hi₂; rw [dif_pos this] at h
      exact h
  } -- ∎

lemma fn_eq (i : ℕ) : P i = if _ : i < P.n then P[i] else b := rfl

-- Either both indexes are legit, or both are equal to b.
lemma fn_eq₂ (i : ℕ) :
  if h : i < P.n then P i = P[i] ∧ P (i - 1) = P[i - 1]
  else                P i = b    ∧ P (i - 1) = b
  := by --
  rw [dite_prop_iff_and]
  refine ⟨?_, ?_⟩
  · intro h
    refine ⟨?_, ?_⟩
    · exact dif_pos h
    · exact dif_pos (Nat.sub_lt_of_lt h)
  · intro h
    refine ⟨?_, ?_⟩
    · exact dif_neg h
    · rcases (Nat.le_of_not_lt h).lt_or_eq with hlt | heq
      · exact dif_neg (Nat.le_sub_one_of_lt hlt).not_gt
      · subst heq
        rw [P.fn_eq, dif_pos ℓₙ]
        refine (List.getElem_eq_iff ℓₙ).mpr ?_
        rw [<-P.tail']
        exact List.getLast?_eq_getElem?.symm -- ∎

/-- The i-th interval. `[xᵢ₋₁, xᵢ]`. Valid ones go from `1` to `n - 1`. -/
def interval (i : ℕ) : Set ℝ := Set.Icc (P (i - 1)) (P i)

def Δ (α : ℝ → ℝ) (i : ℕ) : ℝ := α (P i) - α (P (i - 1))

section OfFunction
variable {n : ℕ} {f : ℕ → ℝ} (I : a < b)
  (hf : StrictMonoOn f (Finset.range n))
  (ha : f 0 = a) (hb : f (n - 1) = b)

/-- Create a partition from a function. -/
def ofFn : Partition I
  := by --
  have hn₂ : 2 ≤ n := by
    by_contra! hn
    have : n - 1 ≤ 0 := Nat.sub_le_of_le_add (Nat.le_of_lt_succ hn)
    have : n - 1 = 0 := Nat.eq_zero_of_le_zero this
    rw [this] at hb
    rw [ha] at hb
    exact hb.not_lt I
  let l := List.ofFn (n := n) (f ·)
  have hl_length : l.length = n := List.length_ofFn
  have hl_length_le : 2 ≤ l.length := by rw [List.length_ofFn]; exact hn₂
  have hl₀ : l ≠ [] := List.ne_nil_of_length_pos (zero_lt_two.trans_le hl_length_le)
  have hl₀ : l ≠ [] := by
    refine List.ne_nil_of_length_pos ?_
    rw [hl_length]
    exact zero_lt_two.trans_le hn₂
  have haᵢ : l[0] = a := by
    dsimp only [l]
    rw [List.getElem_ofFn]
    exact ha
  have hbᵢ : l[l.length - 1] = b := by
    dsimp only [l]
    rw [List.getElem_ofFn]
    simp only [List.length_ofFn]
    exact hb
  refine {
    l
    head' := by
      rw [<-haᵢ]
      refine (List.head_eq_iff_head?_eq_some hl₀).mp ?_
      exact List.head_eq_getElem hl₀
    tail' := by
      rw [<-hbᵢ]
      refine (List.getLast_eq_iff_getLast?_eq_some hl₀).mp ?_
      exact List.getLast_eq_getElem hl₀
    sorted' := by
      intro i j hij
      dsimp only [l]
      simp only [List.get_eq_getElem, List.getElem_ofFn]
      refine hf ?_ ?_ hij
      · refine Finset.mem_coe.mpr (Finset.mem_range.mpr ?_)
        exact lt_of_lt_of_eq i.is_lt hl_length
      · refine Finset.mem_coe.mpr (Finset.mem_range.mpr ?_)
        exact lt_of_lt_of_eq j.is_lt hl_length
  } -- ∎

example : (ofFn I hf ha hb).l = List.ofFn (n := n) (f ·) := rfl
theorem ofFn_eq_l : (ofFn I hf ha hb).l = List.ofFn (n := n) (f ·) := rfl
theorem ofFn_eq_n : (ofFn I hf ha hb).n = n := List.length_ofFn
theorem ofFn_eq_f {i : ℕ} (hi : i < n) : (ofFn I hf ha hb) i = f i := by
  let P := ofFn I hf ha hb
  change (if _ : i < P.n then P[i] else b) = f i
  have : P.n = n := List.length_ofFn
  have : i < P.n := by rw [this]; exact hi
  rw [dif_pos this]
  exact List.getElem_ofFn this

end OfFunction

end Partition

end Rudin
