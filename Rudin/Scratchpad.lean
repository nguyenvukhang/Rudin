import Rudin.Defs.Partition

open Set

namespace Rudin

variable {a b : ℝ} {I : a < b} {P P' P₁ P₂ : Partition I}

private lemma ℓ₀ : P.l ≠ []
  := by --
  have h := P.head'
  by_contra h'
  rw [h', List.head?_nil] at h
  contradiction -- ∎

private lemma ℓₙ : P.n - 1 < P.n
  := by --
  exact Nat.sub_one_lt (List.eq_nil_iff_length_eq_zero.not.mp ℓ₀) -- ∎

private theorem ℓb (P : Partition I) : P[P.n - 1]'(ℓₙ) = b
  := by --
  refine (List.getElem_eq_iff ℓₙ).mpr ?_
  rw [<-P.tail', List.getLast?_eq_some_getLast ℓ₀, List.getElem?_eq_getElem ℓₙ]
  exact congrArg some (List.getLast_eq_getElem ℓ₀).symm -- ∎

/-- The i-th boundary point, but unchecked.
`a = x₀ < x₁ < ... < xₙ₋₁ = b` -/
example {I : a < b} : FunLike (Partition I) ℕ ℝ where
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
      exact False.elim (h.not_gt (P₂.sorted'.get_strictMono hlt))
    else if hc₂ : P₂.n < P₁.n then
      specialize h (P₂.n - 1)
      simp only [tsub_lt_self_iff, zero_lt_one, and_true] at h
      rewrite [dif_pos ℓ₀, dif_pos (Nat.sub_lt_of_lt hc₂)] at h
      conv at h => rhs; rw [ℓb P₂, <-ℓb P₁]
      have hlt : P₂.n - 1 < P₁.n - 1 := Nat.sub_lt_sub_right ℓ₁ hc₂
      exact False.elim (h.not_lt (P₁.sorted'.get_strictMono hlt))
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

end Rudin
