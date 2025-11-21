import Rudin.Alpha.Basic
import Rudin.Partition.Extend
import Rudin.Partition.Union

open Set

namespace Rudin

variable {a b : ℝ} {I : a < b} (P : Partition I) {f α : ℝ → ℝ}
  (hf : BddOn f (Icc a b))
  (hα : MonotoneOn α (Icc a b))

private lemma sum₀ {a b : ℕ} (ha : 0 < a) {f : ℕ → ℝ} :
  ∑ i ∈ Finset.Ico a b, f i = ∑ i ∈ Finset.Ico (a - 1) (b - 1), f (i + 1)
  := by --
  refine Finset.sum_bij ?_ ?_ ?_ ?_ ?_
  · intro n hn
    exact n - 1
  · intro n hn
    rw [Finset.mem_Ico] at hn ⊢
    obtain ⟨han, hnb⟩ := hn
    refine ⟨?_, ?_⟩
    · exact Nat.sub_le_sub_right han 1
    · refine Nat.sub_lt_sub_right ?_ hnb
      exact le_trans ha han
  · intro x hx y hy heq
    rw [Finset.mem_Ico] at hx hy
    have hx₁ : 1 ≤ x := le_trans ha hx.1
    have hy₁ : 1 ≤ y := le_trans ha hy.1
    exact Nat.sub_one_cancel hx₁ hy₁ heq
  · intro y hy
    refine ⟨y + 1, ?_, rfl⟩
    rw [Finset.mem_Ico] at hy ⊢
    obtain ⟨hay, hyb⟩ := hy
    refine ⟨?_, ?_⟩
    · exact Nat.le_add_of_sub_le hay
    · exact Nat.add_lt_of_lt_sub hyb
  · intro x hx
    rw [Finset.mem_Ico] at hx
    have hx₁ : 1 ≤ x := le_trans ha hx.1
    rw [Nat.sub_add_cancel hx₁] -- ∎

include hf hα in
private lemma L_mono₁ (x : ℝ)
  : L P f α ≤ L (insert x P) f α
  := by --
  if hxP : ¬P.IsInsertable x then
    simp only [P.insert_eq]
    dsimp only [L, Partition.ι']
    simp only [hxP, ↓reduceDIte]
    exact le_rfl
  else
  let P' := insert x P
  rw [not_not] at hxP
  dsimp only [L]
  simp only [P.insert_n hxP]
  change ∑ i ∈ Finset.range P.n, m P f i * P.Δ α i
       ≤ ∑ i ∈ Finset.range (P.n + 1), m P' f i * P'.Δ α i

  -- k is the index of x in P'
  obtain ⟨k, hk : P' k = x⟩ := P'.mem_iff_x.mp (P.mem_insert_self_iff.mpr hxP.Icc')
  obtain ⟨hk₀, hk₁⟩ := P.insert_idx_Ioo hxP hk

  have hk₂ : k < P.n + 1
    := by --
    exact Nat.lt_add_right 1 hk₁ -- ∎
  have hk₃ : k < P'.n
    := by --
    rw [P.insert_n hxP]
    exact hk₂ -- ∎

  -- Split the sums
  rw [<-Finset.sum_range_add_sum_Ico _ (Nat.le_of_lt_succ hk₂)]
  rw [<-Finset.sum_range_add_sum_Ico _ (hk₂.le)]
  have hk₄ : k ≤ k + 2 := Nat.le_add_right k 2
  have hk₅ : k + 2 ≤ P.n + 1
    := by --
    refine Nat.le_add_of_sub_le ?_
    rw [Nat.add_one_sub_one]
    exact hk₁ -- ∎
  rw [<-Finset.sum_Ico_consecutive _ hk₄ hk₅]
  rw [Finset.sum_eq_sum_Ico_succ_bot hk₁]

  have φ (i : ℕ) : if i < k then P i = P' i else P i = P' (i + 1) := P.insert_get hxP hk i

  refine add_le_add ?_ (add_le_add ?_ ?_)
  rotate_right
  · simp only [sum₀ (Nat.zero_lt_succ (k + 1)), Nat.add_one_sub_one, add_tsub_cancel_right]
    refine Finset.sum_le_sum ?_
    intro i hi
    rw [Finset.mem_Ico] at hi
    obtain ⟨hki : k < i, _⟩ := hi
    have hi₀ : 0 < i := Nat.zero_lt_of_lt hki
    have φ₀ := φ i
    have φ₁ := φ (i - 1)
    simp only [reduceIte, hki.not_gt] at φ₀
    simp only [reduceIte, (Nat.le_sub_one_of_lt hki).not_gt] at φ₁
    rw [Nat.sub_add_cancel hi₀] at φ₁
    dsimp only [Partition.Δ]
    rw [add_tsub_cancel_right, <-φ₀, <-φ₁]
    refine mul_le_mul_of_nonneg_right ?_ (α_nonneg hα i)
    dsimp only [m, Partition.interval]
    rw [add_tsub_cancel_right, <-φ₀, <-φ₁]
  · refine Finset.sum_le_sum ?_
    intro i hik
    rw [Finset.mem_range] at hik
    have φ₀ := φ i
    have φ₁ := φ (i - 1)
    simp only [reduceIte, hik] at φ₀
    simp only [reduceIte, Nat.sub_lt_of_lt hik] at φ₁
    simp only [Partition.Δ, <-φ₀, <-φ₁]
    refine mul_le_mul_of_nonneg_right ?_ (α_nonneg hα i)
    dsimp only [m, Partition.interval]
    rw [<-φ₀, <-φ₁]
  · have φ₀ := φ k
    have φ₁ := φ (k - 1)
    simp only [reduceIte, Nat.lt_irrefl k] at φ₀
    simp only [reduceIte, Nat.sub_one_lt_of_lt hk₀] at φ₁

    have : k + 1 < k + 2 := (Nat.lt_add_one (k + 1))
    rw [Finset.sum_eq_sum_Ico_succ_bot (Nat.lt_add_of_pos_right zero_lt_two)]
    rw [Finset.sum_eq_sum_Ico_succ_bot this]
    rw [Finset.Ico_eq_empty_of_le le_rfl, Finset.sum_empty, add_zero]
    dsimp only [Partition.Δ]
    rw [add_tsub_cancel_right]
    rw [<-sub_add_sub_cancel (α (P k)) (α (P' k)) (α (P (k - 1))), mul_add, add_comm]
    have hIcc : Icc (P' (k - 1)) (P' k) ∪ Icc (P' k) (P' (k + 1))
      = Icc (P' (k - 1)) (P' (k + 1)) := by
      refine Icc_union_Icc_eq_Icc ?_ ?_
      · exact P'.mono (Nat.sub_le k 1)
      · exact P'.mono (Nat.le_succ k)
    have hf_bdd : BddOn f (Icc (P' (k - 1)) (P' (k + 1))) := by
      rw [<-hIcc]
      refine BddOn.union ?_ ?_
      · exact P'.interval_bdd_on hf k
      · exact P'.interval_bdd_on hf (k + 1)
    refine add_le_add ?_ ?_
    · rw [φ₁]
      refine mul_le_mul_of_nonneg_right ?_ (α_nonneg hα _)
      dsimp only [m, Partition.interval]
      simp only [φ₀, φ₁]
      have h₀ := (P'.interval_nonempty k).image f
      have h₁ : f '' Icc (P' (k - 1)) (P' k) ≤ f '' Icc (P' (k - 1)) (P' (k + 1)) := by
        refine Set.image_mono ?_
        refine Set.Icc_subset_Icc le_rfl ?_
        exact P'.mono (Nat.le_succ k)
      exact sInf.anti h₀ hf_bdd.below' h₁
    · rw [φ₀]
      refine mul_le_mul_of_nonneg_right ?_ (α_nonneg hα _)
      dsimp only [m, Partition.interval]
      simp only [φ₀, φ₁]
      rw [add_tsub_cancel_right]
      have h₀ := (P'.interval_nonempty (k + 1)).image f
      have h₁ : f '' Icc (P' k) (P' (k + 1)) ≤ f '' Icc (P' (k - 1)) (P' (k + 1)) := by
        refine Set.image_mono ?_
        refine Set.Icc_subset_Icc ?_ le_rfl
        exact P'.mono (Nat.sub_le k 1)
      exact sInf.anti h₀ hf_bdd.below' h₁ -- ∎

/-- If P' is a refinement of P, then the lower sum obtained from P' will be
greater or equal to that of P. -/
theorem L_mono
  (hf : BddOn f (Icc a b))
  (hα : MonotoneOn α (Icc a b))
  : Monotone fun P : Partition I ↦ L P f α
  := by
  intro P P' hle -- P' is a refinement of P
  change L P f α ≤ L P' f α
  obtain ⟨ℓ, heq⟩ := Partition.extendable_of_le hle
  subst heq
  induction ℓ generalizing P with
  | nil => exact le_rfl
  | cons x xs ih =>
    refine (L_mono₁ P hf hα x).trans ?_
    exact ih <| (insert x P).le_extend xs

include hf hα in
private lemma U_anti₁ (x : ℝ)
  : U (insert x P) f α ≤ U P f α
  := by --
  if hxP : ¬P.IsInsertable x then
    simp only [P.insert_eq]
    dsimp only [L, Partition.ι']
    simp only [hxP, ↓reduceDIte]
    exact le_rfl
  else
  let P' := insert x P
  rw [not_not] at hxP
  dsimp only [U]
  simp only [P.insert_n hxP]
  change ∑ i ∈ Finset.range (P.n + 1), M P' f i * P'.Δ α i
       ≤ ∑ i ∈ Finset.range P.n, M P f i * P.Δ α i

  -- k is the index of x in P'
  obtain ⟨k, hk : P' k = x⟩ := P'.mem_iff_x.mp (P.mem_insert_self_iff.mpr hxP.Icc')
  obtain ⟨hk₀, hk₁⟩ := P.insert_idx_Ioo hxP hk

  have hk₂ : k < P.n + 1
    := by --
    exact Nat.lt_add_right 1 hk₁ -- ∎
  have hk₃ : k < P'.n
    := by --
    rw [P.insert_n hxP]
    exact hk₂ -- ∎

  -- Split the sums
  rw [<-Finset.sum_range_add_sum_Ico _ (Nat.le_of_lt_succ hk₂)]
  rw [<-Finset.sum_range_add_sum_Ico _ (hk₂.le)]
  have hk₄ : k ≤ k + 2 := Nat.le_add_right k 2
  have hk₅ : k + 2 ≤ P.n + 1
    := by --
    refine Nat.le_add_of_sub_le ?_
    rw [Nat.add_one_sub_one]
    exact hk₁ -- ∎
  rw [<-Finset.sum_Ico_consecutive _ hk₄ hk₅]
  rw [Finset.sum_eq_sum_Ico_succ_bot hk₁]

  have φ (i : ℕ) : if i < k then P i = P' i else P i = P' (i + 1) := P.insert_get hxP hk i

  refine add_le_add ?_ (add_le_add ?_ ?_)
  rotate_right
  · simp only [sum₀ (Nat.zero_lt_succ (k + 1)), Nat.add_one_sub_one, add_tsub_cancel_right]
    refine Finset.sum_le_sum ?_
    intro i hi
    rw [Finset.mem_Ico] at hi
    obtain ⟨hki : k < i, _⟩ := hi
    have hi₀ : 0 < i := Nat.zero_lt_of_lt hki
    have φ₀ := φ i
    have φ₁ := φ (i - 1)
    simp only [reduceIte, hki.not_gt] at φ₀
    simp only [reduceIte, (Nat.le_sub_one_of_lt hki).not_gt] at φ₁
    rw [Nat.sub_add_cancel hi₀] at φ₁
    dsimp only [Partition.Δ]
    rw [add_tsub_cancel_right, <-φ₀, <-φ₁]
    refine mul_le_mul_of_nonneg_right ?_ (α_nonneg hα i)
    dsimp only [M, Partition.interval]
    rw [add_tsub_cancel_right]
    rw [<-φ₀, <-φ₁]
  · refine Finset.sum_le_sum ?_
    intro i hik
    rw [Finset.mem_range] at hik
    have φ₀ := φ i
    have φ₁ := φ (i - 1)
    simp only [reduceIte, hik] at φ₀
    simp only [reduceIte, Nat.sub_lt_of_lt hik] at φ₁
    simp only [Partition.Δ, <-φ₀, <-φ₁]
    refine mul_le_mul_of_nonneg_right ?_ (α_nonneg hα i)
    dsimp only [M, Partition.interval]
    rw [<-φ₀, <-φ₁]
  · have φ₀ := φ k
    have φ₁ := φ (k - 1)
    simp only [reduceIte, Nat.lt_irrefl k] at φ₀
    simp only [reduceIte, Nat.sub_one_lt_of_lt hk₀] at φ₁

    have : k + 1 < k + 2 := (Nat.lt_add_one (k + 1))
    rw [Finset.sum_eq_sum_Ico_succ_bot (Nat.lt_add_of_pos_right zero_lt_two)]
    rw [Finset.sum_eq_sum_Ico_succ_bot this]
    rw [Finset.Ico_eq_empty_of_le le_rfl, Finset.sum_empty, add_zero]

    dsimp only [Partition.Δ]
    rw [add_tsub_cancel_right]

    rw [<-sub_add_sub_cancel (α (P k)) (α (P' k)) (α (P (k - 1))), mul_add, add_comm]

    have hIcc : Icc (P' (k - 1)) (P' k) ∪ Icc (P' k) (P' (k + 1))
      = Icc (P' (k - 1)) (P' (k + 1)) := by
      refine Icc_union_Icc_eq_Icc ?_ ?_
      · exact P'.mono (Nat.sub_le k 1)
      · exact P'.mono (Nat.le_succ k)
    have hf_bdd : BddOn f (Icc (P' (k - 1)) (P' (k + 1))) := by
      rw [<-hIcc]
      refine BddOn.union ?_ ?_
      · exact P'.interval_bdd_on hf k
      · exact P'.interval_bdd_on hf (k + 1)

    refine add_le_add ?_ ?_
    · rw [φ₀]
      refine mul_le_mul_of_nonneg_right ?_ (α_nonneg hα _)
      dsimp only [M, Partition.interval]
      simp only [φ₀, φ₁]
      rw [add_tsub_cancel_right]
      have h₀ := (P'.interval_nonempty (k + 1)).image f
      have h₁ : f '' Icc (P' k) (P' (k + 1)) ≤ f '' Icc (P' (k - 1)) (P' (k + 1)) := by
        refine Set.image_mono ?_
        refine Set.Icc_subset_Icc ?_ le_rfl
        exact P'.mono (Nat.sub_le k 1)
      exact sSup.mono h₀ hf_bdd.above' h₁
    · rw [φ₁]
      refine mul_le_mul_of_nonneg_right ?_ (α_nonneg hα _)
      dsimp only [M, Partition.interval]
      simp only [φ₀, φ₁]
      have h₀ := (P'.interval_nonempty k).image f
      have h₁ : f '' Icc (P' (k - 1)) (P' k) ≤ f '' Icc (P' (k - 1)) (P' (k + 1)) := by
        refine Set.image_mono ?_
        refine Set.Icc_subset_Icc le_rfl ?_
        exact P'.mono (Nat.le_succ k)
      exact sSup.mono h₀ hf_bdd.above' h₁ -- ∎

/-- If P' is a refinement of P, then the upper sum obtained from P' will be
lesser or equal to that of P. -/
theorem U_anti
  (hf : BddOn f (Icc a b))
  (hα : MonotoneOn α (Icc a b))
  : Antitone fun P : Partition I ↦ U P f α
  := by
  intro P P' hle -- P' is a refinement of P
  change U P' f α ≤ U P f α
  obtain ⟨ℓ, heq⟩ := Partition.extendable_of_le hle
  subst heq
  induction ℓ generalizing P with
  | nil => exact le_rfl
  | cons x xs ih =>
    refine (U_anti₁ P hf hα x).trans' ?_
    exact ih <| (insert x P).le_extend xs

end Rudin
