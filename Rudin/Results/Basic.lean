import Rudin.Axioms
import Rudin.Prelude
import Rudin.Partition
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Defs

open Set

namespace Rudin

variable {a b : ℝ} {I : a < b} {P P' P₁ P₂ : Partition I} {f α : ℝ → ℝ}
  (hf : BddOn f (Icc a b))
  (hα : MonotoneOn α (Icc a b))

include hα in
theorem α_nonneg (i : Fin P.n) : (0 : ℝ) ≤ α P[i] - α P[↑i - 1]
  := by --
  rw [sub_nonneg]
  refine hα ?_ ?_ ?_
  · exact P.mem_principal _
  · exact P.mem_principal_fin
  · exact P.get_mono (Nat.sub_le i 1) -- ∎

include hf hα in
theorem L_le_U_same_P : L P f α ≤ U P f α
  := by --
  let g (i : Fin P.n) := α P[i] - α P[i.val - 1]
  have (i : Fin P.n) : m P f i * g i ≤ M P f i * g i := by
    refine mul_le_mul_of_nonneg_right ?_ (α_nonneg hα i)
    exact m_le_M P hf i
  exact Finset.sum_le_sum fun i _ ↦ this i -- ∎

include hf hα in
theorem L_le_U : L P₁ f α ≤ U P₂ f α
  := by --
  have h₁ : P₁ ≤ P₁ ⊔ P₂ := le_sup_left
  have h₂ : P₂ ≤ P₁ ⊔ P₂ := le_sup_right
  have hL := L_mono hf hα h₁
  have hU := U_anti hf hα h₂
  exact hL.trans ((L_le_U_same_P hf hα).trans hU) -- ∎

include hf hα in
theorem Lι_le_Uι : Lι I f α ≤ Uι I f α
  := by --
  let P₀ : Partition I := ⊥
  have (P₂ : Partition I) : sSup { L P f α | P : Partition I } ≤ U P₂ f α := by
    refine csSup_le (L_nonempty I f α) ?_
    intro v ⟨P, heq⟩
    subst heq
    exact L_le_U hf hα
  have :  sSup { L P f α | P : Partition I } ≤ sInf { U P f α | P : Partition I } := by
    refine le_csInf (U_nonempty I f α) ?_
    intro v ⟨P, heq⟩
    subst heq
    exact this P
  exact this -- ∎

include hf in
theorem bdd_f_bdd_on_interval (i : ℕ) : BddOn f (P.interval i) := hf.mono (P.interval_subset i)

include hf in
theorem interval_sInf_le_sSup (i : ℕ) : sInf (f '' P.interval i) ≤ sSup (f '' P.interval i)
  := by --
  refine BddOn.sInf_le_sSup ?_
  exact hf.mono (P.interval_subset i) -- ∎

theorem sInf_ab_le_sInf_interval (i : ℕ) : sInf (Icc a b) ≤ sInf (P.interval i)
  := by --
  refine csInf_le_csInf ?_ ?_ (P.interval_subset i)
  · exact bddBelow_Icc
  · exact P.interval_nonempty i -- ∎

include hf in
theorem sInf_ab_le_sInf_interval_f (i : ℕ) :
  sInf (f '' Icc a b) ≤ sInf (f '' P.interval i)
  := by --
  refine csInf_le_csInf ?_ ?_ (image_mono <| P.interval_subset i)
  · exact hf.below'
  · exact (P.interval_nonempty i).image f -- ∎

theorem sSup_interval_le_sSup_ab (i : ℕ) : sSup (P.interval i) ≤ sSup (Icc a b)
  := by --
  refine csSup_le_csSup ?_ ?_ (P.interval_subset i)
  · exact bddAbove_Icc
  · exact P.interval_nonempty i -- ∎

include hf in
theorem sSup_interval_le_sSup_ab_f (i : ℕ) : sSup (f '' P.interval i) ≤ sSup (f '' Icc a b)
  := by --
  refine csSup_le_csSup ?_ ?_ (image_mono <| P.interval_subset i)
  · exact hf.above'
  · exact (P.interval_nonempty i).image f -- ∎

example {n : ℕ} {f : ℕ → ℝ} : ∑ i : Fin n, f i = ∑ i < n, f i := by
  have : Finset.range n = Finset.Iio n := by
    refine Finset.ext ?_
    intro _
    simp only [Finset.mem_range, Finset.mem_Iio]
  rw [Fin.sum_univ_eq_sum_range, this]

theorem α_telescope : ∑ i : Fin P.n, (α P[i] - α P[↑i - 1]) = α b - α a
  := by --
  let n := P.n
  have h₁ (i : Fin n) : P i = P[i] := Partition.ieq.idx_fin P
  have h₂ (i : Fin n) : P (i - 1) = P[↑i - 1] := Partition.ieq.idx_cond P _
  have : ∑ i : Fin n, (α P[i] - α P[↑i - 1]) = ∑ i : Fin n, (α (P i) - α (P (i - 1))) := by
    simp only [h₁, h₂]
  rw [this]
  let φ (i : ℕ) : ℝ := α (P i) - α (P (i - 1))
  change ∑ i : Fin n, φ i = α b - α a
  rw [Fin.sum_univ_eq_sum_range]
  rw [Finset.sum_range_sub₁]
  rw [P.head_eq₂, P.tail_eq₂] -- ∎

include hf hα in
theorem L_bdd_below : BddBelow { L P f α | P : Partition I }
  := by --
  obtain ⟨y, hy⟩ := hf.below'
  use y * (α b - α a)
  intro val ⟨P, heq⟩
  subst heq
  dsimp only [L, m]
  let n := P.n
  let g (i : Fin n) := α P[i] - α P[i.val - 1]

  have : y ≤ sInf (f '' Icc a b) := by
    refine le_csInf ?_ ?_
    · exact (nonempty_Icc.mpr I.le).image f
    · intro z ⟨x, hx, heq⟩
      subst heq
      exact hy ⟨x, hx, rfl⟩

  have : ∑ i : Fin n, y * g i ≤ ∑ i : Fin n, sInf (f '' P.interval ↑i) * g i := by
    refine Finset.sum_le_sum ?_
    intro i _
    refine mul_le_mul_of_nonneg_right ?_ (α_nonneg hα i)
    exact this.trans (sInf_ab_le_sInf_interval_f hf i)
  refine le_trans ?_ this
  rw [<-Finset.mul_sum]
  refine le_of_eq ?_
  rw [mul_eq_mul_left_iff]
  exact Or.inl α_telescope.symm -- ∎

include hf hα in
theorem U_bdd_above : BddAbove { U P f α | P : Partition I }
  := by --
  obtain ⟨y, hy⟩ := hf.above'
  use y * (α b - α a)
  intro val ⟨P, heq⟩
  subst heq
  dsimp only [U, M]
  let n := P.n
  let g (i : Fin n) := α P[i] - α P[i.val - 1]

  have : sSup (f '' Icc a b) ≤ y := by
    refine csSup_le ?_ ?_
    · exact (nonempty_Icc.mpr I.le).image f
    · intro z ⟨x, hx, heq⟩
      subst heq
      exact hy ⟨x, hx, rfl⟩

  have : ∑ i : Fin n, sSup (f '' P.interval ↑i) * g i ≤ ∑ i : Fin n, y * g i := by
    refine Finset.sum_le_sum ?_
    intro i _
    refine mul_le_mul_of_nonneg_right ?_ (α_nonneg hα i)
    refine (sSup_interval_le_sSup_ab_f hf i).trans this
  refine this.trans ?_
  rw [<-Finset.mul_sum]
  refine le_of_eq ?_
  rw [mul_eq_mul_left_iff]
  exact Or.inl α_telescope -- ∎

include hf hα in
theorem L_bdd_above : BddAbove { L P f α | P : Partition I }
  := by --
  obtain ⟨y, hy⟩ := U_bdd_above (I := I) hf hα
  use y
  intro val ⟨P, heq⟩
  subst heq
  exact (L_le_U_same_P hf hα).trans (hy ⟨P, rfl⟩) -- ∎

include hf hα in
theorem U_bdd_below : BddBelow { U P f α | P : Partition I }
  := by --
  obtain ⟨y, hy⟩ := L_bdd_below (I := I) hf hα
  use y
  intro val ⟨P, heq⟩
  subst heq
  exact (hy ⟨P, rfl⟩).trans (L_le_U_same_P hf hα) -- ∎

include hf hα in
theorem Uι_bot (P : Partition I) : Uι I f α ≤ U P f α
  := by --
  exact csInf_le (U_bdd_below hf hα) ⟨P, rfl⟩ -- ∎

include hf hα in
theorem Lι_top (P : Partition I) : L P f α ≤ Lι I f α
  := by --
  exact le_csSup (L_bdd_above hf hα) ⟨P, rfl⟩ -- ∎

include hf hα in
theorem RiemannStieltjesIntegrable.iff : RiemannStieltjesIntegrable I f α ↔
  ∀ ε > 0, ∃ P : Partition I, U P f α - L P f α < ε
  := by --
  constructor
  · intro h ε hε
    have hε₂ : 0 < ε / 2 := half_pos hε
    obtain ⟨P₁, hP₁⟩ : ∃ P₁ : Partition I, Lι I f α - L P₁ f α < ε / 2 := by
      have := sSup.exist_sub_lt_ε (L_nonempty I f α) (L_bdd_above hf hα) (ε / 2) hε₂
      obtain ⟨val, ⟨P, heq⟩, h⟩ := this
      subst heq
      exact ⟨P, h⟩
    obtain ⟨P₂, hP₂⟩ : ∃ P₂ : Partition I, U P₂ f α - Uι I f α < ε / 2 := by
      have := sInf.exist_sub_lt_ε (U_nonempty I f α) (U_bdd_below hf hα) (ε / 2) hε₂
      obtain ⟨val, ⟨P, heq⟩, h⟩ := this
      subst heq
      exact ⟨P, h⟩
    let P := P₁ ⊔ P₂
    refine ⟨P, sub_right_lt_of_lt_add ?_⟩

    have : U P f α ≤ U P₂ f α := U_anti hf hα le_sup_right
    refine this.trans_lt ?_

    have : U P₂ f α < ε / 2 + Uι I f α := lt_add_of_tsub_lt_right hP₂
    refine this.trans ?_

    rw [h]

    have : L P₁ f α ≤ L P f α := L_mono hf hα le_sup_left
    have : ε + L P₁ f α ≤ ε + L P f α := (add_le_add_iff_left ε).mpr this
    refine this.trans_lt' ?_

    conv => rhs; rw [<-add_halves ε]
    rw [add_assoc]
    have : Lι I f α < ε / 2 + L P₁ f α := lt_add_of_tsub_lt_right hP₁
    exact add_lt_add_left this (ε / 2)
  · intro h
    have hU (P : Partition I) : Uι I f α ≤ U P f α := Uι_bot hf hα P
    have hL (P : Partition I) : L P f α ≤ Lι I f α := Lι_top hf hα P
    have h₁ : 0 ≤ Uι I f α - Lι I f α := sub_nonneg_of_le (Lι_le_Uι hf hα)
    have h₂ : ∀ ε > 0, Uι I f α - Lι I f α ≤ ε := by
      intro ε hε
      specialize h ε hε
      obtain ⟨P, hP⟩ := h
      specialize hU P
      specialize hL P
      exact (tsub_le_tsub hU hL).trans hP.le
    have := eq_zero_of_nonneg_le_pos h₁ h₂
    rw [sub_eq_zero] at this
    exact this -- ∎

end Rudin
