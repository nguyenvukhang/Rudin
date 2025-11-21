import Rudin.Partition.SpecialPartitions
import Rudin.Results.Basic
import Rudin.Results.IsTag

open Set

namespace Rudin

variable {a b : ℝ} {I : a < b} {P P' P₁ P₂ : Partition I} {f α : ℝ → ℝ}
  (hf : BddOn f (Icc a b))
  (hα : MonotoneOn α (Icc a b))

set_option linter.dupNamespace false in
include hf hα in
@[deprecated RiemannStieltjesIntegrable.iff (since := "when")]
theorem Theorem._6._6 : RiemannStieltjesIntegrable I f α ↔
  ∀ ε > 0, ∃ P : Partition I, U P f α - L P f α < ε
  := by --
  exact RiemannStieltjesIntegrable.iff hf hα -- ∎

include hf hα in
theorem Theorem._6._7._a (ε : ℝ) :
  U P f α - L P f α < ε → ∀ P' ≥ P, U P' f α - L P' f α < ε
  := by --
  intro h P' (hP : P ≤ P')
  have hU : U P' f α ≤ U P f α := U_anti hf hα hP
  have hL : L P f α ≤ L P' f α := L_mono hf hα hP
  exact (tsub_le_tsub hU hL).trans_lt h -- ∎

include hf hα in
theorem Theorem._6._7._b (ε : ℝ) :
  U P f α - L P f α < ε → ∀ s t, IsTag P s → IsTag P t →
  ∑ i ∈ Finset.range P.n, |f (s i) - f (t i)| * P.Δ α i < ε
  := by --
  intro h s t hs ht
  rw [UL_eq] at h

  have (i : ℕ) : |f (s i) - f (t i)| ≤ M P f i - m P f i := by
    dsimp only [m, M]
    rcases Nat.lt_or_ge i P.n with hlt | hge
    · specialize hs i
      specialize ht i
      have hs' : f (s i) ∈ f '' P.interval i := ⟨s i, hs, rfl⟩
      have ht' : f (t i) ∈ f '' P.interval i := ⟨t i, ht, rfl⟩
      have hbd : BddOn f (P.interval i) := P.interval_bdd_on hf i
      refine abs_sub_le_of_le_of_le ?_ ?_ ?_ ?_
      · refine hbd.csInf_le hs
      · exact hbd.le_csSup hs
      · exact hbd.csInf_le ht
      · exact hbd.le_csSup ht
    · rw [ht.n_le P hge, hs.n_le P hge, sub_self, abs_zero]
      exact sub_nonneg_of_le (m_le_M P hf i)

  have (i : ℕ) : |f (s i) - f (t i)| * (α (P i) - α (P (i - 1)))
    ≤ (M P f i - m P f i) * (α (P i) - α (P (i - 1))) := by
    refine mul_le_mul_of_nonneg_right ?_ (α_nonneg hα i)
    exact this i

  have : ∑ i ∈ Finset.range P.n, |f (s i) - f (t i)| * (α (P i) - α (P (i - 1))) ≤
  ∑ i ∈ Finset.range P.n, (M P f i - m P f i) * (α (P i) - α (P (i - 1))) := by
    exact Finset.sum_le_sum fun i _ ↦ this i
  exact this.trans_lt h -- ∎

include hf hα in
theorem Theorem._6._7._c (hrsi : RiemannStieltjesIntegrable I f α) (ε : ℝ) :
  U P f α - L P f α < ε → ∀ t, IsTag P t →
  |∑ i ∈ Finset.range P.n, f (t i) * P.Δ α i - ∫ I, f d α| < ε
  := by --
  intro h t ht
  have hL : L P f α ≤ ∑ i ∈ Finset.range P.n, f (t i) * P.Δ α i := by
    refine Finset.sum_le_sum ?_
    intro i hi
    refine mul_le_mul_of_nonneg_right ?_ (P.Δ_nonneg hα i)
    exact ht.ge_m hf i
  have hU : ∑ i ∈ Finset.range P.n, f (t i) * P.Δ α i ≤ U P f α := by
    refine Finset.sum_le_sum ?_
    intro i hi
    refine mul_le_mul_of_nonneg_right ?_ (P.Δ_nonneg hα i)
    exact ht.le_M hf i
  have hL' : L P f α ≤ ∫ I, f d α := by rw [hrsi.eq_L]; exact Lι_top hf hα P
  have hU' : ∫ I, f d α ≤ U P f α := Uι_bot hf hα P
  refine h.trans_le' (abs_sub_le_of_le_of_le ?_ ?_ ?_ ?_)
  · exact hL
  · exact hU
  · exact hL'
  · exact hU' -- ∎

include hα in
theorem Theorem._6._8 (hf_cont : ContinuousOn f (Icc a b))
  : RiemannStieltjesIntegrable I f α
  := by --
  have hab : IsCompact (Icc a b) := isCompact_Icc
  have hf_ucont : UniformContinuousOn f (Icc a b) :=
    hab.uniformContinuousOn_of_continuous hf_cont
  have hf : BddOn f (Icc a b) := {
    below' := hab.bddBelow_image hf_cont
    above' := hab.bddAbove_image hf_cont
  }
  rw [RiemannStieltjesIntegrable.iff hf hα]
  intro ε hε
  if hα₀ : α b - α a = 0 then
    have hα₀ : α a = α b := by rw [sub_eq_zero] at hα₀; exact hα₀.symm
    use ⊥
    rw [α_trivial_U hα hα₀, α_trivial_L hα hα₀, sub_self]
    exact hε
  else

  have hα₀ : 0 < α b - α a := (α_sub_nonneg hα I.le).lt_of_ne' hα₀
  have : 0 < ε / (α b - α a) := div_pos hε hα₀
  obtain ⟨η, hη₀, hη : η < ε / (α b - α a)⟩ := exists_between (div_pos hε hα₀)
  have hηε : (α b - α a) * η < ε := by
    if h₀ : α b - α a = 0 then rw [h₀, zero_mul]; exact hε else
    exact (lt_div_iff₀' hα₀).mp hη
  rw [Metric.uniformContinuousOn_iff] at hf_ucont
  specialize hf_ucont η hη₀
  obtain ⟨δ, hδ, hf_ucont⟩ := hf_ucont
  change ∀ x ∈ Icc a b, ∀ t ∈ Icc a b, |x - t| < δ → |f x - f t| < η at hf_ucont
  obtain ⟨P, hP⟩ := Partition.exists_lt I hδ
  use P
  rw [UL_eq]
  have (i : ℕ) : ∀ y₁ ∈ f '' P.interval i, y₁ - m P f i ≤ η := by
    intro y₁ hy₁
    dsimp only [m]
    have h₀ := (P.interval_nonempty i).image f
    have h₁ := (P.interval_bdd_on hf i).below'
    rw [sInf.sub_set h₀ h₁]
    refine csSup_le ?_ ?_
    · obtain ⟨x, hx⟩ := h₀
      exact ⟨y₁ - x, x, hx, rfl⟩
    · intro z ⟨y₂, hy₂, heq⟩
      subst heq
      refine le_of_lt ?_
      refine lt_of_abs_lt ?_
      obtain ⟨x, hx, heq⟩ := hy₁
      subst heq
      obtain ⟨t, ht, heq⟩ := hy₂
      subst heq
      apply hf_ucont
      · exact (P.interval_subset i) hx
      · exact (P.interval_subset i) ht
      · refine (hP i).trans_le' ?_
        refine .trans ?_ (le_abs_self _)
        exact abs_sub_le_of_le_of_le hx.1 hx.2 ht.1 ht.2
  have (i : ℕ) : M P f i - m P f i ≤ η := by
    dsimp only [M]
    have h₀ := (P.interval_nonempty i).image f
    have h₁ := (P.interval_bdd_on hf i).above'
    rw [sSup.set_sub h₀ h₁]
    refine csSup_le ?_ ?_
    · obtain ⟨x, hx⟩ := h₀
      exact ⟨x - m P f i, x, hx, rfl⟩
    · intro y ⟨x, hx, heq⟩
      subst heq
      exact this i x hx
  have (i : ℕ) : (M P f i - m P f i) * P.Δ α i ≤ η * P.Δ α i := by
    refine mul_le_mul_of_nonneg_right ?_ (P.Δ_nonneg hα i)
    exact this i
  have : ∑ i ∈ Finset.range P.n, (M P f i - m P f i) * P.Δ α i ≤
    ∑ i ∈ Finset.range P.n, η * P.Δ α i := by
    exact Finset.sum_le_sum fun i _ ↦ this i
  refine this.trans_lt ?_
  rw [<-Finset.mul_sum]
  dsimp only [Partition.Δ]
  rw [α_telescope]
  rw [mul_comm]
  exact hηε -- ∎

end Rudin
